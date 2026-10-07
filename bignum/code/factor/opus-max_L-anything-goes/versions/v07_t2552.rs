use rusqsieve::{FactorConfig, Natural, Parallelism, factor_with};
use serde_json::Value;
use std::io::{BufRead, Write};
use std::sync::mpsc;
use std::time::{Duration, Instant};

type N = Natural<16>;

fn parse_args() -> f64 {
    let args: Vec<String> = std::env::args().collect();
    let mut t = 60.0;
    let mut i = 1;
    while i < args.len() {
        let a = &args[i];
        if a == "--time-limit" && i + 1 < args.len() {
            t = args[i + 1].parse().unwrap_or(60.0);
            i += 1;
        } else if let Some(v) = a.strip_prefix("--time-limit=") {
            t = v.parse().unwrap_or(60.0);
        }
        i += 1;
    }
    t
}

fn emit(line: &str) {
    let out = std::io::stdout();
    let mut lock = out.lock();
    let _ = lock.write_all(line.as_bytes());
    let _ = lock.write_all(b"\n");
    let _ = lock.flush();
}

fn answer_line(id: &Value, answer: Option<String>) -> String {
    let mut m = serde_json::Map::new();
    m.insert("id".to_string(), id.clone());
    match answer {
        Some(a) => {
            m.insert("answer".to_string(), Value::String(a));
        }
        None => {
            m.insert("answer".to_string(), Value::Null);
            m.insert("timeout".to_string(), Value::Bool(true));
        }
    }
    Value::Object(m).to_string()
}

fn n_digits(v: &Value) -> Option<String> {
    let s = match v {
        Value::Number(num) => num.to_string(),
        Value::String(s) => s.trim().to_string(),
        _ => return None,
    };
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    Some(s)
}

/// Returns "p q" (smallest first) for a semiprime, or the best split we can produce.
fn solve(digits: &str, threads: usize) -> Option<String> {
    let n = N::from_decimal(digits).ok()?;
    let one = N::from_u64(1);
    if n <= one {
        return Some(format!("{} 1", digits));
    }
    // Retry on the rare engine failure (e.g. no usable dependency) with a fresh witness seed;
    // the main thread enforces the deadline regardless.
    let mut f = None;
    for attempt in 0..4u8 {
        let cfg = FactorConfig::default()
            .with_parallelism(Parallelism::threads(threads).unwrap_or(Parallelism::Auto))
            .with_witness_seed([attempt.wrapping_mul(37).wrapping_add(1); 32]);
        let cfg = tune(cfg, n.bit_len());
        if let Ok(r) = factor_with(n.clone(), cfg) {
            f = Some(r);
            break;
        }
    }
    let f = f?;
    let mut primes: Vec<N> = f.expanded().cloned().collect();
    primes.sort();
    if primes.len() <= 1 {
        return Some(format!("1 {}", digits));
    }
    if primes.len() == 2 {
        return Some(format!("{} {}", primes[0], primes[1]));
    }
    // More than two prime factors: report smallest prime and the cofactor.
    let p = primes[0].clone();
    let mut q = one;
    for x in &primes[1..] {
        q = q.checked_mul(x).unwrap_or(q);
    }
    Some(format!("{} {}", p, q))
}

fn env<T: std::str::FromStr>(k: &str) -> Option<T> {
    std::env::var(k).ok().and_then(|v| v.parse().ok())
}

/// Per-size parameter overrides (measured on this machine); env vars override for experiments.
fn tune(cfg: FactorConfig, bits: usize) -> FactorConfig {
    // Below the crate's own 289-bit high-digit tiers, the high-digit sieve features are enabled
    // from 250 bits (vendored `hdt_bits`); these overrides were measured on the M4 for that range.
    let mid = (250..289).contains(&bits);
    let rp: Option<usize> = env("RQ_RP");
    let skip: Option<u32> = env("RQ_SKIP").or(if mid { Some(100) } else { None });
    let tm: Option<i32> = env("RQ_TM");
    let ta_default = match bits {
        250..=264 => Some(-4),
        265..=280 => Some(-6),
        _ => None,
    };
    let ta: Option<i32> = env("RQ_TA").or(ta_default);
    let fb: Option<u32> = env("RQ_FB");
    let hw: Option<u32> = env("RQ_HW");
    let lpm: Option<u32> = env("RQ_LPM");
    let dlp: Option<u64> = env("RQ_DLP");
    let rho: Option<u64> = env("RQ_RHO");
    let prof = std::env::var("RQ_PROFILE").is_ok();
    cfg.with_tuning_overrides(rp, skip, tm, ta, fb, hw, lpm, dlp, rho, prof)
}

enum Msg {
    Line(String),
    Eof,
}

fn main() {
    let start = Instant::now();
    let limit = parse_args();
    let margin = (limit * 0.01).clamp(0.15, 0.6);
    let deadline = start + Duration::from_secs_f64((limit - margin).max(0.05));
    let threads = std::thread::available_parallelism().map_or(10, usize::from);

    let (tx, rx) = mpsc::channel::<Msg>();
    std::thread::spawn(move || {
        let stdin = std::io::stdin();
        for line in stdin.lock().lines() {
            match line {
                Ok(l) => {
                    if tx.send(Msg::Line(l)).is_err() {
                        return;
                    }
                }
                Err(_) => break,
            }
        }
        let _ = tx.send(Msg::Eof);
    });

    let mut pending: std::collections::VecDeque<(Value, Option<String>)> = Default::default();
    let mut eof = false;
    let (rtx, rrx) = mpsc::channel::<(usize, Option<String>)>();
    let mut busy: Option<(usize, Value)> = None;
    let mut job_seq = 0usize;

    loop {
        // Drain all available input lines without blocking.
        loop {
            match rx.try_recv() {
                Ok(Msg::Line(l)) => {
                    let l = l.trim();
                    if l.is_empty() {
                        continue;
                    }
                    if let Ok(v) = serde_json::from_str::<Value>(l) {
                        let id = v.get("id").cloned().unwrap_or(Value::Null);
                        let n = v.get("n").and_then(n_digits);
                        pending.push_back((id, n));
                    }
                }
                Ok(Msg::Eof) => eof = true,
                Err(_) => break,
            }
        }

        if busy.is_none() {
            if let Some((id, n)) = pending.pop_front() {
                match n {
                    None => emit(&answer_line(&id, None)),
                    Some(d) => {
                        job_seq += 1;
                        let seq = job_seq;
                        let rtx = rtx.clone();
                        std::thread::spawn(move || {
                            let r = solve(&d, threads);
                            let _ = rtx.send((seq, r));
                        });
                        busy = Some((seq, id));
                    }
                }
                continue;
            }
            if eof {
                break;
            }
        }

        let now = Instant::now();
        if now >= deadline {
            break;
        }
        let wait = (deadline - now).min(Duration::from_millis(5));
        if busy.is_some() {
            match rrx.recv_timeout(wait) {
                Ok((seq, r)) => {
                    if let Some((bseq, id)) = busy.take() {
                        if bseq == seq {
                            emit(&answer_line(&id, r));
                        } else {
                            busy = Some((bseq, id));
                        }
                    }
                }
                Err(_) => {}
            }
        } else {
            match rx.recv_timeout(wait) {
                Ok(Msg::Line(l)) => {
                    let l = l.trim();
                    if !l.is_empty() {
                        if let Ok(v) = serde_json::from_str::<Value>(l) {
                            let id = v.get("id").cloned().unwrap_or(Value::Null);
                            let n = v.get("n").and_then(n_digits);
                            pending.push_back((id, n));
                        }
                    }
                }
                Ok(Msg::Eof) => eof = true,
                Err(_) => {}
            }
        }
    }

    // Timeout (or done): report anything unanswered.
    if let Some((_, id)) = busy.take() {
        emit(&answer_line(&id, None));
    }
    while let Some((id, _)) = pending.pop_front() {
        emit(&answer_line(&id, None));
    }
    let _ = std::io::stdout().flush();
    std::process::exit(0);
}
