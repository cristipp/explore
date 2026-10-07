mod linalg;
mod siqs;
mod util;

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};
use std::io::{self, BufRead, Write};
use std::sync::{mpsc, Arc, Mutex};
use std::time::{Duration, Instant};

fn parse_value(s: &str, key: &str) -> Option<String> {
    let pat = format!("\"{}\"", key);
    let pos = s.find(&pat)? + pat.len();
    let rest = s[pos..].trim_start();
    let rest = rest.strip_prefix(':')?.trim_start();
    if let Some(r) = rest.strip_prefix('"') {
        let mut end = 0;
        let bytes = r.as_bytes();
        while end < bytes.len() {
            if bytes[end] == b'\\' {
                end += 2;
                continue;
            }
            if bytes[end] == b'"' {
                break;
            }
            end += 1;
        }
        Some(format!("\"{}\"", &r[..end.min(r.len())]))
    } else {
        let end = rest.find(|c: char| c == ',' || c == '}').unwrap_or(rest.len());
        Some(rest[..end].trim().to_string())
    }
}

fn factor(n: &BigUint, deadline: Instant, verbose: bool) -> Option<(BigUint, BigUint)> {
    if n <= &BigUint::from(3u32) {
        return None;
    }
    if n.is_even() {
        return Some((BigUint::from(2u32), n / 2u32));
    }
    // small trial division
    for p in (3u32..10000).step_by(2) {
        if (n % p).is_zero() {
            if &BigUint::from(p) == n {
                return None;
            }
            return Some((BigUint::from(p), n / p));
        }
    }
    let r = n.sqrt();
    if &(&r * &r) == n {
        return Some((r.clone(), r));
    }
    if n.bits() <= 62 {
        let v = n.to_u64().unwrap();
        if util::is_prime_u64(v) {
            return None;
        }
        let f = util::rho_u64(v);
        return Some((BigUint::from(f), BigUint::from(v / f)));
    }
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    let f = siqs::siqs(n, deadline, nthreads, verbose)?;
    let g = n / &f;
    Some((f, g))
}

struct State {
    pending: Vec<(u64, String)>,
}

fn main() {
    let start = Instant::now();
    let args: Vec<String> = std::env::args().collect();
    let mut tl = 60.0f64;
    let mut verbose = false;
    let mut i = 1;
    while i < args.len() {
        if args[i] == "--time-limit" && i + 1 < args.len() {
            tl = args[i + 1].parse().unwrap_or(60.0);
            i += 1;
        } else if args[i] == "-v" {
            verbose = true;
        }
        i += 1;
    }
    let margin = (tl * 0.02).max(0.15).min(0.6);
    let deadline = start + Duration::from_secs_f64((tl - margin).max(0.05));
    let state = Arc::new(Mutex::new(State { pending: vec![] }));
    // watchdog
    {
        let state = state.clone();
        std::thread::spawn(move || {
            let now = Instant::now();
            if deadline > now {
                std::thread::sleep(deadline - now);
            }
            let st = state.lock().unwrap();
            let stdout = io::stdout();
            let mut out = stdout.lock();
            for (_, id) in &st.pending {
                let _ = writeln!(out, "{{\"id\": {}, \"answer\": null, \"timeout\": true}}", id);
            }
            let _ = out.flush();
            std::process::exit(0);
        });
    }
    let (tx, rx) = mpsc::channel::<(u64, String, Option<BigUint>)>();
    {
        let state = state.clone();
        std::thread::spawn(move || {
            let stdin = io::stdin();
            let mut seq = 0u64;
            for line in stdin.lock().lines() {
                let line = match line {
                    Ok(l) => l,
                    Err(_) => break,
                };
                if line.trim().is_empty() {
                    continue;
                }
                let id = parse_value(&line, "id").unwrap_or_else(|| "null".to_string());
                let n = parse_value(&line, "n")
                    .map(|s| s.trim_matches('"').to_string())
                    .and_then(|s| s.parse::<BigUint>().ok());
                state.lock().unwrap().pending.push((seq, id.clone()));
                if tx.send((seq, id, n)).is_err() {
                    break;
                }
                seq += 1;
            }
        });
    }
    for (seq, id, n) in rx {
        let ans = match &n {
            Some(n) => factor(n, deadline, verbose),
            None => None,
        };
        let st = &mut *state.lock().unwrap();
        let stdout = io::stdout();
        let mut out = stdout.lock();
        match ans {
            Some((a, b)) => {
                let (a, b) = if a <= b { (a, b) } else { (b, a) };
                let _ = writeln!(out, "{{\"id\": {}, \"answer\": \"{} {}\"}}", id, a, b);
            }
            None => {
                if Instant::now() >= deadline {
                    let _ = writeln!(out, "{{\"id\": {}, \"answer\": null, \"timeout\": true}}", id);
                } else {
                    let _ = writeln!(out, "{{\"id\": {}, \"answer\": null}}", id);
                }
            }
        }
        let _ = out.flush();
        st.pending.retain(|(s, _)| *s != seq);
    }
    let _ = BigUint::one();
    std::process::exit(0);
}
