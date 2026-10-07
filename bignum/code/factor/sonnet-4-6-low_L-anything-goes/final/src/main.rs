use std::io::{self, BufRead, Write, BufWriter};
use std::time::{Duration, Instant};
use std::sync::mpsc;
use std::thread;

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        a %= b;
        std::mem::swap(&mut a, &mut b);
    }
    a
}

fn is_prime_u64(n: u64) -> bool {
    if n < 2 { return false; }
    if n == 2 || n == 3 || n == 5 || n == 7 { return true; }
    if n % 2 == 0 || n % 3 == 0 || n % 5 == 0 { return false; }
    let mut d = n - 1;
    let mut r = 0u32;
    while d % 2 == 0 { d /= 2; r += 1; }
    let witnesses: &[u64] = &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    'outer: for &a in witnesses {
        if a >= n { continue; }
        let mut x = powmod64(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..r - 1 {
            x = mulmod64(x, x, n);
            if x == n - 1 { continue 'outer; }
        }
        return false;
    }
    true
}

fn mulmod64(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

fn powmod64(mut base: u64, mut exp: u64, modulus: u64) -> u64 {
    let mut result = 1u64;
    base %= modulus;
    while exp > 0 {
        if exp & 1 == 1 { result = mulmod64(result, base, modulus); }
        base = mulmod64(base, base, modulus);
        exp >>= 1;
    }
    result
}

fn pollard_rho_u64(n: u64) -> u64 {
    if n % 2 == 0 { return 2; }
    let mut rng_state = 12345u64;
    let mut next_rand = move || -> u64 {
        rng_state ^= rng_state << 13;
        rng_state ^= rng_state >> 7;
        rng_state ^= rng_state << 17;
        rng_state % (n - 2) + 2
    };
    loop {
        let c = next_rand();
        let mut y = next_rand();
        let m = 128u64;
        let mut g = 1u64;
        let mut q = 1u64;
        let mut r = 1u64;
        let mut x = 0u64;
        let mut ys = 0u64;
        while g == 1 {
            x = y;
            for _ in 0..r {
                y = (mulmod64(y, y, n) + c) % n;
            }
            let mut k = 0u64;
            g = 1;
            while k < r && g == 1 {
                ys = y;
                let step = m.min(r - k);
                for _ in 0..step {
                    y = (mulmod64(y, y, n) + c) % n;
                    let diff = if y > x { y - x } else { x - y };
                    q = mulmod64(q, diff, n);
                }
                g = gcd(q, n);
                k += m;
            }
            r *= 2;
        }
        if g == n {
            loop {
                ys = (mulmod64(ys, ys, n) + c) % n;
                let diff = if ys > x { ys - x } else { x - ys };
                g = gcd(diff, n);
                if g > 1 { break; }
            }
        }
        if g != n { return g; }
    }
}

fn find_factor_u64(n: u64) -> u64 {
    if is_prime_u64(n) { return n; }
    if n % 2 == 0 { return 2; }
    loop {
        let d = pollard_rho_u64(n);
        if d != n {
            let a = find_factor_u64(d);
            if a != n { return a; }
        }
    }
}

fn factor_u64(n: u64) -> (u64, u64) {
    for p in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
        if n % p == 0 { return (p, n / p); }
    }
    let p = find_factor_u64(n);
    let q = n / p;
    if p <= q { (p, q) } else { (q, p) }
}

fn factors_to_sorted_strings(expanded: Vec<impl std::fmt::Display>) -> Option<(String, String)> {
    if expanded.len() < 2 { return None; }
    let mut strs: Vec<String> = expanded.iter().map(|f| format!("{}", f)).collect();
    strs.sort_by(|a, b| a.len().cmp(&b.len()).then(a.cmp(b)));
    if strs.len() == 2 {
        Some((strs[0].clone(), strs[1].clone()))
    } else {
        // More than 2 factors (shouldn't happen for semiprime); combine last ones
        None
    }
}

fn factor_with_rusqsieve<const P: usize>(n_str: &str, deadline: Instant) -> Option<(String, String)> {
    use rusqsieve::{Natural, factor_with_progress, FactorConfig, Parallelism, ProgressAction};

    let n = Natural::<P>::from_decimal(n_str).ok()?;
    let num_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(10);
    let config = FactorConfig::default().with_parallelism(
        Parallelism::threads(num_threads)?
    );

    let factors = factor_with_progress(n, config, |_snapshot| {
        if Instant::now() >= deadline {
            ProgressAction::Cancel
        } else {
            ProgressAction::Continue
        }
    }).ok()?;

    let expanded: Vec<_> = factors.expanded().collect();
    factors_to_sorted_strings(expanded)
}

fn factor_big(n_str: &str, deadline: Instant) -> Option<(String, String)> {
    // Dispatch to appropriately-sized Natural to minimize overhead
    let bits = (n_str.len() as f64 * 3.3219 + 2.0) as usize;
    if bits <= 256 {
        factor_with_rusqsieve::<4>(n_str, deadline)
    } else if bits <= 320 {
        factor_with_rusqsieve::<5>(n_str, deadline)
    } else if bits <= 384 {
        factor_with_rusqsieve::<6>(n_str, deadline)
    } else if bits <= 448 {
        factor_with_rusqsieve::<7>(n_str, deadline)
    } else {
        factor_with_rusqsieve::<8>(n_str, deadline)
    }
}

fn factor_number(n_str: &str, deadline: Instant) -> Option<(String, String)> {
    // Fast path for numbers fitting in u64
    if let Ok(n) = n_str.parse::<u64>() {
        if n < 4 { return None; }
        let (p, q) = factor_u64(n);
        return Some((p.to_string(), q.to_string()));
    }
    factor_big(n_str, deadline)
}

fn factor_with_timeout(n_str: &str, deadline: Instant) -> Option<(String, String)> {
    let now = Instant::now();
    if now >= deadline { return None; }
    let remaining = deadline.duration_since(now);

    let n_str = n_str.to_string();
    let deadline2 = deadline;
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let result = factor_number(&n_str, deadline2);
        let _ = tx.send(result);
    });

    rx.recv_timeout(remaining + Duration::from_millis(500)).ok()?
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let time_limit = args.windows(2)
        .find(|w| w[0] == "--time-limit")
        .and_then(|w| w[1].parse::<f64>().ok())
        .unwrap_or(60.0);

    let start = Instant::now();
    let deadline = start + Duration::from_secs_f64(time_limit - 0.3);

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    let mut inputs: Vec<(String, String)> = Vec::new();
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let line = line.trim();
        if line.is_empty() { continue; }
        if let Ok(v) = serde_json::from_str::<serde_json::Value>(line) {
            let id = v["id"].as_str().unwrap_or("").to_string();
            let n_str = v["n"].to_string();
            inputs.push((id, n_str));
        }
    }

    for (id, n_str) in &inputs {
        let now = Instant::now();
        if now >= deadline {
            let response = serde_json::json!({"id": id, "answer": null, "timeout": true});
            writeln!(out, "{}", response).unwrap();
            out.flush().unwrap();
            continue;
        }

        match factor_with_timeout(n_str, deadline) {
            Some((p, q)) => {
                let response = serde_json::json!({"id": id, "answer": format!("{} {}", p, q)});
                writeln!(out, "{}", response).unwrap();
            }
            None => {
                let response = serde_json::json!({"id": id, "answer": null, "timeout": true});
                writeln!(out, "{}", response).unwrap();
            }
        }
        out.flush().unwrap();
    }
}
