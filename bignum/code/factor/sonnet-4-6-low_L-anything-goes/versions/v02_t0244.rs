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

// Miller-Rabin primality test for u64
fn is_prime_u64(n: u64) -> bool {
    if n < 2 { return false; }
    if n == 2 || n == 3 || n == 5 || n == 7 { return true; }
    if n % 2 == 0 || n % 3 == 0 || n % 5 == 0 { return false; }

    let mut d = n - 1;
    let mut r = 0u32;
    while d % 2 == 0 { d /= 2; r += 1; }

    // Deterministic witnesses for n < 3,317,044,064,679,887,385,961,981
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

// Pollard's rho (Brent's variant) for u64
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
        let mut m = 128u64;
        let mut g = 1u64;
        let mut q = 1u64;
        let mut r = 1u64;
        let mut x;
        let mut ys;

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
            // Backtrack
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

// Factor n into two primes (assumes n = p*q semiprime)
fn factor_u64(n: u64) -> (u64, u64) {
    // Trial division for small factors
    for p in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
        if n % p == 0 { return (p, n / p); }
    }

    // Pollard's rho
    let p = find_factor_u64(n);
    let q = n / p;
    if p <= q { (p, q) } else { (q, p) }
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

// Factor using rusqsieve for large numbers
fn factor_big(n_str: &str) -> Option<(String, String)> {
    use rusqsieve::{Natural, factor_with, FactorConfig, Parallelism};

    let n = Natural::<8>::from_decimal(n_str).ok()?;

    let num_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8);

    let config = FactorConfig::default().with_parallelism(
        Parallelism::threads(num_threads).ok()?
    );

    let factors = factor_with(n, config).ok()?;

    // For a semiprime, there should be exactly 2 prime factors
    let expanded: Vec<_> = factors.expanded().collect();
    if expanded.len() != 2 {
        // Might be a prime or have more factors; try to extract 2 factors
        let primes: Vec<String> = expanded.iter()
            .map(|f| format!("{}", f))
            .collect();
        if primes.len() == 2 {
            let a: u128 = primes[0].parse().ok()?;
            let b: u128 = primes[1].parse().ok()?;
            let (lo, hi) = if a <= b { (primes[0].clone(), primes[1].clone()) } else { (primes[1].clone(), primes[0].clone()) };
            return Some((lo, hi));
        }
        return None;
    }

    let f0 = format!("{}", expanded[0]);
    let f1 = format!("{}", expanded[1]);

    // Sort smallest first
    let (lo, hi) = if f0.len() < f1.len() || (f0.len() == f1.len() && f0 <= f1) {
        (f0, f1)
    } else {
        (f1, f0)
    };

    Some((lo, hi))
}

fn factor_number(n_str: &str) -> Option<(String, String)> {
    // Try u64 fast path
    if let Ok(n) = n_str.parse::<u64>() {
        if n < 4 { return None; }
        let (p, q) = factor_u64(n);
        return Some((p.to_string(), q.to_string()));
    }

    // Use rusqsieve for larger numbers
    factor_big(n_str)
}

fn factor_with_timeout(n_str: &str, remaining: Duration) -> Option<(String, String)> {
    let n_str = n_str.to_string();
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let result = factor_number(&n_str);
        let _ = tx.send(result);
    });

    rx.recv_timeout(remaining).ok()?
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let time_limit = args.windows(2)
        .find(|w| w[0] == "--time-limit")
        .and_then(|w| w[1].parse::<f64>().ok())
        .unwrap_or(60.0);

    let start = Instant::now();
    let deadline = start + Duration::from_secs_f64(time_limit - 0.2); // 0.2s buffer

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    // Read all inputs first
    let mut inputs: Vec<(String, String)> = Vec::new();
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let line = line.trim();
        if line.is_empty() { continue; }

        // Parse JSON: {"id": "...", "n": <bigint>}
        // Use serde_json with arbitrary_precision
        if let Ok(v) = serde_json::from_str::<serde_json::Value>(line) {
            let id = v["id"].as_str().unwrap_or("").to_string();
            let n_str = v["n"].to_string(); // arbitrary_precision gives us the decimal string
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

        let remaining = deadline.duration_since(now);

        match factor_with_timeout(n_str, remaining) {
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
