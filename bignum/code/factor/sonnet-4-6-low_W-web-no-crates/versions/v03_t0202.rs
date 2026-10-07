use std::io::{self, BufRead, Write, BufWriter};
use std::time::{Duration, Instant};
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use std::sync::mpsc;
use std::thread;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Zero, One, ToPrimitive};

fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

// mulmod for u128 via binary method (handles full u128 range)
fn mulmod128(mut a: u128, mut b: u128, m: u128) -> u128 {
    // Use 128-bit arithmetic with careful wrapping
    // For a, b < 2^63 this is just (a*b)%m with u128
    // For larger values, use binary method
    if a < (1u128 << 64) && b < (1u128 << 64) {
        // Both fit in u64, use u128 directly
        return (a * b) % m;
    }
    let mut result: u128 = 0;
    a %= m;
    b %= m;
    while b > 0 {
        if b & 1 == 1 {
            result += a;
            if result >= m { result -= m; }
        }
        a += a;
        if a >= m { a -= m; }
        b >>= 1;
    }
    result
}

fn powmod128(mut base: u128, mut exp: u128, m: u128) -> u128 {
    if m == 1 { return 0; }
    let mut result = 1u128;
    base %= m;
    while exp > 0 {
        if exp & 1 == 1 {
            result = mulmod128(result, base, m);
        }
        base = mulmod128(base, base, m);
        exp >>= 1;
    }
    result
}

fn is_prime_u128(n: u128) -> bool {
    if n < 2 { return false; }
    if n == 2 { return true; }
    if n % 2 == 0 { return false; }
    if n < 9 { return true; }
    if n % 3 == 0 || n % 5 == 0 { return false; }

    let n_minus_1 = n - 1;
    let mut d = n_minus_1;
    let mut r = 0u32;
    while d & 1 == 0 { d >>= 1; r += 1; }

    // Deterministic witnesses sufficient for n < 3.3 * 10^24
    let witnesses: &[u128] = &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

    'outer: for &a in witnesses {
        if a >= n { continue; }
        let mut x = powmod128(a, d, n);
        if x == 1 || x == n_minus_1 { continue; }
        for _ in 0..r-1 {
            x = mulmod128(x, x, n);
            if x == n_minus_1 { continue 'outer; }
        }
        return false;
    }
    true
}

fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn pollard_brent_u128(n: u128, c: u128, rng: &mut u64) -> Option<u128> {
    if n % 2 == 0 { return Some(2); }
    let start = (xorshift64(rng) as u128) % (n - 2) + 2;
    let mut y = start;
    let mut r: u64 = 1;
    let mut q = 1u128;
    let mut x = y;
    let mut ys;
    let mut d;
    let m: u64 = 128;

    loop {
        x = y;
        for _ in 0..r {
            y = (mulmod128(y, y, n) + c) % n;
        }
        let mut k: u64 = 0;
        d = 1u128;
        while k < r && d == 1 {
            ys = y;
            let steps = m.min(r - k);
            for _ in 0..steps {
                y = (mulmod128(y, y, n) + c) % n;
                let diff = if y > x { y - x } else { x - y };
                q = mulmod128(q, diff, n);
                if q == 0 { q = 1; }
            }
            d = gcd128(q, n);
            k += steps;
        }
        if d != 1 { break; }
        r *= 2;
        if r > (1u64 << 28) { return None; }
    }

    if d == n {
        // backtrack
        d = 1;
        ys = x;
        loop {
            ys = (mulmod128(ys, ys, n) + c) % n;
            let diff = if ys > x { ys - x } else { x - ys };
            d = gcd128(diff, n);
            if d != 1 { break; }
        }
        if d == n { return None; }
    }

    if d != n && d != 0 && d != 1 { Some(d) } else { None }
}

fn factor_u128_single(n: u128) -> (u128, u128) {
    if n <= 1 { return (1, 1); }
    // Quick small primes
    for &p in &[2u128,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97] {
        if n == p { return (p, 1); }
        if n % p == 0 { return (p, n/p); }
    }
    let mut i = 101u128;
    while i * i <= n && i < 1_000_000 {
        if n % i == 0 { return (i, n/i); }
        if n % (i+2) == 0 { return (i+2, n/(i+2)); }
        i += 6;
    }
    if i * i > n { return (n, 1); }
    // Pollard's rho
    let mut rng: u64 = 0xdeadbeef1234abcd ^ (n as u64);
    for attempt in 0..10000 {
        let c = (xorshift64(&mut rng) as u128) % (n - 2) + 1;
        if let Some(f) = pollard_brent_u128(n, c, &mut rng) {
            if f != 1 && f != n {
                return (f.min(n/f), f.max(n/f));
            }
        }
    }
    (1, n)
}

fn factor_u128_parallel(n: u128) -> (u128, u128) {
    let stopped = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<u128>();
    let num_threads = 8usize;

    for t in 0..num_threads {
        let tx = tx.clone();
        let stopped = stopped.clone();
        let mut seed: u64 = 0xdeadbeef1234abcd ^ (n as u64) ^ (t as u64 * 0x9e3779b97f4a7c15);
        xorshift64(&mut seed);
        thread::spawn(move || {
            let mut rng = seed;
            loop {
                if stopped.load(Ordering::Relaxed) { return; }
                let c = (xorshift64(&mut rng) as u128) % (n - 2) + 1;
                if let Some(f) = pollard_brent_u128(n, c, &mut rng) {
                    if f != 1 && f != n {
                        let _ = tx.send(f);
                        stopped.store(true, Ordering::Relaxed);
                        return;
                    }
                }
            }
        });
    }
    drop(tx);

    match rx.recv() {
        Ok(f) => {
            stopped.store(true, Ordering::Relaxed);
            (f.min(n/f), f.max(n/f))
        }
        Err(_) => (1, n),
    }
}

// ============================================================
// BigUint path
// ============================================================

fn is_prime_big(n: &BigUint) -> bool {
    let zero = BigUint::zero();
    let one = BigUint::one();
    let two = BigUint::from(2u64);

    if n < &two { return false; }
    if n == &two { return true; }
    if n % &two == zero { return false; }

    let small_primes: [u64; 20] = [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73];
    for p in small_primes {
        let bp = BigUint::from(p);
        if n == &bp { return true; }
        if n % &bp == zero { return false; }
    }

    let n_minus_1 = n - &one;
    let mut d = n_minus_1.clone();
    let mut r = 0u32;
    while &d % &two == zero { d >>= 1; r += 1; }

    let witnesses: [u64; 20] = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71];
    'outer: for a in witnesses {
        let ab = BigUint::from(a);
        if &ab >= n { continue; }
        let mut x = ab.modpow(&d, n);
        if x == one || x == n_minus_1 { continue; }
        for _ in 0..r-1 {
            x = x.modpow(&two, n);
            if x == n_minus_1 { continue 'outer; }
        }
        return false;
    }
    true
}

fn pollard_brent_big(n: &BigUint, c: u64, rng: &mut u64) -> Option<BigUint> {
    let one = BigUint::one();
    let c_big = BigUint::from(c);
    let two = BigUint::from(2u64);

    let y_val = xorshift64(rng) as u64;
    let mut y = BigUint::from(y_val) % (n - &two) + &two;

    let mut r: u64 = 1;
    let mut q = one.clone();
    let mut x = y.clone();
    let mut ys = y.clone();
    let mut d = one.clone();
    let m: u64 = 128;

    let f = |v: &BigUint| -> BigUint { (v * v + &c_big) % n };

    loop {
        x = y.clone();
        for _ in 0..r {
            y = f(&y);
        }
        let mut k: u64 = 0;
        d = one.clone();
        while k < r && d == one {
            ys = y.clone();
            let steps = m.min(r - k);
            for _ in 0..steps {
                y = f(&y);
                let diff = if y > x { &y - &x } else { &x - &y };
                q = (&q * diff) % n;
                if q == BigUint::zero() { q = one.clone(); }
            }
            d = q.gcd(n);
            k += steps;
        }
        if d != one { break; }
        r *= 2;
        if r > (1u64 << 28) { return None; }
    }

    if &d == n {
        d = one.clone();
        loop {
            ys = f(&ys);
            let diff = if ys > x { &ys - &x } else { &x - &ys };
            d = diff.gcd(n);
            if d != one { break; }
        }
        if &d == n { return None; }
    }

    if d != one && &d != n { Some(d) } else { None }
}

fn factor_big_parallel(n: &BigUint, deadline: Instant) -> Option<(BigUint, BigUint)> {
    let one = BigUint::one();
    let two = BigUint::from(2u64);

    // Trial division
    if n % &two == BigUint::zero() {
        return Some((two.clone(), n / &two));
    }
    let mut i = 3u64;
    while i < 1_000_000 {
        let bi = BigUint::from(i);
        if n % &bi == BigUint::zero() {
            return Some((bi.clone(), n / &bi));
        }
        i += 2;
    }

    // Parallel Pollard's rho
    let stopped = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<BigUint>();
    let num_threads = 8usize;

    for t in 0..num_threads {
        let tx = tx.clone();
        let stopped = stopped.clone();
        let n_clone = n.clone();
        let seed: u64 = 0xdeadbeef1234abcd ^ (t as u64 * 0x9e3779b97f4a7c15);
        thread::spawn(move || {
            let mut rng = seed;
            xorshift64(&mut rng);
            loop {
                if stopped.load(Ordering::Relaxed) { return; }
                let c = (xorshift64(&mut rng) % (n_clone.bits() as u64 * 16).max(16)) + 1;
                if let Some(f) = pollard_brent_big(&n_clone, c, &mut rng) {
                    if f != one && &f != &n_clone {
                        let _ = tx.send(f);
                        stopped.store(true, Ordering::Relaxed);
                        return;
                    }
                }
            }
        });
    }
    drop(tx);

    let remaining = deadline.saturating_duration_since(Instant::now());
    let factor = rx.recv_timeout(remaining).ok()?;
    stopped.store(true, Ordering::Relaxed);

    let q = n / &factor;
    let (p, q) = if factor <= q { (factor, q) } else { (q.clone(), n / &q) };
    Some((p, q))
}

// ============================================================
// Main
// ============================================================

fn parse_id(line: &str) -> Option<String> {
    let key = "\"id\":";
    let pos = line.find(key)?;
    let rest = line[pos + key.len()..].trim_start();
    if let Some(rest2) = rest.strip_prefix('"') {
        let end = rest2.find('"')?;
        Some(rest2[..end].to_string())
    } else {
        let end = rest.find(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != '-').unwrap_or(rest.len());
        Some(rest[..end].to_string())
    }
}

fn parse_n(line: &str) -> Option<BigUint> {
    let key = "\"n\":";
    let pos = line.find(key)?;
    let rest = line[pos + key.len()..].trim_start();
    let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
    if end == 0 { return None; }
    rest[..end].parse::<BigUint>().ok()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut time_limit_secs: u64 = 60;
    let mut i = 1;
    while i < args.len() {
        if args[i] == "--time-limit" && i + 1 < args.len() {
            time_limit_secs = args[i+1].parse().unwrap_or(60);
            i += 2;
        } else {
            i += 1;
        }
    }

    let start = Instant::now();
    // Leave 300ms margin for final output
    let deadline = start + Duration::from_millis(time_limit_secs * 1000 - 300);

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    // Read all inputs
    let mut inputs: Vec<(String, BigUint)> = Vec::new();
    for line in stdin.lock().lines() {
        let line = match line { Ok(l) => l, Err(_) => break };
        let line = line.trim().to_string();
        if line.is_empty() { continue; }
        if let (Some(id), Some(n)) = (parse_id(&line), parse_n(&line)) {
            inputs.push((id, n));
        }
    }

    for (id, n) in &inputs {
        if Instant::now() >= deadline {
            writeln!(out, "{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}", id).unwrap();
            out.flush().unwrap();
            continue;
        }

        let result: Option<(BigUint, BigUint)> = if let Some(n_small) = n.to_u128() {
            // Fast u128 path
            let (p, q) = factor_u128_parallel(n_small);
            if p == 1 { None } else { Some((BigUint::from(p), BigUint::from(q))) }
        } else {
            factor_big_parallel(n, deadline)
        };

        match result {
            Some((p, q)) => {
                writeln!(out, "{{\"id\": \"{}\", \"answer\": \"{} {}\"}}", id, p, q).unwrap();
            }
            None => {
                writeln!(out, "{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}", id).unwrap();
            }
        }
        out.flush().unwrap();
    }
}
