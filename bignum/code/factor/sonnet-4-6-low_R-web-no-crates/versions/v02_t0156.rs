use std::io::{self, BufRead, Write, BufWriter};
use std::time::{Duration, Instant};
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use std::sync::mpsc;
use std::thread;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Zero, One, ToPrimitive};

// XorShift64 PRNG - no external crate needed
fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

// ============================================================
// Fast u128 path (for n fitting in u128, i.e., d <= ~19)
// ============================================================

// mulmod for u128: a, b, m where a,b < m < 2^63 (fits in u64)
#[inline(always)]
fn mulmod64(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

// mulmod for u128 where values can be up to 2^128 - use 128-bit parts
// We use __uint128 trick via 64-bit pieces
fn mulmod128(mut a: u128, mut b: u128, m: u128) -> u128 {
    let mut result: u128 = 0;
    a %= m;
    while b > 0 {
        if b & 1 == 1 {
            result = result.wrapping_add(a);
            if result >= m {
                result -= m;
            }
        }
        a = a.wrapping_add(a);
        if a >= m {
            a -= m;
        }
        b >>= 1;
    }
    result
}

fn powmod128(mut base: u128, mut exp: u128, m: u128) -> u128 {
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
    if n == 2 || n == 3 || n == 5 || n == 7 { return true; }
    if n % 2 == 0 || n % 3 == 0 || n % 5 == 0 { return false; }

    // Miller-Rabin with deterministic witnesses for n < 3,317,044,064,679,887,385,961,981
    // These witnesses are sufficient for all 64-bit numbers
    let witnesses: &[u128] = if n < 3_215_031_751 {
        &[2, 3, 5, 7]
    } else if n < 3_317_044_064_679_887_385_961_981 {
        &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    } else {
        &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
    };

    let n_minus_1 = n - 1;
    let mut d = n_minus_1;
    let mut r = 0u32;
    while d & 1 == 0 {
        d >>= 1;
        r += 1;
    }

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
    let mut y = (xorshift64(rng) as u128) % (n - 2) + 2;
    let mut r: u64 = 1;
    let mut q = 1u128;
    let mut x;
    let mut ys;
    let mut d;
    let m: u64 = 128;

    loop {
        x = y;
        for _ in 0..r {
            y = (mulmod128(y, y, n) + c) % n;
        }
        let mut k: u64 = 0;
        d = 1;
        while k < r {
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
            if d != 1 { break; }
        }
        if d != 1 { break; }
        r *= 2;
        if r > 1 << 30 { return None; }
    }

    if d == n {
        // backtrack to find factor
        loop {
            ys = (mulmod128(ys, ys, n) + c) % n;
            let diff = if ys > x { ys - x } else { x - ys };
            d = gcd128(diff, n);
            if d != 1 { break; }
        }
    }

    if d != n && d != 0 { Some(d) } else { None }
}

fn factor_u128(n: u128) -> (u128, u128) {
    // Trial division up to 1M
    if n == 1 { return (1, 1); }
    let small_primes = [2u128, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
    for &p in &small_primes {
        if n % p == 0 { return (p, n / p); }
    }
    let mut i = 49u128;
    while i * i <= n && i < 1_000_000 {
        if n % i == 0 { return (i, n / i); }
        if n % (i + 2) == 0 { return (i + 2, n / (i + 2)); }
        i += 6;
    }
    if i * i > n {
        // n is prime? shouldn't happen for semiprime
        return (1, n);
    }

    // Pollard's rho
    let mut rng: u64 = 0xdeadbeefcafe1234 ^ n as u64;
    let stopped = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<u128>();
    let num_threads = 8usize;

    for t in 0..num_threads {
        let tx = tx.clone();
        let stopped = stopped.clone();
        let mut thread_rng = rng ^ (t as u64 * 0x9e3779b97f4a7c15);
        thread_rng ^= thread_rng << 13;
        thread_rng ^= thread_rng >> 7;
        let n_copy = n;
        thread::spawn(move || {
            let mut local_rng = thread_rng;
            let mut c = (xorshift64(&mut local_rng) as u128) % (n_copy - 2) + 1;
            loop {
                if stopped.load(Ordering::Relaxed) { break; }
                if let Some(f) = pollard_brent_u128(n_copy, c, &mut local_rng) {
                    if f != 1 && f != n_copy {
                        let _ = tx.send(f);
                        return;
                    }
                }
                c = (xorshift64(&mut local_rng) as u128) % (n_copy - 2) + 1;
            }
        });
    }
    drop(tx);
    rng ^= 0xabcd1234;

    let factor = rx.recv().unwrap_or(1);
    stopped.store(true, Ordering::Relaxed);
    if factor == 0 || factor == 1 || factor == n {
        return (1, n);
    }
    let (p, q) = (factor, n / factor);
    if p <= q { (p, q) } else { (q, p) }
}

// ============================================================
// BigUint path for large numbers
// ============================================================

fn is_prime_bigint(n: &BigUint) -> bool {
    let zero = BigUint::zero();
    let one = BigUint::one();
    let two = BigUint::from(2u64);

    if n < &two { return false; }
    if n == &two || n == &BigUint::from(3u64) { return true; }
    if n % &two == zero { return false; }

    // Check small primes first
    let small_primes: [u64; 15] = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53];
    for p in small_primes {
        let bp = BigUint::from(p);
        if n == &bp { return true; }
        if n % &bp == zero { return false; }
    }

    // Miller-Rabin with several witnesses
    let n_minus_1 = n - &one;
    let mut d = n_minus_1.clone();
    let mut r = 0u32;
    while &d % &two == zero {
        d >>= 1;
        r += 1;
    }

    let witnesses: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
    'outer: for a in witnesses {
        let a_big = BigUint::from(a);
        if &a_big >= n { continue; }
        let mut x = a_big.modpow(&d, n);
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
    let n_minus_2 = n - BigUint::from(2u64);
    let c_big = BigUint::from(c);

    // Generate random starting point
    let y_val = xorshift64(rng) as u128;
    let mut y = BigUint::from(y_val % n_minus_2.to_u128().unwrap_or(u128::MAX)) + BigUint::from(2u64);
    if y >= *n { y = BigUint::from(2u64); }

    let mut r: u64 = 1;
    let mut q = one.clone();
    let mut x;
    let mut ys = BigUint::zero();
    let mut d;
    let m: u64 = 128;

    let f = |val: &BigUint| -> BigUint {
        (val * val + &c_big) % n
    };

    loop {
        x = y.clone();
        for _ in 0..r {
            y = f(&y);
        }
        let mut k: u64 = 0;
        d = one.clone();
        while k < r {
            ys = y.clone();
            let steps = m.min(r - k);
            for _ in 0..steps {
                y = f(&y);
                let diff = if y > x { &y - &x } else { &x - &y };
                q = (q * diff) % n;
                if q == BigUint::zero() { q = one.clone(); }
            }
            d = q.gcd(n);
            k += steps;
            if d != one { break; }
        }
        if d != one { break; }
        r *= 2;
        if r > (1u64 << 28) { return None; }
    }

    if &d == n {
        // backtrack
        d = one.clone();
        loop {
            ys = f(&ys);
            let diff = if ys > x { &ys - &x } else { &x - &ys };
            d = diff.gcd(n);
            if d != one { break; }
        }
    }

    if &d != n && d != BigUint::zero() && d != one {
        Some(d)
    } else {
        None
    }
}

fn factor_big(n: &BigUint, deadline: Instant, stopped: &AtomicBool) -> Option<(BigUint, BigUint)> {
    let one = BigUint::one();
    let two = BigUint::from(2u64);

    // Trial division up to small bound
    let trial_bound = 1_000_000u64;
    if n % &two == BigUint::zero() {
        return Some((two.clone(), n / &two));
    }
    let mut i = 3u64;
    while i < trial_bound {
        let bi = BigUint::from(i);
        if n % &bi == BigUint::zero() {
            return Some((bi.clone(), n / &bi));
        }
        i += 2;
        if Instant::now() > deadline { return None; }
    }

    // Check if n might fit in u128
    if let Some(n_u128) = n.to_u128() {
        let (p, q) = factor_u128(n_u128);
        return Some((BigUint::from(p), BigUint::from(q)));
    }

    // Parallel Pollard's rho
    let (tx, rx) = mpsc::channel::<BigUint>();
    let stopped_arc = Arc::new(AtomicBool::new(false));
    let num_threads = 8usize;

    for t in 0..num_threads {
        let tx = tx.clone();
        let stopped_clone = stopped_arc.clone();
        let n_clone = n.clone();
        let seed: u64 = 0xdeadbeef1234abcd ^ (t as u64 * 0x9e3779b97f4a7c15);
        thread::spawn(move || {
            let mut rng = seed;
            xorshift64(&mut rng); // warm up
            let mut c = (xorshift64(&mut rng) % (n_clone.bits() as u64).max(2)) + 1;
            loop {
                if stopped_clone.load(Ordering::Relaxed) { return; }
                if let Some(f) = pollard_brent_big(&n_clone, c, &mut rng) {
                    if &f != &n_clone && f != BigUint::one() {
                        let _ = tx.send(f);
                        return;
                    }
                }
                c = (xorshift64(&mut rng) % (n_clone.bits() as u64).max(2)) + 1;
            }
        });
    }
    drop(tx);

    // Wait for result or timeout
    let remaining = deadline.saturating_duration_since(Instant::now());
    let factor = rx.recv_timeout(remaining).ok();
    stopped_arc.store(true, Ordering::Relaxed);

    factor.map(|f| {
        let q = n / &f;
        if f <= q { (f, q) } else { (q.clone(), n / &q) }
    })
}

// ============================================================
// Main
// ============================================================

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut time_limit_secs = 60u64;
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
    let deadline = start + Duration::from_secs(time_limit_secs).saturating_sub(Duration::from_millis(200));

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    // Read all inputs first
    let mut inputs: Vec<(serde_like_id, BigUint)> = Vec::new();
    // Actually, let's parse manually since no serde
    let mut lines: Vec<(String, BigUint)> = Vec::new();

    for line in stdin.lock().lines() {
        let line = match line { Ok(l) => l, Err(_) => break };
        let line = line.trim().to_string();
        if line.is_empty() { continue; }

        // Parse {"id": ..., "n": <int>}
        if let (Some(id), Some(n)) = (parse_id(&line), parse_n(&line)) {
            lines.push((id, n));
        }
    }

    let stopped = AtomicBool::new(false);

    for (id, n) in &lines {
        if Instant::now() >= deadline {
            writeln!(out, "{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}", id).unwrap();
            out.flush().unwrap();
            continue;
        }

        // Try to factor
        let result = if let Some(n_u128) = n.to_u128() {
            // Fast path
            let (p, q) = factor_u128(n_u128);
            if p == 1 || p == n_u128 {
                None
            } else {
                Some((BigUint::from(p.min(q)), BigUint::from(p.max(q))))
            }
        } else {
            let remaining = deadline.saturating_duration_since(Instant::now());
            factor_big(n, deadline, &stopped)
                .map(|(p, q)| if p <= q { (p, q) } else { (q.clone(), n / &q) })
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

    // Print timeouts for any remaining (in case we broke early)
}

fn parse_id(line: &str) -> Option<String> {
    // Parse "id": "..."
    let id_key = "\"id\":";
    let pos = line.find(id_key)?;
    let rest = &line[pos + id_key.len()..];
    let rest = rest.trim_start();
    if rest.starts_with('"') {
        let rest = &rest[1..];
        let end = rest.find('"')?;
        Some(rest[..end].to_string())
    } else {
        // numeric id
        let end = rest.find(|c: char| !c.is_ascii_digit())?;
        Some(rest[..end].to_string())
    }
}

fn parse_n(line: &str) -> Option<BigUint> {
    let n_key = "\"n\":";
    let pos = line.find(n_key)?;
    let rest = &line[pos + n_key.len()..];
    let rest = rest.trim_start();
    let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
    let num_str = &rest[..end];
    if num_str.is_empty() { return None; }
    num_str.parse::<BigUint>().ok()
}
