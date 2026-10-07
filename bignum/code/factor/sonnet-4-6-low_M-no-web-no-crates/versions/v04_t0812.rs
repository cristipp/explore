use num_bigint::{BigUint, BigInt, Sign};
use num_integer::Integer;
use num_traits::{Zero, One, ToPrimitive};
use std::io::{self, BufRead, Write, BufWriter};
use std::time::{Instant, Duration};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};

// ===== JSON helpers =====

fn parse_id(line: &str) -> String {
    if let Some(pos) = line.find("\"id\"") {
        let after = &line[pos + 4..];
        if let Some(cp) = after.find(':') {
            let s = after[cp+1..].trim_start();
            if s.starts_with('"') {
                let end = s[1..].find('"').unwrap_or(s.len()-1);
                return s[1..end+1].to_string();
            }
            let end = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
            return s[..end].to_string();
        }
    }
    String::new()
}

fn parse_n(line: &str) -> Option<BigUint> {
    let pos = line.find("\"n\"")?;
    let after = &line[pos + 3..];
    let cp = after.find(':')?;
    let s = after[cp+1..].trim_start();
    let end = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
    BigUint::parse_bytes(s[..end].as_bytes(), 10)
}

// ===== Fast modular arithmetic =====

#[inline(always)]
fn addmod(a: u64, b: u64, m: u64) -> u64 {
    let r = a.wrapping_add(b);
    if r >= m || r < a { r.wrapping_sub(m) } else { r }
}

#[inline(always)]
fn mulmod64(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

fn powmod64(mut base: u64, mut exp: u64, m: u64) -> u64 {
    let mut result = 1u64;
    base %= m;
    while exp > 0 {
        if exp & 1 == 1 { result = mulmod64(result, base, m); }
        base = mulmod64(base, base, m);
        exp >>= 1;
    }
    result
}

// Safe addmod for u128 (a, b < m <= 2^127)
#[inline(always)]
fn addmod128(a: u128, b: u128, m: u128) -> u128 {
    // a + b < 2*m. Since m may be up to ~2^126, a+b < 2^127 fits in u128.
    let r = a + b;
    if r >= m { r - m } else { r }
}

// Mulmod for u128 using binary method (safe for any m < 2^127)
fn mulmod128(mut a: u128, mut b: u128, m: u128) -> u128 {
    // Fast path: if both fit in u64, use u128 directly
    if a < (1u128 << 64) && b < (1u128 << 64) {
        return (a * b) % m;
    }
    // m < 2^127, a,b < m, so a + a < 2^128 (wrapping possible if m > 2^127, but we said m < 2^127)
    let mut result = 0u128;
    a %= m;
    b %= m;
    while b > 0 {
        if b & 1 == 1 {
            result = addmod128(result, a, m);
        }
        a = addmod128(a, a, m);
        b >>= 1;
    }
    result
}

fn powmod128(mut base: u128, mut exp: u128, m: u128) -> u128 {
    let mut result = 1u128;
    base %= m;
    while exp > 0 {
        if exp & 1 == 1 { result = mulmod128(result, base, m); }
        base = mulmod128(base, base, m);
        exp >>= 1;
    }
    result
}

// ===== Primality tests =====

fn is_prime_u64(n: u64) -> bool {
    if n < 2 { return false; }
    if n == 2 || n == 3 || n == 5 || n == 7 { return true; }
    if n % 2 == 0 || n % 3 == 0 || n % 5 == 0 { return false; }
    if n < 49 { return true; }
    // Miller-Rabin: deterministic for n < 3,215,031,751
    // Using witnesses that cover all n < 3,317,044,064,679,887,385,961,981
    let mut d = n - 1;
    let mut r = 0u32;
    while d % 2 == 0 { d /= 2; r += 1; }
    let witnesses: &[u64] = if n < 3_215_031_751 {
        &[2, 3, 5, 7]
    } else if n < 3_317_044_064_679_887_385_961_981 {
        &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    } else {
        &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    };
    'outer: for &a in witnesses {
        if a >= n { continue; }
        let mut x = powmod64(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..r-1 {
            x = mulmod64(x, x, n);
            if x == n - 1 { continue 'outer; }
        }
        return false;
    }
    true
}

fn is_prime_u128(n: u128) -> bool {
    if n <= u64::MAX as u128 {
        return is_prime_u64(n as u64);
    }
    if n % 2 == 0 || n % 3 == 0 { return false; }
    let mut d = n - 1;
    let mut r = 0u32;
    while d % 2 == 0 { d /= 2; r += 1; }
    'outer: for &a in &[2u128, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
        if a >= n { continue; }
        let mut x = powmod128(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..r-1 {
            x = mulmod128(x, x, n);
            if x == n - 1 { continue 'outer; }
        }
        return false;
    }
    true
}

fn is_prime_big(n: &BigUint) -> bool {
    if let Some(n128) = n.to_u128() {
        return is_prime_u128(n128);
    }
    let two = BigUint::from(2u32);
    let one = BigUint::one();
    if n % &two == BigUint::zero() { return false; }
    let nm1 = n - &one;
    let mut d = nm1.clone();
    let mut r = 0u32;
    while &d % &two == BigUint::zero() { d >>= 1; r += 1; }
    'outer: for &a in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
        let a_big = BigUint::from(a);
        if a_big >= *n { continue; }
        let mut x = a_big.modpow(&d, n);
        if x == one || x == nm1 { continue; }
        for _ in 0..r-1 {
            x = x.modpow(&two, n);
            if x == nm1 { continue 'outer; }
        }
        return false;
    }
    true
}

// ===== Integer square root =====

fn isqrt_big(n: &BigUint) -> BigUint {
    if n.is_zero() { return BigUint::zero(); }
    let bits = n.bits() as usize;
    let mut x = BigUint::one() << ((bits + 1) / 2);
    loop {
        let q = n / &x;
        if q >= x { return x; }
        x = (x + q) >> 1usize;
    }
}

// ===== Pollard's Rho (u64 version for n fitting in u64) =====

fn gcd64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 { let t = b; b = a % b; a = t; }
    a
}

fn pollard_brent_u64(n: u64, c: u64) -> Option<u64> {
    if n % 2 == 0 { return Some(2); }
    let mut y = 2u64;
    let mut r = 1u64;
    let mut q = 1u64;
    let mut x;
    let mut d = 1u64;
    let m = 128u64;

    loop {
        x = y;
        for _ in 0..r {
            y = mulmod64(y, y, n).wrapping_add(c);
            if y >= n { y -= n; }
        }
        let mut k = 0u64;
        loop {
            let ys = y;
            let step = m.min(r - k);
            for _ in 0..step {
                y = mulmod64(y, y, n).wrapping_add(c);
                if y >= n { y -= n; }
                let diff = if y > x { y - x } else { x - y };
                q = mulmod64(q, diff, n);
            }
            d = gcd64(q, n);
            k += m;
            if k >= r || d != 1 { break; }
        }
        if d != 1 { break; }
        r <<= 1;
        if r > 1 << 24 {
            // Backtrack approach
            let mut ys2 = ys;
            loop {
                ys2 = mulmod64(ys2, ys2, n).wrapping_add(c);
                if ys2 >= n { ys2 -= n; }
                let diff = if ys2 > x { ys2 - x } else { x - ys2 };
                d = gcd64(diff, n);
                if d != 1 { break; }
            }
            break;
        }
    }

    if d == n {
        // Backtrack
        let mut ys = y;
        loop {
            ys = mulmod64(ys, ys, n).wrapping_add(c);
            if ys >= n { ys -= n; }
            let diff = if ys > x { ys - x } else { x - ys };
            d = gcd64(diff, n);
            if d != 1 { break; }
        }
    }

    if d == 1 || d == n { None } else { Some(d) }
}

fn factor_u64(n: u64) -> Option<u64> {
    if n < 4 { return None; }
    if n % 2 == 0 { return Some(2); }
    if n % 3 == 0 { return Some(3); }
    if is_prime_u64(n) { return None; }

    for c in 1..1000u64 {
        if let Some(d) = pollard_brent_u64(n, c) {
            if d != n { return Some(d); }
        }
    }
    None
}

// ===== Pollard's Rho (u128 version) =====

fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 { let t = b; b = a % b; a = t; }
    a
}

fn pollard_brent_u128(n: u128, c: u128) -> Option<u128> {
    if n % 2 == 0 { return Some(2); }
    let mut y = 2u128;
    let mut r = 1u128;
    let mut q = 1u128;
    let mut x = 2u128;
    let mut ys = 2u128;
    let mut d = 1u128;
    let m = 128u128;

    loop {
        x = y;
        for _ in 0..r {
            y = addmod128(mulmod128(y, y, n), c, n);
        }
        let mut k = 0u128;
        loop {
            ys = y;
            let step = m.min(r - k);
            for _ in 0..step {
                y = addmod128(mulmod128(y, y, n), c, n);
                let diff = if y > x { y - x } else { x - y };
                q = mulmod128(q, diff, n);
            }
            d = gcd128(q, n);
            k += m;
            if k >= r || d != 1 { break; }
        }
        if d != 1 { break; }
        r <<= 1;
        if r > 1 << 26 { return None; }
    }

    if d == n {
        loop {
            ys = addmod128(mulmod128(ys, ys, n), c, n);
            let diff = if ys > x { ys - x } else { x - ys };
            d = gcd128(diff, n);
            if d != 1 { break; }
            // prevent infinite loop
            if ys == x { return None; }
        }
    }

    if d == 1 || d == n { None } else { Some(d) }
}

fn factor_u128_num(n: u128) -> Option<u128> {
    if n < 4 { return None; }
    if n % 2 == 0 { return Some(2); }
    if n % 3 == 0 { return Some(3); }
    if is_prime_u128(n) { return None; }

    // If fits in u64, use fast u64 version
    if n <= u64::MAX as u128 {
        return factor_u64(n as u64).map(|d| d as u128);
    }

    for c in 1..2000u128 {
        if let Some(d) = pollard_brent_u128(n, c) {
            if d != n && d != 1 { return Some(d); }
        }
    }
    None
}

// ===== Pollard's Rho (BigUint version) =====

fn pollard_brent_big(n: &BigUint, c: u64, stop: &Arc<AtomicBool>) -> Option<BigUint> {
    let one = BigUint::one();
    let c_big = BigUint::from(c);

    let f = |x: &BigUint| -> BigUint {
        let sq = x * x % n;
        let r = sq + &c_big;
        if r >= *n { r - n } else { r }
    };

    let mut y = BigUint::from(2u32);
    let mut r = 1usize;
    let mut q = one.clone();
    let mut x = BigUint::from(2u32);
    let mut ys;
    let mut d;
    let m = 256usize;

    loop {
        if stop.load(Ordering::Relaxed) { return None; }
        x = y.clone();
        for _ in 0..r {
            y = f(&y);
        }
        let mut k = 0usize;
        loop {
            ys = y.clone();
            let step = m.min(r - k);
            for _ in 0..step {
                y = f(&y);
                let diff = if y > x { y.clone() - x.clone() } else { x.clone() - y.clone() };
                q = q * diff % n;
            }
            d = q.gcd(n);
            k += m;
            if k >= r || d != one { break; }
        }
        if d != one { break; }
        r <<= 1;
        if r > 1 << 22 { return None; }
    }

    if &d == n {
        loop {
            ys = f(&ys);
            let diff = if ys > x { ys.clone() - x.clone() } else { x.clone() - ys.clone() };
            d = diff.gcd(n);
            if d != one { break; }
            if ys == x { return None; }
        }
    }

    if d == one || &d == n { None } else { Some(d) }
}

// ===== Quadratic Sieve =====

fn sieve_primes_small(limit: usize) -> Vec<u32> {
    if limit < 2 { return vec![]; }
    let mut sieve = vec![true; limit + 1];
    sieve[0] = false;
    if limit > 0 { sieve[1] = false; }
    let mut i = 2usize;
    while i * i <= limit {
        if sieve[i] {
            let mut j = i * i;
            while j <= limit { sieve[j] = false; j += i; }
        }
        i += 1;
    }
    (2..=limit).filter(|&i| sieve[i]).map(|i| i as u32).collect()
}

fn jacobi(mut a: i64, mut n: i64) -> i32 {
    if n <= 0 || n % 2 == 0 { return 0; }
    let mut result = 1i32;
    a = ((a % n) + n) % n;
    while a != 0 {
        while a % 2 == 0 {
            a /= 2;
            let nm8 = n % 8;
            if nm8 == 3 || nm8 == 5 { result = -result; }
        }
        std::mem::swap(&mut a, &mut n);
        if a % 4 == 3 && n % 4 == 3 { result = -result; }
        a %= n;
    }
    if n == 1 { result } else { 0 }
}

fn tonelli_shanks(n: u64, p: u64) -> u64 {
    // Returns r such that r^2 ≡ n (mod p)
    if n == 0 { return 0; }
    if p == 2 { return n & 1; }
    if p % 4 == 3 {
        return powmod64(n, (p + 1) / 4, p);
    }
    if p % 8 == 5 {
        let v = powmod64(2 * n % p, (p - 5) / 8, p);
        let i = mulmod64(mulmod64(2 * n % p, v, p), v, p);
        return mulmod64(mulmod64(n, v, p), (i + p - 1) % p, p);
    }
    // General Tonelli-Shanks
    let mut q = p - 1;
    let mut s = 0u32;
    while q % 2 == 0 { q /= 2; s += 1; }

    let mut z = 2u64;
    while powmod64(z, (p - 1) / 2, p) != p - 1 { z += 1; }

    let mut m = s;
    let mut c = powmod64(z, q, p);
    let mut t = powmod64(n, q, p);
    let mut r = powmod64(n, (q + 1) / 2, p);

    loop {
        if t == 0 { return 0; }
        if t == 1 { return r; }
        let mut i = 1u32;
        let mut tmp = mulmod64(t, t, p);
        while tmp != 1 { tmp = mulmod64(tmp, tmp, p); i += 1; }
        if i >= m { return p; } // shouldn't happen
        let b = powmod64(c, 1u64 << (m - i - 1), p);
        m = i;
        c = mulmod64(b, b, p);
        t = mulmod64(t, c, p);
        r = mulmod64(r, b, p);
    }
}

fn biguint_mod_u64(n: &BigUint, m: u64) -> u64 {
    (n % BigUint::from(m)).to_u64().unwrap_or(0)
}

fn qs_params(n_digits: usize) -> (usize, usize) {
    // Optimal smoothness bound for MPQS: B = L^(1/sqrt(2)) where L = exp(sqrt(ln(n)*ln(ln(n))))
    let ln_n = n_digits as f64 * 2.302585;
    let ln_ln_n = ln_n.ln().max(1.0);
    let exponent = 0.5f64 * (ln_n * ln_ln_n).sqrt(); // This is 0.5 * sqrt(...)
    let b = exponent.exp() as usize;
    // For practical MPQS, we often use a slightly smaller B
    let b = b.max(200).min(5_000_000);
    let m = (b * 30).max(100_000).min(30_000_000);
    (b, m)
}

fn quadratic_sieve(n: &BigUint, deadline: Instant) -> Option<BigUint> {
    let one = BigUint::one();

    let n_str = n.to_str_radix(10);
    let n_digits = n_str.len();

    if n_digits < 8 { return None; }

    let (b_bound, m_half) = qs_params(n_digits);

    // Generate factor base: 2 and odd primes where n is QR
    let all_primes = sieve_primes_small(b_bound);

    let mut factor_base: Vec<u32> = vec![2];
    for &p in &all_primes[1..] {
        let p64 = p as u64;
        let n_mod = biguint_mod_u64(n, p64) as i64;
        if jacobi(n_mod, p64 as i64) == 1 {
            factor_base.push(p);
        }
    }

    let fb_size = factor_base.len();
    if fb_size < 20 { return None; }

    let sqrt_n = isqrt_big(n);
    let base = &sqrt_n + &one; // Q(x) = (base + x)^2 - n, for x = 0, 1, 2, ...

    // For each prime p, compute:
    // - log(p) for sieve
    // - start positions: (base + x) ≡ ±sqrt(n) (mod p), i.e., x ≡ ±r - base (mod p)
    struct FbEntry {
        p: u32,
        log_p: f32,
        r1: u32, // first root (base + r1) ≡ sqrt(n) mod p
        r2: u32, // second root
    }

    let base_mod_p: Vec<u64> = factor_base.iter().map(|&p| {
        biguint_mod_u64(&base, p as u64)
    }).collect();

    let fb_entries: Vec<FbEntry> = factor_base.iter().enumerate().map(|(i, &p)| {
        let p64 = p as u64;
        let log_p = (p as f64).ln() as f32;

        if p == 2 {
            let bm = base_mod_p[i];
            let r = biguint_mod_u64(n, 2);
            // x ≡ r - bm (mod 2)
            let r1 = ((r as i64 - bm as i64).rem_euclid(2)) as u32;
            FbEntry { p, log_p, r1, r2: r1 }
        } else {
            let bm = base_mod_p[i];
            let n_mod = biguint_mod_u64(n, p64);
            let r = tonelli_shanks(n_mod, p64);
            if r >= p64 {
                // No sqrt, shouldn't happen since we filtered by Jacobi
                FbEntry { p, log_p, r1: 0, r2: 0 }
            } else {
                // x ≡ r - bm (mod p) or x ≡ (p-r) - bm (mod p)
                let r1 = ((r as i64 - bm as i64).rem_euclid(p64 as i64)) as u32;
                let r2 = (((p64 - r) as i64 - bm as i64).rem_euclid(p64 as i64)) as u32;
                FbEntry { p, log_p, r1, r2 }
            }
        }
    }).collect();

    // Threshold: log of what a smooth number should have
    // Q(x) = (base + x)^2 - n ≈ 2 * sqrt_n * x + x^2
    // For x in [0, M], Q(x) ≈ 2 * sqrt_n * M
    // log(Q(x)) ≈ log(2 * sqrt_n * M) ≈ log(n)/2 + log(M)
    let log_q_approx = (n_digits as f32 * 2.302585 / 2.0) + (m_half as f64).ln() as f32;
    let threshold = log_q_approx * 0.85; // 85% - allow for small slack

    // Collection phase
    let need = fb_size + 50;

    struct Relation {
        a: BigUint,       // a = base + x
        exp_vec: Vec<u8>, // exponents mod 2 over factor base
        full_exp: Vec<u32>, // full exponents (for square root computation)
    }

    let mut relations: Vec<Relation> = Vec::with_capacity(need + 20);
    let sieve_len = m_half * 2;
    let mut sieve_buf = vec![0.0f32; sieve_len];

    // We sieve in chunks of sieve_len, starting at x=0, then x=sieve_len, etc.
    let mut chunk_start: i64 = 0;

    while relations.len() < need {
        if Instant::now() > deadline { break; }

        // Reset sieve
        for v in &mut sieve_buf { *v = 0.0; }

        // Fill sieve
        for fe in &fb_entries {
            let p = fe.p as usize;
            let lp = fe.log_p;

            // Find first position >= chunk_start for each root
            let start1 = ((fe.r1 as i64 - chunk_start).rem_euclid(p as i64)) as usize;
            let start2 = ((fe.r2 as i64 - chunk_start).rem_euclid(p as i64)) as usize;

            let mut j = start1;
            while j < sieve_len { sieve_buf[j] += lp; j += p; }
            if start1 != start2 {
                let mut j = start2;
                while j < sieve_len { sieve_buf[j] += lp; j += p; }
            }
        }

        // Find smooth candidates
        for i in 0..sieve_len {
            if sieve_buf[i] < threshold { continue; }

            let x = chunk_start + i as i64;
            // a = base + x
            let a = if x >= 0 {
                &base + BigUint::from(x as u64)
            } else {
                // x < 0 shouldn't happen in our setup (chunk_start >= 0)
                continue;
            };

            // Q(x) = a^2 - n (always >= 0 since a >= base = sqrt_n + 1)
            let a_sq = &a * &a;
            if a_sq < *n { continue; }
            let mut qx = a_sq - n;
            if qx.is_zero() { continue; }

            // Factor qx over factor base
            let mut full_exp = vec![0u32; fb_size];
            let mut ev = vec![0u8; fb_size];

            for (idx, &p) in factor_base.iter().enumerate() {
                let p_big = BigUint::from(p as u64);
                let mut cnt = 0u32;
                while &qx % &p_big == BigUint::zero() {
                    qx /= &p_big;
                    cnt += 1;
                }
                full_exp[idx] = cnt;
                ev[idx] = (cnt & 1) as u8;
            }

            if qx != one { continue; } // not smooth

            relations.push(Relation { a: a.clone(), exp_vec: ev, full_exp });

            if relations.len() >= need {
                break;
            }
        }

        chunk_start += sieve_len as i64;

        // Don't sieve too far
        if chunk_start > 1_000_000_000 { break; }
    }

    if relations.len() < fb_size / 2 { return None; }

    // Gaussian elimination over GF(2)
    let nrows = relations.len();
    let ncols = fb_size;
    let words = (ncols + 63) / 64;

    let mut matrix: Vec<Vec<u64>> = relations.iter().map(|r| {
        let mut row = vec![0u64; words];
        for j in 0..ncols {
            if r.exp_vec[j] == 1 {
                row[j / 64] |= 1u64 << (j % 64);
            }
        }
        row
    }).collect();

    // Track which original rows combine to give each current row
    let mut history: Vec<Vec<usize>> = (0..nrows).map(|i| vec![i]).collect();

    let mut pivot_rows = vec![usize::MAX; ncols]; // pivot_rows[col] = row index
    let mut cur_row = 0;

    for col in 0..ncols {
        if cur_row >= nrows { break; }
        // Find pivot
        let pivot = (cur_row..nrows).find(|&r| (matrix[r][col / 64] >> (col % 64)) & 1 == 1);
        if let Some(p) = pivot {
            matrix.swap(cur_row, p);
            history.swap(cur_row, p);
            pivot_rows[col] = cur_row;
            // Eliminate
            for r in 0..nrows {
                if r != cur_row && (matrix[r][col / 64] >> (col % 64)) & 1 == 1 {
                    for w in 0..words {
                        let val = matrix[cur_row][w];
                        matrix[r][w] ^= val;
                    }
                    // Symmetric difference of history
                    let h_cur = history[cur_row].clone();
                    for &idx in &h_cur {
                        if let Some(pos) = history[r].iter().position(|&x| x == idx) {
                            history[r].remove(pos);
                        } else {
                            history[r].push(idx);
                        }
                    }
                }
            }
            cur_row += 1;
        }
    }

    // Find zero rows
    let n_bigint = BigInt::from_biguint(Sign::Plus, n.clone());

    for row_idx in 0..nrows {
        let is_zero = matrix[row_idx].iter().all(|&w| w == 0);
        if !is_zero { continue; }
        let contrib = &history[row_idx];
        if contrib.is_empty() { continue; }

        // Compute x = product of a_i mod n
        let mut x = BigInt::from(1i32);
        for &ri in contrib {
            x = x * BigInt::from_biguint(Sign::Plus, relations[ri].a.clone());
            x = x % &n_bigint;
        }

        // Compute combined exponents and verify they're all even
        let mut total_exp = vec![0u32; fb_size];
        for &ri in contrib {
            for j in 0..fb_size {
                total_exp[j] += relations[ri].full_exp[j];
            }
        }

        if total_exp.iter().any(|&e| e % 2 != 0) { continue; }

        // Compute y = product of p_i^(e_i/2)
        let mut y = BigInt::from(1i32);
        for j in 0..fb_size {
            let half = total_exp[j] / 2;
            if half > 0 {
                let p_pow = BigUint::from(factor_base[j] as u64).pow(half);
                y = y * BigInt::from_biguint(Sign::Plus, p_pow);
            }
        }
        y = ((y % &n_bigint) + &n_bigint) % &n_bigint;
        x = ((x % &n_bigint) + &n_bigint) % &n_bigint;

        let xb = x.magnitude().clone();
        let yb = y.magnitude().clone();

        // Try gcd(x-y, n) and gcd(x+y, n)
        let diff = if xb > yb { (xb.clone() - yb.clone()).gcd(n) } else { (yb.clone() - xb.clone()).gcd(n) };
        if diff != one && &diff != n { return Some(diff); }

        let sum = (xb + yb).gcd(n);
        if sum != one && &sum != n { return Some(sum); }
    }

    None
}

// ===== Trial division =====

fn trial_divide(n: &BigUint) -> Option<BigUint> {
    // Check small primes up to 10000
    let small: Vec<u32> = sieve_primes_small(10000);
    for p in small {
        let p_big = BigUint::from(p as u64);
        if n % &p_big == BigUint::zero() && n != &p_big {
            return Some(p_big);
        }
    }
    None
}

// ===== Main factoring function =====

fn factor_number(n: &BigUint, deadline: Instant, stop: &Arc<AtomicBool>) -> Option<BigUint> {
    let one = BigUint::one();
    if n <= &one { return None; }

    // Trial division
    if let Some(d) = trial_divide(n) {
        return Some(d);
    }

    if is_prime_big(n) { return None; }

    // Fast path: u64
    if let Some(n64) = n.to_u64() {
        return factor_u64(n64).map(BigUint::from);
    }

    // Fast path: u128
    if let Some(n128) = n.to_u128() {
        return factor_u128_num(n128).map(|d| BigUint::from(d));
    }

    // BigUint Pollard's rho (parallel)
    let n_str = n.to_str_radix(10);
    let n_digits = n_str.len();

    let n_arc = Arc::new(n.clone());
    let result = Arc::new(Mutex::new(None::<BigUint>));
    let stop_flag = Arc::new(AtomicBool::new(false));

    // Run Pollard's rho in parallel threads
    let n_threads = 8usize;
    let mut handles = Vec::new();

    for tid in 0..n_threads {
        let n_c = Arc::clone(&n_arc);
        let res_c = Arc::clone(&result);
        let sf = Arc::clone(&stop_flag);

        handles.push(std::thread::spawn(move || {
            for c in (tid as u64 + 1..).step_by(n_threads).take(500) {
                if sf.load(Ordering::Relaxed) { return; }
                if let Some(d) = pollard_brent_big(&n_c, c, &sf) {
                    let mut r = res_c.lock().unwrap();
                    if r.is_none() { *r = Some(d); }
                    sf.store(true, Ordering::Relaxed);
                    return;
                }
            }
        }));
    }

    // Determine Pollard rho time budget
    // For n_digits <= 40, Pollard should work fast; for larger, use QS
    let pollard_budget = if n_digits <= 30 {
        Duration::from_secs(30)
    } else if n_digits <= 50 {
        Duration::from_secs(5)
    } else {
        Duration::from_secs(2)
    };

    let poll_deadline = Instant::now() + pollard_budget;
    loop {
        if stop_flag.load(Ordering::Relaxed) { break; }
        if Instant::now() >= poll_deadline.min(deadline) { break; }
        if stop.load(Ordering::Relaxed) { break; }
        std::thread::sleep(Duration::from_millis(5));
    }
    stop_flag.store(true, Ordering::Relaxed);
    for h in handles { let _ = h.join(); }

    let rho_result = result.lock().unwrap().clone();
    if rho_result.is_some() { return rho_result; }

    // QS for larger numbers
    if Instant::now() < deadline && !stop.load(Ordering::Relaxed) {
        return quadratic_sieve(n, deadline);
    }

    None
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut tl_secs = 60.0f64;
    for i in 0..args.len() {
        if args[i] == "--time-limit" && i + 1 < args.len() {
            tl_secs = args[i+1].parse().unwrap_or(60.0);
        }
    }
    let time_limit = Duration::from_secs_f64(tl_secs);
    let global_start = Instant::now();

    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    let global_stop = Arc::new(AtomicBool::new(false));

    for line in io::stdin().lock().lines() {
        let line = match line { Ok(l) => l, Err(_) => break };
        let line = line.trim().to_string();
        if line.is_empty() { continue; }

        let id = parse_id(&line);
        let n = match parse_n(&line) { Some(n) => n, None => continue };

        let elapsed = global_start.elapsed();
        if elapsed >= time_limit {
            writeln!(out, "{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}", id).unwrap();
            out.flush().unwrap();
            continue;
        }

        let remaining = time_limit - elapsed;
        let per_q = remaining.min(Duration::from_secs_f64(tl_secs * 0.98));
        let deadline = Instant::now() + per_q;

        let factor = factor_number(&n, deadline, &global_stop);

        match factor {
            Some(p) => {
                let q = &n / &p;
                let (lo, hi) = if p < q { (p, q) } else { (q, p) };
                writeln!(out, "{{\"id\": \"{}\", \"answer\": \"{} {}\"}}", id, lo, hi).unwrap();
            }
            None => {
                if global_start.elapsed() >= time_limit {
                    writeln!(out, "{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}", id).unwrap();
                } else {
                    writeln!(out, "{{\"id\": \"{}\", \"answer\": null}}", id).unwrap();
                }
            }
        }
        out.flush().unwrap();
    }
}
