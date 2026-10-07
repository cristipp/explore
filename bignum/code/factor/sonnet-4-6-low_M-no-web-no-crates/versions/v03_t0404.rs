use num_bigint::{BigUint, BigInt, Sign};
use num_integer::Integer;
use num_traits::{Zero, One, ToPrimitive, FromPrimitive};
use std::io::{self, BufRead, Write, BufWriter};
use std::time::{Instant, Duration};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};

// ===== JSON parsing helpers =====

fn extract_field<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let key_pat = format!("\"{}\"", key);
    let pos = line.find(&key_pat)?;
    let after = &line[pos + key_pat.len()..];
    let colon = after.find(':')? ;
    let val_start = after[colon+1..].trim_start();
    Some(val_start)
}

fn parse_id(line: &str) -> String {
    if let Some(s) = extract_field(line, "id") {
        if s.starts_with('"') {
            let end = s[1..].find('"').unwrap_or(s.len()-1);
            return s[1..end+1].to_string();
        }
        // numeric id
        let end = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
        return s[..end].to_string();
    }
    String::new()
}

fn parse_n(line: &str) -> Option<BigUint> {
    let s = extract_field(line, "n")?;
    // trim to just the number
    let s = s.trim_start();
    let end = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
    let num_str = &s[..end];
    BigUint::parse_bytes(num_str.as_bytes(), 10)
}

// ===== Primality (Miller-Rabin) =====

fn mod_mul_u128(a: u128, b: u128, m: u128) -> u128 {
    // Use u128 with potential overflow via checked arithmetic
    // For m up to 2^63, a*b fits in u128. For larger, use BigUint.
    if m <= (1u128 << 63) {
        return (a as u128 * b as u128) % m;
    }
    // Use __uint128 style via BigUint fallback
    let r = (a as u128).wrapping_mul(b as u128);
    // Check for overflow
    if a == 0 || r / a == b {
        r % m
    } else {
        // overflow - use u128 with 256-bit intermediate via splitting
        // a*b = (a_hi*2^64 + a_lo) * b
        let a_lo = a & 0xffffffffffffffff;
        let a_hi = a >> 64;
        let lo = (a_lo.wrapping_mul(b)) % m;
        // a_hi * b * 2^64 mod m
        let mut hi = a_hi.wrapping_mul(b) % m;
        // multiply hi by 2^64 mod m
        for _ in 0..64 {
            hi = hi.wrapping_add(hi);
            if hi >= m { hi = hi.wrapping_sub(m); }
        }
        (lo + hi) % m
    }
}

fn mod_pow_u128(mut base: u128, mut exp: u128, m: u128) -> u128 {
    let mut result = 1u128;
    base %= m;
    while exp > 0 {
        if exp & 1 == 1 { result = mod_mul_u128(result, base, m); }
        base = mod_mul_u128(base, base, m);
        exp >>= 1;
    }
    result
}

fn is_prime_u64(n: u64) -> bool {
    if n < 2 { return false; }
    if n == 2 || n == 3 || n == 5 || n == 7 { return true; }
    if n % 2 == 0 || n % 3 == 0 || n % 5 == 0 { return false; }
    // Deterministic witnesses for n < 3,317,044,064,679,887,385,961,981
    let n128 = n as u128;
    let mut d = n - 1;
    let mut r = 0u32;
    while d % 2 == 0 { d /= 2; r += 1; }
    'outer: for &a in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if a >= n { continue; }
        let mut x = mod_pow_u128(a as u128, d as u128, n128) as u64;
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..r-1 {
            x = mod_mul_u128(x as u128, x as u128, n128) as u64;
            if x == n - 1 { continue 'outer; }
        }
        return false;
    }
    true
}

fn is_prime_big(n: &BigUint) -> bool {
    if let Some(n64) = n.to_u64() {
        return is_prime_u64(n64);
    }
    let two = BigUint::from(2u32);
    let one = BigUint::one();
    if n % &two == BigUint::zero() { return false; }
    // Miller-Rabin with multiple witnesses
    let nm1 = n - &one;
    let mut d = nm1.clone();
    let mut r = 0u32;
    while &d % &two == BigUint::zero() { d >>= 1; r += 1; }

    let witnesses: &[u64] = &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
    'outer: for &a in witnesses {
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
    let bits = n.bits();
    let mut x = BigUint::one() << ((bits + 1) / 2) as usize;
    loop {
        let x1 = (&x + n / &x) >> 1usize;
        if x1 >= x { return x; }
        x = x1;
    }
}

// ===== Pollard's Rho (u128 version for small n) =====

fn pollard_rho_u128(n: u128, c: u128) -> Option<u128> {
    if n % 2 == 0 { return Some(2); }
    let mut y = 2u128;
    let mut d = 1u128;
    let mut q = 1u128;
    let mut x = 2u128;
    let m = 512u128;
    let mut r = 1u128;

    'outer: loop {
        x = y;
        for _ in 0..r {
            y = (mod_mul_u128(y, y, n) + c) % n;
        }
        let mut k = 0u128;
        loop {
            let ys = y;
            let step = m.min(r - k);
            for _ in 0..step {
                y = (mod_mul_u128(y, y, n) + c) % n;
                let diff = if y > x { y - x } else { x - y };
                q = mod_mul_u128(q, diff, n);
            }
            d = gcd_u128(q, n);
            k += m;
            if k >= r || d != 1 { break; }
        }
        if d != 1 { break; }
        r <<= 1;
        if r > 1 << 30 { break 'outer; }
    }

    if d == n {
        // backtrack
        let mut ys = 2u128;
        for _ in 0..1000000 {
            ys = (mod_mul_u128(ys, ys, n) + c) % n;
            let diff = if ys > x { ys - x } else { x - ys };
            d = gcd_u128(diff, n);
            if d != 1 { break; }
        }
    }

    if d == 1 || d == n { None } else { Some(d) }
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 { let t = b; b = a % b; a = t; }
    a
}

fn factor_u128(n: u128) -> Option<(u128, u128)> {
    if n < 2 { return None; }
    if is_prime_u64(n as u64) { return None; } // n is prime, not composite

    // Trial division
    for p in [2u128, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
        if n % p == 0 { return Some((p, n/p)); }
    }

    // Pollard's rho
    for c in 1..200u128 {
        if let Some(d) = pollard_rho_u128(n, c) {
            let p = d;
            let q = n / p;
            return Some((p.min(q), p.max(q)));
        }
    }
    None
}

// ===== Pollard's Rho (BigUint version) =====

fn pollard_rho_big(n: &BigUint, c: &BigUint, stop: &Arc<AtomicBool>) -> Option<BigUint> {
    let one = BigUint::one();
    let two = BigUint::from(2u32);

    let f = |x: &BigUint| -> BigUint { (x * x + c) % n };

    let mut x = two.clone();
    let mut y = two.clone();
    let mut d = one.clone();
    let m = BigUint::from(1024u32);
    let mut r = one.clone();
    let mut q = one.clone();

    'outer: loop {
        if stop.load(Ordering::Relaxed) { return None; }
        x = y.clone();
        let r_val = r.to_usize().unwrap_or(usize::MAX);
        for _ in 0..r_val.min(1<<20) {
            y = f(&y);
        }
        let mut k = BigUint::zero();
        loop {
            if stop.load(Ordering::Relaxed) { return None; }
            let ys = y.clone();
            let step = m.clone().min(r.clone() - k.clone());
            let step_val = step.to_usize().unwrap_or(1024);
            let mut saved_y = y.clone();
            for _ in 0..step_val {
                y = f(&y);
                let diff = if y > x { y.clone() - x.clone() } else { x.clone() - y.clone() };
                q = q * &diff % n;
            }
            d = q.gcd(n);
            k += m.clone();
            if k >= r || d != one { break; }
        }
        if d != one { break; }
        r <<= 1usize;
        if r.bits() > 25 { break 'outer; } // give up after 2^25 steps
    }

    if &d == n {
        // backtrack with smaller steps
        let mut ys = y.clone();
        for _ in 0..100000 {
            ys = f(&ys);
            let diff = if ys > x { ys.clone() - x.clone() } else { x.clone() - ys.clone() };
            d = diff.gcd(n);
            if d != one { break; }
        }
    }

    if d == one || &d == n { None } else { Some(d) }
}

// ===== Quadratic Sieve =====

fn sieve_primes(limit: usize) -> Vec<u32> {
    if limit < 2 { return vec![]; }
    let mut is_prime = vec![true; limit + 1];
    is_prime[0] = false;
    if limit > 0 { is_prime[1] = false; }
    let mut i = 2;
    while i * i <= limit {
        if is_prime[i] {
            let mut j = i * i;
            while j <= limit {
                is_prime[j] = false;
                j += i;
            }
        }
        i += 1;
    }
    (2..=limit).filter(|&i| is_prime[i]).map(|i| i as u32).collect()
}

fn jacobi(mut a: i64, mut n: i64) -> i32 {
    if n <= 0 || n % 2 == 0 { return 0; }
    let mut result = 1i32;
    a %= n;
    while a != 0 {
        while a % 2 == 0 {
            a /= 2;
            let nm = n % 8;
            if nm == 3 || nm == 5 { result = -result; }
        }
        std::mem::swap(&mut a, &mut n);
        if a % 4 == 3 && n % 4 == 3 { result = -result; }
        a %= n;
    }
    if n == 1 { result } else { 0 }
}

fn tonelli_shanks(n: u64, p: u64) -> u64 {
    if n == 0 { return 0; }
    if p == 2 { return n & 1; }
    // Find square root of n mod p using Tonelli-Shanks
    if mod_pow_u128(n as u128, (p-1) as u128 / 2, p as u128) != 1 {
        return p; // no square root (should not happen since we filtered by Jacobi)
    }
    if p % 4 == 3 {
        return mod_pow_u128(n as u128, (p+1) as u128 / 4, p as u128) as u64;
    }
    // Factor out 2s from p-1
    let mut q = p - 1;
    let mut s = 0u32;
    while q % 2 == 0 { q /= 2; s += 1; }

    // Find a quadratic non-residue
    let mut z = 2u64;
    while mod_pow_u128(z as u128, (p-1) as u128 / 2, p as u128) != p as u128 - 1 {
        z += 1;
    }

    let mut m = s;
    let mut c = mod_pow_u128(z as u128, q as u128, p as u128) as u64;
    let mut t = mod_pow_u128(n as u128, q as u128, p as u128) as u64;
    let mut r = mod_pow_u128(n as u128, (q+1) as u128 / 2, p as u128) as u64;

    loop {
        if t == 1 { return r; }
        // Find least i such that t^(2^i) == 1
        let mut i = 1u32;
        let mut tmp = mod_mul_u128(t as u128, t as u128, p as u128) as u64;
        while tmp != 1 {
            tmp = mod_mul_u128(tmp as u128, tmp as u128, p as u128) as u64;
            i += 1;
        }
        let b_exp = 1u64 << (m - i - 1);
        let b = mod_pow_u128(c as u128, b_exp as u128, p as u128) as u64;
        m = i;
        c = mod_mul_u128(b as u128, b as u128, p as u128) as u64;
        t = mod_mul_u128(t as u128, c as u128, p as u128) as u64;
        r = mod_mul_u128(r as u128, b as u128, p as u128) as u64;
    }
}

fn qs_params(n_digits: usize) -> (usize, usize, f64) {
    // Returns (B, M, threshold_factor)
    // B = smoothness bound (factor base limit)
    // M = sieve half-width
    let ln_n = n_digits as f64 * 2.302585;
    let ln_ln_n = ln_n.ln();
    let u = (0.5 * (ln_n * ln_ln_n).sqrt()).exp();
    let b = (u.powf(0.5) as usize).max(200).min(2_000_000);
    let m = (b * 10).max(50_000).min(10_000_000);
    (b, m, 0.85)
}

// Convert BigUint to i128 for modular arithmetic (value must fit)
fn biguint_mod_i64(n: &BigUint, m: u64) -> u64 {
    (n % BigUint::from(m)).to_u64().unwrap_or(0)
}

struct QsRelation {
    a: BigInt, // a such that a^2 - n factors over factor base
    exp_vec: Vec<u8>, // exponents mod 2 for each prime in factor base
}

fn quadratic_sieve(n: &BigUint, timeout: Duration, start_time: Instant) -> Option<BigUint> {
    let one = BigUint::one();
    let two = BigUint::from(2u32);

    // Number of decimal digits
    let n_str = n.to_str_radix(10);
    let n_digits = n_str.len();

    if n_digits < 10 {
        // Too small for QS, but shouldn't reach here
        return None;
    }

    let (b_bound, m_half, thresh_factor) = qs_params(n_digits);

    // Generate factor base
    let all_primes = sieve_primes(b_bound);

    // Filter: keep primes where n is a QR (Jacobi symbol = 1), plus 2
    let mut factor_base: Vec<u64> = Vec::with_capacity(all_primes.len() / 3);
    factor_base.push(2);
    for &p in &all_primes[1..] { // skip 2
        let p64 = p as u64;
        let n_mod = biguint_mod_i64(n, p64);
        if jacobi(n_mod as i64, p64 as i64) == 1 {
            factor_base.push(p64);
        }
    }

    let fb_size = factor_base.len();
    if fb_size < 50 { return None; }

    // Compute sqrt(n) (integer part)
    let sqrt_n = isqrt_big(n);

    // Precompute log(p) for each factor base prime
    let log_p: Vec<f32> = factor_base.iter().map(|&p| (p as f64).ln() as f32).collect();

    // Compute the sieve starting offsets for each prime
    // Q(x) = (sqrt_n + 1 + x)^2 - n  for x = 0, 1, 2, ...
    // Also Q(-x) via symmetric approach
    // Q(x) = 0 when (sqrt_n+1+x)^2 = n, which doesn't happen for proper semiprimes
    // We sieve: for prime p, Q(x) ≡ 0 (mod p) when (sqrt_n+1+x) ≡ ±sqrt(n) (mod p)

    let base_val = &sqrt_n + &one; // sieve base: Q(x) = (base_val + x)^2 - n

    // For each prime p, find starting positions in sieve [0, 2*M)
    // (base_val + x)^2 ≡ n (mod p)
    // base_val + x ≡ ±r_p (mod p)
    // x ≡ r_p - base_val (mod p)  or  x ≡ -r_p - base_val (mod p)

    struct PrimeInfo {
        p: u64,
        start1: usize, // first hit in sieve
        start2: usize, // second hit
        log_val: f32,
    }

    let base_mod: Vec<u64> = factor_base.iter().map(|&p| {
        biguint_mod_i64(&base_val, p)
    }).collect();

    let sqrt_mod: Vec<u64> = factor_base.iter().enumerate().map(|(i, &p)| {
        if p == 2 {
            // For p=2, just 1
            biguint_mod_i64(n, 2)
        } else {
            let n_mod = biguint_mod_i64(n, p);
            tonelli_shanks(n_mod, p)
        }
    }).collect();

    // We need to collect fb_size + extra_margin smooth relations
    let extra = fb_size / 4 + 20;
    let need = fb_size + extra;

    let mut relations: Vec<QsRelation> = Vec::new();
    let sieve_size = m_half * 2;
    let mut sieve: Vec<f32> = vec![0.0; sieve_size];

    // Compute target threshold: log(Q(x)) ≈ log((sqrt_n + M)^2 - n) ≈ log(2 * sqrt_n * M)
    let log_n_half = n_digits as f32 * 2.302585 / 2.0;
    let log_m = (m_half as f64).ln() as f32;
    let threshold = (log_n_half + log_m) * thresh_factor as f32;

    // Multiple polynomial SIQS approach: iterate over sieve intervals
    let mut offset: i64 = 0; // current sieve starting x

    while relations.len() < need {
        if start_time.elapsed() > timeout { break; }

        // Reset sieve
        for v in sieve.iter_mut() { *v = 0.0; }

        // Fill sieve with log contributions
        for i in 0..fb_size {
            let p = factor_base[i];
            let lp = log_p[i];

            if p == 2 {
                // Every other x
                let start = if (offset % 2).abs() as u64 == (base_mod[i] % 2) { 0 } else { 1 };
                let mut j = start as usize;
                while j < sieve_size { sieve[j] += lp; j += 2; }
                continue;
            }

            // Compute starting positions relative to current offset
            let bm = base_mod[i];
            let r = sqrt_mod[i];
            if r >= p { continue; } // no sqrt exists

            // x ≡ r - bm (mod p)
            let x1_raw = (r as i64 - bm as i64).rem_euclid(p as i64) as u64;
            let x2_raw = ((p - r) as i64 - bm as i64).rem_euclid(p as i64) as u64;

            // Adjust for current offset
            let start1 = ((x1_raw as i64 - offset).rem_euclid(p as i64)) as usize;
            let start2 = ((x2_raw as i64 - offset).rem_euclid(p as i64)) as usize;

            let p_usize = p as usize;
            let mut j = start1;
            while j < sieve_size { sieve[j] += lp; j += p_usize; }
            if start1 != start2 {
                let mut j = start2;
                while j < sieve_size { sieve[j] += lp; j += p_usize; }
            }
        }

        // Find smooth candidates
        for xi in 0..sieve_size {
            if sieve[xi] < threshold { continue; }

            let x = offset + xi as i64;
            // Compute Q(x) = (base_val + x)^2 - n
            let ax = if x >= 0 {
                &base_val + BigUint::from(x as u64)
            } else {
                &base_val - BigUint::from((-x) as u64)
            };
            let qx_big = &ax * &ax;
            if qx_big < *n { continue; } // shouldn't happen for balanced case
            let mut qx = qx_big - n;

            if qx.is_zero() { continue; }

            // Try to factor qx over the factor base
            let mut exp_vec = vec![0u8; fb_size];
            let mut smooth = true;

            for i in 0..fb_size {
                let p = factor_base[i];
                let p_big = BigUint::from(p);
                let mut cnt = 0u8;
                while &qx % &p_big == BigUint::zero() {
                    qx /= &p_big;
                    cnt += 1;
                }
                exp_vec[i] = cnt & 1; // mod 2
            }

            if qx != one {
                // Not smooth - large prime variant: if qx is prime and small enough, record partial
                // For now, skip
                continue;
            }

            relations.push(QsRelation {
                a: BigInt::from_biguint(Sign::Plus, ax),
                exp_vec,
            });

            if relations.len() >= need { break; }
        }

        offset += sieve_size as i64;

        // Also sieve negative side
        if relations.len() < need && start_time.elapsed() < timeout {
            for v in sieve.iter_mut() { *v = 0.0; }
            let neg_offset = -(offset);

            for i in 0..fb_size {
                let p = factor_base[i];
                let lp = log_p[i];
                if p == 2 {
                    let start = if (neg_offset % 2).abs() as u64 == base_mod[i] % 2 { 0 } else { 1 };
                    let mut j = start as usize;
                    while j < sieve_size { sieve[j] += lp; j += 2; }
                    continue;
                }
                let bm = base_mod[i];
                let r = sqrt_mod[i];
                if r >= p { continue; }
                let x1_raw = (r as i64 - bm as i64).rem_euclid(p as i64) as u64;
                let x2_raw = ((p - r) as i64 - bm as i64).rem_euclid(p as i64) as u64;
                let start1 = ((x1_raw as i64 - neg_offset).rem_euclid(p as i64)) as usize;
                let start2 = ((x2_raw as i64 - neg_offset).rem_euclid(p as i64)) as usize;
                let p_usize = p as usize;
                let mut j = start1;
                while j < sieve_size { sieve[j] += lp; j += p_usize; }
                if start1 != start2 {
                    let mut j = start2;
                    while j < sieve_size { sieve[j] += lp; j += p_usize; }
                }
            }

            for xi in 0..sieve_size {
                if sieve[xi] < threshold { continue; }
                let x = neg_offset + xi as i64;
                let ax = if x >= 0 {
                    BigInt::from_biguint(Sign::Plus, &base_val + BigUint::from(x as u64))
                } else {
                    BigInt::from_biguint(Sign::Minus, &base_val - BigUint::from((-x) as u64))
                };
                // Q(x) = ax^2 - n (can be negative for negative ax < sqrt(n))
                let ax_abs = ax.magnitude().clone();
                let qx_big = &ax_abs * &ax_abs;
                let mut qx = if qx_big >= *n {
                    qx_big - n
                } else {
                    continue; // skip
                };
                if qx.is_zero() { continue; }

                let mut exp_vec = vec![0u8; fb_size];
                for i in 0..fb_size {
                    let p_big = BigUint::from(factor_base[i]);
                    let mut cnt = 0u8;
                    while &qx % &p_big == BigUint::zero() {
                        qx /= &p_big;
                        cnt += 1;
                    }
                    exp_vec[i] = cnt & 1;
                }
                if qx != one { continue; }

                relations.push(QsRelation {
                    a: ax,
                    exp_vec,
                });
                if relations.len() >= need { break; }
            }
        }
    }

    if relations.len() < fb_size + 1 {
        return None;
    }

    // Gaussian elimination over GF(2) to find null vector
    let nrows = relations.len();
    let ncols = fb_size;

    // Represent matrix as bit-packed rows (each row has ncols bits)
    let words_per_row = (ncols + 63) / 64;
    let mut matrix: Vec<Vec<u64>> = relations.iter()
        .map(|r| {
            let mut row = vec![0u64; words_per_row];
            for j in 0..ncols {
                if r.exp_vec[j] == 1 {
                    row[j / 64] |= 1u64 << (j % 64);
                }
            }
            row
        })
        .collect();

    // Track which original rows contribute to each pivot row
    let mut row_marks: Vec<Vec<usize>> = (0..nrows).map(|i| vec![i]).collect();

    let mut pivot_col: Vec<Option<usize>> = vec![None; ncols]; // pivot_col[j] = which row is pivot for col j
    let mut pivot_row = vec![usize::MAX; ncols]; // which row owns each col pivot
    let mut used_rows = vec![false; nrows];

    let mut free_rows: Vec<usize> = Vec::new();

    // Forward elimination
    let mut cur_row = 0;
    for col in 0..ncols {
        if cur_row >= nrows { break; }
        // Find pivot in this column at or below cur_row
        let pivot = (cur_row..nrows).find(|&r| {
            (matrix[r][col / 64] >> (col % 64)) & 1 == 1
        });
        if let Some(p) = pivot {
            matrix.swap(cur_row, p);
            row_marks.swap(cur_row, p);
            pivot_row[col] = cur_row;
            // Eliminate all other rows
            for r in 0..nrows {
                if r != cur_row && (matrix[r][col / 64] >> (col % 64)) & 1 == 1 {
                    for w in 0..words_per_row {
                        let val = matrix[cur_row][w];
                        matrix[r][w] ^= val;
                    }
                    let marks = row_marks[cur_row].clone();
                    for idx in marks {
                        let pos = row_marks[r].iter().position(|&x| x == idx);
                        if let Some(p) = pos {
                            row_marks[r].remove(p);
                        } else {
                            row_marks[r].push(idx);
                        }
                    }
                }
            }
            used_rows[cur_row] = true;
            cur_row += 1;
        } else {
            // Free column
        }
    }

    // Find zero rows (these correspond to dependencies)
    let n_big = n.clone();
    let n_bigint = BigInt::from_biguint(Sign::Plus, n_big);

    for row_idx in 0..nrows {
        let is_zero = matrix[row_idx].iter().all(|&w| w == 0);
        if !is_zero { continue; }

        let contributing = &row_marks[row_idx];
        if contributing.is_empty() { continue; }

        // Compute product of ax values
        let mut prod_a = BigInt::from(1i32);
        for &ri in contributing {
            prod_a = prod_a * &relations[ri].a;
        }

        // Compute square root of product of Q(x) values
        // Combined exp vector is all even
        let mut total_exp: Vec<u32> = vec![0; fb_size];
        for &ri in contributing {
            for j in 0..fb_size {
                total_exp[j] += relations[ri].exp_vec[j] as u32;
                // Recover actual exponents - but we only stored mod 2...
                // We need full exponents. Let's recompute.
            }
        }

        // Recompute: factor each Q(x) fully over factor base to get full exponents
        let mut full_exp: Vec<u32> = vec![0; fb_size];
        for &ri in contributing {
            let ax = &relations[ri].a;
            let ax_abs = ax.magnitude().clone();
            let qx_big = &ax_abs * &ax_abs;
            if qx_big < *n { continue; }
            let mut qx = qx_big - n;
            for i in 0..fb_size {
                let p_big = BigUint::from(factor_base[i]);
                let mut cnt = 0u32;
                while !qx.is_zero() && &qx % &p_big == BigUint::zero() {
                    qx /= &p_big;
                    cnt += 1;
                }
                full_exp[i] += cnt;
            }
        }

        // All full_exp should be even now
        let ok = full_exp.iter().all(|&e| e % 2 == 0);
        if !ok { continue; }

        // Compute y = product of p_i^(e_i/2)
        let mut y = BigInt::from(1i32);
        for i in 0..fb_size {
            let half = full_exp[i] / 2;
            if half > 0 {
                let p_big = BigInt::from(factor_base[i] as i64);
                let mut pw = BigInt::from(1i32);
                for _ in 0..half { pw = pw * &p_big; }
                y = y * pw;
            }
        }

        // x = prod_a mod n, y = y mod n
        let x_mod = ((prod_a % &n_bigint) + &n_bigint) % &n_bigint;
        let y_mod = ((y % &n_bigint) + &n_bigint) % &n_bigint;

        let x_u = x_mod.magnitude().clone();
        let y_u = y_mod.magnitude().clone();

        let diff1 = if x_u > y_u { x_u.clone() - y_u.clone() } else { y_u.clone() - x_u.clone() };
        let diff2 = x_u + y_u;

        let g1 = diff1.gcd(n);
        if g1 != BigUint::one() && &g1 != n {
            return Some(g1);
        }
        let g2 = diff2.gcd(n);
        if g2 != BigUint::one() && &g2 != n {
            return Some(g2);
        }
    }

    None
}

// ===== Main factor function =====

fn trial_divide(n: &BigUint) -> Option<BigUint> {
    let primes_small: Vec<u64> = vec![
        2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,
        73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,
        157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,
        239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,
        331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,
        421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,
        509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,
        613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,
        709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,
        821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,
        919,929,937,941,947,953,967,971,977,983,991,997,
    ];
    for p in primes_small {
        let p_big = BigUint::from(p);
        if n % &p_big == BigUint::zero() {
            if n != &p_big {
                return Some(p_big);
            }
        }
    }
    None
}

fn factor_number(n: &BigUint, time_limit: Duration, start: Instant) -> Option<(BigUint, BigUint)> {
    let one = BigUint::one();

    if n <= &one { return None; }
    if is_prime_big(n) { return None; }

    // Trial division
    if let Some(d) = trial_divide(n) {
        let q = n / &d;
        let (p, q) = if d < q { (d, q) } else { (q, d) };
        return Some((p, q));
    }

    // Try u128 fast path
    if let Some(n128) = n.to_u128() {
        if let Some((p, q)) = factor_u128(n128) {
            return Some((BigUint::from(p), BigUint::from(q)));
        }
    }

    // Parallel Pollard's rho with BigUint
    let n_arc = Arc::new(n.clone());
    let stop = Arc::new(AtomicBool::new(false));
    let result = Arc::new(Mutex::new(None::<BigUint>));

    // Determine how many threads to use
    let n_digits = n.to_str_radix(10).len();

    // If n is small enough, just run Pollard's rho inline
    if n_digits <= 50 {
        let num_threads = 8usize;
        let mut handles = Vec::new();

        for thread_id in 0..num_threads {
            let n_clone = Arc::clone(&n_arc);
            let stop_clone = Arc::clone(&stop);
            let result_clone = Arc::clone(&result);

            handles.push(std::thread::spawn(move || {
                for c_val in (thread_id..200).step_by(num_threads) {
                    if stop_clone.load(Ordering::Relaxed) { return; }
                    let c = BigUint::from(c_val as u64 + 1);
                    if let Some(d) = pollard_rho_big(&n_clone, &c, &stop_clone) {
                        let mut res = result_clone.lock().unwrap();
                        if res.is_none() {
                            *res = Some(d);
                        }
                        stop_clone.store(true, Ordering::Relaxed);
                        return;
                    }
                }
            }));
        }

        // Wait with timeout
        let poll_start = Instant::now();
        loop {
            if stop.load(Ordering::Relaxed) { break; }
            if poll_start.elapsed() > time_limit.checked_sub(start.elapsed()).unwrap_or(Duration::ZERO) {
                stop.store(true, Ordering::Relaxed);
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }

        for h in handles { let _ = h.join(); }

        if let Some(d) = result.lock().unwrap().clone() {
            let q = n / &d;
            let (p, q) = if d < q { (d, q) } else { (q, d) };
            return Some((p, q));
        }
    }

    // Quadratic Sieve for larger numbers
    if start.elapsed() < time_limit {
        let remaining = time_limit.checked_sub(start.elapsed()).unwrap_or(Duration::ZERO);
        // Also run Pollard's rho in parallel with QS
        let stop_pollard = Arc::new(AtomicBool::new(false));
        let n_arc2 = Arc::clone(&n_arc);
        let result2 = Arc::new(Mutex::new(None::<BigUint>));
        let result2_clone = Arc::clone(&result2);
        let stop2 = Arc::clone(&stop_pollard);

        let pollard_thread = std::thread::spawn(move || {
            for c_val in 1..=500u64 {
                if stop2.load(Ordering::Relaxed) { return; }
                let c = BigUint::from(c_val);
                if let Some(d) = pollard_rho_big(&n_arc2, &c, &stop2) {
                    let mut res = result2_clone.lock().unwrap();
                    if res.is_none() { *res = Some(d); }
                    stop2.store(true, Ordering::Relaxed);
                    return;
                }
            }
        });

        // Run QS in main thread
        if let Some(d) = quadratic_sieve(n, remaining * 9 / 10, start) {
            stop_pollard.store(true, Ordering::Relaxed);
            let _ = pollard_thread.join();
            let q = n / &d;
            let (p, q) = if d < q { (d, q) } else { (q, d) };
            return Some((p, q));
        }

        // Check if Pollard's rho found something
        stop_pollard.store(true, Ordering::Relaxed);
        let _ = pollard_thread.join();
        let r2 = result2.lock().unwrap().clone();
        if let Some(d) = r2 {
            let q = n / &d;
            let (p, q) = if d < q { (d, q) } else { (q, d) };
            return Some((p, q));
        }
    }

    None
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut time_limit_secs = 60.0f64;
    for i in 0..args.len() {
        if args[i] == "--time-limit" && i + 1 < args.len() {
            time_limit_secs = args[i+1].parse().unwrap_or(60.0);
        }
    }
    let time_limit = Duration::from_secs_f64(time_limit_secs);
    let global_start = Instant::now();

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    let mut pending: Vec<(String, BigUint)> = Vec::new();

    for line in stdin.lock().lines() {
        let line = match line { Ok(l) => l, Err(_) => break };
        let line = line.trim().to_string();
        if line.is_empty() { continue; }

        let id = parse_id(&line);
        let n = match parse_n(&line) {
            Some(n) => n,
            None => continue,
        };

        // Check remaining time
        let elapsed = global_start.elapsed();
        if elapsed >= time_limit {
            // Flush pending with timeout
            writeln!(out, "{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}", id).unwrap();
            out.flush().unwrap();
            continue;
        }

        let remaining = time_limit.checked_sub(elapsed).unwrap_or(Duration::from_secs(1));
        let per_query_limit = remaining.min(Duration::from_secs_f64(time_limit_secs * 0.95));

        let query_start = Instant::now();

        let result = factor_number(&n, per_query_limit, query_start);

        match result {
            Some((p, q)) => {
                writeln!(out, "{{\"id\": \"{}\", \"answer\": \"{} {}\"}}", id, p, q).unwrap();
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
