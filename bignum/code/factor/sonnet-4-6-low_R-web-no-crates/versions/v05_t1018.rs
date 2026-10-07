use std::io::{self, BufRead, Write, BufWriter};
use std::time::{Duration, Instant};
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use std::sync::mpsc;
use std::thread;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Zero, One, ToPrimitive, FromPrimitive};

// ============================================================
// Utilities
// ============================================================

fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

// Widening multiply: returns (lo, hi) where a * b = hi * 2^64 + lo
#[inline(always)]
fn widening_mul64(a: u64, b: u64) -> (u64, u64) {
    let full = (a as u128) * (b as u128);
    (full as u64, (full >> 64) as u64)
}

// mulmod for u64 values
#[inline(always)]
fn mulmod64(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

fn powmod64(mut base: u64, mut exp: u64, m: u64) -> u64 {
    let mut result = 1u64;
    base %= m;
    while exp > 0 {
        if exp & 1 == 1 {
            result = mulmod64(result, base, m);
        }
        base = mulmod64(base, base, m);
        exp >>= 1;
    }
    result
}

// ============================================================
// Montgomery multiplication for 128-bit numbers
// Uses CIOS algorithm with 64-bit words
// ============================================================

// Compute n' = -n^{-1} mod 2^64 using Newton's method
fn mont_n_prime(n: u64) -> u64 {
    // n must be odd
    debug_assert!(n & 1 == 1);
    let mut inv = n; // n * n ≡ 1 (mod 2^4) for odd n? Not quite, just start with n
    // Newton: x_{k+1} = x_k * (2 - n * x_k) mod 2^{2^k}
    // Start: x = 1 works since n * 1 ≡ n ≡ 1 (mod 2)... actually start with any odd value
    // Better: use the fact that n * (2 - n) ≡ 1 (mod 4) if n ≡ 1 (mod 2)
    let mut x: u64 = 1;
    // After each step, x approximates n^{-1} mod 2^{2^k}
    // Start: n * 1 ≡ 1 (mod 2). Do 6 Newton steps to get 2^64.
    for _ in 0..6 {
        x = x.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(x)));
    }
    // x = n^{-1} mod 2^64
    // We want n' = -n^{-1} mod 2^64
    0u64.wrapping_sub(x)
}

// Montgomery multiplication: computes a * b * R^{-1} mod n
// where R = 2^128, using CIOS with 64-bit words
// a, b in [0, n-1], n is odd
#[inline]
fn mont_mul_128(a: u128, b: u128, n: u128, n_prime: u64) -> u128 {
    let a0 = a as u64;
    let a1 = (a >> 64) as u64;
    let b0 = b as u64;
    let b1 = (b >> 64) as u64;
    let n0 = n as u64;
    let n1 = (n >> 64) as u64;

    let mut t0: u64 = 0;
    let mut t1: u64 = 0;
    let mut t2: u64 = 0;
    let mut t3: u64 = 0;

    // i = 0
    {
        let mut c: u64 = 0;

        // t += a[0] * b
        let (lo, hi) = widening_mul64(a0, b0);
        let (s, o1) = t0.overflowing_add(lo);
        t0 = s;
        c = hi.wrapping_add(o1 as u64);

        let (lo, hi) = widening_mul64(a0, b1);
        let (s, o1) = t1.overflowing_add(lo);
        let (s, o2) = s.overflowing_add(c);
        t1 = s;
        c = hi.wrapping_add(o1 as u64).wrapping_add(o2 as u64);
        t2 = t2.wrapping_add(c);

        // m = t[0] * n_prime mod 2^64
        let m = t0.wrapping_mul(n_prime);

        // t += m * n
        c = 0;
        let (lo, hi) = widening_mul64(m, n0);
        let (s, o1) = t0.overflowing_add(lo);
        let (s, o2) = s.overflowing_add(c);
        t0 = s;
        c = hi.wrapping_add(o1 as u64).wrapping_add(o2 as u64);

        let (lo, hi) = widening_mul64(m, n1);
        let (s, o1) = t1.overflowing_add(lo);
        let (s, o2) = s.overflowing_add(c);
        t1 = s;
        c = hi.wrapping_add(o1 as u64).wrapping_add(o2 as u64);

        t2 = t2.wrapping_add(c);
        // t0 should now be 0
    }

    // i = 1
    {
        let mut c: u64 = 0;

        // t += a[1] * b (starting at t1)
        let (lo, hi) = widening_mul64(a1, b0);
        let (s, o1) = t1.overflowing_add(lo);
        t1 = s;
        c = hi.wrapping_add(o1 as u64);

        let (lo, hi) = widening_mul64(a1, b1);
        let (s, o1) = t2.overflowing_add(lo);
        let (s, o2) = s.overflowing_add(c);
        t2 = s;
        c = hi.wrapping_add(o1 as u64).wrapping_add(o2 as u64);
        t3 = t3.wrapping_add(c);

        // m = t[1] * n_prime mod 2^64 (t[1] is our current low word)
        let m = t1.wrapping_mul(n_prime);

        // t += m * n
        c = 0;
        let (lo, hi) = widening_mul64(m, n0);
        let (s, o1) = t1.overflowing_add(lo);
        let (s, o2) = s.overflowing_add(c);
        t1 = s;
        c = hi.wrapping_add(o1 as u64).wrapping_add(o2 as u64);

        let (lo, hi) = widening_mul64(m, n1);
        let (s, o1) = t2.overflowing_add(lo);
        let (s, o2) = s.overflowing_add(c);
        t2 = s;
        c = hi.wrapping_add(o1 as u64).wrapping_add(o2 as u64);

        t3 = t3.wrapping_add(c);
        // t1 should now be 0
    }

    let result = (t2 as u128) | ((t3 as u128) << 64);
    if result >= n { result - n } else { result }
}

// Montgomery context for repeated multiplications with the same modulus
struct MontCtx128 {
    n: u128,
    n_prime: u64,
    r2: u128, // R^2 mod n = 2^256 mod n, for converting to Montgomery form
}

impl MontCtx128 {
    fn new(n: u128) -> Self {
        assert!(n & 1 == 1, "n must be odd");
        let n_prime = mont_n_prime(n as u64); // only use low 64 bits
        // Compute R^2 mod n = 2^256 mod n
        // Start with 1, double 256 times
        let mut r2 = 1u128;
        for _ in 0..256 {
            r2 = r2.wrapping_add(r2);
            if r2 >= n { r2 -= n; }
        }
        // Actually compute R mod n = 2^128 mod n first, then square
        // Or just double 256 times from 1
        MontCtx128 { n, n_prime, r2 }
    }

    // Convert a to Montgomery form: a * R mod n
    #[inline]
    fn to_mont(&self, a: u128) -> u128 {
        mont_mul_128(a % self.n, self.r2, self.n, self.n_prime)
    }

    // Convert from Montgomery form: a * R^{-1} mod n
    #[inline]
    fn from_mont(&self, a: u128) -> u128 {
        mont_mul_128(a, 1, self.n, self.n_prime)
    }

    // Multiply in Montgomery form
    #[inline]
    fn mul(&self, a: u128, b: u128) -> u128 {
        mont_mul_128(a, b, self.n, self.n_prime)
    }

    // Add mod n
    #[inline]
    fn add(&self, a: u128, b: u128) -> u128 {
        let s = a.wrapping_add(b);
        if s >= self.n { s - self.n } else { s }
    }
}

// ============================================================
// Miller-Rabin primality tests
// ============================================================

fn is_prime_u128(n: u128) -> bool {
    if n < 2 { return false; }
    if n == 2 || n == 3 { return true; }
    if n & 1 == 0 || n % 3 == 0 { return false; }

    // Write n-1 = 2^r * d
    let mut d = n - 1;
    let mut r = 0u32;
    while d & 1 == 0 { d >>= 1; r += 1; }

    // For n < 3.3 * 10^24, these witnesses are sufficient
    // For n < 2^128 we use more witnesses
    let witnesses: &[u128] = &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];

    // Use Montgomery for efficiency if n is large enough
    if n > (1u128 << 64) && n & 1 == 1 {
        let ctx = MontCtx128::new(n);
        let one_m = ctx.to_mont(1);
        let nm1_m = ctx.to_mont(n - 1);

        'outer: for &a in witnesses {
            if a >= n { continue; }
            // Compute a^d mod n
            let a_m = ctx.to_mont(a as u128);
            let d_m = ctx.to_mont(1); // we do regular powmod
            // Actually, we compute a^d in Montgomery space
            let mut x = {
                let mut base = a_m;
                let mut exp = d;
                let mut result = one_m;
                while exp > 0 {
                    if exp & 1 == 1 { result = ctx.mul(result, base); }
                    base = ctx.mul(base, base);
                    exp >>= 1;
                }
                result
            };
            if x == one_m || x == nm1_m { continue; }
            for _ in 0..r-1 {
                x = ctx.mul(x, x);
                if x == nm1_m { continue 'outer; }
            }
            return false;
        }
        return true;
    }

    // Small n: direct modular arithmetic
    let powmod = |mut base: u128, mut exp: u128, m: u128| -> u128 {
        let mut result = 1u128;
        base %= m;
        while exp > 0 {
            if exp & 1 == 1 {
                result = ((result as u128 * base as u128) % m as u128) as u128;
            }
            base = ((base as u128 * base as u128) % m as u128) as u128;
            exp >>= 1;
        }
        result
    };

    'outer: for &a in witnesses {
        if a >= n { continue; }
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..r-1 {
            x = (x * x) % n;
            if x == n - 1 { continue 'outer; }
        }
        return false;
    }
    true
}

fn is_prime_big(n: &BigUint) -> bool {
    if let Some(n64) = n.to_u128() {
        return is_prime_u128(n64);
    }
    let zero = BigUint::zero();
    let one = BigUint::one();
    let two = BigUint::from(2u64);
    if n % &two == zero { return false; }

    let n_minus_1 = n - &one;
    let mut d = n_minus_1.clone();
    let mut r = 0u32;
    while &d % &two == zero { d >>= 1; r += 1; }

    let witnesses = [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
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

// ============================================================
// Pollard's rho (Brent) - u128 path with Montgomery
// ============================================================

fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 { let t = b; b = a % b; a = t; }
    a
}

fn pollard_brent_u128_mont(n: u128, c_val: u128, start: u128, ctx: &MontCtx128) -> Option<u128> {
    // Work in Montgomery space
    let c = ctx.to_mont(c_val % n);
    let mut y = ctx.to_mont(start);
    let one_m = ctx.to_mont(1);
    let mut r: u64 = 1;
    let mut q = one_m;
    let mut x = y;
    let mut ys;
    let mut d = 1u128;
    let batch = 128u64;

    // f(y) = y^2 + c (in Montgomery space)
    macro_rules! step {
        ($y:expr) => {{
            let sq = ctx.mul($y, $y);
            ctx.add(sq, c)
        }};
    }

    'outer: loop {
        x = y;
        for _ in 0..r {
            y = step!(y);
        }
        let mut k: u64 = 0;
        while k < r {
            ys = y;
            let steps = batch.min(r - k);
            for _ in 0..steps {
                y = step!(y);
                // diff = |y - x| in value space (but we're in Montgomery space)
                // diff in Montgomery space = diff_val * R mod n
                // |y_m - x_m| = |y_val - x_val| * R mod n = diff_val_mont
                let diff_m = if y >= x { y - x } else { x - y };
                if diff_m == 0 { return None; }
                q = ctx.mul(q, diff_m);
                if q == 0 { q = one_m; }
            }
            // Convert q from Montgomery space: q_val = q_m * R^{-1} mod n
            let q_val = ctx.from_mont(q);
            d = gcd128(q_val, n);
            k += steps;
            if d != 1 { break 'outer; }
        }
        r *= 2;
        if r > (1u64 << 28) { return None; }
    }

    if d == n {
        // Backtrack
        d = 1;
        loop {
            ys = step!(ys);
            let diff_m = if ys >= x { ys - x } else { x - ys };
            if diff_m == 0 { return None; }
            let diff_val = ctx.from_mont(diff_m);
            d = gcd128(diff_val, n);
            if d != 1 { break; }
        }
        if d == n { return None; }
    }

    if d != 0 && d != 1 && d != n { Some(d) } else { None }
}

fn factor_u128_parallel(n: u128) -> Option<(u128, u128)> {
    if n <= 1 { return None; }
    if n & 1 == 0 { return Some((2, n/2)); }

    // Trial division
    let small = [3u128,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
                 101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199];
    for &p in &small {
        if p * p > n { return Some((p, n/p)); } // n is prime, shouldn't happen
        if n % p == 0 { return Some((p, n/p)); }
    }

    // Check if n is prime (shouldn't factor semiprimes into 3 factors)
    if is_prime_u128(n) { return None; }

    // Set up Montgomery context if n is odd (it is)
    let ctx = Arc::new(MontCtx128::new(n));
    let stopped = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<u128>();
    let num_threads = 8usize;

    for t in 0..num_threads {
        let tx = tx.clone();
        let stopped = stopped.clone();
        let ctx = ctx.clone();
        let mut seed: u64 = 0xdeadbeef1234abcd ^ (n as u64) ^ (t as u64 * 0x9e3779b97f4a7c15);
        xorshift64(&mut seed);
        thread::spawn(move || {
            let mut rng = seed;
            let n = ctx.n;
            loop {
                if stopped.load(Ordering::Relaxed) { return; }
                let c = (xorshift64(&mut rng) as u128) % (n - 2) + 1;
                let start = (xorshift64(&mut rng) as u128) % (n - 2) + 2;
                if let Some(f) = pollard_brent_u128_mont(n, c, start, &ctx) {
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
            Some((f.min(n/f), f.max(n/f)))
        }
        Err(_) => None,
    }
}

// ============================================================
// Quadratic Sieve for larger numbers
// ============================================================

fn isqrt_big(n: &BigUint) -> BigUint {
    if n.is_zero() { return BigUint::zero(); }
    // Newton's method
    let mut x = BigUint::from(1u64) << ((n.bits() / 2) as u32 + 1);
    loop {
        let x1 = (&x + n / &x) >> 1u32;
        if x1 >= x { break; }
        x = x1;
    }
    x
}

fn sieve_primes(limit: usize) -> Vec<u32> {
    let mut is_prime = vec![true; limit + 1];
    is_prime[0] = false;
    if limit == 0 { return vec![]; }
    is_prime[1] = false;
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

// Tonelli-Shanks: sqrt of n mod p
fn sqrt_mod_p(n: u64, p: u64) -> Option<u64> {
    if p == 2 { return Some(n & 1); }
    let n = n % p;
    if n == 0 { return Some(0); }
    // Check if n is a QR mod p
    if powmod64(n, (p - 1) / 2, p) != 1 { return None; }
    if p % 4 == 3 {
        return Some(powmod64(n, (p + 1) / 4, p));
    }
    // Tonelli-Shanks
    let mut q = p - 1;
    let mut s = 0u32;
    while q & 1 == 0 { q >>= 1; s += 1; }
    // Find a quadratic non-residue
    let mut z = 2u64;
    while powmod64(z, (p - 1) / 2, p) != p - 1 { z += 1; }
    let mut m = s;
    let mut c = powmod64(z, q, p);
    let mut t = powmod64(n, q, p);
    let mut r = powmod64(n, (q + 1) / 2, p);
    loop {
        if t == 0 { return Some(0); }
        if t == 1 { return Some(r); }
        let mut i = 1u32;
        let mut tmp = mulmod64(t, t, p);
        while tmp != 1 { tmp = mulmod64(tmp, tmp, p); i += 1; }
        let b = powmod64(c, 1u64 << (m - i - 1), p);
        m = i;
        c = mulmod64(b, b, p);
        t = mulmod64(t, c, p);
        r = mulmod64(r, b, p);
    }
}

// Legendre symbol
fn legendre(n: u64, p: u64) -> i32 {
    let r = powmod64(n % p, (p - 1) / 2, p);
    if r == 0 { 0 } else if r == 1 { 1 } else { -1 }
}

fn quadratic_sieve(n: &BigUint, deadline: Instant) -> Option<BigUint> {
    let bits = n.bits() as usize;
    if bits < 30 { return None; } // too small for QS

    // Choose smoothness bound B based on number size
    // L[1/2, 1/sqrt(2)] approximation
    let ln_n = bits as f64 * std::f64::consts::LN_2;
    let ln_ln_n = ln_n.ln();
    let b_float = (0.5 * (ln_n * ln_ln_n).sqrt()).exp();
    let b = (b_float as usize).max(100).min(1_500_000);

    // Sieve interval size M
    let m = (b * 8).max(20_000).min(10_000_000);

    let all_primes = sieve_primes(b);

    // Compute sqrt(n) as BigUint
    let sqrt_n = isqrt_big(n);

    // Build factor base: primes p where n is a QR mod p
    let n_u64 = n.to_u64_digits(); // little-endian u64 digits
    let n_mod_p = |p: u64| -> u64 {
        // Compute n mod p using Horner's method
        let mut r = 0u64;
        for &d in n_u64.iter().rev() {
            let (lo, hi) = widening_mul64(r, u64::MAX.wrapping_add(1)); // r * 2^64
            // Actually compute r = (r * 2^64 + d) mod p
            // r * 2^64 mod p: we need this...
            // Simpler: just do it with u128
            r = ((r as u128 * (1u128 << 64) + d as u128) % p as u128) as u64;
        }
        r
    };

    let mut factor_base: Vec<u32> = Vec::new();
    let mut start_roots: Vec<(u32, u32, u32)> = Vec::new(); // (p, r1, r2)

    factor_base.push(2);
    if n_mod_p(2) % 2 == 0 {
        // n is even, shouldn't happen for semiprime > 2
    }
    start_roots.push((2, 1, 1));

    for &p in &all_primes[1..] {
        if Instant::now() > deadline { return None; }
        let p64 = p as u64;
        let n_mod = n_mod_p(p64);
        if n_mod == 0 {
            // p divides n!
            let p_big = BigUint::from(p as u64);
            return Some(p_big);
        }
        if legendre(n_mod, p64) < 1 { continue; }
        if let Some(r) = sqrt_mod_p(n_mod, p64) {
            factor_base.push(p);
            let r2 = if r == 0 { 0 } else { (p64 - r) as u32 };
            start_roots.push((p, r as u32, r2));
        }
    }

    let fb_size = factor_base.len();
    if fb_size < 10 { return None; }

    // Compute where to start sieving: x such that (sqrt_n + x)^2 - n = Q(x)
    // Q(0) = sqrt_n^2 - n (close to 0)
    // Q(x) = x^2 + 2*sqrt_n*x + (sqrt_n^2 - n)

    // Compute starting offset for each prime p in factor base
    // Q(x) ≡ 0 (mod p) iff x ≡ r - sqrt_n (mod p) or x ≡ -r - sqrt_n (mod p)
    // We offset by M so all indices are non-negative

    let sieve_size = 2 * m + 1;
    let mut sieve = vec![0f32; sieve_size];

    let sqrt_n_mod_p = |p: u64| -> u64 {
        let mut r = 0u64;
        for &d in sqrt_n.to_u64_digits().iter().rev() {
            r = ((r as u128 * (1u128 << 64) + d as u128) % p as u128) as u64;
        }
        r
    };

    for (idx, &(p, r1, r2)) in start_roots.iter().enumerate() {
        let p64 = p as u64;
        let log_p = (p as f32).ln();
        let sqn_mod = sqrt_n_mod_p(p64);

        // Q(x) ≡ 0 (mod p) when x ≡ r1 - sqn_mod (mod p) or x ≡ r2 - sqn_mod (mod p)
        // In sieve array, x = i - M, so Q(i - M) ≡ 0 (mod p) when i - M ≡ r1 - sqn_mod (mod p)
        // i ≡ r1 - sqn_mod + M (mod p)

        let roots = if r1 == r2 { vec![r1 as u64] } else { vec![r1 as u64, r2 as u64] };
        for root in roots {
            let offset = (root as i64 - sqn_mod as i64 + m as i64).rem_euclid(p64 as i64) as usize;
            let mut i = offset;
            while i < sieve_size {
                sieve[i] += log_p;
                i += p as usize;
            }
        }
    }

    // Collect smooth candidates
    // Threshold: approximation of log(Q(x))
    // Q(x) ≈ 2 * sqrt_n * |x| for large |x|
    // At x = M: Q(M) ≈ 2 * sqrt_n * M
    let log_qm = {
        let bits_q = n.bits() / 2 + (m as f64).log2() as u64 + 1;
        bits_q as f32 * std::f64::consts::LN_2 as f32
    };
    let threshold = log_qm * 0.75; // Loose threshold, verify actual smoothness

    let mut smooth_relations: Vec<(i64, Vec<u32>)> = Vec::new(); // (x, exponent vector index)
    let need = fb_size + 20; // Need slightly more than fb_size relations

    // Verify smoothness by trial division
    let two_sqrt_n = &sqrt_n * BigUint::from(2u64);
    for i in 0..sieve_size {
        if Instant::now() > deadline { break; }
        if sieve[i] < threshold { continue; }

        let x = i as i64 - m as i64;
        // Compute Q(x) = (sqrt_n + x)^2 - n
        let sx: BigUint = if x >= 0 {
            &sqrt_n + BigUint::from(x as u64)
        } else {
            let neg_x = (-x) as u64;
            if &sqrt_n >= &BigUint::from(neg_x) {
                &sqrt_n - BigUint::from(neg_x)
            } else {
                continue;
            }
        };
        let qx = &sx * &sx;
        if &qx <= n { continue; } // sqrt_n^2 < n, adjusting
        let qx = &sx * &sx;
        // Q(x) = sx^2 - n
        let qx = if &qx >= n { &qx - n } else { continue };
        if qx.is_zero() { continue; }

        // Trial divide qx by factor base
        let mut remainder = qx.clone();
        let mut exponents = vec![0u32; fb_size];

        for (j, &p) in factor_base.iter().enumerate() {
            let bp = BigUint::from(p as u64);
            while &remainder % &bp == BigUint::zero() {
                remainder /= &bp;
                exponents[j] += 1;
            }
        }

        if remainder == BigUint::one() {
            // Fully smooth!
            smooth_relations.push((x, exponents));
            if smooth_relations.len() >= need { break; }
        }
    }

    if smooth_relations.len() < fb_size + 1 {
        return None; // Not enough relations
    }

    // Linear algebra over GF(2) - find a dependency
    // Use bit vectors for efficiency
    let num_rel = smooth_relations.len();

    // Build matrix (fb_size rows x num_rel cols)
    // Each column = parity of exponents for that relation
    let words_per_col = (num_rel + 63) / 64;
    let mut matrix: Vec<u64> = vec![0u64; fb_size * words_per_col];

    for (col, (_, exps)) in smooth_relations.iter().enumerate() {
        for (row, &exp) in exps.iter().enumerate() {
            if exp & 1 == 1 {
                matrix[row * words_per_col + col / 64] |= 1u64 << (col % 64);
            }
        }
    }

    // Gaussian elimination to find kernel vector
    let mut pivot_row = vec![usize::MAX; num_rel];
    let mut pivot_col = vec![usize::MAX; fb_size];
    let mut current_row = 0usize;

    let mut identity: Vec<u64> = vec![0u64; num_rel * words_per_col];
    for i in 0..num_rel {
        identity[i * words_per_col + i / 64] |= 1u64 << (i % 64);
    }

    for col in 0..num_rel {
        if current_row >= fb_size { break; }
        // Find a row with a 1 in this column
        let word_idx = col / 64;
        let bit_idx = col % 64;
        let mut found = usize::MAX;
        for row in current_row..fb_size {
            if (matrix[row * words_per_col + word_idx] >> bit_idx) & 1 == 1 {
                found = row;
                break;
            }
        }
        if found == usize::MAX { continue; }

        // Swap rows
        if found != current_row {
            for w in 0..words_per_col {
                let tmp = matrix[current_row * words_per_col + w];
                matrix[current_row * words_per_col + w] = matrix[found * words_per_col + w];
                matrix[found * words_per_col + w] = tmp;
                let tmp = identity[current_row * words_per_col + w];
                identity[current_row * words_per_col + w] = identity[found * words_per_col + w];
                identity[found * words_per_col + w] = tmp;
            }
        }

        // Eliminate
        for row in 0..fb_size {
            if row == current_row { continue; }
            if (matrix[row * words_per_col + word_idx] >> bit_idx) & 1 == 1 {
                for w in 0..words_per_col {
                    matrix[row * words_per_col + w] ^= matrix[current_row * words_per_col + w];
                    identity[row * words_per_col + w] ^= identity[current_row * words_per_col + w];
                }
            }
        }

        pivot_row[col] = current_row;
        pivot_col[current_row] = col;
        current_row += 1;
    }

    // Find free columns (not pivots) - these give kernel vectors
    for col in 0..num_rel {
        if Instant::now() > deadline { return None; }
        if pivot_row[col] != usize::MAX { continue; }

        // This column gives a dependency: collect the combination
        let mut subset_x = BigUint::one();
        let mut subset_q = BigUint::one();
        let mut combined_exps = vec![0i64; fb_size];

        // The dependency involves column col plus pivot columns as determined by the identity matrix
        // Actually: the null vector is identity[col] with a 1 at position col
        // Let's just include col
        let mut included = vec![false; num_rel];
        for r in 0..num_rel {
            let word = r / 64;
            let bit = r % 64;
            // Check if relation r is included in the combination for column col
            // The null space vector for col: check identity row corresponding to col...
            // Hmm, we need to track which original columns are in the kernel vector.
            // Let's use the identity matrix: identity[col] gives the combination
        }

        // Let me use a simpler approach: just use the identity row for this free column
        let word_idx = col / 64;
        let bit_idx = col % 64;

        for r in 0..num_rel {
            // Check if original relation r is in the combination
            let w = r / 64;
            let b = r % 64;
            if (identity[col * words_per_col + w] >> b) & 1 == 1 {
                included[r] = true;
            }
        }
        // Also include col itself
        included[col] = true;

        // Verify: combination has all even exponents?
        let mut exp_sum = vec![0i64; fb_size];
        for r in 0..num_rel {
            if included[r] {
                for j in 0..fb_size {
                    exp_sum[j] += smooth_relations[r].1[j] as i64;
                }
            }
        }
        if exp_sum.iter().any(|&e| e & 1 != 0) { continue; }

        // Compute X = product of (sqrt_n + x_r) mod n
        // Compute Y = product of sqrt(Q(x_r)) factors
        let mut x_prod = BigUint::one();
        let mut y_sqr_factors = vec![0i64; fb_size]; // half of exp_sum

        for r in 0..num_rel {
            if included[r] {
                let x = smooth_relations[r].0;
                let sx: BigUint = if x >= 0 {
                    &sqrt_n + BigUint::from(x as u64)
                } else {
                    let neg_x = (-x) as u64;
                    &sqrt_n - BigUint::from(neg_x)
                };
                x_prod = (&x_prod * &sx) % n;
                for j in 0..fb_size {
                    y_sqr_factors[j] += smooth_relations[r].1[j] as i64;
                }
            }
        }

        // Y = product of p^(exp/2)
        let mut y = BigUint::one();
        for j in 0..fb_size {
            let half = y_sqr_factors[j] / 2;
            if half > 0 {
                let p = BigUint::from(factor_base[j] as u64);
                y = y * p.pow(half as u32) % n;
            }
        }

        // gcd(X - Y, n) or gcd(X + Y, n)
        let diff = if x_prod >= y {
            &x_prod - &y
        } else {
            n - &y + &x_prod
        };

        if !diff.is_zero() && &diff != n {
            let g = diff.gcd(n);
            if g != BigUint::one() && &g != n {
                return Some(g);
            }
        }

        let sum = (&x_prod + &y) % n;
        if !sum.is_zero() && &sum != n {
            let g = sum.gcd(n);
            if g != BigUint::one() && &g != n {
                return Some(g);
            }
        }
    }

    None
}

// ============================================================
// BigUint Pollard's rho
// ============================================================

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
    let batch: u64 = 128;

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
            let steps = batch.min(r - k);
            for _ in 0..steps {
                y = f(&y);
                let diff = if y > x { &y - &x } else { &x - &y };
                q = (&q * diff) % n;
                if q.is_zero() { q = one.clone(); }
            }
            d = q.gcd(n);
            k += steps;
        }
        if d != one { break; }
        r *= 2;
        if r > (1u64 << 26) { return None; }
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

fn factor_big(n: &BigUint, deadline: Instant) -> Option<(BigUint, BigUint)> {
    let two = BigUint::from(2u64);

    if n % &two == BigUint::zero() {
        return Some((two.clone(), n / &two));
    }

    // Trial division
    for i in (3u64..1_000_000).step_by(2) {
        if Instant::now() > deadline { return None; }
        let bi = BigUint::from(i);
        if n % &bi == BigUint::zero() {
            return Some((bi.clone(), n / &bi));
        }
    }

    // Try quadratic sieve first for larger numbers
    let qs_deadline = deadline - Duration::from_millis(2000);
    if Instant::now() < qs_deadline {
        if let Some(f) = quadratic_sieve(n, qs_deadline) {
            let q = n / &f;
            let (p, q) = if f <= q { (f, q) } else { (q.clone(), n / &q) };
            return Some((p, q));
        }
    }

    // Fall back to Pollard's rho with BigUint
    let stopped = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<BigUint>();

    for t in 0..8usize {
        let tx = tx.clone();
        let stopped = stopped.clone();
        let n_clone = n.clone();
        let seed: u64 = 0xdeadbeef1234abcd ^ (t as u64 * 0x9e3779b97f4a7c15);
        thread::spawn(move || {
            let mut rng = seed;
            xorshift64(&mut rng);
            loop {
                if stopped.load(Ordering::Relaxed) { return; }
                let c = (xorshift64(&mut rng) % (n_clone.bits() as u64 * 4).max(4)) + 1;
                if let Some(f) = pollard_brent_big(&n_clone, c, &mut rng) {
                    if f != BigUint::one() && &f != &n_clone {
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
    let deadline = start + Duration::from_millis(time_limit_secs * 1000 - 300);

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());

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
            if n_small <= 1 {
                None
            } else {
                factor_u128_parallel(n_small).map(|(p, q)| (BigUint::from(p), BigUint::from(q)))
            }
        } else {
            factor_big(n, deadline)
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
