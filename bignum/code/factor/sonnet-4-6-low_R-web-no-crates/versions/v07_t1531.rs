use std::io::{self, BufRead, Write, BufWriter};
use std::time::{Duration, Instant};
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use std::sync::mpsc;
use std::thread;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Zero, One, ToPrimitive};

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

#[inline(always)]
fn widening_mul64(a: u64, b: u64) -> (u64, u64) {
    let full = (a as u128) * (b as u128);
    (full as u64, (full >> 64) as u64)
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

// ============================================================
// Montgomery multiplication for 128-bit numbers (CIOS, 2 words)
// ============================================================

fn mont_n_prime(n: u64) -> u64 {
    // n' = -n^{-1} mod 2^64, n must be odd
    let mut x: u64 = 1;
    for _ in 0..6 { x = x.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(x))); }
    0u64.wrapping_sub(x)
}

#[inline]
fn mont_mul_128(a: u128, b: u128, n: u128, n_prime: u64) -> u128 {
    let a0 = a as u64; let a1 = (a >> 64) as u64;
    let b0 = b as u64; let b1 = (b >> 64) as u64;
    let n0 = n as u64; let n1 = (n >> 64) as u64;

    let mut t0: u64 = 0; let mut t1: u64 = 0;
    let mut t2: u64 = 0; let mut t3: u64 = 0;

    macro_rules! madd {
        ($t:expr, $a:expr, $b:expr, $c:expr) => {{
            let (lo, hi) = widening_mul64($a, $b);
            let (s1, o1) = $t.overflowing_add(lo);
            let (s2, o2) = s1.overflowing_add($c);
            $t = s2;
            hi.wrapping_add(o1 as u64).wrapping_add(o2 as u64)
        }};
    }

    // i = 0
    {
        let mut c = madd!(t0, a0, b0, 0);
        c = madd!(t1, a0, b1, c);
        t2 = t2.wrapping_add(c);
        let m = t0.wrapping_mul(n_prime);
        let mut c2 = madd!(t0, m, n0, 0);
        c2 = madd!(t1, m, n1, c2);
        t2 = t2.wrapping_add(c2);
    }
    // i = 1
    {
        let mut c = madd!(t1, a1, b0, 0);
        c = madd!(t2, a1, b1, c);
        t3 = t3.wrapping_add(c);
        let m = t1.wrapping_mul(n_prime);
        let mut c2 = madd!(t1, m, n0, 0);
        c2 = madd!(t2, m, n1, c2);
        t3 = t3.wrapping_add(c2);
    }

    let result = (t2 as u128) | ((t3 as u128) << 64);
    if result >= n { result - n } else { result }
}

struct MontCtx128 {
    n: u128,
    n_prime: u64,
    r2: u128,
}

impl MontCtx128 {
    fn new(n: u128) -> Self {
        let n_prime = mont_n_prime(n as u64);
        // Compute R^2 mod n = 2^256 mod n by repeated doubling
        let mut r2 = 1u128;
        for _ in 0..256 {
            r2 = r2.wrapping_add(r2);
            if r2 >= n { r2 -= n; }
        }
        MontCtx128 { n, n_prime, r2 }
    }

    #[inline] fn to_mont(&self, a: u128) -> u128 {
        mont_mul_128(a % self.n, self.r2, self.n, self.n_prime)
    }
    #[inline] fn from_mont(&self, a: u128) -> u128 {
        mont_mul_128(a, 1, self.n, self.n_prime)
    }
    #[inline] fn mul(&self, a: u128, b: u128) -> u128 {
        mont_mul_128(a, b, self.n, self.n_prime)
    }
    #[inline] fn add(&self, a: u128, b: u128) -> u128 {
        let s = a.wrapping_add(b);
        if s >= self.n { s - self.n } else { s }
    }
}

// ============================================================
// Primality tests
// ============================================================

fn is_prime_u128(n: u128) -> bool {
    if n < 2 { return false; }
    if n == 2 || n == 3 { return true; }
    if n & 1 == 0 || n % 3 == 0 { return false; }
    if n < 9 { return true; }

    let mut d = n - 1; let mut r = 0u32;
    while d & 1 == 0 { d >>= 1; r += 1; }

    let witnesses: &[u128] = &[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47];

    if n > (1u128 << 64) {
        let ctx = MontCtx128::new(n);
        let one_m = ctx.to_mont(1);
        let nm1_m = ctx.to_mont(n - 1);
        'outer: for &a in witnesses {
            if a >= n { continue; }
            let a_m = ctx.to_mont(a);
            let mut x = { let mut base=a_m; let mut e=d; let mut res=one_m;
                while e>0 { if e&1==1 { res=ctx.mul(res,base); } base=ctx.mul(base,base); e>>=1; } res };
            if x == one_m || x == nm1_m { continue; }
            for _ in 0..r-1 { x = ctx.mul(x, x); if x == nm1_m { continue 'outer; } }
            return false;
        }
        return true;
    }

    let pm = |mut b: u128, mut e: u128, m: u128| -> u128 {
        let mut r = 1u128; b %= m;
        while e > 0 { if e&1==1 { r = (r*b)%m; } b = (b*b)%m; e>>=1; } r
    };
    'outer: for &a in witnesses {
        if a >= n { continue; }
        let mut x = pm(a, d, n);
        if x == 1 || x == n-1 { continue; }
        for _ in 0..r-1 { x = (x*x)%n; if x == n-1 { continue 'outer; } }
        return false;
    }
    true
}

fn is_prime_big(n: &BigUint) -> bool {
    if let Some(v) = n.to_u128() { return is_prime_u128(v); }
    let one = BigUint::one();
    let two = BigUint::from(2u64);
    if n % &two == BigUint::zero() { return false; }
    let nm1 = n - &one;
    let mut d = nm1.clone(); let mut r = 0u32;
    while &d % &two == BigUint::zero() { d >>= 1; r += 1; }
    let witnesses = [2u64,3,5,7,11,13,17,19,23,29,31,37];
    'outer: for a in witnesses {
        let ab = BigUint::from(a);
        if &ab >= n { continue; }
        let mut x = ab.modpow(&d, n);
        if x == one || x == nm1 { continue; }
        for _ in 0..r-1 { x = x.modpow(&two, n); if x == nm1 { continue 'outer; } }
        return false;
    }
    true
}

// ============================================================
// Pollard rho - u128 Montgomery path
// ============================================================

fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 { let t = b; b = a % b; a = t; }
    a
}

fn pollard_brent_u128(n: u128, c_val: u128, start: u128, ctx: &MontCtx128) -> Option<u128> {
    let c = ctx.to_mont(c_val);
    let mut y = ctx.to_mont(start);
    let one_m = ctx.to_mont(1);
    let mut r: u64 = 1;
    let mut q = one_m;
    let mut x = y;
    let mut ys = y;
    let mut d;
    let batch = 128u64;

    macro_rules! step { ($v:expr) => { ctx.add(ctx.mul($v, $v), c) }; }

    loop {
        x = y;
        for _ in 0..r { y = step!(y); }
        let mut k: u64 = 0;
        d = 1u128;
        while k < r && d == 1 {
            ys = y;
            let steps = batch.min(r - k);
            for _ in 0..steps {
                y = step!(y);
                let diff = if y >= x { y - x } else { x - y };
                if diff == 0 { break; }
                // gcd(diff, n) = gcd(ctx.from_mont(diff), n) but simpler: use diff directly
                // Since diff = |y_m - x_m| = |y_val - x_val| * R mod n,
                // gcd(diff, n) = gcd(y_val - x_val, n). OK to use diff.
                q = ctx.mul(q, diff);
                if q == 0 { q = one_m; }
            }
            d = gcd128(ctx.from_mont(q), n);
            k += steps;
        }
        if d != 1 { break; }
        r *= 2;
        if r > (1u64 << 28) { return None; }
    }

    if d == n {
        d = 1;
        loop {
            ys = step!(ys);
            let diff = if ys >= x { ys - x } else { x - ys };
            if diff == 0 { return None; }
            d = gcd128(ctx.from_mont(diff), n);
            if d != 1 { break; }
        }
        if d == n { return None; }
    }

    if d != 0 && d != 1 && d != n { Some(d) } else { None }
}

fn factor_u128_parallel(n: u128) -> Option<(u128, u128)> {
    if n & 1 == 0 { return Some((2, n/2)); }
    for p in [3u128,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97] {
        if n == p { return None; }
        if n % p == 0 { return Some((p, n/p)); }
    }
    let mut i = 101u128;
    while i < 1_000_000 && i * i <= n {
        if n % i == 0 { return Some((i, n/i)); }
        if n % (i+2) == 0 { return Some((i+2, n/(i+2))); }
        i += 6;
    }
    if i * i > n { return None; } // n is prime, shouldn't happen

    if is_prime_u128(n) { return None; }

    let ctx = Arc::new(MontCtx128::new(n));
    let stopped = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<u128>();

    for t in 0..8usize {
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
                if let Some(f) = pollard_brent_u128(n, c, start, &ctx) {
                    let _ = tx.send(f);
                    stopped.store(true, Ordering::Relaxed);
                    return;
                }
            }
        });
    }
    drop(tx);

    rx.recv().ok().map(|f| (f.min(n/f), f.max(n/f)))
}

// ============================================================
// Quadratic Sieve
// ============================================================

fn isqrt_big(n: &BigUint) -> BigUint {
    if n.is_zero() { return BigUint::zero(); }
    let mut x = BigUint::one() << ((n.bits() / 2 + 1) as u32);
    loop {
        let x1 = (&x + n / &x) >> 1u32;
        if x1 >= x { break; }
        x = x1;
    }
    x
}

fn sieve_primes_u32(limit: usize) -> Vec<u32> {
    if limit < 2 { return vec![]; }
    let mut sieve = vec![true; limit + 1];
    sieve[0] = false; sieve[1] = false;
    let mut i = 2;
    while i * i <= limit {
        if sieve[i] { let mut j = i*i; while j <= limit { sieve[j] = false; j += i; } }
        i += 1;
    }
    (2..=limit).filter(|&i| sieve[i]).map(|i| i as u32).collect()
}

fn tonelli_shanks(n: u64, p: u64) -> u64 {
    // Returns r such that r^2 ≡ n (mod p), assumes n is a QR
    if p == 2 { return n & 1; }
    if p % 4 == 3 { return powmod64(n, (p + 1) / 4, p); }
    let mut q = p - 1; let mut s = 0u32;
    while q & 1 == 0 { q >>= 1; s += 1; }
    let mut z = 2u64;
    while powmod64(z, (p-1)/2, p) != p-1 { z += 1; }
    let mut m2 = s;
    let mut c = powmod64(z, q, p);
    let mut t = powmod64(n, q, p);
    let mut r = powmod64(n, (q + 1) / 2, p);
    loop {
        if t == 0 { return 0; }
        if t == 1 { return r; }
        let mut i = 1u32; let mut tmp = mulmod64(t, t, p);
        while tmp != 1 { tmp = mulmod64(tmp, tmp, p); i += 1; }
        let b = powmod64(c, 1u64 << (m2 - i - 1), p);
        m2 = i;
        c = mulmod64(b, b, p);
        t = mulmod64(t, c, p);
        r = mulmod64(r, b, p);
    }
}

// Compute bignum mod small prime p quickly
fn big_mod_p(n_digits: &[u64], p: u64) -> u64 {
    // n_digits is little-endian u64 representation
    let mut r = 0u64;
    for &d in n_digits.iter().rev() {
        r = ((r as u128 * ((u64::MAX as u128 + 1) % p as u128) + d as u128) % p as u128) as u64;
    }
    r
}

// n_digits2 * 2^64 mod p = (n_digits.last() * (2^64 mod p) + ...) mod p
// Actually the function above should work. Let me trace:
// r starts at 0
// For each digit d from most to least significant:
//   r = r * 2^64 + d (mod p)
// This correctly evaluates n in base 2^64.
// But r * 2^64 can overflow... we need to use: r = (r * (2^64 mod p) + d) mod p
// 2^64 mod p = (u64::MAX + 1) mod p = (u64::MAX mod p + 1) mod p

fn big_mod_p_correct(digits: &[u64], p: u64) -> u64 {
    // digits: little-endian u64 words
    let p128 = p as u128;
    let r64_mod_p = (1u128 << 64) % p128; // 2^64 mod p
    let mut r = 0u128;
    for &d in digits.iter().rev() {
        r = (r * r64_mod_p + d as u128) % p128;
    }
    r as u64
}

struct QSRelation {
    x: i64,
    // exponent vector as bit array (one bit per factor base prime)
    exps_parity: Vec<u64>, // bit vector, length = ceil(fb_size / 64)
    // full exponents for computing Y
    exps_full: Vec<u32>,
}

fn quadratic_sieve(n: &BigUint, deadline: Instant) -> Option<BigUint> {
    let bits = n.bits() as usize;
    let ln_n = bits as f64 * std::f64::consts::LN_2;
    let ln_ln_n = if ln_n > 1.0 { ln_n.ln() } else { 1.0 };

    // Smoothness bound B
    let b_float = (0.5 * (ln_n * ln_ln_n).sqrt()).exp();
    let b = (b_float as usize).clamp(200, 500_000);

    // Sieve interval size M
    let m_size = (b * 10).clamp(50_000, 5_000_000) as usize;

    let all_primes = sieve_primes_u32(b);
    let n_digits = n.to_u64_digits(); // little-endian

    // Build factor base: primes where n is a QR (Legendre symbol = 1)
    // Always include 2
    let mut fb: Vec<u32> = vec![2];
    let mut fb_roots: Vec<(u32, u32, u32)> = vec![(2, 1, 1)]; // (p, root1, root2)

    let two = BigUint::from(2u64);
    // Check if n is even (shouldn't be for semiprime)
    if n % &two == BigUint::zero() {
        return Some(two);
    }

    for &p in &all_primes[1..] { // skip 2
        if Instant::now() > deadline { return None; }
        let p64 = p as u64;
        let n_mod_p = big_mod_p_correct(&n_digits, p64);
        if n_mod_p == 0 {
            return Some(BigUint::from(p as u64)); // factor found!
        }
        // Legendre symbol
        let leg = powmod64(n_mod_p, (p64 - 1) / 2, p64);
        if leg != 1 { continue; } // not a QR
        let r = tonelli_shanks(n_mod_p, p64);
        let r2 = if r == 0 { 0u32 } else { (p64 - r) as u32 };
        fb.push(p);
        fb_roots.push((p, r as u32, r2));
    }

    let fb_size = fb.len();
    let words_per_row = (fb_size + 63) / 64;

    // Need slightly more than fb_size + 1 relations
    let need = fb_size + 30;

    // Compute sqrt_n
    let sqrt_n = isqrt_big(n);
    let sqrt_n_digits = sqrt_n.to_u64_digits();

    // For each prime in factor base, compute starting sieve positions
    // x ranges from -m_size to +m_size
    // We only take x > 0 (so Q(x) = (sqrt_n + x)^2 - n > 0 always)
    // Actually Q(x) > 0 for all x ≥ 0 since (sqrt_n)^2 ≤ n < (sqrt_n+1)^2,
    // so Q(0) = sqrt_n^2 - n < 0... hmm.
    //
    // Wait: sqrt_n = floor(sqrt(n)), so sqrt_n^2 ≤ n.
    // Q(x) = (sqrt_n + x)^2 - n. For x = 0: Q(0) = sqrt_n^2 - n ≤ 0.
    // For x = 1: Q(1) = (sqrt_n+1)^2 - n = sqrt_n^2 + 2*sqrt_n + 1 - n.
    // Since n < (sqrt_n+1)^2, Q(1) > 0. So x=1 gives Q(x) > 0.
    //
    // We use x from 1 to m_size (positive side only). Also need negative side:
    // For x < 0: sx = sqrt_n - |x|. Q = sx^2 - n. If sx^2 > n, positive.
    // sx = sqrt_n - |x|. sx^2 > n when (sqrt_n - |x|)^2 > n.
    // This happens when |x| < sqrt_n - sqrt(n) ≈ 0. So Q < 0 for most negative x.
    //
    // To get both positive and negative, use x starting from a value where Q > 0.
    // Simple: use x from 1 to 2*m_size.
    // Actually, the standard QS uses Q(x) = (floor(sqrt(n)) + x)^2 - n for x in [1, M].
    // We also include x in [-M, -1] by using (floor(sqrt(n)) - |x|) if that's > 0,
    // and checking Q(x) = (sqrt_n - |x|)^2 - n. But for most purposes, just use x > 0.
    //
    // Let's use x from 0 to 2*m_size. For each x, Q(x) = (sqrt_n + x)^2 - n.
    // Q(0) = sqrt_n^2 - n ≤ 0 (skip negative Q values).

    let sieve_len = 2 * m_size;
    let mut sieve = vec![0f32; sieve_len];

    for (idx, &(p, r1, r2)) in fb_roots.iter().enumerate() {
        let p64 = p as u64;
        if p == 2 {
            // Special case: sieve all even positions (Q(x) even when?)
            // Q(x) = (sqrt_n + x)^2 - n. For p=2, just mark positions where Q is even.
            // Actually skip 2 for sieving, handle separately or use a simple check.
            // For simplicity, just sieve every other position
            let mut i = 0;
            while i < sieve_len { sieve[i] += 0.693; i += 2; } // ln(2)
            continue;
        }
        let sqn_mod = big_mod_p_correct(&sqrt_n_digits, p64);
        // x in sieve corresponds to x+1 actual (since index 0 = x=1)
        // sieve[i] = Q(i+1), so x = i+1, sx = sqrt_n + i + 1
        // sx ≡ sqn_mod + i + 1 (mod p)
        // Q(x) ≡ 0 (mod p) when sx ≡ ±r1 (mod p)
        // i + 1 ≡ r1 - sqn_mod (mod p) → i ≡ r1 - sqn_mod - 1 (mod p)
        let log_p = (p as f32).ln();
        for &r in &[r1, r2] {
            let start_i = ((r as i64 - sqn_mod as i64 - 1).rem_euclid(p64 as i64)) as usize;
            let mut i = start_i;
            while i < sieve_len {
                sieve[i] += log_p;
                i += p as usize;
            }
        }
    }

    // Threshold: log of Q(x) at x = m_size
    // Q(m_size) ≈ 2 * sqrt_n * m_size
    let log_threshold = {
        let log_sqn = (bits as f64 / 2.0) * std::f64::consts::LN_2;
        let log_m = (m_size as f64).ln();
        (log_sqn + log_m + std::f64::consts::LN_2) as f32 * 0.70
    };

    let mut relations: Vec<QSRelation> = Vec::with_capacity(need + 10);

    for i in 0..sieve_len {
        if sieve[i] < log_threshold { continue; }
        if Instant::now() > deadline { break; }

        let x = (i as i64) + 1; // actual x value
        let sx = &sqrt_n + BigUint::from(x as u64);
        let sx2 = &sx * &sx;
        if &sx2 <= n { continue; }
        let qx = &sx2 - n;
        if qx.is_zero() { continue; }

        // Trial divide by factor base - use u128 fast path when possible
        let mut exps = vec![0u32; fb_size];
        let smooth = if let Some(mut rem128) = qx.to_u128() {
            // Fast u128 path
            let mut ok = true;
            for (j, &p) in fb.iter().enumerate() {
                let p128 = p as u128;
                while rem128 % p128 == 0 {
                    rem128 /= p128;
                    exps[j] += 1;
                }
            }
            rem128 == 1
        } else {
            // BigUint path
            let mut rem = qx.clone();
            let one = BigUint::one();
            for (j, &p) in fb.iter().enumerate() {
                let p64 = p as u64;
                // Quick check: compute rem mod p using fast arithmetic
                while {
                    let r = big_mod_p_correct(&rem.to_u64_digits(), p64);
                    r == 0
                } {
                    rem /= p64;
                    exps[j] += 1;
                }
            }
            rem == BigUint::one()
        };
        if !smooth { continue; }

        // Build parity bit vector
        let mut parity = vec![0u64; words_per_row];
        for (j, &e) in exps.iter().enumerate() {
            if e & 1 == 1 {
                parity[j / 64] |= 1u64 << (j % 64);
            }
        }

        relations.push(QSRelation { x, exps_parity: parity, exps_full: exps });

        if relations.len() >= need { break; }
    }

    if relations.len() < fb_size + 1 {
        return None;
    }

    let num_rel = relations.len();

    // Gaussian elimination over GF(2)
    // Matrix M: fb_size rows, num_rel cols
    // M[row][col] = bit at row of relation col's parity vector
    // We augment with identity on right: [M | I_{fb_size}]
    // After row reduction, we look for relations using the augmented part.
    //
    // Alternative: treat each relation as a row in GF(2)^{fb_size}.
    // Stack into matrix A (num_rel x fb_size). Row reduce.
    // When a row becomes zero, the combination of original rows gives a dependency.
    // Track combinations using augmented identity on LEFT: [I_{num_rel} | A].
    // Row op on A is same row op on I. Zero row in A = null vector in I part.
    //
    // This is O(num_rel * fb_size * num_rel / 64) using bit operations.
    // For num_rel ≈ fb_size ≈ 13000: O(13000^2 * 13000 / 64) ≈ 3.4 * 10^10. Too slow!
    //
    // Better: matrix is fb_size rows x num_rel cols. Row reduce over columns.
    // After reduction, free columns are null vectors.
    // Augment with identity on RIGHT: [M | I_{fb_size}].
    // Free column c: the kernel vector is e_c + {columns corresponding to pivots in rows}.
    // This is O(fb_size * num_rel / 64) per pivot = O(fb_size^2 * num_rel / 64).
    // For fb_size = 13000, num_rel = 13030: O(13000^2 * 13030 / 64) ≈ 3.4 * 10^10. Still slow.
    //
    // The key optimization: use column operations.
    // Matrix: fb_size rows x num_rel cols.
    // Row reduce: for each pivot row, eliminate that row from all other rows.
    // Keep track of which column operations we're doing.
    //
    // For practical QS, fb_size ≈ 100-10000 and num_rel ≈ fb_size + 20.
    // Time: O(fb_size^2 * num_rel / 64) using bitsets.

    // Let's use: matrix is (num_rel) cols x (fb_size) rows, stored row-major.
    // Each row is fb_size bits = words_per_row u64s.
    // But we also need to track which columns are combined.
    //
    // We'll store the matrix as rows, and separately track column combinations.

    // Matrix: fb_size rows, each row is a bit vector over num_rel bits
    // (each bit says which relation contributed to this row's parity)
    let words_per_relset = (num_rel + 63) / 64;

    // Build matrix rows: row j = parity of prime j across all relations
    // matrix[j][c/64] has bit c%64 set if relation c has odd exponent for prime j
    let mut matrix = vec![vec![0u64; words_per_relset]; fb_size];
    for (col, rel) in relations.iter().enumerate() {
        for j in 0..fb_size {
            if (rel.exps_parity[j / 64] >> (j % 64)) & 1 == 1 {
                matrix[j][col / 64] |= 1u64 << (col % 64);
            }
        }
    }

    // Augment each row with a "which relations are in this row's combination"
    // Initially: row j tracks just relation j... wait no.
    // We want: row j represents the XOR of some set of relation parity vectors.
    // Initially row j = relation j's parity (as a GF(2) vector over primes).
    // But we built it above as the j-th prime's parity across relations.
    //
    // I'm confusing myself. Let me restart with a cleaner formulation.
    //
    // Let's use a different approach: each RELATION is a vector in GF(2)^{fb_size}.
    // We have num_rel such vectors.
    // We want to find a nonzero linear combination (over GF(2)) that equals zero.
    // This is: find x in GF(2)^{num_rel} with Mx = 0, where M is fb_size x num_rel.
    //
    // Use Gaussian elimination on M (treating each column as a vector):
    // Augment with I_{num_rel} on top: store each column as (original_col_index, parity_vector).
    // Row reduce M. When a column becomes a zero vector, it's a null vector.
    //
    // This is equivalent to column operations on M.
    //
    // Column operations: swap columns, XOR one column into another.
    // Track these operations on a separate matrix.
    //
    // Let me implement this:
    // - col_matrix: fb_size rows x num_rel cols (sparse -> stored as cols)
    // - ops_matrix: num_rel rows x num_rel cols (tracking col ops), starts as identity
    //
    // Column reduce col_matrix. Track ops in ops_matrix.
    // When a column of col_matrix is zero, the corresponding column of ops_matrix is the null vector.

    // Store each column as a bitset of fb_size bits
    let words_per_col = (fb_size + 63) / 64;
    let mut cols: Vec<Vec<u64>> = Vec::with_capacity(num_rel);
    for rel in &relations {
        cols.push(rel.exps_parity.clone());
    }

    // ops_matrix: num_rel columns, each column is a num_rel-bit vector (identity initially)
    let mut ops: Vec<Vec<u64>> = Vec::with_capacity(num_rel);
    for i in 0..num_rel {
        let mut v = vec![0u64; words_per_relset];
        v[i / 64] |= 1u64 << (i % 64);
        ops.push(v);
    }

    // Gaussian elimination: find pivot rows
    let mut pivot_col_for_row = vec![usize::MAX; fb_size]; // which column is the pivot for row j
    let mut pivot_row_for_col = vec![usize::MAX; num_rel]; // which row is the pivot for col c

    let mut current_pivot_row = 0usize;
    for col in 0..num_rel {
        if current_pivot_row >= fb_size { break; }
        if Instant::now() > deadline { return None; }

        // Find the leading nonzero bit in col >= current_pivot_row
        let word = current_pivot_row / 64;
        let mask = !((1u64 << (current_pivot_row % 64)) - 1);
        let mut pivot_row = usize::MAX;

        // Scan from current_pivot_row downward in this column
        let col_vec = &cols[col];
        'find_pivot: for w in word..words_per_col {
            let mut bits = col_vec[w];
            if w == word { bits &= mask; }
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                let row = w * 64 + bit;
                if row >= fb_size { break 'find_pivot; }
                pivot_row = row;
                break 'find_pivot;
            }
        }

        if pivot_row == usize::MAX { continue; } // free column, skip for now

        // Swap cols[col] leading row to current_pivot_row if needed
        if pivot_row != current_pivot_row {
            // We need to "swap rows", but we store columns.
            // Swapping rows in the column representation: swap bit pivot_row and current_pivot_row
            // in every column.
            // This is expensive if done for every column. Instead, just track a row permutation.
            // For simplicity, swap the actual bits (O(num_rel) per pivot).
            // Since we'll do at most fb_size pivots, total: O(fb_size * num_rel / 64) operations.
            for c in col..num_rel {
                let w1 = current_pivot_row / 64; let b1 = current_pivot_row % 64;
                let w2 = pivot_row / 64; let b2 = pivot_row % 64;
                let bit1 = (cols[c][w1] >> b1) & 1;
                let bit2 = (cols[c][w2] >> b2) & 1;
                if bit1 != bit2 {
                    cols[c][w1] ^= 1u64 << b1;
                    cols[c][w2] ^= 1u64 << b2;
                }
            }
        }

        pivot_row_for_col[col] = current_pivot_row;
        pivot_col_for_row[current_pivot_row] = col;

        // Eliminate this pivot row from all other columns
        for other_col in 0..num_rel {
            if other_col == col { continue; }
            let w = current_pivot_row / 64;
            let b = current_pivot_row % 64;
            if (cols[other_col][w] >> b) & 1 == 0 { continue; }
            // XOR col into other_col
            let col_copy = cols[col].clone();
            let len = words_per_col;
            for w2 in 0..len {
                cols[other_col][w2] ^= col_copy[w2];
            }
            let ops_copy = ops[col].clone();
            let ops_len = words_per_relset;
            for w2 in 0..ops_len {
                ops[other_col][w2] ^= ops_copy[w2];
            }
        }

        current_pivot_row += 1;
    }

    // Find null vectors (columns with zero column vector in cols)
    let one_big = BigUint::one();
    for col in 0..num_rel {
        if Instant::now() > deadline { return None; }
        if pivot_row_for_col[col] != usize::MAX { continue; } // not a free column

        // Check if cols[col] is indeed zero
        if cols[col].iter().any(|&w| w != 0) { continue; }

        // The ops[col] vector tells us which original relations to XOR
        // Collect indices of set bits in ops[col]
        let mut subset: Vec<usize> = Vec::new();
        for w in 0..words_per_relset {
            let mut bits = ops[col][w];
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                let rel_idx = w * 64 + bit;
                if rel_idx < num_rel { subset.push(rel_idx); }
                bits &= bits - 1;
            }
        }

        if subset.is_empty() { continue; }

        // Compute X = product of (sqrt_n + x_i) mod n, and exponents
        let mut x_prod = BigUint::one();
        let mut exp_sum = vec![0u64; fb_size];

        for &ri in &subset {
            let x = relations[ri].x;
            let sx = &sqrt_n + BigUint::from(x as u64);
            x_prod = (&x_prod * &sx) % n;
            for j in 0..fb_size {
                exp_sum[j] += relations[ri].exps_full[j] as u64;
            }
        }

        // Verify all exponents are even
        if exp_sum.iter().any(|&e| e & 1 != 0) { continue; }

        // Compute Y = product of p^(exp/2) mod n
        let mut y = BigUint::one();
        for j in 0..fb_size {
            let half = exp_sum[j] / 2;
            if half > 0 {
                let p = BigUint::from(fb[j] as u64);
                let p_pow = p.pow(half as u32);
                y = (y * p_pow) % n;
            }
        }

        // Try gcd(X ± Y, n)
        for &plus in &[true, false] {
            let diff = if plus {
                if x_prod >= y { &x_prod - &y } else { n - &y + &x_prod }
            } else {
                (&x_prod + &y) % n
            };

            if diff.is_zero() { continue; }
            let g = diff.gcd(n);
            if g != one_big && &g != n {
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
    let y_start = BigUint::from(y_val) % (n - &two) + &two;
    let mut y = y_start;
    let mut r: u64 = 1;
    let mut q = one.clone();
    let mut x = y.clone();
    let mut ys = y.clone();
    let batch: u64 = 128;

    let f = |v: &BigUint| -> BigUint { (v * v + &c_big) % n };

    loop {
        x = y.clone();
        for _ in 0..r { y = f(&y); }
        let mut k: u64 = 0;
        let mut d = one.clone();
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
        if d != one {
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
            if d != one && &d != n { return Some(d); }
            return None;
        }
        r *= 2;
        if r > (1u64 << 26) { return None; }
    }
}

fn factor_big(n: &BigUint, deadline: Instant) -> Option<(BigUint, BigUint)> {
    let two = BigUint::from(2u64);
    if n % &two == BigUint::zero() { return Some((two.clone(), n / &two)); }

    // Small trial division
    for i in (3u64..1_000_000).step_by(2) {
        let bi = BigUint::from(i);
        if n % &bi == BigUint::zero() { return Some((bi.clone(), n / &bi)); }
    }

    // Try QS
    if Instant::now() < deadline.checked_sub(Duration::from_millis(500)).unwrap_or(deadline) {
        if let Some(f) = quadratic_sieve(n, deadline) {
            let q = n / &f;
            let (p, q) = if f <= q { (f, q) } else { (q.clone(), n / &q) };
            return Some((p, q));
        }
    }

    // Fallback: parallel Pollard's rho with BigUint
    let stopped = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<BigUint>();

    for t in 0..8usize {
        let tx = tx.clone(); let stopped = stopped.clone();
        let n_clone = n.clone();
        let seed: u64 = 0xdeadbeef1234abcd ^ (t as u64 * 0x9e3779b97f4a7c15);
        thread::spawn(move || {
            let mut rng = seed; xorshift64(&mut rng);
            loop {
                if stopped.load(Ordering::Relaxed) { return; }
                let c = (xorshift64(&mut rng) % 10000) + 1;
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
        } else { i += 1; }
    }

    let start = Instant::now();
    let deadline = start + Duration::from_millis(time_limit_secs * 1000).saturating_sub(Duration::from_millis(300));

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

        let result = if let Some(n_small) = n.to_u128() {
            if n_small <= 3 { None }
            else { factor_u128_parallel(n_small).map(|(p,q)| (BigUint::from(p), BigUint::from(q))) }
        } else {
            factor_big(n, deadline)
        };

        match result {
            Some((p, q)) => { writeln!(out, "{{\"id\": \"{}\", \"answer\": \"{} {}\"}}", id, p, q).unwrap(); }
            None => { writeln!(out, "{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}", id).unwrap(); }
        }
        out.flush().unwrap();
    }
}
