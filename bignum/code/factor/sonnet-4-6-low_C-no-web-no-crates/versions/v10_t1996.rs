use num_bigint::{BigUint, BigInt, Sign};
use num_integer::Integer;
use num_traits::{Zero, One, ToPrimitive};
use std::io::{self, BufRead, Write, BufWriter};
use std::time::{Instant, Duration};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};

// ===== JSON =====
fn parse_id(line: &str) -> String {
    if let Some(pos) = line.find("\"id\"") {
        let after = &line[pos+4..];
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
    let after = &line[pos+3..];
    let cp = after.find(':')?;
    let s = after[cp+1..].trim_start();
    let end = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
    BigUint::parse_bytes(s[..end].as_bytes(), 10)
}

// ===== Modular arithmetic =====
#[inline(always)]
fn mulmod64(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}
fn powmod64(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64;
    b %= m;
    while e > 0 {
        if e & 1 == 1 { r = mulmod64(r, b, m); }
        b = mulmod64(b, b, m);
        e >>= 1;
    }
    r
}

// Get high 64 bits of 64x64 multiplication using ARM64 umulh
#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn mulhi64(a: u64, b: u64) -> u64 {
    let hi: u64;
    unsafe {
        std::arch::asm!(
            "umulh {0}, {1}, {2}",
            out(reg) hi,
            in(reg) a,
            in(reg) b,
            options(pure, nomem, nostack)
        );
    }
    hi
}

#[cfg(not(target_arch = "aarch64"))]
#[inline(always)]
fn mulhi64(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) >> 64) as u64
}

// Full 128x128->256 bit multiply, returns (hi128, lo128)
#[inline(always)]
fn mul256(a: u128, b: u128) -> (u128, u128) {
    let a0 = a as u64;
    let a1 = (a >> 64) as u64;
    let b0 = b as u64;
    let b1 = (b >> 64) as u64;

    let p00_lo = a0.wrapping_mul(b0);
    let p00_hi = mulhi64(a0, b0);
    let p10_lo = a1.wrapping_mul(b0);
    let p10_hi = mulhi64(a1, b0);
    let p01_lo = a0.wrapping_mul(b1);
    let p01_hi = mulhi64(a0, b1);
    let p11_lo = a1.wrapping_mul(b1);
    let p11_hi = mulhi64(a1, b1);

    // Accumulate: total = p11*2^128 + (p10+p01)*2^64 + p00
    // lo128 = p00 + (p10+p01)*2^64
    // hi128 = p11 + carry from lo128
    let (mid_lo, c1) = p10_lo.overflowing_add(p01_lo);
    let mid_hi = p10_hi.wrapping_add(p01_hi).wrapping_add(c1 as u64);

    let lo0 = p00_lo as u128;
    let lo1_part = (p00_hi as u128) + (mid_lo as u128);
    let lo1 = lo1_part as u64;
    let carry1 = (lo1_part >> 64) as u64;

    let lo128 = lo0 | ((lo1 as u128) << 64);

    let hi_lo = (p11_lo as u128).wrapping_add(mid_hi as u128).wrapping_add(carry1 as u128);
    let hi128 = hi_lo.wrapping_add((p11_hi as u128) << 64);

    (hi128, lo128)
}

// Reduce hi*2^128 + lo mod m using precomputed constants
// Requires: precomputed floor(2^256 / m) for Barrett, or just do it iteratively
// For our use: hi < 2^128, but typically hi << 2^128 for our n sizes
fn mod256(hi: u128, lo: u128, m: u128) -> u128 {
    if hi == 0 { return lo % m; }
    // hi * 2^128 + lo mod m
    // Since hi < 2^128, we compute hi * (2^128 mod m) + lo, mod m
    // 2^128 mod m: compute once (could be precomputed, but for now compute here)
    // Actually, a simpler approach: use the binary method only for the "shift" part
    // which is a much smaller number.

    // For n up to 38 decimal digits (~126 bits), hi is typically very small
    // (since both operands are < n < 2^126, product hi < 2^252-128 = 2^124)

    // Method: repeated halving via Barrett-like approach
    // Compute pow128 = 2^128 mod m via binary doubling (fast since hi is small)
    let mut pow128 = 1u128;
    for _ in 0..128 {
        pow128 = pow128.wrapping_add(pow128);
        if pow128 >= m { pow128 -= m; }
    }
    // hi * pow128 mod m: use same approach for hi * pow128
    // hi can be up to 2^124 for our use case, but for 38-digit n, hi << n
    let hi_mod = hi % m;
    // Compute hi_mod * pow128 mod m via binary method (hi_mod < m < 2^126)
    // But this is slow again...

    // Actually: for our Pollard's rho, a,b < n < 2^126.
    // Product: a*b < 2^252. hi = product >> 128 < 2^(252-128) = 2^124.
    // For 38-digit n (~2^126): hi < 2^124... but pow128 < n < 2^126.
    // hi * pow128 < 2^(124+126) = 2^250. Still overflows.

    // SIMPLEST CORRECT APPROACH: just use the binary method for the hi part
    // The difference: the hi part is small (typically hi < 2^64 for 64-bit n in product)

    // For 32-digit n (d=16), n ≈ 2^107. a,b < n < 2^107. Product hi < 2^(214-128) = 2^86.
    // hi * pow128: hi < 2^86, pow128 < n < 2^107. Product < 2^193. Still overflow.

    // Use binary method for this multiplication:
    let mut result_hi = 0u128;
    let mut base = hi_mod;
    let mut exp = pow128;
    // No, this is mulmod128(hi_mod, pow128, m)...
    // Let me just call binary mulmod128 for this one
    let hi_contribution = mulmod128_binary(hi_mod, pow128, m);
    let lo_mod = lo % m;
    let r = lo_mod + hi_contribution;
    if r >= m { r - m } else { r }
}

fn mulmod128_binary(mut a: u128, mut b: u128, m: u128) -> u128 {
    let mut result = 0u128;
    a %= m;
    b %= m;
    while b > 0 {
        if b & 1 == 1 {
            result += a;
            if result >= m { result -= m; }
        }
        a <<= 1;
        if a >= m { a -= m; }
        b >>= 1;
    }
    result
}

// Fast mulmod128 using hardware 64x64 multiplication
#[inline]
fn mulmod128(a: u128, b: u128, m: u128) -> u128 {
    // Fast path for both in u64
    if a >> 64 == 0 && b >> 64 == 0 {
        return (a * b) % m;
    }
    // Fast path: if m fits in u64
    if m <= u64::MAX as u128 {
        return ((a % m) * (b % m)) % m;
    }
    // Full 128x128->256 multiply then reduce
    let (hi, lo) = mul256(a, b);
    mod256(hi, lo, m)
}

fn powmod128(mut b: u128, mut e: u128, m: u128) -> u128 {
    let mut r = 1u128;
    b %= m;
    while e > 0 {
        if e & 1 == 1 { r = mulmod128(r, b, m); }
        b = mulmod128(b, b, m);
        e >>= 1;
    }
    r
}

// ===== Primality =====
fn is_prime_u64(n: u64) -> bool {
    if n < 2 { return false; }
    if n == 2 || n == 3 || n == 5 || n == 7 { return true; }
    if n % 2 == 0 || n % 3 == 0 || n % 5 == 0 { return false; }
    let mut d = n - 1; let mut r = 0u32;
    while d % 2 == 0 { d /= 2; r += 1; }
    'outer: for &a in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if a >= n { continue; }
        let mut x = powmod64(a, d, n);
        if x == 1 || x == n-1 { continue; }
        for _ in 0..r-1 {
            x = mulmod64(x, x, n);
            if x == n-1 { continue 'outer; }
        }
        return false;
    }
    true
}

fn is_prime_u128(n: u128) -> bool {
    if n <= u64::MAX as u128 { return is_prime_u64(n as u64); }
    if n % 2 == 0 { return false; }
    let mut d = n-1; let mut r = 0u32;
    while d % 2 == 0 { d /= 2; r += 1; }
    'outer: for &a in &[2u128,3,5,7,11,13,17,19,23,29,31,37,41,43,47] {
        let mut x = powmod128(a, d, n);
        if x == 1 || x == n-1 { continue; }
        for _ in 0..r-1 {
            x = mulmod128(x, x, n);
            if x == n-1 { continue 'outer; }
        }
        return false;
    }
    true
}

fn is_prime_big(n: &BigUint) -> bool {
    if let Some(n128) = n.to_u128() { return is_prime_u128(n128); }
    let two = BigUint::from(2u32); let one = BigUint::one();
    if n % &two == BigUint::zero() { return false; }
    let nm1 = n - &one;
    let mut d = nm1.clone(); let mut r = 0u32;
    while &d % &two == BigUint::zero() { d >>= 1; r += 1; }
    'outer: for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37,41,43,47] {
        let ab = BigUint::from(a);
        if ab >= *n { continue; }
        let mut x = ab.modpow(&d, n);
        if x == one || x == nm1 { continue; }
        for _ in 0..r-1 { x = x.modpow(&two, n); if x == nm1 { continue 'outer; } }
        return false;
    }
    true
}

// ===== Integer square root =====
fn isqrt_big(n: &BigUint) -> BigUint {
    if n.is_zero() { return BigUint::zero(); }
    let mut x = BigUint::one() << ((n.bits() as usize + 1) / 2);
    loop {
        let q = n / &x;
        if q >= x { return x; }
        x = (x + q) >> 1usize;
    }
}

// ===== GCD =====
fn gcd64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 { let t = b; b = a%b; a = t; } a
}
fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 { let t = b; b = a%b; a = t; } a
}

// ===== Pollard's Rho =====

fn pollard_brent_u64(n: u64, c: u64) -> Option<u64> {
    if n % 2 == 0 { return Some(2); }
    let mut y = 2u64; let mut r = 1u64; let mut q = 1u64;
    let mut x = 2u64; let mut ys = 2u64; let mut d = 1u64;
    let m = 256u64;
    loop {
        x = y;
        for _ in 0..r {
            y = (mulmod64(y, y, n) + c) % n;
        }
        let mut k = 0u64;
        loop {
            ys = y;
            let step = m.min(r-k);
            for _ in 0..step {
                y = (mulmod64(y, y, n) + c) % n;
                let diff = if y > x { y-x } else { x-y };
                q = mulmod64(q, diff, n);
            }
            d = gcd64(q, n);
            k += m;
            if k >= r || d != 1 { break; }
        }
        if d != 1 { break; }
        r <<= 1;
        if r > 1u64 << 28 {
            d = n;
            break;
        }
    }
    if d == n {
        loop {
            ys = (mulmod64(ys, ys, n) + c) % n;
            let diff = if ys > x { ys-x } else { x-ys };
            d = gcd64(diff, n);
            if d != 1 { break; }
            if ys == x { return None; }
        }
    }
    if d == 1 || d == n { None } else { Some(d) }
}

fn pollard_brent_u128(n: u128, c: u128) -> Option<u128> {
    if n % 2 == 0 { return Some(2); }
    let f = |x: u128| -> u128 {
        let sq = mulmod128(x, x, n);
        let r = sq + c;
        if r >= n { r - n } else { r }
    };
    let mut y = 2u128; let mut r = 1u128; let mut q = 1u128;
    let mut x = 2u128; let mut ys = 2u128; let mut d = 1u128;
    let m = 256u128;
    loop {
        x = y;
        for _ in 0..r { y = f(y); }
        let mut k = 0u128;
        loop {
            ys = y;
            let step = m.min(r-k);
            for _ in 0..step {
                y = f(y);
                let diff = if y > x { y-x } else { x-y };
                q = mulmod128(q, diff, n);
            }
            d = gcd128(q, n);
            k += m;
            if k >= r || d != 1 { break; }
        }
        if d != 1 { break; }
        r <<= 1;
        if r > 1u128 << 24 { return None; } // limit per c; caller retries with different c
    }
    if d == n {
        loop {
            ys = f(ys);
            let diff = if ys > x { ys-x } else { x-ys };
            d = gcd128(diff, n);
            if d != 1 { break; }
            if ys == x { return None; }
        }
    }
    if d == 1 || d == n { None } else { Some(d) }
}

fn pollard_brent_big(n: &BigUint, c: u64, stop: &Arc<AtomicBool>) -> Option<BigUint> {
    let one = BigUint::one();
    let c_big = BigUint::from(c);
    let f = |x: BigUint| -> BigUint {
        let sq = x.modpow(&BigUint::from(2u32), n);
        let r = sq + &c_big;
        if r >= *n { r - n } else { r }
    };
    let mut y = BigUint::from(2u32); let mut r = 1usize; let mut q = one.clone();
    let mut x = BigUint::from(2u32); let mut ys = BigUint::from(2u32);
    let m = 512usize;
    loop {
        if stop.load(Ordering::Relaxed) { return None; }
        x = y.clone();
        for _ in 0..r { y = f(y); }
        let mut k = 0usize;
        loop {
            ys = y.clone();
            let step = m.min(r-k);
            for _ in 0..step {
                y = f(y.clone());
                let diff = if y > x { y.clone()-x.clone() } else { x.clone()-y.clone() };
                q = q * &diff % n;
            }
            let d = q.gcd(n);
            k += m;
            if k >= r || d != one {
                if d != one && &d != n { return Some(d); }
                if &d == n { break; }
                break;
            }
        }
        // Check if d != 1
        let d2 = q.gcd(n);
        if d2 != one {
            if &d2 != n { return Some(d2); }
            // backtrack
            let mut ys2 = ys.clone();
            loop {
                ys2 = f(ys2);
                let diff = if ys2 > x { ys2.clone()-x.clone() } else { x.clone()-ys2.clone() };
                let d3 = diff.gcd(n);
                if d3 != one {
                    if &d3 != n { return Some(d3); }
                    return None;
                }
                if ys2 == x { return None; }
            }
        }
        r <<= 1;
        if r > 1 << 22 { return None; }
    }
    None
}

// ===== Sieve of Eratosthenes =====
fn sieve_primes(limit: usize) -> Vec<u32> {
    if limit < 2 { return vec![]; }
    let mut s = vec![true; limit+1];
    s[0] = false; if limit > 0 { s[1] = false; }
    let mut i = 2;
    while i*i <= limit { if s[i] { let mut j=i*i; while j<=limit { s[j]=false; j+=i; } } i+=1; }
    (2..=limit).filter(|&i| s[i]).map(|i| i as u32).collect()
}

// ===== Jacobi symbol =====
fn jacobi(mut a: i64, mut n: i64) -> i32 {
    if n <= 0 || n%2 == 0 { return 0; }
    let mut r = 1i32;
    a = ((a%n)+n)%n;
    while a != 0 {
        while a%2 == 0 { a/=2; let nm=n%8; if nm==3||nm==5 { r=-r; } }
        std::mem::swap(&mut a, &mut n);
        if a%4==3 && n%4==3 { r=-r; }
        a%=n;
    }
    if n==1 { r } else { 0 }
}

// ===== Tonelli-Shanks =====
fn tonelli(n: u64, p: u64) -> u64 {
    if n==0 { return 0; }
    if p==2 { return n&1; }
    if p%4==3 { return powmod64(n,(p+1)/4,p); }
    if p%8==5 {
        let v = powmod64(mulmod64(2,n,p),(p-5)/8,p);
        let i = mulmod64(mulmod64(mulmod64(2,n,p),v,p),v,p);
        return mulmod64(mulmod64(n,v,p),(i+p-1)%p,p);
    }
    let mut q=p-1; let mut s=0u32;
    while q%2==0 { q/=2; s+=1; }
    let mut z=2u64;
    while powmod64(z,(p-1)/2,p) != p-1 { z+=1; }
    let mut mm=s;
    let mut c=powmod64(z,q,p);
    let mut t=powmod64(n,q,p);
    let mut r=powmod64(n,(q+1)/2,p);
    loop {
        if t==0 { return 0; }
        if t==1 { return r; }
        let mut i=1u32; let mut tmp=mulmod64(t,t,p);
        while tmp!=1 { tmp=mulmod64(tmp,tmp,p); i+=1; }
        if i>=mm { return p; }
        let b=powmod64(c,1u64<<(mm-i-1),p);
        mm=i; c=mulmod64(b,b,p); t=mulmod64(t,c,p); r=mulmod64(r,b,p);
    }
}

// ===== Quadratic Sieve =====

fn biguint_mod_u32(n: &BigUint, m: u32) -> u32 {
    (n % BigUint::from(m)).to_u32().unwrap_or(0)
}

fn qs_params(nd: usize) -> (usize, usize) {
    let ln_n = nd as f64 * 2.302585;
    let ln_ln = ln_n.ln().max(1.0);
    let exp = 0.5 * (ln_n * ln_ln).sqrt();
    let b = (exp.exp() as usize).clamp(500, 3_000_000);
    let m = (b * 50).clamp(200_000, 50_000_000);
    (b, m)
}

// Trial divide qx (BigUint) by all primes in fb, return (remainder, exponent_vec_mod2, full_exp_vec)
fn trial_factor_qs(qx: &BigUint, fb: &[u32]) -> Option<(Vec<u8>, Vec<u32>)> {
    let mut rem = qx.clone();
    let one = BigUint::one();
    let mut ev = vec![0u8; fb.len()];
    let mut fv = vec![0u32; fb.len()];

    for (i, &p) in fb.iter().enumerate() {
        let p64 = p as u64;
        // Quick check: does p divide rem?
        // For small primes, check rem % p
        let p_big = BigUint::from(p64);
        let mut cnt = 0u32;
        loop {
            // Use rem % p (small modulus)
            let r = &rem % &p_big;
            if r.is_zero() {
                rem /= &p_big;
                cnt += 1;
            } else {
                break;
            }
        }
        fv[i] = cnt;
        ev[i] = (cnt & 1) as u8;

        // Early exit: if rem is 1, done
        if rem == one { break; }
        // If rem is small enough, switch to u64
        if let Some(rem64) = rem.to_u64() {
            // trial divide rem64 by remaining primes
            for j in (i+1)..fb.len() {
                let p2 = fb[j] as u64;
                if p2 * p2 > rem64 { break; }
                let mut cnt2 = 0u32;
                let mut r = rem64;
                while r % p2 == 0 { r /= p2; cnt2 += 1; }
                fv[j] = cnt2;
                ev[j] = (cnt2 & 1) as u8;
                if r == 1 {
                    rem = BigUint::one();
                    // zero out remaining
                    break;
                }
                // Update rem
                if cnt2 > 0 {
                    let mut rr = rem64;
                    for _ in 0..cnt2 { rr /= p2; }
                    rem = BigUint::from(rr);
                }
            }
            if let Some(r64) = rem.to_u64() {
                if r64 != 1 {
                    // Check if r64 is 1 of the factor base primes (for partial relations)
                    // For now, not smooth
                    return None;
                }
            }
            break;
        }
    }

    if rem != one { return None; }
    Some((ev, fv))
}

fn quadratic_sieve(n: &BigUint, deadline: Instant) -> Option<BigUint> {
    let one = BigUint::one();
    let nd = n.to_str_radix(10).len();
    if nd < 6 { return None; }

    let (b_bound, m_half) = qs_params(nd);

    let all_primes = sieve_primes(b_bound);

    // Filter factor base: primes where n is QR
    let mut fb: Vec<u32> = vec![2];
    for &p in &all_primes[1..] {
        let nm = biguint_mod_u32(n, p) as i64;
        if jacobi(nm, p as i64) == 1 {
            fb.push(p);
        }
    }
    let fb_size = fb.len();
    if fb_size < 30 { return None; }

    let sqrt_n = isqrt_big(n);
    let base = &sqrt_n + &BigUint::one(); // Q(x) = (base+x)^2 - n >= 0

    // For each prime, compute starting sieve positions
    // Q(x) ≡ 0 (mod p)  iff  base+x ≡ ±sqrt(n) (mod p)
    let base_mod: Vec<u64> = fb.iter().map(|&p| {
        let bm = biguint_mod_u32(&base, p) as u64;
        bm
    }).collect();

    let roots: Vec<(u64, u64)> = fb.iter().enumerate().map(|(i, &p)| {
        let p64 = p as u64;
        if p == 2 {
            let nm = biguint_mod_u32(n, 2) as u64;
            let r = nm & 1;
            let s = ((r as i64 - base_mod[i] as i64).rem_euclid(2)) as u64;
            (s, s)
        } else {
            let nm = biguint_mod_u32(n, p) as u64;
            let r = tonelli(nm, p64);
            if r >= p64 { return (0, 0); }
            let r1 = ((r as i64 - base_mod[i] as i64).rem_euclid(p64 as i64)) as u64;
            let r2 = (((p64-r) as i64 - base_mod[i] as i64).rem_euclid(p64 as i64)) as u64;
            (r1, r2)
        }
    }).collect();

    let log_p: Vec<f32> = fb.iter().map(|&p| (p as f64).ln() as f32).collect();

    // Threshold: log(Q(M)) ≈ log(2 * sqrt_n * M)
    let log_qm = (nd as f64 * 2.302585 / 2.0) + (m_half as f64).ln();
    let threshold = (log_qm * 0.80) as f32;

    let need = fb_size + 60;

    struct Rel {
        a: BigUint,
        ev: Vec<u8>,
        fv: Vec<u32>,
    }

    let mut rels: Vec<Rel> = Vec::with_capacity(need + 20);
    let sieve_len = m_half * 2;
    let mut sieve = vec![0.0f32; sieve_len];

    let mut chunk_offset: i64 = 0;

    while rels.len() < need && Instant::now() < deadline {
        // Reset
        for v in &mut sieve { *v = 0.0; }

        // Fill sieve
        for i in 0..fb_size {
            let p = fb[i] as usize;
            let lp = log_p[i];
            let (r1, r2) = roots[i];
            let s1 = ((r1 as i64 - chunk_offset).rem_euclid(p as i64)) as usize;
            let s2 = ((r2 as i64 - chunk_offset).rem_euclid(p as i64)) as usize;
            let mut j = s1;
            while j < sieve_len { sieve[j] += lp; j += p; }
            if s1 != s2 {
                let mut j = s2;
                while j < sieve_len { sieve[j] += lp; j += p; }
            }
        }

        // Find smooth candidates
        for i in 0..sieve_len {
            if sieve[i] < threshold { continue; }
            let x = chunk_offset + i as i64;
            let a = if x >= 0 {
                &base + BigUint::from(x as u64)
            } else {
                continue; // shouldn't happen (chunk_offset >= 0)
            };
            let asq = &a * &a;
            if asq < *n { continue; }
            let qx = asq - n;
            if qx.is_zero() { continue; }

            if let Some((ev, fv)) = trial_factor_qs(&qx, &fb) {
                rels.push(Rel { a: a.clone(), ev, fv });
                if rels.len() >= need { break; }
            }
        }

        chunk_offset += sieve_len as i64;
        if chunk_offset > 2_000_000_000 { break; }
    }

    if rels.len() < fb_size / 2 + 10 {
        return None;
    }

    // Gaussian elimination over GF(2)
    let nrows = rels.len();
    let ncols = fb_size;
    let words = (ncols + 63) / 64;

    let mut mat: Vec<Vec<u64>> = rels.iter().map(|r| {
        let mut row = vec![0u64; words];
        for j in 0..ncols {
            if r.ev[j] == 1 { row[j/64] |= 1u64 << (j%64); }
        }
        row
    }).collect();

    // Track combinations (symmetric difference of original row indices)
    let mut hist: Vec<Vec<usize>> = (0..nrows).map(|i| vec![i]).collect();
    let mut cur = 0usize;

    for col in 0..ncols {
        if cur >= nrows { break; }
        let piv = (cur..nrows).find(|&r| (mat[r][col/64] >> (col%64)) & 1 == 1);
        if let Some(p) = piv {
            mat.swap(cur, p); hist.swap(cur, p);
            for r in 0..nrows {
                if r != cur && (mat[r][col/64] >> (col%64)) & 1 == 1 {
                    for w in 0..words { let v = mat[cur][w]; mat[r][w] ^= v; }
                    let h = hist[cur].clone();
                    for &idx in &h {
                        if let Some(pos) = hist[r].iter().position(|&x| x==idx) {
                            hist[r].remove(pos);
                        } else {
                            hist[r].push(idx);
                        }
                    }
                }
            }
            cur += 1;
        }
    }

    let n_bigint = BigInt::from_biguint(Sign::Plus, n.clone());

    for row in 0..nrows {
        if mat[row].iter().any(|&w| w != 0) { continue; }
        let contrib = &hist[row];
        if contrib.is_empty() { continue; }

        // Product of a values mod n
        let mut x = BigInt::from(1i32);
        for &ri in contrib {
            x = x * BigInt::from_biguint(Sign::Plus, rels[ri].a.clone()) % &n_bigint;
        }
        x = ((x % &n_bigint) + &n_bigint) % &n_bigint;

        // Combined exponents (should all be even)
        let mut total = vec![0u32; fb_size];
        for &ri in contrib {
            for j in 0..fb_size { total[j] += rels[ri].fv[j]; }
        }
        if total.iter().any(|&e| e%2 != 0) { continue; }

        // y = product of p^(e/2)
        let mut y = BigInt::from(1i32);
        for j in 0..fb_size {
            let h = total[j]/2;
            if h > 0 {
                let pw = BigUint::from(fb[j] as u64).pow(h);
                y = y * BigInt::from_biguint(Sign::Plus, pw) % &n_bigint;
            }
        }
        y = ((y % &n_bigint) + &n_bigint) % &n_bigint;

        let xb = x.magnitude().clone();
        let yb = y.magnitude().clone();

        let diff = if xb > yb { (xb.clone()-yb.clone()).gcd(n) } else { (yb.clone()-xb.clone()).gcd(n) };
        if diff != one && &diff != n { return Some(diff); }
        let sum = (xb + yb).gcd(n);
        if sum != one && &sum != n { return Some(sum); }
    }

    None
}

// ===== Trial division (small primes) =====
const SMALL_PRIMES: &[u32] = &[
    2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
    101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,
    193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,
    293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,
    409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,
    521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,
    641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,
    757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,
    881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,
];

fn trial_divide(n: &BigUint) -> Option<BigUint> {
    for &p in SMALL_PRIMES {
        let pb = BigUint::from(p as u64);
        if n % &pb == BigUint::zero() && n != &pb { return Some(pb); }
    }
    None
}

// ===== Main factor =====
fn factor_number(n: &BigUint, deadline: Instant, stop: &Arc<AtomicBool>) -> Option<BigUint> {
    let one = BigUint::one();
    if n <= &one { return None; }
    if let Some(d) = trial_divide(n) { return Some(d); }
    if is_prime_big(n) { return None; }

    // u64 fast path
    if let Some(n64) = n.to_u64() {
        for c in 1..1000u64 {
            if let Some(d) = pollard_brent_u64(n64, c) {
                if d != n64 && d != 1 { return Some(BigUint::from(d)); }
            }
        }
        return None;
    }

    // u128 fast path - parallel
    if let Some(n128) = n.to_u128() {
        if !is_prime_u128(n128) {
            let n128 = std::sync::Arc::new(n128);
            let found = std::sync::Arc::new(Mutex::new(None::<u128>));
            let done = std::sync::Arc::new(AtomicBool::new(false));
            let n_threads = 10usize;
            let mut handles = Vec::new();
            for tid in 0..n_threads {
                let nc = std::sync::Arc::clone(&n128);
                let fc = std::sync::Arc::clone(&found);
                let dc = std::sync::Arc::clone(&done);
                handles.push(std::thread::spawn(move || {
                    let n = *nc;
                    for c in (tid as u128 + 1..).step_by(n_threads).take(500) {
                        if dc.load(Ordering::Relaxed) { return; }
                        if let Some(d) = pollard_brent_u128(n, c) {
                            if d != n && d != 1 {
                                let mut f = fc.lock().unwrap();
                                if f.is_none() { *f = Some(d); }
                                dc.store(true, Ordering::Relaxed);
                                return;
                            }
                        }
                    }
                }));
            }
            // Poll until done or deadline
            loop {
                if done.load(Ordering::Relaxed) { break; }
                if Instant::now() >= deadline || stop.load(Ordering::Relaxed) { break; }
                std::thread::sleep(Duration::from_millis(5));
            }
            done.store(true, Ordering::Relaxed);
            for h in handles { let _ = h.join(); }
            let result = found.lock().unwrap().clone();
            if let Some(d) = result {
                return Some(BigUint::from(d));
            }
        }
        return None;
    }

    let n_str = n.to_str_radix(10);
    let nd = n_str.len();

    // Parallel BigUint Pollard's rho + QS
    let n_arc = Arc::new(n.clone());
    let rho_result = Arc::new(Mutex::new(None::<BigUint>));
    let rho_stop = Arc::new(AtomicBool::new(false));

    let n_threads = 8usize;
    let mut handles = Vec::new();

    for tid in 0..n_threads {
        let nc = Arc::clone(&n_arc);
        let rc = Arc::clone(&rho_result);
        let sf = Arc::clone(&rho_stop);
        handles.push(std::thread::spawn(move || {
            for c in (tid as u64 + 1..).step_by(n_threads).take(200) {
                if sf.load(Ordering::Relaxed) { return; }
                if let Some(d) = pollard_brent_big(&nc, c, &sf) {
                    let mut r = rc.lock().unwrap();
                    if r.is_none() { *r = Some(d); }
                    sf.store(true, Ordering::Relaxed);
                    return;
                }
            }
        }));
    }

    // Wait: for smaller n, give more time to Pollard; for larger, go to QS quickly
    let rho_budget = if nd <= 40 { Duration::from_secs(30) }
                    else if nd <= 60 { Duration::from_secs(5) }
                    else { Duration::from_secs(2) };
    let rho_dl = Instant::now() + rho_budget;

    loop {
        if rho_stop.load(Ordering::Relaxed) { break; }
        if Instant::now() >= rho_dl.min(deadline) { break; }
        if stop.load(Ordering::Relaxed) { break; }
        std::thread::sleep(Duration::from_millis(5));
    }
    rho_stop.store(true, Ordering::Relaxed);
    for h in handles { let _ = h.join(); }

    let rr = rho_result.lock().unwrap().clone();
    if rr.is_some() { return rr; }

    // QS
    if Instant::now() < deadline && !stop.load(Ordering::Relaxed) {
        return quadratic_sieve(n, deadline);
    }

    None
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut tl = 60.0f64;
    for i in 0..args.len() {
        if args[i] == "--time-limit" && i+1 < args.len() {
            tl = args[i+1].parse().unwrap_or(60.0);
        }
    }
    let time_limit = Duration::from_secs_f64(tl);
    let global_start = Instant::now();
    let mut out = BufWriter::new(io::stdout().lock());
    let stop = Arc::new(AtomicBool::new(false));

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
        let per_q = remaining.min(Duration::from_secs_f64(tl * 0.99));
        let deadline = Instant::now() + per_q;

        let factor = factor_number(&n, deadline, &stop);
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
