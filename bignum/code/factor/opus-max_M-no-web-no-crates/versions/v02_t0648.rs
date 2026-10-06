// Balanced semiprime factoring: trial division / Pollard-Brent rho for small n,
// multi-threaded SIQS (self-initialising quadratic sieve, single large prime) otherwise.
use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};
use std::collections::{HashMap, HashSet};
use std::io::{self, BufRead, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc, Mutex};
use std::time::{Duration, Instant};

// ---------------------------------------------------------------- JSON helpers
fn scan_value(b: &[u8], mut i: usize) -> usize {
    if i >= b.len() {
        return i;
    }
    if b[i] == b'"' {
        i += 1;
        while i < b.len() && b[i] != b'"' {
            if b[i] == b'\\' {
                i += 1;
            }
            i += 1;
        }
        return (i + 1).min(b.len());
    }
    let mut depth = 0i32;
    while i < b.len() {
        let c = b[i];
        if c == b'"' {
            i = scan_value(b, i);
            continue;
        }
        if c == b'{' || c == b'[' {
            depth += 1;
        } else if c == b'}' || c == b']' {
            if depth == 0 {
                return i;
            }
            depth -= 1;
        } else if c == b',' && depth == 0 {
            return i;
        }
        i += 1;
    }
    i
}

fn parse_obj(s: &str) -> Vec<(String, String)> {
    let b = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() && b[i].is_ascii_whitespace() {
        i += 1;
    }
    if i >= b.len() || b[i] != b'{' {
        return out;
    }
    i += 1;
    loop {
        while i < b.len() && (b[i].is_ascii_whitespace() || b[i] == b',') {
            i += 1;
        }
        if i >= b.len() || b[i] == b'}' {
            break;
        }
        let ks = i;
        let ke = scan_value(b, i);
        let key = s[ks..ke].trim().trim_matches('"').to_string();
        i = ke;
        while i < b.len() && b[i].is_ascii_whitespace() {
            i += 1;
        }
        if i < b.len() && b[i] == b':' {
            i += 1;
        }
        while i < b.len() && b[i].is_ascii_whitespace() {
            i += 1;
        }
        let vs = i;
        let ve = scan_value(b, i);
        out.push((key, s[vs..ve].trim().to_string()));
        if ve <= i {
            i += 1;
        } else {
            i = ve;
        }
    }
    out
}

// ---------------------------------------------------------------- small helpers
fn mod_small(l: &[u64], p: u32) -> u32 {
    let p = p as u64;
    let mut r: u64 = 0;
    for &x in l.iter().rev() {
        r = ((r << 32) | (x >> 32)) % p;
        r = ((r << 32) | (x & 0xffff_ffff)) % p;
    }
    r as u32
}

fn div_small(l: &mut Vec<u64>, p: u32) {
    let p = p as u64;
    let mut r: u64 = 0;
    for x in l.iter_mut().rev() {
        let hi = (r << 32) | (*x >> 32);
        let qh = hi / p;
        r = hi % p;
        let lo = (r << 32) | (*x & 0xffff_ffff);
        let ql = lo / p;
        r = lo % p;
        *x = (qh << 32) | ql;
    }
    while l.len() > 1 && *l.last().unwrap() == 0 {
        l.pop();
    }
}

fn powmod(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64 % m;
    b %= m;
    while e > 0 {
        if e & 1 == 1 {
            r = ((r as u128 * b as u128) % m as u128) as u64;
        }
        b = ((b as u128 * b as u128) % m as u128) as u64;
        e >>= 1;
    }
    r
}

fn modinv(a: u64, m: u64) -> u64 {
    let (mut t, mut nt) = (0i64, 1i64);
    let (mut r, mut nr) = (m as i64, (a % m) as i64);
    while nr != 0 {
        let q = r / nr;
        (t, nt) = (nt, t - q * nt);
        (r, nr) = (nr, r - q * nr);
    }
    if t < 0 {
        t += m as i64;
    }
    t as u64
}

fn sqrt_mod(a: u64, p: u64) -> u64 {
    let a = a % p;
    if p == 2 || a == 0 {
        return a;
    }
    if p % 4 == 3 {
        return powmod(a, (p + 1) / 4, p);
    }
    let mut q = p - 1;
    let mut s = 0;
    while q % 2 == 0 {
        q /= 2;
        s += 1;
    }
    let mut z = 2;
    while powmod(z, (p - 1) / 2, p) != p - 1 {
        z += 1;
    }
    let mut m = s;
    let mut c = powmod(z, q, p);
    let mut t = powmod(a, q, p);
    let mut r = powmod(a, (q + 1) / 2, p);
    while t != 1 {
        let mut i = 0;
        let mut tt = t;
        while tt != 1 {
            tt = tt * tt % p;
            i += 1;
        }
        let mut b = c;
        for _ in 0..(m - i - 1) {
            b = b * b % p;
        }
        m = i;
        c = b * b % p;
        t = t * c % p;
        r = r * b % p;
    }
    r
}

fn primes_upto(n: usize) -> Vec<u32> {
    let mut s = vec![true; n + 1];
    let mut out = Vec::new();
    for i in 2..=n {
        if s[i] {
            out.push(i as u32);
            let mut j = i * i;
            while j <= n {
                s[j] = false;
                j += i;
            }
        }
    }
    out
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

// ---------------------------------------------------------------- Pollard-Brent rho (u128 Montgomery)
#[inline]
fn mul_wide(a: u128, b: u128) -> (u128, u128) {
    let a0 = a as u64 as u128;
    let a1 = a >> 64;
    let b0 = b as u64 as u128;
    let b1 = b >> 64;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = (p00 >> 64) + (p01 as u64 as u128) + (p10 as u64 as u128);
    let lo = (p00 as u64 as u128) | (mid << 64);
    let hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
    (lo, hi)
}

#[inline]
fn mont_mul(a: u128, b: u128, n: u128, ninv: u128) -> u128 {
    let (lo, hi) = mul_wide(a, b);
    let m = lo.wrapping_mul(ninv);
    let (mlo, mhi) = mul_wide(m, n);
    let (_, carry) = lo.overflowing_add(mlo);
    let mut u = hi + mhi + carry as u128;
    if u >= n {
        u -= n;
    }
    u
}

fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn rho128(n: u128) -> Option<u128> {
    if n % 2 == 0 {
        return Some(2);
    }
    let mut inv: u128 = n;
    for _ in 0..7 {
        inv = inv.wrapping_mul(2u128.wrapping_sub(n.wrapping_mul(inv)));
    }
    let ninv = inv.wrapping_neg();
    for c in 1..200u128 {
        let f = |y: u128| -> u128 {
            let mut t = mont_mul(y, y, n, ninv) + c;
            if t >= n {
                t -= n;
            }
            t
        };
        let mut y: u128 = 2 + c;
        let mut x = y;
        let mut ys = y;
        let mut q: u128 = 1;
        let mut g: u128 = 1;
        let mut r: u64 = 1;
        let m: u64 = 256;
        while g == 1 {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k = 0;
            while k < r && g == 1 {
                ys = y;
                let lim = m.min(r - k);
                for _ in 0..lim {
                    y = f(y);
                    let d = if x > y { x - y } else { y - x };
                    q = mont_mul(q, d, n, ninv);
                }
                g = gcd128(q, n);
                k += m;
            }
            r *= 2;
            if r > (1u64 << 40) {
                break;
            }
        }
        if g == n || g == 0 {
            g = 1;
            for _ in 0..(1u64 << 22) {
                ys = f(ys);
                let d = if x > ys { x - ys } else { ys - x };
                g = gcd128(d, n);
                if g != 1 {
                    break;
                }
            }
        }
        if g != 1 && g != n {
            return Some(g);
        }
    }
    None
}

// ---------------------------------------------------------------- SIQS
const BS: usize = 32768;

#[derive(Clone)]
struct Rel {
    y: BigUint,
    factors: Vec<u32>,
    lp: u64,
}

struct Shared {
    n_int: BigInt,
    kn_int: BigInt,
    fb: Vec<u32>,
    tmem: Vec<u32>,
    logp: Vec<u8>,
    special: Vec<bool>,
    nfb: usize,
    m: usize,
    size: usize,
    lp_bound: u64,
    sieve_start: usize,
    med_end: usize,
    s: usize,
    pool_lo: usize,
    pool_hi: usize,
    target_ln: f64,
    stop: AtomicBool,
    used: Mutex<HashSet<Vec<usize>>>,
}

fn params(digits: usize) -> (usize, u64, usize) {
    // digits, factor-base size, large prime multiplier, half-interval in blocks
    const T: [(usize, usize, u64, usize); 17] = [
        (20, 60, 30, 1),
        (30, 150, 40, 1),
        (36, 250, 40, 1),
        (40, 350, 50, 1),
        (45, 550, 50, 1),
        (50, 900, 60, 1),
        (55, 1400, 60, 1),
        (60, 2200, 70, 2),
        (65, 3300, 80, 2),
        (70, 5000, 90, 3),
        (75, 7500, 100, 3),
        (80, 11000, 110, 4),
        (85, 16000, 120, 5),
        (90, 24000, 130, 6),
        (95, 32000, 140, 7),
        (100, 42000, 150, 8),
        (120, 90000, 160, 10),
    ];
    if digits <= T[0].0 {
        return (T[0].1, T[0].2, T[0].3);
    }
    for w in T.windows(2) {
        let (d0, f0, l0, b0) = w[0];
        let (d1, f1, _, _) = w[1];
        if digits <= d1 {
            let f = f0 as f64 + (f1 as f64 - f0 as f64) * (digits - d0) as f64 / (d1 - d0) as f64;
            return (f as usize, l0, b0);
        }
    }
    let l = T[T.len() - 1];
    (l.1, l.2, l.3)
}

fn choose_multiplier(n: &BigUint, primes: &[u32]) -> u32 {
    const KS: [u32; 31] = [
        1, 3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 29, 31, 33, 35, 37, 39, 41, 43, 47, 51, 53, 55, 57,
        59, 61, 65, 67, 69, 71, 73,
    ];
    let nl = n.to_u64_digits();
    let mut best = 1;
    let mut best_score = f64::MIN;
    for &k in KS.iter() {
        let kn8 = (mod_small(&nl, 8) as u64 * k as u64) % 8;
        let mut score = -0.5 * (k as f64).ln();
        let ln2 = 2f64.ln();
        score += match kn8 {
            1 => 2.0 * ln2,
            5 => ln2,
            3 | 7 => 0.5 * ln2,
            _ => 0.0,
        };
        for &p in primes.iter().skip(1).take(300) {
            let pl = (p as f64).ln();
            if k % p == 0 {
                score += pl / p as f64;
            } else {
                let r = (mod_small(&nl, p) as u64 * k as u64) % p as u64;
                if r == 0 {
                    continue;
                }
                if powmod(r, (p as u64 - 1) / 2, p as u64) == 1 {
                    score += 2.0 * pl / (p as f64 - 1.0);
                }
            }
        }
        if score > best_score {
            best_score = score;
            best = k;
        }
    }
    best
}

fn choose_a(sh: &Shared, rng: &mut Rng) -> Vec<usize> {
    let s = sh.s;
    let mut last: Vec<usize> = Vec::new();
    for _attempt in 0..2000 {
        let mut idx: Vec<usize> = Vec::with_capacity(s);
        let mut lna = 0.0;
        let span = sh.pool_hi - sh.pool_lo;
        let mut guard = 0;
        while idx.len() < s - 1 && guard < 10000 {
            guard += 1;
            let k = sh.pool_lo + (rng.next() % span as u64) as usize;
            if sh.special[k] || idx.contains(&k) {
                continue;
            }
            idx.push(k);
            lna += (sh.fb[k] as f64).ln();
        }
        let need = (sh.target_ln - lna).exp();
        if need < sh.fb[sh.sieve_start.max(2)] as f64 || need > sh.fb[sh.nfb - 1] as f64 {
            if s == 1 || _attempt < 1500 {
                continue;
            }
        }
        // closest FB prime to need
        let pos = sh.fb[2..].partition_point(|&p| (p as f64) < need) + 2;
        let mut bestk = usize::MAX;
        let mut bestd = f64::MAX;
        for k in pos.saturating_sub(3).max(sh.sieve_start.max(2))..(pos + 3).min(sh.nfb) {
            if sh.special[k] || idx.contains(&k) {
                continue;
            }
            let d = ((sh.fb[k] as f64).ln() - need.ln()).abs();
            if d < bestd {
                bestd = d;
                bestk = k;
            }
        }
        if bestk == usize::MAX {
            continue;
        }
        idx.push(bestk);
        idx.sort();
        last = idx.clone();
        if sh.used.lock().unwrap().insert(idx.clone()) {
            return idx;
        }
    }
    last
}

#[inline(never)]
fn sieve_poly(sh: &Shared, sieve: &mut [u8], r1: &[u32], r2: &[u32], next1: &mut [u32], next2: &mut [u32]) {
    let size = sh.size;
    sieve.fill(0);
    let fb = &sh.fb;
    let lg = &sh.logp;
    for k in sh.med_end..sh.nfb {
        let a = r1[k];
        if a == u32::MAX {
            continue;
        }
        let p = fb[k] as usize;
        let l = lg[k];
        let mut j = a as usize;
        while j < size {
            unsafe {
                let e = sieve.get_unchecked_mut(j);
                *e = e.wrapping_add(l);
            }
            j += p;
        }
        let mut j = r2[k] as usize;
        while j < size {
            unsafe {
                let e = sieve.get_unchecked_mut(j);
                *e = e.wrapping_add(l);
            }
            j += p;
        }
    }
    let bs = BS.min(size);
    for k in sh.sieve_start..sh.med_end {
        next1[k] = r1[k];
        next2[k] = r2[k];
    }
    let nb = size / bs;
    for blk in 0..nb {
        let sv = &mut sieve[blk * bs..(blk + 1) * bs];
        for k in sh.sieve_start..sh.med_end {
            let a = next1[k];
            if a == u32::MAX {
                continue;
            }
            let p = fb[k] as usize;
            let l = lg[k];
            let mut j = a as usize;
            while j < bs {
                unsafe {
                    let e = sv.get_unchecked_mut(j);
                    *e = e.wrapping_add(l);
                }
                j += p;
            }
            next1[k] = (j - bs) as u32;
            let mut j = next2[k] as usize;
            while j < bs {
                unsafe {
                    let e = sv.get_unchecked_mut(j);
                    *e = e.wrapping_add(l);
                }
                j += p;
            }
            next2[k] = (j - bs) as u32;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn trial_divide(
    sh: &Shared,
    i: usize,
    r1: &[u32],
    r2: &[u32],
    a: &BigInt,
    b: &BigInt,
    c: &BigInt,
    qidx: &[usize],
    out: &mut Vec<Rel>,
) {
    let x = BigInt::from(i as i64 - sh.m as i64);
    let ax = a * &x;
    let y = &ax + b;
    let g = (&y + b) * &x + c;
    if g.is_zero() {
        return;
    }
    let mut factors: Vec<u32> = Vec::with_capacity(40);
    if g.sign() == Sign::Minus {
        factors.push(0);
    }
    let mut l = g.magnitude().to_u64_digits();
    // powers of two
    loop {
        if l[0] & 1 == 1 {
            break;
        }
        let tz = l[0].trailing_zeros();
        if tz == 64 {
            l.remove(0);
            for _ in 0..64 {
                factors.push(1);
            }
            continue;
        }
        for _ in 0..tz {
            factors.push(1);
        }
        let n = l.len();
        for w in 0..n {
            let hi = if w + 1 < n { l[w + 1] << (64 - tz) } else { 0 };
            l[w] = (l[w] >> tz) | hi;
        }
        while l.len() > 1 && *l.last().unwrap() == 0 {
            l.pop();
        }
        break;
    }
    let iu = i as u32;
    let fb = &sh.fb;
    for k in 2..sh.nfb {
        let p = fb[k];
        let ra = r1[k];
        if ra == u32::MAX {
            while mod_small(&l, p) == 0 {
                div_small(&mut l, p);
                factors.push(k as u32);
            }
            continue;
        }
        let ip = iu % p;
        if ip == ra || ip == r2[k] {
            while mod_small(&l, p) == 0 {
                div_small(&mut l, p);
                factors.push(k as u32);
            }
        }
    }
    if l.len() != 1 {
        return;
    }
    let cof = l[0];
    let lp = if cof == 1 {
        1
    } else if cof < sh.lp_bound {
        cof
    } else {
        return;
    };
    for &q in qidx {
        factors.push(q as u32);
    }
    let yy = y.mod_floor(&sh.n_int);
    out.push(Rel { y: yy.magnitude().clone(), factors, lp });
}

fn worker(sh: Arc<Shared>, tx: mpsc::Sender<Vec<Rel>>, seed: u64) {
    let nfb = sh.nfb;
    let s = sh.s;
    let m = sh.m as u64;
    let fb = &sh.fb;
    let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
    let mut r1 = vec![0u32; nfb];
    let mut r2 = vec![0u32; nfb];
    let mut bainv2 = vec![0u32; s * nfb];
    let mut next1 = vec![0u32; sh.med_end];
    let mut next2 = vec![0u32; sh.med_end];
    let mut sieve = vec![0u8; sh.size];
    let mut is_a = vec![false; nfb];
    let kn = &sh.kn_int;
    while !sh.stop.load(Ordering::Relaxed) {
        let qidx = choose_a(&sh, &mut rng);
        for &q in &qidx {
            is_a[q] = true;
        }
        let mut a = BigUint::one();
        for &q in &qidx {
            a *= fb[q];
        }
        let mut bj: Vec<BigUint> = Vec::with_capacity(s);
        for &qi in &qidx {
            let q = fb[qi] as u64;
            let aq = &a / q;
            let aqm = mod_small(&aq.to_u64_digits(), q as u32) as u64;
            let inv = modinv(aqm, q);
            let mut gamma = (sh.tmem[qi] as u64) * inv % q;
            if gamma > q / 2 {
                gamma = q - gamma;
            }
            bj.push(aq * gamma);
        }
        let mut bsum = BigUint::zero();
        for x in &bj {
            bsum += x;
        }
        let a_l = a.to_u64_digits();
        let b_l = bsum.to_u64_digits();
        let bj_l: Vec<Vec<u64>> = bj.iter().map(|x| x.to_u64_digits()).collect();
        for k in 1..nfb {
            if sh.special[k] || is_a[k] {
                r1[k] = u32::MAX;
                r2[k] = u32::MAX;
                continue;
            }
            let p = fb[k] as u64;
            let am = mod_small(&a_l, p as u32) as u64;
            let ai = modinv(am, p);
            let bm = mod_small(&b_l, p as u32) as u64;
            for j in 0..s {
                bainv2[j * nfb + k] = (2 * mod_small(&bj_l[j], p as u32) as u64 % p * ai % p) as u32;
            }
            let t = sh.tmem[k] as u64;
            let x1 = ai * ((t + p - bm) % p) % p;
            let x2 = ai * ((2 * p - t - bm) % p) % p;
            r1[k] = ((x1 + m) % p) as u32;
            r2[k] = ((x2 + m) % p) as u32;
        }
        let npoly = 1usize << (s - 1);
        let mut signs = vec![true; s];
        let ab = BigInt::from(a.clone());
        let mut b = BigInt::from(bsum);
        let mut out: Vec<Rel> = Vec::new();
        for pi in 0..npoly {
            if pi > 0 {
                let j = pi.trailing_zeros() as usize + 1;
                let row = &bainv2[j * nfb..(j + 1) * nfb];
                let twob = BigInt::from(&bj[j] << 1u32);
                if signs[j] {
                    b -= &twob;
                    signs[j] = false;
                    for k in 1..nfb {
                        let ra = r1[k];
                        if ra == u32::MAX {
                            continue;
                        }
                        let p = fb[k];
                        let d = row[k];
                        let mut x = ra + d;
                        if x >= p {
                            x -= p;
                        }
                        r1[k] = x;
                        let mut x = r2[k] + d;
                        if x >= p {
                            x -= p;
                        }
                        r2[k] = x;
                    }
                } else {
                    b += &twob;
                    signs[j] = true;
                    for k in 1..nfb {
                        let ra = r1[k];
                        if ra == u32::MAX {
                            continue;
                        }
                        let p = fb[k];
                        let d = p - row[k];
                        let mut x = ra + d;
                        if x >= p {
                            x -= p;
                        }
                        r1[k] = x;
                        let mut x = r2[k] + d;
                        if x >= p {
                            x -= p;
                        }
                        r2[k] = x;
                    }
                }
            }
            let c: BigInt = (&b * &b - kn) / &ab;
            sieve_poly(&sh, &mut sieve, &r1, &r2, &mut next1, &mut next2);
            let size = sh.size;
            for w in 0..size / 8 {
                let v = u64::from_le_bytes(sieve[w * 8..w * 8 + 8].try_into().unwrap());
                if v & 0x8080_8080_8080_8080 == 0 {
                    continue;
                }
                for t in 0..8 {
                    let i = w * 8 + t;
                    if sieve[i] & 0x80 != 0 {
                        trial_divide(&sh, i, &r1, &r2, &ab, &b, &c, &qidx, &mut out);
                    }
                }
            }
            if out.len() >= 8 || (pi + 1 == npoly && !out.is_empty()) {
                if tx.send(std::mem::take(&mut out)).is_err() {
                    return;
                }
            }
            if sh.stop.load(Ordering::Relaxed) {
                return;
            }
        }
        for &q in &qidx {
            is_a[q] = false;
        }
    }
}

struct MRel {
    y: BigUint,
    factors: Vec<u32>,
    lpprod: u64,
}

fn linear_algebra(n: &BigUint, fb: &[u32], rels: &[MRel]) -> Option<BigUint> {
    let nfb = fb.len();
    let nr = rels.len();
    let cols: Vec<Vec<u32>> = rels
        .iter()
        .map(|r| {
            let mut f = r.factors.clone();
            f.sort_unstable();
            let mut odd = Vec::new();
            let mut i = 0;
            while i < f.len() {
                let mut j = i;
                while j < f.len() && f[j] == f[i] {
                    j += 1;
                }
                if (j - i) % 2 == 1 {
                    odd.push(f[i]);
                }
                i = j;
            }
            odd
        })
        .collect();
    let mut weight = vec![0u32; nfb];
    for c in &cols {
        for &x in c {
            weight[x as usize] += 1;
        }
    }
    let mut alive = vec![true; nr];
    loop {
        let mut changed = false;
        for r in 0..nr {
            if alive[r] && cols[r].iter().any(|&c| weight[c as usize] == 1) {
                alive[r] = false;
                for &c in &cols[r] {
                    weight[c as usize] -= 1;
                }
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut active: Vec<usize> = (0..nfb).filter(|&c| weight[c] > 0).collect();
    active.sort_by_key(|&c| weight[c]);
    let mut colmap = vec![usize::MAX; nfb];
    for (i, &c) in active.iter().enumerate() {
        colmap[c] = i;
    }
    let rows: Vec<usize> = (0..nr).filter(|&r| alive[r]).collect();
    let nrows = rows.len();
    let ncols = active.len();
    if nrows == 0 {
        return None;
    }
    let w1 = (ncols + 63) / 64;
    let w2 = (nrows + 63) / 64;
    let w = w1 + w2;
    let mut mat = vec![0u64; nrows * w];
    for (ri, &r) in rows.iter().enumerate() {
        for &c in &cols[r] {
            let nc = colmap[c as usize];
            mat[ri * w + nc / 64] |= 1u64 << (nc % 64);
        }
        mat[ri * w + w1 + ri / 64] |= 1u64 << (ri % 64);
    }
    let mut piv = 0;
    for c in 0..ncols {
        let wi = c / 64;
        let bit = 1u64 << (c % 64);
        let mut found = usize::MAX;
        for r in piv..nrows {
            if mat[r * w + wi] & bit != 0 {
                found = r;
                break;
            }
        }
        if found == usize::MAX {
            continue;
        }
        if found != piv {
            for t in 0..w {
                mat.swap(found * w + t, piv * w + t);
            }
        }
        let (top, bottom) = mat.split_at_mut((piv + 1) * w);
        let prow = &top[piv * w..];
        for row in bottom.chunks_exact_mut(w) {
            if row[wi] & bit != 0 {
                for t in wi..w {
                    row[t] ^= prow[t];
                }
            }
        }
        piv += 1;
    }
    let one = BigUint::one();
    for r in piv..nrows {
        let ident = &mat[r * w + w1..r * w + w];
        let mut cnt = vec![0u32; nfb];
        let mut x = BigUint::one();
        let mut yv = BigUint::one();
        let mut any = false;
        for (wi, &word) in ident.iter().enumerate() {
            let mut wv = word;
            while wv != 0 {
                let b = wv.trailing_zeros() as usize;
                wv &= wv - 1;
                let ri = wi * 64 + b;
                let rel = &rels[rows[ri]];
                any = true;
                x = (x * &rel.y) % n;
                for &f in &rel.factors {
                    cnt[f as usize] += 1;
                }
                if rel.lpprod != 1 {
                    yv = (yv * rel.lpprod) % n;
                }
            }
        }
        if !any {
            continue;
        }
        if cnt.iter().any(|&c| c % 2 == 1) {
            continue;
        }
        for k in 1..nfb {
            if cnt[k] > 0 {
                let pw = BigUint::from(fb[k]).modpow(&BigUint::from(cnt[k] / 2), n);
                yv = (yv * pw) % n;
            }
        }
        let diff = if x >= yv { &x - &yv } else { &yv - &x };
        let g = diff.gcd(n);
        if g > one && &g < n {
            return Some(g);
        }
    }
    None
}

fn siqs(n: &BigUint) -> Option<BigUint> {
    let digits = n.to_string().len();
    let (nfb_target, lp_mult, hb) = params(digits);
    let small = primes_upto(5_000_000);
    let k = choose_multiplier(n, &small);
    let kn = n * k;
    let knl = kn.to_u64_digits();
    let nl = n.to_u64_digits();
    let mut fb: Vec<u32> = vec![1, 2];
    let mut tmem: Vec<u32> = vec![0, 1];
    let mut special: Vec<bool> = vec![true, true];
    for &p in small.iter().skip(1) {
        if fb.len() >= nfb_target {
            break;
        }
        if mod_small(&nl, p) == 0 {
            return Some(BigUint::from(p));
        }
        let r = mod_small(&knl, p) as u64;
        if r == 0 {
            fb.push(p);
            tmem.push(0);
            special.push(true);
            continue;
        }
        if powmod(r, (p as u64 - 1) / 2, p as u64) == 1 {
            fb.push(p);
            tmem.push(sqrt_mod(r, p as u64) as u32);
            special.push(false);
        }
    }
    let nfb = fb.len();
    let m = hb * BS;
    let size = 2 * m;
    let pmax = fb[nfb - 1] as u64;
    let lp_bound = pmax * lp_mult;
    let knf = kn.bits() as f64; // log2(kn) approx
    let kn_log2 = {
        let sh = kn.bits().saturating_sub(60);
        let top = (&kn >> sh).to_f64().unwrap();
        top.log2() + sh as f64
    };
    let _ = knf;
    let lg = (m as f64).log2() + 0.5 * kn_log2 - 0.5;
    let thr_bits = lg - (lp_bound as f64).log2() - 1.0;
    let scale = 128.0 / thr_bits;
    let logp: Vec<u8> = fb
        .iter()
        .map(|&p| ((p as f64).log2() * scale).round().min(255.0) as u8)
        .collect();
    let sieve_start = fb.iter().position(|&p| p > 30).unwrap_or(nfb).max(2);
    let med_end = fb.iter().position(|&p| p as usize >= BS.min(size)).unwrap_or(nfb).max(sieve_start);
    // A selection
    let target_ln = (2.0f64).ln() * 0.5 * (kn_log2 + 1.0) - (m as f64).ln();
    let fbmax = fb[nfb - 1] as f64;
    let mut s = ((target_ln / 2000f64.ln()).round() as usize).max(2);
    loop {
        let q = (target_ln / s as f64).exp();
        if q > fbmax * 0.5 && s < 30 {
            s += 1;
            continue;
        }
        break;
    }
    while s > 2 && (target_ln / s as f64).exp() < fb[sieve_start] as f64 * 2.0 {
        s -= 1;
    }
    let q = (target_ln / s as f64).exp();
    let mut pool_lo = fb.partition_point(|&p| (p as f64) < q / 1.5).max(sieve_start);
    let mut pool_hi = fb.partition_point(|&p| (p as f64) <= q * 1.5).min(nfb);
    while pool_hi - pool_lo < s + 8 {
        if pool_lo > sieve_start {
            pool_lo -= 1;
        }
        if pool_hi < nfb {
            pool_hi += 1;
        }
        if pool_lo <= sieve_start && pool_hi >= nfb {
            break;
        }
    }
    if std::env::var("FACTOR_DEBUG").is_ok() {
        eprintln!(
            "digits={} k={} nfb={} pmax={} M={} s={} q~{:.0} pool=[{},{}) thr_bits={:.1} lg={:.1}",
            digits, k, nfb, pmax, m, s, q, pool_lo, pool_hi, thr_bits, lg
        );
    }
    let sh = Arc::new(Shared {
        n_int: BigInt::from(n.clone()),
        kn_int: BigInt::from(kn.clone()),
        fb: fb.clone(),
        tmem,
        logp,
        special,
        nfb,
        m,
        size,
        lp_bound,
        sieve_start,
        med_end,
        s,
        pool_lo,
        pool_hi,
        target_ln,
        stop: AtomicBool::new(false),
        used: Mutex::new(HashSet::new()),
    });
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    let (tx, rx) = mpsc::channel::<Vec<Rel>>();
    for t in 0..nthreads {
        let shc = sh.clone();
        let txc = tx.clone();
        std::thread::spawn(move || worker(shc, txc, t as u64 + 1));
    }
    drop(tx);
    let mut fulls: Vec<Rel> = Vec::new();
    let mut partials: HashMap<u64, Vec<Rel>> = HashMap::new();
    let mut seen: HashSet<BigUint> = HashSet::new();
    let mut ncyc = 0usize;
    let mut target = nfb + 64;
    let t0 = Instant::now();
    while let Ok(batch) = rx.recv() {
        for r in batch {
            if !seen.insert(r.y.clone()) {
                continue;
            }
            if r.lp == 1 {
                fulls.push(r);
            } else {
                let e = partials.entry(r.lp).or_default();
                if !e.is_empty() {
                    ncyc += 1;
                }
                e.push(r);
            }
        }
        if fulls.len() + ncyc >= target {
            let mut mrels: Vec<MRel> = Vec::new();
            for r in &fulls {
                mrels.push(MRel { y: r.y.clone(), factors: r.factors.clone(), lpprod: 1 });
            }
            for (&lp, v) in partials.iter() {
                for i in 1..v.len() {
                    let mut f = v[0].factors.clone();
                    f.extend_from_slice(&v[i].factors);
                    mrels.push(MRel { y: (&v[0].y * &v[i].y) % n, factors: f, lpprod: lp });
                }
            }
            if std::env::var("FACTOR_DEBUG").is_ok() {
                eprintln!(
                    "sieve done {:.2}s: fulls={} cycles={} partials={} rels={}",
                    t0.elapsed().as_secs_f64(),
                    fulls.len(),
                    ncyc,
                    partials.len(),
                    mrels.len()
                );
            }
            let t1 = Instant::now();
            let res = linear_algebra(n, &fb, &mrels);
            if std::env::var("FACTOR_DEBUG").is_ok() {
                eprintln!("LA {:.2}s -> {:?}", t1.elapsed().as_secs_f64(), res.is_some());
            }
            if let Some(f) = res {
                sh.stop.store(true, Ordering::Relaxed);
                return Some(f);
            }
            target = fulls.len() + ncyc + 32;
        }
    }
    None
}

// ---------------------------------------------------------------- driver
fn factor(n: &BigUint) -> Option<(BigUint, BigUint)> {
    if *n < BigUint::from(4u32) {
        return None;
    }
    let nl = n.to_u64_digits();
    for p in primes_upto(10000) {
        if mod_small(&nl, p) == 0 {
            let q = n / p;
            let pb = BigUint::from(p);
            return Some(if pb <= q { (pb, q) } else { (q, pb) });
        }
    }
    let r = n.sqrt();
    if &r * &r == *n {
        return Some((r.clone(), r));
    }
    let order = |f: BigUint| -> (BigUint, BigUint) {
        let q = n / &f;
        if f <= q { (f, q) } else { (q, f) }
    };
    if n.bits() <= 80 {
        if let Some(f) = rho128(n.to_u128().unwrap()) {
            return Some(order(BigUint::from(f)));
        }
    }
    if let Some(f) = siqs(n) {
        return Some(order(f));
    }
    if n.bits() <= 126 {
        if let Some(f) = rho128(n.to_u128().unwrap()) {
            return Some(order(BigUint::from(f)));
        }
    }
    None
}

fn main() {
    let start = Instant::now();
    let args: Vec<String> = std::env::args().collect();
    let mut tl = 60.0f64;
    let mut i = 1;
    while i < args.len() {
        if args[i] == "--time-limit" && i + 1 < args.len() {
            tl = args[i + 1].parse().unwrap_or(60.0);
            i += 2;
        } else if let Some(v) = args[i].strip_prefix("--time-limit=") {
            tl = v.parse().unwrap_or(60.0);
            i += 1;
        } else {
            i += 1;
        }
    }
    let deadline = start + Duration::from_secs_f64((tl - 0.6).max(0.05));
    let (ltx, lrx) = mpsc::channel::<String>();
    std::thread::spawn(move || {
        let stdin = io::stdin();
        for line in stdin.lock().lines() {
            match line {
                Ok(l) => {
                    if ltx.send(l).is_err() {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
    });
    let out = io::stdout();
    let timeout_exit = |ids: Vec<String>| -> ! {
        let mut o = out.lock();
        for id in ids {
            let _ = writeln!(o, "{{\"id\": {}, \"answer\": null, \"timeout\": true}}", id);
        }
        let _ = o.flush();
        std::process::exit(0);
    };
    let get_id = |line: &str| -> (String, String) {
        let obj = parse_obj(line);
        let id = obj.iter().find(|(k, _)| k == "id").map(|(_, v)| v.clone()).unwrap_or_else(|| "null".to_string());
        let nv = obj.iter().find(|(k, _)| k == "n").map(|(_, v)| v.clone()).unwrap_or_default();
        (id, nv.trim_matches('"').trim().to_string())
    };
    loop {
        let now = Instant::now();
        if now >= deadline {
            let mut ids = Vec::new();
            while let Ok(l) = lrx.try_recv() {
                if !l.trim().is_empty() {
                    ids.push(get_id(&l).0);
                }
            }
            timeout_exit(ids);
        }
        let line = match lrx.recv_timeout(deadline - now) {
            Ok(l) => l,
            Err(mpsc::RecvTimeoutError::Timeout) => continue,
            Err(mpsc::RecvTimeoutError::Disconnected) => break,
        };
        if line.trim().is_empty() {
            continue;
        }
        let (id, nstr) = get_id(&line);
        let (rtx, rrx) = mpsc::channel();
        std::thread::spawn(move || {
            let r = BigUint::parse_bytes(nstr.as_bytes(), 10).and_then(|n| factor(&n));
            let _ = rtx.send(r);
        });
        let now = Instant::now();
        let res = if now < deadline { rrx.recv_timeout(deadline - now).ok() } else { None };
        match res {
            Some(Some((p, q))) => {
                let mut o = out.lock();
                let _ = writeln!(o, "{{\"id\": {}, \"answer\": \"{} {}\"}}", id, p, q);
                let _ = o.flush();
            }
            Some(None) => {
                let mut o = out.lock();
                let _ = writeln!(o, "{{\"id\": {}, \"answer\": null}}", id);
                let _ = o.flush();
            }
            None => {
                let mut ids = vec![id];
                while let Ok(l) = lrx.try_recv() {
                    if !l.trim().is_empty() {
                        ids.push(get_id(&l).0);
                    }
                }
                timeout_exit(ids);
            }
        }
    }
    let _ = out.lock().flush();
    std::process::exit(0);
}
