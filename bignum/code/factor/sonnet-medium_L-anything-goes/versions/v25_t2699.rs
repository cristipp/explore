use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rayon::prelude::*;
use std::collections::HashMap;
use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{mpsc, Mutex};
use std::time::{Duration, Instant};

// ---------------------------------------------------------------- small arithmetic

fn mulmod32(a: u32, b: u32, p: u32) -> u32 {
    ((a as u64 * b as u64) % p as u64) as u32
}
fn powmod32(mut b: u32, mut e: u32, p: u32) -> u32 {
    let mut r = 1u32;
    b %= p;
    while e > 0 {
        if e & 1 == 1 {
            r = mulmod32(r, b, p);
        }
        b = mulmod32(b, b, p);
        e >>= 1;
    }
    r
}
fn inv_mod(a: u32, p: u32) -> u32 {
    let (mut r0, mut r1) = (p as i64, a as i64);
    let (mut t0, mut t1) = (0i64, 1i64);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    t0.rem_euclid(p as i64) as u32
}
fn sqrt_mod(a: u32, p: u32) -> u32 {
    if a == 0 {
        return 0;
    }
    if p % 4 == 3 {
        return powmod32(a, (p + 1) / 4, p);
    }
    let mut q = p - 1;
    let mut s = 0;
    while q % 2 == 0 {
        q /= 2;
        s += 1;
    }
    let mut z = 2;
    while powmod32(z, (p - 1) / 2, p) != p - 1 {
        z += 1;
    }
    let mut c = powmod32(z, q, p);
    let mut r = powmod32(a, (q + 1) / 2, p);
    let mut t = powmod32(a, q, p);
    let mut m = s;
    while t != 1 {
        let mut i = 0;
        let mut tt = t;
        while tt != 1 {
            tt = mulmod32(tt, tt, p);
            i += 1;
        }
        let mut b = c;
        for _ in 0..(m - i - 1) {
            b = mulmod32(b, b, p);
        }
        r = mulmod32(r, b, p);
        c = mulmod32(b, b, p);
        t = mulmod32(t, c, p);
        m = i;
    }
    r
}
fn gcd64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}
fn primes_upto(n: usize) -> Vec<u32> {
    let mut s = vec![true; n + 1];
    let mut v = vec![];
    for i in 2..=n {
        if s[i] {
            v.push(i as u32);
            let mut j = i * i;
            while j <= n {
                s[j] = false;
                j += i;
            }
        }
    }
    v
}

// ---------------------------------------------------------------- tiny n: Pollard rho (Brent)

fn rho_u64(n: u64) -> u64 {
    if n % 2 == 0 {
        return 2;
    }
    let mm = |a: u64, b: u64| ((a as u128 * b as u128) % n as u128) as u64;
    let mut c = 1u64;
    loop {
        let f = |x: u64| (mm(x, x) + c) % n;
        let (mut x, mut y, mut q) = (2u64, 2u64, 1u64);
        let mut g = 1;
        let mut r = 1usize;
        let mut ys = 2;
        while g == 1 {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k = 0;
            while k < r && g == 1 {
                ys = y;
                for _ in 0..128.min(r - k) {
                    y = f(y);
                    q = mm(q, x.abs_diff(y));
                }
                g = gcd64(q, n);
                k += 128;
            }
            r *= 2;
        }
        if g == n {
            g = 1;
            while g == 1 {
                ys = f(ys);
                g = gcd64(x.abs_diff(ys), n);
            }
        }
        if g != n {
            return g;
        }
        c += 1;
    }
}

// ---------------------------------------------------------------- SIQS

struct Rel {
    x: BigUint,
    e: Vec<(u32, u32)>, // (column, exponent) ; column 0 = sign, column i+1 = fb prime i
    l1: u64,            // large primes (1 = none), l1 <= l2
    l2: u64,
    ym: Vec<u64>,
}

// graph of large primes: node 0 = "1"; edges are relations; each closed cycle gives a usable relation
struct Shared {
    edges: Vec<Rel>,
    ids: HashMap<u64, u32>,
    uf: Vec<u32>,
}

impl Shared {
    fn new() -> Shared {
        let mut ids = HashMap::new();
        ids.insert(1u64, 0u32);
        Shared { edges: vec![], ids, uf: vec![0] }
    }
    fn node(&mut self, l: u64) -> u32 {
        if let Some(&i) = self.ids.get(&l) {
            return i;
        }
        let i = self.uf.len() as u32;
        self.uf.push(i);
        self.ids.insert(l, i);
        i
    }
    fn find(&mut self, mut a: u32) -> u32 {
        while self.uf[a as usize] != a {
            let p = self.uf[a as usize];
            self.uf[a as usize] = self.uf[p as usize];
            a = self.uf[a as usize];
        }
        a
    }
    // returns true if the edge closes a cycle
    fn add(&mut self, r: Rel) -> bool {
        let (u, v) = (self.node(r.l1), self.node(r.l2));
        let (fu, fv) = (self.find(u), self.find(v));
        self.edges.push(r);
        if fu == fv {
            true
        } else {
            self.uf[fu as usize] = fv;
            false
        }
    }
}

fn mont_inv(n: u64) -> u64 {
    let mut x = n;
    for _ in 0..6 {
        x = x.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(x)));
    }
    x
}
struct Mont {
    n: u64,
    ni: u64, // -n^-1
    r2: u64,
}
impl Mont {
    fn new(n: u64) -> Mont {
        let r = ((1u128 << 64) % n as u128) as u64;
        let r2 = ((r as u128 * r as u128) % n as u128) as u64;
        Mont { n, ni: mont_inv(n).wrapping_neg(), r2 }
    }
    #[inline]
    fn red(&self, t: u128) -> u64 {
        let m = (t as u64).wrapping_mul(self.ni);
        let u = ((t + m as u128 * self.n as u128) >> 64) as u64;
        if u >= self.n { u - self.n } else { u }
    }
    #[inline]
    fn mul(&self, a: u64, b: u64) -> u64 {
        self.red(a as u128 * b as u128)
    }
    fn to(&self, a: u64) -> u64 {
        self.mul(a % self.n, self.r2)
    }
}

fn is_prime64(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 {
            return n == p;
        }
    }
    let mt = Mont::new(n);
    let one = mt.to(1);
    let mone = n - one;
    let mut d = n - 1;
    let mut s = 0;
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    'a: for &a in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = {
            let (mut r, mut b, mut e) = (one, mt.to(a), d);
            while e > 0 {
                if e & 1 == 1 {
                    r = mt.mul(r, b);
                }
                b = mt.mul(b, b);
                e >>= 1;
            }
            r
        };
        if x == one || x == mone {
            continue;
        }
        for _ in 0..s - 1 {
            x = mt.mul(x, x);
            if x == mone {
                continue 'a;
            }
        }
        return false;
    }
    true
}

// nontrivial factor of odd composite n < 2^63 (Brent rho, Montgomery)
fn split64(n: u64) -> Option<u64> {
    let mt = Mont::new(n);
    for c0 in 1..6u64 {
        let c = mt.to(c0);
        let f = |x: u64| {
            let v = mt.mul(x, x) + c;
            if v >= n { v - n } else { v }
        };
        let (mut x, mut y, mut q) = (mt.to(2), mt.to(2), mt.to(1));
        let mut ys = y;
        let mut g = 1u64;
        let mut r = 1usize;
        let mut iters = 0usize;
        while g == 1 && iters < 1 << 17 {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k = 0;
            while k < r && g == 1 {
                ys = y;
                for _ in 0..64.min(r - k) {
                    y = f(y);
                    q = mt.mul(q, x.abs_diff(y));
                }
                g = gcd64(q, n);
                k += 64;
            }
            iters += r;
            r *= 2;
        }
        if g == n {
            g = 1;
            let mut cnt = 0;
            while g == 1 && cnt < 100000 {
                ys = f(ys);
                g = gcd64(x.abs_diff(ys), n);
                cnt += 1;
            }
        }
        if g != 1 && g != n {
            return Some(g);
        }
    }
    None
}

struct Fb {
    p: Vec<u32>,
    t: Vec<u32>,
    lg: Vec<u8>,
    pinv: Vec<u32>,
    pinv64: Vec<u64>,
    lim: Vec<u32>,
    mmod: Vec<u32>,
}

struct Params {
    nfb: usize,
    mlog: u32,
    minidx: usize,
    thr: i32,
    lpb: u64,
}

fn env_f(name: &str, d: f64) -> f64 {
    std::env::var(name).ok().and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn choose_multiplier(n: &BigUint) -> u32 {
    let ks: [u32; 22] = [
        1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31, 33, 34,
    ];
    let ps = primes_upto(400);
    let mut best = (f64::MIN, 1);
    for &k in &ks {
        let kn = n * k;
        let mut sc = -0.5 * (k as f64).ln();
        let m8 = (&kn % 8u32).to_u32().unwrap();
        let l2 = 2f64.ln();
        sc += match m8 {
            1 => 2.0 * l2,
            5 => l2,
            3 | 7 => 0.5 * l2,
            _ => 0.0,
        };
        for &p in ps.iter().skip(1) {
            let r = (&kn % p).to_u32().unwrap();
            let lp = (p as f64).ln();
            if r == 0 {
                sc += lp / p as f64;
            } else if powmod32(r, (p - 1) / 2, p) == 1 {
                sc += 2.0 * lp / (p as f64 - 1.0);
            }
        }
        if sc > best.0 {
            best = (sc, k);
        }
    }
    best.1
}

fn interp_params(d: f64) -> (usize, u32) {
    // (digits, fb size, mlog)
    let tab: [(f64, f64, u32); 11] = [
        (20.0, 80.0, 11),
        (30.0, 200.0, 12),
        (40.0, 450.0, 13),
        (50.0, 1000.0, 14),
        (60.0, 2300.0, 15),
        (70.0, 5000.0, 16),
        (80.0, 10000.0, 17),
        (90.0, 18000.0, 17),
        (100.0, 35000.0, 18),
        (110.0, 65000.0, 18),
        (130.0, 200000.0, 19),
    ];
    let mut i = 0;
    while i + 2 < tab.len() && d > tab[i + 1].0 {
        i += 1;
    }
    let (d0, f0, m0) = tab[i];
    let (d1, f1, _) = tab[i + 1];
    let t = ((d - d0) / (d1 - d0)).clamp(0.0, 1.5);
    let f = (f0.ln() + t * (f1.ln() - f0.ln())).exp();
    (f as usize, m0)
}

struct Ctx {
    n: BigUint,  // multiplied number kn
    ni: BigInt,
    fb: Fb,
    par: Params,
    a_target: BigUint,
    nthreads: usize,
}

struct Xs(u64);
impl Xs {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

type U256 = [u64; 4];
fn from_bigint(x: &BigInt) -> U256 {
    let d = x.magnitude().to_u64_digits();
    let mut r = [0u64; 4];
    for (i, v) in d.iter().enumerate().take(4) {
        r[i] = *v;
    }
    if x.sign() == Sign::Minus {
        neg256(&r)
    } else {
        r
    }
}
fn from_i64(x: i64) -> U256 {
    let e = (x >> 63) as u64;
    [x as u64, e, e, e]
}
fn add256(a: &U256, b: &U256) -> U256 {
    let mut r = [0u64; 4];
    let mut c = false;
    for i in 0..4 {
        let (s1, c1) = a[i].overflowing_add(b[i]);
        let (s2, c2) = s1.overflowing_add(c as u64);
        r[i] = s2;
        c = c1 | c2;
    }
    r
}
fn neg256(a: &U256) -> U256 {
    let n = [!a[0], !a[1], !a[2], !a[3]];
    add256(&n, &[1, 0, 0, 0])
}
fn mul256(a: &U256, b: &U256) -> U256 {
    let mut r = [0u64; 4];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..(4 - i) {
            let t = a[i] as u128 * b[j] as u128 + r[i + j] as u128 + carry;
            r[i + j] = t as u64;
            carry = t >> 64;
        }
    }
    r
}

struct PolyData {
    a256: U256,
    b2: U256,
    c: U256,
}

// exact division by odd p (pinv = p^-1 mod 2^64); returns false (unchanged) if not divisible
#[inline]
fn div_exact_odd(q: &mut [u64; 4], p: u64, pinv: u64) -> bool {
    let mut out = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (t, b1) = q[i].overflowing_sub(borrow);
        let qi = t.wrapping_mul(pinv);
        out[i] = qi;
        borrow = ((qi as u128 * p as u128) >> 64) as u64 + b1 as u64;
    }
    if borrow == 0 {
        *q = out;
        true
    } else {
        false
    }
}

fn div_exact(q: &mut [u64; 4], p: u64) -> bool {
    let mut out = [0u64; 4];
    let mut rem = 0u128;
    for i in (0..4).rev() {
        let cur = (rem << 64) | q[i] as u128;
        out[i] = (cur / p as u128) as u64;
        rem = cur % p as u128;
    }
    if rem == 0 {
        *q = out;
        true
    } else {
        false
    }
}
fn shr1(q: &mut [u64; 4]) {
    for i in 0..4 {
        q[i] = (q[i] >> 1) | if i < 3 { q[i + 1] << 63 } else { 0 };
    }
}

static T_UPD: AtomicUsize = AtomicUsize::new(0);
static T_SIEVE: AtomicUsize = AtomicUsize::new(0);
static T_SCAN: AtomicUsize = AtomicUsize::new(0);
static T_INIT: AtomicUsize = AtomicUsize::new(0);
static T_SPLIT: AtomicUsize = AtomicUsize::new(0);
static N_SPLIT: AtomicUsize = AtomicUsize::new(0);
static T_TRIAL: AtomicUsize = AtomicUsize::new(0);
static N_REL: AtomicUsize = AtomicUsize::new(0);
static T_BUCK: AtomicUsize = AtomicUsize::new(0);
static CANDS: AtomicUsize = AtomicUsize::new(0);
static POLYS: AtomicUsize = AtomicUsize::new(0);
static NSA: AtomicUsize = AtomicUsize::new(0);

fn worker(ctx: &Ctx, seed: u64, stop: &AtomicBool, shared: &Mutex<Shared>, usable: &AtomicUsize) {
    let fb = &ctx.fb;
    let par = &ctx.par;
    let nfb = par.nfb;
    let m: usize = 1 << par.mlog;
    let two_m = 2 * m;
    let bs = two_m.min(1usize << (env_f("BSLOG", 15.0) as u32));
    let nblocks = two_m / bs;
    let bslog = bs.trailing_zeros();
    let bigidx = fb.p.partition_point(|&p| (p as usize) < bs).max(par.minidx);
    let bcap: usize = (bigidx..nfb).map(|i| 2 * (bs / fb.p[i] as usize + 1)).sum::<usize>() + 16;
    let mut bflat: Vec<u32> = vec![0; nblocks * bcap];
    let mut bcnt: Vec<usize> = vec![0; nblocks];
    let hmax: Vec<u8> = (0..nfb).map(|i| ((two_m + fb.p[i] as usize - 1) / fb.p[i] as usize).min(255) as u8).collect();
    let mut rng = Xs(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
    for _ in 0..8 {
        rng.next();
    }
    let ta = ctx.a_target.bits() as f64;
    let lfbmax = (fb.p[nfb - 1] as f64).log2();
    let s = ((ta / (0.62 * lfbmax)).ceil() as usize).max(2).min(14);
    let qc = 2f64.powf(ta / s as f64);
    let center = fb.p.partition_point(|&p| (p as f64) < qc);
    let lo = (center as f64 * 0.6) as usize;
    let lo = lo.max(2);
    let mut hi = ((center as f64 * 1.6) as usize).min(nfb - 1);
    let mut lo = lo;
    while hi < lo + s + 4 {
        if lo > 2 {
            lo -= 1;
        }
        if hi < nfb - 1 {
            hi += 1;
        }
        if lo <= 2 && hi >= nfb - 1 {
            break;
        }
    }
    let atf = ctx.a_target.to_f64().unwrap_or(f64::MAX);
    let mut buf = vec![0u8; bs];
    let v0 = (128 - par.thr) as u8;
    let mut isa = vec![false; nfb];
    let mut ainv = vec![0u32; nfb];
    let mut bainv: Vec<Vec<u32>> = vec![vec![0u32; nfb]; s];
    let mut rx1 = vec![0u32; nfb];
    let mut rx2 = vec![0u32; nfb];
    let nfbp = fb.p.len();
    let mut pr1 = vec![0u32; nfbp];
    let mut pr2 = vec![0u32; nfbp];
    let mut st1 = vec![0u32; nfb];
    let mut st2 = vec![0u32; nfb];
    let mlogm = m as u64;

    'outer: while !stop.load(Ordering::Relaxed) {
        let tinit = Instant::now();
        // ---- choose a
        let mut qi: Vec<usize> = Vec::with_capacity(s);
        let mut prod = 1f64;
        let mut tries = 0;
        loop {
            tries += 1;
            if tries > 1000 {
                return;
            }
            qi.clear();
            prod = 1.0;
            while qi.len() < s - 1 {
                let i = lo + (rng.next() % (hi - lo + 1) as u64) as usize;
                if fb.t[i] == 0 || qi.contains(&i) {
                    continue;
                }
                qi.push(i);
                prod *= fb.p[i] as f64;
            }
            let ideal = atf / prod;
            if ideal < 3.0 || ideal > fb.p[nfb - 1] as f64 {
                continue;
            }
            let mut i = fb.p.partition_point(|&p| (p as f64) < ideal);
            if i >= nfb {
                i = nfb - 1;
            }
            // nearest valid
            let mut best = None;
            for d in 0..40usize {
                for &c in &[i.wrapping_sub(d), i + d] {
                    if c >= 1 && c < nfb && fb.t[c] != 0 && !qi.contains(&c) {
                        let r = fb.p[c] as f64 / ideal;
                        if (0.7..1.4).contains(&r) {
                            best = Some(c);
                        }
                        break;
                    }
                }
                if best.is_some() {
                    break;
                }
            }
            if let Some(c) = best {
                qi.push(c);
                break;
            }
        }
        qi.sort();
        let mut a = BigUint::one();
        for &i in &qi {
            a *= fb.p[i];
        }
        let ai = BigInt::from(a.clone());
        for v in isa.iter_mut() {
            *v = false;
        }
        for &i in &qi {
            isa[i] = true;
        }
        // B_l
        let mut bl: Vec<BigInt> = Vec::with_capacity(s);
        let mut gm: Vec<u64> = Vec::with_capacity(s);
        for &i in &qi {
            let q = fb.p[i];
            let al = &a / q;
            let am = (&al % q).to_u32().unwrap();
            let g = mulmod32(fb.t[i], inv_mod(am, q), q);
            let g = g.min(q - g);
            gm.push(g as u64);
            bl.push(BigInt::from(al * g));
        }
        let mut b = BigInt::zero();
        for x in &bl {
            b += x;
        }
        let mut qm = vec![0u64; s];
        let mut pre = vec![1u64; s + 1];
        let mut suf = vec![1u64; s + 1];
        for idx in 1..nfb {
            if isa[idx] {
                ainv[idx] = 0;
                for l in 0..s {
                    bainv[l][idx] = 0;
                }
                continue;
            }
            let p = fb.p[idx];
            let pp = p as u64;
            for l in 0..s {
                qm[l] = fb.p[qi[l]] as u64 % pp;
            }
            for l in 0..s {
                pre[l + 1] = pre[l] * qm[l] % pp;
            }
            for l in (0..s).rev() {
                suf[l] = suf[l + 1] * qm[l] % pp;
            }
            let ai_p = inv_mod(pre[s] as u32, p) as u64;
            ainv[idx] = ai_p as u32;
            let mut bmod = 0u64;
            for l in 0..s {
                let al = pre[l] * suf[l + 1] % pp;
                let bm = al * gm[l] % pp;
                bmod += bm;
                bainv[l][idx] = (2 * bm % pp * ai_p % pp) as u32;
            }
            let bmod = bmod % pp;
            let t = fb.t[idx] as u64;
            rx1[idx] = ((t + pp - bmod) % pp * ai_p % pp) as u32;
            rx2[idx] = ((2 * pp - t - bmod) % pp * ai_p % pp) as u32;
        }
        T_INIT.fetch_add(tinit.elapsed().as_nanos() as usize, Ordering::Relaxed);
        let npoly = 1usize << (s - 1);
        let mut signs = vec![false; s]; // true = flipped (-)
        for pi in 0..npoly {
            if stop.load(Ordering::Relaxed) {
                break 'outer;
            }
            let tu = Instant::now();
            if pi > 0 {
                let j = pi.trailing_zeros() as usize;
                if !signs[j] {
                    signs[j] = true;
                    b -= &bl[j] * 2;
                    let ba = &bainv[j];
                    for idx in 1..nfb {
                        let p = fb.p[idx];
                        let mut r = rx1[idx] + ba[idx];
                        if r >= p {
                            r -= p;
                        }
                        rx1[idx] = r;
                        let mut r = rx2[idx] + ba[idx];
                        if r >= p {
                            r -= p;
                        }
                        rx2[idx] = r;
                    }
                } else {
                    signs[j] = false;
                    b += &bl[j] * 2;
                    let ba = &bainv[j];
                    for idx in 1..nfb {
                        let p = fb.p[idx];
                        rx1[idx] = if rx1[idx] >= ba[idx] { rx1[idx] - ba[idx] } else { rx1[idx] + p - ba[idx] };
                        rx2[idx] = if rx2[idx] >= ba[idx] { rx2[idx] - ba[idx] } else { rx2[idx] + p - ba[idx] };
                    }
                }
            }
            if pi < 4 && std::env::var("CHECK").is_ok() {
                let mut badr = 0;
                for idx in 1..nfb {
                    if isa[idx] { continue; }
                    let p = fb.p[idx];
                    let bm = (((&b % p as i64).to_i64().unwrap() + p as i64) % p as i64) as u64;
                    let am = (&a % p).to_u64().unwrap();
                    for r in [rx1[idx], rx2[idx]] {
                        let v = (am * r as u64 + bm) % p as u64;
                        let kn = (&ctx.n % p).to_u64().unwrap();
                        if v * v % p as u64 != kn { badr += 1; }
                    }
                }
                eprintln!("poly {} badroots {}", pi, badr);
            }
            // sieve start positions
            for idx in 1..nfb {
                let p = fb.p[idx];
                let mm = fb.mmod[idx];
                let mut s1 = rx1[idx] + mm;
                if s1 >= p {
                    s1 -= p;
                }
                let mut s2 = rx2[idx] + mm;
                if s2 >= p {
                    s2 -= p;
                }
                pr1[idx] = s1;
                pr2[idx] = s2;
                st1[idx] = s1;
                st2[idx] = if fb.t[idx] == 0 { two_m as u32 } else { s2 };
            }
            for &i in &qi {
                st1[i] = two_m as u32;
                st2[i] = two_m as u32;
            }
            POLYS.fetch_add(1, Ordering::Relaxed);
            T_UPD.fetch_add(tu.elapsed().as_nanos() as usize, Ordering::Relaxed);
            let pd = {
                let b2 = &b * 2;
                let c = (&b * &b - &ctx.ni) / &ai;
                PolyData { a256: from_bigint(&ai), b2: from_bigint(&b2), c: from_bigint(&c) }
            };
            let mut found: Vec<Rel> = Vec::new();
            let tb = Instant::now();
            for c in bcnt.iter_mut() {
                *c = 0;
            }
            for idx in bigidx..nfb {
                let p = fb.p[idx];
                let lg = (fb.lg[idx] as u32) << 16;
                let hm = hmax[idx] as u32;
                for st in [st1[idx], st2[idx]] {
                    for h in 0..hm {
                        let pos = st + h * p;
                        let valid = (pos < two_m as u32) as usize;
                        unsafe {
                            let blk = ((pos >> bslog) as usize).min(nblocks - 1);
                            let c = bcnt.get_unchecked_mut(blk);
                            *bflat.get_unchecked_mut(blk * bcap + *c) = (pos & (bs as u32 - 1)) | lg;
                            *c += valid;
                        }
                    }
                }
            }
            T_BUCK.fetch_add(tb.elapsed().as_nanos() as usize, Ordering::Relaxed);
            for blk in 0..nblocks {
                let blo = (blk * bs) as u32;
                let bhi = blo + bs as u32;
                let ts = Instant::now();
                buf.iter_mut().for_each(|v| *v = v0);
                for idx in par.minidx..bigidx {
                    let p = fb.p[idx];
                    let lg = fb.lg[idx];
                    let mut s1 = st1[idx];
                    while s1 < bhi {
                        unsafe {
                            let r = buf.get_unchecked_mut((s1 - blo) as usize);
                            *r = r.wrapping_add(lg);
                        }
                        s1 += p;
                    }
                    st1[idx] = s1;
                    let mut s2 = st2[idx];
                    while s2 < bhi {
                        unsafe {
                            let r = buf.get_unchecked_mut((s2 - blo) as usize);
                            *r = r.wrapping_add(lg);
                        }
                        s2 += p;
                    }
                    st2[idx] = s2;
                }
                for &e in bflat[blk * bcap..blk * bcap + bcnt[blk]].iter() {
                    unsafe {
                        let r = buf.get_unchecked_mut((e & 0xFFFF) as usize);
                        *r = r.wrapping_add((e >> 16) as u8);
                    }
                }
                T_SIEVE.fetch_add(ts.elapsed().as_nanos() as usize, Ordering::Relaxed);
                let ts = Instant::now();
                // scan
                for (ci, chunk) in buf.chunks_exact(64).enumerate() {
                    let mut acc = 0u64;
                    for k in 0..8 {
                        acc |= u64::from_le_bytes(chunk[k * 8..k * 8 + 8].try_into().unwrap());
                    }
                    if acc & 0x8080808080808080 != 0 {
                        for k in 0..64 {
                            if chunk[k] & 0x80 != 0 {
                                let i = blk * bs + ci * 64 + k;
                                if let Some(r) = try_relation(ctx, i, mlogm, &ai, &b, &pd, &qi, &isa, &pr1, &pr2) {
                                    found.push(r);
                                }
                            }
                        }
                    }
                }
                T_SCAN.fetch_add(ts.elapsed().as_nanos() as usize, Ordering::Relaxed);
            }
            if !found.is_empty() {
                let mut sh = shared.lock().unwrap();
                let mut add = 0;
                for r in found {
                    if sh.add(r) {
                        add += 1;
                    }
                }
                usable.fetch_add(add, Ordering::Relaxed);
            }
        }
    }
}

fn try_relation(
    ctx: &Ctx,
    i: usize,
    m: u64,
    a: &BigInt,
    b: &BigInt,
    pd: &PolyData,
    qi: &[usize],
    isa: &[bool],
    pr1: &[u32],
    pr2: &[u32],
) -> Option<Rel> {
    let fb = &ctx.fb;
    let x = i as i64 - m as i64;
    let xs = from_i64(x);
    let mut t = mul256(&pd.a256, &xs);
    t = add256(&t, &pd.b2);
    t = mul256(&t, &xs);
    t = add256(&t, &pd.c);
    let neg = t[3] >> 63 == 1;
    let mut mag = if neg { neg256(&t) } else { t };
    if mag == [0; 4] || mag[3] >> 56 != 0 || mag[0] == 0 {
        return None;
    }
    let mut e: Vec<(u32, u32)> = Vec::with_capacity(48);
    if neg {
        e.push((0, 1));
    }
    let tz = mag[0].trailing_zeros();
    if tz > 0 {
        for k in 0..4 {
            mag[k] = (mag[k] >> tz) | if k < 3 { mag[k + 1] << (64 - tz) } else { 0 };
        }
        e.push((1, tz));
    }
    let ttr = Instant::now();
    let iu = i as u32;
    let nfbp = fb.p.len();
    let mut base = 1;
    // first chunk starts at idx 1 (idx 0 = prime 2 handled above); use aligned chunks from 0 with idx 0 masked
    base -= 1;
    while base < nfbp {
        let mut mask = 0u32;
        let pc = &fb.p[base..base + 16];
        let ic = &fb.pinv[base..base + 16];
        let lc = &fb.lim[base..base + 16];
        let r1 = &pr1[base..base + 16];
        let r2 = &pr2[base..base + 16];
        for k in 0..16 {
            let d1 = iu + pc[k] - r1[k];
            let d2 = iu + pc[k] - r2[k];
            let h = (d1.wrapping_mul(ic[k]) <= lc[k]) | (d2.wrapping_mul(ic[k]) <= lc[k]);
            mask |= (h as u32) << k;
        }
        if base == 0 {
            mask &= !1;
        }
        while mask != 0 {
            let k = mask.trailing_zeros() as usize;
            mask &= mask - 1;
            let idx = base + k;
            if idx >= ctx.par.nfb || isa[idx] {
                continue;
            }
            let p = fb.p[idx] as u64;
            let pi = fb.pinv64[idx];
            let mut c = 0;
            while div_exact_odd(&mut mag, p, pi) {
                c += 1;
            }
            if c > 0 {
                e.push((idx as u32 + 1, c));
            }
        }
        base += 16;
    }
    for &l in qi {
        let p = fb.p[l] as u64;
        let pi = fb.pinv64[l];
        let mut c = 1;
        while div_exact_odd(&mut mag, p, pi) {
            c += 1;
        }
        e.push((l as u32 + 1, c));
    }
    T_TRIAL.fetch_add(ttr.elapsed().as_nanos() as usize, Ordering::Relaxed);
    if mag[1] != 0 || mag[2] != 0 || mag[3] != 0 {
        return None;
    }
    let cof = mag[0];
    let (l1, l2);
    if cof == 1 {
        l1 = 1;
        l2 = 1;
    } else if cof <= ctx.par.lpb {
        l1 = 1;
        l2 = cof;
    } else {
        if cof > ctx.par.lpb * ctx.par.lpb || is_prime64(cof) {
            return None;
        }
        let tsp = Instant::now();
        let f = split64(cof);
        T_SPLIT.fetch_add(tsp.elapsed().as_nanos() as usize, Ordering::Relaxed);
        N_SPLIT.fetch_add(1, Ordering::Relaxed);
        let f = f?;
        let g = cof / f;
        let (f, g) = (f.min(g), f.max(g));
        if f == g || g > ctx.par.lpb {
            return None;
        }
        l1 = f;
        l2 = g;
    }
    let axb = a * x + b;
    let xv = axb.magnitude() % &ctx.n;
    N_REL.fetch_add(1, Ordering::Relaxed);
    Some(Rel { x: xv, e, l1, l2, ym: vec![] })
}

fn build_cycles(edges: &[Rel], n: &BigUint) -> Vec<Rel> {
    // node ids
    let mut ids: HashMap<u64, usize> = HashMap::new();
    ids.insert(1, 0);
    let mut primes: Vec<u64> = vec![1];
    let mut ends: Vec<(usize, usize)> = Vec::with_capacity(edges.len());
    for r in edges {
        let mut g = |l: u64| -> usize {
            *ids.entry(l).or_insert_with(|| {
                primes.push(l);
                primes.len() - 1
            })
        };
        let u = g(r.l1);
        let v = g(r.l2);
        ends.push((u, v));
    }
    let nv = primes.len();
    let mut adj: Vec<Vec<(usize, usize)>> = vec![vec![]; nv]; // (neighbor, edge)
    for (i, &(u, v)) in ends.iter().enumerate() {
        adj[u].push((v, i));
        if u != v {
            adj[v].push((u, i));
        }
    }
    let mut par_edge = vec![usize::MAX; nv];
    let mut par_node = vec![usize::MAX; nv];
    let mut depth = vec![0u32; nv];
    let mut seen = vec![false; nv];
    let mut tree = vec![false; edges.len()];
    let mut order: Vec<usize> = (0..nv).collect();
    order.swap(0, 0);
    for &root in &order {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(root);
        while let Some(u) = queue.pop_front() {
            for &(v, ei) in &adj[u] {
                if !seen[v] {
                    seen[v] = true;
                    par_edge[v] = ei;
                    par_node[v] = u;
                    depth[v] = depth[u] + 1;
                    tree[ei] = true;
                    queue.push_back(v);
                }
            }
        }
    }
    let mut out = Vec::new();
    for (ei, &(u, v)) in ends.iter().enumerate() {
        if tree[ei] {
            continue;
        }
        let mut set = vec![ei];
        let mut verts: Vec<usize> = vec![];
        let (mut a, mut b) = (u, v);
        while a != b {
            if depth[a] >= depth[b] {
                set.push(par_edge[a]);
                verts.push(a);
                a = par_node[a];
            } else {
                set.push(par_edge[b]);
                verts.push(b);
                b = par_node[b];
            }
        }
        verts.push(a);
        let mut x = BigUint::one();
        let mut ev: Vec<(u32, u32)> = vec![];
        for &i in &set {
            x = x * &edges[i].x % n;
            ev.extend_from_slice(&edges[i].e);
        }
        ev.sort();
        let mut e: Vec<(u32, u32)> = Vec::with_capacity(ev.len());
        for (c, k) in ev {
            if let Some(l) = e.last_mut() {
                if l.0 == c {
                    l.1 += k;
                    continue;
                }
            }
            e.push((c, k));
        }
        let mut ym: Vec<u64> = verts.iter().map(|&v| primes[v]).filter(|&l| l > 1).collect();
        ym.sort();
        ym.dedup();
        out.push(Rel { x, e, l1: 1, l2: 1, ym });
    }
    out
}

fn find_deps(rows: &[Vec<u32>], ncols: usize) -> Vec<Vec<usize>> {
    let nrows = rows.len();
    let w = (ncols + nrows + 63) / 64;
    let mut data = vec![0u64; nrows * w];
    for (r, cols) in rows.iter().enumerate() {
        let row = &mut data[r * w..(r + 1) * w];
        for &c in cols {
            row[c as usize / 64] ^= 1u64 << (c % 64);
        }
        let h = ncols + r;
        row[h / 64] |= 1u64 << (h % 64);
    }
    let mut cur = 0usize;
    let mut c = 0usize;
    let mut pb = vec![0u8; nrows];
    let mut table: Vec<u64> = Vec::new();
    let mut first = true;
    while c < ncols && cur < nrows {
        let c1 = (c + 8).min(ncols);
        let (cw, cb) = (c / 64, c % 64);
        if first {
            for r in cur..nrows {
                pb[r] = (data[r * w + cw] >> cb) as u8;
            }
            first = false;
        }
        let mut pivs: Vec<usize> = vec![];
        let mut np = 0;
        for j in 0..(c1 - c) {
            let mut found = None;
            for r in cur + np..nrows {
                if pb[r] >> j & 1 == 1 {
                    found = Some(r);
                    break;
                }
            }
            let Some(r) = found else { continue };
            let pr = cur + np;
            if r != pr {
                for k in 0..w {
                    data.swap(r * w + k, pr * w + k);
                }
                pb.swap(r, pr);
            }
            let pv = pb[pr];
            for r2 in pr + 1..nrows {
                if pb[r2] >> j & 1 == 1 {
                    pb[r2] ^= pv;
                }
            }
            pivs.push(c + j);
            np += 1;
        }
        if np > 0 {
            // Gauss-Jordan among pivot rows
            for k in 0..np {
                let pc = pivs[k];
                for m in 0..np {
                    if m != k && data[(cur + m) * w + pc / 64] >> (pc % 64) & 1 == 1 {
                        for x in cw..w {
                            let v = data[(cur + k) * w + x];
                            data[(cur + m) * w + x] ^= v;
                        }
                    }
                }
            }
            let tw = w - cw;
            table.clear();
            table.resize((1usize << np) * tw, 0);
            for v in 1usize..(1 << np) {
                let low = v.trailing_zeros() as usize;
                let prev = v & (v - 1);
                let (head, tail) = table.split_at_mut(v * tw);
                let src = &head[prev * tw..prev * tw + tw];
                let prow = &data[(cur + low) * w + cw..(cur + low + 1) * w];
                for x in 0..tw {
                    tail[x] = src[x] ^ prow[x];
                }
            }
            let (_, rest) = data.split_at_mut((cur + np) * w);
            let nc1 = c1;
            let (ncw, ncb) = (nc1 / 64, nc1 % 64);
            let have_next = nc1 < ncols;
            let pivs_ref = &pivs;
            let table_ref = &table;
            let f = |(row, pbr): (&mut [u64], &mut u8)| {
                let mut v = 0usize;
                for (k, &pc) in pivs_ref.iter().enumerate() {
                    v |= ((row[pc / 64] >> (pc % 64)) as usize & 1) << k;
                }
                if v != 0 {
                    let t = &table_ref[v * tw..(v + 1) * tw];
                    for x in 0..tw {
                        row[cw + x] ^= t[x];
                    }
                }
                if have_next {
                    *pbr = (row[ncw] >> ncb) as u8;
                }
            };
            let pbs = &mut pb[cur + np..];
            if (nrows - cur) * tw > 100_000 {
                rest.par_chunks_mut(w).zip(pbs.par_iter_mut()).for_each(f);
            } else {
                rest.chunks_mut(w).zip(pbs.iter_mut()).for_each(f);
            }
            // pivot rows themselves: refresh next-panel byte (not needed: they are done)
            cur += np;
        } else {
            // no pivots in this panel: next panel bytes come from current rows (unchanged)
            if c1 < ncols {
                let (ncw, ncb) = (c1 / 64, c1 % 64);
                for r in cur..nrows {
                    pb[r] = (data[r * w + ncw] >> ncb) as u8;
                }
            }
        }
        c = c1;
    }
    let mut deps = vec![];
    for r in cur..nrows {
        let row = &data[r * w..(r + 1) * w];
        let mut d = vec![];
        for k in 0..nrows {
            let h = ncols + k;
            if row[h / 64] >> (h % 64) & 1 == 1 {
                d.push(k);
            }
        }
        deps.push(d);
    }
    deps
}

fn siqs(n0: &BigUint, deadline: Instant, verbose: bool) -> Option<BigUint> {
    let t0 = Instant::now();
    let k = choose_multiplier(n0);
    let n = n0 * k;
    let digits = n.to_string().len();
    let (mut nfb, mlog) = interp_params(digits as f64);
    nfb = (nfb as f64 * env_f("FBMUL", 1.0)) as usize;
    let mlog = env_f("MLOG", mlog as f64) as u32;
    // factor base
    let plim = ((nfb as f64 * 20.0) as usize).max(2000);
    let allp = primes_upto(plim);
    let mut p = vec![2u32];
    let mut t = vec![1u32];
    for &q in allp.iter().skip(1) {
        let r = (&n % q).to_u32().unwrap();
        if r == 0 {
            p.push(q);
            t.push(0);
        } else if powmod32(r, (q - 1) / 2, q) == 1 {
            p.push(q);
            t.push(sqrt_mod(r, q));
        }
        if p.len() >= nfb {
            break;
        }
    }
    let nfb = p.len();
    let m = 1u32 << mlog;
    let lg: Vec<u8> = p.iter().map(|&q| (q as f64).log2().round() as u8).collect();
    let pinv: Vec<u32> = p
        .iter()
        .map(|&q| if q % 2 == 1 { inv_mod(q, u32::MAX) .wrapping_mul(0) } else { 0 })
        .collect();
    // proper inverse mod 2^32 by Newton
    let pinv: Vec<u32> = p
        .iter()
        .zip(pinv.iter())
        .map(|(&q, _)| {
            let mut x = q;
            for _ in 0..5 {
                x = x.wrapping_mul(2u32.wrapping_sub(q.wrapping_mul(x)));
            }
            x
        })
        .collect();
    let pinv64: Vec<u64> = p.iter().map(|&q| if q % 2 == 1 { mont_inv(q as u64) } else { 1 }).collect();
    let lim: Vec<u32> = p.iter().map(|&q| u32::MAX / q).collect();
    let mmod: Vec<u32> = p.iter().map(|&q| m % q).collect();
    let fbmax = *p.last().unwrap() as u64;
    let lpm = env_f("LPM", 30.0);
    let lpb = ((fbmax as f64 * lpm) as u64).min(fbmax * fbmax / 2).min(1 << 31);
    let nbits = n.bits() as f64;
    let qbits = nbits / 2.0 - 0.5 + (m as f64).log2();
    let minp = env_f("MINP", 30.0) as u32;
    let minidx = p.iter().position(|&q| q >= minp).unwrap_or(1).max(1);
    let bias: f64 = p[1..minidx].iter().map(|&q| 2.0 * (q as f64).log2() / (q as f64 - 1.0)).sum();
    let slack = env_f("SLACK", 2.0);
    let cb = 2.0 * (lpb as f64).log2() * env_f("DLPF", 1.0);
    let thr = (qbits - cb - bias - slack).max(1.0) as i32;
    let a_target = (&n * 2u32).sqrt() / m;
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(8);
    let (mut p, mut pinv, mut lim) = (p, pinv, lim);
    while p.len() % 16 != 0 {
        p.push(1 << 30);
        pinv.push(1);
        lim.push(0);
    }
    let ctx = Ctx {
        ni: BigInt::from(n.clone()),
        n: n.clone(),
        fb: Fb { p, t, lg, pinv, pinv64, lim, mmod },
        par: Params { nfb, mlog, minidx, thr, lpb },
        a_target,
        nthreads,
    };
    if verbose {
        eprintln!("k={} digits={} nfb={} fbmax={} mlog={} thr={} lpb={} minidx={}", k, digits, nfb, fbmax, mlog, thr, lpb, minidx);
    }
    let shared = Mutex::new(Shared::new());
    let usable = AtomicUsize::new(0);
    let ncols = nfb + 1;
    let mut target = ncols + 64;
    let mut round = 0u64;
    loop {
        let stop = AtomicBool::new(false);
        std::thread::scope(|sc| {
            for ti in 0..ctx.nthreads {
                let (ctx, stop, shared, usable) = (&ctx, &stop, &shared, &usable);
                let seed = (ti as u64 + 1 + 1000 * round).wrapping_mul(0xD1B54A32D192ED03);
                sc.spawn(move || worker(ctx, seed, stop, shared, usable));
            }
            while usable.load(Ordering::Relaxed) < target && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(5));
            }
            stop.store(true, Ordering::Relaxed);
        });
        if Instant::now() >= deadline {
            return None;
        }
        round += 1;
        if verbose {
            eprintln!("polys={} cands={} upd={}ms buck={}ms sieve={}ms scan+try={}ms init={}ms split={}ms n={} trial={}ms rels={}", POLYS.load(Ordering::Relaxed), CANDS.load(Ordering::Relaxed), T_UPD.load(Ordering::Relaxed)/1000000, T_BUCK.load(Ordering::Relaxed)/1000000, T_SIEVE.load(Ordering::Relaxed)/1000000, T_SCAN.load(Ordering::Relaxed)/1000000, T_INIT.load(Ordering::Relaxed)/1000000, T_SPLIT.load(Ordering::Relaxed)/1000000, N_SPLIT.load(Ordering::Relaxed), T_TRIAL.load(Ordering::Relaxed)/1000000, N_REL.load(Ordering::Relaxed));
            eprintln!("sieve done at {:.2}s usable={}", t0.elapsed().as_secs_f64(), usable.load(Ordering::Relaxed));
        }
        // build relation set
        let sh = shared.lock().unwrap();
        let rels = build_cycles(&sh.edges, &ctx.n);
        drop(sh);
        if std::env::var("CHECK").is_ok() {
            let mut bad = 0;
            let mut seen = std::collections::HashSet::new();
            let mut dup = 0;
            for r in &rels {
                if !seen.insert(r.x.clone()) { dup += 1; }
                let mut v = BigUint::one();
                let mut neg = false;
                for &(c, e) in &r.e {
                    if c == 0 { neg = e % 2 == 1; continue; }
                    v = v * BigUint::from(ctx.fb.p[c as usize - 1]).pow(e) % &ctx.n;
                }
                for &l in &r.ym { v = v * l * l % &ctx.n; }
                let x2 = &r.x * &r.x % &ctx.n;
                let ok = if neg { (&x2 + &v) % &ctx.n == BigUint::zero() } else { x2 == v };
                if !ok { bad += 1; if bad < 6 { eprintln!("bad ym={:?} neg={} e={:?}", r.ym, neg, r.e); } }
            }
            eprintln!("CHECK bad={} dup={} of {}", bad, dup, rels.len());
        }
        let rows: Vec<Vec<u32>> = rels
            .iter()
            .map(|r| r.e.iter().filter(|&&(_, e)| e % 2 == 1).map(|&(c, _)| c).collect())
            .collect();
        if verbose {
            eprintln!("rels={} cols={} merge {:.2}s", rels.len(), ncols, t0.elapsed().as_secs_f64());
        }
        let deps = find_deps(&rows, ncols);
        if verbose {
            eprintln!("deps={} la done {:.2}s", deps.len(), t0.elapsed().as_secs_f64());
        }
        for d in &deps {
            let mut x = BigUint::one();
            let mut tot = vec![0u64; ncols];
            let mut y = BigUint::one();
            for &ri in d {
                let r = &rels[ri];
                x = x * &r.x % &ctx.n;
                for &(c, e) in &r.e {
                    tot[c as usize] += e as u64;
                }
                for &l in &r.ym {
                    y = y * l % &ctx.n;
                }
            }
            for c in 1..ncols {
                let e = tot[c] / 2;
                if e > 0 {
                    let pw = BigUint::from(ctx.fb.p[c - 1]).modpow(&BigUint::from(e), &ctx.n);
                    y = y * pw % &ctx.n;
                }
            }
            let diff = if x > y { &x - &y } else { &y - &x };
            let g = diff.gcd(&ctx.n).gcd(n0);
            if !g.is_one() && &g != n0 {
                if verbose {
                    eprintln!("done {:.2}s", t0.elapsed().as_secs_f64());
                }
                return Some(g);
            }
        }
        target = usable.load(Ordering::Relaxed) + 100;
    }
}

fn isqrt_check(n: &BigUint) -> Option<BigUint> {
    let r = n.sqrt();
    if &(&r * &r) == n {
        Some(r)
    } else {
        None
    }
}

fn factor(n: &BigUint, deadline: Instant, verbose: bool) -> Option<(BigUint, BigUint)> {
    if let Some(v) = n.to_u64() {
        if v < 4 {
            return None;
        }
        let f = rho_u64(v);
        let (a, b) = (f.min(v / f), f.max(v / f));
        return Some((a.into(), b.into()));
    }
    if let Some(r) = isqrt_check(n) {
        return Some((r.clone(), r));
    }
    for &q in &primes_upto(1000) {
        if (n % q).is_zero() {
            let o = n / q;
            return Some((BigUint::from(q), o));
        }
    }
    let f = siqs(n, deadline, verbose)?;
    let o = n / &f;
    Some((f.clone().min(o.clone()), f.max(o)))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut tl = 60.0f64;
    let mut verbose = false;
    for i in 0..args.len() {
        if args[i] == "--time-limit" {
            tl = args[i + 1].parse().unwrap();
        }
        if args[i] == "-v" {
            verbose = true;
        }
    }
    let start = Instant::now();
    let global = start + Duration::from_secs_f64((tl - 0.3).max(0.1));
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut timed_out = false;
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        if line.trim().is_empty() {
            continue;
        }
        let v: serde_json::Value = serde_json::from_str(&line).unwrap();
        let id = v["id"].clone();
        let ns = match &v["n"] {
            serde_json::Value::String(s) => s.clone(),
            o => o.to_string(),
        };
        let n: BigUint = ns.parse().unwrap();
        let mut ans: Option<String> = None;
        if !timed_out {
            let (tx, rx) = mpsc::channel();
            std::thread::spawn(move || {
                let r = factor(&n, global, verbose);
                let _ = tx.send(r);
            });
            let rem = global.saturating_duration_since(Instant::now()) + Duration::from_millis(100);
            match rx.recv_timeout(rem) {
                Ok(Some((a, b))) => ans = Some(format!("{} {}", a, b)),
                _ => timed_out = true,
            }
        }
        let mut out = stdout.lock();
        match ans {
            Some(s) => writeln!(out, "{}", serde_json::json!({"id": id, "answer": s})).unwrap(),
            None => writeln!(out, "{}", serde_json::json!({"id": id, "answer": null, "timeout": true})).unwrap(),
        }
        out.flush().unwrap();
    }
}
