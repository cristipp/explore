use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};
use std::collections::{HashMap, HashSet, VecDeque};
use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

const BLK: usize = 32768;
static T_SIEVE: AtomicU64 = AtomicU64::new(0);
static T_CAND: AtomicU64 = AtomicU64::new(0);
static T_SETUP: AtomicU64 = AtomicU64::new(0);
static N_CAND: AtomicU64 = AtomicU64::new(0);

// ---------------------------------------------------------------- small math

fn modpow(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1 % m;
    b %= m;
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % m;
        }
        b = b * b % m;
        e >>= 1;
    }
    r
}

fn inv_mod(a: u64, m: u64) -> u64 {
    let (mut t, mut nt) = (0i64, 1i64);
    let (mut r, mut nr) = (m as i64, a as i64);
    while nr != 0 {
        let q = r / nr;
        let x = t - q * nt;
        t = nt;
        nt = x;
        let y = r - q * nr;
        r = nr;
        nr = y;
    }
    if t < 0 {
        t += m as i64;
    }
    t as u64
}

fn sqrt_mod(a: u64, p: u64) -> u64 {
    if p % 4 == 3 {
        return modpow(a, (p + 1) / 4, p);
    }
    let mut q = p - 1;
    let mut s = 0;
    while q % 2 == 0 {
        q /= 2;
        s += 1;
    }
    let mut z = 2;
    while modpow(z, (p - 1) / 2, p) != p - 1 {
        z += 1;
    }
    let mut c = modpow(z, q, p);
    let mut t = modpow(a, q, p);
    let mut r = modpow(a, (q + 1) / 2, p);
    let mut m = s;
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
        r = r * b % p;
        c = b * b % p;
        t = t * c % p;
        m = i;
    }
    r
}

fn gcd64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn rho_u64(n: u64) -> u64 {
    if n % 2 == 0 {
        return 2;
    }
    let mut c = 1u64;
    loop {
        let f = |x: u64| ((x as u128 * x as u128 + c as u128) % n as u128) as u64;
        let (mut x, mut y) = (2u64, 2u64);
        loop {
            x = f(x);
            y = f(f(y));
            let d = gcd64(if x > y { x - y } else { y - x }, n);
            if d == n {
                break;
            }
            if d > 1 {
                return d;
            }
        }
        c += 1;
    }
}

fn primes_upto(lim: usize) -> Vec<u32> {
    let mut s = vec![true; lim + 1];
    let mut v = Vec::new();
    for i in 2..=lim {
        if s[i] {
            v.push(i as u32);
            let mut j = i * i;
            while j <= lim {
                s[j] = false;
                j += i;
            }
        }
    }
    v
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

// small fixed multiprecision for trial division
#[derive(Clone)]
struct Mp {
    d: [u32; 24],
    len: usize,
}
impl Mp {
    fn from(b: &BigUint) -> Mp {
        let v = b.to_u32_digits();
        let mut d = [0u32; 24];
        d[..v.len()].copy_from_slice(&v);
        Mp { d, len: v.len() }
    }
    #[inline]
    fn rem(&self, p: u32) -> u32 {
        let mut r = 0u64;
        let p = p as u64;
        for i in (0..self.len).rev() {
            r = ((r << 32) | self.d[i] as u64) % p;
        }
        r as u32
    }
    fn div(&mut self, p: u32) {
        let mut r = 0u64;
        let p = p as u64;
        for i in (0..self.len).rev() {
            let cur = (r << 32) | self.d[i] as u64;
            self.d[i] = (cur / p) as u32;
            r = cur % p;
        }
        while self.len > 0 && self.d[self.len - 1] == 0 {
            self.len -= 1;
        }
    }
    fn small(&self) -> Option<u64> {
        match self.len {
            0 => Some(0),
            1 => Some(self.d[0] as u64),
            2 => Some(self.d[0] as u64 | (self.d[1] as u64) << 32),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------- SIQS

#[derive(Clone)]
struct Rel {
    s: BigUint,
    f: Vec<(u32, u32)>, // column, exponent
    lp: u64,            // large prime (partial) or y-factor (combined) ; 0 none
}

struct Shared {
    fulls: Vec<Rel>,
    parts: HashMap<u64, Vec<Rel>>,
    usable: usize,
    seen: HashSet<u64>,
    npoly: u64,
    nfull: u64,
    npart: u64,
}

struct Ctx {
    n: BigUint,
    nint: BigInt,
    fbp: Vec<u32>,
    fblog: Vec<u8>,
    fbt: Vec<u32>,
    fb: usize,
    start: usize,
    m: i64,
    nblk: usize,
    thr: u8,
    lpmax: u64,
    target: BigUint,
    s: usize,
    ideal: f64,
}

fn key_of(s: &BigUint) -> u64 {
    let d = s.to_u64_digits();
    let mut h = 0x9E3779B97F4A7C15u64;
    for x in d.iter().take(3) {
        h = (h ^ x).wrapping_mul(0xff51afd7ed558ccd);
        h ^= h >> 29;
    }
    h
}

fn merge_f(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut r = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        if j >= b.len() || (i < a.len() && a[i].0 < b[j].0) {
            r.push(a[i]);
            i += 1;
        } else if i >= a.len() || b[j].0 < a[i].0 {
            r.push(b[j]);
            j += 1;
        } else {
            r.push((a[i].0, a[i].1 + b[j].1));
            i += 1;
            j += 1;
        }
    }
    r
}

struct Params {
    fb: usize,
    nb: usize,
    lpk: f64,
    fudge: f64,
    skip: f64,
}

fn params(digits: f64) -> Params {
    // (digits, fb, nb)
    let tab: [(f64, f64, usize); 10] = [
        (20.0, 60.0, 1),
        (30.0, 150.0, 1),
        (40.0, 450.0, 1),
        (50.0, 1000.0, 1),
        (60.0, 2500.0, 2),
        (70.0, 6000.0, 3),
        (80.0, 13000.0, 4),
        (90.0, 25000.0, 5),
        (100.0, 50000.0, 6),
        (120.0, 150000.0, 8),
    ];
    let mut fb = 60.0;
    let mut nb = 1;
    if digits >= tab[9].0 {
        fb = tab[9].1;
        nb = tab[9].2;
    } else if digits > tab[0].0 {
        for i in 1..10 {
            if digits <= tab[i].0 {
                let t = (digits - tab[i - 1].0) / (tab[i].0 - tab[i - 1].0);
                fb = (tab[i - 1].1.ln() * (1.0 - t) + tab[i].1.ln() * t).exp();
                nb = if t < 0.5 { tab[i - 1].2 } else { tab[i].2 };
                break;
            }
        }
    }
    let envf = |k: &str, d: f64| -> f64 {
        std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
    };
    Params {
        fb: envf("FB", fb) as usize,
        nb: envf("NB", nb as f64) as usize,
        lpk: envf("LPK", 40.0),
        fudge: envf("FUDGE", 16.0),
        skip: envf("SKIP", 30.0),
    }
}

fn kron_score(n: &BigUint, k: u32, primes: &[u32]) -> f64 {
    let kn = n * k;
    let mut sc = -0.5 * (k as f64).ln();
    let m8 = (&kn % 8u32).to_u32().unwrap();
    sc += match m8 {
        1 => 2.0,
        5 => 1.0,
        _ => 0.5,
    } * 2f64.ln();
    let mp = Mp::from(&kn);
    for &p in primes {
        if p == 2 {
            continue;
        }
        let r = mp.rem(p) as u64;
        let lnp = (p as f64).ln();
        if k % p == 0 {
            sc += lnp / p as f64;
        } else if modpow(r, (p as u64 - 1) / 2, p as u64) == 1 {
            sc += 2.0 * lnp / (p as f64 - 1.0);
        }
    }
    sc
}

struct Work {
    r1: Vec<u32>,
    r2: Vec<u32>,
    pos1: Vec<u32>,
    pos2: Vec<u32>,
    skip: Vec<bool>,
    bainv2: Vec<Vec<u32>>,
    sieve: Vec<u8>,
}

fn choose_a(ctx: &Ctx, rng: &mut Rng) -> Vec<usize> {
    let s = ctx.s;
    let lo = {
        let t = (ctx.ideal / 1.5) as u32;
        ctx.fbp.partition_point(|&p| p < t).max(1)
    };
    let hi = {
        let t = (ctx.ideal * 1.5) as u32;
        ctx.fbp.partition_point(|&p| p < t).min(ctx.fb - 1)
    };
    let (mut lo, mut hi) = (lo, hi);
    while hi < lo + 3 * s && (lo > 1 || hi < ctx.fb - 1) {
        lo = lo.saturating_sub(1).max(1);
        hi = (hi + 1).min(ctx.fb - 1);
    }
    let tf = ctx.target.to_f64().unwrap_or(f64::MAX);
    for _ in 0..1000 {
        let mut idx: Vec<usize> = Vec::new();
        let mut prod = BigUint::one();
        while idx.len() < s - 1 {
            let i = lo + (rng.next() % (hi - lo + 1) as u64) as usize;
            if idx.contains(&i) {
                continue;
            }
            idx.push(i);
            prod *= ctx.fbp[i];
        }
        let need = &ctx.target / &prod;
        let nf = need.to_f64().unwrap_or(0.0);
        if nf < 3.0 || nf > *ctx.fbp.last().unwrap() as f64 {
            continue;
        }
        let j = ctx.fbp.partition_point(|&p| (p as f64) < nf);
        let mut best = j.min(ctx.fb - 1);
        if best > 1 && (nf - ctx.fbp[best - 1] as f64).abs() < (ctx.fbp[best] as f64 - nf).abs() {
            best -= 1;
        }
        if best == 0 || idx.contains(&best) {
            continue;
        }
        let a = &prod * ctx.fbp[best];
        let af = a.to_f64().unwrap_or(0.0);
        let ratio = af / tf;
        if ratio < 0.7 || ratio > 1.4 {
            continue;
        }
        idx.push(best);
        return idx;
    }
    panic!("cannot choose a");
}

fn process_poly_candidate(
    ctx: &Ctx,
    x: i64,
    a: &BigInt,
    b: &BigInt,
    c: &BigInt,
    aidx: &[usize],
    w: &Work,
    out: &mut Vec<Rel>,
) {
    let xb = BigInt::from(x);
    let g: BigInt = a * &xb * &xb + b * &xb * 2 + c;
    let neg = g.sign() == Sign::Minus;
    let mut v = Mp::from(g.magnitude());
    let mut f: Vec<(u32, u32)> = Vec::with_capacity(32);
    if neg {
        f.push((0, 1));
    }
    for &i in aidx {
        f.push((i as u32 + 1, 1));
    }
    // direct primes
    for i in 0..ctx.start {
        let p = ctx.fbp[i];
        let mut e = 0;
        while v.rem(p) == 0 {
            v.div(p);
            e += 1;
        }
        if e > 0 {
            f.push((i as u32 + 1, e));
        }
    }
    for &i in aidx {
        if i >= ctx.start {
            let p = ctx.fbp[i];
            let mut e = 0;
            while v.rem(p) == 0 {
                v.div(p);
                e += 1;
            }
            if e > 0 {
                f.push((i as u32 + 1, e));
            }
        }
    }
    for i in ctx.start..ctx.fb {
        let p = ctx.fbp[i];
        let xm = x.rem_euclid(p as i64) as u32;
        if (xm == w.r1[i] || xm == w.r2[i]) && !w.skip[i] {
            let mut e = 0;
            while v.rem(p) == 0 {
                v.div(p);
                e += 1;
            }
            if e > 0 {
                f.push((i as u32 + 1, e));
            }
        }
    }
    let lp;
    match v.small() {
        Some(1) => lp = 0,
        Some(r) if r < ctx.lpmax && r > 1 => lp = r,
        _ => return,
    }
    f.sort_unstable();
    let mut m: Vec<(u32, u32)> = Vec::with_capacity(f.len());
    for (c, e) in f {
        if let Some(l) = m.last_mut() {
            if l.0 == c {
                l.1 += e;
                continue;
            }
        }
        m.push((c, e));
    }
    let t = a * &xb + b;
    let s = t.magnitude() % &ctx.n;
    out.push(Rel { s, f: m, lp });
}

fn worker(ctx: &Ctx, shared: &Mutex<Shared>, stop: &AtomicBool, seed: u64) {
    let mut rng = Rng(seed | 1);
    let fb = ctx.fb;
    let mut w = Work {
        r1: vec![0; fb],
        r2: vec![0; fb],
        pos1: vec![0; fb],
        pos2: vec![0; fb],
        skip: vec![false; fb],
        bainv2: Vec::new(),
        sieve: vec![0u8; BLK],
    };
    let m = ctx.m;
    let mut out: Vec<Rel> = Vec::new();
    while !stop.load(Ordering::Relaxed) {
        let tst = Instant::now();
        let aidx = choose_a(ctx, &mut rng);
        let s = aidx.len();
        let mut a = BigUint::one();
        for &i in &aidx {
            a *= ctx.fbp[i];
        }
        let mut bi: Vec<BigInt> = Vec::new();
        for &i in &aidx {
            let q = ctx.fbp[i] as u64;
            let aq = &a / ctx.fbp[i];
            let aqm = Mp::from(&aq).rem(q as u32) as u64;
            let inv = inv_mod(aqm, q);
            let mut gamma = ctx.fbt[i] as u64 * inv % q;
            if 2 * gamma > q {
                gamma = q - gamma;
            }
            bi.push(BigInt::from(aq * gamma));
        }
        let mut b = BigInt::zero();
        for x in &bi {
            b += x;
        }
        let bi2: Vec<BigInt> = bi.iter().map(|x| x * 2).collect();
        let a_int = BigInt::from(a.clone());
        let am = Mp::from(&a);
        let bm = Mp::from(b.magnitude());
        for k in w.skip.iter_mut() {
            *k = false;
        }
        for &i in &aidx {
            w.skip[i] = true;
        }
        w.bainv2.clear();
        for _ in 0..s {
            w.bainv2.push(vec![0u32; fb]);
        }
        let bi2m: Vec<Mp> = bi2.iter().map(|x| Mp::from(x.magnitude())).collect();
        for i in ctx.start..fb {
            if w.skip[i] {
                continue;
            }
            let p = ctx.fbp[i];
            let pp = p as u64;
            let ainv = inv_mod(am.rem(p) as u64, pp);
            let t = ctx.fbt[i] as u64;
            let bmod = bm.rem(p) as u64;
            w.r1[i] = (((t + pp - bmod) % pp) * ainv % pp) as u32;
            w.r2[i] = (((pp - t) % pp + pp - bmod) % pp * ainv % pp) as u32;
            for j in 0..s {
                w.bainv2[j][i] = (bi2m[j].rem(p) as u64 * ainv % pp) as u32;
            }
        }
        T_SETUP.fetch_add(tst.elapsed().as_nanos() as u64, Ordering::Relaxed);
        let npoly = 1usize << (s - 1);
        for k in 0..npoly {
            if stop.load(Ordering::Relaxed) {
                break;
            }
            if k > 0 {
                let v = k.trailing_zeros() as usize;
                let g = k ^ (k >> 1);
                let neg_now = (g >> v) & 1 == 1;
                // b -= 2B_v when bit becomes 1, else +=
                if neg_now {
                    b -= &bi2[v];
                } else {
                    b += &bi2[v];
                }
                let tab = &w.bainv2[v];
                for i in ctx.start..fb {
                    let p = ctx.fbp[i];
                    let d = tab[i];
                    // r -= delta*ainv  where delta = -2B (neg) => r += d ; else r -= d
                    if neg_now {
                        let mut r = w.r1[i] + d;
                        if r >= p {
                            r -= p;
                        }
                        w.r1[i] = r;
                        let mut r = w.r2[i] + d;
                        if r >= p {
                            r -= p;
                        }
                        w.r2[i] = r;
                    } else {
                        w.r1[i] = if w.r1[i] >= d { w.r1[i] - d } else { w.r1[i] + p - d };
                        w.r2[i] = if w.r2[i] >= d { w.r2[i] - d } else { w.r2[i] + p - d };
                    }
                }
            }
            let c = (&b * &b - &ctx.nint) / &a_int;
            for i in ctx.start..fb {
                if w.skip[i] {
                    continue;
                }
                let p = ctx.fbp[i] as i64;
                w.pos1[i] = ((w.r1[i] as i64 + m) % p) as u32;
                w.pos2[i] = ((w.r2[i] as i64 + m) % p) as u32;
            }
            let before = out.len();
            for blk in 0..ctx.nblk {
                let ts = Instant::now();
                let sv = &mut w.sieve;
                sv.fill(0);
                for i in ctx.start..fb {
                    if w.skip[i] {
                        continue;
                    }
                    let p = ctx.fbp[i] as usize;
                    let l = ctx.fblog[i];
                    unsafe {
                        let sp = sv.as_mut_ptr();
                        let mut x1 = *w.pos1.get_unchecked(i) as usize;
                        let mut x2 = *w.pos2.get_unchecked(i) as usize;
                        if p * 4 < BLK {
                            let p4 = p * 4;
                            while x1 + 3 * p < BLK && x2 + 3 * p < BLK {
                                *sp.add(x1) += l;
                                *sp.add(x2) += l;
                                *sp.add(x1 + p) += l;
                                *sp.add(x2 + p) += l;
                                *sp.add(x1 + 2 * p) += l;
                                *sp.add(x2 + 2 * p) += l;
                                *sp.add(x1 + 3 * p) += l;
                                *sp.add(x2 + 3 * p) += l;
                                x1 += p4;
                                x2 += p4;
                            }
                        }
                        while x1 < BLK {
                            *sp.add(x1) += l;
                            x1 += p;
                        }
                        while x2 < BLK {
                            *sp.add(x2) += l;
                            x2 += p;
                        }
                        *w.pos1.get_unchecked_mut(i) = (x1 - BLK) as u32;
                        *w.pos2.get_unchecked_mut(i) = (x2 - BLK) as u32;
                    }
                }
                let thr = ctx.thr;
                let base = blk * BLK;
                let mut cands: Vec<usize> = Vec::new();
                for (ci, chunk) in w.sieve.chunks(64).enumerate() {
                    let mx = chunk.iter().fold(0u8, |a, &b| a.max(b));
                    if mx >= thr {
                        for (j, &v) in chunk.iter().enumerate() {
                            if v >= thr {
                                cands.push(ci * 64 + j);
                            }
                        }
                    }
                }
                T_SIEVE.fetch_add(ts.elapsed().as_nanos() as u64, Ordering::Relaxed);
                let tc = Instant::now();
                N_CAND.fetch_add(cands.len() as u64, Ordering::Relaxed);
                for off in cands {
                    let x = (base + off) as i64 - m;
                    process_poly_candidate(ctx, x, &a_int, &b, &c, &aidx, &w, &mut out);
                }
                T_CAND.fetch_add(tc.elapsed().as_nanos() as u64, Ordering::Relaxed);
            }
            let _ = before;
            if !out.is_empty() || k % 8 == 7 {
                let mut sh = shared.lock().unwrap();
                sh.npoly += 8;
                for r in out.drain(..) {
                    let key = key_of(&r.s);
                    if !sh.seen.insert(key) {
                        continue;
                    }
                    if r.lp == 0 {
                        sh.fulls.push(r);
                        sh.usable += 1;
                        sh.nfull += 1;
                    } else {
                        sh.npart += 1;
                        let e = sh.parts.entry(r.lp).or_default();
                        let was = !e.is_empty();
                        e.push(r);
                        if was {
                            sh.usable += 1;
                        }
                    }
                }
            }
        }
    }
}

// dense GF(2) elimination; returns dependencies as lists of row ids
fn find_deps(rows: &[Vec<(u32, u32)>], cols: usize, threads: usize) -> Vec<Vec<usize>> {
    let nr = rows.len();
    let w = (cols + 63) / 64;
    let hw = (nr + 63) / 64;
    let rw = w + hw;
    let mut mat = vec![0u64; nr * rw];
    for (i, r) in rows.iter().enumerate() {
        let row = &mut mat[i * rw..(i + 1) * rw];
        for &(c, e) in r {
            if e & 1 == 1 {
                row[c as usize / 64] ^= 1u64 << (c % 64);
            }
        }
        row[w + i / 64] |= 1u64 << (i % 64);
    }
    let mut rank = 0;
    let mut piv = vec![0u64; rw];
    for c in 0..cols {
        let cw = c / 64;
        let cb = 1u64 << (c % 64);
        let mut found = None;
        for r in rank..nr {
            if mat[r * rw + cw] & cb != 0 {
                found = Some(r);
                break;
            }
        }
        let Some(r) = found else { continue };
        if r != rank {
            for k in 0..rw {
                mat.swap(r * rw + k, rank * rw + k);
            }
        }
        piv.copy_from_slice(&mat[rank * rw..(rank + 1) * rw]);
        let (_, below) = mat.split_at_mut((rank + 1) * rw);
        let nbelow = nr - rank - 1;
        let work = nbelow * (rw - cw);
        let pv = &piv;
        let doit = |chunk: &mut [u64]| {
            for row in chunk.chunks_mut(rw) {
                if row[cw] & cb != 0 {
                    for k in cw..rw {
                        row[k] ^= pv[k];
                    }
                }
            }
        };
        if threads > 1 && work > 400_000 {
            let per = (nbelow + threads - 1) / threads;
            std::thread::scope(|s| {
                for ch in below.chunks_mut(per * rw) {
                    s.spawn(move || doit(ch));
                }
            });
        } else {
            doit(below);
        }
        rank += 1;
    }
    let mut deps = Vec::new();
    for r in rank..nr {
        let h = &mat[r * rw + w..(r + 1) * rw];
        let mut d = Vec::new();
        for i in 0..nr {
            if h[i / 64] >> (i % 64) & 1 == 1 {
                d.push(i);
            }
        }
        deps.push(d);
    }
    deps
}

fn siqs(n0: &BigUint, deadline: Instant) -> Option<BigUint> {
    let dbg = std::env::var("FDEBUG").is_ok();
    let t0 = Instant::now();
    let small_primes = primes_upto(3000);
    let mut bestk = 1;
    let mut bests = f64::MIN;
    for &k in &[1u32, 3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 29, 31, 33, 35, 37, 39, 41, 43, 47] {
        let s = kron_score(n0, k, &small_primes);
        if s > bests {
            bests = s;
            bestk = k;
        }
    }
    let n = n0 * bestk;
    let digits = n.bits() as f64 * 0.30103;
    let pr = params(digits);
    // factor base
    let mut fbp: Vec<u32> = vec![2];
    let mut fbt: Vec<u32> = vec![1];
    let mut lim = 100000usize.max(pr.fb * 20);
    let nm = Mp::from(&n);
    loop {
        let ps = primes_upto(lim);
        fbp.truncate(1);
        fbt.truncate(1);
        for &p in ps.iter().skip(1) {
            let r = nm.rem(p) as u64;
            if r == 0 {
                let pb = BigUint::from(p);
                let n0m = n0 % p;
                if n0m.is_zero() {
                    return Some(pb);
                }
                continue;
            }
            if modpow(r, (p as u64 - 1) / 2, p as u64) == 1 {
                fbp.push(p);
                fbt.push(sqrt_mod(r, p as u64) as u32);
                if fbp.len() >= pr.fb {
                    break;
                }
            }
        }
        if fbp.len() >= pr.fb {
            break;
        }
        lim *= 2;
    }
    let fb = fbp.len();
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    let m = (pr.nb * BLK) as i64;
    let nblk = 2 * pr.nb;
    let nbits = n.bits() as f64;
    let log2n = {
        // log2 of n as f64
        let sh = nbits as u64 - 60;
        ((&n >> sh).to_f64().unwrap()).log2() + sh as f64
    };
    let gmax_bits = (m as f64).log2() + 0.5 * (log2n - 1.0);
    let scale = (230.0 / gmax_bits).clamp(1.0, 2.0);
    let fblog: Vec<u8> = fbp.iter().map(|&p| ((p as f64).log2() * scale).round().max(1.0) as u8).collect();
    let lpmax = ((*fbp.last().unwrap() as f64) * pr.lpk) as u64;
    let thr = (scale * (gmax_bits - (lpmax as f64).log2() - pr.fudge)).max(1.0) as u8;
    let skipp = pr.skip as u32;
    let start = fbp.iter().position(|&p| p >= skipp).unwrap_or(fb / 2).min(fb / 2);
    let target = {
        let t = (&n * 2u32).sqrt() / (m as u64);
        t
    };
    let tbits = target.bits() as f64;
    let pmid = fbp[fb * 3 / 4] as f64;
    let s = ((tbits / pmid.log2()).ceil() as usize).clamp(2, 14);
    let ideal = (tbits * 2f64.ln() / s as f64).exp();
    let ctx = Ctx {
        n: n.clone(),
        nint: BigInt::from(n.clone()),
        fbp,
        fblog,
        fbt,
        fb,
        start,
        m,
        nblk,
        thr,
        lpmax,
        target,
        s,
        ideal,
    };
    if dbg {
        eprintln!(
            "k={} digits={:.1} fb={} maxp={} nb={} s={} thr={} scale={:.2} lpmax={} setup={:?}",
            bestk,
            digits,
            fb,
            ctx.fbp[fb - 1],
            pr.nb,
            s,
            thr,
            scale,
            lpmax,
            t0.elapsed()
        );
    }
    let shared = Mutex::new(Shared {
        fulls: Vec::new(),
        parts: HashMap::new(),
        usable: 0,
        seen: HashSet::new(),
        npoly: 0,
        nfull: 0,
        npart: 0,
    });
    let mut need = fb + 1 + 40;
    let seedc = AtomicU64::new(0x1234567);
    loop {
        let stop = AtomicBool::new(false);
        let mut timed_out = false;
        std::thread::scope(|sc| {
            for _ in 0..nthreads {
                let sd = seedc.fetch_add(0x9E3779B97F4A7C15, Ordering::Relaxed);
                let (ctx, shared, stop) = (&ctx, &shared, &stop);
                sc.spawn(move || worker(ctx, shared, stop, sd ^ 0xDEADBEEF12345));
            }
            let mut last = Instant::now();
            loop {
                std::thread::sleep(Duration::from_millis(5));
                let sh = shared.lock().unwrap();
                if dbg && last.elapsed() > Duration::from_millis(1000) {
                    last = Instant::now();
                    eprintln!(
                        "  t={:?} usable={}/{} full={} part={} poly={}",
                        t0.elapsed(),
                        sh.usable,
                        need,
                        sh.nfull,
                        sh.npart,
                        sh.npoly
                    );
                }
                if sh.usable >= need {
                    break;
                }
                if Instant::now() >= deadline {
                    timed_out = true;
                    break;
                }
            }
            stop.store(true, Ordering::Relaxed);
        });
        if timed_out {
            return None;
        }
        if dbg {
            eprintln!("sieving done at {:?} sieve={}ms cand={}ms setup={}ms ncand={}", t0.elapsed(), T_SIEVE.load(Ordering::Relaxed)/1000000, T_CAND.load(Ordering::Relaxed)/1000000, T_SETUP.load(Ordering::Relaxed)/1000000, N_CAND.load(Ordering::Relaxed));
        }
        // build rows
        let sh = shared.lock().unwrap();
        let mut rels: Vec<Rel> = sh.fulls.clone();
        for (&l, v) in sh.parts.iter() {
            for j in 1..v.len() {
                let s = (&v[0].s * &v[j].s) % &ctx.n;
                let f = merge_f(&v[0].f, &v[j].f);
                rels.push(Rel { s, f, lp: l });
            }
        }
        drop(sh);
        let cols = fb + 1;
        let rows: Vec<Vec<(u32, u32)>> = rels.iter().map(|r| r.f.clone()).collect();
        let deps = find_deps(&rows, cols, nthreads);
        if dbg {
            eprintln!("LA done at {:?}, rows={} deps={}", t0.elapsed(), rows.len(), deps.len());
        }
        for d in deps.iter() {
            let mut x = BigUint::one();
            let mut e = vec![0u64; cols];
            let mut y = BigUint::one();
            for &r in d {
                x = x * &rels[r].s % &ctx.n;
                for &(c, ex) in &rels[r].f {
                    e[c as usize] += ex as u64;
                }
                if rels[r].lp != 0 {
                    y = y * rels[r].lp % &ctx.n;
                }
            }
            for c in 1..cols {
                if e[c] > 0 {
                    debug_assert!(e[c] % 2 == 0);
                    y = y * BigUint::from(ctx.fbp[c - 1]).modpow(&BigUint::from(e[c] / 2), &ctx.n) % &ctx.n;
                }
            }
            let diff = if x > y { &x - &y } else { &y - &x };
            let g = diff.gcd(n0);
            if !g.is_one() && &g != n0 {
                return Some(g);
            }
        }
        need += 60;
    }
}

fn factor(n: &BigUint, deadline: Instant) -> Option<(BigUint, BigUint)> {
    if let Some(v) = n.to_u64() {
        if v < 4 {
            return None;
        }
        let d = rho_u64(v);
        let (a, b) = (d.min(v / d), d.max(v / d));
        return Some((BigUint::from(a), BigUint::from(b)));
    }
    for p in primes_upto(1000) {
        if (n % p).is_zero() {
            let q = n / p;
            let p = BigUint::from(p);
            return Some(if p < q { (p, q) } else { (q, p) });
        }
    }
    let r = n.sqrt();
    if &(&r * &r) == n {
        return Some((r.clone(), r));
    }
    let g = siqs(n, deadline)?;
    let h = n / &g;
    Some(if g < h { (g, h) } else { (h, g) })
}

// ---------------------------------------------------------------- IO

struct Pending {
    q: VecDeque<(String, String)>,
    cur: Option<String>,
    eof: bool,
}

fn parse_line(line: &str) -> Option<(String, String)> {
    let ip = line.find("\"id\"")?;
    let rest = &line[ip + 4..];
    let colon = rest.find(':')?;
    let rest = rest[colon + 1..].trim_start();
    let id = if rest.starts_with('"') {
        let end = rest[1..].find('"')? + 2;
        rest[..end].to_string()
    } else {
        let end = rest.find(|c| c == ',' || c == '}').unwrap_or(rest.len());
        rest[..end].trim().to_string()
    };
    let np = line.find("\"n\"")?;
    let rest = &line[np + 3..];
    let colon = rest.find(':')?;
    let rest = rest[colon + 1..].trim_start().trim_start_matches('"');
    let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
    Some((id, rest[..end].to_string()))
}

fn main() {
    let start = Instant::now();
    let args: Vec<String> = std::env::args().collect();
    let mut tl = 60.0f64;
    for i in 0..args.len() {
        if args[i] == "--time-limit" && i + 1 < args.len() {
            tl = args[i + 1].parse().unwrap_or(60.0);
        }
    }
    let deadline = start + Duration::from_secs_f64((tl - 0.25).max(0.05));
    let st = Arc::new(Mutex::new(Pending { q: VecDeque::new(), cur: None, eof: false }));
    {
        let st = st.clone();
        std::thread::spawn(move || {
            let stdin = std::io::stdin();
            for line in stdin.lock().lines() {
                let Ok(line) = line else { break };
                if let Some(x) = parse_line(&line) {
                    st.lock().unwrap().q.push_back(x);
                }
            }
            st.lock().unwrap().eof = true;
        });
    }
    {
        let st = st.clone();
        std::thread::spawn(move || {
            let dl = deadline + Duration::from_millis(100);
            let now = Instant::now();
            if dl > now {
                std::thread::sleep(dl - now);
            }
            let mut g = st.lock().unwrap();
            let out = std::io::stdout();
            let mut o = out.lock();
            let mut ids: Vec<String> = Vec::new();
            if let Some(c) = g.cur.take() {
                ids.push(c);
            }
            for (id, _) in g.q.drain(..) {
                ids.push(id);
            }
            for id in ids {
                let _ = writeln!(o, "{{\"id\": {}, \"answer\": null, \"timeout\": true}}", id);
            }
            let _ = o.flush();
            std::process::exit(0);
        });
    }
    loop {
        let item = {
            let mut g = st.lock().unwrap();
            if let Some((id, n)) = g.q.pop_front() {
                g.cur = Some(id.clone());
                Some((id, n))
            } else if g.eof {
                break;
            } else {
                None
            }
        };
        let Some((id, ns)) = item else {
            std::thread::sleep(Duration::from_millis(1));
            continue;
        };
        let n: BigUint = ns.parse().unwrap_or_else(|_| BigUint::from(4u32));
        let res = factor(&n, deadline);
        let mut g = st.lock().unwrap();
        if g.cur.is_none() {
            break;
        }
        g.cur = None;
        let out = std::io::stdout();
        let mut o = out.lock();
        match res {
            Some((p, q)) => {
                let _ = writeln!(o, "{{\"id\": {}, \"answer\": \"{} {}\"}}", id, p, q);
            }
            None => {
                let _ = writeln!(o, "{{\"id\": {}, \"answer\": null, \"timeout\": true}}", id);
            }
        }
        let _ = o.flush();
    }
}
