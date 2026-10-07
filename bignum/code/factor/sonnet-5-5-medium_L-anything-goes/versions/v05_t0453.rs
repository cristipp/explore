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
    lp: u64,
    ym: u64,
}

struct Shared {
    full: Vec<Rel>,
    part: HashMap<u64, Vec<Rel>>,
}

struct Fb {
    p: Vec<u32>,
    t: Vec<u32>,
    lg: Vec<u8>,
    pinv: Vec<u32>,
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

fn worker(ctx: &Ctx, seed: u64, stop: &AtomicBool, shared: &Mutex<Shared>, usable: &AtomicUsize) {
    let fb = &ctx.fb;
    let par = &ctx.par;
    let nfb = par.nfb;
    let m: usize = 1 << par.mlog;
    let two_m = 2 * m;
    let bs = two_m.min(1 << 15);
    let nblocks = two_m / bs;
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
    let mut pr1 = vec![0u32; nfb];
    let mut pr2 = vec![0u32; nfb];
    let mut st1 = vec![0u32; nfb];
    let mut st2 = vec![0u32; nfb];
    let mlogm = m as u64;

    'outer: while !stop.load(Ordering::Relaxed) {
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
        for &i in &qi {
            let q = fb.p[i];
            let al = &a / q;
            let am = (&al % q).to_u32().unwrap();
            let g = mulmod32(fb.t[i], inv_mod(am, q), q);
            let g = g.min(q - g);
            bl.push(BigInt::from(al * g));
        }
        let mut b = BigInt::zero();
        for x in &bl {
            b += x;
        }
        // a mod p, ainv, bainv
        for idx in 1..nfb {
            if isa[idx] {
                ainv[idx] = 0;
                for l in 0..s {
                    bainv[l][idx] = 0;
                }
                continue;
            }
            let p = fb.p[idx];
            let mut am = 1u32;
            for &i in &qi {
                am = mulmod32(am, fb.p[i] % p, p);
            }
            let ai_p = inv_mod(am, p);
            ainv[idx] = ai_p;
            for l in 0..s {
                let bm = (&bl[l] % p).to_u32().unwrap_or(0); // nonneg
                let b2 = (2 * bm as u64 % p as u64) as u32;
                bainv[l][idx] = mulmod32(b2, ai_p, p);
            }
            let bmod = (((&b % p as i64).to_i64().unwrap() + p as i64) % p as i64) as u32;
            let t = fb.t[idx];
            rx1[idx] = mulmod32((t + p - bmod) % p, ai_p, p);
            rx2[idx] = mulmod32((p - t + p - bmod) % p, ai_p, p);
        }
        let npoly = 1usize << (s - 1);
        let mut signs = vec![false; s]; // true = flipped (-)
        for pi in 0..npoly {
            if stop.load(Ordering::Relaxed) {
                break 'outer;
            }
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
                st2[idx] = if fb.t[idx] == 0 { u32::MAX } else { s2 };
            }
            for &i in &qi {
                st1[i] = u32::MAX;
                st2[i] = u32::MAX;
            }
            let mut found: Vec<Rel> = Vec::new();
            for blk in 0..nblocks {
                let blo = (blk * bs) as u32;
                let bhi = blo + bs as u32;
                buf.iter_mut().for_each(|v| *v = v0);
                for idx in par.minidx..nfb {
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
                // scan
                for w in 0..bs / 8 {
                    let word = u64::from_le_bytes(buf[w * 8..w * 8 + 8].try_into().unwrap());
                    if word & 0x8080808080808080 != 0 {
                        for k in 0..8 {
                            if buf[w * 8 + k] & 0x80 != 0 {
                                let i = blk * bs + w * 8 + k;
                                if let Some(r) = try_relation(ctx, i, mlogm, &ai, &b, &qi, &isa, &pr1, &pr2) {
                                    found.push(r);
                                }
                            }
                        }
                    }
                }
            }
            if !found.is_empty() {
                let mut sh = shared.lock().unwrap();
                let mut add = 0;
                for r in found {
                    if r.lp <= 1 {
                        sh.full.push(r);
                        add += 1;
                    } else {
                        let e = sh.part.entry(r.lp).or_default();
                        if !e.is_empty() {
                            add += 1;
                        }
                        e.push(r);
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
    qi: &[usize],
    isa: &[bool],
    pr1: &[u32],
    pr2: &[u32],
) -> Option<Rel> {
    let fb = &ctx.fb;
    let x = i as i64 - m as i64;
    let axb = a * x + b;
    let qa = &axb * &axb - &ctx.ni;
    let q = qa / a;
    let neg = q.sign() == Sign::Minus;
    let digs = q.magnitude().to_u64_digits();
    if digs.len() > 4 || digs.is_empty() {
        return None;
    }
    let mut mag = [0u64; 4];
    mag[..digs.len()].copy_from_slice(&digs);
    let mut e: Vec<(u32, u32)> = Vec::with_capacity(40);
    if neg {
        e.push((0, 1));
    }
    let mut tz = 0;
    while mag[0] & 1 == 0 {
        if mag == [0; 4] {
            return None;
        }
        shr1(&mut mag);
        tz += 1;
    }
    if tz > 0 {
        e.push((1, tz));
    }
    let iu = i as u32;
    for idx in 1..ctx.par.nfb {
        if isa[idx] {
            continue;
        }
        let p = fb.p[idx];
        let pinv = fb.pinv[idx];
        let lim = fb.lim[idx];
        let d1 = iu + p - pr1[idx];
        let d2 = iu + p - pr2[idx];
        if d1.wrapping_mul(pinv) <= lim || d2.wrapping_mul(pinv) <= lim {
            let mut c = 0;
            while div_exact(&mut mag, p as u64) {
                c += 1;
            }
            if c > 0 {
                e.push((idx as u32 + 1, c));
            }
        }
    }
    for &l in qi {
        let p = fb.p[l] as u64;
        let mut c = 1;
        while div_exact(&mut mag, p) {
            c += 1;
        }
        e.push((l as u32 + 1, c));
    }
    let mut lp = 1;
    if !(mag[0] == 1 && mag[1] == 0 && mag[2] == 0 && mag[3] == 0) {
        if mag[1] == 0 && mag[2] == 0 && mag[3] == 0 && mag[0] <= ctx.par.lpb {
            lp = mag[0];
        } else {
            return None;
        }
    }
    let xv = axb.magnitude() % &ctx.n;
    Some(Rel { x: xv, e, lp, ym: 1 })
}

fn merge_rel(r0: &Rel, r1: &Rel, n: &BigUint) -> Rel {
    let mut m: HashMap<u32, u32> = HashMap::new();
    for &(c, e) in r0.e.iter().chain(r1.e.iter()) {
        *m.entry(c).or_default() += e;
    }
    let mut e: Vec<(u32, u32)> = m.into_iter().collect();
    e.sort();
    Rel { x: (&r0.x * &r1.x) % n, e, lp: 1, ym: r0.lp }
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
    let mut cur = 0;
    let mut tmp = vec![0u64; w];
    for c in 0..ncols {
        let (cw, cb) = (c / 64, c % 64);
        let mut piv = None;
        for r in cur..nrows {
            if data[r * w + cw] >> cb & 1 == 1 {
                piv = Some(r);
                break;
            }
        }
        let Some(pv) = piv else { continue };
        if pv != cur {
            for k in 0..w {
                data.swap(pv * w + k, cur * w + k);
            }
        }
        tmp.copy_from_slice(&data[cur * w..(cur + 1) * w]);
        let rest = &mut data[(cur + 1) * w..];
        let f = |row: &mut [u64]| {
            if row[cw] >> cb & 1 == 1 {
                for k in cw..w {
                    row[k] ^= tmp[k];
                }
            }
        };
        if (nrows - cur) * (w - cw) > 200_000 {
            rest.par_chunks_mut(w).for_each(f);
        } else {
            rest.chunks_mut(w).for_each(f);
        }
        cur += 1;
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
    let lim: Vec<u32> = p.iter().map(|&q| u32::MAX / q).collect();
    let mmod: Vec<u32> = p.iter().map(|&q| m % q).collect();
    let fbmax = *p.last().unwrap() as u64;
    let lpm = env_f("LPM", 30.0);
    let lpb = ((fbmax as f64 * lpm) as u64).min(fbmax * fbmax / 2);
    let nbits = n.bits() as f64;
    let qbits = nbits / 2.0 - 0.5 + (m as f64).log2();
    let minp = env_f("MINP", 30.0) as u32;
    let minidx = p.iter().position(|&q| q >= minp).unwrap_or(1).max(1);
    let bias: f64 = p[1..minidx].iter().map(|&q| 2.0 * (q as f64).log2() / (q as f64 - 1.0)).sum();
    let slack = env_f("SLACK", 2.0);
    let thr = (qbits - (lpb as f64).log2() - bias - slack).max(1.0) as i32;
    let a_target = (&n * 2u32).sqrt() / m;
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(8);
    let ctx = Ctx {
        ni: BigInt::from(n.clone()),
        n: n.clone(),
        fb: Fb { p, t, lg, pinv, lim, mmod },
        par: Params { nfb, mlog, minidx, thr, lpb },
        a_target,
        nthreads,
    };
    if verbose {
        eprintln!("k={} digits={} nfb={} fbmax={} mlog={} thr={} lpb={} minidx={}", k, digits, nfb, fbmax, mlog, thr, lpb, minidx);
    }
    let shared = Mutex::new(Shared { full: vec![], part: HashMap::new() });
    let usable = AtomicUsize::new(0);
    let ncols = nfb + 1;
    let mut target = ncols + 64;
    let mut round = 0u64;
    loop {
        let stop = AtomicBool::new(false);
        std::thread::scope(|sc| {
            for ti in 0..ctx.nthreads {
                let (ctx, stop, shared, usable) = (&ctx, &stop, &shared, &usable);
                let seed = ti as u64 + 1000 * round + 7 + (Instant::now().elapsed().as_nanos() as u64);
                sc.spawn(move || worker(ctx, seed ^ (std::process::id() as u64) << 20, stop, shared, usable));
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
            eprintln!("sieve done at {:.2}s usable={}", t0.elapsed().as_secs_f64(), usable.load(Ordering::Relaxed));
        }
        // build relation set
        let sh = shared.lock().unwrap();
        let mut rels: Vec<Rel> = Vec::new();
        for r in &sh.full {
            rels.push(Rel { x: r.x.clone(), e: r.e.clone(), lp: 1, ym: 1 });
        }
        for (_, g) in sh.part.iter() {
            for j in 1..g.len() {
                rels.push(merge_rel(&g[0], &g[j], &ctx.n));
            }
        }
        drop(sh);
        if std::env::var("CHECK").is_ok() {
            let mut bad = 0;
            let mut seen = std::collections::HashSet::new();
            let mut dup = 0;
            for r in &rels {
                if r.ym == 1 && !seen.insert(r.x.clone()) { dup += 1; }
                let mut v = BigUint::one();
                let mut neg = false;
                for &(c, e) in &r.e {
                    if c == 0 { neg = e % 2 == 1; continue; }
                    v = v * BigUint::from(ctx.fb.p[c as usize - 1]).pow(e) % &ctx.n;
                }
                if r.ym > 1 { v = v * r.ym * r.ym % &ctx.n; }
                let x2 = &r.x * &r.x % &ctx.n;
                let ok = if neg { (&x2 + &v) % &ctx.n == BigUint::zero() } else { x2 == v };
                if !ok { bad += 1; if bad < 6 { eprintln!("bad ym={} neg={} e={:?}", r.ym, neg, r.e); } }
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
                if r.ym > 1 {
                    y = y * r.ym % &ctx.n;
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
