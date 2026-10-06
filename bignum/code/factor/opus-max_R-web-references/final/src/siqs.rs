// Self-initialising quadratic sieve, multi-threaded, single large prime variation.

use crate::linalg;
use crate::util::*;
use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc, Mutex};
use std::time::{Duration, Instant};

const BS_BITS: usize = 15;
const BS: usize = 1 << BS_BITS;
pub static STAT_POLY: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static STAT_CAND: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static T_INIT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static T_FILL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static T_SIEVE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static T_TD: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static STAT_REL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

pub struct Rel {
    pub y: BigUint,
    pub factors: Vec<u32>, // 0 = -1, i+1 = fb[i]
    pub lp: u64,
}

struct Ctx {
    n: BigUint,
    kn: BigInt,
    fb: Vec<u32>,
    sqrt: Vec<u32>,
    logp: Vec<u8>,
    recip: Vec<u64>,
    nfb: usize,
    med_start: usize,
    large_start: usize,
    nblocks: usize,
    m: i64,
    lp_bound: u64,
    thresh: u8,
    s: usize,
    q_lo: usize,
    q_hi: usize,
    log_target_a: f64,
    used_a: Mutex<HashSet<Vec<u32>>>,
}

fn params_for(digits: f64) -> (f64, f64, f64, f64) {
    // digits, fb size, blocks per side, lp multiplier, thresh fudge
    let table: &[(f64, f64, f64, f64, f64)] = &[
        (18.0, 60.0, 1.0, 20.0, 2.0),
        (24.0, 90.0, 1.0, 25.0, 2.0),
        (30.0, 140.0, 1.0, 30.0, 2.5),
        (36.0, 220.0, 1.0, 35.0, 3.0),
        (42.0, 400.0, 1.0, 40.0, 3.0),
        (48.0, 900.0, 1.0, 45.0, 6.0),
        (54.0, 2000.0, 1.0, 50.0, 12.0),
        (60.0, 4500.0, 2.0, 60.0, 20.0),
        (66.0, 9000.0, 2.0, 70.0, 23.0),
        (72.0, 18000.0, 3.0, 80.0, 23.0),
        (78.0, 30000.0, 4.0, 90.0, 23.0),
        (84.0, 50000.0, 5.0, 100.0, 23.0),
        (90.0, 75000.0, 6.0, 110.0, 23.0),
        (96.0, 100000.0, 8.0, 120.0, 23.0),
        (102.0, 120000.0, 10.0, 130.0, 23.0),
        (110.0, 130000.0, 12.0, 140.0, 23.0),
    ];
    let d = digits.max(table[0].0).min(table[table.len() - 1].0);
    for w in table.windows(2) {
        let (a, b) = (w[0], w[1]);
        if d >= a.0 && d <= b.0 {
            let t = (d - a.0) / (b.0 - a.0);
            return (
                a.1 + t * (b.1 - a.1),
                (a.2 + t * (b.2 - a.2)).round(),
                a.3 + t * (b.3 - a.3),
                a.4 + t * (b.4 - a.4),
            );
        }
    }
    let l = table[table.len() - 1];
    (l.1, l.2, l.3, l.4)
}

fn choose_multiplier(n: &BigUint) -> u64 {
    let ks: [u64; 30] = [
        1, 3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 29, 31, 33, 35, 37, 39, 41, 43, 47, 51, 53, 55, 57,
        59, 61, 65, 67, 69, 71,
    ];
    let primes = primes_up_to(2000);
    let mut best = (f64::MIN, 1u64);
    for &k in &ks {
        let kn = n * k;
        let mut score = -0.5 * (k as f64).ln();
        let m8 = (&kn % 8u32).to_u32().unwrap();
        let ln2 = 2f64.ln();
        score += match m8 {
            1 => 2.0 * ln2,
            5 => ln2,
            3 | 7 => 0.5 * ln2,
            _ => 0.0,
        };
        for &p in primes.iter().skip(1) {
            let r = (&kn % p).to_u64().unwrap();
            let lp = (p as f64).ln();
            if r == 0 {
                score += lp / p as f64;
            } else if powmod(r, (p as u64 - 1) / 2, p as u64) == 1 {
                score += 2.0 * lp / (p as f64 - 1.0);
            }
        }
        if score > best.0 {
            best = (score, k);
        }
    }
    best.1
}

fn to_limbs(x: &BigUint) -> Vec<u32> {
    x.to_u32_digits()
}

pub fn siqs(n: &BigUint, deadline: Instant, nthreads: usize, verbose: bool) -> Option<BigUint> {
    let t0 = Instant::now();
    let k = choose_multiplier(n);
    let kn = n * k;
    let digits = n.to_string().len() as f64;
    let (fbsize, bps, lpmult, fudge) = params_for(digits);
    let envf = |k: &str, d: f64| std::env::var(k).ok().and_then(|v| v.parse::<f64>().ok()).unwrap_or(d);
    let fbsize = (fbsize * envf("FBMUL", 1.0)) as usize;
    let bps = envf("BPS", bps);
    let lpmult = envf("LPMULT", lpmult);
    let fudge = envf("FUDGE", fudge);
    // factor base
    let mut fb = vec![2u32];
    let mut sq = vec![1u32];
    let mut bound = (fbsize * 30).max(1000);
    loop {
        let primes = primes_up_to(bound);
        fb.truncate(1);
        sq.truncate(1);
        for &p in primes.iter().skip(1) {
            let r = (&kn % p).to_u64().unwrap();
            if r == 0 {
                if (n % p).is_zero() {
                    return Some(BigUint::from(p));
                }
                fb.push(p);
                sq.push(0);
            } else if powmod(r, (p as u64 - 1) / 2, p as u64) == 1 {
                fb.push(p);
                sq.push(sqrt_mod(r, p as u64) as u32);
            }
            if fb.len() >= fbsize {
                break;
            }
        }
        if fb.len() >= fbsize {
            break;
        }
        bound *= 2;
    }
    let nfb = fb.len();
    let logp: Vec<u8> = fb.iter().map(|&p| ((p as f64).log2()).round() as u8).collect();
    let smallp = envf("SMALLP", if digits < 50.0 { 30.0 } else if digits < 60.0 { 120.0 } else { 300.0 });
    let med_start = fb.iter().position(|&p| p as f64 >= smallp).unwrap_or(nfb).min(nfb);
    let large_start = fb.iter().position(|&p| p as usize >= BS).unwrap_or(nfb);
    let nblocks = 2 * bps as usize;
    let m = (bps as usize * BS) as i64;
    let pmax = fb[nfb - 1] as u64;
    let lp_bound = (pmax as f64 * lpmult) as u64;
    let lp_bound = lp_bound.min(pmax * pmax - 1);
    let kn_bits = kn.bits() as f64;
    let log_gmax = (m as f64).log2() + kn_bits / 2.0 - 0.5;
    let thresh_f = log_gmax - (lp_bound as f64).log2() - fudge;
    let thresh = thresh_f.max(1.0).min(250.0) as u8;
    // A parameters: A ~ sqrt(2kN)/M
    let log_target_a = (kn_bits + 1.0) / 2.0 - (m as f64).log2();
    let mut s = ((log_target_a / 11.0).round() as usize).max(2);
    let max_q = fb[nfb - 1] as f64;
    while s < 30 && (log_target_a / s as f64).exp2() > max_q * 0.5 {
        s += 1;
    }
    while s > 2 && (log_target_a / s as f64).exp2() < 40.0 {
        s -= 1;
    }
    let qc = (log_target_a / s as f64).exp2();
    let mut q_lo = fb.iter().position(|&p| p as f64 >= qc * 0.5).unwrap_or(nfb / 2).max(med_start);
    let mut q_hi = fb.iter().position(|&p| p as f64 > qc * 2.0).unwrap_or(nfb);
    q_hi = q_hi.min(large_start).min(nfb);
    while q_hi - q_lo.min(q_hi) < s + 6 {
        if q_lo > med_start {
            q_lo -= 1;
        }
        if q_hi < nfb.min(large_start) {
            q_hi += 1;
        }
        if q_lo <= med_start && q_hi >= nfb.min(large_start) {
            break;
        }
    }
    // remove primes with zero sqrt (dividing k) from candidacy by checking in choose_a
    if verbose {
        eprintln!(
            "siqs: digits={} k={} nfb={} pmax={} M={} s={} q~{:.0} [{}..{}] thresh={} lp_bound={} med_start={} large_start={}",
            digits, k, nfb, pmax, m, s, qc, fb[q_lo], fb[q_hi.min(nfb) - 1], thresh, lp_bound, med_start, large_start
        );
    }
    let ctx = Arc::new(Ctx {
        n: n.clone(),
        kn: BigInt::from(kn.clone()),
        fb: fb.clone(),
        sqrt: sq,
        recip: fb.iter().map(|&p| (1u64 << 40) / p as u64 + 1).collect(),
        logp,
        nfb,
        med_start,
        large_start,
        nblocks,
        m,
        lp_bound,
        thresh,
        s,
        q_lo,
        q_hi,
        log_target_a,
        used_a: Mutex::new(HashSet::new()),
    });

    let mut fulls: Vec<Rel> = Vec::new();
    let mut partials: Vec<Rel> = Vec::new();
    let mut lp_first: HashMap<u64, usize> = HashMap::new();
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    let mut seen: HashSet<Vec<u32>> = HashSet::new();
    let mut extra = 64usize;
    let mut round = 0u64;
    loop {
        let target = nfb + extra;
        let stop = Arc::new(AtomicBool::new(false));
        let (tx, rx) = mpsc::channel::<Rel>();
        let mut handles = vec![];
        for t in 0..nthreads {
            let ctx = ctx.clone();
            let tx = tx.clone();
            let stop = stop.clone();
            let seed = 0x9e3779b97f4a7c15u64
                .wrapping_mul(t as u64 + 1 + round * 1000)
                .wrapping_add(n.to_u64_digits()[0]);
            handles.push(std::thread::spawn(move || worker(ctx, seed, tx, stop)));
        }
        drop(tx);
        let mut last_report = Instant::now();
        while fulls.len() + pairs.len() < target {
            if Instant::now() >= deadline {
                stop.store(true, Ordering::Relaxed);
                return None;
            }
            match rx.recv_timeout(Duration::from_millis(50)) {
                Ok(rel) => {
                    let key = rel.y.to_u32_digits();
                    if !seen.insert(key) {
                        continue;
                    }
                    if rel.lp == 1 {
                        fulls.push(rel);
                    } else {
                        let lp = rel.lp;
                        let idx = partials.len();
                        partials.push(rel);
                        match lp_first.get(&lp) {
                            Some(&f) => pairs.push((f, idx)),
                            None => {
                                lp_first.insert(lp, idx);
                            }
                        }
                    }
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {}
                Err(_) => break,
            }
            if verbose && last_report.elapsed().as_secs_f64() > 2.0 {
                last_report = Instant::now();
                eprintln!(
                    "  {:.1}s: fulls={} partials={} pairs={} / {}",
                    t0.elapsed().as_secs_f64(),
                    fulls.len(),
                    partials.len(),
                    pairs.len(),
                    target
                );
            }
        }
        stop.store(true, Ordering::Relaxed);
        drop(rx);
        for h in handles {
            let _ = h.join();
        }
        if verbose {
            eprintln!(
                "  sieving done {:.2}s: [init {:.2} fill {:.2} sieve {:.2} td {:.2}] polys={} cands={} rels={} fulls={} partials={} pairs={}",
                t0.elapsed().as_secs_f64(), T_INIT.load(Ordering::Relaxed) as f64*1e-9, T_FILL.load(Ordering::Relaxed) as f64*1e-9, T_SIEVE.load(Ordering::Relaxed) as f64*1e-9, T_TD.load(Ordering::Relaxed) as f64*1e-9, STAT_POLY.load(Ordering::Relaxed), STAT_CAND.load(Ordering::Relaxed), STAT_REL.load(Ordering::Relaxed),
                fulls.len(),
                partials.len(),
                pairs.len()
            );
        }
        // build matrix
        let nrows = nfb + 1;
        let ncols = fulls.len() + pairs.len();
        let mut cols: Vec<Vec<u32>> = Vec::with_capacity(ncols);
        let mut cnt = vec![0u32; nrows];
        let odd_rows = |facs: &[&[u32]], cnt: &mut Vec<u32>| -> Vec<u32> {
            for f in facs {
                for &x in *f {
                    cnt[x as usize] ^= 1;
                }
            }
            let mut out = vec![];
            for f in facs {
                for &x in *f {
                    if cnt[x as usize] == 1 {
                        out.push(x);
                        cnt[x as usize] = 0;
                    }
                }
            }
            for f in facs {
                for &x in *f {
                    cnt[x as usize] = 0;
                }
            }
            out
        };
        for r in &fulls {
            cols.push(odd_rows(&[&r.factors], &mut cnt));
        }
        for &(a, b) in &pairs {
            cols.push(odd_rows(&[&partials[a].factors, &partials[b].factors], &mut cnt));
        }
        let tla = Instant::now();
        let deps = linalg::find_dependencies(nrows, &cols);
        if verbose {
            eprintln!(
                "  linalg {:.2}s: {} deps from {}x{}",
                tla.elapsed().as_secs_f64(),
                deps.len(),
                nrows,
                ncols
            );
        }
        // square roots
        let nint = n.clone();
        let mut exps = vec![0u32; nrows];
        for dep in &deps {
            if Instant::now() >= deadline {
                return None;
            }
            let mut x = BigUint::one();
            let mut lpprod = BigUint::one();
            for e in exps.iter_mut() {
                *e = 0;
            }
            for &c in dep {
                if c < fulls.len() {
                    let r = &fulls[c];
                    x = (x * &r.y) % &nint;
                    for &f in &r.factors {
                        exps[f as usize] += 1;
                    }
                } else {
                    let (a, b) = pairs[c - fulls.len()];
                    for r in [&partials[a], &partials[b]] {
                        x = (x * &r.y) % &nint;
                        for &f in &r.factors {
                            exps[f as usize] += 1;
                        }
                    }
                    lpprod = (lpprod * BigUint::from(partials[a].lp)) % &nint;
                }
            }
            if exps.iter().any(|&e| e & 1 == 1) {
                continue;
            }
            let mut y = lpprod;
            let mut acc: u64 = 1;
            for i in 1..nrows {
                let p = ctx.fb[i - 1] as u64;
                for _ in 0..exps[i] / 2 {
                    if acc > u64::MAX / p {
                        y = (y * acc) % &nint;
                        acc = 1;
                    }
                    acc *= p;
                }
            }
            y = (y * acc) % &nint;
            let diff = if x >= y { &x - &y } else { &y - &x };
            let g = diff.gcd(&nint);
            if !g.is_one() && g != nint {
                if verbose {
                    eprintln!("  total {:.2}s", t0.elapsed().as_secs_f64());
                }
                return Some(g);
            }
        }
        extra += 64;
        round += 1;
        if verbose {
            eprintln!("  no factor from deps; collecting more");
        }
    }
}

fn choose_a(ctx: &Ctx, rng: &mut Rng) -> (Vec<usize>, BigUint) {
    let s = ctx.s;
    let range = ctx.q_hi - ctx.q_lo;
    let mut tries = 0;
    loop {
        tries += 1;
        let mut idx: Vec<usize> = Vec::with_capacity(s);
        let mut logp = 0f64;
        let mut ok = true;
        while idx.len() < s - 1 {
            let i = ctx.q_lo + rng.below(range as u64) as usize;
            if idx.contains(&i) || ctx.sqrt[i] == 0 {
                continue;
            }
            idx.push(i);
            logp += (ctx.fb[i] as f64).log2();
            if idx.len() > 64 {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        // choose last prime closest to target/product
        let want = (ctx.log_target_a - logp).exp2();
        let mut best = usize::MAX;
        let mut bestd = f64::MAX;
        let lo = ctx.med_start;
        let hi = ctx.large_start.min(ctx.nfb);
        // binary search
        let pos = ctx.fb[lo..hi].partition_point(|&p| (p as f64) < want) + lo;
        for j in pos.saturating_sub(3).max(lo)..(pos + 3).min(hi) {
            if idx.contains(&j) || ctx.sqrt[j] == 0 {
                continue;
            }
            let d = ((ctx.fb[j] as f64).log2() - want.log2()).abs();
            if d < bestd {
                bestd = d;
                best = j;
            }
        }
        if best == usize::MAX {
            continue;
        }
        if bestd > 0.6 && tries < 1000 {
            continue;
        }
        idx.push(best);
        idx.sort();
        {
            let mut used = ctx.used_a.lock().unwrap();
            let key: Vec<u32> = idx.iter().map(|&i| i as u32).collect();
            if used.contains(&key) && tries < 10000 {
                continue;
            }
            used.insert(key);
        }
        let mut a = BigUint::one();
        for &i in &idx {
            a *= ctx.fb[i];
        }
        return (idx, a);
    }
}

fn worker(ctx: Arc<Ctx>, seed: u64, tx: mpsc::Sender<Rel>, stop: Arc<AtomicBool>) {
    let mut rng = Rng(seed);
    let nfb = ctx.nfb;
    let s = ctx.s;
    let fb = &ctx.fb;
    let logp = &ctx.logp;
    let med = ctx.med_start;
    let large = ctx.large_start;
    let nblocks = ctx.nblocks;
    let interval = nblocks * BS;
    let m = ctx.m;
    let mut r1 = vec![0u32; nfb];
    let mut r2 = vec![0u32; nfb];
    let mut pos1 = vec![0u32; nfb];
    let mut pos2 = vec![0u32; nfb];
    let mut bainv2 = vec![vec![0u32; nfb]; s];
    let mut sieve = vec![0u8; BS + 64];
    // bucket capacity estimate
    let mut exp_hits = 0f64;
    for i in large..nfb {
        exp_hits += 2.0 * BS as f64 / fb[i] as f64;
    }
    let cap = (exp_hits * 1.5) as usize + 4096;
    let mut bdata: Vec<u32> = vec![0u32; (nblocks + 1) * cap];
    let mut blen: Vec<usize> = vec![0usize; nblocks + 1];
    let xl = fb.iter().position(|&p| p as usize >= interval).unwrap_or(nfb).max(large);
    let n_int = BigInt::from(ctx.n.clone());
    let mut cands: Vec<usize> = Vec::with_capacity(64);
    while !stop.load(Ordering::Relaxed) {
        let tm0 = Instant::now();
        let (qidx, a) = choose_a(&ctx, &mut rng);
        let a_int = BigInt::from(a.clone());
        let mut bl: Vec<BigUint> = Vec::with_capacity(s);
        for l in 0..s {
            let q = fb[qidx[l]] as u64;
            let al: BigUint = &a / q;
            let al_mod = (&al % q).to_u64().unwrap();
            let mut g = mulmod(ctx.sqrt[qidx[l]] as u64, inv_mod(al_mod, q), q);
            if g > q / 2 {
                g = q - g;
            }
            bl.push(al * g);
        }
        let mut b: BigInt = BigInt::zero();
        for x in &bl {
            b += BigInt::from(x.clone());
        }
        debug_assert!(((&b * &b - &ctx.kn) % &a_int).is_zero());
        let a_limbs = to_limbs(&a);
        let bl_limbs: Vec<Vec<u32>> = bl.iter().map(to_limbs).collect();
        let b_limbs = to_limbs(b.magnitude());
        let mut is_q = vec![false; 0];
        is_q.resize(nfb, false);
        for &i in &qidx {
            is_q[i] = true;
        }
        for i in 1..nfb {
            let p = fb[i];
            if is_q[i] {
                for l in 0..s {
                    bainv2[l][i] = 0;
                }
                r1[i] = u32::MAX;
                r2[i] = u32::MAX;
                continue;
            }
            let pp = p as u64;
            let amod = mod_limbs(&a_limbs, p) as u64;
            let ainv = inv_mod(amod, pp);
            for l in 0..s {
                let bm = mod_limbs(&bl_limbs[l], p) as u64;
                bainv2[l][i] = ((2 * bm % pp) * ainv % pp) as u32;
            }
            let bmod = mod_limbs(&b_limbs, p) as u64;
            let t = ctx.sqrt[i] as u64;
            let mm = (m as u64) % pp;
            let x1 = (ainv * ((t + pp - bmod) % pp) % pp + mm) % pp;
            let x2 = (ainv * ((2 * pp - t - bmod) % pp) % pp + mm) % pp;
            r1[i] = x1 as u32;
            r2[i] = x2 as u32;
        }
        let npoly = 1usize << (s - 1);
        T_INIT.fetch_add(tm0.elapsed().as_nanos() as u64, Ordering::Relaxed);
        for poly in 0..npoly {
            if stop.load(Ordering::Relaxed) {
                return;
            }
            let mut v = 0usize;
            let mut on = false;
            if poly > 0 {
                v = poly.trailing_zeros() as usize;
                let gray = poly ^ (poly >> 1);
                on = (gray >> v) & 1 == 1;
                let two_bv = BigInt::from(bl[v].clone()) * 2;
                if on {
                    b -= two_bv;
                } else {
                    b += two_bv;
                }
                let d = &bainv2[v];
                if on {
                    for i in 1..large {
                        let p = fb[i];
                        let mut x = r1[i].wrapping_add(d[i]);
                        if x >= p {
                            x = x.wrapping_sub(p);
                        }
                        r1[i] = x;
                        let mut y = r2[i].wrapping_add(d[i]);
                        if y >= p {
                            y = y.wrapping_sub(p);
                        }
                        r2[i] = y;
                    }
                } else {
                    for i in 1..large {
                        let p = fb[i];
                        let x = r1[i];
                        r1[i] = if x >= d[i] { x - d[i] } else { x.wrapping_add(p).wrapping_sub(d[i]) };
                        let y = r2[i];
                        r2[i] = if y >= d[i] { y - d[i] } else { y.wrapping_add(p).wrapping_sub(d[i]) };
                    }
                }
                for &i in &qidx {
                    r1[i] = u32::MAX;
                    r2[i] = u32::MAX;
                }
            }
            let tm1 = Instant::now();
            let c: BigInt = (&b * &b - &ctx.kn) / &a_int;
            STAT_POLY.fetch_add(1, Ordering::Relaxed);
            // bucket fill for large primes
            for l in blen.iter_mut() {
                *l = 0;
            }
            {
                let d = &bainv2[v][..];
                let r1s = &mut r1[..];
                let r2s = &mut r2[..];
                if poly > 0 {
                    let fbl = &fb[large..nfb];
                    let dl = &d[large..nfb];
                    for rr in [&mut r1s[large..nfb], &mut r2s[large..nfb]] {
                        if on {
                            for ((x, &p), &di) in rr.iter_mut().zip(fbl).zip(dl) {
                                let t = *x + di;
                                *x = t.min(t.wrapping_sub(p));
                            }
                        } else {
                            for ((x, &p), &di) in rr.iter_mut().zip(fbl).zip(dl) {
                                let t = x.wrapping_sub(di);
                                *x = t.min(t.wrapping_add(p));
                            }
                        }
                    }
                }
                for i in large..nfb {
                    let p = fb[i];
                    let (x, y) = (r1s[i], r2s[i]);
                    let tag = ((i - large) as u32) << BS_BITS;
                    if i >= xl {
                        // p >= interval: at most one hit per root, branchless
                        let bx = ((x as usize) >> BS_BITS).min(nblocks);
                        let lx = blen[bx];
                        unsafe { *bdata.get_unchecked_mut(bx * cap + lx) = tag | (x & (BS as u32 - 1)); }
                        blen[bx] = lx + (bx < nblocks) as usize;
                        let by = ((y as usize) >> BS_BITS).min(nblocks);
                        let ly = blen[by];
                        unsafe { *bdata.get_unchecked_mut(by * cap + ly) = tag | (y & (BS as u32 - 1)); }
                        blen[by] = ly + (by < nblocks) as usize;
                    } else {
                        let mut x = x as usize;
                        while x < interval {
                            let bx = x >> BS_BITS;
                            let lx = blen[bx];
                            unsafe { *bdata.get_unchecked_mut(bx * cap + lx) = tag | (x & (BS - 1)) as u32; }
                            blen[bx] = lx + 1;
                            x += p as usize;
                        }
                        let mut y = y as usize;
                        while y < interval {
                            let by = y >> BS_BITS;
                            let ly = blen[by];
                            unsafe { *bdata.get_unchecked_mut(by * cap + ly) = tag | (y & (BS - 1)) as u32; }
                            blen[by] = ly + 1;
                            y += p as usize;
                        }
                    }
                }
                for bb in 0..nblocks {
                    assert!(blen[bb] < cap, "bucket overflow");
                }
            }
            T_FILL.fetch_add(tm1.elapsed().as_nanos() as u64, Ordering::Relaxed);
            for i in med..large {
                pos1[i] = r1[i];
                pos2[i] = r2[i];
            }
            for blk in 0..nblocks {
                let tm2 = Instant::now();
                sieve[..BS].fill(0);
                // medium primes
                for i in med..large {
                    let p = fb[i] as usize;
                    let l = logp[i];
                    let mut x = pos1[i] as usize;
                    let mut y = pos2[i] as usize;
                    if x > y {
                        std::mem::swap(&mut x, &mut y);
                    }
                    unsafe {
                        while y < BS {
                            *sieve.get_unchecked_mut(x) += l;
                            *sieve.get_unchecked_mut(y) += l;
                            x += p;
                            y += p;
                        }
                        if x < BS {
                            *sieve.get_unchecked_mut(x) += l;
                            x += p;
                        }
                    }
                    pos1[i] = (x - BS) as u32;
                    pos2[i] = (y - BS) as u32;
                }
                // large primes from bucket
                let bucket = &bdata[blk * cap..blk * cap + blen[blk]];
                for &e in bucket {
                    let idx = (e >> BS_BITS) as usize + large;
                    unsafe {
                        *sieve.get_unchecked_mut((e as usize) & (BS - 1)) += *logp.get_unchecked(idx);
                    }
                }
                // scan
                cands.clear();
                scan(&sieve[..BS], ctx.thresh, &mut cands);
                STAT_CAND.fetch_add(cands.len() as u64, Ordering::Relaxed);
                let tm3 = Instant::now();
                T_SIEVE.fetch_add((tm3 - tm2).as_nanos() as u64, Ordering::Relaxed);
                for &jl in &cands {
                    let j = blk * BS + jl;
                    if let Some(rel) = trial_divide(
                        &ctx, j, jl, &a_int, &b, &c, &qidx, &r1, &r2, bucket, &n_int,
                    ) {
                        STAT_REL.fetch_add(1, Ordering::Relaxed);
                        if tx.send(rel).is_err() {
                            return;
                        }
                    }
                }
                T_TD.fetch_add(tm3.elapsed().as_nanos() as u64, Ordering::Relaxed);
            }
        }
    }
}

#[inline]
fn scan(sieve: &[u8], thresh: u8, out: &mut Vec<usize>) {
    #[cfg(target_arch = "aarch64")]
    unsafe {
        use std::arch::aarch64::*;
        let p = sieve.as_ptr();
        let mut i = 0;
        while i < sieve.len() {
            let a = vld1q_u8(p.add(i));
            let b = vld1q_u8(p.add(i + 16));
            let c = vld1q_u8(p.add(i + 32));
            let d = vld1q_u8(p.add(i + 48));
            let mx = vmaxq_u8(vmaxq_u8(a, b), vmaxq_u8(c, d));
            if vmaxvq_u8(mx) >= thresh {
                for k in i..i + 64 {
                    if *sieve.get_unchecked(k) >= thresh {
                        out.push(k);
                    }
                }
            }
            i += 64;
        }
    }
    #[cfg(not(target_arch = "aarch64"))]
    for (k, &v) in sieve.iter().enumerate() {
        if v >= thresh {
            out.push(k);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn trial_divide(
    ctx: &Ctx,
    j: usize,
    jl: usize,
    a: &BigInt,
    b: &BigInt,
    c: &BigInt,
    qidx: &[usize],
    r1: &[u32],
    r2: &[u32],
    bucket: &[u32],
    n_int: &BigInt,
) -> Option<Rel> {
    let x = j as i64 - ctx.m;
    let xb = BigInt::from(x);
    let ax = a * &xb;
    let y: BigInt = &ax + b;
    let g: BigInt = (&ax + b + b) * &xb + c;
    let mut factors: Vec<u32> = Vec::with_capacity(32);
    if g.sign() == Sign::Minus {
        factors.push(0);
    }
    if g.is_zero() {
        return None;
    }
    let mut limbs = g.magnitude().to_u32_digits();
    let fb = &ctx.fb;
    // p = 2
    while !limbs.is_empty() && limbs[0] & 1 == 0 {
        let mut carry = 0u32;
        for l in limbs.iter_mut().rev() {
            let nc = *l & 1;
            *l = (*l >> 1) | (carry << 31);
            carry = nc;
        }
        while let Some(&0) = limbs.last() {
            limbs.pop();
        }
        factors.push(1);
    }
    for &i in qidx {
        factors.push(i as u32 + 1);
        while try_div_limbs(&mut limbs, fb[i]) {
            factors.push(i as u32 + 1);
        }
    }
    let jj = j as u64;
    for i in 1..ctx.large_start {
        let p = fb[i];
        let jm = (jj - ((jj * ctx.recip[i]) >> 40) * p as u64) as u32;
        if jm == r1[i] || jm == r2[i] {
            while try_div_limbs(&mut limbs, p) {
                factors.push(i as u32 + 1);
            }
        }
    }
    for &e in bucket {
        if (e as usize) & (BS - 1) == jl {
            let i = (e >> BS_BITS) as usize + ctx.large_start;
            while try_div_limbs(&mut limbs, fb[i]) {
                factors.push(i as u32 + 1);
            }
        }
    }
    if limbs.len() > 2 {
        return None;
    }
    let cof: u64 = match limbs.len() {
        0 => 0,
        1 => limbs[0] as u64,
        _ => limbs[0] as u64 | ((limbs[1] as u64) << 32),
    };
    let lp = if cof == 1 {
        1
    } else if cof < ctx.lp_bound {
        cof
    } else {
        return None;
    };
    let ym = y.mod_floor(n_int);
    Some(Rel { y: ym.magnitude().clone(), factors, lp })
}
