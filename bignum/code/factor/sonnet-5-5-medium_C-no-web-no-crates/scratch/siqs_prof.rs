use crate::big::*;
use std::collections::{HashMap, HashSet};
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering as AO};
use std::time::Instant;

const B: u32 = 131072;
const SENT: u32 = 1 << 30;

pub fn primes_upto(n: usize) -> Vec<u32> {
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

pub fn powmod32(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64;
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

fn modinv(a: u32, m: u32) -> u32 {
    let (mut r0, mut r1) = (m as i64, a as i64);
    let (mut t0, mut t1) = (0i64, 1i64);
    while r1 != 0 {
        let q = r0 / r1;
        let r2 = r0 - q * r1;
        r0 = r1;
        r1 = r2;
        let t2 = t0 - q * t1;
        t0 = t1;
        t1 = t2;
    }
    if t0 < 0 {
        t0 += m as i64;
    }
    t0 as u32
}

pub fn sqrt_mod(a: u32, p: u32) -> u32 {
    let (a, p) = (a as u64, p as u64);
    if a == 0 {
        return 0;
    }
    if p % 4 == 3 {
        return powmod32(a, (p + 1) / 4, p) as u32;
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
    let mut m = s;
    let mut c = powmod32(z, q, p);
    let mut t = powmod32(a, q, p);
    let mut r = powmod32(a, (q + 1) / 2, p);
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
    r as u32
}

#[derive(Clone)]
pub struct Rel {
    t: Big,
    f: Vec<(u32, u32)>,
    lps: Vec<u64>,
}

struct Inner {
    full: Vec<Rel>,
    anchors: HashMap<u64, Rel>,
    seen: HashSet<Big>,
    npartial: usize,
}

pub struct Ctx {
    kn: Big,
    n: Big,
    fb: Vec<u32>,
    sq: Vec<u32>,
    lg: Vec<u8>,
    magic: Vec<u64>,
    m: usize,
    nblocks: usize,
    thresh: u8,
    lpbound: u64,
    pmax: u32,
    start: usize,
    log_target: f64,
    target_a: Big,
    s_a: usize,
}

fn getenv_f(name: &str, d: f64) -> f64 {
    std::env::var(name).ok().and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn choose_multiplier(n: &Big) -> u32 {
    let ps = primes_upto(400);
    let ks = [1u32, 3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 29, 31, 33, 35, 37, 39, 41, 43, 47, 51, 53, 55, 57, 59, 61, 65, 67, 69, 71, 73];
    let mut best = (f64::MIN, 1);
    for &k in &ks {
        let kn = mul_small(n, k as u64);
        let mut sc = -0.5 * (k as f64).ln();
        let r8 = (kn[0] & 7) as u32;
        sc += match r8 {
            1 => 2.0 * 2f64.ln(),
            5 => 2f64.ln(),
            _ => 0.5 * 2f64.ln(),
        };
        for &p in ps.iter().skip(1).take(80) {
            let r = rem32(&kn, p);
            if k % p == 0 {
                sc += (p as f64).ln() / p as f64;
            } else if powmod32(r as u64, ((p - 1) / 2) as u64, p as u64) == 1 {
                sc += 2.0 * (p as f64).ln() / (p as f64 - 1.0);
            }
        }
        if sc > best.0 {
            best = (sc, k);
        }
    }
    best.1
}

fn fb_size_for(digits: f64) -> usize {
    let tab: [(f64, f64); 11] = [(20.0, 50.0), (30.0, 120.0), (40.0, 300.0), (50.0, 800.0), (60.0, 1800.0), (70.0, 3500.0), (80.0, 7000.0), (90.0, 14000.0), (100.0, 28000.0), (110.0, 50000.0), (120.0, 90000.0)];
    let mut r = tab[tab.len() - 1].1;
    if digits <= tab[0].0 {
        r = tab[0].1;
    } else {
        for w in tab.windows(2) {
            if digits <= w[1].0 {
                let f = (digits - w[0].0) / (w[1].0 - w[0].0);
                r = (w[0].1.ln() * (1.0 - f) + w[1].1.ln() * f).exp();
                break;
            }
        }
    }
    (r * getenv_f("FBSCALE", 3.0)) as usize
}

fn nblocks_for(digits: f64) -> usize {
    let v = if digits < 90.0 { 1 } else { 2 };
    let v = (v as f64 * getenv_f("MSCALE", 1.0)).round() as usize;
    v.max(1)
}

impl Ctx {
    pub fn new(n: &Big) -> Ctx {
        let k = choose_multiplier(n);
        let kn = mul_small(n, k as u64);
        let digits = log2_big(&kn) * 0.30103;
        let fbn = fb_size_for(digits).min(120000);
        let nblocks = nblocks_for(digits);
        let m = nblocks * B as usize / 2;
        let ps = primes_upto(3_000_000);
        let mut fb = vec![0u32, 2];
        let mut sq = vec![0u32, 0];
        for &p in ps.iter().skip(1) {
            if fb.len() >= fbn {
                break;
            }
            let r = rem32(&kn, p);
            if k % p == 0 {
                fb.push(p);
                sq.push(0);
            } else if powmod32(r as u64, ((p - 1) / 2) as u64, p as u64) == 1 {
                fb.push(p);
                sq.push(sqrt_mod(r, p));
            }
        }
        let lg: Vec<u8> = fb.iter().map(|&p| if p > 1 { (p as f64).log2().round() as u8 } else { 0 }).collect();
        let magic: Vec<u64> = fb.iter().map(|&p| if p > 1 { u64::MAX / p as u64 + 1 } else { 0 }).collect();
        let pmax = *fb.last().unwrap();
        let lpmult = getenv_f("LPMULT", 40.0);
        let lpbound = (pmax as f64 * lpmult) as u64;
        let logmax = log2_big(&kn) / 2.0 - 0.5 + (m as f64).log2();
        let slack = getenv_f("SLACK", 15.0);
        let thresh = (logmax - (lpbound as f64).log2() - slack).max(10.0) as u8;
        let two_kn = mul_small(&kn, 2);
        let sqrt2n = isqrt(&two_kn);
        let target_a = divrem_small(&sqrt2n, m as u64).0;
        let log_target = log2_big(&target_a);
        let s_min = (log_target / (pmax as f64 * 0.5).log2()).ceil() as usize;
        let s_a = ((log_target / getenv_f("SDIV", 11.5)).round() as usize).max(s_min).clamp(3, 14);
        let mut start = 2;
        while start < fb.len() - 1 && (fb[start] as f64) < getenv_f("MINP", 30.0) {
            start += 1;
        }
        Ctx { kn, n: n.clone(), fb, sq, lg, magic, m, nblocks, thresh, lpbound, pmax, start, log_target, target_a, s_a }
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
}

pub struct Shared {
    inner: Mutex<Inner>,
    pub nfull: AtomicUsize,
    pub ncand: AtomicUsize,
    pub nlp: AtomicUsize,
    pub nraw: AtomicUsize,
    pub npoly: AtomicUsize,
    pub stop: AtomicBool,
    pub pause: AtomicBool,
}

impl Shared {
    fn add(&self, ctx: &Ctx, rel: Rel, lp: u64) {
        let mut g = self.inner.lock().unwrap();
        if !g.seen.insert(rel.t.clone()) {
            return;
        }
        if lp == 1 {
            g.full.push(rel);
        } else if let Some(a) = g.anchors.get(&lp) {
            let t = mulmod(&a.t, &rel.t, &ctx.kn);
            let mut f: Vec<(u32, u32)> = Vec::with_capacity(a.f.len() + rel.f.len());
            let (mut i, mut j) = (0, 0);
            while i < a.f.len() || j < rel.f.len() {
                if j >= rel.f.len() || (i < a.f.len() && a.f[i].0 < rel.f[j].0) {
                    f.push(a.f[i]);
                    i += 1;
                } else if i >= a.f.len() || rel.f[j].0 < a.f[i].0 {
                    f.push(rel.f[j]);
                    j += 1;
                } else {
                    f.push((a.f[i].0, a.f[i].1 + rel.f[j].1));
                    i += 1;
                    j += 1;
                }
            }
            let mut lps = a.lps.clone();
            lps.extend_from_slice(&rel.lps);
            lps.push(lp);
            g.full.push(Rel { t, f, lps });
        } else {
            g.anchors.insert(lp, rel);
            g.npartial += 1;
            return;
        }
        self.nfull.store(g.full.len(), AO::Relaxed);
    }
}

fn make_shared() -> Shared {
    Shared {
        inner: Mutex::new(Inner { full: vec![], anchors: HashMap::new(), seen: HashSet::new(), npartial: 0 }),
        nfull: AtomicUsize::new(0),
        ncand: AtomicUsize::new(0),
        nlp: AtomicUsize::new(0),
        nraw: AtomicUsize::new(0),
        npoly: AtomicUsize::new(0),
        stop: AtomicBool::new(false),
        pause: AtomicBool::new(false),
    }
}

fn worker(ctx: &Ctx, sh: &Shared, seed: u64, tid: usize) {
    let mut prof = [0f64; 4];
    let fnum = ctx.fb.len();
    let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
    for _ in 0..10 {
        rng.next();
    }
    let s = ctx.s_a;
    let mut s1 = vec![0u32; fnum];
    let mut s2 = vec![0u32; fnum];
    let mut cur1 = vec![0u32; fnum];
    let mut cur2 = vec![0u32; fnum];
    let mut bainv2: Vec<Vec<u32>> = vec![vec![0u32; fnum]; s];
    let mut in_a = vec![false; fnum];
    let sq0: Vec<usize> = (2..fnum).filter(|&i| ctx.sq[i] == 0).collect();
    let mut arr = vec![0u8; B as usize + 1];
    let idx_a = ctx.fb.partition_point(|&p| p < B);
    let idx_b = ctx.fb.partition_point(|&p| p < B / 2);
    let m = ctx.m as u64;
    let lo_idx = ctx.start.max(2);
    let nsmallidx = fnum;
    while !sh.stop.load(AO::Relaxed) {
        let tp = Instant::now();
        // choose a
        let log_t = ctx.log_target;
        let pc = (log_t / s as f64).exp2();
        let find = |v: f64| -> usize {
            // nearest idx with fb >= v
            let mut lo = lo_idx;
            let mut hi = nsmallidx;
            while lo < hi {
                let mid = (lo + hi) / 2;
                if (ctx.fb[mid] as f64) < v { lo = mid + 1 } else { hi = mid }
            }
            lo
        };
        let lo_r = find(pc / 1.6);
        let hi_r = find(pc * 1.6).max(lo_r + s + 4).min(nsmallidx);
        let lo_r = lo_r.min(hi_r.saturating_sub(s + 4)).max(lo_idx);
        let mut qs: Vec<usize> = vec![];
        let mut ok = false;
        for _try in 0..200 {
            qs.clear();
            let mut sumlog = 0.0;
            while qs.len() < s - 1 {
                let i = lo_r + (rng.next() % (hi_r - lo_r) as u64) as usize;
                if ctx.sq[i] == 0 || qs.contains(&i) {
                    continue;
                }
                qs.push(i);
                sumlog += (ctx.fb[i] as f64).log2();
            }
            let need = (log_t - sumlog).exp2();
            let mut i = find(need);
            if i >= nsmallidx {
                i = nsmallidx - 1;
            }
            let mut best = i;
            if i > lo_idx && (need - ctx.fb[i - 1] as f64).abs() < (ctx.fb[i] as f64 - need).abs() {
                best = i - 1;
            }
            for cand in [best, best + 1, best.wrapping_sub(1)] {
                if cand >= lo_idx && cand < nsmallidx && ctx.sq[cand] != 0 && !qs.contains(&cand) {
                    let r = ctx.fb[cand] as f64 / need;
                    if r > 0.8 && r < 1.25 {
                        qs.push(cand);
                        ok = true;
                        break;
                    }
                }
            }
            if ok {
                break;
            }
        }
        if !ok {
            continue;
        }
        let qv: Vec<u32> = qs.iter().map(|&i| ctx.fb[i]).collect();
        let mut a: Big = vec![1];
        for &q in &qv {
            a = mul_small(&a, q as u64);
        }
        // B_j
        let mut gj = vec![0u32; s];
        let mut bj: Vec<Big> = Vec::with_capacity(s);
        let mut sum_b: Big = vec![];
        for j in 0..s {
            let mut ao: Big = vec![1];
            for (k2, &q) in qv.iter().enumerate() {
                if k2 != j {
                    ao = mul_small(&ao, q as u64);
                }
            }
            let qj = qv[j];
            let am = rem32(&ao, qj);
            let inv = modinv(am, qj);
            let mut g = (ctx.sq[qs[j]] as u64 * inv as u64 % qj as u64) as u32;
            if g > qj / 2 {
                g = qj - g;
            }
            gj[j] = g;
            let b = mul_small(&ao, g as u64);
            sum_b = add_big(&sum_b, &b);
            bj.push(b);
        }
        for &i in &qs {
            in_a[i] = true;
        }
        // root tables
        let mut qinv = vec![0u32; s];
        for i in 2..fnum {
            let p = ctx.fb[i];
            if in_a[i] {
                for j in 0..s {
                    bainv2[j][i] = 0;
                }
                s1[i] = 0;
                s2[i] = 0;
                continue;
            }
            let p64 = p as u64;
            let mut ainv = 1u64;
            let mut sumb = 0u64;
            for j in 0..s {
                let qi = modinv(qv[j] % p, p);
                qinv[j] = qi;
                ainv = ainv * qi as u64 % p64;
                let bi = gj[j] as u64 % p64 * qi as u64 % p64;
                sumb += bi;
                let b2 = bi * 2 % p64;
                bainv2[j][i] = b2 as u32;
            }
            sumb %= p64;
            let r = ctx.sq[i] as u64 * ainv % p64;
            let moff = m % p64;
            let x1 = (r + p64 - sumb + moff) % p64;
            let x2 = (p64 - r + p64 - sumb + moff) % p64;
            s1[i] = x1 as u32;
            s2[i] = x2 as u32;
        }
        prof[0] += tp.elapsed().as_secs_f64();
        let a_m = mul_small(&a, m);
        let mut tsum: Big = vec![];
        let npoly = 1usize << (s - 1);
        let mut local: Vec<(Rel, u64)> = vec![];
        for k in 0..npoly {
            if sh.stop.load(AO::Relaxed) {
                break;
            }
            while sh.pause.load(AO::Relaxed) && !sh.stop.load(AO::Relaxed) {
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
            sh.npoly.fetch_add(1, AO::Relaxed);
            cur1[2..fnum].copy_from_slice(&s1[2..fnum]);
            cur2[2..fnum].copy_from_slice(&s2[2..fnum]);
            for &i in &qs {
                cur1[i] = SENT;
                cur2[i] = SENT;
            }
            for &i in &sq0 {
                cur2[i] = SENT;
            }
            let two_t = shl_bits(&tsum, 1);
            let v = add_big(&two_t, &a_m);
            for blk in 0..ctx.nblocks {
                let tp = Instant::now();
                arr.fill(0);
                unsafe {
                    for i in ctx.start..idx_b {
                        let p = *ctx.fb.get_unchecked(i);
                        let l = *ctx.lg.get_unchecked(i);
                        let mut x = *cur1.get_unchecked(i);
                        while x < B {
                            *arr.get_unchecked_mut(x as usize) += l;
                            x += p;
                        }
                        *cur1.get_unchecked_mut(i) = x - B;
                        let mut y = *cur2.get_unchecked(i);
                        while y < B {
                            *arr.get_unchecked_mut(y as usize) += l;
                            y += p;
                        }
                        *cur2.get_unchecked_mut(i) = y - B;
                    }
                    for i in idx_b.max(ctx.start)..idx_a {
                        let p = *ctx.fb.get_unchecked(i);
                        let l = *ctx.lg.get_unchecked(i);
                        let mut x = *cur1.get_unchecked(i);
                        let mut y = *cur2.get_unchecked(i);
                        for _ in 0..2 {
                            let cx = x < B;
                            let cy = y < B;
                            *arr.get_unchecked_mut(if cx { x } else { B } as usize) += l;
                            *arr.get_unchecked_mut(if cy { y } else { B } as usize) += l;
                            x += if cx { p } else { 0 };
                            y += if cy { p } else { 0 };
                        }
                        *cur1.get_unchecked_mut(i) = x - B;
                        *cur2.get_unchecked_mut(i) = y - B;
                    }
                    for i in idx_a.max(ctx.start)..fnum {
                        let p = *ctx.fb.get_unchecked(i);
                        let l = *ctx.lg.get_unchecked(i);
                        let x = *cur1.get_unchecked(i);
                        let y = *cur2.get_unchecked(i);
                        let cx = x < B;
                        let cy = y < B;
                        *arr.get_unchecked_mut(if cx { x } else { B } as usize) += l;
                        *arr.get_unchecked_mut(if cy { y } else { B } as usize) += l;
                        *cur1.get_unchecked_mut(i) = x + if cx { p } else { 0 } - B;
                        *cur2.get_unchecked_mut(i) = y + if cy { p } else { 0 } - B;
                    }
                }
                prof[1] += tp.elapsed().as_secs_f64();
                let tp = Instant::now();
                let th = ctx.thresh;
                for (ci, chunk) in arr[..B as usize].chunks_exact(64).enumerate() {
                    let mx = chunk.iter().fold(0u8, |a, &b| a.max(b));
                    if mx >= th {
                        for (o, &val) in chunk.iter().enumerate() {
                            if val >= th {
                                let gi = blk * B as usize + ci * 64 + o;
                                sh.ncand.fetch_add(1, AO::Relaxed);
                                if let Some(r) = ctx.verify(gi, &a, &qs, &sum_b, &v, &s1, &s2) {
                                    local.push(r);
                                }
                            }
                        }
                    }
                }
                prof[2] += tp.elapsed().as_secs_f64();
            }
            if !local.is_empty() {
                sh.nraw.fetch_add(local.len(), AO::Relaxed);
                for (r, lp) in local.drain(..) {
                    if lp > 1 {
                        sh.nlp.fetch_add(1, AO::Relaxed);
                    }
                    sh.add(ctx, r, lp);
                }
            }
            let tp = Instant::now();
            // next polynomial (gray code)
            if k + 1 < npoly {
                let kk = k + 1;
                let j = kk.trailing_zeros() as usize;
                let gray = kk ^ (kk >> 1);
                let up = (gray >> j) & 1 == 1;
                let bj2 = &bainv2[j];
                if up {
                    for (((a, b), &p), &d) in s1[2..].iter_mut().zip(s2[2..].iter_mut()).zip(ctx.fb[2..].iter()).zip(bj2[2..].iter()) {
                        let x = *a + d;
                        *a = x.min(x.wrapping_sub(p));
                        let y = *b + d;
                        *b = y.min(y.wrapping_sub(p));
                    }
                    tsum = add_big(&tsum, &bj[j]);
                } else {
                    for (((a, b), &p), &d) in s1[2..].iter_mut().zip(s2[2..].iter_mut()).zip(ctx.fb[2..].iter()).zip(bj2[2..].iter()) {
                        let x = *a + p - d;
                        *a = x.min(x.wrapping_sub(p));
                        let y = *b + p - d;
                        *b = y.min(y.wrapping_sub(p));
                    }
                    tsum = sub_big(&tsum, &bj[j]);
                }
            }
            prof[3] += tp.elapsed().as_secs_f64();
        }
        for &i in &qs {
            in_a[i] = false;
        }
    }
    if tid == 0 && std::env::var("VERBOSE").is_ok() {
        eprintln!("prof setup {:.2} sieve {:.2} scan+verify {:.2} update {:.2}", prof[0], prof[1], prof[2], prof[3]);
    }
}

impl Ctx {
    fn verify(&self, gi: usize, a: &Big, qs: &[usize], sum_b: &Big, v: &Big, s1: &[u32], s2: &[u32]) -> Option<(Rel, u64)> {
        let w = add_big(sum_b, &mul_small(a, gi as u64));
        let t = if cmp_big(&w, v) != std::cmp::Ordering::Less { sub_big(&w, v) } else { sub_big(v, &w) };
        let t2 = mul_big(&t, &t);
        let neg = cmp_big(&t2, &self.kn) == std::cmp::Ordering::Less;
        let mut pq = if neg { sub_big(&self.kn, &t2) } else { sub_big(&t2, &self.kn) };
        for &qi in qs {
            let (q, r) = div32(&pq, self.fb[qi]);
            debug_assert!(r == 0);
            pq = q;
        }
        if pq.is_empty() {
            return None;
        }
        let mut f: Vec<(u32, u32)> = vec![];
        if neg {
            f.push((0, 1));
        }
        // power of two
        let mut tz = 0usize;
        for &l in pq.iter() {
            if l == 0 { tz += 64 } else { tz += l.trailing_zeros() as usize; break; }
        }
        if tz > 0 {
            pq = shr_bits(&pq, tz);
            f.push((1, tz as u32));
        }
        let gi32 = gi as u32;
        let fnum = self.fb.len();
        for i in 2..fnum {
            if pq.len() == 1 && pq[0] == 1 {
                break;
            }
            let p = self.fb[i];
            let lowbits = self.magic[i].wrapping_mul(gi32 as u64);
            let r = ((lowbits as u128 * p as u128) >> 64) as u32;
            if r == s1[i] || r == s2[i] {
                if qs.contains(&i) {
                    continue;
                }
                let mut e = 0;
                loop {
                    let (q, rem) = div32(&pq, p);
                    if rem == 0 {
                        pq = q;
                        e += 1;
                    } else {
                        break;
                    }
                }
                if e > 0 {
                    f.push((i as u32, e));
                }
            }
        }
        for &qi in qs {
            let q = self.fb[qi];
            let mut e = 0;
            loop {
                let (qq, rem) = div32(&pq, q);
                if rem == 0 {
                    pq = qq;
                    e += 1;
                } else {
                    break;
                }
            }
            f.push((qi as u32, e + 1));
        }
        f.sort();
        let lp;
        if pq.len() == 1 && pq[0] == 1 {
            lp = 1;
        } else if pq.len() == 1 && pq[0] <= self.lpbound && pq[0] > self.pmax as u64 {
            lp = pq[0];
        } else {
            return None;
        }
        Some((Rel { t, f, lps: vec![] }, lp))
    }
}

fn dense_solve(ctx: &Ctx, rels: &[Rel], nthreads: usize) -> Option<Big> {
    let ncol = ctx.fb.len();
    let nr = rels.len();
    let rows: Vec<Vec<u32>> = rels.iter().map(|r| r.f.iter().filter(|&&(_, e)| e & 1 == 1).map(|&(i, _)| i).collect()).collect();
    let mut cnt = vec![0u32; ncol];
    let mut colrows: Vec<Vec<u32>> = vec![vec![]; ncol];
    for (ri, r) in rows.iter().enumerate() {
        for &c in r {
            cnt[c as usize] += 1;
            colrows[c as usize].push(ri as u32);
        }
    }
    let mut alive = vec![true; nr];
    let mut stack: Vec<u32> = (0..ncol as u32).filter(|&c| cnt[c as usize] == 1).collect();
    while let Some(c) = stack.pop() {
        let c = c as usize;
        if cnt[c] != 1 {
            continue;
        }
        let ri = *colrows[c].iter().find(|&&r| alive[r as usize]).unwrap() as usize;
        alive[ri] = false;
        for &c2 in &rows[ri] {
            cnt[c2 as usize] -= 1;
            if cnt[c2 as usize] == 1 {
                stack.push(c2);
            }
        }
    }
    let ridx: Vec<usize> = (0..nr).filter(|&i| alive[i]).collect();
    let mut cmap = vec![u32::MAX; ncol];
    let mut nc = 0usize;
    for c in 0..ncol {
        if cnt[c] > 0 {
            cmap[c] = nc as u32;
            nc += 1;
        }
    }
    let r = ridx.len();
    if std::env::var("VERBOSE").is_ok() {
        eprintln!("   matrix {} x {} (from {} x {})", r, nc, nr, ncol);
    }
    if r <= nc {
        return None;
    }
    // equations: one per live column; unknowns: live relations
    let mut pos = vec![u32::MAX; nr];
    for (k, &ri) in ridx.iter().enumerate() {
        pos[ri] = k as u32;
    }
    let w = (r + 63) / 64;
    let mut mat = vec![0u64; nc * w];
    for c in 0..ncol {
        if cnt[c] > 0 {
            let row = &mut mat[cmap[c] as usize * w..(cmap[c] as usize + 1) * w];
            for &ri in &colrows[c] {
                let p = pos[ri as usize];
                if p != u32::MAX {
                    row[p as usize / 64] ^= 1u64 << (p % 64);
                }
            }
        }
    }
    let (used, pcols) = gf2_echelon(&mut mat, nc, r, w, nthreads);
    let mut is_piv = vec![false; r];
    for &c in &pcols {
        is_piv[c] = true;
    }
    let mut tried = 0;
    for f in 0..r {
        if is_piv[f] {
            continue;
        }
        let mut y = vec![0u64; w];
        y[f / 64] |= 1u64 << (f % 64);
        for t in (0..used).rev() {
            let row = &mat[t * w..(t + 1) * w];
            let mut par = 0u32;
            for x in 0..w {
                par ^= (row[x] & y[x]).count_ones() & 1;
            }
            if par & 1 == 1 {
                let c = pcols[t];
                y[c / 64] |= 1u64 << (c % 64);
            }
        }
        let dep: Vec<usize> = (0..r).filter(|&k| y[k / 64] >> (k % 64) & 1 == 1).map(|k| ridx[k]).collect();
        if let Some(fct) = try_dep(ctx, rels, &dep) {
            return Some(fct);
        }
        tried += 1;
        if tried >= 60 {
            break;
        }
    }
    None
}

// Forward elimination over GF(2) with 8-column Four-Russians strips.
// Returns (number of pivot rows, pivot column of each).
fn gf2_echelon(mat: &mut [u64], nrows: usize, ncols: usize, w: usize, nthreads: usize) -> (usize, Vec<usize>) {
    let mut used = 0usize;
    let mut pcols: Vec<usize> = vec![];
    let mut c0 = 0usize;
    let mut table: Vec<u64> = vec![];
    while c0 < ncols && used < nrows {
        let w0 = c0 / 64;
        let sh = (c0 % 64) as u32;
        let strip = |mat: &[u64], i: usize| -> u8 { ((mat[i * w + w0] >> sh) & 0xff) as u8 };
        let mut pivs: Vec<(u8, usize)> = vec![]; // (reduced byte, pivot bit)
        let mut i = used;
        while i < nrows && pivs.len() < 8 {
            let mut b = strip(mat, i);
            let mut applied = 0u32;
            for (t, &(pb, pj)) in pivs.iter().enumerate() {
                if (b >> pj) & 1 == 1 {
                    b ^= pb;
                    applied |= 1 << t;
                }
            }
            if b != 0 {
                let t = pivs.len();
                let dst = used + t;
                if dst != i {
                    for x in 0..w {
                        mat.swap(i * w + x, dst * w + x);
                    }
                }
                for s in 0..t {
                    if (applied >> s) & 1 == 1 {
                        let (lo, hi) = mat.split_at_mut(dst * w);
                        let src = &lo[(used + s) * w..(used + s + 1) * w];
                        for x in w0..w {
                            hi[x] ^= src[x];
                        }
                    }
                }
                pivs.push((b, b.trailing_zeros() as usize));
            }
            i += 1;
        }
        let m = pivs.len();
        if m > 0 {
            // RREF among the pivots
            for t in 0..m {
                for s in 0..m {
                    if s != t && (pivs[s].0 >> pivs[t].1) & 1 == 1 {
                        let (a, b) = (used + s, used + t);
                        let (lo, hi, a_is_lo) = if a < b { let (l, h) = mat.split_at_mut(b * w); (l, h, true) } else { let (l, h) = mat.split_at_mut(a * w); (l, h, false) };
                        if a_is_lo {
                            let dst = &mut lo[a * w..(a + 1) * w];
                            let src = &hi[..w];
                            for x in w0..w {
                                dst[x] ^= src[x];
                            }
                        } else {
                            let dst = &mut hi[..w];
                            let src = &lo[b * w..(b + 1) * w];
                            for x in w0..w {
                                dst[x] ^= src[x];
                            }
                        }
                        pivs[s].0 ^= pivs[t].0;
                    }
                }
            }
            for t in 0..m {
                pcols.push(c0 + pivs[t].1);
            }
            // table over pivot subsets
            let tw = w - w0;
            table.clear();
            table.resize((1usize << m) * tw, 0);
            for idx in 1..(1usize << m) {
                let low = idx.trailing_zeros() as usize;
                let prev = idx & (idx - 1);
                let src = &mat[(used + low) * w + w0..(used + low + 1) * w];
                let (tl, th) = table.split_at_mut(idx * tw);
                let pr = &tl[prev * tw..(prev + 1) * tw];
                for x in 0..tw {
                    th[x] = pr[x] ^ src[x];
                }
            }
            let mut comp = [0u8; 256];
            for b in 0..256usize {
                let mut idx = 0u8;
                for t in 0..m {
                    if (b >> pivs[t].1) & 1 == 1 {
                        idx |= 1 << t;
                    }
                }
                comp[b] = idx;
            }
            let start = used + m;
            let nrem = nrows - start;
            let (_, rest) = mat.split_at_mut(start * w);
            let work = nrem * tw;
            let nt = if work > 400_000 { nthreads.min(nrem / 64).max(1) } else { 1 };
            let table_ref = &table;
            let comp_ref = &comp;
            let run = |chunk: &mut [u64]| {
                for row in chunk.chunks_exact_mut(w) {
                    let b = ((row[w0] >> sh) & 0xff) as usize;
                    let idx = comp_ref[b] as usize;
                    if idx != 0 {
                        let tr = &table_ref[idx * tw..(idx + 1) * tw];
                        for x in 0..tw {
                            row[w0 + x] ^= tr[x];
                        }
                    }
                }
            };
            if nt <= 1 {
                run(rest);
            } else {
                let per = (nrem + nt - 1) / nt;
                std::thread::scope(|sc| {
                    for ch in rest.chunks_mut(per * w) {
                        let run = &run;
                        sc.spawn(move || run(ch));
                    }
                });
            }
            used += m;
        }
        c0 += 8;
    }
    (used, pcols)
}

fn try_dep(ctx: &Ctx, rels: &[Rel], dep: &[usize]) -> Option<Big> {
    let mut x: Big = vec![1];
    let mut cnt = vec![0u64; ctx.fb.len()];
    let mut lpp: Big = vec![1];
    for &ri in dep {
        let r = &rels[ri];
        x = mulmod(&x, &r.t, &ctx.kn);
        for &(i, e) in &r.f {
            cnt[i as usize] += e as u64;
        }
        for &lp in &r.lps {
            lpp = mulmod(&lpp, &from_u64(lp), &ctx.kn);
        }
    }
    let mut y = lpp;
    for i in 0..cnt.len() {
        if cnt[i] == 0 {
            continue;
        }
        if cnt[i] & 1 == 1 {
            return None;
        }
        if i == 0 {
            continue;
        }
        let pw = powmod_small(&from_u64(ctx.fb[i] as u64), cnt[i] / 2, &ctx.kn);
        y = mulmod(&y, &pw, &ctx.kn);
    }
    for sign in 0..2 {
        let d = if sign == 0 {
            if cmp_big(&x, &y) != std::cmp::Ordering::Less { sub_big(&x, &y) } else { sub_big(&y, &x) }
        } else {
            add_big(&x, &y)
        };
        if d.is_empty() {
            continue;
        }
        let g = gcd_big(&d, &ctx.n);
        if g.len() > 0 && !(g.len() == 1 && g[0] == 1) && cmp_big(&g, &ctx.n) != std::cmp::Ordering::Equal {
            return Some(g);
        }
    }
    None
}

pub fn siqs(n: &Big, deadline: Instant, nthreads: usize) -> Option<Big> {
    let ctx = Ctx::new(n);
    let sh = make_shared();
    let verbose = std::env::var("VERBOSE").is_ok();
    let t0 = Instant::now();
    if verbose {
        eprintln!("kn bits {} fb {} pmax {} M {} s {} thresh {} lp {}", bits(&ctx.kn), ctx.fb.len(), ctx.pmax, ctx.m, ctx.s_a, ctx.thresh, ctx.lpbound);
    }
    let nthreads = std::env::var("NT").ok().and_then(|s| s.parse().ok()).unwrap_or(nthreads);
    let result = std::thread::scope(|sc| {
        for t in 0..nthreads {
            let ctx = &ctx;
            let sh = &sh;
            sc.spawn(move || worker(ctx, sh, 12345 + t as u64 * 7919 + Instant::now().elapsed().as_nanos() as u64, t));
        }
        let ncols = ctx.fb.len();
        let mut target = ncols + 30;
        let mut res = None;
        loop {
            if Instant::now() >= deadline {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
            if verbose && t0.elapsed().as_millis() % 1000 < 12 {
                eprintln!("[{:.1}s] poly {} full {} cand {} raw {} lp {}", t0.elapsed().as_secs_f64(), sh.npoly.load(AO::Relaxed), sh.nfull.load(AO::Relaxed), sh.ncand.load(AO::Relaxed), sh.nraw.load(AO::Relaxed), sh.nlp.load(AO::Relaxed));
            }
            let nf = sh.nfull.load(AO::Relaxed);
            if nf >= target {
                let rels: Vec<Rel> = sh.inner.lock().unwrap().full.clone();
                if verbose {
                    eprintln!("[{:.1}s] LA with {} rels (cand {} raw {} lp {})", t0.elapsed().as_secs_f64(), rels.len(), sh.ncand.load(AO::Relaxed), sh.nraw.load(AO::Relaxed), sh.nlp.load(AO::Relaxed));
                }
                sh.pause.store(true, AO::Relaxed);
                let tla = Instant::now();
                let fres = dense_solve(&ctx, &rels, nthreads);
                if verbose {
                    eprintln!("   LA took {:.2}s ok={}", tla.elapsed().as_secs_f64(), fres.is_some());
                }
                sh.pause.store(false, AO::Relaxed);
                if let Some(f) = fres {
                    res = Some(f);
                    break;
                }
                target = rels.len() + ncols / 40 + 10;
            }
        }
        sh.stop.store(true, AO::Relaxed);
        res
    });
    if verbose {
        eprintln!("[{:.1}s] done, full {} cand {} raw {}", t0.elapsed().as_secs_f64(), sh.nfull.load(AO::Relaxed), sh.ncand.load(AO::Relaxed), sh.nraw.load(AO::Relaxed));
    }
    result
}
