use std::io::{self, BufRead, Write, BufWriter};
use std::time::{Duration, Instant};
use std::sync::{Arc, atomic::{AtomicBool, AtomicU64, Ordering}};
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
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    *state = x; x
}

#[inline(always)]
fn widening_mul64(a: u64, b: u64) -> (u64, u64) {
    let f = (a as u128) * (b as u128);
    (f as u64, (f >> 64) as u64)
}

#[inline(always)]
fn mulmod64(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

fn powmod64(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64; b %= m;
    while e > 0 { if e&1==1 { r=mulmod64(r,b,m); } b=mulmod64(b,b,m); e>>=1; }
    r
}

// ============================================================
// Montgomery multiplication for u128 (2 x 64-bit words, CIOS)
// ============================================================

fn mont_n_prime(n: u64) -> u64 {
    let mut x: u64 = 1;
    for _ in 0..6 { x = x.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(x))); }
    0u64.wrapping_sub(x)
}

#[inline]
fn mont_mul_128(a: u128, b: u128, n: u128, n_prime: u64) -> u128 {
    let a0=a as u64; let a1=(a>>64) as u64;
    let b0=b as u64; let b1=(b>>64) as u64;
    let n0=n as u64; let n1=(n>>64) as u64;
    let mut t0=0u64; let mut t1=0u64; let mut t2=0u64; let mut t3=0u64;

    macro_rules! madd { ($t:expr,$a:expr,$b:expr,$c:expr) => {{
        let (lo,hi)=widening_mul64($a,$b);
        let (s1,o1)=$t.overflowing_add(lo);
        let (s2,o2)=s1.overflowing_add($c);
        $t=s2; hi.wrapping_add(o1 as u64).wrapping_add(o2 as u64)
    }}; }

    { let mut c=madd!(t0,a0,b0,0); c=madd!(t1,a0,b1,c); t2=t2.wrapping_add(c);
      let m=t0.wrapping_mul(n_prime);
      let mut c2=madd!(t0,m,n0,0); c2=madd!(t1,m,n1,c2); t2=t2.wrapping_add(c2); }
    { let mut c=madd!(t1,a1,b0,0); c=madd!(t2,a1,b1,c); t3=t3.wrapping_add(c);
      let m=t1.wrapping_mul(n_prime);
      let mut c2=madd!(t1,m,n0,0); c2=madd!(t2,m,n1,c2); t3=t3.wrapping_add(c2); }

    let r=(t2 as u128)|((t3 as u128)<<64);
    if r>=n { r-n } else { r }
}

struct MontCtx128 { n: u128, np: u64, r2: u128 }
impl MontCtx128 {
    fn new(n: u128) -> Self {
        let np = mont_n_prime(n as u64);
        let mut r2 = 1u128;
        for _ in 0..256 { r2 = r2.wrapping_add(r2); if r2>=n { r2-=n; } }
        Self { n, np, r2 }
    }
    #[inline] fn to_mont(&self, a: u128) -> u128 { mont_mul_128(a%self.n,self.r2,self.n,self.np) }
    #[inline] fn from_mont(&self, a: u128) -> u128 { mont_mul_128(a,1,self.n,self.np) }
    #[inline] fn mul(&self, a: u128, b: u128) -> u128 { mont_mul_128(a,b,self.n,self.np) }
    #[inline] fn add(&self, a: u128, b: u128) -> u128 { let s=a.wrapping_add(b); if s>=self.n {s-self.n} else {s} }
    #[inline] fn sub(&self, a: u128, b: u128) -> u128 { if a>=b {a-b} else {self.n-b+a} }
}

// ============================================================
// Primality tests
// ============================================================

fn is_prime_u128(n: u128) -> bool {
    if n<2 {return false;} if n==2||n==3 {return true;}
    if n&1==0||n%3==0 {return false;} if n<9 {return true;}
    let mut d=n-1; let mut r=0u32;
    while d&1==0 { d>>=1; r+=1; }
    let witnesses: &[u128] = &[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47];
    if n>(1u128<<64) {
        let ctx=MontCtx128::new(n);
        let one_m=ctx.to_mont(1); let nm1_m=ctx.to_mont(n-1);
        'outer: for &a in witnesses {
            if a>=n {continue;}
            let a_m=ctx.to_mont(a);
            let mut x={let mut b=a_m;let mut e=d;let mut res=one_m;
                while e>0{if e&1==1{res=ctx.mul(res,b);}b=ctx.mul(b,b);e>>=1;}res};
            if x==one_m||x==nm1_m {continue;}
            for _ in 0..r-1 { x=ctx.mul(x,x); if x==nm1_m {continue 'outer;} }
            return false;
        }
        return true;
    }
    let pm=|mut b:u128,mut e:u128,m:u128|->u128{let mut r=1u128;b%=m;while e>0{if e&1==1{r=(r*b)%m;}b=(b*b)%m;e>>=1;}r};
    'outer: for &a in witnesses {
        if a>=n {continue;}
        let mut x=pm(a,d,n);
        if x==1||x==n-1 {continue;}
        for _ in 0..r-1 { x=(x*x)%n; if x==n-1 {continue 'outer;} }
        return false;
    }
    true
}

fn is_prime_big(n: &BigUint) -> bool {
    if let Some(v)=n.to_u128() {return is_prime_u128(v);}
    let one=BigUint::one(); let two=BigUint::from(2u64);
    if n%&two==BigUint::zero() {return false;}
    let nm1=n-&one; let mut d=nm1.clone(); let mut r=0u32;
    while &d%&two==BigUint::zero() { d>>=1; r+=1; }
    let witnesses=[2u64,3,5,7,11,13,17,19,23,29,31,37];
    'outer: for a in witnesses {
        let ab=BigUint::from(a); if &ab>=n {continue;}
        let mut x=ab.modpow(&d,n);
        if x==one||x==nm1 {continue;}
        for _ in 0..r-1 { x=x.modpow(&two,n); if x==nm1 {continue 'outer;} }
        return false;
    }
    true
}

// ============================================================
// Pollard rho (u128 Montgomery path)
// ============================================================

fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b!=0 { let t=b; b=a%b; a=t; } a
}

fn pollard_brent_u128(n: u128, c_val: u128, start: u128, ctx: &MontCtx128) -> Option<u128> {
    let c=ctx.to_mont(c_val);
    let mut y=ctx.to_mont(start);
    let one_m=ctx.to_mont(1);
    let mut r:u64=1; let mut q=one_m;
    let mut x=y; let mut ys=y; let mut d;
    macro_rules! step { ($v:expr) => { ctx.add(ctx.mul($v,$v),c) }; }
    loop {
        x=y; for _ in 0..r { y=step!(y); }
        let mut k:u64=0; d=1u128;
        while k<r && d==1 {
            ys=y; let steps=128u64.min(r-k);
            for _ in 0..steps {
                y=step!(y);
                let diff=if y>=x{y-x}else{x-y};
                if diff==0 {break;}
                q=ctx.mul(q,diff);
                if q==0 {q=one_m;}
            }
            d=gcd128(ctx.from_mont(q),n); k+=steps;
        }
        if d!=1 {break;}
        r*=2; if r>(1u64<<28) {return None;}
    }
    if d==n {
        d=1;
        loop { ys=step!(ys); let diff=if ys>=x{ys-x}else{x-ys}; if diff==0{return None;}
               d=gcd128(ctx.from_mont(diff),n); if d!=1{break;} }
        if d==n {return None;}
    }
    if d!=0&&d!=1&&d!=n {Some(d)} else {None}
}

fn factor_u128_parallel(n: u128) -> Option<(u128, u128)> {
    if n&1==0 {return Some((2,n/2));}
    for p in [3u128,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97] {
        if n==p {return None;} if n%p==0 {return Some((p,n/p));}
    }
    let mut i=101u128;
    while i<1_000_000 && i*i<=n {
        if n%i==0 {return Some((i,n/i));} if n%(i+2)==0 {return Some((i+2,n/(i+2)));}
        i+=6;
    }
    if i*i>n {return None;}
    if is_prime_u128(n) {return None;}
    let ctx=Arc::new(MontCtx128::new(n));
    let stopped=Arc::new(AtomicBool::new(false));
    let (tx,rx)=mpsc::channel::<u128>();
    for t in 0..8usize {
        let tx=tx.clone(); let stopped=stopped.clone(); let ctx=ctx.clone();
        let mut seed:u64=0xdeadbeef1234abcd^(n as u64)^(t as u64*0x9e3779b97f4a7c15);
        xorshift64(&mut seed);
        thread::spawn(move || {
            let mut rng=seed; let n=ctx.n;
            loop {
                if stopped.load(Ordering::Relaxed) {return;}
                let c=(xorshift64(&mut rng) as u128)%(n-2)+1;
                let start=(xorshift64(&mut rng) as u128)%(n-2)+2;
                if let Some(f)=pollard_brent_u128(n,c,start,&ctx) {
                    let _ =tx.send(f); stopped.store(true,Ordering::Relaxed); return;
                }
            }
        });
    }
    drop(tx);
    rx.recv().ok().map(|f| (f.min(n/f),f.max(n/f)))
}

// ============================================================
// Fixed-width k-limb Montgomery arithmetic for ECM
// Supports k = 3..=6 limbs (192..384 bits)
// ============================================================

const MAX_LIMBS: usize = 6;

#[derive(Clone, Copy, Debug)]
struct LimbN {
    d: [u64; MAX_LIMBS],
    k: usize,
}

impl LimbN {
    fn zero(k: usize) -> Self { Self { d: [0; MAX_LIMBS], k } }
    fn is_zero(&self) -> bool { self.d[..self.k].iter().all(|&x| x == 0) }

    fn from_biguint(b: &BigUint, k: usize) -> Self {
        let mut s = Self::zero(k);
        for (i, &limb) in b.to_u64_digits().iter().take(k).enumerate() {
            s.d[i] = limb;
        }
        s
    }

    fn to_biguint(&self) -> BigUint {
        BigUint::from_slice(&{
            let mut v: Vec<u32> = Vec::new();
            for i in 0..self.k {
                v.push(self.d[i] as u32);
                v.push((self.d[i] >> 32) as u32);
            }
            v
        })
    }

    // Compare: -1, 0, 1
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for i in (0..self.k).rev() {
            if self.d[i] < other.d[i] { return std::cmp::Ordering::Less; }
            if self.d[i] > other.d[i] { return std::cmp::Ordering::Greater; }
        }
        std::cmp::Ordering::Equal
    }
}

struct MontCtxN {
    n: LimbN,
    np: u64,    // -n[0]^{-1} mod 2^64
    r2: LimbN,  // R^2 mod n, R = 2^(64*k)
    k: usize,
}

impl MontCtxN {
    fn new(n: &LimbN) -> Self {
        let k = n.k;
        let np = mont_n_prime(n.d[0]);
        // Compute R^2 mod n by repeated doubling: R = 2^(64k), R^2 = 2^(128k)
        // Start with 1, double 128*k times
        let mut r2 = LimbN::zero(k);
        r2.d[0] = 1;
        for _ in 0..128*k {
            // Double: r2 = r2 * 2
            let mut carry = 0u64;
            for j in 0..k {
                let (lo, hi) = widening_mul64(r2.d[j], 2);
                let (s, o) = lo.overflowing_add(carry);
                r2.d[j] = s;
                carry = hi + o as u64;
            }
            // Reduce mod n if needed
            if carry > 0 || r2.cmp(n) != std::cmp::Ordering::Less {
                // Subtract n
                let mut borrow = 0i64;
                for j in 0..k {
                    let diff = r2.d[j] as i128 - n.d[j] as i128 - borrow as i128;
                    r2.d[j] = diff as u64;
                    borrow = if diff < 0 { 1 } else { 0 };
                }
            }
        }
        Self { n: *n, np, r2, k }
    }

    // CIOS Montgomery multiply: result = a * b * R^{-1} mod n
    #[inline]
    fn mul(&self, a: &LimbN, b: &LimbN) -> LimbN {
        let k = self.k;
        let mut t = [0u64; MAX_LIMBS + 1];
        for i in 0..k {
            // t = t + a[i] * b
            let mut c = 0u64;
            for j in 0..k {
                let (lo, hi) = widening_mul64(a.d[i], b.d[j]);
                let (s1, o1) = t[j].overflowing_add(lo);
                let (s2, o2) = s1.overflowing_add(c);
                t[j] = s2;
                c = hi + o1 as u64 + o2 as u64;
            }
            t[k] = t[k].wrapping_add(c);
            // Montgomery reduction step
            let m = t[0].wrapping_mul(self.np);
            let mut c2 = 0u64;
            for j in 0..k {
                let (lo, hi) = widening_mul64(m, self.n.d[j]);
                let (s1, o1) = t[j].overflowing_add(lo);
                let (s2, o2) = s1.overflowing_add(c2);
                t[j] = s2;
                c2 = hi + o1 as u64 + o2 as u64;
            }
            t[k] = t[k].wrapping_add(c2);
            // Shift
            for j in 0..k { t[j] = t[j+1]; }
            t[k] = 0;
        }
        // Conditional subtraction
        let mut r = LimbN { d: [0; MAX_LIMBS], k };
        for j in 0..k { r.d[j] = t[j]; }
        if r.cmp(&self.n) != std::cmp::Ordering::Less {
            let mut borrow = 0i64;
            for j in 0..k {
                let diff = r.d[j] as i128 - self.n.d[j] as i128 - borrow as i128;
                r.d[j] = diff as u64;
                borrow = if diff < 0 { 1 } else { 0 };
            }
        }
        r
    }

    fn to_mont(&self, a: &LimbN) -> LimbN { self.mul(a, &self.r2) }
    fn from_mont(&self, a: &LimbN) -> LimbN {
        let one = { let mut o = LimbN::zero(self.k); o.d[0] = 1; o };
        self.mul(a, &one)
    }

    fn add(&self, a: &LimbN, b: &LimbN) -> LimbN {
        let k = self.k;
        let mut r = LimbN::zero(k);
        let mut carry = 0u64;
        for j in 0..k {
            let (s1, o1) = a.d[j].overflowing_add(b.d[j]);
            let (s2, o2) = s1.overflowing_add(carry);
            r.d[j] = s2;
            carry = o1 as u64 + o2 as u64;
        }
        if carry > 0 || r.cmp(&self.n) != std::cmp::Ordering::Less {
            let mut borrow = 0i64;
            for j in 0..k {
                let diff = r.d[j] as i128 - self.n.d[j] as i128 - borrow as i128;
                r.d[j] = diff as u64;
                borrow = if diff < 0 { 1 } else { 0 };
            }
        }
        r
    }

    fn sub(&self, a: &LimbN, b: &LimbN) -> LimbN {
        let k = self.k;
        let mut r = LimbN::zero(k);
        if a.cmp(b) != std::cmp::Ordering::Less {
            let mut borrow = 0i64;
            for j in 0..k {
                let diff = a.d[j] as i128 - b.d[j] as i128 - borrow as i128;
                r.d[j] = diff as u64;
                borrow = if diff < 0 { 1 } else { 0 };
            }
        } else {
            // a < b: result = n - (b - a)
            let mut borrow = 0i64;
            for j in 0..k {
                let diff = b.d[j] as i128 - a.d[j] as i128 - borrow as i128;
                r.d[j] = diff as u64;
                borrow = if diff < 0 { 1 } else { 0 };
            }
            // r = b - a, now compute n - r
            let br = r;
            let mut borrow2 = 0i64;
            for j in 0..k {
                let diff = self.n.d[j] as i128 - br.d[j] as i128 - borrow2 as i128;
                r.d[j] = diff as u64;
                borrow2 = if diff < 0 { 1 } else { 0 };
            }
        }
        r
    }
}

// Compute gcd(a_limbn, n_big) using BigUint
fn gcd_limbn_big(a: &LimbN, n: &BigUint) -> BigUint {
    let ab = a.to_biguint();
    ab.gcd(n)
}

// ============================================================
// ECM with fixed-width Montgomery arithmetic (fast path)
// ============================================================

#[derive(Clone)]
struct EcPointN { x: LimbN, z: LimbN }

impl EcPointN {
    fn is_infty(&self) -> bool { self.z.is_zero() }
    fn infty(k: usize) -> Self {
        let mut x = LimbN::zero(k); x.d[0] = 1;
        EcPointN { x, z: LimbN::zero(k) }
    }
}

struct MontCurveN<'a> {
    a24: LimbN,  // in Montgomery form
    ctx: &'a MontCtxN,
}

impl<'a> MontCurveN<'a> {
    fn double(&self, p: &EcPointN) -> EcPointN {
        if p.is_infty() { return EcPointN::infty(self.ctx.k); }
        let ctx = self.ctx;
        let u = ctx.add(&p.x, &p.z);
        let v = ctx.sub(&p.x, &p.z);
        let u2 = ctx.mul(&u, &u);
        let v2 = ctx.mul(&v, &v);
        let w = ctx.sub(&u2, &v2);
        let xp = ctx.mul(&u2, &v2);
        let a24w = ctx.mul(&self.a24, &w);
        let zp = ctx.mul(&w, &ctx.add(&v2, &a24w));
        EcPointN { x: xp, z: zp }
    }

    fn dadd(&self, p: &EcPointN, q: &EcPointN, diff: &EcPointN) -> EcPointN {
        if p.is_infty() { return q.clone(); }
        if q.is_infty() { return p.clone(); }
        let ctx = self.ctx;
        let u = ctx.mul(&ctx.sub(&q.x, &q.z), &ctx.add(&p.x, &p.z));
        let v = ctx.mul(&ctx.add(&q.x, &q.z), &ctx.sub(&p.x, &p.z));
        let add = ctx.add(&u, &v);
        let sub = ctx.sub(&u, &v);
        let xp = ctx.mul(&diff.z, &ctx.mul(&add, &add));
        let zp = ctx.mul(&diff.x, &ctx.mul(&sub, &sub));
        EcPointN { x: xp, z: zp }
    }

    fn scalar_mul(&self, p: &EcPointN, k: u64) -> EcPointN {
        if k == 0 { return EcPointN::infty(self.ctx.k); }
        if k == 1 { return p.clone(); }
        let bits = 64 - k.leading_zeros() as usize;
        let mut r0 = p.clone();
        let mut r1 = self.double(p);
        for i in (0..bits-1).rev() {
            if (k >> i) & 1 == 0 {
                r1 = self.dadd(&r0, &r1, p);
                r0 = self.double(&r0);
            } else {
                r0 = self.dadd(&r0, &r1, p);
                r1 = self.double(&r1);
            }
        }
        r0
    }
}

fn sieve_primes_small(limit: usize) -> Vec<u32> {
    if limit < 2 { return vec![]; }
    let mut s = vec![true; limit+1];
    s[0]=false; s[1]=false;
    let mut i=2;
    while i*i<=limit { if s[i] { let mut j=i*i; while j<=limit { s[j]=false; j+=i; } } i+=1; }
    (2..=limit).filter(|&i| s[i]).map(|i| i as u32).collect()
}

// Modular inverse using BigUint extended Euclidean
fn modinv_limbn(a: &LimbN, n_big: &BigUint, k: usize) -> Option<LimbN> {
    let ab = a.to_biguint();
    if ab.is_zero() { return None; }
    let one = BigUint::one();
    let zero = BigUint::zero();
    let mut old_r = ab.clone();
    let mut r = n_big.clone();
    let mut old_s = one.clone();
    let mut s = zero.clone();
    while !r.is_zero() {
        let q = &old_r / &r;
        let tmp_r = old_r.clone(); old_r = r.clone(); r = tmp_r - &q * &r;
        let tmp_s = old_s.clone();
        old_s = s.clone();
        let qs = &q * &s % n_big;
        s = if tmp_s >= qs { (tmp_s - qs) % n_big } else { (n_big - (qs - tmp_s) % n_big) % n_big };
    }
    if old_r != one { return None; }
    Some(LimbN::from_biguint(&(old_s % n_big), k))
}

static ECM_CURVE_COUNT: AtomicU64 = AtomicU64::new(0);

// Fast ECM using fixed-width Montgomery arithmetic
fn ecm_one_curve_fast(ctx: &MontCtxN, n_big: &BigUint, sigma_u64: u64, b1: u64, primes: &[u32]) -> Option<LimbN> {
    let k = ctx.k;
    let n = &ctx.n;
    let one_big = BigUint::one();

    // Suyama parameterization
    let sigma = { let mut s = LimbN::zero(k); s.d[0] = sigma_u64; s };
    // All arithmetic done in Montgomery domain
    let sigma_m = ctx.to_mont(&sigma);
    let four = { let mut f = LimbN::zero(k); f.d[0] = 4; f };
    let five = { let mut f = LimbN::zero(k); f.d[0] = 5; f };
    let sixteen = { let mut f = LimbN::zero(k); f.d[0] = 16; f };
    let four_m = ctx.to_mont(&four);
    let five_m = ctx.to_mont(&five);
    let sixteen_m = ctx.to_mont(&sixteen);

    let v_m = ctx.mul(&sigma_m, &four_m);  // 4*sigma (in Montgomery)
    // u = sigma^2 - 5
    let sigma2_m = ctx.mul(&sigma_m, &sigma_m);
    let u_m = ctx.sub(&sigma2_m, &five_m);

    let u3_m = ctx.mul(&ctx.mul(&u_m, &u_m), &u_m);
    let v3_m = ctx.mul(&ctx.mul(&v_m, &v_m), &v_m);

    // a24 = (v-u)^3 * (3u+v) / (16 * u^3 * v)
    let vu_m = ctx.sub(&v_m, &u_m);
    let vu3_m = ctx.mul(&ctx.mul(&vu_m, &vu_m), &vu_m);
    let three_m = { let mut f = LimbN::zero(k); f.d[0] = 3; let fm = ctx.to_mont(&f); fm };
    let three_u_m = ctx.mul(&three_m, &u_m);
    let three_u_v_m = ctx.add(&three_u_m, &v_m);
    let num_m = ctx.mul(&vu3_m, &three_u_v_m);
    // den = 16 * u^3 * v
    let den_m = ctx.mul(&ctx.mul(&sixteen_m, &u3_m), &v_m);

    // Compute modinv(den) - need to convert from Montgomery first
    let den_normal = ctx.from_mont(&den_m);
    let den_big = den_normal.to_biguint();
    let g_check = den_big.gcd(n_big);
    if g_check != one_big && &g_check != n_big { return Some(LimbN::from_biguint(&g_check, k)); }
    let den_inv = modinv_limbn(&den_normal, n_big, k)?;
    let den_inv_m = ctx.to_mont(&den_inv);

    let a24_m = ctx.mul(&num_m, &den_inv_m);

    let curve = MontCurveN { a24: a24_m, ctx };

    // Initial point: x = u^3, z = v^3 (in Montgomery domain)
    let mut p = EcPointN { x: u3_m, z: v3_m };

    // Phase 1
    for &prime in primes {
        if prime as u64 > b1 { break; }
        let pp = prime as u64;
        let mut pk = pp;
        while pk <= b1 / pp { pk *= pp; }
        // pk is now the largest power of pp <= b1
        p = curve.scalar_mul(&p, pk);

        // Check gcd of Z (in Montgomery domain; we need actual value)
        if !p.z.is_zero() {
            let z_normal = ctx.from_mont(&p.z);
            let z_big = z_normal.to_biguint();
            let g = z_big.gcd(n_big);
            if g != one_big && &g != n_big { return Some(LimbN::from_biguint(&g, k)); }
        }
    }

    // Final check
    let z_normal = ctx.from_mont(&p.z);
    let z_big = z_normal.to_biguint();
    let g = z_big.gcd(n_big);
    if g != one_big && &g != n_big { Some(LimbN::from_biguint(&g, k)) } else { None }
}

fn ecm_factor(n_big: &BigUint, deadline: Instant) -> Option<BigUint> {
    let bits = n_big.bits() as usize;
    let factor_bits = bits / 2;

    // Choose k (number of 64-bit limbs) to cover n
    let k = (bits + 63) / 64;
    let k = k.max(3).min(MAX_LIMBS);

    // B1 based on factor size in digits: ECM GMP-ECM recommendations
    // factor_bits / 3.32 ≈ decimal digits of factor
    let b1: u64 = match factor_bits {
        0..=40  => 2_000,
        41..=55 => 11_000,
        56..=66 => 50_000,
        67..=75 => 100_000,
        76..=83 => 250_000,
        84..=92 => 500_000,
        93..=100 => 1_000_000,
        101..=116 => 3_000_000,
        117..=133 => 11_000_000,
        _ => 30_000_000,
    };

    let n_limb = LimbN::from_biguint(n_big, k);
    let ctx = Arc::new(MontCtxN::new(&n_limb));
    let primes = Arc::new(sieve_primes_small(b1.min(10_000_000) as usize));
    let stopped = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<BigUint>();

    for t in 0..8usize {
        let tx = tx.clone();
        let stopped = stopped.clone();
        let ctx_clone = ctx.clone();
        let n_big_clone = n_big.clone();
        let primes_clone = primes.clone();
        let seed: u64 = 0xdeadbeef1234abcd ^ (t as u64 * 0x9e3779b97f4a7c15);
        thread::spawn(move || {
            let mut rng = seed;
            xorshift64(&mut rng);
            loop {
                if stopped.load(Ordering::Relaxed) { return; }
                let sigma_u64 = xorshift64(&mut rng).max(7);
                if let Some(f) = ecm_one_curve_fast(&ctx_clone, &n_big_clone, sigma_u64, b1, &primes_clone) {
                    let _ = tx.send(f.to_biguint());
                    stopped.store(true, Ordering::Relaxed);
                    return;
                }
                ECM_CURVE_COUNT.fetch_add(1, Ordering::Relaxed);
            }
        });
    }
    drop(tx);

    let remaining = deadline.saturating_duration_since(Instant::now());
    let result = rx.recv_timeout(remaining).ok();
    stopped.store(true, Ordering::Relaxed);
    result
}

// ============================================================
// Pollard rho for BigUint (fallback for very large n)
// ============================================================

fn pollard_brent_big(n: &BigUint, c: u64, rng: &mut u64) -> Option<BigUint> {
    let one = BigUint::one(); let c_big = BigUint::from(c);
    let two = BigUint::from(2u64);
    let y_val = xorshift64(rng) as u64;
    let mut y = BigUint::from(y_val) % (n - &two) + &two;
    let mut r: u64 = 1; let mut q = one.clone();
    let mut x = y.clone(); let mut ys = y.clone();
    let f = |v: &BigUint| -> BigUint { (v*v + &c_big) % n };
    loop {
        x = y.clone(); for _ in 0..r { y = f(&y); }
        let mut k: u64 = 0; let mut d = one.clone();
        while k < r && d == one {
            ys = y.clone(); let steps = 128u64.min(r-k);
            for _ in 0..steps {
                y = f(&y);
                let diff = if y>x {&y-&x} else {&x-&y};
                q = (&q * diff) % n;
                if q.is_zero() { q = one.clone(); }
            }
            d = q.gcd(n); k += steps;
        }
        if d != one {
            if &d == n {
                d = one.clone();
                loop { ys=f(&ys); let diff=if ys>x{&ys-&x}else{&x-&ys}; d=diff.gcd(n); if d!=one{break;} }
                if &d==n {return None;}
            }
            if d!=one&&&d!=n {return Some(d);} return None;
        }
        r*=2; if r>(1u64<<26) {return None;}
    }
}

fn factor_big(n: &BigUint, deadline: Instant) -> Option<(BigUint, BigUint)> {
    let two = BigUint::from(2u64);
    if n%&two==BigUint::zero() {return Some((two.clone(),n/&two));}
    for i in (3u64..1_000_000).step_by(2) {
        let bi = BigUint::from(i);
        if n%&bi==BigUint::zero() {return Some((bi.clone(),n/&bi));}
    }

    if let Some(f) = ecm_factor(n, deadline) {
        let q = n/&f;
        let (p,q) = if f<=q {(f,q)} else {(q.clone(),n/&q)};
        return Some((p,q));
    }

    // Fallback: Pollard rho with BigUint
    let stopped = Arc::new(AtomicBool::new(false));
    let (tx,rx) = mpsc::channel::<BigUint>();
    for t in 0..8usize {
        let tx=tx.clone(); let stopped=stopped.clone(); let n_clone=n.clone();
        let seed:u64=0xdeadbeef1234abcd^(t as u64*0x9e3779b97f4a7c15);
        thread::spawn(move || {
            let mut rng=seed; xorshift64(&mut rng);
            loop {
                if stopped.load(Ordering::Relaxed) {return;}
                let c=(xorshift64(&mut rng)%10000)+1;
                if let Some(f)=pollard_brent_big(&n_clone,c,&mut rng) {
                    if f!=BigUint::one()&&&f!=&n_clone { let _=tx.send(f); stopped.store(true,Ordering::Relaxed); return; }
                }
            }
        });
    }
    drop(tx);
    let remaining=deadline.saturating_duration_since(Instant::now());
    let factor=rx.recv_timeout(remaining).ok()?;
    stopped.store(true,Ordering::Relaxed);
    let q=n/&factor;
    let (p,q)=if factor<=q {(factor,q)} else {(q.clone(),n/&q)};
    Some((p,q))
}

// ============================================================
// Main
// ============================================================

fn parse_id(line: &str) -> Option<String> {
    let key = "\"id\":";
    let pos = line.find(key)?;
    let rest = line[pos+key.len()..].trim_start();
    if let Some(r)=rest.strip_prefix('"') { let e=r.find('"')?; Some(r[..e].to_string()) }
    else { let e=rest.find(|c:char| !c.is_ascii_alphanumeric()&&c!='_'&&c!='-').unwrap_or(rest.len()); Some(rest[..e].to_string()) }
}

fn parse_n(line: &str) -> Option<BigUint> {
    let key = "\"n\":";
    let pos = line.find(key)?;
    let rest = line[pos+key.len()..].trim_start();
    let end = rest.find(|c:char| !c.is_ascii_digit()).unwrap_or(rest.len());
    if end==0 {return None;}
    rest[..end].parse::<BigUint>().ok()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut time_limit_secs: u64 = 60;
    let mut i = 1;
    while i < args.len() {
        if args[i]=="--time-limit" && i+1<args.len() { time_limit_secs=args[i+1].parse().unwrap_or(60); i+=2; }
        else { i+=1; }
    }
    let start = Instant::now();
    let deadline = start + Duration::from_millis(time_limit_secs*1000).saturating_sub(Duration::from_millis(300));

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    let mut inputs: Vec<(String,BigUint)> = Vec::new();
    for line in stdin.lock().lines() {
        let line=match line{Ok(l)=>l,Err(_)=>break};
        let line=line.trim().to_string(); if line.is_empty() {continue;}
        if let (Some(id),Some(n))=(parse_id(&line),parse_n(&line)) { inputs.push((id,n)); }
    }

    for (id,n) in &inputs {
        if Instant::now()>=deadline {
            writeln!(out,"{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}",id).unwrap();
            out.flush().unwrap(); continue;
        }
        let result = if let Some(nv)=n.to_u128() {
            if nv<=3 {None} else {factor_u128_parallel(nv).map(|(p,q)|(BigUint::from(p),BigUint::from(q)))}
        } else { factor_big(n,deadline) };

        match result {
            Some((p,q)) => { writeln!(out,"{{\"id\": \"{}\", \"answer\": \"{} {}\"}}",id,p,q).unwrap(); }
            None => { writeln!(out,"{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}",id).unwrap(); }
        }
        out.flush().unwrap();
    }
}
