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
// ECM - Lenstra's Elliptic Curve Method
// Using Montgomery curves By² = x³ + Ax² + x
// with x-only arithmetic (projective: (X:Z), x = X/Z)
// ============================================================

// Represents a point on a Montgomery curve using (X, Z) mod n
// Uses BigUint for modular arithmetic (handles any n size)
#[derive(Clone)]
struct EcPoint { x: BigUint, z: BigUint }

impl EcPoint {
    fn is_infty(&self) -> bool { self.z.is_zero() }
    fn infty() -> Self { EcPoint { x: BigUint::one(), z: BigUint::zero() } }
}

struct MontCurve { a24: BigUint, n: BigUint } // a24 = (A+2)/4 mod n

impl MontCurve {
    // Double: P → 2P
    fn double(&self, p: &EcPoint) -> EcPoint {
        if p.is_infty() { return EcPoint::infty(); }
        let n = &self.n;
        let u = (&p.x + &p.z) % n;
        let v = (&p.x + n - &p.z) % n;  // p.x - p.z mod n (safe)
        let u2 = (&u * &u) % n;
        let v2 = (&v * &v) % n;
        let w = if u2 >= v2 { (&u2 - &v2) % n } else { (n - (&v2 - &u2) % n) % n };
        let xp = (&u2 * &v2) % n;
        // zp = w * (v2 + a24 * w) mod n
        let a24w = (&self.a24 * &w) % n;
        let zp = (&w * ((&v2 + a24w) % n)) % n;
        EcPoint { x: xp, z: zp }
    }

    // Differential addition: (P, Q, P-Q) → P+Q
    fn dadd(&self, p: &EcPoint, q: &EcPoint, diff: &EcPoint) -> EcPoint {
        if p.is_infty() { return q.clone(); }
        if q.is_infty() { return p.clone(); }
        let n = &self.n;
        // Safe subtraction: a - b mod n = (a + n - b) % n
        let qxmz = (&q.x + n - &q.z) % n;  // q.x - q.z mod n
        let qxpz = (&q.x + &q.z) % n;
        let pxpz = (&p.x + &p.z) % n;
        let pxmz = (&p.x + n - &p.z) % n;  // p.x - p.z mod n
        let u = (&qxmz * &pxpz) % n;
        let v = (&qxpz * &pxmz) % n;
        let add = (&u + &v) % n;
        let sub = if u >= v { (&u - &v) % n } else { (n - (&v - &u) % n) % n };
        let xp = (&diff.z * (&add * &add % n)) % n;
        let zp = (&diff.x * (&sub * &sub % n)) % n;
        EcPoint { x: xp, z: zp }
    }

    // Scalar multiplication [k]P using Montgomery ladder
    fn scalar_mul(&self, p: &EcPoint, k: &BigUint) -> EcPoint {
        if k.is_zero() { return EcPoint::infty(); }
        let bits = k.bits();
        if bits == 0 { return EcPoint::infty(); }
        let mut r0 = p.clone();
        let mut r1 = self.double(p);
        let kdigits = k.to_u64_digits();
        for i in (0..bits-1).rev() {
            let wi = (i / 64) as usize;
            let bi = i % 64;
            let bit = if wi < kdigits.len() { (kdigits[wi] >> bi) & 1 } else { 0 };
            if bit == 0 {
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

// ECM for BigUint numbers
// Returns a factor of n, or None if no factor found
fn ecm_one_curve(n: &BigUint, seed: u64, b1: u64, primes: &[u32]) -> Option<BigUint> {
    // Suyama's parameterization: generate curve from random sigma
    let mut rng = seed;
    xorshift64(&mut rng);
    // sigma must be >= 7; for d>=20, n > 2^128 so any u64 >= 7 is < n
    let sigma = BigUint::from(xorshift64(&mut rng).max(7));
    let v = (&sigma * BigUint::from(4u64)) % n;
    let u = ((&sigma * &sigma) % n + n - BigUint::from(5u64)) % n;
    let u3 = (&u * &u % n * &u) % n;
    let v3 = (&v * &v % n * &v) % n;
    // x0 = u^3, z0 = v^3
    // A = (v-u)^3 * (3u+v) / (4u^3*v) - 2
    // We need a24 = (A+2)/4 = (v-u)^3*(3u+v) / (16 * u^3 * v) mod n
    let vu = if v >= u { (&v - &u) % n } else { (n - (&u - &v) % n) % n };
    let vu3 = (&vu * &vu % n * &vu) % n;
    let three_u_v = (&u * BigUint::from(3u64) % n + &v) % n;
    let num = (&vu3 * &three_u_v) % n;
    let den = (BigUint::from(16u64) * &u3 % n * &v) % n;

    // Compute modular inverse of den
    let one = BigUint::one();
    let den_inv = match modinv_big(&den, n) {
        Some(inv) => inv,
        None => {
            // gcd(den, n) is a non-trivial factor!
            let g = den.gcd(n);
            if g != one && &g != n { return Some(g); }
            return None;
        }
    };

    let a24 = (&num * &den_inv) % n;
    let curve = MontCurve { a24, n: n.clone() };

    let mut p = EcPoint { x: u3, z: v3 };

    // Phase 1: compute [m]P for m = product of prime powers up to B1
    for &prime in primes {
        if prime as u64 > b1 { break; }
        let pp = prime as u64;
        let mut pk = pp;
        while pk <= b1 { pk *= pp; }
        pk /= pp;
        let pk_big = BigUint::from(pk);
        p = curve.scalar_mul(&p, &pk_big);

        // Check gcd periodically
        if !p.z.is_zero() {
            let g = p.z.gcd(n);
            if g != one && &g != n { return Some(g); }
        }
    }

    let g = p.z.gcd(n);
    if g != one && &g != n { Some(g) } else { None }
}

fn modinv_big(a: &BigUint, n: &BigUint) -> Option<BigUint> {
    // Extended Euclidean algorithm
    if a.is_zero() { return None; }
    let one = BigUint::one();
    let zero = BigUint::zero();
    let mut old_r = a.clone();
    let mut r = n.clone();
    let mut old_s = one.clone();
    let mut s = zero.clone();
    while !r.is_zero() {
        let q = &old_r / &r;
        let tmp_r = old_r.clone(); old_r = r.clone(); r = tmp_r - &q * &r;
        let tmp_s = old_s.clone();
        old_s = s.clone();
        // s = tmp_s - q * s, but need to stay positive
        let qs = &q * &s % n;
        s = if tmp_s >= qs { (tmp_s - qs) % n } else { (n - (qs - tmp_s) % n) % n };
    }
    if old_r != one { return None; }
    Some(old_s % n)
}

static ECM_CURVE_COUNT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn ecm_factor(n: &BigUint, deadline: Instant) -> Option<BigUint> {
    let bits = n.bits() as usize;

    // Choose B1 based on factor size (half of n's bits)
    let factor_bits = bits / 2;
    let b1: u64 = match factor_bits {
        0..=40 => 2_000,
        41..=60 => 10_000,
        61..=80 => 50_000,
        81..=100 => 250_000,
        101..=120 => 1_000_000,
        121..=150 => 3_000_000,
        151..=180 => 10_000_000,
        _ => 30_000_000,
    };

    let primes = Arc::new(sieve_primes_small(b1.min(10_000_000) as usize));
    let stopped = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<BigUint>();

    for t in 0..8usize {
        let tx = tx.clone();
        let stopped = stopped.clone();
        let n_clone = n.clone();
        let primes_clone = primes.clone();
        let seed: u64 = 0xdeadbeef1234abcd ^ (t as u64 * 0x9e3779b97f4a7c15);
        thread::spawn(move || {
            let mut rng = seed;
            xorshift64(&mut rng);
            loop {
                if stopped.load(Ordering::Relaxed) { return; }
                let curve_seed = xorshift64(&mut rng);
                let t0 = Instant::now();
                let result = ecm_one_curve(&n_clone, curve_seed, b1, &primes_clone);
                let cnt = ECM_CURVE_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
                if cnt <= 3 || cnt % 20 == 0 {
                    eprintln!("ECM curve {} took {:.1}ms (thread {})", cnt, t0.elapsed().as_secs_f64()*1000.0, t);
                }
                if let Some(f) = result {
                    let _ = tx.send(f);
                    stopped.store(true, Ordering::Relaxed);
                    return;
                }
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
// Pollard rho for BigUint (fallback)
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

    // ECM is the primary method for large numbers
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
