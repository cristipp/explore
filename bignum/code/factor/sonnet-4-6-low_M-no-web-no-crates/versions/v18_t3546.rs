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

// ===== Fast 64-bit modular arithmetic =====
#[inline(always)]
fn mulmod64(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}
fn powmod64(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64; b %= m;
    while e > 0 { if e&1==1 {r=mulmod64(r,b,m);} b=mulmod64(b,b,m); e>>=1; } r
}

// ===== ARM64 umulh for high 64 bits of 64x64 =====
#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn mulhi64(a: u64, b: u64) -> u64 {
    let hi: u64;
    std::arch::asm!("umulh {}, {}, {}", out(reg) hi, in(reg) a, in(reg) b, options(pure, nomem, nostack));
    hi
}
#[cfg(not(target_arch = "aarch64"))]
#[inline(always)]
unsafe fn mulhi64(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) >> 64) as u64
}

// Full 128x128->256 multiply, returns (hi, lo)
#[inline(always)]
fn mul256(a: u128, b: u128) -> (u128, u128) {
    let (a0, a1) = (a as u64, (a>>64) as u64);
    let (b0, b1) = (b as u64, (b>>64) as u64);
    let (p00l, p00h) = (a0.wrapping_mul(b0), unsafe { mulhi64(a0, b0) });
    let (p10l, p10h) = (a1.wrapping_mul(b0), unsafe { mulhi64(a1, b0) });
    let (p01l, p01h) = (a0.wrapping_mul(b1), unsafe { mulhi64(a0, b1) });
    let (p11l, p11h) = (a1.wrapping_mul(b1), unsafe { mulhi64(a1, b1) });
    // lo = p00l + (p00h + p10l + p01l)*2^64
    let (s1, c1) = p00h.overflowing_add(p10l);
    let (s1, c2) = s1.overflowing_add(p01l);
    let carry = c1 as u64 + c2 as u64;
    let lo = (p00l as u128) | ((s1 as u128) << 64);
    // hi = p11 + (p10h + p01h + carry)
    let (s2, c3) = p10h.overflowing_add(p01h);
    let (s2, c4) = s2.overflowing_add(p11l);
    let (s2, c5) = s2.overflowing_add(carry);
    let carry2 = c3 as u64 + c4 as u64 + c5 as u64;
    let hi = (s2 as u128) | (((p11h.wrapping_add(carry2)) as u128) << 64);
    (hi, lo)
}

// ===== Montgomery multiplication for 128-bit numbers =====
#[derive(Clone)]
struct Mont128 {
    n: u128,
    np: u128,  // -n^{-1} mod 2^128
    r2: u128,  // 2^256 mod n  (= R^2 mod n where R=2^128)
}

impl Mont128 {
    fn new(n: u128) -> Self {
        debug_assert!(n & 1 == 1);
        // Compute n^{-1} mod 2^128 via Newton's method
        let mut x = 1u128;
        for _ in 0..7 {
            x = x.wrapping_mul(2u128.wrapping_sub(n.wrapping_mul(x)));
        }
        let np = 0u128.wrapping_sub(x);
        // r2 = 2^256 mod n: double 256 times
        let mut r2 = 1u128 % n;
        for _ in 0..256 { r2 = r2.wrapping_add(r2); if r2 >= n { r2 -= n; } }
        Mont128 { n, np, r2 }
    }

    // Montgomery REDC: given (hi, lo) = T, return T * R^{-1} mod n
    #[inline(always)]
    fn redc(&self, hi: u128, lo: u128) -> u128 {
        // u = lo * np mod R (just the low 128 bits)
        let (_, u) = mul256(lo, self.np);
        // t = T + u*n, then take high 128 bits (divide by R)
        let (uh, ul) = mul256(u, self.n);
        let (_, carry) = lo.overflowing_add(ul);
        let res = hi.wrapping_add(uh).wrapping_add(carry as u128);
        if res >= self.n { res - self.n } else { res }
    }

    // Multiply a,b in Montgomery form, return Montgomery form
    #[inline(always)]
    fn mont_mul(&self, a: u128, b: u128) -> u128 {
        let (hi, lo) = mul256(a, b);
        self.redc(hi, lo)
    }

    // Convert to Montgomery form: a -> a*R mod n
    #[inline(always)]
    fn enter(&self, a: u128) -> u128 {
        self.mont_mul(a % self.n, self.r2)
    }

    // Convert from Montgomery form: a_mont -> a
    #[inline(always)]
    fn leave(&self, a: u128) -> u128 {
        self.redc(0, a)
    }
}

// ===== Primality =====
fn is_prime_u64(n: u64) -> bool {
    if n < 2 { return false; }
    if n==2||n==3||n==5||n==7 { return true; }
    if n%2==0||n%3==0||n%5==0 { return false; }
    let mut d=n-1; let mut r=0u32;
    while d%2==0 { d/=2; r+=1; }
    'outer: for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37] {
        if a>=n { continue; }
        let mut x=powmod64(a,d,n);
        if x==1||x==n-1 { continue; }
        for _ in 0..r-1 { x=mulmod64(x,x,n); if x==n-1 { continue 'outer; } }
        return false;
    }
    true
}

fn is_prime_u128(n: u128) -> bool {
    if n<=u64::MAX as u128 { return is_prime_u64(n as u64); }
    if n%2==0 { return false; }
    let mut d=n-1; let mut r=0u32;
    while d%2==0 { d/=2; r+=1; }
    let mont = Mont128::new(n);
    let one_m = mont.enter(1);
    let n1_m = mont.enter(n-1);
    'outer: for &a in &[2u128,3,5,7,11,13,17,19,23,29,31,37,41,43,47] {
        if a>=n { continue; }
        // compute a^d mod n using Montgomery
        let mut x = {
            let mut base = mont.enter(a);
            let mut exp = d;
            let mut res = mont.enter(1);
            while exp > 0 {
                if exp&1==1 { res = mont.mont_mul(res, base); }
                base = mont.mont_mul(base, base);
                exp >>= 1;
            }
            res
        };
        if x==one_m || x==n1_m { continue; }
        for _ in 0..r-1 {
            x = mont.mont_mul(x, x);
            if x==n1_m { continue 'outer; }
        }
        return false;
    }
    true
}

fn is_prime_big(n: &BigUint) -> bool {
    if let Some(n128) = n.to_u128() { return is_prime_u128(n128); }
    let two = BigUint::from(2u32); let one = BigUint::one();
    if n%&two==BigUint::zero() { return false; }
    let nm1=n-&one; let mut d=nm1.clone(); let mut r=0u32;
    while &d%&two==BigUint::zero() { d>>=1; r+=1; }
    'outer: for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37,41,43,47] {
        let ab=BigUint::from(a); if ab>=*n { continue; }
        let mut x=ab.modpow(&d,n);
        if x==one||x==nm1 { continue; }
        for _ in 0..r-1 { x=x.modpow(&two,n); if x==nm1 { continue 'outer; } }
        return false;
    }
    true
}

// ===== Integer square root =====
fn isqrt_big(n: &BigUint) -> BigUint {
    if n.is_zero() { return BigUint::zero(); }
    let mut x = BigUint::one() << ((n.bits() as usize+1)/2);
    loop { let q=n/&x; if q>=x { return x; } x=(x+q)>>1usize; }
}

// ===== GCDs =====
fn gcd64(mut a:u64,mut b:u64)->u64 { while b!=0{let t=b;b=a%b;a=t;}a }
fn gcd128(mut a:u128,mut b:u128)->u128 { while b!=0{let t=b;b=a%b;a=t;}a }

// ===== Pollard's Rho u64 =====
fn pollard_brent_u64(n: u64, c: u64) -> Option<u64> {
    if n%2==0 { return Some(2); }
    let mut y=2u64; let mut r=1u64; let mut q=1u64;
    let mut x=2u64; let mut ys=2u64; let mut d=1u64;
    let m=256u64;
    loop {
        x=y;
        for _ in 0..r { y=(mulmod64(y,y,n)+c)%n; }
        let mut k=0u64;
        loop {
            ys=y; let step=m.min(r-k);
            for _ in 0..step {
                y=(mulmod64(y,y,n)+c)%n;
                let diff=if y>x{y-x}else{x-y};
                q=mulmod64(q,diff,n);
            }
            d=gcd64(q,n); k+=m;
            if k>=r||d!=1 { break; }
        }
        if d!=1 { break; }
        r<<=1; if r>1u64<<28 { d=n; break; }
    }
    if d==n {
        loop { ys=(mulmod64(ys,ys,n)+c)%n;
            let diff=if ys>x{ys-x}else{x-ys}; d=gcd64(diff,n);
            if d!=1 { break; } if ys==x { return None; } }
    }
    if d==1||d==n { None } else { Some(d) }
}

// ===== Pollard's Rho u128 with Montgomery =====
fn pollard_brent_u128_mont(n: u128, c_in: u128, stop: &AtomicBool) -> Option<u128> {
    if n%2==0 { return Some(2); }
    let mont = Mont128::new(n);
    let c = mont.enter(c_in % n);
    let one_m = mont.enter(1);
    // f(x_mont) = (x^2 + c)_mont — all values stay in Montgomery form
    // sq_mont = mont_mul(x_mont, x_mont); result_mont = (sq_mont + c_mont) mod n
    let f = |x: u128| -> u128 {
        let sq = mont.mont_mul(x, x);
        let r = sq + c;
        if r >= n { r - n } else { r }
    };

    let mut y = mont.enter(2);
    let mut r = 1u64;
    // q stays in Montgomery form; gcd(q_mont, n) = gcd(q, n) since gcd(R,n)=1
    let mut q = one_m;
    let mut x = y;
    let mut ys = y;
    let mut d;
    let m_batch = 256u64;

    loop {
        if stop.load(Ordering::Relaxed) { return None; }
        x = y;
        for _ in 0..r { y = f(y); }
        let mut k = 0u64;
        loop {
            ys = y;
            let step = m_batch.min(r-k);
            for _ in 0..step {
                y = f(y);
                // diff_mont = |y_mont - x_mont| mod n (represents |y-x|*R mod n)
                let diff = if y > x { y - x } else { x - y };
                q = mont.mont_mul(q, diff);
                if q == 0 { q = one_m; }
            }
            d = gcd128(q, n); k += m_batch;
            if k>=r || d!=1 { break; }
        }
        if d!=1 { break; }
        r<<=1; if r>1u64<<26 { return None; }
    }
    if d==n {
        // backtrack step by step
        loop {
            let diff = if ys > x { ys - x } else { x - ys };
            d = gcd128(diff, n);
            if d!=1 { break; }
            if ys==x { return None; }
            ys = f(ys);
        }
    }
    if d==1||d==n { None } else { Some(d) }
}

// ===== Pollard's Rho BigUint =====
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
        let mut d = one.clone();
        loop {
            ys = y.clone(); let step = m.min(r-k);
            for _ in 0..step {
                y = f(y.clone());
                let diff = if y>x { y.clone()-x.clone() } else { x.clone()-y.clone() };
                q = q * &diff % n;
            }
            d = q.gcd(n); k += m;
            if k>=r || d!=one { break; }
        }
        if d!=one {
            if &d!=n { return Some(d); }
            // backtrack
            loop {
                ys = f(ys.clone());
                let diff = if ys>x { ys.clone()-x.clone() } else { x.clone()-ys.clone() };
                d = diff.gcd(n);
                if d!=one { return if &d==n { None } else { Some(d) }; }
                if ys==x { return None; }
            }
        }
        r<<=1; if r>1<<22 { return None; }
    }
}

// ===== Sieve of Eratosthenes =====
fn sieve_primes(limit: usize) -> Vec<u32> {
    if limit<2 { return vec![]; }
    let mut s=vec![true;limit+1]; s[0]=false; if limit>0{s[1]=false;}
    let mut i=2; while i*i<=limit { if s[i] { let mut j=i*i; while j<=limit{s[j]=false;j+=i;} } i+=1; }
    (2..=limit).filter(|&i|s[i]).map(|i|i as u32).collect()
}

// ===== Jacobi symbol =====
fn jacobi(mut a:i64,mut n:i64)->i32 {
    if n<=0||n%2==0 { return 0; }
    let mut r=1i32; a=((a%n)+n)%n;
    while a!=0 {
        while a%2==0 { a/=2; let nm=n%8; if nm==3||nm==5{r=-r;} }
        std::mem::swap(&mut a,&mut n);
        if a%4==3&&n%4==3{r=-r;} a%=n;
    }
    if n==1 { r } else { 0 }
}

// ===== Tonelli-Shanks =====
fn tonelli(n:u64,p:u64)->u64 {
    if n==0{return 0;} if p==2{return n&1;}
    if p%4==3{return powmod64(n,(p+1)/4,p);}
    let mut q=p-1; let mut s=0u32;
    while q%2==0{q/=2;s+=1;}
    let mut z=2u64; while powmod64(z,(p-1)/2,p)!=p-1{z+=1;}
    let mut mm=s; let mut c=powmod64(z,q,p); let mut t=powmod64(n,q,p); let mut r=powmod64(n,(q+1)/2,p);
    loop {
        if t==0{return 0;} if t==1{return r;}
        let mut i=1u32; let mut tmp=mulmod64(t,t,p);
        while tmp!=1{tmp=mulmod64(tmp,tmp,p);i+=1;}
        if i>=mm{return p;}
        let b=powmod64(c,1u64<<(mm-i-1),p);
        mm=i; c=mulmod64(b,b,p); t=mulmod64(t,c,p); r=mulmod64(r,b,p);
    }
}

// ===== Quadratic Sieve =====
fn biguint_mod_u32(n:&BigUint,m:u32)->u32 { (n%BigUint::from(m)).to_u32().unwrap_or(0) }

fn qs_params(nd:usize)->(usize,usize) {
    let ln_n=nd as f64*2.302585;
    let ln_ln=ln_n.ln().max(1.0);
    let exp=0.5*(ln_n*ln_ln).sqrt();
    let b=(exp.exp() as usize).clamp(500,3_000_000);
    let m=(b*50).clamp(200_000,50_000_000);
    (b,m)
}

// Fast path: Q(x) fits in u128 (works for n up to ~62 digits)
fn trial_factor_qs_u128(qx: u128, fb: &[u32]) -> Option<(Vec<u8>, Vec<u32>)> {
    let mut rem = qx;
    let mut ev = vec![0u8; fb.len()];
    let mut fv = vec![0u32; fb.len()];
    let b_max = *fb.last().unwrap_or(&0) as u128;
    for (i, &p) in fb.iter().enumerate() {
        let p128 = p as u128;
        if p128 * p128 > rem {
            // rem is 1 or a prime. If prime > B, not smooth.
            return if rem <= b_max {
                // rem is a prime in FB; find and record it
                if let Ok(pos) = fb[i..].binary_search(&(rem as u32)) {
                    fv[i+pos] = 1; ev[i+pos] = 1;
                    Some((ev, fv))
                } else { None }
            } else if rem == 1 { Some((ev, fv)) } else { None };
        }
        let mut cnt = 0u32;
        while rem % p128 == 0 { rem /= p128; cnt += 1; }
        fv[i] = cnt; ev[i] = (cnt & 1) as u8;
        if rem == 1 { return Some((ev, fv)); }
    }
    if rem != 1 { None } else { Some((ev, fv)) }
}

fn trial_factor_qs(qx: &BigUint, fb: &[u32]) -> Option<(Vec<u8>, Vec<u32>)> {
    // Use fast u128 path whenever possible
    if let Some(q128) = qx.to_u128() {
        return trial_factor_qs_u128(q128, fb);
    }
    let mut rem = qx.clone();
    let one = BigUint::one();
    let mut ev = vec![0u8; fb.len()];
    let mut fv = vec![0u32; fb.len()];
    for (i, &p) in fb.iter().enumerate() {
        let p_big = BigUint::from(p as u64);
        let mut cnt = 0u32;
        loop {
            let (q, r) = rem.div_rem(&p_big);
            if r.is_zero() { rem = q; cnt += 1; } else { break; }
        }
        fv[i] = cnt; ev[i] = (cnt&1) as u8;
        if rem == one { return Some((ev, fv)); }
        // Switch to u128 / u64 when small
        if let Some(rem128) = rem.to_u128() {
            // remaining work via u128
            let partial_ev = &ev[..=i];
            let partial_fv = &fv[..=i];
            if let Some((ev2, fv2)) = trial_factor_qs_u128(rem128, &fb[i+1..]) {
                let mut full_ev = vec![0u8; fb.len()];
                let mut full_fv = vec![0u32; fb.len()];
                full_ev[..=i].copy_from_slice(partial_ev);
                full_fv[..=i].copy_from_slice(partial_fv);
                full_ev[i+1..].copy_from_slice(&ev2);
                full_fv[i+1..].copy_from_slice(&fv2);
                return Some((full_ev, full_fv));
            }
            return None;
        }
    }
    if rem != one { None } else { Some((ev, fv)) }
}

fn quadratic_sieve(n: &BigUint, deadline: Instant) -> Option<BigUint> {
    let one = BigUint::one();
    let nd = n.to_str_radix(10).len();
    if nd < 6 { return None; }
    let (b_bound, _) = qs_params(nd);
    let all_primes = sieve_primes(b_bound);
    let mut fb: Vec<u32> = vec![2];
    for &p in &all_primes[1..] {
        let nm = biguint_mod_u32(n, p) as i64;
        if jacobi(nm, p as i64) == 1 { fb.push(p); }
    }
    let fb_size = fb.len();
    if fb_size < 30 { return None; }
    let sqrt_n = isqrt_big(n);
    let base = &sqrt_n + &BigUint::one();
    let base_mod: Vec<u64> = fb.iter().map(|&p| biguint_mod_u32(&base, p) as u64).collect();
    let roots: Vec<(u64,u64)> = fb.iter().enumerate().map(|(i,&p)| {
        let p64=p as u64;
        if p==2 { let r=biguint_mod_u32(n,2) as u64; let s=((r as i64-base_mod[i] as i64).rem_euclid(2)) as u64; (s,s) }
        else {
            let nm=biguint_mod_u32(n,p) as u64;
            let r=tonelli(nm,p64); if r>=p64{return (0,0);}
            let r1=((r as i64-base_mod[i] as i64).rem_euclid(p64 as i64)) as u64;
            let r2=(((p64-r) as i64-base_mod[i] as i64).rem_euclid(p64 as i64)) as u64;
            (r1,r2)
        }
    }).collect();
    let log_p: Vec<f32> = fb.iter().map(|&p|(p as f64).ln() as f32).collect();
    // log_qm: estimate log|Q(x)| at x=sieve_half using Q ≈ 2*sqrt(n)*sieve_half
    let sieve_half: usize = 1 << 17; // 128K: fits in L2 cache (256KB f32)
    let sieve_len = sieve_half * 2;
    let log_qm = (nd as f64*2.302585/2.0)+(sieve_half as f64).ln();
    let threshold = (log_qm*0.80) as f32;
    let need = fb_size + 60;
    struct Rel { a: BigUint, ev: Vec<u8>, fv: Vec<u32> }
    let mut rels: Vec<Rel> = Vec::new();
    let mut sieve = vec![0.0f32; sieve_len];
    let mut chunk: i64 = 0;
    while rels.len() < need && Instant::now() < deadline {
        for v in &mut sieve { *v = 0.0; }
        for i in 0..fb_size {
            let p=fb[i] as usize; let lp=log_p[i];
            let (r1,r2)=roots[i];
            let s1=((r1 as i64-chunk).rem_euclid(p as i64)) as usize;
            let s2=((r2 as i64-chunk).rem_euclid(p as i64)) as usize;
            let mut j=s1; while j<sieve_len{sieve[j]+=lp;j+=p;}
            if s1!=s2 { let mut j=s2; while j<sieve_len{sieve[j]+=lp;j+=p;} }
        }
        for i in 0..sieve_len {
            if sieve[i]<threshold { continue; }
            let x=chunk+i as i64;
            if x<=0 { continue; }
            let a=&base+BigUint::from(x as u64);
            let asq=&a*&a; if asq<*n { continue; }
            let qx=asq-n; if qx.is_zero() { continue; }
            if let Some((ev,fv))=trial_factor_qs(&qx,&fb) {
                rels.push(Rel{a,ev,fv});
                if rels.len()>=need { break; }
            }
        }
        chunk += sieve_len as i64;
        if chunk > 4_000_000_000i64 { break; }
    }
    if rels.len() < fb_size/2+10 { return None; }
    // Gaussian elimination via augmented matrix [A | I]
    // null vectors of A → null-space rows → generate factorization attempts
    let nrows=rels.len(); let ncols=fb_size;
    let awords=(ncols+63)/64;
    let iwords=(nrows+63)/64;
    // mat_a: the exponent matrix (mod 2), mat_i: identity tracking
    let mut mat_a: Vec<Vec<u64>> = rels.iter().map(|r| {
        let mut row=vec![0u64;awords];
        for j in 0..ncols { if r.ev[j]==1{row[j/64]|=1u64<<(j%64);} }
        row
    }).collect();
    let mut mat_i: Vec<Vec<u64>> = (0..nrows).map(|i| {
        let mut row=vec![0u64;iwords];
        row[i/64]|=1u64<<(i%64); row
    }).collect();
    let mut cur=0usize;
    for col in 0..ncols {
        if cur>=nrows { break; }
        let piv=(cur..nrows).find(|&r|(mat_a[r][col/64]>>(col%64))&1==1);
        if let Some(p)=piv {
            mat_a.swap(cur,p); mat_i.swap(cur,p);
            for r in 0..nrows {
                if r!=cur && (mat_a[r][col/64]>>(col%64))&1==1 {
                    for w in 0..awords{let v=mat_a[cur][w];mat_a[r][w]^=v;}
                    for w in 0..iwords{let v=mat_i[cur][w];mat_i[r][w]^=v;}
                }
            }
            cur+=1;
        }
    }
    let n_bigint=BigInt::from_biguint(Sign::Plus,n.clone());
    for row in 0..nrows {
        if mat_a[row].iter().any(|&w|w!=0) { continue; }
        // Collect contributing relation indices from mat_i[row]
        let mut contrib: Vec<usize> = Vec::new();
        for w in 0..iwords {
            let mut bits = mat_i[row][w];
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                contrib.push(w*64 + bit);
                bits &= bits - 1;
            }
        }
        if contrib.is_empty() { continue; }
        let mut total=vec![0u32;fb_size];
        for &ri in &contrib { for j in 0..fb_size{total[j]+=rels[ri].fv[j];} }
        if total.iter().any(|&e|e%2!=0) { continue; }
        let mut x=BigInt::from(1i32);
        for &ri in &contrib { x=x*BigInt::from_biguint(Sign::Plus,rels[ri].a.clone())%&n_bigint; }
        x=((x%&n_bigint)+&n_bigint)%&n_bigint;
        let mut y=BigInt::from(1i32);
        for j in 0..fb_size {
            let h=total[j]/2;
            if h>0 { let pw=BigUint::from(fb[j] as u64).pow(h); y=y*BigInt::from_biguint(Sign::Plus,pw)%&n_bigint; }
        }
        y=((y%&n_bigint)+&n_bigint)%&n_bigint;
        let xb=x.magnitude().clone(); let yb=y.magnitude().clone();
        let diff=if xb>yb{(xb.clone()-yb.clone()).gcd(n)}else{(yb.clone()-xb.clone()).gcd(n)};
        if diff!=one&&diff!=*n { return Some(diff); }
        let sum=(xb+yb).gcd(n);
        if sum!=one&&sum!=*n { return Some(sum); }
    }
    None
}

// ===== Trial division =====
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
fn trial_divide(n:&BigUint)->Option<BigUint> {
    for &p in SMALL_PRIMES {
        let pb=BigUint::from(p as u64);
        if n%&pb==BigUint::zero()&&n!=&pb { return Some(pb); }
    }
    None
}

// ===== Main factor =====
fn factor_number(n: &BigUint, deadline: Instant, global_stop: &Arc<AtomicBool>) -> Option<BigUint> {
    let one = BigUint::one();
    if n<=&one { return None; }
    if let Some(d)=trial_divide(n) { return Some(d); }
    if is_prime_big(n) { return None; }

    // u64 fast path
    if let Some(n64)=n.to_u64() {
        for c in 1..1000u64 {
            if let Some(d)=pollard_brent_u64(n64,c) {
                if d!=n64&&d!=1 { return Some(BigUint::from(d)); }
            }
        }
        return None;
    }

    // u128 path: parallel with stop flag
    if let Some(n128)=n.to_u128() {
        if !is_prime_u128(n128) {
            let done=Arc::new(AtomicBool::new(false));
            let found=Arc::new(Mutex::new(None::<u128>));
            let n_threads=10usize;
            let mut handles=Vec::new();
            for tid in 0..n_threads {
                let dc=Arc::clone(&done);
                let fc=Arc::clone(&found);
                handles.push(std::thread::spawn(move || {
                    for c in (tid as u128+1..).step_by(n_threads) {
                        if dc.load(Ordering::Relaxed) { return; }
                        if let Some(d)=pollard_brent_u128_mont(n128,c,&dc) {
                            if d!=n128&&d!=1 {
                                let mut f=fc.lock().unwrap();
                                if f.is_none() { *f=Some(d); }
                                dc.store(true,Ordering::Relaxed);
                                return;
                            }
                        }
                    }
                }));
            }
            loop {
                if done.load(Ordering::Relaxed) { break; }
                if Instant::now()>=deadline||global_stop.load(Ordering::Relaxed) { break; }
                std::thread::sleep(Duration::from_millis(5));
            }
            done.store(true,Ordering::Relaxed);
            for h in handles { let _=h.join(); }
            let result=found.lock().unwrap().clone();
            if let Some(d)=result { return Some(BigUint::from(d)); }
        }
        return None;
    }

    // BigUint Pollard + QS for large n
    let nd = n.to_str_radix(10).len();
    let n_arc=Arc::new(n.clone());
    let rho_res=Arc::new(Mutex::new(None::<BigUint>));
    let rho_stop=Arc::new(AtomicBool::new(false));
    let n_threads=8usize;
    let mut handles=Vec::new();
    for tid in 0..n_threads {
        let nc=Arc::clone(&n_arc); let rc=Arc::clone(&rho_res); let sf=Arc::clone(&rho_stop);
        handles.push(std::thread::spawn(move || {
            for c in (tid as u64+1..).step_by(n_threads).take(200) {
                if sf.load(Ordering::Relaxed) { return; }
                if let Some(d)=pollard_brent_big(&nc,c,&sf) {
                    let mut r=rc.lock().unwrap();
                    if r.is_none() { *r=Some(d); }
                    sf.store(true,Ordering::Relaxed); return;
                }
            }
        }));
    }
    let rho_budget=if nd<=40{Duration::from_secs(30)} else if nd<=60{Duration::from_secs(5)} else{Duration::from_secs(2)};
    let rho_dl=Instant::now()+rho_budget;
    loop {
        if rho_stop.load(Ordering::Relaxed) { break; }
        if Instant::now()>=rho_dl.min(deadline)||global_stop.load(Ordering::Relaxed) { break; }
        std::thread::sleep(Duration::from_millis(5));
    }
    rho_stop.store(true,Ordering::Relaxed);
    for h in handles { let _=h.join(); }
    let rr=rho_res.lock().unwrap().clone();
    if rr.is_some() { return rr; }
    if Instant::now()<deadline&&!global_stop.load(Ordering::Relaxed) {
        return quadratic_sieve(n, deadline);
    }
    None
}

fn main() {
    let args: Vec<String>=std::env::args().collect();
    let mut tl=60.0f64;
    for i in 0..args.len() {
        if args[i]=="--time-limit"&&i+1<args.len() { tl=args[i+1].parse().unwrap_or(60.0); }
    }
    let time_limit=Duration::from_secs_f64(tl);
    let global_start=Instant::now();
    let mut out=BufWriter::new(io::stdout().lock());
    let stop=Arc::new(AtomicBool::new(false));
    for line in io::stdin().lock().lines() {
        let line=match line{Ok(l)=>l,Err(_)=>break};
        let line=line.trim().to_string(); if line.is_empty(){continue;}
        let id=parse_id(&line);
        let n=match parse_n(&line){Some(n)=>n,None=>continue};
        let elapsed=global_start.elapsed();
        if elapsed>=time_limit {
            writeln!(out,"{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}",id).unwrap();
            out.flush().unwrap(); continue;
        }
        let remaining=time_limit-elapsed;
        let per_q=remaining.min(Duration::from_secs_f64(tl*0.99));
        let deadline=Instant::now()+per_q;
        match factor_number(&n,deadline,&stop) {
            Some(p) => {
                let q=&n/&p;
                let (lo,hi)=if p<q{(p,q)}else{(q,p)};
                writeln!(out,"{{\"id\": \"{}\", \"answer\": \"{} {}\"}}",id,lo,hi).unwrap();
            }
            None => {
                if global_start.elapsed()>=time_limit {
                    writeln!(out,"{{\"id\": \"{}\", \"answer\": null, \"timeout\": true}}",id).unwrap();
                } else {
                    writeln!(out,"{{\"id\": \"{}\", \"answer\": null}}",id).unwrap();
                }
            }
        }
        out.flush().unwrap();
    }
}
