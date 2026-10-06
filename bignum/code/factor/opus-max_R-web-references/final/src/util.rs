// Small number-theory helpers.

#[inline]
pub fn mulmod(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

pub fn powmod(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64 % m;
    b %= m;
    while e > 0 {
        if e & 1 == 1 {
            r = mulmod(r, b, m);
        }
        b = mulmod(b, b, m);
        e >>= 1;
    }
    r
}

/// Inverse of a modulo m (gcd(a,m)=1 assumed). Returns 0 if not invertible.
pub fn inv_mod(a: u64, m: u64) -> u64 {
    let (mut old_r, mut r) = ((a % m) as i128, m as i128);
    let (mut old_s, mut s) = (1i128, 0i128);
    while r != 0 {
        let q = old_r / r;
        let t = old_r - q * r;
        old_r = r;
        r = t;
        let t = old_s - q * s;
        old_s = s;
        s = t;
    }
    if old_r != 1 {
        return 0;
    }
    let mut v = old_s % m as i128;
    if v < 0 {
        v += m as i128;
    }
    v as u64
}

/// Square root of a mod prime p (a must be a QR or 0).
pub fn sqrt_mod(a: u64, p: u64) -> u64 {
    let a = a % p;
    if a == 0 {
        return 0;
    }
    if p == 2 {
        return a;
    }
    if p % 4 == 3 {
        return powmod(a, (p + 1) / 4, p);
    }
    // Tonelli-Shanks
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
            tt = mulmod(tt, tt, p);
            i += 1;
        }
        let b = powmod(c, 1 << (m - i - 1), p);
        m = i;
        c = mulmod(b, b, p);
        t = mulmod(t, c, p);
        r = mulmod(r, b, p);
    }
    r
}

pub fn is_prime_u64(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 {
            return n == p;
        }
    }
    let mut d = n - 1;
    let mut s = 0;
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    'outer: for &a in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 1..s {
            x = mulmod(x, x, n);
            if x == n - 1 {
                continue 'outer;
            }
        }
        return false;
    }
    true
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Pollard-Brent rho; returns a nontrivial factor of composite n (n odd, not a prime power ideally).
pub fn rho_u64(n: u64) -> u64 {
    if n % 2 == 0 {
        return 2;
    }
    let mut c = 1u64;
    loop {
        let f = |x: u64| (mulmod(x, x, n) + c) % n;
        let mut y = 2u64;
        let mut r = 1u64;
        let mut q = 1u64;
        let mut g;
        let mut x;
        let mut ys = 0;
        let m = 128;
        loop {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k = 0;
            loop {
                ys = y;
                for _ in 0..m.min(r - k) {
                    y = f(y);
                    let d = if x > y { x - y } else { y - x };
                    q = mulmod(q, d, n);
                }
                g = gcd(q, n);
                k += m;
                if k >= r || g != 1 {
                    break;
                }
            }
            r *= 2;
            if g != 1 || r > (1 << 40) {
                break;
            }
        }
        if g == n {
            loop {
                ys = f(ys);
                let d = if x > ys { x - ys } else { ys - x };
                g = gcd(d, n);
                if g != 1 {
                    break;
                }
            }
        }
        if g != n && g != 1 {
            return g;
        }
        c += 1;
    }
}

pub fn primes_up_to(n: usize) -> Vec<u32> {
    let mut sieve = vec![true; n + 1];
    sieve[0] = false;
    if n >= 1 {
        sieve[1] = false;
    }
    let mut i = 2;
    while i * i <= n {
        if sieve[i] {
            let mut j = i * i;
            while j <= n {
                sieve[j] = false;
                j += i;
            }
        }
        i += 1;
    }
    (0..=n).filter(|&i| sieve[i]).map(|i| i as u32).collect()
}

/// x mod p for x given as little-endian u32 limbs.
#[inline]
pub fn mod_limbs(x: &[u32], p: u32) -> u32 {
    let p = p as u64;
    let mut r = 0u64;
    for &l in x.iter().rev() {
        r = ((r << 32) | l as u64) % p;
    }
    r as u32
}

/// If p divides x (little-endian u32 limbs), divide in place and return true.
#[inline]
pub fn try_div_limbs(x: &mut Vec<u32>, p: u32) -> bool {
    if mod_limbs(x, p) != 0 {
        return false;
    }
    let p = p as u64;
    let mut r = 0u64;
    for l in x.iter_mut().rev() {
        let cur = (r << 32) | *l as u64;
        *l = (cur / p) as u32;
        r = cur % p;
    }
    while let Some(&0) = x.last() {
        x.pop();
    }
    true
}

pub struct Rng(pub u64);
impl Rng {
    #[inline]
    pub fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}
