use std::cmp::Ordering;

pub type Big = Vec<u64>;

pub fn norm(v: &mut Big) {
    while let Some(&0) = v.last() {
        v.pop();
    }
}

pub fn from_u64(x: u64) -> Big {
    if x == 0 { vec![] } else { vec![x] }
}

pub fn cmp_big(a: &Big, b: &Big) -> Ordering {
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    Ordering::Equal
}

pub fn add_big(a: &Big, b: &Big) -> Big {
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut r = Vec::with_capacity(a.len() + 1);
    let mut c = 0u64;
    for i in 0..a.len() {
        let y = if i < b.len() { b[i] } else { 0 };
        let (s1, c1) = a[i].overflowing_add(y);
        let (s2, c2) = s1.overflowing_add(c);
        r.push(s2);
        c = (c1 | c2) as u64;
    }
    if c > 0 {
        r.push(c);
    }
    r
}

// a >= b required
pub fn sub_big(a: &Big, b: &Big) -> Big {
    let mut r = Vec::with_capacity(a.len());
    let mut br = 0u64;
    for i in 0..a.len() {
        let y = if i < b.len() { b[i] } else { 0 };
        let (s1, c1) = a[i].overflowing_sub(y);
        let (s2, c2) = s1.overflowing_sub(br);
        r.push(s2);
        br = (c1 | c2) as u64;
    }
    norm(&mut r);
    r
}

pub fn mul_big(a: &Big, b: &Big) -> Big {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut r = vec![0u64; a.len() + b.len()];
    for i in 0..a.len() {
        let mut carry = 0u128;
        let ai = a[i] as u128;
        for j in 0..b.len() {
            let t = ai * (b[j] as u128) + r[i + j] as u128 + carry;
            r[i + j] = t as u64;
            carry = t >> 64;
        }
        r[i + b.len()] = carry as u64;
    }
    norm(&mut r);
    r
}

pub fn mul_small(a: &Big, m: u64) -> Big {
    if a.is_empty() || m == 0 {
        return vec![];
    }
    let mut r = Vec::with_capacity(a.len() + 1);
    let mut carry = 0u128;
    for &x in a {
        let t = (x as u128) * (m as u128) + carry;
        r.push(t as u64);
        carry = t >> 64;
    }
    if carry > 0 {
        r.push(carry as u64);
    }
    r
}

pub fn add_small(a: &Big, m: u64) -> Big {
    add_big(a, &from_u64(m))
}

pub fn rem32(a: &[u64], p: u32) -> u32 {
    let p = p as u64;
    let mut r = 0u64;
    for &l in a.iter().rev() {
        r = ((r << 32) | (l >> 32)) % p;
        r = ((r << 32) | (l & 0xffff_ffff)) % p;
    }
    r as u32
}

pub fn div32(a: &Big, p: u32) -> (Big, u32) {
    let p = p as u64;
    let mut r = 0u64;
    let mut q = vec![0u64; a.len()];
    for i in (0..a.len()).rev() {
        let l = a[i];
        let x = (r << 32) | (l >> 32);
        let qh = x / p;
        r = x % p;
        let y = (r << 32) | (l & 0xffff_ffff);
        let ql = y / p;
        r = y % p;
        q[i] = (qh << 32) | ql;
    }
    norm(&mut q);
    (q, r as u32)
}

pub fn divrem_small(a: &Big, p: u64) -> (Big, u64) {
    let mut r = 0u128;
    let mut q = vec![0u64; a.len()];
    for i in (0..a.len()).rev() {
        let x = (r << 64) | a[i] as u128;
        q[i] = (x / p as u128) as u64;
        r = x % p as u128;
    }
    norm(&mut q);
    (q, r as u64)
}

pub fn shl_bits(a: &Big, s: usize) -> Big {
    if a.is_empty() {
        return vec![];
    }
    let limbs = s / 64;
    let b = s % 64;
    let mut r = vec![0u64; limbs];
    if b == 0 {
        r.extend_from_slice(a);
    } else {
        let mut carry = 0u64;
        for &x in a {
            r.push((x << b) | carry);
            carry = x >> (64 - b);
        }
        if carry > 0 {
            r.push(carry);
        }
    }
    r
}

pub fn shr_bits(a: &Big, s: usize) -> Big {
    let limbs = s / 64;
    let b = s % 64;
    if limbs >= a.len() {
        return vec![];
    }
    let mut r = Vec::with_capacity(a.len() - limbs);
    for i in limbs..a.len() {
        let lo = a[i] >> b;
        let hi = if b > 0 && i + 1 < a.len() { a[i + 1] << (64 - b) } else { 0 };
        r.push(lo | hi);
    }
    norm(&mut r);
    r
}

pub fn bits(a: &Big) -> usize {
    match a.last() {
        None => 0,
        Some(&t) => a.len() * 64 - t.leading_zeros() as usize,
    }
}

pub fn log2_big(a: &Big) -> f64 {
    let b = bits(a);
    if b == 0 {
        return 0.0;
    }
    if b <= 64 {
        return (a[0] as f64).log2();
    }
    let top = shr_bits(a, b - 64);
    (top[0] as f64).log2() + (b - 64) as f64
}

pub fn divrem(a: &Big, b: &Big) -> (Big, Big) {
    assert!(!b.is_empty());
    if cmp_big(a, b) == Ordering::Less {
        return (vec![], a.clone());
    }
    if b.len() == 1 {
        let (q, r) = divrem_small(a, b[0]);
        return (q, from_u64(r));
    }
    let s = b[b.len() - 1].leading_zeros() as usize;
    let v = shl_bits(b, s);
    let mut u = shl_bits(a, s);
    u.resize(a.len() + 1, 0);
    let n = v.len();
    let m = a.len() - n;
    let mut q = vec![0u64; m + 1];
    for j in (0..=m).rev() {
        let num = ((u[j + n] as u128) << 64) | u[j + n - 1] as u128;
        let mut qhat = num / (v[n - 1] as u128);
        let mut rhat = num % (v[n - 1] as u128);
        while (qhat >> 64) != 0 || qhat * (v[n - 2] as u128) > ((rhat << 64) | u[j + n - 2] as u128) {
            qhat -= 1;
            rhat += v[n - 1] as u128;
            if (rhat >> 64) != 0 {
                break;
            }
        }
        let mut borrow: i128 = 0;
        let mut carry: u128 = 0;
        for i in 0..n {
            let p = qhat * (v[i] as u128) + carry;
            carry = p >> 64;
            let sub = (u[i + j] as i128) - borrow - ((p as u64) as i128);
            u[i + j] = sub as u64;
            borrow = if sub < 0 { 1 } else { 0 };
        }
        let sub = (u[j + n] as i128) - borrow - (carry as i128);
        u[j + n] = sub as u64;
        if sub < 0 {
            qhat -= 1;
            let mut c = 0u128;
            for i in 0..n {
                let t = u[i + j] as u128 + v[i] as u128 + c;
                u[i + j] = t as u64;
                c = t >> 64;
            }
            u[j + n] = u[j + n].wrapping_add(c as u64);
        }
        q[j] = qhat as u64;
    }
    norm(&mut q);
    u.truncate(n);
    norm(&mut u);
    let r = shr_bits(&u, s);
    (q, r)
}

pub fn rem_big(a: &Big, b: &Big) -> Big {
    divrem(a, b).1
}

pub fn mulmod(a: &Big, b: &Big, n: &Big) -> Big {
    rem_big(&mul_big(a, b), n)
}

pub fn powmod_small(base: &Big, mut e: u64, n: &Big) -> Big {
    let mut r = vec![1u64];
    let mut b = rem_big(base, n);
    while e > 0 {
        if e & 1 == 1 {
            r = mulmod(&r, &b, n);
        }
        e >>= 1;
        if e > 0 {
            b = mulmod(&b, &b, n);
        }
    }
    r
}

pub fn gcd_big(a: &Big, b: &Big) -> Big {
    let mut a = a.clone();
    let mut b = b.clone();
    while !b.is_empty() {
        let r = rem_big(&a, &b);
        a = b;
        b = r;
    }
    a
}

pub fn isqrt(n: &Big) -> Big {
    if n.is_empty() {
        return vec![];
    }
    let mut x = shl_bits(&vec![1], (bits(n) + 1) / 2);
    loop {
        let (q, _) = divrem(n, &x);
        let y = shr_bits(&add_big(&x, &q), 1);
        if cmp_big(&y, &x) != Ordering::Less {
            return x;
        }
        x = y;
    }
}

pub fn from_dec(s: &str) -> Big {
    let mut r: Big = vec![];
    for c in s.bytes() {
        if c.is_ascii_digit() {
            r = mul_small(&r, 10);
            r = add_small(&r, (c - b'0') as u64);
        }
    }
    r
}

pub fn to_dec(a: &Big) -> String {
    if a.is_empty() {
        return "0".to_string();
    }
    let mut parts = vec![];
    let mut x = a.clone();
    while !x.is_empty() {
        let (q, r) = divrem_small(&x, 10_000_000_000_000_000_000);
        parts.push(r);
        x = q;
    }
    let mut s = format!("{}", parts.pop().unwrap());
    while let Some(p) = parts.pop() {
        s.push_str(&format!("{:019}", p));
    }
    s
}
