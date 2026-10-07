mod big;
mod siqs;

use big::*;
use std::io::{self, BufRead, Write};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

fn mulmod64(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

fn gcd64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn rho64(n: u64) -> u64 {
    if n % 2 == 0 {
        return 2;
    }
    let mut c = 1u64;
    loop {
        let f = |x: u64| ((x as u128 * x as u128 + c as u128) % n as u128) as u64;
        let (mut x, mut y, mut q, mut g) = (2u64, 2u64, 1u64, 1u64);
        let mut ys = 2u64;
        let mut r = 1u64;
        let m = 128;
        while g == 1 {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k = 0;
            while k < r && g == 1 {
                ys = y;
                for _ in 0..m.min(r - k) {
                    y = f(y);
                    q = mulmod64(q, x.abs_diff(y), n);
                }
                g = gcd64(q, n);
                k += m;
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

fn factor_small(n: u64) -> Option<(u64, u64)> {
    let mut p = 2u64;
    while p < 1000 && p * p <= n {
        if n % p == 0 {
            return Some((p, n / p));
        }
        p += 1;
    }
    let s = (n as f64).sqrt() as u64;
    for r in s.saturating_sub(1)..=s + 1 {
        if r > 1 && r * r == n {
            return Some((r, r));
        }
    }
    let g = rho64(n);
    let h = n / g;
    Some((g.min(h), g.max(h)))
}

fn factor(n: &Big, deadline: Instant, nthreads: usize) -> Option<(Big, Big)> {
    if n.len() <= 1 {
        let v = if n.is_empty() { 0 } else { n[0] };
        if v < 4 {
            return None;
        }
        let (a, b) = factor_small(v)?;
        return Some((from_u64(a), from_u64(b)));
    }
    let r = isqrt(n);
    if cmp_big(&mul_big(&r, &r), n) == std::cmp::Ordering::Equal {
        return Some((r.clone(), r));
    }
    for p in [2u32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
        if rem32(n, p) == 0 {
            let q = div32(n, p).0;
            return Some((from_u64(p as u64), q));
        }
    }
    let g = siqs::siqs(n, deadline, nthreads)?;
    let h = divrem(n, &g).0;
    if cmp_big(&g, &h) == std::cmp::Ordering::Greater { Some((h, g)) } else { Some((g, h)) }
}

fn parse_line(line: &str) -> Option<(String, String)> {
    let idp = line.find("\"id\"")?;
    let rest = &line[idp + 4..];
    let colon = rest.find(':')?;
    let rest = rest[colon + 1..].trim_start();
    let id_raw: String = if rest.starts_with('"') {
        let end = rest[1..].find('"')? + 2;
        rest[..end].to_string()
    } else {
        rest.chars().take_while(|c| *c != ',' && *c != '}' && !c.is_whitespace()).collect()
    };
    let np = line.find("\"n\"")?;
    let rest = &line[np + 3..];
    let colon = rest.find(':')?;
    let digits: String = rest[colon + 1..].trim_start().trim_start_matches('"').chars().take_while(|c| c.is_ascii_digit()).collect();
    Some((id_raw, digits))
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
    let mut inputs: Vec<(String, String)> = vec![];
    for line in io::stdin().lock().lines() {
        let Ok(line) = line else { break };
        if let Some(x) = parse_line(&line) {
            inputs.push(x);
        }
    }
    let margin = (tl * 0.02).clamp(0.15, 1.0);
    let hard = start + Duration::from_secs_f64((tl - margin).max(0.05));
    let pending: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(inputs.iter().map(|x| x.0.clone()).collect()));
    {
        let pending = pending.clone();
        std::thread::spawn(move || {
            loop {
                let now = Instant::now();
                if now >= hard {
                    break;
                }
                std::thread::sleep((hard - now).min(Duration::from_millis(20)));
            }
            let g = pending.lock().unwrap();
            let out = io::stdout();
            let mut o = out.lock();
            for id in g.iter() {
                let _ = writeln!(o, "{{\"id\": {}, \"answer\": null, \"timeout\": true}}", id);
            }
            let _ = o.flush();
            std::process::exit(0);
        });
    }
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(8);
    for (id, ns) in inputs.iter() {
        let n = from_dec(ns);
        let ans = factor(&n, hard, nthreads);
        let mut g = pending.lock().unwrap();
        if !g.contains(id) {
            continue;
        }
        let out = io::stdout();
        let mut o = out.lock();
        match ans {
            Some((p, q)) => {
                let _ = writeln!(o, "{{\"id\": {}, \"answer\": \"{} {}\"}}", id, to_dec(&p), to_dec(&q));
            }
            None => {
                let _ = writeln!(o, "{{\"id\": {}, \"answer\": null, \"timeout\": true}}", id);
            }
        }
        let _ = o.flush();
        if let Some(pos) = g.iter().position(|x| x == id) {
            g.remove(pos);
        }
    }
}
