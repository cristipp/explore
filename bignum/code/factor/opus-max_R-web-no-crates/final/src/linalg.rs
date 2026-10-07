// Linear algebra over GF(2): find dependencies among columns of a sparse matrix.
// Block Lanczos (Montgomery) for large matrices, dense Gaussian elimination for small ones.

use crate::util::Rng;

/// cols[c] = list of row indices (odd exponents) for relation c. Returns list of dependencies,
/// each a list of column indices whose rows sum to zero mod 2.
pub fn find_dependencies(nrows: usize, cols: &[Vec<u32>]) -> Vec<Vec<usize>> {
    let ncols0 = cols.len();
    // singleton filtering
    let mut alive = vec![true; ncols0];
    let mut weight = vec![0u32; nrows];
    for c in cols {
        for &r in c {
            weight[r as usize] += 1;
        }
    }
    loop {
        let mut changed = false;
        for (ci, c) in cols.iter().enumerate() {
            if alive[ci] && c.iter().any(|&r| weight[r as usize] == 1) {
                alive[ci] = false;
                for &r in c {
                    weight[r as usize] -= 1;
                }
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // renumber rows
    let mut rowmap = vec![u32::MAX; nrows];
    let mut nr = 0usize;
    for r in 0..nrows {
        if weight[r] > 0 {
            rowmap[r] = nr as u32;
            nr += 1;
        }
    }
    let colidx: Vec<usize> = (0..ncols0).filter(|&c| alive[c]).collect();
    let mcols: Vec<Vec<u32>> = colidx
        .iter()
        .map(|&c| cols[c].iter().map(|&r| rowmap[r as usize]).collect())
        .collect();
    let nc = mcols.len();
    if nc == 0 {
        return vec![];
    }
    let deps_local: Vec<Vec<usize>> = if nc <= 1200 {
        gauss(nr, &mcols)
    } else {
        let mut res = vec![];
        for attempt in 0..4u64 {
            if let Some(d) = block_lanczos(nr, &mcols, 0x1234567 + attempt * 7919) {
                res = d;
                if !res.is_empty() {
                    break;
                }
            }
        }
        if res.is_empty() && nc <= 8000 {
            res = gauss(nr, &mcols);
        }
        res
    };
    deps_local
        .into_iter()
        .map(|d| d.into_iter().map(|c| colidx[c]).collect())
        .collect()
}

fn gauss(nrows: usize, cols: &[Vec<u32>]) -> Vec<Vec<usize>> {
    let nc = cols.len();
    let w1 = (nrows + 63) / 64;
    let w2 = (nc + 63) / 64;
    let w = w1 + w2;
    let mut m = vec![0u64; nc * w];
    for (ci, c) in cols.iter().enumerate() {
        let row = &mut m[ci * w..(ci + 1) * w];
        for &r in c {
            row[r as usize / 64] ^= 1u64 << (r % 64);
        }
        row[w1 + ci / 64] |= 1u64 << (ci % 64);
    }
    let mut used = vec![false; nc];
    for bit in 0..nrows {
        let wi = bit / 64;
        let mask = 1u64 << (bit % 64);
        let mut piv = usize::MAX;
        for i in 0..nc {
            if !used[i] && m[i * w + wi] & mask != 0 {
                piv = i;
                break;
            }
        }
        if piv == usize::MAX {
            continue;
        }
        used[piv] = true;
        let prow: Vec<u64> = m[piv * w..(piv + 1) * w].to_vec();
        for i in 0..nc {
            if i != piv && !used[i] && m[i * w + wi] & mask != 0 {
                let row = &mut m[i * w..(i + 1) * w];
                for k in wi..w {
                    row[k] ^= prow[k];
                }
            }
        }
    }
    let mut deps = vec![];
    for i in 0..nc {
        if used[i] {
            continue;
        }
        let row = &m[i * w..(i + 1) * w];
        if row[..w1].iter().all(|&x| x == 0) {
            let mut d = vec![];
            for k in 0..nc {
                if row[w1 + k / 64] >> (k % 64) & 1 == 1 {
                    d.push(k);
                }
            }
            if !d.is_empty() {
                deps.push(d);
            }
        }
        if deps.len() >= 64 {
            break;
        }
    }
    deps
}

struct Sparse {
    nrows: usize,
    ncols: usize,
    start: Vec<u32>,
    rows: Vec<u32>,
}

impl Sparse {
    fn mul_b(&self, x: &[u64]) -> Vec<u64> {
        let mut out = vec![0u64; self.nrows];
        for c in 0..self.ncols {
            let xc = x[c];
            for &r in &self.rows[self.start[c] as usize..self.start[c + 1] as usize] {
                out[r as usize] ^= xc;
            }
        }
        out
    }
    fn mul_bt(&self, y: &[u64], out: &mut [u64]) {
        for c in 0..self.ncols {
            let mut acc = 0u64;
            for &r in &self.rows[self.start[c] as usize..self.start[c + 1] as usize] {
                acc ^= y[r as usize];
            }
            out[c] = acc;
        }
    }
    fn mul_a(&self, x: &[u64], out: &mut [u64]) {
        let t = self.mul_b(x);
        self.mul_bt(&t, out);
    }
}

type M64 = [u64; 64];

fn mul_64x64(a: &M64, b: &M64) -> M64 {
    let mut c = [0u64; 64];
    for i in 0..64 {
        let mut w = a[i];
        let mut acc = 0u64;
        while w != 0 {
            acc ^= b[w.trailing_zeros() as usize];
            w &= w - 1;
        }
        c[i] = acc;
    }
    c
}

/// x^T y (64x64)
fn inner(x: &[u64], y: &[u64]) -> M64 {
    let mut t = vec![[0u64; 256]; 8];
    for k in 0..x.len() {
        let xv = x[k];
        let yv = y[k];
        if xv == 0 {
            continue;
        }
        for b in 0..8 {
            t[b][((xv >> (8 * b)) & 0xff) as usize] ^= yv;
        }
    }
    let mut c = [0u64; 64];
    for b in 0..8 {
        for j in 0..8 {
            let mut acc = 0u64;
            for v in 0..256usize {
                if (v >> j) & 1 == 1 {
                    acc ^= t[b][v];
                }
            }
            c[8 * b + j] = acc;
        }
    }
    c
}

/// out ^= v * m
fn mul_nx64_acc(v: &[u64], m: &M64, out: &mut [u64]) {
    let mut t = vec![[0u64; 256]; 8];
    for b in 0..8 {
        for x in 1..256usize {
            t[b][x] = t[b][x & (x - 1)] ^ m[8 * b + x.trailing_zeros() as usize];
        }
    }
    for k in 0..v.len() {
        let w = v[k];
        out[k] ^= t[0][(w & 0xff) as usize]
            ^ t[1][((w >> 8) & 0xff) as usize]
            ^ t[2][((w >> 16) & 0xff) as usize]
            ^ t[3][((w >> 24) & 0xff) as usize]
            ^ t[4][((w >> 32) & 0xff) as usize]
            ^ t[5][((w >> 40) & 0xff) as usize]
            ^ t[6][((w >> 48) & 0xff) as usize]
            ^ t[7][((w >> 56) & 0xff) as usize];
    }
}

fn find_nonsingular_sub(t: &M64, s: &mut Vec<usize>, last_s: &[usize], w: &mut M64) -> usize {
    let mut m = [[0u64; 2]; 64];
    for i in 0..64 {
        m[i][0] = t[i];
        m[i][1] = 1u64 << i;
    }
    let mut ord = vec![0usize; 64];
    let mut mask = 0u64;
    let mut cols = 64;
    for &ls in last_s {
        cols -= 1;
        ord[cols] = ls;
        mask |= 1u64 << ls;
    }
    let mut dim = 0;
    for i in 0..64 {
        if mask & (1u64 << i) == 0 {
            ord[dim] = i;
            dim += 1;
        }
    }
    s.clear();
    for i in 0..64 {
        let bit = 1u64 << ord[i];
        // find pivot
        let mut found = false;
        for j in i..64 {
            if m[ord[j]][0] & bit != 0 {
                m.swap(ord[i], ord[j]);
                found = true;
                break;
            }
        }
        if found {
            let pi = ord[i];
            let prow = m[pi];
            for j in 0..64 {
                let rj = ord[j];
                if rj != pi && m[rj][0] & bit != 0 {
                    m[rj][0] ^= prow[0];
                    m[rj][1] ^= prow[1];
                }
            }
            s.push(ord[i]);
            continue;
        }
        let mut found2 = false;
        for j in i..64 {
            if m[ord[j]][1] & bit != 0 {
                m.swap(ord[i], ord[j]);
                found2 = true;
                break;
            }
        }
        if !found2 {
            return 0;
        }
        let pi = ord[i];
        let prow = m[pi];
        for j in 0..64 {
            let rj = ord[j];
            if rj != pi && m[rj][1] & bit != 0 {
                m[rj][0] ^= prow[0];
                m[rj][1] ^= prow[1];
            }
        }
        m[pi] = [0, 0];
    }
    for i in 0..64 {
        w[i] = m[i][1];
    }
    s.len()
}

fn block_lanczos(nrows: usize, cols: &[Vec<u32>], seed: u64) -> Option<Vec<Vec<usize>>> {
    let n = cols.len();
    let mut start = Vec::with_capacity(n + 1);
    let mut rows = Vec::new();
    start.push(0u32);
    for c in cols {
        rows.extend_from_slice(c);
        start.push(rows.len() as u32);
    }
    let a = Sparse { nrows, ncols: n, start, rows };
    let mut rng = Rng(seed);
    let mut x: Vec<u64> = (0..n).map(|_| rng.next()).collect();
    let mut v0 = vec![0u64; n];
    a.mul_a(&x, &mut v0);
    let v0save = v0.clone();
    let mut v1 = vec![0u64; n];
    let mut v2 = vec![0u64; n];
    let mut vnext = vec![0u64; n];
    let mut av = vec![0u64; n];
    let mut vt_a_v1: M64 = [0; 64];
    let mut vt_a2_v1: M64 = [0; 64];
    let mut winv1: M64 = [0; 64];
    let mut winv2: M64 = [0; 64];
    let mut s1: Vec<usize> = (0..64).collect();
    let mut s0: Vec<usize> = Vec::with_capacity(64);
    let mut mask1: u64 = !0;
    let max_iter = n / 60 + 50;
    let mut iter = 0;
    loop {
        iter += 1;
        if iter > max_iter {
            return None;
        }
        a.mul_a(&v0, &mut av);
        let vt_a_v0 = inner(&v0, &av);
        let vt_a2_v0 = inner(&av, &av);
        if vt_a_v0.iter().all(|&w| w == 0) {
            break;
        }
        let mut winv0: M64 = [0; 64];
        let dim0 = find_nonsingular_sub(&vt_a_v0, &mut s0, &s1, &mut winv0);
        if dim0 == 0 {
            return None;
        }
        let mut mask0 = 0u64;
        for &c in &s0 {
            mask0 |= 1u64 << c;
        }
        if mask0 | mask1 != !0 {
            return None;
        }
        for k in 0..n {
            vnext[k] = av[k] & mask0;
        }
        let vt_v0 = inner(&v0, &v0save);
        let mut d: M64 = [0; 64];
        for i in 0..64 {
            d[i] = (vt_a2_v0[i] & mask0) ^ vt_a_v0[i];
        }
        let mut d = mul_64x64(&winv0, &d);
        for i in 0..64 {
            d[i] ^= 1u64 << i;
        }
        let mut e = mul_64x64(&winv1, &vt_a_v0);
        for i in 0..64 {
            e[i] &= mask0;
        }
        let mut f = mul_64x64(&vt_a_v1, &winv1);
        for i in 0..64 {
            f[i] ^= 1u64 << i;
        }
        let f = mul_64x64(&winv2, &f);
        let mut f2: M64 = [0; 64];
        for i in 0..64 {
            f2[i] = ((vt_a2_v1[i] & mask1) ^ vt_a_v1[i]) & mask0;
        }
        let f = mul_64x64(&f, &f2);
        mul_nx64_acc(&v0, &d, &mut vnext);
        mul_nx64_acc(&v1, &e, &mut vnext);
        mul_nx64_acc(&v2, &f, &mut vnext);
        let dd = mul_64x64(&winv0, &vt_v0);
        mul_nx64_acc(&v0, &dd, &mut x);
        // rotate
        std::mem::swap(&mut v2, &mut v1);
        std::mem::swap(&mut v1, &mut v0);
        std::mem::swap(&mut v0, &mut vnext);
        winv2 = winv1;
        winv1 = winv0;
        vt_a_v1 = vt_a_v0;
        vt_a2_v1 = vt_a2_v0;
        std::mem::swap(&mut s1, &mut s0);
        mask1 = mask0;
    }
    // combine x and v0 into nullspace vectors of B
    let bx = a.mul_b(&x);
    let bv = a.mul_b(&v0);
    let words = (nrows + 63) / 64;
    let mut colv = vec![vec![0u64; words]; 128];
    for r in 0..nrows {
        let mut w = bx[r];
        while w != 0 {
            let c = w.trailing_zeros() as usize;
            colv[c][r / 64] |= 1u64 << (r % 64);
            w &= w - 1;
        }
        let mut w = bv[r];
        while w != 0 {
            let c = w.trailing_zeros() as usize + 64;
            colv[c][r / 64] |= 1u64 << (r % 64);
            w &= w - 1;
        }
    }
    let mut tags: Vec<u128> = (0..128).map(|c| 1u128 << c).collect();
    let mut pivot = [false; 128];
    for wi in 0..words {
        for b in 0..64 {
            let bit = 1u64 << b;
            let mut p = usize::MAX;
            for c in 0..128 {
                if !pivot[c] && colv[c][wi] & bit != 0 {
                    p = c;
                    break;
                }
            }
            if p == usize::MAX {
                continue;
            }
            pivot[p] = true;
            let pv = colv[p].clone();
            let pt = tags[p];
            for c in 0..128 {
                if c != p && colv[c][wi] & bit != 0 {
                    for k in wi..words {
                        colv[c][k] ^= pv[k];
                    }
                    tags[c] ^= pt;
                }
            }
        }
    }
    let mut deps_bits = vec![0u64; n];
    let mut ndeps = 0;
    for c in 0..128 {
        if pivot[c] || ndeps >= 64 {
            continue;
        }
        let tlo = tags[c] as u64;
        let thi = (tags[c] >> 64) as u64;
        let mut nz = false;
        let bitpos = 1u64 << ndeps;
        for k in 0..n {
            let par = ((x[k] & tlo).count_ones() ^ (v0[k] & thi).count_ones()) & 1;
            if par == 1 {
                deps_bits[k] |= bitpos;
                nz = true;
            }
        }
        if nz {
            ndeps += 1;
        }
    }
    if ndeps == 0 {
        return None;
    }
    // verify
    let chk = a.mul_b(&deps_bits);
    let mut bad = 0u64;
    for &w in &chk {
        bad |= w;
    }
    let mut deps = vec![];
    for j in 0..ndeps {
        if bad >> j & 1 == 1 {
            continue;
        }
        let d: Vec<usize> = (0..n).filter(|&k| deps_bits[k] >> j & 1 == 1).collect();
        if !d.is_empty() {
            deps.push(d);
        }
    }
    Some(deps)
}
