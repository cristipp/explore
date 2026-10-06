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

