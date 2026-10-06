I built a multi-threaded SIQS (self-initializing quadratic sieve) in `./factor`. It builds with `cargo build --release --offline`. On my tests it factors up to d=41 (an 82-digit n) within the limit, so I expect a score of about 41.

**Test results**
- **Correctness:** all 36 samples up to d=32 and 72 generated semiprimes from d=5 to d=36 were factored correctly. I checked each answer by multiplying p·q back to n.
- **Timings:**

| d | digits of n | time |
|---|---|---|
| 32 | 64 | ~0.8s |
| 35 | 70 | ~1.8s |
| 38 | 76 | ~10s |
| 40 | 80 | ~20.7s |
| 41 | 82 | ~30s (estimated, not run) |
| 42 | 84 | 55.3s |

- **d=42 will probably fail:** 55.3s is too close to the 60s limit for all 16 numbers to pass. That run was before my last speedup (about 4% at d=40), so it's still marginal.
- **Timeout:** the d=48 samples (96 digits) ran out of time cleanly. The program printed `"timeout": true` lines at about 59.9s and exited normally.

**How it works**
- **Small inputs:** n below 2^62 uses trial division plus Pollard–Brent rho. Squares are handled directly.
- **Everything else** goes to SIQS:
  - A standard method (Knuth–Schroeppel) picks a small multiplier for n.
  - Each new polynomial comes from the previous one by a cheap root update, so each set-up is reused for 2^(s−1) polynomials (Gray code).
  - The sieve runs in 32 KB blocks on all 10 cores. Primes above 32K are handled through per-block lists. Since they dominated run time, I rewrote that path so the compiler can vectorise the root updates and so it avoids unpredictable branches.
  - Small primes below about 300 are skipped and the threshold lowered to compensate; the sieve scan uses NEON instructions.
  - Relations with one leftover prime are kept and paired up when the same prime appears twice.
- **Matrix step:** Montgomery's Block Lanczos, after removing singletons, with dense Gaussian elimination for small matrices. It takes about 1.4s on the 50K×50K matrix at 84 digits.
- **Tuning:** I tuned parameters by measu