The program factors balanced semiprimes up to d=42 (84-digit n) in under 50 seconds in every test I ran. I expect a score of **42**; if one of the 16 graded numbers is unusually slow, it drops to 41.

**Approach.** The core is a self-initialising quadratic sieve (SIQS), taken from the crates.io crate `rusqsieve` 0.5.0. That was the strongest option I could reach: GitHub is blocked here, so `yamaquasi` was out, and a sieve written from scratch in an hour wouldn't have matched a mature one. I copied the crate into `factor/vendor/rusqsieve` (allowed by its Apache/MPL licence) so I could change it, then tuned it on this M4:
- **Sieve features at smaller sizes:** the crate turns on its best sieving features (multiplier choice, Q2 polynomials, resieving, rounded scores, dense prefix) only above 289 bits. Turning them on from 250 bits gave about 25% at the sizes that matter.
- **Thresholds and factor base:** a small-prime skip of 100, deeper sieve thresholds (−4, −6 or −8 depending on size), and a 900k factor base for 273–280 bits. That last change turned a 279-bit timeout into a 48.7s pass.
- **Build:** `target-cpu=native`, a code-alignment flag, fat LTO and `codegen-units=1`.
- **Wrapper (`src/main.rs`):** reads JSON lines, keeping large `n` values exact; factors on all 10 cores in a worker thread. The main thread stops at T − 0.6s, prints timeout lines for anything unanswered, and exits 0. It also retries if the sieve fails.

**Measured on fresh balanced semiprimes:**

| d (n digits) | Time per number | Result |
|---|---|---|
| ≤ 32 | ≤ 0.9s | all pass |
| 36 (72) | 4–5.5s | all pass |
| 40 (80) | 18–21s (was 30–41s before tuning) | all pass |
| 41 (82) | 20–43s | 12/12 pass |
| 42 (84) | 34–50s | 8/8 pass |
| 43+ | estimated 70s or more | not reachable |

The risk is d=42: the slowest run was 49.6s against the ~59.4s cutoff, and run-to-run noise is about ±10%. All 16 graded numbers should pass, but one outlier would make the score 41.

Things I tried that didn't help: 