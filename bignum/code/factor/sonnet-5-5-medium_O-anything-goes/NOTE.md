The factorer is in `./factor` and builds with `cargo build --release`. It should pass d=39 comfortably, and d=40 is likely but not certain. I'd guess the graded score is 39 or 40.

Measured times on this machine, per number:

| d | Number of tests | Time |
|---|---|---|
| ≤ 28 | 176 (all sample sizes up to d=32, plus generated ones) | all correct; 14.6 s total for the whole batch |
| 38 | 1 | about 12 s |
| 39 | 2 | 17–21 s |
| 40 | 2 | 31–36 s |

Each extra digit costs roughly 1.9× the time, so d=41 should land near 60 s and fail. The d=40 timings are from only two numbers. An unlucky multiplier or a larger-than-average n could still push the slowest of 16 past 60 s.

Timeout handling works: with a 5 s limit it printed `answer: null, timeout: true` for the unanswered inputs and exited with status 0.

**Approach**
- **n < 2^64:** Pollard rho (Brent).
- **Everything larger:** a self-initialising quadratic sieve (SIQS), the usual best method for balanced semiprimes of up to about 100 digits. GNFS only wins well beyond that.
- **Multithreaded sieving:** a Knuth–Schroeppel multiplier is chosen, and all 10 threads sieve in parallel, each on its own polynomials.
- **Large-prime variation:** partial relations with one or two large primes are combined by finding cycles in a graph of those primes. This took d=36 from about 16 s to about 6 s.
- **Linear algebra:** bit-matrix elimination using a lookup table over 8 pivot columns at a time, parallelised with rayon. It costs about 1.5–2 s at d=40.
- **Parameters:** factor-base size, sieve interval, thresholds and large-prime bounds were tuned empirically at d=34–40 and sit at a flat optimum.

Debug output only appears with `-v`; the tuning knobs are environment variables and default to the tuned values.