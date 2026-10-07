The factoring program is in `./factor`. It builds with plain `cargo build --release` and has no dependencies at all.

I expect it to pass d=40 and fail d=41, so I'd put the score around 40. The d=40 times below come from my own random semiprimes. I did not run 16 of them per size, so the tail risk is untested.

| Size | Times (10 threads) | Notes |
|---|---|---|
| d ≤ 34 | under 2 s | all sample numbers correct |
| d=38 | about 10 s | |
| d=40 | 29–37 s | well inside 60 s |
| d=41 | 55 s on the first number | the second number timed out in my 90 s test |

With `--time-limit 8` on d=40 numbers it printed the timeout lines and exited with status 0 at 7.85 s. The watchdog stops about 1 s before the limit at T=60.

**Approach**
- **Small inputs:** numbers below 2^64 go through trial division, a perfect-square check, and Pollard–Brent rho. Anything larger, including all the large sizes, goes to SIQS.
- **Bignums:** the arithmetic is my own u64-limb implementation. I wrote it myself because the num-bigint crate could not be downloaded here.
- **SIQS setup:** it picks a Knuth–Schroeder multiplier and builds the factor base from Tonelli–Shanks square roots. Each polynomial's `a` is a product of about 9–12 random factor-base primes. Gray-code switching of `b` gives hundreds of polynomials per `a`, updating the roots with SIMD-friendly code.
- **Sieve:** it uses 128K-byte blocks that fit in L1. Primes close to or above the block size are sieved without branches. Candidates are checked by fast modular reduction and trial division of the exact cofactor.
- **Relations:** it keeps single-large-prime relations and pairs them by their shared large prime. 10 worker threads sieve with independent random `a` values.
- **Linear algebra:** it removes singleton columns, then runs Gaussian elimination over GF(2) using the Four-Russians method with 8-column strips, parallelised. The workers pause while it runs. It then back-substitutes for null-space vectors and tries each one until a gcd 