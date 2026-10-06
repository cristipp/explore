The program is in `./factor` and builds with `cargo build --release --offline`. On my tests it factors d=38 in about 18–31 s, but one d=40 number timed out at 60 s. I expect it to pass up to about d=38. d=39 is borderline, because the time varies by 1.5x or more between numbers of the same size.

**Approach**
- **Small inputs:** n below 2^64 goes to Pollard rho with `u128` arithmetic. n of 64 bits or more first gets trial division by primes under 1000 and a perfect-square check.
- **Main method:** a multi-threaded self-initializing quadratic sieve (SIQS).
  - **Factor base:** chosen with a Knuth–Schroeppel multiplier, using Tonelli–Shanks square roots.
  - **Sieve:** the polynomial coefficients `a` are picked at random per thread. The polynomials `b` are walked in Gray-code order, so each switch updates the roots with table lookups instead of big-integer work. The sieve uses `u8` log sums in 32 KB blocks, with the inner loop unrolled four hits at a time. Primes below 30 are skipped, and the threshold has a tuned slack.
  - **Candidates:** a candidate is trial-divided with fixed-size multiprecision integers, using the polynomial roots rather than a division per prime.
  - **Large primes:** relations with one large prime are kept and paired up into extra relations. Duplicates are removed.
  - **Linear algebra:** dense GF(2) elimination that tracks row history, with the row updates spread across threads for larger matrices. The program then tries each dependency with a gcd until one gives a factor. If none does, it collects more relations and retries.
- **Parameters:** factor-base size and sieve width follow a table by digit count, which I tuned by timing runs. Smaller sieve intervals were slightly faster at the sizes I tested.
- **Interface:** a reader thread feeds stdin lines to the solver. A watchdog thread prints `{"answer": null, "timeout": true}` for every unanswered id at about `T - 0.15` s, then exits with status 0. Answers print smallest-first and flush after 