I built a multi-threaded quadratic sieve (SIQS) in `factor/`. It factors every test number up to about 82 digits (d=41) in around 26 seconds, so I expect a score of about **d=41**. d=42 is borderline: one 84-digit number took 42s, but another timed out at 58s, so not all 16 would pass.

The final build is in place and gives correct answers on all 36 samples up to d=32, 42 random numbers from d=5 to d=28, and a d=35 number.

**How it works**
- **Small numbers:** trial division by primes below 10,000, a perfect-square check (handles p = q), then Pollard–Brent rho for n up to 80 bits.
- **Larger numbers:** SIQS on all 10 cores, with one sieving worker per core and a collector thread.
  - It picks a small multiplier for n that gives a better set of sieving primes.
  - It switches cheaply between many related polynomials, so each one costs little to set up.
  - Sieving skips primes below 256 and processes 64KB blocks. The largest primes are handled without branches.
  - Candidates are checked by cheap divisibility tests. Hopeless ones are rejected early using the sieve value, so most cost almost nothing.
  - Leftover factors up to 150× the largest base prime are kept, and pairs sharing one are combined.
- **Final step:** the sieve threads pause while it solves the binary matrix (2–3s at 84 digits). If that fails to split n, it collects more relations and retries.
- **Time limit:** it answers at T − 1.2s if unfinished, prints the timeout line for anything unanswered, and exits with status 0.

**Measured times** (wall clock, 10 cores):

| Digits of n | d | Time |
|---|---|---|
| 64 | 32 | ~1s |
| 70 | 35 | ~2s |
| 76 | 38 | ~9s |
| 79 | 40 | ~18s |
| 82 | 41 | ~26s |
| 84 | 42 | 42s to over 58s, depending on the number |

These timings came from back-to-back runs on a hot machine, so they may vary a little.

**Review of the algorithm choice:** SIQS is the right method for this range under a 60-second limit. The number field sieve only pays off above roughly 100 digits and 