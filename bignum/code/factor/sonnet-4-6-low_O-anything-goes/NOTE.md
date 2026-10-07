Everything working correctly. The solution is ready.

**Summary of approach:**

- **Small numbers (≤ u64):** Brent-variant Pollard's rho with u64/u128 arithmetic and deterministic Miller-Rabin primality testing — handles d up to ~10 instantly.

- **Large numbers:** `rusqsieve` (SIQS — Self-Initializing Quadratic Sieve), the fastest pure-Rust SIQS library available. Key optimizations:
  1. **Size-dispatched Natural type**: dispatch to `Natural<4>` (256-bit), `Natural<5>` (320-bit), etc. based on input bit length — using the smallest sufficient type reduces all inner-loop arithmetic overhead, giving ~1.65× speedup over always using `Natural<8>`.
  2. **All available cores** via `available_parallelism()`.
  3. **Progress callback with deadline** for clean cancellation when time is nearly up.
  4. **Thread + channel** for hard timeout enforcement.

**Expected performance (Apple M4, 10 cores):**
| d (digits per prime) | n bits | typical time |
|---|---|---|
| 32 | ~213 | ~1s ✓ |
| 38 | ~253 | ~11s ✓ |
| 40 | ~266 | 30–55s ✓ |
| 41 | ~272 | 51–75s ✗ (some fail) |

**Expected score: d = 40** (80-digit semiprimes with 40-digit factors).

Sources:
- [rusqsieve 0.3.0](https://docs.rs/rusqsieve/0.3.0)
- [rusqsieve changelog](https://docs.rs/crate/rusqsieve/0.5.0/source/CHANGELOG.md)