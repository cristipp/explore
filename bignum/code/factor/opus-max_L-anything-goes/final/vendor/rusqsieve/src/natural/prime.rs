//! Random prime generation.
//!
//! Native builds only. The generator needs an operating-system entropy source, which
//! `wasm32-unknown-unknown` does not define — the browser's is reached through an import the raw
//! Wasm ABI in [`crate::wasm`] deliberately does not declare — so the whole module, and the `rand`
//! dependency behind it, is scoped to `unix` and `windows`.
//!
//! Acceptance is decided by the same [`is_probable_prime`] the factorization pipeline uses on every
//! cofactor it recovers, with the same default configuration: Baillie-PSW above `2^64`, the proven
//! seven-base witness set below it, then sixteen Miller-Rabin rounds. A value this returns and a
//! value the factorizer calls prime are prime under identical rules.

use crate::Natural;
use crate::primality::{PrimalityConfig, is_probable_prime};
use core::fmt;

/// Why [`Natural::random_prime`] produced no prime.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum PrimeGenError {
    /// Fewer than two bits were requested. Two is the narrowest prime there is.
    WidthTooSmall {
        /// The requested width, in bits.
        bits: usize,
    },
    /// The requested width does not fit the target integer's fixed capacity.
    ///
    /// The capacity is `PARTS_64 * 64`, so it moves with the type parameter: `Natural<8>` tops out
    /// at 512 bits and the default `Natural` at 1024.
    WidthExceedsCapacity {
        /// The requested width, in bits.
        bits: usize,
        /// [`Natural::BITS`] for the type that was asked for the prime.
        capacity: usize,
    },
    /// The search drew `attempts` candidates without finding a prime.
    ///
    /// The bound is set hundreds of expected searches above what any width needs, so this is not a
    /// run of bad luck. It means the entropy source returned a constant or repeated itself.
    SearchExhausted {
        /// The requested width, in bits.
        bits: usize,
        /// How many candidates were drawn and rejected.
        attempts: usize,
    },
}

impl fmt::Display for PrimeGenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WidthTooSmall { bits } => {
                write!(f, "cannot generate a {bits}-bit prime: 2 is the narrowest")
            }
            Self::WidthExceedsCapacity { bits, capacity } => write!(
                f,
                "cannot generate a {bits}-bit prime: the integer holds {capacity} bits"
            ),
            Self::SearchExhausted { bits, attempts } => write!(
                f,
                "no {bits}-bit prime in {attempts} candidates: the entropy source is not \
                 delivering fresh bytes"
            ),
        }
    }
}
impl std::error::Error for PrimeGenError {}

/// Candidates are trial-divided by every prime below this bound before the probable-prime test is
/// allowed to run.
///
/// The bound trades one pass over a small table against the modular exponentiation that would
/// otherwise reject the candidate. It is a shallow optimum, and both sides of it cost: the
/// surviving fraction follows Mertens' `1/ln` curve and flattens quickly, while every candidate
/// pays for the whole table. The full `2^16` table `smallfactor` already caches is *slower* than no
/// pre-sieve at all below 512 bits.
///
/// Measured by `profile_presieve_bound` on an x86-64 Xeon 8259CL, 16 generations per cell, seconds,
/// two sweeps agreeing to within 1%:
///
/// | bound  | 256-bit | 512-bit | 1024-bit |
/// |-------:|--------:|--------:|---------:|
/// | none   |   0.078 |   0.368 |    4.271 |
/// | 2^8    |   0.072 |   0.349 |    3.830 |
/// | 2^10   |   0.068 |   0.313 |    3.255 |
/// | 2^12   |   0.071 |   0.306 |    2.922 |
/// | 2^14   |   0.085 |   0.342 |    3.004 |
/// | 2^16   |   0.127 |   0.492 |    3.766 |
///
/// `2^12` wins at 512 and 1024 bits and is inside the noise of the best cell at 256, so it is the
/// one bound rather than a width-dependent schedule. The gain is bounded from above by
/// [`is_probable_prime`] already trial-dividing by the first 32 primes on its own.
const TRIAL_DIVISION_BOUND: u32 = 1 << 12;

/// Candidates drawn per requested bit before the search gives up.
///
/// A width-`b` draw with both leading bits set is prime with probability near `2/(b·ln 2)`, so the
/// expected count is about `b/3` and this is roughly 750 expected searches. The bound exists to
/// turn a broken entropy source into an error instead of a hang, not to bound luck.
const ATTEMPTS_PER_BIT: usize = 256;

/// Draws one candidate of exactly `bits` significant bits.
///
/// The top bit fixes the width. For three bits and up the second-highest bit is also set, which is
/// what makes the type usable for RSA: two `k`-bit values drawn this way are each at least
/// `1.5·2^(k-1)`, so their product is at least `2.25·2^(2k-2) > 2^(2k-1)` and below `2^2k` — exactly
/// `2k` bits, every time, with no rejection loop over the modulus width. Setting bit zero costs
/// nothing and skips the half of the range no prime above two lives in.
fn draw<const P: usize>(bits: usize, fill: &mut dyn FnMut(&mut [u8])) -> Natural<P> {
    let mut bytes = vec![0u8; bits.div_ceil(8)];
    fill(&mut bytes);
    let top = bits - 1;
    // Whatever the source put above the requested width would widen the value past `bits`.
    let significant = top % 8 + 1;
    if significant < 8 {
        bytes[top / 8] &= (1u8 << significant) - 1;
    }
    bytes[top / 8] |= 1 << (top % 8);
    if bits >= 3 {
        bytes[(bits - 2) / 8] |= 1 << ((bits - 2) % 8);
        bytes[0] |= 1;
    }
    // Two bits is the one width where the padding rule cannot apply, and also the one width where
    // it is not needed: both values it leaves, 2 and 3, are prime.
    Natural::from_le_bytes(&bytes).expect("the width was checked against the capacity")
}

/// The generator proper, with the entropy source injected so tests can drive it deterministically
/// and so the `rand` dependency stays confined to one call site.
pub(crate) fn generate<const P: usize>(
    bits: usize,
    fill: &mut dyn FnMut(&mut [u8]),
) -> Result<Natural<P>, PrimeGenError> {
    generate_with_bound(bits, TRIAL_DIVISION_BOUND, fill)
}

/// [`generate`] with the pre-sieve bound left open, so the benchmark that picked
/// [`TRIAL_DIVISION_BOUND`] can be re-run rather than believed.
fn generate_with_bound<const P: usize>(
    bits: usize,
    bound: u32,
    fill: &mut dyn FnMut(&mut [u8]),
) -> Result<Natural<P>, PrimeGenError> {
    if bits < 2 {
        return Err(PrimeGenError::WidthTooSmall { bits });
    }
    if bits > Natural::<P>::BITS {
        return Err(PrimeGenError::WidthExceedsCapacity {
            bits,
            capacity: Natural::<P>::BITS,
        });
    }
    let config = PrimalityConfig::default();
    // The pre-sieve is only sound once every table entry is a *proper* divisor candidate. At or
    // below the bound's width the draw can be a table prime itself, and dividing it by itself would
    // reject a prime. Those widths are cheap enough to hand straight to the full test.
    let presieve = bits > bound.trailing_zeros() as usize;
    let attempts = bits.saturating_mul(ATTEMPTS_PER_BIT);
    for _ in 0..attempts {
        let candidate = draw::<P>(bits, fill);
        if presieve
            && crate::smallfactor::small_primes()
                .iter()
                .take_while(|&&prime| prime < bound)
                .any(|&prime| candidate.mod_u64(u64::from(prime)) == 0)
        {
            continue;
        }
        if is_probable_prime(&candidate, &config) {
            return Ok(candidate);
        }
    }
    Err(PrimeGenError::SearchExhausted { bits, attempts })
}

impl<const P: usize> Natural<P> {
    /// Generates a random probable prime of exactly `bits` significant bits.
    ///
    /// `bits` runs from 2 through [`Natural::BITS`], which is `PARTS_64 * 64` — 1024 for the
    /// default `Natural`, 512 for `Natural<8>`, and so on.
    ///
    /// From three bits up, the two leading bits of the result are both one. That is what makes the
    /// output usable for RSA: the product of a `k`-bit and an `m`-bit prime drawn this way is
    /// always exactly `k + m` bits, so a modulus of a stated width needs no rejection loop. It also
    /// means narrow widths have few candidates and some have exactly one — every three-bit result
    /// is 7 — since the padding rule keeps only the upper half of the width's range.
    ///
    /// Primality is decided by the test the factorization path uses on its own cofactors, in its
    /// default configuration: Baillie-PSW above `2^64` followed by sixteen Miller-Rabin rounds.
    /// The result is a probable prime with the same standing as anything [`crate::factor`] reports,
    /// not a proven one.
    ///
    /// Candidates come from `rand`'s thread generator, a cryptographic stream cipher seeded from
    /// the operating system.
    ///
    /// # Not for key material
    ///
    /// `Natural`'s arithmetic is variable-time throughout, and so is the trial division and the
    /// modular exponentiation this runs on every candidate. A process that can observe the timing
    /// can learn about the primes. This exists to build test vectors, benchmark corpora, and
    /// challenge inputs for the factorizer — use a constant-time cryptographic library for keys.
    ///
    /// # Errors
    ///
    /// Returns [`PrimeGenError::WidthTooSmall`] below two bits,
    /// [`PrimeGenError::WidthExceedsCapacity`] past the type's capacity, and
    /// [`PrimeGenError::SearchExhausted`] if the entropy source stops returning fresh bytes.
    ///
    /// # Examples
    ///
    /// A 256-bit prime, and the 512-bit semiprime two of them make:
    ///
    /// ```
    /// use rusqsieve::Natural;
    ///
    /// let p = Natural::<8>::random_prime(256)?;
    /// let q = Natural::<8>::random_prime(256)?;
    /// assert_eq!(p.bit_len(), 256);
    /// assert!(p.bit(255) && p.bit(254));
    ///
    /// let modulus = p.checked_mul(&q).expect("512 bits fit Natural<8>");
    /// assert_eq!(modulus.bit_len(), 512);
    /// # Ok::<(), rusqsieve::PrimeGenError>(())
    /// ```
    #[cfg(feature = "rand")]
    pub fn random_prime(bits: usize) -> Result<Self, PrimeGenError> {
        use rand::Rng as _;
        let mut rng = rand::rng();
        generate(bits, &mut |bytes| rng.fill_bytes(bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A deterministic filler, so every property below is reproducible and a failure can be
    /// replayed. This is the crate's own ChaCha8 rather than `rand`, which keeps the tests running
    /// under `--no-default-features`.
    struct Fill(u64);
    impl Fill {
        fn new(seed: u64) -> Self {
            Self(seed | 1)
        }
        fn bytes(&mut self, out: &mut [u8]) {
            for slot in out.iter_mut() {
                // SplitMix64, enough of a generator to prove the search does not depend on the
                // source's quality.
                self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = self.0;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                *slot = (z ^ (z >> 31)) as u8;
            }
        }
    }

    fn prime<const P: usize>(seed: u64, bits: usize) -> Natural<P> {
        let mut fill = Fill::new(seed);
        generate(bits, &mut |bytes| fill.bytes(bytes)).expect("width is generatable")
    }

    #[test]
    fn results_have_the_requested_width_and_both_leading_bits() {
        for bits in [
            3usize, 4, 5, 8, 16, 17, 31, 32, 33, 61, 64, 65, 127, 128, 129, 256,
        ] {
            for seed in 1..4u64 {
                let p: Natural<16> = prime(seed, bits);
                assert_eq!(p.bit_len(), bits, "{bits}-bit request, seed {seed}");
                assert!(p.bit(bits - 1) && p.bit(bits - 2), "{bits}-bit leading pad");
                assert!(p.is_odd(), "{bits}-bit result is even");
                assert!(is_probable_prime(&p, &PrimalityConfig::default()));
            }
        }
    }

    /// The pre-sieve is skipped at and below its own width because a draw can equal a table prime.
    /// These are the widths where that matters, checked against an independent trial division so a
    /// silently-rejected prime cannot pass.
    #[test]
    fn narrow_widths_are_prime_and_not_rejected_by_the_pre_sieve() {
        for bits in 2..=16usize {
            for seed in 1..8u64 {
                let p: Natural<2> = prime(seed, bits);
                let value = p.to_u64().expect("16 bits fit a word");
                assert_eq!(64 - value.leading_zeros() as usize, bits);
                assert!(
                    (2..value).all(|d| !value.is_multiple_of(d)),
                    "{value} is not prime for a {bits}-bit request"
                );
            }
        }
    }

    /// Two bits is the width the padding rule cannot cover, and both values it leaves are prime.
    /// The draw must reach each of them rather than collapsing to one.
    #[test]
    fn two_bit_requests_yield_both_two_and_three() {
        let mut seen = [false; 2];
        for seed in 1..64u64 {
            let p: Natural<1> = prime(seed, 2);
            let value = p.to_u64().unwrap();
            assert!(value == 2 || value == 3, "{value} is not a 2-bit prime");
            seen[value as usize - 2] = true;
        }
        assert_eq!(seen, [true, true], "the 2-bit draw is stuck on one value");
    }

    /// The reason the second-highest bit is padded: a modulus built from two of these has the width
    /// it was asked for, with no retry, for both the even and the odd split.
    #[test]
    fn products_of_two_draws_have_exactly_the_summed_width() {
        for (high, low) in [(5usize, 5usize), (8, 7), (32, 32), (64, 63), (256, 256)] {
            for seed in 1..4u64 {
                let p: Natural<16> = prime(seed, high);
                let q: Natural<16> = prime(seed + 977, low);
                let n = p.checked_mul(&q).expect("the product fits");
                assert_eq!(n.bit_len(), high + low, "{high}+{low}, seed {seed}");
            }
        }
    }

    #[test]
    fn a_stuck_entropy_source_is_reported_rather_than_looped_on() {
        // Every byte zero: the padding is then the whole value and the draw is the same composite
        // forever. At 64 bits that is 0xc000_0000_0000_0001 = 13 · 211 · 5295463 · 952469857, so
        // the loop cannot terminate on its own and the attempt bound is the only thing that ends
        // it. The pre-sieve rejects it on its first table entries, which is why exhausting the
        // bound is cheap enough to assert on.
        let outcome = generate::<16>(64, &mut |bytes| bytes.fill(0));
        assert_eq!(
            outcome,
            Err(PrimeGenError::SearchExhausted {
                bits: 64,
                attempts: 64 * ATTEMPTS_PER_BIT,
            })
        );
    }

    #[test]
    fn widths_outside_the_supported_range_are_rejected() {
        let mut fill = Fill::new(1);
        for bits in [0usize, 1] {
            assert_eq!(
                generate::<16>(bits, &mut |b| fill.bytes(b)),
                Err(PrimeGenError::WidthTooSmall { bits })
            );
        }
        // The ceiling is the type's capacity, not a constant: it moves with `PARTS_64`.
        assert_eq!(
            generate::<16>(1025, &mut |b| fill.bytes(b)),
            Err(PrimeGenError::WidthExceedsCapacity {
                bits: 1025,
                capacity: 1024,
            })
        );
        assert_eq!(
            generate::<4>(257, &mut |b| fill.bytes(b)),
            Err(PrimeGenError::WidthExceedsCapacity {
                bits: 257,
                capacity: 256,
            })
        );
        assert!(generate::<4>(256, &mut |b| fill.bytes(b)).is_ok());
    }

    /// Picks [`TRIAL_DIVISION_BOUND`]. Run with
    /// `cargo test --profile release-test -- --ignored --nocapture presieve`.
    #[test]
    #[ignore = "manual pre-sieve bound measurement"]
    fn profile_presieve_bound() {
        for bits in [256usize, 512, 1024] {
            for bound in [2u32, 1 << 6, 1 << 8, 1 << 10, 1 << 12, 1 << 14, 1 << 16] {
                let mut fill = Fill::new(1);
                let started = std::time::Instant::now();
                let mut accepted = 0usize;
                for _ in 0..16 {
                    let p: Natural<16> =
                        generate_with_bound(bits, bound, &mut |b| fill.bytes(b)).unwrap();
                    accepted += p.bit_len();
                }
                eprintln!(
                    "BENCH presieve bits={bits} bound={bound} elapsed={:.3}s checksum={accepted}",
                    started.elapsed().as_secs_f64()
                );
            }
        }
    }

    /// The whole point of the module is that its output survives the factorizer's own opinion of
    /// what is prime, so run one through it.
    #[test]
    fn generated_semiprimes_factor_back_to_their_primes() {
        let p: Natural<16> = prime(7, 48);
        let q: Natural<16> = prime(8, 48);
        assert_ne!(p, q);
        let n = p.checked_mul(&q).expect("96 bits fit");
        let factors = crate::factor(n).expect("a 96-bit semiprime factors");
        let recovered: Vec<_> = factors.expanded().cloned().collect();
        let mut expected = [p, q];
        expected.sort();
        assert_eq!(recovered, expected);
    }
}
