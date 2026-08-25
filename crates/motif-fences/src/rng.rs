//! A small, dependency-free, seedable pseudorandom generator.
//!
//! The optimizer (`anneal`, `skeleton::random_growth`) needs reproducible
//! randomness: a found configuration must be regenerable from its
//! recorded seed (per the task's reproducibility requirement). Pulling in
//! the `rand` crate would work too, but SplitMix64 is ~10 lines, has no
//! external dependency to pin/audit, and is more than good enough for
//! this use (Monte-Carlo-style search, not cryptography). Gaussian
//! sampling is Box-Muller on top of two SplitMix64 draws.

/// A SplitMix64 generator (Vigna 2015). Deterministic from `seed`.
#[derive(Debug, Clone)]
pub struct Rng {
    state: u64,
    spare_gaussian: Option<f64>,
}

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng {
            state: seed,
            spare_gaussian: None,
        }
    }

    /// Next raw 64-bit value.
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    /// Uniform float in `[0, 1)`.
    pub fn next_f64(&mut self) -> f64 {
        // Top 53 bits, the usual construction for a double in [0,1).
        (self.next_u64() >> 11) as f64 * (1.0 / (1u64 << 53) as f64)
    }

    /// Uniform float in `[lo, hi)`.
    pub fn range_f64(&mut self, lo: f64, hi: f64) -> f64 {
        lo + self.next_f64() * (hi - lo)
    }

    /// Uniform integer in `[0, n)`. Panics if `n == 0`.
    pub fn range_usize(&mut self, n: usize) -> usize {
        assert!(n > 0, "range_usize: empty range");
        ((self.next_f64() * n as f64) as usize).min(n - 1)
    }

    /// Standard normal (mean 0, variance 1) sample via Box-Muller,
    /// caching the second value each pair of draws produces.
    pub fn gaussian(&mut self) -> f64 {
        if let Some(g) = self.spare_gaussian.take() {
            return g;
        }
        let u1 = self.next_f64().max(1e-300); // avoid ln(0)
        let u2 = self.next_f64();
        let r = (-2.0 * u1.ln()).sqrt();
        let theta = 2.0 * std::f64::consts::PI * u2;
        self.spare_gaussian = Some(r * theta.sin());
        r * theta.cos()
    }

    /// `true` with probability `p` (`p` clamped to `[0, 1]`).
    pub fn bernoulli(&mut self, p: f64) -> bool {
        self.next_f64() < p.clamp(0.0, 1.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reproducible_from_seed() {
        let mut a = Rng::new(42);
        let mut b = Rng::new(42);
        for _ in 0..100 {
            assert_eq!(a.next_u64(), b.next_u64());
        }
    }

    #[test]
    fn different_seeds_diverge() {
        let mut a = Rng::new(1);
        let mut b = Rng::new(2);
        assert_ne!(a.next_u64(), b.next_u64());
    }

    #[test]
    fn gaussian_is_roughly_standard_normal() {
        let mut rng = Rng::new(7);
        let n = 20_000;
        let samples: Vec<f64> = (0..n).map(|_| rng.gaussian()).collect();
        let mean: f64 = samples.iter().sum::<f64>() / n as f64;
        let var: f64 = samples.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / n as f64;
        assert!(mean.abs() < 0.05, "mean = {mean}");
        assert!((var - 1.0).abs() < 0.1, "var = {var}");
    }
}
