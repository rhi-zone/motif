import Langlands.NonarchimedeanExpLogCofinite
import Langlands.NonarchimedeanSigmaSummability
import Langlands.NonarchimedeanCauchyProduct

/-!
# The flattened `HasSum` for `exp hnorm (log hnorm x)`

This file assembles step (i) of the four-step plan `ROADMAP.md`'s tenth/eleventh passes describe for
the `exp`/`log` mutual-inverse identity: flattening the double sum

`exp hnorm (log hnorm x) = Σ_n coeff n (exp K) * (log hnorm x) ^ n`
`(log hnorm x) ^ n = Σ_{g : Fin n → ℕ} ∏ i, (coeff (g i) (log K) * x ^ (g i))`

into one flat `HasSum` over `Σ n, Fin n → ℕ`, using:

* the outer `HasSum` (`hasSum_coeff_exp`, `Langlands.NonarchimedeanExponentialHasSum`), evaluated at
  `y := log hnorm x` (valid since `‖log hnorm x‖ < convergenceRadius K p`, `norm_log_lt_convergenceRadius`);
* the inner, per-`n` `HasSum`s (`HasSum.pow_of_nonarchimedean` applied to `hasSum_coeff_log`, scaled by
  `coeff n (exp K)` via `HasSum.mul_left`);
* the `cofinite`-vanishing hypothesis closed in `Langlands.NonarchimedeanExpLogCofinite`
  (`tendsto_cofinite_exp_log_flatSum`), fed to `HasSum.sigma_of_isUltrametricDist`
  (`Langlands.NonarchimedeanSigmaSummability`).

## What this does not close

This is only step (i) of the four-step assembly. Steps (ii)–(iv) — matching the flattened sum's
degree-`m` slice against `PowerSeries.coeff_subst'`'s finite `finsum` formula, invoking the closed
formal identity `PowerSeries.exp_sub_one_subst_log`, and concluding `exp hnorm (log hnorm x) = 1 + x`
via uniqueness of `HasSum` — are not attempted here; see `ROADMAP.md`'s pass log for their status.
-/

@[expose] public section

namespace NonarchimedeanExponential

open Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
variable {p : ℕ} [hp : Fact p.Prime]

/-- **The flattened `HasSum` for `exp hnorm (log hnorm x)`.** For `‖x‖ < expLogCompositionRadius K p`,
the flat family `f ⟨n, g⟩ := coeff n (exp K) * ∏ i, (coeff (g i) (log K) * x ^ (g i))` on
`Σ n, Fin n → ℕ` sums to `exp hnorm (log hnorm x)`. Assembled from the outer `HasSum`
(`hasSum_coeff_exp` at `log hnorm x`, valid by `norm_log_lt_convergenceRadius`), the per-`n` inner
`HasSum`s (`HasSum.pow_of_nonarchimedean` on `hasSum_coeff_log`, scaled by `HasSum.mul_left`), and the
`cofinite`-vanishing hypothesis (`tendsto_cofinite_exp_log_flatSum`), via
`HasSum.sigma_of_isUltrametricDist`. -/
theorem hasSum_coeff_exp_log (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < expLogCompositionRadius K p) :
    HasSum (fun q : Σ _n : ℕ, Fin _n → ℕ =>
        PowerSeries.coeff q.1 (PowerSeries.exp K) *
          ∏ i, (PowerSeries.coeff (q.2 i) (PowerSeries.log K) * x ^ (q.2 i)))
      (exp hnorm (log hnorm x)) := by
  have hxlog : ‖x‖ < logConvergenceRadius K p :=
    lt_logConvergenceRadius_of_lt_expLogCompositionRadius hnorm hx
  have hloglt : ‖log hnorm x‖ < convergenceRadius K p := norm_log_lt_convergenceRadius hnorm hx
  have houter : HasSum (fun n => PowerSeries.coeff n (PowerSeries.exp K) * (log hnorm x) ^ n)
      (exp hnorm (log hnorm x)) := hasSum_coeff_exp hnorm hloglt
  have hinner : ∀ n : ℕ, HasSum
      (fun g : Fin n → ℕ =>
        PowerSeries.coeff n (PowerSeries.exp K) *
          ∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i)))
      (PowerSeries.coeff n (PowerSeries.exp K) * (log hnorm x) ^ n) := by
    intro n
    exact ((hasSum_coeff_log hnorm hxlog).pow_of_nonarchimedean n).mul_left _
  have hzero := tendsto_cofinite_exp_log_flatSum hnorm hx
  exact houter.sigma_of_isUltrametricDist hinner hzero

end NonarchimedeanExponential
