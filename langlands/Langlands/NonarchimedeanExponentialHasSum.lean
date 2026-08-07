import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Log
import Langlands.NonarchimedeanExponential
import Langlands.NonarchimedeanUnconditionalSummability

/-!
# `NonarchimedeanExponential.exp`/`.log` are unconditional sums, matching `PowerSeries.exp`/`.log`

This file does part (a) of the gap `Langlands.PowerSeriesExpLog`'s module docstring names ("matching
`PowerSeries.exp`/`.log`'s coefficient-indexed definitions against
`NonarchimedeanExponential.exp`/`.log`'s Cauchy-limit definitions termwise"), plus the first half of
part (b) (upgrading `Tendsto`-along-`range n` to a genuine `HasSum`, which is what "termwise
convergence commutes with formal substitution" will actually need to invoke — a `HasSum` fact, not
merely a sequential limit, is required to reindex/rearrange terms at all).

## What this file proves

`Langlands.NonarchimedeanExponential.exp`/`.log` are defined as `Tendsto`-limits of their partial
sums along `range n` (`tendsto_partialSum_exp`, `tendsto_partialSum_log`). That is weaker than
`HasSum`, which asserts convergence of the net of *all* finite partial sums (unconditional
convergence) — but `Langlands.NonarchimedeanUnconditionalSummability`'s
`IsUltrametricDist.summable_of_tendsto_zero` (this pass, same wild-ramification thread) shows that in
a complete ultrametric normed group, `Tendsto (terms) cofinite (nhds 0)` alone forces `Summable`,
hence `HasSum`, with no separate rearrangement argument needed. Since `cofinite = atTop` on `ℕ`
(`Nat.cofinite_eq_atTop`) and the per-term geometric bounds `norm_pow_div_factorial_le`/
`norm_pow_div_natCast_le` already give `Tendsto (terms) atTop (nhds 0)`, this upgrade is immediate:

* `hasSum_exp`: `HasSum (fun n => x ^ n / n !) (exp hnorm x)`.
* `hasSum_log`: `HasSum (fun k => (-1) ^ k * x ^ (k + 1) / (k + 1)) (log hnorm x)`.

Both proofs identify the (unique, `HasSum`-forced) sum with `exp`/`log`'s already-defined value by
comparing `HasSum.tendsto_sum_nat`'s partial-sum limit against `tendsto_partialSum_exp`/`_log`'s, via
`tendsto_nhds_unique`.

`PowerSeries.exp`/`.log`'s coefficients are then matched termwise against these sums:

* `hasSum_coeff_exp`: `HasSum (fun n => PowerSeries.coeff n (PowerSeries.exp K) * x ^ n) (exp hnorm x)`
  — a direct rewrite of `hasSum_exp`, since `coeff n (exp K) = algebraMap ℚ K (1 / n !)` computes to
  exactly `(n ! : K)⁻¹`.
* `hasSum_coeff_log`: `HasSum (fun n => PowerSeries.coeff n (PowerSeries.log K) * x ^ n) (log hnorm x)`
  — from `hasSum_log` via `hasSum_nat_add_iff' 1`, since `coeff 0 (log K) = 0` drops out of the shift
  and `coeff (n+1) (log K) = (-1) ^ (n+2) / (n+1)` computes to match `(-1) ^ n * x ^ (n+1) / (n+1)`
  exactly (`(-1) ^ (n+2) = (-1) ^ n`) — this is precisely the index/sign match that
  `Langlands.PowerSeriesExpLog`'s module docstring and `ROADMAP.md`'s §6f flagged as unverified.

## What this does not close

This is *coefficientwise* matching of two convergent sums to two formal coefficient sequences — it
does **not** establish that formal *substitution* (`PowerSeries.subst`, i.e. composing one series into
another) commutes with evaluating the composite at a convergent point. That is a strictly harder
claim (a Cauchy-product/double-series rearrangement argument for the composite series
`(log K).subst (exp K - 1)`, not just termwise identification of each series on its own) and is not
attempted in this file; see `ROADMAP.md`'s pass log for the precise remaining state and the specific
Mathlib pieces (`FormalMultilinearSeries.ofScalars`, `HasFPowerSeriesAt.comp`) identified as candidate
machinery for that remaining step.
-/

@[expose] public section

namespace NonarchimedeanExponential

open Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
variable {p : ℕ} [hp : Fact p.Prime]

/-! ## A geometric-bound-to-`Tendsto`-zero helper -/

omit [IsUltrametricDist K] [CharZero K] [CompleteSpace K] in
private theorem tendsto_zero_of_geometric_bound {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {f : ℕ → K} (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) : Tendsto f atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) hf ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C

/-! ## `exp` as a `HasSum` -/

theorem hasSum_exp (hnorm : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < convergenceRadius K p) :
    HasSum (fun n => x ^ n / (n.factorial : K)) (exp hnorm x) := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  set r := ‖x‖ / ‖(p : K)‖ ^ (((p : ℝ) - 1)⁻¹) with hrdef
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg x) (Real.rpow_nonneg hp0.le _)
  have hr1 : r < 1 := by rw [hrdef, div_lt_one (Real.rpow_pos_of_pos hp0 _)]; exact hx
  have hzero : Tendsto (fun n => x ^ n / (n.factorial : K)) atTop (nhds 0) :=
    tendsto_zero_of_geometric_bound (C := 1) hr0 hr1
      (by simpa using norm_pow_div_factorial_le hnorm x)
  have hsummable : Summable (fun n => x ^ n / (n.factorial : K)) :=
    IsUltrametricDist.summable_of_tendsto_zero (Nat.cofinite_eq_atTop ▸ hzero)
  have hlimit : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range n, x ^ k / (k.factorial : K)) atTop
      (nhds (∑' n, x ^ n / (n.factorial : K))) :=
    hsummable.hasSum.tendsto_sum_nat
  have hlimit' : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range n, x ^ k / (k.factorial : K)) atTop (nhds (exp hnorm x)) := by
    have := tendsto_partialSum_exp hnorm hx
    have hshift : Filter.Tendsto
        (fun n => ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : K)) atTop
        (nhds (exp hnorm x)) := this
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp hshift
  have heq : (∑' n, x ^ n / (n.factorial : K)) = exp hnorm x := tendsto_nhds_unique hlimit hlimit'
  have hs := hsummable.hasSum
  rwa [heq] at hs

/-! ## `log` as a `HasSum` -/

theorem hasSum_log (hnorm : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < logConvergenceRadius K p) :
    HasSum (fun k => (-1 : K) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K)) (log hnorm x) := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  set r := ‖x‖ / ‖(p : K)‖ with hrdef
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg x) hp0.le
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hp0]; exact hx
  have hbound : ∀ n : ℕ, ‖(-1 : K) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K)‖ ≤ r * r ^ n := by
    intro n
    have hneg1 : ‖(-1 : K) ^ n‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
    calc ‖(-1 : K) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K)‖
        = ‖x ^ (n + 1) / ((n + 1 : ℕ) : K)‖ := by
          rw [norm_div, norm_mul, hneg1, one_mul, ← norm_div]
      _ ≤ r ^ (n + 1) := norm_pow_div_natCast_le hnorm x n.succ_ne_zero
      _ = r * r ^ n := pow_succ' r n
  have hzero : Tendsto (fun n => (-1 : K) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K)) atTop (nhds 0) :=
    tendsto_zero_of_geometric_bound hr0 hr1 hbound
  have hsummable : Summable (fun n => (-1 : K) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K)) :=
    IsUltrametricDist.summable_of_tendsto_zero (Nat.cofinite_eq_atTop ▸ hzero)
  have hlimit : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range n, (-1 : K) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K)) atTop
      (nhds (∑' n, (-1 : K) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K))) :=
    hsummable.hasSum.tendsto_sum_nat
  have hlimit' : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range n, (-1 : K) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K)) atTop
      (nhds (log hnorm x)) :=
    tendsto_partialSum_log hnorm hx
  have heq : (∑' n, (-1 : K) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K)) = log hnorm x :=
    tendsto_nhds_unique hlimit hlimit'
  have hs := hsummable.hasSum
  rwa [heq] at hs

/-! ## Coefficient matching against `PowerSeries.exp`/`.log` -/

theorem hasSum_coeff_exp (hnorm : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < convergenceRadius K p) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.exp K) * x ^ n) (exp hnorm x) := by
  have hcoeff : ∀ n : ℕ, PowerSeries.coeff n (PowerSeries.exp K) * x ^ n
      = x ^ n / (n.factorial : K) := by
    intro n
    have hinv : (algebraMap ℚ K) (1 / (n.factorial : ℚ)) = ((n.factorial : K))⁻¹ := by
      rw [one_div, map_inv₀, map_natCast]
    rw [PowerSeries.coeff_exp, hinv, div_eq_mul_inv, mul_comm]
  simpa only [hcoeff] using hasSum_exp hnorm hx

theorem hasSum_coeff_log (hnorm : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < logConvergenceRadius K p) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.log K) * x ^ n) (log hnorm x) := by
  have hshift : ∀ n : ℕ, PowerSeries.coeff (n + 1) (PowerSeries.log K) * x ^ (n + 1)
      = (-1 : K) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K) := by
    intro n
    rw [PowerSeries.coeff_log, if_neg n.succ_ne_zero]
    have hpow : ((-1 : ℚ) ^ (n + 1 + 1)) = (-1 : ℚ) ^ n := by ring
    rw [hpow, map_div₀, map_pow, map_neg, map_one, map_natCast]
    ring
  have hsum0 : ∑ i ∈ Finset.range 1, PowerSeries.coeff i (PowerSeries.log K) * x ^ i = 0 := by
    simp
  have hkey : HasSum (fun n => PowerSeries.coeff (n + 1) (PowerSeries.log K) * x ^ (n + 1))
      (log hnorm x - ∑ i ∈ Finset.range 1, PowerSeries.coeff i (PowerSeries.log K) * x ^ i) := by
    rw [hsum0, sub_zero]
    simpa only [hshift] using hasSum_log hnorm hx
  exact (hasSum_nat_add_iff' 1).mp hkey

end NonarchimedeanExponential
