import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPowerSeries.Basic
import Langlands.NonarchimedeanUnconditionalSummability

/-!
# Evaluating a bivariate power series at a concrete point, `Fin 2` case

The bivariate analogue of `Langlands.NonarchimedeanPowerSeriesEval`, specialized to
`σ = Fin 2` (the shape of `Langlands.LubinTateFunctionalEquationBivariate`'s `Φ : MvPowerSeries
(Fin 2) O`, i.e. the Lubin-Tate formal group law `F_π`). The convergence argument is the same
geometric one, generalized from a single exponent `n : ℕ` to a multi-index `n : Fin 2 →₀ ℕ`
weighted by *total degree*: a coefficient of algebra-mapped norm at most `1`, evaluated at a point
`y : Fin 2 → K` with both coordinates of norm `< 1`, contributes a term bounded by
`(max ‖y 0‖ ‖y 1‖) ^ n.degree`.

Two new ingredients over the univariate file:

* The per-term bound is now indexed by `Finsupp.degree` rather than `ℕ` directly, so `cofinite`
  convergence needs `Finsupp.finite_of_degree_lt` (Mathlib, `Mathlib.Data.Finsupp.Weight`) rather
  than the `ℕ`-specific `Nat.cofinite_eq_atTop` bridge the univariate file uses — that Mathlib
  lemma already supplies exactly "finitely many multi-indices below a given total degree", so no
  bespoke enumeration (e.g. via `Langlands.LubinTate.mkIdx`) is needed here.
* `IsUltrametricDist.summable_of_tendsto_zero` is stated for an arbitrary index type, so it applies
  to `Fin 2 →₀ ℕ` exactly as it does to `ℕ`, with no adaptation.

## What this does not do

Same scope as `Langlands.NonarchimedeanPowerSeriesEval`: existence of the evaluation and its
defining `HasSum` property only, no ring/algebra-hom structure and no compatibility with
`MvPowerSeries.subst`/`PowerSeries.subst`. See `Langlands.LubinTateFormalGroupEval`'s module
docstring for the Lubin-Tate-specific specialization and the precise remaining gap.
-/

@[expose] public section

noncomputable section

namespace NonarchimedeanMvPowerSeriesEvalFin2

variable {R K : Type*} [CommRing R] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra R K]

/-- The total degree of a bivariate multi-index is the sum of its two entries. Local restatement
(not imported from `Langlands.LubinTateFunctionalEquationBivariate.degree_fin_two`, to keep this
file independent of the Lubin-Tate development). -/
theorem degree_fin_two (n : Fin 2 →₀ ℕ) : n.degree = n 0 + n 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- The `n`-th summand of the bivariate evaluation series
`Σ (algebraMap (coeff n Φ)) * ∏ i, y i ^ n i`. -/
def evalSummandMv (Φ : MvPowerSeries (Fin 2) R) (y : Fin 2 → K) (n : Fin 2 →₀ ℕ) : K :=
  algebraMap R K (MvPowerSeries.coeff n Φ) * ∏ i, y i ^ (n i)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The per-term bound**: if every coefficient of `Φ`, algebra-mapped into `K`, has norm at most
`1`, then the `n`-th evaluation summand at `y` has norm at most `(max ‖y 0‖ ‖y 1‖) ^ n.degree`. -/
theorem norm_evalSummandMv_le {Φ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) (y : Fin 2 → K) (n : Fin 2 →₀ ℕ) :
    ‖evalSummandMv Φ y n‖ ≤ (max ‖y 0‖ ‖y 1‖) ^ n.degree := by
  unfold evalSummandMv
  set r := max ‖y 0‖ ‖y 1‖ with hrdef
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) (le_max_left _ _)
  have hy0 : ‖y 0‖ ≤ r := le_max_left _ _
  have hy1 : ‖y 1‖ ≤ r := le_max_right _ _
  rw [norm_mul, Fin.prod_univ_two, norm_mul, norm_pow, norm_pow]
  calc ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ * (‖y 0‖ ^ n 0 * ‖y 1‖ ^ n 1)
      ≤ 1 * (r ^ n 0 * r ^ n 1) := by
        refine mul_le_mul (hΦ n) ?_ (by positivity) zero_le_one
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy0 _)
          (pow_le_pow_left₀ (norm_nonneg _) hy1 _) (by positivity) (by positivity)
    _ = r ^ n.degree := by rw [one_mul, ← pow_add, degree_fin_two]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Unconditional convergence to `0` along `cofinite`.** Given `‖y 0‖ < 1` and `‖y 1‖ < 1`, for
every `ε > 0` the set of multi-indices whose term exceeds `ε` is contained in the (finite, by
`Finsupp.finite_of_degree_lt`) set of multi-indices of total degree below a threshold `D` chosen so
that `(max ‖y 0‖ ‖y 1‖) ^ D < ε`. -/
theorem tendsto_evalSummandMv_cofinite_zero {Φ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) :
    Filter.Tendsto (evalSummandMv Φ y) Filter.cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  set r := max ‖y 0‖ ‖y 1‖ with hrdef
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) (le_max_left _ _)
  have hr1 : r < 1 := max_lt hy0 hy1
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε hr1
  have hsub : {n : Fin 2 →₀ ℕ | ¬ dist (evalSummandMv Φ y n) 0 < ε} ⊆
      {n : Fin 2 →₀ ℕ | Finsupp.degree n < D} := by
    intro n hn
    simp only [Set.mem_setOf_eq, not_lt, dist_eq_norm, sub_zero] at hn
    by_contra hge
    simp only [Set.mem_setOf_eq, not_lt] at hge
    have hbound : ‖evalSummandMv Φ y n‖ ≤ r ^ n.degree := norm_evalSummandMv_le hΦ y n
    have hmono : r ^ n.degree ≤ r ^ D := pow_le_pow_of_le_one hr0 hr1.le hge
    linarith [hbound, hmono, hD]
  exact (Finsupp.finite_of_degree_lt (σ := Fin 2) D).subset hsub

/-- **Unconditional summability of the bivariate evaluation series.** -/
theorem summable_evalSummandMv {Φ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) :
    Summable (evalSummandMv Φ y) :=
  IsUltrametricDist.summable_of_tendsto_zero (tendsto_evalSummandMv_cofinite_zero hΦ hy0 hy1)

/-- **Evaluation of a bivariate power series at a concrete point**, unconditionally defined as
`∑' n, evalSummandMv Φ y n` (`0` when not summable); meaningful exactly when `Φ`'s coefficients are
algebra-mapped-norm-bounded by `1` and both coordinates of `y` have norm `< 1`, per `hasSum_evalMv`.
-/
def evalMv (Φ : MvPowerSeries (Fin 2) R) (y : Fin 2 → K) : K := ∑' n, evalSummandMv Φ y n

/-- **The defining property of `evalMv`**: on the domain where it is meaningful, the evaluation
summands genuinely (unconditionally) sum to `evalMv Φ y` — the precise sense in which the
evaluation "agrees with" the formal object `Φ`. -/
theorem hasSum_evalMv {Φ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) :
    HasSum (evalSummandMv Φ y) (evalMv Φ y) :=
  (summable_evalSummandMv hΦ hy0 hy1).hasSum

end NonarchimedeanMvPowerSeriesEvalFin2

end
