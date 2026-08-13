import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPowerSeries.Basic
import Langlands.NonarchimedeanUnconditionalSummability
import Langlands.NonarchimedeanPowerSeriesEval

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

`evalMv_mul`/`evalMv_pow` (`ROADMAP.md` §23's "Lemma A" prerequisite) add the multiplicative
structure, mirroring `Langlands.NonarchimedeanPowerSeriesEval.eval_mul`/`eval_pow` exactly:
`MvPowerSeries.coeff_mul` supplies the `Finset.HasAntidiagonal`-indexed convolution formula for
`Fin 2 →₀ ℕ` (the same `HasAntidiagonal` class `PowerSeries.coeff_subst_X_zero_subst_mul_X_one`
already uses), so `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` transfers verbatim with
`Fin 2 →₀ ℕ` in place of `ℕ`, and the underlying product family's summability comes from
`HasSum.mul_of_nonarchimedean` via the `NonarchimedeanRing K` instance already built in
`Langlands.NonarchimedeanPowerSeriesEval` (imported here for exactly that instance).

## What this does not do

No compatibility with `MvPowerSeries.subst`/`PowerSeries.subst` is proved here — that is
`ROADMAP.md` §23's "Lemma A"/"Lemma S", built on top of `evalMv_mul`/`evalMv_pow`. See
`Langlands.LubinTateFormalGroupEval`'s module docstring for the Lubin-Tate-specific specialization
and the precise remaining gap.
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

omit [CompleteSpace K] in
/-- **`evalMv Φ y` lies in the maximal ideal whenever `Φ` does**: if `Φ` has zero constant term
(so the index-`0` evaluation summand vanishes) and bounded coefficients, `‖evalMv Φ y‖ ≤
max ‖y 0‖ ‖y 1‖`. Via the ultrametric bound `IsUltrametricDist.norm_tsum_le`, applied to
`evalSummandMv Φ y`, mirroring `NonarchimedeanPowerSeriesEval.norm_eval_le`. -/
theorem norm_evalMv_le {Φ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1)
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) :
    ‖evalMv Φ y‖ ≤ max ‖y 0‖ ‖y 1‖ := by
  unfold evalMv
  set r := max ‖y 0‖ ‖y 1‖ with hrdef
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) (le_max_left _ _)
  have hr1 : r < 1 := max_lt hy0 hy1
  refine (IsUltrametricDist.norm_tsum_le _).trans (ciSup_le fun n ↦ ?_)
  rcases eq_or_ne n 0 with hn | hn
  · have h0 : evalSummandMv Φ y n = 0 := by
      unfold evalSummandMv
      rw [hn, MvPowerSeries.coeff_zero_eq_constantCoeff, hΦ0, map_zero, zero_mul]
    rw [h0, norm_zero]
    exact hr0
  · have hdeg : 1 ≤ n.degree := by
      rw [Nat.one_le_iff_ne_zero]
      exact fun hcontra ↦ hn ((Finsupp.degree_eq_zero_iff n).mp hcontra)
    calc ‖evalSummandMv Φ y n‖ ≤ r ^ n.degree := norm_evalSummandMv_le hΦ y n
      _ ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1.le hdeg
      _ = r := pow_one _

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **`evalMv Φ y = 0` when both coordinates of `y` are `0`**, given `Φ` has zero constant term:
every summand of index `n ≠ 0` has some factor `y i ^ n i` with `n i ≠ 0` and `y i = 0`, hence
vanishes; the index-`0` summand vanishes because `Φ`'s constant term does. -/
theorem evalMv_eq_zero_of_zero {Φ : MvPowerSeries (Fin 2) R}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) {y : Fin 2 → K} (hy0 : y 0 = 0) (hy1 : y 1 = 0) :
    evalMv Φ y = 0 := by
  have hterm : ∀ n : Fin 2 →₀ ℕ, evalSummandMv Φ y n = 0 := by
    intro n
    unfold evalSummandMv
    rcases eq_or_ne n 0 with hn | hn
    · rw [hn, MvPowerSeries.coeff_zero_eq_constantCoeff, hΦ0, map_zero, zero_mul]
    · obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp hn
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
      have hyi : y i = 0 := by fin_cases i <;> assumption
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hyi]; exact zero_pow hi), mul_zero]
  unfold evalMv
  simp [hterm]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The coefficients of `1 : MvPowerSeries (Fin 2) R`, algebra-mapped into `K`, are trivially
bounded by `1`. -/
theorem coeff_bound_one_mv :
    ∀ n : Fin 2 →₀ ℕ,
      ‖algebraMap R K (MvPowerSeries.coeff n (1 : MvPowerSeries (Fin 2) R))‖ ≤ 1 := by
  intro n
  rw [MvPowerSeries.coeff_one]
  split <;> simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Evaluation at `1` is `1`**: only the constant term (`= 1`) contributes. -/
theorem evalMv_one (y : Fin 2 → K) : evalMv (1 : MvPowerSeries (Fin 2) R) y = 1 := by
  have hterm : ∀ n : Fin 2 →₀ ℕ, evalSummandMv (1 : MvPowerSeries (Fin 2) R) y n =
      if n = 0 then 1 else 0 := by
    intro n
    unfold evalSummandMv
    rw [MvPowerSeries.coeff_one]
    by_cases h : n = 0 <;> simp [h]
  unfold evalMv
  rw [tsum_eq_single 0 (by intro n hn; rw [hterm]; simp [hn])]
  rw [hterm]; simp

omit [CompleteSpace K] in
/-- **Coefficient boundedness is preserved by multiplication.** `coeff n (Φ * Ψ)` is a sum, over
`Finset.HasAntidiagonal.antidiagonal n`, of products of bounded coefficients; the nonempty-sum
ultrametric bound `Finset.Nonempty.norm_sum_le_sup'_norm` bounds it by `1`. -/
theorem coeff_bound_mul_mv {Φ Ψ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1)
    (hΨ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Ψ)‖ ≤ 1) :
    ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n (Φ * Ψ))‖ ≤ 1 := by
  intro n
  rw [MvPowerSeries.coeff_mul, map_sum]
  refine (Finset.Nonempty.norm_sum_le_sup'_norm
    ⟨(0, n), Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)⟩ _).trans ?_
  simp only [Finset.sup'_le_iff]
  intro p _
  rw [map_mul, norm_mul]
  calc ‖algebraMap R K (MvPowerSeries.coeff p.1 Φ)‖ * ‖algebraMap R K (MvPowerSeries.coeff p.2 Ψ)‖
      ≤ 1 * 1 := mul_le_mul (hΦ p.1) (hΨ p.2) (norm_nonneg _) zero_le_one
    _ = 1 := mul_one 1

omit [CompleteSpace K] in
/-- **Coefficient boundedness is preserved by powers**, by induction on `coeff_bound_mul_mv`. -/
theorem coeff_bound_pow_mv {Φ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) :
    ∀ (m : ℕ) (n : Fin 2 →₀ ℕ), ‖algebraMap R K (MvPowerSeries.coeff n (Φ ^ m))‖ ≤ 1 := by
  intro m
  induction m with
  | zero => intro n; simpa using coeff_bound_one_mv (R := R) (K := K) n
  | succ m ih => intro n; rw [pow_succ]; exact coeff_bound_mul_mv ih hΦ n

/-- **Evaluation is multiplicative**, on the domain where both series have
algebra-mapped-norm-bounded coefficients and both point coordinates lie in the maximal ideal.
Mirrors `Langlands.NonarchimedeanPowerSeriesEval.eval_mul`, with the outer index generalized from
`ℕ` to `Fin 2 →₀ ℕ`: the Cauchy product formula `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`
regroups the `(Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)`-indexed product family (summable via
`HasSum.mul_of_nonarchimedean`, using the `NonarchimedeanRing K` instance from
`Langlands.NonarchimedeanPowerSeriesEval`) by `Finset.HasAntidiagonal.antidiagonal`, matching
`MvPowerSeries.coeff_mul` term-by-term. -/
theorem evalMv_mul {Φ Ψ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1)
    (hΨ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Ψ)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) :
    evalMv (Φ * Ψ) y = evalMv Φ y * evalMv Ψ y := by
  have hfg : Summable (fun p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) =>
      evalSummandMv Φ y p.1 * evalSummandMv Ψ y p.2) :=
    ((hasSum_evalMv hΦ hy0 hy1).mul_of_nonarchimedean (hasSum_evalMv hΨ hy0 hy1)).summable
  unfold evalMv
  rw [(summable_evalSummandMv hΦ hy0 hy1).tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (summable_evalSummandMv hΨ hy0 hy1) hfg]
  congr 1
  funext n
  unfold evalSummandMv
  rw [MvPowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [map_mul, ← hp]
  simp only [Finsupp.add_apply, pow_add]
  rw [Finset.prod_mul_distrib]
  ring

/-- **Evaluation is compatible with powers**: `evalMv (Φ ^ m) y = evalMv Φ y ^ m`, by induction on
`evalMv_mul`. -/
theorem evalMv_pow {Φ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) :
    ∀ m, evalMv (Φ ^ m) y = evalMv Φ y ^ m
  | 0 => by simpa using evalMv_one (R := R) (K := K) y
  | m + 1 => by
      rw [pow_succ, pow_succ, evalMv_mul (coeff_bound_pow_mv hΦ m) hΦ hy0 hy1,
        evalMv_pow hΦ hy0 hy1 m]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Extensionality for bivariate multi-indices: agreeing at `0` and at `1` is equality. Local
restatement (not imported from `Langlands.LubinTateFunctionalEquationBivariate.finsupp_fin_two_ext`),
matching this file's existing convention of keeping `degree_fin_two` independent of the Lubin-Tate
development. -/
theorem finsupp_fin_two_ext {m n : Fin 2 →₀ ℕ} (h0 : m 0 = n 0) (h1 : m 1 = n 1) : m = n := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **A bivariate multi-index has total degree `1` exactly when it is one of the two "axis"
multi-indices** `Finsupp.single 0 1` or `Finsupp.single 1 1`. The combinatorial fact underlying the
quadratic tail bound below: the only multi-indices of total degree `≤ 1` are `0` and these two. -/
theorem degree_fin_two_eq_one_iff {n : Fin 2 →₀ ℕ} :
    n.degree = 1 ↔ n = Finsupp.single 0 1 ∨ n = Finsupp.single 1 1 := by
  constructor
  · intro hn
    rw [degree_fin_two] at hn
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · right
      refine finsupp_fin_two_ext ?_ ?_
      · rw [Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)]; exact h0
      · rw [Finsupp.single_eq_same]; omega
    · left
      refine finsupp_fin_two_ext ?_ ?_
      · rw [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide)]; omega
  · rintro (rfl | rfl) <;> rw [degree_fin_two] <;> simp

/-- **The bivariate quadratic tail bound**: `evalMv Φ y` lies within `(max ‖y 0‖ ‖y 1‖) ^ 2` of
`Φ`'s degree-`1` linear approximation `(coeff (single 0 1) Φ) * y 0 + (coeff (single 1 1) Φ) * y 1`,
given `Φ` has zero constant term. The bivariate analogue of
`Langlands.NonarchimedeanPowerSeriesEval.norm_eval_sub_coeff_one_mul_le`: splits `evalMv Φ y` off at
the three multi-indices of total degree `≤ 1` (`0`, `Finsupp.single 0 1`, `Finsupp.single 1 1`,
via `Summable.sum_add_tsum_compl`), identifies the index-`0` summand as `0` (via `hΦ0`) and the two
degree-`1` summands as the two linear terms, and bounds the remaining tail (every other multi-index,
necessarily of total degree `≥ 2` by `degree_fin_two_eq_one_iff`) by `(max ‖y 0‖ ‖y 1‖) ^ 2`, via the
same per-term geometric bound `norm_evalSummandMv_le` `norm_evalMv_le` already uses. -/
theorem norm_evalMv_sub_linear_le {Φ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1)
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) :
    ‖evalMv Φ y -
        (algebraMap R K (MvPowerSeries.coeff (Finsupp.single 0 1) Φ) * y 0 +
          algebraMap R K (MvPowerSeries.coeff (Finsupp.single 1 1) Φ) * y 1)‖ ≤
      (max ‖y 0‖ ‖y 1‖) ^ 2 := by
  classical
  set r := max ‖y 0‖ ‖y 1‖ with hrdef
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) (le_max_left _ _)
  have hr1 : r < 1 := max_lt hy0 hy1
  set s : Finset (Fin 2 →₀ ℕ) := {0, Finsupp.single 0 1, Finsupp.single 1 1} with hsdef
  have hsum := (summable_evalSummandMv hΦ hy0 hy1).sum_add_tsum_compl (s := s)
  have h0ns : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h; have := congrArg (fun (m : Fin 2 →₀ ℕ) => m 0) h; simp at this
  have h0ns' : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h; have := congrArg (fun (m : Fin 2 →₀ ℕ) => m 1) h; simp at this
  have hns : (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 1 := by
    intro h; have := congrArg (fun (m : Fin 2 →₀ ℕ) => m 0) h; simp at this
  have hmem0 : (0 : Fin 2 →₀ ℕ) ∉
      insert (Finsupp.single 0 1) ({Finsupp.single 1 1} : Finset (Fin 2 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or.mpr ⟨h0ns, h0ns'⟩
  have hmem1 : (Finsupp.single (0 : Fin 2) 1) ∉
      ({Finsupp.single 1 1} : Finset (Fin 2 →₀ ℕ)) := by
    simp only [Finset.mem_singleton]; exact hns
  have hsval : ∑ x ∈ s, evalSummandMv Φ y x =
      algebraMap R K (MvPowerSeries.coeff (Finsupp.single 0 1) Φ) * y 0 +
        algebraMap R K (MvPowerSeries.coeff (Finsupp.single 1 1) Φ) * y 1 := by
    rw [hsdef, Finset.sum_insert hmem0, Finset.sum_insert hmem1, Finset.sum_singleton]
    have hterm0 : evalSummandMv Φ y 0 = 0 := by
      unfold evalSummandMv
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff, hΦ0, map_zero, zero_mul]
    have hterm10 : evalSummandMv Φ y (Finsupp.single 0 1) =
        algebraMap R K (MvPowerSeries.coeff (Finsupp.single 0 1) Φ) * y 0 := by
      unfold evalSummandMv; rw [Fin.prod_univ_two]; simp
    have hterm01 : evalSummandMv Φ y (Finsupp.single 1 1) =
        algebraMap R K (MvPowerSeries.coeff (Finsupp.single 1 1) Φ) * y 1 := by
      unfold evalSummandMv; rw [Fin.prod_univ_two]; simp
    rw [hterm0, hterm10, hterm01, zero_add]
  unfold evalMv
  rw [← hsum, hsval, add_sub_cancel_left]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) (fun x ↦ ?_)
  have hxnotmem : (x : Fin 2 →₀ ℕ) ∉ s := by
    have hx2 := x.2
    rw [Set.mem_compl_iff, Finset.mem_coe] at hx2
    exact hx2
  have hxdeg : 2 ≤ (x : Fin 2 →₀ ℕ).degree := by
    by_contra hlt
    push Not at hlt
    have hcase : (x : Fin 2 →₀ ℕ).degree = 0 ∨ (x : Fin 2 →₀ ℕ).degree = 1 := by omega
    have hmemLit : ∀ z : Fin 2 →₀ ℕ, z = 0 ∨ z = Finsupp.single 0 1 ∨ z = Finsupp.single 1 1 →
        z ∈ ({0, Finsupp.single 0 1, Finsupp.single 1 1} : Finset (Fin 2 →₀ ℕ)) := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rcases hcase with h0 | h1
    · exact hxnotmem (hmemLit _ (Or.inl ((Finsupp.degree_eq_zero_iff _).mp h0)))
    · rcases degree_fin_two_eq_one_iff.mp h1 with h | h
      · exact hxnotmem (hmemLit _ (Or.inr (Or.inl h)))
      · exact hxnotmem (hmemLit _ (Or.inr (Or.inr h)))
  calc ‖evalSummandMv Φ y (x : Fin 2 →₀ ℕ)‖ ≤ r ^ (x : Fin 2 →₀ ℕ).degree :=
        norm_evalSummandMv_le hΦ y _
    _ ≤ r ^ 2 := pow_le_pow_of_le_one hr0 hr1.le hxdeg

end NonarchimedeanMvPowerSeriesEvalFin2

end
