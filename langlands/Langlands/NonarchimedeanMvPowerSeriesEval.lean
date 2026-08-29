import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPowerSeries.Basic
import Langlands.NonarchimedeanUnconditionalSummability
import Langlands.NonarchimedeanPowerSeriesEval

/-!
# Evaluating a multivariate power series at a concrete point, general finite index type

The general-`σ` analogue of `Langlands.NonarchimedeanMvPowerSeriesEvalFin2` (which is specialized
to `σ = Fin 2`, the shape of `Langlands.LubinTateFunctionalEquationBivariate`'s `Φ : MvPowerSeries
(Fin 2) O`). This file is not a re-derivation of that one: checking against Mathlib's actual
statements first (`Finsupp.degree_eq_sum`, `Finsupp.finite_of_degree_lt`, `Finset.prod_le_prod`,
`Finset.prod_pow_eq_pow_sum`, `Finset.Nonempty.norm_sum_le_sup'_norm`) showed every ingredient the
`Fin 2` file uses is already stated by Mathlib for an arbitrary finite `σ`, not just `Fin 2` — the
only `Fin 2`-specific step in that file was unfolding `Fin.sum_univ_two`/`Fin.prod_univ_two` by
hand instead of calling the general lemma. Generalizing costs nothing extra over hardcoding `Fin 3`:
the `Fin 3` instance is recovered for free by specializing `σ := Fin 3`, with no bespoke `Fin 3`
development needed at all.

The convergence argument is the same geometric one used throughout this development: a coefficient
of algebra-mapped norm at most `1`, evaluated at a point `y : σ → K` with every coordinate of norm
`< 1`, contributes a term bounded by `(Finset.univ.sup' _ fun i => ‖y i‖) ^ n.degree` (the general
finite-`σ` analogue of `Fin 2`'s `max ‖y 0‖ ‖y 1‖`).

`[Nonempty σ]` is assumed throughout so that `Finset.univ : Finset σ` is nonempty and
`Finset.sup'` (rather than the `OrderBot`-requiring `Finset.sup`, unusable for `ℝ`) applies
directly; both intended instantiations (`Fin 2`, `Fin 3`) satisfy this.

## What this does not do

No compatibility with `MvPowerSeries.subst`/`PowerSeries.subst` is proved here, matching the scope
of `Langlands.NonarchimedeanMvPowerSeriesEvalFin2`. This file's `evalMv`/`evalMv_mul`/`evalMv_pow`
are meant to feed two `Fin 3`-arity eval-subst compatibility results, which remain unbuilt.
-/

@[expose] public section

noncomputable section

namespace NonarchimedeanMvPowerSeriesEval

variable {σ R K : Type*} [Fintype σ] [Nonempty σ] [DecidableEq σ] [CommRing R] [NormedField K]
  [IsUltrametricDist K] [CompleteSpace K] [Algebra R K]

/-- The `n`-th summand of the multivariate evaluation series
`Σ (algebraMap (coeff n Φ)) * ∏ i, y i ^ n i`. -/
def evalSummandMv (Φ : MvPowerSeries σ R) (y : σ → K) (n : σ →₀ ℕ) : K :=
  algebraMap R K (MvPowerSeries.coeff n Φ) * ∏ i, y i ^ (n i)

omit [DecidableEq σ] [IsUltrametricDist K] [CompleteSpace K] in
/-- **The per-term bound**: if every coefficient of `Φ`, algebra-mapped into `K`, has norm at most
`1`, then the `n`-th evaluation summand at `y` has norm at most
`(Finset.univ.sup' _ fun i => ‖y i‖) ^ n.degree`. -/
theorem norm_evalSummandMv_le {Φ : MvPowerSeries σ R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) (y : σ → K) (n : σ →₀ ℕ) :
    ‖evalSummandMv Φ y n‖ ≤ (Finset.univ.sup' Finset.univ_nonempty fun i => ‖y i‖) ^ n.degree := by
  unfold evalSummandMv
  set r := Finset.univ.sup' Finset.univ_nonempty fun i => ‖y i‖ with hrdef
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg (y (Classical.arbitrary σ)))
    (Finset.le_sup' (fun i => ‖y i‖) (Finset.mem_univ (Classical.arbitrary σ)))
  have hy : ∀ i, ‖y i‖ ≤ r := fun i ↦ Finset.le_sup' (fun i => ‖y i‖) (Finset.mem_univ i)
  rw [norm_mul, norm_prod]
  calc ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ * ∏ i, ‖y i ^ (n i)‖
      ≤ 1 * ∏ i, r ^ n i := by
        refine mul_le_mul (hΦ n) ?_ (Finset.prod_nonneg fun i _ ↦ norm_nonneg _) zero_le_one
        refine Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) (fun i _ ↦ ?_)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hy i) _
    _ = r ^ n.degree := by rw [one_mul, Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]

omit [DecidableEq σ] [IsUltrametricDist K] [CompleteSpace K] in
/-- **Unconditional convergence to `0` along `cofinite`.** Given every coordinate of `y` has norm
`< 1`, for every `ε > 0` the set of multi-indices whose term exceeds `ε` is contained in the
(finite, by `Finsupp.finite_of_degree_lt`) set of multi-indices of total degree below a threshold
`D` chosen so that `(Finset.univ.sup' _ fun i => ‖y i‖) ^ D < ε`. -/
theorem tendsto_evalSummandMv_cofinite_zero {Φ : MvPowerSeries σ R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : σ → K}
    (hy : ∀ i, ‖y i‖ < 1) :
    Filter.Tendsto (evalSummandMv Φ y) Filter.cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  set r := Finset.univ.sup' Finset.univ_nonempty fun i => ‖y i‖ with hrdef
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg (y (Classical.arbitrary σ)))
    (Finset.le_sup' (fun i => ‖y i‖) (Finset.mem_univ (Classical.arbitrary σ)))
  have hr1 : r < 1 := (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ ↦ hy i)
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε hr1
  have hsub : {n : σ →₀ ℕ | ¬ dist (evalSummandMv Φ y n) 0 < ε} ⊆
      {n : σ →₀ ℕ | Finsupp.degree n < D} := by
    intro n hn
    simp only [Set.mem_setOf_eq, not_lt, dist_eq_norm, sub_zero] at hn
    by_contra hge
    simp only [Set.mem_setOf_eq, not_lt] at hge
    have hbound : ‖evalSummandMv Φ y n‖ ≤ r ^ n.degree := norm_evalSummandMv_le hΦ y n
    have hmono : r ^ n.degree ≤ r ^ D := pow_le_pow_of_le_one hr0 hr1.le hge
    linarith [hbound, hmono, hD]
  exact (Finsupp.finite_of_degree_lt (σ := σ) D).subset hsub

omit [DecidableEq σ] in
/-- **Unconditional summability of the multivariate evaluation series.** -/
theorem summable_evalSummandMv {Φ : MvPowerSeries σ R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : σ → K}
    (hy : ∀ i, ‖y i‖ < 1) :
    Summable (evalSummandMv Φ y) :=
  IsUltrametricDist.summable_of_tendsto_zero (tendsto_evalSummandMv_cofinite_zero hΦ hy)

/-- **Evaluation of a multivariate power series at a concrete point**, unconditionally defined as
`∑' n, evalSummandMv Φ y n` (`0` when not summable); meaningful exactly when `Φ`'s coefficients are
algebra-mapped-norm-bounded by `1` and every coordinate of `y` has norm `< 1`, per `hasSum_evalMv`.
-/
def evalMv (Φ : MvPowerSeries σ R) (y : σ → K) : K := ∑' n, evalSummandMv Φ y n

omit [DecidableEq σ] in
/-- **The defining property of `evalMv`**: on the domain where it is meaningful, the evaluation
summands genuinely (unconditionally) sum to `evalMv Φ y` — the precise sense in which the
evaluation "agrees with" the formal object `Φ`. -/
theorem hasSum_evalMv {Φ : MvPowerSeries σ R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : σ → K}
    (hy : ∀ i, ‖y i‖ < 1) :
    HasSum (evalSummandMv Φ y) (evalMv Φ y) :=
  (summable_evalSummandMv hΦ hy).hasSum

omit [DecidableEq σ] [CompleteSpace K] in
/-- **`evalMv Φ y` lies in the maximal ideal whenever `Φ` does**: if `Φ` has zero constant term
(so the index-`0` evaluation summand vanishes) and bounded coefficients,
`‖evalMv Φ y‖ ≤ Finset.univ.sup' _ fun i => ‖y i‖`. Via the ultrametric bound
`IsUltrametricDist.norm_tsum_le`, applied to `evalSummandMv Φ y`, mirroring
`NonarchimedeanPowerSeriesEval.norm_eval_le`. -/
theorem norm_evalMv_le {Φ : MvPowerSeries σ R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1)
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) {y : σ → K} (hy : ∀ i, ‖y i‖ < 1) :
    ‖evalMv Φ y‖ ≤ Finset.univ.sup' Finset.univ_nonempty fun i => ‖y i‖ := by
  unfold evalMv
  set r := Finset.univ.sup' Finset.univ_nonempty fun i => ‖y i‖ with hrdef
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg (y (Classical.arbitrary σ)))
    (Finset.le_sup' (fun i => ‖y i‖) (Finset.mem_univ (Classical.arbitrary σ)))
  have hr1 : r < 1 := (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ ↦ hy i)
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

omit [Nonempty σ] [DecidableEq σ] [IsUltrametricDist K] [CompleteSpace K] in
/-- **`evalMv Φ y = 0` when every coordinate of `y` is `0`**, given `Φ` has zero constant term:
every summand of index `n ≠ 0` has some factor `y i ^ n i` with `n i ≠ 0` and `y i = 0`, hence
vanishes; the index-`0` summand vanishes because `Φ`'s constant term does. -/
theorem evalMv_eq_zero_of_zero {Φ : MvPowerSeries σ R}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) {y : σ → K} (hy : ∀ i, y i = 0) :
    evalMv Φ y = 0 := by
  have hterm : ∀ n : σ →₀ ℕ, evalSummandMv Φ y n = 0 := by
    intro n
    unfold evalSummandMv
    rcases eq_or_ne n 0 with hn | hn
    · rw [hn, MvPowerSeries.coeff_zero_eq_constantCoeff, hΦ0, map_zero, zero_mul]
    · obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp hn
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hy i]; exact zero_pow hi), mul_zero]
  unfold evalMv
  simp [hterm]

omit [Fintype σ] [Nonempty σ] [IsUltrametricDist K] [CompleteSpace K] in
/-- The coefficients of `1 : MvPowerSeries σ R`, algebra-mapped into `K`, are trivially bounded by
`1`. -/
theorem coeff_bound_one_mv :
    ∀ n : σ →₀ ℕ, ‖algebraMap R K (MvPowerSeries.coeff n (1 : MvPowerSeries σ R))‖ ≤ 1 := by
  intro n
  rw [MvPowerSeries.coeff_one]
  split <;> simp

omit [Nonempty σ] [IsUltrametricDist K] [CompleteSpace K] in
/-- **Evaluation at `1` is `1`**: only the constant term (`= 1`) contributes. -/
theorem evalMv_one (y : σ → K) : evalMv (1 : MvPowerSeries σ R) y = 1 := by
  have hterm : ∀ n : σ →₀ ℕ, evalSummandMv (1 : MvPowerSeries σ R) y n =
      if n = 0 then 1 else 0 := by
    intro n
    unfold evalSummandMv
    rw [MvPowerSeries.coeff_one]
    by_cases h : n = 0 <;> simp [h]
  unfold evalMv
  rw [tsum_eq_single 0 (by intro n hn; rw [hterm]; simp [hn])]
  rw [hterm]; simp

omit [Fintype σ] [Nonempty σ] [IsUltrametricDist K] [CompleteSpace K] in
/-- The coefficients of a coordinate variable `X j`, algebra-mapped into `K`, are trivially bounded
by `1` (each is `0` or `1`). -/
theorem coeff_bound_X_mv (j : σ) : ∀ n : σ →₀ ℕ,
    ‖algebraMap R K (MvPowerSeries.coeff n (MvPowerSeries.X j : MvPowerSeries σ R))‖ ≤ 1 := by
  intro n
  rw [MvPowerSeries.coeff_X]
  split <;> simp

omit [Nonempty σ] [IsUltrametricDist K] [CompleteSpace K] in
/-- **Evaluating a coordinate variable returns that coordinate**: `evalMv (X j) z = z j`. Only the
multi-index `Finsupp.single j 1` contributes. -/
theorem evalMv_X (j : σ) (z : σ → K) :
    evalMv (MvPowerSeries.X j : MvPowerSeries σ R) z = z j := by
  have hterm : ∀ n : σ →₀ ℕ,
      evalSummandMv (MvPowerSeries.X j : MvPowerSeries σ R) z n =
        if n = Finsupp.single j 1 then z j else 0 := by
    intro n
    unfold evalSummandMv
    rw [MvPowerSeries.coeff_X]
    by_cases h : n = Finsupp.single j 1
    · subst h
      rw [if_pos rfl, if_pos rfl, map_one, one_mul,
        Finset.prod_eq_single j
          (fun i _ hij ↦ by rw [Finsupp.single_eq_of_ne' hij.symm, pow_zero])
          (by simp)]
      simp
    · rw [if_neg h, if_neg h, map_zero, zero_mul]
  unfold evalMv
  rw [tsum_eq_single (Finsupp.single j 1) (by intro n hn; rw [hterm, if_neg hn])]
  rw [hterm, if_pos rfl]

omit [Fintype σ] [Nonempty σ] [CompleteSpace K] in
/-- **Coefficient boundedness is preserved by multiplication.** `coeff n (Φ * Ψ)` is a sum, over
`Finset.HasAntidiagonal.antidiagonal n`, of products of bounded coefficients; the nonempty-sum
ultrametric bound `Finset.Nonempty.norm_sum_le_sup'_norm` bounds it by `1`. -/
theorem coeff_bound_mul_mv {Φ Ψ : MvPowerSeries σ R}
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

omit [Fintype σ] [Nonempty σ] [CompleteSpace K] in
/-- **Coefficient boundedness is preserved by powers**, by induction on `coeff_bound_mul_mv`. -/
theorem coeff_bound_pow_mv {Φ : MvPowerSeries σ R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) :
    ∀ (m : ℕ) (n : σ →₀ ℕ), ‖algebraMap R K (MvPowerSeries.coeff n (Φ ^ m))‖ ≤ 1 := by
  intro m
  induction m with
  | zero => intro n; simpa using coeff_bound_one_mv (σ := σ) (R := R) (K := K) n
  | succ m ih => intro n; rw [pow_succ]; exact coeff_bound_mul_mv ih hΦ n

/-- **Evaluation is multiplicative**, on the domain where both series have
algebra-mapped-norm-bounded coefficients and every point coordinate lies in the maximal ideal.
Mirrors `NonarchimedeanMvPowerSeriesEvalFin2.evalMv_mul`, with `Fin 2 →₀ ℕ` generalized to
`σ →₀ ℕ`: the Cauchy product formula `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` regroups the
`(σ →₀ ℕ) × (σ →₀ ℕ)`-indexed product family (summable via `HasSum.mul_of_nonarchimedean`, using
the `NonarchimedeanRing K` instance from `Langlands.NonarchimedeanPowerSeriesEval`) by
`Finset.HasAntidiagonal.antidiagonal`, matching `MvPowerSeries.coeff_mul` term-by-term. -/
theorem evalMv_mul {Φ Ψ : MvPowerSeries σ R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1)
    (hΨ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Ψ)‖ ≤ 1) {y : σ → K}
    (hy : ∀ i, ‖y i‖ < 1) :
    evalMv (Φ * Ψ) y = evalMv Φ y * evalMv Ψ y := by
  have hfg : Summable (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) =>
      evalSummandMv Φ y p.1 * evalSummandMv Ψ y p.2) :=
    ((hasSum_evalMv hΦ hy).mul_of_nonarchimedean (hasSum_evalMv hΨ hy)).summable
  unfold evalMv
  rw [(summable_evalSummandMv hΦ hy).tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (summable_evalSummandMv hΨ hy) hfg]
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
theorem evalMv_pow {Φ : MvPowerSeries σ R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : σ → K}
    (hy : ∀ i, ‖y i‖ < 1) :
    ∀ m, evalMv (Φ ^ m) y = evalMv Φ y ^ m
  | 0 => by simpa using evalMv_one (σ := σ) (R := R) (K := K) y
  | m + 1 => by
      rw [pow_succ, pow_succ, evalMv_mul (coeff_bound_pow_mv hΦ m) hΦ hy, evalMv_pow hΦ hy m]

end NonarchimedeanMvPowerSeriesEval

end
