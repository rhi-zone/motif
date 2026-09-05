import Mathlib.RingTheory.PowerSeries.Substitution
import Langlands.NonarchimedeanPowerSeriesEvalSubst
import Langlands.NonarchimedeanMvPowerSeriesEvalFin2
import Langlands.NonarchimedeanCofiniteTendstoOfDegreeBound

/-!
# Univariate-outer eval-subst compatibility: `eval g (evalMv Φ y) = evalMv (g.subst Φ) y`

For `g : PowerSeries R` (univariate outer), substituted by a
*single* bivariate substitutand `Φ : MvPowerSeries (Fin 2) R` (zero constant term), the result lands back in
`MvPowerSeries (Fin 2) R`; evaluating the composite multivariately at a point `y : Fin 2 → K`
agrees with evaluating `g` univariately at the point obtained by evaluating `Φ` multivariately at
`y` first.

## Route

The same double-series-interchange shape as `Langlands.NonarchimedeanPowerSeriesEvalSubst.eval_subst`
and `Langlands.NonarchimedeanPowerSeriesEvalSubstMv.eval_subst_mv`, with the *roles* of the two
index types swapped relative to `eval_subst_mv`: here the **outer** index is `d : ℕ` (the power of
`Φ` a term of `g` selects) and the **inner "row"** index is `n : Fin 2 →₀ ℕ` (`Φ`'s own multi-index).

Concretely, set `T : ℕ × (Fin 2 →₀ ℕ) → K := fun (d, n) ↦ algebraMap R K (coeff d g) *
evalSummandMv (Φ ^ d) y n`.

* `coeff_eq_zero_pow_of_lt_mv` : `Φ ^ d`'s coefficient at any multi-index `n` with `n.degree < d`
  vanishes, from `MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero` and
  `MvPowerSeries.coeff_of_lt_order`.
* `coeff_subst_finset_degree_A` : the finite-range form of `PowerSeries.coeff_subst` (with
  substitutand `Φ`): `coeff n (g.subst Φ)` is the *finite* sum, over `d ≤ n.degree`, of
  `coeff d g • coeff n (Φ ^ d)`.
* `hasSum_row_d_A` : grouping `T` by `d`, the row `n ↦ T (d, n)` sums to
  `NonarchimedeanPowerSeriesEval.evalSummand g (evalMv Φ y) d` — via `hasSum_evalMv` on `Φ ^ d` at
  `y` and `NonarchimedeanMvPowerSeriesEvalFin2.evalMv_pow`.
* `hasSum_row_e_A` : grouping `T` by `n`, the row `d ↦ T (d, n)` sums to
  `evalSummandMv (g.subst Φ) y n`, via `coeff_subst_finset_degree_A`.
* `tendsto_T_cofinite_zero_A` : the uniform bound `‖T (d, n)‖ ≤ (max ‖y 0‖ ‖y 1‖) ^ n.degree`
  together with `T (d, n) = 0` whenever `n.degree < d` confine `{(d, n) : ‖T (d, n)‖ ≥ ε}` to a
  finite box, via `Finsupp.finite_of_degree_lt`/`Set.finite_Iio`.
* `eval_subst_A` : chaining the two identifications, via `HasSum.prod_fiberwise` (grouping by `d`)
  and by `n` (after `Equiv.hasSum_iff (Equiv.prodComm _ _)`), exactly as in the other two files.

## What this does not do

This is the univariate-outer case only. Combined with the diagonal-substitution compatibility fact
(`Langlands.NonarchimedeanMvPowerSeriesEvalSubstDiagonal`), it gives the closure fact `piTorsion`
needs — assembled in `Langlands.LubinTateTorsionPoints`.
-/

@[expose] public section

noncomputable section

namespace NonarchimedeanPowerSeriesEval

open NonarchimedeanMvPowerSeriesEvalFin2

variable {R K : Type*} [CommRing R] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra R K]

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra R K] in
/-- `Φ ^ d`'s coefficient at any multi-index `n` with `n.degree < d` vanishes, given `Φ` has zero
constant term. -/
theorem coeff_eq_zero_pow_of_lt_mv {Φ : MvPowerSeries (Fin 2) R}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) {d : ℕ} {n : Fin 2 →₀ ℕ} (hlt : n.degree < d) :
    MvPowerSeries.coeff n (Φ ^ d) = 0 :=
  MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hlt)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d hΦ0))

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The finite-degree form of `PowerSeries.coeff_subst`**, substitutand `Φ` a single bivariate
series with zero constant term: the `n`-th coefficient of `g.subst Φ` is the *finite* sum, over
`d ≤ n.degree`, of `coeff d g • coeff n (Φ ^ d)`. -/
theorem coeff_subst_finset_degree_A {g : PowerSeries R} {Φ : MvPowerSeries (Fin 2) R}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (PowerSeries.subst Φ g) =
      ∑ d ∈ Finset.range (n.degree + 1),
        PowerSeries.coeff d g • MvPowerSeries.coeff n (Φ ^ d) := by
  have ha : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero hΦ0
  rw [PowerSeries.coeff_subst ha]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support] at hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hge
  push Not at hge
  exact hd (by rw [coeff_eq_zero_pow_of_lt_mv hΦ0 (by omega), smul_zero])

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Grouping `T (d, n) := algebraMap (coeff d g) * evalSummandMv (Φ ^ d) y n` by `n`**: the row
`d ↦ T (d, n)` sums to `evalSummandMv (g.subst Φ) y n`. -/
theorem hasSum_row_e_A {g : PowerSeries R} {Φ : MvPowerSeries (Fin 2) R}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) (y : Fin 2 → K) (n : Fin 2 →₀ ℕ) :
    HasSum (fun d : ℕ ↦ algebraMap R K (PowerSeries.coeff d g) * evalSummandMv (Φ ^ d) y n)
      (evalSummandMv (PowerSeries.subst Φ g) y n) := by
  set s := Finset.range (n.degree + 1) with hsdef
  have hzero : ∀ d ∉ s, algebraMap R K (PowerSeries.coeff d g) * evalSummandMv (Φ ^ d) y n = 0 := by
    intro d hd
    rw [hsdef, Finset.mem_range, not_lt] at hd
    unfold evalSummandMv
    rw [coeff_eq_zero_pow_of_lt_mv hΦ0 (by omega), map_zero, zero_mul, mul_zero]
  have hval : HasSum
      (fun d : ℕ ↦ algebraMap R K (PowerSeries.coeff d g) * evalSummandMv (Φ ^ d) y n)
      (∑ d ∈ s, algebraMap R K (PowerSeries.coeff d g) * evalSummandMv (Φ ^ d) y n) :=
    hasSum_sum_of_ne_finset_zero hzero
  convert hval using 1
  unfold evalSummandMv
  rw [coeff_subst_finset_degree_A hΦ0 n, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [smul_eq_mul, map_mul]
  ring

/-- **Grouping `T (d, n) := algebraMap (coeff d g) * evalSummandMv (Φ ^ d) y n` by `d`**: the row
`n ↦ T (d, n)` sums to `evalSummand g (evalMv Φ y) d`. -/
theorem hasSum_row_d_A {g : PowerSeries R} {Φ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) (d : ℕ) :
    HasSum (fun n : Fin 2 →₀ ℕ ↦ algebraMap R K (PowerSeries.coeff d g) *
        evalSummandMv (Φ ^ d) y n)
      (evalSummand g (evalMv Φ y) d) := by
  have h1 : HasSum (evalSummandMv (Φ ^ d) y) (evalMv (Φ ^ d) y) :=
    hasSum_evalMv (coeff_bound_pow_mv hΦ d) hy0 hy1
  have h2 := h1.mul_left (algebraMap R K (PowerSeries.coeff d g))
  rwa [evalMv_pow hΦ hy0 hy1 d] at h2

omit [CompleteSpace K] in
/-- **`T` tends to `0` along `cofinite` on `ℕ × (Fin 2 →₀ ℕ)`**: a direct application of
`tendsto_zero_cofinite_of_degree_bound`, with `wt := id`, `deg := Finsupp.degree`,
`r := max ‖y 0‖ ‖y 1‖`, the uniform bound `‖T (d, n)‖ ≤ r ^ n.degree`, and exact vanishing from
`coeff_eq_zero_pow_of_lt_mv` (`T (d, n) = 0` when `n.degree < d`). -/
theorem tendsto_T_cofinite_zero_A {g : PowerSeries R} {Φ : MvPowerSeries (Fin 2) R}
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1)
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0)
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) :
    Filter.Tendsto
      (fun p : ℕ × (Fin 2 →₀ ℕ) ↦ algebraMap R K (PowerSeries.coeff p.1 g) *
        evalSummandMv (Φ ^ p.1) y p.2)
      Filter.cofinite (nhds 0) := by
  have hr0 : (0 : ℝ) ≤ max ‖y 0‖ ‖y 1‖ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hr1 : max ‖y 0‖ ‖y 1‖ < 1 := max_lt hy0 hy1
  exact tendsto_zero_cofinite_of_degree_bound _ id Finsupp.degree hr0 hr1
    (fun p => by
      rw [norm_mul]
      calc ‖algebraMap R K (PowerSeries.coeff p.1 g)‖ * ‖evalSummandMv (Φ ^ p.1) y p.2‖
          ≤ 1 * (max ‖y 0‖ ‖y 1‖) ^ p.2.degree :=
            mul_le_mul (hg p.1) (norm_evalSummandMv_le (coeff_bound_pow_mv hΦ p.1) y p.2)
              (norm_nonneg _) zero_le_one
        _ = (max ‖y 0‖ ‖y 1‖) ^ p.2.degree := one_mul _)
    (fun p (hlt : p.2.degree < p.1) => by
      unfold evalSummandMv
      rw [coeff_eq_zero_pow_of_lt_mv hΦ0 hlt, map_zero, zero_mul, mul_zero])
    (fun D => Set.finite_Iic D) (fun D => Finsupp.finite_of_degree_lt (σ := Fin 2) D)

set_option maxHeartbeats 1000000 in
/-- **Univariate-outer eval-subst compatibility.**
`eval g (evalMv Φ y) = evalMv (g.subst Φ) y`, for `g : PowerSeries R` and a *single* bivariate
substitutand `Φ : MvPowerSeries (Fin 2) R` with zero constant term. -/
theorem eval_subst_A {g : PowerSeries R} {Φ : MvPowerSeries (Fin 2) R}
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1)
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0)
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) (hΦy : ‖evalMv Φ y‖ < 1) :
    eval g (evalMv Φ y) = evalMv (PowerSeries.subst Φ g) y := by
  set T : ℕ × (Fin 2 →₀ ℕ) → K :=
    fun p ↦ algebraMap R K (PowerSeries.coeff p.1 g) * evalSummandMv (Φ ^ p.1) y p.2 with hTdef
  have hTsum : Summable T :=
    IsUltrametricDist.summable_of_tendsto_zero (tendsto_T_cofinite_zero_A hg hΦ0 hΦ hy0 hy1)
  set A := ∑' p, T p with hAdef
  have hTA : HasSum T A := hTsum.hasSum
  -- group by `d`
  have hbyD : HasSum (fun d : ℕ ↦ evalSummand g (evalMv Φ y) d) A :=
    hTA.prod_fiberwise (fun d ↦ hasSum_row_d_A hΦ hy0 hy1 d)
  have hAeq1 : A = eval g (evalMv Φ y) := hbyD.unique (hasSum_eval hg hΦy)
  -- group by `n`
  have hbyE : HasSum (evalSummandMv (PowerSeries.subst Φ g) y) A := by
    have hTswap : HasSum (fun q : (Fin 2 →₀ ℕ) × ℕ ↦ T (q.2, q.1)) A :=
      (Equiv.hasSum_iff (Equiv.prodComm (Fin 2 →₀ ℕ) ℕ)).mpr hTA
    exact hTswap.prod_fiberwise (fun n ↦ hasSum_row_e_A hΦ0 y n)
  have hAeq2 : evalMv (PowerSeries.subst Φ g) y = A := by
    unfold evalMv; exact hbyE.tsum_eq
  rw [hAeq2, hAeq1]

end NonarchimedeanPowerSeriesEval

end
