import Mathlib.RingTheory.MvPowerSeries.Order
import Langlands.NonarchimedeanPowerSeriesEvalSubst
import Langlands.NonarchimedeanMvPowerSeriesEvalFin2

/-!
# Bivariate-outer eval-subst compatibility: `eval (Φ.subst A) x = evalMv Φ (fun i ↦ eval (A i) x)`

`ROADMAP.md` §22 re-scoped this as the sole remaining prerequisite for the Lubin-Tate
torsion-point thread's next steps, and pre-verified every Mathlib lemma the proof needs.
This file closes it: for `Φ : MvPowerSeries (Fin 2) R` and a **univariate** family
`A : Fin 2 → PowerSeries R` (each `A i` with zero constant term), substituting `A` into `Φ`
(landing back in `PowerSeries R = MvPowerSeries Unit R`, since each `A i` is univariate) and then
evaluating at a point `x : K` agrees with evaluating `Φ` multivariately at the point obtained by
evaluating each `A i` at `x` first.

## Route

Same double-series-interchange shape as
`Langlands.NonarchimedeanPowerSeriesEvalSubst.eval_subst`, with the outer index generalized from
`ℕ` to `Fin 2 →₀ ℕ` (the "which power of each `A i`" multi-index) and the inner "row" reduced,
via `prod_family_fin2`, to an ordinary product of two univariate powers `A 0 ^ d 0 * A 1 ^ d 1`
rather than a fresh multivariate object — so the inner sums are handled entirely by this
repo's already-closed `NonarchimedeanPowerSeriesEval.eval_mul`/`eval_pow`, exactly as
`NonarchimedeanPowerSeriesEvalSubst`'s own module docstring anticipated.

Concretely, set `T : (Fin 2 →₀ ℕ) × ℕ → K := fun (d, e) ↦ algebraMap R K (coeff d Φ) *
evalSummand (A 0 ^ d 0 * A 1 ^ d 1) x e`.

* `order_prod_family_ge` : `A 0 ^ d 0 * A 1 ^ d 1` has order `≥ d.degree` — from
  `PowerSeries.le_order_pow_of_constantCoeff_eq_zero` on each factor and
  `PowerSeries.le_order_mul` combining them, matching `d.degree = d 0 + d 1`
  (`NonarchimedeanMvPowerSeriesEvalFin2.degree_fin_two`).
* `tendsto_T_cofinite_zero_mv` : as in the univariate file, the uniform bound `‖T (d, e)‖ ≤ ‖x‖ ^ e`
  together with `T (d, e) = 0` whenever `e < d.degree` confine `{(d, e) : ‖T (d, e)‖ ≥ ε}` to a
  finite box, this time using `Finsupp.finite_of_degree_le`/`Set.Finite.prod` in place of
  `Finset.range ×ˢ Finset.range`.
* `hasSum_row_d_mv` : grouping by `d`, the row `e ↦ T (d, e)` sums to `evalSummandMv Φ (fun i ↦
  eval (A i) x) d` — via `hasSum_eval` on the product, `eval_mul`, `eval_pow`, and
  `Fin.prod_univ_two`.
* `coeff_subst_finset_degree`, `hasSum_row_e_mv` : grouping by `e`, the row `d ↦ T (d, e)` sums to
  `evalSummand (MvPowerSeries.subst A Φ) x e` — `MvPowerSeries.coeff_subst`'s `finsum` collapses
  to a finite sum over `{d | d.degree ≤ e}` (`Finsupp.finite_of_degree_le`), matching `T`'s own
  finite-support row.
* `eval_subst_mv` : chaining the two identifications, via `HasSum.prod_fiberwise` (grouping by
  `d`) and by `e` (after `Equiv.hasSum_iff (Equiv.prodComm _ _)`), exactly as in the univariate
  file.

## What this does not do

This closes the case needed for `FormalGroupInverse.subst_Phi_subst_PhiInv_eq_zero` (whose
substitutand family is univariate: `![A, PowerSeries.subst A (PhiInv hπ hf)]`). It does **not**
close the *same-arity* case `LubinTateIterate.subst_iter_Phi` needs — there, `Φ` is substituted by
a family `Fin 2 → MvPowerSeries (Fin 2) R` (each component a univariate series *embedded* along
one axis, not landing in `Unit`-space), and the result is itself bivariate. See `ROADMAP.md` for
the precise re-scoping of that remaining piece.
-/

@[expose] public section

noncomputable section

namespace NonarchimedeanPowerSeriesEval

open NonarchimedeanMvPowerSeriesEvalFin2

variable {R K : Type*} [CommRing R] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra R K]

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra R K] in
/-- Every `d.prod` term in `MvPowerSeries.coeff_subst`'s expansion, for a univariate family
`A : Fin 2 → PowerSeries R`, collapses to the ordinary product `A 0 ^ (d 0) * A 1 ^ (d 1)`. -/
theorem prod_family_fin2 (A : Fin 2 → PowerSeries R) (d : Fin 2 →₀ ℕ) :
    (d.prod fun s j ↦ (A s : MvPowerSeries Unit R) ^ j) = A 0 ^ (d 0) * A 1 ^ (d 1) := by
  rw [Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _), Fin.prod_univ_two]

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra R K] in
/-- `A 0 ^ (d 0) * A 1 ^ (d 1)` has order at least `d.degree`, given both `A 0` and `A 1` have
zero constant term. -/
theorem order_prod_family_ge {A : Fin 2 → PowerSeries R}
    (hA0 : PowerSeries.constantCoeff (A 0) = 0) (hA1 : PowerSeries.constantCoeff (A 1) = 0)
    (d : Fin 2 →₀ ℕ) :
    (d.degree : ℕ∞) ≤ (A 0 ^ (d 0) * A 1 ^ (d 1)).order := by
  have h0 : (d 0 : ℕ∞) ≤ (A 0 ^ (d 0)).order :=
    PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ hA0
  have h1 : (d 1 : ℕ∞) ≤ (A 1 ^ (d 1)).order :=
    PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ hA1
  calc (d.degree : ℕ∞) = (d 0 : ℕ∞) + (d 1 : ℕ∞) := by
        rw [degree_fin_two]; push_cast; ring
    _ ≤ (A 0 ^ (d 0)).order + (A 1 ^ (d 1)).order := add_le_add h0 h1
    _ ≤ (A 0 ^ (d 0) * A 1 ^ (d 1)).order := PowerSeries.le_order_mul _ _

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra R K] in
/-- `A 0 ^ (d 0) * A 1 ^ (d 1)`'s coefficient at any index `e < d.degree` vanishes. -/
theorem coeff_eq_zero_prod_family_of_lt {A : Fin 2 → PowerSeries R}
    (hA0 : PowerSeries.constantCoeff (A 0) = 0) (hA1 : PowerSeries.constantCoeff (A 1) = 0)
    {d : Fin 2 →₀ ℕ} {e : ℕ} (hlt : e < d.degree) :
    PowerSeries.coeff e (A 0 ^ (d 0) * A 1 ^ (d 1)) = 0 :=
  PowerSeries.coeff_of_lt_order e (lt_of_lt_of_le (by exact_mod_cast hlt)
    (order_prod_family_ge hA0 hA1 d))

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The finite-degree form of `MvPowerSeries.coeff_subst`**: for a univariate family `A`, both
of whose components have zero constant term, the `e`-th coefficient of `Φ.subst A` (as a
univariate power series) is the *finite* sum, over `{d | d.degree ≤ e}`, of `coeff d Φ • coeff e
(A 0 ^ (d 0) * A 1 ^ (d 1))`. -/
theorem coeff_subst_finset_degree {Φ : MvPowerSeries (Fin 2) R} {A : Fin 2 → PowerSeries R}
    (hA0 : PowerSeries.constantCoeff (A 0) = 0) (hA1 : PowerSeries.constantCoeff (A 1) = 0)
    (e : ℕ) :
    PowerSeries.coeff e (MvPowerSeries.subst A Φ) =
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := Fin 2) e).toFinset,
        MvPowerSeries.coeff d Φ • PowerSeries.coeff e (A 0 ^ (d 0) * A 1 ^ (d 1)) := by
  have hAfam : ∀ i, PowerSeries.constantCoeff (A i) = 0 := fun i ↦ by fin_cases i <;> assumption
  have ha : MvPowerSeries.HasSubst A := MvPowerSeries.hasSubst_of_constantCoeff_zero hAfam
  rw [← PowerSeries.coeff_coeToMvPowerSeries e, MvPowerSeries.coeff_subst ha]
  rw [finsum_eq_sum_of_support_subset _ (s := (Finsupp.finite_of_degree_le (σ := Fin 2) e).toFinset)]
  · apply Finset.sum_congr rfl
    intro d _
    rw [prod_family_fin2, PowerSeries.coeff_coeToMvPowerSeries]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    by_contra hge
    push Not at hge
    apply hd
    rw [prod_family_fin2, PowerSeries.coeff_coeToMvPowerSeries,
      coeff_eq_zero_prod_family_of_lt hA0 hA1 (by omega), smul_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Grouping `T (d, e) := algebraMap (coeff d Φ) * evalSummand (A 0 ^ d 0 * A 1 ^ d 1) x e` by
`e`**: the row `d ↦ T (d, e)` sums to `evalSummand (MvPowerSeries.subst A Φ) x e`. -/
theorem hasSum_row_e_mv {Φ : MvPowerSeries (Fin 2) R} {A : Fin 2 → PowerSeries R}
    (hA0 : PowerSeries.constantCoeff (A 0) = 0) (hA1 : PowerSeries.constantCoeff (A 1) = 0)
    (x : K) (e : ℕ) :
    HasSum (fun d : Fin 2 →₀ ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummand (A 0 ^ (d 0) * A 1 ^ (d 1)) x e)
      (evalSummand (MvPowerSeries.subst A Φ) x e) := by
  set s := (Finsupp.finite_of_degree_le (σ := Fin 2) e).toFinset with hsdef
  have hzero : ∀ d ∉ s, algebraMap R K (MvPowerSeries.coeff d Φ) *
      evalSummand (A 0 ^ (d 0) * A 1 ^ (d 1)) x e = 0 := by
    intro d hd
    rw [hsdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hd
    unfold evalSummand
    rw [coeff_eq_zero_prod_family_of_lt hA0 hA1 hd, map_zero, zero_mul, mul_zero]
  have hval : HasSum (fun d : Fin 2 →₀ ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
      evalSummand (A 0 ^ (d 0) * A 1 ^ (d 1)) x e)
      (∑ d ∈ s, algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummand (A 0 ^ (d 0) * A 1 ^ (d 1)) x e) :=
    hasSum_sum_of_ne_finset_zero hzero
  convert hval using 1
  unfold evalSummand
  rw [coeff_subst_finset_degree hA0 hA1 e, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [smul_eq_mul, map_mul]
  ring

/-- **Grouping `T (d, e) := algebraMap (coeff d Φ) * evalSummand (A 0 ^ d 0 * A 1 ^ d 1) x e` by
`d`**: the row `e ↦ T (d, e)` sums to `evalSummandMv Φ (fun i ↦ eval (A i) x) d`. -/
theorem hasSum_row_d_mv {Φ : MvPowerSeries (Fin 2) R} {A : Fin 2 → PowerSeries R}
    (hA : ∀ i n, ‖algebraMap R K (PowerSeries.coeff n (A i))‖ ≤ 1) {x : K} (hx : ‖x‖ < 1)
    (d : Fin 2 →₀ ℕ) :
    HasSum (fun e : ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummand (A 0 ^ (d 0) * A 1 ^ (d 1)) x e)
      (evalSummandMv Φ (fun i ↦ eval (A i) x) d) := by
  have h1 : HasSum (evalSummand (A 0 ^ (d 0) * A 1 ^ (d 1)) x)
      (eval (A 0 ^ (d 0) * A 1 ^ (d 1)) x) :=
    hasSum_eval (coeff_bound_mul (coeff_bound_pow (hA 0) (d 0)) (coeff_bound_pow (hA 1) (d 1))) hx
  have h2 := h1.mul_left (algebraMap R K (MvPowerSeries.coeff d Φ))
  have heval : eval (A 0 ^ (d 0) * A 1 ^ (d 1)) x = (eval (A 0) x) ^ (d 0) * (eval (A 1) x) ^ (d 1) := by
    rw [eval_mul (coeff_bound_pow (hA 0) (d 0)) (coeff_bound_pow (hA 1) (d 1)) hx,
      eval_pow (hA 0) hx, eval_pow (hA 1) hx]
  rw [heval] at h2
  unfold evalSummandMv
  rwa [Fin.prod_univ_two]

omit [CompleteSpace K] in
/-- **`T` tends to `0` along `cofinite` on `(Fin 2 →₀ ℕ) × ℕ`**: the uniform bound
`‖T (d, e)‖ ≤ ‖x‖ ^ e` together with `coeff_eq_zero_prod_family_of_lt` (`T (d, e) = 0` when
`e < d.degree`) confine `{(d, e) : ‖T (d, e)‖ ≥ ε}` to a finite box, via
`Finsupp.finite_of_degree_le`/`Set.Finite.prod`. -/
theorem tendsto_T_cofinite_zero_mv {Φ : MvPowerSeries (Fin 2) R} {A : Fin 2 → PowerSeries R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1)
    (hA0 : PowerSeries.constantCoeff (A 0) = 0) (hA1 : PowerSeries.constantCoeff (A 1) = 0)
    (hA : ∀ i n, ‖algebraMap R K (PowerSeries.coeff n (A i))‖ ≤ 1) {x : K} (hx : ‖x‖ < 1) :
    Filter.Tendsto (fun p : (Fin 2 →₀ ℕ) × ℕ ↦ algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
        evalSummand (A 0 ^ (p.1 0) * A 1 ^ (p.1 1)) x p.2)
      Filter.cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε hx
  have hbound : ∀ p : (Fin 2 →₀ ℕ) × ℕ,
      ‖algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
        evalSummand (A 0 ^ (p.1 0) * A 1 ^ (p.1 1)) x p.2‖ ≤ ‖x‖ ^ p.2 := by
    intro p
    rw [norm_mul]
    calc ‖algebraMap R K (MvPowerSeries.coeff p.1 Φ)‖ *
          ‖evalSummand (A 0 ^ (p.1 0) * A 1 ^ (p.1 1)) x p.2‖
        ≤ 1 * ‖x‖ ^ p.2 :=
          mul_le_mul (hΦ p.1) (norm_evalSummand_le
            (coeff_bound_mul (coeff_bound_pow (hA 0) (p.1 0)) (coeff_bound_pow (hA 1) (p.1 1)))
            x p.2) (norm_nonneg _) zero_le_one
      _ = ‖x‖ ^ p.2 := one_mul _
  have hfin : Set.Finite {p : (Fin 2 →₀ ℕ) × ℕ | Finsupp.degree p.1 ≤ D ∧ p.2 < D} := by
    have : {p : (Fin 2 →₀ ℕ) × ℕ | Finsupp.degree p.1 ≤ D ∧ p.2 < D} =
        {d : Fin 2 →₀ ℕ | Finsupp.degree d ≤ D} ×ˢ {e : ℕ | e < D} := rfl
    rw [this]
    exact (Finsupp.finite_of_degree_le D).prod (Set.finite_Iio D)
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq, not_lt, dist_eq_norm, sub_zero] at hp
  have he : p.2 < D := by
    by_contra hge
    push Not at hge
    have := pow_le_pow_of_le_one (norm_nonneg x) hx.le hge
    linarith [hbound p, hD]
  have hd : Finsupp.degree p.1 ≤ p.2 := by
    by_contra hlt
    push Not at hlt
    have hz : algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
        evalSummand (A 0 ^ (p.1 0) * A 1 ^ (p.1 1)) x p.2 = 0 := by
      unfold evalSummand
      rw [coeff_eq_zero_prod_family_of_lt hA0 hA1 hlt, map_zero, zero_mul, mul_zero]
    rw [hz] at hp; simp at hp; linarith
  exact ⟨by omega, he⟩

set_option maxHeartbeats 1000000 in
/-- **Bivariate-outer eval-subst compatibility.** `eval (MvPowerSeries.subst A Φ) x = evalMv Φ
(fun i ↦ eval (A i) x)`, for `Φ : MvPowerSeries (Fin 2) R` and a univariate family
`A : Fin 2 → PowerSeries R` with each `A i` having zero constant term. -/
theorem eval_subst_mv {Φ : MvPowerSeries (Fin 2) R} {A : Fin 2 → PowerSeries R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1)
    (hA0 : PowerSeries.constantCoeff (A 0) = 0) (hA1 : PowerSeries.constantCoeff (A 1) = 0)
    (hA : ∀ i n, ‖algebraMap R K (PowerSeries.coeff n (A i))‖ ≤ 1) {x : K} (hx : ‖x‖ < 1)
    (hAx0 : ‖eval (A 0) x‖ < 1) (hAx1 : ‖eval (A 1) x‖ < 1) :
    eval (MvPowerSeries.subst A Φ) x = evalMv Φ (fun i ↦ eval (A i) x) := by
  set T : (Fin 2 →₀ ℕ) × ℕ → K :=
    fun p ↦ algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
      evalSummand (A 0 ^ (p.1 0) * A 1 ^ (p.1 1)) x p.2 with hTdef
  have hTsum : Summable T :=
    IsUltrametricDist.summable_of_tendsto_zero (tendsto_T_cofinite_zero_mv hΦ hA0 hA1 hA hx)
  set B := ∑' p, T p with hBdef
  have hTB : HasSum T B := hTsum.hasSum
  -- group by `d`
  have hbyD : HasSum (fun d : Fin 2 →₀ ℕ ↦ evalSummandMv Φ (fun i ↦ eval (A i) x) d) B :=
    hTB.prod_fiberwise (fun d ↦ hasSum_row_d_mv hA hx d)
  have hy0 : ‖(fun i ↦ eval (A i) x) 0‖ < 1 := hAx0
  have hy1 : ‖(fun i ↦ eval (A i) x) 1‖ < 1 := hAx1
  have hBeq1 : B = evalMv Φ (fun i ↦ eval (A i) x) := hbyD.unique (hasSum_evalMv hΦ hy0 hy1)
  -- group by `e`
  have hbyE : HasSum (evalSummand (MvPowerSeries.subst A Φ) x) B := by
    have hTswap : HasSum (fun q : ℕ × (Fin 2 →₀ ℕ) ↦ T (q.2, q.1)) B :=
      (Equiv.hasSum_iff (Equiv.prodComm ℕ (Fin 2 →₀ ℕ))).mpr hTB
    exact hTswap.prod_fiberwise (fun e ↦ hasSum_row_e_mv hA0 hA1 x e)
  have hBeq2 : eval (MvPowerSeries.subst A Φ) x = B := by
    unfold eval; exact hbyE.tsum_eq
  rw [hBeq2, hBeq1]

end NonarchimedeanPowerSeriesEval

end
