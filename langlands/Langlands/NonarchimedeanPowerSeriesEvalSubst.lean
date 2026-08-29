import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution
import Langlands.NonarchimedeanPowerSeriesEval

/-!
# Evaluation commutes with substitution: `eval (g.subst h) x = eval g (eval h x)`

This file establishes that evaluation commutes with substitution, for the univariate-into-univariate
case: `g h : PowerSeries R`, `h` with zero
constant term (so `PowerSeries.subst h` makes sense as a substitution), both algebra-mapped into `K`
with coefficients bounded by `1`, `x : K` with `‖x‖ < 1`, and `‖eval h x‖ < 1` (so `g` is itself
evaluable at the point `eval h x`).

## Route

The proof is a genuine double-series-interchange argument, not merely an iteration of `eval_mul`,
because the two "coordinates" being summed over live in genuinely different shapes (`d : ℕ`, the
power of `h` a term of `g` selects; `e : ℕ`, the resulting power of `x`), and the interchange needs a
finiteness fact (`h`'s zero constant term forces `h ^ d` to have order `≥ d`, so for fixed `e` only
finitely many `d ≤ e` contribute) to make sense of regrouping an unconditionally-summed family two
different ways.

Concretely, set `T : ℕ × ℕ → K := fun (d, e) ↦ algebraMap R K (coeff d g) * evalSummand (h ^ d) x e`
— the term where `g`'s `d`-th coefficient meets the `e`-th evaluation-summand of `h ^ d`.

* `tendsto_T_cofinite_zero` : `T` tends to `0` along `cofinite` on `ℕ × ℕ` — from the uniform bound
  `‖T (d, e)‖ ≤ ‖x‖ ^ e` (any `d`, via `coeff_bound_pow`/`norm_evalSummand_le`) together with the
  *exact* vanishing `T (d, e) = 0` whenever `e < d` (`coeff_eq_zero_pow_of_lt`, from `h ^ d`'s order
  being `≥ d`): together these confine `{(d, e) : ‖T (d, e)‖ ≥ ε}` to a finite rectangle. Hence `T` is
  unconditionally `Summable` (`IsUltrametricDist.summable_of_tendsto_zero`), with total sum `A`.
* `hasSum_row_d` : grouping `T` by its first coordinate `d`, the row `e ↦ T (d, e)` sums to
  `evalSummand g (eval h x) d` — from `hasSum_eval` for `h ^ d` at `x`, `HasSum.mul_left`, and
  `eval_pow` (`eval (h ^ d) x = (eval h x) ^ d`). Combined with `HasSum.prod_fiberwise`
  (`Mathlib.Topology.Algebra.InfiniteSum.Constructions`, no separate `RegularSpace`/finiteness
  argument needed beyond what `T`'s own summability already supplies), this identifies `A` with
  `eval g (eval h x)` via `HasSum.unique`.
* `coeff_subst_finset_range`, `hasSum_row_e` : grouping `T` by its second coordinate `e`, the row
  `d ↦ T (d, e)` sums to `evalSummand (g.subst h) x e` — this is where the finiteness fact does its
  work: `PowerSeries.coeff_subst'`'s defining `finsum` for `coeff e (g.subst h)` has support
  contained in `Finset.range (e + 1)` (again from `h ^ d`'s order `≥ d`), so it collapses to a finite
  sum matching `T`'s own finite-support row directly (`hasSum_sum_of_ne_finset_zero`). Grouping via
  `HasSum.prod_fiberwise` after swapping coordinates (`Equiv.hasSum_iff (Equiv.prodComm ℕ ℕ)`)
  identifies `A` with `eval (g.subst h) x`, this time via `HasSum.tsum_eq` directly against `eval`'s
  own definition — no coefficient-boundedness hypothesis on `g.subst h` itself is needed for *this*
  direction, since `eval` is defined unconditionally as a `tsum`.
* `eval_subst` : chaining the two identifications of `A` gives the result.

## What this does not do

This is the univariate-into-univariate case only. The Lubin-Tate torsion-point thread
(`Langlands.LubinTateFormalGroupEval`, `Langlands.LubinTateTorsionPoints`) needs a **bivariate-outer**
form — `eval (MvPowerSeries.subst A Φ) x = evalMv Φ (fun i ↦ eval (A i) x)`, for `Φ : MvPowerSeries
(Fin 2) R` and a univariate family `A : Fin 2 → PowerSeries R` — which is **not** built here. The
proof shape transfers (the same `T`/row-grouping structure works with the outer index `d`
generalized from `ℕ` to `Fin 2 →₀ ℕ`, using `MvPowerSeries.coeff_subst`, `Finsupp.finite_of_degree_lt`
in place of `Finset.range`, and `MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero` in place of
`PowerSeries.le_order_pow_of_constantCoeff_eq_zero`; the inner "row" sums use this file's own
`eval_mul`/`eval_pow` applied to a finite product `∏ i, (A i) ^ (d i)`, not a fresh
multivariate Cauchy product, since each row's target ring stays univariate) but building and
verifying it is a comparably-sized undertaking to this file on its own, and is not done here.
-/

@[expose] public section

noncomputable section

namespace NonarchimedeanPowerSeriesEval

variable {R K : Type*} [CommRing R] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra R K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `h ^ d`'s coefficient at any index `e < d` vanishes, given `h` has zero constant term: `h ^ d`
has order `≥ d` (`PowerSeries.le_order_pow_of_constantCoeff_eq_zero`), so any index below `d` is
below the order. -/
theorem coeff_eq_zero_pow_of_lt {h : PowerSeries R} (hh0 : PowerSeries.constantCoeff h = 0)
    {d e : ℕ} (hlt : e < d) : PowerSeries.coeff e (h ^ d) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hh0)
  exact_mod_cast hlt

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra R K] in
/-- **The finite-range form of `PowerSeries.coeff_subst'`**: for `h` with zero constant term, the
`e`-th coefficient of `g.subst h` is the *finite* sum, over `d ≤ e`, of `coeff d g • coeff e (h ^ d)`
— the general `finsum` version's support is contained in `Finset.range (e + 1)`, by
`coeff_eq_zero_pow_of_lt`. -/
theorem coeff_subst_finset_range {g h : PowerSeries R} (hh0 : PowerSeries.constantCoeff h = 0)
    (e : ℕ) :
    PowerSeries.coeff e (g.subst h) =
      ∑ d ∈ Finset.range (e + 1), PowerSeries.coeff d g • PowerSeries.coeff e (h ^ d) := by
  have hbh : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  rw [PowerSeries.coeff_subst' hbh]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support] at hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hge
  push Not at hge
  exact hd (by rw [coeff_eq_zero_pow_of_lt hh0 (by omega : e < d), smul_zero])

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Grouping `T (d, e) := algebraMap (coeff d g) * evalSummand (h ^ d) x e` by `e`**: the row
`d ↦ T (d, e)` sums to `evalSummand (g.subst h) x e`, using `coeff_subst_finset_range`'s finite-range
form directly against `hasSum_sum_of_ne_finset_zero`. -/
theorem hasSum_row_e {g h : PowerSeries R} (hh0 : PowerSeries.constantCoeff h = 0) (x : K)
    (e : ℕ) :
    HasSum (fun d : ℕ => algebraMap R K (PowerSeries.coeff d g) * evalSummand (h ^ d) x e)
      (evalSummand (g.subst h) x e) := by
  have hzero : ∀ d ∉ Finset.range (e + 1),
      algebraMap R K (PowerSeries.coeff d g) * evalSummand (h ^ d) x e = 0 := by
    intro d hd
    simp only [Finset.mem_range, not_lt] at hd
    unfold evalSummand
    rw [coeff_eq_zero_pow_of_lt hh0 (by omega : e < d), map_zero, zero_mul, mul_zero]
  have hval :
      HasSum (fun d : ℕ => algebraMap R K (PowerSeries.coeff d g) * evalSummand (h ^ d) x e)
        (∑ d ∈ Finset.range (e + 1),
          algebraMap R K (PowerSeries.coeff d g) * evalSummand (h ^ d) x e) :=
    hasSum_sum_of_ne_finset_zero hzero
  convert hval using 1
  unfold evalSummand
  rw [coeff_subst_finset_range hh0 e, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_eq_mul, map_mul]
  ring

/-- **Grouping `T (d, e) := algebraMap (coeff d g) * evalSummand (h ^ d) x e` by `d`**: the row
`e ↦ T (d, e)` sums to `evalSummand g (eval h x) d`, from `hasSum_eval` for `h ^ d` at `x`,
`HasSum.mul_left`, and `eval_pow`. -/
theorem hasSum_row_d {g h : PowerSeries R}
    (hh : ∀ n, ‖algebraMap R K (PowerSeries.coeff n h)‖ ≤ 1) {x : K} (hx : ‖x‖ < 1) (d : ℕ) :
    HasSum (fun e : ℕ => algebraMap R K (PowerSeries.coeff d g) * evalSummand (h ^ d) x e)
      (evalSummand g (eval h x) d) := by
  have h1 : HasSum (evalSummand (h ^ d) x) (eval (h ^ d) x) := hasSum_eval (coeff_bound_pow hh d) hx
  have h2 := h1.mul_left (algebraMap R K (PowerSeries.coeff d g))
  rwa [eval_pow hh hx d] at h2

omit [CompleteSpace K] in
/-- **`T` tends to `0` along `cofinite` on `ℕ × ℕ`**: the uniform bound `‖T (d, e)‖ ≤ ‖x‖ ^ e` (any
`d`) together with `coeff_eq_zero_pow_of_lt` (`T (d, e) = 0` when `e < d`) confine
`{(d, e) : ‖T (d, e)‖ ≥ ε}` to `Finset.range D ×ˢ Finset.range D` for a suitable `D`. -/
theorem tendsto_T_cofinite_zero {g h : PowerSeries R}
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1)
    (hh0 : PowerSeries.constantCoeff h = 0)
    (hh : ∀ n, ‖algebraMap R K (PowerSeries.coeff n h)‖ ≤ 1) {x : K} (hx : ‖x‖ < 1) :
    Filter.Tendsto
      (fun p : ℕ × ℕ => algebraMap R K (PowerSeries.coeff p.1 g) * evalSummand (h ^ p.1) x p.2)
      Filter.cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε hx
  have hbound : ∀ p : ℕ × ℕ,
      ‖algebraMap R K (PowerSeries.coeff p.1 g) * evalSummand (h ^ p.1) x p.2‖ ≤ ‖x‖ ^ p.2 := by
    intro p
    rw [norm_mul]
    calc ‖algebraMap R K (PowerSeries.coeff p.1 g)‖ * ‖evalSummand (h ^ p.1) x p.2‖
        ≤ 1 * ‖x‖ ^ p.2 :=
          mul_le_mul (hg p.1) (norm_evalSummand_le (coeff_bound_pow hh p.1) x p.2)
            (norm_nonneg _) zero_le_one
      _ = ‖x‖ ^ p.2 := one_mul _
  have hsub :
      {p : ℕ × ℕ | ¬ dist
        (algebraMap R K (PowerSeries.coeff p.1 g) * evalSummand (h ^ p.1) x p.2) 0 < ε} ⊆
      (Finset.range D ×ˢ Finset.range D : Finset (ℕ × ℕ)) := by
    intro p hp
    simp only [Set.mem_setOf_eq, not_lt, dist_eq_norm, sub_zero] at hp
    have he : p.2 < D := by
      by_contra hge
      push Not at hge
      have := pow_le_pow_of_le_one (norm_nonneg x) hx.le hge
      linarith [hbound p, hD]
    have hd : p.1 ≤ p.2 := by
      by_contra hlt
      push Not at hlt
      have hz : algebraMap R K (PowerSeries.coeff p.1 g) * evalSummand (h ^ p.1) x p.2 = 0 := by
        unfold evalSummand
        rw [coeff_eq_zero_pow_of_lt hh0 hlt, map_zero, zero_mul, mul_zero]
      rw [hz] at hp; simp at hp; linarith
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    exact ⟨lt_of_le_of_lt hd he, he⟩
  exact ((Finset.range D ×ˢ Finset.range D).finite_toSet).subset hsub

set_option maxHeartbeats 1000000 in
/-- **Evaluation commutes with substitution**, univariate-into-univariate:
`eval (g.subst h) x = eval g (eval h x)`. See the module docstring for the double-series-interchange
route. -/
theorem eval_subst {g h : PowerSeries R}
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1)
    (hh0 : PowerSeries.constantCoeff h = 0)
    (hh : ∀ n, ‖algebraMap R K (PowerSeries.coeff n h)‖ ≤ 1) {x : K} (hx : ‖x‖ < 1)
    (hhx : ‖eval h x‖ < 1) :
    eval (PowerSeries.subst h g) x = eval g (eval h x) := by
  set T : ℕ × ℕ → K :=
    fun p => algebraMap R K (PowerSeries.coeff p.1 g) * evalSummand (h ^ p.1) x p.2 with hTdef
  have hTsum : Summable T :=
    IsUltrametricDist.summable_of_tendsto_zero (tendsto_T_cofinite_zero hg hh0 hh hx)
  set A := ∑' p, T p with hAdef
  have hTA : HasSum T A := hTsum.hasSum
  -- group by `d`
  have hbyD : HasSum (fun d : ℕ => evalSummand g (eval h x) d) A :=
    hTA.prod_fiberwise (fun d => hasSum_row_d hh hx d)
  have hAeq1 : A = eval g (eval h x) := hbyD.unique (hasSum_eval hg hhx)
  -- group by `e`
  have hbyE : HasSum (evalSummand (PowerSeries.subst h g) x) A := by
    have hTswap : HasSum (fun q : ℕ × ℕ => T (q.2, q.1)) A :=
      (Equiv.hasSum_iff (Equiv.prodComm ℕ ℕ)).mpr hTA
    exact hTswap.prod_fiberwise (fun e => hasSum_row_e hh0 x e)
  have hAeq2 : eval (PowerSeries.subst h g) x = A := by
    unfold eval; exact hbyE.tsum_eq
  rw [hAeq2, hAeq1]

end NonarchimedeanPowerSeriesEval

end
