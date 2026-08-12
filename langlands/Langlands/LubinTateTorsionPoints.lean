import Langlands.NonarchimedeanPowerSeriesEvalSubst
import Langlands.LubinTateIterate

/-!
# `π^n`-torsion points of `F_π`, concretely defined

`ROADMAP.md` §19 scoped `F_π[π^n] := {x | f^{(n)}(x) = 0}` as blocked on evaluating a power series
at a concrete ring element. `Langlands.NonarchimedeanPowerSeriesEval.eval` (the from-scratch
`NormedField`/`IsUltrametricDist`/`CompleteSpace` construction) now supplies that evaluation, so
this file gives the definition, using `Langlands.LubinTateIterate.iter` (`f^{(n)}`, the `n`-fold
iterate) directly.

## Main results

* `piTorsion` : `F_π[π^n]`, the set of `x` in the maximal ideal of `K` with `eval (iter f n) x = 0`.
* `zero_mem_piTorsion` : `0 ∈ F_π[π^n]`, for every `n`.
* `mem_piTorsion_add` : **the filtration property `F_π[π^n] ⊆ F_π[π^{m+n}]`**, given `O`'s image
  lies in `K`'s closed unit ball (`hOK`, matching `Langlands.LubinTateFormalGroupEval`'s convention).
  This is the first non-trivial torsion-point fact to close, via
  `Langlands.NonarchimedeanPowerSeriesEvalSubst.eval_subst` applied to
  `Langlands.LubinTateIterate.iter_add`: both sides of `iter_add` are univariate-into-univariate
  composites (`iter f (m + n) = (iter f m).subst (iter f n)`), so the univariate case of
  eval-subst compatibility is exactly what is needed — unlike `F_π`-addition-closure and
  additive-inverse-closure below, which need the bivariate-outer case.

## What this does not do

**No group structure.** Closure of `piTorsion` under `F_π`-addition (`Langlands.LubinTate.FPiEval`)
and under additive inverses (`Langlands.LubinTate.PhiInv`) both need evaluation to commute with
formal substitution/composition, in the **bivariate-outer** shape (a multivariate-in, univariate-out
composite evaluated multivariately) — this is not yet built anywhere in this repo; see
`Langlands.LubinTateFormalGroupEval`'s module docstring for the precise gap and
`Langlands.NonarchimedeanPowerSeriesEvalSubst`'s module docstring for the route by which the
(closed) univariate case's proof structure is expected to transfer.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open NonarchimedeanPowerSeriesEval PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
variable {π : O} {f : O⟦X⟧}

/-- **The concrete `π^n`-torsion points of `F_π`**: elements of the maximal ideal of `K`
(`‖x‖ < 1`) killed by the concrete evaluation of the `n`-fold iterate `f^{(n)} = iter f n`. -/
def piTorsion (_hπ : Irreducible π) (_hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) :
    Set K :=
  {x : K | ‖x‖ < 1 ∧ eval (iter f n) x = 0}

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Evaluating any iterate at `0` gives `0`.** Every evaluation summand of `iter f m` at `0`
vanishes termwise: the constant term because `coeff 0 (iter f m) = 0` (`isLubinTatePoly_iter`), every
other term because `0 ^ k = 0` for `k ≥ 1`. This needs no composition/substitution argument. -/
theorem eval_iter_zero (hf : IsLubinTatePoly π (residueCard O) f) (m : ℕ) :
    eval (iter f m) (0 : K) = 0 := by
  have hc0 : PowerSeries.coeff 0 (iter f m) = 0 := (isLubinTatePoly_iter hf m).1
  have hterm : ∀ k, evalSummand (iter f m) (0 : K) k = 0 := by
    intro k
    unfold evalSummand
    match k with
    | 0 => rw [hc0, map_zero, zero_mul]
    | k + 1 => rw [pow_succ, mul_zero, mul_zero]
  unfold eval
  simp [hterm]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **`0` is always a `π^n`-torsion point.** -/
theorem zero_mem_piTorsion (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f)
    (n : ℕ) : (0 : K) ∈ piTorsion (K := K) hπ hf n :=
  ⟨by simp, eval_iter_zero hf n⟩

/-- **The filtration property**: `F_π[π^n] ⊆ F_π[π^{m+n}]`, given `O`'s image lies in `K`'s closed
unit ball (so every coefficient of every `O`-valued iterate is automatically bounded, matching
`Langlands.LubinTateFormalGroupEval`'s `hOK` convention). Proved by rewriting
`iter f (m + n) = (iter f m).subst (iter f n)` (`LubinTateIterate.iter_add`) via
`NonarchimedeanPowerSeriesEvalSubst.eval_subst`: `eval (iter f (m+n)) x = eval (iter f m) (eval
(iter f n) x) = eval (iter f m) 0 = 0`, using `x ∈ F_π[π^n]` for the middle step and
`eval_iter_zero` for the last. -/
theorem mem_piTorsion_add (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n m : ℕ) {x : K}
    (hx : x ∈ piTorsion (K := K) hπ hf n) : x ∈ piTorsion (K := K) hπ hf (m + n) := by
  obtain ⟨hxnorm, hxzero⟩ := hx
  refine ⟨hxnorm, ?_⟩
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
  have hg : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (iter f m))‖ ≤ 1 := fun k => hOK _
  have hh0 : PowerSeries.constantCoeff (iter f n) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact (isLubinTatePoly_iter hf n).1
  have hh : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (iter f n))‖ ≤ 1 := fun k => hOK _
  have hhx : ‖eval (iter f n) x‖ < 1 := by rw [hxzero]; simp
  rw [iter_add hf0 n m, eval_subst hg hh0 hh hxnorm hhx, hxzero, eval_iter_zero hf m]

end LubinTate

end
