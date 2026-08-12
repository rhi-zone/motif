import Langlands.NonarchimedeanPowerSeriesEval
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

## What this does not do

**No group structure.** Closure of `piTorsion` under `F_π`-addition (`Langlands.LubinTate.FPiEval`)
and under additive inverses (`Langlands.LubinTate.PhiInv`) both need evaluation to commute with
formal substitution/composition — `eval (g.subst h) x = eval g (eval h x)`-style statements — which
is not built anywhere in this repo (see `Langlands.LubinTateFormalGroupEval`'s module docstring for
the precise gap and the two prior places, `Langlands.NonarchimedeanExponentialHasSum` and
`Langlands.NonarchimedeanCauchyProduct`, that already flagged the same composition/rearrangement
argument as unattempted). Nor is the filtration property `F_π[π^n] ⊆ F_π[π^{n+1}]`
(`Langlands.LubinTateIterate.iter_add`, transported through evaluation) proved, for the same
reason. Only the *definition* and its single easy member (`0`, which needs no composition — every
evaluation summand of an iterate at `0` vanishes termwise) are landed here.
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
/-- **`0` is always a `π^n`-torsion point.** Every evaluation summand of `iter f n` at `0` vanishes
termwise: the constant term because `coeff 0 (iter f n) = 0` (`isLubinTatePoly_iter`), every other
term because `0 ^ k = 0` for `k ≥ 1`. This needs no composition/substitution argument, unlike every
other torsion-point fact. -/
theorem zero_mem_piTorsion (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f)
    (n : ℕ) : (0 : K) ∈ piTorsion (K := K) hπ hf n := by
  refine ⟨by simp, ?_⟩
  have hc0 : PowerSeries.coeff 0 (iter f n) = 0 := (isLubinTatePoly_iter hf n).1
  have hterm : ∀ k, evalSummand (iter f n) (0 : K) k = 0 := by
    intro k
    unfold evalSummand
    match k with
    | 0 => rw [hc0, map_zero, zero_mul]
    | k + 1 => rw [pow_succ, mul_zero, mul_zero]
  unfold eval
  simp [hterm]

end LubinTate

end
