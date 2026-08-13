import Langlands.LubinTateFunctionalEquationBivariate
import Langlands.NonarchimedeanMvPowerSeriesEvalFin2

/-!
# `F_π` evaluated at concrete elements of the maximal ideal

`ROADMAP.md` §19/§20 identified this as the missing crux piece of the Lubin-Tate torsion-point
thread: `Langlands.LubinTateFunctionalEquationBivariate.Phi` (`F_π`) is a *formal* bivariate power
series law; torsion points need it evaluated at *concrete* elements `a, b` of the maximal ideal of
a complete local ring. This file supplies that evaluation, via
`Langlands.NonarchimedeanMvPowerSeriesEvalFin2.evalMv` (the from-scratch
`NormedField`/`IsUltrametricDist`/`CompleteSpace` construction — see that file's docstring, and
`Langlands.NonarchimedeanPowerSeriesEval`'s, for why `PowerSeries.aeval`'s `IsLinearTopology`
instance stack is not usable here).

## Setup

`Φ := Phi hπ hf : MvPowerSeries (Fin 2) O` for the abstract Lubin-Tate base `O` (`IsDomain O`,
`IsDiscreteValuationRing O`, `Finite (ResidueField O)`, as in
`Langlands.LubinTateFunctionalEquationBivariate`). To evaluate, a target ring `K` is fixed with:

* `[NormedField K] [IsUltrametricDist K] [CompleteSpace K]` — the analytic structure
  `evalMv` needs, matching this repo's `NonarchimedeanExponential*.lean` files (in the concrete
  case, `K := v.adicCompletionIntegers F`'s ambient field `v.adicCompletion F`, per
  `Langlands.NonarchimedeanExponentialAdicCompletion`'s conventions).
* `[Algebra O K]` together with `hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1` — `O`'s image lies in the
  closed unit ball, i.e. `O` embeds as (a subring of) the ring of integers of `K`. This is the
  hypothesis that makes *every* coefficient of *every* `O`-valued power series automatically
  eligible for `evalMv`/`eval`, with no case-by-case bound needed.

## Main results

* `norm_algebraMap_coeff_Phi_le_one` : every coefficient of `Φ`, algebra-mapped into `K`, has norm
  at most `1` — immediate from `hOK`, since `Φ`'s coefficients are literally elements of `O`.
* `FPiEval` : **`F_π(a, b)`, the concrete-elements evaluation of `Φ` at `a, b : K`.**
* `hasSum_FPiEval` : **`F_π(a, b)` is well-defined and agrees with the formal object `Φ`
  coefficient-by-coefficient**, for `a, b` in the maximal ideal (`‖a‖ < 1`, `‖b‖ < 1`): the family
  `n ↦ algebraMap O K (coeff n Φ) * a ^ n 0 * b ^ n 1` sums *unconditionally* to `FPiEval a b` — the
  precise sense in which the concrete value is "the formal power series `Φ`, evaluated": every
  coefficient of `Φ` contributes its term, and the sum does not depend on the order/grouping in
  which those contributions are combined.

## What this does not do

**No compatibility between `evalMv`/`eval` and `PowerSeries.subst`/`MvPowerSeries.subst` is proved
here.** `Langlands.NonarchimedeanPowerSeriesEvalSubst.eval_subst` has since closed the
univariate-into-univariate case of this compatibility (`eval (g.subst h) x = eval g (eval h x)`, via
a double-series-interchange argument), but the torsion-point thread's next steps — closure of
`F_π[π^n]` under `F_π`-addition via `LubinTateIterate.subst_iter_Phi`, and additive inverses via
`FormalGroupInverse.subst_Phi_subst_PhiInv_eq_zero` — need a **bivariate-outer** form,
`eval (MvPowerSeries.subst A Φ) x = evalMv Φ (fun i ↦ eval (A i) x)` for a univariate family
`A : Fin 2 → PowerSeries R`, which is not yet built (see
`Langlands.NonarchimedeanPowerSeriesEvalSubst`'s module docstring for the precise route by which the
univariate proof's structure is expected to transfer, and `ROADMAP.md` for the dependency-ordered
remainder).
-/

@[expose] public section

noncomputable section

namespace LubinTate

open NonarchimedeanMvPowerSeriesEvalFin2 PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
variable {π : O} {f : O⟦X⟧}

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Every coefficient of `Φ := Phi hπ hf`, algebra-mapped into `K`, has norm at most `1` — since
`Φ`'s coefficients are literally elements of `O`, this is immediate from `hOK`. -/
theorem norm_algebraMap_coeff_Phi_le_one (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) (n : Fin 2 →₀ ℕ) :
    ‖algebraMap O K (MvPowerSeries.coeff n (Phi hπ hf))‖ ≤ 1 :=
  hOK _

/-- **`F_π(a, b)`, the Lubin-Tate formal group law evaluated at concrete elements `a, b : K`.**
Defined unconditionally (via `evalMv`, itself a `tsum`), meaningful exactly on the domain
`‖a‖ < 1`, `‖b‖ < 1` (the maximal ideal, when `K`'s unit ball is `O`'s image), per
`hasSum_FPiEval`. -/
def FPiEval (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) (a b : K) : K :=
  evalMv (Phi hπ hf) ![a, b]

/-- **`F_π(a, b)` is well-defined and agrees with `Φ` coefficient-by-coefficient**, for `a, b` in
the maximal ideal (given `O`'s image lies in `K`'s closed unit ball). -/
theorem hasSum_FPiEval (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (evalSummandMv (Phi hπ hf) ![a, b]) (FPiEval hπ hf a b) :=
  hasSum_evalMv (norm_algebraMap_coeff_Phi_le_one hOK hπ hf)
    (show ‖(![a, b] : Fin 2 → K) 0‖ < 1 by simpa using ha)
    (show ‖(![a, b] : Fin 2 → K) 1‖ < 1 by simpa using hb)

/-- **`F_π(a, b) = F_π(b, a)`, evaluated at concrete elements.** No eval-subst compatibility is
needed here (unlike `FPiEval`'s closure facts): both sides are literally the same `tsum`, up to
reindexing along `swapIdxEquiv` and using `coeff_swapIdx_Phi` (`F_π`'s coefficientwise
commutativity) to identify corresponding terms. Concretely, reindexing
`HasSum (evalSummandMv Φ ![b, a]) (FPiEval b a)` along `swapIdxEquiv` turns its summand at `n`
into `algebraMap (coeff (swapIdx n) Φ) * b ^ n 1 * a ^ n 0`, which `coeff_swapIdx_Phi` and
commutativity of multiplication identify with `evalSummandMv Φ ![a, b] n`; `HasSum.unique` against
`hasSum_FPiEval` at `a, b` then gives the result. -/
theorem FPiEval_comm (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    FPiEval hπ hf a b = FPiEval hπ hf b a := by
  have hab : HasSum (evalSummandMv (Phi hπ hf) ![a, b]) (FPiEval hπ hf a b) :=
    hasSum_FPiEval hOK hπ hf ha hb
  have hba : HasSum (evalSummandMv (Phi hπ hf) ![b, a]) (FPiEval hπ hf b a) :=
    hasSum_FPiEval hOK hπ hf hb ha
  have hreindex : HasSum
      (evalSummandMv (Phi hπ hf) ![b, a] ∘ swapIdxEquiv) (FPiEval hπ hf b a) :=
    (Equiv.hasSum_iff swapIdxEquiv).mpr hba
  have hfun : evalSummandMv (Phi hπ hf) ![b, a] ∘ swapIdxEquiv =
      evalSummandMv (Phi hπ hf) ![a, b] := by
    funext n
    show evalSummandMv (Phi hπ hf) ![b, a] (swapIdx n) = evalSummandMv (Phi hπ hf) ![a, b] n
    unfold evalSummandMv
    rw [Fin.prod_univ_two, Fin.prod_univ_two]
    show algebraMap O K (MvPowerSeries.coeff (swapIdx n) (Phi hπ hf)) *
        (b ^ (swapIdx n) 0 * a ^ (swapIdx n) 1) =
        algebraMap O K (MvPowerSeries.coeff n (Phi hπ hf)) * (a ^ n 0 * b ^ n 1)
    rw [coeff_swapIdx_Phi, swapIdx_apply_zero, swapIdx_apply_one]
    ring
  rw [hfun] at hreindex
  exact (hreindex.unique hab).symm

end LubinTate

end
