import Langlands.NonarchimedeanPowerSeriesEvalSubst
import Langlands.NonarchimedeanPowerSeriesEvalSubstMv
import Langlands.LubinTateIterate
import Langlands.LubinTateFormalGroupEval
import Langlands.FormalGroupInverse

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

/-- **`i_{F_π}(x)` is `F_π`'s additive inverse of `x`, at the level of concrete evaluation.**
`F_π(x, i_{F_π}(x)) = 0`, for any `x` in the maximal ideal of `K` (given `O`'s image lies in `K`'s
closed unit ball). Transports the formal identity `FormalGroupInverse.subst_Phi_PhiInv_eq_zero`
(`Φ(X, i_{F_π}(X)) = 0`) through `NonarchimedeanPowerSeriesEvalSubstMv.eval_subst_mv` (the
bivariate-outer eval-subst compatibility), using the univariate family `![X, PhiInv]` and
`eval_X`/`norm_eval_le` to see `eval X x = x` and `‖eval (PhiInv hπ hf) x‖ ≤ ‖x‖ < 1` (so `Φ` is
itself evaluable at the resulting point). This does **not** by itself show `PhiInv hπ hf` maps
`π^n`-torsion to `π^n`-torsion — that needs the *same-arity* eval-subst compatibility
`ROADMAP.md` re-scopes, not yet built. -/
theorem FPiEval_PhiInv_eq_zero (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {x : K} (hx : ‖x‖ < 1) :
    FPiEval hπ hf x (eval (PhiInv hπ hf) x) = 0 := by
  have hΦ : ∀ n, ‖algebraMap O K (MvPowerSeries.coeff n (Phi hπ hf))‖ ≤ 1 :=
    norm_algebraMap_coeff_Phi_le_one hOK hπ hf
  have hA0 : PowerSeries.constantCoeff
      ((![PowerSeries.X, PhiInv hπ hf] : Fin 2 → PowerSeries O) 0) = 0 := by simp
  have hA1 : PowerSeries.constantCoeff
      ((![PowerSeries.X, PhiInv hπ hf] : Fin 2 → PowerSeries O) 1) = 0 := by
    simp [constantCoeff_PhiInv hπ hf]
  have hPhiInvBound : ∀ n, ‖algebraMap O K (PowerSeries.coeff n (PhiInv hπ hf))‖ ≤ 1 :=
    fun n ↦ hOK _
  have hA : ∀ i n, ‖algebraMap O K (PowerSeries.coeff n
      ((![PowerSeries.X, PhiInv hπ hf] : Fin 2 → PowerSeries O) i))‖ ≤ 1 := by
    intro i n
    fin_cases i
    · exact coeff_bound_X n
    · exact hPhiInvBound n
  have hAx0 : ‖eval ((![PowerSeries.X, PhiInv hπ hf] : Fin 2 → PowerSeries O) 0) x‖ < 1 := by
    show ‖eval (PowerSeries.X : PowerSeries O) x‖ < 1
    rwa [eval_X]
  have hAx1 : ‖eval ((![PowerSeries.X, PhiInv hπ hf] : Fin 2 → PowerSeries O) 1) x‖ < 1 := by
    show ‖eval (PhiInv hπ hf) x‖ < 1
    exact lt_of_le_of_lt (norm_eval_le hPhiInvBound (by simp [constantCoeff_PhiInv hπ hf]) hx) hx
  have key := eval_subst_mv (A := ![PowerSeries.X, PhiInv hπ hf]) hΦ hA0 hA1 hA hx hAx0 hAx1
  rw [subst_Phi_PhiInv_eq_zero hπ hf] at key
  have hz : eval (0 : PowerSeries O) x = 0 := by
    unfold eval evalSummand
    simp
  rw [hz] at key
  have hfam : (fun i ↦ eval ((![PowerSeries.X, PhiInv hπ hf] : Fin 2 → PowerSeries O) i) x) =
      (![x, eval (PhiInv hπ hf) x] : Fin 2 → K) := by
    funext i
    fin_cases i
    · show eval (PowerSeries.X : PowerSeries O) x = x
      exact eval_X x
    · rfl
  rw [hfam] at key
  exact key.symm

end LubinTate

end
