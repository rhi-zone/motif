import Langlands.NonarchimedeanPowerSeriesEvalSubst
import Langlands.NonarchimedeanPowerSeriesEvalSubstMv
import Langlands.NonarchimedeanPowerSeriesEvalSubstMvIn
import Langlands.NonarchimedeanMvPowerSeriesEvalSubstDiagonal
import Langlands.LubinTateIterate
import Langlands.LubinTateFormalGroupEval
import Langlands.FormalGroupInverse
import Langlands.LubinTateWeierstrassPreparation

/-!
# `π^n`-torsion points of `F_π`, concretely defined

`F_π[π^n] := {x | f^{(n)}(x) = 0}` needs a concrete way to evaluate a power series at a ring
element. `Langlands.NonarchimedeanPowerSeriesEval.eval` (the from-scratch
`NormedField`/`IsUltrametricDist`/`CompleteSpace` construction) supplies that evaluation, so
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

open scoped Polynomial

namespace LubinTate

open NonarchimedeanPowerSeriesEval NonarchimedeanMvPowerSeriesEvalFin2 PowerSeries IsLocalRing

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
`π^n`-torsion to `π^n`-torsion — that needs the *same-arity* eval-subst compatibility, not yet
built. -/
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

/-- **`i_{F_π}(x)` is also a *left* additive inverse: `F_π(i_{F_π}(x), x) = 0`.** The other-sided
inverse law, obtained "for free" from `FPiEval_PhiInv_eq_zero` (the right-sided law) via
`FPiEval_comm` (`F_π`'s commutativity, evaluated) — no separate formal identity needed, unlike the
general case where only a one-sided inverse law is assumed. -/
theorem FPiEval_PhiInv_eq_zero' (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {x : K} (hx : ‖x‖ < 1) :
    FPiEval hπ hf (eval (PhiInv hπ hf) x) x = 0 := by
  have hPhiInvBound : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (PhiInv hπ hf))‖ ≤ 1 :=
    fun k ↦ hOK _
  have hInvNorm : ‖eval (PhiInv hπ hf) x‖ < 1 :=
    lt_of_le_of_lt (norm_eval_le hPhiInvBound (by simp [constantCoeff_PhiInv hπ hf]) hx) hx
  rw [FPiEval_comm hOK hπ hf hInvNorm hx]
  exact FPiEval_PhiInv_eq_zero hOK hπ hf hx

/-- **"Fact E"**: the `[π^n]`-endomorphism `eval (iter f n)` commutes with
concrete `F_π`-addition. Chains `LubinTateIterate.subst_iter_Phi`'s formal identity
`(iter f n).subst Φ = Φ.subst (fun i ↦ (iter f n).subst (X i))` through `evalMv` at `y = ![a, b]`:
the LHS matches `NonarchimedeanPowerSeriesEval.eval_subst_A`'s shape ("Lemma A") exactly, giving
`eval (iter f n) (FPiEval a b)`; the RHS matches `NonarchimedeanMvPowerSeriesEvalFin2.eval_subst_S`'s
shape ("Lemma S") exactly (the substitutand family is precisely `diagEmbed (iter f n)`, by
definition), giving `FPiEval (eval (iter f n) a) (eval (iter f n) b)`. -/
theorem eval_iter_FPiEval (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    eval (iter f n) (FPiEval hπ hf a b) =
      FPiEval hπ hf (eval (iter f n) a) (eval (iter f n) b) := by
  have hΦ : ∀ m, ‖algebraMap O K (MvPowerSeries.coeff m (Phi hπ hf))‖ ≤ 1 :=
    norm_algebraMap_coeff_Phi_le_one hOK hπ hf
  have hΦ0 : MvPowerSeries.constantCoeff (Phi hπ hf) = 0 := constantCoeff_Phi hπ hf
  have hfn0 : PowerSeries.constantCoeff (iter f n) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact (isLubinTatePoly_iter hf n).1
  have hfn : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (iter f n))‖ ≤ 1 := fun k ↦ hOK _
  have hab0 : ‖(![a, b] : Fin 2 → K) 0‖ < 1 := by simpa using ha
  have hab1 : ‖(![a, b] : Fin 2 → K) 1‖ < 1 := by simpa using hb
  have hFPiEval_lt : ‖FPiEval hπ hf a b‖ < 1 := by
    calc ‖FPiEval hπ hf a b‖ = ‖evalMv (Phi hπ hf) ![a, b]‖ := rfl
      _ ≤ max ‖(![a, b] : Fin 2 → K) 0‖ ‖(![a, b] : Fin 2 → K) 1‖ :=
          norm_evalMv_le hΦ hΦ0 hab0 hab1
      _ < 1 := by rw [max_lt_iff]; exact ⟨hab0, hab1⟩
  have keyDiag : PowerSeries.subst (Phi hπ hf) (iter f n) =
      MvPowerSeries.subst (diagEmbed (iter f n)) (Phi hπ hf) := subst_iter_Phi hπ hf n
  have hLHS : evalMv (PowerSeries.subst (Phi hπ hf) (iter f n)) ![a, b] =
      eval (iter f n) (FPiEval hπ hf a b) :=
    (eval_subst_A hfn hΦ0 hΦ hab0 hab1 hFPiEval_lt).symm
  have hRHS : evalMv (MvPowerSeries.subst (diagEmbed (iter f n)) (Phi hπ hf)) ![a, b] =
      FPiEval hπ hf (eval (iter f n) a) (eval (iter f n) b) := by
    rw [eval_subst_S hfn0 hfn hΦ hab0 hab1]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [← hLHS, keyDiag]
  exact hRHS

omit [CompleteSpace K] in
/-- **`F_π(a, b)` lies in the maximal ideal**, given both `a, b` do. -/
theorem norm_FPiEval_lt (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖FPiEval hπ hf a b‖ < 1 := by
  have hΦ := norm_algebraMap_coeff_Phi_le_one hOK hπ hf
  have hΦ0 := constantCoeff_Phi hπ hf
  have hab0 : ‖(![a, b] : Fin 2 → K) 0‖ < 1 := by simpa using ha
  have hab1 : ‖(![a, b] : Fin 2 → K) 1‖ < 1 := by simpa using hb
  calc ‖FPiEval hπ hf a b‖ = ‖evalMv (Phi hπ hf) ![a, b]‖ := rfl
    _ ≤ max ‖(![a, b] : Fin 2 → K) 0‖ ‖(![a, b] : Fin 2 → K) 1‖ := norm_evalMv_le hΦ hΦ0 hab0 hab1
    _ < 1 := by rw [max_lt_iff]; exact ⟨hab0, hab1⟩

/-- **`F_π(0, x) = x`**: the evaluated form of Mathlib's `FormalGroup.zeroX_eq_X` (the identity
law `F(0, Y) = Y`, itself proved generically for any commutative `FormalGroup` from the
associativity/identity axioms). Transports it through `eval_subst_mv` at the univariate family
`![0, X]`, exactly as `FPiEval_PhiInv_eq_zero` transports `subst_Phi_PhiInv_eq_zero`. -/
theorem FPiEval_zero (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {x : K} (hx : ‖x‖ < 1) :
    FPiEval hπ hf 0 x = x := by
  have hΦ : ∀ n, ‖algebraMap O K (MvPowerSeries.coeff n (Phi hπ hf))‖ ≤ 1 :=
    norm_algebraMap_coeff_Phi_le_one hOK hπ hf
  have hA0 : PowerSeries.constantCoeff
      ((![0, PowerSeries.X] : Fin 2 → PowerSeries O) 0) = 0 := by simp
  have hA1 : PowerSeries.constantCoeff
      ((![0, PowerSeries.X] : Fin 2 → PowerSeries O) 1) = 0 := by simp
  have hzero : eval (0 : PowerSeries O) x = 0 := by unfold eval evalSummand; simp
  have hA : ∀ i n, ‖algebraMap O K (PowerSeries.coeff n
      ((![0, PowerSeries.X] : Fin 2 → PowerSeries O) i))‖ ≤ 1 := by
    intro i n
    fin_cases i
    · simp
    · exact coeff_bound_X n
  have hAx0 : ‖eval ((![0, PowerSeries.X] : Fin 2 → PowerSeries O) 0) x‖ < 1 := by
    show ‖eval (0 : PowerSeries O) x‖ < 1
    rw [hzero]; simp
  have hAx1 : ‖eval ((![0, PowerSeries.X] : Fin 2 → PowerSeries O) 1) x‖ < 1 := by
    show ‖eval (PowerSeries.X : PowerSeries O) x‖ < 1
    rwa [eval_X]
  have key := eval_subst_mv (A := ![0, PowerSeries.X]) hΦ hA0 hA1 hA hx hAx0 hAx1
  have hZ : MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → PowerSeries O) (Phi hπ hf) =
      PowerSeries.X :=
    (LubinTateFormalGroup hπ hf).zeroX_eq_X
  rw [hZ, eval_X] at key
  have hfam : (fun i ↦ eval ((![0, PowerSeries.X] : Fin 2 → PowerSeries O) i) x) =
      (![0, x] : Fin 2 → K) := by
    funext i
    fin_cases i
    · show eval (0 : PowerSeries O) x = 0
      exact hzero
    · show eval (PowerSeries.X : PowerSeries O) x = x
      exact eval_X x
  rw [hfam] at key
  exact key.symm

/-- **`F_π(x, 0) = x`**: the `X`-slot analogue of `FPiEval_zero`, via Mathlib's
`FormalGroup.Xzero_eq_X`. -/
theorem FPiEval_zero' (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {x : K} (hx : ‖x‖ < 1) :
    FPiEval hπ hf x 0 = x := by
  have hΦ : ∀ n, ‖algebraMap O K (MvPowerSeries.coeff n (Phi hπ hf))‖ ≤ 1 :=
    norm_algebraMap_coeff_Phi_le_one hOK hπ hf
  have hA0 : PowerSeries.constantCoeff
      ((![PowerSeries.X, 0] : Fin 2 → PowerSeries O) 0) = 0 := by simp
  have hA1 : PowerSeries.constantCoeff
      ((![PowerSeries.X, 0] : Fin 2 → PowerSeries O) 1) = 0 := by simp
  have hzero : eval (0 : PowerSeries O) x = 0 := by unfold eval evalSummand; simp
  have hA : ∀ i n, ‖algebraMap O K (PowerSeries.coeff n
      ((![PowerSeries.X, 0] : Fin 2 → PowerSeries O) i))‖ ≤ 1 := by
    intro i n
    fin_cases i
    · exact coeff_bound_X n
    · simp
  have hAx0 : ‖eval ((![PowerSeries.X, 0] : Fin 2 → PowerSeries O) 0) x‖ < 1 := by
    show ‖eval (PowerSeries.X : PowerSeries O) x‖ < 1
    rwa [eval_X]
  have hAx1 : ‖eval ((![PowerSeries.X, 0] : Fin 2 → PowerSeries O) 1) x‖ < 1 := by
    show ‖eval (0 : PowerSeries O) x‖ < 1
    rw [hzero]; simp
  have key := eval_subst_mv (A := ![PowerSeries.X, 0]) hΦ hA0 hA1 hA hx hAx0 hAx1
  have hZ : MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → PowerSeries O) (Phi hπ hf) =
      PowerSeries.X :=
    (LubinTateFormalGroup hπ hf).Xzero_eq_X
  rw [hZ, eval_X] at key
  have hfam : (fun i ↦ eval ((![PowerSeries.X, 0] : Fin 2 → PowerSeries O) i) x) =
      (![x, 0] : Fin 2 → K) := by
    funext i
    fin_cases i
    · show eval (PowerSeries.X : PowerSeries O) x = x
      exact eval_X x
    · show eval (0 : PowerSeries O) x = 0
      exact hzero
  rw [hfam] at key
  exact key.symm

/-- **`piTorsion` is closed under `F_π`-addition.** Via `eval_iter_FPiEval` (Fact E): torsion `x`,
`y` (`eval (iter f n) x = eval (iter f n) y = 0`) give `eval (iter f n) (FPiEval x y) =
FPiEval 0 0 = 0` (`evalMv_eq_zero_of_zero`, `Φ`'s zero constant term). -/
theorem mem_piTorsion_FPiEval (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) {x y : K}
    (hx : x ∈ piTorsion (K := K) hπ hf n) (hy : y ∈ piTorsion (K := K) hπ hf n) :
    FPiEval hπ hf x y ∈ piTorsion (K := K) hπ hf n := by
  obtain ⟨hxnorm, hxzero⟩ := hx
  obtain ⟨hynorm, hyzero⟩ := hy
  refine ⟨norm_FPiEval_lt hOK hπ hf hxnorm hynorm, ?_⟩
  rw [eval_iter_FPiEval hOK hπ hf n hxnorm hynorm, hxzero, hyzero]
  exact evalMv_eq_zero_of_zero (constantCoeff_Phi hπ hf) rfl rfl

/-- **`piTorsion` is closed under `F_π`-additive inverse.** `FPiEval_PhiInv_eq_zero` gives
`F_π(x, i_{F_π}(x)) = 0`; applying `eval (iter f n)` to both sides and using Fact E
(`eval_iter_FPiEval`) plus `x`'s torsion and `FPiEval_zero` (`Φ(0, Z) = Z` evaluated) isolates
`eval (iter f n) (eval (PhiInv hπ hf) x) = 0`. -/
theorem mem_piTorsion_PhiInv (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) {x : K}
    (hx : x ∈ piTorsion (K := K) hπ hf n) :
    eval (PhiInv hπ hf) x ∈ piTorsion (K := K) hπ hf n := by
  obtain ⟨hxnorm, hxzero⟩ := hx
  have hPhiInvBound : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (PhiInv hπ hf))‖ ≤ 1 :=
    fun k ↦ hOK _
  have hInvNorm : ‖eval (PhiInv hπ hf) x‖ < 1 :=
    lt_of_le_of_lt (norm_eval_le hPhiInvBound (by simp [constantCoeff_PhiInv hπ hf]) hxnorm) hxnorm
  refine ⟨hInvNorm, ?_⟩
  have hzero : FPiEval hπ hf x (eval (PhiInv hπ hf) x) = 0 :=
    FPiEval_PhiInv_eq_zero hOK hπ hf hxnorm
  have hE := eval_iter_FPiEval hOK hπ hf n hxnorm hInvNorm
  rw [hzero, eval_iter_zero hf n, hxzero] at hE
  have hfn0 : PowerSeries.constantCoeff (iter f n) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact (isLubinTatePoly_iter hf n).1
  have hfn : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (iter f n))‖ ≤ 1 := fun k ↦ hOK _
  have hzNorm : ‖eval (iter f n) (eval (PhiInv hπ hf) x)‖ < 1 :=
    lt_of_le_of_lt (norm_eval_le hfn hfn0 hInvNorm) hInvNorm
  rw [FPiEval_zero hOK hπ hf hzNorm] at hE
  exact hE.symm

/-! ## `piTorsion hπ hf 1` is exactly the root set of a Weierstrass-preparation factor -/

omit [Finite (ResidueField O)] in
/-- **`piTorsion hπ hf 1` is the zero set, on the maximal ideal, of the degree-`q` distinguished
polynomial `P` from `f`'s Weierstrass factorization.** `iter f 1 = f`
(`LubinTateIterate.iter_one`) identifies `piTorsion hπ hf 1` with `f`'s own zero set on the maximal
ideal; `eval_eq_zero_iff_aeval_eq_zero` (built from the factorization `f = (P : O⟦X⟧) * u` and the
unit factor's non-vanishing) turns that into `P`'s zero set under `Polynomial.aeval`. Existential
in `P` (rather than naming a canonical one) since the Weierstrass factorization itself is only
known to exist, not to be canonically chosen. -/
theorem exists_piTorsion_one_eq_aeval_roots [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) :
    ∃ P : O[X], P.IsDistinguishedAt (IsLocalRing.maximalIdeal O) ∧ P.natDegree = residueCard O ∧
      piTorsion (K := K) hπ hf 1 = {x : K | ‖x‖ < 1 ∧ Polynomial.aeval x P = 0} := by
  obtain ⟨P, u, hPdist, hu, heq, hPdeg⟩ := exists_isWeierstrassFactorization_of_isLubinTatePoly hf
  refine ⟨P, hPdist, hPdeg, ?_⟩
  ext x
  simp only [piTorsion, Set.mem_setOf_eq, iter_one]
  exact and_congr_right fun hx ↦ eval_eq_zero_iff_aeval_eq_zero hOK hu heq hx

end LubinTate

end
