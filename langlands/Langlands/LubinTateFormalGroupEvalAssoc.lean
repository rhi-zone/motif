import Langlands.LubinTateFormalGroupEval
import Langlands.NonarchimedeanMvPowerSeriesEvalSubstGeneral

/-!
# `F_π` is associative at concrete points: `F_π(F_π(a, b), c) = F_π(a, F_π(b, c))`

The last missing `AddGroup` axiom for the concrete `π^n`-torsion points: identity, commutativity
and both-sided inverse were already closed at the evaluated level, but associativity needs
eval-subst compatibility at a nesting shape not covered by the single-substitution or
diagonal-substitution compatibility lemmas used for those.

## Route

`Langlands.LubinTateFunctionalEquationBivariate.assoc_Phi` is the *formal* identity
`PhiAssocLeft = PhiAssocRight` in `MvPowerSeries (Fin 3) O`, where
`PhiAssocLeft = Φ.subst ![Φ.subst ![X 0, X 1], X 2]` and
`PhiAssocRight = Φ.subst ![X 0, Φ.subst ![X 1, X 2]]`. Evaluating both sides at `![a, b, c]` and
identifying each with the corresponding nested `FPiEval` turns it into the concrete statement.

Each identification is **two applications of the single general compatibility**
`Langlands.NonarchimedeanMvPowerSeriesEval.eval_subst_G`
(`evalMv (Φ.subst A) z = evalMv Φ (fun i ↦ evalMv (A i) z)`, arbitrary family `A`, arbitrary finite
index types) — once for the outer substitution (family `![Φ.subst ![X 0, X 1], X 2]`, whose two
components have genuinely different shapes) and once for the inner one (family `![X 0, X 1]`,
handled by `evalMv_subst_pair` below). No separate diagonal-substitution lemma is needed here: the
general lemma's family is unconstrained, so it covers the nested substitution shape directly.

Two small bridges make this go through with no reproved analysis:

* `evalMv_eq_FPiEval` : the general-`σ` `evalMv` (`Langlands.NonarchimedeanMvPowerSeriesEval`) at
  `σ := Fin 2` is *definitionally* the `Fin 2`-specialized `evalMv`
  (`Langlands.NonarchimedeanMvPowerSeriesEvalFin2`) that `FPiEval` is defined by — both are the same
  `tsum` — so no migration of the existing `Fin 2` development is needed to use the general lemma.
* every series in sight has coefficients in `O`, so the coefficient bound `eval_subst_G` asks for is
  just `hOK` applied pointwise; only the zero-constant-term hypotheses need any argument, and for
  the composite component that is `MvPowerSeries.constantCoeff_subst_eq_zero`.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open IsLocalRing PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
variable {π : O} {f : O⟦X⟧}

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The general-`σ` `evalMv` computes `FPiEval`.** `FPiEval` is defined through the
`Fin 2`-specialized `NonarchimedeanMvPowerSeriesEvalFin2.evalMv`; that and the general-`σ`
`NonarchimedeanMvPowerSeriesEval.evalMv` at `σ := Fin 2` are the same `tsum` by definition, so the
general eval-subst machinery applies to `FPiEval` with no transport. -/
theorem evalMv_eq_FPiEval (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f)
    (a b : K) :
    NonarchimedeanMvPowerSeriesEval.evalMv (Phi hπ hf) ![a, b] = FPiEval hπ hf a b := rfl

/-- **`Φ` embedded along two of the three axes, evaluated**: `F_π(X i, X j)` evaluated at
`z : Fin 3 → K` is `F_π(z i, z j)`. One application of `eval_subst_G` with the family
`![X i, X j]`, whose components evaluate to coordinates by `evalMv_X`. -/
theorem evalMv_subst_pair (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (i j : Fin 3) {z : Fin 3 → K}
    (hz : ∀ k, ‖z k‖ < 1) :
    NonarchimedeanMvPowerSeriesEval.evalMv ((Phi hπ hf).subst
        (![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries (Fin 3) O)) z =
      FPiEval hπ hf (z i) (z j) := by
  have hΦ : ∀ d, ‖algebraMap O K (MvPowerSeries.coeff d (Phi hπ hf))‖ ≤ 1 := fun d ↦ hOK _
  have hA0 : ∀ k : Fin 2, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries (Fin 3) O) k) = 0 :=
    fun k ↦ by fin_cases k <;> simp
  have hA : ∀ (k : Fin 2) (n : Fin 3 →₀ ℕ), ‖algebraMap O K (MvPowerSeries.coeff n
      ((![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries (Fin 3) O) k))‖ ≤ 1 :=
    fun _ _ ↦ hOK _
  rw [NonarchimedeanMvPowerSeriesEval.eval_subst_G hΦ hA0 hA hz]
  have hfam : (fun k : Fin 2 ↦ NonarchimedeanMvPowerSeriesEval.evalMv
      ((![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries (Fin 3) O) k) z) =
      (![z i, z j] : Fin 2 → K) := by
    funext k
    fin_cases k
    · exact NonarchimedeanMvPowerSeriesEval.evalMv_X i z
    · exact NonarchimedeanMvPowerSeriesEval.evalMv_X j z
  rw [hfam, evalMv_eq_FPiEval]

/-- **`F_π(F_π(X, Y), Z)` evaluated at `![a, b, c]` is `F_π(F_π(a, b), c)`.** Two applications of
`eval_subst_G`: the outer one at the mixed family `![Φ.subst ![X 0, X 1], X 2]`, the inner one
inside `evalMv_subst_pair`. -/
theorem evalMv_PhiAssocLeft (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {a b c : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hc : ‖c‖ < 1) :
    NonarchimedeanMvPowerSeriesEval.evalMv (PhiAssocLeft hπ hf) ![a, b, c] =
      FPiEval hπ hf (FPiEval hπ hf a b) c := by
  have hz : ∀ k : Fin 3, ‖(![a, b, c] : Fin 3 → K) k‖ < 1 := by
    intro k; fin_cases k <;> simpa
  have hΦ : ∀ d, ‖algebraMap O K (MvPowerSeries.coeff d (Phi hπ hf))‖ ≤ 1 := fun d ↦ hOK _
  have hasSubst_e01 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X (1 : Fin 3)] :
        Fin 2 → MvPowerSeries (Fin 3) O) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun k ↦ by fin_cases k <;> simp)
  have hA0 : ∀ k : Fin 2, MvPowerSeries.constantCoeff
      ((![(Phi hπ hf).subst
            (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) O),
          MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) O) k) = 0 := by
    intro k
    fin_cases k
    · exact MvPowerSeries.constantCoeff_subst_eq_zero hasSubst_e01
        (fun k ↦ by fin_cases k <;> simp) (constantCoeff_Phi hπ hf)
    · simp
  have hA : ∀ (k : Fin 2) (n : Fin 3 →₀ ℕ), ‖algebraMap O K (MvPowerSeries.coeff n
      ((![(Phi hπ hf).subst
            (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) O),
          MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) O) k))‖ ≤ 1 :=
    fun _ _ ↦ hOK _
  show NonarchimedeanMvPowerSeriesEval.evalMv ((Phi hπ hf).subst _) _ = _
  rw [NonarchimedeanMvPowerSeriesEval.eval_subst_G hΦ hA0 hA hz]
  have hfam : (fun k : Fin 2 ↦ NonarchimedeanMvPowerSeriesEval.evalMv
      ((![(Phi hπ hf).subst
            (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) O),
          MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) O) k) ![a, b, c]) =
      (![FPiEval hπ hf a b, c] : Fin 2 → K) := by
    funext k
    fin_cases k
    · show NonarchimedeanMvPowerSeriesEval.evalMv ((Phi hπ hf).subst
          (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
            Fin 2 → MvPowerSeries (Fin 3) O)) ![a, b, c] = FPiEval hπ hf a b
      rw [evalMv_subst_pair hOK hπ hf 0 1 hz]
      rfl
    · show NonarchimedeanMvPowerSeriesEval.evalMv
          (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) O) ![a, b, c] = c
      rw [NonarchimedeanMvPowerSeriesEval.evalMv_X]
      rfl
  rw [hfam, evalMv_eq_FPiEval]

/-- **`F_π(X, F_π(Y, Z))` evaluated at `![a, b, c]` is `F_π(a, F_π(b, c))`.** The mirror image of
`evalMv_PhiAssocLeft`. -/
theorem evalMv_PhiAssocRight (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {a b c : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hc : ‖c‖ < 1) :
    NonarchimedeanMvPowerSeriesEval.evalMv (PhiAssocRight hπ hf) ![a, b, c] =
      FPiEval hπ hf a (FPiEval hπ hf b c) := by
  have hz : ∀ k : Fin 3, ‖(![a, b, c] : Fin 3 → K) k‖ < 1 := by
    intro k; fin_cases k <;> simpa
  have hΦ : ∀ d, ‖algebraMap O K (MvPowerSeries.coeff d (Phi hπ hf))‖ ≤ 1 := fun d ↦ hOK _
  have hasSubst_e12 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X (2 : Fin 3)] :
        Fin 2 → MvPowerSeries (Fin 3) O) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun k ↦ by fin_cases k <;> simp)
  have hA0 : ∀ k : Fin 2, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0,
          (Phi hπ hf).subst
            (![MvPowerSeries.X 1, MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) O)] :
        Fin 2 → MvPowerSeries (Fin 3) O) k) = 0 := by
    intro k
    fin_cases k
    · simp
    · exact MvPowerSeries.constantCoeff_subst_eq_zero hasSubst_e12
        (fun k ↦ by fin_cases k <;> simp) (constantCoeff_Phi hπ hf)
  have hA : ∀ (k : Fin 2) (n : Fin 3 →₀ ℕ), ‖algebraMap O K (MvPowerSeries.coeff n
      ((![MvPowerSeries.X 0,
          (Phi hπ hf).subst
            (![MvPowerSeries.X 1, MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) O)] :
        Fin 2 → MvPowerSeries (Fin 3) O) k))‖ ≤ 1 :=
    fun _ _ ↦ hOK _
  show NonarchimedeanMvPowerSeriesEval.evalMv ((Phi hπ hf).subst _) _ = _
  rw [NonarchimedeanMvPowerSeriesEval.eval_subst_G hΦ hA0 hA hz]
  have hfam : (fun k : Fin 2 ↦ NonarchimedeanMvPowerSeriesEval.evalMv
      ((![MvPowerSeries.X 0,
          (Phi hπ hf).subst
            (![MvPowerSeries.X 1, MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) O)] :
        Fin 2 → MvPowerSeries (Fin 3) O) k) ![a, b, c]) =
      (![a, FPiEval hπ hf b c] : Fin 2 → K) := by
    funext k
    fin_cases k
    · show NonarchimedeanMvPowerSeriesEval.evalMv
          (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) O) ![a, b, c] = a
      rw [NonarchimedeanMvPowerSeriesEval.evalMv_X]
      rfl
    · show NonarchimedeanMvPowerSeriesEval.evalMv ((Phi hπ hf).subst
          (![MvPowerSeries.X 1, MvPowerSeries.X 2] :
            Fin 2 → MvPowerSeries (Fin 3) O)) ![a, b, c] = FPiEval hπ hf b c
      rw [evalMv_subst_pair hOK hπ hf 1 2 hz]
      rfl
  rw [hfam, evalMv_eq_FPiEval]

/-- **`F_π` is associative at concrete points: `F_π(F_π(a, b), c) = F_π(a, F_π(b, c))`.** The
evaluated form of `assoc_Phi` (the formal associativity of `F_π`), transported through
`evalMv_PhiAssocLeft`/`evalMv_PhiAssocRight`. This is the last `AddGroup` axiom for `piTorsion`:
identity (`FPiEval_zero`/`FPiEval_zero'`), commutativity (`FPiEval_comm`) and both-sided inverse
(`FPiEval_PhiInv_eq_zero`/`FPiEval_PhiInv_eq_zero'`) were already available. -/
theorem FPiEval_assoc (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {a b c : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hc : ‖c‖ < 1) :
    FPiEval hπ hf (FPiEval hπ hf a b) c = FPiEval hπ hf a (FPiEval hπ hf b c) := by
  rw [← evalMv_PhiAssocLeft hOK hπ hf ha hb hc, ← evalMv_PhiAssocRight hOK hπ hf ha hb hc,
    assoc_Phi hπ hf]

end LubinTate

end
