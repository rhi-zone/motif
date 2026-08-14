import Langlands.LubinTateTorsionPoints
import Langlands.LubinTateFormalGroupEvalAssoc

/-!
# `f` is an `F_π`-endomorphism, and roots of `f(X) = α` differ by `π`-torsion translation

`ROADMAP.md` §50's Target 1 (`K_1⟮β⟯ = K_2`) needs, per the classical argument: if `β, β'` both
solve `f(X) = α` for a fixed `α`, then `β` and `β'` differ by an `F_π`-translation by a `π`-torsion
point, i.e. `β' = F_π(β, t)` for some `t ∈ piTorsion hπ hf 1` (the kernel of `eval f` itself, since
`iter f 1 = f`). This file supplies that fact, plus the two ingredients it rests on:

* `eval_f_FPiEval` : **`f` is `F_π`-additive**, `eval f (F_π(a, b)) = F_π(eval f a, eval f b)` —
  the `n := 1` case of the already-closed `eval_iter_FPiEval` (`ROADMAP.md` §23's "Fact E"),
  rewritten along `LubinTateIterate.iter_one`.
* `eq_of_FPiEval_eq_zero_left` : **`F_π`-cancellation**, `F_π(a, b) = 0 → F_π(a, c) = 0 → b = c`,
  for `a, b, c` in the maximal ideal. Proved directly from the raw evaluated group-law facts
  (`FPiEval_zero'`, `FPiEval_PhiInv_eq_zero`, `FPiEval_assoc`) — the same computation that
  `LubinTateTorsionGroup.piTorsionAddCommGroup` packages into `AddCommGroup`, but here needed for
  arbitrary maximal-ideal elements, not just a fixed `piTorsion n` subtype, so it is proved at the
  raw-`FPiEval` level rather than by reuse of the packaged instance.
* `eval_f_PhiInv_eq_PhiInv_eval_f` : **`f` commutes with `F_π`-inversion**,
  `eval f (i_{F_π}(x)) = i_{F_π}(eval f x)` — obtained from `eval_f_FPiEval` and
  `eq_of_FPiEval_eq_zero_left` by the standard group-theoretic argument (a homomorphism sends
  inverses to inverses, via uniqueness of the additive inverse), not from any new formal-power-series
  identity.

## What this does not do

This is item (4) of `ROADMAP.md` §50's six-item Target-1 chain ("an `AddGroup`/torsion-translation
action on roots of `f(X) - α`"). It does **not** supply item (5) (transitivity/orbit-counting for
that action — the `π`-torsion analogue of `§44`'s counting argument) or item (6) (reassembly into
`K_1⟮β⟯ = ⊤`). Both remain open.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open NonarchimedeanPowerSeriesEval PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
variable {π : O} {f : O⟦X⟧}

/-- **`f` is `F_π`-additive**: `eval f (F_π(a, b)) = F_π(eval f a, eval f b)`, for `a, b` in the
maximal ideal. The `n := 1` case of `eval_iter_FPiEval` (`ROADMAP.md` §23's "Fact E"), rewritten
along `iter_one`. -/
theorem eval_f_FPiEval (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    eval f (FPiEval hπ hf a b) = FPiEval hπ hf (eval f a) (eval f b) := by
  have h := eval_iter_FPiEval hOK hπ hf 1 ha hb
  rwa [iter_one] at h

/-- **`F_π`-cancellation on the right**: if `F_π(a, b) = 0` and `F_π(a, c) = 0`, then `b = c`, for
`a, b, c` in the maximal ideal. The standard group-cancellation computation
(`b = F_π(0, b) = F_π(F_π(i_{F_π}(a), a), b) = F_π(i_{F_π}(a), F_π(a, b)) = F_π(i_{F_π}(a), 0) =
i_{F_π}(a)`, and symmetrically for `c`), done at the raw evaluated-`FPiEval` level so it applies to
arbitrary maximal-ideal elements, not just a fixed `piTorsion n` subtype. -/
theorem eq_of_FPiEval_eq_zero_left (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {a b c : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hc : ‖c‖ < 1) (hab : FPiEval hπ hf a b = 0) (hac : FPiEval hπ hf a c = 0) : b = c := by
  have hPhiInvBound : ∀ n, ‖algebraMap O K (PowerSeries.coeff n (PhiInv hπ hf))‖ ≤ 1 :=
    fun n ↦ hOK _
  have hInvA : ‖eval (PhiInv hπ hf) a‖ < 1 :=
    lt_of_le_of_lt (norm_eval_le hPhiInvBound (by simp [constantCoeff_PhiInv hπ hf]) ha) ha
  have key : ∀ x : K, ‖x‖ < 1 → FPiEval hπ hf a x = 0 → x = eval (PhiInv hπ hf) a := by
    intro x hx hax
    calc x = FPiEval hπ hf 0 x := (FPiEval_zero hOK hπ hf hx).symm
      _ = FPiEval hπ hf (FPiEval hπ hf (eval (PhiInv hπ hf) a) a) x :=
          by rw [FPiEval_PhiInv_eq_zero' hOK hπ hf ha]
      _ = FPiEval hπ hf (eval (PhiInv hπ hf) a) (FPiEval hπ hf a x) :=
          FPiEval_assoc hOK hπ hf hInvA ha hx
      _ = FPiEval hπ hf (eval (PhiInv hπ hf) a) 0 := by rw [hax]
      _ = eval (PhiInv hπ hf) a := FPiEval_zero' hOK hπ hf hInvA
  rw [key b hb hab, key c hc hac]

/-- **`f` commutes with `F_π`-inversion**: `eval f (i_{F_π}(x)) = i_{F_π}(eval f x)`, for `x` in
the maximal ideal. Obtained group-theoretically from `eval_f_FPiEval` and
`eq_of_FPiEval_eq_zero_left`: both `eval f (i_{F_π}(x))` and `i_{F_π}(eval f x)` are `F_π`-inverses
of `eval f x`, hence equal by cancellation — no new formal-power-series identity is needed. -/
theorem eval_f_PhiInv_eq_PhiInv_eval_f (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {x : K} (hx : ‖x‖ < 1) :
    eval f (eval (PhiInv hπ hf) x) = eval (PhiInv hπ hf) (eval f x) := by
  have hPhiInvBound : ∀ n, ‖algebraMap O K (PowerSeries.coeff n (PhiInv hπ hf))‖ ≤ 1 :=
    fun n ↦ hOK _
  have hInvX : ‖eval (PhiInv hπ hf) x‖ < 1 :=
    lt_of_le_of_lt (norm_eval_le hPhiInvBound (by simp [constantCoeff_PhiInv hπ hf]) hx) hx
  have hfBound : ∀ n, ‖algebraMap O K (PowerSeries.coeff n f)‖ ≤ 1 := fun n ↦ hOK _
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
  have hfx : ‖eval f x‖ < 1 := lt_of_le_of_lt (norm_eval_le hfBound hf0 hx) hx
  have hfInvX : ‖eval f (eval (PhiInv hπ hf) x)‖ < 1 :=
    lt_of_le_of_lt (norm_eval_le hfBound hf0 hInvX) hInvX
  have hPhiInvFx : ‖eval (PhiInv hπ hf) (eval f x)‖ < 1 :=
    lt_of_le_of_lt (norm_eval_le hPhiInvBound (by simp [constantCoeff_PhiInv hπ hf]) hfx) hfx
  refine eq_of_FPiEval_eq_zero_left hOK hπ hf hfx hfInvX hPhiInvFx ?_ ?_
  · rw [← eval_f_FPiEval hOK hπ hf hx hInvX, FPiEval_PhiInv_eq_zero hOK hπ hf hx]
    exact eval_zero_of_coeff_zero_eq_zero hf.1
  · exact FPiEval_PhiInv_eq_zero hOK hπ hf hfx

/-- **Roots of `f(X) = α` differ by `π`-torsion translation.** If `eval f β = eval f β' = α` (both
`β, β'` in the maximal ideal), then `F_π(β, i_{F_π}(β'))` — "`β -_F β'`" — is a nonzero-or-zero
`π`-torsion point, i.e. lies in `piTorsion hπ hf 1` (the kernel of `eval f` itself, since
`iter f 1 = f`): `f(β -_F β') = f(β) -_F f(β') = α -_F α = 0`. This is item (4) of `ROADMAP.md`
§50's Target-1 chain. -/
theorem sub_mem_piTorsion_one_of_eval_f_eq (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) {β β' : K} (hβ : ‖β‖ < 1)
    (hβ' : ‖β'‖ < 1) (heq : eval f β = eval f β') :
    FPiEval hπ hf β (eval (PhiInv hπ hf) β') ∈ piTorsion (K := K) hπ hf 1 := by
  have hPhiInvBound : ∀ n, ‖algebraMap O K (PowerSeries.coeff n (PhiInv hπ hf))‖ ≤ 1 :=
    fun n ↦ hOK _
  have hInvβ' : ‖eval (PhiInv hπ hf) β'‖ < 1 :=
    lt_of_le_of_lt (norm_eval_le hPhiInvBound (by simp [constantCoeff_PhiInv hπ hf]) hβ') hβ'
  have hnorm : ‖FPiEval hπ hf β (eval (PhiInv hπ hf) β')‖ < 1 := norm_FPiEval_lt hOK hπ hf hβ hInvβ'
  have hfBound : ∀ n, ‖algebraMap O K (PowerSeries.coeff n f)‖ ≤ 1 := fun n ↦ hOK _
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
  have hfβ' : ‖eval f β'‖ < 1 := lt_of_le_of_lt (norm_eval_le hfBound hf0 hβ') hβ'
  refine ⟨hnorm, ?_⟩
  rw [iter_one, eval_f_FPiEval hOK hπ hf hβ hInvβ', eval_f_PhiInv_eq_PhiInv_eval_f hOK hπ hf hβ',
    heq]
  exact FPiEval_PhiInv_eq_zero hOK hπ hf hfβ'

end LubinTate

end
