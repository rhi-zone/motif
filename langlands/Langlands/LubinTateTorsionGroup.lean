import Langlands.LubinTateTorsionPoints
import Langlands.LubinTateFormalGroupEvalAssoc

/-!
# The Lubin-Tate torsion points form an abelian group under `F_π`-addition

`piTorsionAddCommGroup` : **`F_π[π^n]` is an `AddCommGroup`**, with addition `F_π(x, y)`
(`Langlands.LubinTate.FPiEval`), zero `0`, and negation `i_{F_π}(x)`
(`eval (PhiInv hπ hf) x`). Every field of the structure is one of the evaluated-level facts already
proved:

| structure field | fact |
| --- | --- |
| `add` well-defined | `mem_piTorsion_FPiEval` |
| `neg` well-defined | `mem_piTorsion_PhiInv` |
| `zero` well-defined | `zero_mem_piTorsion` |
| `add_assoc` | `FPiEval_assoc` (`Langlands.LubinTateFormalGroupEvalAssoc`) |
| `zero_add` / `add_zero` | `FPiEval_zero` / `FPiEval_zero'` |
| `neg_add_cancel` | `FPiEval_PhiInv_eq_zero'` |
| `add_comm` | `FPiEval_comm` |

This is **not** an `AddSubgroup K`: the group law is `F_π`-addition, not `K`'s addition (`F_π(x, y)
= x + y + (higher-order terms)`), so the subtype carries a genuinely different `Add`. It is stated
as a `def` rather than an `instance` because it depends on the non-instance hypotheses `hOK`
(`O`'s image lies in `K`'s closed unit ball), `hπ` and `hf`.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open NonarchimedeanPowerSeriesEval PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
variable {π : O} {f : O⟦X⟧}

/-- `F_π`-addition on `F_π[π^n]`, well-defined by `mem_piTorsion_FPiEval`. -/
@[reducible] def piTorsionAdd (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) :
    Add ↥(piTorsion (K := K) hπ hf n) :=
  ⟨fun x y ↦ ⟨FPiEval hπ hf x y, mem_piTorsion_FPiEval hOK hπ hf n x.2 y.2⟩⟩

/-- `0` as an element of `F_π[π^n]`. -/
@[reducible] def piTorsionZero (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) :
    Zero ↥(piTorsion (K := K) hπ hf n) :=
  ⟨⟨0, zero_mem_piTorsion hπ hf n⟩⟩

/-- `F_π`-negation `i_{F_π}` on `F_π[π^n]`, well-defined by `mem_piTorsion_PhiInv`. -/
@[reducible] def piTorsionNeg (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) :
    Neg ↥(piTorsion (K := K) hπ hf n) :=
  ⟨fun x ↦ ⟨eval (PhiInv hπ hf) x, mem_piTorsion_PhiInv hOK hπ hf n x.2⟩⟩

/-- **`F_π[π^n]`, the `π^n`-torsion points of the Lubin-Tate formal group law, is an abelian
group** under `F_π`-addition — the completed torsion-point group of the Lubin-Tate thread. -/
@[reducible] def piTorsionAddCommGroup (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) :
    AddCommGroup ↥(piTorsion (K := K) hπ hf n) :=
  letI := piTorsionAdd hOK hπ hf n
  letI := piTorsionZero (K := K) hπ hf n
  letI := piTorsionNeg hOK hπ hf n
  { add_assoc := fun x y z ↦ Subtype.ext (FPiEval_assoc hOK hπ hf x.2.1 y.2.1 z.2.1)
    zero_add := fun x ↦ Subtype.ext (FPiEval_zero hOK hπ hf x.2.1)
    add_zero := fun x ↦ Subtype.ext (FPiEval_zero' hOK hπ hf x.2.1)
    neg_add_cancel := fun x ↦ Subtype.ext (FPiEval_PhiInv_eq_zero' hOK hπ hf x.2.1)
    add_comm := fun x y ↦ Subtype.ext (FPiEval_comm hOK hπ hf x.2.1 y.2.1)
    nsmul := nsmulRec
    zsmul := zsmulRec }

/-- **The group law of `piTorsionAddCommGroup` really is `F_π`-addition** (true by definition;
recorded so downstream uses need not unfold the structure). -/
theorem coe_piTorsion_add (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ)
    (x y : ↥(piTorsion (K := K) hπ hf n)) :
    letI := piTorsionAddCommGroup hOK hπ hf n
    ((x + y : ↥(piTorsion (K := K) hπ hf n)) : K) = FPiEval hπ hf ↑x ↑y := rfl

/-- **The negation of `piTorsionAddCommGroup` really is `i_{F_π}`** (true by definition). -/
theorem coe_piTorsion_neg (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ)
    (x : ↥(piTorsion (K := K) hπ hf n)) :
    letI := piTorsionAddCommGroup hOK hπ hf n
    ((-x : ↥(piTorsion (K := K) hπ hf n)) : K) = eval (PhiInv hπ hf) ↑x := rfl

end LubinTate

end
