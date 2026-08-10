import Langlands.PrincipalUnitsFiltration
import Mathlib.GroupTheory.Index

/-!
# The index of a principal-units filtration level, `[Aˣ : U_A^{(j)}]`

`Langlands.PrincipalUnitsFiltration` builds the filtration `U_A^{(i)} = 1 + 𝔪_A^i` of `Aˣ` for a
valuation subring `A` of a field, together with its graded pieces:

* `U_A^{(0)} / U_A^{(1)} ≅ κ_Aˣ` (Mathlib's `unitsModPrincipalUnitsEquivResidueFieldUnits`, here
  used in the equivalent `Units.map (residue A)` form supplied by `principalUnitsPow_one`);
* `U_A^{(i+1)} / U_A^{(i+2)} ≅ (κ_A, +)` (`principalUnitsGradedEquiv`).

This file telescopes those into the index of a filtration level in the full unit group:

`[Aˣ : U_A^{(j+1)}] = #κ_Aˣ · (#κ_A)^j`.

The statement is unconditional on finiteness of the residue field: `Nat.card` of an infinite type is
`0` and `Subgroup.index` of an infinite-index subgroup is `0`, and both sides degenerate to `0`
together (an infinite residue field makes every level `≥ 1` of infinite index). For a *finite*
residue field the right-hand side is nonzero, which is how `index_principalUnitsPow_ne_zero` reads
finiteness of the index off the formula.

## Main results

* `ValuationSubring.index_principalUnitsPow_one` : `[Aˣ : U_A^{(1)}] = #κ_Aˣ`.
* `ValuationSubring.relIndex_principalUnitsPow_succ` : `[U_A^{(i+1)} : U_A^{(i+2)}] = #κ_A`.
* `ValuationSubring.index_principalUnitsPow` : `[Aˣ : U_A^{(j+1)}] = #κ_Aˣ · (#κ_A)^j`.
* `ValuationSubring.index_principalUnitsPow_ne_zero` : the index is nonzero when `κ_A` is finite.
-/

noncomputable section

namespace ValuationSubring

variable {L : Type*} [Field L] (A : ValuationSubring L)

/-- **`[Aˣ : U_A^{(1)}] = #κ_Aˣ`.** `U_A^{(1)}` is the kernel of reduction `Aˣ → κ_Aˣ`
(`principalUnitsPow_one`), which is surjective because `A` is a local ring
(`IsLocalRing.surjective_units_map_of_local_ringHom`). -/
theorem index_principalUnitsPow_one :
    (principalUnitsPow A 1).index = Nat.card (IsLocalRing.ResidueField A)ˣ := by
  have hsurj : Function.Surjective (Units.map (IsLocalRing.residue A).toMonoidHom) :=
    IsLocalRing.surjective_units_map_of_local_ringHom (IsLocalRing.residue A)
      IsLocalRing.residue_surjective inferInstance
  rw [principalUnitsPow_one, Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv

variable {π : A} (hπ : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : π ≠ 0)

include hπ hπ0

/-- **`[U_A^{(i+1)} : U_A^{(i+2)}] = #κ_A`**, the graded piece of the filtration read as a relative
index: `principalUnitsGradedEquiv` identifies the quotient with `Multiplicative κ_A`. -/
theorem relIndex_principalUnitsPow_succ (i : ℕ) :
    (principalUnitsPow A (i + 2)).relIndex (principalUnitsPow A (i + 1))
      = Nat.card (IsLocalRing.ResidueField A) := by
  show ((principalUnitsPow A (i + 2)).subgroupOf (principalUnitsPow A (i + 1))).index = _
  rw [← principalUnitsGradedHom_ker_eq A hπ hπ0 i, Subgroup.index_eq_card]
  exact Nat.card_congr (principalUnitsGradedEquiv A hπ hπ0 i).toEquiv

/-- **`[Aˣ : U_A^{(j+1)}] = #κ_Aˣ · (#κ_A)^j`.** Telescopes `index_principalUnitsPow_one` and
`relIndex_principalUnitsPow_succ` along the filtration via `Subgroup.relIndex_mul_index`. -/
theorem index_principalUnitsPow (j : ℕ) :
    (principalUnitsPow A (j + 1)).index
      = Nat.card (IsLocalRing.ResidueField A)ˣ * Nat.card (IsLocalRing.ResidueField A) ^ j := by
  induction j with
  | zero => simpa using index_principalUnitsPow_one A
  | succ j ih =>
    have hle : principalUnitsPow A (j + 2) ≤ principalUnitsPow A (j + 1) :=
      principalUnitsPow_antitone A (by omega)
    rw [← Subgroup.relIndex_mul_index hle, relIndex_principalUnitsPow_succ A hπ hπ0 j, ih]
    ring

/-- **Every level of the filtration has finite index when the residue field is finite.** -/
theorem index_principalUnitsPow_ne_zero [Finite (IsLocalRing.ResidueField A)] (j : ℕ) :
    (principalUnitsPow A (j + 1)).index ≠ 0 := by
  rw [index_principalUnitsPow A hπ hπ0 j]
  exact Nat.mul_ne_zero (Nat.card_pos.ne' ) (pow_ne_zero _ Nat.card_pos.ne')

end ValuationSubring

end
