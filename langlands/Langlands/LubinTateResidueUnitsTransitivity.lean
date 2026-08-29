import Langlands.LubinTateResidueUnitsFreeness
import Langlands.LubinTateRootCount
import Mathlib.GroupTheory.Index

/-!
# ⚠️ `orbit_image_eq_piTorsion_sdiff_zero` is VACUOUS whenever `residueCard O ≥ 3`

This file's main result takes `hsplit` (via `card_piTorsion_one_eq_residueCard` and
`ncard_piTorsion_one_sdiff_zero`) as a hypothesis, which `Langlands/LubinTateHsplitVacuity.lean`
proves can never be discharged for `residueCard O ≥ 3` under this file's own standing
`[IsFractionRing O K]`. See `Langlands.LubinTateRootCount`'s and `Langlands.LubinTateFieldTower`'s
module docstrings for the full explanation, and `Langlands.LubinTateSplittingField` for the
replacement construction. The freeness and `(O/π)ˣ`-action machinery this file builds on
(`Langlands.LubinTateResidueUnitsFreeness`, `Langlands.LubinTateResidueUnitsAction`) does **not**
depend on `hsplit` and remains genuine, non-vacuous, and reusable as-is.

# Transitivity of the `(O/π)ˣ`-action on nonzero `π`-torsion

`LubinTateResidueUnitsFreeness.lean` establishes freeness of the `(ResidueField O)ˣ`-action
`residuePiTorsionMulAction` on `piTorsion hπ hf 1`: `u' • α = α` for `α` nonzero forces `u' = 1`,
i.e. `stabilizer (ResidueField O)ˣ α = ⊥`. This file assembles that with `Nat.card (ResidueField
O)ˣ = residueCard O - 1` (`Nat.card_units`, a `GroupWithZero` fact) and
`card_piTorsion_one_eq_residueCard` into a counting argument: a free action of a group of size
`q - 1` on a set of size `q - 1` is transitive.

## Route

For `α` a nonzero element of `piTorsion hπ hf 1`, work with the orbit `MulAction.orbit
(ResidueField O)ˣ ⟨α, hα⟩` inside `↥(piTorsion hπ hf 1)`:

* **`0` is a global fixed point** (`residuePiTorsion_smul_zero`): `eval (phiU u) 0 = 0` for any
  `u`, so `u' • ⟨0, _⟩ = ⟨0, _⟩` for every `u'`. Combined with the action being invertible, this
  forces every element of the orbit of a *nonzero* point to be itself nonzero
  (`ne_zero_of_mem_orbit_of_ne_zero`) — if `u' • x = 0` then `x = u'⁻¹ • 0 = 0`.
* **The orbit has exactly `residueCard O - 1` elements** (`ncard_orbit_eq`): `MulAction.
  index_stabilizer` identifies `(orbit G x).ncard` with `(stabilizer G x).index`; freeness gives
  `stabilizer = ⊥` (`Subgroup.eq_bot_iff_forall` + `eq_one_of_residuePiTorsion_smul_eq_self`), and
  `Subgroup.index_bot` identifies that index with `Nat.card (ResidueField O)ˣ = residueCard O - 1`
  (`Nat.card_units`).
* **`piTorsion hπ hf 1 \ {0}` also has exactly `residueCard O - 1` elements**
  (`card_piTorsion_one_eq_residueCard` + `Set.ncard_sdiff_singleton_of_mem`).
* **The orbit's image in `K` is exactly `piTorsion hπ hf 1 \ {0}`** (`orbit_image_eq`): the image
  is a subset of `piTorsion hπ hf 1 \ {0}` of the same finite cardinality
  (`Set.eq_of_subset_of_ncard_le`), forcing equality.

## Main result

* `orbit_image_eq_piTorsion_sdiff_zero` : for `α ≠ 0` in `piTorsion hπ hf 1`, the image in `K` of
  the `(ResidueField O)ˣ`-orbit of `α` is exactly `piTorsion hπ hf 1 \ {0}`.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open NonarchimedeanPowerSeriesEval PowerSeries IsLocalRing Polynomial MulAction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [FaithfulSMul O K]
variable {π : O} {f : O⟦X⟧}

variable (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
  (hπnorm : ‖algebraMap O K π‖ < 1) (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]}
  {w : O⟦X⟧} (hw : IsUnit w) (heq : f = (P : O⟦X⟧) * w)
  (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)

/-- **`0` is a fixed point of `residuePiTorsionMulAction`.** `eval (phiU u) 0 = 0` for any `u`
(`eval_zero_of_coeff_zero_eq_zero`), so every `Oˣ`-preimage acts trivially on the zero element. -/
theorem residuePiTorsion_smul_zero (u' : (ResidueField O)ˣ) :
    letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
    u' • (⟨0, zero_mem_piTorsion hπ hf 1⟩ : ↥(piTorsion (K := K) hπ hf 1)) =
      ⟨0, zero_mem_piTorsion hπ hf 1⟩ := by
  letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
  apply Subtype.ext
  rw [coe_residuePiTorsion_smul hOK hπ hπnorm hf hw heq hPdist hPdeg2]
  exact eval_zero_of_coeff_zero_eq_zero
    (by rw [PowerSeries.coeff_zero_eq_constantCoeff]
        exact constantCoeff_phiU hπ hf (Function.surjInv residueUnitsMap_surjective u'))

/-- **Every element of the orbit of a nonzero point is itself nonzero.** If `y = u' • x` were `0`,
applying `u'⁻¹` and using `0`'s fixed-point property (`residuePiTorsion_smul_zero`) would force `x
= 0`. -/
theorem ne_zero_of_mem_orbit_of_ne_zero {x : ↥(piTorsion (K := K) hπ hf 1)} (hx0 : (x : K) ≠ 0)
    {y : ↥(piTorsion (K := K) hπ hf 1)}
    (hy : letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
      y ∈ orbit (ResidueField O)ˣ x) :
    (y : K) ≠ 0 := by
  letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
  intro hy0
  obtain ⟨u', hu'⟩ := hy
  apply hx0
  have hzero : y = ⟨0, zero_mem_piTorsion hπ hf 1⟩ := Subtype.ext hy0
  have := congrArg (fun z ↦ u'⁻¹ • z) hu'
  simp only [inv_smul_smul] at this
  rw [hzero, residuePiTorsion_smul_zero hOK hπ hπnorm hf hw heq hPdist hPdeg2] at this
  exact congrArg Subtype.val this

/-- **The stabilizer of a nonzero point is trivial.** Exactly `eq_one_of_residuePiTorsion_smul_eq_self`,
repackaged via `Subgroup.eq_bot_iff_forall`. -/
theorem stabilizer_eq_bot {x : ↥(piTorsion (K := K) hπ hf 1)} (hx0 : (x : K) ≠ 0) :
    letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
    stabilizer (ResidueField O)ˣ x = ⊥ := by
  letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
  rw [Subgroup.eq_bot_iff_forall]
  intro u' hu'
  rw [mem_stabilizer_iff] at hu'
  exact eq_one_of_residuePiTorsion_smul_eq_self hOK hπ hπnorm hf hw heq hPdist hPdeg2 hx0 hu'

/-- **The orbit of a nonzero point has exactly `residueCard O - 1` elements.** `MulAction.
index_stabilizer` identifies `(orbit G x).ncard` with `(stabilizer G x).index`; the trivial
stabilizer (`stabilizer_eq_bot`) makes that index `Nat.card (ResidueField O)ˣ`
(`Subgroup.index_bot`), which is `residueCard O - 1` (`Nat.card_units`, `ResidueField O` a field). -/
theorem ncard_orbit_eq {x : ↥(piTorsion (K := K) hπ hf 1)} (hx0 : (x : K) ≠ 0) :
    letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
    (orbit (ResidueField O)ˣ x).ncard = residueCard O - 1 := by
  letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
  rw [← index_stabilizer, stabilizer_eq_bot hOK hπ hπnorm hf hw heq hPdist hPdeg2 hx0,
    Subgroup.index_bot, Nat.card_units]

omit [FaithfulSMul O K] in
/-- **`piTorsion hπ hf 1 \ {0}` has exactly `residueCard O - 1` elements**, given the torsion count
itself. Stated against `hcard` rather than re-deriving it, so that it applies at any field where
the count has been established — including `Langlands.LubinTateSplittingField.K_1`, where
`[IsFractionRing O K]` is unavailable. -/
theorem ncard_piTorsion_one_sdiff_zero_of_card (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f)
    (hcard : Nat.card (piTorsion (K := K) hπ hf 1) = residueCard O) :
    (piTorsion (K := K) hπ hf 1 \ {0}).ncard = residueCard O - 1 := by
  rw [Set.ncard_sdiff_singleton_of_mem (zero_mem_piTorsion hπ hf 1), ← Nat.card_coe_set_eq, hcard]

/-- **The main transitivity theorem**, against the torsion count as a hypothesis. The image in `K`
of the `(ResidueField O)ˣ`-orbit of any nonzero `α ∈ piTorsion hπ hf 1` is exactly
`piTorsion hπ hf 1 \ {0}`: a subset of the same finite cardinality (`ncard_orbit_eq`,
`ncard_piTorsion_one_sdiff_zero_of_card`) forces equality (`Set.eq_of_subset_of_ncard_le`).

This is the "free action of a group of size `q - 1` on a set of size `q - 1` is transitive"
argument, run through orbit cardinality rather than through `MulAction.IsPretransitive` directly:
freeness gives `stabilizer = ⊥` hence `|orbit| = |G| = q - 1` exactly, and an orbit is by
construction contained in the nonzero torsion, so equal cardinality forces equality of sets. -/
theorem orbit_image_eq_piTorsion_sdiff_zero_of_card
    (hcard : Nat.card (piTorsion (K := K) hπ hf 1) = residueCard O)
    {α : K} (hα : α ∈ piTorsion (K := K) hπ hf 1) (hα0 : α ≠ 0) :
    letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
    Subtype.val '' (orbit (ResidueField O)ˣ (⟨α, hα⟩ : ↥(piTorsion (K := K) hπ hf 1))) =
      piTorsion (K := K) hπ hf 1 \ {0} := by
  letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
  have hsub : Subtype.val '' (orbit (ResidueField O)ˣ
      (⟨α, hα⟩ : ↥(piTorsion (K := K) hπ hf 1))) ⊆ piTorsion (K := K) hπ hf 1 \ {0} := by
    rintro y ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    exact ne_zero_of_mem_orbit_of_ne_zero hOK hπ hπnorm hf hw heq hPdist hPdeg2 hα0 hz
  have hcardle : (piTorsion (K := K) hπ hf 1 \ {0}).ncard ≤
      (Subtype.val '' (orbit (ResidueField O)ˣ
        (⟨α, hα⟩ : ↥(piTorsion (K := K) hπ hf 1)))).ncard := by
    rw [Set.ncard_image_of_injective _ Subtype.coe_injective,
      ncard_orbit_eq hOK hπ hπnorm hf hw heq hPdist hPdeg2 hα0,
      ncard_piTorsion_one_sdiff_zero_of_card hπ hf hcard]
  have hcardne : Nat.card ↥(piTorsion (K := K) hπ hf 1) ≠ 0 := by
    rw [hcard]; have := two_le_residueCard (O := O); omega
  have hfinite : Set.Finite (piTorsion (K := K) hπ hf 1) :=
    Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hcardne)
  exact Set.eq_of_subset_of_ncard_le hsub hcardle hfinite.sdiff

/-- **⚠️ VACUOUS whenever `residueCard O ≥ 3`** — see this file's module docstring. The
`[IsFractionRing O K]` + `hsplit` corollary of `ncard_piTorsion_one_sdiff_zero_of_card`. -/
theorem ncard_piTorsion_one_sdiff_zero [IsFractionRing O K]
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1)
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {w : O⟦X⟧} (hw : IsUnit w)
    (heq : f = (P : O⟦X⟧) * w) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) (hsplit : (P.divX.map (algebraMap O K)).Splits) :
    (piTorsion (K := K) hπ hf 1 \ {0}).ncard = residueCard O - 1 :=
  ncard_piTorsion_one_sdiff_zero_of_card hπ hf
    (card_piTorsion_one_eq_residueCard hOK hπ hπnorm hf hw heq hPdist hPdeg hsplit)

/-- **⚠️ VACUOUS whenever `residueCard O ≥ 3`** — see this file's module docstring. The
`[IsFractionRing O K]` + `hsplit` corollary of `orbit_image_eq_piTorsion_sdiff_zero_of_card`. -/
theorem orbit_image_eq_piTorsion_sdiff_zero [IsFractionRing O K]
    (hPdeg : P.natDegree = residueCard O) (hsplit : (P.divX.map (algebraMap O K)).Splits)
    {α : K} (hα : α ∈ piTorsion (K := K) hπ hf 1) (hα0 : α ≠ 0) :
    letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
    Subtype.val '' (orbit (ResidueField O)ˣ (⟨α, hα⟩ : ↥(piTorsion (K := K) hπ hf 1))) =
      piTorsion (K := K) hπ hf 1 \ {0} :=
  orbit_image_eq_piTorsion_sdiff_zero_of_card hOK hπ hπnorm hf hw heq hPdist hPdeg2
    (card_piTorsion_one_eq_residueCard hOK hπ hπnorm hf hw heq hPdist hPdeg hsplit) hα hα0

end LubinTate

end
