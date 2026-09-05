/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelInvariance
import Langlands.LubinTateTowerStepDegree
import Langlands.LubinTateTowerStepK3Degree

/-!
# Concrete `rfl`-checks for `piTorsion`-invariance and the degree theorem, against `LevelInvariance.lean`

Split out of `Langlands/LubinTateTowerStepLevelInvariance.lean` (`ROADMAP.md §100`), for the same
reason as `LubinTateTowerStepLevelExistsCheck.lean`/`LubinTateTowerStepLevelDegreeCheck.lean`:
checking `Level.piTorsion_one_next_eq_algebraMap_image`/`Level.finrank_next_eq_residueCard` against
the real hand-named `piTorsion_one_K_2/K_3_eq_algebraMap_image`/`finrank_K_2/K_3_eq_residueCard`
needs to import `LubinTateTowerStepDegree.lean`/`LubinTateTowerStepK3Degree.lean` directly, and
`LevelInvariance.lean` sits in the import closure of every downstream `Level*.lean` file, so keeping
those imports there would put `LubinTateTowerStepK3Degree.lean` back in that closure for no reason
but housing checks.

## Main results

Unchanged from `LevelInvariance.lean`'s own former four `example`s: the generic invariance/degree
theorems, instantiated at `level_K_1`/`level_K_2`, are `rfl`-equal to
`piTorsion_one_K_2_eq_algebraMap_image`/`piTorsion_one_K_3_eq_algebraMap_image`/
`finrank_K_2_eq_residueCard`/`finrank_K_3_eq_residueCard`.
-/

noncomputable section

open scoped Polynomial IntermediateField

namespace LubinTate

open IsLocalRing PowerSeries Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]

/-- **Invariance, `K_1 → K_2`, `rfl`-recovery**: the generic theorem at `level_K_1`, fed
`splits_divX_map_K_1` (free from `K_1 P`'s own construction), types exactly as
`piTorsion_one_K_2_eq_algebraMap_image`'s own statement. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) :
    Level.piTorsion_one_next_eq_algebraMap_image (level_K_1 (K := K) (P := P)) P₂ hOK
        (hnorm_K_K_1 (K := K) (P := P)) hπ hπnorm hf hu heq hPdist hPdeg
        (splits_divX_map_K_1 (K := K) P) =
      piTorsion_one_K_2_eq_algebraMap_image (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq
        hPdist hPdeg := rfl

/-- **Invariance, `K_2 → K_3`, `rfl`-recovery**: the same generic theorem at `level_K_2`, fed the
`Splits` datum propagated one hop by `Level.splits_next`, types exactly as
`piTorsion_one_K_3_eq_algebraMap_image`'s own statement. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]
    (P₃ : (O_K2 (K := K) P₂)[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) :
    Level.piTorsion_one_next_eq_algebraMap_image (level_K_2 (K := K) (P := P) P₂) P₃ hOK
        (hnorm_K_K_2 (K := K) (P := P) P₂) hπ hπnorm hf hu heq hPdist hPdeg
        (Level.splits_next (level_K_1 (K := K) (P := P)) P₂ hOK
          (splits_divX_map_K_1 (K := K) P)) =
      piTorsion_one_K_3_eq_algebraMap_image (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq
        hPdist hPdeg := rfl

/-- **The degree theorem, `K_1 → K_2`, `rfl`-recovery** against `finrank_K_2_eq_residueCard`.
The concrete version's extra `hα'coe : (α' : K_1 P) = α` argument is the inessential
scaffolding the generic theorem does not need. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' =
      (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)))⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O) :
    Level.finrank_next_eq_residueCard (level_K_1 (K := K) (P := P)) P₂ hOK
        (hnorm_K_K_1 (K := K) (P := P)) hπ hπnorm hf hu heq hPdist hPdeg
        (splits_divX_map_K_1 (K := K) P) hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hβroot
        hβfin =
      finrank_K_2_eq_residueCard (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβfin := rfl

/-- **The degree theorem, `K_2 → K_3`, `rfl`-recovery** against `finrank_K_3_eq_residueCard` —
the degree computation stated once and checked at both real depths. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]
    (P₃ : (O_K2 (K := K) P₂)[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (hu₃ : IsUnit u₃)
    (heq₃ : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : (O_K2 (K := K) P₂)⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0)
    (hγfin : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      Module.finrank (K2P2 (K := K) P₂) (K2P2 (K := K) P₂)⟮γ⟯ = residueCard O) :
    Level.finrank_next_eq_residueCard (level_K_2 (K := K) (P := P) P₂) P₃ hOK
        (hnorm_K_K_2 (K := K) (P := P) P₂) hπ hπnorm hf hu heq hPdist hPdeg
        (Level.splits_next (level_K_1 (K := K) (P := P)) P₂ hOK (splits_divX_map_K_1 (K := K) P))
        hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγfin =
      finrank_K_3_eq_residueCard (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg
        β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγfin := rfl

end LubinTate

end
