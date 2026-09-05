/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelExists
import Langlands.LubinTateTowerStepConcreteK2Flat
import Langlands.LubinTateTowerStepK3Degree

/-!
# Concrete `rfl`-checks for the existence half of the tower step, against `LevelExists.lean`

Split out of `Langlands/LubinTateTowerStepLevelExists.lean` (`ROADMAP.md §100`) to break the import
cycle that file's own concrete `rfl`-checks caused: checking `Level.exists_tower_step_next` and
friends against the real hand-named `exists_eisenstein_tower_step_K_2_flat'`/
`adjoin_eq_integralClosure_K_2`/`finrank_K_3_eq_residueCard` needs to import
`LubinTateTowerStepConcreteK2Flat.lean`/`LubinTateTowerStepK3Degree.lean` directly — but
`LevelExists.lean` is itself in the import closure of every `Level*.lean` file (via
`LevelSplits`/`LevelDegree`/`LevelInvariance`), so having `LevelExists.lean` import those two
concrete files directly put `LubinTateTowerStepK3Degree.lean` in that closure too, for no reason
other than housing this file's checks. The checks themselves are moved here, unchanged, so
`LevelExists.lean` no longer needs those two imports at all.

## Main results

Unchanged from `LevelExists.lean`'s own former "Concrete checks" section:
`exists_eisenstein_tower_step_K_2_flat'_of_Level`,
`exists_piTorsion_translate_of_aeval_P₂_eq_zero_of_Level`, `adjoin_eq_integralClosure_K_2_of_Level`,
and `exists_eisenstein_tower_step_K_3`, each with an `example` checking `rfl`-equality against the
corresponding hand-named concrete theorem (or, for the `K_2 → K_3` depth, against the level
identification itself, since no pre-existing `exists_eisenstein_tower_step_K_3` predates this arc).
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

variable {P : O[X]}
  (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])

theorem exists_eisenstein_tower_step_K_2_flat'_of_Level (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)] [CharZero K]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))]
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)] :
    ∃ (P₃ : (O_K2 (K := K) P₂)[X]) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (β' : O_K2 (K := K) P₂),
      IsUnit u₃ ∧ P₃.IsDistinguishedAt (maximalIdeal _) ∧ P₃.natDegree = residueCard O ∧
      Irreducible β' ∧
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃ ∧
      Associated (P₃.coeff 0) β' := by
  have hxK : IsIntegral (K_1 (K := K) P) β := by
    refine ⟨P₂.map (algebraMap _ (K_1 (K := K) P)), hP₂dist.monic.map _, hβroot⟩
  have hgen : (minpoly (K_1 (K := K) P) β).natDegree =
      Module.finrank (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) :=
    (IntermediateField.adjoin.finrank hxK).symm.trans (hβfin.trans
      (finrank_K_2_eq_residueCard (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβfin).symm)
  obtain ⟨P₃, u₃, β', hu₃, hdist, hdeg₃, hirr₃, heq₃, hassoc₃, -⟩ :=
    Level.exists_tower_step_next (level_K_1 (K := K) (P := P)) P₂ hOK
      (hnorm_K_K_1 (K := K) (P := P)) hπ hπnorm hf hα'irr hP₂dist hassoc hdeg hα'norm hirr
      hβroot hgen
  exact ⟨P₃, u₃, β', hu₃, hdist, hdeg₃, hirr₃, heq₃, hassoc₃⟩

example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)] [CharZero K]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))]
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)] :
    exists_eisenstein_tower_step_K_2_flat'_of_Level (K := K) (P := P) P₂ hOK hπ hπnorm hf hu heq
        hPdist hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin =
      exists_eisenstein_tower_step_K_2_flat' (K := K) (P := P) P₂ hOK hπ hπnorm hf hu heq
        hPdist hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin := rfl

theorem exists_piTorsion_translate_of_aeval_P₂_eq_zero_of_Level
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}
    (_hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (_hα'coe : (α' : K_1 (K := K) P) = α)
    {β β' : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβ'root : Polynomial.aeval β' (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    ∃ t' ∈ piTorsion (K := baseChangeSplittingField (K' := K_1 (K := K) P) P₂) hπ hf 1,
      β' = FPiEval hπ hf β t' :=
  Level.exists_piTorsion_translate_of_root (level_K_1 (K := K) (P := P)) P₂ hOK
    (hnorm_K_K_1 (K := K) (P := P)) hπ hf _hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hβroot
    hβ'root

/-- The generic transitivity fact, at `level_K_1`, is literally
`exists_piTorsion_translate_of_aeval_P₂_eq_zero`. -/
example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}
    (_hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    {β β' : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβ'root : Polynomial.aeval β' (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) :
    exists_piTorsion_translate_of_aeval_P₂_eq_zero_of_Level (K := K) (P := P) P₂ hOK hπ hf _hu₂
        heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβ'root =
      exists_piTorsion_translate_of_aeval_P₂_eq_zero (K := K) (P := P) (P₂ := P₂) hOK hπ hf _hu₂
        heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβ'root := rfl

theorem adjoin_eq_integralClosure_K_2_of_Level (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)] [CharZero K] :
    Algebra.adjoin ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        ({β} : Set (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)) =
      integralClosure ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) := by
  have hxK : IsIntegral (K_1 (K := K) P) β :=
    ⟨P₂.map (algebraMap _ (K_1 (K := K) P)), hP₂dist.monic.map _, hβroot⟩
  have hgen : (minpoly (K_1 (K := K) P) β).natDegree =
      Module.finrank (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) :=
    (IntermediateField.adjoin.finrank hxK).symm.trans (hβfin.trans
      (finrank_K_2_eq_residueCard (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβfin).symm)
  exact Level.adjoin_eq_integralClosure_next (level_K_1 (K := K) (P := P)) P₂ hα'irr hP₂dist
    hassoc hirr hβroot hgen

/-- **…and it is literally `adjoin_eq_integralClosure_K_2`**, checked by `rfl` on the fully-applied
terms. -/
example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)] [CharZero K] :
    adjoin_eq_integralClosure_K_2_of_Level (K := K) (P := P) P₂ hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin =
      adjoin_eq_integralClosure_K_2 (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin := rfl

/-! ### Depth 2 -/

variable (P₃ : (O_K2 (K := K) P₂)[X])
  [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]

example : ((level_K_2 (K := K) (P := P) P₂).next P₃).L =
    K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃ := rfl

example : (level_K_2 (K := K) (P := P) P₂).next P₃ =
    ((level_K_1 (K := K) (P := P)).next P₂).next P₃ := rfl

/-- **`K_4`'s Eisenstein polynomial**, produced by the generic step at `level_K_2`. -/
theorem exists_eisenstein_tower_step_K_3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (hu₃ : IsUnit u₃)
    (heq₃ :
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0)
    (hγfin : Module.finrank (K2P2 (K := K) P₂) (K2P2 (K := K) P₂)⟮γ⟯ = residueCard O)
    [Algebra.IsSeparable (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
      (K' := K2P2 (K := K) P₂) P₃)] [CharZero K] :
    letI := ((level_K_2 (K := K) (P := P) P₂).next P₃).isDiscreteValuationRing_OL
    ∃ (P₄ : ((level_K_2 (K := K) (P := P) P₂).next P₃).OL[X])
      (u₄ : ((level_K_2 (K := K) (P := P) P₂).next P₃).OL⟦X⟧)
      (gen : ((level_K_2 (K := K) (P := P) P₂).next P₃).OL),
      IsUnit u₄ ∧
        P₄.IsDistinguishedAt (maximalIdeal ((level_K_2 (K := K) (P := P) P₂).next P₃).OL) ∧
        P₄.natDegree = residueCard O ∧ Irreducible gen ∧
        shifted f (((level_K_2 (K := K) (P := P) P₂).next P₃).towerHom hOK) gen =
          (P₄ : _⟦X⟧) * u₄ ∧
        Associated (P₄.coeff 0) gen ∧
        ‖algebraMap ((level_K_2 (K := K) (P := P) P₂).next P₃).OL
          (baseChangeSplittingField (K' := ((level_K_2 (K := K) (P := P) P₂).next P₃).L) P₄) gen‖ < 1 := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := finiteDimensional_K_K_2 (K := K) (P := P) P₂
  have hirr : Irreducible (P₃.map (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂))) :=
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hβ'irr hP₃dist.monic
      hP₃dist.toIsWeaklyEisensteinAt hdeg hassoc
  have hxK : IsIntegral (K2P2 (K := K) P₂) γ :=
    ⟨P₃.map (algebraMap _ (K2P2 (K := K) P₂)), hP₃dist.monic.map _, hγroot⟩
  have hgen : (minpoly (K2P2 (K := K) P₂) γ).natDegree =
      Module.finrank (K2P2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) :=
    (IntermediateField.adjoin.finrank hxK).symm.trans (hγfin.trans
      (finrank_K_3_eq_residueCard (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg
        β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγfin).symm)
  exact Level.exists_tower_step_next (level_K_2 (K := K) (P := P) P₂) P₃ hOK
    (hnorm_K_K_2 (K := K) (P := P) P₂) hπ hπnorm hf hβ'irr hP₃dist hassoc hdeg hβ'norm hirr
    hγroot hgen

end LubinTate

end
