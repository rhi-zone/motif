/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepConcreteK2Flat
import Langlands.LubinTateTowerStepResidueFieldK3

/-!
# The `K_2 → K_3` tower step, instantiated at concrete witnesses

`Langlands/LubinTateTowerStepK3RootConnect.lean`/`LubinTateTowerStepK3Degree.lean`/
`LubinTateTowerStepMonogenicK3.lean`/`LubinTateTowerStepResidueFieldK3.lean` state the `K_2 → K_3`
generic theorems for an *arbitrary* `P₃ : (O_K2 P₂)[X]` and generator `β' : O_K2 P₂` satisfying the
Weierstrass equation `heq₃`, taken as explicit hypotheses. `Langlands/
LubinTateTowerStepConcreteK2Flat.lean`'s `exists_eisenstein_tower_step_K_2_flat'` (`ROADMAP.md §77`)
supplies concrete such witnesses. This file feeds them through, mirroring the role `Langlands/
LubinTateTowerStepConcrete.lean` plays at the `K_1 → K_2` step.

## Scope, matched precisely against the `K_1 → K_2` precedent

`Langlands/LubinTateTowerStepConcrete.lean` itself never concretely discharges the norm bound
`hα'norm : ‖algebraMap _ (baseChangeSplittingField P₂) (α' : _)‖ < 1` — every downstream theorem in this arc
(`Langlands/LubinTateTowerStepRootConnect.lean`, `LubinTateTowerStepDegree.lean`,
`LubinTateTowerStepMonogenic.lean`, `LubinTateTowerStepLocalRing.lean`) keeps taking it as an
explicit ambient hypothesis; a repository-wide search confirms `hα'norm` is *never* the conclusion of
any theorem in this codebase, only ever a hypothesis. So "concrete instantiation" at the `K_1 → K_2`
level itself means: partially applying the generic root-connect theorems at concrete `P₂`/`α'`/`heq₂`
data, while still leaving the norm bound and the root itself (`β`/`hβroot`) to be supplied at the call
site — except where `exists_finrank_adjoin_eq_residueCard_K_2` goes further and *derives* a concrete
root `β` (via the splitting field) together with its finite-degree fact, independent of any norm
hypothesis. This file matches that same scope, one level up, not a lesser one: `hβ'norm` stays an
explicit hypothesis (as it does at every existing call site of the `K_2 → K_3` theorems), while
`exists_finrank_adjoin_eq_residueCard_K_3` below derives a concrete root `γ` of `P₃`'s image and its
finite-degree fact directly, mirroring `exists_finrank_adjoin_eq_residueCard_K_2`'s own proof.

## Main results

* `norm_lt_one_of_aeval_P₃_eq_zero_concrete`/`eval_f_eq_of_aeval_P₃_eq_zero_concrete`/
  `exists_piTorsion_translate_of_aeval_P₃_eq_zero_concrete` : the `K_2 → K_3` generic root-connect
  theorems, instantiated at `exists_eisenstein_tower_step_K_2_flat'`'s concrete `P₃`/`u₃`/`β'`/`heq₃`/
  `hβ'irr`/`hP₃dist`/`hassoc` — leaving only `hβ'norm` (unavoidable, per the scope note above) and the
  root data (`γ`/`hγroot`, or `γ, γ'`/`hγroot`/`hγ'root`) to be supplied at the call site.
* `exists_finrank_adjoin_eq_residueCard_K_3` : **a concrete root `γ` of `P₃`'s image exists, with
  `Module.finrank (K2P2 P₂) (K2P2 P₂)⟮γ⟯ = residueCard O`** — the `K_2 → K_3` analogue of
  `exists_finrank_adjoin_eq_residueCard_K_2`, using `K_3 P₃`'s splitting-field structure directly
  (independent of `hβ'norm`).
-/

noncomputable section

open scoped Polynomial IntermediateField

open IsLocalRing Polynomial PowerSeries

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]} (P₂ : (↥(integralClosure
    ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
  [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **`norm_lt_one_of_aeval_P₃_eq_zero`, instantiated at `exists_eisenstein_tower_step_K_2_flat'`'s
concrete witness.** Only `hβ'norm` (the norm bound on the generator, never concretely discharged
anywhere in this codebase — see the module docstring) and the root data (`γ`/`hγroot`) remain as
hypotheses. -/
theorem norm_lt_one_of_aeval_P₃_eq_zero_concrete (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc₂ : Associated (P₂.coeff 0) α') (hdeg₂ : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr₂ : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)] [CharZero K]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))] :
    ∃ (P₃ : (O_K2 (K := K) P₂)[X]) (β' : O_K2 (K := K) P₂),
      ∀ (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
        ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
        (γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        (_hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0),
        letI := K_2.instAlgebraK (K := K) (P := P) P₂
        ‖γ‖ < 1 := by
  obtain ⟨P₃, u₃, β', hu₃, hP₃dist, hdeg₃, hβ'irr, heq₃, hassoc₃⟩ :=
    exists_eisenstein_tower_step_K_2_flat' (K := K) (P := P) P₂ hOK hπ hπnorm hf hu heq hPdist hPdeg
      hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm hα'coe hirr₂ hβroot hβfin
  have hpos : 0 < P₃.natDegree := by rw [hdeg₃]; have := two_le_residueCard (O := O); omega
  exact ⟨P₃, β', fun hβ'norm γ hγroot =>
    norm_lt_one_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ β' hβ'irr hP₃dist hassoc₃ hpos hβ'norm
      hγroot⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **`eval_f_eq_of_aeval_P₃_eq_zero`, instantiated at `exists_eisenstein_tower_step_K_2_flat'`'s
concrete witness.** Same scope note as `norm_lt_one_of_aeval_P₃_eq_zero_concrete`. -/
theorem eval_f_eq_of_aeval_P₃_eq_zero_concrete (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc₂ : Associated (P₂.coeff 0) α') (hdeg₂ : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr₂ : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)] [CharZero K]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))] :
    ∃ (P₃ : (O_K2 (K := K) P₂)[X]) (β' : O_K2 (K := K) P₂),
      ∀ (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
        ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
        (γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        (_hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0),
        letI := K_2.instAlgebraK (K := K) (P := P) P₂
        letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
        NonarchimedeanPowerSeriesEval.eval f γ =
          algebraMap (O_K2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
            β' := by
  obtain ⟨P₃, u₃, β', hu₃, hP₃dist, hdeg₃, hβ'irr, heq₃, hassoc₃⟩ :=
    exists_eisenstein_tower_step_K_2_flat' (K := K) (P := P) P₂ hOK hπ hπnorm hf hu heq hPdist hPdeg
      hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm hα'coe hirr₂ hβroot hβfin
  have hpos : 0 < P₃.natDegree := by rw [hdeg₃]; have := two_le_residueCard (O := O); omega
  exact ⟨P₃, β', fun hβ'norm γ hγroot =>
    eval_f_eq_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ hOK β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc₃
      hpos hβ'norm hγroot⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **`exists_piTorsion_translate_of_aeval_P₃_eq_zero`, instantiated at
`exists_eisenstein_tower_step_K_2_flat'`'s concrete witness.** Same scope note as
`norm_lt_one_of_aeval_P₃_eq_zero_concrete`. -/
theorem exists_piTorsion_translate_of_aeval_P₃_eq_zero_concrete (hOK : ∀ c : O,
    ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1)
    {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc₂ : Associated (P₂.coeff 0) α') (hdeg₂ : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr₂ : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)] [CharZero K]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))] :
    ∃ (P₃ : (O_K2 (K := K) P₂)[X]) (β' : O_K2 (K := K) P₂),
      ∀ (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
        ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
        (γ γ' : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        (_hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0)
        (_hγ'root : Polynomial.aeval γ' (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0),
        letI := K_2.instAlgebraK (K := K) (P := P) P₂
        letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
        ∃ t' ∈ piTorsion (K := K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) hπ hf 1,
          γ' = FPiEval hπ hf γ t' := by
  obtain ⟨P₃, u₃, β', hu₃, hP₃dist, hdeg₃, hβ'irr, heq₃, hassoc₃⟩ :=
    exists_eisenstein_tower_step_K_2_flat' (K := K) (P := P) P₂ hOK hπ hπnorm hf hu heq hPdist hPdeg
      hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm hα'coe hirr₂ hβroot hβfin
  have hpos : 0 < P₃.natDegree := by rw [hdeg₃]; have := two_le_residueCard (O := O); omega
  exact ⟨P₃, β', fun hβ'norm γ γ' hγroot hγ'root =>
    exists_piTorsion_translate_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ hOK hπ hf β' u₃ hu₃ heq₃
      hβ'irr hP₃dist hassoc₃ hpos hβ'norm hγroot hγ'root⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A concrete root of `P₃`'s image exists, generating a degree-`q` extension of `K2P2 P₂`.** The
`K_2 → K_3` analogue of `exists_finrank_adjoin_eq_residueCard_K_2`: `P₃`'s image over `K2P2 P₂` is
monic and irreducible (`Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated`, from
`exists_eisenstein_tower_step_K_2_flat'`'s Eisenstein-shape data — no external `hirr` hypothesis
needed, mirroring `LubinTateTowerStepMonogenicK3.lean`'s own derivation of the same fact), so it
splits over `K_3 P₃` (by construction as a splitting field) with a positive-degree image, giving a
concrete root `γ` whose minimal polynomial is exactly `P₃`'s image, hence
`Module.finrank (K2P2 P₂) (K2P2 P₂)⟮γ⟯ = P₃.natDegree = residueCard O`. -/
theorem exists_finrank_adjoin_eq_residueCard_K_3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc₂ : Associated (P₂.coeff 0) α') (hdeg₂ : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr₂ : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)] [CharZero K]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))] :
    ∃ (P₃ : (O_K2 (K := K) P₂)[X]),
      P₃.natDegree = residueCard O ∧
      ∃ γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃,
        Module.finrank (K2P2 (K := K) P₂) (K2P2 (K := K) P₂)⟮γ⟯ = residueCard O := by
  obtain ⟨P₃, u₃, β', hu₃, hP₃dist, hdeg₃, hβ'irr, heq₃, hassoc₃⟩ :=
    exists_eisenstein_tower_step_K_2_flat' (K := K) (P := P) P₂ hOK hπ hπnorm hf hu heq hPdist hPdeg
      hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm hα'coe hirr₂ hβroot hβfin
  refine ⟨P₃, hdeg₃, ?_⟩
  haveI := finiteDimensional_K_K_2 (K := K) (P := P) P₂
  set P₃k := P₃.map (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) with hP₃k
  have hpos : 0 < P₃.natDegree := by rw [hdeg₃]; have := two_le_residueCard (O := O); omega
  have hirr₃ : Irreducible P₃k :=
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hβ'irr hP₃dist.monic
      hP₃dist.toIsWeaklyEisensteinAt hpos hassoc₃
  have hP₃kmonic : P₃k.Monic := hP₃dist.monic.map _
  have hP₃kdeg : P₃k.natDegree = residueCard O := by rw [hP₃k, hP₃dist.monic.natDegree_map, hdeg₃]
  have hdegne : (P₃k.map (algebraMap (K2P2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃))).degree ≠ 0 := by
    refine (Polynomial.natDegree_pos_iff_degree_pos.mp ?_).ne'
    rw [hP₃kmonic.natDegree_map, hP₃kdeg]
    exact lt_of_lt_of_le (by norm_num) two_le_residueCard
  obtain ⟨γ, hγ⟩ :=
    (Polynomial.IsSplittingField.splits' (K := K2P2 (K := K) P₂)
      (L := K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
      (f := P₃k)).exists_eval_eq_zero hdegne
  rw [Polynomial.eval_map, ← Polynomial.aeval_def] at hγ
  have hγroot : Polynomial.aeval γ P₃k = 0 := hγ
  have hγint : IsIntegral (K2P2 (K := K) P₂) γ := ⟨P₃k, hP₃kmonic, hγroot⟩
  have hmin : P₃k = minpoly (K2P2 (K := K) P₂) γ :=
    minpoly.eq_of_irreducible_of_monic hirr₃ hγroot hP₃kmonic
  refine ⟨γ, ?_⟩
  rw [IntermediateField.adjoin.finrank hγint, ← hmin, hP₃kdeg]

end LubinTate

end
