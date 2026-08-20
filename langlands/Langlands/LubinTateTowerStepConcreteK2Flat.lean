/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepConcreteK2
import Langlands.LubinTateTowerStepK3

/-!
# Transporting `exists_eisenstein_tower_step_K_2`'s output to the flat `O_{K_2}` spelling

`exists_eisenstein_tower_step_K_2` (`Langlands/LubinTateTowerStepConcreteK2.lean`) produces `P₃`/`u₃`
typed against the **nested** `O_{K_2}` spelling `↥(integralClosure (↥(integralClosure ↥𝒪[K] (K_1 P)))
(K_2 P₂))` — the spelling `Langlands/LubinTateTowerStepConcreteK2.lean` has used since it was written
and was not touched by `ROADMAP.md §73`'s switch to the *flat* spelling `O_K2 := ↥(integralClosure
↥𝒪[K] (K_2 P₂))` (`Langlands/LubinTateTowerStepK3.lean`). Every `K_3`-level theorem built in
`ROADMAP.md §74`–`§75` (`Langlands/LubinTateTowerStepK3RootConnect.lean`,
`Langlands/LubinTateTowerStepK3Degree.lean`) is stated against the flat spelling, so using
`exists_eisenstein_tower_step_K_2`'s concrete witnesses there needs a transport.

This file provides it, via `Langlands/IntegralClosureTower.lean`'s `integralClosureRingEquiv`
(specialized at `R := ↥𝒪[K]`, `L := K_1 P`, `M := K_2 P₂`, which is exactly the nested/flat pair here)
run backwards (`.symm`, nested → flat): `Polynomial.map`/`PowerSeries.map` along the underlying ring
homomorphism carry `P₃`/`u₃` across, and `IsUnit`/`IsDistinguishedAt`/`natDegree` transport along with
them.

## The three conjuncts, and what closes them

* `IsUnit u₃` transports along **any** ring homomorphism (`IsUnit.map`, general, no injectivity
  needed): a unit's image under a monoid homomorphism is again a unit.
* `P₃.natDegree = residueCard O` transports because `Polynomial.map` along an **injective** ring
  homomorphism preserves `natDegree` (`Polynomial.natDegree_map_eq_of_injective`) — `e.symm` is a
  `RingEquiv`, hence injective.
* `P₃.IsDistinguishedAt (maximalIdeal _)` transports via the general fact
  `Polynomial.IsDistinguishedAt.map` (added here — `Polynomial.IsWeaklyEisensteinAt.map` already exists
  in Mathlib in exactly this shape, but no `IsDistinguishedAt`-level analogue did; it is immediate from
  that lemma plus `Polynomial.Monic.map`), combined with `IsLocalRing.map_ringEquiv_maximalIdeal`
  (already used in `Langlands/IntegralClosureTower.lean` for the same nested/flat pair) to identify the
  pushed-forward maximal ideal of the nested ring with the maximal ideal of the flat ring.

## Main result

* `exists_eisenstein_tower_step_K_2_flat` : `exists_eisenstein_tower_step_K_2`'s conclusion, restated
  with `P₃ : (O_K2 P₂)[X]` and `u₃ : (O_K2 P₂)⟦X⟧` (the flat spelling), same three conjuncts.
-/

noncomputable section

open scoped Polynomial IntermediateField
open IsLocalRing Polynomial PowerSeries

namespace Polynomial

/-- **`IsDistinguishedAt` transports along any ring homomorphism**, to the pushed-forward ideal —
the `IsDistinguishedAt`-level analogue of `Polynomial.IsWeaklyEisensteinAt.map`, immediate from that
lemma plus `Polynomial.Monic.map`. -/
theorem IsDistinguishedAt.map {R : Type*} [CommRing R] {f : R[X]} {I : Ideal R}
    (hf : f.IsDistinguishedAt I) {A : Type*} [CommRing A] (φ : R →+* A) :
    (f.map φ).IsDistinguishedAt (I.map φ) :=
  ⟨hf.toIsWeaklyEisensteinAt.map φ, hf.monic.map φ⟩

end Polynomial

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]}
  (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])

/-- **`exists_eisenstein_tower_step_K_2`'s output, transported to the flat `O_{K_2}` spelling.**
Same hypotheses (the `[IsDiscreteValuationRing (nested O_{K_2})]` instance is still needed, exactly
as `exists_eisenstein_tower_step_K_2` itself needs it, to elaborate that theorem's own statement), plus
`[IsLocalRing (O_K2 P₂)] [IsDiscreteValuationRing (O_K2 P₂)]` for the flat spelling (mirroring the
ambient hypotheses `Langlands/LubinTateTowerStepK3RootConnect.lean` already carries at every theorem
mentioning `O_K2`). The witnesses are `e.symm`-transported (`e := integralClosureRingEquiv`, nested →
flat), where the transport is along `Polynomial.map`/`PowerSeries.map` of the underlying ring
homomorphism. -/
theorem exists_eisenstein_tower_step_K_2_flat (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
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
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)] [CharZero K]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (K_2 (K' := K_1 (K := K) P) P₂))]
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)] :
    ∃ (P₃ : (O_K2 (K := K) P₂)[X]) (u₃ : (O_K2 (K := K) P₂)⟦X⟧),
      IsUnit u₃ ∧ P₃.IsDistinguishedAt (maximalIdeal _) ∧ P₃.natDegree = residueCard O := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := isScalarTower_R_K_1_K_2 (K := K) (P := P) (P₂ := P₂)
  obtain ⟨P₃n, u₃n, hu₃n, hP₃n, hdeg₃n⟩ :=
    exists_eisenstein_tower_step_K_2 hOK hπ hπnorm hf hu heq hPdist hPdeg hu₂ heq₂ hα'irr hP₂dist
      hassoc hdeg hα'norm hα'coe hirr hβroot hβfin
  set e := (integralClosureRingEquiv (R := ↥(ValuativeRel.valuation K).valuationSubring)
    (L := K_1 (K := K) P) (M := K2P2 (K := K) P₂)).symm with he
  refine ⟨P₃n.map e.toRingHom, PowerSeries.map e.toRingHom u₃n, hu₃n.map (PowerSeries.map e.toRingHom),
    ?_, ?_⟩
  · have hP₃n' : P₃n.IsDistinguishedAt (maximalIdeal ↥(integralClosure
        (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))
        (K2P2 (K := K) P₂)).toSubring) := hP₃n
    have hme := hP₃n'.map e.toRingHom
    have hcoe : Ideal.map e.toRingHom (maximalIdeal ↥(integralClosure
        (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))
        (K2P2 (K := K) P₂)).toSubring) =
        Ideal.map e (maximalIdeal ↥(integralClosure
        (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))
        (K2P2 (K := K) P₂)).toSubring) := rfl
    rw [hcoe, IsLocalRing.map_ringEquiv_maximalIdeal e] at hme
    exact hme
  · rw [Polynomial.natDegree_map_eq_of_injective e.injective, hdeg₃n]

end LubinTate

end
