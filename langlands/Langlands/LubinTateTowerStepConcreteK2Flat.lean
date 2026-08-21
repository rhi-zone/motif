/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepConcreteK2
import Langlands.LubinTateTowerStepK3RootConnect

/-!
# Transporting `exists_eisenstein_tower_step_K_2`'s output to the flat `O_{K_2}` spelling

`exists_eisenstein_tower_step_K_2` (`Langlands/LubinTateTowerStepConcreteK2.lean`) produces `P₃`/`u₃`
typed against the **nested** `O_{K_2}` spelling `↥(integralClosure (↥(integralClosure ↥𝒪[K] (K_1 P)))
(baseChangeSplittingField P₂))` — the spelling `Langlands/LubinTateTowerStepConcreteK2.lean` has used since it was written
and was not touched by `ROADMAP.md §73`'s switch to the *flat* spelling `O_K2 := ↥(integralClosure
↥𝒪[K] (baseChangeSplittingField P₂))` (`Langlands/LubinTateTowerStepK3.lean`). Every `K_3`-level theorem built in
`ROADMAP.md §74`–`§75` (`Langlands/LubinTateTowerStepK3RootConnect.lean`,
`Langlands/LubinTateTowerStepK3Degree.lean`) is stated against the flat spelling, so using
`exists_eisenstein_tower_step_K_2`'s concrete witnesses there needs a transport.

This file provides it, via `Langlands/IntegralClosureTower.lean`'s `integralClosureRingEquiv`
(specialized at `R := ↥𝒪[K]`, `L := K_1 P`, `M := baseChangeSplittingField P₂`, which is exactly the nested/flat pair here)
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

set_option synthInstance.maxHeartbeats 1000000 in
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
    ∃ (P₃ : (O_K2 (K := K) P₂)[X]) (u₃ : (O_K2 (K := K) P₂)⟦X⟧),
      IsUnit u₃ ∧ P₃.IsDistinguishedAt (maximalIdeal _) ∧ P₃.natDegree = residueCard O := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := isScalarTower_R_K_1_K_2 (K := K) (P := P) (P₂ := P₂)
  obtain ⟨P₃n, u₃n, -, hu₃n, hP₃n, hdeg₃n, -, -, -⟩ :=
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

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **`exists_eisenstein_tower_step_K_2`'s richer output, transported to the flat `O_{K_2}`
spelling.** Supersedes `exists_eisenstein_tower_step_K_2_flat` for callers that also need the
generator `β'`, `Irreducible β'`, the Weierstrass equation `heq₃`, and `Associated (P₃.coeff 0) β'` —
exactly the data `Langlands/LubinTateTowerStepK3RootConnect.lean`'s `norm_lt_one_of_aeval_P₃_eq_zero`/
`eval_f_eq_of_aeval_P₃_eq_zero`/`exists_piTorsion_translate_of_aeval_P₃_eq_zero` and
`Langlands/LubinTateTowerStepK3Degree.lean`'s `finrank_K_3_eq_residueCard` take as explicit
hypotheses (`ROADMAP.md §76`).

The three previously-closed conjuncts transport exactly as in `exists_eisenstein_tower_step_K_2_flat`.
The three new pieces:

* `Irreducible β'` transports along the `RingEquiv` `e` via the general `Irreducible.map`
  (`[EquivLike F M N] [MulEquivClass F M N]`).
* `Associated (P₃.coeff 0) β'` transports via the general `Associated.map` (any `MonoidHomClass`),
  using `Polynomial.coeff_map` to identify `(P₃n.map e.toRingHom).coeff 0` with `e.toRingHom
  (P₃n.coeff 0)`.
* `heq₃` (the nested `shifted f ψ β'n = P₃n * u₃n`) transports via `Langlands.LubinTate.map_shifted`
  (`shifted`'s naturality in the target ring, `Langlands/LubinTateTowerStep.lean`) to `shifted f
  (e.toRingHom.comp ψ) (e.toRingHom β'n) = ↑(P₃n.map e.toRingHom) * PowerSeries.map e.toRingHom u₃n`
  (`Polynomial.map_mul`/`polynomial_map_coe` identify the right side with the `Polynomial` cast), then
  the composite-identification fact `e.toRingHom.comp ψ = towerHom2 hOK` rewrites the base-change map
  itself to the flat two-hop structure map. That composite fact is proved by composing both sides with
  the coercion into `K2P2 P₂` (injective: both `O_{K_2}` spellings are literally subalgebras of
  `K2P2 P₂`, so the coercion is `Subtype.coe_injective`, no `IsFractionRing` instance needed): on the
  nested side, `Subalgebra.algebraMap_apply` reduces the outer hop to a coercion, and
  `algebraMap_O_K_1_eq_comp_towerHom` (`Langlands/LubinTateTowerStepRootConnect.lean`) chained with
  `K_2.algebraMap_O_eq_comp_K_1` (same file) collapses the remaining two hops to `algebraMap O
  (K2P2 P₂)`; on the flat side, `algebraMap_O_K2P2_eq_comp_towerHom2`
  (`Langlands/LubinTateTowerStepK3RootConnect.lean`) gives the same identity for `towerHom2` directly,
  by that theorem's own statement. -/
theorem exists_eisenstein_tower_step_K_2_flat' (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
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
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  haveI := isScalarTower_R_K_1_K_2 (K := K) (P := P) (P₂ := P₂)
  obtain ⟨P₃n, u₃n, β'n, hu₃n, hP₃n, hdeg₃n, hβ'nirr, heq₃n, hassoc₃n⟩ :=
    exists_eisenstein_tower_step_K_2 hOK hπ hπnorm hf hu heq hPdist hPdeg hu₂ heq₂ hα'irr hP₂dist
      hassoc hdeg hα'norm hα'coe hirr hβroot hβfin
  set e := (integralClosureRingEquiv (R := ↥(ValuativeRel.valuation K).valuationSubring)
    (L := K_1 (K := K) P) (M := K2P2 (K := K) P₂)).symm with he
  set ψn := (algebraMap ↥(integralClosure
      ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      ↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (K2P2 (K := K) P₂))).comp (towerHom (K := K) hOK P) with hψn
  have hcompeq : e.toRingHom.comp ψn = towerHom2 (K := K) (P := P) P₂ hOK := by
    have hinj : Function.Injective
        (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) := Subtype.coe_injective
    apply RingHom.ext
    intro c
    apply hinj
    show (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) (e.toRingHom (ψn c)) =
      (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) (towerHom2 (K := K) (P := P) P₂ hOK c)
    have hlhs : (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) (e.toRingHom (ψn c)) =
        algebraMap O (K2P2 (K := K) P₂) c := by
      have he_val : ((e.toRingHom (ψn c) :
          ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K2P2 (K := K) P₂))) :
          K2P2 (K := K) P₂) = (ψn c : K2P2 (K := K) P₂) := rfl
      show ((e.toRingHom (ψn c) : ↥(integralClosure
          ↥(ValuativeRel.valuation K).valuationSubring (K2P2 (K := K) P₂))) :
          K2P2 (K := K) P₂) = algebraMap O (K2P2 (K := K) P₂) c
      rw [he_val]
      show ((algebraMap ↥(integralClosure
          ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
          ↥(integralClosure
            ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
            (K2P2 (K := K) P₂))) (towerHom (K := K) hOK P c) : K2P2 (K := K) P₂) =
        algebraMap O (K2P2 (K := K) P₂) c
      have h1 : (towerHom (K := K) hOK P c : K_1 (K := K) P) =
          algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
            (K_1 (K := K) P)) (K_1 (K := K) P) (towerHom (K := K) hOK P c) :=
        (Subalgebra.algebraMap_apply _ _).symm
      have h2 : algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P) (towerHom (K := K) hOK P c) =
          algebraMap O (K_1 (K := K) P) c :=
        (congrFun (algebraMap_O_K_1_eq_comp_towerHom (K := K) hOK) c).symm
      have h3 : algebraMap (K_1 (K := K) P) (K2P2 (K := K) P₂) (algebraMap O (K_1 (K := K) P) c) =
          algebraMap O (K2P2 (K := K) P₂) c :=
        (congrFun (K_2.algebraMap_O_eq_comp_K_1 (K := K) (P := P) hOK) c).symm
      rw [Subalgebra.coe_algebraMap, Subalgebra.algebraMap_eq]
      show algebraMap (K_1 (K := K) P) (K2P2 (K := K) P₂)
        ((towerHom (K := K) hOK P c : K_1 (K := K) P)) = algebraMap O (K2P2 (K := K) P₂) c
      rw [h1, h2]
      exact h3
    have hrhs : (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂))
        (towerHom2 (K := K) (P := P) P₂ hOK c) = algebraMap O (K2P2 (K := K) P₂) c :=
      (congrFun (algebraMap_O_K2P2_eq_comp_towerHom2 (K := K) (P₂ := P₂) hOK) c).symm
    rw [hlhs, hrhs]
  have hshift : PowerSeries.map e.toRingHom (shifted f ψn β'n) =
      PowerSeries.map e.toRingHom ((P₃n : _⟦X⟧) * u₃n) := by rw [heq₃n]
  rw [map_shifted f ψn β'n e.toRingHom, hcompeq, map_mul, ← polynomial_map_coe] at hshift
  refine ⟨P₃n.map e.toRingHom, PowerSeries.map e.toRingHom u₃n, e.toRingHom β'n,
    hu₃n.map (PowerSeries.map e.toRingHom), ?_, ?_, hβ'nirr.map e, hshift, ?_⟩
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
  · rw [Polynomial.coeff_map]
    exact hassoc₃n.map e.toRingHom

end LubinTate

end
