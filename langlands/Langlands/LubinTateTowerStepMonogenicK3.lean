/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepK3Degree
import Langlands.EisensteinMonogenicAbstract
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Monogenicity of `O_{K_3}` over `O_{K_2}` (flat spelling)

The `K_2 → K_3` analogue of `Langlands/LubinTateTowerStepMonogenic.lean`'s `adjoin_eq_integralClosure_
nextSplittingField`, one level up, against the *flat* `O_{K_2}` spelling (`ROADMAP.md §73`). Applies
`Langlands/EisensteinMonogenicAbstract.lean`'s `adjoin_eq_integralClosure_of_isEisensteinAt` directly
at `R := O_{K_2}`, `K := K2P2 P₂`, `L := K_3 P₃` — no `ValuativeRel (K2P2 P₂)` structure is built or
needed, continuing `LubinTateTowerStepMonogenic.lean`'s bare-Eisenstein route one level up.

## What is genuinely new relative to the `K_1 → K_2` template

`adjoin_eq_integralClosure_K_2` takes `hirr : Irreducible (P₂.map (algebraMap _ (K_1 P)))` as an
**explicit** hypothesis (supplied at that level by `exists_eisenstein_tower_step_K_1`'s own richer
conclusion). No `K_3`-level theorem in `Langlands/LubinTateTowerStepK3RootConnect.lean`/
`LubinTateTowerStepK3Degree.lean` carries an analogous hypothesis — `exists_eisenstein_tower_step_K_2`
(and its flat transport, `exists_eisenstein_tower_step_K_2_flat`) does not return it either. This file
**derives** it instead, from data every `K_3`-level generic theorem already carries (`hβ'irr`,
`hP₃dist`, `hassoc`, `hdeg`), via the same `Polynomial.irreducible_map_of_isWeaklyEisensteinAt_
associated` step `exists_eisenstein_tower_step_K_1`'s own proof uses to establish its analogous
`hirr` — so no new hypothesis needs threading through the ambient section, and no external
`exists_eisenstein_tower_step_K_2`-style existence witness is needed for irreducibility specifically
(only for `γ`'s existence, which `hγfin`/`hγroot` still take as given, per `finrank_K_3_eq_residueCard`'s
own established scope decision).

`[IsIntegrallyClosed (O_K2 P₂)]` resolves automatically (`integralClosure.isIntegrallyClosed`, since
the flat `O_K2 P₂` *is* literally `↥(integralClosure ↥𝒪[K] (K2P2 P₂))`) — checked directly, not
assumed, by the theorem below type-checking with no `[IsIntegrallyClosed (O_K2 P₂)]` hypothesis in its
signature.

## Main result

* `adjoin_eq_integralClosure_K_3` : **`Algebra.adjoin O_{K_2} {γ} = integralClosure O_{K_2} (K_3 P₃)`**
  — monogenicity of `O_{K_3}` over `O_{K_2}` (flat spelling).
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
  (P₃ : (O_K2 (K := K) P₂)[X])

/-- **`Algebra.adjoin O_{K_2} {γ} = integralClosure O_{K_2} (K_3 P₃)`** — monogenicity of `O_{K_3}`
over `O_{K_2}` (flat spelling), for `γ` any root of `P₃`'s image generating `K_3` over `K2P2 P₂`.
Mirrors `adjoin_eq_integralClosure_K_2` exactly, one level up: `IsIntegral O_{K_2} γ` witnessed by
`P₃`; `minpoly (K2P2 P₂) γ = P₃.map (algebraMap O_{K_2} (K2P2 P₂))` (`hirr` derived here, not taken as
hypothesis — see the module docstring); `minpoly.isIntegrallyClosed_eq_field_fractions'` plus
injectivity of `Polynomial.map` along `algebraMap O_{K_2} (K2P2 P₂)` (`IsFractionRing`) forces
`minpoly O_{K_2} γ = P₃` on the nose; Eisenstein-ness transports from `P₃`'s own data; `hgen` from
`finrank_K_3_eq_residueCard`. `EisensteinMonogenicAbstract`'s `adjoin_eq_integralClosure_of_
isEisensteinAt` closes the rest. -/
theorem adjoin_eq_integralClosure_K_3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
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
      (K' := K2P2 (K := K) P₂) P₃)] :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    Algebra.adjoin (O_K2 (K := K) P₂)
        ({γ} : Set (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) =
      integralClosure (O_K2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  haveI := finiteDimensional_K_K_2 (K := K) (P := P) P₂
  -- `IsIntegral O_{K_2} γ`, witnessed directly by `P₃`.
  have hγint : IsIntegral (O_K2 (K := K) P₂) γ := by
    refine ⟨P₃, hP₃dist.monic, ?_⟩
    have h1 : Polynomial.aeval γ (Polynomial.map
        (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) P₃) = 0 := hγroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  have hpos : 0 < P₃.natDegree := hdeg
  -- `P₃`'s image over `K2P2 P₂` is irreducible: derived, not taken as hypothesis (see module
  -- docstring).
  have hirr : Irreducible (P₃.map (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂))) :=
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hβ'irr hP₃dist.monic
      hP₃dist.toIsWeaklyEisensteinAt hpos hassoc
  -- `minpoly (K2P2 P₂) γ = P₃.map (algebraMap O_{K_2} (K2P2 P₂))`.
  have hminK2 : minpoly (K2P2 (K := K) P₂) γ =
      P₃.map (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) :=
    (minpoly.eq_of_irreducible_of_monic hirr hγroot (hP₃dist.monic.map _)).symm
  -- `minpoly O_{K_2} γ = P₃`, on the nose.
  have hminR : minpoly (O_K2 (K := K) P₂) γ = P₃ := by
    have hfrac : minpoly (K2P2 (K := K) P₂) γ = Polynomial.map
        (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂))
        (minpoly (O_K2 (K := K) P₂) γ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' (K2P2 (K := K) P₂) hγint
    have hinj : Function.Injective (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) :=
      IsFractionRing.injective _ (K2P2 (K := K) P₂)
    exact (Polynomial.map_injective _ hinj (hfrac ▸ hminK2))
  -- Eisenstein-ness transports from `P₃` onto `minpoly O_{K_2} γ`.
  have hEisP₃ : P₃.IsEisensteinAt (maximalIdeal (O_K2 (K := K) P₂)) :=
    hP₃dist.monic.isEisensteinAt_of_mem_of_notMem
      (maximalIdeal.isMaximal (O_K2 (K := K) P₂)).ne_top
      (fun {n} hn => hP₃dist.toIsWeaklyEisensteinAt.mem hn)
      (not_mem_sq_maximalIdeal_of_associated hβ'irr hassoc)
  have hIdeq : Submodule.span (O_K2 (K := K) P₂) ({β'} : Set (O_K2 (K := K) P₂)) =
      maximalIdeal (O_K2 (K := K) P₂) := by
    rw [Ideal.submodule_span_eq]
    exact (Irreducible.maximalIdeal_eq hβ'irr).symm
  have hEis : (minpoly (O_K2 (K := K) P₂) γ).IsEisensteinAt
      (Submodule.span (O_K2 (K := K) P₂) ({β'} : Set (O_K2 (K := K) P₂))) := by
    rw [hminR, hIdeq]
    exact hEisP₃
  -- `hgen`.
  have hxK : IsIntegral (K2P2 (K := K) P₂) γ := hγint.tower_top
  have hgen : (minpoly (K2P2 (K := K) P₂) γ).natDegree =
      Module.finrank (K2P2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) :=
    (IntermediateField.adjoin.finrank hxK).symm.trans (hγfin.trans
      (finrank_K_3_eq_residueCard (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg
        β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγfin).symm)
  exact adjoin_eq_integralClosure_of_isEisensteinAt hβ'irr hγint hEis hgen

end LubinTate

end
