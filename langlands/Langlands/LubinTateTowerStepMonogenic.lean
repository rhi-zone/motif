/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepDegree
import Langlands.EisensteinMonogenicAbstract
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Monogenicity of `O_{K_2}` over `O_{K_1}`

`ROADMAP.md`'s `§56` ("Gap 2"): `Langlands/TowerBundleResidueField.lean`'s
`_of_valuationSubring` engine cannot be reused for the `K_1 → K_2` hop, because its `letI` chain
rebuilds a *second, non-defeq* `NontriviallyNormedField (K_1 P)` instance (via `Valued.mk'`), distinct
from the one already registered (`K_1.instNontriviallyNormedField`, the `spectralNorm` route
`K_2`'s own construction is built against). This file sidesteps that formalism entirely, applying
`Langlands/EisensteinMonogenicAbstract.lean`'s bare-Eisenstein monogenicity theorem directly at
`R := O_{K_1}`, `K := K_1 P`, `L := K_2 P₂` — no `ValuativeRel`/`NormedField` structure on `K_1 P` is
built or required.

**Checked directly (not assumed) that this level does *not* reproduce the `O → K_2` instance
diamond** `Langlands/LubinTateTowerStepSplittingField.lean`'s `K_2.instAlgebraO` docstring warns
about: `O_{K_1} := ↥(integralClosure ↥𝒪[K] (K_1 P))` is, unlike the base `O`, syntactically a
`Subalgebra ↥𝒪[K] (K_1 P)`-coerced type, so Mathlib's generic `Subalgebra.instSMulSubtypeMem` (`the
action by a subalgebra is the action by the underlying algebra`) already supplies `Algebra O_{K_1}
(K_2 P₂)` and `IsScalarTower O_{K_1} (K_1 P) (K_2 P₂)` via ordinary instance search, *and* this
instance agrees with the honest composite `algebraMap (K_1 P) (K_2 P₂) ∘ algebraMap O_{K_1} (K_1 P)`
by `rfl` — confirmed by direct `rfl`/`infer_instance` test before relying on it. (The `O → K_2` case
needed a hand-built `K_2.instAlgebraO` precisely because `O` is *not* itself a subalgebra of `K_1 P`
— it reaches `K_1 P` via a longer, unrelated path through `K` — so no such generic instance applies
there.) No custom `Algebra`/`IsScalarTower` instance is built in this file as a result.

## The generator `β`, its minimal polynomial, and its Eisenstein-ness

`Langlands/LubinTateTowerStepDegree.lean`'s `adjoin_root_eq_top_K_2` already supplies a root `β` of
`P₂`'s image generating `K_2` over `K_1 P` (`(K_1 P)⟮β⟯ = ⊤`). This file identifies
`minpoly O_{K_1} β = P₂` *exactly* (not merely up to associates): `minpoly.isIntegrallyClosed_eq_
field_fractions'` identifies `minpoly (K_1 P) β` with the base change of `minpoly O_{K_1} β`, and
`minpoly.eq_of_irreducible_of_monic` identifies `minpoly (K_1 P) β` with `P₂`'s own image (`P₂` monic,
its image irreducible by construction, `β` a root) — since `algebraMap O_{K_1} (K_1 P)` is injective
(`IsFractionRing`), the two base-changed polynomials being equal as elements of `(K_1 P)[X]`, and
`Polynomial.map` being injective along an injective ring homomorphism, forces the underlying
polynomials `minpoly O_{K_1} β` and `P₂` themselves to be equal — no associates/`natDegree`-comparison
argument needed. `P₂` being Eisenstein at `𝔪_{O_{K_1}}` then transports directly onto `minpoly O_{K_1}
β`.

## Main result

* `adjoin_eq_integralClosure_K_2` : **`Algebra.adjoin O_{K_1} {β} = integralClosure O_{K_1} (K_2 P₂)`**
  — monogenicity of `O_{K_2}` over `O_{K_1}`. This is a complete, unconditional (given the ambient
  hypothesis package) result, obtained with no `ValuativeRel (K_1 P)` instance anywhere.

## What does not close here: `IsLocalRing O_{K_2}`

Residue-field preservation needs `IsLocalRing.residueFieldEquivOfAdjoinSingleton`, which requires
`[IsLocalRing B]` for `B := integralClosure O_{K_1} (K_2 P₂)` — a hypothesis `IsLocalRing.residueField_
map_surjective_of_adjoin_singleton`'s signature bakes in (`ResidueField B` is not even well-typed
without it). At the `K → K_1` level this instance came for free from `IsDiscreteValuationRing`
(`Langlands/MonogenicIntegralClosure.lean`'s `isDiscreteValuationRing_integralClosure`), itself built
from `ValuationSubring.isDiscreteValuationRing_of_comap_eq` — which needs a `ValuativeRel (K_1 P)`
instance on the *base* field of the integral closure, i.e. exactly the diamond this file avoids. No
substitute construction of `IsLocalRing O_{K_2}` from monogenicity alone (e.g. via the classical "an
integral extension of a local ring, local mod the base's maximal ideal, is itself local" argument —
`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` for the lying-over half, plus an
Eisenstein-nilpotence argument for the residual quotient) is built in this pass: it is a genuine,
general, reusable commutative-algebra lemma not identified by `ROADMAP.md §56`'s scoping and not yet
attempted. See `ROADMAP.md` for the precise handoff.
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
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]}
  {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X]}

/-- **`Algebra.adjoin O_{K_1} {β} = integralClosure O_{K_1} (K_2 P₂)`** — monogenicity of `O_{K_2}`
over `O_{K_1}`, for `β` any root of `P₂`'s image generating `K_2` over `K_1 P`
(`adjoin_root_eq_top_K_2`'s hypothesis package, reused verbatim, plus `hβfin` matching
`finrank_K_2_eq_residueCard`'s own extra hypothesis and `hirr` naming `exists_eisenstein_tower_step_K_1`'s
already-established irreducibility of `P₂`'s image). No `ValuativeRel (K_1 P)` instance is built or
needed — `Algebra O_{K_1} (K_2 P₂)` and `IsScalarTower O_{K_1} (K_1 P) (K_2 P₂)` resolve by ordinary
instance search (`Subalgebra.instSMulSubtypeMem`), confirmed to agree with the honest composite.

Proof: `IsIntegral O_{K_1} β` is witnessed directly by `P₂` itself (`hβroot` transported along
`Polynomial.aeval_map_algebraMap`, valid since `IsScalarTower O_{K_1} (K_1 P) (K_2 P₂)` holds).
`minpoly (K_1 P) β = P₂.map (algebraMap O_{K_1} (K_1 P))` by `minpoly.eq_of_irreducible_of_monic`
(using `hirr`, `hβroot`, `hP₂dist.monic`); combined with `minpoly.isIntegrallyClosed_eq_field_
fractions'` (`minpoly (K_1 P) β = (minpoly O_{K_1} β).map (algebraMap O_{K_1} (K_1 P))`) and
injectivity of `Polynomial.map` along the injective `algebraMap O_{K_1} (K_1 P)` (`IsFractionRing`),
this forces `minpoly O_{K_1} β = P₂` on the nose. `P₂`'s Eisenstein-ness at `𝔪_{O_{K_1}}` (from
`hP₂dist`/`hassoc`/`hα'irr`, the same assembly `Langlands/LubinTateTowerStep.lean`'s
`isEisensteinAt_shifted` uses) transports along this equality onto `minpoly O_{K_1} β`, and `hgen`
(`(minpoly (K_1 P) β).natDegree = Module.finrank (K_1 P) (K_2 P₂)`) from `IntermediateField.adjoin.
finrank`, `hβfin`, and `finrank_K_2_eq_residueCard`. `EisensteinMonogenicAbstract`'s
`adjoin_eq_integralClosure_of_isEisensteinAt` closes the rest. -/
theorem adjoin_eq_integralClosure_K_2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
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
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)] :
    Algebra.adjoin ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        ({β} : Set (K_2 (K' := K_1 (K := K) P) P₂)) =
      integralClosure ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (K_2 (K' := K_1 (K := K) P) P₂) := by
  -- `IsIntegral O_{K_1} β`, witnessed directly by `P₂`.
  have hβint : IsIntegral ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) β := by
    refine ⟨P₂, hP₂dist.monic, ?_⟩
    have h1 : Polynomial.aeval β (Polynomial.map
        (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P)) P₂) = 0 := hβroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  -- `minpoly (K_1 P) β = P₂.map (algebraMap O_{K_1} (K_1 P))`.
  have hminK1 : minpoly (K_1 (K := K) P) β = P₂.map
      (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (K_1 (K := K) P)) :=
    (minpoly.eq_of_irreducible_of_monic hirr hβroot (hP₂dist.monic.map _)).symm
  -- `minpoly O_{K_1} β = P₂`, on the nose.
  have hminR : minpoly ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) β = P₂ := by
    have hfrac : minpoly (K_1 (K := K) P) β = Polynomial.map
        (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P))
        (minpoly ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) β) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' (K_1 (K := K) P) hβint
    have hinj : Function.Injective (algebraMap
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (K_1 (K := K) P)) :=
      IsFractionRing.injective _ (K_1 (K := K) P)
    exact (Polynomial.map_injective _ hinj (hfrac ▸ hminK1))
  -- Eisenstein-ness transports from `P₂` onto `minpoly O_{K_1} β`.
  have hEisP₂ : P₂.IsEisensteinAt (maximalIdeal
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))) :=
    hP₂dist.monic.isEisensteinAt_of_mem_of_notMem
      (maximalIdeal.isMaximal ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P))).ne_top
      (fun {n} hn => hP₂dist.toIsWeaklyEisensteinAt.mem hn)
      (not_mem_sq_maximalIdeal_of_associated hα'irr hassoc)
  have hIdeq : Submodule.span
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      ({α'} : Set ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P))) =
      maximalIdeal ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) := by
    rw [Ideal.submodule_span_eq]
    exact (Irreducible.maximalIdeal_eq hα'irr).symm
  have hEis : (minpoly ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) β).IsEisensteinAt (Submodule.span
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      ({α'} : Set ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)))) := by
    rw [hminR, hIdeq]
    exact hEisP₂
  -- `hgen`.
  have hxK : IsIntegral (K_1 (K := K) P) β := hβint.tower_top
  have hgen : (minpoly (K_1 (K := K) P) β).natDegree =
      Module.finrank (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂) :=
    (IntermediateField.adjoin.finrank hxK).symm.trans (hβfin.trans
      (finrank_K_2_eq_residueCard (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβfin).symm)
  exact adjoin_eq_integralClosure_of_isEisensteinAt hα'irr hβint hEis hgen

end LubinTate

end
