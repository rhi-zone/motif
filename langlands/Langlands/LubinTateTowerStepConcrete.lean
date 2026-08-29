/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.TotallyRamifiedUniformizer
import Langlands.LubinTateResidueFieldPreservation
import Langlands.LubinTateSplittingFieldDVR
import Langlands.LubinTateTowerStep

/-!
# Instantiating the general tower step at the concrete moving base `O_{K_1}`

`Langlands/LubinTateTowerStep.lean` proves the Eisenstein-existence half of one inductive
Lubin-Tate tower step over an *arbitrary* moving base `O'`, and its module docstring records the
remaining obstruction: constructing `O'` concretely as `O_{K_1}` together with `ψ : O →+* O'` local
and `α' : O'` irreducible. `Langlands/TotallyRamifiedResidueField.lean` and
`Langlands/TotallyRamifiedUniformizer.lean` closed the two mathematical inputs
(residue-field preservation, and that the level-1 generator is a genuine uniformizer). This file
performs the substitution.

`O_{K_1}` is taken in the `integralClosure ↥𝒪[K] (K_1 P)` spelling — the one carrying
`IsDomain`/`IsDiscreteValuationRing`/`IsFractionRing … (K_1 P)`/`IsLocalHom (algebraMap …)`
instances (`Langlands/MonogenicIntegralClosure.lean`), all of which resolve by `inferInstance`. Only
`IsAdicComplete` had to be transported from the
`(NormedField.valuation (K := K_1 P)).valuationSubring` spelling
(`Langlands/LubinTateSplittingFieldDVR.lean`), which is done here.

## Main results

* `NormedField.isAdicComplete_integralClosure_of_finiteDimensional` and
  `LubinTate.isAdicComplete_integralClosure_K_1` : `IsAdicComplete` at `O_{K_1}` in the
  `integralClosure` spelling, transported along `LocalField.valuationSubring_eq_of_comap_eq`.
* `LubinTate.toValuationSubring` : the ring homomorphism `O →+* ↥𝒪[K]` cut out by `hOK`, and
  `LubinTate.isLocalHom_toValuationSubring` : it is local, using that a nonunit of the discrete
  valuation ring `O` is divisible by `π`, whose image has norm `< 1` (`hπnorm`).
* `LubinTate.towerHom` / `LubinTate.isLocalHom_towerHom` : the composite `ψ : O →+* O_{K_1}`, local.
* `LubinTate.irreducible_uniformizer_K_1` : the level-1 generator `α`, viewed in `O_{K_1}`, is
  irreducible there — the `hα'` input of `LubinTate.exists_isWeierstrassFactorization_shifted`.
* `LubinTate.exists_eisenstein_tower_step_K_1` : **the tower step, instantiated.** There is a monic
  degree-`q` polynomial `P₂` over `O_{K_1}`, Eisenstein at `𝔪_{O_{K_1}}`, with
  `shifted f ψ α = P₂ * u₂`, whose image over `K_1 P` is irreducible.
* `LubinTate.baseChangeSplittingField` : the splitting field of that image — the level-2 Lubin-Tate extension.
* `LubinTate.finrank_adjoin_root_K_2_eq_residueCard` : a root `β` of `P₂`'s image in `baseChangeSplittingField` generates
  a degree-`q` extension of `K_1 P`, `Module.finrank (K_1 P) (K_1 P)⟮β⟯ = residueCard O`.
-/

noncomputable section

open IsLocalRing ValuativeRel Polynomial PowerSeries

open scoped IntermediateField

/-! ## `IsAdicComplete` in the `integralClosure` spelling -/

/-- **`↥(integralClosure ↥𝒪[K] L)` is `(maximalIdeal)`-adically complete.** Same hypotheses as
`NormedField.isAdicComplete_valuationSubring_of_finiteDimensional`; the conclusion is transported
along `LocalField.valuationSubring_eq_of_comap_eq`, which identifies
`(NormedField.valuation (K := L)).valuationSubring` with
`LocalField.integralClosureValuationSubring ↥𝒪[K] L`, whose coercion is definitionally
`↥(integralClosure ↥𝒪[K] L)`. -/
theorem NormedField.isAdicComplete_integralClosure_of_finiteDimensional
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
    [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
    [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hnorm : ∀ x : K, ‖algebraMap K L x‖ = ‖x‖) :
    IsAdicComplete
      (maximalIdeal ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring L))
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring L) := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hcomapA : (NormedField.valuation (K := L)).valuationSubring.comap (algebraMap K L) =
      (ValuativeRel.valuation K).valuationSubring := by
    have hsub : (ValuativeRel.valuation K).valuationSubring =
        (NormedField.valuation (K := K)).valuationSubring :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mp (ValuativeRel.isEquiv _ _)
    rw [hsub]
    ext x
    have hnn : ‖algebraMap K L x‖₊ = ‖x‖₊ :=
      NNReal.coe_injective (by rw [coe_nnnorm, coe_nnnorm, hnorm])
    rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
      NormedField.valuation_apply, hnn]
  have hcomapI : (LocalField.integralClosureValuationSubring
      ↥(ValuativeRel.valuation K).valuationSubring L).comap (algebraMap K L) =
      (ValuativeRel.valuation K).valuationSubring :=
    LocalField.comap_integralClosureValuationSubring K L
  have hAeq : (NormedField.valuation (K := L)).valuationSubring =
      LocalField.integralClosureValuationSubring ↥(ValuativeRel.valuation K).valuationSubring L :=
    LocalField.valuationSubring_eq_of_comap_eq K hcomapA hcomapI
  have h := NormedField.isAdicComplete_valuationSubring_of_finiteDimensional (K := K) (L := L) hnorm
  rw [hAeq] at h
  exact h

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Algebra O K] [IsFractionRing O K]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`O_{K_1} := integralClosure ↥𝒪[K] (K_1 P)` is `(maximalIdeal)`-adically complete.** Applies
`NormedField.isAdicComplete_integralClosure_of_finiteDimensional`, with `hnorm` discharged by
`spectralNorm_extends` via `K_1.norm_eq_spectralNorm`, exactly as
`isAdicComplete_valuationSubring_K_1` does for the `valuationSubring` spelling. -/
theorem isAdicComplete_integralClosure_K_1
    [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
    (P : O[X]) [Algebra.IsSeparable K (K_1 (K := K) P)] :
    IsAdicComplete
      (maximalIdeal ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)))
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)) :=
  NormedField.isAdicComplete_integralClosure_of_finiteDimensional
    (K := K) (L := K_1 (K := K) P) fun x => by
      rw [K_1.norm_eq_spectralNorm, spectralNorm_extends]

/-! ## The structure map `ψ : O →+* O_{K_1}` -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`O`'s image in `K` lands in `𝒪[K]`**, packaged as a ring homomorphism — the first half of the
tower structure map `ψ`. This is exactly what `hOK` says. -/
def toValuationSubring (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    O →+* ↥(ValuativeRel.valuation K).valuationSubring :=
  (algebraMap O K).codRestrict (ValuativeRel.valuation K).valuationSubring fun c =>
    (LocalField.mem_valuationSubring_iff_norm_le_one K (algebraMap O K c)).mpr (hOK c)

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] [IsFractionRing O K] in
@[simp]
theorem coe_toValuationSubring (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (c : O) :
    ((toValuationSubring (K := K) hOK c : ↥(ValuativeRel.valuation K).valuationSubring) : K) =
      algebraMap O K c := rfl

omit [Finite (ResidueField O)] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] [IsFractionRing O K] in
/-- **`toValuationSubring hOK` is a local homomorphism.** A nonunit of the discrete valuation ring
`O` lies in `𝔪_O = (π)`, so its image has norm at most `‖algebraMap O K π‖ < 1` (`hπnorm`), hence
lies in `𝔪_{𝒪[K]}` (`LocalField.mem_maximalIdeal_iff_norm_lt_one`) and is a nonunit there. This is
the contrapositive of what `IsLocalHom` asks. -/
theorem isLocalHom_toValuationSubring (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) :
    IsLocalHom (toValuationSubring (K := K) hOK) := by
  constructor
  intro c hc
  by_contra hcu
  have hcmem : c ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hcu
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hcmem
  obtain ⟨d, hd⟩ := hcmem
  have hnorm : ‖algebraMap O K c‖ < 1 := by
    rw [hd, map_mul, norm_mul]
    calc ‖algebraMap O K π‖ * ‖algebraMap O K d‖ ≤ ‖algebraMap O K π‖ * 1 :=
          mul_le_mul_of_nonneg_left (hOK d) (norm_nonneg _)
      _ = ‖algebraMap O K π‖ := mul_one _
      _ < 1 := hπnorm
  exact ((IsLocalRing.mem_maximalIdeal _).mp
    ((LocalField.mem_maximalIdeal_iff_norm_lt_one K _).mpr hnorm)) hc

/-- **The tower structure map `ψ : O →+* O_{K_1}`**, the composite `O → 𝒪[K] → O_{K_1}`. -/
def towerHom (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (P : O[X]) :
    O →+* ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)) :=
  (algebraMap ↥(ValuativeRel.valuation K).valuationSubring
    ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P))).comp (toValuationSubring hOK)

omit [Finite (ResidueField O)] in
omit [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] [IsFractionRing O K] in
/-- **`towerHom` is local**, being the composite of the local `toValuationSubring hOK`
(`isLocalHom_toValuationSubring`) and the local `algebraMap ↥𝒪[K] → 𝒪_{K_1}`
(`LocalField.isLocalHom_algebraMap_integralClosure`, `Langlands/MonogenicIntegralClosure.lean`). -/
theorem isLocalHom_towerHom (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) (P : O[X]) :
    IsLocalHom (towerHom (K := K) hOK P) := by
  haveI := isLocalHom_toValuationSubring (K := K) hOK hπ hπnorm
  exact RingHom.isLocalHom_comp _ _

/-! ## The level-1 generator is a uniformizer of `O_{K_1}` -/

variable {π : O} {f : O⟦X⟧} {P : O[X]} {u : O⟦X⟧}

omit [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] in
/-- **`hgen` at `K_1`**: any root of `Qk := P.divX.map (algebraMap O K)` in `K_1 P` has minimal
polynomial of degree `Module.finrank K (K_1 P)`. Combines `minpoly_eq_divX_map_K_1` with
`finrank_K_1_eq_residueCard_sub_one`. -/
theorem natDegree_minpoly_eq_finrank_K_1
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1)
    (hf : IsLubinTatePoly π (residueCard O) f) (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    {α : K_1 (K := K) P} (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0) :
    (minpoly K α).natDegree = Module.finrank K (K_1 (K := K) P) := by
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, -, -, -⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2
  rw [minpoly_eq_divX_map_K_1 hπ hf hu heq hPdist hPdeg hα, hQmonic.natDegree_map,
    Polynomial.natDegree_divX_eq_natDegree_tsub_one, hPdeg,
    finrank_K_1_eq_residueCard_sub_one hOK hπ hπnorm hf hu heq hPdist hPdeg]

omit [(NormedField.valuation (K := K)).Compatible]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] in
/-- **`hram` at `K_1`**: the total-ramification identity in the exact form
`LocalField.irreducible_of_isUniformizer` consumes. -/
theorem norm_eq_spectralNorm_pow_natDegree_K_1
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring}
    (hϖnorm : ‖(ϖ : K)‖ = ‖algebraMap O K π‖)
    {α : K_1 (K := K) P} (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0) :
    ‖(ϖ : K)‖ = spectralNorm K (K_1 (K := K) P) α ^ (minpoly K α).natDegree := by
  rw [hϖnorm, ← spectralNorm_pow_natDegree_minpoly_K_1 hOK hπ hf hu heq hPdist hPdeg hα]

/-- **The level-1 generator, viewed in `O_{K_1}`, is irreducible there** — i.e. it is a uniformizer
of `O_{K_1}`. This is `LocalField.irreducible_of_isUniformizer`
(`Langlands/TotallyRamifiedUniformizer.lean`) with its `hram`/`hgen` discharged at `K_1` by the two
theorems above; it is the `hα'` input of
`LubinTate.exists_isWeierstrassFactorization_shifted`. -/
theorem exists_irreducible_uniformizer_K_1
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1)
    (hf : IsLubinTatePoly π (residueCard O) f) (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} (hϖ : Irreducible ϖ)
    (hϖnorm : ‖(ϖ : K)‖ = ‖algebraMap O K π‖)
    {α : K_1 (K := K) P} (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0)
    [Algebra.IsSeparable K (K_1 (K := K) P)] :
    ∃ α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)),
      Irreducible α' ∧ (α' : K_1 (K := K) P) = α := by
  have hram := norm_eq_spectralNorm_pow_natDegree_K_1 hOK hπ hf hu heq hPdist hPdeg hϖnorm hα
  have hgen := natDegree_minpoly_eq_finrank_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg hα
  have hαint : IsIntegral ↥(ValuativeRel.valuation K).valuationSubring α :=
    LocalField.isIntegral_of_isUniformizer K hϖ hram
  exact ⟨⟨α, hαint⟩, LocalField.irreducible_of_isUniformizer K hϖ hram hgen hαint, rfl⟩

/-! ## The tower step, instantiated -/

/-- **The general tower step of `Langlands/LubinTateTowerStep.lean`, instantiated at the concrete
moving base `O_{K_1}`.** Every hypothesis of that file's `TowerStep` section is discharged here:
`O' := ↥(integralClosure ↥𝒪[K] (K_1 P))` is an `IsDomain`/`IsDiscreteValuationRing`
(`Langlands/MonogenicIntegralClosure.lean`, by `inferInstance`), `IsAdicComplete` by
`isAdicComplete_integralClosure_K_1`, `ψ := towerHom hOK P` is local by `isLocalHom_towerHom`, and
`α'` is irreducible by `exists_irreducible_uniformizer_K_1`.

The conclusion is the level-2 Eisenstein polynomial: a monic degree-`q` `P₂` over `O_{K_1}`,
Weierstrass factor of `f(X) - α'`, whose image over `K_1 P` is irreducible. The raw
`IsDistinguishedAt`/`Associated (P₂.coeff 0) α'` data is also returned (not just the derived
`Monic`/`Irreducible` facts) so downstream root-membership arguments connecting `eval_map_towerHom`
to the roots of `P₂` can rebuild `P₂`'s Eisenstein-shape norm bound without re-invoking
`exists_isWeierstrassFactorization_shifted` at a possibly-different existential witness. -/
theorem exists_eisenstein_tower_step_K_1
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1)
    (hf : IsLubinTatePoly π (residueCard O) f) (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} (hϖ : Irreducible ϖ)
    (hϖnorm : ‖(ϖ : K)‖ = ‖algebraMap O K π‖)
    {α : K_1 (K := K) P} (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0)
    [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
    [Algebra.IsSeparable K (K_1 (K := K) P)] :
    ∃ (α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))
      (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)))[X])
      (u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)))⟦X⟧),
      (α' : K_1 (K := K) P) = α ∧ IsUnit u₂ ∧
        shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂ ∧
        P₂.Monic ∧ P₂.natDegree = residueCard O ∧
        Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))) ∧
        P₂.IsDistinguishedAt (maximalIdeal _) ∧ Associated (P₂.coeff 0) α' := by
  haveI := isAdicComplete_integralClosure_K_1 (K := K) P
  haveI := isLocalHom_towerHom (K := K) hOK hπ hπnorm P
  obtain ⟨α', hα'irr, hα'coe⟩ :=
    exists_irreducible_uniformizer_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg hϖ hϖnorm hα
  obtain ⟨P₂, u₂, hP₂dist, hu₂, heq₂, hdeg₂, hassoc₂⟩ :=
    exists_isWeierstrassFactorization_shifted hf (towerHom (K := K) hOK P) hα'irr
  have hpos : 0 < P₂.natDegree := by
    rw [hdeg₂]; exact lt_of_lt_of_le (by norm_num) two_le_residueCard
  exact ⟨α', P₂, u₂, hα'coe, hu₂, heq₂, hP₂dist.monic, hdeg₂,
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hα'irr hP₂dist.monic
      hP₂dist.toIsWeaklyEisensteinAt hpos hassoc₂, hP₂dist, hassoc₂⟩

/-- **`baseChangeSplittingField`, the generic one-step splitting-field combinator.** Given a base ring
`O'`, a field `K'` with `[Algebra O' K']`, and a polynomial `P₂ : O'[X]`, this is the splitting
field of `P₂`'s image over `K'` — genuinely generic in `O'`/`K'`, not specific to any one tower
level. It is applied throughout this codebase at every tower step: at the literal second level
(`baseChangeSplittingField (K' := K_1 P) P₂`, producing the level-2 Lubin-Tate extension over `K_1 P`'s
image of the level-2 Eisenstein polynomial `P₂` from `exists_eisenstein_tower_step_K_1`), to build
`K_3` (`Langlands/LubinTateTowerStepConcreteK3.lean`, `K' := K_2 P₂`), and inside the fully generic
`Level.next` (`Langlands/LubinTateTowerStepLevelGeneric.lean`) at an arbitrary prior level's field —
hence the name, reflecting its genuinely generic role rather than "the second level" specifically.
Mirrors `LubinTate.K_1`'s own definition
(`Langlands/LubinTateSplittingField.lean`) at the concrete `K' := K` instantiation, with no `divX`
peel: `0` is not a root of `f(X) - α'`, so `P₂` itself, not `P₂.divX`, is the Eisenstein
polynomial there. -/
def baseChangeSplittingField {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K'] (P₂ : O'[X]) : Type _ :=
  (P₂.map (algebraMap O' K')).SplittingField

instance baseChangeSplittingField.instField {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₂ : O'[X]) : Field (baseChangeSplittingField (K' := K') P₂) :=
  inferInstanceAs (Field (P₂.map (algebraMap O' K')).SplittingField)

instance baseChangeSplittingField.instAlgebra {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₂ : O'[X]) : Algebra K' (baseChangeSplittingField (K' := K') P₂) :=
  inferInstanceAs (Algebra K' (P₂.map (algebraMap O' K')).SplittingField)

instance baseChangeSplittingField.instIsSplittingField {O' : Type*} [CommRing O'] {K' : Type*} [Field K']
    [Algebra O' K'] (P₂ : O'[X]) :
    Polynomial.IsSplittingField K' (baseChangeSplittingField (K' := K') P₂) (P₂.map (algebraMap O' K')) :=
  inferInstanceAs (Polynomial.IsSplittingField K' (P₂.map (algebraMap O' K')).SplittingField
    (P₂.map (algebraMap O' K')))

/-- **The level-2 extension has degree exactly `q = residueCard O` over `K_1 P`** — the first
genuine tower step past the base level. A root `β` of `P₂`'s image exists in `baseChangeSplittingField` (the image
splits there and has positive degree), and that image is monic and irreducible, hence is `β`'s
minimal polynomial, so `Module.finrank (K_1 P) (K_1 P)⟮β⟯ = P₂.natDegree = residueCard O`. -/
theorem exists_finrank_adjoin_eq_residueCard_K_2
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1)
    (hf : IsLubinTatePoly π (residueCard O) f) (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} (hϖ : Irreducible ϖ)
    (hϖnorm : ‖(ϖ : K)‖ = ‖algebraMap O K π‖)
    {α : K_1 (K := K) P} (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0)
    [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
    [Algebra.IsSeparable K (K_1 (K := K) P)] :
    ∃ (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)))[X]),
      P₂.natDegree = residueCard O ∧
      ∃ β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂,
        Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O := by
  obtain ⟨α', P₂, u₂, -, -, -, hmonic, hdeg, hirr, -, -⟩ :=
    exists_eisenstein_tower_step_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg hϖ hϖnorm hα
  refine ⟨P₂, hdeg, ?_⟩
  set P₂k := P₂.map (algebraMap _ (K_1 (K := K) P)) with hP₂k
  have hP₂kmonic : P₂k.Monic := hmonic.map _
  have hP₂kdeg : P₂k.natDegree = residueCard O := by rw [hP₂k, hmonic.natDegree_map, hdeg]
  have hdegne : (P₂k.map (algebraMap (K_1 (K := K) P)
      (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))).degree ≠ 0 := by
    refine (Polynomial.natDegree_pos_iff_degree_pos.mp ?_).ne'
    rw [hP₂kmonic.natDegree_map, hP₂kdeg]
    exact lt_of_lt_of_le (by norm_num) two_le_residueCard
  obtain ⟨β, hβ⟩ :=
    (Polynomial.IsSplittingField.splits' (K := K_1 (K := K) P)
      (L := baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (f := P₂k)).exists_eval_eq_zero hdegne
  rw [Polynomial.eval_map, ← Polynomial.aeval_def] at hβ
  have hβroot : Polynomial.aeval β P₂k = 0 := hβ
  have hβint : IsIntegral (K_1 (K := K) P) β := ⟨P₂k, hP₂kmonic, hβroot⟩
  have hmin : P₂k = minpoly (K_1 (K := K) P) β :=
    minpoly.eq_of_irreducible_of_monic hirr hβroot hP₂kmonic
  refine ⟨β, ?_⟩
  rw [IntermediateField.adjoin.finrank hβint, ← hmin, hP₂kdeg]

end LubinTate
