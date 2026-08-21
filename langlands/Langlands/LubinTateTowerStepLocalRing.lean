/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepMonogenic
import Langlands.IntegralExtensionLocalRing

/-!
# `IsLocalRing O_{K_2}`, closing the sub-gap `ROADMAP.md §57` identified

`Langlands/LubinTateTowerStepMonogenic.lean`'s `adjoin_eq_integralClosure_K_2` proves `O_{K_2} :=
integralClosure O_{K_1} (nextSplittingField P₂)` is monogenic over `O_{K_1}`, but residue-field preservation needs
the further fact `[IsLocalRing O_{K_2}]` — a hypothesis
`IsLocalRing.residueFieldEquivOfAdjoinSingleton` (`Langlands/TotallyRamifiedResidueField.lean`) bakes
directly into its signature, and monogenicity alone does not supply it. `§57` diagnosed this precisely
and sketched (but did not attempt) the route this file executes:
`Langlands/IntegralExtensionLocalRing.lean`'s general
`IsLocalRing.of_isIntegral_of_isLocalRing_quotient_map_maximalIdeal` reduces `[IsLocalRing O_{K_2}]`
to `[IsLocalRing (O_{K_2} ⧸ 𝔪_{O_{K_1}} · O_{K_2})]`, and this file identifies that quotient's
local-ness directly from `β`'s Eisenstein minimal polynomial `P₂`.

## Main results

* `Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure` : a general (non-tower-specific)
  helper — `Algebra.adjoin R {x} = integralClosure R L` at the field level transports to
  `Algebra.adjoin R {⟨x, hxint⟩} = ⊤` at the `↥(integralClosure R L)` level. The non-`ValuativeRel`
  analogue of `Langlands/TotallyRamifiedResidueField.lean`'s
  `LocalField.adjoin_singleton_eq_top_of_isUniformizer`, whose proof this reproduces verbatim.
* `isLocalRing_integralClosure_of_isDistinguishedAt_root` : a general (non-tower-specific) engine —
  `R` local, `L` a field extension of `Frac(R)`-ish `Algebra R L`, `β : L` a root of a monic,
  `IsDistinguishedAt`-shaped `P₂ : R[X]` of positive degree, with `Algebra.adjoin R {β} =
  integralClosure R L`. Then `integralClosure R L` is local. Proved entirely by the "nilpotent
  generator of the residual quotient" route
  (`Langlands/IntegralExtensionLocalRing.lean`'s two lemmas), with no valuation theory. Stated
  abstractly (not tied to the Lubin-Tate tower's concrete `K_1`/`nextSplittingField` types) precisely to avoid the
  `Algebra`/`IsScalarTower` instance-diamond fragility this whole arc is built around: instantiating
  it at concrete types is a single application, with no in-proof `set`/rewriting of the ambient ring
  needed.
* `isLocalRing_integralClosure_K_2` : **`IsLocalRing O_{K_2}`**, the instantiation of the above at
  `R := O_{K_1}`, `L := nextSplittingField P₂`, under exactly `adjoin_eq_integralClosure_K_2`'s hypothesis package.
* `isLocalHom_algebraMap_integralClosure_K_2` : the free corollary
  `IsLocalHom (algebraMap O_{K_1} O_{K_2})`, via `Langlands/IntegralExtensionLocalRing.lean`'s
  `IsLocalHom.algebraMap_of_isIntegral`.
* `mem_maximalIdeal_of_isDistinguishedAt_root` / `mem_maximalIdeal_integralClosure_K_2` : the root
  `β` itself (viewed inside the integral closure) lies in the integral closure's maximal ideal —
  the abstract engine and its `K_1`/`nextSplittingField` instantiation, needed for
  `IsLocalRing.residueFieldEquivOfAdjoinSingleton`'s `hπ` hypothesis in
  `Langlands/LubinTateTowerStepResidueField.lean`.

No `ValuativeRel (K_1 P)` instance is built or needed anywhere in this file, continuing
`LubinTateTowerStepMonogenic.lean`'s bare-Eisenstein route.
-/

noncomputable section

open scoped Polynomial PowerSeries IntermediateField
open IsLocalRing Polynomial PowerSeries

/-- **`Algebra.adjoin R {x} = integralClosure R L` transports to `Algebra.adjoin R {x'} = ⊤` at the
`↥(integralClosure R L)` level**, `x'` being `x` viewed inside the integral closure. The
`ValuativeRel`-free analogue of
`Langlands/TotallyRamifiedResidueField.lean`'s `LocalField.adjoin_singleton_eq_top_of_isUniformizer`
— only `R`, `L`, `x` and its integrality are used, no valuation/norm structure at all. Proof:
`Polynomial.aeval_algHom_apply` along `Subalgebra.val (integralClosure R L)` identifies evaluation at
`x'` inside the integral closure with evaluation at `x` inside `L`, transporting the `Set L` adjoin
equality to the `Set ↥(integralClosure R L)` one. -/
theorem Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure
    {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    {x : L} (hxint : IsIntegral R x)
    (hadjL : Algebra.adjoin R ({x} : Set L) = integralClosure R L) :
    Algebra.adjoin R ({(⟨x, hxint⟩ : ↥(integralClosure R L))} : Set ↥(integralClosure R L)) = ⊤ := by
  refine Algebra.eq_top_iff.mpr fun b => ?_
  have hb : (b : L) ∈ Algebra.adjoin R ({x} : Set L) := by rw [hadjL]; exact b.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨p, hp⟩ := hb
  have hp' : Polynomial.aeval x p = (b : L) := hp
  have hval : Polynomial.aeval (⟨x, hxint⟩ : ↥(integralClosure R L)) p = b := by
    have haeval := Polynomial.aeval_algHom_apply (Subalgebra.val (integralClosure R L))
      (⟨x, hxint⟩ : ↥(integralClosure R L)) p
    refine Subtype.ext ?_
    simpa [hp'] using haeval.symm
  rw [← hval, Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨p, rfl⟩

/-- **`integralClosure R L` is local, given a monogenic generator that is a root of an
`R`-`IsDistinguishedAt` polynomial.** `R` local, `L` a field with `Algebra R L`, `P₂ : R[X]` monic of
positive degree with all non-leading coefficients in `maximalIdeal R` (`IsDistinguishedAt`), `β : L`
a root of `P₂` with `Algebra.adjoin R {β} = integralClosure R L`. Then `integralClosure R L` is a
local ring.

Stated abstractly, with `R` and `L` arbitrary type variables (not the Lubin-Tate tower's concrete
`K_1 P`/`nextSplittingField P₂`), so that instantiating it is a single application with no in-proof `set`/rewriting
of the ambient ring — avoiding the `Algebra`/`IsScalarTower` instance-diamond fragility this whole
arc is otherwise built around.

Proof: `β' := ⟨β, hβint⟩ : ↥(integralClosure R L)` generates `↥(integralClosure R L)` as an
`R`-algebra (`Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure`). Reducing `P₂`'s defining
equation `aeval β' P₂ = 0` modulo `J := 𝔪_R · (integralClosure R L)` kills every term below the
leading one (`P₂`'s non-leading coefficients lie in `𝔪_R`, which maps to `0` in the quotient by
construction of `J`), leaving `(mk β')^{P₂.natDegree} = 0` in the quotient — so `mk β'` is nilpotent,
and generates the quotient as an `R`-algebra (image of the monogenicity fact).
`Langlands/IntegralExtensionLocalRing.lean`'s `IsLocalRing.of_isNilpotent_of_adjoin_eq_top` then gives
the quotient is local, and `IsLocalRing.of_isIntegral_of_isLocalRing_quotient_map_maximalIdeal` lifts
this to `integralClosure R L` itself. `J ≠ ⊤` (needed for the quotient to be nontrivial) is Nakayama's
lemma, `integralClosure R L` being a nonzero finite `R`-module (finite since generated by the single
integral element `β'`). -/
theorem isLocalRing_integralClosure_of_isDistinguishedAt_root
    {R : Type*} [CommRing R] [IsLocalRing R] {L : Type*} [Field L] [Algebra R L]
    {P₂ : R[X]} (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal R)) (hdeg : 0 < P₂.natDegree)
    {β : L} (hβroot : Polynomial.aeval β P₂ = 0)
    (hadjL : Algebra.adjoin R ({β} : Set L) = integralClosure R L) :
    IsLocalRing ↥(integralClosure R L) := by
  have hβint : IsIntegral R β := ⟨P₂, hP₂dist.monic, hβroot⟩
  let β' : ↥(integralClosure R L) := ⟨β, hβint⟩
  have hβ'int : IsIntegral R β' := integralClosure.isIntegral β'
  have hβ'root : Polynomial.aeval β' P₂ = 0 := by
    have haeval := Polynomial.aeval_algHom_apply (Subalgebra.val (integralClosure R L)) β' P₂
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, ← hβroot]
    exact haeval.symm
  have hadjS : Algebra.adjoin R ({β'} : Set ↥(integralClosure R L)) = ⊤ :=
    Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure hβint hadjL
  -- The quotient `J := 𝔪_R S` for `S := ↥(integralClosure R L)`.
  let J : Ideal ↥(integralClosure R L) :=
    Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R)
  have hR0 : ∀ m ∈ maximalIdeal R, algebraMap R (↥(integralClosure R L) ⧸ J) m = 0 := by
    intro m hm
    show Ideal.Quotient.mk J (algebraMap R ↥(integralClosure R L) m) = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_map_of_mem _ hm)
  -- `β'`'s image is nilpotent, from `P₂`'s distinguished shape.
  have hcoeff0 : ∀ i, i < P₂.natDegree →
      algebraMap R (↥(integralClosure R L) ⧸ J) (P₂.coeff i) = 0 :=
    fun i hi => hR0 _ (hP₂dist.toIsWeaklyEisensteinAt.mem hi)
  have hmkzero : Polynomial.aeval (Ideal.Quotient.mkₐ R J β') P₂ = 0 := by
    rw [Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ R J) β' P₂, hβ'root, map_zero]
  have hsum : ∑ i ∈ Finset.range (P₂.natDegree + 1),
      algebraMap R (↥(integralClosure R L) ⧸ J) (P₂.coeff i) *
        (Ideal.Quotient.mkₐ R J β' : ↥(integralClosure R L) ⧸ J) ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hmkzero
  rw [Finset.sum_range_succ] at hsum
  have hlow : ∑ i ∈ Finset.range P₂.natDegree,
      algebraMap R (↥(integralClosure R L) ⧸ J) (P₂.coeff i) *
        (Ideal.Quotient.mkₐ R J β' : ↥(integralClosure R L) ⧸ J) ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hcoeff0 i (Finset.mem_range.mp hi), zero_mul]
  rw [hlow, zero_add, hP₂dist.monic.coeff_natDegree, map_one, one_mul] at hsum
  have hβ'nil : IsNilpotent (Ideal.Quotient.mkₐ R J β' : ↥(integralClosure R L) ⧸ J) :=
    ⟨P₂.natDegree, hsum⟩
  -- `S` is a nonzero (finite) `R`-module, so `J ≠ ⊤` by Nakayama.
  have hfin : Module.Finite R ↥(integralClosure R L) := by
    have hfin' : Module.Finite R ↥(Algebra.adjoin R ({β'} : Set ↥(integralClosure R L))) :=
      Algebra.finite_adjoin_simple_of_isIntegral hβ'int
    have hequiv : ↥(Algebra.adjoin R ({β'} : Set ↥(integralClosure R L))) ≃ₐ[R]
        ↥(integralClosure R L) :=
      (Subalgebra.equivOfEq _ _ hadjS).trans Subalgebra.topEquiv
    exact Module.Finite.equiv hequiv.toLinearEquiv
  have hjac : maximalIdeal R ≤ (Module.annihilator R ↥(integralClosure R L)).jacobson :=
    (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).symm.trans_le
      (Ideal.jacobson_mono bot_le)
  have hne : (⊤ : Submodule R ↥(integralClosure R L)) ≠ maximalIdeal R • ⊤ :=
    Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator hjac
  have hne' : (⊤ : Submodule R ↥(integralClosure R L)) ≠ J.restrictScalars R := by
    rwa [← Ideal.smul_top_eq_map]
  have hJtop : J ≠ ⊤ := by
    intro hJeq
    exact hne' (by rw [hJeq, Submodule.restrictScalars_top])
  haveI : Nontrivial (↥(integralClosure R L) ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  -- `S ⧸ J` is generated over `R` by the nilpotent `mk β'`, hence local.
  have hsurj : Function.Surjective (Ideal.Quotient.mkₐ R J) := Ideal.Quotient.mk_surjective
  have hadjSJ : Algebra.adjoin R
      ({(Ideal.Quotient.mkₐ R J β' : ↥(integralClosure R L) ⧸ J)} :
        Set (↥(integralClosure R L) ⧸ J)) = ⊤ := by
    have h := congrArg (Subalgebra.map (Ideal.Quotient.mkₐ R J)) hadjS
    rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top,
      (AlgHom.range_eq_top _).mpr hsurj] at h
    exact h
  haveI : IsLocalRing (↥(integralClosure R L) ⧸ J) :=
    IsLocalRing.of_isNilpotent_of_adjoin_eq_top hR0 hβ'nil hadjSJ
  exact IsLocalRing.of_isIntegral_of_isLocalRing_quotient_map_maximalIdeal
    (R := R) (S := ↥(integralClosure R L))

/-- **The root itself lies in the maximal ideal of the integral closure**, under the same
`IsDistinguishedAt` hypotheses as `isLocalRing_integralClosure_of_isDistinguishedAt_root` (stated
separately, taking `[IsLocalRing ↥(integralClosure R L)]` and
`[IsLocalHom (algebraMap R ↥(integralClosure R L))]` as hypotheses rather than re-deriving them, so
callers who already have those instances — e.g. from the theorem above — do not pay for them twice).

Needed for `IsLocalRing.residueFieldEquivOfAdjoinSingleton`'s `hπ : π ∈ maximalIdeal B` hypothesis.
Proof: reducing `β'`'s defining equation `aeval β' P₂ = 0` gives `β'^{P₂.natDegree} = -∑_{i <
P₂.natDegree} (P₂.coeff i) • β'^i`, and each summand lies in `maximalIdeal ↥(integralClosure R L)`
since `P₂.coeff i ∈ maximalIdeal R` for `i < P₂.natDegree` (`IsDistinguishedAt`) and `𝔪_R ·
(integralClosure R L) ⊆ maximalIdeal (integralClosure R L)` (`IsLocalRing.map_maximalIdeal_le`, from
the local homomorphism hypothesis). So `β'^{P₂.natDegree} ∈ maximalIdeal (integralClosure R L)`, and
maximal ideals are prime, so `β'` itself is (`Ideal.IsPrime.mem_of_pow_mem`). -/
theorem mem_maximalIdeal_of_isDistinguishedAt_root
    {R L : Type*} [CommRing R] [IsLocalRing R] [Field L] [Algebra R L]
    [IsLocalRing ↥(integralClosure R L)]
    [IsLocalHom (algebraMap R ↥(integralClosure R L))]
    {P₂ : R[X]} (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal R))
    {β : L} (hβint : IsIntegral R β) (hβroot : Polynomial.aeval β P₂ = 0) :
    (⟨β, hβint⟩ : ↥(integralClosure R L)) ∈ maximalIdeal ↥(integralClosure R L) := by
  have hβ'root : Polynomial.aeval (⟨β, hβint⟩ : ↥(integralClosure R L)) P₂ = 0 := by
    have haeval := Polynomial.aeval_algHom_apply (Subalgebra.val (integralClosure R L))
      (⟨β, hβint⟩ : ↥(integralClosure R L)) P₂
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, ← hβroot]
    exact haeval.symm
  have hle : Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) ≤
      maximalIdeal ↥(integralClosure R L) := IsLocalRing.map_maximalIdeal_le _
  have heval : Polynomial.eval₂ (algebraMap R ↥(integralClosure R L))
      (⟨β, hβint⟩ : ↥(integralClosure R L)) P₂ = 0 := hβ'root
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hP₂dist.monic.coeff_natDegree,
    map_one, one_mul] at heval
  have hexp : (⟨β, hβint⟩ : ↥(integralClosure R L)) ^ P₂.natDegree =
      -∑ i ∈ Finset.range P₂.natDegree,
        algebraMap R ↥(integralClosure R L) (P₂.coeff i) *
          (⟨β, hβint⟩ : ↥(integralClosure R L)) ^ i :=
    eq_neg_of_add_eq_zero_right heval
  have hmem : (⟨β, hβint⟩ : ↥(integralClosure R L)) ^ P₂.natDegree ∈
      maximalIdeal ↥(integralClosure R L) := by
    rw [hexp]
    refine (maximalIdeal ↥(integralClosure R L)).neg_mem (Ideal.sum_mem _ fun i hi => ?_)
    have hci : algebraMap R ↥(integralClosure R L) (P₂.coeff i) ∈
        maximalIdeal ↥(integralClosure R L) :=
      hle (Ideal.mem_map_of_mem _ (hP₂dist.toIsWeaklyEisensteinAt.mem (Finset.mem_range.mp hi)))
    exact Ideal.mul_mem_right _ _ hci
  exact (maximalIdeal.isMaximal ↥(integralClosure R L)).isPrime.mem_of_pow_mem _ hmem

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]}
  {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X]}

/-- **`IsLocalRing O_{K_2}`.** Under exactly `adjoin_eq_integralClosure_K_2`'s hypothesis package,
`O_{K_2} := integralClosure O_{K_1} (nextSplittingField P₂)` is a local ring. Instantiation of
`isLocalRing_integralClosure_of_isDistinguishedAt_root` at `R := O_{K_1}`, `L := nextSplittingField P₂`; `hβroot`
supplies the root-at-`R`-level fact `isLocalRing_integralClosure_of_isDistinguishedAt_root` needs
(via `Polynomial.aeval_map_algebraMap`, descending `hβroot`'s `K_1 P`-level statement to `O_{K_1}`),
and `adjoin_eq_integralClosure_K_2` supplies `hadjL`. -/
theorem isLocalRing_integralClosure_K_2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
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
    (hα'norm : ‖algebraMap _ (nextSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : nextSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)] :
    IsLocalRing (↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (nextSplittingField (K' := K_1 (K := K) P) P₂))) := by
  have hβroot' : Polynomial.aeval β P₂ = 0 := by
    have h1 : Polynomial.aeval β (Polynomial.map
        (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P)) P₂) = 0 := hβroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  exact isLocalRing_integralClosure_of_isDistinguishedAt_root hP₂dist hdeg hβroot'
    (adjoin_eq_integralClosure_K_2 hOK hπ hπnorm hf hu heq hPdist hPdeg hu₂ heq₂ hα'irr hP₂dist
      hassoc hdeg hα'norm hα'coe hirr hβroot hβfin)

/-- **`algebraMap O_{K_1} O_{K_2}` is a local homomorphism.** Free corollary of
`isLocalRing_integralClosure_K_2` via
`Langlands/IntegralExtensionLocalRing.lean`'s `IsLocalHom.algebraMap_of_isIntegral`. -/
theorem isLocalHom_algebraMap_integralClosure_K_2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
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
    (hα'norm : ‖algebraMap _ (nextSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : nextSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)] :
    IsLocalHom (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) ↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (nextSplittingField (K' := K_1 (K := K) P) P₂))) := by
  haveI := isLocalRing_integralClosure_K_2 hOK hπ hπnorm hf hu heq hPdist hPdeg hu₂ heq₂ hα'irr
    hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin
  exact IsLocalHom.algebraMap_of_isIntegral
    (R := ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))
    (S := ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (nextSplittingField (K' := K_1 (K := K) P) P₂)))

/-- **`β` (viewed inside `O_{K_2}`) lies in `maximalIdeal O_{K_2}`.** The instantiation of
`mem_maximalIdeal_of_isDistinguishedAt_root` needed for
`Langlands/LubinTateTowerStepResidueField.lean`'s residue-field-preservation closure. Takes
`[IsLocalRing O_{K_2}]`/`[IsLocalHom (algebraMap O_{K_1} O_{K_2})]` as explicit hypotheses — callers
supply them via `isLocalRing_integralClosure_K_2` / `isLocalHom_algebraMap_integralClosure_K_2`
(`haveI`), since they are not registered as global instances at this concrete instantiation. -/
theorem mem_maximalIdeal_integralClosure_K_2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
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
    (hα'norm : ‖algebraMap _ (nextSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : nextSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)]
    (hβint : IsIntegral ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) β)
    [IsLocalRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (nextSplittingField (K' := K_1 (K := K) P) P₂))]
    [IsLocalHom (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) ↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (nextSplittingField (K' := K_1 (K := K) P) P₂)))] :
    (⟨β, hβint⟩ : ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (nextSplittingField (K' := K_1 (K := K) P) P₂))) ∈ maximalIdeal ↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (nextSplittingField (K' := K_1 (K := K) P) P₂)) := by
  have hβroot' : Polynomial.aeval β P₂ = 0 := by
    have h1 : Polynomial.aeval β (Polynomial.map
        (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P)) P₂) = 0 := hβroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  exact mem_maximalIdeal_of_isDistinguishedAt_root
    (R := ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))
    (L := nextSplittingField (K' := K_1 (K := K) P) P₂) hP₂dist hβint hβroot'

end LubinTate

end
