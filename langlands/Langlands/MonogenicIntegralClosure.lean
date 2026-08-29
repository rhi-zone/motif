/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.TowerMonogenicConcrete
import Langlands.TowerBundle
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Field

/-!
# Monogenicity of `𝒪_L / 𝒪[K]`, with no auxiliary data in the statement

`Langlands.TowerMonogenicConcrete.LocalField.
exists_adjoin_eq_top_of_tower_of_isEisensteinAt_of_valuationSubring` proves Serre's tower
monogenicity theorem for a tower `𝒪[K] ⊆ 𝒪_M ⊆ 𝒪_N`, but takes the whole tower apparatus as
hypotheses: an intermediate `M`, a residue-field isomorphism `e` with its compatibility `he`, the
unramifiedness equation `hunram`, and an Eisenstein generator `π` of `𝒪_N / 𝒪_M`. This file proves
the theorem Serre actually states, with none of that in the signature:

> For `K` complete discretely valued with finite residue field and `L / K` finite separable,
> `𝒪_L := integralClosure 𝒪[K] L` is monogenic over `𝒪[K]`.

## How the tower disappears

Serre's proof splits `L / K` at the maximal unramified subextension `M`. But
`Langlands.UnramifiedExtension`'s existence theorem only produces such an extension inside an
ambient algebraically closed field, not inside a given `L`, so `M` cannot always be constructed as
a literal subfield of `L`.

The route taken here never builds `M` at all. Monogenicity of `𝒪_L` over `𝒪[K]` is, by
`Langlands.ArtinianPrimitiveElement.LocalField.exists_adjoin_eq_top_of_residue_nilpotent`, a
question about the Artinian local quotient `B := 𝒪_L ⧸ 𝔪_K 𝒪_L`: it suffices to find a *field*
`κ` inside `B`, finite separable over `κ_K`, with `B = κ + π B` for a nilpotent `π`. The maximal
unramified subextension is only ever used to supply that `κ`; and `κ` can be obtained directly,
because `B ↠ B ⧸ 𝔪_B` is a surjection with nilpotent kernel and `B ⧸ 𝔪_B` is separable over `κ_K`,
so it splits by formal étaleness of separable field extensions
(`Algebra.FormallyEtale.of_isSeparable`, `Algebra.FormallySmooth.lift`). The residual avatar of the
unramified subextension is thus produced without any intermediate field, and in particular without
the "does the constructed `M` land inside `L`" problem.

## Main results

* `LocalField.isIntegral_of_spectralNorm_le_one`, `LocalField.isIntegral_or_isIntegral_inv` : the
  spectral-norm characterisation of integrality that makes `integralClosure 𝒪[K] L` a valuation
  subring of `L`.
* `LocalField.valuationRing_integralClosure`, `LocalField.isFractionRing_integralClosure`,
  `LocalField.isDiscreteValuationRing_integralClosure`, `LocalField.finite_integralClosure`,
  `LocalField.isLocalHom_algebraMap_integralClosure` : the instances on `𝒪_L` that the
  `TowerMonogenicConcrete` bundle previously demanded of the caller, here derived from completeness
  of `K` and finiteness of `L / K`.
* `LocalField.exists_adjoin_eq_top_of_span_maximalIdeal` : Serre's theorem in abstract local-ring
  form — `S` local with principal maximal ideal, finite and local over a local `R` with perfect
  residue field, is monogenic over `R`.
* `LocalField.exists_adjoin_eq_top_integralClosure` : the headline corollary,
  `∃ β : 𝒪_L, Algebra.adjoin 𝒪[K] {β} = ⊤`.
* `LocalField.exists_adjoin_eq_integralClosure` : the same at the level of `L`,
  `∃ x : L, Algebra.adjoin 𝒪[K] {x} = integralClosure 𝒪[K] L`.

## Hypotheses

`Finite (ResidueField 𝒪[K])` is a genuine additional hypothesis relative to
`TowerMonogenicConcrete`'s headline theorem, and it is not a disguised substitute for the `M` /
`e` / `hunram` data: it is used only to make the residue field of `𝒪[K]` perfect, which is what
forces the residue extension `κ_L / κ_K` to be separable. Serre's theorem is false without residue
separability, and in `TowerMonogenicConcrete` that separability is supplied by the caller (via `l`
and `he`); here it is derived. Any hypothesis making `ResidueField 𝒪[K]` perfect would do —
`PerfectField (𝒪[K] ⧸ 𝔪)` is what `exists_adjoin_eq_top_of_span_maximalIdeal` actually asks for.
-/

open IsLocalRing ValuativeRel Polynomial

namespace LocalField

section SpectralIntegrality

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]

omit [CompleteSpace K] in
/-- An element of `L` whose spectral norm is at most `1` is integral over `𝒪[K]`.

The non-leading coefficients of `minpoly K x` are bounded by powers of `spectralNorm K L x ≤ 1`
(`spectralValue_coeff_le`), so every coefficient lies in `𝒪[K]` and `Polynomial.toSubring` lifts
`minpoly K x` to a monic polynomial over `𝒪[K]` witnessing integrality. This is the
`≤ 1` analogue of `LocalField.isIntegral_of_isUniformizer`, whose proof it follows. -/
theorem isIntegral_of_spectralNorm_le_one {x : L} (hx : spectralNorm K L x ≤ 1) :
    IsIntegral ↥(valuation K).valuationSubring x := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  set O : ValuationSubring K := (valuation K).valuationSubring with hO
  have hmonic : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hcoeffs : ∀ i, (minpoly K x).coeff i ∈ O := by
    intro i
    rw [hO, mem_valuationSubring_iff_norm_le_one]
    rcases lt_trichotomy i (minpoly K x).natDegree with hi | hi | hi
    · calc ‖(minpoly K x).coeff i‖
          ≤ spectralNorm K L x ^ ((minpoly K x).natDegree - i) := spectralValue_coeff_le hi
        _ ≤ 1 := pow_le_one₀ (spectralNorm_nonneg x) hx
    · rw [hi, hmonic.coeff_natDegree]; simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi]; simp
  have hp : (↑((minpoly K x).coeffs) : Set K) ⊆ (O.toSubring : Set K) := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨j, -, hcj⟩ := hc
    rw [hcj, SetLike.mem_coe, ValuationSubring.mem_toSubring]
    exact hcoeffs j
  set q : Polynomial O.toSubring := (minpoly K x).toSubring O.toSubring hp with hq
  have hqmonic : q.Monic := (Polynomial.monic_toSubring _ _ _).mpr hmonic
  have hqmap : Polynomial.map O.toSubring.subtype q = minpoly K x :=
    Polynomial.map_toSubring _ _ _
  refine ⟨q, hqmonic, ?_⟩
  have h1 : (Polynomial.aeval x) (Polynomial.map (algebraMap O.toSubring K) q) = 0 := by
    rw [show algebraMap O.toSubring K = O.toSubring.subtype from rfl, hqmap, minpoly.aeval]
  rwa [Polynomial.aeval_map_algebraMap] at h1

/-- For `x ≠ 0`, either `x` or `x⁻¹` is integral over `𝒪[K]`: the spectral norm is multiplicative
(`spectralAlgNorm_mul`, using completeness of `K`), so one of `spectralNorm K L x`,
`spectralNorm K L x⁻¹` is at most `1`, and `isIntegral_of_spectralNorm_le_one` applies. -/
theorem isIntegral_or_isIntegral_inv (x : L) :
    IsIntegral ↥(valuation K).valuationSubring x ∨
      IsIntegral ↥(valuation K).valuationSubring x⁻¹ := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  rcases eq_or_ne x 0 with rfl | hx0
  · exact Or.inl isIntegral_zero
  rcases le_or_gt (spectralNorm K L x) 1 with h | h
  · exact Or.inl (isIntegral_of_spectralNorm_le_one K h)
  refine Or.inr (isIntegral_of_spectralNorm_le_one K ?_)
  have hmul : spectralNorm K L x * spectralNorm K L x⁻¹ = 1 := by
    have := spectralAlgNorm_mul (K := K) (L := L) x x⁻¹
    rw [mul_inv_cancel₀ hx0] at this
    simpa [spectralAlgNorm_def, spectralNorm_one] using this.symm
  nlinarith [spectralNorm_nonneg (K := K) (L := L) x⁻¹]

/-- The integral closure of `𝒪[K]` in a finite extension `L`, packaged as a `ValuationSubring L`.
This is the same term as `LocalField.integralClosureValuationSubring 𝒪[K] L`, but constructed
without presupposing the `ValuationRing`/`IsFractionRing` instances that definition requires:
`isIntegral_or_isIntegral_inv` supplies `ValuationSubring.ofSubring`'s hypothesis directly. -/
noncomputable def spectralValuationSubring : ValuationSubring L :=
  ValuationSubring.ofSubring (integralClosure ↥(valuation K).valuationSubring L).toSubring
    (isIntegral_or_isIntegral_inv K)

/-- `↥(integralClosure 𝒪[K] L)` is a valuation ring: it is definitionally the carrier of
`spectralValuationSubring`. -/
instance valuationRing_integralClosure :
    ValuationRing ↥(integralClosure ↥(valuation K).valuationSubring L) :=
  inferInstanceAs (ValuationRing ↥(spectralValuationSubring K (L := L)))

/-- `L` is the fraction field of `↥(integralClosure 𝒪[K] L)`. -/
instance isFractionRing_integralClosure :
    IsFractionRing ↥(integralClosure ↥(valuation K).valuationSubring L) L :=
  integralClosure.isFractionRing_of_finite_extension K L

end SpectralIntegrality

section RingOfIntegers

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(valuation K).valuationSubring]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- `𝒪_L := integralClosure 𝒪[K] L` is a discrete valuation ring, by
`ValuationSubring.isDiscreteValuationRing_of_comap_eq` applied to its `ValuationSubring`
presentation. -/
instance isDiscreteValuationRing_integralClosure :
    IsDiscreteValuationRing ↥(integralClosure ↥(valuation K).valuationSubring L) :=
  ValuationSubring.isDiscreteValuationRing_of_comap_eq
    (integralClosureValuationSubring ↥(valuation K).valuationSubring L)
    (comap_integralClosureValuationSubring K L)

/-- `𝒪_L` is a finite `𝒪[K]`-module, by `LocalField.finite`. -/
instance finite_integralClosure [Algebra.IsSeparable K L] :
    Module.Finite ↥(valuation K).valuationSubring
      ↥(integralClosure ↥(valuation K).valuationSubring L) :=
  LocalField.finite (R := ↥(valuation K).valuationSubring) (M := L) K

omit [IsDiscreteValuationRing ↥(valuation K).valuationSubring] in
/-- An element of `K` integral over `𝒪[K]` after mapping into `L` already lies in `𝒪[K]`. -/
theorem mem_valuationSubring_of_isIntegral_algebraMap {y : K}
    (hy : IsIntegral ↥(valuation K).valuationSubring (algebraMap K L y)) :
    y ∈ (valuation K).valuationSubring := by
  rw [← comap_integralClosureValuationSubring K L, ValuationSubring.mem_comap,
    mem_integralClosureValuationSubring]
  exact hy

/-- `𝒪[K] → 𝒪_L` is a local homomorphism: if `r : 𝒪[K]` becomes a unit in `𝒪_L`, then `r⁻¹`,
computed in `L`, is integral over `𝒪[K]`, hence lies in `𝒪[K]` itself by
`comap_integralClosureValuationSubring`. -/
instance isLocalHom_algebraMap_integralClosure :
    IsLocalHom (algebraMap ↥(valuation K).valuationSubring
      ↥(integralClosure ↥(valuation K).valuationSubring L)) := by
  constructor
  intro r hr
  obtain ⟨s, hs⟩ := hr.exists_right_inv
  have hsL : algebraMap K L (r : K) * (s : L) = 1 := by
    have := congrArg (Subtype.val) hs
    simpa [IsScalarTower.algebraMap_apply ↥(valuation K).valuationSubring K L] using this
  have hr0 : (r : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hsL
    exact zero_ne_one hsL
  have hsval : (s : L) = algebraMap K L ((r : K)⁻¹) := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsL)
  have hmem : ((r : K)⁻¹) ∈ (valuation K).valuationSubring :=
    mem_valuationSubring_of_isIntegral_algebraMap K L (hsval ▸ s.2)
  refine IsUnit.of_mul_eq_one (a := r) ⟨(r : K)⁻¹, hmem⟩ (Subtype.ext ?_)
  simpa using mul_inv_cancel₀ hr0

end RingOfIntegers

section Abstract

open Algebra

attribute [local instance] Ideal.Quotient.field

/-- **Serre's monogenicity theorem, in abstract local-ring form.**

Let `R ⊆ S` be local rings with `S` finite over `R`, `R → S` local, `𝔪_S` principal, and the
residue field of `R` perfect. Then `S` is monogenic over `R`.

The proof does not construct the maximal unramified subextension as a *ring* between `R` and `S`.
Instead it works entirely in the Artinian local quotient `B := S ⧸ 𝔪_R S`, whose maximal ideal is
nilpotent (`IsArtinianRing.isNilpotent_jacobson_bot`) and whose residue field `κ := B ⧸ 𝔪_B` is
finite separable over `κ_R` (perfection of `κ_R`). A separable field extension is formally étale
(`Algebra.FormallyEtale.of_isSeparable`), so `κ → B ⧸ 𝔪_B` lifts along the nilpotent surjection
`B ↠ B ⧸ 𝔪_B` (`Algebra.FormallySmooth.lift`), producing a copy of `κ` *inside* `B` — the residual
avatar of the unramified subextension, obtained without ever exhibiting an intermediate field. With
that copy and the image `π` of a generator of `𝔪_S`, `B = κ + π B` and `π` is nilpotent, which is
exactly the input of `LocalField.exists_adjoin_eq_top_of_residue_nilpotent`. -/
theorem exists_adjoin_eq_top_of_span_maximalIdeal
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [Module.Finite R S] [IsLocalHom (algebraMap R S)] [PerfectField (R ⧸ maximalIdeal R)]
    {ϖ : S} (hϖ : maximalIdeal S = Ideal.span {ϖ}) :
    ∃ β : S, Algebra.adjoin R ({β} : Set S) = ⊤ := by
  classical
  set J : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R) with hJdef
  have hJle : J ≤ maximalIdeal S :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 0 2).mp ‹IsLocalHom (algebraMap R S)›
  have hJtop : J ≠ ⊤ := fun h => (maximalIdeal S).ne_top_iff_one.mp
    (Ideal.IsMaximal.ne_top (maximalIdeal.isMaximal S)) (h ▸ hJle <| Submodule.mem_top)
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  haveI hBloc : IsLocalRing (S ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI hmkloc : IsLocalHom (Ideal.Quotient.mk J) :=
    _root_.isLocalHom_of_le_jacobson_bot J
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal S) bot_ne_top]; exact hJle)
  -- `B := S ⧸ J` is a finite-dimensional algebra over the residue field of `R`, hence Artinian.
  haveI : Module.Finite R (S ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R J).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ maximalIdeal R) (S ⧸ J)
  haveI : IsArtinianRing (S ⧸ J) :=
    IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  have hnilp : IsNilpotent (maximalIdeal (S ⧸ J)) := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := S ⧸ J)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (S ⧸ J)) bot_ne_top] at h
  -- The image of `ϖ` generates the maximal ideal of `B`.
  set π : S ⧸ J := Ideal.Quotient.mk J ϖ with hπdef
  have hmem : ∀ s : S, Ideal.Quotient.mk J s ∈ maximalIdeal (S ⧸ J) ↔ s ∈ maximalIdeal S := by
    intro s
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff]
    exact not_congr ⟨fun h => hmkloc.map_nonunit s h, fun h => h.map _⟩
  have hspan : maximalIdeal (S ⧸ J) = Ideal.span {π} := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hs : s ∈ maximalIdeal S := (hmem s).mp hy
      rw [hϖ, Ideal.mem_span_singleton] at hs
      obtain ⟨t, rfl⟩ := hs
      rw [Ideal.mem_span_singleton, map_mul]
      exact Dvd.intro _ rfl
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (hmem ϖ).mpr (hϖ ▸ Ideal.mem_span_singleton_self ϖ)
  have hdvd : ∀ w : S ⧸ J, w ∈ maximalIdeal (S ⧸ J) → ∃ z, w = π * z := by
    intro w hw
    rw [hspan, Ideal.mem_span_singleton] at hw
    exact hw
  obtain ⟨e, he⟩ := hnilp
  have hnilp : IsNilpotent (maximalIdeal (S ⧸ J)) := ⟨e, he⟩
  have hnil : π ^ e = 0 := by
    have hpow : π ^ e ∈ maximalIdeal (S ⧸ J) ^ e := by
      rw [hspan]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) e
    rwa [he, Ideal.zero_eq_bot, Ideal.mem_bot] at hpow
  -- The residue field of `B`.
  set κ : Type _ := (S ⧸ J) ⧸ maximalIdeal (S ⧸ J) with hκdef
  haveI : Module.Finite (R ⧸ maximalIdeal R) κ :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (R ⧸ maximalIdeal R) _).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic (R ⧸ maximalIdeal R) κ :=
    Algebra.IsAlgebraic.of_finite (R ⧸ maximalIdeal R) κ
  haveI : Algebra.IsSeparable (R ⧸ maximalIdeal R) κ :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale (R ⧸ maximalIdeal R) κ :=
    Algebra.FormallyEtale.of_isSeparable _ _
  -- Lift `κ` into `B` along the nilpotent surjection `B ↠ κ`.
  set σ : κ →ₐ[R ⧸ maximalIdeal R] (S ⧸ J) :=
    Algebra.FormallySmooth.lift (maximalIdeal (S ⧸ J)) hnilp
      (AlgHom.id (R ⧸ maximalIdeal R) κ) with hσdef
  have hσ : ∀ c : κ, Ideal.Quotient.mk (maximalIdeal (S ⧸ J)) (σ c) = c := fun c =>
    Algebra.FormallySmooth.mk_lift _ hnilp _ c
  letI : Algebra κ (S ⧸ J) := σ.toRingHom.toAlgebra
  haveI : IsScalarTower (R ⧸ maximalIdeal R) κ (S ⧸ J) :=
    @IsScalarTower.of_algebraMap_eq (R ⧸ maximalIdeal R) κ (S ⧸ J) _ _ _ _ _ _
      fun x => (σ.commutes x).symm
  refine exists_adjoin_eq_top_of_residue_nilpotent (R := R) (S := S) (κ := κ) (π := π) (e := e)
    hnil ?_
  intro y
  have hsub : y - σ (Ideal.Quotient.mk (maximalIdeal (S ⧸ J)) y) ∈ maximalIdeal (S ⧸ J) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hσ, sub_self]
  obtain ⟨z, hz⟩ := hdvd _ hsub
  refine ⟨Ideal.Quotient.mk (maximalIdeal (S ⧸ J)) y, z, ?_⟩
  have halg : algebraMap κ (S ⧸ J) (Ideal.Quotient.mk (maximalIdeal (S ⧸ J)) y)
      = σ (Ideal.Quotient.mk (maximalIdeal (S ⧸ J)) y) := rfl
  rw [halg]
  linear_combination hz

end Abstract

section Main

attribute [local instance] Ideal.Quotient.field

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(valuation K).valuationSubring]
  [Finite (ResidueField ↥(valuation K).valuationSubring)]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **Serre's monogenicity theorem for `𝒪_L / 𝒪[K]`, unconditionally.**

For `K` complete discretely valued with finite residue field and `L / K` finite separable, the
integral closure `𝒪_L := integralClosure 𝒪[K] L` is monogenic over `𝒪[K]`.

No intermediate extension, residue-field isomorphism, unramifiedness hypothesis or Eisenstein
generator appears in the statement: all of that is internalised by
`LocalField.exists_adjoin_eq_top_of_span_maximalIdeal`, which replaces the maximal unramified
subextension by its residual avatar inside `𝒪_L ⧸ 𝔪_K 𝒪_L` obtained from formal étaleness of the
separable residue extension. The valuation-theoretic inputs — `𝒪_L` is a discrete valuation ring
(hence has principal maximal ideal), is finite over `𝒪[K]`, and receives `𝒪[K]` by a local
homomorphism — are the instances established earlier in this file, all of them consequences of
completeness of `K` via the spectral norm. -/
theorem exists_adjoin_eq_top_integralClosure :
    ∃ β : ↥(integralClosure ↥(valuation K).valuationSubring L),
      Algebra.adjoin ↥(valuation K).valuationSubring
        ({β} : Set ↥(integralClosure ↥(valuation K).valuationSubring L)) = ⊤ := by
  haveI : Finite (↥(valuation K).valuationSubring ⧸
      maximalIdeal ↥(valuation K).valuationSubring) :=
    inferInstanceAs (Finite (ResidueField ↥(valuation K).valuationSubring))
  haveI : PerfectField (↥(valuation K).valuationSubring ⧸
      maximalIdeal ↥(valuation K).valuationSubring) := PerfectField.ofFinite
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
    ↥(integralClosure ↥(valuation K).valuationSubring L)
  exact exists_adjoin_eq_top_of_span_maximalIdeal hϖ.maximalIdeal_eq

/-- `L`-level form of `exists_adjoin_eq_top_integralClosure`: a single `x : L` with
`𝒪[K][x] = 𝒪_L` as subalgebras of `L`. This is the shape
`LocalField.adjoin_eq_integralClosure_of_isUniformizer` states for the totally ramified case, now
without any ramification hypothesis. -/
theorem exists_adjoin_eq_integralClosure :
    ∃ x : L, Algebra.adjoin ↥(valuation K).valuationSubring ({x} : Set L) =
      integralClosure ↥(valuation K).valuationSubring L := by
  obtain ⟨β, hβ⟩ := exists_adjoin_eq_top_integralClosure K L
  refine ⟨(β : L), ?_⟩
  have h := congrArg
    (Subalgebra.map ((integralClosure ↥(valuation K).valuationSubring L).val)) hβ
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val] at h
  simpa using h

end Main

end LocalField
