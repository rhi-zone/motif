import Langlands.HenselianValuation
import Langlands.IdeleGroup
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.Minpoly.IsConjRoot

/-!
# The idèle norm map

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`. The idèle norm
map sends an idèle `a` of `L` to the idèle of `K` whose component at a place `v` is
`∏_{w ∣ v} N_{L_w/K_v}(a_w)`, the product of the local norms over the finitely many places `w`
of `L` above `v`. This file constructs the local norm maps at the finite and at the infinite
places, and assembles them into `NumberField.IdeleGroup.normMap`.

At a finite place, "lying over" is `w.asIdeal.LiesOver v.asIdeal`, and the local norm is the
field norm of the extension of completions `L_w / K_v`. That extension is obtained by extending
`algebraMap K L`, uniformly continuous for the `v`- and `w`-adic uniformities
(`uniformContinuous_algebraMap_liesOver`), to the completions (`adicCompletionComap`). Since
`FiniteAdeleRing` is a restricted product, assembling the local norms into a map of finite idèle
groups requires that the local norm of a local unit is again a local unit
(`localNormMap_mem_units`), which reduces to the ring of integers of `L_w` being the integral
closure of that of `K_v` (Serre, *Local Fields*, Ch. II §2); the section
`IntegralClosure` below proves this via Galois conjugates in a normal closure.

At an infinite place, "lying over" is `w.1.LiesOver v.1` for the underlying complex embeddings,
`InfiniteAdeleRing` is an unrestricted product, and `InfinitePlace K` is finite, so no
support condition and no finiteness argument are needed.

`NumberField.IdeleGroup.normMap` is defined here rather than in `Langlands/IdeleGroup.lean` to
avoid a circular import.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionComap` : the ring hom
  `v.adicCompletion K →+* w.adicCompletion L` induced by `algebraMap K L`, for `w` a place of `S`
  lying over `v`.
* `IsDedekindDomain.HeightOneSpectrum.localNormMap` : the local norm map on units at a finite
  place, `(w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ`.
* `NumberField.InfinitePlace.localNormMap` : the local norm map on units at an infinite place,
  `(w.Completion)ˣ →* (v.Completion)ˣ`.
* `NumberField.FiniteIdeleGroup.normMap`, `NumberField.InfiniteIdeleGroup.normMap` : the
  finite-place and archimedean halves of the idèle norm map.
* `NumberField.IdeleGroup.normMap` : the idèle norm map `IdeleGroup S L →* IdeleGroup R K`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.isIntegral_of_mem_of_comap_eq` : for a finite extension
  `Lw / Kv` of a complete nonarchimedean field, every element of a valuation subring of `Lw`
  lying over the valuation subring of `Kv` is integral over the latter.
* `IsDedekindDomain.HeightOneSpectrum.finite_liesOver` : only finitely many places of `S` lie over
  a given place `v` of `R`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_comap_eq` : `adicCompletionComap`
  pulls `w.adicCompletionIntegers L` back to `v.adicCompletionIntegers K`.
* `IsDedekindDomain.HeightOneSpectrum.localNormMap_mem_units` : the local norm of a local unit is
  a local unit.
* `IsDedekindDomain.HeightOneSpectrum.eventually_localNormMap_mem_units` : for all but finitely
  many places `v` of `R`, the local norms at every place above `v` of an almost-everywhere local
  unit are local units.
-/

noncomputable section

open IsDedekindDomain
open scoped Pointwise WithZeroTopology

namespace IsDedekindDomain.HeightOneSpectrum

section RankOne

open scoped WithZero NNReal

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- The `v`-adic completion of the fraction field of a Dedekind domain carries a rank-one
valuation. Mathlib provides `Valuation.IsRankOneDiscrete` for
`(Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)` for any Dedekind domain `A` with fraction field
`F` (in `Mathlib.NumberTheory.NumberField.Completion.FinitePlace`, despite the namespace);
`Valuation.IsRankOneDiscrete.rankOne` upgrades it to a `Valuation.RankOne` instance for any real
`e > 1`, taken here to be `e = 2`.

The value of `e` is arbitrary because no finiteness of the residue field is assumed. Contrast
`NumberField.instRankOneAdicCompletion`, which takes `e = absNorm v.asIdeal` so that the induced
norm is the classical adic absolute value, a choice available only when `A` is finite free over
`ℤ`. -/
noncomputable instance instRankOneValuedAdicCompletion :
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (by norm_num : (1 : ℝ≥0) < 2)

/-- The `ValuativeRel` on `v.adicCompletion F` induced by its ambient `Valued` structure, via
`ValuativeRel.ofValuation` applied to `Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰`.

This is the first of the four instances (`ValuativeRel`, its compatibility with `Valued.v`,
`NontriviallyNormedField`, and compatibility with `NormedField.valuation`) that
`LocalField.valuationSubring_eq_of_comap_eq` (`Langlands.HenselianValuation`) requires of its base
field. -/
noncomputable instance instValuativeRelValuedAdicCompletion :
    ValuativeRel (v.adicCompletion F) :=
  ValuativeRel.ofValuation (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)

/-- The ambient `Valued.v` on `v.adicCompletion F` is `Compatible` with
`instValuativeRelValuedAdicCompletion`, which is by definition the `ValuativeRel` it induces. -/
instance : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Compatible :=
  Valuation.Compatible.ofValuation _

/-- `v.adicCompletion F` is a nontrivially normed field, via `Valued.toNontriviallyNormedField`
applied to the ambient `Valued` structure and `instRankOneValuedAdicCompletion`. -/
noncomputable instance instNontriviallyNormedFieldAdicCompletion :
    NontriviallyNormedField (v.adicCompletion F) :=
  Valued.toNontriviallyNormedField (v.adicCompletion F) ℤᵐ⁰

/-- The canonical valuation `NormedField.valuation` of `instNontriviallyNormedFieldAdicCompletion`
is `Compatible` with `instValuativeRelValuedAdicCompletion`, completing the hypotheses of
`LocalField.valuationSubring_eq_of_comap_eq` for `v.adicCompletion F`. Proved via
`NormedField.valuation_compatible_of_eq_rankOne_hom_comp_restrict`
(`Langlands.HenselianValuation`); its hypothesis holds definitionally, the normed-field structure
being built from `Valued.v`. -/
instance : (NormedField.valuation (K := v.adicCompletion F)).Compatible :=
  NormedField.valuation_compatible_of_eq_rankOne_hom_comp_restrict
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
    (fun x => congrFun
      (Valued.coe_valuation_eq_rankOne_hom_comp_valuation (v.adicCompletion F) ℤᵐ⁰) x)

/-- `v.adicCompletion F` is discretely valued: `Valued.v` is `Valuation.IsRankOneDiscrete`
(Mathlib, `NumberTheory.NumberField.Completion.FinitePlace`, for any Dedekind domain), hence its
value group is cyclic and nontrivial, and `Valuation.valuationSubring_isDiscreteValuationRing`
(Serre, *Local Fields* I §1 Prop. 1) converts this into `IsDiscreteValuationRing` of the
valuation subring. -/
instance instIsDiscreteValuationRingValuationSubringAdicCompletion :
    IsDiscreteValuationRing ↥(ValuativeRel.valuation (v.adicCompletion F)).valuationSubring := by
  have heq : (ValuativeRel.valuation (v.adicCompletion F)).valuationSubring
      = (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).valuationSubring := by
    refine ValuationSubring.ext _ _ fun x => ?_
    rw [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff]
    have h1 : (ValuativeRel.valuation (v.adicCompletion F)) x ≤ 1 ↔ x ≤ᵥ (1 : v.adicCompletion F) := by
      rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (v.adicCompletion F)), map_one]
    have h2 : x ≤ᵥ (1 : v.adicCompletion F) ↔
        (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) x ≤ 1 := by
      rw [Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)),
        map_one]
    rw [h1, h2]
  rw [heq]
  exact Valuation.valuationSubring_isDiscreteValuationRing
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)

end RankOne

section IntegralClosure

/-! ### Elements of a valuation-ring extension are integral over the base

For a finite extension `Lw / Kv` of complete discretely-valued fields, the ring of integers of
`Lw` is the integral closure in `Lw` of the ring of integers `Ov` of `Kv` (Serre, *Local Fields*,
Ch. II §2). Only the inclusion into the integral closure is proved here; the reverse inclusion is
formal from `IsIntegrallyClosed`.

The argument passes to a normal closure `N` of `Lw / Kv`. Uniqueness of the extension of a
complete valuation (`LocalField.valuationSubring_eq_of_comap_eq`) makes the valuation subring `A`
of `N` lying over `Ov` stable under every `Kv`-automorphism of `N`, and every root of
`minpoly Kv x` in `N` is a conjugate of `x` (`IsConjRoot.exists_algEquiv`), hence lies in `A`.
The coefficients of `minpoly Kv x` therefore lie in `A ∩ Kv = Ov`, exhibiting `x` as integral. -/

open Polynomial in
/-- For a multiset `m` of elements of a field `N` all lying in a subring `T`, the product
`∏ r ∈ m, (X - C r)` is the image of a polynomial over `T`. By induction on `m`. -/
theorem exists_toSubring_of_roots_mem {N : Type*} [Field N] (T : Subring N) (m : Multiset N)
    (hm : ∀ r ∈ m, r ∈ T) : ∃ q : T[X], q.map T.subtype = (m.map (fun r => X - C r)).prod := by
  induction m using Multiset.induction with
  | empty => exact ⟨1, by simp⟩
  | cons a s ih =>
    obtain ⟨q, hq⟩ := ih (fun r hr => hm r (Multiset.mem_cons_of_mem hr))
    refine ⟨(X - C (⟨a, hm a (Multiset.mem_cons_self a s)⟩ : T)) * q, ?_⟩
    simp [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, hq]

open Polynomial in
/-- If a monic polynomial over a field `N` splits and all its roots lie in a subring `T`, then so
do all its coefficients. -/
theorem coeff_mem_subring_of_splits {N : Type*} [Field N] (T : Subring N) {p : N[X]}
    (hpmon : p.Monic) (hp : p.Splits) (hpr : ∀ x, p.IsRoot x → x ∈ T) (i : ℕ) :
    p.coeff i ∈ T := by
  obtain ⟨q, hq⟩ := exists_toSubring_of_roots_mem T p.roots
    (fun r hr => hpr r (Polynomial.mem_roots'.mp hr).2)
  rw [hp.eq_prod_roots_of_monic hpmon, ← hq, Polynomial.coeff_map]
  exact (q.coeff i).2

/-- Chevalley's extension theorem: for a field extension `K → L` and a valuation subring `O` of
`K`, there is a valuation subring of `L` whose comap along `algebraMap K L` is `O`. Generalizes
`LocalField.exists_valuationSubring_extends` (`Langlands.WeilGroup`), which fixes
`O = (valuation K).valuationSubring`. -/
theorem exists_valuationSubring_extends' {K L : Type*} [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring K) :
    ∃ A : ValuationSubring L, A.comap (algebraMap K L) = O := by
  set f : ↥O →+* L := (algebraMap K L).comp O.subtype with hf
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  haveI : IsLocalHom (f.codRestrict A.toSubring hA) := hloc
  refine ⟨A, ValuationSubring.ext _ _ fun x => ?_⟩
  rw [ValuationSubring.mem_comap]
  constructor
  · intro hx
    by_contra hxO
    have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
    have hxinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
    set b : ↥O := ⟨x⁻¹, hxinv⟩ with hb
    have hfb : f b ∈ A.toSubring := hA b
    have hfb' : f b = (algebraMap K L x)⁻¹ := by
      show (algebraMap K L) x⁻¹ = (algebraMap K L x)⁻¹
      exact map_inv₀ _ _
    have hne : algebraMap K L x ≠ 0 :=
      (map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective).mpr hx0
    have hub : IsUnit (f.codRestrict A.toSubring hA b) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L x, hx⟩, Subtype.ext ?_⟩
      show f b * algebraMap K L x = 1
      rw [hfb', inv_mul_cancel₀ hne]
    have hbunit : IsUnit b := IsLocalHom.map_nonunit b hub
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hbunit
    have hcx : (c : K) = x := by
      have hbc : (b : K) * (c : K) = 1 := congrArg Subtype.val hc
      rw [hb] at hbc
      show (c : K) = x
      field_simp at hbc
      rw [hbc]
    exact hxO (hcx ▸ c.2)
  · intro hxO
    exact hA ⟨x, hxO⟩

/-- Let `Kv` be a complete nontrivially normed nonarchimedean field and `Lw / Kv` a finite
extension. If `B` is a valuation subring of `Lw` comapping to `Ov := (valuation Kv).valuationSubring`,
then every `x ∈ B` is integral over `Ov`; that is, `B` is contained in the integral closure of
`Ov` in `Lw` (Serre, *Local Fields*, Ch. II §2). See the section docstring for the argument. -/
theorem isIntegral_of_mem_of_comap_eq {Kv Lw : Type*} [NontriviallyNormedField Kv]
    [IsUltrametricDist Kv] [ValuativeRel Kv] [(NormedField.valuation (K := Kv)).Compatible]
    [CompleteSpace Kv] [Field Lw] [Algebra Kv Lw] [FiniteDimensional Kv Lw]
    (B : ValuationSubring Lw)
    (hB : B.comap (algebraMap Kv Lw) = (ValuativeRel.valuation Kv).valuationSubring)
    {x : Lw} (hx : x ∈ B) : IsIntegral (ValuativeRel.valuation Kv).valuationSubring x := by
  set O := (ValuativeRel.valuation Kv).valuationSubring with hOdef
  rcases eq_or_ne x 0 with rfl | hx0
  · exact isIntegral_zero
  haveI : Algebra.IsAlgebraic Kv Lw := Algebra.IsAlgebraic.of_finite _ _
  haveI : IsAlgClosure Kv (AlgebraicClosure Lw) :=
    IsAlgClosure.ofAlgebraic Kv Lw (AlgebraicClosure Lw)
  haveI : Normal Kv (AlgebraicClosure Lw) := IsAlgClosure.normal Kv (AlgebraicClosure Lw)
  set N := IntermediateField.normalClosure Kv Lw (AlgebraicClosure Lw) with hN
  haveI : Normal Kv N := normalClosure.normal Kv Lw (AlgebraicClosure Lw)
  letI : Algebra Lw N := normalClosure.algebra Kv Lw (AlgebraicClosure Lw)
  set x' : N := algebraMap Lw N x with hx'def
  have hx'0 : x' ≠ 0 := by
    rw [hx'def, Ne, map_eq_zero_iff _ (algebraMap Lw N).injective]
    exact hx0
  -- The unique valuation subring of `N` extending `O`.
  obtain ⟨A, hA⟩ := exists_valuationSubring_extends' (K := Kv) (L := N) O
  have hAfix : ∀ σ : N ≃ₐ[Kv] N, σ • A = A := by
    intro σ
    have h1 : (σ • A).comap (algebraMap Kv N) = O :=
      (ValuationSubring.comap_smul_eq σ A).trans hA
    exact LocalField.valuationSubring_eq_of_comap_eq Kv h1 hA
  have hcomap_ι : A.comap (algebraMap Lw N) = B := by
    apply LocalField.valuationSubring_eq_of_comap_eq Kv
    · show (A.comap (algebraMap Lw N)).comap (algebraMap Kv Lw) = O
      rw [ValuationSubring.comap_comap]
      have heq : (algebraMap Lw N).comp (algebraMap Kv Lw) = algebraMap Kv N :=
        (IsScalarTower.algebraMap_eq Kv Lw N).symm
      rw [heq, hA]
    · exact hB
  have hx'A : x' ∈ A := by
    rw [← ValuationSubring.mem_comap (A := A) (f := algebraMap Lw N), hcomap_ι]
    exact hx
  have hxi : IsIntegral Kv x' := Algebra.IsIntegral.isIntegral x'
  have hroots : ∀ r : N, ((minpoly Kv x').map (algebraMap Kv N)).IsRoot r → r ∈ A.toSubring := by
    intro r hr
    have hconj : IsConjRoot Kv x' r := by
      apply isConjRoot_of_aeval_eq_zero hxi
      rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hr
    obtain ⟨σ, hσ⟩ := hconj.symm.exists_algEquiv
    have hfix := hAfix σ
    have hiff : (σ x' : N) ∈ σ • A ↔ x' ∈ A := by
      simp [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    rw [hfix] at hiff
    rw [← hσ]
    exact hiff.mpr hx'A
  have hcoeffs : ∀ i, ((minpoly Kv x').map (algebraMap Kv N)).coeff i ∈ A.toSubring :=
    coeff_mem_subring_of_splits A.toSubring ((minpoly.monic hxi).map (algebraMap Kv N))
      (Normal.splits inferInstance x') hroots
  have hcoeffs' : ∀ i, (minpoly Kv x').coeff i ∈ O := by
    intro i
    have hmem := hcoeffs i
    rw [Polynomial.coeff_map] at hmem
    have : (minpoly Kv x').coeff i ∈ A.comap (algebraMap Kv N) :=
      (ValuationSubring.mem_comap (A := A) (f := algebraMap Kv N)).mpr hmem
    rwa [hA] at this
  -- Transfer to `minpoly Kv x` (equal to `minpoly Kv x'` since `algebraMap Lw N` is injective).
  have hminpoly_eq : minpoly Kv x' = minpoly Kv x :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom Kv Lw N) (algebraMap Lw N).injective x
  rw [hminpoly_eq] at hcoeffs'
  -- Assemble the monic polynomial over `O` witnessing integrality.
  have hsub : (↑(minpoly Kv x).coeffs : Set Kv) ⊆ O.toSubring := by
    intro c hc
    simp only [Polynomial.coeffs, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Polynomial.mem_support_iff] at hc
    obtain ⟨n, _, rfl⟩ := hc
    exact hcoeffs' n
  have hxi_x : IsIntegral Kv x := Algebra.IsIntegral.isIntegral x
  refine ⟨(minpoly Kv x).toSubring O.toSubring hsub, ?_, ?_⟩
  · exact (Polynomial.monic_toSubring _ _ _).mpr (minpoly.monic hxi_x)
  · show Polynomial.eval₂ (algebraMap (↥O) Lw) x ((minpoly Kv x).toSubring O.toSubring hsub) = 0
    rw [IsScalarTower.algebraMap_eq (↥O) Kv Lw,
      ← Polynomial.eval₂_map, show algebraMap (↥O) Kv = O.toSubring.subtype from rfl,
      Polynomial.map_toSubring _ O.toSubring hsub]
    exact minpoly.aeval Kv x

end IntegralClosure

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-- The ring hom `v.adicCompletion K →+* w.adicCompletion L` induced by `algebraMap K L`, for a
place `w` of `S` lying over a place `v` of `R`. Built by extending the uniformly continuous map
`algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))`
(`uniformContinuous_algebraMap_liesOver`) to the completions, then transporting along the
identification of `adicCompletion` with the completion of the valued field
(`adicCompletion.equiv`). -/
def adicCompletionComap : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)

/-- The `v.adicCompletion K`-algebra structure on `w.adicCompletion L` induced by
`adicCompletionComap`, for a place `w` of `S` lying over a place `v` of `R`. -/
instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionComap K L v w).toAlgebra

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- `adicCompletionComap` is continuous, being a composite of `UniformSpace.Completion.map` with
the homeomorphisms `adicCompletion.equiv`. -/
theorem continuous_adicCompletionComap : Continuous (adicCompletionComap K L v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- `adicCompletionComap` agrees, on the image of `K`, with `algebraMap K (w.adicCompletion L)`
composed through `algebraMap K L`. This is the compatibility fact needed for
`IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)`. -/
theorem adicCompletionComap_algebraMap (x : K) :
    adicCompletionComap K L v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  apply (adicCompletion.equiv L w).injective
  simp only [adicCompletionComap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, adicCompletion.equiv_apply,
    algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.coe_mapRingHom,
    UniformSpace.Completion.map_coe (uniformContinuous_algebraMap_liesOver K L v w)]
  exact congrArg _ <|
    (IsScalarTower.algebraMap_apply K (WithVal (v.valuation K)) (WithVal (w.valuation L)) x).symm.trans
      (IsScalarTower.algebraMap_apply K L (WithVal (w.valuation L)) x)

/-- The scalar tower `K → v.adicCompletion K → w.adicCompletion L`, for a place `w` of `S` lying
over a place `v` of `R`. -/
instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x => (adicCompletionComap_algebraMap K L v w x).symm

/-- `v.adicCompletion K` acts continuously on `w.adicCompletion L`, via `adicCompletionComap`. -/
instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul :=
    (continuous_adicCompletionComap K L v w).comp continuous_fst |>.mul continuous_snd

open scoped TensorProduct Valued in
/-- `w.adicCompletion L` is a finite `v.adicCompletion K`-module. The multiplication map
`Φ : Kv ⊗[K] L →ₗ[Kv] Lw` has dense range (`w.denseRange_algebraMap L`), and its range is
finite-dimensional over `Kv`, hence closed; so `Φ` is surjective.

This is `NumberField.HeightOneSpectrum.instModuleFiniteAdicCompletion` with the `NumberField`
hypotheses relaxed to `Module.Finite K L` and the instances above. -/
instance : Module.Finite (v.adicCompletion K) (w.adicCompletion L) :=
  let Φ : v.adicCompletion K ⊗[K] L →ₗ[v.adicCompletion K] w.adicCompletion L :=
    Algebra.TensorProduct.lift (Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L)) (Algebra.algHom K L (w.adicCompletion L))
      (fun _ _ => mul_comm ..) |>.toLinearMap
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, Algebra.algHom]⟩
  .of_surjective Φ (by
    rw [← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range)

/-- `w.adicCompletion L` is algebraic over `v.adicCompletion K`, being a finite extension. This is
one of the hypotheses of `LocalField.valuationSubring_eq_of_comap_eq`
(`Langlands.HenselianValuation`). -/
instance : Algebra.IsAlgebraic (v.adicCompletion K) (w.adicCompletion L) :=
  .of_finite _ _

/-- The local norm map `N_{L_w/K_v} : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ` at a place
`w` of `S` lying over a place `v` of `R`: the field norm of `w.adicCompletion L` over
`v.adicCompletion K`, transported to units via `Units.map`. This is the local factor at `w` of the
idèle norm map `N_{L/K} a = (∏_{w ∣ v} N_{L_w/K_v}(a_w))_v`. -/
def localNormMap : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (Algebra.norm (v.adicCompletion K) : w.adicCompletion L →* v.adicCompletion K)

/-- Only finitely many places `w` of `S` lie over a given place `v` of `R`: the set
`{w // w.asIdeal.LiesOver v.asIdeal}` injects into `v.asIdeal.primesOver S`
(via `w ↦ w.asIdeal`), which is finite since `v.asIdeal` is a nonzero (hence maximal, by
`IsDedekindDomain.HeightOneSpectrum.isMaximal`) ideal of the Dedekind domain `R` and `S / R` is
integral (`IsDedekindDomain.primesOver_finite`). -/
theorem finite_liesOver (v : HeightOneSpectrum R) :
    {w : HeightOneSpectrum S | w.asIdeal.LiesOver v.asIdeal}.Finite := by
  have hsub : (fun w : HeightOneSpectrum S => w.asIdeal) ''
      {w : HeightOneSpectrum S | w.asIdeal.LiesOver v.asIdeal} ⊆ v.asIdeal.primesOver S := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, hw⟩
  exact Set.Finite.of_finite_image
    (Set.Finite.subset (IsDedekindDomain.primesOver_finite v.asIdeal S) hsub)
    (HeightOneSpectrum.asIdeal_injective.injOn)

/-- The valuation subring of `ValuativeRel.valuation (v.adicCompletion K)` is
`v.adicCompletionIntegers K`. Both that valuation and `Valued.v` are `Compatible` with
`instValuativeRelValuedAdicCompletion`, hence equivalent, hence have the same valuation subring.
This transfers `isIntegral_of_mem_of_comap_eq`, stated for `ValuativeRel.valuation`, to
`v.adicCompletionIntegers K`. -/
theorem valuation_valuationSubring_eq_adicCompletionIntegers :
    (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring
      = v.adicCompletionIntegers K := by
  show (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring = Valued.v.valuationSubring
  rw [← Valuation.isEquiv_iff_valuationSubring]
  exact ValuativeRel.isEquiv _ _

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- `adicCompletionComap` pulls `w.adicCompletionIntegers L` back exactly to
`v.adicCompletionIntegers K`.

Writing `e` for the ramification index of `w` over `v`, the continuous maps
`y ↦ Valued.v (adicCompletionComap y)` and `y ↦ Valued.v y ^ e` agree on the dense image of `K`
(`valuation_liesOver`), hence everywhere. Since `e ≠ 0`, raising to the `e`-th power preserves
`≤ 1`. -/
theorem adicCompletionIntegers_comap_eq :
    (w.adicCompletionIntegers L).comap (adicCompletionComap K L v w)
      = v.adicCompletionIntegers K := by
  set e := v.asIdeal.ramificationIdx' w.asIdeal with hedef
  have he0 : e ≠ 0 := Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  have hcont1 :
      Continuous (fun y : v.adicCompletion K => Valued.v (adicCompletionComap K L v w y)) :=
    (Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective L w)).comp
      (continuous_adicCompletionComap K L v w)
  have hcont2 : Continuous (fun y : v.adicCompletion K => (Valued.v y) ^ e) :=
    (Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K v)).pow e
  have hden : DenseRange (algebraMap K (v.adicCompletion K)) := denseRange_algebraMap K v
  have hcomp : (fun y : v.adicCompletion K => Valued.v (adicCompletionComap K L v w y))
      ∘ (algebraMap K (v.adicCompletion K)) =
      (fun y : v.adicCompletion K => (Valued.v y) ^ e) ∘ (algebraMap K (v.adicCompletion K)) := by
    funext k
    simp only [Function.comp_apply, adicCompletionComap_algebraMap]
    rw [show (algebraMap L (adicCompletion L w) (algebraMap K L k))
        = ((algebraMap K L k : L) : adicCompletion L w) from rfl,
      show (algebraMap K (adicCompletion K v) k) = ((k : K) : adicCompletion K v) from rfl,
      valuedAdicCompletion_eq_valuation', valuedAdicCompletion_eq_valuation',
      valuation_liesOver L v w]
  have heq : ∀ y : v.adicCompletion K,
      Valued.v (adicCompletionComap K L v w y) = (Valued.v y) ^ e :=
    congrFun (hden.equalizer hcont1 hcont2 hcomp)
  ext y
  rw [ValuationSubring.mem_comap, mem_adicCompletionIntegers, mem_adicCompletionIntegers, heq]
  exact pow_le_one_iff_of_nonneg zero_le he0

omit [Algebra.IsIntegral R S] in
/-- The local norm map sends local units to local units: if `a` is a unit of
`w.adicCompletionIntegers L`, then `N_{L_w/K_v}(a)` is a unit of `v.adicCompletionIntegers K`.

By `isIntegral_of_mem_of_comap_eq` (via `adicCompletionIntegers_comap_eq` and
`valuation_valuationSubring_eq_adicCompletionIntegers`), both `a` and `a⁻¹` are integral over
`v.adicCompletionIntegers K`, hence so are their norms (`Algebra.isIntegral_norm`). A valuation
subring is integrally closed in its fraction field, so both norms lie in
`v.adicCompletionIntegers K`. -/
theorem localNormMap_mem_units {a : (w.adicCompletion L)ˣ}
    (ha : a ∈ (w.adicCompletionIntegers L).units) :
    localNormMap K L v w a ∈ (v.adicCompletionIntegers K).units := by
  have hbridge := valuation_valuationSubring_eq_adicCompletionIntegers K v
  have hcomap : (w.adicCompletionIntegers L).comap (adicCompletionComap K L v w)
      = (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring := by
    rw [hbridge]; exact adicCompletionIntegers_comap_eq K L v w
  have h1 : IsIntegral (v.adicCompletionIntegers K) (a : w.adicCompletion L) := by
    have := isIntegral_of_mem_of_comap_eq (w.adicCompletionIntegers L) hcomap
      (x := (a : w.adicCompletion L)) (Submonoid.val_mem_of_mem_units _ ha)
    rwa [hbridge] at this
  have h2 : IsIntegral (v.adicCompletionIntegers K)
      ((a⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) := by
    have := isIntegral_of_mem_of_comap_eq (w.adicCompletionIntegers L) hcomap
      (x := ((a⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L))
      (Submonoid.inv_val_mem_of_mem_units _ ha)
    rwa [hbridge] at this
  have hn1 := Algebra.isIntegral_norm (R := v.adicCompletionIntegers K) (v.adicCompletion K) h1
  have hn2 := Algebra.isIntegral_norm (R := v.adicCompletionIntegers K) (v.adicCompletion K) h2
  obtain ⟨y1, hy1⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hn1
  obtain ⟨y2, hy2⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hn2
  refine Submonoid.mem_units_of_val_mem_inv_val_mem _ ?_ ?_
  · show Algebra.norm (v.adicCompletion K) (a : w.adicCompletion L) ∈
      (v.adicCompletionIntegers K).toSubmonoid
    exact hy1 ▸ y1.2
  · rw [← map_inv]
    show Algebra.norm (v.adicCompletion K) ((a⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈
      (v.adicCompletionIntegers K).toSubmonoid
    exact hy2 ▸ y2.2

/-- Let `a : ∀ w, (w.adicCompletion L)ˣ` be a family of local units that is a unit of
`w.adicCompletionIntegers L` for cofinitely many `w`, i.e. the restricted-product condition
defining a finite idèle of `L`. Then for cofinitely many places `v` of `R`, the local norm
`N_{L_w/K_v}(a w)` is a unit of `v.adicCompletionIntegers K` for every `w` lying over `v`.

Each `w` lies over a unique `v`, namely `HeightOneSpectrum.under R w`, so the exceptional places
`v` are contained in the image under `HeightOneSpectrum.under R` of the finitely many exceptional
places `w`. The pointwise statement is `localNormMap_mem_units`. -/
theorem eventually_localNormMap_mem_units
    {a : ∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ}
    (ha : ∀ᶠ w : HeightOneSpectrum S in Filter.cofinite,
      a w ∈ (w.adicCompletionIntegers L).units) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ∀ w : HeightOneSpectrum S, ∀ _ : w.asIdeal.LiesOver v.asIdeal,
        localNormMap K L v w (a w) ∈ (v.adicCompletionIntegers K).units := by
  rw [Filter.eventually_cofinite] at ha ⊢
  refine Set.Finite.subset (ha.image (HeightOneSpectrum.under R)) fun v hv => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hw, hcontra⟩ := hv
  haveI := hw
  have hveq : v = HeightOneSpectrum.under R w := HeightOneSpectrum.ext hw.over
  exact ⟨w, mt (localNormMap_mem_units K L v w) hcontra, hveq.symm⟩

end IsDedekindDomain.HeightOneSpectrum

section FiniteIdeleNormMap

/-! ### Assembling the finite-place local norms into a finite idèle norm map

`NumberField.FiniteIdeleGroup.normMap : FiniteIdeleGroup S L →* FiniteIdeleGroup R K` takes, at
each place `v` of `R`, the product of `IsDedekindDomain.HeightOneSpectrum.localNormMap` over the
finitely many (`finite_liesOver`) places `w` of `S` lying over `v`. That this respects the
restricted-product condition is `eventually_localNormMap_mem_units`. -/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L)

/-- Unpacks membership in the `attach`ed `Finset` of places `w` of `S` lying over a place `v` of
`R` into a `LiesOver` instance.

Stated separately rather than inlined as `(Set.Finite.mem_toFinset _).mp w.2`, whose implicit
arguments are not determined early enough at the use sites below. -/
theorem mem_liesOver_of_mem_toFinset {v : HeightOneSpectrum R}
    (w : {x : HeightOneSpectrum S // x ∈ (finite_liesOver (R := R) (S := S) v).toFinset}) :
    (w : HeightOneSpectrum S).asIdeal.LiesOver v.asIdeal := by
  have hw := w.2
  rwa [Set.Finite.mem_toFinset] at hw

/-- The `v`-component of the finite-place idèle norm map: the product of the local norms
`N_{L_w/K_v}(a w)` over the (finitely many) places `w` of `S` lying over `v`. -/
noncomputable def finiteNormMapComponent (v : HeightOneSpectrum R)
    (a : ∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ) : (v.adicCompletion K)ˣ :=
  ∏ w ∈ (finite_liesOver (R := R) (S := S) v).toFinset.attach,
    haveI := mem_liesOver_of_mem_toFinset w
    localNormMap K L v (w : HeightOneSpectrum S) (a w)

omit [Module.Finite K L] in
theorem finiteNormMapComponent_one (v : HeightOneSpectrum R) :
    finiteNormMapComponent (R := R) (S := S) K L v 1 = 1 := by
  unfold finiteNormMapComponent
  refine Finset.prod_eq_one fun w _ => ?_
  haveI := mem_liesOver_of_mem_toFinset w
  exact map_one _

omit [Module.Finite K L] in
theorem finiteNormMapComponent_mul (v : HeightOneSpectrum R)
    (a b : ∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ) :
    finiteNormMapComponent K L v (a * b) =
      finiteNormMapComponent K L v a * finiteNormMapComponent K L v b := by
  unfold finiteNormMapComponent
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  haveI := mem_liesOver_of_mem_toFinset w
  exact map_mul (localNormMap K L v (w : HeightOneSpectrum S)) (a w) (b w)

/-- The finite-place idèle norm map on the unrestricted product of local unit groups. It descends
to the restricted product, and hence to `NumberField.FiniteIdeleGroup.normMap`, by
`eventually_finiteNormMap_mem_units`. -/
def finiteNormMap : (∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ) →*
    ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ where
  toFun a v := finiteNormMapComponent K L v a
  map_one' := funext fun v => finiteNormMapComponent_one K L v
  map_mul' a b := funext fun v => finiteNormMapComponent_mul K L v a b

/-- If a family of local units `a` at places of `S` satisfies the restricted-product condition
defining a finite idèle of `L`, then so does its image under `finiteNormMap` at places of `R`.
This is `eventually_localNormMap_mem_units` together with closure of the local units under finite
products. -/
theorem eventually_finiteNormMap_mem_units
    {a : ∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ}
    (ha : ∀ᶠ w : HeightOneSpectrum S in Filter.cofinite,
      a w ∈ (w.adicCompletionIntegers L).units) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      finiteNormMap K L a v ∈ (v.adicCompletionIntegers K).units := by
  filter_upwards [eventually_localNormMap_mem_units K L ha] with v hv
  unfold finiteNormMap finiteNormMapComponent
  refine Subgroup.prod_mem _ fun w _ => ?_
  exact hv (w : HeightOneSpectrum S) (mem_liesOver_of_mem_toFinset w)

end FiniteIdeleNormMap

namespace NumberField.FiniteIdeleGroup

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L)

/-- `finiteNormMap` as a `MonoidHom` between restricted products of local unit groups, the form
that composes with `RestrictedProduct.unitsEquiv` to give `normMap` below. -/
def finiteNormMapRestricted :
    (Πʳ w : HeightOneSpectrum S, [(w.adicCompletion L)ˣ,
        (Submonoid.ofClass (w.adicCompletionIntegers L)).units]_[Filter.cofinite]) →*
      Πʳ v : HeightOneSpectrum R, [(v.adicCompletion K)ˣ,
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[Filter.cofinite] where
  toFun y := ⟨finiteNormMap K L y.1, eventually_finiteNormMap_mem_units K L y.2⟩
  map_one' := Subtype.ext (map_one (finiteNormMap K L))
  map_mul' y1 y2 := Subtype.ext (map_mul (finiteNormMap K L) y1.1 y2.1)

/-- The finite-place idèle norm map `N_{L/K} : FiniteIdeleGroup S L →* FiniteIdeleGroup R K`,
sending a finite idèle `a` to the finite idèle whose component at each place `v` of `R` is
`∏_{w ∣ v} N_{L_w/K_v}(a w)`. Built by conjugating `finiteNormMapRestricted` by
`RestrictedProduct.unitsEquiv` on each side. -/
noncomputable def normMap : FiniteIdeleGroup S L →* FiniteIdeleGroup R K :=
  (RestrictedProduct.unitsEquiv fun v : HeightOneSpectrum R => v.adicCompletion K).symm.toMonoidHom.comp
    ((finiteNormMapRestricted K L).comp
      (RestrictedProduct.unitsEquiv fun w : HeightOneSpectrum S => w.adicCompletion L).toMonoidHom)

end NumberField.FiniteIdeleGroup

section InfinitePlaceNorm

/-! ### The archimedean local norm map

`NumberField.InfinitePlace.localNormMap` is the archimedean analogue of
`IsDedekindDomain.HeightOneSpectrum.localNormMap`. No companion unit-preservation lemma is needed:
`InfiniteAdeleRing K := (v : InfinitePlace K) → v.Completion` is an unrestricted product, with no
archimedean analogue of `adicCompletionIntegers` and hence no support condition. Finiteness of the
set of places above a given place is likewise immediate, `InfinitePlace K` being a `Fintype` for
a number field `K`. -/

namespace NumberField.InfinitePlace

open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1]

/-- The local norm map `N_{L_w/K_v} : (w.Completion)ˣ →* (v.Completion)ˣ` at an infinite place `w`
of `L` lying over an infinite place `v` of `K`: the field norm of `w.Completion` over
`v.Completion`, transported to units via `Units.map`. The extension has degree `1` or `2`
according as `w` is unramified or ramified over `v`. The algebra structure is
`NumberField.LiesOver.completionMap`
(`Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances`). -/
noncomputable def localNormMap : (w.Completion)ˣ →* (v.Completion)ˣ :=
  Units.map (Algebra.norm (v.Completion) : w.Completion →* v.Completion)

end NumberField.InfinitePlace

end InfinitePlaceNorm

section InfiniteIdeleNormMap

/-! ### Assembling the archimedean local norms into an infinite idèle norm map

`NumberField.InfiniteIdeleGroup.normMap : InfiniteIdeleGroup L →* InfiniteIdeleGroup K` mirrors
`FiniteIdeleGroup.normMap`. Since `InfiniteAdeleRing` is an unrestricted product there is no
analogue of `eventually_finiteNormMap_mem_units`, and the assembly uses `MulEquiv.piUnits` in
place of `RestrictedProduct.unitsEquiv`. -/

open NumberField NumberField.InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

omit [NumberField K] in
/-- Unpacks membership in the `attach`ed `Finset` of infinite places `w` of `L` lying over a place
`v` of `K` into a `LiesOver` instance; the archimedean analogue of
`mem_liesOver_of_mem_toFinset`. -/
theorem mem_liesOver_of_mem_placesOver_toFinset {v : InfinitePlace K}
    (w : {x : InfinitePlace L // x ∈ (Set.toFinite (placesOver L v)).toFinset}) :
    (w : InfinitePlace L).1.LiesOver v.1 := by
  have hw := w.2
  rwa [Set.Finite.mem_toFinset] at hw

/-- The `v`-component of the archimedean idèle norm map: the product of the local norms
`N_{L_w/K_v}(a w)` over the (finitely many) places `w` of `L` lying over `v`. -/
noncomputable def infiniteNormMapComponent (v : InfinitePlace K)
    (a : ∀ w : InfinitePlace L, (w.Completion)ˣ) : (v.Completion)ˣ :=
  ∏ w ∈ (Set.toFinite (placesOver L v)).toFinset.attach,
    haveI := mem_liesOver_of_mem_placesOver_toFinset w
    NumberField.InfinitePlace.localNormMap v (w : InfinitePlace L) (a w)

omit [NumberField K] in
theorem infiniteNormMapComponent_one (v : InfinitePlace K) :
    infiniteNormMapComponent (L := L) v 1 = 1 := by
  unfold infiniteNormMapComponent
  refine Finset.prod_eq_one fun w _ => ?_
  haveI := mem_liesOver_of_mem_placesOver_toFinset w
  exact map_one _

omit [NumberField K] in
theorem infiniteNormMapComponent_mul (v : InfinitePlace K)
    (a b : ∀ w : InfinitePlace L, (w.Completion)ˣ) :
    infiniteNormMapComponent v (a * b) =
      infiniteNormMapComponent v a * infiniteNormMapComponent v b := by
  unfold infiniteNormMapComponent
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  haveI := mem_liesOver_of_mem_placesOver_toFinset w
  exact map_mul (NumberField.InfinitePlace.localNormMap v (w : InfinitePlace L)) (a w) (b w)

/-- The archimedean idèle norm map on the product of local unit groups; transported to
`NumberField.InfiniteIdeleGroup.normMap` via `MulEquiv.piUnits`. -/
def infiniteNormMap : (∀ w : InfinitePlace L, (w.Completion)ˣ) →*
    ∀ v : InfinitePlace K, (v.Completion)ˣ where
  toFun a v := infiniteNormMapComponent v a
  map_one' := funext fun v => infiniteNormMapComponent_one v
  map_mul' a b := funext fun v => infiniteNormMapComponent_mul v a b

end InfiniteIdeleNormMap

namespace NumberField.InfiniteIdeleGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

variable (K L)

/-- The archimedean idèle norm map `N_{L/K} : InfiniteIdeleGroup L →* InfiniteIdeleGroup K`,
sending an infinite idèle `a` to the infinite idèle whose component at each place `v` of `K` is
`∏_{w ∣ v} N_{L_w/K_v}(a w)`. Built by conjugating `infiniteNormMap` by `MulEquiv.piUnits` on
each side. -/
noncomputable def normMap : InfiniteIdeleGroup L →* InfiniteIdeleGroup K :=
  (MulEquiv.piUnits (M := fun v : InfinitePlace K => v.Completion)).symm.toMonoidHom.comp
    ((infiniteNormMap (K := K) (L := L)).comp
      (MulEquiv.piUnits (M := fun w : InfinitePlace L => w.Completion)).toMonoidHom)

end NumberField.InfiniteIdeleGroup

namespace NumberField

variable (R S K L : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
  [NumberField K] [NumberField L]

/-- The idèle norm map `N_{L/K} : IdeleGroup S L →* IdeleGroup R K` for a finite extension
`L / K` (of fraction fields of Dedekind domains `S / R`), sending an idèle `a` to the idèle
whose component at each place `v` of `K` is `∏_{w ∣ v} N_{L_w/K_v}(a_w)`. Assembled from the
finite-place half (`FiniteIdeleGroup.normMap`) and the archimedean half
(`InfiniteIdeleGroup.normMap`) via the splitting `IdeleGroup.equivProd`. Defined here rather than
in `Langlands/IdeleGroup.lean` to avoid a circular import, the construction needing the local norm
maps built in this file. -/
noncomputable def IdeleGroup.normMap : IdeleGroup S L →* IdeleGroup R K :=
  (IdeleGroup.equivProd R K).symm.toMonoidHom.comp
    ((MonoidHom.prodMap (InfiniteIdeleGroup.normMap K L) (FiniteIdeleGroup.normMap K L)).comp
      (IdeleGroup.equivProd S L).toMonoidHom)

end NumberField

end
