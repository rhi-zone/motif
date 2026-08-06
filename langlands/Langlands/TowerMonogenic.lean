/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.ArtinianPrimitiveElement
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Serre's tower step for monogenicity

`Langlands.ArtinianPrimitiveElement.LocalField.exists_adjoin_eq_top_of_residue_nilpotent` is the
composite monogenicity criterion in residue-algebra form: for `R` local and `S` finite over `R`, if
`S ⧸ 𝔪_R S` contains a finite separable residue field `κ` and a nilpotent `π` with
`S ⧸ 𝔪_R S = κ + π · (S ⧸ 𝔪_R S)`, then `S` is monogenic over `R`.

This file discharges those hypotheses for a *tower* `R ⊆ OM ⊆ ON` of local rings in which

* `OM / R` is unramified — `𝔪_R · OM = 𝔪_OM` — with separable residue extension, and
* `ON / OM` is generated over `OM` by a single element `π` (`ON = OM + π · ON`) some power of which
  lies in `𝔪_OM · ON`.

These are exactly the two halves of Serre's *Local Fields* Ch. III tower argument: the first is what
`Langlands.UnramifiedExtension.HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv`
now exports, the second is what an Eisenstein/totally-ramified extension supplies (see
`Langlands.TotallyRamifiedEisensteinTower`).

## Main results

* `LocalField.map_maximalIdeal_eq_of_unramified` : `𝔪_OM · ON = 𝔪_R · ON` when `𝔪_R · OM = 𝔪_OM`.
  This is the only place unramifiedness of the lower step is used, and it is what makes
  `ON ⧸ 𝔪_R ON` a `κ_OM`-algebra at all.
* `LocalField.exists_adjoin_eq_top_of_tower` : `∃ γ : ON, Algebra.adjoin R {γ} = ⊤`.

## Implementation notes

The `κ_OM`-algebra structure on `ON ⧸ 𝔪_R ON` is not an instance — it depends on the unramifiedness
hypothesis — so it is introduced by `letI` inside the proof, as `Ideal.Quotient.lift` of
`ON ⧸ 𝔪_R ON`'s quotient map precomposed with `algebraMap OM ON`. The `IsScalarTower` over
`ResidueField R` then has to be checked by hand.
-/

open IsLocalRing

namespace LocalField

variable {R OM ON : Type*} [CommRing R] [IsLocalRing R] [CommRing OM] [IsLocalRing OM]
  [CommRing ON] [Algebra R OM] [Algebra OM ON] [Algebra R ON] [IsScalarTower R OM ON]

/-- **Unramifiedness of the lower step propagates to the top.** If `𝔪_R · OM = 𝔪_OM` then
`𝔪_OM · ON = 𝔪_R · ON`, so the two candidate "residue algebras" of `ON` coincide. -/
theorem map_maximalIdeal_eq_of_unramified
    (hunram : Ideal.map (algebraMap R OM) (maximalIdeal R) = maximalIdeal OM) :
    Ideal.map (algebraMap OM ON) (maximalIdeal OM) =
      Ideal.map (algebraMap R ON) (maximalIdeal R) := by
  rw [← hunram, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **Serre's tower step.** For a tower `R ⊆ OM ⊆ ON` of local rings with `ON` finite over `R`,
`OM / R` unramified with separable residue extension, and `ON` generated over `OM` by an element
`π` some power of which lies in `𝔪_OM · ON`, the ring `ON` is monogenic over `R`.

The single generator is `β + π` for `β` a lift to `ON` of a primitive element of
`κ_OM / κ_R` — see `LocalField.adjoin_add_nilpotent_eq_top`, which is where the choice is made; here
only its existence form is used. -/
theorem exists_adjoin_eq_top_of_tower
    [IsLocalHom (algebraMap R OM)] [Module.Finite R OM] [Module.Finite R ON]
    [Algebra.IsSeparable (ResidueField R) (ResidueField OM)]
    (hunram : Ideal.map (algebraMap R OM) (maximalIdeal R) = maximalIdeal OM)
    {π : ON} {e : ℕ}
    (hnil : π ^ e ∈ Ideal.map (algebraMap OM ON) (maximalIdeal OM))
    (hsurj : ∀ x : ON, ∃ (c : OM) (y : ON), x = algebraMap OM ON c + π * y) :
    ∃ γ : ON, Algebra.adjoin R ({γ} : Set ON) = ⊤ := by
  set J : Ideal ON := Ideal.map (algebraMap R ON) (maximalIdeal R) with hJdef
  have hJ : Ideal.map (algebraMap OM ON) (maximalIdeal OM) = J :=
    map_maximalIdeal_eq_of_unramified hunram
  have hker : ∀ a ∈ maximalIdeal OM,
      ((Ideal.Quotient.mk J).comp (algebraMap OM ON)) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← hJ]
    exact Ideal.mem_map_of_mem _ ha
  letI : Algebra (ResidueField OM) (ON ⧸ J) :=
    RingHom.toAlgebra (Ideal.Quotient.lift (maximalIdeal OM)
      ((Ideal.Quotient.mk J).comp (algebraMap OM ON)) hker)
  have halg : ∀ c : OM,
      algebraMap (ResidueField OM) (ON ⧸ J) (residue OM c) =
        Ideal.Quotient.mk J (algebraMap OM ON c) := fun c =>
    Ideal.Quotient.lift_mk _ _ _
  -- `ResidueField R` is by definition `R ⧸ maximalIdeal R`, but instance search does not unfold
  -- the abbreviation, so the three residue-field instances have to be restated at the raw
  -- quotient — the form `exists_adjoin_eq_top_of_residue_nilpotent` takes them in.
  letI : Algebra (R ⧸ maximalIdeal R) (ResidueField OM) :=
    inferInstanceAs (Algebra (ResidueField R) (ResidueField OM))
  haveI : Algebra.IsSeparable (R ⧸ maximalIdeal R) (ResidueField OM) :=
    inferInstanceAs (Algebra.IsSeparable (ResidueField R) (ResidueField OM))
  haveI : Module.Finite (R ⧸ maximalIdeal R) (ResidueField OM) :=
    inferInstanceAs (Module.Finite (ResidueField R) (ResidueField OM))
  haveI : IsScalarTower (R ⧸ maximalIdeal R) (ResidueField OM) (ON ⧸ J) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk J (algebraMap R ON x) =
      algebraMap (ResidueField OM) (ON ⧸ J) (residue OM (algebraMap R OM x))
    rw [halg, ← IsScalarTower.algebraMap_apply]
  refine exists_adjoin_eq_top_of_residue_nilpotent (R := R) (S := ON)
    (κ := ResidueField OM) (π := Ideal.Quotient.mk J π) (e := e) ?_ ?_
  · rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, ← hJ]
    exact hnil
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, y, hcy⟩ := hsurj x
    refine ⟨residue OM c, Ideal.Quotient.mk J y, ?_⟩
    rw [halg, ← map_mul, ← map_add, hcy]

/-! ### Discharging the upper step's two hypotheses from an Eisenstein generator

`exists_adjoin_eq_top_of_tower`'s `hsurj` and `hnil` are, for the totally ramified upper step,
consequences of `𝒪_N = 𝒪_M[π]` and Eisenstein-ness of `minpoly 𝒪_M π` respectively. Both are
general facts about algebras, stated here without any valuation-theoretic hypotheses. -/

/-- **`hsurj` from monogenicity.** If `S = A[π]` then every `x : S` is `c + π * y` with `c` in the
image of `A`. Immediate from `Algebra.adjoin_singleton_eq_range_aeval` and the polynomial
decomposition `p = X * p.divX + C (p.coeff 0)`. -/
theorem exists_add_mul_of_adjoin_eq_top {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    {π : S} (h : Algebra.adjoin A ({π} : Set S) = ⊤) (x : S) :
    ∃ (c : A) (y : S), x = algebraMap A S c + π * y := by
  have hx : x ∈ Algebra.adjoin A ({π} : Set S) := h ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, rfl⟩ := hx
  refine ⟨p.coeff 0, Polynomial.aeval π p.divX, ?_⟩
  conv_lhs => rw [← Polynomial.X_mul_divX_add p]
  simp [-Polynomial.X_mul_divX_add, add_comm]

/-- **`hnil` from Eisenstein-ness.** If `minpoly A π` is Eisenstein at `𝔪_A` then
`π ^ deg ∈ 𝔪_A · S`. This is `Polynomial.IsWeaklyEisensteinAt.
pow_natDegree_le_of_aeval_zero_of_monic_mem_map` specialised to the minimal polynomial. -/
theorem pow_natDegree_minpoly_mem_map {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S]
    [Algebra A S] {π : S} (hint : IsIntegral A π)
    (hEis : (minpoly A π).IsEisensteinAt (maximalIdeal A)) :
    π ^ (minpoly A π).natDegree ∈ Ideal.map (algebraMap A S) (maximalIdeal A) :=
  hEis.isWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_map
    (minpoly.aeval A π) (minpoly.monic hint) _ (Polynomial.natDegree_map_le)

/-- **Serre's tower theorem, in Eisenstein form.** For a tower `R ⊆ OM ⊆ ON` of local rings with
`ON` finite over `R`, `OM / R` unramified with separable residue extension, and `ON = OM[π]` for a
`π` whose minimal polynomial over `OM` is Eisenstein at `𝔪_OM` (i.e. `ON / OM` totally ramified),
`ON` is monogenic over `R`.

This is `exists_adjoin_eq_top_of_tower` with its two upper-step hypotheses replaced by the single
statement an Eisenstein extension supplies; `Langlands.TotallyRamifiedEisenstein`'s
`isEisensteinAt_minpoly_of_isUniformizer` and
`adjoin_eq_integralClosure_of_isUniformizer` produce exactly `hEis` and `hgen`, modulo the
`Algebra.adjoin`-of-a-subalgebra-versus-`⊤`-of-its-type step
(`adjoin_singleton_eq_top_of_adjoin_eq`). -/
theorem exists_adjoin_eq_top_of_tower_of_isEisensteinAt
    [IsLocalHom (algebraMap R OM)] [Module.Finite R OM] [Module.Finite R ON]
    [Algebra.IsSeparable (ResidueField R) (ResidueField OM)]
    (hunram : Ideal.map (algebraMap R OM) (maximalIdeal R) = maximalIdeal OM)
    {π : ON} (hint : IsIntegral OM π)
    (hEis : (minpoly OM π).IsEisensteinAt (maximalIdeal OM))
    (hgen : Algebra.adjoin OM ({π} : Set ON) = ⊤) :
    ∃ γ : ON, Algebra.adjoin R ({γ} : Set ON) = ⊤ :=
  exists_adjoin_eq_top_of_tower hunram (pow_natDegree_minpoly_mem_map hint hEis)
    (exists_add_mul_of_adjoin_eq_top hgen)

/-- **Passing a monogenicity statement from a subalgebra to its coercion to a type.** If
`Algebra.adjoin A {x} = S` as subalgebras of `B`, then `⟨x, _⟩` generates the whole of `↥S`. -/
theorem adjoin_singleton_eq_top_of_adjoin_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {S : Subalgebra A B} {x : B} (hx : x ∈ S) (h : Algebra.adjoin A ({x} : Set B) = S) :
    Algebra.adjoin A ({(⟨x, hx⟩ : S)} : Set S) = ⊤ := by
  apply Subalgebra.map_injective (f := S.val) Subtype.coe_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val,
    show (S.val : S →ₐ[A] B) '' ({(⟨x, hx⟩ : S)} : Set S) = ({x} : Set B) by simp]
  exact h

end LocalField
