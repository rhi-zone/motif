/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# An integral extension of a local ring is local once its "residual" quotient is

`ROADMAP.md` `§57` records residue-field preservation for the second Lubin-Tate tower step
(`O_{K_2} / O_{K_1}`) as blocked on `[IsLocalRing (integralClosure O_{K_1} (K_2 P₂))]`, an instance
`IsLocalRing.residueFieldEquivOfAdjoinSingleton` bakes directly into its hypotheses. Monogenicity of
`O_{K_2}` over `O_{K_1}` (`Langlands/LubinTateTowerStepMonogenic.lean`) does not by itself supply
`IsLocalRing`, and at this level `IsLocalRing` cannot be obtained the way it was at the `K → K_1`
level (`Langlands/MonogenicIntegralClosure.lean`'s `isDiscreteValuationRing_integralClosure`), because
that route needs a `ValuativeRel (K_1 P)` instance the whole `K_1 → K_2` arc was built to avoid
(`Langlands/LubinTateTowerStepMonogenic.lean`'s module docstring).

This file proves the classical "going-up" replacement instead, with **no valuation theory at all**:

> If `R` is local and `S` is integral over `R`, then `S` is local as soon as the quotient
> `S ⧸ (𝔪_R) S` is local.

## Main results

* `IsLocalRing.of_isIntegral_of_isLocalRing_quotient_map_maximalIdeal` : the general lemma above.
  `R` need not be a domain, `S` need not be a domain, and `𝔪_R S` need not be principal or generated
  by a single element — the only inputs are `[IsLocalRing R]`, `[Algebra.IsIntegral R S]`, and
  `[IsLocalRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))]`. This is more general than the
  route `ROADMAP.md §57` sketched (which assumed `S` a domain, going through
  `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` — that lemma, checked directly here, needs no
  domain hypothesis either) and than a nilpotence-specific argument (`S ⧸ 𝔪_R S` local is used as a
  black box; nothing about it being `κ[X]/(X^q)` or `π` being nilpotent enters this file at all).
* `IsLocalHom.algebraMap_of_isIntegral` : once `[IsLocalRing R] [IsLocalRing S] [Algebra.IsIntegral R
  S]` hold, `algebraMap R S` is automatically a local homomorphism — the maximal ideal of `S`
  contracts to the maximal ideal of `R` by the same going-up fact, so `IsLocalHom` costs nothing
  further once `IsLocalRing S` is in hand (whether obtained from the lemma above or otherwise).

## Proof idea

Every maximal ideal `M` of `S` contracts, by `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`, to a
maximal ideal of `R` — hence, `R` being local, to `𝔪_R` itself — so `M ⊇ 𝔪_R S =: J` for *every*
maximal ideal `M`, i.e. `J` lies in the Jacobson radical `Ideal.jacobson (⊥ : Ideal S)`. Given
`[IsLocalRing (S ⧸ J)]`, `S`'s local-ring criterion `IsLocalRing.of_isUnit_or_isUnit_one_sub_self`
reduces to: for `a : S`, since `S ⧸ J` is local, `mk a` or `1 - mk a` is a unit in `S ⧸ J`; lifting an
inverse `e` of the unit one and using `J ⊆ Jacobson(⊥ : Ideal S)`,
`Ideal.isUnit_of_sub_one_mem_jacobson_bot` promotes the *product* `a * e` (or `(1 - a) * e`) to a unit
of `S` itself, and `isUnit_of_mul_isUnit_left` then extracts that `a` (or `1 - a`) itself is a unit.
No Weierstrass/nilpotence argument for `S ⧸ J` is needed here — it is entirely the caller's job to
supply `[IsLocalRing (S ⧸ J)]`, however that quotient happens to be identified at a given
instantiation (e.g. `κ[X]/(X^q)` for `S` monogenic by an Eisenstein polynomial).
-/

open IsLocalRing

/-- **An integral extension of a local ring is local once its `𝔪_R`-quotient is.** `R` local,
`S` integral over `R`; if `S ⧸ (𝔪_R) S` is local, then `S` is local.

No domain hypothesis on `R` or `S` is needed: `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`
(the going-up fact every maximal ideal of `S` contracts to a maximal ideal of `R`) holds for
arbitrary commutative rings, not just domains. -/
theorem IsLocalRing.of_isIntegral_of_isLocalRing_quotient_map_maximalIdeal
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S]
    [IsLocalRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))] :
    IsLocalRing S := by
  set J : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R) with hJdef
  haveI : Nontrivial S := (Ideal.Quotient.mk_surjective (I := J)).nontrivial
  -- Every maximal ideal of `S` contains `J`, since it contracts to `R`'s unique maximal ideal.
  have hJmax : ∀ M : Ideal S, M.IsMaximal → J ≤ M := by
    intro M hM
    have hcomap : (M.comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    rw [hJdef, Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hcomap]
  have hJjac : J ≤ Ideal.jacobson (⊥ : Ideal S) :=
    le_sInf fun M hM => hJmax M hM.2
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Ideal.Quotient.mk J a) with h | h
  · obtain ⟨s, hs⟩ := h.exists_right_inv
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hme : Ideal.Quotient.mk J (a * e) = 1 := by rw [map_mul]; exact hs
    have hmem : a * e - 1 ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hme, map_one, sub_self]
    exact Or.inl (isUnit_of_mul_isUnit_left
      (Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJjac hmem)))
  · have h' : IsUnit (Ideal.Quotient.mk J (1 - a)) := by rw [map_sub, map_one]; exact h
    obtain ⟨s, hs⟩ := h'.exists_right_inv
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hme : Ideal.Quotient.mk J ((1 - a) * e) = 1 := by rw [map_mul]; exact hs
    have hmem : (1 - a) * e - 1 ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hme, map_one, sub_self]
    exact Or.inr (isUnit_of_mul_isUnit_left
      (Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJjac hmem)))

/-- **`algebraMap R S` is automatically a local homomorphism, for `R`, `S` local and `S` integral
over `R`.** The maximal ideal of `S` contracts (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`)
to a maximal ideal of `R`, hence — `R` being local — to `R`'s unique maximal ideal itself; that
equality is exactly one of the conditions `IsLocalRing.local_hom_TFAE` shows equivalent to
`IsLocalHom`. -/
theorem IsLocalHom.algebraMap_of_isIntegral
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [Algebra.IsIntegral R S] :
    IsLocalHom (algebraMap R S) := by
  have hcomap : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal S))
  exact ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 3 0).mp hcomap.ge
