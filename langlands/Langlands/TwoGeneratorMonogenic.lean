/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# `S = R[x, π]` for a residue-generating `x` and a uniformizer `π`

Serre's monogenicity theorem (*Local Fields* III §6) writes the ring of integers of a local field as
`𝒪_K[a]` for a *single* generator, and the classical route to it factors through the maximal
unramified subextension `L_0`, proving `𝒪_{L_0} = 𝒪_K[x]` (unramified half) and
`𝒪_L = 𝒪_{L_0}[π]` (Eisenstein half) separately. `ROADMAP.md`'s Phase 2b passes thirty-two to
thirty-four record the obstruction to that route in this repo: `L_0` is never available as an
actual subfield of the already-fixed `L`.

The observation this file rests on is that the consumer —
`ValuationSubring.mem_ramificationGroup_succ_of_adjoin`
(`Langlands.RamificationFiltration`) — does not need `L_0`, nor a single generator, nor an
Eisenstein polynomial. It needs only `Algebra.adjoin 𝒪_K {x, π} = ⊤` for the *pair* `(x, π)`, and
that is a direct Nakayama argument with no tower, no intermediate field and no discriminant:

* successive approximation `z ↦ z - (approximation in `R[x, π]`)` gains one power of `𝔪_S` at each
  step, using only that `R[x]` surjects onto the residue field of `S` and that `π` generates `𝔪_S`;
* the image `𝔪_R · S` is a nonzero ideal of the discrete valuation ring `S`, hence *some* power
  `𝔪_S ^ n` — the ramification index never has to be computed;
* so `S = R[x, π] + 𝔪_R · S`, and Nakayama (`Submodule.le_of_le_smul_of_le_jacobson_bot`, as in
  `Langlands.NakayamaMonogenic`) upgrades that to `S = R[x, π]`.

## Main result

* `LocalField.adjoin_pair_eq_top`
-/

noncomputable section

open IsLocalRing

namespace LocalField

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [IsDomain S]
  [IsDiscreteValuationRing S] [Algebra R S] [Module.Finite R S]

omit [IsDomain R] [IsDiscreteValuationRing R] [Module.Finite R S] in
/-- **Successive approximation by `R[x, π]`.** If `π` generates `𝔪_S` and every element of `S` is
congruent mod `𝔪_S` to an element of `R[x]`, then every element of `S` is congruent to an element
of `R[x, π]` modulo `𝔪_S ^ k`, for every `k`.

The induction step writes `z - b = u · π ^ k` (using `𝔪_S ^ k = (π ^ k)`), replaces `u` by an
element `c` of `R[x]` congruent to it mod `𝔪_S`, and returns `b + c · π ^ k`; the new error is
`(u - c) · π ^ k ∈ (π) · (π ^ k) = 𝔪_S ^ (k + 1)`. -/
theorem exists_mem_adjoin_pair_sub_mem_pow {x π : S} (hπ : maximalIdeal S = Ideal.span {π})
    (hres : ∀ z : S, ∃ c ∈ Algebra.adjoin R ({x} : Set S), z - c ∈ maximalIdeal S) (k : ℕ)
    (z : S) : ∃ b ∈ Algebra.adjoin R ({x, π} : Set S), z - b ∈ maximalIdeal S ^ k := by
  have hπmem : π ∈ Algebra.adjoin R ({x, π} : Set S) := Algebra.subset_adjoin (by simp)
  have hsub : Algebra.adjoin R ({x} : Set S) ≤ Algebra.adjoin R ({x, π} : Set S) :=
    Algebra.adjoin_mono (by simp)
  have hpow : ∀ j : ℕ, maximalIdeal S ^ j = Ideal.span {π ^ j} := fun j => by
    rw [hπ, Ideal.span_singleton_pow]
  induction k generalizing z with
  | zero => exact ⟨0, Subalgebra.zero_mem _, by simp⟩
  | succ k ih =>
    obtain ⟨b, hb, hzb⟩ := ih z
    rw [hpow k, Ideal.mem_span_singleton'] at hzb
    obtain ⟨u, hu⟩ := hzb
    obtain ⟨c, hc, huc⟩ := hres u
    rw [hπ, Ideal.mem_span_singleton'] at huc
    obtain ⟨t, ht⟩ := huc
    refine ⟨b + c * π ^ k, add_mem hb (mul_mem (hsub hc) (pow_mem hπmem k)), ?_⟩
    rw [hpow (k + 1), Ideal.mem_span_singleton']
    refine ⟨t, ?_⟩
    have hz : z - (b + c * π ^ k) = (u - c) * π ^ k := by
      have h' : z - b = u * π ^ k := hu.symm
      linear_combination h'
    rw [hz, ← ht]; ring

/-- **`S = R[x, π]`.** For `R`, `S` discrete valuation rings with `S` finite over `R` and
`algebraMap R S` injective, `π` a uniformizer of `S`, and `x` an element whose `R`-subalgebra
`R[x]` surjects onto the residue field of `S`, the pair `{x, π}` generates `S` as an `R`-algebra.

Injectivity of `algebraMap R S` is what makes `𝔪_R · S` nonzero (`𝔪_R ≠ ⊥` since `R` is a discrete
valuation ring, hence not a field), and a nonzero ideal of the discrete valuation ring `S` is
`𝔪_S ^ n` for some `n` (`IsDiscreteValuationRing.ideal_eq_span_pow_irreducible`). Approximating to
that precision by `exists_mem_adjoin_pair_sub_mem_pow` gives `S = R[x, π] + 𝔪_R · S`, and Nakayama
finishes.

No hypothesis relates `x` and `π`, and neither the residue degree nor the ramification index
appears. -/
theorem adjoin_pair_eq_top (hinj : Function.Injective (algebraMap R S)) {x π : S}
    (hπ : maximalIdeal S = Ideal.span {π})
    (hres : ∀ z : S, ∃ c ∈ Algebra.adjoin R ({x} : Set S), z - c ∈ maximalIdeal S) :
    Algebra.adjoin R ({x, π} : Set S) = ⊤ := by
  have hirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  have hpow : ∀ j : ℕ, maximalIdeal S ^ j = Ideal.span {π ^ j} := fun j => by
    rw [hπ, Ideal.span_singleton_pow]
  -- `𝔪_R · S` is a nonzero ideal of `S`, hence a power of `𝔪_S`.
  have hJne : Ideal.map (algebraMap R S) (maximalIdeal R) ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ :=
      Submodule.ne_bot_iff (maximalIdeal R) |>.mp (IsDiscreteValuationRing.not_a_field R)
    intro hbot
    have hmem : algebraMap R S a ∈ Ideal.map (algebraMap R S) (maximalIdeal R) :=
      Ideal.mem_map_of_mem _ ha
    rw [hbot, Ideal.mem_bot] at hmem
    exact ha0 (hinj (by rw [hmem, map_zero]))
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJne hirr
  refine eq_top_iff.mpr <| Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    (?_ : ⊤ ≤ (Algebra.adjoin R ({x, π} : Set S)).toSubmodule ⊔
      maximalIdeal R • (⊤ : Submodule R S))
  intro z _
  obtain ⟨b, hb, hzb⟩ := exists_mem_adjoin_pair_sub_mem_pow hπ hres n z
  rw [Ideal.smul_top_eq_map]
  refine Submodule.mem_sup.mpr ⟨b, hb, z - b, ?_, by ring⟩
  rw [Submodule.restrictScalars_mem]
  show z - b ∈ Ideal.map (algebraMap R S) (maximalIdeal R)
  rw [hn, ← hpow n]
  exact hzb

end LocalField

end
