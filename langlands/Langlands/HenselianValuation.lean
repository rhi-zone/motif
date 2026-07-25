import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Bridging `ValuationSubring` and `NormedField`, and uniqueness of valuation extension

This file bridges the `ValuationSubring`/`ValuativeRel` formalism (used for
`IsNonarchimedeanLocalField`) with the `NormedField`/`AbsoluteValue` formalism (used by
`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`), in order to prove: for `K` a complete
nonarchimedean local field and `L / K` algebraic, a `ValuationSubring` of `L` whose comap along
`algebraMap K L` is `𝒪[K]` is *unique*. Combined with the fact that `K`-automorphisms of `L`
preserve this comap condition (`ValuationSubring.comap_smul_eq`), this gives that the
decomposition subgroup of any such extension is all of `Gal(L/K)`.

## Main definitions/results

* `LocalField.exists_rankOne_absoluteValue_extends` : given a `ValuationSubring A` of `L`
  extending `𝒪[K]` (in the sense `A.comap (algebraMap K L) = 𝒪[K]`), there is an
  `AbsoluteValue L ℝ` extending the norm on `K` (from a fixed rank-1 embedding for `K`) whose
  closed unit ball is `A`. This packages two genuinely deep facts that are not yet in Mathlib
  (see the docstring below) and is recorded as a `sorry`.
* `LocalField.valuationSubring_eq_of_comap_eq` : uniqueness of the valuation subring extension,
  via `spectralNorm_unique_field_norm_ext` (the "unique norm extension theorem" for complete
  nonarchimedean fields) applied to the absolute values produced by the above.
* `ValuationSubring.comap_smul_eq` : the comap of a `G`-translate of a valuation subring (for
  `G = L ≃ₐ[K] L`) along `algebraMap K L` does not depend on the translate, since automorphisms
  in `G` fix `K` pointwise. A purely formal fact, no `sorry`.

## Implementation notes

The single deep `sorry`, `exists_rankOne_absoluteValue_extends`, packages together:

1. **Rank preservation under algebraic extension**: if `K` has a rank-≤-1 (i.e. real-valued)
   valuation and `L / K` is algebraic, then any valuation subring `A` of `L` restricting to
   `𝒪[K]` is again of rank ≤ 1, i.e. `A.valuation` (valued in the abstract group `A.ValueGroup`)
   admits an order-embedding into `ℝ≥0`. This is a standard fact (e.g. Bourbaki, *Commutative
   Algebra*, VI §10, or Engler-Prestel, *Valued Fields*), not yet in Mathlib.
2. **Compatible normalization**: moreover the embedding `A.ValueGroup → ℝ≥0` can be chosen so
   that it agrees with the fixed embedding used to build the `NormedField K` structure on `K`
   (i.e. so that the extended norm genuinely restricts to `‖·‖` on `K`, not just something
   equivalent to it).

Once these are granted, the rest is formal: build `Valued L A.ValueGroup` via `Valued.mk'`
(which needs no ambient topology on `L`), transport the resulting `RankOne A.valuation` instance
into a `NontriviallyNormedField L` via `Valued.toNontriviallyNormedField`, and take
`f := NormedField.toAbsoluteValue L`; then `f x ≤ 1 ↔ x ∈ A` is
`toNormedField.norm_le_one_iff` composed with `ValuationSubring.valuation_le_one_iff`.
-/

noncomputable section

open ValuativeRel Valuation IsLocalRing

namespace LocalField

section NormedFieldBridge

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  {L : Type*} [Field L] [Algebra K L]

/-- **Deep fact, not yet in Mathlib** (see the module docstring for the precise gap): given a
`ValuationSubring A` of an algebraic extension `L` of `K` with `A.comap (algebraMap K L) = 𝒪[K]`,
and a fixed `NontriviallyNormedField` structure on `K` coming from a rank-1 valuation compatible
with `ValuativeRel.valuation K`, there is an `AbsoluteValue L ℝ` extending `‖·‖` on `K` whose
closed unit ball is exactly `A`. -/
theorem exists_rankOne_absoluteValue_extends [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) (hA : A.comap (algebraMap K L) = (valuation K).valuationSubring) :
    ∃ f : AbsoluteValue L ℝ, (∀ x : K, f (algebraMap K L x) = ‖x‖) ∧ ∀ x : L, f x ≤ 1 ↔ x ∈ A := by
  sorry

/-- **Uniqueness of the extension of a complete nonarchimedean valuation to an algebraic
extension.** If `K` is complete with respect to a nontrivial nonarchimedean norm and `L / K` is
algebraic, then any two `ValuationSubring`s of `L` restricting to `𝒪[K]` coincide.

This is the standard fact that makes the decomposition subgroup of a Henselian (in particular,
complete) valued field's valuation ring extension equal to the *whole* Galois group: it is proved
here from `spectralNorm_unique_field_norm_ext` (Mathlib's unique norm extension theorem) via
`exists_rankOne_absoluteValue_extends`, so its only dependency on unformalized mathematics is
that one lemma. -/
theorem valuationSubring_eq_of_comap_eq [Algebra.IsAlgebraic K L] [CompleteSpace K]
    {A B : ValuationSubring L}
    (hA : A.comap (algebraMap K L) = (valuation K).valuationSubring)
    (hB : B.comap (algebraMap K L) = (valuation K).valuationSubring) :
    A = B := by
  obtain ⟨f, hfK, hfA⟩ := exists_rankOne_absoluteValue_extends K A hA
  obtain ⟨g, hgK, hgB⟩ := exists_rankOne_absoluteValue_extends K B hB
  refine ValuationSubring.ext _ _ fun x => ?_
  rw [← hfA, ← hgB, spectralNorm_unique_field_norm_ext hfK x,
    spectralNorm_unique_field_norm_ext hgK x]

end NormedFieldBridge

end LocalField

section ComapSmul

open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The comap of a `σ`-translate of a valuation subring of `L` (for `σ : L ≃ₐ[K] L`) along
`algebraMap K L` does not depend on `σ`: automorphisms of `L` over `K` fix `K` pointwise, so
`σ • A` restricts to the same subring of `K` that `A` does. Purely formal, no `sorry`. -/
theorem ValuationSubring.comap_smul_eq (σ : L ≃ₐ[K] L) (A : ValuationSubring L) :
    (σ • A).comap (algebraMap K L) = A.comap (algebraMap K L) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    show σ⁻¹ (algebraMap K L x) = algebraMap K L x from σ⁻¹.commutes x]

end ComapSmul
