import Langlands.AdicCompletionIntegralClosure

/-!
# Unramifiedness for valuation-ring extensions

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. Prior to this file, there was no way in this repository to
even *state* "the extension `L₀ / K₀` is unramified" in the general-`e` setting (as opposed to the
residue-degree-only setting of `Langlands.ResidueFieldNorm`): `NormMap.lean` proves facts about
the ramification index `e` of the underlying ideals `v.asIdeal`/`w.asIdeal` of `R`/`S`
(`Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver`, used in
`adicCompletionIntegers_comap_eq`), but never packages "`e = 1`" as a standalone predicate on
`K₀ → L₀` itself.

This file defines `IsUnramified`, the classical `𝔪_K·O_L = 𝔪_L` condition, directly on the
`v.adicCompletionIntegers K`-algebra `w.adicCompletionIntegers L` supplied by
`Langlands.AdicCompletionIntegralClosure`, and proves the one general containment always
available for a local homomorphism of local rings
(`IsLocalRing.map_maximalIdeal_le`) — `𝔪_K·O_L ≤ 𝔪_L` unconditionally — so `IsUnramified` is
exactly the assertion that this containment is an equality.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.IsUnramified` : `𝔪_K · O_L = 𝔪_L`, i.e. the ramification
  index of `w.adicCompletionIntegers L` over `v.adicCompletionIntegers K` is `1`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.map_maximalIdeal_le` : `𝔪_K · O_L ≤ 𝔪_L` always holds
  (no unramifiedness hypothesis needed) — this is `IsLocalRing.map_maximalIdeal_le` specialized to
  `K₀ → L₀`, using the `IsLocalHom` instance from `Langlands.ResidueFieldNorm`.

## Scope

Connecting `IsUnramified` to `Ideal.ramificationIdx'` (`Mathlib.NumberTheory.RamificationInertia`)
or to `Langlands.ResidueFieldNorm`'s residue-field-level statements is not attempted here.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- The maximal ideal of `v.adicCompletionIntegers K` always maps into the maximal ideal of
`w.adicCompletionIntegers L`: `𝔪_K · O_L ≤ 𝔪_L`, with no unramifiedness hypothesis. This is
`IsLocalRing.map_maximalIdeal_le` applied to the local homomorphism
`algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)`
(`Langlands.ResidueFieldNorm`). -/
theorem map_maximalIdeal_le :
    Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
        (maximalIdeal (v.adicCompletionIntegers K)) ≤
      maximalIdeal (w.adicCompletionIntegers L) :=
  IsLocalRing.map_maximalIdeal_le _

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- The extension `w.adicCompletionIntegers L / v.adicCompletionIntegers K` is unramified: the
maximal ideal of the base generates the maximal ideal of the top, `𝔪_K · O_L = 𝔪_L`. Equivalently
(not proved here, see the module docstring), the ramification index of `w` over `v` at the level
of the completions is `1`.

By `map_maximalIdeal_le`, `≤` always holds; `IsUnramified` is exactly the assertion of the reverse
containment. -/
def IsUnramified : Prop :=
  Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
      (maximalIdeal (v.adicCompletionIntegers K)) =
    maximalIdeal (w.adicCompletionIntegers L)

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- Unramifiedness is equivalent to the reverse containment `𝔪_L ≤ 𝔪_K · O_L`, given
`map_maximalIdeal_le` for the forward containment. -/
theorem isUnramified_iff_le :
    IsUnramified K L v w ↔
      maximalIdeal (w.adicCompletionIntegers L) ≤
        Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
          (maximalIdeal (v.adicCompletionIntegers K)) :=
  le_antisymm_iff.trans (and_iff_right (map_maximalIdeal_le K L v w))

end IsDedekindDomain.HeightOneSpectrum

end
