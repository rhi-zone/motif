/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.TotallyRamifiedEisenstein
import Langlands.ValueGroupCyclic
import Langlands.UnramifiedExtension
import Mathlib.RingTheory.Henselian

/-!
# The complete-discretely-valued bundle on a finite extension

`Langlands.TotallyRamifiedEisenstein.LocalField.adjoin_eq_integralClosure_of_isUniformizer` — the
totally ramified half of Serre's monogenicity theorem — takes its base field `K` with the bundle

```
[NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
[(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
[IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
```

Serre's tower argument needs that theorem applied with the base field replaced by an intermediate
extension `M` carrying no valuation structure of its own — for instance the maximal unramified
subextension built by
`Langlands.UnramifiedExtension.HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv`.
This file constructs that bundle on `M` from a valuation subring `A : ValuationSubring M` lying
over `𝒪[K]`, and identifies the resulting canonical valuation subring with `A`.

## Main results

* `LocalField.valuationSubring_valuation_ofValuation_eq` : the `ValuativeRel`-canonical valuation
  subring of the `Valued.mk'`/`ofValuation` bundle attached to `A` is `A` itself. Needs only
  `[Valuation.RankOne A.valuation]`; no base field is involved.
* `LocalField.isDiscreteValuationRing_valuation_valuationSubring_of_finiteDimensional` : with `K`
  complete and discretely valued and `M / K` finite, that valuation subring is a discrete valuation
  ring — the last of the six instances the Eisenstein theorem requires.
* `LocalField.adjoin_eq_integralClosure_of_isUniformizer_of_valuationSubring` : the totally ramified
  half of monogenicity, `𝒪_N = 𝒪_M[π]`, over such an intermediate `M` rather than over `K` itself.

## Implementation notes

Both results are stated in `letI`-in-the-statement form (as Mathlib's own
`Valuation.Compatible.ofValuation` is), because the conclusions mention typeclass instances that
are *constructed* rather than assumed: the bundle is not canonical data on a bare `Field M`, so it
has to be named in the statement for the conclusion to be meaningful. A caller reproduces the same
`letI` chain and then applies these lemmas.

The construction route is the `Valued.mk'` one (`Valued.mk' A.valuation`, then
`Valued.toNontriviallyNormedField`), not `spectralNorm.nontriviallyNormedField`; the two are not
definitionally equal and mixing them reproduces a `NontriviallyNormedField M` instance diamond.
Completeness is nevertheless obtained from `spectralNorm.completeSpace`, transported across that
diamond by `LocalField.exists_completeSpace_of_finiteDimensional`.

The `Compatible` instance needs no work at all: `ValuativeRel.ofValuation v` makes `v` compatible
by definition (`Valuation.Compatible.ofValuation`).
-/

open ValuativeRel Valuation
open scoped NNReal

namespace LocalField

/-- The `ValuativeRel`-canonical valuation subring of the normed/valuative bundle built from a
`RankOne` valuation subring `A` of a field `M` is `A` itself.

`ValuativeRel.valuation M` is derived from the relation `≤ᵥ`, which `ValuativeRel.ofValuation`
defines from `NormedField.valuation` — the `ℝ≥0`-valued valuation of the norm, not from
`A.valuation` directly — so the identification is not definitional. It follows by chaining the two
`Valuation.Compatible.vle_iff_le` instances with
`Valued.toNormedField.norm_le_one_iff` and `ValuationSubring.valuation_le_one_iff`. -/
theorem valuationSubring_valuation_ofValuation_eq {M : Type*} [Field M] (A : ValuationSubring M)
    [Valuation.RankOne A.valuation] :
    letI : Valued M A.ValueGroup := Valued.mk' A.valuation
    letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
    letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
    (ValuativeRel.valuation M).valuationSubring = A := by
  letI : Valued M A.ValueGroup := Valued.mk' A.valuation
  letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
  letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
  haveI : (NormedField.valuation (K := M)).Compatible :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
  refine ValuationSubring.ext _ _ fun x => ?_
  rw [Valuation.mem_valuationSubring_iff]
  have h1 : (ValuativeRel.valuation M) x ≤ 1 ↔ x ≤ᵥ (1 : M) := by
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation M), map_one]
  have h2 : x ≤ᵥ (1 : M) ↔ NormedField.valuation x ≤ NormedField.valuation (1 : M) :=
    Valuation.Compatible.vle_iff_le (v := NormedField.valuation (K := M)) x 1
  rw [h1, h2, map_one]
  rw [show ((NormedField.valuation x : ℝ≥0) ≤ 1) ↔ ‖x‖ ≤ 1 from by
    rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]]
  rw [Valued.toNormedField.norm_le_one_iff]
  exact A.valuation_le_one_iff x

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  {M : Type*} [Field M] [Algebra K M] [FiniteDimensional K M]

omit [IsUltrametricDist K] [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K] in
/-- **The discreteness instance of the Eisenstein theorem's base-field bundle, transferred to a
finite extension.** For `𝒪[K]` a discrete valuation ring and `M / K` finite, a valuation subring
`A : ValuationSubring M` lying over `𝒪[K]` induces, via the `Valued.mk'`/`ofValuation` chain, a
`ValuativeRel M` whose canonical valuation subring is a discrete valuation ring.

This is the sixth and only mathematically substantive instance of the bundle
`LocalField.adjoin_eq_integralClosure_of_isUniformizer` requires of its base field. The other five
are obtained by the caller reproducing the same `letI` chain:
`exists_rankOne_compatible` (the `RankOne` structure, passed here as `hR`), `Valued.mk'` +
`Valued.toNontriviallyNormedField` (`NontriviallyNormedField M`, and `IsUltrametricDist M` by
`inferInstance`), `ValuativeRel.ofValuation` + `Valuation.Compatible.ofValuation` (`ValuativeRel M`
and its `Compatible` instance) and `exists_completeSpace_of_finiteDimensional` (`CompleteSpace M`).
Those five are pure instance plumbing and need no lemma of their own; only this one does.

Note that neither `[CompleteSpace K]` nor `[IsUltrametricDist K]` nor the `Compatible` instance on
`K` is used in the proof — `ValuationSubring.isDiscreteValuationRing_of_comap_eq` needs only
finiteness of `M / K` and discreteness of `𝒪[K]`. They are `omit`ted below but remain necessary for
the caller, to build the other five instances. -/
theorem isDiscreteValuationRing_valuation_valuationSubring_of_finiteDimensional
    (A : ValuationSubring M)
    (hA : A.comap (algebraMap K M) = (ValuativeRel.valuation K).valuationSubring)
    (hR : Valuation.RankOne A.valuation) :
    letI := hR
    letI : Valued M A.ValueGroup := Valued.mk' A.valuation
    letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
    letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
    IsDiscreteValuationRing ↥(ValuativeRel.valuation M).valuationSubring := by
  letI := hR
  rw [valuationSubring_valuation_ofValuation_eq A]
  exact ValuationSubring.isDiscreteValuationRing_of_comap_eq A hA

/-- **Totally ramified monogenicity over an intermediate extension.**
`LocalField.adjoin_eq_integralClosure_of_isUniformizer` (`Langlands.TotallyRamifiedEisenstein`)
applied with its base field taken to be a finite extension `M / K` carrying no valuation structure
of its own, only a valuation subring `A : ValuationSubring M` lying over `𝒪[K]`: if `π ∈ N`
generates a further finite separable extension `N / M` and its spectral norm is the
`[N : M]`-th root of the norm of a uniformizer `ϖ` of `M`, then `𝒪_N = 𝒪_M[π]`.

This is the composition step Serre's tower argument needs on the totally ramified side, and the
form in which it composes with the unramified half
(`Langlands.UnramifiedExtension.HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv`,
whose maximal unramified subextension `M` arrives as a bare `IntermediateField`).

The `letI` chain in the statement is the bundle `M` has to be given for the conclusion to typecheck
at all; `‖·‖` and `spectralNorm M N` in the hypotheses, and the base ring
`↥(ValuativeRel.valuation M).valuationSubring` in the conclusion, all refer to it. By
`valuationSubring_valuation_ofValuation_eq` that base ring is `↥A`.

**What this does not yet give.** Serre's theorem states `𝒪_N` is monogenic over `𝒪_K`, i.e.
generated by a *single* element; combining a generator of `𝒪_M / 𝒪_K` with the generator `π` of
`𝒪_N / 𝒪_M` into one generator of `𝒪_N / 𝒪_K` is a separate argument (classically `x + π` for `x`
a lift of a residue-field generator) that is not performed here. Nor is `hram` reformulated
intrinsically in terms of `A`'s own valuation rather than the constructed norm. -/
theorem adjoin_eq_integralClosure_of_isUniformizer_of_valuationSubring
    (A : ValuationSubring M)
    (hA : A.comap (algebraMap K M) = (ValuativeRel.valuation K).valuationSubring)
    (hR : Valuation.RankOne A.valuation)
    (N : Type*) [Field N] [Algebra M N] [FiniteDimensional M N] [Algebra.IsSeparable M N] :
    letI := hR
    letI : Valued M A.ValueGroup := Valued.mk' A.valuation
    letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
    letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
    ∀ ϖ : ↥(ValuativeRel.valuation M).valuationSubring, Irreducible ϖ →
      ∀ π : N, ‖(ϖ : M)‖ = spectralNorm M N π ^ (minpoly M π).natDegree →
        (minpoly M π).natDegree = Module.finrank M N →
        Algebra.adjoin ↥(ValuativeRel.valuation M).valuationSubring ({π} : Set N) =
          integralClosure ↥(ValuativeRel.valuation M).valuationSubring N := by
  haveI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  haveI : Algebra.IsAlgebraic M N := Algebra.IsAlgebraic.of_finite M N
  letI := hR
  letI : Valued M A.ValueGroup := Valued.mk' A.valuation
  letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
  haveI : IsUltrametricDist M := inferInstance
  haveI : CompleteSpace M := exists_completeSpace_of_finiteDimensional K A hA
  letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
  haveI : (NormedField.valuation (K := M)).Compatible :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
  haveI : IsDiscreteValuationRing ↥(ValuativeRel.valuation M).valuationSubring :=
    isDiscreteValuationRing_valuation_valuationSubring_of_finiteDimensional K A hA hR
  exact fun _ϖ hϖ _π hram hgen =>
    adjoin_eq_integralClosure_of_isUniformizer (K := M) (L := N) hϖ hram hgen

/-- **`↥A` itself is Henselian, for `A : ValuationSubring M` lying over a complete discretely
valued `𝒪[K]` with finite residue field, `M / K` finite.**

This gives a route to Hensel's lemma *inside the actual field `M`* (in particular, inside a fixed `L` when
`M = L`), rather than inside an auxiliary algebraically closed field disconnected from `L`. It
reuses exactly the `letI` bundle `isDiscreteValuationRing_valuation_valuationSubring_of_finiteDimensional`
builds, plus `henselianLocalRing_of_valuationSubring` (`Langlands.UnramifiedExtension`) applied to
that bundle, transported from `↥(ValuativeRel.valuation M).valuationSubring` to `↥A` along
`valuationSubring_valuation_ofValuation_eq`. -/
theorem henselianLocalRing_of_comap_eq
    (A : ValuationSubring M)
    (hA : A.comap (algebraMap K M) = (ValuativeRel.valuation K).valuationSubring)
    (hR : Valuation.RankOne A.valuation)
    (hfin : Finite (IsLocalRing.ResidueField A)) :
    letI := hR
    letI : Valued M A.ValueGroup := Valued.mk' A.valuation
    letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
    letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
    HenselianLocalRing ↥A := by
  letI := hR
  letI : Valued M A.ValueGroup := Valued.mk' A.valuation
  letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
  haveI : IsUltrametricDist M := inferInstance
  haveI : CompleteSpace M := exists_completeSpace_of_finiteDimensional K A hA
  letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
  haveI : (NormedField.valuation (K := M)).Compatible :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
  haveI : IsDiscreteValuationRing ↥(ValuativeRel.valuation M).valuationSubring :=
    isDiscreteValuationRing_valuation_valuationSubring_of_finiteDimensional K A hA hR
  haveI : Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation M).valuationSubring) := by
    rw [valuationSubring_valuation_ofValuation_eq A]; exact hfin
  have h := henselianLocalRing_of_valuationSubring M
  rwa [valuationSubring_valuation_ofValuation_eq A] at h

/-- **`↥A` is `(maximalIdeal ↥A)`-adically complete, for `A : ValuationSubring M` lying over a
complete discretely valued `𝒪[K]` with finite residue field, `M / K` finite.**

Same `letI` bundle and the same transport as `henselianLocalRing_of_comap_eq`, using
`isAdicComplete_of_valuationSubring` (`Langlands.UnramifiedExtension`) in place of
`henselianLocalRing_of_valuationSubring`. The conclusion `IsAdicComplete (IsLocalRing.maximalIdeal
↥A) ↥A` is stated purely in terms of `A`'s own `CommRing`/`Ideal` structure — no topology, hence no
dependence on which of the (mutually non-defeq) `NontriviallyNormedField` instances on `M` the
`letI` bundle happens to use internally — so it transports across
`valuationSubring_valuation_ofValuation_eq` exactly as `HenselianLocalRing ↥A` does. -/
theorem isAdicComplete_of_comap_eq
    (A : ValuationSubring M)
    (hA : A.comap (algebraMap K M) = (ValuativeRel.valuation K).valuationSubring)
    (hR : Valuation.RankOne A.valuation)
    (hfin : Finite (IsLocalRing.ResidueField A)) :
    letI := hR
    letI : Valued M A.ValueGroup := Valued.mk' A.valuation
    letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
    letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
    IsAdicComplete (IsLocalRing.maximalIdeal ↥A) ↥A := by
  letI := hR
  letI : Valued M A.ValueGroup := Valued.mk' A.valuation
  letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
  haveI : IsUltrametricDist M := inferInstance
  haveI : CompleteSpace M := exists_completeSpace_of_finiteDimensional K A hA
  letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
  haveI : (NormedField.valuation (K := M)).Compatible :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
  haveI : IsDiscreteValuationRing ↥(ValuativeRel.valuation M).valuationSubring :=
    isDiscreteValuationRing_valuation_valuationSubring_of_finiteDimensional K A hA hR
  haveI : Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation M).valuationSubring) := by
    rw [valuationSubring_valuation_ofValuation_eq A]; exact hfin
  have h := isAdicComplete_of_valuationSubring M
  rwa [valuationSubring_valuation_ofValuation_eq A] at h

end LocalField
