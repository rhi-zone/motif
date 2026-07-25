import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Unramified extensions and lifting automorphisms of the residue field

Let `K` be a field with a `ValuativeRel`, `L / K` a field extension, and `A : ValuationSubring L`
a valuation subring of `L` extending `𝒪[K]` (i.e. `A.comap (algebraMap K L) = 𝒪[K]`) whose
decomposition subgroup `A.decompositionSubgroup K ≤ Gal(L/K)` acts on the residue field
`IsLocalRing.ResidueField A` through the algebra structure coming from `𝒪[K] → A`.

This file records two facts about this setup:

* `ValuationSubring.decompositionSubgroup_smul_algebraMap_residueField` : elements of the
  decomposition subgroup fix the base residue field `𝓀[K]` pointwise (as embedded in
  `IsLocalRing.ResidueField A` via `algebraMap 𝓀[K] (IsLocalRing.ResidueField A)`). This is a
  purely formal consequence of the fact that the decomposition subgroup consists of `K`-algebra
  automorphisms of `L`, unwound through the residue map (`IsLocalRing.ResidueField.residue_smul`,
  `IsLocalRing.ResidueField.algebraMap_residue`). Proved outright, no `sorry`.

* `ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective` : the
  **unramified lifting theorem** -- for every finite Galois subextension `M` of
  `IsLocalRing.ResidueField A` over `𝓀[K]`, every automorphism of `M/𝓀[K]` is the restriction (to
  `M`) of *some* element of the decomposition subgroup's induced action on the residue field. This
  is the genuinely deep, Hensel's-lemma-flavoured content: given a finite separable extension `M`
  of the residue field `𝓀[K]`, the theory of unramified extensions produces a finite unramified
  extension of `K` (inside `L`, with valuation ring inside `A`) whose residue field is `M`, and
  every automorphism of `M/𝓀[K]` lifts (uniquely, since unramified extensions of a Henselian field
  are classified by, and functorial in, their residue extension) to a `K`-automorphism of that
  unramified extension, hence (extending along `L`'s algebraic closedness / normality) to an
  element of `Gal(L/K)` stabilizing `A`, i.e. of the decomposition subgroup. This is **not** a
  consequence of Mathlib's `InfiniteGalois.restrictNormalHom_surjective` (surjectivity of
  restriction between two normal subextensions of one *fixed* Galois extension `L/K`): here the
  map being shown surjective goes from the decomposition subgroup of `A` (acting on the *residue*
  field of `A`, an a priori unrelated extension) to `Gal(M/𝓀[K])`, not a restriction map between
  intermediate fields of a single extension. Recorded as a `sorry`; not yet in Mathlib.

## Implementation notes

The hypotheses on `A` needed to state `decompositionSubgroup_smul_algebraMap_residueField` are
exactly the ones already established by `Langlands.WeilGroup` for its
`valuationSubringExtension K`: an `Algebra ↥(𝒪[K]) A` instance (`integersAlgebraMap`) compatible
with the ambient inclusion `𝒪[K] → K → L`. Compatibility is recorded as an explicit hypothesis
`hcompat` (rather than an `IsScalarTower ↥(𝒪[K]) A L` instance) to avoid a typeclass-resolution
failure encountered when this file's generic `L` is instantiated with a concrete
`AlgebraicClosure K` at the call site in `WeilGroup.lean`: the automatically-derived
`IsScalarTower` instance there fails Lean's instance-search unification even though it is
definitionally exactly `hcompat`, apparently because of how the discrimination tree indexes the
mangled instance name against the (already-assigned) metavariable for `L`. Passing the same fact
as an ordinary hypothesis sidesteps the issue entirely, since it is then just an ordinary term
provided at the call site (proved there by `rfl`, exactly as here). -/

noncomputable section

open ValuativeRel Valuation IsLocalRing

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel K]
  (A : ValuationSubring L) [Algebra ↥(𝒪[K]) A]
  [IsLocalHom (algebraMap ↥(𝒪[K]) A)]

/-- Elements of the decomposition subgroup of `A` (i.e. `K`-algebra automorphisms of `L`
stabilizing `A`) fix the base residue field `𝓀[K]`, embedded in `IsLocalRing.ResidueField A` via
`algebraMap 𝓀[K] (IsLocalRing.ResidueField A)`, pointwise. Concretely: the induced action of
`A.decompositionSubgroup K` on `IsLocalRing.ResidueField A` restricts to the identity on the image
of `𝓀[K]`. A purely formal fact (no Henselian/unramified-extension input needed): every
`σ ∈ Gal(L/K)` fixes `K` pointwise by definition, hence fixes the image of `𝒪[K]` in `A` pointwise
(via `hcompat`, which records that the algebra structure `↥(𝒪[K]) → A` agrees with `↥(𝒪[K]) → K →
L`), hence (taking residues) fixes the image of `𝓀[K]` in `IsLocalRing.ResidueField A` pointwise. -/
theorem decompositionSubgroup_smul_algebraMap_residueField
    (hcompat : ∀ a : ↥(𝒪[K]), (algebraMap ↥(𝒪[K]) A a : L) = algebraMap K L (a : K))
    (σ : A.decompositionSubgroup K) (x : 𝓀[K]) :
    σ • algebraMap 𝓀[K] (IsLocalRing.ResidueField A) x =
      algebraMap 𝓀[K] (IsLocalRing.ResidueField A) x := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := ↥(𝒪[K])) x
  show σ • algebraMap (IsLocalRing.ResidueField ↥(𝒪[K])) (IsLocalRing.ResidueField A)
      (IsLocalRing.residue ↥(𝒪[K]) a) =
    algebraMap (IsLocalRing.ResidueField ↥(𝒪[K])) (IsLocalRing.ResidueField A)
      (IsLocalRing.residue ↥(𝒪[K]) a)
  rw [IsLocalRing.ResidueField.algebraMap_residue (R := ↥(𝒪[K])) (S := A) a,
    ← IsLocalRing.ResidueField.residue_smul (G := A.decompositionSubgroup K) σ
      (algebraMap ↥(𝒪[K]) A a)]
  congr 1
  -- `σ` fixes the image of `𝒪[K]` in `A`, since it fixes `K` pointwise and (by `hcompat`) the
  -- algebra structure on `A` is compatible with the inclusion `𝒪[K] → K → L`.
  apply Subtype.ext
  show (σ : Gal(L/K)) (algebraMap ↥(𝒪[K]) A a : L) = (algebraMap ↥(𝒪[K]) A a : L)
  rw [hcompat a]
  exact (σ : Gal(L/K)).commutes (a : K)

/-- **The unramified lifting theorem** (Hensel's-lemma-flavoured; not yet in Mathlib): for every
finite Galois subextension `M` of `IsLocalRing.ResidueField A / 𝓀[K]`, every automorphism of
`M/𝓀[K]` is realized by (i.e. is the restriction to `M` of) the residue action of *some* element of
the decomposition subgroup `A.decompositionSubgroup K`.

Sketch of the (missing) proof: given `M`, choose a finite separable extension `K' / K` inside `L`
whose residue field (for the valuation subring `A ⊓ K' = A.comap (algebraMap K' L)`, or rather the
unique valuation subring of `K'` lying under `A`) is `M` -- this is the existence half of the
theory of unramified extensions of a Henselian field, itself built on Hensel's lemma (lift a
primitive element of `M/𝓀[K]` to a monic polynomial over `𝒪[K]` via `Polynomial.lifts`, then use
Henselian-ness to find a root generating the corresponding unramified extension). Given an
automorphism `g` of `M/𝓀[K]`, functoriality of this correspondence (unramified extensions of `K`
are classified by, and equivalent as a category to, finite separable extensions of `𝓀[K]`) lifts
`g` to a `K`-automorphism of `K'`; extending this automorphism of `K'` to all of `L` (`L/K'` being
algebraic) via `IsAlgClosed`/normality gives an element of `Gal(L/K)`, which (since it stabilizes
the valuation subring of `K'` lying under `A`, hence -- using uniqueness of extension of the
valuation, i.e. the same Henselian/decomposition-subgroup-is-everything argument as
`LocalField.decompositionSubgroup_eq_top` -- stabilizes `A` itself) lies in the decomposition
subgroup and induces `g` on `M` by construction. -/
theorem exists_restrictNormalHom_decompositionSubgroup_surjective
    (hcompat : ∀ a : ↥(𝒪[K]), (algebraMap ↥(𝒪[K]) A a : L) = algebraMap K L (a : K))
    [IsGalois 𝓀[K] (IsLocalRing.ResidueField A)]
    (M : IntermediateField 𝓀[K] (IsLocalRing.ResidueField A))
    [FiniteDimensional 𝓀[K] M] [Normal 𝓀[K] M] :
    Function.Surjective fun σ : A.decompositionSubgroup K =>
      AlgEquiv.restrictNormalHom (F := 𝓀[K]) M
        (AlgEquiv.ofRingEquiv (f := (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
          (IsLocalRing.ResidueField A)) σ)
          (decompositionSubgroup_smul_algebraMap_residueField A hcompat σ)) := by
  sorry

end ValuationSubring
