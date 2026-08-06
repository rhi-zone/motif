/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.PrimitiveElement

/-!
# A scalar-additive primitive element for a two-step tower

Serre's tower argument for monogenicity of `𝒪_L / 𝒪_K` (*Local Fields* III §6) needs, as the
field-level first step of fusing the unramified generator `β` (of the maximal unramified
subextension `M = K⟮β⟯`) and the uniformizer `π` (of the totally ramified step `N = M⟮π⟯`) into a
single ring-of-integers generator, the fact that `β + c • π` is already a primitive element for
the *whole* tower `N / K`, for a suitable scalar `c` in the (infinite) base field `K` — not
necessarily `c = 1`.

This file proves exactly that field-level fact, phrased concretely (a single ambient field `E`
housing both adjunctions, matching how `M` and `N` actually arise in
`Langlands.UnramifiedExtension`/`Langlands.TowerBundle` as literal `IntermediateField` adjoins of
an ambient field) rather than via `TowerBundle.lean`'s abstract-tower bundle, which does not tie
`M` and `N` to a common ambient field and so cannot host a statement about a *sum* `β + c • π` at
all: identifying `TowerBundle.lean`'s abstract `M`, `N` with concrete `IntermediateField`s of a
common ambient field (as `UnramifiedExtension.lean`'s construction already produces `M` this way)
is exactly the standard `AdjoinSimple`/algebra-equivalence transport, orthogonal to the argument
here.

## Main results

* `Langlands.exists_scalar_add_smul_primitive` : for `E / K` finite separable with `K` infinite,
  `β π : E` with `K⟮β⟯⟮π⟯ = K⟮β, π⟯ = ⊤` (i.e. `π` generates the rest of the tower over
  `M := K⟮β⟯`), there is a scalar `c : K` such that `(minpoly K (β + c • π)).natDegree =
  Module.finrank K E`.

## Implementation notes

Mathlib's own primitive element theorem (`Mathlib/FieldTheory/PrimitiveElement.lean`) proves
exactly this shape of statement for the infinite-field case, but its two relevant results do not
expose the scalar in a directly reusable form:

* `Field.primitive_element_inf_aux` produces `∃ γ, F⟮α, β⟯ = F⟮γ⟯` via a Euclidean-domain/gcd
  argument that is not phrased in terms of the finitely-many-intermediate-fields pigeonhole, so
  its witness `γ` (internally `α + c • β`) is not exposed as such in the statement.
* `Field.primitive_element_inf_aux_of_finite_intermediateField` *does* construct its witness as
  `α + x • β` for an explicit `x` found by `Finite.exists_ne_map_eq_of_infinite`, but is `private`
  and hence unusable from outside that file.

Rather than reproving the general primitive element theorem, this file inlines the (short) pigeonhole
argument of `primitive_element_inf_aux_of_finite_intermediateField` directly with the scalar exposed
in the theorem statement, using `Field.exists_primitive_element_iff_finite_intermediateField`
together with the unconditional `Field.exists_primitive_element` to obtain
`Finite (IntermediateField K E)` (avoiding the separate gcd-based argument entirely, since finite
separable extensions always have finitely many intermediate fields).
-/

namespace Langlands

open IntermediateField

/-- **A scalar-additive primitive element for a two-step tower.** Let `E / K` be finite separable
with `K` infinite, and `β π : E` such that adjoining `π` to `M := K⟮β⟯` gives all of `E`
(equivalently, `K⟮β, π⟯ = ⊤`). Then there is a scalar `c : K` such that `a := β + c • π` is a
primitive element for the whole tower: `(minpoly K a).natDegree = Module.finrank K E`.

This is the classical primitive element theorem's infinite-field construction (`γ := α + c • β`),
specialized so the scalar `c` is exposed in the statement rather than hidden behind an existential
over the generator — needed because the intended downstream use (bounding the discriminant of the
composite generator `a`) has to know `a` has this additive shape, not merely that some primitive
element exists. -/
theorem exists_scalar_add_smul_primitive {K E : Type*} [Field K] [Field E] [Infinite K]
    [Algebra K E] [FiniteDimensional K E] [Algebra.IsSeparable K E] (β π : E)
    (hN : (IntermediateField.adjoin (IntermediateField.adjoin K {β}) {π}).restrictScalars K = ⊤) :
    ∃ c : K, (minpoly K (β + c • π)).natDegree = Module.finrank K E := by
  classical
  -- `K⟮β, π⟯ = ⊤`, obtained from `hN` via the two-single-adjoins identification.
  have hβπ : IntermediateField.adjoin K ({β, π} : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_adjoin_simple K β π]; exact hN
  -- Finite separable extensions have finitely many intermediate fields.
  have hfin : Finite (IntermediateField K E) :=
    (Field.exists_primitive_element_iff_finite_intermediateField K E).mp
      ⟨Algebra.IsAlgebraic.of_finite K E, Field.exists_primitive_element K E⟩
  -- Pigeonhole among the (infinitely many, since `K` is infinite) scalars `c ↦ K⟮β + c • π⟯`.
  let f : K → IntermediateField K E := fun c => IntermediateField.adjoin K {β + c • π}
  obtain ⟨x, y, hxy, hfxy⟩ := Finite.exists_ne_map_eq_of_infinite f
  refine ⟨x, ?_⟩
  rw [← Field.primitive_element_iff_minpoly_natDegree_eq, ← hβπ]
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    have hβin : β ∈ IntermediateField.adjoin K ({β, π} : Set E) :=
      IntermediateField.subset_adjoin K _ (Set.mem_insert β {π})
    have hπin : π ∈ IntermediateField.adjoin K ({β, π} : Set E) :=
      IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem β rfl)
    exact (IntermediateField.adjoin K ({β, π} : Set E)).add_mem hβin
      ((IntermediateField.adjoin K ({β, π} : Set E)).smul_mem hπin)
  · rw [IntermediateField.adjoin_le_iff]
    have hxmem : β + x • π ∈ IntermediateField.adjoin K {β + x • π} :=
      IntermediateField.mem_adjoin_simple_self K _
    have hymem : β + y • π ∈ IntermediateField.adjoin K {β + y • π} :=
      IntermediateField.mem_adjoin_simple_self K _
    dsimp only [f] at hfxy
    rw [← hfxy] at hymem
    have hπdiff : (x - y) • π ∈ IntermediateField.adjoin K {β + x • π} := by
      have hsub := (IntermediateField.adjoin K {β + x • π}).sub_mem hxmem hymem
      rwa [show (β + x • π) - (β + y • π) = (x - y) • π by rw [sub_smul]; abel] at hsub
    have hπmem : π ∈ IntermediateField.adjoin K {β + x • π} := by
      have hsmul := (IntermediateField.adjoin K {β + x • π}).smul_mem hπdiff (x := (x - y)⁻¹)
      rwa [smul_smul, inv_mul_eq_div, div_self (sub_ne_zero.2 hxy), one_smul] at hsmul
    have hβmem : β ∈ IntermediateField.adjoin K {β + x • π} := by
      have hsub := (IntermediateField.adjoin K {β + x • π}).sub_mem hxmem
        ((IntermediateField.adjoin K {β + x • π}).smul_mem hπmem (x := x))
      rwa [add_sub_cancel_right] at hsub
    rintro z (rfl | rfl)
    · exact hβmem
    · exact hπmem

end Langlands
