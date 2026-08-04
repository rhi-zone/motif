import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# The universe lift functor for profinite groups

Mirrors `GrpCat.uliftFunctor` (`Mathlib.Algebra.Category.Grp.Ulift`) and `TopCat.uliftFunctor`
(`Mathlib.Topology.Category.TopCat.ULift`): the functor sending a profinite group `P : ProfiniteGrp.{u}`
to the homeomorphic/isomorphic profinite group `ULift.{v} P : ProfiniteGrp.{max u v}`, fully
faithful. General-purpose category-theory/topology infrastructure, with no dependency on the rest
of `Langlands`.

This was intended as the piece needed to compare `Zhat` (hardwired to universe `0`, being the
profinite completion of `Multiplicative ℤ : Type`) against a `ProfiniteGrp` living in an arbitrary
universe `u` (such as `Langlands.WeilGroup`'s `InfiniteGalois.profiniteGalGrp 𝓀[K] kbar`): instead
of `Zhat` directly, one would compare against `ProfiniteGrp.ProfiniteCompletion.completion
(GrpCat.of (ULift.{u} (Multiplicative ℤ)))`, which lives in `ProfiniteGrp.{u}`. **That comparison
needs `uliftFunctor` to preserve the limit defining `Zhat`, which is a genuine wall distinct from
just building the functor -- see the "Preserves-limits gap" section below.**

## Main definitions and results

* `ProfiniteGrp.uliftFunctor` : the universe lift functor `ProfiniteGrp.{u} ⥤ ProfiniteGrp.{max u v}`.
* `ProfiniteGrp.uliftFunctorFullyFaithful` : it is fully faithful.

## Preserves-limits gap (confirmed, not just anticipated)

Unlike `GrpCat.uliftFunctor`/`TopCat.uliftFunctor` (both of which preserve limits of *arbitrary*
size, even ones too large to exist in the smaller universe, via
`Mathlib.CategoryTheory.Limits.Preserves.Ulift`), `ProfiniteGrp.uliftFunctor` here is **not** shown
to preserve any limits at all, and attempting the mirror of `GrpCat.uliftFunctor_preservesLimit`'s
proof hits a confirmed obstruction, not merely a plausible-but-unproven gap: `Profinite`'s and
`ProfiniteGrp`'s own forgetful-functor `PreservesLimits` instances
(`Profinite.forget_preservesLimits`, `ProfiniteGrp.instPreservesLimitsProfiniteForget₂...`) are
each stated as `PreservesLimitsOfSize.{w, w}` for `w` the *domain category's own* universe -- e.g.
`PreservesLimits (forget Profinite.{w})` only covers diagrams `J` with `Category.{w} J`, not
`Category.{0} J` for a fixed small `J` and varying `w`. Checked directly (`#check`/`inferInstance`
in a scratch file, not guessed): `PreservesLimit K (forget₂ ProfiniteGrp.{v} Profinite ⋙ forget
Profinite)` for `J : Type` `[SmallCategory J]`, `K : J ⥤ ProfiniteGrp.{v}` fails to synthesize for
a general universe variable `v` (succeeding only at the coincidental case `v = 0`, where
`SmallCategory` happens to already match `Profinite.{0}`'s own requirement). So the diagram
`FiniteIndexNormalSubgroup (Multiplicative ℤ) : Type` defining `Zhat` (small, i.e. at universe `0`)
is *not* known, via existing Mathlib lemmas, to have its limit preserved when mapped into
`ProfiniteGrp.{v}` for `v ≠ 0`. This is very plausibly true regardless (compact Hausdorff totally
disconnected spaces are closed under arbitrary products, e.g. via Tychonoff, so there is no
mathematical obstruction) but proving it requires re-deriving a *stronger* preserves-limits fact
for `Profinite`'s (and transitively `CompHaus`'s and `TopCat`'s) forgetful functors than Mathlib
currently has -- a separate, nontrivial piece of infrastructure, not attempted here.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace ProfiniteGrp

instance uLift.totallyDisconnectedSpace {G : Type*} [TopologicalSpace G]
    [TotallyDisconnectedSpace G] : TotallyDisconnectedSpace (ULift.{v} G) :=
  Homeomorph.ulift.symm.totallyDisconnectedSpace

/-- The universe lift functor for profinite groups: sends `P : ProfiniteGrp.{u}` to the
(isomorphic) profinite group `ULift.{v} P : ProfiniteGrp.{max u v}`. -/
def uliftFunctor : ProfiniteGrp.{u} ⥤ ProfiniteGrp.{max u v} where
  obj P := ProfiniteGrp.of (ULift.{v} P)
  map {P Q} f := ProfiniteGrp.ofHom
    { toFun := fun x => ⟨f.hom x.down⟩
      map_one' := ULift.up_inj.mpr (map_one f.hom)
      map_mul' := fun a b => ULift.up_inj.mpr (map_mul f.hom a.down b.down)
      continuous_toFun := by fun_prop }
  map_id P := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The universe lift functor for profinite groups is fully faithful. -/
def uliftFunctorFullyFaithful : uliftFunctor.{u, v}.FullyFaithful where
  preimage f := ProfiniteGrp.ofHom
    { toFun := fun x => (f.hom ⟨x⟩).down
      map_one' := congrArg ULift.down (map_one f.hom)
      map_mul' := fun a b => congrArg ULift.down (map_mul f.hom ⟨a⟩ ⟨b⟩)
      continuous_toFun := by fun_prop }
  map_preimage _ := rfl
  preimage_map _ := rfl

instance : uliftFunctor.{u, v}.Faithful := uliftFunctorFullyFaithful.faithful

instance : uliftFunctor.{u, v}.Full := uliftFunctorFullyFaithful.full

end ProfiniteGrp
