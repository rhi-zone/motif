import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# The universe lift functor for profinite groups

Mirrors `GrpCat.uliftFunctor` (`Mathlib.Algebra.Category.Grp.Ulift`) and `TopCat.uliftFunctor`
(`Mathlib.Topology.Category.TopCat.ULift`): the functor sending a profinite group `P : ProfiniteGrp.{u}`
to the homeomorphic/isomorphic profinite group `ULift.{v} P : ProfiniteGrp.{max u v}`, fully
faithful, and (for *small* diagrams -- see below) preserving limits. General-purpose
category-theory/topology infrastructure, with no dependency on the rest of `Langlands`.

This is the piece needed to compare `Zhat` (hardwired to universe `0`, being the profinite
completion of `Multiplicative ℤ : Type`) against a `ProfiniteGrp` living in an arbitrary universe
`u` (such as `Langlands.WeilGroup`'s `InfiniteGalois.profiniteGalGrp 𝓀[K] kbar`): instead of `Zhat`
directly, one compares against `ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (ULift.{u}
(Multiplicative ℤ)))`, which lives in `ProfiniteGrp.{u}`.

## Main definitions and results

* `ProfiniteGrp.uliftFunctor` : the universe lift functor `ProfiniteGrp.{u} ⥤ ProfiniteGrp.{max u v}`.
* `ProfiniteGrp.uliftFunctorFullyFaithful` : it is fully faithful.
* `ProfiniteGrp.uliftFunctor_preservesLimit` : it preserves the limit of any *small* diagram
  (`J : Type` with `SmallCategory J`), at arbitrary source/target universes.

## The preserves-limits gap, closed

A first attempt tried to mirror `GrpCat.uliftFunctor_preservesLimit`'s proof by composing the
*existing* `PreservesLimits` instances for `Profinite`'s/`ProfiniteGrp`'s forgetful functors
(`Profinite.forget_preservesLimits`, etc.). This does not typecheck for a general target universe:
those instances are stated as `PreservesLimitsOfSize.{w, w}` for `w` the *domain category's own*
universe, so `PreservesLimit K (forget₂ ProfiniteGrp.{v} Profinite ⋙ forget Profinite)` for
`J : Type` `[SmallCategory J]`, `K : J ⥤ ProfiniteGrp.{v}` fails to synthesize except at the
coincidental `v = 0` (checked directly via `inferInstance` in a scratch file).

The fix does not need that composition at all. `Profinite.limitCone`/`Profinite.limitConeIsLimit`
and `ProfiniteGrp.limitCone`/`ProfiniteGrp.limitConeIsLimit` are *already* stated at exactly the
generality needed (`{J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})`, independent
`u`), and -- this is the key fact, confirmed by `rfl` -- forgetting `ProfiniteGrp.limitCone K` to
`Type` is *definitionally equal* to `CategoryTheory.Limits.Types.limitCone (K ⋙ forget
ProfiniteGrp)` (both are literally the sections-of-a-product construction, all the way down through
`ProfiniteGrp → Profinite → CompHaus → TopCat → Type`). Since `Types.limitConeIsLimit` is already
proved at arbitrary universes (the foundational construction everything else is built from), this
identity transports it directly into an `IsLimit` of the *forgetful image* of `ProfiniteGrp`'s own
canonical cone, and `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone` (a functor
preserving *one* limit cone for a diagram preserves *every* limit cone for it) upgrades this to
`PreservesLimit K (forget ProfiniteGrp)` for arbitrary source universe -- with no dependence on the
restrictive pre-existing instances at all. Applying this twice (once for the source, once for the
`uliftFunctor`-composed target diagram) plus `reflectsLimit_of_reflectsIsomorphisms` (using the
already-available `(forget ProfiniteGrp).ReflectsIsomorphisms`) gives `PreservesLimit K
uliftFunctor` exactly as in `GrpCat.uliftFunctor_preservesLimit`'s proof.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace ProfiniteGrp

instance uLift.totallyDisconnectedSpace {G : Type*} [TopologicalSpace G]
    [TotallyDisconnectedSpace G] : TotallyDisconnectedSpace (ULift.{v} G) :=
  Homeomorph.ulift.symm.totallyDisconnectedSpace

instance uLift.discreteTopology {G : Type*} [TopologicalSpace G] [DiscreteTopology G] :
    DiscreteTopology (ULift.{v} G) :=
  Homeomorph.ulift.symm.discreteTopology

/-- Package a `MulEquiv` between the underlying types of two `ProfiniteGrp`s as an isomorphism,
given continuity of both directions. General-purpose glue for building `ProfiniteGrp` isomorphisms
between finite (discretely-topologised) quotients, where continuity is typically automatic via
`continuous_of_discreteTopology`. -/
def isoOfMulEquiv {X Y : ProfiniteGrp} (e : X ≃* Y) (hf : Continuous e) (hg : Continuous e.symm) :
    X ≅ Y where
  hom := ProfiniteGrp.ofHom
    { toFun := e, map_one' := map_one e, map_mul' := map_mul e, continuous_toFun := hf }
  inv := ProfiniteGrp.ofHom
    { toFun := e.symm, map_one' := map_one e.symm, map_mul' := map_mul e.symm,
      continuous_toFun := hg }
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

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

/-- **The forgetful functor `ProfiniteGrp.{u} ⥤ Type u` preserves the limit of any small
diagram**, at any source universe `u`. Proved directly from `ProfiniteGrp.limitConeIsLimit`
together with the fact (`rfl`) that its forgetful image is definitionally
`CategoryTheory.Limits.Types.limitCone`, rather than via the restrictive pre-existing
`PreservesLimits (forget₂ ProfiniteGrp Profinite)`-style instances (see the module docstring). -/
theorem forget_preservesLimit_of_smallCategory {J : Type} [SmallCategory J]
    (K : J ⥤ ProfiniteGrp.{u}) : PreservesLimit K (forget ProfiniteGrp) :=
  preservesLimit_of_preserves_limit_cone (ProfiniteGrp.limitConeIsLimit K)
    (show IsLimit ((forget ProfiniteGrp).mapCone (ProfiniteGrp.limitCone K)) from
      Types.limitConeIsLimit (K ⋙ forget ProfiniteGrp))

/-- The universe lift functor for profinite groups preserves the limit of any small diagram, at
arbitrary source and target universes. -/
noncomputable instance uliftFunctor_preservesLimit {J : Type} [SmallCategory J]
    (K : J ⥤ ProfiniteGrp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
  preserves {c} hc := by
    haveI : PreservesLimit K (forget ProfiniteGrp.{u}) :=
      forget_preservesLimit_of_smallCategory K
    haveI : PreservesLimit (K ⋙ uliftFunctor.{v, u}) (forget ProfiniteGrp.{max u v}) :=
      forget_preservesLimit_of_smallCategory _
    haveI : ReflectsLimit (K ⋙ uliftFunctor.{v, u}) (forget ProfiniteGrp.{max u v}) :=
      reflectsLimit_of_reflectsIsomorphisms _ (forget ProfiniteGrp.{max u v})
    exact ⟨isLimitOfReflects (forget ProfiniteGrp.{max u v}) <|
      isLimitOfPreserves CategoryTheory.uliftFunctor.{v}
        (isLimitOfPreserves (forget ProfiniteGrp.{u}) hc)⟩

/-- The universe lift functor for profinite groups preserves limits of every small shape. -/
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type} [SmallCategory J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where

/-- **The concrete limit `ProfiniteGrp.limit` agrees with the abstract categorical limit**
`CategoryTheory.Limits.limit`. `ProfiniteGrp.limit F` (the "sections of the product" subgroup,
`ProfiniteGrp.limitConePtAux`) is a genuinely different term from `CategoryTheory.Limits.limit F`
(built via `Classical.choice` on the `HasLimit` instance), even though both live in the same
`ProfiniteGrp` and are canonically isomorphic -- this bridges them, via
`CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso` comparing `ProfiniteGrp.limitCone`'s
universal property (`ProfiniteGrp.limitConeIsLimit`) against the generic `limit.isLimit`. Needed
because `ProfiniteGrp.ProfiniteCompletion.completion` is defined via the former (`limit (diagram
G)` inside `namespace ProfiniteGrp`, which resolves to the bespoke `ProfiniteGrp.limit`), while
general limit-comparison lemmas (`HasLimit.isoOfEquivalence`, `preservesLimitIso`) are stated for
the latter. -/
noncomputable def limitIsoLimit {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u}) :
    ProfiniteGrp.limit F ≅ CategoryTheory.Limits.limit F :=
  (ProfiniteGrp.limitConeIsLimit F).conePointUniqueUpToIso (CategoryTheory.Limits.limit.isLimit F)

end ProfiniteGrp
