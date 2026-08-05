import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# The universe lift functor for profinite groups

The functor `ProfiniteGrp.{u} ⥤ ProfiniteGrp.{max u v}` sending a profinite group `P` to the
isomorphic profinite group `ULift.{v} P`, mirroring `GrpCat.uliftFunctor`
(`Mathlib.Algebra.Category.Grp.Ulift`) and `TopCat.uliftFunctor`
(`Mathlib.Topology.Category.TopCat.ULift`). It is fully faithful, and preserves limits of diagrams
indexed by a small category `J : Type`, at arbitrary source and target universes.

## Main definitions and results

* `ProfiniteGrp.uliftFunctor` : the universe lift functor.
* `ProfiniteGrp.uliftFunctorFullyFaithful` : it is fully faithful.
* `ProfiniteGrp.forget_preservesLimit_of_smallCategory` : `forget ProfiniteGrp.{u}` preserves
  limits of `J : Type`-indexed diagrams, at any `u`.
* `ProfiniteGrp.uliftFunctor_preservesLimit`, `ProfiniteGrp.uliftFunctor_preservesLimitsOfShape` :
  the universe lift functor preserves limits of small shapes.
* `ProfiniteGrp.limitIsoLimit` : the concrete limit `ProfiniteGrp.limit` agrees with the
  categorical limit `CategoryTheory.Limits.limit`.
* `ProfiniteGrp.isoOfMulEquiv` : a `MulEquiv` continuous in both directions is an isomorphism of
  profinite groups.

## Implementation notes

The limit-preservation statements are not obtained from the existing `PreservesLimits` instances
for the forgetful functors out of `Profinite` and `ProfiniteGrp`. Those are stated as
`PreservesLimitsOfSize.{w, w}` with `w` the domain category's own universe, so for `J : Type` and
`K : J ⥤ ProfiniteGrp.{u}` the instance
`PreservesLimit K (forget₂ ProfiniteGrp.{u} Profinite ⋙ forget Profinite)` fails to synthesize
except at `u = 0`.

`forget_preservesLimit_of_smallCategory` avoids them. `ProfiniteGrp.limitCone` and
`ProfiniteGrp.limitConeIsLimit` are already stated at the required generality, and the forgetful
image of `ProfiniteGrp.limitCone K` is definitionally `CategoryTheory.Limits.Types.limitCone
(K ⋙ forget ProfiniteGrp)`, both being the sections of the product all the way down through
`ProfiniteGrp → Profinite → CompHaus → TopCat → Type`. So `Types.limitConeIsLimit`, which holds at
arbitrary universes, transports along that identity, and
`CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone` upgrades it to preservation of every
limit cone for the diagram. Applying this to the source diagram and to its `uliftFunctor`-composite,
together with `reflectsLimit_of_reflectsIsomorphisms`, then yields
`uliftFunctor_preservesLimit` as in the proof of `GrpCat.uliftFunctor_preservesLimit`.
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

/-- A `MulEquiv` between the underlying groups of two profinite groups, continuous in both
directions, as an isomorphism in `ProfiniteGrp`. For finite quotients, which carry the discrete
topology, both continuity hypotheses are discharged by `continuous_of_discreteTopology`. -/
def isoOfMulEquiv {X Y : ProfiniteGrp} (e : X ≃* Y) (hf : Continuous e) (hg : Continuous e.symm) :
    X ≅ Y where
  hom := ProfiniteGrp.ofHom
    { toFun := e, map_one' := map_one e, map_mul' := map_mul e, continuous_toFun := hf }
  inv := ProfiniteGrp.ofHom
    { toFun := e.symm, map_one' := map_one e.symm, map_mul' := map_mul e.symm,
      continuous_toFun := hg }
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

/-- The universe lift functor for profinite groups, sending `P : ProfiniteGrp.{u}` to the
isomorphic profinite group `ULift.{v} P : ProfiniteGrp.{max u v}`. -/
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

/-- **The forgetful functor out of `ProfiniteGrp.{u}` preserves the limit of any `J : Type`-indexed
diagram**, at any universe `u`. Proved from `ProfiniteGrp.limitConeIsLimit` together with the
definitional identification of its forgetful image with `CategoryTheory.Limits.Types.limitCone`,
rather than from the existing `PreservesLimits (forget₂ ProfiniteGrp Profinite)`-style instances,
which do not apply at general `u`; see the module docstring. -/
theorem forget_preservesLimit_of_smallCategory {J : Type} [SmallCategory J]
    (K : J ⥤ ProfiniteGrp.{u}) : PreservesLimit K (forget ProfiniteGrp) :=
  preservesLimit_of_preserves_limit_cone (ProfiniteGrp.limitConeIsLimit K)
    (show IsLimit ((forget ProfiniteGrp).mapCone (ProfiniteGrp.limitCone K)) from
      Types.limitConeIsLimit (K ⋙ forget ProfiniteGrp))

/-- The universe lift functor for profinite groups preserves the limit of any `J : Type`-indexed
diagram, at arbitrary source and target universes. -/
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

/-- The universe lift functor for profinite groups preserves limits of every shape `J : Type`. -/
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type} [SmallCategory J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where

/-- **The concrete limit `ProfiniteGrp.limit` agrees with the categorical limit**
`CategoryTheory.Limits.limit`, by comparing the universal property `ProfiniteGrp.limitConeIsLimit`
with `limit.isLimit` through `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`.

The two are distinct terms: `ProfiniteGrp.limit F` is the subgroup of sections of the product
(`ProfiniteGrp.limitConePtAux`), while `CategoryTheory.Limits.limit F` is obtained by
`Classical.choice` from the `HasLimit` instance. The isomorphism is needed because
`ProfiniteGrp.ProfiniteCompletion.completion` is defined using the former — `limit (diagram G)`
inside `namespace ProfiniteGrp` resolves to `ProfiniteGrp.limit` — whereas the general
limit-comparison lemmas `HasLimit.isoOfEquivalence` and `preservesLimitIso` are stated for the
latter. -/
noncomputable def limitIsoLimit {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u}) :
    ProfiniteGrp.limit F ≅ CategoryTheory.Limits.limit F :=
  (ProfiniteGrp.limitConeIsLimit F).conePointUniqueUpToIso (CategoryTheory.Limits.limit.isLimit F)

end ProfiniteGrp
