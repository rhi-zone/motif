import Mathlib.GroupTheory.FiniteIndexNormalSubgroup

/-!
# Transport of finite-index normal subgroups along a group isomorphism

Pure group theory, with no connection to the rest of `Langlands` -- a general-purpose fact: a
`MulEquiv e : G ≃* G'` induces an order isomorphism between the finite-index-normal-subgroup
lattices `FiniteIndexNormalSubgroup G` and `FiniteIndexNormalSubgroup G'` (the indexing categories
of the diagrams defining the profinite completions of `G` and `G'`,
`Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion`), preserving index.

This is a standalone step towards relating `ProfiniteGrp.ProfiniteCompletion.completion` at
different universes via `ProfiniteGrp.uliftFunctor` (`Langlands.ProfiniteGrpUlift`): the
finite-index-normal-subgroup lattices of `G` and `ULift.{v} G` (linked by `MulEquiv.ulift : ULift.{v}
G ≃* G`) need to be identified, as the first step in comparing the diagrams
`FiniteIndexNormalSubgroup (ULift.{v} G) ⥤ FiniteGrp` and `FiniteIndexNormalSubgroup G ⥤ FiniteGrp`.
The remaining steps (a natural isomorphism between the two diagrams valued in `ProfiniteGrp`, and
invoking `CategoryTheory.Limits.HasLimit.isoOfEquivalence` to conclude an isomorphism of the
completions) are not attempted here.

## Main results

* `FiniteIndexNormalSubgroup.mapMulEquiv` : transport of a finite-index normal subgroup along a
  `MulEquiv`.
* `FiniteIndexNormalSubgroup.index_mapMulEquiv` : transport preserves the index.
* `FiniteIndexNormalSubgroup.orderIsoMulEquiv` : the induced order isomorphism between the two
  finite-index-normal-subgroup lattices.

## Proof idea

For `e : G ≃* G'` and `H : Subgroup G`, `Subgroup.index_map` gives `(H.map e).index = (H ⊔
e.ker).index * e.range.index`; since `e` is bijective, `e.ker = ⊥` (so `H ⊔ e.ker = H`) and
`e.range = ⊤` (so its index is `1`), giving `(H.map e).index = H.index`. Normality transports via
`Subgroup.Normal.map` (using surjectivity of `e`). Together these show `H.map e.toMonoidHom` is
again finite-index and normal whenever `H` is, giving `FiniteIndexNormalSubgroup.mapMulEquiv`;
`mapMulEquiv e.symm` is a two-sided inverse (via `Subgroup.map_map` and `Subgroup.map_id`, since
`e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id`), and both directions are order-preserving
(pushforward of subgroups along an injective map preserves `≤`), giving the order isomorphism.
-/

@[expose] public section

namespace FiniteIndexNormalSubgroup

variable {G G' : Type*} [Group G] [Group G']

/-- Transport a finite-index normal subgroup along a group isomorphism `e : G ≃* G'`, via the
pushforward `Subgroup.map e.toMonoidHom`. -/
def mapMulEquiv (e : G ≃* G') (H : FiniteIndexNormalSubgroup G) : FiniteIndexNormalSubgroup G' :=
  haveI : (Subgroup.map e.toMonoidHom H.toSubgroup).Normal :=
    H.isNormal'.map e.toMonoidHom e.surjective
  haveI : (Subgroup.map e.toMonoidHom H.toSubgroup).FiniteIndex := by
    refine Subgroup.FiniteIndex.mk ?_
    rw [Subgroup.index_map, (MonoidHom.ker_eq_bot_iff _).mpr e.injective, sup_bot_eq,
      MonoidHom.range_eq_top_of_surjective _ e.surjective, Subgroup.index_top, mul_one]
    exact Subgroup.finiteIndex_iff.mp H.isFiniteIndex'
  FiniteIndexNormalSubgroup.ofSubgroup (Subgroup.map e.toMonoidHom H.toSubgroup)

@[simp]
theorem toSubgroup_mapMulEquiv (e : G ≃* G') (H : FiniteIndexNormalSubgroup G) :
    (mapMulEquiv e H).toSubgroup = Subgroup.map e.toMonoidHom H.toSubgroup := rfl

/-- Transport along a `MulEquiv` preserves the index of a finite-index normal subgroup. -/
theorem index_mapMulEquiv (e : G ≃* G') (H : FiniteIndexNormalSubgroup G) :
    (mapMulEquiv e H).toSubgroup.index = H.toSubgroup.index := by
  rw [toSubgroup_mapMulEquiv, Subgroup.index_map, (MonoidHom.ker_eq_bot_iff _).mpr e.injective,
    sup_bot_eq, MonoidHom.range_eq_top_of_surjective _ e.surjective, Subgroup.index_top, mul_one]

@[simp]
theorem mapMulEquiv_symm_mapMulEquiv (e : G ≃* G') (H : FiniteIndexNormalSubgroup G) :
    mapMulEquiv e.symm (mapMulEquiv e H) = H := by
  apply FiniteIndexNormalSubgroup.toSubgroup_injective
  show (mapMulEquiv e.symm (mapMulEquiv e H)).toSubgroup = H.toSubgroup
  rw [toSubgroup_mapMulEquiv, toSubgroup_mapMulEquiv, Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x; simp
  rw [this, Subgroup.map_id]

@[simp]
theorem mapMulEquiv_mapMulEquiv_symm (e : G ≃* G') (H : FiniteIndexNormalSubgroup G') :
    mapMulEquiv e (mapMulEquiv e.symm H) = H := by
  apply FiniteIndexNormalSubgroup.toSubgroup_injective
  show (mapMulEquiv e (mapMulEquiv e.symm H)).toSubgroup = H.toSubgroup
  rw [toSubgroup_mapMulEquiv, toSubgroup_mapMulEquiv, Subgroup.map_map]
  have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' := by
    ext x; simp
  rw [this, Subgroup.map_id]

theorem mapMulEquiv_mono (e : G ≃* G') {H₁ H₂ : FiniteIndexNormalSubgroup G} (h : H₁ ≤ H₂) :
    mapMulEquiv e H₁ ≤ mapMulEquiv e H₂ :=
  Subgroup.map_mono h

/-- The order isomorphism between the finite-index-normal-subgroup lattices of `G` and `G'`
induced by a group isomorphism `e : G ≃* G'`. -/
def orderIsoMulEquiv (e : G ≃* G') :
    FiniteIndexNormalSubgroup G ≃o FiniteIndexNormalSubgroup G' where
  toFun := mapMulEquiv e
  invFun := mapMulEquiv e.symm
  left_inv := mapMulEquiv_symm_mapMulEquiv e
  right_inv := mapMulEquiv_mapMulEquiv_symm e
  map_rel_iff' {H₁ H₂} := by
    refine ⟨fun h => ?_, mapMulEquiv_mono e⟩
    have := mapMulEquiv_mono e.symm h
    simpa using this

end FiniteIndexNormalSubgroup
