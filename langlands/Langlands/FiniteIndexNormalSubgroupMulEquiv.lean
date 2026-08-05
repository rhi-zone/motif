import Mathlib.GroupTheory.FiniteIndexNormalSubgroup

/-!
# Transport of finite-index normal subgroups along a group isomorphism

A group isomorphism `e : G ≃* G'` induces an index-preserving order isomorphism between the
lattices `FiniteIndexNormalSubgroup G` and `FiniteIndexNormalSubgroup G'`. Since these lattices are
the indexing categories of the diagrams defining profinite completions
(`Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion`), this is the first step in comparing
the profinite completions of isomorphic groups; `Langlands.ProfiniteCompletionUlift` carries that
out for `MulEquiv.ulift : ULift.{v} G ≃* G`.

## Main results

* `FiniteIndexNormalSubgroup.mapMulEquiv` : pushforward of a finite-index normal subgroup along a
  `MulEquiv`.
* `FiniteIndexNormalSubgroup.index_mapMulEquiv` : the pushforward preserves the index.
* `FiniteIndexNormalSubgroup.orderIsoMulEquiv` : the induced order isomorphism.

## Implementation notes

Index preservation is `Subgroup.index_map`, which gives
`(H.map e).index = (H ⊔ e.ker).index * e.range.index`, together with `e.ker = ⊥` and `e.range = ⊤`.
Normality transports by `Subgroup.Normal.map` along the surjection `e`. The inverse of `mapMulEquiv
e` is `mapMulEquiv e.symm`, both being pushforwards along injective maps and hence monotone.
-/

@[expose] public section

namespace FiniteIndexNormalSubgroup

variable {G G' : Type*} [Group G] [Group G']

/-- The pushforward `Subgroup.map e.toMonoidHom` of a finite-index normal subgroup along a group
isomorphism `e : G ≃* G'`, again finite-index and normal. -/
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

/-- Pushforward along a `MulEquiv` preserves the index of a finite-index normal subgroup. -/
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

/-- The order isomorphism `FiniteIndexNormalSubgroup G ≃o FiniteIndexNormalSubgroup G'` induced by
a group isomorphism `e : G ≃* G'`, given by pushforward along `e` and along `e.symm`. -/
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
