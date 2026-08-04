import Langlands.ProfiniteGrpUlift
import Langlands.FiniteIndexNormalSubgroupMulEquiv

/-!
# The profinite completion commutes with universe lifting

`ProfiniteGrp.ProfiniteCompletion.completion (ULift.{v} G) ≅ ULift.{v} (completion G)`, for `G :
GrpCat.{0}` -- fixed at universe `0` since `ProfiniteGrp.uliftFunctor_preservesLimit`
(`Langlands.ProfiniteGrpUlift`) only preserves limits of diagrams indexed by a category `J : Type`
(literally universe `0`, confirmed by `#check`; the module docstring there overstates the
generality achieved), and the index category here is `FiniteIndexNormalSubgroup G`, which lives in
the same universe as `G` itself. This is exactly the case needed: comparing `Zhat` (hardwired to
universe `0`, being the completion of `Multiplicative ℤ : Type`) against a `ProfiniteGrp` in an
arbitrary universe `v` (such as `InfiniteGalois.profiniteGalGrp 𝓀[K] kbar` in
`Langlands.WeilGroup`, for `K` of universe `v`) via `ProfiniteGrp.ProfiniteCompletion.completion
(GrpCat.of (ULift.{v} (Multiplicative ℤ)))`, itself now identified with `ULift.{v} Zhat` here.

## Main definitions and results

* `ProfiniteGrp.ProfiniteCompletion.diagramULiftNatIso` : the natural isomorphism between the two
  `FiniteIndexNormalSubgroup (ULift.{v} G)`-indexed diagrams valued in `ProfiniteGrp` -- the
  finite-quotient diagram of `ULift.{v} G` directly, versus the finite-quotient diagram of `G`
  precomposed with the index-category equivalence and postcomposed with `ProfiniteGrp.uliftFunctor`.
* `ProfiniteGrp.ProfiniteCompletion.completionULiftIso` : the resulting isomorphism `completion
  (ULift.{v} G) ≅ ProfiniteGrp.uliftFunctor.obj (completion G)`, obtained by combining the natural
  isomorphism above with `CategoryTheory.Limits.HasLimit.isoOfEquivalence` (invariance of the limit
  under precomposition with an equivalence of the index category) and the fact that
  `ProfiniteGrp.uliftFunctor` preserves limits of small diagrams
  (`ProfiniteGrp.uliftFunctor_preservesLimit`).

## Proof idea

Both diagrams are indexed by `FiniteIndexNormalSubgroup (ULift.{v} G)`. At each index `H`, the
degreewise group isomorphism is `QuotientGroup.congr` (transporting the quotient by `H.toSubgroup`
along `MulEquiv.ulift : ULift.{v} G ≃* G`) composed with `MulEquiv.ulift.symm` on the resulting
quotient of `G`, to land back in a `ULift`. Naturality against the diagrams' transition maps
(`QuotientGroup.map` for the finite-quotient diagram) is checked by hand on representatives.
-/

@[expose] public section

universe v

open CategoryTheory Limits

namespace ProfiniteGrp.ProfiniteCompletion

variable (G : GrpCat.{0})

/-- The index-category equivalence identifying finite-index normal subgroups of `ULift.{v} G`
with those of `G`, transported along `MulEquiv.ulift`. -/
noncomputable def indexEquiv :
    FiniteIndexNormalSubgroup (ULift.{v} G) ≌ FiniteIndexNormalSubgroup G :=
  (FiniteIndexNormalSubgroup.orderIsoMulEquiv (MulEquiv.ulift : ULift.{v} G ≃* G)).equivalence

@[simp]
theorem indexEquiv_functor_obj (H : FiniteIndexNormalSubgroup (ULift.{v} G)) :
    (indexEquiv G).functor.obj H =
      FiniteIndexNormalSubgroup.mapMulEquiv (MulEquiv.ulift : ULift.{v} G ≃* G) H := rfl

/-- The degreewise group isomorphism underlying the natural isomorphism of diagrams: the quotient
of `ULift.{v} G` by a finite-index normal subgroup `H` is (via `MulEquiv.ulift`) isomorphic to the
`ULift` of the corresponding quotient of `G`. -/
noncomputable def quotientULiftMulEquiv (H : FiniteIndexNormalSubgroup (ULift.{v} G)) :
    (ULift.{v} G) ⧸ H.toSubgroup ≃*
      ULift.{v} (G ⧸ (FiniteIndexNormalSubgroup.mapMulEquiv
        (MulEquiv.ulift : ULift.{v} G ≃* G) H).toSubgroup) :=
  (QuotientGroup.congr H.toSubgroup _ (MulEquiv.ulift : ULift.{v} G ≃* G)
    (FiniteIndexNormalSubgroup.toSubgroup_mapMulEquiv _ H).symm).trans MulEquiv.ulift.symm

/-- The degreewise component of the natural isomorphism, packaged as a `ProfiniteGrp` isomorphism
(continuity is automatic in both directions since the finite quotients involved carry the discrete
topology, via `ofFiniteGrp`). -/
noncomputable def diagramULiftIsoComponent (H : FiniteIndexNormalSubgroup (ULift.{v} G)) :
    (diagram (GrpCat.of (ULift.{v} G))).obj H ≅
      ProfiniteGrp.uliftFunctor.{v, 0}.obj ((diagram G).obj
        (FiniteIndexNormalSubgroup.mapMulEquiv (MulEquiv.ulift : ULift.{v} G ≃* G) H)) :=
  haveI : DiscreteTopology ((diagram G).obj
      (FiniteIndexNormalSubgroup.mapMulEquiv (MulEquiv.ulift : ULift.{v} G ≃* G) H)) := ⟨rfl⟩
  haveI : DiscreteTopology
      (ProfiniteGrp.uliftFunctor.{v, 0}.obj ((diagram G).obj
        (FiniteIndexNormalSubgroup.mapMulEquiv (MulEquiv.ulift : ULift.{v} G ≃* G) H))) :=
    ProfiniteGrp.uLift.discreteTopology
  ProfiniteGrp.isoOfMulEquiv (quotientULiftMulEquiv G H) continuous_bot continuous_of_discreteTopology

/-- **The natural isomorphism between the two `ProfiniteGrp`-valued diagrams**: the finite-quotient
diagram of `ULift.{v} G`, versus the finite-quotient diagram of `G` precomposed with the
index-category equivalence `indexEquiv` and postcomposed with `ProfiniteGrp.uliftFunctor`. -/
noncomputable def diagramULiftNatIso :
    diagram (GrpCat.of (ULift.{v} G)) ≅
      (indexEquiv G).functor ⋙ diagram G ⋙ ProfiniteGrp.uliftFunctor.{v, 0} :=
  NatIso.ofComponents (fun H => diagramULiftIsoComponent G H) (by
    intro H H' f
    have h : H ≤ H' := leOfHom f
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro (x : (ULift.{v} G) ⧸ H.toSubgroup)
    induction x using QuotientGroup.induction_on with
    | _ x =>
      show ((diagram (GrpCat.of (ULift.{v} G))).map f ≫ (diagramULiftIsoComponent G H').hom)
          (QuotientGroup.mk x) =
        ((diagramULiftIsoComponent G H).hom ≫
          ((indexEquiv G).functor ⋙ diagram G ⋙ ProfiniteGrp.uliftFunctor.{v, 0}).map f)
          (QuotientGroup.mk x)
      simp only [ConcreteCategory.comp_apply]
      show (diagramULiftIsoComponent G H').hom
          (QuotientGroup.map H.toSubgroup H'.toSubgroup (MonoidHom.id _) h (QuotientGroup.mk x)) =
        ProfiniteGrp.uliftFunctor.{v, 0}.map ((diagram G).map
          (homOfLE (FiniteIndexNormalSubgroup.mapMulEquiv_mono
            (MulEquiv.ulift : ULift.{v} G ≃* G) h)))
          ((diagramULiftIsoComponent G H).hom (QuotientGroup.mk x))
      erw [QuotientGroup.map_mk']
      show (quotientULiftMulEquiv G H').toMonoidHom (QuotientGroup.mk (MonoidHom.id _ x)) =
        _
      simp only [MonoidHom.id_apply, quotientULiftMulEquiv, MulEquiv.toMonoidHom_eq_coe]
      rfl)

/-- **The profinite completion commutes with universe lifting**: `completion (ULift.{v} G)` is
isomorphic to `ProfiniteGrp.uliftFunctor.obj (completion G)`, i.e. to `ULift.{v} (completion G)`.
Combines `diagramULiftNatIso` (the natural isomorphism of diagrams) with
`CategoryTheory.Limits.HasLimit.isoOfEquivalence` (limit invariance under precomposing with an
equivalence of the index category) and `CategoryTheory.preservesLimitIso` (since
`ProfiniteGrp.uliftFunctor` preserves the limit of the small diagram `diagram G`). -/
noncomputable def completionULiftIso :
    completion (GrpCat.of (ULift.{v} G)) ≅ ProfiniteGrp.uliftFunctor.{v, 0}.obj (completion G) := by
  unfold completion
  exact (ProfiniteGrp.limitIsoLimit (diagram (GrpCat.of (ULift.{v} G)))).trans
    ((HasLimit.isoOfEquivalence (F := diagram (GrpCat.of (ULift.{v} G)))
        (G := diagram G ⋙ ProfiniteGrp.uliftFunctor.{v, 0}) (indexEquiv.{v} G)
        (diagramULiftNatIso.{v} G).symm).trans
      ((CategoryTheory.preservesLimitIso ProfiniteGrp.uliftFunctor.{v, 0} (diagram G)).symm.trans
        (ProfiniteGrp.uliftFunctor.{v, 0}.mapIso (ProfiniteGrp.limitIsoLimit (diagram G)).symm)))

end ProfiniteGrp.ProfiniteCompletion
