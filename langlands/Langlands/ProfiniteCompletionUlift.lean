import Langlands.ProfiniteGrpUlift
import Langlands.FiniteIndexNormalSubgroupMulEquiv

/-!
# The profinite completion commutes with universe lifting

For `G : GrpCat.{0}`, `ProfiniteGrp.ProfiniteCompletion.completion (ULift.{v} G)` is isomorphic to
`ULift.{v} (completion G)`. The base group is fixed at universe `0` because
`ProfiniteGrp.uliftFunctor_preservesLimit` (`Langlands.ProfiniteGrpUlift`) applies to diagrams
indexed by `J : Type`, and the index category here is `FiniteIndexNormalSubgroup G`, which lives in
the universe of `G`.

This places the profinite completion of a group in `Type` inside `ProfiniteGrp.{v}` for an
arbitrary universe `v`, where it can be compared with profinite groups arising there: the
completion of `ULift.{v} G`, which lives in `ProfiniteGrp.{v}` by construction, is identified with
the universe lift of the completion of `G`.

## Main definitions and results

* `ProfiniteGrp.ProfiniteCompletion.indexEquiv` : the equivalence of index categories
  `FiniteIndexNormalSubgroup (ULift.{v} G) ≌ FiniteIndexNormalSubgroup G` induced by
  `MulEquiv.ulift`.
* `ProfiniteGrp.ProfiniteCompletion.diagramULiftNatIso` : the natural isomorphism between the
  finite-quotient diagram of `ULift.{v} G` and the finite-quotient diagram of `G` precomposed with
  `indexEquiv` and postcomposed with `ProfiniteGrp.uliftFunctor`.
* `ProfiniteGrp.ProfiniteCompletion.completionULiftIso` : the resulting isomorphism
  `completion (ULift.{v} G) ≅ ProfiniteGrp.uliftFunctor.obj (completion G)`.
-/

@[expose] public section

universe v

open CategoryTheory Limits

namespace ProfiniteGrp.ProfiniteCompletion

variable (G : GrpCat.{0})

/-- The equivalence of index categories identifying the finite-index normal subgroups of
`ULift.{v} G` with those of `G`, induced by `MulEquiv.ulift` through
`FiniteIndexNormalSubgroup.orderIsoMulEquiv`. -/
noncomputable def indexEquiv :
    FiniteIndexNormalSubgroup (ULift.{v} G) ≌ FiniteIndexNormalSubgroup G :=
  (FiniteIndexNormalSubgroup.orderIsoMulEquiv (MulEquiv.ulift : ULift.{v} G ≃* G)).equivalence

@[simp]
theorem indexEquiv_functor_obj (H : FiniteIndexNormalSubgroup (ULift.{v} G)) :
    (indexEquiv G).functor.obj H =
      FiniteIndexNormalSubgroup.mapMulEquiv (MulEquiv.ulift : ULift.{v} G ≃* G) H := rfl

/-- The quotient of `ULift.{v} G` by a finite-index normal subgroup `H` is isomorphic to the
universe lift of the quotient of `G` by the corresponding subgroup: `QuotientGroup.congr` along
`MulEquiv.ulift`, followed by `MulEquiv.ulift.symm`. -/
noncomputable def quotientULiftMulEquiv (H : FiniteIndexNormalSubgroup (ULift.{v} G)) :
    (ULift.{v} G) ⧸ H.toSubgroup ≃*
      ULift.{v} (G ⧸ (FiniteIndexNormalSubgroup.mapMulEquiv
        (MulEquiv.ulift : ULift.{v} G ≃* G) H).toSubgroup) :=
  (QuotientGroup.congr H.toSubgroup _ (MulEquiv.ulift : ULift.{v} G ≃* G)
    (FiniteIndexNormalSubgroup.toSubgroup_mapMulEquiv _ H).symm).trans MulEquiv.ulift.symm

/-- The component of `diagramULiftNatIso` at `H`, namely `quotientULiftMulEquiv` packaged as an
isomorphism of profinite groups. Continuity in both directions is automatic, the finite quotients
involved carrying the discrete topology. -/
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

/-- **The natural isomorphism between the two `ProfiniteGrp`-valued diagrams** indexed by
`FiniteIndexNormalSubgroup (ULift.{v} G)`: the finite-quotient diagram of `ULift.{v} G`, and the
finite-quotient diagram of `G` precomposed with `indexEquiv` and postcomposed with
`ProfiniteGrp.uliftFunctor`. Naturality against the transition maps `QuotientGroup.map` is checked
on representatives. -/
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
isomorphic to `ProfiniteGrp.uliftFunctor.obj (completion G)`, that is, to `ULift.{v} (completion
G)`. Combines `diagramULiftNatIso` with `CategoryTheory.Limits.HasLimit.isoOfEquivalence`, the
invariance of a limit under precomposition with an equivalence of the index category, and
`CategoryTheory.preservesLimitIso` for `ProfiniteGrp.uliftFunctor` applied to `diagram G`. -/
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
