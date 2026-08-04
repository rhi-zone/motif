import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Finite-index (normal) subgroups of `ℤ` are classified by index

Pure group theory, with no connection to the rest of `Langlands` -- a general-purpose fact: for
every `n ≠ 0`, there is a *unique* subgroup of `ℤ` (equivalently, of `Multiplicative ℤ`) of index
`n`, namely `n • ℤ` (`AddSubgroup.zmultiples n`) / its multiplicative image. This is exactly the
classification needed to identify the diagram `n ↦ ℤ ⧸ nℤ` defining the profinite integers `ℤ̂`
(`ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))`,
`Langlands.WeilGroup.Zhat`) with the finite-index-normal-subgroup diagram
`FiniteIndexNormalSubgroup (Multiplicative ℤ) ⥤ FiniteGrp` that `Zhat` is literally built from.

A Loogle search for `AddSubgroup.zmultiples`/index-flavoured names and for `Int.subgroup_eq_zmultiples`
directly found nothing packaging this; but searching by type shape (the classification of subgroups
of a cyclic group, `IsAddCyclic`/`AddSubgroup.isAddCyclic`, together with `AddSubgroup.toIntSubmodule`
witnessing that `AddSubgroup ℤ ≃o Submodule ℤ ℤ`, i.e. this is really the statement that `ℤ` is a
PID in disguise) found the two pieces this file assembles: `AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top`
(every subgroup of a cyclic group is again cyclic, i.e. of the form `zmultiples g`) and
`Int.index_zmultiples` (the index of `zmultiples g` is `g.natAbs`), both already in Mathlib.

## Main results

* `AddSubgroup.existsUnique_index_eq_of_ne_zero` : for `n ≠ 0`, a unique `H : AddSubgroup ℤ` has
  `H.index = n`, namely `AddSubgroup.zmultiples n`.
* `Subgroup.existsUnique_index_eq_of_ne_zero` : the multiplicative transport of the above, via the
  order isomorphism `AddSubgroup.toSubgroup : AddSubgroup ℤ ≃o Subgroup (Multiplicative ℤ)`.
* `existsUnique_finiteIndexNormalSubgroup_index_eq` : the same statement packaged as
  `FiniteIndexNormalSubgroup (Multiplicative ℤ)` (normality is automatic, `Multiplicative ℤ` being
  abelian; finiteness of the index is exactly the hypothesis `n ≠ 0`, via `Subgroup.finiteIndex_iff`).

## Proof idea

Existence is `Int.index_zmultiples`. For uniqueness: any `H : AddSubgroup ℤ` is cyclic (`ℤ` being
cyclic, hence so are all its subgroups, `AddSubgroup.isAddCyclic`), so `H = zmultiples g` for some
`g`; if `H.index = n` then `g.natAbs = n` (`Int.index_zmultiples` again), so `g = ↑n` or `g = -↑n`
(`Int.natAbs_eq`), and either way `zmultiples g = zmultiples ↑n` (`AddSubgroup.zmultiples_neg` in
the second case).
-/

@[expose] public section

/-- **Classification of finite-index subgroups of `ℤ`**: for every `n ≠ 0`, there is a unique
`H : AddSubgroup ℤ` with `H.index = n`, namely `AddSubgroup.zmultiples (n : ℤ)`. -/
theorem AddSubgroup.existsUnique_index_eq_of_ne_zero {n : ℕ} (_hn : n ≠ 0) :
    ∃! H : AddSubgroup ℤ, H.index = n := by
  refine ⟨AddSubgroup.zmultiples (n : ℤ), ?_, fun H hH => ?_⟩
  · show (AddSubgroup.zmultiples (n : ℤ)).index = n
    rw [Int.index_zmultiples]
    simp
  · obtain ⟨g, hg⟩ :=
      (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp (AddSubgroup.isAddCyclic H)
    rw [← hg] at hH ⊢
    rw [Int.index_zmultiples] at hH
    rcases Int.natAbs_eq g with hg' | hg'
    · rw [hg', hH]
    · rw [hg', AddSubgroup.zmultiples_neg, hH]

/-- The multiplicative transport of `AddSubgroup.existsUnique_index_eq_of_ne_zero` along
`AddSubgroup.toSubgroup : AddSubgroup ℤ ≃o Subgroup (Multiplicative ℤ)`. -/
theorem Subgroup.existsUnique_index_eq_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∃! H : Subgroup (Multiplicative ℤ), H.index = n := by
  obtain ⟨A, hA, hAuniq⟩ := AddSubgroup.existsUnique_index_eq_of_ne_zero hn
  refine ⟨AddSubgroup.toSubgroup A, ?_, fun H hH => ?_⟩
  · show (AddSubgroup.toSubgroup A).index = n
    rw [AddSubgroup.index_toSubgroup]
    exact hA
  · have hEq : AddSubgroup.toSubgroup.symm H = A := by
      apply hAuniq
      show (AddSubgroup.toSubgroup (AddSubgroup.toSubgroup.symm H)).index = n
      rw [OrderIso.apply_symm_apply]
      exact hH
    rw [← hEq, OrderIso.apply_symm_apply]

/-- **Classification of finite-index normal subgroups of `Multiplicative ℤ`**, packaged as
`FiniteIndexNormalSubgroup` (the indexing category of the diagram defining `Zhat`): for every
`n ≠ 0`, there is a unique `H : FiniteIndexNormalSubgroup (Multiplicative ℤ)` with
`H.toSubgroup.index = n`. Normality is automatic (`Multiplicative ℤ` is abelian,
`Subgroup.normal_of_isMulCommutative`); finite-index-ness is exactly `n ≠ 0`
(`Subgroup.finiteIndex_iff`). -/
theorem existsUnique_finiteIndexNormalSubgroup_index_eq {n : ℕ} (hn : n ≠ 0) :
    ∃! H : FiniteIndexNormalSubgroup (Multiplicative ℤ), H.toSubgroup.index = n := by
  obtain ⟨A, hA, hAuniq⟩ := Subgroup.existsUnique_index_eq_of_ne_zero hn
  haveI : A.Normal := Subgroup.normal_of_isMulCommutative A
  haveI : A.FiniteIndex := Subgroup.finiteIndex_iff.mpr (hA ▸ hn)
  refine ⟨FiniteIndexNormalSubgroup.ofSubgroup A, hA, fun H hH => ?_⟩
  exact FiniteIndexNormalSubgroup.toSubgroup_injective (hAuniq H.toSubgroup hH)
