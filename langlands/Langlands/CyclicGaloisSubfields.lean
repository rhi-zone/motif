import Langlands.CyclicSubgroups
import Mathlib.FieldTheory.Galois.Basic

/-!
# Intermediate fields of a cyclic Galois extension

For a finite Galois extension `E/F` with cyclic Galois group and every divisor `e` of `[E : F]`,
there is a unique intermediate field of degree `e` over `F`. This is the classification of the
subgroups of a finite cyclic group, `IsCyclic.existsUnique_subgroup_card_eq`
(`Langlands.CyclicSubgroups`), transported along the Galois correspondence
`IsGalois.intermediateFieldEquivSubgroup`.

Specialized to `F := GF(q)` and `E := GF(q^n)`, whose Galois group is cyclic of order `n` generated
by Frobenius, it gives existence and uniqueness of the degree-`d` subfield of `GF(q^n)` for every
`d ∣ n` (Lidl and Niederreiter, *Finite Fields*, Theorem 2.6).

Also proved here: every intermediate field of a finite Galois extension with abelian Galois group
is normal over the base, and the degree of an intermediate field is unchanged when the ambient
field is shrunk to any intermediate field containing it.

## Main results

* `IsGalois.existsUnique_intermediateField_finrank_eq` : for `E/F` finite Galois with
  `IsCyclic Gal(E/F)` and `e ∣ Module.finrank F E`, there is a unique `M : IntermediateField F E`
  with `Module.finrank F M = e`.
* `IsGalois.normal_of_isMulCommutative` : every intermediate field of a finite Galois extension
  with abelian Galois group is normal over the base.
* `normal_fixedField_of_isMulCommutative` : the fixed field of any subgroup of an abelian Galois
  group is normal over the base.
* `IntermediateField.finrank_comap_val_of_le` : for `M ≤ E'` in `IntermediateField F E`, pulling
  `M` back along the inclusion `E' →ₐ[F] E` preserves its degree over `F`. This is what allows two
  intermediate fields `M₁, M₂ ≤ E`, not themselves assumed finite or Galois over `F`, to be
  compared inside a finite Galois extension containing both, such as `M₁ ⊔ M₂`.
-/

@[expose] public section

/-- **Restricting an intermediate field to a smaller ambient intermediate field preserves its
degree.** For `M ≤ E'` in `IntermediateField F E`, the pullback `IntermediateField.comap E'.val M`
is `M` regarded as an intermediate field of `E'` rather than of `E`. It is `F`-algebra isomorphic
to `M` by `IntermediateField.equivMap`, since `IntermediateField.map_comap_eq_self` identifies
`(comap E'.val M).map E'.val` with `M`, and hence has the same `F`-degree. -/
theorem IntermediateField.finrank_comap_val_of_le {F E : Type*} [Field F] [Field E] [Algebra F E]
    {E' M : IntermediateField F E} (h : M ≤ E') :
    Module.finrank F (IntermediateField.comap E'.val M) = Module.finrank F M := by
  have hM : M ≤ E'.val.fieldRange := by rw [IntermediateField.fieldRange_val]; exact h
  have hmap : IntermediateField.map E'.val (IntermediateField.comap E'.val M) = M :=
    IntermediateField.map_comap_eq_self hM
  have hequiv := (IntermediateField.comap E'.val M).equivMap E'.val
  rw [hmap] at hequiv
  exact LinearEquiv.finrank_eq hequiv.toLinearEquiv

/-- Every subgroup of an abelian Galois group is normal: `Subgroup.normal_of_isMulCommutative`
in instance form for `Gal(E/F)`. -/
instance Subgroup.normal_of_isMulCommutative_aut {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsMulCommutative Gal(E/F)] (H : Subgroup Gal(E/F)) : H.Normal :=
  Subgroup.normal_of_isMulCommutative H

/-- **The fixed field of any subgroup of an abelian Galois group is normal over the base.** Every
`σ : Gal(E/F)` commutes with every `h ∈ H`, so for `x` fixed by `H` one has `h (σ x) = σ (h x) =
σ x`; thus `σ` maps `fixedField H` into itself, and
`IntermediateField.normal_iff_forall_map_le'` applies. -/
theorem normal_fixedField_of_isMulCommutative {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Normal F E] [IsMulCommutative Gal(E/F)] (H : Subgroup Gal(E/F)) :
    Normal F (IntermediateField.fixedField H) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro σ x hx
  rw [IntermediateField.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [IntermediateField.mem_fixedField_iff] at hy ⊢
  intro h hh
  have hcomm : h * σ = σ * h := IsMulCommutative.is_comm.comm h σ
  show h (σ y) = σ y
  have : (h * σ) y = (σ * h) y := by rw [hcomm]
  simpa [hy h hh] using this

namespace IsGalois

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- **Every intermediate field of a finite Galois extension with abelian Galois group is normal
over the base.** Such an `M` is the fixed field of its own fixing subgroup
(`IsGalois.fixedField_fixingSubgroup`), which is normal by
`normal_fixedField_of_isMulCommutative`. -/
theorem normal_of_isMulCommutative [IsMulCommutative Gal(E/F)] (M : IntermediateField F E) :
    Normal F M := by
  rw [← IsGalois.fixedField_fixingSubgroup M]
  exact normal_fixedField_of_isMulCommutative M.fixingSubgroup

/-- **Unique intermediate field of each degree dividing `[E : F]`**, for `E/F` finite Galois with
cyclic Galois group: for every `e ∣ Module.finrank F E` there is a unique intermediate field `M`
with `Module.finrank F M = e`.

Write `n := [E : F]` and `d := n / e`. The unique subgroup `H ≤ Gal(E/F)` of order `d` given by
`IsCyclic.existsUnique_subgroup_card_eq` has `fixedField H` as witness: its fixing subgroup is `H`
again (`IntermediateField.fixingSubgroup_fixedField`), so `[E : fixedField H] = d` by
`IsGalois.card_fixingSubgroup_eq_finrank`, and the tower law gives
`Module.finrank F (fixedField H) = e`. Uniqueness is the same computation read backwards, converted
from subgroups to fields by `IsGalois.fixedField_eq_iff_fixingSubgroup_eq`. -/
theorem existsUnique_intermediateField_finrank_eq [IsCyclic Gal(E/F)] {e : ℕ}
    (he : e ∣ Module.finrank F E) :
    ∃! M : IntermediateField F E, Module.finrank F M = e := by
  set n := Module.finrank F E with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hn0 (Nat.zero_dvd.mp he)
  have he_pos : 0 < e := Nat.pos_of_ne_zero he0
  have hnd : e * (n / e) = n := Nat.mul_div_cancel' he
  have hd : n / e ∣ n := Nat.div_dvd_of_dvd he
  have hcardG : Nat.card Gal(E/F) = n := IsGalois.card_aut_eq_finrank F E
  have hdG : n / e ∣ Nat.card Gal(E/F) := hcardG ▸ hd
  -- `IsCyclic.existsUnique_subgroup_card_eq` requires `[CommGroup Gal(E/F)]`, supplied here by
  -- `IsCyclic.commGroup`. Its instance arguments are passed explicitly: introducing the derived
  -- `CommGroup` with `haveI` creates a diamond between the ambient `Group Gal(E/F)` instance and
  -- `IsCyclic.commGroup.toGroup`, against which instance search no longer finds the ambient
  -- `[IsCyclic Gal(E/F)]` hypothesis, the two being defeq but not up to instance search.
  obtain ⟨H, hHcard, hHuniq⟩ :=
    @IsCyclic.existsUnique_subgroup_card_eq Gal(E/F) IsCyclic.commGroup ‹IsCyclic Gal(E/F)›
      inferInstance (n / e) hdG
  have hde_pos : 0 < n / e := by
    rcases Nat.eq_zero_or_pos (n / e) with h0 | hpos
    · rw [h0, mul_zero] at hnd; exact absurd hnd.symm hn0
    · exact hpos
  refine ⟨IntermediateField.fixedField H, ?_, fun M' hM' => ?_⟩
  · have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
      IntermediateField.fixingSubgroup_fixedField H
    have hcardM : Module.finrank (IntermediateField.fixedField H) E = n / e := by
      have h := IsGalois.card_fixingSubgroup_eq_finrank (IntermediateField.fixedField H)
      rw [hfix, hHcard] at h
      exact h.symm
    have htower : Module.finrank F (IntermediateField.fixedField H) * (n / e) = n := by
      have h := Module.finrank_mul_finrank F (IntermediateField.fixedField H) E
      rwa [hcardM] at h
    have heq : Module.finrank F (IntermediateField.fixedField H) * (n / e) = e * (n / e) := by
      rw [htower, hnd]
    exact Nat.eq_of_mul_eq_mul_right hde_pos heq
  · have hcardM' : Module.finrank M' E = n / e := by
      have htower' := Module.finrank_mul_finrank F M' E
      rw [hM'] at htower'
      exact Nat.eq_of_mul_eq_mul_left he_pos (htower'.trans hnd.symm)
    have hHM' : Nat.card M'.fixingSubgroup = n / e := by
      rw [IsGalois.card_fixingSubgroup_eq_finrank M', hcardM']
    have hEq : M'.fixingSubgroup = H := hHuniq M'.fixingSubgroup hHM'
    exact (IsGalois.fixedField_eq_iff_fixingSubgroup_eq.mpr hEq).symm

end IsGalois
