import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Finite-index subgroups of `ℤ`

For every `n ≠ 0` there is a unique subgroup of `ℤ` of index `n`, namely
`AddSubgroup.zmultiples (n : ℤ)`, and containment of two such subgroups is divisibility of their
indices in the opposite direction. The same statements are transported to `Multiplicative ℤ` along
`AddSubgroup.toSubgroup` and packaged for `FiniteIndexNormalSubgroup (Multiplicative ℤ)`, the
indexing category of the diagram whose limit is the profinite completion of `ℤ`.

This is the classification of the ideals of the principal ideal domain `ℤ`, read through
`AddSubgroup.toIntSubmodule : AddSubgroup ℤ ≃o Submodule ℤ ℤ`. The two Mathlib ingredients are
`AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top` — every subgroup of a cyclic group is of the
form `zmultiples g` — and `Int.index_zmultiples`, computing that index as `g.natAbs`.

## Main results

* `AddSubgroup.existsUnique_index_eq_of_ne_zero` : for `n ≠ 0` there is a unique
  `H : AddSubgroup ℤ` with `H.index = n`, namely `AddSubgroup.zmultiples (n : ℤ)`.
* `AddSubgroup.zmultiples_le_zmultiples_iff` : `zmultiples n ≤ zmultiples m ↔ m ∣ n`.
* `Subgroup.existsUnique_index_eq_of_ne_zero` : the multiplicative form, transported along the
  order isomorphism `AddSubgroup.toSubgroup : AddSubgroup ℤ ≃o Subgroup (Multiplicative ℤ)`.
* `Subgroup.eq_toSubgroup_zmultiples_index` : a finite-index subgroup of `Multiplicative ℤ` is the
  canonical subgroup of its own index.
* `existsUnique_finiteIndexNormalSubgroup_index_eq` : the same classification for
  `FiniteIndexNormalSubgroup (Multiplicative ℤ)`.
* `FiniteIndexNormalSubgroup.le_iff_dvd_index` : `H ≤ H' ↔ H'.toSubgroup.index ∣ H.toSubgroup.index`.
* `MonoidHom.range_powMonoidHom_multiplicativeInt` : the range of the `n`th-power map on
  `Multiplicative ℤ` is `AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ))`.
* `MonoidHom.index_range_powMonoidHom_multiplicativeInt` : its index is `n`.
-/

@[expose] public section

/-- **Classification of the finite-index subgroups of `ℤ`**: for every `n ≠ 0` there is a unique
`H : AddSubgroup ℤ` with `H.index = n`, namely `AddSubgroup.zmultiples (n : ℤ)`. Any `H` is of the
form `zmultiples g` with `g.natAbs = H.index`, and `zmultiples g = zmultiples (-g)`. -/
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

/-- **Classification of the finite-index subgroups of `Multiplicative ℤ`**: for every `n ≠ 0` there
is a unique subgroup of index `n`. Transport of `AddSubgroup.existsUnique_index_eq_of_ne_zero`
along `AddSubgroup.toSubgroup : AddSubgroup ℤ ≃o Subgroup (Multiplicative ℤ)`. -/
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

/-- **The subgroup lattice of `ℤ` is ordered by divisibility of indices**: `zmultiples n ≤
zmultiples m` iff `m ∣ n`. Equivalently, by `AddSubgroup.existsUnique_index_eq_of_ne_zero`, the
subgroup of index `n` is contained in the subgroup of index `m` exactly when `m ∣ n`. -/
theorem AddSubgroup.zmultiples_le_zmultiples_iff {m n : ℕ} :
    AddSubgroup.zmultiples (n : ℤ) ≤ AddSubgroup.zmultiples (m : ℤ) ↔ m ∣ n := by
  rw [AddSubgroup.zmultiples_le, AddSubgroup.mem_zmultiples_iff, ← Int.natCast_dvd_natCast]
  simp only [zsmul_eq_mul]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm.trans (mul_comm k (m : ℤ))⟩
  · rintro ⟨k, hk⟩; exact ⟨k, (mul_comm k (m : ℤ)).trans hk.symm⟩

/-- The index of `H : FiniteIndexNormalSubgroup (Multiplicative ℤ)` is nonzero. Stated as an
instance so that `NeZero`-requiring constructions applied to `H.toSubgroup.index` elaborate without
a local `haveI` at each use site. -/
instance FiniteIndexNormalSubgroup.instNeZeroIndex (H : FiniteIndexNormalSubgroup (Multiplicative ℤ)) :
    NeZero H.toSubgroup.index :=
  ⟨Subgroup.FiniteIndex.index_ne_zero⟩

/-- **Classification of the finite-index normal subgroups of `Multiplicative ℤ`**: for every
`n ≠ 0` there is a unique `H : FiniteIndexNormalSubgroup (Multiplicative ℤ)` with
`H.toSubgroup.index = n`. Normality is automatic, `Multiplicative ℤ` being abelian
(`Subgroup.normal_of_isMulCommutative`), and finiteness of the index is exactly `n ≠ 0`
(`Subgroup.finiteIndex_iff`). -/
theorem existsUnique_finiteIndexNormalSubgroup_index_eq {n : ℕ} (hn : n ≠ 0) :
    ∃! H : FiniteIndexNormalSubgroup (Multiplicative ℤ), H.toSubgroup.index = n := by
  obtain ⟨A, hA, hAuniq⟩ := Subgroup.existsUnique_index_eq_of_ne_zero hn
  haveI : A.Normal := Subgroup.normal_of_isMulCommutative A
  haveI : A.FiniteIndex := Subgroup.finiteIndex_iff.mpr (hA ▸ hn)
  refine ⟨FiniteIndexNormalSubgroup.ofSubgroup A, hA, fun H hH => ?_⟩
  exact FiniteIndexNormalSubgroup.toSubgroup_injective (hAuniq H.toSubgroup hH)

/-- A finite-index subgroup `H` of `Multiplicative ℤ` is the canonical subgroup of its own index,
that is, the image of `AddSubgroup.zmultiples (H.index : ℤ)` under `AddSubgroup.toSubgroup`. -/
theorem Subgroup.eq_toSubgroup_zmultiples_index {H : Subgroup (Multiplicative ℤ)} [H.FiniteIndex] :
    H = AddSubgroup.toSubgroup (AddSubgroup.zmultiples (H.index : ℤ)) := by
  have hn : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero (H := H)
  have hHA : (AddSubgroup.toSubgroup.symm H).index = H.index := by
    have := AddSubgroup.index_toSubgroup (AddSubgroup.toSubgroup.symm H)
    rwa [OrderIso.apply_symm_apply] at this
  have hZ : (AddSubgroup.zmultiples (H.index : ℤ)).index = H.index := by
    rw [Int.index_zmultiples]; simp
  have hEq : AddSubgroup.toSubgroup.symm H = AddSubgroup.zmultiples (H.index : ℤ) :=
    (AddSubgroup.existsUnique_index_eq_of_ne_zero hn).unique hHA hZ
  rw [← hEq, OrderIso.apply_symm_apply]

/-- **Divisibility from containment**: for finite-index normal subgroups `H ≤ H'` of
`Multiplicative ℤ`, the index of `H'` divides the index of `H`. Both are rewritten in their
`AddSubgroup.zmultiples` form by `Subgroup.eq_toSubgroup_zmultiples_index`, after which
`AddSubgroup.zmultiples_le_zmultiples_iff` applies. -/
theorem FiniteIndexNormalSubgroup.index_dvd_index_of_le
    {H H' : FiniteIndexNormalSubgroup (Multiplicative ℤ)} (h : H ≤ H') :
    H'.toSubgroup.index ∣ H.toSubgroup.index := by
  have hH : H.toSubgroup = AddSubgroup.toSubgroup (AddSubgroup.zmultiples (H.toSubgroup.index : ℤ)) :=
    Subgroup.eq_toSubgroup_zmultiples_index
  have hH' : H'.toSubgroup =
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples (H'.toSubgroup.index : ℤ)) :=
    Subgroup.eq_toSubgroup_zmultiples_index
  have hsub : H.toSubgroup ≤ H'.toSubgroup := h
  have hle : AddSubgroup.zmultiples (H.toSubgroup.index : ℤ) ≤
      AddSubgroup.zmultiples (H'.toSubgroup.index : ℤ) := by
    rw [hH, hH'] at hsub
    exact (AddSubgroup.toSubgroup.le_iff_le).mp hsub
  exact AddSubgroup.zmultiples_le_zmultiples_iff.mp hle

/-- **Containment from divisibility**, the converse of
`FiniteIndexNormalSubgroup.index_dvd_index_of_le`: if the index of `H'` divides the index of `H`,
then `H ≤ H'`. -/
theorem FiniteIndexNormalSubgroup.le_of_dvd_index
    {H H' : FiniteIndexNormalSubgroup (Multiplicative ℤ)}
    (h : H'.toSubgroup.index ∣ H.toSubgroup.index) : H ≤ H' := by
  have hH : H.toSubgroup = AddSubgroup.toSubgroup (AddSubgroup.zmultiples (H.toSubgroup.index : ℤ)) :=
    Subgroup.eq_toSubgroup_zmultiples_index
  have hH' : H'.toSubgroup =
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples (H'.toSubgroup.index : ℤ)) :=
    Subgroup.eq_toSubgroup_zmultiples_index
  have hle : AddSubgroup.zmultiples (H.toSubgroup.index : ℤ) ≤
      AddSubgroup.zmultiples (H'.toSubgroup.index : ℤ) :=
    AddSubgroup.zmultiples_le_zmultiples_iff.mpr h
  show H.toSubgroup ≤ H'.toSubgroup
  rw [hH, hH']
  exact (AddSubgroup.toSubgroup.le_iff_le).mpr hle

/-- **The lattice `FiniteIndexNormalSubgroup (Multiplicative ℤ)` is ordered by divisibility of
indices**: `H ≤ H' ↔ H'.toSubgroup.index ∣ H.toSubgroup.index`. -/
theorem FiniteIndexNormalSubgroup.le_iff_dvd_index
    {H H' : FiniteIndexNormalSubgroup (Multiplicative ℤ)} :
    H ≤ H' ↔ H'.toSubgroup.index ∣ H.toSubgroup.index :=
  ⟨FiniteIndexNormalSubgroup.index_dvd_index_of_le, FiniteIndexNormalSubgroup.le_of_dvd_index⟩

/-- **The range of the `n`th-power map on `Multiplicative ℤ` is `AddSubgroup.zmultiples n`,
transported.** `y = x ^ n` for some `x` iff `toAdd y` is a multiple of `n`
(`Int.toAdd_pow`/`Multiplicative.toAdd_ofAdd`, plus injectivity of `Multiplicative.toAdd`). Needed
to compute the index of the norm group's valuation-side image, `[K_vˣ : N(L_wˣ) ⊔ U_{K_v}] = f`,
in `Langlands.AdicCompletionNormGroupIndex`. -/
theorem MonoidHom.range_powMonoidHom_multiplicativeInt (n : ℕ) :
    MonoidHom.range (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ) =
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) := by
  ext y
  simp only [MonoidHom.mem_range, powMonoidHom_apply, Multiplicative.mem_toSubgroup,
    AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Multiplicative.toAdd x, (Int.toAdd_pow x n).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨Multiplicative.ofAdd k, Multiplicative.toAdd.injective ?_⟩
    rw [Int.toAdd_pow, toAdd_ofAdd, ← hk]
    norm_cast

/-- **The index of the range of the `n`th-power map on `Multiplicative ℤ` is `n`.** Immediate from
`MonoidHom.range_powMonoidHom_multiplicativeInt`, `AddSubgroup.index_toSubgroup`, and
`Int.index_zmultiples`. -/
theorem MonoidHom.index_range_powMonoidHom_multiplicativeInt (n : ℕ) :
    (MonoidHom.range (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ)).index = n := by
  rw [MonoidHom.range_powMonoidHom_multiplicativeInt, AddSubgroup.index_toSubgroup,
    Int.index_zmultiples]
  simp
