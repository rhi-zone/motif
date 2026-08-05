import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Higher ramification groups in lower numbering

This file extends `Mathlib.RingTheory.Valuation.RamificationGroup` with the higher ramification
groups in lower numbering, closing that file's own stated `TODO`.

For `K L : Type*` fields, `[Algebra K L]`, and `A : ValuationSubring L`, `Mathlib` already
supplies:

* `A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)`, the stabilizer of `A`;
* the `MulSemiringAction (A.decompositionSubgroup K) A` induced on `A` itself;
* `A.inertiaSubgroup K : Subgroup (A.decompositionSubgroup K)`, the kernel of the action on the
  residue field of `A`.

## Indexing convention

Serre (*Local Fields*, Ch. IV) numbers the ramification filtration `G_{-1} ⊇ G_0 ⊇ G_1 ⊇ ⋯` with
`G_{-1} = D` (the decomposition group) and `G_0 = I` (the inertia group). Since `D` and `I` already
exist here as `A.decompositionSubgroup K` and `A.inertiaSubgroup K` and don't need to be redefined,
`ramificationGroup K A i` below is index-shifted by one relative to Serre: it defines Serre's `G_i`
for `i : ℕ` starting at `i = 0`, i.e. `ramificationGroup K A i` *is* Serre's `G_i`, and there is no
`ramificationGroup K A (-1)` — that role is played by `A.decompositionSubgroup K` itself (`⊤` as a
subgroup of itself), not by a new definition. So the correspondence is:

* Serre's `G_{-1} = D` ↦ `A.decompositionSubgroup K` (no new object).
* Serre's `G_0 = I` ↦ `A.inertiaSubgroup K`, proved equal to `ramificationGroup K A 0` below
  (`ValuationSubring.ramificationGroup_zero`).
* Serre's `G_i` for `i ≥ 1` ↦ `ramificationGroup K A i`.

## Main definitions

* `ValuationSubring.ramificationGroup` : the `i`-th ramification group in lower numbering,
  `σ ∈ ramificationGroup K A i ↔ ∀ x : A, σ • x - x ∈ 𝔪_A ^ (i + 1)`.

## Main results

* `ValuationSubring.ramificationGroup_succ_le` : the filtration is decreasing,
  `ramificationGroup K A (i + 1) ≤ ramificationGroup K A i`.
* `ValuationSubring.ramificationGroup_zero` : `ramificationGroup K A 0 = A.inertiaSubgroup K`,
  matching Serre's `G_0 = I`.
* `ValuationSubring.ramificationGroup_normal` : `ramificationGroup K A i` is a normal subgroup of
  the *full* decomposition group `A.decompositionSubgroup K`, not merely of the inertia subgroup.

## Scope

The classical "eventually trivial" fact (the filtration hits `⊥` past some `N`, under a finiteness
hypothesis such as finiteness of the residue field) is not attempted here: its standard proof needs
the associated-graded injections `G_i / G_{i+1} ↪ 𝔪_A^i / 𝔪_A^{i+1}` (or the multiplicative variant
for `i = 0`), which is more machinery than this session builds. See `ROADMAP.md`, Phase 2b, for
the tracked gap.
-/

@[expose] public section

noncomputable section

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

section MaximalIdealInvariance

variable {A : ValuationSubring L}

/-- Each `σ` in the decomposition subgroup fixes the maximal ideal of `A` setwise: `σ` acts on `A`
as a ring automorphism (`MulSemiringAction.toRingEquiv`), and ring automorphisms of a local ring
fix its unique maximal ideal setwise (`IsLocalRing.maximalIdeal_comap`, applied to the surjective,
hence local, ring hom underlying the automorphism). -/
theorem mem_maximalIdeal_smul_iff (σ : A.decompositionSubgroup K) (x : A) :
    σ • x ∈ IsLocalRing.maximalIdeal A ↔ x ∈ IsLocalRing.maximalIdeal A := by
  set e : A →+* A := (MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A σ : A →+* A)
    with hedef
  haveI : IsLocalHom e :=
    IsLocalHom.of_surjective e (MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A σ).surjective
  have hcomap : (IsLocalRing.maximalIdeal A).comap e = IsLocalRing.maximalIdeal A :=
    IsLocalRing.maximalIdeal_comap e
  have hex : e x = σ • x := MulSemiringAction.toRingEquiv_apply_apply _ _ σ x
  rw [← hex, ← Ideal.mem_comap, hcomap]

/-- Each `σ` in the decomposition subgroup fixes every power of the maximal ideal of `A` setwise
(one direction, which is all that's needed to build the ramification-group subgroup structure):
if `x ∈ 𝔪_A ^ n` then `σ • x ∈ 𝔪_A ^ n`. This upgrades `mem_maximalIdeal_smul_iff` from `𝔪_A` to
`𝔪_A ^ n` via `Ideal.map_pow` applied to the ring-automorphism view of `σ`. -/
theorem smul_mem_pow_maximalIdeal (σ : A.decompositionSubgroup K) (n : ℕ) {x : A}
    (hx : x ∈ IsLocalRing.maximalIdeal A ^ n) :
    σ • x ∈ IsLocalRing.maximalIdeal A ^ n := by
  set e := MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A σ with hedef
  have hmap : (IsLocalRing.maximalIdeal A ^ n).map e = IsLocalRing.maximalIdeal A ^ n := by
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
  have hmem : e x ∈ (IsLocalRing.maximalIdeal A ^ n).map e := Ideal.mem_map_of_mem e hx
  rw [hmap] at hmem
  have hex : e x = σ • x := MulSemiringAction.toRingEquiv_apply_apply _ _ σ x
  rwa [hex] at hmem

end MaximalIdealInvariance

/-! ### The ramification filtration -/

/-- The `i`-th ramification group in lower numbering: `σ` fixes every element of `A` modulo
`𝔪_A ^ (i + 1)`. This is Serre's `G_i` for `i : ℕ` — see the module docstring for the indexing
convention (there is no separate `i = -1` case; that role is played by `A.decompositionSubgroup K`
itself). -/
def ramificationGroup (A : ValuationSubring L) (i : ℕ) : Subgroup (A.decompositionSubgroup K) where
  carrier := {σ | ∀ x : A, σ • x - x ∈ IsLocalRing.maximalIdeal A ^ (i + 1)}
  one_mem' x := by simp
  mul_mem' {σ τ} hσ hτ x := by
    have hτx : τ • x - x ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := hτ x
    have hσmap : σ • (τ • x - x) ∈ IsLocalRing.maximalIdeal A ^ (i + 1) :=
      smul_mem_pow_maximalIdeal K σ (i + 1) hτx
    have hσx : σ • x - x ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := hσ x
    have hsplit : (σ * τ) • x - x = σ • (τ • x - x) + (σ • x - x) := by
      rw [mul_smul, smul_sub]; ring
    rw [hsplit]
    exact Ideal.add_mem _ hσmap hσx
  inv_mem' {σ} hσ x := by
    have h := hσ (σ⁻¹ • x)
    rw [smul_smul, mul_inv_cancel, one_smul] at h
    have hneg := Submodule.neg_mem _ h
    rwa [neg_sub] at hneg

variable {K}

/-- The ramification filtration is decreasing: `G_{i+1} ≤ G_i`, since `𝔪_A ^ (i + 2) ≤ 𝔪_A ^ (i + 1)`
(ideal powers are decreasing). -/
theorem ramificationGroup_succ_le (A : ValuationSubring L) (i : ℕ) :
    ramificationGroup K A (i + 1) ≤ ramificationGroup K A i := by
  intro σ hσ x
  exact Ideal.pow_le_pow_right (Nat.le_succ _) (hσ x)

/-- `ramificationGroup K A 0` is Serre's `G_0`, the inertia group: `σ` fixes `A` modulo `𝔪_A`
(the `i = 0` case, `𝔪_A ^ 1 = 𝔪_A`) exactly when `σ` acts trivially on the residue field
`A ⧸ 𝔪_A`, which is the defining condition of `A.inertiaSubgroup K`. -/
theorem ramificationGroup_zero (A : ValuationSubring L) :
    ramificationGroup K A 0 = A.inertiaSubgroup K := by
  ext σ
  simp only [ramificationGroup, inertiaSubgroup, Subgroup.mem_mk, zero_add,
    pow_one, MonoidHom.mem_ker]
  have hstep : ∀ y : IsLocalRing.ResidueField A,
      (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) σ) y
        = σ • y := by
    intro y
    change (MulSemiringAction.toRingEquiv (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) σ) y = σ • y
    exact MulSemiringAction.toRingEquiv_apply_apply _ _ σ y
  constructor
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := A) y
    rw [hstep, RingAut.one_apply,
      ← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact h x
  · intro h x
    have hy := RingEquiv.congr_fun h (IsLocalRing.residue A x)
    rw [hstep, RingAut.one_apply,
      ← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff] at hy
    exact hy

/-- Each `ramificationGroup K A i` is normal not merely in the inertia subgroup but in the *full*
decomposition group: for `τ` in `A.decompositionSubgroup K` and `σ ∈ ramificationGroup K A i`,
`τστ⁻¹ • x - x = τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x)`, which lies in `𝔪_A ^ (i + 1)` by
`smul_mem_pow_maximalIdeal` applied to `σ`'s defining property at the point `τ⁻¹ • x` — no
membership hypothesis on `τ` itself is needed. -/
theorem ramificationGroup_normal (A : ValuationSubring L) (i : ℕ) :
    (ramificationGroup K A i).Normal where
  conj_mem σ hσ τ x := by
    have hσy : σ • (τ⁻¹ • x) - τ⁻¹ • x ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := hσ (τ⁻¹ • x)
    have hτmap : τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ IsLocalRing.maximalIdeal A ^ (i + 1) :=
      smul_mem_pow_maximalIdeal K τ (i + 1) hσy
    have hsplit : (τ * σ * τ⁻¹) • x - x = τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) := by
      simp [mul_smul, smul_sub, smul_inv_smul]
    rwa [hsplit]

end ValuationSubring
