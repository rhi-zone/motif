import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The principal-units filtration `U_A^{(i)} := 1 + 𝔪_A^i`

Tame-case unit-norm surjectivity `N_{L/K}(U_L) ⊇ U_K` needs, as a prerequisite, the higher
principal-units filtration of the unit group of a valuation ring — the multiplicative analogue of
`Langlands.RamificationFiltration`'s additive ramification-group filtration. Mathlib has only the
level-1 group (`ValuationSubring.principalUnitGroup`, `{x : Kˣ | A.valuation (x - 1) < 1}`, with
`unitsModPrincipalUnitsEquivResidueFieldUnits : A.unitGroup ⧸ ... ≃* (ResidueField A)ˣ` already
proved) — no `1 + 𝔪_A^i` for `i ≥ 2` exists anywhere in Mathlib (checked by grep before writing
this file).

## Design choice: subgroups of `Aˣ`, not of `Kˣ`

Mathlib's `principalUnitGroup` lives in `Subgroup Kˣ` (the field's unit group), with membership
phrased via the valuation `A.valuation (x - 1) < 1` — a condition that only forces `x ∈ A.unitGroup`
for the *strict* `< 1` case; naively replacing `< 1` by `≤ γ^i` for `γ` the valuation of a fixed
uniformizer and `i ≥ 2` does **not** stay inside `A.unitGroup` (e.g. `x = π⁻¹·(1 + π)` type
counterexamples), so that generalization is wrong. Working instead at the level of `Aˣ` (the unit
group of the ring `A` itself, following the same choice `Langlands.RamificationFiltration` already
makes for its `ramificationGroup` filtration, which is stated over `A`-elements, not `L`-elements)
sidesteps this: every `x : Aˣ` already has `(x : A) - 1 ∈ A`, so ideal-power membership needs no
separate "is it in `A`" side condition, and the subgroup axioms are direct ideal-membership algebra
(no valuation ultrametric inequalities needed at all).

## Main definitions

* `ValuationSubring.principalUnitsPow A i : Subgroup Aˣ` : `{x : Aˣ | (x : A) - 1 ∈ 𝔪_A ^ i}`, for
  `i : ℕ` (with `i = 0` giving all of `Aˣ`, matching the classical convention `U^{(0)} = O_L^×`).

## Main results

* `principalUnitsPow_zero` : `principalUnitsPow A 0 = ⊤`.
* `principalUnitsPow_antitone` : the filtration is decreasing.
* `principalUnitsPow_one` : `principalUnitsPow A 1 = (Units.map (residue A).toMonoidHom).ker` —
  agreement with reduction mod `𝔪_A`, hence (via Mathlib's own
  `ValuationSubring.ker_unitGroupToResidueFieldUnits`, transporting along
  `A.unitGroupMulEquiv : A.unitGroup ≃* Aˣ`) with Mathlib's `principalUnitGroup` at the level-1
  case, without re-deriving that correspondence's proof content from scratch.
* `principalUnitsGradedHom` : for a uniformizer `π` of `A` (`hπ : 𝔪_A = span {π}`, `π ≠ 0`) and
  `i : ℕ`, the map `principalUnitsPow A (i + 1) →* Multiplicative (ResidueField A)`,
  `1 + π^{i+1}·c ↦ residue c` (well-defined since `A` is a domain, so `c` is the *unique* element
  with `(x : A) - 1 = π^{i+1} * c`). Multiplicativity is *exact* algebra with no error term: for
  `x, y` with coefficients `c_x, c_y`, `(xy : A) - 1 = π^{i+1}(c_x + c_y) + π^{2(i+1)} c_x c_y`, and
  `π^{2(i+1)} c_x c_y ∈ π^{i+1} · 𝔪_A ⊆ 𝔪_A · 𝔪_A ⊆ 𝔪_A` since `2(i+1) ≥ i + 2`, so it vanishes under
  `residue`. (No group action is involved here, unlike `Langlands.RamificationFiltration`'s
  `gradedSuccHom` — that file's `geomSum₂_mem_pow_maximalIdeal` two-variable factorization handled
  the twisted `σ(π)` vs. `π` discrepancy of a Galois action; here there is no such twist, so plain
  binomial expansion of `(1 + a)(1 + b) - 1` suffices and no geometric-sum lemma is needed.)
* `principalUnitsGradedHom_ker` : the kernel of `principalUnitsGradedHom` (restricted to
  `principalUnitsPow A (i+1)`) is exactly `principalUnitsPow A (i + 2)` (as a subgroup of
  `principalUnitsPow A (i+1)`, via `Subgroup.subgroupOf`).
* `principalUnitsGradedHom_surjective` : `principalUnitsGradedHom` is surjective (any residue class
  lifts to `A`, and `1 + π^{i+1} • (lift)` is a unit of `A` since `1 + 𝔪_A`-elements are always
  units in a local ring).
* `principalUnitsGradedEquiv` : the resulting isomorphism
  `principalUnitsPow A (i+1) ⧸ (principalUnitsPow A (i+2)).subgroupOf (principalUnitsPow A (i+1))
    ≃* Multiplicative (ResidueField A)`
  — **`U_A^{(i+1)} / U_A^{(i+2)} ≅ (ResidueField A, +)` for every `i : ℕ`**, i.e. the graded pieces
  of the filtration for index `≥ 1`. The `i = 0` half
  (`U_A^{(0)} / U_A^{(1)} ≅ (ResidueField A)ˣ`) is Mathlib's pre-existing
  `unitsModPrincipalUnitsEquivResidueFieldUnits`, reindexed via `principalUnitsPow_zero` /
  `principalUnitsPow_one` rather than reproved.
-/

noncomputable section

namespace ValuationSubring

variable {L : Type*} [Field L] (A : ValuationSubring L)

/-- The `i`-th principal-units subgroup of `Aˣ`: `1 + 𝔪_A^i`. `i = 0` gives all of `Aˣ` (`𝔪_A^0 =
⊤`), matching the classical convention `U^{(0)} = O_L^×`. -/
def principalUnitsPow (i : ℕ) : Subgroup Aˣ where
  carrier := {x : Aˣ | (x : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ i}
  mul_mem' {x y} hx hy := by
    have h2i : IsLocalRing.maximalIdeal A ^ (2 * i) ≤ IsLocalRing.maximalIdeal A ^ i :=
      Ideal.pow_le_pow_right (by omega)
    have key : ((x * y : Aˣ) : A) - 1
        = (((x : A) - 1) + ((y : A) - 1) + ((x : A) - 1) * ((y : A) - 1)) := by
      push_cast; ring
    show ((x * y : Aˣ) : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ i
    rw [key]
    refine Ideal.add_mem _ (Ideal.add_mem _ hx hy) (h2i ?_)
    rw [two_mul, pow_add]
    exact Ideal.mul_mem_mul hx hy
  one_mem' := by simp
  inv_mem' {x} hx := by
    show (↑x⁻¹ : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ i
    have hxx : (x : A) * ((x⁻¹ : Aˣ) : A) = 1 := by exact_mod_cast x.mul_inv
    have heq : ((x⁻¹ : Aˣ) : A) - 1 = -((x⁻¹ : Aˣ) : A) * ((x : A) - 1) := by
      linear_combination hxx
    rw [heq]
    exact Ideal.mul_mem_left _ _ hx

theorem mem_principalUnitsPow_iff {i : ℕ} {x : Aˣ} :
    x ∈ principalUnitsPow A i ↔ (x : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ i :=
  Iff.rfl

@[simp]
theorem principalUnitsPow_zero : principalUnitsPow A 0 = ⊤ := by
  ext x
  simp [mem_principalUnitsPow_iff]

theorem principalUnitsPow_antitone : Antitone (principalUnitsPow A) := by
  intro i j hij x hx
  exact Ideal.pow_le_pow_right hij hx

/-- `principalUnitsPow A 1` agrees with reduction mod `𝔪_A`: `x ≡ 1 mod 𝔪_A` is exactly `x ∈
ker (Units.map (residue A))`. Combined with Mathlib's own
`ValuationSubring.ker_unitGroupToResidueFieldUnits` (transporting along `A.unitGroupMulEquiv :
A.unitGroup ≃* Aˣ`), this identifies `principalUnitsPow A 1` with Mathlib's pre-existing
`principalUnitGroup` at the level-1 case, without re-deriving that correspondence from scratch. -/
theorem principalUnitsPow_one :
    principalUnitsPow A 1 = (Units.map (IsLocalRing.residue A).toMonoidHom).ker := by
  ext x
  rw [mem_principalUnitsPow_iff, pow_one, MonoidHom.mem_ker]
  constructor
  · intro h
    apply Units.ext
    rw [Units.coe_map, Units.val_one]
    have hz : IsLocalRing.residue A ((x : A) - 1) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr h
    rwa [map_sub, map_one, sub_eq_zero] at hz
  · intro h
    have hval : (Units.map (IsLocalRing.residue A).toMonoidHom x : IsLocalRing.ResidueField A) = 1 := by
      rw [h]; rfl
    rw [Units.coe_map] at hval
    show (x : A) - 1 ∈ IsLocalRing.maximalIdeal A
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
    exact hval

variable {π : A} (hπ : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : π ≠ 0)

include hπ hπ0

omit hπ0 in
/-- `𝔪_A ^ n = span {π ^ n}`, the ideal-power form of the uniformizer hypothesis. -/
theorem maximalIdeal_pow_eq_span_pow (n : ℕ) :
    IsLocalRing.maximalIdeal A ^ n = Ideal.span ({π ^ n} : Set A) := by
  rw [hπ, Ideal.span_singleton_pow]

/-- **The coefficient extraction**: for `x ∈ principalUnitsPow A (i+1)`, the unique `c : A` with
`(x : A) - 1 = π^{i+1} * c` (unique because `A`, a subring of the field `L`, is a domain and
`π ≠ 0`). -/
theorem exists_unique_principalUnitsCoeff {i : ℕ} (x : principalUnitsPow A (i + 1)) :
    ∃! c : A, ((x : Aˣ) : A) - 1 = π ^ (i + 1) * c := by
  have hmem : ((x : Aˣ) : A) - 1 ∈ Ideal.span ({π ^ (i + 1)} : Set A) := by
    rw [← maximalIdeal_pow_eq_span_pow A hπ (i + 1)]
    exact x.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hpow0 : π ^ (i + 1) ≠ 0 := pow_ne_zero _ hπ0
  refine ⟨c, by rw [← hc]; ring, fun c' hc' => ?_⟩
  apply mul_left_cancel₀ hpow0
  rw [← hc', ← hc]; ring

/-- The coefficient `c` of `exists_unique_principalUnitsCoeff`, chosen once and for all. -/
def principalUnitsCoeff {i : ℕ} (x : principalUnitsPow A (i + 1)) : A :=
  (exists_unique_principalUnitsCoeff A hπ hπ0 x).choose

theorem principalUnitsCoeff_spec {i : ℕ} (x : principalUnitsPow A (i + 1)) :
    ((x : Aˣ) : A) - 1 = π ^ (i + 1) * principalUnitsCoeff A hπ hπ0 x :=
  (exists_unique_principalUnitsCoeff A hπ hπ0 x).choose_spec.1

theorem principalUnitsCoeff_unique {i : ℕ} (x : principalUnitsPow A (i + 1)) (c : A)
    (hc : ((x : Aˣ) : A) - 1 = π ^ (i + 1) * c) : c = principalUnitsCoeff A hπ hπ0 x :=
  (exists_unique_principalUnitsCoeff A hπ hπ0 x).choose_spec.2 c hc

/-- **The graded coefficient is additive under `residue`, exactly (`i ≥ 0`, no error term).** -/
theorem residue_principalUnitsCoeff_mul {i : ℕ} (x y : principalUnitsPow A (i + 1)) :
    IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 (x * y))
      = IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 x)
        + IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 y) := by
  set cx := principalUnitsCoeff A hπ hπ0 x
  set cy := principalUnitsCoeff A hπ hπ0 y
  have hxy : (((x * y : principalUnitsPow A (i + 1)) : Aˣ) : A) - 1
      = π ^ (i + 1) * (cx + cy + π ^ (i + 1) * (cx * cy)) := by
    have hx := principalUnitsCoeff_spec A hπ hπ0 x
    have hy := principalUnitsCoeff_spec A hπ hπ0 y
    have hval : (((x * y : principalUnitsPow A (i + 1)) : Aˣ) : A)
        = ((x : Aˣ) : A) * ((y : Aˣ) : A) := by
      rw [Subgroup.coe_mul, Units.val_mul]
    rw [hval]
    have hX : ((x : Aˣ) : A) = 1 + π ^ (i + 1) * cx := by linear_combination hx
    have hY : ((y : Aˣ) : A) = 1 + π ^ (i + 1) * cy := by linear_combination hy
    rw [hX, hY]; ring
  have hcxy : cx + cy + π ^ (i + 1) * (cx * cy) = principalUnitsCoeff A hπ hπ0 (x * y) :=
    principalUnitsCoeff_unique A hπ hπ0 (x * y) _ hxy
  rw [← hcxy, map_add, map_add]
  have hπmem : π ∈ IsLocalRing.maximalIdeal A := hπ ▸ Ideal.mem_span_singleton_self π
  have hppow : π ^ (i + 1) ∈ IsLocalRing.maximalIdeal A := by
    have h1 : π ^ (i + 1) ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := Ideal.pow_mem_pow hπmem (i + 1)
    have h2 : IsLocalRing.maximalIdeal A ^ (i + 1) ≤ IsLocalRing.maximalIdeal A ^ 1 :=
      Ideal.pow_le_pow_right (Nat.le_add_left 1 i)
    rw [pow_one] at h2
    exact h2 h1
  have hzero : IsLocalRing.residue A (π ^ (i + 1) * (cx * cy)) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact Ideal.mul_mem_right _ _ hppow
  rw [hzero, add_zero]

/-- **The `i ≥ 1` associated-graded map, as a `MonoidHom`.** `x ↦ residue (principalUnitsCoeff x)`,
valued additively (`Multiplicative (ResidueField A)`), defined on `principalUnitsPow A (i + 1)`. -/
def principalUnitsGradedHom (i : ℕ) :
    principalUnitsPow A (i + 1) →* Multiplicative (IsLocalRing.ResidueField A) where
  toFun x := Multiplicative.ofAdd (IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 x))
  map_one' := by
    have h0 : (0 : A) = principalUnitsCoeff A hπ hπ0 (1 : principalUnitsPow A (i + 1)) :=
      principalUnitsCoeff_unique A hπ hπ0 (1 : principalUnitsPow A (i + 1)) 0 (by simp)
    show Multiplicative.ofAdd
        (IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 (1 : principalUnitsPow A (i + 1))))
      = 1
    rw [← h0, map_zero]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 (x * y)))
      = Multiplicative.ofAdd (IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 x))
        * Multiplicative.ofAdd (IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 y))
    rw [residue_principalUnitsCoeff_mul A hπ hπ0 x y]
    rfl

theorem principalUnitsGradedHom_apply {i : ℕ} (x : principalUnitsPow A (i + 1)) :
    principalUnitsGradedHom A hπ hπ0 i x
      = Multiplicative.ofAdd (IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 x)) :=
  rfl

omit hπ in
/-- Cancellation form of the span-membership underlying the kernel computation: `π^{i+1} · c ∈
span {π^{i+1} · π} ↔ c ∈ span {π}`, using that `A` is a domain and `π^{i+1} ≠ 0`. -/
theorem mul_pow_mem_span_mul_iff {i : ℕ} {c : A} :
    π ^ (i + 1) * c ∈ Ideal.span ({π ^ (i + 1) * π} : Set A) ↔ c ∈ Ideal.span ({π} : Set A) := by
  have hpow0 : π ^ (i + 1) ≠ 0 := pow_ne_zero _ hπ0
  rw [Ideal.mem_span_singleton', Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, mul_left_cancel₀ hpow0 ?_⟩
    linear_combination ha
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha]; ring⟩

/-- **The kernel of `principalUnitsGradedHom`, as a point condition.** `x ↦ 1` unwinds to `(x:A) - 1
∈ 𝔪_A^{i+2}` — the next level of the filtration. -/
theorem principalUnitsGradedHom_apply_eq_one_iff {i : ℕ} (x : principalUnitsPow A (i + 1)) :
    principalUnitsGradedHom A hπ hπ0 i x = 1 ↔
      ((x : Aˣ) : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ (i + 2) := by
  have hspec := principalUnitsCoeff_spec A hπ hπ0 x
  have hspan2 : IsLocalRing.maximalIdeal A ^ (i + 2)
      = Ideal.span ({π ^ (i + 1) * π} : Set A) := by
    rw [maximalIdeal_pow_eq_span_pow A hπ (i + 2)]
    congr 1
    rw [← pow_succ]
  rw [hspec, hspan2, mul_pow_mem_span_mul_iff A hπ0, ← hπ]
  constructor
  · intro h
    rw [principalUnitsGradedHom_apply] at h
    have h1 : IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 x) = 0 := by
      have h2 := congrArg Multiplicative.toAdd h
      simpa using h2
    exact (IsLocalRing.residue_eq_zero_iff _).mp h1
  · intro h
    rw [principalUnitsGradedHom_apply, (IsLocalRing.residue_eq_zero_iff _).mpr h]
    rfl

/-- **`principalUnitsGradedHom` is surjective**: every residue class lifts to a `1 + 𝔪_A^{i+1}`
class, since `1 + 𝔪_A`-elements are always units of a local ring (`isUnit_one_sub_self_of_mem_nonunits`
applied to `-(π^{i+1} • z)`). -/
theorem principalUnitsGradedHom_surjective {i : ℕ} :
    Function.Surjective (principalUnitsGradedHom A hπ hπ0 i) := by
  intro r
  obtain ⟨z, hz⟩ := IsLocalRing.residue_surjective (R := A) (Multiplicative.toAdd r)
  have hmem : π ^ (i + 1) * z ∈ IsLocalRing.maximalIdeal A := by
    have hπmem : π ∈ IsLocalRing.maximalIdeal A := hπ ▸ Ideal.mem_span_singleton_self π
    have hppow : π ^ (i + 1) ∈ IsLocalRing.maximalIdeal A := by
      have h1 : π ^ (i + 1) ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := Ideal.pow_mem_pow hπmem (i + 1)
      have h2 : IsLocalRing.maximalIdeal A ^ (i + 1) ≤ IsLocalRing.maximalIdeal A ^ 1 :=
        Ideal.pow_le_pow_right (Nat.le_add_left 1 i)
      rw [pow_one] at h2
      exact h2 h1
    exact Ideal.mul_mem_right _ _ hppow
  have hunit : IsUnit (1 + π ^ (i + 1) * z) := by
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(π ^ (i + 1) * z))
      ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.maximalIdeal A).neg_mem hmem))
    simpa using this
  refine ⟨⟨hunit.unit, ?_⟩, ?_⟩
  · show (hunit.unit : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ (i + 1)
    have hval : (hunit.unit : A) = 1 + π ^ (i + 1) * z := hunit.unit_spec
    rw [hval, add_sub_cancel_left]
    rw [maximalIdeal_pow_eq_span_pow A hπ (i + 1)]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · have hcoeff : z = principalUnitsCoeff A hπ hπ0
        (⟨hunit.unit, by
          show (hunit.unit : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ (i + 1)
          have hval : (hunit.unit : A) = 1 + π ^ (i + 1) * z := hunit.unit_spec
          rw [hval, add_sub_cancel_left, maximalIdeal_pow_eq_span_pow A hπ (i + 1)]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)⟩ :
          principalUnitsPow A (i + 1)) := by
      apply principalUnitsCoeff_unique
      show (hunit.unit : A) - 1 = π ^ (i + 1) * z
      rw [hunit.unit_spec, add_sub_cancel_left]
    show Multiplicative.ofAdd (IsLocalRing.residue A (principalUnitsCoeff A hπ hπ0 _)) = r
    rw [← hcoeff, hz]
    rfl

/-- **The `i ≥ 1` associated-graded isomorphism**: `U_A^{(i+1)} / U_A^{(i+2)} ≅ (ResidueField A, +)`.
Assembled from `principalUnitsGradedHom` (surjective, `principalUnitsGradedHom_surjective`) and its
kernel (`principalUnitsGradedHom_apply_eq_one_iff`, identifying `ker` with the subgroup
`principalUnitsPow A (i + 2)` of `principalUnitsPow A (i + 1)`) via
`QuotientGroup.quotientKerEquivOfSurjective`. -/
noncomputable def principalUnitsGradedEquiv (i : ℕ) :
    principalUnitsPow A (i + 1) ⧸ (principalUnitsGradedHom A hπ hπ0 i).ker ≃*
      Multiplicative (IsLocalRing.ResidueField A) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (principalUnitsGradedHom_surjective A hπ hπ0)

theorem principalUnitsGradedHom_ker_eq (i : ℕ) :
    (principalUnitsGradedHom A hπ hπ0 i).ker
      = (principalUnitsPow A (i + 2)).subgroupOf (principalUnitsPow A (i + 1)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_principalUnitsPow_iff]
  exact principalUnitsGradedHom_apply_eq_one_iff A hπ hπ0 x

end ValuationSubring
