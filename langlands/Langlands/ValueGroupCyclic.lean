/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Langlands.HenselianValuation

/-!
# Discreteness of a valuation on a finite extension

For `L / K` a finite extension of fields and `A : ValuationSubring L` restricting to a *discrete*
valuation subring `𝒪` of `K` (`A.comap (algebraMap K L) = 𝒪` with `IsDiscreteValuationRing 𝒪`),
this file proves that `A` is itself a discrete valuation ring.

## Main results

* `ValuationSubring.isCyclic_valueGroup_units_of_comap_eq` : the unit group of `A.ValueGroup` is
  cyclic.
* `ValuationSubring.isDiscreteValuationRing_of_comap_eq` : `A` is a discrete valuation ring.

## Implementation notes

The classical argument is that `Γ_L := L^× / A^×` contains `Γ_K := K^× / 𝒪^× ≃ ℤ` with index
dividing the ramification index, so `Γ_L` sits inside the divisible hull of a cyclic group with
bounded denominators and is therefore cyclic. Rather than constructing the divisible hull, the
proof here is purely group-theoretic and avoids the order structure of `Γ_L` entirely:

* `Langlands.HenselianValuation`'s `Valuation.exists_pow_eq_of_isAlgebraic` gives, for each
  `x : L`, an exponent `1 ≤ m ≤ (minpoly K x).natDegree` with `A.valuation x ^ m` equal to the
  value of an element of `K`.
* Every value of an element of `K` is an integer power of `γ := A.valuation (algebraMap K L ϖ)`
  for `ϖ` a uniformizer of `𝒪`, since `𝒪` is a discrete valuation ring and units of `𝒪` have
  value `1` (`hunitVal` below).
* `(minpoly K x).natDegree ≤ [L : K] =: d` (`minpoly.natDegree_le`), so `m ∣ d !` uniformly in
  `x`; hence `u ^ d !` lies in `Subgroup.zpowers γ` for **every** `u : (A.ValueGroup)ˣ`
  (`A.valuation` is surjective).
* `A.ValueGroup` is a `LinearOrderedCommGroupWithZero`, hence `IsMulTorsionFree`, so
  `u ↦ u ^ d !` is injective; an injective homomorphism into a cyclic group has cyclic domain
  (`isCyclic_of_injective`).

`Valuation.valuationSubring_isDiscreteValuationRing` (Serre, *Local Fields* I §1 Prop. 1) then
converts cyclicity plus nontriviality of the value group into `IsDiscreteValuationRing`.

Note that no completeness, henselianity or separability hypothesis is needed: the statement holds
for an arbitrary valuation subring of a finite extension lying over a discrete one. Existence and
uniqueness of such an `A` are separate questions, handled elsewhere
(`Langlands.WeilGroup.LocalField.valuationSubringExtension`,
`Langlands.HenselianValuation.LocalField.valuationSubring_eq_of_comap_eq`).
-/

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The unit group of the value group of a valuation subring `A` of a finite extension `L / K`
lying over a discrete valuation subring `𝒪` of `K` is cyclic. -/
theorem isCyclic_valueGroup_units_of_comap_eq [FiniteDimensional K L]
    {𝒪 : ValuationSubring K} [IsDiscreteValuationRing 𝒪]
    (A : ValuationSubring L) (hA : A.comap (algebraMap K L) = 𝒪) :
    IsCyclic (A.ValueGroup)ˣ := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪)
  set v := A.valuation with hvdef
  -- Membership transfer along `hA`.
  have hmem : ∀ c : K, c ∈ 𝒪 → algebraMap K L c ∈ A := by
    intro c hc
    rw [← hA] at hc
    exact hc
  -- Elements of `K` invertible in `𝒪` have value `1`.
  have hunitVal : ∀ a b : K, a ∈ 𝒪 → b ∈ 𝒪 → a * b = 1 → v (algebraMap K L a) = 1 := by
    intro a b ha hb hab
    have h1 : v (algebraMap K L a) ≤ 1 := (A.valuation_le_one_iff _).mpr (hmem a ha)
    have h2 : v (algebraMap K L b) ≤ 1 := (A.valuation_le_one_iff _).mpr (hmem b hb)
    have hprod : v (algebraMap K L a) * v (algebraMap K L b) = 1 := by
      rw [← Valuation.map_mul, ← map_mul, hab, map_one, Valuation.map_one]
    refine le_antisymm h1 ?_
    calc (1 : A.ValueGroup) = v (algebraMap K L a) * v (algebraMap K L b) := hprod.symm
      _ ≤ v (algebraMap K L a) * 1 := mul_le_mul_right h2 _
      _ = v (algebraMap K L a) := mul_one _
  have hϖK0 : ((ϖ : K)) ≠ 0 := by
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero] using hϖ.ne_zero
  set γ : A.ValueGroup := v (algebraMap K L (ϖ : K)) with hγdef
  have hγ0 : γ ≠ 0 := by
    rw [hγdef]
    exact (Valuation.ne_zero_iff v).mpr (by simpa using hϖK0)
  -- Every nonzero value coming from `K` is an integer power of `γ`.
  have hint : ∀ c : K, c ≠ 0 → c ∈ 𝒪 → ∃ n : ℕ, v (algebraMap K L c) = γ ^ n := by
    intro c hc0 hc
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨c, hc⟩ : 𝒪)) (by simpa [Subtype.ext_iff] using hc0) hϖ
    refine ⟨n, ?_⟩
    have hcK : c = ((u : 𝒪) : K) * ((ϖ : K)) ^ n := by
      have := congrArg (fun z : 𝒪 => (z : K)) hu
      push_cast at this
      simpa using this
    have huval : v (algebraMap K L ((u : 𝒪) : K)) = 1 := by
      refine hunitVal _ (((u⁻¹ : 𝒪ˣ) : 𝒪) : K) (u : 𝒪).2 ((u⁻¹ : 𝒪ˣ) : 𝒪).2 ?_
      have : ((u * u⁻¹ : 𝒪ˣ) : 𝒪) = (1 : 𝒪) := by simp
      have := congrArg (fun z : 𝒪 => (z : K)) this
      push_cast at this
      simpa using this
    rw [hcK, map_mul, map_pow, Valuation.map_mul, Valuation.map_pow, huval, one_mul, hγdef]
  have hK : ∀ c : K, c ≠ 0 → ∃ n : ℤ, v (algebraMap K L c) = γ ^ n := by
    intro c hc0
    rcases 𝒪.mem_or_inv_mem c with hc | hc
    · obtain ⟨n, hn⟩ := hint c hc0 hc
      exact ⟨(n : ℤ), by rw [hn, zpow_natCast]⟩
    · obtain ⟨n, hn⟩ := hint c⁻¹ (inv_ne_zero hc0) hc
      refine ⟨-(n : ℤ), ?_⟩
      have hinv : v (algebraMap K L c) = (v (algebraMap K L c⁻¹))⁻¹ := by
        rw [map_inv₀ (algebraMap K L) c, map_inv₀ v, inv_inv]
      rw [hinv, hn, zpow_neg, zpow_natCast]
  -- The uniform exponent `N = [L : K]!`.
  set d := Module.finrank K L with hddef
  set N := Nat.factorial d with hNdef
  have hN0 : N ≠ 0 := Nat.factorial_ne_zero d
  set g₀ : (A.ValueGroup)ˣ := Units.mk0 γ hγ0 with hg₀def
  have key : ∀ u : (A.ValueGroup)ˣ, u ^ N ∈ Subgroup.zpowers g₀ := by
    intro u
    obtain ⟨x, hx⟩ := A.valuation_surjective (u : A.ValueGroup)
    have hx0 : x ≠ 0 := by
      intro h
      apply u.ne_zero
      rw [← hx, h, Valuation.map_zero]
    obtain ⟨m, c, hm1, hmd, hc0, hmc⟩ :=
      Valuation.exists_pow_eq_of_isAlgebraic v hx0
        (Algebra.IsAlgebraic.isAlgebraic (R := K) x)
    obtain ⟨n, hn⟩ := hK c hc0
    have hmN : m ∣ N := Nat.dvd_factorial hm1 (le_trans hmd (minpoly.natDegree_le x))
    obtain ⟨k, hk⟩ := hmN
    refine Subgroup.mem_zpowers_iff.mpr ⟨n * (k : ℤ), ?_⟩
    apply Units.ext
    have hval : (u : A.ValueGroup) = v x := hx.symm
    have hxm : v x ^ m = γ ^ n := by rw [← hmc, hn]
    calc ((g₀ ^ (n * (k : ℤ)) : (A.ValueGroup)ˣ) : A.ValueGroup)
        = γ ^ (n * (k : ℤ)) := by rw [hg₀def, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      _ = (γ ^ n) ^ (k : ℤ) := by rw [zpow_mul]
      _ = ((v x) ^ m) ^ (k : ℤ) := by rw [hxm]
      _ = (v x) ^ ((m : ℤ) * (k : ℤ)) := by rw [← zpow_natCast (v x) m, ← zpow_mul]
      _ = (v x) ^ N := by rw [← Nat.cast_mul, ← hk, zpow_natCast]
      _ = ((u ^ N : (A.ValueGroup)ˣ) : A.ValueGroup) := by
            rw [Units.val_pow_eq_pow_val, hval]
  haveI : IsCyclic (Subgroup.zpowers g₀) := Subgroup.isCyclic_zpowers g₀
  refine isCyclic_of_injective
    ((powMonoidHom N).codRestrict (Subgroup.zpowers g₀) key) ?_
  intro a b hab
  have hab' : (a : A.ValueGroup) ^ N = (b : A.ValueGroup) ^ N := by
    have := congrArg (fun z : (Subgroup.zpowers g₀) => ((z : (A.ValueGroup)ˣ) : A.ValueGroup)) hab
    simpa [MonoidHom.codRestrict, powMonoidHom, Units.val_pow_eq_pow_val] using this
  exact Units.ext (pow_left_injective (M := A.ValueGroup) hN0 hab')

/-- A valuation subring `A` of a finite extension `L / K` lying over a discrete valuation subring
`𝒪` of `K` is itself a discrete valuation ring.

This is the classical statement that a valuation extending a discrete valuation to a finite
extension is again discrete; the value group of `A` is cyclic by
`isCyclic_valueGroup_units_of_comap_eq` and nontrivial because a uniformizer of `𝒪` stays a
nonunit in `A`. -/
theorem isDiscreteValuationRing_of_comap_eq [FiniteDimensional K L]
    {𝒪 : ValuationSubring K} [IsDiscreteValuationRing 𝒪]
    (A : ValuationSubring L) (hA : A.comap (algebraMap K L) = 𝒪) :
    IsDiscreteValuationRing A := by
  classical
  -- Stated before `ϖ` is introduced: rewriting `𝒪` backwards in a goal mentioning `ϖ : ↥𝒪`
  -- produces an ill-typed motive.
  have hback : ∀ c : K, algebraMap K L c ∈ A → c ∈ 𝒪 := by
    intro c hc
    rw [← hA]
    exact hc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪)
  have hϖK0 : ((ϖ : K)) ≠ 0 := by
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero] using hϖ.ne_zero
  haveI : IsCyclic (A.ValueGroup)ˣ := isCyclic_valueGroup_units_of_comap_eq A hA
  haveI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass A.valuation)) := inferInstance
  -- Nontriviality: `γ := A.valuation (algebraMap K L ϖ)` is a nonzero value different from `1`.
  set γ : A.ValueGroup := A.valuation (algebraMap K L (ϖ : K)) with hγdef
  have hγ0 : γ ≠ 0 := (Valuation.ne_zero_iff _).mpr (by simpa using hϖK0)
  have hγ1 : γ ≠ 1 := by
    intro h
    have hinvA : (algebraMap K L ((ϖ : K))⁻¹) ∈ A := by
      rw [← A.valuation_le_one_iff, map_inv₀ (algebraMap K L), map_inv₀ A.valuation, ← hγdef, h,
        inv_one]
    have hinv𝒪 : ((ϖ : K))⁻¹ ∈ 𝒪 := hback _ hinvA
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one (⟨((ϖ : K))⁻¹, hinv𝒪⟩ : 𝒪) ?_)
    exact Subtype.ext (by simpa using mul_inv_cancel₀ hϖK0)
  haveI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass A.valuation)) := by
    refine ⟨⟨1, ⟨Units.mk0 γ hγ0, ?_⟩, ?_⟩⟩
    · exact MonoidWithZeroHom.mem_valueGroup _ ⟨algebraMap K L (ϖ : K), rfl⟩
    · intro h
      exact hγ1 (by simpa [Units.ext_iff] using (congrArg Subtype.val h).symm)
  have hdvr := Valuation.valuationSubring_isDiscreteValuationRing A.valuation
  rwa [A.valuationSubring_valuation] at hdvr

end ValuationSubring
