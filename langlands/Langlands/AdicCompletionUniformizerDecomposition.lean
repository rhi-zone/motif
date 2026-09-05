import Langlands.NormMap
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The uniformizer-power decomposition of a unit of `v.adicCompletion F`

Let `F` be the fraction field of a Dedekind domain `A` and `v` a place of `A`. Every unit `a` of
`v.adicCompletion F` decomposes as `a = π^k · u` for some `k : ℤ` and some unit `u` of
`v.adicCompletionIntegers F`, for *any* irreducible `π : v.adicCompletionIntegers F` — this is
`IsDiscreteValuationRing.associated_pow_irreducible` (every nonzero element of a DVR is a unit
times a power of a fixed irreducible), transported from the ring-level `Associated` witness to a
field-level unit equation via the algebra map `v.adicCompletionIntegers F → v.adicCompletion F`.

This single-field statement is the common core of three near-identical proofs that used to be
carried separately in `Langlands.TotallyRamifiedNormIndex`, `Langlands.TotallyRamifiedNormRange`
and `Langlands.UnramifiedNormRange`, one per extension shape (`F`-self, `L` with a uniformizer
already in `L₀`, `L` with a uniformizer transported from `K₀` via `algebraMap`) — each an
`Algebra A F` instance away from being this one lemma. It is stated here, low enough in the import graph (only `Langlands.NormMap`, for the
`IsDiscreteValuationRing (v.adicCompletionIntegers F)` instance, plus Mathlib) to sit below all
three consumers without a cycle, so that all three call sites can specialize it directly
instead of re-deriving it; `Langlands.TotallyRamifiedNormRange`/`Langlands.UnramifiedNormRange`
apply it at `F := L`, `v := w`, with `π` either literally in `L₀` or the `algebraMap`-image of a
`K₀`-uniformizer, and `Langlands.TotallyRamifiedNormIndex` applies it reflexively at `F := K`
(or `L`), `v := v` (or `w`) — no extension structure needed at all for that case.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible` : the
  base case, for `a` already in `v.adicCompletionIntegers F` (`Valued.v a ≤ 1`).
* `IsDedekindDomain.HeightOneSpectrum.exists_zpow_mul_unit_eq_of_irreducible` : the full
  decomposition, for `a` any unit of `v.adicCompletion F`.
-/

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- **Base case of the uniformizer-power decomposition.** If a unit `a` of `v.adicCompletion F`
has `Valued.v a ≤ 1` (i.e. `a` lies in `v.adicCompletionIntegers F`), it decomposes as `a = π^n * u`
for some `n : ℕ` and unit `u` of `v.adicCompletionIntegers F`, for any irreducible `π :
v.adicCompletionIntegers F`. -/
theorem exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible
    {π : v.adicCompletionIntegers F} (hπ : Irreducible π)
    {a : (v.adicCompletion F)ˣ} (hle : Valued.v (a : v.adicCompletion F) ≤ 1) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers F)ˣ),
      (a : v.adicCompletion F) =
        ((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ n * (u : v.adicCompletion F) := by
  set x : v.adicCompletionIntegers F :=
    ⟨(a : v.adicCompletion F), (mem_adicCompletionIntegers A F v).mpr hle⟩ with hxdef
  have hx0 : x ≠ 0 := by
    rw [Ne, ← ZeroMemClass.coe_eq_zero]
    exact a.ne_zero
  obtain ⟨n, u₀, hu₀⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hπ
  refine ⟨n, u₀⁻¹, ?_⟩
  have hval : x = π ^ n * ((u₀⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :=
    (Units.eq_mul_inv_iff_mul_eq u₀).mpr hu₀
  have hcast := congrArg (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) hval
  simp only [map_mul, map_pow] at hcast
  rw [hxdef] at hcast
  exact hcast

/-- **The uniformizer-power decomposition.** Every unit `a` of `v.adicCompletion F` decomposes
as `a = π^k * u` for some `k : ℤ` and some unit `u` of `v.adicCompletionIntegers F`, for any
irreducible `π : v.adicCompletionIntegers F`. -/
theorem exists_zpow_mul_unit_eq_of_irreducible
    {π : v.adicCompletionIntegers F} (hπ : Irreducible π) (a : (v.adicCompletion F)ˣ) :
    ∃ (k : ℤ) (u : (v.adicCompletionIntegers F)ˣ),
      (a : v.adicCompletion F) =
        ((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ k * (u : v.adicCompletion F) := by
  rcases le_total (Valued.v (a : v.adicCompletion F)) 1 with hle | hge
  · obtain ⟨n, u, hnu⟩ := exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible v hπ hle
    exact ⟨(n : ℤ), u, by rw [hnu, zpow_natCast]⟩
  · have hinv_le : Valued.v (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) ≤ 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨n, u, hnu⟩ :=
      exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible v hπ hinv_le
    refine ⟨-(n : ℤ), u⁻¹, ?_⟩
    rw [Units.val_inv_eq_inv_val] at hnu
    have ha : (a : v.adicCompletion F) = ((a : v.adicCompletion F)⁻¹)⁻¹ := (inv_inv _).symm
    have hinv : ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletion F) =
        ((u : (v.adicCompletionIntegers F)ˣ) : v.adicCompletion F)⁻¹ := by
      have h1 : (u : v.adicCompletionIntegers F) *
          ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = 1 := u.mul_inv
      have h2 : ((u : v.adicCompletionIntegers F) : v.adicCompletion F) *
          (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
            v.adicCompletion F) = 1 := by exact_mod_cast h1
      exact eq_inv_of_mul_eq_one_right h2
    rw [ha, hnu, mul_inv, ← hinv, zpow_neg, zpow_natCast]

end IsDedekindDomain.HeightOneSpectrum

end
