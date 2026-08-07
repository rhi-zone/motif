import Langlands.TotallyRamifiedNormRange
import Langlands.TotallyRamifiedNormResidueImage
import Mathlib.GroupTheory.Index

/-!
# The totally ramified norm-group index, at the `(v.adicCompletion K)ˣ` level

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`, `e := v.asIdeal.ramificationIdx' w.asIdeal`. This file bridges
`Langlands.TotallyRamifiedNormResidueImage`'s `K₀ˣ`-level index formula
(`index_normUnitsK₀_range_eq_of_isTotallyRamified`) up to the ambient-field index
`[(v.adicCompletion K)ˣ : MonoidHom.range (localNormMap K L v w)]`, closing the gap left open by
that file's module docstring.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.range_units_map_algebraMap_adicCompletionIntegers_eq` : the
  generic embedding-range lemma, proved once and instantiated at both `K` and `L`.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

/-! ### Step 0: the embedding range lemma -/

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F]

/-- **The image of `K₀ˣ` (or `L₀ˣ`) inside the ambient field's units is exactly the local units.**
`Units.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))` has range exactly
`(v.adicCompletionIntegers F).units`. -/
theorem range_units_map_algebraMap_adicCompletionIntegers_eq (v : HeightOneSpectrum A) :
    MonoidHom.range
        (Units.map
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).toMonoidHom) =
      (v.adicCompletionIntegers F).units := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact Submonoid.mem_units_of_val_mem_inv_val_mem _ (x : v.adicCompletionIntegers F).2
      ((x⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  · intro y hy
    obtain ⟨hy1, hy2⟩ :=
      (Submonoid.mem_units_iff (v.adicCompletionIntegers F).toSubmonoid y).mp hy
    set y₀ : v.adicCompletionIntegers F := ⟨(y : v.adicCompletion F), hy1⟩ with hy₀def
    have hy₀u : IsUnit y₀ := by
      refine IsUnit.of_mul_eq_one
        (⟨(y⁻¹ : (v.adicCompletion F)ˣ), hy2⟩ : v.adicCompletionIntegers F) ?_
      apply Subtype.ext
      show (y : v.adicCompletion F) * ((y⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1
      exact_mod_cast y.mul_inv
    refine ⟨hy₀u.unit, ?_⟩
    apply Units.ext
    show algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (hy₀u.unit : _) = y
    rw [hy₀u.unit_spec, hy₀def]
    rfl

end IsDedekindDomain.HeightOneSpectrum

end
