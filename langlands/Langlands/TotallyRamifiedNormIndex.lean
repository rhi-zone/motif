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

/-! ### Task 1: the bridging lemma -/

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

/-- The embedding `K₀ˣ ↪ (v.adicCompletion K)ˣ`, with range exactly `(v.adicCompletionIntegers
K).units` (`range_units_map_algebraMap_adicCompletionIntegers_eq`). -/
def embedK : (v.adicCompletionIntegers K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom

/-- The embedding `L₀ˣ ↪ (w.adicCompletion L)ˣ`, with range exactly `(w.adicCompletionIntegers
L).units` (`range_units_map_algebraMap_adicCompletionIntegers_eq`). -/
def embedL : (w.adicCompletionIntegers L)ˣ →* (w.adicCompletion L)ˣ :=
  Units.map (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)).toMonoidHom

omit [Algebra.IsIntegral R S] in
/-- **`localNormMap ∘ embedL = embedK ∘ normUnitsK₀`.** The square commutes: pushing a unit of
`L₀` into `(w.adicCompletion L)ˣ` and then taking the local norm agrees with first taking the
`K₀`-level norm and then pushing into `(v.adicCompletion K)ˣ`. This is exactly
`algebraMap_norm_eq_norm_algebraMap`, transported from `Algebra.norm` to `Units.map`. -/
theorem localNormMap_comp_embedL_eq :
    (localNormMap K L v w).comp (embedL L w) = (embedK K v).comp (normUnitsK₀ K L v w) := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  show Algebra.norm (v.adicCompletion K)
      (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
        (x : w.adicCompletionIntegers L)) =
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (Algebra.norm (v.adicCompletionIntegers K) (x : w.adicCompletionIntegers L))
  rw [algebraMap_norm_eq_norm_algebraMap K L v w x]

omit [Algebra.IsIntegral R S] in
/-- **Task 1: the bridging lemma.** `N_{L/K}(U_L)`, at the `(v.adicCompletion K)ˣ` level (the
literal image `(w.adicCompletionIntegers L).units.map (localNormMap K L v w)` that
`localNormMap_range_eq_of_isTotallyRamified` is phrased in terms of), coincides with the
`K₀ˣ`-level range `MonoidHom.range (normUnitsK₀ K L v w)` pushed forward along `embedK`. Proved by
rewriting `(w.adicCompletionIntegers L).units` as `MonoidHom.range (embedL L w)` (Step 0) and
pushing both sides of the commuting square (`localNormMap_comp_embedL_eq`) through
`MonoidHom.map_range`. -/
theorem units_map_localNormMap_eq_map_normUnitsK₀ :
    (w.adicCompletionIntegers L).units.map (localNormMap K L v w) =
      (MonoidHom.range (normUnitsK₀ K L v w)).map (embedK K v) := by
  rw [show (w.adicCompletionIntegers L).units = MonoidHom.range (embedL L w) from
      (range_units_map_algebraMap_adicCompletionIntegers_eq w).symm,
    MonoidHom.map_range, MonoidHom.map_range, localNormMap_comp_embedL_eq K L v w]

end IsDedekindDomain.HeightOneSpectrum

end
