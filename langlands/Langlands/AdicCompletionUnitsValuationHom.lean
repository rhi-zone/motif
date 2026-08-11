import Langlands.NormMap

/-!
# The valuation as a `MonoidHom` on units, `(v.adicCompletion F)ˣ →* ℤᵐ⁰ˣ`, surjective with kernel
`U_{F_v}`

`Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰` is only a `MonoidWithZeroHom` (it sends `0 ↦ 0`),
so it does not restrict to a `MonoidHom` on the nose. But `Units.map`, applied to `Valued.v`'s
coercion to a plain `MonoidHom (v.adicCompletion F) ℤᵐ⁰` (available generically for any
`Valuation`, via its `MonoidWithZeroHomClass` instance), gives exactly the wanted
`(v.adicCompletion F)ˣ →* ℤᵐ⁰ˣ`. This file records that it is surjective — from
`valuedAdicCompletion_surjective` together with `v.adicCompletion F` being a field, so every
nonzero valuation value is hit by a genuine unit — and that its kernel is exactly
`(v.adicCompletionIntegers F).units` (`adicCompletionIntegers.mem_units_iff_valued_eq_one`).

This is the ingredient `Langlands.AdicCompletionNormGroupIndex`'s
`index_sup_units_eq_inertiaDeg'` needs to convert the valuation-of-norm formula
(`Langlands.AdicCompletionValuationNorm.valued_localNormMap_eq_pow`) into an index statement, via
`Subgroup.comap_map_eq` and `Subgroup.index_comap_of_surjective`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuationUnitsHom` : the `MonoidHom`
  `(v.adicCompletion F)ˣ →* ℤᵐ⁰ˣ`.
* `IsDedekindDomain.HeightOneSpectrum.valuationUnitsHom_surjective` : it is surjective.
* `IsDedekindDomain.HeightOneSpectrum.valuationUnitsHom_ker` : its kernel is
  `(v.adicCompletionIntegers F).units`.
-/

noncomputable section

open IsDedekindDomain

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (F : Type*) [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- **The valuation as a `MonoidHom` on units.** `Valued.v`'s coercion to a `MonoidHom
(v.adicCompletion F) ℤᵐ⁰`, pushed to units via `Units.map`. -/
def valuationUnitsHom : (v.adicCompletion F)ˣ →* ℤᵐ⁰ˣ :=
  Units.map (Valued.v (R := v.adicCompletion F) (Γ₀ := ℤᵐ⁰)).toMonoidWithZeroHom.toMonoidHom

@[simp]
theorem coe_valuationUnitsHom_apply (a : (v.adicCompletion F)ˣ) :
    (valuationUnitsHom F v a : ℤᵐ⁰) = Valued.v (a : v.adicCompletion F) := rfl

/-- **`valuationUnitsHom` is surjective.** Given `γ : ℤᵐ⁰ˣ`, `valuedAdicCompletion_surjective`
finds `x : v.adicCompletion F` with `Valued.v x = γ`; `x ≠ 0` since `γ ≠ 0`, so `x` is a unit of
the field `v.adicCompletion F`, and its valuation-image is `γ`. -/
theorem valuationUnitsHom_surjective : Function.Surjective (valuationUnitsHom F v) := by
  intro γ
  obtain ⟨x, hx⟩ := valuedAdicCompletion_surjective F v (γ : ℤᵐ⁰)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hx.symm)
  refine ⟨(isUnit_iff_ne_zero.mpr hx0).unit, Units.ext ?_⟩
  rw [coe_valuationUnitsHom_apply, IsUnit.unit_spec, hx]

/-- **The kernel of `valuationUnitsHom` is exactly the local units `(v.adicCompletionIntegers
F).units`.** Immediate from `adicCompletionIntegers.mem_units_iff_valued_eq_one`. -/
theorem valuationUnitsHom_ker : (valuationUnitsHom F v).ker = (v.adicCompletionIntegers F).units := by
  ext a
  rw [MonoidHom.mem_ker, Units.ext_iff, coe_valuationUnitsHom_apply, Units.val_one]
  exact (adicCompletionIntegers.mem_units_iff_valued_eq_one).symm

end IsDedekindDomain.HeightOneSpectrum

end
