import Langlands.NormMap
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The residue fields of a pair of adic completions, and the norm between them

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`. `Langlands.NormMap` builds the ring hom
`adicCompletionComap : v.adicCompletion K →+* w.adicCompletion L` and proves
`adicCompletionIntegers_comap_eq`, that it pulls `w.adicCompletionIntegers L` back exactly to
`v.adicCompletionIntegers K`.

This file turns that comap equation into the statement that `Valued.v` on `w.adicCompletion L` is
an *extension* of `Valued.v` on `v.adicCompletion K` in the sense of `Valuation.HasExtension`.
That single instance unlocks, from `Mathlib.RingTheory.Valuation.Extension`, the whole tower of
structure on the valuation subrings and their residue fields:

* `Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)`,
* `IsLocalHom` for that algebra map, hence `(maximalIdeal L₀).LiesOver (maximalIdeal K₀)`,
* `Algebra 𝓀[K] 𝓀[L]` on the residue fields, writing
  `𝓀[K] := ResidueField (v.adicCompletionIntegers K)`.

With that algebra structure in place, `FiniteField.norm_surjective` gives surjectivity of the
residue-field norm as soon as `𝓀[L]` is finite (which is the case for local fields, and is taken
here as a hypothesis, `R` and `S` being arbitrary Dedekind domains).

## Scope — read this before citing the surjectivity results

`residueField_norm_surjective` and `residueField_units_norm_surjective` below are statements about
the **abstract** norm `Algebra.norm 𝓀[K] : 𝓀[L] → 𝓀[K]` of the residue-field extension. They are
*not* statements about `IsDedekindDomain.HeightOneSpectrum.localNormMap` (the norm
`N_{L_w/K_v} : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ` of `Langlands.NormMap`). Proving
that `localNormMap` reduces mod the maximal ideal to `Algebra.norm 𝓀[K]` — the "compatibility
square" — is a separate, open problem; see `ROADMAP.md`, Phase 2a. Nothing here should be read as
having closed it.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.hasExtension_valued_adicCompletion`
* `IsDedekindDomain.HeightOneSpectrum.residueField_norm_surjective`
* `IsDedekindDomain.HeightOneSpectrum.residueField_units_norm_surjective`
-/

noncomputable section

open IsLocalRing

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-! ### `Valued.v` on `L_w` extends `Valued.v` on `K_v` -/

/-- The valuation of `w.adicCompletion L` is an extension of the valuation of
`v.adicCompletion K`, along `adicCompletionComap`.

`Valuation.HasExtension` asks for `IsEquiv` of the base valuation with the comap of the top one;
by `Valuation.isEquiv_iff_val_le_one` that is exactly the statement that an element of
`v.adicCompletion K` has valuation `≤ 1` iff its image does, which is
`adicCompletionIntegers_comap_eq` read pointwise. (The two valuations are not *equal* under comap
— they differ by the ramification index `e`, per the exponentiation formula proved inside
`adicCompletionIntegers_comap_eq` — which is precisely why `HasExtension` is stated with `IsEquiv`
rather than equality.) -/
instance hasExtension_valued_adicCompletion :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).HasExtension
      (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰) where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    have hx : x ∈ (w.adicCompletionIntegers L).comap (adicCompletionComap K L v w) ↔
        x ∈ v.adicCompletionIntegers K := by
      rw [adicCompletionIntegers_comap_eq K L v w]
    rw [ValuationSubring.mem_comap, mem_adicCompletionIntegers, mem_adicCompletionIntegers] at hx
    exact hx.symm

/-! ### The induced structure on the rings of integers and the residue fields

`Mathlib.RingTheory.Valuation.Extension` states these for `Valuation.valuationSubring`;
`adicCompletionIntegers` is *defined* to be that, but is not reducible, so instance search does not
see through it. The declarations below re-express the instances in `adicCompletionIntegers` form. -/

/-- `w.adicCompletionIntegers L` is an algebra over `v.adicCompletionIntegers K`, by restricting
`adicCompletionComap`. -/
instance : Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  inferInstanceAs (Algebra
    (Valuation.valuationSubring (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))
    (Valuation.valuationSubring (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)))

/-- The inclusion of rings of integers is a local homomorphism: an element of
`v.adicCompletionIntegers K` whose image is a unit was already a unit, the valuations being
equivalent. -/
instance : IsLocalHom
    (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) :=
  inferInstanceAs (IsLocalHom
    (algebraMap (Valuation.valuationSubring (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))
      (Valuation.valuationSubring (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰))))

/-- The residue field of `w.adicCompletionIntegers L` is an algebra over that of
`v.adicCompletionIntegers K`, induced by the local homomorphism above. -/
instance : Algebra (ResidueField (v.adicCompletionIntegers K))
    (ResidueField (w.adicCompletionIntegers L)) :=
  inferInstanceAs (Algebra
    (ResidueField (Valuation.valuationSubring (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)))
    (ResidueField (Valuation.valuationSubring (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰))))

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- The algebra map on rings of integers is the restriction of `adicCompletionComap`. This pins
down that the instances above are the intended ones, and not some unrelated structure found by
instance search. -/
theorem coe_algebraMap_adicCompletionIntegers (x : v.adicCompletionIntegers K) :
    ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) x :
        w.adicCompletionIntegers L) : w.adicCompletion L) =
      adicCompletionComap K L v w (x : v.adicCompletion K) :=
  rfl

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- The algebra map on residue fields is induced by the algebra map on rings of integers, i.e. the
square `K₀ → L₀ → 𝓀[L]` = `K₀ → 𝓀[K] → 𝓀[L]` commutes. -/
theorem algebraMap_residueField_residue (x : v.adicCompletionIntegers K) :
    algebraMap (ResidueField (v.adicCompletionIntegers K))
        (ResidueField (w.adicCompletionIntegers L)) (residue _ x) =
      residue _ (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) x) :=
  rfl

/-! ### Surjectivity of the residue-field norm

Note again: this is the norm of the residue-field extension `𝓀[L] / 𝓀[K]` as such. It is *not*
proved here to be the reduction of `localNormMap`. -/

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- For `𝓀[L]` finite, the norm `𝓀[L] → 𝓀[K]` of the residue-field extension is surjective.

This is `FiniteField.norm_surjective` applied to the residue-field algebra structure built above;
the content of the present file is that structure, not the finite-field fact.

**This is the abstract residue-field norm**, not (yet) the reduction of
`IsDedekindDomain.HeightOneSpectrum.localNormMap` — see the module docstring. -/
theorem residueField_norm_surjective
    [Finite (ResidueField (w.adicCompletionIntegers L))] :
    Function.Surjective (Algebra.norm (ResidueField (v.adicCompletionIntegers K))
      (S := ResidueField (w.adicCompletionIntegers L))) :=
  FiniteField.norm_surjective _ _

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- For `𝓀[L]` finite, the norm is surjective on residue-field unit groups, `𝓀[L]ˣ ↠ 𝓀[K]ˣ`.

**This is the abstract residue-field norm**, not (yet) the reduction of
`IsDedekindDomain.HeightOneSpectrum.localNormMap` — see the module docstring. -/
theorem residueField_units_norm_surjective
    [Finite (ResidueField (w.adicCompletionIntegers L))] :
    Function.Surjective (Units.map (Algebra.norm (ResidueField (v.adicCompletionIntegers K))
      (S := ResidueField (w.adicCompletionIntegers L)))) :=
  FiniteField.unitsMap_norm_surjective _ _

end IsDedekindDomain.HeightOneSpectrum

end
