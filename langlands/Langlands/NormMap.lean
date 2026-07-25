import Langlands.IdeleGroup
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Norm.Defs

/-!
# Local pieces of the idèle norm map

This file assembles the infrastructure the idèle norm map `NumberField.IdeleGroup.normMap`
(`Langlands/IdeleGroup.lean`) needs, filling in the three gaps identified in the survey there:

1. The place-lying-over relation between `HeightOneSpectrum R` and `HeightOneSpectrum S` for a
   ring extension `R → S`: this turns out to already be present in Mathlib, just not under the
   name the previous survey looked for. `IsDedekindDomain.HeightOneSpectrum.under` (in
   `Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas`) restricts a height-one prime `w` of `S` to
   one of `R` (given `Algebra.IsIntegral R S`), and the "lying over" relation itself is
   `w.asIdeal.LiesOver v.asIdeal` (from `Mathlib.RingTheory.Ideal.Over`, applied to the
   underlying ideals) -- indeed `Mathlib.NumberTheory.RamificationInertia.Valuation` already
   states its results in terms of exactly this relation, e.g.
   `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`. `finite_liesOver` below packages the
   finiteness of the set of places lying over a given `v`, via `IsDedekindDomain.primesOver_finite`.
2. Local norm maps between completions of different fields: Mathlib does have (as of a 2026
   addition, `Mathlib.NumberTheory.RamificationInertia.Valuation`) the uniform continuity of
   `algebraMap K L` between the *valued fields* `WithVal (v.valuation K)` and
   `WithVal (w.valuation L)` for `w` lying over `v`
   (`IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver`). Composed with
   `UniformSpace.Completion.mapRingHom` and the identification of `adicCompletion` with the
   completion of the valued field (`adicCompletion.equiv`), this gives an honest ring hom
   `v.adicCompletion K →+* w.adicCompletion L` (`adicCompletionComap` below) -- not a `sorry`.
   The local norm map itself (`localNormMap`) is then `Units.map (Algebra.norm _)` for the
   `Algebra` structure this ring hom induces; also not a `sorry`, though its good behavior
   (matching the classical local norm, being trivial off a finite set of places, etc.) is not
   proved here.
3. A ring hom `AdeleRing S L →+* AdeleRing R K` induced by a finite extension: still missing.
   Assembling the local norms of (2) into a global map on the finite adèles requires knowing the
   local norm map is a *local unit* (valuation `1`) whenever `a_w` is, at all but finitely many
   places -- i.e. that `adicCompletionComap`/`localNormMap` restricts well to
   `adicCompletionIntegers`. This is the standard fact that the local norm map of an unramified
   place sends units to units, but it is not proved here; `IdeleGroup.normMap` therefore remains
   a `sorry`, now expressed in terms of the (fully defined) local pieces above rather than as an
   opaque black box.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionComap` : the ring hom
  `v.adicCompletion K →+* w.adicCompletion L` induced by `algebraMap K L`, for `w` a place of `S`
  lying over `v`.
* `IsDedekindDomain.HeightOneSpectrum.localNormMap` : the local norm map on units,
  `(w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ`.
* `IsDedekindDomain.HeightOneSpectrum.finite_liesOver` : only finitely many places of `S` lie over
  a given place `v` of `R`.
-/

noncomputable section

open IsDedekindDomain

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

namespace IsDedekindDomain.HeightOneSpectrum

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-- The ring hom `v.adicCompletion K →+* w.adicCompletion L` induced by `algebraMap K L`, for a
place `w` of `S` lying over a place `v` of `R`. Built by extending the uniformly continuous map
`algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))`
(`uniformContinuous_algebraMap_liesOver`) to the completions, then transporting along the
identification of `adicCompletion` with the completion of the valued field
(`adicCompletion.equiv`). -/
def adicCompletionComap : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)

/-- The `w.adicCompletion L` obtained from `v.adicCompletion K` via `adicCompletionComap`, for a
place `w` of `S` lying over a place `v` of `R`. -/
instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionComap K L v w).toAlgebra

/-- The local norm map `N_{L_w/K_v} : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ`, for a place
`w` of `S` lying over a place `v` of `R`: the norm of the finite (as `L / K` is finite, hence so is
`L_w / K_v`, though this finiteness is not needed for the definition itself) extension
`w.adicCompletion L` of `v.adicCompletion K`, transported to units via `Units.map`. This is the
local factor of the idèle norm map `N_{L/K} a = (∏_{w ∣ v} N_{L_w/K_v}(a_w))_v`. -/
def localNormMap : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (Algebra.norm (v.adicCompletion K) : w.adicCompletion L →* v.adicCompletion K)

/-- Only finitely many places `w` of `S` lie over a given place `v` of `R`: the set
`{w // w.asIdeal.LiesOver v.asIdeal}` injects into `v.asIdeal.primesOver S`
(via `w ↦ w.asIdeal`), which is finite since `v.asIdeal` is a nonzero (hence maximal, by
`IsDedekindDomain.HeightOneSpectrum.isMaximal`) ideal of the Dedekind domain `R` and `S / R` is
integral (`IsDedekindDomain.primesOver_finite`). -/
theorem finite_liesOver (v : HeightOneSpectrum R) :
    {w : HeightOneSpectrum S | w.asIdeal.LiesOver v.asIdeal}.Finite := by
  have hsub : (fun w : HeightOneSpectrum S => w.asIdeal) ''
      {w : HeightOneSpectrum S | w.asIdeal.LiesOver v.asIdeal} ⊆ v.asIdeal.primesOver S := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, hw⟩
  exact Set.Finite.of_finite_image
    (Set.Finite.subset (IsDedekindDomain.primesOver_finite v.asIdeal S) hsub)
    (HeightOneSpectrum.asIdeal_injective.injOn)

end IsDedekindDomain.HeightOneSpectrum

end
