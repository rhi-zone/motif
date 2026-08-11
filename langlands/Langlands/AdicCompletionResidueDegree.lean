import Langlands.AdicCompletionIntegersResidue
import Langlands.ResidueFieldNorm
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# The residue-degree bridge at adic completions, generically

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. This file proves that `f := v.asIdeal.inertiaDeg' w.asIdeal`,
the residue degree defined *at the base Dedekind-domain level* (via this repo's
`Ideal.inertiaDeg'`), equals the residue degree of the *completed* extension `L₀ / K₀`, i.e.
`Module.finrank (ResidueField K₀) (ResidueField L₀)`.

This is the residue-degree analogue of `Langlands.AdicCompletionRamificationIdeal`'s
`map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx'`, which bridges the ramification index `e`
across the same completion. No `IsTotallyRamified` hypothesis is needed.

## Route

`Ideal.inertiaDeg'_eq_inertiaDeg` and `Ideal.inertiaDeg_eq_of_isMaximal` already reduce `f` to
`Module.finrank (R ⧸ v.asIdeal) (S ⧸ w.asIdeal)`, the *base-level* residue-field extension degree
— this half needs no new work. The remaining gap is showing this equals the *completed-level*
`Module.finrank (ResidueField K₀) (ResidueField L₀)`. That equality is obtained from
`Algebra.finrank_eq_of_equiv_equiv`, fed the two single-place residue-field identifications
`residueFieldQuotientRingEquiv` (already in the repo, `Langlands.AdicCompletionIntegersResidue`)
at `v` and at `w`, together with a naturality square showing these identifications intertwine the
base-level algebra map `R ⧸ v.asIdeal → S ⧸ w.asIdeal` with the completed-level one
`ResidueField K₀ → ResidueField L₀` (`Langlands.ResidueFieldNorm`'s `Algebra` instance). That
naturality square itself reduces, via `residueFieldQuotientRingEquiv`'s construction and
`coe_algebraMap_adicCompletionIntegers`/`adicCompletionComap_algebraMap`, to the single identity
`algebraMap S L (algebraMap R S a) = algebraMap K L (algebraMap R K a)` for `a : R` — the same
"naturality square" fact already proved, in a concrete-instance-specific form, as
`Langlands.TotallyRamifiedConcreteExample.algebraMap_R_K₀_L₀_eq`; the version here is the generic
form, with no `IsTotallyRamified` hypothesis and no hand-built ring `S`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.inertiaDeg_finrank_eq` : the base-level residue-field
  extension degree equals the completed-level one,
  `Module.finrank (R ⧸ v.asIdeal) (S ⧸ w.asIdeal) = Module.finrank (ResidueField K₀) (ResidueField L₀)`.
* `IsDedekindDomain.HeightOneSpectrum.inertiaDeg'_eq_finrank_residueField` : the headline identity,
  `v.asIdeal.inertiaDeg' w.asIdeal = Module.finrank (ResidueField K₀) (ResidueField L₀)`.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-! ### The naturality square `R → K₀ → L₀ = R → S → L₀`, generically -/

omit [IsDedekindDomain R] [IsFractionRing R K] [IsDedekindDomain S] [IsFractionRing S L]
  [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
  [w.asIdeal.LiesOver v.asIdeal] in
/-- `algebraMap S L (algebraMap R S a) = algebraMap K L (algebraMap R K a)`, for `a : R` — the
single identity the naturality square reduces to, from the two scalar towers `R → S → L` and
`R → K → L`. -/
theorem algebraMap_S_L_algebraMap_R_S_eq (a : R) :
    algebraMap S L (algebraMap R S a) = algebraMap K L (algebraMap R K a) := by
  rw [← IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply R K L]

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- **The naturality square `R → K₀ → L₀ = R → S → L₀`, generically.** Pushing `a : R` into
`K₀ := v.adicCompletionIntegers K` and then into `L₀ := w.adicCompletionIntegers L` agrees with
pushing it into `S` and then into `L₀`. The generic (no `IsTotallyRamified`, no hand-built `S`)
version of `Langlands.TotallyRamifiedConcreteExample.algebraMap_R_K₀_L₀_eq`. -/
theorem algebraMap_R_adicCompletionIntegers_eq (a : R) :
    algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
        (algebraMap R (v.adicCompletionIntegers K) a) =
      algebraMap S (w.adicCompletionIntegers L) (algebraMap R S a) := by
  apply Subtype.ext
  rw [coe_algebraMap_adicCompletionIntegers]
  show adicCompletionComap K L v w
      (algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletion K) = _
  rw [show (algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletion K)
        = algebraMap K (v.adicCompletion K) (algebraMap R K a) from rfl,
    adicCompletionComap_algebraMap,
    ← algebraMap_S_L_algebraMap_R_S_eq (R := R) (S := S) K L a]
  rfl

/-! ### `residueFieldQuotientRingEquiv`, unfolded on `Ideal.Quotient.mk` -/

omit [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Module.Finite K L]
  [Algebra.IsIntegral R S] [Module.IsTorsionFree R S] [w.asIdeal.LiesOver v.asIdeal] in
/-- `residueFieldQuotientRingEquiv v`, applied to `Ideal.Quotient.mk v.asIdeal a`, unfolds to the
residue of `a`'s image in `K₀`. Both underlying isomorphisms in `residueFieldQuotientRingEquiv`'s
definition act by `rfl` on `mk`, so this is `rfl`. -/
theorem residueFieldQuotientRingEquiv_apply_mk (a : R) :
    v.residueFieldQuotientRingEquiv (F := K) (Ideal.Quotient.mk v.asIdeal a) =
      residue (v.adicCompletionIntegers K) (algebraMap R (v.adicCompletionIntegers K) a) := rfl

/-! ### The residue-degree bridge -/

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- **The base-level residue-field extension degree equals the completed-level one.**
`Module.finrank (R ⧸ v.asIdeal) (S ⧸ w.asIdeal) = Module.finrank (ResidueField K₀)
(ResidueField L₀)`, via `Algebra.finrank_eq_of_equiv_equiv` fed the two `residueFieldQuotientRingEquiv`s
and the naturality square above. -/
theorem inertiaDeg_finrank_eq :
    Module.finrank (R ⧸ v.asIdeal) (S ⧸ w.asIdeal) =
      Module.finrank (ResidueField (v.adicCompletionIntegers K))
        (ResidueField (w.adicCompletionIntegers L)) := by
  apply Algebra.finrank_eq_of_equiv_equiv (v.residueFieldQuotientRingEquiv (F := K))
    (w.residueFieldQuotientRingEquiv (F := L))
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show algebraMap (ResidueField (v.adicCompletionIntegers K))
      (ResidueField (w.adicCompletionIntegers L))
      (v.residueFieldQuotientRingEquiv (F := K) (Ideal.Quotient.mk v.asIdeal a)) =
    w.residueFieldQuotientRingEquiv (F := L)
      (algebraMap (R ⧸ v.asIdeal) (S ⧸ w.asIdeal) (Ideal.Quotient.mk v.asIdeal a))
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, residueFieldQuotientRingEquiv_apply_mk,
    residueFieldQuotientRingEquiv_apply_mk, algebraMap_residueField_residue,
    algebraMap_R_adicCompletionIntegers_eq]

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- **The residue-degree bridge, headline form.** `f := v.asIdeal.inertiaDeg' w.asIdeal`, defined
at the base Dedekind-domain level, equals the completed-level residue-field extension degree
`Module.finrank (ResidueField K₀) (ResidueField L₀)`. No `IsTotallyRamified` hypothesis: this holds
at every place, not just totally ramified ones — the residue-degree analogue of
`Langlands.AdicCompletionRamificationIdeal.map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx'`. -/
theorem inertiaDeg'_eq_finrank_residueField :
    v.asIdeal.inertiaDeg' w.asIdeal =
      Module.finrank (ResidueField (v.adicCompletionIntegers K))
        (ResidueField (w.adicCompletionIntegers L)) := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  rw [Ideal.inertiaDeg'_eq_inertiaDeg (p := v.asIdeal) (q := w.asIdeal),
    Ideal.inertiaDeg_eq_of_isMaximal (p := v.asIdeal) (q := w.asIdeal),
    inertiaDeg_finrank_eq K L v w]

end IsDedekindDomain.HeightOneSpectrum

end
