import Langlands.NormMap
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuity of the field-level norm

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, `v` a place of
`R`, `w` a place of `S` lying over `v`. This file proves that the field-level norm
`Algebra.norm (v.adicCompletion K) : w.adicCompletion L → v.adicCompletion K` underlying
`localNormMap K L v w` (`Langlands.NormMap`) is continuous.

This continuity fact is needed to pass a limit through the norm at the end of the
successive-approximation argument. It composes directly from instances already built in
`Langlands.NormMap`:
`instNontriviallyNormedFieldAdicCompletion` (giving both `v.adicCompletion K` and
`w.adicCompletion L` `NontriviallyNormedField` structures), the `ContinuousSMul (v.adicCompletion
K) (w.adicCompletion L)` and `Module.Finite (v.adicCompletion K) (w.adicCompletion L)` instances
built for the `localNormMap` construction, and `CompleteSpace (v.adicCompletion K)`
(`Mathlib.RingTheory.DedekindDomain.AdicValuation`). With these, `Algebra.leftMulMatrix b` (a
`v.adicCompletion K`-linear map into `Matrix n n (v.adicCompletion K)`, `b` a chosen basis) is
continuous by `LinearMap.continuous_of_finiteDimensional` (any linear map out of a
finite-dimensional space over a complete nontrivially normed field is continuous), and composing
with `Continuous.matrix_det` (`Mathlib.Topology.Instances.Matrix`) and
`Algebra.norm_eq_matrix_det` gives continuity of the norm itself.

The three ingredients (`LinearMap.continuous_of_finiteDimensional`,
`Continuous.matrix_det`, `Algebra.norm_eq_matrix_det`) are all pre-existing general Mathlib facts,
and every typeclass instance `LinearMap.continuous_of_finiteDimensional` demands was already built
in `Langlands.NormMap` for unrelated reasons (the `localNormMap` construction itself). No new
instance and no new general lemma was needed — only assembling three existing pieces.

## Main result

* `IsDedekindDomain.HeightOneSpectrum.continuous_norm_adicCompletion`
-/

noncomputable section

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

omit [Algebra.IsIntegral R S] [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- **The field-level norm `Algebra.norm (v.adicCompletion K) : w.adicCompletion L →
v.adicCompletion K` is continuous.** This is the norm underlying `localNormMap K L v w` (via
`Units.map`). Proved by expressing the norm as `det ∘ leftMulMatrix b` for a chosen
`v.adicCompletion K`-basis `b` of `w.adicCompletion L`: `leftMulMatrix b` is linear on a
finite-dimensional space over the complete field `v.adicCompletion K`
(`LinearMap.continuous_of_finiteDimensional`), and `det` is continuous on matrices over a
topological ring (`Continuous.matrix_det`). -/
theorem continuous_norm_adicCompletion :
    Continuous (Algebra.norm (v.adicCompletion K) : w.adicCompletion L → v.adicCompletion K) := by
  classical
  set b := Module.Free.chooseBasis (v.adicCompletion K) (w.adicCompletion L)
  have hlin : Continuous (Algebra.leftMulMatrix b) :=
    LinearMap.continuous_of_finiteDimensional (Algebra.leftMulMatrix b).toLinearMap
  have hdet : Continuous (fun x => (Algebra.leftMulMatrix b x).det) := hlin.matrix_det
  have heq : (fun x => (Algebra.leftMulMatrix b x).det) = Algebra.norm (v.adicCompletion K) := by
    funext x; exact (Algebra.norm_eq_matrix_det b x).symm
  rwa [heq] at hdet

end IsDedekindDomain.HeightOneSpectrum

end
