import Langlands.RamificationFiltration
import Langlands.AdicCompletionIntegralClosure

/-!
# Ramification filtration for adic completions

Specializes `Langlands.RamificationFiltration`'s general `ValuationSubring.ramificationGroup` to
this repo's adic-completion setting (`Langlands.AdicCompletionIntegralClosure`,
`Langlands.UnramifiedValuationExtension`): `R S` Dedekind domains with fraction fields `K L`,
`v : HeightOneSpectrum R`, `w : HeightOneSpectrum S` with `w.asIdeal.LiesOver v.asIdeal`,
`K₀ := v.adicCompletionIntegers K`, `L₀ := w.adicCompletionIntegers L`. This file supplies no new
mathematical content beyond the general theory of `Langlands.RamificationFiltration`, instantiated
at `A := L₀ : ValuationSubring (w.adicCompletion L)` over the base field `v.adicCompletion K` (the
`Algebra (v.adicCompletion K) (w.adicCompletion L)` instance is supplied by `Langlands.NormMap`,
already in scope via `Langlands.AdicCompletionIntegralClosure`).

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.ramificationGroup` : the `i`-th ramification group in lower
  numbering of `w.adicCompletionIntegers L` over `v.adicCompletion K`.

## Scope

The Galois-implies-decompositionSubgroup-eq-top corollary considered in the design brief for this
file (paralleling `Langlands.NormMap`'s `hAfix` pattern via
`LocalField.valuationSubring_eq_of_comap_eq`) is not attempted: that lemma needs its base field to
carry a `CompleteSpace`/`NontriviallyNormedField`/`IsUltrametricDist` instance chain (or the
packaged `IsNonarchimedeanLocalField` typeclass), which is not part of the general `R S K L v w`
variable block used here and throughout `Langlands.AdicCompletionIntegralClosure` — supplying it
would need additional hypotheses beyond what this pass's scope covers.
-/

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-- The `i`-th ramification group in lower numbering of `w.adicCompletionIntegers L`, viewed as a
`ValuationSubring (w.adicCompletion L)`, over the base field `v.adicCompletion K`. This is
`ValuationSubring.ramificationGroup` specialized to this repo's adic-completion setting. -/
def ramificationGroup (i : ℕ) :
    Subgroup ((w.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K)) :=
  ValuationSubring.ramificationGroup (v.adicCompletion K) (w.adicCompletionIntegers L) i

end IsDedekindDomain.HeightOneSpectrum

end
