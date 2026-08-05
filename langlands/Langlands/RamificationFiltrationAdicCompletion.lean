import Langlands.RamificationFiltration
import Langlands.AdicCompletionIntegralClosure
import Langlands.NormMap

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

## Main results

* `IsDedekindDomain.HeightOneSpectrum.decompositionSubgroup_eq_top` : the decomposition subgroup
  of `w.adicCompletionIntegers L` in `(w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)`
  is everything — no Galois/normality hypothesis on `w.adicCompletion L / v.adicCompletion K`
  is needed, only completeness of the base field `v.adicCompletion K`. See its docstring.

## Scope

The associated-graded embeddings for `Langlands.RamificationFiltration`'s filtration
(`ramificationGroup i / ramificationGroup (i+1) ↪ residue-field data`) are not attempted here or in
the general file: see `Langlands.RamificationFiltration`'s docstring for the precise blocker
(monogenicity of the ring of integers over the inertia-fixed subfield, absent from Mathlib).
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

/-! ### The decomposition subgroup is everything -/

open scoped Pointwise

omit [Algebra.IsIntegral R S] in
/-- The decomposition subgroup of `w.adicCompletionIntegers L` (as a `ValuationSubring
(w.adicCompletion L)`) in `(w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)` is
all of that automorphism group.

No Galois/normality hypothesis on `w.adicCompletion L / v.adicCompletion K` is needed: since
`v.adicCompletion K` is complete (`instCompleteSpaceAdicCompletion`, via
`Mathlib.RingTheory.DedekindDomain.AdicValuation`) and `w.adicCompletion L / v.adicCompletion K` is
algebraic (`Module.Finite`, an existing instance from `Langlands.NormMap`), every algebraic
extension of a complete field has a *unique* extension of the valuation
(`LocalField.valuationSubring_eq_of_comap_eq`, `Langlands.HenselianValuation`, built on Mathlib's
`spectralNorm_unique_field_norm_ext`). Both `w.adicCompletionIntegers L` and any of its
`σ`-translates comap to `v.adicCompletionIntegers K` under `algebraMap (v.adicCompletion K)
(w.adicCompletion L)` (`ValuationSubring.comap_smul_eq` for the translate,
`adicCompletionIntegers_comap_eq` for the base case, bridged to `ValuativeRel.valuation`'s
valuation subring via `valuation_valuationSubring_eq_adicCompletionIntegers`), so uniqueness forces
`σ • (w.adicCompletionIntegers L) = w.adicCompletionIntegers L` for every `σ`. This exactly
parallels `LocalField.decompositionSubgroup_eq_top` (`Langlands.WeilGroup`), which is the same fact
for `L = AlgebraicClosure K` under the packaged `IsNonarchimedeanLocalField K` hypothesis instead of
this file's `v.adicCompletion K`-specific instance chain. -/
theorem decompositionSubgroup_eq_top :
    (w.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  rw [MulAction.mem_stabilizer_iff]
  have hbase : (w.adicCompletionIntegers L).comap (algebraMap (v.adicCompletion K) (w.adicCompletion L))
      = (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring := by
    rw [valuation_valuationSubring_eq_adicCompletionIntegers]
    exact adicCompletionIntegers_comap_eq K L v w
  apply LocalField.valuationSubring_eq_of_comap_eq (K := v.adicCompletion K)
  · rw [ValuationSubring.comap_smul_eq]
    exact hbase
  · exact hbase

end IsDedekindDomain.HeightOneSpectrum

end
