import Langlands.PrincipalUnitsFiltration
import Langlands.RamificationFiltrationAdicCompletion

/-!
# The principal-units filtration for adic completions

Specializes `Langlands.PrincipalUnitsFiltration`'s general `ValuationSubring.principalUnitsPow` /
`principalUnitsGradedEquiv` to this repo's adic-completion setting (`Langlands.NormMap`,
`Langlands.AdicCompletionIntegralClosure`): `R S` Dedekind domains with fraction fields `K L`,
`v : HeightOneSpectrum R`, `w : HeightOneSpectrum S` with `w.asIdeal.LiesOver v.asIdeal`,
`K₀ := v.adicCompletionIntegers K`, `L₀ := w.adicCompletionIntegers L`. Both `K₀` and
`L₀` are already `ValuationSubring`s (of `v.adicCompletion K`, `w.adicCompletion L` respectively),
so `PrincipalUnitsFiltration.lean`'s theory applies to each with no new mathematical content —
purely an instantiation.

## Main definitions

None beyond `ValuationSubring.principalUnitsPow` itself, applied at `A := L₀` and `A := K₀`; this
file supplies no new `def`s, only specialized restatements of `PrincipalUnitsFiltration.lean`'s
theorems for the two concrete uniformizer choices `π_L` (of `L₀`) and `π_K` (of `K₀`) that appear
throughout the rest of this repo's adic-completion files.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.principalUnitsGradedEquiv_L` : for `π` a uniformizer of `L₀`
  and `i : ℕ`, `U_{L₀}^{(i+1)} ⧸ U_{L₀}^{(i+2)} ≃* Multiplicative (ResidueField L₀)`.
* `IsDedekindDomain.HeightOneSpectrum.principalUnitsGradedEquiv_K` : the same for `K₀`.
-/

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

omit [Algebra.IsIntegral R S] in
/-- **The `i`-th principal-units subgroup of `L₀ˣ` (`i ≥ 0`).** `ValuationSubring.principalUnitsPow`
specialized to `A := w.adicCompletionIntegers L`. -/
def principalUnitsPowL (i : ℕ) : Subgroup (w.adicCompletionIntegers L)ˣ :=
  ValuationSubring.principalUnitsPow (w.adicCompletionIntegers L) i

omit [Algebra.IsIntegral R S] [Module.Finite K L] in
/-- **The `i`-th principal-units subgroup of `K₀ˣ` (`i ≥ 0`).** -/
def principalUnitsPowK (i : ℕ) : Subgroup (v.adicCompletionIntegers K)ˣ :=
  ValuationSubring.principalUnitsPow (v.adicCompletionIntegers K) i

omit [Algebra.IsIntegral R S] in
/-- **The `i ≥ 1` associated-graded isomorphism for `L₀`**: `U_{L₀}^{(i+1)} ⧸ U_{L₀}^{(i+2)} ≃*
Multiplicative (ResidueField L₀)`, for `π` a uniformizer of `L₀`. -/
noncomputable def principalUnitsGradedEquiv_L {π : w.adicCompletionIntegers L}
    (hπ : Irreducible π) (i : ℕ) :
    principalUnitsPowL L w (i + 1) ⧸
        (ValuationSubring.principalUnitsGradedHom (w.adicCompletionIntegers L)
          hπ.maximalIdeal_eq hπ.ne_zero i).ker ≃*
      Multiplicative (IsLocalRing.ResidueField (w.adicCompletionIntegers L)) :=
  ValuationSubring.principalUnitsGradedEquiv (w.adicCompletionIntegers L)
    hπ.maximalIdeal_eq hπ.ne_zero i

omit [Algebra.IsIntegral R S] [Module.Finite K L] in
/-- **The `i ≥ 1` associated-graded isomorphism for `K₀`**: `U_{K₀}^{(i+1)} ⧸ U_{K₀}^{(i+2)} ≃*
Multiplicative (ResidueField K₀)`, for `π` a uniformizer of `K₀`. -/
noncomputable def principalUnitsGradedEquiv_K {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) (i : ℕ) :
    principalUnitsPowK K v (i + 1) ⧸
        (ValuationSubring.principalUnitsGradedHom (v.adicCompletionIntegers K)
          hπ.maximalIdeal_eq hπ.ne_zero i).ker ≃*
      Multiplicative (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  ValuationSubring.principalUnitsGradedEquiv (v.adicCompletionIntegers K)
    hπ.maximalIdeal_eq hπ.ne_zero i

end IsDedekindDomain.HeightOneSpectrum

end

