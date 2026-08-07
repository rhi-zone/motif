import Langlands.AdicCompletionIntegersResidue
import Langlands.NormMap

/-!
# Mixed-characteristic instances for a general adic completion

`Langlands.NonarchimedeanExponential`/`Langlands.NonarchimedeanExponentialFiltration` build a
convergent nonarchimedean `exp`/`log` for any `[NormedField K] [IsUltrametricDist K] [CharZero K]`
field `K` of residue characteristic `p`. Instantiating that machinery for the concrete
`v.adicCompletion F` setting used throughout this repo needs two facts that, before this file, had
no instance anywhere: `CharZero (v.adicCompletion F)`, and a residue-characteristic-`p` instance for
`IsLocalRing.ResidueField (v.adicCompletionIntegers F)`. Both turn out to be cheap consequences of
facts already proved in this repo (`Langlands.NormMap`'s `Field (v.adicCompletion F)` instance chain
and `Langlands.AdicCompletionIntegersResidue`'s `residueFieldQuotientRingEquiv`), not new
mathematical content.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.instCharZeroAdicCompletion` : `[CharZero F] →
  CharZero (v.adicCompletion F)`, for any place `v` of any Dedekind domain `A` with fraction field
  `F`. `CharZero` transfers forward along the injective ring hom `algebraMap F (v.adicCompletion F)`
  (injective because `F` is a field, hence `IsSimpleRing`, and `v.adicCompletion F` is a field, hence
  `Nontrivial` — `RingHom.injective`).
* `IsDedekindDomain.HeightOneSpectrum.instCharPResidueFieldAdicCompletionIntegers` :
  `[CharP (A ⧸ v.asIdeal) p] → CharP (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) p`.
  Completing at `v` does not change the residue field
  (`residueFieldQuotientRingEquiv : A ⧸ v.asIdeal ≃+* ResidueField (v.adicCompletionIntegers F)`,
  `Langlands.AdicCompletionIntegersResidue`), and characteristic transfers along the injective ring
  hom underlying that equivalence.

Neither result needs `A`/`F` to be number-field-flavored, nor any extension data `L / K` — both are
single-place facts about a general Dedekind domain and its fraction field, matching the generality of
the file they draw from.

Note that `CharZero F` is *not* automatic in this repo's setting: `A` (hence `F`) may have positive
characteristic (`Langlands.TotallyRamifiedConcreteExample` is exactly such an example, deliberately
built with `CharP K p` to be a *tame*-ramification test case, the opposite of what `exp`/`log`
require). `instCharZeroAdicCompletion` requires the hypothesis `[CharZero F]` to be supplied at each
use site; it does not manufacture it.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- **`v.adicCompletion F` has characteristic zero whenever `F` does.** `algebraMap F
(v.adicCompletion F)` is injective — a ring hom out of a field (`IsSimpleRing`, via
`DivisionRing.isSimpleRing`) into a nontrivial ring (`v.adicCompletion F` is itself a field) is
injective (`RingHom.injective`) — and `CharZero` transfers forward along an injective ring hom
(`charZero_of_injective_algebraMap`). -/
instance instCharZeroAdicCompletion [CharZero F] : CharZero (v.adicCompletion F) :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap F (v.adicCompletion F)))

/-- **The residue field of `v.adicCompletionIntegers F` has the same characteristic as the residue
field `A ⧸ v.asIdeal` of the base Dedekind domain.** Completing at `v` does not change the residue
field (`residueFieldQuotientRingEquiv`, `Langlands.AdicCompletionIntegersResidue`); characteristic
transfers along the injective ring hom underlying that equivalence
(`charP_of_injective_ringHom`). -/
instance instCharPResidueFieldAdicCompletionIntegers (p : ℕ) [CharP (A ⧸ v.asIdeal) p] :
    CharP (ResidueField (v.adicCompletionIntegers F)) p :=
  charP_of_injective_ringHom (f := (residueFieldQuotientRingEquiv v).toRingHom)
    (residueFieldQuotientRingEquiv v).injective p

end IsDedekindDomain.HeightOneSpectrum

end
