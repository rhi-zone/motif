import Langlands.LubinTateRootCount
import Langlands.NormMapResidueCompatibility
import Langlands.PrincipalUnitsSuccessiveApproximation
import Langlands.AdicCompletionIntegersResidue

/-!
# The concrete instantiation: `O := v.adicCompletionIntegers F`, `K := v.adicCompletion F`

`Langlands.LubinTate.card_piTorsion_one_eq_residueCard` (`Langlands/LubinTateRootCount.lean`) is
stated against this repo's *abstract* Lubin-Tate typeclass package (`[NormedField K]
[IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsFractionRing O K]` on a complete DVR `O`
with finite residue field), and needs two hypotheses that abstract package cannot supply on its
own: `hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1` and `hπnorm : ‖algebraMap O K π‖ < 1`.

This file supplies the missing wiring: no caller anywhere in the repo had instantiated `O`/`K`
against a concrete `HeightOneSpectrum`/`adicCompletion` pair before. Doing so — `O :=
v.adicCompletionIntegers F`, `K := v.adicCompletion F`, for `v` a place of a Dedekind domain `A`
with fraction field `F` — makes both hypotheses free:

* `hOK` is immediate from `Valued.toNormedField.norm_le_one_iff` and membership in
  `v.adicCompletionIntegers F` (`norm_algebraMap_adicCompletionIntegers_le_one`).
* `hπnorm` is exactly `IsDedekindDomain.HeightOneSpectrum.norm_algebraMap_adicCompletion_uniformizer_lt_one`
  (`Langlands/PrincipalUnitsSuccessiveApproximation.lean`), which despite being stated inside a
  two-field-tower variable block (`R S K L`, `v w`) only actually depends on the single-field data
  `R`/`K`/`v`/`π` — confirmed by its use elsewhere in the repo with exactly those explicit
  arguments, and here by direct application with no `S`/`L`/`w` ever chosen.

The one genuine gap the abstract package's typeclasses do not close by themselves is
`Finite (ResidueField O)`: it is not automatic from `O := v.adicCompletionIntegers F` alone (a
Dedekind domain's height-one quotients need not be finite in general, e.g. function fields over an
infinite field), so it is supplied here as the natural hypothesis `Finite (A ⧸ v.asIdeal)`,
transported across `Langlands.AdicCompletionIntegersResidue.residueFieldQuotientRingEquiv` (the
"residue field does not change under completion" fact,
`(A ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers F)`).

## Main results

* `norm_algebraMap_adicCompletionIntegers_le_one` : `hOK`, free of any finiteness hypothesis.
* `instFiniteResidueFieldAdicCompletionIntegers` : `Finite (ResidueField (v.adicCompletionIntegers
  F))`, given `Finite (A ⧸ v.asIdeal)`.
* `card_piTorsion_one_eq_residueCard_of_adicCompletion` : the concrete instantiation of
  `LubinTate.card_piTorsion_one_eq_residueCard` at `O := v.adicCompletionIntegers F`, `K :=
  v.adicCompletion F` — `hOK` and `hπnorm` are discharged automatically, leaving only the
  genuinely-structural hypotheses (`Finite (A ⧸ v.asIdeal)`, the Weierstrass-factorization data,
  and `hsplit`) explicit.
-/

noncomputable section

open IsDedekindDomain IsLocalRing PowerSeries

open scoped Polynomial

namespace IsDedekindDomain.HeightOneSpectrum

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- **`hOK` is free at the concrete `adicCompletionIntegers`/`adicCompletion` pair.** Every `c :
v.adicCompletionIntegers F` has norm `≤ 1` in `v.adicCompletion F`: `algebraMap
(v.adicCompletionIntegers F) (v.adicCompletion F)` is literally the subtype coercion, and
`c ∈ v.adicCompletionIntegers F` unfolds to `Valued.v (c : v.adicCompletion F) ≤ 1`. -/
theorem norm_algebraMap_adicCompletionIntegers_le_one (c : v.adicCompletionIntegers F) :
    ‖(algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) c : v.adicCompletion F)‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr ((mem_adicCompletionIntegers A F v).mp c.2)

/-- **`Finite (ResidueField O)` at `O := v.adicCompletionIntegers F`**, given the natural
hypothesis `Finite (A ⧸ v.asIdeal)`: completion at `v` does not change the residue field
(`residueFieldQuotientRingEquiv`), so finiteness transports across that equivalence. -/
instance instFiniteResidueFieldAdicCompletionIntegers [Finite (A ⧸ v.asIdeal)] :
    Finite (ResidueField (v.adicCompletionIntegers F)) :=
  Finite.of_equiv _ (v.residueFieldQuotientRingEquiv (F := F)).toEquiv

/-- **The concrete instantiation of `LubinTate.card_piTorsion_one_eq_residueCard`**, at
`O := v.adicCompletionIntegers F`, `K := v.adicCompletion F`. `hOK` and `hπnorm` — the two
hypotheses left open in `Langlands/LubinTateRootCount.lean` because the abstract `O`/`K` package
alone cannot supply them — are both discharged automatically here
(`norm_algebraMap_adicCompletionIntegers_le_one`,
`norm_algebraMap_adicCompletion_uniformizer_lt_one`); only the genuinely-structural data remains
explicit: `Finite (A ⧸ v.asIdeal)`, the Weierstrass factorization `f = P * u`, and `hsplit`. -/
theorem card_piTorsion_one_eq_residueCard_of_adicCompletion [Finite (A ⧸ v.asIdeal)]
    {π : v.adicCompletionIntegers F} (hπ : Irreducible π)
    {f : (v.adicCompletionIntegers F)⟦X⟧}
    (hf : LubinTate.IsLubinTatePoly π (LubinTate.residueCard (v.adicCompletionIntegers F)) f)
    {P : (v.adicCompletionIntegers F)[X]} {u : (v.adicCompletionIntegers F)⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : (v.adicCompletionIntegers F)⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal (v.adicCompletionIntegers F)))
    (hPdeg : P.natDegree = LubinTate.residueCard (v.adicCompletionIntegers F))
    (hsplit : (P.divX.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).Splits) :
    Nat.card (LubinTate.piTorsion (K := v.adicCompletion F) hπ hf 1) =
      LubinTate.residueCard (v.adicCompletionIntegers F) :=
  LubinTate.card_piTorsion_one_eq_residueCard (norm_algebraMap_adicCompletionIntegers_le_one v)
    hπ (norm_algebraMap_adicCompletion_uniformizer_lt_one F v hπ) hf hu heq hPdist hPdeg hsplit

end IsDedekindDomain.HeightOneSpectrum

end
