/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.TotallyRamifiedResidueField
import Langlands.LubinTateSplittingFieldDegree
import Langlands.LubinTateEisensteinQ

/-!
# `O_{K_1}` has the same residue field as `O`

`ROADMAP.md` `§48` named residue-field preservation for `K_1 / K` as the sole remaining blocker to
the Lubin-Tate tower step `K_1 → K_2`, and expected it to need a fresh `e · f = n` development plus
a re-derivation in a formalism `K_1` does not live in.
`Langlands/TotallyRamifiedResidueField.lean` shows the general fact needs neither; this file
discharges its hypotheses at `K_1` itself.

The two hypotheses of
`LocalField.residueField_map_bijective_of_isUniformizer` are `hram` (total ramification) and `hgen`
(the uniformizer generates), both at the generator `α` produced by
`LubinTate.exists_generator_K_1`:

* `hgen` is `LubinTate.finrank_K_1_eq_residueCard_sub_one` together with `minpoly K α = Qk`
  (`Qk := P.divX.map (algebraMap O K)`, monic and irreducible by
  `Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated`) — the same identification
  `finrank_K_1_eq_residueCard_sub_one`'s own proof makes.
* `hram` is `LubinTate.spectralNorm_eq_of_isLubinTatePoly_root` (`Langlands/LubinTateEisensteinQ.lean`),
  which pins `spectralNorm K (K_1 P) α` to `‖algebraMap O K (P.divX.coeff 0)‖ ^ (1 / (q - 1))`
  *exactly*; raising to the `(q-1)`-st power (`Real.rpow_inv_natCast_pow`) and using that
  `P.divX.coeff 0` is an associate of `π` (`divX_isWeaklyEisensteinAt_and_associated`) turns it into
  `‖algebraMap O K π‖`. **No Newton polygon and no ramification-index bookkeeping is involved** —
  this is the same "run `spectralNorm_eq_norm_coeff_zero_rpow` in reverse" shortcut
  `Langlands/LubinTateEisensteinQ.lean` already found for the root valuation.

## The one hypothesis left explicit: `hϖnorm`

`hram` compares `‖ϖ‖` for a uniformizer `ϖ` of `𝒪[K] := (ValuativeRel.valuation K).valuationSubring`
against `‖algebraMap O K π‖`. This arc's standing hypothesis package relates the abstract `O` to `K`
only through `hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1` and `hπnorm : ‖algebraMap O K π‖ < 1` — which
do **not** force `algebraMap O K π` to be a *uniformizer* of `𝒪[K]` (`hOK` is compatible with `O`'s
image being a proper subring of the closed unit ball; this is `ROADMAP.md`'s long-tracked "gap 3",
restated in `Langlands/LubinTateTowerStep.lean`'s module docstring). So `hϖnorm : ‖(ϖ : K)‖ =
‖algebraMap O K π‖` is taken as an explicit hypothesis here rather than derived, exactly as
`hOK`/`hπnorm` themselves are. At the arc's concrete instantiation (`O := v.adicCompletionIntegers
F`, `K := v.adicCompletion F`) it is discharged by
`IsDedekindDomain.HeightOneSpectrum.valuationSubring_valuation_eq_adicCompletionIntegers`
(`Langlands/LubinTateSplittingFieldDVR.lean`), which identifies `𝒪[K]` with `O` on the nose.

## Main results

* `LubinTate.norm_algebraMap_eq_of_associated` : associates of `O` have equal norms in `K`, given
  `hOK`. (Units of `O` land at norm exactly `1`: both `u` and `u⁻¹` are bounded by `1` and their
  norms multiply to `1`.)
* `LubinTate.minpoly_eq_divX_map_K_1` : `minpoly K α = P.divX.map (algebraMap O K)` for `α` the
  generator of `LubinTate.exists_generator_K_1`.
* `LubinTate.spectralNorm_pow_natDegree_minpoly_K_1` : `spectralNorm K (K_1 P) α ^
  (minpoly K α).natDegree = ‖algebraMap O K π‖` — the `hram` shape, before comparison with `ϖ`.
* `LubinTate.residueField_map_bijective_K_1` and `LubinTate.residueFieldEquiv_K_1` : **the
  headline results.** `IsLocalRing.ResidueField ↥𝒪[K] ≃+* IsLocalRing.ResidueField ↥𝒪_{K_1}`, with
  `𝒪_{K_1} := integralClosure ↥𝒪[K] (K_1 P)`.
-/

noncomputable section

open IsLocalRing ValuativeRel Polynomial PowerSeries

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Algebra O K] [IsFractionRing O K]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsUltrametricDist K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] [IsFractionRing O K] in
/-- **Associates of `O` have equal norms in `K`**, given `hOK`. A unit `v : Oˣ` has
`‖algebraMap O K v‖ = 1`: both `‖algebraMap O K v‖` and `‖algebraMap O K v⁻¹‖` are `≤ 1` by `hOK`
and their product is `‖algebraMap O K 1‖ = 1`. -/
theorem norm_algebraMap_eq_of_associated (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {a b : O}
    (h : Associated a b) : ‖algebraMap O K a‖ = ‖algebraMap O K b‖ := by
  obtain ⟨v, hv⟩ := h
  have hunit : ‖algebraMap O K (v : O)‖ * ‖algebraMap O K ((v⁻¹ : Oˣ) : O)‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, norm_one]
  have h1 : ‖algebraMap O K (v : O)‖ = 1 := by
    nlinarith [hOK (v : O), hOK ((v⁻¹ : Oˣ) : O), norm_nonneg (algebraMap O K (v : O)),
      norm_nonneg (algebraMap O K ((v⁻¹ : Oˣ) : O))]
  rw [← hv, map_mul, norm_mul, h1, mul_one]

variable {π : O} {f : O⟦X⟧} {P : O[X]} {u : O⟦X⟧}

omit [IsUltrametricDist K] [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [CompleteSpace K] [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] in
/-- **`Qk := P.divX.map (algebraMap O K)` is the minimal polynomial of the generator `α`.**
`Qk` is monic and irreducible (`Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated`,
from `divX_isWeaklyEisensteinAt_and_associated`'s sharp Eisenstein data) and `α` is a root, so
`minpoly.eq_of_irreducible_of_monic` applies. This is the identification
`finrank_K_1_eq_residueCard_sub_one`'s own proof makes internally; it is extracted here because
`hram`/`hgen` both need to name `(minpoly K α).natDegree`. -/
theorem minpoly_eq_divX_map_K_1 (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    {α : K_1 (K := K) P} (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0) :
    minpoly K α = P.divX.map (algebraMap O K) := by
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2
  exact (minpoly.eq_of_irreducible_of_monic
    (Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hπ hQmonic hQweak hQdeg hQ0assoc)
    hα (hQmonic.map _)).symm

omit [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] in
/-- **The exact `hram` shape at `K_1`:** `spectralNorm K (K_1 P) α ^ (minpoly K α).natDegree =
‖algebraMap O K π‖`.

`spectralNorm_eq_of_isLubinTatePoly_root` (`Langlands/LubinTateEisensteinQ.lean`) gives
`spectralNorm K (K_1 P) α = ‖algebraMap O K (P.divX.coeff 0)‖ ^ (1 / P.divX.natDegree : ℝ)`
exactly; `minpoly_eq_divX_map_K_1` identifies the exponent `(minpoly K α).natDegree` with
`P.divX.natDegree`; `Real.rpow_inv_natCast_pow` cancels the `rpow`; and
`norm_algebraMap_eq_of_associated` replaces `P.divX.coeff 0` by its associate `π`. This is the
classical "a generator of the `π`-torsion is a uniformizer of `K_1`, and `K_1 / K` is totally
ramified of degree `q - 1`" statement, in the exact form
`LocalField.residueField_map_bijective_of_isUniformizer` consumes. -/
theorem spectralNorm_pow_natDegree_minpoly_K_1
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    {α : K_1 (K := K) P} (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0) :
    spectralNorm K (K_1 (K := K) P) α ^ (minpoly K α).natDegree = ‖algebraMap O K π‖ := by
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2
  have hmin : minpoly K α = P.divX.map (algebraMap O K) :=
    minpoly_eq_divX_map_K_1 hπ hf hu heq hPdist hPdeg hα
  have hdeg : (minpoly K α).natDegree = P.divX.natDegree := by
    rw [hmin, hQmonic.natDegree_map]
  have hspec : spectralNorm K (K_1 (K := K) P) α =
      ‖algebraMap O K (P.divX.coeff 0)‖ ^ (1 / P.divX.natDegree : ℝ) :=
    spectralNorm_eq_of_isLubinTatePoly_root hu heq hf.1 hπ hf.2.1 hPdist hPdeg2 hα
  rw [hdeg, hspec, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hQdeg.ne']
  exact norm_algebraMap_eq_of_associated hOK hQ0assoc

/-- **`ResidueField ↥𝒪[K] → ResidueField ↥𝒪_{K_1}` is bijective**, `𝒪_{K_1} := integralClosure
↥𝒪[K] (K_1 P)`.

Discharges `LocalField.residueField_map_bijective_of_isUniformizer`'s two hypotheses at the
generator `α` of `exists_generator_K_1`: `hram` from `spectralNorm_pow_natDegree_minpoly_K_1`
together with `hϖnorm`, and `hgen` from `minpoly_eq_divX_map_K_1` together with
`finrank_K_1_eq_residueCard_sub_one`. Separability of `K_1 P / K` is not assumed — it comes from
`isGalois_K_1`, which has exactly the same hypothesis package. -/
theorem residueField_map_bijective_K_1
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1)
    (hf : IsLubinTatePoly π (residueCard O) f) (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} (hϖ : Irreducible ϖ)
    (hϖnorm : ‖(ϖ : K)‖ = ‖algebraMap O K π‖) :
    Function.Bijective (ResidueField.map (algebraMap ↥(ValuativeRel.valuation K).valuationSubring
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))) := by
  haveI := isGalois_K_1 (K := K) hOK hπ hπnorm hf hu heq hPdist hPdeg
  haveI : Algebra.IsSeparable K (K_1 (K := K) P) := inferInstance
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, -, -, -⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2
  obtain ⟨α, hαroot, -, -, -⟩ := exists_generator_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg
  have hmin : minpoly K α = P.divX.map (algebraMap O K) :=
    minpoly_eq_divX_map_K_1 hπ hf hu heq hPdist hPdeg hαroot
  have hgen : (minpoly K α).natDegree = Module.finrank K (K_1 (K := K) P) := by
    rw [hmin, hQmonic.natDegree_map, Polynomial.natDegree_divX_eq_natDegree_tsub_one, hPdeg,
      finrank_K_1_eq_residueCard_sub_one hOK hπ hπnorm hf hu heq hPdist hPdeg]
  have hram : ‖(ϖ : K)‖ = spectralNorm K (K_1 (K := K) P) α ^ (minpoly K α).natDegree := by
    rw [hϖnorm, ← spectralNorm_pow_natDegree_minpoly_K_1 hOK hπ hf hu heq hPdist hPdeg hαroot]
  exact LocalField.residueField_map_bijective_of_isUniformizer K hϖ hram hgen

/-- **The residue field of `K_1` is the residue field of `K`**, packaged as a `RingEquiv`. See
`residueField_map_bijective_K_1`. This closes `ROADMAP.md` `§48`'s residue-field-preservation
blocker for the Lubin-Tate tower. -/
def residueFieldEquiv_K_1
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1)
    (hf : IsLubinTatePoly π (residueCard O) f) (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} (hϖ : Irreducible ϖ)
    (hϖnorm : ‖(ϖ : K)‖ = ‖algebraMap O K π‖) :
    ResidueField ↥(ValuativeRel.valuation K).valuationSubring ≃+*
      ResidueField ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) :=
  RingEquiv.ofBijective _
    (residueField_map_bijective_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg hϖ hϖnorm)

end LubinTate
