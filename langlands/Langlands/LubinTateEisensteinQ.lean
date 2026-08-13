import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Langlands.LubinTateWeierstrassPreparation

/-!
# Eisenstein-ness and root valuation of the sharp Weierstrass-preparation factor `Q`

`ROADMAP.md` §31 identified `piTorsion hπ hf 1` with the root set of `P`, the Weierstrass-prep
factor of a Lubin-Tate power series `f`, and showed `P = X * Q` (`P`'s constant term is exactly `0`,
`LubinTateWeierstrassPreparation.coeff_zero_eq_zero_of_eq_mul`) with `Q`'s own constant term an
*associate* of the uniformizer `π` (`LubinTateWeierstrassPreparation.coeff_one_associated_of_eq_mul`,
valuation exactly `1`, not merely `≥ 1`). §31 flagged the classical root-valuation argument for `Q`
(every root has valuation exactly `1/(q-1)`) as needing genuinely new Newton-polygon machinery, since
Mathlib has no Newton polygon development at all.

**This file finds a shortcut, confirmed by direct investigation (not assumed): no Newton polygon is
needed.** Mathlib's `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`
(`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`) is a *completely general* identity — for *any*
`x : L` algebraic over a complete normed field `K`, `spectralNorm K L x = ‖(minpoly K x).coeff 0‖ ^
(1 / (minpoly K x).natDegree : ℝ)` — with no side conditions beyond `x` being a root of its own
minimal polynomial (automatic). `TotallyRamifiedEisenstein.lean` only ever uses this identity in the
*forward* direction (a known totally-ramified hypothesis on `spectralNorm K L π` derives facts about
`(minpoly K π).coeff 0`). Run in *reverse*: if `Q` (a monic polynomial over `O`) is irreducible after
base-changing to `K := Frac(O)`, then for any root `α` of `Q` in an algebraic extension `L / K`,
`minpoly K α` *is* (up to the base change) `Q` itself (`minpoly.eq_of_irreducible_of_monic`), so the
identity directly pins down `spectralNorm K L α` from `Q`'s own constant coefficient — no
Newton-polygon machinery, no bound-from-both-sides ultrametric argument, needed at all. This reduces
the problem entirely to irreducibility of `Q` (over `O`, then over `K` via Gauss's lemma), which in
turn follows from Mathlib's `Polynomial.irreducible_of_eisenstein_criterion` given the sharp
`coeff 0 ∉ 𝔪 ^ 2` hypothesis — itself a direct, general consequence of "associate of a uniformizer"
in any discrete valuation ring (`not_mem_sq_maximalIdeal_of_associated`, proved here, not previously
in Mathlib: `grep -rn "not_mem.*maximalIdeal.*sq\|sq.*not_mem.*maximalIdeal"` in this repo and a
loogle search for "Associated, Irreducible, Ideal.span" both came up empty).

## Main results

* `not_mem_sq_maximalIdeal_of_associated` : general DVR fact, an associate of an irreducible element
  is never in the square of the maximal ideal — the sharp non-membership Eisenstein's criterion needs
  beyond plain "valuation `≥ 1`".
* `Polynomial.irreducible_of_isWeaklyEisensteinAt_associated` : general polynomial-over-a-DVR fact, a
  monic, weakly-Eisenstein-at-`𝔪`, positive-degree polynomial whose constant term is an associate of
  a uniformizer is irreducible (over the DVR itself). Assembles
  `not_mem_sq_maximalIdeal_of_associated` with Mathlib's `irreducible_of_eisenstein_criterion`.
* `Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated` : the same hypotheses, plus
  `[IsFractionRing O K]`, give irreducibility of the base-changed polynomial over `K := Frac(O)` too,
  via Gauss's lemma (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`).
* `spectralNorm_eq_norm_coeff_zero_rpow_of_aeval_eq_zero` : the general, `Q`-independent
  reversal-of-`spectralNorm_eq_norm_coeff_zero_rpow` lemma — for `Qk : K[X]` monic and irreducible,
  any root `α` of `Qk` in an algebraic extension `L` has `spectralNorm K L α = ‖Qk.coeff 0‖ ^
  (1 / Qk.natDegree : ℝ)` exactly. Reusable independent of the Lubin-Tate setting.
* `LubinTate.spectralNorm_eq_of_isLubinTatePoly_root` : specializes the above to `Q := P.divX` for a
  Lubin-Tate Weierstrass factor `P`, giving the exact root valuation the classical argument needs, for
  any root of `Q` in an algebraic extension of `K := Frac(O)`.

## What this does not do

**Separability of `Q`** (§31's step 4, gap 1's *other* half — distinctness of roots, not their
valuation) is not addressed here: the exact common valuation of all roots is necessary but not
sufficient for separability (a repeated root would have the same valuation as a simple one). That
still needs a separate argument (a derivative-valuation estimate, per §31's proof sketch) or a
different route; not attempted in this file.

**The splitting-field hypothesis** (§31's gap 2: `K` is not assumed to contain `Q`'s roots) is
unaffected by this file — `spectralNorm_eq_norm_coeff_zero_rpow_of_aeval_eq_zero` is stated for an
arbitrary algebraic extension `L / K` containing the root `α`, exactly the generality needed to be
combined with a splitting-field construction later, but no such construction is attempted here.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

open Polynomial

/-! ## A general discrete-valuation-ring fact -/

/-- **An associate of an irreducible element never lies in the square of the maximal ideal.**
General fact about any discrete valuation ring `O`: if `a` is an associate of an irreducible `π`
(so `a` has "valuation exactly `1`", not merely `≥ 1`), then `a ∉ 𝔪 ^ 2`. Proof: `𝔪 = span {π}`
(`Irreducible.maximalIdeal_eq`), so `𝔪 ^ 2 = span {π ^ 2}`; if `a = π ^ 2 * c` while also `a * u = π`
for a unit `u` (the definition of `Associated a π`), substituting and cancelling one copy of `π`
(`O` a domain, `π ≠ 0`) gives `π * (c * u) = 1`, i.e. `π` a unit — contradicting `π` irreducible. -/
theorem not_mem_sq_maximalIdeal_of_associated {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {a π : O} (hπ : Irreducible π) (ha : Associated a π) :
    a ∉ IsLocalRing.maximalIdeal O ^ 2 := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  obtain ⟨u, hu⟩ := ha
  apply hπ.not_isUnit
  have heq2 : π * (π * (c * (u : O))) = π * 1 := by
    rw [mul_one]
    calc π * (π * (c * (u : O))) = π ^ 2 * c * (u : O) := by ring
      _ = a * (u : O) := by rw [hc]
      _ = π := hu
  have hcancel : π * (c * (u : O)) = 1 := mul_left_cancel₀ hπ.ne_zero heq2
  exact IsUnit.of_mul_eq_one (c * (u : O)) hcancel

/-! ## Irreducibility of a sharp Eisenstein polynomial over a DVR, and over its fraction field -/

/-- **A monic, weakly-Eisenstein, positive-degree polynomial over a DVR whose constant term is an
associate of a uniformizer is irreducible.** The sharp non-membership `coeff 0 ∉ 𝔪 ^ 2` that
Mathlib's `irreducible_of_eisenstein_criterion` needs beyond plain (weak) Eisenstein-ness comes from
`not_mem_sq_maximalIdeal_of_associated`; the other hypotheses (`leadingCoeff ∉ 𝔪`, `IsPrimitive`)
follow immediately from monic-ness. -/
theorem Polynomial.irreducible_of_isWeaklyEisensteinAt_associated {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {Q : O[X]} {π : O} (hπ : Irreducible π)
    (hQmonic : Q.Monic) (hQweak : Q.IsWeaklyEisensteinAt (IsLocalRing.maximalIdeal O))
    (hQdeg : 0 < Q.natDegree) (hQ0 : Associated (Q.coeff 0) π) : Irreducible Q := by
  apply Polynomial.irreducible_of_eisenstein_criterion
    (IsLocalRing.maximalIdeal.isMaximal O).isPrime
  · rw [hQmonic.leadingCoeff]
    intro h1
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1)
  · intro n hn
    exact hQweak.mem (Polynomial.coe_lt_degree.mp hn)
  · exact Polynomial.natDegree_pos_iff_degree_pos.mp hQdeg
  · exact not_mem_sq_maximalIdeal_of_associated hπ hQ0
  · exact hQmonic.isPrimitive

/-- **The same polynomial, base-changed to `K := Frac(O)`, is also irreducible.** Gauss's lemma
(`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`, using that a discrete valuation
ring is integrally closed) transports `Polynomial.irreducible_of_isWeaklyEisensteinAt_associated`'s
conclusion from `O[X]` to `K[X]`. -/
theorem Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {K : Type*} [Field K] [Algebra O K]
    [IsFractionRing O K] {Q : O[X]} {π : O} (hπ : Irreducible π) (hQmonic : Q.Monic)
    (hQweak : Q.IsWeaklyEisensteinAt (IsLocalRing.maximalIdeal O)) (hQdeg : 0 < Q.natDegree)
    (hQ0 : Associated (Q.coeff 0) π) : Irreducible (Q.map (algebraMap O K)) := by
  have hQirr : Irreducible Q :=
    Polynomial.irreducible_of_isWeaklyEisensteinAt_associated hπ hQmonic hQweak hQdeg hQ0
  haveI : UniqueFactorizationMonoid O := PrincipalIdealRing.to_uniqueFactorizationMonoid (R := O)
  exact (hQmonic.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hQirr

/-! ## The general spectralNorm-of-root reversal -/

/-- **The exact spectral norm of a root of an irreducible monic polynomial**, reading Mathlib's
`spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` in reverse: given `Qk : K[X]` monic and
irreducible and `α : L` a root of `Qk` (`aeval α Qk = 0`) in an algebraic extension `L / K`,
`Qk` *is* the minimal polynomial of `α` over `K` (`minpoly.eq_of_irreducible_of_monic`), so the
general identity pins `spectralNorm K L α` down exactly from `Qk`'s own constant coefficient. No
Newton-polygon or two-sided-bound argument is needed: this is a direct corollary of the general
identity, valid for *any* algebraic `x : L`, run at `x := α` after identifying `minpoly K α = Qk`. -/
theorem spectralNorm_eq_norm_coeff_zero_rpow_of_aeval_eq_zero {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {L : Type*} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] {Qk : K[X]}
    (hQkirr : Irreducible Qk) (hQkmonic : Qk.Monic) {α : L} (hα : Polynomial.aeval α Qk = 0) :
    spectralNorm K L α = ‖Qk.coeff 0‖ ^ (1 / Qk.natDegree : ℝ) := by
  have hmin : Qk = minpoly K α := minpoly.eq_of_irreducible_of_monic hQkirr hα hQkmonic
  rw [hmin]
  exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L α

/-! ## Specialization to the Lubin-Tate Weierstrass factor -/

namespace LubinTate

open PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **`Q := P.divX` is monic, weakly Eisenstein at `𝔪`, of positive degree, with constant term an
associate of `π`** — exactly the hypotheses
`Polynomial.irreducible_of_isWeaklyEisensteinAt_associated` needs, assembled from `P`'s own
`IsDistinguishedAt` data (`hPdist`), `coeff_zero_eq_zero_of_eq_mul` (`P`'s constant term is `0`, so
`P = X * Q` via `Polynomial.X_mul_divX_add`), and `coeff_one_associated_of_eq_mul` (`Q`'s constant
term `Q.coeff 0 = P.coeff 1` is an associate of `π`). `hPdeg2 : 2 ≤ P.natDegree` (true for `P.natDegree
= residueCard O ≥ 2`, any residue field having at least two elements) ensures `Q.natDegree ≥ 1`. -/
theorem divX_isWeaklyEisensteinAt_and_associated {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) {f : O⟦X⟧}
    (heq : f = (P : O⟦X⟧) * u) (hf0 : PowerSeries.coeff 0 f = 0) {π : O} (hf1 : PowerSeries.coeff 1 f = π)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree) :
    P.divX.Monic ∧ P.divX.IsWeaklyEisensteinAt (maximalIdeal O) ∧ 0 < P.divX.natDegree ∧
      Associated (P.divX.coeff 0) π := by
  have hP0 : P.coeff 0 = 0 := coeff_zero_eq_zero_of_eq_mul hu heq hf0
  have hP1assoc : Associated (P.coeff 1) π := coeff_one_associated_of_eq_mul hu heq hf0 hf1
  have hPdeg1 : 1 ≤ P.natDegree := le_trans (by norm_num) hPdeg2
  have hdegQ : P.divX.natDegree = P.natDegree - 1 :=
    Polynomial.natDegree_divX_eq_natDegree_tsub_one
  have hcoeffQ : ∀ n, P.divX.coeff n = P.coeff (n + 1) := fun n => Polynomial.coeff_divX
  refine ⟨?_, ⟨?_⟩, ?_, ?_⟩
  · -- `P.divX` is monic.
    show P.divX.coeff P.divX.natDegree = 1
    rw [hcoeffQ, hdegQ, Nat.sub_add_cancel hPdeg1]
    exact hPdist.monic
  · -- `P.divX` is weakly Eisenstein at `𝔪`.
    intro n hn
    rw [hdegQ] at hn
    rw [hcoeffQ]
    exact hPdist.toIsWeaklyEisensteinAt.mem
      (show n + 1 < P.natDegree by omega)
  · -- `0 < P.divX.natDegree`.
    rw [hdegQ]; omega
  · -- `P.divX.coeff 0` is an associate of `π`.
    rw [hcoeffQ]; exact hP1assoc

/-- **The exact valuation of a root of `Q := P.divX`, `P` the Weierstrass factor of a Lubin-Tate
power series `f`.** Combines `divX_isWeaklyEisensteinAt_and_associated` (`Q`'s sharp Eisenstein data),
`Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated` (irreducibility of `Q` over
`K := Frac(O)`, given `[IsFractionRing O K]`), and
`spectralNorm_eq_norm_coeff_zero_rpow_of_aeval_eq_zero` (the general spectralNorm-of-root reversal):
for any root `α` of `Q.map (algebraMap O K)` in an algebraic extension `L / K`,
`spectralNorm K L α` is pinned down exactly by `Q`'s own constant coefficient. This is the sharp
root-valuation fact `ROADMAP.md` §31's classical Newton-polygon argument was expected to need — no
Newton polygon required. -/
theorem spectralNorm_eq_of_isLubinTatePoly_root {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) {f : O⟦X⟧}
    (heq : f = (P : O⟦X⟧) * u) (hf0 : PowerSeries.coeff 0 f = 0) {π : O}
    (hπ : Irreducible π) (hf1 : PowerSeries.coeff 1 f = π)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
    [IsFractionRing O K] {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {α : L} (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0) :
    spectralNorm K L α =
      ‖algebraMap O K (P.divX.coeff 0)‖ ^ (1 / P.divX.natDegree : ℝ) := by
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  have hQirr : Irreducible (P.divX.map (algebraMap O K)) :=
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hπ hQmonic hQweak hQdeg hQ0assoc
  have hQKmonic : (P.divX.map (algebraMap O K)).Monic := hQmonic.map _
  have hkey := spectralNorm_eq_norm_coeff_zero_rpow_of_aeval_eq_zero hQirr hQKmonic hα
  rwa [Polynomial.coeff_map, Polynomial.natDegree_map_eq_of_injective
    (IsFractionRing.injective O K)] at hkey

end LubinTate

end
