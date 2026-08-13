import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Separable
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
* `Polynomial.aeval_derivative_ne_zero_of_isEisensteinAt_of_natDegree_norm_eq_one` : the tame-
  ramification separability criterion, general `K[X]`-level form — a monic irreducible `Qk : K[X]`
  Eisenstein-shaped with a *sharp* constant-term norm `c` (`0 < c < 1`) and a *tame* degree (its
  image in `K` has norm exactly `1`) has every root `α` (in any algebraic extension `L`) as a
  *simple* root, `Polynomial.aeval α Qk.derivative ≠ 0`. The classical derivative-valuation argument
  §32 sketched, closed via `spectralNorm`'s power law (`isPowMul_spectralNorm`) and the finite-sum
  ultrametric domination lemma `IsNonarchimedean.apply_sum_eq_of_lt`.
* `Polynomial.separable_of_isEisensteinAt_of_natDegree_norm_eq_one` : the same hypotheses conclude
  `Qk.Separable` directly, via Mathlib's `Polynomial.separable_iff_derivative_ne_zero` (no
  characteristic assumption).
* `LubinTate.separable_map_of_isWeaklyEisensteinAt_associated` : the `O`-level bridge from `Q`'s
  Eisenstein-with-associate-constant-term data (plus a "tame degree" hypothesis `IsUnit
  (Q.natDegree : O)`, and `‖algebraMap O K π‖ < 1`) down to `Polynomial.Separable`.
* `LubinTate.separable_map_divX_of_isLubinTatePoly` : specializes the bridge to `Q := P.divX`,
  reusing `divX_isWeaklyEisensteinAt_and_associated` exactly as `spectralNorm_eq_of_isLubinTatePoly_root`
  does. **This closes §32's separability gap** — the tame-ramification route it identified but did
  not attempt — given the two hypotheses `IsUnit (P.divX.natDegree : O)` and `‖algebraMap O K π‖ < 1`
  (both true in the concrete Lubin-Tate application but not derived here; no caller needing the
  concrete instantiation exists yet, matching `hPdeg2`'s existing convention).

## What this does not do

**The splitting-field hypothesis** (§31's gap 2: `K` is not assumed to contain `Q`'s roots) is
unaffected by this file — every theorem here is stated for an arbitrary algebraic extension `L / K`
containing a root `α`, exactly the generality needed to be combined with a splitting-field
construction later, but no such construction is attempted here.

**Deriving `IsUnit (P.divX.natDegree : O)` from `residueCard O` being a prime power**, and deriving
`‖algebraMap O K π‖ < 1` from `hOK`/`hπ` (this needs a genuinely separate fact — `hOK`'s uniform
`≤ 1` bound does not by itself force a *nonunit* of `O` to land at norm *strictly* less than `1`) —
neither is attempted; both are left as explicit hypotheses to `separable_map_divX_of_isLubinTatePoly`.
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

/-! ## Separability via tame ramification -/

open scoped NNReal

/-- **Tame-ramification separability criterion, general form.** Let `Qk : K[X]` be monic and
irreducible, with constant coefficient of norm exactly `c` (`0 < c < 1`) and every other
coefficient (`i < Qk.natDegree`) of norm `≤ c` — i.e. `Qk` is Eisenstein-shaped with a *sharp*
constant term. If `Qk.natDegree` is "tame" (its image in `K` has norm exactly `1`, automatic when
`Qk.natDegree` is coprime to the residue characteristic), then every root `α` of `Qk` in an
algebraic extension `L / K` is a *simple* root: `Polynomial.aeval α Qk.derivative ≠ 0`.

Proof sketch (the classical tame-ramification derivative argument): by
`spectralNorm_eq_norm_coeff_zero_rpow_of_aeval_eq_zero`, `spectralNorm K L α = c ^ (1/n : ℝ)` exactly
(`n := Qk.natDegree`), hence `spectralNorm K L (α ^ m) = c ^ (m/n : ℝ)` for every `m` (`isPowMul_spectralNorm`).
Writing `Qk.derivative`'s evaluation at `α` as the sum `∑ m ∈ range n, (Qk.derivative).coeff m • α ^ m`
(valid since `Qk.derivative.natDegree = n - 1` exactly, using `(Qk.derivative).coeff (n-1) = (n : K) ≠ 0`
from monic-ness and tameness), the `m = n - 1` term has `spectralNorm` *exactly* `c ^ ((n-1)/n : ℝ)`
(tameness gives `‖(n:K)‖ = 1`), while every other term `m < n - 1` has `spectralNorm ≤ c ^ ((n+m)/n : ℝ)
< c ^ ((n-1)/n : ℝ)` strictly (using `‖Qk.coeff (m+1)‖ ≤ c`, `‖(m+1:K)‖ ≤ 1` from
`IsUltrametricDist.norm_natCast_le_one`, and `c < 1` making `x ↦ c ^ x` strictly antitone). The
finite-sum ultrametric domination lemma `IsNonarchimedean.apply_sum_eq_of_lt` then gives
`spectralNorm K L (aeval α Qk.derivative) = spectralNorm K L ((n:K) • α ^ (n-1)) = c ^ ((n-1)/n : ℝ) ≠ 0`,
so `aeval α Qk.derivative ≠ 0` (contrapositive of `spectralNorm_zero`). -/
theorem Polynomial.aeval_derivative_ne_zero_of_isEisensteinAt_of_natDegree_norm_eq_one
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {Qk : K[X]} (hQkmonic : Qk.Monic) (hQkirr : Irreducible Qk)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hc0eq : ‖Qk.coeff 0‖ = c)
    (hQkweak : ∀ i < Qk.natDegree, ‖Qk.coeff i‖ ≤ c)
    (hn1 : ‖(Qk.natDegree : K)‖ = 1)
    {α : L} (hα : Polynomial.aeval α Qk = 0) :
    Polynomial.aeval α (Polynomial.derivative Qk) ≠ 0 := by
  set n := Qk.natDegree with hndef
  have hnpos : 0 < n := hQkirr.natDegree_pos
  have hnval : spectralNorm K L α = c ^ (1 / n : ℝ) := by
    rw [← hc0eq]
    exact spectralNorm_eq_norm_coeff_zero_rpow_of_aeval_eq_zero hQkirr hQkmonic hα
  -- The power law: `spectralNorm K L (α ^ m) = c ^ (m / n : ℝ)` for every `m`.
  have hpow : ∀ m : ℕ, spectralNorm K L (α ^ m) = c ^ ((m : ℝ) / n) := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hm1
    · subst hm0; simp [spectralNorm_one]
    · rw [isPowMul_spectralNorm α hm1, hnval, ← Real.rpow_natCast (c ^ (1 / n : ℝ)) m,
        ← Real.rpow_mul hc0.le]
      congr 1
      ring
  have hne0 : (n : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn1; norm_num at hn1
  have hnn : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hnpos
  -- The top coefficient of the derivative is exactly `n`.
  have hdcoeff : (Polynomial.derivative Qk).coeff (n - 1) = (n : K) := by
    have hQkn : Qk.coeff n = 1 := by
      rw [hndef, Polynomial.coeff_natDegree]; exact hQkmonic
    rw [Polynomial.coeff_derivative, hnn, hQkn, one_mul]
    conv_rhs => rw [← hnn]
    push_cast
    ring
  have hdnatDegree : (Polynomial.derivative Qk).natDegree = n - 1 :=
    le_antisymm (Polynomial.natDegree_derivative_le Qk)
      (Polynomial.le_natDegree_of_ne_zero (by rw [hdcoeff]; exact hne0))
  have hsum : Polynomial.aeval α (Polynomial.derivative Qk)
      = ∑ m ∈ Finset.range n, (Polynomial.derivative Qk).coeff m • α ^ m := by
    rw [Polynomial.aeval_eq_sum_range, hdnatDegree, hnn]
  have hαalg : ∀ m : ℕ, IsAlgebraic K (α ^ m) := fun m => Algebra.IsAlgebraic.isAlgebraic (α ^ m)
  -- The leading term's spectral norm, exactly.
  have hleadnorm : spectralNorm K L ((Polynomial.derivative Qk).coeff (n - 1) • α ^ (n - 1)) =
      c ^ (((n : ℝ) - 1) / n) := by
    rw [spectralNorm_smul _ (hαalg (n - 1)), hdcoeff, coe_nnnorm, hn1, hpow (n - 1), one_mul]
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hnpos]; norm_num
    rw [this]
  have hleadpos : 0 < c ^ (((n : ℝ) - 1) / n) := Real.rpow_pos_of_pos hc0 _
  -- Every other term is strictly smaller.
  have hmax : ∀ j ∈ Finset.range n, j ≠ n - 1 →
      spectralNorm K L ((Polynomial.derivative Qk).coeff j • α ^ j) <
        spectralNorm K L ((Polynomial.derivative Qk).coeff (n - 1) • α ^ (n - 1)) := by
    intro j hj hjne
    rw [Finset.mem_range] at hj
    have hjlt : j < n - 1 := by omega
    have hj1lt : j + 1 < n := by omega
    have hdcoeffj : (Polynomial.derivative Qk).coeff j = Qk.coeff (j + 1) * ((j : K) + 1) := by
      rw [Polynomial.coeff_derivative]
    rw [hleadnorm, spectralNorm_smul _ (hαalg j), coe_nnnorm, hdcoeffj, hpow j]
    have hbound : ‖Qk.coeff (j + 1) * ((j : K) + 1)‖ ≤ c := by
      calc ‖Qk.coeff (j + 1) * ((j : K) + 1)‖
          = ‖Qk.coeff (j + 1)‖ * ‖(j : K) + 1‖ := norm_mul _ _
        _ ≤ c * 1 := by
            apply mul_le_mul (hQkweak (j + 1) hj1lt) _ (norm_nonneg _) hc0.le
            have : ((j : K) + 1) = ((j + 1 : ℕ) : K) := by push_cast; ring
            rw [this]
            exact IsUltrametricDist.norm_natCast_le_one K (j + 1)
        _ = c := mul_one c
    have hstep : ‖Qk.coeff (j + 1) * ((j : K) + 1)‖ * c ^ ((j : ℝ) / n) ≤
        c * c ^ ((j : ℝ) / n) :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hc0.le _)
    have hcpow : c * c ^ ((j : ℝ) / n) = c ^ ((1 : ℝ) + (j : ℝ) / n) := by
      nth_rewrite 1 [← Real.rpow_one c]
      rw [← Real.rpow_add hc0]
    have hexp : (((n : ℝ) - 1) / n) < (1 : ℝ) + (j : ℝ) / n := by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      rw [div_lt_iff₀ hn0, add_mul, one_mul, div_mul_cancel₀ _ hn0.ne']
      linarith
    have hstrict : c ^ ((1 : ℝ) + (j : ℝ) / n) < c ^ (((n : ℝ) - 1) / n) :=
      Real.rpow_lt_rpow_of_exponent_gt hc0 hc1 hexp
    calc ‖Qk.coeff (j + 1) * ((j : K) + 1)‖ * c ^ ((j : ℝ) / n)
        ≤ c * c ^ ((j : ℝ) / n) := hstep
      _ = c ^ ((1 : ℝ) + (j : ℝ) / n) := hcpow
      _ < c ^ (((n : ℝ) - 1) / n) := hstrict
  have hkmem : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (Nat.sub_lt hnpos one_pos)
  have hf_neg : ∀ a : L, spectralNorm K L a = spectralNorm K L (-a) := fun a =>
    (spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic a)).symm
  have hdom := IsNonarchimedean.apply_sum_eq_of_lt isNonarchimedean_spectralNorm hf_neg hkmem hmax
  rw [← hsum] at hdom
  intro hcontra
  rw [hcontra, spectralNorm_zero, hleadnorm] at hdom
  exact hleadpos.ne' hdom.symm

/-- **Tame-ramification separability, general form (`Polynomial.Separable` conclusion).** Same
hypotheses as `Polynomial.aeval_derivative_ne_zero_of_isEisensteinAt_of_natDegree_norm_eq_one`,
concluding `Qk.Separable` directly via Mathlib's `Polynomial.separable_iff_derivative_ne_zero`
(valid for an irreducible polynomial over *any* field, no characteristic-zero assumption). Only
the existence of *one* root `α` (in *some* algebraic extension `L`) is needed: `Qk.derivative ≠ 0`
is a fact about `Qk` alone, and a single nonzero evaluation of it already forces the whole
polynomial `Qk.derivative` to be nonzero. -/
theorem Polynomial.separable_of_isEisensteinAt_of_natDegree_norm_eq_one
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {Qk : K[X]} (hQkmonic : Qk.Monic) (hQkirr : Irreducible Qk)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hc0eq : ‖Qk.coeff 0‖ = c)
    (hQkweak : ∀ i < Qk.natDegree, ‖Qk.coeff i‖ ≤ c)
    (hn1 : ‖(Qk.natDegree : K)‖ = 1)
    {α : L} (hα : Polynomial.aeval α Qk = 0) :
    Qk.Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero hQkirr]
  intro hzero
  exact (Polynomial.aeval_derivative_ne_zero_of_isEisensteinAt_of_natDegree_norm_eq_one
    hQkmonic hQkirr hc0 hc1 hc0eq hQkweak hn1 hα) (by rw [hzero]; simp)

/-! ## Specialization: separability of `Q := P.divX`, given a tame-degree hypothesis -/

namespace LubinTate

open PowerSeries IsLocalRing

/-- **The `O`-level bridge from Eisenstein-with-associate-constant-term data to `Polynomial.Separable`.**
Bridges `Q : O[X]`'s Eisenstein data (`hQweak`, `hQ0`) and the "tame degree" hypothesis
(`hQn : IsUnit (Q.natDegree : O)`, the discrete-valuation-ring analogue of "coprime to the residue
characteristic") down to `Polynomial.separable_of_isEisensteinAt_of_natDegree_norm_eq_one`'s
`K`-level hypotheses:

* `‖(Q.map (algebraMap O K)).coeff 0‖ = ‖algebraMap O K π‖` exactly, via `Associated (Q.coeff 0) π`
  and `norm_algebraMap_eq_one_of_isUnit` (the unit witnessing the associate-ness has norm `1`).
* `‖(Q.map (algebraMap O K)).coeff i‖ ≤ ‖algebraMap O K π‖` for `i < natDegree`, via
  `Q.coeff i ∈ 𝔪 = span {π}` (`hQweak.mem`, `hπ.maximalIdeal_eq`) and `hOK`.
* `‖((Q.map (algebraMap O K)).natDegree : K)‖ = 1`, via `hQn` and `norm_algebraMap_eq_one_of_isUnit`
  again (applied to the unit `(Q.natDegree : O)`), using `map_natCast` to identify the two casts of
  `Q.natDegree` (once via `O` and `algebraMap O K`, once directly into `K`).

Needs `‖algebraMap O K π‖ < 1` (`hπnorm`) as an explicit hypothesis: `hOK` alone (a uniform bound
`≤ 1` on all of `O`) does not, by itself, force a *nonunit* of `O` to land at norm *strictly* less
than `1` — that is exactly the "the embedding `O ↪ K` is valuation-compatible, not merely bounded"
content, and is assumed explicitly here, matching the convention of `hπnorm`/`hπ0`-style hypotheses
elsewhere in this repo (e.g. `Langlands.NonarchimedeanExponentialUnitsFiltration`). -/
theorem separable_map_of_isWeaklyEisensteinAt_associated {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsFractionRing O K]
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {Q : O[X]} {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) (hQmonic : Q.Monic)
    (hQweak : Q.IsWeaklyEisensteinAt (maximalIdeal O)) (hQdeg : 0 < Q.natDegree)
    (hQ0 : Associated (Q.coeff 0) π) (hQn : IsUnit ((Q.natDegree : O)))
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {α : L} (hα : Polynomial.aeval α (Q.map (algebraMap O K)) = 0) :
    (Q.map (algebraMap O K)).Separable := by
  have hQirr : Irreducible (Q.map (algebraMap O K)) :=
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hπ hQmonic hQweak hQdeg hQ0
  have hQKmonic : (Q.map (algebraMap O K)).Monic := hQmonic.map _
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hdegeq : (Q.map (algebraMap O K)).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj Q
  set c := ‖algebraMap O K π‖ with hcdef
  have hc0 : 0 < c := by
    rw [hcdef, norm_pos_iff]
    exact (map_ne_zero_iff (algebraMap O K) hinj).mpr hπ.ne_zero
  have hc0eq : ‖(Q.map (algebraMap O K)).coeff 0‖ = c := by
    rw [Polynomial.coeff_map]
    obtain ⟨u, hu⟩ := hQ0
    have : algebraMap O K (Q.coeff 0) * algebraMap O K (u : O) = algebraMap O K π := by
      rw [← map_mul, hu]
    have hunorm : ‖algebraMap O K (u : O)‖ = 1 := norm_algebraMap_eq_one_of_isUnit hOK u.isUnit
    have hthis := congrArg norm this
    rw [norm_mul, hunorm, mul_one] at hthis
    exact hthis
  have hQkweak : ∀ i < (Q.map (algebraMap O K)).natDegree,
      ‖(Q.map (algebraMap O K)).coeff i‖ ≤ c := by
    intro i hi
    rw [hdegeq] at hi
    rw [Polynomial.coeff_map]
    have hmem : Q.coeff i ∈ maximalIdeal O := hQweak.mem hi
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    rw [hy, map_mul, norm_mul, hcdef]
    calc ‖algebraMap O K π‖ * ‖algebraMap O K y‖ ≤ ‖algebraMap O K π‖ * 1 := by
          apply mul_le_mul_of_nonneg_left (hOK y) (norm_nonneg _)
      _ = ‖algebraMap O K π‖ := mul_one _
  have hn1 : ‖((Q.map (algebraMap O K)).natDegree : K)‖ = 1 := by
    rw [hdegeq, ← map_natCast (algebraMap O K) Q.natDegree]
    exact norm_algebraMap_eq_one_of_isUnit hOK hQn
  have hc1 : c < 1 := hπnorm
  exact Polynomial.separable_of_isEisensteinAt_of_natDegree_norm_eq_one
    hQKmonic hQirr hc0 hc1 hc0eq hQkweak hn1 hα

/-- **Separability of `Q := P.divX`, given `P.divX`'s degree is tame.** Specializes
`separable_map_of_isWeaklyEisensteinAt_associated` to `Q := P.divX` for a Lubin-Tate Weierstrass
factor `P`, reusing `divX_isWeaklyEisensteinAt_and_associated` for `Q`'s Eisenstein data exactly as
`spectralNorm_eq_of_isLubinTatePoly_root` does. `hQn : IsUnit ((P.divX.natDegree : O))` (the "tame
degree" condition) and `hπnorm : ‖algebraMap O K π‖ < 1` are left as explicit hypotheses: for the
concrete Lubin-Tate application `P.divX.natDegree = residueCard O - 1`, `hQn` is automatically true
(its residue-field image is `-1 ≠ 0`, since `residueCard O` is a prime power), but no caller needing
that concrete instantiation exists yet, so deriving it is left to a future pass — matching
`divX_isWeaklyEisensteinAt_and_associated`'s existing `hPdeg2` convention of taking a fact that is
always true in the intended application as an explicit hypothesis rather than re-deriving it here. -/
theorem separable_map_divX_of_isLubinTatePoly {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) {f : O⟦X⟧}
    (heq : f = (P : O⟦X⟧) * u) (hf0 : PowerSeries.coeff 0 f = 0) {π : O}
    (hπ : Irreducible π) (hf1 : PowerSeries.coeff 1 f = π)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
    [IsFractionRing O K] (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hπnorm : ‖algebraMap O K π‖ < 1) (hQn : IsUnit ((P.divX.natDegree : O)))
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {α : L} (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0) :
    (P.divX.map (algebraMap O K)).Separable := by
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  exact separable_map_of_isWeaklyEisensteinAt_associated hOK hπ hπnorm hQmonic hQweak hQdeg
    hQ0assoc hQn hα

end LubinTate

end
