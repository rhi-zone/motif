import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Towards Eisenstein-ness of the minimal polynomial of a uniformizer

## Scope (status as of this pass)

This file is a **partial** step towards
`LocalField.isEisensteinAt_minpoly_of_isUniformizer` (the theorem that a uniformizer of a
totally ramified extension of complete/Henselian DVRs has an Eisenstein minimal polynomial),
scoped in `ROADMAP.md` Phase 2b's thirteenth pass and `langlands/Langlands/RamificationFiltration.lean`'s
`## Scope` section.

What is proved here, in full and without `sorry`:

* `spectralValue_coeff_le` : for a monic-or-not `p : R[X]` over a `NormedDivisionRing R` and
  `n < p.natDegree`, `‖p.coeff n‖ ≤ spectralValue p ^ (p.natDegree - n)`. This is the coefficient
  bound obtained by unfolding `spectralValue p := iSup (spectralValueTerms p)`: since
  `spectralValueTerms p n = ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ))` is bounded above by the
  `iSup`, raising both sides to the `(p.natDegree - n)`-th power gives the claim. Not previously
  packaged in Mathlib as a standalone lemma (only the weaker `n`-independent boundary statement
  `spectralValue_le_one_iff` exists, for the `≤ 1` case).
* `spectralNorm_coeff_lt_one` : the corollary for `spectralNorm K L x := spectralValue (minpoly K x)`,
  `x : L`: if `spectralNorm K L x < 1`, every non-leading coefficient of `minpoly K x` has norm
  `< 1` strictly (not just `≤ 1`), the sharper bound Eisenstein-ness needs for its `mem` field.

## What remains (the genuine gap, precisely)

The full theorem needs two further pieces, **neither built in this pass**:

1. **Connecting a concrete uniformizer of a `ValuationSubring A` of `L` to
   `spectralNorm K L π < 1`.** This is formal given the machinery already in
   `Langlands.HenselianValuation` (`exists_rankOne_absoluteValue_extends`,
   `spectralNorm_unique_field_norm_ext`) plus the `IsNonarchimedeanLocalField K → NormedField K`
   instance-construction block already written out at
   `Langlands/HenselianValuation.lean:715-732`
   (`valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField`) — but assembling it into a
   standalone lemma, and separately establishing `f π ≠ 1` from `π` being a non-unit of `A`
   (via `ValuationSubring.mem_nonunits_iff_or`/`coe_mem_nonunits_iff`, both confirmed present in
   `Mathlib/RingTheory/Valuation/ValuationSubring.lean`), was not done this pass.
2. **Converting the resulting real-number bound/equality on `‖(minpoly K π).coeff 0‖` into the
   ideal-power statement `(minpoly K π).coeff 0 ∉ 𝔪_K ^ 2`** that `Polynomial.IsEisensteinAt.notMem`
   needs. This is the step the twelfth/thirteenth-pass docstrings did not resolve. Confirmed present
   this pass (via loogle, query `IsDiscreteValuationRing, maximalIdeal, pow`):
   `Valuation.integer.integers.maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow` and its
   `ValuationSubring`-flavored corollary
   `Irreducible.maximalIdeal_pow_eq_setOf_le_v_coe_pow`
   (`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:676,698`), which identify
   `(IsLocalRing.maximalIdeal O ^ n : Set O)` with `{y | v (algebraMap O K y) ≤ v (algebraMap O K ϖ) ^ n}`
   for `O` a DVR with valuation `v` and irreducible `ϖ`. These are stated for `v.integer`
   (`Valuation.integer`, a plain `Subring`), not for `(valuation K).valuationSubring`
   (a bundled `ValuationSubring`) as used throughout `Langlands.HenselianValuation` — the two are
   defeq at the `Subring` level (`Valuation.valuationSubring` is literally
   `{ v.integer with mem_or_inv_mem' := ... }`) but transporting the DVR instance and the pow-ideal
   lemma across that defeq, and then bridging the *real*-number inequality/equality coming out of
   `spectralNorm_coeff_lt_one`/`spectralNorm_eq_norm_coeff_zero_rpow` back down to a `Γ₀`-valued
   (`ValueGroupWithZero K`) inequality via the `RankOne.hom` embedding's `StrictMono.le_iff_le`,
   was not attempted. This is genuine remaining work (instance-chain plumbing across two
   representations of the same valuation ring), not a missing-lemma wall — the needed lemmas are now
   named and located precisely, unlike the twelfth pass's original diagnosis.

No `LocalField.isEisensteinAt_minpoly_of_isUniformizer` statement is declared in this file: writing
the full signature before either of the two gaps above is closed would either need `sorry` (forbidden)
or hypotheses strong enough to trivialize the theorem, neither of which is acceptable per this
project's conventions. The two lemmas below are self-contained, real, and reusable regardless of how
the remaining assembly proceeds.
-/

noncomputable section

open Polynomial

/-- Coefficient bound from the spectral value: for `p : R[X]` over a normed division ring
(monic or not) and `n < p.natDegree`, `‖p.coeff n‖ ≤ (spectralValue p) ^ (p.natDegree - n)`.

Obtained directly from `spectralValue p := iSup (spectralValueTerms p)`: the `n`-th term of the
`iSup` is bounded above by the supremum, and `spectralValueTerms p n = ‖p.coeff n‖ ^ (1 / (p.natDegree
- n : ℝ))` for `n < p.natDegree`; raising both sides to the `(p.natDegree - n)`-th power (a
positive natural number here) via `Real.rpow_inv_natCast_pow` and monotonicity of `Real.rpow` in the
base gives the claim. -/
theorem spectralValue_coeff_le {R : Type*} [NormedDivisionRing R] {p : R[X]}
    {n : ℕ} (hn : n < p.natDegree) :
    ‖p.coeff n‖ ≤ spectralValue p ^ (p.natDegree - n) := by
  have hterm : spectralValueTerms p n ≤ spectralValue p :=
    le_ciSup (spectralValueTerms_bddAbove p) n
  rw [spectralValueTerms_of_lt_natDegree p hn] at hterm
  have hsub_pos : 0 < p.natDegree - n := Nat.sub_pos_of_lt hn
  have hsub_ne : (p.natDegree - n : ℕ) ≠ 0 := hsub_pos.ne'
  have hcast : (p.natDegree - n : ℝ) = ((p.natDegree - n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn.le]
  rw [hcast] at hterm
  have h1 : ‖p.coeff n‖ = (‖p.coeff n‖ ^ ((1 : ℝ) / ((p.natDegree - n : ℕ) : ℝ))) ^
      (p.natDegree - n) := by
    rw [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hsub_ne]
  rw [h1, ← Real.rpow_natCast
    (‖p.coeff n‖ ^ ((1 : ℝ) / ((p.natDegree - n : ℕ) : ℝ))) (p.natDegree - n),
    ← Real.rpow_natCast (spectralValue p) (p.natDegree - n)]
  exact Real.rpow_le_rpow (by positivity) hterm (by positivity)

/-- Sharper corollary for the spectral norm `spectralNorm K L x := spectralValue (minpoly K x)`
(`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`): if `spectralNorm K L x < 1`, every non-leading
coefficient of `minpoly K x` has norm *strictly* less than `1`, not merely `≤ 1`. This is the sharper
form `Polynomial.IsEisensteinAt.mem` needs (membership in a maximal ideal, not just the valuation
ring).

Obtained from `spectralValue_coeff_le` by noting the exponent `(minpoly K x).natDegree - n ≥ 1`, so
`spectralNorm K L x ^ ((minpoly K x).natDegree - n) ≤ spectralNorm K L x ^ 1 = spectralNorm K L x < 1`
(using `0 ≤ spectralNorm K L x ≤ 1` and `pow_le_pow_of_le_one`, decreasing powers of a base in
`[0, 1]`). -/
theorem spectralNorm_coeff_lt_one {K : Type*} [NormedField K] {L : Type*} [Field L] [Algebra K L]
    {x : L} (hx : spectralNorm K L x < 1) {n : ℕ} (hn : n < (minpoly K x).natDegree) :
    ‖(minpoly K x).coeff n‖ < 1 := by
  have hle : ‖(minpoly K x).coeff n‖ ≤ spectralNorm K L x ^ ((minpoly K x).natDegree - n) :=
    spectralValue_coeff_le hn
  have hexp : 1 ≤ (minpoly K x).natDegree - n := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hn)
  calc ‖(minpoly K x).coeff n‖
      ≤ spectralNorm K L x ^ ((minpoly K x).natDegree - n) := hle
    _ ≤ spectralNorm K L x ^ 1 :=
        pow_le_pow_of_le_one (spectralNorm_nonneg x) hx.le hexp
    _ = spectralNorm K L x := pow_one _
    _ < 1 := hx
