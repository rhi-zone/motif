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

## What remains (the genuine gap, precisely — updated fifteenth pass)

**Gap 1 (connecting a concrete uniformizer to `spectralNorm K L π < 1`) is now CLOSED**, in
`Langlands.HenselianValuation`: `LocalField.spectralNorm_lt_one_of_mem_nonunits`
(`Langlands/HenselianValuation.lean`, in the `LocalField.NormedFieldBridge` section, right before
`valuationSubring_eq_of_comap_eq`) takes `A : ValuationSubring L`, `hA : A.comap (algebraMap K L) =
(valuation K).valuationSubring`, `π ∈ A.nonunits`, `π ≠ 0`, and concludes `spectralNorm K L π < 1`,
under the same `[NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
[(NormedField.valuation).Compatible] [CompleteSpace K]` bundle `exists_rankOne_absoluteValue_extends`
already uses. Proved via the absolute value `f` from `exists_rankOne_absoluteValue_extends`
(`f x ≤ 1 ↔ x ∈ A`), `spectralNorm_unique_field_norm_ext` (`f = spectralNorm K L` pointwise),
`ValuationSubring.mem_nonunits_iff_or` (`π⁻¹ ∉ A`), and `map_inv₀` + `inv_lt_one_of_one_lt₀`.
**No `_of_isNonarchimedeanLocalField` wrapper was added** (unlike this file's other paired
theorems): `spectralNorm K L π`'s *type* itself needs a `NormedField K` instance, so a wrapper
stating it under only `[IsNonarchimedeanLocalField K]` cannot even elaborate as a public signature —
the `letI`/`haveI` instance-construction block (identical to the one already inlined twice in
`HenselianValuation.lean`, lines ~715/737) must instead be inlined once inside the proof of any
Henselian-hypothesis caller whose own *conclusion* doesn't mention `spectralNorm`/`NormedField`
(e.g. the final Eisenstein theorem below, whose conclusion is `Polynomial.IsEisensteinAt`).

**Gap 2 (the real-number-to-ideal-power conversion) is still open**, but this pass narrowed it
further and resolved two of the four sub-blockers the fourteenth pass's diagnosis implied,
confirmed via loogle + a standalone typecheck (not yet wired into a full proof):

* **Resolved: `IsIntegrallyClosed`/`IsFractionRing` for `𝒪[K]`.** The fourteenth pass worried about
  transporting these across the `Valuation.integer`/`ValuationSubring` defeq gap. Unnecessary:
  `Mathlib/RingTheory/Valuation/LocalSubring.lean:35,38` gives `IsIntegrallyClosed V` as a **direct**
  instance for *any* `V : ValuationSubring K` (via `V.integer_valuation` internally, already solved
  in Mathlib), and `ValuationSubring.instIsFractionRingSubtypeMem` gives `IsFractionRing ↥V K`
  directly too. Both apply to `𝒪[K] := (valuation K).valuationSubring` with zero transport code
  needed on this project's side.
* **Resolved: the DVR pow-ideal lemma's `Valuation.integer` mismatch.** The fourteenth pass flagged
  `Irreducible.maximalIdeal_pow_eq_setOf_le_v_coe_pow` (stated for `v.integer`, a plain `Subring`) as
  needing defeq transport to `(valuation K).valuationSubring` (a bundled `ValuationSubring`). This is
  avoidable: `ValuationSubring.lean:468`'s `valuationSubring.integers : v.Integers v.valuationSubring`
  gives the `Valuation.Integers` instance **directly at the `ValuationSubring` level**, so
  `Valuation.Integers.maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow`
  (`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:672`) applies with `O := ↥(valuation
  K).valuationSubring` directly — no `v.integer` detour at all. The needed
  `[IsDiscreteValuationRing ↥(valuation K).valuationSubring]` instance is also available directly
  (not via `v.integer`): `Valuation.valuationSubring_isDiscreteValuationRing`
  (`Mathlib/RingTheory/Valuation/Discrete/Basic.lean`), given `[IsCyclic ...valueGroup] [Nontrivial
  ...valueGroup]` (expected to hold for a discretely-valued local field, not separately checked this
  pass).
* **Sharper than anticipated: the real-to-`Γ₀` transport is an exact equality, not an inequality.**
  The fourteenth pass's writeup flagged `RankOne.hom`'s `StrictMono.le_iff_le` as the tool for
  bridging the real-number bound back to `Γ₀`. Since `RankOne.hom' : Γ₀ →*₀ ℝ≥0` is a
  `MonoidWithZeroHom` (multiplicative, not merely order-preserving), an *exact* valuation-level
  hypothesis for total ramification — e.g. `A.valuation (algebraMap K L ϖ) = A.valuation π ^ n` for
  `ϖ` a uniformizer of `𝒪[K]` and `n := (minpoly K π).natDegree` — pushes forward under `hR.hom'`
  to the *exact* real equation `‖ϖ‖ = f π ^ n = spectralNorm K L π ^ n = ‖(minpoly K π).coeff 0‖`
  (the last step via `spectralNorm_eq_norm_coeff_zero_rpow`, `SpectralNorm.lean:988`), rather than
  only an inequality. This is more useful than the fourteenth pass's plan: an exact match of `‖coeff
  0‖` with `‖ϖ‖` (which is `> ‖ϖ‖²` since `‖ϖ‖ < 1`) gives `coeff 0 ∉ 𝔪_K ^ 2` directly, with no slack
  to account for.
* **Not yet attempted: assembling the pieces.** Confirmed by a standalone typecheck this pass (not
  committed, scratch file) that `Algebra ↥(A : ValuationSubring K) L` derives automatically by
  instance search given `[Algebra K L]` — so the `minpoly ↥𝒪[K] π`-level statement (as opposed to
  `minpoly K π` mapped down) should be reachable via `minpoly.isIntegrallyClosed_eq_field_fractions'`
  (`Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean`) without a manual `Algebra` instance, but
  this was not tried end-to-end. What remains, none of it attempted in Lean this pass: (a) precisely
  designing the "totally ramified" hypothesis (the `A.valuation`-level equation above, or an
  equivalent `Associated`-based phrasing, applied to a chosen uniformizer `ϖ` of `𝒪[K]`); (b) the
  `IsScalarTower`/`minpoly.isIntegrallyClosed_eq_field_fractions'` wiring to get `minpoly ↥𝒪[K] π`
  and relate its coefficients to `minpoly K π`'s; (c) assembling `Polynomial.IsEisensteinAt`'s three
  fields (`leading`, `mem`, `notMem`) from `spectralNorm_coeff_lt_one` (gap 1's output) plus the
  exact-equality argument above; (d) checking `Valuation.valuationSubring_isDiscreteValuationRing`'s
  `IsCyclic`/`Nontrivial` value-group hypotheses actually discharge for `IsNonarchimedeanLocalField
  K`. None of (a)–(d) hit a wall — each has a named, real Mathlib lemma or an already-typechecked
  instance to build on — but none was built or tested this pass, so none should be treated as
  confirmed working until actually written and built.

No `LocalField.isEisensteinAt_minpoly_of_isUniformizer` statement is declared in this file: writing
the full signature before gap 2's assembly (a)–(d) above is closed would either need `sorry`
(forbidden) or hypotheses strong enough to trivialize the theorem, neither of which is acceptable per
this project's conventions. The two lemmas below (plus gap 1's `spectralNorm_lt_one_of_mem_nonunits`
in `Langlands.HenselianValuation`) are self-contained, real, and reusable regardless of how the
remaining assembly proceeds.
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
