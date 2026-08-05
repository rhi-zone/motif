import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Eisenstein-ness of the minimal polynomial of a uniformizer

`LocalField.isEisensteinAt_minpoly_of_isUniformizer` (the theorem that a uniformizer of a totally
ramified extension of a complete discretely-valued field has an Eisenstein minimal polynomial over
`𝒪[K] := (valuation K).valuationSubring`) is now proved, without `sorry`, in this file — closing the
gap scoped in `ROADMAP.md` Phase 2b's thirteenth pass and
`langlands/Langlands/RamificationFiltration.lean`'s `## Scope` section.

## Main results

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
* `LocalField.mem_valuationSubring_iff_norm_le_one`, `LocalField.valuation_le_iff_norm_le`,
  `LocalField.mem_maximalIdeal_iff_norm_lt_one` : bridging lemmas between the ambient `ValuativeRel
  K`-canonical valuation `valuation K` and the norm `‖·‖`, for a `K` in the
  `NontriviallyNormedField`/`IsUltrametricDist`/`ValuativeRel`/`Compatible` bundle used throughout
  `Langlands.HenselianValuation`. General-purpose, not specific to the Eisenstein argument.
* `LocalField.isEisensteinAt_minpoly_of_isUniformizer` : for `ϖ : ↥(valuation K).valuationSubring`
  irreducible (a uniformizer of `𝒪[K]`) and `π : L` with the exact "totally ramified of degree `n`"
  hypothesis `‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree` (`n := (minpoly K
  π).natDegree`), `minpoly ↥(valuation K).valuationSubring π` is Eisenstein at `𝔪_{𝒪[K]}`.

## The final hypothesis design (differs from the fourteenth/fifteenth pass's plan)

Earlier passes' diagnosis (see prior `ROADMAP.md` entries) planned to phrase "totally ramified of
degree `n`" as an exact equation `A.valuation (algebraMap K L ϖ) = A.valuation π ^ n` at the level
of a `ValuationSubring A : ValuationSubring L` extending `𝒪[K]`, pushed forward to a real equation
via a `RankOne A.valuation` instance's `hom'` (`Langlands.HenselianValuation`'s
`exists_rankOne_compatible`/`exists_rankOne_absoluteValue_extends` machinery). Attempting this
directly hit a genuine obstruction: the `RankOne A.valuation` instance's `.hom'` field, once
resolved through Lean's dot notation, turned out to resolve to the *parent* `RankLeOne` structure's
`hom'` (operating on the canonical `MonoidWithZeroHom.ValueGroup₀`-embedded value group), not
directly on `A.ValueGroup` as the naive signature `A.valuation x : A.ValueGroup` would suggest — so
`hR.hom' (A.valuation x)` does not typecheck as written; only `hR.hom' (A.valuation.restrict ...)`
(via the `ValueGroup₀`-typed `restrict`) does, and generalizing `exists_rankOne_absoluteValue_extends`'s
`f (algebraMap K L x) = ‖x‖` fact (proved only for `x` in the image of `algebraMap K L`) to *all*
`y : L` was not straightforward from the section's existing lemmas.

**This entire detour is unnecessary.** `spectralNorm K L` is *already* the canonical, unique
extension of `‖·‖` from `K` to `L` (given `L / K` algebraic and `K` complete, by
`spectralNorm_unique_field_norm_ext`, applied to any `f : AbsoluteValue L ℝ` extending `‖·‖`, hence
in particular to any `f` built from a `RankOne A.valuation` compatible instance). So the classical
"totally ramified of degree `n`" condition `v_L(π) = v_L(ϖ)/n` — after normalizing `v_L` to extend
`‖·‖_K` — is *exactly* `spectralNorm K L π ^ n = ‖ϖ‖`, with no reference to a specific
`A : ValuationSubring L` or `RankOne` instance needed at all. This is both a strictly simpler
hypothesis to state and prove from, and (as a consequence) it lets
`isEisensteinAt_minpoly_of_isUniformizer` drop the whole `A`/`hA`/`π ∈ A.nonunits`/`π ≠ 0` apparatus:
`spectralNorm K L π < 1` is now a *derived* fact (from the hypothesis plus `‖ϖ‖ < 1`, since `ϖ`
irreducible forces it into `𝔪_{𝒪[K]}`), not something that needs proving via `A` first. In
particular `LocalField.spectralNorm_lt_one_of_mem_nonunits` (`Langlands.HenselianValuation`) and the
whole `RankOne`/`exists_rankOne_absoluteValue_extends` machinery are **not used** by the theorem
proved here — this file has no dependency on `Langlands.HenselianValuation` at all.

The remaining assembly (coefficients of `minpoly K π` lie in `𝒪[K]`, transported down to
`minpoly ↥𝒪[K] π` via `minpoly.isIntegrallyClosed_eq_field_fractions'`, `IsIntegrallyClosed`/
`IsFractionRing ↥𝒪[K] K` as direct instances from `Mathlib.RingTheory.Valuation.LocalSubring`, and
the ideal-power membership from `Valuation.Integers.maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow`)
follows the fifteenth pass's diagnosis closely and did not hit further obstructions.

## Design note: `[IsDiscreteValuationRing ↥(valuation K).valuationSubring]` is a hypothesis

As anticipated by the task brief, deriving this from `IsCyclic`/`Nontrivial` value-group conditions
(`Valuation.valuationSubring_isDiscreteValuationRing`) was not attempted — it is orthogonal,
structural content about `K` (not about the Eisenstein/ramification argument), so it is taken as an
explicit hypothesis rather than derived.
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

namespace LocalField

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

omit [CompleteSpace K] in
/-- Membership in `(valuation K).valuationSubring` is exactly `‖·‖ ≤ 1`. -/
theorem mem_valuationSubring_iff_norm_le_one (x : K) :
    x ∈ (ValuativeRel.valuation K).valuationSubring ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff]
  have h1 := Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) x 1
  have h2 := Valuation.Compatible.vle_iff_le (v := NormedField.valuation (K := K)) x 1
  rw [map_one] at h1 h2
  rw [← h1, h2, NormedField.valuation_apply]
  norm_cast

omit [CompleteSpace K] in
/-- General `valuation K`-vs-norm bridging, beyond the `≤ 1` special case of
`mem_valuationSubring_iff_norm_le_one`. -/
theorem valuation_le_iff_norm_le (x y : K) :
    ValuativeRel.valuation K x ≤ ValuativeRel.valuation K y ↔ ‖x‖ ≤ ‖y‖ := by
  have h1 := Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) x y
  have h2 := Valuation.Compatible.vle_iff_le (v := NormedField.valuation (K := K)) x y
  rw [← h1, h2, NormedField.valuation_apply, NormedField.valuation_apply]
  norm_cast

omit [CompleteSpace K] in
/-- Membership of `x : ↥(valuation K).valuationSubring` in the maximal ideal is exactly
`‖(x : K)‖ < 1`: a nonunit of a valuation ring has norm strictly less than `1`, and conversely. -/
theorem mem_maximalIdeal_iff_norm_lt_one (x : ↥(ValuativeRel.valuation K).valuationSubring) :
    x ∈ IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation K).valuationSubring ↔ ‖(x : K)‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal]
  constructor
  · intro hx
    by_contra hge
    push Not at hge
    have hle : ‖(x : K)‖ ≤ 1 := (mem_valuationSubring_iff_norm_le_one K (x : K)).mp x.2
    have heq1 : ‖(x : K)‖ = 1 := le_antisymm hle hge
    have hxne : (x : K) ≠ 0 := by
      intro h0; rw [h0] at heq1; simp at heq1
    have hinv_le : ‖((x : K))⁻¹‖ ≤ 1 := by rw [norm_inv, heq1]; norm_num
    have hinv_mem : ((x : K))⁻¹ ∈ (ValuativeRel.valuation K).valuationSubring :=
      (mem_valuationSubring_iff_norm_le_one K _).mpr hinv_le
    exact hx (IsUnit.of_mul_eq_one
      (⟨(x : K)⁻¹, hinv_mem⟩ : ↥(ValuativeRel.valuation K).valuationSubring)
      (Subtype.ext (by simp [hxne])))
  · intro hlt hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hxy : ‖(x : K)‖ * ‖(y : K)‖ = 1 := by
      have h : (x : K) * (y : K) = 1 := by
        have := congrArg (Subtype.val) hy
        simpa using this
      rw [← norm_mul, h, norm_one]
    have hy_le : ‖(y : K)‖ ≤ 1 := (mem_valuationSubring_iff_norm_le_one K _).mp y.2
    nlinarith [norm_nonneg (x : K), norm_nonneg (y : K)]

/-- **Eisenstein-ness of the minimal polynomial of a uniformizer of a totally ramified
extension** (Serre, *Local Fields*, Ch. III). `ϖ` a uniformizer of `𝒪[K] := (valuation
K).valuationSubring` (`Irreducible ϖ`) and `π : L` satisfying the exact "totally ramified of degree
`n := (minpoly K π).natDegree`" hypothesis `‖(ϖ : K)‖ = spectralNorm K L π ^ n` — the classical
`v_L(π) = v_L(ϖ) / n` condition, normalized to extend `‖·‖` on `K` via the canonical extension
`spectralNorm K L` (unique by `spectralNorm_unique_field_norm_ext`, given `L / K` algebraic and `K`
complete) — together imply `minpoly ↥𝒪[K] π` is Eisenstein at `𝔪_{𝒪[K]}`.

Proof outline: `hram` forces `spectralNorm K L π < 1` (since `‖ϖ‖ < 1`, `ϖ` being irreducible hence a
nonunit of `𝒪[K]`), giving via `spectralNorm_coeff_lt_one` that every non-leading coefficient of
`minpoly K π` has norm `< 1`; combined with the leading coefficient (norm `1`, monic), every
coefficient of `minpoly K π` lies in `𝒪[K]`, so `Polynomial.toSubring` lifts `minpoly K π` to a monic
polynomial over `𝒪[K].toSubring` witnessing `IsIntegral ↥𝒪[K] π`. Then
`minpoly.isIntegrallyClosed_eq_field_fractions'` (using the direct `IsIntegrallyClosed`/
`IsFractionRing ↥𝒪[K] K` instances from `Mathlib.RingTheory.Valuation.LocalSubring`) identifies
`minpoly K π` with the base change of `minpoly ↥𝒪[K] π` along `algebraMap ↥𝒪[K] K`, transporting the
coefficient bounds down. The `notMem` field (`coeff 0 ∉ 𝔪 ^ 2`) uses the *exact* equality
`‖(minpoly K π).coeff 0‖ = ‖ϖ‖` (from `hram` via `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`)
together with `‖ϖ‖ > ‖ϖ‖ ^ 2` (as `0 < ‖ϖ‖ < 1`) and the ideal-power/valuation identification
`Valuation.Integers.maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow`. -/
theorem isEisensteinAt_minpoly_of_isUniformizer
    [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} (hϖ : Irreducible ϖ) {π : L}
    (hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree) :
    (minpoly ↥(ValuativeRel.valuation K).valuationSubring π).IsEisensteinAt
      (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation K).valuationSubring) := by
  let O : ValuationSubring K := (ValuativeRel.valuation K).valuationSubring
  set n := (minpoly K π).natDegree with hn
  have hnpos : 0 < n := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral π)
  have hϖlt : ‖(ϖ : K)‖ < 1 :=
    (mem_maximalIdeal_iff_norm_lt_one K ϖ).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr fun hu => hϖ.not_isUnit hu)
  have hϖpos : 0 < ‖(ϖ : K)‖ := by
    have hne0 : (ϖ : K) ≠ 0 := by
      intro h0
      exact hϖ.ne_zero (Subtype.ext (h0.trans (by simp)))
    exact norm_pos_iff.mpr hne0
  have hcoeff0 : ‖(minpoly K π).coeff 0‖ = ‖(ϖ : K)‖ := by
    rw [hram, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div,
      Real.rpow_inv_natCast_pow (norm_nonneg _) hnpos.ne']
  have hspec : spectralNorm K L π < 1 := by
    by_contra hge
    push Not at hge
    have h1 : (1 : ℝ) ≤ spectralNorm K L π ^ n := one_le_pow₀ hge
    rw [← hram] at h1
    linarith
  have hmonic : (minpoly K π).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral π)
  -- All coefficients of `minpoly K π` lie in `O`.
  have hcoeffs : ∀ i, (minpoly K π).coeff i ∈ O := by
    intro i
    rw [mem_valuationSubring_iff_norm_le_one]
    rcases lt_trichotomy i n with hi | hi | hi
    · exact (spectralNorm_coeff_lt_one hspec (n := i) hi).le
    · rw [hi, hn, hmonic.coeff_natDegree]
      simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hn ▸ hi)]
      simp
  have hp : (↑((minpoly K π).coeffs) : Set K) ⊆ (O.toSubring : Set K) := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨j, -, hcj⟩ := hc
    rw [hcj, SetLike.mem_coe, ValuationSubring.mem_toSubring]
    exact hcoeffs j
  set q : Polynomial O.toSubring := (minpoly K π).toSubring O.toSubring hp with hq
  have hqmonic : q.Monic := (Polynomial.monic_toSubring _ _ _).mpr hmonic
  have hqmap : Polynomial.map O.toSubring.subtype q = minpoly K π :=
    Polynomial.map_toSubring _ _ _
  have hintO : IsIntegral (↥O.toSubring) π := by
    refine ⟨q, hqmonic, ?_⟩
    have h1 : (Polynomial.aeval π) (Polynomial.map (algebraMap O.toSubring K) q) = 0 := by
      rw [show algebraMap O.toSubring K = O.toSubring.subtype from rfl, hqmap, minpoly.aeval]
    rwa [Polynomial.aeval_map_algebraMap] at h1
  have hintO' : IsIntegral (↥O) π := hintO
  -- `minpoly K π` is the base change of `minpoly ↥O π` along `algebraMap ↥O K`.
  have hminpolyeq : minpoly K π = Polynomial.map (algebraMap ↥O K) (minpoly ↥O π) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hintO'
  have hinj : Function.Injective (algebraMap ↥O K) := IsFractionRing.injective ↥O K
  have hdeg : (minpoly ↥O π).natDegree = n := by
    rw [hn, hminpolyeq, Polynomial.natDegree_map_eq_of_injective hinj]
  have hcoeff_eq : ∀ i, (minpoly K π).coeff i = ((minpoly ↥O π).coeff i : K) := by
    intro i
    rw [hminpolyeq, Polynomial.coeff_map, ValuationSubring.algebraMap_apply]
  refine (minpoly.monic hintO').isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal ↥O).ne_top ?_ ?_
  · intro i hi
    rw [hdeg] at hi
    rw [mem_maximalIdeal_iff_norm_lt_one, ← hcoeff_eq]
    exact spectralNorm_coeff_lt_one hspec hi
  · have hpow := Valuation.Integers.maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow
      (Valuation.valuationSubring.integers (ValuativeRel.valuation K)) hϖ 2
    have hmem_iff : (minpoly ↥O π).coeff 0 ∈ IsLocalRing.maximalIdeal ↥O ^ 2 ↔
        ValuativeRel.valuation K (algebraMap ↥O K ((minpoly ↥O π).coeff 0)) ≤
          ValuativeRel.valuation K (algebraMap ↥O K ϖ) ^ 2 := by
      rw [← SetLike.mem_coe, hpow]; rfl
    rw [hmem_iff, ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply,
      ← hcoeff_eq, ← map_pow, valuation_le_iff_norm_le]
    rw [hcoeff0, norm_pow]
    push Not
    nlinarith [sq_nonneg (‖(ϖ : K)‖ - 1)]

end LocalField
