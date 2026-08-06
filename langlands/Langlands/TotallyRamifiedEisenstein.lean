import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Eisenstein-ness of the minimal polynomial of a uniformizer, and totally-ramified monogenicity

`LocalField.isEisensteinAt_minpoly_of_isUniformizer` (the theorem that a uniformizer of a totally
ramified extension of a complete discretely-valued field has an Eisenstein minimal polynomial over
`𝒪[K] := (valuation K).valuationSubring`) is proved, without `sorry`, in this file — closing the
gap scoped in `ROADMAP.md` Phase 2b's thirteenth pass and
`langlands/Langlands/RamificationFiltration.lean`'s `## Scope` section. Building on it,
`LocalField.adjoin_eq_integralClosure_of_isUniformizer` proves the classical monogenicity statement
for the totally ramified case (Serre, *Local Fields*, Ch. III): if `π` also generates `L` over `K`,
the integral closure of `𝒪[K]` in `L` is generated as an `𝒪[K]`-algebra by `π`,
`Algebra.adjoin ↥𝒪[K] {π} = integralClosure ↥𝒪[K] L`.

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
* `LocalField.isIntegral_of_isUniformizer` : the same hypotheses (minus `IsDiscreteValuationRing`,
  which the integrality argument doesn't need) give `IsIntegral ↥𝒪[K] π`. Extracted as a standalone
  lemma from the Eisenstein theorem's proof so `adjoin_eq_integralClosure_of_isUniformizer` doesn't
  have to re-derive it.
* `LocalField.isEisensteinAt_minpoly_of_isUniformizer` : for `ϖ : ↥(valuation K).valuationSubring`
  irreducible (a uniformizer of `𝒪[K]`) and `π : L` with the exact "totally ramified of degree `n`"
  hypothesis `‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree` (`n := (minpoly K
  π).natDegree`), `minpoly ↥(valuation K).valuationSubring π` is Eisenstein at `𝔪_{𝒪[K]}`.
* `LocalField.adjoin_eq_integralClosure_of_isUniformizer` : the same `hram` totally-ramified
  hypothesis, plus `[FiniteDimensional K L] [Algebra.IsSeparable K L]` and `hgen : (minpoly K
  π).natDegree = Module.finrank K L` (i.e. `π` also generates `L` over `K`, so `L = K(π)`), give
  `Algebra.adjoin ↥𝒪[K] {π} = integralClosure ↥𝒪[K] L` — monogenicity of the ring of integers of a
  totally ramified extension. Built from the Eisenstein theorem plus Mathlib's
  `Algebra.discr_mul_isIntegral_mem_adjoin` and
  `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt`
  (`Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral`), confirmed by the sixteenth pass to be the
  right general (non-`NumberField`-specific) levers for this step.
* `LocalField.coeff_zero_norm_eq_of_isUniformizer` : `‖(minpoly K π).coeff 0‖ = ‖ϖ‖` under `hram`
  alone (no `IsDiscreteValuationRing` needed). Extracted from `isEisensteinAt_minpoly_of_isUniformizer`'s
  proof (as `hcoeff0`) so `norm_isUniformizer_eq_of_isUniformizer` can reuse it.
* `LocalField.norm_isUniformizer_eq_of_isUniformizer` : the same `hram` hypothesis plus
  `[FiniteDimensional K L]` and `hgen : (minpoly K π).natDegree = Module.finrank K L` (`π` also
  generates `L`) give `‖Algebra.norm K π‖ = ‖ϖ‖` — the norm of a uniformizer-generator is again a
  uniformizer of `K`. Built from `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`
  (`Mathlib.RingTheory.Norm.Basic`) applied to the same `PowerBasis K L` construction used in
  `adjoin_eq_integralClosure_of_isUniformizer`'s proof, plus `coeff_zero_norm_eq_of_isUniformizer`.
  Progress toward Phase 2b's totally-ramified norm-group theorem: establishes that `N(π)`, one of
  the two generators on the RHS of `N_{L/K}(L^×) = ⟨N(π)⟩ · N_{L/K}(U_L)`, is indeed a uniformizer.

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

omit [CompleteSpace K] in
/-- A uniformizer `π` of a totally ramified extension (in the sense of `hram`, the same "totally
ramified of degree `(minpoly K π).natDegree`" hypothesis used by
`isEisensteinAt_minpoly_of_isUniformizer`) is integral over `𝒪[K] := (valuation K).valuationSubring`.
Extracted as a standalone lemma from the proof of `isEisensteinAt_minpoly_of_isUniformizer` (which
uses it as `hintO'`) so that later results (e.g. monogenicity) can build `IsIntegral ↥𝒪[K] π`
without re-deriving the coefficient bounds. -/
theorem isIntegral_of_isUniformizer
    [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} (hϖ : Irreducible ϖ) {π : L}
    (hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree) :
    IsIntegral ↥(ValuativeRel.valuation K).valuationSubring π := by
  let O : ValuationSubring K := (ValuativeRel.valuation K).valuationSubring
  set n := (minpoly K π).natDegree with hn
  have hnpos : 0 < n := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral π)
  have hϖlt : ‖(ϖ : K)‖ < 1 :=
    (mem_maximalIdeal_iff_norm_lt_one K ϖ).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr fun hu => hϖ.not_isUnit hu)
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
  exact hintO

/-- The constant coefficient of `minpoly K π`, for `π` a uniformizer of a totally ramified
extension (in the sense of `hram`), has exactly the norm of the fixed uniformizer `ϖ` of `K`:
`‖(minpoly K π).coeff 0‖ = ‖ϖ‖`. Extracted from the proof of `isEisensteinAt_minpoly_of_isUniformizer`
(where it appears as `hcoeff0`) so `norm_isUniformizer_eq_of_isUniformizer` can reuse it without
re-deriving from `hram` and `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`. -/
theorem coeff_zero_norm_eq_of_isUniformizer
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} {π : L}
    (hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree) :
    ‖(minpoly K π).coeff 0‖ = ‖(ϖ : K)‖ := by
  have hnpos : 0 < (minpoly K π).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral π)
  rw [hram, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div,
    Real.rpow_inv_natCast_pow (norm_nonneg _) hnpos.ne']

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
polynomial over `𝒪[K].toSubring` witnessing `IsIntegral ↥𝒪[K] π` (`isIntegral_of_isUniformizer`).
Then `minpoly.isIntegrallyClosed_eq_field_fractions'` (using the direct `IsIntegrallyClosed`/
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
  have hcoeff0 : ‖(minpoly K π).coeff 0‖ = ‖(ϖ : K)‖ := coeff_zero_norm_eq_of_isUniformizer K hram
  have hspec : spectralNorm K L π < 1 := by
    by_contra hge
    push Not at hge
    have h1 : (1 : ℝ) ≤ spectralNorm K L π ^ n := one_le_pow₀ hge
    rw [← hram] at h1
    linarith
  have hintO' : IsIntegral (↥O) π := isIntegral_of_isUniformizer K hϖ hram
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

/-- **Monogenicity of the ring of integers of a totally ramified extension** (Serre, *Local
Fields*, Ch. III, corollary to Prop. 18). A uniformizer `π` of a totally ramified extension `L / K`
(in the sense of `hram`, as in `isEisensteinAt_minpoly_of_isUniformizer`) that also generates `L`
over `K` (`hgen : (minpoly K π).natDegree = Module.finrank K L`, i.e. `K⟮π⟯ = L`) generates the
integral closure of `𝒪[K]` in `L` as an `𝒪[K]`-algebra:
`Algebra.adjoin ↥𝒪[K] {π} = integralClosure ↥𝒪[K] L`.

Proof outline: build a `PowerBasis K L` `B` with `B.gen = π`, using `hgen` to promote `K⟮π⟯` to `⊤`.
`isEisensteinAt_minpoly_of_isUniformizer` supplies `minpoly ↥𝒪[K] π` Eisenstein at `𝔪_{𝒪[K]}`, which
(via `Irreducible.maximalIdeal_eq`) is Eisenstein at the prime `ϖ` itself (irreducible in the DVR
`↥𝒪[K]`, hence prime, since a DVR is a UFD). For `z` integral over `↥𝒪[K]`,
`Algebra.discr_mul_isIntegral_mem_adjoin` gives `discr K B.basis • z ∈ 𝒪[K][π]`; since `discr K
B.basis ≠ 0` (separability) and integral over the integrally closed `↥𝒪[K]`, it lies in `↥𝒪[K]` as
some `d`, associated (`IsDiscreteValuationRing.associated_pow_irreducible`) to `ϖ ^ m` for some `m`;
cancelling the unit and applying
`mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt` gives `z ∈ 𝒪[K][π]`. -/
theorem adjoin_eq_integralClosure_of_isUniformizer
    [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} (hϖ : Irreducible ϖ) {π : L}
    (hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree)
    (hgen : (minpoly K π).natDegree = Module.finrank K L) :
    Algebra.adjoin ↥(ValuativeRel.valuation K).valuationSubring ({π} : Set L) =
      integralClosure ↥(ValuativeRel.valuation K).valuationSubring L := by
  let O : ValuationSubring K := (ValuativeRel.valuation K).valuationSubring
  have hπO : IsIntegral ↥O π := isIntegral_of_isUniformizer K hϖ hram
  have hxK : IsIntegral K π := hπO.tower_top
  -- `π` generates `L` over `K`.
  have hfr : Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = Module.finrank K L := by
    rw [IntermediateField.adjoin.finrank hxK, hgen]
  have htop : IntermediateField.adjoin K ({π} : Set L) = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.top_toSubalgebra]
    apply Algebra.toSubmodule_eq_top.1
    apply Submodule.eq_top_of_finrank_eq
    rw [Subalgebra.finrank_toSubmodule]
    exact hfr
  -- The Subalgebra generated by `π` is all of `L`.
  have htopalg : Algebra.adjoin K ({π} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxK.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]
  -- A `PowerBasis K L` with generator `π`.
  let B0 : PowerBasis K ↥(Algebra.adjoin K ({π} : Set L)) := Algebra.adjoin.powerBasis hxK
  let e : ↥(Algebra.adjoin K ({π} : Set L)) ≃ₐ[K] L :=
    (Subalgebra.equivOfEq _ _ htopalg).trans Subalgebra.topEquiv
  let B : PowerBasis K L := B0.map e
  have hBgen : B.gen = π := by
    show e B0.gen = π
    rw [Algebra.adjoin.powerBasis_gen]
    show ((Subalgebra.equivOfEq _ _ htopalg).trans Subalgebra.topEquiv)
        (⟨π, Algebra.subset_adjoin rfl⟩ : ↥(Algebra.adjoin K ({π} : Set L))) = π
    rw [AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply, Subalgebra.topEquiv_apply]
  have hBint : IsIntegral ↥O B.gen := hBgen ▸ hπO
  have hEis : (minpoly ↥O B.gen).IsEisensteinAt (Submodule.span ↥O ({ϖ} : Set ↥O)) := by
    rw [hBgen, Ideal.submodule_span_eq, ← Irreducible.maximalIdeal_eq hϖ]
    exact isEisensteinAt_minpoly_of_isUniformizer K hϖ hram
  have hϖPrime : Prime ϖ := by
    haveI := PrincipalIdealRing.to_uniqueFactorizationMonoid (R := ↥O)
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hϖ
  refine le_antisymm (adjoin_le_integralClosure hπO) ?_
  intro z hz
  have hzint : IsIntegral ↥O z := hz
  -- `discr K B.basis` is a nonzero element of `𝒪[K]`, hence an associate of `ϖ ^ m`.
  have hdint : IsIntegral ↥O (Algebra.discr K B.basis) :=
    Algebra.discr_isIntegral K (R := ↥O) (b := ⇑B.basis) fun i => by
      rw [B.basis_eq_pow i]; exact hBint.pow _
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdint
  have hdne : d ≠ 0 := by
    intro h0
    apply Algebra.discr_not_zero_of_basis (K := K) (L := L) B.basis
    rw [← hd, h0, map_zero]
  obtain ⟨m, hassoc⟩ := IsDiscreteValuationRing.associated_pow_irreducible hdne hϖ
  obtain ⟨v, hv⟩ := hassoc.symm
  have hmem : Algebra.discr K B.basis • z ∈ Algebra.adjoin ↥O ({B.gen} : Set L) :=
    Algebra.discr_mul_isIntegral_mem_adjoin K (R := ↥O) hBint hzint
  have hdz : d • z = Algebra.discr K B.basis • z := by
    rw [← hd, IsScalarTower.algebraMap_smul K d z]
  rw [← hdz, ← hv, mul_smul] at hmem
  have hmem2 : ((v⁻¹ : (↥O)ˣ) : ↥O) • ((ϖ ^ m : ↥O) • ((v : ↥O) • z)) ∈
      Algebra.adjoin ↥O ({B.gen} : Set L) :=
    Subalgebra.smul_mem _ hmem _
  have heq : ((v⁻¹ : (↥O)ˣ) : ↥O) • ((ϖ ^ m : ↥O) • ((v : ↥O) • z)) = (ϖ ^ m : ↥O) • z := by
    rw [smul_smul, smul_smul,
      show ((v⁻¹ : (↥O)ˣ) : ↥O) * ϖ ^ m * (v : ↥O) =
          ϖ ^ m * (((v⁻¹ : (↥O)ˣ) : ↥O) * (v : ↥O)) by ring,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  rw [heq] at hmem2
  have := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt hϖPrime hBint hzint hmem2 hEis
  rwa [hBgen] at this

/-- **The norm of a uniformizer generating a totally ramified extension is again a uniformizer**
(Serre, *Local Fields*, Ch. III). A uniformizer `π` of a totally ramified extension `L / K` (in the
sense of `hram`, as in `isEisensteinAt_minpoly_of_isUniformizer`) that also generates `L` over `K`
(`hgen : (minpoly K π).natDegree = Module.finrank K L`, i.e. `K⟮π⟯ = L`) has `Algebra.norm K π`
exactly of the norm of the fixed uniformizer `ϖ`: `‖Algebra.norm K π‖ = ‖ϖ‖`.

This is one of the two facts (the other being unit-norm surjectivity, see `ROADMAP.md` Phase 2b)
needed for the totally-ramified norm-group theorem `N_{L/K}(L^×) = ⟨N(π)⟩ · N_{L/K}(U_L)`: it shows
`N(π)` is itself a uniformizer of `K`, hence a valid generator of the cyclic quotient
`K^× / N_{L/K}(L^×)` alongside `N_{L/K}(U_L)`.

Proof outline: build a `PowerBasis K L` `B` with `B.gen = π`, exactly as in
`adjoin_eq_integralClosure_of_isUniformizer` (using `hgen` to promote `K⟮π⟯` to `⊤`; separability is
*not* needed for this construction, only `[FiniteDimensional K L]`). Mathlib's
`Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly` gives `Algebra.norm K π = (-1) ^ B.dim *
(minpoly K π).coeff 0`. Taking norms, `‖(-1 : K) ^ B.dim‖ = 1` (norm of `±1` is `1`) and
`coeff_zero_norm_eq_of_isUniformizer` gives `‖(minpoly K π).coeff 0‖ = ‖ϖ‖`, so `‖Algebra.norm K π‖ =
1 * ‖ϖ‖ = ‖ϖ‖`. -/
theorem norm_isUniformizer_eq_of_isUniformizer
    [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
    [FiniteDimensional K L]
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} (hϖ : Irreducible ϖ) {π : L}
    (hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree)
    (hgen : (minpoly K π).natDegree = Module.finrank K L) :
    ‖Algebra.norm K π‖ = ‖(ϖ : K)‖ := by
  have hπO : IsIntegral ↥(ValuativeRel.valuation K).valuationSubring π :=
    isIntegral_of_isUniformizer K hϖ hram
  have hxK : IsIntegral K π := hπO.tower_top
  have hfr : Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = Module.finrank K L := by
    rw [IntermediateField.adjoin.finrank hxK, hgen]
  have htop : IntermediateField.adjoin K ({π} : Set L) = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.top_toSubalgebra]
    apply Algebra.toSubmodule_eq_top.1
    apply Submodule.eq_top_of_finrank_eq
    rw [Subalgebra.finrank_toSubmodule]
    exact hfr
  have htopalg : Algebra.adjoin K ({π} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxK.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]
  let B0 : PowerBasis K ↥(Algebra.adjoin K ({π} : Set L)) := Algebra.adjoin.powerBasis hxK
  let e : ↥(Algebra.adjoin K ({π} : Set L)) ≃ₐ[K] L :=
    (Subalgebra.equivOfEq _ _ htopalg).trans Subalgebra.topEquiv
  let B : PowerBasis K L := B0.map e
  have hBgen : B.gen = π := by
    show e B0.gen = π
    rw [Algebra.adjoin.powerBasis_gen]
    show ((Subalgebra.equivOfEq _ _ htopalg).trans Subalgebra.topEquiv)
        (⟨π, Algebra.subset_adjoin rfl⟩ : ↥(Algebra.adjoin K ({π} : Set L))) = π
    rw [AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply, Subalgebra.topEquiv_apply]
  have hnorm : Algebra.norm K π = (-1) ^ B.dim * (minpoly K π).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly B
    rwa [hBgen] at this
  have hcoeff0 : ‖(minpoly K π).coeff 0‖ = ‖(ϖ : K)‖ := coeff_zero_norm_eq_of_isUniformizer K hram
  rw [hnorm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hcoeff0]

end LocalField
