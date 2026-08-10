import Langlands.AdicCompletionMixedCharacteristic
import Langlands.NonarchimedeanExponentialFiltration
import Langlands.NonarchimedeanExponentialUnitsIso

/-!
# Instantiating the exponential/logarithm's convergence domain for `v.adicCompletionIntegers F`

`Langlands.NonarchimedeanExponentialFiltration` translates `NonarchimedeanExponential.exp`/`log`'s
abstract convergence threshold into filtration-level language for an abstract `ValuationSubring A`
of a `NormedField K`, but stops short of the concrete `HeightOneSpectrum` setting used throughout
this repo: that concrete instantiation needs `CharZero (v.adicCompletion F)` and a
residue-characteristic-`p` instance, neither of which existed anywhere in this repo before
`Langlands.AdicCompletionMixedCharacteristic`. This file supplies the missing bridge and produces
the concrete existence statement: for `v` a place of a Dedekind domain `A` with fraction field `F`
of characteristic `0`, and `p` the residue characteristic of `v`, some explicit `i₀` has `exp`
(resp. `log`) defined on all of `𝔪^i` for `v.adicCompletionIntegers F`, for every `i ≥ i₀`.

## Route

* `v.adicCompletionIntegers F` *is*, definitionally, `Valued.v.valuationSubring`
  (`IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers`, Mathlib) — so
  `NonarchimedeanExponentialFiltration`'s abstract `ValuationSubring A` can be instantiated at `A :=
  v.adicCompletionIntegers F` directly, with no new subring construction needed.
* Its membership hypothesis `hA : ∀ x, x ∈ A ↔ ‖x‖ ≤ 1` is `mem_adicCompletionIntegers` chained with
  `Valued.toNormedField.norm_le_one_iff` (the norm on `v.adicCompletion F` built in
  `Langlands.NormMap`'s `instNontriviallyNormedFieldAdicCompletion` is, by construction, compatible
  with `Valued.v`).
* A uniformizer exists unconditionally: `Valued.v` is `Valuation.IsRankOneDiscrete` for any Dedekind
  domain (Mathlib, already invoked in `Langlands.NormMap`), so
  `Valuation.IsRankOneDiscrete.generator_mem_range` produces `π : v.adicCompletion F` with
  `Valued.v π = ↑(generator)`, i.e. `Valuation.IsUniformizer Valued.v π`; `IsUniformizer.is_generator`
  then gives `maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {π}` and `val_lt_one` gives
  `‖π‖ < 1`.
* The threshold hypothesis `‖(p : K)‖ < 1` that `exp`/`log` need is exactly
  `CharP (ResidueField (v.adicCompletionIntegers F)) p`, unwound: that characteristic instance says
  `(p : ResidueField _) = 0`, i.e. (naturality of the residue map's cast, `residue_eq_zero_iff`) `(p :
  v.adicCompletionIntegers F) ∈ maximalIdeal`, hence (`valued_lt_one_of_mem_maximalIdeal`,
  `Langlands.AdicCompletionIntegersResidue`) `Valued.v (p : v.adicCompletion F) < 1`.

## Main results

* `norm_natCast_lt_one_of_charP_residueField` : the threshold hypothesis `exp`/`log` need, derived
  from the residue-characteristic instance rather than assumed separately.
* `exists_uniformizer` : existence of a uniformizer of `v.adicCompletionIntegers F`, unconditionally.
* `exists_maximalIdeal_pow_lt_convergenceRadius` / `..._lt_logConvergenceRadius` : the concrete
  instantiation — some explicit `i₀` has `𝔪^i` inside `exp`'s (resp. `log`'s) convergence domain for
  every `i ≥ i₀`.

## What remains

Landing in the principal-units subgroup `U^{(i)}`, an explicit closed-form `i` (rather than
existential), and the mutual-inverse/norm-compatibility facts are exactly the items
`Langlands.NonarchimedeanExponentialFiltration`'s and `Langlands.NonarchimedeanExponential`'s "What
remains" sections already flag as unattempted; none of that is closed by this file.
-/

noncomputable section

open IsDedekindDomain IsLocalRing NonarchimedeanExponential
open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

open scoped Valued in
/-- **A uniformizer of `v.adicCompletionIntegers F` exists, unconditionally.** `Valued.v` is
`Valuation.IsRankOneDiscrete` for any Dedekind domain (Mathlib), so its generator is realized by
some `π : v.adicCompletion F` (`Valuation.IsRankOneDiscrete.generator_mem_range`). -/
theorem exists_isUniformizer_valued :
    ∃ π : v.adicCompletion F, Valuation.IsUniformizer (Valued.v : Valuation _ ℤᵐ⁰) π :=
  Valuation.IsRankOneDiscrete.generator_mem_range (v.adicCompletion F)
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)

open scoped Valued in
/-- **The threshold hypothesis `exp`/`log` need, derived from the residue characteristic.** If
`ResidueField (v.adicCompletionIntegers F)` has characteristic `p`, then `‖(p : v.adicCompletion
F)‖ < 1`: unwinding `CharP`, `(p : ResidueField _) = 0`, hence (naturality of the cast through the
residue map, `IsLocalRing.residue_eq_zero_iff`) `(p : v.adicCompletionIntegers F) ∈ maximalIdeal`,
hence (`valued_lt_one_of_mem_maximalIdeal`) `Valued.v (p : v.adicCompletion F) < 1`, hence (the norm
on `v.adicCompletion F` is compatible with `Valued.v`) the stated norm bound. -/
theorem norm_natCast_lt_one_of_charP_residueField (p : ℕ)
    [CharP (ResidueField (v.adicCompletionIntegers F)) p] :
    ‖(p : v.adicCompletion F)‖ < 1 := by
  have hzero : (p : ResidueField (v.adicCompletionIntegers F)) = 0 := CharP.cast_eq_zero _ p
  have hnat : (p : ResidueField (v.adicCompletionIntegers F))
      = residue (v.adicCompletionIntegers F) (p : v.adicCompletionIntegers F) := by
    rw [map_natCast]
  rw [hnat] at hzero
  have hmem : (p : v.adicCompletionIntegers F) ∈ maximalIdeal (v.adicCompletionIntegers F) :=
    (residue_eq_zero_iff _).mp hzero
  have hlt := valued_lt_one_of_mem_maximalIdeal v hmem
  have hcast : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) = (p : v.adicCompletion F) := by
    norm_cast
  rw [hcast] at hlt
  exact Valued.toNormedField.norm_lt_one_iff.mpr hlt

/-- **The membership hypothesis `NonarchimedeanExponentialFiltration`'s machinery needs**, for
`A := v.adicCompletionIntegers F`: membership matches the closed unit ball of the norm built from
`Valued.v` (`Langlands.NormMap`'s `instNontriviallyNormedFieldAdicCompletion`). -/
theorem mem_adicCompletionIntegers_iff_norm_le_one (x : v.adicCompletion F) :
    x ∈ v.adicCompletionIntegers F ↔ ‖x‖ ≤ 1 := by
  rw [mem_adicCompletionIntegers A F v, Valued.toNormedField.norm_le_one_iff]

open scoped Valued in
/-- **A uniformizer's norm is `< 1`**, phrased directly from `Valuation.IsUniformizer` (no need to
first extract the norm bound through `exists_isUniformizer_valued`'s existential): the same one-line
argument as `exists_uniformizer` uses internally (`Valued.toNormedField.norm_lt_one_iff`), extracted
as a standalone reusable fact so a *concrete* uniformizer already in hand (e.g. one constructed by
hand in a `NumberField`-visible file, where writing a fresh `‖·‖` type ascription risks the
`NormedField` instance diamond — see `ROADMAP.md` §6u/§6v) can get its norm bound without going
through `exists_uniformizer`'s existential at all. -/
theorem norm_lt_one_of_isUniformizer {π : v.adicCompletion F}
    (hπ : Valuation.IsUniformizer (Valued.v : Valuation _ ℤᵐ⁰) π) : ‖π‖ < 1 :=
  Valued.toNormedField.norm_lt_one_iff.mpr hπ.val_lt_one

open scoped Valued in
/-- **A uniformizer of `v.adicCompletionIntegers F`, as an element of that subring, with norm
`< 1` and generating its maximal ideal.** Packages `exists_isUniformizer_valued` into the exact
shape `NonarchimedeanExponentialFiltration`'s theorems need. -/
theorem exists_uniformizer :
    ∃ π : v.adicCompletionIntegers F, ‖(π : v.adicCompletion F)‖ < 1 ∧
      maximalIdeal (v.adicCompletionIntegers F) = Ideal.span ({π} : Set (v.adicCompletionIntegers F)) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_valued v (F := F)
  have hπlt : ‖π‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hπ.val_lt_one
  have hπmem : π ∈ v.adicCompletionIntegers F :=
    (mem_adicCompletionIntegers_iff_norm_le_one v π).mpr hπlt.le
  refine ⟨⟨π, hπmem⟩, hπlt, ?_⟩
  exact hπ.is_generator (π := (⟨π, hπmem⟩ : v.adicCompletionIntegers F))

/-- **Every positive accuracy is reached by a deep enough filtration level.** For any `ε > 0`, some
`i₀` has `‖x‖ < ε` for every `x ∈ 𝔪^i` with `i ≥ i₀`: a uniformizer's powers tend to `0`
(`exists_pow_lt_of_lt_one`) and bound the filtration levels
(`norm_le_pow_of_mem_maximalIdeal_pow`). This is the accuracy-parametrized form of
`exists_maximalIdeal_pow_lt_convergenceRadius` below, used wherever the target neighbourhood is
produced by continuity of some map rather than fixed in advance. -/
theorem exists_maximalIdeal_pow_norm_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : v.adicCompletionIntegers F,
      x ∈ maximalIdeal (v.adicCompletionIntegers F) ^ i → ‖(x : v.adicCompletion F)‖ < ε := by
  obtain ⟨π, hπnorm, hπ⟩ := exists_uniformizer v (F := F)
  obtain ⟨i₀, hi₀⟩ := exists_pow_lt_of_lt_one hε hπnorm
  refine ⟨i₀, fun i hi x hx => ?_⟩
  refine lt_of_le_of_lt (norm_le_pow_of_mem_maximalIdeal_pow (v.adicCompletionIntegers F)
    (mem_adicCompletionIntegers_iff_norm_le_one v) hπ hx) ?_
  exact lt_of_le_of_lt (pow_le_pow_of_le_one (norm_nonneg _) hπnorm.le hi) hi₀

variable [CharZero F] (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers F)) p]

/-- **The concrete instantiation, for `exp`.** Some explicit `i₀` has every `x ∈ 𝔪^i` (`i ≥ i₀`) of
`v.adicCompletionIntegers F` inside `NonarchimedeanExponential.exp`'s convergence domain. Assembles
`exists_uniformizer`, `norm_natCast_lt_one_of_charP_residueField`, and
`NonarchimedeanExponential.exists_forall_mem_maximalIdeal_pow_norm_lt_convergenceRadius`. -/
theorem exists_maximalIdeal_pow_lt_convergenceRadius :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : v.adicCompletionIntegers F,
      x ∈ maximalIdeal (v.adicCompletionIntegers F) ^ i →
        ‖(x : v.adicCompletion F)‖ < convergenceRadius (v.adicCompletion F) p := by
  obtain ⟨π, hπnorm, hπ⟩ := exists_uniformizer v (F := F)
  exact exists_forall_mem_maximalIdeal_pow_norm_lt_convergenceRadius (v.adicCompletionIntegers F)
    (mem_adicCompletionIntegers_iff_norm_le_one v)
    (norm_natCast_lt_one_of_charP_residueField v p) hπ hπnorm

/-- The `log`-domain analogue of `exists_maximalIdeal_pow_lt_convergenceRadius`. -/
theorem exists_maximalIdeal_pow_lt_logConvergenceRadius :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : v.adicCompletionIntegers F,
      x ∈ maximalIdeal (v.adicCompletionIntegers F) ^ i →
        ‖(x : v.adicCompletion F)‖ < logConvergenceRadius (v.adicCompletion F) p := by
  obtain ⟨π, hπnorm, hπ⟩ := exists_uniformizer v (F := F)
  exact exists_forall_mem_maximalIdeal_pow_norm_lt_logConvergenceRadius (v.adicCompletionIntegers F)
    (mem_adicCompletionIntegers_iff_norm_le_one v)
    (norm_natCast_lt_one_of_charP_residueField v p) hπ hπnorm

omit [CharP (ResidueField (v.adicCompletionIntegers F)) p] in
/-- **The concrete instantiation of `NonarchimedeanExponential.exists_pow_lt_logUnitsThreshold` for
`v.adicCompletion F`.** Some `i₀` has `‖π‖ ^ i < logUnitsThreshold (v.adicCompletion F) p` for every
`i ≥ i₀`, given `‖π‖ < 1`. Baking `K := v.adicCompletion F` at THIS (`NumberField`-free) file's
elaboration site, rather than leaving `K` fully generic, is what keeps this diamond-free when
consumed at a `NumberField`-visible call site: `[NormedField K]` is resolved once here — uniquely,
since only this repo's own instance is reachable from this file — rather than re-resolved (and
ambiguously so) at the call site. -/
theorem exists_pow_lt_logUnitsThreshold {π : v.adicCompletion F} (hπnorm : ‖π‖ < 1) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ‖π‖ ^ i < NonarchimedeanExponential.logUnitsThreshold (v.adicCompletion F) p :=
  NonarchimedeanExponential.exists_pow_lt_logUnitsThreshold hπnorm

/-- **The concrete instantiation of `NonarchimedeanExponential.expEquiv` for
`v.adicCompletionIntegers F`.** `U^{(i)} ≅ (𝔪^i, +)`, for a uniformizer `π` of
`v.adicCompletionIntegers F` and `i` above the strict `logUnitsThreshold` threshold. As with
`exists_pow_lt_logUnitsThreshold` above, baking `A := v.adicCompletionIntegers F` (hence `K :=
v.adicCompletion F`) at THIS `NumberField`-free file's elaboration site — rather than leaving
`expEquiv`'s `A`/`K` fully generic — is exactly what keeps this diamond-free when consumed at a
`NumberField`-visible call site: `[NormedField K]` and `A`'s own `ValuationSubring K` structure are
both resolved once here (unambiguously), rather than re-resolved at the call site, where a fresh
`(A := ...)` on the *generic* `expEquiv` would force eager `[NormedField K]` instance search there
and risk picking Mathlib's competing `absNorm`-based instance instead of this repo's. -/
noncomputable def expEquiv (hnorm : ‖(p : v.adicCompletion F)‖ < 1)
    {π : v.adicCompletionIntegers F}
    (hπ : maximalIdeal (v.adicCompletionIntegers F) = Ideal.span ({π} : Set (v.adicCompletionIntegers F)))
    (hπ0 : (π : v.adicCompletion F) ≠ 0) (hπnorm : ‖(π : v.adicCompletion F)‖ < 1) {i : ℕ}
    (hthreshStrict :
      ‖(π : v.adicCompletion F)‖ ^ i < NonarchimedeanExponential.logUnitsThreshold (v.adicCompletion F) p) :
    Multiplicative ↥(maximalIdeal (v.adicCompletionIntegers F) ^ i) ≃*
      ↥(ValuationSubring.principalUnitsPow (v.adicCompletionIntegers F) i) :=
  NonarchimedeanExponential.expEquiv (A := v.adicCompletionIntegers F)
    (hA := mem_adicCompletionIntegers_iff_norm_le_one v) hnorm hπ hπ0 hπnorm hthreshStrict

end IsDedekindDomain.HeightOneSpectrum

end
