import Langlands.LubinTateEisensteinQ
import Langlands.LubinTateWeierstrassPreparation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The general inductive Lubin-Tate tower step: Eisenstein-ness at a moving base

Once `Gal(K_1/K) ≃* (O/π)ˣ` is known for the level-`1` Lubin-Tate extension, the natural next step is
generalizing to the tower `K_n := K(F_π[π^n])`. The DIRECT route — applying
`LubinTateWeierstrassPreparation` to `iter f n` (`Langlands.LubinTate.iter`, already fully generic
over `n`, `IsLubinTatePoly (π^n) (q^n) (iter f n)`, `Langlands.LubinTateIterate.isLubinTatePoly_iter`)
— is DEAD for `n ≥ 2`: the Weierstrass factor's own constant-coefficient-associate fact
(`Langlands.LubinTateWeierstrassPreparation.coeff_one_associated_of_eq_mul`) ties `Q_n`'s constant
term to an associate of `(iter f n).coeff 1 = π ^ n`
(`Langlands.LubinTateIterate.coeff_one_iter`), which lies in `𝔪 ^ n ⊆ 𝔪 ^ 2` once `n ≥ 2` — exactly
what `Polynomial.irreducible_of_eisenstein_criterion` excludes.

The classical route (Serre, *Local Fields* Ch. IV; Washington Ch. 7) is instead **inductive over
fields**: `K_n = K_{n-1}(α_n)`, where `α_n` is chosen so `f(α_n) = α_{n-1}` for `α_{n-1}` a fixed
generator of the primitive `π^{n-1}`-torsion (`f` itself — the *original* Lubin-Tate series, not
`iter f n`) and `α_{n-1}` a uniformizer of `O_{n-1} := 𝒪[K_{n-1}]`. The Eisenstein polynomial at
step `n` is `f(X) - α_{n-1}`, over the *moving* base `O_{n-1}`, not `f` or `iter f n` themselves —
Eisenstein-ness comes from `α_{n-1}` being a uniformizer of `O_{n-1}` (valuation exactly `1` *there*,
not from any relation to `O`'s own `π`).

## What this file does

**The Eisenstein-existence half of one inductive step, parametrized over an arbitrary moving base
`O'` — not hardcoded to `n = 2`, not a substitution instance of the `n = 1` theorems.** Given:

* `O'`, an arbitrary complete discrete valuation ring (playing the role of `O_{n-1}`, the ring of
  integers of the previous tower level);
* `ψ : O →+* O'`, a *local* ring homomorphism (`[IsLocalHom ψ]`) from the original `O` — the
  composite `O → O_1 → ⋯ → O_{n-1}` of the tower so far;
* `α' : O'`, an irreducible element of `O'` (a uniformizer of the previous level, in the induction's
  intended use: a generator of the primitive `π^{n-1}`-torsion);

`shifted f ψ α' := (PowerSeries.map ψ f) - PowerSeries.C α'` is the base-changed, shifted series
`f(X) - α'`, and this file shows it has a Weierstrass factor `P'` over `O'` that is **Eisenstein at
`𝔪_{O'}`** (`isEisensteinAt_shifted`) — `P'.coeff 0` an associate of `α'` itself, sharply (not
merely `∈ 𝔪_{O'}`), by the *same technique* `LubinTateWeierstrassPreparation.coeff_zero_eq_zero_of_
eq_mul`/`coeff_one_associated_of_eq_mul` use (comparing `f = (P:O⟦X⟧)*u` at a fixed coefficient
index against `u`'s unit constant term), read at index `0` directly against a possibly-nonzero
target `α'` rather than `0` (`coeff_zero_associated_of_eq_mul`, this file's one new general
coefficient-shift lemma — simpler than `coeff_one_associated_of_eq_mul`, since there is no `X`-factor
to peel off: unlike the `n = 1` step, `0` is *not* a root of `shifted f ψ α'` (its constant term is
`-α' ≠ 0`), so the Weierstrass factor `P'` itself, not `P'.divX`, is directly the Eisenstein
polynomial the induction needs).

**No `ValuativeRel`/`spectralNorm` bridge is needed for this half**, and none is built here — see
"## Why no bridge is needed for this half" below for why that is not merely an oversight.

## Main results

* `coeff_zero_associated_of_eq_mul` : general coefficient-shift fact, the index-`0` analogue of
  `LubinTateWeierstrassPreparation.coeff_one_associated_of_eq_mul` at a general (possibly nonzero)
  target coefficient.
* `shifted` : the base-changed, shifted power series `f(X) - α'` at a moving base `O'`.
* `coeff_zero_shifted` : `(shifted f ψ α').coeff 0 = -α'`.
* `map_residue_shifted` : the residue-field congruence `(shifted f ψ α').map (residue O') = X ^ q`,
  given `α' ∈ 𝔪_{O'}` and `[IsLocalHom ψ]` — the two inputs Mathlib's Weierstrass preparation
  theorem needs, obtained by pushing `f`'s own congruence `f.map (residue O) = X ^ q` forward along
  the induced residue-field map `IsLocalRing.ResidueField.map ψ`.
* `exists_isWeierstrassFactorization_shifted` : `shifted f ψ α'` has a Weierstrass factorization
  `P' * u'` over `O'`, `P'` distinguished of degree `q := residueCard O`, with `P'.coeff 0` an
  associate of `α'`.
* `isEisensteinAt_shifted` : `P'` itself (no `divX` peel, unlike the `n = 1` case) is Eisenstein at
  `𝔪_{O'}` — assembled from `exists_isWeierstrassFactorization_shifted` and
  `LubinTateEisensteinQ`'s already-fully-general
  `Polynomial.irreducible_of_isWeaklyEisensteinAt_associated`'s hypothesis package (monic,
  weakly-Eisenstein, positive degree, sharp constant-term-associate), packaged directly as
  `IsEisensteinAt` rather than jumping straight to `Irreducible`, so callers needing the raw
  Eisenstein data (e.g. for `Polynomial.IsEisensteinAt.isIntegral` / monogenicity, not just
  irreducibility) are not forced through irreducibility first.
* `irreducible_shifted` / `irreducible_map_shifted` : `P'` (resp. its image in `K' := Frac(O')`) is
  irreducible — direct corollaries via `LubinTateEisensteinQ`'s existing (already fully general, not
  modified here) `Polynomial.irreducible_of_isWeaklyEisensteinAt_associated`/
  `irreducible_map_of_isWeaklyEisensteinAt_associated`.

## Why no bridge is needed for this half

A general `ValuativeRel ↔ spectralNorm`/`NormedField` bridge reusing
`Langlands.TotallyRamifiedEisenstein.isEisensteinAt_minpoly_of_isUniformizer` (a totally-ramified
Eisenstein theorem stated for `O := ↥(ValuativeRel.valuation K).valuationSubring`, the *specific*
`ValuativeRel`-canonical valuation subring, not an abstract DVR) is not built, and this file does not
need it. Reading that theorem's proof against `LubinTateEisensteinQ.lean`'s abstract-`O` machinery (as
used throughout the rest of the Lubin-Tate arc: `[IsDiscreteValuationRing O] [Algebra O K]
[IsFractionRing O K]`, with `O`'s image in `K`'s closed unit ball an explicit hypothesis `hOK`, *not*
derived from `O` being literally the valuation subring) shows why: `isEisensteinAt_minpoly_of_isUniformizer`'s
proof needs `hcoeffs : ∀ i, (minpoly K π).coeff i ∈ O`, obtained via `mem_valuationSubring_iff_norm_le_one`
— i.e. it needs `O` to contain **every** element of `K` of norm `≤ 1`, not merely to have its own
image land inside the closed unit ball (`hOK`'s direction). This is a strictly stronger fact than
`hOK` supplies, and is false for an *arbitrary* abstract `O` satisfying only `hOK`: `hOK` is
compatible with `O`'s image being a proper subring of the closed unit ball. Closing this gap for an
*arbitrary* `O'` would need proving `O'` literally equals (or is isomorphic to) `(valuation
K').valuationSubring` for some `ValuativeRel K'` compatible with `K'`'s norm — a standing, unresolved,
general architectural question, not specific to this tower-generalization task. At *concrete*
instantiations (`O := v.adicCompletionIntegers F`, `K := v.adicCompletion F`) the needed instances
resolve automatically via `#synth` (the ambient `Valued` structure already supplies a compatible
`ValuativeRel`), so the bridge is a non-problem there; but no general bridge from an *abstract*
`hOK`-style `O` to a `ValuativeRel`-canonical valuation subring has been built.

**This file's Eisenstein-existence step does not need that bridge at all.** Weierstrass preparation
(`PowerSeries.exists_isWeierstrassFactorization`) needs only `g.map (residue O') ≠ 0` and `[
IsAdicComplete (maximalIdeal O') O']` — no norm, no `ValuativeRel`, nothing beyond `O'` being an
abstract complete local ring. `LubinTateEisensteinQ`'s irreducibility criterion
(`Polynomial.irreducible_of_isWeaklyEisensteinAt_associated`) likewise needs only `[
IsDiscreteValuationRing O']` — no norm either. The `spectralNorm`/`NormedField` package (and the
`ValuativeRel ↔ NormedField` question) enters the Lubin-Tate arc only *after* irreducibility is
established, to compute the exact root valuation and separability
(`LubinTate.spectralNorm_eq_of_isLubinTatePoly_root`, `LubinTate.separable_map_divX_of_
isLubinTatePoly`) — and those lemmas are *already* stated with no dependency on how `O'` relates to
`K'`'s valuation ring beyond the explicit `hOK`/`hπnorm`-style hypotheses this whole arc already uses
throughout, so they apply verbatim to `P'` here with no new bridging work, once `O'` and `K' :=
Frac(O')` are supplied. What remains genuinely open — constructing `O'` itself (see below) — is a
different problem from the `ValuativeRel` bridge, and is not attempted here either.

## What remains open — the moving-base construction

This file takes `O'`, `ψ`, and `α'` as **hypotheses** — it does not construct `O_{n-1}` from `O_{n-2}`
and a chosen torsion generator. Constructing it (as, e.g., the integral closure of `O` in `K_{n-1} :=
(P_{n-1}.map …).SplittingField`, or as `{x : K_{n-1} | ‖x‖ ≤ 1}`) and proving it is again a complete
discrete valuation ring with the *same* residue field as `O` ("total ramification", load-bearing at
every step of the induction) is a **separate, unclosed problem**.

The `[IsAdicComplete (maximalIdeal O') O']` hypothesis this section carries is now dischargeable at
the concrete `O' := O_{K_1} := ↥(NormedField.valuation (K := K_1 P)).valuationSubring`
instantiation, given `K_1 P` separable over `K` and `K`'s residue field finite
(`IsDedekindDomain.HeightOneSpectrum.isAdicComplete_valuationSubring_K_1_of_adicCompletion`,
`Langlands/LubinTateSplittingFieldDVR.lean`).
What remains open, separately from that, is constructing `O_{n-1}` itself as an instance of an
*abstract* `IsDomain`/`IsDiscreteValuationRing` `O'` satisfying this section's hypothesis package —
i.e. proving `O_{K_1}` (or, at later steps, `O_{K_{n-1}}`) *is* an `IsDomain`/`IsDiscreteValuationRing`
ring in the sense this file's variables require (straightforward at `n = 1`, via
`LubinTate.isDiscreteValuationRing_valuationSubring_K_1`) and, crucially, has the **same residue field
as `O`** ("total ramification", load-bearing at every step of the induction). Mathlib has no lemma
constructing `IsDiscreteValuationRing`/`IsAdicComplete` instances for the integral closure of a DVR in
a `spectralNorm`-normed finite extension, and this repo's `Langlands.TowerValuationSubring`/
`Langlands.MonogenicMaximalOrder` build comparable integral-closure machinery only inside the
`ValuativeRel`/`ValuationSubring` formalism, not the `spectralNorm`/`NormedField` one
`K_1 := Q.SplittingField` (`Langlands.LubinTateSplittingField`) actually uses. This residue-field-preservation
gap, not `IsAdicComplete`, is what stands between this file's per-step Eisenstein fact and an actual
`baseChangeSplittingField` instantiation.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

open PowerSeries IsLocalRing Polynomial

namespace LubinTate

/-! ## A general coefficient-shift lemma -/

section CoeffShift

variable {R : Type*} [CommRing R]

/-- **Index-`0` analogue of `LubinTateWeierstrassPreparation.coeff_one_associated_of_eq_mul`, at a
general (possibly nonzero) target coefficient `c`.** If `g = P * u` with `u : R⟦X⟧` a unit power
series and `g.coeff 0 = c`, then `P.coeff 0` is an associate of `c` — no `IsDomain R` is actually
needed beyond what `Associated`/`IsUnit` already assume, but the ambient section variable is kept in
scope for uniformity with neighboring lemmas. Simpler than
`coeff_one_associated_of_eq_mul`: there is no lower-index term to cancel first (comparing `g = (P :
R⟦X⟧) * u` at `PowerSeries.coeff 0`, a ring homomorphism, gives `c = P.coeff 0 * constantCoeff u`
directly), and unlike `LubinTateWeierstrassPreparation.coeff_zero_eq_zero_of_eq_mul` (which needs `c
= 0` to cancel `constantCoeff u`, a unit, against a zero product) no hypothesis on `c` being zero or
nonzero is needed: `c = P.coeff 0 * constantCoeff u` exhibits the associate witness directly, for
every `c`. -/
theorem coeff_zero_associated_of_eq_mul {P : R[X]} {u : R⟦X⟧} (hu : IsUnit u) {g : R⟦X⟧}
    {c : R} (heq : g = (P : R⟦X⟧) * u) (hg0 : PowerSeries.coeff 0 g = c) :
    Associated (P.coeff 0) c := by
  have hmul : PowerSeries.constantCoeff g = P.coeff 0 * PowerSeries.constantCoeff u := by
    rw [heq, map_mul, Polynomial.constantCoeff_coe]
  rw [PowerSeries.coeff_zero_eq_constantCoeff] at hg0
  rw [hg0] at hmul
  exact ⟨(PowerSeries.isUnit_constantCoeff u hu).unit, by
    rw [IsUnit.unit_spec]; exact hmul.symm⟩

end CoeffShift

/-! ## The shifted series at a moving base -/

section Shifted

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {O' : Type*} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']

/-- **The shifted Lubin-Tate series at a moving base**: `f(X) - α'`, base-changed along
`ψ : O →+* O'`. The classical inductive tower step solves `f(X) = α_{n-1}` over `O_{n-1}`; this is
that equation rewritten as a zero set. -/
def shifted (f : O⟦X⟧) (ψ : O →+* O') (α' : O') : O'⟦X⟧ :=
  PowerSeries.map ψ f - PowerSeries.C α'

omit [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O'] [IsDiscreteValuationRing O'] in
/-- **The shifted series' constant coefficient is exactly `-α'`.** `f`'s own constant coefficient is
`0` (`IsLubinTatePoly`'s first congruence), so the base-changed `f.map ψ` has constant coefficient
`0` too, and subtracting `C α'` leaves `-α'`. -/
theorem coeff_zero_shifted (f : O⟦X⟧) (ψ : O →+* O') (α' : O')
    (hf0 : PowerSeries.coeff 0 f = 0) :
    PowerSeries.coeff 0 (shifted f ψ α') = -α' := by
  show PowerSeries.coeff 0 (PowerSeries.map ψ f - PowerSeries.C α') = -α'
  rw [map_sub, PowerSeries.coeff_map, hf0, map_zero, PowerSeries.coeff_C]
  simp

omit [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O'] [IsDiscreteValuationRing O'] in
/-- **`shifted` is natural in the target ring.** Pushing `shifted f ψ α'` forward along a ring
homomorphism `e : O' →+* O''` gives `shifted f (e.comp ψ) (e α')`: the shift-by-`α'` and the
base-change-along-`e` operations commute. Immediate from `shifted`'s definition
(`PowerSeries.map_comp`, `PowerSeries.map_C`). -/
theorem map_shifted {O'' : Type*} [CommRing O''] (f : O⟦X⟧) (ψ : O →+* O') (α' : O')
    (e : O' →+* O'') :
    PowerSeries.map e (shifted f ψ α') = shifted f (e.comp ψ) (e α') := by
  show PowerSeries.map e (PowerSeries.map ψ f - PowerSeries.C α') =
      PowerSeries.map (e.comp ψ) f - PowerSeries.C (e α')
  rw [map_sub, PowerSeries.map_C, PowerSeries.map_comp]
  rfl

/-- **The shifted series' residue-field image is exactly `X ^ q`**, given `α'` lies in `O'`'s maximal
ideal and `ψ` is a local ring homomorphism. Pushes `f`'s own congruence `f.map (residue O) = X ^ q`
forward along the induced residue-field map `IsLocalRing.ResidueField.map ψ`
(`IsLocalRing.ResidueField.map_comp_residue` identifies the two ways of composing `ψ` with the
residue maps of `O` and `O'`), then uses `α' ∈ 𝔪_{O'}` to see `C α'` vanishes under `residue O'`. -/
theorem map_residue_shifted {π : O} {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    (ψ : O →+* O') [IsLocalHom ψ] {α' : O'} (hα'mem : α' ∈ maximalIdeal O') :
    PowerSeries.map (residue O') (shifted f ψ α') =
      (PowerSeries.X : (ResidueField O')⟦X⟧) ^ (residueCard O) := by
  have hmapf : PowerSeries.map (residue O') (PowerSeries.map ψ f) =
      (PowerSeries.X : (ResidueField O')⟦X⟧) ^ (residueCard O) := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map,
      ← IsLocalRing.ResidueField.map_residue ψ]
    have hcoeffn : residue O (PowerSeries.coeff n f) =
        PowerSeries.coeff n ((PowerSeries.X : (ResidueField O)⟦X⟧) ^ (residueCard O)) := by
      rw [← PowerSeries.coeff_map, hf.2.2]
    rw [hcoeffn, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
    rcases eq_or_ne n (residueCard O) with hn | hn
    · rw [if_pos hn, if_pos hn]; simp
    · rw [if_neg hn, if_neg hn, map_zero]
  have hCzero : PowerSeries.map (residue O') (PowerSeries.C α') = (0 : (ResidueField O')⟦X⟧) := by
    rw [PowerSeries.map_C]
    have hz : residue O' α' = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hα'mem
    rw [hz, map_zero]
  show PowerSeries.map (residue O') (PowerSeries.map ψ f - PowerSeries.C α') = _
  rw [map_sub, hmapf, hCzero, sub_zero]

end Shifted

/-! ## Weierstrass preparation and Eisenstein-ness of the shifted series -/

section TowerStep

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {O' : Type*} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
  [IsAdicComplete (maximalIdeal O') O']

/-- **Weierstrass preparation for the shifted series, at a moving base `O'`.** Given `α' : O'`
irreducible (a uniformizer of `O'`) and `ψ : O →+* O'` local, `shifted f ψ α'` factors as `P' * u'`
with `P'` distinguished of degree `q := residueCard O` and `P'.coeff 0` an associate of `α'`. This is
the general inductive tower step's Weierstrass-preparation input: unlike the `n = 1` case (`P`'s
constant coefficient exactly `0`, `X ∣ P`), `P'`'s constant coefficient is *itself* the sharp
Eisenstein datum — no `divX` peel, since `0` is not a root of `shifted f ψ α'` (its constant term is
`-α' ≠ 0`). -/
theorem exists_isWeierstrassFactorization_shifted {π : O} {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) (ψ : O →+* O') [IsLocalHom ψ] {α' : O'}
    (hα' : Irreducible α') :
    ∃ (P' : O'[X]) (u' : O'⟦X⟧), P'.IsDistinguishedAt (maximalIdeal O') ∧ IsUnit u' ∧
      shifted f ψ α' = (P' : O'⟦X⟧) * u' ∧ P'.natDegree = residueCard O ∧
      Associated (P'.coeff 0) α' := by
  have hα'mem : α' ∈ maximalIdeal O' := (IsLocalRing.mem_maximalIdeal _).mpr hα'.not_isUnit
  have hne : PowerSeries.map (residue O') (shifted f ψ α') ≠ 0 := by
    rw [map_residue_shifted hf ψ hα'mem]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨P', u', hPu'⟩ := PowerSeries.exists_isWeierstrassFactorization hne
  have hdeg : P'.natDegree = residueCard O := by
    rw [hPu'.natDegree_eq_toNat_order_map, map_residue_shifted hf ψ hα'mem,
      PowerSeries.order_X_pow]
    rfl
  have hassocneg : Associated (P'.coeff 0) (-α') :=
    coeff_zero_associated_of_eq_mul hPu'.isUnit hPu'.eq_mul
      (coeff_zero_shifted f ψ α' hf.1)
  have hassoc : Associated (P'.coeff 0) α' := by
    obtain ⟨v, hv⟩ := hassocneg
    exact ⟨-v, by rw [Units.val_neg, mul_neg, hv, neg_neg]⟩
  exact ⟨P', u', hPu'.isDistinguishedAt, hPu'.isUnit, hPu'.eq_mul, hdeg, hassoc⟩

/-- **`P'` is Eisenstein at `𝔪_{O'}`** — the general inductive tower step's Eisenstein fact. Unlike
the `n = 1` case (`Q := P.divX`, since `P` itself has a trivial root at `0`), `P'` itself is
Eisenstein: its own constant coefficient is an associate of `α'` (sharp, not merely `∈ 𝔪_{O'}`), its
higher non-leading coefficients are in `𝔪_{O'}` (`IsDistinguishedAt`'s own defining data), and it is
monic. -/
theorem isEisensteinAt_shifted {π : O} {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    (ψ : O →+* O') [IsLocalHom ψ] {α' : O'} (hα' : Irreducible α') :
    ∃ (P' : O'[X]) (u' : O'⟦X⟧), IsUnit u' ∧ shifted f ψ α' = (P' : O'⟦X⟧) * u' ∧
      P'.natDegree = residueCard O ∧ P'.IsEisensteinAt (maximalIdeal O') := by
  obtain ⟨P', u', hPdist, hu', heq, hdeg, hassoc⟩ :=
    exists_isWeierstrassFactorization_shifted hf ψ hα'
  refine ⟨P', u', hu', heq, hdeg, hPdist.monic.isEisensteinAt_of_mem_of_notMem
    (maximalIdeal.isMaximal O').ne_top ?_ ?_⟩
  · intro n hn
    exact hPdist.toIsWeaklyEisensteinAt.mem hn
  · exact not_mem_sq_maximalIdeal_of_associated hα' hassoc

/-- **`P'` is irreducible over `O'`.** Direct corollary of `isEisensteinAt_shifted`'s data via
`LubinTateEisensteinQ`'s already fully general `Polynomial.irreducible_of_isWeaklyEisensteinAt_
associated` — no new irreducibility argument, and no `ValuativeRel`/`spectralNorm` machinery, is
needed for this step (see this file's module docstring, "Why no bridge is needed for this half"). -/
theorem irreducible_shifted {π : O} {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    (ψ : O →+* O') [IsLocalHom ψ] {α' : O'} (hα' : Irreducible α') (hq2 : 2 ≤ residueCard O) :
    ∃ (P' : O'[X]) (u' : O'⟦X⟧), IsUnit u' ∧ shifted f ψ α' = (P' : O'⟦X⟧) * u' ∧
      P'.natDegree = residueCard O ∧ Irreducible P' := by
  obtain ⟨P', u', hPdist, hu', heq, hdeg, hassoc⟩ :=
    exists_isWeierstrassFactorization_shifted hf ψ hα'
  have hqdeg : 0 < P'.natDegree := by rw [hdeg]; omega
  refine ⟨P', u', hu', heq, hdeg, Polynomial.irreducible_of_isWeaklyEisensteinAt_associated hα'
    hPdist.monic hPdist.toIsWeaklyEisensteinAt hqdeg hassoc⟩

/-- **`P'`'s image over `K' := Frac(O')` is irreducible.** Direct corollary via `LubinTateEisensteinQ`'s
`Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated` (Gauss's lemma). From here,
`LubinTate.spectralNorm_eq_of_isLubinTatePoly_root`-style spectral-norm and
`LubinTate.separable_map_divX_of_isLubinTatePoly`-style separability facts apply to `P'.map
(algebraMap O' K')` exactly as they do to `Q := P.divX` at `n = 1` — no `divX`, and no new
`spectralNorm` lemma, needed: `LubinTateEisensteinQ.lean`'s `spectralNorm_eq_norm_coeff_zero_rpow_
of_aeval_eq_zero` and `Polynomial.separable_of_isEisensteinAt_of_natDegree_norm_eq_one` are already
stated for an arbitrary monic irreducible polynomial over an arbitrary complete nonarchimedean field,
with no Lubin-Tate- or `n`-specific content, and apply here verbatim once `K'` is supplied. -/
theorem irreducible_map_shifted {π : O} {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    (ψ : O →+* O') [IsLocalHom ψ] {α' : O'} (hα' : Irreducible α') (hq2 : 2 ≤ residueCard O)
    {K' : Type*} [Field K'] [Algebra O' K'] [IsFractionRing O' K'] :
    ∃ (P' : O'[X]) (u' : O'⟦X⟧), IsUnit u' ∧ shifted f ψ α' = (P' : O'⟦X⟧) * u' ∧
      P'.natDegree = residueCard O ∧ Irreducible (P'.map (algebraMap O' K')) := by
  obtain ⟨P', u', hPdist, hu', heq, hdeg, hassoc⟩ :=
    exists_isWeierstrassFactorization_shifted hf ψ hα'
  have hqdeg : 0 < P'.natDegree := by rw [hdeg]; omega
  refine ⟨P', u', hu', heq, hdeg,
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hα' hPdist.monic
      hPdist.toIsWeaklyEisensteinAt hqdeg hassoc⟩

end TowerStep

end LubinTate

end
