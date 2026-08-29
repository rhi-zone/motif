import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Ramification index / inertia degree multiplicativity for towers of number fields, in
`HeightOneSpectrum` vocabulary

Let `K ⊆ L` be a tower of number fields, `v : HeightOneSpectrum (𝓞 K)` a place lying over a
rational prime `p`, and `w : HeightOneSpectrum (𝓞 L)` a place lying over `v`. This file bridges
this repo's `HeightOneSpectrum`/`Ideal.ramificationIdx'`/`Ideal.inertiaDeg'` vocabulary with the
absolute (relative-to-`ℤ`) ramification/inertia facts that `Mathlib.NumberTheory.NumberField.
Cyclotomic.Ideal` and similar files state in terms of Mathlib's newer, Galois-orbit-based
`Ideal.ramificationIdx`/`Ideal.inertiaDeg` (unprimed) — the vocabulary in which "the ramification
index of the rational prime `p` in a number field `F`" is most directly available.

This is a **generic bridge**, not specific to cyclotomic fields: it applies to any tower of number
fields `K ⊆ L` with a chosen chain of places over a rational prime. It composes two pieces already
in Mathlib that had not previously been chained together in this repository:

1. `Ideal.ramificationIdx'_eq_ramificationIdx` / `Ideal.inertiaDeg'_eq_inertiaDeg`: the bridge
   between this repo's `ramificationIdx'`/`inertiaDeg'` (defined via `sSup`/quotient `finrank`,
   the vocabulary `IsTotallyRamified` and its supporting files are stated in) and Mathlib's newer
   `ramificationIdx`/`inertiaDeg` (defined via the length of a localized quotient module /
   residue-field extension degree, the vocabulary `NumberField.Cyclotomic.Ideal`'s concrete
   formulas are stated in).
2. `Ideal.ramificationIdx'_algebra_tower'` / `Ideal.inertiaDeg'_algebra_tower`: multiplicativity of
   the primed invariants across a tower of Dedekind domains `R → S → T` (here `ℤ → 𝓞 K → 𝓞 L`).

Composing (1) at each of the two tower levels (`ℤ → 𝓞 K` and `ℤ → 𝓞 L`) with (2) (`ℤ → 𝓞 K → 𝓞 L`)
gives, directly, the ramification index/inertia degree of `p` in `L` as the product of the
corresponding invariant of `p` in `K` and the `HeightOneSpectrum`-level invariant of `w` over `v` —
exactly the form needed to read off `v.asIdeal.ramificationIdx' w.asIdeal` from two "absolute"
facts about `p` in `K` and in `L` (as `NumberField.Cyclotomic.Ideal` supplies for cyclotomic
fields), without ever exhibiting `w.asIdeal` as an explicit ideal or invoking a going-up theorem.

## Main results

* `liesOver_span_int` : `w` lies over the rational prime `p`, given `w` lies over `v` and `v` lies
  over `p`.
* `ramificationIdx_int_eq_mul_ramificationIdx'` : the absolute ramification index of `p` in `L`
  equals the absolute ramification index of `p` in `K` times the relative ramification index of
  `w` over `v`.
* `inertiaDeg_int_eq_mul_inertiaDeg'` : the analogous multiplicativity for inertia degrees.
-/

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

open Ideal NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [hlies : w.asIdeal.LiesOver v.asIdeal]
  {p : ℕ} [hp : Fact p.Prime] [hliesp : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]

theorem span_int_ne_bot : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  simpa [Ideal.span_singleton_eq_bot] using hp.out.ne_zero

include v hlies hliesp
omit [NumberField K] [NumberField L] hp in
/-- `w.asIdeal.LiesOver (span {(p : ℤ)})`, transported from `v.asIdeal.LiesOver (span {(p : ℤ)})`
and `w.asIdeal.LiesOver v.asIdeal` by transitivity of `Ideal.LiesOver`. Stated as a `theorem`
rather than an `instance`: `p` only appears inside hypotheses, not the conclusion, so instance
search cannot determine it — callers register it locally via `haveI`. -/
theorem liesOver_span_int : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) where
  over := by
    rw [Ideal.over_def v.asIdeal (Ideal.span {(p : ℤ)}), Ideal.over_def w.asIdeal v.asIdeal,
      Ideal.under_under]

include hp
/-- **The ramification-index bridge.** The (Mathlib, relative-to-`ℤ`) ramification index of the
rational prime `p` in `L` is the ramification index of `p` in `K` times the `HeightOneSpectrum`
(`ramificationIdx'`) ramification index of `w` over `v`. -/
theorem ramificationIdx_int_eq_mul_ramificationIdx' :
    Ideal.ramificationIdx w.asIdeal ℤ =
      Ideal.ramificationIdx v.asIdeal ℤ * v.asIdeal.ramificationIdx' w.asIdeal := by
  haveI := liesOver_span_int (p := p) v w
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ w.asIdeal (span_int_ne_bot (p := p)),
    Ideal.ramificationIdx'_algebra_tower' (Ideal.span {(p : ℤ)}) v.asIdeal w.asIdeal,
    Ideal.ramificationIdx'_eq_ramificationIdx _ v.asIdeal (span_int_ne_bot (p := p))]

/-- **The inertia-degree bridge.** The (Mathlib, relative-to-`ℤ`) inertia degree of the rational
prime `p` in `L` is the inertia degree of `p` in `K` times the `HeightOneSpectrum`
(`inertiaDeg'`) inertia degree of `w` over `v`. -/
theorem inertiaDeg_int_eq_mul_inertiaDeg' :
    Ideal.inertiaDeg w.asIdeal ℤ =
      Ideal.inertiaDeg v.asIdeal ℤ * v.asIdeal.inertiaDeg' w.asIdeal := by
  haveI := liesOver_span_int (p := p) v w
  haveI := HeightOneSpectrum.isMaximal v
  haveI := HeightOneSpectrum.isMaximal w
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    (Ideal.span_singleton_prime (p := (p : ℤ)) (by exact_mod_cast hp.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp.out) |>.isMaximal (span_int_ne_bot (p := p))
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) w.asIdeal,
    Ideal.inertiaDeg'_algebra_tower (Ideal.span {(p : ℤ)}) v.asIdeal w.asIdeal,
    Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal]

end IsDedekindDomain.HeightOneSpectrum

end
