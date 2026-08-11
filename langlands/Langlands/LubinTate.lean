import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Lubin-Tate power series: the defining congruences, and existence of `f_π`

Opens a new route toward local class field theory for this repo — Lubin-Tate theory, the
ramified/hard half of local CFT and the route that connects to representation-theoretic / local
Langlands machinery (as opposed to the purely cohomological route Phase 2/2a/2b pursued). This is
the first file of that thread.

For a complete discrete valuation ring `O` with uniformizer `π` and finite residue field of size
`q`, the classical Lubin-Tate construction singles out the set `ℱ_π` of `f ∈ O⟦X⟧` satisfying:

* `f ≡ πX (mod deg 2)`, i.e. `f`'s constant term is `0` and its linear coefficient is `π`.
* `f ≡ X^q (mod π)`, i.e. reducing every coefficient of `f` mod `π` (equivalently, applying
  `PowerSeries.map` along the residue homomorphism `O → O ⧸ 𝔪`) gives exactly `X^q`.

This file states those two congruences precisely (`IsLubinTatePoly`) and proves `ℱ_π` is nonempty
(`exists_isLubinTatePoly`).

## What this does *not* close, and why

**Existence of *some* `f ∈ ℱ_π` is genuinely easy, not a deep Hensel-style limiting argument.**
The explicit polynomial `f₀(X) := π•X + X^q` satisfies both congruences directly: its constant and
linear coefficients are read off `C π * X` and `X^q` separately (no interaction between the two
summands at degrees `0` and `1`, since `q ≥ 2` — guaranteed here since a finite field has at least
two elements, `Finite.one_lt_card`), and reducing mod `π` kills the `π•X` term outright
(`π` lies in the maximal ideal by definition of uniformizer) leaving exactly `X^q`. No use of
completeness of `O` is needed for this step, and `f₀` is literally the standard textbook example
(Serre, *Local Fields* Ch. IV; Lubin–Tate 1965) — not evidence that the theory is shallow, but a
sign that the real content lies elsewhere.

**Uniqueness of `f_π` "up to exactly the two stated congruence conditions" is false, and is not
attempted.** `ℱ_π` is genuinely infinite: `f₀` and `f₀ + π•X^2` are both in `ℱ_π` (their difference
`π•X^2` vanishes to order `≥ 2` and vanishes mod `π`), so no uniqueness statement pinning down a
*single* `f_π` from these two congruences alone can be true. This is not a scope-narrowing
weakening of the target — it is a direct counterexample to the literal statement requested, and no
weakened-but-true replacement is substituted in its place.

**The genuine deep content — where completeness and a real Hensel/successive-approximation
argument are actually needed — is the *functional equation lemma*: given `f, g ∈ ℱ_π` (for the
same or different uniformizers) and a linear starting form, there is a unique power series `φ`
(in one or several variables) with `φ ≡` that linear form `(mod deg 2)` intertwining `f` and `g`,
built by solving one linear equation in `O` per total-degree step, feasible precisely because `f`'s
`πX`/`X^q` congruences make the degree-`n` equation invertible for every `n`. Specializing this
lemma to `f = g` produces the associated formal group law `F_π` with `f` as an endomorphism (the
stretch goal `ROADMAP.md` scopes as item 4). That lemma is substantial 2-variable formal power
series machinery (total-degree induction, `MvPowerSeries.subst`, a fresh coefficient-recursion
argument genuinely comparable in scope to this repo's `exp`/`log` thread) and is not attempted in
this file; see `ROADMAP.md`'s entry for this pass for the precise remaining gap.

## Main results

* `IsLubinTatePoly` : the two defining congruences for `f ∈ ℱ_π`.
* `exists_isLubinTatePoly` : `ℱ_π` is nonempty, via the explicit witness `π • X + X ^ q`.
* `not_forall_isLubinTatePoly_eq` : `ℱ_π` is not a singleton — `f₀` and `f₀ + π • X ^ 2` are
  distinct elements of it — the direct counterexample underlying the "uniqueness is false" claim
  above.

## References

* J. Lubin, J. Tate, *Formal complex multiplication in local fields*, Ann. of Math. 81 (1965).
* J-P. Serre, *Local Fields*, Ch. IV.
-/

@[expose] public section

noncomputable section

open PowerSeries IsLocalRing

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The Lubin-Tate defining congruences for `f ∈ O⟦X⟧`**, relative to a fixed element `π : O`
(intended to be a uniformizer) and a fixed natural number `q` (intended to be the size of the
residue field):

* `f ≡ πX (mod deg 2)`: constant term `0`, linear coefficient `π`.
* `f ≡ X^q (mod π)`: the image of `f` under `PowerSeries.map` along the residue homomorphism
  `residue O : O →+* ResidueField O` is exactly `X ^ q`.
-/
def IsLubinTatePoly (π : O) (q : ℕ) (f : O⟦X⟧) : Prop :=
  coeff 0 f = 0 ∧ coeff 1 f = π ∧
    PowerSeries.map (residue O) f = (X : (ResidueField O)⟦X⟧) ^ q

/-- The residue field's size, as a natural number (`0` if `ResidueField O` is infinite). -/
abbrev residueCard (O : Type*) [CommRing O] [IsLocalRing O] : ℕ := Nat.card (ResidueField O)

variable [Finite (ResidueField O)]

/-- The residue field of a discrete valuation ring is finite (by hypothesis) and a field, hence
has at least two elements. -/
theorem two_le_residueCard : 2 ≤ residueCard O := Finite.one_lt_card

/-- **The standard explicit witness `f₀ := π • X + X ^ q`.** -/
def basicPoly (π : O) (q : ℕ) : O⟦X⟧ := PowerSeries.C π * X + X ^ q

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
@[simp] theorem coeff_zero_basicPoly (π : O) (q : ℕ) (hq : q ≠ 0) :
    coeff 0 (basicPoly π q) = 0 := by
  rw [basicPoly, map_add, coeff_C_mul, coeff_X, coeff_X_pow,
    if_neg (by omega : (0 : ℕ) ≠ 1), if_neg (Ne.symm hq)]
  ring

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
@[simp] theorem coeff_one_basicPoly (π : O) (q : ℕ) (hq : q ≠ 1) :
    coeff 1 (basicPoly π q) = π := by
  rw [basicPoly, map_add, coeff_C_mul, coeff_X, coeff_X_pow, if_pos rfl, if_neg (Ne.symm hq)]
  ring

omit [Finite (ResidueField O)] in
/-- Reducing `basicPoly π q` mod `π` (via `PowerSeries.map (residue O)`) gives exactly `X ^ q`,
since `residue O π = 0` for `π` a uniformizer (its associated maximal ideal contains `π`). -/
theorem map_residue_basicPoly {π : O} (hπ : Irreducible π) (q : ℕ) :
    PowerSeries.map (residue O) (basicPoly π q) = (X : (ResidueField O)⟦X⟧) ^ q := by
  have hπ0 : residue O π = 0 :=
    (residue_eq_zero_iff π).mpr
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸
        Ideal.mem_span_singleton_self π)
  simp [basicPoly, hπ0]

/-- **Existence of a Lubin-Tate polynomial.** For `π` a uniformizer of `O` and `q := residueCard O`
(so `q ≥ 2` since the residue field is finite), the explicit `basicPoly π q := π•X + X^q` satisfies
both defining congruences. -/
theorem exists_isLubinTatePoly {π : O} (hπ : Irreducible π) :
    ∃ f : O⟦X⟧, IsLubinTatePoly π (residueCard O) f := by
  have hq2 : 2 ≤ residueCard O := two_le_residueCard
  refine ⟨basicPoly π (residueCard O),
    coeff_zero_basicPoly π _ (by omega), coeff_one_basicPoly π _ (by omega),
    map_residue_basicPoly hπ _⟩

omit [Finite (ResidueField O)] in
/-- **`ℱ_π` is not a singleton: no uniqueness statement can hold from the two congruences alone.**
`basicPoly π q` and `basicPoly π q + C π * X ^ 2` are two distinct Lubin-Tate polynomials for the
same `π`, `q ≥ 2`: the perturbation `C π * X ^ 2` never disturbs the degree-`0`/`1` congruence (it
vanishes there) nor the mod-`π` congruence (it is itself a multiple of `π`), yet it changes the
degree-`2` coefficient by exactly `π ≠ 0`, so the two witnesses are honestly distinct. This is the
direct counterexample underlying the "uniqueness up to the two stated congruences is false" claim
in this file's module docstring. -/
theorem not_isLubinTatePoly_uniqueness {π : O} (hπ : Irreducible π) (hπ0 : π ≠ 0)
    {q : ℕ} (hq2 : 2 ≤ q) :
    ∃ f g : O⟦X⟧, IsLubinTatePoly π q f ∧ IsLubinTatePoly π q g ∧ f ≠ g := by
  set f := basicPoly π q with hf
  set g := basicPoly π q + PowerSeries.C π * X ^ 2 with hg
  have hf0 : coeff 0 f = 0 := coeff_zero_basicPoly π q (by omega)
  have hf1 : coeff 1 f = π := coeff_one_basicPoly π q (by omega)
  have hfmap : PowerSeries.map (residue O) f = (X : (ResidueField O)⟦X⟧) ^ q :=
    map_residue_basicPoly hπ q
  have hπ0' : residue O π = 0 :=
    (residue_eq_zero_iff π).mpr
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸
        Ideal.mem_span_singleton_self π)
  have hpert0 : coeff 0 (PowerSeries.C π * X ^ 2 : O⟦X⟧) = 0 := by
    simp [coeff_C_mul, coeff_X_pow]
  have hpert1 : coeff 1 (PowerSeries.C π * X ^ 2 : O⟦X⟧) = 0 := by
    simp [coeff_C_mul, coeff_X_pow]
  have hpert2 : coeff 2 (PowerSeries.C π * X ^ 2 : O⟦X⟧) = π := by
    simp [coeff_C_mul, coeff_X_pow]
  have hpertmap : PowerSeries.map (residue O) (PowerSeries.C π * X ^ 2 : O⟦X⟧) = 0 := by
    simp [map_C, map_X, hπ0']
  refine ⟨f, g, ⟨hf0, hf1, hfmap⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hg, map_add, hf0, hpert0, add_zero]
  · rw [hg, map_add, hf1, hpert1, add_zero]
  · rw [hg, map_add, hfmap, hpertmap, add_zero]
  · intro hfg
    have hcoeff2 : coeff 2 f = coeff 2 g := by rw [hfg]
    rw [hg, map_add, hpert2] at hcoeff2
    exact hπ0 (by linear_combination -hcoeff2)

end LubinTate

end

end
