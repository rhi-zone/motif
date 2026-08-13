import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Langlands.LubinTate

/-!
# Weierstrass preparation for Lubin-Tate power series

`ROADMAP.md` §29 named Weierstrass preparation as the remaining blocker for
`|piTorsion hπ hf 1| = q`: turning `f` (a Lubin-Tate power series, an *infinite* object) into a
genuine degree-`q` polynomial with the same roots, so that root-counting becomes a finite/algebraic
question. Mathlib's `Mathlib.RingTheory.PowerSeries.WeierstrassPreparation` (Jz Pan, 2025) already
proves the general Weierstrass preparation theorem for power series over a complete local ring, in
full generality with existence *and* uniqueness — **confirmed present, not absent, by reading the
file directly**, correcting this thread's initial premise (a `grep`/`loogle` pass before this file
existed had not turned it up). This file does not re-derive that theorem; it specializes Mathlib's
statement to the Lubin-Tate setting, checking the two hypotheses (`g`'s residue-field image nonzero,
and `O` adically complete) hold for `f`.

## Route

`IsLubinTatePoly π q f`'s third congruence, `f.map (residue O) = X ^ q` *exactly* (not just the
low-degree congruence used to define `q` classically), gives both of Mathlib's needed inputs at
once:

* `X ^ q ≠ 0` in `(ResidueField O)⟦X⟧` (any field is nontrivial), so `f.map (residue O) ≠ 0`
  (`map_residue_ne_zero`) — Mathlib's nonvanishing hypothesis.
* `(f.map (residue O)).order = q` follows from `PowerSeries.order_X_pow` rewritten along the same
  congruence (`order_map_residue_eq`), identifying the *order* used internally by Mathlib's
  `PowerSeries.IsWeierstrassDivisorAt`/`exists_isWeierstrassFactorization` with the residue-field
  size `q` directly, rather than needing to discover it — this is the "known Weierstrass degree in
  advance" simplification `ROADMAP.md` flagged as possibly easier, confirmed here to be genuinely
  available for `f` specifically.

Mathlib's `PowerSeries.exists_isWeierstrassFactorization` additionally needs `O` to be adically
complete with respect to its maximal ideal (`IsAdicComplete (IsLocalRing.maximalIdeal O) O`) — the
literal formalization of "complete DVR", the standing hypothesis of classical Lubin-Tate theory that
this repo's `O` (so far only `IsDomain`/`IsDiscreteValuationRing`/finite residue field) has not yet
needed to state. It is added here as a new typeclass assumption on `O`, exactly matching what the
classical theory requires — not a narrowing of scope, a hypothesis genuinely used by the argument.

## Main result

* `exists_isWeierstrassFactorization_of_isLubinTatePoly`: for `f` a Lubin-Tate power series (`hf :
  IsLubinTatePoly π (residueCard O) f`) over an adically-complete `O`, there is a distinguished
  polynomial `P : O[X]` of degree exactly `residueCard O` and a unit power series `u : O⟦X⟧` with
  `f = P * u`.

## What this does not do

**Does not yet connect the factorization to `piTorsion`.** Showing `piTorsion hπ hf 1` (the set of
`x` in `K`'s maximal ideal with `eval f x = 0`) coincides with `P`'s roots in `K`'s maximal ideal
needs: (a) `eval` compatibility with the factorization (`eval f x = eval P x * eval u x`, from
`NonarchimedeanPowerSeriesEval.eval_mul`), (b) `eval u x ≠ 0` for `x` in the maximal ideal (`u`'s
constant term is a unit, so `eval u x` stays close to it in the ultrametric — not yet proved here),
(c) identifying `NonarchimedeanPowerSeriesEval.eval` of `(P : O⟦X⟧)` with `Polynomial.eval x P`
(routine, not yet done), and (d) **root-counting**: showing `P` (which is Eisenstein — a
`Polynomial.IsDistinguishedAt` polynomial is automatically `IsWeaklyEisensteinAt`, and here the
degree-`0` coefficient has valuation exactly `1` since `f`'s linear coefficient is `π`) has exactly
`q` *distinct* roots in `K`. That last step is separability, not (yet) a Weierstrass-preparation
consequence — genuinely new content, not attempted here. See `ROADMAP.md` for the precise
remaining state.

## References

* Mathlib, `Mathlib.RingTheory.PowerSeries.WeierstrassPreparation` (Jz Pan, 2025).
* J. Lubin, J. Tate, *Formal complex multiplication in local fields*, Ann. of Math. 81 (1965).
* J-P. Serre, *Local Fields*, Ch. IV.
* Washington, *Introduction to Cyclotomic Fields*, Proposition 7.2 / Theorem 7.3.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

open PowerSeries IsLocalRing

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {π : O} {f : O⟦X⟧}

omit [Finite (ResidueField O)] in
/-- **`f`'s image in the residue field is nonzero.** Immediate from the defining congruence
`f.map (residue O) = X ^ q` (`IsLubinTatePoly`'s third condition): `X ^ q ≠ 0` since `ResidueField
O`, being a field, is nontrivial. -/
theorem map_residue_ne_zero (hf : IsLubinTatePoly π (residueCard O) f) :
    PowerSeries.map (residue O) f ≠ 0 := by
  rw [hf.2.2]
  exact pow_ne_zero _ PowerSeries.X_ne_zero

omit [Finite (ResidueField O)] in
/-- **The order of `f`'s residue-field image is exactly `q := residueCard O`.** Immediate from the
defining congruence together with `PowerSeries.order_X_pow`. This identifies the degree Mathlib's
Weierstrass preparation theorem produces with `q` directly, without needing to discover it from a
weaker (only-low-degree) congruence. -/
theorem order_map_residue_eq (hf : IsLubinTatePoly π (residueCard O) f) :
    (PowerSeries.map (residue O) f).order = (residueCard O : ℕ∞) := by
  rw [hf.2.2, PowerSeries.order_X_pow]

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

omit [Finite (ResidueField O)] in
/-- **Weierstrass preparation for a Lubin-Tate power series.** `f = P * u`, `P : O[X]` a
distinguished polynomial (monic, all lower coefficients in the maximal ideal) of degree exactly
`q := residueCard O`, `u : O⟦X⟧` a unit power series. Specializes Mathlib's
`PowerSeries.exists_isWeierstrassFactorization` via `map_residue_ne_zero`/`order_map_residue_eq`. -/
theorem exists_isWeierstrassFactorization_of_isLubinTatePoly
    (hf : IsLubinTatePoly π (residueCard O) f) :
    ∃ (P : O[X]) (u : O⟦X⟧), P.IsDistinguishedAt (IsLocalRing.maximalIdeal O) ∧ IsUnit u ∧
      f = (P : O⟦X⟧) * u ∧ P.natDegree = residueCard O := by
  obtain ⟨P, u, hPu⟩ := PowerSeries.exists_isWeierstrassFactorization (map_residue_ne_zero hf)
  refine ⟨P, u, hPu.isDistinguishedAt, hPu.isUnit, hPu.eq_mul, ?_⟩
  rw [hPu.natDegree_eq_toNat_order_map, order_map_residue_eq hf]
  rfl

end LubinTate

end
