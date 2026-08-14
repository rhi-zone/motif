/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepSplittingField

/-!
# `K_2 / K_1` is separable, given `K` has characteristic `0`

`ROADMAP.md`'s `§55` "Next step" anticipated closing residue-field preservation for `O_{K_2}` as a
mechanical repeat of the `K_1`-level argument, with "no new mathematical content ... beyond what
`§52`'s `K_2`-generic instance package and this pass's `K_2`-specific `algebraMap`/norm-transport
lemmas already supply". **That expectation does not hold for separability.**

The `K_1`-level separability proof (`LubinTate.separable_map_divX_of_isLubinTatePoly`,
`Langlands/LubinTateEisensteinQ.lean`) is a *tame-ramification* argument: it needs
`IsUnit (Q.natDegree : O)`, i.e. the degree of the defining polynomial coprime to the residue
characteristic. For `K_1 / K`, `Q := P.divX` has degree `q - 1` (`q := residueCard O`, a prime
power), and `q - 1` is automatically coprime to the residue characteristic (its residue image is
`-1 ≠ 0`). For `K_2 / K_1`, the defining polynomial `P₂` (`Langlands/LubinTateTowerStep.lean`'s
`isEisensteinAt_shifted`) has degree exactly `q` itself — **not** coprime to the residue
characteristic (`q ≡ 0` in the residue field). The tame-ramification technique is therefore
genuinely inapplicable to `K_2 / K_1`: `K_2 / K_1` is *wildly* ramified.

Classically, Lubin-Tate torsion extensions are separable at every level regardless of tameness,
via a formal-group argument (the derivative of `[π]_F` is a unit at every point, propagated along
the group law) — but that argument needs the Lubin-Tate formal group law itself, which is a
substantially larger undertaking than reusing existing machinery, and is not attempted here.

**What this file does instead**: in the arc's *concrete* application (`O := v.adicCompletionIntegers
F`, `K := v.adicCompletion F` for a number field `F`), `K` has characteristic `0` — and in
characteristic `0`, every algebraic extension is separable for free
(`Algebra.IsSeparable.of_integral`), no tameness needed at all. This file records that shortcut
explicitly, as a new, genuine, and *documented* additional hypothesis (`[CharZero K]`) — not a
smuggled-in replacement for the general fact, and not available for an equal-characteristic `O`
(e.g. `O = 𝔽_q[[T]]`), where the tame argument fails and the formal-group argument would be needed
instead.

## Main results

* `K_1.instCharZero` : `K_1 P` is `CharZero`, given `K` is. `algebraMap K (K_1 P)` is injective (a
  field homomorphism), so a vanishing `Nat.cast` in `K_1 P` pulls back to one in `K`.
* `K_2.instAlgebraIsSeparable` : `Algebra.IsSeparable (K_1 P) (K_2 P₂)`, given `[CharZero K]`.
  Immediate from `Algebra.IsSeparable.of_integral`, since `K_2 P₂ / K_1 P` is finite (hence
  integral, `Algebra.IsIntegral.of_finite`) and `K_1 P` is `CharZero` (`K_1.instCharZero`).
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]}

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [IsFractionRing O K] in
/-- **`K_1 P` is `CharZero`, given `K` is.** `algebraMap K (K_1 P)` is injective (a field
homomorphism into a nontrivial ring), so `(n : K_1 P) = 0` forces `(n : K) = 0`
(via `map_natCast`), hence `n = 0` by `CharZero K`. -/
instance K_1.instCharZero [CharZero K] : CharZero (K_1 (K := K) P) := by
  haveI hinj : Function.Injective (algebraMap K (K_1 (K := K) P)) :=
    (algebraMap K (K_1 (K := K) P)).injective
  refine ⟨fun m n h => ?_⟩
  have hcast : algebraMap K (K_1 (K := K) P) (m : K) = algebraMap K (K_1 (K := K) P) (n : K) := by
    rw [map_natCast, map_natCast, h]
  exact Nat.cast_injective (hinj hcast)

variable {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X]}

/-- **`K_2 P₂ / K_1 P` is separable, given `K` has characteristic `0`.** The extension is finite
(`K_2.instFiniteDimensional`), hence integral (`Algebra.IsIntegral.of_finite`); every integral
extension of a `CharZero` field is separable (`Algebra.IsSeparable.of_integral`). See this file's
module docstring for why the tame-ramification route (`separable_map_divX_of_isLubinTatePoly`'s
technique) does *not* apply to `K_2 / K_1` and why `[CharZero K]` is a genuine new hypothesis, not
free from the arc's existing standing assumptions. -/
instance K_2.instAlgebraIsSeparable [CharZero K] :
    Algebra.IsSeparable (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂) :=
  haveI : Algebra.IsIntegral (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂) :=
    Algebra.IsIntegral.of_finite _ _
  Algebra.IsSeparable.of_integral (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)

end LubinTate

end
