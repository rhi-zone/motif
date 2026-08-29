/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.NonarchimedeanPowerSeriesEval

/-!
# `eval` is natural under base change along a compatible ring homomorphism

Evaluating `f.map ψ` (a power series base-changed along
`ψ : O →+* O'`) at a point of some target field `K`, using `[Algebra O' K]`, agrees with evaluating
`f` itself directly at that point using `[Algebra O K]` — **provided** the two algebra structures on
`K` agree along `ψ`, i.e. `algebraMap O' K ∘ ψ = algebraMap O K`.

This holds with **no convergence, coefficient-bound, or `‖x‖ < 1` hypothesis at all**:
`NonarchimedeanPowerSeriesEval.eval` is a `tsum` (`∑' n, evalSummand f x n`), and `PowerSeries.map`
satisfies `coeff n (f.map ψ) = ψ (coeff n f)` (`PowerSeries.coeff_map`) — so the two summand
sequences are *termwise* equal whenever the two algebra maps agree along `ψ`, independent of whether
either series is summable at `x` at all (an unconditionally divergent `tsum` is `0` in Mathlib either
way, so termwise-equal summand families always have equal `tsum`s, `tsum_congr`). -/

@[expose] public section

noncomputable section

namespace NonarchimedeanPowerSeriesEval

variable {R R' K : Type*} [CommRing R] [CommRing R'] [NormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [Algebra R K] [Algebra R' K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **`eval` is natural under base change**: `eval (f.map ψ) x = eval f x`, given the two algebra
structures on `K` (via `R` and via `R'`) agree along `ψ : R →+* R'`. Purely termwise
(`PowerSeries.coeff_map` plus `hcomp`), no summability hypothesis needed. -/
theorem eval_map (ψ : R →+* R') (hcomp : ∀ r : R, algebraMap R' K (ψ r) = algebraMap R K r)
    (f : PowerSeries R) (x : K) :
    eval (PowerSeries.map ψ f) x = eval f x := by
  unfold eval
  congr 1
  funext n
  unfold evalSummand
  rw [PowerSeries.coeff_map, hcomp]

end NonarchimedeanPowerSeriesEval

end
