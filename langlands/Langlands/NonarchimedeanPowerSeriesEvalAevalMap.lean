/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.NonarchimedeanPowerSeriesEval
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# `aeval` through an intermediate base agrees with `eval` against the original base

For a polynomial `P : R[X]` base-changed to an intermediate ring
`K'` (`[Algebra R K']`) and then evaluated (`Polynomial.aeval`) at a point of a target field `L`
reached via `K'` (`[Algebra K' L]`), the result agrees with evaluating `P` (as a power series,
`NonarchimedeanPowerSeriesEval.eval`) directly against `R`'s own algebra structure on `L`
(`[Algebra R L]`) — **provided** the two routes `R → K' → L` and `R → L` agree
(`[IsScalarTower R K' L]`).

This is the "second base change" `NonarchimedeanPowerSeriesEval.eval_coe_eq_aeval` (a *single* fixed
base) doesn't cover on its own: here `P` is mapped to `K'` *before* `aeval` is applied, so the
statement first has to identify that two-hop `aeval` with a one-hop `aeval` against the composite
map `R → L` (`Polynomial.map_map` plus `IsScalarTower.algebraMap_eq`), and only then invoke
`eval_coe_eq_aeval` to convert that one-hop `aeval` into the power-series `eval`. No convergence,
coefficient-bound, or `‖x‖ < 1` hypothesis is needed, exactly as for `eval_coe_eq_aeval` itself: both
`aeval` and the polynomial-coercion `eval` are finite sums.

## Main result

* `aeval_map_eq_eval_coe` : `aeval x (P.map (algebraMap R K')) = eval (↑P : R⟦X⟧) x`,
  given `[IsScalarTower R K' L]`.
-/

@[expose] public section

noncomputable section

namespace NonarchimedeanPowerSeriesEval

variable {R K' L : Type*} [CommRing R] [CommRing K'] [Algebra R K']
  [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [Algebra R L] [Algebra K' L]
  [IsScalarTower R K' L]

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- **`aeval` through an intermediate base `K'` agrees with `eval` against the original base `R`**,
given the two routes `R → K' → L` and `R → L` agree (`IsScalarTower R K' L`). Proved by identifying
the two-hop `aeval x (P.map (algebraMap R K'))` with the one-hop `aeval x P` via
`Polynomial.map_map`/`IsScalarTower.algebraMap_eq`, then converting that one-hop `aeval` to the
power-series `eval` via `eval_coe_eq_aeval`. -/
theorem aeval_map_eq_eval_coe (P : Polynomial R) (x : L) :
    Polynomial.aeval x (P.map (algebraMap R K')) = eval (P : PowerSeries R) x := by
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq R K' L, Polynomial.eval_map, ← Polynomial.aeval_def]
  exact (eval_coe_eq_aeval P x).symm

end NonarchimedeanPowerSeriesEval

end
