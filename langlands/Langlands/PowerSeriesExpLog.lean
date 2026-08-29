import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The formal mutual-inverse identity for `PowerSeries.exp`/`PowerSeries.log`

`Langlands.NonarchimedeanExponential`'s module docstring flags, as unbuilt, the mutual-inverse
relationship between its from-scratch convergent `exp`/`log` and Mathlib's *formal* power
series `PowerSeries.exp`/`PowerSeries.log` (`Mathlib.RingTheory.PowerSeries.Exp`/`.Log`): no
`exp_log`/`log_exp`-style formal identity existed anywhere in the vendored Mathlib. But the
**machinery** to derive it was already present and unused:
`Mathlib.RingTheory.PowerSeries.Substitution`'s `PowerSeries.substInv` construction (a formal
substitution-inverse, `P.subst (substInv P) = X` and `(substInv P).subst P = X` for `P` with zero
constant term and invertible linear coefficient) and `Mathlib.RingTheory.PowerSeries.Derivative`'s
chain rule (`derivative_subst`) and derivative/constant-term uniqueness principle
(`PowerSeries.derivative.ext`) — indeed, `Derivative.lean`'s own module docstring names exactly this
identity as its motivating example: "one can easily prove the power series identity
`exp(log(1+X)) = 1+X` by differentiating twice."

This file proves both halves of that identity, `X`-substitution style
(`f.subst g` means "substitute `g` for `X` in `f`", i.e. `f ∘ g` as formal power series):

* `PowerSeries.log_subst_exp_sub_one : (log A).subst (exp A - 1) = X` — formally, `log(exp X) = X`.
* `PowerSeries.exp_sub_one_subst_log : (exp A - 1).subst (log A) = X` — formally,
  `exp(log(1 + X)) - 1 = X`, i.e. `exp(log(1+X)) = 1 + X`.

## Route

1. `log_subst_exp_sub_one` is proved directly by the "differentiate twice" method the `Derivative.lean`
   docstring names: the chain rule (`derivative_subst`) reduces the derivative of
   `(log A).subst (exp A - 1)` to `G.subst (exp A - 1) * exp A` where `G := d⁄dX A (log A)` is the
   geometric series; a direct coefficient computation gives the *formal* identity `(1 + X) * G = 1`
   (`one_add_X_mul_derivative_log_eq_one`, stated as its own general lemma since it is not specific to
   this file's target identities), and applying the substitution ring homomorphism to it turns this
   into `exp A * (G.subst (exp A - 1)) = 1`. So the derivative of
   `(log A).subst (exp A - 1)` is the constant series `1`, matching `d⁄dX A X = 1`; the constant term
   is `0` on both sides (`constantCoeff_logOf`, `constantCoeff_X`); `PowerSeries.derivative.ext`
   concludes the two power series are equal.
2. `exp_sub_one_subst_log` is obtained from `log_subst_exp_sub_one` via a general **uniqueness of
   substitution-inverse** lemma (`eq_substInv_of_subst_eq_X`, proved first, in maximal generality —
   any `CommRing R`, not tied to `exp`/`log`): if `Q.subst P = X` for `P` with zero constant term and
   invertible linear coefficient, then `Q = P.substInv`. Applying this with `P := exp A - 1`,
   `Q := log A` (using step 1's identity as the hypothesis) gives `log A = (exp A - 1).substInv`;
   substituting back into `subst_substInv_right` (`P.subst P.substInv = X`) gives
   `(exp A - 1).subst (log A) = X` directly, with no second derivative computation needed.

## What this does *not* close

This file proves the identity for Mathlib's *formal* `PowerSeries.exp`/`.log` only. Transporting it
to `Langlands.NonarchimedeanExponential`'s from-scratch *convergent* `exp`/`log` needs, additionally:
(a) matching `PowerSeries.exp`/`.log`'s coefficient-indexed definitions against
`NonarchimedeanExponential.exp`/`.log`'s Cauchy-limit definitions termwise, and (b) an analytic
argument that termwise convergence commutes with formal substitution (i.e. that the convergent `exp`
and `log`, viewed as limits of their partial sums, actually satisfy the substitution identity that
the formal power series satisfy coefficientwise). Neither (a) nor (b) is done here.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-! ## A general uniqueness-of-substitution-inverse lemma -/

/-- **Uniqueness of a formal substitution inverse.** If `P : R⟦X⟧` has zero constant term and
invertible linear coefficient, and `Q : R⟦X⟧` satisfies `Q.subst P = X` (i.e. `Q ∘ P = X` as formal
power series), then `Q` must be `P.substInv` — the substitution inverse `PowerSeries.substInv`
already constructs. Combined with `PowerSeries.subst_substInv_right`, this yields the *other*
substitution identity `P.subst Q = X` for free, without a second uniqueness argument specific to `P`.
-/
theorem eq_substInv_of_subst_eq_X {P Q : R⟦X⟧} (hP : P.constantCoeff = 0)
    [Invertible (coeff 1 P)] (hQP : Q.subst P = X) : Q = P.substInv := by
  have hPs : HasSubst P := HasSubst.of_constantCoeff_zero' hP
  have hSI : HasSubst P.substInv := HasSubst.substInv P
  -- Written with the prefix form `subst a f` (rather than `f.subst a`) throughout: nesting the
  -- dot notation here (`(Q.subst P).subst P.substInv`) causes it to elaborate against
  -- `MvPowerSeries.subst` instead of `PowerSeries.subst`, since both live in a namespace matching
  -- `R⟦X⟧`'s reducible head; the prefix form pins the intended `PowerSeries.subst` unambiguously.
  calc Q = subst X Q := (X_subst Q).symm
    _ = subst (subst P.substInv P) Q := by rw [subst_substInv_right P hP]
    _ = subst P.substInv (subst P Q) := (subst_comp_subst_apply hPs hSI Q).symm
    _ = subst P.substInv X := by rw [hQP]
    _ = P.substInv := subst_X hSI

/-! ## The formal geometric-series identity feeding the chain rule -/

/-- **The formal geometric series is the multiplicative inverse of `1 + X`.** A direct coefficient
computation: at `n = 0` both sides are `1`; at `n = m + 1`, the two summands
`(-1)^(m+1)` and `(-1)^m` (pulled back along `algebraMap ℚ A`) cancel. This is exactly
`d⁄dX A (log A)` (`PowerSeries.deriv_log`), stated on its own since the identity itself is a fact
about the geometric series, independent of `log`. -/
theorem one_add_X_mul_derivative_log_eq_one (A : Type*) [CommRing A] [Algebra ℚ A] :
    (1 + X) * (mk fun n ↦ algebraMap ℚ A ((-1 : ℚ) ^ n)) = (1 : A⟦X⟧) := by
  set G : A⟦X⟧ := mk fun n ↦ algebraMap ℚ A ((-1 : ℚ) ^ n) with hG
  rw [add_mul, one_mul]
  ext n
  cases n with
  | zero =>
    simp [hG, coeff_one]
  | succ m =>
    have hcancel : (-1 : ℚ) ^ (m + 1) + (-1 : ℚ) ^ m = 0 := by rw [pow_succ]; ring
    rw [map_add, coeff_succ_X_mul, hG, coeff_mk, coeff_mk]
    calc algebraMap ℚ A ((-1 : ℚ) ^ (m + 1)) + algebraMap ℚ A ((-1 : ℚ) ^ m)
        = algebraMap ℚ A ((-1 : ℚ) ^ (m + 1) + (-1 : ℚ) ^ m) := (map_add _ _ _).symm
      _ = 0 := by rw [hcancel, map_zero]
      _ = coeff (m + 1) (1 : A⟦X⟧) := by rw [coeff_one, if_neg m.succ_ne_zero]

/-! ## The target identities -/

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- `exp A - 1` has zero constant term and linear coefficient exactly `1`, hence carries the
`Invertible` instance `eq_substInv_of_subst_eq_X`/`subst_substInv_right` need. -/
private theorem constantCoeff_exp_sub_one : (exp A - 1 : A⟦X⟧).constantCoeff = 0 := by
  simp [constantCoeff_exp]

private theorem coeff_one_exp_sub_one : coeff 1 (exp A - 1 : A⟦X⟧) = 1 := by
  simp [coeff_exp, coeff_one]

/-- **Formally, `log(exp X) = X`.** Proved by the "differentiate twice" method: the chain rule
(`derivative_subst`) plus the geometric-series identity `one_add_X_mul_derivative_log_eq_one`
transported through the substitution homomorphism shows both
`(log A).subst (exp A - 1)` and `X` have derivative `1` and constant term `0`; `derivative.ext`
concludes they are equal. -/
theorem log_subst_exp_sub_one : (log A).subst (exp A - 1 : A⟦X⟧) = X := by
  haveI : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat (M := A)
  have hg : HasSubst (exp A - 1 : A⟦X⟧) := HasSubst.exp_sub_one
  set G : A⟦X⟧ := mk fun n ↦ algebraMap ℚ A ((-1 : ℚ) ^ n) with hGdef
  have hderivP : d⁄dX A (exp A - 1 : A⟦X⟧) = exp A := by
    rw [map_sub, derivative_exp, Derivation.map_one_eq_zero, sub_zero]
  have hderivLog : d⁄dX A (log A) = G := deriv_log
  have h3 : (1 : A⟦X⟧).subst (exp A - 1 : A⟦X⟧) = 1 := by
    rw [← coe_substAlgHom hg, map_one]
  have hkey : G.subst (exp A - 1 : A⟦X⟧) * exp A = 1 := by
    have h1 : (1 + X : A⟦X⟧).subst (exp A - 1 : A⟦X⟧) = exp A := by
      rw [subst_add hg, h3, subst_X hg]
      ring
    have h2 : ((1 + X) * G).subst (exp A - 1 : A⟦X⟧)
        = (1 + X : A⟦X⟧).subst (exp A - 1 : A⟦X⟧) * G.subst (exp A - 1 : A⟦X⟧) :=
      subst_mul hg _ _
    rw [one_add_X_mul_derivative_log_eq_one, h3, h1] at h2
    rw [mul_comm]
    exact h2.symm
  have hderiv : d⁄dX A ((log A).subst (exp A - 1 : A⟦X⟧)) = d⁄dX A (X : A⟦X⟧) := by
    rw [derivative_subst A hg, hderivLog, hderivP, hkey, derivative_X]
  have hconst : constantCoeff ((log A).subst (exp A - 1 : A⟦X⟧)) = constantCoeff (X : A⟦X⟧) := by
    rw [constantCoeff_X]
    exact constantCoeff_logOf (f := exp A) constantCoeff_exp
  exact derivative.ext hderiv hconst

/-- **Formally, `exp(log(1+X)) = 1+X`.** Obtained from `log_subst_exp_sub_one` via the general
uniqueness-of-substitution-inverse lemma `eq_substInv_of_subst_eq_X`: since `(log A).subst
(exp A - 1) = X`, uniqueness forces `log A = (exp A - 1).substInv`, and substituting this into
`subst_substInv_right` gives the identity directly, with no second derivative computation. -/
theorem exp_sub_one_subst_log : (exp A - 1 : A⟦X⟧).subst (log A) = X := by
  haveI : Invertible (coeff 1 (exp A - 1 : A⟦X⟧)) := by
    rw [coeff_one_exp_sub_one]; exact invertibleOne
  have heq : log A = (exp A - 1 : A⟦X⟧).substInv :=
    eq_substInv_of_subst_eq_X (constantCoeff_exp_sub_one A) (log_subst_exp_sub_one A)
  rw [heq]
  exact subst_substInv_right _ (constantCoeff_exp_sub_one A)

end PowerSeries

end
