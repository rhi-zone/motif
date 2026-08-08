import Langlands.NonarchimedeanExponentialUnitsFiltration
import Langlands.NonarchimedeanExponentialAdd
import Langlands.NonarchimedeanExpLogDegreeMatch
import Langlands.NonarchimedeanExponentialHasSum

/-!
# The exp/log group isomorphism `U_A^{(i)} ≅ (𝔪_A^i, +)`

`Langlands.NonarchimedeanExponentialUnitsFiltration.exp_mem_principalUnitsPow` shows `exp` maps
`𝔪_A^i` into the principal-units subgroup `U_A^{(i)} := ValuationSubring.principalUnitsPow A i`
pointwise (an existential landing statement); `Langlands.NonarchimedeanExponentialAdd.exp_add` gives
the group-homomorphism law. This file assembles those into an actual group isomorphism
`Multiplicative ↥(𝔪_A^i) ≃* ↥(U_A^{(i)})`, for `i` above a strict threshold — closing item (b) of
`ROADMAP.md`'s fifteenth pass "what remains" list (packaging item 3 + `exp_add` into the isomorphism
the wild-case norm-group-index argument actually wants).

## Route

* **The homomorphism (`expHom`).** `exp_mem_principalUnitsPow` is refactored into an explicit
  `noncomputable def expUnit` (via `Classical.choose`) plus `expUnit_mem`/`expUnit_coe` extracting its
  two conjuncts, giving a genuine function to bundle. Equality of two units in `Aˣ` reduces to
  equality of their `A`-values (`Units.ext`), which reduces to equality of their `K`-images
  (`Subtype.ext`, since `A` is literally a subtype of `K`); `map_one'`/`map_mul'` both reduce to
  checking the `K`-image equation, closed directly by `exp_zero`/`exp_add`. No `log` is needed for
  this direction.
* **Surjectivity.** Given `u ∈ U_A^{(i)}`, `y := (u : A) - 1 ∈ 𝔪_A^i`; the preimage is
  `x := log hnorm (y : K)`, using `exp_log_eq_one_add` to identify `exp hnorm x = 1 + (y : K) = (u :
  A : K)`. The catch is showing `x ∈ 𝔪_A^i` itself (not just that `exp` converges there) — this needs
  a genuine "`log` lands in `𝔪_A^i` with no level shift" fact, which `norm_log_le`'s crude bound
  `‖log z‖ ≤ ‖z‖ / ‖p‖` is too weak to give (dividing by `‖p‖ < 1` can *increase* the norm past the
  next filtration level). `norm_log_eq_of_lt_sq` (below) closes this by bounding the *tail*
  `‖log hnorm z - z‖` strictly below `‖z‖` and concluding `‖log hnorm z‖ = ‖z‖` exactly via the
  ultrametric "isosceles triangle" principle (`norm_eq_of_norm_sub_lt`, proved here from scratch — not
  found anywhere in this repo or (searched) in Mathlib under any name).
* **Injectivity.** Does not need `log`. `exp x₁ = exp x₂` reduces (via `exp_add`/`isUnit_exp`, `K`
  commutative) to `exp z = 1 ⟹ z = 0`, which follows from the same "isosceles triangle" principle
  applied to `exp hnorm z - 1 - z` (bounded strictly below `‖z‖` for `z ≠ 0` below threshold via
  `norm_pow_div_factorial_le`, `exp_mul_exp_neg`. Wait — see `norm_exp_sub_one_sub_lt` below for the
  actual tail bound used) against `exp hnorm z = 1`.

## The threshold: `logUnitsThreshold`, and why one threshold serves both directions

The per-term geometric bound behind `norm_log_eq_of_lt_sq` uses the *plain* ratio `‖z‖ / ‖p‖` (no
`rpow` exponent adjustment — `log`'s convergence estimate never needed one, see
`NonarchimedeanExponential.norm_pow_div_natCast_le`), giving a strict tail bound exactly when `‖z‖ <
‖p‖ ^ 2`. This is defined as `logUnitsThreshold K p := ‖(p : K)‖ ^ 2` — a plain natural-number square,
simpler than `expUnitsThreshold`'s `rpow`.

**`logUnitsThreshold K p ≤ expUnitsThreshold K p` always** (`logUnitsThreshold_le_expUnitsThreshold`):
since `expUnitsThreshold K p = ‖p‖ ^ (2/(p-1))` and `2/(p-1) ≤ 2` for `p ≥ 2` (equality only at
`p = 2`), and `‖p‖ < 1` makes smaller exponents give *larger* values, `expUnitsThreshold K p ≥ ‖p‖ ^
2 = logUnitsThreshold K p`. So a single strict hypothesis `‖π‖ ^ i < logUnitsThreshold K p` gives both
`‖π‖ ^ i < expUnitsThreshold K p` (needed for injectivity and for reusing `exp_mem_principalUnitsPow`
via `.le`) and the log-specific bound `‖π‖ ^ i < ‖p‖ ^ 2` (needed for surjectivity) simultaneously,
with no need to track two separate thresholds through the final theorem.

## Main results

* `expUnit`, `expUnit_mem`, `expUnit_coe` : the existential `exp_mem_principalUnitsPow` refactored
  into an explicit function plus its two defining properties.
* `expHom` : the bundled `MonoidHom`, `Multiplicative ↥(𝔪_A^i) →* ↥(U_A^{(i)})`.
* `norm_eq_of_norm_sub_lt` : the ultrametric isosceles-triangle principle,
  `‖a - b‖ < ‖b‖ → ‖a‖ = ‖b‖`.
* `logUnitsThreshold`, `logUnitsThreshold_le_expUnitsThreshold`.
* `norm_log_eq_of_lt_sq` : `‖z‖ < logUnitsThreshold K p → ‖log hnorm z‖ = ‖z‖` (for `z ≠ 0`; trivially
  true at `z = 0` too since both sides vanish).
* `log_mem_maximalIdeal_pow` : the no-shift landing lemma, `x ∈ 𝔪_A^i → log hnorm (x : K) ∈ 𝔪_A^i`
  (as an actual `A`-element), for `i` above `logUnitsThreshold`.
* `expEquiv` : **the headline isomorphism**,
  `Multiplicative ↥(IsLocalRing.maximalIdeal A ^ i) ≃* ↥(ValuationSubring.principalUnitsPow A i)`.

## What remains

Toward the wild-case norm-group index theorem (`ROADMAP.md`'s fifteenth pass "what remains" list):
item (a), a genuine concrete mixed-characteristic instance, and item (c), running the index
computation through this isomorphism using `norm_exp_eq_exp_trace`
(`Langlands.AdicCompletionNormExpTrace`) — mirroring `Langlands.TotallyRamifiedNormIndex`'s pattern
for the tame case. Neither is attempted in this file.
-/

noncomputable section

open IsLocalRing

namespace NonarchimedeanExponential

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
variable {p : ℕ} [hp : Fact p.Prime]

/-! ## An ultrametric isosceles-triangle principle -/

omit [CharZero K] [CompleteSpace K] in
/-- **The ultrametric "isosceles triangle" principle.** If `‖a - b‖ < ‖b‖` then `‖a‖ = ‖b‖`.
Standard consequence of the ultrametric inequality (checked absent from this repo and from Mathlib
under any searched name), proved directly: `‖a‖ = ‖b + (a - b)‖ ≤ max ‖b‖ ‖a - b‖ = ‖b‖`, and
conversely `‖b‖ = ‖a - (a - b)‖ ≤ max ‖a‖ ‖a - b‖`, which (since `‖a - b‖ < ‖b‖`) forces the max to be
`‖a‖`, giving `‖b‖ ≤ ‖a‖`. -/
theorem norm_eq_of_norm_sub_lt {a b : K} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have heq1 : a = b + (a - b) := by ring
  have h1 : ‖a‖ ≤ ‖b‖ := by
    calc ‖a‖ = ‖b + (a - b)‖ := by rw [← heq1]
      _ ≤ max ‖b‖ ‖a - b‖ := IsUltrametricDist.norm_add_le_max b (a - b)
      _ = ‖b‖ := max_eq_left h.le
  have h2 : ‖b‖ ≤ ‖a‖ := by
    by_contra hc
    push Not at hc
    have heq2 : b = a + (-(a - b)) := by ring
    have h3 : ‖b‖ ≤ max ‖a‖ ‖a - b‖ := by
      calc ‖b‖ = ‖a + (-(a - b))‖ := by rw [← heq2]
        _ ≤ max ‖a‖ ‖-(a - b)‖ := IsUltrametricDist.norm_add_le_max a (-(a - b))
        _ = max ‖a‖ ‖a - b‖ := by rw [norm_neg]
    have h4 : max ‖a‖ ‖a - b‖ < ‖b‖ := max_lt hc h
    exact absurd h3 (not_le.mpr h4)
  exact le_antisymm h1 h2

/-! ## Step 1: `expUnit`, and the bundled homomorphism -/

variable (A : ValuationSubring K) (hA : ∀ x : K, x ∈ A ↔ ‖x‖ ≤ 1)

include hA in
/-- **`exp_mem_principalUnitsPow`'s witness, made explicit.** The unit `u : Aˣ` produced
existentially by `exp_mem_principalUnitsPow`, extracted via `Classical.choose`. -/
noncomputable def expUnit (hnorm : ‖(p : K)‖ < 1) {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : (π : K) ≠ 0)
    (hπnorm : ‖(π : K)‖ < 1) {i : ℕ} (hthresh : ‖(π : K)‖ ^ i ≤ expUnitsThreshold K p)
    {x : A} (hx : x ∈ maximalIdeal A ^ i) : Aˣ :=
  (exp_mem_principalUnitsPow A hA hnorm hπ hπ0 hπnorm hthresh hx).choose

include hA in
theorem expUnit_mem (hnorm : ‖(p : K)‖ < 1) {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : (π : K) ≠ 0)
    (hπnorm : ‖(π : K)‖ < 1) {i : ℕ} (hthresh : ‖(π : K)‖ ^ i ≤ expUnitsThreshold K p)
    {x : A} (hx : x ∈ maximalIdeal A ^ i) :
    expUnit A hA hnorm hπ hπ0 hπnorm hthresh hx ∈ ValuationSubring.principalUnitsPow A i :=
  (exp_mem_principalUnitsPow A hA hnorm hπ hπ0 hπnorm hthresh hx).choose_spec.1

include hA in
theorem expUnit_coe (hnorm : ‖(p : K)‖ < 1) {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : (π : K) ≠ 0)
    (hπnorm : ‖(π : K)‖ < 1) {i : ℕ} (hthresh : ‖(π : K)‖ ^ i ≤ expUnitsThreshold K p)
    {x : A} (hx : x ∈ maximalIdeal A ^ i) :
    ((expUnit A hA hnorm hπ hπ0 hπnorm hthresh hx : A) : K) = exp hnorm (x : K) :=
  (exp_mem_principalUnitsPow A hA hnorm hπ hπ0 hπnorm hthresh hx).choose_spec.2

variable {A} {hA}

include hA in
/-- **The bundled group homomorphism induced by `exp`**, `𝔪_A^i → U_A^{(i)}`. Both `map_one'` and
`map_mul'` reduce (via `Subtype.ext`/`Units.ext`, since equality of units in `Aˣ` is equality of
their `A`-values and `A` is itself a subtype of `K`) to a `K`-level identity closed directly by
`exp_zero`/`exp_add`. -/
noncomputable def expHom (hnorm : ‖(p : K)‖ < 1) {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : (π : K) ≠ 0)
    (hπnorm : ‖(π : K)‖ < 1) {i : ℕ} (hthresh : ‖(π : K)‖ ^ i ≤ expUnitsThreshold K p) :
    Multiplicative ↥(maximalIdeal A ^ i) →* ↥(ValuationSubring.principalUnitsPow A i) where
  toFun x := ⟨expUnit A hA hnorm hπ hπ0 hπnorm hthresh (Multiplicative.toAdd x).2,
    expUnit_mem A hA hnorm hπ hπ0 hπnorm hthresh (Multiplicative.toAdd x).2⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    show ((expUnit A hA hnorm hπ hπ0 hπnorm hthresh
        (Multiplicative.toAdd (1 : Multiplicative ↥(maximalIdeal A ^ i))).2 : A) : K) = _
    rw [expUnit_coe]
    have h0 : ((Multiplicative.toAdd (1 : Multiplicative ↥(maximalIdeal A ^ i)) : ↥(maximalIdeal A ^ i))
        : A) = 0 := rfl
    rw [h0]
    show exp hnorm (0 : K) = _
    rw [exp_zero]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    have hxmem : (Multiplicative.toAdd x : ↥(maximalIdeal A ^ i)).1 ∈ maximalIdeal A ^ i :=
      (Multiplicative.toAdd x).2
    have hymem : (Multiplicative.toAdd y : ↥(maximalIdeal A ^ i)).1 ∈ maximalIdeal A ^ i :=
      (Multiplicative.toAdd y).2
    have hxnorm : ‖((Multiplicative.toAdd x : ↥(maximalIdeal A ^ i)).1 : K)‖
        < convergenceRadius K p :=
      lt_of_le_of_lt (norm_le_pow_of_mem_maximalIdeal_pow A hA hπ hxmem)
        (lt_of_le_of_lt hthresh (expUnitsThreshold_lt_convergenceRadius hnorm))
    have hynorm : ‖((Multiplicative.toAdd y : ↥(maximalIdeal A ^ i)).1 : K)‖
        < convergenceRadius K p :=
      lt_of_le_of_lt (norm_le_pow_of_mem_maximalIdeal_pow A hA hπ hymem)
        (lt_of_le_of_lt hthresh (expUnitsThreshold_lt_convergenceRadius hnorm))
    show ((expUnit A hA hnorm hπ hπ0 hπnorm hthresh (Multiplicative.toAdd (x * y)).2 : A) : K)
        = ((expUnit A hA hnorm hπ hπ0 hπnorm hthresh (Multiplicative.toAdd x).2 : A) : K)
          * ((expUnit A hA hnorm hπ hπ0 hπnorm hthresh (Multiplicative.toAdd y).2 : A) : K)
    rw [expUnit_coe, expUnit_coe, expUnit_coe]
    have hsum : ((Multiplicative.toAdd (x * y) : ↥(maximalIdeal A ^ i)).1 : K)
        = ((Multiplicative.toAdd x : ↥(maximalIdeal A ^ i)).1 : K)
          + ((Multiplicative.toAdd y : ↥(maximalIdeal A ^ i)).1 : K) := by
      have h := toAdd_mul x y
      have : (Multiplicative.toAdd (x * y) : ↥(maximalIdeal A ^ i)).1
          = (Multiplicative.toAdd x : ↥(maximalIdeal A ^ i)).1
            + (Multiplicative.toAdd y : ↥(maximalIdeal A ^ i)).1 := by
        exact_mod_cast congrArg Subtype.val h
      exact_mod_cast this
    rw [hsum, exp_add hnorm hxnorm hynorm]

end NonarchimedeanExponential
