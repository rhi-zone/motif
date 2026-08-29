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
`Multiplicative ↥(𝔪_A^i) ≃* ↥(U_A^{(i)})`, for `i` above a strict threshold — packaging the landing
statement together with `exp_add` into the isomorphism the wild-case norm-group-index argument
actually needs.

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
  applied to `exp hnorm z - 1 - z` (bounded strictly below `‖z‖` for `z ≠ 0` below threshold, via
  `norm_exp_sub_one_sub_lt` below) against `exp hnorm z = 1`.

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
* `logUnitsThreshold`, `logUnitsThreshold_le_expUnitsThreshold`,
  `logUnitsThreshold_lt_convergenceRadius`.
* `norm_log_eq_of_lt_sq` : `‖z‖ < logUnitsThreshold K p → ‖log hnorm z‖ = ‖z‖` (for `z ≠ 0`; trivially
  true at `z = 0` too since both sides vanish).
* `log_mem_maximalIdeal_pow` : the no-shift landing lemma, `x ∈ 𝔪_A^i → log hnorm (x : K) ∈ 𝔪_A^i`
  (as an actual `A`-element), for `i` above `logUnitsThreshold`.
* `expEquiv` : **the headline isomorphism**,
  `Multiplicative ↥(IsLocalRing.maximalIdeal A ^ i) ≃* ↥(ValuationSubring.principalUnitsPow A i)`.

## What remains

Toward the wild-case norm-group index theorem: a genuine concrete mixed-characteristic instance, and
running the index computation through this isomorphism using `norm_exp_eq_exp_trace`
(`Langlands.AdicCompletionNormExpTrace`) — mirroring `Langlands.TotallyRamifiedNormIndex`'s pattern
for the tame case. Neither is done in this file.
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

/-! ## Step 2: injectivity — `exp hnorm z = 1 ∧ z ≠ 0` is impossible below a strict threshold -/

omit hA [IsUltrametricDist K] [CompleteSpace K] in
/-- `convergenceRadius K p < 1`: a strictly-positive-exponent power of a norm `< 1` stays `< 1`. -/
theorem convergenceRadius_lt_one (hnorm : ‖(p : K)‖ < 1) : convergenceRadius K p < 1 := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  have hexp0 : (0 : ℝ) < ((p : ℝ) - 1)⁻¹ := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    have : (0:ℝ) < (p:ℝ) - 1 := by linarith
    positivity
  exact Real.rpow_lt_one hp0.le hnorm hexp0

omit hA [IsUltrametricDist K] [CompleteSpace K] in
/-- `convergenceRadius K p ^ 2 = expUnitsThreshold K p`: the units threshold is exactly the square
of `exp`'s own convergence radius, matching `rpow` exponents `2 * (1/(p-1)) = 2/(p-1)`. -/
theorem convergenceRadius_sq_eq_expUnitsThreshold (_hnorm : ‖(p : K)‖ < 1) :
    convergenceRadius K p ^ (2 : ℕ) = expUnitsThreshold K p := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  unfold expUnitsThreshold convergenceRadius
  rw [← Real.rpow_natCast (‖(p : K)‖ ^ (((p : ℝ) - 1)⁻¹)) 2, ← Real.rpow_mul hp0.le]
  congr 1
  ring

omit hA in
/-- **The self-relative tail bound behind injectivity.** For `z ≠ 0` with `‖z‖ <
expUnitsThreshold K p`, `‖exp hnorm z - 1 - z‖ < ‖z‖` — the degree-`≥ 2` tail of the exponential
series is strictly smaller than `‖z‖` itself (not merely `→ 0`), because `expUnitsThreshold` is
*exactly* `d ^ 2` for `d := convergenceRadius K p` (`convergenceRadius_sq_eq_expUnitsThreshold`):
setting `ρ := ‖z‖ / d`, `norm_pow_div_factorial_le` gives `‖z^k/k!‖ ≤ ρ^k ≤ ρ^2` for `k ≥ 2`
(`ρ < d < 1`), and `ρ^2 = ‖z‖^2/d^2 < ‖z‖` is exactly the threshold hypothesis (`‖z‖ < d^2`),
using `‖z‖ > 0`. -/
theorem norm_exp_sub_one_sub_lt (hnorm : ‖(p : K)‖ < 1) {z : K} (hz : z ≠ 0)
    (hzlt : ‖z‖ < expUnitsThreshold K p) :
    ‖exp hnorm z - 1 - z‖ < ‖z‖ := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set d : ℝ := convergenceRadius K p with hd
  have hd0 : 0 < d := Real.rpow_pos_of_pos hp0 _
  have hd1 : d < 1 := convergenceRadius_lt_one hnorm
  have hdsq : d ^ (2 : ℕ) = expUnitsThreshold K p := convergenceRadius_sq_eq_expUnitsThreshold hnorm
  have hzltd2 : ‖z‖ < d ^ 2 := by rw [hdsq]; exact hzlt
  set ρ : ℝ := ‖z‖ / d with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hzpos.le hd0.le
  have hρltd : ρ < d := by rw [hρ, div_lt_iff₀ hd0]; rw [sq] at hzltd2; linarith
  have hρlt1 : ρ < 1 := hρltd.trans hd1
  have hρsq_lt : ρ ^ 2 < ‖z‖ := by
    have heq : ρ ^ 2 = ‖z‖ ^ 2 / d ^ 2 := by rw [hρ, div_pow]
    rw [heq, div_lt_iff₀ (by positivity)]
    have : ‖z‖ ^ 2 = ‖z‖ * ‖z‖ := sq ‖z‖
    rw [this]
    exact mul_lt_mul_of_pos_left hzltd2 hzpos
  have hd2ltd : d ^ 2 < d := by
    calc d ^ 2 = d * d := sq d
      _ < d * 1 := mul_lt_mul_of_pos_left hd1 hd0
      _ = d := mul_one d
  have hx : ‖z‖ < d := hzltd2.trans hd2ltd
  have hsum := hasSum_exp hnorm hx
  have hshift : HasSum (fun k => z ^ (k + 2) / ((k + 2).factorial : K))
      (exp hnorm z - ∑ j ∈ Finset.range 2, z ^ j / (j.factorial : K)) :=
    (hasSum_nat_add_iff' 2).mpr hsum
  have hsum2 : ∑ j ∈ Finset.range 2, z ^ j / (j.factorial : K) = 1 + z := by
    simp [Finset.sum_range_succ]
  rw [hsum2] at hshift
  have heq : exp hnorm z - (1 + z) = ∑' k, z ^ (k + 2) / ((k + 2).factorial : K) := hshift.tsum_eq.symm
  have hgoal_eq : exp hnorm z - 1 - z = exp hnorm z - (1 + z) := by ring
  rw [hgoal_eq, heq]
  refine (IsUltrametricDist.norm_tsum_le _).trans_lt (lt_of_le_of_lt (ciSup_le fun k => ?_) hρsq_lt)
  have hbound : ‖z ^ (k + 2) / ((k + 2).factorial : K)‖ ≤ ρ ^ (k + 2) := by
    rw [hρ]
    exact norm_pow_div_factorial_le hnorm z (k + 2)
  refine hbound.trans ?_
  exact pow_le_pow_of_le_one hρ0 hρlt1.le (by omega)

include hA in
/-- **`expHom` is injective**, for `i` above a *strict* variant of the threshold
(`‖π‖^i < expUnitsThreshold K p`, sharpening `exp_mem_principalUnitsPow`'s `≤`). Reduces (via the
same `Equiv.injective`/`Subtype.ext` chain as `expHom`'s own definitional equalities) to: `exp hnorm
z = 1` and `z ≠ 0` are incompatible for `‖z‖ < expUnitsThreshold K p`. `norm_exp_sub_one_sub_lt`
gives `‖(exp hnorm z - 1) - z‖ < ‖z‖`; since `exp hnorm z - 1 = 0` this identifies `‖z‖ = ‖-z‖ = ‖z‖`
... rather, `norm_eq_of_norm_sub_lt` applied to `a := exp hnorm z - 1 = 0`, `b := z` gives `0 = ‖z‖`,
forcing `z = 0`, contradiction. -/
theorem expHom_injective (hnorm : ‖(p : K)‖ < 1) {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : (π : K) ≠ 0)
    (hπnorm : ‖(π : K)‖ < 1) {i : ℕ} (hthresh : ‖(π : K)‖ ^ i ≤ expUnitsThreshold K p)
    (hthreshStrict : ‖(π : K)‖ ^ i < expUnitsThreshold K p) :
    Function.Injective (expHom (A := A) (hA := hA) hnorm hπ hπ0 hπnorm hthresh) := by
  rw [injective_iff_map_eq_one]
  intro z hz1
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply Subtype.ext
  show ((Multiplicative.toAdd z : ↥(maximalIdeal A ^ i)).1 : K) = ((0 : A) : K)
  have hz0 : ((0 : A) : K) = (0 : K) := rfl
  rw [hz0]
  have hz1A : ((expHom (A := A) (hA := hA) hnorm hπ hπ0 hπnorm hthresh z : Aˣ) : A) = 1 := by
    have := congrArg (fun w : ↥(ValuationSubring.principalUnitsPow A i) => (w : Aˣ)) hz1
    simpa using congrArg (fun u : Aˣ => (u : A)) this
  have hz1K : ((expUnit A hA hnorm hπ hπ0 hπnorm hthresh (Multiplicative.toAdd z).2 : A) : K)
      = ((1 : A) : K) :=
    congrArg (fun a : A => (a : K)) hz1A
  rw [expUnit_coe] at hz1K
  have hz1K' : exp hnorm ((Multiplicative.toAdd z : ↥(maximalIdeal A ^ i)).1 : K) = 1 := by
    simpa using hz1K
  set w : K := ((Multiplicative.toAdd z : ↥(maximalIdeal A ^ i)).1 : K) with hw
  by_contra hwne
  have hwmem : (Multiplicative.toAdd z : ↥(maximalIdeal A ^ i)).1 ∈ maximalIdeal A ^ i :=
    (Multiplicative.toAdd z).2
  have hwnorm : ‖w‖ ≤ ‖(π : K)‖ ^ i := norm_le_pow_of_mem_maximalIdeal_pow A hA hπ hwmem
  have hwlt : ‖w‖ < expUnitsThreshold K p := lt_of_le_of_lt hwnorm hthreshStrict
  have htail := norm_exp_sub_one_sub_lt hnorm hwne hwlt
  rw [hz1K'] at htail
  simp only [sub_self, zero_sub, norm_neg] at htail
  exact absurd htail (lt_irrefl _)

/-! ## Step 3: surjectivity — the no-shift `log` landing lemma -/

omit hA in
/-- `log hnorm 0 = 0`: every term of the defining series vanishes at `z = 0`. -/
theorem log_zero (hnorm : ‖(p : K)‖ < 1) : log hnorm (0 : K) = 0 := by
  have h0 : ‖(0 : K)‖ < logConvergenceRadius K p := by
    rw [norm_zero]; exact norm_natCast_pos
  have hs := hasSum_log hnorm h0
  have hzero : HasSum (fun k => (-1 : K) ^ k * (0 : K) ^ (k + 1) / ((k + 1 : ℕ) : K)) 0 := by
    have heq : (fun k => (-1 : K) ^ k * (0 : K) ^ (k + 1) / ((k + 1 : ℕ) : K)) = fun _ : ℕ => 0 := by
      funext k; simp
    rw [heq]; exact hasSum_zero
  exact (hzero.unique hs).symm

omit hA in
/-- **The `log`-side threshold**, `‖p‖ ^ 2` — a plain natural-number square, simpler than
`expUnitsThreshold`'s `rpow`, since `log`'s own per-term geometric bound
(`norm_pow_div_natCast_le`) already uses the plain ratio `‖z‖ / ‖p‖` with no exponent adjustment. -/
def logUnitsThreshold (K : Type*) [NormedField K] (p : ℕ) : ℝ := ‖(p : K)‖ ^ 2

omit hA [IsUltrametricDist K] [CompleteSpace K] in
/-- **`logUnitsThreshold K p ≤ expUnitsThreshold K p` always.** `expUnitsThreshold K p = ‖p‖ ^
(2/(p-1))` and `2/(p-1) ≤ 2` for `p ≥ 2` (equality only at `p = 2`); since `‖p‖ < 1`, a *smaller*
`rpow` exponent gives a *larger* value, so `expUnitsThreshold K p ≥ ‖p‖ ^ 2 = logUnitsThreshold K
p`. Consequently a single strict hypothesis `‖π‖ ^ i < logUnitsThreshold K p` suffices for both
`expHom_injective` (which only needs the weaker `< expUnitsThreshold K p`) and `log`'s own landing
lemma below. -/
theorem logUnitsThreshold_le_expUnitsThreshold (hnorm : ‖(p : K)‖ < 1) :
    logUnitsThreshold K p ≤ expUnitsThreshold K p := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    linarith
  have hexple : (2 : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ hp1]
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    nlinarith
  unfold logUnitsThreshold expUnitsThreshold
  rw [← Real.rpow_natCast ‖(p : K)‖ 2]
  exact Real.rpow_le_rpow_of_exponent_ge hp0 hnorm.le hexple

omit hA [IsUltrametricDist K] [CompleteSpace K] in
/-- **`logUnitsThreshold K p < convergenceRadius K p`.** Composing
`logUnitsThreshold_le_expUnitsThreshold` with `expUnitsThreshold_lt_convergenceRadius`: the
`log`-side threshold is bounded above by the `exp`-side units threshold, which is itself strictly
below `exp`'s own convergence radius. This lets any `‖x‖ < logUnitsThreshold K p` hypothesis be
reused directly where a `convergenceRadius`-shaped hypothesis is needed. -/
theorem logUnitsThreshold_lt_convergenceRadius (hnorm : ‖(p : K)‖ < 1) :
    logUnitsThreshold K p < convergenceRadius K p :=
  lt_of_le_of_lt (logUnitsThreshold_le_expUnitsThreshold hnorm)
    (expUnitsThreshold_lt_convergenceRadius hnorm)

omit hA [IsUltrametricDist K] [CompleteSpace K] in
/-- **A threshold `i₀` above which `‖π‖ ^ i` is strictly below `logUnitsThreshold K p`**, for any
`π : K` with `‖π‖ < 1`: since `‖π‖ ^ i → 0`, some `i₀` has `‖π‖ ^ i₀ < logUnitsThreshold K p`
(`exists_pow_lt_of_lt_one`), and by antitonicity of `i ↦ ‖π‖ ^ i` (`‖π‖ ≤ 1`), the same bound holds
for every `i ≥ i₀`. Mirrors `NonarchimedeanExponentialFiltration.exists_maximalIdeal_pow_le_convergenceRadius`,
but for `logUnitsThreshold` and for a bare `π : K` (no ambient `ValuationSubring A` needed) — this
is exactly the piece `expEquiv`'s `{i : ℕ}`/`hthreshStrict` hypotheses need, supplied generically
here so instantiating it against a concrete `NumberField`-visible `K` never has to write a fresh
`‖·‖` fact with an explicit type ascription (the diamond-avoidance discipline used throughout this
file). -/
theorem exists_pow_lt_logUnitsThreshold {π : K} (hπnorm : ‖π‖ < 1) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ‖π‖ ^ i < logUnitsThreshold K p := by
  have h0 : (0 : ℝ) < logUnitsThreshold K p := by
    unfold logUnitsThreshold
    exact pow_pos norm_natCast_pos 2
  obtain ⟨i₀, hi₀⟩ := exists_pow_lt_of_lt_one h0 hπnorm
  exact ⟨i₀, fun i hi => lt_of_le_of_lt (pow_le_pow_of_le_one (norm_nonneg _) hπnorm.le hi) hi₀⟩

omit hA [IsUltrametricDist K] [CharZero K] [CompleteSpace K] hp in
/-- **The concrete-witness core of `exists_pow_lt_logUnitsThreshold`.** Given a single strict bound
`‖π‖ ^ i₀ < logUnitsThreshold K p`, antitonicity of `i ↦ ‖π‖ ^ i` (`‖π‖ ≤ 1`) upgrades it to the
same bound for every `i ≥ i₀` — the piece that lets a concrete instance shift an already-closed
numeral threshold up to whatever larger numeral a downstream combination (`max`, `+`) needs, with no
fresh `‖·‖` type ascription. -/
theorem lt_logUnitsThreshold_of_le {π : K} (hπnorm : ‖π‖ ≤ 1) {i i₀ : ℕ} (hi : i₀ ≤ i)
    (hthresh : ‖π‖ ^ i₀ < logUnitsThreshold K p) : ‖π‖ ^ i < logUnitsThreshold K p :=
  lt_of_le_of_lt (pow_le_pow_of_le_one (norm_nonneg _) hπnorm hi) hthresh

omit hA in
/-- **`log` matches `‖·‖` exactly, below the strict threshold** (the no-shift landing bound):
for `z` with `‖z‖ < logUnitsThreshold K p`, `‖log hnorm z‖ = ‖z‖`. Trivial at `z = 0` (`log_zero`);
for `z ≠ 0`, the degree-`≥ 2` tail `‖log hnorm z - z‖` is bounded by `ρ ^ 2` for `ρ := ‖z‖/‖p‖ < 1`
(`norm_pow_div_natCast_le`, shifted via `hasSum_nat_add_iff' 1`), and `ρ^2 = ‖z‖^2/‖p‖^2 < ‖z‖` is
exactly the threshold hypothesis; `norm_eq_of_norm_sub_lt` then identifies `‖log hnorm z‖ = ‖z‖`. -/
theorem norm_log_eq_of_lt_sq (hnorm : ‖(p : K)‖ < 1) {z : K}
    (hzlt : ‖z‖ < logUnitsThreshold K p) : ‖log hnorm z‖ = ‖z‖ := by
  rcases eq_or_ne z 0 with hz0 | hz0
  · rw [hz0, log_zero, norm_zero]
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzltp2 : ‖z‖ < ‖(p : K)‖ ^ 2 := hzlt
  have hzltp : ‖z‖ < ‖(p : K)‖ := by
    have hp1 : ‖(p : K)‖ ^ 2 < ‖(p : K)‖ := by
      calc ‖(p : K)‖ ^ 2 = ‖(p : K)‖ * ‖(p : K)‖ := sq ‖(p : K)‖
        _ < ‖(p : K)‖ * 1 := mul_lt_mul_of_pos_left hnorm hp0
        _ = ‖(p : K)‖ := mul_one _
    exact hzltp2.trans hp1
  have hx : ‖z‖ < logConvergenceRadius K p := hzltp
  set ρ : ℝ := ‖z‖ / ‖(p : K)‖ with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hzpos.le hp0.le
  have hρlt1 : ρ < 1 := by rw [hρ, div_lt_one hp0]; exact hzltp
  have hρsq_lt : ρ ^ 2 < ‖z‖ := by
    have heq : ρ ^ 2 = ‖z‖ ^ 2 / ‖(p : K)‖ ^ 2 := by rw [hρ, div_pow]
    rw [heq, div_lt_iff₀ (by positivity)]
    have hzsq : ‖z‖ ^ 2 = ‖z‖ * ‖z‖ := sq ‖z‖
    rw [hzsq]
    exact mul_lt_mul_of_pos_left hzltp2 hzpos
  have hsum := hasSum_log hnorm hx
  have hshift : HasSum (fun j => (-1 : K) ^ (j + 1) * z ^ (j + 2) / ((j + 2 : ℕ) : K))
      (log hnorm z - ∑ k ∈ Finset.range 1, (-1 : K) ^ k * z ^ (k + 1) / ((k + 1 : ℕ) : K)) :=
    (hasSum_nat_add_iff' 1).mpr hsum
  have hsum0 : ∑ k ∈ Finset.range 1, (-1 : K) ^ k * z ^ (k + 1) / ((k + 1 : ℕ) : K) = z := by
    simp
  rw [hsum0] at hshift
  have heq : log hnorm z - z = ∑' j, (-1 : K) ^ (j + 1) * z ^ (j + 2) / ((j + 2 : ℕ) : K) :=
    hshift.tsum_eq.symm
  have htail : ‖log hnorm z - z‖ < ‖z‖ := by
    rw [heq]
    refine (IsUltrametricDist.norm_tsum_le _).trans_lt (lt_of_le_of_lt (ciSup_le fun j => ?_) hρsq_lt)
    have hneg1 : ‖(-1 : K) ^ (j + 1)‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
    have hbound : ‖(-1 : K) ^ (j + 1) * z ^ (j + 2) / ((j + 2 : ℕ) : K)‖ ≤ ρ ^ (j + 2) := by
      rw [norm_div, norm_mul, hneg1, one_mul, ← norm_div, hρ]
      exact norm_pow_div_natCast_le hnorm z (n := j + 2) (by omega)
    refine hbound.trans ?_
    exact pow_le_pow_of_le_one hρ0 hρlt1.le (by omega)
  exact norm_eq_of_norm_sub_lt htail

include hA in
/-- **`log` lands in `𝔪_A^i`, with no level shift.** For `x ∈ 𝔪_A^i` and `‖π‖^i` strictly below
`logUnitsThreshold K p`, `log hnorm (x : K)` is itself the coercion of an `A`-element of `𝔪_A^i`.
Combines `norm_le_pow_of_mem_maximalIdeal_pow` (bounding `‖(x:K)‖ ≤ ‖π‖^i`) with
`norm_log_eq_of_lt_sq` (identifying `‖log hnorm (x:K)‖ = ‖(x:K)‖` exactly, so the bound transfers
with **no shift**) and `mem_maximalIdeal_pow_of_norm_le` (converting the resulting norm bound back
into ideal membership). -/
theorem log_mem_maximalIdeal_pow (hnorm : ‖(p : K)‖ < 1) {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : (π : K) ≠ 0)
    (hπnorm : ‖(π : K)‖ < 1) {i : ℕ} (hthresh : ‖(π : K)‖ ^ i < logUnitsThreshold K p)
    {x : A} (hx : x ∈ maximalIdeal A ^ i) :
    ∃ y : A, y ∈ maximalIdeal A ^ i ∧ (y : K) = log hnorm (x : K) := by
  have hxnorm : ‖(x : K)‖ ≤ ‖(π : K)‖ ^ i := norm_le_pow_of_mem_maximalIdeal_pow A hA hπ hx
  have hxltthresh : ‖(x : K)‖ < logUnitsThreshold K p := lt_of_le_of_lt hxnorm hthresh
  have hlogeq : ‖log hnorm (x : K)‖ = ‖(x : K)‖ := norm_log_eq_of_lt_sq hnorm hxltthresh
  have hlognorm : ‖log hnorm (x : K)‖ ≤ ‖(π : K)‖ ^ i := hlogeq ▸ hxnorm
  have hlogA : log hnorm (x : K) ∈ A := by
    apply (hA _).mpr
    calc ‖log hnorm (x : K)‖ ≤ ‖(π : K)‖ ^ i := hlognorm
      _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hπnorm.le
  set y : A := ⟨log hnorm (x : K), hlogA⟩ with hydef
  refine ⟨y, ?_, rfl⟩
  apply mem_maximalIdeal_pow_of_norm_le A hA hπ0 hπ
  show ‖(y : K)‖ ≤ ‖(π : K)‖ ^ i
  simpa [hydef] using hlognorm

omit hA [IsUltrametricDist K] [CompleteSpace K] in
/-- **`logUnitsThreshold K p ≤ expLogCompositionRadius K p` always** — the same exponent-comparison
argument as `logUnitsThreshold_le_expUnitsThreshold`: `expLogCompositionRadius K p = ‖p‖ ^ (p/(p-1))`
and `p/(p-1) ≤ 2` for `p ≥ 2`, so `‖p‖ < 1` makes `expLogCompositionRadius K p ≥ ‖p‖ ^ 2 =
logUnitsThreshold K p`. Needed so `expHom_surjective`'s single strict threshold hypothesis also
places `log`'s output back inside `exp`'s domain, for `exp_log_eq_one_add`. -/
theorem logUnitsThreshold_le_expLogCompositionRadius (hnorm : ‖(p : K)‖ < 1) :
    logUnitsThreshold K p ≤ expLogCompositionRadius K p := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    linarith
  have hexple : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ hp1]
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    nlinarith
  unfold logUnitsThreshold expLogCompositionRadius
  rw [← Real.rpow_natCast ‖(p : K)‖ 2]
  exact Real.rpow_le_rpow_of_exponent_ge hp0 hnorm.le hexple

include hA in
/-- **`expHom` is surjective**, for the same strict threshold `expHom_injective` needs. Given `u ∈
U_A^{(i)}`, `y₀ := (u:A) - 1 ∈ 𝔪_A^i` (`principalUnitsPow`'s defining membership); the preimage is
`log hnorm (y₀:K)`, landing in `𝔪_A^i` with no shift (`log_mem_maximalIdeal_pow`); `exp_log_eq_one_add`
(valid since `‖y₀‖ < logUnitsThreshold K p ≤ expLogCompositionRadius K p`) identifies `exp hnorm (log
hnorm (y₀:K)) = 1 + (y₀:K) = (u:A:K)`, closing the loop via the same `Subtype.ext`/`Units.ext`
reduction to a `K`-level identity that `expHom`'s own definitional equalities use. -/
theorem expHom_surjective (hnorm : ‖(p : K)‖ < 1) {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : (π : K) ≠ 0)
    (hπnorm : ‖(π : K)‖ < 1) {i : ℕ} (hthreshStrict : ‖(π : K)‖ ^ i < logUnitsThreshold K p) :
    Function.Surjective (expHom (A := A) (hA := hA) hnorm hπ hπ0 hπnorm
      (hthreshStrict.trans_le (logUnitsThreshold_le_expUnitsThreshold hnorm)).le) := by
  set hthresh : ‖(π : K)‖ ^ i ≤ expUnitsThreshold K p :=
    (hthreshStrict.trans_le (logUnitsThreshold_le_expUnitsThreshold hnorm)).le with hthreshdef
  intro u
  set uA : Aˣ := (u : Aˣ) with huAdef
  set y0 : A := (uA : A) - 1 with hy0def
  have humem : y0 ∈ maximalIdeal A ^ i :=
    (ValuationSubring.mem_principalUnitsPow_iff A).mp u.2
  obtain ⟨y, hymem, hycoe⟩ :=
    log_mem_maximalIdeal_pow (A := A) (hA := hA) hnorm hπ hπ0 hπnorm hthreshStrict humem
  have hy0norm : ‖(y0 : K)‖ ≤ ‖(π : K)‖ ^ i := norm_le_pow_of_mem_maximalIdeal_pow A hA hπ humem
  have hy0lt : ‖(y0 : K)‖ < expLogCompositionRadius K p :=
    lt_of_le_of_lt hy0norm
      (lt_of_lt_of_le hthreshStrict (logUnitsThreshold_le_expLogCompositionRadius hnorm))
  have hexplog : exp hnorm (log hnorm (y0 : K)) = 1 + (y0 : K) := exp_log_eq_one_add hnorm hy0lt
  have huAeq : ((uA : A) : K) = 1 + (y0 : K) := by rw [hy0def]; push_cast; ring
  refine ⟨Multiplicative.ofAdd (⟨y, hymem⟩ : ↥(maximalIdeal A ^ i)), ?_⟩
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  show ((expUnit A hA hnorm hπ hπ0 hπnorm hthresh
      (Multiplicative.toAdd (Multiplicative.ofAdd (⟨y, hymem⟩ : ↥(maximalIdeal A ^ i)))).2 : A) : K)
      = ((uA : A) : K)
  rw [expUnit_coe]
  show exp hnorm ((⟨y, hymem⟩ : ↥(maximalIdeal A ^ i)).1 : K) = ((uA : A) : K)
  show exp hnorm ((y : A) : K) = ((uA : A) : K)
  rw [hycoe, hexplog, huAeq]

/-! ## The headline isomorphism -/

include hA in
/-- **`U_A^{(i)} ≅ (𝔪_A^i, +)`**, for `A` a `ValuationSubring K`, a uniformizer `π`, and `i` above
the strict threshold `‖π‖^i < logUnitsThreshold K p`. Assembled from `expHom` (a `MonoidHom`,
`expHom_injective`, `expHom_surjective`) via `MulEquiv.ofBijective`. -/
noncomputable def expEquiv (hnorm : ‖(p : K)‖ < 1) {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : (π : K) ≠ 0)
    (hπnorm : ‖(π : K)‖ < 1) {i : ℕ} (hthreshStrict : ‖(π : K)‖ ^ i < logUnitsThreshold K p) :
    Multiplicative ↥(maximalIdeal A ^ i) ≃* ↥(ValuationSubring.principalUnitsPow A i) :=
  MulEquiv.ofBijective _
    ⟨expHom_injective (A := A) (hA := hA) hnorm hπ hπ0 hπnorm
        (hthreshStrict.trans_le (logUnitsThreshold_le_expUnitsThreshold hnorm)).le
        (hthreshStrict.trans_le (logUnitsThreshold_le_expUnitsThreshold hnorm)),
      expHom_surjective (A := A) (hA := hA) hnorm hπ hπ0 hπnorm hthreshStrict⟩

include hA in
/-- **`expEquiv`'s surjectivity, in element form.** Every `u ∈ U_A^{(i)}` is `exp` of an element of
`𝔪_A^i` — the unbundled reading of `expEquiv`/`expHom_surjective`, and the exact converse of
`exp_mem_principalUnitsPow` (whose orientation of the defining equation it matches). Stated this way
it composes directly with facts about `exp` at the level of `K`, with no `Multiplicative`/`Subtype`
bookkeeping at the call site. -/
theorem exists_mem_maximalIdeal_pow_coe_eq_exp (hnorm : ‖(p : K)‖ < 1) {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : (π : K) ≠ 0)
    (hπnorm : ‖(π : K)‖ < 1) {i : ℕ} (hthreshStrict : ‖(π : K)‖ ^ i < logUnitsThreshold K p)
    {u : Aˣ} (hu : u ∈ ValuationSubring.principalUnitsPow A i) :
    ∃ x : A, x ∈ maximalIdeal A ^ i ∧ ((u : A) : K) = exp hnorm (x : K) := by
  set hthresh : ‖(π : K)‖ ^ i ≤ expUnitsThreshold K p :=
    (hthreshStrict.trans_le (logUnitsThreshold_le_expUnitsThreshold hnorm)).le with hthreshdef
  obtain ⟨z, hz⟩ :=
    expHom_surjective (A := A) (hA := hA) hnorm hπ hπ0 hπnorm hthreshStrict ⟨u, hu⟩
  refine ⟨(Multiplicative.toAdd z : ↥(maximalIdeal A ^ i)).1, (Multiplicative.toAdd z).2, ?_⟩
  have hA1 : ((expHom (A := A) (hA := hA) hnorm hπ hπ0 hπnorm hthresh z : Aˣ) : A) = (u : A) := by
    have := congrArg (fun t : ↥(ValuationSubring.principalUnitsPow A i) => (t : Aˣ)) hz
    simpa using congrArg (fun t : Aˣ => (t : A)) this
  have hK1 : ((expUnit A hA hnorm hπ hπ0 hπnorm hthresh (Multiplicative.toAdd z).2 : A) : K)
      = ((u : A) : K) :=
    congrArg (fun a : A => (a : K)) hA1
  rw [expUnit_coe] at hK1
  exact hK1.symm

end NonarchimedeanExponential
