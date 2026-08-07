import Langlands.NonarchimedeanExponentialFiltration
import Langlands.NonarchimedeanExponentialHasSum
import Langlands.PrincipalUnitsFiltration

/-!
# `exp` maps `𝔪_A^i` into the principal-units subgroup `U_A^{(i)}`

`Langlands.NonarchimedeanExponentialFiltration` shows `exp` is *defined* (convergent) on `𝔪_A^i`
for `i` above a computed threshold, but stops short of showing the resulting value actually lands
in `U_A^{(i)} = 1 + 𝔪_A^i` (`Langlands.ValuationSubring.principalUnitsPow`) — that file's "What
remains" list names this precisely as item 3 of `ROADMAP.md`'s wild-case exp/log thread. This file
closes that item.

## Main results

* `expUnitsThreshold` : the real number `‖p‖ ^ (2 / (p - 1))`, a (non-sharp, see below) closed-form
  threshold for `i` via `‖π‖ ^ i ≤ expUnitsThreshold K p`.
* `norm_pow_div_factorial_le_of_mem_maximalIdeal_pow` : the per-term bound the threshold is built to
  give: for `x` with `‖x‖ ≤ ‖π‖ ^ i` and `i` above the threshold, every term `x^k/k!` (`k ≥ 1`) of the
  exponential series has norm `≤ ‖π‖ ^ i`, not merely `→ 0`.
* `norm_exp_sub_one_le` : consequently (via `IsUltrametricDist.norm_tsum_le` applied to `hasSum_exp`,
  shifted to drop the constant term, mirroring `NonarchimedeanExponential.norm_log_le`'s proof shape)
  `‖exp hnorm x - 1‖ ≤ ‖π‖ ^ i`.
* `exp_mem_principalUnitsPow` : **the headline theorem.** For `A` a `ValuationSubring K`, `hA`, a
  uniformizer `π` with `hπ`/`hπ0`/`hπnorm`, `i` above the threshold, and `x : A` with `x ∈ 𝔪_A ^ i`,
  there is a unit `u : Aˣ` with `u ∈ ValuationSubring.principalUnitsPow A i` and
  `((u : A) : K) = exp hnorm (x : K)`. This is exactly `exp` mapping `𝔪_A^i` into `U_A^{(i)}` as a
  function (the "landing statement" — item 3 of the wild-case thread's remaining list).

## On the threshold: the non-sharp fallback, not Serre's sharp bound

The classical (Serre, *Local Fields* Ch. II) threshold is `i > v(p)/(p-1)` (additive valuation,
`v(π) = 1`), using the *sharp* Legendre bound `padicValNat p k! ≤ (k-1)/(p-1)` for `k ≥ 1` (dropping
only the base-`p` digit sum, which is `≥ 1` for `k ≠ 0`, rather than the whole `k - digitsum` term).
This file instead uses the *crude* bound already available as
`NonarchimedeanExponential.padicValNat_factorial_le_div` (`padicValNat p k! ≤ k/(p-1)`, dropping the
entire digit-sum term), which forces the threshold here to be twice as large:
`‖π‖ ^ i ≤ ‖p‖ ^ (2/(p-1))` rather than Serre's `‖π‖ ^ i ≤ ‖p‖ ^ (1/(p-1))`. The gap between the two
is exactly the gap between the crude and sharp Legendre bounds; deriving the sharp version (needing
`Nat.digits`/digit-sum lemmas to show the digit sum of a nonzero `k` is `≥ 1`) was not attempted this
pass — see `ROADMAP.md`'s pass log for the precise scoping call. Both this file's threshold and
Serre's are honest, provable statements at this level of generality; this file's is simply not the
sharp one.

Separately: this threshold is stated directly in terms of `‖π‖`, `‖p‖`, and `p` — not in the
classical form `i > e · v(p)/(p-1)` with `e` a ramification index.
`Langlands.NonarchimedeanExponentialExtension`'s module docstring already flags that expressing `‖π‖`
as a ramification-index-th root of `‖p‖` (which is what would let a literal `e` appear) needs
concrete two-field instance data not constructed anywhere in this repo (`ROADMAP.md`'s wild-case
scoping pass); at the abstract single-`ValuationSubring` level of generality used here, `‖π‖` and
`‖p‖` are independent data, and the threshold can only be phrased in terms of both directly, as
above. This is `ROADMAP.md`'s item 4 ("Serre's explicit closed-form threshold") — not reached in the
`e`-parametrized form; what is reached is a genuinely explicit (not merely existential) threshold in
the weaker `‖π‖`/`‖p‖`-only form.

## What remains

* **The group-homomorphism law** `exp (x + y) = exp x * exp y` is proved in
  `Langlands.NonarchimedeanExponentialAdd` (`exp_add`), but the *packaging* it enables — upgrading
  this file's pointwise landing statement to a bundled group homomorphism `𝔪_A^i →* U_A^{(i)}` — is
  still not done here.
* **Serre's sharp threshold** (`‖π‖ ^ i ≤ ‖p‖ ^ (1/(p-1))`, matching the classical statement exactly)
  is not derived — see "On the threshold" above.
* **The concrete `HeightOneSpectrum` instantiation** of this file's abstract `ValuationSubring`
  statement is not done, for the same reason `NonarchimedeanExponentialFiltration`'s is not: no
  mixed-characteristic concrete field instance exists anywhere in this repo yet.
-/

noncomputable section

open IsLocalRing Filter Topology

namespace NonarchimedeanExponential

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
variable {p : ℕ} [hp : Fact p.Prime]

/-- **The units-filtration threshold.** `‖p‖ ^ (2/(p-1))` — twice the exponent of the sharp
classical threshold `‖p‖ ^ (1/(p-1))`, an artifact of using the crude (not sharp) Legendre bound
`padicValNat_factorial_le_div`; see the module docstring's "On the threshold" section. -/
def expUnitsThreshold (K : Type*) [NormedField K] (p : ℕ) : ℝ :=
  ‖(p : K)‖ ^ (2 / ((p : ℝ) - 1))

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `expUnitsThreshold K p < convergenceRadius K p`: the units threshold is strictly more
conservative than `exp`'s own convergence threshold, since `2/(p-1) > 1/(p-1)` and `‖p‖ < 1`. -/
theorem expUnitsThreshold_lt_convergenceRadius (hnorm : ‖(p : K)‖ < 1) :
    expUnitsThreshold K p < convergenceRadius K p := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    linarith
  unfold expUnitsThreshold convergenceRadius
  refine Real.rpow_lt_rpow_of_exponent_gt hp0 hnorm ?_
  rw [inv_eq_one_div, div_lt_div_iff_of_pos_right hp1]
  norm_num

omit [CompleteSpace K] in
/-- **The per-term bound giving the landing statement.** For `x : K` with `‖x‖ ≤ ‖π‖ ^ i` (`‖π‖ <
1`) and `i` above `expUnitsThreshold`, every term `x^k/k!` for `k ≥ 1` has norm `≤ ‖π‖ ^ i` — not
merely `→ 0`. The `k = 1` case is immediate from the hypothesis; for `k ≥ 2`, with
`ρ := ‖π‖^i / ‖p‖^(1/(p-1))`, `norm_pow_div_factorial_le` gives `‖x^k/k!‖ ≤ ρ^k`, and the threshold
is exactly what forces `ρ^2 ≤ ‖π‖^i` (algebra) and `ρ < 1` (so `ρ^k ≤ ρ^2` for `k ≥ 2`,
`pow_le_pow_of_le_one`). -/
theorem norm_pow_div_factorial_le_of_mem_maximalIdeal_pow (hnorm : ‖(p : K)‖ < 1)
    {i : ℕ} {π : K} (hthresh : ‖π‖ ^ i ≤ expUnitsThreshold K p) {x : K}
    (hxnorm : ‖x‖ ≤ ‖π‖ ^ i) {k : ℕ} (hk : 1 ≤ k) :
    ‖x ^ k / (k.factorial : K)‖ ≤ ‖π‖ ^ i := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · -- k = 1
    rw [← hk1]
    simpa using hxnorm
  · -- k ≥ 2
    have hk2' : 2 ≤ k := hk2
    set d : ℝ := ‖(p : K)‖ ^ (((p : ℝ) - 1)⁻¹) with hd
    have hd0 : (0 : ℝ) < d := Real.rpow_pos_of_pos hp0 _
    have hbase := norm_pow_div_factorial_le hnorm x k
    have hle1 : ‖x‖ / d ≤ ‖π‖ ^ i / d := div_le_div_of_nonneg_right hxnorm hd0.le
    have hpow_le : (‖x‖ / d) ^ k ≤ (‖π‖ ^ i / d) ^ k :=
      pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hd0.le) hle1 k
    set ρ : ℝ := ‖π‖ ^ i / d with hρ
    have hρnonneg : 0 ≤ ρ := div_nonneg (by positivity) hd0.le
    have hρlt1 : ρ < 1 := by
      rw [hρ, hd, div_lt_one hd0]
      calc ‖π‖ ^ i ≤ expUnitsThreshold K p := hthresh
        _ < convergenceRadius K p := expUnitsThreshold_lt_convergenceRadius hnorm
        _ = ‖(p : K)‖ ^ (((p : ℝ) - 1)⁻¹) := rfl
    have hρ2_le : ρ ^ 2 ≤ ‖π‖ ^ i := by
      have hrpow2 : d ^ (2 : ℕ) = expUnitsThreshold K p := by
        unfold expUnitsThreshold
        rw [hd, ← Real.rpow_natCast (‖(p : K)‖ ^ (((p : ℝ) - 1)⁻¹)) 2, ← Real.rpow_mul hp0.le]
        congr 1
        rw [div_eq_mul_inv]
        ring
      have hthresh0 : (0 : ℝ) < expUnitsThreshold K p := Real.rpow_pos_of_pos hp0 _
      rw [hρ, div_pow, hrpow2, div_le_iff₀ hthresh0, sq]
      exact mul_le_mul_of_nonneg_left hthresh (by positivity)
    have hρk_le_ρ2 : ρ ^ k ≤ ρ ^ 2 := pow_le_pow_of_le_one hρnonneg hρlt1.le hk2'
    calc ‖x ^ k / (k.factorial : K)‖ ≤ (‖x‖ / d) ^ k := hbase
      _ ≤ (‖π‖ ^ i / d) ^ k := hpow_le
      _ = ρ ^ k := rfl
      _ ≤ ρ ^ 2 := hρk_le_ρ2
      _ ≤ ‖π‖ ^ i := hρ2_le

/-- **A norm bound on the tail of `exp`'s series (`exp x - 1`).** For `x` with `‖x‖ ≤ ‖π‖ ^ i` and
`i` above `expUnitsThreshold`, `‖exp hnorm x - 1‖ ≤ ‖π‖ ^ i`. Proved exactly like
`NonarchimedeanExponential.norm_log_le`: split off the constant term via `hasSum_nat_add_iff'`, then
bound the shifted sum via `IsUltrametricDist.norm_tsum_le` and the per-term bound above. -/
theorem norm_exp_sub_one_le (hnorm : ‖(p : K)‖ < 1) {i : ℕ} {π : K}
    (hthresh : ‖π‖ ^ i ≤ expUnitsThreshold K p) {x : K} (hxnorm : ‖x‖ ≤ ‖π‖ ^ i) :
    ‖exp hnorm x - 1‖ ≤ ‖π‖ ^ i := by
  have hx : ‖x‖ < convergenceRadius K p :=
    lt_of_le_of_lt hxnorm (lt_of_le_of_lt hthresh (expUnitsThreshold_lt_convergenceRadius hnorm))
  have hsum := hasSum_exp hnorm hx
  have hshift : HasSum (fun n => x ^ (n + 1) / ((n + 1).factorial : K))
      (exp hnorm x - ∑ j ∈ Finset.range 1, x ^ j / (j.factorial : K)) :=
    (hasSum_nat_add_iff' 1).mpr hsum
  have hsum0 : ∑ j ∈ Finset.range 1, x ^ j / (j.factorial : K) = 1 := by simp
  rw [hsum0] at hshift
  have heq : exp hnorm x - 1 = ∑' n, x ^ (n + 1) / ((n + 1).factorial : K) := hshift.tsum_eq.symm
  rw [heq]
  refine (IsUltrametricDist.norm_tsum_le _).trans (ciSup_le fun n => ?_)
  exact norm_pow_div_factorial_le_of_mem_maximalIdeal_pow hnorm hthresh hxnorm n.succ_pos

/-! ## The headline theorem: `exp` lands in `U_A^{(i)}` -/

variable (A : ValuationSubring K) (hA : ∀ x : K, x ∈ A ↔ ‖x‖ ≤ 1)

include hA in
/-- **`exp` maps `𝔪_A^i` into the principal-units subgroup `U_A^{(i)}`.** For `A` a
`ValuationSubring K`, `hA`, a uniformizer `π` (`hπ`, `hπ0`, `hπnorm`), `i` above
`expUnitsThreshold`, and `x : A` with `x ∈ 𝔪_A ^ i`, there is a unit `u : Aˣ` with
`u ∈ ValuationSubring.principalUnitsPow A i` and `((u : A) : K) = exp hnorm (x : K)`.

Proof outline: `norm_exp_sub_one_le` bounds `‖exp hnorm (x:K) - 1‖ ≤ ‖π‖ ^ i`, which
`mem_maximalIdeal_pow_of_norm_le` upgrades to an actual `A`-element `y ∈ 𝔪_A ^ i` with
`(y : K) = exp hnorm (x:K) - 1`. Then `1 + y : A` is a unit (`1 + 𝔪_A`-elements are units in a local
ring, `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits` applied to `-y`, the same trick
`ValuationSubring.principalUnitsGradedHom_surjective` uses), and its underlying unit lies in
`principalUnitsPow A i` by construction (`(1 + y) - 1 = y ∈ 𝔪_A ^ i`). -/
theorem exp_mem_principalUnitsPow (hnorm : ‖(p : K)‖ < 1) {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) (hπ0 : (π : K) ≠ 0)
    (hπnorm : ‖(π : K)‖ < 1) {i : ℕ} (hthresh : ‖(π : K)‖ ^ i ≤ expUnitsThreshold K p)
    {x : A} (hx : x ∈ maximalIdeal A ^ i) :
    ∃ u : Aˣ, u ∈ ValuationSubring.principalUnitsPow A i ∧ ((u : A) : K) = exp hnorm (x : K) := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · exfalso
      rw [hi0, pow_zero] at hthresh
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hlt1 : expUnitsThreshold K p < 1 :=
        Real.rpow_lt_one (norm_nonneg _) hnorm (by positivity)
      linarith
    · exact hi0
  have hxnorm : ‖(x : K)‖ ≤ ‖(π : K)‖ ^ i := norm_le_pow_of_mem_maximalIdeal_pow A hA hπ hx
  have hnormbound : ‖exp hnorm (x : K) - 1‖ ≤ ‖(π : K)‖ ^ i :=
    norm_exp_sub_one_le hnorm hthresh hxnorm
  have hy0 : (0 : K) = (0 : A) := rfl
  -- Build the `A`-element `y` with `(y : K) = exp hnorm (x : K) - 1`.
  have hyA : exp hnorm (x : K) - 1 ∈ A := by
    have h1 : ‖exp hnorm (x : K) - 1‖ ≤ 1 :=
      le_trans hnormbound (by
        calc ‖(π : K)‖ ^ i ≤ 1 := by
              have := hπnorm.le
              exact pow_le_one₀ (norm_nonneg _) this)
    exact (hA _).mpr h1
  set y : A := ⟨exp hnorm (x : K) - 1, hyA⟩ with hydef
  have hymem : y ∈ maximalIdeal A ^ i :=
    mem_maximalIdeal_pow_of_norm_le A hA hπ0 hπ (by
      show ‖(y : K)‖ ≤ ‖(π : K)‖ ^ i
      simpa [hydef] using hnormbound)
  have hycoe : (y : K) = exp hnorm (x : K) - 1 := rfl
  set expA : A := 1 + y with hexpAdef
  have hexpAcoe : (expA : K) = exp hnorm (x : K) := by
    show (1 : K) + (y : K) = exp hnorm (x : K)
    rw [hycoe]; ring
  have hmem1 : y ∈ maximalIdeal A := by
    have hle : maximalIdeal A ^ i ≤ maximalIdeal A ^ 1 := Ideal.pow_le_pow_right hi1
    have hmem := hle hymem
    rwa [pow_one] at hmem
  have hnonunit : -y ∈ nonunits A := by
    apply (IsLocalRing.mem_maximalIdeal _).mp
    exact (maximalIdeal A).neg_mem hmem1
  have hunit : IsUnit expA := by
    have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-y) hnonunit
    simpa [hexpAdef, sub_neg_eq_add] using h
  refine ⟨hunit.unit, ?_, ?_⟩
  · show (hunit.unit : A) - 1 ∈ maximalIdeal A ^ i
    have hval : (hunit.unit : A) = expA := hunit.unit_spec
    rw [hval, hexpAdef, add_sub_cancel_left]
    exact hymem
  · have hval : (hunit.unit : A) = expA := hunit.unit_spec
    rw [hval, hexpAcoe]

end NonarchimedeanExponential

end
