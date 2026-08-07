import Langlands.NonarchimedeanExponential
import Langlands.PrincipalUnitsFiltration

/-!
# Translating the exponential's convergence threshold into filtration-level language

`Langlands.NonarchimedeanExponential` builds `exp`/`log` and proves convergence purely in terms of
the abstract threshold `‖x‖ < convergenceRadius K p` (resp. `logConvergenceRadius K p`). This file
takes the first step toward the payoff stated in that file's "What remains" list — connecting that
abstract threshold to `x ∈ 𝔪_A^i` for a valuation subring `A` of `K` and an explicit `i`. The further
step — showing `exp x` actually lands in `U_A^{(i)} = ValuationSubring.principalUnitsPow A i`, not
merely that it converges — is now closed in
`Langlands.NonarchimedeanExponentialUnitsFiltration.exp_mem_principalUnitsPow`, which builds on this
file's `norm_le_pow_of_mem_maximalIdeal_pow` and its converse `mem_maximalIdeal_pow_of_norm_le`
(added here, see below). The remaining gap to the full statement `exp : 𝔪_L^i →+ U_L^{(i)}` that
`NonarchimedeanExponential`'s docstring targets is the group-homomorphism law, not attempted anywhere
in this thread — see "What remains" below.

## Scope: abstract `ValuationSubring`, not the concrete `HeightOneSpectrum` setting

The task this file was scoped against asked for the concrete `w.adicCompletionIntegers L` setting of
`Langlands.PrincipalUnitsFiltrationAdicCompletion`. That setting needs `w.adicCompletion L` to carry
`CharZero` (a nontrivial fact about the *mixed*-characteristic case: `L` itself of characteristic `0`
with residue characteristic `p`) and a `Fact p.Prime` / residue-characteristic-`p` instance for
`IsLocalRing.ResidueField (w.adicCompletionIntegers L)`. Neither is available anywhere in this repo:
`ROADMAP.md` has repeatedly flagged (since the fortieth pass) that `IsTotallyRamified`/
`IsTamelyRamified` have **no nontrivial instances constructed anywhere in this repo**, and the one
concrete field example that does exist (`Langlands.TotallyRamifiedConcreteExample`) is deliberately
*equal*-characteristic (`CharP K p`, not `CharZero K`) — the opposite of what `exp`/`log` need.
Building a genuine mixed-characteristic concrete instance is itself a substantial, unattempted task,
so this file works at the same level of generality as `Langlands.PrincipalUnitsFiltration` (an
abstract `ValuationSubring A` of a field `K`) rather than force a concrete instantiation that does
not yet exist. The concrete specialization is mechanical *given* such an instance, but is not done
here.

## Main results

* `norm_le_pow_of_mem_maximalIdeal_pow` : for `A` a `ValuationSubring K` whose membership matches the
  norm's unit ball (`hA`) and `π` a uniformizer, `x ∈ 𝔪_A^i → ‖x‖ ≤ ‖π‖^i` — the "ideal power implies
  norm bound" half of the classical filtration/norm correspondence.
* `mem_maximalIdeal_pow_of_norm_le` : the converse — `‖x‖ ≤ ‖π‖^i → x ∈ 𝔪_A^i`, for `x : A` — proved
  directly from `hA` with no discrete-valuation-ring uniqueness argument needed. Originally flagged
  as "not proved or needed here"; it turned out to be exactly the fact
  `Langlands.NonarchimedeanExponentialUnitsFiltration.exp_mem_principalUnitsPow` needs to convert its
  tail-sum norm bound on `exp x - 1` into genuine ideal membership.
* `exists_maximalIdeal_pow_le_convergenceRadius` / `..._le_logConvergenceRadius` : since
  `‖π‖ < 1`, `‖π‖^i → 0`, so some explicit `i₀` has `‖π‖^i₀` strictly below the relevant threshold;
  combined with the previous result and antitonicity of `i ↦ ‖π‖^i`, `𝔪_A^i` lies inside the
  convergence domain of `exp` (resp. `log`) for every `i ≥ i₀`.

## What remains

* **Landing in `U_A^{(i)}`, not just convergence.** Closed — see
  `Langlands.NonarchimedeanExponentialUnitsFiltration.exp_mem_principalUnitsPow`.
* **An explicit closed-form `i` in terms of `e` and `p`.** Partially reached: that file's
  `expUnitsThreshold` gives a genuinely explicit (not merely existential) threshold, but in terms of
  `‖π‖`/`‖p‖` directly rather than the classical `e·v(p)/(p-1)` form, and it is twice Serre's sharp
  constant (a consequence of using the crude, not sharp, Legendre bound already available in
  `NonarchimedeanExponential`). Reaching the literal `e`-parametrized sharp bound still needs
  `‖π_A‖` expressed in terms of `‖π_K‖`'s ramification-index-th root, which is exactly the
  concrete-instance data flagged as missing above.
* **The concrete `HeightOneSpectrum` instantiation** (`A := w.adicCompletionIntegers L`,
  `K := w.adicCompletion L`) is not done — see "Scope" above.
-/

noncomputable section

open IsLocalRing

namespace NonarchimedeanExponential

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable (A : ValuationSubring K) (hA : ∀ x : K, x ∈ A ↔ ‖x‖ ≤ 1)

omit [IsUltrametricDist K] [CharZero K] in
include hA in
/-- **Ideal-power membership bounds the norm.** For `A` a `ValuationSubring K` whose membership
matches the norm's closed unit ball (`hA`) and `π` a uniformizer of `A` (`hπ`), an element of
`𝔪_A ^ i` has norm `≤ ‖π‖ ^ i`. Proved by writing `𝔪_A ^ i = span {π ^ i}` (`Ideal.span_singleton_pow`)
so membership gives `x = π ^ i * c` for some `c : A` (`Ideal.mem_span_singleton`), and `‖c‖ ≤ 1`
(`hA`, `c : A`) bounds the extra factor. -/
theorem norm_le_pow_of_mem_maximalIdeal_pow {π : A}
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) {i : ℕ} {x : A}
    (hx : x ∈ maximalIdeal A ^ i) : ‖(x : K)‖ ≤ ‖(π : K)‖ ^ i := by
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := hx
  have hcnorm : ‖(c : K)‖ ≤ 1 := (hA (c : K)).mp (SetLike.coe_mem c)
  have hxeq : (x : K) = (π : K) ^ i * (c : K) := by exact_mod_cast congrArg Subtype.val hc
  rw [hxeq, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) i) hcnorm

omit [IsUltrametricDist K] [CharZero K] in
include hA in
/-- **Converse of `norm_le_pow_of_mem_maximalIdeal_pow`: a norm bound implies ideal-power
membership.** For `π` a uniformizer of `A` with `(π : K) ≠ 0`, an element `x : A` with
`‖(x : K)‖ ≤ ‖(π : K)‖ ^ i` already lies in `𝔪_A ^ i`. Proved directly from `hA`, with no need for
`A` to be a discrete valuation ring or for any uniqueness-of-valuation argument: `y := (x : K) /
(π : K) ^ i` has `‖y‖ ≤ 1` (dividing the hypothesis by `‖π‖ ^ i > 0`), hence `y ∈ A` by `hA`; the
resulting `A`-element `c` satisfies `x = π ^ i * c` in `A` (transported from the `K`-equality
`(x : K) = (π : K) ^ i * y` via injectivity of the coercion `A → K`), i.e. `x ∈ span {π ^ i} = 𝔪_A ^
i`. -/
theorem mem_maximalIdeal_pow_of_norm_le {π : A} (hπ0 : (π : K) ≠ 0)
    (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) {i : ℕ} {x : A}
    (hx : ‖(x : K)‖ ≤ ‖(π : K)‖ ^ i) : x ∈ maximalIdeal A ^ i := by
  have hπpow0 : (0 : ℝ) < ‖(π : K)‖ ^ i := by positivity
  set y : K := (x : K) / (π : K) ^ i with hy
  have hynorm : ‖y‖ ≤ 1 := by
    rw [hy, norm_div, norm_pow, div_le_one hπpow0]
    exact hx
  have hyA : y ∈ A := (hA y).mpr hynorm
  set c : A := ⟨y, hyA⟩ with hc
  have hxeq : (x : K) = (π : K) ^ i * (c : K) := by
    show (x : K) = (π : K) ^ i * y
    rw [hy]
    field_simp
  have hxeqA : x = π ^ i * c := by
    apply Subtype.ext
    push_cast
    exact hxeq
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨c, by rw [hxeqA]; ring⟩

omit [IsUltrametricDist K] hA in
/-- **A threshold `i₀` above which `𝔪_A^i` lies inside `exp`'s convergence domain**, for `{π : A}`
a uniformizer with `‖π‖ < 1`: since `‖π‖ ^ i → 0` (`‖π‖ < 1`), some `i₀` has
`‖π‖ ^ i₀ < convergenceRadius K p` (`exists_pow_lt_of_lt_one`), and by antitonicity of `i ↦ ‖π‖ ^ i`
(`‖π‖ ≤ 1`), the same bound holds for every `i ≥ i₀`. -/
theorem exists_maximalIdeal_pow_le_convergenceRadius {p : ℕ} [Fact p.Prime]
    {π : A} (hπnorm : ‖(π : K)‖ < 1) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ‖(π : K)‖ ^ i < convergenceRadius K p := by
  have hcr0 : (0 : ℝ) < convergenceRadius K p := Real.rpow_pos_of_pos norm_natCast_pos _
  obtain ⟨i₀, hi₀⟩ := exists_pow_lt_of_lt_one hcr0 hπnorm
  refine ⟨i₀, fun i hi => lt_of_le_of_lt ?_ hi₀⟩
  exact pow_le_pow_of_le_one (norm_nonneg _) hπnorm.le hi

omit [IsUltrametricDist K] hA in
/-- The `log`-domain analogue of `exists_maximalIdeal_pow_le_convergenceRadius`, at the (more
conservative) threshold `logConvergenceRadius K p = ‖p‖`. -/
theorem exists_maximalIdeal_pow_le_logConvergenceRadius {p : ℕ} [Fact p.Prime]
    {π : A} (hπnorm : ‖(π : K)‖ < 1) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ‖(π : K)‖ ^ i < logConvergenceRadius K p := by
  have hcr0 : (0 : ℝ) < logConvergenceRadius K p := norm_natCast_pos
  obtain ⟨i₀, hi₀⟩ := exists_pow_lt_of_lt_one hcr0 hπnorm
  refine ⟨i₀, fun i hi => lt_of_le_of_lt ?_ hi₀⟩
  exact pow_le_pow_of_le_one (norm_nonneg _) hπnorm.le hi

omit [IsUltrametricDist K] in
include hA in
/-- **Putting the two together: `exp` is defined (convergent) on all of `𝔪_A^i` for `i` above the
threshold.** Combines `norm_le_pow_of_mem_maximalIdeal_pow` (the ideal-power-to-norm bound) with
`exists_maximalIdeal_pow_le_convergenceRadius` (the threshold's existence). -/
theorem exists_forall_mem_maximalIdeal_pow_norm_lt_convergenceRadius {p : ℕ} [Fact p.Prime]
    (_hnorm : ‖(p : K)‖ < 1) {π : A} (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    (hπnorm : ‖(π : K)‖ < 1) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : A, x ∈ maximalIdeal A ^ i → ‖(x : K)‖ < convergenceRadius K p := by
  obtain ⟨i₀, hi₀⟩ := exists_maximalIdeal_pow_le_convergenceRadius A hπnorm (p := p)
  exact ⟨i₀, fun i hi x hx =>
    lt_of_le_of_lt (norm_le_pow_of_mem_maximalIdeal_pow A hA hπ hx) (hi₀ i hi)⟩

omit [IsUltrametricDist K] in
include hA in
/-- The `log`-domain analogue of `exists_forall_mem_maximalIdeal_pow_norm_lt_convergenceRadius`. -/
theorem exists_forall_mem_maximalIdeal_pow_norm_lt_logConvergenceRadius {p : ℕ} [Fact p.Prime]
    (_hnorm : ‖(p : K)‖ < 1) {π : A} (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    (hπnorm : ‖(π : K)‖ < 1) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : A, x ∈ maximalIdeal A ^ i → ‖(x : K)‖ < logConvergenceRadius K p := by
  obtain ⟨i₀, hi₀⟩ := exists_maximalIdeal_pow_le_logConvergenceRadius A hπnorm (p := p)
  exact ⟨i₀, fun i hi x hx =>
    lt_of_le_of_lt (norm_le_pow_of_mem_maximalIdeal_pow A hA hπ hx) (hi₀ i hi)⟩

end NonarchimedeanExponential

end
