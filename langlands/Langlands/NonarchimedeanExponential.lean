import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.MaxPowDiv

/-!
# A convergent nonarchimedean exponential

The classical `p`-adic exponential `exp(x) = Σ x^n/n!` converges on a ball around `0` in any
complete, characteristic-`0`, nonarchimedean-valued field of residue characteristic `p`. This file
builds that convergence theory from scratch for a *general* such field (not just `ℚ_p`), phrased
purely in terms of `NormedField`/`IsUltrametricDist` — no `HeightOneSpectrum`/`adicCompletion`
machinery is needed for this part, and none is assumed, so this file is independent of the rest of
this repo's local-field infrastructure and could be lifted out (upstream candidate: confirmed
absent from Mathlib in every form checked — `padicLog`, `expLocal`, valuation-tied `exp`/`log`,
Lubin–Tate constructions — see `ROADMAP.md`'s wild-ramification scoping pass).

## Motivation

This is step 1 of a from-scratch construction of the classical fix for the wild-ramification gap
in this repo's totally-ramified norm-group thread (`Langlands.TotallyRamifiedTrace`,
`Langlands.TotallyRamifiedNormSurjective`): in the wild case (`char 𝓀[K] ∣ e`), the tame case's key
computation — the norm induces multiplication-by-`e` on the residue-graded pieces of the
principal-units filtration — degenerates to the zero map at every filtration level, so no variant
of the tame argument closes the wild case. The classical replacement (Serre) is that, above the
ramification break, a `p`-adic exponential/logarithm gives an isomorphism `U_L^{(i)} ≅ (𝔪_L^i, +)`,
turning the norm computation additive instead of multiplicative-residue. This file builds the
exponential map and its convergence; it does **not** attempt the isomorphism with a logarithm, the
translation to a specific principal-units subgroup `U_L^{(i)}` of a `HeightOneSpectrum`-style
`w.adicCompletionIntegers L`, or the norm-compatibility formula `N(exp x) = exp(Tr x)` that would
actually close the wild case — see the module docstring's "What remains" list at the bottom.

## Why `CharZero K` is essential, not a simplifying convenience

`IsNonarchimedeanLocalField` (this repo's ambient notion of "nonarchimedean local field", via
Mathlib's `Mathlib.NumberTheory.LocalField.Basic`) covers **both** mixed-characteristic fields
(finite extensions of `ℚ_p`) and equal-characteristic fields (finite extensions of `𝔽_p((t))`).
In equal characteristic, `char K = p` and the natural map `ℕ → K` kills every multiple of `p`; in
particular `(n ! : K) = 0` for every `n ≥ p`, so the defining series `Σ x^n/n!` is division by zero
from the `p`-th term on. The exponential map is a **mixed-characteristic-only** construction — this
is a classical fact, not an artifact of this formalization — and `[CharZero K]` is the hypothesis
that excludes the equal-characteristic case. Downstream uses of this file must supply a field of
characteristic `0`.

## Route

1. `norm_natCast_eq_one_of_not_dvd`: an integer coprime to the residue characteristic `p` has norm
   exactly `1`. Proved via Bézout (`Nat.gcd_eq_gcd_ab`) and the ultrametric triangle inequality —
   the same "coprime-to-`p`-integers-are-units" fact that underlies the whole `p`-adic norm, made
   available here purely from `‖(p : K)‖ < 1` and `IsUltrametricDist`, with no valuation-subring or
   residue-field machinery.
2. `norm_factorial_eq`: consequently `‖(n ! : K)‖ = ‖(p : K)‖ ^ (padicValNat p n !)` exactly, by
   splitting `n ! = p ^ (padicValNat p n !) * (coprime part)` (`Nat.pow_padicValNat_mul_divMaxPow`,
   `Nat.not_dvd_divMaxPow`) and applying step 1 to the coprime part.
3. `padicValNat_factorial_le_div`: Legendre's theorem, via Mathlib's
   `sub_one_mul_padicValNat_factorial` (`(p - 1) * padicValNat p n ! = n - digitsum`, already in
   `Mathlib.NumberTheory.Padics.PadicVal.Basic`), gives `padicValNat p n ! ≤ n / (p - 1)` as reals.
4. `norm_pow_div_factorial_le`: combining 2–3 with `Real.rpow_le_rpow_of_exponent_ge` (a base in
   `(0, 1]` is exponent-antitone) bounds each term of the series geometrically:
   `‖x ^ n / n !‖ ≤ (‖x‖ / ‖p‖ ^ (1/(p-1))) ^ n`. The classical threshold falls out as exactly the
   condition making the base of this geometric bound `< 1`: `‖x‖ < ‖p‖ ^ (1/(p-1))`, i.e.
   (converting to additive valuation with `v(π) = 1`) `v(x) > v(p)/(p - 1)`.
5. `cauchySeq_partialSum`: the partial sums of the series are Cauchy on this domain, via
   `cauchySeq_of_le_geometric` fed the bound from step 4 (the same pattern this repo's
   `Langlands.PrincipalUnitsSuccessiveApproximation.cauchySeq_approxUnit` uses for its own geometric
   Cauchy-sequence argument).
6. `exp`: given `[CompleteSpace K]`, the limit exists (`cauchySeq_tendsto_of_complete`); `exp` is
   defined as that limit on the convergence domain and `0` outside it.

## What remains

Not attempted in this file, and not small:

* **The isomorphism with a logarithm** (`log` as the two-sided inverse of `exp` on the appropriate
  domain) — needed to actually turn `U_L^{(i)}` into `(𝔪_L^i, +)`, not just to produce *a* map into
  `L`.
* **Translating the abstract threshold `‖x‖ < ‖p‖^(1/(p-1))` into a concrete filtration level** `i`
  of `w.adicCompletionIntegers L`'s principal units (`ValuationSubring.principalUnitsPow`, this
  repo's `Langlands.PrincipalUnitsFiltrationAdicCompletion`), i.e. showing `exp` maps
  `𝔪_L^i` into `U_L^{(i)}` for `i` above the ramification break, and is a bijection onto it.
* **The norm/trace compatibility** `N_{L/K}(exp x) = exp(Tr_{L/K}(x))` (or whatever the precise
  mechanism is) that would let this replace the tame case's residue-multiplication argument in the
  wild-ramification norm-group computation. This is the actual payoff and is not attempted here.
* Group-homomorphism properties of `exp` itself (`exp(x+y) = exp x * exp y` on a suitable domain)
  are not proved — only convergence (existence of the limit) is.

This file closes only the convergence-theory foundation (Serre, *Local Fields* Ch. II §2's estimate,
generalized past `ℚ_p`); the wild case of the totally-ramified norm-group index theorem is not
closed by this file alone.
-/

noncomputable section

open Filter Topology

namespace NonarchimedeanExponential

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable {p : ℕ} [hp : Fact p.Prime]

omit [IsUltrametricDist K] in
/-- The image of the residue characteristic `p` in `K` is nonzero (by `CharZero`), hence has
positive norm. -/
theorem norm_natCast_pos : (0 : ℝ) < ‖(p : K)‖ :=
  norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.pos.ne')

omit [CharZero K] in
/-- **An integer coprime to the residue characteristic has norm exactly `1`.** Given
`‖(p : K)‖ < 1`: write `1 = p * a + m * b` (Bézout, `Nat.gcd_eq_gcd_ab`, using `Nat.Coprime p m`);
the ultrametric inequality gives `1 = ‖1‖ ≤ max ‖p‖ ‖m‖`, and since `‖p‖ < 1`, this forces
`‖m‖ ≥ 1`; combined with the general bound `‖m‖ ≤ 1` (`IsUltrametricDist.norm_natCast_le_one`),
`‖m‖ = 1`. -/
theorem norm_natCast_eq_one_of_not_dvd (hnorm : ‖(p : K)‖ < 1) {m : ℕ} (hm : ¬p ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime p m := hp.out.coprime_iff_not_dvd.mpr hm
  have hbezout : (1 : ℤ) = p * p.gcdA m + m * p.gcdB m := by
    have h := Nat.gcd_eq_gcd_ab p m
    rw [hcop] at h
    exact_mod_cast h
  have hcast : (1 : K) = (p : K) * ((p.gcdA m : ℤ) : K) + (m : K) * ((p.gcdB m : ℤ) : K) := by
    have h := congrArg (fun z : ℤ => (z : K)) hbezout
    push_cast at h
    exact h
  have hle : (1 : ℝ) ≤ max ‖(p : K)‖ ‖(m : K)‖ := by
    calc (1 : ℝ) = ‖(1 : K)‖ := norm_one.symm
      _ = ‖(p : K) * ((p.gcdA m : ℤ) : K) + (m : K) * ((p.gcdB m : ℤ) : K)‖ := by rw [← hcast]
      _ ≤ max ‖(p : K) * ((p.gcdA m : ℤ) : K)‖ ‖(m : K) * ((p.gcdB m : ℤ) : K)‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max ‖(p : K)‖ ‖(m : K)‖ := by
          apply max_le_max <;> rw [norm_mul] <;>
            exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one K _)
  have hmle : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  by_contra hne
  have hmlt : ‖(m : K)‖ < 1 := lt_of_le_of_ne hmle hne
  exact absurd hle (not_le.mpr (max_lt hnorm hmlt))

omit [CharZero K] in
/-- **The norm of `n !` is exactly `‖p‖` to the power of its `p`-adic valuation.** Splitting
`n ! = p ^ (padicValNat p n !) * (n !).divMaxPow p` (`Nat.pow_padicValNat_mul_divMaxPow`), the
second factor is coprime to `p` (`Nat.not_dvd_divMaxPow`), hence has norm `1`
(`norm_natCast_eq_one_of_not_dvd`); multiplicativity of the norm gives the exact value.

Note this identity holds regardless of `CharZero` — it is `norm_pow_div_factorial_le` below,
dividing by `n !`, where `CharZero` becomes essential. -/
theorem norm_factorial_eq (hnorm : ‖(p : K)‖ < 1) (n : ℕ) :
    ‖(n.factorial : K)‖ = ‖(p : K)‖ ^ padicValNat p n.factorial := by
  have hdecomp : p ^ padicValNat p n.factorial * n.factorial.divMaxPow p = n.factorial :=
    Nat.pow_padicValNat_mul_divMaxPow p n.factorial
  have hcopr : ¬p ∣ n.factorial.divMaxPow p :=
    Nat.not_dvd_divMaxPow hp.out.one_lt (Nat.factorial_ne_zero n)
  have hone : ‖((n.factorial.divMaxPow p : ℕ) : K)‖ = 1 :=
    norm_natCast_eq_one_of_not_dvd hnorm hcopr
  calc ‖(n.factorial : K)‖
      = ‖((p ^ padicValNat p n.factorial * n.factorial.divMaxPow p : ℕ) : K)‖ := by rw [hdecomp]
    _ = ‖(p : K)‖ ^ padicValNat p n.factorial * ‖((n.factorial.divMaxPow p : ℕ) : K)‖ := by
        push_cast; rw [norm_mul, norm_pow]
    _ = ‖(p : K)‖ ^ padicValNat p n.factorial := by rw [hone, mul_one]

/-- **Legendre's theorem, as a real inequality.** `padicValNat p n ! ≤ n / (p - 1)`, from Mathlib's
exact formula `(p - 1) * padicValNat p n ! = n - digitsum` (`sub_one_mul_padicValNat_factorial`) —
the digit-sum subtraction is simply dropped (`Nat.sub_le`), giving the (non-sharp, but sufficient)
bound needed for convergence. -/
theorem padicValNat_factorial_le_div (n : ℕ) :
    (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
  have hle : (p - 1) * padicValNat p n.factorial ≤ n := by
    rw [sub_one_mul_padicValNat_factorial]; exact Nat.sub_le _ _
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hpr : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    linarith
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp1]; norm_num
  have hrle : ((p - 1 : ℕ) : ℝ) * (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
  rw [hcast] at hrle
  rw [le_div_iff₀ hpr]
  linarith [hrle]

/-- **The per-term geometric bound on the exponential series.** For `x : K`,
`‖x ^ n / n !‖ ≤ (‖x‖ / ‖p‖ ^ (1/(p-1))) ^ n`. -/
theorem norm_pow_div_factorial_le (hnorm : ‖(p : K)‖ < 1) (x : K) (n : ℕ) :
    ‖x ^ n / (n.factorial : K)‖ ≤ (‖x‖ / ‖(p : K)‖ ^ (((p : ℝ) - 1)⁻¹)) ^ n := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  have hfact : ‖(n.factorial : K)‖ = ‖(p : K)‖ ^ padicValNat p n.factorial := norm_factorial_eq hnorm n
  have hval_le : (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) :=
    padicValNat_factorial_le_div n
  have hrpow_le :
      ‖(p : K)‖ ^ ((n : ℝ) / ((p : ℝ) - 1)) ≤ ‖(p : K)‖ ^ (padicValNat p n.factorial : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hp0 hnorm.le hval_le
  have hrpow_pos : (0 : ℝ) < ‖(p : K)‖ ^ ((n : ℝ) / ((p : ℝ) - 1)) := Real.rpow_pos_of_pos hp0 _
  have hcast : ‖(p : K)‖ ^ (padicValNat p n.factorial : ℝ) = ‖(p : K)‖ ^ padicValNat p n.factorial :=
    Real.rpow_natCast _ _
  rw [norm_div, norm_pow, hfact]
  have hstep : ‖x‖ ^ n / ‖(p : K)‖ ^ padicValNat p n.factorial ≤
      ‖x‖ ^ n / ‖(p : K)‖ ^ ((n : ℝ) / ((p : ℝ) - 1)) :=
    div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg x) n) hrpow_pos (hcast ▸ hrpow_le)
  refine hstep.trans_eq ?_
  rw [div_pow, ← Real.rpow_natCast (‖(p : K)‖ ^ (((p : ℝ) - 1)⁻¹)) n, ← Real.rpow_mul hp0.le]
  congr 2
  field_simp

/-- **The convergence radius**, `‖p‖ ^ (1/(p-1))`: `exp` converges exactly for `‖x‖` strictly below
this. In additive valuation terms (`v(π) = 1`), this is the classical threshold `v(x) > v(p)/(p-1)`.
-/
def convergenceRadius (K : Type*) [NormedField K] (p : ℕ) : ℝ := ‖(p : K)‖ ^ (((p : ℝ) - 1)⁻¹)

/-- **The partial sums of the exponential series form a Cauchy sequence**, for `x` inside the
convergence radius. Consecutive partial sums differ by the `(n+1)`-st term, of norm
`≤ r ^ (n + 1) = r · r ^ n` for `r := ‖x‖ / ‖p‖ ^ (1/(p-1)) < 1` (`norm_pow_div_factorial_le`); this
is exactly the shape `cauchySeq_of_le_geometric` needs. -/
theorem cauchySeq_partialSum (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < convergenceRadius K p) :
    CauchySeq (fun n => ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : K)) := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  set r := ‖x‖ / ‖(p : K)‖ ^ (((p : ℝ) - 1)⁻¹) with hrdef
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg x) (Real.rpow_nonneg (norm_nonneg _) _)
  have hr1 : r < 1 := by
    rw [hrdef, div_lt_one (Real.rpow_pos_of_pos hp0 _)]
    exact hx
  refine cauchySeq_of_le_geometric r r hr1 (fun n => ?_)
  rw [dist_comm, dist_eq_norm, Finset.sum_range_succ, add_sub_cancel_left]
  calc ‖x ^ (n + 1) / ((n + 1).factorial : K)‖ ≤ r ^ (n + 1) := norm_pow_div_factorial_le hnorm x (n + 1)
    _ = r * r ^ n := pow_succ' r n

variable [CompleteSpace K]

/-- **The nonarchimedean exponential.** Defined as the limit of the partial sums of `Σ x^n/n!`
where that sequence is Cauchy (`cauchySeq_partialSum`, using `[CompleteSpace K]`), and `0`
elsewhere. Convergence, not the group-homomorphism law or compatibility with a logarithm, is all
that is proved about it in this file (see the module docstring's "What remains" list). -/
def exp (hnorm : ‖(p : K)‖ < 1) (x : K) : K :=
  if hx : ‖x‖ < convergenceRadius K p then
    (cauchySeq_tendsto_of_complete (cauchySeq_partialSum hnorm hx)).choose
  else 0

/-- The defining property of `exp`: the partial sums of the series actually tend to it, on the
convergence domain. -/
theorem tendsto_partialSum_exp (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < convergenceRadius K p) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : K)) atTop
      (nhds (exp hnorm x)) := by
  unfold exp
  rw [dif_pos hx]
  exact (cauchySeq_tendsto_of_complete (cauchySeq_partialSum hnorm hx)).choose_spec

end NonarchimedeanExponential

end
