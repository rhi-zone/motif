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

This is step 1 (and, for the logarithm's convergence, step 2) of a from-scratch construction of the
classical fix for the wild-ramification gap in this repo's totally-ramified norm-group thread
(`Langlands.TotallyRamifiedTrace`, `Langlands.TotallyRamifiedNormSurjective`): in the wild case
(`char 𝓀[K] ∣ e`), the tame case's key computation — the norm induces multiplication-by-`e` on the
residue-graded pieces of the principal-units filtration — degenerates to the zero map at every
filtration level, so no variant of the tame argument closes the wild case. The classical replacement
(Serre) is that, above the ramification break, a `p`-adic exponential/logarithm gives an isomorphism
`U_L^{(i)} ≅ (𝔪_L^i, +)`, turning the norm computation additive instead of multiplicative-residue.
This file builds the exponential map and the logarithm, each with its own from-scratch convergence
proof; it does **not** attempt the mutual-inverse relationship between them, the translation to a
specific principal-units subgroup `U_L^{(i)}` of a `HeightOneSpectrum`-style
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
7. `log`, by the same route: `norm_natCast_eq` generalizes step 2 from `n!` to any nonzero `n`
   (needed since the logarithm's denominators are `n`, not `n!`); `padicValNat_lt_self_of_ne_zero`
   is a crude (non-sharp) substitute for step 3's Legendre bound, giving the per-term geometric bound
   `norm_pow_div_natCast_le` at the more conservative radius `logConvergenceRadius K p := ‖p‖` (see
   `log`'s section docstring for why the sharp classical radius `‖x‖ < 1` is not reached: it needs a
   genuinely different polynomial-vs-geometric comparison argument, not attempted); the rest
   (`cauchySeq_partialSum_log`, `log`) mirrors steps 5–6 exactly.

## What remains

Not attempted in this file, and not small:

* **The mutual-inverse relationship between `exp` and `log`** (`exp (log (1+x)) = 1+x` and
  `log (1 + (exp x - 1)) = x` on matched domains) — needed to actually turn `U_L^{(i)}` into
  `(𝔪_L^i, +)`, not just to produce two independently convergent maps into `L`. Genuinely attempted
  this pass (not merely deferred): Mathlib's `Mathlib.RingTheory.PowerSeries.Exp` and
  `.Log` provide *formal* power series `PowerSeries.exp`/`PowerSeries.log` over any `Algebra ℚ A`
  (available here since `CharZero K` gives `K` a canonical `ℚ`-algebra structure) with `order_exp`,
  `deriv_log`, etc., but as of the version vendored in this repo's `.lake/packages/mathlib` there is
  no `exp_log`/`log_exp`-style formal mutual-inverse identity for them (`Log.lean` has only order and
  derivative facts) — so there is no ready-made formal statement to transport to the convergent case
  even setting aside the (substantial, itself unattempted) formal-to-convergent bridging argument
  that would be needed regardless (matching coefficients between `PowerSeries.exp`/`log`'s indexing
  and this file's, and justifying that termwise convergence commutes with formal substitution).
* **Translating the abstract thresholds `‖x‖ < ‖p‖^(1/(p-1))` (`exp`) and `‖x‖ < ‖p‖` (`log`) into
  concrete filtration levels** of `w.adicCompletionIntegers L`'s principal units
  (`ValuationSubring.principalUnitsPow`, this repo's `Langlands.PrincipalUnitsFiltrationAdicCompletion`)
  — i.e. relating `‖x‖ < r` to `x ∈ 𝔪_L^i` for a specific `i`, and showing `exp` actually maps into
  the corresponding principal-units level, not just converges. The convergence-domain translation is
  in `Langlands.NonarchimedeanExponentialFiltration`; the landing statement itself (`exp` maps `𝔪_A^i`
  into `U_A^{(i)}`, at the abstract `ValuationSubring` level, not yet the concrete
  `HeightOneSpectrum` one) is now closed in
  `Langlands.NonarchimedeanExponentialUnitsFiltration.exp_mem_principalUnitsPow`. `log`'s analogue is
  not attempted.
* **The norm/trace compatibility** `N_{L/K}(exp x) = exp(Tr_{L/K}(x))` (or whatever the precise
  mechanism is) that would let this replace the tame case's residue-multiplication argument in the
  wild-ramification norm-group computation. This is the actual payoff and is not attempted here.
* Group-homomorphism properties of `exp`/`log` themselves (`exp(x+y) = exp x * exp y`,
  `log(xy) = log x + log y` on suitable domains) are not proved — only convergence (existence of the
  limit) is.

This file closes only the convergence-theory foundation for both series (Serre, *Local Fields*
Ch. II §2's estimate for `exp`, generalized past `ℚ_p`, plus the analogous but non-sharp estimate for
`log`); the wild case of the totally-ramified norm-group index theorem is not closed by this file
alone.
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

/-!
## The logarithm

`log(1+x) = Σ_{n≥1} (-1)^{n+1} x^n/n`, built by the same route as `exp` above: a per-term geometric
bound, feeding `cauchySeq_of_le_geometric`, feeding `cauchySeq_tendsto_of_complete`. The series is
indexed here as `∑ k ∈ range n, (-1)^k * x^(k+1)/(k+1)` (`k = n - 1` in the classical `n`-indexing),
so that the `k`-th summand's exponent (`k+1`) matches the classical term index directly.

**Convergence radius.** The classical sharp radius is `‖x‖ < 1` (`v(x) > 0`), strictly larger than
`exp`'s — but reaching that sharp radius honestly needs a genuinely different (polynomial-vs-geometric
comparison) argument, because `padicValNat p n` grows only like `log_p n`, not linearly, so the crude
bound `padicValNat p n < n` used below is very far from sharp. Rather than build that comparison
argument, this file uses the same `cauchySeq_of_le_geometric` technique as `exp`, at the more
conservative threshold `‖x‖ < ‖p‖` (`logConvergenceRadius`) — narrower than the classical radius but
still enough to be a genuine, honestly-proved convergence result, and (since `‖p‖ ≤ ‖p‖^(1/(p-1))` for
`p ≥ 2`) narrower than `exp`'s domain too, so `exp` and `log` share this common domain. -/

omit [CharZero K] [CompleteSpace K] in
/-- **An arbitrary nonzero natural number's norm is exactly `‖p‖` to the power of its `p`-adic
valuation** — the same fact as `norm_factorial_eq`, generalized from `n!` to any nonzero `n` (needed
here since the logarithm series' denominators are `n`, not `n!`). Same proof: split off the
`p`-coprime part via `Nat.pow_padicValNat_mul_divMaxPow`/`Nat.not_dvd_divMaxPow` and apply
`norm_natCast_eq_one_of_not_dvd`. -/
theorem norm_natCast_eq (hnorm : ‖(p : K)‖ < 1) {n : ℕ} (hn : n ≠ 0) :
    ‖(n : K)‖ = ‖(p : K)‖ ^ padicValNat p n := by
  have hdecomp : p ^ padicValNat p n * n.divMaxPow p = n := Nat.pow_padicValNat_mul_divMaxPow p n
  have hcopr : ¬p ∣ n.divMaxPow p := Nat.not_dvd_divMaxPow hp.out.one_lt hn
  have hone : ‖((n.divMaxPow p : ℕ) : K)‖ = 1 := norm_natCast_eq_one_of_not_dvd hnorm hcopr
  calc ‖(n : K)‖
      = ‖((p ^ padicValNat p n * n.divMaxPow p : ℕ) : K)‖ := by rw [hdecomp]
    _ = ‖(p : K)‖ ^ padicValNat p n * ‖((n.divMaxPow p : ℕ) : K)‖ := by
        push_cast; rw [norm_mul, norm_pow]
    _ = ‖(p : K)‖ ^ padicValNat p n := by rw [hone, mul_one]

/-- `padicValNat p n < n` for `n ≠ 0` (using `p ≥ 2`): `p ^ padicValNat p n ∣ n` gives
`p ^ padicValNat p n ≤ n` (`Nat.le_of_dvd`), and `padicValNat p n < p ^ padicValNat p n` since
`p > 1` (`Nat.lt_pow_self`). A crude (non-sharp) bound, but enough for a literal geometric bound on
the logarithm series' terms. -/
theorem padicValNat_lt_self_of_ne_zero {n : ℕ} (hn : n ≠ 0) : padicValNat p n < n :=
  lt_of_lt_of_le (Nat.lt_pow_self hp.out.one_lt)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd)

omit [CompleteSpace K] in
/-- **The per-term bound on the logarithm series.** For `x : K` and `n ≠ 0`,
`‖x ^ n / n‖ ≤ (‖x‖ / ‖p‖) ^ n`. -/
theorem norm_pow_div_natCast_le (hnorm : ‖(p : K)‖ < 1) (x : K) {n : ℕ} (hn : n ≠ 0) :
    ‖x ^ n / (n : K)‖ ≤ (‖x‖ / ‖(p : K)‖) ^ n := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  have hpn0 : (0 : ℝ) < ‖(p : K)‖ ^ n := pow_pos hp0 n
  have hnle : ‖(p : K)‖ ^ n ≤ ‖(n : K)‖ := by
    rw [norm_natCast_eq hnorm hn]
    exact pow_le_pow_of_le_one hp0.le hnorm.le (padicValNat_lt_self_of_ne_zero hn).le
  rw [norm_div, norm_pow, div_pow]
  exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg x) n) hpn0 hnle

/-- **The logarithm's convergence radius**, `‖p‖`. Strictly more conservative than the classical
sharp radius `1` — see the section docstring above for why. -/
def logConvergenceRadius (K : Type*) [NormedField K] (p : ℕ) : ℝ := ‖(p : K)‖

omit [CompleteSpace K] in
/-- **The partial sums of the logarithm series form a Cauchy sequence**, for `x` inside
`logConvergenceRadius`. Consecutive partial sums (`∑ k ∈ range n, …` vs `∑ k ∈ range (n+1), …`)
differ by the `n`-th summand, `(-1)^n * x^(n+1)/(n+1)`, of norm `≤ r^(n+1) = r · r^n` for
`r := ‖x‖ / ‖p‖ < 1` (`norm_pow_div_natCast_le`) — the same `cauchySeq_of_le_geometric` shape as
`cauchySeq_partialSum`. -/
theorem cauchySeq_partialSum_log (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < logConvergenceRadius K p) :
    CauchySeq (fun n => ∑ k ∈ Finset.range n, (-1 : K) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K)) := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  set r := ‖x‖ / ‖(p : K)‖ with hrdef
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg x) hp0.le
  have hr1 : r < 1 := by
    rw [hrdef, div_lt_one hp0]
    exact hx
  refine cauchySeq_of_le_geometric r r hr1 (fun n => ?_)
  rw [dist_comm, dist_eq_norm, Finset.sum_range_succ, add_sub_cancel_left]
  have hneg1 : ‖(-1 : K) ^ n‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
  calc ‖(-1 : K) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K)‖ ≤ r ^ (n + 1) := by
        rw [norm_div, norm_mul, hneg1, one_mul, ← norm_div]
        exact norm_pow_div_natCast_le hnorm x n.succ_ne_zero
    _ = r * r ^ n := pow_succ' r n

/-- **The nonarchimedean logarithm.** Defined as the limit of the partial sums of
`Σ (-1)^k x^(k+1)/(k+1)` where that sequence is Cauchy (`cauchySeq_partialSum_log`, using
`[CompleteSpace K]`), and `0` elsewhere. Only convergence is proved about it in this file — see the
module docstring's "What remains" list for the mutual-inverse relationship with `exp`, not attempted
here. -/
def log (hnorm : ‖(p : K)‖ < 1) (x : K) : K :=
  if hx : ‖x‖ < logConvergenceRadius K p then
    (cauchySeq_tendsto_of_complete (cauchySeq_partialSum_log hnorm hx)).choose
  else 0

/-- The defining property of `log`: the partial sums of the series actually tend to it, on the
convergence domain. -/
theorem tendsto_partialSum_log (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < logConvergenceRadius K p) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (-1 : K) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K)) atTop
      (nhds (log hnorm x)) := by
  unfold log
  rw [dif_pos hx]
  exact (cauchySeq_tendsto_of_complete (cauchySeq_partialSum_log hnorm hx)).choose_spec

end NonarchimedeanExponential

end
