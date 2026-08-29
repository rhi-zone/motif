import Mathlib.RingTheory.FormalGroup.Basic
import Langlands.LubinTateFunctionalEquationBivariate

/-!
# The formal inverse of a formal group law

Mathlib's `FormalGroup R` (`Mathlib/RingTheory/FormalGroup/Basic.lean`) axiomatizes a
one-dimensional formal group law `F(X, Y) ∈ R⟦X, Y⟧` with `F ≡ X + Y (mod deg 2)` and
associativity, and builds `AddMonoid`/`AddCommMonoid` on `F.Point σ`. It has **no** formal
inverse series and no `Neg`/`AddGroup` instance anywhere. This file builds the missing piece: for any `F : FormalGroup R` over any
commutative ring `R`, a unique `i_F ∈ R⟦X⟧` with `i_F ≡ -X (mod deg 2)` and `F(X, i_F(X)) = 0`.

## Why this is simpler than `PhiState`

`LubinTateFunctionalEquationBivariate.lean`'s `PhiState` construction solves, at each recursive
step, a linear equation whose coefficient is `π * (1 - π^(d+1))` — a unit only because `π` is a
uniformizer (`1 - π^(d+1)` a unit since `π ∈ 𝔪`), which is why that file needs `O` to be a
complete/Henselian-style discrete valuation ring. Here, the analogous coefficient is `F`'s own
`lin_coeff_Y`, which the `FormalGroup` structure fixes to be **exactly `1`** — a unit in every
commutative ring, no divisibility or completeness argument needed. Confirmed by construction
below: `invFun` needs no `Invertible`/`IsUnit` hypothesis at all, unlike even Mathlib's own
`PowerSeries.substInv` (which needs `Invertible (P.coeff 1)`).

## Main definitions/theorems

* `FormalGroup.subst2 F A` : `F(X, A(X))`, substituting `A` for `Y` and leaving `X` fixed.
* `FormalGroup.coeff_subst2_eq_of_dvd_sub` : truncation invariance in the `Y`-slot.
* `FormalGroup.coeff_subst2_add_C_mul_X_pow` : the linear-correction identity that makes the
  recursion solvable, reusing `LubinTate.coeff_pow_add_C_mul_X_pow_sub_coeff_pow` (Fact 2' of the
  univariate functional-equation file) unchanged.
* `FormalGroup.invFun`, `FormalGroup.inv` : the recursive coefficient-by-coefficient construction
  of the formal inverse series, and the assembled series itself.
* `FormalGroup.subst2_inv_eq_zero` : **existence**, `F(X, inv F) = 0`.
* `FormalGroup.eq_inv_of_subst2_eq_zero` : **uniqueness**, any series with zero constant term,
  linear coefficient `-1`, and `F(X, ·) = 0` equals `inv F`.
-/

@[expose] public section

noncomputable section

open PowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

/-- **`F(X, A(X))`**: substitute `A` for the second variable of `F`, leaving the first as `X`.
The `Y`-slot analogue of Mathlib's `F.Xzero`/`F.zeroX` (`subst ![X, 0]`/`subst ![0, X]`), with `A`
a free parameter instead of `0`. -/
def subst2 (A : PowerSeries R) : PowerSeries R :=
  MvPowerSeries.subst ![PowerSeries.X, A] F.toPowerSeries

theorem subst2_zero : F.subst2 0 = F.Xzero := rfl

/-- The family `![X, A]` is admissible whenever `A` has zero constant term. -/
theorem hasSubst_subst2 {A : PowerSeries R} (hA : constantCoeff A = 0) :
    MvPowerSeries.HasSubst (![PowerSeries.X, A] : Fin 2 → MvPowerSeries Unit R) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i
    · exact PowerSeries.constantCoeff_X
    · simpa

/-- Every `d.prod` term in the `MvPowerSeries.coeff_subst` expansion of `subst2 F A` collapses to
`X ^ (d 0) * A ^ (d 1)`. -/
theorem prod_family_subst2 (A : PowerSeries R) (d : Fin 2 →₀ ℕ) :
    (d.prod fun s j ↦ (![PowerSeries.X, A] : Fin 2 → MvPowerSeries Unit R) s ^ j) =
      (PowerSeries.X : R⟦X⟧) ^ d 0 * A ^ d 1 := by
  rw [Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _), Fin.prod_univ_two]
  simp

/-- **Truncation invariance in the `Y`-slot.** If `A`, `A'` agree in coefficients `0, …, n`
(packaged as `X ^ (n + 1) ∣ (A - A')`), substituting either for `Y` gives the same `n`-th
coefficient of `F(X, ·)`. Proved the same way as `LubinTate.coeff_subst_eq_of_dvd_sub`: expand via
`MvPowerSeries.coeff_subst` into a `finsum` over `Fin 2 →₀ ℕ`, and note that `X ^ (n + 1) ∣
(A - A')` propagates to `X ^ (n + 1) ∣ (A ^ (d 1) - A' ^ (d 1))` via `sub_dvd_pow_sub_pow`, which
forces `coeff n (X ^ (d 0) * A ^ (d 1)) = coeff n (X ^ (d 0) * A' ^ (d 1))` via `X_pow_dvd_iff`. -/
theorem coeff_subst2_eq_of_dvd_sub {A A' : PowerSeries R} (hA : constantCoeff A = 0)
    (hA' : constantCoeff A' = 0) (n : ℕ) (hdvd : (PowerSeries.X : R⟦X⟧) ^ (n + 1) ∣ (A - A')) :
    coeff n (F.subst2 A) = coeff n (F.subst2 A') := by
  have ha := hasSubst_subst2 hA
  have ha' := hasSubst_subst2 hA'
  rw [PowerSeries.coeff, subst2, subst2, MvPowerSeries.coeff_subst ha,
    MvPowerSeries.coeff_subst ha']
  simp only [coeff_coeToMvPowerSeries]
  refine finsum_congr fun d ↦ ?_
  congr 1
  rw [prod_family_subst2, prod_family_subst2, coeff_X_pow_mul', coeff_X_pow_mul']
  by_cases hd0 : d 0 ≤ n
  · rw [if_pos hd0, if_pos hd0]
    have hpow : (PowerSeries.X : R⟦X⟧) ^ (n + 1) ∣ (A ^ d 1 - A' ^ d 1) :=
      hdvd.trans (sub_dvd_pow_sub_pow A A' (d 1))
    have hzero : coeff (n - d 0) (A ^ d 1 - A' ^ d 1) = 0 :=
      (X_pow_dvd_iff.mp hpow) (n - d 0) (by omega)
    rwa [map_sub, sub_eq_zero] at hzero
  · rw [if_neg hd0, if_neg hd0]

/-- **The linear-correction identity.** For `A` with zero constant term, `c : R`, and `m ≥ 1`:
correcting `A` by `C c * X ^ m` shifts `coeff m (F(X, ·))` by exactly `c`. Splits the
`MvPowerSeries.coeff_subst` sum over `d : Fin 2 →₀ ℕ` by `d 0`: for `d 0 ≥ 1` the evaluation
position `m - d 0 < m`, so `X ^ m ∣ (C c * X ^ m)` already forces no change there
(`coeff_subst2_eq_of_dvd_sub`'s per-power argument, extracted inline); for `d 0 = 0` the evaluation
position is exactly `m`, where `LubinTate.coeff_pow_add_C_mul_X_pow_sub_coeff_pow` (Fact 2' of the
univariate functional-equation file, fully general over any `CommRing`, reused unchanged) applies
directly, and only `d 1 = 1` (i.e. `d = single 1 1`, whose `F`-coefficient is `lin_coeff_Y = 1`)
survives. -/
theorem coeff_subst2_add_C_mul_X_pow {A : PowerSeries R} (hA0 : constantCoeff A = 0) (c : R)
    {m : ℕ} (hm : 1 ≤ m) :
    coeff m (F.subst2 (A + PowerSeries.C c * PowerSeries.X ^ m)) =
      coeff m (F.subst2 A) + c := by
  have hwc : constantCoeff (PowerSeries.C c * PowerSeries.X ^ m : R⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  have hAc0 : constantCoeff (A + PowerSeries.C c * PowerSeries.X ^ m) = 0 := by
    rw [map_add, hA0, hwc, _root_.zero_add]
  have ha := hasSubst_subst2 hA0
  have hac := hasSubst_subst2 hAc0
  have hstep : ∀ d : Fin 2 →₀ ℕ,
      coeff m (d.prod fun s j ↦ (![PowerSeries.X, A + PowerSeries.C c * PowerSeries.X ^ m] :
          Fin 2 → MvPowerSeries Unit R) s ^ j) =
        coeff m (d.prod fun s j ↦ (![PowerSeries.X, A] :
            Fin 2 → MvPowerSeries Unit R) s ^ j) +
          (if d = Finsupp.single 1 1 then c else 0) := by
    intro d
    rw [prod_family_subst2, prod_family_subst2]
    by_cases hd0 : d 0 = 0
    · have hcoeffpow := LubinTate.coeff_pow_add_C_mul_X_pow_sub_coeff_pow hA0 c hm (d 1)
      rw [hd0, pow_zero, one_mul, one_mul, hcoeffpow]
      by_cases hd1 : d 1 = 1
      · have hde : d = Finsupp.single 1 1 := by
          ext i; fin_cases i <;> simp [hd0, hd1]
        rw [if_pos hd1, if_pos hde]
      · have hde : d ≠ Finsupp.single 1 1 := by
          intro hc; apply hd1; rw [hc]; simp
        rw [if_neg hd1, if_neg hde]
    · have hde : d ≠ Finsupp.single 1 1 := by
        intro hc; apply hd0; rw [hc]; simp
      rw [if_neg hde, _root_.add_zero]
      have hpow : (PowerSeries.X : R⟦X⟧) ^ m ∣
          ((A + PowerSeries.C c * PowerSeries.X ^ m) ^ d 1 - A ^ d 1) :=
        (show (PowerSeries.X : R⟦X⟧) ^ m ∣
            (A + PowerSeries.C c * PowerSeries.X ^ m - A) from by
          rw [add_sub_cancel_left]; exact dvd_mul_left _ _).trans
          (sub_dvd_pow_sub_pow (A + PowerSeries.C c * PowerSeries.X ^ m) A (d 1))
      have hlt : m - d 0 < m := by omega
      have hzero : coeff (m - d 0) ((A + PowerSeries.C c * PowerSeries.X ^ m) ^ d 1 - A ^ d 1)
          = 0 := (X_pow_dvd_iff.mp hpow) (m - d 0) hlt
      rw [map_sub, sub_eq_zero] at hzero
      rw [coeff_X_pow_mul', coeff_X_pow_mul', hzero]
  have hfin1 : Function.HasFiniteSupport (fun d : Fin 2 →₀ ℕ ↦ MvPowerSeries.coeff d F.toPowerSeries •
      coeff m (d.prod fun s j ↦ (![PowerSeries.X, A] : Fin 2 → MvPowerSeries Unit R) s ^ j)) := by
    have := MvPowerSeries.coeff_subst_finite ha F.toPowerSeries (Finsupp.single () m)
    simpa only [coeff_coeToMvPowerSeries] using this
  have hfin2 : Function.HasFiniteSupport (fun d : Fin 2 →₀ ℕ ↦ MvPowerSeries.coeff d F.toPowerSeries •
      (if d = Finsupp.single 1 1 then (c : R) else 0)) :=
    .subset (Set.finite_singleton (Finsupp.single 1 1)) (fun d hd ↦ by
      by_contra hd1
      exact hd (by simp [show d ≠ Finsupp.single 1 1 from hd1]))
  rw [PowerSeries.coeff, subst2, subst2, MvPowerSeries.coeff_subst hac, MvPowerSeries.coeff_subst ha]
  simp only [coeff_coeToMvPowerSeries]
  calc finsum (fun d ↦ MvPowerSeries.coeff d F.toPowerSeries •
        coeff m (d.prod fun s j ↦ (![PowerSeries.X, A + PowerSeries.C c * PowerSeries.X ^ m] :
          Fin 2 → MvPowerSeries Unit R) s ^ j))
      = finsum (fun d ↦ MvPowerSeries.coeff d F.toPowerSeries •
          (coeff m (d.prod fun s j ↦ (![PowerSeries.X, A] :
              Fin 2 → MvPowerSeries Unit R) s ^ j)
            + (if d = Finsupp.single 1 1 then c else 0))) :=
        finsum_congr fun d ↦ by rw [hstep d]
    _ = finsum (fun d ↦ MvPowerSeries.coeff d F.toPowerSeries •
          coeff m (d.prod fun s j ↦ (![PowerSeries.X, A] :
            Fin 2 → MvPowerSeries Unit R) s ^ j)) +
        finsum (fun d ↦ MvPowerSeries.coeff d F.toPowerSeries •
          (if d = Finsupp.single 1 1 then (c : R) else 0)) := by
        simp_rw [smul_add]
        exact finsum_add_distrib hfin1 hfin2
    _ = finsum (fun d ↦ MvPowerSeries.coeff d F.toPowerSeries •
          coeff m (d.prod fun s j ↦ (![PowerSeries.X, A] :
            Fin 2 → MvPowerSeries Unit R) s ^ j)) + c := by
        congr 1
        rw [finsum_eq_single _ (Finsupp.single 1 1)]
        · simp [F.lin_coeff_Y]
        · intro d hd; rw [if_neg hd, smul_zero]

/-- **The coefficient-by-coefficient recursion**: `invFun F 0 = 0`, and for `n ≥ 1`, `invFun F n`
is forced to be the negative of the `n`-th coefficient of `F(X, ·)` evaluated at the partial sum
of the coefficients already fixed. Unlike Mathlib's `PowerSeries.substInvFun` (the model this is
patterned on), no `Invertible`/unit-inversion factor appears: `F`'s `lin_coeff_Y = 1` makes the
coefficient of the new unknown exactly `1` in *every* commutative ring, so a bare negation
suffices (see the module docstring). -/
noncomputable def invFun (F : FormalGroup R) : ℕ → R
  | 0 => 0
  | n + 1 => - coeff (n + 1) (F.subst2 (∑ i : Fin (n + 1),
      PowerSeries.C (invFun F i.1) * PowerSeries.X ^ i.1))

@[simp] theorem invFun_zero : invFun F 0 = 0 := by simp [invFun]

theorem invFun_succ (n : ℕ) :
    invFun F (n + 1) = - coeff (n + 1) (F.subst2 (∑ i : Fin (n + 1),
      PowerSeries.C (invFun F i.1) * PowerSeries.X ^ i.1)) := by
  simp [invFun]

/-- The partial sum of `invFun F` through degree `n`. -/
noncomputable def invPartialSum (n : ℕ) : PowerSeries R :=
  ∑ i : Fin (n + 1), PowerSeries.C (invFun F i.1) * PowerSeries.X ^ i.1

theorem invFun_succ' (n : ℕ) :
    invFun F (n + 1) = - coeff (n + 1) (F.subst2 (invPartialSum F n)) := invFun_succ F n

theorem invPartialSum_succ (n : ℕ) :
    invPartialSum F (n + 1) =
      invPartialSum F n + PowerSeries.C (invFun F (n + 1)) * PowerSeries.X ^ (n + 1) := by
  rw [invPartialSum, invPartialSum, Fin.sum_univ_castSucc]
  simp

theorem constantCoeff_invPartialSum (n : ℕ) : constantCoeff (invPartialSum F n) = 0 := by
  rw [invPartialSum, map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rcases eq_or_ne i.1 0 with hi | hi
  · rw [← coeff_zero_eq_constantCoeff, coeff_C_mul, coeff_X_pow, if_pos hi.symm, mul_one, hi,
      invFun_zero]
  · rw [← coeff_zero_eq_constantCoeff, coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hi), mul_zero]

theorem coeff_invPartialSum_of_le {n k : ℕ} (hk : k ≤ n) :
    coeff k (invPartialSum F n) = invFun F k := by
  rw [invPartialSum, map_sum, Finset.sum_eq_single (⟨k, by omega⟩ : Fin (n + 1))]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro i _ hik
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h ↦ hik (Fin.ext h.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The formal inverse series**: `inv F ≡ -X (mod deg 2)` and `F(X, inv F) = 0`
(`subst2_inv_eq_zero`), assembled from `invFun F`. -/
noncomputable def inv : PowerSeries R := PowerSeries.mk (invFun F)

@[simp] theorem constantCoeff_inv : constantCoeff (inv F) = 0 := by
  rw [inv, ← coeff_zero_eq_constantCoeff, PowerSeries.coeff_mk, invFun_zero]

theorem invFun_one : invFun F 1 = -1 := by
  rw [invFun_succ']
  have h0 : invPartialSum F 0 = 0 := by rw [invPartialSum]; simp
  rw [h0, subst2_zero, coeff_one_Xzero]

/-- **`inv F ≡ -X (mod deg 2)`**: the linear coefficient of the formal inverse is `-1`. -/
@[simp] theorem coeff_one_inv : coeff 1 (inv F) = -1 := by
  rw [inv, PowerSeries.coeff_mk, invFun_one]

/-- **The recursion is self-consistent**: substituting the partial sum through degree `n` into
`F(X, ·)` always vanishes at coefficient `n`, by construction. -/
theorem coeff_subst2_invPartialSum (n : ℕ) : coeff n (F.subst2 (invPartialSum F n)) = 0 := by
  induction n with
  | zero =>
      have h0 : invPartialSum F 0 = 0 := by
        rw [invPartialSum]; simp
      rw [h0, subst2_zero, coeff_zero_eq_constantCoeff, F.constantCoeff_Xzero]
  | succ n _ =>
      rw [invPartialSum_succ,
        coeff_subst2_add_C_mul_X_pow F (constantCoeff_invPartialSum F n) (invFun F (n + 1))
          (by omega),
        invFun_succ']
      ring

/-- **Existence**: `F(X, inv F) = 0`. -/
theorem subst2_inv_eq_zero : F.subst2 (inv F) = 0 := by
  ext n
  have hdvd : (PowerSeries.X : R⟦X⟧) ^ (n + 1) ∣ (inv F - invPartialSum F n) := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [map_sub, sub_eq_zero, inv, PowerSeries.coeff_mk]
    exact (coeff_invPartialSum_of_le F (by omega)).symm
  rw [coeff_subst2_eq_of_dvd_sub F (constantCoeff_inv F) (constantCoeff_invPartialSum F n) n hdvd,
    coeff_subst2_invPartialSum F n, map_zero]

/-- `invPartialSum F n` has no coefficient past degree `n`: it is a sum of monomials of degree
`0, …, n` only. -/
theorem coeff_invPartialSum_of_gt {n k : ℕ} (hk : n < k) : coeff k (invPartialSum F n) = 0 := by
  rw [invPartialSum, map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

/-- **Uniqueness**: any power series with zero constant term solving `F(X, ·) = 0` equals
`inv F`. In particular no separate "linear coefficient `-1`" hypothesis is needed — it, and every
other coefficient, is already forced by `constantCoeff G = 0` and `F.subst2 G = 0` alone, via the
same coefficient-by-coefficient recursion `invFun` follows. -/
theorem eq_inv_of_subst2_eq_zero {G : PowerSeries R} (hG0 : constantCoeff G = 0)
    (hG : F.subst2 G = 0) : G = inv F := by
  have hcoeff : ∀ n, coeff n G = invFun F n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      match n with
      | 0 => rw [coeff_zero_eq_constantCoeff, hG0, invFun_zero]
      | n + 1 =>
          set A' := invPartialSum F n + PowerSeries.C (coeff (n + 1) G) * PowerSeries.X ^ (n + 1)
            with hA'def
          have hA'0 : constantCoeff A' = 0 := by
            rw [hA'def, map_add, constantCoeff_invPartialSum, ← coeff_zero_eq_constantCoeff,
              coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, _root_.add_zero]
          have hdvd : (PowerSeries.X : R⟦X⟧) ^ (n + 2) ∣ (G - A') := by
            rw [X_pow_dvd_iff]
            intro d hd
            rw [map_sub, sub_eq_zero]
            rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hlt | heq
            · rw [hA'def, map_add, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero,
                _root_.add_zero, coeff_invPartialSum_of_le F (by omega), IH d hlt]
            · rw [heq, hA'def, map_add, coeff_invPartialSum_of_gt F (by omega),
                coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one, _root_.zero_add]
          have hstep := coeff_subst2_eq_of_dvd_sub F hG0 hA'0 (n + 1) hdvd
          rw [hG, map_zero] at hstep
          rw [hA'def, coeff_subst2_add_C_mul_X_pow F (constantCoeff_invPartialSum F n)
              (coeff (n + 1) G) (by omega)] at hstep
          rw [invFun_succ']
          linear_combination -hstep
  ext n
  rw [hcoeff n, inv, PowerSeries.coeff_mk]

/-! ### Towards `AddGroup`-flavored structure

Mathlib's `F.Point σ := {f : MvPowerSeries σ R // PowerSeries.HasSubst f}` (`HasSubst f ↔
IsNilpotent (constantCoeff f)`) carries only `AddCommMonoid` (`Mathlib/RingTheory/FormalGroup/
Basic.lean:337`). Retrofitting a literal `Neg (F.Point σ)`/`AddGroup (F.Point σ)` instance for
Mathlib's *full* nilpotent-constant-coefficient generality would need `subst2`/`invFun`/`inv`
rebuilt against "nilpotent" throughout in place of "literally zero" (the hypothesis every lemma
above actually uses) — a substantially larger undertaking, and out of scope here.

What *is* in scope, at the same "zero constant coefficient" generality already built: every
univariate substitutand this whole Lubin-Tate development ever manipulates (`f`, `iter f n`, and
every `A` appearing in `subst2`) has literally zero constant coefficient, never merely nilpotent.
`subst2_subst_eq_zero` below is the standalone fact that matters at that generality: composing
`inv F` with *any* such `A` produces `A`'s additive inverse under `F`, i.e. `F.Point Unit`
restricted to zero-constant-coefficient representatives already behaves like a group, even though
no Mathlib `AddGroup` instance is registered for the full `Point` type. -/

/-- **The formal inverse composes with any admissible substitutand.** Generalizes
`subst2_inv_eq_zero` (the case `A = X`) to any `A` with zero constant term: `F(A, i_F(A)) = 0`
for `i_F(A) := (inv F).subst A`. Proved by substituting `A` for `X` on both sides of
`subst2_inv_eq_zero`'s identity `F(X, inv F) = 0`, via `MvPowerSeries.subst_comp_subst_apply`
(chaining the bivariate substitution `![X, inv F]` with the further univariate substitution `A`)
and `PowerSeries.subst_def` (identifying univariate `subst` with its `Unit`-indexed multivariate
form, the same identification `subst_subst_mv` uses). -/
theorem subst2_subst_eq_zero {A : PowerSeries R} (hA0 : constantCoeff A = 0) :
    F.toPowerSeries.subst ![A, PowerSeries.subst A (F.inv)] = 0 := by
  have hs : MvPowerSeries.HasSubst (![PowerSeries.X, F.inv] : Fin 2 → MvPowerSeries Unit R) :=
    hasSubst_subst2 (constantCoeff_inv F)
  have hA : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have key := MvPowerSeries.subst_comp_subst_apply hs hA.const F.toPowerSeries
  have hfam : (fun i : Fin 2 ↦ MvPowerSeries.subst (fun _ : Unit ↦ A)
        (![PowerSeries.X, F.inv] i)) = (![A, PowerSeries.subst A (F.inv)] :
        Fin 2 → MvPowerSeries Unit R) := by
    funext i
    fin_cases i
    · show MvPowerSeries.subst (fun _ : Unit ↦ A) PowerSeries.X = A
      rw [← PowerSeries.subst_def]
      exact PowerSeries.subst_X hA
    · show MvPowerSeries.subst (fun _ : Unit ↦ A) F.inv = PowerSeries.subst A F.inv
      rw [← PowerSeries.subst_def]
  rw [hfam] at key
  rw [← key, ← subst2, subst2_inv_eq_zero, ← MvPowerSeries.coe_substAlgHom hA.const, map_zero]

end FormalGroup

/-! ### Specialization to `F_π` -/

namespace LubinTate

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O} {f : O⟦X⟧}

/-- **The formal inverse of the Lubin-Tate formal group law `F_π`.** `i_{F_π}(X) ∈ O⟦X⟧`, with
`i_{F_π} ≡ -X (mod deg 2)` (`coeff_one_PhiInv`) and `F_π(X, i_{F_π}(X)) = 0`
(`subst_Phi_PhiInv_eq_zero`), the direct specialization of `FormalGroup.inv` to
`LubinTateFormalGroup`. -/
noncomputable def PhiInv (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    O⟦X⟧ :=
  (LubinTateFormalGroup hπ hf).inv

@[simp] theorem constantCoeff_PhiInv (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) :
    PowerSeries.constantCoeff (PhiInv hπ hf) = 0 :=
  FormalGroup.constantCoeff_inv _

@[simp] theorem coeff_one_PhiInv (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    PowerSeries.coeff 1 (PhiInv hπ hf) = -1 :=
  FormalGroup.coeff_one_inv _

/-- **`i_{F_π}` is the additive inverse of `X` under `F_π`**: `F_π(X, i_{F_π}(X)) = 0`. -/
theorem subst_Phi_PhiInv_eq_zero (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    (Phi hπ hf).subst ![PowerSeries.X, PhiInv hπ hf] = 0 :=
  FormalGroup.subst2_inv_eq_zero (LubinTateFormalGroup hπ hf)

/-- **Uniqueness of `i_{F_π}`**: any power series with zero constant term solving `F_π(X, ·) = 0`
equals `PhiInv hπ hf`. -/
theorem eq_PhiInv_of_subst_Phi_eq_zero (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {G : O⟦X⟧} (hG0 : PowerSeries.constantCoeff G = 0)
    (hG : (Phi hπ hf).subst ![PowerSeries.X, G] = 0) : G = PhiInv hπ hf :=
  FormalGroup.eq_inv_of_subst2_eq_zero (LubinTateFormalGroup hπ hf) hG0 hG

/-- **`i_{F_π}` composes with any zero-constant-coefficient substitutand to give its additive
inverse under `F_π`.** In particular, applied to `A := f` or `A := iter f n`
(`Langlands/LubinTateIterate.lean`) — the only substitutands the `[π^n]`-torsion development ever
needs — this is the precise algebraic content "the `π^n`-multiplication endomorphism has an
additive-inverse-compatible formal inverse", needed for any
"group" (as opposed to commutative monoid) statement about torsion points. See the module-level
docstring of `FormalGroup.subst2_subst_eq_zero` for exactly what this does, and does not, establish
about Mathlib's `FormalGroup.Point`. -/
theorem subst_Phi_subst_PhiInv_eq_zero (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {A : O⟦X⟧} (hA0 : PowerSeries.constantCoeff A = 0) :
    (Phi hπ hf).subst ![A, PowerSeries.subst A (PhiInv hπ hf)] = 0 :=
  FormalGroup.subst2_subst_eq_zero (LubinTateFormalGroup hπ hf) hA0

end LubinTate
