import Mathlib.RingTheory.MvPowerSeries.Expand
import Langlands.LubinTateFunctionalEquation

/-!
# The Lubin-Tate functional equation lemma, 2-variable case — residue congruence only

This file begins the 2-variable generalization of `Langlands/LubinTateFunctionalEquation.lean`
scoped in `ROADMAP.md` §11/§12: building `Φ : MvPowerSeries (Fin 2) O` with `Φ ≡ X + Y (mod deg
2)` and `f.subst Φ = Φ.subst (f, f)` (i.e. `f` substituted into *each* of `Φ`'s two variables
separately), for `f ∈ ℱ_π`. Per §11's three-item breakdown of what remains after the confirmed
Mathlib building blocks, **only item 3 (the residue-field congruence) is closed here**; items 1
(the multivariate linear-correction identity) and 2 (the total-degree-indexed recursive
construction of `Φ`) are not attempted — see `ROADMAP.md`'s entry for this pass for the precise
statement of what blocks them.

## The substitution shape used here

`f, g : O⟦X⟧` remain ordinary univariate power series (as in the closed 1-variable file); the new
object is `Φ : MvPowerSeries (Fin 2) O`. Two different flavors of Mathlib's `subst` API compose to
express the functional equation `f.subst Φ = Φ.subst (f, f)`:

* **Outer position `f.subst Φ`** uses the *univariate* `PowerSeries.subst` API from
  `Mathlib.RingTheory.PowerSeries.Substitution` directly — that API is already fully general in
  its substitutand's ring (`PowerSeries.subst (a : MvPowerSeries τ S) (f : PowerSeries R) :
  MvPowerSeries τ S`), so substituting a two-variable `Φ` into a one-variable `f` needs no new
  infrastructure at all, `τ := Fin 2`, `S := O`.
* **Inner position `Φ.subst (f, f)`** needs the genuinely *multivariate*
  `MvPowerSeries.subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R)` with `σ = τ = Fin 2`,
  `a i := f.subst (MvPowerSeries.X i)` — i.e. `f` composed with the `i`-th coordinate function,
  embedding the univariate `f` into the bivariate ring at each of its two variables separately.
  This is the precise Lean shape of "`f` substituted into each of `Φ`'s two variables": not
  `Φ.subst ![f, f]` with `f` reinterpreted as a bivariate series, but `Φ.subst` applied to the
  *bivariate embeddings* of `f`.

## Main results

* `pow_residueCard_eq_subst_X_pow_mv` : the multivariate Frobenius/`q`-th-power identity, `h ^ q =
  h.subst (fun i ↦ X i ^ q)` for any `h` over the (finite) residue field — the direct `σ = Fin 2`
  instance of `MvPowerSeries.map_iterateFrobenius_expand`, reusing
  `LubinTate.iterateFrobenius_residueField_eq_id` unchanged (that fact is about `ResidueField O`
  alone, with no `σ`-dependence to redo).
* `map_residue_subst_eq_map_residue_subst_mv` : **the multivariate residue-field congruence**, the
  direct generalization of `LubinTate.map_residue_subst_eq_map_residue_subst`. For `f ∈ ℱ_π` and
  any `Φ : MvPowerSeries (Fin 2) O` with zero constant term, reducing mod `π` gives
  `map (residue O) (f.subst Φ) = map (residue O) (Φ.subst (fun i ↦ f.subst (X i)))`; both sides
  reduce to `(map (residue O) Φ) ^ q`. This closes item 3 of `ROADMAP.md` §11's three-item
  breakdown.
* `uniformizer_dvd_coeff_subst_sub_subst_mv` : the coefficient-wise consequence, `π ∣ coeff n (Φ.subst
  (fun i ↦ f.subst (X i))) - coeff n (f.subst Φ)` for every `n : Fin 2 →₀ ℕ` — the multivariate
  analogue of `LubinTate.uniformizer_dvd_coeff_subst_sub_subst`, which is exactly what a future
  total-degree-indexed recursive construction of `Φ` (item 2, not attempted here) would need at
  every step to solve its own local linear equation, the same role the univariate version plays in
  `LubinTate.phiState`.

## What this does not do

Item 1 (`ROADMAP.md` §11: a multivariate analogue of `coeff_subst_add_C_mul_X_pow` accounting for
`f`'s own higher-degree part acting on a genuinely two-variable substitutand, indexed by `σ →₀ ℕ`
rather than a single `ℕ`) and item 2 (the total-degree-indexed recursive definition of `Φ` itself,
producing a `(σ →₀ ℕ) → O` value at each step rather than a single scalar, with the same
`Finset.sum`-buried-recursive-call termination-checker hazard `LubinTate.phiState`'s docstring
flags — now with an extra index dimension) are **not attempted in this pass**. No existence or
uniqueness statement for `Φ` is proved here; only the residue-congruence solvability fact that a
future recursive construction would consume at each step.
-/

@[expose] public section

noncomputable section

open PowerSeries IsLocalRing MvPowerSeries

/-- **A multivariate power series built from its coefficient function**, the multi-index analogue
of `PowerSeries.mk`. `MvPowerSeries σ R` is definitionally `(σ →₀ ℕ) → R`, so this is the identity
map; giving it a name (and the `simp` lemma `MvPowerSeries.coeff_mk`) lets a series be specified by
a coefficient formula without appealing to that definitional unfolding at each use site, exactly as
`PowerSeries.mk`/`PowerSeries.coeff_mk` do in the univariate case. -/
def MvPowerSeries.mk {σ R : Type*} [Semiring R] (c : (σ →₀ ℕ) → R) : MvPowerSeries σ R := c

@[simp] theorem MvPowerSeries.coeff_mk {σ R : Type*} [Semiring R] (c : (σ →₀ ℕ) → R)
    (n : σ →₀ ℕ) : MvPowerSeries.coeff n (MvPowerSeries.mk c) = c n := rfl

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The Frobenius/`q`-th-power identity for multivariate power series over the residue field**,
the `σ = Fin 2` instance of the univariate `pow_residueCard_eq_subst_X_pow`: for *any* `h :
MvPowerSeries (Fin 2) (ResidueField O)`, `h ^ q = h.subst (fun i ↦ X i ^ q)` where `q = residueCard
O`. Proved the same way: `MvPowerSeries.map_iterateFrobenius_expand` together with the iterated
Frobenius being the identity on `ResidueField O` (`iterateFrobenius_residueField_eq_id`, reused
unchanged — it has no `σ`-dependence). -/
theorem pow_residueCard_eq_subst_X_pow_mv
    (h : MvPowerSeries (Fin 2) (ResidueField O)) :
    h ^ residueCard O =
      MvPowerSeries.subst (fun i ↦ (MvPowerSeries.X i : MvPowerSeries (Fin 2) (ResidueField O))
        ^ residueCard O) h := by
  have hp : (residueCharP O) ≠ 0 := (residueCharP_fact (O := O)).out.ne_zero
  have hcard : residueCard O = residueCharP O ^ (residueDegree O : ℕ) := card_residueField_eq
  rw [hcard]
  have key := MvPowerSeries.map_iterateFrobenius_expand (σ := Fin 2) (R := ResidueField O)
    (residueCharP O) hp h (residueDegree O : ℕ)
  rw [iterateFrobenius_residueField_eq_id, MvPowerSeries.map_id, RingHom.id_apply] at key
  rw [← key]
  exact MvPowerSeries.substAlgHom_apply (MvPowerSeries.HasSubst.X_pow (pow_ne_zero _ hp)) h

/-- **The multivariate residue-field congruence underlying a future 2-variable functional
equation recursion.** For `f ∈ ℱ_π` and *any* `Φ : MvPowerSeries (Fin 2) O` with zero constant
term, `f(Φ)` (outer-position univariate substitution) and `Φ(f, f)` (inner-position multivariate
substitution, `f` embedded into each of `Φ`'s two variables) agree mod `π`. Both sides reduce, mod
`π`, to `(Φ mod π) ^ q`: the left via `f ≡ X^q (mod π)` (`PowerSeries.map_subst`), the right via
`f ≡ X^q (mod π)` applied at each coordinate together with the multivariate Frobenius identity
`pow_residueCard_eq_subst_X_pow_mv`. Direct multivariate generalization of
`map_residue_subst_eq_map_residue_subst`; this is item 3 of `ROADMAP.md` §11's three-item
breakdown. -/
theorem map_residue_subst_eq_map_residue_subst_mv {π : O} {f : O⟦X⟧}
    {Φ : MvPowerSeries (Fin 2) O}
    (hf : IsLubinTatePoly π (residueCard O) f) (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) :
    MvPowerSeries.map (residue O) (f.subst Φ) =
      MvPowerSeries.map (residue O) (Φ.subst (fun i ↦ f.subst (MvPowerSeries.X i))) := by
  -- Each coordinate embedding `f.subst (X i)` has zero constant term.
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
  have ha0 : ∀ i, MvPowerSeries.constantCoeff (f.subst (MvPowerSeries.X i)
      (S := O) (τ := Fin 2)) = 0 :=
    fun i ↦ PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0
  have ha : MvPowerSeries.HasSubst (fun i ↦ f.subst (MvPowerSeries.X i) (S := O) (τ := Fin 2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hΦ : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero hΦ0
  -- Outer-position side: `f.subst Φ` reduces mod `π` via `f ≡ X^q`.
  have e1 := PowerSeries.map_subst (a := Φ) hΦ (h := residue O) f
  rw [hf.2.2] at e1
  have hΦmap0 : MvPowerSeries.constantCoeff (MvPowerSeries.map (residue O) Φ) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hΦ0, map_zero]
  have hΦmapSubst : PowerSeries.HasSubst (MvPowerSeries.map (residue O) Φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hΦmap0
  rw [PowerSeries.subst_pow hΦmapSubst, PowerSeries.subst_X hΦmapSubst] at e1
  -- Inner-position side: `Φ.subst (fun i ↦ f.subst (X i))` reduces mod `π` via the same
  -- congruence applied coordinatewise, then the multivariate Frobenius identity.
  have e2 := MvPowerSeries.map_subst (a := fun i ↦ f.subst (MvPowerSeries.X i)
    (S := O) (τ := Fin 2)) ha (h := residue O) Φ
  have hcoord : ∀ i, MvPowerSeries.map (residue O) (f.subst (MvPowerSeries.X i) (S := O)
      (τ := Fin 2)) = (MvPowerSeries.X i : MvPowerSeries (Fin 2) (ResidueField O))
        ^ residueCard O := by
    intro i
    have hXi : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) O) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    have hXi' : PowerSeries.HasSubst
        (MvPowerSeries.X i : MvPowerSeries (Fin 2) (ResidueField O)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    rw [PowerSeries.map_subst (a := MvPowerSeries.X i) hXi (h := residue O) f, hf.2.2,
      MvPowerSeries.map_X, PowerSeries.subst_pow hXi', PowerSeries.subst_X hXi']
  simp_rw [hcoord] at e2
  rw [show (fun i ↦ (MvPowerSeries.X i : MvPowerSeries (Fin 2) (ResidueField O))
      ^ residueCard O) = _ from rfl, ← pow_residueCard_eq_subst_X_pow_mv
      (MvPowerSeries.map (residue O) Φ)] at e2
  rw [e1, e2]

/-- The coefficient-wise consequence of `map_residue_subst_eq_map_residue_subst_mv`: for `f ∈ ℱ_π`
and any `Φ` with zero constant term, every coefficient of `Φ.subst (f, f) - f.subst Φ` is
divisible by `π`. Multivariate analogue of `uniformizer_dvd_coeff_subst_sub_subst`. -/
theorem uniformizer_dvd_coeff_subst_sub_subst_mv {π : O} (hπ : Irreducible π) {f : O⟦X⟧}
    {Φ : MvPowerSeries (Fin 2) O} (hf : IsLubinTatePoly π (residueCard O) f)
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) (n : Fin 2 →₀ ℕ) :
    π ∣ (MvPowerSeries.coeff n (Φ.subst (fun i ↦ f.subst (MvPowerSeries.X i))) -
      MvPowerSeries.coeff n (f.subst Φ)) := by
  have huni : IsLocalRing.maximalIdeal O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  rw [← Ideal.mem_span_singleton, ← huni, ← residue_eq_zero_iff]
  have := map_residue_subst_eq_map_residue_subst_mv hf hΦ0
  have hcoeff : MvPowerSeries.coeff n (MvPowerSeries.map (residue O) (f.subst Φ)) =
      MvPowerSeries.coeff n
        (MvPowerSeries.map (residue O) (Φ.subst (fun i ↦ f.subst (MvPowerSeries.X i)))) := by
    rw [this]
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at hcoeff
  rw [map_sub, hcoeff, sub_self]

/-- **The multivariate binomial correction identity** (multi-index generalization of
`LubinTate.coeff_pow_add_C_mul_X_pow_sub_coeff_pow`, Fact 2' of the univariate file). For `A` with
zero constant term, a nonzero exponent `m : ι →₀ ℕ`, `c : S`, and any exponent `n : ι →₀ ℕ` of
total degree at most that of `m` (`n.degree ≤ m.degree`), the `n`-th coefficient of
`(A + monomial m c) ^ d` differs from that of `A ^ d` by exactly `c` when `n = m` and `d = 1`, and
not at all otherwise. **This settles the combinatorial question item 1 needed to answer**: distinct
monomials of the same (or lower) total degree do not interact through this identity, even though
there are in general several of them at a given total degree (unlike the univariate case, which has
only one degree-`d` monomial). The reason is purely order-theoretic: `m ≤ n` together with
`n.degree ≤ m.degree` forces `m = n` (`Finsupp.degree` is additive and monotone, so writing
`n = m + k` via `exists_add_of_le` gives `n.degree = m.degree + k.degree`, and `n.degree ≤ m.degree`
forces `k.degree = 0`, hence `k = 0`), so a genuinely different exponent `n` at or below `m`'s total
degree never sees the correction term, at any power `d` — not just at the `d ≠ 1` values the
univariate identity already excludes. Proved the same way as the univariate case
(`geom_sum₂_mul` factorization via `coeff_mul_monomial` in place of `coeff_X_pow_mul'`), with the
`n ≠ m` branch closing more directly: `coeff_mul_monomial`'s `if_neg` branch already gives `0`
without needing any constant-coefficient bookkeeping. -/
theorem coeff_pow_add_monomial_sub_coeff_pow_mv {ι S : Type*} [DecidableEq ι] [CommRing S]
    {A : MvPowerSeries ι S} (hA : MvPowerSeries.constantCoeff A = 0) (c : S)
    {m : ι →₀ ℕ} (hm : m ≠ 0) {n : ι →₀ ℕ} (hn : n.degree ≤ m.degree) (d : ℕ) :
    MvPowerSeries.coeff n ((A + MvPowerSeries.monomial m c) ^ d) =
      MvPowerSeries.coeff n (A ^ d) + (if n = m ∧ d = 1 then c else 0) := by
  classical
  have hwc : MvPowerSeries.constantCoeff (MvPowerSeries.monomial m c : MvPowerSeries ι S) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_monomial,
      if_neg (Ne.symm hm)]
  have hxc : MvPowerSeries.constantCoeff (A + MvPowerSeries.monomial m c) = 0 := by
    rw [map_add, hA, hwc, zero_add]
  by_cases hnm : n = m
  · subst hnm
    match d with
    | 0 => simp
    | d + 1 =>
      have hgeom := geom_sum₂_mul (A + MvPowerSeries.monomial n c) A (d + 1)
      have hxy : (A + MvPowerSeries.monomial n c) - A = MvPowerSeries.monomial n c := by ring
      rw [hxy] at hgeom
      set B := ∑ i ∈ Finset.range (d + 1),
        (A + MvPowerSeries.monomial n c) ^ i * A ^ (d + 1 - 1 - i) with hB
      have hcoeff : MvPowerSeries.coeff n (B * MvPowerSeries.monomial n c) =
          MvPowerSeries.coeff n ((A + MvPowerSeries.monomial n c) ^ (d + 1)) -
            MvPowerSeries.coeff n (A ^ (d + 1)) := by
        rw [hgeom, map_sub]
      have hlhs : MvPowerSeries.coeff n (B * MvPowerSeries.monomial n c) =
          c * MvPowerSeries.constantCoeff B := by
        rw [MvPowerSeries.coeff_mul_monomial, if_pos le_rfl, tsub_self,
          MvPowerSeries.coeff_zero_eq_constantCoeff]
        ring
      have hsum : MvPowerSeries.constantCoeff B = if d + 1 = 1 then 1 else 0 := by
        rw [hB, map_sum, Finset.sum_eq_single 0]
        · simp only [Nat.add_sub_cancel, pow_zero, map_pow, hA, one_mul]
          rcases d with _ | d
          · simp
          · simp [zero_pow (Nat.succ_ne_zero d)]
        · intro i hi hi0
          rw [map_mul, map_pow, map_pow, hxc, hA, zero_pow hi0, zero_mul]
        · intro h0
          exact absurd (Finset.mem_range.mpr (by omega)) h0
      rw [hsum] at hlhs
      rw [hlhs] at hcoeff
      rw [eq_sub_iff_add_eq] at hcoeff
      rw [show (if n = n ∧ d + 1 = 1 then (c : S) else 0) = if d + 1 = 1 then c else 0 from by
        simp, ← hcoeff]
      split_ifs <;> ring
  · have hif : (if n = m ∧ d = 1 then c else 0) = 0 := if_neg (fun h ↦ hnm h.1)
    rw [hif, add_zero]
    have hmn : ¬ m ≤ n := by
      intro hle
      obtain ⟨k, hk⟩ := exists_add_of_le hle
      have hdeg_eq : n.degree = m.degree + k.degree := by rw [hk]; exact map_add _ m k
      have hk0 : k.degree = 0 := by omega
      exact hnm (by rw [hk, (Finsupp.degree_eq_zero_iff k).mp hk0, add_zero])
    match d with
    | 0 => simp
    | d + 1 =>
      have hgeom := geom_sum₂_mul (A + MvPowerSeries.monomial m c) A (d + 1)
      have hxy : (A + MvPowerSeries.monomial m c) - A = MvPowerSeries.monomial m c := by ring
      rw [hxy] at hgeom
      have hcoeff : MvPowerSeries.coeff n
          ((∑ i ∈ Finset.range (d + 1),
              (A + MvPowerSeries.monomial m c) ^ i * A ^ (d + 1 - 1 - i)) *
            MvPowerSeries.monomial m c) =
          MvPowerSeries.coeff n ((A + MvPowerSeries.monomial m c) ^ (d + 1)) -
            MvPowerSeries.coeff n (A ^ (d + 1)) := by
        rw [hgeom, map_sub]
      rw [MvPowerSeries.coeff_mul_monomial, if_neg hmn] at hcoeff
      exact sub_eq_zero.mp hcoeff.symm

/-- **The multivariate linear-correction identity, `finsum`-assembled form** (multi-index
generalization of `LubinTate.coeff_subst_add_C_mul_X_pow`, Fact 2 of the univariate file) —
**this closes item 1 of `ROADMAP.md` §11's three-item breakdown**. For a univariate outer series
`h`, a multivariate substitutand `A` with zero constant term, a nonzero exponent `m : ι →₀ ℕ`, and
any exponent `n : ι →₀ ℕ` of total degree at most that of `m`: the `n`-th coefficient of
`h.subst (A + monomial m c)` differs from that of `h.subst A` by exactly `coeff 1 h • c` when
`n = m`, and not at all otherwise (`•` rather than `*` since `h : PowerSeries R` and `A, c` live
over a possibly different `S`-algebra — this is the same `Algebra R S`-scalar action
`PowerSeries.coeff_subst`'s own `finsum` uses termwise; specializing to `R = S` with `Algebra.id`
recovers literal multiplication, matching the univariate statement's `c * coeff 1 h` up to
`smul_eq_mul` and commutativity). Assembling `coeff_pow_add_monomial_sub_coeff_pow_mv` termwise
across `PowerSeries.coeff_subst`'s `finsum`: only the `d = 1` term of the sum ever contributes, and
only when `n = m`. -/
theorem coeff_subst_add_monomial_mv {ι R S : Type*} [DecidableEq ι] [CommRing R] [CommRing S]
    [Algebra R S] (h : PowerSeries R) {A : MvPowerSeries ι S}
    (hA : MvPowerSeries.constantCoeff A = 0) (c : S) {m : ι →₀ ℕ} (hm : m ≠ 0)
    {n : ι →₀ ℕ} (hn : n.degree ≤ m.degree) :
    MvPowerSeries.coeff n (h.subst (A + MvPowerSeries.monomial m c)) =
      MvPowerSeries.coeff n (h.subst A) +
        (if n = m then PowerSeries.coeff 1 h • c else 0) := by
  have hA' : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero hA
  have hmc' : PowerSeries.HasSubst (A + MvPowerSeries.monomial m c) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    rw [map_add, hA, zero_add, ← MvPowerSeries.coeff_zero_eq_constantCoeff,
      MvPowerSeries.coeff_monomial, if_neg (Ne.symm hm)]
  have hfin1 : Function.HasFiniteSupport
      (fun d ↦ PowerSeries.coeff d h • MvPowerSeries.coeff n (A ^ d)) :=
    PowerSeries.coeff_subst_finite hA' h n
  have hfin2 : Function.HasFiniteSupport
      (fun d ↦ PowerSeries.coeff d h • (if n = m ∧ d = 1 then c else 0)) :=
    .subset (Set.finite_singleton 1) (fun d hd ↦ by
      by_contra hd1
      exact hd (by simp [show d ≠ 1 from fun h ↦ hd1 (by simp [h])]))
  calc MvPowerSeries.coeff n (h.subst (A + MvPowerSeries.monomial m c))
      = finsum (fun d ↦ PowerSeries.coeff d h •
          MvPowerSeries.coeff n ((A + MvPowerSeries.monomial m c) ^ d)) :=
        PowerSeries.coeff_subst hmc' h n
    _ = finsum (fun d ↦ PowerSeries.coeff d h •
          (MvPowerSeries.coeff n (A ^ d) + if n = m ∧ d = 1 then c else 0)) :=
        finsum_congr fun d ↦ by
          rw [coeff_pow_add_monomial_sub_coeff_pow_mv hA c hm hn d]
    _ = finsum (fun d ↦ PowerSeries.coeff d h • MvPowerSeries.coeff n (A ^ d)) +
          finsum (fun d ↦ PowerSeries.coeff d h • (if n = m ∧ d = 1 then c else 0)) := by
        simp_rw [smul_add]; exact finsum_add_distrib hfin1 hfin2
    _ = MvPowerSeries.coeff n (h.subst A) + (if n = m then PowerSeries.coeff 1 h • c else 0) := by
        rw [← PowerSeries.coeff_subst hA' h n]
        congr 1
        by_cases hnm : n = m
        · subst hnm
          rw [if_pos rfl, finsum_eq_single _ 1]
          · simp
          · intro d hd; rw [if_neg (by simp [hd]), smul_zero]
        · rw [if_neg hnm, finsum_eq_zero_of_forall_eq_zero]
          intro d
          rw [if_neg (fun h ↦ hnm h.1), smul_zero]

/-- The total degree of a bivariate multi-index is the sum of its two entries. -/
theorem degree_fin_two (m : Fin 2 →₀ ℕ) : m.degree = m 0 + m 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- Extensionality for bivariate multi-indices: agreeing at `0` and at `1` is equality. -/
theorem finsupp_fin_two_ext {m n : Fin 2 →₀ ℕ} (h0 : m 0 = n 0) (h1 : m 1 = n 1) : m = n := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Disequality of bivariate multi-indices, witnessed at a single coordinate. -/
theorem finsupp_fin_two_ne {m n : Fin 2 →₀ ℕ} (i : Fin 2) (h : m i ≠ n i) : m ≠ n :=
  fun hc ↦ h (by rw [hc])

/-- **Two axis-embedded univariate series multiply with independent coefficients.** Substituting
`X 0` into `f` and `X 1` into `g` produces two bivariate series supported on the two coordinate
axes, so the `e`-th coefficient of their product is the plain product of univariate coefficients
`coeff (e 0) f * coeff (e 1) g`. This is the two-series generalization of Mathlib's
`PowerSeries.coeff_subst_X_zero_subst_mul_X_one` (the `g = f` case), proved the same way:
`MvPowerSeries.coeff_mul`'s antidiagonal sum collapses to the single splitting
`e = single 0 (e 0) + single 1 (e 1)`, every other term being killed by
`PowerSeries.coeff_subst_single`'s axis-purity. -/
theorem coeff_subst_X_zero_mul_subst_X_one {R : Type*} [CommRing R] (f g : R⟦X⟧)
    (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) *
        g.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) =
      PowerSeries.coeff (e 0) f * PowerSeries.coeff (e 1) g := by
  rw [MvPowerSeries.coeff_mul,
    Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1)) ?_ ?_]
  · grind [PowerSeries.coeff_subst_single]
  · intro b hb hb'
    by_contra hne
    rcases ne_zero_and_ne_zero_of_mul hne with ⟨h0, h1⟩
    simp only [PowerSeries.coeff_subst_single, ne_eq, ite_eq_right_iff, not_forall,
      exists_prop] at h0 h1
    apply hb'
    rw [Prod.ext_iff, ← Finset.mem_antidiagonal.mp hb, h0.1, h1.1]
    simp
  · intro he
    have he' : Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) = e := by
      ext i; fin_cases i <;> simp
    exact absurd (Finset.mem_antidiagonal.mpr he') he

/-- **The outer-position monomial substitution, coefficientwise.** Substituting the *diagonal*
family `a i := f.subst (X i)` (the univariate `f` embedded along each coordinate axis) into a single
monomial `monomial m c` gives a series whose `n`-th coefficient factors completely into univariate
data: `c * coeff (n 0) (f ^ m 0) * coeff (n 1) (f ^ m 1)`.

This is the multivariate counterpart of the univariate step `(C c * X ^ k).subst g = C c * g ^ k`
used in `LubinTate.subst_phi_eq_phi_subst`, and it is what makes the *outer*-position behaviour of
a monomial correction computable. The proof combines `MvPowerSeries.subst_monomial` (which turns
the monomial into `algebraMap c` times `∏ s, (a s) ^ (m s)`), `PowerSeries.subst_pow` (moving each
power inside the axis embedding, so the factors are `(f ^ m 0).subst (X 0)` and
`(f ^ m 1).subst (X 1)`), and `coeff_subst_X_zero_mul_subst_X_one` (which factors the coefficient
of that axis-disjoint product). -/
theorem coeff_subst_monomial_diag {R : Type*} [CommRing R] {f : R⟦X⟧}
    (ha : MvPowerSeries.HasSubst
      (fun i ↦ f.subst (MvPowerSeries.X i) : Fin 2 → MvPowerSeries (Fin 2) R))
    (m n : Fin 2 →₀ ℕ) (c : R) :
    MvPowerSeries.coeff n
        ((MvPowerSeries.monomial m c).subst (fun i ↦ f.subst (MvPowerSeries.X i))) =
      c * (PowerSeries.coeff (n 0) (f ^ m 0) * PowerSeries.coeff (n 1) (f ^ m 1)) := by
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) :=
    fun i ↦ PowerSeries.HasSubst.X i
  have key : (m.prod fun s e ↦ (f.subst (MvPowerSeries.X s) : MvPowerSeries (Fin 2) R) ^ e) =
      (f ^ m 0).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) *
        (f ^ m 1).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) := by
    rw [Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _), Fin.prod_univ_two,
      PowerSeries.subst_pow (hX 0), PowerSeries.subst_pow (hX 1)]
  rw [MvPowerSeries.subst_monomial ha m c, key]
  simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    MvPowerSeries.coeff_C_mul]
  rw [coeff_subst_X_zero_mul_subst_X_one]

/-- **The outer-position monomial-correction identity.** Specializing `coeff_subst_monomial_diag`
to a series `f` with `coeff 0 f = 0` and `coeff 1 f = u`: at any multi-index `n` of total degree at
most that of `m`, substituting the diagonal family `a i := f.subst (X i)` into `monomial m c`
contributes exactly `c * u ^ m.degree` at `n = m` and nothing at all elsewhere.

This is the *outer*-position analogue of `coeff_subst_add_monomial_mv` (which handles the inner
position), and the exact multivariate replacement for the univariate `c * π ^ (d + 2)` term in
`LubinTate.subst_phi_eq_phi_subst`, with `m.degree` in place of `d + 2`. The vanishing off the
diagonal is the multivariate content: when `n ≠ m` but `n.degree ≤ m.degree`, one of the two
coordinates must satisfy `n i < m i`, and `coeff (n i) (f ^ m i) = 0` there because `f ^ (m i)` has
order at least `m i`. -/
theorem coeff_subst_monomial_diag_of_degree_le {R : Type*} [CommRing R] {f : R⟦X⟧} {u : R}
    (hf0 : PowerSeries.coeff 0 f = 0) (hf1 : PowerSeries.coeff 1 f = u)
    (ha : MvPowerSeries.HasSubst
      (fun i ↦ f.subst (MvPowerSeries.X i) : Fin 2 → MvPowerSeries (Fin 2) R))
    {m n : Fin 2 →₀ ℕ} (hn : n.degree ≤ m.degree) (c : R) :
    MvPowerSeries.coeff n
        ((MvPowerSeries.monomial m c).subst (fun i ↦ f.subst (MvPowerSeries.X i))) =
      if n = m then c * u ^ m.degree else 0 := by
  rw [coeff_subst_monomial_diag ha m n c]
  by_cases hnm : n = m
  · subst hnm
    rw [if_pos rfl, coeff_pow_self_of_coeff_zero_eq_zero hf0 hf1 (n 0),
      coeff_pow_self_of_coeff_zero_eq_zero hf0 hf1 (n 1), ← pow_add, degree_fin_two]
  · rw [if_neg hnm]
    have hd : n 0 + n 1 ≤ m 0 + m 1 := by
      rw [← degree_fin_two, ← degree_fin_two]; exact hn
    have hlt : n 0 < m 0 ∨ n 1 < m 1 := by
      by_contra hc
      exact hnm (finsupp_fin_two_ext (by omega) (by omega))
    have hconst : PowerSeries.constantCoeff f = 0 := by
      rwa [← PowerSeries.coeff_zero_eq_constantCoeff]
    have hzero : ∀ k d : ℕ, k < d → PowerSeries.coeff k (f ^ d) = 0 := fun k d hkd ↦
      PowerSeries.coeff_of_lt_order k
        (lt_of_lt_of_le (by exact_mod_cast hkd)
          (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hconst))
    rcases hlt with h | h
    · rw [hzero _ _ h, zero_mul, mul_zero]
    · rw [hzero _ _ h, mul_zero, mul_zero]

/-- The constant coefficient of a finite sum of monomials at nonzero exponents vanishes. -/
theorem constantCoeff_sum_monomial {ι S κ : Type*} [DecidableEq ι] [CommRing S] (s : Finset κ)
    (M : κ → ι →₀ ℕ) (c : κ → S) (hM : ∀ k ∈ s, M k ≠ 0) :
    MvPowerSeries.constantCoeff (∑ k ∈ s, MvPowerSeries.monomial (M k) (c k)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_monomial,
    if_neg (Ne.symm (hM k hk))]

/-- **The inner-position linear-correction identity for a whole batch of monomials.** Iterating
`coeff_subst_add_monomial_mv` across a `Finset` of simultaneous monomial corrections, all of total
degree at least `n.degree`: each contributes its own `coeff 1 h • c k` exactly at `n = M k`, and the
corrections do not interfere. This is what the multivariate recursion needs that the univariate one
does not — at each total-degree step there is a *batch* of new coefficients (one per multi-index of
that degree), not a single one. -/
theorem coeff_subst_add_sum_monomial_mv {ι κ R S : Type*} [DecidableEq ι] [CommRing R] [CommRing S]
    [Algebra R S] (h : PowerSeries R) {A : MvPowerSeries ι S}
    (hA : MvPowerSeries.constantCoeff A = 0) {n : ι →₀ ℕ} (s : Finset κ) (M : κ → ι →₀ ℕ)
    (c : κ → S) (hM : ∀ k ∈ s, M k ≠ 0) (hdeg : ∀ k ∈ s, n.degree ≤ (M k).degree) :
    MvPowerSeries.coeff n (h.subst (A + ∑ k ∈ s, MvPowerSeries.monomial (M k) (c k))) =
      MvPowerSeries.coeff n (h.subst A) +
        ∑ k ∈ s, (if n = M k then PowerSeries.coeff 1 h • c k else 0) := by
  classical
  revert hM hdeg
  induction s using Finset.induction with
  | empty => intro _ _; simp
  | @insert a s ha ih =>
    intro hM hdeg
    have hmem : ∀ k ∈ s, k ∈ insert a s := fun k hk ↦ Finset.mem_insert_of_mem hk
    have hA' : MvPowerSeries.constantCoeff
        (A + ∑ k ∈ s, MvPowerSeries.monomial (M k) (c k)) = 0 := by
      rw [map_add, hA, constantCoeff_sum_monomial s M c (fun k hk ↦ hM k (hmem k hk)), add_zero]
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      show A + (MvPowerSeries.monomial (M a) (c a) +
            ∑ k ∈ s, MvPowerSeries.monomial (M k) (c k)) =
          (A + ∑ k ∈ s, MvPowerSeries.monomial (M k) (c k)) +
            MvPowerSeries.monomial (M a) (c a) from by ring,
      coeff_subst_add_monomial_mv h hA' (c a) (hM a (Finset.mem_insert_self a s))
        (hdeg a (Finset.mem_insert_self a s)),
      ih (fun k hk ↦ hM k (hmem k hk)) (fun k hk ↦ hdeg k (hmem k hk))]
    ring

/-- **Multi-index truncation invariance for powers.** If two multivariate series agree on every
coefficient of total degree at most `N`, so do all their corresponding powers. Multivariate
replacement for the univariate `X ^ (n + 1) ∣ (b - b')` propagation used in
`LubinTate.coeff_subst_eq_of_dvd_sub`: total-degree truncation is not a divisibility condition, so
the propagation is proved directly, by induction on the exponent through
`MvPowerSeries.coeff_mul`'s antidiagonal (both factors of a splitting of `e` have total degree at
most `e.degree`). -/
theorem coeff_pow_eq_of_coeff_eq_mv {ι S : Type*} [DecidableEq ι] [CommRing S]
    {b b' : MvPowerSeries ι S} {N : ℕ}
    (hbb : ∀ j : ι →₀ ℕ, j.degree ≤ N → MvPowerSeries.coeff j b = MvPowerSeries.coeff j b')
    (d : ℕ) {e : ι →₀ ℕ} (he : e.degree ≤ N) :
    MvPowerSeries.coeff e (b ^ d) = MvPowerSeries.coeff e (b' ^ d) := by
  induction d generalizing e with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.mem_antidiagonal] at hp
    have hdeg : (p.1 + p.2).degree = p.1.degree + p.2.degree := map_add _ _ _
    rw [hp] at hdeg
    rw [ih (by omega), hbb p.2 (by omega)]

/-- **Truncation invariance, inner position, multivariate.** If two admissible multivariate
substitutands agree in total degree at most `N`, substituting either into a fixed univariate outer
series gives the same coefficient at every multi-index of total degree at most `N`. Multivariate
analogue of `LubinTate.coeff_subst_eq_of_dvd_sub`. -/
theorem coeff_subst_eq_of_coeff_eq_mv {ι R S : Type*} [DecidableEq ι] [CommRing R] [CommRing S]
    [Algebra R S] (h : PowerSeries R) {b b' : MvPowerSeries ι S}
    (hb : PowerSeries.HasSubst b) (hb' : PowerSeries.HasSubst b') {N : ℕ}
    (hbb : ∀ j : ι →₀ ℕ, j.degree ≤ N → MvPowerSeries.coeff j b = MvPowerSeries.coeff j b')
    {e : ι →₀ ℕ} (he : e.degree ≤ N) :
    MvPowerSeries.coeff e (h.subst b) = MvPowerSeries.coeff e (h.subst b') := by
  rw [PowerSeries.coeff_subst hb, PowerSeries.coeff_subst hb']
  exact finsum_congr fun d ↦ by rw [coeff_pow_eq_of_coeff_eq_mv hbb d he]

/-- **Truncation invariance, outer position, multivariate.** If two univariate outer series agree
on coefficients `0, …, N`, substituting a fixed multivariate series with zero constant term into
either gives the same coefficient at every multi-index of total degree at most `N`. Multivariate
analogue of `LubinTate.coeff_subst_eq_of_dvd_sub_left`, and proved the same way: beyond degree `N`
the substitutand's powers have order too large to contribute at `e`. -/
theorem coeff_subst_eq_of_coeff_eq_left_mv {ι R S : Type*} [DecidableEq ι] [CommRing R]
    [CommRing S] [Algebra R S] {b : MvPowerSeries ι S}
    (hb0 : MvPowerSeries.constantCoeff b = 0) {h h' : PowerSeries R} {N : ℕ}
    (hh : ∀ d ≤ N, PowerSeries.coeff d h = PowerSeries.coeff d h')
    {e : ι →₀ ℕ} (he : e.degree ≤ N) :
    MvPowerSeries.coeff e (h.subst b) = MvPowerSeries.coeff e (h'.subst b) := by
  have hb : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero hb0
  rw [PowerSeries.coeff_subst hb, PowerSeries.coeff_subst hb]
  refine finsum_congr fun d ↦ ?_
  by_cases hdn : d ≤ N
  · rw [hh d hdn]
  · have hzero : MvPowerSeries.coeff e (b ^ d) = 0 :=
      MvPowerSeries.coeff_of_lt_order
        (lt_of_lt_of_le (by exact_mod_cast (by omega : e.degree < d))
          (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d hb0))
    rw [hzero, smul_zero, smul_zero]

/-- A product `∏ s, (a s) ^ (d s)` of powers of series with zero constant term has no coefficient
below total degree `d.degree`. The multi-index refinement of
`MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero`, extracted from the argument Mathlib uses
inside `MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_sum`. -/
theorem coeff_prod_pow_eq_zero_of_degree_lt {σ τ S : Type*} [CommRing S]
    {a : σ → MvPowerSeries τ S} (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    {d : σ →₀ ℕ} {e : τ →₀ ℕ} (h : e.degree < d.degree) :
    MvPowerSeries.coeff e (d.prod fun s j ↦ (a s) ^ j) = 0 := by
  rw [Finsupp.prod]
  refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (Nat.cast_lt.mpr h)
    (.trans ?_ (MvPowerSeries.le_order_prod _ d.support)))
  exact_mod_cast Finset.sum_le_sum fun i _ ↦
    MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (ha0 i)

/-- **Truncation invariance, outer position, for a multivariate outer series.** If two
multivariate series agree in total degree at most `N`, substituting a fixed admissible family with
zero constant terms into either gives the same coefficient at every multi-index of total degree at
most `N`. This is the shape needed for `Φ.subst (fun i ↦ f.subst (X i))`, where the *outer* series
is itself multivariate — neither `LubinTate.coeff_subst_eq_of_dvd_sub_left` nor its multivariate
restatement `coeff_subst_eq_of_coeff_eq_left_mv` covers it, since both take a univariate outer
series. -/
theorem coeff_subst_eq_of_coeff_eq_outer_mv {σ τ R S : Type*} [DecidableEq σ] [CommRing R]
    [CommRing S] [Algebra R S] {a : σ → MvPowerSeries τ S} (ha : MvPowerSeries.HasSubst a)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {Φ Φ' : MvPowerSeries σ R} {N : ℕ}
    (hΦ : ∀ j : σ →₀ ℕ, j.degree ≤ N → MvPowerSeries.coeff j Φ = MvPowerSeries.coeff j Φ')
    {e : τ →₀ ℕ} (he : e.degree ≤ N) :
    MvPowerSeries.coeff e (Φ.subst a) = MvPowerSeries.coeff e (Φ'.subst a) := by
  rw [MvPowerSeries.coeff_subst ha, MvPowerSeries.coeff_subst ha]
  refine finsum_congr fun d ↦ ?_
  by_cases hd : d.degree ≤ N
  · rw [hΦ d hd]
  · rw [coeff_prod_pow_eq_zero_of_degree_lt ha0 (by omega : e.degree < d.degree),
      smul_zero, smul_zero]

variable {π : O} {f : O⟦X⟧}

/-- **The multi-index `(k, l) : Fin 2 →₀ ℕ`**, built from its two coordinate values via
`Finsupp.equivFunOnFinite` (every function out of a finite type is automatically finitely
supported). This is the concrete enumeration device for "all exponents of a given total degree
`d` over `Fin 2 →₀ ℕ`": the exponents of total degree `d` are exactly `mkIdx k (d - k)` for
`k = 0, …, d`. -/
def mkIdx (k l : ℕ) : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![k, l]

@[simp] theorem mkIdx_apply_zero (k l : ℕ) : mkIdx k l 0 = k := rfl

@[simp] theorem mkIdx_apply_one (k l : ℕ) : mkIdx k l 1 = l := rfl

theorem degree_mkIdx (k l : ℕ) : (mkIdx k l).degree = k + l := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, mkIdx_apply_zero, mkIdx_apply_one]

theorem mkIdx_ne_zero (k l : ℕ) (h : k + l ≠ 0) : mkIdx k l ≠ 0 := by
  intro he
  apply h
  have hk : mkIdx k l 0 = (0 : Fin 2 →₀ ℕ) 0 := by rw [he]
  have hl : mkIdx k l 1 = (0 : Fin 2 →₀ ℕ) 1 := by rw [he]
  simp only [mkIdx_apply_zero, mkIdx_apply_one, Finsupp.coe_zero, Pi.zero_apply] at hk hl
  omega

/-- **The recursive state for the 2-variable functional equation lemma's formal group series
`Φ`, bundled with its own zero-constant-term invariant**, the direct total-degree-indexed
generalization of `LubinTate.phiState`. `PhiState hπ hf n` packages, for total degree `n`: a
function `ℕ → O` giving the newly-fixed coefficients at multi-indices of degree `n` (`.1.1`,
indexed by the first coordinate `k`, so the coefficient at `mkIdx k (n - k)` is `.1.1 k`) and the
partial sum of `Φ`'s coefficients through total degree `n` (`.1.2`), together with a *proof* that
this partial sum has zero constant term (`.2`).

Unlike the univariate case, `Φ ≡ X + Y (mod deg 2)` is a *fixed* base case (not a free linear
parameter `a`): this is the canonical series that, once existence/uniqueness are established,
specializes to the Lubin-Tate formal group law `F_π` itself. At each total degree `d + 2 ≥ 2`,
the batch of `d + 3` new coefficients (one per multi-index `mkIdx k (d + 2 - k)`, `k = 0, …, d +
2`) is computed **directly from the single previous state** `PhiState hπ hf (d + 1)` via
`uniformizer_dvd_coeff_subst_sub_subst_mv` (unconditional `π`-divisibility at *every* multi-index,
for *any* admissible partial sum) and the same unit-inversion technique `phiState` uses (`1 -
π^(d+1)` is a unit since `π ∈ 𝔪`). Crucially, the `Finset.sum` assembling these `d + 3`
correction monomials does **not** bury any recursive call inside it — every one of the `d + 3`
coefficients is computed from the single `let prev := PhiState hπ hf (d + 1)` closed over before
the sum is built, exactly the `phiState`-style workaround the univariate file's docstring flags:
the recursion is structural in `n`, calling `PhiState` at exactly one strictly smaller index. -/
noncomputable def PhiState (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    (n : ℕ) → {p : (ℕ → O) × MvPowerSeries (Fin 2) O // MvPowerSeries.constantCoeff p.2 = 0}
  | 0 => ⟨(fun _ ↦ 0, 0), by simp⟩
  | 1 => ⟨(fun _ ↦ 1, MvPowerSeries.X 0 + MvPowerSeries.X 1), by simp⟩
  | d + 2 =>
      let prev := PhiState hπ hf (d + 1)
      let Φ := prev.1.2
      have hΦ0 : MvPowerSeries.constantCoeff Φ = 0 := prev.2
      have hmem : π ∈ maximalIdeal O := (mem_maximalIdeal π).mpr hπ.not_isUnit
      have hpowmem : π ^ (d + 1) ∈ maximalIdeal O :=
        Ideal.pow_mem_of_mem (maximalIdeal O) hmem (d + 1) (by omega)
      have hunit : IsUnit (1 - π ^ (d + 1)) :=
        isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).mp hpowmem)
      have hdvd : ∀ k : ℕ, π ∣ (MvPowerSeries.coeff (mkIdx k (d + 2 - k))
          (Φ.subst (fun i ↦ f.subst (MvPowerSeries.X i))) -
            MvPowerSeries.coeff (mkIdx k (d + 2 - k)) (f.subst Φ)) :=
        fun k ↦ uniformizer_dvd_coeff_subst_sub_subst_mv hπ hf hΦ0 (mkIdx k (d + 2 - k))
      let c : ℕ → O := fun k ↦ (↑hunit.unit⁻¹ : O) * (hdvd k).choose
      let correction : MvPowerSeries (Fin 2) O :=
        ∑ k ∈ Finset.range (d + 3), MvPowerSeries.monomial (mkIdx k (d + 2 - k)) (c k)
      ⟨(c, Φ + correction), by
        rw [map_add, hΦ0, zero_add, map_sum]
        refine Finset.sum_eq_zero fun k _ ↦ ?_
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_monomial,
          if_neg (Ne.symm (mkIdx_ne_zero k (d + 2 - k) (by omega)))]⟩

/-- The coefficient of `Φ` at multi-index `m`, extracted from `PhiState` at total degree
`m.degree`, reading off the `(m 0)`-th entry of that degree's coefficient function. Direct
generalization of `LubinTate.phiCoeff`. -/
noncomputable def PhiCoeff (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f)
    (m : Fin 2 →₀ ℕ) : O :=
  (PhiState hπ hf m.degree).1.1 (m 0)

/-- The partial sum of `Φ`'s coefficients through total degree `n`, extracted from `PhiState`.
Always has zero constant term (`constantCoeff_PhiPartialSum`), the invariant `PhiState` carries.
Direct generalization of `LubinTate.phiPartialSum`. -/
noncomputable def PhiPartialSum (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f)
    (n : ℕ) : MvPowerSeries (Fin 2) O :=
  (PhiState hπ hf n).1.2

@[simp] theorem constantCoeff_PhiPartialSum (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) :
    MvPowerSeries.constantCoeff (PhiPartialSum hπ hf n) = 0 :=
  (PhiState hπ hf n).2

@[simp] theorem PhiPartialSum_zero (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    PhiPartialSum hπ hf 0 = 0 := by
  simp [PhiPartialSum, PhiState]

@[simp] theorem PhiPartialSum_one (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    PhiPartialSum hπ hf 1 = MvPowerSeries.X 0 + MvPowerSeries.X 1 := by
  simp [PhiPartialSum, PhiState]

@[simp] theorem PhiCoeff_zero (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    PhiCoeff hπ hf 0 = 0 := by
  simp [PhiCoeff, PhiState]

theorem PhiCoeff_mkIdx_one_zero (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    PhiCoeff hπ hf (mkIdx 1 0) = 1 := by
  simp [PhiCoeff, degree_mkIdx, PhiState]

theorem PhiCoeff_mkIdx_zero_one (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    PhiCoeff hπ hf (mkIdx 0 1) = 1 := by
  simp [PhiCoeff, degree_mkIdx, PhiState]

theorem PhiPartialSum_succ_succ (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f)
    (d : ℕ) :
    PhiPartialSum hπ hf (d + 2) =
      PhiPartialSum hπ hf (d + 1) +
        ∑ k ∈ Finset.range (d + 3), MvPowerSeries.monomial (mkIdx k (d + 2 - k))
          (PhiCoeff hπ hf (mkIdx k (d + 2 - k))) := by
  have hcoeff : ∀ k ∈ Finset.range (d + 3),
      MvPowerSeries.monomial (mkIdx k (d + 2 - k)) (PhiCoeff hπ hf (mkIdx k (d + 2 - k))) =
        MvPowerSeries.monomial (mkIdx k (d + 2 - k)) ((PhiState hπ hf (d + 2)).1.1 k) :=
    fun k hk ↦ by
      rw [Finset.mem_range] at hk
      congr 1
      show (PhiState hπ hf (mkIdx k (d + 2 - k)).degree).1.1 (mkIdx k (d + 2 - k) 0) = _
      rw [degree_mkIdx, mkIdx_apply_zero, Nat.add_sub_cancel' (by omega : k ≤ d + 2)]
  rw [Finset.sum_congr rfl hcoeff]
  simp only [PhiPartialSum, PhiState]

/-- **The recursive step actually solves the equation it is defined to solve, at every
multi-index of the new total degree.** The direct generalization of
`LubinTate.pi_mul_one_sub_pow_mul_phiCoeff`: this is the precise sense in which `PhiState`'s
degree-`(d+2)` case is well-defined, at *each* of the `d + 3` multi-indices of total degree `d +
2` independently — matching `ROADMAP.md` §14's confirmation that distinct same-degree monomials
do not interact, so each of these equations is exactly as solvable, and independently so, as the
single univariate equation `phiState` solves at each step. -/
theorem pi_mul_one_sub_pow_mul_PhiCoeff (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (d k : ℕ) (hk : k ≤ d + 2) :
    π * (1 - π ^ (d + 1)) * PhiCoeff hπ hf (mkIdx k (d + 2 - k)) =
      MvPowerSeries.coeff (mkIdx k (d + 2 - k))
        ((PhiPartialSum hπ hf (d + 1)).subst (fun i ↦ f.subst (MvPowerSeries.X i))) -
        MvPowerSeries.coeff (mkIdx k (d + 2 - k)) (f.subst (PhiPartialSum hπ hf (d + 1))) := by
  have hPhiCoeff : PhiCoeff hπ hf (mkIdx k (d + 2 - k)) = (PhiState hπ hf (d + 2)).1.1 k := by
    show (PhiState hπ hf (mkIdx k (d + 2 - k)).degree).1.1 (mkIdx k (d + 2 - k) 0) = _
    rw [degree_mkIdx, mkIdx_apply_zero, Nat.add_sub_cancel' hk]
  rw [hPhiCoeff]
  show π * (1 - π ^ (d + 1)) * (PhiState hπ hf (d + 2)).1.1 k = _
  simp only [PhiPartialSum, PhiState]
  exact pi_mul_mul_unit_inv_mul_choose _ _

/-- Every multi-index of total degree `1` carries coefficient `1`: this is the `Φ ≡ X + Y (mod deg
2)` base case, read off `PhiState`'s degree-`1` constant function. -/
theorem PhiCoeff_of_degree_eq_one (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {m : Fin 2 →₀ ℕ} (hm : m.degree = 1) :
    PhiCoeff hπ hf m = 1 := by
  simp [PhiCoeff, hm, PhiState]

/-- **The coefficient-agreement invariant tying `PhiPartialSum` to `PhiCoeff`**, the multi-index
generalization of `LubinTate.coeff_phiPartialSum`: the partial sum through total degree `n` agrees
with `PhiCoeff` at every multi-index of total degree at most `n`, and vanishes beyond. Proved by
induction on `n` matching `PhiState`'s own recursion shape (`0`, `1`, `d + 2`); at the recursive
step, the batch of `d + 3` degree-`(d + 2)` monomials contributes at exactly one multi-index,
selected by its first coordinate. -/
theorem coeff_PhiPartialSum (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f)
    (n : ℕ) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (PhiPartialSum hπ hf n) =
      if m.degree ≤ n then PhiCoeff hπ hf m else 0 := by
  induction n with
  | zero =>
    rw [PhiPartialSum_zero, map_zero]
    by_cases hm : m.degree ≤ 0
    · rw [if_pos hm, (Finsupp.degree_eq_zero_iff m).mp (by omega), PhiCoeff_zero]
    · rw [if_neg hm]
  | succ n ih =>
    rcases n with _ | d
    · -- total degree `1`: the fixed base case `Φ ≡ X + Y`
      rw [PhiPartialSum_one, map_add, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
      rcases Nat.lt_or_ge m.degree 2 with hlt | hge
      · rcases Nat.eq_zero_or_pos m.degree with h | h
        · have hm : m = 0 := (Finsupp.degree_eq_zero_iff m).mp h
          subst hm
          rw [if_neg (finsupp_fin_two_ne (m := 0) (n := Finsupp.single 0 1) 0 (by simp)),
            if_neg (finsupp_fin_two_ne (m := 0) (n := Finsupp.single 1 1) 1 (by simp)),
            if_pos (show Finsupp.degree (0 : Fin 2 →₀ ℕ) ≤ 0 + 1 from by simp),
            PhiCoeff_zero, add_zero]
        · have hd2 : m 0 + m 1 = 1 := by rw [← degree_fin_two]; omega
          rcases Nat.eq_zero_or_pos (m 0) with h0 | h0
          · have hm : m = Finsupp.single 1 1 :=
              finsupp_fin_two_ext (by simp [h0]) (by simp; omega)
            subst hm
            rw [if_neg (finsupp_fin_two_ne (m := Finsupp.single 1 1)
                (n := Finsupp.single 0 1) 0 (by simp)),
              if_pos (show (Finsupp.single (1 : Fin 2) 1) = Finsupp.single 1 1 from rfl),
              if_pos (show Finsupp.degree (Finsupp.single (1 : Fin 2) (1 : ℕ)) ≤ 0 + 1 from by
                simp),
              PhiCoeff_of_degree_eq_one hπ hf (by simp), zero_add]
          · have hm : m = Finsupp.single 0 1 :=
              finsupp_fin_two_ext (by simp; omega) (by simp; omega)
            subst hm
            rw [if_pos (show (Finsupp.single (0 : Fin 2) 1) = Finsupp.single 0 1 from rfl),
              if_neg (finsupp_fin_two_ne (m := Finsupp.single 0 1)
                (n := Finsupp.single 1 1) 0 (by simp)),
              if_pos (show Finsupp.degree (Finsupp.single (0 : Fin 2) (1 : ℕ)) ≤ 0 + 1 from by
                simp),
              PhiCoeff_of_degree_eq_one hπ hf (by simp), add_zero]
      · rw [if_neg (show ¬(m = Finsupp.single 0 1) from fun hc ↦ by rw [hc] at hge; simp at hge),
          if_neg (show ¬(m = Finsupp.single 1 1) from fun hc ↦ by rw [hc] at hge; simp at hge),
          if_neg (show ¬(Finsupp.degree m ≤ 0 + 1) from by omega), add_zero]
    · -- the recursive step at total degree `d + 2`
      have hMdeg : ∀ k ∈ Finset.range (d + 3), (mkIdx k (d + 2 - k)).degree = d + 2 :=
        fun k hk ↦ by
          rw [Finset.mem_range] at hk
          rw [degree_mkIdx]; omega
      rw [PhiPartialSum_succ_succ, map_add, map_sum, ih]
      by_cases hm2 : m.degree ≤ d + 1
      · rw [if_pos hm2, if_pos (by omega),
          Finset.sum_eq_zero (fun k hk ↦ by
            rw [MvPowerSeries.coeff_monomial, if_neg (fun hc ↦ by
              rw [hc, hMdeg k hk] at hm2; omega)]),
          add_zero]
      · rw [if_neg hm2, zero_add]
        by_cases hm3 : m.degree = d + 2
        · have hm0 : m 0 ≤ d + 2 := by rw [degree_fin_two] at hm3; omega
          have hmk : mkIdx (m 0) (d + 2 - m 0) = m :=
            finsupp_fin_two_ext (by simp) (by
              simp only [mkIdx_apply_one]
              rw [degree_fin_two] at hm3; omega)
          rw [if_pos (by omega), Finset.sum_eq_single (m 0)]
          · rw [hmk, MvPowerSeries.coeff_monomial_same]
          · intro k hk hkne
            rw [MvPowerSeries.coeff_monomial, if_neg (fun hc ↦ hkne (by rw [hc, mkIdx_apply_zero]))]
          · intro hnot
            exact absurd (Finset.mem_range.mpr (by omega)) hnot
        · rw [if_neg (by omega)]
          exact Finset.sum_eq_zero fun k hk ↦ by
            rw [MvPowerSeries.coeff_monomial, if_neg (fun hc ↦ by
              rw [hc, hMdeg k hk] at hm3; omega)]

/-- **The fully assembled 2-variable series `Φ`**, built from `PhiCoeff` at every multi-index.
Once `subst_Phi_eq_Phi_subst` and `eq_of_subst_eq_mv` are in hand, this *is* the Lubin-Tate formal
group law `F_π`. -/
noncomputable def Phi (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    MvPowerSeries (Fin 2) O :=
  MvPowerSeries.mk (PhiCoeff hπ hf)

@[simp] theorem coeff_Phi (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f)
    (m : Fin 2 →₀ ℕ) : MvPowerSeries.coeff m (Phi hπ hf) = PhiCoeff hπ hf m := rfl

@[simp] theorem constantCoeff_Phi (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) :
    MvPowerSeries.constantCoeff (Phi hπ hf) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, coeff_Phi, PhiCoeff_zero]

/-- `Φ` and its degree-`n` truncation agree at every multi-index of total degree at most `n` — the
hypothesis both truncation-invariance lemmas consume. -/
theorem coeff_Phi_eq_coeff_PhiPartialSum (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) (m : Fin 2 →₀ ℕ) (hm : m.degree ≤ n) :
    MvPowerSeries.coeff m (Phi hπ hf) = MvPowerSeries.coeff m (PhiPartialSum hπ hf n) := by
  rw [coeff_Phi, coeff_PhiPartialSum, if_pos hm]

/-- **The 2-variable Lubin-Tate functional equation lemma, existence half.** The fully assembled
bivariate series `Φ := Phi hπ hf` satisfies `f(Φ(X, Y)) = Φ(f(X), f(Y))`. Proved multi-index by
multi-index (`MvPowerSeries.ext`), following `LubinTate.subst_phi_eq_phi_subst`'s shape with total
degree in place of degree — and, as there, needing no induction hypothesis, since truncation
invariance reduces every multi-index to the partial sum at its own total degree.

At total degree `0` both sides have zero constant term. At total degree `1`, truncating `Φ` to
`PhiPartialSum 1 = X + Y` makes both sides computable in closed form (Mathlib's
`PowerSeries.coeff_subst_X_zero_add_X_one` on the left, `PowerSeries.coeff_subst_single` on the
right), and both equal `π`. At total degree `d + 2`, the four facts combine exactly as in the
univariate case: truncation invariance (`coeff_subst_eq_of_coeff_eq_mv` /
`coeff_subst_eq_of_coeff_eq_outer_mv`) replaces `Φ` by `PhiPartialSum (d + 2) = PhiPartialSum (d +
1) + (batch of degree-`(d+2)` monomials)`; the inner-position batch correction
(`coeff_subst_add_sum_monomial_mv`) contributes `coeff 1 f * c = π * c`; the outer-position batch
correction (`coeff_subst_monomial_diag_of_degree_le`) contributes `c * π ^ (d + 2)`; and the
per-multi-index defining equation `pi_mul_one_sub_pow_mul_PhiCoeff` identifies the difference of
the two `PhiPartialSum (d + 1)` terms as `π * (1 - π ^ (d + 1)) * c`, cancelling the two
corrections on the nose. In both batch sums exactly one summand survives, selected by the first
coordinate of the multi-index. -/
theorem subst_Phi_eq_Phi_subst (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) :
    f.subst (Phi hπ hf) =
      (Phi hπ hf).subst (fun i ↦ f.subst (MvPowerSeries.X i)) := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
  have ha0 : ∀ i, MvPowerSeries.constantCoeff
      (f.subst (MvPowerSeries.X i) (S := O) (τ := Fin 2)) = 0 :=
    fun i ↦ PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0
  have ha : MvPowerSeries.HasSubst
      (fun i ↦ f.subst (MvPowerSeries.X i) (S := O) (τ := Fin 2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hΦ0 : MvPowerSeries.constantCoeff (Phi hπ hf) = 0 := constantCoeff_Phi hπ hf
  have hΦ : PowerSeries.HasSubst (Phi hπ hf) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hΦ0
  refine MvPowerSeries.ext fun n ↦ ?_
  rcases hd : n.degree with _ | dd
  · -- total degree `0`: both sides have zero constant term
    have hn0 : n = 0 := (Finsupp.degree_eq_zero_iff n).mp hd
    subst hn0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_subst_eq_zero hΦ0 f hf0,
      MvPowerSeries.constantCoeff_subst_eq_zero ha ha0 hΦ0]
  · rcases dd with _ | d
    · -- total degree `1`: `Φ` truncates to `X + Y`
      have hnd : n.degree ≤ 1 := le_of_eq hd
      have hP0 : MvPowerSeries.constantCoeff (PhiPartialSum hπ hf 1) = 0 :=
        constantCoeff_PhiPartialSum hπ hf 1
      have hPsub : PowerSeries.HasSubst (PhiPartialSum hπ hf 1) :=
        PowerSeries.HasSubst.of_constantCoeff_zero hP0
      have hdeg : n 0 + n 1 = 1 := by rw [← degree_fin_two]; exact hd
      rw [coeff_subst_eq_of_coeff_eq_mv f hΦ hPsub
          (fun j hj ↦ coeff_Phi_eq_coeff_PhiPartialSum hπ hf 1 j hj) hnd,
        coeff_subst_eq_of_coeff_eq_outer_mv ha ha0
          (fun j hj ↦ coeff_Phi_eq_coeff_PhiPartialSum hπ hf 1 j hj) hnd,
        PhiPartialSum_one, MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha,
        MvPowerSeries.subst_X ha, map_add, PowerSeries.coeff_subst_X_zero_add_X_one,
        PowerSeries.coeff_subst_single, PowerSeries.coeff_subst_single, hdeg]
      rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
      · have h1 : n 1 = 1 := by omega
        have hns : n = Finsupp.single 1 1 := finsupp_fin_two_ext (by simp [h0]) (by simp [h1])
        rw [if_neg (by rw [hns]; exact finsupp_fin_two_ne 1 (by simp)),
          if_pos (by rw [hns]; simp), h0, h1, hf.2.1]
        simp
      · have h0' : n 0 = 1 := by omega
        have h1 : n 1 = 0 := by omega
        have hns : n = Finsupp.single 0 1 := finsupp_fin_two_ext (by simp [h0']) (by simp [h1])
        rw [if_pos (by rw [hns]; simp),
          if_neg (by rw [hns]; exact finsupp_fin_two_ne 0 (by simp)),
          h0', hf.2.1]
        simp
    · -- the recursive step at total degree `d + 2`
      have hnd : n.degree ≤ d + 2 := le_of_eq hd
      have hA0 : MvPowerSeries.constantCoeff (PhiPartialSum hπ hf (d + 1)) = 0 :=
        constantCoeff_PhiPartialSum hπ hf (d + 1)
      have hP0 : MvPowerSeries.constantCoeff (PhiPartialSum hπ hf (d + 2)) = 0 :=
        constantCoeff_PhiPartialSum hπ hf (d + 2)
      have hPsub : PowerSeries.HasSubst (PhiPartialSum hπ hf (d + 2)) :=
        PowerSeries.HasSubst.of_constantCoeff_zero hP0
      have hMne : ∀ k ∈ Finset.range (d + 3), mkIdx k (d + 2 - k) ≠ 0 := fun k hk ↦ by
        rw [Finset.mem_range] at hk
        exact mkIdx_ne_zero k (d + 2 - k) (by omega)
      have hMdeg : ∀ k ∈ Finset.range (d + 3), (mkIdx k (d + 2 - k)).degree = d + 2 :=
        fun k hk ↦ by
          rw [Finset.mem_range] at hk
          rw [degree_mkIdx]; omega
      have hn0le : n 0 ≤ d + 2 := by rw [degree_fin_two] at hd; omega
      have hnmk : mkIdx (n 0) (d + 2 - n 0) = n :=
        finsupp_fin_two_ext (by simp) (by
          simp only [mkIdx_apply_one]
          rw [degree_fin_two] at hd; omega)
      have hnot : ∀ k ∈ Finset.range (d + 3), k ≠ n 0 → ¬ (n = mkIdx k (d + 2 - k)) :=
        fun k _ hk hc ↦ hk (by rw [hc, mkIdx_apply_zero])
      have hinner : MvPowerSeries.coeff n (f.subst (Phi hπ hf)) =
          MvPowerSeries.coeff n (f.subst (PhiPartialSum hπ hf (d + 1))) +
            PowerSeries.coeff 1 f * PhiCoeff hπ hf n := by
        rw [coeff_subst_eq_of_coeff_eq_mv f hΦ hPsub
            (fun j hj ↦ coeff_Phi_eq_coeff_PhiPartialSum hπ hf (d + 2) j hj) hnd,
          PhiPartialSum_succ_succ,
          coeff_subst_add_sum_monomial_mv f hA0 (Finset.range (d + 3))
            (fun k ↦ mkIdx k (d + 2 - k)) (fun k ↦ PhiCoeff hπ hf (mkIdx k (d + 2 - k)))
            hMne (fun k hk ↦ by rw [hMdeg k hk]; exact hnd),
          Finset.sum_eq_single (n 0)]
        · rw [if_pos hnmk.symm, hnmk, smul_eq_mul]
        · intro k hk hkne
          rw [if_neg (hnot k hk hkne)]
        · intro hmem
          exact absurd (Finset.mem_range.mpr (by omega)) hmem
      have houter : MvPowerSeries.coeff n
            ((Phi hπ hf).subst (fun i ↦ f.subst (MvPowerSeries.X i))) =
          MvPowerSeries.coeff n
              ((PhiPartialSum hπ hf (d + 1)).subst (fun i ↦ f.subst (MvPowerSeries.X i))) +
            PhiCoeff hπ hf n * π ^ (d + 2) := by
        rw [coeff_subst_eq_of_coeff_eq_outer_mv ha ha0
            (fun j hj ↦ coeff_Phi_eq_coeff_PhiPartialSum hπ hf (d + 2) j hj) hnd,
          PhiPartialSum_succ_succ, MvPowerSeries.subst_add ha]
        simp only [← MvPowerSeries.substAlgHom_apply ha, map_sum, map_add]
        simp only [MvPowerSeries.substAlgHom_apply ha]
        congr 1
        rw [Finset.sum_congr rfl (fun k hk ↦
            coeff_subst_monomial_diag_of_degree_le hf.1 hf.2.1 ha
              (m := mkIdx k (d + 2 - k)) (by rw [hMdeg k hk]; exact hnd) _),
          Finset.sum_eq_single (n 0)]
        · rw [if_pos hnmk.symm, hMdeg (n 0) (Finset.mem_range.mpr (by omega)), hnmk]
        · intro k hk hkne
          rw [if_neg (hnot k hk hkne)]
        · intro hmem
          exact absurd (Finset.mem_range.mpr (by omega)) hmem
      have hkey := pi_mul_one_sub_pow_mul_PhiCoeff hπ hf d (n 0) hn0le
      rw [hnmk] at hkey
      rw [hinner, houter, hf.2.1]
      linear_combination hkey

end LubinTate

end
