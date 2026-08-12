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

end LubinTate

end
