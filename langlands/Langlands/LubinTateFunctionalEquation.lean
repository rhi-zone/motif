import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Langlands.LubinTate

/-!
# Toward the Lubin-Tate functional equation lemma: the residue-field congruence

This file starts the second, genuinely deep stage of the Lubin-Tate thread opened in
`Langlands/LubinTate.lean`: the **functional equation lemma**. That lemma builds, for
`f, g ∈ ℱ_π` and a linear starting form, a power series intertwining `f` and `g` by solving one
linear equation in `O` per total-degree step. This file proves the single load-bearing fact that
makes every one of those steps solvable: reducing mod `π`, `f` and `g` act identically (as the
Frobenius-twisted `q`-th power map) on *any* power series with zero constant term, so the
degree-by-degree obstruction in the functional equation lemma's recursion is *always* divisible by
`π`, unconditionally (not merely once earlier degrees are known to already satisfy the equation).

## Main results

* `residueCharP`, `residueDegree`, `card_residueField_eq` : the residue characteristic `p` and the
  degree `n` with `residueCard O = p ^ n`, packaged the same way `Langlands/WeilGroup.lean` already
  does for `𝓀[K]` (`WeilGroup.residueCharP`/`residueDegree`/`card_residueField_eq`), specialized to
  `ResidueField O`.
* `pow_residueCard_eq_subst_X_pow` : for `h` a power series over the (finite) residue field,
  `h ^ residueCard O = h.subst (X ^ residueCard O)` — the Frobenius/Frobenius-iterate identity
  `h(X)^q = h(X^q)` valid for *any* `h`, coming from `MvPowerSeries.map_iterateFrobenius_expand`
  together with the Fermat/`FiniteField.pow_card` fact that the iterated Frobenius `x ↦ x ^ q` is
  the identity on a field with exactly `q` elements.
* `map_residue_subst_eq_map_residue_subst` : for `f, g ∈ ℱ_π` and any `φ : O⟦X⟧` with
  `coeff 0 φ = 0` (so `f.subst φ` and `φ.subst g` are both defined), reducing mod `π` gives
  `map (residue O) (f.subst φ) = map (residue O) (φ.subst g)`. Both sides reduce to
  `(map (residue O) φ) ^ residueCard O`, using `f ≡ X^q ≡ g (mod π)` on one side and
  `pow_residueCard_eq_subst_X_pow` on the other. Crucially this holds for *every* admissible `φ`,
  not just ones already known to approximately intertwine `f` and `g` — this is what removes the
  need for an interleaved recursion/correctness induction when this lemma is used to build the
  functional equation lemma's intertwining power series degree by degree.
* `uniformizer_dvd_coeff_subst_sub_subst` : the coefficient-wise consequence,
  `π ∣ coeff n (φ.subst g) - coeff n (f.subst φ)` for every `n`, obtained from
  `map_residue_subst_eq_map_residue_subst` via `IsLocalRing.residue_eq_zero_iff` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
* `phiState`, `phiCoeff`, `phiPartialSum` : the recursive construction of the functional equation
  lemma's intertwining power series `φ`, coefficient by coefficient. `phiState hπ a hf hg n`
  bundles the degree-`n` coefficient and the partial sum through degree `n` together with a proof
  that the partial sum has zero constant term — bundling this invariant into the return type is
  what lets the recursive step at degree `d + 2` supply `uniformizer_dvd_coeff_subst_sub_subst`'s
  `coeff 0 φ = 0` hypothesis from the *previous* state's own proof component, with no
  self-reference to `phiState`'s own base case and no `Finset.sum`-buried recursive calls (the
  latter defeats Lean's termination checker outright — documented at `phiState`). `phiCoeff`/
  `phiPartialSum` extract the two components. `phiCoeff_zero`, `phiCoeff_one` give the base cases
  (`0`, `a`); `phiPartialSum_succ_succ` gives the recursive step's shape; and
  `pi_mul_one_sub_pow_mul_phiCoeff` shows the degree-`(d+2)` coefficient actually solves the linear
  equation it is defined to solve — the recursion is well-defined not merely because the term
  typechecks, but because it provably satisfies its own defining equation.

## What this does not yet do

The functional equation lemma's existence half — proving the *fully assembled* `φ := mk
(phiCoeff hπ a hf hg)` satisfies `f.subst φ = φ.subst g` (as opposed to `phiCoeff`'s per-degree
defining equation against the *truncated partial sum*, which is what `pi_mul_one_sub_pow_mul_phiCoeff`
already gives) — is not attempted in this file. That remaining step is a linearization/Taylor
argument analogous to Mathlib's `PowerSeries.coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X`
(`Mathlib/RingTheory/PowerSeries/Substitution.lean`), itself a genuinely hard ~50-line proof for
the strictly simpler one-sided case (`P.subst Q = X`, one power series, not two); our two-sided
intertwining equation is the same shape of argument with materially more bookkeeping, not a
smaller version of it. Also not attempted: uniqueness of `φ`, and everything downstream (the
`n = 2`/`F_π` formal group law specialization).
-/

@[expose] public section

noncomputable section

open PowerSeries IsLocalRing

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

instance : Fintype (ResidueField O) := Fintype.ofFinite _

/-- The residue characteristic of `O`, i.e. the characteristic of `ResidueField O`. Packaged the
same way `WeilGroup.residueCharP` is, specialized to `ResidueField O` in place of `𝓀[K]`. -/
def residueCharP (O : Type*) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] : ℕ :=
  ringChar (ResidueField O)

instance : CharP (ResidueField O) (residueCharP O) := ringChar.charP _

instance residueCharP_fact : Fact (residueCharP O).Prime :=
  ⟨CharP.char_is_prime (ResidueField O) _⟩

instance : ExpChar (ResidueField O) (residueCharP O) :=
  .prime (residueCharP_fact (O := O)).out

/-- The degree of `ResidueField O` over its prime field, i.e. the `n` with
`residueCard O = residueCharP O ^ n` (`card_residueField_eq`). -/
def residueDegree (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] : ℕ+ :=
  (FiniteField.card (ResidueField O) (residueCharP O)).choose

theorem card_residueField_eq :
    residueCard O = (residueCharP O) ^ (residueDegree O : ℕ) := by
  rw [residueCard, Nat.card_eq_fintype_card]
  exact (FiniteField.card (ResidueField O) (residueCharP O)).choose_spec.2

/-- The iterated Frobenius `x ↦ x ^ residueCard O` fixes every element of `ResidueField O`
(Fermat's little theorem for finite fields, `FiniteField.pow_card`), so as a ring homomorphism it
is the identity. -/
theorem iterateFrobenius_residueField_eq_id :
    iterateFrobenius (ResidueField O) (residueCharP O) (residueDegree O : ℕ) =
      RingHom.id (ResidueField O) := by
  have hcard : Fintype.card (ResidueField O) = (residueCharP O) ^ (residueDegree O : ℕ) := by
    rw [← Nat.card_eq_fintype_card]; exact card_residueField_eq
  ext x
  rw [iterateFrobenius_def, RingHom.id_apply, ← hcard]
  exact FiniteField.pow_card x

/-- **The Frobenius/`q`-th-power identity for power series over the residue field.** For *any*
power series `h` over the finite residue field `ResidueField O`, `h(X)^q = h(X^q)` where
`q = residueCard O`: raising `h` to the `q`-th power is the same as substituting `X^q` for `X`.
This is the Frobenius-iterate fact `MvPowerSeries.map_iterateFrobenius_expand`, specialized using
that the iterated Frobenius is the identity on `ResidueField O`
(`iterateFrobenius_residueField_eq_id`). -/
theorem pow_residueCard_eq_subst_X_pow (h : (ResidueField O)⟦X⟧) :
    h ^ residueCard O = PowerSeries.subst (X ^ residueCard O) h := by
  have hp : (residueCharP O) ≠ 0 := (residueCharP_fact (O := O)).out.ne_zero
  have hcard : residueCard O = residueCharP O ^ (residueDegree O : ℕ) := card_residueField_eq
  rw [hcard]
  have key := MvPowerSeries.map_iterateFrobenius_expand (σ := Unit) (R := ResidueField O)
    (residueCharP O) hp h (residueDegree O : ℕ)
  rw [iterateFrobenius_residueField_eq_id, MvPowerSeries.map_id, RingHom.id_apply] at key
  rw [← key]
  exact PowerSeries.expand_apply _ (pow_ne_zero _ hp) h

/-- **The residue-field congruence underlying the functional equation lemma's recursion.** For
`f, g ∈ ℱ_π` (same `π`, `q`) and *any* `φ : O⟦X⟧` with zero constant term, `f(φ(X))` and `φ(g(X))`
agree mod `π`. Both sides reduce, mod `π`, to `(φ mod π) ^ q`: the left via `f ≡ X^q (mod π)`
(direct substitution), the right via `g ≡ X^q (mod π)` together with the Frobenius identity
`pow_residueCard_eq_subst_X_pow`. This holds unconditionally for every admissible `φ`, not only
for `φ` already known to approximately intertwine `f` and `g`. -/
theorem map_residue_subst_eq_map_residue_subst {π : O} {f g φ : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    (hφ0 : coeff 0 φ = 0) :
    PowerSeries.map (residue O) (f.subst φ) = PowerSeries.map (residue O) (φ.subst g) := by
  have hφ0' : constantCoeff φ = 0 := by rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hφ0
  have hg0' : constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hg.1
  have hφ : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ0'
  have hg' : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg0'
  have hgmap : MvPowerSeries.map (residue O) g = (X : (ResidueField O)⟦X⟧) ^ residueCard O :=
    hg.2.2
  have e1 := PowerSeries.map_subst (S := ResidueField O) hφ (h := residue O) f
  have e2 := PowerSeries.map_subst (S := ResidueField O) hg' (h := residue O) φ
  rw [hf.2.2] at e1
  rw [hgmap] at e2
  rw [show PowerSeries.map (residue O) (f.subst φ) = _ from e1,
    show PowerSeries.map (residue O) (φ.subst g) = _ from e2]
  have hφmap0 : MvPowerSeries.constantCoeff (MvPowerSeries.map (residue O) φ) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, show MvPowerSeries.constantCoeff φ = (0 : O) from hφ0',
      map_zero]
  have hφmapSubst : PowerSeries.HasSubst (MvPowerSeries.map (residue O) φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hφmap0
  rw [PowerSeries.subst_pow hφmapSubst, PowerSeries.subst_X hφmapSubst]
  exact pow_residueCard_eq_subst_X_pow (O := O) (MvPowerSeries.map (residue O) φ)

/-- The coefficient-wise consequence of `map_residue_subst_eq_map_residue_subst`: for `f, g ∈ ℱ_π`
and any admissible `φ`, every coefficient of `φ.subst g - f.subst φ` is divisible by `π`. This is
exactly the solvability fact the functional equation lemma's degree-by-degree recursion needs at
every step, and it holds unconditionally (see the module docstring). -/
theorem uniformizer_dvd_coeff_subst_sub_subst {π : O} (hπ : Irreducible π)
    {f g φ : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    (hg : IsLubinTatePoly π (residueCard O) g) (hφ0 : coeff 0 φ = 0) (n : ℕ) :
    π ∣ (coeff n (φ.subst g) - coeff n (f.subst φ)) := by
  have huni : IsLocalRing.maximalIdeal O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  rw [← Ideal.mem_span_singleton, ← huni, ← residue_eq_zero_iff]
  have := map_residue_subst_eq_map_residue_subst hf hg hφ0
  have hcoeff : PowerSeries.coeff n (PowerSeries.map (residue O) (φ.subst g)) =
      PowerSeries.coeff n (PowerSeries.map (residue O) (f.subst φ)) := by rw [this]
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map] at hcoeff
  rw [map_sub, hcoeff, sub_self]

variable {π : O} {f g : O⟦X⟧}

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **Generic algebraic solving step**, stated independently of `phiCoeff`/`phiState` so it can
discharge the recursive step's defining equation *by unification* against whatever specific
`IsUnit`/`Dvd.dvd` proof terms Lean's equation compiler happens to have produced internally,
without needing those opaque terms to be named or rewritten (rewriting them directly runs into a
dependent-motive obstruction, since the `IsUnit` witness's *type* mentions the very ring element
being solved for). For any `u` with `IsUnit u` and any `y` with `π ∣ y`:
`π * u * (↑hunit.unit⁻¹ * hdvd.choose) = y`. -/
theorem pi_mul_mul_unit_inv_mul_choose {π : O} {u : O} (hunit : IsUnit u) {y : O}
    (hdvd : π ∣ y) : π * u * ((↑hunit.unit⁻¹ : O) * hdvd.choose) = y := by
  have h1 : u * (↑hunit.unit⁻¹ : O) = 1 := hunit.mul_val_inv
  calc π * u * ((↑hunit.unit⁻¹ : O) * hdvd.choose)
      = π * (u * (↑hunit.unit⁻¹ : O)) * hdvd.choose := by ring
    _ = π * 1 * hdvd.choose := by rw [h1]
    _ = π * hdvd.choose := by ring
    _ = y := hdvd.choose_spec.symm

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **Truncation invariance, inner position** (Fact 1 of the existence induction). If two
admissible substitutands `b`, `b'` agree on coefficients `0, …, n` (packaged as
`X^(n+1) ∣ (b - b')`), then substituting either of them into a fixed outer series `h` gives the
same `n`-th coefficient. Proved the same way Mathlib's `PowerSeries.subst_substInv_right` proves
its analogous truncation fact: expand via `coeff_subst'` into a `finsum` over powers of the
substitutand, and note `X^(n+1) ∣ (b - b')` propagates to `X^(n+1) ∣ (b^d - b'^d)` via
`sub_dvd_pow_sub_pow`, which forces `coeff n (b^d) = coeff n (b'^d)` via `X_pow_dvd_iff`. -/
theorem coeff_subst_eq_of_dvd_sub {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : R⟦X⟧) {b b' : S⟦X⟧} (hb : PowerSeries.HasSubst b) (hb' : PowerSeries.HasSubst b')
    (n : ℕ) (hdvd : (X : S⟦X⟧) ^ (n + 1) ∣ (b - b')) :
    coeff n (h.subst b) = coeff n (h.subst b') := by
  rw [coeff_subst' hb, coeff_subst' hb']
  refine finsum_congr fun d ↦ ?_
  congr 1
  have hpow : (X : S⟦X⟧) ^ (n + 1) ∣ (b ^ d - b' ^ d) := hdvd.trans (sub_dvd_pow_sub_pow b b' d)
  have := X_pow_dvd_iff.mp hpow n (Nat.lt_succ_self n)
  rwa [map_sub, sub_eq_zero] at this

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **Truncation invariance, outer position** (the outer-position analogue of Fact 1). If two
outer series `f`, `f'` agree on coefficients `0, …, n`, substituting a fixed admissible `g` into
either gives the same `n`-th coefficient. Unlike the inner-position case, this needs no
`HasSubst` hypothesis on `f`/`f'` themselves (substitution is always defined in the outer
argument) — only `constantCoeff g = 0`, so that `coeff n (g ^ d) = 0` once `d > n`
(`le_order_pow_of_constantCoeff_eq_zero`), collapsing the `finsum` over `d` to the range where the
hypothesis on `f`/`f'` already applies termwise. -/
theorem coeff_subst_eq_of_dvd_sub_left {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {g : S⟦X⟧} (hg : constantCoeff g = 0) {f f' : R⟦X⟧} (n : ℕ)
    (hdvd : (X : R⟦X⟧) ^ (n + 1) ∣ (f - f')) :
    coeff n (f.subst g) = coeff n (f'.subst g) := by
  have hg' : PowerSeries.HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [coeff_subst' hg' f, coeff_subst' hg' f']
  refine finsum_congr fun d ↦ ?_
  by_cases hdn : d ≤ n
  · congr 1
    have := X_pow_dvd_iff.mp hdvd d (by omega)
    rwa [map_sub, sub_eq_zero] at this
  · have horder : (n : ℕ∞) < (g ^ d).order :=
      lt_of_lt_of_le (by exact_mod_cast (by omega : n < d))
        (le_order_pow_of_constantCoeff_eq_zero d hg)
    rw [coeff_of_lt_order n horder, smul_zero, smul_zero]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **The binomial correction identity** (Fact 2', the crux algebraic fact behind Fact 2). For `A`
with zero constant term, `c : S`, `n ≥ 1`, and every exponent `d`, the `n`-th coefficient of
`(A + C c * X^n)^d` differs from that of `A^d` by exactly `c` when `d = 1`, and not at all
otherwise. Proved via the geometric-sum factorization `x^d - y^d = (∑ i < d, x^i y^(d-1-i))(x-y)`
(`geom_sum₂_mul`) with `x := A + C c * X^n`, `y := A`, so `x - y = C c * X^n`: the `n`-th
coefficient of the difference is `c` times the *constant* coefficient of the geometric sum (via
`coeff_X_pow_mul`), and that constant coefficient is `(constantCoeff (A + C c * X^n))^i *
(constantCoeff A)^(d-1-i)` summed over `i < d` — since both constant coefficients are `0`, every
term vanishes except possibly `i = 0`, which itself only survives (contributing `1`) when
`d - 1 = 0`, i.e. `d = 1`. -/
theorem coeff_pow_add_C_mul_X_pow_sub_coeff_pow {S : Type*} [CommRing S] {A : S⟦X⟧}
    (hA : constantCoeff A = 0) (c : S) {n : ℕ} (hn : 1 ≤ n) (d : ℕ) :
    coeff n ((A + C c * X ^ n) ^ d) = coeff n (A ^ d) + (if d = 1 then c else 0) := by
  have hwc : constantCoeff (C c * X ^ n : S⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  have hxc : constantCoeff (A + C c * X ^ n) = 0 := by rw [map_add, hA, hwc, zero_add]
  match d with
  | 0 => simp
  | d + 1 =>
    have hgeom := geom_sum₂_mul (A + C c * X ^ n) A (d + 1)
    have hxy : (A + C c * X ^ n) - A = C c * X ^ n := by ring
    rw [hxy] at hgeom
    set B := ∑ i ∈ Finset.range (d + 1), (A + C c * X ^ n) ^ i * A ^ (d + 1 - 1 - i) with hB
    have hcoeff : coeff n (B * (C c * X ^ n)) =
        coeff n ((A + C c * X ^ n) ^ (d + 1)) - coeff n (A ^ (d + 1)) := by
      rw [hgeom, map_sub]
    have hlhs : coeff n (B * (C c * X ^ n)) = c * constantCoeff B := by
      rw [show B * (C c * X ^ n) = C c * (X ^ n * B) from by ring, coeff_C_mul,
        coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff]
    have hsum : constantCoeff B = if d + 1 = 1 then 1 else 0 := by
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
    rw [← hcoeff]
    split_ifs <;> ring

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **Fact 2, the linear-correction identity in `finsum` form.** Assembling
`coeff_pow_add_C_mul_X_pow_sub_coeff_pow` (Fact 2') termwise across `coeff_subst'`'s `finsum`: the
`n`-th coefficient of substituting `A + C c * X^n` into `h` differs from that of substituting `A`
alone by exactly `c * coeff 1 h` — only the `d = 1` term of the `finsum` sees the correction. -/
theorem coeff_subst_add_C_mul_X_pow {R : Type*} [CommRing R]
    (h : R⟦X⟧) {A : R⟦X⟧} (hA : constantCoeff A = 0) (c : R) {n : ℕ} (hn : 1 ≤ n) :
    coeff n (h.subst (A + C c * X ^ n)) = coeff n (h.subst A) + c * coeff 1 h := by
  have hA' : PowerSeries.HasSubst A := HasSubst.of_constantCoeff_zero' hA
  have hAc' : PowerSeries.HasSubst (A + C c * X ^ n) := by
    apply HasSubst.of_constantCoeff_zero'
    rw [map_add, hA, zero_add, ← coeff_zero_eq_constantCoeff, coeff_C_mul, coeff_X_pow,
      if_neg (by omega), mul_zero]
  have hfin1 : Function.HasFiniteSupport (fun d ↦ coeff d h • coeff n (A ^ d)) :=
    coeff_subst_finite' hA' h n
  have hfin2 : Function.HasFiniteSupport (fun d ↦ coeff d h • (if d = 1 then c else 0)) :=
    .subset (Set.finite_singleton 1) (fun d hd ↦ by
      by_contra hd1
      exact hd (by simp [show d ≠ 1 from fun h ↦ hd1 (by simp [h])]))
  calc coeff n (h.subst (A + C c * X ^ n))
      = finsum (fun d ↦ coeff d h • coeff n ((A + C c * X ^ n) ^ d)) := coeff_subst' hAc' h n
    _ = finsum (fun d ↦ coeff d h • (coeff n (A ^ d) + if d = 1 then c else 0)) :=
        finsum_congr fun d ↦ by rw [coeff_pow_add_C_mul_X_pow_sub_coeff_pow hA c hn d]
    _ = finsum (fun d ↦ coeff d h • coeff n (A ^ d)) +
          finsum (fun d ↦ coeff d h • (if d = 1 then c else 0)) := by
        simp_rw [smul_add]; exact finsum_add_distrib hfin1 hfin2
    _ = coeff n (h.subst A) + c * coeff 1 h := by
        rw [← coeff_subst' hA' h n, finsum_eq_single _ 1]
        · simp [mul_comm]
        · intro d hd; rw [if_neg hd, smul_zero]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **Fact 4, the leading coefficient of `g^n`.** For `b` with `coeff 0 b = 0` and
`coeff 1 b = u`, the `n`-th coefficient of `b^n` is `u^n`: by induction on `n`, using that
`coeff i (b^n) = 0` for `i < n` (`le_order_pow_of_constantCoeff_eq_zero`) to collapse
`coeff (n+1) (b^n * b)`'s convolution sum to its `(n, 1)` term, and `coeff 0 b = 0` to kill the
`(n+1, 0)` term. -/
theorem coeff_pow_self_of_coeff_zero_eq_zero {S : Type*} [CommRing S] {b : S⟦X⟧} {u : S}
    (hb0 : coeff 0 b = 0) (hb1 : coeff 1 b = u) (n : ℕ) :
    coeff n (b ^ n) = u ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hconst : constantCoeff b = 0 := by rwa [← coeff_zero_eq_constantCoeff]
    have horder : (n : ℕ∞) ≤ (b ^ n).order := le_order_pow_of_constantCoeff_eq_zero n hconst
    rw [pow_succ, coeff_mul, Finset.sum_eq_single (n, 1)]
    · rw [ih, hb1]; ring
    · rintro ⟨i, j⟩ hij hne
      rw [Finset.mem_antidiagonal] at hij
      rcases Nat.lt_trichotomy i n with hi | hi | hi
      · have hlt : (i : ℕ∞) < (b ^ n).order := lt_of_lt_of_le (by exact_mod_cast hi) horder
        rw [coeff_of_lt_order i hlt, zero_mul]
      · exact absurd (Prod.ext hi (by omega)) hne
      · have hj0 : j = 0 := by omega
        rw [hj0, hb0, mul_zero]
    · intro hmem
      exact absurd
        (show ((n, 1) : ℕ × ℕ) ∈ Finset.antidiagonal (n + 1) from Finset.mem_antidiagonal.mpr rfl)
        hmem

/-- **The recursive state for the functional equation lemma's intertwining power series `φ`,
bundled with its own zero-constant-term invariant.** `phiState hπ a hf hg n` packages, for
degree `n`: the newly-fixed coefficient (`.1.1`) and the partial sum of `φ`'s coefficients up
through degree `n` (`.1.2`), together with a *proof* that this partial sum has zero constant term
(`.2`). Bundling the invariant into the return type (rather than proving it after the fact) is
what makes the recursive step well-typed: at degree `d + 2`, the previous state's own proof
component (`(phiState hπ a hf hg (d + 1)).2`) supplies exactly the `coeff 0 φ = 0` hypothesis
`uniformizer_dvd_coeff_subst_sub_subst` needs, with no self-reference to `phiState`'s own base
case required — this is what makes Lean accept the definition as a single structural recursion on
`n` (each case calls `phiState` at exactly one strictly smaller index, unlike an approach summing
over all prior coefficients via `Finset.sum`, which defeats Lean's termination checker since the
recursive calls end up buried inside an opaque higher-order `Finset.sum` argument).

At `n = d + 2 ≥ 2`, the new coefficient solves the linear equation the hand-derivation recorded in
`ROADMAP.md` §8 identifies: `π · (1 - π^(d+1)) · c = coeff (d+2) (φ_d.subst g) - coeff (d+2)
(f.subst φ_d)`, where `φ_d` is the previous state's partial sum — obtained by extracting the
`π`-divisible witness for the right-hand side via `uniformizer_dvd_coeff_subst_sub_subst` (this
applies unconditionally, to *any* admissible partial sum, not only to ones already known to
intertwine `f` and `g` correctly — see this file's module docstring) and inverting the unit factor
`1 - π^(d+1)` via `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits` (`π^(d+1) ∈ 𝔪` since `π ∈ 𝔪`
and `d + 1 ≥ 1`, so `1 - π^(d+1)` is a unit in the local ring `O`, no completeness needed). -/
noncomputable def phiState (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g) :
    (n : ℕ) → {p : O × O⟦X⟧ // coeff 0 p.2 = 0}
  | 0 => ⟨(0, 0), by simp⟩
  | 1 => ⟨(a, PowerSeries.C a * X), by simp⟩
  | d + 2 =>
      let prev := phiState hπ a hf hg (d + 1)
      let φ := prev.1.2
      have hφ0 : coeff 0 φ = 0 := prev.2
      have hmem : π ∈ maximalIdeal O := (mem_maximalIdeal π).mpr hπ.not_isUnit
      have hpowmem : π ^ (d + 1) ∈ maximalIdeal O :=
        Ideal.pow_mem_of_mem (maximalIdeal O) hmem (d + 1) (by omega)
      have hunit : IsUnit (1 - π ^ (d + 1)) :=
        isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).mp hpowmem)
      have hdvd : π ∣ (coeff (d + 2) (φ.subst g) - coeff (d + 2) (f.subst φ)) :=
        uniformizer_dvd_coeff_subst_sub_subst hπ hf hg hφ0 (d + 2)
      let c := (↑hunit.unit⁻¹ : O) * hdvd.choose
      ⟨(c, φ + PowerSeries.C c * X ^ (d + 2)), by
        show coeff 0 (φ + PowerSeries.C c * X ^ (d + 2)) = 0
        rw [map_add, hφ0, zero_add, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]⟩

/-- The degree-`n` coefficient of the functional equation lemma's intertwining power series `φ`,
extracted from `phiState`. `phiCoeff 0 = 0`, `phiCoeff 1 = a` (`phiCoeff_zero`, `phiCoeff_one`). -/
noncomputable def phiCoeff (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    (n : ℕ) : O :=
  (phiState hπ a hf hg n).1.1

/-- The partial sum of `φ`'s coefficients through degree `n`, extracted from `phiState`. Always
has zero constant term (`coeff_zero_phiPartialSum`), the invariant `phiState` carries. -/
noncomputable def phiPartialSum (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    (n : ℕ) : O⟦X⟧ :=
  (phiState hπ a hf hg n).1.2

@[simp] theorem coeff_zero_phiPartialSum (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    (n : ℕ) :
    coeff 0 (phiPartialSum hπ a hf hg n) = 0 :=
  (phiState hπ a hf hg n).2

@[simp] theorem phiCoeff_zero (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g) :
    phiCoeff hπ a hf hg 0 = 0 := by
  simp [phiCoeff, phiState]

@[simp] theorem phiCoeff_one (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g) :
    phiCoeff hπ a hf hg 1 = a := by
  simp [phiCoeff, phiState]

@[simp] theorem phiPartialSum_one (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g) :
    phiPartialSum hπ a hf hg 1 = PowerSeries.C a * X := by
  simp [phiPartialSum, phiState]

theorem phiPartialSum_succ_succ (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    (d : ℕ) :
    phiPartialSum hπ a hf hg (d + 2) =
      phiPartialSum hπ a hf hg (d + 1) +
        PowerSeries.C (phiCoeff hπ a hf hg (d + 2)) * X ^ (d + 2) := by
  simp only [phiPartialSum, phiCoeff, phiState]

/-- **The recursive step actually solves the equation it is defined to solve.** This is the
precise sense in which `phiState`'s degree-`(d+2)` case is well-defined: not merely that the term
typechecks (it must, to compile at all — `IsUnit (1 - π^(d+1))` and the `π`-divisibility witness
are both genuinely constructed, not assumed), but that the resulting coefficient satisfies the
defining linear equation on the nose. -/
theorem pi_mul_one_sub_pow_mul_phiCoeff (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    (d : ℕ) :
    π * (1 - π ^ (d + 1)) * phiCoeff hπ a hf hg (d + 2) =
      coeff (d + 2) ((phiPartialSum hπ a hf hg (d + 1)).subst g) -
        coeff (d + 2) (f.subst (phiPartialSum hπ a hf hg (d + 1))) := by
  simp only [phiCoeff, phiPartialSum, phiState]
  exact pi_mul_mul_unit_inv_mul_choose _ _

end LubinTate

end
