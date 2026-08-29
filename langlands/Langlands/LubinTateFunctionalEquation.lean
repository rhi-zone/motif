import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Langlands.LubinTate

/-!
# The Lubin-Tate functional equation lemma: existence and uniqueness

This file completes the Lubin-Tate thread opened in `Langlands/LubinTate.lean`: the **functional
equation lemma**. That lemma builds, for `f, g ∈ ℱ_π` and a linear starting form `a`, a power
series `φ` intertwining `f` and `g` — `f(φ(X)) = φ(g(X))` — and shows `φ` is the unique such series
with the given linear coefficient. Both halves are proved here, in full:
`subst_phi_eq_phi_subst` (existence) and `eq_of_coeff_zero_eq_zero_of_coeff_one_eq_of_subst_eq`
(uniqueness).

The file proceeds in three stages. First, the residue-field congruence: reducing mod `π`, `f` and
`g` act identically (as the Frobenius-twisted `q`-th power map) on *any* power series with zero
constant term, so the degree-by-degree obstruction in the functional equation lemma's recursion is
*always* divisible by `π`, unconditionally. Second, the recursive coefficient-by-coefficient
construction of `φ` (`phiState`/`phiCoeff`/`phiPartialSum`), each step solving its own local linear
equation. Third, the bridge from "each truncation solves its own local equation" to "the fully
assembled series solves the global equation" — four general algebraic facts (two truncation-
invariance lemmas, a linear-correction identity, and a leading-coefficient identity) that together
prove existence, and whose reuse against an *arbitrary* solution (via `genTrunc` in place of
`phiPartialSum`) proves uniqueness.

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

* `coeff_subst_eq_of_dvd_sub`, `coeff_subst_eq_of_dvd_sub_left` : general-purpose truncation
  invariance, inner and outer position — if two substitutands (resp. two outer series) agree on
  coefficients `0, …, n`, substitution agrees on coefficient `n`.
* `coeff_pow_add_C_mul_X_pow_sub_coeff_pow`, `coeff_subst_add_C_mul_X_pow` : the linear correction
  identity — extending a substitutand by one new top-degree term shifts the `n`-th coefficient of a
  substitution by exactly `(new coefficient) * (coeff 1 of the outer series)`.
* `coeff_pow_self_of_coeff_zero_eq_zero` : the leading-coefficient identity, `coeff n (b^n) = u^n`
  when `coeff 0 b = 0`, `coeff 1 b = u`.
* `subst_phi_eq_phi_subst` : **existence** — `f.subst φ = φ.subst g` for `φ := mk (phiCoeff hπ a hf
  hg)`, proved coefficient by coefficient via `PowerSeries.ext`, assembling the four facts above.
* `genTrunc`, `pi_mul_one_sub_pow_mul_coeff_of_subst_eq` : a non-recursive truncation of an
  arbitrary power series, and the recovery of `phiCoeff`'s local defining equation from *any*
  global solution — the converse direction of the existence argument, needed for uniqueness.
* `eq_of_coeff_zero_eq_zero_of_coeff_one_eq_of_subst_eq` : **uniqueness** — any two solutions with
  the same zero constant term and linear coefficient coincide, by strong induction cancelling the
  regular factor `π * (1 - π^(d+1))` at each step.

## What this does not yet do

Everything downstream of the functional equation lemma itself: specializing `L = X + Y`, `f = g` to
extract the formal group law `F_π`, and the theory built on top of it (isogenies, the reciprocity
map, etc.).
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
/-- **Truncation invariance, inner position.** If two
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
/-- **Truncation invariance, outer position** (the outer-position analogue of the inner-position
truncation invariance above). If two
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
/-- **The binomial correction identity** (the crux algebraic fact behind the linear-correction
identity below). For `A`
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
/-- **The linear-correction identity, in `finsum` form.** Assembling
`coeff_pow_add_C_mul_X_pow_sub_coeff_pow` termwise across `coeff_subst'`'s `finsum`: the
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
/-- **The leading coefficient of `b^n`.** For `b` with `coeff 0 b = 0` and
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

At `n = d + 2 ≥ 2`, the new coefficient solves the linear equation
`π · (1 - π^(d+1)) · c = coeff (d+2) (φ_d.subst g) - coeff (d+2)
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

@[simp] theorem phiPartialSum_zero (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g) :
    phiPartialSum hπ a hf hg 0 = 0 := by
  simp [phiPartialSum, phiState]

/-- **The coefficient-agreement invariant tying `phiPartialSum` to `phiCoeff`.** For every degree
`n`, the partial sum `phiPartialSum n` agrees with `phiCoeff` on coefficients `0, …, n`, and is
identically `0` beyond degree `n` — the latter is what lets the degree-`(d+2)` recursive step
(which only inspects `phiPartialSum (d+1)`, not the not-yet-defined `phiCoeff (d+2)`) still see
the correct value at every coefficient index. Proved by induction on `n` matching `phiState`'s own
recursion shape (`0`, `1`, `d + 2`). -/
theorem coeff_phiPartialSum (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    (n m : ℕ) :
    coeff m (phiPartialSum hπ a hf hg n) = if m ≤ n then phiCoeff hπ a hf hg m else 0 := by
  induction n with
  | zero =>
    rw [phiPartialSum_zero, map_zero]
    rcases m with _ | m
    · simp
    · simp
  | succ n ih =>
    rcases n with _ | d
    · rcases m with _ | _ | m
      · simp
      · simp
      · simp
    · rw [phiPartialSum_succ_succ, map_add, coeff_C_mul, coeff_X_pow]
      rcases Nat.lt_trichotomy m (d + 2) with hmd | hmd | hmd
      · rw [ih, if_pos (by omega : m ≤ d + 1), if_neg (by omega : m ≠ d + 2),
          if_pos (by omega : m ≤ d + 1 + 1)]
        ring
      · rw [ih, if_neg (by omega : ¬ m ≤ d + 1), if_pos hmd, if_pos (by omega : m ≤ d + 1 + 1), hmd]
        ring
      · rw [ih, if_neg (by omega : ¬ m ≤ d + 1), if_neg (by omega : m ≠ d + 2),
          if_neg (by omega : ¬ m ≤ d + 1 + 1)]
        ring

/-- The corollary of `coeff_phiPartialSum` used to invoke the two truncation-invariance lemmas: the
fully assembled `φ := PowerSeries.mk (phiCoeff hπ a hf hg)` and the degree-`n` partial sum agree on
coefficients `0, …, n`. -/
theorem X_pow_dvd_phi_sub_phiPartialSum (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    (n : ℕ) :
    (X : O⟦X⟧) ^ (n + 1) ∣
      (PowerSeries.mk (phiCoeff hπ a hf hg) - phiPartialSum hπ a hf hg n) := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, PowerSeries.coeff_mk, coeff_phiPartialSum, if_pos (by omega), sub_self]

/-- **The Lubin-Tate functional equation lemma, existence half.** The fully assembled power series
`φ := PowerSeries.mk (phiCoeff hπ a hf hg)` intertwines `f` and `g`: `f(φ(X)) = φ(g(X))`. Proved
coefficient by coefficient (`PowerSeries.ext`). Degrees `0` and `1` are direct (both series have
zero constant term; the linear coefficient is forced by truncating `φ` to its linear part
`phiPartialSum 1 = C a * X` via the outer/inner truncation-invariance lemmas). At degree `d + 2`,
combine: truncation invariance (`coeff_subst_eq_of_dvd_sub`/`_left`) replaces `φ` by
`phiPartialSum (d + 2) = phiPartialSum (d + 1) + C c * X^(d+2)` (`c := phiCoeff (d+2)`) on both
sides; the linear correction identity (`coeff_subst_add_C_mul_X_pow`) evaluates the inner-position
side exactly against `phiPartialSum (d+1)` plus a `c * coeff 1 f` term; the exact algebra-hom laws
(`subst_add`/`subst_mul`/`subst_C`/`subst_pow`/`subst_X`) together with the leading-coefficient
fact (`coeff_pow_self_of_coeff_zero_eq_zero`) evaluate the outer-position side exactly against
`phiPartialSum (d+1)` plus a `c * π^(d+2)` term; and the per-degree defining equation
(`pi_mul_one_sub_pow_mul_phiCoeff`) identifies the difference of the two `phiPartialSum (d+1)`
terms as exactly `π * (1 - π^(d+1)) * c`, which cancels the two correction terms
(`c * π^(d+2) - c * π = c * π * (π^(d+1) - 1) = -(π * (1 - π^(d+1)) * c)`) on the nose. -/
theorem subst_phi_eq_phi_subst (hπ : Irreducible π) (a : O)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g) :
    f.subst (PowerSeries.mk (phiCoeff hπ a hf hg)) =
      (PowerSeries.mk (phiCoeff hπ a hf hg)).subst g := by
  set φ := PowerSeries.mk (phiCoeff hπ a hf hg) with hφdef
  have hφ0 : constantCoeff φ = 0 := by
    rw [← coeff_zero_eq_constantCoeff, hφdef, PowerSeries.coeff_mk]
    exact phiCoeff_zero hπ a hf hg
  have hg0 : constantCoeff g = 0 := by rw [← coeff_zero_eq_constantCoeff]; exact hg.1
  have hf0 : constantCoeff f = 0 := by rw [← coeff_zero_eq_constantCoeff]; exact hf.1
  have hpartial0 : ∀ m, constantCoeff (phiPartialSum hπ a hf hg m) = 0 := fun m ↦ by
    rw [← coeff_zero_eq_constantCoeff]; exact coeff_zero_phiPartialSum hπ a hf hg m
  refine PowerSeries.ext fun n ↦ ?_
  match n with
  | 0 =>
    rw [coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_eq, PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst_eq_zero (a := φ) hφ0 f hf0,
      PowerSeries.constantCoeff_subst_eq_zero (a := g) hg0 φ hφ0]
  | 1 =>
    have hφ' : PowerSeries.HasSubst φ := HasSubst.of_constantCoeff_zero' hφ0
    have hp1 : PowerSeries.HasSubst (phiPartialSum hπ a hf hg 1) :=
      HasSubst.of_constantCoeff_zero' (hpartial0 1)
    have hdvd1 := X_pow_dvd_phi_sub_phiPartialSum hπ a hf hg 1
    have hstep1 : coeff 1 (f.subst φ) = coeff 1 (f.subst (phiPartialSum hπ a hf hg 1)) :=
      coeff_subst_eq_of_dvd_sub f hφ' hp1 1 hdvd1
    have hstep2 : coeff 1 (φ.subst g) = coeff 1 ((phiPartialSum hπ a hf hg 1).subst g) :=
      coeff_subst_eq_of_dvd_sub_left hg0 1 hdvd1
    rw [hstep1, hstep2, phiPartialSum_one]
    have ha : PowerSeries.HasSubst (PowerSeries.C a * X : O⟦X⟧) :=
      HasSubst.of_constantCoeff_zero' (by simp)
    have hleft : coeff 1 (f.subst (PowerSeries.C a * X)) = π * a := by
      rw [coeff_subst' ha, finsum_eq_single _ 1]
      · rw [pow_one, coeff_C_mul, coeff_X, if_pos rfl, mul_one, hf.2.1, smul_eq_mul]
      · intro d hd
        have : coeff 1 ((PowerSeries.C a * X : O⟦X⟧) ^ d) = 0 := by
          rw [mul_pow, ← map_pow, coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hd), mul_zero]
        rw [this, smul_zero]
    have hright : coeff 1 ((PowerSeries.C a * X : O⟦X⟧).subst g) = a * π := by
      have hg' : PowerSeries.HasSubst g := HasSubst.of_constantCoeff_zero' hg0
      rw [subst_mul hg', subst_C, ← C_apply, subst_X hg', coeff_C_mul, hg.2.1]
    rw [hleft, hright]; ring
  | d + 2 =>
    set A := phiPartialSum hπ a hf hg (d + 1) with hAdef
    set c := phiCoeff hπ a hf hg (d + 2) with hcdef
    have hA0 : constantCoeff A = 0 := hpartial0 (d + 1)
    have hAsucc : phiPartialSum hπ a hf hg (d + 2) = A + PowerSeries.C c * X ^ (d + 2) :=
      phiPartialSum_succ_succ hπ a hf hg d
    have hφ' : PowerSeries.HasSubst φ := HasSubst.of_constantCoeff_zero' hφ0
    have hp2 : PowerSeries.HasSubst (phiPartialSum hπ a hf hg (d + 2)) :=
      HasSubst.of_constantCoeff_zero' (hpartial0 (d + 2))
    have hdvd2 := X_pow_dvd_phi_sub_phiPartialSum hπ a hf hg (d + 2)
    -- inner-position side: coeff (d+2) (f.subst φ) = coeff (d+2) (f.subst A) + c * coeff 1 f
    have hstep1 : coeff (d + 2) (f.subst φ) =
        coeff (d + 2) (f.subst (phiPartialSum hπ a hf hg (d + 2))) :=
      coeff_subst_eq_of_dvd_sub f hφ' hp2 (d + 2) hdvd2
    have hinner : coeff (d + 2) (f.subst φ) = coeff (d + 2) (f.subst A) + c * coeff 1 f := by
      rw [hstep1, hAsucc, coeff_subst_add_C_mul_X_pow f hA0 c (by omega : 1 ≤ d + 2)]
    -- outer-position side: coeff (d+2) (φ.subst g) = coeff (d+2) (A.subst g) + c * π^(d+2)
    have hstep2 : coeff (d + 2) (φ.subst g) =
        coeff (d + 2) ((phiPartialSum hπ a hf hg (d + 2)).subst g) :=
      coeff_subst_eq_of_dvd_sub_left hg0 (d + 2) hdvd2
    have hg' : PowerSeries.HasSubst g := HasSubst.of_constantCoeff_zero' hg0
    have houter : coeff (d + 2) (φ.subst g) =
        coeff (d + 2) (A.subst g) + c * π ^ (d + 2) := by
      rw [hstep2, hAsucc, subst_add hg', map_add, subst_mul hg', subst_C, ← C_apply,
        subst_pow hg', subst_X hg', coeff_C_mul,
        coeff_pow_self_of_coeff_zero_eq_zero hg.1 hg.2.1 (d + 2)]
    -- combine with the per-degree defining equation
    have hkey := pi_mul_one_sub_pow_mul_phiCoeff hπ a hf hg d
    rw [hinner, houter, hf.2.1]
    have : coeff (d + 2) (A.subst g) - coeff (d + 2) (f.subst A) =
        π * (1 - π ^ (d + 1)) * c := hkey.symm
    linear_combination -this

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **A generic (non-recursive) truncation of an arbitrary power series**, used only for the
uniqueness argument: unlike `phiPartialSum`, which is tied to the specific recursively-constructed
`phiCoeff`, `genTrunc φ n` truncates *any* `φ` to its coefficients `0, …, n`. Defined directly via
`PowerSeries.mk` (not a `Finset.sum`, unlike Mathlib's `substInvFun`-style truncations) so that its
defining coefficient formula is immediate from `coeff_mk`. -/
noncomputable def genTrunc (φ : O⟦X⟧) (n : ℕ) : O⟦X⟧ :=
  PowerSeries.mk (fun m ↦ if m ≤ n then coeff m φ else 0)

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
theorem coeff_genTrunc (φ : O⟦X⟧) (n m : ℕ) :
    coeff m (genTrunc φ n) = if m ≤ n then coeff m φ else 0 :=
  PowerSeries.coeff_mk _ _

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
theorem constantCoeff_genTrunc (φ : O⟦X⟧) (hφ0 : coeff 0 φ = 0) (n : ℕ) :
    constantCoeff (genTrunc φ n) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_genTrunc, if_pos (Nat.zero_le n), hφ0]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
theorem X_pow_dvd_sub_genTrunc (φ : O⟦X⟧) (n : ℕ) :
    (X : O⟦X⟧) ^ (n + 1) ∣ (φ - genTrunc φ n) := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, coeff_genTrunc, if_pos (by omega), sub_self]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
theorem genTrunc_succ (φ : O⟦X⟧) (n : ℕ) :
    genTrunc φ (n + 1) = genTrunc φ n + PowerSeries.C (coeff (n + 1) φ) * X ^ (n + 1) := by
  refine PowerSeries.ext fun m ↦ ?_
  rw [map_add, coeff_genTrunc, coeff_C_mul, coeff_X_pow, coeff_genTrunc]
  rcases Nat.lt_trichotomy m (n + 1) with hmn | hmn | hmn
  · rw [if_pos (by omega : m ≤ n), if_neg (by omega : m ≠ n + 1), if_pos (by omega : m ≤ n + 1),
      mul_zero, add_zero]
  · rw [if_neg (by omega : ¬ m ≤ n), if_pos hmn, if_pos (by omega : m ≤ n + 1), zero_add,
      hmn, mul_one]
  · rw [if_neg (by omega : ¬ m ≤ n), if_neg (by omega : m ≠ n + 1), if_neg (by omega : ¬ m ≤ n + 1),
      mul_zero, add_zero]

omit [Finite (ResidueField O)] in
/-- **The local defining equation, recovered from an arbitrary global solution.** This is the
converse direction of the algebra used to prove `subst_phi_eq_phi_subst`: given *any* `φ` (not
necessarily `phiCoeff`-constructed) with zero constant term solving the *global* functional
equation `f.subst φ = φ.subst g`, its coefficients solve the *same* per-degree linear equation
`pi_mul_one_sub_pow_mul_phiCoeff` established for the recursively-constructed solution — obtained
by running exactly the same four facts (truncation invariance both ways, the linear correction,
and the leading-coefficient identity) against `genTrunc φ` in place of `phiPartialSum`, then
solving for the coefficient using the hypothesis `heq` instead of verifying it. This is the key
step that lets uniqueness be proved without any information about *how* a solution `φ` was
constructed. -/
theorem pi_mul_one_sub_pow_mul_coeff_of_subst_eq
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    {φ : O⟦X⟧} (hφ0 : coeff 0 φ = 0) (heq : f.subst φ = φ.subst g) (d : ℕ) :
    π * (1 - π ^ (d + 1)) * coeff (d + 2) φ =
      coeff (d + 2) ((genTrunc φ (d + 1)).subst g) - coeff (d + 2) (f.subst (genTrunc φ (d + 1))) := by
  have hφ0' : constantCoeff φ = 0 := by rw [← coeff_zero_eq_constantCoeff]; exact hφ0
  have hg0 : constantCoeff g = 0 := by rw [← coeff_zero_eq_constantCoeff]; exact hg.1
  set A := genTrunc φ (d + 1) with hAdef
  set c := coeff (d + 2) φ with hcdef
  have hA0 : constantCoeff A = 0 := constantCoeff_genTrunc φ hφ0 (d + 1)
  have hAsucc : genTrunc φ (d + 2) = A + PowerSeries.C c * X ^ (d + 2) := genTrunc_succ φ (d + 1)
  have hφ' : PowerSeries.HasSubst φ := HasSubst.of_constantCoeff_zero' hφ0'
  have hp2 : PowerSeries.HasSubst (genTrunc φ (d + 2)) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_genTrunc φ hφ0 (d + 2))
  have hdvd2 := X_pow_dvd_sub_genTrunc φ (d + 2)
  have hstep1 : coeff (d + 2) (f.subst φ) = coeff (d + 2) (f.subst (genTrunc φ (d + 2))) :=
    coeff_subst_eq_of_dvd_sub f hφ' hp2 (d + 2) hdvd2
  have hinner : coeff (d + 2) (f.subst φ) = coeff (d + 2) (f.subst A) + c * coeff 1 f := by
    rw [hstep1, hAsucc, coeff_subst_add_C_mul_X_pow f hA0 c (by omega : 1 ≤ d + 2)]
  have hstep2 : coeff (d + 2) (φ.subst g) = coeff (d + 2) ((genTrunc φ (d + 2)).subst g) :=
    coeff_subst_eq_of_dvd_sub_left hg0 (d + 2) hdvd2
  have hg' : PowerSeries.HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  have houter : coeff (d + 2) (φ.subst g) = coeff (d + 2) (A.subst g) + c * π ^ (d + 2) := by
    rw [hstep2, hAsucc, subst_add hg', map_add, subst_mul hg', subst_C, ← C_apply,
      subst_pow hg', subst_X hg', coeff_C_mul,
      coeff_pow_self_of_coeff_zero_eq_zero hg.1 hg.2.1 (d + 2)]
  have hcoeff_eq : coeff (d + 2) (f.subst φ) = coeff (d + 2) (φ.subst g) := by rw [heq]
  rw [hinner, houter, hf.2.1] at hcoeff_eq
  linear_combination hcoeff_eq

omit [Finite (ResidueField O)] in
/-- **The Lubin-Tate functional equation lemma, uniqueness half** (alongside
`subst_phi_eq_phi_subst`, the existence half). Any two power series with zero constant term,
linear coefficient `a`,
and both solving `f.subst _ = _.subst g` must coincide: their coefficients agree by strong
induction on the degree, using `pi_mul_one_sub_pow_mul_coeff_of_subst_eq` to see that both
coefficient sequences solve the *same* linear equation at every step once their truncations agree
(the truncations `genTrunc φ (d+1)`/`genTrunc ψ (d+1)` are literally equal once the coefficients
below degree `d + 2` are known to agree, by the induction hypothesis and `PowerSeries.ext`), and
cancelling the shared unit-times-`π` factor `π * (1 - π^(d+1))` — regular in the domain `O` since
`π ≠ 0` (irreducible) and `1 - π^(d+1)` is a unit. -/
theorem eq_of_coeff_zero_eq_zero_of_coeff_one_eq_of_subst_eq (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    {φ ψ : O⟦X⟧} (a : O) (hφ0 : coeff 0 φ = 0) (hφ1 : coeff 1 φ = a)
    (heqφ : f.subst φ = φ.subst g) (hψ0 : coeff 0 ψ = 0) (hψ1 : coeff 1 ψ = a)
    (heqψ : f.subst ψ = ψ.subst g) : φ = ψ := by
  refine PowerSeries.ext fun n ↦ ?_
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [hφ0, hψ0]
    | 1 => rw [hφ1, hψ1]
    | d + 2 =>
      have htrunc : genTrunc φ (d + 1) = genTrunc ψ (d + 1) := by
        refine PowerSeries.ext fun m ↦ ?_
        rw [coeff_genTrunc, coeff_genTrunc]
        split_ifs with hmle
        · exact ih m (by omega)
        · rfl
      have heφ := pi_mul_one_sub_pow_mul_coeff_of_subst_eq hf hg hφ0 heqφ d
      have heψ := pi_mul_one_sub_pow_mul_coeff_of_subst_eq hf hg hψ0 heqψ d
      rw [htrunc] at heφ
      have hval : π * (1 - π ^ (d + 1)) * coeff (d + 2) φ =
          π * (1 - π ^ (d + 1)) * coeff (d + 2) ψ := heφ.trans heψ.symm
      have hunit : IsUnit (1 - π ^ (d + 1)) :=
        isUnit_one_sub_self_of_mem_nonunits _
          ((mem_maximalIdeal _).mp (Ideal.pow_mem_of_mem (maximalIdeal O) ((mem_maximalIdeal π).mpr
            hπ.not_isUnit) (d + 1) (by omega)))
      have hπne : π ≠ 0 := hπ.ne_zero
      have hfactorne : π * (1 - π ^ (d + 1)) ≠ 0 := mul_ne_zero hπne hunit.ne_zero
      exact mul_left_cancel₀ hfactorne hval

end LubinTate

end
