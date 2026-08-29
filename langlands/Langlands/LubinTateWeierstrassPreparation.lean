import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Langlands.LubinTate
import Langlands.NonarchimedeanPowerSeriesEval

/-!
# Weierstrass preparation for Lubin-Tate power series

Weierstrass preparation turns `f` (a Lubin-Tate power series, an *infinite* object) into a
genuine degree-`q` polynomial with the same roots, so that root-counting toward
`|piTorsion hπ hf 1| = q` becomes a finite/algebraic question. Mathlib's
`Mathlib.RingTheory.PowerSeries.WeierstrassPreparation` (Jz Pan, 2025) already
proves the general Weierstrass preparation theorem for power series over a complete local ring, in
full generality with existence *and* uniqueness. This file does not re-derive that theorem; it specializes Mathlib's
statement to the Lubin-Tate setting, checking the two hypotheses (`g`'s residue-field image nonzero,
and `O` adically complete) hold for `f`.

## Route

`IsLubinTatePoly π q f`'s third congruence, `f.map (residue O) = X ^ q` *exactly* (not just the
low-degree congruence used to define `q` classically), gives both of Mathlib's needed inputs at
once:

* `X ^ q ≠ 0` in `(ResidueField O)⟦X⟧` (any field is nontrivial), so `f.map (residue O) ≠ 0`
  (`map_residue_ne_zero`) — Mathlib's nonvanishing hypothesis.
* `(f.map (residue O)).order = q` follows from `PowerSeries.order_X_pow` rewritten along the same
  congruence (`order_map_residue_eq`), identifying the *order* used internally by Mathlib's
  `PowerSeries.IsWeierstrassDivisorAt`/`exists_isWeierstrassFactorization` with the residue-field
  size `q` directly, rather than needing to discover it.

Mathlib's `PowerSeries.exists_isWeierstrassFactorization` additionally needs `O` to be adically
complete with respect to its maximal ideal (`IsAdicComplete (IsLocalRing.maximalIdeal O) O`) — the
literal formalization of "complete DVR", the standing hypothesis of classical Lubin-Tate theory. It
is added here as a new typeclass assumption on `O`, matching what the classical theory requires —
not a narrowing of scope, but a hypothesis genuinely used by the argument.

## Main result

* `exists_isWeierstrassFactorization_of_isLubinTatePoly`: for `f` a Lubin-Tate power series (`hf :
  IsLubinTatePoly π (residueCard O) f`) over an adically-complete `O`, there is a distinguished
  polynomial `P : O[X]` of degree exactly `residueCard O` and a unit power series `u : O⟦X⟧` with
  `f = P * u`.

* `norm_eval_eq_one_of_isUnit`/`eval_ne_zero_of_isUnit`: the unit factor `u` of any Weierstrass
  factorization evaluates, at any point of `K`'s maximal ideal, to something of norm exactly `1` —
  in particular never `0`. Built from a new general lemma
  `NonarchimedeanPowerSeriesEval.norm_eval_sub_algebraMap_constantCoeff_le` (`eval f x` lies within
  `‖x‖` of `f`'s constant term, algebra-mapped into `K` — the general form of the existing
  `norm_eval_le`, which is its `constantCoeff f = 0` case) plus the ultrametric "isosceles
  triangle" law: a unit's algebra-mapped constant term has norm exactly `1`
  (`norm_algebraMap_eq_one_of_isUnit`), strictly greater than the `< 1` distance `eval u x` can
  have moved from it, so `‖eval u x‖` is forced to equal that `1`.

* `coeff_zero_eq_zero_of_eq_mul`/`coeff_one_associated_of_eq_mul`: `P`'s constant coefficient is
  exactly `0` (not merely in the maximal ideal), and `P`'s linear coefficient is an *associate* of
  `π` — valuation exactly `1`, not merely `≥ 1`. Both come from comparing `f`'s own defining
  congruences against `f = (P : O⟦X⟧) * u` at degrees `0` and `1`, using that `u`'s constant term is
  a unit. This is the sharp Newton-polygon-style input a separability argument for `P` needs, beyond
  what `IsDistinguishedAt`/Eisenstein alone supplies.

## What this does not do

**`piTorsion hπ hf 1` is now identified with `P`'s zero set** — see
`Langlands.LubinTate.eval_eq_zero_iff_aeval_eq_zero` (this file) and
`Langlands.LubinTate.exists_piTorsion_one_eq_aeval_roots`
(`Langlands/LubinTateTorsionPoints.lean`): `piTorsion hπ hf 1 = {x | ‖x‖ < 1 ∧ Polynomial.aeval x
P = 0}`. What remains toward `|piTorsion hπ hf 1| = q` is root-counting, and it splits into two
genuinely separate gaps:

1. **Separability of `P` is not established, and `P` itself is *not* irreducible** (so no Eisenstein
   irreducibility criterion applies to `P` directly): `coeff_zero_eq_zero_of_eq_mul` shows `P`'s
   constant term is exactly `0`, i.e. `X ∣ P`, so `P = X * Q` for `Q : O[X]` of degree `q - 1` — the
   root `0` (`zero_mem_piTorsion`) accounts for one of `P`'s `q` roots, and it is `Q`,
   not `P`, that is the genuine Eisenstein polynomial the classical argument needs: `Q`'s own
   constant term is `Q.coeff 0 = P.coeff 1` (shifting indices by the `X` factor), an associate of `π`
   (`coeff_one_associated_of_eq_mul`) — valuation exactly `1`, the sharp non-`P²`-membership Mathlib's
   `Polynomial.irreducible_of_eisenstein_criterion` needs and `IsDistinguishedAt`/
   `IsWeaklyEisensteinAt` alone do not supply (`Q`'s own `IsDistinguishedAt`/`IsWeaklyEisensteinAt`
   status has not been checked here, only the underlying valuation fact it would need). The
   classical separability argument itself
   (Serre, *Local Fields* Ch. IV; Washington, Thm 7.3) is a Newton-polygon computation on `Q`: every
   root has valuation exactly `1/(q-1)`, then a formal-derivative valuation comparison shows
   `Q'(α) ≠ 0` at every root. Mathlib has no Newton polygon file and no "valuation of roots of an
   Eisenstein polynomial" lemma; `Mathlib/RingTheory/Polynomial/Eisenstein/{Basic,Criterion,
   Distinguished,IsIntegral}.lean` cover irreducibility and integral-closure facts only, not root
   valuations. Building the valuation-of-roots machinery — extending `O`'s valuation to a field
   containing `Q`'s roots, an ultrametric argument bounding each root's norm from both sides, then
   the derivative estimate — is a separate multi-lemma development, not a one-off consequence of
   Weierstrass preparation.
2. **`K` is not assumed to contain `P`'s roots**, and the statement is false without such a
   hypothesis: `piTorsion`/this file's `K` carries only `NormedField`/`IsUltrametricDist`/
   `CompleteSpace`/`[Algebra O K]` — for `K` the base field itself, `piTorsion hπ hf 1 = {0}` (size
   `1`, not `q`). Closing this needs `K ⊇ K_1` (the field extension the Lubin-Tate tower is
   building toward) or `[IsAlgClosed K]`.

Neither gap is closed here; `coeff_zero_eq_zero_of_eq_mul` and `coeff_one_associated_of_eq_mul` give
the sharp linear-coefficient valuation fact gap 1's argument needs as its base case.

## References

* Mathlib, `Mathlib.RingTheory.PowerSeries.WeierstrassPreparation` (Jz Pan, 2025).
* J. Lubin, J. Tate, *Formal complex multiplication in local fields*, Ann. of Math. 81 (1965).
* J-P. Serre, *Local Fields*, Ch. IV.
* Washington, *Introduction to Cyclotomic Fields*, Proposition 7.2 / Theorem 7.3.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

open PowerSeries IsLocalRing

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {π : O} {f : O⟦X⟧}

omit [Finite (ResidueField O)] in
/-- **`f`'s image in the residue field is nonzero.** Immediate from the defining congruence
`f.map (residue O) = X ^ q` (`IsLubinTatePoly`'s third condition): `X ^ q ≠ 0` since `ResidueField
O`, being a field, is nontrivial. -/
theorem map_residue_ne_zero (hf : IsLubinTatePoly π (residueCard O) f) :
    PowerSeries.map (residue O) f ≠ 0 := by
  rw [hf.2.2]
  exact pow_ne_zero _ PowerSeries.X_ne_zero

omit [Finite (ResidueField O)] in
/-- **The order of `f`'s residue-field image is exactly `q := residueCard O`.** Immediate from the
defining congruence together with `PowerSeries.order_X_pow`. This identifies the degree Mathlib's
Weierstrass preparation theorem produces with `q` directly, without needing to discover it from a
weaker (only-low-degree) congruence. -/
theorem order_map_residue_eq (hf : IsLubinTatePoly π (residueCard O) f) :
    (PowerSeries.map (residue O) f).order = (residueCard O : ℕ∞) := by
  rw [hf.2.2, PowerSeries.order_X_pow]

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

omit [Finite (ResidueField O)] in
/-- **Weierstrass preparation for a Lubin-Tate power series.** `f = P * u`, `P : O[X]` a
distinguished polynomial (monic, all lower coefficients in the maximal ideal) of degree exactly
`q := residueCard O`, `u : O⟦X⟧` a unit power series. Specializes Mathlib's
`PowerSeries.exists_isWeierstrassFactorization` via `map_residue_ne_zero`/`order_map_residue_eq`. -/
theorem exists_isWeierstrassFactorization_of_isLubinTatePoly
    (hf : IsLubinTatePoly π (residueCard O) f) :
    ∃ (P : O[X]) (u : O⟦X⟧), P.IsDistinguishedAt (IsLocalRing.maximalIdeal O) ∧ IsUnit u ∧
      f = (P : O⟦X⟧) * u ∧ P.natDegree = residueCard O := by
  obtain ⟨P, u, hPu⟩ := PowerSeries.exists_isWeierstrassFactorization (map_residue_ne_zero hf)
  refine ⟨P, u, hPu.isDistinguishedAt, hPu.isUnit, hPu.eq_mul, ?_⟩
  rw [hPu.natDegree_eq_toNat_order_map, order_map_residue_eq hf]
  rfl

/-! ## The Weierstrass factor `P`'s own low-degree coefficients

Toward separability of `P` (the remaining gap above): `P`'s constant coefficient is not merely
in the maximal ideal (as `IsDistinguishedAt` already gives) but *exactly* `0`, and `P`'s linear
coefficient is not merely in the maximal ideal but an *associate of `π` itself* — i.e. a
uniformizer, valuation exactly `1`. Both facts come from comparing `f`'s own defining congruences
(`coeff 0 f = 0`, `coeff 1 f = π`) against the factorization `f = (P : O⟦X⟧) * u` at degrees `0`
and `1`, using that `u`'s constant coefficient is a unit. -/

omit [Finite (ResidueField O)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- **`P`'s constant coefficient is exactly `0`.** `f`'s constant coefficient is `0`
(`IsLubinTatePoly`'s first congruence) and equals `P.coeff 0 * constantCoeff u`
(`PowerSeries.constantCoeff` is a ring homomorphism, applied to `f = (P : O⟦X⟧) * u`); since `u`'s
constant coefficient is a unit (`PowerSeries.isUnit_constantCoeff`), in particular nonzero (`O` a
domain), the domain cancels it. -/
theorem coeff_zero_eq_zero_of_eq_mul {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) {f : O⟦X⟧}
    (heq : f = (P : O⟦X⟧) * u) (hf0 : PowerSeries.coeff 0 f = 0) : P.coeff 0 = 0 := by
  have hmul : PowerSeries.constantCoeff f =
      P.coeff 0 * PowerSeries.constantCoeff u := by
    rw [heq, map_mul, Polynomial.constantCoeff_coe]
  rw [PowerSeries.coeff_zero_eq_constantCoeff] at hf0
  rw [hf0] at hmul
  exact (mul_eq_zero.mp hmul.symm).resolve_right
    (PowerSeries.isUnit_constantCoeff u hu).ne_zero

omit [Finite (ResidueField O)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- **`P`'s linear coefficient is an associate of `π`.** `f`'s linear coefficient is `π`
(`IsLubinTatePoly`'s second congruence) and equals `P.coeff 0 * coeff 1 u + P.coeff 1 * coeff 0 u`
(`PowerSeries.coeff_mul` at `n = 1`, `Finset.antidiagonal 1 = {(0, 1), (1, 0)}`); since
`P.coeff 0 = 0` (`coeff_zero_eq_zero_of_eq_mul`), this collapses to
`P.coeff 1 * constantCoeff u = π`, exhibiting `P.coeff 1 = π * (constantCoeff u)⁻¹` as an
associate of `π` (`constantCoeff u` a unit). In a discrete valuation ring this is exactly
"valuation `1`", the sharp input a Newton-polygon-style separability argument for `P` needs (as
opposed to the weaker "valuation `≥ 1`" that `IsDistinguishedAt`/Eisenstein alone supplies). -/
theorem coeff_one_associated_of_eq_mul {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) {f : O⟦X⟧}
    (heq : f = (P : O⟦X⟧) * u) (hf0 : PowerSeries.coeff 0 f = 0) (hf1 : PowerSeries.coeff 1 f = π) :
    Associated (P.coeff 1) π := by
  have hP0 : P.coeff 0 = 0 := coeff_zero_eq_zero_of_eq_mul hu heq hf0
  have hanti : Finset.antidiagonal 1 = {((0 : ℕ), (1 : ℕ)), (1, 0)} := rfl
  have hmul : PowerSeries.coeff 1 f =
      P.coeff 0 * PowerSeries.coeff 1 u + P.coeff 1 * PowerSeries.coeff 0 u := by
    rw [heq, PowerSeries.coeff_mul, hanti]
    simp [Polynomial.coeff_coe]
  rw [hP0, zero_mul, zero_add, hf1, PowerSeries.coeff_zero_eq_constantCoeff] at hmul
  refine ⟨(PowerSeries.isUnit_constantCoeff u hu).unit, ?_⟩
  rw [IsUnit.unit_spec]
  exact hmul.symm

/-! ## Toward `piTorsion`: the unit factor never vanishes on the maximal ideal -/

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsUltrametricDist K] [CompleteSpace K] in
/-- **A unit of `O`, algebra-mapped into `K`, has norm exactly `1`**, given `O`'s image lies in
`K`'s closed unit ball. Both `a` and `a⁻¹` map with norm `≤ 1` (`hOK`), and their product maps to
`1`; the two bounds force equality. Same argument as
`Langlands.PrincipalUnitsSuccessiveApproximation.norm_approxUnit_eq_one`, specialized from
`Oˣ`-valued limits down to a single element. -/
theorem norm_algebraMap_eq_one_of_isUnit (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {a : O}
    (ha : IsUnit a) : ‖algebraMap O K a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have h1 : ‖algebraMap O K (u : O)‖ ≤ 1 := hOK _
  have h2 : ‖algebraMap O K ((u⁻¹ : Oˣ) : O)‖ ≤ 1 := hOK _
  have hmul : algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul]
    simp
  have h3 : (1 : ℝ) ≤ ‖algebraMap O K (u : O)‖ := by
    calc (1 : ℝ) = ‖(1 : K)‖ := norm_one.symm
      _ = ‖algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O)‖ := by rw [hmul]
      _ = ‖algebraMap O K (u : O)‖ * ‖algebraMap O K ((u⁻¹ : Oˣ) : O)‖ := norm_mul _ _
      _ ≤ ‖algebraMap O K (u : O)‖ * 1 := by gcongr
      _ = ‖algebraMap O K (u : O)‖ := mul_one _
  exact le_antisymm h1 h3

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- **The unit factor `u` of a Weierstrass factorization never vanishes under evaluation on the
maximal ideal.** `eval u x` lies within `‖x‖ < 1` of `algebraMap O K (constantCoeff u)`
(`NonarchimedeanPowerSeriesEval.norm_eval_sub_algebraMap_constantCoeff_le`), which itself has norm
exactly `1` (`norm_algebraMap_eq_one_of_isUnit`, since `u` a unit of `O⟦X⟧` forces `constantCoeff u`
to be a unit of `O`, `PowerSeries.isUnit_constantCoeff`); the ultrametric "isosceles triangle" law
(`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`) then forces `‖eval u x‖` to be exactly `1` as
well, in particular nonzero. -/
theorem norm_eval_eq_one_of_isUnit (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {u : O⟦X⟧}
    (hu : IsUnit u) {x : K} (hx : ‖x‖ < 1) :
    ‖NonarchimedeanPowerSeriesEval.eval u x‖ = 1 := by
  have hcoeffs : ∀ n, ‖algebraMap O K (PowerSeries.coeff n u)‖ ≤ 1 := fun n ↦ hOK _
  have hconst : ‖algebraMap O K (PowerSeries.constantCoeff u)‖ = 1 :=
    norm_algebraMap_eq_one_of_isUnit hOK (PowerSeries.isUnit_constantCoeff u hu)
  have hclose : ‖NonarchimedeanPowerSeriesEval.eval u x -
      algebraMap O K (PowerSeries.constantCoeff u)‖ ≤ ‖x‖ :=
    NonarchimedeanPowerSeriesEval.norm_eval_sub_algebraMap_constantCoeff_le hcoeffs hx
  have hne : ‖algebraMap O K (PowerSeries.constantCoeff u)‖ ≠
      ‖NonarchimedeanPowerSeriesEval.eval u x -
        algebraMap O K (PowerSeries.constantCoeff u)‖ := by
    rw [hconst]
    exact (lt_of_le_of_lt hclose hx).ne'
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rwa [add_sub_cancel, hconst, max_eq_left (lt_of_le_of_lt hclose hx).le] at this

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem eval_ne_zero_of_isUnit (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {u : O⟦X⟧}
    (hu : IsUnit u) {x : K} (hx : ‖x‖ < 1) : NonarchimedeanPowerSeriesEval.eval u x ≠ 0 := by
  intro h
  have := norm_eval_eq_one_of_isUnit hOK hu hx
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

/-! ## The zero set of `f` on the maximal ideal is exactly the zero set of `P` -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- **`eval f x = 0 ↔ Polynomial.aeval x P = 0`, for `x` in the maximal ideal.** Given a
Weierstrass factorization `f = (P : O⟦X⟧) * u` with `u` a unit: `eval f x = eval P x * eval u x`
(`NonarchimedeanPowerSeriesEval.eval_mul`, both factors' coefficients bounded by `hOK`), `eval P x`
is identified with `Polynomial.aeval x P`
(`NonarchimedeanPowerSeriesEval.eval_coe_eq_aeval`), and `eval u x ≠ 0`
(`eval_ne_zero_of_isUnit`, this file's previous result) lets a product vanish only through its
first factor. -/
theorem eval_eq_zero_iff_aeval_eq_zero (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {P : O[X]}
    {u : O⟦X⟧} (hu : IsUnit u) {f : O⟦X⟧} (heq : f = (P : O⟦X⟧) * u) {x : K} (hx : ‖x‖ < 1) :
    NonarchimedeanPowerSeriesEval.eval f x = 0 ↔ Polynomial.aeval x P = 0 := by
  have hPcoeff : ∀ n, ‖algebraMap O K (PowerSeries.coeff n (P : O⟦X⟧))‖ ≤ 1 := fun n ↦ hOK _
  have hucoeff : ∀ n, ‖algebraMap O K (PowerSeries.coeff n u)‖ ≤ 1 := fun n ↦ hOK _
  rw [heq, NonarchimedeanPowerSeriesEval.eval_mul hPcoeff hucoeff hx,
    NonarchimedeanPowerSeriesEval.eval_coe_eq_aeval, mul_eq_zero,
    or_iff_left (eval_ne_zero_of_isUnit hOK hu hx)]

end LubinTate

end
