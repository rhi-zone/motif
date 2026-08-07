import Langlands.TotallyRamifiedNormIndex

/-!
# A concrete totally, tamely ramified extension: `k(Y) / k(Y^e)`

Closes the gap flagged in `ROADMAP.md`: nowhere in this repository is there a concrete instance
of `R S K L v w` satisfying `IsDedekindDomain.HeightOneSpectrum.IsTotallyRamified`. This file
builds one, entirely algebraically (no Eisenstein polynomials, no actual number fields), as the
function-field analogue of `ℚ_p(p^{1/e}) / ℚ_p`.

## The construction

* `k := ZMod p` for a fixed prime `p` (a finite field, so residue fields below are finite).
* `R := Polynomial k` (variable "`X`"), a PID hence a Dedekind domain; `K := FractionRing R`.
* `S`, a type synonym of `Polynomial k` (variable "`Y`"), kept as a genuinely distinct type from
  `R` (via a one-field wrapper structure, transporting `CommRing`/domain/PID structure across the
  equivalence `S ≃ Polynomial k`) so that the custom `Algebra R S` instance below does not collide
  with the global `Algebra.id R` diamond that would arise if `S` were `R` itself.
* The algebra map `R →+* S` sends `X ↦ Y ^ e` (via `Polynomial.aeval`/`eval₂`, transported across
  the wrapper), for a fixed `e ≥ 2` coprime to `p`. `L := FractionRing S`.
* `v : HeightOneSpectrum R` at `(X)`, `w : HeightOneSpectrum S` at `(Y)`.

This is tractable because the ramification data is definitional: `Ideal.map (algebraMap R S)
(span {X}) = span {Y ^ e} = (span {Y}) ^ e` by construction, not an Eisenstein-criterion argument.

-/

noncomputable section

open IsDedekindDomain IsLocalRing Polynomial

namespace Langlands.TotallyRamifiedConcreteExample

/-! ### The base field and ramification data -/

/-- The residue characteristic: a fixed odd prime, `7`. -/
abbrev p : ℕ := 7

instance : Fact (Nat.Prime p) := ⟨by decide⟩

/-- The residue field `k := ZMod p`, finite of order `p`. -/
abbrev k : Type := ZMod p

/-- The ramification index, coprime to `p` (so the extension will be tamely ramified). -/
abbrev e : ℕ := 3

theorem e_pos : 0 < e := by norm_num

theorem coprime_e_p : Nat.Coprime e p := by decide

/-! ### `R := k[X]` and `K := Frac(R)` -/

/-- `R := k[X]`. -/
abbrev R : Type := Polynomial k

instance : IsDedekindDomain R := IsPrincipalIdealRing.isDedekindDomain R

/-- `K := Frac(R)`. -/
abbrev K : Type := FractionRing R

/-! ### `S`, a type synonym of `k[Y]` distinct from `R` -/

/-- `S`, a one-field wrapper around `k[Y]` — a genuinely distinct type from `R := k[X]`, needed so
that the custom `Algebra R S` instance defined below does not collide with the global `Algebra.id`
diamond that would arise from `R = S` literally. -/
structure S : Type where
  /-- The underlying polynomial in `Y`. -/
  toPoly : Polynomial k

namespace S

/-- The identification `S ≃ k[Y]`. -/
def equivPoly : S ≃ Polynomial k := ⟨toPoly, S.mk, fun _ => rfl, fun _ => rfl⟩

instance : CommRing S := equivPoly.commRing

/-- `S` is ring-isomorphic to `k[Y]`. -/
def ringEquivPoly : S ≃+* Polynomial k := equivPoly.ringEquiv

instance : IsDomain S :=
  Function.Injective.isDomain ringEquivPoly.toRingHom ringEquivPoly.injective

instance : IsPrincipalIdealRing S where
  principal I := by
    obtain ⟨g, hg⟩ :=
      (IsPrincipalIdealRing.principal (Ideal.map ringEquivPoly.toRingHom I)).principal
    refine ⟨ringEquivPoly.symm g, ?_⟩
    have hmap : Ideal.map ringEquivPoly.symm.toRingHom (Ideal.map ringEquivPoly.toRingHom I) = I := by
      rw [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id]
    rw [← hmap, hg, Ideal.map_span]
    simp

instance : IsDedekindDomain S := IsPrincipalIdealRing.isDedekindDomain S

end S

/-- `L := Frac(S)`. -/
abbrev L : Type := FractionRing S

/-! ### The algebra map `R →+* S`, `X ↦ Y ^ e` -/

/-- The ring hom `R →+* S`, `X ↦ Y ^ e`: `Polynomial.expand k e` (`X ↦ X ^ e` on `k[Y]`) composed
with the identification `S ≃+* k[Y]`. -/
def algMapRS : R →+* S :=
  S.ringEquivPoly.symm.toRingHom.comp (Polynomial.expand k e).toRingHom

theorem algMapRS_injective : Function.Injective algMapRS :=
  S.ringEquivPoly.symm.injective.comp (Polynomial.expand_injective e_pos)

theorem algMapRS_X : algMapRS (Polynomial.X : R) = S.ringEquivPoly.symm (Polynomial.X ^ e) := by
  show S.ringEquivPoly.symm (Polynomial.expand k e Polynomial.X) = _
  rw [Polynomial.expand_X]

instance : Algebra R S := algMapRS.toAlgebra

theorem algebraMap_R_S_eq : algebraMap R S = algMapRS := rfl

/-- `Y : S`, the image of `k[Y]`'s `X` under the identification `S ≃+* k[Y]`. -/
def Y : S := S.ringEquivPoly.symm Polynomial.X

theorem Y_eq : Y = S.ringEquivPoly.symm Polynomial.X := rfl

theorem algebraMap_X_eq : algebraMap R S (Polynomial.X : R) = Y ^ e := by
  rw [algebraMap_R_S_eq, algMapRS_X, Y_eq, map_pow]

/-! ### `K →+* L`, hence `Algebra K L` -/

/-- `K := Frac(R) →+* L := Frac(S)`, extending `algMapRS`. -/
def algMapKL : K →+* L := IsFractionRing.map algMapRS_injective

instance : Algebra K L := algMapKL.toAlgebra

theorem algMapKL_hy : nonZeroDivisors R ≤ Submonoid.comap algMapRS (nonZeroDivisors S) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective algMapRS algMapRS_injective

instance : IsScalarTower R K L := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [IsScalarTower.algebraMap_eq R S L, RingHom.comp_apply, algebraMap_R_S_eq]
  exact (IsLocalization.map_eq algMapKL_hy x).symm

/-! ### `v : HeightOneSpectrum R` at `(X)`, `w : HeightOneSpectrum S` at `(Y)` -/

/-- `v`, the place of `R = k[X]` at `X`. -/
def v : HeightOneSpectrum R where
  asIdeal := Ideal.span {Polynomial.X}
  isPrime := (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  ne_bot := by simpa using Polynomial.X_ne_zero (R := k)

/-- `w`, the place of `S = k[Y]` at `Y`. -/
def w : HeightOneSpectrum S where
  asIdeal := Ideal.span {Y}
  isPrime := (Ideal.span_singleton_prime (by rw [Y_eq]; simpa using Polynomial.X_ne_zero (R := k))).mpr
    (Y_eq ▸ (MulEquiv.prime_iff S.ringEquivPoly.symm).mpr Polynomial.prime_X)
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot, Y_eq]
    simpa using Polynomial.X_ne_zero (R := k)

/-- **The ramification is definitional**: `algebraMap R S` sends `(X)` to `(Y) ^ e`. -/
theorem map_v_eq : Ideal.map algMapRS v.asIdeal = w.asIdeal ^ e := by
  show Ideal.map algMapRS (Ideal.span {Polynomial.X}) = (Ideal.span {Y}) ^ e
  rw [Ideal.map_span, Set.image_singleton, algMapRS_X, Ideal.span_singleton_pow, Y_eq, map_pow]

/-- **`w` lies over `v`.** Since `algebraMap R S` maps `v.asIdeal` into `w.asIdeal ^ e ⊆ w.asIdeal`
and `v.asIdeal` is maximal, `Ideal.comap (algebraMap R S) w.asIdeal` (a proper ideal containing
`v.asIdeal`) must equal `v.asIdeal`. -/
instance : w.asIdeal.LiesOver v.asIdeal := by
  refine ⟨v.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) ?_⟩
  rw [← Ideal.map_le_iff_le_comap, algebraMap_R_S_eq, map_v_eq]
  exact Ideal.pow_le_self e_pos.ne'

end Langlands.TotallyRamifiedConcreteExample

end
