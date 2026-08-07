import Langlands.AdicCompletionIntegersResidue
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

instance : DecidableEq S := Classical.decEq S

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

/-! ### `S` is free of rank `e` over `R`, via the basis `{1, Y, …, Y ^ (e - 1)}`

`S = k[Y]` decomposes over `R = k[X]` (acting via `X ↦ Y ^ e`) exactly as `k[Y]` decomposes over
its degree-`e` "Veronese" subring `k[Y ^ e]`: writing a monomial's exponent `n = e * (n / e) + n %
e`, `C c * Y ^ n = algebraMap R S (C c * X ^ (n / e)) * Y ^ (n % e)`, an `R`-multiple of one of the
`e` basis elements. Induction on `natDegree` (via `Polynomial.eraseLead`) then spans all of `S`. -/

/-- The key algebraic identity: a monomial of `S = k[Y]`, split via division of its exponent by
`e`, is an `R`-multiple of `Y ^ (n % e)`. -/
theorem algebraMap_mul_Y_pow_eq (c : k) (n : ℕ) :
    algebraMap R S (Polynomial.C c * Polynomial.X ^ (n / e)) * Y ^ (n % e) =
      S.ringEquivPoly.symm (Polynomial.C c * Polynomial.X ^ n) := by
  have hexpand : algebraMap R S (Polynomial.C c * Polynomial.X ^ (n / e)) =
      S.ringEquivPoly.symm (Polynomial.expand k e (Polynomial.C c * Polynomial.X ^ (n / e))) := rfl
  rw [hexpand, Y_eq, ← map_pow, ← map_mul, map_mul (Polynomial.expand k e), Polynomial.expand_C,
    map_pow, Polynomial.expand_X, ← pow_mul, mul_assoc, ← pow_add, Nat.div_add_mod]

/-- The finite spanning set `{Y ^ i : i < e}`, as a `Finset S`. -/
def basisFinset : Finset S := (Finset.range e).image (Y ^ ·)

theorem mem_span_basisFinset (p : Polynomial k) :
    S.ringEquivPoly.symm p ∈ Submodule.span R (basisFinset : Set S) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    rcases eq_or_ne p 0 with rfl | hp0
    · simp only [map_zero]; exact Submodule.zero_mem _
    · have hkey := Polynomial.self_sub_C_mul_X_pow p
      have hp_eq : p = p.eraseLead + Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree := by
        rw [← hkey]; ring
      rw [hp_eq, map_add]
      refine Submodule.add_mem _ ?_ ?_
      · rcases p.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt | h0
        · exact ih p.eraseLead.natDegree (hn ▸ hlt) p.eraseLead rfl
        · rw [h0, map_zero]; exact Submodule.zero_mem _
      · rw [hn, ← algebraMap_mul_Y_pow_eq]
        exact Submodule.smul_mem _ _
          (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr
            ⟨n % e, Finset.mem_range.mpr (Nat.mod_lt _ e_pos), rfl⟩)))

theorem span_basisFinset_eq_top : Submodule.span R (basisFinset : Set S) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  simpa using mem_span_basisFinset (S.ringEquivPoly z)

instance : Module.Finite R S :=
  Module.finite_def.mpr (span_basisFinset_eq_top ▸ Submodule.fg_span (Set.toFinite _))

instance : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S

instance : Module.IsTorsionFree R S where
  isSMulRegular r hr := by
    intro s1 s2 hs
    simp only [Algebra.smul_def] at hs
    have hr0 : algebraMap R S r ≠ 0 := by
      rw [algebraMap_R_S_eq]
      exact fun h => hr.ne_zero (algMapRS_injective (h.trans (map_zero algMapRS).symm))
    exact mul_left_cancel₀ hr0 hs

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

/-! ### `Module.Finite K L`, via `yL := algebraMap S L Y` generating `L` over `K`

`yL` satisfies `yL ^ e = algebraMap K L (algebraMap R K X)`, hence is integral over `K`, so `K⟮yL⟯`
is a finite extension of `K`. `K⟮yL⟯ = ⊤` because it contains the image of every element of `S`
(by the basis fact above, pushed through the compatible algebra maps) and, being a field, therefore
contains every quotient of two such images — i.e. all of `L = Frac(S)`. -/

/-- `yL`, the image of `Y` in `L`. -/
def yL : L := algebraMap S L Y

theorem yL_pow_eq : yL ^ e = algebraMap K L (algebraMap R K (Polynomial.X : R)) := by
  show (algebraMap S L Y) ^ e = _
  rw [← map_pow, ← algebraMap_X_eq, ← IsScalarTower.algebraMap_apply R S L]
  exact IsScalarTower.algebraMap_apply R K L _

theorem isIntegral_yL : IsIntegral K yL :=
  ⟨Polynomial.X ^ e - Polynomial.C (algebraMap R K (Polynomial.X : R)),
    Polynomial.monic_X_pow_sub_C _ e_pos.ne', by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, yL_pow_eq, sub_self]⟩

theorem algebraMap_S_L_algebraMap_R_S_eq (r : R) :
    algebraMap S L (algebraMap R S r) = algebraMap K L (algebraMap R K r) := by
  rw [← IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply R K L]

theorem algebraMap_mem_adjoin_yL (s : S) :
    algebraMap S L s ∈ IntermediateField.adjoin K ({yL} : Set L) := by
  have hs : s ∈ Submodule.span R (basisFinset : Set S) :=
    span_basisFinset_eq_top ▸ Submodule.mem_top
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    rw [map_pow]
    exact pow_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton yL)) i
  | zero => rw [map_zero]; exact (IntermediateField.adjoin K ({yL} : Set L)).zero_mem
  | add x y' hx hy' ihx ihy' =>
    rw [map_add]
    exact (IntermediateField.adjoin K ({yL} : Set L)).add_mem ihx ihy'
  | smul r x hx ih =>
    have hr : algebraMap K L (algebraMap R K r) ∈ IntermediateField.adjoin K ({yL} : Set L) :=
      IntermediateField.algebraMap_mem _ _
    have heq : algebraMap S L (r • x) = algebraMap K L (algebraMap R K r) * algebraMap S L x := by
      rw [Algebra.smul_def, map_mul, algebraMap_S_L_algebraMap_R_S_eq]
    rw [heq]
    exact (IntermediateField.adjoin K ({yL} : Set L)).mul_mem hr ih

theorem adjoin_yL_eq_top : IntermediateField.adjoin K ({yL} : Set L) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors S) z
  have hb0 : (b : S) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
  have hbL0 : algebraMap S L (b : S) ≠ 0 :=
    fun h => hb0 (IsLocalization.injective L (le_refl (nonZeroDivisors S))
      (h.trans (map_zero (algebraMap S L)).symm))
  have heq : z * algebraMap S L (b : S) = algebraMap S L a := by
    rw [← hab]; exact IsLocalization.mk'_spec L a b
  have hz : z = algebraMap S L a * (algebraMap S L (b : S))⁻¹ := by
    rw [← heq, mul_inv_cancel_right₀ hbL0]
  rw [hz]
  exact (IntermediateField.adjoin K _).mul_mem (algebraMap_mem_adjoin_yL a)
    ((IntermediateField.adjoin K _).inv_mem (algebraMap_mem_adjoin_yL b))

instance : Module.Finite K L := by
  have hfin : FiniteDimensional K (IntermediateField.adjoin K ({yL} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional isIntegral_yL
  have htop := adjoin_yL_eq_top
  rw [htop] at hfin
  exact Module.Finite.equiv (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv

/-! ### `v : HeightOneSpectrum R` at `(X)`, `w : HeightOneSpectrum S` at `(Y)` -/

/-- `v`, the place of `R = k[X]` at `X`. -/
def v : HeightOneSpectrum R where
  asIdeal := Ideal.span {Polynomial.X}
  isPrime := (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  ne_bot := by simp

/-- `w`, the place of `S = k[Y]` at `Y`. -/
def w : HeightOneSpectrum S where
  asIdeal := Ideal.span {Y}
  isPrime := (Ideal.span_singleton_prime (by rw [Y_eq]; simp)).mpr
    (Y_eq ▸ (MulEquiv.prime_iff S.ringEquivPoly.symm).mpr Polynomial.prime_X)
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot, Y_eq]
    simp

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

/-! ### `Algebra.IsSeparable K L`

`T ^ e - C x` (the integral witness for `yL`, `isIntegral_yL`) is separable over `K`: `CharP K p`
transports from `CharP k p` through `R = k[X]` (`Polynomial.charP`) and `K = Frac(R)`
(`IsFractionRing.charP`), giving `(e : K) ≠ 0` since `p ∤ e` (`coprime_e_p`); `x ≠ 0` since
`algebraMap R K` is injective and `X ≠ 0`. `Polynomial.separable_X_pow_sub_C` then applies.
Since `minpoly K yL` divides this separable polynomial (`minpoly.dvd`, using the same witness),
it is itself separable (`Polynomial.Separable.of_dvd`), i.e. `IsSeparable K yL`. As `K⟮yL⟯ = ⊤`
(`adjoin_yL_eq_top`), `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable` upgrades this to
`Algebra.IsSeparable K ↥(⊤ : IntermediateField K L)`, transported to `Algebra.IsSeparable K L` across
`IntermediateField.topEquiv` (`AlgEquiv.Algebra.isSeparable`). -/

instance charP_K : CharP K p :=
  haveI : CharP R p := Polynomial.charP
  IsFractionRing.charP R p

theorem e_cast_ne_zero : ((e : ℕ) : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K p]
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mp coprime_e_p.symm

theorem x_ne_zero : algebraMap R K (Polynomial.X : R) ≠ 0 :=
  fun h => Polynomial.X_ne_zero
    (IsFractionRing.injective R K (h.trans (map_zero (algebraMap R K)).symm))

theorem separable_X_pow_sub_C_x :
    (Polynomial.X ^ e - Polynomial.C (algebraMap R K (Polynomial.X : R)) : Polynomial K).Separable :=
  Polynomial.separable_X_pow_sub_C _ e_cast_ne_zero x_ne_zero

theorem isSeparable_yL : IsSeparable K yL := by
  have haeval : Polynomial.aeval yL
      (Polynomial.X ^ e - Polynomial.C (algebraMap R K (Polynomial.X : R)) : Polynomial K) = 0 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, yL_pow_eq, sub_self]
  exact separable_X_pow_sub_C_x.of_dvd (minpoly.dvd K yL haeval)

instance : Algebra.IsSeparable K L := by
  haveI htop : Algebra.IsSeparable K ↥(⊤ : IntermediateField K L) :=
    adjoin_yL_eq_top ▸
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).mpr isSeparable_yL
  exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv (F := K) (E := L))

/-! ### `Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)`

The completion-level bridge. Write `Kv := v.adicCompletion K`, `Lw := w.adicCompletion L`,
`xK := algebraMap K Kv (algebraMap R K X)`, `yLw := algebraMap L Lw yL`. The candidate polynomial
`gPoly := X ^ e - C xK` is separable over `Kv` *for free*, by mapping `separable_X_pow_sub_C_x`
along `algebraMap K Kv` (`Polynomial.Separable.map`) — no Eisenstein/irreducibility argument is
needed for separability itself. `yLw` is a root of `gPoly` (chasing `yL_pow_eq` through the
commuting square `adicCompletionComap_algebraMap`, i.e. `algebraMap Kv Lw ∘ algebraMap K Kv =
algebraMap L Lw ∘ algebraMap K L`), so `minpoly Kv yLw ∣ gPoly` (`minpoly.dvd`), hence is itself
separable (`Polynomial.Separable.of_dvd`) — `IsSeparable Kv yLw`.

The remaining content is `Kv⟮yLw⟯ = ⊤`: this is where "totally ramified" (in the sense that this
instance's construction makes it, definitionally) actually enters, via the two facts flagged in
`ROADMAP.md` as the missing local-field-theory ingredients — both of which turned out to already
exist in `Langlands.HenselianValuation`/`Langlands.NormMap`, just not yet invoked here. `Kv⟮yLw⟯`
is finite-dimensional over `Kv` (from `IsIntegral Kv yLw`, witnessed by `gPoly`), hence *closed* in
`Lw` (`Submodule.closed_of_finiteDimensional`, needing only `CompleteSpace Kv` — the adic-completion
instance already in Mathlib — not the more elaborate `LocalField.exists_completeSpace_of_finiteDimensional`
machinery, since `Lw` is already known complete as an adic completion in its own right). It contains
the image of `L` (every `l : L` is a `K`-polynomial value at `yL`, since `K⟮yL⟯ = ⊤`; push through
the commuting square to express its image as a `Kv`-polynomial value at `yLw`). Since the image of
`L` is *dense* in `Lw` (`IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap`), a closed set
containing a dense set is everything: `Kv⟮yLw⟯ = ⊤`. -/

/-- `xK`, the image of `x := algebraMap R K X` inside `v.adicCompletion K`. -/
def xK : v.adicCompletion K := algebraMap K (v.adicCompletion K) (algebraMap R K (Polynomial.X : R))

/-- `yLw`, the image of `yL` inside `w.adicCompletion L`. -/
def yLw : w.adicCompletion L := algebraMap L (w.adicCompletion L) yL

/-- The candidate minimal-polynomial witness for `yLw` over `v.adicCompletion K`. -/
def gPoly : Polynomial (v.adicCompletion K) := Polynomial.X ^ e - Polynomial.C (xK)

theorem gPoly_monic : gPoly.Monic := Polynomial.monic_X_pow_sub_C _ e_pos.ne'

theorem gPoly_separable : gPoly.Separable := by
  have hmap := separable_X_pow_sub_C_x.map (f := algebraMap K (v.adicCompletion K))
  rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] at hmap

theorem yLw_pow_eq : yLw ^ e = algebraMap (v.adicCompletion K) (w.adicCompletion L) xK := by
  show (algebraMap L (w.adicCompletion L) yL) ^ e = _
  rw [← map_pow, yL_pow_eq, xK]
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionComap_algebraMap K L v w
    (algebraMap R K (Polynomial.X : R))).symm

theorem isIntegral_yLw : IsIntegral (v.adicCompletion K) yLw :=
  ⟨gPoly, gPoly_monic, by
    rw [gPoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, yLw_pow_eq,
      sub_self]⟩

theorem isSeparable_yLw : IsSeparable (v.adicCompletion K) yLw := by
  have haeval : Polynomial.aeval yLw gPoly = 0 := by
    rw [gPoly, Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, yLw_pow_eq,
      sub_self]
  exact gPoly_separable.of_dvd (minpoly.dvd (v.adicCompletion K) yLw haeval)

theorem algebraMap_L_mem_adjoin_yLw (l : L) :
    algebraMap L (w.adicCompletion L) l ∈
      IntermediateField.adjoin (v.adicCompletion K) ({yLw} : Set (w.adicCompletion L)) := by
  have htopalg : Algebra.adjoin K ({yL} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic isIntegral_yL.isAlgebraic,
      adjoin_yL_eq_top, IntermediateField.top_toSubalgebra]
  have hl : l ∈ Algebra.adjoin K ({yL} : Set L) := htopalg ▸ Algebra.mem_top
  induction hl using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton yLw)
  | algebraMap r =>
    have heq : algebraMap L (w.adicCompletion L) (algebraMap K L r) =
        algebraMap (v.adicCompletion K) (w.adicCompletion L)
          (algebraMap K (v.adicCompletion K) r) :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionComap_algebraMap K L v w r).symm
    rw [heq]
    exact IntermediateField.algebraMap_mem _ _
  | add x y' hx hy' ihx ihy' =>
    rw [map_add]
    exact (IntermediateField.adjoin (v.adicCompletion K)
      ({yLw} : Set (w.adicCompletion L))).add_mem ihx ihy'
  | mul x y' hx hy' ihx ihy' =>
    rw [map_mul]
    exact (IntermediateField.adjoin (v.adicCompletion K)
      ({yLw} : Set (w.adicCompletion L))).mul_mem ihx ihy'

theorem adjoin_yLw_eq_top :
    IntermediateField.adjoin (v.adicCompletion K) ({yLw} : Set (w.adicCompletion L)) = ⊤ := by
  haveI : FiniteDimensional (v.adicCompletion K)
      (IntermediateField.adjoin (v.adicCompletion K) ({yLw} : Set (w.adicCompletion L))) :=
    IntermediateField.adjoin.finiteDimensional isIntegral_yLw
  have hMclosed : IsClosed
      ((IntermediateField.adjoin (v.adicCompletion K)
        ({yLw} : Set (w.adicCompletion L))).toSubalgebra.toSubmodule : Set (w.adicCompletion L)) :=
    Submodule.closed_of_finiteDimensional _
  have hsub : Set.range (algebraMap L (w.adicCompletion L)) ⊆
      ((IntermediateField.adjoin (v.adicCompletion K)
        ({yLw} : Set (w.adicCompletion L))) : Set (w.adicCompletion L)) := by
    rintro _ ⟨l, rfl⟩
    exact algebraMap_L_mem_adjoin_yLw l
  have hdense : Dense (Set.range (algebraMap L (w.adicCompletion L))) :=
    w.denseRange_algebraMap L
  have htop : (Set.univ : Set (w.adicCompletion L)) ⊆
      ((IntermediateField.adjoin (v.adicCompletion K)
        ({yLw} : Set (w.adicCompletion L))) : Set (w.adicCompletion L)) := by
    rw [← hdense.closure_eq]
    exact closure_minimal hsub hMclosed
  rw [eq_top_iff]
  intro z _
  exact htop (Set.mem_univ z)

instance : Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) := by
  haveI htop : Algebra.IsSeparable (v.adicCompletion K)
      ↥(⊤ : IntermediateField (v.adicCompletion K) (w.adicCompletion L)) :=
    adjoin_yLw_eq_top ▸
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
        (v.adicCompletion K) (w.adicCompletion L)).mpr isSeparable_yLw
  exact AlgEquiv.Algebra.isSeparable
    (IntermediateField.topEquiv (F := v.adicCompletion K) (E := w.adicCompletion L))

/-! ### The Dedekind-style ramification index equals `e`

`v.asIdeal.ramificationIdx' w.asIdeal` (the exponent `IsTotallyRamified` is stated in terms of)
equals the concrete instance's `e`, via `Ideal.ramificationIdx'_spec` applied to the exact identity
`map_v_eq` and the strict decrease `Ideal.pow_succ_lt_pow` of powers of the nonzero prime
`w.asIdeal`. -/

theorem ramificationIdx'_eq : v.asIdeal.ramificationIdx' w.asIdeal = e := by
  apply Ideal.ramificationIdx'_spec
  · show Ideal.map algMapRS v.asIdeal ≤ w.asIdeal ^ e
    exact le_of_eq map_v_eq
  · show ¬ Ideal.map algMapRS v.asIdeal ≤ w.asIdeal ^ (e + 1)
    intro hle
    rw [map_v_eq] at hle
    have hlt := Ideal.pow_succ_lt_pow w.ne_bot e
    exact hlt.ne (le_antisymm hlt.le hle)

/-! ### `xK` and `yLw` are uniformizers of `v.adicCompletion K` / `w.adicCompletion L`

`X` generates `v.asIdeal` exactly (`v.asIdeal := Ideal.span {X}` by definition), so its `v`-adic
valuation is the canonical uniformizer value `exp (-1)` (`intValuation_singleton`). Since `yLw ^ e =
algebraMap xK` (`yLw_pow_eq`) and `Valued.v (algebraMap xK) = Valued.v xK ^ e`
(`valuation_algebraMap_pow_eq`, via `ramificationIdx'_eq`), `Valued.v yLw` and `exp (-1)` have equal
`e`-th powers in `ℤᵐ⁰`; taking `WithZero.log` (additive, so `e`-th powers become `e`-multiples) and
cancelling the nonzero integer `e` pins `Valued.v yLw` down to `exp (-1)` exactly, not merely up to
an `e`-th root of unity — `ℤᵐ⁰`'s value group `ℤ` is torsion-free, so there is no such ambiguity. -/

open scoped WithZero

theorem valuation_xK : Valued.v xK = WithZero.exp (-1 : ℤ) := by
  show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K (Polynomial.X : R))) = _
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K (Polynomial.X : R))
      = ((algebraMap R K (Polynomial.X : R) : K) : v.adicCompletion K) from rfl,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_singleton Polynomial.X_ne_zero rfl

theorem valuation_yLw : Valued.v yLw = WithZero.exp (-1 : ℤ) := by
  have hpow : (Valued.v yLw) ^ e = (WithZero.exp (-1 : ℤ)) ^ e := by
    rw [← map_pow, yLw_pow_eq]
    show Valued.v (IsDedekindDomain.HeightOneSpectrum.adicCompletionComap K L v w xK) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_pow_eq K L v w xK,
      ramificationIdx'_eq, valuation_xK]
  have hlog := congrArg WithZero.log hpow
  rw [WithZero.log_pow, WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul, nsmul_eq_mul] at hlog
  have he : WithZero.log (Valued.v yLw) = -1 :=
    mul_left_cancel₀ (by exact_mod_cast e_pos.ne' : (e : ℤ) ≠ 0) hlog
  have hne0 : Valued.v yLw ≠ 0 := by
    intro h0; rw [h0, WithZero.log_zero] at he; exact absurd he (by norm_num)
  rw [← WithZero.exp_log hne0, he]

/-- `xK`, viewed as an element of `v.adicCompletionIntegers K`. -/
def xK₀ : v.adicCompletionIntegers K :=
  ⟨xK, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v, valuation_xK,
      ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)⟩

/-- `yLw`, viewed as an element of `w.adicCompletionIntegers L`. -/
def yLw₀ : w.adicCompletionIntegers L :=
  ⟨yLw, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers S L w, valuation_yLw,
      ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)⟩

theorem coe_xK₀ : (xK₀ : v.adicCompletion K) = xK := rfl

theorem coe_yLw₀ : (yLw₀ : w.adicCompletion L) = yLw := rfl

theorem isUniformizer_xK₀ : Valuation.IsUniformizer Valued.v (xK₀ : v.adicCompletion K) := by
  rw [Valuation.IsUniformizer.iff, coe_xK₀, valuation_xK,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v)]
  rfl

theorem isUniformizer_yLw₀ : Valuation.IsUniformizer Valued.v (yLw₀ : w.adicCompletion L) := by
  rw [Valuation.IsUniformizer.iff, coe_yLw₀, valuation_yLw,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective L w)]
  rfl

/-- `xK₀` generates the maximal ideal of `K₀ := v.adicCompletionIntegers K`. -/
theorem maximalIdeal_K₀_eq : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
    = Ideal.span {(xK₀ : v.adicCompletionIntegers K)} :=
  isUniformizer_xK₀.is_generator

/-- `yLw₀` generates the maximal ideal of `L₀ := w.adicCompletionIntegers L`. -/
theorem maximalIdeal_L₀_eq : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)
    = Ideal.span {(yLw₀ : w.adicCompletionIntegers L)} :=
  isUniformizer_yLw₀.is_generator

theorem irreducible_xK₀ : Irreducible (xK₀ : v.adicCompletionIntegers K) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr maximalIdeal_K₀_eq

theorem irreducible_yLw₀ : Irreducible (yLw₀ : w.adicCompletionIntegers L) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr maximalIdeal_L₀_eq

/-! ### Field 1 of `IsTotallyRamified`: `map_maximalIdeal_eq` -/

theorem algebraMap_xK₀_eq : algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
    (xK₀ : v.adicCompletionIntegers K) = (yLw₀ : w.adicCompletionIntegers L) ^ e := by
  apply Subtype.ext
  show IsDedekindDomain.HeightOneSpectrum.adicCompletionComap K L v w xK = yLw ^ e
  rw [yLw_pow_eq]; rfl

theorem map_maximalIdeal_eq :
    Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^
        (v.asIdeal.ramificationIdx' w.asIdeal) := by
  rw [maximalIdeal_K₀_eq, Ideal.map_span, Set.image_singleton, algebraMap_xK₀_eq,
    ← Ideal.span_singleton_pow, ← maximalIdeal_L₀_eq, ramificationIdx'_eq]

/-! ### Field 2 of `IsTotallyRamified`: `finrank_eq`

`e = 3` is prime, so it suffices to show `xK` has no `e`-th root in `v.adicCompletion K`
(`X_pow_sub_C_irreducible_of_prime`) to conclude `gPoly := X ^ e - C xK` is irreducible. Since
`gPoly` is monic and `yLw` is a root, `gPoly` **is** `minpoly (v.adicCompletion K) yLw`
(`minpoly.eq_of_irreducible`), pinning `Module.finrank (v.adicCompletion K)
(v.adicCompletion K)⟮yLw⟯` at exactly `e = gPoly.natDegree` (`IntermediateField.adjoin.finrank`) —
not just `≤ e` from integrality alone. Combined with `adjoin_yLw_eq_top`, this gives
`Module.finrank (v.adicCompletion K) (w.adicCompletion L) = e`, which transports to the
completed-integers level via `IsIntegralClosure.rank` (`w.adicCompletionIntegers L` being the
integral closure of `v.adicCompletionIntegers K` in `w.adicCompletion L`,
`instIsIntegralClosureAdicCompletionIntegers`). -/

theorem e_prime : Nat.Prime e := by decide

/-- `xK` has no `e`-th root in `v.adicCompletion K`: if `b ^ e = xK`, taking `Valued.v` and then
`WithZero.log` gives `e * WithZero.log (Valued.v b) = -1` in `ℤ`, impossible since `e = 3 ∤ 1`. -/
theorem xK_not_pow (b : v.adicCompletion K) : b ^ e ≠ xK := by
  intro hb
  have hv : Valued.v (b ^ e) = Valued.v xK := congrArg Valued.v hb
  rw [map_pow, valuation_xK] at hv
  have hlog := congrArg WithZero.log hv
  rw [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hlog
  have he3 : (e : ℤ) = 3 := by norm_num [e]
  rw [he3] at hlog
  omega

theorem gPoly_irreducible : Irreducible gPoly :=
  X_pow_sub_C_irreducible_of_prime e_prime xK_not_pow

theorem minpoly_yLw_eq : minpoly (v.adicCompletion K) yLw = gPoly := by
  have haeval : Polynomial.aeval yLw gPoly = 0 := by
    rw [gPoly, Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, yLw_pow_eq,
      sub_self]
  have heq := minpoly.eq_of_irreducible gPoly_irreducible haeval
  rw [gPoly_monic.leadingCoeff, inv_one, map_one, mul_one] at heq
  exact heq.symm

theorem natDegree_minpoly_yLw : (minpoly (v.adicCompletion K) yLw).natDegree = e := by
  rw [minpoly_yLw_eq, gPoly, Polynomial.natDegree_X_pow_sub_C]

theorem finrank_adjoin_yLw : Module.finrank (v.adicCompletion K)
    (IntermediateField.adjoin (v.adicCompletion K) ({yLw} : Set (w.adicCompletion L))) = e := by
  rw [IntermediateField.adjoin.finrank isIntegral_yLw, natDegree_minpoly_yLw]

theorem finrank_Kv_Lw : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = e := by
  rw [← LinearEquiv.finrank_eq (IntermediateField.topEquiv (F := v.adicCompletion K)
    (E := w.adicCompletion L)).toLinearEquiv, ← adjoin_yLw_eq_top]
  exact finrank_adjoin_yLw

theorem finrank_K₀_L₀ :
    Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) = e := by
  rw [IsIntegralClosure.rank (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.adicCompletion L) (w.adicCompletionIntegers L), finrank_Kv_Lw]

theorem finrank_eq :
    Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      v.asIdeal.ramificationIdx' w.asIdeal := by
  rw [finrank_K₀_L₀, ramificationIdx'_eq]

/-! ### `IsTamelyRamified`

`ResidueField (v.adicCompletionIntegers K)` has characteristic `p`: `CharP K p` (`charP_K`)
transports along the injective field map `K → v.adicCompletion K`
(`RingHom.charP_iff_charP`), then along the injective inclusion `v.adicCompletionIntegers K →
v.adicCompletion K` (`RingHom.charP`), then along the (surjective, but injectivity is not needed —
any ring hom out of a nonzero-characteristic domain into a nontrivial ring preserves that
characteristic) residue map (`CharP.of_ringHom_of_ne_zero`). Since `finrank_eq` gives
`Module.finrank K₀ L₀ = e = 3`, `IsTamelyRamified` reduces to `(3 : ResidueField K₀) ≠ 0`, which
holds because `p = 7 ∤ 3` (`coprime_e_p`). -/

instance charP_Kv : CharP (v.adicCompletion K) p :=
  (RingHom.charP_iff_charP (algebraMap K (v.adicCompletion K)) p).mp charP_K

instance charP_K₀ : CharP (v.adicCompletionIntegers K) p :=
  RingHom.charP (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
    Subtype.coe_injective p

instance charP_residueK₀ : CharP (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) p :=
  CharP.of_ringHom_of_ne_zero (IsLocalRing.residue (v.adicCompletionIntegers K)) p (by norm_num)

theorem isTamelyRamified : IsDedekindDomain.HeightOneSpectrum.IsTamelyRamified K L v w := by
  show IsUnit ((Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) : ℕ) :
    IsLocalRing.ResidueField (v.adicCompletionIntegers K))
  rw [finrank_eq, ramificationIdx'_eq, isUnit_iff_ne_zero, Ne,
    CharP.cast_eq_zero_iff (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) p]
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mp coprime_e_p.symm

/-! ### Field 3 of `IsTotallyRamified`: `exists_sub_algebraMap_mem_maximalIdeal`

`Langlands.AdicCompletionIntegersResidue.exists_algebraMap_sub_mem_maximalIdeal` (a general,
single-place density fact — no extension data needed) gives, for `y : w.adicCompletionIntegers L`,
some `s : S` with `y - algebraMap S (w.adicCompletionIntegers L) s ∈ maximalIdeal
(w.adicCompletionIntegers L)`. It remains to replace `s` by an element of `v.adicCompletionIntegers
K`: writing `c := (S.ringEquivPoly s).coeff 0 : k` for `s`'s constant term, `s -
S.ringEquivPoly.symm (C c) ∈ w.asIdeal = (Y)` (its image under `S ≃+* k[Y]` has zero constant term,
hence is a multiple of `X`), so `algebraMap S s` and `algebraMap S (S.ringEquivPoly.symm (C c))`
agree mod `maximalIdeal (w.adicCompletionIntegers L)`. Since `X ↦ Y ^ e` fixes constants,
`algebraMap R S (C c) = S.ringEquivPoly.symm (C c)`, and the naturality square `R → K₀ → L₀ = R → S
→ L₀` (`coe_algebraMap_adicCompletionIntegers`, `adicCompletionComap_algebraMap`,
`algebraMap_S_L_algebraMap_R_S_eq`) identifies `algebraMap S (S.ringEquivPoly.symm (C c))` with
`algebraMap K₀ L₀ (algebraMap R K₀ (C c))`. Composing the two maximal-ideal memberships (the ideal
being closed under addition) finishes it, with `r := algebraMap R (v.adicCompletionIntegers K) (C
c)`. -/

/-- **The naturality square `R → K₀ → L₀ = R → S → L₀`.** Pushing `a : R` into `K₀ :=
v.adicCompletionIntegers K` and then into `L₀ := w.adicCompletionIntegers L` agrees with pushing it
into `S` and then into `L₀`. Both sides reduce, via `coe_algebraMap_adicCompletionIntegers` /
`algebraMap_adicCompletionIntegers_apply` and `adicCompletionComap_algebraMap`, to the single
identity `algebraMap S L (algebraMap R S a) = algebraMap K L (algebraMap R K a)`
(`algebraMap_S_L_algebraMap_R_S_eq`). -/
theorem algebraMap_R_K₀_L₀_eq (a : R) :
    algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
        (algebraMap R (v.adicCompletionIntegers K) a) =
      algebraMap S (w.adicCompletionIntegers L) (algebraMap R S a) := by
  apply Subtype.ext
  rw [IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_adicCompletionIntegers]
  show IsDedekindDomain.HeightOneSpectrum.adicCompletionComap K L v w
      (algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletion K) = _
  rw [show (algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletion K)
        = algebraMap K (v.adicCompletion K) (algebraMap R K a) from rfl,
    IsDedekindDomain.HeightOneSpectrum.adicCompletionComap_algebraMap,
    ← algebraMap_S_L_algebraMap_R_S_eq a]
  rfl

theorem algebraMap_R_S_C_eq (c : k) :
    algebraMap R S (Polynomial.C c) = S.ringEquivPoly.symm (Polynomial.C c) := by
  rw [algebraMap_R_S_eq]
  show S.ringEquivPoly.symm (Polynomial.expand k e (Polynomial.C c)) = _
  rw [Polynomial.expand_C]

theorem exists_sub_algebraMap_mem_maximalIdeal :
    ∀ y : w.adicCompletionIntegers L, ∃ r : v.adicCompletionIntegers K,
      y - algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r ∈
        IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) := by
  intro y
  obtain ⟨s, hs⟩ := w.exists_algebraMap_sub_mem_maximalIdeal y
  set c : k := (S.ringEquivPoly s).coeff 0 with hcdef
  refine ⟨algebraMap R (v.adicCompletionIntegers K) (Polynomial.C c), ?_⟩
  rw [algebraMap_R_K₀_L₀_eq, algebraMap_R_S_C_eq]
  have hsc : (y : w.adicCompletionIntegers L) -
      algebraMap S (w.adicCompletionIntegers L) (S.ringEquivPoly.symm (Polynomial.C c)) =
      ((y : w.adicCompletionIntegers L) - algebraMap S (w.adicCompletionIntegers L) s) +
        algebraMap S (w.adicCompletionIntegers L) (s - S.ringEquivPoly.symm (Polynomial.C c)) := by
    rw [map_sub]; ring
  rw [hsc]
  refine (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).add_mem hs ?_
  have hmem : s - S.ringEquivPoly.symm (Polynomial.C c) ∈ w.asIdeal := by
    have hdvdX : Polynomial.X ∣ (S.ringEquivPoly s - Polynomial.C c) :=
      Polynomial.X_dvd_iff.mpr (by simp [hcdef])
    have hdvdY : S.ringEquivPoly.symm Polynomial.X ∣
        S.ringEquivPoly.symm (S.ringEquivPoly s - Polynomial.C c) :=
      map_dvd S.ringEquivPoly.symm hdvdX
    rw [map_sub, RingEquiv.symm_apply_apply] at hdvdY
    show s - S.ringEquivPoly.symm (Polynomial.C c) ∈ Ideal.span ({Y} : Set S)
    rw [Ideal.mem_span_singleton, Y_eq]
    exact hdvdY
  have hval_lt : w.valuation L (algebraMap S L (s - S.ringEquivPoly.symm (Polynomial.C c))) < 1 :=
    (w.valuation_lt_one_iff_mem (s - S.ringEquivPoly.symm (Polynomial.C c))).mpr hmem
  have hValued_lt : Valued.v (algebraMap S (w.adicCompletionIntegers L)
      (s - S.ringEquivPoly.symm (Polynomial.C c)) : w.adicCompletion L) < 1 := by
    rw [show (algebraMap S (w.adicCompletionIntegers L)
        (s - S.ringEquivPoly.symm (Polynomial.C c)) : w.adicCompletion L)
        = (algebraMap S L (s - S.ringEquivPoly.symm (Polynomial.C c)) : w.adicCompletion L)
        from rfl,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hval_lt
  exact IsDedekindDomain.HeightOneSpectrum.mem_maximalIdeal_of_valued_lt_one w hValued_lt

/-- **`IsTotallyRamified K L v w` for this concrete instance.** Assembled from `map_maximalIdeal_eq`,
`finrank_eq`, and `exists_sub_algebraMap_mem_maximalIdeal` above. -/
theorem isTotallyRamified : IsDedekindDomain.HeightOneSpectrum.IsTotallyRamified K L v w where
  map_maximalIdeal_eq := map_maximalIdeal_eq
  finrank_eq := finrank_eq
  exists_sub_algebraMap_mem_maximalIdeal := exists_sub_algebraMap_mem_maximalIdeal

/-! ### Capstone: the norm-group index `[(v.adicCompletion K)ˣ : N(L_w^×)] = gcd(e, #κ[K]ˣ) = 3`

`R = k[X]`, `v.asIdeal = (X)`, so `R ⧸ v.asIdeal ≅ k` via the constant-coefficient map
(`Polynomial.ker_constantCoeff`); likewise `S ⧸ w.asIdeal ≅ k` via the same map transported across
`S ≃+* k[Y]`. Composed with `Langlands.AdicCompletionIntegersResidue.residueFieldQuotientRingEquiv`,
this identifies both `ResidueField (v.adicCompletionIntegers K)` and `ResidueField
(w.adicCompletionIntegers L)` with `k := ZMod 7`, giving `Nat.card (ResidueField
(v.adicCompletionIntegers K))ˣ = Nat.card kˣ = 6` and finiteness of `ResidueField
(w.adicCompletionIntegers L)` (needed as an instance by
`index_localNormMap_range_eq_of_isTotallyRamified`). With `e = 3`, the classical formula
`gcd(e, #κ[K]ˣ)` evaluates to `gcd(3, 6) = 3`. -/

theorem constantCoeff_S_surjective :
    Function.Surjective (Polynomial.constantCoeff.comp S.ringEquivPoly.toRingHom : S →+* k) :=
  fun c => ⟨S.ringEquivPoly.symm (Polynomial.C c), by simp⟩

theorem ker_constantCoeff_S_eq :
    RingHom.ker (Polynomial.constantCoeff.comp S.ringEquivPoly.toRingHom : S →+* k) = w.asIdeal := by
  ext s
  rw [RingHom.mem_ker, RingHom.comp_apply, Polynomial.constantCoeff_apply]
  show (S.ringEquivPoly s).coeff 0 = 0 ↔ s ∈ Ideal.span ({Y} : Set S)
  rw [Ideal.mem_span_singleton, Y_eq]
  constructor
  · intro h0
    have hdvdX : Polynomial.X ∣ S.ringEquivPoly s := Polynomial.X_dvd_iff.mpr h0
    have hdvdY := map_dvd S.ringEquivPoly.symm hdvdX
    rwa [RingEquiv.symm_apply_apply] at hdvdY
  · intro hdvd
    have hdvdX : Polynomial.X ∣ S.ringEquivPoly s := by
      have hdvdY := map_dvd S.ringEquivPoly hdvd
      rwa [RingEquiv.apply_symm_apply] at hdvdY
    exact Polynomial.X_dvd_iff.mp hdvdX

/-- `R ⧸ v.asIdeal ≃+* k`, via the constant-coefficient map (`Polynomial.ker_constantCoeff`,
`v.asIdeal = Ideal.span {X}` by definition). -/
noncomputable def quotientVAsIdealRingEquiv : (R ⧸ v.asIdeal) ≃+* k :=
  (Ideal.quotEquivOfEq
      (show v.asIdeal = RingHom.ker (Polynomial.constantCoeff : R →+* k) from
        Polynomial.ker_constantCoeff.symm)).trans
    (RingHom.quotientKerEquivOfSurjective
      (fun c => ⟨Polynomial.C c, by rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]⟩))

/-- `S ⧸ w.asIdeal ≃+* k`, via the constant-coefficient map transported across `S ≃+* k[Y]`. -/
noncomputable def quotientWAsIdealRingEquiv : (S ⧸ w.asIdeal) ≃+* k :=
  (Ideal.quotEquivOfEq ker_constantCoeff_S_eq.symm).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_S_surjective)

/-- `ResidueField (v.adicCompletionIntegers K) ≃+* k`. -/
noncomputable def residueFieldK₀RingEquiv :
    IsLocalRing.ResidueField (v.adicCompletionIntegers K) ≃+* k :=
  (v.residueFieldQuotientRingEquiv (F := K)).symm.trans quotientVAsIdealRingEquiv

/-- `ResidueField (w.adicCompletionIntegers L) ≃+* k`. -/
noncomputable def residueFieldL₀RingEquiv :
    IsLocalRing.ResidueField (w.adicCompletionIntegers L) ≃+* k :=
  (w.residueFieldQuotientRingEquiv (F := L)).symm.trans quotientWAsIdealRingEquiv

instance : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers L)) :=
  Finite.of_equiv k residueFieldL₀RingEquiv.symm.toEquiv

theorem nat_card_residueFieldK₀_units :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K))ˣ = 6 := by
  rw [Nat.card_congr (Units.mapEquiv residueFieldK₀RingEquiv.toMulEquiv).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

/-- **The capstone computation**: instantiating
`index_localNormMap_range_eq_of_isTotallyRamified` on this concrete totally, tamely ramified
example gives `[(v.adicCompletion K)ˣ : N(L_w^×)] = gcd(3, 6) = 3`, a genuine local class field
theory computation checked end-to-end by the Lean type-checker. -/
theorem index_localNormMap_range_eq_three
    {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) :
    (MonoidHom.range (IsDedekindDomain.HeightOneSpectrum.localNormMap K L v w)).index = 3 := by
  rw [IsDedekindDomain.HeightOneSpectrum.index_localNormMap_range_eq_of_isTotallyRamified K L v w
      isTotallyRamified isTamelyRamified hπL,
    ramificationIdx'_eq, nat_card_residueFieldK₀_units]
  decide

end Langlands.TotallyRamifiedConcreteExample

end
