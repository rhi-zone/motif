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

/- **Sanity check**: `IsTotallyRamified K L v w` now typechecks against this concrete instance —
every ambient hypothesis in its `variable` block (`Module.Finite K L`, `Algebra.IsIntegral R S`,
`Module.IsTorsionFree R S`, `IsScalarTower R K L`, etc.) is satisfied. This is a regression check,
not a proof of the predicate itself: `IsTotallyRamified`'s three fields talk about
`v.adicCompletionIntegers K` / `w.adicCompletionIntegers L`, and completing that proof needs the
separability bridge documented in `ROADMAP.md` (still open). -/
#check (IsDedekindDomain.HeightOneSpectrum.IsTotallyRamified K L v w : Prop)

end Langlands.TotallyRamifiedConcreteExample

end
