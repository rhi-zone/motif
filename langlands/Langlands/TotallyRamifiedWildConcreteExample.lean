import Langlands.AdicCompletionIntegersResidue
import Langlands.TotallyRamifiedNormIndex

/-!
# A concrete WILDLY ramified extension: `k(Y) / k(Y^p)` in characteristic `p`

A concrete instance of `R S K L v w` with residue characteristic `p` of `K` *dividing* the
ramification index `e` (here `e := p`), the wild case. It follows
`Langlands.TotallyRamifiedConcreteExample`'s construction pattern literally, with `e := p := 2`
instead of `e := 3`, `p := 7`.

## The construction

Identical in shape to the tame example: `k := ZMod p`, `R := k[X]` (PID hence Dedekind), `S` a
type-synonym wrapper around `k[Y]` (kept distinct from `R` to avoid an `Algebra.id` diamond), the
algebra map `R →+* S` sending `X ↦ Y ^ e` via `Polynomial.expand k e`, `K := Frac(R)`, `L :=
Frac(S)`, `v`/`w` the places at `X`/`Y`. The difference: `e := p := 2`, so `p ∣ e` — the extension
is wildly, not tamely, ramified.

## Status: two of three fields of `IsTotallyRamified` closed; the third genuinely blocked

Reading `Langlands.TotallyRamifiedConcreteExample`'s proofs line by line, most of what's needed —
`Module.Finite R S`, `Module.IsTorsionFree R S`, `Module.Finite K L`, `w LiesOver v`,
`ramificationIdx'_eq`, the uniformizer facts, `map_maximalIdeal_eq` (field 1), and
`exists_sub_algebraMap_mem_maximalIdeal` (field 3) — carries over verbatim: none of it uses
`gcd(e, p) = 1` or separability. **`finrank_eq` (field 2) does not carry over**: the tame file's
route to it (`IsIntegralClosure.rank`) transitively needs `Algebra.IsSeparable`, which is genuinely
false for this purely inseparable extension (not merely unproved — the trace form Mathlib's proof
relies on is identically zero in this case). See the dedicated docstring immediately above
`exists_sub_algebraMap_mem_maximalIdeal` below for the precise argument and what a fix would need.
Consequently **`IsTotallyRamified` is not assembled in this file** — this is an honest, sorry-free
partial result (fields 1 and 3, plus the field-level, not completed-integers-level, degree
computation `finrank_Kv_Lw = e`), not the full milestone.

**Dropped, and genuinely cannot be recovered for this construction regardless:** the two
`Algebra.IsSeparable` instance sections and their supporting lemmas, the `IsTamelyRamified` section,
and the tame capstone norm-index theorem (`index_localNormMap_range_eq_of_isTotallyRamified` takes
`IsTamelyRamified` as an explicit hypothesis). `Y ^ p - X` is genuinely inseparable in
characteristic `p`: its `Y`-derivative is `p · Y ^ (p - 1) = 0`. `L / K` here is a *purely
inseparable* degree-`p` extension (the Frobenius-twist example `k(Y)/k(Y^p)`), not separable, and
in particular not Galois — inseparable extensions are never Galois. See the closing section for
what this rules out even if field 2 were closed.
-/

noncomputable section

open IsDedekindDomain IsLocalRing Polynomial

namespace Langlands.TotallyRamifiedWildConcreteExample

/-! ### The base field and ramification data -/

/-- The residue characteristic, and also the ramification index: `p = e = 2`, the simplest wild
case (`p ∣ e` since `e = p`). -/
abbrev p : ℕ := 2

instance : Fact (Nat.Prime p) := ⟨by decide⟩

/-- The residue field `k := ZMod p`, finite of order `p`. -/
abbrev k : Type := ZMod p

/-- The ramification index, equal to `p` — the wild case. -/
abbrev e : ℕ := p

theorem e_pos : 0 < e := by norm_num

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

Identical argument to the tame example: `S = k[Y]` decomposes over `R = k[X]` (acting via
`X ↦ Y ^ e`) exactly as `k[Y]` decomposes over its degree-`e` "Veronese" subring `k[Y ^ e]`, purely
combinatorially — no characteristic or coprimality dependence. -/

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

Identical to the tame example: `yL` satisfies `yL ^ e = algebraMap K L (algebraMap R K X)`, hence
is integral over `K` (`IsIntegral`, no separability needed), so `K⟮yL⟯` is finite over `K`; it
equals `⊤` because it contains the image of every element of `S` via the basis fact above. -/

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

/-! ### The Dedekind-style ramification index equals `e`

Identical to the tame example: `v.asIdeal.ramificationIdx' w.asIdeal` equals `e`, via
`Ideal.ramificationIdx'_spec` applied to `map_v_eq` and the strict decrease of powers of the
nonzero prime `w.asIdeal` — no characteristic dependence. -/

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

Identical valuation argument to the tame example, purely about the value group `ℤᵐ⁰` — no
characteristic dependence. -/

open scoped WithZero

/-- `xK`, the image of `x := algebraMap R K X` inside `v.adicCompletion K`. -/
def xK : v.adicCompletion K := algebraMap K (v.adicCompletion K) (algebraMap R K (Polynomial.X : R))

/-- `yLw`, the image of `yL` inside `w.adicCompletion L`. -/
def yLw : w.adicCompletion L := algebraMap L (w.adicCompletion L) yL

/-- The candidate minimal-polynomial witness for `yLw` over `v.adicCompletion K`. -/
def gPoly : Polynomial (v.adicCompletion K) := Polynomial.X ^ e - Polynomial.C (xK)

theorem gPoly_monic : gPoly.Monic := Polynomial.monic_X_pow_sub_C _ e_pos.ne'

theorem yLw_pow_eq : yLw ^ e = algebraMap (v.adicCompletion K) (w.adicCompletion L) xK := by
  show (algebraMap L (w.adicCompletion L) yL) ^ e = _
  rw [← map_pow, yL_pow_eq, xK]
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionComap_algebraMap K L v w
    (algebraMap R K (Polynomial.X : R))).symm

theorem isIntegral_yLw : IsIntegral (v.adicCompletion K) yLw :=
  ⟨gPoly, gPoly_monic, by
    rw [gPoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, yLw_pow_eq,
      sub_self]⟩

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

`e = p = 2` is prime, so it suffices to show `xK` has no `e`-th root in `v.adicCompletion K`
(`X_pow_sub_C_irreducible_of_prime`) to conclude `gPoly := X ^ e - C xK` is irreducible — this
lemma has **no characteristic restriction** (confirmed by reading its Mathlib source; the
restriction to `p ≠ 2` applies only to the separate lemma
`X_pow_sub_C_irreducible_of_prime_pow` for higher prime powers, not needed here since `e` itself
is prime). The rest of the argument is identical to the tame example. -/

theorem e_prime : Nat.Prime e := Fact.out

/-- `xK` has no `e`-th root in `v.adicCompletion K`: if `b ^ e = xK`, taking `Valued.v` and then
`WithZero.log` gives `e * WithZero.log (Valued.v b) = -1` in `ℤ`, impossible since `e ∣ 1` fails
for `e ≥ 2`. -/
theorem xK_not_pow (b : v.adicCompletion K) : b ^ e ≠ xK := by
  intro hb
  have hv : Valued.v (b ^ e) = Valued.v xK := congrArg Valued.v hb
  rw [map_pow, valuation_xK] at hv
  have hlog := congrArg WithZero.log hv
  rw [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hlog
  have hdvd : (e : ℤ) ∣ 1 := ⟨-WithZero.log (Valued.v b), by linarith⟩
  have he2 : (2 : ℤ) ≤ e := by exact_mod_cast e_prime.two_le
  have := Int.le_of_dvd one_pos hdvd
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

/-! ### `Kv⟮yLw⟯ = ⊤`

Same closed-dense-set argument as the tame example: `Kv⟮yLw⟯` is finite-dimensional over `Kv`
(from `IsIntegral Kv yLw`), hence closed in `Lw`; it contains the image of `L` (every `l : L` is a
`K`-polynomial value at `yL`, pushed through the commuting square), which is dense — no
separability or characteristic input needed anywhere in this argument. -/

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

theorem finrank_Kv_Lw : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = e := by
  rw [← LinearEquiv.finrank_eq (IntermediateField.topEquiv (F := v.adicCompletion K)
    (E := w.adicCompletion L)).toLinearEquiv, ← adjoin_yLw_eq_top]
  exact finrank_adjoin_yLw

/-! ### Field 2 is BLOCKED here — a genuine gap, not merely a missing lemma

The tame example transfers `finrank_Kv_Lw` down to the completed-*integers* level
(`Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) = e`) via
`IsIntegralClosure.rank`. Reading that lemma's actual proof (not just its printed signature) shows
it transitively needs `Algebra.IsSeparable K L`: `IsIntegralClosure.rank` calls
`IsIntegralClosure.module_free`, which calls `IsIntegralClosure.isNoetherian`, which is stated
inside a `variable [Algebra.IsSeparable K L]` section in
`Mathlib.RingTheory.DedekindDomain.IntegralClosure` (lines 146–199) precisely because its proof
builds a *dual basis with respect to the trace form* (`(traceForm K L).dualBasis
(traceForm_nondegenerate K L) b`) — and the trace form is not just unavailable but **genuinely
degenerate** for inseparable extensions (in characteristic `p`, the trace of a purely inseparable
degree-`p` extension is identically zero). This is not a formalization gap that a differently-named
Mathlib lemma would sidestep; it is a real fact about why the standard "integral basis via dual
trace basis" proof technique cannot apply here. `Langlands.AdicCompletionIntegralClosure`'s own
docstring already flags this exact restriction ("under a `Algebra.IsSeparable` hypothesis ... not in
general") for `Module.Finite`/`Module.Free` of `w.adicCompletionIntegers L` over
`v.adicCompletionIntegers K`.

Establishing `Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) = e` for a
purely inseparable extension therefore needs a genuinely different argument — the classical fact
"`O_L = O_K[π_L]` is free of rank `e`" for a totally ramified extension of complete discrete
valuation rings with a *common* residue field, proved directly (not via the trace form), e.g. by:

* a **compactness/density** argument: `v.adicCompletionIntegers K` is compact (finite residue
  field + completeness + `IsDiscreteValuationRing`, via
  `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
  or its analogue for `HeightOneSpectrum.adicCompletionIntegers`), so the continuous image of
  `(v.adicCompletionIntegers K) ^ e` under `(a_i) ↦ ∑ a_i • yLw₀ ^ i` is compact, hence closed;
  showing it contains the (dense, since `w.adicCompletionIntegers L` is open in `w.adicCompletion
  L`) image of `S` pins it down to all of `w.adicCompletionIntegers L`; or
* a **completeness-based successive-approximation** bootstrap using the residue-lifting fact proved
  below (`exists_sub_algebraMap_mem_maximalIdeal`, itself separability-free) repeatedly, folding the
  resulting convergent series back into `e` coefficients via `yLw₀ ^ e = algebraMap xK₀` (exact
  equality, no unit factor needed).

Linear independence of `{yLw₀ ^ i : i < e}` over `v.adicCompletionIntegers K` is *not* the
bottleneck — it follows directly from `Polynomial.linearIndependent_pow` at the `Kv`/`Lw` field
level (via `natDegree_minpoly_yLw`) restricted to the subring `K₀` (`LinearIndependent.restrict_scalars`).
Only *surjectivity* — every element of `w.adicCompletionIntegers L` is an actual
`v.adicCompletionIntegers K`-combination of the `yLw₀ ^ i` — needs one of the two arguments above,
and neither is built, in Mathlib or in this repo, in a form directly usable here. Building either is
comparable in scope to other genuinely new machinery in this repo (e.g. the `expEquiv`/units-filtration
thread), so it is not attempted here, to avoid leaving a broken or `sorry`-laden file.

**Consequence:** `finrank_eq` and the full three-field assembly `isTotallyRamified` are NOT built in
this file. What *is* fully built and sorry-free below is Field 3
(`exists_sub_algebraMap_mem_maximalIdeal`) and Field 1 (`map_maximalIdeal_eq`, above) — two of the
three fields `IsTotallyRamified` needs — plus the field-level (not completed-integers-level) degree
computation `finrank_Kv_Lw : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = e`. -/

/-! ### Field 3 of `IsTotallyRamified`: `exists_sub_algebraMap_mem_maximalIdeal`

Identical to the tame example — a general, single-place density fact
(`Langlands.AdicCompletionIntegersResidue.exists_algebraMap_sub_mem_maximalIdeal`) plus the
naturality square `R → K₀ → L₀ = R → S → L₀`, none of it characteristic-dependent. -/

/-- **The naturality square `R → K₀ → L₀ = R → S → L₀`.** -/
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

/-! ### What remains toward `IsTotallyRamified`, and what this instance cannot support regardless

**`IsTotallyRamified K L v w` is NOT assembled in this file.** Two of its three fields
(`map_maximalIdeal_eq` and `exists_sub_algebraMap_mem_maximalIdeal`) are proved above, sorry-free;
the third (`finrank_eq`, at the completed-*integers* level) is blocked on the genuine,
newly-identified gap documented above `exists_sub_algebraMap_mem_maximalIdeal`'s section — Mathlib's
only route to it (`IsIntegralClosure.rank`) transitively needs `Algebra.IsSeparable`, which
genuinely fails here (the trace form of a purely inseparable extension vanishes identically), and no
alternative construction exists yet.

Even setting `finrank_eq` aside, this instance has a further, independent limitation.
`index_localNormMap_range_eq_of_isTotallyRamified` (the tame capstone) requires `IsTamelyRamified`
as an explicit hypothesis, false here by construction (`p ∣ e`); more fundamentally, `L / K` is
*purely inseparable* (the Frobenius-twist extension `k(Y)/k(Y^p)`), hence not Galois, so this
instance also cannot exercise `Langlands.AdicCompletionNormExpTrace`'s `norm_exp_eq_exp_trace`
(which needs `IsGalois`) or the `expEquiv` units-filtration isomorphism of
`Langlands.NonarchimedeanExponentialUnitsIso` in any Galois-dependent way — that machinery needs a
wild instance with actual Galois structure to run on, not merely a wild `IsTotallyRamified`
witness.

A genuinely **separable, Galois, wildly ramified** degree-`p` example would need a different
construction: the Artin–Schreier extension `S := R[Y] / (X · Y ^ p - X · Y - 1)` (clearing
denominators in `Y ^ p - Y = 1 / X`, which has a simple pole at `X = 0`), which is Galois with
group `ZMod p` acting by `Y ↦ Y + i`, and totally, wildly ramified at that pole. Mathlib has **no**
Artin–Schreier irreducibility or Galois-theory machinery at all (grepping
`.lake/packages/mathlib` for "artinschreier"/"artin_schreier" returns zero hits), so proving that
polynomial's irreducibility and the resulting extension's Galois property from scratch would be
substantial new algebra — out of scope for this file, recorded here for the record of what the
actual remaining gap is.
-/

end Langlands.TotallyRamifiedWildConcreteExample

end
