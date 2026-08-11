import Langlands.CyclotomicDifferentExponent
import Langlands.TotallyRamifiedNormIndex
import Langlands.AdicCompletionNormGroupIndex

/-!
# The wild-case norm-group index, numerically, for `K = ℚ_3(ζ_3) ⊆ L = ℚ_3(ζ_9)`

Wires `TotallyRamifiedNormIndex`'s tameness-free index equality
(`index_localNormMap_range_eq_index_normUnitsK₀_of_isTotallyRamified`) and
`AdicCompletionNormGroupIndex`'s wild-case divisibility bound
(`exists_index_dvd_index_principalUnitsPow`) against the concrete mixed-characteristic wild Galois
instance of `Langlands.TotallyRamifiedCyclotomicConcreteExample`, with the different exponent `d = 6`
of `Langlands.CyclotomicDifferentExponent` plugged in.

## Main results

* `Langlands.TotallyRamifiedCyclotomicConcreteExample.index_localNormMap_range_eq_index_normUnitsK₀`
  : `[(v.adicCompletion K)ˣ : N(L_wˣ)] = [K₀ˣ : N(L₀ˣ)]` **exactly**, for this concrete wild
  instance — the valuation-side factor of `index_range_localNormMap_eq_mul` is `1` here (residue
  degree `f = 1`, matching `inertiaDeg'_eq`), even though the extension is wild.
* `Langlands.TotallyRamifiedCyclotomicConcreteExample.nat_card_residueFieldK₀_eq` /
  `nat_card_residueFieldK₀_units_eq` : the residue field of `K₀ := v.adicCompletionIntegers K` has
  `3` elements (`𝔽_3`), so its unit group has `2` elements.
* `Langlands.TotallyRamifiedCyclotomicConcreteExample.exists_index_normUnitsK₀_dvd` : the capstone
  numeric bound, `∃ j, [K₀ˣ : N(L₀ˣ)] ∣ 2 * 3 ^ j` — a genuine divisibility constraint on the
  wild-case local norm index for a concrete instance, with `j` existential (the filtration depth
  needed for the `exp`/`log`/norm-trace machinery to apply is not made explicit anywhere upstream).

## Scope

`j` remains existential: nothing in this repo computes an explicit threshold depth, nor closes the
divisibility to an equality (that would need the generic `v(N(x)) = f · w(x)` valuation formula, not
established here — see `ROADMAP.md` §6ac). This is a genuine, checked *bound*, not a computed value.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField

namespace Langlands.TotallyRamifiedCyclotomicConcreteExample

/-- `Θ₀` is irreducible in `w.adicCompletionIntegers L`, from its generating the maximal ideal
(`maximalIdeal_L₀_eq`). -/
theorem irreducible_Θ₀ : Irreducible (Θ₀ : w.adicCompletionIntegers L) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr maximalIdeal_L₀_eq

/-- **`Nat.card (ResidueField K₀) = 3`.** `ResidueField (v.adicCompletionIntegers K) ≃+* 𝓞 K ⧸
v.asIdeal` (`residueFieldQuotientRingEquiv`), and `Nat.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm
v.asIdeal = 3 ^ (v.asIdeal.inertiaDeg ℤ) = 3 ^ 1 = 3` (`Ideal.pow_inertiaDeg`,
`Ideal.absNorm_apply`, `Submodule.cardQuot_apply`), since `v.asIdeal.inertiaDeg ℤ = 1`
(`inertiaDeg_v`). -/
theorem nat_card_residueFieldK₀_eq :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = 3 := by
  haveI := v.isMaximal
  have hcard : Nat.card ((𝓞 K) ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have habs : (p : ℕ) ^ (v.asIdeal.inertiaDeg ℤ) = Ideal.absNorm v.asIdeal :=
    Ideal.pow_inertiaDeg p v.asIdeal
  rw [inertiaDeg_v, pow_one] at habs
  rw [Nat.card_congr (v.residueFieldQuotientRingEquiv (F := K)).symm.toEquiv, hcard, ← habs]

/-- **`Nat.card (ResidueField K₀)ˣ = 2`.** From `nat_card_residueFieldK₀_eq` and `Nat.card_units`
for the field `ResidueField K₀` (`Nat.card αˣ = Nat.card α - 1` for a `GroupWithZero`). -/
theorem nat_card_residueFieldK₀_units_eq :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K))ˣ = 2 := by
  rw [Nat.card_units, nat_card_residueFieldK₀_eq]

/-- **`Nat.card (ResidueField L₀) = 3`.** Same route as `nat_card_residueFieldK₀_eq`, using
`inertiaDeg_w : w.asIdeal.inertiaDeg ℤ = 1`. -/
theorem nat_card_residueFieldL₀_eq :
    Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers L)) = 3 := by
  haveI := w.isMaximal
  have hcard : Nat.card ((𝓞 L) ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have habs : (p : ℕ) ^ (w.asIdeal.inertiaDeg ℤ) = Ideal.absNorm w.asIdeal :=
    Ideal.pow_inertiaDeg p w.asIdeal
  rw [inertiaDeg_w, pow_one] at habs
  rw [Nat.card_congr (w.residueFieldQuotientRingEquiv (F := L)).symm.toEquiv, hcard, ← habs]

instance : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_Kv_Lw]; norm_num)

instance : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  Nat.finite_of_card_ne_zero (by rw [nat_card_residueFieldK₀_eq]; norm_num)

instance : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers L)) :=
  Nat.finite_of_card_ne_zero (by rw [nat_card_residueFieldL₀_eq]; norm_num)

/-- **The field-level norm index equals the `K₀ˣ`-level norm index, exactly, for this concrete
wild instance** — `TotallyRamifiedNormIndex`'s tameness-free
`index_localNormMap_range_eq_index_normUnitsK₀_of_isTotallyRamified`, instantiated at
`isTotallyRamified` and `irreducible_Θ₀`. -/
theorem index_localNormMap_range_eq_index_normUnitsK₀ :
    (MonoidHom.range
        (IsDedekindDomain.HeightOneSpectrum.localNormMap K L v w)).index =
      (MonoidHom.range
        (IsDedekindDomain.HeightOneSpectrum.normUnitsK₀ K L v w)).index :=
  IsDedekindDomain.HeightOneSpectrum.index_localNormMap_range_eq_index_normUnitsK₀_of_isTotallyRamified
    K L v w isTotallyRamified irreducible_Θ₀

/-- **The capstone: a genuine divisibility bound on the wild-case local norm index, for the
concrete instance `K = ℚ_3(ζ_3) ⊆ L = ℚ_3(ζ_9)`.** For some existential `j`, both the `K₀ˣ`-level
norm index `[K₀ˣ : N(L₀ˣ)]` — which by `index_localNormMap_range_eq_index_normUnitsK₀` above is
*exactly* the field-level index `[K_vˣ : N(L_wˣ)]` for this instance — and the relative index
`[U_{K_v} : N(L_wˣ) ⊓ U_{K_v}]` divide `2 * 3 ^ j`, obtained from
`AdicCompletionNormGroupIndex.exists_index_dvd_index_principalUnitsPow` fed `d := 6`
(`differentIdeal_eq`) and the residue-field cardinalities above (`#κ_{K₀}ˣ = 2`, `#κ_{K₀} = 3`). -/
theorem exists_index_normUnitsK₀_dvd :
    ∃ j : ℕ,
      (MonoidHom.range (IsDedekindDomain.HeightOneSpectrum.normUnitsK₀ K L v w)).index ∣
          2 * 3 ^ j ∧
        (MonoidHom.range (IsDedekindDomain.HeightOneSpectrum.localNormMap K L v w)).relIndex
            (v.adicCompletionIntegers K).units ∣ 2 * 3 ^ j := by
  obtain ⟨j, hdvd1, hdvd2⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_index_dvd_index_principalUnitsPow K L v w p
      differentIdeal_eq hnormK hnormL
  have hidx := ValuationSubring.index_principalUnitsPow (v.adicCompletionIntegers K)
    maximalIdeal_eq_span_π₀ π₀_ne_zero j
  rw [nat_card_residueFieldK₀_units_eq, nat_card_residueFieldK₀_eq] at hidx
  refine ⟨j, ?_, ?_⟩
  · rwa [hidx] at hdvd1
  · rwa [hidx] at hdvd2

/-! ### Closing `j` to a concrete numeral

`exists_map_principalUnitsPow_normUnitsK₀_eq`'s `i₀ := max (max iL iN) (iK * e) = max (max 13 7) (5
* 3) = max 13 15 = 15`, with `iL := 13` (`hthreshStrict_i₀`, `TotallyRamifiedCyclotomicConcreteExample`),
`iN := 7` (`forall_maximalIdeal_pow_norm_exp_eq_exp_trace_iN`, closing `i1 := 4`/`i3 := 7` to `iN :=
max 4 7 = 7`), `iK := 5` (`hthreshStrict_iK`), `e := 3` (`ramificationIdx'_eq`).
`lt_logUnitsThreshold_of_le` shifts `hthreshStrict_i₀`/`hthreshStrict_iK` up from their own witnesses
to the concrete `i := 15` (resp. `(15 + 6) / e = 7`) `map_principalUnitsPow_normUnitsK₀_eq` needs,
and `forall_maximalIdeal_pow_norm_exp_eq_exp_trace_iN` supplies `hexp` at that same `i := 15` (`15 ≥
max 4 7`). This closes the wild-case norm-group IMAGE to a genuine closed-form EQUALITY (not merely
existential) at the concrete numeral `i := 15`. -/

set_option linter.defProp false in
/-- `‖Θ₀‖ ^ 15 < logUnitsThreshold (w.adicCompletion L) p`, shifting `hthreshStrict_i₀` (`i := 13`)
up to `i := 15` via `lt_logUnitsThreshold_of_le`. -/
def hthreshL_i₀ :=
  IsDedekindDomain.HeightOneSpectrum.lt_logUnitsThreshold_of_le (v := w) (F := L) (p := p)
    (π := (Θ₀ : w.adicCompletion L)) hπnorm_Θ.le (i := 15) (i₀ := 13) (by norm_num) hthreshStrict_i₀

set_option linter.defProp false in
/-- `‖π₀‖ ^ ((15 + 6) / (v.asIdeal.ramificationIdx' w.asIdeal)) < logUnitsThreshold (v.adicCompletion K) p`,
shifting `hthreshStrict_iK` (`i := 5`) up to the concrete exponent `(15 + 6) / e = 7` (`e := 3`,
`ramificationIdx'_eq`) via `lt_logUnitsThreshold_of_le`. Stated with the exponent left UNREDUCED
(`(15 + 6) / (v.asIdeal.ramificationIdx' w.asIdeal)`, not the literal `7`) to match
`map_principalUnitsPow_normUnitsK₀_eq`'s hypothesis shape exactly. -/
def hthreshK_i₀ :=
  IsDedekindDomain.HeightOneSpectrum.lt_logUnitsThreshold_of_le (v := v) (F := K) (p := p)
    (π := (π₀ : v.adicCompletion K)) hπnorm_π₀.le
    (i := (15 + 6) / (v.asIdeal.ramificationIdx' w.asIdeal)) (i₀ := 5)
    (by rw [ramificationIdx'_eq]; norm_num) hthreshStrict_iK

set_option linter.defProp false in
/-- `∀ x ∈ 𝔪_{L_w}^15, N(exp x) = exp(Tr x)`, the `i := 15` instance of
`forall_maximalIdeal_pow_norm_exp_eq_exp_trace_iN` (`15 ≥ max 4 7`). -/
def hexp_i₀ := forall_maximalIdeal_pow_norm_exp_eq_exp_trace_iN 15 (by norm_num)

set_option linter.defProp false in
/-- **`Subgroup.map (normUnitsK₀ K L v w) (principalUnitsPow L₀ 15) = principalUnitsPow K₀ 7`,
EXACTLY, for the concrete instance.** Instantiates `map_principalUnitsPow_normUnitsK₀_eq`
(`AdicCompletionNormGroupImage.lean`) with every witness closed to a literal numeral: `d := 6`
(`differentIdeal_eq`), `πK := π₀`, `πL := Θ₀`, `i := 15`, giving `(i + d) / e = (15 + 6) / 3 = 7` on
the `K₀`-side. No existential anywhere — the first fully closed-form equality (not merely a bound)
in this repo's wild-case norm-group-image thread. -/
def map_principalUnitsPow_normUnitsK₀_eq_15 :=
  IsDedekindDomain.HeightOneSpectrum.map_principalUnitsPow_normUnitsK₀_eq K L v w p
    differentIdeal_eq hnormK hnormL maximalIdeal_eq_span_π₀ π₀_coe_ne_zero hπnorm_π₀
    maximalIdeal_L₀_eq Θ_ne_zero hπnorm_Θ hthreshL_i₀ hthreshK_i₀ hexp_i₀

/-- `(15 + 6) / v.asIdeal.ramificationIdx' w.asIdeal = 7`, closing the exponent
`map_principalUnitsPow_normUnitsK₀_eq_15` produces to the literal numeral `7` (`j + 1` for `j := 6`
below). -/
theorem exponent_K_i₀_eq : (15 + 6) / (v.asIdeal.ramificationIdx' w.asIdeal) = 7 := by
  rw [ramificationIdx'_eq]; norm_num

set_option linter.defProp false in
/-- **`Subgroup.map (normUnitsK₀ K L v w) (principalUnitsPow L₀ 15) = principalUnitsPow K₀ 7`**,
`map_principalUnitsPow_normUnitsK₀_eq_15` with its exponent reduced to the literal `7` via
`exponent_K_i₀_eq`. -/
def map_principalUnitsPow_normUnitsK₀_eq_15_7 :=
  exponent_K_i₀_eq ▸ map_principalUnitsPow_normUnitsK₀_eq_15

set_option linter.defProp false in
/-- **`(MonoidHom.range (normUnitsK₀ K L v w)).index ∣ (principalUnitsPow K₀ 7).index`** and the
matching relative-index bound — the `i := 15`, `j := 6` instantiation of
`exists_index_dvd_index_principalUnitsPow`'s two divisibility conclusions, built directly from
`map_principalUnitsPow_normUnitsK₀_eq_15_7` (an EQUALITY, stronger than what the generic existential
proof produces) via `Subgroup.index_dvd_of_le`/`relIndex_range_localNormMap_units_dvd_index_map_normUnitsK₀`,
mirroring `AdicCompletionNormGroupIndex.exists_index_dvd_index_principalUnitsPow`'s own proof
verbatim but with `i := 15`, `j := 6` concrete throughout. -/
def index_normUnitsK₀_dvd_index_principalUnitsPow_7 :
    (MonoidHom.range (IsDedekindDomain.HeightOneSpectrum.normUnitsK₀ K L v w)).index ∣
        (ValuationSubring.principalUnitsPow (v.adicCompletionIntegers K) 7).index ∧
      (MonoidHom.range (IsDedekindDomain.HeightOneSpectrum.localNormMap K L v w)).relIndex
          (v.adicCompletionIntegers K).units ∣
        (ValuationSubring.principalUnitsPow (v.adicCompletionIntegers K) 7).index :=
  ⟨map_principalUnitsPow_normUnitsK₀_eq_15_7 ▸
      Subgroup.index_dvd_of_le (Subgroup.map_le_range _ _),
    map_principalUnitsPow_normUnitsK₀_eq_15_7 ▸
      IsDedekindDomain.HeightOneSpectrum.relIndex_range_localNormMap_units_dvd_index_map_normUnitsK₀
        K L v w _⟩

/-- **The final concrete numeral: `[K₀ˣ : N(L₀ˣ)] ∣ 2 * 3 ^ 6`, and the matching relative-index
bound, for the concrete instance `K = ℚ_3(ζ_3) ⊆ L = ℚ_3(ζ_9)`.** The `j := 6` instantiation of
`exists_index_normUnitsK₀_dvd` above, with `j` closed to a literal numeral throughout — no
existential anywhere in the chain from `exp`/`log` (`i1 := 4`, `i3 := 7`) through the norm-group
image (`i := 15`) to this index bound. Still a genuine DIVISIBILITY bound, not an equality: the
upstream `ValuationSubring.index_principalUnitsPow`/`relIndex_range_localNormMap_units_dvd_index_map_normUnitsK₀`
route only ever produces `∣`, never `=`. -/
theorem index_normUnitsK₀_dvd_two_mul_three_pow_six :
    (MonoidHom.range (IsDedekindDomain.HeightOneSpectrum.normUnitsK₀ K L v w)).index ∣
        2 * 3 ^ (6 : ℕ) ∧
      (MonoidHom.range (IsDedekindDomain.HeightOneSpectrum.localNormMap K L v w)).relIndex
          (v.adicCompletionIntegers K).units ∣ 2 * 3 ^ (6 : ℕ) := by
  have hidx := ValuationSubring.index_principalUnitsPow (v.adicCompletionIntegers K)
    maximalIdeal_eq_span_π₀ π₀_ne_zero 6
  rw [nat_card_residueFieldK₀_units_eq, nat_card_residueFieldK₀_eq] at hidx
  obtain ⟨hdvd1, hdvd2⟩ := index_normUnitsK₀_dvd_index_principalUnitsPow_7
  exact ⟨hidx ▸ hdvd1, hidx ▸ hdvd2⟩

end Langlands.TotallyRamifiedCyclotomicConcreteExample

end
