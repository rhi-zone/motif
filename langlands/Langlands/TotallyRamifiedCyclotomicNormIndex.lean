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

end Langlands.TotallyRamifiedCyclotomicConcreteExample

end
