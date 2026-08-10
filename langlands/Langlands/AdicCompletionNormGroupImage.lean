import Langlands.AdicCompletionNormExpTrace
import Langlands.AdicCompletionTraceSurjectivity
import Langlands.NonarchimedeanExponentialAdicCompletion
import Langlands.TotallyRamifiedNormResidueImage

/-!
# The exact norm-group image of a filtration level, `N_{L_w/K_v}(U_{L_w}^{(i)}) = U_{K_v}^{(j₀)}`

Let `K₀ := v.adicCompletionIntegers K`, `L₀ := w.adicCompletionIntegers L`, `e :=
v.asIdeal.ramificationIdx' w.asIdeal`, and let `d` be the different exponent
(`differentIdeal K₀ L₀ = 𝔪_{L₀} ^ d`). This file transports the additive trace-image formula of
`Langlands.AdicCompletionTraceSurjectivity`,

`Tr_{L_w/K_v}(𝔪_{L₀} ^ i) = 𝔪_{K₀} ^ ((i + d) / e)`,

across the exponential to the multiplicative side, giving the **exact** norm-group image of a
principal-units filtration level:

`N_{L_w/K_v}(U_{L₀}^{(i)}) = U_{K₀}^{((i + d) / e)}`

for `i` above a threshold — an *equality* of subgroups of `K₀ˣ`, not merely a containment or an
index. This is the wild-case counterpart of `Langlands.TotallyRamifiedNormIndex`'s tame formula:
it is unconditional on tameness, and at the top of the filtration it computes the norm group on the
nose.

## Route

Three inputs, each already closed elsewhere, meet here:

1. **`expEquiv` on both sides.** `exp` is a group isomorphism `𝔪^i ≅ U^{(i)}` above the strict
   `logUnitsThreshold` threshold (`Langlands.NonarchimedeanExponentialUnitsIso`). Only its two
   element-level halves are used: `exp_mem_principalUnitsPow` (every `exp` of `𝔪^i` is a unit of
   `U^{(i)}`) and `exists_mem_maximalIdeal_pow_coe_eq_exp` (its converse, i.e. surjectivity).
2. **`norm_exp_eq_exp_trace`.** Under `exp`, the norm on `L_w` corresponds to the trace
   (`Langlands.AdicCompletionNormExpTrace`); `exists_maximalIdeal_pow_norm_exp_eq_exp_trace`
   supplies it uniformly on a deep enough filtration level.
3. **The trace-image equality** of `Langlands.AdicCompletionTraceSurjectivity`, which is what makes
   the conclusion an equality rather than a containment: the *surjectivity* half of the trace
   formula is exactly what produces preimages for the `⊇` direction.

Both directions of the subgroup equality then reduce to one computation, `key` in the proof below:
if `u_L ∈ L₀ˣ` and `u_K ∈ K₀ˣ` satisfy `u_L = exp x` and `u_K = exp a` in the ambient fields, with
`Tr x = a`, then `N(u_L) = u_K`. Indeed `N` and `exp` commute with the passage from the integers to
the ambient field (`algebraMap_norm_eq_norm_algebraMap`), the field-level norm of `exp x` is
`exp (Tr x)` by input 2, and `algebraMap K₀ K_v` is injective. The `⊆` direction feeds it the trace
containment, the `⊇` direction the trace surjectivity.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.map_principalUnitsPow_normUnitsK₀_eq` : the equality, with the
  two uniformizers, the two filtration thresholds, and the norm/trace compatibility all as explicit
  hypotheses.
* `IsDedekindDomain.HeightOneSpectrum.exists_map_principalUnitsPow_normUnitsK₀_eq` : the packaged
  form, `∃ i₀, ∀ i ≥ i₀, …`, with every threshold produced internally.

## Scope

`d` is a hypothesis (`differentIdeal K₀ L₀ = 𝔪_{L₀} ^ d`) rather than derived, exactly as in
`Langlands.AdicCompletionTraceSurjectivity`; see that file's docstring. `IsGalois K_v L_w` is
inherited from `norm_exp_eq_exp_trace`. Filtration levels *below* the threshold are untouched: the
`exp`/`log` correspondence is unavailable there, and a different argument is needed.
-/

noncomputable section

open IsDedekindDomain IsLocalRing IsLocalization NonarchimedeanExponential

namespace IsDedekindDomain.HeightOneSpectrum

section Injective

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F]

/-- The inclusion `𝒪_{F_v} → F_v` is injective: it is the coercion of a subring. -/
theorem algebraMap_adicCompletion_injective (v : HeightOneSpectrum A) :
    Function.Injective (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) :=
  fun _ _ h => Subtype.ext h

end Injective

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [FiniteDimensional (v.adicCompletion K) (w.adicCompletion L)]

variable [CharZero K] [CharZero L] (p : ℕ) [hp : Fact p.Prime]

omit [Algebra.IsIntegral R S] in
/-- **The exact norm-group image of a filtration level.**

`N_{L_w/K_v}(U_{L₀}^{(i)}) = U_{K₀}^{((i + d) / e)}`, as subgroups of `K₀ˣ`, with `d` the different
exponent and `e = v.asIdeal.ramificationIdx' w.asIdeal`.

The hypotheses are: uniformizers `π_K`, `π_L` of the two integer rings; that `i` (resp.
`(i + d) / e`) is above the strict `logUnitsThreshold` at which `exp` is a bijection
`𝔪^i ≅ U^{(i)}`; and `hexp`, the norm/trace compatibility on `𝔪_{L₀}^i` supplied by
`exists_maximalIdeal_pow_norm_exp_eq_exp_trace`. See
`exists_map_principalUnitsPow_normUnitsK₀_eq` for the form in which all of these are produced
internally. -/
theorem map_principalUnitsPow_normUnitsK₀_eq {d : ℕ}
    (hd : differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      maximalIdeal (w.adicCompletionIntegers L) ^ d)
    (hnormK : ‖(p : v.adicCompletion K)‖ < 1) (hnormL : ‖(p : w.adicCompletion L)‖ < 1)
    {πK : v.adicCompletionIntegers K}
    (hπK : maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span ({πK} : Set (v.adicCompletionIntegers K)))
    (hπK0 : (πK : v.adicCompletion K) ≠ 0) (hπKnorm : ‖(πK : v.adicCompletion K)‖ < 1)
    {πL : w.adicCompletionIntegers L}
    (hπL : maximalIdeal (w.adicCompletionIntegers L) =
      Ideal.span ({πL} : Set (w.adicCompletionIntegers L)))
    (hπL0 : (πL : w.adicCompletion L) ≠ 0) (hπLnorm : ‖(πL : w.adicCompletion L)‖ < 1) {i : ℕ}
    (hthreshL : ‖(πL : w.adicCompletion L)‖ ^ i < logUnitsThreshold (w.adicCompletion L) p)
    (hthreshK : ‖(πK : v.adicCompletion K)‖ ^ ((i + d) / v.asIdeal.ramificationIdx' w.asIdeal) <
      logUnitsThreshold (v.adicCompletion K) p)
    (hexp : ∀ x : w.adicCompletionIntegers L, x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
      Algebra.norm (v.adicCompletion K) (exp hnormL (x : w.adicCompletion L)) =
        exp hnormK (Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
          (x : w.adicCompletion L))) :
    Subgroup.map (normUnitsK₀ K L v w)
        (ValuationSubring.principalUnitsPow (w.adicCompletionIntegers L) i) =
      ValuationSubring.principalUnitsPow (v.adicCompletionIntegers K)
        ((i + d) / v.asIdeal.ramificationIdx' w.asIdeal) := by
  have htrace := map_trace_coeSubmodule_maximalIdeal_pow_adicCompletion K L v w hd i
  set j₀ := (i + d) / v.asIdeal.ramificationIdx' w.asIdeal with hj₀
  have hAK := mem_adicCompletionIntegers_iff_norm_le_one (F := K) v
  have hAL := mem_adicCompletionIntegers_iff_norm_le_one (F := L) w
  have hinjK := algebraMap_adicCompletion_injective (F := K) v
  -- The single computation both directions reduce to.
  have key : ∀ (x : w.adicCompletionIntegers L),
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
      ∀ (uL : (w.adicCompletionIntegers L)ˣ) (a : v.adicCompletionIntegers K)
        (uK : (v.adicCompletionIntegers K)ˣ),
      ((uL : w.adicCompletionIntegers L) : w.adicCompletion L)
          = exp hnormL (x : w.adicCompletion L) →
      Algebra.trace (v.adicCompletion K) (w.adicCompletion L) (x : w.adicCompletion L)
          = (a : v.adicCompletion K) →
      ((uK : v.adicCompletionIntegers K) : v.adicCompletion K)
          = exp hnormK (a : v.adicCompletion K) →
      normUnitsK₀ K L v w uL = uK := by
    intro x hx uL a uK huL ha huK
    apply Units.ext
    apply hinjK
    have hcoe : ((normUnitsK₀ K L v w uL : (v.adicCompletionIntegers K)ˣ) :
        v.adicCompletionIntegers K)
        = Algebra.norm (v.adicCompletionIntegers K) (uL : w.adicCompletionIntegers L) := rfl
    rw [hcoe, algebraMap_norm_eq_norm_algebraMap K L v w]
    have hcast : algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
        (uL : w.adicCompletionIntegers L) = exp hnormL (x : w.adicCompletion L) := huL
    rw [hcast, hexp x hx, ha]
    exact huK.symm
  apply le_antisymm
  · rw [SetLike.le_def]
    rintro u hu
    obtain ⟨uL, huLmem, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨x, hx, hxeq⟩ := exists_mem_maximalIdeal_pow_coe_eq_exp
      (A := w.adicCompletionIntegers L) (hA := hAL) hnormL hπL hπL0 hπLnorm hthreshL huLmem
    have hmem : Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
        (x : w.adicCompletion L) ∈
        coeSubmodule (v.adicCompletion K)
          (maximalIdeal (v.adicCompletionIntegers K) ^ j₀) := by
      rw [← htrace]
      exact ⟨(x : w.adicCompletion L), ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨a, ha, haeq⟩ := hmem
    obtain ⟨uK, huKmem, huKeq⟩ := exp_mem_principalUnitsPow (v.adicCompletionIntegers K) hAK
      hnormK hπK hπK0 hπKnorm
      (hthreshK.trans_le (logUnitsThreshold_le_expUnitsThreshold hnormK)).le ha
    rw [key x hx uL a uK hxeq haeq.symm huKeq]
    exact huKmem
  · rw [SetLike.le_def]
    intro uK huKmem
    obtain ⟨a, ha, haeq⟩ := exists_mem_maximalIdeal_pow_coe_eq_exp
      (A := v.adicCompletionIntegers K) (hA := hAK) hnormK hπK hπK0 hπKnorm hthreshK huKmem
    have hmem : (a : v.adicCompletion K) ∈
        Submodule.map ((Algebra.trace (v.adicCompletion K) (w.adicCompletion L)).restrictScalars
            (v.adicCompletionIntegers K))
          (Submodule.restrictScalars (v.adicCompletionIntegers K)
            (coeSubmodule (w.adicCompletion L)
              (maximalIdeal (w.adicCompletionIntegers L) ^ i))) := by
      rw [htrace]
      exact ⟨a, ha, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := hmem
    obtain ⟨x, hx, hxeq⟩ := hz
    obtain ⟨uL, huLmem, huLeq⟩ := exp_mem_principalUnitsPow (w.adicCompletionIntegers L) hAL
      hnormL hπL hπL0 hπLnorm
      (hthreshL.trans_le (logUnitsThreshold_le_expUnitsThreshold hnormL)).le hx
    refine Subgroup.mem_map.mpr ⟨uL, huLmem, ?_⟩
    refine key x hx uL a uK huLeq ?_ haeq
    rw [← hxeq] at hzeq
    exact hzeq

omit [Algebra.IsIntegral R S] in
/-- **The exact norm-group image of a filtration level, packaged.** Some `i₀` has

`N_{L_w/K_v}(U_{L₀}^{(i)}) = U_{K₀}^{((i + d) / e)}`

for every `i ≥ i₀`, with no further hypotheses. The threshold combines three separate ones: the
`logUnitsThreshold` bound on the `L`-side at level `i`, the same bound on the `K`-side at level
`(i + d) / e` (reached because `e ≠ 0` makes `(i + d) / e` grow with `i`), and the level above which
`norm_exp_eq_exp_trace` applies uniformly. -/
theorem exists_map_principalUnitsPow_normUnitsK₀_eq
    [IsGalois (v.adicCompletion K) (w.adicCompletion L)] {d : ℕ}
    (hd : differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      maximalIdeal (w.adicCompletionIntegers L) ^ d)
    (hnormK : ‖(p : v.adicCompletion K)‖ < 1) (hnormL : ‖(p : w.adicCompletion L)‖ < 1) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀,
      Subgroup.map (normUnitsK₀ K L v w)
          (ValuationSubring.principalUnitsPow (w.adicCompletionIntegers L) i) =
        ValuationSubring.principalUnitsPow (v.adicCompletionIntegers K)
          ((i + d) / v.asIdeal.ramificationIdx' w.asIdeal) := by
  have he0 : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  obtain ⟨πK, hπKirr⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨πL, hπLirr⟩ := IsDiscreteValuationRing.exists_irreducible (w.adicCompletionIntegers L)
  have hπK : maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span ({πK} : Set (v.adicCompletionIntegers K)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer πK).mp hπKirr
  have hπL : maximalIdeal (w.adicCompletionIntegers L) =
      Ideal.span ({πL} : Set (w.adicCompletionIntegers L)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer πL).mp hπLirr
  have hπK0 : (πK : v.adicCompletion K) ≠ 0 := fun h => hπKirr.ne_zero (Subtype.ext h)
  have hπL0 : (πL : w.adicCompletion L) ≠ 0 := fun h => hπLirr.ne_zero (Subtype.ext h)
  have hπKmem : πK ∈ maximalIdeal (v.adicCompletionIntegers K) := by
    rw [hπK]; exact Ideal.mem_span_singleton_self _
  have hπLmem : πL ∈ maximalIdeal (w.adicCompletionIntegers L) := by
    rw [hπL]; exact Ideal.mem_span_singleton_self _
  have hπKnorm : ‖(πK : v.adicCompletion K)‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mpr (valued_lt_one_of_mem_maximalIdeal v hπKmem)
  have hπLnorm : ‖(πL : w.adicCompletion L)‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mpr (valued_lt_one_of_mem_maximalIdeal w hπLmem)
  obtain ⟨iL, hiL⟩ := exists_pow_lt_logUnitsThreshold (F := L) w p hπLnorm
  obtain ⟨iK, hiK⟩ := exists_pow_lt_logUnitsThreshold (F := K) v p hπKnorm
  obtain ⟨iN, hiN⟩ := exists_maximalIdeal_pow_norm_exp_eq_exp_trace K L v w p hnormK hnormL
  refine ⟨max (max iL iN) (iK * v.asIdeal.ramificationIdx' w.asIdeal), fun i hi => ?_⟩
  have hiL' : iL ≤ i := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hi
  have hiN' : iN ≤ i := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hi
  have hiK' : iK ≤ (i + d) / v.asIdeal.ramificationIdx' w.asIdeal := by
    rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero he0)]
    have := le_trans (le_max_right _ _) hi
    omega
  exact map_principalUnitsPow_normUnitsK₀_eq K L v w p hd hnormK hnormL hπK hπK0 hπKnorm hπL hπL0
    hπLnorm (hiL i hiL') (hiK _ hiK') (fun x hx => hiN i hiN' x hx)

end IsDedekindDomain.HeightOneSpectrum

end
