import Langlands.NormMapResidueCompatibility
import Langlands.ResidueFieldNorm

/-!
# `localNormMap` is surjective on unit groups modulo principal units

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. This file closes the milestone scoped in `ROADMAP.md`'s
Phase 2a "fifth pass" entry: composing `Langlands.ResidueFieldNorm`'s
`residueField_units_norm_surjective` (`𝓀[L]ˣ ↠ 𝓀[K]ˣ`) with the surjectivity of reduction mod the
maximal ideal on unit groups (a general fact for any local ring, `IsLocalRing.residue_surjective`
transported to units) and `Langlands.NormMapResidueCompatibility`'s `localNormMap_reduce` gives:
under `IsUnramified`, the composite

`O_L^× → 𝓀[L]^× --(residue field norm)--> 𝓀[K]^×`

agrees with `a ↦ residue (localNormMap a)`, hence is surjective. Since `𝓀[K]^× ≅ O_K^× / (1+𝔪_K)`
(the unit group modulo the principal units, `ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits`,
not invoked by name here since the statement below targets `(ResidueField K₀)ˣ` directly, which is
the same group), this is exactly `O_L^× ↠ O_K^× / (1 + 𝔪_K)`.

## Main result

* `IsDedekindDomain.HeightOneSpectrum.localNormMap_units_surjective_mod_principalUnits`
-/

noncomputable section

open IsDedekindDomain IsLocalRing

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

/-- Reduction mod the maximal ideal is surjective on unit groups, for any local ring: a general
consequence of `IsLocalRing.residue_surjective` and `IsLocalRing.surjective_units_map_of_local_ringHom`. -/
theorem surjective_units_map_residue {A : Type*} [CommRing A] [IsLocalRing A] :
    Function.Surjective (Units.map (IsLocalRing.residue A).toMonoidHom) :=
  IsLocalRing.surjective_units_map_of_local_ringHom (IsLocalRing.residue A)
    IsLocalRing.residue_surjective inferInstance

omit [Algebra.IsIntegral R S] in
/-- **`localNormMap` is surjective on unit groups modulo principal units.** Under `IsUnramified`,
for every target `t : (ResidueField K₀)ˣ` (equivalently, every class in `O_K^× / (1 + 𝔪_K)`), there
is a local unit `a` of `L₀ = w.adicCompletionIntegers L` whose norm `localNormMap K L v w a`
reduces, modulo `𝔪_K`, to `t`. -/
theorem localNormMap_units_surjective_mod_principalUnits
    [Finite (ResidueField (w.adicCompletionIntegers L))] (hU : IsUnramified K L v w)
    (t : (ResidueField (v.adicCompletionIntegers K))ˣ) :
    ∃ a : (w.adicCompletion L)ˣ, ∃ ha : a ∈ (w.adicCompletionIntegers L).units,
      Units.map (IsLocalRing.residue (v.adicCompletionIntegers K)).toMonoidHom
          ((v.adicCompletionIntegers K).unitsEquivUnitsType
            (⟨localNormMap K L v w a, localNormMap_mem_units K L v w ha⟩ :
              ↥((v.adicCompletionIntegers K).units))) = t := by
  classical
  obtain ⟨s, hs⟩ := residueField_units_norm_surjective (K := K) (L := L) (v := v) (w := w) t
  obtain ⟨y, hy⟩ := surjective_units_map_residue (A := w.adicCompletionIntegers L) s
  set a₀ : ↥((w.adicCompletionIntegers L).units) :=
    (w.adicCompletionIntegers L).unitsEquivUnitsType.symm y with ha₀
  refine ⟨(a₀ : (w.adicCompletion L)ˣ), a₀.2, ?_⟩
  apply Units.ext
  have hy' : (w.adicCompletionIntegers L).unitsEquivUnitsType a₀ = y := by
    rw [ha₀]; exact (w.adicCompletionIntegers L).unitsEquivUnitsType.apply_symm_apply y
  have hval : ((Units.map (IsLocalRing.residue (v.adicCompletionIntegers K)).toMonoidHom
        ((v.adicCompletionIntegers K).unitsEquivUnitsType
          (⟨localNormMap K L v w (a₀ : (w.adicCompletion L)ˣ),
            localNormMap_mem_units K L v w a₀.2⟩ :
            ↥((v.adicCompletionIntegers K).units))) : ResidueField (v.adicCompletionIntegers K)))
      = residue (v.adicCompletionIntegers K)
          ⟨(localNormMap K L v w (a₀ : (w.adicCompletion L)ˣ) : v.adicCompletion K),
            Submonoid.val_mem_of_mem_units _ (localNormMap_mem_units K L v w a₀.2)⟩ := rfl
  have hval' : ((Units.map (IsLocalRing.residue (w.adicCompletionIntegers L)).toMonoidHom
        ((w.adicCompletionIntegers L).unitsEquivUnitsType a₀) :
        ResidueField (w.adicCompletionIntegers L)))
      = residue (w.adicCompletionIntegers L)
          ⟨((a₀ : (w.adicCompletion L)ˣ) : w.adicCompletion L),
            Submonoid.val_mem_of_mem_units _ a₀.2⟩ := rfl
  rw [hval, ← hs, Units.coe_map, localNormMap_reduce K L v w hU a₀.2]
  congr 1
  rw [← hval', hy', hy]

end IsDedekindDomain.HeightOneSpectrum

end
