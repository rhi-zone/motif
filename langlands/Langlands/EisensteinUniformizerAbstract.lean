/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.EisensteinMonogenicAbstract
import Langlands.TotallyRamifiedUniformizer
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# A bare-Eisenstein generator is a uniformizer, with no `ValuativeRel`/`NormedField`

`Langlands/EisensteinMonogenicAbstract.lean` extracts monogenicity
(`adjoin_eq_integralClosure_of_isEisensteinAt`) from `Langlands/TotallyRamifiedEisenstein.lean`'s
`spectralNorm`/`ValuativeRel`-based proof, stated for an arbitrary integrally closed
`IsDiscreteValuationRing` base `R`. This file does the same for
`Langlands/TotallyRamifiedUniformizer.lean`'s sharper conclusion — that the generator, viewed
inside the integral closure, is itself irreducible there (a uniformizer) — replacing the
`hram : ‖ϖ‖ = spectralNorm K L π ^ n` total-ramification hypothesis with a bare
`hEis : (minpoly R β).IsEisensteinAt (maximalIdeal R)` hypothesis.

This is exactly the tool the `K_1 → K_2` tower step needs and the `K_1` level did not: at `K_1`,
the generator's Eisenstein-ness and total ramification were both derived from a `hram` condition
stated in terms of `K`'s norm (available because `K` carries `ValuativeRel`/`NormedField`
structure). At `nextSplittingField`, the "base field" one level up is `K_1 P`, and
`Langlands/LubinTateTowerStepMonogenic.lean`'s docstring records — and this file's own probing
confirms — that `K_1 P` deliberately carries **no** `ValuativeRel`/`NormedField` instance (giving
it one reproduces a non-defeq diamond against the existing `spectralNorm`-based
`K_1.instNontriviallyNormedField`). So the `K_1`-level route through `spectralNorm K (K_1 P) _`
cannot be repeated one level up with `K_1 P` playing the role of the base field. What *is* already
available one level up is the Eisenstein data itself: the Weierstrass-factorization step already
produces `P₂` Eisenstein at `𝔪_{O_{K_1}}` directly (no norm computation), so a version of the
uniformizer machinery that consumes Eisenstein-ness as a bare hypothesis, rather than deriving it
from `hram`, is exactly what closes the gap.

## Main results

* `isLocalHom_algebraMap_integralClosure_of_isIntegrallyClosed` : `algebraMap R ↥(integralClosure
  R L)` is local, for any integrally closed domain `R` with fraction field `K` and any field
  extension `L / K`. Generalizes `LocalField.isLocalHom_algebraMap_integralClosure`
  (`Langlands/MonogenicIntegralClosure.lean`), whose proof is specific to `R := ↥𝒪[K]`
  (`ValuativeRel`-canonical) and uses `mem_valuationSubring_of_isIntegral_algebraMap` where this
  file uses the general `IsIntegrallyClosed.isIntegral_iff`.
* `mem_maximalIdeal_of_isWeaklyEisensteinAt` : a root of a monic weakly-Eisenstein-at-`𝔪_R`
  polynomial, evaluated in any local `R`-algebra `S` with `algebraMap R S` local, lies in `𝔪_S`.
  Proved via Mathlib's `Polynomial.IsWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_
  mem_map` (`β ^ n ∈ 𝔪_R.map (algebraMap R S)`) combined with `IsLocalRing.map_maximalIdeal_le`
  (`𝔪_R.map (algebraMap R S) ≤ 𝔪_S`, from `IsLocalHom`) and primality of `𝔪_S`.
* `coeff_zero_associated_of_isEisensteinAt` : for `R` an integrally closed `IsDiscreteValuationRing`
  and `p` Eisenstein at `𝔪_R` with a chosen uniformizer `ϖ`, `p.coeff 0` is an associate of `ϖ`.
  The bare-Eisenstein analogue of `LocalField.coeff_zero_minpoly_associated_of_isUniformizer`,
  whose derivation of the underlying `IsEisensteinAt` fact from `hram` is skipped since `hEis` is
  now a direct hypothesis.
* `adjoin_singleton_eq_top_of_adjoin_eq_integralClosure` : the `Subalgebra R ↥(integralClosure R
  L)` form of monogenicity — `Algebra.adjoin R {⟨β, hβint⟩} = ⊤` — from the `Subalgebra R L` form
  `Algebra.adjoin R {β} = integralClosure R L`. The abstraction of
  `LocalField.adjoin_singleton_eq_top_of_isUniformizer`
  (`Langlands/TotallyRamifiedResidueField.lean`), whose proof needs no `ValuativeRel`/`NormedField`
  structure to begin with.
* `maximalIdeal_eq_span_of_isEisensteinAt` / `irreducible_of_isEisensteinAt` : **the headline
  results.** `𝔪_{↥(integralClosure R L)} = (⟨β, hβint⟩)`, hence `⟨β, hβint⟩` is irreducible there —
  i.e. a uniformizer. The bare-Eisenstein analogues of
  `LocalField.maximalIdeal_integralClosure_eq_span_of_isUniformizer` /
  `LocalField.irreducible_of_isUniformizer`.

## What the caller still has to supply

Unlike the `ValuativeRel`-based route, this file does *not* itself supply
`[IsLocalRing ↥(integralClosure R L)]` / `[IsDiscreteValuationRing ↥(integralClosure R L)]` — at
`R := ↥𝒪[K]` those came for free from `ValuationSubring.isDiscreteValuationRing_of_comap_eq`
(`Langlands/MonogenicIntegralClosure.lean`), a construction specific to the `ValuativeRel`-canonical
valuation subring. At a moving base such as `R := O_{K_1}` these instances are **not** free from
`R`'s own structure; they are exactly what `Langlands/IntegralClosureTower.lean`'s general
`RingEquiv`-transport (`§62`) supplies, given the *base*-relative (`R₀ := ↥𝒪[K]`-relative) instances
`Langlands/MonogenicIntegralClosure.lean` already provides. The caller is expected to stage them via
that transport before invoking `irreducible_of_isEisensteinAt`.
-/

open Polynomial IsLocalRing

/-- **`algebraMap R ↥(integralClosure R L)` is local**, for `R` an integrally closed domain with
fraction field `K` and `L / K` any field extension. If `r : R` becomes a unit `s` of the integral
closure, then `s`, viewed in `L`, equals `(algebraMap R K r)⁻¹`; being integral over `R`
(`s.2`, transported along the injective `algebraMap K L`), it lies in the image of `algebraMap R K`
(`R` integrally closed), giving an inverse of `r` inside `R` itself. Generalizes
`LocalField.isLocalHom_algebraMap_integralClosure`. -/
theorem isLocalHom_algebraMap_integralClosure_of_isIntegrallyClosed
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] :
    IsLocalHom (algebraMap R ↥(integralClosure R L)) := by
  constructor
  intro r hr
  obtain ⟨s, hs⟩ := hr.exists_right_inv
  have hsL : algebraMap K L (algebraMap R K r) * (s : L) = 1 := by
    have := congrArg (Subtype.val) hs
    simpa [IsScalarTower.algebraMap_apply R K L] using this
  have hr0 : algebraMap R K r ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hsL
    exact zero_ne_one hsL
  have hsval : (s : L) = algebraMap K L (algebraMap R K r)⁻¹ := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsL)
  have hint : IsIntegral R (algebraMap R K r)⁻¹ := by
    have hs2 : IsIntegral R (s : L) := s.2
    rw [hsval] at hs2
    exact (isIntegral_algebraMap_iff (R := R) (A := K) (B := L)
      (algebraMap K L).injective).mp hs2
  obtain ⟨r', hr'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine IsUnit.of_mul_eq_one (a := r) r' ?_
  have : algebraMap R K (r * r') = algebraMap R K 1 := by
    rw [map_mul, map_one, hr']
    exact mul_inv_cancel₀ hr0
  exact IsFractionRing.injective R K this

/-- **A root of a monic weakly-Eisenstein-at-`𝔪_R` polynomial lies in `𝔪_S`**, for any local
`R`-algebra `S` with `algebraMap R S` local. Via `IsWeaklyEisensteinAt.pow_natDegree_le_of_aeval_
zero_of_monic_mem_map`, `β ^ n ∈ (𝔪_R).map (algebraMap R S)` for `n` the mapped polynomial's degree;
`IsLocalRing.map_maximalIdeal_le` pushes this into `𝔪_S`, and `𝔪_S` being prime (maximal ideals
always are) then forces `β ∈ 𝔪_S`. -/
theorem mem_maximalIdeal_of_isWeaklyEisensteinAt
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    {f : R[X]} (hf : f.IsWeaklyEisensteinAt (maximalIdeal R)) (hfmo : f.Monic)
    {β : S} (hβ : Polynomial.aeval β f = 0) :
    β ∈ maximalIdeal S := by
  have hmem := hf.pow_natDegree_le_of_aeval_zero_of_monic_mem_map hβ hfmo
    (f.map (algebraMap R S)).natDegree le_rfl
  have hle := IsLocalRing.map_maximalIdeal_le (algebraMap R S)
  exact (IsLocalRing.maximalIdeal.isMaximal S).isPrime.mem_of_pow_mem _ (hle hmem)

/-- **The constant coefficient of an Eisenstein-at-`𝔪_R` polynomial is an associate of a chosen
uniformizer `ϖ`.** The bare-Eisenstein analogue of `LocalField.coeff_zero_minpoly_associated_of_
isUniformizer`: in a discrete valuation ring every nonzero element is an associate of `ϖ ^ m`
(`IsDiscreteValuationRing.associated_pow_irreducible`), and `m = 0` is excluded by `coeff 0 ∈ 𝔪_R`,
`m ≥ 2` by `coeff 0 ∉ 𝔪_R ^ 2`. -/
theorem coeff_zero_associated_of_isEisensteinAt
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {p : R[X]}
    (hEis : p.IsEisensteinAt (maximalIdeal R)) (hdeg : 0 < p.natDegree) :
    Associated (p.coeff 0) ϖ := by
  have hmem : p.coeff 0 ∈ maximalIdeal R := hEis.mem hdeg
  have hnsq : p.coeff 0 ∉ maximalIdeal R ^ 2 := hEis.notMem
  have hne : p.coeff 0 ≠ 0 := fun h0 => hnsq (h0 ▸ Ideal.zero_mem _)
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ
  match m, hv with
  | 0, hv =>
    exact absurd (IsUnit.of_mul_eq_one _ (by simpa using hv))
      ((IsLocalRing.mem_maximalIdeal _).mp hmem)
  | 1, hv => exact ⟨v, by simpa using hv⟩
  | (m + 2), hv =>
    refine absurd ?_ hnsq
    have ha : p.coeff 0 = ϖ ^ (m + 2) * ((v⁻¹ : Rˣ) : R) := by
      rw [← hv, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨ϖ ^ m * ((v⁻¹ : Rˣ) : R), by rw [ha]; ring⟩

/-- **The `Subalgebra R ↥(integralClosure R L)` form of monogenicity.** From `Algebra.adjoin R {β}
= integralClosure R L` (subalgebras of `L`), every `b : ↥(integralClosure R L)` is `aeval
⟨β, hβint⟩ p` for some `p : R[X]` — the same `p` witnessing `(b : L) = aeval β p`, transported along
the injective inclusion `Subalgebra.val`. The abstraction of `LocalField.adjoin_singleton_eq_top_
of_isUniformizer`. -/
theorem adjoin_singleton_eq_top_of_adjoin_eq_integralClosure
    {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L]
    {β : L} (hβint : IsIntegral R β)
    (hadjL : Algebra.adjoin R ({β} : Set L) = integralClosure R L) :
    Algebra.adjoin R ({(⟨β, hβint⟩ : ↥(integralClosure R L))} :
        Set ↥(integralClosure R L)) = ⊤ := by
  refine Algebra.eq_top_iff.mpr fun b => ?_
  have hb : (b : L) ∈ Algebra.adjoin R ({β} : Set L) := by
    rw [hadjL]; exact b.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨p, hp⟩ := hb
  have hp' : Polynomial.aeval β p = (b : L) := hp
  have hval : Polynomial.aeval (⟨β, hβint⟩ : ↥(integralClosure R L)) p = b := by
    have haeval := Polynomial.aeval_algHom_apply
      (Subalgebra.val (integralClosure R L)) (⟨β, hβint⟩ : ↥(integralClosure R L)) p
    refine Subtype.ext ?_
    simpa [hp'] using haeval.symm
  rw [← hval, Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨p, rfl⟩

/-- **`𝔪_{↥(integralClosure R L)} = (⟨β, hβint⟩)`**, for `β` with Eisenstein-at-`𝔪_R` minimal
polynomial generating `L / K` (`hgen`). The bare-Eisenstein analogue of `LocalField.maximalIdeal_
integralClosure_eq_span_of_isUniformizer`: `IsLocalRing.maximalIdeal_eq_span_of_adjoin_singleton`
(`Langlands/TotallyRamifiedUniformizer.lean`, itself already `ValuativeRel`-free) reduces this to
`β ∈ 𝔪_{↥(integralClosure R L)}` (`mem_maximalIdeal_of_isWeaklyEisensteinAt`) and `𝔪_R ↦ (β)` (the
same Eisenstein-relation computation as the concrete file, with `coeff_zero_associated_of_
isEisensteinAt` supplying `coeff 0 ~ ϖ` directly instead of via `hram`).

Unlike the `R := ↥𝒪[K]` case, `[IsLocalRing ↥(integralClosure R L)]` is **not** derived here — it
must be supplied by the caller (see the module docstring). -/
theorem maximalIdeal_eq_span_of_isEisensteinAt
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsLocalRing ↥(integralClosure R L)]
    {ϖ : R} (hϖ : Irreducible ϖ) {β : L} (hβint : IsIntegral R β)
    (hEis : (minpoly R β).IsEisensteinAt (maximalIdeal R))
    (hgen : (minpoly K β).natDegree = Module.finrank K L) :
    maximalIdeal ↥(integralClosure R L) =
      Ideal.span {(⟨β, hβint⟩ : ↥(integralClosure R L))} := by
  haveI := isLocalHom_algebraMap_integralClosure_of_isIntegrallyClosed (R := R) (K := K) (L := L)
  have hEis' := hEis
  rw [hϖ.maximalIdeal_eq] at hEis'
  have hadjL := adjoin_eq_integralClosure_of_isEisensteinAt hϖ hβint hEis' hgen
  have hadjS := adjoin_singleton_eq_top_of_adjoin_eq_integralClosure hβint hadjL
  have hβaeval : Polynomial.aeval (⟨β, hβint⟩ : ↥(integralClosure R L)) (minpoly R β) = 0 := by
    have haeval := Polynomial.aeval_algHom_apply
      (Subalgebra.val (integralClosure R L)) (⟨β, hβint⟩ : ↥(integralClosure R L)) (minpoly R β)
    refine Subtype.ext ?_
    simpa [minpoly.aeval] using haeval.symm
  have hβmem : (⟨β, hβint⟩ : ↥(integralClosure R L)) ∈ maximalIdeal ↥(integralClosure R L) :=
    mem_maximalIdeal_of_isWeaklyEisensteinAt hEis.isWeaklyEisensteinAt (minpoly.monic hβint)
      hβaeval
  refine IsLocalRing.maximalIdeal_eq_span_of_adjoin_singleton hβmem hadjS ?_
  set q : R[X] := minpoly R β with hq
  have hdegpos : 0 < q.natDegree := minpoly.natDegree_pos hβint
  obtain ⟨w, hw⟩ := coeff_zero_associated_of_isEisensteinAt hϖ hEis hdegpos
  have haevalS : Polynomial.aeval
      (⟨β, hβint⟩ : ↥(integralClosure R L)) q = 0 := hβaeval
  have hkey : Polynomial.aeval
      (⟨β, hβint⟩ : ↥(integralClosure R L))
        (Polynomial.X * q.divX + Polynomial.C (q.coeff 0)) = 0 := by
    rw [Polynomial.X_mul_divX_add]; exact haevalS
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hkey
  have hc0span : algebraMap R ↥(integralClosure R L) (q.coeff 0) ∈
      Ideal.span {(⟨β, hβint⟩ : ↥(integralClosure R L))} := by
    have heq : algebraMap R ↥(integralClosure R L) (q.coeff 0) =
        -((⟨β, hβint⟩ : ↥(integralClosure R L)) *
          Polynomial.aeval (⟨β, hβint⟩ : ↥(integralClosure R L)) q.divX) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hkey
    rw [heq]
    exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hϖspan : algebraMap R ↥(integralClosure R L) ϖ ∈
      Ideal.span {(⟨β, hβint⟩ : ↥(integralClosure R L))} := by
    rw [← hw, map_mul]
    exact Ideal.mul_mem_right _ _ hc0span
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff]
  exact hϖspan

/-- **`⟨β, hβint⟩` is irreducible in `↥(integralClosure R L)`** — i.e. it is a uniformizer. The
bare-Eisenstein analogue of `LocalField.irreducible_of_isUniformizer`, immediate from
`maximalIdeal_eq_span_of_isEisensteinAt` via `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
This is the `Irreducible α'` input `Langlands/LubinTateTowerStep.lean`'s `TowerStep` section needs
of its moving base, at any level of the tower for which the Eisenstein data is directly at hand
(rather than derived from a `spectralNorm` total-ramification condition). -/
theorem irreducible_of_isEisensteinAt
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsDiscreteValuationRing ↥(integralClosure R L)]
    {ϖ : R} (hϖ : Irreducible ϖ) {β : L} (hβint : IsIntegral R β)
    (hEis : (minpoly R β).IsEisensteinAt (maximalIdeal R))
    (hgen : (minpoly K β).natDegree = Module.finrank K L) :
    Irreducible (⟨β, hβint⟩ : ↥(integralClosure R L)) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (maximalIdeal_eq_span_of_isEisensteinAt hϖ hβint hEis hgen)
