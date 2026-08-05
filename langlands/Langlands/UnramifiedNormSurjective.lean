import Langlands.PrincipalUnitsCauchySequence
import Langlands.NormMapContinuity
import Langlands.UnitGroupModPrincipalUnitsSurjective
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Full unramified norm-group surjectivity

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. This file assembles the classical successive-approximation
argument (Serre, *Local Fields*, Ch. V §2-3) into the full statement `N_{L/K}(L^×) ⊇ O_K^×`, under
`IsUnramified`: **every unit of `K₀` is the norm of a unit of `L₀`.**

## Route

1. `exists_isUnit_norm_residue_eq`: the "level 0" base case — every unit `y : K₀` is the norm of
   some `x₀ : L₀ˣ` modulo `𝔪_K`, i.e. `residue K₀ (N x₀) = residue K₀ y`. Built directly from the
   residue-field norm surjectivity (`Langlands.ResidueFieldNorm`) and surjectivity of reduction on
   unit groups (`Langlands.UnitGroupModPrincipalUnitsSurjective`), via
   `residue_norm_eq_norm_residue_of_isUnramified` (`Langlands.NormMapResidueCompatibility`) —
   without needing to go through `localNormMap` at all.
2. `approxData`: a recursively-defined sequence, for each `n : ℕ`, of `x_n : L₀ˣ` and `t_n : K₀`
   with the exact multiplicative invariant `y = Algebra.norm K₀ x_n * (1 + π^{n+1}·t_n)`. The base
   case is (1); the inductive step applies the one-step correction
   `exists_one_add_uniformizer_pow_smul_norm_sub_mem` (`Langlands.PrincipalUnitsCauchySequence`)
   to `t_n`, producing `z_n : L₀` with `x_{n+1} := x_n·(1 + π^{n+1}·z_n)`.
3. `cauchySeq_approx`: the sequence `n ↦ (x_n : w.adicCompletion L)` is Cauchy. Consecutive terms
   differ by `x_n·π^{n+1}·z_n`, of norm `≤ ‖algebraMap K₀ L₀ π‖^{n+1}` (both `x_n`, `z_n` having
   norm `≤ 1`, being elements of `L₀`), and `‖algebraMap K₀ L₀ π‖ < 1` (`π` a uniformizer, so
   non-unit, so norm `< 1`); `cauchySeq_of_le_geometric` closes it. This uses the
   `NontriviallyNormedField (w.adicCompletion L)` structure already built in `Langlands.NormMap`
   (`instNontriviallyNormedFieldAdicCompletion`) — its `TopologicalSpace`/`UniformSpace` fields are
   *definitionally* `Valued.toUniformSpace`, the same instance `continuous_norm_adicCompletion`
   (`Langlands.NormMapContinuity`) is stated against, so no topology-compatibility gap arises.
4. The limit `x := lim x_n` (via `cauchySeq_tendsto_of_complete`, using
   `CompleteSpace (w.adicCompletion L)`) is shown to be a unit of `L₀` (its norm is `1`, being the
   limit of the constant-`1`-norm sequence `‖x_n‖`) and to satisfy `Algebra.norm K₀ x = y` exactly
   (continuity of the norm, `continuous_norm_adicCompletion`, applied to the invariant from (2),
   using `1 + π^{n+1}·t_n → 1`).

## Main result

* `IsDedekindDomain.HeightOneSpectrum.exists_isUnit_algebraMap_norm_eq_of_isUnramified`
-/

noncomputable section

open IsDedekindDomain IsLocalRing Filter Topology

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

omit [Algebra.IsIntegral R S] in
/-- **The base case: every unit of `K₀` is the norm of a unit of `L₀`, modulo `𝔪_K`.** Under
`IsUnramified`, for `y : K₀` a unit, there is a unit `x : L₀` with `residue K₀ (Algebra.norm K₀ x)
= residue K₀ y`. -/
theorem exists_isUnit_norm_residue_eq [Finite (ResidueField (w.adicCompletionIntegers L))]
    (hU : IsUnramified K L v w) {y : v.adicCompletionIntegers K} (hy : IsUnit y) :
    ∃ x : w.adicCompletionIntegers L, IsUnit x ∧
      residue (v.adicCompletionIntegers K) (Algebra.norm (v.adicCompletionIntegers K) x) =
        residue (v.adicCompletionIntegers K) y := by
  classical
  set t : (ResidueField (v.adicCompletionIntegers K))ˣ :=
    (Ne.isUnit ((residue_ne_zero_iff_isUnit y).mpr hy)).unit with ht
  obtain ⟨s, hs⟩ := residueField_units_norm_surjective (K := K) (L := L) (v := v) (w := w) t
  obtain ⟨xu, hxu⟩ := surjective_units_map_residue (A := w.adicCompletionIntegers L) s
  refine ⟨(xu : w.adicCompletionIntegers L), xu.isUnit, ?_⟩
  rw [residue_norm_eq_norm_residue_of_isUnramified K L v w hU]
  have hxures : residue (w.adicCompletionIntegers L) (xu : w.adicCompletionIntegers L) =
      (s : ResidueField (w.adicCompletionIntegers L)) := by
    rw [← hxu]; exact (Units.coe_map _ xu).symm
  rw [hxures]
  have hs' : Algebra.norm (ResidueField (v.adicCompletionIntegers K))
      (s : ResidueField (w.adicCompletionIntegers L)) =
      (t : ResidueField (v.adicCompletionIntegers K)) := by
    rw [← hs]; exact (Units.coe_map _ s).symm
  rw [hs']
  have : (t : ResidueField (v.adicCompletionIntegers K)) =
      residue (v.adicCompletionIntegers K) y := by
    rw [ht]; exact (Ne.isUnit ((residue_ne_zero_iff_isUnit y).mpr hy)).unit_spec
  rw [this]

/-! ### The successive-approximation sequence -/

variable [Finite (ResidueField (w.adicCompletionIntegers L))]
  {π : v.adicCompletionIntegers K}

omit [Algebra.IsIntegral R S] in
/-- The base case of the successive-approximation sequence, in exact multiplicative form: `y =
Algebra.norm K₀ x * (1 + π * t)` for some unit `x : L₀` and some `t : K₀`. -/
theorem exists_isUnit_mul_one_add_uniformizer_eq (hU : IsUnramified K L v w) (hπ : Irreducible π)
    {y : v.adicCompletionIntegers K} (hy : IsUnit y) :
    ∃ p : w.adicCompletionIntegers L × v.adicCompletionIntegers K,
      IsUnit p.1 ∧ y = Algebra.norm (v.adicCompletionIntegers K) p.1 * (1 + π ^ (0 + 1) * p.2) := by
  obtain ⟨x, hx, hxy⟩ := exists_isUnit_norm_residue_eq K L v w hU hy
  set Nx := Algebra.norm (v.adicCompletionIntegers K) x with hNxdef
  obtain ⟨Nx', hNx'0⟩ := (hx.map (Algebra.norm (v.adicCompletionIntegers K))).exists_right_inv
  have hNx' : Nx * Nx' = 1 := by rw [hNxdef]; exact hNx'0
  have hsub : y - Nx ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (Ideal.Quotient.eq).mp hxy.symm
  have hspan : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ hsub)
  refine ⟨(x, c * Nx'), hx, ?_⟩
  simp only [zero_add, pow_one]
  linear_combination -hc - (π * c) * hNx'

omit [Algebra.IsIntegral R S] in
/-- The inductive step of the successive-approximation sequence: given the invariant at level `n`,
produce a correction `z : L₀` (via `exists_one_add_uniformizer_pow_smul_norm_sub_mem`) so that
`x * (1 + π^{n+1} • z)` satisfies the invariant at level `n+1`. Exposing the new unit as literally
`x * (1 + π^{n+1} • z)` (rather than an abstractly-existing unit) keeps the multiplicative
step-to-step relationship visible to `approxData`'s recursion, for the later Cauchy-sequence
bound. -/
theorem exists_uniformizer_pow_smul_mul_one_add_uniformizer_pow_succ_eq (hU : IsUnramified K L v w)
    (hπ : Irreducible π) {y : v.adicCompletionIntegers K} (n : ℕ)
    {x : w.adicCompletionIntegers L} (hx : IsUnit x) {t : v.adicCompletionIntegers K}
    (heq : y = Algebra.norm (v.adicCompletionIntegers K) x * (1 + π ^ (n + 1) * t)) :
    ∃ z : w.adicCompletionIntegers L, ∃ t' : v.adicCompletionIntegers K,
      y = Algebra.norm (v.adicCompletionIntegers K) (x * (1 + π ^ (n + 1) • z)) *
        (1 + π ^ (n + 1 + 1) * t') := by
  obtain ⟨z, hz⟩ := exists_one_add_uniformizer_pow_smul_norm_sub_mem K L v w hU hπ n t
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hz
  set x' := x * (1 + π ^ (n + 1) • z) with hx'def
  have hx'u : IsUnit x' := hx.mul (isUnit_one_add_uniformizer_pow_smul K L v w hπ n z)
  set Nx := Algebra.norm (v.adicCompletionIntegers K) x with hNxdef
  set Nx' := Algebra.norm (v.adicCompletionIntegers K) x' with hNx'def
  obtain ⟨Nx'inv, hNx'inv0⟩ :=
    (hx'u.map (Algebra.norm (v.adicCompletionIntegers K))).exists_right_inv
  have hNx'inv : Nx' * Nx'inv = 1 := by rw [hNx'def]; exact hNx'inv0
  refine ⟨z, -(Nx * d) * Nx'inv, ?_⟩
  rw [← hx'def]
  have hmul : Nx' = Nx * Algebra.norm (v.adicCompletionIntegers K) (1 + π ^ (n + 1) • z) := by
    rw [hNx'def, hx'def, map_mul, hNxdef]
  have hNx'y : Nx' = y + Nx * d * π ^ (n + 2) := by
    rw [hmul]; linear_combination -Nx * hd - heq
  show y = Nx' * (1 + π ^ (n + 1 + 1) * (-(Nx * d) * Nx'inv))
  have hpow : π ^ (n + 1 + 1) = π ^ (n + 2) := by norm_num
  rw [hpow]
  linear_combination -hNx'y + (π ^ (n + 2) * Nx * d) * hNx'inv

variable (hU : IsUnramified K L v w) (hπ : Irreducible π) {y : v.adicCompletionIntegers K}
  (hy : IsUnit y)

omit [Algebra.IsIntegral R S] in
/-- The successive-approximation sequence: for every `n`, a unit `x_n : L₀` and an error term
`t_n : K₀` with the exact invariant `y = Algebra.norm K₀ x_n * (1 + π^{n+1}·t_n)`, together with,
for `n ≥ 1`, the correction witness `z_{n-1} : L₀` making `x_n = x_{n-1}·(1+π^n • z_{n-1})`
*definitionally* (not just propositionally) — needed so the Cauchy-sequence bound below can read
off consecutive differences directly. Built by structural recursion, choosing witnesses via
`exists_isUnit_mul_one_add_uniformizer_eq` (base) and
`exists_uniformizer_pow_smul_mul_one_add_uniformizer_pow_succ_eq` (step). -/
noncomputable def approxData :
    (n : ℕ) → {p : w.adicCompletionIntegers L × v.adicCompletionIntegers K //
      IsUnit p.1 ∧ y = Algebra.norm (v.adicCompletionIntegers K) p.1 * (1 + π ^ (n + 1) * p.2)}
  | 0 => ⟨(exists_isUnit_mul_one_add_uniformizer_eq K L v w hU hπ hy).choose,
      (exists_isUnit_mul_one_add_uniformizer_eq K L v w hU hπ hy).choose_spec⟩
  | n + 1 =>
      let ih := approxData n
      let h := exists_uniformizer_pow_smul_mul_one_add_uniformizer_pow_succ_eq K L v w hU hπ n
        ih.2.1 ih.2.2
      ⟨(ih.1.1 * (1 + π ^ (n + 1) • h.choose), h.choose_spec.choose),
        ih.2.1.mul (isUnit_one_add_uniformizer_pow_smul K L v w hπ n h.choose),
        h.choose_spec.choose_spec⟩

/-- The unit component of `approxData`. -/
noncomputable def approxUnit (n : ℕ) : w.adicCompletionIntegers L :=
  (approxData K L v w hU hπ hy n).1.1

/-- The error component of `approxData`. -/
noncomputable def approxError (n : ℕ) : v.adicCompletionIntegers K :=
  (approxData K L v w hU hπ hy n).1.2

omit [Algebra.IsIntegral R S] in
theorem isUnit_approxUnit (n : ℕ) : IsUnit (approxUnit K L v w hU hπ hy n) :=
  (approxData K L v w hU hπ hy n).2.1

omit [Algebra.IsIntegral R S] in
theorem approxUnit_norm_eq (n : ℕ) :
    y = Algebra.norm (v.adicCompletionIntegers K) (approxUnit K L v w hU hπ hy n) *
      (1 + π ^ (n + 1) * approxError K L v w hU hπ hy n) :=
  (approxData K L v w hU hπ hy n).2.2

omit [Algebra.IsIntegral R S] in
/-- Consecutive terms of the sequence differ by `x_n · π^{n+1} • z_n` for some correction witness
`z_n : L₀` — directly from `approxData`'s recursive definition. -/
theorem approxUnit_succ_eq (n : ℕ) :
    ∃ z : w.adicCompletionIntegers L,
      approxUnit K L v w hU hπ hy (n + 1) =
        approxUnit K L v w hU hπ hy n * (1 + π ^ (n + 1) • z) := by
  set ih := approxData K L v w hU hπ hy n with hihdef
  set h := exists_uniformizer_pow_smul_mul_one_add_uniformizer_pow_succ_eq K L v w hU hπ n
    ih.2.1 ih.2.2 with hhdef
  exact ⟨h.choose, rfl⟩

end IsDedekindDomain.HeightOneSpectrum

end
