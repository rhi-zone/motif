import Langlands.NormTraceLinearization
import Langlands.NormMapContinuity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Successive approximation on the principal-units filtration

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. This file contains the classical successive-approximation
argument (Serre, *Local Fields*, Ch. V §2-3) that turns *approximate* norm-surjectivity, level by
level along the principal-units filtration, into *exact* norm-surjectivity — with **no ramification
hypothesis of any kind**.

It was extracted from `Langlands.UnramifiedNormSurjective`, where it was originally written
against `IsUnramified` directly, once `Langlands.TotallyRamifiedNormSurjective` needed the same
machinery for the tame totally-ramified case. Nothing in it ever used unramifiedness except through
the two inputs it now takes as hypotheses:

* `hcorr`, the one-step correction: every residual error `t : K₀` at filtration level `n` is
  matched, mod `π^{n+2}`, by the norm of some `1 + π^{n+1} • z`. In the unramified case this is
  `Langlands.PrincipalUnitsCauchySequence`'s
  `exists_one_add_uniformizer_pow_smul_norm_sub_mem` (via surjectivity of the residue-field trace);
  in the tame totally-ramified case it is `Langlands.TotallyRamifiedNormSurjective`'s
  `exists_one_add_uniformizer_pow_smul_norm_sub_mem_of_isTotallyRamified` (via invertibility of
  `e` in `𝓀[K]`).
* `hbase`, the level-`0` base case: `y = N(x₀)·(1 + π·t₀)` for some unit `x₀ : L₀`.

## Route

1. `approxData`: a recursively-defined sequence, for each `n : ℕ`, of `x_n : L₀ˣ` and `t_n : K₀`
   with the exact multiplicative invariant `y = Algebra.norm K₀ x_n * (1 + π^{n+1}·t_n)`. The base
   case is `hbase`; the inductive step applies `hcorr` to `t_n`, producing `z_n : L₀` with
   `x_{n+1} := x_n·(1 + π^{n+1}·z_n)`.
2. `cauchySeq_approxUnit`: the sequence `n ↦ (x_n : w.adicCompletion L)` is Cauchy. Consecutive
   terms differ by `x_n·π^{n+1}·z_n`, of norm `≤ ‖algebraMap K₀ L₀ π‖^{n+1}` (both `x_n`, `z_n`
   having norm `≤ 1`, being elements of `L₀`), and `‖algebraMap K₀ L₀ π‖ < 1` (`π` a uniformizer,
   so non-unit, so norm `< 1`); `cauchySeq_of_le_geometric` closes it. This uses the
   `NontriviallyNormedField (w.adicCompletion L)` structure already built in `Langlands.NormMap`
   (`instNontriviallyNormedFieldAdicCompletion`) — its `TopologicalSpace`/`UniformSpace` fields are
   *definitionally* `Valued.toUniformSpace`, the same instance `continuous_norm_adicCompletion`
   (`Langlands.NormMapContinuity`) is stated against, so no topology-compatibility gap arises.
3. The limit `x := lim x_n` (via `cauchySeq_tendsto_of_complete`, using
   `CompleteSpace (w.adicCompletion L)`) is shown to be a unit of `L₀` (its norm is `1`, being the
   limit of the constant-`1`-norm sequence `‖x_n‖`) and to satisfy `Algebra.norm K₀ x = y` exactly
   (continuity of the norm, `continuous_norm_adicCompletion`, applied to the invariant from (1),
   using `1 + π^{n+1}·t_n → 1`).

## Main result

* `IsDedekindDomain.HeightOneSpectrum.exists_isUnit_norm_eq_of_correction`
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

variable {π : v.adicCompletionIntegers K}

/-- **The one-step correction hypothesis.** For every filtration level `n` and every residual error
`t : K₀`, some `1 + π^{n+1} • z` (with `z : L₀`) has norm congruent to `1 + π^{n+1}·t` mod
`π^{n+2}`.

Read against the successive-approximation sketch: if `N(x) ≡ y \pmod{π^{n+1}}`, writing
`y·N(x)⁻¹ = 1 + π^{n+1}·t`, this `z` gives `x' := x·(1+π^{n+1}•z)` with `N(x') ≡ y \pmod{π^{n+2}}` —
one filtration level closer. This is the *only* place ramification data enters the
successive-approximation argument. -/
abbrev OneStepCorrection (π : v.adicCompletionIntegers K) : Prop :=
  ∀ (n : ℕ) (t : v.adicCompletionIntegers K),
    ∃ z : w.adicCompletionIntegers L,
      Algebra.norm (v.adicCompletionIntegers K) (1 + π ^ (n + 1) • z) -
        (1 + π ^ (n + 1) * t) ∈ Ideal.span {π ^ (n + 2)}

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- The inductive step of the successive-approximation sequence: given the invariant at level `n`,
produce a correction `z : L₀` (via `hcorr`) so that `x * (1 + π^{n+1} • z)` satisfies the invariant
at level `n+1`. Exposing the new unit as literally `x * (1 + π^{n+1} • z)` (rather than an
abstractly-existing unit) keeps the multiplicative step-to-step relationship visible to
`approxData`'s recursion, for the later Cauchy-sequence bound. -/
theorem exists_uniformizer_pow_smul_mul_one_add_uniformizer_pow_succ_eq
    (hcorr : OneStepCorrection K L v w π) (hπ : Irreducible π)
    {y : v.adicCompletionIntegers K} (n : ℕ)
    {x : w.adicCompletionIntegers L} (hx : IsUnit x) {t : v.adicCompletionIntegers K}
    (heq : y = Algebra.norm (v.adicCompletionIntegers K) x * (1 + π ^ (n + 1) * t)) :
    ∃ z : w.adicCompletionIntegers L, ∃ t' : v.adicCompletionIntegers K,
      y = Algebra.norm (v.adicCompletionIntegers K) (x * (1 + π ^ (n + 1) • z)) *
        (1 + π ^ (n + 1 + 1) * t') := by
  obtain ⟨z, hz⟩ := hcorr n t
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

variable (hcorr : OneStepCorrection K L v w π) (hπ : Irreducible π)
  {y : v.adicCompletionIntegers K}
  (hbase : ∃ p : w.adicCompletionIntegers L × v.adicCompletionIntegers K,
    IsUnit p.1 ∧ y = Algebra.norm (v.adicCompletionIntegers K) p.1 * (1 + π ^ (0 + 1) * p.2))

omit [Algebra.IsIntegral R S] in
/-- The successive-approximation sequence: for every `n`, a unit `x_n : L₀` and an error term
`t_n : K₀` with the exact invariant `y = Algebra.norm K₀ x_n * (1 + π^{n+1}·t_n)`, together with,
for `n ≥ 1`, the correction witness `z_{n-1} : L₀` making `x_n = x_{n-1}·(1+π^n • z_{n-1})`
*definitionally* (not just propositionally) — needed so the Cauchy-sequence bound below can read
off consecutive differences directly. Built by structural recursion, choosing witnesses via
`hbase` (base) and `exists_uniformizer_pow_smul_mul_one_add_uniformizer_pow_succ_eq` (step). -/
noncomputable def approxData :
    (n : ℕ) → {p : w.adicCompletionIntegers L × v.adicCompletionIntegers K //
      IsUnit p.1 ∧ y = Algebra.norm (v.adicCompletionIntegers K) p.1 * (1 + π ^ (n + 1) * p.2)}
  | 0 => ⟨hbase.choose, hbase.choose_spec⟩
  | n + 1 =>
      let ih := approxData n
      let h := exists_uniformizer_pow_smul_mul_one_add_uniformizer_pow_succ_eq K L v w hcorr hπ n
        ih.2.1 ih.2.2
      ⟨(ih.1.1 * (1 + π ^ (n + 1) • h.choose), h.choose_spec.choose),
        ih.2.1.mul (isUnit_one_add_uniformizer_pow_smul K L v w hπ n h.choose),
        h.choose_spec.choose_spec⟩

/-- The unit component of `approxData`. -/
noncomputable def approxUnit (n : ℕ) : w.adicCompletionIntegers L :=
  (approxData K L v w hcorr hπ hbase n).1.1

/-- The error component of `approxData`. -/
noncomputable def approxError (n : ℕ) : v.adicCompletionIntegers K :=
  (approxData K L v w hcorr hπ hbase n).1.2

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
theorem isUnit_approxUnit (n : ℕ) : IsUnit (approxUnit K L v w hcorr hπ hbase n) :=
  (approxData K L v w hcorr hπ hbase n).2.1

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
theorem approxUnit_norm_eq (n : ℕ) :
    y = Algebra.norm (v.adicCompletionIntegers K) (approxUnit K L v w hcorr hπ hbase n) *
      (1 + π ^ (n + 1) * approxError K L v w hcorr hπ hbase n) :=
  (approxData K L v w hcorr hπ hbase n).2.2

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- Consecutive terms of the sequence differ by `x_n · π^{n+1} • z_n` for some correction witness
`z_n : L₀` — directly from `approxData`'s recursive definition. -/
theorem approxUnit_succ_eq (n : ℕ) :
    ∃ z : w.adicCompletionIntegers L,
      approxUnit K L v w hcorr hπ hbase (n + 1) =
        approxUnit K L v w hcorr hπ hbase n * (1 + π ^ (n + 1) • z) := by
  set ih := approxData K L v w hcorr hπ hbase n with hihdef
  set h := exists_uniformizer_pow_smul_mul_one_add_uniformizer_pow_succ_eq K L v w hcorr hπ n
    ih.2.1 ih.2.2 with hhdef
  exact ⟨h.choose, rfl⟩

/-! ### The sequence is Cauchy -/

omit [Algebra.IsIntegral R S] in
/-- Elements of `L₀` have norm `≤ 1` in `w.adicCompletion L`. -/
theorem norm_coe_le_one_of_adicCompletionIntegers (a : w.adicCompletionIntegers L) :
    ‖(a : w.adicCompletion L)‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr ((mem_adicCompletionIntegers S L w).mp a.2)

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- The image of the uniformizer `π` in `L₀` has norm `< 1` in `w.adicCompletion L`. -/
theorem norm_algebraMap_uniformizer_lt_one (hπ : Irreducible π) :
    ‖(algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π :
        w.adicCompletion L)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  have hmem : algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π ∈
      maximalIdeal (w.adicCompletionIntegers L) :=
    map_maximalIdeal_le K L v w
      (Ideal.mem_map_of_mem _ (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π))
  exact (Valuation.mem_maximalIdeal_iff (w.adicCompletion L)
    (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)).mp hmem

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- **The successive-approximation sequence is Cauchy.** Consecutive terms differ by
`x_n · π^{n+1} • z_n` (`approxUnit_succ_eq`), of norm `≤ ‖algebraMap π‖^{n+1}` (both `x_n`, `z_n`
being elements of `L₀`, of norm `≤ 1`); `‖algebraMap π‖ < 1`
(`norm_algebraMap_uniformizer_lt_one`), so `cauchySeq_of_le_geometric` applies. -/
theorem cauchySeq_approxUnit :
    CauchySeq (fun n => (approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L)) := by
  set r := ‖(algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π :
      w.adicCompletion L)‖ with hrdef
  have hr : r < 1 := norm_algebraMap_uniformizer_lt_one K L v w hπ
  refine cauchySeq_of_le_geometric r r hr (fun n => ?_)
  obtain ⟨z, hz⟩ := approxUnit_succ_eq K L v w hcorr hπ hbase n
  rw [dist_comm, dist_eq_norm, hz]
  have hdiff : (approxUnit K L v w hcorr hπ hbase n : w.adicCompletionIntegers L) *
        (1 + π ^ (n + 1) • z) - approxUnit K L v w hcorr hπ hbase n =
      approxUnit K L v w hcorr hπ hbase n *
        (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) (π ^ (n + 1)) * z) :=
    by rw [Algebra.smul_def]; ring
  show ‖((approxUnit K L v w hcorr hπ hbase n * (1 + π ^ (n + 1) • z) -
      approxUnit K L v w hcorr hπ hbase n : w.adicCompletionIntegers L) : w.adicCompletion L)‖ ≤
    r * r ^ n
  rw [hdiff]
  push_cast
  rw [norm_mul, norm_mul, norm_pow]
  calc ‖(approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L)‖ *
        (‖(algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π :
          w.adicCompletion L)‖ ^ (n + 1) * ‖(z : w.adicCompletion L)‖)
      ≤ 1 * (r ^ (n + 1) * 1) := by
        gcongr
        · exact norm_coe_le_one_of_adicCompletionIntegers (L := L) (w := w) _
        · exact norm_coe_le_one_of_adicCompletionIntegers (L := L) (w := w) z
    _ = r * r ^ n := by rw [one_mul, mul_one, pow_succ']

/-! ### The limit is a unit with the exact norm `y` -/

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- Every term of the sequence has norm exactly `1` in `w.adicCompletion L` (each `approxUnit n`
being a unit of `L₀`: norm `≤ 1` since it lies in `L₀`, and norm `≥ 1` since its inverse — also in
`L₀` — has norm `≤ 1` too). -/
theorem norm_approxUnit_eq_one (n : ℕ) :
    ‖(approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L)‖ = 1 := by
  have h1 : ‖(approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L)‖ ≤ 1 :=
    norm_coe_le_one_of_adicCompletionIntegers (L := L) (w := w) _
  set u := (isUnit_approxUnit K L v w hcorr hπ hbase n).unit with hudef
  have hinv_le : ‖((u⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletion L)‖ ≤ 1 :=
    norm_coe_le_one_of_adicCompletionIntegers (L := L) (w := w)
      ((u⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L)
  have hmul : (approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L) *
      ((u⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletion L) = 1 := by
    have hu3 : ((u : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L) =
        approxUnit K L v w hcorr hπ hbase n := hudef ▸ rfl
    rw [← hu3]
    have h4 : ((u : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L) *
        ((u⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L) = 1 :=
      u.mul_inv
    exact_mod_cast h4
  have h2 : (1 : ℝ) ≤ ‖(approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L)‖ := by
    have hle : ‖(approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L)‖ *
        ‖((u⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletion L)‖ ≤
        ‖(approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hinv_le
    calc (1 : ℝ) = ‖(1 : w.adicCompletion L)‖ := (norm_one).symm
      _ = ‖(approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L) *
          ((u⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletion L)‖ := by rw [hmul]
      _ = ‖(approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L)‖ *
          ‖((u⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletion L)‖ := norm_mul _ _
      _ ≤ ‖(approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L)‖ := hle
  exact le_antisymm h1 h2

omit [Algebra.IsIntegral R S] in
/-- The image of `π` in `v.adicCompletion K` (via `algebraMap K₀ (v.adicCompletion K)`) has norm
`< 1`. -/
theorem norm_algebraMap_adicCompletion_uniformizer_lt_one (hπ : Irreducible π) :
    ‖(algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π : v.adicCompletion K)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  have hmem : π ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  exact (Valuation.mem_maximalIdeal_iff (v.adicCompletion K)
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).mp hmem

omit [Algebra.IsIntegral R S] in
include hcorr hπ hbase in
/-- **Exact norm-surjectivity from level-by-level approximate norm-surjectivity.** Given the
one-step correction `hcorr` at every filtration level and the level-`0` base case `hbase`, the
target `y : K₀` is the exact norm `Algebra.norm K₀ x` of some unit `x` of `L₀`.

No ramification hypothesis: all ramification data is carried by `hcorr` and `hbase`. -/
theorem exists_isUnit_norm_eq_of_correction :
    ∃ x : w.adicCompletionIntegers L, IsUnit x ∧
      Algebra.norm (v.adicCompletionIntegers K) x = y := by
  classical
  obtain ⟨xL, hxL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_approxUnit K L v w hcorr hπ hbase)
  -- The limit has norm exactly 1, hence lies in `L₀` and is a unit there.
  have hconst : Filter.Tendsto
      (fun n => ‖(approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L)‖)
      Filter.atTop (nhds 1) := by
    simp [norm_approxUnit_eq_one K L v w hcorr hπ hbase]
  have hnormxL : ‖xL‖ = 1 := tendsto_nhds_unique hxL.norm hconst
  have hval_le : Valued.v xL ≤ 1 := Valued.toNormedField.norm_le_one_iff.mp hnormxL.le
  have hval_ge : (1 : ℤᵐ⁰) ≤ Valued.v xL := Valued.toNormedField.one_le_norm_iff.mp hnormxL.ge
  have hval_eq : Valued.v xL = 1 := le_antisymm hval_le hval_ge
  set xL₀ : w.adicCompletionIntegers L := ⟨xL, (mem_adicCompletionIntegers S L w).mpr hval_le⟩
    with hxL₀def
  have hxL₀u : IsUnit xL₀ :=
    adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hval_eq
  refine ⟨xL₀, hxL₀u, ?_⟩
  -- Push the invariant `y = N(x_n) * (1 + π^{n+1} t_n)` through `algebraMap K₀ (v.adicCompletion
  -- K)` and take limits.
  have hinj : Function.Injective
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) :=
    Subtype.coe_injective
  apply hinj
  have herr : Filter.Tendsto
      (fun n => (1 : v.adicCompletion K) +
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^ (n + 1) *
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            (approxError K L v w hcorr hπ hbase n))
      Filter.atTop (nhds 1) := by
    have hzero : Filter.Tendsto
        (fun n => (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^ (n + 1) *
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            (approxError K L v w hcorr hπ hbase n))
        Filter.atTop (nhds 0) := by
      apply squeeze_zero_norm (a := fun n =>
        ‖(algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π :
          v.adicCompletion K)‖ ^ (n + 1))
      · intro n
        rw [norm_mul, norm_pow]
        calc ‖(algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π :
              v.adicCompletion K)‖ ^ (n + 1) *
              ‖algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
                (approxError K L v w hcorr hπ hbase n)‖
            ≤ ‖(algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π :
              v.adicCompletion K)‖ ^ (n + 1) * 1 := by
              gcongr
              exact Valued.toNormedField.norm_le_one_iff.mpr
                (approxError K L v w hcorr hπ hbase n).2
          _ = ‖(algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π :
              v.adicCompletion K)‖ ^ (n + 1) := mul_one _
      · have hlt := norm_algebraMap_adicCompletion_uniformizer_lt_one K v hπ
        have hzero' := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt
        exact hzero'.comp (Filter.tendsto_add_atTop_nat 1)
    simpa using hzero.const_add 1
  have hnormeq : ∀ n, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (Algebra.norm (v.adicCompletionIntegers K) (approxUnit K L v w hcorr hπ hbase n)) *
        ((1 : v.adicCompletion K) +
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^ (n + 1) *
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
              (approxError K L v w hcorr hπ hbase n)) := by
    intro n
    have := congrArg (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
      (approxUnit_norm_eq K L v w hcorr hπ hbase n)
    simpa using this
  have hlim1 : Filter.Tendsto
      (fun _ : ℕ => algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y)
      Filter.atTop
      (nhds (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y)) :=
    tendsto_const_nhds
  have hlim2 : Filter.Tendsto
      (fun n => algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (Algebra.norm (v.adicCompletionIntegers K) (approxUnit K L v w hcorr hπ hbase n)) *
        ((1 : v.adicCompletion K) +
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^ (n + 1) *
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
              (approxError K L v w hcorr hπ hbase n)))
      Filter.atTop
      (nhds (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (Algebra.norm (v.adicCompletionIntegers K) xL₀) * 1)) := by
    apply Filter.Tendsto.mul _ herr
    have hcont : Filter.Tendsto
        (fun n => algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (Algebra.norm (v.adicCompletionIntegers K) (approxUnit K L v w hcorr hπ hbase n)))
        Filter.atTop
        (nhds (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (Algebra.norm (v.adicCompletionIntegers K) xL₀))) := by
      have heq : ∀ n, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            (Algebra.norm (v.adicCompletionIntegers K)
              (approxUnit K L v w hcorr hπ hbase n)) =
          Algebra.norm (v.adicCompletion K)
            (approxUnit K L v w hcorr hπ hbase n : w.adicCompletion L) :=
        fun n => algebraMap_norm_eq_norm_algebraMap K L v w
          (approxUnit K L v w hcorr hπ hbase n)
      have heq' : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            (Algebra.norm (v.adicCompletionIntegers K) xL₀) =
          Algebra.norm (v.adicCompletion K) xL := algebraMap_norm_eq_norm_algebraMap K L v w xL₀
      simp_rw [heq]
      rw [heq']
      exact (continuous_norm_adicCompletion K L v w).continuousAt.tendsto.comp hxL
    exact hcont
  have hlim2' : Filter.Tendsto
      (fun _ : ℕ => algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y)
      Filter.atTop
      (nhds (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (Algebra.norm (v.adicCompletionIntegers K) xL₀) * 1)) :=
    Filter.Tendsto.congr (fun n => (hnormeq n).symm) hlim2
  have hfin := tendsto_nhds_unique hlim1 hlim2'
  rw [mul_one] at hfin
  exact hfin.symm

end IsDedekindDomain.HeightOneSpectrum

end
