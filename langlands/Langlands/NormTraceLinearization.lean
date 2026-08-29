import Langlands.NormMapResidueCompatibility
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The norm linearizes to the trace on the principal-units filtration

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`, `𝓀[K] := IsLocalRing.ResidueField K₀`,
`𝓀[L] := IsLocalRing.ResidueField L₀`. This file proves the classical fact that the norm,
restricted to a graded piece `1 + 𝔪_K^i` of the principal-units filtration, acts as the trace on
the residue field — one step of upgrading `O_L^× ↠ O_K^× / (1+𝔪_K)`
(`Langlands.UnitGroupModPrincipalUnitsSurjective`) to the full unramified norm-group theorem.

## Route

1. `Algebra.exists_norm_one_add_smul_eq` (general, no valuation content, no local-ring content
   even): for `S` a finite free `R`-algebra, `t : R`, `x : S`, `Algebra.norm R (1 + t • x)` equals
   `1 + t * Algebra.trace R x` up to a multiple of `t ^ 2`. This is exactly the determinant Taylor
   expansion `Matrix.det_one_add_smul` applied to the matrix of left multiplication by `x` in a
   chosen basis — the standard fact that "the norm looks like the trace infinitesimally near `1`".
2. `IsLocalRing.residue_trace_eq_trace_residue` (general, no valuation content): the trace analogue
   of `IsLocalRing.residue_norm_eq_norm_residue` (`Langlands.NormMapResidueCompatibility`) — for `S`
   a finite free algebra over a local ring `R`, `Algebra.trace` commutes with reduction mod the
   maximal ideal. Easier than the norm case: trace is a sum of diagonal entries, so it commutes
   with any ring hom applied entrywise (`AddMonoidHom.map_trace`), no determinant needed.
3. Specializing (2) to `R := K₀`, `S := L₀` under `IsUnramified` (to identify the quotient
   `L₀ ⧸ 𝔪_K · L₀` with `𝓀[L] = L₀ ⧸ 𝔪_L`, exactly as `NormMapResidueCompatibility`'s
   `residue_norm_eq_norm_residue_of_isUnramified` does for the norm) gives
   `residue_trace_eq_trace_residue_of_isUnramified`.
4. Combining (1) (with `t := π ^ (n+1)` for a uniformizer `π` of `K₀`, `n : ℕ`) and (3): for
   `x : L₀`, `Algebra.norm K₀ (1 + π ^ (n+1) • x) = 1 + π ^ (n+1) * y` for some `y : K₀` whose
   residue in `𝓀[K]` is `Algebra.trace 𝓀[K]` of the residue of `x` in `𝓀[L]`. This is the
   norm-linearizes-to-trace identity on the `(n+1)`-th graded piece of the principal-units
   filtration, for every `n` (not just `n = 0`) — the same proof works uniformly for all filtration
   levels, since it only uses `π ^ (n+1) ∈ 𝔪_K`, which holds for every `n ≥ 0`. This is
   `exists_norm_one_add_uniformizer_pow_smul_eq_trace_add` below.

## Scope

This proves the *algebraic identity* underlying "the norm acts as the trace on each graded piece",
in the form `N(1 + π^{n+1} x) = 1 + π^{n+1} y` with `residue y = trace (residue x)`. It does **not**
construct the quotient groups `(1 + 𝔪_L^{n+1}) / (1 + 𝔪_L^{n+2})` / `(1 + 𝔪_K^{n+1}) / (1 + 𝔪_K^{n+2})`
as bundled objects or phrase the result as a genuine group homomorphism between them — building that
group-theoretic packaging (and connecting `1 + π^{n+1} • x` to actual local units and to
`localNormMap`, rather than working at the `Algebra.norm K₀`/`Algebra.trace K₀` ring level) is left
to the Cauchy-sequence argument (`Langlands.PrincipalUnitsCauchySequence`), for which this file's
identity is the input.

## Main results

* `Algebra.exists_norm_one_add_smul_eq`
* `IsLocalRing.residue_trace_eq_trace_residue`
* `IsDedekindDomain.HeightOneSpectrum.residue_trace_eq_trace_residue_of_isUnramified`
* `IsDedekindDomain.HeightOneSpectrum.exists_norm_one_add_uniformizer_pow_smul_eq_trace_add`
-/

noncomputable section

open IsDedekindDomain IsLocalRing

open scoped WithZero

/-! ### General fact: the norm at `1` linearizes to the trace, up to a multiple of `t ^ 2` -/

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  [Module.Free R S]

/-- For `S` a finite free `R`-algebra, `t : R`, `x : S`, the norm `Algebra.norm R (1 + t • x)`
equals `1 + t * Algebra.trace R x` up to a multiple of `t ^ 2` — the first-order Taylor expansion
of the norm at `1` in the direction `x`.

Proved via `Matrix.det_one_add_smul`, the determinant Taylor expansion, applied to the matrix of
left multiplication by `x` in a chosen basis: `Algebra.leftMulMatrix b (1 + t • x) = 1 + t •
Algebra.leftMulMatrix b x` (since `leftMulMatrix b` is an `R`-algebra hom), whose determinant's
first two Taylor coefficients are `1` and `(leftMulMatrix b x).trace = Algebra.trace R x`
(`Algebra.trace_eq_matrix_trace`). -/
theorem exists_norm_one_add_smul_eq (t : R) (x : S) :
    ∃ c : R, norm R (1 + t • x) = 1 + t * trace R S x + t ^ 2 * c := by
  classical
  set b := Module.Free.chooseBasis R S with hb
  have hlm : Algebra.leftMulMatrix b (1 + t • x) = 1 + t • Algebra.leftMulMatrix b x := by
    rw [map_add, map_one, map_smul]
  rw [norm_eq_matrix_det b, trace_eq_matrix_trace b, hlm, Matrix.det_one_add_smul]
  exact ⟨_, by
    rw [mul_comm ((Algebra.leftMulMatrix b) x).trace t, mul_comm _ (t ^ 2)]⟩

end Algebra

/-! ### General fact: `Algebra.trace` commutes with reduction mod the maximal ideal -/

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Finite R S] [Module.Free R S]

/-- For `S` a finite free algebra over a local ring `R`, the trace `Algebra.trace R : S → R`
commutes with reduction mod the maximal ideal: reducing the trace mod `𝔪_R` agrees with taking the
trace, over the residue field `R ⧸ 𝔪_R`, of the reduction of the element mod `𝔪_R · S`.

The trace analogue of `IsLocalRing.residue_norm_eq_norm_residue`
(`Langlands.NormMapResidueCompatibility`), and easier: `Algebra.trace` is the sum of the diagonal
entries of `Algebra.leftMulMatrix`, which commutes with any ring hom applied entrywise
(`AddMonoidHom.map_trace`), no determinant needed. -/
theorem residue_trace_eq_trace_residue (x : S) :
    Ideal.Quotient.mk (maximalIdeal R) (Algebra.trace R S x) =
      Algebra.trace (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) x) := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace (basisQuotient b),
    AddMonoidHom.map_trace (Ideal.Quotient.mk (maximalIdeal R))]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [basisQuotient_apply, ← map_mul, basisQuotient_repr]

/-- A version of `residue_trace_eq_trace_residue` for an arbitrary ideal `I` of `S` known equal to
`Ideal.map (algebraMap R S) (maximalIdeal R)`, and an arbitrary `Algebra (R ⧸ maximalIdeal R)
(S ⧸ I)` instance, as long as that instance's `algebraMap` agrees with the natural one
(`hcompat`). The trace analogue of `IsLocalRing.residue_norm_eq_norm_residue_of_eq_map`; see that
theorem's docstring for why the extra generality (over a pre-existing `Algebra` instance rather
than `Ideal.Quotient.algebraQuotientMapQuotient`) is needed. -/
theorem residue_trace_eq_trace_residue_of_eq_map {I : Ideal S}
    (hI : I = Ideal.map (algebraMap R S) (maximalIdeal R))
    [inst : Algebra (R ⧸ maximalIdeal R) (S ⧸ I)]
    (hcompat : ∀ r : R, algebraMap (R ⧸ maximalIdeal R) (S ⧸ I) (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk I (algebraMap R S r))
    (x : S) :
    Ideal.Quotient.mk (maximalIdeal R) (Algebra.trace R S x) =
      Algebra.trace (R ⧸ maximalIdeal R) (S ⧸ I) (Ideal.Quotient.mk I x) := by
  subst hI
  have hinst : inst = Ideal.Quotient.algebraQuotientMapQuotient := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [hcompat, Ideal.Quotient.algebraMap_quotient_map_quotient]
  rw [hinst]
  exact residue_trace_eq_trace_residue x

end IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

/-! ### The residue-field level trace compatibility, under `IsUnramified` -/

omit [Algebra.IsIntegral R S] in
/-- Under `IsUnramified`, the ring-trace `Algebra.trace K₀ : L₀ → K₀` reduces mod `𝔪_K` to the
trace `Algebra.trace 𝓀[K] : 𝓀[L] → 𝓀[K]` of the residue-field extension
(`Langlands.ResidueFieldNorm`'s `Algebra 𝓀[K] 𝓀[L]` instance). The trace analogue of
`residue_norm_eq_norm_residue_of_isUnramified`. -/
theorem residue_trace_eq_trace_residue_of_isUnramified
    (hU : IsUnramified K L v w) (x : w.adicCompletionIntegers L) :
    residue (v.adicCompletionIntegers K)
        (Algebra.trace (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) x) =
      Algebra.trace (ResidueField (v.adicCompletionIntegers K))
        (ResidueField (w.adicCompletionIntegers L)) (residue (w.adicCompletionIntegers L) x) :=
  IsLocalRing.residue_trace_eq_trace_residue_of_eq_map (R := v.adicCompletionIntegers K)
    (S := w.adicCompletionIntegers L) hU.symm
    (fun r => algebraMap_residueField_residue K L v w r) x

/-! ### The norm-linearizes-to-trace identity on the graded pieces of the principal-units
filtration -/

omit [Algebra.IsIntegral R S] in
/-- **The norm linearizes to the trace on the graded piece `1 + 𝔪_K^{n+1}` of the principal-units
filtration.** Let `π` be a uniformizer of `K₀`. Under `IsUnramified`, for every `n : ℕ` and every
`x : L₀`, there is `y : K₀` with

* `Algebra.norm K₀ (1 + π ^ (n+1) • x) = 1 + π ^ (n+1) * y`, and
* the residue of `y` in `𝓀[K]` equals `Algebra.trace 𝓀[K]` of the residue of `x` in `𝓀[L]`.

Read via the identification `1 + π ^ (n+1) • x ∈ 1 + 𝔪_K^{n+1}` (from `y ↦ 1 + π^{n+1} y`
identifying `𝔪_K^{n+1}/𝔪_K^{n+2}` with `𝓀[K]`, and likewise on the `L` side): this exhibits the map
induced on the `(n+1)`-th graded piece by `x ↦ Algebra.norm K₀ (1 + π^{n+1} • x)` as
`Algebra.trace 𝓀[K] : 𝓀[L] → 𝓀[K]`, the classical fact `N(1 + π^i x) ≡ 1 + Tr(x)·π^i \pmod{π^{i+1}}`
(here for the ring-level norm/trace `K₀ → L₀`; see the module docstring for the scope of what is
*not* built here — the quotient-group packaging and the connection to `localNormMap`).

Works uniformly for every `n`, not just `n = 0`: the proof only uses `π^{n+1} ∈ 𝔪_K`
(`hπ.maximalIdeal_eq`), which holds for every `n ≥ 0`, not a separate mod-`π^2`-only argument. -/
theorem exists_norm_one_add_uniformizer_pow_smul_eq_trace_add
    (hU : IsUnramified K L v w) {π : v.adicCompletionIntegers K} (hπ : Irreducible π) (n : ℕ)
    (x : w.adicCompletionIntegers L) :
    ∃ y : v.adicCompletionIntegers K,
      Algebra.norm (v.adicCompletionIntegers K) (1 + π ^ (n + 1) • x) = 1 + π ^ (n + 1) * y ∧
        residue (v.adicCompletionIntegers K) y =
          Algebra.trace (ResidueField (v.adicCompletionIntegers K))
            (ResidueField (w.adicCompletionIntegers L)) (residue (w.adicCompletionIntegers L) x) := by
  obtain ⟨c, hc⟩ := Algebra.exists_norm_one_add_smul_eq (R := v.adicCompletionIntegers K)
    (S := w.adicCompletionIntegers L) (π ^ (n + 1) : v.adicCompletionIntegers K) x
  refine ⟨Algebra.trace (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) x
    + π ^ (n + 1) * c, ?_, ?_⟩
  · rw [hc]; ring
  · have hπmem : π ∈ maximalIdeal (v.adicCompletionIntegers K) :=
      hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
    have hπnmem : π ^ (n + 1) ∈ maximalIdeal (v.adicCompletionIntegers K) :=
      Ideal.pow_mem_of_mem _ hπmem (n + 1) n.succ_pos
    have hres0 : residue (v.adicCompletionIntegers K) (π ^ (n + 1)) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hπnmem
    rw [map_add, map_mul, hres0, zero_mul, add_zero]
    exact residue_trace_eq_trace_residue_of_isUnramified K L v w hU x

/-! ### `1 + π^{n+1} • x` is a local unit, and the identity transfers to `localNormMap`

Closes the gap flagged in the module docstring's "Scope" section: connecting `1 + π^{n+1} • x` to
actual local units and to `localNormMap`, to the extent load-bearing for the successive-approximation
assembly of `Langlands.PrincipalUnitsCauchySequence`. -/

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- `1 + π^{n+1} • x` is a unit of `L₀`, for `π` a uniformizer of `K₀` and `x : L₀` — no
`IsUnramified` hypothesis needed, only the *forward* containment `𝔪_K·L₀ ≤ 𝔪_L` that always holds
(`map_maximalIdeal_le`), since `π^{n+1} ∈ 𝔪_K` puts `π^{n+1} • x ∈ 𝔪_K·L₀ ≤ 𝔪_L`, so
`1 + π^{n+1} • x` reduces to `1 ≠ 0` in `𝓀[L]` (`residue_ne_zero_iff_isUnit`). -/
theorem isUnit_one_add_uniformizer_pow_smul {π : v.adicCompletionIntegers K} (hπ : Irreducible π)
    (n : ℕ) (x : w.adicCompletionIntegers L) :
    IsUnit (1 + π ^ (n + 1) • x : w.adicCompletionIntegers L) := by
  refine (residue_ne_zero_iff_isUnit _).mp ?_
  have hπmem : π ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hπnmem : π ^ (n + 1) ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    Ideal.pow_mem_of_mem _ hπmem (n + 1) n.succ_pos
  have hmem : π ^ (n + 1) • x ∈ maximalIdeal (w.adicCompletionIntegers L) := by
    rw [Algebra.smul_def]
    exact (maximalIdeal (w.adicCompletionIntegers L)).mul_mem_right _
      (map_maximalIdeal_le K L v w (Ideal.mem_map_of_mem _ hπnmem))
  have hres0 : residue (w.adicCompletionIntegers L) (π ^ (n + 1) • x) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [map_add, hres0, add_zero, map_one]
  exact one_ne_zero

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- The image of `1 + π^{n+1} • x` in `L` (via `algebraMap L₀ L`) is a unit of the field `L` —
the field-level counterpart of `isUnit_one_add_uniformizer_pow_smul`, obtained by pushing that
local-ring unit forward along the (injective) ring hom `algebraMap L₀ L`. -/
theorem isUnit_algebraMap_one_add_uniformizer_pow_smul {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) (n : ℕ) (x : w.adicCompletionIntegers L) :
    IsUnit (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
      (1 + π ^ (n + 1) • x)) :=
  (isUnit_one_add_uniformizer_pow_smul K L v w hπ n x).map _

omit [Algebra.IsIntegral R S] in
/-- The ring-level norm of `1 + π^{n+1} • x` (in `K₀`) agrees, under `algebraMap K₀ K`, with the
field-level `Algebra.norm K` applied to the image of `1 + π^{n+1} • x` in `L` — i.e. `localNormMap`
applied to the unit of `(w.adicCompletion L)ˣ` corresponding to `1 + π^{n+1} • x` (via
`isUnit_algebraMap_one_add_uniformizer_pow_smul`) reduces, after applying `algebraMap K₀ K`, to
`Algebra.norm K₀ (1 + π^{n+1} • x)`. This is `algebraMap_norm_eq_norm_algebraMap`
(`Langlands.NormMapResidueCompatibility`) specialized to `x := 1 + π^{n+1} • x`, restated through
`localNormMap`'s definition (`Units.map (Algebra.norm (v.adicCompletion K))`), mirroring
`NormMapResidueCompatibility.lean`'s `localNormMap_reduce`. -/
theorem localNormMap_coe_one_add_uniformizer_pow_smul {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) (n : ℕ) (x : w.adicCompletionIntegers L) :
    (localNormMap K L v w
        (isUnit_algebraMap_one_add_uniformizer_pow_smul K L v w hπ n x).unit :
        v.adicCompletion K) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (Algebra.norm (v.adicCompletionIntegers K) (1 + π ^ (n + 1) • x)) := by
  show Algebra.norm (v.adicCompletion K)
      ((isUnit_algebraMap_one_add_uniformizer_pow_smul K L v w hπ n x).unit :
        w.adicCompletion L) = _
  rw [IsUnit.unit_spec, ← algebraMap_norm_eq_norm_algebraMap K L v w]

end IsDedekindDomain.HeightOneSpectrum

end
