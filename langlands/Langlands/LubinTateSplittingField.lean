import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Group.Ultra
import Langlands.LubinTateRootCount

/-!
# `K_1` rebuilt as a genuine field extension: `Polynomial.SplittingField`

`Langlands/LubinTateHsplitVacuity.lean` shows that the old `K_1` (`Langlands/LubinTateFieldTower.lean`,
`IntermediateField.adjoin (FractionRing O) (piTorsion hπ hf 1 : Set K)`) is built on a
jointly-unsatisfiable pair of hypotheses whenever `residueCard O ≥ 3`: `[IsFractionRing O K]` forces
`K` to already *be* `Frac(O)`, while `hsplit` demands `Q := P.divX`'s image *already* splits
completely inside that same `K` — impossible once `Q` (degree `q - 1 ≥ 2`) is irreducible over its
own base field (Gauss's lemma).

This file replaces that design: `K_1` is built as the **splitting field of `Q`'s image in `K`
itself** (`Q.SplittingField`, for `Q := P.divX.map (algebraMap O K)`, `K` this repo's standing
complete nonarchimedean field with `[IsFractionRing O K]`) — a genuine field *extension* of `K`
constructed to contain `Q`'s roots by definition (Mathlib's `Polynomial.SplittingField`), not a
subfield of `K` assumed to already contain them. `Q` splitting over `K_1` is then automatic
(`Polynomial.SplittingField.splits`), not a hypothesis.

## The norm/valuation extension

`piTorsion`'s machinery (`Langlands.LubinTateTorsionPoints`) needs `K_1` to carry the same
`[NontriviallyNormedField] [IsUltrametricDist] [CompleteSpace]` package `K` does, compatibly with
`K`'s own norm — the classical "a finite extension of a complete nonarchimedean field carries a
canonical extension of the norm, and is itself complete" fact. **This is already in Mathlib**,
under the name `spectralNorm` (`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`), not built from
scratch here:

* `spectralNorm.normedField K K_1 : NormedField K_1`, given `[NontriviallyNormedField K]
  [Algebra.IsAlgebraic K K_1]` (automatic from `[FiniteDimensional K K_1]`,
  `Algebra.IsAlgebraic.of_finite`) — the spectral norm as an actual `NormedField` structure.
* `IsUltrametricDist K_1`, from `IsNonarchimedean (spectralNorm K K_1)`
  (`isNonarchimedean_spectralNorm`, needs `[IsUltrametricDist K]`) via
  `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`.
* `spectralNorm.completeSpace K K_1 : CompleteSpace K_1`, an instance whenever `[FiniteDimensional
  K K_1]` (always true for a splitting field, `Polynomial.SplittingField.instFiniteDimensional`).
* `spectralNorm_extends : spectralNorm K L (algebraMap K L k) = ‖k‖` — the extended norm agrees
  with `K`'s own norm on `K` itself, which is exactly what lets `hOK`/`hπnorm` (this repo's two
  standing per-application hypotheses on `K`) transport down to `K_1` for free.

`Algebra O K_1` is built by composing the existing `Algebra O K` with the fresh `Algebra K K_1`
(`RingHom.toAlgebra` on the composite ring hom, with `IsScalarTower O K K_1` recorded so downstream
lemmas expecting the tower see it directly) — not a second, independently-built `O → K_1` map that
could disagree with the first (there is only one `O → K` map, `K`'s own `algebraMap`, and only one
further `K → K_1` map, `K_1`'s own `algebraMap`; composing them is the only map in play).

## What this file does NOT attempt

`[IsFractionRing O K_1]` is **not** claimed or needed — `K_1` genuinely, properly extends `K` (and
hence `Frac(O)`) whenever `Q` has degree `≥ 2`, so `K_1 ≠ Frac(O)` and `IsFractionRing O K_1` would
be false in the interesting case. This means `LubinTateRootCount.lean`'s theorems that *require*
`[IsFractionRing O K]` on their ambient field (`card_piTorsion_one_eq_residueCard`,
`mem_piTorsion_one_of_root_divX_map`, the irreducibility-over-`K`-itself argument) do **not**
transfer to `K_1` by direct specialization — re-deriving the root-count and degree facts for `K_1`
needs a fresh argument keyed to `K_1`'s own defining property (`Q` splits by construction) rather
than a hypothesis. This file covers the norm/valuation-extension wiring only.

## Main results

* `K_1` : `Q.SplittingField`, for `Q := P.divX.map (algebraMap O K)` — the splitting field of `Q`'s
  image in `K`, a genuine extension of `K` (hence of `O`, via the composite algebra map).
* `splits_K_1` : `Q` splits completely over `K_1`, for free (`Polynomial.SplittingField.splits`,
  no `hsplit` hypothesis).
* `hOK_K_1` / `hπnorm_K_1` : `K`'s two standing per-application norm hypotheses transport down to
  `K_1` unchanged, via `spectralNorm_extends`.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open IsLocalRing PowerSeries Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsFractionRing O K]

/-- **`K_1 := Q.SplittingField`**, `Q := P.divX`'s image in `K`. A genuine field extension of `K`,
constructed (by Mathlib's `Polynomial.SplittingField`) to contain all of `Q`'s roots, rather than a
subfield of a `K` assumed to already contain them. -/
def K_1 (P : O[X]) : Type _ := (P.divX.map (algebraMap O K)).SplittingField

instance K_1.instField (P : O[X]) : Field (K_1 (K := K) P) :=
  inferInstanceAs (Field (P.divX.map (algebraMap O K)).SplittingField)

instance K_1.instAlgebra (P : O[X]) : Algebra K (K_1 (K := K) P) :=
  inferInstanceAs (Algebra K (P.divX.map (algebraMap O K)).SplittingField)

instance K_1.instFiniteDimensional (P : O[X]) : FiniteDimensional K (K_1 (K := K) P) :=
  inferInstanceAs (FiniteDimensional K (P.divX.map (algebraMap O K)).SplittingField)

instance K_1.instIsAlgebraic (P : O[X]) : Algebra.IsAlgebraic K (K_1 (K := K) P) :=
  Algebra.IsAlgebraic.of_finite K (K_1 (K := K) P)

/-- **`K_1 P` is a splitting field of `Q`'s image in `K`**, by construction — recorded as an
instance so `Polynomial.IsSplittingField.adjoin_rootSet` (`K_1` is generated over `K` by `Q`'s
roots) applies to `K_1 P` without unfolding the type synonym at every call site. -/
instance K_1.instIsSplittingField (P : O[X]) :
    Polynomial.IsSplittingField K (K_1 (K := K) P) (P.divX.map (algebraMap O K)) :=
  inferInstanceAs
    (Polynomial.IsSplittingField K (P.divX.map (algebraMap O K)).SplittingField
      (P.divX.map (algebraMap O K)))

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsUltrametricDist K]
  [CompleteSpace K] [IsFractionRing O K] in
/-- **`Q` splits completely over `K_1`, by construction — no `hsplit` hypothesis.** -/
theorem splits_K_1 (P : O[X]) :
    ((P.divX.map (algebraMap O K)).map (algebraMap K (K_1 (K := K) P))).Splits :=
  Polynomial.SplittingField.splits _

section NormExtension

variable (P : O[X])

/-- **The extended norm on `K_1`**, Mathlib's `spectralNorm` made into an actual
`NontriviallyNormedField` structure (`spectralNorm.nontriviallyNormedField`: `K_1`'s norm restricts
to `K`'s on `K`'s image, so `K`'s own norm-`> 1` witness transports up).

Unlike Mathlib's `spectralNorm.normedField`/`spectralNorm.nontriviallyNormedField` — `def`s, since
an arbitrary `L` may already carry an unrelated norm this would silently conflict with — this *is*
an `instance`, because `K_1 P` is a dedicated type synonym introduced in this file: no other norm
on it exists anywhere to conflict, and downstream files need `piTorsion (K := K_1 P)` and the whole
spacing/action/freeness machinery to resolve `‖·‖` by ordinary instance search rather than by
threading `letI` through every statement. The induced `Field (K_1 P)` agrees definitionally with
`K_1.instField` (Mathlib builds the structure as `{ (inferInstance : Field L) with … }`), so the
`Field` diamond is closed by structure eta. -/
instance K_1.instNontriviallyNormedField : NontriviallyNormedField (K_1 (K := K) P) :=
  spectralNorm.nontriviallyNormedField K (K_1 (K := K) P)

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`K_1`'s norm is literally `spectralNorm K K_1`** — true by `rfl`, recorded so downstream
proofs can rewrite rather than `show`. -/
theorem K_1.norm_eq_spectralNorm (x : K_1 (K := K) P) :
    ‖x‖ = spectralNorm K (K_1 (K := K) P) x := rfl

/-- **`K_1`, with the extended norm, is nonarchimedean.** `isNonarchimedean_spectralNorm` gives
`IsNonarchimedean (spectralNorm K K_1)`; `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`
turns that into `IsUltrametricDist K_1`, using `K_1.norm_eq_spectralNorm`. -/
instance K_1.instIsUltrametricDist : IsUltrametricDist (K_1 (K := K) P) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (show IsNonarchimedean (fun x : K_1 (K := K) P => ‖x‖) from isNonarchimedean_spectralNorm)

/-- **`K_1`, with the extended norm, is complete.** `spectralNorm.completeSpace` is an instance
whenever `[FiniteDimensional K K_1]` (always true for a splitting field), stated relative to
`spectralNorm.uniformSpace K K_1` — definitionally the same uniform space
`K_1.instNontriviallyNormedField` induces, since both trace back to the same underlying
`dist`/`norm` function. -/
instance K_1.instCompleteSpace : CompleteSpace (K_1 (K := K) P) :=
  spectralNorm.completeSpace K (K_1 (K := K) P)

/-- **`K_1` is a normed `K`-vector space.** Mathlib's `spectralNorm.normedSpace` is a `def` (stated
relative to `spectralNorm.seminormedAddCommGroup K L`, definitionally the additive structure
`K_1.instNontriviallyNormedField` induces — both trace back to the same `norm` function); it is made
an `instance` here for the same reason as `K_1.instNontriviallyNormedField`, namely that `K_1 P` is a
dedicated type synonym with no competing norm. What this buys downstream is `ContinuousSMul K
(K_1 P)`, hence `Submodule.closed_of_finiteDimensional`: every finite-dimensional `K`-subspace of
`K_1 P` is closed, which is what lets a `tsum` (`NonarchimedeanPowerSeriesEval.eval`) whose summands
lie in an intermediate field stay inside it — see `Langlands.LubinTateSplittingFieldDegree`. -/
instance K_1.instNormedSpace : NormedSpace K (K_1 (K := K) P) :=
  spectralNorm.normedSpace K (K_1 (K := K) P)

/-- **`Algebra O K_1`**, built by composing the existing `algebraMap O K` with `K_1`'s own
`algebraMap K K_1` — the only `O → K_1` map available, not a second independently-built one
(there is exactly one `O → K` map and exactly one `K → K_1` map, so no competing composite
exists for this to diverge from). -/
instance K_1.instAlgebraO : Algebra O (K_1 (K := K) P) :=
  ((algebraMap K (K_1 (K := K) P)).comp (algebraMap O K)).toAlgebra

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsUltrametricDist K]
  [CompleteSpace K] [IsFractionRing O K] in
theorem K_1.algebraMap_O_eq :
    ⇑(algebraMap O (K_1 (K := K) P)) = ⇑(algebraMap K (K_1 (K := K) P)) ∘ ⇑(algebraMap O K) := rfl

instance K_1.instIsScalarTower : IsScalarTower O K (K_1 (K := K) P) :=
  IsScalarTower.of_algebraMap_eq (fun x ↦ by rw [K_1.algebraMap_O_eq]; rfl)

/-- **`algebraMap O K_1` is injective.** The composite of `algebraMap O K` (injective, `O` a domain
with `K` its fraction field) and `algebraMap K K_1` (injective, any ring hom out of a field). This
is the replacement for the `[IsFractionRing O K]` that `LubinTateRootCount.lean`'s counting argument
used on its own ambient field — `K_1` is a *proper* extension of `Frac(O)` whenever `Q` has degree
`≥ 2`, so `IsFractionRing O K_1` is false there, but injectivity (all the counting argument
actually needs) survives the tower. -/
instance K_1.instFaithfulSMul : FaithfulSMul O (K_1 (K := K) P) :=
  (faithfulSMul_iff_algebraMap_injective O (K_1 (K := K) P)).mpr <| by
    rw [K_1.algebraMap_O_eq]
    exact (algebraMap K (K_1 (K := K) P)).injective.comp (IsFractionRing.injective O K)

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`K`'s uniform norm bound (`hOK`) transports down to `K_1` unchanged.** For every `c : O`,
`‖algebraMap O K_1 c‖ = ‖algebraMap O K c‖` — `algebraMap K K_1`'s extended norm agrees with `K`'s
own norm on `K`'s image (`spectralNorm_extends`), and `algebraMap O K_1` factors through it
(`K_1.algebraMap_O_eq`). -/
theorem K_1.hOK_transport (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    ∀ c : O, ‖algebraMap O (K_1 (K := K) P) c‖ ≤ 1 := by
  intro c
  have hcoe : algebraMap O (K_1 (K := K) P) c = algebraMap K (K_1 (K := K) P) (algebraMap O K c) :=
    congrFun (K_1.algebraMap_O_eq (K := K) P) c
  rw [K_1.norm_eq_spectralNorm, hcoe, spectralNorm_extends]
  exact hOK c

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`K`'s strict uniformizer bound (`hπnorm`) transports down to `K_1` unchanged.** Same route as
`K_1.hOK_transport`. -/
theorem K_1.hπnorm_transport {π : O} (hπnorm : ‖algebraMap O K π‖ < 1) :
    ‖algebraMap O (K_1 (K := K) P) π‖ < 1 := by
  have hcoe : algebraMap O (K_1 (K := K) P) π = algebraMap K (K_1 (K := K) P) (algebraMap O K π) :=
    congrFun (K_1.algebraMap_O_eq (K := K) P) π
  rw [K_1.norm_eq_spectralNorm, hcoe, spectralNorm_extends]
  exact hπnorm

end NormExtension

end LubinTate

end
