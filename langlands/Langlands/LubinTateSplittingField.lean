import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Group.Ultra
import Langlands.LubinTateRootCount

/-!
# `K_1` rebuilt as a genuine field extension: `Polynomial.SplittingField`

`ROADMAP.md`'s `hsplit`-vacuity finding (`Langlands/LubinTateHsplitVacuity.lean`) showed that the
old `K_1` (`Langlands/LubinTateFieldTower.lean`, `IntermediateField.adjoin (FractionRing O)
(piTorsion hπ hf 1 : Set K)`) is built on a jointly-unsatisfiable pair of hypotheses whenever
`residueCard O ≥ 3`: `[IsFractionRing O K]` forces `K` to already *be* `Frac(O)`, while `hsplit`
demands `Q := P.divX`'s image *already* splits completely inside that same `K` — impossible once
`Q` (degree `q - 1 ≥ 2`) is irreducible over its own base field (Gauss's lemma).

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
(steps 4-5 of the rearchitecture) needs a fresh argument keyed to `K_1`'s own defining property
(`Q` splits by construction) rather than a hypothesis, and is left to a follow-up pass; seeing this
file's norm/valuation-extension wiring through to completion (confirming the instances above are
mutually compatible and `lake build`-clean) is this pass's scope.

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

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsUltrametricDist K]
  [CompleteSpace K] [IsFractionRing O K] in
/-- **`Q` splits completely over `K_1`, by construction — no `hsplit` hypothesis.** -/
theorem splits_K_1 (P : O[X]) :
    ((P.divX.map (algebraMap O K)).map (algebraMap K (K_1 (K := K) P))).Splits :=
  Polynomial.SplittingField.splits _

section NormExtension

variable (P : O[X])

/-- **The extended norm on `K_1`**, Mathlib's `spectralNorm` made into an actual `NormedField`
structure. Local instance: activating it globally would conflict with any other norm `K_1` might
independently carry (e.g. if `K_1` happened to coincide with some other normed field), matching the
convention `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` itself uses (`spectralNorm.normedField`
is a `def`, not an `instance`). -/
@[implicit_reducible] def K_1.normedField : NormedField (K_1 (K := K) P) :=
  spectralNorm.normedField K (K_1 (K := K) P)

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`K_1`, with the extended norm, is nonarchimedean.** `isNonarchimedean_spectralNorm` gives
`IsNonarchimedean (spectralNorm K K_1)`; `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`
turns that into `IsUltrametricDist K_1`, using that `K_1.normedField`'s own `norm` function *is*
`spectralNorm K K_1` definitionally (`spectralNorm.normedField`'s field `norm x := spectralNorm K L x`). -/
theorem K_1.isUltrametricDist :
    letI := K_1.normedField (K := K) P
    IsUltrametricDist (K_1 (K := K) P) := by
  letI := K_1.normedField (K := K) P
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (show IsNonarchimedean (fun x : K_1 (K := K) P => ‖x‖) from isNonarchimedean_spectralNorm)

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`K_1`, with the extended norm, is complete.** `spectralNorm.completeSpace` is an instance
whenever `[FiniteDimensional K K_1]` (always true for a splitting field), stated relative to
`spectralNorm.uniformSpace K K_1` — definitionally the same uniform space `K_1.normedField`
induces, since both trace back to the same underlying `dist`/`norm` function. -/
theorem K_1.completeSpace :
    letI := K_1.normedField (K := K) P
    CompleteSpace (K_1 (K := K) P) :=
  spectralNorm.completeSpace K (K_1 (K := K) P)

/-- **`Algebra O K_1`**, built by composing the existing `algebraMap O K` with `K_1`'s own
`algebraMap K K_1` — the only `O → K_1` map available, not a second independently-built one. -/
@[implicit_reducible] def K_1.algebraO : Algebra O (K_1 (K := K) P) :=
  ((algebraMap K (K_1 (K := K) P)).comp (algebraMap O K)).toAlgebra

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsUltrametricDist K]
  [CompleteSpace K] [IsFractionRing O K] in
theorem K_1.algebraMap_O_eq :
    letI := K_1.algebraO (K := K) P
    ⇑(algebraMap O (K_1 (K := K) P)) = ⇑(algebraMap K (K_1 (K := K) P)) ∘ ⇑(algebraMap O K) := by
  letI := K_1.algebraO (K := K) P
  rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsUltrametricDist K]
  [CompleteSpace K] [IsFractionRing O K] in
theorem K_1.isScalarTower :
    letI := K_1.algebraO (K := K) P
    IsScalarTower O K (K_1 (K := K) P) := by
  letI := K_1.algebraO (K := K) P
  exact IsScalarTower.of_algebraMap_eq (fun x ↦ by
    rw [K_1.algebraMap_O_eq]; rfl)

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`K`'s uniform norm bound (`hOK`) transports down to `K_1` unchanged.** For every `c : O`,
`‖algebraMap O K_1 c‖ = ‖algebraMap O K c‖` — `algebraMap K K_1`'s extended norm agrees with `K`'s
own norm on `K`'s image (`spectralNorm_extends`), and `algebraMap O K_1` factors through it
(`K_1.algebraMap_O_eq`). -/
theorem K_1.hOK_transport (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_1.normedField (K := K) P
    letI := K_1.algebraO (K := K) P
    ∀ c : O, ‖algebraMap O (K_1 (K := K) P) c‖ ≤ 1 := by
  letI := K_1.normedField (K := K) P
  letI := K_1.algebraO (K := K) P
  intro c
  have hcoe : algebraMap O (K_1 (K := K) P) c = algebraMap K (K_1 (K := K) P) (algebraMap O K c) :=
    congrFun (K_1.algebraMap_O_eq (K := K) P) c
  show spectralNorm K (K_1 (K := K) P) (algebraMap O (K_1 (K := K) P) c) ≤ 1
  rw [hcoe, spectralNorm_extends]
  exact hOK c

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`K`'s strict uniformizer bound (`hπnorm`) transports down to `K_1` unchanged.** Same route as
`K_1.hOK_transport`. -/
theorem K_1.hπnorm_transport {π : O} (hπnorm : ‖algebraMap O K π‖ < 1) :
    letI := K_1.normedField (K := K) P
    letI := K_1.algebraO (K := K) P
    ‖algebraMap O (K_1 (K := K) P) π‖ < 1 := by
  letI := K_1.normedField (K := K) P
  letI := K_1.algebraO (K := K) P
  have hcoe : algebraMap O (K_1 (K := K) P) π = algebraMap K (K_1 (K := K) P) (algebraMap O K π) :=
    congrFun (K_1.algebraMap_O_eq (K := K) P) π
  show spectralNorm K (K_1 (K := K) P) (algebraMap O (K_1 (K := K) P) π) < 1
  rw [hcoe, spectralNorm_extends]
  exact hπnorm

end NormExtension

end LubinTate

end
