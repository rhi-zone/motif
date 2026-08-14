import Langlands.LubinTateSplittingField
import Langlands.LubinTateResidueUnitsTransitivity

/-!
# `π`-torsion inside `K_1 = Q.SplittingField`: the root count and the transitive `(O/π)ˣ`-action

`Langlands.LubinTateSplittingField` rebuilt `K_1` as `Q.SplittingField` for
`Q := P.divX.map (algebraMap O K)` — a genuine extension of `K` in which `Q` splits **by
construction** (`splits_K_1`), replacing the old, unsatisfiable `hsplit` hypothesis
(`Langlands.LubinTateHsplitVacuity`). It stopped short of instantiating `piTorsion` there.

This file instantiates `piTorsion hπ hf 1` at `K := K_1 P` and closes the two facts everything
downstream needs:

* `card_piTorsion_one_K_1_eq_residueCard` : `Nat.card (piTorsion hπ hf 1 : Set (K_1 P)) =
  residueCard O` — **non-vacuously**, with no `hsplit` hypothesis anywhere in sight.
* `orbit_image_eq_piTorsion_sdiff_zero_K_1` : the `(ResidueField O)ˣ`-action on the nonzero
  `π`-torsion of `K_1` is **transitive**.

## What made this possible

Two hypotheses in the old chain had to be separated from each other first:

1. **`[IsFractionRing O K]` on the field containing the roots.** The old root-valuation lemmas got
   the exact norm of a torsion point from `spectralNorm` via `minpoly`, which needs `Q` to be
   *irreducible over the ambient field* — false in `K_1`, where `Q` splits. Replaced by the purely
   ultrametric Eisenstein-polygon computation (`Langlands.EisensteinRootNorm`), which needs no
   irreducibility; the whole spacing/mod-`π`/action/freeness chain now asks only for
   `[FaithfulSMul O K]` (`algebraMap O K` injective), which `K_1` satisfies via the tower
   `O → K → K_1` (`K_1.instFaithfulSMul`).
2. **Separability of `Q`'s image.** This *does* still need Gauss's lemma over the base, so it is
   proved over `K` (`separable_map_divX_of_isLubinTatePoly`, with the root supplied from `K_1`
   itself) and transported up along the field embedding `K ↪ K_1` (`Polynomial.Separable.map`) —
   which is exactly why `card_piTorsion_one_eq_residueCard_of_separable_of_splits` takes
   separability as a hypothesis rather than deriving it.

`[IsFractionRing O K]` is retained on the **base** `K` throughout (it is what makes `Q` irreducible
over `K`, hence what pins the degree down). It is never asked of `K_1`, where it is false.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open NonarchimedeanPowerSeriesEval PowerSeries IsLocalRing Polynomial MulAction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsFractionRing O K]
variable {π : O} {f : O⟦X⟧}

section

variable (P : O[X])

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsUltrametricDist K]
  [CompleteSpace K] [IsFractionRing O K] in
/-- **`Q`'s image in `K_1` is the same polynomial however you get there.** `P.divX.map (algebraMap O
K_1)` and `(P.divX.map (algebraMap O K)).map (algebraMap K K_1)` agree, by `Polynomial.map_map` and
the scalar tower `O → K → K_1` (`K_1.instIsScalarTower`). -/
theorem map_divX_algebraMap_K_1 :
    (P.divX.map (algebraMap O K)).map (algebraMap K (K_1 (K := K) P))
      = P.divX.map (algebraMap O (K_1 (K := K) P)) := by
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsUltrametricDist K]
  [CompleteSpace K] [IsFractionRing O K] in
/-- **`Q` splits inside `K_1`, as a polynomial over `O`** — `splits_K_1` re-expressed through
`map_divX_algebraMap_K_1`. No hypothesis: this is `K_1`'s defining property. -/
theorem splits_divX_map_K_1 : (P.divX.map (algebraMap O (K_1 (K := K) P))).Splits :=
  map_divX_algebraMap_K_1 (K := K) P ▸ splits_K_1 (K := K) P

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsUltrametricDist K]
  [CompleteSpace K] [IsFractionRing O K] in
/-- **`aeval`-over-`K` at a point of `K_1` is `eval` of `Q`'s image in `K_1`.** The bridge between
the two ways the base-changed polynomial gets evaluated: `Polynomial.aeval_def` +
`Polynomial.eval_map` + `map_divX_algebraMap_K_1`. -/
theorem aeval_K_divX_eq_eval_K_1 (y : K_1 (K := K) P) :
    Polynomial.aeval y (P.divX.map (algebraMap O K))
      = Polynomial.eval y (P.divX.map (algebraMap O (K_1 (K := K) P))) := by
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, map_divX_algebraMap_K_1]

end

/-- **`Q := P.divX`'s image is separable in `K_1`.** Separability is a Gauss's-lemma fact about the
*base* field (`separable_map_divX_of_isLubinTatePoly`, using `[IsFractionRing O K]` and tameness of
`Q.natDegree`), fed a root taken from `K_1` itself (`splits_divX_map_K_1` plus
`Polynomial.Splits.exists_eval_eq_zero`); `Polynomial.Separable.map` then transports it up the
embedding `K ↪ K_1`. -/
theorem separable_divX_map_K_1 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O) :
    (P.divX.map (algebraMap O (K_1 (K := K) P))).Separable := by
  have hf0 : PowerSeries.coeff 0 f = 0 := hf.1
  have hf1 : PowerSeries.coeff 1 f = π := hf.2.1
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  have hQn1 : P.divX.natDegree + 1 = residueCard O := by
    have hQdegval : P.divX.natDegree = residueCard O - 1 := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hPdeg]
    have h2 := two_le_residueCard (O := O); omega
  have hQn : IsUnit ((P.divX.natDegree : O)) := isUnit_natCast_of_add_one_eq_residueCard hQn1
  -- A root of `Q`'s image, taken from `K_1`.
  have hQmapdeg : (P.divX.map (algebraMap O (K_1 (K := K) P))).natDegree = P.divX.natDegree :=
    hQmonic.natDegree_map _
  have hQmapdegne : (P.divX.map (algebraMap O (K_1 (K := K) P))).degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hQmapdeg]; exact hQdeg)).ne'
  obtain ⟨a0, ha0⟩ := (splits_divX_map_K_1 (K := K) P).exists_eval_eq_zero hQmapdegne
  have ha0' : Polynomial.aeval a0 (P.divX.map (algebraMap O K)) = 0 := by
    rw [aeval_K_divX_eq_eval_K_1]; exact ha0
  have hsepK : (P.divX.map (algebraMap O K)).Separable :=
    separable_map_divX_of_isLubinTatePoly hu heq hf0 hπ hf1 hPdist hPdeg2 hOK hπnorm hQn
      (L := K_1 (K := K) P) ha0'
  exact map_divX_algebraMap_K_1 (K := K) P ▸ hsepK.map

/-- **The root count at `K_1`, non-vacuously: `Nat.card (piTorsion hπ hf 1 : Set (K_1 P)) =
residueCard O`.** No `hsplit` hypothesis — `Q` splits over `K_1` by construction — and no
`[IsFractionRing O (K_1 P)]`, which would be false. Every hypothesis here is a fact about the base
`K` and the Weierstrass factorization of `f`, all of them satisfiable together (see `ROADMAP.md`'s
non-vacuity check for this pass). -/
theorem card_piTorsion_one_K_1_eq_residueCard
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O) :
    Nat.card (piTorsion (K := K_1 (K := K) P) hπ hf 1) = residueCard O :=
  card_piTorsion_one_eq_residueCard_of_separable_of_splits
    (K_1.hOK_transport P hOK) hπ (K_1.hπnorm_transport P hπnorm) hf hu heq hPdist hPdeg
    (separable_divX_map_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg)
    (splits_divX_map_K_1 (K := K) P)

/-- **Transitivity of the `(O/π)ˣ`-action on the nonzero `π`-torsion of `K_1`.** The freeness and
`(ResidueField O)ˣ`-action machinery (`LubinTateResidueUnitsAction`,
`LubinTateResidueUnitsFreeness`, `LubinTateResidueUnitsTransitivity`) specializes at `K := K_1 P`
with no further work once `[FaithfulSMul O (K_1 P)]` replaces the old `[IsFractionRing O K]`; the
only missing input was the root count, now supplied by `card_piTorsion_one_K_1_eq_residueCard`.

Concretely: the action is free (`stabilizer = ⊥`), so every orbit of a nonzero point has exactly
`|(ResidueField O)ˣ| = q - 1` elements; the nonzero torsion also has exactly `q - 1` elements; an
orbit sits inside it; equal finite cardinality forces equality. -/
theorem orbit_image_eq_piTorsion_sdiff_zero_K_1
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    {α : K_1 (K := K) P} (hα : α ∈ piTorsion (K := K_1 (K := K) P) hπ hf 1) (hα0 : α ≠ 0) :
    letI := residuePiTorsionMulAction (K_1.hOK_transport P hOK) hπ (K_1.hπnorm_transport P hπnorm)
      hf hu heq hPdist (hPdeg ▸ two_le_residueCard)
    Subtype.val '' (orbit (ResidueField O)ˣ
        (⟨α, hα⟩ : ↥(piTorsion (K := K_1 (K := K) P) hπ hf 1))) =
      piTorsion (K := K_1 (K := K) P) hπ hf 1 \ {0} :=
  orbit_image_eq_piTorsion_sdiff_zero_of_card (K_1.hOK_transport P hOK) hπ
    (K_1.hπnorm_transport P hπnorm) hf hu heq hPdist (hPdeg ▸ two_le_residueCard)
    (card_piTorsion_one_K_1_eq_residueCard hOK hπ hπnorm hf hu heq hPdist hPdeg) hα hα0

end LubinTate

end
