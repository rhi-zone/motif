import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Langlands.LubinTateTorsionPoints
import Langlands.LubinTateRootCount

/-!
# ⚠️ VACUOUS whenever `residueCard O ≥ 3` — see `Langlands.LubinTateHsplitVacuity`

**Every theorem in this file that takes `hsplit` as a hypothesis is vacuously true outside the
degenerate case `residueCard O = 2`.** `Langlands/LubinTateHsplitVacuity.lean` proves `hsplit :
(P.divX.map (algebraMap O K)).Splits` is jointly unsatisfiable with this file's own standing
`[IsFractionRing O K]` whenever `P.divX.natDegree ≥ 2` (i.e. `residueCard O ≥ 3`): `[IsFractionRing
O K]` forces `K` to already *be* `Frac(O)`, while `Q := P.divX`'s image is irreducible over that
same `K` (Gauss's lemma), so it cannot also split completely there. `K_1`, `splits_map_K_1_of_splits`,
and `finrank_adjoin_of_aeval_divX_map_eq_zero` are all logically valid `hsplit → …` implications, but
`hsplit` can never actually be discharged for a genuine ramified extension — the case this whole
arc exists to formalize. **Do not build further theorems on `hsplit` in this file**; see
`Langlands.LubinTateSplittingField` for the replacement construction (`K_1` built as
`Polynomial.SplittingField`, a genuine extension of `K` in which `Q` splits by construction, no
`hsplit` hypothesis) and `ROADMAP.md`'s entry for this pass for the full rearchitecture status.

# The base-field embedding, `K_1 = K(F_π[π])`, and the `hsplit`-transport to `K_1`

`ROADMAP.md` §27's pointer-forward: the natural next step after the torsion-point group
`piTorsion hπ hf n` (packaged as an `AddCommGroup` in `Langlands.LubinTateTorsionGroup`) is the
field extension `K_1 := K(F_π[π])` and the tower `K_n := K(F_π[π^n])`.

Both `piTorsion` and the ambient evaluation field `K` are already parametrized abstractly in
`Langlands/LubinTateTorsionPoints.lean`: `O` is the base complete discrete valuation ring, `K` is
*any* `NormedField` with `[Algebra O K]` in which `O`'s image lies in the closed unit ball. This
file, however, is where `K_1`'s tower structure and the `hsplit`-transport to it are built, and
both genuinely need `K` to be (isomorphic to) `O`'s field of fractions — `[IsFractionRing O K]` —
not merely a normed field containing `O`'s bounded image:

* To adjoin torsion points to a genuine *base field* (rather than the base ring `O`), `K_1` is
  built over `O`'s field of fractions as an intermediate field base point, using Mathlib's own
  fraction-field machinery (`IsFractionRing.lift`/`FractionRing.liftAlgebra`) rather than a
  bespoke `F`/`K` split or an assumption that `K` itself already is `Frac(O)`.
* The `hsplit`-transport to `K_1` (`ROADMAP.md`'s `hsplit`/`K_1` framing question, §34 item 2, §35
  Part 2) reuses `Langlands.LubinTate.mem_piTorsion_one_of_root_divX_map`
  (`Langlands/LubinTateRootCount.lean`), which — like `card_piTorsion_one_eq_residueCard` itself —
  needs `[IsFractionRing O K]`: Gauss's lemma, comparing `Q := P.divX`'s irreducibility over `O`
  and over `K`, genuinely needs `K` to be a fraction field of `O`, not merely a normed field
  containing `O`'s bounded image (checked directly by reading `LubinTateEisensteinQ.lean`'s
  `Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated`, the one place
  `[IsFractionRing O K]` is actually used in that chain). This matches the setting
  `Langlands/LubinTateRootCountConcrete.lean` already instantiates (`K := v.adicCompletion F`,
  where `IsFractionRing (v.adicCompletionIntegers F) (v.adicCompletion F)` holds), so this file
  requires `[IsFractionRing O K]` throughout rather than only for the transport theorem — `K_1`
  has no caller anywhere else in the repo that needs the weaker `[FaithfulSMul O K]` this file
  used to carry, so strengthening its hypothesis here is free.

`[IsFractionRing O K]` implies `[FaithfulSMul O K]` (`IsFractionRing.injective` +
`faithfulSMul_iff_algebraMap_injective`, below), so `FractionRing.liftAlgebra` still applies
unchanged.

## A genuine diamond hit and resolved, and one avoided

Building the `hsplit`-transport surfaced two real obstacles, both diagnosed rather than routed
around:

* **A diamond risk anticipated but avoidable.** `ROADMAP.md` anticipated needing a fresh
  `Algebra O K_1` instance (composing `Algebra O (FractionRing O)` with `Algebra (FractionRing O)
  K_1`) to state the transport, flagging the risk of a second, independently-built instance
  disagreeing with the standing `Algebra O K` chain. Investigation showed this is unnecessary:
  `IntermediateField.splits_of_splits` only ever needs the *primary* `Algebra (FractionRing O)
  K_1` structure `IntermediateField` already supplies for free (`IntermediateField.toAlgebra`) —
  stating the transported conclusion as a polynomial over `Frac(O)` mapped into `K_1` (rather than
  as `Q.map (algebraMap O K_1)`) sidesteps the need for `Algebra O K_1` entirely, so there is no
  second `O`-to-`K_1` map to build or reconcile.
* **A genuine, reproducible Lean elaboration-order sensitivity, diagnosed and fixed directly.**
  Even `Field (K_1 hπ hf)` alone (`Algebra`/`Field` typeclass search touching `K_1`'s coeSort)
  reproducibly got "stuck" (`typeclass instance problem is stuck: IsFractionRing O ?m`) whenever
  `K_1` was applied to explicit arguments (`hπ`, `hf`, or even an unrelated `n : ℕ`) without `O`
  and `K` pinned first — confirmed via a from-scratch, minimized reproduction (isolated in a
  throwaway file, bisected down to the exact triggering shape) that this is *not* about
  `piTorsion`, `FractionRing.liftAlgebra`, or any custom instance in this file: it reproduces with
  `K_1`'s body replaced by `IntermediateField.adjoin (FractionRing O) (∅ : Set K)` and an unrelated
  `ℕ` parameter. Lean's elaborator, when checking an instance goal built from an under-elaborated
  application `K_1 hπ hf`, searches with `O`/`K` still as metavariables before the application is
  fully resolved. The fix, confirmed by the same reproduction: supply `O` and `K` explicitly at
  every call site, `K_1 (O := O) (K := K) hπ hf` — this is not a workaround for a mathematical
  diamond (there is none here), just resolving a real, narrow elaboration-order issue the direct
  way, by giving Lean the information it needs before it needs it.

## Main results

* `FractionRing.liftAlgebra` (Mathlib, made a local instance here): given
  `[FaithfulSMul O K]` — `algebraMap O K` injective, phrased the way Mathlib's fraction-ring
  machinery wants it (`faithfulSMul_iff_algebraMap_injective`), itself derived here from
  `[IsFractionRing O K]` (`faithfulSMul_of_isFractionRing`) — this supplies
  `Algebra (FractionRing O) K`, compatible with the existing `Algebra O K` via
  `FractionRing.isScalarTower_liftAlgebra : IsScalarTower O (FractionRing O) K`. Mathlib does not
  make this an instance globally (it would create a diamond when `K = FractionRing O` itself), so
  it is activated locally in this file only.
* `K_1` : `IntermediateField.adjoin (FractionRing O) (piTorsion hπ hf 1 : Set K)`, the field
  generated over `Frac(O)` by the `π`-torsion points of `F_π` inside `K`.
* `splits_map_K_1_of_splits` : the positive half of the `hsplit`/`K_1` framing question — `Q :=
  P.divX` splitting completely inside `K` (`hsplit`) transports down to `K_1` for free, via
  `IntermediateField.splits_of_splits` and `mem_piTorsion_one_of_root_divX_map`.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open IsLocalRing PowerSeries

open scoped Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsFractionRing O K]
variable {π : O} {f : O⟦X⟧}

/-- `IsFractionRing O K` gives `FaithfulSMul O K` for free: an injective ring hom into a field
(`IsFractionRing.injective`, since `O` is a domain) is automatically injective as a scalar action
(`faithfulSMul_iff_algebraMap_injective`). This is what lets `FractionRing.liftAlgebra` below apply
to this file's `K`. -/
instance faithfulSMul_of_isFractionRing : FaithfulSMul O K :=
  (faithfulSMul_iff_algebraMap_injective O K).mpr (IsFractionRing.injective O K)

attribute [local instance] FractionRing.liftAlgebra

/-- **`K_1 := K(F_π[π])`**, the field generated over `O`'s field of fractions by the `π`-torsion
points of the Lubin-Tate formal group law `F_π` inside `K`. The first step of the tower
`K_n := K(F_π[π^n])` that `ROADMAP.md` §27 points toward. -/
def K_1 (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    IntermediateField (FractionRing O) K :=
  IntermediateField.adjoin (FractionRing O) (piTorsion (K := K) hπ hf 1 : Set K)

omit [Finite (ResidueField O)] in
/-- **`hsplit` transports downward to `K_1`.** Given `Q := P.divX` splits completely inside `K`
(`hsplit`, the hypothesis `card_piTorsion_one_eq_residueCard` needs), it also splits completely
inside `K_1 := K(F_π[π])`, viewed (as it naturally is) as a polynomial over `Frac(O)`: `K_1`'s
generators (`piTorsion hπ hf 1`) already contain every root of `Q`'s image in `K`
(`mem_piTorsion_one_of_root_divX_map`), so `IntermediateField.splits_of_splits` applies directly to
`Q.map (algebraMap O (FractionRing O))`, after re-expressing `Q`'s image in `K` as that polynomial
further mapped down (`Polynomial.map_map` + `IsScalarTower.algebraMap_eq`). This resolves
`ROADMAP.md`'s `hsplit`/`K_1` framing question on its positive side: not "by construction" alone,
but for free once `hsplit` is already known for `K`; `hsplit` for `K` itself remains a hypothesis
that has to be checked directly (the negative half of the framing question, unaffected by this
theorem). The conclusion is stated over `Frac(O)` rather than `O` directly
(`Q.map (algebraMap O K_1)`) because `IntermediateField.splits_of_splits` only ever needs the
primary `Algebra (FractionRing O) K_1` structure `IntermediateField` already supplies — no
`Algebra O K_1` instance needs to be built (see the module docstring's diamond discussion). `O` and
`K` are supplied explicitly at every `K_1` application (`K_1 (O := O) (K := K) hπ hf`) to work
around a confirmed Lean elaboration-order issue: typeclass search on `K_1 hπ hf`'s coeSort gets
"stuck" with `O`/`K` as metavariables unless they are pinned before the application elaborates. -/
theorem splits_map_K_1_of_splits
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    (hsplit : (P.divX.map (algebraMap O K)).Splits) :
    ((P.divX.map (algebraMap O (FractionRing O))).map
      (algebraMap (FractionRing O) (K_1 (O := O) (K := K) hπ hf))).Splits := by
  classical
  have hmapK : (P.divX.map (algebraMap O (FractionRing O))).map (algebraMap (FractionRing O) K)
      = P.divX.map (algebraMap O K) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq O (FractionRing O) K]
  have hsplit' :
      ((P.divX.map (algebraMap O (FractionRing O))).map (algebraMap (FractionRing O) K)).Splits := by
    rw [hmapK]; exact hsplit
  have hF : ∀ x ∈ (P.divX.map (algebraMap O (FractionRing O))).rootSet K,
      x ∈ K_1 (O := O) (K := K) hπ hf := by
    intro x hx
    rw [Polynomial.rootSet_def, Polynomial.aroots_def, hmapK] at hx
    exact IntermediateField.subset_adjoin (FractionRing O) (piTorsion (K := K) hπ hf 1 : Set K)
      (mem_piTorsion_one_of_root_divX_map hOK hπ hπnorm hf hu heq hPdist hPdeg2 hx)
  exact IntermediateField.splits_of_splits (F := K_1 (O := O) (K := K) hπ hf) hsplit' hF

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **`[Frac(O)(α) : Frac(O)] = q - 1` for any single root `α` of `Q := P.divX`'s image in `K`** —
pure minimal-polynomial theory, no group action or splitting hypothesis needed (unlike `K_1` itself,
which adjoins *all* of `piTorsion hπ hf 1` at once). `Q' := P.divX` base-changed to `Frac(O)` is
monic and irreducible (`Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated`, specialized
at `K := FractionRing O`, i.e. Gauss's lemma applied to `Frac(O)` itself); `α`'s vanishing on `Q`'s
image in `K` transports down to vanishing on `Q'` via `Polynomial.aeval_map_algebraMap` applied
twice (once to strip `K`'s map, once to reinterpret the result as `Q'`'s map into `K` through the
scalar tower `O → Frac(O) → K`), so `Q' = minpoly (FractionRing O) α`
(`minpoly.eq_of_irreducible_of_monic`) and `IntermediateField.adjoin.finrank` gives the degree
directly as `Q'.natDegree = P.divX.natDegree = residueCard O - 1`. -/
theorem finrank_adjoin_of_aeval_divX_map_eq_zero (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) {x : K}
    (hx : Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0) :
    Module.finrank (FractionRing O) (IntermediateField.adjoin (FractionRing O) ({x} : Set K))
      = residueCard O - 1 := by
  have hf0 : PowerSeries.coeff 0 f = 0 := hf.1
  have hf1 : PowerSeries.coeff 1 f = π := hf.2.1
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  set Q' : (FractionRing O)[X] := P.divX.map (algebraMap O (FractionRing O)) with hQ'def
  have hQ'irr : Irreducible Q' :=
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hπ hQmonic hQweak hQdeg hQ0assoc
  have hQ'monic : Q'.Monic := hQmonic.map _
  haveI := FractionRing.isScalarTower_liftAlgebra O K
  have hxQ' : Polynomial.aeval x Q' = Polynomial.aeval x P.divX :=
    Polynomial.aeval_map_algebraMap (FractionRing O) x P.divX
  have haevalQO : Polynomial.aeval x P.divX = 0 := by
    rw [← Polynomial.aeval_map_algebraMap K x P.divX]
    exact hx
  have hx' : Polynomial.aeval x Q' = 0 := hxQ'.trans haevalQO
  have hInt : IsIntegral (FractionRing O) x := ⟨Q', hQ'monic, hx'⟩
  have hmin : Q' = minpoly (FractionRing O) x :=
    minpoly.eq_of_irreducible_of_monic hQ'irr hx' hQ'monic
  rw [IntermediateField.adjoin.finrank hInt, ← hmin, hQ'def,
    Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective O (FractionRing O)),
    Polynomial.natDegree_divX_eq_natDegree_tsub_one, hPdeg]

end LubinTate

end
