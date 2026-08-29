import Langlands.LubinTateRootCount

/-!
# `hsplit` is unsatisfiable whenever `residueCard O ≥ 3`

`Langlands.LubinTate.card_piTorsion_one_eq_residueCard` (`LubinTateRootCount.lean`) and everything
built on it in this repo (`K_1`, `finrank_adjoin_of_aeval_divX_map_eq_zero`,
`LubinTateResidueUnitsTransitivity.lean`'s `orbit_image_eq_piTorsion_sdiff_zero`) take `hsplit :
(P.divX.map (algebraMap O K)).Splits` as an explicit hypothesis — `Q := P.divX`'s image splits
completely *inside `K` itself*, the design choice `LubinTateRootCount.lean`'s docstring flags as
deliberately preferring "`K` itself already contains the roots" over an abstract splitting field.

**This file shows that design choice makes `hsplit` jointly unsatisfiable with this repo's other
standing hypotheses whenever `P.divX.natDegree ≥ 2`, i.e. `residueCard O ≥ 3`.** The obstruction:
`[IsFractionRing O K]` (already required throughout `LubinTateRootCount.lean`/`LubinTateFieldTower.lean`)
plus the Weierstrass/Eisenstein data already available (`divX_isWeaklyEisensteinAt_and_associated`)
gives, via `Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated`, that `Q`'s image **is
irreducible over `K` itself** (not just over `Frac(O)` abstractly — `K` *is* `Frac(O)` up to the
canonical isomorphism `[IsFractionRing O K]` supplies). An irreducible polynomial of degree `≥ 2`
over a field has no root in that field (`Polynomial.degree_eq_one_of_irreducible_of_root`), so it
cannot split completely there either (`Polynomial.Splits.natDegree_eq_card_roots` would force a
root to exist). `hsplit` and irreducibility-of-degree-`≥2` are jointly contradictory.

## Consequence

`card_piTorsion_one_eq_residueCard` (and everything downstream depending on `hsplit`, including
`orbit_image_eq_piTorsion_sdiff_zero` in `LubinTateResidueUnitsTransitivity.lean`) is **vacuously
true** whenever `residueCard O ≥ 3` — its hypotheses can never be jointly satisfied, so it proves
nothing about any actual instantiation with a nontrivial residue field. It is only *non-vacuously*
meaningful at `residueCard O = 2` (`P.divX.natDegree = 1`, where `hsplit` trivially holds since every
degree-`1` polynomial splits over its own base field, and the whole arc collapses to the trivial
extension `K_1 = K`).

This does not mean any individual proof in this repo is *wrong* — every theorem built on `hsplit`
remains a logically valid implication `hsplit → ...`. It means `hsplit`, as formalized (splitting
*inside `K` itself*, with `K = Frac(O)` forced by `[IsFractionRing O K]`), can never be discharged
for the mathematically interesting case (`q ≥ 3`, where Lubin-Tate theory's `K_1/K` is a genuine
*ramified extension*, not contained in `K`). Fixing the design would mean building `K_1` as a
genuine extension field, rather than as a subfield of a `K` assumed to already contain the torsion
points.

## Main result

* `false_of_isFractionRing_splits_irreducible` : the general obstruction, independent of Lubin-Tate
  content — `Irreducible p`, `p.Splits`, `2 ≤ p.natDegree` are jointly inconsistent for any `p : K[X]`
  over a field `K`.
* `false_of_hsplit_of_two_le_divX_natDegree` : the Lubin-Tate-specific instantiation, showing
  `card_piTorsion_one_eq_residueCard`'s own hypotheses are unsatisfiable whenever `2 ≤
  P.divX.natDegree` (i.e. `residueCard O ≥ 3`).
-/

@[expose] public section

noncomputable section

open scoped Polynomial

open Polynomial IsLocalRing PowerSeries

/-- **An irreducible polynomial of degree `≥ 2` cannot split completely over its own base field.**
General fact, no Lubin-Tate content: a root forced by `Splits.natDegree_eq_card_roots` would give
`p.degree = 1` (`Polynomial.degree_eq_one_of_irreducible_of_root`), contradicting `2 ≤ p.natDegree`. -/
theorem false_of_isFractionRing_splits_irreducible {K : Type*} [Field K] {p : K[X]}
    (hirr : Irreducible p) (hsplit : p.Splits) (hdeg : 2 ≤ p.natDegree) : False := by
  have hcard := hsplit.natDegree_eq_card_roots
  have hpos : 0 < p.roots.card := by omega
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  rw [Polynomial.mem_roots'] at hx
  have hdeg1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr hx.2
  have hnd1 : p.natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some hdeg1
  omega

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
variable {π : O} {f : O⟦X⟧}

/-- **`card_piTorsion_one_eq_residueCard`'s hypotheses are jointly unsatisfiable whenever `2 ≤
P.divX.natDegree`** (i.e. `residueCard O ≥ 3`, since `P.divX.natDegree = residueCard O - 1` under
`hPdeg : P.natDegree = residueCard O`). `Q := P.divX`'s image in `K` is irreducible
(`Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated`, using `[IsFractionRing O K]`) of
degree `≥ 2`, so it cannot also split completely in `K`
(`false_of_isFractionRing_splits_irreducible`). -/
theorem false_of_hsplit_of_two_le_divX_natDegree {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hf0 : PowerSeries.coeff 0 f = 0) (hπ : Irreducible π)
    (hf1 : PowerSeries.coeff 1 f = π) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg2 : 2 ≤ P.natDegree) (hsplit : (P.divX.map (algebraMap O K)).Splits)
    (hdeg2 : 2 ≤ P.divX.natDegree) : False := by
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  have hirr : Irreducible (P.divX.map (algebraMap O K)) :=
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hπ hQmonic hQweak hQdeg hQ0assoc
  have hdegmap : (P.divX.map (algebraMap O K)).natDegree = P.divX.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective O K) P.divX
  exact false_of_isFractionRing_splits_irreducible hirr hsplit (hdegmap ▸ hdeg2)

end LubinTate

end
