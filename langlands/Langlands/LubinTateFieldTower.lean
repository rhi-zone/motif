import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Langlands.LubinTateTorsionPoints

/-!
# The base-field embedding and `K_1 = K(F_π[π])`

`ROADMAP.md` §27's pointer-forward: the natural next step after the torsion-point group
`piTorsion hπ hf n` (packaged as an `AddCommGroup` in `Langlands.LubinTateTorsionGroup`) is the
field extension `K_1 := K(F_π[π])` and the tower `K_n := K(F_π[π^n])`.

Both `piTorsion` and the ambient evaluation field `K` are already parametrized abstractly: `O` is
the base complete discrete valuation ring, `K` is *any* `NormedField` with `[Algebra O K]` in which
`O`'s image lies in the closed unit ball. To adjoin torsion points to a genuine *base field*
(rather than the base ring `O`), this file supplies `O`'s field of fractions as an intermediate
field base point, using Mathlib's own fraction-field machinery
(`IsFractionRing.lift`/`FractionRing.liftAlgebra`) rather than a bespoke `F`/`K` split or an
assumption that `K` itself already is `Frac(O)`.

## Main results

* `FractionRing.liftAlgebra` (Mathlib, made a local instance here): given
  `[FaithfulSMul O K]` — `algebraMap O K` injective, phrased the way Mathlib's fraction-ring
  machinery wants it (`faithfulSMul_iff_algebraMap_injective`) — this supplies
  `Algebra (FractionRing O) K`, compatible with the existing `Algebra O K` via
  `FractionRing.isScalarTower_liftAlgebra : IsScalarTower O (FractionRing O) K`. Mathlib does not
  make this an instance globally (it would create a diamond when `K = FractionRing O` itself), so
  it is activated locally in this file only.
* `K_1` : `IntermediateField.adjoin (FractionRing O) (piTorsion hπ hf 1 : Set K)`, the field
  generated over `Frac(O)` by the `π`-torsion points of `F_π` inside `K`.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open IsLocalRing PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [FaithfulSMul O K]
variable {π : O} {f : O⟦X⟧}

attribute [local instance] FractionRing.liftAlgebra

/-- **`K_1 := K(F_π[π])`**, the field generated over `O`'s field of fractions by the `π`-torsion
points of the Lubin-Tate formal group law `F_π` inside `K`. The first step of the tower
`K_n := K(F_π[π^n])` that `ROADMAP.md` §27 points toward. -/
def K_1 (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    IntermediateField (FractionRing O) K :=
  IntermediateField.adjoin (FractionRing O) (piTorsion (K := K) hπ hf 1 : Set K)

end LubinTate

end
