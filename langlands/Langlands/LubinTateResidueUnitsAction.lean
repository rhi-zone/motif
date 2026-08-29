import Langlands.LubinTateModPiFactoring

/-!
# The `Oˣ`-action on nonzero `π`-torsion factors through a genuine `(O/π)ˣ`-action

The mod-`π` factoring fact `eval_phiU_eq_of_dvd_sub` — `u ≡ v (mod π)` in `Oˣ` forces `eval (phiU
hπ hf u) α = eval (phiU hπ hf v) α` exactly, for `α` a nonzero element of `piTorsion hπ hf 1` —
assembles into an actual `MulAction` of `(O/π)ˣ` on the torsion. This file does that assembly: it
takes `IsLocalRing.ResidueField O` (already the repo's concrete model for `O/π` via `residueCard O
:= Nat.card (ResidueField O)`) as the model for `O/π`, packages the reduction homomorphism `Oˣ →*
(ResidueField O)ˣ`, and lifts `piTorsionMulAction` along it.

## Route

* `residueUnitsMap : Oˣ →* (ResidueField O)ˣ := Units.map (IsLocalRing.residue O)`.
* `residueUnitsMap_surjective` : surjective, from `IsLocalRing.residue_surjective` (any `y ≠ 0` in
  `ResidueField O` lifts to some `x : O`, and `x` is automatically a unit,
  `residue_ne_zero_iff_isUnit`).
* `residueUnitsMap_eq_iff_dvd_sub` : `residueUnitsMap u = residueUnitsMap v ↔ π ∣ ((u:O)-(v:O))`,
  translating `Units.ext_iff` through `residue_eq_zero_iff` and `hπ.maximalIdeal_eq : maximalIdeal
  O = Ideal.span {π}`.
* Combining these two with `eval_phiU_eq_of_dvd_sub` (extended to *all* of `piTorsion hπ hf 1`,
  including `0`, where both sides vanish trivially) gives: **the `Oˣ`-action on `piTorsion hπ hf 1`
  is constant on fibers of `residueUnitsMap`.**
* The `(ResidueField O)ˣ`-action itself is defined via `Function.surjInv
  residueUnitsMap_surjective` — for `u' : (ResidueField O)ˣ`, act by `piTorsionMulAction`'s `•`
  through the chosen preimage `Function.surjInv residueUnitsMap_surjective u' : Oˣ`. The
  `MulAction` laws (`one_smul`, `mul_smul`) transport from `piTorsionMulAction`'s own laws plus the
  fiber-constancy fact above, applied to the two pairs of units that `residueUnitsMap` (a monoid
  hom) sends to the same value by construction (`Function.rightInverse_surjInv` +
  `MonoidHom.map_one`/`MonoidHom.map_mul`).

## What this does not do

Freeness and transitivity of the resulting `(ResidueField O)ˣ`-action are not attempted here; see
`Langlands/LubinTateResidueUnitsFreeness.lean` and `Langlands/LubinTateResidueUnitsTransitivity.lean`.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open NonarchimedeanPowerSeriesEval PowerSeries IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [FaithfulSMul O K]
variable {π : O} {f : O⟦X⟧}

/-! ### The reduction homomorphism `Oˣ →* (ResidueField O)ˣ` -/

/-- **The reduction map `Oˣ → (ResidueField O)ˣ`**, `(O/π)ˣ`'s concrete model in this repo. -/
abbrev residueUnitsMap : Oˣ →* (ResidueField O)ˣ := Units.map (IsLocalRing.residue O)

omit [Finite (ResidueField O)] in
/-- **`residueUnitsMap` is surjective.** Any `y : (ResidueField O)ˣ` lifts (`residue_surjective`)
to some `x : O` with `residue O x = y ≠ 0`, forcing `x` to be a unit (`residue_ne_zero_iff_isUnit`);
`x`'s unit witness maps to `y` under `residueUnitsMap`. -/
theorem residueUnitsMap_surjective : Function.Surjective (residueUnitsMap (O := O)) := by
  intro y
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := O) (y : ResidueField O)
  have hxu : IsUnit x := (IsLocalRing.residue_ne_zero_iff_isUnit x).mp (hx ▸ y.ne_zero)
  refine ⟨hxu.unit, Units.ext ?_⟩
  show IsLocalRing.residue O (hxu.unit : O) = (y : ResidueField O)
  rw [hxu.unit_spec]
  exact hx

omit [Finite (ResidueField O)] in
/-- **`residueUnitsMap u = residueUnitsMap v` iff `π ∣ (u - v)`.** Translates `Units.ext_iff`
through `residue_eq_zero_iff` and `hπ.maximalIdeal_eq`. -/
theorem residueUnitsMap_eq_iff_dvd_sub (hπ : Irreducible π) {u v : Oˣ} :
    residueUnitsMap u = residueUnitsMap v ↔ π ∣ ((u : O) - (v : O)) := by
  rw [Units.ext_iff]
  show IsLocalRing.residue O (u : O) = IsLocalRing.residue O (v : O) ↔ _
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq,
    Ideal.mem_span_singleton]

/-! ### The `Oˣ`-action is constant on fibers of `residueUnitsMap` -/

/-- **`eval_phiU_eq_of_dvd_sub`, extended to all of `piTorsion hπ hf 1` (including `0`).** At `α =
0` both sides vanish (`eval_zero_of_coeff_zero_eq_zero`); the nonzero case is exactly
`eval_phiU_eq_of_dvd_sub`. -/
theorem eval_phiU_eq_of_dvd_sub' (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {w : O⟦X⟧} (hw : IsUnit w)
    (heq : f = (P : O⟦X⟧) * w) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg2 : 2 ≤ P.natDegree) {u v : Oˣ} (huv : π ∣ ((u : O) - (v : O)))
    {α : K} (hα : α ∈ piTorsion (K := K) hπ hf 1) :
    eval (phiU hπ hf u) α = eval (phiU hπ hf v) α := by
  rcases eq_or_ne α 0 with hα0 | hα0
  · subst hα0
    rw [eval_zero_of_coeff_zero_eq_zero
        (by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact constantCoeff_phiU hπ hf u),
      eval_zero_of_coeff_zero_eq_zero
        (by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact constantCoeff_phiU hπ hf v)]
  · exact eval_phiU_eq_of_dvd_sub hOK hπ hπnorm hf hw heq hPdist hPdeg2 huv hα hα0

/-- **The `Oˣ`-action on `piTorsion hπ hf 1` is constant on fibers of `residueUnitsMap`**: if
`residueUnitsMap u = residueUnitsMap v`, then `u` and `v` act identically on every element of
`piTorsion hπ hf 1`. -/
theorem piTorsionSMul_eq_of_residueUnitsMap_eq (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {w : O⟦X⟧} (hw : IsUnit w)
    (heq : f = (P : O⟦X⟧) * w) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg2 : 2 ≤ P.natDegree) {u v : Oˣ} (huv : residueUnitsMap u = residueUnitsMap v)
    {α : K} (hα : α ∈ piTorsion (K := K) hπ hf 1) :
    eval (phiU hπ hf u) α = eval (phiU hπ hf v) α :=
  eval_phiU_eq_of_dvd_sub' hOK hπ hπnorm hf hw heq hPdist hPdeg2
    ((residueUnitsMap_eq_iff_dvd_sub hπ).mp huv) hα

/-! ### The induced `(ResidueField O)ˣ`-action -/

/-- **`SMul (ResidueField O)ˣ` on `piTorsion hπ hf 1`**, acting through a chosen `Oˣ`-preimage
(`Function.surjInv residueUnitsMap_surjective`) via `piTorsionMulAction`'s `•`. -/
@[reducible] def residuePiTorsionSMul (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]}
    {w : O⟦X⟧} (hw : IsUnit w) (heq : f = (P : O⟦X⟧) * w)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree) :
    SMul (ResidueField O)ˣ ↥(piTorsion (K := K) hπ hf 1) :=
  letI := piTorsionMulAction hOK hπ hf 1
  ⟨fun u' x ↦ Function.surjInv residueUnitsMap_surjective u' • x⟩

omit [FaithfulSMul O K] in
/-- **`residuePiTorsionSMul` really is `piTorsionMulAction`'s `•`, through the chosen preimage**
(true by definition). -/
theorem residuePiTorsionSMul_def (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]}
    {w : O⟦X⟧} (hw : IsUnit w) (heq : f = (P : O⟦X⟧) * w)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    (u' : (ResidueField O)ˣ) (x : ↥(piTorsion (K := K) hπ hf 1)) :
    letI := piTorsionMulAction hOK hπ hf 1
    letI := residuePiTorsionSMul (K := K) hOK hπ hπnorm hf hw heq hPdist hPdeg2
    u' • x = Function.surjInv residueUnitsMap_surjective u' • x := rfl

/-- **`piTorsion hπ hf 1` is a genuine `(ResidueField O)ˣ`-action.** `one_smul`/`mul_smul` transport
from `piTorsionMulAction`'s own laws plus `piTorsionSMul_eq_of_residueUnitsMap_eq`, applied to the
pairs of `Oˣ`-witnesses that `residueUnitsMap` — a monoid hom — sends to the same value:
`residueUnitsMap (surjInv u') = u'` (`Function.rightInverse_surjInv`) makes
`residueUnitsMap (surjInv 1) = residueUnitsMap 1` and `residueUnitsMap (surjInv (u'*v')) =
residueUnitsMap (surjInv u' * surjInv v')` hold by direct computation. -/
@[reducible] def residuePiTorsionMulAction (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]}
    {w : O⟦X⟧} (hw : IsUnit w) (heq : f = (P : O⟦X⟧) * w)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree) :
    MulAction (ResidueField O)ˣ ↥(piTorsion (K := K) hπ hf 1) :=
  letI := piTorsionMulAction hOK hπ hf 1
  letI := residuePiTorsionSMul (K := K) hOK hπ hπnorm hf hw heq hPdist hPdeg2
  { one_smul := fun x ↦ by
      have hdef : (1 : (ResidueField O)ˣ) • x = Function.surjInv residueUnitsMap_surjective 1 • x :=
        residuePiTorsionSMul_def hOK hπ hπnorm hf hw heq hPdist hPdeg2 1 x
      rw [hdef]
      have hfib : residueUnitsMap (Function.surjInv residueUnitsMap_surjective (1 : (ResidueField O)ˣ)) =
          residueUnitsMap (1 : Oˣ) := by
        rw [map_one]
        exact Function.rightInverse_surjInv residueUnitsMap_surjective 1
      apply Subtype.ext
      show eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective 1)) (x : K) = (x : K)
      rw [piTorsionSMul_eq_of_residueUnitsMap_eq hOK hπ hπnorm hf hw heq hPdist hPdeg2 hfib x.2]
      exact congrArg Subtype.val (one_smul Oˣ x)
    mul_smul := fun u' v' x ↦ by
      have hdefUV : (u' * v') • x =
          Function.surjInv residueUnitsMap_surjective (u' * v') • x :=
        residuePiTorsionSMul_def hOK hπ hπnorm hf hw heq hPdist hPdeg2 (u' * v') x
      have hdefV : v' • x = Function.surjInv residueUnitsMap_surjective v' • x :=
        residuePiTorsionSMul_def hOK hπ hπnorm hf hw heq hPdist hPdeg2 v' x
      have hdefU : u' • (v' • x) =
          Function.surjInv residueUnitsMap_surjective u' •
            (Function.surjInv residueUnitsMap_surjective v' • x) := by
        rw [hdefV]
        exact residuePiTorsionSMul_def hOK hπ hπnorm hf hw heq hPdist hPdeg2 u'
          (Function.surjInv residueUnitsMap_surjective v' • x)
      rw [hdefUV, hdefU]
      have hfib : residueUnitsMap
          (Function.surjInv residueUnitsMap_surjective (u' * v')) =
          residueUnitsMap
            (Function.surjInv residueUnitsMap_surjective u' *
              Function.surjInv residueUnitsMap_surjective v') := by
        rw [map_mul, Function.rightInverse_surjInv residueUnitsMap_surjective u',
          Function.rightInverse_surjInv residueUnitsMap_surjective v']
        exact Function.rightInverse_surjInv residueUnitsMap_surjective (u' * v')
      apply Subtype.ext
      show eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective (u' * v'))) (x : K) =
        eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective u'))
          (eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective v')) (x : K))
      rw [piTorsionSMul_eq_of_residueUnitsMap_eq hOK hπ hπnorm hf hw heq hPdist hPdeg2 hfib x.2]
      exact congrArg Subtype.val (mul_smul (Function.surjInv residueUnitsMap_surjective u')
        (Function.surjInv residueUnitsMap_surjective v') x) }

/-- **The `(ResidueField O)ˣ`-action really is `[u]_F`, evaluated at a chosen `Oˣ`-preimage** (true
by definition; recorded so downstream uses need not unfold the structure). -/
theorem coe_residuePiTorsion_smul (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]}
    {w : O⟦X⟧} (hw : IsUnit w) (heq : f = (P : O⟦X⟧) * w)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    (u' : (ResidueField O)ˣ) (x : ↥(piTorsion (K := K) hπ hf 1)) :
    letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
    ((u' • x : ↥(piTorsion (K := K) hπ hf 1)) : K) =
      eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective u')) (x : K) := by
  letI := piTorsionMulAction hOK hπ hf 1
  show ((Function.surjInv residueUnitsMap_surjective u' • x :
    ↥(piTorsion (K := K) hπ hf 1)) : K) = _
  rw [coe_piTorsion_smul]

end LubinTate

end
