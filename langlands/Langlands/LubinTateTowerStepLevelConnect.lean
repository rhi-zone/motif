/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelGeneric

/-!
# The connecting identity, generic in `Level`

`Level` bundles `L`, its normed-field/completeness instances, `algL : Algebra K L` as a plain stored
field, and `finiteDim`; the generic `Algebra K K_n`/norm-bound pieces built against it are elsewhere
(`Langlands/LubinTateTowerStepLevelGeneric.lean`). This file closes the connecting identity itself,
generically — the piece those files left unattempted: formalizing "level `n`'s data" as an actual
Lean argument type usable by the connecting-identity/transitivity/invariance/degree/monogenicity
chain.

## What the two concrete templates actually needed, diffed directly

`eval_f_eq_of_aeval_P₂_eq_zero` (`Langlands/LubinTateTowerStepRootConnect.lean`, the `K_1 → K_2`
step) and `eval_f_eq_of_aeval_P₃_eq_zero` (`Langlands/LubinTateTowerStepK3RootConnect.lean`, the
`K_2 → K_3` step) run the same argument: chain the Weierstrass factorization
`shifted f ψ gen = (P_{n+1} : _⟦X⟧) * u_{n+1}` through `eval` (`eval_mul`/`eval_sub`/`eval_C`, with a
norm bound for `‖root‖ < 1` and the level's own "`O_L`-elements have norm `≤ 1`" bound discharging
their coefficient hypotheses), then a naturality lemma for `eval` under `ψ` to land on `eval f root`.

They differ in exactly one place, re-derived here by reading both proofs in full rather than taken on
report: the `K_1 → K_2` version's conclusion is stated at the **field** level, `algebraMap (K_1 P) baseChangeSplittingField
α`, reached from the ring-of-integers-valued statement by one extra `IsScalarTower.algebraMap_apply`
rewrite along an extra hypothesis `hα'coe : (α' : K_1 P) = α`; the `K_2 → K_3` version's conclusion is
`algebraMap O_{K_2} K_3 β'` directly, its own docstring calling it *"Simpler in one respect than that
template: since `β'` is already an `O_{K_2}` element (not a field-level `α` reached via a separate
`hα'coe` witness), the conclusion is stated directly as `algebraMap O_{K_2} K_3 β'`, with no
intermediate field-level identification needed."* The generic theorem here is stated in the
`K_2 → K_3` shape (conclusion `algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) gen`); `hα'coe` re-enters only
at the `level_K_1` instantiation below, as the one extra rewrite it always was.

## What is genuinely new here, and one non-defeq pair found along the way

Both templates' structure maps and `Algebra O K_{n+1}` composites turn out to be **literally the same
term** as their `Level`-generic counterparts, not merely equivalent — confirmed by `rfl`, not asserted:
`Level.towerHom` is `towerHom hOK P` at `level_K_1` and `towerHom2 P₂ hOK` at `level_K_2`, and
`Level.instAlgebraO` is `K_2.instAlgebraO` and `K_3.instAlgebraO` respectively. (`towerHom` goes
`O → ↥𝒪[K] → O_{K_1}` and `towerHom2` goes `O → ↥𝒪[K] → O_{K_2}`; with the *flat* `O_{K_2}` spelling,
both are the single generic composite `(algebraMap ↥𝒪[K] lvl.OL).comp
(toValuationSubring hOK)`. Under a nested spelling they would not have been.)

**A non-defeq pair found, and worked around by restating rather than bridging**:
`Level.norm_le_one_of_mem_algebraMap_OL` states its bound against an `Algebra lvl.OL
(baseChangeSplittingField (K' := lvl.L) P₂)` instance it introduces *itself*, by `letI`, as the explicit composite
`((algebraMap lvl.L (baseChangeSplittingField …)).comp (algebraMap lvl.OL lvl.L)).toAlgebra`. Feeding it to
`norm_coeff_map_of_isWeaklyEisensteinAt_associated` (which takes that class by ordinary instance
search) fails, with Lean reporting directly:

> synthesized type class instance is not definitionally equal to expression inferred by typing rules,
> synthesized `(integralClosure (↥(ValuativeRel.valuation K).valuationSubring) lvl.L).toAlgebra`,
> inferred `((algebraMap lvl.L (baseChangeSplittingField Pn)).comp (algebraMap lvl.OL lvl.L)).toAlgebra`

These two *are* defeq at both concrete depths — that is exactly what the `funext`+`rfl`
checks against `K_2.norm_le_one_of_mem_O_K1`/`K_3.norm_le_one_of_mem_O_K2` establish — but not
generically in `lvl`. This is **not** a diamond in the usual sense (there is still exactly one stored
`algL`, and both terms are functions of it); it is that earlier lemma having baked a *chosen* composite
into its statement where the concrete templates' statements use the search-found one. The fix taken
is to restate the bound against the search-found instance (`Level.norm_le_one_of_mem_OL_next`,
proved through `IsScalarTower.algebraMap_apply` exactly as `K_2.norm_le_one_of_mem_O_K1` and
`K_3.norm_le_one_of_mem_O_K2` themselves are), **not** to bridge the two instances with a cast —
which is also why the `rfl` checks below against the real theorems are meaningful.

## Where the step data lives: a new structure, not extra `Level` fields

`Level K` is parametrized by `K` alone. The generator/Weierstrass data is not: it depends on `O`,
on the Lubin-Tate series `f : O⟦X⟧`, and on `hOK` (through `Level.towerHom hOK`, which the Weierstrass
equation names). Adding it to `Level` would therefore force the `Algebra K K_n`/
norm-bound generics in `Langlands/LubinTateTowerStepLevelGeneric.lean` — none of which mention `O` or `f` at all — to carry it, and would break both
concrete `Level` values. So the data goes in a separate `TowerStep f hOK` bundling `lvl : Level K`
plus the step data, leaving `Level` itself unchanged.

**No new diamond is introduced by the extension**, checked rather than assumed: every new field's type
is built from `lvl.OL`, whose `CommRing`/`Algebra` structure is derived by ordinary typeclass search
from the single stored `lvl.algL` — there is no second route to it, and the concrete
`TowerStep` values below elaborate at default heartbeats. The two `Prop`-class fields `[instDomain :
IsDomain lvl.OL]`/`[instDVR : IsDiscreteValuationRing lvl.OL]` (needed to write `shifted` and
`maximalIdeal lvl.OL` at all, and not derivable generically — no lemma in this repo constructs them,
matching how both concrete templates obtain them: globally for `O_{K_1}`, as ambient hypotheses for
`O_{K_2}`) cannot form a data-level diamond either, since `IsLocalRing` is reached through both and
definitional proof irrelevance identifies the two routes. They are deliberately **not** promoted to
global instances (matching `algL`'s own treatment); they are activated by `letI` at the one use
site.

## Main results

* `Level.towerHom` : the generic structure map `O →+* lvl.OL`; `rfl`-equal to `towerHom hOK P` at
  `level_K_1` and to `towerHom2 P₂ hOK` at `level_K_2`.
* `Level.instAlgebraO` : the generic three-hop `Algebra O (baseChangeSplittingField (K' := lvl.L) Pn)`; `rfl`-equal to
  `K_2.instAlgebraO` and `K_3.instAlgebraO` at those two depths.
* `Level.eval_map_towerHom` : naturality of `eval` under `Level.towerHom`. Unlike `eval_map_towerHom2`
  (which had to repeat `NonarchimedeanPowerSeriesEval.eval_map`'s proof to sidestep an elaboration
  snag at the doubly-nested concrete type), this closes by invoking `eval_map` directly with `fun _ =>
  rfl`.
* `Level.faithfulSMul_OL`, `Level.norm_le_one_of_mem_OL_next` : the two side facts the Eisenstein-shape
  norm computation needs, generic in `lvl`.
* `Level.norm_lt_one_of_root` : a root of `Pn`'s image lies in the open unit ball — the generic
  `norm_lt_one_of_aeval_P₂_eq_zero`/`norm_lt_one_of_aeval_P₃_eq_zero`.
* `Level.eval_f_eq_of_root` : **the generic connecting identity**.
* `Level.next` : the next `Level`, one hop up. `(level_K_1).next P₂ = level_K_2 P₂` **by `rfl`** — the
  concrete depth-2 level value is literally the generic successor of the depth-1 one.
* `TowerStep`, `TowerStep.eval_f_eq_of_root` : the bundled step data and the connecting identity
  against it.
* Two concrete checks, `rfl`-against-the-real-theorem: the bundled theorem, instantiated at a `TowerStep` built over `level_K_1` from
  `eval_f_eq_of_aeval_P₂_eq_zero`'s own hypotheses (plus its `hα'coe` rewrite), is `rfl`-equal to
  `eval_f_eq_of_aeval_P₂_eq_zero` itself; instantiated at a `TowerStep` over `level_K_2`, it is
  `rfl`-equal to `eval_f_eq_of_aeval_P₃_eq_zero` itself.

## What this does not close

**Not attempted**: the transitivity/invariance/degree/monogenicity remainder of the chain. Both
concrete files derive transitivity (`exists_piTorsion_translate_of_aeval_P₂_eq_zero`/
`…_P₃_eq_zero`) from the connecting identity plus a `hOK_transport` fact and
`exists_piTorsion_translate_of_eval_f_eq`; the generic `hOK_transport` is not built here.
**Not built**: any `TowerStep → TowerStep` successor map. `Level.next` supplies the *field* half of
the induction step and is `rfl`-checked against the real depth-2 value, but producing the next
step's generator/Weierstrass data is exactly what `exists_eisenstein_tower_step_K_2` does concretely,
and no generic version of that exists. **Not derived**: `Level.eval_f_eq_of_root`'s
`hα'norm` hypothesis, carried explicitly here exactly as both concrete templates carry it.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open IsLocalRing PowerSeries Polynomial NonarchimedeanPowerSeriesEval

universe v

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]

/-! ## The generic structure map, algebra composite, and naturality -/

/-- **The generic tower structure map `O →+* lvl.OL`**, the composite `O → ↥𝒪[K] → lvl.OL`.
Generalizes `towerHom` (`O → ↥𝒪[K] → O_{K_1}`) and `towerHom2` (`O → ↥𝒪[K] → O_{K_2}`) at once — and
is `rfl`-equal to each at the corresponding concrete `Level`, checked below. The middle hop is the
`lvl.OL` subalgebra inclusion out of `↥𝒪[K]`, which is available precisely because `Level.OL` derives
its `Algebra ↥𝒪[K] lvl.L` from the structure's own stored `algL`. -/
def Level.towerHom (lvl : Level K) (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) : O →+* lvl.OL :=
  letI := lvl.algL
  (algebraMap ↥(ValuativeRel.valuation K).valuationSubring lvl.OL).comp
    (toValuationSubring (K := K) hOK)

/-- **The generic `Algebra O (baseChangeSplittingField (K' := lvl.L) Pn)`**, the explicit three-hop composite
`O →(Level.towerHom hOK)→ lvl.OL →(subalgebra inclusion)→ lvl.L →(algebraMap)→ baseChangeSplittingField (K' := lvl.L) Pn`.
Generalizes `K_2.instAlgebraO`'s three-hop and `K_3.instAlgebraO`'s four-hop composites (the latter's
extra hop is `Level.towerHom`'s own middle hop, so the two are the same composite once
`Level.towerHom` is named); `rfl`-equal to each at the corresponding concrete `Level`, checked below.
As with those, choosing the composite rather than a search-found instance is what makes the
`algebraMap`-unfolding facts hold by `rfl`. -/
@[reducible] def Level.instAlgebraO (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    Algebra O (baseChangeSplittingField (K' := lvl.L) Pn) :=
  letI := lvl.algL
  ((algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)).comp
    ((algebraMap lvl.OL lvl.L).comp (lvl.towerHom hOK))).toAlgebra

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [IsFractionRing O K] in
/-- **`eval` is natural under `Level.towerHom`**, generic in `lvl` — the `Level`-level
`eval_map_towerHom`/`eval_map_towerHom2`. Closes by invoking
`NonarchimedeanPowerSeriesEval.eval_map` directly with `fun _ => rfl` for its `hcomp` hypothesis,
which is possible here (unlike at `eval_map_towerHom2`'s doubly-nested concrete type, where that
exact form hit the elaboration snag `Langlands/LubinTateTowerStepK3RootConnect.lean`'s module
docstring records and the proof had to repeat `eval_map`'s own body instead). -/
theorem Level.eval_map_towerHom (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {f : O⟦X⟧} (x : baseChangeSplittingField (K' := lvl.L) Pn) :
    letI := lvl.instAlgebraO Pn hOK
    NonarchimedeanPowerSeriesEval.eval (PowerSeries.map (lvl.towerHom hOK) f) x =
      NonarchimedeanPowerSeriesEval.eval f x := by
  letI := lvl.algL
  letI := lvl.instAlgebraO Pn hOK
  exact NonarchimedeanPowerSeriesEval.eval_map (lvl.towerHom hOK) (fun _ => rfl) f x

/-! ## The two side facts the Eisenstein-shape norm computation needs -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K] in
/-- **`algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn)` is injective**, generic in `lvl` — the `Level`-level
`K_2.instFaithfulSMul_O_K1`/`K_3.instFaithfulSMul_O_K2`, left unbuilt elsewhere (recovering
`K_2.instFaithfulSMul_O_K1`/`K_3.instFaithfulSMul_O_K2` concretely needs an
extra `faithfulSMul_iff_algebraMap_injective` unwrapping layer) and which
`norm_coeff_map_of_isWeaklyEisensteinAt_associated` genuinely requires. Follows
`K_3.instFaithfulSMul_O_K2`'s own shape: `RingHom.injective _` for the field hop (**not** dot
notation, per that file's elaboration finding), `Subtype.coe_injective` for the subalgebra inclusion,
composed pointwise through `IsScalarTower.algebraMap_apply`. -/
theorem Level.faithfulSMul_OL (lvl : Level K) (Pn : lvl.OL[X]) :
    FaithfulSMul lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h1 : Function.Injective (algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)) := RingHom.injective _
  have h2 : Function.Injective (algebraMap lvl.OL lvl.L) := Subtype.coe_injective
  intro a b hab
  have ha := IsScalarTower.algebraMap_apply lvl.OL lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) a
  have hb := IsScalarTower.algebraMap_apply lvl.OL lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) b
  rw [ha, hb] at hab
  exact h2 (h1 hab)

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K] in
/-- **`lvl.OL`'s elements, algebra-mapped into `baseChangeSplittingField (K' := lvl.L) Pn`, have norm at most `1`** —
generic in `lvl`, and stated against the `Algebra lvl.OL (baseChangeSplittingField …)` instance **ordinary instance search
finds**, which is what `norm_coeff_map_of_isWeaklyEisensteinAt_associated` and both concrete
templates' statements use.

This is deliberately *not* `Level.norm_le_one_of_mem_algebraMap_OL`, which states the same
bound against a composite instance it introduces itself by `letI`: those two instances are defeq at
both concrete depths (that is what its own `rfl` checks show) but **not** generically in `lvl` —
see this file's module docstring for Lean's own report of the mismatch. Proved exactly as
`K_2.norm_le_one_of_mem_O_K1`/`K_3.norm_le_one_of_mem_O_K2` are: split the map through `lvl.L` by
`IsScalarTower.algebraMap_apply`, then `spectralNorm_extends` for the field hop and
`norm_le_one_of_mem_integralClosure` for the integral-closure hop. -/
theorem Level.norm_le_one_of_mem_OL_next (lvl : Level K) (Pn : lvl.OL[X])
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖) (c : lvl.OL) :
    ‖algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) c‖ ≤ 1 := by
  letI := lvl.algL
  letI := lvl.finiteDim
  have heq : algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) c =
      algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) (algebraMap lvl.OL lvl.L c) :=
    IsScalarTower.algebraMap_apply _ _ _ c
  rw [baseChangeSplittingField.norm_eq_spectralNorm, heq, spectralNorm_extends]
  exact norm_le_one_of_mem_integralClosure hnormL c

/-! ## A root of `Pn`'s image lies in the open unit ball -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K] in
/-- **A root of `Pn`'s image (via the `lvl.L` polynomial route) lies in the open unit ball of
`baseChangeSplittingField (K' := lvl.L) Pn`** — the `Level`-generic `norm_lt_one_of_aeval_P₂_eq_zero`/
`norm_lt_one_of_aeval_P₃_eq_zero`, with the same argument both use: `Langlands.EisensteinRootNorm`'s
ultrametric-only Eisenstein-polygon computation (no irreducibility over a base field needed), fed the
norm data `norm_coeff_map_of_isWeaklyEisensteinAt_associated` produces from `Pn`'s `lvl.OL`-level
Eisenstein data. `hα'norm` is carried as an explicit hypothesis, matching the convention used
at every tower level in this development. -/
theorem Level.norm_lt_one_of_root (lvl : Level K) [IsDomain lvl.OL]
    [IsDiscreteValuationRing lvl.OL] (Pn : lvl.OL[X])
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {α' : lvl.OL} (hα'irr : Irreducible α')
    (hPdist : Pn.IsDistinguishedAt (maximalIdeal lvl.OL))
    (hassoc : Associated (Pn.coeff 0) α') (hdeg : 0 < Pn.natDegree)
    (hα'norm : ‖algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) α'‖ < 1)
    {x : baseChangeSplittingField (K' := lvl.L) Pn}
    (hroot : Polynomial.aeval x (Pn.map (algebraMap lvl.OL lvl.L)) = 0) : ‖x‖ < 1 := by
  letI := lvl.algL
  haveI := lvl.faithfulSMul_OL Pn
  have hstep : Polynomial.aeval x Pn = 0 := by
    rw [aeval_map_eq_eval_coe] at hroot
    rwa [eval_coe_eq_aeval] at hroot
  obtain ⟨hmonic, hdegeq, hc0, -, hweak⟩ :=
    norm_coeff_map_of_isWeaklyEisensteinAt_associated (K := baseChangeSplittingField (K' := lvl.L) Pn)
      (lvl.norm_le_one_of_mem_OL_next Pn hnormL) hα'irr
      hPdist.monic hPdist.toIsWeaklyEisensteinAt hassoc
  exact Polynomial.norm_lt_one_of_isEisensteinShape_of_root hmonic (by rw [hdegeq]; exact hdeg)
    hα'norm hc0 hweak
    (by rw [Polynomial.aeval_def, ← Polynomial.eval_map] at hstep; exact hstep)

/-! ## The connecting identity -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [IsFractionRing O K] in
/-- **The connecting identity, generic in `lvl : Level K`**: for `x` a root of `Pn`'s image,
`eval f x` equals the level's generator `α'`, algebra-mapped into `baseChangeSplittingField (K' := lvl.L) Pn` — an equation
about the power-series `eval`, taken directly against the original base `O` (via `Level.instAlgebraO`).

Stated in the `K_2 → K_3` template's shape (conclusion in terms of the ring-of-integers-valued
generator directly), which is the mathematically general one; the `K_1 → K_2` template's extra
`hα'coe : (α' : K_1 P) = α` step is inessential scaffolding and re-enters only at that instantiation
(see below, and this file's module docstring).

Chains the Weierstrass factorization `shifted f (lvl.towerHom hOK) α' = (Pn : _⟦X⟧) * u` through
`eval` (`eval_mul`/`eval_sub`/`eval_C`, with `Level.norm_lt_one_of_root` discharging their `‖x‖ < 1`
hypothesis and `Level.norm_le_one_of_mem_OL_next` their coefficient-bound hypotheses), then
`Level.eval_map_towerHom` to land on `eval f x` itself. -/
theorem Level.eval_f_eq_of_root (lvl : Level K) [IsDomain lvl.OL]
    [IsDiscreteValuationRing lvl.OL] (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {f : O⟦X⟧} {α' : lvl.OL} {u : lvl.OL⟦X⟧} (_hu : IsUnit u)
    (heq : shifted f (lvl.towerHom hOK) α' = (Pn : lvl.OL⟦X⟧) * u)
    (hα'irr : Irreducible α') (hPdist : Pn.IsDistinguishedAt (maximalIdeal lvl.OL))
    (hassoc : Associated (Pn.coeff 0) α') (hdeg : 0 < Pn.natDegree)
    (hα'norm : ‖algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) α'‖ < 1)
    {x : baseChangeSplittingField (K' := lvl.L) Pn}
    (hroot : Polynomial.aeval x (Pn.map (algebraMap lvl.OL lvl.L)) = 0) :
    letI := lvl.instAlgebraO Pn hOK
    NonarchimedeanPowerSeriesEval.eval f x = algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) α' := by
  letI := lvl.algL
  letI := lvl.instAlgebraO Pn hOK
  have hxnorm : ‖x‖ < 1 :=
    lvl.norm_lt_one_of_root Pn hnormL hα'irr hPdist hassoc hdeg hα'norm hroot
  have hstep0 : NonarchimedeanPowerSeriesEval.eval (↑Pn : PowerSeries lvl.OL) x = 0 := by
    rw [← aeval_map_eq_eval_coe (K' := lvl.L)]; exact hroot
  have hb : ∀ (g : PowerSeries lvl.OL) (n : ℕ),
      ‖algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) (PowerSeries.coeff n g)‖ ≤ 1 :=
    fun _ _ => lvl.norm_le_one_of_mem_OL_next Pn hnormL _
  have hshifted0 :
      NonarchimedeanPowerSeriesEval.eval (shifted f (lvl.towerHom hOK) α') x = 0 := by
    rw [heq, NonarchimedeanPowerSeriesEval.eval_mul (hb _) (hb _) hxnorm, hstep0, zero_mul]
  have hsub : NonarchimedeanPowerSeriesEval.eval (PowerSeries.map (lvl.towerHom hOK) f) x -
      NonarchimedeanPowerSeriesEval.eval (PowerSeries.C α' : PowerSeries lvl.OL) x = 0 := by
    rw [← NonarchimedeanPowerSeriesEval.eval_sub (hb _) (hb _) hxnorm]
    exact hshifted0
  rw [NonarchimedeanPowerSeriesEval.eval_C] at hsub
  have hmapeq := sub_eq_zero.mp hsub
  rwa [lvl.eval_map_towerHom Pn hOK x] at hmapeq

/-! ## The next `Level`, one hop up -/

/-- **The next `Level`**: `L := baseChangeSplittingField (K' := lvl.L) Pn`, with `instAlgebraK_of_Level` as its
stored `algL` and finite-dimensionality over `K` by `FiniteDimensional.trans` through `lvl.L` (the
`IsScalarTower K lvl.L (baseChangeSplittingField …)` it needs is exactly `algebraMap_K_eq_of_Level`, fed to
`IsScalarTower.of_algebraMap_eq`).

`(level_K_1).next P₂ = level_K_2 P₂` holds **by `rfl`** (checked below): the concrete depth-2 `Level`
value built by hand is literally this generic successor of the depth-1 one, not merely an
equivalent restatement. -/
@[reducible] def Level.next (lvl : Level K) (Pn : lvl.OL[X]) : Level K where
  L := baseChangeSplittingField (K' := lvl.L) Pn
  algL := instAlgebraK_of_Level lvl Pn
  finiteDim := by
    letI := lvl.algL
    letI := lvl.finiteDim
    letI := instAlgebraK_of_Level lvl Pn
    haveI : IsScalarTower K lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrFun (algebraMap_K_eq_of_Level lvl Pn) x)
    exact FiniteDimensional.trans K lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)

/-! ## Bundled step data -/

/-- **Bundled tower-step data**: a `Level`, plus exactly what the connecting identity needs beyond it
— the generator, the next level's Eisenstein polynomial with its distinguished/`Associated`/degree
data, the Weierstrass unit and factorization, and the two norm facts.

Kept separate from `Level` rather than folded into it because `Level K` is parametrized by `K` alone
while this data depends on `O`, `f` and `hOK` (see the module docstring). The two instance-implicit
fields are needed to state `shifted`/`maximalIdeal lvl.OL` at all and are not derivable generically;
they are deliberately not promoted to global instances, matching `algL`'s own treatment. -/
structure TowerStep (f : O⟦X⟧) (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) where
  /-- The level this step starts from. -/
  lvl : Level.{_, v} K
  /-- `K`'s norm extends exactly to `lvl.L`. -/
  hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖
  [instDomain : IsDomain lvl.OL]
  [instDVR : IsDiscreteValuationRing lvl.OL]
  /-- The level's generator, inside `lvl.OL`. -/
  gen : lvl.OL
  /-- The generator is irreducible in `lvl.OL`. -/
  genIrr : Irreducible gen
  /-- The next level's Eisenstein polynomial. -/
  nextPoly : lvl.OL[X]
  /-- `nextPoly` is distinguished at `lvl.OL`'s maximal ideal. -/
  nextDist : nextPoly.IsDistinguishedAt (maximalIdeal lvl.OL)
  /-- `nextPoly`'s constant term is associated to the generator. -/
  nextAssoc : Associated (nextPoly.coeff 0) gen
  /-- `nextPoly` is not constant. -/
  nextDegPos : 0 < nextPoly.natDegree
  /-- The Weierstrass unit. -/
  unit : lvl.OL⟦X⟧
  /-- …which really is a unit. -/
  unitIsUnit : IsUnit unit
  /-- The Weierstrass factorization of the shifted Lubin-Tate series. -/
  weierstrass : shifted f (lvl.towerHom hOK) gen = (nextPoly : lvl.OL⟦X⟧) * unit
  /-- The generator lies in the next field's open unit ball. -/
  genNormLt : ‖algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) nextPoly) gen‖ < 1

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [IsFractionRing O K] in
/-- **The connecting identity against the bundled step data** — `Level.eval_f_eq_of_root` with every
hypothesis read off `st`'s fields. -/
theorem TowerStep.eval_f_eq_of_root {f : O⟦X⟧} {hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1}
    (st : TowerStep f hOK) {x : baseChangeSplittingField (K' := st.lvl.L) st.nextPoly}
    (hroot : Polynomial.aeval x (st.nextPoly.map (algebraMap st.lvl.OL st.lvl.L)) = 0) :
    letI := st.lvl.instAlgebraO st.nextPoly hOK
    NonarchimedeanPowerSeriesEval.eval f x =
      algebraMap st.lvl.OL (baseChangeSplittingField (K' := st.lvl.L) st.nextPoly) st.gen := by
  letI := st.instDomain
  letI := st.instDVR
  exact st.lvl.eval_f_eq_of_root st.nextPoly hOK st.hnormL st.unitIsUnit st.weierstrass st.genIrr
    st.nextDist st.nextAssoc st.nextDegPos st.genNormLt hroot

/-! ## The generic pieces really are the concrete ones -/

variable {P : O[X]}

/-- `Level.towerHom` at `level_K_1` is literally `towerHom hOK P`. -/
example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    (level_K_1 (K := K) (P := P)).towerHom hOK = towerHom (K := K) hOK P := rfl

variable (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X])

/-- `Level.towerHom` at `level_K_2` is literally `towerHom2 P₂ hOK`. -/
example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    (level_K_2 (K := K) (P := P) P₂).towerHom hOK = towerHom2 (K := K) (P := P) P₂ hOK := rfl

/-- `Level.instAlgebraO` at `level_K_1` is literally `K_2.instAlgebraO`. -/
example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    (level_K_1 (K := K) (P := P)).instAlgebraO P₂ hOK =
      K_2.instAlgebraO (K := K) (P := P) P₂ hOK := rfl

variable (P₃ : (O_K2 (K := K) P₂)[X])

/-- `Level.instAlgebraO` at `level_K_2` is literally `K_3.instAlgebraO`. -/
example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    (level_K_2 (K := K) (P := P) P₂).instAlgebraO P₃ hOK =
      K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK := rfl

/-- **`level_K_2` is literally `(level_K_1).next P₂`** — the depth-2 `Level` value built by
hand is the generic successor of the depth-1 one, not merely an equivalent restatement. -/
example : (level_K_1 (K := K) (P := P)).next P₂ = level_K_2 (K := K) (P := P) P₂ := rfl

/-! ## Concrete check 1: `level_K_1` recovers `eval_f_eq_of_aeval_P₂_eq_zero` exactly -/

/-- **`eval_f_eq_of_aeval_P₂_eq_zero`'s statement, re-derived from the bundled generic theorem** at a
`TowerStep` built over `level_K_1` from that theorem's own hypotheses. The final
`IsScalarTower.algebraMap_apply` rewrite along `hα'coe` is the one inessential step separating the
`K_1 → K_2` template from the general shape (module docstring). -/
theorem eval_f_eq_of_aeval_P₂_eq_zero_of_TowerStep (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {f : O⟦X⟧}
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}
    (_hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    NonarchimedeanPowerSeriesEval.eval f β =
      algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) α := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  have h := TowerStep.eval_f_eq_of_root (f := f) (hOK := hOK)
    { lvl := level_K_1 (K := K) (P := P), hnormL := hnorm_K_K_1 (K := K) (P := P), gen := α',
      genIrr := hα'irr, nextPoly := P₂, nextDist := hP₂dist, nextAssoc := hassoc,
      nextDegPos := hdeg, unit := u₂, unitIsUnit := _hu₂, weierstrass := heq₂,
      genNormLt := hα'norm } hβroot
  refine h.trans ?_
  rw [← hα'coe]
  exact IsScalarTower.algebraMap_apply _ (K_1 (K := K) P) _ α'

/-- **…and it is literally `eval_f_eq_of_aeval_P₂_eq_zero`**, checked by `rfl` on the fully-applied
terms. -/
example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {f : O⟦X⟧}
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}
    (_hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) :
    eval_f_eq_of_aeval_P₂_eq_zero_of_TowerStep (K := K) (P := P) P₂ hOK _hu₂ heq₂ hα'irr hP₂dist
        hassoc hdeg hα'norm hα'coe hβroot =
      eval_f_eq_of_aeval_P₂_eq_zero (K := K) (P := P) (P₂ := P₂) hOK _hu₂ heq₂ hα'irr hP₂dist
        hassoc hdeg hα'norm hα'coe hβroot := rfl

/-! ## Concrete check 2: `level_K_2` recovers `eval_f_eq_of_aeval_P₃_eq_zero` exactly -/

variable [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]

/-- **`eval_f_eq_of_aeval_P₃_eq_zero`'s statement, re-derived from the bundled generic theorem** at a
`TowerStep` built over `level_K_2` — with no `hα'coe`-style extra step, the generic theorem's
conclusion already being the one this template states. -/
theorem eval_f_eq_of_aeval_P₃_eq_zero_of_TowerStep (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {f : O⟦X⟧} (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (_hu₃ : IsUnit u₃)
    (heq₃ :
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    NonarchimedeanPowerSeriesEval.eval f γ =
      algebraMap (O_K2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        β' :=
  TowerStep.eval_f_eq_of_root (f := f) (hOK := hOK)
    { lvl := level_K_2 (K := K) (P := P) P₂, hnormL := hnorm_K_K_2 (K := K) (P := P) P₂,
      gen := β', genIrr := hβ'irr, nextPoly := P₃, nextDist := hP₃dist, nextAssoc := hassoc,
      nextDegPos := hdeg, unit := u₃, unitIsUnit := _hu₃, weierstrass := heq₃,
      genNormLt := hβ'norm } hγroot

/-- **…and it is literally `eval_f_eq_of_aeval_P₃_eq_zero`**, checked by `rfl` on the fully-applied
terms. -/
example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {f : O⟦X⟧}
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (_hu₃ : IsUnit u₃)
    (heq₃ :
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0) :
    eval_f_eq_of_aeval_P₃_eq_zero_of_TowerStep (K := K) (P := P) P₂ P₃ hOK β' u₃ _hu₃ heq₃ hβ'irr
        hP₃dist hassoc hdeg hβ'norm hγroot =
      eval_f_eq_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ hOK β' u₃ _hu₃ heq₃ hβ'irr hP₃dist
        hassoc hdeg hβ'norm hγroot := rfl

end LubinTate

end
