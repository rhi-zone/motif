/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelExistsCheck

/-!
# The `∀ n` Lubin-Tate tower-step induction, generic over `TowerStep`

`TowerStep f hOK` bundles one hop of a Lubin-Tate tower: a `Level` (a field `L` with ring of
integers `OL`), a uniformizer `gen : OL`, and the data of the *next* level — an Eisenstein
polynomial `nextPoly`, a Weierstrass factorization `shifted f (lvl.towerHom hOK) gen = nextPoly *
unit`, and the side facts needed to build `lvl.next nextPoly`. `TowerStep.exists_next` advances one
such step to the next: given `ts : TowerStep f hOK` and, about the base-changed `ts.nextPoly` inside
its splitting field, an irreducibility witness `hirr`, a root `β` of it (`hβroot`), and a degree
equality `hgen` saying `β` generates that splitting field over `ts.lvl.L` (i.e. `ts.nextPoly` stays
monogenic one level up), it produces a `TowerStep` sitting at `ts.lvl.next ts.nextPoly`. This file
iterates that one step `∀ n` times, taking `hirr`/`β`/`hβroot`/`hgen` as a hypothesis supplied at
every tower point rather than as something derived, and states precisely why folding residue-field
preservation into the same induction would require changing `TowerStep` itself.

## Design decision: propositional, hypothesis-driven induction, not a constructive `def`

`TowerStep.exists_next`'s hypotheses `hirr`/`β`/`hβroot`/`hgen` are not derived from `ts` alone by
anything in this repo: at every existing call site they are supplied by hand, computed for one
specific concrete polynomial at one specific level. No lemma here constructs this data
*generically* — proves, for an arbitrary `TowerStep` at an arbitrary level, that such an irreducible
factor / root / monogenic generator always exists (a "root-count" argument: bounding how a
polynomial's roots and their degrees distribute across the extension, uniformly in `n`) — that is
separate, larger work this file does not attempt. Checked directly against the real proof term
(`TowerStep.exists_next` in `Langlands/LubinTateTowerStepLevelExists.lean`): its proof is an
explicit `refine ⟨{...}, rfl⟩`, not `Classical.choice` — so *given* `hirr`/`β`/`hβroot`/`hgen` at a
level, the step itself is fully constructive. But a genuine `def : ℕ → TowerStep f hOK` would need
this data supplied at *every* level, which is exactly the gap above. Two ways to handle that:

* **(a) A constructive `def`, extracting a witness via `Classical.choose` at each step from some
  externally-supplied total function producing this data for every `TowerStep`.** Rejected: it does
  not remove the gap (that total function still has to be built — proving it exists is the same
  unattempted "root-count" argument, not a formalization choice), and it adds a real cost on top:
  `Classical.choose` does not reduce definitionally even when applied to an explicit witness, so a
  `def` built this way could not be `rfl`-checked against the hand-built `level_K_1`/`level_K_2`
  values the way the concrete checks below rely on.
* **(b) A propositional `∀ n` theorem, taking the needed per-step data as a hypothesis of
  existential (not functional) type: `∀ ts, ∃ hirr β hβroot hgen, …`.** This states the gap honestly
  as an open assumption rather than manufacturing a function to discharge it, and the induction step
  itself stays fully constructive (`obtain` on a hypothesis is not `Classical.choice`) — which is
  what makes the concrete checks below possible by `rfl` at all.

**(b) is what is built here.**

## The `∀ n`-indexed relation

`TowerStep.IsNStepFrom ts₀ st n` is a plain structurally-recursive `Prop`-valued `def` on `n`
(`st = ts₀` at `n = 0`; at `n + 1`, some `n`-step point `st'` with `st.lvl = st'.lvl.next
st'.nextPoly`) rather than an inductive type — the recursive clause is exactly `TowerStep.exists_next`'s
own conclusion shape, so unfolding one layer of `IsNStepFrom` is unfolding one application of that
theorem's output, nothing more. An iterated-`Level` formulation (`K n := lvl₀.L`-then-`.next`
`n` times) was considered and not used: `TowerStep.exists_next`'s conclusion only pins down the
*next* `Level`, not the full next `TowerStep` (the generator/polynomial/unit data is only known to
exist, not which value it takes) — so `Level.next` iterated `n` times over is not literally the `lvl`
field of an `n`-step `TowerStep` without first choosing the intervening `TowerStep`s, which is
exactly what `IsNStepFrom`'s existential does explicitly rather than folding into a function.

## The residue-field piece: why it stays out of this induction

`Level.residueFieldEquiv_next` proves the next level's residue field is unchanged, but it is not a
drop-in replacement for the `hgen` hypothesis used here: reading its signature, it takes `hgen` as
*derived*, not assumed, from `Level.natDegree_minpoly_eq_finrank`, which itself needs (1) a
genuinely level-indexed `Splits` invariant, `(P.divX.map (algebraMap O lvl.L)).Splits` — not a field
of `TowerStep`, and not derivable from `TowerStep`'s own `hirr`/`β`/`hβroot`/`hgen` data; it is only
propagated level-to-level by a separate mechanism, `Level.splits_next` — and (2) the **base-level**
Eisenstein factorization data for `f` itself (`P`, `u`, `heq : f = P * u`, `hPdist`, `hPdeg` over
`O`), fixed once for the whole tower but not carried by any individual `TowerStep` either. Composing
residue-field preservation into the induction here would therefore mean either (i) extending
`TowerStep`'s own structure to also carry the `Splits` invariant (and the base-level Eisenstein
data) and re-deriving `TowerStep.exists_next` to propagate it, or (ii) building a second, parallel
bundled step carrying strictly more data than `TowerStep`, duplicating most of its proof. Both
change what `TowerStep` (or its proof obligations) actually is, rather than being a gap closable by
adding a lemma against the current structure — so it is recorded here as an open structural choice
rather than attempted.

## Main results

* `TowerStep.IsNStepFrom` — the `∀ n`-indexed "`n` tower hops from a fixed base" relation.
* `TowerStep.exists_isNStepFrom` — **the `∀ n` induction**: given the base `π`/`hπ`/`hπnorm`/`hf`
  data (constant throughout the tower, matching `TowerStep.exists_next`'s own binding) and a
  hypothesis `hstep` supplying, for *every* `TowerStep`, existential `hirr`/`β`/`hβroot`/`hgen` data
  (the standing "such data always exists" gap, stated as an assumption rather than discharged),
  `∀ n, ∃ st, IsNStepFrom ts₀ st n`. Proved by `induction n`: the base case is `⟨ts₀, rfl⟩`, the step
  case a single application of `TowerStep.exists_next` fed `hstep`'s witness at the current point.
* Concrete checks at `n = 1` (`level_K_1 → level_K_2`) and `n = 2` (`level_K_1 → level_K_2 →
  level_K_2.next P₃`, the latter using `exists_eisenstein_tower_step_K_3`), showing the real
  hand-built `TowerStep` values genuinely satisfy `IsNStepFrom` — **not** by invoking
  `TowerStep.exists_isNStepFrom` with a literal total hypothesis (building one generically is
  exactly the unattempted work above), but by directly constructing `TowerStep` values the same way
  `TowerStep.exists_next`'s own proof does, at real data, and checking `IsNStepFrom` holds of the
  results by `rfl` where the level-equality itself is `rfl` (`(level_K_1).next P₂ = level_K_2 P₂`,
  and its twice-iterated `.next` counterpart), and by direct construction (not `rfl`) at the one
  place a raw `obtain` against a genuine `∃` (`exists_eisenstein_tower_step_K_3`'s own conclusion) is
  unavoidable — the same shape of `∃`-typed step the underlying Weierstrass-factorization engine
  (`exists_isWeierstrassFactorization_shifted`) always produces.
-/

@[expose] public section

noncomputable section

open scoped Polynomial IntermediateField

namespace LubinTate

open IsLocalRing PowerSeries Polynomial

universe v

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]

/-! ## The `∀ n`-indexed relation -/

/-- **`st` is `n` tower hops up from `ts₀`.** At `n = 0`, `st` literally is `ts₀`. At `n + 1`, some
`n`-step point `st'` exists whose `Level` successor (`Level.next`) is `st.lvl` — exactly
`TowerStep.exists_next`'s own conclusion shape, one layer at a time. -/
def TowerStep.IsNStepFrom {f : O⟦X⟧} {hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1}
    (ts₀ : TowerStep f hOK) : TowerStep f hOK → ℕ → Prop
  | st, 0 => st = ts₀
  | st, n + 1 =>
    ∃ st' : TowerStep f hOK, TowerStep.IsNStepFrom ts₀ st' n ∧ st.lvl = st'.lvl.next st'.nextPoly

/-- **The `∀ n` tower-step induction.** `hstep` states, as an assumption rather than something
derived, that at *every* `TowerStep` the irreducibility/root/monogenicity data
`TowerStep.exists_next` needs does exist (not: that a function computing it is given — see the
module docstring for why that distinction is the whole point). The proof itself is a two-line
`induction n`: the base case is `⟨ts₀, rfl⟩`, the step case is one application of
`TowerStep.exists_next` fed `hstep`'s witness at the current point. -/
theorem TowerStep.exists_isNStepFrom {f : O⟦X⟧} {hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1}
    [CharZero K] {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1)
    (hf : IsLubinTatePoly π (residueCard O) f)
    (hstep : ∀ ts : TowerStep.{v, _, _} f hOK,
      ∃ (hirr : Irreducible (ts.nextPoly.map (algebraMap ts.lvl.OL ts.lvl.L)))
        (β : baseChangeSplittingField (K' := ts.lvl.L) ts.nextPoly)
        (hβroot : Polynomial.aeval β (ts.nextPoly.map (algebraMap ts.lvl.OL ts.lvl.L)) = 0),
        (minpoly ts.lvl.L β).natDegree = Module.finrank ts.lvl.L (baseChangeSplittingField (K' := ts.lvl.L) ts.nextPoly))
    (ts₀ : TowerStep.{v, _, _} f hOK) :
    ∀ n : ℕ, ∃ st : TowerStep.{v, _, _} f hOK, TowerStep.IsNStepFrom ts₀ st n := by
  intro n
  induction n with
  | zero => exact ⟨ts₀, rfl⟩
  | succ n ih =>
    obtain ⟨st, hst⟩ := ih
    obtain ⟨hirr, β, hβroot, hgen⟩ := hstep st
    obtain ⟨st', hst'⟩ := st.exists_next hπ hπnorm hf hirr hβroot hgen
    exact ⟨st', st, hst, hst'⟩

/-! ## Concrete checks: the real `level_K_1`/`level_K_2` `TowerStep` values genuinely witness
`IsNStepFrom` at `n = 1, 2` -/

section ConcreteCheck

variable {P : O[X]}
  (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
  (P₃ : (O_K2 (K := K) P₂)[X])

/-- **The real `TowerStep` at `level_K_1`**, built exactly as `eval_f_eq_of_aeval_P₂_eq_zero_of_TowerStep`
(`Langlands/LubinTateTowerStepLevelConnect.lean:454-458`) builds it, from that theorem's own free
variables. -/
def ts_K1 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {f : O⟦X⟧}
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}
    (hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc₂ : Associated (P₂.coeff 0) α') (hdeg₂ : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1) :
    TowerStep f hOK :=
  { lvl := level_K_1 (K := K) (P := P), hnormL := hnorm_K_K_1 (K := K) (P := P), gen := α',
    genIrr := hα'irr, nextPoly := P₂, nextDist := hP₂dist, nextAssoc := hassoc₂,
    nextDegPos := hdeg₂, unit := u₂, unitIsUnit := hu₂, weierstrass := heq₂, genNormLt := hα'norm }

variable [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]

/-- **The real `TowerStep` at `level_K_2`**, built exactly as
`eval_f_eq_of_aeval_P₃_eq_zero_of_TowerStep` (`Langlands/LubinTateTowerStepLevelConnect.lean:503-507`)
builds it. -/
def ts_K2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {f : O⟦X⟧}
    (β' : O_K2 (K := K) P₂) {u₃ : (O_K2 (K := K) P₂)⟦X⟧} (hu₃ : IsUnit u₃)
    (heq₃ : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc₃ : Associated (P₃.coeff 0) β') (hdeg₃ : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1) :
    TowerStep f hOK :=
  { lvl := level_K_2 (K := K) (P := P) P₂, hnormL := hnorm_K_K_2 (K := K) (P := P) P₂,
    gen := β', genIrr := hβ'irr, nextPoly := P₃, nextDist := hP₃dist, nextAssoc := hassoc₃,
    nextDegPos := hdeg₃, unit := u₃, unitIsUnit := hu₃, weierstrass := heq₃, genNormLt := hβ'norm }

/-- **`n = 1`: `ts_K2` is one tower hop from `ts_K1`.** Holds by exhibiting `ts_K1` itself as the
`n = 0` point and `rfl` for the level equation — `level_K_2 P₂ = (level_K_1).next P₂` is exactly
the same checked identity used above, in the other direction. -/
theorem isNStepFrom_ts_K2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {f : O⟦X⟧}
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}
    (hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc₂ : Associated (P₂.coeff 0) α') (hdeg₂ : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    (β' : O_K2 (K := K) P₂) {u₃ : (O_K2 (K := K) P₂)⟦X⟧} (hu₃ : IsUnit u₃)
    (heq₃ : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc₃ : Associated (P₃.coeff 0) β') (hdeg₃ : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1) :
    TowerStep.IsNStepFrom (ts_K1 (K := K) (P := P) P₂ hOK hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂
        hα'norm)
      (ts_K2 (K := K) (P := P) P₂ P₃ hOK β' hu₃ heq₃ hβ'irr hP₃dist hassoc₃ hdeg₃ hβ'norm) 1 :=
  ⟨ts_K1 (K := K) (P := P) P₂ hOK hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm, rfl, rfl⟩

/-! ### `n = 2`: reaching one hop past `level_K_2`, using `exists_eisenstein_tower_step_K_3` -/

/-- **`n = 2`: a real `TowerStep` at `(level_K_2 P₂).next P₃` is two tower hops from `ts_K1`.**
`exists_eisenstein_tower_step_K_3`'s own conclusion is an `∃` (inherited from the underlying
Weierstrass-factorization engine — this is not a new source of opacity,
it is the same shape of `∃`-typed step this repo's engine has always produced), so unlike the `n = 1`
check this one genuinely uses `obtain` rather than closing entirely by `rfl` — recorded precisely, not
elided: the level-equality half (`ts_K3.lvl = ts_K2.lvl.next ts_K2.nextPoly`) is still `rfl`, since
`ts_K3` is built directly from the `obtain`ed witness by the same literal construction `TowerStep.
exists_next`'s own proof uses; what is *not* `rfl`-checked is the existence of that witness itself. -/
theorem isNStepFrom_ts_K3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}
    (hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc₂ : Associated (P₂.coeff 0) α') (hdeg₂ : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    (β' : O_K2 (K := K) P₂) {u₃ : (O_K2 (K := K) P₂)⟦X⟧} (hu₃ : IsUnit u₃)
    (heq₃ : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc₃ : Associated (P₃.coeff 0) β') (hdeg₃ : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0)
    (hγfin : Module.finrank (K2P2 (K := K) P₂) (K2P2 (K := K) P₂)⟮γ⟯ = residueCard O)
    [Algebra.IsSeparable (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
      (K' := K2P2 (K := K) P₂) P₃)] [CharZero K] :
    ∃ st3 : TowerStep f hOK, st3.lvl = (level_K_2 (K := K) (P := P) P₂).next P₃ ∧
      TowerStep.IsNStepFrom (ts_K1 (K := K) (P := P) P₂ hOK hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂
          hα'norm)
        st3 2 := by
  obtain ⟨P₄, u₄, gen, hu₄, hP₄dist, hP₄deg, hgenirr, heq₄, hassoc₄, hnormlt⟩ :=
    exists_eisenstein_tower_step_K_3 (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg
      β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc₃ hdeg₃ hβ'norm hγroot hγfin
  refine ⟨{ lvl := (level_K_2 (K := K) (P := P) P₂).next P₃
            hnormL := hnorm_K_of_Level (level_K_2 (K := K) (P := P) P₂) P₃
              (hnorm_K_K_2 (K := K) (P := P) P₂)
            instDomain := ((level_K_2 (K := K) (P := P) P₂).next P₃).isDomain_OL
            instDVR := ((level_K_2 (K := K) (P := P) P₂).next P₃).isDiscreteValuationRing_OL
            gen := gen, genIrr := hgenirr, nextPoly := P₄, nextDist := hP₄dist
            nextAssoc := hassoc₄
            nextDegPos := by rw [hP₄deg]; exact lt_of_lt_of_le two_pos two_le_residueCard
            unit := u₄, unitIsUnit := hu₄, weierstrass := heq₄, genNormLt := hnormlt }, rfl,
    ts_K2 (K := K) (P := P) P₂ P₃ hOK β' hu₃ heq₃ hβ'irr hP₃dist hassoc₃ hdeg₃ hβ'norm,
    isNStepFrom_ts_K2 (K := K) (P := P) P₂ P₃ hOK hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm β'
      hu₃ heq₃ hβ'irr hP₃dist hassoc₃ hdeg₃ hβ'norm,
    rfl⟩

end ConcreteCheck

end LubinTate

end
