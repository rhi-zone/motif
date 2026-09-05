import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# The shared "confine to a finite box" step of the eval-subst family

Five files in this repo (`Langlands.NonarchimedeanPowerSeriesEvalSubst`,
`...EvalSubstMv`, `...MvPowerSeriesEvalSubstDiagonal`, `...MvPowerSeriesEvalSubstGeneral`,
`...PowerSeriesEvalSubstMvIn`) each prove `eval`/`subst` compatibility via a double-series
interchange on a term family `T : ι × κ → K` (`ι`/`κ` being `ℕ` or `τ →₀ ℕ`/`σ →₀ ℕ` depending on
the file), and each independently re-derives the same "`T` tends to `0` along `cofinite`" fact from
the same two ingredients: a uniform norm bound depending only on the second coordinate's "degree",
and *exact* vanishing whenever that degree falls short of the first coordinate's "weight". This file
factors that shared argument out once, generically over the index types and the weight/degree
functions, so each of the five files' `tendsto_T_cofinite_zero_*` becomes a direct application of it
instead of a re-derivation of the finite-box argument.

## Main result

* `tendsto_zero_cofinite_of_degree_bound` : given `wt : ι → ℕ`, `deg : κ → ℕ`, a bound
  `‖T (i, k)‖ ≤ r ^ deg k` (`0 ≤ r < 1`), exact vanishing `T (i, k) = 0` whenever `deg k < wt i`, and
  finiteness of every sublevel set `{i | wt i ≤ D}`/`{k | deg k < D}`, `T` tends to `0` along
  `cofinite` on `ι × κ`.

This is exactly the "uniform bound + exact vanishing below a threshold, confining the non-`ε`-small
set to `{i | wt i ≤ D} ×ˢ {k | deg k < D}`" argument each of the five files spelled out by hand; only
the (file-specific) bound and vanishing facts, and instantiating `wt`/`deg` at that file's own index
types, remain file-local.
-/

@[expose] public section

theorem tendsto_zero_cofinite_of_degree_bound {ι κ K : Type*} [SeminormedAddGroup K]
    (T : ι × κ → K) (wt : ι → ℕ) (deg : κ → ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ p : ι × κ, ‖T p‖ ≤ r ^ deg p.2)
    (hvanish : ∀ p : ι × κ, deg p.2 < wt p.1 → T p = 0)
    (hfin_wt : ∀ D : ℕ, {i : ι | wt i ≤ D}.Finite)
    (hfin_deg : ∀ D : ℕ, {k : κ | deg k < D}.Finite) :
    Filter.Tendsto T Filter.cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε hr1
  have hfin : Set.Finite {p : ι × κ | wt p.1 ≤ D ∧ deg p.2 < D} := by
    have heq : {p : ι × κ | wt p.1 ≤ D ∧ deg p.2 < D} =
        {i : ι | wt i ≤ D} ×ˢ {k : κ | deg k < D} := rfl
    rw [heq]
    exact (hfin_wt D).prod (hfin_deg D)
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq, not_lt, dist_zero_right] at hp
  have he : deg p.2 < D := by
    by_contra hge
    push Not at hge
    have := pow_le_pow_of_le_one hr0 hr1.le hge
    linarith [hbound p, hD]
  have hd : wt p.1 ≤ deg p.2 := by
    by_contra hlt
    push Not at hlt
    rw [hvanish p (by omega)] at hp
    simp at hp
    linarith
  exact ⟨by omega, he⟩
