import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# The `m`-th coefficient of `φ ^ n` as a sum over `Fin n → ℕ` tuples

`PowerSeries.coeff_pow` expresses `coeff m (φ ^ n)` as a sum over `Finset.Nat.antidiagonal`-style
data indexed by `Finset.finsuppAntidiag`, a `Finset` of finitely-supported functions `ℕ →₀ ℕ`. This
file restates that formula in the tuple-indexed form `Finset.Nat.antidiagonalTuple n m : Finset (Fin
n → ℕ)` provides — a `Finset` of genuine `Fin n → ℕ` tuples summing to `m` — which is the form needed
to match a convergent, tuple-indexed sum (as built by `HasSum.pow_of_nonarchimedean`,
`Langlands.NonarchimedeanCauchyProduct`) against the formal coefficient of a power. General-purpose,
not tied to any particular series or ring.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommSemiring R]

/-- **The `m`-th coefficient of `φ ^ n` as a sum over tuples summing to `m`.** Restates
`coeff_prod` (applied to the constant family `fun _ : Fin n ↦ φ` over `Finset.univ`) in terms of
`Finset.Nat.antidiagonalTuple n m` (tuples `g : Fin n → ℕ` with `∑ i, g i = m`) rather than
`Finset.finsuppAntidiag`, via the bijection `Finsupp.equivFunOnFinite` between `Fin n →₀ ℕ` and
`Fin n → ℕ` (every function on the finite type `Fin n` is finitely supported). -/
theorem coeff_pow_eq_sum_antidiagonalTuple (n m : ℕ) (φ : R⟦X⟧) :
    coeff m (φ ^ n) = ∑ g ∈ Finset.Nat.antidiagonalTuple n m, ∏ i, coeff (g i) φ := by
  classical
  have hprod := coeff_prod (fun _ : Fin n => φ) m Finset.univ
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  rw [hprod]
  refine Finset.sum_nbij' (fun l => (l : Fin n → ℕ)) (fun g => Finsupp.equivFunOnFinite.symm g)
    ?_ ?_ ?_ ?_ ?_
  · intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl
    rw [Finset.Nat.mem_antidiagonalTuple]
    exact hl.1
  · intro g hg
    rw [Finset.Nat.mem_antidiagonalTuple] at hg
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨hg, Finset.subset_univ _⟩
  · intro l _
    ext i
    simp
  · intro g _
    simp
  · intro l _
    rfl
end PowerSeries
