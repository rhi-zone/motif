import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite Cauchy products in a nonarchimedean ring: `HasSum` of an `n`-th power

`Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean`'s `HasSum.mul_of_nonarchimedean` gives the
binary Cauchy product for free in a `NonarchimedeanRing`: if `HasSum f a` and `HasSum g b`, then
`fun i : α × β ↦ f i.1 * g i.2` sums to `a * b`, with **no** separate summability hypothesis on the
product family (unlike the archimedean `HasSum.mul`, which needs
`Summable (fun p ↦ f p.1 * g p.2)` supplied separately).

This file iterates that binary product `n` times to get the `n`-ary Cauchy product: if `HasSum f a`,
then the function sending each length-`n` tuple `g : Fin n → ι` to the product
`∏ i, f (g i)` sums to `a ^ n` (`HasSum.pow_of_nonarchimedean`). This is exactly the "expand `y ^ n` as
an infinite sum over multi-indices" step needed to evaluate a composite convergent power series
`∑ n, c n * y ^ n` (with `y` itself an infinite sum `∑ k, f k`) as a single sum indexed by tuples,
en route to the wild-ramification thread's `exp`/`log` mutual-inverse identity (see `ROADMAP.md`, the
tenth pass on that thread) — matching this tuple-indexed sum against the formal coefficients of
`PowerSeries.subst` (`Mathlib.RingTheory.PowerSeries.Substitution`'s `coeff_subst'`, a *finite* `finsum`
over compositions) is the remaining, unattempted assembly step.

## Proof

Induction on `n`. The base case `n = 0` is `Fin 0 → ι`, a one-point type (the empty function), on which
the constant function `1` trivially sums to `1 = a ^ 0` (`hasSum_fintype`). For the successor step,
`hf.mul_of_nonarchimedean (hf.pow_of_nonarchimedean n)` gives `HasSum` on the product type
`ι × (Fin n → ι)`; transporting along `Fin.consEquiv`'s inverse (`Equiv.hasSum_iff`, which needs no
extra hypotheses since it merely reindexes along a bijection) turns this into `HasSum` on
`Fin (n + 1) → ι`, and `Fin.consEquiv_symm_apply`/`Fin.prod_univ_succ` identify the reindexed function
with `fun g ↦ ∏ i, f (g i)`.
-/

@[expose] public section

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanRing R]
variable {ι : Type*} {f : ι → R} {a : R}

/-- **The `n`-ary Cauchy product in a nonarchimedean ring.** If `f` sums to `a`, then the function
sending each length-`n` tuple `g : Fin n → ι` to `∏ i, f (g i)` sums to `a ^ n` — with no separate
summability hypothesis on the tuple-indexed family, courtesy of `HasSum.mul_of_nonarchimedean`. -/
theorem HasSum.pow_of_nonarchimedean (hf : HasSum f a) :
    ∀ n : ℕ, HasSum (fun g : Fin n → ι => ∏ i, f (g i)) (a ^ n)
  | 0 => by simpa using hasSum_fintype (fun _ : Fin 0 → ι => (1 : R))
  | n + 1 => by
      have h := hf.mul_of_nonarchimedean (hf.pow_of_nonarchimedean n)
      have h2 := (Equiv.hasSum_iff (Fin.consEquiv (fun _ => ι)).symm).mpr h
      have hfun : (fun p : ι × (Fin n → ι) => f p.1 * ∏ i, f (p.2 i)) ∘
            ⇑(Fin.consEquiv (fun _ => ι)).symm
          = fun g : Fin (n + 1) → ι => ∏ i, f (g i) := by
        funext g
        simp [Function.comp_apply, Fin.consEquiv_symm_apply, Fin.prod_univ_succ, Fin.tail]
      rw [hfun] at h2
      rwa [pow_succ']
