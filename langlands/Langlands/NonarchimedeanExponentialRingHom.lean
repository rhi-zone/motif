import Langlands.NonarchimedeanExponentialAdd

/-!
# `exp` versus continuous ring homomorphisms and finite sums

Two structural facts about `NonarchimedeanExponential.exp` needed by every route to the wild-case
norm/trace compatibility formula `N_{L/K}(exp x) = exp(Tr_{L/K} x)`:

* a continuous ring homomorphism between nonarchimedean fields commutes with `exp` (so, in
  particular, do the Galois conjugations of a finite extension of complete fields, which are
  automatically continuous by `LinearMap.continuous_of_finiteDimensional`);
* `exp` turns a *finite sum* into a product, which is `exp_add` iterated — the form the
  `N = ∏ σ` / `Tr = ∑ σ` pair actually consumes.

Both are stated for two possibly-different base fields where that costs nothing, since the intended
application has `K = K_v` and `K' = L_w` with genuinely different norms.

## Main results

* `NonarchimedeanExponential.map_exp` : `f (exp x) = exp (f x)` for `f` a continuous ring hom, given
  that `x` and `f x` are in the respective convergence domains.
* `NonarchimedeanExponential.exp_sum` : `exp (∑ i ∈ s, g i) = ∏ i ∈ s, exp (g i)`.
-/

noncomputable section

namespace NonarchimedeanExponential

variable {K K' : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
  [NormedField K'] [IsUltrametricDist K'] [CharZero K'] [CompleteSpace K']
variable {p : ℕ} [hp : Fact p.Prime]

/-- **A continuous ring homomorphism commutes with `exp`.** Both sides are sums of the same series
(`hasSum_exp`), one transported along `f` (`HasSum.map`, using continuity), the other formed
directly at `f x`; the termwise match is `f (xⁿ/n!) = (f x)ⁿ/n!` (`map_div₀`, `map_natCast`). -/
theorem map_exp (hnorm : ‖(p : K)‖ < 1) (hnorm' : ‖(p : K')‖ < 1) (f : K →+* K')
    (hf : Continuous f) {x : K} (hx : ‖x‖ < convergenceRadius K p)
    (hfx : ‖f x‖ < convergenceRadius K' p) :
    f (exp hnorm x) = exp hnorm' (f x) := by
  have h1 : HasSum (fun n : ℕ => f (x ^ n / (n.factorial : K))) (f (exp hnorm x)) :=
    (hasSum_exp hnorm hx).map f hf
  have h2 : (fun n : ℕ => f (x ^ n / (n.factorial : K)))
      = fun n : ℕ => (f x) ^ n / (n.factorial : K') := by
    funext n
    rw [map_div₀, map_pow, map_natCast]
  rw [h2] at h1
  exact h1.unique (hasSum_exp hnorm' hfx)

omit [CompleteSpace K] in
/-- A finite sum of elements of `exp`'s convergence domain is again in the convergence domain: the
ultrametric inequality bounds the sum's norm by the maximum of the summands' norms
(`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`), and the empty sum is `0`. -/
theorem norm_sum_lt_convergenceRadius {ι : Type*} {s : Finset ι} {g : ι → K}
    (hg : ∀ i ∈ s, ‖g i‖ < convergenceRadius K p) :
    ‖∑ i ∈ s, g i‖ < convergenceRadius K p := by
  have hpos : (0 : ℝ) < convergenceRadius K p := Real.rpow_pos_of_pos norm_natCast_pos _
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hpos
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs g
  exact lt_of_le_of_lt hle (hg i hi)

/-- **`exp` turns a finite sum into a product.** `exp_add` iterated over the `Finset`, the induction
staying inside the convergence domain by `norm_sum_lt_convergenceRadius`. -/
theorem exp_sum (hnorm : ‖(p : K)‖ < 1) {ι : Type*} {s : Finset ι} {g : ι → K}
    (hg : ∀ i ∈ s, ‖g i‖ < convergenceRadius K p) :
    exp hnorm (∑ i ∈ s, g i) = ∏ i ∈ s, exp hnorm (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using exp_zero hnorm
  | insert a t ha ih =>
      have hga : ‖g a‖ < convergenceRadius K p := hg a (Finset.mem_insert_self a t)
      have hgt : ∀ i ∈ t, ‖g i‖ < convergenceRadius K p := fun i hi =>
        hg i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        exp_add hnorm hga (norm_sum_lt_convergenceRadius hgt), ih hgt]

end NonarchimedeanExponential

end
