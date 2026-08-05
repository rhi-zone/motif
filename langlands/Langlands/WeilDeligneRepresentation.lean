import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Langlands.WeilGroup

/-!
# Weil–Deligne representations

Let `K` be a nonarchimedean local field with Weil group `W_K` (`LocalField.WeilGroup`,
`Langlands/WeilGroup.lean`). A **Weil–Deligne representation** of `W_K` on a `ℂ`-vector space `V`
is a pair `(ρ, N)` of

* a representation `ρ : Representation ℂ W_K V`, and
* a nilpotent endomorphism `N : V →ₗ[ℂ] V`,

satisfying the intertwining relation `ρ(w) ∘ N ∘ ρ(w)⁻¹ = ‖w‖ • N` for every `w ∈ W_K`, where
`‖w‖ = q ^ n` is the norm character of `W_K`, `q = #𝓀[K]` the residue field cardinality and `n`
the integer such that `toArt K w = ofAdd n` (`LocalField.toArt`, `Langlands/WeilGroup.lean`).

Since `ρ` is a group homomorphism, `ρ(w)⁻¹` is realized as `ρ(w⁻¹)`: `ρ w ∘ₗ ρ w⁻¹ = ρ 1 = id`,
so `ρ w⁻¹` really is the two-sided inverse of `ρ w` as a linear map, without requiring `ρ` to land
in a group of units.

## Main definitions

* `LocalField.weilNormChar K w` : the norm character `‖w‖ = q ^ n` of `w ∈ W_K`, `q = #𝓀[K]` and
  `n` read off through `toArt`.
* `LocalField.WeilDeligneRepresentation K V` : the structure bundling `ρ`, `N`, nilpotence of `N`,
  and the intertwining relation.
* `LocalField.WeilDeligneRepresentation.trivial K V` : the trivial Weil–Deligne representation,
  with `ρ` trivial and `N = 0`.
* `LocalField.WeilDeligneRepresentation.ofRepresentation ρ` : any representation `ρ` of `W_K`,
  paired with `N = 0`, is a Weil–Deligne representation (the intertwining relation is trivially
  satisfied since both sides vanish).

## References
* J. Tate, *Number theoretic background*, §1, in *Automorphic forms, representations, and
  L-functions* (Corvallis proceedings).
-/

open ValuativeRel
open scoped Topology

namespace LocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The **norm character** `‖·‖ : W_K → ℂ`, sending `w` to `q ^ n`, where `q = #𝓀[K]` is the
residue field cardinality and `n : ℤ` is such that `toArt K w = Multiplicative.ofAdd n`. -/
noncomputable def weilNormChar (w : WeilGroup K) : ℂ :=
  (Fintype.card 𝓀[K] : ℂ) ^ (toArt K w).toAdd

@[simp]
theorem weilNormChar_one : weilNormChar K 1 = 1 := by
  simp [weilNormChar]

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- A **Weil–Deligne representation** of `W_K` on the `ℂ`-vector space `V`: a representation
`ρ : Representation ℂ W_K V` together with a nilpotent `N : V →ₗ[ℂ] V` satisfying the
intertwining relation `ρ(w) ∘ N ∘ ρ(w)⁻¹ = ‖w‖ • N`. -/
structure WeilDeligneRepresentation where
  /-- The underlying representation of `W_K`. -/
  ρ : Representation ℂ (WeilGroup K) V
  /-- The monodromy operator. -/
  N : V →ₗ[ℂ] V
  /-- `N` is nilpotent. -/
  isNilpotent_N : IsNilpotent N
  /-- The intertwining relation `ρ(w) N ρ(w)⁻¹ = ‖w‖ N`. -/
  compatible : ∀ w : WeilGroup K, ρ w ∘ₗ N ∘ₗ ρ w⁻¹ = weilNormChar K w • N

namespace WeilDeligneRepresentation

variable {K V}

/-- Any representation `ρ` of `W_K`, paired with monodromy `N = 0`, is a Weil–Deligne
representation: the intertwining relation degenerates to `0 = ‖w‖ • 0`, true for any `ρ`. -/
noncomputable def ofRepresentation (ρ : Representation ℂ (WeilGroup K) V) :
    WeilDeligneRepresentation K V where
  ρ := ρ
  N := 0
  isNilpotent_N := IsNilpotent.zero
  compatible w := by simp

variable (K V)

/-- The trivial Weil–Deligne representation: `ρ` trivial, `N = 0`. -/
noncomputable def trivial : WeilDeligneRepresentation K V :=
  ofRepresentation (Representation.trivial ℂ (WeilGroup K) V)

end WeilDeligneRepresentation

end LocalField
