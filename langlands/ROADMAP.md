# Roadmap: Formalizing the Langlands Program in Lean 4 / Mathlib

Scope: get to the point where the **core Langlands conjectures can be formally
stated** (local and global correspondence, functoriality, Artin's conjecture),
then prove whatever is in reach. Grounded against Mathlib as vendored at
`langlands/.lake/packages/mathlib` (tagged for Lean toolchain in this project,
"v4.32.1" per the task brief). All claims below are backed by `find`/`grep`
against that source tree, not memory — file paths are cited so they can be
re-checked.

---

## 1. What Mathlib already has

### 1.1 Algebraic number theory (number fields, rings of integers, completions, valuations)

**Strong.** `Mathlib/NumberTheory/NumberField/` is a large, actively developed
directory:
- `Basic.lean` — `NumberField` class, ring of integers `𝓞 K`.
- `InfinitePlace/{Basic,Embeddings,Ramification,TotallyRealComplex}.lean`,
  `InfinitePlace/Completion.lean` — archimedean places and their completions.
- `Completion/{FinitePlace,InfinitePlace,LiesOverInstances,Ramification}.lean`
  — completions at all places, uniform treatment.
- `FinitePlaces.lean`, `RamificationInertia.lean` (in `NumberTheory/`) —
  non-archimedean places, ramification/inertia degrees.
- `Ideal/{Basic,Asymptotics,KummerDedekind}.lean` — ideal theory,
  Kummer–Dedekind.
- `Discriminant/{Defs,Basic,Different}.lean`, `ClassNumber.lean`,
  `Units/{Basic,Regulator,DirichletTheorem}.lean` — discriminant, class group,
  unit group, Dirichlet's unit theorem.
- `CanonicalEmbedding/*`, `FractionalIdeal.lean`, `Norm.lean`,
  `ProductFormula.lean`, `CMField.lean`, `Cyclotomic/*`, `DedekindZeta.lean`.
- Valuations: `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` (used by
  the finite adèle ring), `Mathlib/RingTheory/Valuation/Discrete/Basic.lean`.
- `Mathlib/RingTheory/Frobenius.lean` (2025, Andrew Yang) — **arithmetic
  Frobenius elements** for a finite Galois extension, built on
  `Mathlib/RingTheory/Invariant/{Basic,Profinite}.lean`. This is a genuinely
  load-bearing result for Langlands (Frobenius conjugacy classes are exactly
  what a Galois representation is decorated with).

**Missing:** no notion of "Frobenius element well-defined up to conjugacy as a
function of the Galois representation", no Chebotarev density statement tying
Frobenius distribution to L-functions.

### 1.2 p-adic numbers and local fields

**Partial.** `Mathlib/NumberTheory/Padics/` has `PadicNumbers.lean`,
`PadicIntegers.lean`, `PadicNorm.lean`, `Hensel.lean`, `ProperSpace.lean`,
`ValuativeRel.lean`, `WithVal.lean`, `RingHoms.lean`, `HeightOneSpectrum.lean`,
`Complex.lean` (ℂ_p), `Measure/{Basic,Topology}.lean` (Haar measure on ℚ_p /
ℤ_p already exists via general Haar-measure machinery), `AddChar.lean`
(additive characters of ℚ_p — directly useful for Tate's thesis / local
L-factors).

`Mathlib/NumberTheory/LocalField/Basic.lean` exists but is thin (one file) —
general local fields (finite extensions of ℚ_p or 𝔽_q((t))) are not developed
as a first-class abstraction the way number fields are; what's available is
via `NumberField.Completion.FinitePlace`, i.e. completions of number fields
at finite places, rather than a standalone "local field" typeclass hierarchy
with local class field theory attached.

**Missing:** local class field theory (local Artin map), local
Langlands-relevant structure (no smooth/admissible representations of
`GL_n(local field)`, see §1.5).

### 1.3 Adeles and ideles

**Present, additive side only.**
- `Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean` (María Inés de
  Frutos-Fernández) — finite adèle ring of a Dedekind domain as a restricted
  product, built on `Mathlib/Topology/Algebra/RestrictedProduct/*`.
- `Mathlib/NumberTheory/NumberField/InfiniteAdeleRing.lean` — infinite adèle
  ring (product over archimedean completions).
- `Mathlib/NumberTheory/NumberField/AdeleRing.lean` — full adèle ring
  `AdeleRing (𝓞 K) K` = infinite × finite, with `principalSubgroup` (the
  diagonal embedding of `K`).
- Restricted-product infrastructure: `Topology/Algebra/RestrictedProduct/
  {Basic,TopologicalSpace,Units}.lean`, `Topology/Algebra/IsOpenUnits.lean`
  (needed to give the units of a restricted product, i.e. ideles, their
  correct topology).

**Update — built in this project (Phase 0, now complete):** `IdeleGroup` and
`IdeleClassGroup` are defined in `Langlands/IdeleGroup.lean` (this repo, not
upstreamed to Mathlib), with `toClassGroup` and its kernel computed,
sorry-free. This closes the gap noted originally against Mathlib itself
(Mathlib upstream still has no such definition). Also landed this project:
the local norm map at finite places (`Langlands/NormMap.lean`, via
`HeightOneSpectrum`) and at archimedean places (`NumberField.InfinitePlace`),
plus the full idele-group norm map.

**Still missing:** no compactness of `𝔸ₖ/K` or of the norm-one idele class
group; no strong approximation theorem (`grep` for "strong approximation" is
empty); no self-dual Haar measure / Tate's thesis setup beyond the raw
`AddChar` and Haar-measure primitives.

### 1.4 Algebraic groups (linear, reductive, split, ...)

**Essentially absent as a theory.** What exists:
- Concrete classical groups over a ring/field: `Mathlib/LinearAlgebra/
  GeneralLinearGroup/`, `Matrix/GeneralLinearGroup/`, `SpecialLinearGroup.lean`,
  `Matrix/SpecialLinearGroup.lean`, `Matrix/ProjectiveSpecialLinearGroup.lean`.
  These give `GL_n`, `SL_n`, `PSL_n` as abstract/matrix groups (used already
  by the modular forms library for `SL(2,ℤ)`), but with no group-scheme
  structure, no functor-of-points perspective, no algebraicity/rationality
  theory attached.
- Root systems and Weyl groups exist as **combinatorial/Lie-theoretic**
  objects: `Mathlib/LinearAlgebra/RootSystem/{Base,Hom,WeylGroup,
  Finite/CanonicalBilinear,Finite/Nondegenerate,GeckConstruction/Basic}.lean`,
  `Mathlib/Algebra/Lie/Weights/RootSystem.lean`. This is exactly the
  combinatorial data (root datum) that classifies split reductive groups —
  genuinely reusable — but there is no bridge from "abstract root system" to
  "reductive group scheme with that root datum."
- Group schemes: `grep` for "group scheme" only turns up
  `Mathlib/AlgebraicGeometry/Group/{Abelian,Smooth}.lean` (about group objects
  in the category of schemes generically, e.g. abelian varieties/smooth
  group schemes) and `Mathlib/RingTheory/HopfAlgebra/MonoidAlgebra.lean`. No
  torus, no notion of split/quasi-split/reductive/semisimple group scheme, no
  Chevalley classification, no dual group (Langlands dual) construction.
- `Mathlib/Algebra/BrauerGroup/{Defs,...}` exists (relevant to inner forms of
  reductive groups and to local class field theory via `H^2`, but not
  connected to anything algebraic-group-shaped yet).

**This is the single largest gap for Langlands.** Even *stating* "let G be a
split reductive group over a number field, ^L G its Langlands dual" requires
a theory of reductive groups that does not exist in Mathlib today. The
closest reusable ingredient is the root-system/Weyl-group library plus the
raw matrix groups `GL_n`/`SL_n` for the archetypal case.

### 1.5 Representation theory (finite groups, topological groups, p-adic groups)

**Good for finite/general abstract groups, essentially absent for the
smooth/admissible p-adic representation theory Langlands actually needs.**
- `Mathlib/RepresentationTheory/` is rich: `Basic.lean`, `Character.lean`,
  `FDRep.lean`, `Rep/{Basic,Iso,Res}.lean`, `Semisimple.lean`,
  `Irreducible.lean`, `Induced.lean`, `Coinduced.lean`, `Intertwining.lean`,
  `Maschke.lean`, `Tannaka.lean`, `AlgebraRepresentation/Basic.lean`.
- `Mathlib/RepresentationTheory/Continuous/{Basic,TopRep}.lean` — continuous
  representations of topological groups exist as a category (`TopRep`). This
  is a real foothold: admissible/smooth representations of `GL_n(ℚ_p)` are a
  further specialization (locally constant vectors under compact open
  subgroups) that is not yet formalized but has a plausible landing spot.
- `Mathlib/RepresentationTheory/Homological/` — group cohomology
  (`GroupCohomology/{Basic,Functoriality,Shapiro,Hilbert90,
  LongExactSequence,LowDegree,FiniteCyclic}.lean`), group homology, **Tate
  cohomology** (`TateCohomology/Basic.lean`), and **continuous cohomology**
  (`ContCohomology/{Basic,LowDegree,Functoriality}.lean`) for profinite/
  topological-group coefficients. `Hilbert90.lean` is present and is a
  genuine class-field-theory-adjacent result already proved.

**Missing:** no smooth representations, no admissible representations, no
Jacquet modules, no parabolic induction, no supercuspidal
representations/support, no Bernstein decomposition — i.e. none of the
representation-theoretic vocabulary the local Langlands correspondence is
stated in.

### 1.6 Automorphic forms

**Absent for the general notion; present only for the classical GL_2/SL_2(ℤ)
special case under a different name (modular forms).** `grep -rli
"automorphic"` across all of Mathlib returns only incidental hits
(`Algebra/Quandle.lean`, `NumberTheory/HeckeRing/Defs.lean` use the word
informally, not as a defined concept). What *does* exist and is directly
reusable as the motivating example:
- `Mathlib/NumberTheory/ModularForms/` — a substantial library: `Basic.lean`,
  `SlashActions.lean`, `SlashInvariantForms.lean`, `CongruenceSubgroups.lean`,
  `ArithmeticSubgroups.lean`, `Cusps.lean`, `BoundedAtCusp.lean`,
  `QExpansion.lean`, `CuspFormSubmodule.lean`, `Petersson.lean` (inner
  product), `EisensteinSeries/*` (a full sub-library), `LevelOne/*`
  (dimension formulas), `JacobiTheta/*`, `Delta.lean`, `DedekindEta.lean`.
- `Mathlib/NumberTheory/HeckeRing/Defs.lean` — an abstract Hecke ring, but
  this is the double-coset-algebra formalism, not Hecke *operators* acting on
  a specific space of modular forms with eigenform theory attached (`grep`
  for Hecke-operator-specific names like `HeckeOperator`/`T_p` found nothing
  relevant).

**Missing:** automorphic forms/representations for a general reductive group
`G(𝔸_K)`, cusp forms in that generality, Hecke operators as an algebra acting
on automorphic forms (only the abstract ring, not the action), Satake
isomorphism, Langlands' automorphic representation ↔ classical modular form
dictionary (the modular-forms library never leaves the classical, concrete
`SL(2,ℤ)` picture).

### 1.7 L-functions (Dirichlet, Hecke, Artin, automorphic)

**Strong for Dirichlet/Riemann zeta, absent for Hecke/Artin/automorphic.**
`Mathlib/NumberTheory/LSeries/` is large: `Basic.lean`, `Convergence.lean`,
`Linearity.lean`, `Convolution.lean`, `Dirichlet.lean`,
`DirichletContinuation.lean`, `RiemannZeta.lean`, `ZetaZeros.lean`,
`HurwitzZeta{Even,Odd,Values}.lean`, `AbstractFuncEq.lean` (an abstract
functional-equation framework — potentially reusable scaffolding for other
L-functions), `Nonvanishing.lean`, `Positivity.lean`, `PrimesInAP.lean`,
`MellinEqDirichlet.lean`, `SumCoeff.lean`, `Deriv.lean`, `Injectivity.lean`,
`ZMod.lean`. Plus `Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
(Dedekind zeta function of a number field) and
`Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean`.

**Missing:** Hecke L-functions (of a Hecke character on the idele class
group — blocked on §1.3's missing idele class group), Artin L-functions (of
a Galois representation — blocked on §1.8), automorphic L-functions (blocked
on §1.6). The `AbstractFuncEq.lean` framework is the most promising reusable
piece: it's plausible Artin/automorphic L-functions could eventually plug
into it once their Euler products/coefficients are defined.

### 1.8 Galois representations

**Absent as a defined concept.** `grep -rli "galois representation"` finds
nothing; the closest hit, `CategoryTheory/Galois/Decomposition.lean`, is
about Grothendieck's categorical Galois theory (fiber functors, decomposition
groups for the category-theoretic Galois formalism), not about
`ρ : Gal(K̄/K) → GL_n(F)`. Ingredients that *are* present and directly
prerequisite:
- `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean` — the absolute Galois group
  itself.
- `Mathlib/FieldTheory/Galois/Profinite.lean`,
  `Mathlib/Topology/Algebra/Category/ProfiniteGrp/`,
  `Mathlib/Topology/Category/{Profinite,LightProfinite}/` — profinite-group
  category theory, needed since Galois groups are profinite and a
  representation must be continuous.
- `Mathlib/CategoryTheory/Galois/*` (`Basic`, `Action`, `Equivalence`,
  `EssSurj`, `Full`, `GaloisObjects`, `IsFundamentalgroup`,
  `Prorepresentability`, `Topology`) — Grothendieck's Galois theory, giving
  an abstract fiber-functor formalism that generalizes the classical
  Gal(L/K)-action; reusable as scaffolding.
- `RingTheory/Frobenius.lean` (§1.1) and `RepresentationTheory/Continuous/*`
  (§1.5) are exactly the two ingredients that would need to be combined:
  continuous representations + Frobenius elements = the statement "a Galois
  representation is unramified at p and sends Frob_p to [specified conjugacy
  class]."

**Missing:** the actual definition
`GaloisRepresentation := ContinuousRepresentation (Gal(K̄/K)) F V` (or
similar), unramifiedness, local Galois representations at each place,
compatible systems of ℓ-adic representations.

**Update — Weil group and Weil–Deligne group both now built in this project
(Phase 1, complete):** `grep` for "weil group"/"WeilGroup" still finds
nothing in Mathlib itself, but this project's own `Langlands/WeilGroup.lean`
fully constructs `W_K` as the preimage of ℤ in ℤ̂ under `toZhatHom`, with the
decomposition subgroup (everything), the inertia subgroup, the arithmetic
Frobenius, and `Gal(k̄/𝓀[K]) ≅ ℤ̂` sending Frobenius to 1. On top of that,
`Langlands/WeilDeligneRepresentation.lean` lands
`LocalField.WeilDeligneRepresentation K V`: a structure bundling a
representation `ρ : Representation ℂ (WeilGroup K) V`, a nilpotent
`N : V →ₗ[ℂ] V`, and the intertwining relation
`ρ w ∘ₗ N ∘ₗ ρ w⁻¹ = weilNormChar K w • N`, plus `ofRepresentation`/`trivial`
constructors — all sorry-free. This closes the hard blocker for local
Langlands and for Artin/Weil L-functions at ramified places.

### 1.9 Class field theory

**Not present as a theorem, but real prerequisite infrastructure exists.**
`grep -rli "class field theory\|artin reciprocity"` turns up nothing on
point. What is present and is a genuine down payment:
- `Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean` —
  Hilbert's Theorem 90, a classical stepping stone to local CFT via
  cohomological methods.
- `Mathlib/Algebra/BrauerGroup/*` — the Brauer group, which is where local
  CFT's `H²(Gal(L/K), L^×) ≅ ℚ/ℤ` statement lives.
- `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`.
- `RingTheory/Frobenius.lean` (Frobenius elements, §1.1) is precisely the
  input to the (global) Artin map on unramified primes.

**Missing:** the Artin reciprocity map itself
(`Idele class group → Gal(K^ab/K)`), local reciprocity, the existence
theorem, everything tying Brauer-group `H²` to an explicit reciprocity
isomorphism.

### 1.10 Modular forms and modularity

Covered in §1.6 — this is Mathlib's most mature "Langlands-adjacent" corner.
Notably absent: any formal statement or partial result toward the modularity
theorem (elliptic curve ↔ weight-2 newform) or the Serre conjecture (odd
irreducible 2-dim mod-p Galois reps ↔ mod-p modular forms) — both are
"blocked on Galois representations" (§1.8) plus an elliptic-curve L-function
side that does exist in some form (`Mathlib/NumberTheory/FLT/` directory
exists, worth checking separately for Fermat's Last Theorem groundwork, which
is adjacent but a different project).

### 1.11 Homological algebra (group cohomology, Galois cohomology)

**Good, and directly useful.** Beyond what's cited in §1.5/§1.9: this is
arguably Mathlib's *strongest* Langlands-adjacent area after number fields —
group cohomology, group homology, Tate cohomology, and continuous cohomology
of topological/profinite groups are all present with functoriality,
long-exact-sequence, Shapiro's lemma, and low-degree (H⁰/H¹/H²) computations.
Galois cohomology specifically (i.e. continuous cohomology specialized to
`Gal(L/K)`-modules) is not packaged as its own named theory but is a thin
wrapper away given `ContCohomology` + `AbsoluteGaloisGroup` +
`ProfiniteGrp`.

### 1.12 Category theory (derived categories, sheaves)

**Broad and mature**, though this is general-purpose Mathlib category theory
rather than anything Langlands-specific: `CategoryTheory/Sites/*` (sheaves,
`SheafCohomology/{Basic,Cech,MayerVietoris}`,
`NonabelianCohomology/H1.lean`), `AlgebraicGeometry/Sites/
ElladicCohomology.lean` (a stub/start on étale-style ℓ-adic cohomology —
worth a closer look if the geometric Langlands / étale-cohomology route is
ever pursued), derived-category and homological-algebra scaffolding under
`Algebra/Homology/*`. Not a near-term bottleneck for *stating* the arithmetic
Langlands conjectures, but will matter for any proof that goes through étale
cohomology of Shimura varieties.

---

## 2. Prerequisites to formally *state* the core conjectures

### 2.1 Local Langlands correspondence (for `GL_n`, then general reductive `G`)

To state "there is a bijection between (a) `L`-parameters
`Gal(K̄_v/K_v) → ^L G` (or Weil-Deligne group → `^L G`) up to conjugacy, and
(b) packets of irreducible admissible representations of `G(K_v)`" you need,
at minimum:
1. A local field `K_v` (§1.2 — partial: have completions, not a clean local-field abstraction).
2. The absolute Galois group / Weil group of `K_v`, continuous (§1.8 — Galois group yes; Weil group and Weil-Deligne group both now built in this project's `Langlands/WeilGroup.lean` and `Langlands/WeilDeligneRepresentation.lean`, Phase 1, complete).
3. A reductive group `G` over `K_v` and its Langlands dual `^L G` (§1.4 — **missing entirely**, hardest gap).
4. Admissible (or at least smooth) representations of `G(K_v)` (§1.5 — **missing**; have continuous reps, not smoothness/admissibility over a locally profinite group).
5. `L`-parameters as continuous, Frobenius-semisimple homomorphisms
   `W_{K_v} → ^L G(ℂ)` (needs 2 and 3).

For `GL_n` specifically, steps 3–4 simplify (dual group of `GL_n` is `GL_n`;
"reductive group" can be replaced by literal matrix group `GL_n` from
§1.4's classical-groups library), which is why `GL_n` is the right entry
point rather than general `G`.

### 2.2 Global Langlands correspondence (automorphic ↔ Galois)

Needs: number field `K` (have, §1.1); adele ring `𝔸_K` (have, §1.3); a
reductive group `G/K`; automorphic representations of `G(𝔸_K)` (§1.6 —
missing in general, have the `GL_2`/classical special case); a global Galois
representation or compatible system (§1.8 — missing); and the local
correspondence at every place to state compatibility. Strictly harder than
2.1 since it needs 2.1 at every place plus a global automorphic theory.

### 2.3 Functoriality

Needs a map of `L`-groups `^L H → ^L G` (needs §1.4's dual-group
construction) inducing a transfer of automorphic representations/L-parameters
— i.e. depends on everything in 2.1/2.2 already existing for *two* groups
`H`, `G` plus the dual-group functor being contravariant-composable.
Strictly the hardest to even state, since it quantifies over pairs of
reductive groups and a homomorphism of their duals.

### 2.4 Artin's conjecture (Artin L-functions are automorphic)

Needs: Artin L-function of a Galois representation (needs §1.8 Galois reps +
§1.7's L-function framework, specifically factoring in local factors at
ramified primes via the **Weil-Deligne group** — now built in this project,
§1.8, `Langlands/WeilDeligneRepresentation.lean`); and the
`n = 1` global Langlands correspondence for `GL_n` (§2.2) to state "is
automorphic." This is *more* tractable to fully state than 2.2/2.3 in one
respect — it only needs `GL_n` — and the Artin L-function side's Weil-Deligne
prerequisite is now in place in this project (nothing in Mathlib upstream
touches it yet).

**Cross-cutting observation:** all four conjectures bottleneck on the same
three missing primitives: **(a)** reductive groups + Langlands dual group,
**(b)** the Weil–Deligne group (now built in this project — both
`Langlands/WeilGroup.lean` and `Langlands/WeilDeligneRepresentation.lean`,
Phase 1 complete), **(c)** smooth/admissible representations of `p`-adic and
adelic groups. Sequencing the roadmap around building these three first, in
the cheapest special case (`GL_n`) before the general case, is the only path
that avoids stalling on (a).

---

## 3. Dependency-ordered roadmap

### Phase 0 — Idele class group (extends existing adele infrastructure) — **COMPLETE**
- **Status:** done, sorry-free. `IdeleGroup K := (AdeleRing (𝓞 K) K)ˣ` and
  `IdeleClassGroup K := IdeleGroup K ⧸ K^×` are built in
  `Langlands/IdeleGroup.lean`, with `toClassGroup` and its kernel computed.
  Also landed alongside it: the local norm map at finite places
  (`Langlands/NormMap.lean`, via `HeightOneSpectrum`) and at archimedean
  places (`NumberField.InfinitePlace`), the full idele-group norm map, the
  Kedlaya–Sutherland unramified-extension correspondence
  (`Langlands/UnramifiedExtension.lean`), and rank-one valuation
  compatibility (`Langlands/HenselianValuation.lean`).
- **Depended on:** `NumberField.AdeleRing` (have),
  `Topology/Algebra/RestrictedProduct/Units.lean` (have),
  `IsOpenUnits.lean` (have).
- **Not yet done:** not upstreamed to Mathlib; compactness of the norm-one
  idele class group and strong approximation remain open (§1.3).
- **Upstreamable:** yes, cleanly — natural next file in
  `Mathlib/NumberTheory/NumberField/`, same authors' territory
  (de Frutos-Fernández, Mercuri have prior art here).

### Phase 1 — Weil group and Weil–Deligne group — **COMPLETE**
- **Status:** done, sorry-free. The plain Weil group is built in
  `Langlands/WeilGroup.lean`: `W_K` as the preimage of ℤ in ℤ̂ under
  `toZhatHom`, the decomposition subgroup (everything), the inertia
  subgroup, the arithmetic Frobenius, and
  `Gal(k̄/𝓀[K]) ≅ ℤ̂` sending Frobenius to 1. On top of that,
  `Langlands/WeilDeligneRepresentation.lean` lands
  `LocalField.WeilDeligneRepresentation K V`: a structure bundling a
  representation `ρ : Representation ℂ (WeilGroup K) V`, a nilpotent
  `N : V →ₗ[ℂ] V`, and the intertwining relation
  `ρ w ∘ₗ N ∘ₗ ρ w⁻¹ = weilNormChar K w • N`, with `ofRepresentation`/
  `trivial` constructors. This matches the phase's original description
  (extension of `Gal(K̄_v/K_v)` by ℤ via valuation/Frobenius, plus the
  `(ρ, N)` pair formalism with nilpotent-intertwining condition, chosen
  over the `W_K × SL_2` alternative).
- **Depended on:** absolute Galois group (have, `AbsoluteGaloisGroup.lean`),
  profinite group category (have, `ProfiniteGrp`, plus a new
  universe-bridging instance landed this session), local field valuation
  (have, `Padics`/completions, plus new rank-one valuation compatibility in
  `Langlands/HenselianValuation.lean`), Frobenius elements (have,
  `RingTheory/Frobenius.lean`). Also newly available as general-purpose
  infrastructure: cyclic-subgroup-by-divisor classification,
  ℤ-subgroup-by-index classification.
- **Not yet done:** not upstreamed to Mathlib.
- **Upstreamable:** yes — this is a standalone, well-defined object useful
  far beyond Langlands (local class field theory, Artin L-functions,
  local epsilon factors).

### Phase 2 — Local class field theory: local Artin map
- **Build:** the local reciprocity map `K_v^× → Gal(K_v^ab/K_v)` (or its
  Weil-group refinement `K_v^× ≅ W_{K_v}^ab`).
- **Depends on:** Phase 1 (Weil group — **now complete**), `RingTheory/
  Frobenius.lean`, `Algebra/BrauerGroup/*` (have — this is where the `H²`
  computation that proves the existence theorem lives),
  `GroupCohomology/Hilbert90.lean` (have).
- **Size:** large. This is a genuine theorem (not just a definition) with a
  real proof burden (local existence theorem, norm groups, Brauer group
  computation over local fields).
- **Scope correction (review):** "`BrauerGroup + Hilbert90`" in the
  dependency list above is the route marker, not the distance covered. The
  local Artin map is not just an isomorphism `K_v^× ≅ W_{K_v}^ab` — it needs
  to be *characterized*: norm functoriality (the map is compatible with norm
  maps for finite extensions), Frobenius compatibility (uniformizers map to
  Frobenius lifts on unramified extensions), and the existence theorem
  (open subgroups of finite index in `K_v^×` correspond to abelian
  extensions). Getting from the raw Brauer-group `H²` computation to an
  Artin map *with these characterizing properties* is the bulk of Serre's
  *Local Fields*, chapters VIII–XIII — this is comparable in size to
  everything else in Phase 2 combined, not a footnote to it.
- **New prerequisites now available (this project):** the local norm map at
  finite places (`Langlands/NormMap.lean`) and archimedean places, the full
  idele-group norm map, and the Kedlaya–Sutherland unramified-extension
  correspondence (`Langlands/UnramifiedExtension.lean`) — these are direct
  down payments on the "norm functoriality" and "Frobenius compatibility on
  unramified extensions" characterizing properties described above, though
  the reciprocity map itself and the existence theorem are still not
  started.
- **Upstreamable:** yes, high-value — local CFT is a named, citable theorem
  many other projects would want.
- **Note:** not strictly required to *state* the four core conjectures (they
  can be stated with the Artin map as an assumed/axiomatized black box), but
  required to make any of Phase 3+ meaningful rather than vacuous.
- **Before building: check for prior formalization.** Of every phase in this
  roadmap, Phase 2 is the likeliest to already exist in some form elsewhere
  — local/global class field theory is a natural target for other
  formalization efforts (e.g. community CFT work adjacent to the
  Mathlib `FLT` project, `Mathlib/NumberTheory/FLT/`, §1.10). Check that
  effort, and any Zulip/roadmap discussion around it, before writing new CFT
  proofs in-repo — duplicating an in-flight class field theory formalization
  would be the single most wasteful outcome in this whole plan.

### Phase 2a — Unramified norm-group surjectivity (scoped first milestone, 2026-08-05)
- **Why this exists:** Phase 2 as written has no small starting task — its
  "first move" jumps straight to the full reciprocity map, sized comparable
  to Serre's *Local Fields* Ch. VIII–XIII combined. This subsection scopes a
  genuinely smaller first cut: the classical fact that for `L/K` the
  **unramified** extension of local fields of degree `n`, the norm map is
  as surjective as it can possibly be — this is the "easy half" of local
  CFT (Serre Ch. V §2–3); the ramified/Lubin–Tate half is the hard part
  Phase 2 is really about.
- **Statement, full version (the classical theorem):** `N_{L/K}(L^×) =
  ⟨π⟩^n · O_K^×` for `L/K` unramified of degree `n`, `π` any uniformizer of
  `K` (also a uniformizer of `L`, since unramified). Equivalently the norm
  map is surjective on unit groups `O_L^× ↠ O_K^×`.
- **Investigated 2026-08-05 (research agent, read-only):** what's already in
  place and what's missing, ingredient by ingredient:
  - **Have, exactly what's needed:** a single-extension local norm map
    `IsDedekindDomain.HeightOneSpectrum.localNormMap : (w.adicCompletion
    L)ˣ →* (v.adicCompletion K)ˣ` in `Langlands/NormMap.lean` (built from
    `Algebra.norm`, already proven to send local units to local units via
    `localNormMap_mem_units`) — this had been an open question (is there a
    *single-extension* norm map, as opposed to only the idele-level one?);
    confirmed yes.
  - **Have, residue-field level:** `Mathlib.FieldTheory.Finite.GaloisField.
    norm_surjective` (norm `𝔽_{q^n} → 𝔽_q` is surjective) and
    `ValuationSubring.surjective_unitGroupToResidueFieldUnits` (reduction
    `O_L^× ↠ 𝓀[L]^×` is surjective, general valuation theory, no
    completeness needed, kernel = `principalUnitGroup`). Composing these
    with the residue-field correspondence already built in
    `Langlands/UnramifiedExtension.lean` gives, essentially for free: **the
    norm map on residue fields `𝓀[L]^× → 𝓀[K]^×` is surjective for the
    unramified extension.**
  - **Missing — real new content, not wiring:** closing the gap from
    "surjective mod principal units" to "surjective on all of `O_K^×`"
    needs lifting through the principal-units filtration `1 + π^i O_L`,
    which classically requires (a) a graded/log isomorphism of successive
    quotients `(1+π^iO_L)/(1+π^{i+1}O_L)` with the residue field
    (additively), (b) the fact the norm acts there via the *trace* map
    (`Mathlib.RingTheory.Trace.Basic.Algebra.trace_surjective` exists and is
    the right trace-surjectivity ingredient, but nothing connects it to
    norm-on-principal-units), and (c) a completeness/limit argument to
    piece the filtration together into full unit-group surjectivity. None
    of (a)–(c) exists in Mathlib or this repo — this is genuinely the
    mathematical content Serre spends real pages on, not a missing lemma
    name.
- **Scoped milestone (what to actually build first):** stop at the
  residue-field-level statement — `𝓀[L]^× → 𝓀[K]^×` is surjective for the
  unramified extension, proved by composing the three pieces above (finite
  field norm surjectivity + residue reduction surjectivity + the existing
  `UnramifiedExtension.lean` residue correspondence) — plus, if the
  `localNormMap`-reduces-to-residue-norm compatibility lemma turns out
  tractable, `O_L^× ↠ O_K^×` **modulo principal units**
  (`O_K^×/(1+𝔪_K)`). This is a clean, citable sub-theorem and an honest
  stopping point that does not require the principal-units filtration
  machinery.
- **Explicitly deferred to a later phase:** the full unramified norm-group
  theorem (`N_{L/K}(L^×) = ⟨π⟩^n · O_K^×`) needs the principal-units
  filtration graded isomorphism first — that filtration machinery is itself
  a legitimate next milestone after this one lands, not part of it.
- **Depends on:** `Langlands/NormMap.lean` (have, single-extension local
  norm map), `Langlands/UnramifiedExtension.lean` (have, residue-field
  correspondence), `Mathlib.FieldTheory.Finite.GaloisField.norm_surjective`
  (have), `ValuationSubring.surjective_unitGroupToResidueFieldUnits` (have).
- **Size:** small for the residue-field-level statement itself, **but the
  `localNormMap`-reduces-to-residue-norm compatibility square does not
  compose from existing pieces** — attempted 2026-08-05 and stopped
  (no file written, no `sorry`) after confirming via loogle against vendored
  Mathlib that no lemma connects `Algebra.norm` (`LinearMap.det (lmul R S
  x)`, `Mathlib/RingTheory/Norm/Defs.lean:64`) to a norm computed after
  reducing mod an ideal/maximal ideal — searches for
  `Algebra.norm (?A ⧸ ?I)`, `LinearMap.det, Ideal.Quotient.mk`, and
  base-change-style norm lemmas all returned nothing on point. Two viable
  routes to close it, both real sub-developments, not one-lemma glue:
  1. **Determinant/basis route.** Establish `Module.Free` for
     `w.adicCompletionIntegers L` over `v.adicCompletionIntegers K`
     (plausible via `Module.free_of_finite_type_torsion_free'`,
     `Mathlib/LinearAlgebra/FreeModule/PID.lean`, needing
     `IsPrincipalIdealRing`/`Module.Finite`/`Module.IsTorsionFree` instances
     for these adic-completion subrings not yet in this repo); lift that
     basis to the residue fields via
     `IsLocalRing.linearCombination_bijective_of_flat`
     (`Mathlib/RingTheory/LocalRing/Module.lean:292`, a genuine
     Nakayama/flatness tool that already exists and is on point); push the
     matrix of `lmul` through `RingHom.map_det`
     (`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`, confirmed to
     exist) to match entrywise reduction.
  2. **Galois/Frobenius route.** Use `Algebra.norm_eq_prod_automorphisms`
     (`Mathlib/RingTheory/Norm/Transitivity.lean`) and
     `prod_galRestrict_eq_norm`
     (`Mathlib/RingTheory/IntegralClosure/IntegralRestrict.lean`) to express
     the norm as a product over `Gal(L/K)` acting on the integral closure
     directly, then match that action to Frobenius on residue fields. Needs
     an `IsGalois` instance for the specific unramified completion
     extension and an `IsIntegralClosure` instance linking
     `w.adicCompletionIntegers L` to `v.adicCompletionIntegers K` — neither
     exists yet; `UnramifiedExtension.lean`'s decomposition-subgroup
     machinery is close but not packaged this way, and reconciling its
     action with `galRestrict`'s is itself nontrivial.
  Either route is comparable in size to what's already in
  `Langlands/UnramifiedExtension.lean` — a legitimate follow-on milestone in
  its own right, not a same-session composition on top of Phase 2a.
- **Next concrete step (for whoever picks this up):** pick route 1 or 2
  above and build the missing instance(s) it needs first, in isolation,
  before attempting the compatibility square itself.
- **Upstreamable:** the residue-field composition itself is likely too thin
  to be its own Mathlib PR, but is a real building block toward an
  upstreamable unramified-norm-group theorem once the principal-units
  filtration exists.

#### Status 2026-08-05 (second attempt) — residue-field half **CLOSED**, compatibility square still open

- **Built:** `Langlands/ResidueFieldNorm.lean` (new, 165 lines, zero
  `sorry`, `lake build Langlands.ResidueFieldNorm` green). Not yet in
  `Langlands.lean`'s import list — consistent with `NormMap.lean`,
  `HenselianValuation.lean`, `UnramifiedExtension.lean`, which are also
  built module-by-module rather than from the root target.
- **Key structural find (supersedes the prior session's "build `Module.Free`
  first" framing for the *structure*, not for the square):**
  `Valuation.HasExtension` (`Mathlib/RingTheory/Valuation/Extension.lean`)
  is exactly the right abstraction, and `NormMap.lean`'s
  `adicCompletionIntegers_comap_eq` (`Langlands/NormMap.lean:424`) is
  literally its hypothesis in disguise —
  `Valuation.isEquiv_iff_val_le_one` (`Mathlib/RingTheory/Valuation/
  Basic.lean:913`) turns the comap-of-valuation-subrings equation into
  `HasExtension`'s `val_isEquiv_comap`. Note `HasExtension` asks only for
  `IsEquiv`, not equality, so the ramification-index factor `e` in the
  valuation relation is harmless.
  - `ResidueFieldNorm.lean:72` `hasExtension_valued_adicCompletion` —
    `(Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).HasExtension
    (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)`.
  - That single instance yields, from `Extension.lean`'s
    `instAlgebra_valuationSubring` / `instIsLocalHomValuationInteger` /
    `IsLocalRing.ResidueField`'s `Ideal.Quotient.algebraOfLiesOver`:
    `Algebra K₀ L₀`, `IsLocalHom (algebraMap K₀ L₀)`,
    `(maximalIdeal L₀).LiesOver (maximalIdeal K₀)`, and
    **`Algebra 𝓀[K] 𝓀[L]`** — the instance whose absence previously made
    the residue-field norm unstatable in the `adicCompletion` setting.
    Re-stated in `adicCompletionIntegers` form at `ResidueFieldNorm.lean:92,
    100, 108` via `inferInstanceAs`, because `adicCompletionIntegers`
    (`Mathlib/RingTheory/DedekindDomain/AdicValuation.lean:809`) is a
    non-reducible `def` for `Valued.v.valuationSubring` and instance search
    does not see through it.
  - `ResidueFieldNorm.lean:118` `coe_algebraMap_adicCompletionIntegers` and
    `:127` `algebraMap_residueField_residue` (both `rfl`) pin these
    instances to `adicCompletionComap`, so the structure is provably the
    intended one and not something else instance search happened to find.
- **Proved:** for `[Finite 𝓀[L]]`,
  - `ResidueFieldNorm.lean:146` `residueField_norm_surjective` —
    `Function.Surjective (Algebra.norm 𝓀[K] (S := 𝓀[L]))`;
  - `ResidueFieldNorm.lean:157` `residueField_units_norm_surjective` —
    `Function.Surjective (Units.map (Algebra.norm 𝓀[K]))`, i.e.
    **`𝓀[L]^× ↠ 𝓀[K]^×`**.
  Both are `FiniteField.norm_surjective` / `FiniteField.unitsMap_norm_surjective`
  (`Mathlib.FieldTheory.Finite.GaloisField` — namespace `FiniteField`, not
  `GaloisField` as the note above says; fully general in `Algebra K K'` with
  `[Finite K']`, not tied to `GaloisField`) applied to the new instance.
  `Finite 𝓀[L]` is a hypothesis: `R`, `S` here are arbitrary Dedekind
  domains, so residue finiteness is not derivable.
- **Scope caveat, stated in the file's docstrings:** these are the
  **abstract** residue-field norm `Algebra.norm 𝓀[K] : 𝓀[L] → 𝓀[K]`. They
  are *not* the reduction of `localNormMap` (`NormMap.lean:386`). The
  unramifiedness of `w | v` is nowhere used and nowhere assumed.
- **Compatibility square: still open, not attempted in code.** Verified this
  session, via loogle against the vendored Mathlib:
  - `IsLocalRing.residue, Algebra.norm` → 0 hits;
    `Algebra.norm, Ideal.Quotient.mk` → 0 hits. No norm-mod-ideal lemma
    exists, confirming the prior session's finding.
  - `Module.Finite, Valuation.integer` → 0 hits;
    `Module.Free, Valuation.integer` → 0 hits;
    `Module.Finite, ValuationSubring` → 0 hits. So route 1's basis is not
    available: `Module.Finite`/`Module.Free` for `L₀` over `K₀` would have
    to be built from scratch (finiteness of the integral closure over a
    complete DVR), which is the bulk of that route.
  - Correction to route 1 above: `IsLocalRing.linearCombination_bijective_of_flat`
    **does not exist** (loogle: unknown identifier; no grep hit in vendored
    Mathlib). The on-point Nakayama-style tools that do exist are
    `Module.exists_basis_of_basis_baseChange` and
    `IsLocalRing.span_eq_top_of_tmul_eq_basis`, but both require
    `Module.FinitePresentation K₀ L₀` — i.e. they need the finiteness above
    as input, they do not supply it.
  - `IsDiscreteValuationRing (v.adicCompletionIntegers K)` *does* exist as a
    Mathlib instance
    (`instIsDiscreteValuationRingSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegers`),
    so once `Module.Finite` + torsion-freeness land, PID-freeness follows.
  - **Additional blocker not previously named:** even with a basis, the
    reduction step needs `𝔪_K · L₀ = 𝔪_L`, i.e. *unramifiedness*. There is
    currently no way to even state that in `NormMap.lean`'s setting — its
    `w | v` has arbitrary ramification index `e`, and Mathlib has no
    `Algebra.IsUnramified` for valuation-ring extensions (only
    `Algebra.IsUnramifiedAt`/`IsUnramifiedIn` for Dedekind-domain primes and
    `IsUnramifiedAtInfinitePlaces`). So route 1 needs *three* new pieces,
    not one: finiteness/freeness, an unramifiedness formulation, and the
    determinant reduction.
  - **The `AdjoinRoot`-basis shortcut was checked and does not apply.**
    `AdjoinRoot.powerBasisAux'` does exist and does work over an arbitrary
    `CommRing` (unlike `AdjoinRoot.powerBasis`), so it would give a free
    basis for free — but only for a ring of the form `AdjoinRoot f`.
    `HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv`
    (`Langlands/UnramifiedExtension.lean:715`) does not expose the internal
    `AdjoinRoot f ≃+* C` isomorphism in its statement, and more decisively
    its setting is the wrong one: it produces
    `integralClosure R (IntermediateField.adjoin K {x})` inside an
    **algebraically closed** ambient `L` (`[IsAlgClosed L]` is a hypothesis),
    whereas `localNormMap` lives on `w.adicCompletion L`, which is not
    algebraically closed and is not given as `K_v⟮x⟯`. Bridging the two
    would require proving the completion extension is monogenic over
    `K₀` — i.e. proving unramified-implies-monogenic in the completion
    setting, which is itself the missing content, not a way around it.
- **Honest summary of Phase 2a status:** `𝓀[L]^× ↠ 𝓀[K]^×` is **closed as
  an abstract finite-field fact** in the correct `adicCompletion` setting,
  with the residue-field algebra structure now genuinely present and pinned
  to `adicCompletionComap`. It is **not** closed as the reduction of
  `localNormMap`; that remains the gate to `O_L^× ↠ O_K^×` mod principal
  units, and is a milestone-sized development (three pieces above), not
  session-sized glue.

#### Status 2026-08-05 (third pass) — re-verification confirms no drift; one new route considered and closed

- **Re-verified against live files and current vendored Mathlib** (still
  commit `520045a` per `.lake/packages/mathlib` git log, unchanged since the
  second-pass session — `langlands/flake.lock` has not moved since the
  original project-skeleton commit `6df4f72`, so this is the *same* Mathlib
  checkout, not a newer one). `Langlands/ResidueFieldNorm.lean` (165 lines),
  `Langlands/NormMap.lean` (763 lines), `Langlands/UnramifiedExtension.lean`
  (1211 lines) all match the second-pass description exactly.
  `lake build Langlands.ResidueFieldNorm` green (3412 jobs).
  `grep -rn sorry langlands/Langlands/` empty.
- **All prior loogle findings re-run fresh, all still 0 hits, confirming no
  Mathlib drift on this specific gap:** `Algebra.norm (?A ⧸ ?I)`,
  `LinearMap.det, Ideal.Quotient.mk`, `IsLocalRing.residue, Algebra.norm`,
  `Algebra.norm, Ideal.Quotient.mk`, `Module.Finite, Valuation.integer`,
  `Module.Free, Valuation.integer`, `Module.Finite, ValuationSubring`,
  `Module.Free, ValuationSubring`, `IsDiscreteValuationRing, Module.Finite`,
  `Valuation.Integers, Module.Finite` — all 0 hits.
  `IsLocalRing.linearCombination_bijective_of_flat` still does not exist
  (unknown identifier). `Module.exists_basis_of_basis_baseChange` and
  `IsLocalRing.span_eq_top_of_tmul_eq_basis` still exist, still need
  `Module.FinitePresentation`/`Module.Finite K₀ L₀` as *input*.
- **New candidate route considered this session (route 3): finiteness via
  `IsIntegralClosure.finite` instead of via `Module.Free`/PID theory.**
  `IsIntegralClosure.finite` (`Mathlib/RingTheory/DedekindDomain/
  IntegralClosure.lean`) gives `Module.Finite A C` for `C` the integral
  closure of a Noetherian integrally-closed domain `A` in a finite separable
  extension `L` of `Frac(A)`. `v.adicCompletionIntegers K` already has
  `IsDiscreteValuationRing` (hence Noetherian, hence — via
  `Valuation.Integers.isIntegrallyClosed_integers` — integrally closed), so
  the two domain-side hypotheses on `A` are already satisfied. This looked
  like a shortcut around building `Module.Free` from PID theory from
  scratch. **It is not**, because it needs `[IsIntegralClosure C A L]` as an
  *instance* — i.e. it needs `w.adicCompletionIntegers L` to actually **be**
  the integral closure of `v.adicCompletionIntegers K` in `w.adicCompletion
  L`, and that fact does not exist in Mathlib for general valuation-ring
  extensions:
  - `ValuationRing, IsIntegralClosure` → 0 hits;
    `Valuation.integer, IsIntegralClosure` → 0 hits;
    `Valuation.HasExtension, IsIntegral` → 0 hits;
    `FiniteDimensional, ValuationSubring, IsIntegral` → 0 hits. No lemma
    connects a `Valuation.HasExtension` pair (which this repo already has,
    `ResidueFieldNorm.lean:72`) to the statement that the top valuation
    subring equals the integral closure of the bottom one.
  - Two directions would be needed to build this fact by hand: (i)
    integral-over-`K₀` elements of `L` land in `L₀` — a standard
    non-archimedean argument (dominant-term bound on a monic relation) that
    does *not* need completeness, but is not in Mathlib in this generality
    either; (ii) elements of `L₀` are integral over `K₀` — the hard
    direction, which genuinely needs completeness of `K` (uniqueness of the
    valuation extension to a finite extension of a complete field), and is
    itself the kind of fact `IsIntegralClosure.finite` was supposed to
    shortcut around, not a corollary of it. Proving only (i) would not
    unlock `IsIntegralClosure.finite`, which needs the full `IsIntegralClosure`
    instance (both directions), so a partial result here wires nothing
    downstream.
  - Checked whether Mathlib's separate non-archimedean-analysis
    normed-field development (`Mathlib/Analysis/Normed/Unbundled/
    SpectralNorm.lean`, `spectralNorm`/`isNonarchimedean_spectralNorm`,
    the de Frutos-Fernández et al. formalization of unique norm extension
    on complete fields) could supply direction (ii) via a
    spectral-norm-equals-valuation identification. It is disconnected from
    this repo's `Valued`/`adicCompletion` framework: `spectralNorm,
    integralClosure` → 0 hits; no lemma equates `spectralNorm` with a
    `Valuation`/`Valued.v` instance anywhere in vendored Mathlib. Bridging
    the two formalizations would itself be new work, not a shortcut.
  - `UnramifiedExtension.lean:808,901` already uses `IsIntegralClosure.finite
    R K K' C` — but in the `[IsAlgClosed L]`/`K⟮x⟯` setting checked and
    rejected in the second-pass session (line 715's theorem doesn't expose
    the needed isomorphism and isn't in the `adicCompletion` setting), not
    the `w.adicCompletionIntegers L` setting needed here. Confirms this is
    the same wall from a different angle, not a way around it.
- **Conclusion: no route to `Module.Finite`/`Module.Free` for
  `w.adicCompletionIntegers L` over `v.adicCompletionIntegers K` is
  buildable from existing Mathlib pieces without first proving, from
  scratch, that a valuation subring extending another (in the
  `Valuation.HasExtension` sense) equals the integral closure of the base in
  a finite extension of a complete field.** That fact is itself genuine
  local-field theory (uses completeness essentially, via uniqueness of
  valuation extension) and is not present under any of the three
  formalizations checked (`Valuation`/`ValuationSubring`,
  `IsIntegralClosure`, `spectralNorm`). No code was written this session —
  every candidate stopped at a landscape check, not a proof attempt, so
  there is nothing partial to leave as `sorry` and nothing was.
- **Status unchanged from second pass**: residue-field half closed
  (`ResidueFieldNorm.lean`), compatibility square open, routes 1 and 2 as
  scoped in the second-pass entry above still stand, route 3 is now also
  ruled out for the same reason as route 1 (needs the same missing
  integral-closure-equals-valuation-ring fact, just reached via a different
  Mathlib lemma). Next session should not re-run any of the loogle queries
  listed above — they are confirmed stable across two independent sessions
  on the same Mathlib commit.

#### Status 2026-08-05 (fourth pass) — the missing integral-closure fact was already in this repo; primitives (1) and (2) both closed

- **Correction to the third-pass conclusion.** The third pass concluded no
  route to `Module.Finite`/`Module.Free` was buildable without proving, from
  scratch, that `w.adicCompletionIntegers L` equals the integral closure of
  `v.adicCompletionIntegers K` in `w.adicCompletion L` (the "hard
  direction": elements of the top valuation ring are integral over the
  base, which needs completeness). **That hard direction had already been
  proved in this repo**, one session earlier than the third pass, as
  `IsDedekindDomain.HeightOneSpectrum.isIntegral_of_mem_of_comap_eq`
  (`NormMap.lean:214`, landed in commit `be81faa`, "close
  `localNormMap_mem_units` via Galois-conjugate integrality argument") — via
  a normal-closure-plus-Galois-conjugates argument that genuinely uses
  `LocalField.valuationSubring_eq_of_comap_eq` (completeness/uniqueness of
  valuation extension). It was used only pointwise, to show local units
  have unit norms, in `localNormMap_mem_units`; nobody had recognized it as
  the general integral-closure fact three sessions had been searching for.
  This is a **process finding**, not just a math one: the third-pass
  loogle-based search strategy (querying vendored Mathlib for "is this
  connected to `IsIntegralClosure`/`spectralNorm`/etc.") never checked
  whether the fact already existed *in this repo's own files* under a
  different name/framing.
- **Primitive (1) — `Module.Finite`/`Module.Free` for
  `w.adicCompletionIntegers L` over `v.adicCompletionIntegers K` —
  CLOSED.** New file `langlands/Langlands/AdicCompletionIntegralClosure.lean`
  (commit `106870a`), zero `sorry`, `lake build
  Langlands.AdicCompletionIntegralClosure` and full `lake build` both green
  (8670 jobs). Content:
  - `Valuation.isIntegral_imp_map_le_one` (`:67`): the genuinely missing
    "easy direction" — a standalone generalization of the forward direction
    of `Valuation.Integers.isIntegral_iff_v_le_one`
    (`Mathlib/RingTheory/Valuation/Integral.lean`) that drops its bundled
    `exists_of_le_one` surjectivity field (false here: `v.adicCompletionIntegers
    K` is a proper subring of `w.adicCompletionIntegers L` in general, not
    all of it). Proof is the same dominant-term/ultrametric argument as the
    Mathlib original, ported by hand since the `Valuation.Integers`
    structure itself doesn't apply.
  - `isIntegral_iff_mem_adicCompletionIntegers` (`:163`): combines the easy
    direction with `isIntegral_of_mem_of_comap_eq` (`NormMap.lean`) to get
    the full iff.
  - `instIsIntegralClosureAdicCompletionIntegers` (`:187`): the
    `IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers
    K) (w.adicCompletion L)` instance this unlocks.
  - `instModuleFiniteAdicCompletionIntegers` / `instModuleFreeAdicCompletionIntegers`
    (`:198`, `:204`): from `IsIntegralClosure.finite`/`.module_free`
    (`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`), under an
    added `[Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]`
    hypothesis — those two Mathlib lemmas are themselves scoped to finite
    *separable* extensions, so this repo's instances inherit that scope.
    Separability is automatic in characteristic `0` (number fields, this
    project's primary target) but not attempted in general (positive
    characteristic local fields can have inseparable extensions).
  - Building this also required constructing, from scratch,
    `Algebra (v.adicCompletionIntegers K) (w.adicCompletion L)` (the
    composite through `v.adicCompletion K`), the matching `IsScalarTower`
    instances, and `Module.IsTorsionFree (v.adicCompletionIntegers K)
    (w.adicCompletion L)` (from injectivity of the algebra map into a field)
    — none of these existed prior to this file, and `IsIntegralClosure.module_free`
    needs the torsion-free instance as a hypothesis.
- **Primitive (2) — formulate unramifiedness for valuation-ring extensions
  (general `e`) — CLOSED (formulation only, not connected to anything
  downstream yet).** New file
  `langlands/Langlands/UnramifiedValuationExtension.lean` (commit `61eab9b`),
  zero `sorry`, builds green. `IsUnramified K L v w : Prop` is defined as
  `𝔪_K · O_L = 𝔪_L` (`Ideal.map (algebraMap K₀ L₀) (maximalIdeal K₀) =
  maximalIdeal L₀`), directly on the algebra structure from primitive (1).
  `map_maximalIdeal_le` proves the containment `𝔪_K · O_L ≤ 𝔪_L` holds
  unconditionally (`IsLocalRing.map_maximalIdeal_le`, using the `IsLocalHom`
  instance already in `ResidueFieldNorm.lean`), so `isUnramified_iff_le`
  reduces `IsUnramified` to the one nontrivial reverse containment. This was
  a much smaller piece than primitive (1) — `Ideal.ramificationIdx'`
  (`Mathlib/NumberTheory/RamificationInertia/Ramification.lean`) turned out
  to already be stated generally enough (any `CommRing`s with an `Algebra`
  instance and any two ideals) to apply directly to `K₀ → L₀`, no new
  ramification-index theory was needed, only the packaging.
- **Compatibility square (does `localNormMap` reduce mod the maximal ideal
  to the `ResidueFieldNorm.lean` residue norm?) — NOT attempted this
  session, per the task's own instruction not to force it.** With
  primitives (1) and (2) now in hand, the determinant/basis route sketched
  in the second-pass entry above is substantially more tractable than it
  was: `Module.Free` (primitive 1) gives an integral basis of `L₀` over
  `K₀`; for a *finite free* module over a local ring, a basis always
  reduces (mod the maximal ideal) to a basis of the quotient — a standard
  Nakayama-type fact, not yet located/proved in this repo. The quotient
  `L₀ ⧸ 𝔪_K·L₀` only equals `𝓀[L] = L₀ ⧸ 𝔪_L` (the residue field target of
  `ResidueFieldNorm.lean`'s norm) **under `IsUnramified`** (primitive 2) —
  this is precisely why unramifiedness is the natural hypothesis for this
  square, matching Serre's scoping of the "easy half" of local CFT. The
  remaining gap, concretely: (a) locate or prove "basis of finite free
  module over local ring reduces to basis of quotient by maximal ideal"
  (Nakayama consequence, likely exists in Mathlib under
  `Module.Free`/`IsLocalRing` somewhere, not checked this session); (b)
  under `IsUnramified`, identify `L₀ ⧸ 𝔪_K·L₀` with `𝓀[L]`; (c) show
  `Algebra.norm K L` (the determinant of the multiplication matrix in the
  chosen basis) reduces mod `𝔪_K` to `Algebra.norm 𝓀[K]` of the reduced
  element in the reduced basis — a determinant-reduces-mod-ideal argument.
  None of (a)-(c) attempted; this is the concrete next-session starting
  point, smaller in scope than the second-pass entry's "route 1" since (1)
  and (2) are now discharged prerequisites rather than open blockers.
- **Full build status**: `grep -rn sorry langlands/Langlands/` empty across
  the whole `Langlands/` tree; full `lake build` green, 8670 jobs.
- **Mathlib-upstreaming candidate flagged** (not attempted, see
  `/home/me/git/rhizone/motif/TODO.md`): `Valuation.isIntegral_imp_map_le_one`
  and the general pattern "a valuation subring extending a base valuation
  ring, in the `Valuation.HasExtension` sense, over a *complete* base field
  in a finite extension, equals the integral closure of the base" look like
  a genuine gap in Mathlib's own `Valuation`/`ValuationSubring` API, not
  specific to this project's `HeightOneSpectrum`/adele setup.

#### Status 2026-08-05 (fifth pass) — the compatibility square is CLOSED

- **New file** `langlands/Langlands/NormMapResidueCompatibility.lean`, zero
  `sorry`, `lake build Langlands.NormMapResidueCompatibility` and full
  `lake build` both green (8670 jobs; `grep -rn sorry langlands/Langlands/`
  still empty). Not yet in `Langlands.lean`'s import list, consistent with
  `NormMap.lean`/`HenselianValuation.lean`/`UnramifiedExtension.lean`/
  `ResidueFieldNorm.lean`/`AdicCompletionIntegralClosure.lean`/
  `UnramifiedValuationExtension.lean`, which are also all built
  module-by-module rather than from the root target.
- **The three-step path the fourth pass laid out (a)-(c) all closed, plus a
  route-around for a subtlety the fourth pass didn't anticipate:**
  1. **(a) — basis-reduces-to-basis-of-quotient (Nakayama-type fact).**
     Not built from scratch as the fourth pass expected — it was already in
     Mathlib, unrecognized: `IsLocalRing.basisQuotient`
     (`Mathlib/RingTheory/LocalRing/Quotient.lean`), for `[IsLocalRing R]
     [Module.Finite R S] [Module.Free R S]`, gives a basis of `S ⧸
     Ideal.map (algebraMap R S) (maximalIdeal R)` over `ResidueField R`
     from a basis of `S` over `R`, plus a companion `basisQuotient_repr`
     pinning down how `Basis.repr` reduces. A fresh loogle query
     (`Module.Free, IsLocalRing, Module.Basis`) surfaced it directly — the
     fourth-pass session's searches never tried this exact combination.
  2. **(c) — determinant reduces mod the ideal.** `RingHom.map_det`
     (`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`, confirmed
     already in the fourth-pass writeup) plus `Algebra.leftMulMatrix_eq_repr_mul`
     (the direct entrywise formula for `leftMulMatrix`, not the
     `LinearMap.toMatrix`-wrapped `leftMulMatrix_apply`) combine directly
     with (a)'s `basisQuotient_repr`/`basisQuotient_apply` to give a fully
     general, valuation-theory-free fact:
     `IsLocalRing.residue_norm_eq_norm_residue`
     (`NormMapResidueCompatibility.lean:63`) — for any finite free algebra
     `S` over a local ring `R`, `Algebra.norm` commutes with reduction mod
     the maximal ideal. This is a genuinely reusable, self-contained lemma,
     not specific to this project's adic-completion setting at all.
  3. **(b) — identifying `L₀ ⧸ 𝔪_K·L₀` with `𝓀[L]` under `IsUnramified`, and
     the instance-mismatch subtlety this actually raised.** Naively
     rewriting the ideal via the `IsUnramified` equation
     (`rw [hU] at h`) fails with "motive is not type correct": the
     `Algebra (R ⧸ 𝔪) (S ⧸ pS)` instance baked into
     `IsLocalRing.basisQuotient`'s ambient context
     (`Ideal.Quotient.algebraQuotientMapQuotient`) is stated for the
     specific syntactic form `Ideal.map (algebraMap R S) 𝔪`, not for an
     arbitrary ideal — `rw` cannot generalize through it. Worse, even after
     fixing the type-level identification, `𝓀[L]`'s *actual* algebra
     structure over `𝓀[K]` in this repo (`Langlands.ResidueFieldNorm`,
     built via `Valuation.HasExtension`/`Ideal.Quotient.algebraOfLiesOver`)
     is a *different* `Algebra` term than `algebraQuotientMapQuotient`,
     even though both are mathematically "the" residue-field algebra
     structure induced by the same ring hom. Fixed by proving a version of
     the general lemma, `IsLocalRing.residue_norm_eq_norm_residue_of_eq_map`
     (`:82`), parametrized over an arbitrary `Algebra (R⧸𝔪) (S⧸I)` instance
     satisfying only a compatibility hypothesis on `algebraMap`, then
     discharging that hypothesis for the two instances via
     `Algebra.algebra_ext` (two `Algebra` structures agreeing as terms once
     their `algebraMap`s agree pointwise) — both instances' `algebraMap`s
     reduce to the same formula, `mk 𝔪 r ↦ mk I (algebraMap R S r)`
     (`Ideal.Quotient.algebraMap_quotient_map_quotient` for one side,
     `Ideal.Quotient.algebraMap_mk_of_liesOver`-shaped for the other, both
     already `rfl`/`simp` lemmas in Mathlib), so the ext argument is
     immediate once stated. This closes (b) as
     `residue_norm_eq_norm_residue_of_isUnramified` (`:139`).
  4. **Connecting the ring-norm `Algebra.norm K₀` to the field-norm inside
     `localNormMap` (an extra piece the fourth pass's three-step sketch
     didn't separate out, since it conflated "the norm" without
     distinguishing the ring-level and field-level versions).**
     `Algebra.algebraMap_intNorm`
     (`Mathlib/RingTheory/IntegralClosure/IntegralRestrict.lean`, general
     norm/fraction-field compatibility for an integral-closure pair) plus
     `Algebra.intNorm_eq_norm` (`intNorm` agrees with `Algebra.norm` once
     the extension is finite free, which `L₀/K₀` now is, by primitive (1))
     give `algebraMap_norm_eq_norm_algebraMap` (`:192`): `algebraMap K₀ K
     (Algebra.norm K₀ x) = Algebra.norm K (algebraMap L₀ L x)` — i.e. the
     ring-norm and the field-norm (`localNormMap`'s underlying map) agree
     under the field inclusions. Needed three more instances not
     previously built at the `K₀`/`L₀` level (as opposed to the ambient
     field level already available): `IsDomain`, `IsIntegrallyClosed`,
     `IsFractionRing K₀ K` (all three via `inferInstanceAs` through the
     generic `ValuationSubring` instances, same pattern as
     `ResidueFieldNorm.lean`'s `Algebra`/`IsLocalHom` restatements — needed
     because `adicCompletionIntegers` is a non-reducible `def` for
     `Valued.v.valuationSubring`), `Algebra.IsIntegral K₀ L₀` (from
     `Algebra.IsIntegral.of_finite`, using primitive (1)'s
     `Module.Finite`), and `Module.IsTorsionFree K₀ L₀` (built by hand,
     mirroring `AdicCompletionIntegralClosure.lean`'s proof pattern for
     `Module.IsTorsionFree K₀ (w.adicCompletion L)`, via injectivity of
     `algebraMap K₀ L₀` — itself derived from injectivity of the composite
     into the field, using `coe_algebraMap_adicCompletionIntegers`).
  5. **The square itself:** `localNormMap_reduce`
     (`NormMapResidueCompatibility.lean:206`) combines steps 3 and 4: for a
     unit `a` of `w.adicCompletion L` landing in `w.adicCompletionIntegers
     L`, `IsUnramified K L v w →` the residue (in `𝓀[K]`, via
     `IsLocalRing.residue`) of `localNormMap K L v w a` (which lands in
     `v.adicCompletionIntegers K`, by the already-existing
     `localNormMap_mem_units`) equals `Algebra.norm 𝓀[K]`
     (`Langlands.ResidueFieldNorm`'s residue-field norm) of the residue of
     `a`. This is the compatibility square from the module docstring, fully
     closed, `IsUnramified` used exactly where the fourth pass predicted it
     would be needed and nowhere else.
- **Scope note:** `IsLocalRing.residue_norm_eq_norm_residue` and
  `residue_norm_eq_norm_residue_of_eq_map` (steps 2-3 above) are stated with
  no reference to `HeightOneSpectrum`/adic completions at all — they are
  general facts about `Algebra.norm` for any finite free algebra over a
  local ring, and are plausible standalone Mathlib-upstreaming candidates in
  their own right (`Mathlib.RingTheory.LocalRing.Quotient` or
  `Mathlib.RingTheory.Norm.Defs` look like natural homes), independent of
  whether the rest of this file's valuation-specific content is
  upstreamed. Not attempted this session.
- **Not attempted this session, explicitly deferred:** tying
  `residueField_units_norm_surjective` (`𝓀[L]ˣ ↠ 𝓀[K]ˣ`) through
  `localNormMap_reduce` to get `O_L^× ↠ O_K^× / (1+𝔪_K)` (surjectivity of
  `localNormMap` on unit groups modulo principal units — the milestone this
  section originally scoped as the stopping point). The composition is
  believed to go through cleanly by inspection — lift a target
  `𝓀[K]`-residue via `ValuationSubring.surjective_unitGroupToResidueFieldUnits`
  applied twice (once at each of `K₀`, `L₀`) and `residueField_units_norm_surjective`
  in between, then use `localNormMap_reduce` to match residues — but was
  not built this session (the task's brief was scoped to the compatibility
  square as the main goal, with this composition as an optional stretch not
  to be forced), and the exact API mismatch between `localNormMap_mem_units`'s
  `(_).units` (generic `Submonoid.units`) and
  `ValuationSubring.unitGroupToResidueFieldUnits`'s `.unitGroup` (a
  purpose-built `Subgroup Kˣ`) would need to be reconciled first — likely a
  short lemma, not a new development, but not checked. This is the concrete
  next step for whoever picks this up, and is now genuinely session-sized
  (no new instances or general lemmas expected to be needed), unlike every
  prior entry in this section.
- **The full unramified norm-group theorem** (`N_{L/K}(L^×) = ⟨π⟩^n·O_K^×`,
  needing the principal-units filtration graded isomorphism) remains out of
  scope for Phase 2a as originally scoped, unchanged from prior passes.

#### Status 2026-08-05 (sixth pass) — mod-principal-units surjectivity CLOSED; full `O_K^×` surjectivity scoped, not attempted

- **New file** `langlands/Langlands/UnitGroupModPrincipalUnitsSurjective.lean`, zero
  `sorry`, `lake build Langlands.UnitGroupModPrincipalUnitsSurjective` and full
  `lake build` both green (8670 jobs; `grep -rn sorry langlands/Langlands/` empty).
  Not yet in `Langlands.lean`'s import list, consistent with the rest of Phase 2a's
  files.
- **Closed exactly the composition the fifth pass scoped as the next step:**
  `IsDedekindDomain.HeightOneSpectrum.localNormMap_units_surjective_mod_principalUnits`
  — for every `t : (ResidueField K₀)ˣ` (a class of `O_K^× / (1 + 𝔪_K)`, presented as a
  residue-field unit rather than via `ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits`
  by name, since the two are the same group and the residue-field presentation is what
  `localNormMap_reduce` and `residueField_units_norm_surjective` are already stated in
  terms of), there is a local unit `a` of `L₀ = w.adicCompletionIntegers L` whose norm
  `localNormMap K L v w a` reduces mod `𝔪_K` to `t`. This is `N_{L/K} : O_L^× ↠
  O_K^× / (1 + 𝔪_K)`, the milestone Phase 2a originally scoped as its stopping point.
- **The API-mismatch "known snag" flagged at the end of the fifth pass (`localNormMap_mem_units`'s
  `Submonoid.units` vs. `ValuationSubring.unitGroupToResidueFieldUnits`'s purpose-built
  `.unitGroup`) turned out to need no reconciliation lemma at all** — the proof sidesteps
  `ValuationSubring.unitGroup`/`unitGroupToResidueFieldUnits` entirely and instead composes
  three pieces already in the right form: (1) `Submonoid.unitsEquivUnitsType : S.units ≃*
  Sˣ` (general submonoid API, converts a `Submonoid.units`-style element directly to the
  ring's own unit type, no bridging lemma needed since it's definitionally the same
  `Aˣ` that `localNormMap_reduce`'s residue statement is phrased in terms of once
  unfolded); (2) `IsLocalRing.surjective_units_map_of_local_ringHom` applied to
  `IsLocalRing.residue_surjective` (both fully general, no valuation content) gives
  surjectivity of reduction-mod-maximal-ideal on unit groups for *any* local ring, in
  particular `L₀`; (3) `residueField_units_norm_surjective` (`Langlands.ResidueFieldNorm`,
  the abstract residue norm) and `localNormMap_reduce` (`Langlands.NormMapResidueCompatibility`,
  the compatibility square) match up the two sides. The only nontrivial bookkeeping was
  unfolding `Units.map (residue A).toMonoidHom (S.unitsEquivUnitsType ⟨x, hx⟩)` down to
  `residue A ⟨x, hx.1⟩` (`rfl`, since `unitsEquivUnitsType`'s underlying value is literally
  the representative) to match `localNormMap_reduce`'s statement shape, plus a
  `Units.coe_map`/`Units.ext` dance to move between unit-level and value-level equalities.
  No new instances, no new general lemmas — exactly the "session-sized, no new instances
  expected" scope the fifth pass predicted.
- **Full unramified norm-group theorem — the route to close it, worked out but not
  attempted this session (per the task's brief: land mod-principal-units surjectivity as
  the main goal, don't force the full lift).** The classical argument
  (Serre, *Local Fields*, Ch. V §2–3) for upgrading `O_L^× ↠ O_K^× / (1+𝔪_K)` to full
  `O_L^× ↠ O_K^×` in the unramified case is a Hensel-type successive-approximation
  argument, not a single lemma — concretely:
  1. **Graded pieces of the principal-units filtration are the residue field,
     additively, matching on both sides under `IsUnramified`.** For `i ≥ 1`,
     `(1 + 𝔪_K^i) / (1 + 𝔪_K^{i+1}) ≅ 𝔪_K^i / 𝔪_K^{i+1} ≅ 𝓀[K]` (additively, via
     `1 + πx ↦ x mod 𝔪_K`, `π` a uniformizer), and likewise on the `L` side with `𝓀[L]`
     — the *same* isomorphism data as `IsLocalRing.residue`/`basisQuotient`, one filtration
     step down. Since `L/K` is unramified, `π` (a uniformizer of `K`) is also a uniformizer
     of `L`, so the filtration steps `1 + 𝔪_K^i` and `1 + 𝔪_L^i` are indexed compatibly
     (no ramification-index rescaling needed) — this is precisely why the unramified case
     is the "easy half"; for ramified extensions the filtration on the two sides is indexed
     by different powers and the graded pieces don't align this simply.
  2. **The norm, restricted to each graded piece, acts as the trace.** The standard
     computation `N(1 + πx) ≡ 1 + Tr(x)·π mod π^{i+2}·(\text{higher order in } x)` (a
     first-order expansion of the norm/determinant of `1 + πx` acting by multiplication)
     identifies the induced map on graded pieces `𝓀[L] → 𝓀[K]` with
     `Algebra.trace 𝓀[K] : 𝓀[L] → 𝓀[K]` (additive), not with `Algebra.norm` (multiplicative)
     — this is the standard fact that norm "looks like" trace infinitesimally near `1`.
     `Mathlib.RingTheory.Trace.Basic`'s `Algebra.trace_surjective` (cited already in the
     original Phase 2a scoping, still not connected to anything) is exactly the ingredient
     this step needs, once the norm-linearizes-to-trace identity itself is proved — that
     identity is new content, not in Mathlib or this repo.
  3. **Completeness assembles the filtration into full surjectivity.** Given `y ∈ O_K^×`,
     step 1 lifts `t := y mod (1+𝔪_K)` to some `x_1 ∈ O_L^×` with `N(x_1) ≡ y mod (1+𝔪_K)`
     (this session's theorem). Write `y = N(x_1)·u_1` with `u_1 ∈ 1 + 𝔪_K`; step 2's
     graded-trace-surjectivity lifts `u_1` to `1 + z_1 ∈ 1 + 𝔪_L` with
     `N(1+z_1) ≡ u_1 mod (1+\mathfrak m_K^2)`, giving `x_2 := x_1(1+z_1)` with
     `N(x_2) ≡ y mod (1+\mathfrak m_K^2)`; iterating produces a Cauchy sequence
     `x_1, x_2, \dots` in `O_L^×` (in the `𝔪_L`-adic topology) converging (by completeness
     of `L`, already available via `adicCompletion`) to `x` with `N(x) = y` exactly.
     This is a genuine limit/Cauchy-sequence argument over `adicCompletion L`, not
     algebraic bookkeeping — the kind of thing `Mathlib.Topology.UniformSpace.Cauchy` /
     `CompleteSpace` machinery is built for, but no prior work in this repo has done a
     successive-approximation argument of this shape, so there is no local pattern to
     reuse.
  - **Net assessment:** step 1 (this session) and step 3's completeness *infrastructure*
    (already available, `adicCompletion` is complete) are in hand; steps 1's counterpart
    at each filtration level (step 2, the norm-linearizes-to-trace identity) is genuinely
    new mathematical content — comparable in size to the compatibility-square work of the
    fourth/fifth passes, not a short lemma. This is exactly the "principal-units filtration
    machinery" the original Phase 2a scoping (top of this section) flagged as **explicitly
    deferred to a later phase**, and that assessment still stands: it is a legitimate
    next milestone in its own right, sized similarly to what this section has already
    built, not a same-session extension of it.
  - **Next concrete step for whoever picks this up:** prove the norm-linearizes-to-trace
    identity on a single graded piece first, in isolation (step 2 above), before attempting
    the successive-approximation assembly (step 3) — mirroring how this project has
    sequenced every other piece of Phase 2a (primitives before the square, the square
    before the composition).

#### Status 2026-08-05 (seventh pass) — step 2 (norm linearizes to trace on the graded pieces) CLOSED, for every filtration level

- **New file** `langlands/Langlands/NormTraceLinearization.lean`, zero `sorry`,
  `lake build Langlands.NormTraceLinearization` and full `lake build` both green (8670 jobs;
  `grep -rn sorry langlands/Langlands/` empty). Not yet in `Langlands.lean`'s import list,
  consistent with the rest of Phase 2a's files.
- **Worked out on paper first, then checked against Mathlib, per the task's brief.** The
  classical computation `N(1+πx) ≡ 1+Tr(x)·π \pmod{π^2}` is the constant/linear-coefficient
  read-off of the determinant Taylor expansion `det(1+tA) = 1 + tr(A)·t + O(t^2)` applied to
  `A :=` the matrix of left multiplication by `x` in a chosen `K₀`-basis of `L₀` — i.e. this is
  not new content Serre proves by hand; it is the `k=1` case of the standard
  characteristic-polynomial-coefficients-are-elementary-symmetric-functions fact, which Mathlib
  already has as `Matrix.det_one_add_smul` (`Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`,
  found via loogle query `Matrix.det (1 + ?t • ?A)`, one query, first try — this is the single
  ingredient that makes the whole step close in one session rather than needing new
  determinant-Taylor-expansion theory).
- **Closed as an exact algebraic identity, not merely a mod-`t^2` congruence**, and — the one
  genuine improvement over the roadmap's own scoping — **for every filtration level `n`, not
  just `n = 0`/`i = 1`.** The task's brief explicitly invited scoping down to `i = 1` alone if
  defensible ("check whether step 3 actually needs the general-`i` version"); it turned out
  general `i` costs nothing extra, because the same proof that gives the `i=1` case, with `t`
  replaced by `π^{n+1}`, gives every `i = n+1` for free — the argument only ever uses
  `π^{n+1} ∈ 𝔪_K` (true for every `n ≥ 0`), never a `mod π^2`-specific fact. So the file proves
  the fully general statement and the `i=1` case is simply `n = 0` of it; no separate
  future-work item for general `i` is needed.
- **Route, three pieces:**
  1. `Algebra.exists_norm_one_add_smul_eq` (`NormTraceLinearization.lean:83`) — fully general, no
     valuation or local-ring content at all: for `S` a finite free `R`-algebra, `t : R`, `x : S`,
     `∃ c, Algebra.norm R (1 + t•x) = 1 + t·Algebra.trace R S x + t²·c`. Proved via
     `Algebra.leftMulMatrix b (1+t•x) = 1 + t•(leftMulMatrix b x)` (since `leftMulMatrix b` is an
     `R`-algebra hom, so respects `+`, `1`, and `R`-scalar `•`) fed into `Matrix.det_one_add_smul`,
     matched against `Algebra.norm_eq_matrix_det`/`Algebra.trace_eq_matrix_trace`.
  2. `IsLocalRing.residue_trace_eq_trace_residue` / `residue_trace_eq_trace_residue_of_eq_map`
     (`:110`, `:129`) — the trace analogue of `NormMapResidueCompatibility.lean`'s
     `residue_norm_eq_norm_residue`/`_of_eq_map`, proved the same way (`IsLocalRing.basisQuotient`
     plus entrywise reduction) but genuinely easier: trace is a sum of diagonal entries, so it
     commutes with any ring hom applied entrywise via the general `AddMonoidHom.map_trace`
     (found by loogle query `Matrix.trace, Matrix.map`, one query), with no determinant/`RingHom.map_det`
     step needed. The `_of_eq_map` version carries over the same instance-mismatch fix as the norm
     case (`Algebra.algebra_ext` reconciling `Ideal.Quotient.algebraQuotientMapQuotient` against
     `Langlands.ResidueFieldNorm`'s `Valuation.HasExtension`-built `Algebra 𝓀[K] 𝓀[L]` instance) —
     copied directly from the fifth pass's proof of the norm version, no new idea needed there.
  3. `IsDedekindDomain.HeightOneSpectrum.residue_trace_eq_trace_residue_of_isUnramified` (`:164`)
     specializes (2) to `K₀`/`L₀` under `IsUnramified`, exactly mirroring
     `residue_norm_eq_norm_residue_of_isUnramified` from the fifth pass.
- **The main theorem:** `exists_norm_one_add_uniformizer_pow_smul_eq_trace_add`
  (`NormTraceLinearization.lean:194`) — for `π` a uniformizer of `K₀` (`Irreducible π`, giving
  `maximalIdeal K₀ = Ideal.span {π}` via Mathlib's `Irreducible.maximalIdeal_eq`, using the
  pre-existing `IsDiscreteValuationRing K₀` instance), `IsUnramified K L v w`, `n : ℕ`, and
  `x : L₀`: there is `y : K₀` with `Algebra.norm K₀ (1 + π^{n+1}•x) = 1 + π^{n+1}·y` and
  `residue K₀ y = Algebra.trace 𝓀[K] (residue L₀ x)`. Combines (1) (with `t := π^{n+1}`) and (3):
  `y := Algebra.trace K₀ L₀ x + π^{n+1}·c` from (1)'s witness `c`, and `residue K₀ y =
  residue K₀ (trace K₀ L₀ x)` since `π^{n+1} ∈ maximalIdeal K₀` kills the `π^{n+1}·c` term, then
  (3) identifies that with `Algebra.trace 𝓀[K] (residue L₀ x)`.
- **What this identity means, read against the `(1+𝔪_K^i)/(1+𝔪_K^{i+1})` framing of the sixth
  pass's step 2:** identifying `𝔪_K^{n+1}/𝔪_K^{n+2}` with `𝓀[K]` via `y ↦ 1+π^{n+1}y`
  (likewise `𝔪_L^{n+1}/𝔪_L^{n+2}` with `𝓀[L]`, using that `L₀`'s maximal ideal is
  `Ideal.span {algebraMap K₀ L₀ π}` under `IsUnramified` — `π` remains a uniformizer of `L₀`
  too, matching the roadmap's "same filtration index on both sides" observation for the
  unramified case), this theorem is exactly "the map induced on the `(n+1)`-th graded piece by
  `x ↦ N(1+π^{n+1}x)` is `Algebra.trace 𝓀[K] : 𝓀[L] → 𝓀[K]`" for `i = n+1 = 1, 2, 3, …`.
- **Explicitly not built this session (left for step 3's assembly, per the task's scoping
  instruction not to force step 3):**
  1. No bundled quotient-group objects `(1+𝔪_K^i)/(1+𝔪_K^{i+1})` or `𝔪_K^i/𝔪_K^{i+1}` — the
     result is stated as a concrete algebraic identity (`∃ y, N(1+π^{n+1}x) = 1+π^{n+1}y ∧
     residue y = trace (residue x)`) rather than as a genuine `AddMonoidHom`/`MonoidHom` between
     bundled quotients. Building that packaging (and proving the identification
     `𝔪_K^{n+1}/𝔪_K^{n+2} ≃+ 𝓀[K]` as an actual `Module`/`AddEquiv`, not just the ad hoc
     `y ↦ 1+π^{n+1}y` reading used informally above) is bookkeeping, not new mathematical
     content, but was not attempted — nothing in step 3's Cauchy-sequence argument (as sketched
     in the sixth pass) obviously needs the bundled form over the concrete-identity form; whoever
     assembles step 3 should check this directly rather than assume it.
  2. `1 + π^{n+1} • x` is not shown to be a genuine element of `L₀ˣ` (a local unit) here, nor is
     the result connected to `localNormMap` (field-level, `w.adicCompletion L`) the way
     `NormMapResidueCompatibility.lean`'s `localNormMap_reduce` connects the norm compatibility
     square to `localNormMap`. This theorem works entirely at the `Algebra.norm K₀ : L₀ → K₀`
     ring level, matching how the fifth-pass square was *proved* (`algebraMap_norm_eq_norm_algebraMap`
     bridges ring-norm to field-norm only afterward) — the same bridging lemma should transfer
     here without new difficulty (`1+π^{n+1}x` is visibly a unit of the local ring `L₀`, since it
     reduces to `1 ≠ 0` in the residue field), but was not written, since it is not needed to
     state step 2's mathematical content and the task scoped this session to step 2 itself.
  3. **Step 3 (Cauchy-sequence assembly) remains untouched, as instructed** — still explicitly
     out of scope for this session, per the task's brief. With steps 1 and 2 now both closed, the
     `ROADMAP.md` state is: the full unramified norm-group theorem needs only the
     successive-approximation/completeness argument described in the sixth pass's step 3 sketch,
     built on top of `localNormMap_units_surjective_mod_principalUnits` (sixth pass) and this
     session's `exists_norm_one_add_uniformizer_pow_smul_eq_trace_add`.

#### Status 2026-08-05 (eighth pass) — Step A gaps closed; step 3's one-step correction and continuity ingredients built; full assembly (induction, Cauchy-ness, limit) not attempted

- **Three new files, zero `sorry`, full `lake build` green (8670 jobs; `grep -rn sorry
  langlands/Langlands/` empty).** None yet in `Langlands.lean`'s import list, consistent with the
  rest of Phase 2a's files.
- **`NormTraceLinearization.lean`'s two flagged gaps, closed** (commit `796ea51`), scoped to what
  the successive-approximation assembly actually needs:
  - `isUnit_one_add_uniformizer_pow_smul` (`:236`): `1 + π^{n+1} • x` is a unit of `L₀`. Needs no
    `IsUnramified` hypothesis, only the always-true forward containment `𝔪_K·L₀ ≤ 𝔪_L`
    (`map_maximalIdeal_le`): `π^{n+1} ∈ 𝔪_K` puts `π^{n+1} • x ∈ 𝔪_K·L₀ ≤ 𝔪_L`, so `1 + π^{n+1}•x`
    reduces to `1 ≠ 0` in `𝓀[L]`, hence is a unit by `IsLocalRing.residue_ne_zero_iff_isUnit`.
  - `isUnit_algebraMap_one_add_uniformizer_pow_smul` (`:257`) and
    `localNormMap_coe_one_add_uniformizer_pow_smul` (`:266`): the field-level counterpart (push
    the local unit forward along `algebraMap L₀ L`) and the bridge from the ring-level identity to
    `localNormMap`, via `algebraMap_norm_eq_norm_algebraMap` (`NormMapResidueCompatibility.lean`,
    fifth pass) — exactly the "should transfer without new difficulty" prediction from the seventh
    pass's writeup, confirmed: no new idea was needed, only re-deriving the fifth pass's
    `localNormMap_reduce`-proof pattern for this specific element.
- **New file `PrincipalUnitsCauchySequence.lean`** (commit `a0359bd`): the single Hensel-lift
  correction step, `exists_one_add_uniformizer_pow_smul_norm_sub_mem` — under `IsUnramified` and
  `[Finite 𝓀[L]]`, for `π` a uniformizer of `K₀`, `n : ℕ`, `t : K₀`, there is `z : L₀` with
  `Algebra.norm K₀ (1 + π^{n+1}•z) ≡ 1 + π^{n+1}·t (mod π^{n+2})`. This is the step-3 sketch's
  "step 2's counterpart at each filtration level," made concrete and iterable: given `N(x) ≡ y
  (mod π^{n+1})`, writing the error as `y·N(x)⁻¹ = 1 + π^{n+1}·t`, this `z` gives `x' :=
  x·(1+π^{n+1}•z)` with `N(x') ≡ y (mod π^{n+2})` — one filtration level closer. Proved by
  composing `Algebra.trace_surjective` on the residue-field extension `𝓀[L]/𝓀[K]` (Mathlib,
  `Mathlib.RingTheory.Trace.Basic`, confirmed by loogle — needs `FiniteDimensional`/
  `Algebra.IsSeparable`, both derived from `[Finite 𝓀[L]]`: `𝓀[K]` is finite too, by injectivity of
  `algebraMap 𝓀[K] 𝓀[L]` [`Finite.of_injective`], giving `PerfectField 𝓀[K]`
  [`PerfectField.ofFinite`] and hence `Algebra.IsSeparable 𝓀[K] 𝓀[L]` via Mathlib's general
  `Algebra.IsAlgebraic.isSeparable_of_perfectField` instance, and `Module.Finite`/
  `Algebra.IsAlgebraic` via the general `Module.Finite.of_finite` instance for any module that is
  itself a finite type) with `IsLocalRing.residue_surjective` (lift the trace-preimage to `L₀`)
  and this session's `exists_norm_one_add_uniformizer_pow_smul_eq_trace_add` (seventh pass).
- **New file `NormMapContinuity.lean`** (commit `72871b5`): `continuous_norm_adicCompletion` —
  `Algebra.norm (v.adicCompletion K) : w.adicCompletion L → v.adicCompletion K` (the norm
  underlying `localNormMap`) is continuous. **This directly answers the task brief's flagged
  concern that continuity of the norm on a finite extension of complete valued fields might be "a
  genuine wall in Mathlib infrastructure" — it is not.** The proof composes three pre-existing
  general Mathlib facts — `LinearMap.continuous_of_finiteDimensional` (any linear map out of a
  finite-dimensional space over a complete nontrivially normed field is continuous),
  `Continuous.matrix_det` (`Mathlib.Topology.Instances.Matrix`), and `Algebra.norm_eq_matrix_det`
  — against typeclass instances that were *already sitting in `NormMap.lean`* for the unrelated
  purpose of building `localNormMap` itself: `instNontriviallyNormedFieldAdicCompletion` (giving
  both completions `NontriviallyNormedField` structure), the `ContinuousSMul`/`Module.Finite`
  instances for `w.adicCompletion L` over `v.adicCompletion K`, and `CompleteSpace (v.adicCompletion
  K)` (Mathlib, `Mathlib.RingTheory.DedekindDomain.AdicValuation:731`, generic in the Dedekind
  domain/fraction field/place triple, so it specializes to `v.adicCompletion K` for free — no new
  instance needed for that side either). No new instance and no new general lemma was required;
  this took one file, roughly 70 lines, and closed in the first attempt once the right three
  Mathlib names were located.
- **What remains for the full unramified norm-group theorem, precisely.** The sixth pass's step 3
  sketch has three parts: (1) construct the sequence `x₁, x₂, …` by iterating the one-step
  correction; (2) show it is Cauchy in the `𝔪_L`-adic topology; (3) take the limit (using
  `CompleteSpace (adicCompletion L w)` — confirmed to exist as a Mathlib instance, generic in the
  same way as the `K`-side one cited above, so no gap there either) and show the limit is a unit of
  `L₀` with norm exactly `y`, using `continuous_norm_adicCompletion` above. **None of (1)-(3) is
  built.** This is not a landscape gap the way prior passes' missing primitives were — every
  ingredient this session went looking for (`Algebra.trace_surjective`, finiteness transfer for
  residue fields, continuity of the norm, completeness of both adic completions) turned out to
  already exist or compose in one file's worth of work. What remains is the construction itself:
  packaging `exists_one_add_uniformizer_pow_smul_norm_sub_mem` into an actual recursively-defined
  sequence `x : ℕ → L₀ˣ` (needs `Nat.rec`/strong recursion with choice, since each step's witness
  `z` is only known to exist, not computed), proving the resulting sequence is Cauchy via
  `Valued.hasBasis_uniformity` + `Filter.HasBasis.cauchySeq_iff` (both confirmed present in
  Mathlib, per the task brief; not independently re-verified this session since no code reached
  that point), and the final limit/continuity argument connecting the sequence's limit back to
  `localNormMap` (not just the ring-level `Algebra.norm`) via this session's
  `localNormMap_coe_one_add_uniformizer_pow_smul` and the fifth pass's
  `algebraMap_norm_eq_norm_algebraMap`. This is genuine Lean engineering — bookkeeping-heavy
  (tracking `π`-adic valuations of the error term through a multiplicative recursion) rather than
  requiring new mathematical facts — comparable in size to what `UnitGroupModPrincipalUnitsSurjective.lean`
  (sixth pass) or `NormTraceLinearization.lean` (seventh pass) took, not a short lemma, but with no
  outstanding "is this even true in Mathlib" question left open going in.
- **Next concrete step for whoever picks this up:** build the sequence via well-founded/strong
  recursion producing, for each `n`, `x n : L₀ˣ` and a proof `Algebra.norm K₀ (x n : L₀) - y ∈
  Ideal.span {π^(n+1)}` (start from `localNormMap_units_surjective_mod_principalUnits`'s witness
  for `n = 0`, using `exists_one_add_uniformizer_pow_smul_norm_sub_mem` for the step from `n` to
  `n+1`), then prove `CauchySeq (fun n => (x n : w.adicCompletion L))` from the same valuation
  bound, then close with `cauchySeq_tendsto_of_complete` and `continuous_norm_adicCompletion`.

#### Status 2026-08-05 (ninth pass) — full unramified norm-group surjectivity CLOSED: `N_{L/K}(L^×) ⊇ O_K^×`

- **New file `langlands/Langlands/UnramifiedNormSurjective.lean`** (commits `a21df52`, `4e1ac36`),
  zero `sorry`, full `lake build` green (8670 jobs; `grep -rn sorry langlands/Langlands/` empty).
  Same-session continuation of the eighth pass, pushed through to completion at a peer session's
  request rather than stopping at the eighth pass's documented scoping point — the blocker that
  pass flagged as "genuine Lean engineering, not a landscape gap" turned out to be exactly that:
  no new mathematical fact was needed anywhere in this pass, only assembling what the eighth pass
  had already confirmed exists.
- **The main theorem:** `exists_isUnit_algebraMap_norm_eq_of_isUnramified` (`:309`) — under
  `IsUnramified K L v w`, for every unit `y : K₀`, there is a unit `x : L₀` with `Algebra.norm K₀ x
  = y` exactly. This is `N_{L/K}(L^×) ⊇ O_K^×`, the surjectivity core of the classical unramified
  norm-group theorem (the "easy half" of local CFT, Serre Ch. V §2-3) — the milestone the original
  Phase 2a scoping (top of this section) set out to reach.
- **Route, in order:**
  1. `exists_isUnit_norm_residue_eq` (`:67`) — the base case, `residue K₀ (N x₀) = residue K₀ y`
     for some unit `x₀ : L₀`, built directly from `residueField_units_norm_surjective`
     (`Langlands.ResidueFieldNorm`) and `surjective_units_map_residue`
     (`Langlands.UnitGroupModPrincipalUnitsSurjective`) composed through
     `residue_norm_eq_norm_residue_of_isUnramified` (`Langlands.NormMapResidueCompatibility`,
     fifth pass) — **bypassing `localNormMap` entirely**, a simplification not anticipated in the
     eighth pass's writeup (which expected to route the base case through
     `localNormMap_units_surjective_mod_principalUnits`); working at the ring level throughout
     turned out to need one fewer bridging layer.
  2. `exists_isUnit_mul_one_add_uniformizer_eq` (`:83`) and
     `exists_uniformizer_pow_smul_mul_one_add_uniformizer_pow_succ_eq` (`:118`) restate the base
     case and the eighth pass's one-step correction
     (`exists_one_add_uniformizer_pow_smul_norm_sub_mem`,
     `Langlands.PrincipalUnitsCauchySequence`) as an **exact multiplicative invariant** `y =
     Algebra.norm K₀ x · (1 + π^{n+1}·t)` (rather than the additive `mod π^{n+1}` congruence the
     eighth pass's writeup sketched) — the multiplicative form is what makes the induction close
     exactly rather than only up to higher-order terms, and what makes `approxUnit (n+1) =
     approxUnit n · (1 + π^{n+1} • z)` hold *definitionally*, not just propositionally, which the
     Cauchy bound (step 4 below) needs. Each step's algebra was closed via `linear_combination`
     with hand-derived coefficients (not `ring`/`field_simp` directly, since `K₀`/`L₀` are only
     commutative rings, not fields — inverses are tracked via `IsUnit.exists_right_inv` witnesses,
     not `⁻¹`).
  3. `approxData`/`approxUnit`/`approxError` (`:150`-`:180`) — the successive-approximation
     sequence itself, built by structural recursion on `ℕ` returning a dependent `Subtype` (motive
     `fun n => {p // IsUnit p.1 ∧ y = N p.1 · (1+π^{n+1}·p.2)}`), choosing witnesses via
     `Exists.choose` at each step. Exposing the correction witness `z` *inside* the recursive
     definition (rather than only asserting its existence abstractly) was the key design choice —
     it makes `approxUnit_succ_eq` (`:193`, `approxUnit (n+1) = approxUnit n · (1+π^{n+1}•z)` for
     some `z`) provable by `rfl`, with no separate uniqueness/reconstruction argument needed to
     recover the step relationship from the abstract existence statement.
  4. `cauchySeq_approxUnit` (`:233`) — Cauchy-ness, via the **`NontriviallyNormedField`
     structure already built in `Langlands.NormMap`** (`instNontriviallyNormedFieldAdicCompletion`,
     confirmed to have `toUniformSpace := Valued.toUniformSpace` literally, i.e. no topology
     diamond against the `Valued`-based instances the rest of Phase 2a uses) rather than the
     `Valued.hasBasis_uniformity`/`Filter.HasBasis.cauchySeq_iff` route the task brief suggested —
     `cauchySeq_of_le_geometric` (`Mathlib.Analysis.SpecificLimits.Basic`) applies directly once
     consecutive differences are bounded by `‖algebraMap π‖^{n+1}` (both `x_n`, `z_n` having norm
     `≤ 1`, being elements of `L₀`; `‖algebraMap π‖ < 1` since `π` is a non-unit, via
     `Valuation.mem_maximalIdeal_iff`). This substitution of the metric-space route for the
     valuation-basis route the eighth pass's writeup anticipated turned out to be strictly less
     work, since the `NormedField` machinery was already sitting in `NormMap.lean` for unrelated
     reasons (the same discovery pattern as `NormMapContinuity.lean`'s continuity lemma).
  5. `norm_approxUnit_eq_one` (`:266`) — every `approxUnit n` has norm exactly `1` (not just `≤
     1`): its inverse, also a unit of `L₀`, has norm `≤ 1` too, giving `‖approxUnit n‖ ≥ 1` via
     `mul_le_of_le_one_right`.
  6. The main theorem (`:309`) assembles the rest: `cauchySeq_tendsto_of_complete` (using
     `CompleteSpace (w.adicCompletion L)`, confirmed to exist as the same generic Mathlib instance
     `CompleteSpace (v.adicCompletion K)` specializes from, `Mathlib.RingTheory.DedekindDomain.
     AdicValuation:731` — no gap on the `L`-side either, exactly as the eighth pass predicted)
     gives a limit `xL`; continuity of `‖·‖` plus (5) forces `‖xL‖ = 1` (via `tendsto_nhds_unique`
     against the constant-`1` sequence), hence `xL ∈ L₀` and `IsUnit xL` in `L₀`
     (`adicCompletionIntegers.isUnit_iff_valued_eq_one`, found by loogle, not anticipated in the
     eighth pass's writeup); pushing the exact invariant `y = N(x_n)·(1+π^{n+1}·t_n)` through
     `algebraMap K₀ (v.adicCompletion K)` and taking `n → ∞` (the error term `π^{n+1}·t_n → 0` via
     `squeeze_zero_norm` + `tendsto_pow_atTop_nhds_zero_of_lt_one`, and `N(x_n) → N(xL)` via
     `continuous_norm_adicCompletion`, `Langlands.NormMapContinuity`, composed with `hxL`) gives
     `algebraMap y = algebraMap (N xL)` by `tendsto_nhds_unique`, hence `y = N(xL)` by injectivity
     of `algebraMap K₀ (v.adicCompletion K)` (`Subtype.coe_injective`).
- **What this does and does not close.** This closes `N_{L/K}(L^×) ⊇ O_K^×` (surjectivity onto
  units), the scoped stopping point of the original Phase 2a milestone. It does **not** close the
  full classical statement `N_{L/K}(L^×) = ⟨π⟩^n·O_K^×` — the reverse inclusion `⊆` and the
  `⟨π⟩^n` factor tracking the valuation/uniformizer part of the norm image are untouched; those are
  comparatively routine (the reverse inclusion is essentially "the norm of any element has the
  expected valuation," and `π` itself is visibly a norm since `L/K` is unramified — `N_{L/K}(π) =
  π^n` up to a unit, by the standard unramified-extension norm-of-uniformizer computation) but were
  not attempted this session, the task having been scoped to surjectivity.
- **No genuine Mathlib wall was hit anywhere in this pass.** Every fact the eighth pass flagged as
  needed (`Valued.hasBasis_uniformity`/`Filter.HasBasis.cauchySeq_iff`, `CompleteSpace
  (w.adicCompletion L)`) either existed as anticipated or was superseded by a simpler pre-existing
  route (`NontriviallyNormedField`/`cauchySeq_of_le_geometric` in place of the valuation-basis
  approach). The entire session was proof engineering — correct bookkeeping of a multiplicative
  Hensel-lift recursion and its limit — not lemma discovery.

#### Status 2026-08-05 (tenth pass) — full Phase 2a statement CLOSED: `N_{L/K}(L^×) = ⟨π⟩^n · O_K^×`

- **New file `langlands/Langlands/UnramifiedNormRange.lean`** (commit `d5ec480`), zero `sorry`,
  full `lake build` green (8670 jobs; `grep -rn sorry langlands/Langlands/` empty). Not yet in
  `Langlands.lean`'s import list, consistent with the rest of Phase 2a's files.
- **Re-derived from the actual math first, per the task's brief, rather than trusting the ninth
  pass's "comparatively routine" hedge in either direction.** The route sketched there (every
  nonzero element of `L_w` is `(uniformizer)^k · unit`, since `L₀` is a DVR) turned out to be
  exactly right and to close with no new mathematical content — every ingredient needed either
  already existed in Mathlib or was already sitting in this repo's earlier Phase 2a files.
- **The main theorem:** `localNormMap_range_eq` (`UnramifiedNormRange.lean:275`) — under
  `IsUnramified K L v w` and `Irreducible π` (`π` a uniformizer of `K₀`),
  ```
  MonoidHom.range (localNormMap K L v w) =
    Subgroup.zpowers (uniformizerUnit v hπ ^ n) ⊔ (v.adicCompletionIntegers K).units
  ```
  as an equality of subgroups of `(v.adicCompletion K)ˣ`, where `n := Module.finrank
  (v.adicCompletion K) (w.adicCompletion L)` (the local degree `[L_w : K_v]`, which — since
  `L/K` is unramified — is the residue degree) and `uniformizerUnit v hπ : (v.adicCompletion K)ˣ`
  is the unit corresponding to (the image of) `π`. This is the full classical statement
  `N_{L/K}(L^×) = ⟨π⟩^n · O_K^×` (Serre, *Local Fields*, Ch. V §2-3), stated at the level of
  `localNormMap`'s actual codomain (`(v.adicCompletion K)ˣ`, i.e. `K_v^×`) rather than invented
  vocabulary — `⟨π⟩^n` is `Subgroup.zpowers`, `O_K^×` is the pre-existing
  `(v.adicCompletionIntegers K).units` (`Submonoid.units`, already used throughout `NormMap.lean`),
  and the sup of two subgroups of an abelian group is exactly the pointwise product
  (`Subgroup.mem_sup`) — no new statement-shape vocabulary was invented, matching the task's
  instruction to prefer existing Mathlib idiom over hand-rolled shapes.
- **Route, in order:**
  1. `algebraMap_uniformizer_irreducible` (`:71`) — under `IsUnramified`, the image of `π` in `L₀`
     is itself irreducible, i.e. a uniformizer of `L₀`: `IsUnramified` says `𝔪_K·L₀ = 𝔪_L`, and
     `𝔪_K = (π)` (`Irreducible.maximalIdeal_eq`, Mathlib), so `𝔪_L = (algebraMap π)`
     (`Ideal.map_span`/`Set.image_singleton`), which is exactly
     `IsDiscreteValuationRing.irreducible_iff_uniformizer` (Mathlib) read backwards. This closes
     the task brief's "does `π` remain a uniformizer of `L₀`" question definitively yes, formally.
  2. **The `π^k · unit` decomposition** (`exists_zpow_mul_unit_eq`, `:139`) — the task brief's
     "plausible route", verified and built exactly as sketched: `IsDiscreteValuationRing.
     associated_pow_irreducible` (confirmed present in Mathlib by loogle, `Mathlib.RingTheory.
     DiscreteValuationRing.Basic`; every nonzero element of a DVR is associated to a power of a
     fixed irreducible) gives the decomposition for `n : ℕ` directly when a unit `a` of
     `w.adicCompletion L` already lies in `L₀` (`Valued.v a ≤ 1`); applying it to `a⁻¹` instead and
     inverting (`inv_le_one_of_one_le₀`, `mul_inv`, `zpow_neg`/`zpow_natCast`) extends the exponent
     to `k : ℤ` for the general case. **`IsDiscreteValuationRing (w.adicCompletionIntegers L)` and
     `(v.adicCompletionIntegers K)` are unconditional Mathlib instances** (`Mathlib.NumberTheory.
     NumberField.Completion.FinitePlace`, generic in the Dedekind-domain/fraction-field/place
     triple — not gated on any number-field-specific hypothesis, confirmed by reading the instance
     directly), so no new instance was needed for this either — resolving the task brief's
     "genuine gap, comparable to compatibility-square gaps" concern in the negative: this route hit
     no wall of that kind.
  3. `norm_algebraMap_uniformizer_eq` (`:168`) — `Algebra.norm (v.adicCompletion K)` of (the `L₀`-
     route image of) `π` is exactly `π^n`, via Mathlib's `Algebra.norm_algebraMap`
     (`Algebra.norm R (algebraMap R S x) = x ^ Module.finrank R S`, confirmed present by loogle,
     one query) applied directly **at the field level** (`R := v.adicCompletion K`, `S :=
     w.adicCompletion L`), using `Langlands.ResidueFieldNorm.coe_algebraMap_adicCompletionIntegers`
     (already proved by `rfl` in an earlier pass) to identify the `L₀`-route image of `π` with the
     `adicCompletionComap`/`K_v`-route image `Algebra.norm_algebraMap` is stated for. **This
     resolves the task brief's flagged uncertainty about which "`n`" is correct** (ring-level
     `Module.finrank K₀ L₀` vs. field-level `Module.finrank K_v L_w`) by sidestepping it entirely:
     working at the field level from the start means only the field-level `n` — the natural one
     for a statement about `localNormMap`'s codomain — ever appears; no comparison lemma between
     the two `finrank`s was needed anywhere.
  4. `localNormMap_range_le` (`:253`) — the reverse inclusion, combining (2) and (3) with the
     pre-existing `localNormMap_mem_units` (`Langlands.NormMap`, norm of a local unit of `L₀` is a
     local unit of `K₀`): decompose a preimage `a = ϖ^k · u`, push through `localNormMap`
     (`Units.map`, so `map_mul`/`map_zpow` apply directly, being a genuine group hom on unit
     groups — this is why the file works with `Units.map`-embedded elements throughout rather than
     raw ring elements, sidestepping all `0`/inverse case-splitting that a `MonoidHom` on the full
     ring (rather than its unit group) would have required), and land in the claimed sup via
     `Subgroup.mem_sup`.
  5. `localNormMap_range_eq` (`:275`) combines (4) with the reverse direction: `uniformizerUnit^n`
     is itself `localNormMap` of the uniformizer unit (from (3), transported to `Units.map` form by
     `Units.ext`), and every element of `(v.adicCompletionIntegers K).units` is a norm by the ninth
     pass's `exists_isUnit_algebraMap_norm_eq_of_isUnramified`.
- **No genuine gap was hit anywhere in this pass** — every ingredient the task brief flagged as
  uncertain (the `π^k · unit` decomposition's existence in Mathlib for this specific setup, which
  `finrank` is the right `n`, whether `π` remains a uniformizer of `L₀`) resolved cleanly using
  Mathlib facts confirmed by loogle plus results already sitting in this repo's earlier Phase 2a
  files. The only friction was ordinary Lean bookkeeping — `algebraMap` vs. plain-coercion
  syntactic mismatches in `rw`/`rfl` steps (several instances, all resolved by matching the
  notation style already used at each call site) and getting unit-vs-ring-element type ascriptions
  right for `Inv`/`Units.map` — not any new mathematical or landscape gap.
- **Milestone assessment.** Phase 2a's originally-scoped goal (top of this section, "the easy
  half of local CFT") is now **fully closed**: `N_{L/K}(L^×) = ⟨π⟩^n · O_K^×` for `L/K` unramified,
  proved end to end from the `IsUnramified` hypothesis with zero `sorry`. This is a genuine
  milestone completion, not an incremental step — it is the first full classical theorem-statement
  (as opposed to a supporting lemma or a one-directional inclusion) this repo's Phase 2a work has
  closed. What it does *not* do: it says nothing about the *ramified* case (Phase 2's actual hard
  content — Lubin–Tate theory, the reciprocity map itself) or about assembling this single-place
  statement into a global/idelic norm-group statement (`NormMap.lean`'s idèle norm map exists, but
  connecting its image to a global class-field-theory statement is untouched). See Phase 2's
  section below for what's next.

### Phase 2b — Ramified local reciprocity: landscape and scoped candidates (2026-08-05, research/scoping pass, no code)

- **Why this exists.** Phase 2a closed the "easy half" of local CFT (unramified norm-group
  surjectivity) in full, across ten passes. This section applies the same before-you-build
  discipline to Phase 2's actual hard content — the ramified case and the reciprocity map itself —
  the way the original Phase 2a entry (top of this file) scoped a smaller first cut before any
  ramified-case proof code was written. **No `.lean` files were touched this pass**; this is a pure
  research/scoping session, per its own brief.
- **What full local Artin reciprocity for ramified extensions requires, mathematically.** Two
  established routes exist in the literature, and neither is a small extension of what Phase 2a
  built:
  1. **Lubin–Tate formal groups.** Attach a formal group law to a choice of uniformizer of `K`,
     generate totally ramified abelian extensions of `K` by adjoining its torsion points, and
     identify the reciprocity map directly via the action on torsion points (this is the
     constructive route — it builds the abelian extensions and the map simultaneously, rather than
     proving an abstract isomorphism exists).
  2. **The cohomological/class-formation route** (the route the roadmap's original Phase 2 sizing,
     "comparable to Serre Ch. VIII–XIII," already presumed): Tate's theorem that
     `H²(Gal(L/K), L^×)` is cyclic of order `[L:K]`, generated by a local fundamental class, fed
     into the abstract class-formation machinery (Herbrand quotients, the local Artin map built
     from the fundamental class via cup product) to produce the reciprocity isomorphism
     `K^×/N_{L/K}(L^×) ≅ Gal(L/K)^{ab}` without explicitly constructing extensions.
  Both are needed in full generality for the complete statement; Lubin–Tate is usually the more
  direct route to the totally-ramified case specifically, with the cohomological route handling the
  general (mixed ramified/unramified) case uniformly.
- **Mathlib landscape, checked fresh this pass (loogle + grep against vendored Mathlib, commit
  unchanged since prior passes per `flake.lock`):**
  - **Lubin–Tate theory: absent entirely.** `grep -rli "Lubin"` over vendored Mathlib returns
    nothing. `Mathlib/RingTheory/FormalGroup/Basic.lean` has a generic 1-dimensional `FormalGroup R`
    over a commutative ring with additive/multiplicative examples and a `Point` construction, but
    nothing Lubin–Tate-specific (no formal group attached to a uniformizer, no torsion-point
    construction, no Lubin–Tate character) — this would need to be built essentially from scratch
    on top of the generic formal-group scaffolding.
  - **The cohomological/fundamental-class route: also absent.** `grep -rli
    "fundamentalClass\|fundamental class"` and `grep -rli "herbrand"` both return nothing — no local
    fundamental class, no Herbrand quotient, no Tate's theorem on `H²(Gal(L/K), L^×)`. Generic
    machinery is present and reusable as scaffolding only: `H2`/`H2π` for an arbitrary `k[G]`-module
    (`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean:1031-1082`), Hilbert 90
    (`GroupCohomology/Hilbert90.lean`, already cited), and Tate cohomology
    (`GroupCohomology/TateCohomology/Basic.lean`) — none specialized to Galois cohomology of `L^×`,
    none carrying an invariant map or local-fundamental-class statement.
  - **Higher ramification groups: explicitly incomplete in Mathlib itself.**
    `grep -rli "ramification group\|higher ramification\|lowerNumbering\|upperNumbering"` finds
    exactly one file, `Mathlib/RingTheory/Valuation/RamificationGroup.lean`. Read in full: it
    defines only `decompositionSubgroup` and `inertiaSubgroup` (the ramification group at index 0)
    — its own header comment states `TODO: Define higher ramification groups in lower numbering`.
    No upper numbering, no Herbrand's theorem on either side.
  - **Eisenstein polynomials exist, unconnected to this repo.**
    `Mathlib/RingTheory/Polynomial/Eisenstein/{Basic,IsIntegral}.lean` has `IsWeaklyEisensteinAt`,
    `IsEisensteinAt`, irreducibility/integrality lemmas, stated generically over `R[X]` and an ideal
    — real, usable primitives for presenting a totally-ramified uniformizer, but `grep -rli
    "Eisenstein" langlands/Langlands/` returns nothing: no existing bridge to
    `adicCompletionIntegers` in this repo.
  - **Different/discriminant machinery** (`Mathlib/RingTheory/DedekindDomain/Different.lean`,
    already cited in §1.1) is substantial and general (`differentIdeal`, `not_dvd_differentIdeal_iff`
    unramified-characterization, transitivity under towers) but not yet wired to anything in this
    repo's `adicCompletion` setting either.
- **What Phase 2a's own infrastructure already generalizes to the ramified case (checked by reading
  both files in full, not by inference from names).** `Langlands/AdicCompletionIntegralClosure.lean`
  and `Langlands/UnramifiedValuationExtension.lean` — the `Module.Finite`/`Module.Free`/
  `IsIntegralClosure` scaffolding for `w.adicCompletionIntegers L` over `v.adicCompletionIntegers K`,
  and the `IsUnramified` predicate itself — carry **no unramified-specific hypothesis anywhere**.
  Every declaration in both files is stated for a generic finite (separable) extension; `IsUnramified`
  is defined as `𝔪_K·O_L = 𝔪_L` precisely so the ramified case is the negation (or, with
  `Ideal.ramificationIdx'`, `e > 1`), and `UnramifiedValuationExtension.lean`'s own docstring notes
  the `≤` containment it proves holds unconditionally, for any extension. **This means any
  ramified-case milestone gets the finite/free module scaffolding for free — it does not need to be
  rebuilt.** What is genuinely unramified-specific and does *not* transfer is everything built on top
  of it in the later Phase 2a passes (`ResidueFieldNorm.lean`'s reliance on `FiniteField.norm_surjective`,
  the principal-units filtration argument, the Cauchy-sequence assembly) — those all use, essentially,
  that the residue extension is nontrivial and the ramification index is 1, which is exactly what
  breaks in the ramified case.
- **Duplication re-check against kbuzzard/ClassFieldTheory (`github.com/kbuzzard/ClassFieldTheory`),
  re-verified fresh this pass, focused specifically on the ramified case (general local CFT there was
  already known to be in-flight via cohomology as of the prior TODO.md entry).** Actively developed
  (`pushed_at` 2026-08-03, commits within days of this check). The unramified-case cohomological
  machinery there is sorry-free (`LocalCFT/{Continuity,Teichmuller}.lean`, `Cohomology/LocalInv.lean`,
  `IsNonarchimedeanLocalField/Unramified.lean`); `UnramifiedCohomology.lean` has one remaining `sorry`.
  The *general* (including ramified) reciprocity theorem exists only as an unformalized blueprint
  statement — `thm:local fund class` in `blueprint/src/_3_local.tex`, `Gal(l/k) ≅ k^×/N(l^×)` for
  arbitrary finite Galois `l/k`, with a full paper-style proof sketch (Hilbert 90 + `H²`
  order-bound) but **no `\lean{}`/`\leanok` tag** — not yet connected to any Lean code. GitHub code
  search (`gh api search/code`, authenticated) across the full repo returns **zero** hits for
  "Lubin-Tate", "LubinTate", "Weil group", "WeilGroup", "formal group". "Totally ramified" appears
  only as a bare `todo: totally ramified` comment in `IsNonarchimedeanLocalField/RamificationInertia.lean`
  — no code, no lemma, no blueprint entry. **Conclusion: no construction-level duplication.** The two
  projects' routes to ramified local CFT are disjoint (Weil group vs. Tate cohomology/class
  formations), and neither project currently has ramified-case content beyond a TODO placeholder.
  Worth flagging as a *strategic*, not technical, consideration for whoever continues: kbuzzard's
  project is more actively staffed and its cohomological infrastructure is further along, so it may
  reach general local CFT (via the cohomological route) before this project's Weil-group route does
  — this does not make pursuing the Weil-group route here wasted (the constructions genuinely differ
  and both are independently valuable/upstreamable), but it is a live consideration, not a settled one.
- **Scoped first-milestone candidates (tradeoffs, not a recommendation — a genuinely open call for
  whoever picks this up).**
  1. **Higher ramification groups (lower numbering), for finite Galois extensions of adic
     completions.** Extend Mathlib's own `RamificationGroup.lean` (which stops at index 0 —
     decomposition/inertia — with an explicit upstream TODO for higher numbering) by defining
     `G_i := {σ ∈ Gal(L/K) : σ acts trivially on O_L/𝔪_L^{i+1}}` (equivalently, a valuation-gap
     condition on `σ(π_L) - π_L`), reusing `AdicCompletionIntegralClosure.lean`'s already-general
     `Module.Free`/`IsIntegralClosure` machinery to make the quotient action well-defined. **Why
     attemptable:** bounded scope (a filtration plus basic monotonicity/`G_0 = inertia` identification
     lemmas), reuses existing general infrastructure with zero modification, and fills a gap Mathlib
     itself flags as open — genuinely upstream-worthy on its own, independent of whether this
     project's Weil-group route to reciprocity ever completes. It is also a real prerequisite for
     *both* Lubin–Tate (conductor/different computations use the filtration) and the cohomological
     route (compatibility of local CFT under subfields uses it too). **Caveat:** unlike every closed
     Phase 2a milestone, this produces infrastructure/definitions plus basic lemmas, not a closed
     classical theorem-statement — whoever picks it up should treat that as a real difference in
     kind, not assume it reads the same as "another Phase 2a."
  2. **Totally ramified extension norm-group computation** — the "other half" of Serre's
     unramified-times-totally-ramified tower decomposition, the standard way the general ramified
     case is built up. Define `IsTotallyRamified` (trivial residue extension, `e = [L:K]`), and
     attempt the analogous norm-image statement for totally ramified `L/K`, presumably via an
     Eisenstein-polynomial presentation of a uniformizer of `L₀` (Mathlib's `IsEisensteinAt` API
     exists but has zero existing bridge to `adicCompletionIntegers` here) combined with
     `AdicCompletionIntegralClosure.lean`'s reusable scaffolding. **Honest caveat, stated up front
     rather than discovered three sessions in the way Phase 2a's compatibility square was:** this is
     *not* structurally parallel to Phase 2a despite looking that way at a glance. Phase 2a's whole
     argument worked by reducing to a **residue-field** fact (`FiniteField.norm_surjective`) and then
     lifting through the principal-units filtration via norm-linearizes-to-trace. In the totally
     ramified case the residue extension is trivial (`𝓀[L] = 𝓀[K]`), so that entire lever is gone —
     the totally-ramified norm computation is governed by different mechanics entirely (essentially
     reading off the norm from the Eisenstein minimal polynomial's coefficients directly). This is
     genuinely new mathematical content, not a recomposition of Phase 2a's existing pieces, and its
     size relative to Phase 2a's ten-pass arc is unknown rather than "probably smaller."
  **Tradeoff, stated plainly for whoever chooses:** candidate 1 is smaller, more certain to close in
  bounded time, and independently upstream-worthy, but does not produce a citable closed theorem the
  way Phase 2a's milestone did. Candidate 2 is the more natural "next chapter" in the classical proof
  strategy and would produce a closed theorem if it succeeds, but its size is genuinely unknown and
  the technique that made Phase 2a tractable does not transfer to it — starting it expecting a
  Phase-2a-shaped quick win would be a mistake. Neither was attempted this pass, per its scope-only
  brief.

#### Status 2026-08-05 (eleventh pass) — candidate 1 (higher ramification groups) CLOSED

- **What got built.** `langlands/Langlands/RamificationFiltration.lean` (commit `6bdd1eb`) closes
  Mathlib's own stated `TODO: Define higher ramification groups in lower numbering` in
  `Mathlib/RingTheory/Valuation/RamificationGroup.lean`, in the same generality as that file (`K L`
  fields, `[Algebra K L]`, `A : ValuationSubring L`) rather than specialized to this repo's
  adic-completion setup. Defines `ValuationSubring.ramificationGroup K A i : Subgroup
  (A.decompositionSubgroup K)`, Serre's `G_i` for `i : ℕ`, index-shifted by one relative to Serre
  since `D`/`I` already exist as `decompositionSubgroup`/`inertiaSubgroup` and don't need
  redefining (documented explicitly in the file's module docstring). Proves:
  - `mem_maximalIdeal_smul_iff` / `smul_mem_pow_maximalIdeal` (`RamificationFiltration.lean:72,87`):
    the decomposition-subgroup action fixes `𝔪_A` and its powers setwise — the ingredient needed to
    show `ramificationGroup` is actually a subgroup.
  - `ramificationGroup_succ_le` (`:128`): the filtration is decreasing, `G_{i+1} ≤ G_i`.
  - `ramificationGroup_zero` (`:136`): `ramificationGroup K A 0 = A.inertiaSubgroup K`, the sanity
    check that the indexing convention matches Serre's classical `G_0 = I`.
  - `ramificationGroup_normal` (`:161`): each `G_i` is normal in the **full** decomposition group
    `A.decompositionSubgroup K`, stronger than the classically-stated `G_i ⊴ G_0` — this fell out
    directly from the same maximal-ideal-invariance lemma used for the subgroup structure, with no
    extra hypothesis on the conjugating element needed, so it was proved in the strong form rather
    than the weaker one originally anticipated.
  `langlands/Langlands/RamificationFiltrationAdicCompletion.lean` (commit `6cfbb96`) adds the thin
  adic-completion specialization requested alongside it: `IsDedekindDomain.HeightOneSpectrum.
  ramificationGroup`, instantiating the general definition at `A := w.adicCompletionIntegers L`
  over `v.adicCompletion K`, using the `R S K L v w` variable block from
  `AdicCompletionIntegralClosure.lean`/`UnramifiedValuationExtension.lean`. Pure instantiation, no
  new mathematical content. Both files: zero `sorry`, `lake build Langlands` green (re-verified
  2026-08-05, 8675 jobs).
- **What's left open, and why.** The "eventually trivial" finiteness fact (`∃ N, G_N = ⊥`) was not
  attempted — its standard proof needs the associated-graded injections `G_i/G_{i+1} ↪
  𝔪_A^i/𝔪_A^{i+1}` (or the multiplicative variant for `i = 0`), machinery beyond this pass's scope;
  documented in the file's own module docstring rather than left as a `sorry`. The stretch-goal
  structure theorems (`G_0/G_1` embeds in the residue field's multiplicative group, `G_i/G_{i+1}`
  embeds additively for `i ≥ 1`) were not attempted, same reason. A corollary considered for the
  adic-completion file — "Galois `⟹` `decompositionSubgroup = ⊤`", paralleling `Langlands.NormMap`'s
  `hAfix` pattern via `LocalField.valuationSubring_eq_of_comap_eq` — was scoped but not attempted:
  it needs a `CompleteSpace`/`NontriviallyNormedField`/`IsUltrametricDist` instance chain (or
  `IsNonarchimedeanLocalField`) on `v.adicCompletion K` not present in the general `R S K L v w`
  block used throughout `AdicCompletionIntegralClosure.lean`; supplying it is new scope, not a
  by-product of what this pass built. Flagged as a Mathlib upstreaming candidate in `TODO.md` (it
  closes Mathlib's own stated gap, in Mathlib's own generality).
- **Candidate 2 (totally ramified norm-group computation) remains untouched**, per the tradeoff
  stated above — this pass only closed candidate 1.

#### Status 2026-08-05 (twelfth pass) — `decompositionSubgroup = ⊤` for adic completions CLOSED; associated-graded embeddings blocked and documented

- **What got built.** `langlands/Langlands/RamificationFiltrationAdicCompletion.lean` (commit
  `163c755`) adds `IsDedekindDomain.HeightOneSpectrum.decompositionSubgroup_eq_top`: for the
  `R S K L v w` variable block already in use in that file, `(w.adicCompletionIntegers
  L).decompositionSubgroup (v.adicCompletion K) = ⊤`. This closes the corollary the eleventh pass
  scoped but didn't attempt — and turns out to need **no Galois/normality hypothesis at all**: the
  underlying fact is that every algebraic extension of a *complete* field has a unique valuation
  extension (`LocalField.valuationSubring_eq_of_comap_eq`, `Langlands.HenselianValuation`), so every
  `σ : (w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)` automatically stabilizes
  `w.adicCompletionIntegers L`, whether or not the extension is normal — exactly parallel to
  `LocalField.decompositionSubgroup_eq_top` in `Langlands.WeilGroup` (same fact for `L =
  AlgebraicClosure K`). The instance chain the eleventh pass thought was missing
  (`CompleteSpace`/`ValuativeRel`/`Compatible` on `v.adicCompletion K`) turned out to already exist
  in full, keyed to exactly this file's `R S K L v w` variable block, in `Langlands.NormMap`'s
  `RankOne` section (`instRankOneValuedAdicCompletion`, `instValuativeRelValuedAdicCompletion`, and
  the `Compatible` instances) plus its `Module.Finite (v.adicCompletion K) (w.adicCompletion L)`
  instance (`NormMap.lean:363`) and `adicCompletionIntegers_comap_eq`/
  `valuation_valuationSubring_eq_adicCompletionIntegers` (`NormMap.lean:409,424`) — importing
  `Langlands.NormMap` (no cycle: nothing under `RamificationFiltration` is imported transitively by
  it) was sufficient; no new instances had to be built. `lake build`: 8675 jobs, clean.
- **What's still blocked, and precisely why.** The associated-graded embeddings (`ramificationGroup
  i / ramificationGroup (i+1) ↪` residue-field data, for `i = 0` multiplicative and `i ≥ 1`
  additive) were attempted directly in the general `RamificationFiltration.lean` setting (a chosen
  uniformizer `π` with `hπ : maximalIdeal A = span {π}`). The homomorphism property was worked out
  and confirmed to hold (recorded in `RamificationFiltration.lean`'s docstring: the `i = 0` case is
  an exact computation via `Ideal.span_singleton_eq_span_singleton` needing no error-term estimate;
  the `i ≥ 1` case needs a generic commutative-ring divisibility identity, `(1+x)^{i+1} - 1 -
  (i+1)x` divisible by `x^2`, to bound the cross term). **The actual wall is proving the *kernel* of
  either map, restricted to `ramificationGroup K A i`, is *exactly* `ramificationGroup K A (i+1)`**
  — the `⊇` direction is free (test the defining `∀x` property at `x = π`), but `⊆` needs that a
  congruence checked only at the uniformizer `π` propagates to *all* `x ∈ A`, which classically uses
  monogenicity of the ring of integers over the inertia-fixed subfield (`O_L = O_{L_0}[π_L]` for a
  totally ramified extension of a complete DVR, via an Eisenstein-polynomial argument). Checked this
  pass: `grep -rli "monogenic\|PowerBasis"` over `Mathlib/RingTheory/Valuation/` and
  `Mathlib/RingTheory/DiscreteValuationRing/` is empty — **no such theorem exists in Mathlib**.
  Adding it as a hypothesis directly (rather than deriving it) would assume most of the content of
  the theorem being proved, not supply a narrow missing typeclass — so, per this project's
  stop-on-genuine-wall discipline, it was left undone and documented in
  `RamificationFiltration.lean`'s "## Scope" section rather than forced with an ad hoc hypothesis or
  a `sorry`. This also means the finiteness fact (step 2 of the original brief) and the
  eventually-trivial filtration remain out of reach, since both are built on the embeddings.
- **Candidate 2 (totally ramified norm-group computation) remains untouched.**

#### Status 2026-08-06 (thirteenth pass) — monogenicity for the totally ramified case: correct Mathlib route identified, precise remaining gap scoped, no code written

- **Task.** Attempt full monogenicity (`O_L = O_K[α]`) for finite extensions of complete DVRs with
  separable residue extension, per Serre's unramified-times-totally-ramified decomposition. The
  unramified half is already fully available:
  `Mathlib.RingTheory.LocalRing.Etale.IsLocalRing.exists_adjoin_eq_top` (general étale local rings,
  landed by the UW Math AI Lab) and this repo's `HenselianLocalRing.
  exists_isDiscreteValuationRing_integralClosure_residueField_equiv`
  (`Langlands/UnramifiedExtension.lean:715`, read in full this pass, no changes needed) construct
  the unramified subextension concretely. What was missing, per the twelfth pass's diagnosis in
  `RamificationFiltration.lean`, is the totally ramified half: `O_L = O_{L_0}[π_L]` for `π_L` a
  uniformizer, via an Eisenstein-polynomial argument.
- **Correction to the twelfth pass's diagnosis.** That pass's `grep -rli "monogenic\|PowerBasis"`
  over `Mathlib/RingTheory/Valuation/` and `Mathlib/RingTheory/DiscreteValuationRing/` (both empty)
  was accurate as far as it went, but searched the wrong directories: the relevant machinery lives
  in `Mathlib/RingTheory/Polynomial/Eisenstein/IsIntegral.lean` and
  `Mathlib/RingTheory/Discriminant.lean`, filed under Eisenstein polynomials and number-field
  ring-of-integers computations (its only current Mathlib caller is
  `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean`, for cyclotomic fields), not under
  `Valuation`/`DiscreteValuationRing` at all — general Dedekind-domain content, not
  valuation-ring-specific. Confirmed present this pass:
  - `Polynomial.IsEisensteinAt.irreducible` (`Eisenstein/Basic.lean:231`) — a primitive Eisenstein
    polynomial is irreducible, the standard criterion.
  - `Algebra.discr_mul_isIntegral_mem_adjoin` (`Discriminant.lean`) — for `B : PowerBasis K L` with
    `B.gen` integral over an integrally closed `R` with fraction field `K`, `L/K` finite separable:
    `Algebra.discr K B.basis • z ∈ R[B.gen]` for every `z : L` integral over `R`.
  - `Polynomial.IsEisensteinAt.mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt`
    (`Eisenstein/IsIntegral.lean:365`) — if `minpoly R B.gen` is Eisenstein at a prime `p` and
    `p ^ n • z ∈ R[B.gen]` for some `n`, then `z ∈ R[B.gen]` outright (by induction on `n`, peeling
    off one factor of `p` at a time via `mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt`).
  Composed: for `R` a DVR with uniformizer `p`, `discr K B.basis` is a nonzero element of `R`
  (nonzero by separability, in `R` by `IsIntegrallyClosed`), hence — `R` being a DVR — equal to
  `unit * p ^ n` for a unique `n` (the `p`-adic valuation of the discriminant); multiplying the
  discriminant lemma's conclusion by the unit's inverse turns it into `p ^ n • z ∈ R[B.gen]`, and
  the induction lemma then gives `z ∈ R[B.gen]` for *every* `z : L` integral over `R` — i.e.
  `Algebra.adjoin R {B.gen} = ⊤` as a subalgebra of the integral closure. This is a real,
  Mathlib-supported route to totally-ramified monogenicity that does **not** need topological
  completeness of `R` (the induction bottoms out after finitely many steps, bounded by `n = v_p(disc
  f)`; `R = ℤ` in the cyclotomic-field caller is not `p`-adically complete at all). The twelfth
  pass's docstring claim that the classical argument "needs completeness" is corrected by this: what
  needs Henselian/complete `K` is a different step (below), not this index-computation step itself.
- **What Henselian-ness is actually needed for.** The one fact this route does not hand over for
  free is Eisenstein-ness of `minpoly R π` itself, for `π` a chosen uniformizer of `O_L` in a totally
  ramified extension. Classically: writing `f = minpoly K π = ∏ (X - π_i)` over the splitting field,
  each coefficient `a_i` (`i < e = deg f`) is (up to sign) an elementary symmetric function of the
  conjugates `π_j`, and Eisenstein-ness needs `v(a_i) ≥ 1` for `i < e` and `v(a_0) = 1` exactly —
  which needs every conjugate `π_j` to have the *same* valuation as `π` itself. That equality of
  valuations across conjugates is exactly the "unique extension of the valuation to any algebraic
  extension of a Henselian field" fact this repo already has
  (`Langlands.HenselianValuation`/`LocalField.valuationSubring_eq_of_comap_eq`, used by
  `RamificationFiltrationAdicCompletion.lean`'s `decompositionSubgroup_eq_top`). This step —
  "uniformizer of a totally ramified extension of a Henselian DVR has Eisenstein minimal
  polynomial" — was not attempted this pass; it is the one piece of genuine new content standing
  between the existing infrastructure (Eisenstein/discriminant machinery above, plus this repo's
  Henselian-valuation uniqueness machinery) and a closed totally-ramified monogenicity theorem. It
  is a bounded, well-scoped statement (not "assume most of the theorem," unlike the hypothesis the
  twelfth pass declined to add) — a genuine next-step candidate, not a wall in the same sense as the
  twelfth pass's.
- **A second, independent check this pass: the discriminant-unit route does not apply to any
  ramified case.** `Langlands.MonogenicMaximalOrder`'s
  `Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly` (the tool driving the *unramified* half
  in `UnramifiedExtension.lean:715`) needs `IsUnit (aeval x (minpoly A x).derivative)`. For `x = π` a
  root of a degree-`e` Eisenstein-type polynomial with `e ≥ 2`, `v_L(f'(π)) = v_L(e) + (e-1) \cdot
  v_L(\pi) \geq e - 1 > 0` in the totally ramified normalization `v_L(π) = 1` (this is, up to a unit,
  the valuation of the different, which is classically positive exactly when the extension is
  ramified — trivial different characterizes unramifiedness). So `f'(π)` is never a unit for `e ≥
  2`, tame or wild: this confirms (rather than assumes) that the totally ramified case genuinely
  needs the separate Eisenstein/discriminant argument above, not a variant of the tool already used
  for the unramified half. (This computation was carried out this session, not sourced from a
  citation — flagged as such, though it is a standard fact: the different is trivial iff the
  extension is unramified.)
- **Net effect on `RamificationFiltration.lean`'s associated-graded embeddings.** Not closed this
  pass. The wall documented there is now more precisely located — not "no Mathlib
  monogenicity-of-DVR-extension theorem exists" (there is a usable route, corrected above) but "the
  Eisenstein-ness-from-uniformizer step is unbuilt." No `.lean` files were touched this pass; `lake
  build Langlands` re-verified clean (8675 jobs) before and after, unchanged.
- **Not attempted, scoped for a future pass:** (1) the Eisenstein-ness-from-uniformizer lemma
  itself; (2) wiring a `PowerBasis K L` for `π` (needs `K(π) = L`, itself needing Eisenstein
  irreducibility of `minpoly K π`, circular with (1) unless sequenced correctly — irreducibility over
  `K` needs Eisenstein-ness at the `R`-level *first*, which is the right order since `(1)` produces
  exactly that); (3) the DVR unit/`p`-power factorization glue connecting `Algebra.
  discr_mul_isIntegral_mem_adjoin`'s output to the induction lemma's `p ^ n • z` hypothesis; (4) the
  composition step combining this half with the unramified half into monogenicity over `O_K` proper
  (Serre's actual combining argument, not yet checked in detail this pass).

#### Status 2026-08-06 (fourteenth pass) — spectral-value coefficient bound proved and committed; the two remaining assembly gaps precisely relocated, no `LocalField.isEisensteinAt_minpoly_of_isUniformizer` statement declared

- **Task.** Attempt the Eisenstein-ness-from-uniformizer lemma scoped by the thirteenth pass, via a
  route through `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean` (`spectralNorm K L x :=
  spectralValue (minpoly K x)`) that sidesteps most of the Galois/conjugate-valuation argument: two
  elements sharing a minimal polynomial automatically share a `spectralNorm`, by definition, with no
  completeness needed for *that* fact.
- **Built and committed, sorry-free** (`Langlands/TotallyRamifiedEisenstein.lean`, commit
  `55d1a9d`):
  - `spectralValue_coeff_le {R} [NormedDivisionRing R] {p : R[X]} {n} (hn : n < p.natDegree) :
    ‖p.coeff n‖ ≤ spectralValue p ^ (p.natDegree - n)` (`TotallyRamifiedEisenstein.lean:76`) — the
    per-coefficient bound obtained by unfolding `spectralValue p := iSup (spectralValueTerms p)`
    (`le_ciSup (spectralValueTerms_bddAbove p) n` dominates each term, then
    `spectralValueTerms_of_lt_natDegree` identifies the term as `‖p.coeff n‖ ^ (1/(natDegree-n:ℝ))`,
    and raising both sides to the `(natDegree-n)`-th power via `Real.rpow_inv_natCast_pow` +
    `Real.rpow_le_rpow` gives the claim). Confirmed via direct read of
    `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean` that no such per-`n` bound is already
    packaged (only the `≤ 1` boundary case, `spectralValue_le_one_iff`, exists).
  - `spectralNorm_coeff_lt_one {K} [NormedField K] {L} [Field L] [Algebra K L] {x : L} (hx :
    spectralNorm K L x < 1) {n} (hn : n < (minpoly K x).natDegree) : ‖(minpoly K x).coeff n‖ < 1`
    (`TotallyRamifiedEisenstein.lean:105`) — the sharper *strict* form needed for
    `Polynomial.IsEisensteinAt.mem` (ideal membership, not just valuation-ring membership), via
    `pow_le_pow_of_le_one` collapsing the exponent `natDegree - n ≥ 1` down to `1`.
- **The two gaps that remain, now relocated precisely** (documented in the new file's module
  docstring, not repeated here in full):
  1. Connecting a concrete uniformizer `π` of a `ValuationSubring A` of `L` (with `A.comap
     (algebraMap K L) = 𝒪[K]`) to the hypothesis `spectralNorm K L π < 1` these two lemmas need. This
     is formal given machinery already in `Langlands.HenselianValuation`
     (`exists_rankOne_absoluteValue_extends`, `spectralNorm_unique_field_norm_ext`) plus the
     `IsNonarchimedeanLocalField K → NormedField K` instance-construction block already written out
     at `Langlands/HenselianValuation.lean:715-732`
     (`valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField`), plus
     `ValuationSubring.mem_nonunits_iff_or`/`coe_mem_nonunits_iff`
     (`Mathlib/RingTheory/Valuation/ValuationSubring.lean:562-620`, confirmed present this pass) for
     `f π ≠ 1`. Not assembled into a standalone lemma this pass.
  2. Converting the resulting real-number bound (from `spectralNorm_coeff_lt_one`) and exact value
     (from `spectralNorm_eq_norm_coeff_zero_rpow`, `SpectralNorm.lean:988`, note: namespaced as
     `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` — the task brief's transcription omitted the
     `namespace spectralNorm` wrapping it, verify with `open scoped spectralNorm` or full
     qualification before use) into the *ideal-power* statement
     `(minpoly K π).coeff 0 ∉ 𝔪_K ^ 2` that `Polynomial.IsEisensteinAt.notMem` needs. Confirmed
     present this pass, via loogle (`IsDiscreteValuationRing, maximalIdeal, pow`):
     `Valuation.integer.integers.maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow` and
     `Irreducible.maximalIdeal_pow_eq_setOf_le_v_coe_pow`
     (`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:676,698`), identifying `(maximalIdeal O ^
     n : Set O)` with `{y | v (algebraMap O K y) ≤ v (algebraMap O K ϖ) ^ n}` for `O` a DVR with
     valuation `v` and irreducible uniformizer `ϖ`. These are stated for `v.integer`
     (`Valuation.integer`, a plain `Subring`), not for `(valuation K).valuationSubring` (a bundled
     `ValuationSubring`) as used throughout `Langlands.HenselianValuation` — the two carrier types are
     defeq (`Valuation.valuationSubring` is literally `{ v.integer with mem_or_inv_mem' := ... }`,
     `Mathlib/RingTheory/Valuation/ValuationSubring.lean:439`) but transporting the `IsDiscreteValuationRing`
     instance and the pow-ideal lemma across that defeq, and bridging the *real*-number
     inequality/equality out of step (2)'s starting lemmas back down to a `Γ₀`-valued
     (`ValueGroupWithZero K`) inequality via the ambient `RankOne.hom` embedding's
     `StrictMono.le_iff_le`, was not attempted.
- **Why no `LocalField.isEisensteinAt_minpoly_of_isUniformizer` statement was declared.** Writing the
  full signature before either gap above is closed would force a choice between `sorry` (forbidden,
  hard constraint) or hypotheses strong enough to trivialize the theorem (e.g. hypothesizing the
  ideal-power condition directly) — neither is acceptable. The two lemmas that are committed are
  self-contained and reusable regardless of how the remaining assembly proceeds; `lake build
  Langlands` re-verified clean (8676 jobs, one file added) and `grep -rn sorry Langlands/` confirmed
  zero non-prose occurrences project-wide.
- **Next step for whoever picks this up:** gap (1) first (it is the more mechanical of the two —
  copying an existing, already-typechecking instance-construction block), then gap (2)'s
  `ValuationSubring`/`Valuation.integer` defeq transport, in that order — gap (1)'s output
  (`spectralNorm K L π < 1`, a real inequality) is exactly what gap (2)'s bridging step needs as
  input, so sequencing them the other way round has nothing to feed gap (2) until gap (1) exists.

#### Status 2026-08-06 (fifteenth pass) — gap 1 CLOSED; gap 2 narrowed (two of four sub-blockers resolved), still not assembled, no theorem declared

- **Task.** Close gap 1, then attempt gap 2, of the fourteenth pass's Eisenstein-ness-from-uniformizer
  route; state the full `isEisensteinAt_minpoly_of_isUniformizer` theorem if both close.
- **Gap 1 CLOSED**, commit `6b823af`: `LocalField.spectralNorm_lt_one_of_mem_nonunits`
  (`Langlands/HenselianValuation.lean`, `LocalField.NormedFieldBridge` section, immediately before
  `valuationSubring_eq_of_comap_eq`) — for `A : ValuationSubring L` with `A.comap (algebraMap K L) =
  (valuation K).valuationSubring` and `π ∈ A.nonunits`, `π ≠ 0`: `spectralNorm K L π < 1`. Built from
  `exists_rankOne_absoluteValue_extends` + `spectralNorm_unique_field_norm_ext` +
  `ValuationSubring.mem_nonunits_iff_or` + `map_inv₀` + `inv_lt_one_of_one_lt₀`. No
  `_of_isNonarchimedeanLocalField` wrapper: `spectralNorm K L π`'s type needs `NormedField K` already
  at the *signature* level, so such a wrapper can't elaborate under only `[IsNonarchimedeanLocalField
  K]` — the instance-construction `letI`/`haveI` block must be inlined once inside any Henselian
  caller whose own conclusion doesn't mention `spectralNorm` (confirmed by hitting exactly this
  "failed to synthesize instance NormedField K" error when first attempting such a wrapper, then
  removing it in favor of the plain bundle-hypothesis version).
- **Gap 2 narrowed, not closed.** Investigated the four sub-pieces the fourteenth pass's diagnosis
  implied (transport `IsIntegrallyClosed`/`IsFractionRing` for `𝒪[K]`; transport the DVR pow-ideal
  lemma across the `Valuation.integer`/`ValuationSubring` defeq; bridge the real-number bound back to
  `Γ₀`; assemble the pieces into `Polynomial.IsEisensteinAt`). Two resolved this pass (via loogle +
  one standalone `lake env lean` typecheck, not yet wired into a real proof):
  1. `IsIntegrallyClosed`/`IsFractionRing` for any `V : ValuationSubring K` are **direct instances**
     (`Mathlib/RingTheory/Valuation/LocalSubring.lean:35,38`,
     `ValuationSubring.instIsFractionRingSubtypeMem`) — no transport code needed on this project's
     side, contrary to the fourteenth pass's concern.
  2. The DVR pow-ideal lemma has a **`ValuationSubring`-level route avoiding `Valuation.integer`
     entirely**: `ValuationSubring.lean:468`'s `valuationSubring.integers : v.Integers
     v.valuationSubring` supplies `Valuation.Integers` directly at the `ValuationSubring` level, so
     `Valuation.Integers.maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow`
     (`DiscreteValuationRing/Basic.lean:672`) applies to `O := ↥(valuation K).valuationSubring`
     directly, sidestepping the defeq transport the fourteenth pass flagged as needing "real care".
     `IsDiscreteValuationRing ↥(valuation K).valuationSubring` is also available directly via
     `Valuation.valuationSubring_isDiscreteValuationRing`
     (`Mathlib/RingTheory/Valuation/Discrete/Basic.lean`), given `[IsCyclic ...][Nontrivial ...]` on
     the value group (expected for a local field, not separately checked this pass).
  3. **New, sharper than the fourteenth pass's plan**: `RankOne.hom' : Γ₀ →*₀ ℝ≥0` is a
     `MonoidWithZeroHom`, so an *exact* valuation-level total-ramification hypothesis (`A.valuation
     (algebraMap K L ϖ) = A.valuation π ^ n`) pushes forward to an *exact* real equation `‖ϖ‖ =
     spectralNorm K L π ^ n = ‖(minpoly K π).coeff 0‖` (via `spectralNorm_eq_norm_coeff_zero_rpow`),
     not merely the inequality the fourteenth pass's `StrictMono.le_iff_le` plan would have given —
     an exact match directly forces `coeff 0 ∉ 𝔪_K ^ 2` (since `‖ϖ‖ > ‖ϖ‖²`), no slack to account for.
  4. **Not attempted**: assembling (1)-(3) plus `minpoly.isIntegrallyClosed_eq_field_fractions'`
     (`Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean`, confirmed applicable since `Algebra
     ↥(A : ValuationSubring K) L` derives automatically by instance search given `[Algebra K L]` —
     checked via a standalone `example ... : Algebra A L := inferInstance` typecheck, not committed)
     into an actual `Polynomial.IsEisensteinAt` proof: precisely designing the "totally ramified"
     hypothesis and applying it to a chosen uniformizer of `𝒪[K]`, the `IsScalarTower` wiring for
     `minpoly ↥𝒪[K] π`, assembling `IsEisensteinAt`'s three fields, and checking the `IsCyclic`/
     `Nontrivial` value-group side-condition from (2) actually discharges for
     `IsNonarchimedeanLocalField K`. None of these hit a wall this pass — each has a named, real
     lemma or already-typechecked instance — but none was written or built, so none should be
     treated as confirmed working until it is. `lake build Langlands` re-verified clean (8676 jobs);
     `grep -rn sorry langlands/Langlands/` empty.
- **Next step for whoever picks this up:** design the exact "totally ramified" hypothesis first (item
  4(a) above) — everything else in item 4 is mechanical assembly once that hypothesis's shape is
  fixed, and getting the hypothesis shape wrong (e.g. omitting the specific uniformizer `ϖ` it should
  quantify over, or phrasing it via `Associated` instead of the `A.valuation` equation) would force
  rework of the assembly built on top of it.

#### Status 2026-08-06 (sixteenth pass) — `LocalField.isEisensteinAt_minpoly_of_isUniformizer` CLOSED (no `sorry`); monogenicity assembly not attempted

- **Task.** Design and close the fifteenth pass's remaining "totally ramified" hypothesis + assembly
  gap; state and prove the full Eisenstein theorem targeted since the thirteenth pass.
- **Closed, commit-pending in `langlands/Langlands/TotallyRamifiedEisenstein.lean`** (zero `sorry`,
  `lake build Langlands` clean, 8676 jobs):
  ```
  theorem LocalField.isEisensteinAt_minpoly_of_isUniformizer
      {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
      [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
      {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
      [IsDiscreteValuationRing ↥(valuation K).valuationSubring]
      {ϖ : ↥(valuation K).valuationSubring} (hϖ : Irreducible ϖ) {π : L}
      (hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree) :
      (minpoly ↥(valuation K).valuationSubring π).IsEisensteinAt
        (IsLocalRing.maximalIdeal ↥(valuation K).valuationSubring)
  ```
  This is the exact target signature scoped since the thirteenth pass, with
  `[IsDiscreteValuationRing ↥(valuation K).valuationSubring]` kept as an explicit hypothesis per the
  task brief (deriving it from `IsCyclic`/`Nontrivial` value-group conditions is orthogonal,
  structural content about `K`, not attempted here).
- **The hypothesis design deviates from the fifteenth pass's plan, and this is the key finding of
  this pass.** The fifteenth pass planned an exact `A.valuation`-level equation (`A : ValuationSubring
  L` extending `𝒪[K]`) pushed forward through a `RankOne A.valuation` instance's `hom'`. Attempting
  this directly (via `Langlands.HenselianValuation`'s `exists_rankOne_compatible`/
  `exists_rankOne_absoluteValue_extends`) hit a real obstruction: `hR.hom'` for `hR : RankOne
  A.valuation`, once resolved through dot notation, is the *parent* `RankLeOne` structure's `hom'`
  operating on the canonical `MonoidWithZeroHom.ValueGroup₀`-embedded value group, not directly on
  `A.ValueGroup` — so `hR.hom' (A.valuation x)` does not typecheck as the fifteenth pass's writeup
  implied; only `hR.hom' (A.valuation.restrict (algebraMap K L x))` (already used by
  `exists_rankOne_absoluteValue_extends` for `x : K` specifically) does, and generalizing that fact to
  all `y : L` was not straightforward from the section's existing lemmas. **This detour turned out to
  be unnecessary**: `spectralNorm K L` is already the canonical, unique norm extension (by
  `spectralNorm_unique_field_norm_ext`, applicable to *any* absolute value extending `‖·‖`, including
  ones built from a `RankOne A.valuation` instance), so the classical "totally ramified of degree `n`"
  condition is *exactly* `‖ϖ‖ = spectralNorm K L π ^ n` with no reference to a specific `A` or
  `RankOne` instance needed. This is simpler to state, simpler to prove from, and — as a consequence —
  the final theorem needs **no** `A : ValuationSubring L`, `hA`, `π ∈ A.nonunits`, or `π ≠ 0`
  hypothesis at all: `spectralNorm K L π < 1` is *derived* from `hram` plus `‖ϖ‖ < 1` (from `ϖ`
  irreducible), not proved via `A` first. **`LocalField.spectralNorm_lt_one_of_mem_nonunits`
  (`Langlands.HenselianValuation`, gap 1 from the fifteenth pass) and the whole `RankOne`/
  `exists_rankOne_absoluteValue_extends` machinery are unused by the closed theorem** —
  `TotallyRamifiedEisenstein.lean` has zero dependency on `Langlands.HenselianValuation`.
- **New general-purpose lemmas** (same file, `LocalField` namespace, reusable independent of the
  Eisenstein argument): `mem_valuationSubring_iff_norm_le_one` (`x ∈ (valuation K).valuationSubring ↔
  ‖x‖ ≤ 1`, from `Valuation.Compatible.vle_iff_le` applied to both `valuation K` and
  `NormedField.valuation`), `valuation_le_iff_norm_le` (the same bridging generalized beyond the `≤ 1`
  special case), `mem_maximalIdeal_iff_norm_lt_one` (`x ∈ 𝔪_{𝒪[K]} ↔ ‖(x:K)‖ < 1`, proved directly from
  first principles — if `‖x‖ = 1` exactly then `x⁻¹` also has norm `≤ 1` hence lies in `𝒪[K]`,
  witnessing `x` a unit; conversely a unit's inverse has norm `≤ 1`, forcing the product of norms to
  exceed `1` unless `‖x‖ = 1` — no dependence on `ValuationSubring.mem_nonunits_iff`, which is stated
  for the *different* `ValuationSubring.valuation` rather than the ambient `ValuativeRel`-canonical
  `valuation K`, avoiding an `IsEquiv`-transport detour).
- **Assembly, following the fifteenth pass's diagnosis closely with no further obstructions**: all
  coefficients of `minpoly K π` lie in `𝒪[K]` (monic leading coefficient trivially; non-leading via
  `spectralNorm_coeff_lt_one`, this file's existing fourteenth-pass lemma); `Polynomial.toSubring`
  lifts this to a monic witness for `IsIntegral ↥𝒪[K] π` (`Algebra ↥𝒪[K] L` and the defeq between
  `↥𝒪[K]` and `↥𝒪[K].toSubring` both resolve automatically by instance search / `exact`, confirmed
  live, not merely assumed); `minpoly.isIntegrallyClosed_eq_field_fractions'` (using the direct
  `IsIntegrallyClosed`/`IsFractionRing ↥𝒪[K] K` instances from `Mathlib.RingTheory.Valuation.LocalSubring`,
  confirmed exactly as the fifteenth pass predicted) identifies `minpoly K π` with the base change of
  `minpoly ↥𝒪[K] π`, transporting the coefficient bounds down via `Polynomial.natDegree_map_eq_of_injective`
  (injectivity via `IsFractionRing.injective`, not the `IsSimpleRing`-requiring generic
  `RingHom.injective` the naive `(algebraMap ↥𝒪[K] K).injective` term elaborates to) and
  `Polynomial.coeff_map`. The `notMem` field uses the exact equality `‖(minpoly K π).coeff 0‖ = ‖ϖ‖`
  (from `hram` via `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` and
  `Real.rpow_inv_natCast_pow`) together with `‖ϖ‖ > ‖ϖ‖ ^ 2` (as `0 < ‖ϖ‖ < 1`) and
  `Valuation.Integers.maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow` exactly as the fifteenth pass
  located it (via `Valuation.valuationSubring.integers`, no `Valuation.integer` defeq transport
  needed).
- **Monogenicity (item 3 of the task brief) not attempted this pass** — ran out of budget after
  closing the Eisenstein theorem itself. Checked what's available:
  `Mathlib/RingTheory/Polynomial/Eisenstein/IsIntegral.lean` (confirmed, despite living alongside
  cyclotomic-specific lemmas in the same file, to contain genuinely general statements — not
  `NumberField`-specific) has `mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt`: for `R`
  integrally closed with fraction field `K`, `L / K` with an integral power basis `B` whose generator
  has Eisenstein minimal polynomial at a *prime* `p : R`, any integral `z` with `p • z ∈ R[B.gen]`
  satisfies `z ∈ R[B.gen]`. This is the natural next lever (combined with
  `Algebra.discr_mul_isIntegral_mem_adjoin`, per the thirteenth pass's citation) but wiring it to
  `𝒪[K]`/`↥(valuation K).valuationSubring` — building the `PowerBasis`, checking `Prime ϖ` (should
  follow from `Irreducible ϖ` since a DVR is a PID/UFD, not separately checked), and the induction to
  peel off finitely many factors of `ϖ` bounded by the discriminant — was not attempted. This is a
  genuinely new, not-yet-scoped-in-detail piece of work, not a small remainder.
- **Also not attempted**: the `RamificationFiltration.lean` `## Scope` section's actual downstream use
  (feeding this theorem into the associated-graded-embedding kernel argument blocked since the twelfth
  pass) — that still needs the monogenicity step above first, plus wiring the specific uniformizer `π`
  of `RamificationFiltration.lean`'s `A : ValuationSubring L` (with `hπ : 𝔪_A = Ideal.span {π}`) to
  this theorem's hypotheses.
- **Verification**: `lake build Langlands` clean (8676 jobs, no `sorry`); `grep -rn sorry
  langlands/Langlands/` shows only prose mentions of the word (in this file's own module doc and
  `RamificationFiltration.lean`'s `## Scope` discussion of why `sorry` was avoided), zero actual
  `sorry` tactics.

#### Status 2026-08-06 (seventeenth pass) — totally-ramified monogenicity CLOSED (no `sorry`); general (tower) monogenicity and the `RamificationFiltration.lean` wiring not attempted

- **Task.** Close the sixteenth pass's item 3 (monogenicity, `O_L = O_K[π]`, for the totally
  ramified case) using `isEisensteinAt_minpoly_of_isUniformizer` plus
  `mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt`; attempt the composition step (general
  monogenicity via the unramified-times-totally-ramified tower) if time allowed; return to
  `RamificationFiltration.lean`'s associated-graded embeddings if time allowed after that.
- **Closed, commit `531f1b4`, `langlands/Langlands/TotallyRamifiedEisenstein.lean`** (zero `sorry`,
  `lake build Langlands` clean, 8676 jobs):
  ```
  theorem LocalField.adjoin_eq_integralClosure_of_isUniformizer
      {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
      [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
      {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
      [IsDiscreteValuationRing ↥(valuation K).valuationSubring]
      [FiniteDimensional K L] [Algebra.IsSeparable K L]
      {ϖ : ↥(valuation K).valuationSubring} (hϖ : Irreducible ϖ) {π : L}
      (hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree)
      (hgen : (minpoly K π).natDegree = Module.finrank K L) :
      Algebra.adjoin ↥(valuation K).valuationSubring ({π} : Set L) =
        integralClosure ↥(valuation K).valuationSubring L
  ```
  `hgen` is the new ingredient beyond the Eisenstein theorem's hypotheses: it is exactly "`π` also
  generates `L` over `K`" (`K⟮π⟯ = L`), the condition implicit in "`π` is a uniformizer of a totally
  ramified extension" that the Eisenstein theorem alone doesn't need (it only ever uses `K(π)`, the
  subextension `π` generates, not all of `L`).
- **Used the more general Mathlib lever than the sixteenth pass named.** The sixteenth pass flagged
  `mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt` (the single-`p`-factor peeling step) as
  the next lever; this pass used its wrapper
  `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt` (`p ^ n • z ∈ R[gen] → z ∈ R[gen]`,
  proved by iterating the single-factor version) directly, since the discriminant is only known to
  be *some* power of `ϖ` up to a unit, not literally `ϖ` itself — no new gap, just using the already
  correct general-purpose wrapper instead of manually iterating the single-factor lemma.
- **Proof assembly, four pieces:**
  1. **A `PowerBasis K L` with generator `π`.** `hgen` promotes `IntermediateField.adjoin K {π}` to
     `⊤` (via `IntermediateField.adjoin.finrank` + `Submodule.eq_top_of_finrank_eq`, transported
     across `IntermediateField.toSubalgebra`/`Subalgebra.toSubmodule`), and thence, via
     `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic` +
     `IntermediateField.top_toSubalgebra`, promotes the *Subalgebra* `Algebra.adjoin K {π} = K[π]`
     to `⊤` as well — the Subalgebra route (not `IntermediateField.equivOfEq`/`topEquiv`) was the one
     that actually worked: `IntermediateField.equivOfEq` has no `_apply` simp lemma exposing that it
     preserves the ambient coercion to `L` (only `Subalgebra.equivOfEq_apply` and
     `Subalgebra.topEquiv_apply` exist and compose cleanly), so `Algebra.adjoin.powerBasis hxK` (the
     `Subalgebra`-valued `PowerBasis`, `Mathlib.RingTheory.Adjoin.PowerBasis`, needs its own import —
     not pulled in transitively by `Discriminant.lean`) mapped along
     `(Subalgebra.equivOfEq _ _ htopalg).trans Subalgebra.topEquiv` is what closed `B.gen = π`.
  2. **`Prime ϖ`** from `Irreducible ϖ`, via `PrincipalIdealRing.to_uniqueFactorizationMonoid`
     (`↥𝒪[K]` is a PID since `IsDiscreteValuationRing` extends `IsPrincipalIdealRing`) +
     `UniqueFactorizationMonoid.irreducible_iff_prime` — confirmed a DVR-is-a-PID route works
     directly; the sixteenth pass's guess ("should follow ... not separately checked") holds, though
     the actual lemma needed (`PrincipalIdealRing.to_uniqueFactorizationMonoid`) is not the one a
     first guess (`IsDiscreteValuationRing.toUniqueFactorizationMonoid`, which turned out to need an
     unrelated `HasUnitMulPowIrreducibleFactorization` hypothesis, not just `IsDiscreteValuationRing`)
     would suggest.
  3. **`discr K B.basis` factors as `unit * ϖ ^ m`.** `Algebra.discr_isIntegral` gives integrality
     over `↥𝒪[K]`; `IsIntegrallyClosed.isIntegral_iff` (already a direct instance for
     `ValuationSubring`s, per the fifteenth/sixteenth passes) pins it to an actual `d : ↥𝒪[K]`;
     `discr_not_zero_of_basis` (separability) gives `d ≠ 0`; `IsDiscreteValuationRing.
     associated_pow_irreducible` (already used by the tenth pass's `UnramifiedNormRange.lean`) gives
     `Associated d (ϖ ^ m)`, unfolded to `d = ϖ ^ m * v` for a unit `v`.
  4. **Assembly**: `Algebra.discr_mul_isIntegral_mem_adjoin` gives `discr • z ∈ 𝒪[K][π]` for any `z`
     integral over `𝒪[K]`; `d • z = discr • z` via `IsScalarTower.algebraMap_smul`; substituting
     `d = ϖ^m * v` and using `Subalgebra.smul_mem` with `v⁻¹` cancels the unit, leaving `ϖ^m • z ∈
     𝒪[K][π]`; `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt` then gives `z ∈
     𝒪[K][π]` outright. Combined with `adjoin_le_integralClosure` (the trivial `≤` direction) this is
     the full equality `Algebra.adjoin ↥𝒪[K] {π} = integralClosure ↥𝒪[K] L`.
- **Genuine build friction, none a wall**: `Algebra.adjoin.powerBasis`/`Algebra.discr_isIntegral`/
  `Algebra.discr_mul_isIntegral_mem_adjoin` all take their base field `K` as an *explicit* first
  argument (not inferable from named implicit args alone — passing `(R := ↥𝒪[K])` without also
  supplying `K` positionally left `K`'s metavariable unresolved in a way that surfaced as confusing
  "expected `Type`" errors pointing at unrelated argument positions); `Ideal.span`/`Submodule.span`
  are propositionally but not syntactically equal (`Ideal.submodule_span_eq` bridges them); and a
  `set O := ... with hOdef` (rather than `let`) inside the final theorem's proof caused `ϖ`'s own
  binder to be silently re-generalized into a shadowed, display-inconsistent `ϖ✝`/`ϖ` pair — switched
  to `let` (matching `isEisensteinAt_minpoly_of_isUniformizer`'s own proof style) to avoid it. None
  of these needed new infrastructure; all were resolved within the session's normal build-iterate
  loop, unlike the genuine walls flagged in the ROADMAP entries above this one.
- **Not attempted (per the task's explicit "don't force it" permission, budget spent on step 1):**
  1. **General (tower) monogenicity** — combining this theorem with the already-complete unramified
     half (`HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv`,
     `Langlands/UnramifiedExtension.lean:715`) via Serre's pass-to-the-maximal-unramified-subfield-
     then-adjoin-a-uniformizer argument. Not scoped in detail this pass beyond what the task brief
     already sketches; the two halves are proved in visibly different settings (the unramified half
     works inside `IsAlgClosed L` with a from-scratch `AdjoinRoot` construction; the totally ramified
     half here works with an ambient `ValuativeRel`/`NormedField`/`spectralNorm` bundle) — reconciling
     those two settings into a single tower statement is real, unscoped work, not a small remainder.
  2. **`RamificationFiltration.lean`'s associated-graded-embedding kernel argument** (blocked since
     the twelfth pass). Still needs: (a) the composition step above (monogenicity over `O_K`, not
     just over the maximal unramified subfield), since the associated-graded argument is stated for a
     general `A : ValuationSubring L` over `K` directly, not pre-decomposed into an unramified/totally
     ramified tower; (b) wiring the specific uniformizer `π` of `RamificationFiltration.lean`'s
     `hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}` to this theorem's `hram`/`hgen` hypotheses
     (needs, at minimum, phrasing `hram` in terms of `A`'s own valuation rather than `spectralNorm`,
     or a bridging lemma between the two — not attempted, not checked for obstructions this pass).
- **Next step for whoever picks this up:** (1) is the more valuable and more tractable of the two —
  it produces a second closed classical theorem (full monogenicity) reusable well beyond
  `RamificationFiltration.lean`; scope it by first reading both halves' exact statements side by side
  (`UnramifiedExtension.lean:715`'s conclusion and `adjoin_eq_integralClosure_of_isUniformizer`'s
  hypotheses above) and identifying precisely which instance/hypothesis bridges are needed to state
  a single tower theorem, before writing any proof code — this project's own recurring failure mode
  (per `CLAUDE.md`'s "flagged as mechanical, turned out to need a workaround") is exactly the risk
  here given the two halves' visibly different ambient settings.

#### Status 2026-08-06 (eighteenth pass) — spike on the seventeenth pass's "not attempted item 1": does the totally-ramified bundle transport onto the unramified half's `M`? Norm/completeness half has a real composable path but hit a genuine diamond wall in one attempt; the DVR half has no ready-made Mathlib lemma and needs new proof work. No `sorry`, nothing committed (the one composition attempt did not typecheck and was reverted).

This pass targeted one narrow question, precisely scoped by the parent task: once `M`
(`IntermediateField K {x}`, the unramified half's maximal unramified subextension,
`Langlands/UnramifiedExtension.lean:715`) is built with **no valuation structure attached**, does
`𝒪[M]` inherit completeness and discreteness of valuation from `K`, in a form composing with the
totally-ramified half's `NontriviallyNormedField`/`IsUltrametricDist`/`ValuativeRel`/`Compatible`/
`CompleteSpace`/`IsDiscreteValuationRing` bundle (`TotallyRamifiedEisenstein.lean:163`)? The
"two generators into one"/full tower-monogenicity composition itself was explicitly out of scope
and not attempted.

- **Mathlib does have the general "finite extension of a complete nonarchimedean field is
  complete" result, confirmed by reading the source, and it is not specific to adic completions.**
  `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`: `spectralNorm.nontriviallyNormedField K L`
  builds a `NontriviallyNormedField L` from `[NontriviallyNormedField K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]` via the spectral norm; `isNonarchimedean_spectralNorm` gives it's
  nonarchimedean (`IsUltrametricDist L` via `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`,
  `Mathlib/Analysis/Normed/Group/Ultra.lean:57`); `spectralNorm.completeSpace` (line 936, needs
  `[CompleteSpace K] [FiniteDimensional K L]`) gives `@CompleteSpace L (uniformSpace K L)`; and
  `spectralNorm_extends` shows the norm extends `‖·‖` on `K`. This is [BGR, Theorem 3.2.4/2] and is
  a genuine derivation, not a definitional freebie.
- **`Langlands/NormMap.lean`'s adic-completion instance block (`RankOne` section, lines 92–129) is
  confirmed, by reading the actual definitions, to be the latter — completeness there is
  definitional, not derived from finiteness.** `v.adicCompletion F` and `w.adicCompletion L` are
  literally *defined* as `UniformSpace.Completion`s (via `adicCompletion.equiv`), so their
  `CompleteSpace` instances are free by construction. The one instance in that block that *is* a
  genuine derivation from finiteness is `Module.Finite (v.adicCompletion K) (w.adicCompletion L)`
  (line 363, via a dense-range-plus-closed-finite-dimensional-range argument) — but that is a
  different fact (finiteness of the completion as a module) from completeness itself. So this
  block does **not** answer the open question; `spectralNorm.completeSpace` is the correct general
  tool for an abstract finite extension with no prior completion structure.
- **Attempted the concrete composition** (norm/completeness/`ValuativeRel`/`Compatible` half only,
  in `Langlands/HenselianValuation.lean`'s `NormedFieldBridge` section, as a new theorem
  `exists_bundle_of_finiteDimensional`) and hit a reproducible instance diamond, confirmed on two
  successive builds with the identical error (the skill's stop-on-repeated-error signal):
  `letI hnf : NontriviallyNormedField M := spectralNorm.nontriviallyNormedField K M` reconstructs
  `Field M` via an anonymous-constructor merge `{ (inferInstance : Field L) with ... }` internal to
  that def; the resulting `hnf.toField` is not recognized as definitionally equal, at the
  transparency Lean's typeclass-diamond check uses, to the ambient `[Field M]` instance already
  required by the theorem's own hypotheses (`[Algebra K M]`) — even though the two are
  propositionally identical. This blocked `ValuativeRel.ofValuation (NormedField.valuation (K :=
  M))` with `synthesized type class instance is not definitionally equal to expression inferred by
  typing rules`. The edit was reverted (`git checkout`); nothing was committed.
- **A plausible, un-executed workaround, evidenced by already-working code in this same file:**
  `LocalField.exists_rankOne_absoluteValue_extends` (line 664) also has an ambient `[Field L]` in
  scope and *does* build a `NontriviallyNormedField L` successfully, via `Valued.mk' A.valuation`
  then `Valued.toNontriviallyNormedField` — a route that adds a valuation on top of the existing
  `Field L` instance rather than reconstructing it, and so does not hit the diamond above. Composing
  that route (via a `ValuationSubring M` extending `𝒪[K]`, from `exists_rankOne_compatible`) with
  the generic `FiniteDimensional.complete` (`Mathlib/Topology/Algebra/Module/FiniteDimension.lean`,
  needs `ContinuousSMul K M` + `IsUniformAddGroup M` + `T2Space M`, all plausible but unverified for
  the `Valued`-induced topology) instead of `spectralNorm.completeSpace` was identified as a way to
  route around the diamond, but was not attempted — budget for this pass was spent on diagnosing the
  wall precisely rather than iterating further variants.
- **The `IsDiscreteValuationRing` half of the bundle has no ready-made Mathlib lemma and needs real
  new proof work, not composition.** Grepped `Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean`
  and `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`: the only path found is
  `IsDiscreteValuationRing.TFAE` (needs `[IsNoetherianRing R] [IsLocalRing R] [IsDomain R]`, not
  `¬ IsField R`) applied to a Dedekind domain (`integralClosure.isDedekindDomain`, confirmed to
  exist, needs `Algebra.IsSeparable K L`) that is also local. Confirmed by reading
  `UnramifiedExtension.lean:892` (`hCisLocalRing := e.isLocalRing`) that the existing local-ring
  proof for that file's `C := integralClosure R K'` is bespoke — it transports `IsLocalRing` along
  a specific `AdjoinRoot f ≃+* C` ring equivalence tied to the chosen generator `x`, not a generic
  "integral closure of a Henselian/complete DVR in an arbitrary finite extension is local" lemma.
  `Mathlib/RingTheory/Henselian.lean` has no such generic lemma either (grepped; only `TFAE` and the
  Hensel-lift existence/uniqueness theorem). A plausible general strategy, sketched but not
  attempted: the valuation subring `A` of `M` extending `𝒪[K]` is unique
  (`LocalField.valuationSubring_eq_of_comap_eq`, already in this repo) and automatically local (all
  `ValuationSubring`s are); showing `A = integralClosure 𝒪[K] M` and that the integral closure is
  Dedekind (via `Algebra.IsSeparable K M`, available in the totally-ramified bundle) plus not a
  field would give `IsDiscreteValuationRing A` via the same `TFAE` step `UnramifiedExtension.lean`
  already uses (lines 897–910) — but proving `A = integralClosure 𝒪[K] M` and threading
  nontriviality is a real proof, not a lemma lookup.
- **Conclusion for the parent task's question:** the norm/completeness/`ValuativeRel`/`Compatible`
  half of the bundle transports via a real, general Mathlib theorem
  (`spectralNorm.completeSpace` + friends), but composing it onto an abstract finite extension `M`
  that already carries an ambient `Field M` instance hit a diamond that needs a different
  construction route than the one tried (see the `Valued.mk'` workaround above). The
  `IsDiscreteValuationRing` half is not a composition question at all — Mathlib has no generic
  "integral closure of a Henselian/complete local ring in a finite extension is local" theorem, and
  this repo's own precedent (`UnramifiedExtension.lean`) proves it by a bespoke, generator-specific
  argument each time. Reconciling the two monogenicity halves into one tower theorem remains real,
  unscoped work, exactly as the seventeenth pass flagged — this pass narrows *why* (a diamond in one
  concrete route, plus a missing general local-ness lemma) without closing it.
- **Next step for whoever picks this up:** retry the composition using the `Valued.mk'`/
  `Valued.toNontriviallyNormedField` route (diamond-safe, evidenced by
  `exists_rankOne_absoluteValue_extends` already compiling with an ambient `[Field L]`) instead of
  `spectralNorm.nontriviallyNormedField`, and separately attempt the `A = integralClosure 𝒪[K] M`
  argument sketched above as its own lemma before trying to assemble the full bundle.

#### Status 2026-08-06 (nineteenth pass) — diamond reproduced first-hand and root-caused; not a
Field-instance clash per se but a non-defeq `UniformSpace M` clash between two independently
*constructed* bundles. No `.lean` file changed (scratch repro built and deleted, nothing
committed); this is a diagnosis-only pass, as scoped.

- **Reproduced the eighteenth pass's diamond directly** (scratch file, `lake build`-verified, then
  deleted — not committed). Two isolated attempts to compose `spectralNorm.nontriviallyNormedField`
  onto an `M` carrying only an ambient `[Field M]` (no pre-existing norm/valuation structure)
  **typechecked with no diamond** — `letI hnf := spectralNorm.nontriviallyNormedField K M` followed
  by `ValuativeRel.ofValuation (NormedField.valuation (K := M))`, and separately a `have key : A =
  (NormedField.valuation (K := M)).valuationSubring` goal against a pre-existing `A : ValuationSubring
  M`, both compiled clean. **The diamond is not triggered by `spectralNorm` meeting a bare ambient
  `[Field M]`** — the eighteenth pass's report of hitting it in that shape could not be reproduced in
  isolation; either it needs a more specific context than isolable in a small snippet, or (more
  likely, per the finding below) the actual trigger is the co-presence of a *second* pre-existing
  normed/valued bundle on `M`, which the isolated attempts didn't include.
- **Reproduced a genuine, clean diamond by registering both bundles at once** — mirroring what the
  real composition task requires: `M` needs the totally-ramified half's `Valued`/`RankOne`-based
  `NontriviallyNormedField M` (built via `Valued.mk' A.valuation` +
  `Valued.toNontriviallyNormedField`, the same route `exists_rankOne_absoluteValue_extends` already
  uses) **and** the general finiteness-only completeness result, which only comes from
  `spectralNorm.completeSpace`. Registering both `NontriviallyNormedField M` instances (`hnfValued`
  via `Valued.mk'`/`Valued.toNontriviallyNormedField`, `hnfSpectral` via
  `spectralNorm.nontriviallyNormedField`) in the same local context and then writing `haveI :
  CompleteSpace M := spectralNorm.completeSpace K M` gives, verbatim:
  ```
  error: Type mismatch
    spectralNorm.completeSpace K M
  has type
    @CompleteSpace M (spectralNorm.uniformSpace K M)
  but is expected to have type
    @CompleteSpace M this✝.toUniformSpace
  ```
  This is a **hard type mismatch, not a resolvable-by-more-unfolding defeq failure**: the expected
  type's `UniformSpace M` was resolved (via ordinary local-instance search, picking whichever
  `NontriviallyNormedField M`/`Valued M _` instance is in scope) to the `Valued`-route instance, while
  `spectralNorm.completeSpace K M`'s stated type is pinned to `spectralNorm.uniformSpace K M` — the
  metric space `spectralNorm.metricSpace K M`'s own `UniformSpace`, built from a completely different
  construction path (the abstract sup-over-embeddings spectral norm, `SpectralNorm.lean:644–940`) than
  `Valued.toNontriviallyNormedField`'s (built from the `RankOne`-normalized embedding of a concrete
  `ValuationSubring A : ValuationSubring M`). The eighteenth pass's wording ("not recognized as
  definitionally equal ... even though the two are propositionally identical") describes the same
  phenomenon at the point where a proof step needs the two to agree; this pass's error is the same
  mechanism caught one step earlier, as an outright type mismatch rather than a failed instance
  search.
- **Diagnosis: Lean/typeclass-resolution artifact, not a genuine mathematical ambiguity — but not a
  trivial one to dismiss either.** The two `NontriviallyNormedField M` structures represent the *same*
  norm mathematically: `spectralNorm_unique_field_norm_ext` (already used three times elsewhere in
  `HenselianValuation.lean`, e.g. `spectralNorm_lt_one_of_mem_nonunits`) proves any absolute value on
  `M` extending `‖·‖` on `K` — which the `Valued`-route norm is, by
  `exists_rankOne_absoluteValue_extends`'s own conclusion — equals `spectralNorm K M` pointwise. So the
  *values* agree provably; what doesn't automatically agree is the *Lean term* for the bundled
  `UniformSpace M` (or `MetricSpace M`, or `NontriviallyNormedField M`) instance, because
  `spectralNorm.nontriviallyNormedField` and `Valued.toNontriviallyNormedField` each construct their
  structure from scratch via unrelated code paths (`SpectralNorm.lean`'s anonymous-constructor merge
  off `(inferInstance : Field L)` vs. `Valued`'s uniformity machinery off a `Valuation`/`RankOne` pair)
  — there is no shared "attach this norm to the existing structure" constructor connecting them, only
  two independent ways to build a full bundle from lower-level data.
- **Checked for a Mathlib synonym-management tool that would close this generically** (the task's
  explicit ask): `NormedField.induced` exists (`Mathlib/Analysis/Normed/Field/Basic.lean`) — "an
  injective ring hom from a `Field` into an existing `NormedField` induces a `NormedField` structure on
  the domain" — but it *also* builds a fresh instance, so it doesn't itself dissolve a diamond between
  two already-built instances; it would need to be the *only* route taken (build `NormedField M` via
  `NormedField.induced` off the inclusion `M ↪ (whatever already-normed ambient field)`, never touching
  `spectralNorm.nontriviallyNormedField` directly) to avoid creating a second bundle at all —
  structurally the same idea as the already-known `Valued.mk'` workaround the user asked not to reach
  for as a patch, since it also routes around `spectralNorm` rather than reconciling with it.
  `UniformSpace.replaceTopology` (`Mathlib/Topology/UniformSpace/Defs.lean`) is the actual Mathlib
  primitive for "install a `UniformSpace` whose topology is *definitionally* a given, already-fixed
  `TopologicalSpace`, given a proof the propositional topologies agree" — the right shape of tool for
  this exact problem — but there is no `CompleteSpace`-level or `UniformSpace`-uniformity-level analogue
  (`UniformSpace.replaceUniformity`, `CompleteSpace.replaceUniformity` — checked via loogle, neither
  exists), so `replaceTopology` alone is not enough to transport *completeness* (a uniformity-level, not
  merely topology-level, property) from `spectralNorm.completeSpace` onto the ambient `Valued`-based
  uniform structure. Building that transport by hand — prove `spectralNorm K M = ‖·‖` pointwise on the
  `Valued`-route norm (available, per above), derive the two `dist` functions agree, get topology
  agreement then *uniformity* agreement (Cauchy-filter level, stronger than topology alone), and only
  then move `CompleteSpace` across — is real new proof work, comparable in size to what the eighteenth
  and eighteenth-pass status entries already flagged, not a lemma lookup.
- **Root-cause verdict:** the diamond is real, reproducible, and is a Lean/typeclass artifact (both
  sides are the same field with the same norm) rather than a genuine mathematical ambiguity — but
  resolving it "at the root" in the sense the task asked (not routing around via `Valued.mk'` /
  `NormedField.induced`, which both just relocate the problem to "never build the `spectralNorm`
  instance at all") requires writing the missing uniformity-level transport lemma by hand; Mathlib has
  the topology-level primitive (`UniformSpace.replaceTopology`) but not the uniformity/completeness-level
  one. This was not attempted this pass — it is a genuine, scoped, and nontrivial next milestone (build
  a `spectralNorm`-agrees-with-ambient-norm-therefore-same-uniformity-therefore-same-completeness
  lemma), not a redesign and not something closeable by finding an existing Mathlib name.
- **Next step for whoever picks this up:** state and prove, as a standalone lemma (independent of the
  rest of the tower-monogenicity composition), something like: given two `NontriviallyNormedField M`
  instances whose `‖·‖` functions agree pointwise (by `funext` from `spectralNorm_unique_field_norm_ext`
  applied to the `Valued`-route absolute value), their `UniformSpace M` instances are equal as terms
  (via a `UniformSpace`/`PseudoMetricSpace` `ext`-style lemma keyed on `dist`, e.g. check for
  `PseudoMetricSpace.ext`/`UniformSpace.ext` and whether `dist` uniquely determines the uniformity for a
  `NontriviallyNormedField`), then `▸`-transport `spectralNorm.completeSpace`'s `CompleteSpace` instance
  across that equality onto the ambient one. This is the "different construction route" the eighteenth
  pass's `Valued.mk'` note gestured at, done as a genuine bridge rather than a substitution.

#### Status 2026-08-06 (twentieth pass) — the missing uniformity-level transport lemma landed; the
diamond closes cleanly, including the concrete repro. `Langlands/HenselianValuation.lean` gained a
new `UniformSpaceTransport` section (two theorems, no `sorry`, builds clean via `lake build
Langlands.HenselianValuation`). No `sorry` anywhere in the file.

- **Verified both loogle-found lemmas the nineteenth pass identified**, by re-grepping this
  project's vendored Mathlib rather than trusting the prior report: `PseudoMetricSpace.ext`
  (`Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:157`, `{m m' : PseudoMetricSpace α} (h :
  m.toDist = m'.toDist) : m = m'`, tagged `@[ext]`) and `UniformSpace.ext`
  (`Mathlib/Topology/UniformSpace/Defs.lean:249`, `{u₁ u₂ : UniformSpace α} (h : 𝓤[u₁] = 𝓤[u₂]) :
  u₁ = u₂`) both exist with exactly the stated signatures. Also reconfirmed by reading source (not
  just the prior report) that `spectralNorm.normedField` (`SpectralNorm.lean:851`) sets `dist`
  directly and does not override `toUniformSpace`, while `Valued.toNormedField`
  (`NormedValued.lean:149–165`) explicitly overrides `toUniformSpace := Valued.toUniformSpace` — the
  two non-defeq construction routes the diamond is between.
- **Reproduced the diamond first-hand** in a scratch file (`lake env lean`, deleted after, not
  committed): registering `hnfValued := Valued.toNontriviallyNormedField M A.ValueGroup` and
  `hnfSpectral := spectralNorm.nontriviallyNormedField K M` in the same context and writing `haveI :
  CompleteSpace M := spectralNorm.completeSpace K M` reproduces verbatim the nineteenth pass's error
  (`Type mismatch ... has type @CompleteSpace M (spectralNorm.uniformSpace K M) but is expected to
  have type @CompleteSpace M this.toUniformSpace`).
- **Landed the general transport lemma, proved and building**, in a new `UniformSpaceTransport`
  section of `HenselianValuation.lean` (after `ReusableInfrastructure`, before
  `NormedFieldValuativeRelBridge`):
  ```
  theorem PseudoMetricSpace.toUniformSpace_eq_of_toDist_eq {α : Type*} {m m' : PseudoMetricSpace α}
      (h : m.toDist = m'.toDist) : m.toUniformSpace = m'.toUniformSpace := by
    rw [PseudoMetricSpace.ext h]

  theorem CompleteSpace.of_pseudoMetricSpace_toDist_eq {α : Type*} {m m' : PseudoMetricSpace α}
      (h : m.toDist = m'.toDist) (h' : @CompleteSpace α m'.toUniformSpace) :
      @CompleteSpace α m.toUniformSpace :=
    (PseudoMetricSpace.toUniformSpace_eq_of_toDist_eq h).symm ▸ h'
  ```
  The first is `PseudoMetricSpace.ext` composed with `toUniformSpace`; the second `▸`-transports a
  `CompleteSpace` instance across the resulting equality. Both are proved with no `sorry` and no
  unfinished goals.
- **Verified the transport actually closes the concrete diamond, not just the abstract shape**: in
  the same scratch file, after obtaining `hR`/`hcompat` from the already-proved
  `LocalField.exists_rankOne_compatible`, building `hnfValued` via `Valued.mk'` +
  `Valued.toNontriviallyNormedField`, and `hnfSpectral` via `spectralNorm.nontriviallyNormedField`,
  the pointwise norm equality `∀ y : M, ‖y‖ = spectralNorm K M y` follows from
  `spectralNorm_unique_field_norm_ext` applied to `f := NormedField.toAbsoluteValue M` (the same
  `f` `exists_rankOne_absoluteValue_extends` already builds internally) together with `hcompat`;
  `ext x y` (the `Dist` structure's own `@[ext]` lemma — plain `funext` does not apply to a `Dist`
  record) turns that into `hnfValued.toDist = hnfSpectral.toDist`; and
  `CompleteSpace.of_pseudoMetricSpace_toDist_eq` applied to that plus `spectralNorm.completeSpace K
  M` produces `CompleteSpace M` under `hnfValued.toUniformSpace` (the `Valued`-route uniform
  structure) with **zero errors, zero `sorry`, zero warnings**. This is a strictly stronger
  confirmation than the nineteenth pass's diagnosis-only pass: the fix is not just plausible in
  shape, it discharges the exact failing goal from the exact reproduced diamond.
- **Not wired into a permanent theorem in this file**: the concrete repro's surrounding hypotheses
  (`A : ValuationSubring M`, `FiniteDimensional K M`, etc., mirroring what
  `exists_rankOne_absoluteValue_extends` already assumes) don't correspond to any existing theorem
  statement in this file, and pinning a *permanent* `CompleteSpace L` conclusion would require
  deciding which `UniformSpace L` instance the statement is stated relative to (the whole diamond is
  that there are two, and nothing yet makes one of them the file's canonical choice) — a design
  decision distinct from "does the transport lemma work," which this pass answers unambiguously yes.
  That composition (assembling a permanent `exists_bundle_of_finiteDimensional`-shaped theorem, the
  eighteenth pass's original target) remains open, but the specific technical wall the seventeenth
  through nineteenth passes hit is now closed.
- **Next step for whoever picks this up:** use `CompleteSpace.of_pseudoMetricSpace_toDist_eq` to
  finish assembling `exists_bundle_of_finiteDimensional` (or an equivalent), deciding explicitly
  which `NontriviallyNormedField M` instance (the `Valued`-route one, matching this file's other
  theorems' pattern) is canonical at the point `CompleteSpace M` is asserted, and the separate,
  unrelated `IsDiscreteValuationRing` half the seventeenth/eighteenth passes flagged as needing real
  new proof work (not a composition or lemma-lookup question).

#### Status 2026-08-06 (twenty-first pass) — the permanent completeness-transport theorem landed
(zero `sorry`); the tower composition (step 3) got substantially further than any prior pass —
three of the bundle's five open pieces close cleanly, one closes with a scoped, undischarged proof
sketch, and only the acknowledged `IsDiscreteValuationRing` half remains a genuinely new
mathematical gap. Nothing forced; the one scratch file used to verify all of this
(`Langlands/ZZScratch.lean`) was deleted after verification, not committed.

- **Landed `LocalField.exists_completeSpace_of_finiteDimensional`** (`HenselianValuation.lean`,
  commit `a5df40e`), assembling the twentieth pass's `UniformSpaceTransport` lemmas into the
  permanent theorem the twentieth pass's "next step" asked for:
  ```
  theorem exists_completeSpace_of_finiteDimensional [CompleteSpace K] [Algebra.IsAlgebraic K L]
      [FiniteDimensional K L] (A : ValuationSubring L)
      (hA : A.comap (algebraMap K L) = (valuation K).valuationSubring) :
      @CompleteSpace L (Valued.mk' A.valuation).toUniformSpace
  ```
  in the `NormedFieldBridge` section (variable block: `[NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]`). Design
  choice (documented in the theorem's docstring): the conclusion names the `UniformSpace` term
  explicitly (`(Valued.mk' A.valuation).toUniformSpace`) rather than taking it as an ambient
  instance argument, since `Valued.mk' A.valuation` needs no `RankOne` instance to fix `L`'s uniform
  structure — `RankOne` is only needed inside the proof, to build the *normed*-field structure
  compared against `spectralNorm`. A caller who has already done `letI := Valued.mk' A.valuation`
  (the pattern `exists_rankOne_absoluteValue_extends`'s own downstream callers already use) gets
  `CompleteSpace L` with one line, no `letI` chain to repeat. The proof inlines the same `hR` from
  a single call to `exists_rankOne_compatible` for both the `Valued`-route `NontriviallyNormedField`
  and the `f := NormedField.toAbsoluteValue L` used in `spectralNorm_unique_field_norm_ext` (rather
  than calling `exists_rankOne_absoluteValue_extends` as a black box a second time), so the two are
  provably built from the same witness rather than merely propositionally-equal witnesses of two
  separate existentials. One real friction point building it: with two `NontriviallyNormedField L`
  instances (`hnfValued`, `hnfSpectral`) simultaneously in local context, bare `‖·‖`/`dist` notation
  is ambiguous (resolves to whichever instance typeclass search prefers, not necessarily the
  intended one) — every `L`-typed norm/dist in the proof is pinned explicitly (`@norm L
  hnfValued.toNorm`, `Dist.ext (funext ...)` instead of the `ext` tactic) rather than written via
  bare notation, after two build failures from exactly this ambiguity (not a repeated-identical
  error in the stop-on-repeat sense — each attempt's error message differed slightly since the
  elaborator's ambient-instance guess differed by position in the proof — but the same root cause).
  `lake build Langlands` clean (8676 jobs); `grep -rn sorry langlands/Langlands/` empty.
- **New finding closing half of the "existence of `A`" question the eighteenth/nineteenth passes
  never posed:** `Langlands/WeilGroup.lean` already contains
  `LocalField.exists_valuationSubring_extends`/`valuationSubringExtension` — Chevalley's extension
  theorem (`IsLocalRing.exists_factor_valuationRing` composed with a locality argument), proved
  there for `L := AlgebraicClosure K` via a `local notation`, but the proof itself uses nothing
  specific to `AlgebraicClosure` (only `[Field K] [Field L] [Algebra K L]` and `𝒪[K]`'s own
  `mem_or_inv_mem`). For `M := IntermediateField K (AlgebraicClosure K)` (the unramified
  subextension `UnramifiedExtension.lean:715` builds, always literally a subfield of
  `AlgebraicClosure K`), **`A_M := (valuationSubringExtension K).comap (algebraMap M
  (AlgebraicClosure K))` satisfies `A_M.comap (algebraMap K M) = 𝒪[K]` exactly**, by
  `ValuationSubring.comap_comap` plus `IsScalarTower.algebraMap_eq K M (AlgebraicClosure K)` plus
  `valuationSubringExtension_comap` — three existing lemmas, no new proof content. This means the
  tower composition does **not** need a fresh "does a valuation extension exist on `M`" argument at
  all; it can reuse the existing `AlgebraicClosure K`-level extension by restriction. (Verified
  end-to-end in the deleted scratch file, not merely asserted.)
- **Verified, by direct construction in the scratch file, that with this `A_M` the following close
  with *zero* new proof content** (each is a literal copy of the K-side construction already used
  by `valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField`, `WeilGroup.lean`'s own pattern
  for `K`, substituting `A_M`/`M` for `Valued.v`/`K`):
  1. `hA_M_comap : A_M.comap (algebraMap K M) = 𝒪[K]` (as above).
  2. `hCompleteM : CompleteSpace M` (relative to `Valued.mk' A_M.valuation`'s uniform space) — one
     call to the twenty-first pass's own new `exists_completeSpace_of_finiteDimensional K A_M
     hA_M_comap`, needing only `[CompleteSpace K] [Algebra.IsAlgebraic K M] [FiniteDimensional K M]`,
     all already in hand.
  3. The `Valued M A_M.ValueGroup`/`NontriviallyNormedField M`/`IsUltrametricDist M` bundle, via
     `hRM := (exists_rankOne_compatible K A_M hA_M_comap).choose`, then `Valued.mk'`/
     `Valued.toNontriviallyNormedField`, exactly as `exists_rankOne_absoluteValue_extends` builds it.
  4. `hMCompat : (NormedField.valuation (K := M)).Compatible` — with `ValuativeRel M :=
     ValuativeRel.ofValuation (NormedField.valuation (K := M))`, the identical `hnorm`/
     `NormedField.valuation_compatible_of_eq_rankOne_hom_comp_restrict` argument
     `valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField` uses for `K` closes for `M`
     verbatim (`Valued.coe_valuation_eq_rankOne_hom_comp_valuation` supplies `hnormM`).
  With 1–4 in hand, `@LocalField.adjoin_eq_integralClosure_of_isUniformizer M _ _ _ hMCompat _ N _ _
  hMalgN _ _` (for `N` an arbitrary further finite separable extension of `M`, standing in for a
  totally ramified extension) **type-checks completely** as soon as two more facts are supplied —
  confirmed by elaborating the full application with those two facts abstracted as universally
  quantified hypotheses (i.e. the composed statement's *shape* is sound; only content is missing):
  - `hvalM : (ValuativeRel.valuation M).valuationSubring = A_M` — **not closed, but precisely
    scoped**: unlike 1–4, this needs one step beyond direct reuse of the `K`-side pattern, because
    `ValuativeRel.valuation M` (the canonical valuation the `ValuativeRel` typeclass derives from
    `ofValuation`'s `vle` relation) is not launched from `A_M.valuation` itself but from
    `NormedField.valuation (K := M)`. The scoped route: `ValuationSubring.ext` reduces this to `∀ x,
    NormedField.valuation x ≤ 1 ↔ x ∈ A_M`, which `Valued.toNormedField.norm_le_one_iff` (already
    used for exactly this purpose in `exists_rankOne_absoluteValue_extends`) plus
    `A_M.valuation_le_one_iff` should discharge directly, *without* needing `ValuativeRel.isEquiv`
    or any new lemma — not attempted to completion this pass, but no obstruction was hit in scoping
    it, only budget.
  - `hDVR : IsDiscreteValuationRing ↥(ValuativeRel.valuation M).valuationSubring` (`= ↥A_M` given
    `hvalM`) — **the one piece confirmed to need genuinely new mathematical content**, exactly as
    the eighteenth/nineteenth passes flagged, now precisely pinned to a *specific, concretely
    constructed* `A_M` rather than an abstract unnamed valuation subring. Re-confirmed via loogle
    this pass (`IsCyclic, ValuationSubring.ValueGroup, FiniteDimensional` and `IsCyclic,
    MonoidWithZeroHom.ValueGroup₀, FiniteDimensional` both 0 hits) that Mathlib has no
    "finite extension of a discretely-valued field has cyclic value group" theorem feeding
    `Valuation.valuationSubring_isDiscreteValuationRing`'s `[IsCyclic ↥ValueGroup₀] [Nontrivial
    ↥ValueGroup₀]` hypotheses. **Correction to the eighteenth/nineteenth passes' framing**: closing
    this does *not* require reconciling `A_M` with `integralClosure R M` from
    `UnramifiedExtension.lean:715` (the DVR that file already builds) — `TotallyRamifiedEisenstein`'s
    theorem only ever needs `IsDiscreteValuationRing ↥(valuation M).valuationSubring` for whichever
    `ValuativeRel M` is in scope, and with `A_M` fixed as that valuation subring directly, the
    question is self-contained: is `A_M`'s value group cyclic and nontrivial? No reconciliation with
    a *different* ring is needed at all. This narrows, rather than duplicates, prior passes' framing
    of the gap.
- **Next step for whoever picks this up:** close `hvalM` via the sketched
  `Valued.toNormedField.norm_le_one_iff`/`A_M.valuation_le_one_iff` route (small, no new idea
  needed), then attack `hDVR` directly as "is `A_M.ValueGroup` cyclic and nontrivial, given `M/K`
  finite and `𝒪[K]`'s value group cyclic/nontrivial" — likely via a bounded-index argument using
  `Valuation.exists_pow_eq_of_isAlgebraic` (already in `HenselianValuation.lean`: every element of
  `L` is dominated exactly by a `K`-power up to degree `[M:K]`), which bounds how far `A_M`'s value
  group can diverge from a cyclic group of the same rank — this is the actual remaining
  mathematical content, not a lookup.

### Phase 2.5 — Satake isomorphism for unramified `GL_n` (new milestone, review addition)
- **Build:** the unramified Hecke algebra `H(GL_n(K_v), GL_n(𝒪_v))` (the
  double-coset convolution algebra of `GL_n(K_v)` relative to the maximal
  compact `GL_n(𝒪_v)`) and the Satake isomorphism identifying it with the
  ring of symmetric polynomials in `n` variables (equivalently, with
  representations of the dual torus/Weyl-invariant functions on it — for
  `GL_n` the dual group is again `GL_n`, so this needs none of Phase 3).
- **Why it goes here:** this is the best value-per-effort item in the whole
  roadmap. It is **self-contained** — needs only `GL_n(K_v)`'s double-coset
  structure, the existing `HeckeRing/Defs.lean` abstract Hecke-ring formalism
  (have, §1.6), and Mathlib's polynomial-ring/symmetric-function library
  (not audited above but standard Mathlib territory) — and it **yields a
  provable theorem**, not just a stated conjecture: the unramified local
  Langlands correspondence (Satake parameters ↔ unramified irreducible
  admissible representations) drops out of the Satake isomorphism directly,
  giving the roadmap its first genuine, non-vacuous local Langlands result
  well before the general Phase 5 statement is reachable.
- **Depends on:** `NumberTheory/HeckeRing/Defs.lean` (have), Phase 4's
  `GL_n`-track admissible representations (for the unramified-representations
  side of the correspondence), `GeneralLinearGroup` (have). Does **not**
  depend on Phase 3.
- **Feeds:** the unramified case of Phase 5's local Langlands statement
  (directly, as a proved special case rather than a stated conjecture), and
  Phase 8's restricted tensor products (an automorphic representation is
  unramified — i.e. has a fixed vector under the maximal compact — at almost
  all places, and the Satake isomorphism is exactly what controls the local
  factor at those places).
- **Size:** medium. Bounded, classical, and well-documented in standard
  references (Bump's *Automorphic Forms*, Gelbart's `GL_2` notes generalize
  cleanly to `GL_n`).
- **Upstreamable:** yes — the Satake isomorphism is a named, citable result
  independent of the rest of Langlands.

### Phase 3 — Reductive groups over a field (the dual-group blocker)
- **Build, in order:**
  1. Algebraic tori (split first: `𝔾_m^n` with a Galois action for
     non-split), as group schemes or as functor-of-points objects.
  2. Root data: pair a torus with the existing `RootSystem` combinatorial
     library (`Mathlib/LinearAlgebra/RootSystem/*` — have) via cocharacter/
     character lattices.
  3. Split reductive groups classified by root data (Chevalley); construct
     `GL_n`, `SL_n`, `Sp_{2n}`, `SO_n` as the running examples on top of the
     existing concrete matrix groups (have, §1.4) to validate the
     abstraction against known cases.
  4. The Langlands dual group `^L G` as the reductive group with dual root
     datum (roots ↔ coroots swapped); for split `G`, `^L G` needs no Galois
     action, for quasi-split/general `G` the dual carries an action of
     `Gal(K̄/K)` on the based root datum (needs Phase 1's Galois group +
     pinnings/automorphisms of the root datum — new).
- **Depends on:** `LinearAlgebra/RootSystem/*` (have), `GeneralLinearGroup`/
  `SpecialLinearGroup` (have, as validation targets), `AbsoluteGaloisGroup`
  (have, for step 4), essentially nothing else in Mathlib — this is mostly
  new development on top of the root-system library.
- **Size:** huge. This is comparable in scope to formalizing a chapter of
  Springer's *Linear Algebraic Groups* or Conrad's reductive-groups notes.
  Plausibly the single biggest piece of the entire roadmap. Can be
  meaningfully de-scoped: build split reductive groups classified by root
  data first (skip general algebraic-group/scheme foundations, skip
  non-split forms), which is enough to state local/global Langlands for
  quasi-split groups — the case almost all conjecture *statements* (not
  proofs) are given in.
- **Upstreamable:** yes, extremely high-value — Mathlib has no reductive
  group theory at all; this would be a foundational new area, not a
  patch to an existing one. Also the piece most likely to already be
  wanted by other Mathlib contributors (algebraic geometry / Lie theory
  communities) — worth checking Mathlib's Zulip/roadmap for parallel effort
  before starting, since duplicating a large in-flight project would be
  the worst outcome here.
- **Reframing (review):** this is not a project phase in the same sense as
  the others in this roadmap — it is a **Mathlib-core campaign**. The dual
  group `^L G` needs Chevalley existence/uniqueness for reductive groups
  built from root data, and that is Mathlib's largest relevant crater: as of
  this writing there is no settled maintainer consensus even on the base
  definitions (what a "reductive group" *is* as a Mathlib structure — scheme-
  theoretic vs. functor-of-points vs. combinatorial-root-datum-first — is an
  open design question upstream, not just an unfilled gap). Treating Phase 3
  as a phase this project completes on its own timeline is the wrong frame;
  treating it as an upstream Mathlib contribution this project seeds and
  budgets for indefinite duration is the right one.
  - **Mitigation (a) — decouple the Galois layer from group existence.**
    Define `^L G` *combinatorially* now: a dual root datum, built directly on
    the existing `RootSystem` API (have, §1.4), with the Galois action on it
    given by an action on the abstract based root datum (needed anyway for
    step 4 above). This lets everything downstream that only needs `^L G` as
    a group *with a root datum* (L-parameters, functoriality maps between
    dual sides) proceed without waiting on Chevalley's theorem — i.e. without
    waiting on `G` itself existing as a bona fide reductive group object.
    Only the "transfer of representations of `G(K_v)` itself" side of local
    Langlands needs `G`, not `^L G`, to exist as a group scheme.
  - **Mitigation (b) — budget, don't schedule.** Treat full Phase 3 (Chevalley
    existence + uniqueness for general reductive groups) as an upstream
    Mathlib contribution with its own review cycle and timeline, not a task
    this roadmap can complete unilaterally. Phase 7 (Galois cohomology
    packaging) correctly feeds only the non-split-forms case of Phase 3 and
    can lag indefinitely without blocking anything else in this roadmap.

### Phase 4 — Smooth and admissible representations of `p`-adic / adelic groups
- **Build:** for a locally profinite group `H` (e.g. `G(K_v)` once Phase 3
  exists, or concretely `GL_n(K_v)` before Phase 3 lands), a smooth
  representation = a representation on which every vector is fixed by some
  compact open subgroup; admissible = smooth + finite-dimensional fixed
  spaces under every compact open subgroup.
- **Depends on:** `RepresentationTheory/Continuous/{Basic,TopRep}.lean`
  (have — specialize `TopRep` to locally profinite groups and add the
  smoothness condition), `ProfiniteGrp`/compact-open-subgroup topology
  (have, for `GL_n` over `Padics`, §1.2).
- **Size:** medium–large for the `GL_n`-only version (usable immediately,
  doesn't wait on Phase 3); large again for the general-`G` version once
  Phase 3 exists (parabolic induction, Jacquet modules, supercuspidal
  support, Bernstein decomposition needed for the *full* local Langlands
  statement with L-packets, though the bijection can be *stated* for
  `GL_n` without any of that extra machinery, since local Langlands for
  `GL_n` is a clean bijection with no packets).
- **Upstreamable:** yes — smooth/admissible representation theory of
  `p`-adic groups is foundational and wanted independently of Langlands.

### Phase 4.5 — Local L-factors and ε-factors (review addition — vacuity fix for Phase 5)
- **Why this phase exists:** a bare bijection between `L`-parameters and
  irreducible admissible representations of `GL_n(K_v)`, with no further
  structure, is **vacuously true by cardinality** — both sides are countably
  infinite sets, so *some* bijection trivially exists with no mathematical
  content. The actual content of local Langlands for `GL_n` (this is
  Henniart's uniqueness theorem territory) lives in the correspondence being
  the *unique* bijection compatible with: twisting by characters, duality
  (contragredient ↔ dual representation), central characters
  (determinant ↔ central character under class field theory), and
  **preservation of L-factors and ε-factors of pairs** under the
  correspondence. Without this phase, Phase 5 cannot distinguish a genuine
  statement of local Langlands from a cardinality triviality.
- **Build:** local L-factors `L(s, ρ)` and Deligne–Langlands ε-factors
  `ε(s, ρ, ψ)` for Weil–Deligne representations `ρ`, and their representation-
  theoretic counterparts (Rankin–Selberg / Godement–Jacquet local factors)
  for admissible representations of `GL_n(K_v)` and `GL_n(K_v) × GL_m(K_v)`
  pairs.
- **New prerequisites, confirmed missing:** additive characters of `K_v`
  (have for `K_v = ℚ_p` via `Padics/AddChar.lean`, §1.2, but not for general
  local fields), a Haar measure normalization convention (Tate's thesis
  requires a self-dual measure with respect to the chosen additive
  character — flagged as missing in §1.3), and the local functional equation
  relating `L(s, ρ)` to `L(1-s, ρ^∨)` via the ε-factor.
- **Convention hazard, flagged for whoever picks this up:** Tate's original
  thesis normalization and Deligne's later ε-factor formalism (*Les
  constantes des équations fonctionnelles des fonctions L*, Antwerp II)
  diverge in bookkeeping conventions (choice of additive character, measure
  normalization, and sign/exponent conventions on the local root number) —
  this is a well-known source of errors in the literature, so the Lean
  definitions must pin down *which* convention is being formalized and state
  it explicitly rather than silently inheriting one source's choices.
- **Depends on:** Phase 1 (Weil–Deligne group, for the Galois side), Phase 4
  (admissible representations of `GL_n(K_v)`, for the automorphic side),
  `Padics/AddChar.lean` and `Padics/Measure/*` (have, for `ℚ_p`; need
  extending to general local fields), `NumberTheory/LSeries/
  AbstractFuncEq.lean` (have, potential scaffold for the functional
  equation).
- **Size:** large — this is a full local-constants theory, comparable in
  scope to a chapter of Bushnell–Henniart's *The Local Langlands Conjecture
  for GL(2)* or Tate's Corvallis article.
- **Upstreamable:** yes — local L- and ε-factors are foundational and wanted
  independently (Tate's thesis itself is a natural, self-contained Mathlib
  target).

### Phase 5 — Statement of local Langlands for `GL_n`
- **Build:** the conjecture-as-a-`Prop`: a bijection between (continuous,
  Frobenius-semisimple, Weil–Deligne) `n`-dimensional representations of
  `W_{K_v}` and irreducible admissible representations of `GL_n(K_v)`,
  compatible with L-functions and ε-factors on both sides (the compatibility
  clause can initially be omitted/stubbed to get the bare bijection
  statement first).
- **Vacuity caveat (review) — acceptance test:** per Phase 4.5 above, a bare
  bijection is **not an acceptable formalization goal on its own** — both
  sides are countably infinite, so a bijection exists trivially by
  cardinality with zero mathematical content. Two ways to avoid shipping a
  vacuous statement:
  1. Do the full version: require Phase 4.5's L-factor/ε-factor compatibility
     clauses (plus twisting, duality, central-character compatibility) as
     part of the `Prop`, so the bijection is characterized, not just
     asserted. This is Henniart's uniqueness theorem and is the
     mathematically honest statement of local Langlands for `GL_n`.
  2. Or explicitly scope Phase 5 as "the bijection statement up to
     characterization" — i.e. keep the bare bijection as an intentionally
     weaker placeholder, but **label it as such in the `Prop`'s
     documentation** (e.g. a doc-comment noting "this statement, absent the
     compatibility clauses of Phase 4.5, is a cardinality triviality and
     should not be cited as a formalization of local Langlands without
     them"), so nobody downstream mistakes the placeholder for the theorem.
  Either path is acceptable; shipping the bare bijection *without* one of
  these two markers is not — that is exactly the failure mode this
  correction targets.
- **Depends on:** Phase 1 (Weil–Deligne group), Phase 4's `GL_n`-only track
  (admissible reps of `GL_n(K_v)`), Phase 4.5 (L-/ε-factors, for the
  non-vacuous version), existing `GeneralLinearGroup` (have).
  **Does not need Phase 3** — this is exactly why `GL_n` is the right first
  target: its own dual group is itself.
- **Size:** small, once Phases 1 and 4 (`GL_n` track) exist, *for the bare
  bijection*; the non-vacuous version additionally needs Phase 4.5, which is
  large. This phase is "just" writing the `Prop` only in the weak sense —
  writing the `Prop` that is actually worth writing is gated on Phase 4.5.
- **Upstreamable:** yes, as a formalized *conjecture statement* (a `Prop`/
  axiom-free `def`, not a `sorry`-laden proof) — valuable in its own right
  as a landmark for the Mathlib number theory community, independent of any
  progress toward proving it, **provided** the vacuity caveat above is
  respected.

### Phase 6 — Statement of Artin's conjecture
- **Build:** Artin `L`-function of an `n`-dimensional Galois representation
  `ρ : Gal(K̄/K) → GL_n(ℂ)` (Euler product over unramified primes using
  Frobenius eigenvalues from `RingTheory/Frobenius.lean`, plus local factors
  at ramified primes needing the **inertia-invariants** of `ρ` restricted to
  `W_{K_v}` — needs Phase 1); state "`L(s, ρ)` equals `L(s, π)` for some
  automorphic representation `π` of `GL_n(𝔸_K)`" (needs Phase 8's global
  automorphic-representation notion, or can be stated over `GL_1` alone
  first, which reduces to classical Hecke-character CFT and needs only
  Phase 0 + Phase 2).
- **Depends on:** Phase 1, Phase 2 (for the `n=1` reduction — Artin's
  conjecture for 1-dim reps is essentially class field theory, already a
  theorem, not a conjecture, once Phase 2 lands), `NumberTheory/LSeries/
  AbstractFuncEq.lean` (have, as a scaffold for the L-function's analytic
  side), Phase 8 for `n > 1`.
- **Size:** medium for `n=1` statement/proof (mostly repackaging Phase 0/2);
  large for general `n` statement (needs Phase 8).
- **Upstreamable:** yes — Artin `L`-functions are independently notable.

### Phase 7 — Galois cohomology packaging (parallel track, low risk)
- **Build:** name and package `Gal(L/K)`-module cohomology as "Galois
  cohomology" explicitly (thin wrapper over `ContCohomology` +
  `AbsoluteGaloisGroup`), including inflation-restriction, and connect
  `Hilbert90.lean` to the `H^1(Gal, GL_n)`-classifies-forms statement
  (relevant to inner forms / non-quasi-split reductive groups in Phase 3).
- **Depends on:** `RepresentationTheory/Homological/ContCohomology/*`
  (have), `AbsoluteGaloisGroup` (have), `GroupCohomology/Hilbert90.lean`
  (have).
- **Size:** small–medium. Can run **in parallel** with Phases 0–2; no
  dependency either direction except that Phase 3's non-split forms will
  eventually want it.
- **Upstreamable:** yes, cheap win — Mathlib already has all the pieces,
  just not the "Galois cohomology" framing/API surface.

### Phase 8 — Automorphic representations of `G(𝔸_K)` and statement of global Langlands
- **Build:** automorphic forms/representations for general reductive `G`
  (functions on `G(K)\G(𝔸_K)` satisfying finiteness/growth/smoothness
  conditions, decomposed into irreducible representations of `G(𝔸_K)`);
  reconcile with the classical modular-forms library (§1.6) for `G = GL_2`
  as the validating special case; state the global correspondence as a
  `Prop` relating automorphic representations to (compatible systems of)
  Galois representations, using local Langlands (Phase 5, generalized via
  Phase 3+4) at each place for compatibility.
- **Depends on:** Phase 0 (adeles/idele class group), Phase 3 (reductive
  groups, for general `G`; `GL_2` case can lean on existing modular forms
  instead), Phase 4 (admissible representations, adelic/restricted-tensor-
  product version — new content: an automorphic representation is a
  restricted tensor product of local admissible representations, which
  needs its own "almost all factors unramified" bookkeeping).
- **Acceptance criteria (review) — vacuity test:** "automorphic
  representations" defined as a bare restricted tensor product of local
  admissible representations, with no further structure, is a definition
  with no theorem in it — it says nothing about which restricted tensor
  products actually arise from genuine automorphic forms. The content that
  must be present before this phase counts as done:
  - **Cuspidality:** the subspace of cusp forms (vanishing constant terms
    along all proper parabolics) must be identified, since the cuspidal
    spectrum is where the representation theory is discrete and where local
    Langlands packets are meant to land; without it, "automorphic
    representation" has no home for the actual correspondence.
  - **Multiplicity:** the multiplicity of an irreducible representation in
    the (cuspidal) automorphic spectrum must be at least stated as a
    quantity (finite for cuspidal, by a Gelfand-pair/discrete-spectrum
    argument), even if multiplicity-one (known for `GL_n`, false in general)
    is deferred as a separate theorem.
  - **L² structure:** the decomposition of `L²(G(K)\G(𝔸_K))` (or its
    central-character-twisted variant) into a direct sum/integral of
    irreducibles — discrete spectrum (cuspidal + residual) plus continuous
    (Eisenstein) spectrum — needs to be at least stated, since "automorphic
    representation" without reference to this decomposition is just "some
    representation of `G(𝔸_K))`," not the object Langlands' conjectures are
    about.
  Absent these three, Phase 8 produces a restricted tensor product with no
  theorem attached to it — a definition that type-checks but proves nothing
  and characterizes nothing. These three items should be treated as the
  minimum bar for calling Phase 8 "done" rather than "stated."
- **Size:** huge — the single most mathematically demanding phase, on par
  with or larger than Phase 3. Realistically this is where "prove what we
  can" gives way to "state what we can" for the foreseeable future.
- **Upstreamable:** yes, high-value, but high risk of drift/duplication
  with any parallel effort elsewhere (geometric Langlands formalization
  projects exist outside Mathlib, e.g. in other proof assistants and in
  active math research — worth a literature/community check before
  committing large effort here specifically).

### Phase 9 — Functoriality statement
- **Build:** given `L`-map `^L H → ^L G` (a homomorphism of dual groups from
  Phase 3), state functorial transfer of automorphic representations
  (Phase 8) and/or of L-parameters (Phase 5, generalized).
- **Depends on:** Phase 3 (dual groups + homs between them), Phase 5/8
  generalized to arbitrary reductive `G`.
- **Size:** small once Phases 3, 5 (generalized), and 8 exist — again,
  "just" the `Prop`, but it sits at the end of the longest dependency chain
  in the whole roadmap.
- **Upstreamable:** yes.

---

## 4. Roadmap dependency graph (summary)

```
Phase 0 (idele class group) — COMPLETE ────────────────┐
   built: IdeleGroup/IdeleClassGroup, norm maps          │
   (finite + archimedean places), unramified-ext.        │
   correspondence, Henselian valuation compat.           ▼
Phase 1 (Weil/Weil–Deligne group) — COMPLETE            Phase 2 (local CFT / Artin map)
   built: WeilGroup, WeilDeligneRepresentation             depends on: Phase 1 (done), BrauerGroup
   depends on: AbsoluteGaloisGroup (have),        (have), Hilbert90 (have) — scope: also norm
   ProfiniteGrp (have), Frobenius (have)          functoriality + Frobenius compat (Serre
        │                                          Local Fields VIII–XIII); norm maps +
        │                                          unramified-ext. correspondence now available
        │                                          (Phase 0) as down payment; check FLT-adjacent
        │                                          CFT formalization before building
        │                                                │
        │                                                ▼
        │                                       Phase 2.5 (Satake isomorphism for
        │                                       unramified GL_n — new, self-contained,
        │                                       first PROVABLE unramified LLC)
        ├──────────────┬─────────────────────────────────┘
        ▼              ▼
Phase 4.5 (local L-/ε-factors — new, fixes  Phase 6 (state Artin conj., n=1 track
Phase 5 vacuity; needs additive characters,   reduces to Phase 0+2; n>1 needs Phase 8)
Haar normalization, functional equation;
Tate-vs-Deligne convention hazard flagged)
        │
        ▼
Phase 5 (state local Langlands for GL_n —
bare bijection is VACUOUS by cardinality;
needs Phase 4.5's compatibility clauses or
an explicit "up to characterization" label)
        ▲
        │
Phase 4 (smooth/admissible reps; GL_n track needs no Phase 3)
        ▲
        │
Phase 3 (reductive groups + dual group)  ◄── Mathlib-CORE CAMPAIGN, not a project
   depends on: RootSystem (have), GeneralLinearGroup (have), AbsoluteGaloisGroup (have)   phase: Chevalley existence/uniqueness has
        │                                                                                  no settled upstream maintainer consensus.
        ▼                                                                                  Mitigation: define ^L G combinatorially now
Phase 4 (general-G track)  ──►  Phase 8 (automorphic reps, global Langlands —              via dual root datum (decouples from Chevalley);
acceptance test: needs cuspidality,           ──►  Phase 9 (functoriality)                 budget rest as upstream PR, not in-repo work.
multiplicity, L² structure — bare restricted
tensor product has no theorem in it)
                                        ▲
                                        │
                                 Phase 0 (idele class group)

Phase 7 (Galois cohomology packaging) — parallel, low-risk, feeds Phase 3's non-split-forms case only, can lag indefinitely.
```

Everything downstream of Phase 3 for **general `G`** is gated on Phase 3.
Everything needed to state local/global Langlands **for `GL_n` specifically**
(Phases 0, 1, 2, 2.5, 4-GL_n-track, 4.5, 5, 6-n=1-track) can proceed without
ever touching Phase 3 — this is the practical route to "formally state the
core conjectures" fastest, deferring the huge, contested Phase 3 (general
reductive groups, reframed above as a Mathlib-core campaign rather than a
project phase) and Phase 8 (general automorphic representations) until later
or indefinitely, while still landing a real, citable formal statement of
local Langlands for `GL_n` and (via Phase 2) a fully *proved* class field
theory. Phase 2.5 (Satake for unramified `GL_n`) is flagged separately as
the single best value-per-effort item in the graph: self-contained, needs no
Phase 3, and yields an actually-provable theorem rather than another stated
conjecture.

---

## 5. The first move

**Status update: Phase 0 (idele class group) and Phase 1 (Weil group /
Weil–Deligne group) are both done.** `IdeleGroup`/`IdeleClassGroup` are
built in `Langlands/IdeleGroup.lean`, sorry-free, along with local norm maps
at finite and archimedean places, the idele-group norm map, the
Kedlaya–Sutherland unramified-extension correspondence, and rank-one
valuation compatibility. The Weil group is built in `Langlands/WeilGroup.lean`,
and the Weil–Deligne representation formalism — `LocalField.
WeilDeligneRepresentation K V`, bundling `ρ`, nilpotent `N`, and the
intertwining relation — is built in `Langlands/WeilDeligneRepresentation.lean`.
Both are sorry-free (see Phase 0 and Phase 1 status above).

**Status update: Phase 2a (unramified norm-group surjectivity, `N_{L/K}(L^×)
= ⟨π⟩^n·O_K^×` for unramified `L/K`) is also done, sorry-free, closed across
ten passes — see Phase 2a's status entries above.**

**Next move: Phase 2b's scoped candidates (ramified local reciprocity —
see the "Phase 2b" section above for the full landscape survey, the
duplication re-check against kbuzzard/ClassFieldTheory, and two candidate
first milestones with their tradeoffs laid out honestly rather than a single
recommendation).** Neither candidate has been attempted; Phase 2b was a
research/scoping pass only, no `.lean` files touched.

Concretely, beyond Phase 2b's two candidates: the full local reciprocity map
`K_v^× → Gal(K_v^ab/K_v)` (or its Weil-group refinement `K_v^× ≅ W_{K_v}^ab`)
still needs either Lubin–Tate formal-group theory or the cohomological
fundamental-class route — both confirmed absent from Mathlib this pass (see
Phase 2b) — built on top of the now-complete `WeilGroup`, drawing on this
project's norm-map and unramified-extension infrastructure
(`Langlands/NormMap.lean`, `Langlands/UnramifiedExtension.lean`,
`Langlands/AdicCompletionIntegralClosure.lean`) as a down payment on the
norm-functoriality and Frobenius-compatibility characterizing properties the
map needs (see Phase 2's scope correction above). Before writing new proofs,
check for prior formalization of local/global CFT elsewhere (e.g. around the
Mathlib `FLT` project, and re-check kbuzzard/ClassFieldTheory's progress
since it is actively developed) — duplicating an in-flight effort would be
the most wasteful outcome available here.

This is the correct next move because:
- It is **the only remaining prerequisite gate before Phase 3+ becomes
  meaningful** — every phase in this roadmap can already be *stated* with
  the Artin map axiomatized, but Phase 2 is required to make any of it
  *proved* rather than vacuous (see Phase 2's note above).
- It has **more prerequisites in place than any point so far** — Phase 1
  (Weil group), the Brauer group, and Hilbert's Theorem 90 are all
  available in Mathlib, and this project's own norm-map and
  unramified-extension infrastructure is a direct down payment on Phase 2's
  hardest characterizing properties.
- It is **independently upstreamable and high-value** — local class field
  theory is a named, citable theorem many other formalization efforts would
  want, the same way the Weil group, Weil–Deligne representation, and idele
  class group already are.
- It carries a **real risk of duplicated effort** that's cheap to check for
  up front but expensive to discover after building — hence checking for
  prior/in-flight CFT formalization is the first concrete step, not an
  afterthought.
