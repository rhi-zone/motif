# Formalization Priorities

## Tier 1: Infrastructure (unblocks everything downstream)

### 1. ∞-Categories
Single biggest blocker for modern math formalization. Modern Langlands, derived algebraic geometry, algebraic topology all need this. Not in any proof assistant.

### 2. Real Analysis Gaps
Path integrals via Rouché's theorem, measure theory completeness. Blocks PDEs, probability, physics, Fourier analysis.

### 3. Algebraic Geometry
Schemes exist in 3 formulations but coherent sheaves, derived categories, moduli theory incomplete. Blocks number theory, Langlands, intersection theory.

## Tier 2: High-Value Domains

### 4. Classification of Finite Simple Groups
10,000+ pages across ~500 papers. Known error-prone. Highest proof-reliability payoff. Odd-order theorem done in Coq (Gonthier).

### 5. Number Theory / Langlands Infrastructure  
Adeles, L-functions, Weil groups, class field theory. Central to modern number theory. Our current work lives here.

### 6. HoTT Coherence
Higher-dimensional coherence in HoTT. Affects foundations of constructive mathematics.

## Tier 3: Verification Targets

### 7. Disputed Proofs (IUT)
Mochizuki's Inter-Universal Teichmüller Theory. Scholze-Stix controversy unresolved. Formalization would be definitive.

## Tier 4: Applications

### 8. Probability / Statistics
Central Limit Theorem, martingale convergence, statistical learning theory. ML and science applications.

### 9. Physics Formalization
PhysLean, index notation, Wick's theorem. Very early stage.

## Status

For each field, we need to check: is anyone (lean-pool, TauCeti, leanprover-community/intentions, Mathlib PRs) already working on it? See companion analysis: [ECOSYSTEM_SURVEY.md](./ECOSYSTEM_SURVEY.md).

---

Sources: Kevin Buzzard ICM 2022, Quanta Magazine coverage, Mathlib Initiative roadmap, arXiv surveys on formalization gaps.
