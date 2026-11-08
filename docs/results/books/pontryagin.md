# Pontryagin duality for locally compact abelian groups: map to the Lean library

G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd edition, CRC Press, 2016, Chapter 4 (§§4.2–4.4), and A. Weil, *Basic Number Theory*, II.§5 and VII.§2, where Weil states the duality theory he uses. There is no item-by-item audit of Folland's Chapter 4 yet: the rows are the results the library's docstrings cite.

Each row is a result of the book, the Lean declaration that formalizes it, and its status. *Proved* means proved in Lean with only the standard axioms, assuming no unproved input (a hypothesis that is a condition of the statement, such as "$K$ is a local field", is not an input); *conditional* names the unproved inputs it still assumes; *in Mathlib* means Mathlib (v4.35.0, on which this library is built) already has the result, and the Lean name is Mathlib's; *not formalized* means the library does not state it. Rows that are not results (examples, history, comments, computations) are omitted and only counted. The statements in the middle column are short descriptions, not quotations; read the book for the exact wording. Items that the library states in a generalized form are mapped to the general statement.

Rows: 24. proved: 22; formalized (a definition): 2.

Named statements of the library for this book: results stated as Lean structures (a cited result is never assumed silently; it is a named structure, and a theorem assuming it lists it as a hypothesis), counted by a kernel-level audit of the hypotheses of every declaration. An *open predicate* is a condition used in statements, not a result to prove.

| part of the library | named statements | proved unconditionally | open inputs | refuted | open predicates |
|---|---|---|---|---|---|
| `NumberFieldKB.Pontryagin` | 5 | 4 | 0 | 0 | 1 |

Open predicates: `Pontryagin.IsAdmissibleFor`.

## Folland, Chapter 4

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Theorem 4.18 | — | Bochner's theorem: a continuous positive-definite function is the Fourier–Stieltjes transform of a unique positive finite Radon measure on the dual group | `Pontryagin.bochnerTheorem` | proved |
| Corollary 4.20 | — | Gelfand–Raikov for commutative groups: the characters of a locally compact abelian group separate points | `Pontryagin.Unconditional.charactersSeparate` | proved |
| Theorem 4.32 | — | Pontryagin duality: the canonical map $G \to G^{**}$ is an isomorphism of topological groups | `Pontryagin.Unconditional.pontryaginDuality` | proved |
| Theorem 4.32, proof | — | the canonical map $G \to G^{**}$ is injective, a closed embedding, and surjective | `Pontryagin.Unconditional.dualEval_injective`, `Pontryagin.Unconditional.isClosedEmbedding_dualEval`, `Pontryagin.Unconditional.dualEval_surjective` | proved |
| Theorem 4.33 | — | Fourier inversion: for $f$ in the inversion class, $\hat f$ is integrable for the dual Haar measure and $f(x) = \int \hat f(\xi)\xi(x)\,d\xi$ | `Pontryagin.inversion_isInvClass` | proved |
| Theorem 4.33, proof | — | consistency of the Bochner measures, $\hat g\,\mu_f = \hat f\,\mu_g$ | `Pontryagin.withDensity_bochnerMeasure_comm` | proved |
| Theorem 4.33, proof | — | the dual Haar measure, built by the Riesz–Markov–Kakutani theorem from the Bochner measures, is a Haar measure | `Pontryagin.isHaarMeasure_dualHaar` | proved |

## Weil, Chapter II, §5 (duality of locally compact abelian groups)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| II.§5, p. 38 | — | $G$ is compact if and only if $G^*$ is discrete | `Pontryagin.Unconditional.compactSpace_iff_discreteTopology_dual` | proved |
| II.§5, p. 38 | — | $G$ is discrete if and only if $G^*$ is compact | `Pontryagin.Unconditional.discreteTopology_iff_compactSpace_dual` | proved |
| II.§5, p. 38 | — | duality for discrete groups | `Pontryagin.pontryaginDuality_discrete` | proved |
| II.§5, p. 38 | — | duality for compact groups (from the Peter–Weyl theorem) | `Pontryagin.peterWeylTheorem`, `Pontryagin.pontryaginDuality_compact` | proved |
| II.§5, p. 38 | — | for a closed subgroup $H$, the subgroup of $G$ orthogonal to $H^*$ is $H$ | `Pontryagin.Unconditional.doubleAnnihilator_eq` | proved |
| II.§5, p. 38 | — | a closed subgroup $H$ is isomorphic, as a topological group, to the dual of $G^*/H^*$ | `Pontryagin.Unconditional.subgroupEquivDualQuotient` | formalized (a definition) |
| II.§5, p. 38 | — | $H^* \cong (G/H)^*$ as topological groups | `Pontryagin.annihilatorEquiv` | formalized (a definition) |
| II.§5, p. 39 | — | $H$ is open if and only if $H^*$ is compact; $H$ is compact if and only if $H^*$ is open | `Pontryagin.Unconditional.isOpen_iff_isCompact_annihilator`, `Pontryagin.Unconditional.isCompact_iff_isOpen_annihilator` | proved |
| II.§5, p. 39 | — | $G/H$ is compact if and only if $H^*$ is discrete | `Pontryagin.Unconditional.compactSpace_quotient_iff` | proved |

## Weil, Chapter VII, §2 (Fourier transforms and dual measures)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| VII.§2, p. 105 | — | the dual measure of a Haar measure exists and is a regular Haar measure on $G^*$ | `Pontryagin.Unconditional.exists_isDualMeasure` | proved |
| VII.§2, p. 105 | — | the dual measure is unique | `Pontryagin.Unconditional.isDualMeasure_unique` | proved |
| VII.§2, p. 105 | — | scaling: the dual measure of $c\alpha$ is $c^{-1}\beta$ | `Pontryagin.isDualMeasure_smul` | proved |
| VII.§2, p. 105 | — | under an identification $G \cong G^*$ there is a unique self-dual Haar measure | `Pontryagin.Unconditional.exists_isDualMeasure_map_self`, `Pontryagin.Unconditional.isDualMeasure_map_self_unique` | proved |
| VII.§2, p. 105 | — | for compact $G$ of volume 1 the dual measure is the counting measure | `Pontryagin.Unconditional.isDualMeasure_count_of_compact` | proved |
| VII.§2, p. 105 | — | for discrete $G$ with the counting measure the dual measure has total mass 1 | `Pontryagin.isDualMeasure_of_discrete` | proved |
| VII.§2, p. 105 | — | Fourier inversion for every admissible function | `Pontryagin.inversion_admissible` | proved |
| VII.§2, p. 106 | — | the Poisson summation formula for a discrete subgroup $\Gamma$ with compact quotient and an admissible function | `Pontryagin.poisson_summation` | proved |
