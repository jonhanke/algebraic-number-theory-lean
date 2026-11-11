# The modular curves $X_0(N)$: J. S. Milne, *Elliptic Curves*, Chapter V: map to the Lean library

J. S. Milne, *Elliptic Curves*, 2nd edition (2020), Chapter V, "Elliptic curves and modular forms": §§1–3 (the curves $X_0(N)$, modular functions, the modular polynomial, modular forms and the genus) and §7 (Hecke correspondences). Pages are those of the PDF. The other sections of Chapter V (46 rows: modular forms and Hecke operators, the Eichler–Shimura construction, Galois representations) and the other chapters of this book are not part of this release.

Each row is a result of the book, the Lean declaration that formalizes it, and its status. *Proved* means proved in Lean with only the standard axioms, assuming no unproved input (a hypothesis that is a condition of the statement, such as "$K$ is a local field", is not an input); *conditional* names the unproved inputs it still assumes; *in Mathlib* means Mathlib (v4.35.0, on which this library is built) already has the result, and the Lean name is Mathlib's; *not formalized* means the library does not state it. Rows that are not results (examples, history, comments, computations) are omitted and only counted. The statements in the middle column are short descriptions, not quotations; read the book for the exact wording. Items that the library states in a generalized form are mapped to the general statement.

Rows: 43. proved: 29; proved, conditional: 1; formalized (a definition): 3; in Mathlib: 1; in Tau Ceti, not in this library: 2; formalized, not in this release: 4; proved in part: 1; not formalized: 2. Not results (omitted): 3.

Named statements of the library for this book: results stated as Lean structures (a cited result is never assumed silently; it is a named structure, and a theorem assuming it lists it as a hypothesis), counted by a kernel-level audit of the hypotheses of every declaration. An *open predicate* is a condition used in statements, not a result to prove.

| part of the library | named statements | proved unconditionally | open inputs | refuted | open predicates |
|---|---|---|---|---|---|
| `NumberFieldKB.ModularCurves` | 3 | 3 | 0 | 0 | 0 |

## §1. The Riemann surfaces $\Gamma\backslash\mathbb H$ and $X_0(N)$

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Example 1.1 | 181 | The quotient $\mathbb{C}/\mathbb{Z}$ is a Riemann surface, isomorphic to $\mathbb{C}^\times$ via $q(z)=e^{2\pi iz}$ | `MilneEC.V.example_1_1` | proved |
| Definition (prose) | 182 | The complex structure (Riemann surface structure) on the quotient $\Gamma\backslash\mathbb H$ for finite-index $\Gamma\subset\mathrm{SL}_2(\mathbb Z)$, extended to $\Gamma\backslash\mathbb H^*$ with charts at elliptic points and cusps. | — | in Tau Ceti, not in this library |
| Example 1.2 | 182 | A finite group acting on the unit disk is cyclic, and the quotient disk by a cyclic group of order $m$ is again a disk via $z\mapsto z^m$ | `MilneEC.V.example_1_2`, `MilneEC.V.example_1_2_invariant` | proved |
| Remark 1.4 | 183 | For a finite index subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ the union of translates of the standard fundamental domain, suitably chosen, gives a fundamental domain for $\Gamma$ | `MilneEC.V.remark_1_4` | proved |
| Corollary 1.6 | 185 | For a finite-index subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb Z)$, the quotient space $\Gamma\backslash\mathbb H$ is Hausdorff. | `MilneEC.V.cor_1_6` | proved |
| Proposition 1.5 | 185 | For a finite index subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ acting on the upper half plane: finitely many $\gamma$ with $\gamma A\cap B\neq\emptyset$ for compact $A,B$; points have neighbourhoods moved off themselves; distinct orbits have separated neighbourhoods | `MilneEC.V.prop_1_5` | proved |
| Proposition 1.7 | 186 | The quotient $\Gamma\backslash\mathbb H^*$ of the extended upper half-plane (with cusps) is Hausdorff and compact. | `MilneEC.V.prop_1_7`, `MilneEC.V.compactSpace_xGamma`, `MilneEC.V.t2Space_xGamma`, `MilneEC.V.continuous_smul_hstar` | proved |
| Proposition 1.9 | 187 | The compact Riemann surface $X_0(1)$ has genus zero. | `MilneEC.V.prop_1_9_unconditional`, `MilneEC.V.prop_1_9`, `ModularCurves.prop_1_9_of_prop1_7` | proved |
| Proposition 1.8 | 187 | The coordinate neighbourhoods on $\Gamma_0(N)\backslash\mathbb{H}^*$ are compatible and give it the structure of a Riemann surface | — | in Tau Ceti, not in this library |
| Exercise 1.10 | 188 | (a) $\Gamma_0(p)$ has two orbits on $\mathbb P^1(\mathbb Q)$, so $X_0(p)$ has two cusps; (b) $\Delta(11z)$ is a weight-12 cusp form for $\Gamma_0(11)$; (c) $q\prod(1-q^n)^2(1-q^{11n})^2$ is a weight-2 cusp form for $\Gamma_0(11)$. | `MilneEC.V.exercise_1_10_a`, `MilneEC.V.exercise_1_10_b`, `MilneEC.V.exercise_1_10_c` | proved in part: (a) and (b) proved; (c) proved, conditional on `MilneEC.V.DimS2Small` ($S_2(\Gamma_0(N)) = 0$ for $N \le 10$ and $\dim S_2(\Gamma_0(11)) = 1$, a named statement) |
| Definition (prose) | 189 | The meromorphic functions on $\Gamma\backslash\mathbb H^*$ are the modular functions for $\Gamma$: meromorphic on $\mathbb H$, $\Gamma$-invariant, meromorphic at cusps. | `MilneEC.V.IsModularFunction` | formalized (a definition) |
| Proposition 1.3 | 183 | $D = \{\lvert z\rvert > 1, \lvert\Re z\rvert < 1/2\}$ is a fundamental domain for $\mathrm{SL}_2(\mathbb Z)$ with the boundary identifications; stabilizers of points of $\bar D$; $S$, $T$ generate $\mathrm{SL}_2(\mathbb Z)/\{\pm I\}$ | `MilneEC.V.prop_1_3_a`, `MilneEC.V.prop_1_3_a_boundary`, `MilneEC.V.prop_1_3_b`, `MilneEC.V.prop_1_3_c` | proved |
| Definition (prose) | 182 | A fundamental domain for a group acting on a Riemann surface: a connected open set with no two points in one orbit whose closure meets every orbit | `MilneEC.V.isFundamentalDomain_strip`, `MilneEC.V.isFundamentalDomain_sector` | proved |

## §2. Modular functions; $X_0(N)$ over $\mathbb Q$ and the modular polynomial

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Proposition 2.1 | 190 | There is a unique meromorphic function $J$ on $X_0(1)$ with a simple pole at $\infty$ and $J(i)=1$, $J(\rho)=0$, and all meromorphic functions on $X_0(1)$ are rational functions of $J$ | `MilneEC.V.prop_2_1` | proved |
| Proposition 2.2 | 191 | The function $j$ is the unique meromorphic function on $X_0(1)$ with a simple pole at the cusp and values $j(i)=1728$, $j(\rho)=0$; hence the meromorphic functions on $X_0(1)$ are $\mathbb C(j)$. | `MilneEC.V.prop_2_2_exists`, `MilneEC.V.prop_2_2_unique`, `MilneEC.V.jFun_surjective`, `MilneEC.V.prop2_2Rational` | proved |
| Theorem 2.3 | 192 | The field of meromorphic functions on $X_0(N)$ is $\mathbb C(j, j_N)$ with $j_N(z)=j(Nz)$. | `ModularCurves.thm2_3`, `MilneEC.V.Thm2_3`, `ModularCurves.exists_num`, `ModularCurves.isMeromorphicAtImInfty_of_isModerate` | proved |
| Proposition 2.4 | 193 | The modular polynomial $F_N(X,Y)$, the minimal polynomial of $j(Nz)$ over $\mathbb{C}(j)$, has rational coefficients | `ModularCurves.prop2_4`, `ModularCurves.modularPolynomial`, `ModularCurves.modPolyCx_dvd`, `ModularCurves.mem_gamma0_of_jN_smul` | proved |
| Remark 2.6 | 194 | The curve $F_N(X,Y)=0$ is highly singular, since otherwise the genus formula would give too large a genus | `ModularCurves.remark_2_6`, `ModularCurves.twelve_mul_genus_le`, `ModularCurves.transcendental_jX0`, `ModularCurves.adjoin_jX0_jNX0` | proved |
| Theorem 2.7 | 196 | For every field $k$ of characteristic zero there is a functorial map from isomorphism classes of elliptic curves with a cyclic subgroup of order $N$ stable under Galois to $Y_0(N)(k)$, compatible with $(j(E), j(E/S))$, surjective, and bijective for algebraically closed $k$. | — | not formalized |
| Definition (prose) | 196 | $\mathcal E_0(N)(k)$ is the set of isomorphism classes of pairs $(E,S)$ with $E$ over $k$ and $S\subset E(k^{al})$ cyclic of order $N$, stable under Galois. | `MilneEC.Vb.CyclicPair.iso_equivalence`, `MilneEC.Vb.transportPts_galois` | proved |

## §3. Modular forms and the genus of $X_0(N)$

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Definition 3.1 | 198 | A modular form of weight $2k$ for a finite-index subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb Z)$ is a holomorphic function on the upper half-plane with $f(\gamma z)=(cz+d)^{2k}f(z)$, holomorphic at the cusps; a cusp form vanishes at the cusps. | `MilneEC.V.def_3_1`, `MilneEC.V.def_3_1_cusp` | proved |
| Proposition 3.3 | 199 | Pulling back holomorphic differentials on $\Gamma_0(N)\backslash\mathbb{H}^*$ to $\mathbb{H}$ gives an isomorphism with the space $S_2(\Gamma_0(N))$ of weight 2 cusp forms | `MilneEC.V.prop_3_3_cusps`, `MilneEC.V.prop_3_3_elliptic`, `MilneEC.V.weight_two_iff_differential_invariant`, `MilneEC.V.differentialHolomorphicAtInfty_iff` | proved |
| Corollary 3.4 | 199 | The dimension of $S_2(\Gamma_0(N))$ equals the genus of $X_0(N)$ | `ModularCurves.cor_3_4`, `ModularCurves.dim_canonicalW_eq_genus`, `ModularCurves.genus_X0C_eq`, `ModularCurves.IsRep.mem_canonicalW` | proved |
| Proposition 3.5 | 200 | For $k>1$ the Eisenstein series $G_{2k}(z)$ is a modular form of weight $2k$ for $\mathrm{SL}_2(\mathbb Z)$, and $\Delta$ is a cusp form of weight 12. | `MilneEC.V.prop_3_5_eisenstein`, `MilneEC.V.prop_3_5_discr`, `MilneEC.V.eisG_eq`, `MilneEC.V.discr_eq` | proved |
| Theorem 3.6 | 200 | The graded algebra of level-one modular forms is the polynomial algebra $\mathbb C[G_4,G_6]$ (algebraically independent), and $f\mapsto f\Delta$ is a bijection $M_{2k-12}\to S_{2k}$. | `MilneEC.V.thm_3_6_span`, `MilneEC.V.thm_3_6_algebraicIndependent`, `MilneEC.V.thm_3_6_graded`, `MilneEC.V.thm_3_6_discr` | proved |
| Theorem 3.7 (Jacobi) | 201 | $\Delta=(2\pi)^{12}q\prod_{n\ge1}(1-q^n)^{24}$. | `MilneEC.V.thm_3_7` | proved |
| Definition (prose) | 202 | The $L$-series $L(E,s)=\prod_{p\ \mathrm{good}}(1-a_pp^{-s}+p^{1-2s})^{-1}\prod_{p\ \mathrm{bad}}(1-a_pp^{-s})^{-1}$ of an elliptic curve over $\mathbb Q$. | `WeierstrassCurve.LFunction`, `WeierstrassCurve.LSeries` | in Mathlib |

## §7. Hecke correspondences on $X_0(N)$

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Remark 7.1 | 225 | A regular map between open subsets of nonsingular projective curves extends uniquely to the compactifications, hence correspondences extend. | `MilneEC.remark_7_1_corrected`, `MilneEC.remark_7_1` | proved, conditional on `MilneEC.Prop4_18Corrected` |
| Remark 7.2 | 225 | A correspondence $T$ pulls back regular functions via $f\mapsto (P\mapsto\sum f(\beta Q_i))$ and holomorphic differentials. | `MilneEC.remark_7_2_regular`, `MilneEC.pullbackFun_algebraMap` | proved |
| Definition (prose) | 225 | For $p\nmid N$ the Hecke correspondence $T(p)$ on $Y_0(N)$ is $Y_0(N)\leftarrow Y_0(pN)\to Y_0(N)$ using the projection and $z\mapsto pz$. | `ModularCurves.finrank_forget`, `ModularCurves.deg_heckeDiv`, `ModularCurves.deg_heckeX0`, `ModularCurves.sum_ramIndex_mul_residueDeg_forget` | proved |
| Definition (prose) | 225 | For a curve $C$ over $\overline{\mathbb F}_p$, the curve $C^{(p)}$ has equations with coefficients raised to the $p$-th power, and the Frobenius map $\varphi_p:C\to C^{(p)}$ raises coordinates to the $p$-th power. | `MilneEC.Vb.frobeniusTwist_baseChange` | proved |
| Proposition 7.3 | 226 | The Frobenius map $\varphi_p:C\to C^{(p)}$ is purely inseparable of degree $p$, and any purely inseparable degree-$p$ map factors through it. | — | formalized, not in this release |
| Theorem 7.4 (Eichler-Shimura relation) | 226 | At a prime of good reduction $\tilde T(p)=\varphi_p+\varphi_p^{\mathrm{tr}}$ in the ring of correspondences of $\tilde X_0(N)$. | — | not formalized |
| Definition (prose) | 226 | The degree of a nonconstant morphism of curves $\alpha:C\to C'$ is $[k(C):\alpha^*k(C')]$. | `MilneEC.Vb.curveMapDegree` | formalized (a definition) |
| Definition (prose) | 226 | A morphism of curves is separable or purely inseparable according as the function field extension $k(C)/\alpha^*k(C')$ is. | `MilneEC.Vb.IsSeparableCurveMap`, `MilneEC.Vb.IsPurelyInseparableCurveMap` | formalized (a definition) |
| Proposition 7.5 | 228 | For an elliptic curve $E$ over $\mathbb F_p$ the trace of Frobenius on $T_\ell E$ is $p+1-N_p$. | — | formalized, not in this release |
| Corollary 7.6 | 228 | The Frobenius and its transpose have the same trace on $T_\ell E$. | — | formalized, not in this release |
| Proposition 7.7 | 228 | For a real vector space $V$ with complex structure $J$, $V\to V\otimes\mathbb C\to V^+$ is a complex-linear isomorphism and conjugation swaps $V^+$ and $V^-$. | `MilneEC.Vb.prop_7_7_a`, `MilneEC.Vb.prop_7_7_b`, `MilneEC.Vb.cx_isCompl` | proved |
| Corollary 7.8 | 229 | A complex-linear endomorphism has real matrix equivalent to $A_1\oplus\overline{A_1}$. | `MilneEC.Vb.cor_7_8`, `MilneEC.Vb.cor_7_8_trace`, `MilneEC.Vb.cor_7_8_charpoly` | proved |
| Corollary 7.9 | 229 | For $p\nmid N$, $\mathrm{Tr}(T(p)\mid H_1(X_0(N),\mathbb Z))=\mathrm{Tr}(T(p)\mid\Omega^1)+\overline{\mathrm{Tr}(T(p)\mid\Omega^1)}$. | `MilneEC.Vb.cor_7_9_lattice` | proved |
| Theorem 7.10 | 229 | For a normalized integral newform $f$ and a prime $p\nmid N$, the coefficient $c(p)$ equals $a_p=p+1-N_p(E)$ (Eichler-Shimura) | — | formalized, not in this release |
| Definition (prose) | 230 | A prime $p$ is unramified in a number field $K$ if no prime of $\mathcal O_K$ over $p$ has ramification index above 1. | `MilneEC.Vb.unramified_iff_ramificationIdx` | proved |
| Definition (prose) | 230 | The Frobenius element at a prime $\mathfrak p$ over $p$ in a Galois extension is the $\sigma\in G(\mathfrak p)$ with $\sigma x\equiv x^p \bmod\mathfrak p$; well defined up to conjugacy. | `MilneEC.Vb.frobenius_mem_decomposition`, `MilneEC.Vb.frobenius_conj` | proved |
