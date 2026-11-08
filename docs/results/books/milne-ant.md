# J. S. Milne, *Algebraic Number Theory*: map to the Lean library

Version 3.08 (2020), available at jmilne.org. Items as numbered in the notes; *Definition (prose)* is a definition given in the running text. Pages are those of the PDF.

Each row is a result of the book, the Lean declaration that formalizes it, and its status. *Proved* means proved in Lean with only the standard axioms, assuming no unproved input (a hypothesis that is a condition of the statement, such as "$K$ is a local field", is not an input); *conditional* names the unproved inputs it still assumes; *in Mathlib* means Mathlib (v4.35.0, on which this library is built) already has the result, and the Lean name is Mathlib's; *not formalized* means the library does not state it. Rows that are not results (examples, history, comments, computations) are omitted and only counted. The statements in the middle column are short descriptions, not quotations; read the book for the exact wording. Items that the library states in a generalized form are mapped to the general statement.

Rows: 328. proved: 132; formalized (a definition): 17; in Mathlib: 179. Not results (omitted): 30.

Named statements of the library for this book: results stated as Lean structures (a cited result is never assumed silently; it is a named structure, and a theorem assuming it lists it as a hypothesis), counted by a kernel-level audit of the hypotheses of every declaration. An *open predicate* is a condition used in statements, not a result to prove.

| part of the library | named statements | proved unconditionally | open inputs | refuted | open predicates |
|---|---|---|---|---|---|
| `NumberFieldKB.MilneANT` | 38 | 36 | 0 | 0 | 2 |

Open predicates: `MilneANT.Aside89.AWAxioms`, `MilneANT.IsLocalFieldMilne`.

## Chapter 1. Preliminaries from Commutative Algebra

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Proposition 1.1 | 17 | Every ideal of a product ring $A\times B$ is $\mathfrak a\times\mathfrak b$; the prime ideals are $\mathfrak p\times B$ and $A\times\mathfrak p$ for primes $\mathfrak p$. | `Ideal.ideal_prod_eq`, `Ideal.ideal_prod_prime` | in Mathlib |
| Remark 1.2 | 17 | The same description holds for finite products $A_1\times\dots\times A_m$ (ideals are products; prime iff one factor prime and the rest the whole ring). | `MilneANT.remark_1_2_ideal_eq_pi`, `MilneANT.remark_1_2_isPrime_pi_iff` | proved |
| Proposition 1.3 | 17 | A ring is noetherian iff every ascending chain of ideals stabilizes iff every nonempty set of ideals has a maximal element. | `isNoetherianRing_iff_ideal_fg`, `monotone_stabilizes_iff_noetherian`, `set_has_maximal_iff_noetherian` | in Mathlib |
| Proposition 1.4 | 18 | Every nonzero nonunit of a noetherian domain is a product of irreducible elements. | `IsNoetherianRing.wfDvdMonoid`, `WfDvdMonoid.exists_factors` | in Mathlib |
| Remark 1.5 | 18 | The ring of all algebraic integers is not noetherian, since $\sqrt\alpha$ can always be extracted. | `MilneANT.remark_1_5` | proved |
| Proposition 1.6 | 19 | A module is noetherian iff ascending chains of submodules stabilize iff every nonempty set of submodules has a maximal element. | `isNoetherian_iff`, `monotone_stabilizes_iff_noetherian`, `set_has_maximal_iff_noetherian` | in Mathlib |
| Proposition 1.7 | 19 | If $N$ and $M/N$ are noetherian then $M$ is noetherian. | `isNoetherian_iff_submodule_quotient`, `isNoetherian_of_range_eq_ker` | in Mathlib |
| Proposition 1.8 | 19 | Over a noetherian ring every finitely generated module is noetherian. | `isNoetherian_of_isNoetherianRing_of_finite` | in Mathlib |
| Lemma 1.9 | 19 | Nakayama's lemma: for a local ring and proper ideal $\mathfrak a$, $M$ finitely generated with $\mathfrak aM=M$ gives $M=0$; and $N+\mathfrak aM=M$ gives $N=M$. | `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`, `Submodule.le_of_le_smul_of_le_jacobson_bot`, `Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson` | in Mathlib |
| Proposition 1.11 | 20 | For $S^{-1}A$, extension then contraction returns the ideal for every ideal of $S^{-1}A$, and contraction then extension returns a prime ideal of $A$ disjoint from $S$. | `IsLocalization.map_under`, `IsLocalization.under_map_of_isPrime_disjoint` | in Mathlib |
| Proposition 1.12 | 21 | Extension $\mathfrak p\mapsto\mathfrak pS^{-1}A$ is a bijection from primes of $A$ disjoint from $S$ to primes of $S^{-1}A$, inverse contraction. | `IsLocalization.orderIsoOfPrime` | in Mathlib |
| Example 1.13 | 21 | $A_{\mathfrak p}$ is local with maximal ideal $\mathfrak pA_{\mathfrak p}$; lists of primes of $\mathbb Z$, $\mathbb Z[1/2]$, $\mathbb Z_{(2)}$, $\mathbb Z[1/42]$, $\mathbb Z/(42)$. | `IsLocalization.AtPrime.isLocalRing`, `IsLocalization.AtPrime.map_eq_maximalIdeal` | in Mathlib |
| Theorem 1.14 | 22 | Chinese remainder theorem: for pairwise coprime ideals, $A\to\prod A/\mathfrak a_i$ is surjective with kernel $\bigcap\mathfrak a_i=\prod\mathfrak a_i$. | `Ideal.quotientInfRingEquivPiQuotient`, `Ideal.exists_forall_sub_mem_ideal`, `Ideal.prod_eq_iInf_of_pairwise_isCoprime` | in Mathlib |
| Theorem 1.15 | 22 | Chinese remainder theorem for modules: $0\to\mathfrak aM\to M\to\prod M/\mathfrak a_iM\to 0$ is exact. | `Ideal.pi_tensorProductMk_quotient_surjective`, `Ideal.ker_tensorProductMk_quotient` | in Mathlib |
| Lemma 1.17 | 24 | The tensor product of two surjective linear maps is surjective. | `TensorProduct.map_surjective` | in Mathlib |
| Theorem 1.18 | 26 | For $K/k$ finite separable and $\Omega/k$ any extension, $K\otimes_k\Omega$ is a product of finite separable extensions of $\Omega$, and the minimal polynomial of a primitive element factors accordingly. | `MilneANT.thm_1_18` | proved |
| Example 1.19 | 26 | For $K=\mathbb Q[\alpha]$, $\mathbb C\otimes_{\mathbb Q}K\cong\mathbb C^r$ with the $i$th projection given by $\alpha\mapsto\alpha_i$. | `MilneANT.example_1_19` | proved |

## Chapter 2. Rings of Integers

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Theorem 2.1 | 27 | The elements of $L$ integral over a domain $A\subseteq L$ form a ring. | `integralClosure`, `IsIntegral.add`, `IsIntegral.mul` | in Mathlib |
| Theorem 2.2 | 27 | Symmetric function theorem: every symmetric polynomial over a ring is a polynomial in the elementary symmetric polynomials. | `MvPolynomial.esymmAlgHom_surjective`, `MvPolynomial.esymmAlgEquiv` | in Mathlib |
| Proposition 2.3 | 28 | If $\alpha_1,\dots,\alpha_n$ are the roots of a monic polynomial over $A$, every polynomial in the $\alpha_i$ with coefficients in $A$ is integral over $A$. | `roots_mem_integralClosure`, `IsIntegral.add`, `IsIntegral.mul` | in Mathlib |
| Proposition 2.4 | 28 | If a nonzero finitely generated $A$-submodule $M$ of a field $L$ satisfies $\alpha M\subseteq M$, then $\alpha$ is integral over $A$ (and conversely). | `isIntegral_of_smul_mem_submodule`, `IsIntegral.of_mem_of_fg` | in Mathlib |
| Definition 2.5 | 30 | The integral closure of $A$ in $L$; the ring of integers $\mathcal O_L$ of a number field. | `integralClosure`, `NumberField.RingOfIntegers` | in Mathlib |
| Proposition 2.6 | 30 | If $\alpha$ is algebraic over $K=\operatorname{Frac}A$, then $d\alpha$ is integral over $A$ for some nonzero $d\in A$. | `IsAlgebraic.exists_integral_multiple` | in Mathlib |
| Corollary 2.7 | 30 | If $L/K$ is algebraic, $L$ is the field of fractions of the integral closure of $A$ in $L$. | `integralClosure.isFractionRing_of_algebraic` | in Mathlib |
| Definition 2.8 | 30 | A ring is integrally closed if it equals its integral closure in its field of fractions. | `IsIntegrallyClosed` | in Mathlib |
| Proposition 2.9 | 30 | A unique factorization domain (in particular a principal ideal domain) is integrally closed. | `UniqueFactorizationMonoid.instIsIntegrallyClosed` | in Mathlib |
| Example 2.10 | 31 | (a) $\mathbb Z$ and $\mathbb Z[i]$ are integrally closed; (b) unique factorization fails in $\mathbb Z[\sqrt{-3}]$; (c) the integral closure of $k[S_1,\dots,S_m]$ in $k(X_1,\dots,X_m)$ is $k[X_1,\dots,X_m]$. | `MilneANT.example_2_10_a_int`, `MilneANT.example_2_10_a_gaussianInt`, `MilneANT.example_2_10_b`, `MilneANT.example_2_10_c` | proved |
| Proposition 2.11 | 31 | For $A$ integrally closed with fraction field $K$ and $L/K$ finite, $\alpha\in L$ is integral over $A$ iff its minimal polynomial over $K$ has coefficients in $A$. | `minpoly.isIntegrallyClosed_eq_field_fractions'`, `minpoly.isIntegrallyClosed_eq_field_fractions` | in Mathlib |
| Remark 2.12 | 31 | For $d$ squarefree-type, $\alpha\in\mathbb Q[\sqrt d]$ is integral iff its trace and norm lie in $\mathbb Z$. | `Algebra.isIntegral_trace`, `Algebra.isIntegral_norm`, `QuadFormsKB.Binary.isIntegral_iff` | in Mathlib |
| Proposition 2.13 | 31 | If $B$ is integral over $A$ and finitely generated as an $A$-algebra, it is finitely generated as an $A$-module. | `Algebra.IsIntegral.finite` | in Mathlib |
| Lemma 2.14 | 32 | If $B$ is a finitely generated $A$-module and $C$ a finitely generated $B$-module, then $C$ is a finitely generated $A$-module. | `Module.Finite.trans` | in Mathlib |
| Proposition 2.15 | 32 | Transitivity of integrality for domains $A\subseteq B\subseteq C$. | `isIntegral_trans`, `Algebra.IsIntegral.trans` | in Mathlib |
| Corollary 2.16 | 32 | The integral closure of $A$ in an algebraic extension $L$ of its fraction field is integrally closed. | `integralClosure_idem`, `integralClosure.isIntegrallyClosedOfFiniteExtension` | in Mathlib |
| Remark 2.17 | 32 | In particular, the ring of integers of a number field is integrally closed. | — | in Mathlib |
| Proposition 2.19 | 33 | For $L/K$ of degree $n$ and $\beta\in L$ with minimal polynomial roots $\beta_1,\dots,\beta_m$, $\operatorname{Tr}\beta=r\sum\beta_i$ and $\operatorname{Nm}\beta=(\prod\beta_i)^r$ with $r=[L:K[\beta]]$. | `trace_eq_sum_roots`, `Algebra.norm_eq_prod_roots` | in Mathlib |
| Corollary 2.20 | 34 | For $L/K$ separable, trace and norm are the sum and product of the images under all $K$-embeddings into a big Galois extension. | `trace_eq_sum_embeddings`, `Algebra.norm_eq_prod_embeddings` | in Mathlib |
| Corollary 2.21 | 34 | If $A$ is integrally closed and $\beta\in L$ is integral over $A$, then $\operatorname{Tr}\beta,\operatorname{Nm}\beta\in A$. | `Algebra.isIntegral_trace`, `Algebra.isIntegral_norm` | in Mathlib |
| Lemma 2.23 | 35 | If $\gamma_j=\sum a_{ji}\beta_i$ then $D(\gamma)=\det(a_{ij})^2D(\beta)$. | `Algebra.discr_of_matrix_vecMul` | in Mathlib |
| Proposition 2.24 | 35 | For $B$ free of rank $m$ over a domain $A$ with $\operatorname{disc}(B/A)\ne0$, elements $\gamma_i$ form a basis iff $(D(\gamma))=(\operatorname{disc}B/A)$ as ideals. | `MilneANT.prop_2_24` | proved |
| Remark 2.25 | 36 | $\gamma_1,\dots,\gamma_m$ generate a finite-index submodule $N\subseteq B$ iff $D(\gamma)\ne0$, and then $D(\gamma)=(B:N)^2\operatorname{disc}(B/\mathbb Z)$. | `MilneANT.remark_2_25` | proved |
| Proposition 2.26 | 36 | For $L/K$ finite separable, $D(\beta_1,\dots,\beta_m)=\det(\sigma_i\beta_j)^2\ne0$ for every basis. | `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two`, `Algebra.discr_not_zero_of_basis` | in Mathlib |
| Corollary 2.27 | 36 | If the integral closure $B$ of $A$ in a finite separable $L/K$ is free of rank $m$ over $A$, then $\operatorname{disc}(B/A)\ne0$. | `Algebra.discr_not_zero_of_basis`, `NumberField.discr_ne_zero` | in Mathlib |
| Remark 2.28 | 36 | (a) The trace pairing on $L/K$ separable is nondegenerate; (b) if $L/K$ is inseparable then $\operatorname{disc}(L/K)=0$. | `traceForm_nondegenerate`, `traceForm_nondegenerate_tfae`, `Algebra.trace_eq_zero_of_not_isSeparable` | in Mathlib |
| Proposition 2.29 | 37 | For $A$ integrally closed and $B$ the integral closure in a separable $L/K$ of degree $m$, free submodules $M\subseteq B\subseteq M'$ exist; so $B$ is finite over noetherian $A$ and free of rank $m$ over a principal ideal domain. | `IsIntegralClosure.range_le_span_dualBasis`, `IsIntegralClosure.isNoetherian`, `IsIntegralClosure.finite`, `IsIntegralClosure.module_free`, `IsIntegralClosure.rank` | in Mathlib |
| Corollary 2.30 | 37 | $\mathcal O_L$ is the largest subring of a number field $L$ that is finitely generated as a $\mathbb Z$-module. | `IsIntegralClosure.finite`, `IsIntegral.of_finite` | in Mathlib |
| Definition 2.32 | 38 | An integral basis of a number field is a $\mathbb Z$-basis of $\mathcal O_K$. | `NumberField.RingOfIntegers.basis`, `NumberField.integralBasis` | in Mathlib |
| Remark 2.33 | 38 | (a) The trace dual $C^*$ of $C=\sum A\beta_i$ is $\sum A\beta_i'$ and $C\subseteq B\subseteq C^*$; (b) for $C=A[\beta]$ the dual is $f'(\beta)^{-1}A[\beta]$ with basis $\beta^i/f'(\beta)$ (Euler). | `MilneANT.remark_2_33_b` | proved |
| Proposition 2.34 | 39 | For $L=K[\beta]$ with minimal polynomial $f$, $D(1,\beta,\dots,\beta^{m-1})=\prod_{i<j}(\beta_i-\beta_j)^2=(-1)^{m(m-1)/2}\operatorname{Nm}f'(\beta)$. | `Algebra.discr_powerBasis_eq_norm`, `Algebra.discr_powerBasis_eq_prod` | in Mathlib |
| Example 2.35 | 39 | The discriminant of $X^n+aX+b$ is $(-1)^{n(n-1)/2}(n^nb^{n-1}+(-1)^{n-1}(n-1)^{n-1}a^n)$, with the cases $n=2,3,4,5$. | `MilneANT.example_2_35`, `MilneANT.example_2_35_deg_two`, `MilneANT.example_2_35_deg_three`, `MilneANT.example_2_35_deg_four` | proved |
| Example 2.36 | 40 | $X^3-X-1$ has discriminant $-23$ (squarefree) so $\mathbb Z[\alpha]$ is the ring of integers. | `MilneANT.example_2_36` | proved |
| Example 2.37 | 40 | $X^3+X+1$ has discriminant $-31$, so $\mathbb Z[\alpha]$ is the ring of integers. | `MilneANT.example_2_37` | proved |
| Example 2.38 | 41 | Dedekind's example $X^3+X^2-2X+8$: discriminant $-2012$ but $\operatorname{disc}\mathcal O_K=-503$, no power integral basis. | `MilneANT.example_2_38`, `MilneANT.example_2_38_not_monogenic` | proved |
| Example 2.39 | 41 | $X^5-X-1$ is irreducible with squarefree discriminant $2869$, so $\mathbb Z[\alpha]$ is the ring of integers. | `MilneANT.example_2_39` | proved |
| Proposition 2.40 | 41 | (a) The sign of $\operatorname{disc}K$ is $(-1)^s$ where $2s$ is the number of non-real embeddings; (b) Stickelberger: $\operatorname{disc}\mathcal O_K\equiv0,1\pmod 4$. | `MilneANT.prop_2_40_a`, `MilneANT.prop_2_40_b` | proved |
| Example 2.41 | 41 | For $K=\mathbb Q[\sqrt m]$, $m$ squarefree: $\{1,\sqrt m\}$ is an integral basis if $m\equiv2,3\pmod 4$ and $\{1,(1+\sqrt m)/2\}$ if $m\equiv1\pmod 4$. | `MilneANT.example_2_41` | proved |
| Remark 2.42 | 42 | Isomorphic number fields have the same degree and discriminant (converse false, e.g. four cubic fields of discriminant $4027$); no integral polynomial of degree $>1$ has discriminant $\pm1$ except as noted. | `NumberField.discr_eq_discr_of_algEquiv`, `NumberField.discr_eq_discr_of_ringEquiv` | in Mathlib |
| Proposition 2.43 | 42 | For a basis $\beta_1,\dots,\beta_m$ of $L/K$ consisting of integral elements over a principal ideal domain $A$ and $d=D(\beta)$, $\sum A\beta_i\subseteq B\subseteq\sum A(\beta_i/d)$. | `MilneANT.prop_2_43` | proved |
| Lemma 2.44 | 43 | Over a Euclidean domain, every square matrix can be brought to upper triangular form by row additions and swaps. | `MilneANT.lemma_2_44` | proved |
| Remark 2.45 | 44 | Invertible-matrix reformulation, Hermite normal form (uniqueness) over $\mathbb Z$, and its use to build an integral basis. | `MilneANT.remark_2_45_a_upper`, `MilneANT.remark_2_45_a_lower`, `MilneANT.remark_2_45_b_exists`, `MilneANT.remark_2_45_b_unique` | proved |

## Chapter 3. Dedekind Domains; Factorization

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Example 3.1 | 48 | The localization $\mathbb Z_{(p)}$ is a discrete valuation ring with unique nonzero prime $(p)$, units $m/n$ with $p\nmid mn$. | `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`, `IsPrincipalIdealRing.isDedekindDomain` | in Mathlib |
| Proposition 3.2 | 49 | A domain is a discrete valuation ring iff it is noetherian, integrally closed, and has exactly one nonzero prime ideal. | `IsDiscreteValuationRing.TFAE`, `IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime` | in Mathlib |
| Definition 3.3 | 50 | A Dedekind domain is a noetherian, integrally closed domain in which every nonzero prime is maximal. | `IsDedekindDomain` | in Mathlib |
| Proposition 3.4 | 50 | A localization $S^{-1}A$ of a Dedekind domain is a Dedekind domain. | `IsLocalization.isDedekindDomain` | in Mathlib |
| Proposition 3.5 | 50 | A localization of a noetherian (resp. integrally closed) domain is noetherian (resp. integrally closed). | `IsLocalization.isNoetherianRing`, `isIntegrallyClosed_of_isLocalization` | in Mathlib |
| Proposition 3.6 | 50 | A noetherian domain is Dedekind iff its localization at every nonzero prime is a discrete valuation ring. | `isDedekindDomain_iff_isDiscreteValuationRing_atPrime`, `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` | in Mathlib |
| Theorem 3.7 | 51 | Every proper nonzero ideal of a Dedekind domain is uniquely a product of powers of distinct primes. | `Ideal.uniqueFactorizationMonoid`, `Ideal.finprod_heightOneSpectrum_factorization` | in Mathlib |
| Lemma 3.8 | 51 | In a noetherian ring every ideal contains a product of nonzero prime ideals. | `PrimeSpectrum.exists_primeSpectrum_prod_le`, `PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain` | in Mathlib |
| Lemma 3.9 | 51 | If $\mathfrak a,\mathfrak b$ are relatively prime then so are $\mathfrak a^m,\mathfrak b^n$. | `Ideal.pow_sup_pow_eq_top`, `IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne` | in Mathlib |
| Lemma 3.10 | 51 | For a maximal ideal $\mathfrak p$, $A/\mathfrak p^m\to A_{\mathfrak p}/\mathfrak q^m$ is an isomorphism. | `MilneANT.lemma_3_10` | proved |
| Remark 3.11 | 52 | For $\mathfrak a$ a power of a maximal ideal and $S=A\setminus\mathfrak p$, extension then contraction returns $\mathfrak a$. | `MilneANT.remark_3_11` | proved |
| Remark 3.12 | 52 | In the factorization, $s_i>0$ iff $\mathfrak aA_{\mathfrak p_i}\ne A_{\mathfrak p_i}$ iff $\mathfrak a\subseteq\mathfrak p_i$. | `Ideal.mem_normalizedFactors_iff`, `Ideal.dvd_iff_le` | in Mathlib |
| Corollary 3.13 | 53 | $\mathfrak a\subseteq\mathfrak b$ iff $\mathfrak aA_{\mathfrak p}\subseteq\mathfrak bA_{\mathfrak p}$ for all nonzero primes; hence equality is local. | `Ideal.le_of_localization_maximal`, `Ideal.eq_of_localization_maximal` | in Mathlib |
| Corollary 3.14 | 53 | A domain with finitely many primes is Dedekind iff it is a principal ideal domain. | `IsPrincipalIdealRing.of_finite_primes`, `IsPrincipalIdealRing.isDedekindDomain` | in Mathlib |
| Corollary 3.15 | 53 | If $\mathfrak a\supseteq\mathfrak b\ne0$ in a Dedekind domain then $\mathfrak a=\mathfrak b+(a)$ for some $a$. | `IsDedekindDomain.exists_sup_span_eq` | in Mathlib |
| Corollary 3.16 | 53 | Every ideal containing a nonzero $a$ is generated by $a$ and one more element. | `IsDedekindDomain.exists_eq_span_pair` | in Mathlib |
| Corollary 3.17 | 54 | For a nonzero ideal $\mathfrak a$ there is $\mathfrak a'$ with $\mathfrak a\mathfrak a'$ principal, can be chosen prime to a given ideal $\mathfrak c$. | `MilneANT.cor_3_17_element`, `MilneANT.cor_3_17_principal`, `MilneANT.cor_3_17_coprime` | proved |
| Proposition 3.18 | 54 | A Dedekind domain that is a unique factorization domain is a principal ideal domain. | `IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid` | in Mathlib |
| Example 3.19 | 55 | For a discrete valuation ring, fractional ideals are $(\pi^m)$, $m\in\mathbb Z$, forming a free abelian group of rank 1. | `MilneANT.example_3_19` | proved |
| Theorem 3.20 | 55 | Fractional ideals of a Dedekind domain form a group, free abelian on the nonzero primes. | `FractionalIdeal.semifield`, `FractionalIdeal.finprod_heightOneSpectrum_factorization'`, `FractionalIdeal.count_mul` | in Mathlib |
| Remark 3.21 | 55 | (a) Noether: a domain whose fractional ideals form a group is Dedekind; (b) compatibility of localization with products and inverses; (c) a direct proof of inverses. | `isDedekindDomain_iff_mul_inv_cancel`, `FractionalIdeal.coe_ideal_mul_inv` | in Mathlib |
| Example 3.22 | 56 | The coordinate ring of an affine complex elliptic curve is Dedekind with class group $\cong\mathbb C/\Lambda$, uncountable. | `MilneANT.ellipticCoordinateRingInput`, `MilneANT.EllipticCoordinateRingInput`, `MilneANT.example_3_22_uncountable`, `MilneANT.not_isDedekindDomain_ellipticW_zero_zero` | proved |
| Proposition 3.23 | 57 | $\mathfrak a\mapsto S^{-1}\mathfrak a$ is an isomorphism from the subgroup of ideals generated by primes not meeting $S$ onto the ideal group of $S^{-1}A$. | `MilneANT.prop_3_23` | proved |
| Remark 3.24 | 57 | If the class group is finite, inverting a suitable element gives a principal ideal domain. | `MilneANT.remark_3_24` | proved |
| Remark 3.25 | 57 | For a noetherian domain, being Dedekind is equivalent to local rings at primes being valuation rings, fractional ideals forming a group, and every fractional ideal being invertible. | `isDedekindDomain_iff_isDiscreteValuationRing_atPrime`, `isDedekindDomain_iff_mul_inv_cancel` | in Mathlib |
| Example 3.26 | 57 | Examples of discrete valuations: order of a meromorphic function; $p$-adic order on the fraction field of a principal ideal domain; $\mathrm{ord}_{\mathfrak p}$ on a Dedekind domain. | `MilneANT.example_3_26_a`, `MilneANT.example_3_26_b`, `MilneANT.example_3_26_c` | proved |
| Proposition 3.27 | 58 | For a discrete valuation $v$ on $K$, $\{v\ge0\}$ is a principal ideal domain with maximal ideal $\{v>0\}$ generated by any element of minimal positive value. | `Valuation.valuationSubring_isPrincipalIdealRing`, `Valuation.valuationSubring_isDiscreteValuationRing` | in Mathlib |
| Proposition 3.28 | 58 | Approximation: for distinct primes and elements $x_i$ there is $x$ with $\mathrm{ord}_{\mathfrak p_i}(x-x_i)>n$. | `IsDedekindDomain.exists_forall_sub_mem_ideal` | in Mathlib |
| Theorem 3.29 | 59 | The integral closure of a Dedekind domain in a finite separable extension of its fraction field is Dedekind. | `TauCeti.IsIntegralClosure.isDedekindDomain`, `TauCeti.integralClosure.isDedekindDomain` | in Mathlib |
| Lemma 3.30 | 59 | A domain containing a field $k$ and algebraic over $k$ is a field. | `isField_of_isIntegral_of_isField'`, `Subalgebra.isField_of_algebraic` | in Mathlib |
| Theorem 3.31 | 59 | Finitely generated torsion-free modules over a Dedekind domain are direct sums of fractional ideals, classified by rank and class. | `MilneANT.thm_3_31`, `MilneANT.TorsionFreeModuleStructure`, `MilneANT.thm_3_31_rank_one` | proved |
| Theorem 3.32 | 60 | Invariant factor theorem for $M\subseteq N$ torsion-free over a Dedekind domain. | `MilneANT.InvariantFactorTheorem`, `MilneANT.InvariantFactors.thm_3_32_exists`, `MilneANT.InvariantFactors.thm_3_32_unique` | proved |
| Lemma 3.33 | 61 | A prime $P$ of $B$ divides $\mathfrak pB$ iff $P\cap A=\mathfrak p$. | `Ideal.liesOver_iff_dvd_map` | in Mathlib |
| Theorem 3.34 | 61 | $\sum e_if_i=[L:K]$; in the Galois case $efg=[L:K]$ with all $e_i$, $f_i$ equal and transitive Galois action. | `Ideal.sum_ramification_inertia_eq_finrank`, `Ideal.exists_smul_eq_of_isGaloisGroup`, `Ideal.ramificationIdx_eq_of_isGaloisGroup`, `Ideal.inertiaDeg_eq_of_isGaloisGroup`, `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`, `QuadFormsKB.Binary.Rel.sum_ramificationIdx_mul_inertiaDeg` | in Mathlib |
| Theorem 3.35 | 62 | For $B$ free over $A$, a prime $\mathfrak p$ ramifies iff $\mathfrak p\mid\mathrm{disc}(B/A)$; only finitely many ramify. | `NumberField.not_dvd_discr_iff_isUnramifiedIn` | in Mathlib |
| Lemma 3.36 | 62 | For a free $A$-algebra with basis $e_i$, reduction mod $\mathfrak a$ gives a basis of $B/\mathfrak aB$ with discriminant the reduction. | `MilneANT.lemma_3_36` | proved |
| Lemma 3.37 | 62 | The discriminant of a product of rings free over $A$ is the product of discriminants. | `MilneANT.lemma_3_37` | proved |
| Lemma 3.38 | 63 | For a perfect field $k$ and a finite $k$-algebra $B$: $B$ is reduced iff $\mathrm{disc}(B/k)\ne0$. | `MilneANT.lemma_3_38` | proved |
| Remark 3.39 | 64 | (a) $\mathrm{ord}_{\mathfrak p}\mathrm{disc}\ge\sum f_i(e_i-1)$ with equality when the characteristic does not divide the $e_i$; (b) relative discriminant ideal defined without freeness. | `MilneANT.remark_3_39_a_le`, `MilneANT.remark_3_39_a_eq`, `MilneANT.relDiscr_int`, `MilneANT.remark_3_39_b` | proved |
| Theorem 3.41 | 64 | If $B=A[\alpha]$, then $\mathfrak pB=\prod(\mathfrak p,g_i(\alpha))^{e_i}$ from the factorization of the minimal polynomial mod $\mathfrak p$, with $f_i=\deg g_i$. | `KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map`, `KummerDedekind.emultiplicity_factors_map_eq_emultiplicity`, `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` | in Mathlib |
| Remark 3.43 | 65 | The conclusion of 3.41 holds at $\mathfrak p$ if $D(1,\alpha,\dots)=\mathfrak a\,\mathrm{disc}(B/A)$ with $\mathfrak p\nmid\mathfrak a$. | `MilneANT.remark_3_43` | proved |
| Example 3.44 | 65 | Splitting of primes in $\mathbb Q[\sqrt m]$ via the Legendre symbol, including the prime 2. | `MilneANT.example_3_44_i`, `MilneANT.example_3_44_ii_split`, `MilneANT.example_3_44_ii_inert`, `MilneANT.example_3_44_iii_split` | proved |
| Example 3.45 | 66 | For odd $p$: $p\equiv1\bmod4$ iff $(p)$ splits in $\mathbb Z[i]$ iff $p=a^2+b^2$. | `MilneANT.example_3_45` | proved |
| Remark 3.50 | 67 | The set of split primes of $\mathbb Q[\sqrt m]$ is described by the Legendre symbol; Galois fields are determined by their split primes (Theorem 8.38). | `MilneANT.remark_3_50_split`, `MilneANT.galoisDeterminedBySplitPrimes`, `MilneANT.GaloisDeterminedBySplitPrimes` | proved |
| Proposition 3.53 | 68 | An Eisenstein polynomial at $\mathfrak p$ is irreducible and $\mathfrak p$ is totally ramified: $\mathfrak pB=P^m$, $P=(\mathfrak p,\alpha)$. | `MilneANT.prop_3_53_irreducible`, `MilneANT.prop_3_53` | proved |

## Chapter 4. The Finiteness of the Class Number

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Proposition 4.1 | 71 | For $L/K$ of number fields, $N_{L/K}(\mathfrak a B)=\mathfrak a^{[L:K]}$; in the Galois case $N\mathfrak P\cdot B=\prod_\sigma \sigma\mathfrak P$; and $\mathrm{Nm}(\beta)A=N(\beta B)$. | `Ideal.relNorm_algebraMap`, `Ideal.relNorm_eq_pow_of_isPrime_isGalois`, `Ideal.relNorm_singleton` | in Mathlib |
| Proposition 4.2 | 71 | The ideal norm of $\mathfrak a\subset\mathcal O_K$ is the principal ideal generated by the index $(\mathcal O_K:\mathfrak a)$, so the numerical norm is multiplicative; and $(\mathfrak a:\mathfrak b)=N(\mathfrak a^{-1}\mathfrak b)$ for fractional ideals $\mathfrak b\subset\mathfrak a$. | `Ideal.relNorm_int`, `Ideal.absNorm_relNorm`, `Ideal.absNorm_apply`, `FractionalIdeal.absNorm` | in Mathlib |
| Theorem 4.3 | 72 | Minkowski bound: every ideal class contains an integral ideal $\mathfrak a$ with $N\mathfrak a\le \frac{n!}{n^n}\left(\frac4\pi\right)^s\lvert\Delta_K\rvert^{1/2}$. | `NumberField.exists_ideal_in_class_of_norm_le` | in Mathlib |
| Theorem 4.4 | 72 | The class number of a number field is finite. | `NumberField.RingOfIntegers.instFintypeClassGroup`, `NumberField.classNumber`, `NumberField.classNumber_pos` | in Mathlib |
| Example 4.5 | 73 | $\mathbb Z[i]$ is a principal ideal domain (indeed Euclidean), since the Minkowski bound for $\mathbb Q[i]$ is below 2. | `GaussianInt` | in Mathlib |
| Example 4.6 | 73 | The class group of $\mathbb Z[\sqrt{-5}]$ has order 2, generated by $(2,1+\sqrt{-5})$. | `MilneANT.example_4_6` | proved |
| Example 4.7 | 73 | A cubic field with $-49\le\Delta<0$ has class number 1; for $X^3+10X+1$ ($\Delta=-4027$) the class group is cyclic of order 6. | `MilneANT.example_4_7_a`, `MilneANT.example47ClassGroup`, `MilneANT.Example47ClassGroup` | proved |
| Example 4.8 | 74 | For a root $\alpha$ of $X^5-X+1$, $\mathcal O_{\mathbb Q[\alpha]}=\mathbb Z[\alpha]$ is a principal ideal domain (discriminant $19\cdot151$). | `MilneANT.example_4_8` | proved |
| Theorem 4.9 | 74 | There is no unramified extension of $\mathbb Q$ other than $\mathbb Q$ (Minkowski). | `NumberField.abs_discr_gt_two`, `NumberField.exists_not_isUnramifiedIn`, `NumberField.finrank_eq_one_of_unramified` | in Mathlib |
| Corollary 4.10 | 74 | There is no irreducible monic $f\in\mathbb Z[X]$ of degree $>1$ with discriminant $\pm1$. | `MilneANT.cor_4_10` | proved |
| Remark 4.11 | 74 | Class field theory: the Hilbert class field of $K$ has Galois group $\mathrm{Cl}(\mathcal O_K)$; e.g. $\mathbb Q[\sqrt{-1},\sqrt5]/\mathbb Q[\sqrt5]$ is unramified. | `MilneANT.remark_4_11_hilbert`, `MilneANT.remark_4_11_example` | proved |
| Lemma 4.14 | 75 | For a subgroup $\Lambda$ of a finite-dimensional real vector space: discrete iff some open set meets it only in 0 iff compact sets meet it in finite sets iff bounded sets meet it in finite sets. | `Metric.finite_isBounded_inter_isClosed`, `AddSubgroup.isClosed_of_discreteTopology`, `DiscreteTopology.of_continuous_injective` | in Mathlib |
| Proposition 4.15 | 76 | A subgroup of a real vector space $V$ is a lattice (generated by $\mathbb R$-independent vectors) iff it is discrete. | `instModuleFree_of_discrete_submodule`, `instModuleFinite_of_discrete_submodule`, `ZLattice.rank` | in Mathlib |
| Remark 4.16 | 77 | The volume of a fundamental parallelepiped is $\lvert\det(f_1,\dots,f_n)\rvert$, independent of the basis; for full lattices $\Lambda'\subset\Lambda$ the ratio of volumes is the index. | `ZSpan.volume_fundamentalDomain`, `ZLattice.covolume_div_covolume_eq_relIndex`, `ZLattice.covolume_eq_det` | in Mathlib |
| Theorem 4.17 | 77 | Blichfeldt: if $\mu(S)>\mu(D_0)$ then $S$ contains distinct $\alpha,\beta$ with $\beta-\alpha\in\Lambda$. | `MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd` | in Mathlib |
| Remark 4.18 | 78 | Geometric reformulation; a convex set symmetric about the origin of volume $>2^n\mu(D)$ contains a nonzero lattice point. | `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | in Mathlib |
| Theorem 4.19 | 78 | Minkowski: a compact convex symmetric set $T$ with $\mu(T)\ge 2^n\mu(D)$ contains a nonzero lattice point. | `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` | in Mathlib |
| Remark 4.20 | 78 | Minkowski's theorem proves that every positive integer is a sum of four squares (Lagrange). | `Nat.sum_four_squares`, `Nat.Prime.sum_four_squares` | in Mathlib |
| Lemma 4.22 | 80 | In $V=\mathbb R^r\times\mathbb C^s$ the set $\{\lVert x\rVert\le t\}$ has volume $2^r(\pi/2)^s t^n/n!$. | `NumberField.mixedEmbedding.convexBodySum_volume` | in Mathlib |
| Lemma 4.23 | 80 | Dirichlet integral: $\int_{x_i\ge0,\sum x_i\le t}\prod x_i^{a_i}\,dx=t^{\sum a_i+m}\prod\Gamma(a_i+1)/\Gamma(\sum a_i+m+1)$. | `MilneANT.lemma_4_23` | proved |
| Lemma 4.25 | 81 | Arithmetic-geometric mean inequality for positive reals. | `Real.geom_mean_le_arith_mean` | in Mathlib |
| Proposition 4.26 | 81 | For a nonzero ideal $\mathfrak a$, $\sigma(\mathfrak a)$ is a full lattice in $\mathbb R^r\times\mathbb C^s$ with covolume $2^{-s}N\mathfrak a\,\lvert\Delta_K\rvert^{1/2}$. | `NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis`, `NumberField.mixedEmbedding.covolume_integerLattice` | in Mathlib |
| Proposition 4.27 | 82 | Every nonzero ideal $\mathfrak a$ contains $\alpha\ne0$ with $\lvert\mathrm{Nm}\,\alpha\rvert\le B_K N\mathfrak a$. | `NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr`, `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_of_norm_le` | in Mathlib |
| Theorem 4.29 | 84 | For a quadratic field of discriminant $d_K$, the class group (narrow class group if $d>0$) is in bijection with equivalence classes of integral binary quadratic forms of discriminant $d_K$. | `MilneANT.thm_4_29_imaginary`, `MilneANT.quadraticFormsIdealClasses`, `MilneANT.QuadraticFormsIdealClasses` | proved |

## Chapter 5. The Unit Theorem

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Theorem 5.1 | 87 | Dirichlet unit theorem: the unit group of $\mathcal O_K$ is finitely generated of rank $r+s-1$. | `NumberField.Units.finrank_eq`, `NumberField.Units.rank`, `NumberField.Units.exist_unique_eq_mul_prod`, `NumberField.Units.fundSystem` | in Mathlib |
| Lemma 5.2 | 88 | $\alpha\in K$ is a unit iff $\alpha\in\mathcal O_K$ and $\mathrm{Nm}_{K/\mathbb Q}\alpha=\pm1$. | `NumberField.isUnit_iff_norm` | in Mathlib |
| Example 5.3 | 88 | Units of quadratic fields: finite torsion-only for $d<0$ with $\mu(K)=\{\pm1\}$ except $\mathbb Q[i]$ and $\mathbb Q[\sqrt{-3}]$; infinitely many for $d>0$. | `MilneANT.example_5_3_isUnit_iff`, `MilneANT.example_5_3_neg`, `MilneANT.example_5_3_pos`, `MilneANT.torsionOrder_eq_two_of_isReal` | proved |
| Example 5.4 | 88 | For $X^3+10X+1$, $\alpha$ is a unit (norm $-1$), of infinite order, and later a fundamental unit. | `MilneANT.example_5_4` | proved |
| Proposition 5.5 | 89 | There are only finitely many algebraic integers of bounded degree all of whose conjugates have absolute value $<M$. | `NumberField.Embeddings.finite_of_norm_le`, `NumberField.Embeddings.coeff_bdd_of_norm_le` | in Mathlib |
| Corollary 5.6 | 89 | An algebraic integer all of whose conjugates have absolute value 1 is a root of unity. | `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`, `NumberField.Embeddings.pow_eq_one_of_norm_le_one` | in Mathlib |
| Remark 5.7 | 89 | The integrality hypothesis in 5.6 is needed: $(3+4i)/5$ has all conjugates of absolute value 1 but is not a root of unity. | `MilneANT.remark_5_7` | proved |
| Proposition 5.8 | 89 | The image of $L:U\to H$ (log embedding) is a lattice in the trace-zero hyperplane and the kernel is finite, equal to $\mu(K)$. | `NumberField.Units.instZLattice_unitLattice`, `NumberField.Units.dirichletUnitTheorem.logEmbedding_ker`, `NumberField.Units.dirichletUnitTheorem.unitLattice_inter_ball_finite`, `NumberField.Units.mem_torsion` | in Mathlib |
| Theorem 5.9 | 90 | The image $L(U)$ is a full lattice in $H$; hence $\mathrm{rank}\,U=r+s-1$. | `NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top`, `NumberField.Units.unitLattice_rank`, `NumberField.Units.dirichletUnitTheorem.exists_unit` | in Mathlib |
| Lemma 5.10 | 91 | A real $m\times m$ matrix with negative off-diagonal entries and positive row sums is invertible. | — | in Mathlib |
| Theorem 5.11 | 92 | The group of $S$-units is finitely generated of rank $r+s+\#S-1$. | `MilneANT.theorem_5_11` | proved |
| Proposition 5.12 | 92 | For a CM field $K$ with maximal totally real subfield $K^+$, the index of $\mu(K)U_{K^+}$ in $U_K$ is 1 or 2. | `NumberField.IsCMField.indexRealUnits_eq_one_or_two` | in Mathlib |
| Lemma 5.13 | 94 | For a cubic field with negative discriminant and fundamental unit $\varepsilon>1$: $\lvert\Delta_K\rvert<4\varepsilon^3+24$. | `MilneANT.lemma_5_13` | proved |
| Example 5.14 | 95 | For $X^3+10X+1$: $\alpha^{-1}$ is the fundamental unit, $U_K=\{\pm\alpha^m\}$, and the class group is cyclic of order 6. | `MilneANT.example_5_14_units`, `MilneANT.example_5_14_classGroup` | proved |

## Chapter 6. Cyclotomic Extensions; Fermat's Last Theorem

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Lemma 6.1 | 97 | If $\zeta$ is a primitive $n$th root of 1, then $\zeta^m$ is primitive iff $\gcd(m,n)=1$. | `IsPrimitiveRoot.pow_iff_coprime`, `IsPrimitiveRoot.pow_of_coprime` | in Mathlib |
| Proposition 6.2 | 98 | For $\zeta$ a primitive $p^r$th root of 1 and $K=\mathbb Q[\zeta]$: (a) $[K:\mathbb Q]=\varphi(p^r)$; (b) $\mathcal O_K=\mathbb Z[\zeta]$; (c) $1-\zeta$ is a prime element with $(p)=(1-\zeta)^{\varphi(p^r)}$; (d) $\Delta=\pm p^c$ with $c=p^{r-1}$, $p$ the only ramified prime. | `IsCyclotomicExtension.Rat.finrank`, `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow`, `IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one`, `IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow`, `IsCyclotomicExtension.Rat.discr_prime_pow'`, `IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one` | in Mathlib |
| Remark 6.3 | 101 | (a) Sign of $\mathrm{disc}\,\mathbb Q[\zeta]$ is $(-1)^s$, with parity of $[\mathbb Q[\zeta]:\mathbb Q]/2$ for prime powers; (b) $\mathbb Q[\zeta_{p^r}]\cap\mathbb Q[\zeta_{q^s}]=\mathbb Q$ for distinct primes. | `MilneANT.remark_6_3_a_sign`, `MilneANT.remark_6_3_a_odd_iff`, `MilneANT.remark_6_3_b` | proved |
| Theorem 6.4 | 101 | For $\zeta$ a primitive $n$th root of 1: (a) $[\mathbb Q[\zeta]:\mathbb Q]=\varphi(n)$; (b) $\mathcal O=\mathbb Z[\zeta]$ with integral basis $1,\zeta,\dots,\zeta^{\varphi(n)-1}$; (c) ramified primes divide $n$, and for $n=p^rm$, $(p)=(P_1\cdots P_s)^{\varphi(p^r)}$. | `IsCyclotomicExtension.Rat.finrank`, `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`, `IsCyclotomicExtension.Rat.ramificationIdxIn_eq`, `IsCyclotomicExtension.Rat.inertiaDegIn_eq`, `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd`, `Polynomial.cyclotomic.irreducible_rat` | in Mathlib |
| Lemma 6.5 | 102 | For number fields $K,L$ with $[KL:\mathbb Q]=[K:\mathbb Q][L:\mathbb Q]$ and $d=\gcd(\Delta_K,\Delta_L)$, $\mathcal O_{KL}\subset d^{-1}\mathcal O_K\mathcal O_L$. | `MilneANT.lemma_6_5` | proved |
| Remark 6.6 | 102 | (a) $p\mid n$ ramifies unless $p=2$ and $n=2\cdot$odd; (b) $\mu(\mathbb Q[\zeta_n])$ is cyclic of order $n$ ($n$ even) or $2n$ ($n$ odd); (c) $\mathrm{disc}(KL)=\mathrm{disc}(K)^{[L:\mathbb Q]}\mathrm{disc}(L)^{[K:\mathbb Q]}$ when $\mathcal O_{KL}=\mathcal O_K\mathcal O_L$, and the formula for $\mathrm{disc}\,\mathbb Q[\zeta_n]$. | `IsCyclotomicExtension.Rat.torsionOrder_eq`, `IsCyclotomicExtension.Rat.discr`, `IsCyclotomicExtension.Rat.natAbs_discr`, `NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow`, `IsCyclotomicExtension.Rat.ramificationIdxIn_eq` | in Mathlib |
| Proposition 6.7 | 104 | For $n$ a prime power, every unit of $\mathbb Q[\zeta_n]$ is $\zeta v$ with $\zeta$ a root of unity and $v$ a unit of $\mathbb Q[\zeta_n]^+$. | `MilneANT.proposition_6_7`, `MilneANT.proposition_6_7_indexRealUnits`, `MilneANT.maximalRealSubfield_eq_adjoin` | proved |
| Theorem 6.8 | 104 | First case of Fermat's last theorem for regular primes: if $p\nmid h(\mathbb Q[\zeta_p])$ then $x^p+y^p=z^p$ has no solution with $p\nmid xyz$. | `MilneANT.theorem_6_8`, `MilneANT.theorem_6_8_of_isRegularPrime` | proved |
| Lemma 6.9 | 105 | The elements $x+\zeta^iy$ of $\mathbb Z[\zeta]$ ($0\le i\le p-1$) are pairwise relatively prime under the hypotheses of the proof of 6.8. | `MilneANT.lemma_6_9` | proved |
| Lemma 6.10 | 105 | For every $\alpha\in\mathbb Z[\zeta]$, $\alpha^p\in\mathbb Z+p\,\mathbb Z[\zeta]$. | `MilneANT.lemma_6_10` | proved |
| Lemma 6.11 | 105 | If $\alpha=\sum a_i\zeta^i$ with some $a_i=0$ is divisible by an integer $n$ in $\mathbb Z[\zeta]$, then $n\mid a_i$ for all $i$. | `MilneANT.lemma_6_11` | proved |

## Chapter 7. Absolute Values; Local Fields

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Proposition 7.2 | 108 | An absolute value is nonarchimedean iff $\{\lvert m\cdot 1\rvert : m\in\mathbb Z\}$ is bounded | `MilneANT.prop_7_2` | in Mathlib |
| Corollary 7.3 | 108 | If $\operatorname{char}K\ne 0$ then every absolute value on $K$ is nonarchimedean | `MilneANT.cor_7_3` | proved |
| Proposition 7.5 | 109 | For a nontrivial nonarchimedean $\lvert\cdot\rvert$, $v=\log\lvert\cdot\rvert$ is additive with $v(x+y)\ge\min$; if $v(K^\times)$ is discrete then $v$ is a multiple of a discrete valuation $K^\times\to\mathbb Z$ | `MilneANT.prop_7_5` | proved |
| Proposition 7.6 | 109 | For a nonarchimedean absolute value, $A=\{\lvert a\rvert\le1\}$ is a ring with units $\{\lvert a\rvert=1\}$ and unique maximal ideal $\{\lvert a\rvert<1\}$; discrete iff $\mathfrak m$ principal, then $A$ is a discrete valuation ring | `MilneANT.prop_7_6` | proved |
| Remark 7.7 | 109 | There are nondiscrete nonarchimedean absolute values (e.g. an extension of $\lvert\cdot\rvert_p$ to $\overline{\mathbb Q}$, with value group $p^{\mathbb Q}$) | `MilneANT.remark_7_7`, `MilneANT.remark_7_7_algebraicClosure`, `MilneANT.remark_7_7_valueGroup` | proved |
| Proposition 7.8 | 110 | For absolute values with $\lvert\cdot\rvert_1$ nontrivial: same topology $\iff$ $\lvert\alpha\rvert_1<1\Rightarrow\lvert\alpha\rvert_2<1$ $\iff$ $\lvert\cdot\rvert_2=\lvert\cdot\rvert_1^a$, $a>0$ | `MilneANT.prop_7_8` | in Mathlib |
| Theorem 7.12 | 112 | A nontrivial absolute value on $\mathbb Q$ is equivalent to $\lvert\cdot\rvert_\infty$ or to $\lvert\cdot\rvert_p$ for exactly one prime $p$ | `Rat.AbsoluteValue.equiv_real_or_padic` | in Mathlib |
| Theorem 7.13 | 113 | $\prod_p\lvert a\rvert_p=1$ over all places of $\mathbb Q$ | `MilneANT.thm_7_13` | in Mathlib |
| Theorem 7.14 | 113 | A number field has exactly one prime (equivalence class of absolute values) for each prime ideal, each real embedding, each conjugate pair of complex embeddings | `MilneANT.theorem7_14`, `MilneANT.thm_7_14_unconditional`, `MilneANT.exists_finitePlace_isEquiv`, `MilneANT.exists_infinitePlace_isEquiv_of_remark_7_49a` | proved |
| Theorem 7.15 | 114 | For every nonzero $\alpha$ in a number field $K$, $\prod_v\lvert\alpha\rvert_v=1$ with normalized absolute values | `NumberField.prod_abs_eq_one` | in Mathlib |
| Lemma 7.16 | 114 | (a) a prime of $K$ has finitely many extensions to a finite extension $L$; (b) $\prod_{w\mid v}\lvert\alpha\rvert_w=\lvert\mathrm{Nm}_{L/K}\alpha\rvert_v$ for $\alpha\in L$ | `MilneANT.lemma_7_16a_unconditional`, `MilneANT.lemma_7_16b` | proved |
| Remark 7.17 | 114 | Product formula also holds for finite extensions of $k(T)$ ($k$ finite) and for function fields over algebraically closed $k$ | `MilneANT.remark7_17a`, `MilneANT.remark7_17b`, `MilneANT.Remark7_17a`, `MilneANT.Remark7_17b` | proved |
| Lemma 7.18 | 115 | For nontrivial inequivalent $\lvert\cdot\rvert_1,\dots,\lvert\cdot\rvert_n$ there is $a$ with $\lvert a\rvert_1>1$, $\lvert a\rvert_i<1$ for $i\ne1$ | `AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv` | in Mathlib |
| Lemma 7.19 | 116 | There is an element close to $1$ for $\lvert\cdot\rvert_1$ and close to $0$ for $\lvert\cdot\rvert_i$, $i\ge2$ | `MilneANT.lemma_7_19` | proved |
| Theorem 7.20 | 116 | For nontrivial inequivalent absolute values $\lvert\cdot\rvert_i$ on $K$, $K$ is dense in $\prod_i K$ (and in $\prod K_i$) | `AbsoluteValue.denseRange_algebraMap_pi`, `NumberField.InfinitePlace.denseRange_algebraMap_pi` | in Mathlib |
| Corollary 7.21 | 116 | If $\prod_i\lvert a\rvert_i^{r_i}=1$ for all $a\in K^\times$ for nontrivial inequivalent absolute values, then all $r_i=0$ | `MilneANT.cor_7_21` | proved |
| Theorem 7.23 | 117 | Every valued field has a complete valued completion with the universal property for absolute-value-preserving maps to complete valued fields | `MilneANT.thm_7_23` | in Mathlib |
| Remark 7.24 | 117 | (a) completion unique up to unique isomorphism; (b) the image of $K$ in $\hat K$ is dense | `UniformSpace.Completion.denseRange_coe` | in Mathlib |
| Lemma 7.25 | 118 | For a complete discretely valued field, $A/\mathfrak m^n\to\hat A/\hat{\mathfrak m}^n$ is an isomorphism | `MilneANT.lemma_7_25` | proved |
| Proposition 7.26 | 118 | Every element of $\hat K$ has a unique series $\sum_{i\ge-n}a_i\pi^i$ with $a_i$ in a set of representatives of $A/\mathfrak m$ | `MilneANT.prop_7_26` | proved |
| Example 7.28 | 120 | $-1$ is a square in $\mathbb Q_5$ | `MilneANT.example_7_28` | proved |
| Example 7.29 | 120 | The series $\exp(x)$ converges in $\mathbb Q_p$ for $\operatorname{ord}(x)>1/(p-1)$ | `MilneANT.example_7_29_tendsto_iff`, `MilneANT.example_7_29_summable` | proved |
| Aside 7.30 | 121 | For a discrete valuation ring $R$, $\varprojlim R/\mathfrak m^n$ agrees with the completion $\hat R$ | `MilneANT.aside_7_30` | proved |
| Proposition 7.31 | 122 | In a complete discrete valuation ring, a simple root of $f$ mod $\pi$ lifts to a unique root | `MilneANT.prop_7_31` | proved |
| Theorem 7.32 | 122 | If $\lvert f(a_0)\rvert<\lvert f'(a_0)\rvert^2$ then $f$ has a root $a$ with $\lvert a-a_0\rvert\le\lvert f(a_0)/f'(a_0)^2\rvert$ | `hensels_lemma` | in Mathlib |
| Theorem 7.33 | 123 | A factorization $\bar f=g_0h_0$ into coprime monic polynomials over the residue field lifts uniquely to $f=gh$ | `MilneANT.thm_7_33` | proved |
| Lemma 7.34 | 123 | Over a local ring, if $\bar f,\bar g$ are coprime and $f$ is monic, then $(f,g)=A[X]$ with Bézout degree bounds | `MilneANT.lemma_7_34_isCoprime`, `MilneANT.lemma_7_34` | proved |
| Lemma 7.35 | 123 | Lifts of coprime monic factorizations over a local ring are unique | `MilneANT.lemma_7_35` | proved |
| Remark 7.36 | 124 | Coprime factorizations lift; $\mathbb Z_p$ contains the $(p-1)$st roots of 1; Teichmüller representatives | `MilneANT.remark_7_36_prod`, `MilneANT.remark_7_36_teichmuller`, `MilneANT.remark_7_36_padicInt` | proved |
| Remark 7.37 | 124 | Stronger Hensel: if $\lVert f-g_0h_0\rVert<\lvert\operatorname{Res}(g_0,h_0)\rvert^2$ (or $<\lvert\operatorname{disc}f\rvert$) then $f$ factors | `MilneANT.remark7_37Resultant`, `MilneANT.remark7_37Discriminant`, `MilneANT.Remark7_37Resultant`, `MilneANT.Remark7_37Discriminant` | proved |
| Theorem 7.38 | 125 | For $K$ complete with a discrete absolute value and $L/K$ finite separable of degree $n$, the absolute value extends uniquely, $L$ is complete, and $\lvert\beta\rvert_L=\lvert\mathrm{Nm}_{L/K}\beta\rvert_K^{1/n}$ | `spectralNorm_extends`, `spectralNorm_unique_field_norm_ext` | in Mathlib |
| Corollary 7.40 | 126 | For $K$ as in 7.38 and $\Omega/K$ separable algebraic (possibly infinite), $\lvert\cdot\rvert_K$ extends uniquely to $\Omega$ | `spectralNorm_unique_field_norm_ext`, `spectralMulAlgNorm` | in Mathlib |
| Remark 7.41 | 126 | The extension to $\Omega$ is nonarchimedean but need not be discrete or complete; the completion of $\Omega$ is algebraically closed ($\mathbb C_p$) | `PadicComplex.isAlgClosed` | in Mathlib |
| Corollary 7.42 | 126 | For $K$ complete and $L/K$ finite, $n=ef$ | `MilneANT.cor_7_42` | proved |
| Proposition 7.44 | 127 | Newton polygon: segments of length $n_i$ and slope $s_i$ correspond to exactly $n_i$ roots of valuation $s_i$, and $\prod_{\operatorname{ord}\alpha_i=s_i}(X-\alpha_i)$ has coefficients in $K$ | `MilneANT.prop_7_44` | proved |
| Proposition 7.46 | 128 | For $K$ complete with a discrete absolute value, $A$ is compact iff $A/\mathfrak m$ is finite | `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField` | in Mathlib |
| Corollary 7.47 | 128 | If the residue field is finite, then $\mathfrak p^n$, $1+\mathfrak p^n$ and $A$ are compact | `IsNonarchimedeanLocalField.isCompact_closedBall` | in Mathlib |
| Definition 7.48 | 128 | A local field is a field with a nontrivial absolute value that is locally compact | `MilneANT.IsLocalFieldMilne.completeSpace` | proved |
| Remark 7.49 | 129 | Classification of local fields: (a) complete archimedean gives $\mathbb R$ or $\mathbb C$; (b) characteristic $0$ nonarchimedean gives finite extensions of $\mathbb Q_p$; (c) characteristic $p$ gives $k((T))$ | `MilneANT.Remark7_49a`, `MilneANT.Remark7_49b`, `MilneANT.Remark7_49c`, `MilneANT.remark_7_49a_locallyCompact` | proved |
| Proposition 7.50 | 129 | Finite unramified subextensions of $L/K$ correspond bijectively to finite subextensions of the residue field, with Galois compatibility | `MilneANT.prop_7_50`, `MilneANT.Prop7_50`, `MilneANT.HenselExt.hensel_of_algebraic`, `MilneANT.ResidueSub.isUnramified_of_le` | proved |
| Corollary 7.51 | 130 | There is a largest unramified extension $K_0\subset L$; for finite $k$ it is obtained by adjoining prime-to-$p$ roots of unity | `MilneANT.cor_7_51`, `MilneANT.Cor7_51` | proved |
| Corollary 7.52 | 130 | The residue field of $K^{\mathrm{al}}$ is $k^{\mathrm{al}}$ and $K^{\mathrm{un}}$ exists | `MilneANT.cor_7_52`, `MilneANT.Cor7_52` | proved |
| Remark 7.53 | 131 | The category of finite unramified extensions of $K$ is equivalent to that of finite separable extensions of $k$ | `MilneANT.remark_7_53`, `MilneANT.Remark7_53`, `MilneANT.Remark753.hom_equiv`, `MilneANT.Remark753.exists_lift` | proved |
| Example 7.54 | 131 | Unramified extension $K_n$ of degree $n$, splitting field of $X^{q^n}-X$, cyclic Galois group generated by Frobenius | `MilneANT.example_7_54`, `MilneANT.Example7_54` | proved |
| Proposition 7.55 | 131 | $L/K$ is totally ramified iff $L=K[\alpha]$ with $\alpha$ a root of an Eisenstein polynomial | `MilneANT.prop_7_55` | proved |
| Remark 7.56 | 132 | For totally ramified $L/K$, $B=A[\Pi]$ | `MilneANT.remark_7_56` | proved |
| Lemma 7.57 | 132 | The ramification groups $G_i$ are normal and $G_i=\{1\}$ for large $i$ | `MilneANT.lemma_7_57_normal`, `MilneANT.lemma_7_57_eq_bot` | proved |
| Theorem 7.58 | 132 | $G_0$ is the inertia group with fixed field the maximal unramified subextension; $G_i$ described by $\lvert\sigma\Pi-\Pi\rvert<\lvert\Pi\rvert^i$ | `MilneANT.thm_7_58a`, `MilneANT.thm_7_58b_le`, `MilneANT.Theorem7_58b`, `MilneANT.theorem_7_58b` | proved |
| Corollary 7.59 | 133 | The filtration has $G/G_0=\mathrm{Gal}(l/k)$, $G_0/G_1\hookrightarrow l^\times$, $G_i/G_{i+1}\hookrightarrow l$; $\mathrm{Gal}(L/K)$ is solvable for finite $k$ | `MilneANT.cor_7_59_units`, `MilneANT.cor_7_59_additive`, `MilneANT.cor_7_59_isSolvable`, `MilneANT.cor_7_59_units_unconditional` | proved |
| Proposition 7.60 | 133 | If $\alpha$ is separable over $K[\beta]$ and closer to $\beta$ than to any $K$-conjugate, then $K[\alpha]\subset K[\beta]$ | `IsKrasner.krasner`, `IsKrasner.of_completeSpace` | in Mathlib |
| Proposition 7.61 | 134 | A monic polynomial sufficiently close to an irreducible $f$ is irreducible, and each root $\beta$ of $g$ belongs to a root $\alpha$ of $f$ with $K[\alpha]=K[\beta]$ | `MilneANT.prop_7_61` | proved |
| Corollary 7.62 | 134 | A finite extension $K$ of $\mathbb Q_p$ is $L\cdot\mathbb Q_p$ for a number field $L$ with $[L:\mathbb Q]=[K:\mathbb Q_p]$ | `MilneANT.cor_7_62` | proved |
| Proposition 7.63 | 135 | Close irreducible polynomials define the same set of field extensions $\{K[\alpha]\}=\{K[\beta]\}$ | `MilneANT.prop_7_63` | proved |
| Proposition 7.64 | 135 | With finite residue field and characteristic zero, there are only finitely many totally ramified extensions of $K$ of a given degree up to isomorphism | `MilneANT.prop_7_64`, `MilneANT.prop_7_64_pos`, `MilneANT.Prop7_64`, `MilneANT.not_prop764Original` | proved |

## Chapter 8. Global Fields

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Proposition 8.1 | 138 | Extensions of an absolute value of $K$ to $L=K[\alpha]$ correspond bijectively to the irreducible factors of the minimal polynomial of $\alpha$ over the completion. | `MilneANT.prop_8_1`, `MilneANT.Prop8_1` | proved |
| Proposition 8.2 | 138 | For a finite separable $L/K$ and an absolute value on $K$ with completion $\hat K$, there are finitely many extensions and $L\otimes_K\hat K\cong\prod_i L_i$. | `MilneANT.prop_8_2`, `MilneANT.Prop8_2`, `MilneANT.exists_tensor_algEquiv_pi` | proved |
| Remark 8.3 | 138 | For $O_L=O_K[\alpha]$, the factorization $\mathfrak pO_L=\prod\mathfrak P_i^{e_i}$ with $\mathfrak P_i=(\mathfrak p,g_i(\alpha))$ matches the extensions of $\lvert\cdot\rvert_{\mathfrak p}$ (Hensel). | `MilneANT.remark_8_3`, `MilneANT.Remark8_3`, `MilneANT.finrank_completion_eq_ramificationIdx_mul_inertiaDeg`, `MilneANT.ramificationIdx_mul_inertiaDeg_le_finrank` | proved |
| Corollary 8.4 | 138 | In the situation of 8.2, $\mathrm{Nm}_{L/K}\alpha=\prod_i\mathrm{Nm}_{L_i/\hat K}\alpha$ and $\mathrm{Tr}_{L/K}\alpha=\sum_i\mathrm{Tr}_{L_i/\hat K}\alpha$. | `MilneANT.cor_8_4`, `MilneANT.cor_8_4_unconditional` | proved |
| Lemma 8.6 | 139 | For a local field $K$ and finite separable $L/K$, the normalized absolute value on $L$ satisfies $\lVert a\rVert=\lvert a\rvert^n$ with $n=[L:K]$. | `MilneANT.lemma_8_6_finite`, `MilneANT.lemma_8_6_infinite` | proved |
| Proposition 8.7 | 140 | For a finite extension of number fields $L/K$, a prime $v$ of $K$ and $\alpha\in L$: $\prod_{w\mid v}\lVert\alpha\rVert_w=\lVert\mathrm{Nm}_{L/K}\alpha\rVert_v$. | `MilneANT.prop_8_7_finite`, `MilneANT.prop_8_7_infinite` | proved |
| Theorem 8.8 | 140 | Product formula: for nonzero $\alpha$ in a number field, $\prod_w\lVert\alpha\rVert_w=1$ over all places. | `MilneANT.thm_8_8`, `NumberField.prod_abs_eq_one` | in Mathlib |
| Aside 8.9 | 140 | Artin-Whaples: a field with a set of absolute values satisfying the product-formula axiom and one local-field axiom is a global field. | `MilneANT.Aside8_9`, `MilneANT.aside8_9` | proved |
| Proposition 8.10 | 141 | For $L/K$ Galois of number fields and a place $w$, the map from the decomposition group $G_w$ to $\mathrm{Gal}(L_w/K_v)$ is an isomorphism. | `MilneANT.prop_8_10`, `MilneANT.Prop8_10` | proved |
| Proposition 8.11 | 142 | Decomposition and inertia fields (a)–(d). | `MilneANT.prop_8_11a`, `MilneANT.prop_8_11b`, `MilneANT.prop_8_11c`, `MilneANT.prop_8_11d` | proved |
| Proposition 8.13 | 143 | In a tower $K\subset L\subset M$ with $M/K$ Galois: (a) $H(\mathfrak P)=G(\mathfrak P)\cap H$; (b) if $H$ is normal, the decomposition group of $\mathfrak P_L$ is the image of $G(\mathfrak P)$ in $G/H$. | `MilneANT.prop_8_13a`, `MilneANT.prop_8_13b` | proved |
| 8.14 | 143 | $G(\tau\mathfrak P)=\tau G(\mathfrak P)\tau^{-1}$ and $(\tau\mathfrak P,L/K)=\tau(\mathfrak P,L/K)\tau^{-1}$; the Frobenius elements above $\mathfrak p$ form a conjugacy class. | `MilneANT.item_8_14_stabilizer`, `MilneANT.item_8_14_frob`, `MilneANT.item_8_14_conjClass`, `MilneANT.item_8_14_abelian` | proved |
| 8.15 | 144 | In a tower, $(\mathfrak Q,M/K)^{f(\mathfrak P/\mathfrak p)}=(\mathfrak Q,M/L)$. | `MilneANT.item_8_15` | proved |
| 8.17 | 144 | For $M=L_1L_2$, $\mathrm{Gal}(M/K)\hookrightarrow\mathrm{Gal}(L_1/K)\times\mathrm{Gal}(L_2/K)$ sends $(\mathfrak Q,M/K)$ to the pair of Frobenius elements; hence $\mathfrak p$ splits in $M$ iff in $L_1$ and $L_2$. | `MilneANT.item_8_17_injective`, `MilneANT.item_8_17`, `MilneANT.splitPrimes_sup` | proved |
| Example 8.18 | 145 | In $\mathbb Q(\zeta_n)$, for $p\nmid n$ the Frobenius at $p$ is $\zeta_n\mapsto\zeta_n^p$, of order the order of $p$ in $(\mathbb Z/n)^\times$. | `MilneANT.example_8_18` | proved |
| Example 8.19 | 145 | For $K=\mathbb Q(\sqrt d)$ and $p$ unramified, the Frobenius is $+1$ iff $p$ splits iff $d$ is a square mod $p$; it equals the Legendre symbol $(d/p)$. | `MilneANT.example_8_19` | proved |
| Theorem 8.20 | 146 | The Galois group of $f$ is the subgroup of $S_n$ fixing a chosen irreducible factor $F_1(X,t)$ of $\prod_\sigma(X-\sigma t\cdot\alpha)$ (van der Waerden). | `MilneANT.Theorem8_20`, `MilneANT.thm_8_20` | proved |
| Proposition 8.21 | 146 | If the Galois group of a monic separable $f$ has orbits of sizes $n_1,\dots,n_s$ on the roots, then $f$ factors over $K$ into irreducibles of degrees $n_i$. | `MilneANT.prop_8_21` | proved |
| Corollary 8.22 | 147 | Over a finite field, the cycle type of the Frobenius on the roots of a separable $f$ equals the degrees of the irreducible factors of $f$. | `MilneANT.cor_8_22` | proved |
| Theorem 8.23 | 147 | Dedekind: if $f\in O_K[X]$ is monic and factors mod $\mathfrak p$ into distinct irreducibles of degrees $n_i$, the Galois group of $f$ contains a permutation with disjoint cycles of lengths $n_i$. | `MilneANT.thm_8_23`, `MilneANT.thm_8_23'`, `MilneANT.DedekindFrobenius`, `MilneANT.dedekindFrobenius` | proved |
| Remark 8.24 | 147 | For real primes: if $f$ factors over $\mathbb R$ with $j$ quadratic factors, the Galois group contains a product of $j$ disjoint transpositions. | `MilneANT.Remark8_24`, `MilneANT.remark_8_24` | proved |
| Example 8.25 | 148 | The Galois group of $X^5-X-1$ over $\mathbb Q$ is $S_5$ (via factorizations mod 2 and 3). | `MilneANT.example_8_25` | proved |
| Lemma 8.26 | 148 | A transitive subgroup of $S_n$ containing an $(n-1)$-cycle and a transposition is $S_n$. | `MilneANT.lemma_8_26` | proved |
| Example 8.27 | 148 | Construction of monic integer polynomials of every degree $n$ with Galois group $S_n$ from three local conditions at 2, 3, 5. | `MilneANT.example_8_27` | proved |
| Remark 8.28 | 148 | A subgroup of $S_p$ ($p$ prime) containing an element of order $p$ and a transposition is $S_p$. | `Equiv.Perm.closure_prime_cycle_swap` | in Mathlib |
| Definition 8.30 | 149 | Natural density of a set of finite primes. | `MilneANT.HasNaturalDensity`, `MilneANT.primeCount` | formalized (a definition) |
| Theorem 8.31 | 149 | Chebotarev density theorem: the set of primes with Frobenius class $C$ has density $\lvert C\rvert/\lvert G\rvert$. | `MilneANT.theorem8_31`, `MilneANT.thm_8_31`, `MilneANT.Theorem8_31`, `MilneANT.thm_8_31_dirichlet` | proved |
| Corollary 8.32 | 149 | The primes that split in $L$ have density $1/[L:K]$; in particular infinitely many split. | `MilneANT.cor_8_32'`, `MilneANT.cor_8_32`, `MilneANT.cor_8_32_dirichlet`, `MilneANT.cor_8_32_infinite` | proved |
| Example 8.34 | 150 | For $K=\mathbb Q(\zeta_n)$, Frobenius is the class of $p$; hence primes equidistribute among residue classes mod $n$ (Dirichlet). | `MilneANT.example_8_34'`, `MilneANT.example_8_34`, `MilneANT.example_8_34_dirichlet`, `MilneANT.example_8_34_infinite` | proved |
| Example 8.35 | 150 | In a quadratic extension, half the primes split and half are inert. | `MilneANT.example_8_35'`, `MilneANT.example_8_35`, `MilneANT.example_8_35_dirichlet` | proved |
| Example 8.36 | 150 | Densities of the splitting types of a cubic over $\mathbb Q$ for each Galois group ($1$, $C_2$, $A_3$, $S_3$). | `MilneANT.example_8_36'`, `MilneANT.example_8_36`, `MilneANT.factorizationType_hasDirichletDensity`, `MilneANT.factorizationType_hasNaturalDensity'` | proved |
| Example 8.37 | 150 | Possible Galois groups and cycle-type counts of a quartic, giving factorization densities (for example $D_8$). | `MilneANT.example_8_37_D8'`, `MilneANT.example_8_37_D8` | proved |
| Theorem 8.38 | 151 | For Galois $L,M$ over $K$: $L\subset M$ iff $\mathrm{Spl}(L/K)\supset\mathrm{Spl}(M/K)$. | `MilneANT.thm_8_38`, `MilneANT.splitPrimes_sup` | proved |
| Corollary 8.39 | 152 | For Galois $L,M$ over $K$: $L=M$ iff $\mathrm{Spl}(M/K)=\mathrm{Spl}(L/K)$. | `MilneANT.cor_8_39` | proved |
| Remark 8.40 | 152 | (a) $L=M$ if the split sets differ by a density-zero set; (b) effective form; (c) fails without Galois; (d) an irreducible polynomial has a root mod almost all $p$ only if linear; (e) irreducible polynomials reducible at every $p$ exist. | `MilneANT.remark_8_40a_finite`, `MilneANT.remark_8_40a_dirichlet`, `MilneANT.remark_8_40a_natural`, `MilneANT.remark_8_40b` | proved |
| Theorem 8.42 | 153 | For a number field $K$, integer $N$ and finite set of primes $S$, only finitely many extensions of degree $N$ are unramified outside $S$. | `MilneANT.theorem8_42`, `MilneANT.Theorem8_42`, `MilneANT.ramifiedSupport_subset_of_isUnramifiedIn` | proved |
| Theorem 8.43 | 153 | Hermite: only finitely many number fields have a given discriminant. | `MilneANT.thm_8_43`, `NumberField.finite_of_discr_bdd` | in Mathlib |

## Definitions given in prose

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Prose definition D003 (unit) | 9 | An element of a ring with a two-sided inverse is a unit. | `IsUnit` | in Mathlib |
| Prose definition D006 (irreducible element) | 10 | A nonzero nonunit of a domain that is not a product of two nonunits is irreducible. | `Irreducible` | in Mathlib |
| Prose definition D009 (class number) | 12 | The class number of a number field is the order of the ideal class group of its ring of integers. | `NumberField.classNumber` | in Mathlib |
| Prose definition D010 (subalgebra generated by elements) | 16 | A[b_1,...,b_m] is the set of polynomial expressions in the b_i with coefficients in A. | `Algebra.adjoin` | in Mathlib |
| Prose definition D011 (ideal generated by elements) | 16 | The ideal generated by a_1, a_2, ... consists of finite combinations with coefficients in A. | `Ideal.span` | in Mathlib |
| Prose definition D012 (sum of ideals) | 16 | The sum of two ideals is the smallest ideal containing both. | `Ideal.add_eq_sup` | in Mathlib |
| Prose definition D013 (prime element) | 17 | A nonzero element is prime if the ideal it generates is prime, equivalently it divides a or b whenever it divides ab. | `Prime` | in Mathlib |
| Prose definition D014 (noetherian module) | 18 | A module is noetherian if every submodule is finitely generated. | `IsNoetherian` | in Mathlib |
| Prose definition D015 (local ring) | 19 | A ring is local if it has exactly one maximal ideal. | `IsLocalRing` | in Mathlib |
| Prose definition D016 (multiplicative subset) | 20 | A subset not containing 0, containing 1 and closed under multiplication. | `Submonoid` | in Mathlib |
| Prose definition D017 (localization S^{-1}A) | 20 | S^{-1}A is the set of fractions a/b with b in S inside the fraction field. | `IsLocalization` | in Mathlib |
| Prose definition D018 (localization at a prime) | 20 | A_p is the localization at the complement of the prime ideal p. | `Localization.AtPrime`, `IsLocalization.AtPrime` | in Mathlib |
| Prose definition D019 (bilinear map) | 23 | A map M x N -> P is A-bilinear if it is A-linear in each argument. | `LinearMap.mk₂'`, `IsBilinearMap` | in Mathlib |
| Prose definition D020 (tensor product) | 23 | The tensor product of two modules is the universal target of bilinear maps. | `TensorProduct`, `TensorProduct.mk`, `IsTensorProduct` | in Mathlib |
| Prose definition D024 (free module of rank m) | 23 | A module isomorphic to A^m through a basis is free of rank m. | `Module.Free` | in Mathlib |
| Prose definition D025 (extension of scalars) | 25 | For an algebra A -> B, B tensor_A M is a B-module with a universal property for maps into B-modules. | `TensorProduct`, `IsBaseChange` | in Mathlib |
| Prose definition D027 (saturated multiplicative subset) | 26 | S is saturated if ab in S implies a in S and b in S. | `Submonoid.MulSaturated` | in Mathlib |
| Prose definition D028 (integral element) | 27 | An element of L is integral over A if it is a root of a monic polynomial over A; algebraic integers are the case A = Z. | `IsIntegral` | in Mathlib |
| Prose definition D029 (symmetric polynomial) | 27 | A polynomial is symmetric if it is unchanged by permuting variables. | `MvPolynomial.IsSymmetric` | in Mathlib |
| Prose definition D030 (elementary symmetric polynomials) | 27 | The polynomials sigma_1 = sum of X_i, ..., sigma_r = X_1 ... X_r. | `MvPolynomial.esymm` | in Mathlib |
| Prose definition D031 (monomial ordering) | 27 | Monomials are ordered by total degree, ties broken lexicographically. | `MonomialOrder`, `MonomialOrder.lex` | in Mathlib |
| Prose definition D034 (basis of a module) | 33 | Elements that are linearly independent and span the module. | — | in Mathlib |
| Prose definition D035 (trace and norm) | 33 | Trace and norm of an element of a free algebra B over A are the trace and determinant of multiplication by it. | `Algebra.trace`, `Algebra.norm` | in Mathlib |
| Prose definition D036 (nondegenerate bilinear form) | 34 | A bilinear form is nondegenerate if its Gram determinant is nonzero, equivalently its kernels are trivial. | `LinearMap.BilinForm.Nondegenerate` | in Mathlib |
| Prose definition D038 (discriminant of elements) | 35 | D(b_1,...,b_m) = det(Tr(b_i b_j)). | `Algebra.discr`, `Algebra.traceForm` | in Mathlib |
| Prose definition D039 (discriminant of a free algebra) | 35 | disc(B/A) is the ideal (or class modulo squares of units) generated by the discriminant of a basis. | `Algebra.discr`, `NumberField.discr` | in Mathlib |
| Prose definition D041 (discriminant of a polynomial) | 39 | The discriminant of f is (-1)^{m(m-1)/2} times the norm of f'(beta), the product of squared root differences. | `Polynomial.discr` | in Mathlib |
| Prose definition D043 (monogenic number field) | 41 | A number field is monogenic if its ring of integers equals Z[alpha] for some alpha. | `MilneANT.IsMonogenic` | formalized (a definition) |
| Prose definition D044 (Euclidean domain) | 43 | A domain with a size function delta allowing division with remainder. | `EuclideanDomain` | in Mathlib |
| Prose definition D045 (Hermite normal form) | 44 | The unique triangular form of a nonsingular integer matrix with positive diagonal and reduced columns. | `MilneANT.remark_2_45_b_exists`, `MilneANT.remark_2_45_b_unique` | proved |
| Prose definition D047 (discrete valuation ring) | 48 | A principal ideal domain with exactly one nonzero prime, equivalently local and not a field. | `IsDiscreteValuationRing` | in Mathlib |
| Prose definition D050 (product of fractional ideals) | 55 | The product ab is the set of finite sums of products a b with a in a, b in b; again a fractional ideal. | `FractionalIdeal` | in Mathlib |
| Prose definition D051 (ideal class group) | 56 | Cl(A) is the group of fractional ideals modulo the principal ones. | `ClassGroup`, `ClassGroup.mk` | in Mathlib |
| Prose definition D052 (normalized discrete valuation) | 57 | A valuation v: K^x -> Z is normalized if surjective. | `MilneANT.IsNormalizedDiscreteValuation` | formalized (a definition) |
| Prose definition D054 (invariant factors) | 60 | The ideals b_i uniquely determined by a pair N in M of modules over a Dedekind domain. | `MilneANT.InvariantFactorTheorem` | proved |
| Prose definition D055 (ramified prime) | 61 | p is ramified in B if some ramification index exceeds 1. | `Algebra.IsUnramifiedIn` | in Mathlib |
| Prose definition D056 (ramification index) | 61 | The exponent e_i of P_i in the factorization of pB. | `Ideal.ramificationIdx` | in Mathlib |
| Prose definition D058 (residue degree) | 61 | f_i is the degree of the residue field extension B/P_i over A/p. | `Ideal.inertiaDeg` | in Mathlib |
| Prose definition D059 (nilpotent element) | 63 | An element with a power equal to 0. | `IsNilpotent` | in Mathlib |
| Prose definition D060 (reduced ring) | 63 | A ring with no nonzero nilpotent element. | — | in Mathlib |
| Prose definition D061 (perfect field) | 63 | Every finite extension is separable. | `PerfectField` | in Mathlib |
| Prose definition D063 (Eisenstein polynomial) | 68 | A monic polynomial with coefficients in A whose non-leading coefficients lie in p and constant term not in p^2. | `Polynomial.IsEisensteinAt` | in Mathlib |
| Prose definition D064 (numerical norm of an ideal) | 71 | Na is the index of a in the ring of integers. | `Ideal.absNorm`, `Ideal.absNorm_apply` | in Mathlib |
| Prose definition D065 (Minkowski constant) | 72 | C_K = (n!/n^n)(4/pi)^s. | `NumberField.mixedEmbedding.minkowskiBound` | in Mathlib |
| Prose definition D066 (unramified extension) | 74 | L/K is unramified if no prime of O_K ramifies in O_L. | `Algebra.IsUnramifiedIn` | in Mathlib |
| Prose definition D067 (full lattice) | 75 | A lattice generated by n independent vectors in an n-dimensional space. | `IsZLattice` | in Mathlib |
| Prose definition D068 (discrete subgroup) | 75 | A subgroup that is discrete in the induced topology. | `DiscreteTopology` | in Mathlib |
| Prose definition D070 (fundamental parallelopiped) | 77 | The set of f0 + sum a_i e_i with 0 <= a_i < 1. | `ZSpan.fundamentalDomain` | in Mathlib |
| Prose definition D071 (convex and symmetric set) | 78 | Convex: contains line segments; symmetric: closed under negation. | `Convex` | in Mathlib |
| Prose definition D074 (integral binary quadratic form) | 83 | Q = aX^2 + bXY + cY^2, integral if a, b, c are integers. | `QuadFormsKB.BinQF`, `QuadFormsKB.BinQF.disc`, `QuadFormsKB.Binary.SLEquiv` | formalized (a definition) |
| Prose definition D075 (discriminant and nondegeneracy of a binary form) | 83 | d_Q = b^2 - 4ac; nondegenerate when nonzero. | `QuadFormsKB.BinQF`, `QuadFormsKB.BinQF.disc`, `QuadFormsKB.Binary.SLEquiv` | formalized (a definition) |
| Prose definition D076 (equivalence of binary forms) | 83 | Q and Q' are equivalent if Q' = Q composed with a matrix of SL2(Z). | `QuadFormsKB.BinQF`, `QuadFormsKB.BinQF.disc`, `QuadFormsKB.Binary.SLEquiv` | formalized (a definition) |
| Prose definition D077 (norm form of an ideal basis) | 84 | The form q_K(X,Y) = N(a1 X + a2 Y)/N(a) attached to a basis of a fractional ideal. | `MilneANT.idealNormForm` | formalized (a definition) |
| Prose definition D078 (rank of a finitely generated abelian group) | 87 | The free rank t of A modulo torsion. | `Module.finrank`, `Group.rank` | in Mathlib |
| Prose definition D079 (r and s) | 87 | r real embeddings, 2s nonreal complex embeddings. | `NumberField.InfinitePlace.nrRealPlaces`, `NumberField.InfinitePlace.nrComplexPlaces` | in Mathlib |
| Prose definition D080 (fundamental system of units) | 87 | Units forming a basis of U_K modulo torsion. | `NumberField.Units.fundSystem` | in Mathlib |
| Prose definition D081 (ring of S-integers) | 92 | The elements of K integral outside the finite set S of primes. | `Set.integer` | in Mathlib |
| Prose definition D082 (group of S-units) | 92 | The units of the ring of S-integers. | `Set.unit`, `Set.unitEquivUnitsInteger` | in Mathlib |
| Prose definition D083 (continued fraction) | 93 | The expression a0 + 1/(a1 + 1/(a2 + ...)). | `GenContFract` | in Mathlib |
| Prose definition D084 (quotients and convergents) | 93 | The a_i are the quotients; [a0;...;an] is the nth convergent. | `GenContFract` | in Mathlib |
| Prose definition D086 (regulator) | 96 | The absolute value of the determinant of a maximal minor of the logarithmic embedding of a fundamental system of units. | `NumberField.Units.regulator` | in Mathlib |
| Prose definition D088 (primitive root of unity) | 97 | zeta with zeta^n = 1 and zeta^d != 1 for d < n. | `IsPrimitiveRoot` | in Mathlib |
| Prose definition D089 (cyclotomic polynomial) | 98 | The product of X - zeta^m over m coprime to n. | `Polynomial.cyclotomic` | in Mathlib |
| Prose definition D090 (regular prime) | 103 | p is regular if it does not divide the class number of Q(zeta_p). | `MilneANT.IsRegularPrime` | formalized (a definition) |
| Prose definition D091 (Bernoulli numbers) | 103 | t/(e^t-1) = sum B_n t^n / n!. | `bernoulli` | in Mathlib |
| Prose definition D094 (discrete absolute value) | 109 | The value group is a discrete subgroup of R>0. | `MilneANT.IsDiscreteAbv` | formalized (a definition) |
| Prose definition D101 (place of a number field) | 113 | A prime or place of a number field K is an equivalence class of absolute values on K. | `MilneANT.MilnePlace` | formalized (a definition) |
| Prose definition D102 (finite prime of a number field) | 114 | A finite prime is the place defined by a nonzero prime ideal p of the ring of integers; p_v denotes the ideal. | `NumberField.FinitePlace` | in Mathlib |
| Prose definition D104 (infinite prime of a number field) | 114 | An infinite prime is the place defined by a real or nonreal (conjugate pair of) embedding(s) of K into the complex numbers. | `NumberField.InfinitePlace` | in Mathlib |
| Prose definition D106 (place lying over a place) | 114 | For L containing K, a place w of L divides (lies over) a place v of K if the restriction of an absolute value of w to K is equivalent to one of v. | `MilneANT.MilnePlace.LiesOver` | formalized (a definition) |
| Prose definition D109 (complete valued field) | 116 | A valued field is complete if every Cauchy sequence has a limit in the field. | `CompleteSpace` | in Mathlib |
| Prose definition D112 (ring of p-adic integers) | 117 | Z_p is the ring of integers of Q_p, the completion of Q at the p-adic absolute value. | `PadicInt` | in Mathlib |
| Prose definition D113 (local uniformizing parameter) | 118 | For a discrete nonarchimedean absolute value, a local uniformizing parameter is an element whose absolute value is the largest below 1; it generates the maximal ideal. | `Valuation.IsUniformizer` | in Mathlib |
| Prose definition D115 (strictly coprime polynomials) | 123 | A pair (g,h) in A[X] is strictly coprime if (g,h) = A[X]. | `IsCoprime` | in Mathlib |
| Prose definition D117 (totally ramified extension of local fields) | 126 | A finite extension L/K of complete discretely valued fields is totally ramified if e = n = [L:K], i.e. pB = P^n. | `MilneANT.IsTotallyRamifiedMilne` | formalized (a definition) |
| Prose definition D118 (unramified extension of local fields) | 126 | A finite extension L/K of complete discretely valued fields is unramified if f = n, the residue degree equals the degree. | `MilneANT.IsUnramifiedMilne` | formalized (a definition) |
| Prose definition D120 (Newton polygon) | 127 | The Newton polygon of a monic polynomial over a complete discretely valued field is the lower convex hull of the points (i, ord a_i). | `MilneANT.newtonPolygon` | formalized (a definition) |
| Prose definition D123 (Eisenstein polynomial over a local field) | 131 | A polynomial is Eisenstein over a complete discretely valued field if the leading coefficient is a unit, the other coefficients lie in the maximal ideal and the constant term is a uniformizer times a unit. | `Polynomial.IsEisensteinAt` | in Mathlib |
| Prose definition D125 (inertia group of a local Galois extension) | 132 | The inertia group is G_0, the elements acting trivially on the residue field. | `MilneANT.ramificationGroupMilne` | formalized (a definition) |
| Prose definition D129 (wild and tame ramification) | 133 | L/K is wildly ramified if p = char of the residue field divides e, and tamely ramified otherwise. | `MilneANT.IsWildlyRamifiedMilne`, `MilneANT.IsTamelyRamifiedMilne` | formalized (a definition) |
| Prose definition D134 (normalized absolute value of a place) | 139 | The normalized absolute value is the usual one for R, its square for C, and N(p)^{-ord_p} for a prime ideal p. | `MilneANT.normalizedAbv` | formalized (a definition) |
| Prose definition D136 (decomposition group) | 141 | The decomposition group G_w of a place w is the stabilizer of w in the Galois group. | `MilneANT.decompGroupAbv_finitePlace`, `MilneANT.decompGroupAbv_conj` | proved |
| Prose definition D137 (Frobenius element) | 143 | For a prime P of L unramified over p, the Frobenius element (P, L/K) is the element of G(P) with sigma(a) congruent to a^q modulo P for all a in O_L. | `IsArithFrobAt`, `arithFrobAt` | in Mathlib |
| Prose definition (Spl and Spl', p. 151) | 151 | Spl(L/K): primes splitting completely in L; Spl'(L/K): primes with at least one split factor. | `MilneANT.splitPrimes_subset_splitPrimes'`, `MilneANT.splitPrimes_eq_splitPrimes'` | proved |
