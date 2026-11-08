# J. Tate, "Fourier analysis in number fields and Hecke's zeta-functions" (Tate's thesis): map to the Lean library

Chapter XV of J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Academic Press, 1967. There is no item-by-item audit of this text yet: the rows are the declarations of the library that cite it (`@[kb "casselsfrohlich1967" ...]`), grouped by the section they cite. The section and theorem numbers in these citations have **not yet been checked** against the book.

Each row is a result of the book, the Lean declaration that formalizes it, and its status. *Proved* means proved in Lean with only the standard axioms, assuming no unproved input (a hypothesis that is a condition of the statement, such as "$K$ is a local field", is not an input); *conditional* names the unproved inputs it still assumes; *in Mathlib* means Mathlib (v4.35.0, on which this library is built) already has the result, and the Lean name is Mathlib's; *not formalized* means the library does not state it. Rows that are not results (examples, history, comments, computations) are omitted and only counted. The statements in the middle column are short descriptions, not quotations; read the book for the exact wording. Items that the library states in a generalized form are mapped to the general statement.

Rows: 80. proved: 57; formalized (a definition): 23.

## §2.2. The local additive theory

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §2.2 | — | the class 𝔅 at a 𝔭-adic place: locally constant, compact support | `LocalZeta.IsSchwartzBruhatLC` | formalized (a definition) |
| §2.2 | — | f ∈ 𝔅 ⇒ f̂ ∈ 𝔅 at a 𝔭-adic place | `LocalZeta.IsSchwartzBruhatLC.fourierV` | proved |

## §2.3. The local multiplicative theory

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §2.3 | — | quasi-characters of R^×: \|x\|^s or sgn(x)\|x\|^s | `HeckeCharacter.realExponent` | formalized (a definition) |
| §2.3 | — | quasi-characters of C^×: \|z\|^s (z/\|z\|)^n | `HeckeCharacter.complexExponent` | formalized (a definition) |
| §2.3 | — | unramified quasi-characters | `HeckeCharacter.IsUnramifiedAt` | formalized (a definition) |
| §2.3 | — | the conductor p^ν of a ramified quasi-character | `HeckeCharacter.conductorExponent` | formalized (a definition) |
| §2.3 | — | the local zeta function ζ(f, c) | `LocalZeta.zetaIntegral` | formalized (a definition) |
| §2.3 | — | d^×z = 2 dx dy/\|z\|² at a complex place | `LocalZeta.tateHaarC` | formalized (a definition) |
| §2.3 | — | d^×α = (N𝔭/(N𝔭 − 1)) dα/\|α\| | `LocalZeta.tateHaarV` | formalized (a definition) |
| §2.3 | — | d^×x = dx/\|x\| at a real place | `LocalZeta.tateHaarR` | formalized (a definition) |
| §2.3 | — | d*a = N𝔭/(N𝔭 - 1) · da/\|a\| | `Ideles.inv_lamV_eq` | proved |
| §2.3, Lemma 2.3.1 / §2.4 | — | ζ(f, c) converges for σ > 0 | `LocalZeta.integrable_zetaIntegrand` | proved |

## §2.4. The local zeta functions and their functional equation

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §2.4 | — | ζ(f, c) converges for σ > 0 | `LocalZeta.integrable_zetaIntegrand_schwartz` | proved |
| §2.4 | — | ρ(c)ρ(ĉ) = c(−1) | `HeckeL.gammaFactorV_mul_inv` | proved |
| §2.4 | — | ρ(c̄) = c(−1) conj ρ(c) | `HeckeL.gammaFactorV_conj` | proved |
| §2.4 | — | \|ρ(c)\| = 1 for unitary c on the critical line | `HeckeL.norm_gammaFactorV` | proved |
| §2.4, Lemma 2.4.1 | — | ζ(f, c)ζ(ĝ, ĉ) = ζ(f̂, ĉ)ζ(g, c) | `LocalZeta.zetaIntegral_mul_zetaIntegral` | proved |
| §2.4, Thm. 2.4.1 | — | the local functional equation | `LocalZeta.zetaIntegral_fourierC_comm` | proved |
| §2.4, Thm. 2.4.1 | — | ζ(f, c) is holomorphic where it converges | `LocalZeta.differentiableOn_zetaIntegral` | proved |
| §2.4, Thm. 2.4.1 | — | the local functional equation | `LocalZeta.zetaIntegral_fourierV_comm` | proved |
| §2.4, Thm. 2.4.1 | — | the factor ρ(c) | `LocalZeta.gammaFactorV` | formalized (a definition) |
| §2.4, Thm. 2.4.1 | — | ζ(f̂, ĉ) = ρ(c) ζ(f, c) | `LocalZeta.zetaIntegral_fourierV_eq_gammaFactorV` | proved |
| §2.4, Thm. 2.4.1 | — | the local functional equation | `LocalZeta.zetaIntegral_fourierR_comm` | proved |
| §2.4, Thm. 2.4.1 and Lemma 2.4.1 | — | Tate's local functional equation (symmetric form, Cassels–Fröhlich Ch. | `LocalZeta.zetaIntegral_mul_fourier_comm` | proved |

## §2.5. Computation of the factor ρ(c)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §2.5 | — | ζ(f, ‖·‖^s) = (2π)^{1−s}Γ(s) for f = e^{−2π\|z\|²} | `LocalZeta.zetaIntegral_gaussian_complex` | proved |
| §2.5 | — | ρ(‖·‖^s) at a complex place | `LocalZeta.zetaIntegral_fourierC_one` | proved |
| §2.5 | — | ζ(f, c) = (N𝔡)^{−1/2}(1 − c(π))^{−1} for unramified c | `LocalZeta.zetaIntegral_tateHaarV_charO` | proved |
| §2.5 | — | ζ(f, \|·\|^s) = π^{−s/2}Γ(s/2) for f = e^{−πx²} | `LocalZeta.zetaIntegral_gaussian_real` | proved |
| §2.5 | — | f = ξe^{−πξ²} for c = sgn·\|·\|^s | `LocalZeta.zetaIntegral_mul_gaussian_sign` | proved |
| §2.5 | — | ρ(\|·\|^s) = Γ_ℝ(1 − s)/Γ_ℝ(s) at a real place | `LocalZeta.zetaIntegral_fourierR_one` | proved |
| §2.5 | — | the test functions at a complex place | `HeckeL.fourierC_fCk` | proved |
| §2.5 | — | the archimedean ζ-functions | `HeckeL.archZeta_archTest` | proved |
| §2.5 | — | the ramified local ζ-function, a Gauss sum | `HeckeL.zetaIntegral_fourierV_ram` | proved |
| §2.5 | — | ρ(c) at a real place, c = \|·\|^s or sgn·\|·\|^s | `HeckeL.zetaIntegral_fourierR_infType` | proved |
| §2.5 | — | ρ(c) at a complex place, c(z) = \|z\|^t (z/\|z\|)^k | `HeckeL.zetaIntegral_fourierC_infType` | proved |
| §2.5 | — | ρ(c) for ramified c, a Gauss sum | `HeckeL.gammaFactorV_ram` | proved |
| §2.5 | — | ρ(c) for unramified c at a finite place | `HeckeL.zetaIntegral_fourierV_unram` | proved |
| §2.5 | — | ρ(c) for unramified c at a finite place | `HeckeL.gammaFactorV_unram` | proved |
| §2.5 and §3.3 | — | the unramified local factor | `HeckeCharacter.zetaIntegral_finiteComponent_charO` | proved |
| §2.5 and §4.4 | — | the archimedean factors of ζ_F | `HeckeL.archZeta_gaussInf_one` | proved |

## §3.1. Characters of the idele class group

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §3.1 | — | quasi-characters of J/k^× | `HeckeCharacter` | formalized (a definition) |
| §3.1 | — | the quasi-characters \|·\|^s | `HeckeCharacter.normPow` | formalized (a definition) |
| §3.1 | — | \|c\| = ‖·‖^σ, σ real | `HeckeCharacter.norm_apply_eq_rpow_shift` | proved |
| §3.1 | — | c = c₀\|·\|^σ, c₀ a character | `HeckeCharacter.unitaryPart_mul_normPow_shift` | proved |
| §3.1 | — | c = c₀\|·\|^σ, c₀ a character | `HeckeCharacter.existsUnique_isUnitary_mul_normPow` | proved |

## §3.2. Restricted products, the adeles and their characters

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §3.2 | — | c_p, the restriction of c to k_p^× | `HeckeCharacter.finiteComponent` | formalized (a definition) |
| §3.2 | — | c_p at the archimedean primes | `HeckeCharacter.infiniteComponent` | formalized (a definition) |
| §3.2 | — | c_p unramified for almost all p | `HeckeCharacter.eventually_isUnramifiedAt` | proved |
| §3.2 | — | the conductor of a quasi-character of C_k | `HeckeCharacter.conductor` | formalized (a definition) |
| §3.2 | — | the class 𝔅 of functions on the adeles; f = ∏ f_p | `SchwartzBruhat` | formalized (a definition) |
| §3.2 | — | f̂ = ∏ f̂_p for f = ∏ f_p | `SchwartzBruhat.fourier` | formalized (a definition) |

## §3.3. The ideles and their measure

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §3.3 | — | the idele group as the units of the adele ring | `Ideles.ideleGroupEquiv` | formalized (a definition) |
| §3.3 | — | d*a = ∏ d*a_p, vol(𝔬_p^×) = (N𝔡_p)^{-1/2} | `Ideles.ideleHaar_box_OHatUnits` | proved |
| §3.3 | — | the idele absolute value \|a\| = ∏_p \|a_p\|_p | `Ideles.norm_eq_ideleNorm` | proved |

## §4.2. The Riemann–Roch theorem

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §4.2, Thm. 4.2.1 | — | the Riemann–Roch theorem | `SchwartzBruhat.theta_eq_poisson` | proved |

## §4.3. The idele class group

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §4.3 | — | J⁰/k^× is compact | `Ideles.IdeleClassGroup.isCompact_normOne` | proved |

## §4.4. The main theorem and the zeta functions

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Main Theorem 4.4.1 | — | analytic continuation of ζ(f, c) | `GlobalZeta.globalZetaCont` | formalized (a definition) |
| Main Theorem 4.4.1 | — | The continuation agrees with the zeta integral where the integral converges: | `GlobalZeta.globalZetaCont_eq` | proved |
| Main Theorem 4.4.1 | — | ζ(f, c) = ζ(f̂, ĉ) | `GlobalZeta.globalZetaCont_one_sub` | proved |
| Main Theorem 4.4.1 | — | no poles unless c = \|·\|^s | `GlobalZeta.differentiable_globalZetaCont` | proved |
| Main Theorem 4.4.1 | — | residue κ f̂(0) at s = 1 - c | `GlobalZeta.tendsto_globalZetaCont_normPow_residue_one` | proved |
| Main Theorem 4.4.1 | — | residue −κ f(0) at s = −c | `GlobalZeta.tendsto_globalZetaCont_normPow_residue_zero` | proved |
| Main Theorem 4.4.1 | — | Meromorphy: | `GlobalZeta.meromorphic_globalZetaCont` | proved |
| §4.4 | — | ζ_∞(f_∞, c_∞) = ∏_{p\|∞} ζ_p(f_p, c_p) | `HeckeL.archZeta_eq_prod` | proved |
| §4.4 | — | the L-function Π_p (1 − c(p))^{-1} | `HeckeL.localL` | formalized (a definition) |
| §4.4 | — | Hecke's L-function L(s, χ) | `HeckeL.heckeL` | formalized (a definition) |
| §4.4 | — | The Euler product converges (unconditionally) for $\operatorname{Re}s+\sigma>1$. | `HeckeL.hasProd_heckeL` | proved |
| §4.4 | — | ζ(f, c) = ζ_∞ · Π_p ζ_p, unramified factors L_p | `HeckeL.globalZeta_stdPhi` | proved |
| §4.4 | — | residue of ζ_k at s = 1, the class number formula | `HeckeL.tendsto_sub_one_mul_dedekindZetaCont` | proved |
| §4.4 | — | ζ(f, c) = ∫ f(a)c(a) d×a | `globalZeta` | formalized (a definition) |
| §4.4 | — | ζ(f, c) converges for σ > 1 | `GlobalZeta.integrable_globalZetaIntegrand` | proved |
| §4.4 | — | ζ(f, c) as an integral over t of the theta integral | `GlobalZeta.globalZeta_eq_mellin` | proved |
| §4.4 | — | ζ(f, c) = ∏_p ζ_p(f_p, c_p) for Re > 1 | `GlobalZeta.hasProd_finZeta` | proved |
| §4.4 | — | ζ(f, c) = ∏_p ζ_p(f_p, c_p) | `GlobalZeta.globalZeta_eq_archZeta_mul_tprod` | proved |
| §4.4 | — | the theta integral and Riemann–Roch | `GlobalZeta.thetaInt_one_div` | proved |

## §4.5. Hecke's L-functions

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §4.5 | — | L(s, χ) entire for χ ≠ \|·\|^{iτ} | `HeckeL.differentiable_completedHeckeL` | proved |
| §4.5 | — | $L(s,\chi)$ continues to an entire function unless $\chi = \|\cdot\|^c$. | `HeckeL.differentiable_heckeLCont` | proved |
| §4.5 | — | the constant of the functional equation | `HeckeL.rootNumber` | formalized (a definition) |
| §4.5 | — | Λ(s, χ) = W(χ) Λ(1 − s, χ̄) | `HeckeL.completedHeckeL_functional_equation` | proved |
| §4.5 | — | \|W(χ)\| = 1 | `HeckeL.norm_rootNumber` | proved |
