/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.ModularCurves.EllipticCount
import NumberFieldKB.ModularCurves.EllipticCountClosed
import NumberFieldKB.ModularCurves.GenusX0
import NumberFieldKB.ModularCurves.Rationality
import NumberFieldKB.ModularCurves.Theorem23
import NumberFieldKB.ModularCurves.Cor34

/-!
# Headline statements of NumberFieldKB 0.2.1: The modular curves X_0(N), proved

The declarations of `Challenge.lean`, with the same names and statements, each proved by citing the library theorems
named in its proof. `lake comparator` (configured by `comparator.json`) checks that every theorem here has exactly the
statement of its counterpart in `Challenge.lean` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. Read `Challenge.lean` for the statements, their docstrings and the definitions they use.
-/

noncomputable section

namespace NumberFieldKB.Headlines

/-! ## The modular curves X₀(N) -/

open NumberFieldKB.MilneEC NumberFieldKB.ModularCurves in
/-- **The genus of $X_0(N)$** (Milne, *Elliptic Curves*, Chapter V, §2): for $N \ge 1$, the function field
$\mathbb Q(X_0(N)) = \mathbb Q(j, j_N)$ has a genus $g$ in the sense of Riemann's theorem ($\ell(D) \ge \deg D + 1 - g$ for
every divisor $D$, with equality when $\deg D > 2g - 2$), and
$12 g = 12 + \mu - 3\nu_2 - 4\nu_3 - 6\nu_\infty$, where $\mu = [\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N)]$,
$\nu_2 = \prod_{p \mid N}(1 + \chi_4(p))$ (or $0$ if $4 \mid N$), $\nu_3 = \prod_{p \mid N}(1 + (p/3))$ (or $0$ if $9 \mid N$) and
$\nu_\infty = \sum_{d \mid N} \varphi(\gcd(d, N/d))$. (The library states the formula with its counts `nu2`, `nu3` of fixed
cosets; they are replaced here by their closed forms, proved in the library.) -/
theorem genus_X0 (N : ℕ) [NeZero N] :
    IsGenus ℚ (X0 N) (genus ℚ (X0 N)) ∧
    12 * genus ℚ (X0 N) = 12 + (CongruenceSubgroup.Gamma0 N).index -
      3 * (if 4 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + ZMod.χ₄ p)) -
      4 * (if 9 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + legendreSym 3 p)) -
      6 * ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d)) :=
  by
    refine ⟨NumberFieldKB.ModularCurves.isGenus_X0 N, ?_⟩
    rw [← NumberFieldKB.ModularCurves.nu2_eq_prod N, ← NumberFieldKB.ModularCurves.nu3_eq_prod N]
    exact NumberFieldKB.ModularCurves.genus_formula_X0 N

open UpperHalfPlane hiding I in
open Polynomial in
open NumberFieldKB.MilneEC.V in
/-- **The modular polynomial** (Milne, *Elliptic Curves*, Chapter V, Proposition 2.4): for $N \ge 1$ there is a monic
$F_N \in \mathbb Q[X][Y]$ of degree $[\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N)]$ in $Y$ with $F_N(j(z), j(Nz)) = 0$ for every $z$ in
the upper half plane, which divides every $G \in \mathbb C[X][Y]$ with $G(j(z), j(Nz)) = 0$ for all $z$ (so it is the
minimal polynomial of $j_N$ over $\mathbb C(j)$): the curve $X_0(N)$ is defined over $\mathbb Q$. (The library's statement is
the field of the structure `Prop2_4`, unfolded here.) -/
theorem modularPolynomial_rational {N : ℕ} (hN : 1 ≤ N) :
    ∃ F : Polynomial (Polynomial ℚ), F.Monic ∧
      F.natDegree = (CongruenceSubgroup.Gamma0 N).index ∧
      (∀ z, evalJJN N (F.map (Polynomial.mapRingHom (algebraMap ℚ ℂ))) z = 0) ∧
      ∀ G : Polynomial (Polynomial ℂ), (∀ z, evalJJN N G z = 0) →
        F.map (Polynomial.mapRingHom (algebraMap ℚ ℂ)) ∣ G :=
  (NumberFieldKB.ModularCurves.prop2_4 hN).exists_poly

open UpperHalfPlane hiding I in
open scoped UpperHalfPlane in
open Filter Polynomial in
open NumberFieldKB.MilneEC.V in
/-- **The function field of $X_0(N)$** (Milne, *Elliptic Curves*, Chapter V, Theorem 2.3): for $N \ge 1$, every modular
function $f$ for $\Gamma_0(N)$ (meromorphic on the upper half plane $\mathbb H$, invariant under $\Gamma_0(N)$, and
meromorphic at every cusp) agrees, off a discrete subset of $\mathbb H$, with $P(j, j_N)/Q(j, j_N)$ for polynomials
$P, Q \in \mathbb C[X][Y]$ with $Q(j, j_N)$ not identically zero, where $j_N(z) = j(Nz)$: the field of modular
functions for $\Gamma_0(N)$ is $\mathbb C(j, j_N)$. (The library's statement is the field of the structure `Thm2_3`,
unfolded here; `codiscrete ℍ` is Mathlib's filter of complements of closed discrete sets.) -/
theorem modularFunctions_Gamma0 (N : ℕ) (hN : 1 ≤ N) (f : ℍ → ℂ) (hf : IsModularFunction (CongruenceSubgroup.Gamma0 N) f) :
    ∃ P Q : Polynomial (Polynomial ℂ), (∃ z, evalJJN N Q z ≠ 0) ∧
      f =ᶠ[codiscrete ℍ] fun z ↦ evalJJN N P z / evalJJN N Q z :=
  NumberFieldKB.ModularCurves.thm2_3.rational N hN f hf

open NumberFieldKB.MilneEC NumberFieldKB.ModularCurves in
/-- **Cusp forms of weight 2 and the genus** (Milne, *Elliptic Curves*, Chapter V, Corollary 3.4): for $N \ge 1$, the
complex dimension of the space $S_2(\Gamma_0(N))$ of cusp forms of weight 2 for $\Gamma_0(N)$ (Mathlib's `CuspForm`)
equals the genus of $X_0(N)$, the genus of the function field $\mathbb Q(X_0(N))$ of the headline `genus_X0` (so
$\dim S_2(\Gamma_0(N)) = 1 + \mu/12 - \nu_2/4 - \nu_3/3 - \nu_\infty/2$). -/
theorem cuspForms_weightTwo_finrank (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2) : ℤ) =
      genus ℚ (X0 N) :=
  NumberFieldKB.ModularCurves.cor_3_4 N

end NumberFieldKB.Headlines
