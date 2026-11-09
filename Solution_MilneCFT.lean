/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangUncond
import NumberFieldKB.MilneCFT.Ch8.GaussCubicUncond
import NumberFieldKB.MilneCFT.Ch5LSeriesExtends

/-!
# Headline statements of NumberFieldKB 0.2.0: Milne, Class Field Theory, proved

The declarations of `Challenge.lean`, with the same names and statements, each proved by citing the library theorems
named in its proof. `lake comparator` (configured by `comparator.json`) checks that every theorem here has exactly the
statement of its counterpart in `Challenge.lean` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. Read `Challenge.lean` for the statements, their docstrings and the definitions they use.
-/

noncomputable section

namespace NumberFieldKB.Headlines

/-! ## Milne, *Class Field Theory* -/

open NumberField IsDedekindDomain in
/-- **The Grunwald–Wang theorem** (Milne, *Class Field Theory*, Chapter VIII, Theorem 2.4): let $K$ be a number field,
$S$ a finite set of finite places and $T$ a finite set of infinite places, and for each $v \in S \cup T$ let
$\chi_v$ be a continuous character of finite order of $K_v^\times$; let $n$ be the least common multiple of their
orders. There is a continuous character $\psi$ of the idele class group $C_K$ whose restriction to $K_v^\times$ is
$\chi_v$ for all $v \in S \cup T$, and $\psi$ can be chosen of order exactly $n$ unless $2^t \mid n$ for some $t$
with $K(\zeta_{2^t})/K$ not cyclic (Wang's special case). (The library's named statement `Theorem2_4`, unfolded.) -/
theorem grunwaldWang {K : Type} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ)
    (hχ : ∀ v ∈ S, Continuous (χ v) ∧ IsOfFinOrder (χ v)) (hχ' : ∀ w ∈ T, Continuous (χ' w) ∧ IsOfFinOrder (χ' w))
    (n : ℕ) (hn : ∀ v ∈ S, orderOf (χ v) ∣ n) (hn' : ∀ w ∈ T, orderOf (χ' w) ∣ n)
    (hlcm : ∀ m : ℕ, (∀ v ∈ S, orderOf (χ v) ∣ m) → (∀ w ∈ T, orderOf (χ' w) ∣ m) → n ∣ m) :
    ∃ ψ : IdeleClassGroup (𝓞 K) K →* ℂˣ, Continuous ψ ∧
      (∀ v ∈ S, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)) = χ v) ∧
      (∀ w ∈ T, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofCompletion (𝓞 K) K w)) = χ' w) ∧
      ((∀ t : ℕ, 2 ^ t ∣ n →
          IsCyclic (CyclotomicField (2 ^ t) K ≃ₐ[K] CyclotomicField (2 ^ t) K)) → orderOf ψ = n) :=
  (NumberFieldKB.MilneCFT.Ch8.GW.theorem2_4 (K := K)).exists_char S T χ χ' hχ hχ' n hn hn' hlcm

open NumberFieldKB.MilneCFT.Ch8 in
/-- **A theorem of Gauss** (Milne, *Class Field Theory*, Chapter VIII, §10; Silverman–Tate IV.2): let $N_p$ be the
number of points of the projective curve $X^3 + Y^3 + Z^3 = 0$ over $\mathbb F_p$, so that the number of nonzero
solutions in $\mathbb F_p^3$ (`cubicAffineCount p`) is $(p-1)N_p$. If $p \not\equiv 1 \pmod 3$ then $N_p = p + 1$;
if $p \equiv 1 \pmod 3$ then $N_p = p + 1 + A$, where $A$ is the unique integer $\equiv 1 \pmod 3$ with
$4p = A^2 + 27B^2$ for some integer $B$. (The library's named statement `GaussCubicCount`, unfolded.) -/
theorem gauss_cubicCurve_count (p : ℕ) [Fact p.Prime] :
    (p % 3 ≠ 1 → cubicAffineCount p = (p - 1) * (p + 1)) ∧
    (p % 3 = 1 → ∃ A B : ℤ, A % 3 = 1 ∧ 4 * p = A ^ 2 + 27 * B ^ 2 ∧
      (cubicAffineCount p : ℤ) = (p - 1) * (p + 1 + A) ∧
      ∀ A' B' : ℤ, A' % 3 = 1 → 4 * p = A' ^ 2 + 27 * B' ^ 2 → A' = A) :=
  ⟨NumberFieldKB.MilneCFT.Ch8.gaussCubicCount.not_one p, NumberFieldKB.MilneCFT.Ch8.gaussCubicCount.one p⟩

open NumberField in
open NumberFieldKB.MilneCFT in
/-- **Weber $L$-series** (Milne, *Class Field Theory*, Chapter V, Theorem 2.4(b), in the corrected form: the book says
"converges for $\mathrm{Re}(s) > 0$", which fails in general for $[K:\mathbb Q] \ge 2$; the author of this library
confirmed "extends" as the intended reading): for a modulus $\mathfrak m$ of a number field $K$ and a nontrivial
character $\chi$ of the ray class group $C_\mathfrak m$, the series
$L(s,\chi) = \sum_{(\mathfrak a,\mathfrak m_0) = 1}\chi(\mathfrak a)N\mathfrak a^{-s}$ (`weberLSeries`) extends to a
holomorphic function on $\mathrm{Re}(s) > 0$ whose value at $s = 1$ is nonzero. (The library's named statement
`Theorem2_4bExtends`, unfolded; proved from the Hecke $L$-function of the attached Hecke character of finite order.) -/
theorem weberL_continuation {K : Type} [Field K] [NumberField K] (m : Modulus K) (χ : RayClassGroup m →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → L s = weberLSeries m χ s) ∧ L 1 ≠ 0 :=
  (NumberFieldKB.MilneCFT.theorem_2_4b_extends K).extends_ m χ hχ

end NumberFieldKB.Headlines
