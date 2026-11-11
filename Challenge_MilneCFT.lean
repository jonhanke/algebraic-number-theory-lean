/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangUncond
import NumberFieldKB.MilneCFT.Ch8.Theorem26Uncond
import NumberFieldKB.MilneCFT.LubinTate.LocalKroneckerWeberCFT
import NumberFieldKB.MilneCFT.Ch8.Eisenstein.Reciprocity
import NumberFieldKB.MilneCFT.Ch8.Eisenstein.Furtwangler
import NumberFieldKB.MilneCFT.Ch8.GaussCubicUncond
import NumberFieldKB.MilneCFT.Ch5LSeriesExtends

/-!
# Headline statements of NumberFieldKB 0.2.1: Milne, Class Field Theory

The main results of the library, one theorem each, with every proof a deliberate `sorry`: to check what is claimed,
read this file. `Solution.lean` proves the same statements from the library, and `lake comparator` (configured by
`comparator.json`) checks that each proved statement is exactly the one here and uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied, except where its docstring says otherwise: a named statement in the
conclusion (a `Prop` structure of the library) is unfolded, and where the library defines a continuation by cases the
headline states the existence of a continuation with the stated properties. The statements were not yet reviewed by a
human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library (and of the quadratic-forms library it builds
on); a reader checking a statement should check these too:

* `NumberFieldKB.MilneANT.galPerm`
* `NumberFieldKB.MilneANT.placeOf`
* `NumberFieldKB.MilneANT.MilnePlace`
* `NumberFieldKB.MilneANT.placeAbv`
* `NumberFieldKB.WeilBNT.chiA`
* `NumberFieldKB.WeilBNT.chiInf`
* `NumberFieldKB.WeilBNT.chiFin`
* `NumberFieldKB.WeilBNT.omega`
* `NumberField.IdeleGroup.principalSubgroup`
* `NumberFieldKB.WeilBNT.FF.IsConstantField`
* `NumberFieldKB.WeilBNT.FF.genus`
* `NumberFieldKB.WeilBNT.FF.ClassGroup0`
* `NumberFieldKB.WeilBNT.FF.zetaSeries`
* `NumberFieldKB.WeilBNT.FF.FFHeckeCharacter`
* `NumberFieldKB.WeilBNT.FF.FFHeckeCharacter.conductor`
* `NumberFieldKB.WeilBNT.FF.FFHeckeCharacter.lSeriesF`
* `NumberFieldKB.SchwartzBruhat`
* `NumberFieldKB.SchwartzBruhat.fourier`
* `NumberFieldKB.HeckeCharacter`
* `NumberFieldKB.HeckeCharacter.shift`
* `NumberFieldKB.globalZeta`
* `QuadFormsKB.Tamagawa.Measure.Weil.Adeles`
* `NumberFieldKB.HeckeCharacter.normPow`
* `NumberFieldKB.HeckeL.completedHeckeL`
* `NumberFieldKB.HeckeL.condDisc`
* `NumberFieldKB.HeckeL.gammaInf`
* `NumberFieldKB.HeckeL.heckeL`
* `NumberFieldKB.HeckeL.IsPoleFree`
* `NumberFieldKB.HeckeL.rootNumber`
* `NumberFieldKB.HeckeCharacter.IsUnitary`
* `NumberFieldKB.Pontryagin.IsDualMeasure`
* `NumberFieldKB.WeilBNT.AbstractFourier.IsAdmissible`
* `NumberFieldKB.WeilBNT.AbstractFourier.fourierLCA`
* `NumberFieldKB.Pontryagin.annihilator`
* `NumberFieldKB.ModularCurves.X0`
* `NumberFieldKB.MilneEC.IsGenus`
* `NumberFieldKB.MilneEC.genus`
* `NumberFieldKB.MilneEC.Divisor.ell`
* `NumberFieldKB.MilneEC.V.evalJJN`
* `NumberFieldKB.MilneEC.V.jFun`
* `NumberFieldKB.MilneEC.V.jN`
* `NumberFieldKB.MilneEC.V.IsModularFunction`
* `NumberFieldKB.MilneEC.V.IsMeromorphicOnUpperHalfPlane`
* `NumberFieldKB.MilneEC.V.IsMeromorphicAtImInfty`
* `NumberFieldKB.MilneEC.V.g4`
* `NumberFieldKB.MilneEC.V.g6`
* `NumberFieldKB.MilneEC.V.discr`
* `NumberFieldKB.MilneCFT.Ch4.BrauerGroup`
* `NumberFieldKB.MilneCFT.Ch4.BrauerGroup.mk`
* `NumberFieldKB.MilneCFT.LocalCFT.FiniteAbelianExt`
* `NumberFieldKB.MilneCFT.LocalCFT.ltTower`
* `NumberFieldKB.MilneCFT.LocalCFT.ltField`
* `NumberFieldKB.MilneCFT.LocalCFT.unramifiedClosure`
* `NumberFieldKB.MilneCFT.Ch8.cubicAffineCount`
* `NumberFieldKB.MilneCFT.Modulus`
* `NumberFieldKB.MilneCFT.RayClassGroup`
* `NumberFieldKB.MilneCFT.weberLSeries`
* `NumberFieldKB.MilneCFT.idealRayClass`
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
  sorry

open NumberField in
open NumberFieldKB.MilneCFT in
/-- **Central division algebras over a number field** (Milne, *Class Field Theory*, Chapter VIII, Theorem 2.6;
Albert, Brauer–Hasse–Noether): for every finite-dimensional central division algebra $D$ over a number field $K$, the
order of the class of $D$ in the Brauer group of $K$ is $\sqrt{[D:K]}$, and $D$ is a cyclic algebra: it contains a
cyclic extension $L$ of $K$ with $[L:K]^2 = [D:K]$, and is generated by $L$ and one element $\beta$ with
$\beta\alpha\beta^{-1} = \sigma(\alpha)$ for $\alpha \in L$ and $\beta^{[L:K]} = \gamma \in K^\times$, $\sigma$ a
generator of $\mathrm{Gal}(L/K)$. (The library's named statement `Theorem2_6`, unfolded; the Brauer group is the
library's `Ch4.BrauerGroup` of central simple algebras.) -/
theorem centralDivisionAlgebra_cyclic {K : Type} [Field K] [NumberField K] (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] :
    (orderOf (Ch4.BrauerGroup.mk (⟨.of K D⟩ : CSA.{0, 0} K))) ^ 2 = Module.finrank K D ∧
    ∃ (L : Subalgebra K D) (_ : IsField L), IsCyclic (L ≃ₐ[K] L) ∧ Nat.card (L ≃ₐ[K] L) = Module.finrank K L ∧
      (Module.finrank K L) ^ 2 = Module.finrank K D ∧
      ∃ (σ : L ≃ₐ[K] L) (β : D) (γ : K), Subgroup.zpowers σ = ⊤ ∧ γ ≠ 0 ∧
        β ^ Module.finrank K L = algebraMap K D γ ∧ (∀ α : L, β * (α : D) = (σ α : D) * β) ∧
        Algebra.adjoin K ((L : Set D) ∪ {β}) = ⊤ :=
  sorry

open scoped ValuativeRel in
open NumberFieldKB.MilneCFT.LocalCFT in
/-- **The local Kronecker–Weber theorem** (Milne, *Class Field Theory*, Chapter I, Theorem 4.8): let $K$ be a
nonarchimedean local field (of any characteristic), $\Omega$ a separable closure and $\pi$ a prime element. Every
finite abelian extension $L$ of $K$ in $\Omega$ lies in $K_\pi K^{\mathrm{un}}$, the compositum of the Lubin–Tate
tower $K_\pi = \bigcup_n K(\Lambda_n)$ of $\pi$ (the fields generated by the $\pi^n$-torsion of a Lubin–Tate formal
group, the library's `ltTower`) and the maximal unramified extension. (The library's named statement
`LocalKroneckerWeber`, unfolded; its proof uses the Lubin–Tate extension theorem, Milne I.3.6, proved from a port of
Yamaguchi's library, and the local reciprocity law from a port of Tau Ceti.) -/
theorem localKroneckerWeber_lubinTate (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] {π : 𝒪[K]} (hπ : Irreducible π)
    (L : FiniteAbelianExt K Ω) :
    L.toField ≤ ltTower Ω π ⊔ unramifiedClosure K Ω :=
  sorry

open NumberField Ideal in
/-- **The Eisenstein reciprocity law** (Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Theorem
14.5.1; used by Milne, *Class Field Theory*, Chapter VIII, §5, for Theorem 5.14): let $p$ be an odd prime,
$K = \mathbb Q(\zeta_p)$, $a \in \mathbb Z$ prime to $p$ and $\alpha \in \mathcal O_K$ a primary non-unit prime to
$a$. Then $(\alpha/a)_p = (a/\alpha)_p$ for the $p$-th power residue symbols at the ideals $(a)$ and $(\alpha)$.
(Proved from the Hilbert reciprocity law for the idelic Artin map; the library's named statement
`EisensteinReciprocity`, unfolded.) -/
theorem eisensteinReciprocity (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (α : 𝓞 K) (a : ℤ) (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α)
    (hu : ¬ IsUnit α) (ha : ¬ (p : ℤ) ∣ a) (hcop : IsCoprime α (a : 𝓞 K)) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) :=
  sorry

/-- **Furtwängler's theorem** (Milne, *Class Field Theory*, Chapter VIII, Theorem 5.14): let $p$ be an odd prime and
$x, y, z$ relatively prime positive integers with $p \nmid xyz$ and $x^p + y^p = z^p$. Then $q^{p-1} \equiv 1
\pmod{p^2}$ for every prime $q$ dividing $xyz$. (The library's named statement `Theorem5_14`, unfolded; proved from the
Eisenstein reciprocity law.) -/
theorem furtwangler_fermat (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgcd : Nat.gcd (Nat.gcd x y) z = 1) (hpxyz : ¬ p ∣ x * y * z) (hF : x ^ p + y ^ p = z ^ p)
    (q : ℕ) (hq : q.Prime) (hqxyz : q ∣ x * y * z) :
    q ^ (p - 1) ≡ 1 [MOD p ^ 2] :=
  sorry

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
  sorry

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
  sorry

end NumberFieldKB.Headlines
