/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.GlobalZeta.FunctionalEquation
import NumberFieldKB.HeckeL.RootNumber
import NumberFieldKB.HeckeL.DedekindCont

/-!
# Headline statements of NumberFieldKB 0.2.1: Tate's thesis and Hecke L-functions, proved

The declarations of `Challenge.lean`, with the same names and statements, each proved by citing the library theorems
named in its proof. `lake comparator` (configured by `comparator.json`) checks that every theorem here has exactly the
statement of its counterpart in `Challenge.lean` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. Read `Challenge.lean` for the statements, their docstrings and the definitions they use.
-/

noncomputable section

namespace NumberFieldKB.Headlines

/-! ## Tate's thesis -/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set in
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil in
open scoped Classical ENNReal NNReal nonZeroDivisors in
open NumberFieldKB NumberFieldKB.GlobalZeta in
/-- **Tate's main theorem** (Cassels–Fröhlich, Chapter XV, Main Theorem 4.4.1): for a number field $F$, a factorizable
Schwartz–Bruhat function $\Phi$ on $\mathbb A_F$ and a Hecke character $\chi$ with $|\chi| = \|\cdot\|^\sigma$, the zeta
integral $Z(\Phi, \chi, s) = \int_{\mathbb A_F^\times} \Phi(x)\chi(x)\|x\|^s\,d^\times x$ (convergent for
$\operatorname{Re} s + \sigma > 1$) extends to a meromorphic function $Z$ on $\mathbb C$ with
$Z(1 - s) = Z(\hat\Phi, \chi^{-1}, s)$ wherever the right side converges. (The library proves this for its continuation
`globalZetaCont`; the headline states the existence of the continuation.) -/
theorem tate_globalZeta_functionalEquation {F : Type} [Field F] [NumberField F] (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) :
    ∃ Z : ℂ → ℂ, Meromorphic Z ∧
      (∀ s : ℂ, 1 < s.re + χ.shift → Z s = globalZeta (Φ : Adeles F → ℂ) χ s) ∧
      ∀ s : ℂ, 1 < s.re - χ.shift → Z (1 - s) = globalZeta Φ.fourier χ⁻¹ s :=
  ⟨NumberFieldKB.GlobalZeta.globalZetaCont Φ χ, NumberFieldKB.GlobalZeta.meromorphic_globalZetaCont Φ χ,
      fun _ hs => NumberFieldKB.GlobalZeta.globalZetaCont_eq Φ χ hs,
      fun _ hs => NumberFieldKB.GlobalZeta.globalZetaCont_one_sub Φ χ hs⟩

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set in
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil in
open scoped Classical ENNReal NNReal nonZeroDivisors in
open NumberFieldKB NumberFieldKB.GlobalZeta in
/-- **Poles and residues** (Cassels–Fröhlich, Chapter XV, Main Theorem 4.4.1): for $\chi = \|\cdot\|^c$ the continuation $Z$ of
$Z(\Phi, \chi, s)$ has residue $\hat\Phi(0)\rho_F$ at $s = 1 - c$ and $-\Phi(0)\rho_F$ at $s = -c$, where $\rho_F$ is the residue of
the Dedekind zeta function at $s = 1$ (Mathlib's `NumberField.dedekindZeta_residue`, given by the class number formula).
(The library proves this for its continuation `globalZetaCont`.) -/
theorem tate_globalZeta_residues {F : Type} [Field F] [NumberField F] (Φ : SchwartzBruhat F) (c : ℂ) :
    ∃ Z : ℂ → ℂ, Meromorphic Z ∧
      (∀ s : ℂ, 1 < s.re + (HeckeCharacter.normPow F c).shift →
        Z s = globalZeta (Φ : Adeles F → ℂ) (HeckeCharacter.normPow F c) s) ∧
      Tendsto (fun s => (s - (1 - c)) * Z s) (𝓝[≠] (1 - c)) (𝓝 (Φ.fourier 0 * dedekindZeta_residue F)) ∧
      Tendsto (fun s => (s + c) * Z s) (𝓝[≠] (-c)) (𝓝 (-((Φ : Adeles F → ℂ) 0 * dedekindZeta_residue F))) :=
  ⟨NumberFieldKB.GlobalZeta.globalZetaCont Φ (HeckeCharacter.normPow F c),
      NumberFieldKB.GlobalZeta.meromorphic_globalZetaCont Φ _,
      fun _ hs => NumberFieldKB.GlobalZeta.globalZetaCont_eq Φ _ hs,
      NumberFieldKB.GlobalZeta.tendsto_globalZetaCont_normPow_residue_one Φ c,
      NumberFieldKB.GlobalZeta.tendsto_globalZetaCont_normPow_residue_zero Φ c⟩

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set in
open Topology in
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil in
open scoped Classical ComplexConjugate in
open NumberFieldKB NumberFieldKB.HeckeL NumberFieldKB.GlobalZeta NumberFieldKB.LocalZeta in
/-- **Hecke $L$-functions** (Cassels–Fröhlich, Chapter XV, §4.5): for every Hecke character $\chi$ of a number field $F$,
the completed $L$-function $\Lambda(s, \chi)$ equals $A(\chi)^{s/2} L_\infty(s, \chi) L(s, \chi)$ for
$\operatorname{Re} s + \sigma > 1$ ($A(\chi) = |d_F| \cdot N\mathfrak f(\chi)$, $L(s, \chi)$ the Euler product over the finite
primes, $L_\infty$ the product of the archimedean Gamma factors), is holomorphic at every $s$ that is not a pole
(every $s$, unless $\chi = \|\cdot\|^c$; then $s \ne -c, 1 - c$), and satisfies
$\Lambda(s, \chi) = W(\chi) \Lambda(1 - s, \chi^{-1})$ with a root number of absolute value $1$ when $\chi$ is unitary. -/
theorem heckeL_functionalEquation {F : Type} [Field F] [NumberField F] (χ : HeckeCharacter F) :
    (∀ s : ℂ, 1 < s.re + χ.shift →
      completedHeckeL χ s = ((condDisc χ : ℝ) : ℂ) ^ (s / 2) * gammaInf χ s * heckeL χ s) ∧
    (∀ s : ℂ, IsPoleFree χ s → DifferentiableAt ℂ (completedHeckeL χ) s) ∧
    (∀ s : ℂ, IsPoleFree χ s → completedHeckeL χ s = rootNumber χ * completedHeckeL χ⁻¹ (1 - s)) ∧
    (χ.IsUnitary → ‖rootNumber χ‖ = 1) :=
  ⟨fun _ hs => NumberFieldKB.HeckeL.completedHeckeL_eq χ hs,
      fun _ hs => NumberFieldKB.HeckeL.differentiableAt_completedHeckeL hs,
      fun _ hs => NumberFieldKB.HeckeL.completedHeckeL_functional_equation χ hs,
      fun hχ => NumberFieldKB.HeckeL.norm_rootNumber hχ⟩

open NumberField Filter Topology in
/-- **The Dedekind zeta function** of a number field $F$ (Mathlib's `NumberField.dedekindZeta`, defined by its Dirichlet
series for $\operatorname{Re} s > 1$) extends to a function holomorphic on $\mathbb C \setminus \{1\}$, with residue at $s = 1$
equal to $2^{r_1}(2\pi)^{r_2} h_F R_F / (w_F \sqrt{|d_F|})$ (Mathlib's `NumberField.dedekindZeta_residue`): the class number
formula, read on the continuation. -/
theorem dedekindZeta_continuation (F : Type) [Field F] [NumberField F] :
    ∃ Z : ℂ → ℂ, (∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ Z s) ∧
      (∀ s : ℂ, 1 < s.re → Z s = dedekindZeta F s) ∧
      Tendsto (fun s => (s - 1) * Z s) (𝓝[≠] 1) (𝓝 (dedekindZeta_residue F : ℂ)) :=
  ⟨NumberFieldKB.HeckeL.dedekindZetaCont F, fun _ hs => NumberFieldKB.HeckeL.differentiableAt_dedekindZetaCont (F := F) hs,
      fun _ hs => NumberFieldKB.HeckeL.dedekindZetaCont_eq (F := F) hs,
      NumberFieldKB.HeckeL.tendsto_sub_one_mul_dedekindZetaCont (F := F)⟩

open NumberField NumberField.InfinitePlace Filter Topology in
/-- **The functional equation of the Dedekind zeta function** (Neukirch, *Algebraic Number Theory*, Chapter VII,
Corollary 5.11): for a number field $F$ with $r_1$ real and $r_2$ complex places, the function
$\Lambda_F(s) = |d_F|^{s/2}\,\Gamma_{\mathbb R}(s)^{r_1}\Gamma_{\mathbb C}(s)^{r_2}\zeta_F(s)$ ($\operatorname{Re} s > 1$) extends to a
function holomorphic on $\mathbb C \setminus \{0, 1\}$ with $\Lambda_F(1 - s) = \Lambda_F(s)$. Only Mathlib definitions occur. -/
theorem completedDedekindZeta_functionalEquation (F : Type) [Field F] [NumberField F] :
    ∃ Λ : ℂ → ℂ, (∀ s : ℂ, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ Λ s) ∧
      (∀ s : ℂ, 1 < s.re → Λ s = (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (s / 2) *
        (Complex.Gammaℝ s ^ nrRealPlaces F * Complex.Gammaℂ s ^ nrComplexPlaces F) * dedekindZeta F s) ∧
      ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s :=
  ⟨NumberFieldKB.HeckeL.completedDedekindZeta F,
      fun _ h0 h1 => NumberFieldKB.HeckeL.differentiableAt_completedDedekindZeta (F := F) h0 h1,
      fun _ hs => NumberFieldKB.HeckeL.completedDedekindZeta_eq (F := F) hs,
      fun _ h0 h1 => NumberFieldKB.HeckeL.completedDedekindZeta_one_sub (F := F) h0 h1⟩

end NumberFieldKB.Headlines
