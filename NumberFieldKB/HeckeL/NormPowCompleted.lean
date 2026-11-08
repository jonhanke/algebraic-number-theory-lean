import NumberFieldKB.HeckeL.DedekindCont
import NumberFieldKB.HeckeL.RootNumber
import NumberFieldKB.HeckeCharacter.Examples

/-!
# The completed L-function of the norm character is the shifted completed Dedekind zeta function

Let $F$ be a number field and $\|\cdot\|^c$ the Hecke character `HeckeCharacter.normPow F c`. In Tate's thesis (and
already in Hecke's work) the $L$-function of $\|\cdot\|^c$ is the Dedekind zeta function shifted by $c$, and the same
holds for the completed functions up to a power of the discriminant. We prove:

* `gammaInf_normPow`: the archimedean factor of $\|\cdot\|^c$ is $\Gamma_{\mathbb R}(s+c)^{r_1}\Gamma_{\mathbb C}(s+c)^{r_2}$,
  the Dedekind gamma factor evaluated at $s+c$.
* `condDisc_normPow`: the conductor of $\|\cdot\|^c$ is trivial, so $A(\|\cdot\|^c) = |d_F|$.
* `completedHeckeL_normPow_of_re`: for $\operatorname{Re}s+\operatorname{Re}c>1$,
  $\Lambda(s,\|\cdot\|^c) = |d_F|^{-c/2}\Lambda_F(s+c)$.
* `completedHeckeL_normPow`: the same identity for all $s\ne-c,\,1-c$, by the identity theorem.
* `completedHeckeL_one`: for the trivial character, $\Lambda(s,1)=\Lambda_F(s)$ for $s\ne0,1$.

Tate's thesis, Cassels–Fröhlich Ch. XV, §4 [unverified locator]; Neukirch, *Algebraic Number Theory*, Ch. VII, §8
[unverified locator].
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set
open Topology
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

open GlobalZeta LocalZeta

/-- **The archimedean factor of $\|\cdot\|^c$** is the Dedekind gamma factor at $s+c$:
$L_\infty(s,\|\cdot\|^c) = \Gamma_{\mathbb R}(s+c)^{r_1}\Gamma_{\mathbb C}(s+c)^{r_2}$. -/
theorem gammaInf_normPow (c s : ℂ) :
    gammaInf (HeckeCharacter.normPow F c) s = gammaFactor F (s + c) := by
  have hr : ∀ w : {w : InfinitePlace F // w.IsReal},
      Complex.Gammaℝ (s + (HeckeCharacter.normPow F c).realExponent w.2 + eW (HeckeCharacter.normPow F c) w)
        = Complex.Gammaℝ (s + c) := by
    intro w
    have h : eW (HeckeCharacter.normPow F c) w = 0 := by
      simp [eW, HeckeCharacter.realSign_normPow, signExp]
    rw [h, HeckeCharacter.realExponent_normPow]; simp
  have hc : ∀ w : {w : InfinitePlace F // w.IsComplex},
      Complex.Gammaℂ (s + (HeckeCharacter.normPow F c).complexExponent w.2 / 2
        + ((kW (HeckeCharacter.normPow F c) w).natAbs : ℂ) / 2) = Complex.Gammaℂ (s + c) := by
    intro w
    have h : kW (HeckeCharacter.normPow F c) w = 0 := by
      simp [kW, HeckeCharacter.complexFrequency_normPow]
    rw [h, HeckeCharacter.complexExponent_normPow]; simp
  unfold gammaInf gammaFactor
  simp only [hr, hc, Finset.prod_const, Finset.card_univ]

/-- **The conductor-discriminant factor of $\|\cdot\|^c$** is $A(\|\cdot\|^c) = |d_F|$, since the conductor is trivial. -/
theorem condDisc_normPow (c : ℂ) : condDisc (HeckeCharacter.normPow F c) = |(discr F : ℝ)| := by
  simp [condDisc, condNorm, HeckeCharacter.conductor_normPow]

/-- **$\Lambda(s,\|\cdot\|^c) = |d_F|^{-c/2}\Lambda_F(s+c)$** for $\operatorname{Re}s+\operatorname{Re}c>1$. -/
theorem completedHeckeL_normPow_of_re (c : ℂ) {s : ℂ} (hs : 1 < s.re + c.re) :
    completedHeckeL (HeckeCharacter.normPow F c) s
      = ((|(discr F : ℝ)| : ℝ) : ℂ) ^ (-c / 2) * completedDedekindZeta F (s + c) := by
  have hs' : 1 < (s + c).re := by simpa using hs
  rw [completedHeckeL_eq _ (by simpa using hs), condDisc_normPow, gammaInf_normPow, heckeL_normPow,
    heckeL_one_eq_dedekindZeta hs', completedDedekindZeta_eq hs']
  have : s / 2 = -c / 2 + (s + c) / 2 := by ring
  rw [this, Complex.cpow_add _ _ abs_discr_ne_zero]
  ring

/-- **$\Lambda(s,\|\cdot\|^c) = |d_F|^{-c/2}\Lambda_F(s+c)$** for all $s\ne-c,\,1-c$. -/
theorem completedHeckeL_normPow (c : ℂ) {s : ℂ} (h0 : s ≠ -c) (h1 : s ≠ 1 - c) :
    completedHeckeL (HeckeCharacter.normPow F c) s
      = ((|(discr F : ℝ)| : ℝ) : ℂ) ^ (-c / 2) * completedDedekindZeta F (s + c) := by
  obtain ⟨z, hz, hzS⟩ := exists_re_gt_notMem ({-c, 1 - c} : Finset ℂ) (1 - c.re)
  refine eq_of_eqOn_open (f := completedHeckeL (HeckeCharacter.normPow F c))
    (g := fun s => ((|(discr F : ℝ)| : ℝ) : ℂ) ^ (-c / 2) * completedDedekindZeta F (s + c))
    {-c, 1 - c} ?_ ?_ (W := {s | 1 < s.re + c.re}) ?_ (z₀ := z) ?_ hzS
    (fun t ht => completedHeckeL_normPow_of_re c ht) (s := s) ?_
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    exact differentiableAt_completedHeckeL_normPow c ht.1 ht.2
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    refine (differentiableAt_const _).mul ?_
    have h := differentiableAt_completedDedekindZeta (F := F) (s := t + c)
      (fun h => ht.1 (by linear_combination h)) (fun h => ht.2 (by linear_combination h))
    exact h.comp t (differentiableAt_id.add_const c)
  · exact isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)
  · show 1 < z.re + c.re
    linarith
  · simp [h0, h1]

/-- **$\Lambda(s,1) = \Lambda_F(s)$**: the completed $L$-function of the trivial character is the completed Dedekind
zeta function, for $s\ne0,1$. -/
theorem completedHeckeL_one (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedHeckeL (1 : HeckeCharacter F) s = completedDedekindZeta F s := by
  have := completedHeckeL_normPow (F := F) 0 (s := s) (by simpa using h0) (by simpa using h1)
  simpa using this

end

end NumberFieldKB.HeckeL
