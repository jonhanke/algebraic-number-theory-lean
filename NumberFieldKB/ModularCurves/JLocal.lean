import Mathlib.NumberTheory.ModularForms.RamanujanFormula
import NumberFieldKB.MilneEC.Ch5JFunction
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# The local behaviour of $j$ at a point of $\mathbb H$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (the ramification of $j : X_0(N) \to X_0(1)$, pdf p. 196).
In the coordinate $z$ of $\mathbb H$, $j - j(\tau)$ has order $1$ at $\tau$ unless $j(\tau) \in \{0, 1728\}$, order $3$
if $j(\tau) = 0$ and order $2$ if $j(\tau) = 1728$.

The proof does not use the valence formula. Ramanujan's formulas (Mathlib, `Derivative.normalizedDerivOfComplex_E₄`,
`Derivative.normalizedDerivOfComplex_E₆`) give $D(E_4^3 - E_6^2) = E_2 (E_4^3 - E_6^2)$ and so
$$ D j = -1728\, \frac{E_4^2 E_6}{E_4^3 - E_6^2}, \qquad D = \frac{1}{2\pi i}\frac{d}{dz}, $$
which vanishes only where $E_4 E_6$ does, that is where $j \in \{0, 1728\}$. At a zero of $E_4$,
$D E_4 = -E_6/3 \ne 0$; at a zero of $E_6$, $D E_6 = -E_4^2/2 \ne 0$; and $j = 1728 E_4^3/(E_4^3 - E_6^2)$,
$j - 1728 = 1728 E_6^2/(E_4^3 - E_6^2)$ with a nonvanishing denominator.

Orders are `analyticOrderAt` of the function $z \mapsto j(z)$ on $\mathbb C$ (through `UpperHalfPlane.ofComplex`).
-/

open UpperHalfPlane hiding I
open Complex Filter Topology ModularForm EisensteinSeries
open scoped Manifold MatrixGroups Real

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-- $E_4^3 - E_6^2 = 1728 \Delta$ does not vanish on $\mathbb H$. -/
theorem E4_cube_sub_E6_sq_ne_zero (τ : ℍ) : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  intro h0
  rw [h0, zero_div] at h
  exact ModularForm.discriminant_ne_zero τ h

/-- A holomorphic function on $\mathbb H$ is analytic in the coordinate $z$. -/
theorem analyticAt_comp_ofComplex {f : ℍ → ℂ} (hf : MDiff f) (τ : ℍ) :
    AnalyticAt ℂ (f ∘ ofComplex) (τ : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.1 hf).analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem mdiff_E4 : MDiff (E₄ : ℍ → ℂ) := E₄.holo'

theorem mdiff_E6 : MDiff (E₆ : ℍ → ℂ) := E₆.holo'

/-- $\frac{d}{dz} E_4 = \frac{2\pi i}{3}(E_2 E_4 - E_6)$. -/
theorem deriv_E4 (τ : ℍ) :
    deriv ((E₄ : ℍ → ℂ) ∘ ofComplex) τ = 2 * π * I * (3⁻¹ * (E2 τ * E₄ τ - E₆ τ)) := by
  have h := congrFun Derivative.normalizedDerivOfComplex_E₄ τ
  simp only [Derivative.normalizedDerivOfComplex, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply,
    smul_eq_mul] at h
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [← h, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]

/-- $\frac{d}{dz} E_6 = \pi i (E_2 E_6 - E_4^2)$. -/
theorem deriv_E6 (τ : ℍ) :
    deriv ((E₆ : ℍ → ℂ) ∘ ofComplex) τ = 2 * π * I * (2⁻¹ * (E2 τ * E₆ τ - E₄ τ ^ 2)) := by
  have h := congrFun Derivative.normalizedDerivOfComplex_E₆ τ
  simp only [Derivative.normalizedDerivOfComplex, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply,
    Pi.pow_apply, smul_eq_mul] at h
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [← h, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]

/-- In the coordinate $z$: $j = 1728 E_4^3 / (E_4^3 - E_6^2)$ near $\tau$. -/
theorem jFun_comp_eq :
    (jFun ∘ ofComplex) = fun z : ℂ =>
      1728 * ((E₄ : ℍ → ℂ) ∘ ofComplex) z ^ 3 /
        (((E₄ : ℍ → ℂ) ∘ ofComplex) z ^ 3 - ((E₆ : ℍ → ℂ) ∘ ofComplex) z ^ 2) := by
  funext z
  simp only [Function.comp_apply, jFun_eq']

/-- $j$ is analytic in the coordinate $z$. -/
theorem analyticAt_jFun (τ : ℍ) : AnalyticAt ℂ (jFun ∘ ofComplex) (τ : ℂ) := by
  rw [jFun_comp_eq]
  have h4 := analyticAt_comp_ofComplex mdiff_E4 τ
  have h6 := analyticAt_comp_ofComplex mdiff_E6 τ
  refine (analyticAt_const.mul (h4.pow 3)).div ((h4.pow 3).sub (h6.pow 2)) ?_
  simpa [ofComplex_apply] using E4_cube_sub_E6_sq_ne_zero τ

/-- **The derivative of $j$**: $\frac{d}{dz} j = -2\pi i \cdot 1728\, E_4^2 E_6 / (E_4^3 - E_6^2)$. -/
theorem deriv_jFun (τ : ℍ) :
    deriv (jFun ∘ ofComplex) τ = -(2 * π * I) * 1728 * E₄ τ ^ 2 * E₆ τ / (E₄ τ ^ 3 - E₆ τ ^ 2) := by
  have h4 := analyticAt_comp_ofComplex mdiff_E4 τ
  have h6 := analyticAt_comp_ofComplex mdiff_E6 τ
  have hB : (((E₄ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) ^ 3 - ((E₆ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) ^ 2) ≠ 0 := by
    simpa [ofComplex_apply] using E4_cube_sub_E6_sq_ne_zero τ
  have hd4 := h4.differentiableAt.hasDerivAt
  have hd6 := h6.differentiableAt.hasDerivAt
  have hnum := (hd4.pow 3).const_mul (1728 : ℂ)
  have hden := (hd4.pow 3).sub (hd6.pow 2)
  have hq := hnum.div hden hB
  have e : (fun z : ℂ => 1728 * ((E₄ : ℍ → ℂ) ∘ ofComplex) z ^ 3 /
      (((E₄ : ℍ → ℂ) ∘ ofComplex) z ^ 3 - ((E₆ : ℍ → ℂ) ∘ ofComplex) z ^ 2)) =
      (fun y ↦ 1728 * (((E₄ : ℍ → ℂ) ∘ ofComplex) ^ 3) y) /
        (((E₄ : ℍ → ℂ) ∘ ofComplex) ^ 3 - ((E₆ : ℍ → ℂ) ∘ ofComplex) ^ 2) := by
    funext z; simp
  rw [jFun_comp_eq, e, hq.deriv, deriv_E4, deriv_E6]
  simp only [Function.comp_apply, ofComplex_apply, Nat.cast_ofNat, Pi.pow_apply, Pi.sub_apply]
  have hB' := E4_cube_sub_E6_sq_ne_zero τ
  field_simp
  ring

/-- $j(\tau) = 0$ iff $E_4(\tau) = 0$. -/
theorem jFun_eq_zero_iff (τ : ℍ) : jFun τ = 0 ↔ E₄ τ = 0 := by
  rw [jFun_eq', div_eq_zero_iff]
  have := E4_cube_sub_E6_sq_ne_zero τ
  simp [this]

/-- $j(\tau) = 1728$ iff $E_6(\tau) = 0$. -/
theorem jFun_eq_1728_iff (τ : ℍ) : jFun τ = 1728 ↔ E₆ τ = 0 := by
  have hB := E4_cube_sub_E6_sq_ne_zero τ
  rw [jFun_eq', div_eq_iff hB]
  constructor
  · intro h
    have : 1728 * E₆ τ ^ 2 = 0 := by linear_combination h
    simpa using this
  · intro h
    rw [h]
    ring

/-- **Away from $j \in \{0, 1728\}$, $j - j(\tau)$ has a simple zero at $\tau$.** -/
theorem analyticOrderAt_jFun_sub_eq_one (τ : ℍ) (h0 : jFun τ ≠ 0) (h1728 : jFun τ ≠ 1728) :
    analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun τ) (τ : ℂ) = 1 := by
  have h := (analyticAt_jFun τ).analyticOrderAt_sub_eq_one_of_deriv_ne_zero ?_
  · simpa [ofComplex_apply] using h
  rw [deriv_jFun]
  have h4 : E₄ τ ≠ 0 := fun h => h0 ((jFun_eq_zero_iff τ).2 h)
  have h6 : E₆ τ ≠ 0 := fun h => h1728 ((jFun_eq_1728_iff τ).2 h)
  have hB := E4_cube_sub_E6_sq_ne_zero τ
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 h2) (by norm_num))
    (pow_ne_zero _ h4)) h6) hB

/-- A function analytic at $x$ with value $0$ and nonzero derivative has order $1$. -/
theorem analyticOrderAt_eq_one_of_zero {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (h0 : f x = 0)
    (hd : deriv f x ≠ 0) : analyticOrderAt f x = 1 := by
  have h := hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd
  simpa [h0] using h

/-- Multiplying by a function analytic and nonzero at $x$ does not change the order. -/
theorem analyticOrderAt_mul_unit {f g : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (hgx : g x ≠ 0) : analyticOrderAt (fun z => f z * g z) x = analyticOrderAt f x := by
  have h := analyticOrderAt_mul hf hg
  have hg0 : analyticOrderAt g x = 0 := analyticOrderAt_eq_zero.2 (Or.inr hgx)
  rw [show (fun z => f z * g z) = f * g from rfl, h, hg0, add_zero]

/-- **At a zero of $j$, $j$ has order $3$.** -/
theorem analyticOrderAt_jFun_of_eq_zero (τ : ℍ) (h0 : jFun τ = 0) :
    analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun τ) (τ : ℂ) = 3 := by
  have h4 := analyticAt_comp_ofComplex mdiff_E4 τ
  have h6 := analyticAt_comp_ofComplex mdiff_E6 τ
  have hE4 : E₄ τ = 0 := (jFun_eq_zero_iff τ).1 h0
  have hB := E4_cube_sub_E6_sq_ne_zero τ
  have hE6 : E₆ τ ≠ 0 := by
    intro h; apply hB; rw [hE4, h]; ring
  set g : ℂ → ℂ := fun z =>
    1728 / (((E₄ : ℍ → ℂ) ∘ ofComplex) z ^ 3 - ((E₆ : ℍ → ℂ) ∘ ofComplex) z ^ 2) with hg
  have hBz : (((E₄ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) ^ 3 - ((E₆ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) ^ 2) ≠ 0 := by
    simpa [ofComplex_apply] using hB
  have hga : AnalyticAt ℂ g τ := analyticAt_const.div ((h4.pow 3).sub (h6.pow 2)) hBz
  have hg0 : g τ ≠ 0 := div_ne_zero (by norm_num) hBz
  have heq : (fun z => (jFun ∘ ofComplex) z - jFun τ) =
      fun z => (((E₄ : ℍ → ℂ) ∘ ofComplex) ^ 3) z * g z := by
    funext z
    rw [h0, sub_zero, jFun_comp_eq]
    simp only [hg, Pi.pow_apply]
    ring
  rw [heq, analyticOrderAt_mul_unit (h4.pow 3) hga hg0, analyticOrderAt_pow h4]
  have hord : analyticOrderAt ((E₄ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) = 1 := by
    refine analyticOrderAt_eq_one_of_zero h4 (by simpa [ofComplex_apply] using hE4) ?_
    rw [deriv_E4, hE4]
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    simpa [h2] using hE6
  rw [hord]
  rfl

/-- **At a point with $j = 1728$, $j - 1728$ has order $2$.** -/
theorem analyticOrderAt_jFun_of_eq_1728 (τ : ℍ) (h1728 : jFun τ = 1728) :
    analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun τ) (τ : ℂ) = 2 := by
  have h4 := analyticAt_comp_ofComplex mdiff_E4 τ
  have h6 := analyticAt_comp_ofComplex mdiff_E6 τ
  have hE6 : E₆ τ = 0 := (jFun_eq_1728_iff τ).1 h1728
  have hB := E4_cube_sub_E6_sq_ne_zero τ
  have hE4 : E₄ τ ≠ 0 := by
    intro h; apply hB; rw [hE6, h]; ring
  set g : ℂ → ℂ := fun z =>
    1728 / (((E₄ : ℍ → ℂ) ∘ ofComplex) z ^ 3 - ((E₆ : ℍ → ℂ) ∘ ofComplex) z ^ 2) with hg
  have hBz : (((E₄ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) ^ 3 - ((E₆ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) ^ 2) ≠ 0 := by
    simpa [ofComplex_apply] using hB
  have hga : AnalyticAt ℂ g τ := analyticAt_const.div ((h4.pow 3).sub (h6.pow 2)) hBz
  have hg0 : g τ ≠ 0 := div_ne_zero (by norm_num) hBz
  have heq : (fun z => (jFun ∘ ofComplex) z - jFun τ) =
      fun z => (((E₆ : ℍ → ℂ) ∘ ofComplex) ^ 2) z * g z := by
    funext z
    rw [h1728, jFun_comp_eq]
    simp only [hg, Pi.pow_apply]
    have hz : (((E₄ : ℍ → ℂ) ∘ ofComplex) z ^ 3 - ((E₆ : ℍ → ℂ) ∘ ofComplex) z ^ 2) ≠ 0 := by
      simpa using E4_cube_sub_E6_sq_ne_zero (ofComplex z)
    field_simp
    ring
  rw [heq, analyticOrderAt_mul_unit (h6.pow 2) hga hg0, analyticOrderAt_pow h6]
  have hord : analyticOrderAt ((E₆ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) = 1 := by
    refine analyticOrderAt_eq_one_of_zero h6 (by simpa [ofComplex_apply] using hE6) ?_
    rw [deriv_E6, hE6]
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    simpa [h2] using hE4
  rw [hord]
  rfl

end NumberFieldKB.ModularCurves
