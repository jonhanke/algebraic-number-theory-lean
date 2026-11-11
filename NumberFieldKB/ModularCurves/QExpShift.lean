import NumberFieldKB.ModularCurves.CuspInfinity
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# $q$-expansions of $f(z + r)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2: at the cusps of $X_0(N)$ the conjugates of $j_N$ are
$j((az + b)/d)$, whose expansions are those of $j$ twisted by roots of unity. For $f$ with a $q$-expansion (period 1)
and $r \in \mathbb R$, $z \mapsto f(z + r)$ has a $q$-expansion with coefficients $e^{2\pi i n r} c_n$
(`IsQExp.shift`, `qExpansion_shift_coeff`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex ModularForm
open scoped MatrixGroups Real

namespace NumberFieldKB.ModularCurves

/-- $f(z + r)$. -/
noncomputable def shiftR (r : ℝ) (f : ℍ → ℂ) (z : ℍ) : ℂ := f (r +ᵥ z)

/-- On the upper half plane, `shiftR r f ∘ ofComplex` is `f ∘ ofComplex` translated by `r`. -/
lemma shiftR_ofComplex (r : ℝ) (f : ℍ → ℂ) {w : ℂ} (hw : 0 < w.im) :
    shiftR r f (ofComplex w) = (f ∘ ofComplex) ((r : ℂ) + w) := by
  have h1 : 0 < ((r : ℂ) + w).im := by simpa using hw
  have : r +ᵥ (ofComplex w : ℍ) = ofComplex ((r : ℂ) + w) := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd, ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos h1]
  simp only [shiftR, this, Function.comp_apply]

/-- The `q`-parameter of a real translate. -/
lemma qParam_shift (r : ℝ) (z : ℍ) :
    Function.Periodic.qParam 1 ((r +ᵥ z : ℍ) : ℂ) =
      cexp (2 * π * I * r) * Function.Periodic.qParam 1 (z : ℂ) := by
  rw [UpperHalfPlane.coe_vadd]
  simp only [Function.Periodic.qParam, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem IsQExp.shift {f : ℍ → ℂ} (hf : IsQExp f) (r : ℝ) : IsQExp (shiftR r f) where
  mdiff := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hf' := UpperHalfPlane.mdifferentiable_iff.1 hf.mdiff
    have hmaps : Set.MapsTo (fun w : ℂ => (r : ℂ) + w) {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} :=
      fun w hw => by simpa using hw
    refine (hf'.comp ((differentiable_id.const_add _).differentiableOn) hmaps).congr ?_
    intro w hw
    exact shiftR_ofComplex r f hw
  periodic := by
    intro w
    simp only [Function.comp_apply]
    rcases le_or_gt w.im 0 with hw | hw
    · rw [ofComplex_apply_eq_of_im_nonpos (w := w + 1) (w' := w) (by simpa using hw) hw]
    · have hw1 : 0 < (w + 1).im := by simpa using hw
      rw [shiftR_ofComplex r f hw1, shiftR_ofComplex r f hw]
      have := hf.periodic ((r : ℂ) + w)
      rw [← this]
      simp only [Function.comp_apply]
      congr 2
      ring
  bounded := by
    obtain ⟨M, A, h⟩ := isBoundedAtImInfty_iff.1 hf.bounded
    refine isBoundedAtImInfty_iff.2 ⟨M, A, fun z hz => h _ ?_⟩
    simpa [UpperHalfPlane.vadd_im] using hz

/-- The $q$-expansion of $f(z + r)$: the coefficient of $q^n$ is $e^{2\pi i n r}$ times that of $f$. -/
theorem qExpansion_shift_coeff {f : ℍ → ℂ} (hf : IsQExp f) (r : ℝ) (n : ℕ) :
    (qExpansion 1 (shiftR r f)).coeff n = cexp (2 * π * I * n * r) * (qExpansion 1 f).coeff n := by
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => (cexp (2 * π * I * m * r) * (qExpansion 1 f).coeff m) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (shiftR r f τ) := by
    intro τ
    have h0 := hasSum_qExpansion one_pos hf.periodic hf.mdiff hf.bounded (r +ᵥ τ)
    show HasSum _ (f (r +ᵥ τ))
    convert h0 using 1
    funext m
    rw [qParam_shift, mul_pow, ← Complex.exp_nat_mul]
    simp only [smul_eq_mul]
    have : (m : ℂ) * (2 * π * I * r) = 2 * π * I * m * r := by ring
    rw [this]
    ring
  exact (qExpansion_coeff_unique' (hf.shift r).analytic hsum n).symm

end NumberFieldKB.ModularCurves
