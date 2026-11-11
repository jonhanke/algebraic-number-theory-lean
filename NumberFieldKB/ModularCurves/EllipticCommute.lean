import NumberFieldKB.ModularCurves.EllipticFibre
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Cosets whose point $w_c$ lies over $j(\tau_0)$ are fixed by the elliptic element

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196). A real matrix $M$ of positive determinant
with $M i = i$ has the form $\begin{pmatrix} a & -c \\ c & a \end{pmatrix}$ and commutes with $S$; one with
$M\rho = \rho$ has the form $\begin{pmatrix} a & -c \\ c & a + c \end{pmatrix}$ and commutes with $ST$
(`commute_S_of_smul_I`, `commute_ST_of_smul_rho`).

If $j(w_c) = j(\tau_0)$ for $w_c = N\gamma_c^{-1}\tau_0$, then by `JInjective` (Milne's Proposition 2.2, a named
statement) $\delta w_c = \tau_0$ for some $\delta \in \mathrm{SL}_2(\mathbb Z)$; $M = \delta \operatorname{diag}(N, 1)
\gamma_c^{-1}$ fixes $\tau_0$, so it commutes with $g$, and $j_N \circ \gamma_c^{-1} = j \circ M$ is invariant under
$g$: the coset $c$ is fixed by $g$ (`smul_eq_of_jFun_cosetPoint_eq`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped MatrixGroups

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

theorem GL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = (g i j : ℝ) := rfl

theorem GL_S : ((ModularGroup.S : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0] := by
  ext i j; rw [GL_apply]; fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_S]

theorem GL_ST :
    (((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 1] := by
  ext i j; rw [GL_apply]; fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_S, ModularGroup.coe_T, Matrix.SpecialLinearGroup.coe_mul]

/-- The fixed-point equation $M\tau = \tau$ as $a\tau + b = \tau(c\tau + d)$. -/
theorem num_eq_of_smul_eq {M : GL (Fin 2) ℝ} (hM : 0 < (Matrix.GeneralLinearGroup.det M : ℝ)) {τ : ℍ}
    (hfix : M • τ = τ) : num M τ = (τ : ℂ) * denom M τ := by
  have h := UpperHalfPlane.coe_smul_of_det_pos hM τ
  rw [hfix, eq_div_iff (denom_ne_zero M τ)] at h
  exact h.symm

/-- **A matrix of positive determinant fixing $i$ commutes with $S$.** -/
theorem commute_S_of_smul_I {M : GL (Fin 2) ℝ} (hM : 0 < (Matrix.GeneralLinearGroup.det M : ℝ))
    (hfix : M • UpperHalfPlane.I = UpperHalfPlane.I) :
    M * (ModularGroup.S : GL (Fin 2) ℝ) = (ModularGroup.S : GL (Fin 2) ℝ) * M := by
  have h := num_eq_of_smul_eq hM hfix
  simp only [num, denom, UpperHalfPlane.coe_I] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, GL_S]
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- **A matrix of positive determinant fixing $\rho$ commutes with $ST$.** -/
theorem commute_ST_of_smul_rho {M : GL (Fin 2) ℝ} (hM : 0 < (Matrix.GeneralLinearGroup.det M : ℝ))
    (hfix : M • ρ = ρ) :
    M * ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) * M := by
  have h := num_eq_of_smul_eq hM hfix
  simp only [num, denom] at h
  have hsq := UpperHalfPlane.ρ_sq
  have h2 : (((M 0 0 + M 1 0 - M 1 1 : ℝ) : ℂ)) * ρ + ((M 0 1 + M 1 0 : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination h + (M 1 0 : ℂ) * hsq
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.zero_im, Complex.add_re, Complex.mul_re, sub_zero, Complex.zero_re] at him hre
  have hpos := ρ.im_pos
  have h1 : M 0 0 + M 1 0 - M 1 1 = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · exact absurd h hpos.ne'
  rw [h1, zero_mul, zero_add] at hre
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, GL_ST]
  fin_cases i <;> fin_cases j <;> simp <;> linarith

variable (N : ℕ) [NeZero N]

/-- $\operatorname{diag}(N, 1)$. -/
def diagN : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(N : ℝ), 0; 0, 1] (by simp [NeZero.ne N])

theorem det_diagN : (Matrix.GeneralLinearGroup.det (diagN N) : ℝ) = N := by
  simp [diagN, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem coe_diagN_smul (w : ℍ) : ((diagN N • w : ℍ) : ℂ) = N * w := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [det_diagN]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))]
  simp [num, denom, diagN, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem jN_eq_jFun_diagN (w : ℍ) : jN N w = jFun (diagN N • w) := by
  rw [jN, ← coe_diagN_smul, ofComplex_apply]

theorem det_SL_GL_units (g : SL(2, ℤ)) : (Matrix.GeneralLinearGroup.det (g : GL (Fin 2) ℝ) : ℝ) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact det_SL_GL g

/-- **If $j(w_c) = j(\tau_0)$, the coset $c$ is fixed by $g$**, given `JInjective` and that matrices of positive
determinant fixing $\tau_0$ commute with $g$. -/
theorem smul_eq_of_jFun_cosetPoint_eq (hJ : JInjective) (τ₀ : ℍ) (g : SL(2, ℤ))
    (hcomm : ∀ M : GL (Fin 2) ℝ, 0 < (Matrix.GeneralLinearGroup.det M : ℝ) → M • τ₀ = τ₀ →
      M * (g : GL (Fin 2) ℝ) = (g : GL (Fin 2) ℝ) * M)
    (c : Cosets N) (hj : jFun (cosetPoint N τ₀ c) = jFun τ₀) : g⁻¹ • c = c := by
  obtain ⟨δ, hδ⟩ := hJ.orbit _ _ hj
  set γ := Quotient.out c
  have hw : cosetPoint N τ₀ c = diagN N • (γ⁻¹ • τ₀) := by
    apply UpperHalfPlane.ext
    rw [coe_cosetPoint, coe_diagN_smul, cosetMoeb, moeb_coe]
  set M : GL (Fin 2) ℝ := (δ : GL (Fin 2) ℝ) * diagN N * ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)
  have hMz : ∀ z : ℍ, M • z = δ • (diagN N • (γ⁻¹ • z)) := by
    intro z
    simp only [M, mul_smul]
    rfl
  have hMdet : 0 < (Matrix.GeneralLinearGroup.det M : ℝ) := by
    simp only [M, map_mul, Units.val_mul, det_SL_GL_units, det_diagN, one_mul, mul_one]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hMfix : M • τ₀ = τ₀ := by rw [hMz, ← hw, hδ]
  have hcm := hcomm M hMdet hMfix
  have hroot : ∀ z, cosetRoot N c z = jFun (M • z) := by
    intro z
    rw [hMz, jFun_smul, cosetRoot, jN_eq_jFun_diagN]
  have hinv : ∀ z, cosetRoot N c (g • z) = cosetRoot N c z := by
    intro z
    rw [hroot, hroot]
    change jFun (M • ((g : GL (Fin 2) ℝ) • z)) = _
    rw [← mul_smul, hcm, mul_smul]
    exact jFun_smul g (M • z)
  apply cosetRoot_injective (one_le_N N)
  funext z
  have := cosetRoot_smul (one_le_N N) g⁻¹ c (g • z)
  rw [inv_smul_smul] at this
  rw [this, hinv]

end NumberFieldKB.ModularCurves
