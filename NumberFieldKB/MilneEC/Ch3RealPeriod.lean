import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch3RealLattice
import NumberFieldKB.MilneEC.Ch3RealCubic

/-!
# The real period and the period lattice

Not a numbered item of Milne, *Elliptic Curves*: this file connects the period
$\Omega = \int_{E(\mathbb R)}|\omega|$ of Milne's Conjecture IV.10.5, pdf p. 173, computed as Formal Conjectures'
`realPeriod`, with the uniformization $E(\mathbb C) \cong \mathbb C/\Lambda$ of Chapter III, Theorem 3.10 and
Proposition 3.7.

**Main result.** For an elliptic curve $W$ over $\mathbb R$, the real period is the least positive real period of
the lattice times the number of connected components of $E(\mathbb R)$:
$$\Omega(W) = \#\pi_0(E(\mathbb R))\cdot\omega_{\mathbb R}(\Lambda), \qquad \#\pi_0(E(\mathbb R)) = \begin{cases}
2 & \Delta > 0\\ 1 & \Delta < 0,\end{cases}$$
for every lattice $\Lambda$ with $E(\Lambda) \cong W_{\mathbb C}$ by a change of variables with $u = 1$ over
$\mathbb R$ (`realPeriod_eq_of_variableChange`); such a lattice exists (`rp1_real_period`, from Chapter III's
`exists_lattice_with_g`).

* `realCurveOf L`: Milne's $E(\Lambda)$, $y^2 = x^3 - \tfrac{g_2}4x - \tfrac{g_3}4$ (Mathlib's normalization, as
  `curveOf`), over $\mathbb R$ when the invariants are real; `realCurveOf_map`: its base change to $\mathbb C$ is
  `curveOf L`.
* `realComponentCount W`: `if 0 < W.Δ then 2 else 1`; `delta_pos_iff_three_real_roots` shows that $\Delta > 0$
  exactly when $\Psi_2^2$ has three real roots, i.e. when $\{x : \Psi_2^2(x) \ge 0\}$, over which $E(\mathbb R)$
  lies, has two components.
* `realPeriod_realCurveOf`: $\Omega(E(\Lambda)_{\mathbb R}) = \#\pi_0\cdot\omega_{\mathbb R}(\Lambda)$.

Scaling: a change of variables with $u \ne 1$ multiplies $\Omega$ by $|u|$ and the lattice by $u^{-1}$ (not needed
here, since $u = 1$ suffices to reach $E(\Lambda)$ over $\mathbb R$).
-/

open Set MeasureTheory

namespace NumberFieldKB.MilneEC.III

/-- Milne's $E(\Lambda)$ over $\mathbb R$: $y^2 = x^3 - \tfrac{\operatorname{Re} g_2}4x - \tfrac{\operatorname{Re}
g_3}4$ (for a lattice with real invariants, this is `curveOf L` over $\mathbb R$, `realCurveOf_map`). -/
noncomputable def realCurveOf (L : PeriodPair) : WeierstrassCurve ℝ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -(L.g₂.re / 4), a₆ := -(L.g₃.re / 4) }

/-- The number of connected components of $E(\mathbb R)$: $2$ if $\Delta > 0$, else $1$
(see `delta_pos_iff_three_real_roots`). -/
noncomputable def realComponentCount (W : WeierstrassCurve ℝ) : ℕ := if 0 < W.Δ then 2 else 1

/-- For real invariants, the base change of `realCurveOf L` to $\mathbb C$ is `curveOf L`. -/
theorem realCurveOf_map {L : PeriodPair} (h : HasRealInvariants L) :
    (realCurveOf L).map (algebraMap ℝ ℂ) = curveOf L := by
  have h2 : ((L.g₂.re : ℝ) : ℂ) = L.g₂ := Complex.ext rfl (by simp [h.1])
  have h3 : ((L.g₃.re : ℝ) : ℂ) = L.g₃ := Complex.ext rfl (by simp [h.2])
  ext <;> simp [realCurveOf, curveOf, h2, h3]

/-- $\Psi_2^2$ of `realCurveOf L` is the real cubic $4x^3 - g_2x - g_3$. -/
theorem eval_Ψ₂Sq_realCurveOf (L : PeriodPair) (x : ℝ) :
    (realCurveOf L).Ψ₂Sq.eval x = realCubic L x := by
  simp [WeierstrassCurve.Ψ₂Sq, realCurveOf, realCubic, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring

/-- `realCurveOf L` is an elliptic curve when the invariants are real. -/
theorem isElliptic_realCurveOf {L : PeriodPair} (h : HasRealInvariants L) : (realCurveOf L).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  intro h0
  have hc : (curveOf L).Δ = 0 := by
    rw [← realCurveOf_map h, WeierstrassCurve.map_Δ, h0, map_zero]
  exact (isUnit_iff_ne_zero.1 (curveOf L).isUnit_Δ) hc

/-- **The real period of $E(\Lambda)$** for a lattice with real invariants: $\Omega = \#\pi_0(E(\mathbb R))\cdot
\omega_{\mathbb R}(\Lambda)$. -/
@[kb "milne2006ec" "Ch. IV, §10, the real period Ω of Conjecture 10.5 through Ch. III's lattice, pdf p. 173"]
theorem realPeriod_realCurveOf {L : PeriodPair} (h : HasRealInvariants L) :
    FormalConjectures.realPeriod (realCurveOf L) =
      realComponentCount (realCurveOf L) * leastRealPeriod L := by
  have := isElliptic_realCurveOf h
  obtain ⟨e, -, he, hpos, hint, hI⟩ := halfPeriod_integral h
  have hF : ∀ x, (realCurveOf L).Ψ₂Sq.eval x = realCubic L x := eval_Ψ₂Sq_realCurveOf L
  simp_rw [← hF] at he hpos hint hI
  rw [realPeriod_eq_of_largest_root (realCurveOf L) he hpos hint, hI, realComponentCount]
  split_ifs <;> push_cast <;> ring

/-- **The real period, for any lattice reached with $u = 1$.** If a change of variables with $u = 1$ over $\mathbb R$ takes $W$ to
$E(\Lambda)$ for a lattice with real invariants, then $\Omega(W) = \#\pi_0(E(\mathbb R))\cdot\omega_{\mathbb R}(\Lambda)$. -/
@[kb "milne2006ec" "Ch. IV, §10, the real period Ω of Conjecture 10.5 through Ch. III's lattice, pdf p. 173"]
theorem realPeriod_eq_of_variableChange (W : WeierstrassCurve ℝ) {L : PeriodPair} (h : HasRealInvariants L)
    (C : WeierstrassCurve.VariableChange ℝ) (hu : C.u = 1) (hC : C • W = realCurveOf L) :
    FormalConjectures.realPeriod W = realComponentCount W * leastRealPeriod L := by
  have hΔ : (C • W).Δ = W.Δ := by
    rw [WeierstrassCurve.variableChange_Δ, hu]; simp
  rw [← realPeriod_variableChange_of_u_eq_one W C hu, hC, realPeriod_realCurveOf h,
    realComponentCount, realComponentCount, ← hC, hΔ]

/-- **The real period and the lattice**: for every elliptic curve $W$ over $\mathbb R$ there is a lattice
$\Lambda$ with real invariants and a change of variables with $u = 1$ taking $W$ to $E(\Lambda)$; for it,
Formal Conjectures' real period is the number of real components times the least positive real period:
$\Omega(W) = \#\pi_0(E(\mathbb R))\cdot\omega_{\mathbb R}(\Lambda)$. -/
@[kb "milne2006ec" "Ch. IV, §10, the real period Ω of Conjecture 10.5 through Ch. III's lattice, pdf p. 173"]
theorem rp1_real_period (W : WeierstrassCurve ℝ) [W.IsElliptic] :
    ∃ L : PeriodPair, HasRealInvariants L ∧
      ∃ C : WeierstrassCurve.VariableChange ℝ, C.u = 1 ∧ C • W = realCurveOf L ∧
        FormalConjectures.realPeriod W = realComponentCount W * leastRealPeriod L := by
  obtain ⟨C, hu, h1, h2, h3⟩ := exists_variableChange_short W
  set W' := C • W with hW'
  have hell : W'.IsElliptic := by rw [hW']; infer_instance
  have hΔW' : W'.Δ = -16 * (4 * W'.a₄ ^ 3 + 27 * W'.a₆ ^ 2) := by
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, h1, h2, h3]
    ring
  have hΔ0 : W'.Δ ≠ 0 := isUnit_iff_ne_zero.1 hell.isUnit
  have hg : ((-4 * W'.a₄ : ℝ) : ℂ) ^ 3 - 27 * ((-4 * W'.a₆ : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have : ((-4 * W'.a₄) ^ 3 - 27 * (-4 * W'.a₆) ^ 2 : ℝ) ≠ 0 := by
      intro h0; apply hΔ0; rw [hΔW']; linear_combination h0
    exact_mod_cast this
  obtain ⟨L, hL2, hL3⟩ := CurveAux.exists_lattice_with_g _ _ hg
  have hreal : HasRealInvariants L := ⟨by rw [hL2]; simp, by rw [hL3]; simp⟩
  have hCW : C • W = realCurveOf L := by
    rw [← hW']
    ext <;> simp [realCurveOf, hL2, hL3, h1, h2, h3] <;> ring
  exact ⟨L, hreal, C, hu, hCW, realPeriod_eq_of_variableChange W hreal C hu hCW⟩

end NumberFieldKB.MilneEC.III
