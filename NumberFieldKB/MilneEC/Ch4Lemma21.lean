import NumberFieldKB.MilneEC.Ch3Torsion
import NumberFieldKB.MilneEC.Ch4Selmer
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Omega
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.Affine.IsAlgClosed

/-!
# Milne, Elliptic Curves: Lemma III.3.14, Proposition III.3.13 and Lemma IV.2.1

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`).  This file proves three named statements of
the library from the division-polynomial multiplication formula, ported from Tau Ceti
(`NumberFieldKB/TauCetiPort/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/ZSMul.lean`,
`WeierstrassCurve.zsmul_point_eq_smulEval`, with the coprimality of $\Phi_n$ and $\Psi_n^2$ from `Coprimality.lean`):

* `divisionPolynomialFormula : III.DivisionPolynomialFormula` (Lemma III.3.14, pdf p. 103): the coordinates of $nP$
  on $Y^2 = X^3 + aX + b$ are $(x - \psi_{n-1}\psi_{n+1}/\psi_n^2,\ \psi_{2n}/2\psi_n^4)$, and $nP = O$ when
  $\psi_n(P) = 0$.
* `torsionBaseChange : III.TorsionBaseChange` (Proposition III.3.13, pdf p. 103, in every characteristic): for
  algebraically closed fields $k \subseteq \Omega$ every torsion point of $E(\Omega)$ lies in $E(k)$.  Milne's proof
  needs characteristic different from 2 and 3; in every characteristic the $x$-coordinate of an $n$-torsion point is
  a root of $\Psi_n^2$, which is a nonzero polynomial over $k$ (`ΨSq_ne_zero_of_Δ_ne_zero`).
* `lemma2_1 : Lemma2_1` (Lemma IV.2.1, pdf p. 116, in every characteristic): for an elliptic curve over an
  algebraically closed field and $n \ne 0$, $P \mapsto nP$ is surjective.  Milne's proofs are geometric (the image of
  the regular map $n$ is closed and connected) or analytic (over $\mathbb C$); here, for $P = (x_0, y_0)$, a root
  $x_1$ of the monic polynomial $\Phi_n - x_0\Psi_n^2$ of degree $n^2$ is not a root of $\Psi_n^2$ (coprimality),
  so a point $Q$ over $x_1$ has $x(nQ) = \Phi_n(x_1)/\Psi_n^2(x_1) = x_0$, and $nQ = \pm P$.
-/

open Polynomial WeierstrassCurve

namespace NumberFieldKB.MilneEC

section Formula

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- The affine form of the multiplication formula: if $\psi_n(P) \ne 0$ then
$nP = (\varphi_n(P)/\psi_n(P)^2, \omega_n(P)/\psi_n(P)^3)$ (from Tau Ceti's Jacobian form
`zsmul_point_eq_smulEval`). -/
theorem zsmul_some_eq_of_evalEval_ψ_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ)
    (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ h' : W.toAffine.Nonsingular ((W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2)
        ((W.ω n).evalEval x y / (W.ψ n).evalEval x y ^ 3),
      n • Affine.Point.some x y h = Affine.Point.some _ _ h' := by
  have hQ := zsmul_point_eq_smulEval W h n
  have hz : smulEval W x y n 2 ≠ 0 := by simpa [smulEval] using hψ
  have key : n • Affine.Point.some x y h = Jacobian.Point.toAffineAddEquiv _
      (n • Jacobian.Point.fromAffine (Affine.Point.some x y h)) := by
    rw [← Jacobian.Point.toAffineAddEquiv_symm_apply, ← map_zsmul, AddEquiv.apply_symm_apply]
  rw [key, Jacobian.Point.toAffineAddEquiv_apply]
  generalize n • Jacobian.Point.fromAffine (Affine.Point.some x y h) = Q at hQ ⊢
  rcases Q with @⟨pt, hpt⟩
  subst hQ
  rw [Jacobian.Point.toAffineLift_of_Z_ne_zero hz]
  have e0 : smulEval W x y n 0 = (W.φ n).evalEval x y := rfl
  have e1 : smulEval W x y n 1 = (W.ω n).evalEval x y := rfl
  have e2 : smulEval W x y n 2 = (W.ψ n).evalEval x y := rfl
  exact ⟨by simpa only [e0, e1, e2] using (Jacobian.nonsingular_of_Z_ne_zero hz).mp hpt, rfl⟩

end Formula

namespace III

/-- **Lemma 3.14** (Milne, pdf p. 103), proved from Tau Ceti's multiplication formula: on
$Y^2 = X^3 + aX + b$ over a field of characteristic $\ne 2$, $nP = O$ when $\psi_n(P) = 0$, and otherwise
$nP = (x - \psi_{n-1}\psi_{n+1}/\psi_n^2,\ \psi_{2n}/2\psi_n^4)$. -/
@[kb "milne2006ec" "Ch. III, Lemma 3.14, pdf p. 103"]
theorem divisionPolynomialFormula : DivisionPolynomialFormula where
  smul_eq_zero k _ _ _ a b _ x y h n _ hψ := by
    have := zsmul_eq_zero_of_evalEval_ψ_eq_zero (shortCurve a b) h n hψ
    exact zsmul_fromAffine_eq_zero_iff.1 this
  smul_eq_some k _ _ h2 a b _ x y h n hn hψ := by
    obtain ⟨h', heq⟩ := zsmul_some_eq_of_evalEval_ψ_ne_zero (shortCurve a b) h n hψ
    have hx : ((shortCurve a b).φ n).evalEval x y /
          ((shortCurve a b).ψ n).evalEval x y ^ 2 =
        x - ((shortCurve a b).ψ (n - 1)).evalEval x y *
          ((shortCurve a b).ψ (n + 1)).evalEval x y /
          ((shortCurve a b).ψ n).evalEval x y ^ 2 := by
      rw [WeierstrassCurve.φ]
      simp only [evalEval, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
      field_simp
    have h2ω : 2 * ((shortCurve a b).ω n).evalEval x y =
        ((shortCurve a b).ψc n).evalEval x y := by
      have := congrArg (evalEval x y) ((shortCurve a b).two_mul_ω n)
      simp [shortCurve, evalEval] at this ⊢
      linear_combination this
    have hψc : ((shortCurve a b).ψ n).evalEval x y *
        ((shortCurve a b).ψc n).evalEval x y =
        ((shortCurve a b).ψ (2 * n)).evalEval x y := by
      rw [← evalEval_mul, (shortCurve a b).ψ_mul_ψc n]
    have hy : ((shortCurve a b).ω n).evalEval x y /
          ((shortCurve a b).ψ n).evalEval x y ^ 3 =
        ((shortCurve a b).ψ (2 * n)).evalEval x y /
          (2 * ((shortCurve a b).ψ n).evalEval x y ^ 4) := by
      rw [← hψc, ← h2ω]
      field_simp
    refine ⟨hx ▸ hy ▸ h', ?_⟩
    rw [← natCast_zsmul, heq]
    simp only [Affine.Point.some.injEq]
    exact ⟨hx, hy⟩

/-- **Proposition 3.13 in every characteristic** (Milne, pdf p. 103): for algebraically closed fields
$k \subseteq \Omega$ every torsion point of $E(\Omega)$ comes from $E(k)$.  The $x$-coordinate of an $n$-torsion point
is a root of $\Psi_n^2$, a nonzero polynomial over $k$ in every characteristic (Tau Ceti's
`ΨSq_ne_zero_of_Δ_ne_zero`), so it lies in $k$; then so does the $y$-coordinate. -/
@[kb "milne2006ec" "Ch. III, Prop. 3.13, pdf p. 103"]
theorem torsionBaseChange : TorsionBaseChange where
  bijective k Ω _ _ _ _ _ _ _ E _ Q hQ := by
    obtain ⟨n, hn, hnQ⟩ := hQ
    rcases Q with _ | ⟨x, y, hns⟩
    · exact ⟨0, map_zero _⟩
    have hΨ : ((E.baseChange Ω).ΨSq n).eval x = 0 :=
      (eval_ΨSq_eq_zero_iff_zsmul_eq_zero _ hns n).2 (zsmul_fromAffine_eq_zero_iff.2 hnQ)
    rw [WeierstrassCurve.baseChange, map_ΨSq] at hΨ
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have halg : IsAlgebraic k x :=
      ⟨E.ΨSq n, E.ΨSq_ne_zero_of_Δ_ne_zero E.isUnit_Δ.ne_zero hn0, by
        rwa [aeval_def, eval₂_eq_eval_map]⟩
    obtain ⟨x₀, rfl⟩ := algClosed_mem_range x halg
    obtain ⟨y₀, rfl⟩ := WeierstrassCurve.mem_range_y_of_equation_of_mem_range_x E hns.1 rfl
    have h₀ : E.toAffine.Nonsingular x₀ y₀ :=
      (WeierstrassCurve.Affine.map_nonsingular (W := E.toAffine) (f := algebraMap k Ω)
        (algebraMap k Ω).injective _ _).1 hns
    exact ⟨.some _ _ h₀, rfl⟩

end III

/-- **Lemma 2.1** (Milne, pdf p. 116), proved in every characteristic: for an elliptic curve over an
algebraically closed field and an integer $n \ne 0$, $P \mapsto nP$ is surjective on points.  For
$P = (x_0, y_0)$, the polynomial $\Phi_n - x_0 \Psi_n^2$ is monic of degree $n^2$ (Mathlib's `natDegree_Φ`,
`leadingCoeff_Φ`, `natDegree_ΨSq_le`), so it has a root $x_1$; coprimality of $\Phi_n$ and $\Psi_n^2$
(Tau Ceti's `isCoprime_Φ_ΨSq`) gives $\Psi_n^2(x_1) \ne 0$, and a point $Q$ over $x_1$ satisfies
$x(nQ) = x_0$ by the multiplication formula, so $nQ = P$ or $n(-Q) = P$. -/
@[kb "milne2006ec" "Ch. IV, Lemma 2.1, pdf p. 116"]
theorem lemma2_1 : Lemma2_1 where
  surjective k _ _ _ W _ n hn := by
    intro P
    rcases P with _ | ⟨x₀, y₀, h₀⟩
    · exact ⟨0, smul_zero n⟩
    have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
    set f : k[X] := W.Φ n - C x₀ * W.ΨSq n with hf
    have hpos : 0 < n.natAbs ^ 2 := pow_pos (Int.natAbs_pos.2 hn) 2
    have hlt : (C x₀ * W.ΨSq n).natDegree < (W.Φ n).natDegree := by
      rw [W.natDegree_Φ]
      calc (C x₀ * W.ΨSq n).natDegree ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
        _ ≤ n.natAbs ^ 2 - 1 := W.natDegree_ΨSq_le n
        _ < n.natAbs ^ 2 := by omega
    have hdeg : f.natDegree = n.natAbs ^ 2 := by
      rw [hf, natDegree_sub_eq_left_of_natDegree_lt hlt, W.natDegree_Φ]
    have hdeg0 : f.degree ≠ 0 :=
      (natDegree_pos_iff_degree_pos.mp (by omega)).ne'
    obtain ⟨x₁, hx₁⟩ := IsAlgClosed.exists_root f hdeg0
    have hx₁' : (W.Φ n).eval x₁ = x₀ * (W.ΨSq n).eval x₁ := by
      have := hx₁
      rw [IsRoot.def, hf, eval_sub, eval_mul, eval_C, sub_eq_zero] at this
      exact this
    obtain ⟨y₁, hy₁⟩ := Affine.exists_point_on_curve W.toAffine x₁
    have hns₁ : W.toAffine.Nonsingular x₁ y₁ := Affine.equation_iff_nonsingular.1 hy₁
    have hΨ : (W.ΨSq n).eval x₁ ≠ 0 := by
      intro h0
      have hΦ : (W.Φ n).eval x₁ = 0 := by rw [hx₁', h0, mul_zero]
      obtain ⟨a, b, hab⟩ := W.isCoprime_Φ_ΨSq n hΔ
      have := congrArg (eval x₁) hab
      simp [hΦ, h0] at this
    have hsq : (W.ψ n).evalEval x₁ y₁ ^ 2 = (W.ΨSq n).eval x₁ := by
      rw [evalEval_ψ_eq_evalEval_Ψ W hy₁ n, evalEval_Ψ_sq_eq_eval_ΨSq W hy₁ n]
    have hψ : (W.ψ n).evalEval x₁ y₁ ≠ 0 := fun h0 => hΨ (by rw [← hsq, h0]; ring)
    obtain ⟨h', heq⟩ := zsmul_some_eq_of_evalEval_ψ_ne_zero W hns₁ n hψ
    have hx : (W.φ n).evalEval x₁ y₁ / (W.ψ n).evalEval x₁ y₁ ^ 2 = x₀ := by
      rw [evalEval_φ_eq_eval_Φ W hy₁ n, hsq, div_eq_iff hΨ, hx₁']
    rcases Affine.Y_eq_of_X_eq h'.1 h₀.1 hx with hy | hy
    · refine ⟨Affine.Point.some x₁ y₁ hns₁, ?_⟩
      change n • Affine.Point.some x₁ y₁ hns₁ = _
      rw [heq]
      simp only [Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
    · refine ⟨-Affine.Point.some x₁ y₁ hns₁, ?_⟩
      change n • -Affine.Point.some x₁ y₁ hns₁ = _
      rw [smul_neg, heq, Affine.Point.neg_some]
      simp only [Affine.Point.some.injEq]
      refine ⟨hx, ?_⟩
      rw [hy, hx, Affine.negY_negY]

/-- The weak finite basis theorem with Lemma 2.1 proved (`lemma2_1`): for an elliptic curve over a number field and
$n \ne 0$, $E(K)/nE(K)$ is finite, given the Selmer finiteness `Thm3_1_Selmer` (a named statement). -/
@[kb "milne2006ec" "Ch. IV, introduction, Weak finite basis theorem, pdf p. 109"]
theorem weak_finite_basis_of_selmer (h31 : Thm3_1_Selmer) {K : Type} [Field K] [DecidableEq K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    Finite (W.toAffine.Point ⧸ multiples W.toAffine.Point n) :=
  weak_finite_basis K W lemma2_1 h31 n hn

/-- The Mordell–Weil theorem with Lemma 2.1 proved (`lemma2_1`): for an elliptic curve over a number field, $E(K)$ is
finitely generated, given the Selmer finiteness `Thm3_1_Selmer` (a named statement). -/
@[kb "milne2006ec" "Ch. IV, introduction, Finite basis theorem, pdf p. 109"]
theorem finite_basis_of_selmer (h31 : Thm3_1_Selmer) {K : Type} [Field K] [DecidableEq K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] : AddGroup.FG W.toAffine.Point :=
  finite_basis K W lemma2_1 h31

end NumberFieldKB.MilneEC
