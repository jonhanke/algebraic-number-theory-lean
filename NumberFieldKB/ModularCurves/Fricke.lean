import NumberFieldKB.ModularCurves.PlaneModel

/-!
# The Fricke symmetry of the modular polynomial
J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §2 and §4. The Fricke involution
$w_N : z \mapsto -1/(Nz)$ of $\mathbb H$ exchanges $j(z)$ and $j_N(z) = j(Nz)$:
$j(-1/(Nz)) = j(Nz)$ and $j(N \cdot (-1/(Nz))) = j(-1/z) = j(z)$. Hence the ring automorphism
$G(X, Y) \mapsto G(Y, X)$ of $\mathbb Q[X, Y]$ preserves the ideal of $(j, j_N)$, which is $(F_N)$
(`ker_evalJJNRat`), so $F_N(Y, X) = \pm F_N(X, Y)$, and $F_N(Y, X) = F_N(X, Y)$ for $N > 1$
(`swapQ_modPolyQ`). On the function field this gives the involution $w_N$ of $\mathbb Q(X_0(N))$,
$j \leftrightarrow j_N$ (an automorphism of the curve $X_0(N)$ over $\mathbb Q$).

Main results:
* `jFun_fricke`, `jN_fricke`: $j(w_N z) = j_N(z)$ and $j_N(w_N z) = j(z)$.
* `evalJJNRat_swapQ`: $(G(Y, X))(j, j_N)(z) = G(j, j_N)(w_N z)$.
* `swapQ_modPolyQ_eq_or`: $F_N(Y, X) = \pm F_N(X, Y)$; `swapQ_modPolyQ`: $F_N(Y, X) = F_N(X, Y)$ for $N > 1$.
-/

open UpperHalfPlane hiding I
open Polynomial
open scoped MatrixGroups

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-! ### The Fricke involution on $\mathbb H$ -/

theorem im_neg_one_div_pos (u : ℍ) : 0 < (-1 / (u : ℂ)).im := by
  simpa [neg_div, inv_neg, one_div] using u.im_inv_neg_coe_pos

/-- $j(-1/u) = j(u)$ ($S \in \mathrm{SL}_2(\mathbb Z)$). -/
theorem jFun_neg_inv (u : ℍ) : jFun (ofComplex (-1 / (u : ℂ))) = jFun u := by
  have h : ofComplex (-1 / (u : ℂ)) = ModularGroup.S • u := by
    rw [UpperHalfPlane.modular_S_smul, ofComplex_apply_of_im_pos (im_neg_one_div_pos u)]
    ext
    simp [neg_div, inv_neg, one_div]
  rw [h, jFun_smul]

/-- The Fricke involution $w_N(z) = -1/(Nz)$. -/
noncomputable def fricke (N : ℕ) (z : ℍ) : ℍ := ofComplex (-1 / ((N : ℂ) * z))

variable {N : ℕ}

theorem coe_ofComplex_mul (hN : 1 ≤ N) (z : ℍ) : ((ofComplex ((N : ℂ) * z) : ℍ) : ℂ) = (N : ℂ) * z := by
  have : 0 < ((N : ℂ) * z).im := by
    rw [Complex.mul_im]
    simpa using mul_pos (by exact_mod_cast hN : (0 : ℝ) < N) z.im_pos
  rw [ofComplex_apply_of_im_pos this]

theorem coe_fricke (hN : 1 ≤ N) (z : ℍ) : (fricke N z : ℂ) = -1 / ((N : ℂ) * z) := by
  have hw := coe_ofComplex_mul hN z
  unfold fricke
  rw [← hw, ofComplex_apply_of_im_pos (im_neg_one_div_pos _)]

/-- $j(w_N z) = j(Nz)$. -/
@[kb "milne2006ec" "Ch. V, §4, w_N exchanges j and j_N (j(-1/(Nz)) = j(Nz)), pdf p. 205"]
theorem jFun_fricke (hN : 1 ≤ N) (z : ℍ) : jFun (fricke N z) = jN N z := by
  have hw := coe_ofComplex_mul hN z
  unfold fricke jN
  set w := ofComplex ((N : ℂ) * z)
  rw [← hw, jFun_neg_inv]

/-- $j_N(w_N z) = j(z)$. -/
@[kb "milne2006ec" "Ch. V, §4, w_N exchanges j and j_N (j(N(-1/(Nz))) = j(z)), pdf p. 205"]
theorem jN_fricke (hN : 1 ≤ N) (z : ℍ) : jN N (fricke N z) = jFun z := by
  unfold jN
  rw [coe_fricke hN]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  rw [show (N : ℂ) * (-1 / ((N : ℂ) * z)) = -1 / (z : ℂ) by field_simp]
  exact jFun_neg_inv z

/-! ### The swap $G(X, Y) \mapsto G(Y, X)$ -/

/-- The ring endomorphism $G(X, Y) \mapsto G(Y, X)$ of $\mathbb Q[X][Y]$ (the inner variable is $X$). -/
noncomputable def swapQ : ℚ[X][X] →+* ℚ[X][X] :=
  eval₂RingHom (eval₂RingHom (C.comp C) X) (C X)

theorem swapQ_C_C (c : ℚ) : swapQ (C (C c)) = C (C c) := by simp [swapQ]

theorem swapQ_C_X : swapQ (C X) = X := by simp [swapQ]

theorem swapQ_X : swapQ X = C X := by simp [swapQ]

theorem swapQ_swapQ (G : ℚ[X][X]) : swapQ (swapQ G) = G := by
  have : swapQ.comp swapQ = RingHom.id _ := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext c; simp [swapQ]
      · simp [swapQ]
    · simp [swapQ]
  exact RingHom.congr_fun this G

/-- $G(Y, X)$ evaluated at $(j, j_N)$ is $G$ evaluated at $(j, j_N) \circ w_N$. -/
theorem evalJJNRat_swapQ (hN : 1 ≤ N) (G : ℚ[X][X]) (z : ℍ) :
    evalJJNRat N (swapQ G) z = evalJJNRat N G (fricke N z) := by
  have key : (Pi.evalRingHom (fun _ : ℍ => ℂ) z).comp ((evalJJNRat N).comp swapQ) =
      (Pi.evalRingHom (fun _ : ℍ => ℂ) (fricke N z)).comp (evalJJNRat N) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext c; simp [swapQ, evalJJNHom]
      · simp only [swapQ, evalJJNHom, RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_C,
          eval₂_X, Pi.evalRingHom_apply]
        exact (jFun_fricke hN z).symm
    · simp only [swapQ, evalJJNHom, RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_C,
        eval₂_X, Pi.evalRingHom_apply]
      exact (jN_fricke hN z).symm
  exact RingHom.congr_fun key G

/-- The diagonal $Y = X$ is fixed by the swap: $G(Y, X)$ and $G(X, Y)$ agree at $Y = X$. -/
theorem eval_X_swapQ (G : ℚ[X][X]) : (swapQ G).eval (X : ℚ[X]) = G.eval (X : ℚ[X]) := by
  have : (evalRingHom (X : ℚ[X])).comp swapQ = evalRingHom (X : ℚ[X]) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext c; simp [swapQ]
      · simp [swapQ]
    · simp [swapQ]
  exact RingHom.congr_fun this G

/-- The swap preserves the ideal of $(j, j_N)$. -/
theorem swapQ_mem_ker (hN : 1 ≤ N) {G : ℚ[X][X]} (hG : G ∈ RingHom.ker (evalJJNRat N)) :
    swapQ G ∈ RingHom.ker (evalJJNRat N) := by
  rw [RingHom.mem_ker] at hG ⊢
  funext z
  rw [evalJJNRat_swapQ hN, hG]
  rfl

/-- **$F_N(Y, X) = \pm F_N(X, Y)$.** -/
theorem swapQ_modPolyQ_eq_or (h : Prop2_4 N) (hN : 1 ≤ N) :
    swapQ (modPolyQ h) = modPolyQ h ∨ swapQ (modPolyQ h) = -modPolyQ h := by
  have hm := modPolyQ_monic h
  have hker : modPolyQ h ∈ RingHom.ker (evalJJNRat N) := by
    rw [ker_evalJJNRat h]; exact Ideal.subset_span rfl
  have hs := swapQ_mem_ker hN hker
  rw [ker_evalJJNRat h, Ideal.mem_span_singleton] at hs
  obtain ⟨a, ha⟩ := hs
  have h2 : modPolyQ h * (a * swapQ a) = modPolyQ h * 1 := by
    rw [mul_one]
    conv_rhs => rw [← swapQ_swapQ (modPolyQ h)]
    rw [ha, map_mul, ha, mul_assoc]
  have hau : a * swapQ a = 1 := mul_left_cancel₀ hm.ne_zero h2
  obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.1 (IsUnit.of_mul_eq_one _ hau)
  obtain ⟨c, -, rfl⟩ := Polynomial.isUnit_iff.1 hr
  rw [swapQ_C_C] at hau
  rcases mul_self_eq_one_iff.1 hau with h1 | h1
  · left; rw [ha, h1, mul_one]
  · right; rw [ha, h1]; ring

/-- $\Gamma_0(N) = \mathrm{SL}_2(\mathbb Z)$ only for $N = 1$. -/
theorem index_Gamma0_ne_one (hN : N ≠ 1) : (CongruenceSubgroup.Gamma0 N).index ≠ 1 := by
  intro h1
  rw [Subgroup.index_eq_one] at h1
  let U : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hU : U ∈ CongruenceSubgroup.Gamma0 N := h1 ▸ Subgroup.mem_top U
  rw [CongruenceSubgroup.Gamma0_mem] at hU
  have : ((1 : ℕ) : ZMod N) = 0 := by simpa [U] using hU
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hN (Nat.dvd_one.1 this)

/-- **Fricke symmetry of the modular polynomial**: $F_N(Y, X) = F_N(X, Y)$ for $N > 1$ ($F_1 = Y - X$ is
antisymmetric). -/
@[kb "milne2006ec" "Ch. V, §2/§4, F_N(X, Y) = F_N(Y, X) (w_N exchanges j and j_N), pdf pp. 193, 205"]
theorem swapQ_modPolyQ (h : Prop2_4 N) (hN : 1 < N) : swapQ (modPolyQ h) = modPolyQ h := by
  rcases swapQ_modPolyQ_eq_or h hN.le with h1 | h1
  · exact h1
  exfalso
  have hroot : (modPolyQ h).IsRoot X := by
    have := eval_X_swapQ (modPolyQ h)
    rw [h1, eval_neg] at this
    have h2 : (2 : ℚ[X]) * (modPolyQ h).eval X = 0 := by
      rw [two_mul]
      nth_rewrite 1 [← this]
      exact neg_add_cancel _
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.2 hroot
  rcases (irreducible_modPolyQ h hN.le).isUnit_or_isUnit hq with hu | hu
  · exact not_isUnit_X_sub_C _ hu
  · have hdeg := congrArg natDegree hq
    rw [natDegree_mul (X_sub_C_ne_zero _) hu.ne_zero, natDegree_X_sub_C, natDegree_eq_zero_of_isUnit hu,
      modPolyQ_natDegree] at hdeg
    exact index_Gamma0_ne_one (by omega) hdeg

/-! ### The involution $w_N$ of the plane model -/

/-- **The Fricke involution $w_N$ of the coordinate ring** $\mathbb Q[X, Y]/(F_N)$: $X \leftrightarrow Y$. -/
@[kb "milne2006ec" "Ch. V, §4, the involution w_N of X_0(N) defined over Q, pdf p. 205"]
noncomputable def frickeCoord (h : Prop2_4 N) (hN : 1 ≤ N) : coordRing h →+* coordRing h :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp swapQ) fun G hG => by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← ker_evalJJNRat h]
    rw [← ker_evalJJNRat h] at hG
    exact swapQ_mem_ker hN hG

theorem frickeCoord_mk (h : Prop2_4 N) (hN : 1 ≤ N) (G : ℚ[X][X]) :
    frickeCoord h hN (Ideal.Quotient.mk _ G) = Ideal.Quotient.mk _ (swapQ G) := rfl

/-- $w_N$ is an involution. -/
theorem frickeCoord_frickeCoord (h : Prop2_4 N) (hN : 1 ≤ N) (x : coordRing h) :
    frickeCoord h hN (frickeCoord h hN x) = x := by
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [frickeCoord_mk, frickeCoord_mk, swapQ_swapQ]

/-- **Analytic comparison for $w_N$**: under $\mathbb Q[X, Y]/(F_N) \cong \mathbb Q[j, j_N]$, the involution $w_N$ is
composition with $z \mapsto -1/(Nz)$. -/
@[kb "milne2006ec" "Ch. V, §4, w_N acts on functions by z ↦ -1/(Nz), pdf p. 205"]
theorem coordRingEquiv_frickeCoord (h : Prop2_4 N) (hN : 1 ≤ N) (x : coordRing h) :
    (coordRingEquiv h (frickeCoord h hN x) : ℍ → ℂ) = (coordRingEquiv h x : ℍ → ℂ) ∘ fricke N := by
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [frickeCoord_mk, coordRingEquiv_mk, coordRingEquiv_mk]
  funext z
  exact evalJJNRat_swapQ hN G z

end NumberFieldKB.ModularCurves
