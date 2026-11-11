import NumberFieldKB.MilneEC.Ch5ModularForms
import NumberFieldKB.MilneEC.Ch5Fricke
import NumberFieldKB.MilneEC.Ch5FiniteDim
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Star.Int

/-!
# Milne, *Elliptic Curves*, Chapter V, Exercise 1.10 (b), (c)

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Exercise 1.10 (pdf p. 188): $\Delta(Nz)$ and
the weight-two cusp form $q\prod(1-q^n)^2(1-q^{11n})^2$ of level $11$.
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold Pointwise Modular ArithmeticFunction.sigma

namespace NumberFieldKB.MilneEC.V

/-- The matrix $\operatorname{diag}(N, 1) \in \mathrm{GL}_2(\mathbb R)$. -/
noncomputable def gDiag (N : ℕ) (hN : 1 ≤ N) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(N : ℝ), 0; 0, 1] (by
    simp [Matrix.det_fin_two]; omega)

/-- The underlying matrix of `gDiag`. -/
lemma gDiag_val (N : ℕ) (hN : 1 ≤ N) : ((gDiag N hN : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(N : ℝ), 0; 0, 1] := by
  simp [gDiag]

/-- The determinant of `gDiag N` is $N$. -/
lemma gDiag_det (N : ℕ) (hN : 1 ≤ N) : (gDiag N hN).det.val = N := by
  simp [Matrix.GeneralLinearGroup.det, gDiag_val, Matrix.det_fin_two]

/-- The conjugation twist `σ` of `gDiag N` is the identity (positive determinant). -/
lemma gDiag_σ (N : ℕ) (hN : 1 ≤ N) (w : ℂ) : UpperHalfPlane.σ (gDiag N hN) w = w := by
  have : 0 < (gDiag N hN).det.val := by
    rw [gDiag_det]; exact_mod_cast hN
  simp only [UpperHalfPlane.σ]
  split_ifs
  rfl

/-- The Möbius action of `gDiag N` is $z \mapsto Nz$. -/
lemma gDiag_smul (N : ℕ) (hN : 1 ≤ N) (z : ℍ) :
    ((gDiag N hN • z : ℍ) : ℂ) = N * z := by
  rw [UpperHalfPlane.coe_smul]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, gDiag_val, gDiag_σ]

/-- Weight $12$ slash action of `gDiag N`: $(f \mid g)(z) = N^{11}f(Nz)$. -/
lemma gDiag_slash (N : ℕ) (hN : 1 ≤ N) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[(12:ℤ)] gDiag N hN) z = (N : ℂ) ^ 11 * f (gDiag N hN • z) := by
  rw [ModularForm.slash_apply, gDiag_σ, gDiag_det]
  have : denom (gDiag N hN) z = 1 := by
    simp [UpperHalfPlane.denom, gDiag_val]
  rw [this]
  have h0 : (|(N:ℝ)| : ℝ) = N := abs_of_nonneg (by positivity)
  rw [h0]
  simp
  ring

/-- $\Gamma_0(N) \subseteq g^{-1}\,\mathrm{SL}_2(\mathbb Z)\,g$ for $g = \mathrm{diag}(N,1)$. -/
lemma le_conj (N : ℕ) (hN : 1 ≤ N) :
    Gamma0GL N ≤ ConjAct.toConjAct (gDiag N hN)⁻¹ • 𝒮ℒ := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  have hc : (N : ℤ) ∣ γ 1 0 := by
    have := CongruenceSubgroup.Gamma0_mem.mp hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  obtain ⟨m, hm⟩ := hc
  have hdet : (!![γ 0 0, N * γ 0 1; m, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this ⊢
    simp
    rw [hm] at this
    linarith
  refine ⟨⟨!![γ 0 0, N * γ 0 1; m, γ 1 1], hdet⟩, ?_⟩
  · rw [eq_mul_inv_iff_mul_eq]
    have hm' : ((γ 1 0 : ℤ) : ℝ) = N * m := by exact_mod_cast hm
    have e00 : (((mapGL ℝ) (⟨!![γ 0 0, N * γ 0 1; m, γ 1 1], hdet⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (γ 0 0 : ℝ) := rfl
    have e01 : (((mapGL ℝ) (⟨!![γ 0 0, N * γ 0 1; m, γ 1 1], hdet⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = (N : ℝ) * (γ 0 1 : ℝ) := by
      show (((N * γ 0 1 : ℤ)) : ℝ) = _
      push_cast; rfl
    have e10 : (((mapGL ℝ) (⟨!![γ 0 0, N * γ 0 1; m, γ 1 1], hdet⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = (m : ℝ) := rfl
    have e11 : (((mapGL ℝ) (⟨!![γ 0 0, N * γ 0 1; m, γ 1 1], hdet⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (γ 1 1 : ℝ) := rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e00, e01, e10, e11, gDiag_val, Matrix.mul_apply, Fin.sum_univ_two, hm', Matrix.SpecialLinearGroup.mapGL_coe_matrix] <;> ring

/-- `ofComplex (N z)` is `gDiag N • z`. -/
lemma ofComplex_N (N : ℕ) (hN : 1 ≤ N) (z : ℍ) : ofComplex ((N : ℂ) * z) = gDiag N hN • z := by
  have h : 0 < ((N : ℂ) * z).im := by
    simp
    exact mul_pos (by exact_mod_cast hN) z.im_pos
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos h, gDiag_smul]

/-- **Exercise 1.10** (b) (pdf p. 188), for every level $N \ge 1$: $\Delta_N(z) = \Delta(Nz)$ is a cusp form of
weight $12$ for $\Gamma_0(N)$. -/
@[kb "milne2006ec" "Ch. V, Exercise 1.10 (b), pdf p. 188"]
theorem exercise_1_10_b {N : ℕ} (hN : 1 ≤ N) :
    ∃ F : CuspForm (Gamma0GL N) 12, ⇑F = fun z : ℍ ↦ discr (ofComplex ((N : ℂ) * z)) := by
  obtain ⟨F0, hF0⟩ := prop_3_5_discr
  refine ⟨((N : ℂ) ^ (-11 : ℤ)) • CuspForm.restrict (le_conj N hN) (CuspForm.translate F0 (gDiag N hN)), ?_⟩
  funext z
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, CuspForm.restrict, CuspForm.coe_translate]
  change (N : ℂ) ^ (-11 : ℤ) * ((⇑F0 ∣[(12:ℤ)] gDiag N hN) z) = _
  rw [gDiag_slash, hF0, ofComplex_N N hN z, zpow_neg]
  field_simp

/-- **Exercise 1.10** (b) (pdf p. 188): $\Delta\cdot\Delta_{11}$ is a cusp form of weight $24$ for
$\Gamma_0(11)$. -/
@[kb "milne2006ec" "Ch. V, Exercise 1.10 (b), pdf p. 188"]
theorem exercise_1_10_b' :
    ∃ F : CuspForm (Gamma0GL 11) 24, ⇑F = fun z : ℍ ↦ discr z * discr (ofComplex (11 * (z : ℂ))) := by
  obtain ⟨F0, hF0⟩ := prop_3_5_discr
  obtain ⟨F1, hF1⟩ := exercise_1_10_b (N := 11) (by norm_num)
  have hle : Gamma0GL 11 ≤ 𝒮ℒ := by
    rintro x ⟨γ, -, rfl⟩
    exact ⟨γ, rfl⟩
  refine ⟨CuspForm.mcast (by norm_num) ((CuspForm.restrict hle F0).mulModularForm (F1 : ModularForm (Gamma0GL 11) 12)), ?_⟩
  funext z
  have h0 : F0 z = discr z := congrFun hF0 z
  have h1 : F1 z = discr (ofComplex (11 * (z : ℂ))) := by
    have := congrFun hF1 z
    simpa using this
  change F0 z * F1 z = _
  rw [h0, h1]

/-! ### Exercise 1.10 (c): auxiliary lemmas

Plan (Milne's hint): for a nonzero $f \in S_2(\Gamma_0(11))$ and $g = \Delta\cdot\Delta_{11}$ (part (b')),
$\varphi = f^{12}/g$ is a modular form of weight $0$ for $\Gamma_0(11)$, hence constant. Boundedness at the cusps
reduces (`ex110_SL2Z_cases`) to the cusps $\infty$ (`ex110_bound_infty`) and $0$ (`ex110_bound_S`, through the
Fricke transform of $f$). Then $F = \eta(z)^2\eta(11z)^2$ (`ex110_prod_eq_eta`) satisfies
$F^{12} = g/(2\pi)^{24}$ (`ex110_eta_pow`), so $F/f$ is continuous with values in a finite set of $12$-th roots,
hence constant on the connected upper half plane. -/

/-- Elementary estimate: if $0 \le a \le Ce$, $b_i \ge ce_i$ with $c > 0$, and $e^{12} = e_1e_2$, then
$a^{12}/(b_1b_2) \le C^{12}/c^2$. -/
lemma ex110_bound_aux {a b1 b2 C c e e1 e2 : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ C * e) (hc : 0 < c)
    (he : 0 < e) (he1 : 0 < e1) (he2 : 0 < e2) (hb1 : c * e1 ≤ b1) (hb2 : c * e2 ≤ b2)
    (hE : e ^ 12 = e1 * e2) : a ^ 12 / (b1 * b2) ≤ C ^ 12 / c ^ 2 := by
  have hC : 0 ≤ C := le_of_mul_le_mul_right (by simpa using ha0.trans ha) he
  have h1 : a ^ 12 ≤ C ^ 12 * (e1 * e2) := by
    rw [← hE, ← mul_pow]; exact pow_le_pow_left₀ ha0 ha 12
  have hb1p : 0 < b1 := lt_of_lt_of_le (mul_pos hc he1) hb1
  have hb2p : 0 < b2 := lt_of_lt_of_le (mul_pos hc he2) hb2
  have h2 : c ^ 2 * (e1 * e2) ≤ b1 * b2 := by
    have := mul_le_mul hb1 hb2 (by positivity) hb1p.le
    nlinarith
  rw [div_le_div_iff₀ (mul_pos hb1p hb2p) (by positivity)]
  calc a ^ 12 * c ^ 2 ≤ C ^ 12 * (e1 * e2) * c ^ 2 := by gcongr
    _ = C ^ 12 * (c ^ 2 * (e1 * e2)) := by ring
    _ ≤ C ^ 12 * (b1 * b2) := by gcongr

/-- A cusp form of level $\Gamma_0(N)$ is $O(e^{-2\pi\Im\tau})$ at infinity, with explicit constants. -/
lemma ex110_cuspForm_exp_bound {N : ℕ} {k : ℤ} (F : CuspForm (Gamma0GL N) k) :
    ∃ C A : ℝ, ∀ τ : ℍ, A ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-2 * π * τ.im) := by
  have h := CuspFormClass.exp_decay_atImInfty F one_pos (one_mem_strictPeriods_Gamma0GL (N := N))
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 hC
  refine ⟨C, A, fun τ hτ => ?_⟩
  have := hA τ hτ
  simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using this

/-- $|\Delta(\tau)| \ge c\,e^{-2\pi\Im\tau}$ for $\Im\tau$ large (from Mathlib's `exp_isBigO_discriminant`). -/
lemma ex110_discr_lower_bound : ∃ c > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im →
    c * Real.exp (-2 * π * τ.im) ≤ ‖discr τ‖ := by
  obtain ⟨K, hK, hKw⟩ := ModularForm.exp_isBigO_discriminant.exists_pos
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 hKw.bound
  refine ⟨K⁻¹ * (2 * π) ^ 12, by positivity, A, fun τ hτ => ?_⟩
  have h1 : Real.exp (-2 * π * τ.im) ≤ K * ‖ModularForm.discriminant τ‖ := by
    have := hA τ hτ
    simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using this
  have h2 : ‖discr τ‖ = (2 * π) ^ 12 * ‖ModularForm.discriminant τ‖ := by
    rw [discr_eq, norm_mul, norm_pow, norm_mul]
    simp [abs_of_pos Real.pi_pos]
  rw [h2]
  have : K⁻¹ * Real.exp (-2 * π * τ.im) ≤ ‖ModularForm.discriminant τ‖ := by
    rw [inv_mul_le_iff₀ hK]; exact h1
  calc K⁻¹ * (2 * π) ^ 12 * Real.exp (-2 * π * τ.im)
      = (2 * π) ^ 12 * (K⁻¹ * Real.exp (-2 * π * τ.im)) := by ring
    _ ≤ _ := by gcongr

/-- Slash invariance of weight $w$ under $\gamma \in \mathrm{SL}_2(\mathbb Z)$ as the transformation law
$f(\gamma z) = (cz+d)^w f(z)$. -/
lemma ex110_smul_eq_of_slash_eq {w : ℕ} {f : ℍ → ℂ} {γ : SL(2, ℤ)} (h : f ∣[(w : ℤ)] mapGL ℝ γ = f)
    (z : ℍ) : f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ w * f z := by
  have h1 := congrFun h z
  rw [slash_mapGL_apply, zpow_neg, zpow_natCast] at h1
  rw [← h1, mul_inv_cancel_left₀ (pow_ne_zero _ (denom_aux γ z))]

/-- $\Delta(\gamma z) = (cz+d)^{12}\Delta(z)$ for $\gamma \in \mathrm{SL}_2(\mathbb Z)$. -/
lemma ex110_discr_SL_smul (γ : SL(2, ℤ)) (z : ℍ) :
    discr (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ 12 * discr z := by
  obtain ⟨F0, hF0⟩ := prop_3_5_discr
  have h : (⇑F0 ∣[((12 : ℕ) : ℤ)] mapGL ℝ γ) = ⇑F0 := F0.slash_action_eq' (mapGL ℝ γ) ⟨γ, rfl⟩
  rw [hF0] at h
  exact ex110_smul_eq_of_slash_eq (w := 12) h z

/-- Every $\gamma \in \mathrm{SL}_2(\mathbb Z)$ lies in $\Gamma_0(11)$ or equals $\delta ST^j$ with
$\delta \in \Gamma_0(11)$ (the two cusps $\infty$ and $0$ of $\Gamma_0(11)$). -/
lemma ex110_SL2Z_cases (γ : SL(2, ℤ)) : γ ∈ CongruenceSubgroup.Gamma0 11 ∨
    ∃ δ ∈ CongruenceSubgroup.Gamma0 11, ∃ j : ℤ, γ = δ * (ModularGroup.S * ModularGroup.T ^ j) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  by_cases hc : ((γ 1 0 : ℤ) : ZMod 11) = 0
  · exact Or.inl (CongruenceSubgroup.Gamma0_mem.2 hc)
  right
  set j : ℤ := ((((γ 1 1 : ℤ) : ZMod 11) * ((γ 1 0 : ℤ) : ZMod 11)⁻¹).val : ℤ) with hj
  refine ⟨γ * (ModularGroup.S * ModularGroup.T ^ j)⁻¹, ?_, j, by group⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  have hjc : ((j : ℤ) : ZMod 11) = ((γ 1 1 : ℤ) : ZMod 11) * ((γ 1 0 : ℤ) : ZMod 11)⁻¹ := by
    rw [hj]; simp
  have e : ((γ * (ModularGroup.S * ModularGroup.T ^ j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = γ 1 0 * j - γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ModularGroup.coe_S,
      ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [e]
  push_cast
  rw [hjc]
  field_simp
  ring

section Fricke

variable {N : ℕ} [NeZero N]

/-- $\alpha_N z = -1/(Nz)$ as complex numbers. -/
lemma coe_alphaN_smul (z : ℍ) : ((alphaN N • z : ℍ) : ℂ) = -1 / ((N : ℂ) * z) := by
  rw [alphaN_smul, coe_ofComplex_alphaN]

/-- The Fricke transform $z \mapsto Nf(-1/(Nz))/(Nz)^2$ of a cusp form of weight two for $\Gamma_0(N)$ is again
one. -/
lemma ex110_fricke_cuspForm (f : CuspForm (Gamma0GL N) 2) :
    ∃ W : CuspForm (Gamma0GL N) 2, ∀ z, W z = N * f (alphaN N • z) / ((N : ℂ) * z) ^ 2 := by
  obtain ⟨W, hW⟩ := wN_cuspForm (N := N) 1 f
  refine ⟨W, fun z => ?_⟩
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hs : ((Real.sqrt N : ℂ)) ^ 2 = N := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; simp
  rw [hW, wN, alphaN_smul, mul_zpow, show (-(2 * ((1 : ℕ) : ℤ))) = -((2 : ℕ) : ℤ) by norm_num]
  simp only [zpow_neg, zpow_natCast]
  rw [mul_pow, hs]
  field_simp

end Fricke

/-- $e^{2\pi i\cdot 11z} = (e^{2\pi iz})^{11}$. -/
lemma ex110_q_pow (z : ℂ) : cexp (2 * π * I * (11 * z)) = cexp (2 * π * I * z) ^ 11 := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- $11z$ lies in the upper half plane. -/
lemma ex110_mem_eleven (z : ℍ) : (11 * (z : ℂ)) ∈ upperHalfPlaneSet := by
  show 0 < (11 * (z : ℂ)).im
  simpa using z.im_pos

/-- The product $q\prod_{n\ge1}(1-q^n)^2(1-q^{11n})^2$ is $\eta(z)^2\eta(11z)^2$ (Mathlib's Dedekind eta). -/
lemma ex110_prod_eq_eta (z : ℍ) : cexp (2 * π * I * z) *
      ∏' n : ℕ, ((1 - cexp (2 * π * I * z) ^ (n + 1)) ^ 2 * (1 - cexp (2 * π * I * z) ^ (11 * (n + 1))) ^ 2) =
    η z ^ 2 * η (11 * z) ^ 2 := by
  have m1 := multipliableLocallyUniformlyOn_eta.multipliable z.2
  have m2 := multipliableLocallyUniformlyOn_eta.multipliable (ex110_mem_eleven z)
  have e : (fun n : ℕ => (1 - cexp (2 * π * I * z) ^ (n + 1)) ^ 2 *
      (1 - cexp (2 * π * I * z) ^ (11 * (n + 1))) ^ 2) =
      fun n => (1 - eta_q n z) ^ 2 * (1 - eta_q n (11 * z)) ^ 2 := by
    funext n
    rw [eta_q_eq_pow, eta_q_eq_pow, ex110_q_pow, ← pow_mul]
  rw [e, (m1.pow 2).tprod_mul (m2.pow 2), m1.tprod_pow, m2.tprod_pow]
  have hq : cexp (2 * π * I * z) = Function.Periodic.qParam 24 z ^ 2 *
      Function.Periodic.qParam 24 (11 * z) ^ 2 := by
    simp only [Function.Periodic.qParam, sq, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hq]
  simp only [ModularForm.eta]
  ring

/-- $\bigl(\eta(z)^2\eta(11z)^2\bigr)^{12} = \Delta(z)\Delta(11z)/(2\pi)^{24}$ (Milne's $\Delta$). -/
lemma ex110_eta_pow (z : ℍ) : (η z ^ 2 * η (11 * z) ^ 2) ^ 12 =
    discr z * discr (ofComplex (11 * (z : ℂ))) / (2 * π) ^ 24 := by
  have hv : ((ofComplex (11 * (z : ℂ)) : ℍ) : ℂ) = 11 * z := by
    rw [ofComplex_apply_of_im_pos (ex110_mem_eleven z)]
  rw [discr_eq, discr_eq]
  simp only [ModularForm.discriminant, hv]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- $z \mapsto \eta(z)^2\eta(11z)^2$ is continuous on the upper half plane. -/
lemma ex110_eta_cont : Continuous fun z : ℍ => η z ^ 2 * η (11 * z) ^ 2 := by
  rw [continuous_iff_continuousAt]
  intro z
  have h1 : ContinuousAt (fun z : ℍ => η (z : ℂ)) z :=
    (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2).continuousAt.comp
      continuous_coe.continuousAt
  have h2 : ContinuousAt (fun z : ℍ => η (11 * (z : ℂ))) z :=
    (differentiableAt_eta_of_mem_upperHalfPlaneSet (ex110_mem_eleven z)).continuousAt.comp
      (f := fun z : ℍ => 11 * (z : ℂ)) (by fun_prop : Continuous fun z : ℍ => 11 * (z : ℂ)).continuousAt
  exact (h1.pow 2).mul (h2.pow 2)

/-- $\Delta(-1/z) = z^{12}\Delta(z)$. -/
lemma ex110_discr_S (z : ℍ) : discr (ModularGroup.S • z) = (z : ℂ) ^ 12 * discr z := by
  rw [ex110_discr_SL_smul]; simp [ModularGroup.coe_S]

/-- At the cusp $\infty$: $f^{12}/(\Delta\cdot\Delta_{11})$ is bounded for a cusp form $f$ of weight two for
$\Gamma_0(11)$ (both sides decay like $e^{-24\pi\Im z}$). -/
lemma ex110_bound_infty (f : CuspForm (Gamma0GL 11) 2) : ∃ M A : ℝ, ∀ z : ℍ, A ≤ z.im →
    ‖f z ^ 12 / (discr z * discr (ofComplex (11 * (z : ℂ))))‖ ≤ M := by
  obtain ⟨C, A1, hC⟩ := ex110_cuspForm_exp_bound f
  obtain ⟨c, hc, A2, hc2⟩ := ex110_discr_lower_bound
  refine ⟨C ^ 12 / c ^ 2, max A1 (max A2 0), fun z hz => ?_⟩
  obtain ⟨hz1, hz2, hz3⟩ : A1 ≤ z.im ∧ A2 ≤ z.im ∧ 0 ≤ z.im := by
    simpa [max_le_iff] using hz
  have hv : ((ofComplex (11 * (z : ℂ)) : ℍ) : ℂ) = 11 * z := by
    rw [ofComplex_apply_of_im_pos (ex110_mem_eleven z)]
  set v := ofComplex (11 * (z : ℂ))
  have hvim : v.im = 11 * z.im := by
    have := congrArg Complex.im hv; simpa using this
  rw [norm_div, norm_pow, norm_mul]
  refine ex110_bound_aux (norm_nonneg _) (hC z hz1) hc (Real.exp_pos _) (Real.exp_pos _)
    (Real.exp_pos _) (hc2 z hz2) (hc2 v (by rw [hvim]; linarith)) ?_
  rw [hvim, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring

/-- At the cusp $0$: $f^{12}/(\Delta\cdot\Delta_{11})$ composed with $S$ is bounded (it equals
$W(z/11)^{12}/(\Delta(z)\Delta(z/11))$ for the Fricke transform $W$ of $f$; both decay like
$e^{-24\pi\Im z/11}$). -/
lemma ex110_bound_S (f : CuspForm (Gamma0GL 11) 2) : ∃ M A : ℝ, ∀ w : ℍ, A ≤ w.im →
    ‖f (ModularGroup.S • w) ^ 12 / (discr (ModularGroup.S • w) *
      discr (ofComplex (11 * ((ModularGroup.S • w : ℍ) : ℂ))))‖ ≤ M := by
  obtain ⟨W, hW⟩ := ex110_fricke_cuspForm (N := 11) f
  obtain ⟨C, A1, hC⟩ := ex110_cuspForm_exp_bound W
  obtain ⟨c, hc, A2, hc2⟩ := ex110_discr_lower_bound
  refine ⟨C ^ 12 / c ^ 2, max (11 * A1) (max (11 * A2) A2), fun w hw => ?_⟩
  obtain ⟨hw1, hw2, hw3⟩ : 11 * A1 ≤ w.im ∧ 11 * A2 ≤ w.im ∧ A2 ≤ w.im := by
    simpa [max_le_iff] using hw
  let u : ℍ := ⟨(w : ℂ) / 11, by simpa using w.im_pos⟩
  have hu : (u : ℂ) = w / 11 := rfl
  have huim : u.im = w.im / 11 := by
    show ((w : ℂ) / 11).im = _; simp
  have hw0 : (w : ℂ) ≠ 0 := w.ne_zero
  have hSw : ((ModularGroup.S • w : ℍ) : ℂ) = -1 / w := by
    rw [modular_S_smul]; change (-(w : ℂ))⁻¹ = _; field_simp
  have hSu : ((ModularGroup.S • u : ℍ) : ℂ) = -1 / (w / 11) := by
    rw [modular_S_smul]; change (-(u : ℂ))⁻¹ = _; rw [hu]; field_simp
  have hαu : alphaN 11 • u = ModularGroup.S • w := by
    apply UpperHalfPlane.ext
    rw [coe_alphaN_smul, hSw, hu]; push_cast; field_simp
  have hOf : ofComplex (11 * ((ModularGroup.S • w : ℍ) : ℂ)) = ModularGroup.S • u := by
    have : (11 : ℂ) * ((ModularGroup.S • w : ℍ) : ℂ) = ((ModularGroup.S • u : ℍ) : ℂ) := by
      rw [hSw, hSu]; field_simp
    rw [this, ofComplex_apply]
  have hfS : f (ModularGroup.S • w) = W u * ((w : ℂ) ^ 2 / 11) := by
    rw [hW u, hαu, hu]; push_cast; field_simp
  have key : f (ModularGroup.S • w) ^ 12 / (discr (ModularGroup.S • w) *
      discr (ofComplex (11 * ((ModularGroup.S • w : ℍ) : ℂ)))) = W u ^ 12 / (discr w * discr u) := by
    rw [hfS, hOf, ex110_discr_S, ex110_discr_S, hu]
    have h1 := discr_ne_zero w
    have h2 := discr_ne_zero u
    field_simp
  rw [key, norm_div, norm_pow, norm_mul]
  refine ex110_bound_aux (norm_nonneg _) (hC u (by rw [huim]; linarith)) hc (Real.exp_pos _)
    (Real.exp_pos _) (Real.exp_pos _) (hc2 w hw3) (hc2 u (by rw [huim]; linarith)) ?_
  rw [huim, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring

/-- **Exercise 1.10** (c) (pdf p. 188): assuming $\dim S_2(\Gamma_0(11)) = 1$ (part of the named statement
`DimS2Small`; Jacobi's formula is `thm_3_7`), $F(z) = q\prod_{n\ge1}(1-q^n)^2(1-q^{11n})^2$ is a cusp form of
weight $2$ for $\Gamma_0(11)$. -/
@[kb "milne2006ec" "Ch. V, Exercise 1.10 (c), pdf p. 188"]
theorem exercise_1_10_c (h : DimS2Small) :
    ∃ F : CuspForm (Gamma0GL 11) 2, ∀ z : ℍ, F z = cexp (2 * π * I * z) *
      ∏' n : ℕ, ((1 - cexp (2 * π * I * z) ^ (n + 1)) ^ 2 * (1 - cexp (2 * π * I * z) ^ (11 * (n + 1))) ^ 2) := by
  -- a nonzero cusp form `f` and the weight 24 cusp form `G = Δ·Δ₁₁`
  obtain ⟨f, hf0⟩ : ∃ f : CuspForm (Gamma0GL 11) 2, f ≠ 0 := by
    have : 0 < Module.rank ℂ (CuspForm (Gamma0GL 11) 2) := by rw [h.eq_one]; exact zero_lt_one
    exact rank_pos_iff_exists_ne_zero.1 this
  obtain ⟨G, hG⟩ := exercise_1_10_b'
  have hGz : ∀ z, G z = discr z * discr (ofComplex (11 * (z : ℂ))) := fun z => congrFun hG z
  have hG0 : ∀ z, G z ≠ 0 := fun z => by
    rw [hGz]; exact mul_ne_zero (discr_ne_zero _) (discr_ne_zero _)
  have hfinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 11, ∀ z : ℍ,
      f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 * f z := by
    intro γ hγ z
    have h1 : (⇑f ∣[((2 : ℕ) : ℤ)] mapGL ℝ γ) = ⇑f := f.slash_action_eq' (mapGL ℝ γ) ⟨γ, hγ, rfl⟩
    exact ex110_smul_eq_of_slash_eq h1 z
  have hGinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 11, ∀ z : ℍ,
      G (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ 24 * G z := by
    intro γ hγ z
    have h1 : (⇑G ∣[((24 : ℕ) : ℤ)] mapGL ℝ γ) = ⇑G := G.slash_action_eq' (mapGL ℝ γ) ⟨γ, hγ, rfl⟩
    exact ex110_smul_eq_of_slash_eq h1 z
  -- `φ = f^12/G` is a modular form of weight 0, hence constant
  set φ : ℍ → ℂ := fun z => f z ^ 12 / G z with hφ
  have hφinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 11, ∀ z : ℍ, φ (γ • z) = φ z := by
    intro γ hγ z
    simp only [hφ]
    rw [hfinv γ hγ z, hGinv γ hγ z, mul_pow, ← pow_mul]
    have := denom_aux γ z
    have := hG0 z
    field_simp
  obtain ⟨M1, A1, h1⟩ := ex110_bound_infty f
  obtain ⟨M2, A2, h2⟩ := ex110_bound_S f
  have hbdd : ∀ γ : SL(2, ℤ), IsBoundedAtImInfty fun z => φ (γ • z) := by
    intro γ
    rw [isBoundedAtImInfty_iff]
    rcases ex110_SL2Z_cases γ with hγ | ⟨δ, hδ, j, rfl⟩
    · refine ⟨M1, A1, fun z hz => ?_⟩
      rw [hφinv γ hγ]
      simpa [hφ, hGz] using h1 z hz
    · refine ⟨M2, A2, fun z hz => ?_⟩
      rw [mul_smul, hφinv δ hδ, mul_smul]
      have him : (ModularGroup.T ^ j • z).im = z.im := by
        rw [modular_T_zpow_smul]; simp
      have hz' : A2 ≤ (ModularGroup.T ^ j • z).im := by rw [him]; exact hz
      have := h2 _ hz'
      simp only [hφ, hGz]
      exact this
  have hMilne : IsModularFormMilne (CongruenceSubgroup.Gamma0 11) 0 φ := by
    refine ⟨?_, ?_, ?_⟩
    · exact (f.holo'.pow 12).div G.holo' hG0
    · intro γ hγ z
      rw [hφinv γ hγ z]
      simp
    · intro γ
      simpa using hbdd γ
  obtain ⟨Φ, hΦ⟩ := (def_3_1 _ 0 φ).1 hMilne
  obtain ⟨c0, hc0⟩ := modularForm_weight_zero_const _ Φ
  have hf12 : ∀ z, f z ^ 12 = c0 * G z := by
    intro z
    have : φ z = c0 := by rw [← hΦ, hc0]; rfl
    simp only [hφ] at this
    rw [← this]
    field_simp [hG0 z]
  have hc00 : c0 ≠ 0 := by
    intro h0
    apply hf0
    ext z
    have := hf12 z
    rw [h0, zero_mul] at this
    simpa using this
  have hfnz : ∀ z, f z ≠ 0 := by
    intro z hz
    have := hf12 z
    rw [hz, zero_pow (by norm_num)] at this
    exact mul_ne_zero hc00 (hG0 z) this.symm
  -- `P = η(z)²η(11z)²` satisfies `(P/f)^12 = K`, so the continuous `P/f` is constant
  set P : ℍ → ℂ := fun z => η z ^ 2 * η (11 * z) ^ 2 with hP
  set K : ℂ := 1 / ((2 * π : ℂ) ^ 24 * c0) with hK
  have hr12 : ∀ z, (P z / f z) ^ 12 = K := by
    intro z
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [div_pow, hP, ex110_eta_pow, ← hGz, hf12, hK]
    have := hG0 z
    field_simp
  have hrcont : Continuous fun z => P z / f z :=
    ex110_eta_cont.div f.holo'.continuous hfnz
  have hfin : {x : ℂ | x ^ 12 = K}.Finite :=
    (Polynomial.nthRoots 12 K).toFinset.finite_toSet.subset
      (fun x hx => by simpa [Polynomial.mem_nthRoots] using hx)
  let z0 : ℍ := ⟨Complex.I, by simp⟩
  have hconst : ∀ z, P z / f z = P z0 / f z0 := fun z =>
    isPreconnected_univ.constant_of_mapsTo hfin.isDiscrete hrcont.continuousOn
      (fun x _ => hr12 x) (Set.mem_univ z) (Set.mem_univ z0)
  refine ⟨(P z0 / f z0) • f, fun z => ?_⟩
  rw [ex110_prod_eq_eta z, smul_apply, ← hconst z, smul_eq_mul]
  have := hfnz z
  simp only [hP]
  field_simp

end NumberFieldKB.MilneEC.V
