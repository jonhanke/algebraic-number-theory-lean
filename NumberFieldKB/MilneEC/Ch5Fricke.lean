import NumberFieldKB.MilneEC.Ch5LSeries
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Int

/-!
# Milne, *Elliptic Curves*, Chapter V §4: the involution $w_N$ and Hecke's functional equation

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §4, pdf p. 205: $w_N$ and Theorem 4.4,
proved from Mathlib's functional equation for the `WeakFEPair` of a cusp form (`ModularForm.weakFEPair`).
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold Pointwise Modular ArithmeticFunction.sigma

namespace NumberFieldKB.MilneEC.V

variable {N : ℕ} [NeZero N]

/-! ### The involution $w_N$ and Hecke's theorem -/

/-- $\alpha_N = \begin{pmatrix}0&-1\\N&0\end{pmatrix} \in \mathrm{GL}_2(\mathbb R)$ (pdf p. 205); conjugation by
$\alpha_N$ preserves $\Gamma_0(N)$. -/
noncomputable def alphaN (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℝ), 0] (by simp [Matrix.det_fin_two, NeZero.ne])

/-- Matrix of `alphaN`. -/
lemma coe_alphaN : ((alphaN N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (N : ℝ), 0] := rfl

/-- Intertwining of `alphaN` with elements of $\Gamma_0(N)$: $\alpha_N\gamma = \gamma'\alpha_N$ and
$\alpha_N\gamma' = \gamma\alpha_N$ with $\gamma' \in \Gamma_0(N)$. -/
lemma alphaN_intertwine (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ γ' ∈ CongruenceSubgroup.Gamma0 N,
      alphaN N * Matrix.SpecialLinearGroup.mapGL ℝ γ = Matrix.SpecialLinearGroup.mapGL ℝ γ' * alphaN N ∧
      alphaN N * Matrix.SpecialLinearGroup.mapGL ℝ γ' = Matrix.SpecialLinearGroup.mapGL ℝ γ * alphaN N := by
  have hc : (N : ℤ) ∣ γ 1 0 := by
    have := CongruenceSubgroup.Gamma0_mem.mp hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  obtain ⟨c', hc'⟩ := hc
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at this
  obtain ⟨γ', h00, h01, h10, h11⟩ : ∃ γ' : SL(2, ℤ), γ' 0 0 = γ 1 1 ∧ γ' 0 1 = -c' ∧ γ' 1 0 = -(N : ℤ) * γ 0 1 ∧ γ' 1 1 = γ 0 0 := by
    refine ⟨⟨!![γ 1 1, -c'; -(N : ℤ) * γ 0 1, γ 0 0], ?_⟩, rfl, rfl, rfl, rfl⟩
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hc'] at hdet
    linear_combination hdet
  refine ⟨γ', ?_, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, h10]
    simp
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_alphaN, Matrix.mul_apply, Fin.sum_univ_two, hc', Matrix.SpecialLinearGroup.mapGL_coe_matrix, h00, h01, h10, h11] <;> ring
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_alphaN, Matrix.mul_apply, Fin.sum_univ_two, hc', Matrix.SpecialLinearGroup.mapGL_coe_matrix, h00, h01, h10, h11] <;> ring

/-- Conjugation by $\alpha_N$ preserves $\Gamma_0(N)$ (pdf p. 205). -/
@[kb "milne2006ec" "Ch. V, §4, conjugation by α_N preserves Γ₀(N) (running text), pdf p. 205"]
theorem alphaN_conj_Gamma0 : ConjAct.toConjAct (alphaN N)⁻¹ • Gamma0GL N = Gamma0GL N := by
  ext x
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  constructor
  · intro hx
    obtain ⟨γ', hγ', hx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨γ, hγ, h1, h2⟩ := alphaN_intertwine γ' hγ'
    have h3 : alphaN N * x = alphaN N * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
      rw [h2, hx]
      simp [mul_assoc]
    rw [mul_left_cancel h3]
    exact Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
  · intro hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨γ', hγ', h1, h2⟩ := alphaN_intertwine γ hγ
    have : alphaN N * Matrix.SpecialLinearGroup.mapGL ℝ γ * (alphaN N)⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ γ' := by
      rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact Subgroup.mem_map.mpr ⟨γ', hγ', rfl⟩

/-- The involution $(w_Nf)(z) = (\sqrt N z)^{-2k}f(-1/(Nz))$ (pdf p. 205). -/
@[kb "milne2006ec" "Ch. V, §4, the involution w_N (definition in prose), pdf p. 205"]
noncomputable def wN (N k : ℕ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  ((Real.sqrt N : ℂ) * z) ^ (-(2 * k : ℤ)) * f (ofComplex (-1 / ((N : ℂ) * z)))

/-- $\alpha_N z = -1/(Nz)$ (as a point of the upper half plane). -/
lemma alphaN_smul (z : ℍ) : alphaN N • z = ofComplex (-1 / ((N : ℂ) * z)) := by
  have hdet : 0 < (alphaN N).det.val := by
    simp [alphaN, Matrix.det_fin_two, NeZero.pos]
  have : ((alphaN N • z : ℍ) : ℂ) = -1 / ((N : ℂ) * z) := by
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, coe_alphaN]
  rw [← this, ofComplex_apply]

/-- The coordinate of $-1/(Nz)$ is $-1/(Nz)$. -/
lemma coe_ofComplex_alphaN (z : ℍ) : ((ofComplex (-1 / ((N : ℂ) * z)) : ℍ) : ℂ) = -1 / ((N : ℂ) * z) := by
  have hdet : 0 < (alphaN N).det.val := by
    simp [alphaN, Matrix.det_fin_two, NeZero.pos]
  rw [← alphaN_smul, UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, coe_alphaN]

/-- $w_N f = N^{1-k}\,(f \mid_{2k} \alpha_N)$. -/
lemma wN_eq_slash (k : ℕ) (f : ℍ → ℂ) :
    wN N k f = fun z => (N : ℂ) ^ (1 - (k : ℤ)) * (f ∣[(2 * k : ℤ)] alphaN N) z := by
  funext z
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hdet : (alphaN N).det.val = N := by
    simp [alphaN, Matrix.det_fin_two]
  rw [wN, ModularForm.slash_apply, alphaN_smul, hdet]
  simp [UpperHalfPlane.denom, coe_alphaN]
  have hpos : 0 < (alphaN N).det.val := by
    simp [alphaN, Matrix.det_fin_two, NeZero.pos]
  have hσ : ∀ w, UpperHalfPlane.σ (alphaN N) w = w := by
    intro w; unfold UpperHalfPlane.σ; rw [if_pos hpos]; rfl
  rw [hσ]
  have hs : ((Real.sqrt N : ℂ)) ^ 2 = N := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; simp
  have e1 : ((Real.sqrt N : ℂ) * z) ^ (2 * (k : ℤ)) = (N : ℂ) ^ (k : ℤ) * (z : ℂ) ^ (2 * (k : ℤ)) := by
    rw [mul_zpow, zpow_mul, zpow_ofNat, hs]
  have e2 : ((N : ℂ) * z) ^ (2 * (k : ℤ)) = (N : ℂ) ^ (2 * (k : ℤ)) * (z : ℂ) ^ (2 * (k : ℤ)) := by
    rw [mul_zpow]
  rw [e1, e2]
  have e3 : (N : ℂ) ^ (2 * (k : ℤ) - 1) = (N : ℂ) ^ (2 * (k : ℤ)) / N := zpow_sub_one₀ hN _
  have e4 : (N : ℂ) ^ (1 - (k : ℤ)) = N / (N : ℂ) ^ (k : ℤ) := by
    rw [zpow_sub₀ hN, zpow_one]
  have e5 : (N : ℂ) ^ (2 * (k : ℤ)) = (N : ℂ) ^ (k : ℤ) * (N : ℂ) ^ (k : ℤ) := by
    rw [two_mul, zpow_add₀ hN]
  have hNk : (N : ℂ) ^ (k : ℤ) ≠ 0 := zpow_ne_zero _ hN
  have hzk : (z : ℂ) ^ (2 * (k : ℤ)) ≠ 0 := zpow_ne_zero _ hz
  rw [e3, e4, e5]
  field_simp

/-- Transport of a cusp form along an equality of levels. -/
lemma exists_cuspForm_of_eq {G H : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : G = H) (F : CuspForm G k) :
    ∃ F' : CuspForm H k, ⇑F' = ⇑F := by
  subst h; exact ⟨F, rfl⟩

/-- $w_N$ preserves $S_{2k}(\Gamma_0(N))$ (pdf p. 205). -/
@[kb "milne2006ec" "Ch. V, §4, w_N preserves S_{2k}(Γ₀(N)) (running text), pdf p. 205"]
theorem wN_cuspForm (k : ℕ) (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) :
    ∃ F : CuspForm (Gamma0GL N) (2 * k : ℤ), ⇑F = wN N k f := by
  obtain ⟨F', hF'⟩ := exists_cuspForm_of_eq alphaN_conj_Gamma0 (CuspForm.translate f (alphaN N))
  refine ⟨((N : ℂ) ^ (1 - (k : ℤ))) • F', ?_⟩
  rw [wN_eq_slash]
  funext z
  simp [hF']
  exact Or.inl rfl

/-- $w_N^2 = 1$ (pdf p. 205). -/
@[kb "milne2006ec" "Ch. V, §4, w_N² = 1 (running text), pdf p. 205"]
theorem wN_wN (k : ℕ) (f : ℍ → ℂ) : wN N k (wN N k f) = f := by
  funext z
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hs : ((Real.sqrt N : ℂ)) ^ 2 = N := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; simp
  have hs0 : ((Real.sqrt N : ℂ)) ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; exact hN hs.symm
  have h1 : (-1 : ℂ) / ((N : ℂ) * (-1 / ((N : ℂ) * z))) = z := by
    field_simp
  have h2 : ((Real.sqrt N : ℂ) * z) * ((Real.sqrt N : ℂ) * (-1 / ((N : ℂ) * z))) = -1 := by
    have : ((Real.sqrt N : ℂ) * z) * ((Real.sqrt N : ℂ) * (-1 / ((N : ℂ) * z))) = -((Real.sqrt N : ℂ) ^ 2 / N) := by
      field_simp
    rw [this, hs]; field_simp
  simp only [wN]
  rw [coe_ofComplex_alphaN, h1, ofComplex_apply, ← mul_assoc, ← mul_zpow, h2]
  rw [Even.neg_one_zpow ⟨-(k : ℤ), by ring⟩, one_mul]

omit [NeZero N] in
/-- $w_N$ is additive. -/
lemma wN_add (k : ℕ) (f g : ℍ → ℂ) : wN N k (f + g) = wN N k f + wN N k g := by
  funext z; simp [wN, mul_add]

omit [NeZero N] in
/-- $w_N$ commutes with scalars. -/
lemma wN_smul (k : ℕ) (c : ℂ) (f : ℍ → ℂ) : wN N k (c • f) = c • wN N k f := by
  funext z; simp [wN]; ring

/-- $w_N$ as a linear involution of $S_{2k}(\Gamma_0(N))$. -/
noncomputable def wNLinear (N k : ℕ) [NeZero N] :
    CuspForm (Gamma0GL N) (2 * k : ℤ) →ₗ[ℂ] CuspForm (Gamma0GL N) (2 * k : ℤ) where
  toFun f := Classical.choose (wN_cuspForm k f)
  map_add' f g := by
    apply DFunLike.coe_injective
    have h1 := Classical.choose_spec (wN_cuspForm k f)
    have h2 := Classical.choose_spec (wN_cuspForm k g)
    have h3 := Classical.choose_spec (wN_cuspForm k (f + g))
    refine h3.trans (Eq.trans ?_ (FunLike.coe_add _ _).symm)
    rw [h1, h2, FunLike.coe_add, wN_add]
  map_smul' c f := by
    apply DFunLike.coe_injective
    have h1 := Classical.choose_spec (wN_cuspForm k f)
    have h3 := Classical.choose_spec (wN_cuspForm k (c • f))
    rw [RingHom.id_apply]
    refine h3.trans (Eq.trans ?_ (FunLike.coe_smul _ _).symm)
    rw [h1, FunLike.coe_smul, wN_smul]

/-- The linear map $w_N$ on cusp forms has underlying function $w_N$. -/
theorem coe_wNLinear (k : ℕ) (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) : ⇑(wNLinear N k f) = wN N k f :=
  Classical.choose_spec (wN_cuspForm k f)

/-- $w_N$ is an involution on cusp forms. -/
lemma wNLinear_wNLinear (k : ℕ) (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) :
    wNLinear N k (wNLinear N k f) = f := by
  apply DFunLike.coe_injective
  rw [coe_wNLinear, coe_wNLinear, wN_wN]

/-- The eigenvalues of $w_N$ are $\pm1$ and $S_{2k}(\Gamma_0(N)) = S^{+1}_{2k} \oplus S^{-1}_{2k}$
(pdf p. 205). -/
@[kb "milne2006ec" "Ch. V, §4, S_{2k} = S⁺ ⊕ S⁻ (running text), pdf p. 205"]
theorem wN_eigen_decomposition (k : ℕ) :
    (∀ (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) (c : ℂ), f ≠ 0 → wNLinear N k f = c • f → c = 1 ∨ c = -1) ∧
    IsCompl (Module.End.eigenspace (wNLinear N k) 1) (Module.End.eigenspace (wNLinear N k) (-1)) := by
  constructor
  · intro f c hf h
    have h2 : f = (c * c) • f := by
      conv_lhs => rw [← wNLinear_wNLinear k f, h]
      rw [map_smul, h, smul_smul]
    have h3 : (c * c - 1) • f = 0 := by
      rw [sub_smul, one_smul, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · have : (c - 1) * (c + 1) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp this with h5 | h5
      · left; linear_combination h5
      · right; linear_combination h5
    · exact absurd h4 hf
  · constructor
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro f hf
      rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff] at hf
      obtain ⟨h1, h2⟩ := hf
      rw [h1] at h2
      have : (2 : ℂ) • f = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← one_smul ℂ f]
        nth_rewrite 2 [← one_smul ℂ f]
        have h3 : (1 : ℂ) • f + (1 : ℂ) • f = (1 : ℂ) • f - (-1 : ℂ) • f := by simp
        rw [h3, ← h2]
        simp
      rcases smul_eq_zero.mp this with h | h
      · norm_num at h
      · exact h
    · rw [codisjoint_iff, eq_top_iff]
      intro f _
      have e : f = (1 / 2 : ℂ) • (f + wNLinear N k f) + (1 / 2 : ℂ) • (f - wNLinear N k f) := by
        module
      rw [e]
      refine Submodule.add_mem_sup ?_ ?_
      · rw [Module.End.mem_eigenspace_iff, map_smul, map_add, wNLinear_wNLinear, one_smul, add_comm]
      · rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, wNLinear_wNLinear]
        module

/-- The completed $L$-function $\Lambda(f, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(f, s)$ of Theorem 4.4, defined through
Mathlib's entire function `ModularForm.Λ` $= (2\pi)^{-s}\Gamma(s)L(f,s)$ (see `LambdaHecke_eq`). -/
noncomputable def LambdaHecke (N k : ℕ) [NeZero N] (hk : 0 < k) (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * ModularForm.Λ (by positivity : (0 : ℤ) < 2 * k) f s

/-- $\Lambda(f, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(f, s)$ away from the poles of $\Gamma$. -/
theorem LambdaHecke_eq {k : ℕ} (hk : 0 < k) (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) :
    LambdaHecke N k hk f s =
      (N : ℂ) ^ (s / 2) * (2 * π) ^ (-s) * Gamma s * ModularForm.L (by positivity : (0 : ℤ) < 2 * k) f s := by
  have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hp : ((2 : ℂ) * π) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [Real.pi_ne_zero]
  unfold LambdaHecke ModularForm.L
  rw [Complex.Gammaℂ_def]
  field_simp

/-- If $w_N f = \varepsilon f$ then $(f \mid_{2k} S)(Nu) = \varepsilon N^{-k} f(u)$. -/
lemma slash_S_eq (k : ℕ) (f : ℍ → ℂ) (ε : ℂ) (hf : wN N k f = ε • f) (z u : ℍ)
    (hu : (z : ℂ) = N * u) :
    (f ∣[(2 * k : ℤ)] (ModularGroup.S : GL (Fin 2) ℝ)) z = ε * (N : ℂ) ^ (-(k : ℤ)) * f u := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hu0 : (u : ℂ) ≠ 0 := u.ne_zero
  have hs : ((Real.sqrt N : ℂ)) ^ 2 = N := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; simp
  have hs0 : ((Real.sqrt N : ℂ)) ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; exact hN hs.symm
  have hSz : ((ModularGroup.S : GL (Fin 2) ℝ) • z : ℍ) = ofComplex (-1 / ((N : ℂ) * u)) := by
    apply UpperHalfPlane.ext
    rw [coe_ofComplex_alphaN, UpperHalfPlane.coe_smul_of_det_pos (by simp), hu]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, div_eq_mul_inv, mul_comm]
  have h1 := congrFun hf u
  simp only [wN, Pi.smul_apply, smul_eq_mul] at h1
  rw [ModularForm.slash_apply, hSz]
  simp [UpperHalfPlane.σ, UpperHalfPlane.denom]
  have h1' : (((Real.sqrt N : ℂ) * u) ^ (2 * k))⁻¹ * f (ofComplex (-1 / ((N : ℂ) * u))) = ε * f u := by
    rw [show -(2 * (k : ℤ)) = -((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast] at h1
    exact h1
  have e1 : ((Real.sqrt N : ℂ) * u) ^ (2 * k) = (N : ℂ) ^ k * (u : ℂ) ^ (2 * k) := by
    rw [mul_pow, pow_mul, hs]
  have e2 : ((N : ℂ) * u) ^ (2 * k) = (N : ℂ) ^ (2 * k) * (u : ℂ) ^ (2 * k) := mul_pow _ _ _
  rw [hu, show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, e2]
  rw [e1] at h1'
  have hNk : (N : ℂ) ^ k ≠ 0 := pow_ne_zero _ hN
  have huk : (u : ℂ) ^ (2 * k) ≠ 0 := pow_ne_zero _ hu0
  have hA : f (ofComplex (-1 / ((N : ℂ) * u))) = ε * f u * ((N : ℂ) ^ k * (u : ℂ) ^ (2 * k)) := by
    field_simp at h1' ⊢
    linear_combination h1'
  rw [hA]
  field_simp
  ring

/-- **Theorem 4.4** (Hecke, pdf p. 205): let $f \in S_{2k}(\Gamma_0(N))$ with $w_Nf = \varepsilon f$,
$\varepsilon = \pm1$. Then $L(f, s)$ extends to an entire function and
$\Lambda(f, 2k - s) = \varepsilon(-1)^k\Lambda(f, s)$. Milne prints $\Lambda(f, k - s)$; for weight $2k$ the
functional equation relates $s$ and $2k - s$ (erratum; consistent with $\Lambda(f, 2 - s)$ for weight $2$ on
pdf p. 215). -/
@[kb "milne2006ec" "Ch. V, Theorem 4.4 (Hecke), pdf p. 205"]
theorem thm_4_4 {k : ℕ} (hk : 0 < k) (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hf : wN N k f = ε • ⇑f) :
    Differentiable ℂ (ModularForm.L (by positivity : (0 : ℤ) < 2 * k) f) ∧
    Differentiable ℂ (LambdaHecke N k hk f) ∧
    ∀ s : ℂ, LambdaHecke N k hk f (2 * k - s) = ε * (-1) ^ k * LambdaHecke N k hk f s := by
  have hK : (0 : ℤ) < 2 * k := by positivity
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  refine ⟨CuspForm.differentiable_L hK f, ?_, ?_⟩
  · unfold LambdaHecke
    exact Differentiable.mul (Differentiable.const_cpow (by fun_prop) (Or.inl hN))
      (CuspForm.differentiable_Λ hK f)
  have hgt : ∀ t : ℝ, 0 < t → (weakFEPair hK f).g t =
      (ε * (N : ℂ) ^ (-(k : ℤ))) • (fun t : ℝ => f (ofComplex (I * t))) (((N : ℝ)⁻¹) * t) := by
    intro t ht
    have h1 : (0 : ℝ) < ((N : ℝ)⁻¹) * t := by positivity
    simp only [weakFEPair_g, ModularForm.coe_translate, smul_eq_mul]
    rw [slash_S_eq k f ε hf (ofComplex (I * t)) (ofComplex (I * ((((N : ℝ)⁻¹) * t : ℝ) : ℂ)))]
    rw [ofComplex_apply_of_im_pos (by simpa using ht), ofComplex_apply_of_im_pos (by simpa using h1)]
    simp
    field_simp
  have hsymm : ∀ s, (weakFEPair hK f).symm.Λ s =
      ε * (N : ℂ) ^ (-(k : ℤ)) * (N : ℂ) ^ s * ModularForm.Λ hK f s := by
    intro s
    rw [(CuspForm.isStrongFEPair hK f).symm_Λ_eq, CuspForm.Λ_eq_mellin]
    have : mellin (weakFEPair hK f).g s = mellin (fun t : ℝ => (ε * (N : ℂ) ^ (-(k : ℤ))) •
        (fun t : ℝ => f (ofComplex (I * t))) (((N : ℝ)⁻¹) * t)) s := by
      unfold mellin
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [hgt t ht]
    rw [this, mellin_const_smul, mellin_comp_mul_left (fun t : ℝ => f (ofComplex (I * t))) s (by positivity : (0 : ℝ) < (N : ℝ)⁻¹)]
    simp only [smul_eq_mul]
    have harg : ((N : ℂ)).arg ≠ π := by
      rw [show (N : ℂ) = ((N : ℝ) : ℂ) by simp, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg N)]
      exact Real.pi_ne_zero.symm
    rw [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]
    ring
  intro s
  have hfe := (weakFEPair hK f).functional_equation s
  have hk' : (((weakFEPair hK f).k : ℝ) : ℂ) = 2 * k := by simp [weakFEPair]
  have hε' : (weakFEPair hK f).ε = (-1) ^ k := by
    simp only [weakFEPair]
    rw [show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul, Complex.I_sq]
  rw [hk', hε', hsymm] at hfe
  have hΛ : ModularForm.Λ hK f (2 * k - s) = (-1) ^ k * (ε * (N : ℂ) ^ (-(k : ℤ)) * (N : ℂ) ^ s * ModularForm.Λ hK f s) := by
    exact hfe
  have hcp : (N : ℂ) ^ ((2 * k - s) / 2) * ((N : ℂ) ^ (-(k : ℤ)) * (N : ℂ) ^ s) = (N : ℂ) ^ (s / 2) := by
    rw [← Complex.cpow_intCast, ← Complex.cpow_add _ _ hN, ← Complex.cpow_add _ _ hN]
    congr 1
    push_cast
    ring
  unfold LambdaHecke
  rw [hΛ]
  linear_combination (ε * (-1) ^ k * ModularForm.Λ hK f s) * hcp

end NumberFieldKB.MilneEC.V
