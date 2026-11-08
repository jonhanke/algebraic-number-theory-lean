import NumberFieldKB.MilneEC.Ch5ModularForms

/-!
# Milne, *Elliptic Curves*, Chapter V §3: the graded algebra of modular forms of level one

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §2 equation (36) and §3 Theorem 3.6 with the
dimension formula (pdf pp. 191, 200).

Proof strategy for Theorem 3.6. Write $G_4 = c_4E_4$ and $G_6 = c_6E_6$ with Mathlib's normalised Eisenstein series
and nonzero constants (`eisG4_eq`, `eisG6_eq`). Generation is by strong induction on the weight (`span_aux`):
subtracting a multiple of a monomial removes the constant term of the $q$-expansion, and a cusp form is $\Delta$
times a form of weight $w - 12$ (`CuspForm.discriminantEquiv`). Linear independence of the monomials of one weight
(`linInd_even`) follows from generation and a count of the monomials against Mathlib's dimension formula
(`card_expo`, `finrank_M`). Monomials of different weights are separated by the transformation law under the
matrices with bottom row $(1, d)$, since a polynomial with infinitely many roots is zero (`linInd_all`).
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup EisensteinSeries
open scoped MatrixGroups Real Manifold Pointwise Modular ArithmeticFunction.sigma

namespace NumberFieldKB.MilneEC.V

/-! ### The $q$-expansion of $\Delta$ -/

/-- The $q$-expansion coefficients of Mathlib's `E₄`. -/
lemma E4_coeff (n : ℕ) : (qExpansion 1 E₄).coeff n = if n = 0 then 1 else 240 * (σ 3 n : ℂ) := by
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩]
  split_ifs
  · rfl
  · norm_num [show bernoulli 4 = -1 / 30 by decide +kernel]

/-- The $q$-expansion coefficients of Mathlib's `E₆`. -/
lemma E6_coeff (n : ℕ) : (qExpansion 1 E₆).coeff n = if n = 0 then 1 else -504 * (σ 5 n : ℂ) := by
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩]
  split_ifs
  · rfl
  · norm_num [show bernoulli 6 = 1 / 42 by decide +kernel]

/-- The first values of the divisor power sums used in the expansion of $\Delta$. -/
lemma sigma_values :
    σ 3 2 = 9 ∧ σ 3 3 = 28 ∧ σ 3 4 = 73 ∧ σ 5 2 = 33 ∧ σ 5 3 = 244 ∧ σ 5 4 = 1057 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The weight twelve form $E_4^3 - E_6^2$. -/
noncomputable def E4cubeSubE6sq : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

/-- The form $E_4^3 - E_6^2$ evaluated at $z$ equals $E_4(z)^3 - E_6(z)^2$. -/
lemma E4cubeSubE6sq_apply (z : ℍ) : E4cubeSubE6sq z = E₄ z ^ 3 - E₆ z ^ 2 := by
  simp only [E4cubeSubE6sq, FunLike.coe_sub, coe_mcast, Pi.sub_apply, ModularForm.coe_pow,
    Pi.pow_apply]

/-- The discriminant form is $(2\pi)^{12}/1728$ times $E_4^3 - E_6^2$. -/
lemma discr_eq_smul : discr = ((2 * π : ℂ) ^ 12 / 1728) • ⇑E4cubeSubE6sq := by
  funext z
  simp [discr_eq, discriminant_eq_E₄_cube_sub_E₆_sq, E4cubeSubE6sq_apply]
  ring

/-- The $q$-expansion of $E_4^3 - E_6^2$. -/
lemma qExpansion_E4cubeSubE6sq : qExpansion 1 E4cubeSubE6sq =
    qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
  simp only [E4cubeSubE6sq, FunLike.coe_sub, coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

/-- The $q$-expansion of the discriminant form. -/
lemma qExpansion_discr : qExpansion 1 discr =
    ((2 * π : ℂ) ^ 12 / 1728) • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) := by
  rw [discr_eq_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    qExpansion_E4cubeSubE6sq]

/-- Equation (36) (pdf p. 191): $\Delta = (2\pi)^{12}(q - 24q^2 + 252q^3 - 1472q^4 + \cdots)$, as the first
coefficients of the $q$-expansion of Milne's $\Delta$. -/
@[kb "milne2006ec" "Ch. V, §2, equation (36), pdf p. 191"]
theorem eq_36 :
    (qExpansion 1 discr).coeff 0 = 0 ∧ (qExpansion 1 discr).coeff 1 = (2 * π) ^ 12 ∧
      (qExpansion 1 discr).coeff 2 = -24 * (2 * π) ^ 12 ∧
      (qExpansion 1 discr).coeff 3 = 252 * (2 * π) ^ 12 ∧
      (qExpansion 1 discr).coeff 4 = -1472 * (2 * π) ^ 12 := by
  obtain ⟨h32, h33, h34, h52, h53, h54⟩ := sigma_values
  have h4 := E4_coeff
  have h6 := E6_coeff
  rw [qExpansion_discr]
  simp only [PowerSeries.coeff_smul, map_sub, pow_succ, pow_zero, one_mul, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.sum_cons, Finset.sum_map]
  simp [h4, h6, h32, h33, h34, h52, h53, h54, Finset.Nat.antidiagonal_succ]
  norm_num
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-! ### Comparison constants and the monomial forms -/

/-- The constant $c_4 = 2\zeta(4)$ with $G_4 = c_4E_4$. -/
noncomputable def c4 : ℂ := 2 * riemannZeta 4

/-- The constant $c_6 = 2\zeta(6)$ with $G_6 = c_6E_6$. -/
noncomputable def c6 : ℂ := 2 * riemannZeta 6

/-- The normalizing constant $c_4$ of the Eisenstein series of weight $4$ is nonzero. -/
lemma c4_ne_zero : c4 ≠ 0 := by
  have : riemannZeta 4 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  simpa [c4] using this

/-- The normalizing constant $c_6$ of the Eisenstein series of weight $6$ is nonzero. -/
lemma c6_ne_zero : c6 ≠ 0 := by
  have : riemannZeta 6 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  simpa [c6] using this

/-- The Eisenstein series $G_4$ equals $c_4 E_4$. -/
lemma eisG4_eq : eisG 4 = c4 • ⇑E₄ := by
  funext z
  have := eisG_eq (by norm_num : 3 ≤ 4) z
  simpa [c4] using this

/-- The Eisenstein series $G_6$ equals $c_6 E_6$. -/
lemma eisG6_eq : eisG 6 = c6 • ⇑E₆ := by
  funext z
  have := eisG_eq (by norm_num : 3 ≤ 6) z
  simpa [c6] using this

/-- The monomial $E_4^aE_6^b$ as a modular form of weight $w = 4a + 6b$. -/
noncomputable def Eform (w a b : ℕ) (h : 4 * a + 6 * b = w) : ModularForm 𝒮ℒ (w : ℤ) :=
  ModularForm.mcast (by rw [← h]; push_cast; ring) ((E₄.pow a).mul (E₆.pow b))

/-- The underlying function of the monomial form $E_4^a E_6^b$ of weight $w = 4a + 6b$. -/
lemma coe_Eform (w a b : ℕ) (h : 4 * a + 6 * b = w) :
    ⇑(Eform w a b h) = ⇑E₄ ^ a * ⇑E₆ ^ b := by
  simp [Eform, ModularForm.coe_pow]

/-- The constant term of the $q$-expansion of $E_4^a E_6^b$ is $1$. -/
lemma qExpansion_coeff_zero_Eform (w a b : ℕ) (h : 4 * a + 6 * b = w) :
    (qExpansion 1 (Eform w a b h)).coeff 0 = 1 := by
  have : qExpansion 1 (Eform w a b h) = qExpansion 1 E₄ ^ a * qExpansion 1 E₆ ^ b := by
    simp only [Eform, ModularForm.qExpansion_mcast]
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have h4 : PowerSeries.constantCoeff (qExpansion 1 E₄) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  have h6 : PowerSeries.constantCoeff (qExpansion 1 E₆) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact E_qExpansion_coeff_zero _ ⟨3, rfl⟩
  rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [h4, h6]

/-- The dimension of $M_{2k}$ for $\mathrm{SL}_2(\mathbb Z)$ (Mathlib's `ModularForm.dimension_level_one`). -/
lemma rank_even_aux (k : ℕ) :
    Module.rank ℂ (ModularForm 𝒮ℒ (2 * k : ℤ)) =
      if k % 6 = 1 then (k / 6 : ℕ) else (k / 6 + 1 : ℕ) := by
  have h := ModularForm.dimension_level_one (2 * k) (even_two_mul k)
  push_cast at h
  rw [h]
  have hmod : 2 * k ≡ 2 [MOD 12] ↔ k % 6 = 1 := by
    simp only [Nat.ModEq]
    omega
  by_cases hk : k % 6 = 1
  · have : 2 * k / 12 = k / 6 := by omega
    simp [hmod.mpr hk, hk, this]
  · have : 2 * k / 12 = k / 6 := by omega
    simp [hk, this, mt hmod.mp hk]

/-! ### Generation -/

/-- The monomials $G_4^aG_6^b$ of weight `w`. -/
def monoms (w : ℕ) : Set (ℍ → ℂ) :=
  {g | ∃ a b : ℕ, 4 * a + 6 * b = w ∧ g = eisG 4 ^ a * eisG 6 ^ b}

/-- The monomial form of weight $w = 4a + 6b$ is the function $E_4^a E_6^b$. -/
lemma coe_Eform_eq (w a b : ℕ) (h : 4 * a + 6 * b = w) :
    ⇑(Eform w a b h) = (c4 ^ a * c6 ^ b)⁻¹ • (eisG 4 ^ a * eisG 6 ^ b) := by
  have h4 := c4_ne_zero
  have h6 := c6_ne_zero
  rw [coe_Eform, eisG4_eq, eisG6_eq]
  funext z
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  field_simp
  ring

/-- The monomial form $E_4^a E_6^b$ lies in the span of the monomials of weight $w$. -/
lemma Eform_mem_span (w a b : ℕ) (h : 4 * a + 6 * b = w) :
    ⇑(Eform w a b h) ∈ Submodule.span ℂ (monoms w) := by
  rw [coe_Eform_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, b, h, rfl⟩)

/-- Multiplying a form in the span of the monomials of weight $w'$ by $E_4^{a_0} E_6^{b_0}$ gives a form in the span of the monomials of the combined weight. -/
lemma mul_mem_aux (a0 b0 w' : ℕ) {h : ℍ → ℂ} (hh : h ∈ Submodule.span ℂ (monoms w')) :
    (eisG 4 ^ a0 * eisG 6 ^ b0) * h ∈ Submodule.span ℂ (monoms (4 * a0 + 6 * b0 + w')) := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨a0 + a, b0 + b, by omega, ?_⟩
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- Multiplying a form in the span of the monomials of weight $w'$ by $\Delta$ gives a form in the span of the monomials of weight $w' + 12$. -/
lemma delta_mul_mem (w' : ℕ) {h : ℍ → ℂ} (hh : h ∈ Submodule.span ℂ (monoms w')) :
    ModularForm.discriminant * h ∈ Submodule.span ℂ (monoms (12 + w')) := by
  have h4 := c4_ne_zero
  have h6 := c6_ne_zero
  have hΔ : ModularForm.discriminant * h =
      ((1728 : ℂ)⁻¹ * (c4 ^ 3)⁻¹) • ((eisG 4 ^ 3 * eisG 6 ^ 0) * h) -
        ((1728 : ℂ)⁻¹ * (c6 ^ 2)⁻¹) • ((eisG 4 ^ 0 * eisG 6 ^ 2) * h) := by
    funext z
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul,
      discriminant_eq_E₄_cube_sub_E₆_sq, eisG4_eq, eisG6_eq]
    field_simp
  rw [hΔ]
  refine Submodule.sub_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · have := mul_mem_aux 3 0 w' hh
    simpa using this
  · have := mul_mem_aux 0 2 w' hh
    simpa using this

/-- Every level one modular form of weight `w` lies in the span of the monomials of weight `w`. -/
theorem span_aux (w : ℕ) : ∀ f : ModularForm 𝒮ℒ (w : ℤ), ⇑f ∈ Submodule.span ℂ (monoms w) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro f
  by_cases hodd : Odd w
  · have : f = 0 := ModularForm.levelOne_odd_weight_eq_zero (by exact_mod_cast hodd) f
    simp [this]
  by_cases h2 : w = 2
  · subst h2
    have : f = 0 := rank_zero_iff_forall_zero.mp
      (by exact_mod_cast ModularForm.levelOne_weight_two_rank_zero) f
    simp [this]
  have hex : ∃ a b : ℕ, 4 * a + 6 * b = w := by
    have he : w % 2 = 0 := by simpa [Nat.odd_iff] using hodd
    by_cases h4 : w % 4 = 0
    · exact ⟨w / 4, 0, by omega⟩
    · exact ⟨(w - 6) / 4, 1, by omega⟩
  obtain ⟨a, b, hab⟩ := hex
  set c := (qExpansion 1 f).coeff 0 with hc
  have hcusp := ModularForm.sub_smul_isCuspForm f (Eform w a b hab)
    (qExpansion_coeff_zero_Eform w a b hab)
  have h0 := (ModularForm.isCuspForm_iff_coeffZero_eq_zero _).mp hcusp
  let g : ModularForm 𝒮ℒ (w : ℤ) := f - c • Eform w a b hab
  let F := CuspForm.discriminantEquiv (ModularForm.toCuspForm g h0)
  have hg : ⇑g = ModularForm.discriminant * ⇑F :=
    (ModularForm.discriminant_mul_discriminantEquiv (ModularForm.toCuspForm g h0)).symm
  have hf : ⇑f = ⇑g + c • ⇑(Eform w a b hab) := by
    ext z
    simp [g]
  rw [hf]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Eform_mem_span w a b hab))
  rw [hg]
  by_cases hw : w < 12
  · have : F = 0 := rank_zero_iff_forall_zero.mp
      (ModularForm.levelOne_neg_weight_rank_zero (by omega)) F
    simp [this]
  · obtain ⟨w', rfl⟩ : ∃ w', w = w' + 12 := ⟨w - 12, by omega⟩
    let F' : ModularForm 𝒮ℒ (w' : ℤ) := ModularForm.mcast (by push_cast; ring) F
    have h1 := ih w' (by omega) F'
    have h2 := delta_mul_mem w' h1
    rw [add_comm 12 w'] at h2
    exact h2

/-- **Theorem 3.6** (pdf p. 200), generation: every modular form of weight $w$ for $\mathrm{SL}_2(\mathbb Z)$ is a
$\mathbb C$-linear combination of the monomials $G_4^aG_6^b$ with $4a + 6b = w$. -/
@[kb "milne2006ec" "Ch. V, Theorem 3.6 (generation by G₄, G₆), pdf p. 200"]
theorem thm_3_6_span (w : ℕ) (f : ModularForm 𝒮ℒ w) :
    ⇑f ∈ Submodule.span ℂ {g : ℍ → ℂ | ∃ a b : ℕ, 4 * a + 6 * b = w ∧ g = eisG 4 ^ a * eisG 6 ^ b} := by
  exact span_aux w f

/-! ### Separating the weights -/

/-- A matrix in $\mathrm{SL}_2(\mathbb Z)$ with bottom row $(1, d)$. -/
def gam (d : ℤ) : SL(2, ℤ) := ⟨!![1, d - 1; 1, d], by simp [Matrix.det_fin_two]⟩

/-- The transformation law of a level one modular form of weight $k$ under an element of $\mathrm{SL}_2(\mathbb Z)$ with lower right entry $d$. -/
lemma transform_gam {k : ℤ} (F : ModularForm 𝒮ℒ k) (d : ℤ) (z : ℍ) :
    F ((gam d : GL (Fin 2) ℝ) • z) = ((z : ℂ) + d) ^ k * F z := by
  have hγ : ((gam d : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨gam d, rfl⟩
  rw [SlashInvariantForm.slash_action_eqn' F hγ z]
  have e10 : (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) (gam d) :
      Matrix (Fin 2) (Fin 2) ℝ) 1 0) = 1 := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    simp [gam]
  have e11 : (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) (gam d) :
      Matrix (Fin 2) (Fin 2) ℝ) 1 1) = d := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    simp [gam]
  congr 2
  simp [e10, e11]

/-! ### Counting the monomials of a given weight -/

/-- The exponent pairs $(a, b)$ with $4a + 6b = w$. -/
def expo (w : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (w + 1)) ×ˢ (Finset.range (w + 1))).filter fun p => 4 * p.1 + 6 * p.2 = w

/-- A pair $(a, b)$ is an exponent pair of weight $w$ if and only if $4a + 6b = w$. -/
lemma mem_expo {w : ℕ} {p : ℕ × ℕ} : p ∈ expo w ↔ 4 * p.1 + 6 * p.2 = w := by
  simp only [expo, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- The number of exponent pairs of weight $2(k + 6)$ is one more than that of weight $2k$. -/
lemma card_expo_step (k : ℕ) : (expo (2 * (k + 6))).card = (expo (2 * k)).card + 1 := by
  have h1 : ((expo (2 * (k + 6))).filter (fun p => 2 ≤ p.2)).card = (expo (2 * k)).card := by
    apply Finset.card_nbij' (fun p => (p.1, p.2 - 2)) (fun p => (p.1, p.2 + 2))
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_expo, Finset.mem_coe] at hp ⊢
      omega
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_expo, Finset.mem_coe] at hp ⊢
      omega
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
      ext <;> simp <;> omega
    · intro p hp
      simp
  have h2 : ((expo (2 * (k + 6))).filter (fun p => ¬ 2 ≤ p.2)).card = 1 := by
    rw [Finset.card_eq_one]
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · refine ⟨(m + 3, 0), ?_⟩
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, mem_expo, Finset.mem_singleton, Prod.mk.injEq]
      omega
    · refine ⟨(m + 2, 1), ?_⟩
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, mem_expo, Finset.mem_singleton, Prod.mk.injEq]
      omega
  have := Finset.card_filter_add_card_filter_not (s := expo (2 * (k + 6))) (fun p => 2 ≤ p.2)
  omega

/-- The number of exponent pairs of weight $2k$, which is the dimension of the space of level one forms of weight $2k$. -/
lemma card_expo (k : ℕ) :
    (expo (2 * k)).card = if k % 6 = 1 then k / 6 else k / 6 + 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  by_cases hk : k < 6
  · interval_cases k <;> decide
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 6 := ⟨k - 6, by omega⟩
    rw [card_expo_step, ih k' (by omega)]
    have : (k' + 6) % 6 = k' % 6 := by omega
    have h2 : (k' + 6) / 6 = k' / 6 + 1 := by omega
    rw [this, h2]
    split_ifs <;> omega

/-! ### Linear independence in a fixed weight -/

/-- The monomial $G_4^aG_6^b$ as a modular form of weight $w = 4a + 6b$. -/
noncomputable def Gform (w a b : ℕ) (h : 4 * a + 6 * b = w) : ModularForm 𝒮ℒ (w : ℤ) :=
  (c4 ^ a * c6 ^ b) • Eform w a b h

/-- The underlying function of the monomial form $G_4^a G_6^b$ of weight $w = 4a + 6b$. -/
lemma coe_Gform (w a b : ℕ) (h : 4 * a + 6 * b = w) :
    ⇑(Gform w a b h) = eisG 4 ^ a * eisG 6 ^ b := by
  have h4 := c4_ne_zero
  have h6 := c6_ne_zero
  rw [Gform, FunLike.coe_smul, coe_Eform_eq, smul_smul]
  funext z
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  field_simp

/-- Coercion of modular forms to functions, as a linear map. -/
def coeL (k : ℤ) : ModularForm 𝒮ℒ k →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Passing from a modular form of weight $k$ to its underlying function is injective. -/
lemma coeL_injective (k : ℤ) : Function.Injective (coeL k) := DFunLike.coe_injective

/-- The dimension of the space of level one modular forms of weight $2k$. -/
lemma finrank_M (k : ℕ) :
    Module.finrank ℂ (ModularForm 𝒮ℒ ((2 * k : ℕ) : ℤ)) = (expo (2 * k)).card := by
  rw [card_expo]
  have := rank_even_aux k
  push_cast
  exact Module.finrank_eq_of_rank_eq (by rw [this])

/-- The family of monomials of weight $2k$ as modular forms. -/
noncomputable def bfam (k : ℕ) (p : expo (2 * k)) : ModularForm 𝒮ℒ ((2 * k : ℕ) : ℤ) :=
  Gform (2 * k) p.1.1 p.1.2 (mem_expo.mp p.2)

/-- The monomial forms of weight $2k$ are linearly independent over $\mathbb C$. -/
lemma linInd_even (k : ℕ) : LinearIndependent ℂ (bfam k) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · intro f _
    have hf := span_aux (2 * k) f
    have hsub : monoms (2 * k) ⊆ coeL _ '' Set.range (bfam k) := by
      rintro g ⟨a, b, hab, rfl⟩
      exact ⟨bfam k ⟨(a, b), mem_expo.mpr hab⟩, ⟨_, rfl⟩, coe_Gform _ _ _ _⟩
    have : coeL _ f ∈ Submodule.map (coeL _) (Submodule.span ℂ (Set.range (bfam k))) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono hsub hf
    obtain ⟨x, hx, hxf⟩ := this
    have := coeL_injective _ hxf
    rw [← this]
    exact hx
  · rw [Fintype.card_coe, finrank_M]

/-- The monomial forms of fixed weight $w$ indexed by a finite set of exponent pairs are linearly independent over $\mathbb C$. -/
lemma linInd_fixed (w : ℕ) (t : Finset (ℕ × ℕ)) (ht : ∀ p ∈ t, 4 * p.1 + 6 * p.2 = w)
    (c : ℕ × ℕ → ℂ)
    (h : ∑ p ∈ t, c p • (eisG 4 ^ p.1 * eisG 6 ^ p.2) = 0) : ∀ p ∈ t, c p = 0 := by
  rcases Nat.even_or_odd' w with ⟨k, rfl | rfl⟩
  · intro p hp
    have key := Fintype.linearIndependent_iff.mp (linInd_even k)
      (fun q => if q.1 ∈ t then c q.1 else 0) ?_ ⟨p, mem_expo.mpr (ht p hp)⟩
    · simpa [hp] using key
    · apply coeL_injective
      rw [map_sum, map_zero]
      have : ∀ q : expo (2 * k), coeL _ ((if q.1 ∈ t then c q.1 else 0) • bfam k q) =
          (if q.1 ∈ t then c q.1 else 0) • (eisG 4 ^ q.1.1 * eisG 6 ^ q.1.2) := by
        intro q
        rw [map_smul]
        exact congrArg _ (coe_Gform _ _ _ _)
      simp_rw [this]
      rw [Finset.sum_coe_sort (expo (2 * k))
        (fun p => (if p ∈ t then c p else 0) • (eisG 4 ^ p.1 * eisG 6 ^ p.2))]
      simp_rw [ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr]
      · exact h
      · intro p hp
        exact mem_expo.mpr (ht p hp)
  · intro p hp
    have := ht p hp
    omega

/-- The transformation law of $G_4$ under an element of $\mathrm{SL}_2(\mathbb Z)$ with lower right entry $d$. -/
lemma eisG4_transform (d : ℤ) (z : ℍ) :
    eisG 4 ((gam d : GL (Fin 2) ℝ) • z) = ((z : ℂ) + d) ^ 4 * eisG 4 z := by
  have := transform_gam E₄ d z
  rw [eisG4_eq]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [this]
  simp only [zpow_ofNat]
  ring

/-- The transformation law of $G_6$ under an element of $\mathrm{SL}_2(\mathbb Z)$ with lower right entry $d$. -/
lemma eisG6_transform (d : ℤ) (z : ℍ) :
    eisG 6 ((gam d : GL (Fin 2) ℝ) • z) = ((z : ℂ) + d) ^ 6 * eisG 6 z := by
  have := transform_gam E₆ d z
  rw [eisG6_eq]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [this]
  simp only [zpow_ofNat]
  ring

/-- All monomials $G_4^aG_6^b$ are linearly independent over $\mathbb C$. -/
lemma linInd_all : LinearIndependent ℂ (fun p : ℕ × ℕ => eisG 4 ^ p.1 * eisG 6 ^ p.2) := by
  rw [linearIndependent_iff']
  intro s g hs i hi
  have hz : ∀ (z : ℍ) (n : ℕ), ∑ p ∈ s.filter (fun p => 4 * p.1 + 6 * p.2 = n),
      g p * (eisG 4 z ^ p.1 * eisG 6 z ^ p.2) = 0 := by
    intro z n
    let Q : Polynomial ℂ := ∑ p ∈ s, Polynomial.C (g p * (eisG 4 z ^ p.1 * eisG 6 z ^ p.2)) *
      Polynomial.X ^ (4 * p.1 + 6 * p.2)
    have hQ : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.infinite_of_injective_forall_mem (f := fun d : ℤ => (z : ℂ) + d)
      · intro a b hab
        simpa using hab
      · intro d
        have := congrFun hs ((gam d : GL (Fin 2) ℝ) • z)
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul,
          eisG4_transform, eisG6_transform, Pi.zero_apply] at this
        simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Q, Polynomial.eval_finsetSum,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        refine Eq.trans ?_ this
        apply Finset.sum_congr rfl
        intro p _
        generalize (z : ℂ) + (d : ℂ) = u
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
        ring
    have h := congrArg (fun q => Polynomial.coeff q n) hQ
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at h
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl ?_) h
    intro p _
    exact if_congr eq_comm rfl rfl
  have := linInd_fixed (4 * i.1 + 6 * i.2)
    (s.filter (fun p => 4 * p.1 + 6 * p.2 = 4 * i.1 + 6 * i.2))
    (fun p hp => (Finset.mem_filter.mp hp).2) g ?_ i (Finset.mem_filter.mpr ⟨hi, rfl⟩)
  · exact this
  · funext z
    simpa [Finset.sum_apply] using hz z (4 * i.1 + 6 * i.2)

/-- **Theorem 3.6** (pdf p. 200), algebraic independence: $G_4$ and $G_6$ are algebraically independent over
$\mathbb C$ (in the ring of functions on $\mathbb H$). -/
@[kb "milne2006ec" "Ch. V, Theorem 3.6 (algebraic independence of G₄, G₆), pdf p. 200"]
theorem thm_3_6_algebraicIndependent : AlgebraicIndependent ℂ ![eisG 4, eisG 6] := by
  let b := MvPolynomial.basisMonomials (Fin 2) ℂ
  have hb : ∀ d, MvPolynomial.aeval ![eisG 4, eisG 6] (b d) = eisG 4 ^ d 0 * eisG 6 ^ d 1 := by
    intro d
    simp [b, MvPolynomial.coe_basisMonomials, MvPolynomial.aeval_monomial, Finsupp.prod_fintype,
      Fin.prod_univ_two]
  have hli : LinearIndependent ℂ (fun d => MvPolynomial.aeval ![eisG 4, eisG 6] (b d)) := by
    have := linInd_all.comp (fun d : Fin 2 →₀ ℕ => (d 0, d 1)) (by
      intro d d' h
      ext i
      fin_cases i <;> simp_all [Prod.ext_iff])
    convert this using 1
    funext d
    exact hb d
  rw [AlgebraicIndependent, injective_iff_map_eq_zero]
  intro P hP
  have h1 := b.linearCombination_repr P
  have h2 : Finsupp.linearCombination ℂ (fun d => MvPolynomial.aeval ![eisG 4, eisG 6] (b d))
      (b.repr P) = 0 := by
    have := Finsupp.apply_linearCombination ℂ
      (MvPolynomial.aeval ![eisG 4, eisG 6] : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] (ℍ → ℂ)).toLinearMap
      b (b.repr P)
    rw [h1] at this
    exact this.symm.trans hP
  have hl := (linearIndependent_iff.mp hli) (b.repr P) h2
  rw [← h1, hl]
  simp

/-! ### The graded isomorphism -/

/-- The weight of the exponent $d$ with respect to the weights $(4, 6)$ is $4 d_0 + 6 d_1$. -/
lemma weight_eq (d : Fin 2 →₀ ℕ) : Finsupp.weight ![(4 : ℕ), 6] d = 4 * d 0 + 6 * d 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  simp [mul_comm]

/-- The evaluation of a weighted homogeneous polynomial of weight $w$ at $(E_4, E_6)$ lies in the range of the monomial forms. -/
lemma aeval_mem_range (w : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ ![(4 : ℕ), 6] w) :
    MvPolynomial.aeval ![eisG 4, eisG 6] P ∈ LinearMap.range (coeL (w : ℤ)) := by
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hP
  rw [MvPolynomial.as_sum P, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hw : 4 * d 0 + 6 * d 1 = w := by
    have := hP (MvPolynomial.mem_support_iff.mp hd)
    rwa [weight_eq] at this
  refine ⟨P.coeff d • Gform w (d 0) (d 1) hw, ?_⟩
  rw [map_smul, coeL, LinearMap.coe_mk, AddHom.coe_mk, coe_Gform]
  simp [MvPolynomial.aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two, Algebra.smul_def]

/-- Every level one modular form of weight $w$ is a polynomial in $E_4$ and $E_6$. -/
lemma exists_poly (w : ℕ) (f : ModularForm 𝒮ℒ w) :
    ∃ P ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ ![(4 : ℕ), 6] w,
      MvPolynomial.aeval ![eisG 4, eisG 6] P = ⇑f := by
  have hle : Submodule.span ℂ (monoms w) ≤ Submodule.map
      (MvPolynomial.aeval ![eisG 4, eisG 6] : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] (ℍ → ℂ)).toLinearMap
      (MvPolynomial.weightedHomogeneousSubmodule ℂ ![(4 : ℕ), 6] w) := by
    rw [Submodule.span_le]
    rintro g ⟨a, b, hab, rfl⟩
    refine ⟨MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b, ?_, ?_⟩
    · rw [SetLike.mem_coe, MvPolynomial.mem_weightedHomogeneousSubmodule]
      have := ((MvPolynomial.isWeightedHomogeneous_X ℂ ![(4 : ℕ), 6] 0).pow a).mul
        ((MvPolynomial.isWeightedHomogeneous_X ℂ ![(4 : ℕ), 6] 1).pow b)
      convert this using 1
      simp
      omega
    · simp
  obtain ⟨P, hP, hPf⟩ := hle (span_aux w f)
  exact ⟨P, hP, hPf⟩

/-- **Theorem 3.6** (pdf p. 200), the graded isomorphism $\mathbb C[X,Y] \to \bigoplus_k M_{2k}(\Gamma_0(1))$,
$X \mapsto G_4$, $Y \mapsto G_6$ ($X$, $Y$ of weights $4$, $6$): it maps the polynomials of weight $w$ onto
$M_w$, and every modular form of weight $w$ is the image of exactly one polynomial of weight $w$. -/
@[kb "milne2006ec" "Ch. V, Theorem 3.6 (graded isomorphism ℂ[G₄,G₆] ≅ ⊕ M_{2k}), pdf p. 200"]
theorem thm_3_6_graded (w : ℕ) :
    (∀ P ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ ![(4 : ℕ), 6] w,
      ∃ F : ModularForm 𝒮ℒ w, ⇑F = MvPolynomial.aeval ![eisG 4, eisG 6] P) ∧
    ∀ F : ModularForm 𝒮ℒ w, ∃! P, P ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ ![(4 : ℕ), 6] w ∧
      MvPolynomial.aeval ![eisG 4, eisG 6] P = ⇑F := by
  refine ⟨fun P hP => ?_, fun F => ?_⟩
  · obtain ⟨F, hF⟩ := aeval_mem_range w P hP
    exact ⟨F, hF⟩
  · obtain ⟨P, hP, hPF⟩ := exists_poly w F
    refine ⟨P, ⟨hP, hPF⟩, ?_⟩
    rintro Q ⟨_, hQ⟩
    exact thm_3_6_algebraicIndependent (hQ.trans hPF.symm)

/-- **Theorem 3.6** (pdf p. 200), last part: $f \mapsto f\Delta$ is a bijection
$M_{w-12}(\Gamma_0(1)) \to S_w(\Gamma_0(1))$ (Mathlib's `CuspForm.discriminantEquiv` for its normalisation). -/
@[kb "milne2006ec" "Ch. V, Theorem 3.6 (multiplication by Δ), pdf p. 200"]
theorem thm_3_6_discr (w : ℤ) :
    (∀ f : ModularForm 𝒮ℒ (w - 12), ∃ F : CuspForm 𝒮ℒ w, ⇑F = ⇑f * discr) ∧
    ∀ F : CuspForm 𝒮ℒ w, ∃! f : ModularForm 𝒮ℒ (w - 12), ⇑F = ⇑f * discr := by
  refine ⟨fun f => ⟨((2 * π : ℂ) ^ 12) • CuspForm.ofMulDiscriminant f, ?_⟩, fun F => ?_⟩
  · funext z
    simp [discr_eq]
    ring
  · have hF : ⇑F = ((2 * π : ℂ) ^ 12)⁻¹ • ⇑(CuspForm.discriminantEquiv F) * discr := by
      funext z
      have := ModularForm.discriminant_mul_discriminantEquiv_apply F z
      have hπ : ((2 * π : ℂ) ^ 12) ≠ 0 := by
        have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        simp [this]
      simp only [Pi.mul_apply, discr_eq, Pi.smul_apply, smul_eq_mul]
      rw [← this]
      field_simp
    refine ⟨((2 * π : ℂ) ^ 12)⁻¹ • CuspForm.discriminantEquiv F, hF, ?_⟩
    intro f' hf'
    ext z
    have h1 := congrFun (hf'.symm.trans hF) z
    have h2 := discr_ne_zero z
    simpa [h2] using h1

/-- The dimension formula after Theorem 3.6 (pdf p. 200): for $k \ge 0$, $\dim M_{2k}(\Gamma_0(1)) = [k/6]$ if
$k \equiv 1 \bmod 6$ and $[k/6] + 1$ otherwise. Milne writes $\Gamma_0(N)$ for $\Gamma_0(1)$ (erratum). -/
@[kb "milne2006ec" "Ch. V, §3, dim M_{2k}(Γ₀(1)) (after Theorem 3.6), pdf p. 200"]
theorem dim_M_level_one (k : ℕ) :
    Module.rank ℂ (ModularForm 𝒮ℒ (2 * k : ℤ)) = if k % 6 = 1 then (k / 6 : ℕ) else (k / 6 + 1 : ℕ) :=
  rank_even_aux k

end NumberFieldKB.MilneEC.V
