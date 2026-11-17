import NumberFieldKB.MilneEC.Ch4LocalPeriodBad

/-!
# Points of a singular Weierstrass cubic over $\mathbb F_p$, $p$ odd

For Milne, *Elliptic Curves* (`milne2006ec`), Remark IV.10.6 (c), pdf p. 173: at bad reduction
$L_p(E, 1)^{-1} = N_p/p$, i.e. $N_p = \#\tilde E_{ns}(\mathbb F_p)$ is $p - 1$ (split multiplicative), $p + 1$
(non-split multiplicative) or $p$ (additive). Here $p$ is odd.

If $\Psi_2^2 = 4x^3 + b_2x^2 + 2b_4x + b_6$ has a double root $r$ then
$\Psi_2^2 = (x - r)^2(4x + b_2 + 8r)$, $c_4 = s^2$ and $c_6 = -s^3$ with $s = 12r + b_2$, and
$N_p = p - \chi(s)$, $\chi$ the quadratic character. A double root exists when $\Delta = 0$: it is
$r = (18b_6 - b_2b_4)/c_4$ when $c_4 \ne 0$ (as $c_4^2\,\Psi_2^{2\prime}(r) = -144\Delta$ and
$c_4^3\,\Psi_2^2(r) = 4c_6\Delta$), $r = -b_2/12$ when $c_4 = 0$ and $p > 3$, and a cube root of $-b_6$ when $p = 3$.
-/

open Polynomial

namespace NumberFieldKB.MilneEC.LocalPeriod

variable {p : ℕ} [hp : Fact p.Prime]

section DoubleRoot

variable {k : Type*} [Field k] (V : WeierstrassCurve k)

lemma eval_Ψ₂Sq' (x : k) : V.Ψ₂Sq.eval x = 4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆ := by
  simp [WeierstrassCurve.Ψ₂Sq]

lemma four_Δ_eq : 4 * V.Δ = -V.b₂ ^ 2 * (V.b₂ * V.b₆ - V.b₄ ^ 2) - 32 * V.b₄ ^ 3 - 108 * V.b₆ ^ 2 +
    36 * V.b₂ * V.b₄ * V.b₆ := by
  rw [WeierstrassCurve.Δ]
  linear_combination (-V.b₂ ^ 2) * V.b_relation

/-- The node: $r = (18b_6 - b_2b_4)/c_4$ is a double root of $\Psi_2^2$ when $\Delta = 0 \ne c_4$. -/
lemma double_root_of_c₄_ne_zero (hΔ : V.Δ = 0) (hc : V.c₄ ≠ 0) :
    V.Ψ₂Sq.eval ((18 * V.b₆ - V.b₂ * V.b₄) / V.c₄) = 0 ∧
      V.Ψ₂Sq.derivative.eval ((18 * V.b₆ - V.b₂ * V.b₄) / V.c₄) = 0 := by
  set r := (18 * V.b₆ - V.b₂ * V.b₄) / V.c₄
  have hr : V.c₄ * r = 18 * V.b₆ - V.b₂ * V.b₄ := mul_div_cancel₀ _ hc
  have h4 := four_Δ_eq V
  rw [hΔ, mul_zero] at h4
  have hc4 : V.c₄ = V.b₂ ^ 2 - 24 * V.b₄ := rfl
  rw [eval_Ψ₂Sq', LocalPeriod.eval_derivative_Ψ₂Sq]
  constructor
  · have : V.c₄ ^ 3 * (4 * r ^ 3 + V.b₂ * r ^ 2 + 2 * V.b₄ * r + V.b₆) = 0 := by
      rw [hc4] at hr ⊢
      linear_combination (4 * ((V.b₂ ^ 2 - 24 * V.b₄) ^ 2 * r ^ 2 + (V.b₂ ^ 2 - 24 * V.b₄) * r *
        (18 * V.b₆ - V.b₂ * V.b₄) + (18 * V.b₆ - V.b₂ * V.b₄) ^ 2) + V.b₂ * (V.b₂ ^ 2 - 24 * V.b₄) *
        ((V.b₂ ^ 2 - 24 * V.b₄) * r + (18 * V.b₆ - V.b₂ * V.b₄)) +
        2 * V.b₄ * (V.b₂ ^ 2 - 24 * V.b₄) ^ 2) * hr +
        (216 * V.b₆ - 36 * V.b₂ * V.b₄ + V.b₂ ^ 3) * h4
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hc)
  · have : V.c₄ ^ 2 * (12 * r ^ 2 + 2 * V.b₂ * r + 2 * V.b₄) = 0 := by
      rw [hc4] at hr ⊢
      linear_combination (12 * ((V.b₂ ^ 2 - 24 * V.b₄) * r + (18 * V.b₆ - V.b₂ * V.b₄)) +
        2 * V.b₂ * (V.b₂ ^ 2 - 24 * V.b₄)) * hr + 36 * h4
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hc)

variable {V}

lemma Ψ₂Sq_factor {r : k} (h0 : V.Ψ₂Sq.eval r = 0) (h1 : V.Ψ₂Sq.derivative.eval r = 0) (x : k) :
    V.Ψ₂Sq.eval x = (x - r) ^ 2 * (4 * x + V.b₂ + 8 * r) := by
  rw [eval_Ψ₂Sq'] at h0 ⊢
  rw [LocalPeriod.eval_derivative_Ψ₂Sq] at h1
  linear_combination x * h1 + h0 - r * h1

lemma Ψ₂Sq_derivative_factor {r : k} (h1 : V.Ψ₂Sq.derivative.eval r = 0) (x : k) :
    V.Ψ₂Sq.derivative.eval x = 2 * (x - r) * (4 * x + V.b₂ + 8 * r) + 4 * (x - r) ^ 2 := by
  rw [LocalPeriod.eval_derivative_Ψ₂Sq] at h1 ⊢
  linear_combination h1

lemma c₄_of_double_root' {r : k} (h1 : V.Ψ₂Sq.derivative.eval r = 0) :
    V.c₄ = (12 * r + V.b₂) ^ 2 := by
  rw [LocalPeriod.eval_derivative_Ψ₂Sq] at h1
  rw [WeierstrassCurve.c₄]
  linear_combination (-12) * h1

lemma c₆_of_double_root' {r : k} (h0 : V.Ψ₂Sq.eval r = 0) (h1 : V.Ψ₂Sq.derivative.eval r = 0) :
    V.c₆ = -(12 * r + V.b₂) ^ 3 := by
  rw [eval_Ψ₂Sq'] at h0
  rw [LocalPeriod.eval_derivative_Ψ₂Sq] at h1
  rw [WeierstrassCurve.c₆]
  linear_combination 18 * V.b₂ * h1 - 216 * h0 + 216 * r * h1

end DoubleRoot

theorem exists_double_root (hp2 : p ≠ 2) (V : WeierstrassCurve (ZMod p)) (hΔ : V.Δ = 0) :
    ∃ r : ZMod p, V.Ψ₂Sq.eval r = 0 ∧ V.Ψ₂Sq.derivative.eval r = 0 := by
  by_cases hc : V.c₄ = 0
  swap
  · exact ⟨_, double_root_of_c₄_ne_zero V hΔ hc⟩
  have h6 : V.c₆ = 0 := by
    have := V.c_relation
    rw [hΔ, hc] at this
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linear_combination this)
  have h4 := four_Δ_eq V
  rw [hΔ, mul_zero] at h4
  have hc' : V.b₂ ^ 2 - 24 * V.b₄ = 0 := hc
  have h6' : -V.b₂ ^ 3 + 36 * V.b₂ * V.b₄ - 216 * V.b₆ = 0 := h6
  simp only [eval_Ψ₂Sq', LocalPeriod.eval_derivative_Ψ₂Sq]
  by_cases h3 : p = 3
  · subst h3
    have e24 : (24 : ZMod 3) = 0 := rfl
    have e12 : (12 : ZMod 3) = 0 := rfl
    have hb2 : V.b₂ = 0 := by
      rw [e24, zero_mul, sub_zero] at hc'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc'
    have hb4 : V.b₄ = 0 := by
      have e33 : (33 : ZMod 3) = 0 := rfl
      have e108 : (108 : ZMod 3) = 0 := rfl
      have : V.b₄ ^ 3 = 0 := by
        rw [hb2] at h4
        linear_combination (-1 : ZMod 3) * h4 + V.b₄ ^ 3 * e33 + V.b₆ ^ 2 * e108
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this
    refine ⟨-V.b₆, ?_, ?_⟩
    · have hcube : (-V.b₆) ^ 3 = -V.b₆ := ZMod.pow_card _
      have e4 : (4 : ZMod 3) = 1 := rfl
      rw [hcube, hb2, hb4, e4]; ring
    · rw [hb2, hb4, e12]; ring
  · have h2 := two_ne_zero_zmod hp2
    have h3' : (3 : ZMod p) ≠ 0 := by
      intro h
      have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact h3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp this)
    have h12 : (12 : ZMod p) ≠ 0 := by
      have : (12 : ZMod p) = 2 * 2 * 3 := by norm_num
      rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h3'
    refine ⟨-V.b₂ / 12, ?_, ?_⟩
    · have hr : 12 * (-V.b₂ / 12) = -V.b₂ := mul_div_cancel₀ _ h12
      have h1728 : (1728 : ZMod p) ≠ 0 := by
        have : (1728 : ZMod p) = 12 * 12 * 12 := by norm_num
        rw [this]; exact mul_ne_zero (mul_ne_zero h12 h12) h12
      apply (mul_eq_zero.mp _).resolve_left h1728
      generalize -V.b₂ / 12 = r at hr ⊢
      linear_combination (4 * ((12 * r) ^ 2 + 12 * r * (-V.b₂) + V.b₂ ^ 2) +
        12 * V.b₂ * (12 * r + (-V.b₂)) + 288 * V.b₄) * hr - 8 * h6'
    · have hr : 12 * (-V.b₂ / 12) = -V.b₂ := mul_div_cancel₀ _ h12
      apply (mul_eq_zero.mp _).resolve_left h12
      generalize -V.b₂ / 12 = r at hr ⊢
      linear_combination (12 * r + (-V.b₂) + 2 * V.b₂) * hr - hc'

theorem c₄_of_double_root (V : WeierstrassCurve (ZMod p)) {r : ZMod p}
    (h0 : V.Ψ₂Sq.eval r = 0) (h1 : V.Ψ₂Sq.derivative.eval r = 0) :
    V.c₄ = (12 * r + V.b₂) ^ 2 :=
  c₄_of_double_root' h1

theorem c₆_of_double_root (V : WeierstrassCurve (ZMod p)) {r : ZMod p}
    (h0 : V.Ψ₂Sq.eval r = 0) (h1 : V.Ψ₂Sq.derivative.eval r = 0) :
    V.c₆ = -(12 * r + V.b₂) ^ 3 :=
  c₆_of_double_root' h0 h1

theorem card_point_of_double_root (hp2 : p ≠ 2) (V : WeierstrassCurve (ZMod p)) {r : ZMod p}
    (h0 : V.Ψ₂Sq.eval r = 0) (h1 : V.Ψ₂Sq.derivative.eval r = 0) :
    (Nat.card V.toAffine.Point : ℤ) = p - quadraticChar (ZMod p) (12 * r + V.b₂) := by
  classical
  have h2 := two_ne_zero_zmod hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  set β := V.b₂ + 8 * r
  -- the fibre over `r` is bad, every other fibre is good
  have hbad : ¬ GoodFibre V r := by
    intro hg
    obtain ⟨b, hψ⟩ : ∃ b : ZMod p, 2 * b + V.a₁ * r + V.a₃ = 0 :=
      ⟨-(V.a₁ * r + V.a₃) / 2, by field_simp; ring⟩
    have he : V.toAffine.Equation r b := by
      rw [equation_iff_sq hp2, hψ, h0]; ring
    have hns := (WeierstrassCurve.Affine.nonsingular_iff' _ _).mp (hg b he)
    rcases hns.2 with hX | hY
    · apply hX
      apply mul_left_cancel₀ h4
      rw [LocalPeriod.eval_derivative_Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄] at h1
      linear_combination (-1 : ZMod p) * h1 + 2 * V.a₁ * hψ
    · exact hY hψ
  have hgood : ∀ a, a ≠ r → GoodFibre V a := by
    intro a har b he
    by_contra hns
    obtain ⟨hX, hψ⟩ := psi_eq_zero_of_singular V he hns
    have hF : V.Ψ₂Sq.eval a = 0 := by
      rw [← (equation_iff_sq hp2 V a b).mp he, hψ]; ring
    have hF' : V.Ψ₂Sq.derivative.eval a = 0 := by
      rw [LocalPeriod.eval_derivative_Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      linear_combination (-4 : ZMod p) * hX + 2 * V.a₁ * hψ
    have hsub : a - r ≠ 0 := sub_ne_zero.mpr har
    rw [Ψ₂Sq_factor h0 h1] at hF
    have hl : 4 * a + V.b₂ + 8 * r = 0 :=
      (mul_eq_zero.mp hF).resolve_left (pow_ne_zero 2 hsub)
    rw [Ψ₂Sq_derivative_factor h1, hl, mul_zero, zero_add] at hF'
    exact mul_ne_zero h4 (pow_ne_zero 2 hsub) hF'
  have hterm : ∀ a : ZMod p,
      ((if GoodFibre V a then Nat.card {v : ZMod p // v ^ 2 = V.Ψ₂Sq.eval a} else 0 : ℕ) : ℤ) =
        if a = r then 0 else 1 + quadraticChar (ZMod p) (4 * a + β) := by
    intro a
    by_cases har : a = r
    · subst har; simp [hbad]
    · rw [if_neg har, if_pos (hgood a har), natCard_sqrt hp2, Ψ₂Sq_factor h0 h1, map_mul,
        quadraticChar_sq_one' (sub_ne_zero.mpr har), one_mul, add_comm]
      simp only [β, add_assoc]
  have hsum : ∑ a : ZMod p, quadraticChar (ZMod p) (4 * a + β) = 0 := by
    have := quadraticChar_sum_zero hchar
    rw [← this]
    exact Fintype.sum_equiv ((Equiv.mulLeft₀ 4 h4).trans (Equiv.addRight β)) _ _ (fun a => rfl)
  rw [card_point_eq_goodFibre hp2 V, Nat.cast_add, Nat.cast_one, Nat.cast_sum,
    Finset.sum_congr rfl (fun a _ => hterm a)]
  have hsplit : ∑ a : ZMod p, (if a = r then (0 : ℤ) else 1 + quadraticChar (ZMod p) (4 * a + β)) =
      ∑ a : ZMod p, (1 + quadraticChar (ZMod p) (4 * a + β)) - (1 + quadraticChar (ZMod p) (4 * r + β)) := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ r),
      ← Finset.sum_erase_add Finset.univ (fun a => 1 + quadraticChar (ZMod p) (4 * a + β))
        (Finset.mem_univ r), if_pos rfl, add_zero]
    congr 1
    exact Finset.sum_congr rfl fun a ha => if_neg (Finset.ne_of_mem_erase ha)
  rw [hsplit, Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ, ZMod.card]
  have : 4 * r + β = 12 * r + V.b₂ := by simp only [β]; ring
  rw [this]
  simp
  ring

/-! ## Reduction types read on the reduction modulo $p$ -/

section Types

open IsDedekindDomain.HeightOneSpectrum

lemma val_lt_one_iff_toZMod (a : ℤ_[p]) :
    valuation ℚ_[p] (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) (algebraMap ℤ_[p] ℚ_[p] a) < 1 ↔
      PadicInt.toZMod a = 0 := by
  rw [valuation_lt_one_iff_mem, ← not_ne_iff, ← isUnit_iff_toZMod_ne]
  exact (IsLocalRing.mem_maximalIdeal a).trans Iff.rfl

lemma val_eq_one_iff_toZMod (a : ℤ_[p]) :
    valuation ℚ_[p] (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) (algebraMap ℤ_[p] ℚ_[p] a) = 1 ↔
      PadicInt.toZMod a ≠ 0 := by
  constructor
  · intro h h0
    have := (val_lt_one_iff_toZMod a).mpr h0
    rw [h] at this
    exact lt_irrefl _ this
  · intro h
    exact le_antisymm (valuation_le_one _ _)
      (not_lt.mp fun hl => h ((val_lt_one_iff_toZMod a).mp hl))

variable (W : WeierstrassCurve ℚ_[p])

lemma reductionZMod_Δ [W.IsIntegral ℤ_[p]] :
    (reductionZMod W).Δ = PadicInt.toZMod (W.integralModel ℤ_[p]).Δ := by
  rw [reductionZMod, WeierstrassCurve.map_Δ]

lemma reductionZMod_c₄ [W.IsIntegral ℤ_[p]] :
    (reductionZMod W).c₄ = PadicInt.toZMod (W.integralModel ℤ_[p]).c₄ := by
  rw [reductionZMod, WeierstrassCurve.map_c₄]

lemma reductionZMod_Δ_eq_zero [W.IsMinimal ℤ_[p]]
    (hW : W.HasMultiplicativeReduction ℤ_[p] ∨ W.HasAdditiveReduction ℤ_[p]) : (reductionZMod W).Δ = 0 := by
  have h : valuation ℚ_[p] (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) W.Δ < 1 := by
    rcases hW with h | h
    · exact h.badReduction
    · exact h.badReduction
  rw [← WeierstrassCurve.integralModel_Δ_eq ℤ_[p] W, val_lt_one_iff_toZMod] at h
  rw [reductionZMod_Δ, h]

end Types

/-! ## Splitting of the tangent quadratic -/

lemma splits_quadratic_iff (hp2 : p ≠ 2) {A B C' : ZMod p} (hA : A ≠ 0) :
    Splits (C A * X ^ 2 + C B * X - C C') ↔ IsSquare (B ^ 2 + 4 * A * C') := by
  have h2 := two_ne_zero_zmod hp2
  constructor
  · intro hs
    have hdeg : (C A * X ^ 2 + C B * X - C C').degree ≠ 0 := by
      have hn : (C A * X ^ 2 + C B * X - C C').natDegree = 2 := by
        rw [sub_eq_add_neg, ← C_neg]; exact natDegree_quadratic hA
      intro h0
      have hn0 := natDegree_eq_of_degree_eq_some h0
      rw [hn] at hn0
      exact absurd hn0 (by norm_num)
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero hdeg
    simp only [eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hx
    exact ⟨2 * A * x + B, by linear_combination (-4) * A * hx⟩
  · rintro ⟨d, hd⟩
    have h2A : 2 * A ≠ 0 := mul_ne_zero h2 hA
    set r₁ := (-B + d) / (2 * A)
    set r₂ := (-B - d) / (2 * A)
    have e1 : 2 * A * r₁ = -B + d := mul_div_cancel₀ _ h2A
    have e2 : 2 * A * r₂ = -B - d := mul_div_cancel₀ _ h2A
    have hsum : A * (r₁ + r₂) = -B := by
      apply mul_left_cancel₀ h2; linear_combination e1 + e2
    have hprod : A * (r₁ * r₂) = -C' := by
      apply mul_left_cancel₀ (mul_ne_zero h2 h2A)
      linear_combination (2 * A * r₂) * e1 + (-B + d) * e2 + hd
    have hf : C A * X ^ 2 + C B * X - C C' = C A * ((X - C r₁) * (X - C r₂)) := by
      have hB : C B = -(C A * C (r₁ + r₂)) := by rw [← C_mul, hsum, C_neg, neg_neg]
      have hC : C C' = -(C A * C (r₁ * r₂)) := by rw [← C_mul, hprod, C_neg, neg_neg]
      rw [hB, hC, C_add, C_mul]
      ring
    rw [hf]
    exact ((Splits.X_sub_C _).mul (Splits.X_sub_C _)).C_mul _

/-! ## $N_p$ at bad reduction -/

/-- The splitting condition of Mathlib's `HasSplitMultiplicativeReduction`, read over `ZMod p`. -/
lemma hasSplit_iff (W : WeierstrassCurve ℚ_[p]) [hm : W.HasMultiplicativeReduction ℤ_[p]] :
    W.HasSplitMultiplicativeReduction ℤ_[p] ↔
      Splits (C (reductionZMod W).c₄ * X ^ 2 + C ((reductionZMod W).a₁ * (reductionZMod W).c₄) * X -
        C (54 * (reductionZMod W).b₆ - 3 * (reductionZMod W).b₂ * (reductionZMod W).b₄ +
          (reductionZMod W).a₂ * (reductionZMod W).c₄)) := by
  set I := W.integralModel ℤ_[p]
  set P : (ℤ_[p])[X] := C I.c₄ * X ^ 2 + C (I.a₁ * I.c₄) * X - C (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)
  set φ : IsLocalRing.ResidueField ℤ_[p] ≃+* ZMod p := PadicInt.residueField
  have hcomp : (φ : IsLocalRing.ResidueField ℤ_[p] →+* ZMod p).comp
      (algebraMap ℤ_[p] (IsLocalRing.ResidueField ℤ_[p])) = PadicInt.toZMod := rfl
  have hmapZ : (P.map (algebraMap ℤ_[p] (IsLocalRing.ResidueField ℤ_[p]))).map
      (φ : IsLocalRing.ResidueField ℤ_[p] →+* ZMod p) =
      C (reductionZMod W).c₄ * X ^ 2 + C ((reductionZMod W).a₁ * (reductionZMod W).c₄) * X -
        C (54 * (reductionZMod W).b₆ - 3 * (reductionZMod W).b₂ * (reductionZMod W).b₄ +
          (reductionZMod W).a₂ * (reductionZMod W).c₄) := by
    rw [Polynomial.map_map, hcomp]
    simp only [P, reductionZMod, WeierstrassCurve.map_c₄, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, Polynomial.map_sub,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      map_sub, map_add, map_mul, map_ofNat, I, Polynomial.map_ofNat, C_mul, C_sub, C_add, C_ofNat]
  rw [← hmapZ]
  constructor
  · intro h
    exact h.splitMultiplicativeReduction.map _
  · intro h
    refine ⟨?_⟩
    have := h.map (φ.symm : ZMod p →+* IsLocalRing.ResidueField ℤ_[p])
    rwa [Polynomial.map_map, show ((φ.symm : ZMod p →+* IsLocalRing.ResidueField ℤ_[p]).comp
      (φ : IsLocalRing.ResidueField ℤ_[p] →+* ZMod p)) = RingHom.id _ from
        RingHom.ext fun x => φ.symm_apply_apply x, Polynomial.map_id] at this

lemma isSquare_pow_five_iff {s : ZMod p} (hs : s ≠ 0) : IsSquare (s ^ 5) ↔ IsSquare s := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d / s ^ 2, ?_⟩
    rw [div_mul_div_comm, ← hd, eq_div_iff (by positivity)]
    ring
  · rintro ⟨t, rfl⟩
    exact ⟨t ^ 5, by ring⟩

/-- The discriminant of the tangent quadratic is $-c_4c_6 = s^5$, $s = 12r + b_2$. -/
lemma disc_eq (V : WeierstrassCurve (ZMod p)) {r : ZMod p} (h0 : V.Ψ₂Sq.eval r = 0)
    (h1 : V.Ψ₂Sq.derivative.eval r = 0) :
    (12 * r + V.b₂) ^ 5 = (V.a₁ * V.c₄) ^ 2 + 4 * V.c₄ * (54 * V.b₆ - 3 * V.b₂ * V.b₄ + V.a₂ * V.c₄) := by
  have e4 := c₄_of_double_root V h0 h1
  have e6 := c₆_of_double_root V h0 h1
  have hb2 : V.b₂ = V.a₁ ^ 2 + 4 * V.a₂ := rfl
  have hc4 : V.c₄ = V.b₂ ^ 2 - 24 * V.b₄ := rfl
  have hc6 : V.c₆ = -V.b₂ ^ 3 + 36 * V.b₂ * V.b₄ - 216 * V.b₆ := rfl
  set s := 12 * r + V.b₂
  linear_combination V.c₆ * e4 + s ^ 2 * e6 - V.c₄ * hc6 + V.c₄ ^ 2 * hb2 - V.c₄ * V.b₂ * hc4

/-- The bad-reduction data: a double root `r` of $\Psi_2^2$ modulo $p$, and $N_p = p - \chi(12r + b_2)$. -/
lemma bad_data (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p]) [W.IsMinimal ℤ_[p]]
    (hW : W.HasMultiplicativeReduction ℤ_[p] ∨ W.HasAdditiveReduction ℤ_[p]) :
    ∃ r : ZMod p, (reductionZMod W).Ψ₂Sq.eval r = 0 ∧ (reductionZMod W).Ψ₂Sq.derivative.eval r = 0 ∧
      (Nat.card (W.reduction ℤ_[p]).toAffine.Point : ℤ) =
        p - quadraticChar (ZMod p) (12 * r + (reductionZMod W).b₂) := by
  obtain ⟨r, h0, h1⟩ := exists_double_root hp2 _ (reductionZMod_Δ_eq_zero W hW)
  refine ⟨r, h0, h1, ?_⟩
  rw [← card_point_of_double_root hp2 _ h0 h1, reductionZMod_eq_reduction,
    card_point_map_equiv (PadicInt.residueField (p := p))]

/-- $N_p$ at split multiplicative reduction, $p$ odd. -/
theorem card_reduction_of_split (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p])
    [hs : W.HasSplitMultiplicativeReduction ℤ_[p]] :
    Nat.card (W.reduction ℤ_[p]).toAffine.Point = p - 1 := by
  have hm : W.HasMultiplicativeReduction ℤ_[p] := hs.toHasMultiplicativeReduction
  obtain ⟨r, h0, h1, hN⟩ := bad_data hp2 W (Or.inl hm)
  have h := (hasSplit_iff W).mp hs
  set V := reductionZMod W
  have hc : V.c₄ ≠ 0 := by
    have := hm.multiplicativeReduction
    rw [← WeierstrassCurve.integralModel_c₄_eq ℤ_[p] W, val_eq_one_iff_toZMod] at this
    rwa [reductionZMod_c₄]
  have hs0 : 12 * r + V.b₂ ≠ 0 := by
    intro h; apply hc; rw [c₄_of_double_root V h0 h1, h]; ring
  have hsq : IsSquare (12 * r + V.b₂) := by
    rw [splits_quadratic_iff hp2 hc] at h
    rw [← isSquare_pow_five_iff hs0]
    convert h using 1
    exact disc_eq V h0 h1
  rw [(quadraticChar_one_iff_isSquare hs0).mpr hsq] at hN
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  omega

/-- $N_p$ at non-split multiplicative reduction, $p$ odd. -/
theorem card_reduction_of_nonsplit (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p])
    [hm : W.HasMultiplicativeReduction ℤ_[p]] (hns : ¬ W.HasSplitMultiplicativeReduction ℤ_[p]) :
    Nat.card (W.reduction ℤ_[p]).toAffine.Point = p + 1 := by
  obtain ⟨r, h0, h1, hN⟩ := bad_data hp2 W (Or.inl hm)
  set V := reductionZMod W
  have hc : V.c₄ ≠ 0 := by
    have := hm.multiplicativeReduction
    rw [← WeierstrassCurve.integralModel_c₄_eq ℤ_[p] W, val_eq_one_iff_toZMod] at this
    rwa [reductionZMod_c₄]
  have hs0 : 12 * r + V.b₂ ≠ 0 := by
    intro h; apply hc; rw [c₄_of_double_root V h0 h1, h]; ring
  have hsq : ¬ IsSquare (12 * r + V.b₂) := by
    intro hsq
    apply hns
    rw [hasSplit_iff, splits_quadratic_iff hp2 hc]
    rw [← isSquare_pow_five_iff hs0] at hsq
    convert hsq using 1
    exact (disc_eq V h0 h1).symm
  rw [quadraticChar_neg_one_iff_not_isSquare.mpr hsq] at hN
  omega

/-- $N_p$ at additive reduction, $p$ odd. -/
theorem card_reduction_of_additive (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p])
    [ha : W.HasAdditiveReduction ℤ_[p]] :
    Nat.card (W.reduction ℤ_[p]).toAffine.Point = p := by
  obtain ⟨r, h0, h1, hN⟩ := bad_data hp2 W (Or.inr ha)
  set V := reductionZMod W
  have hc : V.c₄ = 0 := by
    have := ha.additiveReduction
    rw [← WeierstrassCurve.integralModel_c₄_eq ℤ_[p] W, val_lt_one_iff_toZMod] at this
    rwa [reductionZMod_c₄]
  have hs0 : 12 * r + V.b₂ = 0 := by
    rw [c₄_of_double_root V h0 h1] at hc
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc
  rw [hs0, quadraticChar_zero, sub_zero] at hN
  exact_mod_cast hN

end NumberFieldKB.MilneEC.LocalPeriod
