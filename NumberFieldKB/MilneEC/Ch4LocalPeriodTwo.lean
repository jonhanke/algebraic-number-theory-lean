import NumberFieldKB.MilneEC.Ch4LocalPeriodCount

/-!
# Non-singular points of a singular Weierstrass cubic over $\mathbb F_2$

For Milne, *Elliptic Curves* (`milne2006ec`), Remark IV.10.6 (c), pdf p. 173, at $p = 2$:
$N_2 = \#\tilde E_{ns}(\mathbb F_2)$ is $1$, $3$, $2$ at split multiplicative, non-split multiplicative and additive
reduction. There are $2^5$ Weierstrass cubics over $\mathbb F_2$; after writing non-singularity and Mathlib's
splitting condition as explicit equations in $a_1, \dots, a_6$, the table is checked by `decide`.

* `card_point_two`: $\#V_{ns}(\mathbb F_2) = 1 + \#\{(x, y) \text{ non-singular}\}$ as an explicit count.
* `splits_quadratic_iff_root`: a quadratic over a field splits iff it has a root.
* `card_reduction_two_of_split`, `_of_nonsplit`, `_of_additive`: $N_2 = 1, 3, 2$; hence `pointCountTwo`.
-/

open Polynomial

namespace NumberFieldKB.MilneEC.LocalPeriod

/-- A quadratic with nonzero leading coefficient over a field splits iff it has a root. -/
lemma splits_quadratic_iff_root {k : Type*} [Field k] {A B C' : k} (hA : A ≠ 0) :
    Splits (C A * X ^ 2 + C B * X - C C') ↔ ∃ x : k, A * x ^ 2 + B * x - C' = 0 := by
  set f := C A * X ^ 2 + C B * X - C C'
  have hdeg : f.natDegree = 2 := by
    simp only [f]; rw [sub_eq_add_neg, ← C_neg]; exact natDegree_quadratic hA
  have hf0 : f ≠ 0 := by intro h; rw [h] at hdeg; simp at hdeg
  constructor
  · intro hs
    have hd : f.degree ≠ 0 := by
      rw [degree_eq_natDegree hf0, hdeg]; exact_mod_cast (by norm_num : (2 : ℕ) ≠ 0)
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero hd
    refine ⟨x, ?_⟩
    simpa [f] using hx
  · rintro ⟨x, hx⟩
    have hroot : f.IsRoot x := by simp [f, hx]
    rw [← mul_divByMonic_eq_iff_isRoot.mpr hroot]
    refine (Splits.X_sub_C x).mul ?_
    have hq0 : f /ₘ (X - C x) ≠ 0 := by
      intro h0
      have := mul_divByMonic_eq_iff_isRoot.mpr hroot
      rw [h0, mul_zero] at this
      exact hf0 this.symm
    have hqdeg : (f /ₘ (X - C x)).natDegree ≤ 1 := by
      have := natDegree_divByMonic f (monic_X_sub_C x)
      rw [this, hdeg, natDegree_X_sub_C]
    have hlc : (f /ₘ (X - C x)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
    letI := invertibleOfNonzero hlc
    exact Splits.of_natDegree_le_one_of_invertible hqdeg inferInstance

/-- The explicit non-singularity condition. -/
def NS2 (a₁ a₂ a₃ a₄ a₆ x y : ZMod 2) : Prop :=
  (y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) ∧
    (a₁ * y - (3 * x ^ 2 + 2 * a₂ * x + a₄) ≠ 0 ∨ 2 * y + a₁ * x + a₃ ≠ 0)

instance (a₁ a₂ a₃ a₄ a₆ x y : ZMod 2) : Decidable (NS2 a₁ a₂ a₃ a₄ a₆ x y) := by
  unfold NS2; infer_instance

/-- The explicit count of affine non-singular points. -/
def cnt2 (a₁ a₂ a₃ a₄ a₆ : ZMod 2) : ℕ :=
  (Finset.univ.filter fun xy : ZMod 2 × ZMod 2 => NS2 a₁ a₂ a₃ a₄ a₆ xy.1 xy.2).card

lemma card_point_two (V : WeierstrassCurve (ZMod 2)) :
    Nat.card V.toAffine.Point = 1 + cnt2 V.a₁ V.a₂ V.a₃ V.a₄ V.a₆ := by
  have e : {xy : ZMod 2 × ZMod 2 // V.toAffine.Nonsingular xy.1 xy.2} ≃
      {xy : ZMod 2 × ZMod 2 // NS2 V.a₁ V.a₂ V.a₃ V.a₄ V.a₆ xy.1 xy.2} :=
    Equiv.subtypeEquivRight fun xy => by
      rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
      exact Iff.rfl
  rw [Nat.card_congr (pointEquivOptionNS V), Finite.card_option, add_comm, Nat.card_congr e,
    Nat.card_eq_fintype_card, Fintype.card_subtype, cnt2]

/-- The explicit discriminant, $c_4$, and Mathlib's splitting quadratic over $\mathbb F_2$. -/
def Δ2 (a₁ a₂ a₃ a₄ a₆ : ZMod 2) : ZMod 2 := (⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve (ZMod 2)).Δ
def c₄2 (a₁ a₂ a₃ a₄ a₆ : ZMod 2) : ZMod 2 := (⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve (ZMod 2)).c₄
def root2 (a₁ a₂ a₃ a₄ a₆ : ZMod 2) : Prop :=
  letI V : WeierstrassCurve (ZMod 2) := ⟨a₁, a₂, a₃, a₄, a₆⟩
  ∃ x : ZMod 2, V.c₄ * x ^ 2 + V.a₁ * V.c₄ * x - (54 * V.b₆ - 3 * V.b₂ * V.b₄ + V.a₂ * V.c₄) = 0

instance (a₁ a₂ a₃ a₄ a₆ : ZMod 2) : Decidable (root2 a₁ a₂ a₃ a₄ a₆) := by
  unfold root2; infer_instance

/-- **The table over $\mathbb F_2$**, by enumeration of the $32$ cubics. -/
theorem table_two : ∀ a₁ a₂ a₃ a₄ a₆ : ZMod 2, Δ2 a₁ a₂ a₃ a₄ a₆ = 0 →
    (c₄2 a₁ a₂ a₃ a₄ a₆ ≠ 0 → (root2 a₁ a₂ a₃ a₄ a₆ → 1 + cnt2 a₁ a₂ a₃ a₄ a₆ = 1) ∧
        (¬ root2 a₁ a₂ a₃ a₄ a₆ → 1 + cnt2 a₁ a₂ a₃ a₄ a₆ = 3)) ∧
      (c₄2 a₁ a₂ a₃ a₄ a₆ = 0 → 1 + cnt2 a₁ a₂ a₃ a₄ a₆ = 2) := by
  decide

lemma eta_Δ (V : WeierstrassCurve (ZMod 2)) : Δ2 V.a₁ V.a₂ V.a₃ V.a₄ V.a₆ = V.Δ := by cases V; rfl
lemma eta_c₄ (V : WeierstrassCurve (ZMod 2)) : c₄2 V.a₁ V.a₂ V.a₃ V.a₄ V.a₆ = V.c₄ := by cases V; rfl
lemma eta_root (V : WeierstrassCurve (ZMod 2)) : root2 V.a₁ V.a₂ V.a₃ V.a₄ V.a₆ ↔
    ∃ x : ZMod 2, V.c₄ * x ^ 2 + V.a₁ * V.c₄ * x - (54 * V.b₆ - 3 * V.b₂ * V.b₄ + V.a₂ * V.c₄) = 0 := by
  cases V; rfl

lemma card_reduction_two_eq (W : WeierstrassCurve ℚ_[2]) [W.IsMinimal ℤ_[2]] :
    Nat.card (W.reduction ℤ_[2]).toAffine.Point =
      1 + cnt2 (reductionZMod W).a₁ (reductionZMod W).a₂ (reductionZMod W).a₃ (reductionZMod W).a₄
        (reductionZMod W).a₆ := by
  rw [← card_point_two, reductionZMod_eq_reduction, card_point_map_equiv (PadicInt.residueField (p := 2))]

lemma c₄_ne_zero_two (W : WeierstrassCurve ℚ_[2]) [hm : W.HasMultiplicativeReduction ℤ_[2]] :
    (reductionZMod W).c₄ ≠ 0 := by
  have := hm.multiplicativeReduction
  rw [← WeierstrassCurve.integralModel_c₄_eq ℤ_[2] W, val_eq_one_iff_toZMod] at this
  rwa [reductionZMod_c₄]

/-- $N_2 = 1$ at split multiplicative reduction. -/
theorem card_reduction_two_of_split (W : WeierstrassCurve ℚ_[2]) [hs : W.HasSplitMultiplicativeReduction ℤ_[2]] :
    Nat.card (W.reduction ℤ_[2]).toAffine.Point = 1 := by
  have hm : W.HasMultiplicativeReduction ℤ_[2] := hs.toHasMultiplicativeReduction
  have hc := c₄_ne_zero_two W
  have hΔ := reductionZMod_Δ_eq_zero W (Or.inl hm)
  have hsplit := (hasSplit_iff W).mp hs
  rw [splits_quadratic_iff_root hc] at hsplit
  have ht := table_two _ _ _ _ _ ((eta_Δ (reductionZMod W)).trans hΔ)
  rw [card_reduction_two_eq]
  exact (ht.1 ((eta_c₄ _).trans_ne hc)).1 ((eta_root _).mpr hsplit)

/-- $N_2 = 3$ at non-split multiplicative reduction. -/
theorem card_reduction_two_of_nonsplit (W : WeierstrassCurve ℚ_[2]) [hm : W.HasMultiplicativeReduction ℤ_[2]]
    (hns : ¬ W.HasSplitMultiplicativeReduction ℤ_[2]) :
    Nat.card (W.reduction ℤ_[2]).toAffine.Point = 3 := by
  have hc := c₄_ne_zero_two W
  have hΔ := reductionZMod_Δ_eq_zero W (Or.inl hm)
  have ht := table_two _ _ _ _ _ ((eta_Δ (reductionZMod W)).trans hΔ)
  rw [card_reduction_two_eq]
  refine (ht.1 ((eta_c₄ _).trans_ne hc)).2 fun hr => hns ?_
  rw [hasSplit_iff, splits_quadratic_iff_root hc]
  exact (eta_root _).mp hr

/-- $N_2 = 2$ at additive reduction. -/
theorem card_reduction_two_of_additive (W : WeierstrassCurve ℚ_[2]) [ha : W.HasAdditiveReduction ℤ_[2]] :
    Nat.card (W.reduction ℤ_[2]).toAffine.Point = 2 := by
  have hc : (reductionZMod W).c₄ = 0 := by
    have := ha.additiveReduction
    rw [← WeierstrassCurve.integralModel_c₄_eq ℤ_[2] W, val_lt_one_iff_toZMod] at this
    rwa [reductionZMod_c₄]
  have hΔ := reductionZMod_Δ_eq_zero W (Or.inr ha)
  have ht := table_two _ _ _ _ _ ((eta_Δ (reductionZMod W)).trans hΔ)
  rw [card_reduction_two_eq]
  exact ht.2 ((eta_c₄ _).trans hc)

end NumberFieldKB.MilneEC.LocalPeriod
