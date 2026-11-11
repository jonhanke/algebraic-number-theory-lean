import NumberFieldKB.Port.ModularForms.XGammaCompact
import NumberFieldKB.MilneEC.Ch5Quotients
import Mathlib.NumberTheory.Modular
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Milne, *Elliptic Curves*, Proposition V.1.7 (Hausdorff): $X(\Gamma)$ is Hausdorff

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §1, Proposition 1.7 (pdf p. 186).

With the compactness of `XGammaCompact` this proves the named statement `Prop1_7` (`prop_1_7`).

Two points of $\mathbb H^*$ in different $\Gamma$-orbits have open neighbourhoods $U$, $V$ with $\gamma U \cap V =
\emptyset$ for all $\gamma \in \Gamma$ (`separated_of_forall_smul_ne`); since the quotient map is open (the action is by
homeomorphisms, `continuous_smul_hstar`), their images separate the two points of $X(\Gamma)$. The three cases:

* two points of $\mathbb H$: Proposition 1.5 (c) (`prop_1_5`, from the proper discontinuity of the action);
* a point $z \in \mathbb H$ and a cusp $h\infty$: $\Im(gw) \le \max(\Im w, 1/\Im w)$ for every
  $g \in \mathrm{SL}_2(\mathbb Z)$ (`im_smul_le`), so a band $\Im z/2 < \Im w < 2\Im z$ around $z$ never meets
  $h\{\Im > M\}$ for $M$ large;
* two cusps $h\infty$, $k\infty$: if $\Im w > 2$ and $\Im(gw) > 2$ then $g$ fixes $\infty$
  (`c_eq_zero_of_im_gt_two`, Milne's chart at $\infty$), so the horoballs $h\{\Im > 2\}$ and $\gamma k \{\Im > 2\}$
  meet only when $\gamma k\infty = h\infty$.

This is the standard argument (Milne, pdf p. 186; Shimura, *Introduction to the arithmetic theory of automorphic
functions*, §1.5 [unverified]); the modular forms library proves the Hausdorff property for Tau Ceti's compactified
quotient instead, which is a different construction.
-/

open UpperHalfPlane hiding I
open Complex Filter Topology Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups OnePoint Pointwise

namespace NumberFieldKB.MilneEC.V

instance instContinuousConstSMulHStar : ContinuousConstSMul SL(2, ℤ) HStar := ⟨continuous_smul_hstar⟩

instance instContinuousConstSMulHStarSubgroup (Γ : Subgroup SL(2, ℤ)) : ContinuousConstSMul Γ HStar :=
  ⟨fun g => continuous_smul_hstar (g : SL(2, ℤ))⟩

/-- $g\infty = \infty$ exactly when the lower left entry of $g$ vanishes. -/
theorem smul_infty_eq_infty_iff (g : SL(2, ℤ)) : g • (∞ : OnePoint ℚ) = ∞ ↔ g 1 0 = 0 := by
  rw [smul_onePoint_def, OnePoint.smul_infty_eq_self_iff]
  have e : ((mapGL ℚ g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (g 1 0 : ℚ) := rfl
  rw [e]
  exact Int.cast_eq_zero

/-- $\Im(gw) \le \max(\Im w, 1/\Im w)$ for $g \in \mathrm{SL}_2(\mathbb Z)$. -/
theorem im_smul_le (g : SL(2, ℤ)) (w : ℍ) : (g • w).im ≤ max w.im (1 / w.im) := by
  by_cases hc : g 1 0 = 0
  · obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
    rw [hn, T_zpow_smul_im]
    exact le_max_left _ _
  · refine le_trans ?_ (le_max_right _ _)
    have h1 : (1 : ℝ) ≤ (g 1 0 : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ |g 1 0| := Int.one_le_abs hc
      have h' : (1 : ℝ) ≤ |(g 1 0 : ℝ)| := by exact_mod_cast this
      nlinarith [sq_abs (g 1 0 : ℝ), abs_nonneg (g 1 0 : ℝ)]
    rw [ModularGroup.im_smul_eq_div_normSq]
    have hN := normSq_denom_pos g w.im_ne_zero
    have h2 : ((g 1 0 : ℝ) * w.im) ^ 2 ≤
        Complex.normSq (denom (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ)) := by
      simpa using w.c_mul_im_sq_le_normSq_denom g
    have hw := w.im_pos
    rw [div_le_div_iff₀ hN hw]
    nlinarith [mul_pow (g 1 0 : ℝ) w.im 2]

/-- If $a$ and $ga$ both lie in $\{\Im > 2\} \cup \{\infty\}$, then $g$ fixes $\infty$. -/
theorem smul_infty_of_mem_horoInfty_two {g : SL(2, ℤ)} {a : HStar} (ha : a ∈ HStar.horoInfty 2)
    (hga : g • a ∈ HStar.horoInfty 2) : g • (∞ : OnePoint ℚ) = ∞ := by
  induction a using HStar.ind with
  | inl w =>
    rw [mem_horoInfty_inl] at ha
    rw [smul_inl, mem_horoInfty_inl] at hga
    exact (smul_infty_eq_infty_iff g).mpr (c_eq_zero_of_im_gt_two ha hga).1
  | inr c =>
    rw [mem_horoInfty_inr] at ha
    subst ha
    rwa [smul_inr, mem_horoInfty_inr] at hga

/-- Points `x`, `y` of $\mathbb H^*$ are **separated for $\Gamma$**: they have open neighbourhoods $U$, $V$ with
$\gamma U \cap V = \emptyset$ for all $\gamma \in \Gamma$. -/
def Separated (Γ : Subgroup SL(2, ℤ)) (x y : HStar) : Prop :=
  ∃ U V : Set HStar, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ ∀ γ ∈ Γ, ∀ u ∈ U, γ • u ∉ V

theorem Separated.symm {Γ : Subgroup SL(2, ℤ)} {x y : HStar} (h : Separated Γ x y) : Separated Γ y x := by
  obtain ⟨U, V, hU, hV, hx, hy, h⟩ := h
  refine ⟨V, U, hV, hU, hy, hx, fun γ hγ v hv hu => ?_⟩
  exact h γ⁻¹ (Γ.inv_mem hγ) (γ • v) hu (by rwa [inv_smul_smul])

/-- Two points of $\mathbb H$ in different $\Gamma$-orbits are separated (Proposition 1.5 (c)). -/
theorem separated_inl_inl (Γ : Subgroup SL(2, ℤ)) {z w : ℍ} (h : ∀ γ ∈ Γ, γ • z ≠ w) :
    Separated Γ (HStar.inl z) (HStar.inl w) := by
  obtain ⟨U, hU, V, hV, hUV⟩ := (prop_1_5 Γ).2.2 z w h
  obtain ⟨U', hU'U, hU'o, hzU'⟩ := mem_nhds_iff.mp hU
  obtain ⟨V', hV'V, hV'o, hwV'⟩ := mem_nhds_iff.mp hV
  refine ⟨HStar.inl '' U', HStar.inl '' V', isOpen_inl_image hU'o, isOpen_inl_image hV'o,
    ⟨z, hzU', rfl⟩, ⟨w, hwV', rfl⟩, ?_⟩
  rintro γ hγ _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  rw [smul_inl] at hba
  have hab : b = γ • a := Sum.inl_injective hba
  exact Set.disjoint_left.mp (hUV γ hγ) (Set.smul_mem_smul_set (hU'U ha)) (hab ▸ hV'V hb)

/-- A point of $\mathbb H$ and a cusp are separated. -/
theorem separated_inl_cusp (Γ : Subgroup SL(2, ℤ)) (z : ℍ) (c : OnePoint ℚ) :
    Separated Γ (HStar.inl z) (HStar.cusp c) := by
  obtain ⟨h, hh⟩ := exists_smul_infty c
  have hz := z.im_pos
  set B : ℝ := max (2 * z.im) (2 / z.im) with hB
  have hB0 : 0 < B + 1 := by positivity
  refine ⟨HStar.inl '' {w : ℍ | z.im / 2 < w.im ∧ w.im < 2 * z.im},
    (fun x => h • x) '' HStar.horoInfty (B + 1), isOpen_inl_image ?_,
    isOpenMap_smul h _ (isOpen_horoInfty hB0), ⟨z, ⟨by linarith, by linarith⟩, rfl⟩,
    ⟨HStar.cusp ∞, (mem_horoInfty_inr _ _).mpr rfl, by
      show h • HStar.cusp ∞ = HStar.cusp c
      rw [smul_inr, hh]⟩, ?_⟩
  · exact (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
      (isOpen_lt UpperHalfPlane.continuous_im continuous_const)
  · rintro γ - _ ⟨w, ⟨hw1, hw2⟩, rfl⟩ ⟨v, hv, hvw⟩
    have hv' : v = (h⁻¹ * γ) • HStar.inl w := by
      rw [mul_smul, ← hvw, inv_smul_smul]
    rw [hv', smul_inl, mem_horoInfty_inl] at hv
    have hle := im_smul_le (h⁻¹ * γ) w
    have hw := w.im_pos
    have h1 : w.im ≤ B := le_trans hw2.le (le_max_left _ _)
    have h2 : 1 / w.im ≤ B := by
      refine le_trans ?_ (le_max_right _ _)
      rw [div_le_div_iff₀ hw hz]
      linarith
    have := max_le h1 h2
    linarith

/-- Two cusps in different $\Gamma$-orbits are separated. -/
theorem separated_cusp_cusp (Γ : Subgroup SL(2, ℤ)) {c d : OnePoint ℚ} (hcd : ∀ γ ∈ Γ, γ • c ≠ d) :
    Separated Γ (HStar.cusp c) (HStar.cusp d) := by
  obtain ⟨h, hh⟩ := exists_smul_infty c
  obtain ⟨k, hk⟩ := exists_smul_infty d
  have h2 : (0 : ℝ) < 2 := two_pos
  refine ⟨(fun x => h • x) '' HStar.horoInfty 2, (fun x => k • x) '' HStar.horoInfty 2,
    isOpenMap_smul h _ (isOpen_horoInfty h2), isOpenMap_smul k _ (isOpen_horoInfty h2),
    ⟨HStar.cusp ∞, (mem_horoInfty_inr _ _).mpr rfl, by
      show h • HStar.cusp ∞ = HStar.cusp c
      rw [smul_inr, hh]⟩,
    ⟨HStar.cusp ∞, (mem_horoInfty_inr _ _).mpr rfl, by
      show k • HStar.cusp ∞ = HStar.cusp d
      rw [smul_inr, hk]⟩, ?_⟩
  rintro γ hγ _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  have hba' : k • b = γ • h • a := hba
  have hgb : (k⁻¹ * γ * h) • a = b := by
    rw [mul_smul, mul_smul, ← hba', inv_smul_smul]
  have hfix := smul_infty_of_mem_horoInfty_two ha (hgb ▸ hb)
  apply hcd γ hγ
  rw [← hh, ← hk]
  calc γ • h • (∞ : OnePoint ℚ) = k • ((k⁻¹ * γ * h) • (∞ : OnePoint ℚ)) := by
        rw [mul_smul, mul_smul, smul_inv_smul]
    _ = k • (∞ : OnePoint ℚ) := by rw [hfix]

/-- Two points of $\mathbb H^*$ in different $\Gamma$-orbits are separated. -/
theorem separated_of_forall_smul_ne (Γ : Subgroup SL(2, ℤ)) (x y : HStar) (hxy : ∀ γ ∈ Γ, γ • x ≠ y) :
    Separated Γ x y := by
  have hyx : ∀ γ ∈ Γ, γ • y ≠ x := fun γ hγ he =>
    hxy γ⁻¹ (Γ.inv_mem hγ) (by rw [← he, inv_smul_smul])
  induction x using HStar.ind with
  | inl z =>
    induction y using HStar.ind with
    | inl w =>
      exact separated_inl_inl Γ fun γ hγ he => hxy γ hγ (by rw [smul_inl, he])
    | inr d => exact separated_inl_cusp Γ z d
  | inr c =>
    induction y using HStar.ind with
    | inl w => exact (separated_inl_cusp Γ w c).symm
    | inr d =>
      exact separated_cusp_cusp Γ fun γ hγ he => hxy γ hγ (by rw [smul_inr, he])

/-- **Proposition 1.7, Hausdorff** (Milne, *EC*, V, Proposition 1.7, pdf p. 186): $X(\Gamma) = \Gamma\backslash\mathbb H^*$
is Hausdorff for every subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb Z)$ (finite index is not needed). -/
@[kb "milne2006ec" "Ch. V, Proposition 1.7 (Hausdorff), pdf p. 186"]
theorem t2Space_xGamma (Γ : Subgroup SL(2, ℤ)) : T2Space (XGamma Γ) := by
  refine ⟨fun p q hpq => ?_⟩
  revert hpq
  refine Quotient.inductionOn₂ p q fun x y hxy => ?_
  have hsep : ∀ γ ∈ Γ, γ • x ≠ y := by
    intro γ hγ he
    apply hxy
    apply Quotient.sound
    refine MulAction.orbitRel_apply.mpr ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
    show γ⁻¹ • y = x
    rw [← he, inv_smul_smul]
  obtain ⟨U, V, hU, hV, hxU, hyV, h⟩ := separated_of_forall_smul_ne Γ x y hsep
  have hopen := isOpenMap_quotient_mk'_mul (Γ := Γ) (T := HStar)
  refine ⟨Quotient.mk _ '' U, Quotient.mk _ '' V, hopen U hU, hopen V hV, ⟨x, hxU, rfl⟩, ⟨y, hyV, rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hvu)
  exact h γ γ.2 u hu (by rw [show (γ : SL(2, ℤ)) • u = v from hγ]; exact hv)

/-- **Proposition 1.7** (Milne, *EC*, V, Proposition 1.7, pdf p. 186), the named statement `Prop1_7`, proved: for
$\Gamma$ of finite index in $\mathrm{SL}_2(\mathbb Z)$, $\Gamma\backslash\mathbb H^*$ is Hausdorff and compact. -/
@[kb "milne2006ec" "Ch. V, Proposition 1.7, pdf p. 186"]
theorem prop_1_7 : Prop1_7 :=
  ⟨fun Γ _ => t2Space_xGamma Γ, fun Γ hΓ => @compactSpace_xGamma Γ hΓ⟩

end NumberFieldKB.MilneEC.V
