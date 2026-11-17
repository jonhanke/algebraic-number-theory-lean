import NumberFieldKB.MilneEC.Ch4Prop81Kummer

/-!
# Proposition 8.1: the local conditions

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 8.1 (pdf p. 151),
following Silverman (1986), X.4.9.  Over a field $F \supseteq \mathbb Q$ with algebraic closure $\bar F$ and
$G_F = \operatorname{Aut}(\bar F/F)$ acting on $E(\bar F)$ (`gact`), for $d \in \mathbb Q^\times$ and a square root
$u \in \bar F$ of $d$:

* `torsor_neg4p_of_local`: if $\sigma P - P = [\sigma u \ne u]\,T$ for all $\sigma$, then the quartic
  $N^2 = dM^4 - (4p/d)e^4$ has a point over $F$;
* `torsor_p_of_local`: if $\sigma P - P \in E[2]$ and `psi` $(\sigma P - P) = [\sigma u \ne u]$ for all
  $\sigma$, then $N^2 = dM^4 + (p/d)e^4$ has a point over $F$;
* `local_point_of_torsor`: conversely to the first, a point of $N^2 = dM^4 - (4p/d)e^4$ over $F$ gives $P$ with
  $\sigma P - P = [\sigma u \ne u]\,T$.
-/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

-- the algebra structure of `Ch4Selmer` on an algebraic closure, not `DivisionRing.toRatAlgebra`
attribute [local instance 2000] AlgebraicClosure.instAlgebra

namespace NumberFieldKB.MilneEC.Prop81

attribute [local instance] charZero_adicCompletion_rat charZero_completion_rat

variable {p : ℕ} [hp : Fact p.Prime]

variable {F : Type} [Field F] [Algebra ℚ F]

local instance : CharZero F := charZero_of_algebraRat F

/-- The action of $\sigma \in G_F$ on $E(\bar F)$. -/
noncomputable def gact (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    (EC p (AlgebraicClosure F)).Point →+ (EC p (AlgebraicClosure F)).Point :=
  Point.map (W' := (curveP p).toAffine)
    ((AlgEquiv.restrictScalarsHom ℚ σ : AlgebraicClosure F ≃ₐ[ℚ] AlgebraicClosure F) :
      AlgebraicClosure F →ₐ[ℚ] AlgebraicClosure F)

section Gact

variable (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)

theorem gact_apply (x : AlgebraicClosure F) :
    ((AlgEquiv.restrictScalarsHom ℚ σ : AlgebraicClosure F ≃ₐ[ℚ] AlgebraicClosure F) :
      AlgebraicClosure F →ₐ[ℚ] AlgebraicClosure F) x = σ x := rfl

theorem gact_some {x y : AlgebraicClosure F} (h : (EC p (AlgebraicClosure F)).Nonsingular x y) :
    ∃ h' : (EC p (AlgebraicClosure F)).Nonsingular (σ x) (σ y), gact σ (Point.some x y h) = Point.some _ _ h' :=
  ⟨_, rfl⟩

theorem gact_ptT : gact σ (ptT : (EC p (AlgebraicClosure F)).Point) = ptT := map_ptT _

theorem psi_gact (Q : (EC p (AlgebraicClosure F)).Point) : psi (gact σ Q) = psi Q := psi_map _ Q

theorem xc_gact (Q : (EC p (AlgebraicClosure F)).Point) : xc (gact σ Q) = σ (xc Q) := xc_map _ Q

theorem tc_gact (Q : (EC p (AlgebraicClosure F)).Point) : tc (gact σ Q) = σ (tc Q) := by
  cases Q with
  | zero => simp [tc]; rfl
  | @some x y h =>
    show (σ x ^ 2 - p) / (2 * σ y) = σ ((x ^ 2 - p) / (2 * y))
    simp [map_div₀, map_sub, map_pow, map_mul, map_natCast, map_ofNat]

theorem sc_gact (Q : (EC p (AlgebraicClosure F)).Point) : sc (gact σ Q) = σ (sc Q) := by
  cases Q with
  | zero => simp [sc]; rfl
  | @some x y h =>
    show σ y / σ x = σ (y / x)
    simp [map_div₀]

theorem Yc_gact (Q : (EC p (AlgebraicClosure F)).Point) : Yc (gact σ Q) = σ (Yc Q) := by
  cases Q with
  | zero => simp [Yc]; rfl
  | @some x y h =>
    show σ y * (p - σ x ^ 2) / σ x ^ 2 = σ (y * (p - x ^ 2) / x ^ 2)
    simp [map_div₀, map_sub, map_pow, map_mul, map_natCast]

theorem two_smul_gact (Q : (EC p (AlgebraicClosure F)).Point) (h : (2 : ℤ) • Q = 0) :
    (2 : ℤ) • gact σ Q = 0 := by
  rw [← map_zsmul, h, map_zero]

end Gact

/-- A square root of a rational number moved by no automorphism lies in $F$; then the number is a square in
$F$. -/
theorem isSquare_of_fixed {d : ℚ} {u : AlgebraicClosure F} (hu : u ^ 2 = (d : AlgebraicClosure F))
    (h : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ u = u) : IsSquare (d : F) := by
  obtain ⟨k, hk⟩ := mem_range_of_fixed (K := F) h
  refine ⟨k, (algebraMap F (AlgebraicClosure F)).injective ?_⟩
  rw [map_mul, hk, map_ratCast, ← hu]
  ring

theorem ratCast_sqrt {d : ℚ} {u : AlgebraicClosure F} (hu : u ^ 2 = (d : AlgebraicClosure F)) :
    ∃ e : F, u ^ 2 = algebraMap F (AlgebraicClosure F) e :=
  ⟨d, by rw [hu, map_ratCast]⟩

/-- The product of two square roots moved by the same automorphisms is in $F$. -/
theorem prod_mem {d : ℚ} {u w : AlgebraicClosure F} (hu : u ^ 2 = (d : AlgebraicClosure F))
    (hw : ∃ e : F, w ^ 2 = algebraMap F (AlgebraicClosure F) e)
    (h : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ w = w ↔ σ u = u) :
    ∃ k : F, algebraMap F (AlgebraicClosure F) k = w * u :=
  mul_mem_range_of_same_sign hw (ratCast_sqrt hu) h

theorem ne_neg_of_ne_zero {K : Type*} [Field K] [CharZero K] {a : K} (ha : a ≠ 0) : a ≠ -a := by
  intro e; apply ha; linear_combination e / 2

/-- **The local condition for $\hat\varphi$** (kernel part).  If $\sigma P - P = [\sigma u \ne u]\,T$ for every
$\sigma \in G_F$, where $u^2 = d$, then $N^2 = dM^4 - (4p/d)e^4$ has a point over $F$. -/
theorem torsor_neg4p_of_local {d : ℚ} (hd : d ≠ 0) {u : AlgebraicClosure F}
    (hu : u ^ 2 = (d : AlgebraicClosure F)) (P : (EC p (AlgebraicClosure F)).Point)
    (hP : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, gact σ P - P = if σ u = u then 0 else ptT) :
    TorsorSolvable F (-4 * p) d := by
  have hu0 : u ≠ 0 := by
    rintro rfl; apply hd; exact_mod_cast (by rw [← hu]; ring : ((d : ℚ) : AlgebraicClosure F) = 0)
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd
  have hp0 := p_ne_zero (L := F) (p := p)
  -- if `P` is fixed by every automorphism, `d` is a square
  have fixed_case : (∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, gact σ P = P) →
      TorsorSolvable F (-4 * p) d := by
    intro hfix
    refine SelmerExplicit.ts_of_sq_d _ _ (isSquare_of_fixed hu fun σ => ?_)
    by_contra hσ
    have := hP σ
    rw [hfix σ, sub_self, if_neg hσ] at this
    exact ptT_ne_zero this.symm
  cases P with
  | zero => exact fixed_case fun σ => map_zero _
  | @some x y h =>
    by_cases hy : y = 0
    · subst hy
      rcases two_torsion_root h with hx | hx
      · subst hx
        exact fixed_case fun σ => by
          obtain ⟨h', e⟩ := gact_some σ h
          rw [e]; exact some_eq_some' (by simp) (by simp)
      · -- `P = (r, 0)` with `r^2 = -p`
        have hx0 := root_ne_zero hx
        have hxF : ∃ e : F, x ^ 2 = algebraMap F (AlgebraicClosure F) e :=
          ⟨-(p : F), by rw [hx, map_neg, map_natCast]⟩
        have hsame : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ x = x ↔ σ u = u := by
          intro σ
          have hs := hP σ
          obtain ⟨h', e⟩ := gact_some σ h
          rw [e] at hs
          constructor
          · intro hσx
            by_contra hσ
            rw [if_neg hσ] at hs
            have : Point.some (σ x) (σ 0) h' = Point.some x 0 h := some_eq_some' hσx (by simp)
            rw [this, sub_self] at hs
            exact ptT_ne_zero hs.symm
          · intro hσ
            rw [if_pos hσ, sub_eq_zero] at hs
            exact (Point.some.inj hs).1
        obtain ⟨k, hk⟩ := prod_mem hu hxF hsame
        have hk2 : k ^ 2 = -(p : F) * d := by
          apply (algebraMap F (AlgebraicClosure F)).injective
          rw [map_pow, hk, mul_pow, hx, hu, map_mul, map_neg, map_natCast, map_ratCast]
        refine SelmerExplicit.ts_of_sq_cd _ _ ⟨2 * k / d, ?_⟩
        rw [Rat.cast_div, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_natCast]
        field_simp
        linear_combination (-4 : F) * hk2
    · -- a point of order `≠ 2`: `x ≠ 0`
      have heq := eq_of_nonsingular h
      have hx0 : x ≠ 0 := by
        rintro rfl; apply hy; simpa using heq
      obtain ⟨hsT, hYT, hYeq⟩ := sfun_add_T h hx0
      set s := sc (Point.some x y h) with hs_def
      set Y := Yc (Point.some x y h) with hY_def
      have hs0 : s ≠ 0 := by
        simp only [hs_def, sc]; exact div_ne_zero hy hx0
      have hgact : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
          gact σ (Point.some x y h) = Point.some x y h + if σ u = u then 0 else ptT := by
        intro σ; rw [← hP σ]; abel
      have hsσ : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ s = if σ u = u then s else -s := by
        intro σ
        rw [← sc_gact, hgact]
        split_ifs
        · rw [add_zero]
        · exact hsT
      have hYσ : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ Y = Y := by
        intro σ
        rw [← Yc_gact, hgact]
        split_ifs
        · rw [add_zero]
        · exact hYT
      obtain ⟨Y₀, hY₀⟩ := mem_range_of_fixed (K := F) hYσ
      obtain ⟨X₀, hX₀⟩ := mem_range_of_fixed (K := F) (u := s ^ 2) fun σ => by
        rw [map_pow, hsσ]; split_ifs <;> ring
      have hsame : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ s = s ↔ σ u = u := by
        intro σ
        rw [hsσ]
        split_ifs with hσ
        · simp [hσ]
        · simp only [hσ, iff_false]
          exact (ne_neg_of_ne_zero hs0).symm
      obtain ⟨w, hw⟩ := prod_mem hu ⟨X₀, hX₀.symm⟩ hsame
      have inj := (algebraMap F (AlgebraicClosure F)).injective
      have hX0 : X₀ ≠ 0 := by
        intro h0; apply hs0; rw [h0, map_zero] at hX₀; exact pow_eq_zero_iff two_ne_zero |>.1 hX₀.symm
      have hw2 : w ^ 2 = X₀ * d := by
        apply inj; rw [map_pow, hw, mul_pow, map_mul, hX₀, hu, map_ratCast]
      have hE : Y₀ ^ 2 = X₀ ^ 3 - 4 * p * X₀ := by
        apply inj
        rw [map_pow, hY₀, map_sub, map_mul, map_mul, map_pow, hX₀, hYeq, map_ofNat, map_natCast]
      refine ⟨w / X₀ * Y₀ / X₀, 1, w / X₀, Or.inl one_ne_zero, ?_⟩
      rw [Rat.cast_div, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_natCast]
      field_simp
      rw [hE, show w ^ 4 = (w ^ 2) ^ 2 by ring, hw2]
      ring

/-- **The local condition for $\varphi$** (the `psi` part).  If $\sigma P - P \in E[2]$ and
`psi` $(\sigma P - P) = 0 \iff \sigma u = u$ for every $\sigma \in G_F$, where $u^2 = d$, then
$N^2 = dM^4 + (p/d)e^4$ has a point over $F$. -/
theorem torsor_p_of_local {d : ℚ} (hd : d ≠ 0) {u : AlgebraicClosure F}
    (hu : u ^ 2 = (d : AlgebraicClosure F)) (P : (EC p (AlgebraicClosure F)).Point)
    (hP2 : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, (2 : ℤ) • (gact σ P - P) = 0)
    (hψ : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, psi (gact σ P - P) = 0 ↔ σ u = u) :
    TorsorSolvable F p d := by
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd
  have hp0 := p_ne_zero (L := F) (p := p)
  have inj := (algebraMap F (AlgebraicClosure F)).injective
  have hgP : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, gact σ P = P + (gact σ P - P) := fun σ => by
    abel
  have hQfix : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, gact σ ((2 : ℤ) • P) = (2 : ℤ) • P := by
    intro σ
    rw [map_zsmul, hgP σ, zsmul_add, hP2 σ, add_zero]
  rcases hQ : (2 : ℤ) • P with _ | ⟨x₀, y₀, hQns⟩
  · -- `P ∈ E[2]`: the character is trivial
    refine SelmerExplicit.ts_of_sq_d _ _ (isSquare_of_fixed hu fun σ => (hψ σ).1 ?_)
    have h2 : (2 : ℤ) • gact σ P = 0 := two_smul_gact σ P hQ
    have hneg : (2 : ℤ) • (-P) = 0 := by rw [zsmul_neg, hQ]; rfl
    rw [sub_eq_add_neg, psi_add _ _ h2 hneg, psi_gact]
    have : -P = P := by
      rw [neg_eq_iff_add_eq_zero, ← two_zsmul, hQ]; rfl
    rw [this]
    generalize psi P = z
    revert z; decide
  · have hfix0 : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ x₀ = x₀ ∧ σ y₀ = y₀ := by
      intro σ
      have := hQfix σ
      rw [hQ] at this
      obtain ⟨h', e⟩ := gact_some σ hQns
      rw [e] at this
      exact Point.some.inj this
    obtain ⟨X₀, hX₀⟩ := mem_range_of_fixed (K := F) fun σ => (hfix0 σ).1
    obtain ⟨Y₀, hY₀⟩ := mem_range_of_fixed (K := F) fun σ => (hfix0 σ).2
    have heq0 := eq_of_nonsingular hQns
    by_cases hx₀ : x₀ = 0
    · -- `2P = T`
      have hy₀ : y₀ = 0 := by
        rw [hx₀] at heq0; exact pow_eq_zero_iff two_ne_zero |>.1 (by rw [heq0]; ring)
      subst hx₀ hy₀
      obtain ⟨x, y, h, hPe, hx2, hxc⟩ := halving_T P (hQ.trans rfl)
      have hx0 : x ≠ 0 := by
        rintro rfl; apply hp0; exact_mod_cast (by rw [← hx2]; ring : ((p : ℕ) : AlgebraicClosure F) = 0)
      have hsame : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ x = x ↔ σ u = u := by
        intro σ
        rw [← hψ σ]
        have e1 : σ x = xc (gact σ P) := by rw [xc_gact, hPe]; rfl
        have hge : gact σ P = P + (gact σ P - P) := hgP σ
        have h2e := hP2 σ
        rw [e1]
        generalize gact σ P - P = e at h2e hge ⊢
        rw [hge, hxc e h2e]
        split_ifs with hψσ
        · exact iff_of_true rfl hψσ
        · simp only [hψσ, iff_false]
          exact (ne_neg_of_ne_zero hx0).symm
      obtain ⟨k, hk⟩ := prod_mem hu ⟨p, by rw [hx2, map_natCast]⟩ hsame
      have hk2 : k ^ 2 = (p : F) * d := by
        apply inj; rw [map_pow, hk, mul_pow, hx2, hu, map_mul, map_natCast, map_ratCast]
      refine SelmerExplicit.ts_of_sq_cd _ _ ⟨k / d, ?_⟩
      rw [Rat.cast_div, Rat.cast_natCast]
      field_simp
      linear_combination -hk2
    · -- `2P = (x₀, y₀)` with `x₀ ≠ 0`
      obtain ⟨ht2, ht0, htc⟩ := halving_t P hQns hQ hx₀
      set t := tc P with ht_def
      have hsame : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ t = t ↔ σ u = u := by
        intro σ
        rw [← hψ σ, ← tc_gact]
        have hge : gact σ P = P + (gact σ P - P) := hgP σ
        have h2e := hP2 σ
        generalize gact σ P - P = e at h2e hge ⊢
        rw [hge, htc e h2e]
        split_ifs with hψσ
        · exact iff_of_true rfl hψσ
        · simp only [hψσ, iff_false]
          exact (ne_neg_of_ne_zero ht0).symm
      obtain ⟨k, hk⟩ := prod_mem hu ⟨X₀, by rw [ht2, hX₀]⟩ hsame
      have hX0 : X₀ ≠ 0 := by
        intro h0; apply hx₀; rw [← hX₀, h0, map_zero]
      have hk2 : k ^ 2 = X₀ * d := by
        apply inj; rw [map_pow, hk, mul_pow, ht2, hu, map_mul, hX₀, map_ratCast]
      have hE : Y₀ ^ 2 = X₀ ^ 3 + p * X₀ := by
        apply inj
        rw [map_pow, hY₀, map_add, map_mul, map_pow, hX₀, heq0, map_natCast]
      refine ⟨k / X₀ * Y₀ / X₀, 1, k / X₀, Or.inl one_ne_zero, ?_⟩
      rw [Rat.cast_div, Rat.cast_natCast]
      field_simp
      rw [hE, show k ^ 4 = (k ^ 2) ^ 2 by ring, hk2]
      ring

/-- **Local points from the quartic.**  A point of $N^2 = dM^4 - (4p/d)e^4$ over $F$ gives $P \in E(\bar F)$ with
$\sigma P - P = [\sigma u \ne u]\,T$ for every $\sigma \in G_F$, where $u^2 = d$. -/
theorem local_point_of_torsor {d : ℚ} (hd : d ≠ 0) {u : AlgebraicClosure F}
    (hu : u ^ 2 = (d : AlgebraicClosure F)) (h : TorsorSolvable F (-4 * p) d) :
    ∃ P : (EC p (AlgebraicClosure F)).Point,
      ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, gact σ P - P = if σ u = u then 0 else ptT := by
  obtain ⟨N, M, e, hne, heq⟩ := h
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd
  have hp0 := p_ne_zero (L := F) (p := p)
  have hu0 : u ≠ 0 := by
    rintro rfl; apply hd; exact_mod_cast (by rw [← hu]; ring : ((d : ℚ) : AlgebraicClosure F) = 0)
  have hcast : (((-4 * p / d : ℚ)) : F) = -4 * p / d := by
    rw [Rat.cast_div, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_natCast]
  rw [hcast] at heq
  let ι := algebraMap F (AlgebraicClosure F)
  have hσF : ∀ (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (a : F), σ (ι a) = ι a :=
    fun σ a => σ.commutes a
  by_cases he : e = 0
  · -- `d` is a square in `F`: `u ∈ F`
    subst he
    have hM : M ≠ 0 := hne.resolve_right (by simp)
    refine ⟨0, fun σ => ?_⟩
    have hσu : σ u = u := by
      have hsq : (u - ι (N / M ^ 2)) * (u + ι (N / M ^ 2)) = 0 := by
        have : ι (N / M ^ 2) ^ 2 = (d : AlgebraicClosure F) := by
          rw [← map_pow, div_pow, heq, ← map_ratCast ι]
          congr 1
          field_simp
          ring
        linear_combination hu - this
      rcases mul_eq_zero.1 hsq with h0 | h0
      · rw [show u = ι (N / M ^ 2) by linear_combination h0, hσF]
      · rw [show u = -ι (N / M ^ 2) by linear_combination h0, map_neg, hσF]
    rw [if_pos hσu, map_zero, sub_zero]
  by_cases hM : M = 0
  · -- `-pd` is a square: `P = (r, 0)` with `r^2 = -p`
    subst hM
    set k : F := d * N / (2 * e ^ 2) with hk
    have hk2 : k ^ 2 = -(p : F) * d := by
      rw [hk]; field_simp; rw [heq]; field_simp; ring
    set r := ι k / u with hr
    have hr2 : r ^ 2 = -(p : AlgebraicClosure F) := by
      rw [hr, div_pow, ← map_pow, hk2, hu, map_mul, map_neg, map_natCast, map_ratCast]
      field_simp
    have hrns := nonsingular (p := p) (L := AlgebraicClosure F) (x := r) (y := 0)
      (by linear_combination (-r) * hr2)
    refine ⟨Point.some r 0 hrns, fun σ => ?_⟩
    obtain ⟨h', e'⟩ := gact_some σ hrns
    rw [e']
    rcases sq_fixed_sign (ratCast_sqrt hu) σ with hσ | hσ
    · rw [if_pos hσ]
      have : σ r = r := by rw [hr, map_div₀, hσ, hσF]
      rw [sub_eq_zero]
      exact some_eq_some' this (by simp)
    · have hne' : σ u ≠ u := by rw [hσ]; exact (ne_neg_of_ne_zero hu0).symm
      rw [if_neg hne']
      have : σ r = -r := by rw [hr, map_div₀, hσ, hσF, div_neg]
      have hneg : -Point.some r 0 hrns = Point.some r 0 hrns := by
        rw [neg_eq_iff_add_eq_zero, root_add_self]
      rw [sub_eq_add_neg, hneg]
      have h2 : Point.some (σ r) (σ 0) h' = Point.some (-r) 0 (by simpa [this] using h') :=
        some_eq_some' this (by simp)
      rw [h2, add_comm]
      exact root_add_neg_root hr2 hrns _
  · -- the general case: lift the point `(dM^2/e^2, dMN/e^3)` of `E'`
    set X : F := d * M ^ 2 / e ^ 2 with hX
    set Y : F := d * M * N / e ^ 3 with hY
    have hE : Y ^ 2 = X ^ 3 - 4 * p * X := by
      rw [hX, hY]; field_simp; rw [heq]; field_simp; ring
    set s := u * ι (M / e) with hs
    have hs2 : s ^ 2 = ι X := by
      rw [hs, mul_pow, hu, ← map_pow, ← map_ratCast ι, ← map_mul, hX]; congr 1; field_simp
    have hs0 : s ≠ 0 := mul_ne_zero hu0 ((map_ne_zero ι).2 (div_ne_zero hM he))
    have hE' : ι Y ^ 2 = ι X ^ 3 - 4 * p * ι X := by
      rw [← map_pow, hE, map_sub, map_mul, map_mul, map_pow, map_ofNat, map_natCast]
    obtain ⟨hns, hns', hadd⟩ := lift_point (p := p) hE' hs2 hs0
    refine ⟨Point.some _ _ hns, fun σ => ?_⟩
    obtain ⟨h', e'⟩ := gact_some σ hns
    rw [e']
    rcases sq_fixed_sign (ratCast_sqrt hu) σ with hσ | hσ
    · rw [if_pos hσ, sub_eq_zero]
      have hσs : σ s = s := by rw [hs, map_mul, hσ, hσF]
      apply some_eq_some'
      · simp only [map_div₀, map_sub, hσF, hσs, map_ofNat]
      · simp only [map_mul, map_div₀, map_sub, hσF, hσs, map_ofNat]
    · have hne' : σ u ≠ u := by rw [hσ]; exact (ne_neg_of_ne_zero hu0).symm
      rw [if_neg hne', sub_eq_iff_eq_add', hadd]
      have hσs : σ s = -s := by rw [hs, map_mul, hσ, hσF, neg_mul]
      apply some_eq_some'
      · simp only [map_div₀, map_sub, hσF, hσs, map_ofNat]
      · simp only [map_mul, map_div₀, map_sub, hσF, hσs, map_ofNat]

end NumberFieldKB.MilneEC.Prop81
