import NumberFieldKB.MilneEC.Ch1BezoutDefs

/-!
# Bezout's theorem: the dimension count

Part of the proof of Milne, *Elliptic Curves*, Theorem I.1.18 (Bezout), after Fulton 1969, §5.3 (the
dimension count), done in the affine plane: if the leading forms $f_m$, $g_n$ of `f` and `g` have no
common factor (the curves do not meet on the line at infinity), then $K[X, Y]/(f, g)$ is finite
dimensional of dimension $mn$. Over any field.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC.Bezout

section Homog

variable {σ R : Type*} [CommRing R]

/-- All monomials of `x` have degree `< B`. -/
def LtDeg (B : ℕ) (x : MvPolynomial σ R) : Prop :=
  ∀ i, B ≤ i → homogeneousComponent i x = 0

lemma hc_of_isHom {x : MvPolynomial σ R} {n : ℕ} (h : x.IsHomogeneous n) (j : ℕ) :
    homogeneousComponent j x = if j = n then x else 0 :=
  homogeneousComponent_of_mem h

lemma ltDeg_of_totalDegree_le {x : MvPolynomial σ R} {p : ℕ} (h : x.totalDegree ≤ p) :
    LtDeg (p + 1) x := fun i hi => homogeneousComponent_eq_zero i x (by omega)

lemma ltDeg_zero {x : MvPolynomial σ R} (h : LtDeg 0 x) : x = 0 := by
  rw [← sum_homogeneousComponent x]
  exact Finset.sum_eq_zero fun i _ => h i (Nat.zero_le _)

lemma totalDegree_le_of_ltDeg {x : MvPolynomial σ R} {p : ℕ} (h : LtDeg (p + 1) x) :
    x.totalDegree ≤ p := by
  rw [← sum_homogeneousComponent x]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  by_cases hi : i ≤ p
  · exact ((homogeneousComponent_isHomogeneous i x).totalDegree_le).trans hi
  · rw [h i (by omega)]; simp

lemma eq_zero_or_totalDegree_lt {x : MvPolynomial σ R} {B : ℕ} (h : LtDeg B x) :
    x = 0 ∨ x.totalDegree < B := by
  cases B with
  | zero => exact Or.inl (ltDeg_zero h)
  | succ b => exact Or.inr (Nat.lt_succ_of_le (totalDegree_le_of_ltDeg h))

lemma ltDeg_mul {x y : MvPolynomial σ R} {B q : ℕ} (hx : LtDeg B x) (hy : y.totalDegree ≤ q) :
    LtDeg (B + q) (x * y) := by
  intro i hi
  rcases eq_zero_or_totalDegree_lt hx with h | h
  · simp [h]
  · exact homogeneousComponent_eq_zero i _
      (lt_of_le_of_lt (totalDegree_mul x y) (by omega))

lemma ltDeg_sub_hc {x : MvPolynomial σ R} {p : ℕ} (h : x.totalDegree ≤ p) :
    LtDeg p (x - homogeneousComponent p x) := by
  intro i hi
  rw [map_sub, hc_of_isHom (homogeneousComponent_isHomogeneous p x) i]
  rcases Nat.eq_or_lt_of_le hi with h1 | h1
  · subst h1; simp
  · rw [homogeneousComponent_eq_zero i x (by omega)]
    simp [Nat.ne_of_gt h1]

/-- The top form of a product (Fulton). -/
theorem hc_mul_top {x y : MvPolynomial σ R} {p q : ℕ} (hx : x.totalDegree ≤ p)
    (hy : y.totalDegree ≤ q) :
    homogeneousComponent (p + q) (x * y) = homogeneousComponent p x * homogeneousComponent q y := by
  have hx' := ltDeg_sub_hc hx
  have hy' := ltDeg_sub_hc hy
  set xp := homogeneousComponent p x with hxp
  set yq := homogeneousComponent q y with hyq
  have hxpd : xp.totalDegree ≤ p := (homogeneousComponent_isHomogeneous p x).totalDegree_le
  have e : x * y = xp * yq + (xp * (y - yq) + (x - xp) * y) := by ring
  rw [e, map_add, map_add]
  have h1 : homogeneousComponent (p + q) (xp * yq) = xp * yq :=
    homogeneousComponent_eq_self ((homogeneousComponent_isHomogeneous p x).mul
      (homogeneousComponent_isHomogeneous q y))
  have h2 : homogeneousComponent (p + q) (xp * (y - yq)) = 0 := by
    rw [mul_comm]; exact ltDeg_mul hy' hxpd (p + q) (by omega)
  have h3 : homogeneousComponent (p + q) ((x - xp) * y) = 0 :=
    ltDeg_mul hx' hy (p + q) le_rfl
  rw [h1, h2, h3]; simp

/-- Multiplying by a homogeneous polynomial shifts the homogeneous components. -/
theorem hc_mul_homog {G : MvPolynomial σ R} {n : ℕ} (hG : G.IsHomogeneous n)
    (x : MvPolynomial σ R) (j : ℕ) :
    homogeneousComponent j (x * G) =
      if n ≤ j then homogeneousComponent (j - n) x * G else 0 := by
  induction x using MvPolynomial.induction_on' with
  | monomial d r =>
    have h1 : (monomial d r).IsHomogeneous d.degree := isHomogeneous_monomial r rfl
    rw [hc_of_isHom (h1.mul hG), hc_of_isHom h1]
    split_ifs <;> first | rfl | (exfalso; omega) | simp
  | add p q hp hq =>
    rw [add_mul, map_add, hp, hq, map_add, add_mul]
    split_ifs <;> simp

lemma ltDeg_step {x y : MvPolynomial σ R} {p : ℕ} (hx : LtDeg (p + 1) x)
    (hy : y.totalDegree ≤ p) (h : homogeneousComponent p x + homogeneousComponent p y = 0) :
    LtDeg p (x + y) := by
  intro i hi
  rw [map_add]
  rcases Nat.eq_or_lt_of_le hi with h1 | h1
  · subst h1; exact h
  · rw [hx i h1, homogeneousComponent_eq_zero i y (by omega)]; simp

end Homog

section Reduce

variable {K : Type*} [Field K]

/-- Syzygies of relatively prime forms. -/
lemma form_syzygy {F G α β : MvPolynomial (Fin 2) K} {p n : ℕ}
    (hF : F ≠ 0) (hG : G ≠ 0) (hGh : G.IsHomogeneous n) (hcop : IsRelPrime F G)
    (hα : α.IsHomogeneous p) (h : α * F + β * G = 0) :
    ∃ c : MvPolynomial (Fin 2) K, (c = 0 ∨ ∃ s, c.IsHomogeneous s ∧ p = s + n) ∧
      α = c * G ∧ β = -(c * F) := by
  have hdvd : F ∣ β * G := ⟨-α, by linear_combination h⟩
  obtain ⟨c', hc'⟩ := hcop.dvd_of_dvd_mul_right hdvd
  have hα' : α = -c' * G := by
    refine mul_left_cancel₀ hF ?_
    rw [hc'] at h
    linear_combination h
  have hαp : α = homogeneousComponent p α := (homogeneousComponent_eq_self hα).symm
  have key : ∀ c : MvPolynomial (Fin 2) K, α = c * G → β = -(c * F) := by
    intro c hc
    refine mul_right_cancel₀ hG ?_
    rw [hc] at h
    linear_combination h
  by_cases hnp : n ≤ p
  · refine ⟨homogeneousComponent (p - n) (-c'), Or.inr ⟨p - n,
      homogeneousComponent_isHomogeneous _ _, by omega⟩, ?_⟩
    have : α = homogeneousComponent (p - n) (-c') * G := by
      rw [hαp, hα', hc_mul_homog hGh, if_pos hnp]
    exact ⟨this, key _ this⟩
  · have h0 : α = 0 := by
      rw [hαp, hα', hc_mul_homog hGh, if_neg hnp]
    have : α = 0 * G := by rw [h0]; simp
    exact ⟨0, Or.inl rfl, this, key _ this⟩

/-- The reduction step: the degree-`p` corrections `c * g`, `c * f` killing the top forms. -/
lemma step_corr {f g a b : MvPolynomial (Fin 2) K} {m n p q : ℕ}
    (hf : f.totalDegree ≤ m) (hg : g.totalDegree ≤ n)
    (hfm : homogeneousComponent m f ≠ 0) (hgn : homogeneousComponent n g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent m f) (homogeneousComponent n g))
    (hap : a.totalDegree ≤ p) (hbq : b.totalDegree ≤ q) (hpq : p + m = q + n)
    (h : homogeneousComponent (p + m) (a * f + b * g) = 0) :
    ∃ c : MvPolynomial (Fin 2) K, (c * g).totalDegree ≤ p ∧ (c * f).totalDegree ≤ q ∧
      homogeneousComponent p (c * g) = homogeneousComponent p a ∧
      homogeneousComponent q (c * f) = -homogeneousComponent q b := by
  have e1 := hc_mul_top hap hf
  have e2 : homogeneousComponent (p + m) (b * g) =
      homogeneousComponent q b * homogeneousComponent n g := by
    rw [hpq]; exact hc_mul_top hbq hg
  rw [map_add, e1, e2] at h
  obtain ⟨c, hc, hα, hβ⟩ := form_syzygy hfm hgn (homogeneousComponent_isHomogeneous n g) hcop
    (homogeneousComponent_isHomogeneous p a) h
  rcases hc with rfl | ⟨s, hs, hps⟩
  · refine ⟨0, by simp, by simp, ?_, ?_⟩
    · rw [hα]; simp
    · rw [hβ]; simp
  · have hq : q = s + m := by omega
    have h1 : (c * g).totalDegree ≤ p := by
      rw [hps]; exact (totalDegree_mul _ _).trans (add_le_add hs.totalDegree_le hg)
    have h2 : (c * f).totalDegree ≤ q := by
      rw [hq]; exact (totalDegree_mul _ _).trans (add_le_add hs.totalDegree_le hf)
    refine ⟨c, h1, h2, ?_, ?_⟩
    · rw [hps, hc_mul_top hs.totalDegree_le hg, hc_of_isHom hs, if_pos rfl, ← hps]
      exact hα.symm
    · rw [hq, hc_mul_top hs.totalDegree_le hf, hc_of_isHom hs, if_pos rfl, ← hq]
      rw [hβ]; simp

/-- The reduction (Fulton §5.3, Lemma). -/
theorem reduce_aux {f g : MvPolynomial (Fin 2) K} {m n : ℕ}
    (hf : f.totalDegree ≤ m) (hg : g.totalDegree ≤ n)
    (hfm : homogeneousComponent m f ≠ 0) (hgn : homogeneousComponent n g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent m f) (homogeneousComponent n g))
    {A B D : ℕ} (hA : A + m = D) (hB : B + n = D) :
    ∀ (j : ℕ) (a b : MvPolynomial (Fin 2) K), LtDeg (A + j) a → LtDeg (B + j) b →
      LtDeg D (a * f + b * g) →
      ∃ c : MvPolynomial (Fin 2) K, LtDeg A (a - c * g) ∧ LtDeg B (b + c * f) := by
  intro j
  induction j with
  | zero => intro a b ha hb _; exact ⟨0, by simpa using ha, by simpa using hb⟩
  | succ j ih =>
    intro a b ha hb hh
    have hap : a.totalDegree ≤ A + j := totalDegree_le_of_ltDeg ha
    have hbq : b.totalDegree ≤ B + j := totalDegree_le_of_ltDeg hb
    obtain ⟨c0, h1, h2, h3, h4⟩ := step_corr hf hg hfm hgn hcop hap hbq (by omega)
      (hh _ (by omega))
    have ha' : LtDeg (A + j) (a - c0 * g) := by
      have := ltDeg_step (p := A + j) (x := a) (y := -(c0 * g)) ha (by simpa using h1)
        (by rw [map_neg, h3]; simp)
      simpa [sub_eq_add_neg] using this
    have hb' : LtDeg (B + j) (b + c0 * f) :=
      ltDeg_step hb h2 (by rw [h4]; simp)
    have e : (a - c0 * g) * f + (b + c0 * f) * g = a * f + b * g := by ring
    obtain ⟨c1, k1, k2⟩ := ih _ _ ha' hb' (by rw [e]; exact hh)
    refine ⟨c0 + c1, ?_, ?_⟩
    · have : a - (c0 + c1) * g = (a - c0 * g) - c1 * g := by ring
      rw [this]; exact k1
    · have : b + (c0 + c1) * f = (b + c0 * f) + c1 * f := by ring
      rw [this]; exact k2

/-- Lemma A (Fulton §5.3): bounded-degree representations. -/
theorem exists_repr_of_mem_span_of_isRelPrime_top {f g h : MvPolynomial (Fin 2) K} {m n d : ℕ}
    (hf : f.totalDegree ≤ m) (hg : g.totalDegree ≤ n)
    (hfm : homogeneousComponent m f ≠ 0) (hgn : homogeneousComponent n g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent m f) (homogeneousComponent n g))
    (hh : h ∈ Ideal.span {f, g}) (hd : h.totalDegree ≤ d) (hmd : m ≤ d) (hnd : n ≤ d) :
    ∃ a b : MvPolynomial (Fin 2) K, h = a * f + b * g ∧ a.totalDegree ≤ d - m ∧
      b.totalDegree ≤ d - n := by
  obtain ⟨a0, b0, hab⟩ := Ideal.mem_span_pair.1 hh
  obtain ⟨c, k1, k2⟩ := reduce_aux hf hg hfm hgn hcop (A := d - m + 1) (B := d - n + 1)
    (D := d + 1) (by omega) (by omega) (a0.totalDegree + b0.totalDegree + 1) a0 b0
    (fun i hi => homogeneousComponent_eq_zero i a0 (by omega))
    (fun i hi => homogeneousComponent_eq_zero i b0 (by omega))
    (by rw [hab]; exact ltDeg_of_totalDegree_le hd)
  refine ⟨a0 - c * g, b0 + c * f, ?_, totalDegree_le_of_ltDeg k1, totalDegree_le_of_ltDeg k2⟩
  rw [← hab]; ring

/-- Syzygies of `f, g`. -/
theorem syzygy_of_isRelPrime_top {f g : MvPolynomial (Fin 2) K} {m n : ℕ}
    (hf : f.totalDegree ≤ m) (hg : g.totalDegree ≤ n)
    (hfm : homogeneousComponent m f ≠ 0) (hgn : homogeneousComponent n g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent m f) (homogeneousComponent n g))
    {a b : MvPolynomial (Fin 2) K} (h : a * f + b * g = 0) :
    ∃ c : MvPolynomial (Fin 2) K, a = c * g ∧ b = -(c * f) := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hfm
  have hg0 : g ≠ 0 := by rintro rfl; simp at hgn
  obtain ⟨c, k1, k2⟩ := reduce_aux hf hg hfm hgn hcop (A := max m n - m) (B := max m n - n)
    (D := max m n) (by omega) (by omega) (a.totalDegree + b.totalDegree + max m n + 1) a b
    (fun i hi => homogeneousComponent_eq_zero i a (by omega))
    (fun i hi => homogeneousComponent_eq_zero i b (by omega))
    (by rw [h]; intro i _; simp)
  have e : (a - c * g) * f + (b + c * f) * g = 0 := by linear_combination h
  have key : a - c * g = 0 ∧ b + c * f = 0 := by
    rcases le_total m n with hmn | hmn
    · have hb : b + c * f = 0 := by
        apply ltDeg_zero
        have : max m n - n = 0 := by omega
        rwa [this] at k2
      rw [hb, zero_mul, add_zero] at e
      exact ⟨(mul_eq_zero.1 e).resolve_right hf0, hb⟩
    · have ha : a - c * g = 0 := by
        apply ltDeg_zero
        have : max m n - m = 0 := by omega
        rwa [this] at k1
      rw [ha, zero_mul, zero_add] at e
      exact ⟨ha, (mul_eq_zero.1 e).resolve_right hg0⟩
  exact ⟨c, by linear_combination key.1, by linear_combination key.2⟩

end Reduce

section Count

/-- The pairs `(i, j)` with `i + j ≤ e`. -/
def triSet (e : ℕ) : Finset (ℕ × ℕ) := (Finset.range (e + 1)).biUnion Finset.antidiagonal

lemma mem_triSet {e : ℕ} {x : ℕ × ℕ} : x ∈ triSet e ↔ x.1 + x.2 ≤ e := by
  simp only [triSet, Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
  constructor
  · rintro ⟨t, ht, h⟩; omega
  · intro h; exact ⟨_, by omega, rfl⟩

lemma sum_succ_mul_two (e : ℕ) :
    (∑ t ∈ Finset.range (e + 1), (t + 1)) * 2 = (e + 1) * (e + 2) := by
  induction e with
  | zero => simp
  | succ e ih => rw [Finset.sum_range_succ, add_mul, ih]; ring

lemma card_triSet_mul_two (e : ℕ) : (triSet e).card * 2 = (e + 1) * (e + 2) := by
  rw [triSet, Finset.card_biUnion]
  · simp only [Finset.Nat.card_antidiagonal]
    exact sum_succ_mul_two e
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 fun z hz hz' => ?_
    rw [Finset.mem_antidiagonal] at hz hz'
    exact hxy (hz.symm.trans hz')

/-- Monomials of degree at most `e` in two variables, as pairs. -/
noncomputable def monoEquiv (e : ℕ) :
    {s : Fin 2 →₀ ℕ // s.sum (fun _ k => k) ≤ e} ≃ {x : ℕ × ℕ // x ∈ triSet e} :=
  Equiv.subtypeEquiv (Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv ℕ)) (fun s => by
    rw [mem_triSet, Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    rfl)

lemma finrank_restrictTotalDegree (K : Type*) [Field K] (e : ℕ) :
    Module.finrank K (restrictTotalDegree (Fin 2) K e) * 2 = (e + 1) * (e + 2) := by
  have h1 : Module.finrank K (restrictTotalDegree (Fin 2) K e) =
      Nat.card {s : Fin 2 →₀ ℕ // s.sum (fun _ k => k) ≤ e} :=
    Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)
  rw [h1, Nat.card_congr (monoEquiv e), Nat.card_eq_fintype_card, Fintype.card_coe]
  exact card_triSet_mul_two e

end Count

section Main

variable {K : Type*} [Field K]

/-- Polynomials of total degree at most `e`. -/
noncomputable abbrev Vd (K : Type*) [Field K] (e : ℕ) : Submodule K (MvPolynomial (Fin 2) K) :=
  restrictTotalDegree (Fin 2) K e

lemma mem_Vd {x : MvPolynomial (Fin 2) K} {e : ℕ} : x ∈ Vd K e ↔ x.totalDegree ≤ e :=
  mem_restrictTotalDegree _ _ _

/-- The map from degree `≤ e` polynomials to the quotient. -/
noncomputable def phi (f g : MvPolynomial (Fin 2) K) (e : ℕ) :
    Vd K e →ₗ[K] (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g}) :=
  (Ideal.Quotient.mkₐ K (Ideal.span {f, g})).toLinearMap.comp (Vd K e).subtype

lemma phi_apply (f g : MvPolynomial (Fin 2) K) (e : ℕ) (x : Vd K e) :
    phi f g e x = Ideal.Quotient.mk _ x.1 := rfl

lemma totalDegree_add_mul {f g a b : MvPolynomial (Fin 2) K} {m n p q : ℕ}
    (hf : f.totalDegree ≤ m) (hg : g.totalDegree ≤ n) (ha : a.totalDegree ≤ p)
    (hb : b.totalDegree ≤ q) (h : p + m = q + n) :
    (a * f + b * g).totalDegree ≤ p + m := by
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (add_le_add ha hf)
  · rw [h]; exact (totalDegree_mul _ _).trans (add_le_add hb hg)

/-- The multiplication map `(a, b) ↦ a f + b g`. -/
noncomputable def mu (f g : MvPolynomial (Fin 2) K) {m n : ℕ} (hf : f.totalDegree ≤ m)
    (hg : g.totalDegree ≤ n) (k : ℕ) : (Vd K (n + k) × Vd K (m + k)) →ₗ[K] Vd K (m + n + k) :=
  LinearMap.codRestrict (Vd K (m + n + k))
    ((LinearMap.mulRight K f ∘ₗ (Vd K (n + k)).subtype).coprod
      (LinearMap.mulRight K g ∘ₗ (Vd K (m + k)).subtype))
    (fun x => by
      rw [mem_Vd]
      have := totalDegree_add_mul hf hg (mem_Vd.1 x.1.2) (mem_Vd.1 x.2.2) (p := n + k)
        (q := m + k) (by omega)
      simpa [LinearMap.coprod_apply, add_assoc, add_comm, add_left_comm] using this.trans (le_of_eq (by ring)))

lemma mu_val {f g : MvPolynomial (Fin 2) K} {m n : ℕ} (hf : f.totalDegree ≤ m)
    (hg : g.totalDegree ≤ n) (k : ℕ) (x : Vd K (n + k) × Vd K (m + k)) :
    (mu f g hf hg k x : MvPolynomial (Fin 2) K) = x.1.1 * f + x.2.1 * g := rfl

/-- The syzygy map `c ↦ (c g, -c f)`. -/
noncomputable def psi (f g : MvPolynomial (Fin 2) K) {m n : ℕ} (hf : f.totalDegree ≤ m)
    (hg : g.totalDegree ≤ n) (k : ℕ) : Vd K k →ₗ[K] (Vd K (n + k) × Vd K (m + k)) :=
  LinearMap.prod
    (LinearMap.codRestrict (Vd K (n + k)) (LinearMap.mulRight K g ∘ₗ (Vd K k).subtype)
      (fun c => by
        rw [mem_Vd]
        show (c.1 * g).totalDegree ≤ n + k
        exact (totalDegree_mul _ _).trans (by have := mem_Vd.1 c.2; omega)))
    (LinearMap.codRestrict (Vd K (m + k)) (-(LinearMap.mulRight K f ∘ₗ (Vd K k).subtype))
      (fun c => by
        rw [mem_Vd]
        show (-(c.1 * f)).totalDegree ≤ m + k
        rw [totalDegree_neg]
        exact (totalDegree_mul _ _).trans (by have := mem_Vd.1 c.2; omega)))

lemma psi_fst {f g : MvPolynomial (Fin 2) K} {m n : ℕ} (hf : f.totalDegree ≤ m)
    (hg : g.totalDegree ≤ n) (k : ℕ) (c : Vd K k) :
    ((psi f g hf hg k c).1 : MvPolynomial (Fin 2) K) = c.1 * g := rfl

lemma psi_snd {f g : MvPolynomial (Fin 2) K} {m n : ℕ} (hf : f.totalDegree ≤ m)
    (hg : g.totalDegree ≤ n) (k : ℕ) (c : Vd K k) :
    ((psi f g hf hg k c).2 : MvPolynomial (Fin 2) K) = -(c.1 * f) := rfl

lemma psi_injective {f g : MvPolynomial (Fin 2) K} {m n : ℕ} (hf : f.totalDegree ≤ m)
    (hg : g.totalDegree ≤ n) (hg0 : g ≠ 0) (k : ℕ) :
    Function.Injective (psi f g hf hg k) := by
  intro c c' h
  have := congrArg (fun x => (x.1 : MvPolynomial (Fin 2) K)) h
  simp only [psi_fst] at this
  exact Subtype.ext (mul_right_cancel₀ hg0 this)

lemma le_totalDegree_of_hc_ne {g : MvPolynomial (Fin 2) K} {n : ℕ}
    (hgn : homogeneousComponent n g ≠ 0) : n ≤ g.totalDegree := by
  by_contra h
  exact hgn (homogeneousComponent_eq_zero n g (by omega))

lemma range_mu_eq_ker_phi {f g : MvPolynomial (Fin 2) K} {m n : ℕ} (hf : f.totalDegree ≤ m)
    (hg : g.totalDegree ≤ n) (hfm : homogeneousComponent m f ≠ 0)
    (hgn : homogeneousComponent n g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent m f) (homogeneousComponent n g)) (k : ℕ) :
    LinearMap.range (mu f g hf hg k) = LinearMap.ker (phi f g (m + n + k)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker, phi_apply, Ideal.Quotient.eq_zero_iff_mem, mu_val]
    exact Ideal.mem_span_pair.2 ⟨_, _, rfl⟩
  · intro hx
    rw [LinearMap.mem_ker, phi_apply, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨a, b, hab, ha, hb⟩ := exists_repr_of_mem_span_of_isRelPrime_top hf hg hfm hgn hcop hx
      (mem_Vd.1 x.2) (by omega) (by omega)
    refine ⟨(⟨a, mem_Vd.2 (by omega)⟩, ⟨b, mem_Vd.2 (by omega)⟩), Subtype.ext ?_⟩
    rw [mu_val]; exact hab.symm

lemma ker_mu_eq_range_psi {f g : MvPolynomial (Fin 2) K} {m n : ℕ} (hf : f.totalDegree ≤ m)
    (hg : g.totalDegree ≤ n) (hfm : homogeneousComponent m f ≠ 0)
    (hgn : homogeneousComponent n g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent m f) (homogeneousComponent n g)) (k : ℕ) :
    LinearMap.ker (mu f g hf hg k) = LinearMap.range (psi f g hf hg k) := by
  have hg0 : g ≠ 0 := by rintro rfl; simp at hgn
  ext x
  constructor
  · intro hx
    have h0 : x.1.1 * f + x.2.1 * g = 0 := by
      rw [← mu_val hf hg k x, LinearMap.mem_ker.1 hx]; rfl
    obtain ⟨c, hc1, hc2⟩ := syzygy_of_isRelPrime_top hf hg hfm hgn hcop h0
    have hcd : c.totalDegree ≤ k := by
      by_cases hc0 : c = 0
      · simp [hc0]
      · have h1 := mem_Vd.1 x.1.2
        rw [hc1, totalDegree_mul_of_isDomain hc0 hg0] at h1
        have := le_totalDegree_of_hc_ne hgn
        omega
    refine ⟨⟨c, mem_Vd.2 hcd⟩, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · rw [psi_fst]; exact hc1.symm
    · rw [psi_snd]; exact hc2.symm
  · rintro ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [mu_val, psi_fst, psi_snd]
    show c.1 * g * f + -(c.1 * f) * g = 0
    ring

lemma finrank_range_phi {f g : MvPolynomial (Fin 2) K} {m n : ℕ} (hf : f.totalDegree ≤ m)
    (hg : g.totalDegree ≤ n) (hfm : homogeneousComponent m f ≠ 0)
    (hgn : homogeneousComponent n g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent m f) (homogeneousComponent n g)) (k : ℕ) :
    Module.finrank K (LinearMap.range (phi f g (m + n + k))) = m * n := by
  have hg0 : g ≠ 0 := by rintro rfl; simp at hgn
  have E1 := LinearMap.finrank_range_add_finrank_ker (phi f g (m + n + k))
  have E2 := LinearMap.finrank_range_add_finrank_ker (mu f g hf hg k)
  have E3 : Module.finrank K (LinearMap.range (psi f g hf hg k)) = Module.finrank K (Vd K k) :=
    LinearMap.finrank_range_of_inj (psi_injective hf hg hg0 k)
  rw [← range_mu_eq_ker_phi hf hg hfm hgn hcop k] at E1
  rw [ker_mu_eq_range_psi hf hg hfm hgn hcop k, E3, Module.finrank_prod] at E2
  have hW := finrank_restrictTotalDegree K (m + n + k)
  have hA := finrank_restrictTotalDegree K (n + k)
  have hB := finrank_restrictTotalDegree K (m + k)
  have hC := finrank_restrictTotalDegree K k
  change Module.finrank K (Vd K (m + n + k)) * 2 = _ at hW
  change Module.finrank K (Vd K (n + k)) * 2 = _ at hA
  change Module.finrank K (Vd K (m + k)) * 2 = _ at hB
  change Module.finrank K (Vd K k) * 2 = _ at hC
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
  nlinarith [E1, E2, hW, hA, hB, hC]

lemma range_phi_mono (f g : MvPolynomial (Fin 2) K) {e e' : ℕ} (h : e ≤ e') :
    LinearMap.range (phi f g e) ≤ LinearMap.range (phi f g e') := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.1, mem_Vd.2 ((mem_Vd.1 x.2).trans h)⟩, rfl⟩

theorem finrank_quotient_of_isRelPrime_top {f g : MvPolynomial (Fin 2) K} {m n : ℕ}
    (hf : f.totalDegree ≤ m) (hg : g.totalDegree ≤ n)
    (hfm : homogeneousComponent m f ≠ 0) (hgn : homogeneousComponent n g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent m f) (homogeneousComponent n g)) :
    Module.Finite K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g}) ∧
      Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g}) = m * n := by
  have hfin : ∀ e, Module.Finite K (LinearMap.range (phi f g e)) := fun e => inferInstance
  have heq : ∀ k, LinearMap.range (phi f g (m + n + k)) = LinearMap.range (phi f g (m + n)) := by
    intro k
    symm
    refine Submodule.eq_of_le_of_finrank_eq (range_phi_mono f g (by omega)) ?_
    rw [finrank_range_phi hf hg hfm hgn hcop k, ← add_zero (m + n),
      finrank_range_phi hf hg hfm hgn hcop 0]
  have htop : LinearMap.range (phi f g (m + n)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← heq p.totalDegree]
    exact range_phi_mono f g (e := p.totalDegree) (by omega) ⟨⟨p, mem_Vd.2 le_rfl⟩, rfl⟩
  have hsurj : Function.Surjective (phi f g (m + n)) := LinearMap.range_eq_top.1 htop
  refine ⟨Module.Finite.of_surjective _ hsurj, ?_⟩
  have := finrank_range_phi hf hg hfm hgn hcop 0
  rw [add_zero, htop, finrank_top] at this
  exact this

end Main

end NumberFieldKB.MilneEC.Bezout
