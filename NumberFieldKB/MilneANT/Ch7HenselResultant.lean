import NumberFieldKB.MilneANT.Ch7Hensel

/-!
# Milne, Remark 7.37: proofs of the resultant and discriminant forms of Hensel's lemma

Proof outline (resultant form).  Put `r = deg g₀`, `s = deg h₀`, `R = Res(g₀, h₀)`.
If `R = 0` the hypothesis says `f = g₀ h₀`.  Otherwise `lc g₀ · lc h₀ ≡ lc f` is a unit modulo `𝔪`, so
`lc h₀` is a unit, and Bezout gives `g₀ p + h₀ q = R`.  A Newton iteration produces `g_k, h_k` with
`g_k = g₀ + R u_k`, `h_k = h₀ + R v_k`, `f - g_k h_k = R² t_k`, `t_k` with coefficients in `𝔪^k`,
`deg g_k ≤ r`, `deg h_k ≤ s`: dividing `t p` by `h₀` (unit leading coefficient) as `t p = a h₀ + b`,
the corrections are `Δh = R b`, `Δg = R (t q + g₀ a)`.  The sequences are `𝔪`-adically Cauchy, their
limits `g, h` satisfy `f = g h` (Hausdorff), and `deg g + deg h = r + s` forces equality of degrees.

Proof outline (discriminant form).  If `disc f = 0` then `f = g₀ h₀`.  Otherwise `disc f` and
`disc (g₀ h₀)` differ by `disc f · 𝔪` (the discriminant is a determinant of a matrix with entries
linear in the coefficients, of size depending only on the degree), so they agree up to a unit; and
`Res(g₀, h₀)² ∣ disc (g₀ h₀)` (from `resultant_deriv` and multiplicativity of the resultant).  So the
discriminant hypothesis implies the resultant one.
-/

open Polynomial IsLocalRing

namespace NumberFieldKB.MilneANT

section Aux

variable {A : Type*} [CommRing A]

/-- Polynomials all of whose coefficients lie in `J`. -/
private noncomputable abbrev cI (J : Ideal A) : Ideal A[X] := Ideal.map C J

private lemma mem_cI {J : Ideal A} {p : A[X]} : p ∈ cI J ↔ ∀ i, p.coeff i ∈ J :=
  Ideal.mem_map_C_iff

private lemma mem_cI_iff_map {J : Ideal A} {p : A[X]} :
    p ∈ cI J ↔ p.map (Ideal.Quotient.mk J) = 0 := by
  rw [mem_cI, Polynomial.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

private lemma cI_mul_le (I J : Ideal A) : cI I * cI J ≤ cI (I * J) := by
  rw [cI, cI, cI, Ideal.map_mul]

private lemma cI_mono {I J : Ideal A} (h : I ≤ J) : cI I ≤ cI J := Ideal.map_mono h

private lemma modDiv_mem {J : Ideal A} {q p : A[X]} (hq : q.Monic) (hp : p ∈ cI J) :
    p %ₘ q ∈ cI J ∧ p /ₘ q ∈ cI J := by
  rw [mem_cI_iff_map] at hp ⊢
  rw [mem_cI_iff_map]
  rw [Polynomial.map_modByMonic _ hq, Polynomial.map_divByMonic _ hq, hp]
  simp

private lemma exists_limit [IsDomain A] (I : Ideal A) [IsPrecomplete I A] (g : ℕ → A[X]) (d : ℕ)
    (hd : ∀ n, (g n).natDegree ≤ d) (hc : ∀ m n, m ≤ n → g n - g m ∈ cI (I ^ m)) :
    ∃ G : A[X], G.natDegree ≤ d ∧ ∀ n, G - g n ∈ cI (I ^ n) := by
  classical
  have key : ∀ i, ∃ L : A, ∀ n, L - (g n).coeff i ∈ I ^ n := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => (g n).coeff i) (by
      intro m n hmn
      rw [SModEq.sub_mem]
      have := mem_cI.mp (hc m n hmn) i
      have h2 : (g m).coeff i - (g n).coeff i ∈ I ^ m := by
        have := (I ^ m).neg_mem this
        simpa using this
      simpa [Ideal.smul_eq_mul] using h2)
    refine ⟨L, fun n => ?_⟩
    have := (SModEq.sub_mem).mp (hL n).symm
    simpa [Ideal.smul_eq_mul] using this
  choose L hL using key
  refine ⟨∑ i ∈ Finset.range (d + 1), monomial i (L i), ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le (n := d) _ _ (fun i hi => ?_)
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  · intro n
    rw [mem_cI]
    intro i
    rw [coeff_sub, finsetSum_coeff]
    by_cases hi : i ≤ d
    · have : ∑ j ∈ Finset.range (d + 1), (monomial j (L j)).coeff i = L i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [coeff_monomial, hj]
        · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)) h
      rw [this]; exact hL i n
    · have h1 : ∑ j ∈ Finset.range (d + 1), (monomial j (L j)).coeff i = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have : j ≠ i := by
          have := Finset.mem_range.mp hj
          omega
        simp [coeff_monomial, this]
      have h2 : (g n).coeff i = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hd n) (by omega))
      rw [h1, h2]; simp

end Aux

section Step

variable {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]

/-- The Newton-iteration invariant at stage `k`. -/
private def Inv (f g₀ h₀ : A[X]) (R : A) (r s k : ℕ) (g h : A[X]) : Prop :=
  ∃ u v t : A[X], g = g₀ + C R * u ∧ h = h₀ + C R * v ∧ u ∈ cI (maximalIdeal A) ∧
    v ∈ cI (maximalIdeal A) ∧ f - g * h = C R ^ 2 * t ∧ t ∈ cI (maximalIdeal A ^ k) ∧
    g.natDegree ≤ r ∧ h.natDegree ≤ s

omit [IsDomain A] in
private lemma cI_pow_mul (j k : ℕ) {p q : A[X]} (hp : p ∈ cI (maximalIdeal A ^ j))
    (hq : q ∈ cI (maximalIdeal A ^ k)) : p * q ∈ cI (maximalIdeal A ^ (j + k)) := by
  have := cI_mul_le (maximalIdeal A ^ j) (maximalIdeal A ^ k)
  rw [← pow_add] at this
  exact this (Ideal.mul_mem_mul hp hq)

omit [IsDomain A] in
private lemma cI_pow_mono {j k : ℕ} (h : j ≤ k) :
    cI (maximalIdeal A ^ k) ≤ cI (maximalIdeal A ^ j) :=
  cI_mono (Ideal.pow_le_pow_right h)

private lemma newton_step (f g₀ h₀ : A[X]) (R : A) (hR : R ≠ 0) (r s : ℕ)
    (hg₀ : g₀.natDegree = r) (hh₀ : h₀.natDegree = s) (hfd : f.natDegree ≤ r + s)
    (hlc : IsUnit h₀.leadingCoeff) (p q : A[X]) (hpq : g₀ * p + h₀ * q = C R)
    (k : ℕ) (hk : 1 ≤ k) (g h : A[X]) (hI : Inv f g₀ h₀ R r s k g h) :
    ∃ g' h', Inv f g₀ h₀ R r s (k + 1) g' h' ∧ g' - g ∈ cI (maximalIdeal A ^ k) ∧
      h' - h ∈ cI (maximalIdeal A ^ k) := by
  obtain ⟨u, v, t, rfl, rfl, hu, hv, hft, ht, hgd, hhd⟩ := hI
  obtain ⟨c', hc'⟩ := hlc.exists_left_inv
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    simp at hc'
  have hmon : (C c' * h₀).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hc'
  have hdec := modByMonic_add_div (t * p) (C c' * h₀)
  set b := (t * p) %ₘ (C c' * h₀) with hb
  set a' := (t * p) /ₘ (C c' * h₀) with ha'
  have htp : t * p ∈ cI (maximalIdeal A ^ k) := Ideal.mul_mem_right _ _ ht
  obtain ⟨hbm, ham⟩ := modDiv_mem hmon htp
  set a := C c' * a' with ha
  have hdec2 : b + h₀ * a = t * p := by rw [ha, ← hdec]; ring
  have hamem : a ∈ cI (maximalIdeal A ^ k) := Ideal.mul_mem_left _ _ ham
  have hbdeg : b.natDegree ≤ s := by
    have := natDegree_modByMonic_le (t * p) hmon
    rwa [natDegree_C_mul hc'0, hh₀] at this
  set w := t * q + g₀ * a with hw
  have hwm : w ∈ cI (maximalIdeal A ^ k) :=
    Ideal.add_mem _ (Ideal.mul_mem_right _ _ ht) (Ideal.mul_mem_left _ _ hamem)
  have e : g₀ * (C R * b) + h₀ * (C R * w) = C R ^ 2 * t := by
    rw [hw]
    linear_combination (C R * g₀) * hdec2 + (C R * t) * hpq
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have htdeg : t.natDegree ≤ r + s := by
    have h1 : (f - (g₀ + C R * u) * (h₀ + C R * v)).natDegree ≤ r + s := by
      refine (natDegree_sub_le _ _).trans (max_le hfd ?_)
      exact natDegree_mul_le.trans (add_le_add hgd hhd)
    rw [hft, ← C_pow, natDegree_C_mul hR2] at h1
    exact h1
  have hΔg : (C R * w).natDegree ≤ r := by
    have h1 : (h₀ * (C R * w)).natDegree ≤ r + s := by
      have : h₀ * (C R * w) = C (R ^ 2) * t - g₀ * (C R * b) := by
        rw [C_pow]; linear_combination e
      rw [this]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_C_mul_le _ _).trans htdeg
      · refine natDegree_mul_le.trans ?_
        rw [hg₀]
        exact add_le_add le_rfl ((natDegree_C_mul_le _ _).trans hbdeg)
    by_cases h0 : C R * w = 0
    · rw [h0]; simp
    · have hh : h₀ ≠ 0 := by
        rintro rfl; simp at hlc
      rw [natDegree_mul hh h0, hh₀] at h1
      omega
  refine ⟨g₀ + C R * (u + w) , h₀ + C R * (v + b), ?_, ?_, ?_⟩
  · refine ⟨u + w, v + b, -(u * b + v * w + w * b), rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := cI_pow_mono (j := 1) hk hwm
      rw [pow_one] at this
      exact Ideal.add_mem _ hu this
    · have := cI_pow_mono (j := 1) hk hbm
      rw [pow_one] at this
      exact Ideal.add_mem _ hv this
    · linear_combination hft - e
    · have h1 : u * b ∈ cI (maximalIdeal A ^ (1 + k)) :=
        cI_pow_mul 1 k (by simpa using hu) hbm
      have h2 : v * w ∈ cI (maximalIdeal A ^ (1 + k)) :=
        cI_pow_mul 1 k (by simpa using hv) hwm
      have h3 : w * b ∈ cI (maximalIdeal A ^ (k + k)) := cI_pow_mul k k hwm hbm
      have h4 : cI (maximalIdeal A ^ (k + k)) ≤ cI (maximalIdeal A ^ (k + 1)) :=
        cI_pow_mono (by omega)
      rw [add_comm 1 k] at h1 h2
      exact Ideal.neg_mem_iff _ |>.mpr
        (Ideal.add_mem _ (Ideal.add_mem _ h1 h2) (h4 h3))
    · have : g₀ + C R * (u + w) = (g₀ + C R * u) + C R * w := by ring
      rw [this]
      exact (natDegree_add_le _ _).trans (max_le hgd hΔg)
    · have : h₀ + C R * (v + b) = (h₀ + C R * v) + C R * b := by ring
      rw [this]
      exact (natDegree_add_le _ _).trans (max_le hhd ((natDegree_C_mul_le _ _).trans hbdeg))
  · have : g₀ + C R * (u + w) - (g₀ + C R * u) = C R * w := by ring
    rw [this]; exact Ideal.mul_mem_left _ _ hwm
  · have : h₀ + C R * (v + b) - (h₀ + C R * v) = C R * b := by ring
    rw [this]; exact Ideal.mul_mem_left _ _ hbm

end Step


section Main

private lemma lc_mul_unit {A : Type*} [CommRing A] [IsLocalRing A] (f g₀ h₀ : A[X])
    (hfu : IsUnit f.leadingCoeff) (hdeg : g₀.natDegree + h₀.natDegree = f.natDegree)
    (hmem : ∀ i, (f - g₀ * h₀).coeff i ∈ maximalIdeal A) :
    IsUnit (g₀.leadingCoeff * h₀.leadingCoeff) := by
  by_contra hn
  have h1 : g₀.leadingCoeff * h₀.leadingCoeff ∈ maximalIdeal A := by
    by_contra h
    exact hn (notMem_maximalIdeal.mp h)
  have h2 := hmem (g₀.natDegree + h₀.natDegree)
  rw [coeff_sub, coeff_mul_degree_add_degree, hdeg, ← leadingCoeff] at h2
  have h3 : f.leadingCoeff ∈ maximalIdeal A := by
    have := Ideal.add_mem _ h2 h1
    simpa using this
  exact (notMem_maximalIdeal.mpr hfu) h3

private lemma cauchy_of_step {A : Type*} [CommRing A] [IsLocalRing A] (F : ℕ → A[X])
    (h : ∀ n, F (n + 1) - F n ∈ cI (maximalIdeal A ^ (n + 1))) :
    ∀ m n, m ≤ n → F n - F m ∈ cI (maximalIdeal A ^ m) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have : F (n + 1) - F m = (F (n + 1) - F n) + (F n - F m) := by ring
    rw [this]
    exact Ideal.add_mem _ (cI_pow_mono (by omega) (h n)) ih

private lemma haus_zero {A : Type*} [CommRing A] (I : Ideal A) [IsHausdorff I A] (x : A)
    (h : ∀ n, x ∈ I ^ n) : x = 0 := by
  refine IsHausdorff.haus (I := I) inferInstance x (fun n => ?_)
  rw [SModEq.sub_mem]
  simpa [Ideal.smul_eq_mul] using h n

/-- **Remark 7.37, resultant form** (Milne, citing Cassels 1986), proved by Newton iteration
with Bezout correction terms; see the module docstring. -/
@[kb "milne2020ant" "v3.08, Remark 7.37, p. 122"]
theorem remark7_37Resultant (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] : Remark7_37Resultant A := by
  refine ⟨fun f g₀ h₀ hfu hdeg hyp => ?_⟩
  by_cases hR : resultant g₀ h₀ = 0
  · refine ⟨g₀, h₀, ?_, rfl, rfl⟩
    have : ∀ i, (f - g₀ * h₀).coeff i = 0 := fun i => by simpa [hR] using hyp i
    exact sub_eq_zero.mp (Polynomial.ext (by simpa using this))
  by_cases hrs : g₀.natDegree = 0 ∧ h₀.natDegree = 0
  · refine ⟨f, 1, by simp, ?_, by simpa using hrs.2.symm⟩
    omega
  have hH : g₀.natDegree ≠ 0 ∨ h₀.natDegree ≠ 0 := by tauto
  set R := resultant g₀ h₀ with hRdef
  set r := g₀.natDegree with hr
  set s := h₀.natDegree with hs
  obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant g₀ h₀ (m := r) (n := s)
    le_rfl le_rfl hH
  have hmem1 : ∀ i, (f - g₀ * h₀).coeff i ∈ maximalIdeal A := fun i =>
    (Ideal.mul_le_left : maximalIdeal A * Ideal.span {R ^ 2} ≤ maximalIdeal A)
      (by rw [mul_comm]; exact hyp i)
  have hlcu := lc_mul_unit f g₀ h₀ hfu hdeg hmem1
  have hlc : IsUnit h₀.leadingCoeff := (IsUnit.mul_iff.mp hlcu).2
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hfu
  -- initial stage
  have hI0 : f - g₀ * h₀ ∈ Ideal.span {C R ^ 2} * cI (maximalIdeal A) := by
    have h1 := mem_cI.mpr hyp
    rw [cI, Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_pow] at h1
    exact h1
  obtain ⟨t, ht, het⟩ := Ideal.mem_span_singleton_mul.mp hI0
  have hinit : Inv f g₀ h₀ R r s 1 g₀ h₀ :=
    ⟨0, 0, t, by simp, by simp, zero_mem _, zero_mem _, by simpa using het.symm,
      by rwa [pow_one], le_rfl, le_rfl⟩
  have hstep : ∀ (n : ℕ) (x : A[X] × A[X]), Inv f g₀ h₀ R r s (n + 1) x.1 x.2 →
      ∃ y : A[X] × A[X], Inv f g₀ h₀ R r s (n + 1 + 1) y.1 y.2 ∧
        y.1 - x.1 ∈ cI (maximalIdeal A ^ (n + 1)) ∧ y.2 - x.2 ∈ cI (maximalIdeal A ^ (n + 1)) := by
    intro n x hx
    obtain ⟨g', h', h1, h2, h3⟩ := newton_step f g₀ h₀ R hR r s rfl rfl
      (by omega) hlc p q hpq (n + 1) (by omega) x.1 x.2 hx
    exact ⟨(g', h'), h1, h2, h3⟩
  choose! nxt hnxt using hstep
  obtain ⟨seq, hseq0, hseqS⟩ : ∃ seq : ℕ → A[X] × A[X], seq 0 = (g₀, h₀) ∧
      ∀ n, seq (n + 1) = nxt n (seq n) :=
    ⟨fun n => Nat.rec (g₀, h₀) (fun n x => nxt n x) n, rfl, fun _ => rfl⟩
  have hseqP : ∀ n, Inv f g₀ h₀ R r s (n + 1) (seq n).1 (seq n).2 := by
    intro n
    induction n with
    | zero => rw [hseq0]; exact hinit
    | succ n ih => rw [hseqS]; exact (hnxt n _ ih).1
  have hdiff : ∀ n, (seq (n + 1)).1 - (seq n).1 ∈ cI (maximalIdeal A ^ (n + 1)) ∧
      (seq (n + 1)).2 - (seq n).2 ∈ cI (maximalIdeal A ^ (n + 1)) :=
    fun n => by rw [hseqS]; exact (hnxt n _ (hseqP n)).2
  obtain ⟨G, hGd, hG⟩ := exists_limit (maximalIdeal A) (fun n => (seq n).1) r
    (fun n => by obtain ⟨_, _, _, _, _, _, _, _, _, hgd, -⟩ := hseqP n; exact hgd)
    (cauchy_of_step _ (fun n => (hdiff n).1))
  obtain ⟨H, hHd, hH'⟩ := exists_limit (maximalIdeal A) (fun n => (seq n).2) s
    (fun n => by obtain ⟨_, _, _, _, _, _, _, _, _, -, hhd⟩ := hseqP n; exact hhd)
    (cauchy_of_step _ (fun n => (hdiff n).2))
  have hfGH : f = G * H := by
    have : ∀ n, f - G * H ∈ cI (maximalIdeal A ^ n) := by
      intro n
      obtain ⟨u, v, t, -, -, -, -, hft, ht, -, -⟩ := hseqP n
      have h1 : f - (seq n).1 * (seq n).2 ∈ cI (maximalIdeal A ^ n) := by
        rw [hft]
        exact Ideal.mul_mem_left _ _ (cI_pow_mono (by omega) ht)
      have h2 := Ideal.mul_mem_right H _ (hG n)
      have h3 := Ideal.mul_mem_left _ (seq n).1 (hH' n)
      have : f - G * H = (f - (seq n).1 * (seq n).2) - ((G - (seq n).1) * H) -
          ((seq n).1 * (H - (seq n).2)) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.sub_mem _ h1 h2) h3
    refine sub_eq_zero.mp (Polynomial.ext fun i => ?_)
    simpa using haus_zero (maximalIdeal A) _ (fun n => mem_cI.mp (this n) i)
  have hG0 : G ≠ 0 := by rintro rfl; simp at hfGH; exact hf0 hfGH
  have hH0 : H ≠ 0 := by rintro rfl; simp at hfGH; exact hf0 hfGH
  have hd := natDegree_mul hG0 hH0
  rw [← hfGH] at hd
  exact ⟨G, H, hfGH, by omega, by omega⟩

end Main

end NumberFieldKB.MilneANT
