import NumberFieldKB.MilneEC.Ch1BezoutDim

/-!
# The nine-point lemma: the line argument

Part of the proof of Milne, *Elliptic Curves*, Proposition I.3.2, from Bezout's theorem.

Let `f`, `g` be affine cubics whose leading forms are nonzero and relatively prime, `p` a common zero at
which `f` is nonsingular, and `h` of degree at most 3 vanishing at every other common zero. Suppose that
whenever `l * h` vanishes at all the common zeros it lies in the ideal $(f, g)$ (this is where the
intersections are transversal). Then $h(p) = 0$.

Proof: take a line `l` through `p` and through no other common zero, not tangent to `f` at `p`, and not in
a direction where the leading form of `f` vanishes. Then $lh = af + bg$ with `a`, `b` of degree at most 1
(`exists_repr_of_mem_span_of_isRelPrime_top`). On the line, $af + bg = 0$; there $f$ has a simple zero
at `p` and no other zero in common with `g`, which forces `a` and `b` to vanish on the line, so
$a = c\,l$, $b = d\,l$ and $h = cf + dg$ vanishes at `p`.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

section Line

/-- Restriction to the line `(x₀ + t, y₀ + s t)`. -/
noncomputable def lineMap (x₀ y₀ s : K) : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  aeval ![Polynomial.X + Polynomial.C x₀, Polynomial.C s * Polynomial.X + Polynomial.C y₀]

lemma lineMap_monomial (x₀ y₀ s : K) (m : Fin 2 →₀ ℕ) (c : K) :
    lineMap x₀ y₀ s (monomial m c) = Polynomial.C c *
      ((Polynomial.X + Polynomial.C x₀) ^ (m 0) *
        (Polynomial.C s * Polynomial.X + Polynomial.C y₀) ^ (m 1)) := by
  simp [lineMap, aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]

lemma lineMap_monomial_natDegree (x₀ y₀ s : K) (m : Fin 2 →₀ ℕ) (c : K) :
    (lineMap x₀ y₀ s (monomial m c)).natDegree ≤ m 0 + m 1 := by
  rw [lineMap_monomial]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 : (Polynomial.X + Polynomial.C x₀).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_X_add_C]
  have h2 : (Polynomial.C s * Polynomial.X + Polynomial.C y₀).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  have := Polynomial.natDegree_pow_le (p := Polynomial.X + Polynomial.C x₀) (n := m 0)
  have := Polynomial.natDegree_pow_le (p := Polynomial.C s * Polynomial.X + Polynomial.C y₀)
    (n := m 1)
  nlinarith

lemma lineMap_monomial_coeff (x₀ y₀ s : K) (m : Fin 2 →₀ ℕ) (c : K) :
    (lineMap x₀ y₀ s (monomial m c)).coeff (m 0 + m 1) = c * s ^ (m 1) := by
  rw [lineMap_monomial, Polynomial.coeff_C_mul]
  have h1 : (Polynomial.X + Polynomial.C x₀).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_X_add_C]
  have h2 : (Polynomial.C s * Polynomial.X + Polynomial.C y₀).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  have e1 := Polynomial.coeff_pow_of_natDegree_le (m := m 0) h1
  have e2 := Polynomial.coeff_pow_of_natDegree_le (m := m 1) h2
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (by simpa using Polynomial.natDegree_pow_le_of_le (m 0) h1)
    (by simpa using Polynomial.natDegree_pow_le_of_le (m 1) h2)]
  simp at e1 e2
  rw [e1, e2]
  simp

lemma lineMap_natDegree_le (x₀ y₀ s : K) (u : MvPolynomial (Fin 2) K) :
    (lineMap x₀ y₀ s u).natDegree ≤ u.totalDegree := by
  conv_lhs => rw [u.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine (lineMap_monomial_natDegree x₀ y₀ s m _).trans ?_
  have := le_totalDegree hm
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using this

lemma lineMap_coeff_top (x₀ y₀ s : K) {n : ℕ} (u : MvPolynomial (Fin 2) K)
    (hu : u.totalDegree ≤ n) :
    (lineMap x₀ y₀ s u).coeff n = aeval ![1, s] (homogeneousComponent n u) := by
  conv_lhs => rw [u.as_sum]
  rw [homogeneousComponent_apply, map_sum, map_sum, Polynomial.finset_sum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : m 0 + m 1 ≤ n := by
    have := le_totalDegree hm
    simp [Finsupp.sum_fintype, Fin.sum_univ_two] at this
    omega
  have hdeg : m.degree = m 0 + m 1 := by
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  split_ifs with h
  · rw [hdeg] at h
    rw [← h, lineMap_monomial_coeff]
    simp [aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]
  · rw [hdeg] at h
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (lineMap_monomial_natDegree x₀ y₀ s m _) (by omega))

lemma lineMap_eval (x₀ y₀ s t : K) (u : MvPolynomial (Fin 2) K) :
    (lineMap x₀ y₀ s u).eval t = evalAt u (x₀ + t, y₀ + s * t) := by
  rw [← Polynomial.coe_aeval_eq_eval, lineMap, MvPolynomial.comp_aeval_apply, evalAt]
  congr 1
  ext i
  fin_cases i <;> simp [add_comm]

lemma lineMap_coeff_zero (x₀ y₀ s : K) (u : MvPolynomial (Fin 2) K) :
    (lineMap x₀ y₀ s u).coeff 0 = evalAt u (x₀, y₀) := by
  rw [Polynomial.coeff_zero_eq_eval_zero, lineMap_eval]
  simp

lemma coeff_one_mul (P Q : Polynomial K) :
    (P * Q).coeff 1 = P.coeff 0 * Q.coeff 1 + P.coeff 1 * Q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp

lemma lineMap_coeff_one (x₀ y₀ s : K) (u : MvPolynomial (Fin 2) K) :
    (lineMap x₀ y₀ s u).coeff 1 =
      evalAt (pderiv 0 u) (x₀, y₀) + s * evalAt (pderiv 1 u) (x₀, y₀) := by
  induction u using MvPolynomial.induction_on with
  | C a => simp [evalAt]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq, evalAt]; ring
  | mul_X p i hp =>
    rw [map_mul, coeff_one_mul, lineMap_coeff_zero, hp]
    fin_cases i <;> simp [lineMap, Pi.single_apply, evalAt] <;> ring

lemma exists_poly_of_homog {v : MvPolynomial (Fin 2) K} {n : ℕ} (hv : v.IsHomogeneous n)
    (hv0 : v ≠ 0) :
    ∃ P : Polynomial K, P ≠ 0 ∧ ∀ s, P.eval s = aeval ![1, s] v := by
  refine ⟨∑ m ∈ v.support, Polynomial.C (v.coeff m) * Polynomial.X ^ (m 1), ?_, ?_⟩
  · obtain ⟨m₀, hm₀⟩ : v.support.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    intro h
    have := congrArg (fun P => P.coeff (m₀ 1)) h
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single m₀] at this
    · simp at this
      exact (mem_support_iff.1 hm₀) this
    · intro m' hm' hne
      rw [if_neg, mul_zero]
      intro h1
      apply hne
      have d1 : m'.degree = n := by
        rw [Finsupp.degree_eq_weight_one]; exact hv (mem_support_iff.1 hm')
      have d2 : m₀.degree = n := by
        rw [Finsupp.degree_eq_weight_one]; exact hv (mem_support_iff.1 hm₀)
      simp only [Finsupp.degree_eq_sum, Fin.sum_univ_two] at d1 d2
      ext i
      fin_cases i <;> simp <;> omega
    · intro h; exact absurd hm₀ h
  · intro s
    have : aeval ![1, s] v = ∑ m ∈ v.support, aeval ![1, s] (monomial m (v.coeff m)) := by
      conv_lhs => rw [v.as_sum]
      rw [map_sum]
    rw [this, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]

lemma exists_good_s [IsAlgClosed K] {f g : MvPolynomial (Fin 2) K}
    (hf3 : homogeneousComponent 3 f ≠ 0) (hfin : (commonZeros f g).Finite) (p : K × K)
    (hgrad : evalAt (pderiv 0 f) p ≠ 0 ∨ evalAt (pderiv 1 f) p ≠ 0) :
    ∃ s : K, aeval ![1, s] (homogeneousComponent 3 f) ≠ 0 ∧
      evalAt (pderiv 0 f) p + s * evalAt (pderiv 1 f) p ≠ 0 ∧
      ∀ q ∈ commonZeros f g, q ≠ p → s * (q.1 - p.1) ≠ q.2 - p.2 := by
  classical
  obtain ⟨P, hP0, hP⟩ := exists_poly_of_homog (homogeneousComponent_isHomogeneous 3 f) hf3
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset
    (P.roots.toFinset ∪ {-(evalAt (pderiv 0 f) p) / evalAt (pderiv 1 f) p} ∪
      hfin.toFinset.image (fun q => (q.2 - p.2) / (q.1 - p.1)))
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Multiset.mem_toFinset,
    Polynomial.mem_roots hP0, Polynomial.IsRoot.def, Set.Finite.mem_toFinset, not_or,
    not_exists, not_and] at hs
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  refine ⟨s, ?_, ?_, ?_⟩
  · rw [← hP]; exact h1
  · intro h
    by_cases hB : evalAt (pderiv 1 f) p = 0
    · rw [hB] at h
      rcases hgrad with h' | h'
      · exact h' (by simpa using h)
      · exact h' hB
    · apply h2
      field_simp
      linear_combination h
  · intro q hq hne h
    apply h3 q hq
    by_cases h0 : q.1 - p.1 = 0
    · exfalso; apply hne
      rw [h0, mul_zero] at h
      exact Prod.ext (by linear_combination h0) (by linear_combination -h)
    · field_simp
      linear_combination -h

/-- The line through `(x₀, y₀)` of slope `s`, as a polynomial. -/
noncomputable def lineForm (x₀ y₀ s : K) : MvPolynomial (Fin 2) K :=
  C s * X 0 - X 1 + C (y₀ - s * x₀)

lemma lineForm_totalDegree (x₀ y₀ s : K) : (lineForm x₀ y₀ s).totalDegree ≤ 1 := by
  unfold lineForm
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le ?_ ?_)) ?_)
  · exact (totalDegree_mul _ _).trans (by simp)
  · simp
  · exact (totalDegree_C _).le.trans (by norm_num)

lemma lineMap_lineForm (x₀ y₀ s : K) : lineMap x₀ y₀ s (lineForm x₀ y₀ s) = 0 := by
  simp [lineForm, lineMap]
  ring

lemma evalAt_lineForm (x₀ y₀ s : K) (q : K × K) :
    evalAt (lineForm x₀ y₀ s) q = s * (q.1 - x₀) - (q.2 - y₀) := by
  simp [lineForm, evalAt]
  ring

lemma lineForm_ne_zero (x₀ y₀ s : K) : lineForm x₀ y₀ s ≠ 0 := by
  intro h
  have := evalAt_lineForm x₀ y₀ s (x₀, y₀ + 1)
  rw [h] at this
  simp [evalAt] at this

lemma linear_decomp {a : MvPolynomial (Fin 2) K} (ha : a.totalDegree ≤ 1) :
    ∃ α β γ : K, a = C α + C β * X 0 + C γ * X 1 := by
  refine ⟨a.coeff 0, a.coeff (Finsupp.single 0 1), a.coeff (Finsupp.single 1 1), ?_⟩
  ext m
  simp only [MvPolynomial.coeff_add, coeff_C_mul, coeff_C, coeff_X]
  have n01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    simp [Finsupp.single_left_inj]
  have n0 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0 := by simp
  have n1 : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0 := by simp
  by_cases hm : m = 0 ∨ m = Finsupp.single 0 1 ∨ m = Finsupp.single 1 1
  · rcases hm with rfl | rfl | rfl
    · simp [n0, n1]
    · simp [n0, n01, n0.symm, n01.symm]
    · simp [n0, n1, n01, n1.symm, n01.symm]
  · have h2 : 2 ≤ m 0 + m 1 := by
      by_contra hlt
      apply hm
      have : m 0 = 0 ∧ m 1 = 0 ∨ m 0 = 1 ∧ m 1 = 0 ∨ m 0 = 0 ∧ m 1 = 1 := by omega
      rcases this with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
      · left; ext i; fin_cases i <;> simp [h0, h1]
      · right; left; ext i; fin_cases i <;> simp [h0, h1]
      · right; right; ext i; fin_cases i <;> simp [h0, h1]
    have hz : a.coeff m = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      rw [Finset.sum_subset (Finset.subset_univ m.support) (fun i _ hi => by simpa using hi),
        Fin.sum_univ_two]
      omega
    rw [hz]
    simp only [not_or] at hm
    simp [Ne.symm hm.1, Ne.symm hm.2.1, Ne.symm hm.2.2]

lemma eq_C_mul_lineForm {x₀ y₀ s : K} {a : MvPolynomial (Fin 2) K} (ha : a.totalDegree ≤ 1)
    (h0 : lineMap x₀ y₀ s a = 0) : ∃ c : K, a = C c * lineForm x₀ y₀ s := by
  obtain ⟨α, β, γ, rfl⟩ := linear_decomp ha
  have e0 : α + β * x₀ + γ * y₀ = 0 := by
    have := congrArg (fun P => P.coeff 0) h0
    simpa [lineMap] using this
  have e1 : β + γ * s = 0 := by
    have := congrArg (fun P => P.coeff 1) h0
    simpa [lineMap] using this
  refine ⟨-γ, ?_⟩
  have hβ : β = -(γ * s) := by linear_combination e1
  have hα : α = γ * s * x₀ - γ * y₀ := by linear_combination e0 - x₀ * e1
  subst hα hβ
  simp only [lineForm, map_sub, map_mul, map_neg]
  ring

end Line

/-- The core of the line argument: if `l * h ∈ (f, g)` for the line `l` through the common zero `p`
with slope `s` (not tangent to `f` at `p`, not in a direction where the leading form of `f` vanishes,
and through no other common zero), then `h` is a linear combination of `f` and `g` with constant
coefficients. -/
theorem exists_eq_of_lineForm_mul_mem [IsAlgClosed K] {f g h : MvPolynomial (Fin 2) K}
    (hf : f.totalDegree ≤ 3) (hg : g.totalDegree ≤ 3) (hh : h.totalDegree ≤ 3)
    (hf3 : homogeneousComponent 3 f ≠ 0) (hg3 : homogeneousComponent 3 g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent 3 f) (homogeneousComponent 3 g))
    {p : K × K} (hp : p ∈ commonZeros f g) {s : K}
    (hs1 : aeval ![1, s] (homogeneousComponent 3 f) ≠ 0)
    (hs2 : evalAt (pderiv 0 f) p + s * evalAt (pderiv 1 f) p ≠ 0)
    (hs3 : ∀ q ∈ commonZeros f g, q ≠ p → s * (q.1 - p.1) ≠ q.2 - p.2)
    (hmem : lineForm p.1 p.2 s * h ∈ Ideal.span {f, g}) :
    ∃ c d : K, h = C c * f + C d * g := by
  have hdeg : (lineForm p.1 p.2 s * h).totalDegree ≤ 4 := by
    have := totalDegree_mul (lineForm p.1 p.2 s) h
    have := lineForm_totalDegree p.1 p.2 s
    omega
  obtain ⟨a, b, hab, ha, hb⟩ := exists_repr_of_mem_span_of_isRelPrime_top (m := 3) (n := 3)
    (d := 4) hf hg hf3 hg3 hcop hmem hdeg (by norm_num) (by norm_num)
  have h1 : lineMap p.1 p.2 s a * lineMap p.1 p.2 s f + lineMap p.1 p.2 s b * lineMap p.1 p.2 s g
      = 0 := by
    have := congrArg (lineMap p.1 p.2 s) hab
    rw [map_mul, lineMap_lineForm, zero_mul, map_add, map_mul, map_mul] at this
    exact this.symm
  have hf0 : (lineMap p.1 p.2 s f).coeff 0 = 0 := by
    rw [lineMap_coeff_zero]; simpa using hp.1
  have hf1 : (lineMap p.1 p.2 s f).coeff 1 ≠ 0 := by
    rw [lineMap_coeff_one]; simpa using hs2
  have hf3' : (lineMap p.1 p.2 s f).coeff 3 ≠ 0 := by
    rw [lineMap_coeff_top _ _ _ _ hf]; exact hs1
  obtain ⟨φ, hφ⟩ : Polynomial.X ∣ lineMap p.1 p.2 s f := Polynomial.X_dvd_iff.2 hf0
  have hφ0 : φ.coeff 0 ≠ 0 := by
    have : (Polynomial.X * φ).coeff (0 + 1) = φ.coeff 0 := Polynomial.coeff_X_mul _ _
    rw [← this, ← hφ]; exact hf1
  have hφ2 : φ.coeff 2 ≠ 0 := by
    have : (Polynomial.X * φ).coeff (2 + 1) = φ.coeff 2 := Polynomial.coeff_X_mul _ _
    rw [← this, ← hφ]; exact hf3'
  have hcopφ : IsCoprime φ (lineMap p.1 p.2 s g) := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K]
    intro t
    by_contra hcon
    push_neg at hcon
    simp only [Polynomial.coe_aeval_eq_eval] at hcon
    have hft : (lineMap p.1 p.2 s f).eval t = 0 := by rw [hφ]; simp [hcon.1]
    have hq : (p.1 + t, p.2 + s * t) ∈ commonZeros f g :=
      ⟨by rw [← lineMap_eval]; exact hft, by rw [← lineMap_eval]; exact hcon.2⟩
    by_cases hqp : (p.1 + t, p.2 + s * t) = p
    · have ht : t = 0 := by simpa using congrArg Prod.fst hqp
      subst ht
      apply hφ0
      rw [Polynomial.coeff_zero_eq_eval_zero]; exact hcon.1
    · exact hs3 _ hq hqp (by simp)
  have hdvd : φ ∣ lineMap p.1 p.2 s b := by
    have h1' := h1
    rw [hφ] at h1'
    have : φ ∣ lineMap p.1 p.2 s b * lineMap p.1 p.2 s g :=
      ⟨-(lineMap p.1 p.2 s a * Polynomial.X), by linear_combination h1'⟩
    exact hcopφ.dvd_of_dvd_mul_right this
  have hb0 : lineMap p.1 p.2 s b = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd ?_
    have h2 := Polynomial.le_natDegree_of_ne_zero hφ2
    have h3 := lineMap_natDegree_le p.1 p.2 s b
    omega
  have ha0 : lineMap p.1 p.2 s a = 0 := by
    rw [hb0, zero_mul, add_zero] at h1
    have hne : lineMap p.1 p.2 s f ≠ 0 := fun h0 => hf3' (by rw [h0]; simp)
    exact (mul_eq_zero.1 h1).resolve_right hne
  obtain ⟨c, hc⟩ := eq_C_mul_lineForm (by omega) ha0
  obtain ⟨d, hd⟩ := eq_C_mul_lineForm (by omega) hb0
  have key : lineForm p.1 p.2 s * h = lineForm p.1 p.2 s * (C c * f + C d * g) := by
    rw [hab, hc, hd]; ring
  exact ⟨c, d, mul_left_cancel₀ (lineForm_ne_zero _ _ _) key⟩

theorem eval_eq_zero_of_line [IsAlgClosed K] {f g h : MvPolynomial (Fin 2) K}
    (hf : f.totalDegree ≤ 3) (hg : g.totalDegree ≤ 3) (hh : h.totalDegree ≤ 3)
    (hf3 : homogeneousComponent 3 f ≠ 0) (hg3 : homogeneousComponent 3 g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent 3 f) (homogeneousComponent 3 g))
    (hfin : (commonZeros f g).Finite) {p : K × K} (hp : p ∈ commonZeros f g)
    (hgrad : evalAt (pderiv 0 f) p ≠ 0 ∨ evalAt (pderiv 1 f) p ≠ 0)
    (hvan : ∀ q ∈ commonZeros f g, q ≠ p → evalAt h q = 0)
    (hmem : ∀ l : MvPolynomial (Fin 2) K, (∀ q ∈ commonZeros f g, evalAt (l * h) q = 0) →
      l * h ∈ Ideal.span {f, g}) :
    evalAt h p = 0 := by
  classical
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_good_s hf3 hfin p hgrad
  have hmul : ∀ (u v : MvPolynomial (Fin 2) K) (q : K × K),
      evalAt (u * v) q = evalAt u q * evalAt v q := fun u v q => by simp [evalAt]
  have hlh : ∀ q ∈ commonZeros f g, evalAt (lineForm p.1 p.2 s * h) q = 0 := by
    intro q hq
    rw [hmul]
    by_cases hqp : q = p
    · subst hqp
      rw [evalAt_lineForm]; simp
    · rw [hvan q hq hqp, mul_zero]
  obtain ⟨c, d, hh'⟩ := exists_eq_of_lineForm_mul_mem hf hg hh hf3 hg3 hcop hp hs1 hs2 hs3
    (hmem _ hlh)
  have e : evalAt (C c * f + C d * g) p = c * evalAt f p + d * evalAt g p := by
    simp [evalAt]
  rw [hh', e, hp.1, hp.2]
  simp

end NumberFieldKB.MilneEC.Bezout
