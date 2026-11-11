import Mathlib.RingTheory.Henselian
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import QuadFormsKB.Citation
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: Newton's lemma and Hensel's lemma

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Milne's standing hypothesis in this subsection (p. 119): $A$ is a complete discrete valuation ring and $\pi$
generates its maximal ideal. Here "complete" is the $\mathfrak m$-adic completeness `IsAdicComplete 𝔪 A`
(for a discrete valuation ring this is the same as completeness for the absolute value, since the balls
$\{|a| \le |\pi|^n\}$ are the ideals $\mathfrak m^n$). Reduction modulo $\mathfrak m$ is `IsLocalRing.residue A`, and
$\bar f$ is `f.map (IsLocalRing.residue A)`.

* **Proposition 7.31** (`prop_7_31`): a simple root modulo $\pi$ of any $f \in A[X]$ (not necessarily monic) lifts
  to a unique root.
* **Lemma 7.34** (`lemma_7_34_isCoprime`, `lemma_7_34`), **Lemma 7.35** (`lemma_7_35`): over a local ring, coprime
  reductions give strictly coprime polynomials, and lifts of coprime monic factorizations are unique.
* **Theorem 7.33** (`thm_7_33`, Hensel's lemma): coprime monic factorizations of $\bar f$ lift uniquely.
* **Remark 7.36** (`remark_7_36_prod`, `remark_7_36_teichmuller`, `remark_7_36_padicInt`): factorizations into
  pairwise coprime factors lift; Teichmüller representatives; $\mathbb Z_p$ contains the $(p-1)$st roots of $1$.
* **Remark 7.37** (`Remark7_37Resultant`, `Remark7_37Discriminant`): the stronger versions of Hensel's lemma
  (Cassels 1986), stated as named statements.
-/

open Polynomial IsLocalRing

namespace NumberFieldKB.MilneANT

open scoped Ring in
/-- Newton iteration for any polynomial (not nec. monic) over an adically complete ring. -/
private theorem newton_root {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let f' := derivative f
  let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
    intro n
    simp only [c]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => ?_
    rw [hc, sub_eq_add_neg, ← add_zero a₀]
    refine ih.add ?_
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine I.mul_mem_right _ ?_
    rw [← SModEq.zero] at h₁ ⊢
    exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
    | succ n ih => ?_
    rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
      add_neg_cancel_comm]
    rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
      Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
    swap
    · intro i
      rw [zero_mul]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
        taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
        mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
      exact Ideal.zero_mem _
    · refine Submodule.sum_mem _ ?_
      simp only [Finset.mem_Ico]
      rintro i ⟨h2i, _⟩
      have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih => ?_
    rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
    refine ih.add ?_
    symm
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
    rw [add_assoc]
    exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁


/-! ## Helper lemmas -/

section Aux


variable {R : Type*} [CommRing R]


/-- Membership in the coefficientwise ideal `I[X]` is vanishing modulo `I`. -/
private theorem memC_iff (I : Ideal R) (P : R[X]) :
    P ∈ Ideal.map (C : R →+* R[X]) I ↔ P.map (Ideal.Quotient.mk I) = 0 := by
  rw [Ideal.mem_map_C_iff, Polynomial.ext_iff]
  refine forall_congr' fun i => ?_
  rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]

/-- Division step of Milne's proof of Hensel's lemma: correction terms of degrees below `deg g`, `deg h`. -/
private theorem step_aux [Nontrivial R] (I : Ideal R) {g h d u v : R[X]} (hg : g.Monic) (hh : h.Monic)
    (huv : u * g + v * h = 1) (hd : d ∈ Ideal.map (C : R →+* R[X]) I)
    (hdeg : d.degree < ((g.natDegree + h.natDegree : ℕ) : WithBot ℕ)) :
    ∃ a b : R[X], a ∈ Ideal.map (C : R →+* R[X]) I ∧ b ∈ Ideal.map (C : R →+* R[X]) I ∧
      (b = 0 ∨ b.natDegree < g.natDegree) ∧ (a = 0 ∨ a.natDegree < h.natDegree) ∧
      a * g + b * h = d := by
  set b := (d * v) %ₘ g with hb
  set q := (d * v) /ₘ g with hq
  have hdv : b + g * q = d * v := Polynomial.modByMonic_add_div (d * v) g
  set a := d * u + q * h with ha
  have hab : a * g + b * h = d := by
    calc a * g + b * h = d * (u * g + v * h) - (d * v - b - g * q) * h := by
          rw [ha]; ring
      _ = d := by
          have : d * v - b - g * q = 0 := by rw [← hdv]; ring
          rw [this, huv]; ring
  have hd0 := (memC_iff I d).mp hd
  have hbI : b ∈ Ideal.map (C : R →+* R[X]) I := by
    rw [memC_iff, hb, Polynomial.map_modByMonic _ hg, Polynomial.map_mul, hd0]
    simp
  have hqI : q ∈ Ideal.map (C : R →+* R[X]) I := by
    rw [memC_iff, hq, Polynomial.map_divByMonic _ hg, Polynomial.map_mul, hd0]
    simp
  have haI : a ∈ Ideal.map (C : R →+* R[X]) I :=
    Ideal.add_mem _ (Ideal.mul_mem_right _ _ hd) (Ideal.mul_mem_right _ _ hqI)
  have hblt : b.degree < g.degree := Polynomial.degree_modByMonic_lt _ hg
  have hb' : b = 0 ∨ b.natDegree < g.natDegree := by
    by_cases h0 : b = 0
    · exact Or.inl h0
    · right
      rw [Polynomial.natDegree_lt_iff_degree_lt h0, Polynomial.degree_eq_natDegree hg.ne_zero] at *
      exact hblt
  refine ⟨a, b, haI, hbI, hb', ?_, hab⟩
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  right
  have hbh : (b * h).degree < ((g.natDegree + h.natDegree : ℕ) : WithBot ℕ) := by
    by_cases h0 : b = 0
    · rw [h0]; simp
    · have : b * h ≠ 0 := fun hh0 => h0 ((hh.mul_right_eq_zero_iff.mp (by rw [mul_comm]; exact hh0)))
      rw [← Polynomial.natDegree_lt_iff_degree_lt this]
      have := Polynomial.natDegree_mul_le (p := b) (q := h)
      rcases hb' with h1 | h1
      · exact absurd h1 h0
      · omega
  have hag : (a * g).degree < ((g.natDegree + h.natDegree : ℕ) : WithBot ℕ) := by
    have : a * g = d - b * h := by linear_combination hab
    rw [this]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hdeg hbh)
  have hag0 : a * g ≠ 0 := fun h0 => ha0 (hg.mul_left_eq_zero_iff.mp h0)
  rw [← Polynomial.natDegree_lt_iff_degree_lt hag0, mul_comm, hg.natDegree_mul' ha0] at hag
  omega

/-- Coefficientwise limit of a Cauchy sequence of polynomials of bounded degree. -/
private theorem lim_poly {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] (r : ℕ)
    (P : ℕ → R[X]) (hdeg : ∀ n, (P n).natDegree ≤ r)
    (hc : ∀ k n, k ≤ n → ∀ i, (P k).coeff i - (P n).coeff i ∈ I ^ k) :
    ∃ G : R[X], G.natDegree ≤ r ∧ ∀ n i, (P n).coeff i - G.coeff i ∈ I ^ n := by
  have e : ∀ n, (I ^ n • ⊤ : Ideal R) = I ^ n := fun n => by rw [smul_eq_mul, Ideal.mul_top]
  have hL : ∀ i, ∃ L : R, ∀ n, (P n).coeff i ≡ L [SMOD (I ^ n • ⊤ : Ideal R)] := by
    intro i
    refine IsPrecomplete.prec' (fun n => (P n).coeff i) ?_
    intro k n hkn
    rw [SModEq.sub_mem, e]
    exact hc k n hkn i
  choose L hL using hL
  refine ⟨∑ i ∈ Finset.range (r + 1), C (L i) * X ^ i, ?_, ?_⟩
  · refine (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := r) ?_)
    intro i hi
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    simpa [Nat.lt_succ_iff] using hi
  · intro n i
    have := (hL i n)
    rw [SModEq.sub_mem, e] at this
    by_cases hi : i ≤ r
    · rw [Polynomial.finsetSum_coeff]
      simp only [coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single i]
      · simpa using this
      · intro j _ hj; simp [Ne.symm hj]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)) h
    · have h1 : (P n).coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hdeg n) (not_le.mp hi))
      have h2 : (∑ i ∈ Finset.range (r + 1), C (L i) * X ^ i).coeff i = 0 := by
        rw [Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro j hj
        rw [coeff_C_mul_X_pow]
        have : i ≠ j := by
          have := Finset.mem_range.mp hj; omega
        simp [this]
      rw [h1, h2]; simp

end Aux

/-! ## Lemmas over a local ring -/

section Local

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- **Lemma 7.34**, first assertion. Let $A$ be a local ring with residue field $k$. If $f, g \in A[X]$ have relatively
prime images $\bar f, \bar g$ in $k[X]$ and $f$ is monic, then $(f, g) = A[X]$ ($f$ and $g$ are *strictly coprime*). -/
@[kb "milne2020ant" "v3.08, Lemma 7.34, p. 121"]
theorem lemma_7_34_isCoprime {f g : A[X]} (hf : f.Monic)
    (h : IsCoprime (f.map (residue A)) (g.map (residue A))) : IsCoprime f g := by
  obtain ⟨u', v', huv⟩ := h
  obtain ⟨u, rfl⟩ := Polynomial.map_surjective _ residue_surjective u'
  obtain ⟨v, rfl⟩ := Polynomial.map_surjective _ residue_surjective v'
  set e : A[X] := 1 - (u * f + v * g) with he
  have hem : ∀ q : A[X], AdjoinRoot.mk f (q * e) ∈
      (Ideal.map (algebraMap A (AdjoinRoot f)) (maximalIdeal A)) := by
    intro q
    have h1 : e ∈ Ideal.map (C : A →+* A[X]) (maximalIdeal A) := by
      rw [Ideal.mem_map_C_iff]
      intro i
      rw [← residue_eq_zero_iff, ← coeff_map]
      have : e.map (residue A) = 0 := by
        simp only [he, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
          Polynomial.map_one]
        rw [huv]; simp
      rw [this]; simp
    have h2 := Ideal.mul_mem_left _ q h1
    have h3 := Ideal.mem_map_of_mem (AdjoinRoot.mk f) h2
    rw [Ideal.map_map] at h3
    convert h3 using 2
    rw [AdjoinRoot.algebraMap_eq]; rfl
  have hfin : Module.Finite A (AdjoinRoot f) := hf.finite_adjoinRoot
  set J : Submodule A (AdjoinRoot f) :=
    (Ideal.span {AdjoinRoot.mk f g}).restrictScalars A with hJ
  have key : (⊤ : Submodule A (AdjoinRoot f)) ≤ J ⊔ maximalIdeal A • (⊤ : Submodule A (AdjoinRoot f)) := by
    intro x _
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    have hq : AdjoinRoot.mk f q = AdjoinRoot.mk f (q * v) * AdjoinRoot.mk f g
        + AdjoinRoot.mk f (q * e) := by
      have h1 : AdjoinRoot.mk f q = AdjoinRoot.mk f (q * u * f + q * v * g + q * e) := by
        congr 1; rw [he]; ring
      rw [h1]; simp [AdjoinRoot.mk_self]
    rw [hq]
    refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, rfl⟩
    · exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · rw [Ideal.smul_top_eq_map]; exact hem q
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp hfin)
    (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top).ge key
  have h1 : (1 : AdjoinRoot f) ∈ J := hle Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨w, rfl⟩ := AdjoinRoot.mk_surjective a
  have : AdjoinRoot.mk f (w * g) = AdjoinRoot.mk f 1 := by rw [map_mul, ha, map_one]
  obtain ⟨c, hc⟩ := AdjoinRoot.mk_eq_mk.mp this
  exact ⟨-c, w, by linear_combination hc⟩

/-- **Lemma 7.34**, degree bounds. In the situation of `lemma_7_34_isCoprime` there are $u, v \in A[X]$ with
$\deg u < \deg g$, $\deg v < \deg f$ and $uf + vg = 1$.

Hypothesis added: $f$ and $g$ are not both constant. (If $f = 1$ and $g$ is a constant, then $\deg u < \deg g \le 0$ and
$\deg v < \deg f = 0$ force $u = v = 0$; the book's claim fails in this degenerate case.) -/
@[kb "milne2020ant" "v3.08, Lemma 7.34, p. 121"]
theorem lemma_7_34 {f g : A[X]} (hf : f.Monic) (h : IsCoprime (f.map (residue A)) (g.map (residue A)))
    (hdeg : 0 < f.natDegree ∨ 0 < g.natDegree) :
    ∃ u v : A[X], u.degree < g.degree ∧ v.degree < f.degree ∧ u * f + v * g = 1 := by
  obtain ⟨u0, v0, h0⟩ := lemma_7_34_isCoprime hf h
  have hg0 : g ≠ 0 := by
    rintro rfl
    rcases hdeg with h1 | h1
    · have hu : IsUnit f := by
        have : IsCoprime f 0 := ⟨u0, v0, by simpa using h0⟩
        exact isCoprime_zero_right.mp this
      have := congrArg Polynomial.natDegree (hf.eq_one_of_isUnit hu)
      simp at this
      omega
    · simp at h1
  set r := v0 %ₘ f with hr
  set q := v0 /ₘ f with hq
  have hrlt : r.degree < f.degree := Polynomial.degree_modByMonic_lt v0 hf
  have hdiv : f * q + r = v0 := by have := Polynomial.modByMonic_add_div v0 f; rw [add_comm] at this; exact this
  refine ⟨u0 + q * g, r, ?_, hrlt, ?_⟩
  · have hug : (u0 + q * g) * f = 1 - r * g := by
      rw [← h0, ← hdiv]; ring
    set u := u0 + q * g with hu
    by_cases hu0 : u = 0
    · rw [hu0]; simpa using (Polynomial.degree_eq_bot.not.mpr hg0 |> fun h => bot_lt_iff_ne_bot.mpr h)
    rw [Polynomial.degree_eq_natDegree hu0, Polynomial.degree_eq_natDegree hg0, Nat.cast_lt]
    have hl : (u * f).natDegree = u.natDegree + f.natDegree := by
      rw [mul_comm, hf.natDegree_mul' hu0, add_comm]
    have hle : (1 - r * g).natDegree ≤ max 0 (r.natDegree + g.natDegree) := by
      refine (Polynomial.natDegree_sub_le _ _).trans ?_
      simp only [natDegree_one]
      exact max_le_max le_rfl (Polynomial.natDegree_mul_le)
    rw [← hug, hl] at hle
    by_cases hr0 : r = 0
    · rw [hr0] at hug
      simp only [zero_mul, sub_zero] at hug
      rw [hug] at hl
      simp at hl
      omega
    · have := Polynomial.natDegree_lt_natDegree hr0 hrlt
      omega
  · rw [← h0, ← hdiv]; ring

/-- **Lemma 7.35.** Let $A$ be a local ring with residue field $k$. If $f = gh = g'h'$ with $g, h, g', h'$ monic,
$\bar g = \bar g'$, $\bar h = \bar h'$, and $\bar g$, $\bar h$ relatively prime, then $g = g'$ and $h = h'$. -/
@[kb "milne2020ant" "v3.08, Lemma 7.35, p. 121"]
theorem lemma_7_35 {g h g' h' : A[X]} (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hgh : g * h = g' * h') (hgg : g.map (residue A) = g'.map (residue A))
    (hhh : h.map (residue A) = h'.map (residue A))
    (hcop : IsCoprime (g.map (residue A)) (h.map (residue A))) : g = g' ∧ h = h' := by
  have c1 : IsCoprime g h' := lemma_7_34_isCoprime hg (by rwa [← hhh])
  have c2 : IsCoprime g' h := lemma_7_34_isCoprime hg' (by rwa [← hgg])
  have d1 : g ∣ g' := by
    obtain ⟨a, b, hab⟩ := c1
    refine ⟨g' * a + b * h, ?_⟩
    have : g' = g' * (a * g + b * h') := by rw [hab, mul_one]
    calc g' = g' * (a * g + b * h') := this
      _ = g * (g' * a + b * h) := by
        have : g' * h' = g * h := hgh.symm
        linear_combination b * this
  have d2 : g' ∣ g := by
    obtain ⟨a, b, hab⟩ := c2
    refine ⟨g * a + b * h', ?_⟩
    have : g = g * (a * g' + b * h) := by rw [hab, mul_one]
    calc g = g * (a * g' + b * h) := this
      _ = g' * (g * a + b * h') := by
        linear_combination b * hgh
  have hgg' : g = g' :=
    Polynomial.eq_of_monic_of_associated hg hg' (by
      obtain ⟨c, hc⟩ := d1
      obtain ⟨c', hc'⟩ := d2
      have h1 : g * (1 - c * c') = 0 := by
        have : g = g * c * c' := by rw [← hc]; exact hc'
        linear_combination this
      have h2 : c * c' = 1 := by
        have := (hg.mul_right_eq_zero_iff).mp h1
        exact (sub_eq_zero.mp this).symm
      exact ⟨⟨c, c', h2, by rw [mul_comm]; exact h2⟩, hc.symm⟩)
  subst hgg'
  refine ⟨rfl, ?_⟩
  have : g * (h - h') = 0 := by rw [mul_sub, hgh, sub_self]
  exact sub_eq_zero.mp ((hg.mul_right_eq_zero_iff).mp this)

/-- One Newton-type correction step in Hensel's lemma (Milne's proof of Thm. 7.33). -/
private theorem hensel_step {f g h : A[X]} (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hfd : f.natDegree = g.natDegree + h.natDegree)
    (hcop : IsCoprime (g.map (residue A)) (h.map (residue A))) (n : ℕ)
    (hn : f - g * h ∈ Ideal.map (C : A →+* A[X]) (maximalIdeal A ^ (n + 1))) :
    ∃ a b : A[X], a ∈ Ideal.map (C : A →+* A[X]) (maximalIdeal A ^ (n + 1)) ∧
      b ∈ Ideal.map (C : A →+* A[X]) (maximalIdeal A ^ (n + 1)) ∧
      b.degree < g.degree ∧ a.degree < h.degree ∧
      f - (g + b) * (h + a) ∈ Ideal.map (C : A →+* A[X]) (maximalIdeal A ^ (n + 2)) := by
  obtain ⟨u, v, huv⟩ := lemma_7_34_isCoprime hg hcop
  have hdeg : (f - g * h).degree < ((g.natDegree + h.natDegree : ℕ) : WithBot ℕ) := by
    have hgh : (g * h).Monic := hg.mul hh
    have hgh' : (g * h).natDegree = g.natDegree + h.natDegree := hg.natDegree_mul' hh.ne_zero
    have h1 : f.degree = (g * h).degree := by
      rw [Polynomial.degree_eq_natDegree hf.ne_zero, Polynomial.degree_eq_natDegree hgh.ne_zero, hfd,
        hgh']
    have := Polynomial.degree_sub_lt_left h1 hf.ne_zero (by rw [hf.leadingCoeff, hgh.leadingCoeff])
    rwa [Polynomial.degree_eq_natDegree hf.ne_zero, hfd] at this
  obtain ⟨a, b, haI, hbI, hb, ha, hab⟩ := step_aux _ hg hh huv hn hdeg
  have hb' : b.degree < g.degree := by
    rcases hb with h0 | h0
    · rw [h0, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by simpa using hg.ne_zero)
    · exact Polynomial.degree_lt_degree h0
  have ha' : a.degree < h.degree := by
    rcases ha with h0 | h0
    · rw [h0, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by simpa using hh.ne_zero)
    · exact Polynomial.degree_lt_degree h0
  refine ⟨a, b, haI, hbI, hb', ha', ?_⟩
  have : f - (g + b) * (h + a) = -(a * b) + (-(a * g + b * h) + (f - g * h)) := by ring
  rw [this, hab, neg_add_cancel, add_zero]
  refine Ideal.neg_mem_iff _ |>.2 ?_
  have h2 := Ideal.mul_mem_mul haI hbI
  rw [← Ideal.map_mul] at h2
  exact Ideal.map_mono (by rw [← pow_add]; exact Ideal.pow_le_pow_right (by omega)) h2

end Local

/-! ## Complete discrete valuation rings -/

section Complete

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

/-- **Proposition 7.31.** Let $A$ be a complete discrete valuation ring with maximal ideal $(\pi)$, let
$f \in A[X]$, and let $a_0$ be a simple root of $f$ modulo $\pi$ ($f(a_0) \equiv 0$ and $f'(a_0) \not\equiv 0$).
Then there is a unique root $a$ of $f$ with $a \equiv a_0 \bmod \pi$.

Mathlib's `HenselianLocalRing` (with `IsAdicComplete.henselianRing`) gives existence for monic $f$ only;
this is the book's form, for every $f$ and with uniqueness. -/
@[kb "milne2020ant" "v3.08, Prop. 7.31, p. 120"]
theorem prop_7_31 (f : A[X]) (a₀ : A) (h₀ : f.eval a₀ ∈ maximalIdeal A)
    (h₁ : f.derivative.eval a₀ ∉ maximalIdeal A) :
    ∃! a : A, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal A := by
  have hu : IsUnit (f.derivative.eval a₀) := (notMem_maximalIdeal.mp h₁)
  obtain ⟨a, ha, hma⟩ := newton_root (maximalIdeal A) f a₀ h₀ (hu.map _)
  refine ⟨a, ⟨ha, hma⟩, ?_⟩
  rintro b ⟨hb, hmb⟩
  have hd : a - b ∈ maximalIdeal A := by
    have := Ideal.sub_mem _ hma hmb
    simpa using this
  have hd' : IsUnit (f.derivative.eval a) := by
    rw [← notMem_maximalIdeal]
    intro hm
    apply h₁
    have h3 : f.derivative.eval a₀ - f.derivative.eval a ∈ maximalIdeal A := by
      obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub a₀ a f.derivative
      rw [hc]
      exact Ideal.mul_mem_right _ _ (by rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 hma)
    simpa using Ideal.add_mem _ h3 hm
  exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ha hb
    (by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hd) hd').symm

/-- **Theorem 7.33 (Hensel's lemma).** Let $A$ be a complete discrete valuation ring with residue field $k$ and let
$f \in A[X]$ be monic. If $\bar f = g_0 h_0$ with $g_0, h_0 \in k[X]$ monic and relatively prime, then $f = gh$ with
$g, h \in A[X]$ monic, $\bar g = g_0$ and $\bar h = h_0$; moreover $g$ and $h$ are uniquely determined, and
$(g, h) = A[X]$. -/
@[kb "milne2020ant" "v3.08, Thm. 7.33, p. 121"]
theorem thm_7_33 (f : A[X]) (hf : f.Monic) (g₀ h₀ : (ResidueField A)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hfac : f.map (residue A) = g₀ * h₀) (hcop : IsCoprime g₀ h₀) :
    ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧ g.map (residue A) = g₀ ∧ h.map (residue A) = h₀ ∧
      IsCoprime g h ∧
      ∀ g' h' : A[X], g'.Monic → h'.Monic → f = g' * h' → g'.map (residue A) = g₀ →
        h'.map (residue A) = h₀ → g' = g ∧ h' = h := by
  classical
  set m := maximalIdeal A with hm
  set r := g₀.natDegree with hr
  set s := h₀.natDegree with hs
  have hfd : f.natDegree = r + s := by
    rw [← hf.natDegree_map (residue A), hfac, hg₀.natDegree_mul' hh₀.ne_zero]
  have hH : ∀ x : A, (∀ n, x ∈ m ^ n) → x = 0 := by
    intro x hx
    refine IsHausdorff.haus' (I := m) x fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hx n
  have hmC : ∀ (P : A[X]) (n : ℕ), P ∈ Ideal.map (C : A →+* A[X]) (m ^ n) ↔
      ∀ i, P.coeff i ∈ m ^ n := fun P n => Ideal.mem_map_C_iff
  -- the good pairs
  let Good : ℕ → A[X] × A[X] → Prop := fun n p =>
    p.1.Monic ∧ p.2.Monic ∧ p.1.natDegree = r ∧ p.2.natDegree = s ∧
      p.1.map (residue A) = g₀ ∧ p.2.map (residue A) = h₀ ∧
      f - p.1 * p.2 ∈ Ideal.map (C : A →+* A[X]) (m ^ n)
  have hres : ∀ (P : A[X]), P ∈ Ideal.map (C : A →+* A[X]) (m ^ 1) → P.map (residue A) = 0 := by
    intro P hP
    rw [pow_one] at hP
    exact (memC_iff m P).mp hP
  have step : ∀ n p, ∃ p' : A[X] × A[X], Good (n + 1) p →
      Good (n + 2) p' ∧ p'.1 - p.1 ∈ Ideal.map (C : A →+* A[X]) (m ^ (n + 1)) ∧
        p'.2 - p.2 ∈ Ideal.map (C : A →+* A[X]) (m ^ (n + 1)) := by
    intro n p
    by_cases hp : Good (n + 1) p
    · obtain ⟨hg, hh, hgd, hhd, hgm, hhm, hd⟩ := hp
      obtain ⟨a, b, haI, hbI, hb, ha, hd'⟩ := hensel_step hf hg hh (by rw [hfd, hgd, hhd])
        (by rw [hgm, hhm]; exact hcop) n hd
      have hm1 : ∀ P : A[X], P ∈ Ideal.map (C : A →+* A[X]) (m ^ (n + 1)) →
          P.map (residue A) = 0 := fun P hP =>
        hres P (Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) hP)
      refine ⟨(p.1 + b, p.2 + a), fun _ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hd'⟩, ?_, ?_⟩⟩
      · exact hg.add_of_left hb
      · exact hh.add_of_left ha
      · rw [Polynomial.natDegree_add_eq_left_of_degree_lt hb, hgd]
      · rw [Polynomial.natDegree_add_eq_left_of_degree_lt ha, hhd]
      · simp only [Polynomial.map_add, hgm, hm1 b hbI, add_zero]
      · simp only [Polynomial.map_add, hhm, hm1 a haI, add_zero]
      · simpa using hbI
      · simpa using haI
    · exact ⟨p, fun h => absurd h hp⟩
  choose next hnext using step
  -- initial pair
  obtain ⟨g1, hg1m, hg1d, hg1⟩ : ∃ q : A[X], q.map (residue A) = g₀ ∧ q.natDegree = r ∧ q.Monic := by
    obtain ⟨q, hq⟩ := Polynomial.map_surjective _ residue_surjective g₀
    obtain ⟨q', h1, h2, h3⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (f := residue A) (p := g₀) ⟨q, hq⟩ hg₀
    exact ⟨q', h1, h2, h3⟩
  obtain ⟨h1, hh1m, hh1d, hh1⟩ : ∃ q : A[X], q.map (residue A) = h₀ ∧ q.natDegree = s ∧ q.Monic := by
    obtain ⟨q, hq⟩ := Polynomial.map_surjective _ residue_surjective h₀
    obtain ⟨q', h1, h2, h3⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (f := residue A) (p := h₀) ⟨q, hq⟩ hh₀
    exact ⟨q', h1, h2, h3⟩
  have hgood0 : Good 1 (g1, h1) := by
    refine ⟨hg1, hh1, hg1d, hh1d, hg1m, hh1m, ?_⟩
    rw [pow_one, memC_iff]
    show Polynomial.map (residue A) (f - g1 * h1) = 0
    rw [Polynomial.map_sub, Polynomial.map_mul, hg1m, hh1m, hfac, sub_self]
  let seq : ℕ → A[X] × A[X] := fun n => Nat.rec (g1, h1) (fun k p => next k p) n
  have hseq : ∀ n, seq (n + 1) = next n (seq n) := fun n => rfl
  have hgoodn : ∀ n, Good (n + 1) (seq n) := by
    intro n
    induction n with
    | zero => exact hgood0
    | succ n ih => rw [hseq]; exact (hnext n _ ih).1
  have hdiff : ∀ n, (seq (n + 1)).1 - (seq n).1 ∈ Ideal.map (C : A →+* A[X]) (m ^ (n + 1)) ∧
      (seq (n + 1)).2 - (seq n).2 ∈ Ideal.map (C : A →+* A[X]) (m ^ (n + 1)) := by
    intro n
    rw [hseq]
    exact (hnext n _ (hgoodn n)).2
  -- Cauchy
  have cauchy : ∀ (F : A[X] × A[X] → A[X]),
      (∀ n, F (seq (n + 1)) - F (seq n) ∈ Ideal.map (C : A →+* A[X]) (m ^ (n + 1))) →
      ∀ k n, k ≤ n → ∀ i, (F (seq k)).coeff i - (F (seq n)).coeff i ∈ m ^ k := by
    intro F hF k n hkn i
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
    have : ∀ j, F (seq k) - F (seq (k + j)) ∈ Ideal.map (C : A →+* A[X]) (m ^ k) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h1 := Ideal.map_mono (Ideal.pow_le_pow_right (show k ≤ k + j + 1 by omega)) (hF (k + j))
        have h2 := Ideal.sub_mem _ ih h1
        convert h2 using 1
        rw [← add_assoc]; ring
    have := (hmC _ _).mp (this j) i
    simpa using this
  obtain ⟨G, hGd, hG⟩ := lim_poly m r (fun n => (seq n).1)
    (fun n => ((hgoodn n).2.2.1).le)
    (cauchy Prod.fst (fun n => (hdiff n).1))
  obtain ⟨H, hHd, hH'⟩ := lim_poly m s (fun n => (seq n).2)
    (fun n => ((hgoodn n).2.2.2.1).le)
    (cauchy Prod.snd (fun n => (hdiff n).2))
  have hGn : ∀ n, (seq n).1 - G ∈ Ideal.map (C : A →+* A[X]) (m ^ n) := fun n =>
    (hmC _ _).mpr (fun i => by simpa using hG n i)
  have hHn : ∀ n, (seq n).2 - H ∈ Ideal.map (C : A →+* A[X]) (m ^ n) := fun n =>
    (hmC _ _).mpr (fun i => by simpa using hH' n i)
  have hfGH : f = G * H := by
    have key : ∀ n, f - G * H ∈ Ideal.map (C : A →+* A[X]) (m ^ n) := by
      intro n
      have e : f - G * H = (f - (seq n).1 * (seq n).2) +
          ((seq n).1 * ((seq n).2 - H) + ((seq n).1 - G) * H) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n))
        (hgoodn n).2.2.2.2.2.2)
        (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hHn n)) (Ideal.mul_mem_right _ _ (hGn n)))
    ext i
    have := hH _ (fun n => by simpa using (hmC _ _).mp (key n) i)
    exact sub_eq_zero.mp (by simpa using this)
  have hmon : ∀ (P : ℕ → A[X]) (Q : A[X]) (t : ℕ), (∀ n, (P n).Monic) → (∀ n, (P n).natDegree = t) →
      Q.natDegree ≤ t → (∀ n i, (P n).coeff i - Q.coeff i ∈ m ^ n) → Q.Monic ∧ Q.natDegree = t := by
    intro P Q t hP hPd hQd hPQ
    have hc : Q.coeff t = 1 := by
      have := hH (1 - Q.coeff t) (fun n => by
        have h1 := hPQ n t
        have h2 : (P n).coeff t = 1 := by
          have := (hP n).coeff_natDegree
          rwa [hPd n] at this
        rwa [h2] at h1)
      exact (sub_eq_zero.mp this).symm
    have hd : Q.natDegree = t := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hQd (by
      rw [hc]; exact one_ne_zero)
    refine ⟨?_, hd⟩
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hd, hc]
  have hmapeq : ∀ (P : ℕ → A[X]) (Q : A[X]) (T : (ResidueField A)[X]),
      (P 1).map (residue A) = T → (∀ n i, (P n).coeff i - Q.coeff i ∈ m ^ n) →
      Q.map (residue A) = T := by
    intro P Q T hT hPQ
    ext i
    rw [coeff_map, ← hT, coeff_map]
    have h1 := hPQ 1 i
    rw [pow_one, ← residue_eq_zero_iff, map_sub] at h1
    exact (sub_eq_zero.mp h1).symm
  obtain ⟨hGm, hGdeg⟩ := hmon (fun n => (seq n).1) G r (fun n => (hgoodn n).1)
    (fun n => (hgoodn n).2.2.1) hGd hG
  obtain ⟨hHm, hHdeg⟩ := hmon (fun n => (seq n).2) H s (fun n => (hgoodn n).2.1)
    (fun n => (hgoodn n).2.2.2.1) hHd hH'
  have hGg : G.map (residue A) = g₀ :=
    hmapeq (fun n => (seq n).1) G g₀ (hgoodn 1).2.2.2.2.1 hG
  have hHh : H.map (residue A) = h₀ :=
    hmapeq (fun n => (seq n).2) H h₀ (hgoodn 1).2.2.2.2.2.1 hH'
  refine ⟨G, H, hGm, hHm, hfGH, hGg, hHh,
    lemma_7_34_isCoprime hGm (by rw [hGg, hHh]; exact hcop), ?_⟩
  intro g' h' hg' hh' hf' hg'm hh'm
  have := lemma_7_35 hGm hHm hg' hh' (hfGH.symm.trans hf') (by rw [hGg, hg'm])
    (by rw [hHh, hh'm]) (by rw [hGg, hHh]; exact hcop)
  exact ⟨this.1.symm, this.2.symm⟩

/-- **Remark 7.36**, first sentence: by induction, a factorization of a monic $f$ modulo $\mathfrak m$ into a product
of pairwise relatively prime monic polynomials lifts to a factorization in $A[X]$ into monic polynomials. -/
@[kb "milne2020ant" "v3.08, Remark 7.36, p. 122"]
theorem remark_7_36_prod {ι : Type*} (s : Finset ι) (f : A[X]) (hf : f.Monic) (g₀ : ι → (ResidueField A)[X])
    (hg₀ : ∀ i ∈ s, (g₀ i).Monic) (hfac : f.map (residue A) = ∏ i ∈ s, g₀ i)
    (hcop : (s : Set ι).Pairwise fun i j => IsCoprime (g₀ i) (g₀ j)) :
    ∃ g : ι → A[X], (∀ i ∈ s, (g i).Monic ∧ (g i).map (residue A) = g₀ i) ∧ f = ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    refine ⟨fun _ => 1, by simp, ?_⟩
    simp only [Finset.prod_empty]
    rw [Finset.prod_empty] at hfac
    have : f.natDegree = 0 := by
      rw [← hf.natDegree_map (residue A), hfac]; simp
    exact (Polynomial.Monic.natDegree_eq_zero hf).mp this
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at hfac
    have hmon : (∏ i ∈ s, g₀ i).Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun i hi => hg₀ i (Finset.mem_insert_of_mem hi))
    have hcp : IsCoprime (g₀ a) (∏ i ∈ s, g₀ i) := by
      refine IsCoprime.prod_right fun i hi => ?_
      refine hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) ?_
      rintro rfl; exact ha hi
    obtain ⟨g, h, hg, hh, hfgh, hgm, hhm, -, -⟩ :=
      thm_7_33 A f hf (g₀ a) _ (hg₀ a (Finset.mem_insert_self a s)) hmon hfac hcp
    obtain ⟨g', hg'1, hg'2⟩ := ih h hh
      (fun i hi => hg₀ i (Finset.mem_insert_of_mem hi)) hhm
      (hcop.mono (by simp))
    refine ⟨fun i => if i = a then g else g' i, ?_, ?_⟩
    · intro i hi
      by_cases hia : i = a
      · subst hia; simpa [hg] using hgm
      · have := hg'1 i ((Finset.mem_insert.mp hi).resolve_left hia)
        simpa [hia] using this
    · rw [Finset.prod_insert ha, hfgh, hg'2]
      simp only [ite_true]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have : i ≠ a := fun h => ha (h ▸ hi)
      simp [this]

/-- **Remark 7.36**, Teichmüller representatives. If the residue field $k$ of the complete discrete valuation ring
$A$ is finite with $q$ elements, then $A$ contains $q$ roots of $X^q - X$, and reduction is a bijection from the set
$S$ of these roots onto $k$ preserving multiplication. Stated as: there is a multiplicative map $\omega : k \to A$
(the Teichmüller representatives) that is a section of the reduction map, with image exactly the roots of
$X^q - X$. -/
@[kb "milne2020ant" "v3.08, Remark 7.36, p. 122"]
theorem remark_7_36_teichmuller [Finite (ResidueField A)] :
    ∃ ω : ResidueField A →* A, (∀ x, residue A (ω x) = x) ∧
      ∀ a : A, a ^ Nat.card (ResidueField A) = a ↔ a ∈ Set.range ω := by
  classical
  have := Fintype.ofFinite (ResidueField A)
  set q := Nat.card (ResidueField A) with hq
  have hqF : q = Fintype.card (ResidueField A) := Nat.card_eq_fintype_card
  have hpow : ∀ x : ResidueField A, x ^ q = x := by
    intro x; rw [hqF]; exact FiniteField.pow_card x
  have hqz : ((q : ℕ) : ResidueField A) = 0 := by
    rw [hqF]; exact FiniteField.cast_card_eq_zero _
  have hex : ∀ x : ResidueField A, ∃! a : A, a ^ q = a ∧ residue A a = x := by
    intro x
    obtain ⟨a₀, rfl⟩ := residue_surjective x
    have h0 : (X ^ q - X : A[X]).eval a₀ ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff]
      simp [hpow]
    have h1 : (X ^ q - X : A[X]).derivative.eval a₀ ∉ maximalIdeal A := by
      rw [← residue_eq_zero_iff]
      have : residue A ((X ^ q - X : A[X]).derivative.eval a₀) = -1 := by
        simp [Polynomial.derivative_X_pow, hqz]
      rw [this]; simp
    obtain ⟨a, ⟨ha, hma⟩, hu⟩ := prop_7_31 A _ a₀ h0 h1
    have hres : residue A a = residue A a₀ := by
      have := (residue_eq_zero_iff _).mpr hma
      rw [map_sub] at this
      exact sub_eq_zero.mp this
    refine ⟨a, ⟨?_, hres⟩, ?_⟩
    · have : a ^ q - a = 0 := by simpa using ha
      exact sub_eq_zero.mp this
    · rintro b ⟨hb, hrb⟩
      apply hu
      refine ⟨by simp [hb], ?_⟩
      rw [← residue_eq_zero_iff, map_sub, hrb]
      simp
  choose ω hω using fun x => (hex x).exists
  have hω2 : ∀ x a, a ^ q = a → residue A a = x → a = ω x := fun x a h1 h2 =>
    (hex x).unique ⟨h1, h2⟩ (hω x)
  refine ⟨MonoidHom.mk ⟨ω, (hω2 1 1 (one_pow _) (map_one _)).symm⟩ ?_, fun x => (hω x).2, ?_⟩
  · intro x y
    exact (hω2 (x * y) (ω x * ω y) (by rw [mul_pow, (hω x).1, (hω y).1])
      (by rw [map_mul, (hω x).2, (hω y).2])).symm
  · intro a
    constructor
    · intro h
      exact ⟨residue A a, (hω2 _ a h rfl).symm⟩
    · rintro ⟨x, rfl⟩
      exact (hω x).1

end Complete

/-- **Remark 7.36**, the example: $\mathbb Z_p$ contains the $(p-1)$st roots of $1$, i.e. a primitive
$(p-1)$st root of unity. -/
@[kb "milne2020ant" "v3.08, Remark 7.36, p. 122"]
theorem remark_7_36_padicInt (p : ℕ) [Fact p.Prime] : ∃ ζ : ℤ_[p], IsPrimitiveRoot ζ (p - 1) := by
  have : Finite (ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  obtain ⟨ω, hω1, -⟩ := remark_7_36_teichmuller ℤ_[p]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hprim : IsPrimitiveRoot (g : ZMod p) (p - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hord]
    exact IsPrimitiveRoot.orderOf g
  let ψ : ZMod p →* ℤ_[p] :=
    ω.comp (PadicInt.residueField (p := p)).symm.toRingHom.toMonoidHom
  have hinj : Function.Injective ψ := by
    intro a b hab
    have := congrArg (residue ℤ_[p]) hab
    simp only [ψ, MonoidHom.comp_apply] at this
    rw [hω1, hω1] at this
    exact (PadicInt.residueField (p := p)).symm.injective this
  exact ⟨ψ g, hprim.map_of_injective hinj⟩

/-! ## Remark 7.37: stronger forms of Hensel's lemma (named statements) -/

/-- **Remark 7.37, resultant form** (Milne, citing Cassels 1986, Chapter 4), as a named statement. Let $A$ be a
complete discrete valuation ring and $f \in A[X]$ with unit leading coefficient. Let $g_0, h_0 \in A[X]$ have degrees
$r$ and $s$, and suppose $\lVert f - g_0 h_0 \rVert < |\operatorname{Res}(g_0, h_0)|^2$, where
$\lVert \sum c_i X^i \rVert = \max |c_i|$. Then $f$ is the product of a polynomial of degree $r$ and one of degree $s$.

In a discrete valuation ring, $|c| < |R|^2$ (for $R \ne 0$) means $c \in R^2 \mathfrak m$, which is how the norm
condition is written. Hypothesis made explicit: $r + s = \deg f$ (the conclusion forces it). -/
@[kb "milne2020ant" "v3.08, Remark 7.37, p. 122"]
structure Remark7_37Resultant (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] : Prop where
  factors : ∀ (f g₀ h₀ : A[X]), IsUnit f.leadingCoeff →
    g₀.natDegree + h₀.natDegree = f.natDegree →
    (∀ i, (f - g₀ * h₀).coeff i ∈
      Ideal.span {resultant g₀ h₀ ^ 2} * maximalIdeal A) →
    ∃ g h : A[X], f = g * h ∧ g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree

/-- **Remark 7.37, discriminant form** (Milne, citing Cassels 1986, p. 107), as a named statement: the hypothesis of
`Remark7_37Resultant` may be replaced by $\lVert f - g_0 h_0 \rVert < |\operatorname{disc}(f)|$. -/
@[kb "milne2020ant" "v3.08, Remark 7.37, p. 123"]
structure Remark7_37Discriminant (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] : Prop where
  factors : ∀ (f g₀ h₀ : A[X]), IsUnit f.leadingCoeff →
    g₀.natDegree + h₀.natDegree = f.natDegree →
    (∀ i, (f - g₀ * h₀).coeff i ∈ Ideal.span {f.discr} * maximalIdeal A) →
    ∃ g h : A[X], f = g * h ∧ g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree

end NumberFieldKB.MilneANT
