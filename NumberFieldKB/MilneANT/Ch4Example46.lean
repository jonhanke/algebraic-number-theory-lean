import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import NumberFieldKB.MilneANT.Ch2Examples
import Mathlib.RingTheory.Flat.Rank

/-!
# Milne, *Algebraic Number Theory*, Example 4.6: auxiliary results for $\mathbb Q(\sqrt{-5})$

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), p. 71; bib key `milne2020ant`.

For a quadratic field $K$ containing $s$ with $s^2 = -5$: $\mathcal O_K = \mathbb Z[s]$ (Example 2.41),
$\mathfrak p = (2, 1 + s)$ satisfies $\mathfrak p^2 = (2)$, is not principal, and is the only ideal of norm $2$;
the Minkowski bound is $< 3$, so the class number is $2$. The tagged statement is
`NumberFieldKB.MilneANT.example_4_6` in `Ch4.lean`.
-/

open NumberField Polynomial Module
open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT.Q5

variable {K : Type*} [Field K] [NumberField K]

lemma not_sq_neg5 (q : ℚ) : q ^ 2 ≠ -5 := by
  intro h; nlinarith [sq_nonneg q]

lemma s_irrat (s : K) (hs : s ^ 2 = -5) (q : ℚ) : s ≠ algebraMap ℚ K q := by
  intro h
  apply not_sq_neg5 q
  apply (algebraMap ℚ K).injective
  rw [map_pow, ← h, hs]
  simp

lemma coord (s : 𝓞 K) (hs : s ^ 2 = -5) (a b a' b' : ℤ) (h : (a : 𝓞 K) + b * s = a' + b' * s) :
    a = a' ∧ b = b' := by
  have hsK : (s : K) ^ 2 = -5 := by
    have := congrArg (algebraMap (𝓞 K) K) hs
    simpa [map_ofNat] using this
  have hK : (a : K) + b * s = a' + b' * s := by
    have := congrArg (fun x : 𝓞 K => (x : K)) h
    simpa using this
  have hb : b = b' := by
    by_contra hne
    have hne' : ((b : ℚ) - b') ≠ 0 := by
      intro h0; apply hne; exact_mod_cast sub_eq_zero.1 h0
    apply s_irrat (s : K) hsK (((a' : ℚ) - a) / ((b : ℚ) - b'))
    have h1 : ((b : K) - b') * s = (a' : K) - a := by linear_combination hK
    have h2 : (algebraMap ℚ K ((b : ℚ) - b')) ≠ 0 := (map_ne_zero (algebraMap ℚ K)).2 hne'
    rw [map_div₀, eq_div_iff h2]
    simp only [map_sub, map_intCast, eq_intCast]
    linear_combination h1
  subst hb
  refine ⟨?_, rfl⟩
  have : (a : K) = a' := by linear_combination hK
  exact_mod_cast this

lemma sK_sq (s : 𝓞 K) (hs : s ^ 2 = -5) : (s : K) ^ 2 = -5 := by
  have := congrArg (algebraMap (𝓞 K) K) hs
  simpa [map_ofNat] using this

lemma trace_s (hK : finrank ℚ K = 2) (s : 𝓞 K) (hs : s ^ 2 = -5) :
    Algebra.trace ℚ K (s : K) = 0 := by
  have hsK := sK_sq s hs
  have irr : Irreducible (X ^ 2 + 5 : ℚ[X]) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · have : (X ^ 2 + 5 : ℚ[X]).natDegree = 2 := by compute_degree!
      rw [this]; decide
    · intro x hx
      simp [IsRoot] at hx
      nlinarith [sq_nonneg x]
  have hroot : aeval (s : K) (X ^ 2 + 5 : ℚ[X]) = 0 := by
    simp [hsK, map_ofNat]
  have hmin : minpoly ℚ (s : K) = X ^ 2 + 5 :=
    (minpoly.eq_of_irreducible_of_monic irr hroot (by monicity!)).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin]
  have : (X ^ 2 + 5 : ℚ[X]).nextCoeff = 0 := by
    have hd : (X ^ 2 + 5 : ℚ[X]).natDegree = 2 := by compute_degree!
    rw [Polynomial.nextCoeff, hd]
    simp [coeff_X_pow]
  rw [this]; simp

lemma discr_rel (hK : finrank ℚ K = 2) (s : 𝓞 K) (hs : s ^ 2 = -5) :
    ∃ d : ℤ, d ≠ 0 ∧ d ^ 2 * discr K = -20 := by
  have hrk : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, hK]
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrk
  let v : Fin 2 → 𝓞 K := ![1, s]
  have h1 : Algebra.discr ℤ v = (b.toMatrix v).det ^ 2 * discr K := by
    have := Algebra.discr_of_matrix_vecMul b (b.toMatrix v)
    rw [Module.Basis.toMatrix_map_vecMul] at this
    rw [this, discr_eq_discr K b]
  have h2 : ((Algebra.discr ℤ v : ℤ) : ℚ) = Algebra.discr ℚ (fun i : Fin 2 => (v i : K)) := by
    rw [Algebra.discr_def, Algebra.discr_def, ← eq_intCast (Int.castRingHom ℚ), RingHom.map_det]
    congr 1
    ext i j
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.coe_trace_int]
  have h3 : Algebra.discr ℚ (fun i : Fin 2 => (v i : K)) = -20 := by
    have hsK := sK_sq s hs
    have ht := trace_s hK s hs
    have t1 : Algebra.trace ℚ K (algebraMap ℚ K 1) = 2 := by
      rw [Algebra.trace_algebraMap, hK]; simp
    have t5 : Algebra.trace ℚ K (algebraMap ℚ K (-5)) = -10 := by
      rw [Algebra.trace_algebraMap, hK]; simp; norm_num
    have e00 : ((v 0 : 𝓞 K) : K) * ((v 0 : 𝓞 K) : K) = algebraMap ℚ K 1 := by simp [v]
    have e01 : ((v 0 : 𝓞 K) : K) * ((v 1 : 𝓞 K) : K) = (s : K) := by simp [v]
    have e10 : ((v 1 : 𝓞 K) : K) * ((v 0 : 𝓞 K) : K) = (s : K) := by simp [v]
    have e11 : ((v 1 : 𝓞 K) : K) * ((v 1 : 𝓞 K) : K) = algebraMap ℚ K (-5) := by
      simp only [v]
      simp
      rw [← sq, hsK]
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rw [e00, e01, e10, e11, t1, t5, ht]
    norm_num
  refine ⟨(b.toMatrix v).det, ?_, ?_⟩
  · intro h0
    rw [h0] at h1
    have : ((Algebra.discr ℤ v : ℤ) : ℚ) = -20 := by rw [h2, h3]
    rw [h1] at this
    simp at this
  · have : ((Algebra.discr ℤ v : ℤ) : ℚ) = -20 := by rw [h2, h3]
    rw [h1] at this
    exact_mod_cast this

lemma every (hK : finrank ℚ K = 2) (s : 𝓞 K) (hs : s ^ 2 = -5) (x : 𝓞 K) :
    ∃ a b : ℤ, x = a + b * s := by
  have hsq : Squarefree (-5 : ℤ) := (Int.prime_iff_natAbs_prime.2 (by norm_num)).squarefree
  have hsK : (s : K) ^ 2 = ((-5 : ℤ) : K) := by
    have := congrArg (algebraMap (𝓞 K) K) hs
    simpa [map_ofNat] using this
  have := (NumberFieldKB.MilneANT.example_2_41 K hK (-5) hsq (by norm_num) (s : K) hsK).1
    (by norm_num) (x : K)
  obtain ⟨a, b, hab⟩ := this.1 x.2
  refine ⟨a, b, ?_⟩
  apply RingOfIntegers.coe_injective
  simpa using hab

def P (s : 𝓞 K) : Ideal (𝓞 K) := Ideal.span {2, 1 + s}

lemma two_mem_P (s : 𝓞 K) : (2 : 𝓞 K) ∈ P s := Ideal.subset_span (by simp)
lemma one_add_mem_P (s : 𝓞 K) : (1 + s : 𝓞 K) ∈ P s := Ideal.subset_span (by simp)

lemma even_of_mem_P (hK : finrank ℚ K = 2) (s : 𝓞 K) (hs : s ^ 2 = -5) (x : 𝓞 K) (hx : x ∈ P s)
    (a b : ℤ) (h : x = a + b * s) : Even (a - b) := by
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hx
  obtain ⟨a1, b1, rfl⟩ := every hK s hs u
  obtain ⟨a2, b2, rfl⟩ := every hK s hs v
  have : (a : 𝓞 K) + b * s = ((2 * a1 + a2 - 5 * b2 : ℤ) : 𝓞 K) + ((2 * b1 + a2 + b2 : ℤ) : 𝓞 K) * s := by
    rw [← h, ← huv]
    push_cast
    linear_combination (b2 : 𝓞 K) * hs
  obtain ⟨h1, h2⟩ := coord s hs _ _ _ _ this
  exact ⟨a1 - b1 - 3 * b2, by omega⟩

lemma mem_P_of_even (s : 𝓞 K) (a b : ℤ) (h : Even (a - b)) : ((a : 𝓞 K) + b * s) ∈ P s := by
  obtain ⟨k, hk⟩ := h
  have ha : (a : 𝓞 K) = 2 * k + b := by exact_mod_cast (by omega : a = 2 * k + b)
  have : (a : 𝓞 K) + b * s = (k : 𝓞 K) * 2 + (b : 𝓞 K) * (1 + s) := by rw [ha]; ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (two_mem_P s)) (Ideal.mul_mem_left _ _ (one_add_mem_P s))

lemma one_notMem_P (hK : finrank ℚ K = 2) (s : 𝓞 K) (hs : s ^ 2 = -5) : (1 : 𝓞 K) ∉ P s := by
  intro h
  have := even_of_mem_P hK s hs 1 h 1 0 (by simp)
  simp at this

lemma P_sq (s : 𝓞 K) (hs : s ^ 2 = -5) : P s ^ 2 = Ideal.span {2} := by
  apply le_antisymm
  · rw [pow_two, Ideal.mul_le]
    intro r hr t ht
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hr
    obtain ⟨u', v', huv'⟩ := Ideal.mem_span_pair.1 ht
    rw [Ideal.mem_span_singleton]
    refine ⟨2 * u * u' + u * v' * (1 + s) + v * u' * (1 + s) + v * v' * (s - 2), ?_⟩
    rw [← huv, ← huv']
    linear_combination (v * v') * hs
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    have e : (2 : 𝓞 K) = 2 * (1 + s) - (1 + s) * (1 + s) - 2 * 2 := by linear_combination hs
    rw [e, pow_two]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_mul (two_mem_P s) (one_add_mem_P s))
      (Ideal.mul_mem_mul (one_add_mem_P s) (one_add_mem_P s))) (Ideal.mul_mem_mul (two_mem_P s) (two_mem_P s))

lemma P_not_principal (hK : finrank ℚ K = 2) (s : 𝓞 K) (hs : s ^ 2 = -5) :
    ¬ (P s).IsPrincipal := by
  intro hpr
  obtain ⟨g, hg⟩ := hpr.principal
  have h2 : g ∣ 2 := by
    have := two_mem_P s
    rw [hg] at this
    exact Ideal.mem_span_singleton.1 this
  have h1 : g ∣ 1 + s := by
    have := one_add_mem_P s
    rw [hg] at this
    exact Ideal.mem_span_singleton.1 this
  obtain ⟨h, hh⟩ := h2
  obtain ⟨h', hh'⟩ := h1
  obtain ⟨c, d, rfl⟩ := every hK s hs g
  obtain ⟨e, f, rfl⟩ := every hK s hs h
  obtain ⟨e', f', rfl⟩ := every hK s hs h'
  have q1 : ((2 : ℤ) : 𝓞 K) + (0 : ℤ) * s =
      ((c * e - 5 * d * f : ℤ) : 𝓞 K) + ((c * f + d * e : ℤ) : 𝓞 K) * s := by
    push_cast
    linear_combination hh + (d * f : 𝓞 K) * hs
  have q2 : ((1 : ℤ) : 𝓞 K) + (1 : ℤ) * s =
      ((c * e' - 5 * d * f' : ℤ) : 𝓞 K) + ((c * f' + d * e' : ℤ) : 𝓞 K) * s := by
    push_cast
    linear_combination hh' + (d * f' : 𝓞 K) * hs
  obtain ⟨x1, y1⟩ := coord s hs _ _ _ _ q1
  obtain ⟨x2, y2⟩ := coord s hs _ _ _ _ q2
  have n1 : (c ^ 2 + 5 * d ^ 2) * (e ^ 2 + 5 * f ^ 2) = 4 := by
    linear_combination (c * e - 5 * d * f + 2) * (-x1) + 5 * (c * f + d * e) * (-y1)
  have n2 : (c ^ 2 + 5 * d ^ 2) * (e' ^ 2 + 5 * f' ^ 2) = 6 := by
    linear_combination (c * e' - 5 * d * f' + 1) * (-x2) + 5 * (c * f' + d * e' + 1) * (-y2)
  have hN0 : 0 < c ^ 2 + 5 * d ^ 2 := by
    rcases (by positivity : 0 ≤ c ^ 2 + 5 * d ^ 2).lt_or_eq with h | h
    · exact h
    · rw [← h] at n1; simp at n1
  have hd2 : (c ^ 2 + 5 * d ^ 2) ∣ 2 := by
    have a4 : (c ^ 2 + 5 * d ^ 2) ∣ 4 := ⟨_, n1.symm⟩
    have a6 : (c ^ 2 + 5 * d ^ 2) ∣ 6 := ⟨_, n2.symm⟩
    have := dvd_sub a6 a4
    simpa using this
  have hle := Int.le_of_dvd (by norm_num) hd2
  have hN1 : c ^ 2 + 5 * d ^ 2 = 1 := by
    by_contra hne
    have h2' : c ^ 2 + 5 * d ^ 2 = 2 := by omega
    have hd : d = 0 := by nlinarith [sq_nonneg c, sq_nonneg d, sq_nonneg (d - 1), sq_nonneg (d + 1)]
    subst hd
    have : c ^ 2 = 2 := by linarith
    have hc1 : c ≤ 1 := by nlinarith
    have hc2 : -1 ≤ c := by nlinarith
    interval_cases c <;> omega
  apply one_notMem_P hK s hs
  rw [hg]
  have : (1 : 𝓞 K) = ((c : 𝓞 K) + d * s) * ((c : 𝓞 K) - d * s) := by
    have hN : ((c ^ 2 + 5 * d ^ 2 : ℤ) : 𝓞 K) = 1 := by rw [hN1]; simp
    push_cast at hN
    linear_combination (-1 : 𝓞 K) * hN + ((d : 𝓞 K) ^ 2) * hs
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

lemma norm2_eq (hK : finrank ℚ K = 2) (s : 𝓞 K) (hs : s ^ 2 = -5) (I : Ideal (𝓞 K))
    (hI : Ideal.absNorm I = 2) : I = P s := by
  have hne : I ≠ ⊤ := by
    intro h; rw [h, Ideal.absNorm_top] at hI; norm_num at hI
  have h1 : (1 : 𝓞 K) ∉ I := fun h => hne ((Ideal.eq_top_iff_one I).2 h)
  have h2 : (2 : 𝓞 K) ∈ I := by
    have := Ideal.absNorm_mem I
    rw [hI] at this
    simpa using this
  have hc : Nat.card (𝓞 K ⧸ I) = 2 := by
    rw [← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.1 hc
  have hall : ∀ q : 𝓞 K ⧸ I, q = x ∨ q = y := fun q => by
    have : q ∈ ({x, y} : Set (𝓞 K ⧸ I)) := by rw [hset]; trivial
    simpa using this
  have hz : (0 : 𝓞 K ⧸ I) ≠ 1 := by
    intro h
    apply h1
    exact (Ideal.Quotient.eq_zero_iff_mem).1 h.symm
  have ht : Ideal.Quotient.mk I s = 0 ∨ Ideal.Quotient.mk I s = 1 := by
    have a := hall (Ideal.Quotient.mk I s)
    have b := hall 0
    have c := hall 1
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> aesop
  have hm5 : Ideal.Quotient.mk I (-5) = Ideal.Quotient.mk I 1 := by
    rw [Ideal.Quotient.eq]
    have : (-5 - 1 : 𝓞 K) = (-3) * 2 := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ h2
  have hsq : (Ideal.Quotient.mk I s) ^ 2 = 1 := by
    rw [← map_pow, hs, hm5, map_one]
  have ht1 : Ideal.Quotient.mk I s = 1 := by
    rcases ht with h | h
    · rw [h] at hsq; simp at hsq; exact absurd hsq hz
    · exact h
  have hs1 : s - 1 ∈ I := Ideal.Quotient.eq.1 ht1
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, rfl⟩ := every hK s hs x
    rcases Int.even_or_odd (a - b) with he | ⟨k, hk⟩
    · exact mem_P_of_even s a b he
    · exfalso
      have e1 : ((a + b : ℤ) : 𝓞 K) ∈ I := by
        have : ((a + b : ℤ) : 𝓞 K) = ((a : 𝓞 K) + b * s) - b * (s - 1) := by push_cast; ring
        rw [this]
        exact Ideal.sub_mem _ hx (Ideal.mul_mem_left _ _ hs1)
      have e2 : (1 : 𝓞 K) = ((a + b : ℤ) : 𝓞 K) - ((k + b : ℤ) : 𝓞 K) * 2 := by
        have : a + b = 2 * (k + b) + 1 := by omega
        rw [this]; push_cast; ring
      apply h1
      rw [e2]
      exact Ideal.sub_mem _ e1 (Ideal.mul_mem_left _ _ h2)
  · rw [P, Ideal.span_le]
    intro z hz
    rcases hz with rfl | hz
    · exact h2
    · rw [Set.mem_singleton_iff.1 hz]
      have : (1 + s : 𝓞 K) = (s - 1) + 2 := by ring
      rw [this]
      exact Ideal.add_mem _ hs1 h2

lemma class_number_two (hK : finrank ℚ K = 2) (s : 𝓞 K) (hs : s ^ 2 = -5) : classNumber K = 2 := by
  obtain ⟨d, hd0, hd⟩ := discr_rel hK s hs
  have hd1 : (1 : ℤ) ≤ d ^ 2 := by nlinarith [sq_pos_of_ne_zero hd0]
  have hD : discr K < 0 := by
    by_contra h
    push_neg at h
    nlinarith
  have hDle : -discr K ≤ 20 := by nlinarith
  have hs1 : InfinitePlace.nrComplexPlaces K = 1 := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h2 := NumberField.sign_discr K
    rw [Int.sign_eq_neg_one_of_neg hD] at h2
    rcases Nat.lt_or_ge (InfinitePlace.nrComplexPlaces K) 1 with h | h
    · have : InfinitePlace.nrComplexPlaces K = 0 := by omega
      rw [this] at h2
      simp at h2
    · omega
  have hbound : ∀ I : (Ideal (𝓞 K))⁰, ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤
      (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
        ((finrank ℚ K).factorial / (finrank ℚ K : ℝ) ^ finrank ℚ K * Real.sqrt |(discr K : ℝ)|)) →
      Ideal.absNorm (I : Ideal (𝓞 K)) < 3 := by
    intro I hle
    rw [hs1, hK] at hle
    have hr : Real.sqrt |(discr K : ℝ)| < 9 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      have : (discr K : ℝ) < 0 := by exact_mod_cast hD
      have h20 : (-(discr K : ℝ)) ≤ 20 := by exact_mod_cast hDle
      rw [abs_of_neg this]
      norm_num; linarith
    have hpi := Real.pi_gt_three
    have hpos := Real.pi_pos
    have : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) < 3 := by
      refine lt_of_le_of_lt hle ?_
      norm_num [Nat.factorial]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
      nlinarith
    exact_mod_cast this
  -- the two classes
  have hPmem : P s ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero (by
    intro h
    have := two_mem_P s
    rw [h] at this
    simp at this)
  let c : ClassGroup (𝓞 K) := ClassGroup.mk0 ⟨P s, hPmem⟩
  have hc1 : c ≠ 1 := by
    intro h
    exact P_not_principal hK s hs ((ClassGroup.mk0_eq_one_iff hPmem).1 h)
  unfold classNumber
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff]
  refine ⟨1, c, hc1.symm, ?_⟩
  ext C
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  obtain ⟨I, hI, hle⟩ := NumberField.exists_ideal_in_class_of_norm_le (K := K) C
  have hlt := hbound I hle
  have hpos := Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors I)
  have : Ideal.absNorm (I : Ideal (𝓞 K)) = 1 ∨ Ideal.absNorm (I : Ideal (𝓞 K)) = 2 := by omega
  rcases this with h | h
  · left
    rw [← hI, ClassGroup.mk0_eq_one_iff, Ideal.absNorm_eq_one_iff.1 h]
    exact top_isPrincipal
  · right
    rw [← hI]
    have := norm2_eq hK s hs _ h
    congr 1
    exact Subtype.ext this

end NumberFieldKB.MilneANT.Q5
