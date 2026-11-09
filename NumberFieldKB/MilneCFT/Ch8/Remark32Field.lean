import NumberFieldKB.MilneCFT.Ch8.Quadratic

/-!
# Milne, *Class Field Theory*, Remark VIII.3.2: the field $\mathbb Q(\sqrt{13}, \sqrt{17})$

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, Remark 3.2,
p. 234.

For a number field $L$ generated over $\mathbb Q$ by $s, t$ with $s^2 = 13$, $t^2 = 17$:
* $13$, $17$, $221$ are not squares in $\mathbb Q$ (`R32.rat_sq_ne`);
* $t \notin \mathbb Q(s)$ (`R32.t_not_mem`), so $[L : \mathbb Q] = 4$ (`R32.finrank_eq_four`);
* $L/\mathbb Q$ is Galois (`R32.isGalois`), and for $\delta \in \{s, t, st\}$ some automorphism sends $\delta$ to
  $-\delta$ (`R32.exists_aut_neg`).
-/

open Polynomial IntermediateField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.R32

/-- $13$, $17$ and $221$ are not squares of rationals. -/
theorem rat_sq_ne (q : ℚ) : q ^ 2 ≠ 13 ∧ q ^ 2 ≠ 17 ∧ q ^ 2 ≠ 221 := by
  have key : ∀ n : ℕ, ¬ IsSquare (n : ℤ) → q ^ 2 ≠ n := by
    intro n hn h
    have hsq : IsSquare (n : ℚ) := ⟨q, by rw [← h]; ring⟩
    have := (Rat.isSquare_iff.mp hsq).1
    exact hn (by simpa using this)
  refine ⟨?_, ?_, ?_⟩
  · have := key 13 (by
      rw [Int.isSquare_natCast_iff]; rintro ⟨r, hr⟩
      have : r ≤ 15 := by nlinarith
      interval_cases r <;> omega)
    exact_mod_cast this
  · have := key 17 (by
      rw [Int.isSquare_natCast_iff]; rintro ⟨r, hr⟩
      have : r ≤ 15 := by nlinarith
      interval_cases r <;> omega)
    exact_mod_cast this
  · have := key 221 (by
      rw [Int.isSquare_natCast_iff]; rintro ⟨r, hr⟩
      have : r ≤ 15 := by nlinarith
      interval_cases r <;> omega)
    exact_mod_cast this

variable {L : Type} [Field L] [NumberField L] {s t : L}

/-- An element whose square is a rational non-square is not rational. -/
theorem not_mem_bot_of_sq {δ : L} {d : ℚ} (hδ : δ ^ 2 = algebraMap ℚ L d) (hd : ∀ q : ℚ, q ^ 2 ≠ d) :
    δ ∉ (⊥ : IntermediateField ℚ L) := by
  intro h
  rw [IntermediateField.mem_bot] at h
  obtain ⟨q, rfl⟩ := h
  apply hd q
  apply (algebraMap ℚ L).injective
  rw [map_pow, hδ]

theorem s_not_mem (hs : s ^ 2 = 13) : s ∉ (⊥ : IntermediateField ℚ L) :=
  not_mem_bot_of_sq (d := 13) (by rw [hs, map_ofNat]) fun q => (rat_sq_ne q).1

/-- $t \notin \mathbb Q(s)$. -/
theorem t_not_mem (hs : s ^ 2 = 13) (ht : t ^ 2 = 17) : t ∉ ℚ⟮s⟯ := by
  intro hmem
  obtain ⟨a, b, hab⟩ := exists_eq_add_mul_of_mem_adjoin s 13 (by rw [hs, map_ofNat]) hmem
  have h2 : algebraMap ℚ L (a ^ 2 + 13 * b ^ 2 - 17) + algebraMap ℚ L (2 * a * b) * s = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    have : t ^ 2 = (algebraMap ℚ L a + algebraMap ℚ L b * s) ^ 2 := by rw [← hab]
    linear_combination -this + ht - (algebraMap ℚ L b) ^ 2 * hs
  by_cases hab0 : 2 * a * b = 0
  · rw [hab0, map_zero, zero_mul, add_zero] at h2
    have h3 : a ^ 2 + 13 * b ^ 2 - 17 = 0 := (map_eq_zero_iff _ (algebraMap ℚ L).injective).mp h2
    rcases mul_eq_zero.mp hab0 with h | h
    · have ha : a = 0 := by simpa using h
      subst ha
      exact (rat_sq_ne (13 * b)).2.2 (by linear_combination 13 * h3)
    · subst h
      exact (rat_sq_ne a).2.1 (by linear_combination h3)
  · apply s_not_mem hs
    rw [IntermediateField.mem_bot]
    refine ⟨-(a ^ 2 + 13 * b ^ 2 - 17) / (2 * a * b), ?_⟩
    have hne : algebraMap ℚ L (2 * a * b) ≠ 0 := (_root_.map_ne_zero _).mpr hab0
    rw [map_div₀, map_neg, div_eq_iff hne]
    linear_combination -h2

theorem finrank_adjoin_sq {K : Type} [Field K] [Algebra K L] {δ : L} {d : K} (hδ : δ ^ 2 = algebraMap K L d)
    (hd : ∀ q : K, q ^ 2 ≠ d) : Module.finrank K K⟮δ⟯ = 2 := by
  have hint : IsIntegral K δ :=
    ⟨X ^ 2 - C d, monic_X_pow_sub_C d two_ne_zero, by simp [hδ]⟩
  rw [adjoin.finrank hint]
  have hirr : Irreducible (X ^ 2 - C d) := X_pow_sub_C_irreducible_of_prime Nat.prime_two hd
  rw [← minpoly.eq_of_irreducible_of_monic hirr (by simp [hδ]) (monic_X_pow_sub_C d two_ne_zero)]
  exact natDegree_X_pow_sub_C

/-- $[L : \mathbb Q] = 4$. -/
theorem finrank_eq_four (hs : s ^ 2 = 13) (ht : t ^ 2 = 17) (hgen : adjoin ℚ ({s, t} : Set L) = ⊤) :
    Module.finrank ℚ L = 4 := by
  set K := ℚ⟮s⟯
  have h1 : Module.finrank ℚ K = 2 :=
    finrank_adjoin_sq (d := 13) (by rw [hs, map_ofNat]) fun q => (rat_sq_ne q).1
  have htop : adjoin K ({t} : Set L) = ⊤ := by
    apply restrictScalars_injective ℚ
    rw [adjoin_adjoin_left, restrictScalars_top, ← hgen]
    rfl
  have h2 : Module.finrank K K⟮t⟯ = 2 := by
    refine finrank_adjoin_sq (d := 17) (by rw [ht, map_ofNat]) fun q hq => ?_
    apply t_not_mem hs ht
    have h0 : (t - (q : L)) * (t + (q : L)) = 0 := by
      have : ((q : L)) ^ 2 = 17 := by
        have := congrArg (algebraMap K L) hq
        rw [map_pow, map_ofNat] at this
        exact this
      linear_combination ht - this
    rcases mul_eq_zero.mp h0 with h | h
    · rw [sub_eq_zero.mp h]; exact q.2
    · rw [eq_neg_of_add_eq_zero_left h]; exact neg_mem q.2
  rw [htop, finrank_top'] at h2
  rw [← Module.finrank_mul_finrank ℚ K L, h1, h2]

/-- $L/\mathbb Q$ is Galois: $L$ is the splitting field of $(X^2 - 13)(X^2 - 17)$. -/
theorem isGalois (hs : s ^ 2 = 13) (ht : t ^ 2 = 17) (hgen : adjoin ℚ ({s, t} : Set L) = ⊤) :
    IsGalois ℚ L := by
  set f : ℚ[X] := (X ^ 2 - C 13) * (X ^ 2 - C 17)
  have hf0 : f ≠ 0 := mul_ne_zero (X_pow_sub_C_ne_zero two_pos _) (X_pow_sub_C_ne_zero two_pos _)
  have hmap : f.map (algebraMap ℚ L) = (X - C s) * (X - C (-s)) * ((X - C t) * (X - C (-t))) := by
    have e13 : (13 : L[X]) = C s ^ 2 := by rw [← C_pow, hs, map_ofNat]
    have e17 : (17 : L[X]) = C t ^ 2 := by rw [← C_pow, ht, map_ofNat]
    simp only [f, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_ofNat,
      Polynomial.map_ofNat, C_neg]
    rw [e13, e17]
    ring
  have hroot : ∀ x : L, x ^ 2 = 13 ∨ x ^ 2 = 17 → x ∈ f.rootSet L := by
    intro x hx
    rw [mem_rootSet]
    refine ⟨hf0, ?_⟩
    simp only [f, map_mul, map_sub, map_pow, aeval_X, aeval_C, map_ofNat]
    rcases hx with h | h <;> rw [h] <;> ring
  haveI : IsSplittingField ℚ L f := by
    constructor
    · rw [hmap]
      exact ((Splits.X_sub_C _).mul (Splits.X_sub_C _)).mul ((Splits.X_sub_C _).mul (Splits.X_sub_C _))
    · rw [eq_top_iff]
      have hS : Algebra.adjoin ℚ ({s, t} : Set L) = ⊤ := by
        rw [← adjoin_toSubalgebra_of_isAlgebraic (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hgen]
        rfl
      rw [← hS]
      apply Algebra.adjoin_mono
      rintro x (rfl | rfl)
      · exact hroot _ (Or.inl hs)
      · exact hroot _ (Or.inr ht)
  haveI := Normal.of_isSplittingField (F := ℚ) (E := L) f
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

/-- For $\delta \in L$ with $\delta^2 = d$ a rational non-square, some automorphism of $L/\mathbb Q$ sends $\delta$
to $-\delta$. -/
theorem exists_aut_neg [IsGalois ℚ L] {δ : L} {d : ℚ} (hδ : δ ^ 2 = algebraMap ℚ L d)
    (hd : ∀ q : ℚ, q ^ 2 ≠ d) : ∃ σ : Gal(L/ℚ), σ δ = -δ := by
  have hnot := not_mem_bot_of_sq hδ hd
  rw [IsGalois.mem_bot_iff_fixed] at hnot
  push_neg at hnot
  obtain ⟨σ, hσ⟩ := hnot
  refine ⟨σ, ?_⟩
  have h2 : (σ δ) ^ 2 = δ ^ 2 := by rw [← map_pow, hδ, AlgEquiv.commutes]
  have : (σ δ - δ) * (σ δ + δ) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hσ
  · exact eq_neg_of_add_eq_zero_left h

end NumberFieldKB.MilneCFT.Ch8.R32
