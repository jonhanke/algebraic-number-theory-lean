import NumberFieldKB.MilneCFT.Ch5Complements
import NumberFieldKB.HilbertClassField.TauCeti
import NumberFieldKB.MilneANT.Ch4Example46
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Kummer.Ramification
import NumberFieldKB.TauCetiPort.RingTheory.DedekindDomain.Different.Derivative

/-!
# Milne, *Class Field Theory*, Chapter V, Example 3.9 (the Hilbert class field of $\mathbb Q(\sqrt{-5})$), unconditional

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Example 3.9 (p. 159).

`example3_9_sqrt_neg5`: for $K=\mathbb Q(s)$, $s^2=-5$, and a quadratic Galois extension $H/K$ containing $i$, $H$ is the
Hilbert class field of $K$. The class number is $2$ (`MilneANT.Q5.class_number_two`), so by
`HilbertClassField.isHilbertClassField_of_finrank_eq` it suffices that $H/K$ is unramified everywhere. At infinity this
holds since $K$ is totally complex. At a finite prime $\mathfrak p$ of $K$: if $2\notin\mathfrak p$, $H=K(i)$ is a radical
extension and Tau Ceti's `isUnramifiedIn_of_pow_eq_of_valuation_eq_one` applies; otherwise $5\notin\mathfrak p$ and
$H=K(\theta)$, $\theta=(1+s/i)/2$, $\theta^2-\theta-1=0$, a ramified prime would contain $2\theta-1$ (the derivative lies in
the different) hence $5=(2\theta-1)^2$.
-/

open NumberField IsDedekindDomain Polynomial
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

theorem ex39_no_rat_sq_five (q : ℚ) : q ^ 2 ≠ 5 := by
  intro h
  have hirr : Irrational (Real.sqrt 5) := by exact_mod_cast Nat.prime_five.irrational_sqrt
  apply hirr
  refine ⟨|q|, ?_⟩
  push_cast
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  exact_mod_cast h

section Field

variable {K : Type} [Field K] [NumberField K]

theorem ex39_isComplex (s : K) (hs : s ^ 2 = -5) (w : InfinitePlace K) : w.IsComplex := by
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  have := congrArg (w.embedding_of_isReal hw) hs
  simp only [map_pow, map_neg, map_ofNat] at this
  nlinarith [sq_nonneg (w.embedding_of_isReal hw s)]

theorem ex39_s_not_rat (s : K) (hs : s ^ 2 = -5) (q : ℚ) : (q : K) ≠ s := by
  intro hq
  have h1 : ((q ^ 2 : ℚ) : K) = ((-5 : ℚ) : K) := by
    push_cast
    rw [hq]
    exact hs
  have := Rat.cast_injective h1
  nlinarith [sq_nonneg q]

/-- $\sqrt{-1}\notin\mathbb Q(\sqrt{-5})$: three elements of a $2$-dimensional $\mathbb Q$-space are dependent. -/
theorem ex39_no_sqrt_neg_one (hK : Module.finrank ℚ K = 2) (s k : K) (hs : s ^ 2 = -5) (hk : k ^ 2 = -1) :
    False := by
  have hli : ¬ LinearIndependent ℚ ![(1 : K), s, k] := fun h => by
    have := h.fintype_card_le_finrank
    simp [hK] at this
  rw [Fintype.not_linearIndependent_iff] at hli
  obtain ⟨g, hg, i0, hi0⟩ := hli
  obtain ⟨a, b, c, h, hnz⟩ : ∃ a b c : ℚ, (a : K) + b * s + c * k = 0 ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) := by
    refine ⟨g 0, g 1, g 2, ?_, ?_⟩
    · simpa [Fin.sum_univ_three, Rat.smul_def] using hg
    · rintro ⟨h0, h1, h2⟩
      fin_cases i0 <;> simp_all
  have hsq := ex39_s_not_rat s hs
  by_cases hc : c = 0
  · subst hc
    by_cases hb : b = 0
    · subst hb
      have : (a : K) = 0 := by simpa using h
      have ha : a = 0 := by exact_mod_cast this
      exact hnz ⟨ha, rfl, rfl⟩
    · apply hsq (-a / b)
      have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
      push_cast
      field_simp
      linear_combination -h
  · have hc' : (c : K) ≠ 0 := by exact_mod_cast hc
    have hk' : (c : K) * k = -((a : K) + b * s) := by linear_combination h
    have h2 : ((c : K) * k) ^ 2 = ((a : K) + b * s) ^ 2 := by rw [hk']; ring
    have e1 : ((2 * a * b : ℚ) : K) * s = ((-c ^ 2 - a ^ 2 + 5 * b ^ 2 : ℚ) : K) := by
      push_cast
      linear_combination (-1 : K) * h2 + (c : K) ^ 2 * hk - (b : K) ^ 2 * hs
    by_cases hab : 2 * a * b = 0
    · have hab' : a = 0 ∨ b = 0 := by
        rcases mul_eq_zero.1 hab with h1 | h1
        · rcases mul_eq_zero.1 h1 with h2 | h2
          · norm_num at h2
          · exact Or.inl h2
        · exact Or.inr h1
      rcases hab' with ha | hb
      · subst ha
        have e2 : (c : K) ^ 2 = 5 * (b : K) ^ 2 := by
          push_cast at e1
          simp at e1
          linear_combination e1
        have e3 : c ^ 2 = 5 * b ^ 2 := by exact_mod_cast e2
        by_cases hb : b = 0
        · subst hb
          simp at e3
          exact hc e3
        · apply ex39_no_rat_sq_five (c / b)
          field_simp
          linear_combination e3
      · subst hb
        have e3 : -c ^ 2 - a ^ 2 + 5 * 0 ^ 2 = 0 := by
          have : (((-c ^ 2 - a ^ 2 + 5 * 0 ^ 2 : ℚ)) : K) = 0 := by
            rw [← e1]; simp
          exact_mod_cast this
        have : 0 < c ^ 2 := by positivity
        nlinarith [sq_nonneg a]
    · apply hsq ((-c ^ 2 - a ^ 2 + 5 * b ^ 2) / (2 * a * b))
      have hab' : ((2 * a * b : ℚ) : K) ≠ 0 := by exact_mod_cast hab
      rw [Rat.cast_div, div_eq_iff hab']
      push_cast at e1 ⊢
      linear_combination -e1

/-- A prime of `K` whose primes above never contain the derivative `p'(α)` of an annihilating polynomial of a generator `α`
is unramified (the derivative lies in the different). -/
theorem ex39_unram_of_derivative {H : Type} [Field H] [NumberField H] [Algebra K H] (α : 𝓞 H)
    (hα : IntermediateField.adjoin K {(α : H)} = ⊤) (p : (𝓞 K)[X]) (hp : aeval α p = 0) (𝔭 : Ideal (𝓞 K))
    (hnot : ∀ Q : Ideal (𝓞 H), Q.IsPrime → Q.LiesOver 𝔭 → aeval α (derivative p) ∈ Q → False) :
    Algebra.IsUnramifiedIn (𝓞 H) 𝔭 := by
  have hα' : Algebra.adjoin K {algebraMap (𝓞 H) H α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _)]
    exact congrArg IntermediateField.toSubalgebra hα
  intro Q _ _
  by_contra hQ
  have hmem := Ideal.le_of_dvd (dvd_differentIdeal_iff.mpr hQ)
    (TauCeti.aeval_derivative_mem_differentIdeal_of_aeval_eq_zero (K := K) (L := H) hα' hp)
  exact hnot Q ‹_› ‹_› hmem

end Field

section Main

open NumberFieldKB.Chebotarev

/-- **Example 3.9, unconditional** (Milne, *CFT*, V, Example 3.9, p. 159): the Hilbert class field of
$\mathbb Q(\sqrt{-5})$ is $\mathbb Q(\sqrt{-1},\sqrt5)$. -/
@[kb "milne2020cft" "Ch. V, Example 3.9 (Hilbert class field of Q(√-5))"]
theorem example3_9_sqrt_neg5 : Example3_9_sqrt_neg5 := by
  refine ⟨fun K H _ _ _ _ _ _ s i hs hK hi hH => ?_⟩
  have hs' : (algebraMap K H s) ^ 2 = -5 := by
    rw [← map_pow, hs, map_neg, map_ofNat]
  have hik : ∀ k : K, algebraMap K H k ≠ i := by
    intro k hk
    apply ex39_no_sqrt_neg_one hK s k hs
    apply (algebraMap K H).injective
    rw [map_pow, hk, hi]; simp
  have hgen : ∀ x : H, (∀ k : K, algebraMap K H k ≠ x) → IntermediateField.adjoin K {x} = ⊤ := by
    intro x hx
    have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    have h1 : (minpoly K x).natDegree ≤ 2 := hH ▸ minpoly.natDegree_le x
    have h2 : (minpoly K x).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨k, hk⟩
      exact hx k hk
    have h3 : 0 < (minpoly K x).natDegree := minpoly.natDegree_pos hint
    have h4 : (minpoly K x).natDegree = 2 := by omega
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.adjoin.finrank hint, h4, IntermediateField.finrank_top', hH]
  have hi0 : i ≠ 0 := by
    intro h
    rw [h] at hi
    norm_num at hi
  have hs0 : algebraMap K H s ≠ 0 := by
    intro h
    rw [h] at hs'
    norm_num at hs'
  set r : H := algebraMap K H s / i with hr
  have hr2 : r ^ 2 = 5 := by
    rw [hr, div_pow, hs', hi]; norm_num
  set θ : H := (1 + r) / 2 with hθdef
  have hθ : θ ^ 2 = θ + 1 := by
    rw [hθdef]; linear_combination (1 / 4 : H) * hr2
  have hθint : IsIntegral ℤ θ :=
    ⟨X ^ 2 - X - 1, by monicity!, by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
      linear_combination hθ⟩
  let θ' : 𝓞 H := ⟨θ, hθint⟩
  have hθK : ∀ k : K, algebraMap K H k ≠ θ := by
    intro k hk
    apply hik (s / (2 * k - 1))
    have hr0 : r ≠ 0 := by
      intro h; rw [h] at hr2; norm_num at hr2
    have h2θ : 2 * θ - 1 = r := by rw [hθdef]; ring
    have : algebraMap K H (2 * k - 1) = r := by
      rw [map_sub, map_mul, hk, map_one, map_ofNat]; exact h2θ
    have hne : (2 * k - 1 : K) ≠ 0 := by
      intro h; rw [h, map_zero] at this; exact hr0 this.symm
    rw [map_div₀, this, hr]
    field_simp
  have hθadj : IntermediateField.adjoin K {(θ' : H)} = ⊤ := hgen θ hθK
  have hunr : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∈ unramifiedPrimes K H := by
    intro 𝔭
    by_cases h2 : (2 : 𝓞 K) ∈ 𝔭.asIdeal
    · have h5 : (5 : 𝓞 K) ∉ 𝔭.asIdeal := by
        intro h5
        have h1 : (1 : 𝓞 K) ∈ 𝔭.asIdeal := by
          have : (1 : 𝓞 K) = 5 - 2 * 2 := by norm_num
          rw [this]
          exact Ideal.sub_mem _ h5 (Ideal.mul_mem_right _ _ h2)
        exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
      refine ex39_unram_of_derivative θ' hθadj (X ^ 2 - X - 1) ?_ 𝔭.asIdeal ?_
      · apply Subtype.ext
        simp only [aeval_sub, aeval_X_pow, aeval_X, map_one]
        show θ ^ 2 - θ - 1 = 0
        linear_combination hθ
      · intro Q hQ hlies hmem
        have e : aeval θ' (derivative (X ^ 2 - X - 1 : (𝓞 K)[X])) = 2 * θ' - 1 := by
          simp
          exact Or.inl one_add_one_eq_two
        have e5 : algebraMap (𝓞 K) (𝓞 H) 5 = (2 * θ' - 1) ^ 2 := by
          rw [map_ofNat]
          apply Subtype.ext
          show (5 : H) = (2 * θ - 1) ^ 2
          have h2θ : 2 * θ - 1 = r := by rw [hθdef]; ring
          rw [h2θ, hr2]
        have : algebraMap (𝓞 K) (𝓞 H) 5 ∈ Q := by
          rw [e5]
          exact Ideal.pow_mem_of_mem Q (e ▸ hmem) 2 (by norm_num)
        exact h5 ((Ideal.mem_of_liesOver Q 𝔭.asIdeal 5).2 this)
    · exact TauCeti.NumberField.isUnramifiedIn_of_pow_eq_of_valuation_eq_one (hgen i hik) (n := 2) (a := -1)
        (by rw [hi, map_neg, map_one]) (by simpa using h2) (by simp)
  have hinf : IsUnramifiedAtInfinitePlaces K H := ⟨fun w => by
    by_contra h
    rw [InfinitePlace.not_isUnramified_iff] at h
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (ex39_isComplex s hs _)) h.2⟩
  have hcard : Nat.card Gal(H/K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hH]
  have hab : ∀ σ τ : Gal(H/K), σ * τ = τ * σ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic Gal(H/K) := isCyclic_of_prime_card (p := 2) hcard
    intro σ τ
    let _ : CommGroup Gal(H/K) := IsCyclic.commGroup
    exact mul_comm σ τ
  have hsint : IsIntegral ℤ s := ⟨X ^ 2 + 5, by monicity!, by
    simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_ofNat]
    linear_combination hs⟩
  let s0 : 𝓞 K := ⟨s, hsint⟩
  have hs0' : s0 ^ 2 = -5 := Subtype.ext (by exact hs)
  have hcl : classNumber K = 2 := NumberFieldKB.MilneANT.Q5.class_number_two hK s0 hs0'
  have hdeg : Module.finrank K H = classNumber K := by rw [hH, hcl]
  obtain ⟨ψ, hψ⟩ := (HilbertClassField.unramifiedArtinReciprocityInput K).exists_artin H hab hunr hinf
  exact HilbertClassField.isHilbertClassField_of_finrank_eq hunr hinf hdeg ψ hψ

end Main

end NumberFieldKB.MilneCFT
