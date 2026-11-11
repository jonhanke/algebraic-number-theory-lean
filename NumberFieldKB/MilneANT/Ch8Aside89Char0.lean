import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch8Aside89Basic

/-!
# Milne, *Algebraic Number Theory*, Aside 8.9 (Artin–Whaples): characteristic zero

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Aside 8.9, p. 138; bib key `milne2020ant`.
E. Artin, *Algebraic Numbers and Algebraic Functions*, Ch. 12.

If `K` has characteristic zero, `V` satisfies the Artin–Whaples axioms and some `v₀ ∈ V` satisfies the packing bound,
then `K` is finite-dimensional over `ℚ` (`finiteDimensional_rat`). This is Artin's counting argument: a
`ℚ`-linearly independent family `x₁, …, xₙ` gives `(2N+1)ⁿ` distinct points `∑ aᵢ xᵢ` (`|aᵢ| ≤ N`) in a `v₀`-ball of
radius `≍ N`, pairwise at `v₀`-distance `≳ N^{-|A|}` by the product formula (`one_le_prod`), where `A` is the
finite set of archimedean members of `V`. The packing bound then forces `n ≤ (|A|+1)κ`.
-/

open scoped BigOperators
open Finset

namespace NumberFieldKB.MilneANT.Aside89

variable {K : Type*} [Field K]

/-- If `v 2 ≤ 1` then `v n ≤ log₂ n + 1` for every natural number `n`. -/
lemma apply_natCast_le_log (v : AbsoluteValue K ℝ) (h2 : v 2 ≤ 1) (n : ℕ) :
    v (n : K) ≤ Nat.log 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
      have hlog : Nat.log 2 n = Nat.log 2 (n / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by norm_num) hn
      have hcast : (n : K) = 2 * ((n / 2 : ℕ) : K) + ((n % 2 : ℕ) : K) := by
        have := Nat.div_add_mod n 2
        conv_lhs => rw [← this]
        push_cast
        ring
      have hmod : v ((n % 2 : ℕ) : K) ≤ 1 := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
      have hih := ih (n / 2) hlt
      calc v (n : K) = v (2 * ((n / 2 : ℕ) : K) + ((n % 2 : ℕ) : K)) := by rw [← hcast]
        _ ≤ v (2 * ((n / 2 : ℕ) : K)) + v ((n % 2 : ℕ) : K) := v.add_le _ _
        _ = v 2 * v ((n / 2 : ℕ) : K) + v ((n % 2 : ℕ) : K) := by rw [map_mul]
        _ ≤ 1 * ((Nat.log 2 (n / 2) : ℝ) + 1) + 1 := by
            have := v.nonneg ((n / 2 : ℕ) : K)
            have := v.nonneg (2 : K)
            nlinarith
        _ = (Nat.log 2 n : ℝ) + 1 := by rw [hlog]; push_cast; ring

/-- An absolute value with `v 2 ≤ 1` is bounded by `1` on the natural numbers. -/
lemma natCast_le_one (v : AbsoluteValue K ℝ) (h2 : v 2 ≤ 1) (n : ℕ) : v (n : K) ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hcon
    linarith
  set b := v (n : K) with hb
  set c : ℝ := (Nat.log 2 n : ℝ) + 1 with hc
  have hcpos : 0 < c := by positivity
  have hk : ∀ k : ℕ, 1 ≤ k → b ^ k ≤ c * k := by
    intro k hk1
    have hpow : b ^ k = v (((n ^ k : ℕ)) : K) := by
      rw [hb, ← map_pow]; push_cast; rfl
    have h1 := apply_natCast_le_log v h2 (n ^ k)
    have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hlt2 : n ^ k < 2 ^ ((Nat.log 2 n + 1) * k) := by
      rw [pow_mul]
      exact Nat.pow_lt_pow_left hlt (by omega)
    have hlt3 : Nat.log 2 (n ^ k) < (Nat.log 2 n + 1) * k :=
      Nat.log_lt_of_lt_pow (pow_ne_zero _ hn) hlt2
    have hlt4 : (Nat.log 2 (n ^ k) : ℝ) + 1 ≤ c * k := by
      have : Nat.log 2 (n ^ k) + 1 ≤ (Nat.log 2 n + 1) * k := hlt3
      have h5 : ((Nat.log 2 (n ^ k) + 1 : ℕ) : ℝ) ≤ (((Nat.log 2 n + 1) * k : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at h5
      rw [hc]
      linarith
    rw [hpow]
    exact h1.trans hlt4
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hcon
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / c by positivity))).and
    (Filter.eventually_ge_atTop 1)
  obtain ⟨k, hk1, hk2⟩ := hev.exists
  have hbpos : 0 < b ^ k := by positivity
  have h3 := hk k hk2
  rw [pow_one, div_lt_div_iff₀ hbpos hcpos] at hk1
  nlinarith

/-- An absolute value with `v 2 ≤ 1` is nonarchimedean. -/
lemma isNonarchimedean_of_two_le_one (v : AbsoluteValue K ℝ) (h2 : v 2 ≤ 1) :
    IsNonarchimedean v := by
  let _ : NormedField K := v.toNormedField
  have : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one (natCast_le_one v h2)
  exact IsUltrametricDist.isNonarchimedean_norm

lemma intCast_le_one (v : AbsoluteValue K ℝ) (h2 : v 2 ≤ 1) (a : ℤ) : v (a : K) ≤ 1 := by
  rcases Int.eq_nat_or_neg a with ⟨m, rfl | rfl⟩
  · simpa using natCast_le_one v h2 m
  · simpa using natCast_le_one v h2 m

lemma abs_intCast_le (v : AbsoluteValue K ℝ) (a : ℤ) : v (a : K) ≤ |(a : ℝ)| := by
  rcases Int.eq_nat_or_neg a with ⟨m, rfl | rfl⟩
  · simpa using v.apply_nat_le_self m
  · simpa using v.apply_nat_le_self m

lemma sum_le_of_nonarch {ι : Type*} (s : Finset ι) (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (f : ι → K) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ i ∈ s, v (f i) ≤ B) : v (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hv _ _).trans (max_le (hf a (mem_insert_self _ _))
      (ih fun i hi => hf i (mem_insert_of_mem hi)))

lemma sum_int_le {n : ℕ} (v : AbsoluteValue K ℝ) (x : Fin n → K) (b : Fin n → ℤ) (m : ℕ)
    (hb : ∀ i, |b i| ≤ m) : v (∑ i, (b i : K) * x i) ≤ m * ∑ i, v (x i) := by
  calc v (∑ i, (b i : K) * x i) ≤ ∑ i, v ((b i : K) * x i) := v.sum_le _ _
    _ = ∑ i, v (b i : K) * v (x i) := by simp [map_mul]
    _ ≤ ∑ i, (m : ℝ) * v (x i) := by
        refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ((abs_intCast_le v _).trans ?_)
          (v.nonneg _)
        exact_mod_cast hb i
    _ = m * ∑ i, v (x i) := by rw [mul_sum]

lemma sum_int_le_of_two_le_one {n : ℕ} (v : AbsoluteValue K ℝ) (h2 : v 2 ≤ 1) (x : Fin n → K)
    (b : Fin n → ℤ) (B : ℝ) (hB : 0 ≤ B) (hx : ∀ i, v (x i) ≤ B) : v (∑ i, (b i : K) * x i) ≤ B := by
  refine sum_le_of_nonarch _ v (isNonarchimedean_of_two_le_one v h2) _ B hB fun i _ => ?_
  rw [map_mul]
  calc v (b i : K) * v (x i) ≤ 1 * B :=
        mul_le_mul (intCast_le_one v h2 _) (hx i) (v.nonneg _) zero_le_one
    _ = B := one_mul B

/-- Artin's counting argument: the size of a `ℚ`-linearly independent family in `K` is bounded. -/
theorem rank_le [CharZero K] {V : Set (AbsoluteValue K ℝ)} (hV : AWAxioms V)
    {v₀ : AbsoluteValue K ℝ} (hv₀ : v₀ ∈ V) (hpack : PackingBound v₀) :
    ∃ s : ℝ, ∀ (n : ℕ) (x : Fin n → K), LinearIndependent ℚ x → (n : ℝ) ≤ s := by
  classical
  obtain ⟨C, κ, hC, hκ, hP⟩ := hpack
  have hAfin : {v ∈ V | 1 < v 2}.Finite :=
    (hV.prod 2 two_ne_zero).1.subset fun v hv => ⟨hv.1, ne_of_gt hv.2⟩
  set A := hAfin.toFinset with hAdef
  have hAmem : ∀ v, v ∈ A ↔ v ∈ V ∧ 1 < v 2 := by
    intro v; simp [hAdef]
  refine ⟨((A.card : ℝ) + 1) * κ, ?_⟩
  intro n x hx
  by_contra hcon
  push Not at hcon
  have hx0 : ∀ i, x i ≠ 0 := fun i => hx.ne_zero i
  have hfin : {v | v ∈ V ∧ ∃ i, v (x i) ≠ 1}.Finite := by
    have : {v | v ∈ V ∧ ∃ i, v (x i) ≠ 1} = ⋃ i, {v ∈ V | v (x i) ≠ 1} := by
      ext v; simp
    rw [this]
    exact Set.finite_iUnion fun i => (hV.prod _ (hx0 i)).1
  set T : Finset (AbsoluteValue K ℝ) := insert v₀ (A ∪ hfin.toFinset) with hT
  have hTmem : ∀ v, v ∈ T ↔ v = v₀ ∨ (v ∈ V ∧ 1 < v 2) ∨ (v ∈ V ∧ ∃ i, v (x i) ≠ 1) := by
    intro v; simp [hT, hAdef]
  have hTV : (T : Set (AbsoluteValue K ℝ)) ⊆ V := by
    intro v hv
    rcases (hTmem v).1 hv with rfl | h | h
    · exact hv₀
    · exact h.1
    · exact h.1
  have hv₀T : v₀ ∈ T := (hTmem v₀).2 (Or.inl rfl)
  have hAT : A ⊆ T := fun v hv => (hTmem v).2 (Or.inr (Or.inl ((hAmem v).1 hv)))
  set M : AbsoluteValue K ℝ → ℝ := fun v => 1 + ∑ i, v (x i) with hMdef
  have hsum_nonneg : ∀ v : AbsoluteValue K ℝ, 0 ≤ ∑ i, v (x i) :=
    fun v => sum_nonneg fun i _ => v.nonneg _
  have hM1 : ∀ v : AbsoluteValue K ℝ, 1 ≤ M v := fun v => by
    have := hsum_nonneg v; simp only [hMdef]; linarith
  have hMx : ∀ (v : AbsoluteValue K ℝ) (i : Fin n), v (x i) ≤ ∑ j, v (x j) := fun v i =>
    single_le_sum (f := fun j => v (x j)) (fun j _ => v.nonneg _) (mem_univ i)
  set P : ℝ := ∏ v ∈ T, M v with hPdef
  have hQ1 : 1 ≤ ∏ v ∈ T.erase v₀, M v := by
    refine one_le_prod₀ (fun v _ => hM1 v)
  have hPeq : M v₀ * ∏ v ∈ T.erase v₀, M v = P := mul_prod_erase T M hv₀T
  have hP1 : 1 ≤ P := by nlinarith [hM1 v₀]
  have hQP : ∏ v ∈ T.erase v₀, M v ≤ P := by nlinarith [hM1 v₀]
  have hMP : M v₀ ≤ P := by nlinarith [hM1 v₀]
  have hPpos : 0 < P := by linarith
  -- the main inequality
  have key : ∀ N : ℕ, 1 ≤ N →
      (((2 * N + 1 : ℕ) ^ n : ℕ) : ℝ) ≤ C * (((N : ℝ) * P) * ((2 * N : ℝ) ^ A.card * P)) ^ κ := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h2N : (1 : ℝ) ≤ 2 * N := by linarith
    set D : ℝ := (2 * N : ℝ) ^ A.card * P with hD
    have hD1 : 1 ≤ D := by
      have : (1 : ℝ) ≤ (2 * N : ℝ) ^ A.card := one_le_pow₀ h2N
      rw [hD]; nlinarith
    have hDpos : 0 < D := by linarith
    set ε : ℝ := 1 / D with hε
    have hεpos : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by rw [hε]; exact (div_le_one hDpos).2 hD1
    have hεR : ε ≤ N * P := by nlinarith
    let g : (Fin n → Fin (2 * N + 1)) → K :=
      fun c => ∑ i, ((((c i : ℕ) : ℤ) - N : ℤ) : K) * x i
    have hg : Function.Injective g := by
      intro c c' h
      have h0 : ∑ i, ((((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ) : ℤ) : ℚ) • x i = 0 := by
        have : g c - g c' = 0 := sub_eq_zero.2 h
        rw [← this]
        simp only [g, ← Finset.sum_sub_distrib]
        refine sum_congr rfl fun i _ => ?_
        rw [Rat.smul_def]
        push_cast
        ring
      have h1 := Fintype.linearIndependent_iff.1 hx _ h0
      funext i
      have h3 := h1 i
      apply Fin.ext
      have h4 : (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ)) = 0 := by exact_mod_cast h3
      omega
    set S : Finset K := univ.image g with hS
    have hScard : S.card = (2 * N + 1) ^ n := by
      rw [hS, card_image_of_injective _ hg]; simp
    have hSR : ∀ y ∈ S, v₀ y ≤ N * P := by
      intro y hy
      obtain ⟨c, -, rfl⟩ := mem_image.1 hy
      have h1 := sum_int_le v₀ x (fun i => (((c i : ℕ) : ℤ) - N : ℤ)) N (fun i => by
        have := (c i).isLt
        rw [abs_le]; constructor <;> omega)
      refine h1.trans ?_
      have : ∑ i, v₀ (x i) ≤ P := by
        have : M v₀ = 1 + ∑ i, v₀ (x i) := rfl
        linarith
      nlinarith
    have hSsep : ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → ε ≤ v₀ (y - y') := by
      intro y hy y' hy' hne
      obtain ⟨c, -, rfl⟩ := mem_image.1 hy
      obtain ⟨c', -, rfl⟩ := mem_image.1 hy'
      set b : Fin n → ℤ := fun i => ((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ) with hb
      have hbN : ∀ i, |b i| ≤ ((2 * N : ℕ) : ℤ) := fun i => by
        have := (c i).isLt
        have := (c' i).isLt
        rw [abs_le]; constructor <;> (simp only [hb]; push_cast; omega)
      have hz : g c - g c' = ∑ i, (b i : K) * x i := by
        simp only [g, hb, ← Finset.sum_sub_distrib]
        refine sum_congr rfl fun i _ => ?_
        push_cast
        ring
      obtain ⟨z, hzdef⟩ : ∃ z : K, z = g c - g c' := ⟨_, rfl⟩
      have hz' : z = ∑ i, (b i : K) * x i := hzdef.trans hz
      have hz0 : z ≠ 0 := by rw [hzdef]; exact sub_ne_zero.2 hne
      have hout : ∀ v ∈ V, v ∉ T → v z ≤ 1 := by
        intro v hvV hvT
        have h2 : v 2 ≤ 1 := by
          by_contra h
          push Not at h
          exact hvT ((hTmem v).2 (Or.inr (Or.inl ⟨hvV, h⟩)))
        have hxv : ∀ i, v (x i) ≤ 1 := by
          intro i
          by_contra h
          push Not at h
          exact hvT ((hTmem v).2 (Or.inr (Or.inr ⟨hvV, i, ne_of_gt h⟩)))
        rw [hz']
        exact sum_int_le_of_two_le_one v h2 x b 1 zero_le_one hxv
      have hprod := one_le_prod hV hz0 T hTV hout
      -- local bounds
      set c₁ : AbsoluteValue K ℝ → ℝ := fun v => if v ∈ A then (2 * N : ℝ) else 1 with hc₁
      have hc₁1 : ∀ v, 1 ≤ c₁ v := fun v => by
        simp only [hc₁]; split_ifs <;> linarith
      have hloc : ∀ v ∈ T, v z ≤ c₁ v * M v := by
        intro v hvT
        have hvV : v ∈ V := hTV hvT
        by_cases hvA : v ∈ A
        · have h1 := sum_int_le v x b (2 * N) hbN
          have h3 : v z ≤ ((2 * N : ℕ) : ℝ) * ∑ i, v (x i) := by rw [hz']; exact h1
          have h4 : c₁ v = 2 * N := by simp [hc₁, hvA]
          rw [h4]
          have h5 := hsum_nonneg v
          have : M v = 1 + ∑ i, v (x i) := rfl
          push_cast at h3
          nlinarith
        · have h2 : v 2 ≤ 1 := by
            by_contra h
            push Not at h
            exact hvA ((hAmem v).2 ⟨hvV, h⟩)
          have h4 : c₁ v = 1 := by simp [hc₁, hvA]
          rw [h4, one_mul]
          have h3 := sum_int_le_of_two_le_one v h2 x b (∑ i, v (x i)) (hsum_nonneg v)
            (fun i => hMx v i)
          rw [hz']
          have : M v = 1 + ∑ i, v (x i) := rfl
          linarith
      have hprod2 : ∏ v ∈ T, v z ≤ ∏ v ∈ T, (c₁ v * M v) :=
        prod_le_prod₀ (fun v _ => v.nonneg _) hloc
      rw [← mul_prod_erase T (fun v => v z) hv₀T,
        ← mul_prod_erase T (fun v => c₁ v * M v) hv₀T] at hprod2
      rw [← mul_prod_erase T (fun v => v z) hv₀T] at hprod
      have hE : ∏ v ∈ T.erase v₀, v z ≤ ∏ v ∈ T.erase v₀, (c₁ v * M v) :=
        prod_le_prod₀ (fun v _ => v.nonneg _) (fun v hv => hloc v (mem_of_mem_erase hv))
      rw [prod_mul_distrib] at hE
      have hcprod : ∏ v ∈ T.erase v₀, c₁ v ≤ (2 * N : ℝ) ^ A.card := by
        have e1 : ∏ v ∈ T.erase v₀, c₁ v = (2 * N : ℝ) ^ ((T.erase v₀).filter (· ∈ A)).card := by
          simp only [hc₁]
          rw [prod_ite]
          simp
        rw [e1]
        refine pow_le_pow_right₀ h2N (card_le_card ?_)
        intro v hv
        exact (mem_filter.1 hv).2
      have hcprod0 : 0 ≤ ∏ v ∈ T.erase v₀, c₁ v := prod_nonneg fun v _ => by linarith [hc₁1 v]
      have hQ0 : 0 ≤ ∏ v ∈ T.erase v₀, M v := by linarith
      have hE2 : ∏ v ∈ T.erase v₀, v z ≤ D := by
        refine hE.trans ?_
        rw [hD]
        exact mul_le_mul hcprod hQP hQ0 (by positivity)
      have hv₀z : 1 ≤ v₀ z * D := by
        have h0 : 0 ≤ v₀ z := v₀.nonneg _
        calc (1 : ℝ) ≤ v₀ z * ∏ v ∈ T.erase v₀, v z := hprod
          _ ≤ v₀ z * D := mul_le_mul_of_nonneg_left hE2 h0
      rw [← hzdef, hε]
      exact (div_le_iff₀ hDpos).2 (by linarith)
    have hmain := hP (N * P) ε hεpos hεR S hSR hSsep
    have hrat : (N * P) / ε = ((N : ℝ) * P) * ((2 * N : ℝ) ^ A.card * P) := by
      rw [hε, one_div, div_inv_eq_mul]
    rw [hrat] at hmain
    rw [← hScard]
    exact hmain
  -- asymptotics
  set a : ℕ := A.card with ha
  set s : ℝ := ((a : ℝ) + 1) * κ with hs
  set D' : ℝ := 2 ^ a * P ^ 2 with hD'
  have hD'pos : 0 < D' := by positivity
  set C' : ℝ := C * D' ^ κ with hC'
  have hC'pos : 0 < C' := by positivity
  have hgrow : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ^ n ≤ C' * (N : ℝ) ^ s := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := by linarith
    have h1 := key N hN
    have h2 : (N : ℝ) ^ n ≤ (((2 * N + 1 : ℕ) ^ n : ℕ) : ℝ) := by
      push_cast
      exact pow_le_pow_left₀ hNpos.le (by linarith) n
    have h3 : ((N : ℝ) * P) * ((2 * N : ℝ) ^ a * P) = D' * (N : ℝ) ^ (a + 1) := by
      rw [hD', mul_pow]; ring
    rw [h3, Real.mul_rpow hD'pos.le (by positivity)] at h1
    have h4 : ((N : ℝ) ^ (a + 1)) ^ κ = (N : ℝ) ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, hs]
      push_cast
      rfl
    rw [h4] at h1
    calc (N : ℝ) ^ n ≤ _ := h2
      _ ≤ _ := h1
      _ = C' * (N : ℝ) ^ s := by rw [hC']; ring
  have hpos : 0 < (n : ℝ) - s := by linarith
  have ht : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ ((n : ℝ) - s)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hpos).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN2, hN1⟩ := ((ht.eventually_gt_atTop C').and (Filter.eventually_ge_atTop 1)).exists
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have h1 := hgrow N hN1
  have h2 : (N : ℝ) ^ (n : ℝ) = (N : ℝ) ^ ((n : ℝ) - s) * (N : ℝ) ^ s := by
    rw [← Real.rpow_add hNpos]; ring_nf
  rw [← Real.rpow_natCast, h2] at h1
  have hspos : 0 < (N : ℝ) ^ s := by positivity
  nlinarith

/-- **Aside 8.9 (characteristic zero)**: a field of characteristic zero with a set `V` of absolute values satisfying
the Artin–Whaples axioms, one member of which satisfies the packing bound, is finite-dimensional over `ℚ`. -/
@[kb "milne2020ant" "v3.08, Aside 8.9, p. 138"]
theorem finiteDimensional_rat {K : Type*} [Field K] [CharZero K] {V : Set (AbsoluteValue K ℝ)}
    (hV : AWAxioms V) {v₀ : AbsoluteValue K ℝ} (hv₀ : v₀ ∈ V) (hpack : PackingBound v₀) :
    FiniteDimensional ℚ K := by
  obtain ⟨s, hs⟩ := rank_le hV hv₀ hpack
  let b := Module.Basis.ofVectorSpace ℚ K
  have hfin : Finite (Module.Basis.ofVectorSpaceIndex ℚ K) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    obtain ⟨m, hm⟩ := exists_nat_gt s
    let e : Fin m ↪ Module.Basis.ofVectorSpaceIndex ℚ K :=
      Fin.valEmbedding.trans (Infinite.natEmbedding _)
    have hli : LinearIndependent ℚ (fun i : Fin m => b (e i)) :=
      b.linearIndependent.comp e e.injective
    have := hs m _ hli
    linarith
  exact Module.Finite.of_basis b

end NumberFieldKB.MilneANT.Aside89
