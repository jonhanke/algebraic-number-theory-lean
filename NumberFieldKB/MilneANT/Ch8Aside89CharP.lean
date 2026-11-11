import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch8Aside89Basic

/-!
# Milne, *Algebraic Number Theory*, Aside 8.9 (Artin–Whaples): the characteristic `p` case

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Aside 8.9, p. 138; bib key `milne2020ant`.
E. Artin, *Algebraic Numbers and Algebraic Functions*, Ch. 12.

In characteristic `p`, a field `K` with a set `V` of absolute values satisfying the Artin–Whaples axioms and with
a packing bound at one `v₀ ∈ V` is a finite extension of `𝔽_p(t)` (`exists_ratFunc_finiteDimensional`).
Artin's counting argument: all absolute values are nonarchimedean and trivial on the algebraic elements over
`𝔽_p`; pick `t` transcendental, and bound the number of elements `∑ aᵢ(t) xᵢ` (`deg aᵢ < N`) by the packing bound
and the product formula (`one_le_prod`), which bounds the size of an `𝔽_p(t)`-linearly independent family.
-/

open scoped BigOperators Polynomial

namespace NumberFieldKB.MilneANT.Aside89

section Basic

variable {K : Type*} [Field K]

lemma abv_eq_one_of_pow_eq_one (v : AbsoluteValue K ℝ) {y : K} {m : ℕ} (hm : m ≠ 0) (h : y ^ m = 1) :
    v y = 1 := by
  have := congrArg v h
  rw [map_pow, map_one] at this
  exact (pow_eq_one_iff_of_nonneg (v.nonneg y) hm).1 this

lemma abv_zmod_le_one (p : ℕ) [Fact p.Prime] [CharP K p] (v : AbsoluteValue K ℝ) (a : ZMod p) :
    v (ZMod.castHom (dvd_refl p) K a) ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · have h1 : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
    have h2 : (ZMod.castHom (dvd_refl p) K a) ^ (p - 1) = 1 := by
      rw [← map_pow, h1, map_one]
    have hp : p - 1 ≠ 0 := by
      have := (Fact.out : p.Prime).two_le
      omega
    exact (abv_eq_one_of_pow_eq_one v hp h2).le

lemma abv_natCast_le_one (p : ℕ) [Fact p.Prime] [CharP K p] (v : AbsoluteValue K ℝ) (n : ℕ) : v (n : K) ≤ 1 := by
  have := abv_zmod_le_one p v (n : ZMod p)
  simpa using this

lemma isNonarch (p : ℕ) [Fact p.Prime] [CharP K p] (v : AbsoluteValue K ℝ) (x y : K) : v (x + y) ≤ max (v x) (v y) := by
  let _ : NormedField K := v.toNormedField
  have : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
      (fun n => abv_natCast_le_one p v n)
  exact IsUltrametricDist.isNonarchimedean_norm x y

lemma abv_sum_le (p : ℕ) [Fact p.Prime] [CharP K p] (v : AbsoluteValue K ℝ) {ι : Type*} (s : Finset ι) (f : ι → K) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ s, v (f i) ≤ b) : v (∑ i ∈ s, f i) ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hb
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (isNonarch p v _ _).trans (max_le (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma abv_eq_one_of_isAlgebraic (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] (v : AbsoluteValue K ℝ) {y : K}
    (hy : IsAlgebraic (ZMod p) y) (h0 : y ≠ 0) : v y = 1 := by
  have : FiniteDimensional (ZMod p) (IntermediateField.adjoin (ZMod p) {y}) :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  have : Finite (IntermediateField.adjoin (ZMod p) {y}) := Module.finite_of_finite (ZMod p)
  have := Fintype.ofFinite (IntermediateField.adjoin (ZMod p) {y})
  let z : IntermediateField.adjoin (ZMod p) {y} := ⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩
  have hz : z ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one z hz
  have h2 : y ^ (Fintype.card (IntermediateField.adjoin (ZMod p) {y}) - 1) = 1 :=
    congrArg Subtype.val h1
  refine abv_eq_one_of_pow_eq_one v ?_ h2
  have := Fintype.one_lt_card (α := IntermediateField.adjoin (ZMod p) {y})
  omega

end Basic

section Comb

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The element `∑ₓ ∑ⱼ cₓⱼ tʲ x` of `K` attached to coefficients `c`. -/
noncomputable def comb (t : K) (s : Finset K) (N : ℕ) (c : s → Fin N → ZMod p) : K :=
  ∑ x : s, ∑ j : Fin N, ZMod.castHom (dvd_refl p) K (c x j) * t ^ (j : ℕ) * (x : K)

lemma comb_sub (t : K) (s : Finset K) (N : ℕ) (c c' : s → Fin N → ZMod p) :
    comb p t s N (c - c') = comb p t s N c - comb p t s N c' := by
  simp only [comb, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

lemma abv_comb_le (v : AbsoluteValue K ℝ) (t : K) (s : Finset K) (N : ℕ) (c : s → Fin N → ZMod p)
    {τ m : ℝ} (hτ : 1 ≤ τ) (hm : 0 ≤ m) (ht : v t ≤ τ) (hx : ∀ x ∈ s, v x ≤ m) :
    v (comb p t s N c) ≤ m * τ ^ (N - 1) := by
  have hb : 0 ≤ m * τ ^ (N - 1) := mul_nonneg hm (pow_nonneg (by linarith) _)
  unfold comb
  refine abv_sum_le p v _ _ hb (fun x _ => abv_sum_le p v _ _ hb (fun j _ => ?_))
  rw [map_mul, map_mul, map_pow]
  have h1 := abv_zmod_le_one p v (c x j)
  have h2 : v t ^ (j : ℕ) ≤ τ ^ (N - 1) :=
    (pow_le_pow_left₀ (v.nonneg t) ht _).trans (pow_le_pow_right₀ hτ (by omega))
  have h3 : v (x : K) ≤ m := hx x x.2
  calc _ ≤ 1 * τ ^ (N - 1) * m :=
        mul_le_mul (mul_le_mul h1 h2 (pow_nonneg (v.nonneg t) _) zero_le_one) h3 (v.nonneg _)
          (by positivity)
    _ = m * τ ^ (N - 1) := by ring

lemma comb_eq_zero [Algebra (RatFunc (ZMod p)) K] (s : Finset K)
    (hli : LinearIndependent (RatFunc (ZMod p)) (fun i : s => (i : K))) (N : ℕ)
    (c : s → Fin N → ZMod p)
    (h : comb p (algebraMap (RatFunc (ZMod p)) K RatFunc.X) s N c = 0) : c = 0 := by
  let φ : (ZMod p)[X] →+* K :=
    (algebraMap (RatFunc (ZMod p)) K).comp (algebraMap (ZMod p)[X] (RatFunc (ZMod p)))
  have hφC : ∀ a, φ (Polynomial.C a) = ZMod.castHom (dvd_refl p) K a := fun a => by
    have := RingHom.ext_zmod (φ.comp Polynomial.C) (ZMod.castHom (dvd_refl p) K)
    exact DFunLike.congr_fun this a
  have hφX : φ Polynomial.X = algebraMap (RatFunc (ZMod p)) K RatFunc.X := by
    show algebraMap (RatFunc (ZMod p)) K (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) Polynomial.X) = _
    rw [RatFunc.algebraMap_X]
  let P : s → (ZMod p)[X] := fun x => ∑ j : Fin N, Polynomial.C (c x j) * Polynomial.X ^ (j : ℕ)
  have hP : ∀ x, φ (P x) = ∑ j : Fin N,
      ZMod.castHom (dvd_refl p) K (c x j) * (algebraMap (RatFunc (ZMod p)) K RatFunc.X) ^ (j : ℕ) := by
    intro x
    simp [P, map_sum, map_mul, map_pow, hφC, hφX]
  have hsum : ∑ x : s, (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (P x)) • (x : K) = 0 := by
    rw [← h]
    unfold comb
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Algebra.smul_def, ← Finset.sum_mul]
    have := hP x
    simp only [φ, RingHom.comp_apply] at this
    rw [this]
  have hz := Fintype.linearIndependent_iff.1 hli _ hsum
  funext x j
  have hx0 : P x = 0 := (RatFunc.algebraMap_injective (ZMod p)) (by simpa using hz x)
  have := congrArg (fun q => q.coeff (j : ℕ)) hx0
  simpa [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Fin.val_inj] using this

end Comb

section Asymptotic

lemma aux_log (n L h κ c0 : ℝ) (hκ : 0 ≤ κ) (hh : 0 ≤ h)
    (H : ∀ N : ℕ, 1 ≤ N → n * N * L ≤ c0 + 2 * κ * ((N : ℝ) - 1) * h) : n * L ≤ 2 * κ * h := by
  by_contra hcon
  push Not at hcon
  set δ := n * L - 2 * κ * h with hδ
  have hδpos : 0 < δ := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (c0 / δ)
  have h1 := H (k + 1) (by omega)
  push_cast at h1
  have : c0 < δ * k := by
    rw [div_lt_iff₀ hδpos] at hk
    linarith
  have hκh : 0 ≤ κ * h := mul_nonneg hκ hh
  nlinarith

lemma finiteDimensional_of_bound {F E : Type*} [Field F] [Field E] [Algebra F E] (B : ℕ)
    (h : ∀ s : Finset E, LinearIndependent F (fun i : s => (i : E)) → s.card ≤ B) :
    FiniteDimensional F E := by
  have := rank_le h
  exact Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt this (Cardinal.natCast_lt_aleph0))

end Asymptotic

section Main

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

lemma one_le_prod_real {ι : Type*} (S : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ S, 1 ≤ f i) :
    1 ≤ ∏ i ∈ S, f i := by
  calc (1 : ℝ) = ∏ _i ∈ S, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h

open Classical in
/-- Artin's counting argument: an explicit bound on the size of an independent family. -/
lemma exists_card_bound [Algebra (RatFunc (ZMod p)) K] {V : Set (AbsoluteValue K ℝ)} (hV : AWAxioms V)
    {v₀ : AbsoluteValue K ℝ} (hv₀ : v₀ ∈ V) (hpack : PackingBound v₀) :
    ∃ B : ℕ, ∀ s : Finset K, LinearIndependent (RatFunc (ZMod p)) (fun i : s => (i : K)) →
      s.card ≤ B := by
  set t : K := algebraMap (RatFunc (ZMod p)) K RatFunc.X with ht
  have ht0 : t ≠ 0 := (map_ne_zero _).2 RatFunc.X_ne_zero
  obtain ⟨C, κ, hC, hκ, hpk⟩ := hpack
  obtain ⟨hfin, -⟩ := hV.prod t ht0
  set Ht : Finset (AbsoluteValue K ℝ) := hfin.toFinset with hHt
  let τ : AbsoluteValue K ℝ → ℝ := fun v => max 1 (v t)
  have hτ1 : ∀ v, 1 ≤ τ v := fun v => le_max_left _ _
  set H : ℝ := ∏ v ∈ Ht, τ v with hH
  have hH1 : 1 ≤ H := one_le_prod_real _ _ (fun v _ => hτ1 v)
  have hHpos : 0 < H := by linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hL : 0 < Real.log p := Real.log_pos hp1
  refine ⟨⌈2 * κ * Real.log H / Real.log p⌉₊, fun s hli => ?_⟩
  have hs0 : ∀ x ∈ s, x ≠ 0 := fun x hx => hli.ne_zero ⟨x, hx⟩
  let Hx : K → Finset (AbsoluteValue K ℝ) := fun x =>
    if h : x ≠ 0 then (hV.prod x h).1.toFinset else ∅
  have hHx : ∀ x ≠ 0, ∀ v ∈ V, v x ≠ 1 → v ∈ Hx x := by
    intro x hx v hv hvx
    simp [Hx, hx, Set.Finite.mem_toFinset, hv, hvx]
  have hHxV : ∀ x v, v ∈ Hx x → v ∈ V := by
    intro x v hv
    by_cases hx : x ≠ 0
    · have h1 : Hx x = (hV.prod x hx).1.toFinset := by simp [Hx, hx]
      rw [h1, Set.Finite.mem_toFinset] at hv
      exact hv.1
    · have h1 : Hx x = ∅ := by simp [Hx, hx]
      rw [h1] at hv
      simp at hv
  have hHtV : ∀ v ∈ Ht, v ∈ V := fun v hv => by
    rw [hHt, Set.Finite.mem_toFinset] at hv
    exact hv.1
  let T : Finset (AbsoluteValue K ℝ) := insert v₀ (Ht ∪ s.biUnion Hx)
  have hTV : ∀ v ∈ T, v ∈ V := by
    intro v hv
    simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion] at hv
    rcases hv with rfl | hv | ⟨x, -, hv⟩
    · exact hv₀
    · exact hHtV v hv
    · exact hHxV x v hv
  have hv₀T : v₀ ∈ T := Finset.mem_insert_self _ _
  have hHtT : Ht ⊆ T := fun v hv => by
    simp only [T, Finset.mem_insert, Finset.mem_union]; exact Or.inr (Or.inl hv)
  have hout : ∀ v ∈ V, v ∉ T → v t ≤ 1 ∧ ∀ x ∈ s, v x ≤ 1 := by
    intro v hv hvT
    constructor
    · by_contra hlt
      have : v t ≠ 1 := fun h => hlt h.le
      exact hvT (hHtT (by rw [hHt, Set.Finite.mem_toFinset]; exact ⟨hv, this⟩))
    · intro x hx
      by_contra hlt
      have : v x ≠ 1 := fun h => hlt h.le
      exact hvT (by
        simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
        exact Or.inr (Or.inr ⟨x, hx, hHx x (hs0 x hx) v hv this⟩))
  have hτt : ∀ v ∈ T, v ∉ Ht → τ v = 1 := by
    intro v hvT hvH
    have hvV := hTV v hvT
    have : v t = 1 := by
      by_contra hne
      exact hvH (by rw [hHt, Set.Finite.mem_toFinset]; exact ⟨hvV, hne⟩)
    simp [τ, this]
  let M : AbsoluteValue K ℝ → ℝ := fun v => 1 + ∑ x ∈ s, v x
  have hM1 : ∀ v, 1 ≤ M v := fun v =>
    by have := Finset.sum_nonneg (fun x (_ : x ∈ s) => v.nonneg x); simp only [M]; linarith
  have hMx : ∀ v, ∀ x ∈ s, v x ≤ M v := fun v x hx => by
    have := Finset.single_le_sum (f := fun x => v x) (fun x _ => v.nonneg x) hx
    simp only [M]; linarith
  set P : ℝ := ∏ v ∈ T, M v with hP
  have hP1 : 1 ≤ P := one_le_prod_real _ _ (fun v _ => hM1 v)
  have hPpos : 0 < P := by linarith
  have claim : ∀ N : ℕ, 1 ≤ N →
      (((p : ℝ) ^ N) ^ s.card) ≤ C * ((P * H ^ (N - 1)) * (P * H ^ (N - 1))) ^ κ := by
    intro N hN
    let f : AbsoluteValue K ℝ → ℝ := fun v => M v * τ v ^ (N - 1)
    have hf1 : ∀ v, 1 ≤ f v := fun v => by
      have h1 : 1 ≤ τ v ^ (N - 1) := one_le_pow₀ (hτ1 v)
      simp only [f]; nlinarith [hM1 v]
    set D : ℝ := ∏ v ∈ T, f v with hD
    have hDeq : D = P * H ^ (N - 1) := by
      simp only [hD, f, Finset.prod_mul_distrib, Finset.prod_pow]
      congr 2
      rw [hH]
      exact (Finset.prod_subset hHtT (fun v hvT hvH => hτt v hvT hvH)).symm
    have hD1 : 1 ≤ D := one_le_prod_real _ _ (fun v _ => hf1 v)
    have hDpos : 0 < D := by linarith
    have hbT : ∀ c, ∀ v ∈ T, v (comb p t s N c) ≤ f v := fun c v _ =>
      abv_comb_le p v t s N c (hτ1 v) (by linarith [hM1 v]) (le_max_right _ _) (hMx v)
    have hbout : ∀ c, ∀ v ∈ V, v ∉ T → v (comb p t s N c) ≤ 1 := fun c v hv hvT => by
      have := abv_comb_le p v t s N c (τ := 1) (m := 1) le_rfl zero_le_one (hout v hv hvT).1
        (hout v hv hvT).2
      simpa using this
    have hQ : D = f v₀ * ∏ v ∈ T.erase v₀, f v := (Finset.mul_prod_erase T f hv₀T).symm
    have hQ1 : 1 ≤ ∏ v ∈ T.erase v₀, f v := one_le_prod_real _ _ (fun v _ => hf1 v)
    have hfD : f v₀ ≤ D := by rw [hQ]; nlinarith [hf1 v₀]
    have hQD : ∏ v ∈ T.erase v₀, f v ≤ D := by rw [hQ]; nlinarith [hf1 v₀]
    have hinj : Function.Injective (comb p t s N) := by
      intro c c' hcc
      have h0 : comb p t s N (c - c') = 0 := by rw [comb_sub, hcc, sub_self]
      exact sub_eq_zero.1 (comb_eq_zero p s hli N _ h0)
    have hsep : ∀ c c', c ≠ c' → 1 / D ≤ v₀ (comb p t s N c - comb p t s N c') := by
      intro c c' hne
      rw [← comb_sub]
      have hz : comb p t s N (c - c') ≠ 0 := fun h0 =>
        hne (sub_eq_zero.1 (comb_eq_zero p s hli N _ h0))
      have h1 := one_le_prod hV hz T (fun v hv => hTV v hv)
        (fun v hv hvT => (by simpa using hbout (c - c') v hv hvT))
      rw [← Finset.mul_prod_erase T _ hv₀T] at h1
      have h2 : ∏ v ∈ T.erase v₀, v (comb p t s N (c - c')) ≤ ∏ v ∈ T.erase v₀, f v :=
        Finset.prod_le_prod₀ (fun v _ => v.nonneg _) (fun v hv => hbT _ v (Finset.mem_of_mem_erase hv))
      have h3 : v₀ (comb p t s N (c - c')) * ∏ v ∈ T.erase v₀, v (comb p t s N (c - c')) ≤
          v₀ (comb p t s N (c - c')) * D :=
        (mul_le_mul_of_nonneg_left h2 (v₀.nonneg _)).trans
          (mul_le_mul_of_nonneg_left hQD (v₀.nonneg _))
      rw [div_le_iff₀ hDpos]
      linarith
    have hpk' := hpk D (1 / D) (by positivity) (by rw [div_le_iff₀ hDpos]; nlinarith)
      (Finset.univ.image (comb p t s N))
      (by
        intro x hx
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
        exact (hbT c v₀ hv₀T).trans hfD)
      (by
        intro x hx y hy hxy
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hy
        exact hsep c c' (fun h => hxy (by rw [h])))
    have hcard : (Finset.univ.image (comb p t s N)).card = (p ^ N) ^ s.card := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    rw [hcard] at hpk'
    have hDD : D / (1 / D) = D * D := by field_simp
    rw [hDD] at hpk'
    rw [hDeq] at hpk'
    exact_mod_cast hpk'
  have hlog := aux_log (s.card : ℝ) (Real.log p) (Real.log H) κ (Real.log C + 2 * κ * Real.log P)
    hκ (Real.log_nonneg hH1) (by
      intro N hN
      obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      have h1 := claim (k + 1) hN
      simp only [Nat.add_sub_cancel] at h1
      have hX : 0 < P * H ^ k := by positivity
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos (mul_pos hX hX) _).ne',
        Real.log_rpow (mul_pos hX hX), Real.log_mul hX.ne' hX.ne',
        Real.log_mul hPpos.ne' (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow] at h2
      push_cast at h2 ⊢
      linarith)
  have hle : (s.card : ℝ) ≤ 2 * κ * Real.log H / Real.log p := by
    rw [le_div_iff₀ hL]; exact hlog
  exact_mod_cast hle.trans (Nat.le_ceil _)

/-- **Aside 8.9, characteristic `p`** (Artin): a field of characteristic `p` with a set `V` of absolute values
satisfying the Artin–Whaples axioms and a packing bound at one `v₀ ∈ V` is a finite extension of `𝔽_p(t)`. -/
@[kb "milne2020ant" "v3.08, Aside 8.9, p. 138"]
theorem exists_ratFunc_finiteDimensional {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {V : Set (AbsoluteValue K ℝ)} (hV : AWAxioms V) {v₀ : AbsoluteValue K ℝ} (hv₀ : v₀ ∈ V)
    (hpack : PackingBound v₀) :
    ∃ (_ : Algebra (RatFunc (ZMod p)) K), FiniteDimensional (RatFunc (ZMod p)) K := by
  let _ : Algebra (ZMod p) K := (ZMod.castHom (dvd_refl p) K).toAlgebra
  have hex : ∃ t : K, Transcendental (ZMod p) t := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy0, hy1⟩ := hV.nontrivial v₀ hv₀
    exact hy1 (abv_eq_one_of_isAlgebraic p v₀ (not_not.1 (hcon y)) hy0)
  obtain ⟨t, ht⟩ := hex
  have hinj : Function.Injective (Polynomial.aeval (R := ZMod p) t) :=
    transcendental_iff_injective.1 ht
  let φ : (ZMod p)[X] →+* K := (Polynomial.aeval (R := ZMod p) t).toRingHom
  let f : RatFunc (ZMod p) →+* K :=
    RatFunc.liftRingHom φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  let alg : Algebra (RatFunc (ZMod p)) K := f.toAlgebra
  refine ⟨alg, ?_⟩
  let _ := alg
  obtain ⟨B, hB⟩ := exists_card_bound p hV hv₀ hpack
  exact finiteDimensional_of_bound B hB

end Main

end NumberFieldKB.MilneANT.Aside89
