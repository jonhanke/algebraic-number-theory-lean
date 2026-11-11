import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Milne, *Algebraic Number Theory*, Remark 4.11: auxiliary results for the example

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), p. 72; bib key `milne2020ant`.

$L = \mathbb Q(\sqrt{-1}, \sqrt 5)$ is unramified over $K = \mathbb Q(\sqrt{-5})$ at every finite prime: $i$ and
$(1 + \sqrt 5)/2$ are integral generators of $L/K$, so the different of $\mathcal O_L/\mathcal O_K$
contains $2i$ and $\sqrt 5$, hence $1 = (\sqrt 5)^2 + (2i)^2$; no prime divides it. The tagged statement is
`NumberFieldKB.MilneANT.remark_4_11_example` in `Ch4.lean`.
-/

open NumberField Polynomial Module

namespace NumberFieldKB.MilneANT.Rem411

lemma rem411_aux (K : Type*) [Field K] [NumberField K] (hK : finrank ℚ K = 2) (s : K) (hs : s ^ 2 = -5)
    (c : ℚ) (h1 : ¬ ∃ p : ℚ, p ^ 2 = c) (h2 : ¬ ∃ q : ℚ, -5 * q ^ 2 = c) :
    ¬ ∃ a : K, a ^ 2 = (c : K) := by
  rintro ⟨a, ha⟩
  have hsq : ∀ x : ℚ, s ≠ (x : K) := by
    intro x hx
    have : ((x ^ 2 : ℚ) : K) = ((-5 : ℚ) : K) := by
      push_cast; rw [← hx, hs]
    have := (Rat.cast_injective this)
    nlinarith [sq_nonneg x]
  have hli : LinearIndependent ℚ ![(1 : K), s] := by
    rw [LinearIndependent.pair_iff]
    intro u t h
    simp only [Rat.smul_def, mul_one] at h
    by_cases ht : t = 0
    · subst ht; simp at h; simp [h]
    · exfalso
      apply hsq (-u / t)
      have : (t : K) ≠ 0 := by exact_mod_cast ht
      push_cast; field_simp; linear_combination h
  have htop : Submodule.span ℚ (Set.range ![(1 : K), s]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hK])
  have ha' : a ∈ Submodule.span ℚ ({1, s} : Set K) := by
    have : Set.range ![(1 : K), s] = {1, s} := by
      ext x; simp [eq_comm, or_comm]
    rw [← this, htop]; trivial
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp ha'
  simp only [Rat.smul_def, mul_one] at hpq
  subst hpq
  have key : ((p ^ 2 + q ^ 2 * (-5) : ℚ) : K) + ((2 * p * q : ℚ) : K) * s = (c : K) := by
    rw [← ha]; push_cast; linear_combination (-(q:K)^2) * hs
  by_cases hpq0 : 2 * p * q = 0
  · rw [hpq0] at key
    simp only [Rat.cast_zero, zero_mul, add_zero] at key
    have key' : p ^ 2 + q ^ 2 * (-5) = c := Rat.cast_injective key
    have : p = 0 ∨ q = 0 := by
      rcases mul_eq_zero.mp hpq0 with h | h
      · left; linarith [mul_eq_zero.mp h |>.resolve_left (by norm_num)]
      · right; exact h
    rcases this with h | h
    · subst h; exact h2 ⟨q, by linarith⟩
    · subst h; exact h1 ⟨p, by linarith⟩
  · apply hsq ((c - (p ^ 2 + q ^ 2 * (-5))) / (2 * p * q))
    have h3 : ((2 * p * q : ℚ) : K) ≠ 0 := by exact_mod_cast hpq0
    push_cast at h3 key ⊢
    rw [eq_div_iff h3]
    linear_combination key

lemma rem411_gen (K L : Type*) [Field K] [Field L] [Algebra K L] (hL : finrank K L = 2) (x : L)
    (hx : x ∉ Set.range (algebraMap K L)) : Algebra.adjoin K {x} = ⊤ := by
  haveI : Module.Finite K L := Module.finite_of_finrank_eq_succ hL
  have hli : LinearIndependent K ![(1 : L), x] := by
    rw [LinearIndependent.pair_iff]
    intro u t h
    simp only [Algebra.smul_def, mul_one] at h
    by_cases ht : t = 0
    · subst ht; simp at h; simp [h]
    · exfalso
      apply hx
      refine ⟨-u / t, ?_⟩
      have : algebraMap K L t ≠ 0 := by simpa using ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -h
  have htop : Submodule.span K (Set.range ![(1 : L), x]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hL])
  have hs : Set.range ![(1 : L), x] = {1, x} := by
    ext y; simp [eq_comm, or_comm]
  rw [hs] at htop
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Submodule.span K ({1, x} : Set L) := by rw [htop]; trivial
  refine (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin K {x})).mpr ?_) hy
  intro y hy
  rcases hy with rfl | rfl
  · exact (Algebra.adjoin K {x}).one_mem
  · exact Algebra.subset_adjoin (Set.mem_singleton _)

lemma rem411_key (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : 𝓞 L) (g : (𝓞 K)[X]) (hg : aeval x g = 0)
    (hgen : Algebra.adjoin K {algebraMap (𝓞 L) L x} = ⊤) :
    aeval x (derivative g) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K L x hgen
  have hint : IsIntegral (𝓞 K) x := IsIntegral.of_finite _ _
  obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd hint hg
  rw [hh, derivative_mul]
  simp only [map_add, map_mul, minpoly.aeval, zero_mul, add_zero]
  exact Ideal.mul_mem_right _ _ hmem

lemma rem411_five : ¬ ∃ p : ℚ, p ^ 2 = 5 := by
  rintro ⟨p, hp⟩
  have h := Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)
  apply h
  refine ⟨|p|, ?_⟩
  have : ((p : ℝ)) ^ 2 = 5 := by exact_mod_cast hp
  have h5 : ((5 : ℕ) : ℝ) = (p : ℝ) ^ 2 := by rw [this]; norm_num
  rw [h5, Real.sqrt_sq_eq_abs]; push_cast; rfl

theorem remark_4_11_example' (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hK : finrank ℚ K = 2) (hL : finrank K L = 2) (s : K) (hs : s ^ 2 = -5) (i r : L) (hi : i ^ 2 = -1)
    (hr : r ^ 2 = 5) (P : Ideal (𝓞 L)) [P.IsPrime] (_hP : P ≠ ⊥) : Algebra.IsUnramifiedAt (𝓞 K) P := by
  have hiI : IsIntegral ℤ i := ⟨X ^ 2 + 1, (monic_X_pow 2).add_of_left (by simp), by simp [hi]⟩
  have hwI : IsIntegral ℤ ((1 + r) / 2) := by
    refine ⟨X ^ 2 - X - 1, ?_, ?_⟩
    · monicity!
    · simp
      have h2 : (2 : L) ≠ 0 := two_ne_zero
      field_simp
      linear_combination hr
  obtain ⟨xi, hxi⟩ : ∃ xi : 𝓞 L, algebraMap (𝓞 L) L xi = i := ⟨⟨i, hiI⟩, rfl⟩
  obtain ⟨w, hwv⟩ : ∃ w : 𝓞 L, algebraMap (𝓞 L) L w = (1 + r) / 2 := ⟨⟨_, hwI⟩, rfl⟩
  have e2' : algebraMap (𝓞 K) (𝓞 L) 2 = 2 := map_ofNat _ 2
  have hr_nr : r ∉ Set.range (algebraMap K L) := by
    rintro ⟨a, ha⟩
    refine rem411_aux K hK s hs 5 rem411_five ?_ ⟨a, ?_⟩
    · rintro ⟨q, hq⟩; nlinarith [sq_nonneg q]
    · apply (algebraMap K L).injective
      rw [map_pow, ha, hr, Rat.cast_ofNat, map_ofNat]
  have hi_nr : i ∉ Set.range (algebraMap K L) := by
    rintro ⟨a, ha⟩
    refine rem411_aux K hK s hs (-1) ?_ ?_ ⟨a, ?_⟩
    · rintro ⟨p, hp⟩; nlinarith [sq_nonneg p]
    · rintro ⟨q, hq⟩
      exact rem411_five ⟨5 * q, by linear_combination (-5) * hq⟩
    · apply (algebraMap K L).injective
      rw [map_pow, ha, hi]; simp
  have hw_nr : (1 + r) / 2 ∉ Set.range (algebraMap K L) := by
    rintro ⟨a, ha⟩
    apply hr_nr
    refine ⟨2 * a - 1, ?_⟩
    rw [map_sub, map_mul, ha, map_one]
    simp only [map_ofNat]
    ring
  have hgen_i : Algebra.adjoin K {algebraMap (𝓞 L) L xi} = ⊤ :=
    (by rw [hxi]; exact rem411_gen K L hL i hi_nr)
  have hgen_w : Algebra.adjoin K {algebraMap (𝓞 L) L w} = ⊤ :=
    (by rw [hwv]; exact rem411_gen K L hL _ hw_nr)
  have e1 : xi ^ 2 + 1 = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    simp only [map_add, map_pow, map_one, map_zero, hxi, hi]; ring
  have e2 : w ^ 2 - w - 1 = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    simp only [map_sub, map_pow, map_one, map_zero, hwv]
    linear_combination (1 / 4 : L) * hr
  have m1 : 2 * xi ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    have := rem411_key K L xi (X ^ 2 + 1) (by simpa using e1) hgen_i
    simpa [one_add_one_eq_two, e2'] using this
  have m2 : 2 * w - 1 ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    have := rem411_key K L w (X ^ 2 - X - 1) (by simpa using e2) hgen_w
    simpa [one_add_one_eq_two, e2'] using this
  have ht2 : (2 * w - 1) ^ 2 = 5 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    simp only [map_sub, map_pow, map_mul, map_one, map_ofNat, hwv]
    linear_combination hr
  have hnd : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    intro hd
    have hle := Ideal.dvd_iff_le.mp hd
    have h1 : 2 * xi ∈ P := hle m1
    have h2 : 2 * w - 1 ∈ P := hle m2
    have h3 : (1 : 𝓞 L) ∈ P := by
      have : (1 : 𝓞 L) = (2 * w - 1) * (2 * w - 1) + (2 * xi) * (2 * xi) := by
        linear_combination (-1) * ht2 + (-4) * e1
      rw [this]
      exact P.add_mem (Ideal.mul_mem_right _ _ h2) (Ideal.mul_mem_right _ _ h1)
    exact (Ideal.IsPrime.ne_top ‹P.IsPrime›) ((Ideal.eq_top_iff_one _).mpr h3)
  exact not_dvd_differentIdeal_iff.mp hnd

end NumberFieldKB.MilneANT.Rem411
