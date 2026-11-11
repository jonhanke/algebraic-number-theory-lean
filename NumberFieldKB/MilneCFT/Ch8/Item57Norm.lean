import NumberFieldKB.MilneCFT.Ch8.ReciprocityLaw
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Group.Defs

/-!
# Milne, *Class Field Theory*, VIII, 5.7 (auxiliary): $-\gamma^n$ is a norm from $K(\gamma)$

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §5 (p. 246).
For $\zeta_n \in K$ and $\gamma \neq 0$ in an abelian extension with $\gamma^n = c \in K$: $d = [K(\gamma):K]$ divides
$n$, the minimal polynomial of $\gamma$ is $X^d - \gamma^d$, so $N(-\gamma) = -\gamma^d$, and $-c$ is a norm
(`exists_norm_eq_neg`; parity of $n/d$, with $N(\zeta^{n/2d}) = -1$ when $n/d$ is even).
-/

open NumberField IsDedekindDomain NumberFieldKB.MilneCFT Polynomial
open scoped IsMulCommutative

set_option linter.unusedSectionVars false

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

namespace Item57

variable {K : Type} [Field K] [NumberField K]

/-! ## $-\gamma^n$ is a norm from $K(\gamma)$ -/

section Norm

variable {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
include hn hζ

/-- For $\gamma \ne 0$ in an abelian extension $M$ with $\gamma^n = c \in K$: $-c$ is a norm from $K(\gamma)$. -/
theorem exists_norm_eq_neg {M : Type} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    {γ : M} (hγ : γ ≠ 0) {c : K} (hc : γ ^ n = algebraMap K M c) :
    ∃ y : (IntermediateField.adjoin K {γ})ˣ, Algebra.norm K (y : IntermediateField.adjoin K {γ}) = -c := by
  classical
  have hint : IsIntegral K γ := IsIntegral.of_finite K γ
  set d := (minpoly K γ).natDegree with hd
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact hγ (pow_eq_zero_iff hn.ne' |>.1 hc)
  -- `γ ^ d` is fixed by every automorphism, hence lies in `K`
  have hfix : ∀ σ : Gal(M/K), σ (γ ^ d) = γ ^ d := by
    intro σ
    obtain ⟨j, -, hj⟩ := kummer_zeta hn hζ c hc0 M γ hc σ
    have hpow : ∀ k : ℕ, (σ ^ k) γ = algebraMap K M ((ζ ^ j) ^ k) * γ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes, hj, map_pow, map_pow, map_pow,
          map_pow]
        ring
    have hnorm : (IntermediateField.adjoin K {γ}).fixingSubgroup.Normal := ⟨fun x hx g => by
      have : g * x * g⁻¹ = x := by rw [IsMulCommutative.is_comm.comm g x, mul_inv_cancel_right]
      rwa [this]⟩
    have hmem := (IntermediateField.adjoin K {γ}).fixingSubgroup.pow_index_mem σ
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index, IntermediateField.adjoin.finrank hint] at hmem
    have h1 : (σ ^ d) γ = γ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem γ (IntermediateField.mem_adjoin_simple_self K γ)
    rw [hpow] at h1
    have hμ : (ζ ^ j) ^ d = 1 := by
      have h2 : algebraMap K M ((ζ ^ j) ^ d) * γ = algebraMap K M 1 * γ := by rw [h1, map_one, one_mul]
      exact (algebraMap K M).injective (mul_right_cancel₀ hγ h2)
    rw [map_pow, hj, mul_pow, ← map_pow, hμ, map_one, one_mul]
  have hbot : γ ^ d ∈ (⊥ : IntermediateField K M) := (IsGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.1 hbot
  -- the minimal polynomial of `γ` is `X ^ d - b`
  have hmin : minpoly K γ = X ^ d - C b := by
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (monic_X_pow_sub_C b hd0.ne')
      (minpoly.dvd K γ ?_) ?_).symm
    · simp [hb]
    · rw [natDegree_X_pow_sub_C]
  -- `d` divides `n`
  have hdvd : d ∣ n := by
    by_contra hnd
    have hr : 0 < n % d := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      exact hγ (pow_eq_zero_iff hd0.ne' |>.1 hb.symm)
    have hγr : γ ^ (n % d) = algebraMap K M (c / b ^ (n / d)) := by
      have hsplit : γ ^ n = (γ ^ d) ^ (n / d) * γ ^ (n % d) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      rw [map_div₀, map_pow, ← hc, hsplit, hb, mul_div_cancel_left₀ _ (pow_ne_zero _ (pow_ne_zero _ hγ))]
    have hle := natDegree_le_natDegree (minpoly.min K γ (monic_X_pow_sub_C (c / b ^ (n / d)) hr.ne')
      (by simp [hγr]))
    rw [natDegree_X_pow_sub_C, ← hd] at hle
    exact absurd (Nat.mod_lt n hd0) (not_lt.2 hle)
  obtain ⟨q, rfl⟩ := hdvd
  have hfin : Module.finrank K (IntermediateField.adjoin K {γ}) = d := IntermediateField.adjoin.finrank hint
  have hNg : Algebra.norm K (IntermediateField.AdjoinSimple.gen K γ) = (-1) ^ d * -b := by
    rw [← IntermediateField.adjoin.powerBasis_gen hint, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
      IntermediateField.adjoin.powerBasis_dim, IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.minpoly_gen, hmin, natDegree_X_pow_sub_C]
    simp [(Ne.symm hd0.ne')]
  have hNneg : Algebra.norm K (-IntermediateField.AdjoinSimple.gen K γ) = -b := by
    have : -IntermediateField.AdjoinSimple.gen K γ =
        algebraMap K (IntermediateField.adjoin K {γ}) (-1) * IntermediateField.AdjoinSimple.gen K γ := by simp
    rw [this, map_mul, Algebra.norm_algebraMap, hfin, hNg, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  have hcq : c = b ^ q := by
    apply (algebraMap K M).injective
    rw [← hc, map_pow, hb, pow_mul]
  -- the element with norm `-c`
  obtain ⟨z, hz⟩ : ∃ z : IntermediateField.adjoin K {γ}, Algebra.norm K z = -c := by
    rcases Nat.even_or_odd q with ⟨m, hm⟩ | hodd
    · -- `η = ζ ^ m` satisfies `η ^ d = -1`
      have hη : (ζ ^ m) ^ d = -1 := by
        have h2 : IsPrimitiveRoot (ζ ^ (d * m)) 2 := hζ.pow hn (by rw [hm]; ring)
        rw [← pow_mul, mul_comm m d]
        exact h2.eq_neg_one_of_two_right
      refine ⟨algebraMap K (IntermediateField.adjoin K {γ}) (ζ ^ m) *
        (-IntermediateField.AdjoinSimple.gen K γ) ^ q, ?_⟩
      rw [map_mul, Algebra.norm_algebraMap, hfin, hη, map_pow, hNneg, hcq, hm, ← two_mul, pow_mul, pow_mul]
      simp
    · refine ⟨(-IntermediateField.AdjoinSimple.gen K γ) ^ q, ?_⟩
      rw [map_pow, hNneg, hcq, hodd.neg_pow]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hz
    exact hc0 (neg_eq_zero.1 hz.symm)
  exact ⟨Units.mk0 z hz0, hz⟩

end Norm

end Item57

end NumberFieldKB.MilneCFT.Ch8
