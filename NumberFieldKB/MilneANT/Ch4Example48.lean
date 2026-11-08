import Mathlib
import NumberFieldKB.MilneANT.Ch2Examples

/-!
# Milne, *Algebraic Number Theory*, Example 4.8: auxiliary results

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), p. 72; bib key `milne2020ant`.

For a root $\alpha$ of $X^5 - X + 1$ generating $K$: $\beta = -\alpha$ is a root of $X^5 - X - 1$, so
$\mathcal O_K = \mathbb Z[\alpha]$ and $\Delta_K = 2869$ by Example 2.39; the Minkowski bound is $< 4$, and there are
no ideals of norm $2$ or $3$ because $X^5 - X - 1$ has no roots modulo $2$ or $3$. The tagged statement is
`NumberFieldKB.MilneANT.example_4_8` in `Ch4.lean`.
-/

open NumberField Polynomial Module
open scoped nonZeroDivisors
namespace NumberFieldKB.MilneANT.Q8

variable {K : Type*} [Field K] [NumberField K]

lemma no_norm_p (p : ℕ) (hp : p.Prime) (β : 𝓞 K) (hβ : β ^ 5 - β - 1 = 0)
    (hnd : ∀ a : ℤ, ¬ (p : ℤ) ∣ a ^ 5 - a - 1) (I : Ideal (𝓞 K)) (hI : Ideal.absNorm I = p) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : I ≠ ⊤ := by
    intro h; rw [h, Ideal.absNorm_top] at hI; exact hp.one_lt.ne' hI.symm
  haveI : Nontrivial (𝓞 K ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  have hc : Nat.card (𝓞 K ⧸ I) = p := by
    rw [← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hpI : (p : 𝓞 K) ∈ I := by
    have := Ideal.absNorm_mem I
    rwa [hI] at this
  have hz : ((p : ℤ) : 𝓞 K ⧸ I) = 0 := by
    have : Ideal.Quotient.mk I (p : 𝓞 K) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hpI
    simpa using this
  have hfin : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)
  haveI : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ I) = p := by rw [← Nat.card_eq_fintype_card]; exact hc
  haveI : CharP (𝓞 K ⧸ I) p := charP_of_card_eq_prime hcard
  let φ : ZMod p →+* 𝓞 K ⧸ I := ZMod.castHom (dvd_refl p) (𝓞 K ⧸ I)
  have hinj : Function.Injective φ := RingHom.injective φ
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [hc, Nat.card_zmod])
  obtain ⟨z, hzβ⟩ := hbij.2 (Ideal.Quotient.mk I β)
  have hza : z = ((z.cast : ℤ) : ZMod p) := (ZMod.intCast_zmod_cast z).symm
  set a : ℤ := z.cast with ha
  have hβa : Ideal.Quotient.mk I β = (a : 𝓞 K ⧸ I) := by
    rw [← hzβ, hza]
    simp [φ]
  have h0 : ((a ^ 5 - a - 1 : ℤ) : 𝓞 K ⧸ I) = 0 := by
    have := congrArg (Ideal.Quotient.mk I) hβ
    rw [map_sub, map_sub, map_pow, map_one, hβa, map_zero] at this
    push_cast
    exact this
  have h1 : φ ((a ^ 5 - a - 1 : ℤ) : ZMod p) = 0 := by
    rw [map_intCast]; exact h0
  have h2 : ((a ^ 5 - a - 1 : ℤ) : ZMod p) = 0 := hinj (by rw [h1, map_zero])
  exact hnd a ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h2)

private lemma cast_discr' {n : ℕ} (v : Fin n → 𝓞 K) :
    ((Algebra.discr ℤ v : ℤ) : ℚ) = Algebra.discr ℚ (fun i : Fin n => (v i : K)) := by
  rw [Algebra.discr_def, Algebra.discr_def, ← eq_intCast (Int.castRingHom ℚ), RingHom.map_det]
  congr 1
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.coe_trace_int]

lemma finrank_five (β : 𝓞 K) (hβ : β ^ 5 - β - 1 = 0) (hgen : IntermediateField.adjoin ℚ {(β : K)} = ⊤) :
    Module.finrank ℚ K = 5 := by
  have irr : Irreducible (X ^ 5 - X - 1 : ℚ[X]) := X_pow_sub_X_sub_one_irreducible_rat (by norm_num)
  have hroot : aeval (β : K) (X ^ 5 - X - 1 : ℚ[X]) = 0 := by
    have := congrArg (fun x : 𝓞 K => (x : K)) hβ
    simpa using this
  have hmin : minpoly ℚ (β : K) = X ^ 5 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic irr hroot (by monicity!)).symm
  have h1 := IntermediateField.adjoin.finrank (K := ℚ) (x := (β : K)) (Algebra.IsIntegral.isIntegral _)
  rw [hgen, IntermediateField.finrank_top'] at h1
  rw [h1, hmin]; compute_degree!

lemma discr_2869 (β : 𝓞 K) (hβ : β ^ 5 - β - 1 = 0) (hgen : IntermediateField.adjoin ℚ {(β : K)} = ⊤) :
    discr K = 2869 := by
  obtain ⟨hd, hadj⟩ := (example_2_39.2 K β hβ hgen)
  have hint : IsIntegral ℤ β := Algebra.IsIntegral.isIntegral β
  let pb := PowerBasis.ofAdjoinEqTop' hint hadj
  have h5 := finrank_five β hβ hgen
  have hdim : pb.dim = 5 := by
    rw [← pb.finrank, RingOfIntegers.rank, h5]
  have e1 : discr K = Algebra.discr ℤ pb.basis := (discr_eq_discr K pb.basis).symm
  have e2 : Algebra.discr ℤ pb.basis = Algebra.discr ℤ (pb.basis ∘ (finCongr hdim).symm) :=
    (Algebra.discr_reindex ℤ pb.basis (finCongr hdim)).symm
  have e3 : (pb.basis ∘ (finCongr hdim).symm : Fin 5 → 𝓞 K) = fun i : Fin 5 => β ^ (i : ℕ) := by
    funext i
    have hg : pb.gen = β := PowerBasis.ofAdjoinEqTop'_gen hint hadj
    simp only [Function.comp_apply]
    rw [pb.coe_basis, hg]
    simp
  rw [e1, e2, e3]
  have := cast_discr' (K := K) (fun i : Fin 5 => β ^ (i : ℕ))
  push_cast at this
  rw [hd] at this
  exact_mod_cast this

lemma minkowski_lt (hdisc : discr K = 2869) (h5 : Module.finrank ℚ K = 5) :
    (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      ((Nat.factorial (finrank ℚ K) : ℝ) / (finrank ℚ K) ^ (finrank ℚ K) * √|(discr K : ℝ)|) < 4 := by
  have hs : NumberField.InfinitePlace.nrComplexPlaces K ≤ 2 := by
    have := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  have hpi := Real.pi_gt_d2
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  have hr : (1:ℝ) ≤ 4 / Real.pi := by rw [le_div_iff₀ Real.pi_pos]; linarith
  have hr2 : (4 / Real.pi) ≤ 4 / 3.14 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hp : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K ≤ (4 / Real.pi) ^ 2 :=
    pow_le_pow_right₀ hr hs
  have hp2 : (4 / Real.pi) ^ 2 ≤ (4 / 3.14) ^ 2 := by gcongr
  rw [h5, hdisc]
  have hsq : √|((2869 : ℤ) : ℝ)| < 53.6 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num [abs_of_pos]
  have hsq0 : 0 ≤ √|((2869 : ℤ) : ℝ)| := Real.sqrt_nonneg _
  have hpos : 0 ≤ (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K := by positivity
  have : ((Nat.factorial 5 : ℕ) : ℝ) / (5:ℕ) ^ 5 = 120 / 3125 := by
    norm_num [Nat.factorial]
  rw [this]
  refine lt_of_le_of_lt (b := (4 / 3.14) ^ 2 * (120 / 3125 * 53.6)) ?_ (by norm_num)
  apply mul_le_mul (hp.trans hp2) _ (by positivity) (by positivity)
  have : (120:ℝ) / 3125 * √|((2869 : ℤ) : ℝ)| ≤ 120 / 3125 * 53.6 := by gcongr
  simpa using this

lemma nd2 : ∀ a : ℤ, ¬ ((2 : ℕ) : ℤ) ∣ a ^ 5 - a - 1 := by
  intro a h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  push_cast at h
  generalize (a : ZMod 2) = x at h
  revert x; decide

lemma nd3 : ∀ a : ℤ, ¬ ((3 : ℕ) : ℤ) ∣ a ^ 5 - a - 1 := by
  intro a h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  push_cast at h
  generalize (a : ZMod 3) = x at h
  revert x; decide

theorem example_4_8' (K : Type*) [Field K] [NumberField K] (α : 𝓞 K) (hα : α ^ 5 - α + 1 = 0)
    (hgen : IntermediateField.adjoin ℚ {(α : K)} = ⊤) :
    Algebra.adjoin ℤ {α} = ⊤ ∧ IsPrincipalIdealRing (𝓞 K) := by
  have hβ : (-α) ^ 5 - (-α) - 1 = 0 := by linear_combination (-1 : 𝓞 K) * hα
  have hgenβ : IntermediateField.adjoin ℚ {((-α : 𝓞 K) : K)} = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have : ((α : 𝓞 K) : K) = -((-α : 𝓞 K) : K) := by simp
    rw [this]
    exact neg_mem (IntermediateField.subset_adjoin ℚ _ rfl)
  refine ⟨?_, ?_⟩
  · have := (example_2_39.2 K (-α) hβ hgenβ).2
    rw [eq_top_iff, ← this, Algebra.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact neg_mem (Algebra.subset_adjoin rfl)
  · have h5 := finrank_five (-α) hβ hgenβ
    have hd := discr_2869 (-α) hβ hgenβ
    have hM := minkowski_lt hd h5
    refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI => ?_)
    have hlt : ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℕ) : ℝ) < 4 := lt_of_le_of_lt hI hM
    have hlt' : Ideal.absNorm (I : Ideal (𝓞 K)) < 4 := by exact_mod_cast hlt
    have hpos := Ideal.absNorm_pos_of_nonZeroDivisors I
    generalize hn : Ideal.absNorm (I : Ideal (𝓞 K)) = n at hlt' hpos
    interval_cases n
    · rw [Ideal.absNorm_eq_one_iff.mp hn]; exact ⟨1, by simp⟩
    · exact (no_norm_p 2 Nat.prime_two (-α) hβ nd2 _ hn).elim
    · exact (no_norm_p 3 Nat.prime_three (-α) hβ nd3 _ hn).elim
end NumberFieldKB.MilneANT.Q8
