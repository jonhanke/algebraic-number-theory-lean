import NumberFieldKB.MilneANT.Ch7Hensel

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: the integral closure of a complete discrete valuation ring is local

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

The first step of Milne's proof of Theorem 7.38 shows that if $A$ is a complete discrete valuation ring, then the
integral closure $B$ of $A$ in a finite extension $L$ of its field of fractions has only one prime ideal over
$\mathfrak p$ (by Hensel's lemma 7.33, the reduction of an irreducible polynomial is a power of an irreducible one).
Equivalently, $B$ is a local ring; this is what makes the absolute value extend uniquely. We record it for the
integral closure of $A$ in an arbitrary field $L$ (so also for infinite algebraic extensions, as used in
Proposition 7.50), and use it in the files on unramified extensions and ramification groups.
-/

open IsLocalRing

namespace NumberFieldKB.MilneANT

section Helpers

open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A] {L : Type*} [Field L] [Algebra A L]

omit [IsAdicComplete (maximalIdeal A) A] in
/-- A maximal ideal of the integral closure lies over the maximal ideal of $A$. -/
private lemma comap_eq_maximalIdeal_aux (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    P.comap (algebraMap A (integralClosure A L)) = maximalIdeal A := by
  have : (P.comap (algebraMap A (integralClosure A L))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (fun x => Algebra.IsIntegral.isIntegral x) P
  exact IsLocalRing.eq_maximalIdeal this

omit [IsAdicComplete (maximalIdeal A) A] in
/-- The minimal polynomial of an element of the integral closure has no monic factorization into
two nonconstant monic factors. -/
private lemma minpoly_factor_aux (β : integralClosure A L) (g h : A[X]) (hg : g.Monic) (hh : h.Monic)
    (hf : minpoly A β = g * h) : g = 1 ∨ h = 1 := by
  have h0 : aeval β g * aeval β h = 0 := by
    rw [← map_mul, ← hf]; exact minpoly.aeval A β
  have hdeg : (g * h).natDegree = g.natDegree + h.natDegree := hg.natDegree_mul' hh.ne_zero
  have hint : IsIntegral A β := Algebra.IsIntegral.isIntegral β
  rcases mul_eq_zero.mp h0 with h1 | h1
  · have h2 := Polynomial.natDegree_le_natDegree (minpoly.min A β hg h1)
    rw [hf, hdeg] at h2
    exact Or.inr (hh.natDegree_eq_zero.mp (by omega))
  · have h2 := Polynomial.natDegree_le_natDegree (minpoly.min A β hh h1)
    rw [hf, hdeg] at h2
    exact Or.inl (hg.natDegree_eq_zero.mp (by omega))

/-- If $\beta$ lies in one maximal ideal of the integral closure, it lies in every one (Hensel). -/
private lemma mem_of_mem_aux (P₁ P₂ : Ideal (integralClosure A L)) [P₁.IsMaximal] [P₂.IsMaximal]
    {β : integralClosure A L} (hβ : β ∈ P₁) : β ∈ P₂ := by
  classical
  have hint : IsIntegral A β := Algebra.IsIntegral.isIntegral β
  set f : A[X] := minpoly A β with hfdef
  have hfm : f.Monic := minpoly.monic hint
  have hf0 : aeval β f = 0 := minpoly.aeval A β
  have hc1 := comap_eq_maximalIdeal_aux (A := A) (L := L) P₁
  have hc2 := comap_eq_maximalIdeal_aux (A := A) (L := L) P₂
  have hcoef : f.coeff 0 ∈ maximalIdeal A := by
    rw [← hc1, Ideal.mem_comap]
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := f)
    have h3 : algebraMap A (integralClosure A L) (f.coeff 0) = -(β * aeval β q) := by
      have := congrArg (aeval β) hq
      simp only [map_sub, map_mul, aeval_X, aeval_C, hf0] at this
      linear_combination -this
    rw [h3]
    exact P₁.neg_mem (P₁.mul_mem_right _ hβ)
  obtain ⟨q, hfbar, hqnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd
    (f.map (residue A)) (hfm.map _).ne_zero 0
  generalize (f.map (residue A)).rootMultiplicity 0 = r at hfbar
  simp only [map_zero, sub_zero] at hfbar hqnd
  have hqm : q.Monic := by
    have : (X ^ r * q).Monic := by rw [← hfbar]; exact hfm.map _
    exact (Polynomial.monic_X_pow r).of_mul_monic_left this
  have hXdvd : (X : (ResidueField A)[X]) ∣ f.map (residue A) := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_map, (residue_eq_zero_iff _).mpr hcoef]
  have hr : r ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hfbar
    exact hqnd (hfbar ▸ hXdvd)
  have hcop : IsCoprime ((X : (ResidueField A)[X]) ^ r) q :=
    ((Polynomial.irreducible_X.coprime_iff_not_dvd).mpr hqnd).pow_left
  obtain ⟨g, h, hg, hh, hfgh, hgbar, hhbar, -, -⟩ :=
    thm_7_33 A f hfm (X ^ r) q (Polynomial.monic_X_pow r) hqm hfbar hcop
  have hfq : f.map (residue A) = X ^ r := by
    rcases minpoly_factor_aux β g h hg hh hfgh with rfl | rfl
    · rw [Polynomial.map_one] at hgbar
      have := congrArg Polynomial.natDegree hgbar
      simp at this
      omega
    · rw [Polynomial.map_one] at hhbar
      rw [hfbar, ← hhbar, mul_one]
  have hdc : ∀ i, (f - X ^ r).coeff i ∈ maximalIdeal A := by
    intro i
    rw [← residue_eq_zero_iff, ← Polynomial.coeff_map, Polynomial.map_sub, hfq]
    simp
  have hd : aeval β (f - X ^ r) ∈ P₂ := by
    rw [Polynomial.aeval_eq_sum_range]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    apply P₂.mul_mem_right
    rw [← Ideal.mem_comap, hc2]
    exact hdc i
  have hpow : β ^ r ∈ P₂ := by
    have : β ^ r = -(aeval β (f - X ^ r)) := by
      simp only [map_sub, map_pow, aeval_X, hf0]; ring
    rw [this]
    exact P₂.neg_mem hd
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance r hpow

end Helpers

/-- **Theorem 7.38, first step of the proof**: the integral closure of a complete discrete valuation ring $A$ in a
field $L$ is a local ring (only one prime ideal lies over the maximal ideal of $A$). -/
@[kb "milne2020ant" "v3.08, Thm. 7.38 (proof), p. 123"]
theorem isLocalRing_integralClosure (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] (L : Type*) [Field L] [Algebra A L] :
    IsLocalRing (integralClosure A L) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (integralClosure A L)
  refine IsLocalRing.of_unique_max_ideal ⟨P, hP, fun Q hQ => ?_⟩
  exact hQ.eq_of_le hP.ne_top (fun β hβ => mem_of_mem_aux Q P hβ)

instance instIsLocalRingIntegralClosure (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] (L : Type*) [Field L] [Algebra A L] :
    IsLocalRing (integralClosure A L) :=
  isLocalRing_integralClosure A L

/-- The inclusion of a complete discrete valuation ring $A$ in its integral closure in a field is a local
homomorphism (the maximal ideal of $A$ maps into the maximal ideal); so the residue field of the integral closure is an
extension of the residue field of $A$. -/
theorem isLocalHom_algebraMap_integralClosure (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] (L : Type*) [Field L] [Algebra A L] :
    IsLocalHom (algebraMap A (integralClosure A L)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal]; exact hna
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (integralClosure A L)
  have h1 : algebraMap A (integralClosure A L) a ∈ P := by
    rw [← Ideal.mem_comap, comap_eq_maximalIdeal_aux]; exact hm
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P h1 ha)

instance instIsLocalHomAlgebraMapIntegralClosure (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A] (L : Type*) [Field L] [Algebra A L] :
    IsLocalHom (algebraMap A (integralClosure A L)) :=
  isLocalHom_algebraMap_integralClosure A L

end NumberFieldKB.MilneANT
