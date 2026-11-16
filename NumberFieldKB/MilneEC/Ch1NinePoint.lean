import NumberFieldKB.MilneEC.Ch1Bezout
import NumberFieldKB.MilneEC.Ch1NinePointLocal
import NumberFieldKB.MilneEC.Ch1NinePointLine
import NumberFieldKB.MilneEC.Ch1GroupLaw

/-!
# Milne, Elliptic Curves, Proposition I.3.2: the nine-point lemma

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, Proposition 3.2 (p. 35): over an algebraically
closed field, if two cubic curves meet in exactly nine points, every cubic through eight of them passes
through the ninth. Milne proves it in general position and refers to Walker 1950 for the general case.
The proof here is not Milne's:

1. The two cubics have no common component, since a common component has infinitely many points.
2. In a good frame (`Bezout.exists_frame`) the nine points are affine, and by Bezout's theorem (the
   dimension count `finrank_quotient_of_isRelPrime_top` and `finrank_quotient_eq_sum_numAt`) the nine
   local intersection numbers are positive and add up to 9, so each is 1: the intersections are
   transversal.
3. Hence a polynomial vanishing at the nine points lies in $(f, g)$, one of the two curves is nonsingular
   at the ninth point, and the line argument (`eval_eq_zero_of_line`) concludes.
-/

open MvPolynomial Matrix
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

theorem commonZeros_comm (f g : MvPolynomial (Fin 2) K) : commonZeros f g = commonZeros g f := by
  ext p; simp [commonZeros, and_comm]

/-- Two forms of positive degree over an algebraically closed field with finitely many common zeros have
no common component. -/
theorem noCommonComponent_of_finite [IsAlgClosed K] {F G : MvPolynomial (Fin 3) K} {m : ℕ}
    (hF : F.IsHomogeneous m) (hF0 : F ≠ 0)
    (hfin : (projectivePoints F K ∩ projectivePoints G K).Finite) : NoCommonComponent F G := by
  intro h hh hhF hhG
  obtain ⟨e, he⟩ := isHomogeneous_of_dvd hF hF0 hhF
  have he0 : e ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc⟩ : ∃ c, h = C c := ⟨h.coeff 0, by
      rw [← totalDegree_eq_zero_iff_eq_C]
      exact Nat.le_zero.mp he.totalDegree_le⟩
    have hc0 : c ≠ 0 := by rintro rfl; exact hh.ne_zero (by simp [hc])
    exact hh.not_isUnit (hc ▸ (isUnit_iff_ne_zero.mpr hc0).map C)
  apply infinite_zeros_of_isHomogeneous he he0
  refine hfin.subset fun P hP => ⟨?_, ?_⟩
  · obtain ⟨q, rfl⟩ := hhF
    show aeval P.rep (h * q) = 0
    rw [map_mul, show aeval P.rep h = 0 from hP, zero_mul]
  · obtain ⟨q, rfl⟩ := hhG
    show aeval P.rep (h * q) = 0
    rw [map_mul, show aeval P.rep h = 0 from hP, zero_mul]

/-- The nine-point lemma over an algebraically closed field, for forms. -/
theorem nine_point [IsAlgClosed K] {F G H : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3)
    (hG : G.IsHomogeneous 3) (hH : H.IsHomogeneous 3) (hF0 : F ≠ 0)
    (S : Finset (ℙ K (Fin 3 → K))) (hS9 : S.card = 9)
    (hS : (S : Set _) = projectivePoints F K ∩ projectivePoints G K)
    (P : ℙ K (Fin 3 → K)) (hP : P ∈ S) (hH8 : ∀ Q ∈ S, Q ≠ P → Q ∈ projectivePoints H K) :
    P ∈ projectivePoints H K := by
  classical
  have hFG : NoCommonComponent F G :=
    noCommonComponent_of_finite hF hF0 (hS ▸ S.finite_toSet)
  obtain ⟨fr⟩ := exists_frame hF hG (by norm_num) (by norm_num) hFG
  set f := dehomogenize 2 (linSubst fr.A F)
  set g := dehomogenize 2 (linSubst fr.A G)
  set h := dehomogenize 2 (linSubst fr.A H)
  obtain ⟨hQfin, hQdim⟩ := finrank_quotient_of_isRelPrime_top fr.hf fr.hg fr.hfm fr.hgn fr.hcop
  obtain ⟨S1, hS1, hsum⟩ := finrank_quotient_eq_sum_numAt f g hQfin
  -- the affine common zeros correspond to the nine points
  have himage : S1.image fr.pt = S := by
    apply Finset.coe_injective
    rw [hS]
    ext Q
    simp only [Finset.coe_image, Set.mem_image, hS1]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact (fr.mem_commonZeros_iff hF hG p).mp hp
    · intro hQ; exact fr.surj Q hQ
  have hcard : S1.card = 9 := by
    rw [← hS9, ← himage, Finset.card_image_of_injective _ fr.pt_injective]
  -- all local intersection numbers are 1
  have hpos : ∀ p ∈ S1, 1 ≤ numAt f g p := fun p hp =>
    numAt_pos hQfin (by rw [← hS1]; exact hp)
  have hone : ∀ p ∈ S1, numAt f g p = 1 := by
    have hle : ∑ p ∈ S1, 1 ≤ ∑ p ∈ S1, numAt f g p := Finset.sum_le_sum hpos
    have heq : ∑ p ∈ S1, numAt f g p = ∑ p ∈ S1, 1 := by
      rw [← hsum, hQdim, Finset.sum_const, hcard]; rfl
    exact fun p hp => ((Finset.sum_eq_sum_iff_of_le hpos).mp heq.symm p hp).symm
  -- a polynomial vanishing at the nine points lies in `(f, g)`
  have hmem : ∀ q : MvPolynomial (Fin 2) K, (∀ p ∈ commonZeros f g, evalAt q p = 0) →
      q ∈ Ideal.span {f, g} := by
    intro q hq
    refine mem_span_of_forall_localQuotient f g q hQfin fun p hp => ?_
    exact mk_eq_zero_of_numAt_eq_one hp (hone p (by rw [← hS1] at hp; exact hp)) (hq p hp)
  -- the ninth point
  obtain ⟨p, hp, rfl⟩ := fr.surj P (hS ▸ hP)
  have hvan : ∀ q ∈ commonZeros f g, q ≠ p → evalAt h q = 0 := by
    intro q hq hqp
    have hqS : fr.pt q ∈ S := by
      rw [← himage]; exact Finset.mem_image_of_mem _ (by rw [← hS1] at hq; exact hq)
    have := hH8 _ hqS (fun e => hqp (fr.pt_injective e))
    rw [show fr.pt q = Projectivization.mk K (fr.A *ᵥ affVec q) (mulVec_affVec_ne_zero fr.hA q)
      from rfl, mem_projectivePoints_mk hH _ (mulVec_affVec_ne_zero fr.hA q)] at this
    rw [evalAt_dehomogenize_affVec, aeval_linSubst]
    exact this
  have hh : h.totalDegree ≤ 3 := totalDegree_dehomogenize_le (isHomogeneous_linSubst hH fr.A)
  have hfin : (commonZeros f g).Finite := by rw [← hS1]; exact S1.finite_toSet
  have hmem' : ∀ l : MvPolynomial (Fin 2) K, (∀ q ∈ commonZeros f g, evalAt (l * h) q = 0) →
      l * h ∈ Ideal.span {f, g} := fun l hl => hmem _ hl
  have hp1 : numAt f g p = 1 := hone p (by rw [← hS1] at hp; exact hp)
  have key : evalAt h p = 0 := by
    rcases gradient_ne_zero_of_numAt_eq_one hp hp1 with hgf | hgg
    · exact eval_eq_zero_of_line fr.hf fr.hg hh fr.hfm fr.hgn fr.hcop hfin hp hgf hvan hmem'
    · rw [commonZeros_comm] at hp hfin hvan
      have hmem'' : ∀ l : MvPolynomial (Fin 2) K, (∀ q ∈ commonZeros g f, evalAt (l * h) q = 0) →
          l * h ∈ Ideal.span {g, f} := by
        intro l hl
        rw [Set.pair_comm]
        exact hmem' l (by rw [commonZeros_comm]; exact hl)
      exact eval_eq_zero_of_line fr.hg fr.hf hh fr.hgn fr.hfm fr.hcop.symm hfin hp hgg hvan hmem''
  show Projectivization.mk K (fr.A *ᵥ affVec p) (mulVec_affVec_ne_zero fr.hA p) ∈ _
  rw [mem_projectivePoints_mk hH _ (mulVec_affVec_ne_zero fr.hA p), ← aeval_linSubst,
    ← evalAt_dehomogenize_affVec]
  exact key

end NumberFieldKB.MilneEC.Bezout

namespace NumberFieldKB.MilneEC

/-- **Proposition 3.2** (p. 35), proved: over an algebraically closed field, if two cubic curves meet in
exactly nine points, then every cubic curve passing through eight of the points also passes through the
ninth. (The proof uses Bezout's theorem and a line argument, not Milne's general-position argument.) -/
@[kb "milne2006ec" "Ch. I, Prop. 3.2, pdf p. 35"]
theorem prop3_2 : Prop3_2 where
  cayley_bacharach k _ _ F G H hF hF3 hG hG3 hH hH3 S hS9 hS P hP hH8 := by
    have hFh : F.IsHomogeneous 3 := by
      have h := hF.1
      unfold curveDegree at hF3
      rwa [hF3] at h
    have hGh : G.IsHomogeneous 3 := by
      have h := hG.1
      unfold curveDegree at hG3
      rwa [hG3] at h
    have hHh : H.IsHomogeneous 3 := by
      have h := hH.1
      unfold curveDegree at hH3
      rwa [hH3] at h
    have hF0 : F ≠ 0 := by rintro rfl; exact hF.2.1 (by simp)
    exact Bezout.nine_point hFh hGh hHh hF0 S hS9 hS P hP hH8

end NumberFieldKB.MilneEC
