import NumberFieldKB.MilneEC.Ch1BezoutLocal
import NumberFieldKB.MilneEC.Ch1BezoutCRT
import NumberFieldKB.MilneEC.Ch1BezoutDim
import NumberFieldKB.MilneEC.Ch1BezoutFinite
import NumberFieldKB.MilneEC.Ch1BezoutAux

/-!
# Milne, Elliptic Curves, Theorem I.1.18: Bezout's theorem

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, Theorem 1.18 (p. 21). Milne refers to Fulton 1969,
Chapter 5; the proof here follows Fulton's, with the dimension count done in the affine plane.

Let $C_F$, $C_G$ be projective plane curves of degrees `m`, `n` with no common component, over an
algebraically closed field `K`.

1. $C_F \cap C_G$ is finite (`finite_projectivePoints_inter`).
2. Since `K` is infinite there is a line $X + tY + t^2Z = 0$ missing $C_F \cap C_G$
   (`exists_line_avoiding`). Change coordinates (`linSubst`) so that this line is $Z = 0$.
3. In the new coordinates the leading forms $F(X, Y, 0)$ and $G(X, Y, 0)$ of $f = F(X, Y, 1)$ and
   $g = G(X, Y, 1)$ have no common zero, hence are relatively prime, and the dimension count gives
   $\dim_K K[X, Y]/(f, g) = mn$ (`finrank_quotient_of_isRelPrime_top`).
4. $\dim_K K[X, Y]/(f, g) = \sum_p \dim_K \mathcal O_p/(f, g)$ over the common zeros of `f` and `g`
   (`finrank_quotient_eq_sum_numAt`), and each summand is the intersection number of $C_F$ and $C_G$
   at the corresponding point (`intersectionNumberAt_eq_numAt`, `intersectionNumberAt_linSubst`).

For curves over an arbitrary field `k` (`thm1_18`), extend the coefficients to $k^{\mathrm{al}}$.
-/

open MvPolynomial Matrix
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

/-- The affine point `p` of the chart $Z = 1$, as a vector. -/
def affVec (p : K × K) : Fin 3 → K := ![p.1, p.2, 1]

theorem affVec_ne_zero (p : K × K) : affVec p ≠ 0 := fun h => by
  simpa [affVec] using congrFun h 2

theorem pieceCoords_affVec (p : K × K) : pieceCoords 2 (affVec p) = p := by
  simp [pieceCoords, affVec]

theorem evalAt_dehomogenize_affVec (F : MvPolynomial (Fin 3) K) (p : K × K) :
    evalAt (dehomogenize 2 F) p = aeval (affVec p) F := by
  have h := evalAt_dehomogenize F 2 (affVec p) (by simp [affVec])
  rw [pieceCoords_affVec] at h
  rw [h]
  simp [affVec]

/-- A form vanishing at no point of the line at infinity in the sense of `atInfinity` is not a unit
there unless its degree is 0. -/
theorem not_isUnit_of_isHomogeneous {P : MvPolynomial (Fin 2) K} {n : ℕ} (hP : P.IsHomogeneous n)
    (hn : n ≠ 0) (hP0 : P ≠ 0) : ¬ IsUnit P := by
  intro hu
  obtain ⟨c, hc, rfl⟩ : ∃ c : K, c ≠ 0 ∧ P = C c := by
    obtain ⟨c, hc⟩ := (isUnit_iff_eq_C_of_isReduced).mp hu
    exact ⟨c, fun h => hP0 (by rw [hc.2, h, C_0]), hc.2⟩
  exact hn ((isHomogeneous_C (Fin 2) c).inj_right hP (by simpa using hc)).symm

theorem mulVec_affVec_ne_zero {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnit A.det) (p : K × K) :
    A *ᵥ affVec p ≠ 0 := by
  intro h0
  have : A⁻¹ *ᵥ (A *ᵥ affVec p) = 0 := by rw [h0]; simp
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec] at this
  exact affVec_ne_zero p this

/-- A **good frame** for two forms `F`, `G` (Fulton 1969, §5.3): an invertible substitution `A` after
which the curves do not meet on the line at infinity $Z = 0$. Then the leading forms of the
dehomogenizations `f`, `g` are nonzero and relatively prime, and every common zero of `F` and `G` comes
from a common zero of `f` and `g`. -/
structure Frame (F G : MvPolynomial (Fin 3) K) (m n : ℕ) where
  /-- The change of coordinates. -/
  A : Matrix (Fin 3) (Fin 3) K
  hA : IsUnit A.det
  hf : (dehomogenize 2 (linSubst A F)).totalDegree ≤ m
  hg : (dehomogenize 2 (linSubst A G)).totalDegree ≤ n
  hfm : homogeneousComponent m (dehomogenize 2 (linSubst A F)) ≠ 0
  hgn : homogeneousComponent n (dehomogenize 2 (linSubst A G)) ≠ 0
  hcop : IsRelPrime (homogeneousComponent m (dehomogenize 2 (linSubst A F)))
    (homogeneousComponent n (dehomogenize 2 (linSubst A G)))
  surj : ∀ P ∈ projectivePoints F K ∩ projectivePoints G K,
    ∃ p ∈ commonZeros (dehomogenize 2 (linSubst A F)) (dehomogenize 2 (linSubst A G)),
      Projectivization.mk K (A *ᵥ affVec p) (mulVec_affVec_ne_zero hA p) = P

namespace Frame

variable {F G : MvPolynomial (Fin 3) K} {m n : ℕ} (fr : Frame F G m n)

/-- The point of the projective plane given by an affine point of the frame. -/
def pt (p : K × K) : ℙ K (Fin 3 → K) :=
  Projectivization.mk K (fr.A *ᵥ affVec p) (mulVec_affVec_ne_zero fr.hA p)

theorem pt_injective : Function.Injective fr.pt := by
  intro p q hpq
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ (mulVec_affVec_ne_zero fr.hA p)
    (mulVec_affVec_ne_zero fr.hA q)).mp hpq
  have e : affVec p = (c : K) • affVec q := by
    have := congrArg (fun v => fr.A⁻¹ *ᵥ v) hc
    simp only [Matrix.mulVec_smul, Units.smul_def, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul fr.A fr.hA, Matrix.one_mulVec] at this
    exact this.symm
  have hc1 : (c : K) = 1 := by simpa [affVec] using (congrFun e 2).symm
  have e0 : p.1 = q.1 := by simpa [affVec, hc1] using congrFun e 0
  have e1 : p.2 = q.2 := by simpa [affVec, hc1] using congrFun e 1
  exact Prod.ext e0 e1

theorem mem_commonZeros_iff (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (p : K × K) :
    p ∈ commonZeros (dehomogenize 2 (linSubst fr.A F)) (dehomogenize 2 (linSubst fr.A G)) ↔
      fr.pt p ∈ projectivePoints F K ∩ projectivePoints G K := by
  simp only [commonZeros, Set.mem_ofPred_eq, Set.mem_inter_iff, pt,
    mem_projectivePoints_mk hF _ (mulVec_affVec_ne_zero fr.hA p),
    mem_projectivePoints_mk hG _ (mulVec_affVec_ne_zero fr.hA p),
    evalAt_dehomogenize_affVec, aeval_linSubst]

theorem numAt_eq (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (p : K × K) :
    numAt (dehomogenize 2 (linSubst fr.A F)) (dehomogenize 2 (linSubst fr.A G)) p =
      projIntersectionNumber F G (fr.pt p) := by
  rw [← intersectionNumberAt_eq_numAt]
  have := intersectionNumberAt_linSubst hF hG fr.hA (affVec p) (by simp [affVec])
    (mulVec_affVec_ne_zero fr.hA p)
  rw [pieceCoords_affVec] at this
  exact this

end Frame

/-- Over an infinite field, an invertible matrix `B` such that $(B v)_2 \neq 0$ for the representatives
`v` of finitely many given points (a line $Z = 0$ in new coordinates missing them). -/
theorem exists_matrix_avoiding [Infinite K] (T : Finset (ℙ K (Fin 3 → K))) :
    ∃ B : Matrix (Fin 3) (Fin 3) K, IsUnit B.det ∧ ∀ P ∈ T, (B *ᵥ P.rep) 2 ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := exists_line_avoiding (T.image fun P => P.rep)
    (by
      intro v hv
      obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hv
      exact P.rep_nonzero)
  refine ⟨lineMatrix t, by rw [det_lineMatrix]; exact isUnit_one, fun P hP => ?_⟩
  rw [lineMatrix_mulVec_two]
  exact ht P.rep (Finset.mem_image.mpr ⟨P, hP, rfl⟩)

/-- A good frame from a matrix `B` whose new line at infinity misses the intersection: the frame's
substitution is $B^{-1}$. -/
theorem exists_frame_of_matrix [IsAlgClosed K] {F G : MvPolynomial (Fin 3) K} {m n : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hm : m ≠ 0) (hn : n ≠ 0)
    (B : Matrix (Fin 3) (Fin 3) K) (hB : IsUnit B.det)
    (hlin : ∀ P ∈ projectivePoints F K ∩ projectivePoints G K, (B *ᵥ P.rep) 2 ≠ 0) :
    ∃ fr : Frame F G m n, fr.A = B⁻¹ := by
  classical
  set A := B⁻¹
  have hA : IsUnit A.det := by
    exact Matrix.isUnit_nonsing_inv_det B hB
  have hAB : A * B = 1 := Matrix.nonsing_inv_mul B hB
  have hBA : B * A = 1 := Matrix.mul_nonsing_inv B hB
  set F' := linSubst A F
  set G' := linSubst A G
  have hF' : F'.IsHomogeneous m := isHomogeneous_linSubst hF A
  have hG' : G'.IsHomogeneous n := isHomogeneous_linSubst hG A
  set f := dehomogenize 2 F'
  set g := dehomogenize 2 G'
  -- a common zero of `F'` and `G'` on the line at infinity would give a point of the intersection on
  -- the line
  have hinf : ∀ a b : K, (a, b) ≠ (0, 0) → aeval ![a, b] (atInfinity F') = 0 →
      aeval ![a, b] (atInfinity G') ≠ 0 := by
    intro a b hab hFa hGa
    rw [aeval_atInfinity] at hFa hGa
    have hv : A *ᵥ ![a, b, 0] ≠ 0 := by
      intro h0
      have : B *ᵥ (A *ᵥ ![a, b, 0]) = 0 := by rw [h0]; simp
      rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] at this
      apply hab
      have h0' := congrFun this 0
      have h1' := congrFun this 1
      simp at h0' h1'
      simp [h0', h1']
    set P := Projectivization.mk K (A *ᵥ ![a, b, 0]) hv
    have hP : P ∈ projectivePoints F K ∩ projectivePoints G K := by
      refine ⟨(mem_projectivePoints_mk hF _ hv).mpr ?_, (mem_projectivePoints_mk hG _ hv).mpr ?_⟩
      · rw [← aeval_linSubst]; exact hFa
      · rw [← aeval_linSubst]; exact hGa
    apply hlin P hP
    obtain ⟨c, hc, hcv⟩ := exists_smul_rep (A *ᵥ ![a, b, 0]) hv
    have : B *ᵥ (A *ᵥ ![a, b, 0]) = c • (B *ᵥ P.rep) := by
      rw [hcv, Matrix.mulVec_smul]
    rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] at this
    have h2 := congrFun this 2
    simp at h2
    rcases h2 with h2 | h2
    · exact absurd h2 hc
    · exact h2
  -- Step 3: the leading forms are relatively prime and nonzero
  have hfm : homogeneousComponent m f = atInfinity F' := homogeneousComponent_dehomogenize hF'
  have hgn : homogeneousComponent n g = atInfinity G' := homogeneousComponent_dehomogenize hG'
  have hFi : (atInfinity F').IsHomogeneous m := hfm ▸ homogeneousComponent_isHomogeneous m f
  have hGi : (atInfinity G').IsHomogeneous n := hgn ▸ homogeneousComponent_isHomogeneous n g
  have hF0 : atInfinity F' ≠ 0 := by
    intro h0
    by_cases hG0 : atInfinity G' = 0
    · exact hinf 1 0 (by simp) (by rw [h0]; simp) (by rw [hG0]; simp)
    · obtain ⟨a, b, hab, hz⟩ := exists_zero_ne_origin (not_isUnit_of_isHomogeneous hGi hn hG0) hG0
      exact hinf a b hab (by rw [h0]; simp) hz
  have hG0 : atInfinity G' ≠ 0 := by
    intro h0
    obtain ⟨a, b, hab, hz⟩ := exists_zero_ne_origin (not_isUnit_of_isHomogeneous hFi hm hF0) hF0
    exact hinf a b hab hz (by rw [h0]; simp)
  have hcop : IsRelPrime (homogeneousComponent m f) (homogeneousComponent n g) := by
    rw [hfm, hgn]; exact isRelPrime_of_forall_ne_zero hF0 hinf
  refine ⟨⟨A, hA, totalDegree_dehomogenize_le hF', totalDegree_dehomogenize_le hG', hfm ▸ hF0,
    hgn ▸ hG0, hcop, ?_⟩, rfl⟩
  intro P hP
  set u := B *ᵥ P.rep
  have hu : u 2 ≠ 0 := hlin P hP
  have e : Projectivization.mk K (A *ᵥ affVec (pieceCoords 2 u))
      (mulVec_affVec_ne_zero hA _) = P := by
    have hv : affVec (pieceCoords 2 u) = (u 2)⁻¹ • u := by
      funext i
      fin_cases i <;> simp [affVec, pieceCoords, div_eq_inv_mul, hu]
    have hw : A *ᵥ affVec (pieceCoords 2 u) = (u 2)⁻¹ • P.rep := by
      rw [hv, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
    conv_rhs => rw [← Projectivization.mk_rep P]
    exact (Projectivization.mk_eq_mk_iff K _ _ _ P.rep_nonzero).mpr
      ⟨Units.mk0 (u 2)⁻¹ (inv_ne_zero hu), by rw [hw, Units.smul_def, Units.val_mk0]⟩
  refine ⟨pieceCoords 2 u, ?_, e⟩
  have key : ∀ p : K × K, p ∈ commonZeros f g ↔ Projectivization.mk K (A *ᵥ affVec p)
      (mulVec_affVec_ne_zero hA p) ∈ projectivePoints F K ∩ projectivePoints G K := by
    intro p
    simp only [commonZeros, Set.mem_ofPred_eq, Set.mem_inter_iff,
      mem_projectivePoints_mk hF _ (mulVec_affVec_ne_zero hA p),
      mem_projectivePoints_mk hG _ (mulVec_affVec_ne_zero hA p),
      evalAt_dehomogenize_affVec, f, g, F', G', aeval_linSubst]
  exact (key _).mpr (e ▸ hP)

/-- A good frame exists over an algebraically closed field (Fulton 1969, §5.3). -/
theorem exists_frame [IsAlgClosed K] {F G : MvPolynomial (Fin 3) K} {m n : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hm : m ≠ 0) (hn : n ≠ 0)
    (hFG : NoCommonComponent F G) : Nonempty (Frame F G m n) := by
  obtain ⟨B, hB, hlin⟩ := exists_matrix_avoiding (finite_projectivePoints_inter hF hG hFG).toFinset
  obtain ⟨fr, -⟩ := exists_frame_of_matrix hF hG hm hn B hB
    (fun P hP => hlin P ((Set.Finite.mem_toFinset _).mpr hP))
  exact ⟨fr⟩

/-- **Bezout's theorem** over an algebraically closed field (Fulton 1969, §5.3). -/
theorem bezout_of_isAlgClosed [IsAlgClosed K] {F G : MvPolynomial (Fin 3) K} {m n : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hm : m ≠ 0) (hn : n ≠ 0)
    (hFG : NoCommonComponent F G) :
    ∃ S : Finset (ℙ K (Fin 3 → K)),
      (S : Set _) = projectivePoints F K ∩ projectivePoints G K ∧
      ∑ P ∈ S, projIntersectionNumber F G P = m * n := by
  classical
  obtain ⟨fr⟩ := exists_frame hF hG hm hn hFG
  obtain ⟨hQfin, hQdim⟩ := finrank_quotient_of_isRelPrime_top fr.hf fr.hg fr.hfm fr.hgn fr.hcop
  obtain ⟨S1, hS1, hsum⟩ := finrank_quotient_eq_sum_numAt _ _ hQfin
  refine ⟨S1.image fr.pt, ?_, ?_⟩
  · ext P
    simp only [Finset.coe_image, Set.mem_image, hS1]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact (fr.mem_commonZeros_iff hF hG p).mp hp
    · intro hP
      obtain ⟨p, hp, e⟩ := fr.surj P hP
      exact ⟨p, hp, e⟩
  · rw [Finset.sum_image (fun p _ q _ h => fr.pt_injective h), ← hQdim, hsum]
    exact Finset.sum_congr rfl fun p _ => (fr.numAt_eq hF hG p).symm

end NumberFieldKB.MilneEC.Bezout

namespace NumberFieldKB.MilneEC

/-- **Theorem 1.18 (Bezout)** (p. 21), proved: projective plane curves over `k` of degrees `m`, `n` with no
common component meet over $k^{\mathrm{al}}$ in finitely many points, and $\sum_P I(P, C \cap D) = mn$.
The proof follows Fulton 1969, Chapter 5 (`Bezout.bezout_of_isAlgClosed`). -/
@[kb "milne2006ec" "Ch. I, Thm. 1.18, pdf p. 21"]
theorem thm1_18 : Thm1_18 where
  bezout k _ F G hF hG hFG := by
    obtain ⟨S, hS, hsum⟩ := Bezout.bezout_of_isAlgClosed (K := AlgebraicClosure k)
      (Bezout.isHomogeneous_baseChange hF.1) (Bezout.isHomogeneous_baseChange hG.1) hF.2.1 hG.2.1
      (Bezout.NoCommonComponent.baseChange hF.1 hG.1 hFG _)
    refine ⟨S, ?_, ?_⟩
    · rw [hS, Bezout.projectivePoints_baseChange, Bezout.projectivePoints_baseChange]
    · rw [← hsum]
      exact Finset.sum_congr rfl fun P _ => (Bezout.projIntersectionNumber_baseChange F G P).symm

/-- **Remark 1.21** (p. 22), first part, unconditional: a projective plane curve with two components has
a singular point over $k^{\mathrm{al}}$. -/
@[kb "milne2006ec" "Ch. I, Rem. 1.21, pdf p. 22"]
theorem remark_1_21_singular' {k : Type} [Field k] {F G H : MvPolynomial (Fin 3) k}
    (hF : IsProjectivePlaneCurve F) (hGH : F = G * H) (hG : G.totalDegree ≠ 0)
    (hH : H.totalDegree ≠ 0) :
    ∃ P ∈ projectivePoints F (AlgebraicClosure k), ¬ IsNonsingularProjPoint F P :=
  remark_1_21_singular thm1_18 hF hGH hG hH

/-- **Remark 1.21** (p. 22), unconditional: every nonsingular projective plane curve is geometrically
irreducible. -/
@[kb "milne2006ec" "Ch. I, Rem. 1.21, pdf p. 22"]
theorem remark_1_21' {k : Type} [Field k] {F : MvPolynomial (Fin 3) k}
    (hF : IsProjectivePlaneCurve F) (hns : IsNonsingularProjCurve F) :
    Irreducible (baseChange (AlgebraicClosure k) F) :=
  remark_1_21 thm1_18 hF hns

end NumberFieldKB.MilneEC
