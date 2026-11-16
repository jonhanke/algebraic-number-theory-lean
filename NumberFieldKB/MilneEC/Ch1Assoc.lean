import NumberFieldKB.MilneEC.Ch1CubicProj
import NumberFieldKB.MilneEC.Ch1CubicLine
import NumberFieldKB.MilneEC.Ch1CubicThird
import NumberFieldKB.MilneEC.Ch1CubicBase

/-!
# Milne, Elliptic Curves, Theorem I.3.1: associativity of the chord and tangent law

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, Theorem 3.1 (p. 35). Milne sketches associativity by
Proposition 3.2 and refers to Fulton 1969, p. 124, for the degenerate cases; this is Fulton's argument.

Over $k^{\mathrm{al}}$, let $S = PQ$, $T = OS$ ($= P + Q$), $U = TR$, $S' = QR$, $T' = OS'$ ($= Q + R$),
$U' = PT'$. With $L_1, L_2, L_3$ the lines through $P, Q, S$; $T, R, U$; $S', O, T'$ and
$M_1, M_2, M_3$ the lines through $S, O, T$; $Q, R, S'$; $P, T', U'$, the cubics $G = L_1L_2L_3$ and
$H = M_1M_2M_3$ cut the curve in the divisors $E + U$ and $E + U'$ with $E = P + Q + S + T + R + S' + O + T'$
(`projIntersectionNumber_line_eq_count`, `projIntersectionNumber_mul`). By the nine-point lemma with
multiplicities (`projIntersectionNumber_le_of_le_succ`), $U = U'$, hence $(P + Q) + R = OU = OU' = P + (Q + R)$.
The construction commutes with extending the field (`IsThirdPoint.map`), which gives the result over `k`.
No hypothesis on `k` is needed (Milne's statement assumes `k` perfect).
-/

open MvPolynomial Matrix
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

theorem noCommonComponent_mul {F G₁ G₂ : MvPolynomial (Fin 3) K} (h₁ : NoCommonComponent F G₁)
    (h₂ : NoCommonComponent F G₂) : NoCommonComponent F (G₁ * G₂) := by
  intro h hh hF hG
  rcases hh.prime.dvd_or_dvd hG with h' | h'
  · exact h₁ h hh hF h'
  · exact h₂ h hh hF h'

theorem dehomogenize_linSubst_mul (A : Matrix (Fin 3) (Fin 3) K) (G₁ G₂ : MvPolynomial (Fin 3) K) :
    dehomogenize 2 (linSubst A (G₁ * G₂)) =
      dehomogenize 2 (linSubst A G₁) * dehomogenize 2 (linSubst A G₂) := by
  simp [dehomogenize, linSubst, map_mul]

/-- Intersection numbers with a smooth curve are additive in the second curve. -/
theorem projIntersectionNumber_mul [IsAlgClosed K] {F G₁ G₂ : MvPolynomial (Fin 3) K} {m n₁ n₂ : ℕ}
    (hF : F.IsHomogeneous m) (hG₁ : G₁.IsHomogeneous n₁) (hG₂ : G₂.IsHomogeneous n₂)
    (hm : m ≠ 0) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (h₁ : NoCommonComponent F G₁) (h₂ : NoCommonComponent F G₂) (hsm : IsSmoothForm F)
    (X : ℙ K (Fin 3 → K)) :
    projIntersectionNumber F (G₁ * G₂) X =
      projIntersectionNumber F G₁ X + projIntersectionNumber F G₂ X := by
  classical
  have h₁₂ := noCommonComponent_mul h₁ h₂
  set T := (finite_projectivePoints_inter hF hG₁ h₁).toFinset ∪
    (finite_projectivePoints_inter hF hG₂ h₂).toFinset ∪ {X}
  obtain ⟨B, hB, hlin⟩ := exists_matrix_avoiding T
  obtain ⟨fr1, e1⟩ := exists_frame_of_matrix hF hG₁ hm hn₁ B hB
    (fun P hP => hlin P (by simp [T, hP]))
  obtain ⟨fr2, e2⟩ := exists_frame_of_matrix hF hG₂ hm hn₂ B hB
    (fun P hP => hlin P (by simp [T, hP]))
  obtain ⟨fr12, e12⟩ := exists_frame_of_matrix hF (hG₁.mul hG₂) hm (by omega) B hB
    (by
      intro P hP
      apply hlin P
      have h0 : aeval P.rep G₁ * aeval P.rep G₂ = 0 := by
        have := hP.2; simp only [projectivePoints, Set.mem_setOf_eq, map_mul] at this; exact this
      rcases mul_eq_zero.mp h0 with h | h
      · simp [T, show P ∈ projectivePoints F K ∩ projectivePoints G₁ K from ⟨hP.1, h⟩]
      · simp [T, show P ∈ projectivePoints F K ∩ projectivePoints G₂ K from ⟨hP.1, h⟩])
  set A := B⁻¹
  have hA : IsUnit A.det := Matrix.isUnit_nonsing_inv_det B hB
  set u := pieceCoords 2 (B *ᵥ X.rep)
  have hu : Projectivization.mk K (A *ᵥ affVec u) (mulVec_affVec_ne_zero hA u) = X :=
    mk_inv_mulVec_affVec_pieceCoords hB X (hlin X (by simp [T]))
  have n1 := fr1.numAt_eq hF hG₁ u
  have n2 := fr2.numAt_eq hF hG₂ u
  have n12 := fr12.numAt_eq hF (hG₁.mul hG₂) u
  simp only [Frame.pt, e1, e2, e12, hu] at n1 n2 n12
  rw [← n1, ← n2, ← n12, dehomogenize_linSubst_mul]
  set f := dehomogenize 2 (linSubst A F)
  set g₁ := dehomogenize 2 (linSubst A G₁)
  set g₂ := dehomogenize 2 (linSubst A G₂)
  by_cases hfu : evalAt f u = 0
  · have hns : NonsingAt f u := ⟨hfu, nonsingAt_dehomogenize_linSubst hF hm hsm hA hfu⟩
    have q1 := (finrank_quotient_of_isRelPrime_top fr1.hf fr1.hg fr1.hfm fr1.hgn fr1.hcop).1
    have q2 := (finrank_quotient_of_isRelPrime_top fr2.hf fr2.hg fr2.hfm fr2.hgn fr2.hcop).1
    rw [e1] at q1
    rw [e2] at q2
    exact (numAt_mul hns (finite_localQuotient' q1 u) (finite_localQuotient' q2 u)).2
  · have hnot : ∀ g : MvPolynomial (Fin 2) K, u ∉ commonZeros f g := fun g h => hfu h.1
    rw [numAt_eq_zero_of_not_mem (hnot _), numAt_eq_zero_of_not_mem (hnot _),
      numAt_eq_zero_of_not_mem (hnot _)]

/-- The intersection numbers of a smooth cubic with the line of a chord and tangent construction:
$I_X(F, ℓ)$ is the number of times `X` occurs among `P`, `Q`, `R`. -/
theorem projIntersectionNumber_line_eq_count [IsAlgClosed K] {F : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous 3) (hsm : IsSmoothForm F) {P Q R : ℙ K (Fin 3 → K)}
    (h : IsThirdPoint F P Q R) :
    ∃ ℓ : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 ∧ ℓ ≠ 0 ∧
      ∀ X, projIntersectionNumber F ℓ X = count3 P Q R X := by
  classical
  obtain ⟨ℓ, hℓ, hℓ0, hpts, htan⟩ := isThirdPoint_line hF hsm h
  refine ⟨ℓ, hℓ, hℓ0, ?_⟩
  set S : Finset (ℙ K (Fin 3 → K)) := {P, Q, R}
  have hS : (S : Set _) = projectivePoints F K ∩ projectivePoints ℓ K := by
    ext X; simp [S, hpts]
  have hsum := sum_projIntersectionNumber_line hF hsm hℓ hℓ0 S hS
  have hone : ∀ X, (X = P ∨ X = Q ∨ X = R) → count3 P Q R X = 1 →
      projIntersectionNumber F ℓ X = 1 := by
    intro X hX hc
    refine projIntersectionNumber_line_eq_one hF hsm hℓ hℓ0 ((hpts X).mpr hX) ?_
    rw [htan X hX]; omega
  have htwo : ∀ X, (X = P ∨ X = Q ∨ X = R) → 2 ≤ count3 P Q R X →
      2 ≤ projIntersectionNumber F ℓ X := by
    intro X hX hc
    exact projIntersectionNumber_line_ge_two hF hsm hℓ hℓ0 ((hpts X).mpr hX) ((htan X hX).mpr hc)
  intro X
  by_cases hX : X = P ∨ X = Q ∨ X = R
  swap
  · rw [projIntersectionNumber_line_eq_zero hF hℓ (fun h' => hX ((hpts X).mp h'))]
    push_neg at hX
    simp [count3, hX.1, hX.2.1, hX.2.2]
  -- case analysis on the coincidences among `P`, `Q`, `R`
  by_cases hPQ : P = Q <;> by_cases hQR : Q = R <;> by_cases hPR : P = R
  · -- all equal
    subst hPQ; subst hQR
    have hX' : X = P := by rcases hX with h | h | h <;> exact h
    subst hX'
    simpa [S, count3] using hsum
  · exact absurd (hPQ.trans hQR) hPR
  · exact absurd (hPQ.symm.trans hPR) hQR
  · -- P = Q ≠ R
    subst hPQ
    have hcR : count3 P P R R = 1 := by simp [count3, Ne.symm hPR]
    have hcP : count3 P P R P = 2 := by simp [count3, hPR]
    have h1 := hone R (Or.inr (Or.inr rfl)) hcR
    have hS2 : S = {P, R} := by ext Y; simp only [S, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hS2, Finset.sum_pair hPR, h1] at hsum
    rcases hX with rfl | rfl | rfl
    · rw [hcP]; omega
    · rw [hcP]; omega
    · rw [hcR, h1]
  · exact absurd (hPR.trans hQR.symm) hPQ
  · -- Q = R ≠ P
    subst hQR
    have hcP : count3 P Q Q P = 1 := by simp [count3, hPQ]
    have hcQ : count3 P Q Q Q = 2 := by simp [count3, Ne.symm hPQ]
    have h1 := hone P (Or.inl rfl) hcP
    have hS2 : S = {P, Q} := by ext Y; simp only [S, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hS2, Finset.sum_pair hPQ, h1] at hsum
    have h2 := htwo Q (Or.inr (Or.inl rfl)) (by omega)
    rcases hX with rfl | rfl | rfl
    · rw [hcP, h1]
    · rw [hcQ]; omega
    · rw [hcQ]; omega
  · -- P = R ≠ Q
    subst hPR
    have hcQ : count3 P Q P Q = 1 := by simp [count3, Ne.symm hPQ]
    have hcP : count3 P Q P P = 2 := by simp [count3, hPQ]
    have h1 := hone Q (Or.inr (Or.inl rfl)) hcQ
    have hS2 : S = {P, Q} := by ext Y; simp only [S, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hS2, Finset.sum_pair hPQ, h1] at hsum
    rcases hX with rfl | rfl | rfl
    · rw [hcP]; omega
    · rw [hcQ, h1]
    · rw [hcP]; omega
  · -- all distinct
    have hc : count3 P Q R X = 1 := by
      rcases hX with rfl | rfl | rfl <;> simp [count3, hPQ, hQR, hPR, Ne.symm hPQ, Ne.symm hQR,
        Ne.symm hPR]
    rw [hc, hone X hX hc]

/-- Fulton's argument: the two ways of adding three points give the same point before the last step. -/
theorem assoc_core [IsAlgClosed K] {F : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3)
    (hsm : IsSmoothForm F) {O P Q R S T U S' T' U' : ℙ K (Fin 3 → K)}
    (h₁ : IsThirdPoint F P Q S) (h₂ : IsThirdPoint F S O T) (h₃ : IsThirdPoint F T R U)
    (h₄ : IsThirdPoint F Q R S') (h₅ : IsThirdPoint F S' O T') (h₆ : IsThirdPoint F P T' U') :
    U = U' := by
  classical
  obtain ⟨ℓ₁, hℓ₁, hℓ₁0, e₁⟩ := projIntersectionNumber_line_eq_count hF hsm h₁
  obtain ⟨ℓ₂, hℓ₂, hℓ₂0, e₂⟩ := projIntersectionNumber_line_eq_count hF hsm h₂
  obtain ⟨ℓ₃, hℓ₃, hℓ₃0, e₃⟩ := projIntersectionNumber_line_eq_count hF hsm h₃
  obtain ⟨ℓ₄, hℓ₄, hℓ₄0, e₄⟩ := projIntersectionNumber_line_eq_count hF hsm h₄
  obtain ⟨ℓ₅, hℓ₅, hℓ₅0, e₅⟩ := projIntersectionNumber_line_eq_count hF hsm h₅
  obtain ⟨ℓ₆, hℓ₆, hℓ₆0, e₆⟩ := projIntersectionNumber_line_eq_count hF hsm h₆
  have nc : ∀ ℓ : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 → ℓ ≠ 0 → NoCommonComponent F ℓ :=
    fun ℓ h h0 => noCommonComponent_line hF hsm h h0
  -- the two cubics
  set G := ℓ₁ * ℓ₃ * ℓ₅
  set H := ℓ₂ * ℓ₄ * ℓ₆
  have hG : G.IsHomogeneous 3 := (hℓ₁.mul hℓ₃).mul hℓ₅
  have hH : H.IsHomogeneous 3 := (hℓ₂.mul hℓ₄).mul hℓ₆
  have ncG : NoCommonComponent F G :=
    noCommonComponent_mul (noCommonComponent_mul (nc _ hℓ₁ hℓ₁0) (nc _ hℓ₃ hℓ₃0)) (nc _ hℓ₅ hℓ₅0)
  have ncH : NoCommonComponent F H :=
    noCommonComponent_mul (noCommonComponent_mul (nc _ hℓ₂ hℓ₂0) (nc _ hℓ₄ hℓ₄0)) (nc _ hℓ₆ hℓ₆0)
  have hGX : ∀ X, projIntersectionNumber F G X =
      count3 P Q S X + count3 T R U X + count3 S' O T' X := by
    intro X
    rw [projIntersectionNumber_mul hF (hℓ₁.mul hℓ₃) hℓ₅ (by norm_num) (by norm_num) (by norm_num)
      (noCommonComponent_mul (nc _ hℓ₁ hℓ₁0) (nc _ hℓ₃ hℓ₃0)) (nc _ hℓ₅ hℓ₅0) hsm,
      projIntersectionNumber_mul hF hℓ₁ hℓ₃ (by norm_num) (by norm_num) (by norm_num)
      (nc _ hℓ₁ hℓ₁0) (nc _ hℓ₃ hℓ₃0) hsm, e₁, e₃, e₅]
  have hHX : ∀ X, projIntersectionNumber F H X =
      count3 S O T X + count3 Q R S' X + count3 P T' U' X := by
    intro X
    rw [projIntersectionNumber_mul hF (hℓ₂.mul hℓ₄) hℓ₆ (by norm_num) (by norm_num) (by norm_num)
      (noCommonComponent_mul (nc _ hℓ₂ hℓ₂0) (nc _ hℓ₄ hℓ₄0)) (nc _ hℓ₆ hℓ₆0) hsm,
      projIntersectionNumber_mul hF hℓ₂ hℓ₄ (by norm_num) (by norm_num) (by norm_num)
      (nc _ hℓ₂ hℓ₂0) (nc _ hℓ₄ hℓ₄0) hsm, e₂, e₄, e₆]
  -- the common part `E` of the two divisors
  set E : ℙ K (Fin 3 → K) → ℕ := fun X =>
    count3 P Q S X + ((if X = T then 1 else 0) + (if X = R then 1 else 0)) + count3 S' O T' X
  have hG' : ∀ X, projIntersectionNumber F G X = E X + (if X = U then 1 else 0) := by
    intro X; rw [hGX]; simp only [E, count3]; ring
  have hH' : ∀ X, projIntersectionNumber F H X = E X + (if X = U' then 1 else 0) := by
    intro X; rw [hHX]; simp only [E, count3]; ring
  by_contra hUU
  have key := projIntersectionNumber_le_of_le_succ hF hH hG ncH ncG hsm U'
    (by
      intro X hX
      rw [hG', hH', if_neg hX]
      omega)
    (by
      rw [hG', hH']
      split_ifs <;> omega)
  rw [hG', hH', if_pos rfl, if_neg (Ne.symm hUU)] at key
  omega

end NumberFieldKB.MilneEC.Bezout

namespace NumberFieldKB.MilneEC

open Bezout in
/-- **Theorem 3.1**, associativity (p. 35), proved: for a nonsingular projective plane cubic and
$O \in C(k)$, the chord and tangent law is associative (Fulton's argument, `Bezout.assoc_core`). -/
@[kb "milne2006ec" "Ch. I, Thm. 3.1 (associativity), pdf p. 35"]
theorem thm3_1 : Thm3_1 where
  assoc k _ _ F hF O P Q R := by
    have hFh := hF.isHomogeneous
    set K := AlgebraicClosure k
    unfold chordAdd
    congr 1
    set S := thirdPoint hF P Q
    set T := thirdPoint hF O S
    set U := thirdPoint hF T R
    set S' := thirdPoint hF Q R
    set T' := thirdPoint hF O S'
    set U' := thirdPoint hF P T'
    apply Subtype.ext
    apply mapPoint_injective K
    exact assoc_core (isHomogeneous_baseChange hFh) (isSmoothForm_baseChange hF)
      (Bezout.IsThirdPoint.map hFh K ((isThirdPoint_thirdPoint hF P Q)))
      (Bezout.IsThirdPoint.map hFh K ((isThirdPoint_thirdPoint hF O S).comm))
      (Bezout.IsThirdPoint.map hFh K ((isThirdPoint_thirdPoint hF T R)))
      (Bezout.IsThirdPoint.map hFh K ((isThirdPoint_thirdPoint hF Q R)))
      (Bezout.IsThirdPoint.map hFh K ((isThirdPoint_thirdPoint hF O S').comm))
      (Bezout.IsThirdPoint.map hFh K ((isThirdPoint_thirdPoint hF P T')))

/-- **Theorem 3.1** (p. 35), unconditional: the chord and tangent construction makes $C(k)$ into a
commutative group with zero `O`. -/
@[kb "milne2006ec" "Ch. I, Thm. 3.1, pdf p. 35", reducible]
noncomputable def theorem_3_1' {k : Type} [Field k] [PerfectField k] {F : MvPolynomial (Fin 3) k}
    (hF : IsNonsingularCubic F) (O : CurvePoints F) : AddCommGroup (CurvePoints F) :=
  theorem_3_1 thm3_1 hF O

/-- **Remark 4.11** (p. 43), unconditional: choosing a different zero $O'$ translates the group law,
$P +' Q = P + Q - O'$ in the group with zero `O`. -/
@[kb "milne2006ec" "Ch. I, Rem. 4.11, pdf p. 43"]
theorem remark_4_11' {k : Type} [Field k] [PerfectField k] {F : MvPolynomial (Fin 3) k}
    (hF : IsNonsingularCubic F) (O O' P Q : CurvePoints F) :
    letI := theorem_3_1' hF O
    chordAdd hF O' P Q = P + Q - O' :=
  remark_4_11 thm3_1 hF O O' P Q

/-- After Theorem 2.1 (p. 28): $C(\mathbb Q)$, if nonempty, is a finitely generated group, given only the
named statement `Thm2_1` (associativity is now proved). -/
@[kb "milne2006ec" "Ch. I, §2, after Thm. 2.1: C(Q) is finitely generated, pdf p. 28"]
theorem fg_of_thm2_1' (h₁ : Thm2_1) {F : MvPolynomial (Fin 3) ℚ} (hF : IsNonsingularCubic F)
    (O : CurvePoints F) :
    letI := theorem_3_1' hF O
    AddGroup.FG (CurvePoints F) :=
  fg_of_thm2_1 h₁ thm3_1 hF O

end NumberFieldKB.MilneEC
