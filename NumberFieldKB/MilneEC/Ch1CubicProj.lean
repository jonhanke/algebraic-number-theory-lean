import NumberFieldKB.MilneEC.Ch1CubicCB
import NumberFieldKB.MilneEC.Ch1CubicGrad

/-!
# The nine-point lemma with multiplicities, projective form

Part of the proof of associativity of the chord and tangent law (Milne, *Elliptic Curves*, Theorem I.3.1;
Fulton 1969, §5.6). For a smooth plane cubic `F` and cubics `G`, `H` with no component in common with `F`:
if $I_P(F, G) \le I_P(F, H)$ for every point $P \neq U$ and $I_U(F, G) \le I_U(F, H) + 1$, then
$I_U(F, G) \le I_U(F, H)$. Equivalently (Fulton's Proposition 5.6.1 for cubics): if
$C \cdot G = P_1 + \dots + P_9$ and $C \cdot H = P_1 + \dots + P_8 + Q$ then $Q = P_9$.

Proof: choose one frame for both pairs (a line missing $C \cap G$, $C \cap H$ and `U`), then apply the
affine statement `numAt_le_of_le_succ`.
-/

open MvPolynomial Matrix
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

theorem mk_inv_mulVec_affVec_pieceCoords {B : Matrix (Fin 3) (Fin 3) K} (hB : IsUnit B.det)
    (P : ℙ K (Fin 3 → K)) (hu : (B *ᵥ P.rep) 2 ≠ 0) :
    Projectivization.mk K (B⁻¹ *ᵥ affVec (pieceCoords 2 (B *ᵥ P.rep)))
      (mulVec_affVec_ne_zero (Matrix.isUnit_nonsing_inv_det B hB) _) = P := by
  set u := B *ᵥ P.rep
  have hv : affVec (pieceCoords 2 u) = (u 2)⁻¹ • u := by
    funext i
    fin_cases i <;> simp [affVec, pieceCoords, div_eq_inv_mul, hu]
  have hw : B⁻¹ *ᵥ affVec (pieceCoords 2 u) = (u 2)⁻¹ • P.rep := by
    rw [hv, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hB,
      Matrix.one_mulVec]
  conv_rhs => rw [← Projectivization.mk_rep P]
  exact (Projectivization.mk_eq_mk_iff K _ _ _ P.rep_nonzero).mpr
    ⟨Units.mk0 (u 2)⁻¹ (inv_ne_zero hu), by rw [hw, Units.smul_def, Units.val_mk0]⟩

theorem projIntersectionNumber_le_of_le_succ [IsAlgClosed K] {F G H : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous 3) (hG : G.IsHomogeneous 3) (hH : H.IsHomogeneous 3)
    (hFG : NoCommonComponent F G) (hFH : NoCommonComponent F H) (hsm : IsSmoothForm F)
    (U : ℙ K (Fin 3 → K))
    (hle : ∀ P, P ≠ U → projIntersectionNumber F G P ≤ projIntersectionNumber F H P)
    (hU : projIntersectionNumber F G U ≤ projIntersectionNumber F H U + 1) :
    projIntersectionNumber F G U ≤ projIntersectionNumber F H U := by
  classical
  set T := (finite_projectivePoints_inter hF hG hFG).toFinset ∪
    (finite_projectivePoints_inter hF hH hFH).toFinset ∪ {U}
  obtain ⟨B, hB, hlin⟩ := exists_matrix_avoiding T
  obtain ⟨fr1, h1⟩ := exists_frame_of_matrix hF hG (by norm_num) (by norm_num) B hB
    (fun P hP => hlin P (by simp [T, hP]))
  obtain ⟨fr2, h2⟩ := exists_frame_of_matrix hF hH (by norm_num) (by norm_num) B hB
    (fun P hP => hlin P (by simp [T, hP]))
  set A := B⁻¹ with hAdef
  have hA : IsUnit A.det := Matrix.isUnit_nonsing_inv_det B hB
  set f := dehomogenize 2 (linSubst A F)
  set g := dehomogenize 2 (linSubst A G)
  set h := dehomogenize 2 (linSubst A H)
  have hpt : ∀ p, fr1.pt p = Projectivization.mk K (A *ᵥ affVec p) (mulVec_affVec_ne_zero hA p) := by
    intro p; simp only [Frame.pt, h1]
  have hpt2 : ∀ p, fr2.pt p = Projectivization.mk K (A *ᵥ affVec p) (mulVec_affVec_ne_zero hA p) := by
    intro p; simp only [Frame.pt, h2]
  have hG' : ∀ p, numAt f g p = projIntersectionNumber F G
      (Projectivization.mk K (A *ᵥ affVec p) (mulVec_affVec_ne_zero hA p)) := by
    intro p
    have := fr1.numAt_eq hF hG p
    rw [hpt] at this
    simpa only [h1] using this
  have hH' : ∀ p, numAt f h p = projIntersectionNumber F H
      (Projectivization.mk K (A *ᵥ affVec p) (mulVec_affVec_ne_zero hA p)) := by
    intro p
    have := fr2.numAt_eq hF hH p
    rw [hpt2] at this
    simpa only [h2] using this
  set u := pieceCoords 2 (B *ᵥ U.rep)
  have hu : Projectivization.mk K (A *ᵥ affVec u) (mulVec_affVec_ne_zero hA u) = U :=
    mk_inv_mulVec_affVec_pieceCoords hB U (hlin U (by simp [T]))
  have hinj : ∀ p, Projectivization.mk K (A *ᵥ affVec p) (mulVec_affVec_ne_zero hA p) = U → p = u := by
    intro p hp
    apply fr1.pt_injective
    rw [hpt, hpt, hp, hu]
  have hf := fr1.hf; rw [h1] at hf
  have hg := fr1.hg; rw [h1] at hg
  have hh := fr2.hg; rw [h2] at hh
  have hfm := fr1.hfm; rw [h1] at hfm
  have hgn := fr1.hgn; rw [h1] at hgn
  have hhn := fr2.hgn; rw [h2] at hhn
  have hcop := fr1.hcop; rw [h1] at hcop
  have hcop' := fr2.hcop; rw [h2] at hcop'
  have key := numAt_le_of_le_succ hf hg hh hfm hgn hhn hcop hcop'
    (fun p hp => ⟨hp.1, nonsingAt_dehomogenize_linSubst hF (by norm_num) hsm hA hp.1⟩) u
    (fun p hpu => by
      rw [hG', hH']
      exact hle _ (fun e => hpu (hinj p e)))
    (by rw [hG', hH', hu]; exact hU)
  rw [hG', hH', hu] at key
  exact key

end NumberFieldKB.MilneEC.Bezout
