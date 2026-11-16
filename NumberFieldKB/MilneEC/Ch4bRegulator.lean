import Mathlib.Tactic.Have
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import QuadFormsKB.Citation

/-!
# Milne, Elliptic Curves, Chapter IV, Remark 10.6(b): the regulator quotient

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Remark 10.6(b), pdf pp. 173–174.

In the conjecture of Birch and Swinnerton-Dyer (Conjecture 10.5) Milne uses, for linearly independent
$P_1, \dots, P_r \in E(\mathbb Q)$ ($r$ the rank), the quotient
$\det(\langle P_i, P_j\rangle) / (E(\mathbb Q) : \sum \mathbb Z P_i)^2$, and remarks that it does not depend on the
choice of the $P_i$ and equals $\operatorname{disc}\langle\,,\rangle / [E(\mathbb Q)_{\mathrm{tors}}]^2$ when the $P_i$
form a basis modulo torsion.  This is a statement about any finitely generated abelian group $M$ with a bilinear form
$\langle\,,\rangle : M \times M \to \mathbb R$ (for $E(\mathbb Q)$: Mordell–Weil and the Néron–Tate pairing of §6), and
is proved here in that generality.

## Proved
* `remark_10_6_b_independent`: the quotient is the same for any two linearly independent families of size $r$.
* `remark_10_6_b_basis`: if the $P_i$ form a basis modulo torsion, $(M : \sum \mathbb Z P_i) = \#M_{\mathrm{tors}}$, so
  the quotient is $\det(\langle P_i, P_j\rangle)/[M_{\mathrm{tors}}]^2$.
-/

namespace NumberFieldKB.MilneEC

open Module Matrix

variable {M : Type*} [AddCommGroup M] [Module.Finite ℤ M]

/-- Milne's quotient $\det(\langle P_i, P_j\rangle) / (M : \sum \mathbb Z P_i)^2$ (pdf p. 173). -/
noncomputable def regulatorQuotient (B : M →ₗ[ℤ] M →ₗ[ℤ] ℝ) {r : ℕ} (P : Fin r → M) : ℝ :=
  (Matrix.of fun i j => B (P i) (P j)).det / ((Submodule.span ℤ (Set.range P)).toAddSubgroup.index : ℝ) ^ 2

/-- A linearly independent family of $r = \operatorname{rank} M$ elements spans a subgroup of finite index. -/
lemma index_span_ne_zero {r : ℕ} (hr : Module.finrank ℤ M = r) (P : Fin r → M)
    (hP : LinearIndependent ℤ P) :
    (Submodule.span ℤ (Set.range P)).toAddSubgroup.index ≠ 0 := by
  set S := Submodule.span ℤ (Set.range P)
  have h1 := S.finrank_quotient_add_finrank
  have h2 : Module.finrank ℤ S = r := by simpa using finrank_span_eq_card hP
  have h3 : Module.finrank ℤ (M ⧸ S) = 0 := by omega
  have htors : Module.IsTorsion ℤ (M ⧸ S) := by
    intro x
    obtain ⟨a, ha, hx⟩ := Module.finrank_eq_zero_iff.1 h3 x
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, hx⟩
  have : Finite (M ⧸ S) := Module.finite_of_fg_torsion _ htors
  have : Finite (M ⧸ S.toAddSubgroup) := this
  exact AddSubgroup.index_ne_zero_of_finite

/-- The index of the span of such a family kills the quotient: $n x \in \sum \mathbb Z P_i$ for $n$ the index. -/
lemma index_nsmul_mem_span {r : ℕ} (hr : Module.finrank ℤ M = r) (P : Fin r → M)
    (hP : LinearIndependent ℤ P) (x : M) :
    (Submodule.span ℤ (Set.range P)).toAddSubgroup.index • x ∈ Submodule.span ℤ (Set.range P) := by
  set S := Submodule.span ℤ (Set.range P)
  have h := index_span_ne_zero hr P hP
  have : Finite (M ⧸ S.toAddSubgroup) := Nat.finite_of_card_ne_zero h
  have h0 : Nat.card (M ⧸ S.toAddSubgroup) • (x : M ⧸ S.toAddSubgroup) = 0 := card_nsmul_eq_zero'
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h0
  exact h0

/-- Change of basis: if $R$ is linearly independent and lies in the span of $P$, the quotients agree
(the Gram determinant gains $\det(C)^2$ and the index gains $|\det C|$). -/
lemma regulatorQuotient_eq_of_mem_span (B : M →ₗ[ℤ] M →ₗ[ℤ] ℝ) {r : ℕ}
    (hr : Module.finrank ℤ M = r) (P R : Fin r → M) (hP : LinearIndependent ℤ P)
    (hR : LinearIndependent ℤ R) (hmem : ∀ i, R i ∈ Submodule.span ℤ (Set.range P)) :
    regulatorQuotient B R = regulatorQuotient B P := by
  classical
  let bP := Basis.span hP
  let C : Matrix (Fin r) (Fin r) ℤ := fun i j => bP.repr ⟨R i, hmem i⟩ j
  have hRC : ∀ i, R i = ∑ j, C i j • P j := by
    intro i
    have := congrArg Subtype.val (bP.sum_repr ⟨R i, hmem i⟩)
    simpa [C, bP, Basis.span_apply] using this.symm
  have hG : (Matrix.of fun i j => B (R i) (R j)) =
      C.map (Int.cast : ℤ → ℝ) * (Matrix.of fun i j => B (P i) (P j)) * (C.map (Int.cast : ℤ → ℝ))ᵀ := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [hRC i, hRC j]
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp [mul_comm]
  have hdet : (Matrix.of fun i j => B (R i) (R j)).det =
      (C.det : ℝ) ^ 2 * (Matrix.of fun i j => B (P i) (P j)).det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have : (C.map (Int.cast : ℤ → ℝ)).det = (C.det : ℝ) := by
      exact (RingHom.map_det (Int.castRingHom ℝ) C).symm
    rw [this]; ring
  have hle : (Submodule.span ℤ (Set.range R)).toAddSubgroup ≤
      (Submodule.span ℤ (Set.range P)).toAddSubgroup := by
    intro x hx
    exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hmem i) hx
  have hrel := AddSubgroup.relIndex_eq_natAbs_det _ _ hle (Basis.span hR) bP
  have hdetC : (bP.det fun i => (⟨(Basis.span hR i : M), hle (Basis.span hR i).2⟩ :
      Submodule.span ℤ (Set.range P))) = C.det := by
    rw [Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp [Basis.toMatrix_apply, C, bP, Basis.span_apply]
  have hidx : (Submodule.span ℤ (Set.range R)).toAddSubgroup.index =
      C.det.natAbs * (Submodule.span ℤ (Set.range P)).toAddSubgroup.index := by
    rw [← AddSubgroup.relIndex_mul_index hle, hrel]
    exact congrArg (fun z : ℤ => z.natAbs * _) hdetC
  have hR0 := index_span_ne_zero hr R hR
  have hP0 := index_span_ne_zero hr P hP
  have hC0 : (C.det : ℝ) ≠ 0 := by
    intro h
    have : C.det = 0 := by exact_mod_cast h
    apply hR0
    rw [hidx, this]; simp
  unfold regulatorQuotient
  rw [hdet, hidx]
  have : ((C.det.natAbs : ℕ) : ℝ) ^ 2 = (C.det : ℝ) ^ 2 := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
  rw [Nat.cast_mul, mul_pow, this]
  have : ((Submodule.span ℤ (Set.range P)).toAddSubgroup.index : ℝ) ≠ 0 := by exact_mod_cast hP0
  field_simp

omit [Module.Finite ℤ M] in
/-- The span of a linearly independent family meets the torsion subgroup trivially. -/
lemma disjoint_span_torsion {r : ℕ} (P : Fin r → M) (hP : LinearIndependent ℤ P) :
    Disjoint (Submodule.span ℤ (Set.range P)) (Submodule.torsion ℤ M) := by
  rw [Submodule.disjoint_def]
  intro x hxS hxT
  obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).1 hxT
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  let bP := Basis.span hP
  have h : bP.repr (a • (⟨x, hxS⟩ : Submodule.span ℤ (Set.range P))) = 0 := by
    have : a • (⟨x, hxS⟩ : Submodule.span ℤ (Set.range P)) = 0 := Subtype.ext hax
    rw [this]; simp
  have : (⟨x, hxS⟩ : Submodule.span ℤ (Set.range P)) = 0 := by
    apply bP.repr.injective
    ext i
    have := congrArg (fun f => f i) (congrArg DFunLike.coe h)
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.coe_zero,
      Pi.zero_apply] at this
    simpa [ha0] using this
  simpa using congrArg Subtype.val this


/-- **Remark 10.6(b)**, independence (pdf p. 173): for $r$ the rank of $M$ and two linearly independent families
$P, Q$ of $r$ elements, the quotients $\det(\langle P_i, P_j\rangle) / (M : \sum \mathbb Z P_i)^2$ agree. -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6(b), pdf p. 173"]
theorem remark_10_6_b_independent (B : M →ₗ[ℤ] M →ₗ[ℤ] ℝ) {r : ℕ} (hr : Module.finrank ℤ M = r)
    (P Q : Fin r → M) (hP : LinearIndependent ℤ P) (hQ : LinearIndependent ℤ Q) :
    regulatorQuotient B P = regulatorQuotient B Q := by
  set N := (Submodule.span ℤ (Set.range Q)).toAddSubgroup.index with hNdef
  have hN : N ≠ 0 := index_span_ne_zero hr Q hQ
  let R : Fin r → M := fun i => N • P i
  have hRind : LinearIndependent ℤ R := by
    rw [Fintype.linearIndependent_iff] at hP ⊢
    intro g hg
    have h2 : ∑ i, (g i * (N : ℤ)) • P i = 0 := by
      rw [← hg]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [R, mul_smul, natCast_zsmul]
    intro i
    have := hP _ h2 i
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (by exact_mod_cast h) hN
  have hmemP : ∀ i, R i ∈ Submodule.span ℤ (Set.range P) := fun i => by
    rw [show R i = (N : ℤ) • P i from (natCast_zsmul _ _).symm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmemQ : ∀ i, R i ∈ Submodule.span ℤ (Set.range Q) := fun i =>
    index_nsmul_mem_span hr Q hQ (P i)
  rw [← regulatorQuotient_eq_of_mem_span B hr P R hP hRind hmemP,
    regulatorQuotient_eq_of_mem_span B hr Q R hQ hRind hmemQ]

/-- **Remark 10.6(b)**, basis modulo torsion (pdf p. 174): if $P_1, \dots, P_r$ together with the torsion subgroup
generate $M$ (and are linearly independent), then $(M : \sum \mathbb Z P_i) = \#M_{\mathrm{tors}}$, so the quotient is
$\operatorname{disc}\langle\,,\rangle / [M_{\mathrm{tors}}]^2$ with $\operatorname{disc} = \det(\langle P_i, P_j\rangle)$. -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6(b), pdf p. 174"]
theorem remark_10_6_b_basis (B : M →ₗ[ℤ] M →ₗ[ℤ] ℝ) {r : ℕ} (P : Fin r → M) (hP : LinearIndependent ℤ P)
    (hgen : Submodule.span ℤ (Set.range P) ⊔ Submodule.torsion ℤ M = ⊤) :
    (Submodule.span ℤ (Set.range P)).toAddSubgroup.index = Nat.card (Submodule.torsion ℤ M) ∧
    regulatorQuotient B P =
      (Matrix.of fun i j => B (P i) (P j)).det / (Nat.card (Submodule.torsion ℤ M) : ℝ) ^ 2 := by
  have hc : IsCompl (Submodule.span ℤ (Set.range P)) (Submodule.torsion ℤ M) :=
    ⟨disjoint_span_torsion P hP, codisjoint_iff.2 hgen⟩
  have hidx : (Submodule.span ℤ (Set.range P)).toAddSubgroup.index =
      Nat.card (Submodule.torsion ℤ M) :=
    Nat.card_congr (Submodule.quotientEquivOfIsCompl _ _ hc).toEquiv
  refine ⟨hidx, ?_⟩
  unfold regulatorQuotient
  rw [hidx]

end NumberFieldKB.MilneEC
