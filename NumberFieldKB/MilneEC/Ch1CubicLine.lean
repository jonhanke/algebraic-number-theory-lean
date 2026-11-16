import NumberFieldKB.MilneEC.Ch1CubicDefs
import NumberFieldKB.MilneEC.Ch1CubicLocal
import NumberFieldKB.MilneEC.Ch1CubicGrad
import NumberFieldKB.MilneEC.Ch1CubicCB
import NumberFieldKB.MilneEC.Ch1GroupLaw

/-!
# A smooth cubic and a line

Part of the proof of associativity of the chord and tangent law (Milne, *Elliptic Curves*, Theorem I.3.1).
For a smooth cubic form `F` over an algebraically closed field and a line `ℓ` (a nonzero linear form):

* `noCommonComponent_line`: `ℓ` is not a component of `F`;
* `projIntersectionNumber_line_eq_zero`: off $C \cap ℓ$ the intersection number is 0;
* `projIntersectionNumber_line_eq_one`: at a point of $C \cap ℓ$ where `ℓ` is not the tangent line, it is 1;
* `projIntersectionNumber_line_ge_two`: where `ℓ` is the tangent line, it is at least 2;
* `sum_projIntersectionNumber_line`: the intersection numbers add up to 3 (Bezout).

`IsTangentForm F ℓ X`: the gradient of `F` at `X` is proportional to the coefficient vector of `ℓ`.
-/

open MvPolynomial Matrix
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

/-! ### Linear forms -/

theorem pderiv_lin {ℓ : MvPolynomial (Fin 3) K} (hℓ : ℓ.IsHomogeneous 1) (j : Fin 3) :
    pderiv j ℓ = C (linCoeff ℓ j) := by
  have h0 : (pderiv j ℓ).IsHomogeneous 0 := hℓ.pderiv
  ext d
  rw [coeff_C]
  by_cases hd : d = 0
  · subst hd
    simp [coeff_pderiv, linCoeff]
  · rw [if_neg (Ne.symm hd)]
    apply h0.coeff_eq_zero
    intro h
    exact hd ((Finsupp.degree_eq_zero_iff d).mp h)

theorem aeval_pderiv_lin {ℓ : MvPolynomial (Fin 3) K} (hℓ : ℓ.IsHomogeneous 1) (j : Fin 3)
    (x : Fin 3 → K) : aeval x (pderiv j ℓ) = linCoeff ℓ j := by
  rw [pderiv_lin hℓ]; simp

theorem aeval_lin {ℓ : MvPolynomial (Fin 3) K} (hℓ : ℓ.IsHomogeneous 1) (x : Fin 3 → K) :
    aeval x ℓ = ∑ j, linCoeff ℓ j * x j := by
  have := euler_eval hℓ x
  simp only [aeval_pderiv_lin hℓ, Nat.cast_one, one_mul] at this
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_linCoeff_ne_zero {ℓ : MvPolynomial (Fin 3) K} (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0) :
    ∃ j, linCoeff ℓ j ≠ 0 := by
  by_contra h
  push Not at h
  apply hℓ0
  have := hℓ.sum_X_mul_pderiv
  simp only [pderiv_lin hℓ, h, C_0, mul_zero, Finset.sum_const_zero, one_smul] at this
  exact this.symm

theorem exists_kernel_pair {c : Fin 3 → K} (hc : ∃ j, c j ≠ 0) :
    ∃ v w : Fin 3 → K, ∑ j, c j * v j = 0 ∧ ∑ j, c j * w j = 0 ∧
      ∀ s t : K, (s ≠ 0 ∨ t ≠ 0) → s • v + t • w ≠ 0 := by
  obtain ⟨j, hj⟩ := hc
  fin_cases j
  · refine ⟨![-c 1, c 0, 0], ![-c 2, 0, c 0], ?_, ?_, ?_⟩
    · simp [Fin.sum_univ_three]; ring
    · simp [Fin.sum_univ_three]; ring
    · intro s t hst h0
      have h1 := congrFun h0 1
      have h2 := congrFun h0 2
      simp at h1 h2
      simp at hj
      rcases hst with h | h
      · exact h (h1.resolve_right hj)
      · exact h (h2.resolve_right hj)
  · refine ⟨![c 1, -c 0, 0], ![0, -c 2, c 1], ?_, ?_, ?_⟩
    · simp [Fin.sum_univ_three]; ring
    · simp [Fin.sum_univ_three]; ring
    · intro s t hst h0
      have h1 := congrFun h0 0
      have h2 := congrFun h0 2
      simp at h1 h2
      simp at hj
      rcases hst with h | h
      · exact h (h1.resolve_right hj)
      · exact h (h2.resolve_right hj)
  · refine ⟨![c 2, 0, -c 0], ![0, c 2, -c 1], ?_, ?_, ?_⟩
    · simp [Fin.sum_univ_three]; ring
    · simp [Fin.sum_univ_three]; ring
    · intro s t hst h0
      have h1 := congrFun h0 0
      have h2 := congrFun h0 1
      simp at h1 h2
      simp at hj
      rcases hst with h | h
      · exact h (h1.resolve_right hj)
      · exact h (h2.resolve_right hj)

/-! ### A line is not a component -/

theorem hc_mul_lin {ℓ : MvPolynomial (Fin 3) K} (hℓ : ℓ.IsHomogeneous 1)
    (Q : MvPolynomial (Fin 3) K) (n : ℕ) :
    homogeneousComponent (n + 1) (ℓ * Q) = ℓ * homogeneousComponent n Q := by
  conv_lhs => rw [← sum_homogeneousComponent Q]
  rw [Finset.mul_sum, map_sum]
  have key : ∀ i ∈ Finset.range (Q.totalDegree + 1),
      homogeneousComponent (n + 1) (ℓ * homogeneousComponent i Q) =
        if n = i then ℓ * homogeneousComponent i Q else 0 := by
    intro i _
    have hh := hℓ.mul (homogeneousComponent_isHomogeneous i Q)
    rw [homogeneousComponent_of_mem hh]
    have e : (n + 1 = 1 + i) ↔ n = i := by omega
    simp only [e]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq]
  by_cases hn : n ∈ Finset.range (Q.totalDegree + 1)
  · rw [if_pos hn]
  · rw [if_neg hn, homogeneousComponent_eq_zero n Q (by simp at hn; omega), mul_zero]

theorem isHomogeneous_cofactor {F ℓ Q : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3)
    (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0) (hQ : F = ℓ * Q) : Q.IsHomogeneous 2 := by
  have hz : ∀ n, n ≠ 2 → homogeneousComponent n Q = 0 := by
    intro n hn
    have h1 := hc_mul_lin hℓ Q n
    rw [← hQ, homogeneousComponent_of_mem hF, if_neg (by omega)] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hℓ0
  have hQ2 : Q = homogeneousComponent 2 Q := by
    conv_lhs => rw [← sum_homogeneousComponent Q]
    rw [Finset.sum_eq_single 2 (fun b _ hb => hz b hb)]
    intro h2
    exact homogeneousComponent_eq_zero 2 Q (by simp at h2; omega)
  rw [hQ2]
  exact homogeneousComponent_isHomogeneous 2 Q

theorem dvd_of_common_factor {F ℓ h : MvPolynomial (Fin 3) K} (hℓ : ℓ.IsHomogeneous 1)
    (hℓ0 : ℓ ≠ 0) (hirr : Irreducible h) (h1 : h ∣ F) (h2 : h ∣ ℓ) : ℓ ∣ F := by
  obtain ⟨q, hq⟩ := h2
  have hh0 : h ≠ 0 := hirr.ne_zero
  have hq0 : q ≠ 0 := right_ne_zero_of_mul (hq ▸ hℓ0)
  have hdeg := totalDegree_mul_of_isDomain hh0 hq0
  rw [← hq, hℓ.totalDegree hℓ0] at hdeg
  have : h.totalDegree = 0 ∨ q.totalDegree = 0 := by omega
  rcases this with h0 | h0
  · exfalso
    have hc := totalDegree_eq_zero_iff_eq_C.mp h0
    have hc0 : h.coeff 0 ≠ 0 := fun e => hh0 (by rw [hc, e, C_0])
    exact hirr.not_isUnit (hc ▸ (isUnit_iff_ne_zero.mpr hc0).map C)
  · have hc := totalDegree_eq_zero_iff_eq_C.mp h0
    set c := q.coeff 0
    have hc0 : c ≠ 0 := fun e => hq0 (by rw [hc, e, C_0])
    have : h = ℓ * C c⁻¹ := by
      rw [hq, hc, mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, mul_one]
    exact (Dvd.intro _ this.symm).trans h1

theorem noCommonComponent_line [IsAlgClosed K] {F ℓ : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous 3) (hsm : IsSmoothForm F) (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0) :
    NoCommonComponent F ℓ := by
  intro h hirr h1 h2
  obtain ⟨Q, hQ⟩ := dvd_of_common_factor hℓ hℓ0 hirr h1 h2
  have hQh := isHomogeneous_cofactor hF hℓ hℓ0 hQ
  obtain ⟨v, w, hv, hw, hind⟩ := exists_kernel_pair (exists_linCoeff_ne_zero hℓ hℓ0)
  obtain ⟨a0, a1, a2, hb⟩ := binary_quadratic_shape _ (lineRestriction_isHomogeneous hQh v w)
  obtain ⟨s, t, hst, hroot⟩ := exists_root_binary_quadratic a0 a1 a2
  set x : Fin 3 → K := fun j => v j * s + w j * t with hx
  have hQx : aeval x Q = 0 := by
    have h := aeval_aeval_line Q v w (K := K) s t
    have e : aeval ![s, t] (lineRestriction Q v w) = aeval x Q := by
      rw [lineRestriction, h]; simp [hx]
    rw [← e, hb]
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, Algebra.algebraMap_self,
      RingHom.id_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hroot
  have hlx : aeval x ℓ = 0 := by
    rw [aeval_lin hℓ]
    have : ∑ j, linCoeff ℓ j * x j = s * ∑ j, linCoeff ℓ j * v j + t * ∑ j, linCoeff ℓ j * w j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [hx]; ring
    rw [this, hv, hw]; ring
  have hx0 : x ≠ 0 := by
    have := hind s t hst
    intro h
    apply this
    funext j
    have := congrFun h j
    simp only [hx, Pi.zero_apply] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination this
  have hFx : aeval x F = 0 := by rw [hQ, map_mul, hlx, zero_mul]
  obtain ⟨j, hj⟩ := hsm x hx0 hFx
  apply hj
  rw [hQ, Derivation.leibniz]
  simp only [smul_eq_mul, map_add, map_mul, hlx, hQx, zero_mul, add_zero]

theorem projIntersectionNumber_line_eq_zero {F ℓ : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous 3) (hℓ : ℓ.IsHomogeneous 1) {X : ℙ K (Fin 3 → K)}
    (hX : X ∉ projectivePoints F K ∩ projectivePoints ℓ K) :
    projIntersectionNumber F ℓ X = 0 := by
  unfold projIntersectionNumber
  rw [intersectionNumberAt_eq_numAt]
  apply numAt_eq_zero_of_not_mem
  intro hp
  apply hX
  have hi := pieceIndex_coord_ne_zero X.rep X.rep_nonzero
  exact ⟨(aeval_eq_zero_iff_mem_piece hF _ _ hi).mpr hp.1,
    (aeval_eq_zero_iff_mem_piece hℓ _ _ hi).mpr hp.2⟩

/-! ### Tangency in an affine chart -/

theorem proportional_of_det {w0 w1 : K} {G H : Fin 3 → K}
    (hG : G 2 = -(w0 * G 0 + w1 * G 1)) (hH : H 2 = -(w0 * H 0 + w1 * H 1)) (hH0 : H ≠ 0)
    (hdet : G 0 * H 1 - G 1 * H 0 = 0) : ∃ c : K, G = c • H := by
  obtain ⟨c, e0, e1⟩ : ∃ c : K, G 0 = c * H 0 ∧ G 1 = c * H 1 := by
    by_cases h0 : H 0 = 0
    · by_cases h1 : H 1 = 0
      · exfalso
        apply hH0
        funext j
        fin_cases j <;> simp [h0, h1, hH]
      · refine ⟨G 1 / H 1, ?_, by field_simp⟩
        field_simp
        linear_combination hdet
    · refine ⟨G 0 / H 0, by field_simp, ?_⟩
      field_simp
      linear_combination -hdet
  refine ⟨c, funext fun j => ?_⟩
  fin_cases j
  · simpa using e0
  · simpa using e1
  · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    rw [hG, hH, e0, e1]
    ring

theorem evalAt_pderiv_affVec {P : MvPolynomial (Fin 3) K} {d : ℕ} (hP : P.IsHomogeneous d)
    (p : K × K) (a : Fin 2) :
    evalAt (pderiv a (dehomogenize 2 P)) p = aeval (affVec p) (pderiv (pieceVar 2 a) P) := by
  have := evalAt_pderiv_dehomogenize hP 2 (affVec p) (by simp [affVec]) a
  rw [pieceCoords_affVec] at this
  simpa [affVec] using this

theorem det_eq_zero_iff {F ℓ : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3)
    (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0) {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnit A.det)
    (p : K × K) (hFp : aeval (A *ᵥ affVec p) F = 0) (hℓp : aeval (A *ᵥ affVec p) ℓ = 0) :
    (evalAt (pderiv 0 (dehomogenize 2 (linSubst A F))) p *
        evalAt (pderiv 1 (dehomogenize 2 (linSubst A ℓ))) p -
      evalAt (pderiv 1 (dehomogenize 2 (linSubst A F))) p *
        evalAt (pderiv 0 (dehomogenize 2 (linSubst A ℓ))) p = 0) ↔
    ∃ c : K, ∀ j, aeval (A *ᵥ affVec p) (pderiv j F) = c * linCoeff ℓ j := by
  have hF' := isHomogeneous_linSubst hF A
  have hℓ' := isHomogeneous_linSubst hℓ A
  have hAt : Aᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hA.ne_zero
  obtain ⟨g, hg⟩ : ∃ g : Fin 3 → K, ∀ i, g i = aeval (A *ᵥ affVec p) (pderiv i F) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Fin 3 → K, ∀ j, G j = aeval (affVec p) (pderiv j (linSubst A F)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Fin 3 → K, ∀ j, H j = aeval (affVec p) (pderiv j (linSubst A ℓ)) :=
    ⟨_, fun _ => rfl⟩
  have hGv : G = Aᵀ *ᵥ g := by
    funext j
    simp only [hG, hg, pderiv_linSubst, map_sum, map_mul, aeval_C, aeval_linSubst,
      Algebra.algebraMap_self, RingHom.id_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have hHv : H = Aᵀ *ᵥ (fun i => linCoeff ℓ i) := by
    funext j
    simp only [hH, pderiv_linSubst, map_sum, map_mul, aeval_C, aeval_linSubst, aeval_pderiv_lin hℓ,
      Algebra.algebraMap_self, RingHom.id_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have e1 : p.1 * G 0 + p.2 * G 1 + G 2 = 0 := by
    have h3 : aeval (affVec p) (linSubst A F) = 0 := by rw [aeval_linSubst]; exact hFp
    have := euler_eval hF' (affVec p)
    rw [h3, mul_zero, Fin.sum_univ_three] at this
    simp only [← hG] at this
    simpa [affVec] using this
  have e2 : p.1 * H 0 + p.2 * H 1 + H 2 = 0 := by
    have h3 : aeval (affVec p) (linSubst A ℓ) = 0 := by rw [aeval_linSubst]; exact hℓp
    have := euler_eval hℓ' (affVec p)
    rw [h3, mul_zero, Fin.sum_univ_three] at this
    simp only [← hH] at this
    simpa [affVec] using this
  have aF0 : evalAt (pderiv 0 (dehomogenize 2 (linSubst A F))) p = G 0 := by
    rw [evalAt_pderiv_affVec hF', hG]; rfl
  have aF1 : evalAt (pderiv 1 (dehomogenize 2 (linSubst A F))) p = G 1 := by
    rw [evalAt_pderiv_affVec hF', hG]; rfl
  have aH0 : evalAt (pderiv 0 (dehomogenize 2 (linSubst A ℓ))) p = H 0 := by
    rw [evalAt_pderiv_affVec hℓ', hH]; rfl
  have aH1 : evalAt (pderiv 1 (dehomogenize 2 (linSubst A ℓ))) p = H 1 := by
    rw [evalAt_pderiv_affVec hℓ', hH]; rfl
  rw [aF0, aF1, aH0, aH1]
  constructor
  · intro hdet
    have hc0 : (fun i => linCoeff ℓ i) ≠ 0 := by
      obtain ⟨j, hj⟩ := exists_linCoeff_ne_zero hℓ hℓ0
      intro h
      exact hj (congrFun h j)
    have hH0 : H ≠ 0 := fun h => hc0 (Matrix.eq_zero_of_mulVec_eq_zero hAt (hHv ▸ h))
    obtain ⟨c', hc'⟩ := proportional_of_det (w0 := p.1) (w1 := p.2) (by linear_combination e1)
      (by linear_combination e2) hH0 hdet
    refine ⟨c', fun j => ?_⟩
    have hz : Aᵀ *ᵥ (g - c' • (fun i => linCoeff ℓ i)) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ← hGv, ← hHv, hc', sub_self]
    have := congrFun (sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hAt hz)) j
    rw [hg] at this
    simpa using this
  · rintro ⟨c', hc'⟩
    have hgc : g = c' • (fun i => linCoeff ℓ i) := by
      funext j
      rw [hg, hc']
      simp
    have : G = c' • H := by rw [hGv, hHv, hgc, Matrix.mulVec_smul]
    rw [this]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem isTangentForm_mk_iff {F ℓ : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3)
    {y : Fin 3 → K} (hy : y ≠ 0) :
    IsTangentForm F ℓ (Projectivization.mk K y hy) ↔
      ∃ c : K, ∀ j, aeval y (pderiv j F) = c * linCoeff ℓ j := by
  obtain ⟨a, ha, hya⟩ := exists_smul_rep y hy
  have h2 : ∀ j, aeval y (pderiv j F) =
      a ^ 2 * aeval (Projectivization.mk K y hy).rep (pderiv j F) := by
    intro j
    conv_lhs => rw [hya]
    exact aeval_smul_of_isHomogeneous (hF.pderiv (i := j)) a _
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨a ^ 2 * c, fun j => by rw [h2, hc]; ring⟩
  · rintro ⟨c, hc⟩
    refine ⟨(a ^ 2)⁻¹ * c, fun j => ?_⟩
    have h := hc j
    rw [h2] at h
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    field_simp
    linear_combination h

theorem line_core [IsAlgClosed K] {F ℓ : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3)
    (hsm : IsSmoothForm F) (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0) {X : ℙ K (Fin 3 → K)}
    (hX : X ∈ projectivePoints F K ∩ projectivePoints ℓ K) :
    ∃ (f l : MvPolynomial (Fin 2) K) (p : K × K), NonsingAt f p ∧ p ∈ commonZeros f l ∧
      Module.Finite K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, l}) ∧
      numAt f l p = projIntersectionNumber F ℓ X ∧
      (evalAt (pderiv 0 f) p * evalAt (pderiv 1 l) p -
        evalAt (pderiv 1 f) p * evalAt (pderiv 0 l) p = 0 ↔ IsTangentForm F ℓ X) := by
  obtain ⟨fr⟩ := exists_frame hF hℓ (by norm_num) (by norm_num)
    (noCommonComponent_line hF hsm hℓ hℓ0)
  obtain ⟨p, hp, hpX⟩ := fr.surj X hX
  have hpt : fr.pt p = X := hpX
  refine ⟨dehomogenize 2 (linSubst fr.A F), dehomogenize 2 (linSubst fr.A ℓ), p,
    ⟨hp.1, nonsingAt_dehomogenize_linSubst hF (by norm_num) hsm fr.hA hp.1⟩, hp,
    (finrank_quotient_of_isRelPrime_top fr.hf fr.hg fr.hfm fr.hgn fr.hcop).1, ?_, ?_⟩
  · rw [fr.numAt_eq hF hℓ p, hpt]
  · have hFp : aeval (fr.A *ᵥ affVec p) F = 0 := by
      rw [← aeval_linSubst, ← evalAt_dehomogenize_affVec]; exact hp.1
    have hℓp : aeval (fr.A *ᵥ affVec p) ℓ = 0 := by
      rw [← aeval_linSubst, ← evalAt_dehomogenize_affVec]; exact hp.2
    rw [det_eq_zero_iff hF hℓ hℓ0 fr.hA p hFp hℓp, ← hpX]
    exact (isTangentForm_mk_iff hF (mulVec_affVec_ne_zero fr.hA p)).symm

theorem projIntersectionNumber_line_eq_one [IsAlgClosed K] {F ℓ : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous 3) (hsm : IsSmoothForm F) (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0)
    {X : ℙ K (Fin 3 → K)} (hX : X ∈ projectivePoints F K ∩ projectivePoints ℓ K)
    (htan : ¬ IsTangentForm F ℓ X) :
    projIntersectionNumber F ℓ X = 1 := by
  obtain ⟨f, l, p, hns, hp, -, hnum, hiff⟩ := line_core hF hsm hℓ hℓ0 hX
  rw [← hnum]
  exact (numAt_eq_one_of_det hns hp.2 (fun h => htan (hiff.mp h))).2

theorem projIntersectionNumber_line_ge_two [IsAlgClosed K] {F ℓ : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous 3) (hsm : IsSmoothForm F) (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0)
    {X : ℙ K (Fin 3 → K)} (hX : X ∈ projectivePoints F K ∩ projectivePoints ℓ K)
    (htan : IsTangentForm F ℓ X) :
    2 ≤ projIntersectionNumber F ℓ X := by
  obtain ⟨f, l, p, hns, hp, hfin, hnum, hiff⟩ := line_core hF hsm hℓ hℓ0 hX
  rw [← hnum]
  have hpos := numAt_pos hfin hp
  have hne : numAt f l p ≠ 1 := fun h1 => det_ne_zero_of_numAt_eq_one hp h1 (hiff.mpr htan)
  omega

theorem sum_projIntersectionNumber_line [IsAlgClosed K] {F ℓ : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous 3) (hsm : IsSmoothForm F) (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0)
    (S : Finset (ℙ K (Fin 3 → K))) (hS : (S : Set _) = projectivePoints F K ∩ projectivePoints ℓ K) :
    ∑ X ∈ S, projIntersectionNumber F ℓ X = 3 := by
  obtain ⟨S', hS', hsum⟩ := bezout_of_isAlgClosed hF hℓ (by norm_num) (by norm_num)
    (noCommonComponent_line hF hsm hℓ hℓ0)
  have : S = S' := Finset.coe_injective (hS.trans hS'.symm)
  rw [this, hsum]

end NumberFieldKB.MilneEC.Bezout
