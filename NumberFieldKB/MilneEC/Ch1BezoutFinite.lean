import NumberFieldKB.MilneEC.Ch1BezoutDefs
import NumberFieldKB.MilneEC.Ch1IntersectionExists

/-!
# Bezout's theorem: coprimality and finiteness of the intersection

Part of the proof of Milne, *Elliptic Curves*, Theorem I.1.18 (Bezout), after Fulton 1969, §§1.6, 5.1:

* a factor of a nonzero homogeneous polynomial is homogeneous;
* if two forms in $X, Y, Z$ have no common component, neither have their dehomogenizations at $Z = 1$;
* having no common component is preserved by extending the field of coefficients;
* over an algebraically closed field, two forms with no common component have finitely many common zeros
  in the projective plane.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

theorem isHomogeneous_of_dvd {σ : Type*} {F H : MvPolynomial σ K} {m : ℕ} (hF : F.IsHomogeneous m)
    (hF0 : F ≠ 0) (hH : H ∣ F) : ∃ e, H.IsHomogeneous e := by
  obtain ⟨Q, rfl⟩ := hH
  exact (isHomogeneous_of_mul_isHomogeneous hF (left_ne_zero_of_mul hF0)
    (right_ne_zero_of_mul hF0)).1

/-- Homogenization of a polynomial in two variables at the piece `i`. -/
noncomputable def hom (i : Fin 3) (D : ℕ) (p : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 3) K :=
  ∑ d ∈ Finset.range (D + 1), X i ^ (D - d) * rename (pieceVar i) (homogeneousComponent d p)

theorem dehomogenize_X_self (i : Fin 3) : dehomogenize i (X i : MvPolynomial (Fin 3) K) = 1 := by
  fin_cases i <;> simp [dehomogenize, pieceSubst]

theorem dehomogenize_rename_pieceVar (i : Fin 3) (q : MvPolynomial (Fin 2) K) :
    dehomogenize i (rename (pieceVar i) q) = q := by
  unfold dehomogenize
  rw [aeval_rename]
  have : pieceSubst i ∘ pieceVar i = (X : Fin 2 → MvPolynomial (Fin 2) K) := by
    fin_cases i <;> funext a <;> fin_cases a <;> simp [pieceSubst, pieceVar]
  rw [this, aeval_X_left_apply]

theorem isHomogeneous_hom (i : Fin 3) (D : ℕ) (p : MvPolynomial (Fin 2) K) :
    (hom i D p).IsHomogeneous D := by
  unfold hom
  refine IsHomogeneous.sum _ _ _ fun d hd => ?_
  have h1 := (isHomogeneous_X_pow i (D - d)).mul
    ((homogeneousComponent_isHomogeneous d p).rename_isHomogeneous (f := pieceVar i))
  rwa [Nat.sub_add_cancel (by simpa [Nat.lt_succ_iff] using hd)] at h1

theorem dehomogenize_hom (i : Fin 3) {D : ℕ} {p : MvPolynomial (Fin 2) K}
    (hp : p.totalDegree ≤ D) : dehomogenize i (hom i D p) = p := by
  unfold hom dehomogenize
  rw [map_sum]
  simp only [map_mul, map_pow]
  have h1 : ∀ d, (aeval (pieceSubst i)) (rename (pieceVar i) (homogeneousComponent d p))
      = homogeneousComponent d p := fun d => dehomogenize_rename_pieceVar i _
  have h2 : (aeval (pieceSubst i)) (X i : MvPolynomial (Fin 3) K) = 1 := dehomogenize_X_self i
  simp only [h1, h2, one_pow, one_mul]
  conv_rhs => rw [← sum_homogeneousComponent p]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro d hd
    simp only [Finset.mem_range] at hd ⊢
    omega
  · intro d _ hd
    simp only [Finset.mem_range, not_lt] at hd
    exact homogeneousComponent_eq_zero d p (by omega)

theorem eq_zero_of_dehomogenize_eq_zero (i : Fin 3) {P : MvPolynomial (Fin 3) K} {m : ℕ}
    (hP : P.IsHomogeneous m) (h : dehomogenize i P = 0) : P = 0 := by
  let Kf := FractionRing (MvPolynomial (Fin 3) K)
  let v : Fin 3 → Kf := fun j => algebraMap (MvPolynomial (Fin 3) K) Kf (X j)
  have hv : v i ≠ 0 := by
    simp only [v, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin 3) K) Kf)]
    exact X_ne_zero i
  have h1 := evalAt_dehomogenize P i v hv
  rw [h] at h1
  have h2 : aeval ((v i)⁻¹ • v) P = 0 := by rw [← h1]; simp [evalAt]
  rw [aeval_smul_of_isHomogeneous hP] at h2
  have h3 : aeval v P = algebraMap _ Kf P := by
    have : (aeval v : MvPolynomial (Fin 3) K →ₐ[K] Kf) =
        IsScalarTower.toAlgHom K (MvPolynomial (Fin 3) K) Kf := by
      apply MvPolynomial.algHom_ext
      intro j; simp [v]
    exact congrArg (fun φ => φ P) this
  rw [h3] at h2
  have : algebraMap _ Kf P = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 (inv_ne_zero hv)
    · exact h
  exact (map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin 3) K) Kf)).mp this

theorem exists_irreducible_dvd {n : ℕ} [NeZero n] {G : MvPolynomial (Fin n) K} (hG : ¬ IsUnit G) :
    ∃ p, Irreducible p ∧ p ∣ G := by
  by_cases h0 : G = 0
  · exact ⟨X 0, (X_prime (i := (0 : Fin n)) (R := K)).irreducible, by rw [h0]; exact dvd_zero _⟩
  · obtain ⟨p, hp, hpG⟩ := WfDvdMonoid.exists_irreducible_factor hG h0
    exact ⟨p, hp, hpG⟩

theorem dvd_pow_hom (i : Fin 3) {F : MvPolynomial (Fin 3) K} {m : ℕ} (hF : F.IsHomogeneous m)
    {h a : MvPolynomial (Fin 2) K} (hfa : dehomogenize i F = h * a) :
    hom i h.totalDegree h ∣ X i ^ (h.totalDegree + a.totalDegree) * F := by
  have key : X i ^ (h.totalDegree + a.totalDegree) * F =
      X i ^ m * (hom i h.totalDegree h * hom i a.totalDegree a) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_dehomogenize_eq_zero i (m := h.totalDegree + a.totalDegree + m) ?_ ?_
    · refine ((isHomogeneous_X_pow i _).mul hF).sub ?_
      have := (isHomogeneous_X_pow i m).mul
        ((isHomogeneous_hom i h.totalDegree h).mul (isHomogeneous_hom i a.totalDegree a))
      rwa [add_comm m] at this
    · simp only [dehomogenize, map_sub, map_mul, map_pow] at hfa ⊢
      have h1 := dehomogenize_X_self (K := K) i
      have h2 := dehomogenize_hom i (le_refl h.totalDegree)
      have h3 := dehomogenize_hom i (le_refl a.totalDegree)
      simp only [dehomogenize] at h1 h2 h3
      rw [h1, h2, h3, hfa]; simp
  rw [key]
  exact Dvd.dvd.mul_left (dvd_mul_right _ _) _

theorem exists_irreducible_dvd_dehomogenize (i : Fin 3) {H : MvPolynomial (Fin 3) K} (hH0 : H ≠ 0)
    (hH : ¬ IsUnit (dehomogenize i H)) :
    ∃ H', Irreducible H' ∧ H' ∣ H ∧ ¬ IsUnit (dehomogenize i H') := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hassoc⟩ := WfDvdMonoid.exists_factors H hH0
  apply hH
  have h1 : IsUnit (dehomogenize i s.prod) := by
    have : dehomogenize i s.prod = (s.map (dehomogenize i)).prod := by
      unfold dehomogenize; exact map_multiset_prod (aeval (pieceSubst i)) s
    rw [this]
    refine Multiset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
    exact hcon b (hs b hb) ((Multiset.dvd_prod hb).trans hassoc.dvd)
  exact (hassoc.map (aeval (pieceSubst i) : MvPolynomial (Fin 3) K →ₐ[K] _)).isUnit_iff.mp h1

theorem isRelPrime_dehomogenize_aux (i : Fin 3) {F G : MvPolynomial (Fin 3) K} {m n : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hFG : NoCommonComponent F G) :
    IsRelPrime (dehomogenize i F) (dehomogenize i G) := by
  intro d hdf hdg
  by_contra hd
  obtain ⟨h, hh, hhd⟩ := exists_irreducible_dvd hd
  obtain ⟨a, ha⟩ := hhd.trans hdf
  obtain ⟨b, hb⟩ := hhd.trans hdg
  have hdeh : dehomogenize i (hom i h.totalDegree h) = h := dehomogenize_hom i (le_refl _)
  have hH0 : hom i h.totalDegree h ≠ 0 := by
    intro h0
    rw [h0] at hdeh
    exact hh.ne_zero (by rw [← hdeh]; simp [dehomogenize])
  obtain ⟨H', hH', hH'H, hH'u⟩ := exists_irreducible_dvd_dehomogenize i hH0 (by rw [hdeh]; exact hh.not_isUnit)
  have hp := hH'.prime
  have hz : ¬ H' ∣ X i := by
    intro hdvd
    apply hH'u
    have := map_dvd (aeval (pieceSubst i) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 2) K)
      hdvd
    have h1 := dehomogenize_X_self (K := K) i
    simp only [dehomogenize] at h1 ⊢
    rw [h1] at this
    exact isUnit_of_dvd_one this
  refine hFG H' hH' ?_ ?_
  · have := hH'H.trans (dvd_pow_hom i hF ha)
    rcases hp.dvd_or_dvd this with h1 | h1
    · exact absurd (hp.dvd_of_dvd_pow h1) hz
    · exact h1
  · have := hH'H.trans (dvd_pow_hom i hG hb)
    rcases hp.dvd_or_dvd this with h1 | h1
    · exact absurd (hp.dvd_of_dvd_pow h1) hz
    · exact h1

theorem isRelPrime_dehomogenize {F G : MvPolynomial (Fin 3) K} {m n : ℕ} (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) (hFG : NoCommonComponent F G) :
    IsRelPrime (dehomogenize 2 F) (dehomogenize 2 G) :=
  isRelPrime_dehomogenize_aux 2 hF hG hFG

theorem dehomogenize_baseChange (L : Type*) [Field L] [Algebra K L] (i : Fin 3)
    (F : MvPolynomial (Fin 3) K) :
    dehomogenize i (baseChange L F) = baseChange L (dehomogenize i F) := by
  have hs : ∀ j, baseChange L (pieceSubst i j : MvPolynomial (Fin 2) K) = pieceSubst i j := by
    intro j
    fin_cases i <;> fin_cases j <;> simp [pieceSubst]
  have : ((aeval (pieceSubst i) : MvPolynomial (Fin 3) L →ₐ[L] MvPolynomial (Fin 2) L) :
      MvPolynomial (Fin 3) L →+* MvPolynomial (Fin 2) L).comp (map (algebraMap K L)) =
      (map (algebraMap K L)).comp
        ((aeval (pieceSubst i) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 2) K) :
          MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K) := by
    refine ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp
    · simpa using (hs j).symm
  exact congrArg (fun φ => φ F) this

theorem X_dvd_iff_coeff {σ : Type*} {R : Type*} [CommRing R] {i : σ} {p : MvPolynomial σ R} :
    X i ∣ p ↔ ∀ d : σ →₀ ℕ, d i = 0 → p.coeff d = 0 := by
  classical
  rw [X_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h d hd
    have := coeff_modMonomial_of_not_le (s' := d) p (s := Finsupp.single i 1)
      (by rw [Finsupp.single_le_iff]; omega)
    rw [h] at this
    simpa using this.symm
  · intro h
    ext d
    by_cases hle : Finsupp.single i 1 ≤ d
    · rw [coeff_modMonomial_of_le p hle]; simp
    · rw [coeff_modMonomial_of_not_le p hle]
      apply h
      rw [Finsupp.single_le_iff] at hle
      omega

theorem eq_C_mul_X_pow_of_dehomogenize_eq_C (i : Fin 3) {H : MvPolynomial (Fin 3) K} {e : ℕ}
    (hH : H.IsHomogeneous e) {c : K} (h : dehomogenize i H = C c) :
    H = C c * X i ^ e := by
  rw [← sub_eq_zero]
  refine eq_zero_of_dehomogenize_eq_zero i (m := e) ?_ ?_
  · refine hH.sub ?_
    have := (isHomogeneous_C (Fin 3) c).mul (isHomogeneous_X_pow i e)
    rwa [zero_add] at this
  · have h1 := dehomogenize_X_self (K := K) i
    simp only [dehomogenize, map_sub, map_mul, map_pow] at h h1 ⊢
    rw [h, h1]; simp

theorem degreeOf_baseChange (L : Type*) [Field L] [Algebra K L] (j : Fin 2)
    (p : MvPolynomial (Fin 2) K) : degreeOf j (baseChange L p) = degreeOf j p := by
  rw [degreeOf_eq_sup, degreeOf_eq_sup, support_map_of_injective _ (algebraMap K L).injective]

theorem degreeOf_aeval_X (i j : Fin 2) (hij : j ≠ i) (r : Polynomial K) :
    degreeOf j (Polynomial.aeval (X i : MvPolynomial (Fin 2) K) r) = 0 := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact Nat.le_zero.mp ((degreeOf_add_le _ _ _).trans (by simp [hp, hq]))
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    refine Nat.le_zero.mp ((degreeOf_mul_le _ _ _).trans ?_)
    have h1 := degreeOf_pow_le j (X i : MvPolynomial (Fin 2) K) n
    rw [degreeOf_X] at h1
    simp only [hij, ite_false, mul_zero, Nat.le_zero] at h1
    simp [h1]

theorem eq_C_of_degreeOf_eq_zero {L : Type*} [Field L] {h : MvPolynomial (Fin 2) L}
    (h0 : degreeOf 0 h = 0) (h1 : degreeOf 1 h = 0) : h = C (h.coeff 0) := by
  ext m
  by_cases hm : m = 0
  · subst hm; simp
  · rw [coeff_C, if_neg (Ne.symm hm)]
    by_contra hne
    have hs : m ∈ h.support := mem_support_iff.mpr hne
    have a0 := monomial_le_degreeOf 0 hs
    have a1 := monomial_le_degreeOf 1 hs
    apply hm
    ext j
    fin_cases j <;> simp <;> omega

theorem isUnit_of_dvd_of_degreeOf {L : Type*} [Field L] {h R S : MvPolynomial (Fin 2) L}
    (hR : R ≠ 0) (hS : S ≠ 0) (hR1 : degreeOf 1 R = 0) (hS0 : degreeOf 0 S = 0)
    (hhR : h ∣ R) (hhS : h ∣ S) : ∃ c : L, c ≠ 0 ∧ h = C c := by
  obtain ⟨q, rfl⟩ := hhR
  obtain ⟨q', rfl⟩ := hhS
  have hh : h ≠ 0 := left_ne_zero_of_mul hR
  have e1 := degreeOf_mul_eq (n := 1) hh (right_ne_zero_of_mul hR)
  have e0 := degreeOf_mul_eq (n := 0) hh (right_ne_zero_of_mul hS)
  rw [hR1] at e1
  rw [hS0] at e0
  have hc := eq_C_of_degreeOf_eq_zero (h := h) (by omega) (by omega)
  refine ⟨h.coeff 0, ?_, hc⟩
  intro hz
  rw [hz, C_0] at hc
  exact hh hc

theorem isUnit_of_left_eq_zero {F G : MvPolynomial (Fin 3) K} (hFG : NoCommonComponent F G)
    (h0 : F = 0) : IsUnit G := by
  by_contra hG
  obtain ⟨p, hp, hpG⟩ := exists_irreducible_dvd hG
  exact hFG p hp (h0 ▸ dvd_zero p) hpG

theorem not_mem_projectivePoints_of_isUnit {G : MvPolynomial (Fin 3) K} (hG : IsUnit G)
    (P : Projectivization K (Fin 3 → K)) : P ∉ projectivePoints G K := by
  intro h
  exact (hG.map (aeval P.rep : MvPolynomial (Fin 3) K →ₐ[K] K)).ne_zero h

/-- The point of the affine piece `i` with coordinates `p`, as a vector. -/
noncomputable def chartVec (i : Fin 3) (p : K × K) : Fin 3 → K :=
  fun j => aeval ![p.1, p.2] (pieceSubst i j : MvPolynomial (Fin 2) K)

theorem chartVec_ne_zero (i : Fin 3) (p : K × K) : chartVec i p ≠ 0 := by
  intro h
  have := congrFun h i
  revert this
  fin_cases i <;> simp [chartVec, pieceSubst]

theorem smul_eq_chartVec (i : Fin 3) (v : Fin 3 → K) (hv : v i ≠ 0) :
    (v i)⁻¹ • v = chartVec i (pieceCoords i v) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp_all [chartVec, pieceSubst, pieceCoords, div_eq_inv_mul]

theorem evalAt_ofX (r : Polynomial K) (x y : K) :
    evalAt (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) r) (x, y) = r.eval x := by
  have := eval_aeval_X 0 ![x, y] r
  rw [← MvPolynomial.coe_aeval_eq_eval] at this
  simpa [evalAt] using this

theorem evalAt_ofY (r : Polynomial K) (x y : K) :
    evalAt (Polynomial.aeval (X 1 : MvPolynomial (Fin 2) K) r) (x, y) = r.eval y := by
  have := eval_aeval_X 1 ![x, y] r
  rw [← MvPolynomial.coe_aeval_eq_eval] at this
  simpa [evalAt] using this

theorem evalAt_eq_zero_of_mem_span {f g x : MvPolynomial (Fin 2) K} (hx : x ∈ Ideal.span {f, g})
    (p : K × K) (hf : evalAt f p = 0) (hg : evalAt g p = 0) : evalAt x p = 0 := by
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
  unfold evalAt at *
  rw [map_add, map_mul, map_mul, hf, hg]
  simp

theorem finite_chart [IsAlgClosed K] (i : Fin 3) {F G : MvPolynomial (Fin 3) K} {m n : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hFG : NoCommonComponent F G)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) :
    {P : Projectivization K (Fin 3 → K) | P ∈ projectivePoints F K ∩ projectivePoints G K ∧
      P.rep i ≠ 0}.Finite := by
  classical
  have hf0 : dehomogenize i F ≠ 0 := fun h => hF0 (eq_zero_of_dehomogenize_eq_zero i hF h)
  have hg0 : dehomogenize i G ≠ 0 := fun h => hG0 (eq_zero_of_dehomogenize_eq_zero i hG h)
  have hrel := isRelPrime_dehomogenize_aux i hF hG hFG
  obtain ⟨r, hr, hrmem⟩ := exists_ofX_mem_span hf0 hg0 hrel
  obtain ⟨s, hs, hsmem⟩ := exists_ofY_mem_span hf0 hg0 hrel
  let T : Finset (K × K) := r.roots.toFinset ×ˢ s.roots.toFinset
  refine ((T.finite_toSet).image
    (fun p => Projectivization.mk K (chartVec i p) (chartVec_ne_zero i p))).subset ?_
  rintro P ⟨⟨hPF, hPG⟩, hPi⟩
  have hv := P.rep_nonzero
  refine ⟨pieceCoords i P.rep, ?_, ?_⟩
  · have hf : evalAt (dehomogenize i F) (pieceCoords i P.rep) = 0 := by
      rw [evalAt_dehomogenize F i _ hPi, aeval_smul_of_isHomogeneous hF]
      simp [show aeval P.rep F = 0 from hPF]
    have hg : evalAt (dehomogenize i G) (pieceCoords i P.rep) = 0 := by
      rw [evalAt_dehomogenize G i _ hPi, aeval_smul_of_isHomogeneous hG]
      simp [show aeval P.rep G = 0 from hPG]
    have hx := evalAt_eq_zero_of_mem_span hrmem _ hf hg
    have hy := evalAt_eq_zero_of_mem_span hsmem _ hf hg
    generalize pieceCoords i P.rep = p at hx hy ⊢
    obtain ⟨x, y⟩ := p
    change evalAt (Polynomial.aeval (X 0) r) _ = 0 at hx
    rw [evalAt_ofX] at hx
    rw [evalAt_ofY] at hy
    simp [T, hr, hs, hx, hy]
  · simp only
    conv_rhs => rw [← Projectivization.mk_rep P]
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨(P.rep i)⁻¹, smul_eq_chartVec i _ hPi⟩

theorem ofX_ne_zero {r : Polynomial K} (hr : r ≠ 0) : ofX r ≠ 0 := by
  intro h0
  have := yPolyEquiv_ofX r
  rw [h0, map_zero] at this
  exact hr (Polynomial.C_eq_zero.mp this.symm)

theorem ofY_ne_zero {r : Polynomial K} (hr : r ≠ 0) :
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) K) r ≠ 0 := by
  have h3 : renameEquiv K (Equiv.swap (0 : Fin 2) 1) (ofX r) =
      Polynomial.aeval (X 1 : MvPolynomial (Fin 2) K) r := by
    have := Polynomial.aeval_algHom_apply
      (renameEquiv K (Equiv.swap (0 : Fin 2) 1) : MvPolynomial (Fin 2) K ≃ₐ[K] _).toAlgHom
      (X 0 : MvPolynomial (Fin 2) K) r
    have h5 : (renameEquiv K (Equiv.swap (0 : Fin 2) 1) : MvPolynomial (Fin 2) K ≃ₐ[K] _).toAlgHom
        (X 0 : MvPolynomial (Fin 2) K) = (X 1 : MvPolynomial (Fin 2) K) := by simp
    rw [h5] at this
    exact this.symm
  rw [← h3]
  intro h
  exact ofX_ne_zero hr ((renameEquiv K (Equiv.swap (0 : Fin 2) 1)).injective
    (h.trans (map_zero _).symm))

theorem NoCommonComponent.baseChange {F G : MvPolynomial (Fin 3) K} {m n : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hFG : NoCommonComponent F G)
    (L : Type*) [Field L] [Algebra K L] :
    NoCommonComponent (baseChange L F) (baseChange L G) := by
  intro H hH hHF hHG
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  by_cases hF0 : F = 0
  · have hu := (isUnit_of_left_eq_zero hFG hF0).map
      (map (algebraMap K L) : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) L)
    exact hH.not_isUnit (isUnit_of_dvd_unit hHG hu)
  by_cases hG0 : G = 0
  · have hu := (isUnit_of_left_eq_zero (fun h hh h1 h2 => hFG h hh h2 h1) hG0).map
      (map (algebraMap K L) : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) L)
    exact hH.not_isUnit (isUnit_of_dvd_unit hHF hu)
  have hFL : (MilneEC.baseChange L F).IsHomogeneous m := hF.map _
  have hFL0 : MilneEC.baseChange L F ≠ 0 := fun h => hF0 (map_injective _ hinj (h.trans (map_zero _).symm))
  obtain ⟨e, hHe⟩ := isHomogeneous_of_dvd hFL hFL0 hHF
  have hf0 : dehomogenize 2 F ≠ 0 := fun h => hF0 (eq_zero_of_dehomogenize_eq_zero 2 hF h)
  have hg0 : dehomogenize 2 G ≠ 0 := fun h => hG0 (eq_zero_of_dehomogenize_eq_zero 2 hG h)
  have hrel := isRelPrime_dehomogenize hF hG hFG
  have hdF : dehomogenize 2 H ∣ MilneEC.baseChange L (dehomogenize 2 F) := by
    rw [← dehomogenize_baseChange]
    exact map_dvd (aeval (pieceSubst 2) : MvPolynomial (Fin 3) L →ₐ[L] MvPolynomial (Fin 2) L) hHF
  have hdG : dehomogenize 2 H ∣ MilneEC.baseChange L (dehomogenize 2 G) := by
    rw [← dehomogenize_baseChange]
    exact map_dvd (aeval (pieceSubst 2) : MvPolynomial (Fin 3) L →ₐ[L] MvPolynomial (Fin 2) L) hHG
  obtain ⟨r, hr, hrmem⟩ := exists_ofX_mem_span hf0 hg0 hrel
  obtain ⟨s, hs, hsmem⟩ := exists_ofY_mem_span hf0 hg0 hrel
  have hdvdspan : ∀ x ∈ Ideal.span {dehomogenize 2 F, dehomogenize 2 G},
      dehomogenize 2 H ∣ MilneEC.baseChange L x := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
    show _ ∣ map (algebraMap K L) _
    rw [map_add, map_mul, map_mul]
    exact dvd_add (Dvd.dvd.mul_left hdF _) (Dvd.dvd.mul_left hdG _)
  have hR : MilneEC.baseChange L (ofX r) ≠ 0 := fun h =>
    ofX_ne_zero hr (map_injective _ hinj (h.trans (map_zero _).symm))
  have hS : MilneEC.baseChange L (Polynomial.aeval (X 1 : MvPolynomial (Fin 2) K) s) ≠ 0 := fun h =>
    ofY_ne_zero hs (map_injective _ hinj (h.trans (map_zero _).symm))
  obtain ⟨c, hc, hhc⟩ := isUnit_of_dvd_of_degreeOf hR hS
    (by rw [degreeOf_baseChange]; exact degreeOf_aeval_X 0 1 (by decide) r)
    (by rw [degreeOf_baseChange]; exact degreeOf_aeval_X 1 0 (by decide) s)
    (hdvdspan _ hrmem) (hdvdspan _ hsmem)
  have hH' := eq_C_mul_X_pow_of_dehomogenize_eq_C 2 hHe hhc
  have he : e ≠ 0 := by
    rintro rfl
    apply hH.not_isUnit
    rw [hH', pow_zero, mul_one]
    exact (IsUnit.mk0 c hc).map C
  obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  have hXH : X 2 ∣ H := ⟨C c * X 2 ^ e', by rw [hH', pow_succ]; ring⟩
  have desc : ∀ P : MvPolynomial (Fin 3) K, X 2 ∣ MilneEC.baseChange L P → X 2 ∣ P := by
    intro P hP
    rw [X_dvd_iff_coeff] at hP ⊢
    intro d hd
    apply hinj
    rw [map_zero, ← coeff_map]
    exact hP d hd
  exact hFG (X 2) (X_prime (i := (2 : Fin 3)) (R := K)).irreducible (desc _ (hXH.trans hHF))
    (desc _ (hXH.trans hHG))

theorem finite_projectivePoints_inter [IsAlgClosed K] {F G : MvPolynomial (Fin 3) K} {m n : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hFG : NoCommonComponent F G) :
    (projectivePoints F K ∩ projectivePoints G K).Finite := by
  by_cases hF0 : F = 0
  · refine Set.finite_empty.subset fun P hP => ?_
    exact not_mem_projectivePoints_of_isUnit (isUnit_of_left_eq_zero hFG hF0) P hP.2
  by_cases hG0 : G = 0
  · refine Set.finite_empty.subset fun P hP => ?_
    exact not_mem_projectivePoints_of_isUnit
      (isUnit_of_left_eq_zero (fun h hh h1 h2 => hFG h hh h2 h1) hG0) P hP.1
  refine (((finite_chart 0 hF hG hFG hF0 hG0).union (finite_chart 1 hF hG hFG hF0 hG0)).union
    (finite_chart 2 hF hG hFG hF0 hG0)).subset ?_
  intro P hP
  obtain ⟨i, hi⟩ := exists_ne_zero_coord P.rep P.rep_nonzero
  fin_cases i
  · exact Or.inl (Or.inl ⟨hP, hi⟩)
  · exact Or.inl (Or.inr ⟨hP, hi⟩)
  · exact Or.inr ⟨hP, hi⟩

end NumberFieldKB.MilneEC.Bezout
