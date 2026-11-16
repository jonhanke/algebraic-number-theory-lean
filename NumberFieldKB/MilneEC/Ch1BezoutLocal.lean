import NumberFieldKB.MilneEC.Ch1BezoutDefs

/-!
# Bezout's theorem: local intersection numbers under changes of coordinates

Part of the proof of Milne, *Elliptic Curves*, Theorem I.1.18 (Bezout), after Fulton 1969, Chapter 5.

* `numAt_congr`: `numAt` is invariant under an isomorphism of local rings carrying `f`, `g` to unit
  multiples of `f'`, `g'`.
* `intersectionNumberAt_eq_numAt`: Milne's `intersectionNumberAt` (translate to the origin, then take
  the dimension) is the dimension of $\mathcal O_p/(f, g)$.
* `intersectionNumberAt_linSubst`: the intersection number at a point of a projective plane curve can be
  computed in the chart $Z \ne 0$ after any invertible linear change of coordinates (Fulton 1969, §3.1,
  property (3), and §5.1: independence of the affine piece and of projective changes of coordinates).
-/

open MvPolynomial Matrix

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

/-! ### Linear substitutions -/

theorem aeval_linSubst' {R : Type*} [CommRing R] [Algebra K R] (A : Matrix (Fin 3) (Fin 3) K)
    (F : MvPolynomial (Fin 3) K) (v : Fin 3 → R) :
    aeval v (linSubst A F) = aeval (fun i => ∑ j, algebraMap K R (A i j) * v j) F := by
  unfold linSubst
  rw [aeval_bind₁]
  refine congrArg (fun w => aeval w F) ?_
  funext i
  simp [map_sum]

theorem aeval_linSubst (A : Matrix (Fin 3) (Fin 3) K) (F : MvPolynomial (Fin 3) K) (v : Fin 3 → K) :
    aeval v (linSubst A F) = aeval (A *ᵥ v) F := by
  rw [aeval_linSubst']
  congr 1

theorem linSubst_linSubst (A B : Matrix (Fin 3) (Fin 3) K) (F : MvPolynomial (Fin 3) K) :
    linSubst A (linSubst B F) = linSubst (B * A) F := by
  unfold linSubst
  rw [bind₁_bind₁]
  refine congrArg (fun w => bind₁ w F) ?_
  funext i
  simp only [map_sum, map_mul, bind₁_C_right, bind₁_X_right, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem linSubst_one (F : MvPolynomial (Fin 3) K) : linSubst 1 F = F := by
  unfold linSubst
  have : (fun i : Fin 3 => ∑ j, C ((1 : Matrix (Fin 3) (Fin 3) K) i j) * (X j : MvPolynomial (Fin 3) K))
      = X := by
    funext i
    simp [Matrix.one_apply]
  rw [this, bind₁_X_left]; rfl

theorem isHomogeneous_linSubst {F : MvPolynomial (Fin 3) K} {m : ℕ} (hF : F.IsHomogeneous m)
    (A : Matrix (Fin 3) (Fin 3) K) : (linSubst A F).IsHomogeneous m := by
  have hg : ∀ i, (∑ j, C (A i j) * X j : MvPolynomial (Fin 3) K).IsHomogeneous 1 := by
    intro i
    refine IsHomogeneous.sum _ _ _ fun j _ => ?_
    simpa using (isHomogeneous_X K j).C_mul (A i j)
  have := hF.aeval (g := fun i => ∑ j, C (A i j) * X j) hg
  simpa [linSubst] using this

theorem linSubst_inv_left {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnit A.det)
    (F : MvPolynomial (Fin 3) K) : linSubst A (linSubst A⁻¹ F) = F := by
  rw [linSubst_linSubst, Matrix.nonsing_inv_mul A hA, linSubst_one]

theorem linSubst_inv_right {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnit A.det)
    (F : MvPolynomial (Fin 3) K) : linSubst A⁻¹ (linSubst A F) = F := by
  rw [linSubst_linSubst, Matrix.mul_nonsing_inv A hA, linSubst_one]

/-- For an invertible matrix, the linear substitution is a `K`-algebra automorphism. -/
noncomputable def linSubstEquiv (A : Matrix (Fin 3) (Fin 3) K) (hA : IsUnit A.det) :
    MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K :=
  AlgEquiv.ofAlgHom (bind₁ (fun i => ∑ j, C (A i j) * X j))
    (bind₁ (fun i => ∑ j, C (A⁻¹ i j) * X j))
    (AlgHom.ext fun F => by
      have := linSubst_inv_left hA F
      simpa only [linSubst, AlgHom.comp_apply, AlgHom.id_apply] using this)
    (AlgHom.ext fun F => by
      have := linSubst_inv_right hA F
      simpa only [linSubst, AlgHom.comp_apply, AlgHom.id_apply] using this)

theorem linSubstEquiv_apply (A : Matrix (Fin 3) (Fin 3) K) (hA : IsUnit A.det)
    (F : MvPolynomial (Fin 3) K) : linSubstEquiv A hA F = linSubst A F := rfl

theorem noCommonComponent_linSubst {F G : MvPolynomial (Fin 3) K} (h : NoCommonComponent F G)
    {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnit A.det) :
    NoCommonComponent (linSubst A F) (linSubst A G) := by
  intro d hd hdF hdG
  have hB : IsUnit (A⁻¹).det := by
    rw [Matrix.det_nonsing_inv]; exact hA.ringInverse
  have e : ∀ H : MvPolynomial (Fin 3) K,
      linSubstEquiv A⁻¹ hB (linSubst A H) = H := fun H => linSubst_inv_right hA H
  refine h (linSubstEquiv A⁻¹ hB d) (MulEquiv.irreducible_iff (linSubstEquiv A⁻¹ hB).toMulEquiv |>.mpr hd) ?_ ?_
  · have := map_dvd (linSubstEquiv A⁻¹ hB) hdF
    rwa [e] at this
  · have := map_dvd (linSubstEquiv A⁻¹ hB) hdG
    rwa [e] at this

/-! ### Transport of `numAt` -/

/-! ### Transport between localizations of `K[X, Y]` -/

section Transport

variable (P Q : Ideal (MvPolynomial (Fin 2) K)) [P.IsPrime] [Q.IsPrime]

/-- Two localizations of `K[X, Y]` at primes are isomorphic if there are `K`-algebra maps `Φ`, `Ψ`
from `K[X, Y]` inverting the complements of the opposite primes whose induced maps are inverse on
the variables. -/
theorem exists_algEquiv_localization
    (Φ : MvPolynomial (Fin 2) K →ₐ[K] Localization.AtPrime P)
    (Ψ : MvPolynomial (Fin 2) K →ₐ[K] Localization.AtPrime Q)
    (hΦ : ∀ y : Q.primeCompl, IsUnit (Φ y)) (hΨ : ∀ y : P.primeCompl, IsUnit (Ψ y))
    (h1 : ∀ i : Fin 2, IsLocalization.liftAlgHom (M := P.primeCompl) (S := Localization.AtPrime P) hΨ
        (Φ (X i)) = algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime Q) (X i))
    (h2 : ∀ i : Fin 2, IsLocalization.liftAlgHom (M := Q.primeCompl) (S := Localization.AtPrime Q) hΦ
        (Ψ (X i)) = algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime P) (X i)) :
    ∃ E : Localization.AtPrime Q ≃ₐ[K] Localization.AtPrime P,
      ∀ s, E (algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime Q) s) = Φ s := by
  set Φ' := IsLocalization.liftAlgHom (M := Q.primeCompl) (S := Localization.AtPrime Q) hΦ
  set Ψ' := IsLocalization.liftAlgHom (M := P.primeCompl) (S := Localization.AtPrime P) hΨ
  have hΦ' : ∀ s : MvPolynomial (Fin 2) K, Φ' (algebraMap _ (Localization.AtPrime Q) s) = Φ s := fun s => IsLocalization.lift_eq _ _
  have hΨ' : ∀ s : MvPolynomial (Fin 2) K, Ψ' (algebraMap _ (Localization.AtPrime P) s) = Ψ s := fun s => IsLocalization.lift_eq _ _
  refine ⟨AlgEquiv.ofAlgHom Φ' Ψ' ?_ ?_, fun s => hΦ' s⟩
  · apply IsLocalization.algHom_ext P.primeCompl
    apply MvPolynomial.algHom_ext
    intro i
    show Φ' (Ψ' (algebraMap _ (Localization.AtPrime P) (X i))) =
      algebraMap _ (Localization.AtPrime P) (X i)
    rw [hΨ']
    exact h2 i
  · apply IsLocalization.algHom_ext Q.primeCompl
    apply MvPolynomial.algHom_ext
    intro i
    show Ψ' (Φ' (algebraMap _ (Localization.AtPrime Q) (X i))) =
      algebraMap _ (Localization.AtPrime Q) (X i)
    rw [hΦ']
    exact h1 i

end Transport

/-- The dimension of the quotient by `(a, b)` is invariant under an algebra isomorphism carrying `a`,
`b` to unit multiples of `a'`, `b'`. -/
theorem finrank_quotient_span_congr {S₁ S₂ : Type*} [CommRing S₁] [CommRing S₂] [Algebra K S₁]
    [Algebra K S₂] (e : S₁ ≃ₐ[K] S₂) {a b : S₁} {a₂ b₂ : S₂} {u v : S₂} (hu : IsUnit u)
    (hv : IsUnit v) (ha : e a = u * a₂) (hb : e b = v * b₂) :
    Module.finrank K (S₂ ⧸ Ideal.span {a₂, b₂}) = Module.finrank K (S₁ ⧸ Ideal.span {a, b}) := by
  have hI : Ideal.span {a₂, b₂} = (Ideal.span {a, b}).map (e : S₁ →+* S₂) := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    simp only [RingHom.coe_coe]
    rw [ha, hb, Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_mul_left_unit hu,
      Ideal.span_singleton_mul_left_unit hv]
  exact (Ideal.quotientEquivAlg _ _ e hI).toLinearEquiv.finrank_eq.symm

/-- `numAt` is invariant under an isomorphism of local rings carrying `f`, `g` to unit multiples of
`f'`, `g'`. -/
theorem numAt_congr {p q : K × K} (e : LocalRingAt p ≃ₐ[K] LocalRingAt q)
    {f g f' g' : MvPolynomial (Fin 2) K} {u v : LocalRingAt q} (hu : IsUnit u) (hv : IsUnit v)
    (hf : e (algebraMap _ _ f) = u * algebraMap _ _ f')
    (hg : e (algebraMap _ _ g) = v * algebraMap _ _ g') :
    numAt f g p = numAt f' g' q :=
  (finrank_quotient_span_congr e hu hv hf hg).symm

/-! ### Translation to the origin -/

/-- The translation automorphism `f ↦ f(X + c)` of `K[X, Y]`. -/
noncomputable def tr (c : K × K) : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval ![X 0 + C c.1, X 1 + C c.2]

theorem tr_eq_translate (c : K × K) (f : MvPolynomial (Fin 2) K) : tr c f = translate f c := rfl

theorem aeval_tr (c p : K × K) (f : MvPolynomial (Fin 2) K) :
    aeval ![p.1, p.2] (tr c f) = aeval ![p.1 + c.1, p.2 + c.2] f := by
  unfold tr
  rw [comp_aeval_apply]
  refine congrArg (fun w => aeval w f) ?_
  funext i
  fin_cases i <;> simp

theorem tr_tr_neg (p : K × K) (f : MvPolynomial (Fin 2) K) : tr p (tr (-p) f) = f := by
  have : (tr p).comp (tr (-p)) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [tr]
  exact DFunLike.congr_fun this f

theorem tr_neg_tr (p : K × K) (f : MvPolynomial (Fin 2) K) : tr (-p) (tr p f) = f := by
  have := tr_tr_neg (-p) f
  rwa [neg_neg] at this

theorem mem_originIdeal_iff (f : MvPolynomial (Fin 2) K) :
    f ∈ originIdeal K ↔ aeval ![(0 : K), 0] f = 0 := by
  unfold originIdeal
  rw [RingHom.mem_ker]
  have : (![(0 : K), 0]) = (0 : Fin 2 → K) := by funext i; fin_cases i <;> rfl
  rw [this]
  simp [MvPolynomial.aeval_def, MvPolynomial.eval]

theorem mem_pointIdeal_iff (p : K × K) (f : MvPolynomial (Fin 2) K) :
    f ∈ pointIdeal p ↔ aeval ![p.1, p.2] f = 0 := by
  unfold pointIdeal
  rw [RingHom.mem_ker]

/-- Milne's intersection number at `p` (translate `p` to the origin, then take the dimension) is
$\dim_K \mathcal O_p/(f, g)$. -/
theorem intersectionNumberAt_eq_numAt (f g : MvPolynomial (Fin 2) K) (p : K × K) :
    intersectionNumberAt f g p = numAt f g p := by
  have hP : ∀ s : MvPolynomial (Fin 2) K, s ∈ (originIdeal K).primeCompl →
      tr (-p) s ∈ (pointIdeal p).primeCompl := by
    intro s hs h
    apply hs
    replace h := (mem_pointIdeal_iff p _).mp h
    rw [aeval_tr] at h
    refine (mem_originIdeal_iff _).mpr ?_
    simpa using h
  have hQ : ∀ s : MvPolynomial (Fin 2) K, s ∈ (pointIdeal p).primeCompl →
      tr p s ∈ (originIdeal K).primeCompl := by
    intro s hs h
    apply hs
    replace h := (mem_originIdeal_iff _).mp h
    have h2 : aeval ![(0:K), 0] (tr p s) = aeval ![p.1, p.2] s := by
      simpa using aeval_tr p (0, 0) s
    refine (mem_pointIdeal_iff p _).mpr ?_
    rw [← h2]; exact h
  let Φ : MvPolynomial (Fin 2) K →ₐ[K] LocalRingAt p :=
    (IsScalarTower.toAlgHom K (MvPolynomial (Fin 2) K) (LocalRingAt p)).comp (tr (-p))
  let Ψ : MvPolynomial (Fin 2) K →ₐ[K] LocalRingAtOrigin K :=
    (IsScalarTower.toAlgHom K (MvPolynomial (Fin 2) K) (LocalRingAtOrigin K)).comp (tr p)
  have hΦ : ∀ y : (originIdeal K).primeCompl, IsUnit (Φ y) := fun y =>
    IsLocalization.map_units (LocalRingAt p) (⟨tr (-p) y, hP y y.2⟩ : (pointIdeal p).primeCompl)
  have hΨ : ∀ y : (pointIdeal p).primeCompl, IsUnit (Ψ y) := fun y =>
    IsLocalization.map_units (LocalRingAtOrigin K) (⟨tr p y, hQ y y.2⟩ : (originIdeal K).primeCompl)
  obtain ⟨E, hE⟩ := exists_algEquiv_localization (pointIdeal p) (originIdeal K) Φ Ψ hΦ hΨ
    (fun i => by
      have h := IsLocalization.lift_eq (M := (pointIdeal p).primeCompl)
        (S := LocalRingAt p) (g := (Ψ : MvPolynomial (Fin 2) K →+* LocalRingAtOrigin K)) hΨ
        (tr (-p) (X i))
      simp only [IsLocalization.coe_liftAlgHom]
      refine h.trans ?_
      show algebraMap _ _ (tr p (tr (-p) (X i))) = _
      rw [tr_tr_neg])
    (fun i => by
      have h := IsLocalization.lift_eq (M := (originIdeal K).primeCompl)
        (S := LocalRingAtOrigin K) (g := (Φ : MvPolynomial (Fin 2) K →+* LocalRingAt p)) hΦ
        (tr p (X i))
      simp only [IsLocalization.coe_liftAlgHom]
      refine h.trans ?_
      show algebraMap _ _ (tr (-p) (tr p (X i))) = _
      rw [tr_neg_tr])
  unfold intersectionNumberAt localIntersectionNumber numAt LocalQuotient LocalQuotientAt
  refine (finrank_quotient_span_congr (K := K) E (u := 1) (v := 1) isUnit_one isUnit_one ?_ ?_).symm
  · rw [one_mul, hE]
    show algebraMap _ _ (tr (-p) (tr p f)) = _
    rw [tr_neg_tr]
  · rw [one_mul, hE]
    show algebraMap _ _ (tr (-p) (tr p g)) = _
    rw [tr_neg_tr]

/-! ### Evaluation at the point and units of the local ring -/

/-- The evaluation of `O_p` at the point `p`. -/
noncomputable def evAt (p : K × K) : LocalRingAt p →ₐ[K] K :=
  IsLocalization.liftAlgHom (M := (pointIdeal p).primeCompl) (S := LocalRingAt p)
    (f := (aeval ![p.1, p.2] : MvPolynomial (Fin 2) K →ₐ[K] K))
    (fun y => isUnit_iff_ne_zero.mpr fun h => y.2 ((mem_pointIdeal_iff p _).mpr h))

theorem evAt_algebraMap (p : K × K) (s : MvPolynomial (Fin 2) K) :
    evAt p (algebraMap _ (LocalRingAt p) s) = aeval ![p.1, p.2] s :=
  IsLocalization.lift_eq _ _

theorem isUnit_iff_evAt (p : K × K) (x : LocalRingAt p) : IsUnit x ↔ evAt p x ≠ 0 := by
  constructor
  · intro h
    exact (h.map (evAt p)).ne_zero
  · intro h
    by_contra hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (pointIdeal p).primeCompl x
    have ha : a ∈ pointIdeal p := by
      by_contra ha
      exact hx ((IsLocalization.AtPrime.isUnit_mk'_iff (LocalRingAt p) (pointIdeal p) a s).mpr ha)
    apply h
    have h1 := IsLocalization.mk'_spec (LocalRingAt p) a s
    have h2 := congrArg (evAt p) h1
    rw [map_mul, evAt_algebraMap, evAt_algebraMap, (mem_pointIdeal_iff p a).mp ha] at h2
    have h3 : aeval ![p.1, p.2] (s : MvPolynomial (Fin 2) K) ≠ 0 :=
      fun h => s.2 ((mem_pointIdeal_iff p _).mpr h)
    exact (mul_eq_zero.mp h2).resolve_right h3

/-! ### Projective change of the affine chart -/

/-- The `i`-th coordinate of $N (x, y, 1)^{\mathsf T}$, as a polynomial in `x, y`. -/
noncomputable def affL (N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) : MvPolynomial (Fin 2) K :=
  C (N i 0) * X 0 + C (N i 1) * X 1 + C (N i 2)

theorem dehomogenize_linSubst (N : Matrix (Fin 3) (Fin 3) K) (F : MvPolynomial (Fin 3) K) :
    dehomogenize 2 (linSubst N F) = aeval (affL N) F := by
  unfold dehomogenize linSubst
  rw [aeval_bind₁]
  refine congrArg (fun w => aeval w F) ?_
  funext i
  simp [pieceSubst, affL, Fin.sum_univ_three]

theorem aeval_affL (N : Matrix (Fin 3) (Fin 3) K) (p : K × K) (i : Fin 3) :
    aeval ![p.1, p.2] (affL N i) = (N *ᵥ ![p.1, p.2, 1]) i := by
  simp [affL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem aeval_smul_homog {R : Type*} [CommRing R] [Algebra K R] {σ : Type*}
    {G : MvPolynomial σ K} {e : ℕ} (hG : G.IsHomogeneous e) (c : R) (v : σ → R) :
    aeval (c • v) G = c ^ e * aeval v G := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : (∑ i ∈ d.support, d i) = e := by
    have := hG (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have : ∏ i ∈ d.support, (c • v) i ^ d i = c ^ e * ∏ i ∈ d.support, v i ^ d i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hdeg]
  rw [this]; ring

section Chart

variable (N : Matrix (Fin 3) (Fin 3) K) (p : K × K)

/-- The map $K[X, Y] \to \mathcal O_p$ sending `X, Y` to $(N(x,y,1))_{0,1} / (N(x,y,1))_2$. -/
noncomputable def chartMap : MvPolynomial (Fin 2) K →ₐ[K] LocalRingAt p :=
  aeval ![Ring.inverse (algebraMap _ (LocalRingAt p) (affL N 2)) *
      algebraMap _ (LocalRingAt p) (affL N 0),
    Ring.inverse (algebraMap _ (LocalRingAt p) (affL N 2)) *
      algebraMap _ (LocalRingAt p) (affL N 1)]

theorem chartMap_X0 : chartMap N p (X 0) = Ring.inverse (algebraMap _ (LocalRingAt p) (affL N 2)) *
      algebraMap _ (LocalRingAt p) (affL N 0) := by
  simp [chartMap]

theorem chartMap_X1 : chartMap N p (X 1) = Ring.inverse (algebraMap _ (LocalRingAt p) (affL N 2)) *
      algebraMap _ (LocalRingAt p) (affL N 1) := by
  simp [chartMap]

theorem algebraMap_affL {S : Type*} [CommRing S] [Algebra K S] [Algebra (MvPolynomial (Fin 2) K) S]
    [IsScalarTower K (MvPolynomial (Fin 2) K) S] (i : Fin 3) :
    algebraMap (MvPolynomial (Fin 2) K) S (affL N i) =
      algebraMap K S (N i 0) * algebraMap _ S (X 0 : MvPolynomial (Fin 2) K) +
        algebraMap K S (N i 1) * algebraMap _ S (X 1 : MvPolynomial (Fin 2) K)
        + algebraMap K S (N i 2) := by
  simp only [affL, map_add, map_mul, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

/-- Key algebraic identity: if $b = Q (x, y, 1)$ and $\rho b_2 = 1$ with $NQ = 1$, then
$\sum_{j<2} N_{ij} (\rho b_j) + N_{i2} = \rho x_i$. -/
theorem key_identity {R : Type*} [CommRing R] [Algebra K R] (N Q : Matrix (Fin 3) (Fin 3) K)
    (hNQ : N * Q = 1) (x : Fin 3 → R) (ρ : R) (b : Fin 3 → R)
    (hb : ∀ j, b j = ∑ k, algebraMap K R (Q j k) * x k) (hρ : ρ * b 2 = 1) (i : Fin 3) :
    algebraMap K R (N i 0) * (ρ * b 0) + algebraMap K R (N i 1) * (ρ * b 1) +
      algebraMap K R (N i 2) = ρ * x i := by
  have hsum : ∑ j, algebraMap K R (N i j) * b j = x i := by
    simp_rw [hb, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ k, ∑ j, algebraMap K R (N i j) * (algebraMap K R (Q j k) * x k) =
        algebraMap K R ((N * Q) i k) * x k := by
      intro k
      rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]; ring
    simp_rw [this, hNQ, Matrix.one_apply]
    simp [apply_ite (algebraMap K R)]
  have h2 := congrArg (ρ * ·) hsum
  simp only [Fin.sum_univ_three] at h2
  linear_combination h2 - algebraMap K R (N i 2) * hρ

theorem chartMap_affL (Q : Matrix (Fin 3) (Fin 3) K) (hNQ : N * Q = 1) (q : K × K)
    (hB : IsUnit (algebraMap _ (LocalRingAt q) (affL Q 2))) (i : Fin 3) :
    chartMap Q q (affL N i) = Ring.inverse (algebraMap _ (LocalRingAt q) (affL Q 2)) *
      (![algebraMap _ (LocalRingAt q) (X 0 : MvPolynomial (Fin 2) K),
        algebraMap _ (LocalRingAt q) (X 1 : MvPolynomial (Fin 2) K), 1] i) := by
  have := key_identity N Q hNQ
    ![algebraMap _ (LocalRingAt q) (X 0 : MvPolynomial (Fin 2) K),
        algebraMap _ (LocalRingAt q) (X 1 : MvPolynomial (Fin 2) K), 1]
    (Ring.inverse (algebraMap _ (LocalRingAt q) (affL Q 2)))
    (fun j => algebraMap _ (LocalRingAt q) (affL Q j))
    (fun j => by rw [algebraMap_affL, Fin.sum_univ_three]; simp)
    (Ring.inverse_mul_cancel _ hB) i
  rw [← this]
  simp only [affL, map_add, map_mul, chartMap_X0, chartMap_X1, ← MvPolynomial.algebraMap_eq,
    AlgHom.commutes]

theorem lift_chartMap_X (Q : Matrix (Fin 3) (Fin 3) K) (hNQ : N * Q = 1) (q : K × K)
    (Ψ' : LocalRingAt p →ₐ[K] LocalRingAt q)
    (hΨ' : ∀ s, Ψ' (algebraMap _ (LocalRingAt p) s) = chartMap Q q s)
    (hA : IsUnit (algebraMap _ (LocalRingAt p) (affL N 2)))
    (hB : IsUnit (algebraMap _ (LocalRingAt q) (affL Q 2))) (i : Fin 2) :
    Ψ' (chartMap N p (X i)) = algebraMap _ (LocalRingAt q) (X i : MvPolynomial (Fin 2) K) := by
  have hr := Ring.inverse_mul_cancel _ hA
  have hρ := Ring.inverse_mul_cancel _ hB
  have hΨA : ∀ j, Ψ' (algebraMap _ (LocalRingAt p) (affL N j)) = Ring.inverse
      (algebraMap _ (LocalRingAt q) (affL Q 2)) *
      (![algebraMap _ (LocalRingAt q) (X 0 : MvPolynomial (Fin 2) K),
        algebraMap _ (LocalRingAt q) (X 1 : MvPolynomial (Fin 2) K), 1] j) := fun j => by
    rw [hΨ', chartMap_affL N Q hNQ q hB]
  have h2 : Ψ' (Ring.inverse (algebraMap _ (LocalRingAt p) (affL N 2))) =
      algebraMap _ (LocalRingAt q) (affL Q 2) := by
    have := congrArg Ψ' hr
    rw [map_mul, hΨA 2, map_one] at this
    replace this : Ψ' (Ring.inverse (algebraMap _ (LocalRingAt p) (affL N 2))) *
        Ring.inverse (algebraMap _ (LocalRingAt q) (affL Q 2)) = 1 := by
      rw [← this]; congr 1; exact (mul_one _).symm
    calc _ = Ψ' (Ring.inverse (algebraMap _ (LocalRingAt p) (affL N 2))) *
          (Ring.inverse (algebraMap _ (LocalRingAt q) (affL Q 2)) *
            algebraMap _ (LocalRingAt q) (affL Q 2)) := by rw [hρ, mul_one]
      _ = _ := by rw [← mul_assoc, this, one_mul]
  fin_cases i
  · simp only [Fin.zero_eta, chartMap_X0, map_mul, h2, hΨA 0]
    show _ * (_ * algebraMap _ _ (X 0 : MvPolynomial (Fin 2) K)) = _
    linear_combination (algebraMap _ (LocalRingAt q) (X 0 : MvPolynomial (Fin 2) K)) * hρ
  · simp only [Fin.mk_one, chartMap_X1, map_mul, h2, hΨA 1]
    show _ * (_ * algebraMap _ _ (X 1 : MvPolynomial (Fin 2) K)) = _
    linear_combination (algebraMap _ (LocalRingAt q) (X 1 : MvPolynomial (Fin 2) K)) * hρ

theorem evAt_algebraMap_affL (c : K) (q : K × K)
    (hpq : N *ᵥ ![p.1, p.2, 1] = c • ![q.1, q.2, 1]) (j : Fin 3) :
    evAt p (algebraMap _ (LocalRingAt p) (affL N j)) = (c • ![q.1, q.2, 1]) j := by
  rw [evAt_algebraMap, aeval_affL, hpq]

theorem evAt_chartMap (c : K) (hc : c ≠ 0) (q : K × K)
    (hpq : N *ᵥ ![p.1, p.2, 1] = c • ![q.1, q.2, 1]) (s : MvPolynomial (Fin 2) K) :
    evAt p (chartMap N p s) = aeval ![q.1, q.2] s := by
  have hA2 : evAt p (algebraMap _ (LocalRingAt p) (affL N 2)) = c := by
    rw [evAt_algebraMap_affL N p c q hpq]; simp
  have hAu : IsUnit (algebraMap _ (LocalRingAt p) (affL N 2)) :=
    (isUnit_iff_evAt p _).mpr (by rw [hA2]; exact hc)
  have hr : evAt p (Ring.inverse (algebraMap _ (LocalRingAt p) (affL N 2))) = c⁻¹ := by
    have := congrArg (evAt p) (Ring.inverse_mul_cancel _ hAu)
    rw [map_mul, hA2, map_one] at this
    exact eq_inv_of_mul_eq_one_left this
  unfold chartMap
  rw [comp_aeval_apply]
  refine congrArg (fun w => (aeval w : MvPolynomial (Fin 2) K →ₐ[K] K) s) ?_
  funext i
  fin_cases i
  · show evAt p (_ * _) = ![q.1, q.2] 0
    rw [map_mul, hr, evAt_algebraMap_affL N p c q hpq]
    simp [hc]
  · show evAt p (_ * _) = ![q.1, q.2] 1
    rw [map_mul, hr, evAt_algebraMap_affL N p c q hpq]
    simp [hc]

end Chart

theorem exists_chart_equiv (N Q : Matrix (Fin 3) (Fin 3) K) (hNQ : N * Q = 1) (hQN : Q * N = 1)
    (p q : K × K) (c : K) (hc : c ≠ 0) (hpq : N *ᵥ ![p.1, p.2, 1] = c • ![q.1, q.2, 1]) :
    ∃ E : LocalRingAt q ≃ₐ[K] LocalRingAt p,
      ∀ s, E (algebraMap _ (LocalRingAt q) s) = chartMap N p s := by
  have hqp : Q *ᵥ ![q.1, q.2, 1] = c⁻¹ • ![p.1, p.2, 1] := by
    have h := congrArg (fun v => Q *ᵥ v) hpq
    simp only [Matrix.mulVec_mulVec, hQN, Matrix.one_mulVec, Matrix.mulVec_smul] at h
    rw [h, inv_smul_smul₀ hc]
  have hA : IsUnit (algebraMap _ (LocalRingAt p) (affL N 2)) := by
    refine (isUnit_iff_evAt p _).mpr ?_
    rw [evAt_algebraMap_affL N p c q hpq]; simpa using hc
  have hB : IsUnit (algebraMap _ (LocalRingAt q) (affL Q 2)) := by
    refine (isUnit_iff_evAt q _).mpr ?_
    rw [evAt_algebraMap_affL Q q c⁻¹ p hqp]; simpa using hc
  have hΦ : ∀ y : (pointIdeal q).primeCompl, IsUnit (chartMap N p y) := fun y => by
    refine (isUnit_iff_evAt p _).mpr ?_
    rw [evAt_chartMap N p c hc q hpq]
    exact fun h => y.2 ((mem_pointIdeal_iff q _).mpr h)
  have hΨ : ∀ y : (pointIdeal p).primeCompl, IsUnit (chartMap Q q y) := fun y => by
    refine (isUnit_iff_evAt q _).mpr ?_
    rw [evAt_chartMap Q q c⁻¹ (inv_ne_zero hc) p hqp]
    exact fun h => y.2 ((mem_pointIdeal_iff p _).mpr h)
  exact exists_algEquiv_localization (pointIdeal p) (pointIdeal q) (chartMap N p) (chartMap Q q)
    hΦ hΨ
    (fun i => lift_chartMap_X N p Q hNQ q
      (IsLocalization.liftAlgHom (M := (pointIdeal p).primeCompl) (S := LocalRingAt p) hΨ)
      (fun s => IsLocalization.lift_eq _ _) hA hB i)
    (fun i => lift_chartMap_X Q q N hQN p
      (IsLocalization.liftAlgHom (M := (pointIdeal q).primeCompl) (S := LocalRingAt q) hΦ)
      (fun s => IsLocalization.lift_eq _ _) hB hA i)

theorem chartMap_dehomogenize (N : Matrix (Fin 3) (Fin 3) K) (p : K × K)
    (hA : IsUnit (algebraMap _ (LocalRingAt p) (affL N 2))) {F : MvPolynomial (Fin 3) K} {m : ℕ}
    (hF : F.IsHomogeneous m) :
    chartMap N p (dehomogenize 2 F) = Ring.inverse (algebraMap _ (LocalRingAt p) (affL N 2)) ^ m *
      algebraMap _ (LocalRingAt p) (dehomogenize 2 (linSubst N F)) := by
  have h1 : algebraMap _ (LocalRingAt p) (dehomogenize 2 (linSubst N F)) =
      aeval (fun i => algebraMap _ (LocalRingAt p) (affL N i)) F := by
    rw [dehomogenize_linSubst]
    exact comp_aeval_apply (f := affL N)
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin 2) K) (LocalRingAt p)) F
  rw [h1, ← aeval_smul_homog hF]
  unfold dehomogenize
  rw [comp_aeval_apply]
  refine congrArg (fun w => aeval w F) ?_
  funext i
  have hr := Ring.inverse_mul_cancel _ hA
  fin_cases i
  · simp [pieceSubst, chartMap_X0]
  · simp [pieceSubst, chartMap_X1]
  · simp [pieceSubst, hr]

/-- Core projective-change lemma, on the chart `2`. -/
theorem numAt_linSubst_chart2 {F G : MvPolynomial (Fin 3) K} {m n : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : IsUnit M.det) (u : Fin 3 → K) (hu : u 2 ≠ 0) (hMu : (M *ᵥ u) 2 ≠ 0) :
    numAt (dehomogenize 2 (linSubst M F)) (dehomogenize 2 (linSubst M G)) (pieceCoords 2 u) =
      numAt (dehomogenize 2 F) (dehomogenize 2 G) (pieceCoords 2 (M *ᵥ u)) := by
  set p := pieceCoords 2 u with hp
  set q := pieceCoords 2 (M *ᵥ u) with hq
  set c : K := (u 2)⁻¹ * (M *ᵥ u) 2 with hcdef
  have hc : c ≠ 0 := mul_ne_zero (inv_ne_zero hu) hMu
  have hpq : M *ᵥ ![p.1, p.2, 1] = c • ![q.1, q.2, 1] := by
    have h1 : ![p.1, p.2, 1] = (u 2)⁻¹ • u := by
      funext i
      fin_cases i <;> simp [hp, pieceCoords, div_eq_inv_mul, hu]
    have h2 : ![q.1, q.2, 1] = ((M *ᵥ u) 2)⁻¹ • (M *ᵥ u) := by
      funext i
      fin_cases i <;> simp [hq, pieceCoords, div_eq_inv_mul, hMu]
    rw [h1, h2, Matrix.mulVec_smul, smul_smul]
    congr 1
    rw [hcdef]
    field_simp
  have hMinv : IsUnit (M⁻¹).det := by
    rw [Matrix.det_nonsing_inv]; exact hM.ringInverse
  obtain ⟨E, hE⟩ := exists_chart_equiv M M⁻¹ (Matrix.mul_nonsing_inv M hM)
    (Matrix.nonsing_inv_mul M hM) p q c hc hpq
  have hA : IsUnit (algebraMap _ (LocalRingAt p) (affL M 2)) := by
    refine (isUnit_iff_evAt p _).mpr ?_
    rw [evAt_algebraMap_affL M p c q hpq]; simpa using hc
  have hrU : IsUnit (Ring.inverse (algebraMap _ (LocalRingAt p) (affL M 2))) :=
    hA.ringInverse
  symm
  exact numAt_congr E (hrU.pow m) (hrU.pow n)
    (by rw [hE, chartMap_dehomogenize M p hA hF])
    (by rw [hE, chartMap_dehomogenize M p hA hG])

/-- Permutation matrices relating the chart `i` to the chart `2`. -/
theorem exists_chart_perm (i : Fin 3) : ∃ σ τ : Matrix (Fin 3) (Fin 3) K, σ * τ = 1 ∧
    (∀ F : MvPolynomial (Fin 3) K, dehomogenize i F = dehomogenize 2 (linSubst σ F)) ∧
    (∀ v : Fin 3 → K, pieceCoords i v = pieceCoords 2 (τ *ᵥ v)) ∧
    (∀ v : Fin 3 → K, (τ *ᵥ v) 2 = v i) := by
  have key : ∀ σ : Matrix (Fin 3) (Fin 3) K, affL σ = pieceSubst i →
      ∀ F : MvPolynomial (Fin 3) K, dehomogenize i F = dehomogenize 2 (linSubst σ F) := by
    intro σ h F
    rw [dehomogenize_linSubst, h]; rfl
  fin_cases i
  · refine ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], ?_, key _ ?_, ?_, ?_⟩
    · ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · funext j; fin_cases j <;> simp [affL, pieceSubst]
    · intro v; simp [pieceCoords, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · intro v; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · refine ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], ?_, key _ ?_, ?_, ?_⟩
    · ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · funext j; fin_cases j <;> simp [affL, pieceSubst]
    · intro v; simp [pieceCoords, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · intro v; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · refine ⟨1, 1, by simp, key _ ?_, ?_, ?_⟩
    · funext j; fin_cases j <;> simp [affL, pieceSubst, Matrix.one_apply]
    · intro v; simp
    · intro v; simp

theorem pieceCoords_smul (i : Fin 3) {c : K} (hc : c ≠ 0) (v : Fin 3 → K) :
    pieceCoords i (c • v) = pieceCoords i v := by
  fin_cases i <;> simp [pieceCoords, mul_div_mul_left _ _ hc]

theorem pieceIndex_ne_zero (v : Fin 3 → K) (hv : v ≠ 0) : v (pieceIndex v) ≠ 0 := by
  unfold pieceIndex
  by_cases h2 : v 2 ≠ 0
  · simp [h2]
  · by_cases h1 : v 1 ≠ 0
    · simp [h2, h1]
    · have h0 : v 0 ≠ 0 := by
        intro h0
        apply hv
        funext j
        fin_cases j
        · exact h0
        · exact not_not.mp h1
        · exact not_not.mp h2
      simpa [h2, h1] using h0

/-- Fulton 1969, §5.1: the intersection number at a point of the projective plane can be computed on
the chart $Z \neq 0$ after an invertible linear change of coordinates. The point `w` of the curves
$F(A\vec x) = 0$, $G(A\vec x) = 0$ corresponds to the point $A w$ of $F = 0$, $G = 0$. -/
theorem intersectionNumberAt_linSubst {F G : MvPolynomial (Fin 3) K} {m n : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) {A : Matrix (Fin 3) (Fin 3) K}
    (hA : IsUnit A.det) (w : Fin 3 → K) (hw : w 2 ≠ 0) (hAw : A *ᵥ w ≠ 0) :
    intersectionNumberAt (dehomogenize 2 (linSubst A F)) (dehomogenize 2 (linSubst A G))
        (pieceCoords 2 w) =
      projIntersectionNumber F G (Projectivization.mk K (A *ᵥ w) hAw) := by
  set P := Projectivization.mk K (A *ᵥ w) hAw with hP
  obtain ⟨c, hc, hcv⟩ := exists_smul_rep (A *ᵥ w) hAw
  have hrep : P.rep ≠ 0 := P.rep_nonzero
  set i := pieceIndex P.rep with hi
  have hri : P.rep i ≠ 0 := pieceIndex_ne_zero _ hrep
  obtain ⟨σ, τ, hστ, hdeh, hpc, hτ⟩ := exists_chart_perm (K := K) i
  have hτdet : IsUnit τ.det := Matrix.isUnit_det_of_left_inverse hστ
  have hMdet : IsUnit (τ * A).det := by
    rw [Matrix.det_mul]; exact hτdet.mul hA
  unfold projIntersectionNumber
  rw [intersectionNumberAt_eq_numAt, intersectionNumberAt_eq_numAt]
  rw [← hi, hdeh F, hdeh G, hpc]
  have hmul : (τ * A) *ᵥ w = τ *ᵥ (A *ᵥ w) := by rw [Matrix.mulVec_mulVec]
  have hsm : pieceCoords 2 (τ *ᵥ P.rep) = pieceCoords 2 ((τ * A) *ᵥ w) := by
    rw [hmul, hcv, Matrix.mulVec_smul, pieceCoords_smul 2 hc]
  rw [hsm]
  have hne : ((τ * A) *ᵥ w) 2 ≠ 0 := by
    rw [hmul, hτ, hcv]
    simpa [hc] using hri
  have := numAt_linSubst_chart2 (isHomogeneous_linSubst hF σ) (isHomogeneous_linSubst hG σ)
    hMdet w hw hne
  rw [linSubst_linSubst, linSubst_linSubst, ← Matrix.mul_assoc, hστ, Matrix.one_mul] at this
  exact this

end NumberFieldKB.MilneEC.Bezout
