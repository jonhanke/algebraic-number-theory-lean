import NumberFieldKB.MilneCFT.Ch7.GaloisAdeles
import NumberFieldKB.MilneCFT.Ch7.Basic

/-!
# Milne, *Class Field Theory*, Chapter VII §§2, 4: $H^0_T(G, C_L) = \mathbb I_K/K^\times\mathrm{Nm}(\mathbb I_L)$

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

For $L/K$ finite Galois with group $G$:
* **Proposition 2.5 (a)** (`prop_2_5a`): $\mathbb I_K\to\mathbb I_L^G$ is an isomorphism.
* The norm of ideles is the $G$-norm: $\iota(\mathrm{Nm}_{L/K}x) = \prod_{\sigma\in G}\sigma x$ (`ideleIncl_ideleNorm`).
* **Lemma 4.1** (`lemma_4_1`): $C_K\to C_L^G$ is an isomorphism (from Hilbert 90).
* `card_tateZero_ideleClassRep`: $|H^0_T(G, C_L)| = (\mathbb I_K : K^\times\mathrm{Nm}(\mathbb I_L))$ (p. 207).
-/

open IsDedekindDomain NumberField CategoryTheory

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

section Aux

open QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.Ideles

omit [IsGalois K L] in
/-- $\iota:\mathbb A_K\to\mathbb A_L$ is injective. -/
theorem adeleMap_injective : Function.Injective (adeleMap K L) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  set b := Module.finBasis K L
  have h1 : (adeleBaseChange b).symm 1 = diagVec K (Fin (Module.finrank K L)) (b.equivFun 1) := by
    have := adeleBaseChange_diag b (b.equivFun 1)
    rw [LinearEquiv.symm_apply_apply] at this
    have hd : diag L 1 = 1 := map_one (diagRing L)
    rw [hd] at this
    rw [← this, ContinuousAddEquiv.symm_apply_apply]
  obtain ⟨i, hi⟩ : ∃ i, b.equivFun 1 i ≠ 0 := by
    by_contra h
    push Not at h
    have : b.equivFun 1 = 0 := funext h
    simp at this
  have h2 := adeleBaseChange_smul b t ((adeleBaseChange b).symm 1)
  rw [ht, zero_mul] at h2
  have h3 := congrFun ((adeleBaseChange b).injective (h2.trans (adeleBaseChange b).map_zero.symm)) i
  rw [h1] at h3
  simp only [diagVec_apply, Pi.zero_apply] at h3
  have hu : IsUnit (diagRing K (b.equivFun 1 i)) := (Ne.isUnit hi).map _
  exact (hu.mul_left_eq_zero).mp h3

omit [IsGalois K L] in
/-- $\iota(\xi)$ for $\xi\in K$ is the diagonal image of $\xi\in L$. -/
theorem adeleMap_diagRing (c : K) : adeleMap K L (diagRing K c) = diagRing L (algebraMap K L c) :=
  adeleMap_diag c

/-- A $G$-fixed adele of $L$ lies in $\iota(\mathbb A_K)$ (averaging with the trace). -/
theorem exists_adeleMap_of_fixed (y : Adeles L) (h : ∀ σ : Gal(L/K), galAdeleFun σ y = y) :
    ∃ t : Adeles K, y = adeleMap K L t := by
  set b := Module.finBasis K L
  set a := (adeleBaseChange b).symm y
  set m : ℕ := Fintype.card Gal(L/K)
  have hm : (m : K) ≠ 0 := by
    have : 0 < m := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsum : ∑ σ : Gal(L/K), galAdeleFun σ y = m • y := by
    rw [Finset.sum_congr rfl (fun σ _ => h σ), Finset.sum_const, Finset.card_univ]
  have hexp : ∑ σ : Gal(L/K), galAdeleFun σ y =
      adeleMap K L (∑ j, diagRing K (Algebra.trace K L (b j)) * a j) := by
    simp only [galAdeleFun_eq, map_sum, map_mul, adeleMap_diagRing]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← map_sum, trace_eq_sum_automorphisms]
  refine ⟨diagRing K (m : K)⁻¹ * ∑ j, diagRing K (Algebra.trace K L (b j)) * a j, ?_⟩
  rw [map_mul, ← hexp, hsum, adeleMap_diagRing, nsmul_eq_mul, ← mul_assoc, ← map_natCast (diagRing L) m,
    ← map_mul]
  have : algebraMap K L (m : K)⁻¹ * (m : L) = 1 := by
    rw [map_inv₀, map_natCast]
    exact inv_mul_cancel₀ (by exact_mod_cast hm)
  rw [this, map_one, one_mul]

omit [IsGalois K L] in
/-- `ideleGroupEquiv L` intertwines `ideleIncl` with `Units.map (adeleMap K L)`. -/
theorem ideleGroupEquiv_ideleIncl (x : IdeleGroup (𝓞 K) K) :
    ideleGroupEquiv L (ideleIncl K L x) = Units.map (adeleMap K L).toMonoidHom (ideleGroupEquiv K x) :=
  ContinuousMulEquiv.apply_symm_apply _ _

omit [IsGalois K L] in
/-- A fixed idele has fixed adelic coordinates. -/
theorem galAdeleFun_of_smul_eq (σ : Gal(L/K)) (y : IdeleGroup (𝓞 L) L) (h : σ • y = y) :
    galAdeleFun σ (adeleRingEquiv L (y : AdeleRing (𝓞 L) L)) = adeleRingEquiv L (y : AdeleRing (𝓞 L) L) := by
  have := congrArg (fun z : IdeleGroup (𝓞 L) L => adeleRingEquiv L (z : AdeleRing (𝓞 L) L)) h
  simp only [val_smul_idele, adeleRingEquiv_smul] at this
  exact this

end Aux

/-- **Proposition 2.5 (a)** (Milne, *CFT*, Chapter VII, p. 205): the map $\mathbb I_K\hookrightarrow\mathbb I_L$ is
injective with image $\mathbb I_L^G$. -/
@[kb "milne2020cft" "Ch. VII, Prop. 2.5 (a)"]
theorem prop_2_5a : Function.Injective (ideleIncl K L) ∧
    ∀ y : IdeleGroup (𝓞 L) L, (∀ σ : Gal(L/K), σ • y = y) ↔ y ∈ (ideleIncl K L).range := by
  refine ⟨?_, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · intro x x' h
    apply (NumberFieldKB.Ideles.ideleGroupEquiv K).injective
    have h' := congrArg (NumberFieldKB.Ideles.ideleGroupEquiv L) h
    rw [ideleGroupEquiv_ideleIncl, ideleGroupEquiv_ideleIncl] at h'
    exact Units.map_injective (adeleMap_injective K L) h'
  · obtain ⟨t, ht⟩ := exists_adeleMap_of_fixed K L _ (fun σ => galAdeleFun_of_smul_eq K L σ y (hy σ))
    obtain ⟨t', ht'⟩ := exists_adeleMap_of_fixed K L _
      (fun σ => galAdeleFun_of_smul_eq K L σ y⁻¹ (by rw [smul_inv', hy σ]))
    have hmul : t * t' = 1 := by
      apply adeleMap_injective K L
      rw [map_mul, ← ht, ← ht', map_one, ← map_mul]
      have : ((y * y⁻¹ : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L) = 1 := by rw [mul_inv_cancel]; rfl
      rw [← map_one (NumberFieldKB.Ideles.adeleRingEquiv L), ← this]
      rfl
    have hmul' : t' * t = 1 := by rw [mul_comm, hmul]
    refine ⟨(NumberFieldKB.Ideles.ideleGroupEquiv K).symm ⟨t, t', hmul, hmul'⟩, ?_⟩
    apply (NumberFieldKB.Ideles.ideleGroupEquiv L).injective
    rw [ideleGroupEquiv_ideleIncl, ContinuousMulEquiv.apply_symm_apply]
    exact Units.ext ht.symm
  · rintro ⟨x, rfl⟩ σ
    exact smul_ideleIncl σ x

section Aux2

open QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.Ideles

omit [IsGalois K L] in
/-- The polynomial $\det(\sum_jX_jA_j)$, $A_j$ the matrix of multiplication by $b_j$. -/
def detPoly : MvPolynomial (Fin (Module.finrank K L)) L :=
  (Matrix.of fun i k => ∑ j, MvPolynomial.C (algebraMap K L
    (Algebra.leftMulMatrix (Module.finBasis K L) (Module.finBasis K L j) i k)) * MvPolynomial.X j).det

omit [IsGalois K L] in
/-- The polynomial $\prod_\sigma\sum_j\sigma(b_j)X_j$. -/
def prodPoly : MvPolynomial (Fin (Module.finrank K L)) L :=
  ∏ σ : Gal(L/K), ∑ j, MvPolynomial.C (σ (Module.finBasis K L j)) * MvPolynomial.X j

/-- $\det(\sum_jc_jA_j) = N_{L/K}(\sum_jc_jb_j)$. -/
theorem det_comb_eq_norm (c : Fin (Module.finrank K L) → K) :
    (Matrix.of fun i k => ∑ j, c j * Algebra.leftMulMatrix (Module.finBasis K L) (Module.finBasis K L j) i k).det =
      Algebra.norm K (∑ j, c j • Module.finBasis K L j) := by
  rw [Algebra.norm_eq_matrix_det (Module.finBasis K L)]
  congr 1
  ext i k
  simp [map_sum, map_smul, Matrix.sum_apply]

/-- **Polynomial identity**: $\det(\sum_jX_jA_j)=\prod_\sigma\sum_j\sigma(b_j)X_j$ in $L[X_0,\dots,X_{n-1}]$. -/
theorem detPoly_eq_prodPoly : detPoly K L = prodPoly K L := by
  have : Infinite K := CharZero.infinite K
  refine MvPolynomial.funext_set (fun _ => Set.range (algebraMap K L))
    (fun _ => Set.infinite_range_of_injective (algebraMap K L).injective) fun x hx => ?_
  choose c hc using fun i => hx i (Set.mem_univ i)
  have hx' : x = fun i => algebraMap K L (c i) := funext fun i => (hc i).symm
  subst hx'
  have h1 : MvPolynomial.eval (fun i => algebraMap K L (c i)) (detPoly K L) =
      algebraMap K L (Algebra.norm K (∑ j, c j • Module.finBasis K L j)) := by
    rw [← det_comb_eq_norm, detPoly, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i k
    simp [map_sum, mul_comm]
  have h2 : MvPolynomial.eval (fun i => algebraMap K L (c i)) (prodPoly K L) =
      algebraMap K L (Algebra.norm K (∑ j, c j • Module.finBasis K L j)) := by
    rw [Algebra.norm_eq_prod_automorphisms, prodPoly, map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    simp [map_sum, Algebra.smul_def, mul_comm]
  rw [h1, h2]

/-- Evaluating the polynomial identity in any commutative $L$-algebra, at any point. -/
theorem det_eq_prod {R : Type*} [CommRing R] (φ : L →+* R) (c : Fin (Module.finrank K L) → R) :
    (Matrix.of fun i k => ∑ j, φ (algebraMap K L
      (Algebra.leftMulMatrix (Module.finBasis K L) (Module.finBasis K L j) i k)) * c j).det =
      ∏ σ : Gal(L/K), ∑ j, φ (σ (Module.finBasis K L j)) * c j := by
  have h := congrArg (MvPolynomial.eval₂Hom φ c) (detPoly_eq_prodPoly K L)
  rw [detPoly, prodPoly, RingHom.map_det, map_prod] at h
  convert h using 2
  · ext i k
    simp
  · simp

/-- $y\mapsto M(y)$ is additive. -/
theorem adeleLmat_add (y z : Adeles L) :
    adeleLmat (Module.finBasis K L) (y + z) = adeleLmat (Module.finBasis K L) y + adeleLmat (Module.finBasis K L) z :=
  Matrix.ext fun i j => by simp [adeleLmat, add_mul]

/-- $y\mapsto M(y)$ commutes with finite sums. -/
theorem adeleLmat_sum {ι' : Type*} (s : Finset ι') (f : ι' → Adeles L) :
    adeleLmat (Module.finBasis K L) (∑ i ∈ s, f i) = ∑ i ∈ s, adeleLmat (Module.finBasis K L) (f i) :=
  map_sum (AddMonoidHom.mk' (adeleLmat (Module.finBasis K L)) (adeleLmat_add K L)) f s

/-- **The determinant of $M(y)$ is the product of the conjugates**:
$\iota(\det M(y)) = \prod_\sigma\sigma(y)$. -/
theorem adeleMap_det_adeleLmat (y : Adeles L) :
    adeleMap K L (adeleLmat (Module.finBasis K L) y).det = ∏ σ : Gal(L/K), galAdeleFun σ y := by
  set a := (adeleBaseChange (Module.finBasis K L)).symm y
  have hM : adeleLmat (Module.finBasis K L) y = Matrix.of fun i k => ∑ j, diagRing K
      (Algebra.leftMulMatrix (Module.finBasis K L) (Module.finBasis K L j) i k) * a j := by
    conv_lhs => rw [adele_expand K y]
    rw [adeleLmat_sum]
    simp_rw [adeleLmat_mul, adeleLmat_adeleMap, adeleLmat_diag]
    refine Matrix.ext fun i k => ?_
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    rfl
  rw [hM, RingHom.map_det]
  have h := det_eq_prod K L (diagRing L) (fun j => adeleMap K L (a j))
  simp only [galAdeleFun_eq]
  rw [← h]
  congr 1
  refine Matrix.ext fun i k => ?_
  simp [map_sum, adeleMap_diagRing]

/-- `ideleIncl_ideleNorm` for `ideleRelNorm` of the basis `Module.finBasis K L`. -/
theorem ideleIncl_ideleRelNorm (x : IdeleGroup (𝓞 L) L) :
    ideleIncl K L (ideleRelNorm (Module.finBasis K L) x) = ∏ σ : Gal(L/K), σ • x := by
  apply (ideleGroupEquiv L).injective
  rw [ideleGroupEquiv_ideleIncl, ideleGroupEquiv_ideleRelNorm, map_prod]
  refine Units.ext ?_
  rw [Units.coe_prod]
  show adeleMap K L (adeleLmat (Module.finBasis K L) ((ideleGroupEquiv L x : (Adeles L)ˣ) : Adeles L)).det = _
  rw [adeleMap_det_adeleLmat]
  refine Finset.prod_congr rfl fun σ _ => ?_
  show _ = adeleRingEquiv L ((σ • x : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L)
  rw [val_smul_idele, adeleRingEquiv_smul]
  rfl

end Aux2

/-- The norm of ideles is the norm of the $G$-module $\mathbb I_L$ (Milne, *CFT*, Chapter VII, p. 206):
$\iota(\mathrm{Nm}_{L/K}x) = \prod_{\sigma\in G}\sigma x$. -/
theorem ideleIncl_ideleNorm (x : IdeleGroup (𝓞 L) L) :
    ideleIncl K L (ideleNorm K L x) = ∏ σ : Gal(L/K), σ • x :=
  ideleIncl_ideleRelNorm K L x

omit [IsGalois K L] in
/-- $\iota$ maps the principal idele of $\xi\in K^\times$ to that of $\xi\in L^\times$. -/
theorem ideleIncl_unitEmbedding (ξ : Kˣ) :
    ideleIncl K L (IdeleGroup.unitEmbedding (𝓞 K) K ξ) =
      IdeleGroup.unitEmbedding (𝓞 L) L (Units.map (algebraMap K L : K →* L) ξ) := by
  apply (NumberFieldKB.Ideles.ideleGroupEquiv L).injective
  rw [ideleGroupEquiv_ideleIncl, NumberFieldKB.Ideles.ideleGroupEquiv_unitEmbedding,
    NumberFieldKB.Ideles.ideleGroupEquiv_unitEmbedding]
  exact Units.ext (adeleMap_diagRing K L ξ)

omit [IsGalois K L] in
theorem principalSubgroup_le_comap_ideleIncl :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤ (IdeleGroup.principalSubgroup (𝓞 L) L).comap (ideleIncl K L) := by
  rintro _ ⟨ξ, rfl⟩
  exact ⟨_, (ideleIncl_unitEmbedding K L ξ).symm⟩

/-- The map $C_K\to C_L$ induced by $\mathbb I_K\hookrightarrow\mathbb I_L$. -/
def ideleClassIncl : IdeleClassGroup (𝓞 K) K →* IdeleClassGroup (𝓞 L) L :=
  QuotientGroup.map _ _ (ideleIncl K L) (principalSubgroup_le_comap_ideleIncl K L)

section Aux3

open QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.Ideles

omit [IsGalois K L] in
/-- Principal ideles determine the field element. -/
theorem unitEmbedding_injective_L : Function.Injective (IdeleGroup.unitEmbedding (𝓞 L) L) := by
  intro ξ ξ' h
  apply Units.ext
  have h1 := congrArg (fun u : IdeleGroup (𝓞 L) L => adeleRingEquiv L (u : AdeleRing (𝓞 L) L)) h
  change adeleRingEquiv L (algebraMap L (AdeleRing (𝓞 L) L) ξ) =
    adeleRingEquiv L (algebraMap L (AdeleRing (𝓞 L) L) ξ') at h1
  rw [adeleRingEquiv_algebraMap, adeleRingEquiv_algebraMap] at h1
  exact (diagRing L).injective h1

/-- A unit of $L$ whose principal idele is $G$-fixed comes from $K^\times$. -/
theorem exists_unit_of_fixed (ξ : Lˣ) (h : ∀ σ : Gal(L/K),
    σ • IdeleGroup.unitEmbedding (𝓞 L) L ξ = IdeleGroup.unitEmbedding (𝓞 L) L ξ) :
    ∃ η : Kˣ, Units.map (algebraMap K L : K →* L) η = ξ := by
  have hfix : ∀ σ : Gal(L/K), σ (ξ : L) = ξ := fun σ => by
    have h1 := h σ
    rw [smul_unitEmbedding] at h1
    exact congrArg Units.val (unitEmbedding_injective_L L h1)
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) (ξ : L)).2 hfix
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact ξ.ne_zero hk.symm
  exact ⟨Units.mk0 k hk0, Units.ext hk⟩

/-- Lemma 4.1, injectivity. -/
theorem ideleClassIncl_injective : Function.Injective (ideleClassIncl K L) := by
  intro a b
  refine QuotientGroup.induction_on a fun x => QuotientGroup.induction_on b fun x' => ?_
  intro hab
  have h1 : (ideleIncl K L x)⁻¹ * ideleIncl K L x' ∈ IdeleGroup.principalSubgroup (𝓞 L) L :=
    QuotientGroup.eq.1 hab
  obtain ⟨ξ, hξ⟩ := h1
  have hfix : ∀ σ : Gal(L/K), σ • IdeleGroup.unitEmbedding (𝓞 L) L ξ =
      IdeleGroup.unitEmbedding (𝓞 L) L ξ := fun σ => by
    have := smul_ideleIncl σ (x⁻¹ * x')
    rw [map_mul, map_inv] at this
    rw [hξ]
    exact this
  obtain ⟨η, rfl⟩ := exists_unit_of_fixed K L ξ hfix
  have h2 : ideleIncl K L (x⁻¹ * x') = ideleIncl K L (IdeleGroup.unitEmbedding (𝓞 K) K η) := by
    rw [map_mul, map_inv, ideleIncl_unitEmbedding]
    exact hξ.symm
  have h3 := (prop_2_5a K L).1 h2
  exact QuotientGroup.eq.2 ⟨η, h3.symm⟩

/-- Lemma 4.1, the image is the fixed classes (Hilbert 90). -/
theorem mem_range_ideleClassIncl_of_fixed (c : IdeleClassGroup (𝓞 L) L) (hc : ∀ σ : Gal(L/K), σ • c = c) :
    c ∈ (ideleClassIncl K L).range := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  have hf : ∀ σ : Gal(L/K), ∃ ξ : Lˣ, IdeleGroup.unitEmbedding (𝓞 L) L ξ = y⁻¹ * σ • y := fun σ => by
    have h1 := hc σ
    rw [smul_mk] at h1
    exact QuotientGroup.eq.1 h1.symm
  choose f hf using hf
  have h2 : ∀ σ : Gal(L/K), σ • y = y * IdeleGroup.unitEmbedding (𝓞 L) L (f σ) := fun σ => by
    rw [hf σ]; exact (mul_inv_cancel_left y _).symm
  have hcoc : groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    apply unitEmbedding_injective_L L
    calc IdeleGroup.unitEmbedding (𝓞 L) L (f (σ * τ)) = y⁻¹ * (σ • (τ • y)) := by rw [hf, mul_smul]
      _ = y⁻¹ * (σ • (y * IdeleGroup.unitEmbedding (𝓞 L) L (f τ))) := by rw [h2 τ]
      _ = y⁻¹ * (σ • y * σ • IdeleGroup.unitEmbedding (𝓞 L) L (f τ)) := by rw [smul_mul']
      _ = y⁻¹ * (y * IdeleGroup.unitEmbedding (𝓞 L) L (f σ) * σ • IdeleGroup.unitEmbedding (𝓞 L) L (f τ)) := by
        rw [h2 σ]
      _ = IdeleGroup.unitEmbedding (𝓞 L) L (f σ) *
          IdeleGroup.unitEmbedding (𝓞 L) L (Units.map (σ : L →* L) (f τ)) := by
        rw [smul_unitEmbedding]; group
      _ = IdeleGroup.unitEmbedding (𝓞 L) L (σ • f τ * f σ) := by
        rw [AlgEquiv.smul_units_def, map_mul, mul_comm]
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hcoc
  have hfixed : ∀ σ : Gal(L/K), σ • (y * IdeleGroup.unitEmbedding (𝓞 L) L β⁻¹) =
      y * IdeleGroup.unitEmbedding (𝓞 L) L β⁻¹ := fun σ => by
    rw [smul_mul', h2 σ, mul_assoc, smul_unitEmbedding, ← map_mul]
    congr 2
    rw [← hβ σ, AlgEquiv.smul_units_def, map_inv, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]
  obtain ⟨x, hx⟩ := ((prop_2_5a K L).2 _).1 hfixed
  refine ⟨QuotientGroup.mk x, ?_⟩
  show QuotientGroup.mk (ideleIncl K L x) = QuotientGroup.mk y
  rw [hx]
  refine QuotientGroup.eq.2 ⟨β, ?_⟩
  rw [mul_inv_rev, map_inv, inv_inv]
  group

end Aux3

/-- **Lemma 4.1** (Milne, *CFT*, Chapter VII, p. 210): the map $C_K\to C_L$ induced by $\mathbb I_K\hookrightarrow
\mathbb I_L$ is injective with image $C_L^G$. -/
@[kb "milne2020cft" "Ch. VII, Lemma 4.1"]
theorem lemma_4_1 :
    Function.Injective (ideleClassIncl K L) ∧
      ∀ c : IdeleClassGroup (𝓞 L) L, (∀ σ : Gal(L/K), σ • c = c) ↔ c ∈ (ideleClassIncl K L).range := by
  refine ⟨ideleClassIncl_injective K L, fun c => ⟨mem_range_ideleClassIncl_of_fixed K L c, ?_⟩⟩
  rintro ⟨a, rfl⟩ σ
  refine QuotientGroup.induction_on a fun x => ?_
  exact congrArg QuotientGroup.mk (smul_ideleIncl σ x)

section TateZero

variable (G A : Type) [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]

/-- The $G$-invariants $A^G$ of a multiplicative $G$-module. -/
def invSub : Subgroup A where
  carrier := {a | ∀ g : G, g • a = a}
  mul_mem' := by
    intro a b ha hb g
    rw [smul_mul', ha g, hb g]
  one_mem' := fun g => smul_one g
  inv_mem' := by
    intro a ha g
    rw [smul_inv', ha g]

/-- The norm $a\mapsto\prod_{g\in G}g\cdot a$. -/
def normHomG : A →* A where
  toFun a := ∏ g : G, g • a
  map_one' := by simp
  map_mul' a b := by simp [smul_mul', Finset.prod_mul_distrib]

theorem normHomG_mem_invSub (a : A) : normHomG G A a ∈ invSub G A := by
  intro g
  show g • ∏ h : G, h • a = ∏ h : G, h • a
  rw [← MulDistribMulAction.toMonoidHom_apply, map_prod]
  simp only [MulDistribMulAction.toMonoidHom_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun _ => rfl

/-- The $G$-norms inside the $G$-invariants. -/
def normSubG : Subgroup (invSub G A) :=
  (normHomG G A).range.subgroupOf (invSub G A)

theorem tate_zero_card :
    Nat.card (tateCohomology (Rep.ofMulDistribMulAction G A) 0) =
      Nat.card (invSub G A ⧸ normSubG G A) := by
  classical
  let M : Rep ℤ G := Rep.ofMulDistribMulAction G A
  let S := (tateComplex M).sc' (-1) 0 1
  let e1 : tateCohomology M 0 ≅ S.homology :=
    (tateComplex M).homologyIsoSc' (-1) 0 1 (by simp) (by simp)
  let e : tateCohomology M 0 ≃ₗ[ℤ] (↥(LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles) :=
    (e1 ≪≫ S.moduleCatHomologyIso).toLinearEquiv
  let ev : S.X₂ → A := fun f => Additive.toMul (show Additive A from f default)
  have key : ∀ (f : S.X₂) (x : Fin 1 → G), (S.g.hom f) x = M.ρ (x 0) (f default) - f default := by
    intro f x
    show M.ρ (x 0) (f fun i => x i.succ) + ∑ j : Fin 1, (-1 : ℤ) ^ ((j : ℕ) + 1) •
      f (Fin.contractNth j (· * ·) x) = _
    simp [Subsingleton.elim _ (default : Fin 0 → G)]
    exact (sub_eq_add_neg _ _).symm
  have hg : ∀ f : S.X₂, S.g.hom f = 0 ↔ ∀ g : G, g • ev f = ev f := by
    intro f
    constructor
    · intro h g
      have h1 : M.ρ g (f default) - f default = (0 : Additive A) :=
        (key f (fun _ => g)).symm.trans (congrFun h (fun _ => g))
      exact congrArg Additive.toMul (sub_eq_zero.1 h1)
    · intro h
      funext x
      exact (key f x).trans (sub_eq_zero.2 (congrArg Additive.ofMul (h (x 0))))
  let c0 : S.X₁ → M := fun c => (show (Fin 0 → G) →₀ M from c) default
  have hf : ∀ c : S.X₁, S.f.hom c = fun _ => M.ρ.norm (c0 c) := by
    intro c
    show M.tateNorm.hom c = _
    rw [Rep.tateNorm_eq]
    let c' : (Fin 0 → G) →₀ M := c
    funext x
    change Finsupp.sum c' (fun _ => ⇑(LinearMap.pi fun _ : Fin 0 → G => M.ρ.norm)) x = M.ρ.norm (c' default)
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_unique]
    simp [Subsingleton.elim x default]
  have hnorm : ∀ a : A, ev (fun _ => Additive.ofMul a) = a := fun a => rfl
  have hnorm' : ∀ c : S.X₁, ev (S.f.hom c) = normHomG G A (Additive.toMul (c0 c)) := by
    intro c
    show Additive.toMul (S.f.hom c default) = _
    rw [hf]
    exact Representation.norm_ofMulDistribMulAction_eq (G := G) (M := A) _
  let ψ0 : ↥(LinearMap.ker S.g.hom) →+ Additive (↥(invSub G A) ⧸ normSubG G A) :=
    { toFun := fun f => Additive.ofMul (QuotientGroup.mk ⟨ev f.1, (hg f.1).1 f.2⟩)
      map_zero' := by
        show Additive.ofMul (QuotientGroup.mk _) = 0
        have : (⟨ev (0 : ↥(LinearMap.ker S.g.hom)).1, (hg _).1 (0 : ↥(LinearMap.ker S.g.hom)).2⟩ :
            invSub G A) = 1 := Subtype.ext rfl
        rw [this, QuotientGroup.mk_one]
        rfl
      map_add' := by
        intro f g
        show Additive.ofMul (QuotientGroup.mk _) = Additive.ofMul (QuotientGroup.mk _) +
          Additive.ofMul (QuotientGroup.mk _)
        rw [← ofMul_mul, ← QuotientGroup.mk_mul]
        rfl }
  have hev_inj : ∀ g1 g2 : S.X₂, ev g1 = ev g2 → g1 = g2 := by
    intro g1 g2 h
    funext x
    rw [Subsingleton.elim x default]
    exact Additive.toMul.injective h
  have hsurj : Function.Surjective ψ0 := by
    intro q
    obtain ⟨a', ha'⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    refine ⟨⟨fun _ => Additive.ofMul a'.1, (hg _).2 (fun g => a'.2 g)⟩, ?_⟩
    exact (congrArg (fun z : invSub G A => Additive.ofMul
      (QuotientGroup.mk z : ↥(invSub G A) ⧸ normSubG G A)) (Subtype.ext rfl : _ = a')).trans
      (by rw [ha']; rfl)
  have hker : ψ0.ker = (LinearMap.range S.moduleCatToCycles).toAddSubgroup := by
    ext f
    rw [AddMonoidHom.mem_ker]
    show ψ0 f = 0 ↔ ∃ c, S.moduleCatToCycles c = f
    constructor
    · intro h
      have h1 : (QuotientGroup.mk (⟨ev f.1, (hg f.1).1 f.2⟩ : invSub G A) :
          ↥(invSub G A) ⧸ normSubG G A) = 1 := h
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨a, ha⟩ := (Subgroup.mem_subgroupOf.1 h1)
      let c : S.X₁ := show S.X₁ from
        (Finsupp.single (default : Fin 0 → G) (show M from Additive.ofMul a) : (Fin 0 → G) →₀ M)
      refine ⟨c, Subtype.ext (hev_inj _ _ ?_)⟩
      exact ((hnorm' c).trans (congrArg (normHomG G A) (by
        show Additive.toMul ((Finsupp.single (default : Fin 0 → G) (Additive.ofMul a) :
          (Fin 0 → G) →₀ Additive A) default) = a
        rw [Finsupp.single_eq_same]
        rfl))).trans ha
    · rintro ⟨c, rfl⟩
      show (Additive.ofMul (QuotientGroup.mk _) : Additive (↥(invSub G A) ⧸ normSubG G A)) = 0
      apply congrArg Additive.ofMul
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 ⟨Additive.toMul (c0 c), (hnorm' c).symm⟩)
  have hcard : Nat.card (↥(LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles) =
      Nat.card (invSub G A ⧸ normSubG G A) :=
    Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hker.symm).toEquiv.trans
      ((QuotientAddGroup.quotientKerEquivOfSurjective ψ0 hsurj).toEquiv.trans Additive.toMul))
  exact (Nat.card_congr e.toEquiv).trans hcard

end TateZero

/-- $H^0_T(G, C_L) = C_L^G/\mathrm{Nm}_G(C_L)\cong C_K/\mathrm{Nm}(C_L)\cong\mathbb I_K/K^\times\mathrm{Nm}(\mathbb I_L)$
(Milne, *CFT*, Chapter VII, Lemma 4.1 and p. 207): the two groups have the same cardinality. -/
theorem card_tateZero_ideleClassRep :
    Nat.card (tateCohomology (ideleClassRep K L) 0) = (principalNormIdeles K L).index := by
  refine (tate_zero_card Gal(L/K) (IdeleClassGroup (𝓞 L) L)).trans ?_
  let f : IdeleGroup (𝓞 K) K →* invSub Gal(L/K) (IdeleClassGroup (𝓞 L) L) :=
    ((ideleClassIncl K L).comp (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))).codRestrict _
      (fun x => ((lemma_4_1 K L).2 _).2 ⟨QuotientGroup.mk x, rfl⟩)
  have hsurj : Function.Surjective f := by
    rintro ⟨c, hc⟩
    obtain ⟨a, rfl⟩ := ((lemma_4_1 K L).2 c).1 hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨x, rfl⟩
  have hprod : ∀ z : IdeleGroup (𝓞 L) L, ∏ σ : Gal(L/K), σ • (QuotientGroup.mk z : IdeleClassGroup (𝓞 L) L) =
      QuotientGroup.mk (∏ σ : Gal(L/K), σ • z) := fun z =>
    (QuotientGroup.mk_prod (IdeleGroup.principalSubgroup (𝓞 L) L) Finset.univ
      (f := fun σ : Gal(L/K) => σ • z)).symm
  have hcomap : (normSubG Gal(L/K) (IdeleClassGroup (𝓞 L) L)).comap f = principalNormIdeles K L := by
    ext x
    rw [Subgroup.mem_comap, normSubG, Subgroup.mem_subgroupOf]
    unfold principalNormIdeles normIdeles
    rw [Subgroup.mem_sup]
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective c
      have h1 : ideleClassIncl K L (QuotientGroup.mk (ideleNorm K L z)) =
          ideleClassIncl K L (QuotientGroup.mk x) := by
        calc ideleClassIncl K L (QuotientGroup.mk (ideleNorm K L z))
            = QuotientGroup.mk (∏ σ : Gal(L/K), σ • z) := by
              show QuotientGroup.mk (ideleIncl K L (ideleNorm K L z)) = _
              rw [ideleIncl_ideleNorm]
          _ = ∏ σ : Gal(L/K), σ • (QuotientGroup.mk z : IdeleClassGroup (𝓞 L) L) := (hprod z).symm
          _ = ideleClassIncl K L (QuotientGroup.mk x) := hc
      obtain ⟨η, hη⟩ := QuotientGroup.eq.1 (ideleClassIncl_injective K L h1)
      exact ⟨IdeleGroup.unitEmbedding (𝓞 K) K η, ⟨η, rfl⟩, ideleNorm K L z, ⟨z, rfl⟩, by
        rw [hη, mul_right_comm, inv_mul_cancel, one_mul]⟩
    · rintro ⟨p, ⟨η, rfl⟩, n, ⟨z, rfl⟩, rfl⟩
      refine ⟨QuotientGroup.mk z, ?_⟩
      show ∏ σ : Gal(L/K), σ • (QuotientGroup.mk z : IdeleClassGroup (𝓞 L) L) =
        QuotientGroup.mk (ideleIncl K L (IdeleGroup.unitEmbedding (𝓞 K) K η * ideleNorm K L z))
      rw [hprod, ← ideleIncl_ideleNorm]
      refine QuotientGroup.eq.2 ⟨Units.map (algebraMap K L : K →* L) η, ?_⟩
      rw [map_mul, ideleIncl_unitEmbedding, mul_comm (IdeleGroup.unitEmbedding (𝓞 L) L _),
        inv_mul_cancel_left]
  rw [← hcomap, Subgroup.index_comap_of_surjective _ hsurj]
  rfl

end NumberFieldKB.MilneCFT.Ch7
