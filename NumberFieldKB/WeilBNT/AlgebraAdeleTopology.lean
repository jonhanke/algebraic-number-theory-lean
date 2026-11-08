import NumberFieldKB.WeilBNT.AlgebraIdeles
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicMinkowski
import QuadFormsKB.Tamagawa.Measure.Weil.Ideles

/-!
# The adele ring of a finite-dimensional algebra: topology, Haar measure, the discrete subring

Notation as in `NumberFieldKB.WeilBNT.AlgebraIdeles`: $k$ a number field (`F`), $\mathcal A$ a finite-dimensional
$k$-algebra, $\mathcal A_{\mathbb A}=k_{\mathbb A}\otimes_k\mathcal A$. This file gives $\mathcal A_{\mathbb A}$ the
topology of $k_{\mathbb A}^n$ through the coordinates of the basis `Module.finBasis F A` (`algAdeleTop`, a local
instance; Weil IV.1 Prop. 1 makes $E_{\mathbb A}$ a product of copies of $k_{\mathbb A}$ in any basis), and proves the
facts used in Weil IV.3 Thm. 4:

* `coordsHomeo`: the coordinates are a homeomorphism onto $k_{\mathbb A}^n$; `continuous_mul_algAdele`,
  `t2Space_algAdele`: $\mathcal A_{\mathbb A}$ is a Hausdorff topological ring;
* `coords_tmul`: the coordinates of $1\otimes a$, $a\in\mathcal A$, are the diagonal image of those of $a$, so
  $\mathcal A$ is discrete in $\mathcal A_{\mathbb A}$ (`finite_inter_isCompact`: it meets every compact set in a
  finite set);
* `algVol S` $=\mu(\text{coordinates of }S)$, the Haar measure with $\mathrm{vol}(\mathcal A_{\mathbb A}/\mathcal A)=1$
  (QuadFormsKB `addCovolume_muAddVec`); `algVol_mul_right`, `algVol_mul_left`: the modules of $x\mapsto xd$ and
  $x\mapsto dx$ (Cor. of Prop. 3 and text p. 74); `exists_isCompact_algVol_gt`; `algBlichfeldt` (Weil II.4 Lemma 1:
  a set of volume $>1$ contains two points whose difference is a nonzero element of $\mathcal A$);
* `modL`, `modR`: the modules $\lvert N(d)\rvert_{\mathbb A}$, $\lvert N'(d)\rvert_{\mathbb A}$ on the units, continuous
  for the topology of Weil's Def. 2 (Mathlib's topology on units, $x\mapsto(x,x^{-1})$), multiplicative, and $1$ on
  $\mathcal A^\times$ (product formula).
-/

open IsDedekindDomain NumberField MeasureTheory QuadFormsKB.Tamagawa.Measure.Weil Topology
open scoped TensorProduct Pointwise

noncomputable section

namespace NumberFieldKB.WeilBNT

attribute [local instance] adelesAlgebra

variable {F : Type} [Field F] [NumberField F] {A : Type} [Ring A] [Algebra F A] [FiniteDimensional F A]

variable (F A) in
/-- The index type of the standard basis of $\mathcal A$. -/
abbrev AIdx : Type := Fin (Module.finrank F A)

variable (F A) in
/-- The coordinates $\mathcal A_{\mathbb A}\cong k_{\mathbb A}^n$ in the basis `Module.finBasis F A`. -/
def coordsA : (Adeles F ⊗[F] A) ≃ₗ[Adeles F] (AIdx F A → Adeles F) := algCoords (Module.finBasis F A)

variable (F A) in
/-- The topology of $\mathcal A_{\mathbb A}$: that of $k_{\mathbb A}^n$ through `coordsA`. -/
abbrev algAdeleTop : TopologicalSpace (Adeles F ⊗[F] A) := TopologicalSpace.induced (coordsA F A) inferInstance

attribute [local instance] algAdeleTop

variable (F A) in
/-- The coordinates as a homeomorphism. -/
def coordsHomeo : (Adeles F ⊗[F] A) ≃ₜ (AIdx F A → Adeles F) :=
  (coordsA F A).toEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

theorem coordsHomeo_apply (x : Adeles F ⊗[F] A) : coordsHomeo F A x = coordsA F A x := rfl

theorem continuous_coordsA : Continuous (coordsA F A) := continuous_induced_dom

theorem coordsA_mul (x y : Adeles F ⊗[F] A) :
    coordsA F A (x * y) = ∑ i, coordsA F A x i •
      (Algebra.leftMulMatrix (algAdelesBasis (Module.finBasis F A))
        (algAdelesBasis (Module.finBasis F A) i)).mulVec (coordsA F A y) := by
  have hx : x = ∑ i, coordsA F A x i • algAdelesBasis (Module.finBasis F A) i :=
    ((algAdelesBasis (Module.finBasis F A)).sum_repr x).symm
  conv_lhs => rw [hx]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, map_smul]
  congr 1
  have := algCoords_mul (Module.finBasis F A) (algAdelesBasis (Module.finBasis F A) i) (coordsA F A y)
  rw [← this]
  congr 2
  exact ((algCoords (Module.finBasis F A)).symm_apply_apply y).symm

theorem continuous_mul_algAdele : ContinuousMul (Adeles F ⊗[F] A) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  have : (coordsA F A ∘ fun p : (Adeles F ⊗[F] A) × (Adeles F ⊗[F] A) => p.1 * p.2) = fun p =>
      ∑ i, coordsA F A p.1 i • (Algebra.leftMulMatrix (algAdelesBasis (Module.finBasis F A))
        (algAdelesBasis (Module.finBasis F A) i)).mulVec (coordsA F A p.2) := funext fun p => coordsA_mul _ _
  rw [this]
  refine continuous_finsetSum _ fun i _ => ?_
  have h1 : Continuous fun p : (Adeles F ⊗[F] A) × (Adeles F ⊗[F] A) => coordsA F A p.1 i :=
    (continuous_apply i).comp (continuous_coordsA.comp continuous_fst)
  have h2 : Continuous fun p : (Adeles F ⊗[F] A) × (Adeles F ⊗[F] A) =>
      (Algebra.leftMulMatrix (algAdelesBasis (Module.finBasis F A))
        (algAdelesBasis (Module.finBasis F A) i)).mulVec (coordsA F A p.2) :=
    Continuous.matrix_mulVec continuous_const (continuous_coordsA.comp continuous_snd)
  exact h1.smul h2

theorem continuous_add_algAdele : ContinuousAdd (Adeles F ⊗[F] A) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  have : (coordsA F A ∘ fun p : (Adeles F ⊗[F] A) × (Adeles F ⊗[F] A) => p.1 + p.2) = fun p =>
      coordsA F A p.1 + coordsA F A p.2 := funext fun p => map_add _ _ _
  rw [this]
  exact (continuous_coordsA.comp continuous_fst).add (continuous_coordsA.comp continuous_snd)

theorem t2Space_adeles : T2Space (Adeles F) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), T2Space (v.adicCompletion F) := fun v => by
    have : T0Space (v.adicCompletion F) := inferInstance
    infer_instance
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    .of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  exact inferInstanceAs (T2Space (_ × FiniteAdeleRing (𝓞 F) F))

theorem t2Space_algAdele : T2Space (Adeles F ⊗[F] A) := by
  have := t2Space_adeles (F := F)
  exact (coordsHomeo F A).isEmbedding.t2Space

/-- The coordinates of $1\otimes a$ are the diagonal image of the coordinates of $a$. -/
theorem coords_tmul (a : A) :
    coordsA F A ((1 : Adeles F) ⊗ₜ[F] a) = diagVec F (AIdx F A) ((Module.finBasis F A).equivFun a) := by
  funext i
  show (algAdelesBasis (Module.finBasis F A)).repr ((1 : Adeles F) ⊗ₜ[F] a) i = _
  simp only [algAdelesBasis, Algebra.TensorProduct.basis_repr_tmul]
  simp [Algebra.smul_def]
  rfl

attribute [local instance] continuous_mul_algAdele continuous_add_algAdele t2Space_algAdele t2Space_adeles

/-- $\mathcal A$ meets every compact subset of $\mathcal A_{\mathbb A}$ in a finite set. -/
theorem finite_inter_isCompact {C : Set (Adeles F ⊗[F] A)} (hC : IsCompact C) :
    {a : A | (1 : Adeles F) ⊗ₜ[F] a ∈ C}.Finite := by
  have hK : IsCompact (coordsA F A '' C) := hC.image continuous_coordsA
  haveI := discreteTopology_diagVecSub (F := F) (ι := AIdx F A)
  have hcl : IsClosed (diagVecSub F (AIdx F A) : Set (AIdx F A → Adeles F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  have hfin : (coordsA F A '' C ∩ (diagVecSub F (AIdx F A) : Set (AIdx F A → Adeles F))).Finite := by
    have hc := hK.inter_right hcl
    haveI : DiscreteTopology (coordsA F A '' C ∩ (diagVecSub F (AIdx F A) : Set (AIdx F A → Adeles F)) :
        Set (AIdx F A → Adeles F)) :=
      DiscreteTopology.of_subset (s := (diagVecSub F (AIdx F A) : Set (AIdx F A → Adeles F)))
        (inferInstanceAs (DiscreteTopology (diagVecSub F (AIdx F A)))) Set.inter_subset_right
    exact hc.finite (isDiscrete_iff_discreteTopology.2 inferInstance)
  have hinj : Function.Injective fun a : A => diagVec F (AIdx F A) ((Module.finBasis F A).equivFun a) :=
    diagVec_injective.comp (Module.finBasis F A).equivFun.injective
  refine Set.Finite.of_finite_image (f := fun a : A => diagVec F (AIdx F A) ((Module.finBasis F A).equivFun a))
    (hfin.subset ?_) hinj.injOn
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨⟨_, ha, coords_tmul a⟩, ⟨_, rfl⟩⟩

variable (F A) in
/-- The Haar measure of a subset of $\mathcal A_{\mathbb A}$: that of its coordinates. -/
def algVol (S : Set (Adeles F ⊗[F] A)) : ENNReal := muAddVec F (AIdx F A) (coordsA F A '' S)

theorem coordsA_eq : coordsA F A = algCoords (Module.finBasis F A) := rfl

theorem coregularNorm_mul (x y : Adeles F ⊗[F] A) :
    coregularNorm (x * y) = coregularNorm x * coregularNorm y := by
  unfold coregularNorm
  have : LinearMap.mulRight (Adeles F) (x * y) =
      (LinearMap.mulRight (Adeles F) y).comp (LinearMap.mulRight (Adeles F) x) := by
    ext z; simp [mul_assoc]
  rw [this, LinearMap.det_comp, mul_comm]

theorem coregularNorm_one : coregularNorm (1 : Adeles F ⊗[F] A) = 1 := by
  unfold coregularNorm
  rw [LinearMap.mulRight_one]
  exact LinearMap.det_id

theorem vol_image_of_map {ι : Type} [Fintype ι] {g h : AdeleSpace F ι → AdeleSpace F ι}
    (hgh : Function.LeftInverse h g) (hhg : Function.RightInverse h g) (hh : Measurable h)
    {c : ENNReal} (hmap : Measure.map h (muAddVec F ι) = c • muAddVec F ι)
    {T : Set (AdeleSpace F ι)} (hT : MeasurableSet T) :
    muAddVec F ι (g '' T) = c * muAddVec F ι T := by
  rw [Set.image_eq_preimage_of_inverse hgh hhg, ← Measure.map_apply hh hT, hmap]
  rfl

theorem measurable_mulRightCoords (e : Adeles F ⊗[F] A) :
    Measurable fun y : AIdx F A → Adeles F => coordsA F A ((coordsA F A).symm y * e) := by
  refine Continuous.measurable ?_
  exact (coordsHomeo F A).continuous.comp ((coordsHomeo F A).symm.continuous.mul continuous_const)

theorem measurable_mulLeftCoords (e : Adeles F ⊗[F] A) :
    Measurable fun y : AIdx F A → Adeles F => coordsA F A (e * (coordsA F A).symm y) := by
  refine Continuous.measurable ?_
  exact (coordsHomeo F A).continuous.comp (continuous_const.mul (coordsHomeo F A).symm.continuous)

/-- The module of $x\mapsto xd$ is $\lvert N'(d)\rvert_{\mathbb A}$: $\mathrm{vol}(Sd)=\lvert N'(d)\rvert\mathrm{vol}(S)$
for a measurable (e.g. compact) $S$. -/
theorem algVol_mul_right (d : (Adeles F ⊗[F] A)ˣ) (hd : IsUnit (coregularNorm (d : Adeles F ⊗[F] A)))
    {S : Set (Adeles F ⊗[F] A)} (hS : MeasurableSet (coordsA F A '' S)) :
    algVol F A ((fun x => x * (d : Adeles F ⊗[F] A)) '' S) = ENNReal.ofReal (ideleNorm F hd.unit) * algVol F A S := by
  have hd' : IsUnit (coregularNorm ((d⁻¹ : (Adeles F ⊗[F] A)ˣ) : Adeles F ⊗[F] A)) :=
    (weil_IV_3_coregular_iff _).1 (Units.isUnit _)
  have hu : hd'.unit = hd.unit⁻¹ := by
    refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
    simp only [Units.val_mul, IsUnit.unit_spec, Units.val_one]
    rw [← coregularNorm_mul, Units.inv_mul, coregularNorm_one]
  have hmap := weil_IV_3_coregular_module (Module.finBasis F A) d⁻¹ hd'
  rw [hu, ideleNorm_inv, inv_inv, ← coordsA_eq] at hmap
  have himg : coordsA F A '' ((fun x => x * (d : Adeles F ⊗[F] A)) '' S) =
      (fun y => coordsA F A ((coordsA F A).symm y * (d : Adeles F ⊗[F] A))) '' (coordsA F A '' S) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun x _ => by simp
  unfold algVol
  rw [himg]
  refine vol_image_of_map (h := fun y => coordsA F A ((coordsA F A).symm y * ((d⁻¹ : (Adeles F ⊗[F] A)ˣ) : Adeles F ⊗[F] A)))
    ?_ ?_ (measurable_mulRightCoords _) hmap hS
  · intro y; simp [mul_assoc]
  · intro y; simp [mul_assoc]

/-- The module of $x\mapsto dx$ is $\lvert N(d)\rvert_{\mathbb A}$. -/
theorem algVol_mul_left (d : (Adeles F ⊗[F] A)ˣ) {S : Set (Adeles F ⊗[F] A)}
    (hS : MeasurableSet (coordsA F A '' S)) :
    algVol F A ((fun x => (d : Adeles F ⊗[F] A) * x) '' S) =
      ENNReal.ofReal (ideleNorm F (Units.map (Algebra.norm (Adeles F)) d)) * algVol F A S := by
  have hmap := weil_IV_3_prop3_cor_module (Module.finBasis F A) d⁻¹
  rw [map_inv, ideleNorm_inv, inv_inv, ← coordsA_eq] at hmap
  have himg : coordsA F A '' ((fun x => (d : Adeles F ⊗[F] A) * x) '' S) =
      (fun y => coordsA F A ((d : Adeles F ⊗[F] A) * (coordsA F A).symm y)) '' (coordsA F A '' S) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun x _ => by simp
  unfold algVol
  rw [himg]
  refine vol_image_of_map (h := fun y => coordsA F A (((d⁻¹ : (Adeles F ⊗[F] A)ˣ) : Adeles F ⊗[F] A) * (coordsA F A).symm y))
    ?_ ?_ (measurable_mulLeftCoords _) hmap hS
  · intro y; simp [← mul_assoc]
  · intro y; simp [← mul_assoc]

/-- $\mathcal A_{\mathbb A}$ has compact subsets of arbitrarily large volume (it is not compact), when
$\mathcal A\ne0$. -/
theorem exists_isCompact_algVol_gt [Nontrivial A] (r : ENNReal) (hr : r ≠ ⊤) :
    ∃ C : Set (Adeles F ⊗[F] A), IsCompact C ∧ r < algVol F A C := by
  have hpos : 0 < Module.finrank F A := Module.finrank_pos
  haveI : Nonempty (AIdx F A) := ⟨⟨0, hpos⟩⟩
  haveI : Infinite (diagVecSub F (AIdx F A)) :=
    Infinite.of_injective (fun ξ : AIdx F A → F => (⟨diagVec F (AIdx F A) ξ, ξ, rfl⟩ : diagVecSub F (AIdx F A)))
      (fun ξ η h => diagVec_injective (congrArg Subtype.val h))
  have htop : muAddVec F (AIdx F A) Set.univ = ⊤ := by
    rw [(isAddFundamentalDomain_fundDomVec (muAddVec F (AIdx F A))).measure_eq_tsum' Set.univ]
    have : ∀ g : diagVecSub F (AIdx F A),
        muAddVec F (AIdx F A) (Set.univ ∩ (g +ᵥ fundDomVec F (AIdx F A) : Set (AdeleSpace F (AIdx F A)))) = 1 := fun g => by
      rw [Set.univ_inter, measure_vadd (muAddVec F (AIdx F A)) g, muAddVec_fundDomVec]
    simp_rw [this]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  obtain ⟨K, -, hK, hrK⟩ := isOpen_univ.exists_lt_isCompact
    (μ := muAddVec F (AIdx F A)) (show r < muAddVec F (AIdx F A) Set.univ by rw [htop]; exact lt_top_iff_ne_top.2 hr)
  refine ⟨(coordsHomeo F A).symm '' K, hK.image (coordsHomeo F A).symm.continuous, ?_⟩
  unfold algVol
  have : coordsA F A '' ((coordsHomeo F A).symm '' K) = K := by
    rw [Set.image_image]
    simp [← coordsHomeo_apply]
  rw [this]; exact hrK

/-- Compact sets have measurable coordinates. -/
theorem measurableSet_coords_of_isCompact {C : Set (Adeles F ⊗[F] A)} (hC : IsCompact C) :
    MeasurableSet (coordsA F A '' C) :=
  (hC.image continuous_coordsA).isClosed.measurableSet

/-- **Weil, II.4 Lemma 1** for $\mathcal A\subset\mathcal A_{\mathbb A}$ (volume of the quotient $1$): a measurable set of
volume $>1$ contains $x,y$ with $x-y=1\otimes a$, $a\in\mathcal A$, $a\ne0$. -/
theorem algBlichfeldt {S : Set (Adeles F ⊗[F] A)} (hS : MeasurableSet (coordsA F A '' S))
    (h : 1 < algVol F A S) :
    ∃ a : A, a ≠ 0 ∧ ∃ x ∈ S, ∃ y ∈ S, x - y = (1 : Adeles F) ⊗ₜ[F] a := by
  obtain ⟨ξ, hξ, u, hu, v, hv, huv⟩ := adelicBlichfeldt hS.nullMeasurableSet h
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  refine ⟨(Module.finBasis F A).equivFun.symm ξ, ?_, x, hx, y, hy, ?_⟩
  · intro h0
    apply hξ
    exact (LinearEquiv.map_eq_zero_iff _).1 h0
  · apply (coordsA F A).injective
    rw [map_sub, coords_tmul, huv, LinearEquiv.apply_symm_apply]

/-- The coregular norm $N'$ as a morphism of monoids ($N'(xy)=N'(y)N'(x)=N'(x)N'(y)$). -/
def coregularNormHom : (Adeles F ⊗[F] A) →* Adeles F where
  toFun := coregularNorm
  map_one' := coregularNorm_one
  map_mul' := coregularNorm_mul

theorem coregularNormHom_apply (x : Adeles F ⊗[F] A) : coregularNormHom x = coregularNorm x := rfl

variable (F A) in
/-- The module of $x\mapsto dx$ on $\mathcal A_{\mathbb A}$: $\lvert N(d)\rvert_{\mathbb A}$. -/
def modL (d : (Adeles F ⊗[F] A)ˣ) : ℝ := ideleNorm F (Units.map (Algebra.norm (Adeles F)) d)

variable (F A) in
/-- The module of $x\mapsto xd$ on $\mathcal A_{\mathbb A}$: $\lvert N'(d)\rvert_{\mathbb A}$. -/
def modR (d : (Adeles F ⊗[F] A)ˣ) : ℝ := ideleNorm F (Units.map coregularNormHom d)

theorem modL_mul (d e : (Adeles F ⊗[F] A)ˣ) : modL F A (d * e) = modL F A d * modL F A e := by
  unfold modL
  rw [map_mul, ideleNorm_mul]

theorem modR_mul (d e : (Adeles F ⊗[F] A)ˣ) : modR F A (d * e) = modR F A d * modR F A e := by
  unfold modR
  rw [map_mul, ideleNorm_mul]

theorem modL_pos (d : (Adeles F ⊗[F] A)ˣ) : 0 < modL F A d := ideleNorm_pos _

theorem modR_pos (d : (Adeles F ⊗[F] A)ˣ) : 0 < modR F A d := ideleNorm_pos _

/-- $\mathcal A^\times$ inside the idele group of $\mathcal A$. -/
def unitsA : (A)ˣ →* (Adeles F ⊗[F] A)ˣ := Units.map (Algebra.TensorProduct.includeRight : A →ₐ[F] Adeles F ⊗[F] A)

theorem unitsA_val (a : Aˣ) : ((unitsA a : (Adeles F ⊗[F] A)ˣ) : Adeles F ⊗[F] A) = (1 : Adeles F) ⊗ₜ[F] (a : A) := rfl

theorem coregularNorm_tmul (a : A) :
    coregularNorm ((1 : Adeles F) ⊗ₜ[F] a) = diag F (LinearMap.det (LinearMap.mulRight F a)) := by
  have h : LinearMap.mulRight (Adeles F) ((1 : Adeles F) ⊗ₜ[F] a) =
      (LinearMap.mulRight F a).baseChange (Adeles F) := by
    ext x
    simp
  rw [coregularNorm, h, LinearMap.det_baseChange]
  rfl

theorem continuous_norm_algAdele : Continuous (Algebra.norm (Adeles F) : (Adeles F ⊗[F] A) → Adeles F) := by
  refine ((weil_IV_3_prop3_cor_continuous (Module.finBasis F A)).comp (coordsHomeo F A).continuous).congr ?_
  intro x
  show _ = _
  simp only [Function.comp]
  rw [coordsHomeo_apply, coordsA_eq, LinearEquiv.symm_apply_apply]

theorem continuous_coregularNorm_algAdele : Continuous (coregularNorm : (Adeles F ⊗[F] A) → Adeles F) := by
  have h : (coregularNorm : (Adeles F ⊗[F] A) → Adeles F) = fun x =>
      Matrix.det (fun j i : AIdx F A => coordsA F A (algAdelesBasis (Module.finBasis F A) i * x) j) := by
    funext x
    unfold coregularNorm
    rw [← LinearMap.det_toMatrix (algAdelesBasis (Module.finBasis F A))]
    congr 1
    funext j i
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [h]
  refine Continuous.matrix_det (continuous_pi fun j => continuous_pi fun i => ?_)
  exact (continuous_apply j).comp (continuous_coordsA.comp (continuous_const.mul continuous_id))

/-- Product formula: $\lvert N(a)\rvert_{\mathbb A}=1$ for $a\in\mathcal A^\times$. -/
theorem modL_unitsA (a : Aˣ) : modL F A (unitsA a) = 1 := by
  have h : Units.map (Algebra.norm (Adeles F)) (unitsA a : (Adeles F ⊗[F] A)ˣ) =
      diagUnits F (Units.map (Algebra.norm F) a) :=
    Units.ext (by rw [Units.coe_map, unitsA_val, weil_IV_3_norm_tmul]; rfl)
  unfold modL
  rw [h]
  exact ideleNorm_diagUnits _

/-- Product formula: $\lvert N'(a)\rvert_{\mathbb A}=1$ for $a\in\mathcal A^\times$. -/
theorem modR_unitsA (a : Aˣ) : modR F A (unitsA a) = 1 := by
  have hbij : Function.Bijective (LinearMap.mulRight F a.val) := Units.mulRight_bijective a
  have hU : IsUnit (LinearMap.det (LinearMap.mulRight F (a : A))) :=
    (LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2 hbij)
  have h : Units.map coregularNormHom (unitsA a : (Adeles F ⊗[F] A)ˣ) = diagUnits F hU.unit :=
    Units.ext (by
      rw [Units.coe_map, unitsA_val, coregularNormHom_apply, coregularNorm_tmul]
      rfl)
  unfold modR
  rw [h]
  exact ideleNorm_diagUnits _

/-- `modL` and `modR` are continuous on the idele group of $\mathcal A$ (Weil's Def. 2 topology). -/
theorem continuous_modL : Continuous (modL F A) :=
  continuous_ideleNorm.comp (Continuous.units_map (Algebra.norm (Adeles F)) continuous_norm_algAdele)

theorem continuous_modR : Continuous (modR F A) :=
  continuous_ideleNorm.comp (Continuous.units_map coregularNormHom continuous_coregularNorm_algAdele)

end NumberFieldKB.WeilBNT
