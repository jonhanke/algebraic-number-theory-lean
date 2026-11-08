import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Weil, *Basic Number Theory*, Chapter IV, §3, Corollary of Proposition 3 (algebras over a number field)

$k$ is a number field (here `F`) and $\mathcal A$ a finite-dimensional algebra over $k$ with a unit (not necessarily
commutative). Weil's $\mathcal A_{\mathbb A}$ is the adele space of the vector space underlying $\mathcal A$, with the
multiplication extended by continuity; here it is the base change $k_{\mathbb A}\otimes_k\mathcal A$
(`Algebra.TensorProduct`), $k_{\mathbb A}$ being QuadFormsKB's `Adeles F` $=k_\infty\times\mathbb A_f$, made a
$k$-algebra by the diagonal embedding (`adelesAlgebra`, a local instance of this file only). A basis $b$ of
$\mathcal A$ over $k$ gives the $k_{\mathbb A}$-basis $1\otimes b_i$ of $\mathcal A_{\mathbb A}$ and the coordinate
isomorphism `algCoords b` of $\mathcal A_{\mathbb A}$ onto $k_{\mathbb A}^n$; through it $\mathcal A_{\mathbb A}$ carries
the topology and Haar measure of $k_{\mathbb A}^n$ (QuadFormsKB's `muAddVec`), as in Weil (IV.1 Prop. 1).

$N_{\mathcal A/k}$ is the regular norm: for $a\in\mathcal A_{\mathbb A}$, the determinant of $x\mapsto ax$ over
$k_{\mathbb A}$ (Mathlib's `Algebra.norm`); the coregular norm $N'(a)$ is the determinant of $x\mapsto xa$
(`coregularNorm`).

**Corollary of Prop. 3** (p. 74): for $a\in\mathcal A_{\mathbb A}$ the following are equivalent: (i) $a$ is an idele
of $\mathcal A$ (a unit of $\mathcal A_{\mathbb A}$); (ii) $N_{\mathcal A/k}(a)$ is an idele of $k$;
(iii) $x\mapsto ax$ is an automorphism of $\mathcal A_{\mathbb A}$. When that is so, the module of $x\mapsto ax$ is
$\lvert N_{\mathcal A/k}(a)\rvert_{\mathbb A}$; and $N_{\mathcal A/k}$ is a continuous morphism.

* **`weil_IV_3_prop3_cor_iff`**: (i) $\iff$ (ii) $\iff$ ($x\mapsto ax$ bijective). Weil's proof: Prop. 3 applied to
  the regular representation, plus "(iii) implies (i)" because $\mathcal A$ has a unit.
* **`weil_IV_3_prop3_cor_module`**: for a unit $a$, the image of the Haar measure under $x\mapsto ax$ (in the
  coordinates $b$) is $\lvert N_{\mathcal A/k}(a)\rvert_{\mathbb A}^{-1}$ times it, by Prop. 3 (QuadFormsKB
  `map_mulVec_muAddVec`) applied to the matrix of $x\mapsto ax$.
* **`weil_IV_3_prop3_cor_continuous`**: $N_{\mathcal A/k}$ is continuous on $\mathcal A_{\mathbb A}$ (in the
  coordinates $b$), hence on the idele group, whose topology (Def. 2) is finer; it is multiplicative (a `MonoidHom`).
* **`weil_IV_3_coregular_module`** (text p. 74): for a unit $a$, the module of $x\mapsto xa$ is
  $\lvert N'(a)\rvert_{\mathbb A}$; **`weil_IV_3_coregular_iff`**: $a$ is a unit iff $N'(a)$ is an idele;
  **`weil_IV_3_coregularNorm_comm`**: $N'=N_{\mathcal A/k}$ when $\mathcal A$ is commutative.
* **`weil_IV_3_norm_tmul`**: on $\mathcal A$ itself, $N_{\mathcal A_{\mathbb A}/k_{\mathbb A}}(1\otimes a)$ is the
  image in $k_{\mathbb A}$ of $N_{\mathcal A/k}(a)$ (Weil: the determinant in $\mathrm{End}(E_K)$ extends that of
  $\mathrm{End}(E)$, p. 71).

Weil's topology on the idele group $\mathcal A_{\mathbb A}^\times$ (Def. 2) and Prop. 2 are not packaged here.
-/

open IsDedekindDomain NumberField MeasureTheory QuadFormsKB.Tamagawa.Measure.Weil
open scoped TensorProduct

noncomputable section

namespace NumberFieldKB.WeilBNT

variable (F : Type) [Field F] [NumberField F]

/-- The diagonal embedding $k\to k_{\mathbb A}=k_\infty\times\mathbb A_f$ as a ring morphism (its additive part is
QuadFormsKB's `diag`). -/
def diagRingHom : F →+* Adeles F :=
  RingHom.prod (mixedEmbedding F) (algebraMap F (FiniteAdeleRing (𝓞 F) F))

theorem diagRingHom_apply (x : F) : diagRingHom F x = diag F x := rfl

/-- $k_{\mathbb A}$ as a $k$-algebra through the diagonal embedding. A local instance of this file only (QuadFormsKB
declares no such instance; making it global is a change for the shared library). -/
abbrev adelesAlgebra : Algebra F (Adeles F) := (diagRingHom F).toAlgebra

attribute [local instance] adelesAlgebra

variable {F} {A : Type} [Ring A] [Algebra F A] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The $k_{\mathbb A}$-basis $1\otimes b_i$ of $\mathcal A_{\mathbb A}=k_{\mathbb A}\otimes_k\mathcal A$. -/
def algAdelesBasis (b : Module.Basis ι F A) : Module.Basis ι (Adeles F) (Adeles F ⊗[F] A) :=
  Algebra.TensorProduct.basis (Adeles F) b

/-- The coordinates $\mathcal A_{\mathbb A}\cong k_{\mathbb A}^n$ in the basis $1\otimes b_i$. -/
def algCoords (b : Module.Basis ι F A) : (Adeles F ⊗[F] A) ≃ₗ[Adeles F] (ι → Adeles F) :=
  (algAdelesBasis b).equivFun

/-- The coregular norm $N'(a)=\det(x\mapsto xa)$ on $\mathcal A_{\mathbb A}$ (Weil, p. 74). -/
def coregularNorm (a : Adeles F ⊗[F] A) : Adeles F :=
  LinearMap.det (LinearMap.mulRight (Adeles F) a)

/-- In a ring that is free of finite rank over a commutative ring, if $x\mapsto ax$ is bijective then $a$ is a unit
(Weil: "as $\mathcal A$ contains a unit, (iii) implies (i)"). -/
theorem isUnit_of_bijective_mulLeft {S : Type*} [Ring S] {a : S} (h : Function.Bijective (a * ·)) : IsUnit a := by
  obtain ⟨c, hc⟩ := h.2 1
  have hca : c * a = 1 := h.1 (by simp only [← mul_assoc, hc, one_mul, mul_one])
  exact ⟨⟨a, c, hc, hca⟩, rfl⟩

/-- Likewise for $x\mapsto xa$. -/
theorem isUnit_of_bijective_mulRight {S : Type*} [Ring S] {a : S} (h : Function.Bijective (· * a)) : IsUnit a := by
  obtain ⟨c, hc⟩ := h.2 1
  have hac : a * c = 1 := h.1 (by simp only [mul_assoc, hc, one_mul, mul_one])
  exact ⟨⟨a, c, hac, hc⟩, rfl⟩

variable [FiniteDimensional F A]

instance : Module.Free (Adeles F) (Adeles F ⊗[F] A) := Module.Free.of_basis (algAdelesBasis (Module.finBasis F A))

instance : Module.Finite (Adeles F) (Adeles F ⊗[F] A) := Module.Finite.of_basis (algAdelesBasis (Module.finBasis F A))

/-- **Weil, IV.§3, Corollary of Prop. 3**, the equivalences: $a\in\mathcal A_{\mathbb A}$ is a unit iff
$N_{\mathcal A/k}(a)$ is an idele of $k$ iff $x\mapsto ax$ is a bijection of $\mathcal A_{\mathbb A}$. -/
@[kb "weil1973bnt" "Ch. IV, §3, Cor. of Prop. 3 (p. 74), equivalence of (i)-(iii), number field case"]
theorem weil_IV_3_prop3_cor_iff (a : Adeles F ⊗[F] A) :
    (IsUnit a ↔ IsUnit (Algebra.norm (Adeles F) a)) ∧ (IsUnit a ↔ Function.Bijective (a * ·)) := by
  have h2 : IsUnit a ↔ Function.Bijective (a * ·) :=
    ⟨fun ⟨u, hu⟩ => hu ▸ (Units.mulLeft_bijective u), isUnit_of_bijective_mulLeft⟩
  refine ⟨?_, h2⟩
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff, h2]
  rfl

omit [FiniteDimensional F A] in
/-- The matrix of $x\mapsto ax$ in the basis $1\otimes b_i$ acts on coordinates by `mulVec`. -/
theorem algCoords_mul (b : Module.Basis ι F A) (a : Adeles F ⊗[F] A) (x : ι → Adeles F) :
    algCoords b (a * (algCoords b).symm x) = (Algebra.leftMulMatrix (algAdelesBasis b) a).mulVec x := by
  have h := Algebra.leftMulMatrix_mulVec_repr (algAdelesBasis b) a ((algCoords b).symm x)
  have hx : ⇑((algAdelesBasis b).repr ((algCoords b).symm x)) = x :=
    (algAdelesBasis b).equivFun.apply_symm_apply x
  rw [hx] at h
  rw [h]
  rfl

omit [FiniteDimensional F A] in
/-- Same for $x\mapsto xa$, with the matrix of right multiplication. -/
theorem algCoords_mulRight (b : Module.Basis ι F A) (a : Adeles F ⊗[F] A) (x : ι → Adeles F) :
    algCoords b ((algCoords b).symm x * a) =
      (LinearMap.toMatrix (algAdelesBasis b) (algAdelesBasis b) (LinearMap.mulRight (Adeles F) a)).mulVec x := by
  have h := (LinearMap.mulRight (Adeles F) a).toMatrix_mulVec_repr (algAdelesBasis b) (algAdelesBasis b)
    ((algCoords b).symm x)
  have hx : ⇑((algAdelesBasis b).repr ((algCoords b).symm x)) = x :=
    (algAdelesBasis b).equivFun.apply_symm_apply x
  rw [hx] at h
  rw [h]
  rfl

/-- Prop. 3 for a matrix with invertible determinant, in the form used below. -/
theorem map_mulVec_muAddVec_of_isUnit_det (M : Matrix ι ι (Adeles F)) (h : IsUnit M.det) :
    Measure.map M.mulVec (muAddVec F ι) = ENNReal.ofReal (ideleNorm F h.unit)⁻¹ • muAddVec F ι := by
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr h
  have := map_mulVec_muAddVec (F := F) hM.unit
  have hdet : Matrix.GeneralLinearGroup.det hM.unit = h.unit := Units.ext rfl
  rw [hdet] at this
  exact this

omit [FiniteDimensional F A] in
/-- **Weil, IV.§3, Corollary of Prop. 3**, the module: for an idele $a$ of $\mathcal A$, the image of the Haar
measure of $\mathcal A_{\mathbb A}$ (in the coordinates $b$) under $x\mapsto ax$ is
$\lvert N_{\mathcal A/k}(a)\rvert_{\mathbb A}^{-1}$ times it; i.e. the module of $x\mapsto ax$ is
$\lvert N_{\mathcal A/k}(a)\rvert_{\mathbb A}$. -/
@[kb "weil1973bnt" "Ch. IV, §3, Cor. of Prop. 3 (p. 74), the module |N(a)|_A, number field case"]
theorem weil_IV_3_prop3_cor_module (b : Module.Basis ι F A) (a : (Adeles F ⊗[F] A)ˣ) :
    Measure.map (fun x => algCoords b ((a : Adeles F ⊗[F] A) * (algCoords b).symm x)) (muAddVec F ι) =
      ENNReal.ofReal (ideleNorm F (Units.map (Algebra.norm (Adeles F)) a))⁻¹ • muAddVec F ι := by
  have hdet : IsUnit (Algebra.leftMulMatrix (algAdelesBasis b) (a : Adeles F ⊗[F] A)).det := by
    rw [← Algebra.norm_eq_matrix_det]
    exact (Units.map (Algebra.norm (Adeles F)) a).isUnit
  have hu : hdet.unit = Units.map (Algebra.norm (Adeles F)) a := Units.ext (by
    rw [IsUnit.unit_spec, Units.coe_map]; exact (Algebra.norm_eq_matrix_det (algAdelesBasis b) _).symm)
  rw [show (fun x => algCoords b ((a : Adeles F ⊗[F] A) * (algCoords b).symm x)) =
      (Algebra.leftMulMatrix (algAdelesBasis b) (a : Adeles F ⊗[F] A)).mulVec from
      funext (algCoords_mul b _), map_mulVec_muAddVec_of_isUnit_det _ hdet, hu]

omit [FiniteDimensional F A] in
/-- **Weil, IV.§3, Corollary of Prop. 3**, continuity: $N_{\mathcal A/k}$ is continuous on $\mathcal A_{\mathbb A}$
(in the coordinates $b$). It is multiplicative, being Mathlib's `Algebra.norm : _ →* _`. -/
@[kb "weil1973bnt" "Ch. IV, §3, Cor. of Prop. 3 (p. 74), continuity of the norm, number field case"]
theorem weil_IV_3_prop3_cor_continuous (b : Module.Basis ι F A) :
    Continuous fun x : ι → Adeles F => Algebra.norm (Adeles F) ((algCoords b).symm x) := by
  have hlin : Continuous fun x : ι → Adeles F =>
      Algebra.leftMulMatrix (algAdelesBasis b) ((algCoords b).symm x) :=
    LinearMap.continuous_on_pi
      ((Algebra.leftMulMatrix (algAdelesBasis b)).toLinearMap ∘ₗ (algCoords b).symm.toLinearMap)
  simp_rw [Algebra.norm_eq_matrix_det (algAdelesBasis b)]
  exact hlin.matrix_det

omit [FiniteDimensional F A] in
/-- **Weil, IV.§3, text p. 74**, the coregular norm: for an idele $a$ of $\mathcal A$, the module of $x\mapsto xa$ is
$\lvert N'(a)\rvert_{\mathbb A}$. -/
@[kb "weil1973bnt" "Ch. IV, §3, text p. 74 (module of x -> xa is |N'(a)|_A), number field case"]
theorem weil_IV_3_coregular_module (b : Module.Basis ι F A) (a : (Adeles F ⊗[F] A)ˣ)
    (ha : IsUnit (coregularNorm (a : Adeles F ⊗[F] A))) :
    Measure.map (fun x => algCoords b ((algCoords b).symm x * (a : Adeles F ⊗[F] A))) (muAddVec F ι) =
      ENNReal.ofReal (ideleNorm F ha.unit)⁻¹ • muAddVec F ι := by
  have hdet : IsUnit (LinearMap.toMatrix (algAdelesBasis b) (algAdelesBasis b)
      (LinearMap.mulRight (Adeles F) (a : Adeles F ⊗[F] A))).det := by
    rw [LinearMap.det_toMatrix]; exact ha
  have hu : hdet.unit = ha.unit := Units.ext (by
    rw [IsUnit.unit_spec, IsUnit.unit_spec, LinearMap.det_toMatrix]; rfl)
  rw [show (fun x => algCoords b ((algCoords b).symm x * (a : Adeles F ⊗[F] A))) =
      (LinearMap.toMatrix (algAdelesBasis b) (algAdelesBasis b)
        (LinearMap.mulRight (Adeles F) (a : Adeles F ⊗[F] A))).mulVec from
      funext (algCoords_mulRight b _), map_mulVec_muAddVec_of_isUnit_det _ hdet, hu]

/-- **Weil, IV.§3, text p. 74**: $a$ is an idele of $\mathcal A$ iff $N'(a)$ is an idele of $k$ (so the hypothesis of
`weil_IV_3_coregular_module` holds for every idele $a$). -/
theorem weil_IV_3_coregular_iff (a : Adeles F ⊗[F] A) : IsUnit a ↔ IsUnit (coregularNorm a) := by
  have h2 : IsUnit a ↔ Function.Bijective (· * a) :=
    ⟨fun ⟨u, hu⟩ => hu ▸ (Units.mulRight_bijective u), isUnit_of_bijective_mulRight⟩
  rw [coregularNorm, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff, h2]
  rfl

/-- **Weil, IV.§3, text p. 74**: $N'=N_{\mathcal A/k}$ when $\mathcal A$ is commutative. -/
theorem weil_IV_3_coregularNorm_comm {A : Type} [CommRing A] [Algebra F A] [FiniteDimensional F A]
    (a : Adeles F ⊗[F] A) : coregularNorm a = Algebra.norm (Adeles F) a := by
  rw [coregularNorm, Algebra.norm_apply]
  congr 1
  ext x
  simp [mul_comm]

/-- The regular norm of $\mathcal A_{\mathbb A}$ over $k_{\mathbb A}$ extends that of $\mathcal A$ over $k$:
$N(1\otimes a)$ is the diagonal image of $N_{\mathcal A/k}(a)$. -/
theorem weil_IV_3_norm_tmul (a : A) :
    Algebra.norm (Adeles F) ((1 : Adeles F) ⊗ₜ[F] a) = diag F (Algebra.norm F a) := by
  have h : Algebra.lmul (Adeles F) (Adeles F ⊗[F] A) ((1 : Adeles F) ⊗ₜ[F] a) =
      (Algebra.lmul F A a).baseChange (Adeles F) := by
    ext x
    simp
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]
  rfl

end NumberFieldKB.WeilBNT
