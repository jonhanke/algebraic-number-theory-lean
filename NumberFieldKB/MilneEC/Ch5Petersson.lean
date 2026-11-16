import NumberFieldKB.MilneEC.Ch5Hecke
import NumberFieldKB.MilneEC.Ch5Fricke
import NumberFieldKB.MilneEC.Ch5FiniteDim
import Mathlib.RingTheory.TotallySplit
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
# Milne, *Elliptic Curves*, Chapter V §4: the spectral theorem, the Petersson product, newforms

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §4, pdf pp. 212–215.

Formalized: Theorem 4.16 (from Mathlib's spectral theorem), Proposition 4.17 (Mathlib's
$\mathrm{GL}_2(\mathbb R)$-invariant measure `volume` on `ℍ`, which is $dx\,dy/y^2$), Lemma 4.18 (by the
Cauchy–Riemann equations and the change of variables formula), the invariance of $f\bar g y^{2k}$, the Petersson
product (definition in prose), old and new forms (definition in prose). Named statements: Theorem 4.19
(Petersson), the properties of $w_N$ and of the new subspace used on pdf pp. 214–215, Theorem 4.20 (Atkin–Lehner).
Proved from them: the decomposition into simultaneous eigenspaces (pdf p. 214) and the properties of newforms
(pdf p. 215: eigenform of $w_N$ and of all $T(p)$, a unique normalised form, Euler product, functional equation).

Old forms: Milne calls a form old if it lies in some $S_{2k}(\Gamma_0(M))$, $M \mid N$, $M < N$; the standard
definition (Atkin–Lehner), needed for Theorem 4.20, also includes the forms $f(dz)$ for $dM \mid N$ (erratum,
recorded in `oldforms`).
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup MeasureTheory
open scoped MatrixGroups Real Manifold ComplexConjugate Pointwise Modular

namespace NumberFieldKB.MilneEC.V

/-! ### Linear algebra: the spectral theorem -/

/-- **Theorem 4.16** (spectral theorem, pdf p. 212): on a finite-dimensional complex inner product space,
(a) a self-adjoint map is diagonalisable: $V$ is the direct sum of its eigenspaces; (b) a family of commuting
self-adjoint maps has a basis of common eigenvectors (Mathlib: `LinearMap.IsSymmetric.direct_sum_isInternal`,
`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`). -/
@[kb "milne2006ec" "Ch. V, Theorem 4.16 (spectral theorem), pdf p. 212"]
theorem thm_4_16 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] :
    (∀ α : V →ₗ[ℂ] V, α.IsSymmetric →
      DirectSum.IsInternal fun μ : Module.End.Eigenvalues α ↦ Module.End.eigenspace α μ) ∧
    ∀ {ι : Type*} (α : ι → V →ₗ[ℂ] V), (∀ i, (α i).IsSymmetric) → (∀ i j, α i ∘ₗ α j = α j ∘ₗ α i) →
      ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V, ∀ i j, ∃ μ : ℂ, α i (b j) = μ • b j := by
  refine ⟨fun α hα => hα.direct_sum_isInternal, ?_⟩
  intro ι α hα hc
  classical
  have hC : Pairwise (Function.onFun Commute α) := by
    intro i j _
    exact LinearMap.ext fun x => by simpa using LinearMap.congr_fun (hc i j) x
  have hint := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hα hC
  let E : (ι → ℂ) → Submodule ℂ V := fun γ => ⨅ j, Module.End.eigenspace (α j) (γ j)
  let v : ∀ γ, Module.Basis _ ℂ (E γ) := fun γ => Module.Free.chooseBasis ℂ (E γ)
  let B := hint.collectedBasis v
  refine ⟨B.reindex (B.indexEquiv (Module.finBasis ℂ V)), fun i j => ?_⟩
  rw [Module.Basis.reindex_apply]
  set a := (B.indexEquiv (Module.finBasis ℂ V)).symm j
  have hmem := hint.collectedBasis_mem v a
  rw [Submodule.mem_iInf] at hmem
  exact ⟨a.1 i, Module.End.mem_eigenspace_iff.mp (hmem i)⟩

/-! ### The invariant measure on the upper half-plane -/

/-- **Proposition 4.17** (pdf p. 213): the measure $\mu(U) = \iint_U dx\,dy/y^2$ is invariant under
$\mathrm{SL}_2(\mathbb R)$. Mathlib's `volume` on `ℍ` is this measure (`UpperHalfPlane.volume_eq_lintegral`), and
it is invariant under $\mathrm{GL}_2(\mathbb R)$. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.17, pdf p. 213"]
theorem prop_4_17 :
    (∀ U : Set ℍ, MeasurableSet U →
      volume U = ∫⁻ z in (UpperHalfPlane.coe '' U), ENNReal.ofReal (1 / z.im ^ 2)) ∧
    ∀ (γ : SL(2, ℝ)) (U : Set ℍ), volume ((Matrix.SpecialLinearGroup.toGL γ : GL (Fin 2) ℝ) • U) = volume U := by
  refine ⟨fun U hU => ?_, fun γ U => ?_⟩
  · rw [UpperHalfPlane.volume_eq_lintegral]
    refine setLIntegral_congr_fun (measurableEmbedding_coe.measurableSet_image.mpr hU) ?_
    intro z hz
    obtain ⟨w, -, rfl⟩ := hz
    have h : 0 < (w : ℂ).im := w.im_pos
    show (((1 / ‖(w : ℂ).im‖₊) ^ 2 : NNReal) : ENNReal) = ENNReal.ofReal (1 / (w : ℂ).im ^ 2)
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs, abs_of_pos h]
    ring
  · exact measure_smul _ _ _

/-- **Lemma 4.18** (pdf p. 213), pointwise form: for $w$ holomorphic at $z$, the Jacobian determinant of
$z \mapsto w(z)$, viewed as a map $\mathbb R^2 \to \mathbb R^2$, is $|w'(z)|^2$ (Cauchy–Riemann). -/
@[kb "milne2006ec" "Ch. V, Lemma 4.18, pdf p. 213"]
theorem lemma_4_18 {w : ℂ → ℂ} {z : ℂ} (hw : DifferentiableAt ℂ w z) :
    LinearMap.det ((fderiv ℝ w z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = ‖deriv w z‖ ^ 2 := by
  have h := hw.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  rw [h.fderiv]
  have : (((ContinuousLinearMap.toSpanSingleton ℂ (deriv w z)).restrictScalars ℝ :
      ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = (LinearMap.mulLeft ℂ (deriv w z)).restrictScalars ℝ := by
    ext; simp [mul_comm]
  rw [this, LinearMap.det_restrictScalars, LinearMap.det_mulLeft, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

/-- **Lemma 4.18** (pdf p. 213): an injective holomorphic map multiplies areas by $|w'(z)|^2$:
$\mathrm{area}(w(U)) = \iint_U |w'(z)|^2\,dx\,dy$. -/
@[kb "milne2006ec" "Ch. V, Lemma 4.18, pdf p. 213"]
theorem lemma_4_18_area {w : ℂ → ℂ} {U : Set ℂ} (hU : MeasurableSet U) (hopen : IsOpen U)
    (hw : DifferentiableOn ℂ w U) (hinj : Set.InjOn w U) :
    volume (w '' U) = ∫⁻ z in U, ENNReal.ofReal (‖deriv w z‖ ^ 2) := by
  have hd : ∀ x ∈ U, DifferentiableAt ℂ w x := fun x hx => hw.differentiableAt (hopen.mem_nhds hx)
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU
    (f := w) (f' := fun x => (fderiv ℝ w x : ℂ →L[ℝ] ℂ))
    (fun x hx => by
      have := ((hd x hx).hasFDerivAt.restrictScalars ℝ)
      rw [this.fderiv] at *
      exact this.hasFDerivWithinAt) hinj (fun _ => 1)
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul] at key
  rw [key]
  refine setLIntegral_congr_fun hU ?_
  intro x hx
  have := lemma_4_18 (hd x hx)
  show ENNReal.ofReal |LinearMap.det ((fderiv ℝ w x : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)| = _
  rw [this, abs_of_nonneg (by positivity)]

/-- Running text (pdf p. 214): for modular forms $f$, $g$ of weight $2k$ for $\Gamma_0(N)$, the function
$f(z)\overline{g(z)}y^{2k}$ is invariant under $\Gamma_0(N)$. (Milne writes "invariant under
$\mathrm{SL}_2(\mathbb R)$": what holds for all of $\mathrm{SL}_2(\mathbb R)$ is the transformation rule
$\phi(\gamma z) = \phi(z)$ for $\phi = (f|\gamma)\overline{(g|\gamma)}y^{2k}$, Mathlib's `petersson_slash`.) -/
@[kb "milne2006ec" "Ch. V, §4, invariance of f ḡ y^{2k} (running text), pdf p. 214"]
theorem petersson_integrand_invariant {N : ℕ} [NeZero N] {k : ℕ} (f g : ModularForm (Gamma0GL N) (2 * k : ℤ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    UpperHalfPlane.petersson (2 * k) g f (γ • z) = UpperHalfPlane.petersson (2 * k) g f z := by
  have hmem : Matrix.SpecialLinearGroup.mapGL ℝ γ ∈ Gamma0GL N := ⟨γ, hγ, rfl⟩
  exact SlashInvariantFormClass.petersson_smul (k := (2 * k : ℤ)) (f := g) (f' := f) (τ := z) hmem

/-! ### The Petersson product -/

/-- A set of representatives of the right cosets $\Gamma_0(N)\gamma$ in $\mathrm{SL}_2(\mathbb Z)$. -/
def IsRightCosetReps (N : ℕ) (R : Set SL(2, ℤ)) : Prop :=
  ∀ g : SL(2, ℤ), ∃! r, r ∈ R ∧ g * r⁻¹ ∈ CongruenceSubgroup.Gamma0 N

/-- Right coset representatives exist for every level $N$. -/
theorem exists_rightCosetReps (N : ℕ) : ∃ R, IsRightCosetReps N R := by
  refine ⟨Set.range fun q : Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 N)) => q.out, ?_⟩
  intro g
  refine ⟨(Quotient.mk _ g).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · have := Quotient.mk_out (s := QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 N)) g
    rw [QuotientGroup.rightRel_apply] at this
    exact this
  · rintro r ⟨⟨q, rfl⟩, hr⟩
    have h1 : (Quotient.mk _ q.out : Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 N))) =
        Quotient.mk _ g := by
      apply Quotient.sound
      show (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 N)) _ _
      rw [QuotientGroup.rightRel_apply]
      exact hr
    have h2 : q = Quotient.mk _ g := by rw [← h1]; exact (Quotient.out_eq q).symm
    show q.out = _
    rw [h2]

/-- The fundamental domain $D_N = \bigcup_i \gamma_iD$ for $\Gamma_0(N)$ built from the chosen coset
representatives (Remark 1.4). -/
noncomputable def fundDomainGamma0 (N : ℕ) : Set ℍ :=
  ⋃ r ∈ (exists_rightCosetReps N).choose, r • 𝒟ᵒ

/-- The Petersson product (pdf p. 214): $\langle f, g\rangle = \iint_{D} f\bar g\,y^{2k}\,dx\,dy/y^2$ over a
fundamental domain $D$ for $\Gamma_0(N)$. -/
@[kb "milne2006ec" "Ch. V, §4, the Petersson product (definition in prose), pdf p. 214"]
noncomputable def peterssonProduct (N k : ℕ) (f g : ℍ → ℂ) : ℂ :=
  ∫ z in fundDomainGamma0 N, UpperHalfPlane.petersson (2 * k) g f z

/-- **Theorem 4.19** (Petersson, pdf p. 214), a named statement: the integral converges when one of $f$, $g$ is a
cusp form, and is independent of the fundamental domain built from coset representatives; it is a
positive-definite hermitian form on $S_{2k}(\Gamma_0(N))$; the Hecke operators $T(n)$ with $\gcd(n, N) = 1$ are
self-adjoint. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.19 (Petersson), pdf p. 214"]
structure Thm4_19 (N k : ℕ) [NeZero N] : Prop where
  integrable : ∀ (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) (g : ModularForm (Gamma0GL N) (2 * k : ℤ)),
    IntegrableOn (UpperHalfPlane.petersson (2 * k) g f) (fundDomainGamma0 N) ∧
      IntegrableOn (UpperHalfPlane.petersson (2 * k) f g) (fundDomainGamma0 N)
  independent : ∀ (R : Set SL(2, ℤ)), IsRightCosetReps N R → ∀ (f : CuspForm (Gamma0GL N) (2 * k : ℤ))
    (g : ModularForm (Gamma0GL N) (2 * k : ℤ)),
    ∫ z in ⋃ r ∈ R, r • 𝒟ᵒ, UpperHalfPlane.petersson (2 * k) g f z = peterssonProduct N k f g
  hermitian : ∀ f g : CuspForm (Gamma0GL N) (2 * k : ℤ), peterssonProduct N k g f = conj (peterssonProduct N k f g)
  pos : ∀ f : CuspForm (Gamma0GL N) (2 * k : ℤ), f ≠ 0 → 0 < (peterssonProduct N k f f).re
  selfAdjoint : ∀ n : ℕ, 1 ≤ n → n.Coprime N → ∀ f g : CuspForm (Gamma0GL N) (2 * k : ℤ),
    peterssonProduct N k (heckeT N k n f) g = peterssonProduct N k f (heckeT N k n g)

/-- Running text (pdf p. 214), named: $w_N$ is self-adjoint for the Petersson product and commutes with the
$T(n)$, $\gcd(n, N) = 1$. -/
@[kb "milne2006ec" "Ch. V, §4, w_N is self-adjoint and commutes with T(n) (running text), pdf p. 214"]
structure WNProperties (N k : ℕ) [NeZero N] : Prop where
  selfAdjoint : ∀ f g : CuspForm (Gamma0GL N) (2 * k : ℤ),
    peterssonProduct N k (wN N k f) g = peterssonProduct N k f (wN N k g)
  comm : ∀ n : ℕ, 1 ≤ n → n.Coprime N → ∀ f : CuspForm (Gamma0GL N) (2 * k : ℤ),
    wN N k (heckeT N k n f) = heckeT N k n (wN N k f)

/-- The explicit Hecke operator is additive. -/
theorem heckeT_add (N k n : ℕ) (f g : ℍ → ℂ) :
    heckeT N k n (f + g) = heckeT N k n f + heckeT N k n g := by
  funext z
  simp only [heckeT, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The explicit Hecke operator is homogeneous. -/
theorem heckeT_smul' (N k n : ℕ) (c : ℂ) (f : ℍ → ℂ) :
    heckeT N k n (c • f) = c • heckeT N k n f := by
  funext z
  simp only [heckeT, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

/-- Under Theorem 4.7, $T(n)$ as a linear endomorphism of the cusp forms. -/
noncomputable def heckeLin {N : ℕ} [NeZero N] {k : ℕ} (h47 : Thm4_7 N k) (n : ℕ) (hn : 1 ≤ n) :
    CuspForm (Gamma0GL N) (2 * k : ℤ) →ₗ[ℂ] CuspForm (Gamma0GL N) (2 * k : ℤ) where
  toFun f := (h47.maps_to n hn f).choose
  map_add' f g := by
    apply DFunLike.coe_injective
    rw [(h47.maps_to n hn (f + g)).choose_spec, FunLike.coe_add, heckeT_add, FunLike.coe_add,
      (h47.maps_to n hn f).choose_spec, (h47.maps_to n hn g).choose_spec]
  map_smul' c f := by
    apply DFunLike.coe_injective
    rw [(h47.maps_to n hn (c • f)).choose_spec, FunLike.coe_smul, heckeT_smul', RingHom.id_apply,
      FunLike.coe_smul, (h47.maps_to n hn f).choose_spec]

/-- The underlying function of the linear Hecke operator $T_n$ is the Hecke operator $T_n$. -/
theorem coe_heckeLin {N : ℕ} [NeZero N] {k : ℕ} (h47 : Thm4_7 N k) (n : ℕ) (hn : 1 ≤ n)
    (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) : ⇑(heckeLin h47 n hn f) = heckeT N k n f :=
  (h47.maps_to n hn f).choose_spec

/-- The Petersson product on the cusp forms, as an inner product core (Theorem 4.19). -/
@[instance_reducible] noncomputable def peterssonCore{N : ℕ} [NeZero N] {k : ℕ} (h419 : Thm4_19 N k) :
    InnerProductSpace.Core ℂ (CuspForm (Gamma0GL N) (2 * k : ℤ)) where
  inner f g := peterssonProduct N k g f
  conj_inner_symm f g := by
    show conj (peterssonProduct N k f g) = peterssonProduct N k g f
    exact (h419.hermitian f g).symm
  re_inner_nonneg f := by
    by_cases hf : f = 0
    · subst hf
      simp [peterssonProduct, UpperHalfPlane.petersson]
    · exact (h419.pos f hf).le
  add_left f g h := by
    show peterssonProduct N k h (⇑(f + g)) = peterssonProduct N k h f + peterssonProduct N k h g
    have hxi : IntegrableOn (UpperHalfPlane.petersson (2 * k) f h) (fundDomainGamma0 N) :=
      (h419.integrable f (ModularFormClass.modularForm h)).2
    have hyi : IntegrableOn (UpperHalfPlane.petersson (2 * k) g h) (fundDomainGamma0 N) :=
      (h419.integrable g (ModularFormClass.modularForm h)).2
    unfold peterssonProduct
    rw [← integral_add hxi hyi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [UpperHalfPlane.petersson, add_mul]
  smul_left f g c := by
    show peterssonProduct N k g (⇑(c • f)) = conj c * peterssonProduct N k g f
    unfold peterssonProduct
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [UpperHalfPlane.petersson]
    ring
  definite f hf := by
    by_contra hne
    have := h419.pos f hne
    have h0 : peterssonProduct N k f f = 0 := hf
    rw [h0] at this
    simp at this

/-- Running text (pdf p. 214), from Theorems 4.7, 4.16 and 4.19: $S_{2k}(\Gamma_0(N))$ has a basis of simultaneous
eigenvectors of all $T(n)$ with $\gcd(n, N) = 1$. -/
@[kb "milne2006ec" "Ch. V, §4, S_{2k} = ⊕ V_i, simultaneous eigenspaces (running text), pdf p. 214"]
theorem exists_eigenbasis {N : ℕ} [NeZero N] {k : ℕ} (h47 : Thm4_7 N k) (h419 : Thm4_19 N k) :
    ∃ (ι : Type) (b : Module.Basis ι ℂ (CuspForm (Gamma0GL N) (2 * k : ℤ))), ∀ (n : ℕ), 1 ≤ n → n.Coprime N →
      ∀ i, ∃ μ : ℂ, heckeT N k n (b i) = μ • ⇑(b i) := by
  -- finite dimensionality of `S_{2k}(Γ₀(N))`: `finiteDimensional_cuspForm_Gamma0` (Ch5FiniteDim)
  have hfin : FiniteDimensional ℂ (CuspForm (Gamma0GL N) (2 * k : ℤ)) := finiteDimensional_cuspForm_Gamma0 _
  let cd : InnerProductSpace.Core ℂ (CuspForm (Gamma0GL N) (2 * k : ℤ)) := peterssonCore h419
  let _ : NormedAddCommGroup (CuspForm (Gamma0GL N) (2 * k : ℤ)) := cd.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ (CuspForm (Gamma0GL N) (2 * k : ℤ)) := InnerProductSpace.ofCore cd.toCore
  let α : {n : ℕ // 1 ≤ n ∧ n.Coprime N} → (CuspForm (Gamma0GL N) (2 * k : ℤ)) →ₗ[ℂ]
      (CuspForm (Gamma0GL N) (2 * k : ℤ)) := fun n => heckeLin h47 n.1 n.2.1
  have hsym : ∀ n, (α n).IsSymmetric := by
    intro n x y
    show peterssonProduct N k y (⇑(α n x)) = peterssonProduct N k (⇑(α n y)) x
    rw [coe_heckeLin, coe_heckeLin]
    exact (h419.selfAdjoint n.1 n.2.1 n.2.2 y x).symm
  have hcomm : ∀ i j, α i ∘ₗ α j = α j ∘ₗ α i := by
    intro i j
    apply LinearMap.ext
    intro f
    apply DFunLike.coe_injective
    show ⇑(α i (α j f)) = ⇑(α j (α i f))
    simp only [α, coe_heckeLin]
    exact h47.comm i.1 j.1 i.2.1 j.2.1 f
  obtain ⟨b, hb⟩ := (thm_4_16 (V := CuspForm (Gamma0GL N) (2 * k : ℤ))).2 α hsym hcomm
  refine ⟨Fin (Module.finrank ℂ (CuspForm (Gamma0GL N) (2 * k : ℤ))), b, fun n hn hnc j => ?_⟩
  obtain ⟨μ, hμ⟩ := hb ⟨n, hn, hnc⟩ j
  refine ⟨μ, ?_⟩
  have := congrArg (fun F : CuspForm (Gamma0GL N) (2 * k : ℤ) => (⇑F : ℍ → ℂ)) hμ
  simp only [α, coe_heckeLin, FunLike.coe_smul] at this
  exact this

/-! ### Old forms and new forms -/

/-- The old forms (pdf p. 215, Atkin–Lehner's definition): the span of the forms $z \mapsto g(dz)$ with
$g \in S_{2k}(\Gamma_0(M))$, $M \mid N$, $M < N$, $dM \mid N$. -/
@[kb "milne2006ec" "Ch. V, §4, old forms (definition in prose), pdf p. 215"]
noncomputable def oldforms (N k : ℕ) [NeZero N] : Submodule ℂ (CuspForm (Gamma0GL N) (2 * k : ℤ)) :=
  Submodule.span ℂ {f | ∃ M d : ℕ, 1 ≤ M ∧ M ∣ N ∧ M < N ∧ 1 ≤ d ∧ d * M ∣ N ∧
    ∃ g : CuspForm (Gamma0GL M) (2 * k : ℤ), ∀ z : ℍ, f z = g (ofComplex ((d : ℂ) * z))}

/-- The new forms (pdf p. 215): the orthogonal complement of the old forms for the Petersson product. Linearity of
the Petersson integral needs its convergence (Theorem 4.19), so the complement is defined as the span of the forms
orthogonal to all old forms; under Theorem 4.19 it is exactly that set (`mem_newforms_iff`). -/
@[kb "milne2006ec" "Ch. V, §4, new forms (definition in prose), pdf p. 215"]
noncomputable def newforms (N k : ℕ) [NeZero N] : Submodule ℂ (CuspForm (Gamma0GL N) (2 * k : ℤ)) :=
  Submodule.span ℂ {f | ∀ g ∈ oldforms N k, peterssonProduct N k f g = 0}

/-- Under Theorem 4.19, a cusp form is new if and only if it is orthogonal to all old forms. -/
theorem mem_newforms_iff {N : ℕ} [NeZero N] {k : ℕ} (h419 : Thm4_19 N k) (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) :
    f ∈ newforms N k ↔ ∀ g ∈ oldforms N k, peterssonProduct N k f g = 0 := by
  constructor
  · intro hf
    unfold newforms at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro g _
      simp [peterssonProduct, UpperHalfPlane.petersson]
    | add x y _ _ hx hy =>
      intro g hg
      have hxi : IntegrableOn (UpperHalfPlane.petersson (2 * k) g x) (fundDomainGamma0 N) :=
        (h419.integrable x (ModularFormClass.modularForm g)).1
      have hyi : IntegrableOn (UpperHalfPlane.petersson (2 * k) g y) (fundDomainGamma0 N) :=
        (h419.integrable y (ModularFormClass.modularForm g)).1
      have : peterssonProduct N k (⇑(x + y)) g =
          peterssonProduct N k x g + peterssonProduct N k y g := by
        unfold peterssonProduct
        rw [← integral_add hxi hyi]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp [UpperHalfPlane.petersson, mul_add, add_mul]
      rw [this, hx g hg, hy g hg, add_zero]
    | smul c x _ hx =>
      intro g hg
      have : peterssonProduct N k (⇑(c • x)) g = c * peterssonProduct N k x g := by
        unfold peterssonProduct
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp [UpperHalfPlane.petersson]
        ring
      rw [this, hx g hg, mul_zero]
  · intro h
    exact Submodule.subset_span h

/-- **Theorem 4.20** (Atkin–Lehner 1970, pdf p. 215), a named statement, with the stability of the new space
stated in the text: $S^{\mathrm{new}}_{2k}(\Gamma_0(N))$ is stable under all $T(n)$ and $w_N$, and its
simultaneous eigenspaces for the $T(n)$ with $\gcd(n, N) = 1$ have dimension $1$. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.20 (Atkin–Lehner), pdf p. 215"]
structure Thm4_20 (N k : ℕ) [NeZero N] : Prop where
  heckeT_mem : ∀ n : ℕ, 1 ≤ n → ∀ f ∈ newforms N k, ∃ F ∈ newforms N k, ⇑F = heckeT N k n f
  wN_mem : ∀ f ∈ newforms N k, ∃ F ∈ newforms N k, ⇑F = wN N k f
  multiplicity_one : ∀ f ∈ newforms N k, ∀ g ∈ newforms N k, f ≠ 0 →
    (∀ n : ℕ, 1 ≤ n → n.Coprime N → ∃ μ : ℂ, heckeT N k n f = μ • ⇑f ∧ heckeT N k n g = μ • ⇑g) →
    ∃ c : ℂ, g = c • f

/-- $w_N$ is homogeneous. -/
theorem wN_smul' (N k : ℕ) (c : ℂ) (f : ℍ → ℂ) : wN N k (c • f) = c • wN N k f := by
  funext z
  simp only [wN, Pi.smul_apply, smul_eq_mul]
  ring

/-- The $q$-expansion coefficients of a cusp form for $\Gamma_0(N)$ are homogeneous. -/
theorem qExpansion_coeff_smul_cuspForm {N k : ℕ} [NeZero N] (c : ℂ)
    (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) (n : ℕ) :
    (qExpansion 1 ⇑(c • f)).coeff n = c * (qExpansion 1 ⇑f).coeff n := by
  have hw : (Gamma0GL N).strictWidthInfty = 1 := strictWidthInfty_Gamma0GL
  have hp : (1 : ℝ) ∈ (Gamma0GL N).strictPeriods :=
    hw ▸ (Gamma0GL N).strictWidthInfty_mem_strictPeriods
  have := ModularForm.qExpansion_smul one_pos hp c f
  rw [FunLike.coe_smul, this]
  simp

/-- Consequences of Theorem 4.20 (pdf p. 215), proved from the named statements: a nonzero new form $f$ that is an
eigenvector of all $T(n)$, $\gcd(n, N) = 1$, is an eigenvector of $w_N$ and of all $T(n)$; it has $c(1) \ne 0$;
normalised by $c(1) = 1$ it has the Euler product of Corollary 4.9, and its completed $L$-function satisfies
$\Lambda(f, 2k - s) = \varepsilon(-1)^k\Lambda(f, s)$ with $\varepsilon = \pm1$ the eigenvalue of $w_N$. For $k = 1$
this reads $\Lambda(f, s) = -\varepsilon\Lambda(f, 2 - s)$; Milne prints $\varepsilon\Lambda(f, 2 - s)$ (erratum,
sign). -/
@[kb "milne2006ec" "Ch. V, §4, properties of newforms after Theorem 4.20 (running text), pdf p. 215"]
theorem newform_properties {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k) (h47 : Thm4_7 N k) (h420 : Thm4_20 N k)
    (hwN : WNProperties N k) (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) (hf : f ∈ newforms N k) (hf0 : f ≠ 0)
    (hT : ∀ n : ℕ, 1 ≤ n → n.Coprime N → ∃ μ : ℂ, heckeT N k n f = μ • ⇑f) :
    (∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ wN N k f = ε • ⇑f) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ μ : ℂ, heckeT N k n f = μ • ⇑f) ∧
    (qExpansion 1 f).coeff 1 ≠ 0 ∧
    ∃ F : CuspForm (Gamma0GL N) (2 * k : ℤ), (∃ c : ℂ, F = c • f) ∧ (qExpansion 1 F).coeff 1 = 1 ∧
      (∀ G : CuspForm (Gamma0GL N) (2 * k : ℤ), (∃ c : ℂ, G = c • f) → (qExpansion 1 G).coeff 1 = 1 → G = F) ∧
      (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        HasProd (fun p : Nat.Primes ↦ eulerFactor N k (fun n ↦ (qExpansion 1 F).coeff n) p s)
          (ModularForm.L (by positivity : (0 : ℤ) < 2 * k) F s)) ∧
      ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ wN N k F = ε • ⇑F ∧
        ∀ s : ℂ, LambdaHecke N k hk F (2 * k - s) = ε * (-1) ^ k * LambdaHecke N k hk F s := by
  choose! μ hμ using hT
  have key : ∀ G ∈ newforms N k, (∀ n : ℕ, 1 ≤ n → n.Coprime N → heckeT N k n G = μ n • ⇑G) →
      ∃ c : ℂ, G = c • f := fun G hG hGT =>
    h420.multiplicity_one f hf G hG hf0 (fun n hn hc => ⟨μ n, hμ n hn hc, hGT n hn hc⟩)
  -- the eigenvalue of `w_N`
  obtain ⟨W, hWnew, hWeq⟩ := h420.wN_mem f hf
  have hWT : ∀ n : ℕ, 1 ≤ n → n.Coprime N → heckeT N k n W = μ n • ⇑W := by
    intro n hn hc
    rw [hWeq, ← hwN.comm n hn hc f, hμ n hn hc, wN_smul']
  obtain ⟨ε, hε⟩ := key W hWnew hWT
  have hwNf : wN N k f = ε • ⇑f := by
    rw [← hWeq, hε, FunLike.coe_smul]
  have hf_fun : ∃ z : ℍ, f z ≠ 0 := by
    by_contra h
    exact hf0 (DFunLike.coe_injective (funext fun z => by_contra fun hz => h ⟨z, hz⟩))
  obtain ⟨z0, hz0⟩ := hf_fun
  have hε1 : ε = 1 ∨ ε = -1 := by
    have h2 := congrFun (wN_wN (N := N) k f) z0
    rw [hwNf, wN_smul', hwNf] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have h3 : ε * ε = 1 := by
      have : (ε * ε) * f z0 = 1 * f z0 := by rw [one_mul, mul_assoc]; exact h2
      exact mul_right_cancel₀ hz0 this
    exact mul_self_eq_one_iff.mp h3
  -- eigenvector of all `T(n)`
  have hall : ∀ n : ℕ, 1 ≤ n → ∃ l : ℂ, heckeT N k n f = l • ⇑f := by
    intro n hn
    obtain ⟨G, hGnew, hGeq⟩ := h420.heckeT_mem n hn f hf
    have hGT : ∀ m : ℕ, 1 ≤ m → m.Coprime N → heckeT N k m G = μ m • ⇑G := by
      intro m hm hc
      rw [hGeq, h47.comm m n hm hn f, hμ m hm hc, heckeT_smul']
    obtain ⟨c, hc⟩ := key G hGnew hGT
    exact ⟨c, by rw [← hGeq, hc, FunLike.coe_smul]⟩
  choose! lam hlam using hall
  have hc1 : (qExpansion 1 ⇑f).coeff 1 ≠ 0 := coeff_one_ne_zero_of_eigen f hf0 lam hlam
  set c1 : ℂ := (qExpansion 1 ⇑f).coeff 1 with hc1def
  have hF1 : (qExpansion 1 ⇑(c1⁻¹ • f)).coeff 1 = 1 := by
    rw [qExpansion_coeff_smul_cuspForm, ← hc1def, inv_mul_cancel₀ hc1]
  have hFT : ∀ n : ℕ, 1 ≤ n → heckeT N k n ⇑(c1⁻¹ • f) = lam n • ⇑(c1⁻¹ • f) := by
    intro n hn
    rw [FunLike.coe_smul, heckeT_smul', hlam n hn, smul_comm]
  have hwF : wN N k ⇑(c1⁻¹ • f) = ε • ⇑(c1⁻¹ • f) := by
    rw [FunLike.coe_smul, wN_smul', hwNf, smul_comm]
  refine ⟨⟨ε, hε1, hwNf⟩, fun n hn => ⟨lam n, hlam n hn⟩, hc1,
    c1⁻¹ • f, ⟨_, rfl⟩, hF1, ?_, cor_4_9 hk h47 _ lam hFT hF1,
    ε, hε1, hwF, (thm_4_4 hk _ hε1 hwF).2.2⟩
  rintro G ⟨d, rfl⟩ hG
  rw [qExpansion_coeff_smul_cuspForm] at hG
  rw [eq_inv_of_mul_eq_one_left hG]

end NumberFieldKB.MilneEC.V
