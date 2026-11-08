import NumberFieldKB.Pontryagin.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Characters of a compact commutative group: orthogonality and density
$K$ is a compact commutative topological group, $\mu$ a left-invariant probability measure on it (the normalized Haar
measure).

* `integral_char_eq_zero`: $\int_K\chi\,d\mu=0$ for every character $\chi\ne1$ (orthogonality).
* `integral_mul_eq_zero_of_separates`: if a subgroup $S$ of characters separates the points of $K$ and a continuous
  $F$ satisfies $\int\chi F\,d\mu=0$ for all $\chi\in S$, then $\int fF\,d\mu=0$ for every continuous $f$. The proof is
  Stone–Weierstrass: the span of $S$ is a $*$-subalgebra of $C(K,\mathbb C)$ (closed under products and complex
  conjugation, since $\bar\chi=\chi^{-1}$), it separates points, so it is dense.
* `mem_of_separates`: **a subgroup of characters that separates the points of a compact group contains every
  character.** (If $\psi\notin S$, then $\int\chi\psi\,d\mu=0$ for $\chi\in S$, hence $\int\bar\psi\psi\,d\mu=0$, but
  $|\psi|=1$.)
-/

open MeasureTheory Topology Pointwise

noncomputable section

namespace NumberFieldKB.Pontryagin

@[simp]
lemma dual_mul_apply {A : Type*} [CommGroup A] [TopologicalSpace A] (χ ψ : PontryaginDual A) (g : A) :
    (χ * ψ) g = χ g * ψ g := rfl

@[simp]
lemma dual_inv_apply {A : Type*} [CommGroup A] [TopologicalSpace A] (χ : PontryaginDual A) (g : A) :
    χ⁻¹ g = (χ g)⁻¹ := rfl

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

/-- A character as a continuous complex-valued function. -/
def charToC (χ : PontryaginDual K) : C(K, ℂ) :=
  ⟨fun g => ((χ g : Circle) : ℂ), continuous_subtype_val.comp χ.continuous⟩

@[simp]
lemma charToC_apply (χ : PontryaginDual K) (g : K) : charToC χ g = ((χ g : Circle) : ℂ) := rfl

lemma charToC_mul (χ ψ : PontryaginDual K) : charToC (χ * ψ) = charToC χ * charToC ψ := by
  ext g; simp [charToC]

lemma charToC_one : charToC (1 : PontryaginDual K) = 1 := by
  ext g; simp [charToC]

lemma star_charToC (χ : PontryaginDual K) : star (charToC χ) = charToC χ⁻¹ := by
  ext g
  simp only [ContinuousMap.star_apply, charToC_apply]
  change (starRingEnd ℂ) ((χ g : Circle) : ℂ) = (((χ g)⁻¹ : Circle) : ℂ)
  rw [Circle.coe_inv_eq_conj]

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsProbabilityMeasure μ]

lemma integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {f : K → E} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- **Orthogonality**: the integral of a non-trivial character over a compact group is $0$. -/
theorem integral_char_eq_zero [μ.IsMulLeftInvariant] {χ : PontryaginDual K} (hχ : χ ≠ 1) :
    ∫ g, ((χ g : Circle) : ℂ) ∂μ = 0 := by
  obtain ⟨h, hh⟩ : ∃ h, χ h ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hχ (PontryaginDual.ext fun a => by simpa using hcon a)
  have key : ∫ g, ((χ (h * g) : Circle) : ℂ) ∂μ = ∫ g, ((χ g : Circle) : ℂ) ∂μ :=
    integral_mul_left_eq_self (fun g => ((χ g : Circle) : ℂ)) h
  simp only [map_mul, Circle.coe_mul] at key
  rw [integral_const_mul] at key
  have hne : ((χ h : Circle) : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro e
    exact hh (Subtype.ext e)
  have h0 : (((χ h : Circle) : ℂ) - 1) * ∫ g, ((χ g : Circle) : ℂ) ∂μ = 0 := by
    rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left hne

/-- The integral of the trivial character is $1$. -/
theorem integral_char_one : ∫ _g : K, (((1 : PontryaginDual K) _g : Circle) : ℂ) ∂μ = 1 := by
  simp

/-- The continuous linear functional $f\mapsto\int fF\,d\mu$ on $C(K,\mathbb C)$, for continuous $F$. -/
def integralMulCLM {F : K → ℂ} (hF : Continuous F) : C(K, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ g, f g * F g ∂μ
      map_add' := fun f f' => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (integrable_of_continuous μ (f.continuous.mul hF))
          (integrable_of_continuous μ (f'.continuous.mul hF))
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
    (∫ g, ‖F g‖ ∂μ) (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ g, f g * F g ∂μ‖ ≤ ∫ g, ‖f‖ * ‖F g‖ ∂μ := by
            refine norm_integral_le_of_norm_le
              (integrable_of_continuous μ (continuous_const.mul hF.norm)) ?_
            exact Filter.Eventually.of_forall fun g => by
                rw [norm_mul]; gcongr; exact f.norm_coe_le_norm g
        _ = (∫ g, ‖F g‖ ∂μ) * ‖f‖ := by rw [integral_const_mul, mul_comm])

@[simp]
lemma integralMulCLM_apply {F : K → ℂ} (hF : Continuous F) (f : C(K, ℂ)) :
    integralMulCLM μ hF f = ∫ g, f g * F g ∂μ := rfl

/-- The span of a subgroup of characters, as a $*$-subalgebra of $C(K,\mathbb C)$. -/
def charSpan (S : Subgroup (PontryaginDual K)) : StarSubalgebra ℂ C(K, ℂ) where
  carrier := Submodule.span ℂ (charToC '' (S : Set (PontryaginDual K)))
  mul_mem' := by
    intro a b ha hb
    have hT : charToC '' (S : Set (PontryaginDual K)) * charToC '' (S : Set (PontryaginDual K)) ⊆
        charToC '' (S : Set (PontryaginDual K)) := by
      rintro _ ⟨_, ⟨χ, hχ, rfl⟩, _, ⟨ψ, hψ, rfl⟩, rfl⟩
      exact ⟨χ * ψ, S.mul_mem hχ hψ, charToC_mul χ ψ⟩
    have := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at this
    exact Submodule.span_mono hT this
  one_mem' := Submodule.subset_span ⟨1, S.one_mem, charToC_one⟩
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨1, S.one_mem, charToC_one⟩)
  star_mem' := by
    intro a ha
    simp only [SetLike.mem_coe] at ha ⊢
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨χ, hχ, rfl⟩ := hx
      rw [star_charToC]
      exact Submodule.subset_span ⟨χ⁻¹, S.inv_mem hχ, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

/-- If a subgroup of characters separates points, every continuous $F$ orthogonal to it (in the sense
$\int\chi F\,d\mu=0$) is orthogonal to every continuous function. -/
theorem integral_mul_eq_zero_of_separates (S : Subgroup (PontryaginDual K))
    (hS : ∀ x y : K, x ≠ y → ∃ χ ∈ S, χ x ≠ χ y) {F : K → ℂ} (hF : Continuous F)
    (h : ∀ χ ∈ S, ∫ g, ((χ g : Circle) : ℂ) * F g ∂μ = 0) (f : C(K, ℂ)) :
    ∫ g, f g * F g ∂μ = 0 := by
  have hsep : (charSpan S).SeparatesPoints := by
    intro x y hxy
    obtain ⟨χ, hχ, hne⟩ := hS x y hxy
    refine ⟨charToC χ, ⟨charToC χ, Submodule.subset_span ⟨χ, hχ, rfl⟩, rfl⟩, ?_⟩
    intro e
    exact hne (Subtype.ext e)
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  let Z : Submodule ℂ C(K, ℂ) := LinearMap.ker (integralMulCLM μ hF).toLinearMap
  have hZ : IsClosed (Z : Set C(K, ℂ)) :=
    isClosed_eq (integralMulCLM μ hF).continuous continuous_const
  have hsub : (charSpan S : Set C(K, ℂ)) ⊆ Z := by
    intro a ha
    change a ∈ Submodule.span ℂ _ at ha
    refine Submodule.span_le.mpr ?_ ha
    rintro _ ⟨χ, hχ, rfl⟩
    change integralMulCLM μ hF (charToC χ) = 0
    simpa using h χ hχ
  have hcl : closure (charSpan S : Set C(K, ℂ)) ⊆ Z := closure_minimal hsub hZ
  have hf : f ∈ closure (charSpan S : Set C(K, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]
    trivial
  have := hcl hf
  simpa [Z] using this

/-- **A subgroup of characters separating the points of a compact group contains every character.** -/
theorem mem_of_separates' [μ.IsMulLeftInvariant] (S : Subgroup (PontryaginDual K))
    (hS : ∀ x y : K, x ≠ y → ∃ χ ∈ S, χ x ≠ χ y) (ψ : PontryaginDual K) : ψ ∈ S := by
  by_contra hψ
  have h : ∀ χ ∈ S, ∫ g, ((χ g : Circle) : ℂ) * ((ψ g : Circle) : ℂ) ∂μ = 0 := by
    intro χ hχ
    have hne : χ * ψ ≠ 1 := by
      intro e
      apply hψ
      have : ψ = χ⁻¹ := eq_inv_of_mul_eq_one_right e
      rw [this]
      exact S.inv_mem hχ
    have := integral_char_eq_zero μ hne
    simpa using this
  have h0 := integral_mul_eq_zero_of_separates μ S hS (charToC ψ).continuous h (star (charToC ψ))
  rw [star_charToC] at h0
  have h1 : ∀ g, (charToC ψ⁻¹) g * ((ψ g : Circle) : ℂ) = 1 := by
    intro g
    simp only [charToC_apply]
    change (((ψ g)⁻¹ : Circle) : ℂ) * ((ψ g : Circle) : ℂ) = 1
    rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  have h2 : ∫ g, (charToC ψ⁻¹) g * ((ψ g : Circle) : ℂ) ∂μ = 1 := by
    simp_rw [h1]; simp
  exact one_ne_zero (h2.symm.trans h0)

/-- A left-invariant probability measure on a compact group (the normalized Haar measure) exists. -/
theorem exists_haar_probability [T2Space K] :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant := by
  let K₀ : TopologicalSpace.PositiveCompacts K := ⊤
  refine ⟨Measure.haarMeasure K₀, ⟨?_⟩, inferInstance⟩
  have := Measure.haarMeasure_self (K₀ := K₀)
  simpa [K₀] using this

end NumberFieldKB.Pontryagin

namespace NumberFieldKB.Pontryagin

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K]

/-- **A subgroup of characters separating the points of a compact Hausdorff group contains every character.** -/
theorem mem_of_separates (S : Subgroup (PontryaginDual K))
    (hS : ∀ x y : K, x ≠ y → ∃ χ ∈ S, χ x ≠ χ y) (ψ : PontryaginDual K) : ψ ∈ S := by
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨μ, hμ, hinv⟩ := exists_haar_probability (K := K)
  exact mem_of_separates' μ S hS ψ

end NumberFieldKB.Pontryagin
