import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter V, Section 4: the spectral theorem and the invariant measure

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, subsections "Linear algebra: the spectral theorem" and "The
Petersson inner product" (pdf pp. 212–213).

* **Theorem 4.16** (spectral theorem): Mathlib's `LinearMap.IsSymmetric.direct_sum_isInternal` (part (a)) and
  `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute` (joint eigenspaces); restated in Milne's form as
  `thm_4_16_a` and `thm_4_16_b` (a basis of common eigenvectors). Milne's "positive-definite hermitian form" is the
  inner product of a complex inner product space, "self-adjoint" is `LinearMap.IsSymmetric`.
* **Proposition 4.17**: Mathlib proves invariance of $dx\,dy/y^2$ under $\mathrm{GL}_2(\mathbb R)$ (the instance
  `SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume` in `Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`, whose
  `volume` is `UpperHalfPlane.volume_def`); `prop_4_17` restates it for $\mathrm{SL}_2(\mathbb R)$.
* **Lemma 4.18** (`lemma_4_18`, `lemma_4_18_area`): a holomorphic map multiplies areas by $|w'(z)|^2$.
-/

open MeasureTheory Module
open scoped Pointwise MatrixGroups

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

/-- **Theorem 4.16(a)** (Milne, *EC*, V, Theorem 4.16(a), p. 212; Mathlib
`LinearMap.IsSymmetric.direct_sum_isInternal`): a self-adjoint linear map of a finite-dimensional complex inner
product space is diagonalizable, i.e. $V$ is the direct sum of its eigenspaces. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.16(a) (pdf p. 212); Mathlib LinearMap.IsSymmetric.direct_sum_isInternal"]
theorem thm_4_16_a {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {α : V →ₗ[ℂ] V} (hα : α.IsSymmetric) :
    DirectSum.IsInternal fun μ : Module.End.Eigenvalues α => Module.End.eigenspace α μ :=
  hα.direct_sum_isInternal

/-- **Theorem 4.16(b)** (Milne, *EC*, V, Theorem 4.16(b), p. 212; from Mathlib
`LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`): a commuting family of self-adjoint linear maps
of a finite-dimensional complex inner product space has a basis of common eigenvectors. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.16(b) (pdf p. 212)"]
theorem thm_4_16_b {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {ι : Type*} {α : ι → V →ₗ[ℂ] V} (hα : ∀ i, (α i).IsSymmetric) (hc : ∀ i j, Commute (α i) (α j)) :
    ∃ (κ : Type*) (b : Basis κ ℂ V), ∀ i k, ∃ μ : ℂ, α i (b k) = μ • b k := by
  classical
  have hint := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hα
    (fun i j _ => hc i j)
  let bs : ∀ χ : ι → ℂ, Module.Basis (Module.Free.ChooseBasisIndex ℂ
        (⨅ j, Module.End.eigenspace (α j) (χ j) : Submodule ℂ V))
      ℂ (⨅ j, Module.End.eigenspace (α j) (χ j) : Submodule ℂ V) :=
    fun χ => Module.Free.chooseBasis ℂ _
  let B := hint.collectedBasis bs
  have : Finite (Σ χ : ι → ℂ, Module.Free.ChooseBasisIndex ℂ
        (⨅ j, Module.End.eigenspace (α j) (χ j) : Submodule ℂ V)) := Module.Finite.finite_basis B
  let e := B.indexEquiv (Module.finBasis ℂ V)
  refine ⟨ULift (Fin (Module.finrank ℂ V)), B.reindex (e.trans Equiv.ulift.symm), ?_⟩
  intro i k
  rw [Module.Basis.reindex_apply]
  generalize (e.trans Equiv.ulift.symm).symm k = x
  obtain ⟨χ, a⟩ := x
  have hmem : (B ⟨χ, a⟩ : V) ∈ ⨅ j, Module.End.eigenspace (α j) (χ j) := by
    have : B ⟨χ, a⟩ = ((bs χ a : (⨅ j, Module.End.eigenspace (α j) (χ j) : Submodule ℂ V)) : V) := by
      simp [B]
    rw [this]
    exact (bs χ a).2
  rw [Submodule.mem_iInf] at hmem
  exact ⟨χ i, Module.End.mem_eigenspace_iff.mp (hmem i)⟩

/-- **Proposition 4.17** (Milne, *EC*, V, Proposition 4.17, p. 213): the measure $\mu(U) = \iint_U dx\,dy/y^2$ on the
upper half-plane (Mathlib's `volume` on `ℍ`, `UpperHalfPlane.volume_def`) satisfies $\mu(\gamma U) = \mu(U)$ for
all $\gamma \in \mathrm{SL}_2(\mathbb R)$. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.17 (pdf p. 213)"]
theorem prop_4_17 (γ : SL(2, ℝ)) (U : Set UpperHalfPlane) :
    volume (γ • U) = volume U := by
  have h : γ • U = (Matrix.SpecialLinearGroup.mapGL ℝ γ) • U := rfl
  rw [h]
  exact measure_smul _ _ _

/-- **Lemma 4.18, pointwise form** (Milne, *EC*, V, Lemma 4.18, p. 213): if $w$ is complex differentiable at $z$,
the jacobian determinant of $z \mapsto w(z)$ (as a map $\mathbb R^2 \to \mathbb R^2$) is $|w'(z)|^2$. -/
@[kb "milne2006ec" "Ch. V, Lemma 4.18 (pdf p. 213): the jacobian is |w'|^2"]
theorem lemma_4_18 {w : ℂ → ℂ} {z : ℂ} (hw : DifferentiableAt ℂ w z) :
    (fderiv ℝ w z).det = ‖deriv w z‖ ^ 2 := by
  have h1 := hw.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  rw [h1.fderiv, ContinuousLinearMap.det]
  have : ((ContinuousLinearMap.toSpanSingleton ℂ (deriv w z)).restrictScalars ℝ : ℂ →ₗ[ℝ] ℂ)
      = LinearMap.mulLeft ℝ (deriv w z) := by
    ext x <;> simp [mul_comm]
  rw [this]
  have h2 : LinearMap.mulLeft ℝ (deriv w z) = Algebra.lmul ℝ ℂ (deriv w z) := rfl
  rw [h2, ← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

/-- **Lemma 4.18** (Milne, *EC*, V, Lemma 4.18, p. 213): a holomorphic map $w$ multiplies areas by $|w'(z)|^2$: for
$w$ holomorphic and injective on an open set $s$, the area of $w(s)$ is $\int_s |w'(z)|^2\,dx\,dy$. -/
@[kb "milne2006ec" "Ch. V, Lemma 4.18 (pdf p. 213)"]
theorem lemma_4_18_area {w : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hw : DifferentiableOn ℂ w s)
    (hinj : Set.InjOn w s) :
    volume (w '' s) = ∫⁻ z in s, ENNReal.ofReal (‖deriv w z‖ ^ 2) := by
  have hd : ∀ x ∈ s, HasFDerivWithinAt w (fderiv ℝ w x) s x := fun x hx =>
    ((hw.differentiableAt (hs.mem_nhds hx)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have := lintegral_abs_det_fderiv_eq_addHaar_image volume hs.measurableSet hd hinj
  rw [← this]
  refine setLIntegral_congr_fun hs.measurableSet (fun z hz => ?_)
  rw [lemma_4_18 (hw.differentiableAt (hs.mem_nhds hz)), abs_of_nonneg (by positivity)]

end NumberFieldKB.MilneEC.Vb
