import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Instances.Matrix
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, IV.§3, text p. 71: units of an algebra over a topological field

$K$ is a Hausdorff topological field, $E=K^n$ (with the product topology), and $\mathcal A$ a finite-dimensional
$K$-algebra with its natural topology (the module topology, `IsModuleTopology K A`: the topology of $K^r$ in any
basis).

* **`weil_IV_3_text71_aut`**: $\operatorname{Aut}(E)=\operatorname{End}(E)^\times$ is the set $\det\neq0$, and it is
  open in $\operatorname{End}(E)=M_n(K)$.
* **`weil_IV_3_text71_units`**: $\mathcal A^\times$ is open in $\mathcal A$.
* **`weil_IV_3_text71_regular`**: for a basis $b$ of $\mathcal A$, the regular representation
  $\rho:x\mapsto(\text{matrix of }y\mapsto xy)$ (`Algebra.leftMulMatrix b`) is an injective algebra homomorphism
  $\mathcal A\to M_r(K)$ and a topological embedding, i.e. a topological isomorphism onto its image (a subalgebra).
-/

open Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

/-- **Weil, IV.§3, text p. 71** (first sentence): in $\operatorname{End}(K^n)=M_n(K)$ the automorphisms are the
matrices with $\det\neq0$, and they form an open set. -/
@[kb "weil1973bnt" "Ch. IV, §3, text p. 71 (Aut(E) is the open set det ≠ 0)"]
theorem weil_IV_3_text71_aut (n : ℕ) :
    {g : Matrix (Fin n) (Fin n) K | IsUnit g} = {g | g.det ≠ 0} ∧
      IsOpen {g : Matrix (Fin n) (Fin n) K | IsUnit g} := by
  have h : {g : Matrix (Fin n) (Fin n) K | IsUnit g} = {g | g.det ≠ 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  refine ⟨h, ?_⟩
  rw [h]
  exact (isOpen_ne_fun continuous_id.matrix_det continuous_const)

variable {A : Type*} [Ring A] [Algebra K A] [FiniteDimensional K A] [TopologicalSpace A] [IsModuleTopology K A]

/-- **Weil, IV.§3, text p. 71**: the regular representation of a finite-dimensional algebra in a basis $b$ is an
injective algebra homomorphism into matrices and a topological embedding. -/
@[kb "weil1973bnt" "Ch. IV, §3, text p. 71 (the regular representation is a topological isomorphism onto its image)"]
theorem weil_IV_3_text71_regular {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K A) :
    Function.Injective (Algebra.leftMulMatrix b) ∧ IsEmbedding (Algebra.leftMulMatrix b) := by
  have : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A
  have hcont : Continuous (Algebra.leftMulMatrix b) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    let l : A →ₗ[K] K :=
      { toFun := fun x => Algebra.leftMulMatrix b x i j
        map_add' := fun x y => by simp
        map_smul' := fun c x => by simp }
    exact IsModuleTopology.continuous_of_linearMap l
  refine ⟨Algebra.leftMulMatrix_injective b, ?_⟩
  have hsymm : Continuous (b.equivFun.symm : (ι → K) → A) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.symm : (ι → K) →ₗ[K] A)
  refine Function.LeftInverse.isEmbedding (f := fun M : Matrix ι ι K => b.equivFun.symm (M.mulVec (b.equivFun 1)))
    ?_ ?_ hcont
  · intro x
    have := Algebra.leftMulMatrix_mulVec_repr b x 1
    simp only [mul_one] at this
    show b.equivFun.symm ((Algebra.leftMulMatrix b x).mulVec (b.equivFun 1)) = x
    have h2 : (Algebra.leftMulMatrix b x).mulVec (b.equivFun 1) = b.equivFun x := this
    rw [h2]; simp
  · exact hsymm.comp (Continuous.matrix_mulVec continuous_id continuous_const)

include K in
/-- **Weil, IV.§3, text p. 71**: the group of invertible elements of a finite-dimensional algebra is open. -/
@[kb "weil1973bnt" "Ch. IV, §3, text p. 71 (the units of a finite-dimensional algebra form an open set)"]
theorem weil_IV_3_text71_units : IsOpen {x : A | IsUnit x} := by
  classical
  let b := Module.finBasis K A
  have key : {x : A | IsUnit x} = (fun x => (Algebra.leftMulMatrix b x).det) ⁻¹' {0}ᶜ := by
    have rinv : ∀ x : A, (Algebra.leftMulMatrix b x).det ≠ 0 → ∃ y, x * y = 1 := by
      intro x hx
      have hu : IsUnit (Algebra.leftMulMatrix b x) := by
        rw [Matrix.isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.mpr hx
      obtain ⟨N, hN⟩ := hu.exists_right_inv
      refine ⟨b.equivFun.symm (N.mulVec (b.equivFun 1)), b.equivFun.injective ?_⟩
      have h1 := Algebra.leftMulMatrix_mulVec_repr b x (b.equivFun.symm (N.mulVec (b.equivFun 1)))
      have h2 : b.equivFun (x * b.equivFun.symm (N.mulVec (b.equivFun 1))) =
          (Algebra.leftMulMatrix b x).mulVec (b.equivFun (b.equivFun.symm (N.mulVec (b.equivFun 1)))) := h1.symm
      rw [h2, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hN, Matrix.one_mulVec]
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro hx
      have := (RingHom.isUnit_map (Algebra.leftMulMatrix b).toRingHom hx)
      have h2 := (Matrix.isUnit_iff_isUnit_det _).mp this
      exact isUnit_iff_ne_zero.mp h2
    · intro hx
      obtain ⟨y, hy⟩ := rinv x hx
      have hdy : (Algebra.leftMulMatrix b y).det ≠ 0 := by
        have : (Algebra.leftMulMatrix b x).det * (Algebra.leftMulMatrix b y).det = 1 := by
          rw [← Matrix.det_mul, ← map_mul, hy, map_one, Matrix.det_one]
        intro h0; rw [h0, mul_zero] at this; exact zero_ne_one this
      obtain ⟨z, hz⟩ := rinv y hdy
      have : z = x := by
        calc z = (x * y) * z := by rw [hy, one_mul]
          _ = x * (y * z) := mul_assoc _ _ _
          _ = x := by rw [hz, mul_one]
      subst this
      exact Units.isUnit ⟨z, y, hy, hz⟩
  rw [key]
  have hcont : Continuous (Algebra.leftMulMatrix b) :=
    (weil_IV_3_text71_regular b).2.continuous
  exact (isOpen_compl_singleton).preimage (hcont.matrix_det)

end NumberFieldKB.WeilBNT
