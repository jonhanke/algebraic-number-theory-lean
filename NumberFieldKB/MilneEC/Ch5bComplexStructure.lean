import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import QuadFormsKB.Citation
import Mathlib.Control.Traversable.Equiv

/-!
# Milne, *Elliptic Curves*, Chapter V, Section 7: real vector spaces with a complex structure

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Section 7, "The action of the Hecke operators on
$H_1(E, \mathbb Z)$" (pdf pp. 228–229): Proposition 7.7, Corollary 7.8, and the linear algebra behind Remark 6.2
and Corollary 7.9.

**Setting.** Milne takes a real vector space $V$ with an $\mathbb R$-linear $J$, $J^2 = -1$ (a complex structure).
Here $V$ is a complex vector space (so $J$ is multiplication by $i$) regarded as a real vector space by restriction
of scalars; this is the same datum. Milne's $V \otimes_{\mathbb R} \mathbb C$ is Mathlib's $\mathbb C \otimes_{\mathbb R}
V$ (complex structure on the left factor), $J_{\mathbb C} = \mathrm{id} \otimes J$.

**Correction.** The text calls $V^{\pm}$ "the $\pm 1$ eigenspaces of
$J$"; since $J^2 = -1$ these are the $\pm i$ eigenspaces of $J_{\mathbb C}$ (the $\pm 1$ eigenspaces are zero).

**Remark 6.2 and Corollary 7.9.** Milne applies the linear algebra to $T(n)$ acting on
$H_1(X_0(N), \mathbb Z) \subset \Omega^1(X_0(N))^\vee$. The modular curve, its homology and its differentials are not
formalized; `remark_6_2_lattice` and `cor_7_9_lattice` are the statements for any $\mathbb Z$-lattice
$H \subset V$ (the $\mathbb Z$-span of an $\mathbb R$-basis) stable under a $\mathbb C$-linear $\alpha$, which is
exactly what the proofs use.
-/

open Complex TensorProduct Module

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Close module equations over `ℂ` using `I ^ 2 = -1`. -/
macro "cx_scalars" : tactic =>
  `(tactic| (match_scalars <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring_nf)))

/-- The complex structure $J$ of $V$ (multiplication by $i$), as an $\mathbb R$-linear map. -/
def cxJ (V : Type*) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℝ] V :=
  (I • LinearMap.id : V →ₗ[ℂ] V).restrictScalars ℝ

/-- $J_{\mathbb C} = \mathrm{id} \otimes J$ on $\mathbb C \otimes_{\mathbb R} V$. -/
def cxJC (V : Type*) [AddCommGroup V] [Module ℂ V] : (ℂ ⊗[ℝ] V) →ₗ[ℂ] (ℂ ⊗[ℝ] V) :=
  (cxJ V).baseChange ℂ

/-- $V^+$, the $+i$ eigenspace of $J_{\mathbb C}$. -/
def cxPlus (V : Type*) [AddCommGroup V] [Module ℂ V] : Submodule ℂ (ℂ ⊗[ℝ] V) :=
  Module.End.eigenspace (cxJC V) I

/-- $V^-$, the $-i$ eigenspace of $J_{\mathbb C}$. -/
def cxMinus (V : Type*) [AddCommGroup V] [Module ℂ V] : Submodule ℂ (ℂ ⊗[ℝ] V) :=
  Module.End.eigenspace (cxJC V) (-I)

@[simp] lemma cxJC_tmul (z : ℂ) (v : V) : cxJC V (z ⊗ₜ[ℝ] v) = z ⊗ₜ[ℝ] (I • v) := by
  simp [cxJC, cxJ]

lemma cxJC_cxJC (x : ℂ ⊗[ℝ] V) : cxJC V (cxJC V x) = -x := by
  induction x using TensorProduct.inductionOn with
  | tmul z v => simp [smul_smul, TensorProduct.tmul_neg]
  | add x y hx hy => simp [hx, hy, add_comm]

/-- The projection onto $V^+$: $x \mapsto \tfrac12(x - i J_{\mathbb C} x)$. -/
def cxPp (V : Type*) [AddCommGroup V] [Module ℂ V] : (ℂ ⊗[ℝ] V) →ₗ[ℂ] (ℂ ⊗[ℝ] V) :=
  (1 / 2 : ℂ) • (LinearMap.id - I • cxJC V)

/-- The projection onto $V^-$: $x \mapsto \tfrac12(x + i J_{\mathbb C} x)$. -/
def cxPm (V : Type*) [AddCommGroup V] [Module ℂ V] : (ℂ ⊗[ℝ] V) →ₗ[ℂ] (ℂ ⊗[ℝ] V) :=
  (1 / 2 : ℂ) • (LinearMap.id + I • cxJC V)

lemma cxPp_apply (x : ℂ ⊗[ℝ] V) : cxPp V x = (1 / 2 : ℂ) • (x - I • cxJC V x) := by
  simp [cxPp]

lemma cxPm_apply (x : ℂ ⊗[ℝ] V) : cxPm V x = (1 / 2 : ℂ) • (x + I • cxJC V x) := by
  simp [cxPm]

lemma cxPp_mem (x : ℂ ⊗[ℝ] V) : cxPp V x ∈ cxPlus V := by
  rw [cxPlus, Module.End.mem_eigenspace_iff, cxPp_apply, map_smul, map_sub, map_smul, cxJC_cxJC]
  cx_scalars

lemma cxPm_mem (x : ℂ ⊗[ℝ] V) : cxPm V x ∈ cxMinus V := by
  rw [cxMinus, Module.End.mem_eigenspace_iff, cxPm_apply, map_smul, map_add, map_smul, cxJC_cxJC]
  cx_scalars

lemma cxPp_of_mem {x : ℂ ⊗[ℝ] V} (hx : x ∈ cxPlus V) : cxPp V x = x := by
  rw [cxPlus, Module.End.mem_eigenspace_iff] at hx
  rw [cxPp_apply, hx]
  cx_scalars

lemma cxPp_cxJC (x : ℂ ⊗[ℝ] V) : cxPp V (cxJC V x) = I • cxPp V x := by
  rw [cxPp_apply, cxPp_apply, cxJC_cxJC]
  cx_scalars

/-- Milne, *EC*, V.7, p. 228 (running text): $V \otimes_{\mathbb R} \mathbb C = V^+ \oplus V^-$. -/
@[kb "milne2006ec" "Ch. V, Section 7 (pdf p. 228): V ⊗ C = V⁺ ⊕ V⁻"]
theorem cx_isCompl : IsCompl (cxPlus V) (cxMinus V) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x h1 h2
    rw [cxPlus, Module.End.mem_eigenspace_iff] at h1
    rw [cxMinus, Module.End.mem_eigenspace_iff] at h2
    have h3 : (2 * I : ℂ) • x = 0 := by
      have : I • x - (-I) • x = 0 := by rw [← h1, ← h2, sub_self]
      rw [← this]
      module
    have h4 : (2 * I : ℂ) ≠ 0 := by simp
    exact (smul_eq_zero.mp h3).resolve_left h4
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = cxPp V x + cxPm V x := by
      simp only [cxPp_apply, cxPm_apply]
      cx_scalars
    rw [hx]
    exact Submodule.add_mem_sup (cxPp_mem x) (cxPm_mem x)

/-- The $\mathbb R$-linear multiplication map $\mathbb C \otimes_{\mathbb R} V \to V$, $z \otimes v \mapsto z v$. -/
def cxMul (V : Type*) [AddCommGroup V] [Module ℂ V] : (ℂ ⊗[ℝ] V) →ₗ[ℝ] V :=
  TensorProduct.lift
    (LinearMap.mk₂ ℝ (fun (z : ℂ) (v : V) => z • v) (fun _ _ _ => add_smul _ _ _)
      (fun r z v => smul_assoc r z v) (fun _ _ _ => smul_add _ _ _)
      (fun r z v => smul_comm z r v))

@[simp] lemma cxMul_tmul (z : ℂ) (v : V) : cxMul V (z ⊗ₜ[ℝ] v) = z • v := by
  simp [cxMul]

lemma cxMul_smul (c : ℂ) (x : ℂ ⊗[ℝ] V) : cxMul V (c • x) = c • cxMul V x := by
  induction x using TensorProduct.inductionOn with
  | tmul z v => simp [TensorProduct.smul_tmul', mul_smul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

lemma cxPp_one_tmul_smul (c : ℂ) (v : V) :
    cxPp V ((1 : ℂ) ⊗ₜ[ℝ] (c • v)) = c • cxPp V ((1 : ℂ) ⊗ₜ[ℝ] v) := by
  have h : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (I • v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have h2 : (1 : ℂ) ⊗ₜ[ℝ] (I • v) = cxJC V ((1 : ℂ) ⊗ₜ[ℝ] v) := by simp
  rw [h, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, h2, map_add,
    LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, cxPp_cxJC, ← algebraMap_smul ℂ c.re,
    ← algebraMap_smul ℂ c.im, Complex.coe_algebraMap]
  conv_rhs => rw [← Complex.re_add_im c]
  cx_scalars

lemma cxPp_one_tmul_cxMul (x : ℂ ⊗[ℝ] V) : cxPp V ((1 : ℂ) ⊗ₜ[ℝ] (cxMul V x)) = cxPp V x := by
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
    rw [cxMul_tmul, cxPp_one_tmul_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, TensorProduct.tmul_add, map_add, hx, hy, map_add]

/-- **Proposition 7.7(a)** (Milne, *EC*, V, Proposition 7.7(a), p. 228): the map
$V \to V \otimes_{\mathbb R} \mathbb C \to V^+$, $v \mapsto v \otimes 1 \mapsto$ (its $V^+$ component
$\tfrac12(1 \otimes v - i \cdot (1 \otimes Jv))$), is an isomorphism of complex vector spaces. -/
@[kb "milne2006ec" "Ch. V, Proposition 7.7(a) (pdf p. 228)"]
theorem prop_7_7_a :
    (∀ v : V, (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] v - I • ((1 : ℂ) ⊗ₜ[ℝ] (I • v))) ∈ cxPlus V) ∧
    (∀ v : V, (1 : ℂ) ⊗ₜ[ℝ] v - (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] v - I • ((1 : ℂ) ⊗ₜ[ℝ] (I • v))) ∈ cxMinus V) ∧
    ∃ e : V ≃ₗ[ℂ] cxPlus V, ∀ v : V,
      (e v : ℂ ⊗[ℝ] V) = (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] v - I • ((1 : ℂ) ⊗ₜ[ℝ] (I • v))) := by
  have hform : ∀ v : V, (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] v - I • ((1 : ℂ) ⊗ₜ[ℝ] (I • v))) =
      cxPp V ((1 : ℂ) ⊗ₜ[ℝ] v) := by
    intro v
    rw [cxPp_apply, cxJC_tmul]
  have hm : ∀ v : V, cxMul V (cxPp V ((1 : ℂ) ⊗ₜ[ℝ] v)) = v := by
    intro v
    rw [cxPp_apply, cxMul_smul, map_sub, cxMul_smul, cxJC_tmul]
    simp only [cxMul_tmul, one_smul, smul_smul]
    cx_scalars
  refine ⟨?_, ?_, ?_⟩
  · intro v; rw [hform]; exact cxPp_mem _
  · intro v
    rw [hform]
    have : (1 : ℂ) ⊗ₜ[ℝ] v - cxPp V ((1 : ℂ) ⊗ₜ[ℝ] v) = cxPm V ((1 : ℂ) ⊗ₜ[ℝ] v) := by
      rw [cxPp_apply, cxPm_apply]; cx_scalars
    rw [this]; exact cxPm_mem _
  · let f : V →ₗ[ℂ] cxPlus V :=
      { toFun := fun v => ⟨cxPp V ((1 : ℂ) ⊗ₜ[ℝ] v), cxPp_mem _⟩
        map_add' := fun v w => by
          apply Subtype.ext
          simp [TensorProduct.tmul_add]
        map_smul' := fun c v => by
          apply Subtype.ext
          simp [cxPp_one_tmul_smul] }
    have hf : Function.Bijective f := by
      constructor
      · intro v w h
        have h' := congrArg (fun p : cxPlus V => cxMul V (p : ℂ ⊗[ℝ] V)) h
        simpa [f, hm] using h'
      · rintro ⟨p, hp⟩
        refine ⟨cxMul V p, Subtype.ext ?_⟩
        simp only [f, LinearMap.coe_mk, AddHom.coe_mk]
        rw [cxPp_one_tmul_cxMul, cxPp_of_mem hp]
    refine ⟨LinearEquiv.ofBijective f hf, fun v => ?_⟩
    rw [hform]
    rfl

/-- The $\mathbb R$-linear map $v \otimes z \mapsto v \otimes \bar z$ of $V \otimes_{\mathbb R} \mathbb C$. -/
def cxConj (V : Type*) [AddCommGroup V] [Module ℂ V] : (ℂ ⊗[ℝ] V) →ₗ[ℝ] (ℂ ⊗[ℝ] V) :=
  TensorProduct.map (conjAe.toLinearMap) LinearMap.id

@[simp] lemma cxConj_tmul (z : ℂ) (v : V) : cxConj V (z ⊗ₜ[ℝ] v) = (starRingEnd ℂ z) ⊗ₜ[ℝ] v := by
  simp [cxConj]

/-- **Proposition 7.7(b)** (Milne, *EC*, V, Proposition 7.7(b), p. 228): $v \otimes z \mapsto v \otimes \bar z$ is an
$\mathbb R$-linear involution of $V \otimes_{\mathbb R} \mathbb C$ interchanging $V^+$ and $V^-$. -/
@[kb "milne2006ec" "Ch. V, Proposition 7.7(b) (pdf p. 228)"]
theorem prop_7_7_b :
    cxConj V ∘ₗ cxConj V = LinearMap.id ∧
      ((cxPlus V).restrictScalars ℝ).map (cxConj V) = (cxMinus V).restrictScalars ℝ ∧
      ((cxMinus V).restrictScalars ℝ).map (cxConj V) = (cxPlus V).restrictScalars ℝ := by
  have hinv : ∀ x, cxConj V (cxConj V x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul z v => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsmul : ∀ (c : ℂ) x, cxConj V (c • x) = starRingEnd ℂ c • cxConj V x := by
    intro c x
    induction x using TensorProduct.inductionOn with
    | tmul z v => simp [TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  have hJ : ∀ x, cxConj V (cxJC V x) = cxJC V (cxConj V x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul z v => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hPM : ∀ x ∈ cxPlus V, cxConj V x ∈ cxMinus V := by
    intro x hx
    rw [cxPlus, Module.End.mem_eigenspace_iff] at hx
    rw [cxMinus, Module.End.mem_eigenspace_iff, ← hJ, hx, hsmul]
    simp
  have hMP : ∀ x ∈ cxMinus V, cxConj V x ∈ cxPlus V := by
    intro x hx
    rw [cxMinus, Module.End.mem_eigenspace_iff] at hx
    rw [cxPlus, Module.End.mem_eigenspace_iff, ← hJ, hx, hsmul]
    simp
  refine ⟨LinearMap.ext hinv, ?_, ?_⟩
  · ext x
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hPM y hy
    · intro hx
      exact ⟨cxConj V x, hMP x hx, hinv x⟩
  · ext x
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hMP y hy
    · intro hx
      exact ⟨cxConj V x, hPM x hx, hinv x⟩

/-- The $\mathbb R$-basis $(b_i, i b_i)$ of $V$, indexed by $\iota \sqcup \iota$, built from a
$\mathbb C$-basis $b$. -/
def cxRealBasis {ι : Type*} (b : Basis ι ℂ V) : Basis (ι ⊕ ι) ℝ V :=
  (Complex.basisOneI.smulTower b).reindex
    ((Equiv.prodCongr finTwoEquiv (Equiv.refl ι)).trans (Equiv.boolProdEquivSum ι))

@[simp] lemma cxRealBasis_inl {ι : Type*} (b : Basis ι ℂ V) (i : ι) : cxRealBasis b (Sum.inl i) = b i := by
  have h0 : (finTwoEquiv.symm false : Fin 2) = 0 := rfl
  simp [cxRealBasis, Basis.reindex_apply, Equiv.boolProdEquivSum, h0]

@[simp] lemma cxRealBasis_inr {ι : Type*} (b : Basis ι ℂ V) (i : ι) :
    cxRealBasis b (Sum.inr i) = I • b i := by
  have h1 : (finTwoEquiv.symm true : Fin 2) = 1 := rfl
  simp [cxRealBasis, Basis.reindex_apply, Equiv.boolProdEquivSum, h1]

/-- Coordinates of the real basis `cxRealBasis b` in terms of the complex coordinates. -/
lemma cxRealBasis_repr {ι : Type*} [Fintype ι] (b : Basis ι ℂ V) (w : V) :
    (cxRealBasis b).repr w = Sum.elim (fun i => (b.repr w i).re) (fun i => (b.repr w i).im) := by
  have h : ∑ k, (Sum.elim (fun i => (b.repr w i).re) (fun i => (b.repr w i).im) k) •
      cxRealBasis b k = w := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, cxRealBasis_inl, cxRealBasis_inr]
    conv_rhs => rw [← b.sum_repr w]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Complex.re_add_im (b.repr w i)]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have h2 := Basis.repr_sum_self (cxRealBasis b)
    (Sum.elim (fun i => (b.repr w i).re) (fun i => (b.repr w i).im))
  rw [h] at h2
  exact h2

/-- The matrix of a $\mathbb C$-linear map in the real basis `cxRealBasis b`. -/
lemma cxRealBasis_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ V) (α : V →ₗ[ℂ] V) :
    (LinearMap.toMatrix (cxRealBasis b) (cxRealBasis b) (α.restrictScalars ℝ)).map
        ((↑) : ℝ → ℂ) =
      Matrix.fromBlocks
        ((LinearMap.toMatrix b b α).map fun z => ((z.re : ℝ) : ℂ))
        (-((LinearMap.toMatrix b b α).map fun z => ((z.im : ℝ) : ℂ)))
        ((LinearMap.toMatrix b b α).map fun z => ((z.im : ℝ) : ℂ))
        ((LinearMap.toMatrix b b α).map fun z => ((z.re : ℝ) : ℂ)) := by
  ext (i | i) (j | j)
  · simp [LinearMap.toMatrix_apply, cxRealBasis_repr]
  · simp [LinearMap.toMatrix_apply, cxRealBasis_repr]
  · simp [LinearMap.toMatrix_apply, cxRealBasis_repr]
  · simp [LinearMap.toMatrix_apply, cxRealBasis_repr]

/-- The change of basis matrix $\begin{pmatrix}1 & 1\\ -i & i\end{pmatrix}$ from the eigenbasis. -/
def cxP0 (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 1 1 (-(I • 1)) (I • 1)

/-- The inverse $\tfrac12\begin{pmatrix}1 & i\\ 1 & -i\end{pmatrix}$ of `cxP0`. -/
def cxQ0 (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  (1 / 2 : ℂ) • Matrix.fromBlocks 1 (I • 1) 1 (-(I • 1))

lemma cxP0_mul_cxQ0 (ι : Type*) [Fintype ι] [DecidableEq ι] : cxP0 ι * cxQ0 ι = 1 := by
  rw [cxP0, cxQ0, Matrix.mul_smul, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_smul]
  congr 1 <;> simp <;> cx_scalars

lemma cxQ0_mul_cxP0 (ι : Type*) [Fintype ι] [DecidableEq ι] : cxQ0 ι * cxP0 ι = 1 := by
  rw [cxP0, cxQ0, Matrix.smul_mul, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_smul]
  congr 1 <;> simp <;> cx_scalars

lemma cxBlock_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℂ) :
    Matrix.fromBlocks X (-Y) Y X * cxP0 ι =
      cxP0 ι * Matrix.fromBlocks (X + I • Y) 0 0 (X - I • Y) := by
  rw [cxP0, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1 <;> simp <;> cx_scalars

/-- **Corollary 7.8** (Milne, *EC*, V, Corollary 7.8, p. 229): let $\alpha$ be a $\mathbb C$-linear endomorphism of
the finite-dimensional complex vector space $V$, $A$ its matrix as an $\mathbb R$-linear endomorphism (in an
$\mathbb R$-basis indexed by $\kappa$) and $A_1$ its matrix as a $\mathbb C$-linear endomorphism (in a
$\mathbb C$-basis indexed by $\iota$). Then $A \sim A_1 \oplus \bar A_1$: after an identification
$\kappa \simeq \iota \sqcup \iota$, $A$ is conjugate over $\mathbb C$ to the block matrix
$\begin{pmatrix} A_1 & 0 \\ 0 & \bar A_1\end{pmatrix}$. -/
@[kb "milne2006ec" "Ch. V, Corollary 7.8 (pdf p. 229)"]
theorem cor_7_8 [FiniteDimensional ℂ V] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℂ V) (b' : Basis κ ℝ V) (α : V →ₗ[ℂ] V) :
    ∃ (e : κ ≃ ι ⊕ ι) (P : GL (ι ⊕ ι) ℂ),
      ((LinearMap.toMatrix b' b' (α.restrictScalars ℝ)).map ((↑) : ℝ → ℂ)).reindex e e =
        (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) *
          Matrix.fromBlocks (LinearMap.toMatrix b b α) 0 0 ((LinearMap.toMatrix b b α).map (starRingEnd ℂ)) *
          ((P⁻¹ : GL (ι ⊕ ι) ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  classical
  set c : Basis (ι ⊕ ι) ℝ V := cxRealBasis b with hc
  let e : κ ≃ ι ⊕ ι := b'.indexEquiv c
  set d : Basis (ι ⊕ ι) ℝ V := b'.reindex e with hd
  set A := LinearMap.toMatrix b b α with hAdef
  set X : Matrix ι ι ℂ := A.map fun z => ((z.re : ℝ) : ℂ) with hX
  set Y : Matrix ι ι ℂ := A.map fun z => ((z.im : ℝ) : ℂ) with hY
  have hA : A = X + I • Y := by
    ext i j
    simp only [hX, hY, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have hAb : A.map (starRingEnd ℂ) = X - I • Y := by
    ext i j
    apply Complex.ext <;> simp [hX, hY]
  have hMc : (LinearMap.toMatrix c c (α.restrictScalars ℝ)).map ((↑) : ℝ → ℂ) =
      Matrix.fromBlocks X (-Y) Y X := cxRealBasis_toMatrix b α
  have hkey : (LinearMap.toMatrix c c (α.restrictScalars ℝ)).map ((↑) : ℝ → ℂ) =
      cxP0 ι * Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ)) * cxQ0 ι := by
    rw [hAb, hMc, hA]
    rw [← cxBlock_aux, mul_assoc, cxP0_mul_cxQ0, mul_one]
  have hre : ((LinearMap.toMatrix b' b' (α.restrictScalars ℝ)).map ((↑) : ℝ → ℂ)).reindex e e =
      (LinearMap.toMatrix d d (α.restrictScalars ℝ)).map ((↑) : ℝ → ℂ) := by
    ext i j
    simp [LinearMap.toMatrix_apply, hd, Basis.reindex_apply]
  have hT := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix d c d c
    (α.restrictScalars ℝ)
  have h1 := Basis.toMatrix_mul_toMatrix_flip d c
  have h2 := Basis.toMatrix_mul_toMatrix_flip c d
  let D : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := (d.toMatrix c).map ((↑) : ℝ → ℂ)
  let D' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := (c.toMatrix d).map ((↑) : ℝ → ℂ)
  have hDD' : D * D' = 1 := by
    have : Complex.ofRealHom.mapMatrix (d.toMatrix c * c.toMatrix d) = 1 := by rw [h1, map_one]
    rw [map_mul] at this
    exact this
  have hD'D : D' * D = 1 := by
    have : Complex.ofRealHom.mapMatrix (c.toMatrix d * d.toMatrix c) = 1 := by rw [h2, map_one]
    rw [map_mul] at this
    exact this
  have hT' : (LinearMap.toMatrix d d (α.restrictScalars ℝ)).map ((↑) : ℝ → ℂ) =
      D * (LinearMap.toMatrix c c (α.restrictScalars ℝ)).map ((↑) : ℝ → ℂ) * D' := by
    have := congrArg Complex.ofRealHom.mapMatrix hT
    rw [map_mul, map_mul] at this
    exact this.symm
  refine ⟨e, ⟨D * cxP0 ι, cxQ0 ι * D', ?_, ?_⟩, ?_⟩
  · rw [mul_assoc, ← mul_assoc (cxP0 ι), cxP0_mul_cxQ0, one_mul, hDD']
  · rw [mul_assoc, ← mul_assoc D', hD'D, one_mul, cxQ0_mul_cxP0]
  · show _ = D * cxP0 ι * _ * (cxQ0 ι * D')
    rw [hre, hT', hkey]
    simp only [mul_assoc]

/-- Trace form of Corollary 7.8 at the level of matrices. -/
lemma cx_trace_matrix [FiniteDimensional ℂ V] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (b : Basis ι ℂ V) (b' : Basis κ ℝ V) (α : V →ₗ[ℂ] V) :
    (((LinearMap.toMatrix b' b' (α.restrictScalars ℝ)).trace : ℝ) : ℂ) =
      (LinearMap.toMatrix b b α).trace + starRingEnd ℂ (LinearMap.toMatrix b b α).trace := by
  obtain ⟨e, P, h⟩ := cor_7_8 b b' α
  have h1 : (((LinearMap.toMatrix b' b' (α.restrictScalars ℝ)).trace : ℝ) : ℂ) =
      (((LinearMap.toMatrix b' b' (α.restrictScalars ℝ)).map ((↑) : ℝ → ℂ)).reindex e e).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.map_apply, Complex.ofReal_sum]
    exact (Equiv.sum_comp e.symm (fun i => (((LinearMap.toMatrix b' b' (α.restrictScalars ℝ)) i i : ℝ) : ℂ))).symm
  rw [h1, h, Matrix.trace_units_conj]
  simp [Matrix.trace, Fintype.sum_sum_type, map_sum]

/-- Characteristic polynomial form of Corollary 7.8 at the level of matrices. -/
lemma cx_charpoly_matrix [FiniteDimensional ℂ V] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (b : Basis ι ℂ V) (b' : Basis κ ℝ V) (α : V →ₗ[ℂ] V) :
    (LinearMap.toMatrix b' b' (α.restrictScalars ℝ)).charpoly.map (algebraMap ℝ ℂ) =
      (LinearMap.toMatrix b b α).charpoly * (LinearMap.toMatrix b b α).charpoly.map (starRingEnd ℂ) := by
  obtain ⟨e, P, h⟩ := cor_7_8 b b' α
  have h1 : (LinearMap.toMatrix b' b' (α.restrictScalars ℝ)).charpoly.map (algebraMap ℝ ℂ) =
      (((LinearMap.toMatrix b' b' (α.restrictScalars ℝ)).map ((↑) : ℝ → ℂ)).reindex e e).charpoly := by
    rw [Matrix.charpoly_reindex]
    exact (Matrix.charpoly_map _ Complex.ofRealHom).symm
  rw [h1, h, Matrix.coe_units_inv, Matrix.charpoly_units_conj, Matrix.charpoly_fromBlocks_zero₁₂,
    Matrix.charpoly_map]

/-- Consequence of Corollary 7.8 for traces (used in Corollary 7.9): for a $\mathbb C$-linear $\alpha$,
$\mathrm{Tr}_{\mathbb R}(\alpha) = \mathrm{Tr}_{\mathbb C}(\alpha) + \overline{\mathrm{Tr}_{\mathbb C}(\alpha)}$. -/
@[kb "milne2006ec" "Ch. V, Corollary 7.8 (pdf p. 229): trace form"]
theorem cor_7_8_trace [FiniteDimensional ℂ V] (α : V →ₗ[ℂ] V) :
    ((LinearMap.trace ℝ V (α.restrictScalars ℝ) : ℝ) : ℂ) =
      LinearMap.trace ℂ V α + starRingEnd ℂ (LinearMap.trace ℂ V α) := by
  classical
  have := cx_trace_matrix (Module.finBasis ℂ V) (Module.finBasis ℝ V) α
  rwa [← LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ V),
    ← LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V)] at this

/-- Consequence of Corollary 7.8 for characteristic polynomials (the linear algebra of Remark 6.2): the
characteristic polynomial of $\alpha$ as an $\mathbb R$-linear map is $Q \bar Q$, where $Q$ is its characteristic
polynomial as a $\mathbb C$-linear map. -/
@[kb "milne2006ec" "Ch. V, Corollary 7.8 (pdf p. 229): characteristic polynomial form"]
theorem cor_7_8_charpoly [FiniteDimensional ℂ V] (α : V →ₗ[ℂ] V) :
    (LinearMap.charpoly (α.restrictScalars ℝ)).map (algebraMap ℝ ℂ) =
      LinearMap.charpoly α * (LinearMap.charpoly α).map (starRingEnd ℂ) := by
  classical
  have := cx_charpoly_matrix (Module.finBasis ℂ V) (Module.finBasis ℝ V) α
  rwa [LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix] at this

/-- The $\mathbb Z$-basis $b'$ of the lattice $\mathbb Z$-spanned by an $\mathbb R$-basis $b'$ of $V$. -/
def latticeBasisOf {κ : Type*} (b' : Basis κ ℝ V) : Basis κ ℤ (Submodule.span ℤ (Set.range b')) :=
  Basis.span (b'.linearIndependent.restrict_scalars' ℤ)

/-- Coordinates in the lattice basis agree with coordinates in the real basis. -/
lemma latticeBasisOf_repr {κ : Type*} [Fintype κ] (b' : Basis κ ℝ V)
    (x : V) (hx : x ∈ Submodule.span ℤ (Set.range b')) (i : κ) :
    b'.repr x i = (((latticeBasisOf b').repr ⟨x, hx⟩ i : ℤ) : ℝ) := by
  classical
  have h := congrArg (fun y : Submodule.span ℤ (Set.range b') => b'.repr (y : V) i)
    ((latticeBasisOf b').sum_repr ⟨x, hx⟩)
  simp only [latticeBasisOf, Basis.span_apply] at h ⊢
  rw [← h]
  simp [map_sum, Finsupp.single_apply]

/-- The matrix of the restriction of `α` to the lattice, mapped to the complex numbers, is the real
matrix of `α`. -/
lemma lattice_matrix_map {κ : Type*} [Fintype κ] [DecidableEq κ] (b' : Basis κ ℝ V) (α : V →ₗ[ℂ] V)
    (hα : ∀ x ∈ Submodule.span ℤ (Set.range b'), α x ∈ Submodule.span ℤ (Set.range b')) :
    (LinearMap.toMatrix (latticeBasisOf b') (latticeBasisOf b')
      ((α.restrictScalars ℤ).restrict hα)).map (Int.castRingHom ℂ) =
      (LinearMap.toMatrix b' b' (α.restrictScalars ℝ)).map ((↑) : ℝ → ℂ) := by
  ext i j
  have hj : ((latticeBasisOf b' j : Submodule.span ℤ (Set.range b')) : V) = b' j := by
    simp [latticeBasisOf, Basis.span_apply]
  have hmem := hα (b' j) (Submodule.subset_span ⟨j, rfl⟩)
  have hrestr : ((α.restrictScalars ℤ).restrict hα) (latticeBasisOf b' j) = ⟨α (b' j), hmem⟩ :=
    Subtype.ext (by
      show α ((latticeBasisOf b' j : Submodule.span ℤ (Set.range b')) : V) = α (b' j)
      rw [hj])
  have hr := latticeBasisOf_repr b' (α (b' j)) hmem i
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply, eq_intCast]
  rw [hrestr]
  simp [hr]

/-- **Remark 6.2, linear-algebra content** (Milne, *EC*, V, Remark 6.2, p. 222): let $H \subset V$ be the
$\mathbb Z$-span of an $\mathbb R$-basis $b'$ of $V$ (a lattice; for Milne $H = H_1(X_0(N), \mathbb Z)$ in
$V = \Omega^1(X_0(N))^\vee$) and $\alpha$ a $\mathbb C$-linear endomorphism of $V$ with $\alpha(H) \subset H$. The
characteristic polynomial $P \in \mathbb Z[Y]$ of $\alpha$ on $H$ is $Q \bar Q$, where $Q \in \mathbb C[Y]$ is the
characteristic polynomial of $\alpha$ on $V$. -/
@[kb "milne2006ec" "Ch. V, Remark 6.2 (pdf p. 222): linear algebra for a lattice"]
theorem remark_6_2_lattice [FiniteDimensional ℂ V] {κ : Type*} [Fintype κ] [DecidableEq κ] (b' : Basis κ ℝ V)
    (α : V →ₗ[ℂ] V)
    (hα : ∀ x ∈ Submodule.span ℤ (Set.range b'), α x ∈ Submodule.span ℤ (Set.range b')) :
    (LinearMap.toMatrix (latticeBasisOf b') (latticeBasisOf b')
      ((α.restrictScalars ℤ).restrict hα)).charpoly.map (Int.castRingHom ℂ) =
      LinearMap.charpoly α * (LinearMap.charpoly α).map (starRingEnd ℂ) := by
  rw [← Matrix.charpoly_map, lattice_matrix_map b' α hα]
  change ((LinearMap.toMatrix b' b' (α.restrictScalars ℝ)).map Complex.ofRealHom).charpoly = _
  rw [Matrix.charpoly_map]
  have := cx_charpoly_matrix (Module.finBasis ℂ V) b' α
  rw [LinearMap.charpoly_toMatrix α (Module.finBasis ℂ V)] at this
  exact this

/-- **Corollary 7.9, linear-algebra content** (Milne, *EC*, V, Corollary 7.9, p. 229): in the setting of
`remark_6_2_lattice`, $\mathrm{Tr}(\alpha \mid H) = \mathrm{Tr}(\alpha \mid V) + \overline{\mathrm{Tr}(\alpha \mid
V)}$. (Milne's statement is for $\alpha = T(p)$, $H = H_1(X_0(N), \mathbb Z)$, $V = \Omega^1(X_0(N))^\vee$; the
trace on $\Omega^1$ and on its dual agree.) -/
@[kb "milne2006ec" "Ch. V, Corollary 7.9 (pdf p. 229): linear algebra for a lattice"]
theorem cor_7_9_lattice [FiniteDimensional ℂ V] {κ : Type*} [Fintype κ] (b' : Basis κ ℝ V) (α : V →ₗ[ℂ] V)
    (hα : ∀ x ∈ Submodule.span ℤ (Set.range b'), α x ∈ Submodule.span ℤ (Set.range b')) :
    ((LinearMap.trace ℤ _ ((α.restrictScalars ℤ).restrict hα) : ℤ) : ℂ) =
      LinearMap.trace ℂ V α + starRingEnd ℂ (LinearMap.trace ℂ V α) := by
  classical
  have h1 := cx_trace_matrix (Module.finBasis ℂ V) b' α
  rw [← LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V)] at h1
  rw [← h1, LinearMap.trace_eq_matrix_trace ℤ (latticeBasisOf b')]
  push_cast [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := congrFun (congrFun (lattice_matrix_map b' α hα) i) i
  simpa using this

end NumberFieldKB.MilneEC.Vb
