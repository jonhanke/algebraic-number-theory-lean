import NumberFieldKB.MilneCFT.Ch2
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Milne, *Class Field Theory*, Chapter VII §3: Herbrand quotients of lattices

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

* **Lemma 3.4** (`lemma_3_4`): Herbrand quotients of finitely generated modules with isomorphic rationalizations agree.
* **Full lattice** (definition in prose, p. 208): Mathlib's `IsZLattice` (`fullLattice_span_basis`).
-/

open CategoryTheory

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

open TensorProduct

section Aux

variable {A : Type*} [AddCommGroup A] [inst : Module ℤ A]

/-- `a ↦ 1 ⊗ a` is the localization of `A` at the nonzero integers. -/
lemma isLocalizedModule_tmul_one :
    IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ A 1) := by
  obtain rfl := Subsingleton.elim inst (AddCommGroup.toIntModule (M := A))
  exact (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).2
    (TensorProduct.isBaseChange (R := ℤ) (S := ℚ) (M := A))

/-- `1 ⊗ a = 0` iff `a` is a torsion element. -/
lemma tmul_one_eq_zero_iff (a : A) : (1 : ℚ) ⊗ₜ[ℤ] a = 0 ↔ ∃ s : ℤ, s ≠ 0 ∧ s • a = 0 := by
  obtain rfl := Subsingleton.elim inst (AddCommGroup.toIntModule (M := A))
  have := isLocalizedModule_tmul_one (A := A)
  have := IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ A 1) (m := a)
  simp only [TensorProduct.mk_apply] at this
  rw [this]
  constructor
  · rintro ⟨⟨s, hs⟩, h⟩
    exact ⟨s, nonZeroDivisors.ne_zero hs, by simpa [Submonoid.smul_def] using h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩, by simpa [Submonoid.smul_def] using h⟩

/-- Every element of `ℚ ⊗ A` has a nonzero integer multiple of the form `1 ⊗ a`. -/
lemma exists_smul_eq_tmul_one (y : ℚ ⊗[ℤ] A) : ∃ s : ℤ, s ≠ 0 ∧ ∃ a : A, s • y = (1 : ℚ) ⊗ₜ[ℤ] a := by
  obtain rfl := Subsingleton.elim inst (AddCommGroup.toIntModule (M := A))
  have := isLocalizedModule_tmul_one (A := A)
  obtain ⟨⟨a, ⟨s, hs⟩⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ A 1) y
  exact ⟨s, nonZeroDivisors.ne_zero hs, a, by simpa [Submonoid.smul_def] using h⟩

/-- The torsion in `A` (the kernel of `a ↦ 1 ⊗ a`) is finite. -/
lemma finite_ker_tmul_one [Module.Finite ℤ A] :
    Finite (LinearMap.ker (TensorProduct.mk ℤ ℚ A 1)) := by
  obtain rfl := Subsingleton.elim inst (AddCommGroup.toIntModule (M := A))
  apply Module.finite_of_fg_torsion
  intro x
  obtain ⟨s, hs, h⟩ := (tmul_one_eq_zero_iff (x : A)).1 (LinearMap.mem_ker.1 x.2)
  exact ⟨⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩, Subtype.ext (by simpa [Submonoid.smul_def] using h)⟩

/-- A quotient of `A` by a submodule in which every element has a nonzero multiple is finite. -/
lemma finite_quotient_of_torsion [Module.Finite ℤ A] (Q : Submodule ℤ A)
    (h : ∀ a : A, ∃ s : ℤ, s ≠ 0 ∧ s • a ∈ Q) : Finite (A ⧸ Q) := by
  obtain rfl := Subsingleton.elim inst (AddCommGroup.toIntModule (M := A))
  apply Module.finite_of_fg_torsion
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    obtain ⟨s, hs, hsa⟩ := h a
    exact ⟨⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩, by
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul]; exact (Submodule.Quotient.mk_eq_zero Q).2 hsa⟩

end Aux

section Pullback

attribute [local instance 2000] Prod.instModule Submodule.module

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [iA : Module ℤ A] [iB : Module ℤ B]
  (φ : TensorProduct ℤ ℚ A ≃ₗ[ℚ] TensorProduct ℤ ℚ B)

/-- The pullback `{(a, b) | φ(1 ⊗ a) = 1 ⊗ b}` inside `A × B`. -/
def pbSub : Submodule ℤ (A × B) where
  carrier := {x | φ ((1 : ℚ) ⊗ₜ[ℤ] x.1) = (1 : ℚ) ⊗ₜ[ℤ] x.2}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, hx, hy]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    obtain rfl := Subsingleton.elim iA (AddCommGroup.toIntModule (M := A))
    obtain rfl := Subsingleton.elim iB (AddCommGroup.toIntModule (M := B))
    simp only [Set.mem_ofPred_eq] at *
    rw [Prod.smul_fst, Prod.smul_snd, TensorProduct.tmul_smul, TensorProduct.tmul_smul, map_zsmul, hx]

lemma mem_pbSub (x : A × B) : x ∈ pbSub φ ↔ φ ((1 : ℚ) ⊗ₜ[ℤ] x.1) = (1 : ℚ) ⊗ₜ[ℤ] x.2 := Iff.rfl

variable {φ}

lemma pbSub_map (f : A →ₗ[ℤ] A) (f' : B →ₗ[ℤ] B)
    (h : ∀ x, φ (LinearMap.baseChange ℚ f x) = LinearMap.baseChange ℚ f' (φ x)) (x : A × B)
    (hx : x ∈ pbSub φ) : f.prodMap f' x ∈ pbSub φ := by
  rw [mem_pbSub] at *
  have := h ((1 : ℚ) ⊗ₜ[ℤ] x.1)
  simp only [LinearMap.baseChange_tmul] at this
  simp [this, hx]

/-- The first projection of the pullback has finite kernel. -/
lemma pb_fst_ker_finite [Module.Finite ℤ B] :
    Finite (LinearMap.ker ((LinearMap.fst ℤ A B).comp (pbSub φ).subtype)) := by
  obtain rfl := Subsingleton.elim iA (AddCommGroup.toIntModule (M := A))
  obtain rfl := Subsingleton.elim iB (AddCommGroup.toIntModule (M := B))
  haveI := finite_ker_tmul_one (A := B)
  refine Finite.of_injective (fun x => (⟨x.1.1.2, ?_⟩ : LinearMap.ker (TensorProduct.mk ℤ ℚ B 1))) ?_
  · have h1 := x.1.2
    have h2 : x.1.1.1 = 0 := LinearMap.mem_ker.1 x.2
    rw [mem_pbSub, h2] at h1
    simpa [LinearMap.mem_ker] using h1.symm
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · exact (LinearMap.mem_ker.1 x.2).trans (LinearMap.mem_ker.1 y.2).symm
    · exact h

/-- The first projection of the pullback has finite cokernel. -/
lemma pb_fst_coker_finite [Module.Finite ℤ A] :
    Finite (A ⧸ LinearMap.range ((LinearMap.fst ℤ A B).comp (pbSub φ).subtype)) := by
  obtain rfl := Subsingleton.elim iA (AddCommGroup.toIntModule (M := A))
  obtain rfl := Subsingleton.elim iB (AddCommGroup.toIntModule (M := B))
  apply finite_quotient_of_torsion
  intro a
  obtain ⟨s, hs, b, hb⟩ := exists_smul_eq_tmul_one (φ ((1 : ℚ) ⊗ₜ[ℤ] a))
  refine ⟨s, hs, ⟨(s • a, b), ?_⟩, rfl⟩
  rw [mem_pbSub]
  simp only [TensorProduct.tmul_smul, map_zsmul]
  exact hb

/-- The second projection of the pullback has finite kernel. -/
lemma pb_snd_ker_finite [Module.Finite ℤ A] :
    Finite (LinearMap.ker ((LinearMap.snd ℤ A B).comp (pbSub φ).subtype)) := by
  obtain rfl := Subsingleton.elim iA (AddCommGroup.toIntModule (M := A))
  obtain rfl := Subsingleton.elim iB (AddCommGroup.toIntModule (M := B))
  haveI := finite_ker_tmul_one (A := A)
  refine Finite.of_injective (fun x => (⟨x.1.1.1, ?_⟩ : LinearMap.ker (TensorProduct.mk ℤ ℚ A 1))) ?_
  · have h1 := x.1.2
    have h2 : x.1.1.2 = 0 := LinearMap.mem_ker.1 x.2
    rw [mem_pbSub, h2] at h1
    have : (1 : ℚ) ⊗ₜ[ℤ] x.1.1.1 = 0 := φ.injective (by simpa using h1)
    exact this
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · exact h
    · exact (LinearMap.mem_ker.1 x.2).trans (LinearMap.mem_ker.1 y.2).symm

/-- The second projection of the pullback has finite cokernel. -/
lemma pb_snd_coker_finite [Module.Finite ℤ B] :
    Finite (B ⧸ LinearMap.range ((LinearMap.snd ℤ A B).comp (pbSub φ).subtype)) := by
  obtain rfl := Subsingleton.elim iA (AddCommGroup.toIntModule (M := A))
  obtain rfl := Subsingleton.elim iB (AddCommGroup.toIntModule (M := B))
  apply finite_quotient_of_torsion
  intro b
  obtain ⟨s, hs, a, ha⟩ := exists_smul_eq_tmul_one (φ.symm ((1 : ℚ) ⊗ₜ[ℤ] b))
  refine ⟨s, hs, ⟨(a, s • b), ?_⟩, rfl⟩
  rw [mem_pbSub]
  have : φ (s • φ.symm ((1 : ℚ) ⊗ₜ[ℤ] b)) = (1 : ℚ) ⊗ₜ[ℤ] (s • b) := by
    rw [map_zsmul]; simp [TensorProduct.tmul_smul]
  rw [ha] at this
  exact this

end Pullback

section PullbackRep

universe u

attribute [local instance 2000] Prod.instModule Submodule.module

variable {G : Type} [Group G] [Fintype G] {M N : Rep.{u} ℤ G}
  {φ : TensorProduct ℤ ℚ M ≃ₗ[ℚ] TensorProduct ℤ ℚ N}
  (hφ : ∀ (g : G) (x : TensorProduct ℤ ℚ M),
      φ (LinearMap.baseChange ℚ (M.ρ g) x) = LinearMap.baseChange ℚ (N.ρ g) (φ x))

/-- The pullback as a representation. -/
def pbRep : Rep ℤ G :=
  @Rep.of ℤ G _ _ (pbSub φ) _ (Submodule.module _) (Representation.subrepresentation (M.ρ.prod N.ρ) (pbSub φ)
    (fun g x hx => pbSub_map (M.ρ g) (N.ρ g) (hφ g) x hx))

/-- The first projection of the pullback, as a morphism of representations. -/
def pbFst : pbRep hφ ⟶ M :=
  ConcreteCategory.ofHom (C := Rep ℤ G)
    (LinearMap.intertwiningMap_of_isIntertwiningMap
      (ρ := (pbRep hφ).ρ) (σ := M.ρ) (f := (LinearMap.fst ℤ M N).comp (pbSub φ).subtype) (fun g v => rfl))

/-- The second projection of the pullback, as a morphism of representations. -/
def pbSnd : pbRep hφ ⟶ N :=
  ConcreteCategory.ofHom (C := Rep ℤ G)
    (LinearMap.intertwiningMap_of_isIntertwiningMap
      (ρ := (pbRep hφ).ρ) (σ := N.ρ) (f := (LinearMap.snd ℤ M N).comp (pbSub φ).subtype) (fun g v => rfl))

end PullbackRep

/-- **Lemma 3.4** (Milne, *CFT*, Chapter VII, p. 208): let $G$ be a finite cyclic group and $M$, $N$ $G$-modules finitely
generated over $\mathbb Z$ with $M\otimes\mathbb Q\cong N\otimes\mathbb Q$ as $G$-modules. If either Herbrand quotient is
defined, so is the other, and they are equal. -/
@[kb "milne2020cft" "Ch. VII, Lemma 3.4"]
theorem lemma_3_4 {G : Type} [Group G] [Fintype G] [IsCyclic G] (M N : Rep ℤ G)
    [Module.Finite ℤ M] [Module.Finite ℤ N]
    (φ : TensorProduct ℤ ℚ M ≃ₗ[ℚ] TensorProduct ℤ ℚ N)
    (hφ : ∀ (g : G) (x : TensorProduct ℤ ℚ M),
      φ (LinearMap.baseChange ℚ (M.ρ g) x) = LinearMap.baseChange ℚ (N.ρ g) (φ x)) :
    (HerbrandDefined M ↔ HerbrandDefined N) ∧ (HerbrandDefined M → herbrandQuotient M = herbrandQuotient N) := by
  have c1 := cor_3_9 (pbFst hφ) pb_fst_ker_finite pb_fst_coker_finite
  have c2 := cor_3_9 (pbSnd hφ) pb_snd_ker_finite pb_snd_coker_finite
  refine ⟨⟨fun h => c2.1.1 (c1.1.2 h), fun h => c1.1.1 (c2.1.2 h)⟩, fun h => ?_⟩
  have hP := c1.1.2 h
  exact (c1.2 hP).symm.trans (c2.2 hP)

/-- **Full lattice** (definition in prose; Milne, *CFT*, Chapter VII, p. 208, footnote 2): a subgroup of a real vector
space generated by a basis. Mathlib's `IsZLattice` (discrete and spanning): the span of a basis is one. -/
@[kb "milne2020cft" "Ch. VII, §3, p. 208 (full lattice)"]
theorem fullLattice_span_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ E) :
    DiscreteTopology (Submodule.span ℤ (Set.range b)) ∧ IsZLattice ℝ (Submodule.span ℤ (Set.range b)) :=
  ⟨inferInstance, inferInstance⟩

end NumberFieldKB.MilneCFT.Ch7
