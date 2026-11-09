import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Lattice
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.UnitFiltration.Lattice
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.UnitFiltration.TateCohomology
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.FiniteExtension.IntermediateField
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Coinduced
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Filtration
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.TrivialityCriterion
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Functoriality

/-!
# Milne, *Class Field Theory*, Chapter III, Lemma 2.4 (proved)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Ch. III, Lemma 2.4, p. 104.
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.Ch3.L24

open CategoryTheory Limits Rep

section Abstract

variable {G : Type} [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

/-- Restricting a complete separated filtration to a subgroup `S`: degree-zero Tate cohomology. -/
theorem isZero_res_tateCohomology_zero_of_filtration {M : Rep ℤ G} {F : ℕ → Submodule ℤ M}
    {Q : ℕ → Rep ℤ G} (hF : ∀ n g, F n ≤ (F n).comap (M.ρ g))
    (π : ∀ n, M.subrepresentation (F n) (hF n) ⟶ Q n) (hF0 : F 0 = ⊤)
    (hsep : ∀ x : M, (∀ n, x ∈ F n) → x = 0)
    (hcomplete : ∀ x : ℕ → M, (∀ n, x n ∈ F n) →
      ∃ s : M, ∀ n, s - ∑ i ∈ Finset.range n, x i ∈ F n)
    (hπ : ∀ n, Function.Surjective (π n).hom)
    (hker : ∀ n (x : F n), (π n).hom x = 0 → (x : M) ∈ F (n + 1))
    (hQ : ∀ n, IsZero (tateCohomology (res S.subtype (Q n)) 0)) :
    IsZero (tateCohomology (res S.subtype M) 0) :=
  TauCeti.TateCohomology.isZero_tateCohomology_zero_of_filtration
    (M := res S.subtype M) (F := F) (Q := fun n => res S.subtype (Q n))
    (fun n g => hF n (S.subtype g))
    (fun n => resMap S.subtype (π n)) hF0 hsep hcomplete
    (fun n => hπ n) hker hQ

/-- Restricting a complete separated filtration to a subgroup `S`: degree `-1` Tate cohomology. -/
theorem isZero_res_tateCohomology_negOne_of_filtration {M : Rep ℤ G} {F : ℕ → Submodule ℤ M}
    {Q : ℕ → Rep ℤ G} (hF : ∀ n g, F n ≤ (F n).comap (M.ρ g))
    (π : ∀ n, M.subrepresentation (F n) (hF n) ⟶ Q n) (hF0 : F 0 = ⊤)
    (hsep : ∀ x : M, (∀ n, x ∈ F n) → x = 0)
    (hcomplete : ∀ x : ℕ → M, (∀ n, x n ∈ F n) →
      ∃ s : M, ∀ n, s - ∑ i ∈ Finset.range n, x i ∈ F n)
    (hπ : ∀ n, Function.Surjective (π n).hom)
    (hker : ∀ n (x : F n), (π n).hom x = 0 → (x : M) ∈ F (n + 1))
    (hQ : ∀ n, IsZero (tateCohomology (res S.subtype (Q n)) (-1))) :
    IsZero (tateCohomology (res S.subtype M) (-1)) :=
  TauCeti.TateCohomology.isZero_tateCohomology_negOne_of_filtration
    (M := res S.subtype M) (F := F) (Q := fun n => res S.subtype (Q n))
    (fun n g => hF n (S.subtype g))
    (fun n => resMap S.subtype (π n)) hF0 hsep hcomplete
    (fun n => hπ n) hker hQ

end Abstract

section Free

/-- The equivalence `(G ⧸ S) × S ≃ G`, `(q, s) ↦ q.out * s`. -/
def cosetEquiv {G : Type} [Group G] (S : Subgroup G) : (G ⧸ S) × S ≃ G :=
  Equiv.ofBijective (fun p => (Quotient.out p.1 : G) * (p.2 : G)) (by
    constructor
    · rintro ⟨q₁, s₁⟩ ⟨q₂, s₂⟩ h
      have hq : q₁ = q₂ := by
        have h1 : ((Quotient.out q₁ * (s₁ : G) : G) : G ⧸ S) = q₁ := by
          rw [QuotientGroup.mk_mul_of_mem _ s₁.2]; exact QuotientGroup.out_eq' q₁
        have h2 : ((Quotient.out q₂ * (s₂ : G) : G) : G ⧸ S) = q₂ := by
          rw [QuotientGroup.mk_mul_of_mem _ s₂.2]; exact QuotientGroup.out_eq' q₂
        rw [← h1, ← h2]; exact congrArg _ h
      subst hq
      have : (s₁ : G) = s₂ := mul_left_cancel h
      exact Prod.ext rfl (Subtype.ext this)
    · intro g
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S g
      refine ⟨(QuotientGroup.mk g, h⁻¹), ?_⟩
      simp only [hh, Subgroup.coe_inv]
      group)

theorem cosetEquiv_apply {G : Type} [Group G] (S : Subgroup G) (q : G ⧸ S) (s : S) :
    cosetEquiv S (q, s) = (Quotient.out q : G) * s := rfl

/-- If the identity of `ρ` is the norm of `φ` over `G`, it is the norm of some `ψ` over a subgroup `S`. -/
theorem exists_forall_eq_sum_subgroup {k V : Type*} [Semiring k] [AddCommGroup V] [Module k V]
    {G : Type} [Group G] [Fintype G] {ρ : Representation k G V} (φ : V →ₗ[k] V)
    (hφ : ∀ x, x = ∑ g : G, ρ g (φ (ρ g⁻¹ x))) (S : Subgroup G) [Fintype S] :
    ∃ ψ : V →ₗ[k] V, ∀ x, x = ∑ s : S, ρ (s : G) (ψ (ρ (s : G)⁻¹ x)) := by
  classical
  refine ⟨∑ q : G ⧸ S, (ρ (Quotient.out q : G)⁻¹) ∘ₗ φ ∘ₗ (ρ (Quotient.out q : G)), fun x => ?_⟩
  have h1 : x = ∑ g : G, ρ g⁻¹ (φ (ρ g x)) := by
    conv_lhs => rw [hφ x]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by simp)
  have h2 : x = ∑ s : S, ρ (s : G)⁻¹ ((∑ q : G ⧸ S,
      (ρ (Quotient.out q : G)⁻¹) ∘ₗ φ ∘ₗ (ρ (Quotient.out q : G))) (ρ (s : G) x)) := by
    conv_lhs => rw [h1]
    rw [← Fintype.sum_equiv (cosetEquiv S) (fun p => ρ (Quotient.out p.1 * (p.2 : G))⁻¹
      (φ (ρ (Quotient.out p.1 * (p.2 : G)) x))) _ (fun p => rfl), Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [mul_inv_rev, map_mul]
  conv_lhs => rw [h2]
  exact Fintype.sum_equiv (Equiv.inv S) _ _ (fun s => by simp)

/-- A free representation modulo a scalar has trivial Tate cohomology on every subgroup. -/
theorem isZero_res_quotSMulTop_of_equiv_leftRegular {k : Type} [CommRing k] {G V : Type} [Group G]
    [Fintype G] [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    (e : (Representation.leftRegular k G).Equiv ρ) (r : k) (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype (Rep.of (ρ.quotSMulTop r).restrictScalarsInt)) n) := by
  obtain ⟨φ, hφ⟩ := TauCeti.TateCohomology.exists_forall_eq_sum_of_equiv_leftRegular e
  obtain ⟨ψ, hψ⟩ := exists_forall_eq_sum_subgroup φ hφ S
  exact TauCeti.TateCohomology.isZero_restrictScalarsInt_quotSMulTop_of_forall_eq_sum
    (G := S) (ρ := ρ.comp S.subtype) ψ (fun x => by simpa using hψ x) r n

end Free

end NumberFieldKB.MilneCFT.Ch3.L24

section TauCetiCopy

open CategoryTheory Limits ValuativeRel Submodule MulAction Rep

namespace TauCeti

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

namespace IsUnitFiltrationLattice

/-! ### Step zero of the filtration as an integral representation -/

variable {ϖ : 𝒪[K]} {A : Submodule 𝒪[K] 𝒪[L]} (hA : IsUnitFiltrationLattice ϖ A)
  (hσ : ∀ σ : L ≃ₐ[K] L,
    A ≤ A.comap (Representation.ofDistribMulAction 𝒪[K] (L ≃ₐ[K] L) 𝒪[L] σ))

/-- The Galois action on step zero `1 + A` of the unit filtration of a Galois-stable lattice. -/
@[instance_reducible]
private def mulDistribMulAction : MulDistribMulAction (L ≃ₐ[K] L) (hA.filtration 0) :=
  letI : SMul (L ≃ₐ[K] L) (hA.filtration 0) :=
    ⟨fun σ x ↦ ⟨σ • (x : Lˣ), by
      simpa only [AlgEquiv.smul_units_def] using
        hA.unitsMap_mem_filtration σ (fun _ ha ↦ hσ σ ha) x.2⟩⟩
  Subtype.coe_injective.mulDistribMulAction (hA.filtration 0).subtype fun _ _ ↦ rfl

/-- The Galois action on step zero `1 + A` is the restriction of the Galois action on `Lˣ`. -/
private theorem coe_smul (σ : L ≃ₐ[K] L) (x : hA.filtration 0) :
    letI := hA.mulDistribMulAction hσ
    ((σ • x : hA.filtration 0) : Lˣ) = σ • (x : Lˣ) :=
  rfl

/-- Step zero `1 + A` of the unit filtration of a Galois-stable lattice, written additively, as an
integral representation of the Galois group. -/
private abbrev rep : Rep ℤ (L ≃ₐ[K] L) :=
  letI := hA.mulDistribMulAction hσ
  Rep.of (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) (hA.filtration 0))

/-- The unit of `L` underlying an element of `hA.rep hσ`. -/
private def toUnits (x : hA.rep hσ) : Lˣ :=
  (Additive.toMul x : hA.filtration 0)

private theorem toUnits_mem (x : hA.rep hσ) : hA.toUnits hσ x ∈ hA.filtration 0 :=
  (Additive.toMul x).2

private theorem toUnits_injective : Function.Injective (hA.toUnits hσ) := fun _ _ h ↦
  Additive.toMul.injective (Subtype.ext h)

private theorem toUnits_ρ (σ : L ≃ₐ[K] L) (x : hA.rep hσ) :
    hA.toUnits hσ ((hA.rep hσ).ρ σ x) = σ • hA.toUnits hσ x := by
  simp only [toUnits, Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul]
  exact hA.coe_smul hσ σ _

private theorem toUnits_sub (x y : hA.rep hσ) :
    hA.toUnits hσ (x - y) = hA.toUnits hσ x / hA.toUnits hσ y := by
  simp [toUnits]

private theorem toUnits_sum (s : Finset ℕ) (x : ℕ → hA.rep hσ) :
    hA.toUnits hσ (∑ i ∈ s, x i) = ∏ i ∈ s, hA.toUnits hσ (x i) := by
  simp [toUnits]

/-- The `n`-th step `1 + ϖ ^ n • A` of the filtration, as a submodule of `hA.rep hσ`. -/
private def step (n : ℕ) : Submodule ℤ (hA.rep hσ) :=
  (Subgroup.toAddSubgroup ((hA.filtration n).subgroupOf (hA.filtration 0))).toIntSubmodule

private theorem mem_step {n : ℕ} {x : hA.rep hσ} :
    x ∈ hA.step hσ n ↔ hA.toUnits hσ x ∈ hA.filtration n := by
  rw [step, ← Submodule.mem_toAddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup,
    Additive.mem_toAddSubgroup, Subgroup.mem_subgroupOf, toUnits]

private theorem step_zero : hA.step hσ 0 = ⊤ :=
  eq_top_iff.2 fun x _ ↦ (hA.mem_step hσ).2 (hA.toUnits_mem hσ x)

private theorem step_le_comap (n : ℕ) (σ : L ≃ₐ[K] L) :
    hA.step hσ n ≤ (hA.step hσ n).comap ((hA.rep hσ).ρ σ) := fun _ hx ↦ by
  rw [Submodule.mem_comap, mem_step, toUnits_ρ, AlgEquiv.smul_units_def]
  exact hA.unitsMap_mem_filtration σ (fun _ ha ↦ hσ σ ha) ((hA.mem_step hσ).1 hx)

/-- The filtration by the steps is separated. -/
private theorem eq_zero_of_forall_mem_step (x : hA.rep hσ) (hx : ∀ n, x ∈ hA.step hσ n) :
    x = 0 := by
  have h : hA.toUnits hσ x ∈ ⨅ n, hA.filtration n :=
    Subgroup.mem_iInf.2 fun n ↦ (hA.mem_step hσ).1 (hx n)
  rw [hA.iInf_filtration, Subgroup.mem_bot] at h
  exact hA.toUnits_injective hσ (h.trans (by simp [toUnits]))

/-- The filtration by the steps is complete. -/
private theorem exists_forall_sub_sum_mem_step (x : ℕ → hA.rep hσ)
    (hx : ∀ n, x n ∈ hA.step hσ n) :
    ∃ s : hA.rep hσ, ∀ n, s - ∑ i ∈ Finset.range n, x i ∈ hA.step hσ n := by
  obtain ⟨s, hs0, hs⟩ := hA.exists_forall_div_prod_mem_filtration
    (fun n ↦ hA.toUnits hσ (x n)) fun n ↦ (hA.mem_step hσ).1 (hx n)
  refine ⟨Additive.ofMul (α := hA.filtration 0) ⟨s, hs0⟩, fun n ↦ (hA.mem_step hσ).2 ?_⟩
  rw [toUnits_sub, toUnits_sum]
  simpa [toUnits] using hs n

/-! ### The graded pieces -/

/-- The lattice `A` as a representation of the Galois group over `𝒪[K]`. -/
private abbrev latticeRep : Representation 𝒪[K] (L ≃ₐ[K] L) A :=
  (Representation.ofDistribMulAction 𝒪[K] (L ≃ₐ[K] L) 𝒪[L]).subrepresentation A hσ

/-- The map `1 + ϖ ^ n • a ↦ a mod ϖ • A` from the `n`-th step onto the graded piece
`A ⧸ ϖ • A`, additively. -/
private def gradedMap (n : ℕ) : hA.step hσ n →+ QuotSMulTop ϖ A :=
  (hA.filtrationToQuotient n).toAdditive.comp
    (AddMonoidHom.mk'
      (fun x ↦ Additive.ofMul (⟨hA.toUnits hσ x, (hA.mem_step hσ).1 x.2⟩ : hA.filtration n))
      fun _ _ ↦ rfl)

/-- `gradedMap` is `filtrationToQuotient` applied to the underlying unit of `1 + ϖ ^ n • A`. -/
private theorem gradedMap_eq_toAdd_filtrationToQuotient {n : ℕ} (x : hA.step hσ n) :
    hA.gradedMap hσ n x = Multiplicative.toAdd
      (hA.filtrationToQuotient n ⟨hA.toUnits hσ x, (hA.mem_step hσ).1 x.2⟩) :=
  rfl

private theorem gradedMap_apply {n : ℕ} (x : hA.step hσ n) {a : 𝒪[L]} (ha : a ∈ A)
    (hx : (hA.toUnits hσ x : L) = ((1 + ϖ ^ n • a : 𝒪[L]) : L)) :
    hA.gradedMap hσ n x = Submodule.Quotient.mk ⟨a, ha⟩ :=
  (hA.gradedMap_eq_toAdd_filtrationToQuotient hσ x).trans
    (congrArg Multiplicative.toAdd (hA.filtrationToQuotient_apply _ ha hx))

private theorem gradedMap_ρ {n : ℕ} (σ : L ≃ₐ[K] L) (x : hA.step hσ n) :
    hA.gradedMap hσ n ⟨(hA.rep hσ).ρ σ x, hA.step_le_comap hσ n σ x.2⟩ =
      ((latticeRep hσ).quotSMulTop ϖ).restrictScalarsInt σ (hA.gradedMap hσ n x) := by
  obtain ⟨a, ha, hx⟩ := hA.mem_filtration_iff.1 ((hA.mem_step hσ).1 x.2)
  have hσx : (hA.toUnits hσ ((hA.rep hσ).ρ σ x) : L) = ((1 + ϖ ^ n • (σ • a) : 𝒪[L]) : L) := by
    rw [toUnits_ρ, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass, hx,
      ← AlgEquiv.coe_smul_integerRing, smul_add, smul_one, smul_comm]
  rw [hA.gradedMap_apply hσ x ha hx, hA.gradedMap_apply hσ _ (hσ σ ha) hσx,
    Representation.restrictScalarsInt_apply, Representation.quotSMulTop_apply_mk]
  simp [LinearMap.restrict_apply]

/-- The map `1 + ϖ ^ n • a ↦ a mod ϖ • A` onto the graded piece, as a morphism of integral
representations. -/
private def gradedHom (n : ℕ) :
    (hA.rep hσ).subrepresentation (hA.step hσ n) (hA.step_le_comap hσ n) ⟶
      Rep.of ((latticeRep hσ).quotSMulTop ϖ).restrictScalarsInt :=
  Rep.ofHom
    { toFun := hA.gradedMap hσ n
      map_add' := map_add _
      map_smul' := map_zsmul _
      isIntertwining' σ := LinearMap.ext fun x ↦ hA.gradedMap_ρ hσ σ x }

private theorem gradedHom_hom_apply (n : ℕ) (x : hA.step hσ n) :
    (hA.gradedHom hσ n).hom x = hA.gradedMap hσ n x := by
  simp [gradedHom]

private theorem gradedHom_surjective (n : ℕ) : Function.Surjective (hA.gradedHom hσ n).hom := by
  intro q
  obtain ⟨y, hy⟩ := hA.filtrationToQuotient_surjective n (Multiplicative.ofAdd q)
  exact ⟨⟨Additive.ofMul ⟨y, hA.filtration_antitone (Nat.zero_le n) y.2⟩, y.2⟩,
    congrArg Multiplicative.toAdd hy⟩

private theorem mem_step_succ_of_gradedHom_eq_zero (n : ℕ) (x : hA.step hσ n)
    (hx : (hA.gradedHom hσ n).hom x = 0) : (x : hA.rep hσ) ∈ hA.step hσ (n + 1) := by
  rw [gradedHom_hom_apply, gradedMap_eq_toAdd_filtrationToQuotient, toAdd_eq_zero] at hx
  exact (hA.mem_step hσ).2 (Subgroup.mem_subgroupOf.1 ((hA.ker_filtrationToQuotient n).le hx))


open _root_.TateCohomology in
/-- Tate cohomology of `1 + A` restricted to any subgroup vanishes in degrees `0` and `-1`. -/
theorem isZero_res_tateCohomology_rep
    (e : (Representation.leftRegular 𝒪[K] (L ≃ₐ[K] L)).Equiv (latticeRep hσ))
    (S : Subgroup (L ≃ₐ[K] L)) [Fintype S] :
    IsZero (tateCohomology (res S.subtype (hA.rep hσ)) 0) ∧
      IsZero (tateCohomology (res S.subtype (hA.rep hσ)) (-1)) := by
  refine ⟨NumberFieldKB.MilneCFT.Ch3.L24.isZero_res_tateCohomology_zero_of_filtration S
    (hA.step_le_comap hσ) (hA.gradedHom hσ) (hA.step_zero hσ) (hA.eq_zero_of_forall_mem_step hσ)
    (hA.exists_forall_sub_sum_mem_step hσ) (hA.gradedHom_surjective hσ)
    (hA.mem_step_succ_of_gradedHom_eq_zero hσ) (fun _ ↦
      NumberFieldKB.MilneCFT.Ch3.L24.isZero_res_quotSMulTop_of_equiv_leftRegular e ϖ S 0),
    NumberFieldKB.MilneCFT.Ch3.L24.isZero_res_tateCohomology_negOne_of_filtration S
    (hA.step_le_comap hσ) (hA.gradedHom hσ) (hA.step_zero hσ) (hA.eq_zero_of_forall_mem_step hσ)
    (hA.exists_forall_sub_sum_mem_step hσ) (hA.gradedHom_surjective hσ)
    (hA.mem_step_succ_of_gradedHom_eq_zero hσ) (fun _ ↦
      NumberFieldKB.MilneCFT.Ch3.L24.isZero_res_quotSMulTop_of_equiv_leftRegular e ϖ S (-1))⟩

/-- **All Tate cohomology of `1 + A` vanishes** (Serre, Local Fields IX §3 Lemma 2 and Tate's criterion). -/
theorem isZero_tateCohomology_rep
    (e : (Representation.leftRegular 𝒪[K] (L ≃ₐ[K] L)).Equiv (latticeRep hσ)) (n : ℤ) :
    IsZero (tateCohomology (hA.rep hσ) n) :=
  TauCeti.TateCohomology.isZero_of_forall_isZero_res (hA.rep hσ) (fun S _ m =>
    TauCeti.TateCohomology.isZero_of_forall_isPGroup (hA.rep hσ) (q := -1)
      (fun _ _ T _ _ => (hA.isZero_res_tateCohomology_rep hσ e T).2)
      (fun _ _ T _ _ => by simpa using (hA.isZero_res_tateCohomology_rep hσ e T).1) S m) n

/-- `1 + A`, as an additive subgroup of the `G`-module `Lˣ`. -/
def stableSub : AddSubgroup (Rep.ofAlgebraAutOnUnits K L) :=
  show AddSubgroup (Additive Lˣ) from Subgroup.toAddSubgroup (hA.filtration 0)

/-- The comparison isomorphism between our `stableRep` of `V = 1 + A` inside `Lˣ` and Tau Ceti's
`hA.rep`. -/
def stableIso
    (hV : ∀ (σ : L ≃ₐ[K] L), ∀ x ∈ hA.stableSub,
      (Rep.ofAlgebraAutOnUnits K L).ρ σ x ∈ hA.stableSub) :
    NumberFieldKB.MilneCFT.Ch3.stableRep (Rep.ofAlgebraAutOnUnits K L)
      hA.stableSub hV ≅ hA.rep hσ where
  hom := Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun x => Additive.ofMul (α := hA.filtration 0) ⟨Additive.toMul x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }, fun σ => by ext x; rfl⟩
  inv := Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun x => ⟨Additive.ofMul (Additive.toMul x : hA.filtration 0).1,
        (Additive.toMul x : hA.filtration 0).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }, fun σ => by ext x; rfl⟩
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; exact Additive.toMul.injective (Subtype.ext rfl)

/-- **Higher cohomology of `1 + A` in `Lˣ` vanishes**, for our `stableRep`. -/
theorem isZero_groupCohomology_stableRep
    (e : (Representation.leftRegular 𝒪[K] (L ≃ₐ[K] L)).Equiv (latticeRep hσ))
    (hV : ∀ (σ : L ≃ₐ[K] L), ∀ x ∈ hA.stableSub,
      (Rep.ofAlgebraAutOnUnits K L).ρ σ x ∈ hA.stableSub)
    (r : ℕ) (hr : 0 < r) :
    IsZero (groupCohomology (NumberFieldKB.MilneCFT.Ch3.stableRep (Rep.ofAlgebraAutOnUnits K L)
      hA.stableSub hV) r) := by
  have : NeZero r := ⟨hr.ne'⟩
  have h1 : IsZero (groupCohomology (hA.rep hσ) r) :=
    ((hA.isZero_tateCohomology_rep hσ e r).of_iso
      ((_root_.TateCohomology.isoGroupCohomology (R := ℤ) (G := L ≃ₐ[K] L) r).app (hA.rep hσ)).symm)
  exact h1.of_iso ((groupCohomology.functor ℤ (L ≃ₐ[K] L) r).mapIso (hA.stableIso hσ hV)).symm

end IsUnitFiltrationLattice

end TauCeti

end TauCetiCopy

namespace NumberFieldKB.MilneCFT.Ch3

open NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT Submodule MulAction

set_option synthInstance.maxHeartbeats 400000

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem isUnit_one_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) : IsUnit (1 + a) := by
  by_contra hu
  have h1 : 1 + a ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hu
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by simpa using sub_mem h1 ha
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top this

/-- **Lemma 2.4** (Milne, *Class Field Theory* v4.03, Ch. III, p. 104; Serre, *Local Fields*, IX §3). For
$L/K$ finite Galois there is a $G$-stable subgroup $V\subseteq U_L$ containing $1+c\,\mathcal O_L$ for some nonzero
$c\in\mathfrak m_K$ with $H^r(G,V)=0$ for all $r>0$. Proof: $V=1+A$ for a Galois-stable lattice $A$ free over
$\mathcal O_K[G]$ (Tau Ceti `exists_isUnitFiltrationLattice_span_orbit`); the filtration $1+\varpi^nA$ is separated
and complete with graded pieces $A/\varpi A$ free over $(\mathcal O_K/\varpi)[G]$, so $V$ has vanishing Tate cohomology
in degrees $0,-1$ on every subgroup, hence in all degrees by Tate's criterion. -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 2.4, p. 104"]
theorem lemma2_4 : Lemma2_4 K Ω := by
  refine ⟨fun L _ _ => ?_⟩
  let _ : ValuativeRel L := TauCeti.finiteIntermediateFieldValuativeRel K Ω L
  let _ : TopologicalSpace L := TauCeti.finiteIntermediateFieldTopology K Ω L
  have : ValuativeExtension K L := TauCeti.finiteIntermediateField_valuativeExtension K Ω L
  have : IsNonarchimedeanLocalField L := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨α, hα, hA⟩ := TauCeti.exists_isUnitFiltrationLattice_span_orbit (K := K) (L := L)
    hϖ.ne_zero ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
  have hσ (σ : L ≃ₐ[K] L) : span 𝒪[K] (orbit (L ≃ₐ[K] L) α) ≤
      (span 𝒪[K] (orbit (L ≃ₐ[K] L) α)).comap
        (Representation.ofDistribMulAction 𝒪[K] (L ≃ₐ[K] L) 𝒪[L] σ) :=
    (Module.End.mem_invtSubmodule _).1 <| Module.End.span_orbit_mem_invtSubmodule _ α σ
  have hV : ∀ (σ : Gal(L/K)), ∀ x ∈ unitsSub L (hA.filtration 0),
      (Rep.ofAlgebraAutOnUnits K L).ρ σ x ∈ unitsSub L (hA.filtration 0) := by
    intro σ x hx
    exact hA.unitsMap_mem_filtration σ (fun _ ha ↦ hσ σ ha) hx
  refine ⟨hA.filtration 0, hV, ?_, ?_, ?_⟩
  · have key : ∀ x ∈ hA.filtration 0, (x : L) ∈ integers L := by
      intro x hx
      obtain ⟨a, _, h⟩ := hx
      rw [h, ← TauCeti.coe_integerRingEquivIntegralClosure_apply (K := K)]
      exact (TauCeti.integerRingEquivIntegralClosure K L _).2
    intro x hx
    exact ⟨key x hx, key x⁻¹ (inv_mem hx)⟩
  · obtain ⟨m, hm⟩ := hA.exists_unitFiltration_le_filtration 0
    have hϖm : ϖ ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
    refine ⟨ϖ ^ (m + 1), pow_ne_zero _ hϖ.ne_zero, (𝓂[K]).pow_mem_of_mem hϖm _ (Nat.succ_pos m), ?_⟩
    intro y hy h
    apply hm
    apply TauCeti.unitFiltration_antitone (Nat.le_succ m)
    rw [TauCeti.mem_unitFiltration_iff_exists]
    set y' : 𝒪[L] := (TauCeti.integerRingEquivIntegralClosure K L).symm ⟨y, hy⟩ with hy'
    have hyy : (y' : L) = y := TauCeti.coe_integerRingEquivIntegralClosure_symm_apply _
    have hmem : algebraMap 𝒪[K] 𝒪[L] ϖ ∈ 𝓂[L] :=
      IsLocalRing.map_maximalIdeal_le (algebraMap 𝒪[K] 𝒪[L]) (Ideal.mem_map_of_mem _ hϖm)
    have hz : algebraMap 𝒪[K] 𝒪[L] (ϖ ^ (m + 1)) * y' ∈ 𝓂[L] ^ (m + 1) := by
      rw [map_pow]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hmem _)
    have hu : IsUnit (1 + algebraMap 𝒪[K] 𝒪[L] (ϖ ^ (m + 1)) * y') :=
      isUnit_one_add_of_mem_maximalIdeal
        (Ideal.pow_le_self (Nat.succ_ne_zero m) hz)
    refine ⟨hu.unit, ?_, ?_⟩
    · simpa using hz
    · show ((1 + algebraMap 𝒪[K] 𝒪[L] (ϖ ^ (m + 1)) * y' : 𝒪[L]) : L) =
        1 + algebraMap K L ((ϖ ^ (m + 1) : 𝒪[K]) : K) * y
      push_cast
      rw [hyy]
  · intro r hr
    exact hA.isZero_groupCohomology_stableRep hσ (TauCeti.spanOrbitEquiv hα) hV r hr

end NumberFieldKB.MilneCFT.Ch3
