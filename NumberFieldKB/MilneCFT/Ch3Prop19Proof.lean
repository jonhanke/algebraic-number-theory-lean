import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Prop19
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Connecting.LowDegree
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Connecting.GroupHomology

/-!
# Milne, *Class Field Theory*, Chapter III §1: explicit form of Proposition 1.9

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

The composite `prop19Map` of Ch3Prop19.lean is computed explicitly from the following descriptions of the Tate
connecting maps in low degrees:

* `delta_aug_neg_two` — the connecting map of `augSeq` from $\hat H^{-2}$ to $\hat H^{-1}$ sends the class of
  $[\tau] \in H_1(G, \mathbb Z)$ to the class of $(\tau^{-1} - 1) \otimes 1$ (Mathlib's chain differential
  $d_{10}(g \otimes a) = g^{-1}a - a$ is what produces the inverse);
* `delta_split` — the connecting map of `splitSeq` from $\hat H^{-1}$ to $\hat H^0$ sends the class of
  $(\rho - 1) \otimes 1$ to the class of $\mathrm{Nm}(x_\rho) = \sum_g \varphi(g, \rho)$;
* `tateZeroUnitsEquiv_H0π` — the value of `tateZeroUnitsEquiv` on a class of norms.

Consequently (`prop19Map_eq`) $\tau \mapsto [\pi^{e(\tau^{-1})}]$ where $\tau^{-1} = \sigma^{e}$, $0 \le e < n$.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep Limits MonoidalCategory groupHomology groupCohomology NumberFieldKB.MilneCFT
  NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

section LowDegree

variable {G : Type} [Group G] [Fintype G]

set_option backward.isDefEq.respectTransparency false in
/-- The degree `-1` comparison with `H₀` sends the class of a norm-zero element to its class in `H₀`. -/
theorem toGH_HNegOne (M : Rep ℤ G) (z : LinearMap.ker M.ρ.norm) :
    (TauCeti.TateCohomology.toGroupHomology M 0).hom
      ((TauCeti.TateCohomology.HNegOneπ M).hom z) = groupHomology.H0π M z.1 := by
  have := ConcreteCategory.congr_hom (TauCeti.TateCohomology.HNegOneπ_comp_toGroupHomology M) z
  simp only [ConcreteCategory.comp_apply] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
/-- The connecting map `H₁(G, ℤ) → H₀(G, I_G)` of `augSeq` sends `[τ] ⊗ 1` to the class of `(τ⁻¹ - 1) ⊗ 1`. -/
theorem delta_H1_tau (τ : G)
    (x'' : (augSeq (trivial ℤ G ℤ)).X₁)
    (hx : (augSeq (trivial ℤ G ℤ)).f.hom x'' =
      (MonoidAlgebra.single τ⁻¹ (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) ⊗ₜ[ℤ] (1 : ℤ)) :
    groupHomology.δ (augSeq_shortExact (trivial ℤ G ℤ)) 1 0 rfl
      ((groupHomology.H1AddEquivOfIsTrivial (trivial ℤ G ℤ)).symm
          (Additive.ofMul (Abelianization.of τ) ⊗ₜ (1 : ℤ))) =
      groupHomology.H0π (augSeq (trivial ℤ G ℤ)).X₁ x'' := by
  classical
  rw [H1AddEquivOfIsTrivial_symm_tmul]
  refine δ₀_apply (augSeq_shortExact (trivial ℤ G ℤ)) _
    (Finsupp.single τ ((MonoidAlgebra.single 1 (1 : ℤ)) ⊗ₜ[ℤ] (1 : ℤ))) ?_ x'' ?_
  · change _ = Finsupp.single τ (1 : ℤ)
    have h : (augTensor (trivial ℤ G ℤ)).hom (MonoidAlgebra.single 1 (1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) = (1 : ℤ) := by
      rw [augTensor_tmul_one, augmentation_single]
    ext g
    simp
    erw [h]
  · rw [d₁₀_single, hx]
    simp [TensorProduct.sub_tmul]
    symm
    change (leftRegular ℤ G ⊗ Rep.trivial ℤ G ℤ : Rep ℤ G).ρ τ⁻¹ _ = _
    simp [Representation.ofMulAction_single]

set_option backward.isDefEq.respectTransparency false in
/-- **The connecting map $\hat H^{-2}(G, \mathbb Z) \to \hat H^{-1}(G, I_G)$ of `augSeq`**: it sends the class
of $[\tau] \in H_1(G, \mathbb Z)$ (through `isoGroupHomology` and `H1AddEquivOfIsTrivial`) to the class of
$(\tau^{-1} - 1) \otimes 1 \in I_G$. -/
theorem delta_aug_neg_two (τ : G)
    (x'' : (augSeq (trivial ℤ G ℤ)).X₁)
    (hx : (augSeq (trivial ℤ G ℤ)).f.hom x'' =
      (MonoidAlgebra.single τ⁻¹ (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) ⊗ₜ[ℤ] (1 : ℤ))
    (hn : x'' ∈ LinearMap.ker (augSeq (trivial ℤ G ℤ)).X₁.ρ.norm) :
    (TateCohomology.δ (augSeq_shortExact (trivial ℤ G ℤ)) (-2)).hom
      (((TateCohomology.isoGroupHomology (R := ℤ) (G := G) (-2) 1 (by norm_num)).app
        (trivial ℤ G ℤ)).inv.hom
        ((groupHomology.H1AddEquivOfIsTrivial (trivial ℤ G ℤ)).symm
          (Additive.ofMul (Abelianization.of τ) ⊗ₜ (1 : ℤ)))) =
      (TauCeti.TateCohomology.HNegOneπ (augSeq (trivial ℤ G ℤ)).X₁).hom ⟨x'', hn⟩ := by
  have hS := augSeq_shortExact (trivial ℤ G ℤ)
  have inj : Function.Injective (TauCeti.TateCohomology.toGroupHomology (augSeq (trivial ℤ G ℤ)).X₁ 0).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply inj
  have h1 := ConcreteCategory.congr_hom (TauCeti.TateCohomology.δ_comp_toGroupHomology hS 0)
    (((TateCohomology.isoGroupHomology (R := ℤ) (G := G) (-2) 1 (by norm_num)).app
        (trivial ℤ G ℤ)).inv.hom
        ((groupHomology.H1AddEquivOfIsTrivial (trivial ℤ G ℤ)).symm
          (Additive.ofMul (Abelianization.of τ) ⊗ₜ (1 : ℤ))))
  have h2 : (TauCeti.TateCohomology.toGroupHomology (trivial ℤ G ℤ) 1).hom
      (((TateCohomology.isoGroupHomology (R := ℤ) (G := G) (-2) 1 (by norm_num)).app
        (trivial ℤ G ℤ)).inv.hom
        ((groupHomology.H1AddEquivOfIsTrivial (trivial ℤ G ℤ)).symm
          (Additive.ofMul (Abelianization.of τ) ⊗ₜ (1 : ℤ)))) =
      (groupHomology.H1AddEquivOfIsTrivial (trivial ℤ G ℤ)).symm
          (Additive.ofMul (Abelianization.of τ) ⊗ₜ (1 : ℤ)) := by
    rw [TauCeti.TateCohomology.toGroupHomology_eq_negSuccIso_hom]
    exact Iso.inv_hom_id_apply (TauCeti.TateCohomology.negSuccIso (trivial ℤ G ℤ) 1) _
  simp only [ConcreteCategory.comp_apply] at h1
  rw [toGH_HNegOne]
  refine h1.trans ?_
  erw [h2]
  exact delta_H1_tau τ x'' hx

set_option backward.isDefEq.respectTransparency false in
/-- Every element $(\rho - 1) \otimes 1$ of $\mathbb Z[G] \otimes \mathbb Z$ lies in $I_G$ and has norm zero
there. -/
theorem exists_aug_elem (ρ : G) :
    ∃ (x'' : (augSeq (trivial ℤ G ℤ)).X₁)
      (_ : x'' ∈ LinearMap.ker (augSeq (trivial ℤ G ℤ)).X₁.ρ.norm),
      (augSeq (trivial ℤ G ℤ)).f.hom x'' =
        (MonoidAlgebra.single ρ (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) ⊗ₜ[ℤ] (1 : ℤ) := by
  classical
  have hS := augSeq_shortExact (trivial ℤ G ℤ)
  have hinj : Function.Injective (augSeq (trivial ℤ G ℤ)).f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have he : Function.Exact (augSeq (trivial ℤ G ℤ)).f.hom (augSeq (trivial ℤ G ℤ)).g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.exact.map (forget₂ (Rep ℤ G) (ModuleCat ℤ)))
  have h0 : (augSeq (trivial ℤ G ℤ)).g.hom
      ((MonoidAlgebra.single ρ (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) ⊗ₜ[ℤ] (1 : ℤ)) = 0 := by
    change (augTensor (trivial ℤ G ℤ)).hom _ = 0
    rw [augTensor_tmul_one, map_sub, augmentation_single, augmentation_single, sub_self]
  obtain ⟨x'', hx''⟩ := (he _).1 h0
  refine ⟨x'', ?_, hx''⟩
  show (Representation.norm (augSeq (trivial ℤ G ℤ)).X₁.ρ) x'' = 0
  apply hinj
  rw [map_zero]
  simp only [Representation.norm, LinearMap.sum_apply, map_sum, Rep.hom_comm_apply, hx'']
  have hρ : ∀ g : G, (augSeq (trivial ℤ G ℤ)).X₂.ρ g
      ((MonoidAlgebra.single ρ (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) ⊗ₜ[ℤ] (1 : ℤ)) =
      (MonoidAlgebra.single (g * ρ) (1 : ℤ) - MonoidAlgebra.single g (1 : ℤ)) ⊗ₜ[ℤ] (1 : ℤ) := by
    intro g
    change (leftRegular ℤ G ⊗ Rep.trivial ℤ G ℤ : Rep ℤ G).ρ g _ = _
    rw [TensorProduct.sub_tmul, TensorProduct.sub_tmul, map_sub]
    simp [Representation.ofMulAction_single]
  simp only [hρ]
  rw [← TensorProduct.sum_tmul, Finset.sum_sub_distrib]
  have h2 : ∑ g : G, (MonoidAlgebra.single (g * ρ) (1 : ℤ) : MonoidAlgebra ℤ G) =
      ∑ g : G, MonoidAlgebra.single g (1 : ℤ) :=
    Fintype.sum_equiv (Equiv.mulRight ρ) _ _ (fun g => rfl)
  rw [h2, sub_self, TensorProduct.zero_tmul]

set_option backward.isDefEq.respectTransparency false in
/-- The identification `tateZeroEquiv` sends the class of an invariant to its class modulo the norms. -/
theorem tateZeroEquiv_H0π (M : Rep.{0,0,0} ℤ G) (a : M.ρ.invariants) :
    tateZeroEquiv M ((TauCeti.TateCohomology.H0π M).hom a) = QuotientAddGroup.mk a := by
  rw [TauCeti.TateCohomology.H0π_eq_H0CyclesIso_inv_comp_homologyπ]
  unfold tateZeroEquiv
  simp only [AddEquiv.trans_apply]
  set c := (TauCeti.TateCohomology.H0CyclesIso M).inv a with hc
  have hA := ConcreteCategory.congr_hom
    (HomologicalComplex.π_homologyIsoSc'_hom (tateComplex M) (-1) 0 1 (by simp) (by simp)) c
  have hB := ConcreteCategory.congr_hom
    ((tateComplex M).sc' (-1) 0 1).π_moduleCatCyclesIso_hom
    (((tateComplex M).cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).hom c)
  simp only [ConcreteCategory.comp_apply] at hA hB
  have h1 := ConcreteCategory.congr_hom
    ((tateComplex M).sc' (-1) 0 1).moduleCatCyclesIso_hom_i
    (((tateComplex M).cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).hom c)
  have h2 := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesIsoSc'_hom_iCycles (tateComplex M) (-1) 0 1 (by simp) (by simp)) c
  have h3 := ConcreteCategory.congr_hom (TauCeti.TateCohomology.H0CyclesIso_inv_comp_iCycles M) a
  simp only [ConcreteCategory.comp_apply] at h1 h2 h3
  have hE : ((HomologicalComplex.homologyIsoSc' (tateComplex M) (-1) 0 1 (by simp) (by simp) ≪≫
              (HomologicalComplex.sc' (tateComplex M) (-1) 0
                    1).moduleCatLeftHomologyData.homologyIso).toLinearEquiv.toAddEquiv
        ((ModuleCat.Hom.hom
            ((TauCeti.TateCohomology.H0CyclesIso M).inv ≫ HomologicalComplex.homologyπ (tateComplex M) 0))
          a)) = _ := (congrArg _ hA).trans hB
  erw [hE]
  generalize hk : (ConcreteCategory.hom (HomologicalComplex.sc' (tateComplex M) (-1) 0 1).moduleCatCyclesIso.hom)
        ((ConcreteCategory.hom (HomologicalComplex.cyclesIsoSc' (tateComplex M) (-1) 0 1 (by simp) (by simp)).hom) c) = k at h1 ⊢
  have hk' := h1.trans (h2.trans h3)
  show (QuotientAddGroup.mk _ : M.ρ.invariants ⧸ normRange M) = QuotientAddGroup.mk a
  congr 1
  apply Subtype.ext
  change (cochainsIso₀ M).hom ((ConcreteCategory.hom (HomologicalComplex.sc' (tateComplex M) (-1) 0 1).moduleCatLeftHomologyData.i) k) = a.1
  rw [hk']
  exact ConcreteCategory.congr_hom (Iso.inv_hom_id (cochainsIso₀ M)) a.1

end LowDegree

section Units

theorem quotAddEquivAdditive_mk {A : Type} [CommGroup A] (N : Subgroup A) {B : Type}
    [AddCommGroup B] (Q : AddSubgroup B) (φ : Additive A →+ B) (hφ : Function.Surjective φ)
    (h : ∀ x : Additive A, φ x ∈ Q ↔ x.toMul ∈ N) (x : Additive A) :
    quotAddEquivAdditive N Q φ hφ h (QuotientAddGroup.mk (φ x)) =
      Additive.ofMul (QuotientGroup.mk x.toMul) := by
  unfold quotAddEquivAdditive
  simp only [AddEquiv.trans_apply]
  have e1 : ∀ (π : Additive A →+ B ⧸ Q) (hπ : Function.Surjective π),
      (QuotientAddGroup.quotientKerEquivOfSurjective π hπ).symm (π x) = QuotientAddGroup.mk x :=
    fun π hπ => (AddEquiv.symm_apply_eq _).2 rfl
  erw [e1 ((QuotientAddGroup.mk' Q).comp φ) ((QuotientAddGroup.mk'_surjective _).comp hφ)]
  rfl

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

set_option backward.isDefEq.respectTransparency false in
/-- `tateZeroUnitsEquiv` sends the class of the invariant `k ∈ K^×` to its class in `K^×/Nm L^×`. -/
theorem tateZeroUnitsEquiv_H0π (k : Kˣ) (a : (Rep.ofAlgebraAutOnUnits K L).ρ.invariants)
    (ha : a = unitsToInv K L (Additive.ofMul k)) :
    tateZeroUnitsEquiv K L ((TauCeti.TateCohomology.H0π (Rep.ofAlgebraAutOnUnits K L)).hom a) =
      Additive.ofMul (QuotientGroup.mk k) := by
  subst ha
  unfold tateZeroUnitsEquiv
  simp only [AddEquiv.trans_apply]
  rw [tateZeroEquiv_H0π]
  exact quotAddEquivAdditive_mk _ _ _ _ _ _

end Units

section Split

variable {G : Type} [Group G] [Fintype G] [DecidableEq G] (C : Rep ℤ G) (φ : cocycles₂ C)

set_option backward.isDefEq.respectTransparency false in
/-- The norm of $x_\rho - x_1$ in the splitting module is $\sum_g (\varphi(g, \rho) - \varphi(g, 1)) \in C$. -/
theorem norm_split_X (ρ : G) :
    (splittingModule C φ).ρ.norm (splittingX C φ ρ - splittingX C φ 1) =
      ((∑ g : G, ((φ : G × G → C) (g, ρ) - (φ : G × G → C) (g, 1)) : C), 0) := by
  have h1 : ∀ g : G, splittingAct C φ g (splittingX C φ ρ - splittingX C φ 1 : SplittingCarrier C) =
      (splittingX C φ (g * ρ) - splittingX C φ g +
        (((φ : G × G → C) (g, ρ) - (φ : G × G → C) (g, 1) : C), 0) : SplittingCarrier C) := by
    intro g
    rw [map_sub, splittingAct_X, splittingAct_X, mul_one]
    refine Prod.ext ?_ ?_ <;> simp <;> abel
  simp only [Representation.norm, LinearMap.sum_apply]
  change ∑ g : G, splittingAct C φ g (splittingX C φ ρ - splittingX C φ 1 : SplittingCarrier C) =
    ((∑ g : G, ((φ : G × G → C) (g, ρ) - (φ : G × G → C) (g, 1)) : C), 0)
  rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h2 : ∑ g : G, splittingX C φ (g * ρ) = ∑ g : G, splittingX C φ g :=
    Fintype.sum_equiv (Equiv.mulRight ρ) _ _ (fun g => rfl)
  rw [h2, sub_self, zero_add]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]

set_option backward.isDefEq.respectTransparency false in
/-- **The connecting map $\hat H^{-1}(G, I_G) \to \hat H^0(G, C)$ of `splitSeq`**: it sends the class of
$(\rho - 1) \otimes 1$ to the class of the norm $\sum_g (\varphi(g, \rho) - \varphi(g, 1))$ of $x_\rho - x_1$
(Milne's computation $\mathrm{Nm}(x_\sigma) = \sum_\tau \varphi(\tau, \sigma)$, p. 102). -/
theorem delta_split (ρ : G) (x'' : (augSeq (trivial ℤ G ℤ)).X₁)
    (hx : (augSeq (trivial ℤ G ℤ)).f.hom x'' =
      (MonoidAlgebra.single ρ (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) ⊗ₜ[ℤ] (1 : ℤ))
    (hn : x'' ∈ LinearMap.ker (augSeq (trivial ℤ G ℤ)).X₁.ρ.norm) :
    ∃ hinv : (∑ g : G, ((φ : G × G → C) (g, ρ) - (φ : G × G → C) (g, 1)) : C) ∈ C.ρ.invariants,
      (TateCohomology.δ (splitSeq_shortExact C φ) (-1)).hom
        ((TauCeti.TateCohomology.HNegOneπ (augSeq (trivial ℤ G ℤ)).X₁).hom ⟨x'', hn⟩) =
      (TauCeti.TateCohomology.H0π C).hom
        ⟨(∑ g : G, ((φ : G × G → C) (g, ρ) - (φ : G × G → C) (g, 1)) : C), hinv⟩ := by
  have hfc : (splitSeq C φ).f.hom
      (∑ g : G, ((φ : G × G → C) (g, ρ) - (φ : G × G → C) (g, 1)) : C) =
      (splittingModule C φ).ρ.norm (splittingX C φ ρ - splittingX C φ 1) := by
    rw [norm_split_X]; rfl
  have hinv : (∑ g : G, ((φ : G × G → C) (g, ρ) - (φ : G × G → C) (g, 1)) : C) ∈ C.ρ.invariants := by
    intro h
    apply (Rep.mono_iff_injective (splitSeq C φ).f).mp (splitSeq_shortExact C φ).mono_f
    calc (splitSeq C φ).f.hom (C.ρ h _) = (splitSeq C φ).X₂.ρ h ((splitSeq C φ).f.hom _) :=
          (Rep.hom_comm_apply _ _ _)
      _ = (splittingModule C φ).ρ h ((splittingModule C φ).ρ.norm (splittingX C φ ρ - splittingX C φ 1)) := by
          rw [hfc]; rfl
      _ = (splittingModule C φ).ρ.norm (splittingX C φ ρ - splittingX C φ 1) :=
          Representation.self_norm_apply _ h _
      _ = _ := hfc.symm
  refine ⟨hinv, ?_⟩
  have hι : Function.Injective (augSeq (trivial ℤ G ℤ)).f.hom :=
    (Rep.mono_iff_injective _).1 (augSeq_shortExact (trivial ℤ G ℤ)).mono_f
  have hy : (splitSeq C φ).g.hom (splittingX C φ ρ - splittingX C φ 1) = x'' := by
    apply hι
    change kernel.ι (augTensor (Rep.trivial ℤ G ℤ)) ((splitProj C φ).hom _) = _
    rw [hx, map_sub, map_sub (ConcreteCategory.hom (kernel.ι (augTensor (Rep.trivial ℤ G ℤ)))),
      splitProj_X, splitProj_X]
    simp
  exact TauCeti.TateCohomology.δ_neg_one_HNegOneπ (splitSeq_shortExact C φ) ⟨x'', hn⟩ _ hy ⟨_, hinv⟩ hfc

end Split

section Cyclic

variable {G : Type} [Group G] [Fintype G] {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ)

include hσ in
theorem cycExp_one : cycExp hσ 1 = 0 := by
  simp [cycExp]

include hσ in
theorem cycExp_pow_natCast (i : ℕ) (hi : i < Nat.card G) : cycExp hσ (σ ^ i) = i := by
  unfold cycExp
  have := zmodMulEquivOfGenerator_symm_apply_zpow hσ (n := Nat.card G) rfl (i : ℤ)
  rw [zpow_natCast] at this
  rw [this]
  simpa using ZMod.val_cast_of_lt hi

include hσ in
theorem cycExp_gen : cycExp hσ σ = 1 % Nat.card G := by
  unfold cycExp
  rw [zmodMulEquivOfGenerator_symm_apply_generator]
  exact ZMod.val_one_eq_one_mod _

include hσ in
theorem sum_cycExp {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ g : G, f (cycExp hσ g) = ∑ i ∈ Finset.range (Nat.card G), f i := by
  refine Finset.sum_nbij' (cycExp hσ) (fun i => σ ^ i) ?_ ?_ ?_ ?_ ?_
  · intro g _
    exact Finset.mem_range.2 (cycExp_lt hσ g)
  · intro i _
    exact Finset.mem_univ _
  · intro g _
    exact pow_cycExp hσ g
  · intro i hi
    exact cycExp_pow_natCast hσ i (Finset.mem_range.1 hi)
  · intro g _
    rfl

theorem carry_sum {A : Type*} [AddCommGroup A] (p : A) (n e : ℕ) (he : e ≤ n) :
    ∑ i ∈ Finset.range n, (if i + e < n then (0 : A) else p) = e • p := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const]
  congr 1
  have : (Finset.range n).filter (fun i => ¬ (i + e < n)) = Finset.Ico (n - e) n := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]
  omega

include hσ in
/-- For the carry cocycle $\varphi$ of $(\sigma, p)$, $\sum_g (\varphi(g, \rho) - \varphi(g, 1)) = e\,p$ where
$\rho = \sigma^e$, $0 \le e < n$. -/
theorem carry_sum_G (M : Rep ℤ G) (p : M) (hp : ∀ g : G, M.ρ g p = p) (ρ : G) :
    ∑ g : G, (((carryCocycle hσ M p hp : cocycles₂ M) : G × G → M) (g, ρ) -
      ((carryCocycle hσ M p hp : cocycles₂ M) : G × G → M) (g, 1)) = cycExp hσ ρ • p := by
  have h1 : ∀ g : G, (((carryCocycle hσ M p hp : cocycles₂ M) : G × G → M) (g, ρ) -
      ((carryCocycle hσ M p hp : cocycles₂ M) : G × G → M) (g, 1)) =
      (fun i : ℕ => if i + cycExp hσ ρ < Nat.card G then (0 : M) else p) (cycExp hσ g) := by
    intro g
    rw [carryCocycle_apply, carryCocycle_apply, cycExp_one hσ, add_zero]
    have hg := cycExp_lt hσ g
    dsimp only
    simp only [hg, ↓reduceIte, sub_zero]
  rw [Finset.sum_congr rfl (fun g _ => h1 g)]
  refine (sum_cycExp hσ (fun i : ℕ => if i + cycExp hσ ρ < Nat.card G then (0 : M) else p)).trans ?_
  exact carry_sum p _ _ (cycExp_lt hσ ρ).le

end Cyclic

section Main

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

set_option backward.isDefEq.respectTransparency false in
/-- **Explicit form of `prop19Map`**: $\tau \mapsto [\pi^{e}]$ where $\tau^{-1} = \sigma^{e}$, $0 \le e < n$
(Milne's $\mathrm{Nm}(x_\sigma) = \pi$ computation, with the inverse coming from Mathlib's convention
$d_{10}(g \otimes a) = g^{-1}a - a$ for the differential of the chain complex). -/
theorem prop19Map_eq (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    {σ : Gal(L/K)} (hgen : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ) {π : 𝒪[K]} (hπ : Irreducible π)
    (τ : Gal(L/K)) :
    prop19Map L hgen hπ τ =
      Additive.ofMul (QuotientGroup.mk (primeUnit hπ ^ cycExp hgen τ⁻¹)) := by
  classical
  obtain ⟨x'', hn, hx⟩ := exists_aug_elem τ⁻¹
  have h1 := delta_aug_neg_two τ x'' hx hn
  obtain ⟨hinv, h2⟩ := delta_split (Rep.ofAlgebraAutOnUnits K L)
    (carryCocycle hgen (Rep.ofAlgebraAutOnUnits K L) (Additive.ofMul (embUnits L (primeUnit hπ)))
      (prime_fixed L hπ)) τ⁻¹ x'' hx hn
  unfold prop19Map
  simp only []
  rw [h1]
  have hsum := carry_sum_G hgen (Rep.ofAlgebraAutOnUnits K L)
    (Additive.ofMul (embUnits L (primeUnit hπ))) (prime_fixed L hπ) τ⁻¹
  refine Eq.trans (congrArg (tateZeroUnitsEquiv K L) h2) ?_
  refine tateZeroUnitsEquiv_H0π K L (primeUnit hπ ^ cycExp hgen τ⁻¹) _ ?_
  refine Subtype.ext ?_
  refine hsum.trans ?_
  rw [unitsToInv_coe, toMul_ofMul, map_pow, ofMul_pow]
  rfl

theorem primeUnit_pow_card_mem_normGroup (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] {π : 𝒪[K]} (hπ : Irreducible π) :
    primeUnit hπ ^ Nat.card Gal(L/K) ∈ normGroup L := by
  refine ⟨embUnits L (primeUnit hπ), ?_⟩
  apply Units.ext
  have hc : Nat.card Gal(L/K) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  rw [hc]
  simp [Algebra.norm_algebraMap]

theorem primeUnit_pow_mul_card_mem_normGroup (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] {π : 𝒪[K]} (hπ : Irreducible π) (k : ℕ) :
    primeUnit hπ ^ (Nat.card Gal(L/K) * k) ∈ normGroup L := by
  rw [pow_mul]
  exact Subgroup.pow_mem _ (primeUnit_pow_card_mem_normGroup L hπ) k

/-- **Proposition 1.9, in the orientation produced by Mathlib's chain complex**: $\sigma^{-1}$ (rather than
$\sigma$) is sent to the class of $\pi$. -/
theorem prop19Map_inv_frob (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    {σ : Gal(L/K)} (hgen : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ) {π : 𝒪[K]} (hπ : Irreducible π) :
    prop19Map L hgen hπ σ⁻¹ = Additive.ofMul (QuotientGroup.mk (primeUnit hπ)) := by
  rw [prop19Map_eq, inv_inv, cycExp_gen hgen]
  congr 1
  rw [QuotientGroup.eq]
  have hmod := Nat.mod_add_div 1 (Nat.card Gal(L/K))
  have : (primeUnit hπ ^ (1 % Nat.card Gal(L/K)))⁻¹ * primeUnit hπ =
      primeUnit hπ ^ (Nat.card Gal(L/K) * (1 / Nat.card Gal(L/K))) := by
    have e : primeUnit hπ ^ (1 % Nat.card Gal(L/K) + Nat.card Gal(L/K) * (1 / Nat.card Gal(L/K))) =
        primeUnit hπ := by rw [hmod, pow_one]
    calc (primeUnit hπ ^ (1 % Nat.card Gal(L/K)))⁻¹ * primeUnit hπ
        = (primeUnit hπ ^ (1 % Nat.card Gal(L/K)))⁻¹ * (primeUnit hπ ^ (1 % Nat.card Gal(L/K)) *
            primeUnit hπ ^ (Nat.card Gal(L/K) * (1 / Nat.card Gal(L/K)))) := by
          rw [← pow_add, e]
      _ = _ := inv_mul_cancel_left _ _
  rw [this]
  exact primeUnit_pow_mul_card_mem_normGroup L hπ _

/-- At the Frobenius element $\sigma$ itself, `prop19Map` gives the class of $\pi^{-1}$. -/
theorem prop19Map_frob (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    {σ : Gal(L/K)} (hgen : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ) {π : 𝒪[K]} (hπ : Irreducible π) :
    prop19Map L hgen hπ σ = Additive.ofMul (QuotientGroup.mk (primeUnit hπ)⁻¹) := by
  rw [prop19Map_eq]
  congr 1
  rw [QuotientGroup.eq]
  have h1 := cycExp_mul hgen σ⁻¹ σ
  rw [inv_mul_cancel, cycExp_one hgen, cycExp_gen hgen] at h1
  obtain ⟨k, hk⟩ : Nat.card Gal(L/K) ∣ cycExp hgen σ⁻¹ + 1 % Nat.card Gal(L/K) :=
    Nat.dvd_of_mod_eq_zero h1.symm
  have hmod := Nat.mod_add_div 1 (Nat.card Gal(L/K))
  have : (primeUnit hπ ^ cycExp hgen σ⁻¹)⁻¹ * (primeUnit hπ)⁻¹ =
      (primeUnit hπ ^ (Nat.card Gal(L/K) * (k + 1 / Nat.card Gal(L/K))))⁻¹ := by
    have e2 : primeUnit hπ ^ (Nat.card Gal(L/K) * (k + 1 / Nat.card Gal(L/K))) =
        primeUnit hπ ^ cycExp hgen σ⁻¹ * primeUnit hπ := by
      rw [mul_add, ← hk, add_assoc, hmod, pow_succ]
    rw [e2, mul_inv_rev, mul_comm]
  rw [this]
  exact Subgroup.inv_mem _ (primeUnit_pow_mul_card_mem_normGroup L hπ _)

/-- The statement of Proposition 1.9 as literally formalized in `Prop1_9` (`prop19Map σ = [π]`) holds for a given
$(L, \sigma, \pi)$ if and only if $\pi^2 \in \mathrm{Nm}(L^\times)$ (for unramified $L$ of degree $n$ this means
$n \mid 2$), since `prop19Map σ = [π⁻¹]` (`prop19Map_frob`). The corrected statement is `prop19Map_inv_frob`. -/
theorem prop19Map_frob_eq_iff (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    {σ : Gal(L/K)} (hgen : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ) {π : 𝒪[K]} (hπ : Irreducible π) :
    prop19Map L hgen hπ σ = Additive.ofMul (QuotientGroup.mk (primeUnit hπ)) ↔
      primeUnit hπ ^ 2 ∈ normGroup L := by
  rw [prop19Map_frob, Additive.ofMul.injective.eq_iff, QuotientGroup.eq, inv_inv, ← pow_two]

variable (K Ω) in
/-- **Proposition 1.9** (Milne, *CFT*, III, p. 102), proved unconditionally in the corrected form of `Prop1_9`
(Mathlib's sign convention for the first connecting map, see its docstring). -/
@[kb "milne2020cft" "v4.03, Ch. III, Prop. 1.9, p. 102"]
theorem prop1_9 : Prop1_9 K Ω :=
  ⟨fun L _ _ _ _ _ hgen _ hπ => prop19Map_inv_frob L hgen hπ⟩

end Main

end NumberFieldKB.MilneCFT.Ch3
