import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Tate
import NumberFieldKB.MilneCFT.Ch2Homology

/-!
# Milne, *Class Field Theory*: the sequence of the splitting module, and the carry cocycle

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

* `splitSeq`, `splitSeq_shortExact` — the short exact sequence $0 \to C \to C(\varphi) \to I_G \to 0$ of the
  splitting module of a 2-cocycle $\varphi$ (Chapter II, §3, sequence (24), p. 84), with $x_\tau \mapsto \tau - 1$
  (`splitProj_X`); $I_G$ is the kernel of the augmentation $\mathbb Z[G] \otimes \mathbb Z \to \mathbb Z$ of
  `augSeq`.
* `carryCocycle` — the 2-cocycle of a cyclic group used in Chapter III, §1, p. 102.
These are used to state Chapter III, Proposition 1.9.
-/


namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology groupHomology Limits MonoidalCategory

section SplitSeq

variable {G : Type} [Group G] [Fintype G] [DecidableEq G] (C : Rep ℤ G) (φ : cocycles₂ C)

/-- The elements `τ - 1 ∈ ℤ[G]`, `τ ≠ 1`. -/
noncomputable def splitGen (τ : {τ : G // τ ≠ 1}) : MonoidAlgebra ℤ G :=
  MonoidAlgebra.single (τ : G) (1 : ℤ) - 1

set_option backward.isDefEq.respectTransparency false in
/-- The additive map `C(φ) → ℤ[G] ⊗ ℤ`: `C ↦ 0`, `x_τ ↦ (τ - 1) ⊗ 1`. -/
noncomputable def splitProjAux : SplittingCarrier C →+ (leftRegular ℤ G ⊗ Rep.trivial ℤ G ℤ : Rep ℤ G) :=
  (((TensorProduct.mk ℤ (MonoidAlgebra ℤ G) ℤ).flip 1).toAddMonoidHom).comp
    ((Finsupp.linearCombination ℤ splitGen).toAddMonoidHom.comp (AddMonoidHom.snd C _))

@[simp] theorem splitProjAux_inl (c : C) : splitProjAux C ((c, 0) : SplittingCarrier C) = 0 := by
  simp [splitProjAux]

theorem splitProjAux_inr (n : {τ : G // τ ≠ 1} →₀ ℤ) :
    splitProjAux C (0, n) = (Finsupp.linearCombination ℤ splitGen n) ⊗ₜ[ℤ] (1 : ℤ) := by
  simp [splitProjAux]


set_option backward.isDefEq.respectTransparency false in
theorem splitProjAux_X (τ : G) :
    splitProjAux C (splittingX C φ τ) =
      (MonoidAlgebra.single τ (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) ⊗ₜ[ℤ] (1 : ℤ) := by
  by_cases h : τ = 1
  · subst h
    rw [splittingX_one, splitProjAux_inl]
    simp
  · simp only [splittingX, dite_eq_right h, splitProjAux_inr]
    simp [splitGen, MonoidAlgebra.one_def]

theorem splitting_ext' {A : Type*} [AddCommGroup A] {f g : SplittingCarrier C →+ A}
    (hC : ∀ c : C, f (c, 0) = g (c, 0))
    (hX : ∀ τ : G, τ ≠ 1 → f (splittingX C φ τ) = g (splittingX C φ τ)) : f = g := by
  refine AddMonoidHom.ext fun ⟨c, x⟩ => ?_
  have hcx : ((c, x) : SplittingCarrier C) = (c, 0) + (0, x) := by simp
  rw [hcx, map_add, map_add, hC]
  clear hcx
  congr 1
  induction x using Finsupp.induction_linear with
  | zero => simp only [Prod.mk_zero_zero, map_zero]
  | add a b ha hb =>
    have hab : ((0 : C), a + b) = ((0 : C), a) + (0, b) := by simp
    rw [hab, map_add, map_add, ha, hb]
  | single τ n =>
    have hτ : ((0 : C), Finsupp.single τ n) = n • splittingX C φ τ := by
      simp only [splittingX, τ.2, dite_false, Prod.smul_mk, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [zsmul_zero]
    rw [hτ, map_zsmul, map_zsmul, hX τ τ.2]

set_option backward.isDefEq.respectTransparency false in
theorem splitProjAux_equivariant (σ : G) (x : SplittingCarrier C) :
    splitProjAux C ((splittingModule C φ).ρ σ x) =
      (leftRegular ℤ G ⊗ Rep.trivial ℤ G ℤ : Rep ℤ G).ρ σ (splitProjAux C x) := by
  have := splitting_ext' C φ
    (f := (splitProjAux C).comp (splittingAct C φ σ))
    (g := ((leftRegular ℤ G ⊗ Rep.trivial ℤ G ℤ : Rep ℤ G).ρ σ).toAddMonoidHom.comp (splitProjAux C))
    (fun c => by
      simp only [AddMonoidHom.comp_apply, splittingAct_inl]
      rw [splitProjAux_inl, splitProjAux_inl]; simp)
    (fun τ _ => by
      simp only [AddMonoidHom.comp_apply, splittingAct_X, map_add, map_sub, splitProjAux_X, splitProjAux_inl]
      simp [Representation.ofMulAction_single, TensorProduct.sub_tmul])
  exact DFunLike.congr_fun this x


set_option backward.isDefEq.respectTransparency false in
theorem augTensor_tmul_one (a : MonoidAlgebra ℤ G) :
    (augTensor (Rep.trivial ℤ G ℤ)).hom (a ⊗ₜ[ℤ] (1 : ℤ)) = augmentation G a := by
  change (augTensorAux (Rep.trivial ℤ G ℤ)).hom _ = _
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [TensorProduct.add_tmul, map_add, ha, hb, map_add]
  | single x r => rw [augTensorAux_single, augmentation_single]; simp

set_option backward.isDefEq.respectTransparency false in
/-- The `G`-map `C(φ) → ℤ[G] ⊗ ℤ`, `C ↦ 0`, `x_τ ↦ (τ - 1) ⊗ 1`. -/
noncomputable def splitProjEnd : splittingModule C φ ⟶ (leftRegular ℤ G ⊗ Rep.trivial ℤ G ℤ : Rep ℤ G) :=
  Rep.ofHom ⟨(splitProjAux C).toIntLinearMap, fun σ => LinearMap.ext fun x => by
    exact splitProjAux_equivariant C φ σ x⟩

theorem splitProjEnd_apply (x : SplittingCarrier C) :
    (splitProjEnd C φ).hom x = splitProjAux C x := rfl

set_option backward.isDefEq.respectTransparency false in
theorem splitProjEnd_comp_augTensor : splitProjEnd C φ ≫ augTensor (Rep.trivial ℤ G ℤ) = 0 := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  change (augTensor (Rep.trivial ℤ G ℤ)).hom (splitProjAux C x) = 0
  have := splitting_ext' C φ
    (f := ((augTensor (Rep.trivial ℤ G ℤ)).hom.toLinearMap.toAddMonoidHom).comp (splitProjAux C))
    (g := 0) (fun c => by
      change (augTensor (Rep.trivial ℤ G ℤ)).hom (splitProjAux C (c, 0)) = 0
      rw [splitProjAux_inl, map_zero])
    (fun τ _ => by
      change (augTensor (Rep.trivial ℤ G ℤ)).hom (splitProjAux C (splittingX C φ τ)) = 0
      rw [splitProjAux_X, augTensor_tmul_one]
      simp [augmentation_single])
  exact DFunLike.congr_fun this x


set_option backward.isDefEq.respectTransparency false in
/-- The inclusion `C → C(φ)`, `c ↦ (c, 0)`. -/
noncomputable def splitIncl : C ⟶ splittingModule C φ :=
  Rep.ofHom ⟨({ toFun := fun c => ((c, 0) : SplittingCarrier C)
                map_add' := fun a b => by
                  change ((a + b, 0) : SplittingCarrier C) = (a, 0) + (b, 0)
                  simp
                map_smul' := fun n c => by
                  simp only [RingHom.id_apply]
                  have h := map_zsmul (AddMonoidHom.inl C ({σ : G // σ ≠ 1} →₀ ℤ)) n c
                  simp only [AddMonoidHom.inl_apply] at h
                  have e := Int.cast_smul_eq_zsmul ℤ n c
                  simp only [Int.cast_id] at e
                  rw [e]
                  exact h } : C →ₗ[ℤ] splittingModule C φ), by
    intro σ
    refine LinearMap.ext fun c => ?_
    exact (splittingModule_ρ_inl C φ σ c).symm⟩

set_option backward.isDefEq.respectTransparency false in
theorem splitIncl_apply (c : C) :
    ((splitIncl C φ).hom c : SplittingCarrier C) = ((c, 0) : SplittingCarrier C) := rfl

/-- The projection `C(φ) → I_G`, `C ↦ 0`, `x_τ ↦ τ - 1`, with `I_G` the kernel of the augmentation
`ℤ[G] ⊗ ℤ → ℤ`. -/
noncomputable def splitProj : splittingModule C φ ⟶ (augSeq (Rep.trivial ℤ G ℤ)).X₁ :=
  kernel.lift (augTensor (Rep.trivial ℤ G ℤ)) (splitProjEnd C φ) (splitProjEnd_comp_augTensor C φ)

set_option backward.isDefEq.respectTransparency false in
theorem splitProj_ι (x : splittingModule C φ) :
    kernel.ι (augTensor (Rep.trivial ℤ G ℤ)) ((splitProj C φ).hom x) = splitProjAux C x := by
  show (splitProj C φ ≫ kernel.ι (augTensor (Rep.trivial ℤ G ℤ))).hom x = _
  rw [splitProj, kernel.lift_ι]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem splitProj_X (τ : G) :
    kernel.ι (augTensor (Rep.trivial ℤ G ℤ)) ((splitProj C φ).hom (splittingX C φ τ)) =
      (MonoidAlgebra.single τ (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) ⊗ₜ[ℤ] (1 : ℤ) := by
  rw [splitProj_ι, splitProjAux_X]

set_option backward.isDefEq.respectTransparency false in
theorem splitProj_inl (c : C) :
    (splitProj C φ).hom (((c, 0) : SplittingCarrier C) : splittingModule C φ) = 0 := by
  have hι : Function.Injective (kernel.ι (augTensor (Rep.trivial ℤ G ℤ))).hom :=
    (Rep.mono_iff_injective _).1 inferInstance
  apply hι
  refine Eq.trans ?_ (map_zero _).symm
  exact (splitProj_ι C φ _).trans (splitProjAux_inl C c)

set_option backward.isDefEq.respectTransparency false in
theorem splitIncl_comp_splitProj : splitIncl C φ ≫ splitProj C φ = 0 := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun c => ?_))
  exact splitProj_inl C φ c

/-- Milne's sequence (24): `0 → C → C(φ) → I_G → 0`. -/
noncomputable def splitSeq : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (splitIncl C φ) (splitProj C φ) (splitIncl_comp_splitProj C φ)


theorem tmul_one_eq (t : TensorProduct ℤ (MonoidAlgebra ℤ G) ℤ) :
    t = (TensorProduct.rid ℤ (MonoidAlgebra ℤ G) t) ⊗ₜ[ℤ] (1 : ℤ) :=
  ((TensorProduct.rid ℤ (MonoidAlgebra ℤ G)).symm_apply_apply t).symm.trans
    (TensorProduct.rid_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
theorem splitProj_surjective : Function.Surjective (splitProj C φ).hom := by
  have hι : Function.Injective (kernel.ι (augTensor (Rep.trivial ℤ G ℤ))).hom :=
    (Rep.mono_iff_injective _).1 inferInstance
  intro y
  set t : TensorProduct ℤ (MonoidAlgebra ℤ G) ℤ := (kernel.ι (augTensor (Rep.trivial ℤ G ℤ))).hom y with ht
  have h0 : (augTensor (Rep.trivial ℤ G ℤ)).hom t = 0 := by
    rw [ht, ← Rep.comp_apply, kernel.condition]; rfl
  set a := TensorProduct.rid ℤ (MonoidAlgebra ℤ G) t with ha
  have hta : t = a ⊗ₜ[ℤ] (1 : ℤ) := tmul_one_eq t
  have hmem : a ∈ augmentationIdeal G := by
    rw [mem_augmentationIdeal, ← augTensor_tmul_one, ← hta]; exact h0
  obtain ⟨-, hspan⟩ := augmentationIdeal_basis G
  rw [← hspan, Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨n, hn⟩ := hmem
  refine ⟨((0 : C), n), hι ?_⟩
  rw [splitProj_ι]
  change splitProjAux C (0, n) = t
  rw [splitProjAux_inr, hta, ← hn]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem splitSeq_shortExact : (splitSeq C φ).ShortExact := by
  have hmono : Mono (splitSeq C φ).f := by
    rw [Rep.mono_iff_injective]
    intro a b hab
    have := congrArg Prod.fst hab
    exact this
  have hepi : Epi (splitSeq C φ).g := by
    rw [Rep.epi_iff_surjective]
    exact splitProj_surjective C φ
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ G) (ModuleCat ℤ)),
    ShortComplex.moduleCat_exact_iff]
  have hι : Function.Injective (kernel.ι (augTensor (Rep.trivial ℤ G ℤ))).hom :=
    (Rep.mono_iff_injective _).1 inferInstance
  intro x hx
  obtain ⟨c, n⟩ := x
  have h1 : splitProjAux C (c, n) = 0 := by
    have := congrArg (kernel.ι (augTensor (Rep.trivial ℤ G ℤ))).hom
      (show (splitProj C φ).hom (c, n) = 0 from hx)
    rw [splitProj_ι, map_zero] at this
    exact this
  have hcn : ((c, n) : SplittingCarrier C) = (c, 0) + (0, n) := by simp
  rw [hcn, map_add, splitProjAux_inl, zero_add, splitProjAux_inr] at h1
  have h2 : Finsupp.linearCombination ℤ splitGen n = 0 := by
    have := congrArg (TensorProduct.rid ℤ (MonoidAlgebra ℤ G)) h1
    simpa using this
  obtain ⟨hli, -⟩ := augmentationIdeal_basis G
  have hn : n = 0 := (linearIndependent_iff.1 hli) n h2
  subst hn
  exact ⟨c, rfl⟩

end SplitSeq

end NumberFieldKB.MilneCFT

namespace NumberFieldKB.MilneCFT
open groupCohomology

variable {G : Type} [Group G] [Fintype G] {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ)

/-- The exponent $i \in [0, n)$ with $\tau = \sigma^i$, for a generator $\sigma$ of a cyclic group of
order $n$. -/
noncomputable def cycExp (τ : G) : ℕ :=
  (Multiplicative.toAdd ((zmodMulEquivOfGenerator hσ (n := Nat.card G) rfl).symm τ)).val

local instance : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩

include hσ in
theorem cycExp_lt (τ : G) : cycExp hσ τ < Nat.card G := ZMod.val_lt _

include hσ in
theorem pow_cycExp (τ : G) : σ ^ cycExp hσ τ = τ := by
  have key : (zmodMulEquivOfGenerator hσ (n := Nat.card G) rfl).symm (σ ^ cycExp hσ τ)
      = (zmodMulEquivOfGenerator hσ (n := Nat.card G) rfl).symm τ := by
    have := zmodMulEquivOfGenerator_symm_apply_zpow hσ (n := Nat.card G) rfl (cycExp hσ τ : ℤ)
    rw [zpow_natCast] at this
    rw [this]
    unfold cycExp
    simp
  exact ((zmodMulEquivOfGenerator hσ (n := Nat.card G) rfl).symm.injective key)

include hσ in
theorem cycExp_mul (τ τ' : G) :
    cycExp hσ (τ * τ') = (cycExp hσ τ + cycExp hσ τ') % Nat.card G := by
  unfold cycExp
  rw [map_mul]
  exact ZMod.val_add _ _

/-- **The carry cocycle** (Milne, Chapter III, §1, p. 102): for $G$ cyclic of order $n$ generated by $\sigma$ and
$p \in M^G$, $\varphi(\sigma^i, \sigma^j) = 0$ if $i + j < n$ and $p$ otherwise ($0 \le i, j < n$). With $M = L^\times$
and $p = \pi$ it represents the fundamental class of an unramified $L/K$ (Milne: values $1$ and $\pi$). -/
noncomputable def carryCocycle (M : Rep ℤ G) (p : M) (hp : ∀ g : G, M.ρ g p = p) :
    cocycles₂ M :=
  ⟨fun x => if cycExp hσ x.1 + cycExp hσ x.2 < Nat.card G then 0 else p, by
    rw [mem_cocycles₂_iff]
    intro g h j
    have hg := cycExp_lt hσ g
    have hh := cycExp_lt hσ h
    have hj := cycExp_lt hσ j
    simp only [cycExp_mul hσ]
    generalize Nat.card G = n at *
    generalize cycExp hσ g = x at *
    generalize cycExp hσ h = y at *
    generalize cycExp hσ j = z at *
    by_cases h1 : x + y < n <;> by_cases h2 : y + z < n
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]; split_ifs <;> first | omega | simp [hp]
    · have e : (y + z) % n = y + z - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt h1, e]; split_ifs <;> first | omega | simp [hp]
    · have e : (x + y) % n = x + y - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e, Nat.mod_eq_of_lt h2]; split_ifs <;> first | omega | simp [hp]
    · have e : (x + y) % n = x + y - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have e' : (y + z) % n = y + z - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e, e']; split_ifs <;> first | omega | simp [hp]⟩

theorem carryCocycle_apply (M : Rep ℤ G) (p : M) (hp : ∀ g : G, M.ρ g p = p) (x : G × G) :
    (carryCocycle hσ M p hp : G × G → M) x
      = if cycExp hσ x.1 + cycExp hσ x.2 < Nat.card G then 0 else p := rfl

end NumberFieldKB.MilneCFT
