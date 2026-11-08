import NumberFieldKB.MilneCFT.Ch2Remark313
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.HomologySequence
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Cup.Cyclic
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.ContCohomology.CarryCocycle

open CategoryTheory Rep Limits MonoidalCategory

namespace NumberFieldKB.MilneCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

section Diagrams

variable {G : Type} [Group G] [Fintype G]

theorem augKernelMap_ι {M N : Rep ℤ G} (f : M ⟶ N) :
    augKernelMap f ≫ kernel.ι (augTensor N) = kernel.ι (augTensor M) ≫ (𝟙 (leftRegular ℤ G) ⊗ₘ f) :=
  kernel.lift_ι _ _ _

/-- The sequence of kernels of the augmentations induced by a short exact sequence. -/
noncomputable def kSeq (S : ShortComplex (Rep ℤ G)) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (augKernelMap S.f) (augKernelMap S.g) (by
    refine (cancel_mono (kernel.ι (augTensor S.X₃))).1 ?_
    have h : (𝟙 (leftRegular ℤ G) ⊗ₘ S.f) ≫ (𝟙 (leftRegular ℤ G) ⊗ₘ S.g) = 0 := by
      rw [id_tensorHom, id_tensorHom, ← whiskerLeft_comp, S.zero]
      simp
    rw [Category.assoc, augKernelMap_ι, ← Category.assoc, augKernelMap_ι, Category.assoc, h]
    simp)

theorem kSeq_shortExact {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact)
    (hI : (S.map (tensorLeft (leftRegular ℤ G))).ShortExact) : (kSeq S).ShortExact := by
  have hιinj : ∀ M : Rep ℤ G, Function.Injective (kernel.ι (augTensor M)).hom := fun M =>
    (Rep.mono_iff_injective _).1 (augSeq_shortExact M).mono_f
  have hex : ∀ M : Rep ℤ G, Function.Exact (kernel.ι (augTensor M)).hom (augTensor M).hom := fun M =>
    functionExact_of_shortExact (augSeq_shortExact M)
  have hIex := functionExact_of_shortExact hI
  have hIinj : Function.Injective (𝟙 (leftRegular ℤ G) ⊗ₘ S.f).hom := by
    have := (Rep.mono_iff_injective _).1 hI.mono_f
    rwa [id_tensorHom]
  have hIsurj : Function.Surjective (𝟙 (leftRegular ℤ G) ⊗ₘ S.g).hom := by
    have := (Rep.epi_iff_surjective _).1 hI.epi_g
    rwa [id_tensorHom]
  have hIex' : Function.Exact (𝟙 (leftRegular ℤ G) ⊗ₘ S.f).hom (𝟙 (leftRegular ℤ G) ⊗ₘ S.g).hom := by
    rw [id_tensorHom, id_tensorHom]; exact hIex
  have hfinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hgsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hSex := functionExact_of_shortExact hS
  have haugsurj : ∀ M : Rep ℤ G, Function.Surjective (augTensor M).hom := fun M =>
    (Rep.epi_iff_surjective _).1 (augSeq_shortExact M).epi_g
  have hc : ∀ {M N : Rep ℤ G} (f : M ⟶ N) (k : (kernel (augTensor M) : Rep ℤ G)),
      (kernel.ι (augTensor N)).hom ((augKernelMap f).hom k) =
        (𝟙 (leftRegular ℤ G) ⊗ₘ f).hom ((kernel.ι (augTensor M)).hom k) := fun f k => by
    have := congrArg (fun φ => φ.hom k) (augKernelMap_ι f)
    simpa using this
  have ha : ∀ {M N : Rep ℤ G} (f : M ⟶ N) (x : (leftRegular ℤ G ⊗ M : Rep ℤ G)),
      (augTensor N).hom ((𝟙 (leftRegular ℤ G) ⊗ₘ f).hom x) = f.hom ((augTensor M).hom x) := fun f x => by
    have := congrArg (fun φ => φ.hom x) (whisker_comp_augTensor f)
    simpa using this
  refine shortExact_of_forget₂ ?_ ?_ ?_
  · intro a b hab
    apply hιinj S.X₁
    apply hIinj
    have := congrArg (kernel.ι (augTensor S.X₂)).hom hab
    change (kernel.ι (augTensor S.X₂)).hom ((augKernelMap S.f).hom a) =
      (kernel.ι (augTensor S.X₂)).hom ((augKernelMap S.f).hom b) at this
    erw [hc, hc] at this
    exact this
  · intro k
    obtain ⟨u, hu⟩ := hIsurj ((kernel.ι (augTensor S.X₃)).hom k)
    have h1 : S.g.hom ((augTensor S.X₂).hom u) = 0 := by
      rw [← ha, hu]
      exact (hex S.X₃).apply_apply_eq_zero k
    obtain ⟨a, ha'⟩ := (hSex _).1 h1
    obtain ⟨w, hw⟩ := haugsurj S.X₁ a
    have h2 : (augTensor S.X₂).hom (u - (𝟙 (leftRegular ℤ G) ⊗ₘ S.f).hom w) = 0 := by
      rw [map_sub, ha, hw, ha', sub_self]
    obtain ⟨k', hk'⟩ := (hex S.X₂ _).1 h2
    refine ⟨k', hιinj S.X₃ ?_⟩
    change (kernel.ι (augTensor S.X₃)).hom ((augKernelMap S.g).hom k') = _
    rw [hc, hk', map_sub, hu, hIex'.apply_apply_eq_zero, sub_zero]
  · intro k'
    constructor
    · intro hk'
      have h1 : (𝟙 (leftRegular ℤ G) ⊗ₘ S.g).hom ((kernel.ι (augTensor S.X₂)).hom k') = 0 := by
        erw [← hc]
        change (kernel.ι (augTensor S.X₃)).hom ((augKernelMap S.g).hom k') = 0
        change (augKernelMap S.g).hom k' = 0 at hk'
        rw [hk', map_zero]
      obtain ⟨v, hv⟩ := (hIex' _).1 h1
      have h2 : S.f.hom ((augTensor S.X₁).hom v) = 0 := by
        rw [← ha, hv]
        exact (hex S.X₂).apply_apply_eq_zero k'
      have h3 : (augTensor S.X₁).hom v = 0 := hfinj (by rw [h2, map_zero])
      obtain ⟨k'', hk''⟩ := (hex S.X₁ _).1 h3
      refine ⟨k'', hιinj S.X₂ ?_⟩
      change (kernel.ι (augTensor S.X₂)).hom ((augKernelMap S.f).hom k'') = _
      rw [hc, hk'', hv]
    · rintro ⟨k'', rfl⟩
      have := congrArg (fun φ => φ.hom k'') (kSeq S).zero
      exact this

/-- The `3 × 3` diagram of the augmentation sequences of a short exact sequence. -/
noncomputable def augDiag (S : ShortComplex (Rep ℤ G)) : ShortComplex (ShortComplex (Rep ℤ G)) :=
  ShortComplex.mk (augMap S.f) (augMap S.g) (by
    refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
    · exact (kSeq S).zero
    · change (𝟙 (leftRegular ℤ G) ⊗ₘ S.f) ≫ (𝟙 (leftRegular ℤ G) ⊗ₘ S.g) = 0
      rw [id_tensorHom, id_tensorHom, ← whiskerLeft_comp, S.zero]
      simp
    · exact S.zero)

/-- The `3 × 3` diagram of the cyclic sequences of a short exact sequence. -/
noncomputable def cycDiag (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (S : ShortComplex (Rep ℤ G)) :
    ShortComplex (ShortComplex (Rep ℤ G)) :=
  ShortComplex.mk (cyclicMap g hg S.f) (cyclicMap g hg S.g) (by
    refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
    · exact S.zero
    · change (𝟙 (leftRegular ℤ G) ⊗ₘ S.f) ≫ (𝟙 (leftRegular ℤ G) ⊗ₘ S.g) = 0
      rw [id_tensorHom, id_tensorHom, ← whiskerLeft_comp, S.zero]
      simp
    · exact (kSeq S).zero)

/-- The middle column is `S` tensored with the regular representation. -/
noncomputable def tensorColIso (S : ShortComplex (Rep ℤ G)) :
    S.map (tensorLeft (leftRegular ℤ G)) ≅ (augDiag S).map ShortComplex.π₂ :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by exact (Category.id_comp _).trans ((id_tensorHom _ _).trans (Category.comp_id _).symm))
    (by exact (Category.id_comp _).trans ((id_tensorHom _ _).trans (Category.comp_id _).symm))

theorem periodicity_δ_comm (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) {S : ShortComplex (Rep ℤ G)}
    (hS : S.ShortExact) (hI : (S.map (tensorLeft (leftRegular ℤ G))).ShortExact) (n : ℤ) :
    TateCohomology.δ hS n ≫ (TateCohomology.δ (augSeq_shortExact S.X₁) (n + 1) ≫
        TateCohomology.δ (cyclicSeq_shortExact g hg S.X₁) (n + 1 + 1)) =
      (TateCohomology.δ (augSeq_shortExact S.X₃) n ≫
        TateCohomology.δ (cyclicSeq_shortExact g hg S.X₃) (n + 1)) ≫ TateCohomology.δ hS (n + 1 + 1) := by
  have hI2 : ((augDiag S).map ShortComplex.π₂).ShortExact :=
    ShortComplex.shortExact_of_iso (tensorColIso S) hI
  have hK := kSeq_shortExact hS hI
  have A1 := TauCeti.TateCohomology.δ_comp_δ_eq_neg (augDiag S) (augSeq_shortExact S.X₁)
    (augSeq_shortExact S.X₂) (augSeq_shortExact S.X₃) hK hI2 hS n
  have B1 := TauCeti.TateCohomology.δ_comp_δ_eq_neg (cycDiag g hg S) (cyclicSeq_shortExact g hg S.X₁)
    (cyclicSeq_shortExact g hg S.X₂) (cyclicSeq_shortExact g hg S.X₃) hS hI2 hK (n + 1)
  have h1 : TateCohomology.δ hS n ≫ TateCohomology.δ (augSeq_shortExact S.X₁) (n + 1) =
      -(TateCohomology.δ (augSeq_shortExact S.X₃) n ≫ TateCohomology.δ hK (n + 1)) :=
    neg_eq_iff_eq_neg.1 A1.symm
  have h2 : TateCohomology.δ hK (n + 1) ≫ TateCohomology.δ (cyclicSeq_shortExact g hg S.X₁) (n + 1 + 1) =
      -(TateCohomology.δ (cyclicSeq_shortExact g hg S.X₃) (n + 1) ≫ TateCohomology.δ hS (n + 1 + 1)) :=
    neg_eq_iff_eq_neg.1 B1.symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun φ => φ ≫ TateCohomology.δ (cyclicSeq_shortExact g hg S.X₁) (n + 1 + 1)) h1).trans ?_
  refine (Preadditive.neg_comp _ _).trans ?_
  refine (congrArg Neg.neg (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun z => -(TateCohomology.δ (augSeq_shortExact S.X₃) n ≫ z)) h2).trans ?_
  refine (congrArg Neg.neg (Preadditive.comp_neg _ _)).trans ?_
  refine (neg_neg _).trans ?_
  exact (Category.assoc _ _ _).symm

end Diagrams

section CupSide

variable {G : Type} [Group G] [Fintype G]

/-- Cup product with a class `u ∈ Ĥ²(G, ℤ)` followed by `M ⊗ ℤ ≃ M`, as a map `Ĥʳ(G, M) → Ĥʳ⁺²(G, M)`. -/
noncomputable def Cu (u : tateCohomology (Rep.trivial ℤ G ℤ) 2) (M : Rep ℤ G) (r : ℤ)
    (x : tateCohomology M r) : tateCohomology M (r + 1 + 1) :=
  (tateCohomologyFunctor (r + 1 + 1)).map (ρ_ M).hom
    (TauCeti.TateCohomology.cup M (Rep.trivial ℤ G ℤ) r 2 (r + 1 + 1) (by ring) x u)

/-- `Cu` commutes with the connecting maps of sequences whose first map has a `ℤ`-linear retraction. -/
theorem Cu_δ (u : tateCohomology (Rep.trivial ℤ G ℤ) 2) {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact)
    {ret : S.X₂.V →ₗ[ℤ] S.X₁.V} (hr : Function.LeftInverse ret S.f.hom) (n : ℤ)
    (y : tateCohomology S.X₃ n) :
    Cu u S.X₁ (n + 1) (TateCohomology.δ hS n y) = TateCohomology.δ hS (n + 1 + 1) (Cu u S.X₃ n y) := by
  have hT : (S.map (tensorRight (Rep.trivial ℤ G ℤ))).ShortExact :=
    haveI := hS.epi_g
    Rep.shortExact_map_tensorRight_of_leftInverse hS.exact _ hr
  have h1 := TauCeti.TateCohomology.δ_cup_of_leftInverse hS hr (Rep.trivial ℤ G ℤ)
    (p := n) (q := 2) (n := n + 1 + 1) (by ring) y u
  let ψ : S.map (tensorRight (Rep.trivial ℤ G ℤ)) ⟶ S :=
    { τ₁ := (ρ_ S.X₁).hom
      τ₂ := (ρ_ S.X₂).hom
      τ₃ := (ρ_ S.X₃).hom
      comm₁₂ := by exact (rightUnitor_naturality S.f).symm
      comm₂₃ := by exact (rightUnitor_naturality S.g).symm }
  have h2 := ConcreteCategory.congr_hom (TateCohomology.δ_naturality hT hS ψ (n + 1 + 1))
    (TauCeti.TateCohomology.cup S.X₃ (Rep.trivial ℤ G ℤ) n 2 (n + 1 + 1) (by ring) y u)
  unfold Cu
  rw [← h1]
  exact h2

/-- Milne's periodicity map before the identification of the degree `r + 2`: the composite of the connecting
maps of `augSeq M` and `cyclicSeq g hg M`. -/
noncomputable def Pc (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) (r : ℤ) :
    tateCohomology M r ⟶ tateCohomology M (r + 1 + 1) :=
  TateCohomology.δ (augSeq_shortExact M) r ≫ TateCohomology.δ (cyclicSeq_shortExact g hg M) (r + 1)

theorem Pc_naturality (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) {M N : Rep ℤ G} (f : M ⟶ N) (r : ℤ) :
    Pc g hg M r ≫ (tateCohomologyFunctor (r + 1 + 1)).map f =
      (tateCohomologyFunctor r).map f ≫ Pc g hg N r := by
  have h1 := TateCohomology.δ_naturality (augSeq_shortExact M) (augSeq_shortExact N) (augMap f) r
  have h2 := TateCohomology.δ_naturality (cyclicSeq_shortExact g hg M) (cyclicSeq_shortExact g hg N)
    (cyclicMap g hg f) (r + 1)
  unfold Pc
  refine (congrArg (fun z => TateCohomology.δ (augSeq_shortExact M) r ≫ z) h2).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ TateCohomology.δ (cyclicSeq_shortExact g hg N) (r + 1)) h1).trans ?_
  exact Category.assoc _ _ _

theorem Pc_eq_Cu (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (u : tateCohomology (Rep.trivial ℤ G ℤ) 2)
    (hbase : ∀ (M : Rep ℤ G) (x : tateCohomology M 0), (Pc g hg M 0).hom x = Cu u M 0 x)
    (n : ℤ) (hn : 0 ≤ n) : ∀ (M : Rep ℤ G) (x : tateCohomology M n), (Pc g hg M n).hom x = Cu u M n x := by
  induction n, hn using Int.leInduction with
  | base => exact hbase
  | succ n hn ih =>
    intro M x
    have hJ : ∀ r : ℤ, IsZero (tateCohomology (seq15 M).X₂ r) := fun r =>
      prop_3_1 ⟨M, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩ r
    have := tate_isIso_δ (seq15_shortExact M) hJ n
    obtain ⟨y, rfl⟩ : ∃ y, (TateCohomology.δ (seq15_shortExact M) n).hom y = x :=
      ⟨(inv (TateCohomology.δ (seq15_shortExact M) n)).hom x, by
        exact ConcreteCategory.congr_hom (IsIso.inv_hom_id (TateCohomology.δ (seq15_shortExact M) n)) x⟩
    have key := congrArg (fun φ => φ.hom y)
      (periodicity_δ_comm g hg (seq15_shortExact M) (seq15_tensorLeft (leftRegular ℤ G) M) n)
    have hCu := Cu_δ u (seq15_shortExact M) (indRetraction_toIndG M) n y
    exact key.trans ((congrArg (TateCohomology.δ (seq15_shortExact M) (n + 1 + 1)).hom (ih (seq15 M).X₃ y)).trans hCu.symm)

end CupSide

section Base

open TauCeti.TateCohomology Rep.FiniteCyclicGroup groupCohomology

variable {G : Type} [CommGroup G] [Fintype G] (M : Rep ℤ G) (a : M.ρ.invariants)

/-- The element `[h] ⊗ a` of `ℤ[G] ⊗ M`. -/
noncomputable abbrev eps (h : G) : (leftRegular ℤ G ⊗ M : Rep ℤ G) :=
  rtmul (A := leftRegular ℤ G) (B := M) (MonoidAlgebra.single h (1 : ℤ)) a.1

set_option backward.isDefEq.respectTransparency false in
theorem rho_eps (h k : G) : (leftRegular ℤ G ⊗ M : Rep ℤ G).ρ h (eps M a k) = eps M a (h * k) := by
  have := a.2 h
  simp [eps, rtmul, Representation.tprod_apply, Representation.ofMulAction_single, this]

theorem exists_t (g : G) : ∃ t : LinearMap.ker ((augSeq M).X₁.norm.asHom.hom.toLinearMap),
    (augSeq M).f.hom t.1 = eps M a g - eps M a 1 := by
  have hex := functionExact_of_shortExact (augSeq_shortExact M)
  have h0 : (augSeq M).g.hom (eps M a g - eps M a 1) = 0 := by
    change (augTensor M).hom (eps M a g - eps M a 1) = 0
    rw [map_sub]
    change (augTensor M).hom (rtmul (A := leftRegular ℤ G) (B := M) (MonoidAlgebra.single g (1 : ℤ)) a.1) -
      (augTensor M).hom (rtmul (A := leftRegular ℤ G) (B := M) (MonoidAlgebra.single 1 (1 : ℤ)) a.1) = 0
    rw [augTensor_apply, augTensor_apply, sub_self]
  obtain ⟨k, hk⟩ := (hex _).1 h0
  have hinj : Function.Injective (augSeq M).f.hom := (Rep.mono_iff_injective _).1 (augSeq_shortExact M).mono_f
  refine ⟨⟨k, ?_⟩, hk⟩
  change (Rep.norm (augSeq M).X₁).asHom.hom k = 0
  apply hinj
  rw [map_zero]
  change (augSeq M).f.hom ((augSeq M).X₁.ρ.norm k) = 0
  simp only [Representation.norm, LinearMap.sum_apply, map_sum, hom_comm_apply]
  have hrho : ∀ h : G, ((augSeq M).X₂.ρ h) ((augSeq M).f.hom k) = eps M a (h * g) - eps M a (h * 1) :=
    fun h => by rw [hk]; erw [map_sub, rho_eps, rho_eps]; rfl
  refine (Finset.sum_congr rfl (fun h _ => hrho h)).trans ?_
  refine (Finset.sum_sub_distrib _ _).trans ?_
  refine sub_eq_zero.2 ?_
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => by simp; rfl)

open TauCeti (pow_cyclicLog) in
theorem δ_aug_H0 (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (t : LinearMap.ker ((augSeq M).X₁.norm.asHom.hom.toLinearMap))
    (ht : (augSeq M).f.hom t.1 = eps M a g - eps M a 1) :
    groupCohomology.δ (augSeq_shortExact M) 0 1 rfl ((H0Iso M).inv a) =
      groupCohomologyπOdd (augSeq M).X₁ g hg 1 odd_one t := by
  rw [groupCohomologyπOdd_one_apply]
  refine (δ₀_apply (augSeq_shortExact M) a (eps M a 1)
    (augTensor_apply M 1 a.1) _ ?_).trans rfl
  funext h
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, g ^ i = h := ⟨_, pow_cyclicLog g hg h⟩
  change (augSeq M).f.hom ((partialNormCocycle (augSeq M).X₁ g hg t : G → (augSeq M).X₁) (g ^ i)) = _
  rw [partialNormCocycle_apply_pow, map_sum]
  have h1 : ∀ l : ℕ, (augSeq M).f.hom ((augSeq M).X₁.ρ (g ^ l) t.1) = eps M a (g ^ (l + 1)) - eps M a (g ^ l) := by
    intro l
    rw [hom_comm_apply, ht]
    erw [map_sub, rho_eps, rho_eps]
    rw [pow_succ, mul_one]
    rfl
  rw [Finset.sum_congr rfl (fun l _ => h1 l)]
  erw [d₀₁_hom_apply]
  refine (Finset.sum_range_sub (fun l => eps M a (g ^ l)) i).trans ?_
  erw [rho_eps]
  simp
  rfl

theorem δ_cyc_odd (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (t : LinearMap.ker ((augSeq M).X₁.norm.asHom.hom.toLinearMap))
    (ht : (augSeq M).f.hom t.1 = eps M a g - eps M a 1)
    (x : LinearMap.ker (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap) (hx : x.1 = a.1) :
    groupCohomology.δ (cyclicSeq_shortExact g hg M) 1 2 rfl
        (groupCohomologyπOdd (augSeq M).X₁ g hg 1 odd_one t) =
      groupCohomologyπEven M g hg 2 even_two x := by
  have hinj : Function.Injective (kernel.ι (augTensor M)).hom :=
    (Rep.mono_iff_injective _).1 (augSeq_shortExact M).mono_f
  refine δ_groupCohomologyπOdd_one g hg (cyclicSeq_shortExact g hg M) t (eps M a 1) ?_ x ?_
  · apply hinj
    change (kernel.ι (augTensor M)).hom ((subOneTensor g hg M).hom
      (rtmul (A := leftRegular ℤ G) (B := M) (MonoidAlgebra.single 1 (1 : ℤ)) a.1)) = _
    rw [subOneTensor_apply]
    have := ht
    change (kernel.ι (augTensor M)).hom t.1 = _ at this
    rw [this, mul_one]
  · change (normTensor M).hom x.1 = _
    rw [normTensor_apply, hx]
    refine Eq.trans ?_ (LinearMap.sum_apply Finset.univ (fun h : G => ((cyclicSeq g hg M).X₂.ρ h)) (eps M a 1)).symm
    refine Finset.sum_congr rfl fun h _ => ?_
    erw [rho_eps, mul_one]

theorem Pc_H0π (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (x : LinearMap.ker (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap) (hx : x.1 = a.1) :
    (Pc g hg M 0).hom (H0π M a) =
      (_root_.TateCohomology.isoGroupCohomology 2).inv.app M (groupCohomologyπEven M g hg 2 even_two x) := by
  obtain ⟨t, ht⟩ := exists_t M a g
  have e0 : H0π M a = (Rep.fromGroupCohomology M 0).hom ((H0Iso M).inv a) := by
    rw [Rep.fromGroupCohomology_zero]
    simp
  have hA : (Rep.fromGroupCohomology (augSeq M).X₁ 1).hom
      (groupCohomology.δ (augSeq_shortExact M) 0 1 rfl ((H0Iso M).inv a)) =
      (TateCohomology.δ (augSeq_shortExact M) 0).hom ((Rep.fromGroupCohomology M 0).hom ((H0Iso M).inv a)) :=
    ConcreteCategory.congr_hom (δ_comp_fromGroupCohomology (augSeq_shortExact M) 0) _
  have hB : (Rep.fromGroupCohomology M 2).hom
      (groupCohomology.δ (cyclicSeq_shortExact g hg M) 1 2 rfl
        (groupCohomologyπOdd (augSeq M).X₁ g hg 1 odd_one t)) =
      (TateCohomology.δ (cyclicSeq_shortExact g hg M) 1).hom
        ((Rep.fromGroupCohomology (augSeq M).X₁ 1).hom (groupCohomologyπOdd (augSeq M).X₁ g hg 1 odd_one t)) :=
    ConcreteCategory.congr_hom (δ_comp_fromGroupCohomology (cyclicSeq_shortExact g hg M) 1) _
  rw [δ_aug_H0 M a g hg t ht] at hA
  rw [δ_cyc_odd M a g hg t ht x hx] at hB
  rw [e0]
  change (TateCohomology.δ (cyclicSeq_shortExact g hg M) (0 + 1)).hom
    ((TateCohomology.δ (augSeq_shortExact M) 0).hom ((Rep.fromGroupCohomology M 0).hom ((H0Iso M).inv a))) = _
  rw [← hA]
  refine hB.symm.trans ?_
  change (Rep.fromGroupCohomology M (1 + 1)).hom _ = _
  rw [Rep.fromGroupCohomology_succ]
  rfl

end Base

section Gamma

open TauCeti.ContCohomology Rep.FiniteCyclicGroup groupCohomology

/-- $\mathbb Q/\mathbb Z$ as `AddCircle (1 : ℚ)` is `QZ`. -/
noncomputable def circQZ : AddCircle (1 : ℚ) ≃+ QZ :=
  QuotientAddGroup.quotientAddEquivOfEq (by
    ext q
    simp only [AddSubgroup.mem_zmultiples_iff, AddMonoidHom.mem_range, Int.coe_castAddHom, zsmul_one])

/-- The representative in $[0, 1)$ of a class of $\mathbb Q/\mathbb Z$. -/
noncomputable def qzLift35 (q : QZ) : ℚ := (AddCircle.equivIco 1 0 (circQZ.symm q) : ℚ)

theorem mk_qzLift35 (q : QZ) : (QuotientAddGroup.mk (qzLift35 q) : QZ) = q := by
  have h : ((qzLift35 q : ℚ) : AddCircle (1 : ℚ)) = circQZ.symm q := AddCircle.coe_equivIco
  have : circQZ ((qzLift35 q : ℚ) : AddCircle (1 : ℚ)) = QuotientAddGroup.mk (qzLift35 q) := rfl
  rw [← this, h, AddEquiv.apply_symm_apply]

variable {G : Type} [Group G]

/-- A character $G \to \mathbb Q/\mathbb Z$ as a character with values in `AddCircle (1 : ℚ)`. -/
noncomputable def toCircle35 (χ : Additive G →+ QZ) : Additive G →+ AddCircle (1 : ℚ) :=
  circQZ.symm.toAddMonoidHom.comp χ

theorem intCast_characterCarry_toCircle35 (χ : Additive G →+ QZ) (g h : G) :
    (characterCarry (toCircle35 χ) g h : ℚ) =
      qzLift35 (χ (.ofMul h)) - qzLift35 (χ (.ofMul (g * h))) + qzLift35 (χ (.ofMul g)) := by
  rw [intCast_characterCarry]
  simp only [toCircle35, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, qzLift35]
  ring

/-- The carry cocycle $(g, h) \mapsto \tilde\chi(g) + \tilde\chi(h) - \tilde\chi(gh) \in \mathbb Z$. -/
noncomputable def carryZ35 (χ : Additive G →+ QZ) : cocycles₂ (seqZQ G).X₁ :=
  ⟨(fun p => characterCarry (toCircle35 χ) p.1 p.2 : G × G → (seqZQ G).X₁),
    (mem_cocycles₂_iff (A := (seqZQ G).X₁) _).2 fun g h j =>
      characterCarry_mul_add (toCircle35 χ) g h j⟩

/-- **$\delta\chi$ is the carry cocycle** of the representatives of $\chi$ in $[0, 1)$. -/
theorem delta_char35 (χ : Additive G →+ QZ) :
    (groupCohomology.δ (seqZQ_shortExact G) 1 2 rfl).hom ((H1IsoOfIsTrivial (trivial ℤ G QZ)).inv.hom χ) =
      H2π _ (carryZ35 χ) := by
  erw [H1IsoOfIsTrivial_inv_apply]
  refine (δ₁_apply (seqZQ_shortExact G) _ (fun g => qzLift35 (χ (.ofMul g))) ?_ (carryZ35 χ) ?_).trans rfl
  · funext g
    exact mk_qzLift35 _
  · funext p
    change ((characterCarry (toCircle35 χ) p.1 p.2 : ℤ) : ℚ) = qzLift35 (χ (.ofMul p.2)) -
      qzLift35 (χ (.ofMul (p.1 * p.2))) + qzLift35 (χ (.ofMul p.1))
    exact intCast_characterCarry_toCircle35 χ p.1 p.2

end Gamma

section Gamma2

open TauCeti.ContCohomology Rep.FiniteCyclicGroup groupCohomology

variable {G : Type} [CommGroup G] [Fintype G]

theorem toCircle35_pow {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (f : Additive G →+ QZ)
    (hf : f (Additive.ofMul g) = QuotientAddGroup.mk ((1 : ℚ) / Fintype.card G)) (i : ℕ) :
    toCircle35 f (Additive.ofMul (g ^ i)) = ((i / orderOf g : ℚ) : AddCircle (1 : ℚ)) := by
  have hcard : (Fintype.card G : ℚ) = orderOf g := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have h1 : toCircle35 f (Additive.ofMul g) = (((1 : ℚ) / orderOf g : ℚ) : AddCircle (1 : ℚ)) := by
    change circQZ.symm (f (Additive.ofMul g)) = _
    rw [hf, ← hcard]
    rfl
  rw [ofMul_pow, map_nsmul, h1, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  ring

theorem γ_eq {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (f : Additive G →+ QZ)
    (hf : f (Additive.ofMul g) = QuotientAddGroup.mk ((1 : ℚ) / Fintype.card G))
    (x : LinearMap.ker (Rep.applyAsHom (Rep.trivial ℤ G ℤ) g - 𝟙 _).hom.toLinearMap) (hx : x.1 = (1 : ℤ)) :
    (groupCohomology.δ (seqZQ_shortExact G) 1 2 rfl).hom
        ((H1IsoOfIsTrivial (trivial ℤ G QZ)).inv.hom f) =
      groupCohomologyπEven (Rep.trivial ℤ G ℤ) g hg 2 even_two x := by
  classical
  rw [delta_char35, groupCohomologyπEven_two_apply]
  congr 1
  refine Subtype.ext (funext fun p => ?_)
  obtain ⟨y, z⟩ := p
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 (hg y))
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 (hg z))
  rw [Finset.mem_range] at hi hj
  refine Eq.trans ?_ (carryCocycle_apply_pow (Rep.trivial ℤ G ℤ) g hg x hi hj).symm
  rw [hx]
  change ((characterCarry (toCircle35 f) (g ^ i) (g ^ j) : ℤ)) = _
  rw [characterCarry_eq_ite (toCircle35 f) hi hj (toCircle35_pow hg f hf i) (toCircle35_pow hg f hf j)]

open TauCeti.TateCohomology in
/-- Cup product of the degree-zero class of an invariant `a` with the periodicity class of `1`. -/
theorem Cu_H0π (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (x₁ : LinearMap.ker (Rep.applyAsHom (Rep.trivial ℤ G ℤ) g - 𝟙 _).hom.toLinearMap)
    (hx₁ : x₁.1 = (1 : ℤ)) (A : Rep ℤ G) (a : A.ρ.invariants)
    (x : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) (hx : x.1 = a) :
    Cu ((_root_.TateCohomology.isoGroupCohomology 2).inv.app (Rep.trivial ℤ G ℤ)
        (groupCohomologyπEven (Rep.trivial ℤ G ℤ) g hg 2 even_two x₁)) A 0 (H0π A a) =
      (_root_.TateCohomology.isoGroupCohomology 2).inv.app A
        (groupCohomologyπEven A g hg 2 even_two x) := by
  change (tateCohomologyFunctor 2).map (ρ_ A).hom
      (cup A (Rep.trivial ℤ G ℤ) 0 2 2 (zero_add 2) (H0π A a) _) = _
  rw [TauCeti.TateCohomology.cup_zero_left, TauCeti.TateCohomology.cup0H_H0π, ← ModuleCat.comp_apply, ← Functor.map_comp, Category.assoc]
  set φ : Rep.trivial ℤ G ℤ ⟶ A :=
    (Rep.trivial ℤ G ℤ).tensorInvariant a ≫ (β_ (Rep.trivial ℤ G ℤ) A).hom ≫ (ρ_ A).hom with _
  have h := ConcreteCategory.congr_hom
    ((_root_.TateCohomology.isoGroupCohomology 2).inv.naturality φ)
    (groupCohomologyπEven (Rep.trivial ℤ G ℤ) g hg 2 even_two x₁)
  have hmap : groupCohomology.map (MonoidHom.id G) φ 2
      (groupCohomologyπEven (Rep.trivial ℤ G ℤ) g hg 2 even_two x₁) =
      groupCohomologyπEven A g hg 2 even_two x := by
    refine map_groupCohomologyπEven_two (B := Rep.trivial ℤ G ℤ) A g hg (MonoidHom.id G) hg 1
      (pow_one g).symm φ 1 rfl x₁ x ?_
    rw [one_smul, hx, hx₁]
    exact ((TauCeti.Rep.tensorInvariant_braiding_rightUnitor_hom_apply a 1).trans
      (A.hV2.one_smul _)).symm
  refine h.symm.trans ?_
  rw [← hmap]
  rfl

/-- **Periodicity is cup product with the periodicity class of `1`, in Tate cohomology** (degrees `n ≥ 0`). -/
theorem Pc_eq_Cu_periodicityClass (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (x₁ : LinearMap.ker (Rep.applyAsHom (Rep.trivial ℤ G ℤ) g - 𝟙 _).hom.toLinearMap)
    (hx₁ : x₁.1 = (1 : ℤ)) (n : ℤ) (hn : 0 ≤ n) (M : Rep ℤ G) (y : tateCohomology M n) :
    (Pc g hg M n).hom y =
      Cu ((_root_.TateCohomology.isoGroupCohomology 2).inv.app (Rep.trivial ℤ G ℤ)
        (groupCohomologyπEven (Rep.trivial ℤ G ℤ) g hg 2 even_two x₁)) M n y := by
  refine Pc_eq_Cu g hg _ ?_ n hn M y
  intro M' y0
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (TauCeti.TateCohomology.H0π M')).1 inferInstance y0
  exact (Pc_H0π M' a g hg ⟨a.1, LinearMap.mem_ker.2 (sub_eq_zero.2 (a.2 g))⟩ rfl).trans
    (Cu_H0π g hg x₁ hx₁ M' a ⟨a.1, LinearMap.mem_ker.2 (sub_eq_zero.2 (a.2 g))⟩ rfl).symm

end Gamma2

section Final

variable {G : Type} [Group G] [Fintype G]

theorem fromGC_tateIsoOfEq (M : Rep ℤ G) (k : ℕ) [NeZero k] (y : tateCohomology M k) :
    (Rep.fromGroupCohomology M k).hom ((tateIsoOfEq M k k rfl).hom y) = y := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := NeZero.ne k; omega⟩
  rw [Rep.fromGroupCohomology_succ]
  exact ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (k' + 1)).app M).hom_inv_id_apply y

theorem tateIsoOfEq_fromGC (M : Rep ℤ G) (k : ℕ) [NeZero k] (z : groupCohomology M k) :
    (tateIsoOfEq M k k rfl).hom ((Rep.fromGroupCohomology M k).hom z) = z := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := NeZero.ne k; omega⟩
  rw [Rep.fromGroupCohomology_succ]
  exact ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (k' + 1)).app M).inv_hom_id_apply z

end Final

open Rep.FiniteCyclicGroup groupCohomology in
/-- **Remark 3.5, proved** (Milne, *CFT*, II, Remark 3.5, p. 81): for $G$ cyclic with generator $\sigma$,
the periodicity isomorphism of Proposition 3.4 is $x \mapsto x \cup \gamma$, $\gamma = \delta f$,
$f(\sigma) = 1/|G|$, for every cup-product family and $r \ge 1$. Proof: both sides commute with the
connecting maps of the sequence (15) (3 × 3 diagrams of the augmentation and norm sequences for the
periodicity, `Cu_δ` for the cup product), so by dimension shifting it suffices to check degree $0$, where
both are the class of the carry cocycle (`Pc_H0π`, `Cu_H0π`, `γ_eq`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 3.5, p. 81"]
theorem remark3_5 : Remark3_5 := by
  refine ⟨fun G _ _ σ hσ f hf c M r _ x => ?_⟩
  haveI : IsCyclic G := ⟨⟨σ, hσ⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by have := NeZero.ne r; omega⟩
  let x₁ : LinearMap.ker (Rep.applyAsHom (Rep.trivial ℤ G ℤ) σ - 𝟙 _).hom.toLinearMap :=
    ⟨(1 : ℤ), LinearMap.mem_ker.2 (sub_self (1 : ℤ))⟩
  have hP := Pc_eq_Cu_periodicityClass σ hσ x₁ rfl ((n + 1 : ℕ) : ℤ) (by positivity) M x
  have hγ := γ_eq hσ f hf x₁ rfl
  have hu : (Rep.fromGroupCohomology (Rep.trivial ℤ G ℤ) 2).hom
      ((groupCohomology.δ (seqZQ_shortExact G) 1 2 rfl).hom ((H1IsoOfIsTrivial (trivial ℤ G QZ)).inv.hom f)) =
      (_root_.TateCohomology.isoGroupCohomology 2).inv.app (Rep.trivial ℤ G ℤ)
        (groupCohomologyπEven (Rep.trivial ℤ G ℤ) σ hσ 2 even_two x₁) := by
    rw [hγ]
    change (Rep.fromGroupCohomology (Rep.trivial ℤ G ℤ) (1 + 1)).hom _ = _
    rw [Rep.fromGroupCohomology_succ]
    rfl
  have h1 := fromGroupCohomology_cup c (Rep.trivial ℤ G ℤ)
    ((groupCohomology.δ (seqZQ_shortExact G) 1 2 rfl).hom ((H1IsoOfIsTrivial (trivial ℤ G QZ)).inv.hom f))
    (n + 1) M ((tateIsoOfEq M ((n + 1 : ℕ) : ℤ) (n + 1) rfl).hom x)
  rw [fromGC_tateIsoOfEq, hu] at h1
  have h2 := fromGroupCohomology_succ_natural (ρ_ M).hom (n + 2)
    (c.cup M (trivial ℤ G ℤ) (n + 1) 2 (n + 1 + 2) rfl ((tateIsoOfEq M ((n + 1 : ℕ) : ℤ) (n + 1) rfl).hom x)
      ((groupCohomology.δ (seqZQ_shortExact G) 1 2 rfl).hom
        ((H1IsoOfIsTrivial (trivial ℤ G QZ)).inv.hom f)))
  have key : (periodicity σ hσ M ((n + 1 : ℕ) : ℤ)).hom x = (Rep.fromGroupCohomology M (n + 1 + 2)).hom
      ((functor ℤ G (n + 1 + 2)).map (ρ_ M).hom
        (c.cup M (trivial ℤ G ℤ) (n + 1) 2 (n + 1 + 2) rfl ((tateIsoOfEq M ((n + 1 : ℕ) : ℤ) (n + 1) rfl).hom x)
          ((groupCohomology.δ (seqZQ_shortExact G) 1 2 rfl).hom
            ((H1IsoOfIsTrivial (trivial ℤ G QZ)).inv.hom f)))) := by
    refine Eq.trans ?_ h2.symm
    exact hP.trans (congrArg (fun w => (tateCohomologyFunctor (((n + 2 + 1 : ℕ)) : ℤ)).map (ρ_ M).hom w) h1.symm)
  exact (congrArg (tateIsoOfEq M _ (n + 1 + 2) _).hom key).trans (tateIsoOfEq_fromGC M (n + 1 + 2) _)

end NumberFieldKB.MilneCFT
