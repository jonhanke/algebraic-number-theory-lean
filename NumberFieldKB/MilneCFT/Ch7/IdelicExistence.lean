import NumberFieldKB.MilneCFT.Ch5IdelicMain
import NumberFieldKB.MilneCFT.Ch5Complements
import NumberFieldKB.MilneCFT.Ch7.Existence

/-!
# Chapter V's existence theorem (Theorem 5.5) from Chapter VII's (Theorem 9.5)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Theorem 5.5 (p. 179) and Chapter VII, Theorem 9.5 (p. 226).

Chapter VII proves that every open subgroup of finite index of $C_K$ is a norm group (`Ch7.Theorem9_5`). Chapter V's
statement (`IdelicExistence`) adds that the class field is unique up to isomorphism. Uniqueness follows from the
reciprocity law (`IdelicReciprocity`): for $v$ unramified in $L$, $\mathrm{Frob}_v = \phi_{L/K}(\pi_v)$, which is
trivial iff the class of $\pi_v$ lies in $\mathrm{Nm}(C_L)$; so two abelian extensions with the same norm group have
the same split primes outside a finite set and embed in each other (`nonempty_algHom_of_artinFrob`, Chebotarev).
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-- The preimage of $\mathrm{Nm}(C_L)$ in $\mathbb I_K$ is $K^\times\cdot\mathrm{Nm}(\mathbb I_L)$. -/
theorem comap_normGroupC (L : Type) [Field L] [NumberField L] [Algebra K L] :
    (normGroupC K L).comap (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) = ideleNormGroup L := by
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    have hc' : (((ideleNormMap K L y : IdeleGroup (𝓞 K) K)) : IdeleClassGroup (𝓞 K) K) =
        QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) x := hc
    have hmem : (ideleNormMap K L y)⁻¹ * x ∈ IdeleGroup.principalSubgroup (𝓞 K) K :=
      QuotientGroup.eq.mp hc'
    rw [ideleNormGroup]
    refine Subgroup.mem_sup.mpr ⟨_, hmem, ideleNormMap K L y, ⟨y, rfl⟩, ?_⟩
    simp
  · intro hx
    obtain ⟨a, ha, n, ⟨y, rfl⟩, rfl⟩ := Subgroup.mem_sup.mp hx
    refine ⟨(y : IdeleClassGroup (𝓞 L) L), ?_⟩
    refine (Ideles.ideleClassRelNorm_mk _ y).trans ?_
    show _ = QuotientGroup.mk (a * _)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).mpr ha]
    exact (one_mul (M := IdeleClassGroup (𝓞 K) K) _).symm

/-- For $L/K$ abelian and $v$ unramified in $L$: $\mathrm{Frob}_v = 1$ iff the class of a uniformizer at $v$ lies in
$\mathrm{Nm}(C_L)$ (the reciprocity law). -/
theorem artinFrob_eq_one_iff (hR : IdelicReciprocity K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ unramifiedPrimes K L)
    (π : (v.adicCompletion K)ˣ) (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1)) :
    artinFrob L v = 1 ↔ IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π ∈ normGroupC K L := by
  obtain ⟨hφ, -, -, hker⟩ := idelicArtinOf_spec hR L
  have h1 := hφ.frobenius v hv π hπ
  have h2 : artinFrob L v = 1 ↔ IdeleGroup.ofAdicCompletion (𝓞 K) K v π ∈ ideleNormGroup L := by
    rw [← hker, MonoidHom.mem_ker, h1]
  rw [h2, ← comap_normGroupC L, Subgroup.mem_comap]
  rfl

/-- **Uniqueness in the existence theorem** (Milne, *CFT*, Chapter V, Theorem 5.5, from the reciprocity law): two
finite abelian extensions with the same norm group are $K$-isomorphic. -/
@[kb "milne2020cft" "Ch. V, Thm. 5.5 (uniqueness, from Thm. 5.3)"]
theorem nonempty_algEquiv_of_normGroupC_eq (hR : IdelicReciprocity K) (L L' : Type) [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] [Field L'] [NumberField L'] [Algebra K L'] [IsAbelianGalois K L']
    (h : normGroupC K L = normGroupC K L') : Nonempty (L ≃ₐ[K] L') := by
  classical
  set S : Set (HeightOneSpectrum (𝓞 K)) := (unramifiedPrimes K L)ᶜ ∪ (unramifiedPrimes K L')ᶜ with hS
  have hSf : S.Finite := (finite_compl_unramifiedPrimes K L).union (finite_compl_unramifiedPrimes K L')
  have hSL : ∀ v, v ∉ S → v ∈ unramifiedPrimes K L := fun v hv => by
    by_contra h; exact hv (Or.inl h)
  have hSL' : ∀ v, v ∉ S → v ∈ unramifiedPrimes K L' := fun v hv => by
    by_contra h; exact hv (Or.inr h)
  have key : ∀ v, v ∉ S → (artinFrob L v = 1 ↔ artinFrob L' v = 1) := by
    intro v hv
    obtain ⟨π, hπ⟩ := exists_unit_uniformizer (K := K) v
    rw [artinFrob_eq_one_iff hR L v (hSL v hv) π hπ, artinFrob_eq_one_iff hR L' v (hSL' v hv) π hπ, h]
  obtain ⟨f⟩ := nonempty_algHom_of_artinFrob L L' S hSf hSL hSL' (fun v hv => (key v hv).2)
  obtain ⟨g⟩ := nonempty_algHom_of_artinFrob L' L S hSf hSL' hSL (fun v hv => (key v hv).1)
  have hle : Module.finrank K L ≤ Module.finrank K L' :=
    LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.injective
  have hge : Module.finrank K L' ≤ Module.finrank K L :=
    LinearMap.finrank_le_finrank_of_injective (f := g.toLinearMap) g.injective
  have heq : Module.finrank K L = Module.finrank K L' := le_antisymm hle hge
  have hbij : Function.Bijective f :=
    ⟨f.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) heq).mp f.injective⟩
  exact ⟨AlgEquiv.ofBijective f hbij⟩

/-- **Theorem 5.5 of Chapter V from Theorem 9.5 of Chapter VII** (Milne, *CFT*): conditional on the reciprocity law
(Chapter V, Theorem 5.3) and Chapter VII's existence theorem. -/
@[kb "milne2020cft" "Ch. V, Thm. 5.5 (from Ch. VII, Thm. 9.5 and Thm. 5.3)"]
theorem idelicExistence_of_theorem9_5 (hR : IdelicReciprocity K) (h95 : Ch7.Theorem9_5 K) :
    IdelicExistence K := by
  refine ⟨fun N hopen hfin => ?_, fun L L' _ _ _ _ _ _ _ _ h => nonempty_algEquiv_of_normGroupC_eq hR L L' h⟩
  obtain ⟨L, _, _, _, hG, hc, hN⟩ := h95.isNormGroup N hopen hfin
  have : IsGalois K L := hG
  have : IsMulCommutative Gal(L/K) := ⟨⟨fun a b => hc a b⟩⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, ⟨⟩, hN.symm⟩

/-! ## Chapter VII's reciprocity law from Chapter V's -/

/-- For $L/K$ abelian and an intermediate field $M$ normal over $K$, restriction to $M$ of the idelic Artin map of
$L$ is the idelic Artin map of $M$ (uniqueness in Summary 5.10, as in Proposition 5.2). -/
theorem restrict_idelicArtinOf (hR : IdelicReciprocity K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (M : IntermediateField K L) [NumberField M] [IsAbelianGalois K M] :
    (AlgEquiv.restrictNormalHom M).comp (idelicArtinOf hR L) = idelicArtinOf hR M := by
  have : IsScalarTower K M L := inferInstance
  have : IsGalois K L := inferInstance
  obtain ⟨hL, hLK, -, -⟩ := idelicArtinOf_spec hR L
  obtain ⟨hM, hMK, -, -⟩ := idelicArtinOf_spec hR M
  obtain ⟨nL, hnL⟩ := hL.local_ramified
  obtain ⟨nM, hnM⟩ := hM.local_ramified
  have hram : ∀ w : InfinitePlace K, InfinitePlace.RamifiesIn M w → InfinitePlace.RamifiesIn L w := by
    intro w h
    have : Algebra.IsAlgebraic M L := Algebra.IsAlgebraic.tower_top (K := K) M
    obtain ⟨wM, hwM, hc⟩ := h.2
    obtain ⟨wL, hwL⟩ := InfinitePlace.comap_surjective (k := M) (K := L) wM
    have hwL' : wL.comap (algebraMap M L) = wM := hwL
    refine ⟨h.1, wL, ?_, InfinitePlace.IsComplex.of_comap (algebraMap M L) (hwL' ▸ hc)⟩
    rw [IsScalarTower.algebraMap_eq K M L, InfinitePlace.comap_comp, hwL', hwM]
  refine ideleHom_eq_of_local _ _ (unramifiedPrimes K L)ᶜ (finite_compl_unramifiedPrimes K L)
    (InfinitePlace.RamifiesIn L) (fun w hw => hw.1) (max (max nL nM) 1)
    (fun a => by rw [MonoidHom.comp_apply, hLK, map_one, hMK]) ?_ ?_
  · intro u h1 h2 h3
    have hL1 : idelicArtinOf hR L u = 1 := hnL u (fun v hv => h1 v (not_not.mpr hv))
      (fun v hv => (h2 v hv).trans (WithZero.exp_le_exp.mpr (by omega))) (fun w hw hr => h3 w hr)
    have hM1 : idelicArtinOf hR M u = 1 := by
      refine hnM u (fun v hv => ?_) (fun v hv => ?_) (fun w hw hr => h3 w (hram w hr))
      · by_cases hvL : v ∈ unramifiedPrimes K L
        · exact h1 v (not_not.mpr hvL)
        · exact valued_eq_one_of_sub_le_exp (h2 v hvL) (by omega)
      · have hvL : v ∉ unramifiedPrimes K L := fun h => hv (unramifiedPrimes_subset_of_tower K M L h)
        exact (h2 v hvL).trans (WithZero.exp_le_exp.mpr (by omega))
    rw [MonoidHom.comp_apply, hL1, map_one, hM1]
  · intro v hv π hπ
    have hvL : v ∈ unramifiedPrimes K L := not_not.mp hv
    rw [MonoidHom.comp_apply, hL.frobenius v hvL π hπ, ← artinFrob_restrict M L v hvL,
      hM.frobenius v (unramifiedPrimes_subset_of_tower K M L hvL) π hπ]

/-- **Chapter VII's form of the reciprocity law from Chapter V's** (Milne, *CFT*, Chapter V, Theorem 5.3 and
Proposition 5.2): the class-group Artin map of $L/K$ is onto with kernel $\mathrm{Nm}(C_L)$, and its restriction to an
intermediate field $M$ has kernel $\mathrm{Nm}(C_M)$. -/
@[kb "milne2020cft" "Ch. V, Thm. 5.3 and Prop. 5.2 ⇒ Ch. VII form of the reciprocity law"]
theorem reciprocityLaw_of_idelic (hR : IdelicReciprocity K) : Ch7.ReciprocityLaw K := by
  refine ⟨fun L _ _ _ hG hc => ?_⟩
  have : IsMulCommutative Gal(L/K) := ⟨⟨fun a b => hc a b⟩⟩
  have : IsAbelianGalois K L := ⟨⟩
  refine ⟨classArtinOf hR L, classArtinOf_surjective hR L, ker_classArtinOf hR L, fun M hMn => ?_⟩
  have : NumberField M :=
    { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans K M }
  have : IsGalois K M := ⟨⟩
  have : IsMulCommutative Gal(M/K) := ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L a
    obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L b
    rw [← map_mul, ← map_mul, hc a b]⟩⟩
  have : IsAbelianGalois K M := ⟨⟩
  have hker := ker_classArtinOf hR M
  have key : (AlgEquiv.restrictNormalHom M).comp (classArtinOf hR L) = classArtinOf hR M := by
    refine MonoidHom.ext fun c => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    simp only [MonoidHom.comp_apply, classArtinOf_mk]
    exact DFunLike.congr_fun (restrict_idelicArtinOf hR L M) x
  rw [key, hker]
  rfl

end NumberFieldKB.MilneCFT
