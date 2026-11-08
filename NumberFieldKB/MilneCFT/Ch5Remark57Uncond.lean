import NumberFieldKB.MilneCFT.GlobalUnconditional
import NumberFieldKB.MilneCFT.Ch5IdelicReciprocityTauCeti
import NumberFieldKB.MilneCFT.Ch7.ExistenceTauCeti
import NumberFieldKB.MilneCFT.Ch5IdelesChar
import NumberFieldKB.Ideles.Compact
import NumberFieldKB.WeilBNT.NormSplitting

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 5.7(a), proved from Tau Ceti

The named statement `NumberFieldKB.MilneCFT.Remark5_7` (Milne, V, Remark 5.7(a), p. 179) is proved unconditionally
(`remark5_7`). Write $\tau_L$ for Tau Ceti's idèlic Artin map `idelicArtinTauCeti L` and $S = K^\times\cdot I_\infty^+$
(`principalSubgroup ⊔ idelesInfPos`). Every family $\varphi_L$ in the statement satisfies the properties (a), (b) of
Summary 5.10 and is trivial on $K^\times$, so $\varphi_L = \tau_L$ (`R57.eq_tc`, from `idelicArtin_unique`).

* **`surjective`** (`R57.surjective_aux`). For a compatible family $\sigma$ let $F_L \subseteq C_K^1$ be the set of
  norm-one idèle classes $c$ with $\psi_L(c) = \sigma_L$ ($\psi_L$ the class-level Artin map). It is closed (a coset
  of an open kernel, `isClosed_fibre`), nonempty (the Artin map is onto and kills $I_\infty^+$, which contains Weil's
  idèles $Z(\lambda)$ of every norm, `exists_normOne`), and the family is directed: $F_{L\sqcup M}\subseteq F_L\cap F_M$
  by compatibility of Tau Ceti's maps with restriction (`tc_compat'`; the compositum is `Idx.sup`). Compactness of
  $C_K^1$ (`IdeleClassGroup.isCompact_normOne`) and Cantor's intersection theorem give a class in all $F_L$; lift it.
* **`connectedComponent`** (`R57.image_closure_eq_cc`). The image of $\overline S$ lies in the identity component:
  $I_\infty^+$ lies in the identity component of the idèle group (`idelesInfPos_le_cc`: each local factor is the image
  of a connected set under the exponential), the quotient map is continuous and the component is closed. Conversely,
  the identity component of $C_K$ lies in every clopen subgroup, in particular in the open subgroups of finite index
  $N_m$ = image of $W_{\mathfrak m}$ (`isOpen_Nm`, `finiteIndex_Nm`, the latter from the finiteness of the ray class
  group via Proposition 4.6), and an idèle class in all $N_m$ has its idèles in $\overline S$
  (`mem_closure_of_forall_Nm`: $W_{\mathfrak m}\subseteq I_\infty^+\cdot U$ for small $\mathfrak m$, from
  `idele_nhds_one` and `exists_modulus`).
* **`ker_eq`**. ($\Leftarrow$) is `remark_5_7_le_ker`. ($\Rightarrow$) (`mem_closure_of_forall_ker`) by
  `mem_closure_of_forall_Nm` it suffices to put the class of $x$ in each $N_m$. By the existence theorem
  (`Ch7.theorem9_5`) $N_m = \mathrm{Nm}(C_L)$ for an abstract finite abelian $L/K$; embed $L$ in $\Omega$ (algebraically
  closed) with image $L'$; norm groups of $K$-isomorphic fields agree
  (`range_ideleClassNormMap_eq_of_algEquiv`), and $\varphi_{L'}(x) = 1$ means the class of $x$ lies in
  $\ker\psi_{L'} = \mathrm{Nm}(C_{L'})$ (`ker_ideleClassArtinMap`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev Filter Topology
open scoped nonZeroDivisors Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT
namespace R57

variable {K : Type} [Field K] [NumberField K]

/-- A subgroup of the idèles containing the positive real and the complex local units contains `idelesInfPos`. -/
theorem idelesInfPos_le (H : Subgroup (IdeleGroup (𝓞 K) K))
    (hreal : ∀ (a : InfinitePlace K) (ha : a.IsReal) (u : a.Completionˣ),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal ha (u : a.Completion) →
        IdeleGroup.ofCompletion (𝓞 K) K a u ∈ H)
    (hcomplex : ∀ (a : InfinitePlace K), a.IsComplex → ∀ u : a.Completionˣ,
        IdeleGroup.ofCompletion (𝓞 K) K a u ∈ H) :
    idelesInfPos K ≤ H := by
  classical
  intro x ⟨hx1, hx2⟩
  have key : ∀ (F : Finset (InfinitePlace K)) (x : IdeleGroup (𝓞 K) K), (∀ v, ideleFinAt x v = 1) →
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) →
      (∀ w ∉ F, ideleInfAt x w = 1) → x ∈ H := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro x h1 _ h3
      have : x = 1 := by
        apply Units.ext
        refine Prod.ext (funext fun w => h3 w (by simp)) ?_
        refine FiniteAdeleRing.ext _ fun v => h1 v
      rw [this]; exact one_mem _
    | insert a F haF ih =>
      intro x h1 h2 h3
      set u : (a.Completion)ˣ := ⟨ideleInfAt x a, ideleInfAt x⁻¹ a, by
        rw [← ideleInfAt_mul, mul_inv_cancel, ideleInfAt_one], by
        rw [← ideleInfAt_mul, inv_mul_cancel, ideleInfAt_one]⟩ with hu
      set y := IdeleGroup.ofCompletion (𝓞 K) K a u with hy
      have hy' : y ∈ H := by
        by_cases ha : a.IsReal
        · exact hreal a ha u (h2 a ha)
        · exact hcomplex a (InfinitePlace.not_isReal_iff_isComplex.mp ha) u
      have hx' : x * y⁻¹ ∈ H := by
        refine ih (x * y⁻¹) (fun v => ?_) (fun w hw => ?_) (fun w hw => ?_)
        · rw [ideleFinAt_mul, ideleFinAt_inv, hy, ideleFinAt_ofCompletion, h1 v]; simp
        · by_cases hwa : w = a
          · subst hwa
            rw [ideleInfAt_mul, ideleInfAt_inv, hy, ideleInfAt_ofCompletion_self]
            have : ideleInfAt x w * ((u : w.Completion))⁻¹ = 1 := mul_inv_cancel₀ u.ne_zero
            rw [this]
            unfold IsPosAt; simp
          · rw [ideleInfAt_mul, ideleInfAt_inv, hy, ideleInfAt_ofCompletion_ne a w hwa, inv_one, mul_one]
            exact h2 w hw
        · by_cases hwa : w = a
          · subst hwa
            rw [ideleInfAt_mul, ideleInfAt_inv, hy, ideleInfAt_ofCompletion_self]
            exact mul_inv_cancel₀ u.ne_zero
          · rw [ideleInfAt_mul, ideleInfAt_inv, hy, ideleInfAt_ofCompletion_ne a w hwa, inv_one, mul_one]
            exact h3 w (by simp [hwa, hw])
      have := mul_mem hx' hy'
      rwa [inv_mul_cancel_right] at this
  exact key Finset.univ x hx1 hx2 (by simp)

/-- The idèle `ofCompletion` of a positive unit at a real place lies in the identity component. -/
theorem ofCompletion_real_mem_cc (a : InfinitePlace K) (ha : a.IsReal) (u : a.Completionˣ)
    (hu : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal ha (u : a.Completion)) :
    IdeleGroup.ofCompletion (𝓞 K) K a u ∈ connectedComponent (1 : IdeleGroup (𝓞 K) K) := by
  set e := InfinitePlace.Completion.isometryEquivRealOfIsReal ha with he
  have hsymm : (e.symm : ℝ → a.Completion) = (InfinitePlace.Completion.ringEquivRealOfIsReal ha).symm := rfl
  let ρ : ℝ → a.Completionˣ := fun t =>
    ⟨e.symm (Real.exp t), e.symm (Real.exp (-t)), by
      rw [hsymm, ← map_mul, ← Real.exp_add]; simp, by
      rw [hsymm, ← map_mul, ← Real.exp_add]; simp⟩
  have hρ : Continuous ρ := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact e.symm.continuous.comp Real.continuous_exp
    · exact e.symm.continuous.comp (Real.continuous_exp.comp continuous_neg)
  have h0 : ρ 0 = 1 := by
    apply Units.ext
    show e.symm (Real.exp 0) = 1
    rw [Real.exp_zero]
    exact map_one (InfinitePlace.Completion.ringEquivRealOfIsReal ha).symm
  have hu' : u = ρ (Real.log (InfinitePlace.Completion.extensionEmbeddingOfIsReal ha (u : a.Completion))) := by
    apply Units.ext
    show (u : a.Completion) = e.symm (Real.exp _)
    rw [Real.exp_log hu]
    exact ((InfinitePlace.Completion.ringEquivRealOfIsReal ha).symm_apply_apply _).symm
  set f : ℝ → IdeleGroup (𝓞 K) K := fun t => IdeleGroup.ofCompletion (𝓞 K) K a (ρ t) with hf
  have hfc : Continuous f := (NumberFieldKB.Ideles.IdeleGroup.continuous_ofCompletion a).comp hρ
  have hf0 : f 0 = 1 := by rw [hf]; simp only [h0, map_one]
  have := (isPreconnected_range hfc).subset_connectedComponent (Set.mem_range_self 0)
  rw [hf0] at this
  rw [hu']
  exact this (Set.mem_range_self _)

/-- The idèle `ofCompletion` of a unit at a complex place lies in the identity component. -/
theorem ofCompletion_complex_mem_cc (a : InfinitePlace K) (ha : a.IsComplex) (u : a.Completionˣ) :
    IdeleGroup.ofCompletion (𝓞 K) K a u ∈ connectedComponent (1 : IdeleGroup (𝓞 K) K) := by
  set e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex ha with he
  have hsymm : (e.symm : ℂ → a.Completion) = (InfinitePlace.Completion.ringEquivComplexOfIsComplex ha).symm := rfl
  let ρ : ℂ → a.Completionˣ := fun t =>
    ⟨e.symm (Complex.exp t), e.symm (Complex.exp (-t)), by
      rw [hsymm, ← map_mul, ← Complex.exp_add]; simp, by
      rw [hsymm, ← map_mul, ← Complex.exp_add]; simp⟩
  have hρ : Continuous ρ := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact e.symm.continuous.comp Complex.continuous_exp
    · exact e.symm.continuous.comp (Complex.continuous_exp.comp continuous_neg)
  have h0 : ρ 0 = 1 := by
    apply Units.ext
    show e.symm (Complex.exp 0) = 1
    rw [Complex.exp_zero, hsymm]
    exact map_one _
  have hne : InfinitePlace.Completion.ringEquivComplexOfIsComplex ha (u : a.Completion) ≠ 0 :=
    (map_ne_zero _).mpr u.ne_zero
  have hu' : u = ρ (Complex.log (InfinitePlace.Completion.ringEquivComplexOfIsComplex ha (u : a.Completion))) := by
    apply Units.ext
    show (u : a.Completion) = e.symm (Complex.exp _)
    rw [Complex.exp_log hne]
    exact ((InfinitePlace.Completion.ringEquivComplexOfIsComplex ha).symm_apply_apply _).symm
  set f : ℂ → IdeleGroup (𝓞 K) K := fun t => IdeleGroup.ofCompletion (𝓞 K) K a (ρ t) with hf
  have hfc : Continuous f := (NumberFieldKB.Ideles.IdeleGroup.continuous_ofCompletion a).comp hρ
  have hf0 : f 0 = 1 := by rw [hf]; simp only [h0, map_one]
  have := (isPreconnected_range hfc).subset_connectedComponent (Set.mem_range_self 0)
  rw [hf0] at this
  rw [hu']
  exact this (Set.mem_range_self _)

/-- `idelesInfPos` lies in the identity component of the idèle group. -/
theorem idelesInfPos_le_cc :
    idelesInfPos K ≤ Subgroup.connectedComponentOfOne (IdeleGroup (𝓞 K) K) :=
  idelesInfPos_le _ (fun a ha u hu => ofCompletion_real_mem_cc a ha u hu)
    (fun a ha u => ofCompletion_complex_mem_cc a ha u)

/-! ### The open subgroups `N_m` of finite index -/

variable (K) in
/-- The image `q(W_m)` of `W_m` in the idèle class group. -/
def Nm (m : Modulus K) : Subgroup (IdeleClassGroup (𝓞 K) K) :=
  (idelesW m).map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))

theorem mem_Nm {m : Modulus K} {x : IdeleGroup (𝓞 K) K} :
    (x : IdeleClassGroup (𝓞 K) K) ∈ Nm K m ↔ ∃ w ∈ idelesW m, w⁻¹ * x ∈ IdeleGroup.principalSubgroup (𝓞 K) K := by
  constructor
  · rintro ⟨w, hw, hwx⟩
    exact ⟨w, hw, QuotientGroup.eq.mp hwx⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, QuotientGroup.eq.mpr h⟩

theorem isOpen_Nm (m : Modulus K) : IsOpen (Nm K m : Set (IdeleClassGroup (𝓞 K) K)) :=
  QuotientGroup.isOpenMap_coe _ (isOpen_idelesW m)

/-- `N_m` has finite index in `C_K`: the quotient is a quotient of the finite ray class group `C_m`. -/
theorem finiteIndex_Nm (m : Modulus K) : (Nm K m).FiniteIndex := by
  have : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  let f : idelesMod m →* IdeleClassGroup (𝓞 K) K ⧸ Nm K m :=
    (QuotientGroup.mk' (Nm K m)).comp ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)).comp
      (idelesMod m).subtype)
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨x, hx⟩ := (prop_4_6b m).1 c
    exact ⟨x, by simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype]; exact congrArg _ hx⟩
  have hle : (idelesModToRay m).ker ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    obtain ⟨y, ⟨b, hb, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 (((prop_4_6a m).2 x).1 hx)
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype]
    rw [QuotientGroup.eq_one_iff, ← hyz, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 K) K) _).2 ⟨b, rfl⟩]
    exact ⟨z, hz, (one_mul (z : IdeleClassGroup (𝓞 K) K)).symm⟩
  have : (idelesModToRay m).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have : f.ker.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have : Finite (idelesMod m ⧸ f.ker) := inferInstance
  have : Finite (IdeleClassGroup (𝓞 K) K ⧸ Nm K m) := by
    refine Finite.of_surjective (QuotientGroup.kerLift f) ?_
    intro b
    obtain ⟨x, rfl⟩ := hsurj b
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact Subgroup.finiteIndex_of_finite_quotient

/-- An idèle whose class lies in every `N_m` ($\mathfrak m$ running over the moduli with all real places) is in the
closure of $K^\times\cdot I_\infty^+$: $W_\mathfrak m\subseteq I_\infty^+\cdot U$ for small $\mathfrak m$. -/
theorem mem_closure_of_forall_Nm (x : IdeleGroup (𝓞 K) K)
    (h : ∀ m : Modulus K, m.infinite = {w | w.IsReal} → (x : IdeleClassGroup (𝓞 K) K) ∈ Nm K m) :
    x ∈ closure ((IdeleGroup.principalSubgroup (𝓞 K) K ⊔ idelesInfPos K : Subgroup _) :
      Set (IdeleGroup (𝓞 K) K)) := by
  rw [mem_closure_iff_nhds_one]
  intro U hU
  obtain ⟨T, n, hTn⟩ := idele_nhds_one (inv_mem_nhds_one _ hU)
  obtain ⟨m, hm, hmT, hord⟩ := exists_modulus T (n + 1) (by omega)
  obtain ⟨w, hw, hwx⟩ := mem_Nm.1 (h m hm)
  obtain ⟨⟨hpos, hclose⟩, hunit⟩ := hw
  set i := infPart w with hi
  set y := w * i⁻¹ with hy
  have hiI : i ∈ idelesInfPos K := by
    refine ⟨fun v => ideleFinAt_infPart w v, fun a ha => ?_⟩
    exact hpos a (by rw [hm]; exact ha)
  have hyU : y ∈ U⁻¹ := by
    refine hTn y (fun a => ?_) (fun v hv => ?_) (fun v hv => ?_)
    · rw [hy, ideleInfAt_mul, ideleInfAt_inv, hi, ideleInfAt_infPart]
      exact mul_inv_cancel₀ (ideleInfAt_ne_zero w a)
    · rw [hy, ideleFinAt_mul, ideleFinAt_inv, hi, ideleFinAt_infPart, inv_one, mul_one]
      refine (hclose v (by rw [hmT]; exact hv)).trans ?_
      rw [WithZero.exp_le_exp]
      have := hord v hv
      omega
    · rw [hy, ideleFinAt_mul, ideleFinAt_inv, hi, ideleFinAt_infPart, inv_one, mul_one]
      exact hunit v (by rw [hmT]; exact hv)
  refine ⟨(w⁻¹ * x) * i, Subgroup.mul_mem_sup hwx hiI, ?_⟩
  have : (w⁻¹ * x) * i / x = y⁻¹ := by
    rw [mul_right_comm, mul_div_cancel_right, hy, mul_inv_rev, inv_inv, mul_comm]
  rw [this]
  simpa using hyU

/-! ### The identity component -/

/-- The image of $\overline{K^\times\cdot I_\infty^+}$ in $C_K$ is the identity component. -/
theorem image_closure_eq_cc :
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) ''
      closure ((IdeleGroup.principalSubgroup (𝓞 K) K ⊔ idelesInfPos K : Subgroup _) :
        Set (IdeleGroup (𝓞 K) K)) = connectedComponent (1 : IdeleClassGroup (𝓞 K) K) := by
  apply Set.Subset.antisymm
  · have hq : Continuous (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) :=
      QuotientGroup.continuous_mk
    refine (image_closure_subset_closure_image hq).trans (closure_minimal ?_ isClosed_connectedComponent)
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨p, hp, i, hi, rfl⟩ := Subgroup.mem_sup.1 hs
    have hp1 : (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) p = 1 :=
      (QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 K) K) _).2 hp
    rw [map_mul, hp1, one_mul (_ : IdeleClassGroup (𝓞 K) K)]
    have := hq.image_connectedComponent_subset (1 : IdeleGroup (𝓞 K) K)
      ⟨i, idelesInfPos_le_cc hi, rfl⟩
    rwa [map_one] at this
  · intro c hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨x, mem_closure_of_forall_Nm x (fun m _ => ?_), rfl⟩
    have hcl : IsClopen (Nm K m : Set (IdeleClassGroup (𝓞 K) K)) :=
      ⟨Subgroup.isClosed_of_isOpen _ (isOpen_Nm m), isOpen_Nm m⟩
    exact hcl.connectedComponent_subset (one_mem _) hc

/-! ### Tau Ceti's Artin maps -/

section TauCeti

variable {Ω : Type} [Field Ω] [Algebra K Ω]

/-- Every `φ_L` of the statement is Tau Ceti's idèlic Artin map. -/
theorem eq_tc (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L]
    (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (h : IsIdelicArtinMap L φ)
    (hK : ∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) : φ = idelicArtinTauCeti L :=
  idelicArtin_unique L φ _ h (isIdelicArtinMap_tauCeti L) hK (idelicArtinTauCeti_principal L)

/-- Tau Ceti's Artin maps are compatible with restriction (inside an arbitrary `Ω`). -/
theorem tc_compat' {L M : IntermediateField K Ω} [NumberField L] [IsAbelianGalois K L] [NumberField M]
    [IsAbelianGalois K M] (h : L ≤ M) (x : IdeleGroup (𝓞 K) K) :
    LocalCFT.galRestrict h (idelicArtinTauCeti M x) = idelicArtinTauCeti L x := by
  apply Abelianization.of_injective
  have h1 := TauCeti.ClassFieldTheory.globalArtinMap_comp K M (IntermediateField.inclusion h)
    IsSepClosed.lift
  have h2 := congrArg (fun F => F (Additive.ofMul (x : IdeleClassGroup (𝓞 K) K))) h1
  simp only [AddMonoidHom.comp_apply] at h2
  conv_rhs => rw [idelicArtinTauCeti_apply, TauCeti.ClassFieldTheory.of_ideleClassArtinMap K L
    (IsSepClosed.lift.comp (IntermediateField.inclusion h)), ← h2]
  rw [← Abelianization.map_of, of_idelicArtinTauCeti]
  rfl

theorem isAbelianGalois_of_algEquiv {L L' : Type} [Field L] [Field L'] [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') [IsAbelianGalois K L] : IsAbelianGalois K L' := by
  have : IsGalois K L' := IsGalois.of_algEquiv e
  refine { toIsGalois := this, toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩ }
  apply e.autCongr.symm.injective
  rw [map_mul, map_mul]
  exact (inferInstance : IsMulCommutative Gal(L/K)).is_comm.comm _ _

/-- The fibre of a homomorphism with open kernel is closed (a coset of the kernel). -/
theorem isClosed_fibre {A H : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group H]
    (ψ : A →* H) (hψ : IsOpen (ψ.ker : Set A)) (s : H) : IsClosed {c | ψ c = s} := by
  by_cases h : ∃ c0, ψ c0 = s
  · obtain ⟨c0, hc0⟩ := h
    have : {c | ψ c = s} = (fun c => c0⁻¹ * c) ⁻¹' (ψ.ker : Set A) := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hc0]
      constructor
      · intro hc; rw [hc]; exact inv_mul_cancel _
      · intro hc; exact (inv_mul_eq_one.1 hc).symm
    rw [this]
    exact (Subgroup.isClosed_of_isOpen _ hψ).preimage (continuous_const.mul continuous_id)
  · convert isClosed_empty
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hc => h ⟨c, hc⟩

theorem isOpen_ker_classArtin (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] :
    IsOpen ((TauCeti.ClassFieldTheory.ideleClassArtinMap K L).ker : Set (IdeleClassGroup (𝓞 K) K)) := by
  rw [TauCeti.ClassFieldTheory.ker_ideleClassArtinMap]
  exact TauCeti.GlobalNumberFields.isOpen_range_ideleClassNormMap K L

/-- Weil's idèle `Z(λ)` lies in `idelesInfPos`. -/
theorem weilZ_mem (t : {t : ℝ // 0 < t}) : WeilBNT.weilZ K t ∈ idelesInfPos K := by
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · show ((WeilBNT.weilZ K t : AdeleRing (𝓞 K) K).2 v) = 1
    rw [WeilBNT.weilZ_snd]; rfl
  · show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      (((WeilBNT.weilZ K t : AdeleRing (𝓞 K) K).1 w))
    rw [WeilBNT.weilZ_fst]
    unfold WeilBNT.realToCompletion
    simp only [hw, ↓reduceDIte]
    show 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (t : ℝ))
    rw [RingEquiv.apply_symm_apply]
    exact t.2

/-- Tau Ceti's Artin map kills `idelesInfPos`. -/
theorem idelesInfPos_le_ker (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] :
    idelesInfPos K ≤ (idelicArtinTauCeti L (K := K)).ker := fun _ hx =>
  remark_5_7_le_ker L (idelicArtinTauCeti L) (isIdelicArtinMap_tauCeti L) (idelicArtinTauCeti_principal L)
    (subset_closure (Subgroup.mem_sup_right hx))

/-- Every fibre of the Artin map meets the norm-one idèle classes. -/
theorem exists_normOne (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (s : Gal(L/K)) :
    ∃ c : NumberFieldKB.Ideles.IdeleClassGroup.normOne K,
      TauCeti.ClassFieldTheory.ideleClassArtinMap K L (c : IdeleClassGroup (𝓞 K) K) = s := by
  obtain ⟨x, hx⟩ := idelicArtinTauCeti_surjective L (K := K) s
  set y := x * (WeilBNT.weilZ K (WeilBNT.normRoot K x))⁻¹ with hy
  have hy1 : y ∈ NumberFieldKB.Ideles.ideleGroupOne K := WeilBNT.mul_weilZ_normRoot_inv_mem x
  refine ⟨⟨(y : IdeleClassGroup (𝓞 K) K), (NumberFieldKB.Ideles.IdeleClassGroup.mem_normOne_mk y).2 hy1⟩, ?_⟩
  show idelicArtinTauCeti L y = s
  rw [hy, map_mul, map_inv, (idelesInfPos_le_ker L (weilZ_mem _) : _), inv_one, mul_one, hx]

end TauCeti

/-! ### The index type -/

/-- A finite abelian extension of `K` inside `Ω` (no hypothesis on `Ω`). -/
structure Idx (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω] [Algebra K Ω] where
  L : IntermediateField K Ω
  [numberField : NumberField L]
  [isAbelianGalois : IsAbelianGalois K L]

attribute [instance] Idx.numberField Idx.isAbelianGalois

variable {Ω : Type} [Field Ω] [Algebra K Ω]

instance (i : Idx K Ω) : FiniteDimensional K i.L := Module.Finite.of_restrictScalars_finite ℚ K i.L

/-- The compositum of two finite abelian extensions. -/
def Idx.sup (i j : Idx K Ω) : Idx K Ω where
  L := i.L ⊔ j.L
  numberField := NumberField.of_module_finite K _
  isAbelianGalois :=
    { toIsGalois := inferInstance
      toIsMulCommutative := ⟨⟨fun σ τ => by
        apply IntermediateField.restrictNormalHomSupProd_injective i.L j.L
        rw [map_mul, map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
          (inferInstance : IsMulCommutative Gal(i.L/K)).is_comm.comm,
          (inferInstance : IsMulCommutative Gal(j.L/K)).is_comm.comm]⟩⟩ }

/-- The `surjective` field of `Remark5_7`: a compatible family of Galois elements is attained by an idèle
(compactness of $C_K^1$ and Cantor's intersection theorem). -/
theorem surjective_aux
    (φ : ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], IdeleGroup (𝓞 K) K →* Gal(L/K))
    (hφ : ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], IsIdelicArtinMap L (φ L) ∧
      ∀ a : Kˣ, φ L (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1)
    (σ : ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], Gal(L/K))
    (hσ : ∀ (L M : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L] [NumberField M]
        [IsAbelianGalois K M] (h : L ≤ M), LocalCFT.galRestrict h (σ M) = σ L) :
    ∃ x : IdeleGroup (𝓞 K) K, ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L],
        φ L x = σ L := by
  classical
  by_cases hne : Nonempty (Idx K Ω)
  swap
  · exact ⟨1, fun L _ _ => (hne ⟨⟨L⟩⟩).elim⟩
  have hφ' : ∀ i : Idx K Ω, φ i.L = idelicArtinTauCeti i.L := fun i =>
    eq_tc i.L (φ i.L) (hφ i.L).1 (hφ i.L).2
  let X := NumberFieldKB.Ideles.IdeleClassGroup.normOne K
  let t : Idx K Ω → Set X := fun i =>
    {c | TauCeti.ClassFieldTheory.ideleClassArtinMap K i.L (c : IdeleClassGroup (𝓞 K) K) = σ i.L}
  have htcl : ∀ i, IsClosed (t i) := fun i =>
    (isClosed_fibre _ (isOpen_ker_classArtin i.L) (σ i.L)).preimage continuous_subtype_val
  have : CompactSpace X := NumberFieldKB.Ideles.IdeleClassGroup.compactSpace_normOne
  have hdir : Directed (· ⊇ ·) t := by
    intro i j
    have key : ∀ (k : Idx K Ω) (hk : k.L ≤ (i.sup j).L) (c : X), c ∈ t (i.sup j) → c ∈ t k := by
      intro k hk c hc
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (c : IdeleClassGroup (𝓞 K) K)
      have hc' : TauCeti.ClassFieldTheory.ideleClassArtinMap K (i.sup j).L (c : IdeleClassGroup (𝓞 K) K) =
          σ (i.sup j).L := hc
      rw [← hx] at hc'
      have h1 : idelicArtinTauCeti (i.sup j).L x = σ (i.sup j).L := hc'
      have h2 : idelicArtinTauCeti k.L x = σ k.L := by
        rw [← tc_compat' hk, h1, hσ]
      show TauCeti.ClassFieldTheory.ideleClassArtinMap K k.L (c : IdeleClassGroup (𝓞 K) K) = σ k.L
      rw [← hx]
      exact h2
    exact ⟨i.sup j, fun c hc => key i le_sup_left c hc, fun c hc => key j le_sup_right c hc⟩
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir
    (fun i => exists_normOne i.L (σ i.L)) (fun i => (htcl i).isCompact) htcl
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (c : IdeleClassGroup (𝓞 K) K)
  refine ⟨x, fun L _ _ => ?_⟩
  have := Set.mem_iInter.1 hc ⟨L⟩
  show φ L x = σ L
  rw [hφ' ⟨L⟩, idelicArtinTauCeti_apply, hx]
  exact this

/-- The hard inclusion of the kernel formula: a family of idèlic Artin maps all killing `x` forces `x` into the
closure, by the existence theorem applied to the open subgroups `K^× · W_m` of finite index. -/
theorem mem_closure_of_forall_ker [IsAlgClosure K Ω]
    (φ : ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], IdeleGroup (𝓞 K) K →* Gal(L/K))
    (hφ : ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], IsIdelicArtinMap L (φ L) ∧
      ∀ a : Kˣ, φ L (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1)
    (x : IdeleGroup (𝓞 K) K)
    (hx : ∀ (L : IntermediateField K Ω) [NumberField L] [IsAbelianGalois K L], φ L x = 1) :
    x ∈ closure ((IdeleGroup.principalSubgroup (𝓞 K) K ⊔ idelesInfPos K : Subgroup _) :
      Set (IdeleGroup (𝓞 K) K)) := by
  refine mem_closure_of_forall_Nm x (fun m _ => ?_)
  obtain ⟨L, hL1, hL2, hL3, hL4, hcomm, hLN⟩ :=
    (Ch7.theorem9_5 K).isNormGroup (Nm K m) (isOpen_Nm m) (finiteIndex_Nm m)
  have : IsAbelianGalois K L := { toIsGalois := hL4, toIsMulCommutative := ⟨⟨hcomm⟩⟩ }
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let ι : L →ₐ[K] Ω := IsAlgClosed.lift
  let L' : IntermediateField K Ω := ι.fieldRange
  let e : L ≃ₐ[K] L' := AlgEquiv.ofInjectiveField ι
  have : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have : Module.Finite K L' := Module.Finite.equiv e.toLinearEquiv
  have : NumberField L' := NumberField.of_module_finite K L'
  have : IsAbelianGalois K L' := isAbelianGalois_of_algEquiv e
  have h1 := hx L'
  rw [eq_tc L' (φ L') (hφ L').1 (hφ L').2, idelicArtinTauCeti_apply] at h1
  have h2 : (x : IdeleClassGroup (𝓞 K) K) ∈ (TauCeti.ClassFieldTheory.ideleClassArtinMap K L').ker := h1
  rw [TauCeti.ClassFieldTheory.ker_ideleClassArtinMap,
    ← TauCeti.GlobalNumberFields.range_ideleClassNormMap_eq_of_algEquiv e] at h2
  rw [hLN, Ch7.normClasses_eq_tauCeti]
  exact h2

end R57

/-- **Remark 5.7(a)** (Milne, *CFT*, V, Remark 5.7(a), p. 179), proved: the global Artin map is onto, its kernel is
the closure of $K^\times\cdot\prod_{v\mid\infty}K_v^+$, and the image of that closure in $C_K$ is the identity
component. This is the named statement `Remark5_7`; see the module docstring for the proof. -/
@[kb "milne2020cft" "Ch. V, Remark 5.7(a)"]
theorem remark5_7 (K : Type) [Field K] [NumberField K] : Remark5_7 K where
  surjective := fun _ _ _ φ hφ σ hσ => R57.surjective_aux φ hφ σ hσ
  ker_eq := fun _ _ _ _ φ hφ x => ⟨fun h => R57.mem_closure_of_forall_ker φ hφ x h,
    fun h L _ _ => MonoidHom.mem_ker.1
      (remark_5_7_le_ker L (φ L) (hφ L).1 (hφ L).2 h)⟩
  connectedComponent := R57.image_closure_eq_cc

end NumberFieldKB.MilneCFT
