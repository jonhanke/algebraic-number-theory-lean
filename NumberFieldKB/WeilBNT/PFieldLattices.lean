import NumberFieldKB.WeilBNT.PFieldNorms

/-!
# Weil, *Basic Number Theory*, II.§2: lattices over a $p$-field

$K$ is a $p$-field (`PField`), $R$ = `pR hK`, $V$ a left vector space of finite dimension over $K$ with its natural
topology. An $R$-module in $V$ is an additive subgroup $M$ with $RM\subseteq M$ (`IsRModule`).

* `weil_II_2_prop5_isOpen`, `weil_II_2_prop5_isClosed`, `weil_II_2_prop5_compact_iff`: Prop. 5. An $R$-module $M$ is
  open and closed in the subspace $W$ it spans, and compact iff finitely generated.
* `IsKLattice`: Def. 2, a compact open $R$-module.
* `weil_II_2_text_p28_inf`, `weil_II_2_text_p28_comap`, `weil_II_2_text_p28_map`: text p. 28 (intersection with a
  subspace, inverse image by an injective and image by a surjective linear map); `weil_II_2_text_p28_ball`: the balls
  $N(v)\le r$ of a $K$-norm are lattices.
* `latticeNorm`, `weil_II_2_prop6`: Prop. 6 ($N_M(v)=\inf_{xv\in M}\operatorname{mod}_K(x)^{-1}$; it satisfies (ii),
  (iii) of Def. 1, $M=\{N_M\le1\}$, and $N_M$ is a $K$-norm iff $M$ is a lattice).
* `weil_II_2_cor1_prop6`: Cor. 1 (an open $R$-module is a lattice iff it contains no nonzero subspace);
  `weil_II_2_cor2_prop6`: Cor. 2.
* `weil_II_2_prop7`: Prop. 7 (in dimension 1, $L=Rv$).
* `weil_II_2_thm1`, `weil_II_2_thm2`: Thm. 1 ($L=\bigoplus Rv_i$ for a basis), Thm. 2 ($L=\bigoplus Rv_i$,
  $L'=\bigoplus P^{\nu_i}v_i$).
-/

open Topology Filter
open scoped NNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}
  {V : Type*} [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul K V] [T2Space V] [FiniteDimensional K V]

/-- An $R$-module in $V$ (II.§2): an additive subgroup stable under multiplication by $R$. -/
def IsRModule (hK : IsPField K p) (M : AddSubgroup V) : Prop := ∀ r ∈ pR hK, ∀ m ∈ M, r • m ∈ M

/-- Def. 2: a $K$-lattice in $V$ is a compact open $R$-module. -/
def IsKLattice (hK : IsPField K p) (M : AddSubgroup V) : Prop :=
  IsRModule hK M ∧ IsCompact (M : Set V) ∧ IsOpen (M : Set V)

section Toolkit

variable {V' : Type*} [AddCommGroup V'] [Module K V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
  [ContinuousSMul K V'] [T2Space V']

/-- The coordinate homeomorphism of a basis (I.§2, Cor. 1 of Thm. 3). -/
def basisHomeo {n : ℕ} (b : Module.Basis (Fin n) K V') : V' ≃ₜ (Fin n → K) :=
  (weil_I_2_thm3_cor1 b.equivFun.symm).homeomorph.symm

theorem basisHomeo_apply {n : ℕ} (b : Module.Basis (Fin n) K V') : ⇑(basisHomeo b) = b.equivFun := by
  funext v
  show (weil_I_2_thm3_cor1 b.equivFun.symm).homeomorph.symm v = _
  rw [Homeomorph.symm_apply_eq]
  simp [IsHomeomorph.homeomorph_apply]

/-- A linear map is determined by its values on a basis. -/
theorem map_eq_sum_repr {n : ℕ} (b : Module.Basis (Fin n) K V') (f : V' →ₗ[K] V) (v : V') :
    f v = ∑ i, b.equivFun v i • f (b i) := by
  calc f v = f (∑ i, b.repr v i • b i) := by rw [b.sum_repr]
    _ = _ := by rw [map_sum]; simp only [map_smul]; rfl

/-- A linear map out of a finite-dimensional space is continuous (I.§2, Cor. 1 of Thm. 3). -/
theorem continuous_of_linearMap [FiniteDimensional K V'] (f : V' →ₗ[K] V) : Continuous f := by
  set b := Module.finBasis K V' with hb
  have h1 : Continuous (fun x : Fin (Module.finrank K V') → K => ∑ i, x i • f (b i)) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have h2 : (f : V' → V) =
      (fun x : Fin (Module.finrank K V') → K => ∑ i, x i • f (b i)) ∘ b.equivFun := by
    funext v
    exact map_eq_sum_repr b f v
  rw [h2]
  rw [← basisHomeo_apply]
  exact h1.comp (basisHomeo b).continuous

/-- An injective linear map out of a finite-dimensional space is a closed embedding (I.§2, Thm. 3). -/
theorem isClosedEmbedding_of_injective [FiniteDimensional K V'] {f : V' →ₗ[K] V}
    (hf : Function.Injective f) : IsClosedEmbedding f := by
  set b := Module.finBasis K V' with hb
  have hli : LinearIndependent K (fun i => f (b i)) :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
  have h1 := weil_I_2_thm3 (fun i => f (b i)) hli
  have h2 : (f : V' → V) =
      (fun x : Fin (Module.finrank K V') → K => ∑ i, x i • f (b i)) ∘ b.equivFun := by
    funext v
    exact map_eq_sum_repr b f v
  rw [h2, ← basisHomeo_apply]
  exact h1.comp (basisHomeo b).isClosedEmbedding

/-- A surjective linear map between finite-dimensional spaces is open. -/
theorem isOpenMap_of_surjective [FiniteDimensional K V'] {f : V →ₗ[K] V'}
    (hf : Function.Surjective f) : IsOpenMap f := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ y, f (s y) = y := fun y => by simpa using LinearMap.congr_fun hs y
  have hsc : Continuous s := continuous_of_linearMap s
  rw [isOpenMap_iff_nhds_le]
  intro v
  rw [Filter.le_map_iff]
  intro U hU
  have hc : Continuous (fun y : V' => v + s (y - f v)) :=
    continuous_const.add (hsc.comp (continuous_id.sub continuous_const))
  have hmem : (fun y : V' => v + s (y - f v)) ⁻¹' U ∈ 𝓝 (f v) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using hU
  refine Filter.mem_of_superset hmem ?_
  intro y hy
  refine ⟨v + s (y - f v), hy, ?_⟩
  simp [hs']

/-- The inverse image of a lattice by an injective linear map is a lattice. -/
theorem isKLattice_comap (hK : IsPField K p) [FiniteDimensional K V'] {L : AddSubgroup V}
    (hL : IsKLattice hK L) {f : V' →ₗ[K] V} (hf : Function.Injective f) :
    IsKLattice hK (L.comap f.toAddMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr m hm
    show f (r • m) ∈ L
    rw [map_smul]
    exact hL.1 r hr _ hm
  · exact (isClosedEmbedding_of_injective hf).isProperMap.isCompact_preimage hL.2.1
  · exact hL.2.2.preimage (continuous_of_linearMap f)

end Toolkit

section Prop5Aux

/-- A linearly independent family in $M$ spanning the same subspace as $M$. -/
theorem exists_basis_in_span (M : AddSubgroup V) :
    ∃ (n : ℕ) (m : Fin n → V), (∀ i, m i ∈ M) ∧ LinearIndependent K m ∧
      Submodule.span K (Set.range m) = Submodule.span K (M : Set V) := by
  obtain ⟨b, hbM, hspan, hli⟩ := exists_linearIndependent K (M : Set V)
  have hfin : Finite b := hli.finite
  let e := Finite.equivFin b
  refine ⟨Nat.card b, fun i => ((e.symm i : b) : V), fun i => hbM (e.symm i).2,
    hli.comp _ e.symm.injective, ?_⟩
  have hr : Set.range (fun i => ((e.symm i : b) : V)) = b := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hv
      exact ⟨e ⟨v, hv⟩, by simp only [Equiv.symm_apply_apply]⟩
  rw [hr]
  exact hspan

/-- Prop. 5, key step: the span of a basis in $M$, with coefficients in $R$, is an open neighbourhood
of $0$ in the subspace spanned by $M$, and it lies in $M$. -/
theorem exists_open_nhd (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M) :
    ∃ (n : ℕ) (m : Fin n → V), (∀ i, m i ∈ M) ∧ ∃ U : Set (Submodule.span K (M : Set V)),
      IsOpen U ∧ (0 : Submodule.span K (M : Set V)) ∈ U ∧
      (∀ x ∈ U, (x : V) ∈ M) ∧
      (∀ x ∈ U, ∃ r : Fin n → K, (∀ i, r i ∈ pR hK) ∧ (x : V) = ∑ i, r i • m i) := by
  obtain ⟨n, m, hmM, hli, hspan⟩ := exists_basis_in_span (K := K) M
  have hg := weil_I_2_thm3 m hli
  set g : (Fin n → K) → V := fun x => ∑ i, x i • m i with hgdef
  have hmem : ∀ x, g x ∈ Submodule.span K (M : Set V) := by
    intro x
    rw [← hspan]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  set g' : (Fin n → K) → Submodule.span K (M : Set V) := fun x => ⟨g x, hmem x⟩ with hg'def
  have hg'c : Continuous g' := hg.continuous.subtype_mk _
  have hg'ind : Topology.IsInducing g' :=
    Topology.IsInducing.of_comp hg'c continuous_subtype_val hg.isInducing
  have hsurj : Function.Surjective g' := by
    intro w
    have hw : (w : V) ∈ Submodule.span K (Set.range m) := by rw [hspan]; exact w.2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
    exact ⟨c, Subtype.ext hc⟩
  have hopen : IsOpenMap g' :=
    hg'ind.isOpenMap (by rw [hsurj.range_eq]; exact isOpen_univ)
  have hRn : IsOpen (Set.pi Set.univ fun _ : Fin n => (pR hK : Set K)) :=
    isOpen_set_pi Set.finite_univ fun i _ => (weil_I_4_thm6_isOpen hK).1
  refine ⟨n, m, hmM, g' '' Set.pi Set.univ fun _ : Fin n => (pR hK : Set K), hopen _ hRn, ?_, ?_, ?_⟩
  · refine ⟨0, fun i _ => (pR hK).zero_mem, Subtype.ext ?_⟩
    simp [hg'def, hgdef]
  · rintro _ ⟨x, hx, rfl⟩
    show g x ∈ M
    exact M.sum_mem fun i _ => hM _ (hx i trivial) _ (hmM i)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, fun i => hx i trivial, rfl⟩

/-- $x$ is an $R$-combination of the elements of the finite set $s$. -/
def GenBy (hK : IsPField K p) (s : Finset V) (x : V) : Prop :=
  ∃ c : V → K, (∀ u, c u ∈ pR hK) ∧ x = ∑ u ∈ s, c u • u

theorem GenBy.zero (hK : IsPField K p) (s : Finset V) : GenBy hK s 0 :=
  ⟨fun _ => 0, fun _ => (pR hK).zero_mem, by simp⟩

theorem GenBy.add {hK : IsPField K p} {s : Finset V} {a b : V} (ha : GenBy hK s a)
    (hb : GenBy hK s b) : GenBy hK s (a + b) := by
  obtain ⟨c, hc, rfl⟩ := ha
  obtain ⟨d, hd, rfl⟩ := hb
  refine ⟨fun u => c u + d u, fun u => (pR hK).add_mem (hc u) (hd u), ?_⟩
  simp [add_smul, Finset.sum_add_distrib]

theorem GenBy.smul_mem {hK : IsPField K p} {s : Finset V} {v : V} (hv : v ∈ s) {r : K}
    (hr : r ∈ pR hK) : GenBy hK s (r • v) := by
  classical
  refine ⟨fun u => if u = v then r else 0, fun u => ?_, ?_⟩
  · show (if u = v then r else 0) ∈ pR hK
    split_ifs
    · exact hr
    · exact (pR hK).zero_mem
  · simp [ite_smul, Finset.sum_ite_eq', hv]

end Prop5Aux

/-- Prop. 5: $M$ is open in the subspace $W$ it spans (topologized as a subspace of $V$). -/
@[kb "weil1973bnt" "Ch. II, §2, Prop. 5 (open in the span)"]
theorem weil_II_2_prop5_isOpen (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M) :
    IsOpen ((Subtype.val : Submodule.span K (M : Set V) → V) ⁻¹' M) := by
  obtain ⟨n, m, hmM, U, hUo, hU0, hUM, -⟩ := exists_open_nhd hK hM
  exact AddSubgroup.isOpen_of_mem_nhds
    (M.comap (Submodule.span K (M : Set V)).subtype.toAddMonoidHom)
    (Filter.mem_of_superset (hUo.mem_nhds hU0) hUM)

@[kb "weil1973bnt" "Ch. II, §2, Prop. 5 (closed in the span)"]
theorem weil_II_2_prop5_isClosed (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M) :
    IsClosed ((Subtype.val : Submodule.span K (M : Set V) → V) ⁻¹' M) :=
  AddSubgroup.isClosed_of_isOpen
    (M.comap (Submodule.span K (M : Set V)).subtype.toAddMonoidHom) (weil_II_2_prop5_isOpen hK hM)

@[kb "weil1973bnt" "Ch. II, §2, Prop. 5 (compact iff finitely generated)"]
theorem weil_II_2_prop5_compact_iff (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M) :
    IsCompact (M : Set V) ↔ ∃ s : Finset V, (s : Set V) ⊆ M ∧
      ∀ m ∈ M, ∃ c : V → K, (∀ v, c v ∈ pR hK) ∧ m = ∑ v ∈ s, c v • v := by
  classical
  constructor
  · intro hc
    obtain ⟨n, m, hmM, U, hUo, hU0, hUM, hUr⟩ := exists_open_nhd hK hM
    set S : Set (Submodule.span K (M : Set V)) := Subtype.val ⁻¹' (M : Set V) with hSdef
    have himg : Subtype.val '' S = (M : Set V) := by
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hv
        exact ⟨⟨v, Submodule.subset_span hv⟩, hv, rfl⟩
    have hS : IsCompact S := by
      rw [Topology.IsInducing.subtypeVal.isCompact_iff]
      convert hc using 1
    obtain ⟨t, htS, hcov⟩ := hS.elim_nhds_subcover (fun w => (fun u => w + u) '' U)
      (fun w _ => ((isOpenMap_add_left w) U hUo).mem_nhds ⟨0, hU0, add_zero w⟩)
    refine ⟨t.image Subtype.val ∪ Finset.univ.image m, ?_, ?_⟩
    · intro v hv
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_union, Set.mem_image, Finset.mem_coe, Set.mem_range] at hv
      rcases hv with ⟨w, hw, rfl⟩ | ⟨i, rfl⟩
      · exact htS w hw
      · exact hmM i
    · intro x hx
      have hxS : (⟨x, Submodule.subset_span hx⟩ : Submodule.span K (M : Set V)) ∈ S := hx
      have := hcov hxS
      simp only [Set.mem_iUnion] at this
      obtain ⟨w, hwt, u, hu, hwu⟩ := this
      obtain ⟨r, hr, hu'⟩ := hUr u hu
      have hx' : x = (w : V) + ∑ i, r i • m i := by
        rw [← hu']
        exact (congrArg Subtype.val hwu).symm
      have h1 : GenBy hK (t.image Subtype.val ∪ Finset.univ.image m) (w : V) := by
        simpa using GenBy.smul_mem (hK := hK) (s := t.image Subtype.val ∪ Finset.univ.image m)
          (v := (w : V)) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hwt))
          (pR hK).one_mem
      have h2 : GenBy hK (t.image Subtype.val ∪ Finset.univ.image m) (∑ i, r i • m i) := by
        refine Finset.sum_induction _ (GenBy hK (t.image Subtype.val ∪ Finset.univ.image m))
          (fun a b ha hb => ha.add hb) (GenBy.zero hK _) fun i _ => ?_
        exact GenBy.smul_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
          (hr i)
      rw [hx']
      exact h1.add h2
  · rintro ⟨s, hsM, hgen⟩
    have hcont : Continuous (fun c : V → K => ∑ v ∈ s, c v • v) :=
      continuous_finsetSum _ fun v _ => (continuous_apply v).smul continuous_const
    have hcomp : IsCompact (Set.pi Set.univ fun _ : V => (pR hK : Set K)) :=
      isCompact_univ_pi fun _ => weil_I_4_thm6_isCompact hK
    have : (M : Set V) = (fun c : V → K => ∑ v ∈ s, c v • v) '' Set.pi Set.univ fun _ : V => (pR hK : Set K) := by
      ext v
      constructor
      · intro hv
        obtain ⟨c, hc, rfl⟩ := hgen v hv
        exact ⟨c, fun u _ => hc u, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact M.sum_mem fun u hu => hM _ (hc u trivial) _ (hsM hu)
    rw [this]
    exact hcomp.image hcont

@[kb "weil1973bnt" "Ch. II, §2, text p. 28 (intersection with a subspace)"]
theorem weil_II_2_text_p28_inf (hK : IsPField K p) {L : AddSubgroup V} (hL : IsKLattice hK L)
    (W : Submodule K V) : IsKLattice hK (L.comap (W.subtype.toAddMonoidHom)) :=
  isKLattice_comap hK hL (f := W.subtype) W.injective_subtype

@[kb "weil1973bnt" "Ch. II, §2, text p. 28 (inverse image by an injective linear map)"]
theorem weil_II_2_text_p28_comap (hK : IsPField K p) {V' : Type*} [AddCommGroup V'] [Module K V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousSMul K V'] [T2Space V']
    [FiniteDimensional K V'] {L : AddSubgroup V} (hL : IsKLattice hK L) {f : V' →ₗ[K] V}
    (hf : Function.Injective f) : IsKLattice hK (L.comap f.toAddMonoidHom) :=
  isKLattice_comap hK hL hf

@[kb "weil1973bnt" "Ch. II, §2, text p. 28 (image by a surjective linear map)"]
theorem weil_II_2_text_p28_map (hK : IsPField K p) {V' : Type*} [AddCommGroup V'] [Module K V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousSMul K V'] [T2Space V']
    [FiniteDimensional K V'] {L : AddSubgroup V} (hL : IsKLattice hK L) {f : V →ₗ[K] V'}
    (hf : Function.Surjective f) : IsKLattice hK (L.map f.toAddMonoidHom) := by
  have hcoe : ((L.map f.toAddMonoidHom : AddSubgroup V') : Set V') = f '' (L : Set V) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro r hr _ ⟨m, hm, rfl⟩
    exact ⟨r • m, hL.1 r hr m hm, by simp⟩
  · rw [hcoe]
    exact hL.2.1.image (continuous_of_linearMap f)
  · rw [hcoe]
    exact isOpenMap_of_surjective hf _ hL.2.2

/-- Text p. 28: the ball $N(v)\le r$ ($r>0$) of a $K$-norm, as an additive subgroup. -/
def normBall {N : V → ℝ≥0} (hN : IsKNorm (K := K) N) (r : ℝ≥0) : AddSubgroup V where
  carrier := {v | N v ≤ r}
  add_mem' {a b} ha hb := (hN.add_le a b).trans (max_le ha hb)
  zero_mem' := by
    show N 0 ≤ r
    rw [(hN.eq_zero_iff 0).2 rfl]; exact zero_le
  neg_mem' {a} ha := by
    show N (-a) ≤ r
    have h := hN.smul (-1) a
    rw [neg_one_smul] at h
    have h1 : modK K (-1 : K) = 1 := by rw [modK_neg]; exact modK_one
    rw [h, h1, one_mul]; exact ha

@[kb "weil1973bnt" "Ch. II, §2, text p. 28 (the balls of a K-norm are lattices)"]
theorem weil_II_2_text_p28_ball (hK : IsPField K p) {N : V → ℝ≥0} (hN : IsKNorm (K := K) N) {r : ℝ≥0}
    (hr : 0 < r) : IsKLattice hK (normBall hN r) := by
  obtain ⟨hc, hcomp, hbasis⟩ := weil_II_1_prop1 hK hN
  refine ⟨?_, hcomp r, ?_⟩
  · intro x hx m hm
    show N (x • m) ≤ r
    rw [hN.smul]
    have hx' : modK K x ≤ 1 := hx
    calc modK K x * N m ≤ 1 * N m := mul_le_mul' hx' le_rfl
      _ = N m := one_mul _
      _ ≤ r := hm
  · exact AddSubgroup.isOpen_of_mem_nhds (normBall hN r) (hbasis.mem_of_mem hr)

variable (K) in
/-- Prop. 6: $N_M(v)=\inf\{\operatorname{mod}_K(x)^{-1}: x\ne0,\ xv\in M\}$. -/
def latticeNorm (M : AddSubgroup V) (v : V) : ℝ≥0 :=
  ⨅ x : {x : K // x ≠ 0 ∧ x • v ∈ M}, (modK K (x : K))⁻¹

section Prop6Aux

/-- The set $\{x : xv\in M\}$ is closed downwards for the module. -/
theorem mem_of_modK_le (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M) {v : V}
    {x y : K} (hx : x • v ∈ M) (hxy : modK K y ≤ modK K x) : y • v ∈ M := by
  by_cases hx0 : x = 0
  · have : y = 0 := modK_eq_zero_iff.1 (le_antisymm (by simpa [hx0] using hxy) zero_le)
    subst this
    simp [M.zero_mem]
  · have hr : y * x⁻¹ ∈ pR hK := by
      show modK K (y * x⁻¹) ≤ 1
      rw [modK_mul, modK_inv hx0]
      exact (mul_inv_le_iff₀ (modK_pos_iff.2 hx0)).2 (by simpa using hxy)
    have := hM _ hr _ hx
    rwa [smul_smul, mul_assoc, inv_mul_cancel₀ hx0, mul_one] at this

/-- For an open subgroup $M$ and any $v$, some nonzero multiple $xv$ lies in $M$. -/
theorem exists_ne_zero_smul_mem {M : AddSubgroup V} (hMo : IsOpen (M : Set V)) (v : V) :
    ∃ x : K, x ≠ 0 ∧ x • v ∈ M := by
  have hc : Continuous (fun x : K => x • v) := continuous_id.smul continuous_const
  have hU : (fun x : K => x • v) ⁻¹' (M : Set V) ∈ 𝓝 (0 : K) :=
    (hMo.preimage hc).mem_nhds (by simp [M.zero_mem])
  obtain ⟨ε, hε, hsub⟩ := hasBasis_nhds_zero_modK.mem_iff.1 hU
  obtain ⟨a, ha, haε⟩ := exists_modK_pos_lt (K := K) hε
  exact ⟨a, modK_pos_iff.1 ha, hsub (show modK K a ≤ ε from haε.le)⟩

/-- A gap constant: distinct values of the module differ by a factor of at least $g^{-1}$. -/
theorem exists_gap_const (hK : IsPField K p) : ∃ g : ℝ≥0, 0 < g ∧ g < 1 ∧
    ∀ x y : K, x ≠ 0 → modK K y < modK K x → modK K y ≤ g * modK K x := by
  obtain ⟨π, hπ0, hπ1, hmax⟩ := exists_gen hK
  refine ⟨modK K π, modK_pos_iff.2 hπ0, hπ1, fun x y hx hxy => ?_⟩
  have h1 : modK K (y * x⁻¹) < 1 := by
    rw [modK_mul, modK_inv hx]
    exact (mul_inv_lt_iff₀ (modK_pos_iff.2 hx)).2 (by simpa using hxy)
  have h2 := hmax _ h1
  rw [modK_mul, modK_inv hx] at h2
  exact (mul_inv_le_iff₀ (modK_pos_iff.2 hx)).1 h2

theorem latticeNorm_le_inv {M : AddSubgroup V} {v : V} {x : K} (hx : x ≠ 0) (hxv : x • v ∈ M) :
    latticeNorm K M v ≤ (modK K x)⁻¹ := by
  unfold latticeNorm
  exact ciInf_le (OrderBot.bddBelow _) (⟨x, hx, hxv⟩ : {x : K // x ≠ 0 ∧ x • v ∈ M})

theorem exists_lt_of_latticeNorm_lt {M : AddSubgroup V} (hMo : IsOpen (M : Set V)) {v : V}
    {s : ℝ≥0} (h : latticeNorm K M v < s) : ∃ x : K, x ≠ 0 ∧ x • v ∈ M ∧ (modK K x)⁻¹ < s := by
  have : Nonempty {x : K // x ≠ 0 ∧ x • v ∈ M} := by
    obtain ⟨x, hx, hxv⟩ := exists_ne_zero_smul_mem (K := K) hMo v
    exact ⟨⟨x, hx, hxv⟩⟩
  unfold latticeNorm at h
  obtain ⟨⟨x, hx, hxv⟩, hlt⟩ := exists_lt_of_ciInf_lt h
  exact ⟨x, hx, hxv, hlt⟩

theorem le_latticeNorm {M : AddSubgroup V} (hMo : IsOpen (M : Set V)) {v : V} {s : ℝ≥0}
    (h : ∀ x : K, x ≠ 0 → x • v ∈ M → s ≤ (modK K x)⁻¹) : s ≤ latticeNorm K M v := by
  have : Nonempty {x : K // x ≠ 0 ∧ x • v ∈ M} := by
    obtain ⟨x, hx, hxv⟩ := exists_ne_zero_smul_mem (K := K) hMo v
    exact ⟨⟨x, hx, hxv⟩⟩
  unfold latticeNorm
  exact le_ciInf fun ⟨x, hx, hxv⟩ => h x hx hxv

/-- The infimum defining $N_M(v)$ is attained when it is positive. -/
theorem exists_attained (hK : IsPField K p) {M : AddSubgroup V} (hMo : IsOpen (M : Set V)) {v : V}
    (h : 0 < latticeNorm K M v) :
    ∃ y : K, y ≠ 0 ∧ y • v ∈ M ∧ latticeNorm K M v = (modK K y)⁻¹ := by
  obtain ⟨g, hg0, hg1, hgap⟩ := exists_gap_const hK
  set s := latticeNorm K M v with hs
  have hlt : s < s * g⁻¹ := by
    have : 1 < g⁻¹ := (one_lt_inv₀ hg0).2 hg1
    calc s = s * 1 := (mul_one s).symm
      _ < s * g⁻¹ := mul_lt_mul_of_pos_left this h
  obtain ⟨y, hy0, hyv, hy⟩ := exists_lt_of_latticeNorm_lt hMo hlt
  have hmin : ∀ z : K, z ≠ 0 → z • v ∈ M → (modK K y)⁻¹ ≤ (modK K z)⁻¹ := by
    intro z hz hzv
    by_contra hcon
    rw [not_le] at hcon
    have hya := modK_pos_iff.2 hy0
    have hza := modK_pos_iff.2 hz
    have h1 : modK K y < modK K z := (inv_lt_inv₀ hza hya).1 hcon
    have h2 := hgap z y hz h1
    have h3 : s ≤ (modK K z)⁻¹ := latticeNorm_le_inv hz hzv
    have h4 : (g * modK K z)⁻¹ ≤ (modK K y)⁻¹ := inv_anti₀ hya h2
    rw [mul_inv] at h4
    have h5 : s * g⁻¹ ≤ (modK K y)⁻¹ :=
      calc s * g⁻¹ = g⁻¹ * s := mul_comm _ _
        _ ≤ g⁻¹ * (modK K z)⁻¹ := mul_le_mul' le_rfl h3
        _ ≤ (modK K y)⁻¹ := h4
    exact absurd hy (not_lt.2 h5)
  have hle : (modK K y)⁻¹ ≤ s := le_latticeNorm hMo hmin
  exact ⟨y, hy0, hyv, le_antisymm (latticeNorm_le_inv hy0 hyv) hle⟩

theorem forall_smul_mem_of_latticeNorm_eq_zero (hK : IsPField K p) {M : AddSubgroup V}
    (hM : IsRModule hK M) (hMo : IsOpen (M : Set V)) {v : V} (h : latticeNorm K M v = 0) (x : K) :
    x • v ∈ M := by
  by_cases hx : x = 0
  · simp [hx, M.zero_mem]
  · have hpos : 0 < (modK K x)⁻¹ := inv_pos.2 (modK_pos_iff.2 hx)
    have hlt : latticeNorm K M v < (modK K x)⁻¹ := by rw [h]; exact hpos
    obtain ⟨y, hy0, hyv, hy⟩ := exists_lt_of_latticeNorm_lt hMo hlt
    have : modK K x < modK K y := (inv_lt_inv₀ (modK_pos_iff.2 hy0) (modK_pos_iff.2 hx)).1 hy
    exact mem_of_modK_le hK hM hyv this.le

/-- Characterization: $xv\in M$ iff $\operatorname{mod}_K(x)N_M(v)\le1$. -/
theorem smul_mem_iff_latticeNorm (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M)
    (hMo : IsOpen (M : Set V)) {v : V} {x : K} :
    x • v ∈ M ↔ modK K x * latticeNorm K M v ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, M.zero_mem]
  constructor
  · intro h
    have := latticeNorm_le_inv hx h
    have hpos := modK_pos_iff.2 hx
    calc modK K x * latticeNorm K M v ≤ modK K x * (modK K x)⁻¹ := mul_le_mul' le_rfl this
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  · intro h
    rcases eq_zero_or_pos (latticeNorm K M v) with h0 | hpos
    · exact forall_smul_mem_of_latticeNorm_eq_zero hK hM hMo h0 x
    · obtain ⟨y, hy0, hyv, hy⟩ := exists_attained hK hMo hpos
      refine mem_of_modK_le hK hM hyv ?_
      have hya := modK_pos_iff.2 hy0
      rw [hy] at h
      have := (mul_inv_le_iff₀ hya).1 (by simpa [mul_comm] using h)
      simpa using this

theorem eq_zero_of_forall_modK_mul_le {t : ℝ≥0} (h : ∀ x : K, modK K x * t ≤ 1) : t = 0 := by
  by_contra ht
  have htp : 0 < t := pos_iff_ne_zero.2 ht
  obtain ⟨b, hb⟩ := exists_modK_gt (K := K) t⁻¹
  have := mul_lt_mul_of_pos_right hb htp
  rw [inv_mul_cancel₀ ht] at this
  exact absurd (h b) (not_le.2 this)

theorem latticeNorm_eq_zero_iff (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M)
    (hMo : IsOpen (M : Set V)) {v : V} : latticeNorm K M v = 0 ↔ ∀ x : K, x • v ∈ M := by
  constructor
  · exact forall_smul_mem_of_latticeNorm_eq_zero hK hM hMo
  · intro h
    exact eq_zero_of_forall_modK_mul_le fun x => (smul_mem_iff_latticeNorm hK hM hMo).1 (h x)

theorem latticeNorm_smul_le {M : AddSubgroup V} (hMo : IsOpen (M : Set V))
    {a : K} (ha : a ≠ 0) (v : V) :
    latticeNorm K M (a • v) ≤ modK K a * latticeNorm K M v := by
  have hap := modK_pos_iff.2 ha
  have h : latticeNorm K M (a • v) * (modK K a)⁻¹ ≤ latticeNorm K M v := by
    refine le_latticeNorm hMo fun z hz hzv => ?_
    have hmem : (z * a⁻¹) • (a • v) ∈ M := by
      rw [smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]; exact hzv
    have := latticeNorm_le_inv (mul_ne_zero hz (inv_ne_zero ha)) hmem
    rw [modK_mul, modK_inv ha, mul_inv, inv_inv] at this
    calc latticeNorm K M (a • v) * (modK K a)⁻¹ ≤ (modK K z)⁻¹ * modK K a * (modK K a)⁻¹ :=
          mul_le_mul' this le_rfl
      _ = (modK K z)⁻¹ := mul_inv_cancel_right₀ hap.ne' _
  calc latticeNorm K M (a • v)
      = latticeNorm K M (a • v) * (modK K a)⁻¹ * modK K a :=
        (inv_mul_cancel_right₀ hap.ne' _).symm
    _ ≤ latticeNorm K M v * modK K a := mul_le_mul' h le_rfl
    _ = _ := mul_comm _ _

theorem latticeNorm_smul (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M)
    (hMo : IsOpen (M : Set V)) (x : K) (v : V) :
    latticeNorm K M (x • v) = modK K x * latticeNorm K M v := by
  by_cases hx : x = 0
  · subst hx
    have : latticeNorm K M (0 : V) = 0 := by
      exact (latticeNorm_eq_zero_iff hK hM hMo).2 fun x => by simp [M.zero_mem]
    simp [this]
  · refine le_antisymm (latticeNorm_smul_le hMo hx v) ?_
    have h := latticeNorm_smul_le hMo (inv_ne_zero hx) (x • v)
    rw [smul_smul, inv_mul_cancel₀ hx, one_smul, modK_inv hx] at h
    have hp := modK_pos_iff.2 hx
    calc modK K x * latticeNorm K M v ≤ modK K x * ((modK K x)⁻¹ * latticeNorm K M (x • v)) :=
          mul_le_mul' le_rfl h
      _ = latticeNorm K M (x • v) := mul_inv_cancel_left₀ hp.ne' _

theorem latticeNorm_add_le (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M)
    (hMo : IsOpen (M : Set V)) (v w : V) :
    latticeNorm K M (v + w) ≤ max (latticeNorm K M v) (latticeNorm K M w) := by
  have key : ∀ v w : V, latticeNorm K M w ≤ latticeNorm K M v →
      latticeNorm K M (v + w) ≤ latticeNorm K M v := by
    intro v w hwv
    rcases eq_zero_or_pos (latticeNorm K M v) with h0 | hpos
    · have h0w : latticeNorm K M w = 0 := le_antisymm (h0 ▸ hwv) zero_le
      have : latticeNorm K M (v + w) = 0 :=
        (latticeNorm_eq_zero_iff hK hM hMo).2 fun x => by
          rw [smul_add]
          exact M.add_mem (forall_smul_mem_of_latticeNorm_eq_zero hK hM hMo h0 x)
            (forall_smul_mem_of_latticeNorm_eq_zero hK hM hMo h0w x)
      rw [this]; exact zero_le
    · obtain ⟨y, hy0, hyv, hy⟩ := exists_attained hK hMo hpos
      have hyp := modK_pos_iff.2 hy0
      have h2 : y • w ∈ M := by
        rw [smul_mem_iff_latticeNorm hK hM hMo]
        calc modK K y * latticeNorm K M w ≤ modK K y * latticeNorm K M v :=
              mul_le_mul' le_rfl hwv
          _ = 1 := by rw [hy]; exact mul_inv_cancel₀ hyp.ne'
      have h3 : y • (v + w) ∈ M := by rw [smul_add]; exact M.add_mem hyv h2
      have h4 := (smul_mem_iff_latticeNorm hK hM hMo).1 h3
      rw [hy]
      calc latticeNorm K M (v + w) = (modK K y)⁻¹ * (modK K y * latticeNorm K M (v + w)) :=
            (inv_mul_cancel_left₀ hyp.ne' _).symm
        _ ≤ (modK K y)⁻¹ * 1 := mul_le_mul' le_rfl h4
        _ = (modK K y)⁻¹ := mul_one _
  rcases le_total (latticeNorm K M w) (latticeNorm K M v) with h | h
  · exact (key v w h).trans (le_max_left _ _)
  · rw [add_comm]; exact (key w v h).trans (le_max_right _ _)

theorem mem_iff_latticeNorm_le (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M)
    (hMo : IsOpen (M : Set V)) (v : V) : v ∈ M ↔ latticeNorm K M v ≤ 1 := by
  simpa using (smul_mem_iff_latticeNorm hK hM hMo (v := v) (x := 1))

/-- A compact subgroup contains no full line. -/
theorem exists_smul_not_mem_of_compact {M : AddSubgroup V} (hc : IsCompact (M : Set V)) {v : V}
    (hv : v ≠ 0) : ∃ x : K, x • v ∉ M := by
  by_contra h
  push Not at h
  have hinj : Function.Injective (LinearMap.toSpanSingleton K V v) :=
    fun a b hab => smul_left_injective K hv hab
  have hce := isClosedEmbedding_of_injective (V' := K) hinj
  have hcomp : IsCompact (LinearMap.toSpanSingleton K V v ⁻¹' (M : Set V)) :=
    hce.isProperMap.isCompact_preimage hc
  have hu : (LinearMap.toSpanSingleton K V v ⁻¹' (M : Set V)) = Set.univ :=
    Set.eq_univ_of_forall fun x => h x
  rw [hu] at hcomp
  exact not_compactSpace K ⟨hcomp⟩

theorem isKNorm_latticeNorm_iff (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M)
    (hMo : IsOpen (M : Set V)) :
    IsKNorm (K := K) (latticeNorm K M) ↔ IsKLattice hK M := by
  constructor
  · intro hN
    have hEq : normBall hN 1 = M := by
      ext v
      exact (mem_iff_latticeNorm_le hK hM hMo v).symm
    rw [← hEq]
    exact weil_II_2_text_p28_ball hK hN one_pos
  · intro hL
    refine ⟨fun v => ⟨fun h => ?_, fun h => ?_⟩, latticeNorm_smul hK hM hMo,
      latticeNorm_add_le hK hM hMo⟩
    · by_contra hv
      obtain ⟨x, hx⟩ := exists_smul_not_mem_of_compact (K := K) hL.2.1 hv
      exact hx (forall_smul_mem_of_latticeNorm_eq_zero hK hM hMo h x)
    · subst h
      exact (latticeNorm_eq_zero_iff hK hM hMo).2 fun x => by simp [M.zero_mem]

end Prop6Aux

@[kb "weil1973bnt" "Ch. II, §2, Prop. 6"]
theorem weil_II_2_prop6 (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M)
    (hMo : IsOpen (M : Set V)) :
    (∀ (x : K) (v : V), latticeNorm K M (x • v) = modK K x * latticeNorm K M v) ∧
      (∀ v w : V, latticeNorm K M (v + w) ≤ max (latticeNorm K M v) (latticeNorm K M w)) ∧
      (M : Set V) = {v | latticeNorm K M v ≤ 1} ∧
      (IsKNorm (K := K) (latticeNorm K M) ↔ IsKLattice hK M) :=
  ⟨latticeNorm_smul hK hM hMo, latticeNorm_add_le hK hM hMo,
    Set.ext fun v => mem_iff_latticeNorm_le hK hM hMo v, isKNorm_latticeNorm_iff hK hM hMo⟩

@[kb "weil1973bnt" "Ch. II, §2, Cor. 1 of Prop. 6"]
theorem weil_II_2_cor1_prop6 (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M)
    (hMo : IsOpen (M : Set V)) :
    IsKLattice hK M ↔ ∀ W : Submodule K V, (W : Set V) ⊆ M → W = ⊥ := by
  constructor
  · intro hL W hW
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    obtain ⟨x, hx⟩ := exists_smul_not_mem_of_compact (K := K) hL.2.1 hv0
    exact hx (hW (W.smul_mem x hv))
  · intro h
    rw [← isKNorm_latticeNorm_iff hK hM hMo]
    refine ⟨fun v => ⟨fun h0 => ?_, fun h0 => ?_⟩, latticeNorm_smul hK hM hMo,
      latticeNorm_add_le hK hM hMo⟩
    · have hall := (latticeNorm_eq_zero_iff hK hM hMo).1 h0
      have hbot := h (K ∙ v) (by
        intro w hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
        exact hall a)
      exact Submodule.span_singleton_eq_bot.1 hbot
    · subst h0
      exact (latticeNorm_eq_zero_iff hK hM hMo).2 fun x => by simp [M.zero_mem]

@[kb "weil1973bnt" "Ch. II, §2, Cor. 2 of Prop. 6"]
theorem weil_II_2_cor2_prop6 (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M)
    (hMo : IsOpen (M : Set V)) {W : Submodule K V} (hWM : (W : Set V) ⊆ M)
    (hWmax : ∀ W' : Submodule K V, (W' : Set V) ⊆ M → W' ≤ W) {W' : Submodule K V} (hWW' : IsCompl W W') :
    IsKLattice hK (M.comap W'.subtype.toAddMonoidHom) ∧
      (M : Set V) = {v | ∃ a ∈ M, a ∈ W' ∧ ∃ w ∈ W, v = a + w} := by
  refine ⟨?_, ?_⟩
  · have hM' : IsRModule hK (M.comap W'.subtype.toAddMonoidHom) := by
      intro r hr m hm
      exact hM r hr _ hm
    have hMo' : IsOpen ((M.comap W'.subtype.toAddMonoidHom : AddSubgroup W') : Set W') :=
      hMo.preimage continuous_subtype_val
    refine (weil_II_2_cor1_prop6 (V := W') hK hM' hMo').2 ?_
    intro U hU
    have hU' : ((U.map W'.subtype : Submodule K V) : Set V) ⊆ M := by
      rintro _ ⟨u, hu, rfl⟩
      exact hU hu
    have h1 := hWmax _ hU'
    have h2 : U.map W'.subtype ≤ W' := by
      rintro _ ⟨u, _, rfl⟩
      exact u.2
    have h3 : U.map W'.subtype ≤ ⊥ := by
      rw [← hWW'.disjoint.eq_bot]
      exact le_inf h1 h2
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : (u : V) ∈ U.map W'.subtype := ⟨u, hu, rfl⟩
    have h4 := h3 this
    rw [Submodule.mem_bot] at h4
    exact Subtype.ext h4
  · ext v
    constructor
    · intro hv
      have htop : v ∈ W ⊔ W' := by rw [hWW'.sup_eq_top]; trivial
      obtain ⟨w, hw, a, ha, hwa⟩ := Submodule.mem_sup.1 htop
      refine ⟨a, ?_, ha, w, hw, by rw [← hwa, add_comm]⟩
      have : a = v - w := by rw [← hwa]; abel
      rw [this]
      exact M.sub_mem hv (hWM hw)
    · rintro ⟨a, ha, _, w, hw, rfl⟩
      exact M.add_mem ha (hWM hw)

@[kb "weil1973bnt" "Ch. II, §2, Prop. 7"]
theorem weil_II_2_prop7 (hK : IsPField K p) (hV : Module.finrank K V = 1) {L : AddSubgroup V}
    (hL : IsKLattice hK L) : ∃ v : V, v ≠ 0 ∧ (L : Set V) = {w | ∃ r ∈ pR hK, w = r • v} := by
  have hM := hL.1
  have hMo := hL.2.2
  have hN := (isKNorm_latticeNorm_iff hK hM hMo).2 hL
  obtain ⟨w0, hw0⟩ : ∃ w0 : V, w0 ≠ 0 := by
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hV]; exact one_pos)
    exact exists_ne 0
  have hpos : 0 < latticeNorm K L w0 :=
    pos_iff_ne_zero.2 fun h => hw0 ((hN.eq_zero_iff w0).1 h)
  obtain ⟨y, hy0, hyv, hy⟩ := exists_attained hK hMo hpos
  have hv0 : y • w0 ≠ 0 := smul_ne_zero hy0 hw0
  have hNv : latticeNorm K L (y • w0) = 1 := by
    rw [latticeNorm_smul hK hM hMo, hy]
    exact mul_inv_cancel₀ (modK_pos_iff.2 hy0).ne'
  refine ⟨y • w0, hv0, ?_⟩
  ext w
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (y • w0) hv0).1 hV w
  constructor
  · intro h
    refine ⟨c, ?_, rfl⟩
    have := (smul_mem_iff_latticeNorm hK hM hMo).1 h
    rw [hNv, mul_one] at this
    exact this
  · rintro ⟨r, hr, hrc⟩
    have hcr : c = r := smul_left_injective K hv0 hrc
    subst hcr
    show c • y • w0 ∈ L
    rw [smul_mem_iff_latticeNorm hK hM hMo, hNv, mul_one]
    exact hr

section ThmAux

/-- Membership of $\sum d_iB_i$ in $M$ when the norm $N_M$ is the sup-norm for $B$. -/
theorem sum_mem_iff_forall (hK : IsPField K p) {M : AddSubgroup V} (hM : IsRModule hK M)
    (hMo : IsOpen (M : Set V)) {n : ℕ} {B : Fin n → V}
    (hsup : ∀ c : Fin n → K, latticeNorm K M (∑ i, c i • B i) =
      Finset.univ.sup fun i => latticeNorm K M (c i • B i)) (d : Fin n → K) :
    ∑ i, d i • B i ∈ M ↔ ∀ i, modK K (d i) * latticeNorm K M (B i) ≤ 1 := by
  rw [mem_iff_latticeNorm_le hK hM hMo, hsup, Finset.sup_le_iff]
  simp only [Finset.mem_univ, true_implies, latticeNorm_smul hK hM hMo]

/-- Rescaling the vectors of a basis preserves the sup-norm property. -/
theorem sup_rescale {n : ℕ} {N : V → ℝ≥0} {b : Fin n → V} (y : Fin n → K)
    (hb : ∀ c : Fin n → K, N (∑ i, c i • b i) = Finset.univ.sup fun i => N (c i • b i)) :
    ∀ c : Fin n → K, N (∑ i, c i • (y i • b i)) =
      Finset.univ.sup fun i => N (c i • (y i • b i)) := by
  intro c
  simp only [smul_smul]
  exact hb (fun i => c i * y i)

/-- A basis with its vectors multiplied by nonzero scalars is again a basis. -/
theorem exists_rescaled_basis (b : Module.Basis (Fin (Module.finrank K V)) K V)
    (y : Fin (Module.finrank K V) → K) (hy : ∀ i, y i ≠ 0) :
    ∃ b' : Module.Basis (Fin (Module.finrank K V)) K V, ∀ i, b' i = y i • b i := by
  have hli : LinearIndependent K (fun i => y i • b i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    simp only [smul_smul] at hg
    have := Fintype.linearIndependent_iff.1 b.linearIndependent (fun i => g i * y i) hg i
    exact (mul_eq_zero.1 this).resolve_right (hy i)
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (Fintype.card_fin _), fun i => by simp⟩

theorem coord_equiv (hK : IsPField K p) {g : K} (hg : g ≠ 0) (d : K) :
    modK K d * (modK K g)⁻¹ ≤ 1 ↔ ∃ c ∈ pR hK, d = c * g := by
  constructor
  · intro h
    refine ⟨d * g⁻¹, ?_, (inv_mul_cancel_right₀ hg d).symm⟩
    show modK K (d * g⁻¹) ≤ 1
    rw [modK_mul, modK_inv hg]
    exact h
  · rintro ⟨c, hc, rfl⟩
    rw [modK_mul, mul_inv_cancel_right₀ (modK_pos_iff.2 hg).ne']
    exact hc

end ThmAux

@[kb "weil1973bnt" "Ch. II, §2, Thm. 2"]
theorem weil_II_2_thm2 (hK : IsPField K p) {L L' : AddSubgroup V} (hL : IsKLattice hK L)
    (hL' : IsKLattice hK L') {π : K} (hπ0 : π ≠ 0) (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K)) :
    ∃ (b : Module.Basis (Fin (Module.finrank K V)) K V) (ν : Fin (Module.finrank K V) → ℤ),
      (L : Set V) = {w | ∃ c : Fin (Module.finrank K V) → K, (∀ i, c i ∈ pR hK) ∧ w = ∑ i, c i • b i} ∧
      (L' : Set V) = {w | ∃ c : Fin (Module.finrank K V) → K, (∀ i, c i ∈ pR hK) ∧
        w = ∑ i, (c i * π ^ ν i) • b i} := by
  have hM := hL.1
  have hMo := hL.2.2
  have hM' := hL'.1
  have hMo' := hL'.2.2
  have hN := (isKNorm_latticeNorm_iff hK hM hMo).2 hL
  have hN' := (isKNorm_latticeNorm_iff hK hM' hMo').2 hL'
  obtain ⟨b, hb, hb'⟩ := weil_II_1_prop4 hK hN hN'
  have hpos : ∀ i, 0 < latticeNorm K L (b i) := fun i =>
    pos_iff_ne_zero.2 fun h => b.ne_zero i ((hN.eq_zero_iff _).1 h)
  choose y hy0 hyv hy using fun i => exists_attained hK hMo (hpos i)
  obtain ⟨b2, hb2⟩ := exists_rescaled_basis b y hy0
  have hsup2 : ∀ c : Fin (Module.finrank K V) → K, latticeNorm K L (∑ i, c i • b2 i) =
      Finset.univ.sup fun i => latticeNorm K L (c i • b2 i) := by
    simp only [hb2]; exact sup_rescale y hb
  have hsup2' : ∀ c : Fin (Module.finrank K V) → K, latticeNorm K L' (∑ i, c i • b2 i) =
      Finset.univ.sup fun i => latticeNorm K L' (c i • b2 i) := by
    simp only [hb2]; exact sup_rescale y hb'
  have hNb2 : ∀ i, latticeNorm K L (b2 i) = 1 := by
    intro i
    rw [hb2 i, latticeNorm_smul hK hM hMo, hy i]
    exact mul_inv_cancel₀ (modK_pos_iff.2 (hy0 i)).ne'
  have hpos' : ∀ i, 0 < latticeNorm K L' (b2 i) := fun i =>
    pos_iff_ne_zero.2 fun h => b2.ne_zero i ((hN'.eq_zero_iff _).1 h)
  choose z hz0 hzv hz using fun i => exists_attained hK hMo' (hpos' i)
  have hπmem : π ∈ pP hK := by
    rw [hπ]; exact ⟨1, (pR hK).one_mem, mul_one π⟩
  have hπ1 : modK K π < 1 := hπmem
  have hmax : ∀ x : K, modK K x < 1 → modK K x ≤ modK K π := by
    intro x hx
    have hx' : x ∈ pP hK := hx
    rw [hπ] at hx'
    obtain ⟨r, hr, rfl⟩ := hx'
    rw [modK_mul]
    calc modK K π * modK K r ≤ modK K π * 1 := mul_le_mul' le_rfl hr
      _ = modK K π := mul_one _
  choose ν hν using fun i => exists_zpow_of_gen hπ0 hπ1 hmax (hz0 i)
  have hN'b2 : ∀ i, latticeNorm K L' (b2 i) = (modK K (π ^ ν i))⁻¹ := fun i => by
    rw [hz i, hν i, modK_zpow hπ0]
  refine ⟨b2, ν, ?_, ?_⟩
  · ext w
    constructor
    · intro hw
      refine ⟨fun i => b2.repr w i, fun i => ?_, (b2.sum_repr w).symm⟩
      have h1 : ∑ i, b2.repr w i • b2 i ∈ L := by rw [b2.sum_repr]; exact hw
      have := (sum_mem_iff_forall hK hM hMo hsup2 (fun i => b2.repr w i)).1 h1 i
      rw [hNb2, mul_one] at this
      exact this
    · rintro ⟨c, hc, rfl⟩
      exact (sum_mem_iff_forall hK hM hMo hsup2 c).2 fun i => by rw [hNb2, mul_one]; exact hc i
  · ext w
    constructor
    · intro hw
      have h1' : ∑ i, b2.repr w i • b2 i ∈ L' := by rw [b2.sum_repr]; exact hw
      have h1 := (sum_mem_iff_forall hK hM' hMo' hsup2' (fun i => b2.repr w i)).1 h1'
      have h2 : ∀ i, ∃ c ∈ pR hK, b2.repr w i = c * π ^ ν i := fun i => by
        refine (coord_equiv hK (zpow_ne_zero _ hπ0) _).1 ?_
        have := h1 i
        rwa [hN'b2] at this
      choose c hc hcd using h2
      refine ⟨c, hc, ?_⟩
      conv_lhs => rw [← b2.sum_repr w]
      exact Finset.sum_congr rfl fun i _ => by rw [hcd i]
    · rintro ⟨c, hc, rfl⟩
      refine (sum_mem_iff_forall hK hM' hMo' hsup2' _).2 fun i => ?_
      rw [hN'b2]
      exact (coord_equiv hK (zpow_ne_zero _ hπ0) _).2 ⟨c i, hc i, rfl⟩

@[kb "weil1973bnt" "Ch. II, §2, Thm. 1"]
theorem weil_II_2_thm1 (hK : IsPField K p) {L : AddSubgroup V} (hL : IsKLattice hK L) :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      (L : Set V) = {w | ∃ c : Fin (Module.finrank K V) → K, (∀ i, c i ∈ pR hK) ∧ w = ∑ i, c i • b i} := by
  obtain ⟨π, hπ0, hP, _⟩ := weil_I_4_thm6_prime hK
  obtain ⟨b, ν, h1, _⟩ := weil_II_2_thm2 hK hL hL hπ0 hP
  exact ⟨b, h1⟩

end NumberFieldKB.WeilBNT.FieldModule

