import NumberFieldKB.WeilBNT.FieldModule
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Determinant

/-!
# Weil, *Basic Number Theory*, I.§2, Thm. 3 and Cor. 1–3: vector spaces over a locally compact field

$K$ is a nondiscrete locally compact division ring (`FieldModule`). $V$ is a topological left vector space over $K$:
`[Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [T2Space V]`.

* `weil_I_2_thm3`: Thm. 3. For linearly independent $v_1,\dots,v_n$ in $V$, the map $(x_i)\mapsto\sum_ix_iv_i$ is a
  closed embedding of $K^n$ into $V$ (an isomorphism of topological vector spaces onto its image $V'$, and $V'$ is
  closed in $V$).
* `weil_I_2_thm3_cor1`: Cor. 1. On a finite-dimensional space there is only one such topology: every $K$-linear
  bijection $K^n\to V$ is a homeomorphism.
* `weil_I_2_thm3_cor2_finiteDimensional`, `weil_I_2_thm3_cor2_mod`: Cor. 2. A locally compact $V$ is
  finite-dimensional, of dimension $d$ say, and $\operatorname{mod}_V(a)=\operatorname{mod}_K(a)^d$.
* `weil_I_2_text_p7`: text p. 7. A subspace of dimension $<n$ of $K^n$ has Haar measure $0$.
* `weil_I_2_thm3_cor3`: Cor. 3. For commutative $K$ and a $K$-linear map $A$ of $K^n$ into itself,
  $\mu(A(X))=\operatorname{mod}_K(\det A)\,\mu(X)$ for every Haar measure $\mu$ (with Weil's convention
  $\operatorname{mod}_V(A)=0$ when $A$ is not invertible).
-/

open MeasureTheory Topology Filter
open scoped Uniformity NNReal ENNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot]
  {V : Type*} [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul K V] [T2Space V]

/-- A nondiscrete locally compact division ring is `σ`-compact: it is the union of the compact sets
`{x : modK(x) ≤ n}` (Prop. 2). -/
instance sigmaCompactSpace_field : SigmaCompactSpace K :=
  ⟨⟨fun n : ℕ => {x : K | modK K x ≤ n}, fun n => isCompact_modK_le _, by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (modK K x)
    exact ⟨n, hn⟩⟩⟩

theorem isCountablyGenerated_nhds_zero_field : (𝓝 (0 : K)).IsCountablyGenerated := by
  have : (𝓝 (0 : K)).HasBasis (fun _ : ℕ => True)
      (fun n => {x : K | modK K x ≤ ((n : ℝ≥0) + 1)⁻¹}) := by
    refine hasBasis_nhds_zero_modK.to_hasBasis (fun m hm => ?_) (fun n _ => ?_)
    · obtain ⟨n, hn⟩ := exists_nat_gt (m⁻¹)
      have h : ((n : ℝ≥0) + 1)⁻¹ ≤ m :=
        (inv_le_comm₀ (by positivity) hm).2 (hn.le.trans le_self_add)
      exact ⟨n, trivial, fun x (hx : modK K x ≤ _) => (show modK K x ≤ m from hx.trans h)⟩
    · exact ⟨((n : ℝ≥0) + 1)⁻¹, by positivity, subset_rfl⟩
  exact this.isCountablyGenerated

/-- The topology of a nondiscrete locally compact division ring is pseudo-metrizable: it is a
first countable additive group (Cor. 1 of Prop. 2). -/
instance pseudoMetrizableSpace_field : TopologicalSpace.PseudoMetrizableSpace K := by
  have := isCountablyGenerated_nhds_zero_field (K := K)
  let _ : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have : (𝓤 K).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero K]
    exact Filter.comap.isCountablyGenerated _ _
  exact UniformSpace.pseudoMetrizableSpace

/-- A nondiscrete locally compact division ring is second countable (`σ`-compact and
pseudo-metrizable). -/
instance secondCountable_field : SecondCountableTopology K := by
  let _ := TopologicalSpace.pseudoMetrizableSpacePseudoMetric K
  exact EMetric.secondCountable_of_sigmaCompact K

variable (K) in
/-- The linear combination map `x ↦ ∑ xᵢ vᵢ` as a linear map. -/
def lcMap {n : ℕ} (v : Fin n → V) : (Fin n → K) →ₗ[K] V := Fintype.linearCombination K v

variable (K) in
theorem lcMap_apply {n : ℕ} (v : Fin n → V) (x : Fin n → K) : lcMap K v x = ∑ i, x i • v i := by
  simp [lcMap, Fintype.linearCombination_apply]

variable (K) in
theorem continuous_lcMap {n : ℕ} (v : Fin n → V) : Continuous (lcMap K v) := by
  have : (lcMap K v : (Fin n → K) → V) = fun x => ∑ i, x i • v i := funext (lcMap_apply K v)
  rw [this]
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i).smul continuous_const)

variable (K) in
/-- The compact "unit sphere" `{x : max modK(xᵢ) = 1}` of `Kⁿ`. -/
def unitSphere (n : ℕ) : Set (Fin n → K) :=
  {x | (∀ i, modK K (x i) ≤ 1) ∧ ∃ i, 1 ≤ modK K (x i)}

theorem isCompact_unitSphere (n : ℕ) : IsCompact (unitSphere K n) := by
  have h1 : IsClosed {x : Fin n → K | ∀ i, modK K (x i) ≤ 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_modK.comp (continuous_apply i)) continuous_const
  have h2 : IsClosed {x : Fin n → K | ∃ i, 1 ≤ modK K (x i)} := by
    simp only [Set.ofPred_exists]
    exact isClosed_iUnion_of_finite fun i =>
      isClosed_le continuous_const (continuous_modK.comp (continuous_apply i))
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin n => {x : K | modK K x ≤ 1}) :=
    isCompact_univ_pi fun _ => isCompact_modK_le 1
  refine hc.of_isClosed_subset (h1.inter h2) ?_
  intro x hx i _
  exact hx.1 i

/-- Local form of Thm. 3: a neighbourhood of `0` in `V` whose preimage lies in a small box. -/
theorem exists_nhds_lcMap {n : ℕ} {v : Fin n → V} (hv : LinearIndependent K v) {m : ℝ≥0}
    (hm : 0 < m) :
    ∃ N ∈ 𝓝 (0 : V), ∀ x : Fin n → K, lcMap K v x ∈ N → ∀ i, modK K (x i) ≤ m := by
  have hS : IsClosed (lcMap K v '' unitSphere K n) :=
    ((isCompact_unitSphere n).image (continuous_lcMap K v)).isClosed
  have h0 : (0 : V) ∉ lcMap K v '' unitSphere K n := by
    rintro ⟨x, ⟨_, i, hi⟩, hx⟩
    have hx' : ∑ j, x j • v j = 0 := by rw [← lcMap_apply]; exact hx
    have := Fintype.linearIndependent_iff.1 hv x hx' i
    rw [this] at hi
    simp at hi
  have hW1 : (lcMap K v '' unitSphere K n)ᶜ ∈ 𝓝 (0 : V) := hS.isOpen_compl.mem_nhds h0
  have hcont : ContinuousAt (fun p : K × V => p.1 • p.2) (0, 0) := continuous_smul.continuousAt
  have hev : ∀ᶠ p in 𝓝 ((0 : K), (0 : V)), p.1 • p.2 ∈ (lcMap K v '' unitSphere K n)ᶜ := by
    refine hcont.eventually_mem ?_
    show _ ∈ 𝓝 ((0 : K) • (0 : V))
    rw [smul_zero]; exact hW1
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hev
  obtain ⟨pK, hpK, pV, hpV, hp⟩ := hev
  obtain ⟨ε, hε, hεsub⟩ := hasBasis_nhds_zero_modK.mem_iff.1 hpK
  obtain ⟨a, ha, ham⟩ := exists_modK_pos_lt (K := K) (ε := ε * m) (by positivity)
  have ha0 : a ≠ 0 := modK_pos_iff.1 ha
  refine ⟨{y : V | pV (a⁻¹ • y)}, ?_, ?_⟩
  · have : Continuous fun y : V => a⁻¹ • y := continuous_const_smul _
    exact this.continuousAt.preimage_mem_nhds (by rw [smul_zero]; exact hpV)
  intro x hx i
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨h, -, hh⟩ := Finset.exists_max_image Finset.univ (fun i => modK K (x i))
    (⟨(Function.ne_iff.1 hx0).choose, Finset.mem_univ _⟩)
  have hxh : x h ≠ 0 := by
    intro h0'
    apply hx0
    funext j
    have := hh j (Finset.mem_univ _)
    rw [h0', modK_zero] at this
    exact modK_eq_zero_iff.1 (le_antisymm this zero_le)
  have hpos : 0 < modK K (x h) := modK_pos_iff.2 hxh
  set y : Fin n → K := (x h)⁻¹ • x with hy
  have hyS : y ∈ unitSphere K n := by
    refine ⟨fun j => ?_, h, ?_⟩
    · simp only [hy, Pi.smul_apply, smul_eq_mul, modK_mul, modK_inv hxh]
      rw [← div_eq_inv_mul]
      exact (div_le_one hpos).2 (hh j (Finset.mem_univ _))
    · simp only [hy, Pi.smul_apply, smul_eq_mul, modK_mul, modK_inv hxh]
      exact (inv_mul_cancel₀ hpos.ne').ge
  have hly : lcMap K v y = (x h)⁻¹ • lcMap K v x := by
    simp [hy]
  have hmem : (x h)⁻¹ • lcMap K v x ∈ lcMap K v '' unitSphere K n := ⟨y, hyS, hly⟩
  have hmod : ε < modK K ((x h)⁻¹ * a) := by
    by_contra hle
    rw [not_lt] at hle
    have e : ((x h)⁻¹ * a) • (a⁻¹ • lcMap K v x) = (x h)⁻¹ • lcMap K v x := by
      rw [smul_smul, mul_inv_cancel_right₀ ha0]
    have := hp (hεsub hle) (show pV (a⁻¹ • lcMap K v x) from hx)
    rw [e] at this
    exact this hmem
  rw [modK_mul, modK_inv hxh, lt_inv_mul_iff₀ hpos] at hmod
  have h2 : ε * modK K (x h) < ε * m := by rw [mul_comm]; exact hmod.trans ham
  have h3 : modK K (x h) < m := lt_of_mul_lt_mul_left h2 zero_le
  exact (hh i (Finset.mem_univ _)).trans h3.le

theorem isInducing_lcMap {n : ℕ} {v : Fin n → V} (hv : LinearIndependent K v) :
    IsInducing (lcMap K v) := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm (tendsto_iff_comap.1 ?_) ?_
  · simpa using (continuous_lcMap K v).tendsto 0
  · intro U hU
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hIU⟩ := hU
    have h1 : ∀ i, ∃ N ∈ 𝓝 (0 : V), ∀ x, lcMap K v x ∈ N → x i ∈ t i := by
      intro i
      obtain ⟨m, hm, hsub⟩ :=
        hasBasis_nhds_zero_modK.mem_iff.1 (by simpa using ht i : t i ∈ 𝓝 (0 : K))
      obtain ⟨N, hN, hNx⟩ := exists_nhds_lcMap hv hm
      exact ⟨N, hN, fun x hx => hsub (hNx x hx i)⟩
    choose N hN hNx using h1
    refine Filter.mem_comap.2 ⟨⋂ i, N i, Filter.iInter_mem.2 hN, fun x hx => hIU fun i _ => ?_⟩
    exact hNx i x (Set.mem_iInter.1 (Set.mem_preimage.1 hx) i)

@[kb "weil1973bnt" "Ch. I, §2, Thm. 3"]
theorem weil_I_2_thm3 {n : ℕ} (v : Fin n → V) (hv : LinearIndependent K v) :
    IsClosedEmbedding (fun x : Fin n → K => ∑ i, x i • v i) := by
  have hf : (fun x : Fin n → K => ∑ i, x i • v i) = lcMap K v :=
    funext fun x => (lcMap_apply K v x).symm
  rw [hf]
  have hinj : Function.Injective (lcMap K v) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    funext i
    exact Fintype.linearIndependent_iff.1 hv x (by rwa [← lcMap_apply]) i
  refine ⟨⟨isInducing_lcMap hv, hinj⟩, ?_⟩
  refine isClosed_of_closure_subset fun w hw => ?_
  by_contra hwn
  have hli : LinearIndependent K (Fin.cons w v : Fin (n + 1) → V) := by
    refine linearIndependent_finCons.2 ⟨hv, fun hmem => hwn ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    exact ⟨c, by rw [lcMap_apply]; exact hc⟩
  have hgind := isInducing_lcMap hli
  set g := lcMap K (Fin.cons w v : Fin (n + 1) → V) with hg
  set S : Set (Fin (n + 1) → K) := {x | x 0 = 0} with hS
  have hSc : IsClosed S := isClosed_eq (continuous_apply 0) continuous_const
  have hsub : Set.range (lcMap K v) ⊆ g '' S := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(Fin.cons 0 x : Fin (n + 1) → K), by simp [hS], ?_⟩
    simp [hg, lcMap_apply, Fin.sum_univ_succ]
  have hw' : w ∈ closure (g '' S) := closure_mono hsub hw
  have hgw : g (Pi.single 0 1) = w := by
    simp [hg, lcMap_apply, Pi.single_apply]
  have : (Pi.single 0 1 : Fin (n + 1) → K) ∈ closure S := by
    rw [hgind.closure_eq_preimage_closure_image]
    rw [Set.mem_preimage, hgw]; exact hw'
  rw [hSc.closure_eq] at this
  simp [hS] at this

/-- A finite-dimensional subspace of `V` is closed (Thm. 3). -/
theorem isClosed_of_finiteDimensional (W : Submodule K V) [FiniteDimensional K W] :
    IsClosed (W : Set V) := by
  set b := Module.finBasis K W with hb
  set v : Fin (Module.finrank K W) → V := fun i => (b i : V) with hvdef
  have hli : LinearIndependent K v := b.linearIndependent.map' W.subtype W.ker_subtype
  have hcl := (weil_I_2_thm3 v hli).isClosed_range
  have : Set.range (fun x : Fin (Module.finrank K W) → K => ∑ i, x i • v i) = W := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact W.sum_mem fun i _ => W.smul_mem _ (b i).2
    · intro hw
      refine ⟨b.repr ⟨w, hw⟩, ?_⟩
      have h1 := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
      simp only [map_sum, map_smul, Submodule.subtype_apply] at h1
      exact h1
  rwa [this] at hcl

@[kb "weil1973bnt" "Ch. I, §2, Cor. 1 of Thm. 3"]
theorem weil_I_2_thm3_cor1 {n : ℕ} (e : (Fin n → K) ≃ₗ[K] V) : IsHomeomorph e := by
  set v : Fin n → V := fun i => e (Pi.single i 1) with hvdef
  have hli : LinearIndependent K v := by
    have := (Pi.basisFun K (Fin n)).linearIndependent.map' e.toLinearMap
      (LinearMap.ker_eq_bot.2 e.injective)
    convert this using 1
    funext i
    simp [hvdef]
  have hf : (fun x : Fin n → K => ∑ i, x i • v i) = e := by
    funext x
    have h1 : ∑ i, x i • (Pi.single i (1 : K) : Fin n → K) = x := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    calc ∑ i, x i • v i = e (∑ i, x i • (Pi.single i (1 : K) : Fin n → K)) := by
          simp [hvdef, map_sum]
      _ = e x := by rw [h1]
  have := weil_I_2_thm3 v hli
  rw [hf] at this
  exact isHomeomorph_iff_isEmbedding_surjective.2 ⟨this.isEmbedding, e.surjective⟩

@[kb "weil1973bnt" "Ch. I, §2, Cor. 2 of Thm. 3 (finite dimension)"]
theorem weil_I_2_thm3_cor2_finiteDimensional [LocallyCompactSpace V] : FiniteDimensional K V := by
  obtain ⟨C, hCc, hC0⟩ := exists_compact_mem_nhds (0 : V)
  obtain ⟨a, ha, ha1⟩ := exists_modK_pos_lt (K := K) (ε := 1) one_pos
  have ha0 : a ≠ 0 := modK_pos_iff.1 ha
  have hlim : Tendsto (fun k : ℕ => a ^ k) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_iff_modK a).2 ha1
  have haC : a • C ∈ 𝓝 (0 : V) := by
    have h1 : (fun x : V => a⁻¹ • x) ⁻¹' C ∈ 𝓝 (0 : V) :=
      (continuous_const_smul a⁻¹).continuousAt.preimage_mem_nhds (by rw [smul_zero]; exact hC0)
    exact Filter.mem_of_superset h1 fun x hx => ⟨a⁻¹ • x, hx, smul_inv_smul₀ ha0 x⟩
  obtain ⟨t, -, hcov⟩ := hCc.elim_nhds_subcover (fun x => (fun y => y - x) ⁻¹' (a • C))
    (fun x _ => (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by show a • C ∈ 𝓝 (x - x); rw [sub_self]; exact haC))
  set W : Submodule K V := Submodule.span K (t : Set V) with hW
  have : FiniteDimensional K W := FiniteDimensional.span_finset K t
  have hWcl : IsClosed (W : Set V) := isClosed_of_finiteDimensional W
  have step : ∀ k : ℕ, ∀ y ∈ C, ∃ w ∈ W, ∃ c ∈ C, y = w + a ^ k • c := by
    intro k
    induction k with
    | zero => exact fun y hy => ⟨0, W.zero_mem, y, hy, by simp⟩
    | succ k ih =>
      intro y hy
      obtain ⟨w, hw, c, hc, rfl⟩ := ih y hy
      obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.1 (hcov hc)
      obtain ⟨c', hc', hcc⟩ := hx
      refine ⟨w + a ^ k • x, W.add_mem hw (W.smul_mem _ (Submodule.subset_span hxt)), c', hc', ?_⟩
      have : c = x + a • c' := by
        have h := hcc
        simp only at h
        rw [h]; abel
      rw [this, smul_add, smul_smul, ← pow_succ]
      abel
  have hCW : ∀ y ∈ C, y ∈ W := by
    intro y hy
    have : y ∈ closure (W : Set V) := by
      rw [mem_closure_iff_nhds]
      intro N hN
      have hN1 : (fun z : V => y - z) ⁻¹' N ∈ 𝓝 (0 : V) :=
        (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
          (by simpa using hN)
      have ev : ∀ᶠ r in 𝓝 (0 : K), ∀ c ∈ C, r • c ∈ (fun z : V => y - z) ⁻¹' N :=
        hCc.eventually_forall_of_forall_eventually fun c _ =>
          (continuous_smul.tendsto ((0 : K), c)).eventually (by simpa using (show ∀ᶠ z in 𝓝 (0 : V), z ∈ (fun z : V => y - z) ⁻¹' N from hN1))
      obtain ⟨k, hk⟩ := (hlim.eventually ev).exists
      obtain ⟨w, hw, c, hc, rfl⟩ := step k y hy
      exact ⟨w, by simpa using hk c hc, hw⟩
    rwa [hWcl.closure_eq] at this
  have hall : ∀ v : V, v ∈ W := by
    intro v
    obtain ⟨k, hk⟩ := ((hlim.smul_const v).eventually_mem (by rw [zero_smul]; exact hC0)).exists
    have := W.smul_mem (a ^ k)⁻¹ (hCW _ hk)
    rwa [inv_smul_smul₀ (pow_ne_zero k ha0)] at this
  exact Module.finite_def.2 ⟨t, eq_top_iff.2 fun v _ => hall v⟩

@[kb "weil1973bnt" "Ch. I, §2, Cor. 2 of Thm. 3 (the module)"]
theorem weil_I_2_thm3_cor2_mod [LocallyCompactSpace V] (a : Kˣ) :
    distribHaarChar V a = modK K (a : K) ^ Module.finrank K V := by
  have : FiniteDimensional K V := weil_I_2_thm3_cor2_finiteDimensional
  set d := Module.finrank K V with hd
  let e : (Fin d → K) ≃ₗ[K] V := (Module.finBasis K V).equivFun.symm
  have he : IsHomeomorph e := weil_I_2_thm3_cor1 e
  let h : (Fin d → K) ≃ₜ V := he.homeomorph
  borelize K V
  let α : Measure K := Measure.addHaar
  let μ0 : Measure (Fin d → K) := Measure.pi fun _ => α
  have : μ0.IsAddHaarMeasure := inferInstance
  let ν : Measure V := Measure.map h μ0
  have hs : ∀ y, h.symm y = e.symm y := fun y => by
    rw [Homeomorph.symm_apply_eq]; exact (e.apply_symm_apply y).symm
  have hcs : Continuous (e.toAddEquiv.symm : V → (Fin d → K)) := by
    have : (e.toAddEquiv.symm : V → (Fin d → K)) = h.symm := funext fun y => (hs y).symm
    rw [this]; exact h.symm.continuous
  have hν : ν.IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map μ0 e.toAddEquiv h.continuous hcs
  have hνr : ν.Regular := Measure.Regular.map h
  have hsm : ∀ t : Set (Fin d → K), ν (h '' t) = μ0 t := by
    intro t
    have := (h.toMeasurableEquiv).map_apply (μ := μ0) (h '' t)
    simpa [ν, Homeomorph.preimage_image] using this
  obtain ⟨X, hXc, hX0⟩ := exists_compact_mem_nhds (0 : K)
  have hXpos : α X ≠ 0 := (Measure.measure_pos_of_mem_nhds α hX0).ne'
  have hXtop : α X ≠ ∞ := hXc.measure_lt_top.ne
  set box : Set (Fin d → K) := Set.pi Set.univ fun _ => X with hbox
  have hμbox : μ0 box = (α X) ^ d := by
    rw [hbox, Measure.pi_pi]
    simp
  have hsmul : a • box = Set.pi Set.univ fun _ => (a : K) • X := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [hbox, Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply]
    refine forall_congr' fun i => ?_
    rw [Units.smul_def, Set.mem_smul_set_iff_inv_smul_mem₀ a.ne_zero]
    simp
  have hμsmul : μ0 (a • box) = (modK K (a : K) : ℝ≥0∞) ^ d * μ0 box := by
    rw [hsmul, Measure.pi_pi, hμbox]
    simp only [← modK_mul_measure α a.ne_zero X, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [mul_pow]
  have hcomm : ∀ x, h (a • x) = a • h x := fun x => by
    show e _ = _
    rw [Units.smul_def, Units.smul_def]
    exact map_smul e _ _
  have himg : a • (h '' box) = h '' (a • box) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a • x, Set.smul_mem_smul_set hx, hcomm x⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨h x, ⟨x, hx, rfl⟩, (hcomm x).symm⟩
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν) (s := h '' box) ?_ ?_ ?_
  · rw [hsm, hμbox]; exact pow_ne_zero _ hXpos
  · rw [hsm, hμbox]; exact ENNReal.pow_ne_top hXtop
  · rw [himg, hsm, hsm, hμsmul]
    push_cast
    rfl

@[kb "weil1973bnt" "Ch. I, §2, text p. 7 (proper subspaces have measure 0)"]
theorem weil_I_2_text_p7 {n : ℕ} [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] (W : Submodule K (Fin n → K))
    (hW : Module.finrank K W < n) : μ W = 0 := by
  have hWcl : IsClosed (W : Set (Fin n → K)) := isClosed_of_finiteDimensional W
  have hWm : MeasurableSet (W : Set (Fin n → K)) := hWcl.measurableSet
  obtain ⟨u, hu⟩ : ∃ u : Fin n → K, u ∉ W := by
    by_contra hcon
    push Not at hcon
    have : W = ⊤ := eq_top_iff.2 fun x _ => hcon x
    rw [this] at hW
    simp at hW
  have key : ∀ C : Set (Fin n → K), IsCompact C → μ (W ∩ C) = 0 := by
    intro C hC
    by_contra hc
    have hinf : ({t : K | modK K t ≤ 1}).Infinite :=
      infinite_of_mem_nhds (0 : K) (hasBasis_nhds_zero_modK.mem_of_mem one_pos)
    let t : ℕ → K := fun k => (hinf.natEmbedding _ k : K)
    have ht_inj : Function.Injective t := fun j k hjk =>
      (hinf.natEmbedding _).injective (Subtype.ext hjk)
    have ht_mem : ∀ k, modK K (t k) ≤ 1 := fun k => (hinf.natEmbedding _ k).2
    let A : ℕ → Set (Fin n → K) := fun k => (fun x => x + -(t k • u)) ⁻¹' (W ∩ C)
    have hAm : ∀ k, MeasurableSet (A k) := fun k =>
      (continuous_add_const (-(t k • u))).measurable
        (hWm.inter hC.isClosed.measurableSet)
    have hAμ : ∀ k, μ (A k) = μ (W ∩ C) := fun k => measure_preimage_add_right μ _ _
    have hdisj : Pairwise (Function.onFun Disjoint A) := by
      intro j k hjk
      rw [Function.onFun, Set.disjoint_left]
      intro x hxj hxk
      have h1 : x + -(t j • u) ∈ W := hxj.1
      have h2 : x + -(t k • u) ∈ W := hxk.1
      have h3 : (t k - t j) • u ∈ W := by
        have := W.sub_mem h1 h2
        convert this using 1
        rw [sub_smul]
        abel
      have hne : t k - t j ≠ 0 := sub_ne_zero.2 (fun h => hjk (ht_inj h.symm))
      apply hu
      have := W.smul_mem (t k - t j)⁻¹ h3
      rwa [inv_smul_smul₀ hne] at this
    have hD : IsCompact ((fun p : (Fin n → K) × K => p.1 + p.2 • u) ''
        (C ×ˢ {s : K | modK K s ≤ 1})) :=
      (hC.prod (isCompact_modK_le 1)).image
        (continuous_fst.add (continuous_snd.smul continuous_const))
    have hsub : (⋃ k, A k) ⊆ (fun p : (Fin n → K) × K => p.1 + p.2 • u) ''
        (C ×ˢ {s : K | modK K s ≤ 1}) := by
      intro x hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
      exact ⟨(x + -(t k • u), t k), ⟨hk.2, ht_mem k⟩, by simp⟩
    have h1 := measure_mono (μ := μ) hsub
    rw [measure_iUnion hdisj hAm] at h1
    simp only [hAμ] at h1
    rw [ENNReal.tsum_const_eq_top_of_ne_zero hc] at h1
    exact absurd (top_le_iff.1 h1) hD.measure_lt_top.ne
  have hcov : (W : Set (Fin n → K)) ⊆
      ⋃ m : ℕ, W ∩ Set.pi Set.univ fun _ : Fin n => {x : K | modK K x ≤ m} := by
    intro x hx
    obtain ⟨m, hm⟩ := exists_nat_ge (Finset.univ.sup fun i => modK K (x i))
    refine Set.mem_iUnion.2 ⟨m, hx, fun i _ => ?_⟩
    exact (Finset.le_sup (f := fun i => modK K (x i)) (Finset.mem_univ i)).trans hm
  refine measure_mono_null hcov (measure_iUnion_null fun m => key _ ?_)
  exact isCompact_univ_pi fun _ => isCompact_modK_le _

section Cor3

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot]

open Matrix in
/-- A transvection preserves the product of Haar measures on `Fⁿ` (Fubini; the shear acts as a
translation in one coordinate). -/
theorem measurePreserving_transvectionStruct [MeasurableSpace F] [BorelSpace F] (α : Measure F)
    [α.IsAddHaarMeasure] {n : ℕ} (t : TransvectionStruct (Fin n) F) :
    MeasurePreserving (toLin' t.toMatrix) (Measure.pi fun _ => α) (Measure.pi fun _ => α) := by
  have ht : Measurable (toLin' t.toMatrix) :=
    (LinearMap.continuous_on_pi (toLin' t.toMatrix)).measurable
  refine ⟨ht, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, single_mulVec, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x t_i xᵢ)]

theorem modK_prod {ι : Type*} (s : Finset ι) (f : ι → F) :
    modK F (∏ i ∈ s, f i) = ∏ i ∈ s, modK F (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, modK_mul, ih]

/-- Every linear equivalence of `Fⁿ` acts by a continuous map. -/
instance continuousConstSMul_linearEquiv {n : ℕ} :
    ContinuousConstSMul ((Fin n → F) ≃ₗ[F] (Fin n → F)) (Fin n → F) :=
  ⟨fun g => LinearMap.continuous_on_pi (g : (Fin n → F) →ₗ[F] (Fin n → F))⟩

/-- A linear automorphism fixing the product Haar measure has distributive Haar character `1`. -/
theorem distribHaarChar_eq_one_of_measurePreserving [MeasurableSpace F] [BorelSpace F]
    (α : Measure F) [α.IsAddHaarMeasure] {n : ℕ} (g : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (hg : MeasurePreserving g (Measure.pi fun _ => α) (Measure.pi fun _ => α)) :
    distribHaarChar (Fin n → F) g = 1 := by
  let μ0 : Measure (Fin n → F) := Measure.pi fun _ => α
  have : μ0.IsAddHaarMeasure := inferInstance
  obtain ⟨X, hXc, hX0⟩ := exists_compact_mem_nhds (0 : F)
  have hXpos : α X ≠ 0 := (Measure.measure_pos_of_mem_nhds α hX0).ne'
  have hXtop : α X ≠ ∞ := hXc.measure_lt_top.ne
  set box : Set (Fin n → F) := Set.pi Set.univ fun _ => X with hbox
  have hμbox : μ0 box = (α X) ^ n := by
    rw [hbox, Measure.pi_pi]
    simp
  have hbm : MeasurableSet box := MeasurableSet.univ_pi fun _ => hXc.isClosed.measurableSet
  have hpre : g⁻¹ • box = (g : (Fin n → F) → (Fin n → F)) ⁻¹' box := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    rfl
  have h1 : distribHaarChar (Fin n → F) g⁻¹ = 1 := by
    refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ0) (s := box) ?_ ?_ ?_
    · rw [hμbox]; exact pow_ne_zero _ hXpos
    · rw [hμbox]; exact ENNReal.pow_ne_top hXtop
    · rw [hpre, hg.measure_preimage hbm.nullMeasurableSet]
      simp only [ENNReal.coe_one, one_mul]
      rfl
  have h2 := map_mul (distribHaarChar (Fin n → F)) g g⁻¹
  rw [mul_inv_cancel, map_one, h1, mul_one] at h2
  exact h2.symm

/-- The distributive Haar character of a diagonal linear automorphism of `Fⁿ`. -/
theorem distribHaarChar_diag {n : ℕ} (g : (Fin n → F) ≃ₗ[F] (Fin n → F)) (d : Fin n → F)
    (hd : ∀ i, d i ≠ 0) (hg : ∀ x i, g x i = d i * x i) :
    distribHaarChar (Fin n → F) g = ∏ i, modK F (d i) := by
  borelize F
  let α : Measure F := Measure.addHaar
  let μ0 : Measure (Fin n → F) := Measure.pi fun _ => α
  have : μ0.IsAddHaarMeasure := inferInstance
  obtain ⟨X, hXc, hX0⟩ := exists_compact_mem_nhds (0 : F)
  have hXpos : α X ≠ 0 := (Measure.measure_pos_of_mem_nhds α hX0).ne'
  have hXtop : α X ≠ ∞ := hXc.measure_lt_top.ne
  set box : Set (Fin n → F) := Set.pi Set.univ fun _ => X with hbox
  have hμbox : μ0 box = (α X) ^ n := by
    rw [hbox, Measure.pi_pi]
    simp
  have himg : g • box = Set.pi Set.univ fun i => d i • X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ i _
      refine ⟨x i, hx i (Set.mem_univ i), ?_⟩
      show d i • x i = g x i
      rw [hg]; rfl
    · intro hy
      choose x hxX hxy using fun i => Set.mem_smul_set.1 (hy i (Set.mem_univ i))
      refine ⟨x, fun i _ => hxX i, ?_⟩
      funext i
      show g (x) i = y i
      rw [hg]
      exact hxy i
  have hμg : μ0 (g • box) = ((∏ i, modK F (d i) : ℝ≥0) : ℝ≥0∞) * μ0 box := by
    rw [himg, Measure.pi_pi, hμbox]
    simp only [← modK_mul_measure α (hd _) X]
    rw [Finset.prod_mul_distrib, ENNReal.ofNNReal_finsetProd]
    simp
  exact distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ0) (s := box)
    (by rw [hμbox]; exact pow_ne_zero _ hXpos) (by rw [hμbox]; exact ENNReal.pow_ne_top hXtop) hμg

variable {n : ℕ}

/-- The linear automorphism of `Fⁿ` given by a matrix with nonzero determinant. -/
def geq (M : Matrix (Fin n) (Fin n) F) (hM : M.det ≠ 0) : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
  LinearMap.equivOfDetNeZero (Matrix.toLin' M) (by rwa [LinearMap.det_toLin'])

theorem geq_apply (M : Matrix (Fin n) (Fin n) F) (hM : M.det ≠ 0) (x : Fin n → F) :
    geq M hM x = M.mulVec x := by
  simp [geq]

theorem geq_mul (A B : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (hAB : (A * B).det ≠ 0) : geq (A * B) hAB = geq A hA * geq B hB := by
  ext x : 1
  simp [geq_apply, Matrix.mulVec_mulVec]

/-- The distributive Haar character of the linear automorphism given by a matrix is the module of
its determinant. -/
theorem distribHaarChar_geq (M : Matrix (Fin n) (Fin n) F) (hM : M.det ≠ 0) :
    distribHaarChar (Fin n → F) (geq M hM) = modK F M.det := by
  classical
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ hM : M.det ≠ 0, distribHaarChar (Fin n → F) (geq M hM) = modK F M.det) M hM
    ?_ ?_ ?_ hM
  · intro D hD h
    have hDi : ∀ i, D i ≠ 0 := fun i =>
      Finset.prod_ne_zero_iff.1 (by simpa [Matrix.det_diagonal] using hD) i (Finset.mem_univ i)
    rw [distribHaarChar_diag (geq _ h) D hDi
      (fun x i => by rw [geq_apply, Matrix.mulVec_diagonal]), Matrix.det_diagonal, modK_prod]
  · intro t h
    rw [Matrix.TransvectionStruct.det, modK_one]
    borelize F
    refine distribHaarChar_eq_one_of_measurePreserving Measure.addHaar _ ?_
    have hfun : ⇑(geq t.toMatrix h) = ⇑(Matrix.toLin' t.toMatrix) := by
      funext x
      rw [geq_apply, Matrix.toLin'_apply]
    rw [hfun]
    exact measurePreserving_transvectionStruct _ t
  · intro A B hA hB PA PB h
    rw [geq_mul A B hA hB h, map_mul, PA hA, PB hB, Matrix.det_mul, modK_mul]

end Cor3

@[kb "weil1973bnt" "Ch. I, §2, Cor. 3 of Thm. 3"]
theorem weil_I_2_thm3_cor3 {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] {n : ℕ}
    [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)] (μ : Measure (Fin n → F)) [μ.IsAddHaarMeasure]
    [μ.Regular] (A : (Fin n → F) →ₗ[F] (Fin n → F)) (s : Set (Fin n → F)) :
    μ (A '' s) = modK F (LinearMap.det A) * μ s := by
  classical
  by_cases hdet : LinearMap.det A = 0
  · rw [hdet, modK_zero]
    have hlt : Module.finrank F (LinearMap.range A) < n := by
      have hker : LinearMap.ker A ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.1 hdet
      have h1 := LinearMap.finrank_range_add_finrank_ker A
      have h2 : 1 ≤ Module.finrank F (LinearMap.ker A) := Submodule.one_le_finrank_iff.2 hker
      rw [Module.finrank_fin_fun] at h1
      omega
    have := measure_mono_null (Set.image_subset_range A s) (weil_I_2_text_p7 μ (LinearMap.range A) hlt)
    simp [this]
  · set M := LinearMap.toMatrix' A with hMdef
    have hdetM : M.det = LinearMap.det A := LinearMap.det_toMatrix' A
    have hM : M.det ≠ 0 := by rw [hdetM]; exact hdet
    have himg : A '' s = geq M hM • s := by
      rw [← Set.image_smul]
      refine Set.image_congr fun x _ => ?_
      show A x = geq M hM x
      rw [geq_apply, ← Matrix.toLin'_apply, hMdef, Matrix.toLin'_toMatrix']
    rw [himg, ← distribHaarChar_mul μ (geq M hM) s, distribHaarChar_geq, hdetM]

end NumberFieldKB.WeilBNT.FieldModule
