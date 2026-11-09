import NumberFieldKB.MilneCFT.Ch5Remark48Corrected
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Approximation.Weak

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 4.8: the extension of an admissible homomorphism ($G$ complete Hausdorff)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Remark 4.8, p. 174.
See `Ch5Remark48Corrected.lean` for the statement `Remark4_8Corrected` and the proof outline.
-/

open NumberField IsDedekindDomain Topology
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-- A homomorphism from a dense subgroup of a commutative topological group to a complete Hausdorff commutative
uniform group, continuous at `1`, extends to a continuous homomorphism. -/
theorem exists_extend_of_dense {I : Type*} [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I]
    {G : Type*} [CommGroup G] [UniformSpace G] [IsUniformGroup G] [CompleteSpace G] [T2Space G]
    (H : Subgroup I) (hH : Dense (H : Set I)) (φ0 : H →* G)
    (hc : ∀ N ∈ 𝓝 (1 : G), ∃ U ∈ 𝓝 (1 : I), ∀ h : H, (h : I) ∈ U → φ0 h ∈ N) :
    ∃ φ : I →* G, Continuous φ ∧ ∀ h : H, φ h = φ0 h := by
  let _ : UniformSpace I := IsTopologicalGroup.rightUniformSpace I
  have : IsUniformGroup I := isUniformGroup_of_commGroup
  have hcont : ContinuousAt φ0 1 := by
    intro N hN
    rw [map_one] at hN
    obtain ⟨U, hU, hUN⟩ := hc N hN
    refine Filter.mem_map.2 ?_
    rw [nhds_subtype_eq_comap]
    refine Filter.mem_comap.2 ⟨U, ?_, fun h hh => hUN h hh⟩
    simpa using hU
  have huc : UniformContinuous φ0 := uniformContinuous_of_continuousAt_one φ0 hcont
  set ψ : I → G := hH.extend φ0 with hψ
  have hψc : Continuous ψ := (hH.uniformContinuous_extend huc).continuous
  have hψe : ∀ h : H, ψ h = φ0 h := fun h => hH.extend_eq huc.continuous h
  have hmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    refine hH.denseRange_val.induction_on₂ (p := fun x y => ψ (x * y) = ψ x * ψ y) ?_ ?_ x y
    · exact isClosed_eq (hψc.comp (continuous_fst.mul continuous_snd))
        ((hψc.comp continuous_fst).mul (hψc.comp continuous_snd))
    · intro a b
      show ψ (((a * b : H)) : I) = ψ a * ψ b
      rw [hψe (a * b), hψe a, hψe b, map_mul]
  exact ⟨MonoidHom.mk' ψ hmul, hψc, hψe⟩

/-- A principal idèle is determined by its component at any infinite place. -/
theorem unitEmbedding_eq_of_infAt {a a' : Kˣ} (w : InfinitePlace K)
    (h : ideleInfAt (IdeleGroup.unitEmbedding (𝓞 K) K a) w = ideleInfAt (IdeleGroup.unitEmbedding (𝓞 K) K a') w) :
    a = a' := by
  have h' : algebraMap K w.Completion (a : K) = algebraMap K w.Completion (a' : K) := by
    simpa [InfinitePlace.Completion.algebraMap_apply, ideleInfAt_unitEmbedding] using h
  exact Units.ext ((algebraMap K w.Completion).injective h')

/-- Decompositions `a * x` (`a ∈ K^×`, `x ∈ I_S`) are unique. -/
theorem unitEmbedding_mul_unique (S : Set (HeightOneSpectrum (𝓞 K))) {a a' : Kˣ}
    {x x' : IdeleGroup (𝓞 K) K} (hx : x ∈ idelesTrivialAt S) (hx' : x' ∈ idelesTrivialAt S)
    (h : IdeleGroup.unitEmbedding (𝓞 K) K a * x = IdeleGroup.unitEmbedding (𝓞 K) K a' * x') :
    a = a' ∧ x = x' := by
  have ha : a = a' := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    refine unitEmbedding_eq_of_infAt w ?_
    have := congrArg (fun y => ideleInfAt y w) h
    simpa only [ideleInfAt_mul, hx.1 w, hx'.1 w, mul_one] using this
  subst ha
  exact ⟨rfl, mul_left_cancel h⟩

/-- The subgroup `K^× · I_S` of the idèles. -/
def kIS (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K) :=
  (IdeleGroup.unitEmbedding (𝓞 K) K).range ⊔ idelesTrivialAt S

theorem mem_kIS {S : Set (HeightOneSpectrum (𝓞 K))} {y : IdeleGroup (𝓞 K) K} :
    y ∈ kIS S ↔ ∃ a : Kˣ, ∃ x ∈ idelesTrivialAt S, IdeleGroup.unitEmbedding (𝓞 K) K a * x = y := by
  unfold kIS
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, x, hx, rfl⟩
    exact ⟨a, x, hx, rfl⟩
  · rintro ⟨a, x, hx, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, x, hx, rfl⟩

/-- Neighbourhoods of `1` in the idèle group, with arbitrary (small) components at the infinite places: a box
condition on the infinite components of `y` and `y⁻¹`, closeness to `1` at finitely many finite places and units
elsewhere. -/
theorem idele_nhds_one' {U : Set (IdeleGroup (𝓞 K) K)} (hU : U ∈ 𝓝 (1 : IdeleGroup (𝓞 K) K)) :
    ∃ (O : ∀ w : InfinitePlace K, Set w.Completion) (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ),
      (∀ w, O w ∈ 𝓝 (1 : w.Completion)) ∧ ∀ y : IdeleGroup (𝓞 K) K,
      (∀ w, ideleInfAt y w ∈ O w) → (∀ w, ideleInfAt y⁻¹ w ∈ O w) →
      (∀ v ∈ T, Valued.v (ideleFinAt y v - 1) ≤ WithZero.exp (-(n : ℤ))) →
      (∀ v ∉ T, Valued.v (ideleFinAt y v) = 1) → y ∈ U := by
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [show Units.embedProduct (AdeleRing (𝓞 K) K) 1 =
      ((1 : AdeleRing (𝓞 K) K), MulOpposite.op (1 : AdeleRing (𝓞 K) K)) from rfl, nhds_prod_eq] at hV
  obtain ⟨V1, hV1, V2, hV2, hV12⟩ := Filter.mem_prod_iff.mp hV
  have hV2' : MulOpposite.op ⁻¹' V2 ∈ 𝓝 (1 : AdeleRing (𝓞 K) K) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using hV2)
  have hW := Filter.inter_mem hV1 hV2'
  rw [show (1 : AdeleRing (𝓞 K) K) = ((1 : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K)) from rfl,
    nhds_prod_eq] at hW
  obtain ⟨N1, hN1, N2, hN2, hN12⟩ := Filter.mem_prod_iff.mp hW
  obtain ⟨T, n, hTn⟩ := finiteAdele_nhds_one hN2
  have hN1' : N1 ∈ Filter.pi (fun w : InfinitePlace K => 𝓝 (1 : w.Completion)) := by
    rw [← nhds_pi]; exact hN1
  rw [Filter.mem_pi'] at hN1'
  obtain ⟨I, t, ht, hIt⟩ := hN1'
  refine ⟨t, T, n + 1, ht, fun y hy1 hy1' hy2 hy3 => ?_⟩
  have hlt : WithZero.exp (-((n + 1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hle : WithZero.exp (-((n + 1 : ℕ) : ℤ)) ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.exp_le_exp]; omega
  have h1 : (y : AdeleRing (𝓞 K) K).1 ∈ N1 := hIt (fun w _ => hy1 w)
  have h1' : ((y⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 ∈ N1 := hIt (fun w _ => hy1' w)
  have hf : (y : AdeleRing (𝓞 K) K).2 ∈ N2 := by
    refine hTn _ (fun v hv => (hy2 v hv).trans hle) (fun v hv => ?_)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (hy3 v hv).le
  have hg : ((y⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 ∈ N2 := by
    refine hTn _ (fun v hv => ?_) (fun v hv => ?_)
    · have h := val_inv_sub_one_le Valued.v hlt (hy2 v hv)
      have e := ideleFinAt_inv y v
      change Valued.v (ideleFinAt y⁻¹ v - 1) ≤ _
      rw [e]
      exact h.trans hle
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (ideleFinAt y⁻¹ v) ≤ 1
      rw [ideleFinAt_inv, map_inv₀, hy3 v hv, inv_one]
  apply hVU
  have e1 := hN12 (show ((y : AdeleRing (𝓞 K) K).1, (y : AdeleRing (𝓞 K) K).2) ∈ N1 ×ˢ N2 from ⟨h1, hf⟩)
  have e2 := hN12 (show (((y⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1,
      ((y⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2) ∈ N1 ×ˢ N2 from ⟨h1', hg⟩)
  exact hV12 ⟨e1.1, e2.2⟩

/-- The part of an idèle at the infinite places and at a finite set `P` of finite places. -/
def splitPart (P : Finset (HeightOneSpectrum (𝓞 K))) (y : IdeleGroup (𝓞 K) K) : IdeleGroup (𝓞 K) K :=
  infPart y * localPart y P

theorem ideleInfAt_splitPart (P : Finset (HeightOneSpectrum (𝓞 K))) (y : IdeleGroup (𝓞 K) K)
    (w : InfinitePlace K) : ideleInfAt (splitPart P y) w = ideleInfAt y w := by
  simp [splitPart, ideleInfAt_mul, ideleInfAt_infPart, ideleInfAt_localPart]

open scoped Classical in
theorem ideleFinAt_splitPart (P : Finset (HeightOneSpectrum (𝓞 K))) (y : IdeleGroup (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleFinAt (splitPart P y) v = if v ∈ P then ideleFinAt y v else 1 := by
  simp [splitPart, ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart]

/-- **Density**: `K^× · I_S` is dense in the idèles (weak approximation). -/
theorem dense_kIS (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    Dense ((kIS S : Subgroup (IdeleGroup (𝓞 K) K)) : Set (IdeleGroup (𝓞 K) K)) := by
  classical
  set Sf : Finset (HeightOneSpectrum (𝓞 K)) := hS.toFinset with hSf_def
  have hSf : S ⊆ ↑Sf := fun v hv => by simpa [hSf_def] using hv
  have hIS : ∀ y : IdeleGroup (𝓞 K) K, y * (splitPart Sf y)⁻¹ ∈ idelesTrivialAt S :=
    fun y => splitTriv_mem y Sf S hSf
  have hIS' : ∀ y : IdeleGroup (𝓞 K) K, y * (splitPart Sf y)⁻¹ ∈ kIS S := fun y =>
    mem_kIS.2 ⟨1, _, hIS y, by rw [map_one, one_mul]⟩
  have hι : ∀ a : Kˣ, splitPart Sf (IdeleGroup.unitEmbedding (𝓞 K) K a) ∈ kIS S := fun a => by
    refine mem_kIS.2 ⟨a, _, inv_mem (hIS (IdeleGroup.unitEmbedding (𝓞 K) K a)), ?_⟩
    rw [mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
  have hw : ∀ y : IdeleGroup (𝓞 K) K, splitPart Sf y ∈ closure ((kIS S : Subgroup (IdeleGroup (𝓞 K) K)) :
      Set (IdeleGroup (𝓞 K) K)) := by
    intro y
    rw [mem_closure_iff_nhds]
    intro t ht
    set w := splitPart Sf y with hw_def
    have hU : (fun z => w * z) ⁻¹' t ∈ 𝓝 (1 : IdeleGroup (𝓞 K) K) :=
      (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht)
    obtain ⟨O, T, n, hO, hUO⟩ := idele_nhds_one' hU
    have hy0 : ∀ w', ideleInfAt y w' ≠ 0 := ideleInfAt_ne_zero y
    have hyf0 : ∀ v, ideleFinAt y v ≠ 0 := ideleFinAt_ne_zero y
    let Q : ∀ w' : InfinitePlace K, Set w'.Completion := fun w' =>
      O w' ∩ (fun c => c⁻¹) ⁻¹' O w' ∩ {c | c ≠ 0}
    have hQ : ∀ w', Q w' ∈ 𝓝 (1 : w'.Completion) := fun w' =>
      Filter.inter_mem (Filter.inter_mem (hO w')
        ((continuousAt_inv₀ one_ne_zero).preimage_mem_nhds (by simpa using hO w')))
        (isOpen_ne.mem_nhds one_ne_zero)
    have hWi : ∀ w' : InfinitePlace K,
        (fun x => (ideleInfAt y w')⁻¹ * x) ⁻¹' Q w' ∈ 𝓝 (ideleInfAt y w') := fun w' =>
      (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
        (by show Q w' ∈ 𝓝 ((ideleInfAt y w')⁻¹ * ideleInfAt y w'); rw [inv_mul_cancel₀ (hy0 w')]; exact hQ w')
    have hWf : ∀ v : HeightOneSpectrum (𝓞 K),
        {x : v.adicCompletion K | Valued.v ((ideleFinAt y v)⁻¹ * x - 1) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))} ∈
          𝓝 (ideleFinAt y v) := fun v => by
      refine (IsOpen.mem_nhds ?_ ?_)
      · have hc : Continuous (fun x : v.adicCompletion K => (ideleFinAt y v)⁻¹ * x) :=
          continuous_const.mul continuous_id
        exact (isOpen_valued_sub_one_le v ((n + 1 : ℕ) : ℤ)).preimage hc
      · show Valued.v ((ideleFinAt y v)⁻¹ * ideleFinAt y v - 1) ≤ _
        rw [inv_mul_cancel₀ (hyf0 v), sub_self, map_zero]
        exact zero_le'
    have hd := TauCeti.GlobalNumberFields.weakApproximation_denseRange (K := K) Sf Finset.univ
    let tgt : ((v : {v : HeightOneSpectrum (𝓞 K) // v ∈ Sf}) → v.1.adicCompletion K) ×
        ((w' : {w : InfinitePlace K // w ∈ (Finset.univ : Finset (InfinitePlace K))}) → w'.1.Completion) :=
      (fun v => ideleFinAt y v.1, fun w' => ideleInfAt y w'.1)
    have hU0 : (Set.pi Set.univ fun v : {v : HeightOneSpectrum (𝓞 K) // v ∈ Sf} =>
          {x : v.1.adicCompletion K | Valued.v ((ideleFinAt y v.1)⁻¹ * x - 1) ≤
            WithZero.exp (-((n + 1 : ℕ) : ℤ))}) ×ˢ
        (Set.pi Set.univ fun w' : {w : InfinitePlace K // w ∈ (Finset.univ : Finset (InfinitePlace K))} =>
          (fun x => (ideleInfAt y w'.1)⁻¹ * x) ⁻¹' Q w'.1) ∈ 𝓝 tgt :=
      prod_mem_nhds (set_pi_mem_nhds Set.finite_univ fun v _ => hWf v.1)
        (set_pi_mem_nhds Set.finite_univ fun w' _ => hWi w'.1)
    obtain ⟨_, ⟨hz1, hz2⟩, ⟨x, rfl⟩⟩ := mem_closure_iff_nhds.1 (hd tgt) _ hU0
    have hz1' : ∀ v ∈ Sf, Valued.v ((ideleFinAt y v)⁻¹ * algebraMap K (v.adicCompletion K) x - 1) ≤
        WithZero.exp (-((n + 1 : ℕ) : ℤ)) := fun v hv => hz1 ⟨v, hv⟩ (Set.mem_univ _)
    have hz2' : ∀ w' : InfinitePlace K, (ideleInfAt y w')⁻¹ * algebraMap K w'.Completion x ∈ Q w' :=
      fun w' => hz2 ⟨w', Finset.mem_univ _⟩ (Set.mem_univ _)
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have hx0 : x ≠ 0 := by
      rintro rfl
      have h := (hz2' w0).2
      rw [Set.mem_setOf_eq, map_zero, mul_zero] at h
      exact h rfl
    set a : Kˣ := Units.mk0 x hx0 with ha
    set z : IdeleGroup (𝓞 K) K := w⁻¹ * splitPart Sf (IdeleGroup.unitEmbedding (𝓞 K) K a) with hz
    have zinf : ∀ w', ideleInfAt z w' = (ideleInfAt y w')⁻¹ * algebraMap K w'.Completion x := by
      intro w'
      rw [hz, ideleInfAt_mul, ideleInfAt_inv, hw_def, ideleInfAt_splitPart, ideleInfAt_splitPart,
        ideleInfAt_unitEmbedding]
      rfl
    have zfin : ∀ v, ideleFinAt z v = if v ∈ Sf then (ideleFinAt y v)⁻¹ *
        algebraMap K (v.adicCompletion K) x else 1 := by
      intro v
      rw [hz, ideleFinAt_mul, ideleFinAt_inv, hw_def, ideleFinAt_splitPart, ideleFinAt_splitPart]
      by_cases hv : v ∈ Sf
      · simp only [hv, if_true]
        rw [ideleFinAt_unitEmbedding]
        rfl
      · simp [hv]
    have hzU : z ∈ (fun z => w * z) ⁻¹' t := by
      refine hUO z (fun w' => ?_) (fun w' => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · rw [zinf]; exact (hz2' w').1.1
      · rw [show ideleInfAt z⁻¹ w' = (ideleInfAt z w')⁻¹ from ideleInfAt_inv z w', zinf]
        exact (hz2' w').1.2
      · rw [zfin]
        by_cases hvS : v ∈ Sf
        · rw [if_pos hvS]
          refine (hz1' v hvS).trans ?_
          rw [WithZero.exp_le_exp]; omega
        · rw [if_neg hvS, sub_self, map_zero]; exact zero_le'
      · rw [zfin]
        by_cases hvS : v ∈ Sf
        · rw [if_pos hvS]
          have h1 := val_eq_one_of_sub_one_le (Valued.v : Valuation (v.adicCompletion K) _)
            (show WithZero.exp (-((n + 1 : ℕ) : ℤ)) < 1 by
              rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega) (hz1' v hvS)
          exact h1
        · rw [if_neg hvS, map_one]
    refine ⟨w * z, ?_, ?_⟩
    · exact hzU
    · rw [hz, mul_inv_cancel_left]
      exact hι a
  intro y
  have hy : y = (y * (splitPart Sf y)⁻¹) * splitPart Sf y := by rw [inv_mul_cancel_right]
  have hmem : y ∈ (kIS S).topologicalClosure :=
    hy ▸ (kIS S).topologicalClosure.mul_mem ((kIS S).le_topologicalClosure (hIS' y)) (by
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]; exact hw y)
  rwa [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hmem

/-- The homomorphism `φ0 : K^× · I_S → G`, `φ0 (a x) = ψ (id x)`. -/
theorem exists_decomp (S : Set (HeightOneSpectrum (𝓞 K))) (y : kIS S) :
    ∃ x : idelesTrivialAt S, ∃ a : Kˣ, IdeleGroup.unitEmbedding (𝓞 K) K a * (x : IdeleGroup (𝓞 K) K) = y := by
  obtain ⟨a, x, hx, h⟩ := mem_kIS.1 y.2
  exact ⟨⟨x, hx⟩, a, h⟩

/-- The `I_S`-component of an element of `K^× · I_S`. -/
def xpart (S : Set (HeightOneSpectrum (𝓞 K))) (y : kIS S) : idelesTrivialAt S :=
  Classical.choose (exists_decomp S y)

theorem xpart_eq (S : Set (HeightOneSpectrum (𝓞 K))) (y : kIS S) (a : Kˣ) (x : idelesTrivialAt S)
    (h : IdeleGroup.unitEmbedding (𝓞 K) K a * (x : IdeleGroup (𝓞 K) K) = y) : xpart S y = x := by
  obtain ⟨a', ha'⟩ := Classical.choose_spec (exists_decomp S y)
  exact Subtype.ext (unitEmbedding_mul_unique S (Classical.choose (exists_decomp S y)).2 x.2
    (ha'.trans h.symm)).2

/-- The homomorphism `φ0 : K^× · I_S → G`, `φ0 (a x) = ψ (id x)`. -/
def phi0 {G : Type} [CommGroup G] (S : Set (HeightOneSpectrum (𝓞 K))) (ψ : sIdeals S →* G) :
    kIS S →* G where
  toFun y := ψ (idealOfTrivialAt S (xpart S y))
  map_one' := by
    have : xpart S 1 = 1 := xpart_eq S 1 1 1 (by simp)
    simp [this]
  map_mul' := by
    intro y y'
    obtain ⟨x, a, h⟩ := exists_decomp S y
    obtain ⟨x', a', h'⟩ := exists_decomp S y'
    have e1 := xpart_eq S y a x h
    have e2 := xpart_eq S y' a' x' h'
    have e3 : xpart S (y * y') = x * x' := by
      refine xpart_eq S _ (a * a') (x * x') ?_
      rw [map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ← h, ← h']
      exact mul_mul_mul_comm _ _ _ _
    simp only [e1, e2, e3, map_mul]

theorem phi0_apply {G : Type} [CommGroup G] (S : Set (HeightOneSpectrum (𝓞 K))) (ψ : sIdeals S →* G)
    (y : kIS S) (a : Kˣ) (x : IdeleGroup (𝓞 K) K) (hx : x ∈ idelesTrivialAt S)
    (h : IdeleGroup.unitEmbedding (𝓞 K) K a * x = (y : IdeleGroup (𝓞 K) K)) :
    phi0 S ψ y = ψ (idealOfTrivialAt S ⟨x, hx⟩) := by
  show ψ (idealOfTrivialAt S (xpart S y)) = _
  rw [xpart_eq S y a ⟨x, hx⟩ h]

/-- Admissibility gives continuity of `φ0` at `1` for the topology induced from the idèles. -/
theorem phi0_continuousAt_one {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Set (HeightOneSpectrum (𝓞 K))) (ψ : sIdeals S →* G) (hψ : IsAdmissible S ψ) :
    ∀ N ∈ 𝓝 (1 : G), ∃ U ∈ 𝓝 (1 : IdeleGroup (𝓞 K) K),
      ∀ h : kIS S, (h : IdeleGroup (𝓞 K) K) ∈ U → phi0 S ψ h ∈ N := by
  intro N hN
  obtain ⟨m, hmS, hm⟩ := hψ N⁻¹ (inv_mem_nhds_one G hN)
  refine ⟨idelesW m, (isOpen_idelesW m).mem_nhds (one_mem _), fun h hh => ?_⟩
  obtain ⟨x, a, hxa⟩ := exists_decomp S h
  rw [phi0_apply S ψ h a x x.2 hxa]
  have hx1 : ∀ w, ideleInfAt (x : IdeleGroup (𝓞 K) K) w = 1 := x.2.1
  have hx2 : ∀ v ∈ S, ideleFinAt (x : IdeleGroup (𝓞 K) K) v = 1 := x.2.2
  have hinf : ∀ w, ideleInfAt (h : IdeleGroup (𝓞 K) K) w =
      ideleInfAt (IdeleGroup.unitEmbedding (𝓞 K) K a) w := fun w => by
    rw [← hxa, ideleInfAt_mul, hx1 w, mul_one]
  have hfin : ∀ v ∈ S, ideleFinAt (h : IdeleGroup (𝓞 K) K) v =
      ideleFinAt (IdeleGroup.unitEmbedding (𝓞 K) K a) v := fun v hv => by
    rw [← hxa, ideleFinAt_mul, hx2 v hv, mul_one]
  have hcong : a ∈ congruenceSubgroup m := by
    rw [mem_congruenceSubgroup_iff_mem_idelesMod]
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · rw [← hinf w]; exact hh.1.1 w hw
    · rw [← hfin v (hmS hv)]; exact hh.1.2 v hv
  have hI : ideleToIdeal K (h : IdeleGroup (𝓞 K) K) = 1 := by
    refine (item_4_1.2 _).2 fun v => ?_
    by_cases hv : v ∈ m.finiteSupport
    · exact val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one m v hv) (hh.1.2 v hv)
    · exact hh.2 v hv
  have hps : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S := by
    rw [← ideleToIdeal_unitEmbedding, ideleToIdeal_mem_sIdeals_iff]
    intro v hv
    rw [← hfin v hv]
    by_cases hv' : v ∈ m.finiteSupport
    · exact val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one m v hv') (hh.1.2 v hv')
    · exact hh.2 v hv'
  have hid : idealOfTrivialAt S x = (⟨_, hps⟩ : sIdeals S)⁻¹ := by
    refine Subtype.ext ?_
    rw [idealOfTrivialAt_apply, Subgroup.coe_inv]
    refine eq_inv_of_mul_eq_one_right ?_
    show toPrincipalIdeal (𝓞 K) K a * ideleToIdeal K x = 1
    rw [← ideleToIdeal_unitEmbedding, ← map_mul, hxa]
    exact hI
  rw [hid, map_inv]
  exact hm a hcong hps

/-- **Remark 4.8, first sentence, corrected**: the extension of an admissible $\psi$ for $G$ complete Hausdorff. -/
@[kb "milne2020cft" "Ch. V, Remark 4.8 (extension, G complete Hausdorff)"]
theorem remark4_8_extend (G : Type) [CommGroup G] [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
    [T2Space G] (S : Set (HeightOneSpectrum (𝓞 K))) (ψ : sIdeals S →* G) (hS : S.Finite)
    (hψ : IsAdmissible S ψ) :
    ∃ φ : IdeleGroup (𝓞 K) K →* G, Continuous φ ∧ (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
      ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
        φ x = ψ b := by
  obtain ⟨φ, hφc, hφe⟩ := exists_extend_of_dense (kIS S) (dense_kIS S hS) (phi0 S ψ)
    (phi0_continuousAt_one S ψ hψ)
  refine ⟨φ, hφc, fun a => ?_, fun x hx b hb => ?_⟩
  · have hmem : IdeleGroup.unitEmbedding (𝓞 K) K a ∈ kIS S := mem_kIS.2 ⟨a, 1, one_mem _, mul_one _⟩
    have := hφe ⟨_, hmem⟩
    simp only at this
    rw [this, phi0_apply S ψ ⟨_, hmem⟩ a 1 (one_mem _) (mul_one _)]
    have h1 : idealOfTrivialAt S ⟨1, one_mem _⟩ = 1 := map_one (idealOfTrivialAt S)
    rw [h1, map_one]
  · have hmem : x ∈ kIS S := mem_kIS.2 ⟨1, x, hx, by rw [map_one, one_mul]⟩
    have := hφe ⟨_, hmem⟩
    simp only at this
    rw [this, phi0_apply S ψ ⟨_, hmem⟩ 1 x hx (by rw [map_one, one_mul])]
    congr 1
    exact Subtype.ext (by rw [idealOfTrivialAt_apply]; exact hb.symm)

end NumberFieldKB.MilneCFT
