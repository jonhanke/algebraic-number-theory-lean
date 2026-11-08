import NumberFieldKB.Pontryagin.Compact

/-!
# Annihilators (Weil II.§5, pp. 38–39)

$G$ is a locally compact commutative group, $H$ a closed subgroup, $H^*\subset G^*$ its annihilator (Weil: "the
subgroup associated with $H$ by duality").

* `annihilator H`; `isClosed_annihilator`: $H^*$ is a closed subgroup of $G^*$.
* **`annihilatorEquiv`**: $(G/H)^*\cong H^*$ as topological groups, $\psi\mapsto\psi\circ q$ (Weil: "it is isomorphic
  to the dual of $G/H$"). The inverse is continuous because every compact subset of $G/H$ is the image of a compact
  subset of $G$ (`exists_isCompact_image_eq`, local compactness).
* **`doubleAnnihilator_eq`**: $\{g:\chi(g)=1\ \forall\chi\in H^*\}=H$ when the characters of $G/H$ separate points
  (Weil: "the subgroup of $G$ associated with $H^*$ is then $H$ itself"); unconditional for discrete $G$
  (`doubleAnnihilator_eq_of_discrete`) and, given the Peter–Weyl theorem, for compact $G$
  (`doubleAnnihilator_eq_of_compact`). For general $G$ it follows from `PontryaginDualityStatement (G ⧸ H)`.
* `isCompact_annihilator_of_isOpen` ($H$ open ⇒ $H^*$ compact) and `isOpen_annihilator_of_isCompact`
  ($H$ compact ⇒ $H^*$ open): the directions of Weil's correspondences that do not need the duality theorem.
-/

open Topology

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The annihilator $H^*$ of a subgroup $H$: the characters trivial on $H$. -/
def annihilator (H : Subgroup G) : Subgroup (PontryaginDual G) where
  carrier := {χ | ∀ h ∈ H, χ h = 1}
  mul_mem' {a b} ha hb h hh := by simp [dual_mul_apply, ha h hh, hb h hh]
  one_mem' h _ := rfl
  inv_mem' {a} ha h hh := by simp [dual_inv_apply, ha h hh]

lemma mem_annihilator {H : Subgroup G} {χ : PontryaginDual G} : χ ∈ annihilator H ↔ ∀ h ∈ H, χ h = 1 :=
  Iff.rfl

/-- The annihilator is closed. -/
theorem isClosed_annihilator (H : Subgroup G) : IsClosed (annihilator H : Set (PontryaginDual G)) := by
  have : (annihilator H : Set (PontryaginDual G)) = ⋂ h ∈ H, {χ : PontryaginDual G | χ h = 1} := by
    ext χ; simp [mem_annihilator]
  rw [this]
  refine isClosed_biInter fun h _ => isClosed_eq ?_ continuous_const
  exact (continuous_eval_const (F := C(G, Circle)) h).comp
    (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous

variable [LocallyCompactSpace G]

/-- In a locally compact group, every compact subset of $G/H$ ($H$ closed) is the image of a compact subset of $G$. -/
theorem exists_isCompact_image_eq (H : Subgroup G) [IsClosed (H : Set G)] {K : Set (G ⧸ H)}
    (hK : IsCompact K) : ∃ L : Set G, IsCompact L ∧ (QuotientGroup.mk : G → G ⧸ H) '' L = K := by
  have hT2 : T2Space (G ⧸ H) := inferInstance
  choose y hy using fun x : G ⧸ H => QuotientGroup.mk_surjective x
  choose C hC hCc using fun x : G ⧸ H => exists_compact_mem_nhds (y x)
  have hnhds : ∀ x ∈ K, (QuotientGroup.mk : G → G ⧸ H) '' C x ∈ 𝓝 x := by
    intro x _
    have := (QuotientGroup.isOpenMap_coe (N := H)).image_mem_nhds (hCc x)
    rwa [hy x] at this
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover _ hnhds
  refine ⟨(⋃ x ∈ t, C x) ∩ (QuotientGroup.mk ⁻¹' K), ?_, ?_⟩
  · exact (t.isCompact_biUnion fun x _ => hC x).inter_right (hK.isClosed.preimage continuous_quot_mk)
  · apply Set.Subset.antisymm
    · rintro _ ⟨g, ⟨-, hg⟩, rfl⟩; exact hg
    · intro x hx
      obtain ⟨i, hit, g, hg, rfl⟩ := Set.mem_iUnion₂.mp (ht hx)
      exact ⟨g, ⟨Set.mem_biUnion hit hg, hx⟩, rfl⟩

/-- The map $(G/H)^*\to G^*$, $\psi\mapsto\psi\circ q$. -/
def quotientDualMap (H : Subgroup G) : PontryaginDual (G ⧸ H) →ₜ* PontryaginDual G :=
  PontryaginDual.map ⟨QuotientGroup.mk' H, continuous_quot_mk⟩

lemma quotientDualMap_apply (H : Subgroup G) (ψ : PontryaginDual (G ⧸ H)) (g : G) :
    quotientDualMap H ψ g = ψ (g : G ⧸ H) := rfl

lemma quotientDualMap_mem (H : Subgroup G) (ψ : PontryaginDual (G ⧸ H)) :
    quotientDualMap H ψ ∈ annihilator H := by
  intro h hh
  rw [quotientDualMap_apply, (QuotientGroup.eq_one_iff h).mpr hh, map_one]

/-- The character of $G/H$ induced by a character of $G$ trivial on $H$. -/
def liftChar (H : Subgroup G) (χ : annihilator H) : PontryaginDual (G ⧸ H) where
  toMonoidHom := QuotientGroup.lift H (χ.1 : G →* Circle) (fun h hh => χ.2 h hh)
  continuous_toFun := by
    apply Continuous.quotient_lift χ.1.continuous

@[simp]
lemma liftChar_apply (H : Subgroup G) (χ : annihilator H) (g : G) : liftChar H χ (g : G ⧸ H) = χ.1 g := rfl

/-- **Weil II.§5, p. 38**: the annihilator $H^*$ of a closed subgroup is isomorphic, as a topological group, to the
dual of $G/H$. -/
def annihilatorEquiv (H : Subgroup G) [IsClosed (H : Set G)] :
    PontryaginDual (G ⧸ H) ≃ₜ* annihilator H where
  toFun ψ := ⟨quotientDualMap H ψ, quotientDualMap_mem H ψ⟩
  invFun := liftChar H
  left_inv ψ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g => rfl
  right_inv χ := by ext g; rfl
  map_mul' ψ ψ' := rfl
  continuous_toFun := (quotientDualMap H).continuous.subtype_mk _
  continuous_invFun := by
    -- continuity into the compact-open topology, tested on compact sets of `G ⧸ H`
    apply (ContinuousMonoidHom.isInducing_toContinuousMap (G ⧸ H) Circle).continuous_iff.mpr
    apply ContinuousMap.continuous_compactOpen.mpr
    intro K hK U hU
    obtain ⟨L, hL, hLK⟩ := exists_isCompact_image_eq H hK
    have hopen := (ContinuousMap.isOpen_setOfPred_mapsTo hL hU).preimage
      ((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        (continuous_subtype_val (p := fun χ => χ ∈ annihilator H)))
    convert hopen using 1
    ext χ
    show Set.MapsTo _ K U ↔ Set.MapsTo _ L U
    rw [← hLK, Set.mapsTo_image_iff]
    exact Iff.rfl

@[simp]
lemma annihilatorEquiv_apply (H : Subgroup G) [IsClosed (H : Set G)] (ψ : PontryaginDual (G ⧸ H)) (g : G) :
    (annihilatorEquiv H ψ).1 g = ψ (g : G ⧸ H) := rfl

/-- **Weil II.§5, p. 38**: the subgroup of $G$ associated with $H^*$ is $H$ itself, provided the characters of
$G/H$ separate points (which is part of the duality theorem for $G/H$). -/
theorem doubleAnnihilator_eq (H : Subgroup G) (hsep : CharactersSeparate (G ⧸ H)) :
    {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H := by
  ext g
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro hg
    by_contra hgH
    have hq : (g : G ⧸ H) ≠ 1 := by rwa [ne_eq, QuotientGroup.eq_one_iff]
    obtain ⟨ψ, hψ⟩ := hsep _ hq
    exact hψ (hg _ (quotientDualMap_mem H ψ))
  · intro hg χ hχ
    exact hχ g hg

/-- The double annihilator, for a discrete group. -/
theorem doubleAnnihilator_eq_of_discrete [DiscreteTopology G] (H : Subgroup G) :
    {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H := by
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology (by simp)
  exact doubleAnnihilator_eq H charactersSeparate_of_discrete

omit [LocallyCompactSpace G] in
/-- The double annihilator, for a compact group (given the Peter–Weyl theorem). -/
theorem doubleAnnihilator_eq_of_compact {G : Type u} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (hPW : PeterWeylTheorem.{u}) (H : Subgroup G)
    [IsClosed (H : Set G)] :
    {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H :=
  doubleAnnihilator_eq H (charactersSeparate_of_compact hPW)

/-- **Weil II.§5, p. 39**: if $H$ is open, then $H^*$ is compact ($G/H$ is discrete, so its dual is compact). -/
theorem isCompact_annihilator_of_isOpen (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsCompact (annihilator H : Set (PontryaginDual G)) := by
  have : IsClosed (H : Set G) := H.isClosed_of_isOpen hH
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  have hc : IsCompact (Set.univ : Set (PontryaginDual (G ⧸ H))) := isCompact_univ
  have := (hc.image (annihilatorEquiv H).continuous).image continuous_subtype_val
  convert this using 1
  ext χ
  simp only [Set.image_univ, Set.mem_image, Set.mem_range, SetLike.mem_coe]
  constructor
  · intro hχ
    exact ⟨⟨χ, hχ⟩, ⟨(annihilatorEquiv H).symm ⟨χ, hχ⟩, (annihilatorEquiv H).apply_symm_apply _⟩, rfl⟩
  · rintro ⟨χ', -, rfl⟩
    exact χ'.2

/-- **Weil II.§5, p. 39**: if $H$ is compact, then $H^*$ is open (a character mapping the compact subgroup $H$ into
the open half circle is trivial on it). -/
theorem isOpen_annihilator_of_isCompact (H : Subgroup G) (hH : IsCompact (H : Set G)) :
    IsOpen (annihilator H : Set (PontryaginDual G)) := by
  have hset : (annihilator H : Set (PontryaginDual G)) =
      (fun χ : PontryaginDual G => (χ : G →ₜ* Circle).toContinuousMap) ⁻¹'
        {f : C(G, Circle) | Set.MapsTo f H (Circle.centeredArc (Real.pi / 2))} := by
    ext χ
    simp only [SetLike.mem_coe, Set.mem_preimage]
    constructor
    · intro hχ h hh
      change χ h ∈ Circle.centeredArc (Real.pi / 2)
      rw [hχ h hh, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
      simp [Real.pi_pos]
    · intro hmaps h hh
      refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
      have := hmaps (H.pow_mem hh n)
      change χ (h ^ n) ∈ _ at this
      rwa [map_pow] at this
  rw [hset]
  exact (ContinuousMap.isOpen_setOfPred_mapsTo hH (Circle.isOpen_centeredArc _)).preimage
    (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous

end NumberFieldKB.Pontryagin
