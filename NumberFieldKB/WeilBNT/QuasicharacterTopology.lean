import NumberFieldKB.WeilBNT.QuasicompactGroups
import Mathlib.Geometry.Manifold.IsManifold.Basic
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, VII.§3, text p. 116–117: the topology and complex structure of $\Omega(G)$

For a quasicompact group $G$ with $G/G_1\cong\mathbb R$, Cor. 1 of Prop. 7 gives an isomorphism $s\mapsto\omega_s$ of
$\mathbb C$ onto the group $\Omega_1$ of principal quasicharacters. Weil puts on $\Omega(G)$ the topology for which
$\Omega_1$ is an open subgroup carrying the topology of $\mathbb C$, and on every coset $\chi\Omega_1$ the complex
structure deduced from that of $\Omega_1$ by translation. Then $\Omega(G)/\Omega_1$ is discrete and the connected
components of $\Omega(G)$ are the cosets of $\Omega_1$, each isomorphic to $\mathbb C$.

**Construction.** The construction only uses the group $M=\Omega(G)$ and the map $p:\mathbb C\to M$, $s\mapsto\omega_s$,
with $p(s+t)=p(s)p(t)$; so it is done for any commutative group $M$ and such a $p$ (type synonym `WeilOmega M p`).
The topology (`instTopologicalSpaceWeilOmega`) is the finest one making every map $s\mapsto\chi\,p(s)$ ($\chi\in M$,
`cosetMap p χ`) continuous: $U$ is open iff every $\{s:\chi p(s)\in U\}$ is open in $\mathbb C$ (`isOpen_iff`). This is
Weil's topology: the cosets are open (`isOpen_range_cosetMap`) and, when $p$ is injective, $s\mapsto\chi p(s)$ is a
homeomorphism of $\mathbb C$ onto the coset $\chi\Omega_1$ (`isOpenEmbedding_cosetMap`). The charts of the complex
structure are the inverses of these maps (`instChartedSpaceWeilOmega`); the transition maps are translations
$s\mapsto s+c$, so this is an analytic manifold modelled on $\mathbb C$ (`weil_VII_3_text117_complexStructure`).

* `omegaOne p`: $\Omega_1=p(\mathbb C)$ as a subgroup; **`weil_VII_3_text117_isOpen`**: it is open.
* **`weil_VII_3_text117_discrete`**: $\Omega(G)/\Omega_1$ is discrete.
* **`weil_VII_3_text117_components`**: the connected component of $\chi$ is the coset $\chi\Omega_1$.
* **`weil_VII_3_text117_homeomorph`**: $s\mapsto\chi p(s)$ is a homeomorphism of $\mathbb C$ onto $\chi\Omega_1$.
* **`weil_VII_3_text117_topologicalGroup`**: $\Omega(G)$ is a topological group.
* **`weil_VII_3_text117_complexStructure`**: the complex (analytic) manifold structure.
* **`weil_VII_3_text117_ideleClass`**: all of this for $G=C_k$, $k$ a number field, with $p(s)=|\cdot|^s$
  (`HeckeCharacter.normPow`); there $p(\mathbb C)$ is exactly the set of principal quasicharacters
  (`weil_VII_3_def6_ideleClass`) and $p$ is injective (`GlobalZeta.normPow_injective`).

Not done here: the case $G/G_1\cong\mathbb Z$ (e.g. $K^\times$ for a $p$-field $K$), where $s\mapsto\omega_s$ has kernel
$2\pi i a^{-1}\mathbb Z$ and the components are copies of $\mathbb C^\times$; and the comparison of Weil's topology
with Mathlib's compact-open topology on `ContinuousMonoidHom G ℂˣ` (they agree, but the proof needs the discreteness of
the dual of the compact group $G_1$).
-/

open Topology Set
open scoped Manifold

noncomputable section

namespace NumberFieldKB.WeilBNT

/-- Weil's $\Omega(G)$ with its topology and complex structure: a type synonym for the commutative group `M` (the
quasicharacters of $G$), remembering the map $p:s\mapsto\omega_s$ onto the principal ones. -/
@[nolint unusedArguments]
def WeilOmega (M : Type*) [CommGroup M] (_p : ℂ → M) : Type _ := M

namespace WeilOmega

variable {M : Type*} [CommGroup M] {p : ℂ → M}

instance : CommGroup (WeilOmega M p) := inferInstanceAs (CommGroup M)

/-- The identification of `M` with `WeilOmega M p`. -/
def toW (p : ℂ → M) : M → WeilOmega M p := id

/-- The identification of `WeilOmega M p` with `M`. -/
def ofW : WeilOmega M p → M := id

@[simp] theorem toW_mul (a b : M) : toW p (a * b) = toW p a * toW p b := rfl
@[simp] theorem toW_one : toW p (1 : M) = 1 := rfl
@[simp] theorem toW_inv (a : M) : toW p a⁻¹ = (toW p a)⁻¹ := rfl
@[simp] theorem toW_ofW (x : WeilOmega M p) : toW p (ofW x) = x := rfl
@[simp] theorem ofW_toW (a : M) : ofW (toW p a) = a := rfl
theorem toW_injective : Function.Injective (toW p) := fun _ _ h => h

/-- The parametrization $s\mapsto\chi\,p(s)$ of the coset $\chi\Omega_1$. -/
def cosetMap (p : ℂ → M) (χ : M) (s : ℂ) : WeilOmega M p := toW p (χ * p s)

/-- **Weil's topology** on $\Omega(G)$: the finest topology making every $s\mapsto\chi\,p(s)$ continuous. -/
instance instTopologicalSpaceWeilOmega : TopologicalSpace (WeilOmega M p) :=
  ⨆ χ : M, TopologicalSpace.coinduced (cosetMap p χ) inferInstance

theorem isOpen_iff {U : Set (WeilOmega M p)} : IsOpen U ↔ ∀ χ : M, IsOpen (cosetMap p χ ⁻¹' U) := by
  simp only [isOpen_iSup_iff, isOpen_coinduced]

theorem continuous_cosetMap (χ : M) : Continuous (cosetMap p χ) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup (fun χ : M => TopologicalSpace.coinduced (cosetMap p χ) inferInstance) χ

variable (hp : ∀ s t, p (s + t) = p s * p t)
include hp

theorem map_zero : p 0 = 1 := by
  have h := hp 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem cosetMap_add (χ : M) (s t : ℂ) : cosetMap p χ (s + t) = cosetMap p (χ * p s) t := by
  show toW p (χ * p (s + t)) = toW p (χ * p s * p t)
  rw [hp, mul_assoc]

theorem cosetMap_zero (χ : M) : cosetMap p χ 0 = toW p χ := by
  simp [cosetMap, map_zero hp]

/-- A set stable under multiplication by $p(\mathbb C)$ (a union of cosets of $\Omega_1$) is open. -/
theorem isOpen_of_stable {U : Set (WeilOmega M p)} (hU : ∀ χ : M, toW p χ ∈ U → ∀ s, cosetMap p χ s ∈ U) :
    IsOpen U := by
  rw [isOpen_iff]
  intro ψ
  by_cases h : ∃ s₀, cosetMap p ψ s₀ ∈ U
  · obtain ⟨s₀, hs₀⟩ := h
    convert isOpen_univ
    ext s
    simp only [mem_preimage, mem_univ, iff_true]
    have := hU (ψ * p s₀) hs₀ (s - s₀)
    rwa [← cosetMap_add hp, add_sub_cancel] at this
  · convert isOpen_empty
    ext s
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    exact fun hs => h ⟨s, hs⟩

omit hp in
/-- Membership in a coset. -/
theorem mem_range_cosetMap_iff (χ ψ : M) : toW p ψ ∈ range (cosetMap p χ) ↔ ∃ a, ψ = χ * p a := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (toW_injective ha).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

/-- Cosets are stable. -/
theorem range_cosetMap_stable (χ : M) :
    ∀ ψ : M, toW p ψ ∈ range (cosetMap p χ) → ∀ s, cosetMap p ψ s ∈ range (cosetMap p χ) := by
  rintro ψ ⟨a, ha⟩ s
  refine ⟨a + s, ?_⟩
  rw [cosetMap_add hp]
  have : χ * p a = ψ := toW_injective ha
  rw [this]

/-- The cosets $\chi\Omega_1$ are open. -/
theorem isOpen_range_cosetMap (χ : M) : IsOpen (range (cosetMap p χ)) :=
  isOpen_of_stable hp (range_cosetMap_stable hp χ)

/-- The cosets $\chi\Omega_1$ are closed. -/
theorem isClosed_range_cosetMap (χ : M) : IsClosed (range (cosetMap p χ)) := by
  rw [← isOpen_compl_iff]
  refine isOpen_of_stable hp fun ψ hψ s hs => hψ ?_
  obtain ⟨a, ha⟩ := hs
  refine ⟨a - s, ?_⟩
  have h1 : χ * p a = ψ * p s := toW_injective ha
  show toW p (χ * p (a - s)) = toW p ψ
  congr 1
  have h2 : p a = p (a - s) * p s := by rw [← hp, sub_add_cancel]
  rw [h2, ← mul_assoc] at h1
  exact mul_right_cancel h1

/-- $\Omega_1=p(\mathbb C)$, the subgroup of principal quasicharacters. -/
def omegaOne (hp : ∀ s t, p (s + t) = p s * p t) : Subgroup (WeilOmega M p) where
  carrier := range (cosetMap p 1)
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, by simp [cosetMap, hp]⟩
  one_mem' := ⟨0, by simp [cosetMap, map_zero hp]⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    refine ⟨-s, ?_⟩
    simp only [cosetMap, one_mul, ← toW_inv]
    congr 1
    exact eq_inv_of_mul_eq_one_left (by rw [← hp, neg_add_cancel, map_zero hp])

theorem mem_omegaOne {χ : WeilOmega M p} : χ ∈ omegaOne hp ↔ ∃ s, χ = toW p (p s) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, by simp [cosetMap]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, by simp [cosetMap]⟩

/-- **Weil, VII.§3, text p. 117**: $\Omega_1$ is an open subgroup of $\Omega(G)$. -/
@[kb "weil1973bnt" "Ch. VII, §3, text p. 116-117 (Ω₁ is an open subgroup of Ω(G))"]
theorem weil_VII_3_text117_isOpen : IsOpen ((omegaOne hp : Subgroup (WeilOmega M p)) : Set (WeilOmega M p)) :=
  isOpen_range_cosetMap hp 1

/-- **Weil, VII.§3, text p. 117**: $\Omega(G)/\Omega_1$ is discrete. -/
@[kb "weil1973bnt" "Ch. VII, §3, text p. 116-117 (Ω(G)/Ω₁ is discrete)"]
theorem weil_VII_3_text117_discrete : DiscreteTopology (WeilOmega M p ⧸ omegaOne hp) := by
  refine discreteTopology_iff_forall_isOpen.mpr fun S => ?_
  rw [isOpen_coinduced]
  refine isOpen_of_stable hp fun χ hχ s => ?_
  simp only [mem_preimage] at hχ ⊢
  convert hχ using 1
  refine QuotientGroup.eq.mpr ⟨-s, ?_⟩
  simp only [cosetMap, one_mul, ← toW_inv, ← toW_mul, mul_inv_rev, inv_mul_cancel_right]
  congr 1
  exact eq_inv_of_mul_eq_one_left (by rw [← hp, neg_add_cancel, map_zero hp])

/-- **Weil, VII.§3, text p. 117**: the connected component of $\chi$ in $\Omega(G)$ is the coset $\chi\Omega_1$. -/
@[kb "weil1973bnt" "Ch. VII, §3, text p. 116-117 (the connected components of Ω(G) are the cosets of Ω₁)"]
theorem weil_VII_3_text117_components (χ : M) :
    connectedComponent (toW p χ) = range (cosetMap p χ) := by
  have hmem : toW p χ ∈ range (cosetMap p χ) := ⟨0, cosetMap_zero hp χ⟩
  apply Subset.antisymm
  · exact (IsClopen.connectedComponent_subset
      ⟨isClosed_range_cosetMap hp χ, isOpen_range_cosetMap hp χ⟩ hmem)
  · exact (isConnected_range (continuous_cosetMap χ)).isPreconnected.subset_connectedComponent hmem

/-- The coset map is open. -/
theorem isOpenMap_cosetMap (hinj : Function.Injective p) (χ : M) : IsOpenMap (cosetMap p χ) := by
  intro U hU
  rw [isOpen_iff]
  intro ψ
  by_cases h : ∃ a, ψ = χ * p a
  · obtain ⟨a, rfl⟩ := h
    convert hU.preimage (continuous_const_add a) using 1
    ext s
    simp only [mem_preimage, mem_image]
    constructor
    · rintro ⟨u, hu, hus⟩
      rw [← cosetMap_add hp] at hus
      have : χ * p u = χ * p (a + s) := toW_injective hus
      rwa [← hinj (mul_left_cancel this)]
    · intro hs
      exact ⟨a + s, hs, by rw [cosetMap_add hp]⟩
  · convert isOpen_empty
    ext s
    simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
    intro u _ hus
    apply h
    refine ⟨u - s, ?_⟩
    have h1 : χ * p u = ψ * p s := toW_injective hus
    have h2 : p u = p (u - s) * p s := by rw [← hp, sub_add_cancel]
    rw [h2, ← mul_assoc] at h1
    exact (mul_right_cancel h1).symm

omit hp in
theorem cosetMap_injective (hinj : Function.Injective p) (χ : M) : Function.Injective (cosetMap p χ) := by
  intro s t h
  exact hinj (mul_left_cancel (toW_injective h))

theorem isOpenEmbedding_cosetMap (hinj : Function.Injective p) (χ : M) : IsOpenEmbedding (cosetMap p χ) :=
  .of_continuous_injective_isOpenMap (continuous_cosetMap χ) (cosetMap_injective hinj χ)
    (isOpenMap_cosetMap hp hinj χ)

/-- **Weil, VII.§3, text p. 117**: for $p$ injective (the case $G/G_1\cong\mathbb R$), $s\mapsto\chi\,p(s)$ is a
homeomorphism of $\mathbb C$ onto the coset $\chi\Omega_1$, an open subset. -/
@[kb "weil1973bnt" "Ch. VII, §3, text p. 116-117 (each coset of Ω₁ is homeomorphic to C, by s ↦ χω_s)"]
theorem weil_VII_3_text117_homeomorph (hinj : Function.Injective p) (χ : M) :
    IsOpenEmbedding (cosetMap p χ) ∧ range (cosetMap p χ) = connectedComponent (toW p χ) :=
  ⟨isOpenEmbedding_cosetMap hp hinj χ, (weil_VII_3_text117_components hp χ).symm⟩

/-- **Weil, VII.§3, text p. 117**: with this topology $\Omega(G)$ is a topological group (so $\Omega(G)/\Omega_1$ is a
discrete topological group). -/
@[kb "weil1973bnt" "Ch. VII, §3, text p. 116-117 (Ω(G) is a topological group)"]
theorem weil_VII_3_text117_topologicalGroup (hinj : Function.Injective p) : IsTopologicalGroup (WeilOmega M p) where
  continuous_mul := by
    rw [continuous_iff_continuousAt]
    rintro ⟨x, y⟩
    have he := (isOpenEmbedding_cosetMap hp hinj (ofW x)).prodMap (isOpenEmbedding_cosetMap hp hinj (ofW y))
    have hxy : (x, y) = Prod.map (cosetMap p (ofW x)) (cosetMap p (ofW y)) (0, 0) := by
      simp [cosetMap_zero hp]
    rw [hxy, ← he.continuousAt_iff]
    have : (fun q : WeilOmega M p × WeilOmega M p => q.1 * q.2) ∘
        Prod.map (cosetMap p (ofW x)) (cosetMap p (ofW y)) =
        fun st : ℂ × ℂ => cosetMap p (ofW x * ofW y) (st.1 + st.2) := by
      funext st
      simp only [Function.comp, Prod.map, cosetMap, hp, ← toW_mul]
      congr 1
      ac_rfl
    rw [this]
    exact ((continuous_cosetMap _).comp continuous_add).continuousAt
  continuous_inv := by
    rw [continuous_iff_continuousAt]
    intro x
    have he := isOpenEmbedding_cosetMap hp hinj (ofW x)
    have hx : x = cosetMap p (ofW x) 0 := by rw [cosetMap_zero hp, toW_ofW]
    rw [hx, ← he.continuousAt_iff]
    have : (fun q : WeilOmega M p => q⁻¹) ∘ cosetMap p (ofW x) = fun s => cosetMap p (ofW x)⁻¹ (-s) := by
      funext s
      simp only [Function.comp, cosetMap, ← toW_inv]
      congr 1
      rw [mul_inv, eq_inv_of_mul_eq_one_left (a := p (-s)) (b := p s)
        (by rw [← hp, neg_add_cancel, map_zero hp])]
    rw [this]
    exact ((continuous_cosetMap _).comp continuous_neg).continuousAt

/-! ### The complex structure -/

/-- The conditions of Cor. 1 of Prop. 7 in the case $G/G_1\cong\mathbb R$: $s\mapsto\omega_s$ is an injective
morphism $\mathbb C\to\Omega(G)$. (A condition on the data, not a cited result.) -/
class IsPrincipalParam (p : ℂ → M) : Prop where
  map_add : ∀ s t, p (s + t) = p s * p t
  injective : Function.Injective p

variable [hP : IsPrincipalParam p]

omit hp

/-- The chart at the coset $\chi\Omega_1$: the inverse of $s\mapsto\chi\,p(s)$. -/
def chart (χ : M) : OpenPartialHomeomorph (WeilOmega M p) ℂ :=
  ((isOpenEmbedding_cosetMap hP.map_add hP.injective χ).toOpenPartialHomeomorph (cosetMap p χ)).symm

theorem chart_source (χ : M) : (chart (p := p) χ).source = range (cosetMap p χ) := by
  simp [chart]

theorem chart_cosetMap (χ : M) (s : ℂ) : chart (p := p) χ (cosetMap p χ s) = s :=
  (isOpenEmbedding_cosetMap hP.map_add hP.injective χ).toOpenPartialHomeomorph_left_inv

theorem chart_symm (χ : M) : ⇑(chart (p := p) χ).symm = cosetMap p χ := by
  simp [chart]

/-- **Weil's complex structure** on $\Omega(G)$: charts $\chi\,p(s)\mapsto s$ on the cosets $\chi\Omega_1$. -/
instance instChartedSpaceWeilOmega : ChartedSpace ℂ (WeilOmega M p) where
  atlas := range (chart (p := p))
  chartAt x := chart (ofW x)
  mem_chart_source x := by
    rw [chart_source]
    exact ⟨0, by rw [cosetMap_zero hP.map_add, toW_ofW]⟩
  chart_mem_atlas x := ⟨ofW x, rfl⟩

/-- The transition maps are translations. -/
theorem transition_eq (χ ψ : M) :
    ∃ c : ℂ, ∀ z ∈ ((chart (p := p) χ).symm ≫ₕ chart ψ).source,
      ((chart (p := p) χ).symm ≫ₕ chart ψ) z = c + z := by
  by_cases h : ∃ a, χ = ψ * p a
  · obtain ⟨a, rfl⟩ := h
    refine ⟨a, fun z _ => ?_⟩
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, chart_symm]
    rw [← cosetMap_add hP.map_add, chart_cosetMap]
  · refine ⟨0, fun z hz => ?_⟩
    exfalso
    simp only [OpenPartialHomeomorph.trans_source, chart_symm, mem_inter_iff, mem_preimage,
      chart_source] at hz
    obtain ⟨u, hu⟩ := hz.2
    apply h
    refine ⟨u - z, ?_⟩
    have h1 : ψ * p u = χ * p z := toW_injective hu
    have h2 : p u = p (u - z) * p z := by rw [← hP.map_add, sub_add_cancel]
    rw [h2, ← mul_assoc] at h1
    exact (mul_right_cancel h1).symm

/-- **Weil, VII.§3, text p. 117**: the complex structure on $\Omega(G)$ (case $G/G_1\cong\mathbb R$). The charts
$\chi\,p(s)\mapsto s$ have translations as transition maps, so they define an analytic (holomorphic) manifold
structure modelled on $\mathbb C$, on which each coset $\chi\Omega_1$ is a copy of $\mathbb C$. -/
@[kb "weil1973bnt" "Ch. VII, §3, text p. 116-117 (the complex structure on Ω(G), deduced from Ω₁ ≅ C by translation)"]
theorem weil_VII_3_text117_complexStructure : IsManifold 𝓘(ℂ) ⊤ (WeilOmega M p) := by
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  obtain ⟨χ, rfl⟩ := he
  obtain ⟨ψ, rfl⟩ := he'
  obtain ⟨c, hc⟩ := transition_eq (p := p) χ ψ
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    preimage_id_eq, id_eq, range_id, inter_univ]
  exact (contDiff_const.add contDiff_id).contDiffOn.congr fun z hz => hc z hz

end WeilOmega

/-! ### The idele class group of a number field -/

section IdeleClass

variable (F : Type) [Field F] [NumberField F]

instance isPrincipalParam_normPow : WeilOmega.IsPrincipalParam (HeckeCharacter.normPow F) where
  map_add := HeckeCharacter.normPow_add (F := F)
  injective _ _ h := GlobalZeta.normPow_injective h

/-- Weil's $\Omega(G_k)$ for the idele class group of a number field: the Hecke characters (quasicharacters of
$C_k=\mathbb A_k^\times/k^\times$) with Weil's topology and complex structure, built from $s\mapsto|\cdot|^s$. -/
abbrev OmegaIdeleClass : Type := WeilOmega (HeckeCharacter F) (HeckeCharacter.normPow F)

/-- **Weil, VII.§3, text p. 116–117, for $G=C_k$** ($k$ a number field, $G/G_1\cong\mathbb R$): $\Omega_1$, the set of
$|\cdot|^s$, is exactly the set of principal quasicharacters; it is an open subgroup of $\Omega(C_k)$; the quotient
$\Omega(C_k)/\Omega_1$ is discrete; $\Omega(C_k)$ is a topological group; the connected component of $\chi$ is the coset
$\{\chi|\cdot|^s\}$, onto which $s\mapsto\chi|\cdot|^s$ is a homeomorphism from $\mathbb C$; and the charts
$\chi|\cdot|^s\mapsto s$ make $\Omega(C_k)$ a complex analytic manifold. -/
@[kb "weil1973bnt" "Ch. VII, §3, text p. 116-117 (topology and complex structure on Ω(G_k), k a number field)"]
theorem weil_VII_3_text117_ideleClass :
    let hp := HeckeCharacter.normPow_add (F := F)
    (∀ χ : HeckeCharacter F, WeilOmega.toW _ χ ∈ WeilOmega.omegaOne hp ↔
      IsPrincipalQuasicharacter (G := NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F) χ) ∧
    IsOpen ((WeilOmega.omegaOne hp : Subgroup (OmegaIdeleClass F)) : Set (OmegaIdeleClass F)) ∧
    DiscreteTopology (OmegaIdeleClass F ⧸ WeilOmega.omegaOne hp) ∧
    IsTopologicalGroup (OmegaIdeleClass F) ∧
    (∀ χ : HeckeCharacter F, IsOpenEmbedding (WeilOmega.cosetMap (HeckeCharacter.normPow F) χ) ∧
      connectedComponent (WeilOmega.toW (HeckeCharacter.normPow F) χ) =
        range (WeilOmega.cosetMap (HeckeCharacter.normPow F) χ)) ∧
    IsManifold 𝓘(ℂ) ⊤ (OmegaIdeleClass F) := by
  intro hp
  have hinj : Function.Injective (HeckeCharacter.normPow F) := fun _ _ h => GlobalZeta.normPow_injective h
  refine ⟨fun χ => ?_, WeilOmega.weil_VII_3_text117_isOpen hp, WeilOmega.weil_VII_3_text117_discrete hp,
    WeilOmega.weil_VII_3_text117_topologicalGroup hp hinj,
    fun χ => ⟨WeilOmega.isOpenEmbedding_cosetMap hp hinj χ, WeilOmega.weil_VII_3_text117_components hp χ⟩,
    WeilOmega.weil_VII_3_text117_complexStructure⟩
  rw [WeilOmega.mem_omegaOne, weil_VII_3_def6_ideleClass]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, WeilOmega.toW_injective hs⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩

end IdeleClass

end NumberFieldKB.WeilBNT
