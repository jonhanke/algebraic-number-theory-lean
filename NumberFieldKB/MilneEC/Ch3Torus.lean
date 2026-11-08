import NumberFieldKB.MilneEC.Ch3Defs
import NumberFieldKB.MilneEC.Ch3Lattice

/-!
# Milne, Elliptic Curves, Chapter III §3: the Riemann surfaces `ℂ/Λ` and their endomorphisms

Items of Milne, *Elliptic Curves* (`milne2006ec`, pdf pp. 98–108) about the quotients `ℂ/Λ`:
Proposition 3.3, Corollaries 3.4 and 3.5, Proposition 3.17, Lemma 3.20, Proposition 3.21, the
Tate module of `ℂ/Λ`, Proposition 3.22 and Corollary 3.23 over `ℂ`.

Conventions.
* `ℂ ⧸ Λ` is the quotient of `ℂ` by the lattice `Λ : Submodule ℤ ℂ`.  Milne gives `ℂ/Λ` "the
  unique complex structure for which `π : ℂ → ℂ/Λ` is a local isomorphism of Riemann surfaces"
  (pdf p. 98).  Mathlib has no complex structure on `ℂ ⧸ Λ`; we record holomorphy of a map
  `φ : ℂ/Λ → ℂ/Λ'` as the existence of local holomorphic lifts (`IsHolomorphicMap`), which is
  the meaning of holomorphy for that complex structure (both quotient maps are local
  isomorphisms).
* The endomorphism ring of the Riemann surface `ℂ/Λ` (holomorphic maps fixing `0`) is identified
  by Proposition 3.3 with `endRing Λ = {α ∈ ℂ | αΛ ⊆ Λ}`.
* Milne's degree of a nonzero endomorphism `α` of `E(ℂ) = ℂ/Λ` is the order of its kernel
  (pdf p. 107: "`α(ℂ)` is `n : 1`, and so `α` has degree `n`", by Chapter I, 4.24); Mathlib has no
  degree of a morphism of curves, so `degree` below is the order of the kernel.
* Remark 3.18 says `End(E(Λ)) = End(ℂ/Λ)`; Mathlib has no endomorphism ring of an elliptic
  curve, so Propositions 3.21, 3.22 and Corollary 3.23 are stated for `ℂ/Λ` (the case `k = ℂ`
  that Milne proves).  The versions over an arbitrary algebraically closed field are not stated.
-/

open Complex Set Filter Topology Pointwise IntermediateField
open scoped TensorProduct

namespace NumberFieldKB.MilneEC.III

/-! ### Holomorphic maps `ℂ/Λ → ℂ/Λ'` -/

/-- A map `φ : ℂ/Λ → ℂ/Λ'` is holomorphic for Milne's complex structures (pdf p. 98) if near
every point it lifts to a holomorphic map `ℂ → ℂ`: for every `z ∈ ℂ` there are a neighbourhood
`U` of `z` and a function `g` holomorphic on `U` with `[g(u)] = φ([u])` for `u ∈ U`. -/
@[kb "milne2006ec" "Ch. III, §3, complex structure on C/Λ, holomorphic maps, pdf p. 98"]
def IsHolomorphicMap (Λ Λ' : Submodule ℤ ℂ) (φ : ℂ ⧸ Λ → ℂ ⧸ Λ') : Prop :=
  ∀ z : ℂ, ∃ U ∈ 𝓝 z, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
    ∀ u ∈ U, (Submodule.Quotient.mk (g u) : ℂ ⧸ Λ') = φ (Submodule.Quotient.mk u)

/-- An isomorphism of Riemann surfaces `ℂ/Λ ≅ ℂ/Λ'` (Milne, pdf p. 97): a bijection that is
holomorphic with holomorphic inverse. -/
def IsBiholomorphic (Λ Λ' : Submodule ℤ ℂ) (φ : ℂ ⧸ Λ ≃ ℂ ⧸ Λ') : Prop :=
  IsHolomorphicMap Λ Λ' φ ∧ IsHolomorphicMap Λ' Λ φ.symm

/-- The map `[z] ↦ [αz] : ℂ/Λ → ℂ/Λ'` for `αΛ ⊆ Λ'` (Proposition 3.3). -/
noncomputable def mulMap {Λ Λ' : Submodule ℤ ℂ} (α : ℂ) (h : ∀ x ∈ Λ, α * x ∈ Λ') :
    ℂ ⧸ Λ →ₗ[ℤ] ℂ ⧸ Λ' :=
  Λ.mapQ Λ' (LinearMap.mulLeft ℤ α) h

@[simp] theorem mulMap_mk {Λ Λ' : Submodule ℤ ℂ} (α : ℂ) (h : ∀ x ∈ Λ, α * x ∈ Λ') (z : ℂ) :
    mulMap α h (Submodule.Quotient.mk z) = Submodule.Quotient.mk (α * z) := rfl

private theorem exists_open_lift {Λ Λ' : Submodule ℤ ℂ} {φ : ℂ ⧸ Λ → ℂ ⧸ Λ'}
    (hφ : IsHolomorphicMap Λ Λ' φ) (z : ℂ) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ u ∈ U, (Submodule.Quotient.mk (g u) : ℂ ⧸ Λ') = φ (Submodule.Quotient.mk u) := by
  obtain ⟨U, hU, g, hg, h⟩ := hφ z
  exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, g,
    hg.mono interior_subset, fun u hu => h u (interior_subset hu)⟩

private theorem deriv_eq_of_lift (L : PeriodPair) {V : Set ℂ} (hV : IsOpen V) {z : ℂ} (hz : z ∈ V)
    {g₁ g₂ : ℂ → ℂ} (h1 : DifferentiableOn ℂ g₁ V) (h2 : DifferentiableOn ℂ g₂ V)
    (h : ∀ u ∈ V, (Submodule.Quotient.mk (g₁ u) : ℂ ⧸ L.lattice) = Submodule.Quotient.mk (g₂ u)) :
    deriv g₁ z = deriv g₂ z := by
  have hc : ContinuousAt (fun u => g₁ u - g₂ u) z :=
    (h1.continuousOn.continuousAt (hV.mem_nhds hz)).sub
      (h2.continuousOn.continuousAt (hV.mem_nhds hz))
  have hmem : ∀ u ∈ V, g₁ u - g₂ u ∈ L.lattice := fun u hu => (Submodule.Quotient.eq _).1 (h u hu)
  have hev : ∀ᶠ u in 𝓝 z, g₁ u - g₂ u ∈ ((L.lattice : Set ℂ) \ {g₁ z - g₂ z})ᶜ :=
    hc.preimage_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds _)
  have hev2 : ∀ᶠ u in 𝓝 z, g₁ u = g₂ u + (g₁ z - g₂ z) := by
    filter_upwards [hev, hV.mem_nhds hz] with u hu huV
    by_contra hne
    apply hu
    refine ⟨hmem u huV, ?_⟩
    intro e
    apply hne
    rw [Set.mem_singleton_iff] at e
    linear_combination e
  rw [Filter.EventuallyEq.deriv_eq hev2, deriv_add_const]

/-- Proposition 3.3 (Milne, pdf p. 99), first part: for `αΛ ⊆ Λ'`, `[z] ↦ [αz]` is a holomorphic
map `ℂ/Λ → ℂ/Λ'` sending `0` to `0`. -/
@[kb "milne2006ec" "Ch. III, Prop. 3.3, pdf p. 99"]
theorem prop_3_3_holomorphic {Λ Λ' : Submodule ℤ ℂ} (α : ℂ) (h : ∀ x ∈ Λ, α * x ∈ Λ') :
    IsHolomorphicMap Λ Λ' (mulMap α h) ∧ mulMap α h 0 = 0 := by
  refine ⟨fun z => ⟨univ, univ_mem, fun u => α * u, ?_, fun u _ => rfl⟩, ?_⟩
  · exact (differentiable_id.const_mul α).differentiableOn
  · rw [← Submodule.Quotient.mk_zero Λ, mulMap_mk, mul_zero]; rfl

/-- Proposition 3.3 (Milne, pdf p. 99), second part: every holomorphic map `ℂ/Λ → ℂ/Λ'` sending
`0` to `0` is `[z] ↦ [αz]` for a unique `α` with `αΛ ⊆ Λ'`. -/
@[kb "milne2006ec" "Ch. III, Prop. 3.3, pdf p. 99"]
theorem prop_3_3 {Λ Λ' : Submodule ℤ ℂ} (hΛ : IsLattice Λ) (hΛ' : IsLattice Λ')
    (φ : ℂ ⧸ Λ → ℂ ⧸ Λ') (hφ : IsHolomorphicMap Λ Λ' φ) (h0 : φ 0 = 0) :
    ∃! α : ℂ, ∃ h : ∀ x ∈ Λ, α * x ∈ Λ', ⇑(mulMap α h) = φ := by
  obtain ⟨L, rfl⟩ := hΛ'
  obtain ⟨M, rfl⟩ := hΛ
  choose U hUo hzU G hGd hG using exists_open_lift hφ
  set h : ℂ → ℂ := fun z => deriv (G z) z with hh
  have hderiv : ∀ z, ∀ u ∈ U z, deriv (G z) u = h u := by
    intro z u hu
    exact deriv_eq_of_lift L ((hUo z).inter (hUo u)) ⟨hu, hzU u⟩
      ((hGd z).mono inter_subset_left) ((hGd u).mono inter_subset_right)
      (fun v hv => by rw [hG z v hv.1, hG u v hv.2])
  have hloc : ∀ z, h =ᶠ[𝓝 z] deriv (G z) := fun z => by
    filter_upwards [(hUo z).mem_nhds (hzU z)] with u hu
    exact (hderiv z u hu).symm
  have hdiff : Differentiable ℂ h := fun z => by
    have : DifferentiableAt ℂ (deriv (G z)) z :=
      ((hGd z).deriv (hUo z)).differentiableAt ((hUo z).mem_nhds (hzU z))
    exact (this.congr_of_eventuallyEq (hloc z))
  have hper : ∀ z w, w ∈ M.lattice → h (z + w) = h z := by
    intro z ω hω
    have hmk : ∀ u : ℂ, (Submodule.Quotient.mk (u + ω) : ℂ ⧸ M.lattice) = Submodule.Quotient.mk u :=
      fun u => (Submodule.Quotient.eq _).2 (by simpa using M.lattice.neg_mem hω)
    have hV : IsOpen ((fun u => u + ω) ⁻¹' U (z + ω)) :=
      (hUo (z + ω)).preimage (continuous_id.add continuous_const)
    have hzV : z ∈ (fun u => u + ω) ⁻¹' U (z + ω) := hzU (z + ω)
    have hg' : DifferentiableOn ℂ (fun u => G (z + ω) (u + ω)) ((fun u => u + ω) ⁻¹' U (z + ω)) :=
      (hGd (z + ω)).comp (differentiable_id.add_const ω).differentiableOn (fun u hu => hu)
    have := deriv_eq_of_lift L (hV.inter (hUo z)) ⟨hzV, hzU z⟩
      (hg'.mono inter_subset_left) ((hGd z).mono inter_subset_right)
      (fun v hv => by rw [hG (z + ω) (v + ω) hv.1, hG z v hv.2, hmk])
    rw [deriv_comp_add_const] at this
    exact (hderiv (z + ω) (z + ω) (hzU _)).symm.trans (this.trans (hderiv z z (hzU z)))
  have hbdd : Bornology.IsBounded (Set.range h) :=
    (IsZLattice.isCompact_range_of_periodic M.lattice h hdiff.continuous hper).isBounded
  have hconst : ∀ z, h z = h 0 := fun z => hdiff.apply_eq_apply_of_bounded hbdd z 0
  set α := h 0 with hα
  have hlc : IsLocallyConstant (fun z : ℂ =>
      φ (Submodule.Quotient.mk z) - (Submodule.Quotient.mk (α * z) : ℂ ⧸ L.lattice)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hUo z) z (hzU z)
    have hf : DifferentiableOn ℂ (fun u => G z u - α * u) (Metric.ball z ε) :=
      ((hGd z).mono hball).sub (differentiable_id.const_mul α).differentiableOn
    have hf0 : (Metric.ball z ε).EqOn (deriv fun u => G z u - α * u) 0 := by
      intro u hu
      have hd : DifferentiableAt ℂ (G z) u :=
        (hGd z).differentiableAt ((hUo z).mem_nhds (hball hu))
      have : deriv (fun u => G z u - α * u) u = deriv (G z) u - α := by
        have hd2 : DifferentiableAt ℂ (fun u => α * u) u := by fun_prop
        rw [deriv_fun_sub hd hd2]
        simp
      rw [this, hderiv z u (hball hu), hconst u]
      simp
    filter_upwards [Metric.ball_mem_nhds z hε] with u hu
    have := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z ε).isPreconnected hf hf0
      hu (Metric.mem_ball_self hε)
    rw [← hG z u (hball hu), ← hG z z (hzU z), ← Submodule.Quotient.mk_sub,
      ← Submodule.Quotient.mk_sub, this]
  have hφeq : ∀ z : ℂ, φ (Submodule.Quotient.mk z) = Submodule.Quotient.mk (α * z) := by
    intro z
    have := hlc.apply_eq_of_preconnectedSpace z 0
    simp only [mul_zero, Submodule.Quotient.mk_zero, h0, sub_zero] at this
    exact sub_eq_zero.1 this
  have hαΛ : ∀ x ∈ M.lattice, α * x ∈ L.lattice := by
    intro x hx
    have h1 := hφeq x
    rw [(Submodule.Quotient.mk_eq_zero _).2 hx, h0] at h1
    exact (Submodule.Quotient.mk_eq_zero _).1 h1.symm
  refine ⟨α, ⟨hαΛ, ?_⟩, ?_⟩
  · funext q
    induction q using Submodule.Quotient.induction_on with
    | H z => exact (hφeq z).symm
  · rintro β ⟨hβ, hβφ⟩
    by_contra hne
    have hsub : β - α ≠ 0 := sub_ne_zero.2 hne
    have key : ∀ z : ℂ, (β - α) * z ∈ L.lattice := by
      intro z
      have := congr_fun hβφ (Submodule.Quotient.mk z)
      rw [mulMap_mk, hφeq] at this
      have := (Submodule.Quotient.eq _).1 this
      rwa [← sub_mul] at this
    apply L.ω₁_div_two_notMem_lattice
    have := key (L.ω₁ / 2 / (β - α))
    rwa [mul_div_cancel₀ _ hsub] at this

private theorem mulMap_injective {Λ Λ' : Submodule ℤ ℂ} (hΛ' : IsLattice Λ') {α β : ℂ}
    {h : ∀ x ∈ Λ, α * x ∈ Λ'} {h' : ∀ x ∈ Λ, β * x ∈ Λ'}
    (e : ⇑(mulMap α h) = ⇑(mulMap β h')) : α = β := by
  obtain ⟨L, rfl⟩ := hΛ'
  by_contra hne
  have hsub : α - β ≠ 0 := sub_ne_zero.2 hne
  have key : ∀ z : ℂ, (α - β) * z ∈ L.lattice := by
    intro z
    have := congr_fun e (Submodule.Quotient.mk z)
    rw [mulMap_mk, mulMap_mk] at this
    have := (Submodule.Quotient.eq _).1 this
    rwa [← sub_mul] at this
  apply L.ω₁_div_two_notMem_lattice
  have := key (L.ω₁ / 2 / (α - β))
  rwa [mul_div_cancel₀ _ hsub] at this

private theorem hol_sub_const {Λ Λ' : Submodule ℤ ℂ} {φ : ℂ ⧸ Λ → ℂ ⧸ Λ'}
    (hφ : IsHolomorphicMap Λ Λ' φ) (c : ℂ) :
    IsHolomorphicMap Λ Λ' (fun q => φ q - Submodule.Quotient.mk c) := by
  intro z
  obtain ⟨U, hU, g, hg, h⟩ := hφ z
  exact ⟨U, hU, fun u => g u - c, hg.sub_const c, fun u hu => by
    rw [Submodule.Quotient.mk_sub, h u hu]⟩

private theorem hol_comp_add_const {Λ Λ' : Submodule ℤ ℂ} {φ : ℂ ⧸ Λ' → ℂ ⧸ Λ}
    (hφ : IsHolomorphicMap Λ' Λ φ) (c : ℂ) :
    IsHolomorphicMap Λ' Λ (fun q => φ (q + Submodule.Quotient.mk c)) := by
  intro z
  obtain ⟨U, hU, g, hg, h⟩ := hφ (z + c)
  refine ⟨(fun u => u + c) ⁻¹' U,
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds hU,
    fun u => g (u + c), hg.comp (differentiable_id.add_const c).differentiableOn (fun u hu => hu),
    fun u hu => ?_⟩
  rw [h (u + c) hu, Submodule.Quotient.mk_add]

/-- Corollary 3.4 (Milne, pdf p. 99): `ℂ/Λ` and `ℂ/Λ'` are isomorphic Riemann surfaces if and only
if `Λ' = αΛ` for some `α ∈ ℂ^×`. -/
@[kb "milne2006ec" "Ch. III, Cor. 3.4, pdf p. 99"]
theorem cor_3_4 {Λ Λ' : Submodule ℤ ℂ} (hΛ : IsLattice Λ) (hΛ' : IsLattice Λ') :
    (∃ φ : ℂ ⧸ Λ ≃ ℂ ⧸ Λ', IsBiholomorphic Λ Λ' φ) ↔ ∃ α : ℂ, α ≠ 0 ∧ Λ' = α • Λ := by
  constructor
  · rintro ⟨φ, hφ, hφ'⟩
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective Λ' (φ 0)
    have h1 : IsHolomorphicMap Λ Λ' (fun q => φ q - Submodule.Quotient.mk c) := hol_sub_const hφ c
    have h2 : IsHolomorphicMap Λ' Λ (fun q => φ.symm (q + Submodule.Quotient.mk c)) :=
      hol_comp_add_const hφ' c
    have e1 : (fun q => φ q - (Submodule.Quotient.mk c : ℂ ⧸ Λ')) 0 = 0 := by
      simp [hc]
    have e2 : (fun q => φ.symm (q + (Submodule.Quotient.mk c : ℂ ⧸ Λ'))) 0 = 0 := by
      simp only [zero_add, hc]; simp
    obtain ⟨α, ⟨hα, hαφ⟩, -⟩ := prop_3_3 hΛ hΛ' _ h1 e1
    obtain ⟨β, ⟨hβ, hβφ⟩, -⟩ := prop_3_3 hΛ' hΛ _ h2 e2
    have hcomp : ∀ q : ℂ ⧸ Λ, mulMap β hβ (mulMap α hα q) = q := by
      intro q
      show ⇑(mulMap β hβ) (⇑(mulMap α hα) q) = q
      rw [hαφ, hβφ]
      simp
    have hone : (⇑(mulMap (β * α) (fun x hx => by simpa [mul_assoc] using hβ _ (hα x hx))) :
        ℂ ⧸ Λ → ℂ ⧸ Λ) = ⇑(mulMap (1 : ℂ) (fun x hx => by simpa using hx)) := by
      funext q
      induction q using Submodule.Quotient.induction_on with
      | H z =>
        have := hcomp (Submodule.Quotient.mk z)
        simpa [mul_assoc] using this
    have hβα : β * α = 1 := mulMap_injective hΛ hone
    have hα0 : α ≠ 0 := by rintro rfl; simp at hβα
    refine ⟨α, hα0, le_antisymm ?_ ?_⟩
    · intro x hx
      rw [Submodule.mem_smul_pointwise_iff_exists]
      refine ⟨β * x, hβ x hx, ?_⟩
      rw [smul_eq_mul, ← mul_assoc, mul_comm α β, hβα, one_mul]
    · intro x hx
      obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      exact hα b hb
  · rintro ⟨α, hα0, rfl⟩
    have hα : ∀ x ∈ Λ, α * x ∈ α • Λ := fun x hx =>
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx, rfl⟩
    have hβ : ∀ x ∈ α • Λ, α⁻¹ * x ∈ Λ := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      simpa [hα0] using hb
    refine ⟨{ toFun := mulMap α hα, invFun := mulMap α⁻¹ hβ, left_inv := ?_, right_inv := ?_ },
      (prop_3_3_holomorphic α hα).1, (prop_3_3_holomorphic α⁻¹ hβ).1⟩
    · intro q
      induction q using Submodule.Quotient.induction_on with
      | H z => simp [hα0]
    · intro q
      induction q using Submodule.Quotient.induction_on with
      | H z => simp [hα0]

/-- Corollary 3.5 (Milne, pdf p. 99): every holomorphic map `ℂ/Λ → ℂ/Λ'` sending `0` to `0` is a
homomorphism of groups. -/
@[kb "milne2006ec" "Ch. III, Cor. 3.5, pdf p. 99"]
theorem cor_3_5 {Λ Λ' : Submodule ℤ ℂ} (hΛ : IsLattice Λ) (hΛ' : IsLattice Λ')
    (φ : ℂ ⧸ Λ → ℂ ⧸ Λ') (hφ : IsHolomorphicMap Λ Λ' φ) (h0 : φ 0 = 0) (x y : ℂ ⧸ Λ) :
    φ (x + y) = φ x + φ y := by
  obtain ⟨α, ⟨h, rfl⟩, -⟩ := prop_3_3 hΛ hΛ' φ hφ h0
  exact map_add (mulMap α h) x y

/-! ### Endomorphisms (Proposition 3.17) -/

/-- `{α ∈ ℂ | αΛ ⊆ Λ}`, the endomorphism ring of the Riemann surface `ℂ/Λ` (Proposition 3.3 with
`Λ' = Λ`; Milne, pdf p. 99: `Hom(ℂ/Λ, ℂ/Λ') ≅ {α ∈ ℂ | αΛ ⊆ Λ'}`). -/
@[kb "milne2006ec" "Ch. III, §3, Hom(C/Λ, C/Λ') ≅ {α | αΛ ⊆ Λ'}, pdf p. 99"]
def endRing (Λ : Submodule ℤ ℂ) : Subring ℂ where
  carrier := {α | ∀ x ∈ Λ, α * x ∈ Λ}
  mul_mem' {a b} ha hb x hx := by rw [mul_assoc]; exact ha _ (hb x hx)
  one_mem' x hx := by rwa [one_mul]
  add_mem' {a b} ha hb x hx := by rw [add_mul]; exact Λ.add_mem (ha x hx) (hb x hx)
  zero_mem' x _ := by rw [zero_mul]; exact Λ.zero_mem
  neg_mem' {a} ha x hx := by rw [neg_mul]; exact Λ.neg_mem (ha x hx)

/-- The endomorphisms of `ℂ/Λ` fixing `0` are exactly the maps `[z] ↦ [αz]`, `α ∈ endRing Λ`
(Proposition 3.3 for `Λ' = Λ`). -/
theorem holomorphic_endo_iff {Λ : Submodule ℤ ℂ} (hΛ : IsLattice Λ) (φ : ℂ ⧸ Λ → ℂ ⧸ Λ) :
    (IsHolomorphicMap Λ Λ φ ∧ φ 0 = 0) ↔ ∃ α ∈ endRing Λ, ∃ h, ⇑(mulMap (Λ := Λ) α h) = φ := by
  constructor
  · rintro ⟨hφ, h0⟩
    obtain ⟨α, ⟨h, hαφ⟩, -⟩ := prop_3_3 hΛ hΛ φ hφ h0
    exact ⟨α, h, h, hαφ⟩
  · rintro ⟨α, -, h, rfl⟩
    exact prop_3_3_holomorphic α h

private theorem OrientedPair.ω₂_ne_zero (p : OrientedPair) : p.1.2 ≠ 0 := by
  intro h
  have := p.2
  simp [h] at this

private theorem OrientedPair.mem_lattice_iff (p : OrientedPair) (z : ℂ) :
    z ∈ p.lattice ↔ ∃ m n : ℤ, z = p.1.2 * (m * (p.1.1 / p.1.2) + n) := by
  have h2 := p.ω₂_ne_zero
  unfold OrientedPair.lattice
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m, n, ?_⟩
    simp only [zsmul_eq_mul]
    field_simp
  · rintro ⟨m, n, rfl⟩
    refine ⟨m, n, ?_⟩
    simp only [zsmul_eq_mul]
    field_simp

private theorem endRing_char (p : OrientedPair) {α : ℂ} (hα : α ∈ endRing p.lattice) :
    ∃ m n a b : ℤ, α = m * (p.1.1 / p.1.2) + n ∧
      α * (p.1.1 / p.1.2) = a * (p.1.1 / p.1.2) + b := by
  have h2 := p.ω₂_ne_zero
  have hω₂ : p.1.2 ∈ p.lattice := Submodule.subset_span (by simp)
  have hω₁ : p.1.1 ∈ p.lattice := Submodule.subset_span (by simp)
  obtain ⟨m, n, h1⟩ := (p.mem_lattice_iff _).1 (hα _ hω₂)
  obtain ⟨a, b, h3⟩ := (p.mem_lattice_iff _).1 (hα _ hω₁)
  have hτ : p.1.2 * (p.1.1 / p.1.2) = p.1.1 := by field_simp
  refine ⟨m, n, a, b, ?_, ?_⟩
  · exact mul_left_cancel₀ h2 (by linear_combination h1)
  · exact mul_left_cancel₀ h2 (by linear_combination h3 + α * hτ)

private theorem endRing_integral (p : OrientedPair) {α : ℂ} (hα : α ∈ endRing p.lattice) :
    IsIntegral ℤ α := by
  obtain ⟨m, n, a, b, h1, h2⟩ := endRing_char p hα
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (a + n : ℤ) * Polynomial.X +
    Polynomial.C (n * a - m * b : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp only [eq_intCast]
  push_cast
  linear_combination (α - a) * h1 + m * h2

private theorem finrank_eq_two_of_rat_quad (p : OrientedPair) (q₂ q₁ q₀ : ℚ) (hq : q₂ ≠ 0)
    (h : (q₂ : ℂ) * (p.1.1 / p.1.2) ^ 2 + q₁ * (p.1.1 / p.1.2) + q₀ = 0) :
    Module.finrank ℚ ℚ⟮p.1.1 / p.1.2⟯ = 2 := by
  set τ := p.1.1 / p.1.2 with hτ
  have him : 0 < τ.im := p.2
  let P : Polynomial ℚ := Polynomial.C q₂ * Polynomial.X ^ 2 +
    Polynomial.C q₁ * Polynomial.X + Polynomial.C q₀
  have hP0 : P ≠ 0 := by
    intro h0
    have := congrArg (fun q => q.coeff 2) h0
    simp [P] at this
    exact hq this
  have hPτ : Polynomial.aeval τ P = 0 := by
    simpa [P] using h
  have hint : IsIntegral ℚ τ := (show IsAlgebraic ℚ τ from ⟨P, hP0, hPτ⟩).isIntegral
  rw [IntermediateField.adjoin.finrank hint]
  have hle : (minpoly ℚ τ).natDegree ≤ 2 := by
    have h1 := minpoly.degree_le_of_ne_zero ℚ τ hP0 hPτ
    have hdeg : P.degree ≤ 2 := by
      simp only [P]
      compute_degree
    exact Polynomial.natDegree_le_of_degree_le (h1.trans hdeg)
  have hpos := minpoly.natDegree_pos hint
  have hne : (minpoly ℚ τ).natDegree ≠ 1 := by
    intro h1
    obtain ⟨q, hq⟩ := (minpoly.natDegree_eq_one_iff).1 h1
    rw [← hq] at him
    simp at him
  omega

private theorem finrank_eq_two_of_quad (p : OrientedPair) (m n a b : ℤ) (hm : m ≠ 0)
    (h : (m : ℂ) * (p.1.1 / p.1.2) ^ 2 + (n - a) * (p.1.1 / p.1.2) - b = 0) :
    Module.finrank ℚ ℚ⟮p.1.1 / p.1.2⟯ = 2 :=
  finrank_eq_two_of_rat_quad p m (n - a : ℤ) (-b : ℤ) (by exact_mod_cast hm)
    (by push_cast; linear_combination h)

private theorem exists_quad_of_finrank (p : OrientedPair)
    (h : Module.finrank ℚ ℚ⟮p.1.1 / p.1.2⟯ = 2) :
    ∃ A B C : ℤ, 0 < A ∧ (A : ℂ) * (p.1.1 / p.1.2) ^ 2 + B * (p.1.1 / p.1.2) + C = 0 := by
  set τ := p.1.1 / p.1.2 with hτ
  have hfin : Module.Finite ℚ ℚ⟮τ⟯ := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral ℚ τ :=
    IntermediateField.isIntegral_iff.1
      (Algebra.IsIntegral.isIntegral (⟨τ, IntermediateField.mem_adjoin_simple_self ℚ τ⟩ : ℚ⟮τ⟯))
  rw [IntermediateField.adjoin.finrank hint] at h
  have hc2 : (minpoly ℚ τ).coeff 2 = 1 := by
    have := (minpoly.monic hint).coeff_natDegree
    rwa [h] at this
  have hroot := minpoly.aeval ℚ τ
  rw [Polynomial.aeval_eq_sum_range' (n := 3) (by omega)] at hroot
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc2] at hroot
  set u := (minpoly ℚ τ).coeff 1
  set v := (minpoly ℚ τ).coeff 0
  have key : τ ^ 2 + (u : ℂ) * τ + (v : ℂ) = 0 := by
    simp only [Algebra.smul_def, eq_ratCast, map_one] at hroot
    simp at hroot
    linear_combination hroot
  have hu : (u : ℂ) * (u.den : ℂ) = (u.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num u
  have hv : (v : ℂ) * (v.den : ℂ) = (v.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num v
  refine ⟨(u.den : ℤ) * v.den, (v.den : ℤ) * u.num, (u.den : ℤ) * v.num,
    by have := u.den_pos; have := v.den_pos; positivity, ?_⟩
  push_cast
  linear_combination ((u.den : ℂ) * v.den) * key - ((v.den : ℂ) * τ) * hu - (u.den : ℂ) * hv

/-- Proposition 3.17 (Milne, pdf p. 105): let `Λ = ℤω₁ + ℤω₂` with `τ = ω₁/ω₂ ∈ ℍ`.  The
endomorphism ring of `ℂ/Λ` is `ℤ` unless `[ℚ(τ) : ℚ] = 2`, in which case it is a subring of `ℚ(τ)`
of rank `2` as a `ℤ`-module, consisting of algebraic integers (Milne's proof: it lies in the ring
of integers of `ℚ(τ)`). -/
@[kb "milne2006ec" "Ch. III, Prop. 3.17, pdf p. 105"]
theorem prop_3_17 (p : OrientedPair) :
    (Module.finrank ℚ ℚ⟮p.1.1 / p.1.2⟯ ≠ 2 → endRing p.lattice = ⊥) ∧
      (Module.finrank ℚ ℚ⟮p.1.1 / p.1.2⟯ = 2 →
        (∀ α ∈ endRing p.lattice, α ∈ ℚ⟮p.1.1 / p.1.2⟯ ∧ IsIntegral ℤ α) ∧
          Module.finrank ℤ (endRing p.lattice) = 2) := by
  have h2 := p.ω₂_ne_zero
  set τ := p.1.1 / p.1.2 with hτ
  have him : 0 < τ.im := p.2
  constructor
  · intro hne
    rw [eq_bot_iff]
    intro α hα
    obtain ⟨m, n, a, b, h1, h3⟩ := endRing_char p hα
    have hm : m = 0 := by
      by_contra hm
      apply hne
      apply finrank_eq_two_of_quad p m n a b hm
      linear_combination h3 - τ * h1
    rw [Subring.mem_bot]
    exact ⟨n, by rw [h1, hm]; simp⟩
  · intro hfin
    refine ⟨fun α hα => ⟨?_, endRing_integral p hα⟩, ?_⟩
    · obtain ⟨m, n, a, b, h1, -⟩ := endRing_char p hα
      rw [h1]
      exact add_mem (mul_mem (intCast_mem _ m) (IntermediateField.mem_adjoin_simple_self _ _))
        (intCast_mem _ n)
    · obtain ⟨A, B, C, hA, hq⟩ := exists_quad_of_finrank p hfin
      let L := p.toPeriodPair
      have hω₂ : p.1.2 ∈ p.lattice := Submodule.subset_span (by simp)
      let Φ : endRing p.lattice →ₗ[ℤ] L.lattice :=
        { toFun := fun x => ⟨(x : ℂ) * p.1.2, x.2 p.1.2 hω₂⟩
          map_add' := fun x y => by
            apply Subtype.ext
            show ((x + y : endRing p.lattice) : ℂ) * p.1.2 = (x : ℂ) * p.1.2 + (y : ℂ) * p.1.2
            push_cast; ring
          map_smul' := fun r x => by
            apply Subtype.ext
            show ((r • x : endRing p.lattice) : ℂ) * p.1.2 = r • ((x : ℂ) * p.1.2)
            simp [zsmul_eq_mul, mul_assoc] }
      have hΦ : Function.Injective Φ := by
        intro x y hxy
        apply Subtype.ext
        have := congrArg Subtype.val hxy
        exact mul_right_cancel₀ h2 this
      have hfinR : Module.Finite ℤ (endRing p.lattice) := Module.Finite.of_injective Φ hΦ
      have hle : Module.finrank ℤ (endRing p.lattice) ≤ 2 := by
        have := LinearMap.finrank_le_finrank_of_injective hΦ
        rwa [L.finrank_lattice] at this
      have hmem : (A : ℂ) * τ ∈ endRing p.lattice := by
        intro x hx
        obtain ⟨m, n, rfl⟩ := (p.mem_lattice_iff x).1 hx
        refine (p.mem_lattice_iff _).2 ⟨-m * B + n * A, -m * C, ?_⟩
        push_cast
        linear_combination (p.1.2 * m) * hq
      have hli : LinearIndependent ℤ ![(1 : endRing p.lattice), ⟨(A : ℂ) * τ, hmem⟩] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        have h1 := congrArg Subtype.val hst
        have h2 : (s : ℂ) + t * ((A : ℂ) * τ) = 0 := by
          simpa [zsmul_eq_mul] using h1
        have h3 := congrArg Complex.im h2
        simp at h3
        have ht : t = 0 := by
          rcases h3 with h3 | h3 | h3
          · exact_mod_cast h3
          · omega
          · exact absurd h3 him.ne'
        subst ht
        refine ⟨?_, rfl⟩
        simpa using h2
      have hge := hli.fintype_card_le_finrank
      simp at hge
      omega

/-! ### Lemma 3.20 -/

/-- Lemma 3.20 (a) (Milne, pdf p. 106): for a `ℤ`-linear endomorphism `α` of a free `ℤ`-module of
finite rank with `det α ≠ 0`, the cokernel of `α` is finite of order `|det α|`. -/
@[kb "milne2006ec" "Ch. III, Lemma 3.20 (a), pdf p. 106"]
theorem lemma_3_20_a {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (α : M →ₗ[ℤ] M) (hα : LinearMap.det α ≠ 0) :
    Finite (M ⧸ LinearMap.range α) ∧ Nat.card (M ⧸ LinearMap.range α) = (LinearMap.det α).natAbs := by
  have hinj : Function.Injective α :=
    LinearMap.ker_eq_bot.1 (by
      by_contra h
      exact hα (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h))
  let e : M ≃ₗ[ℤ] LinearMap.range α := LinearEquiv.ofInjective α hinj
  have key := Submodule.natAbs_det_equiv (LinearMap.range α) e.toAddEquiv
  have hα' : (LinearMap.range α).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((e.toAddEquiv : M ≃+ LinearMap.range α) : M →+ LinearMap.range α)
      = α := by
    ext x; rfl
  rw [hα'] at key
  refine ⟨?_, key.symm⟩
  exact Nat.finite_of_card_ne_zero (by rw [← key]; exact Int.natAbs_ne_zero.2 hα)

/-- The image of `Λ` in `Λ ⊗ ℚ` (as `ℚ ⊗[ℤ] Λ`), `λ ↦ 1 ⊗ λ`. -/
noncomputable def latticeInTensor (M : Type*) [AddCommGroup M] : AddSubgroup (ℚ ⊗[ℤ] M) :=
  (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom.range

/-- The map `α̃ : (Λ ⊗ ℚ)/Λ → (Λ ⊗ ℚ)/Λ` induced by `α` (Lemma 3.20 (b)). -/
noncomputable def tensorQuotMap {M : Type*} [AddCommGroup M] (α : M →ₗ[ℤ] M) :
    (ℚ ⊗[ℤ] M) ⧸ latticeInTensor M →+ (ℚ ⊗[ℤ] M) ⧸ latticeInTensor M :=
  QuotientAddGroup.map _ _ (LinearMap.baseChange ℚ α).toAddMonoidHom (by
    rintro _ ⟨m, rfl⟩
    exact ⟨α m, by simp [LinearMap.baseChange_tmul]⟩)

/-- Lemma 3.20 (b) (Milne, pdf p. 107): the kernel of `α̃ : (Λ ⊗ ℚ)/Λ → (Λ ⊗ ℚ)/Λ` is finite of
order `|det α|`. -/
@[kb "milne2006ec" "Ch. III, Lemma 3.20 (b), pdf p. 107"]
theorem lemma_3_20_b {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (α : M →ₗ[ℤ] M) (hα : LinearMap.det α ≠ 0) :
    Finite (tensorQuotMap α).ker ∧
      Nat.card (tensorQuotMap α).ker = (LinearMap.det α).natAbs := by
  classical
  let i : M →ₗ[ℤ] ℚ ⊗[ℤ] M := TensorProduct.mk ℤ ℚ M 1
  have hi : Function.Injective i := by
    have h1 : Function.Injective (LinearMap.rTensor M (Algebra.linearMap ℤ ℚ)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap ℤ ℚ).injective_int
    intro a b hab
    have : (TensorProduct.lid ℤ M).symm a = (TensorProduct.lid ℤ M).symm b := by
      apply h1
      have hab' : (1 : ℚ) ⊗ₜ[ℤ] a = (1 : ℚ) ⊗ₜ[ℤ] b := hab
      simpa using hab'
    exact (TensorProduct.lid ℤ M).symm.injective this
  let αQ : (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℚ ⊗[ℤ] M) := LinearMap.baseChange ℚ α
  have hdet : LinearMap.det αQ ≠ 0 := by
    rw [LinearMap.det_baseChange]
    simpa using hα
  have hαQinj : Function.Injective αQ :=
    LinearMap.ker_eq_bot.1 (by
      by_contra h
      exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h))
  have hαQ : Function.Bijective αQ := ⟨hαQinj, LinearMap.injective_iff_surjective.1 hαQinj⟩
  let β : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] M) := LinearEquiv.ofBijective αQ hαQ
  have hαi : ∀ m, αQ (i m) = i (α m) := fun m => by
    show LinearMap.baseChange ℚ α ((1 : ℚ) ⊗ₜ[ℤ] m) = (1 : ℚ) ⊗ₜ[ℤ] α m
    rfl
  have hmem : ∀ m, i m ∈ latticeInTensor M := fun m => ⟨m, rfl⟩
  have hker : ∀ t : ℚ ⊗[ℤ] M, tensorQuotMap α (QuotientAddGroup.mk t) = 0 ↔
      αQ t ∈ latticeInTensor M := fun t => QuotientAddGroup.eq_zero_iff _
  let Φ : M →ₗ[ℤ] (tensorQuotMap α).ker :=
    { toFun := fun m => ⟨QuotientAddGroup.mk (β.symm (i m)), by
        rw [AddMonoidHom.mem_ker, hker]
        have : αQ (β.symm (i m)) = i m := β.apply_symm_apply (i m)
        rw [this]; exact hmem m⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp [QuotientAddGroup.mk_add]
      map_smul' := fun r a => by
        apply Subtype.ext
        simp }
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨q, hq⟩
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [AddMonoidHom.mem_ker, hker] at hq
    obtain ⟨m, hm⟩ := hq
    refine ⟨m, Subtype.ext ?_⟩
    have : β.symm (i m) = t := by
      apply β.injective
      rw [β.apply_symm_apply]
      exact hm
    show QuotientAddGroup.mk (β.symm (i m)) = QuotientAddGroup.mk t
    rw [this]
  have hΦker : LinearMap.ker Φ = LinearMap.range α := by
    ext m
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro h
      have h1 : (QuotientAddGroup.mk (β.symm (i m)) : (ℚ ⊗[ℤ] M) ⧸ latticeInTensor M) = 0 :=
        congrArg Subtype.val h
      obtain ⟨m', hm'⟩ := (QuotientAddGroup.eq_zero_iff _).1 h1
      refine ⟨m', hi ?_⟩
      rw [← hαi]
      have : i m' = β.symm (i m) := hm'
      rw [this]
      exact β.apply_symm_apply (i m)
    · rintro ⟨m', rfl⟩
      apply Subtype.ext
      have : β.symm (i (α m')) = i m' := by
        apply β.injective
        rw [β.apply_symm_apply]
        exact (hαi m').symm
      show (QuotientAddGroup.mk (β.symm (i (α m'))) : (ℚ ⊗[ℤ] M) ⧸ latticeInTensor M) = 0
      rw [this]
      exact (QuotientAddGroup.eq_zero_iff _).2 (hmem m')
  let E : (M ⧸ LinearMap.range α) ≃ₗ[ℤ] (tensorQuotMap α).ker :=
    (Submodule.quotEquivOfEq _ _ hΦker.symm).trans (Φ.quotKerEquivOfSurjective hΦsurj)
  obtain ⟨hfin, hcard⟩ := lemma_3_20_a α hα
  have := hfin
  exact ⟨Finite.of_equiv _ E.toEquiv, by rw [← Nat.card_congr E.toEquiv, hcard]⟩

/-! ### The degree of an endomorphism (Proposition 3.21) -/

instance (L : PeriodPair) : Module.Free ℤ L.lattice := .of_basis L.latticeBasis
instance (L : PeriodPair) : Module.Finite ℤ L.lattice := .of_basis L.latticeBasis

/-- Multiplication by `α ∈ endRing Λ` as a `ℤ`-linear endomorphism of `Λ`. -/
noncomputable def latticeEndo {Λ : Submodule ℤ ℂ} (α : endRing Λ) : Λ →ₗ[ℤ] Λ :=
  (LinearMap.mulLeft ℤ (α : ℂ)).restrict fun x hx => α.2 x hx

/-- The endomorphism `[z] ↦ [αz]` of `ℂ/Λ`, `α ∈ endRing Λ`. -/
noncomputable def endoMap {Λ : Submodule ℤ ℂ} (α : endRing Λ) : ℂ ⧸ Λ →ₗ[ℤ] ℂ ⧸ Λ :=
  mulMap (α : ℂ) α.2

/-- Milne's degree of a nonzero endomorphism of `E(ℂ) = ℂ/Λ` (pdf p. 107): the order of its
kernel (see the module docstring). -/
@[kb "milne2006ec" "Ch. III, §3, degree of an endomorphism of C/Λ, pdf p. 107"]
noncomputable def degree {Λ : Submodule ℤ ℂ} (α : endRing Λ) : ℕ :=
  Nat.card (LinearMap.ker (endoMap α))

private theorem toMatrix_compat (L : PeriodPair) (F : ℂ →ₗ[ℝ] ℂ) (f : L.lattice →ₗ[ℤ] L.lattice)
    (h : ∀ x : L.lattice, F x = f x) :
    LinearMap.toMatrix (L.latticeBasis.ofZLatticeBasis ℝ L.lattice)
        (L.latticeBasis.ofZLatticeBasis ℝ L.lattice) F =
      (LinearMap.toMatrix L.latticeBasis L.latticeBasis f).map (Int.castRingHom ℝ) := by
  ext i j
  simp [LinearMap.toMatrix_apply, h]

theorem det_latticeEndo_cast (L : PeriodPair) (α : endRing L.lattice) :
    ((LinearMap.det (latticeEndo α) : ℤ) : ℝ) = Complex.normSq (α : ℂ) := by
  rw [← Algebra.norm_complex_apply, Algebra.norm_apply,
    ← LinearMap.det_toMatrix (L.latticeBasis.ofZLatticeBasis ℝ L.lattice),
    toMatrix_compat L (Algebra.lmul ℝ ℂ (α : ℂ)) (latticeEndo α) (fun x => rfl),
    ← LinearMap.det_toMatrix L.latticeBasis]
  exact (RingHom.map_det (Int.castRingHom ℝ)
    (LinearMap.toMatrix L.latticeBasis L.latticeBasis (latticeEndo α)))

theorem trace_latticeEndo_cast (L : PeriodPair) (α : endRing L.lattice) :
    ((LinearMap.trace ℤ L.lattice (latticeEndo α) : ℤ) : ℝ) = 2 * (α : ℂ).re := by
  rw [← Algebra.trace_complex_apply, Algebra.trace_apply,
    LinearMap.trace_eq_matrix_trace ℝ (L.latticeBasis.ofZLatticeBasis ℝ L.lattice),
    toMatrix_compat L (Algebra.lmul ℝ ℂ (α : ℂ)) (latticeEndo α) (fun x => rfl),
    LinearMap.trace_eq_matrix_trace ℤ L.latticeBasis]
  simp [Matrix.trace]

/-- Proposition 3.21 (Milne, pdf p. 107): the degree of a nonzero endomorphism `α` of `ℂ/Λ` is the
determinant of `α` acting on `Λ` (in particular the kernel is finite and the determinant is
positive). -/
@[kb "milne2006ec" "Ch. III, Prop. 3.21, pdf p. 107"]
theorem prop_3_21 (L : PeriodPair) (α : endRing L.lattice) (hα : α ≠ 0) :
    Finite (LinearMap.ker (endoMap α)) ∧ (degree α : ℤ) = LinearMap.det (latticeEndo α) := by
  have hα0 : (α : ℂ) ≠ 0 := fun h => hα (Subtype.ext h)
  have hinj : Function.Injective (latticeEndo α) := fun x y h =>
    Subtype.ext (mul_left_cancel₀ hα0 (congrArg Subtype.val h))
  have hdet : LinearMap.det (latticeEndo α) ≠ 0 := fun h =>
    LinearMap.det_eq_zero_iff_ker_ne_bot.1 h (LinearMap.ker_eq_bot.2 hinj)
  have hpos : 0 < LinearMap.det (latticeEndo α) := by
    have h1 := det_latticeEndo_cast L α
    have h2 : (0 : ℝ) < ((LinearMap.det (latticeEndo α) : ℤ) : ℝ) := by
      rw [h1]; exact Complex.normSq_pos.2 hα0
    exact_mod_cast h2
  have hmemker : ∀ x : L.lattice, endoMap α (Submodule.Quotient.mk ((α : ℂ)⁻¹ * x)) = 0 := by
    intro x
    show (Submodule.Quotient.mk ((α : ℂ) * ((α : ℂ)⁻¹ * x)) : ℂ ⧸ L.lattice) = 0
    rw [← mul_assoc, mul_inv_cancel₀ hα0, one_mul]
    exact (Submodule.Quotient.mk_eq_zero _).2 x.2
  let Θ : L.lattice →ₗ[ℤ] LinearMap.ker (endoMap α) :=
    { toFun := fun x => ⟨Submodule.Quotient.mk ((α : ℂ)⁻¹ * x), LinearMap.mem_ker.2 (hmemker x)⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp [mul_add, Submodule.Quotient.mk_add]
      map_smul' := fun r a => by
        apply Subtype.ext
        show (Submodule.Quotient.mk ((α : ℂ)⁻¹ * ((r • a : L.lattice) : ℂ)) : ℂ ⧸ L.lattice) =
          r • Submodule.Quotient.mk ((α : ℂ)⁻¹ * (a : ℂ))
        have : (α : ℂ)⁻¹ * ((r • a : L.lattice) : ℂ) = r • ((α : ℂ)⁻¹ * (a : ℂ)) := by
          rw [Submodule.coe_smul, zsmul_eq_mul, zsmul_eq_mul]; ring
        rw [this]
        rfl }
  have hΘsurj : Function.Surjective Θ := by
    rintro ⟨q, hq⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hz : (α : ℂ) * z ∈ L.lattice :=
      (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.mem_ker.1 hq)
    refine ⟨⟨(α : ℂ) * z, hz⟩, Subtype.ext ?_⟩
    show (Submodule.Quotient.mk ((α : ℂ)⁻¹ * ((α : ℂ) * z)) : ℂ ⧸ L.lattice) = Submodule.Quotient.mk z
    rw [← mul_assoc, inv_mul_cancel₀ hα0, one_mul]
  have hΘker : LinearMap.ker Θ = LinearMap.range (latticeEndo α) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro h
      have h1 : (Submodule.Quotient.mk ((α : ℂ)⁻¹ * x) : ℂ ⧸ L.lattice) = 0 :=
        congrArg Subtype.val h
      have h2 := (Submodule.Quotient.mk_eq_zero _).1 h1
      refine ⟨⟨(α : ℂ)⁻¹ * x, h2⟩, Subtype.ext ?_⟩
      show (α : ℂ) * ((α : ℂ)⁻¹ * x) = x
      rw [← mul_assoc, mul_inv_cancel₀ hα0, one_mul]
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      show (Submodule.Quotient.mk ((α : ℂ)⁻¹ * ((α : ℂ) * y)) : ℂ ⧸ L.lattice) = 0
      rw [← mul_assoc, inv_mul_cancel₀ hα0, one_mul]
      exact (Submodule.Quotient.mk_eq_zero _).2 y.2
  let E : (L.lattice ⧸ LinearMap.range (latticeEndo α)) ≃ₗ[ℤ] LinearMap.ker (endoMap α) :=
    (Submodule.quotEquivOfEq _ _ hΘker.symm).trans (Θ.quotKerEquivOfSurjective hΘsurj)
  obtain ⟨hfin, hcard⟩ := lemma_3_20_a (latticeEndo α) hdet
  refine ⟨Finite.of_equiv _ E.toEquiv, ?_⟩
  unfold degree
  rw [← Nat.card_congr E.toEquiv, hcard]
  exact (Int.natAbs_of_nonneg hpos.le)

/-! ### The Tate module of `ℂ/Λ` (Proposition 3.22, Corollary 3.23) -/

/-- The map of Tate modules induced by a homomorphism. -/
def tateMap {ℓ : ℕ} {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    tateModule ℓ A →+ tateModule ℓ B where
  toFun x := ⟨fun n => f (x.1 n), by simp [x.2.1], fun n => by rw [← map_nsmul, x.2.2 n]⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Data exhibiting the `ℓⁿ`-torsion of `A` as `(ℤ/ℓⁿ)²`: `K n v = ℓ⁻ⁿ v` for `v ∈ ℤ²`. -/
structure TateCoord (ℓ : ℕ) (A : Type*) [AddCommGroup A] where
  K : ℕ → (Fin 2 → ℤ) →+ A
  zero : ∀ v, K 0 v = 0
  ker : ∀ n v, K n v = 0 ↔ ∀ i, ((ℓ : ℤ) ^ n ∣ v i)
  surj : ∀ n q, ℓ ^ n • q = 0 → ∃ v, K n v = q
  step : ∀ n v, ℓ • K (n + 1) v = K n v

namespace TateCoord

variable {ℓ : ℕ} {A : Type*} [AddCommGroup A] (C : TateCoord ℓ A)

theorem coord_eq (n : ℕ) {u u' : Fin 2 → ℤ} (h : C.K n u = C.K n u') (i : Fin 2) :
    (u i : ZMod (ℓ ^ n)) = u' i := by
  have h0 : C.K n (u - u') = 0 := by rw [map_sub, h, sub_self]
  have h1 := (C.ker n _).1 h0 i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h2 : ((ℓ ^ n : ℕ) : ℤ) ∣ u i - u' i := by push_cast; simpa using h1
  rw [← dvd_neg, neg_sub] at h2
  exact h2

theorem eq_of_coord (n : ℕ) {u u' : Fin 2 → ℤ} (h : ∀ i, (u i : ZMod (ℓ ^ n)) = u' i) :
    C.K n u = C.K n u' := by
  rw [← sub_eq_zero, ← map_sub, C.ker]
  intro i
  have h1 := (ZMod.intCast_eq_intCast_iff_dvd_sub (u i) (u' i) (ℓ ^ n)).1 (h i)
  have h2 : ((ℓ ^ n : ℕ) : ℤ) ∣ u i - u' i := by rw [← dvd_neg, neg_sub]; exact h1
  simpa using h2

variable [Fact ℓ.Prime]

/-- `y` is the `ℤ_ℓ`-coordinate vector of `x ∈ T_ℓ A`. -/
def Rel (x : tateModule ℓ A) (y : Fin 2 → ℤ_[ℓ]) : Prop :=
  ∀ n (u : Fin 2 → ℤ), C.K n u = x.1 n → ∀ i, PadicInt.toZModPow n (y i) = (u i : ZMod (ℓ ^ n))

theorem rel_exists (x : tateModule ℓ A) : ∃ y, C.Rel x y := by
  choose u hu using fun n => C.surj n (x.1 n) (tateModule_smul_pow_eq_zero x.2 n)
  have hcauchy : ∀ i n, (ℓ : ℤ) ^ n ∣ u (n + 1) i - u n i := by
    intro i n
    have : C.K n (u (n + 1) - u n) = 0 := by
      rw [map_sub, hu n, ← C.step, hu (n + 1), x.2.2 n, sub_self]
    simpa using (C.ker n _).1 this i
  refine ⟨fun i => PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => u n i) ℓ (hcauchy i)), ?_⟩
  intro n u' hu' i
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => u n i) ℓ (hcauchy i) n]
  exact (C.coord_eq n (by rw [hu', hu n]) i).symm

theorem rel_unique {x : tateModule ℓ A} {y y' : Fin 2 → ℤ_[ℓ]}
    (h : C.Rel x y) (h' : C.Rel x y') : y = y' := by
  funext i
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  obtain ⟨u, hu⟩ := C.surj n (x.1 n) (tateModule_smul_pow_eq_zero x.2 n)
  rw [h n u hu i, h' n u hu i]

theorem rel_add {x x' : tateModule ℓ A} {y y' : Fin 2 → ℤ_[ℓ]} (h : C.Rel x y) (h' : C.Rel x' y') :
    C.Rel (x + x') (y + y') := by
  intro n u hu i
  obtain ⟨u₁, h₁⟩ := C.surj n (x.1 n) (tateModule_smul_pow_eq_zero x.2 n)
  obtain ⟨u₂, h₂⟩ := C.surj n (x'.1 n) (tateModule_smul_pow_eq_zero x'.2 n)
  have : C.K n u = C.K n (u₁ + u₂) := by
    rw [map_add, h₁, h₂]; exact hu
  rw [C.coord_eq n this i]
  simp [h n u₁ h₁ i, h' n u₂ h₂ i]

theorem rel_zero : C.Rel 0 0 := by
  intro n u hu i
  have h1 : C.K n u = 0 := hu
  have h2 := (C.ker n u).1 h1 i
  have : (u i : ZMod (ℓ ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using h2
  simp [this]

theorem rel_map (Mat : Matrix (Fin 2) (Fin 2) ℤ) (φ : A →+ A)
    (hMat : ∀ n u, C.K n (Mat.mulVec u) = φ (C.K n u)) {x : tateModule ℓ A} {y : Fin 2 → ℤ_[ℓ]}
    (h : C.Rel x y) :
    C.Rel (tateMap φ x) ((Mat.map (algebraMap ℤ ℤ_[ℓ])).mulVec y) := by
  intro n u hu i
  obtain ⟨u₁, h₁⟩ := C.surj n (x.1 n) (tateModule_smul_pow_eq_zero x.2 n)
  have : C.K n u = C.K n (Mat.mulVec u₁) := by
    rw [hMat, h₁]; exact hu
  rw [C.coord_eq n this i]
  simp [Matrix.mulVec, dotProduct, h n u₁ h₁]

/-- The `ℤ_ℓ`-coordinates of an element of `T_ℓ A`. -/
noncomputable def toCoord (x : tateModule ℓ A) : Fin 2 → ℤ_[ℓ] := Classical.choose (C.rel_exists x)

theorem rel_toCoord (x : tateModule ℓ A) : C.Rel x (C.toCoord x) :=
  Classical.choose_spec (C.rel_exists x)

theorem toCoord_eq {x : tateModule ℓ A} {y : Fin 2 → ℤ_[ℓ]} (h : C.Rel x y) : C.toCoord x = y :=
  C.rel_unique (C.rel_toCoord x) h

/-- The coordinates as an additive map. -/
noncomputable def coordHom : tateModule ℓ A →+ (Fin 2 → ℤ_[ℓ]) where
  toFun := C.toCoord
  map_zero' := C.toCoord_eq C.rel_zero
  map_add' x x' := C.toCoord_eq (C.rel_add (C.rel_toCoord x) (C.rel_toCoord x'))

theorem coordHom_injective : Function.Injective C.coordHom := by
  intro x x' hxx
  have hxx' : C.toCoord x = C.toCoord x' := hxx
  apply Subtype.ext
  funext n
  obtain ⟨u, hu⟩ := C.surj n (x.1 n) (tateModule_smul_pow_eq_zero x.2 n)
  obtain ⟨u', hu'⟩ := C.surj n (x'.1 n) (tateModule_smul_pow_eq_zero x'.2 n)
  rw [← hu, ← hu']
  apply C.eq_of_coord
  intro i
  rw [← C.rel_toCoord x n u hu i, hxx', C.rel_toCoord x' n u' hu' i]

theorem coordHom_surjective : Function.Surjective C.coordHom := by
  intro y
  let w : ℕ → Fin 2 → ℤ := fun n i => ((PadicInt.toZModPow n (y i)).val : ℤ)
  have hw : ∀ n i, (w n i : ZMod (ℓ ^ n)) = PadicInt.toZModPow n (y i) := by
    intro n i
    simp only [w, Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  have hstep : ∀ n, C.K n (w (n + 1)) = C.K n (w n) := by
    intro n
    apply C.eq_of_coord
    intro i
    have h1 : (w (n + 1) i : ZMod (ℓ ^ n)) =
        ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n)) (w (n + 1) i : ZMod (ℓ ^ (n + 1))) :=
      (map_intCast _ _).symm
    rw [h1, hw, hw]
    exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) (y i)
  let x : tateModule ℓ A := ⟨fun n => C.K n (w n), C.zero _, fun n => by
    show ℓ • C.K (n + 1) (w (n + 1)) = C.K n (w n)
    rw [C.step, hstep]⟩
  refine ⟨x, C.toCoord_eq ?_⟩
  intro n u hu i
  have : (u i : ZMod (ℓ ^ n)) = w n i := C.coord_eq n hu i
  rw [this, hw]

/-- The coordinates as an additive equivalence `T_ℓ A ≃ ℤ_ℓ²`. -/
noncomputable def coordEquiv : tateModule ℓ A ≃+ (Fin 2 → ℤ_[ℓ]) :=
  AddEquiv.ofBijective C.coordHom ⟨C.coordHom_injective, C.coordHom_surjective⟩

theorem coordEquiv_map (Mat : Matrix (Fin 2) (Fin 2) ℤ) (φ : A →+ A)
    (hMat : ∀ n u, C.K n (Mat.mulVec u) = φ (C.K n u)) (x : tateModule ℓ A) :
    C.coordEquiv (tateMap φ x) = (Mat.map (algebraMap ℤ ℤ_[ℓ])).mulVec (C.coordEquiv x) :=
  C.toCoord_eq (C.rel_map Mat φ hMat (C.rel_toCoord x))

end TateCoord

private theorem ell_pow_ne_zero (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) : (ℓ : ℂ) ^ n ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)

/-- The torsion coordinates of `ℂ/Λ`: `K n v = [ℓ⁻ⁿ (v₀ ω₁ + v₁ ω₂)]`. -/
noncomputable def tateCoordOf (ℓ : ℕ) [Fact ℓ.Prime] (L : PeriodPair) :
    TateCoord ℓ (ℂ ⧸ L.lattice) where
  K n :=
    { toFun := fun v => Submodule.Quotient.mk
        (((L.latticeBasis.equivFun.symm v : L.lattice) : ℂ) / (ℓ : ℂ) ^ n)
      map_zero' := by simp
      map_add' := fun v w => by
        rw [map_add, Submodule.coe_add, add_div, Submodule.Quotient.mk_add] }
  zero := fun v => by
    show (Submodule.Quotient.mk _ : ℂ ⧸ L.lattice) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using (L.latticeBasis.equivFun.symm v).2
  ker := fun n v => by
    show (Submodule.Quotient.mk _ : ℂ ⧸ L.lattice) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    have hne := ell_pow_ne_zero ℓ n
    constructor
    · intro h i
      set lam := L.latticeBasis.equivFun.symm v with hlam
      have h1 : lam = ((ℓ : ℤ) ^ n) • (⟨(lam : ℂ) / (ℓ : ℂ) ^ n, h⟩ : L.lattice) := by
        apply Subtype.ext
        simp only [Submodule.coe_smul, zsmul_eq_mul]
        push_cast
        field_simp
      have h2 := congrArg (fun z => L.latticeBasis.equivFun z i) h1
      have h3 : L.latticeBasis.equivFun lam = v := LinearEquiv.apply_symm_apply _ v
      simp only [map_zsmul, Pi.smul_apply, zsmul_eq_mul, h3] at h2
      exact ⟨_, h2⟩
    · intro h
      choose w hw using h
      have h1 : L.latticeBasis.equivFun.symm v = ((ℓ : ℤ) ^ n) • L.latticeBasis.equivFun.symm w := by
        rw [← map_zsmul]
        congr 1
        funext i
        simp [hw i]
      rw [h1, Submodule.coe_smul, zsmul_eq_mul]
      push_cast
      rw [mul_div_cancel_left₀ _ hne]
      exact (L.latticeBasis.equivFun.symm w).2
  surj := fun n q hq => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hz : (ℓ : ℂ) ^ n * z ∈ L.lattice := by
      have : ((ℓ ^ n) • (Submodule.Quotient.mk z : ℂ ⧸ L.lattice)) = 0 := hq
      have e : (Submodule.Quotient.mk (ℓ ^ n • z) : ℂ ⧸ L.lattice) =
          ℓ ^ n • Submodule.Quotient.mk z := map_nsmul (Submodule.mkQ L.lattice) (ℓ ^ n) z
      rw [← e] at this
      have := (Submodule.Quotient.mk_eq_zero _).1 this
      simpa [nsmul_eq_mul] using this
    refine ⟨L.latticeBasis.equivFun ⟨(ℓ : ℂ) ^ n * z, hz⟩, ?_⟩
    show (Submodule.Quotient.mk _ : ℂ ⧸ L.lattice) = _
    simp [ell_pow_ne_zero ℓ n]
  step := fun n v => by
    show ℓ • (Submodule.Quotient.mk _ : ℂ ⧸ L.lattice) = Submodule.Quotient.mk _
    have e : ∀ z : ℂ, (Submodule.Quotient.mk (ℓ • z) : ℂ ⧸ L.lattice) =
        ℓ • Submodule.Quotient.mk z := fun z => map_nsmul (Submodule.mkQ L.lattice) ℓ z
    rw [← e]
    congr 1
    have hne := ell_pow_ne_zero ℓ n
    have hl : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
    rw [nsmul_eq_mul, pow_succ]
    field_simp

/-- Milne (pdf p. 108): for `E(ℂ) = ℂ/Λ`, `T_ℓ E = Λ ⊗ ℤ_ℓ`, compatibly with endomorphisms:
there is an isomorphism `T_ℓ(ℂ/Λ) ≅ ℤ_ℓ ⊗ Λ` carrying the action of `α` to `1 ⊗ α`. -/
@[kb "milne2006ec" "Ch. III, §3, T_ℓ E = Λ ⊗ Z_ℓ, pdf p. 108"]
theorem tateModule_quotient_equiv (ℓ : ℕ) [Fact ℓ.Prime] (L : PeriodPair) :
    ∃ e : tateModule ℓ (ℂ ⧸ L.lattice) ≃+ ℤ_[ℓ] ⊗[ℤ] L.lattice,
      ∀ (α : endRing L.lattice) (x : tateModule ℓ (ℂ ⧸ L.lattice)),
      e (tateMap (endoMap α).toAddMonoidHom x) = (latticeEndo α).baseChange ℤ_[ℓ] (e x) := by
  let C := tateCoordOf ℓ L
  let bℓ := Algebra.TensorProduct.basis ℤ_[ℓ] L.latticeBasis
  refine ⟨C.coordEquiv.trans bℓ.equivFun.symm.toAddEquiv, fun α x => ?_⟩
  have hMat : ∀ n u, C.K n ((LinearMap.toMatrix L.latticeBasis L.latticeBasis (latticeEndo α)).mulVec u)
      = (endoMap α).toAddMonoidHom (C.K n u) := by
    intro n u
    have h1 : (LinearMap.toMatrix L.latticeBasis L.latticeBasis (latticeEndo α)).mulVec u =
        L.latticeBasis.equivFun (latticeEndo α (L.latticeBasis.equivFun.symm u)) := by
      have := LinearMap.toMatrix_mulVec_repr L.latticeBasis L.latticeBasis (latticeEndo α)
        (L.latticeBasis.equivFun.symm u)
      simpa using this
    rw [h1]
    show (Submodule.Quotient.mk (((L.latticeBasis.equivFun.symm
        (L.latticeBasis.equivFun (latticeEndo α (L.latticeBasis.equivFun.symm u))) : L.lattice) : ℂ) /
          (ℓ : ℂ) ^ n) : ℂ ⧸ L.lattice) =
      Submodule.Quotient.mk ((α : ℂ) * (((L.latticeBasis.equivFun.symm u : L.lattice) : ℂ) / (ℓ : ℂ) ^ n))
    rw [LinearEquiv.symm_apply_apply, ← mul_div_assoc]
    rfl
  show bℓ.equivFun.symm (C.coordEquiv (tateMap (endoMap α).toAddMonoidHom x)) =
    (latticeEndo α).baseChange ℤ_[ℓ] (bℓ.equivFun.symm (C.coordEquiv x))
  rw [C.coordEquiv_map _ _ hMat]
  apply bℓ.equivFun.injective
  simp only [LinearEquiv.apply_symm_apply]
  have := LinearMap.toMatrix_mulVec_repr bℓ bℓ ((latticeEndo α).baseChange ℤ_[ℓ])
    (bℓ.equivFun.symm (C.coordEquiv x))
  rw [LinearMap.toMatrix_baseChange] at this
  have e : ⇑(bℓ.repr (bℓ.equivFun.symm (C.coordEquiv x))) = C.coordEquiv x :=
    LinearEquiv.apply_symm_apply bℓ.equivFun _
  rw [e] at this
  exact this

/-- Proposition 3.22 for `k = ℂ` (Milne, pdf p. 108): for a nonzero endomorphism `α` of
`E(ℂ) = ℂ/Λ`, `det(α | T_ℓ E) = deg α`.  Through `tateModule_quotient_equiv`, `α` acts on
`T_ℓ E` as `1 ⊗ α` on `ℤ_ℓ ⊗ Λ`, whose determinant is taken. -/
@[kb "milne2006ec" "Ch. III, Prop. 3.22, pdf p. 108"]
theorem prop_3_22 (ℓ : ℕ) [Fact ℓ.Prime] (L : PeriodPair) (α : endRing L.lattice) (hα : α ≠ 0) :
    LinearMap.det ((latticeEndo α).baseChange ℤ_[ℓ]) = (degree α : ℤ_[ℓ]) := by
  rw [LinearMap.det_baseChange, ← (prop_3_21 L α hα).2]
  simp

/-- Corollary 3.23 for `k = ℂ` (Milne, pdf p. 108): let `X² + cX + d` be the characteristic
polynomial of `α` acting on `T_ℓ E` (`= ℤ_ℓ ⊗ Λ`).  Then (a) `c, d` lie in `ℤ` and do not depend
on `ℓ`, with `d = deg α`; (b) `c² - 4d ≤ 0`; (c) `α² + cα + d = 0` as an endomorphism.
(Here `α ≠ 0`; for `α = 0` (a) and (c) also hold with `c = d = 0`.) -/
@[kb "milne2006ec" "Ch. III, Cor. 3.23, pdf p. 108"]
theorem cor_3_23 (L : PeriodPair) (α : endRing L.lattice) (hα : α ≠ 0) :
    ∃ c d : ℤ,
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], LinearMap.charpoly ((latticeEndo α).baseChange ℤ_[ℓ]) =
        Polynomial.X ^ 2 + Polynomial.C (c : ℤ_[ℓ]) * Polynomial.X + Polynomial.C (d : ℤ_[ℓ])) ∧
      d = degree α ∧ c ^ 2 - 4 * d ≤ 0 ∧ (α : ℂ) ^ 2 + c * α + d = 0 := by
  set g := latticeEndo α with hg
  have hχ : g.charpoly = Polynomial.X ^ 2 + Polynomial.C (-LinearMap.trace ℤ L.lattice g) *
      Polynomial.X + Polynomial.C (LinearMap.det g) := by
    rw [← LinearMap.charpoly_toMatrix g L.latticeBasis, Matrix.charpoly_fin_two,
      ← LinearMap.trace_eq_matrix_trace ℤ L.latticeBasis, LinearMap.det_toMatrix]
    simp [sub_eq_add_neg]
  set c : ℤ := -LinearMap.trace ℤ L.lattice g with hc
  set d : ℤ := LinearMap.det g with hd
  have hdeg : d = (degree α : ℤ) := ((prop_3_21 L α hα).2).symm
  have hc2 : ((c : ℤ) : ℝ) = -(2 * (α : ℂ).re) := by
    rw [hc, Int.cast_neg, trace_latticeEndo_cast]
  have hd2 : ((d : ℤ) : ℝ) = Complex.normSq (α : ℂ) := det_latticeEndo_cast L α
  refine ⟨c, d, fun ℓ _ => ?_, hdeg, ?_, ?_⟩
  · rw [LinearMap.charpoly_baseChange, hχ]
    simp [c, d]
  · have : (((c ^ 2 - 4 * d : ℤ)) : ℝ) ≤ 0 := by
      push_cast
      rw [hc2, hd2, Complex.normSq_apply]
      nlinarith [sq_nonneg (α : ℂ).im]
    exact_mod_cast this
  · have h := LinearMap.aeval_self_charpoly g
    rw [hχ] at h
    have h0 : (g ^ 2 + (c : ℤ) • g + (d : ℤ) • 1 : L.lattice →ₗ[ℤ] L.lattice) = 0 := by
      simpa using h
    have h1 := congrArg (fun F : L.lattice →ₗ[ℤ] L.lattice =>
      ((F ⟨L.ω₁, L.ω₁_mem_lattice⟩ : L.lattice) : ℂ)) h0
    have e1 : ((g ⟨L.ω₁, L.ω₁_mem_lattice⟩ : L.lattice) : ℂ) = α * L.ω₁ := rfl
    have e2 : ((g (g ⟨L.ω₁, L.ω₁_mem_lattice⟩) : L.lattice) : ℂ) = α * (α * L.ω₁) := rfl
    simp only [LinearMap.add_apply, LinearMap.smul_apply, pow_two, Module.End.mul_apply,
      Module.End.one_apply, Submodule.coe_add, Submodule.coe_smul, LinearMap.zero_apply,
      Submodule.coe_zero] at h1
    rw [e2, e1] at h1
    simp only [zsmul_eq_mul] at h1
    have hne : L.ω₁ ≠ 0 := L.indep.ne_zero 0
    apply mul_right_cancel₀ hne
    linear_combination h1

end NumberFieldKB.MilneEC.III
