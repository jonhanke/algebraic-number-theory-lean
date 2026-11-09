import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Lemma33

/-!
# Milne, *Class Field Theory*, Chapters II–III: $H^0_T(G, M) = M^G/\mathrm{Nm}_G M$

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

* `tateZeroEquiv` — $H^0_T(G, M) \simeq M^G/\mathrm{Nm}_G M$ for a finite group $G$ (Chapter II, §3, definition of
  $H^0_T$, p. 77).
* `tateZeroUnitsEquiv` — for a finite Galois extension of fields $L/K$, $H^0_T(\operatorname{Gal}(L/K), L^\times)
  \simeq K^\times/\mathrm{Nm}_{L/K}(L^\times)$ (used in Chapter III, Theorem 3.1, for $r = -2$).
-/

open CategoryTheory Rep groupCohomology Limits

namespace NumberFieldKB.MilneCFT.Ch3

variable {G : Type} [Group G] [Fintype G]

/-- The norm $m \mapsto \sum_g g m$ of a $G$-module, with values in the invariants. -/
noncomputable def normMap (M : Rep.{0,0,0} ℤ G) : M →+ M.ρ.invariants :=
  (LinearMap.codRestrict M.ρ.invariants (Representation.norm M.ρ)
    (fun m g => Representation.self_norm_apply _ g m)).toAddMonoidHom

/-- The image $\mathrm{Nm}_G M$ of the norm map, as a subgroup of $M^G$. -/
noncomputable def normRange (M : Rep.{0,0,0} ℤ G) : AddSubgroup M.ρ.invariants :=
  (normMap M).range

/-- $H^0_T(G, M) = M^G / \mathrm{Nm}_G M$. -/
noncomputable def tateZeroEquiv (M : Rep.{0,0,0} ℤ G) :
    tateCohomology M 0 ≃+ (M.ρ.invariants ⧸ normRange M) := by
  classical
  let S := (tateComplex M).sc' (-1) 0 1
  let e : S.X₂ ≃ₗ[ℤ] M := (cochainsIso₀ M).toLinearEquiv
  have hg : ∀ x : S.X₂, S.g x = 0 ↔ ∀ g : G, M.ρ g (e x) = e x := by
    intro x
    obtain ⟨m, rfl⟩ : ∃ m, x = e.symm m := ⟨e x, (e.symm_apply_apply x).symm⟩
    have h1 := eq_d₀₁_comp_inv_apply M m
    have h2 : S.g (e.symm m) = (cochainsIso₁ M).inv (d₀₁ M m) := h1
    rw [e.apply_symm_apply, h2]
    constructor
    · intro h g
      have : d₀₁ M m = 0 := by
        exact (cochainsIso₁ M).toLinearEquiv.symm.injective (h.trans (map_zero (cochainsIso₁ M).toLinearEquiv.symm).symm)
      exact sub_eq_zero.1 (congrFun this g)
    · intro h
      have : d₀₁ M m = 0 := by
        funext g
        exact sub_eq_zero.2 (h g)
      rw [this]; exact map_zero (cochainsIso₁ M).toLinearEquiv.symm
  have hf : ∀ y : (Fin 0 → G) →₀ M, e (S.f y) = ∑ g : G, M.ρ g (y default) := by
    intro y
    change e (M.tateNorm.hom y) = _
    rw [Rep.tateNorm_eq]
    obtain ⟨v, rfl⟩ : ∃ v, y = Finsupp.single default v := ⟨y default, (Finsupp.unique_single y)⟩
    simp [e, cochainsIso₀, Representation.norm]
    change (LinearMap.pi (fun _ : Fin 0 → G => ∑ g, M.ρ g) v) default = _
    simp
  have hker : (LinearMap.ker S.g.hom).map (e : S.X₂ →ₗ[ℤ] M) = M.ρ.invariants := by
    ext m
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩ g
      exact (hg x).1 hx g
    · intro hm
      exact ⟨e.symm m, (hg _).2 (by simpa using hm), by simp⟩
  letI : Module ℤ (LinearMap.ker S.g.hom) := Submodule.module _
  letI : Module ℤ M.ρ.invariants := Submodule.module _
  let ψ := e.ofSubmodules (LinearMap.ker S.g.hom) M.ρ.invariants hker
  let e1 : tateCohomology M 0 ≅ S.homology :=
    (tateComplex M).homologyIsoSc' (-1) 0 1 (by simp) (by simp)
  let e2 : S.homology ≅ S.moduleCatLeftHomologyData.H := S.moduleCatLeftHomologyData.homologyIso
  have key : (LinearMap.range S.moduleCatToCycles).toAddSubgroup.map ψ.toAddEquiv.toAddMonoidHom
      = normRange M := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.mem_range, normRange,
      AddMonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨(show (Fin 0 → G) →₀ M from y) default, ?_⟩
      ext
      refine Eq.trans ?_ (hf y).symm
      simp [normMap, Representation.norm]
    · rintro ⟨m, rfl⟩
      refine ⟨_, ⟨Finsupp.single default m, rfl⟩, ?_⟩
      ext
      refine (hf (Finsupp.single default m)).trans ?_
      simp [normMap, Representation.norm]
  exact (e1 ≪≫ e2).toLinearEquiv.toAddEquiv.trans
    (QuotientAddGroup.congr _ _ ψ.toAddEquiv key)

/-- Two quotients of the same group by the same kernel. -/
noncomputable def quotAddEquivAdditive {A : Type} [CommGroup A] (N : Subgroup A) {B : Type}
    [AddCommGroup B] (Q : AddSubgroup B) (φ : Additive A →+ B) (hφ : Function.Surjective φ)
    (h : ∀ x : Additive A, φ x ∈ Q ↔ x.toMul ∈ N) : (B ⧸ Q) ≃+ Additive (A ⧸ N) := by
  let π : Additive A →+ B ⧸ Q := (QuotientAddGroup.mk' Q).comp φ
  let π' : Additive A →+ Additive (A ⧸ N) := (QuotientGroup.mk' N).toAdditive
  have hπ : Function.Surjective π := (QuotientAddGroup.mk'_surjective _).comp hφ
  have hπ' : Function.Surjective π' := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q.toMul
    exact ⟨Additive.ofMul x, rfl⟩
  have hker : π.ker = π'.ker := by
    ext x
    simp only [AddMonoidHom.mem_ker]
    have h1 : π x = 0 ↔ φ x ∈ Q := QuotientAddGroup.eq_zero_iff _
    have h2 : π' x = 0 ↔ x.toMul ∈ N := by
      change Additive.ofMul (QuotientGroup.mk x.toMul : A ⧸ N) = Additive.ofMul 1 ↔ _
      rw [Additive.ofMul.injective.eq_iff, QuotientGroup.eq_one_iff]
    rw [h1, h2, h x]
  exact (QuotientAddGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective π' hπ'))

section Units

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem coe_prod_smul_units (y : Lˣ) :
    ((∏ σ : L ≃ₐ[K] L, σ • y : Lˣ) : L) = algebraMap K L (Algebra.norm K (y : L)) := by
  rw [Algebra.norm_eq_prod_automorphisms, Units.coe_prod]
  rfl

theorem exists_units_of_fixed (u : Lˣ) (hu : ∀ σ : L ≃ₐ[K] L, σ • u = u) :
    ∃ a : Kˣ, Units.map (algebraMap K L : K →* L) a = u := by
  have hfix' : ∀ x : Lˣ, (∀ σ : L ≃ₐ[K] L, σ • x = x) → ∃ c : K, algebraMap K L c = x := by
    intro x hx
    have : (x : L) ∈ (⊥ : IntermediateField K L) := by
      rw [← IsGalois.fixedField_top (F := K) (E := L)]
      intro σ
      exact congrArg Units.val (hx σ)
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 this
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hfix' u hu
  obtain ⟨d, hd⟩ := hfix' u⁻¹ (fun σ => by rw [smul_inv', hu σ])
  have hcd : c * d = 1 := by
    apply (algebraMap K L).injective
    rw [map_mul, hc, hd, map_one]; simp
  refine ⟨⟨c, d, hcd, by rw [mul_comm]; exact hcd⟩, ?_⟩
  ext
  simpa using hc

/-- The inclusion $K^\times \to (L^\times)^G$, additively. -/
noncomputable def unitsToInv : Additive Kˣ →+ (Rep.ofAlgebraAutOnUnits K L).ρ.invariants where
  toFun x := ⟨Additive.ofMul (Units.map (algebraMap K L : K →* L) x.toMul), fun σ => by
    change Additive.ofMul (σ • Units.map (algebraMap K L : K →* L) x.toMul) = _
    congr 1
    ext
    simp⟩
  map_zero' := Subtype.ext (by simp only [toMul_zero, map_one]; rfl)
  map_add' a b := Subtype.ext (by simp only [toMul_add, map_mul]; rfl)

theorem unitsToInv_coe (x : Additive Kˣ) :
    (unitsToInv K L x).1 = Additive.ofMul (Units.map (algebraMap K L : K →* L) x.toMul) := rfl

/-- **Milne, II.3**: $H^0_T(G, L^\times) = K^\times / \mathrm{Nm}\, L^\times$. -/
noncomputable def tateZeroUnitsEquiv :
    tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0 ≃+
      Additive (Kˣ ⧸ (Units.map (Algebra.norm K (S := L) : L →* K)).range) := by
  classical
  let M := Rep.ofAlgebraAutOnUnits K L
  let N := (Units.map (Algebra.norm K (S := L) : L →* K)).range
  have hsurj : Function.Surjective (unitsToInv K L) := by
    rintro ⟨m, hm⟩
    obtain ⟨a, ha⟩ := exists_units_of_fixed K L m.toMul (fun σ => congrArg Additive.toMul (hm σ))
    refine ⟨Additive.ofMul a, Subtype.ext ?_⟩
    rw [unitsToInv_coe, toMul_ofMul, ha]; rfl
  have hnorm : ∀ x : Additive Kˣ, unitsToInv K L x ∈ normRange M ↔ x.toMul ∈ N := by
    intro x
    have key : ∀ y : Lˣ, (normMap M (Additive.ofMul y)).1 =
        Additive.ofMul (∏ σ : L ≃ₐ[K] L, σ • y) := by
      intro y
      have : (normMap M (Additive.ofMul y)).1 = ∑ g, M.ρ g (Additive.ofMul y) := by
        show (Representation.norm M.ρ (Additive.ofMul y : M)) = _
        simp only [Representation.norm]
        first | exact LinearMap.sum_apply _ _ _ | exact Finset.sum_apply _ _ _ | rfl
      rw [this]
      exact (ofMul_prod Finset.univ (fun σ : L ≃ₐ[K] L => σ • y)).symm
    constructor
    · rintro ⟨m, hm⟩
      obtain ⟨y, hmy⟩ : ∃ y : Lˣ, m = Additive.ofMul y := ⟨m.toMul, rfl⟩
      rw [hmy] at hm
      refine ⟨y, ?_⟩
      have h1 := (key y).symm.trans (congrArg Subtype.val hm)
      rw [unitsToInv_coe] at h1
      have h2 := congrArg (fun z => (Additive.toMul z : Lˣ).val) h1
      simp only [toMul_ofMul] at h2
      rw [coe_prod_smul_units] at h2
      apply Units.ext
      apply (algebraMap K L).injective
      simpa using h2
    · rintro ⟨y, hy⟩
      refine ⟨Additive.ofMul y, Subtype.ext ?_⟩
      rw [key, unitsToInv_coe]
      congr 1
      apply Units.ext
      rw [coe_prod_smul_units, ← hy]
      simp
  exact (tateZeroEquiv M).trans (quotAddEquivAdditive N (normRange M) (unitsToInv K L) hsurj hnorm)

end Units

end NumberFieldKB.MilneCFT.Ch3
