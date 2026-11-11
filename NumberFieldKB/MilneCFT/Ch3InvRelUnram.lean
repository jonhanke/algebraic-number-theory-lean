import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3InvSystemRel
import NumberFieldKB.MilneCFT.Ch3InvTauCeti
import NumberFieldKB.MilneCFT.Ch3InvInfl
import NumberFieldKB.MilneCFT.LubinTate.RamificationQuotientTauCeti

/-!
# Milne, *Class Field Theory*, Chapter III, Theorem 2.1: normalization of the relative invariant on unramified extensions

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Ch. III,
Thm. 2.1, p. 103–105.

For a finite Galois $M/K$ inside $\Omega$ and a subgroup $H$ of $\operatorname{Gal}(M/K)$, with $F = M^H$ and $M/F$
unramified, the relative invariant `tcInvRel M H` (Tau Ceti's $\mathrm{inv}_F$ after inflation into $\mathrm{Br}(F)$)
is the invariant map `invRel M hv H σ` of $M/F$ of Milne's p. 99 (normalized valuation $\mathrm{ord}_M$, connecting
map, evaluation at the Frobenius element $\sigma$ of $M/F$): `tcInvRel_unramified`.

Route: (1) the abstract form of `invK_eq_unramifiedInv` (`invOf_eq_unramifiedInv`), for any unramified Galois
extension of local fields `L/F` and any invariant $v : L^\times \to \mathbb Z$ restricting to $\mathrm{ord}_F$ on
$F^\times$; (2) transport of `invOf` along $H \simeq \operatorname{Gal}(M/F)$ (`invRel_eq_invOf`); (3) bridges from the
subgroup-encoded notions of `Ch3Invariant.lean` to Tau Ceti's structure on $M/F$: `mem_integers_iff`,
`exists_maxIdealL_iff`, `isUnramified_of_isUnramifiedOver`, `natCard_residueFieldL_baseOf`,
`galFixEquiv_eq_frobenius`, `ord_algebraMap_eq`.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT
open TauCeti.ClassFieldTheory IntermediateField

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

/-! ## (1) The abstract form of `invK_eq_unramifiedInv` -/

section AbstractDef

variable {F L : Type} [Field F] [Field L] [Algebra F L]

/-- A $\operatorname{Gal}(L/F)$-invariant homomorphism $v : L^\times \to \mathbb Z$ as a $G$-map
$L^\times \to \mathbb Z$. -/
noncomputable def ordRepAbs (v : Additive Lˣ →+ ℤ)
    (hv : ∀ (g : L ≃ₐ[F] L) (x : Lˣ), v (Additive.ofMul (g • x)) = v (Additive.ofMul x)) :
    Rep.ofAlgebraAutOnUnits F L ⟶ (seqZQ (L ≃ₐ[F] L)).X₁ :=
  Rep.ofHom ⟨v.toIntLinearMap, fun σ => by
    ext x
    exact hv σ (Additive.toMul x)⟩

theorem invOf_apply {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (v : M ⟶ (seqZQ G).X₁) (σ : G)
    (x : groupCohomology M 2) :
    invOf M v σ x = h2IntToHom.hom ((groupCohomology.map (MonoidHom.id G) v 2).hom x) (Additive.ofMul σ) :=
  rfl

end AbstractDef

section Abstract

variable {F L : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L]
  [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L]

/-- **The invariant of an unramified extension of local fields is Tau Ceti's** (Milne, *CFT*, III, §1, p. 99–101;
abstract form of `invK_eq_unramifiedInv`): for $L/F$ finite unramified Galois, a Galois-invariant
$v : L^\times \to \mathbb Z$ restricting to $\mathrm{ord}_F$ on $F^\times$, and $\sigma = \mathrm{Frob}_{L/F}$,
`invOf` is Tau Ceti's `unramifiedInv` under $\mathbb Q/\mathbb Z \simeq$ `AddCircle (1 : ℚ)`. -/
theorem invOf_eq_unramifiedInv [TauCeti.IsUnramified F L] (v : Additive Lˣ →+ ℤ)
    (hv : ∀ (g : L ≃ₐ[F] L) (x : Lˣ), v (Additive.ofMul (g • x)) = v (Additive.ofMul x))
    (hord : ∀ a : Fˣ, v (Additive.ofMul (Units.map (algebraMap F L : F →+* L).toMonoidHom a)) =
      (TauCeti.normalizedValuation F a).toAdd)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) :
    invOf (Rep.ofAlgebraAutOnUnits F L) (ordRepAbs v hv) (TauCeti.frobeniusAlgEquiv (K := F) (L := L)) x =
      Ch4.addCircleEquivQZ (TauCeti.ClassFieldTheory.unramifiedInv F L x) := by
  classical
  set g := TauCeti.frobeniusAlgEquiv (K := F) (L := L) with hgdef
  have hg : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers g := fun τ => by
    rw [hgdef, TauCeti.zpowers_frobeniusAlgEquiv]; exact Subgroup.mem_top τ
  obtain ⟨a, rfl⟩ := TauCeti.ClassFieldTheory.unramifiedClass_surjective F L x
  obtain ⟨zM, hzM, hval⟩ := TauCeti.exists_H2π_eq_cyclicClass hg (Additive.toMul a)
  have hord' : orderOf g = Nat.card (L ≃ₐ[F] L) := by
    rw [← Nat.card_zpowers g]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv hg)
  set eU : Fˣ →* Lˣ := Units.map (algebraMap F L : F →+* L).toMonoidHom with heU
  have hp : ∀ τ : L ≃ₐ[F] L, (Rep.ofAlgebraAutOnUnits F L).ρ τ (Additive.ofMul (eU (Additive.toMul a))) =
      Additive.ofMul (eU (Additive.toMul a)) := fun τ =>
    congrArg Additive.ofMul (Units.ext (τ.commutes _))
  have hz : zM = carryCocycle hg (Rep.ofAlgebraAutOnUnits F L)
      (Additive.ofMul (eU (Additive.toMul a))) hp := by
    apply Subtype.ext
    funext p
    obtain ⟨τ₁, τ₂⟩ := p
    refine Eq.trans ?_ (carryCocycle_apply hg _ _ hp _).symm
    have h1 := pow_cycExp hg τ₁
    have h2 := pow_cycExp hg τ₂
    have l1 := cycExp_lt hg τ₁
    have l2 := cycExp_lt hg τ₂
    have key := hval (cycExp hg τ₁) (cycExp hg τ₂) (hord' ▸ l1) (hord' ▸ l2)
    rw [h1, h2, hord'] at key
    apply Additive.toMul.injective
    change Additive.toMul (zM (τ₁, τ₂)) = _
    rw [key]
    dsimp only
    by_cases c : cycExp hg τ₁ + cycExp hg τ₂ < Nat.card (L ≃ₐ[F] L)
    · simp only [c, ↓reduceIte, show ¬ (Nat.card (L ≃ₐ[F] L) ≤ cycExp hg τ₁ + cycExp hg τ₂) by omega]
      rfl
    · simp only [c, ↓reduceIte, show Nat.card (L ≃ₐ[F] L) ≤ cycExp hg τ₁ + cycExp hg τ₂ by omega]
      rfl
  have hcls : TauCeti.ClassFieldTheory.unramifiedClass F L a =
      H2π _ (carryCocycle hg (Rep.ofAlgebraAutOnUnits F L)
        (Additive.ofMul (eU (Additive.toMul a))) hp) := by
    rw [TauCeti.ClassFieldTheory.unramifiedClass_eq_cyclicClass F L hg]
    change TauCeti.cyclicClass hg (Additive.ofMul (Additive.toMul a)) = _
    rw [← hzM, hz]
    rfl
  have hv' : (show ℤ from (ordRepAbs v hv).hom (Additive.ofMul (eU (Additive.toMul a)))) =
      (TauCeti.normalizedValuation F (Additive.toMul a)).toAdd :=
    hord _
  have lhs : invOf (Rep.ofAlgebraAutOnUnits F L) (ordRepAbs v hv) g
      (TauCeti.ClassFieldTheory.unramifiedClass F L a) =
      qz (((TauCeti.normalizedValuation F (Additive.toMul a)).toAdd : ℚ) / Nat.card (L ≃ₐ[F] L)) := by
    rw [hcls, ← hv']
    exact invOf_carryCocycle hg (Rep.ofAlgebraAutOnUnits F L) (ordRepAbs v hv) _ hp
  have rhs := TauCeti.ClassFieldTheory.unramifiedInv_unramifiedClass (K := F) (L := L) (Additive.toMul a)
  rw [lhs, IsGalois.card_aut_eq_finrank]
  erw [rhs]
  rfl

end Abstract

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Local

variable {M : IntermediateField K Ω} [FiniteDimensional K M]

-- Tau Ceti's local-field structure (spectral norm) on a subfield of $M$ containing $K$: the four local instances
-- `subVR`, `subTop`, `subLocal`, `subExt` of `Ch3InvSystemRel.lean` (their names are importable; only the
-- instance attribute is local to that file), re-enabled here.
attribute [local instance] subVR subTop subLocal subExt

variable (M)

/-! ## (2) Transport of `invOf` along $H \simeq \operatorname{Gal}(M/M^H)$ -/

theorem galFixEquiv_apply (H : Subgroup Gal(M/K)) (σ : H) (y : M) : galFixEquiv M H σ y = (σ : Gal(M/K)) y :=
  rfl

/-- $\mathrm{ord}_M$ is invariant under $\operatorname{Gal}(M/M^H)$. -/
theorem ord_invariant_fix (H : Subgroup Gal(M/K)) {v : Additive Mˣ →+ ℤ} (hv : IsNormalizedOrd M v)
    (g : M ≃ₐ[fixedField H] M) (x : Mˣ) : v (Additive.ofMul (g • x)) = v (Additive.ofMul x) := by
  have h : g • x = (g.restrictScalars K) • x := Units.ext rfl
  rw [h]
  exact hv.gal (g.restrictScalars K) x

/-- **Transport**: the relative invariant `invRel` is `invOf` for $\operatorname{Gal}(M/M^H)$ after the identification
$H \simeq \operatorname{Gal}(M/M^H)$ (`galFixEquiv`, `relIso`). -/
theorem invRel_eq_invOf (H : Subgroup Gal(M/K)) {v : Additive Mˣ →+ ℤ} (hv : IsNormalizedOrd M v) (σ' : H)
    (x : H2rel M H) :
    invRel M hv H σ' x =
      invOf (Rep.ofAlgebraAutOnUnits (fixedField H) M) (ordRepAbs v (ord_invariant_fix M H hv))
        (galFixEquiv M H σ') ((relIso M H).hom.hom x) := by
  letI := Fintype.ofFinite H
  let f : (M ≃ₐ[fixedField H] M) →* H := (galFixEquiv M H).symm.toMonoidHom
  let φ : res f (res H.subtype (Rep.ofAlgebraAutOnUnits K M)) ⟶
      Rep.ofAlgebraAutOnUnits (fixedField H) M :=
    Rep.ofHom ⟨LinearMap.id, fun g => rfl⟩
  have hrel : (relIso M H).hom.hom x = (groupCohomology.map f φ 2).hom x := rfl
  have key := map_comm_ord f φ (ordRepRel hv H) (ordRepAbs v (ord_invariant_fix M H hv))
    (fun _ => rfl) x
  have nat := h2IntToHom_natural f ((groupCohomology.map (MonoidHom.id H) (ordRepRel hv H) 2).hom x)
    (galFixEquiv M H σ')
  have hfg : f (galFixEquiv M H σ') = σ' := (galFixEquiv M H).symm_apply_apply σ'
  rw [invOf_apply, hrel, key, nat, hfg]
  rfl

/-! ## (3) Bridges to Tau Ceti's structure on $M/M^H$ -/

section Bridges

variable (H : Subgroup Gal(M/K)) [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [ValuativeExtension (fixedField H) M]

include H

/-- **$\mathcal O_M$**: $x \in M$ is integral over $\mathcal O_K$ iff its valuation (for Tau Ceti's structure of
$M/M^H$) is at most $1$. -/
theorem mem_integers_iff (x : M) : x ∈ integers M ↔ ValuativeRel.valuation M x ≤ 1 := by
  haveI : ValuativeExtension K M := TauCeti.ValuativeExtension.trans K (fixedField H) M
  exact Valuation.Integers.isIntegral_iff_valuation_le_one
    (Valuation.integer.integers (ValuativeRel.valuation K)) x

/-- **$\mathfrak m_M$**: $x \in M$ is the image of an element of `maxIdealL M` iff its valuation is $< 1$. -/
theorem exists_maxIdealL_iff (x : M) :
    (∃ y ∈ maxIdealL M, (y : M) = x) ↔ ValuativeRel.valuation M x < 1 := by
  haveI : ValuativeExtension K M := TauCeti.ValuativeExtension.trans K (fixedField H) M
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy1 : y ∈ maxIdealL M ^ 1 := by rwa [pow_one]
    have hm := (mem_maxIdealL_pow_iff M 1 y).1 hy1
    rw [pow_one] at hm
    have hv := (Valuation.mem_maximalIdeal_iff (v := ValuativeRel.valuation M)).1 hm
    rwa [TauCeti.coe_integerRingEquivIntegralClosure_symm_apply] at hv
  · intro h
    have hx : x ∈ integers M := (mem_integers_iff M H x).2 h.le
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have h1 : (⟨x, hx⟩ : integers M) ∈ maxIdealL M ^ 1 := by
      rw [mem_maxIdealL_pow_iff, pow_one]
      refine (Valuation.mem_maximalIdeal_iff (v := ValuativeRel.valuation M)).2 ?_
      rw [TauCeti.coe_integerRingEquivIntegralClosure_symm_apply]
      exact h
    rwa [pow_one] at h1

/-- **$M/M^H$ is unramified** in Tau Ceti's sense, from `IsUnramifiedOver M H` (trivial inertia in $H$). -/
theorem isUnramified_of_isUnramifiedOver (hH : IsUnramifiedOver M H) :
    TauCeti.IsUnramified (fixedField H) M := by
  rw [TauCeti.isUnramified_iff_ramificationIndex_eq_one,
    ← TauCeti.LocalFieldsRamification.natCard_lowerRamificationGroup_zero (fixedField H) M]
  have hbot : TauCeti.LocalFieldsRamification.lowerRamificationGroup (fixedField H) M 0 = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨σ', rfl⟩ := (galFixEquiv M H).surjective g
    rw [Subgroup.mem_bot]
    have h1 : (σ' : Gal(M/K)) = 1 := by
      apply hH σ'.1 σ'.2
      intro a ha
      refine (exists_maxIdealL_iff M H _).2 ?_
      have hmem := TauCeti.LocalFieldsRamification.mem_lowerRamificationGroup_iff.1 hg
        ⟨a, (mem_integers_iff M H a).1 ha⟩
      have hmem' : (galFixEquiv M H σ') • (⟨a, (mem_integers_iff M H a).1 ha⟩ : 𝒪[M]) -
          ⟨a, (mem_integers_iff M H a).1 ha⟩ ∈ 𝓂[M] := by
        simpa using hmem
      have := (Valuation.mem_maximalIdeal_iff (v := ValuativeRel.valuation M)).1 hmem'
      exact this
    have : σ' = 1 := Subtype.ext h1
    rw [this, map_one]
  rw [hbot, Subgroup.card_bot]

omit [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [ValuativeExtension (fixedField H) M] in
/-- The residue field of `baseOf M H` has the cardinality of the residue field of $M^H$. -/
theorem natCard_residueFieldL_baseOf :
    Nat.card (residueFieldL (baseOf M H)) = Nat.card 𝓀[fixedField H] := by
  let e : fixedField H ≃ₐ[K] baseOf M H := IntermediateField.equivMap (fixedField H) M.val
  haveI : FiniteDimensional K (baseOf M H) := e.toLinearEquiv.finiteDimensional
  letI : ValuativeRel (baseOf M H) := TauCeti.finiteIntermediateFieldValuativeRel K Ω (baseOf M H)
  letI : TopologicalSpace (baseOf M H) := TauCeti.finiteIntermediateFieldTopology K Ω (baseOf M H)
  haveI : ValuativeExtension K (baseOf M H) := TauCeti.finiteIntermediateField_valuativeExtension K Ω _
  haveI : IsNonarchimedeanLocalField (baseOf M H) :=
    TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω _
  rw [natCard_residueFieldL]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e.symm.integerRingEquiv.toRingEquiv).toEquiv

/-- **Frobenius of $M/M^H$**: the element of $H$ with Milne's Frobenius congruence (`IsFrobeniusOver`) is Tau Ceti's
`frobeniusAlgEquiv` of the unramified extension $M/M^H$. -/
theorem galFixEquiv_eq_frobenius [TauCeti.IsUnramified (fixedField H) M] {σ : Gal(M/K)}
    (hσ : IsFrobeniusOver M H σ) :
    galFixEquiv M H ⟨σ, hσ.1⟩ = TauCeti.frobeniusAlgEquiv (K := fixedField H) (L := M) := by
  apply TauCeti.eq_frobeniusAlgEquiv_of_valuation_sub_pow_lt_one
  intro y
  have hy : (y : M) ∈ integers M := (mem_integers_iff M H _).2 y.2
  obtain ⟨b, hb, hby⟩ := hσ.2 (y : M) hy
  rw [natCard_residueFieldL_baseOf M H] at hby
  exact (exists_maxIdealL_iff M H _).1 ⟨b, hb, hby⟩

/-- **$\mathrm{ord}_M$ restricts to $\mathrm{ord}_F$** on $F^\times$, $F = M^H$, when $M/F$ is unramified. -/
theorem ord_algebraMap_eq [TauCeti.IsUnramified (fixedField H) M] {v : Additive Mˣ →+ ℤ}
    (hv : IsNormalizedOrd M v) (a : (fixedField H)ˣ) :
    v (Additive.ofMul (Units.map (algebraMap (fixedField H) M : (fixedField H) →+* M).toMonoidHom a)) =
      (TauCeti.normalizedValuation (fixedField H) a).toAdd := by
  haveI : ValuativeExtension K M := TauCeti.ValuativeExtension.trans K (fixedField H) M
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[fixedField H]
  have hπM : Irreducible (algebraMap 𝒪[fixedField H] 𝒪[M] π) :=
    TauCeti.IsUnramified.irreducible_algebraMap hπ
  set eU : (fixedField H)ˣ →* Mˣ := Units.map (algebraMap (fixedField H) M : (fixedField H) →+* M).toMonoidHom
    with heU
  have hint : ∀ y : fixedField H, ValuativeRel.valuation (fixedField H) y ≤ 1 →
      algebraMap (fixedField H) M y ∈ integers M := by
    intro y hy
    rw [mem_integers_iff M H]
    have hy' : y ∈ 𝒪[fixedField H] := hy
    exact (algebraMap 𝒪[fixedField H] 𝒪[M] ⟨y, hy'⟩).2
  have hpF : ∀ h, Units.mk0 ((π : 𝒪[fixedField H]) : fixedField H) h = Units.mk0 ((π : 𝒪[fixedField H]) :
      fixedField H) (fun h' => hπ.ne_zero (Subtype.ext h')) := fun h => rfl
  set pF : (fixedField H)ˣ := Units.mk0 ((π : 𝒪[fixedField H]) : fixedField H)
    (fun h' => hπ.ne_zero (Subtype.ext h')) with hpFdef
  have hpM : ∀ h, Units.mk0 (((algebraMap 𝒪[fixedField H] 𝒪[M] π : 𝒪[M])) : M) h = eU pF :=
    fun h => Units.ext rfl
  -- v of the image of a uniformizer is 1
  have hvπ : v (Additive.ofMul (eU pF)) = 1 := by
    have hnn : 0 ≤ v (Additive.ofMul (eU pF)) := by
      apply hv.nonneg
      exact hint _ (by
        have : (π : fixedField H) ∈ 𝒪[fixedField H] := π.2
        exact this)
    obtain ⟨y, hy⟩ := hv.surj 1
    obtain ⟨u, m, hu, hm⟩ := TauCeti.exists_eq_mul_zpow_of_irreducible hπM (Additive.toMul y)
    rw [hpM] at hm
    have hu0 : v (Additive.ofMul u) = 0 := by
      rw [hv.ker]
      have hu1 : (u : M) ∈ integers M := (mem_integers_iff M H _).2 hu.le
      refine ⟨hu1, ?_⟩
      rw [Units.val_inv_eq_inv_val]
      exact (mem_integers_iff M H _).2 (by rw [map_inv₀, hu, inv_one])
    have : y = Additive.ofMul u + m • Additive.ofMul (eU pF) := by
      apply Additive.toMul.injective
      simp [hm]
    rw [this, map_add, map_zsmul, hu0, zero_add, smul_eq_mul] at hy
    exact Int.eq_one_of_mul_eq_one_left hnn hy
  let w : (fixedField H)ˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd (v (Additive.ofMul (eU x)))
      map_one' := by simp
      map_mul' := fun x y => by simp [map_mul, ofMul_mul, ofAdd_add] }
  have hw : w = TauCeti.normalizedValuation (fixedField H) := by
    refine TauCeti.eq_normalizedValuation w (fun x hx => ?_) hπ ?_
    · have hu : eU x ∈ unitsL M := by
        refine ⟨hint _ hx.le, ?_⟩
        have : ((eU x)⁻¹ : Mˣ) = eU x⁻¹ := (map_inv _ _).symm
        rw [this]
        refine hint _ ?_
        rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
      change Multiplicative.ofAdd (v (Additive.ofMul (eU x))) = 1
      rw [(hv.ker _).2 hu]; rfl
    · change Multiplicative.ofAdd (v (Additive.ofMul (eU pF))) = _
      rw [hvπ]
  have := congrArg (fun f : (fixedField H)ˣ →* Multiplicative ℤ => (f a).toAdd) hw
  simpa [w] using this

end Bridges

/-! ## (4) Theorem 2.1 on unramified extensions -/

/-- **Milne, CFT III, Thm. 2.1: normalization of the relative invariant on unramified extensions** (p. 103–105).
For a finite Galois $M/K$ in $\Omega$, a subgroup $H$ with $M/M^H$ unramified, a normalized valuation $\mathrm{ord}_M$
and the Frobenius element $\sigma \in H$ of $M/M^H$, Tau Ceti's relative invariant `tcInvRel M H` is Milne's
`invRel M hv H σ` (valuation, connecting map, evaluation at $\sigma$). -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 2.1, relative invariant on unramified extensions, p. 103–105"]
theorem tcInvRel_unramified (H : Subgroup Gal(M/K)) (hH : IsUnramifiedOver M H) {v : Additive Mˣ →+ ℤ}
    (hv : IsNormalizedOrd M v) {σ : Gal(M/K)} (hσ : IsFrobeniusOver M H σ) :
    tcInvRel M H = invRel M hv H ⟨σ, hσ.1⟩ := by
  refine AddMonoidHom.ext fun x => ?_
  let _ := TauCeti.algebraicExtensionValuativeRel (fixedField H) M
  let _ := TauCeti.algebraicExtensionNormedFieldTopology (fixedField H) M
  have := TauCeti.finiteExtension_isNonarchimedeanLocalField (fixedField H) M
  have := TauCeti.algebraicExtension_valuativeExtension (fixedField H) M
  have hU : TauCeti.IsUnramified (fixedField H) M := isUnramified_of_isUnramifiedOver M H hH
  rw [invRel_eq_invOf M H hv, galFixEquiv_eq_frobenius M H hσ,
    invOf_eq_unramifiedInv v (ord_invariant_fix M H hv) (ord_algebraMap_eq M H hv),
    tcInvRel_apply]
  congr 1
  exact invMap_relBrInfl_unramified (fixedField H) M (embFix M H) _

end Local

end NumberFieldKB.MilneCFT.Ch3
