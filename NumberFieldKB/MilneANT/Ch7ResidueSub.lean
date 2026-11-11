import NumberFieldKB.MilneANT.Ch7Remark753
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Algebraic Number Theory*, proof of Proposition 7.50: the residue field of an intermediate field

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`,
proof of Proposition 7.50, p. 127.

Setting as in `Ch7Extensions.lean`: $A$ is a complete discrete valuation ring with fraction field $K$, $L/K$ a field
extension, $B$ the integral closure of $A$ in $L$ with residue field $l$, and $K'$ an intermediate field with
$B' = $ integral closure of $A$ in $K'$ and residue field $l'$. Since $B' = B \cap K'$, reduction identifies $l'$ with
the subfield $k' \subset l$ (`residueRange`): `ResidueSub.resIncl` is the (injective) map $l' \to l$ induced by
$B' \subset B$, `ResidueSub.range_resIncl` says its image is `residueRange A K L K'`, and
`ResidueSub.residueEquiv` is the resulting isomorphism $l' \cong k'$. For finite separable $K'$, $[k':k] = f$
(`ResidueSub.finrank_residueField'`), so $K'$ is unramified iff $[k':k] = [K':K]$
(`ResidueSub.isUnramified_iff_finrank`). Subextensions of unramified extensions are unramified
(`ResidueSub.isUnramified_of_le`).
-/

open IsLocalRing Polynomial

universe u v w

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneANT.ResidueSub

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]

/-! ## The inclusion of integral closures -/

section MapB

variable {E : Type v} [Field E] [Algebra A E] {F : Type w} [Field F] [Algebra A F]

/-- An $A$-algebra map of fields induces a map of the integral closures of $A$. -/
noncomputable def mapB (f : E →ₐ[A] F) : integralClosure A E →ₐ[A] integralClosure A F :=
  ((f.comp (integralClosure A E).val).codRestrict (integralClosure A F) (fun x => x.2.map f))

@[simp] theorem coe_mapB (f : E →ₐ[A] F) (x : integralClosure A E) : (mapB A f x : F) = f (x : E) := rfl

theorem mapB_injective (f : E →ₐ[A] F) : Function.Injective (mapB A f) := fun _ _ h =>
  Subtype.ext (f.toRingHom.injective (congrArg Subtype.val h))

/-- The map on integral closures is local: if the image of `x` is a unit, then so is `x`
(`x⁻¹` is integral over `A` as its image `(f x)⁻¹` is). -/
theorem isLocalHom_mapB (f : E →ₐ[A] F) : IsLocalHom (mapB A f) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨u, hu⟩ := hx
  have h1 : ((↑u⁻¹ : integralClosure A F) : F) * f (x : E) = 1 := by
    have := congrArg Subtype.val (u.inv_mul)
    rw [hu] at this
    exact this
  have hx0 : (x : E) ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at h1
    exact zero_ne_one h1
  have hinv : f ((x : E)⁻¹) = ((↑u⁻¹ : integralClosure A F) : F) := by
    rw [map_inv₀]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  have hint : IsIntegral A ((x : E)⁻¹) := by
    rw [← isIntegral_algHom_iff f f.toRingHom.injective, hinv]
    exact (↑u⁻¹ : integralClosure A F).2
  refine IsUnit.of_mul_eq_one (⟨(x : E)⁻¹, hint⟩ : integralClosure A E) (Subtype.ext ?_)
  simp [hx0]

end MapB

variable (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] (K' : IntermediateField K L)

instance instIsScalarTowerIntermediate : IsScalarTower A K' L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A K L]
    show _ = ((algebraMap A K' x : K') : L)
    rw [Algebra.algebraMap_eq_smul_one (A := K') x, IntermediateField.coe_smul, IntermediateField.coe_one,
      ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one]

section Incl

/-- The inclusion $B' = \mathcal O_{K'} \subset B = \mathcal O_L$ of integral closures. -/
noncomputable def incl : integralClosure A K' →ₐ[A] integralClosure A L :=
  mapB A (IsScalarTower.toAlgHom A K' L)

@[simp] theorem coe_incl (x : integralClosure A K') : (incl A K L K' x : L) = ((x : K') : L) := rfl

theorem incl_injective : Function.Injective (incl A K L K') := mapB_injective A _

instance isLocalHom_incl : IsLocalHom (incl A K L K') := isLocalHom_mapB A _

/-- The map $l' \to l$ of residue fields induced by $B' \subset B$. -/
noncomputable def resIncl :
    ResidueField (integralClosure A K') →ₐ[ResidueField A] ResidueField (integralClosure A L) where
  __ := ResidueField.map (incl A K L K' : integralClosure A K' →+* integralClosure A L)
  commutes' r := by
    obtain ⟨a, rfl⟩ := residue_surjective r
    have h := (ResidueField.mapAlgHom (incl A K L K')).commutes a
    have h1 := IsScalarTower.algebraMap_apply A (ResidueField A) (ResidueField (integralClosure A K')) a
    have h2 := IsScalarTower.algebraMap_apply A (ResidueField A) (ResidueField (integralClosure A L)) a
    show ResidueField.map _ (algebraMap _ _ (algebraMap A (ResidueField A) a)) =
      algebraMap _ _ (algebraMap A (ResidueField A) a)
    rw [← h1, ← h2]
    exact h

@[simp] theorem resIncl_residue (b : integralClosure A K') :
    resIncl A K L K' (residue _ b) = residue _ (incl A K L K' b) := rfl

theorem resIncl_injective : Function.Injective (resIncl A K L K') :=
  (resIncl A K L K').toRingHom.injective

theorem range_resIncl :
    (resIncl A K L K').range.toSubring = residueRange A K L K' := by
  ext y
  simp only [AlgHom.mem_range, Subalgebra.mem_toSubring, residueRange, Subring.mem_map, Subring.mem_comap]
  constructor
  · rintro ⟨b', rfl⟩
    obtain ⟨b, rfl⟩ := residue_surjective b'
    exact ⟨incl A K L K' b, by simp, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hint : IsIntegral A (⟨(c : L), hc⟩ : K') := by
      rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom A K' L) (algebraMap K' L).injective]
      exact c.2
    exact ⟨residue _ (⟨⟨(c : L), hc⟩, hint⟩ : integralClosure A K'), rfl⟩

/-- The image of $l'$ in $l$, as an intermediate field of $l/k$. -/
noncomputable def residueField' :
    IntermediateField (ResidueField A) (ResidueField (integralClosure A L)) :=
  (resIncl A K L K').fieldRange

theorem residueField'_toSubring :
    (residueField' A K L K').toSubalgebra.toSubring = residueRange A K L K' :=
  (range_resIncl A K L K')

/-- The residue field $l'$ of $K'$ is isomorphic to $k' \subset l$. -/
noncomputable def residueEquiv :
    ResidueField (integralClosure A K') ≃ₐ[ResidueField A] residueField' A K L K' :=
  AlgEquiv.ofInjectiveField (resIncl A K L K')

/-- $K' \subset K''$ implies $k' \subset k''$ (directly from the definition of `residueRange`). -/
theorem residueRange_mono {K' K'' : IntermediateField K L} (h : K' ≤ K'') :
    residueRange A K L K' ≤ residueRange A K L K'' :=
  fun _ hy => by
    obtain ⟨x, hx, rfl⟩ := Subring.mem_map.1 hy
    exact Subring.mem_map.2 ⟨x, h hx, rfl⟩

section Finite

variable [FiniteDimensional K K'] [Algebra.IsSeparable K K']

instance moduleFiniteIntegralClosure : Module.Finite A (integralClosure A K') :=
  IsIntegralClosure.finite A K K' (integralClosure A K')

instance finiteDimensional_residueField' : FiniteDimensional (ResidueField A) (residueField' A K L K') :=
  LinearEquiv.finiteDimensional (residueEquiv A K L K').toLinearEquiv

/-- $[k' : k] = f$: the residue field $k' \subset l$ of a finite separable $K'$ has degree $f$ over $k$. -/
theorem finrank_residueField' :
    Module.finrank (ResidueField A) (residueField' A K L K') = resDegMilne A K' := by
  rw [Thm758aFixed.resDeg_eq_finrank]
  exact (residueEquiv A K L K').toLinearEquiv.finrank_eq.symm

/-- $K'/K$ is unramified iff $[k' : k] = [K' : K]$ (Milne p. 124 and the proof of Prop. 7.50). -/
theorem isUnramified_iff_finrank :
    IsUnramifiedMilne A K K' ↔
      Module.finrank (ResidueField A) (residueField' A K L K') = Module.finrank K K' := by
  unfold IsUnramifiedMilne
  rw [finrank_residueField']

end Finite

end Incl

section Tower

variable [Algebra.IsSeparable K L] {K' K'' : IntermediateField K L}
  [FiniteDimensional K K'] [FiniteDimensional K K'']

/-- **Subextensions of unramified extensions are unramified** (used in the proof of Prop. 7.50(a), p. 127): if
$K' \subset K''$ are finite over $K$ and $K''/K$ is unramified, so is $K'/K$. Indeed $e(K''/K) = e(K'/K)\,e(K''/K')$
and $e(K''/K) = 1$, so $e(K'/K) = 1$ and $f = n$ by Cor. 7.42. -/
theorem isUnramified_of_le (h : K' ≤ K'') (hU : IsUnramifiedMilne A K K'') : IsUnramifiedMilne A K K' := by
  have hfin' : Module.Finite A (integralClosure A K') := IsIntegralClosure.finite A K K' _
  have hfin'' : Module.Finite A (integralClosure A K'') := IsIntegralClosure.finite A K K'' _
  have := Remark753.isDVR_of_finite A K K'
  have := Remark753.isDVR_of_finite A K K''
  let f : K' →ₐ[A] K'' := (IntermediateField.inclusion h).restrictScalars A
  let : Algebra (integralClosure A K') (integralClosure A K'') := (mapB A f).toRingHom.toAlgebra
  have : IsScalarTower A (integralClosure A K') (integralClosure A K'') :=
    IsScalarTower.of_algebraMap_eq fun x => ((mapB A f).commutes x).symm
  have : IsLocalHom (algebraMap (integralClosure A K') (integralClosure A K'')) := by
    show IsLocalHom (mapB A f).toRingHom
    exact ⟨(isLocalHom_mapB A f).map_nonunit⟩
  have hlies : (maximalIdeal (integralClosure A K'')).LiesOver (maximalIdeal (integralClosure A K')) := by
    refine ⟨?_⟩
    ext x
    simp [Ideal.under, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have : FaithfulSMul (integralClosure A K') (integralClosure A K'') :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (mapB_injective A f)
  have : Module.IsTorsionFree (integralClosure A K') (integralClosure A K'') := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    rw [Algebra.smul_def, mul_eq_zero] at hrm
    rcases hrm with h0 | h0
    · left; exact (mapB_injective A f) (by rw [map_zero]; exact h0)
    · right; exact h0
  have : Module.Flat (integralClosure A K') (integralClosure A K'') := inferInstance
  have htower := Ideal.ramificationIdx_tower (R := A) (q := maximalIdeal (integralClosure A K'))
    (r := maximalIdeal (integralClosure A K''))
  have hn'' : 0 < Module.finrank K K'' := Module.finrank_pos
  have hc'' := cor_7_42 A K K''
  have hc' := cor_7_42 A K K'
  have he'' : ramIdxMilne A K'' = 1 := by
    have : ramIdxMilne A K'' * Module.finrank K K'' = 1 * Module.finrank K K'' := by
      rw [one_mul]; unfold IsUnramifiedMilne at hU; rw [hU] at hc''; exact hc''
    exact Nat.eq_of_mul_eq_mul_right hn'' this
  have he' : ramIdxMilne A K' = 1 := by
    unfold ramIdxMilne at he'' ⊢
    rw [htower] at he''
    exact Nat.eq_one_of_mul_eq_one_right he''
  unfold IsUnramifiedMilne
  rw [he', one_mul] at hc'
  exact hc'

end Tower

end NumberFieldKB.MilneANT.ResidueSub
