import Mathlib.FieldTheory.IsSepClosed
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3InvCarry
import NumberFieldKB.MilneCFT.Ch3NormalizedOrd
import NumberFieldKB.MilneCFT.Ch3UnramifiedTauCeti
import NumberFieldKB.MilneCFT.Ch4BrauerTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.UnramifiedTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.Invariant

/-!
# Milne, *Class Field Theory*, Chapter III §1: the invariant map of an unramified extension is Tau Ceti's

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

For a finite unramified Galois extension $E/K$ inside $\Omega$, the invariant map `Ch3.invK E hv σ` of p. 99 (built from
$\mathrm{ord}_E$, the connecting map of $0 \to \mathbb Z \to \mathbb Q \to \mathbb Q/\mathbb Z \to 0$ and evaluation
at the Frobenius element) is Tau Ceti's unramified invariant `TauCeti.ClassFieldTheory.unramifiedInv K E`
(`invK_eq_unramifiedInv`). Both send the class of the carry cocycle of $a \in K^\times$ to
$\mathrm{ord}_K(a)/[E:K]$ (`invOf_carryCocycle`, Tau Ceti `unramifiedInv_unramifiedClass`), and these classes exhaust
$H^2(E/K)$.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- On $K^\times$, the normalized valuation of an unramified extension $E$ restricts to Tau Ceti's normalized
valuation of $K$. -/
theorem ord_embUnits_eq (E : IntermediateField K Ω) [FiniteDimensional K E] (hE : IsUnramifiedExt E)
    {v : Additive Eˣ →+ ℤ} (hv : IsNormalizedOrd E v) (a : Kˣ) :
    v (Additive.ofMul (embUnits E a)) = (TauCeti.normalizedValuation K a).toAdd := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let w : Kˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd (v (Additive.ofMul (embUnits E x)))
      map_one' := by simp
      map_mul' := fun x y => by simp [map_mul, ofMul_mul, ofAdd_add] }
  have hw : w = TauCeti.normalizedValuation K := by
    refine TauCeti.eq_normalizedValuation w (fun x hx => ?_) hπ ?_
    · have hint : ∀ y : K, ValuativeRel.valuation K y ≤ 1 → algebraMap K E y ∈ integers E := by
        intro y hy
        have : y ∈ 𝒪[K] := hy
        have e : algebraMap K E y = algebraMap 𝒪[K] E ⟨y, this⟩ :=
          (IsScalarTower.algebraMap_apply 𝒪[K] K E ⟨y, this⟩)
        rw [e]
        exact isIntegral_algebraMap
      have hu : embUnits E x ∈ unitsL E := by
        refine ⟨hint _ hx.le, ?_⟩
        have : ((embUnits E x)⁻¹ : Eˣ) = embUnits E x⁻¹ := (map_inv _ _).symm
        rw [this]
        refine hint _ ?_
        rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
      change Multiplicative.ofAdd (v (Additive.ofMul (embUnits E x))) = 1
      rw [(hv.ker _).2 hu]; rfl
    · change Multiplicative.ofAdd (v (Additive.ofMul (embUnits E (primeUnit hπ)))) = _
      rw [ord_embUnits (unitPrimeDecomposition K Ω) E hE hv hπ]
  have := congrArg (fun f : Kˣ →* Multiplicative ℤ => (f a).toAdd) hw
  simpa [w] using this

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
  [TauCeti.IsUnramified K E]

/-- **Our invariant map of an unramified extension is Tau Ceti's** (Milne, *CFT*, III, §1, p. 99–101):
`Ch3.invK E hv σ` (normalized valuation, connecting map, Frobenius) agrees with
`TauCeti.ClassFieldTheory.unramifiedInv K E` under $\mathbb Q/\mathbb Z \simeq$ `AddCircle (1 : ℚ)`. -/
@[kb "milne2020cft" "v4.03, Ch. III, §1, the invariant map inv_{L/K} of an unramified L/K, p. 99–101"]
theorem invK_eq_unramifiedInv {v : Additive Eˣ →+ ℤ} (hv : IsNormalizedOrd E v) {σ : Gal(E/K)}
    (hσ : IsFrobenius E σ) (x : H2 E) :
    invK E hv σ x = Ch4.addCircleEquivQZ (TauCeti.ClassFieldTheory.unramifiedInv K E x) := by
  classical
  have hE : IsUnramifiedExt E := (isUnramified_iff_isUnramifiedExt E).1 inferInstance
  have hσF : σ = TauCeti.frobeniusAlgEquiv (K := K) (L := E) := eq_frobeniusAlgEquiv_of_isFrobenius E σ hσ
  subst hσF
  set g := TauCeti.frobeniusAlgEquiv (K := K) (L := E) with hgdef
  have hg : ∀ τ : E ≃ₐ[K] E, τ ∈ Subgroup.zpowers g := fun τ => by
    rw [hgdef, TauCeti.zpowers_frobeniusAlgEquiv]; exact Subgroup.mem_top τ
  obtain ⟨a, rfl⟩ := TauCeti.ClassFieldTheory.unramifiedClass_surjective K E x
  obtain ⟨zM, hzM, hval⟩ := TauCeti.exists_H2π_eq_cyclicClass hg (Additive.toMul a)
  have hord : orderOf g = Nat.card (E ≃ₐ[K] E) := by
    rw [← Nat.card_zpowers g]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv hg)
  have hp : ∀ τ : E ≃ₐ[K] E, (Rep.ofAlgebraAutOnUnits K E).ρ τ (Additive.ofMul (embUnits E (Additive.toMul a))) =
      Additive.ofMul (embUnits E (Additive.toMul a)) := fun τ =>
    congrArg Additive.ofMul (gal_smul_embUnits E τ _)
  have hz : zM = carryCocycle hg (Rep.ofAlgebraAutOnUnits K E)
      (Additive.ofMul (embUnits E (Additive.toMul a))) hp := by
    apply Subtype.ext
    funext p
    obtain ⟨τ₁, τ₂⟩ := p
    refine Eq.trans ?_ (carryCocycle_apply hg _ _ hp _).symm
    have h1 := pow_cycExp hg τ₁
    have h2 := pow_cycExp hg τ₂
    have l1 := cycExp_lt hg τ₁
    have l2 := cycExp_lt hg τ₂
    have key := hval (cycExp hg τ₁) (cycExp hg τ₂) (hord ▸ l1) (hord ▸ l2)
    rw [h1, h2, hord] at key
    apply Additive.toMul.injective
    change Additive.toMul (zM (τ₁, τ₂)) = _
    rw [key]
    dsimp only
    by_cases c : cycExp hg τ₁ + cycExp hg τ₂ < Nat.card (E ≃ₐ[K] E)
    · simp only [c, ↓reduceIte, show ¬ (Nat.card (E ≃ₐ[K] E) ≤ cycExp hg τ₁ + cycExp hg τ₂) by omega]
      rfl
    · simp only [c, ↓reduceIte, show Nat.card (E ≃ₐ[K] E) ≤ cycExp hg τ₁ + cycExp hg τ₂ by omega]
      rfl
  have hcls : TauCeti.ClassFieldTheory.unramifiedClass K E a =
      H2π _ (carryCocycle hg (Rep.ofAlgebraAutOnUnits K E)
        (Additive.ofMul (embUnits E (Additive.toMul a))) hp) := by
    rw [TauCeti.ClassFieldTheory.unramifiedClass_eq_cyclicClass K E hg]
    change TauCeti.cyclicClass hg (Additive.ofMul (Additive.toMul a)) = _
    rw [← hzM, hz]
    rfl
  have hv' : (show ℤ from (ordRep hv).hom (Additive.ofMul (embUnits E (Additive.toMul a)))) =
      (TauCeti.normalizedValuation K (Additive.toMul a)).toAdd :=
    ord_embUnits_eq E hE hv _
  have lhs : invK E hv g (TauCeti.ClassFieldTheory.unramifiedClass K E a) =
      qz (((TauCeti.normalizedValuation K (Additive.toMul a)).toAdd : ℚ) / Nat.card (E ≃ₐ[K] E)) := by
    rw [hcls, ← hv']
    exact invOf_carryCocycle hg (Rep.ofAlgebraAutOnUnits K E) (ordRep hv) _ hp
  have rhs := TauCeti.ClassFieldTheory.unramifiedInv_unramifiedClass (K := K) (L := E) (Additive.toMul a)
  rw [lhs, IsGalois.card_aut_eq_finrank]
  erw [rhs]
  rfl

end NumberFieldKB.MilneCFT.Ch3
