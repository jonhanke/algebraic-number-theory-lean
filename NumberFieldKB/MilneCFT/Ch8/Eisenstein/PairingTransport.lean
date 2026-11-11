import NumberFieldKB.MilneCFT.Ch8.Eisenstein.LocalGlobal
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Transport of the local Hilbert pairing along an isomorphism of local fields

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter I, Theorem 1.1
(the local Artin map is determined by the local field) and Chapter III, Remark 4.5 (the Hilbert symbol from the
local Artin map).

For a continuous ring isomorphism $e : F \to F'$ of nonarchimedean local fields, the Hilbert pairings of order $p$
(built from any local Artin maps) correspond: $(e\,a, e\,b)_{F'} = e\,(a, b)_F$ (`hilbertPairing_map_equiv`). The
proof uses the naturality of Tau Ceti's absolute local Artin map (`TauCeti.ClassFieldTheory.artinMap_congr`) and the
description of the pairing through it (`hilbertPairing_eq_of_artinMap`).
-/

open scoped ValuativeRel
open NumberFieldKB.MilneCFT.LocalCFT

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.Eisenstein

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {Ω : Type} [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
variable {F' : Type} [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']
variable {Ω' : Type} [Field Ω'] [Algebra F' Ω'] [IsSepClosure F' Ω']
variable {p : ℕ} [Fact p.Prime]

/-- **Transport of the Hilbert pairing** along a continuous isomorphism of local fields. -/
theorem hilbertPairing_map_equiv (e : F ≃+* F') (he : Continuous e) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ p)
    {ζ' : F'ˣ} (hζ' : IsPrimitiveRoot ζ' p)
    {φ : ∀ L : FiniteAbelianExt F Ω, Fˣ →* Gal(L.toField/F)} (hφ : IsLocalArtinMap φ)
    {φ' : ∀ L : FiniteAbelianExt F' Ω', F'ˣ →* Gal(L.toField/F')} (hφ' : IsLocalArtinMap φ') (a b : Fˣ) :
    (hilbertPairing hζ' hφ' (Units.map e.toMonoidHom a) (Units.map e.toMonoidHom b) : F') =
      e (hilbertPairing hζ hφ a b) := by
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap F b)
  set e' : AlgebraicClosure F ≃+* AlgebraicClosure F' :=
    IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure F') e
  have he' : ∀ c : F, e' (algebraMap F (AlgebraicClosure F) c) = algebraMap F' (AlgebraicClosure F') (e c) :=
    fun c => IsAlgClosure.equivOfEquiv_algebraMap _ _ e c
  let σ' : Field.absoluteGaloisGroup F' :=
    AlgEquiv.ofRingEquiv (f := e'.symm.trans (τ.toRingEquiv.trans e')) (fun c => by
      simp only [RingEquiv.trans_apply]
      have h1 : e'.symm (algebraMap F' (AlgebraicClosure F') c) =
          algebraMap F (AlgebraicClosure F) (e.symm c) := by
        rw [RingEquiv.symm_apply_eq, he', RingEquiv.apply_symm_apply]
      rw [h1]
      have h2 : τ.toRingEquiv (algebraMap F (AlgebraicClosure F) (e.symm c)) =
          algebraMap F (AlgebraicClosure F) (e.symm c) := τ.commutes _
      rw [h2, he', RingEquiv.apply_symm_apply])
  have hσσ' : ∀ y : AlgebraicClosure F, e' (τ.toRingEquiv y) = σ'.toRingEquiv (e' y) := by
    intro y
    change _ = e' (τ.toRingEquiv (e'.symm (e' y)))
    rw [RingEquiv.symm_apply_apply]
  have hτ' := TauCeti.ClassFieldTheory.artinMap_congr e he e' he' b τ σ' hσσ' hτ
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) (a : F))
    (Fact.out : p.Prime).pos
  have h1 := hilbertPairing_eq_of_artinMap hζ hφ a b τ hτ hγ
  have hγ' : (e' γ) ^ p = algebraMap F' (AlgebraicClosure F') (Units.map e.toMonoidHom a : F') := by
    rw [← map_pow, hγ, he']; rfl
  have h2 := hilbertPairing_eq_of_artinMap hζ' hφ' _ _ σ' hτ' hγ'
  have hγ0 : e' γ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at hγ'
    exact (Units.map e.toMonoidHom a).ne_zero ((map_eq_zero _).mp hγ'.symm)
  have h3 : DFunLike.coe (F := Gal(AlgebraicClosure F'/F')) σ' (e' γ) =
      algebraMap F' (AlgebraicClosure F') (e (hilbertPairing hζ hφ a b : F)) * e' γ := by
    have := hσσ' γ
    change e' (DFunLike.coe (F := Gal(AlgebraicClosure F/F)) τ γ) = _ at this
    rw [h1, map_mul, he'] at this
    exact this.symm
  apply (algebraMap F' (AlgebraicClosure F')).injective
  exact mul_right_cancel₀ hγ0 (h2.symm.trans h3)

end NumberFieldKB.MilneCFT.Ch8.Eisenstein
