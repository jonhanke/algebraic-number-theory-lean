import NumberFieldKB.MilneCFT.Ch7.NormTransitivity
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open IsDedekindDomain NumberField
open QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.Ideles

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

open NormTransitivity

attribute [local instance] adeleAlgebra

/-- If $[L:K']=1$ the idele norm $\mathbb I_L\to\mathbb I_{K'}$ is surjective. -/
theorem normIdeles_eq_top_of_finrank_eq_one (K' L : Type) [Field K'] [NumberField K'] [Field L]
    [NumberField L] [Algebra K' L] (h : Module.finrank K' L = 1) : normIdeles K' L = ⊤ := by
  refine top_unique fun y _ => ?_
  refine ⟨(ideleGroupEquiv L).symm (Units.map (adeleMap K' L : Adeles K' →* Adeles L)
    (ideleGroupEquiv K' y)), ?_⟩
  apply (ideleGroupEquiv K').injective
  change ideleGroupEquiv K' (ideleRelNorm (Module.finBasis K' L) _) = _
  rw [ideleGroupEquiv_ideleRelNorm, ContinuousMulEquiv.apply_symm_apply]
  refine Units.ext ?_
  rw [coe_adeleNorm]
  have hb : Module.finrank (Adeles K') (Adeles L) = 1 := by
    rw [Module.finrank_eq_card_basis (adeleBasis (Module.finBasis K' L)), Fintype.card_fin, h]
  have : Module.Finite (Adeles K') (Adeles L) :=
    Module.Finite.of_basis (adeleBasis (Module.finBasis K' L))
  have := Algebra.norm_algebraMap (R := Adeles K') (S := Adeles L)
    ((ideleGroupEquiv K' y : (Adeles K')ˣ) : Adeles K')
  rw [hb, pow_one] at this
  exact this

/-- Transport along an isomorphism: the norm ideles only depend on the $K$-algebra up to isomorphism. -/
theorem normIdeles_eq_aux (K L L' : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field L'] [NumberField L'] [Algebra K L] [Algebra K L'] [Algebra L' L] [IsScalarTower K L' L]
    (h : Module.finrank L' L = 1) : normIdeles K L = normIdeles K L' := by
  rw [← normIdeles_comp K L' L, normIdeles_eq_top_of_finrank_eq_one L' L h, Subgroup.map_top]
  rfl

theorem normIdeles_eq_of_algEquiv (K L L' : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field L'] [NumberField L'] [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L') :
    normIdeles K L = normIdeles K L' := by
  let _ : Algebra L' L := e.symm.toRingHom.toAlgebra
  have : IsScalarTower K L' L := IsScalarTower.of_algebraMap_eq fun t => by
    change algebraMap K L t = e.symm (algebraMap K L' t)
    exact (e.symm.commutes t).symm
  have h : Module.finrank L' L = 1 := by
    have hb : Function.Bijective (algebraMap L' L) := e.symm.bijective
    have e1 := (LinearEquiv.ofBijective (Algebra.linearMap L' L) hb).finrank_eq
    rw [← e1]
    exact Module.finrank_self L'
  exact normIdeles_eq_aux K L L' h

theorem principalNormIdeles_eq_of_algEquiv (K L L' : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Field L'] [NumberField L'] [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L') :
    principalNormIdeles K L = principalNormIdeles K L' := by
  rw [principalNormIdeles, principalNormIdeles, normIdeles_eq_of_algEquiv K L L' e]

end NumberFieldKB.MilneCFT.Ch7
