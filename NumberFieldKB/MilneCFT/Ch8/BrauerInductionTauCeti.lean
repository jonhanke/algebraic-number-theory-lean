import NumberFieldKB.MilneCFT.Ch8.BrauerInductionUncond
import NumberFieldKB.TauCetiPort.RepresentationTheory.Induction.Brauer.Induction
import NumberFieldKB.TauCetiPort.RepresentationTheory.Induction.Monomial
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Brauer's induction theorem from Tau Ceti (Milne, *CFT*, VIII, §10, p. 262)

Bridge from the ported Tau Ceti proof (`NumberFieldKB/TauCetiPort/RepresentationTheory/Induction/Brauer/Induction`,
`.../Monomial`; see the README section "Brauer induction") to `BrauerInduction`.

* Tau Ceti: `TauCeti.ClassFunction.character_mem_indCharacterSpanInt_isElementary` (the character of every
  `FDRep ℂ G` is an integral combination of characters induced from irreducible characters of elementary
  subgroups) and `FDRep.exists_character_eq_indClassFun_of_isNilpotent` (irreducible characters of nilpotent,
  e.g. elementary, groups are induced from linear characters).
* Here: Tau Ceti's coset-sum `Subgroup.indClassFun` agrees with our `indFun` on class functions
  (`BrauerTC.indClassFun_eq_indFun`); transitivity of induction turns "induced from an irreducible character
  of an elementary `C`" into "induced from a linear character of a subgroup of `G`", which lies in
  `brauerSpan G` by `indFun_mem_zspan`.

`BrauerData` (the stronger elementary-subgroup datum with `1 = ∑ mᵢ Ind φᵢ`) is not proved here; it is not needed
for `BrauerInduction`.
-/

open scoped Classical

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

namespace BrauerTC

open TauCeti

/-- Tau Ceti's induction (sum over coset representatives) agrees with `indFun` on class functions. -/
lemma indClassFun_eq_indFun {G : Type} [Group G] [Fintype G] (K : Subgroup G) (f : K → ℂ)
    (hf : f ∈ ClassFunction ℂ K) (g : G) :
    Subgroup.indClassFun K f g = indFun K f g := by
  have hu : IsUnit (Nat.card K : ℂ) :=
    (Nat.cast_ne_zero.mpr Nat.card_pos.ne').isUnit
  rw [Subgroup.indClassFun_eq_natCard_inv_mul_sum K hu hf g]
  unfold indFun
  congr 1
  refine Fintype.sum_equiv (Equiv.inv G) _ _ (fun x => ?_)
  simp only [Equiv.inv_apply, inv_inv]

/-- The generators: a character induced from an irreducible character of an elementary subgroup lies in
`brauerSpan G`. -/
lemma induced_irreducible_mem {G : Type} [Group G] [Fintype G] (C : Subgroup G)
    (hC : IsElementary C) (n : ℕ) (ρ : Representation ℂ C (Fin n → ℂ)) (hρ : ρ.IsIrreducible) :
    ((C.indClassFunction (ClassFunction.ofCharacter ρ) : ClassFunction ℂ G) : G → ℂ) ∈
      brauerSpan G := by
  let W : FDRep ℂ C := FDRep.of ρ
  haveI : Representation.IsIrreducible W.ρ := hρ
  haveI : CategoryTheory.Simple W := FDRep.simple_of_isIrreducible W
  haveI : Group.IsNilpotent C := hC.isNilpotent
  obtain ⟨H₀, χ, hχ⟩ := FDRep.exists_character_eq_indClassFun_of_isNilpotent W
  obtain ⟨L, hLT, rfl⟩ : ∃ L ≤ C, L.subgroupOf C = H₀ :=
    ⟨H₀.map C.subtype, Subgroup.map_subtype_le H₀,
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective H₀⟩
  let ψ : L →* ℂˣ := χ.comp (Subgroup.subgroupOfEquivOfLe hLT).symm.toMonoidHom
  have hψ : (fun l : L => (ψ l : ℂ)) ∈ ClassFunction ℂ L :=
    MonoidHom.comp_mem_classFunction ψ (fun u : ℂˣ => (u : ℂ))
  have key := Subgroup.indClassFun_indClassFun_subgroupOf L hLT (ClassFunction.mem_iff.mp hψ)
  have hfun : (fun x => (fun l : L => (ψ l : ℂ)) (Subgroup.subgroupOfEquivOfLe hLT x)) =
      fun h => (χ h : ℂ) := by
    funext x
    simp [ψ]
  rw [hfun] at key
  have h1 : ((C.indClassFunction (ClassFunction.ofCharacter ρ) : ClassFunction ℂ G) : G → ℂ) =
      Subgroup.indClassFun L (fun l : L => (ψ l : ℂ)) := by
    funext g
    have e1 : ((C.indClassFunction (ClassFunction.ofCharacter ρ) : ClassFunction ℂ G) : G → ℂ) g =
        Subgroup.indClassFun C W.character g := rfl
    rw [e1, hχ]
    exact congrFun key g
  rw [h1]
  have h2 : Subgroup.indClassFun L (fun l : L => (ψ l : ℂ)) =
      indFun L (fun l : L => (ψ l : ℂ)) :=
    funext fun g => indClassFun_eq_indFun L _ hψ g
  rw [h2]
  exact indFun_mem_zspan L (Submodule.subset_span ⟨ψ, rfl⟩)

end BrauerTC

/-- **Brauer's induction theorem** (Milne, *CFT*, VIII, §10, p. 262): the trace of every complex representation of
a finite group is an integral combination of characters induced from linear characters of subgroups. Proved from
the ported Tau Ceti theory of Brauer induction. -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (Brauer's induction theorem)"]
theorem brauerInduction : BrauerInduction where
  span G _ _ _ n ρ := by
    let σ : Representation ℂ G (Fin n → ℂ) :=
      ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] _).toAlgHom.toMonoidHom).comp
        ((Units.coeHom _).comp ρ)
    let V : FDRep ℂ G := FDRep.of σ
    have h := TauCeti.ClassFunction.character_mem_indCharacterSpanInt_isElementary V
    have hle : TauCeti.ClassFunction.indCharacterSpanInt ℂ G (fun E => TauCeti.IsElementary E) ≤
        (brauerSpan G).toAddSubgroup :=
      TauCeti.ClassFunction.indCharacterSpanInt_le_iff.2 fun C hC m τ hτ =>
        BrauerTC.induced_irreducible_mem C hC m τ hτ
    have h2 : V.character ∈ brauerSpan G := hle h
    have h3 : V.character = fun g => Matrix.trace ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
      funext g
      show LinearMap.trace ℂ _ (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) ℂ)) = _
      rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), ← Matrix.toLin_eq_toLin',
        LinearMap.toMatrix_toLin]
    rwa [h3] at h2

end NumberFieldKB.MilneCFT.Ch8
