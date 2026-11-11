/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumberFieldKB.MilneCFT.Ch8.BrauerInductionTauCeti
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Brauer's elementary-subgroup datum, corrected (Milne, *CFT*, VIII, §10, p. 262; Serre, §§10–11)

`BrauerData` (in `BrauerInductionUncond.lean`) is false as stated (`not_brauerData`, `Brauer/BrauerDataFalse.lean`):
it asks for `χ|_{Hᵢ} φᵢ` in the `ℤ`-span of the *linear* characters of `Hᵢ`. The corrected datum
`BrauerDataElementary` asks for what Brauer's argument gives (Serre, *Linear Representations of Finite Groups*,
§10.5, Theorem 19 and §11.1): for the trace `χ` of a representation `ρ` of `G`, elementary subgroups `Hᵢ`, integers
`mᵢ` and characters `φᵢ` of representations of `Hᵢ` with

* `1 = ∑ mᵢ Ind_{Hᵢ} φᵢ` (Brauer's theorem for the unit character), and
* `χ|_{Hᵢ} φᵢ` in `brauerSpan Hᵢ`, the `ℤ`-span of characters of `Hᵢ` induced from linear characters of subgroups of
  `Hᵢ` (elementary groups are nilpotent, hence monomial).

Proof (`brauerDataElementary`): the unit character lies in Tau Ceti's `indCharacterSpanInt` for elementary subgroups
(`TauCeti.ClassFunction.character_mem_indCharacterSpanInt_isElementary`); each generator `Ind_C τ` is `indFun C`
of the matrix trace of a representation of `C` (`BrauerTC.indClassFun_eq_indFun`); and `χ|_C φ` is the character
of the tensor product `ρ|_C ⊗ τ` (`Representation.char_tensor`), which lies in `brauerSpan C`
(`character_mem_brauerSpan`, from the same Tau Ceti theorem).
-/

open scoped Classical

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

open TauCeti

namespace BrauerElem

/-- The character of every finite-dimensional complex representation lies in `brauerSpan G`. -/
lemma character_mem_brauerSpan {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (r : Representation ℂ G V) : r.character ∈ brauerSpan G := by
  let W : FDRep ℂ G := FDRep.of r
  have h := TauCeti.ClassFunction.character_mem_indCharacterSpanInt_isElementary W
  have hle : TauCeti.ClassFunction.indCharacterSpanInt ℂ G (fun E => TauCeti.IsElementary E) ≤
      (brauerSpan G).toAddSubgroup :=
    TauCeti.ClassFunction.indCharacterSpanInt_le_iff.2 fun C hC m τ hτ =>
      BrauerTC.induced_irreducible_mem C hC m τ hτ
  exact hle h

/-- The matrix form of a representation on `Fin k → ℂ`. -/
def toGL {H : Type} [Group H] {k : ℕ} (τ : Representation ℂ H (Fin k → ℂ)) : H →* GL (Fin k) ℂ :=
  MonoidHom.toHomUnits ((LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin k → ℂ) ≃ₐ[ℂ] _).toMonoidHom.comp τ)

lemma trace_toGL {H : Type} [Group H] {k : ℕ} (τ : Representation ℂ H (Fin k → ℂ)) (h : H) :
    Matrix.trace ((toGL τ h : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) = τ.character h := by
  show Matrix.trace (LinearMap.toMatrix' (τ h)) = LinearMap.trace ℂ _ (τ h)
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin k)), LinearMap.toMatrix_eq_toMatrix']

/-- The representation on `Fin n → ℂ` given by a matrix representation. -/
def ofGL {G : Type} [Group G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) : Representation ℂ G (Fin n → ℂ) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] _).toAlgHom.toMonoidHom).comp
    ((Units.coeHom _).comp ρ)

lemma character_ofGL {G : Type} [Group G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) (g : G) :
    (ofGL ρ).character g = Matrix.trace ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
  show LinearMap.trace ℂ _ (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) ℂ)) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), ← Matrix.toLin_eq_toLin',
    LinearMap.toMatrix_toLin]

/-- The generators: characters induced from (matrix) representations of elementary subgroups. -/
def elemSet (G : Type) [Group G] [Fintype G] : Set (G → ℂ) :=
  {f | ∃ (C : Subgroup G) (_ : IsElementary C) (k : ℕ) (τ : C →* GL (Fin k) ℂ),
    f = indFun C (fun h => Matrix.trace ((τ h : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ))}

lemma one_mem_span_elemSet (G : Type) [Group G] [Fintype G] :
    (fun _ : G => (1 : ℂ)) ∈ Submodule.span ℤ (elemSet G) := by
  let r : Representation ℂ G ℂ := 1
  let W : FDRep ℂ G := FDRep.of r
  have h := TauCeti.ClassFunction.character_mem_indCharacterSpanInt_isElementary W
  have hle : TauCeti.ClassFunction.indCharacterSpanInt ℂ G (fun E => TauCeti.IsElementary E) ≤
      (Submodule.span ℤ (elemSet G)).toAddSubgroup := by
    refine TauCeti.ClassFunction.indCharacterSpanInt_le_iff.2 fun C hC m τ _ => ?_
    refine Submodule.subset_span ⟨C, hC, m, toGL τ, ?_⟩
    funext g
    have hcl : (fun h : C => Matrix.trace ((toGL τ h : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)) ∈
        ClassFunction ℂ C := by
      have : (fun h : C => Matrix.trace ((toGL τ h : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)) =
          (ClassFunction.ofCharacter τ : C → ℂ) := funext fun h => trace_toGL τ h
      rw [this]; exact (ClassFunction.ofCharacter τ).2
    rw [← BrauerTC.indClassFun_eq_indFun C _ hcl g]
    have : (fun h : C => Matrix.trace ((toGL τ h : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)) =
        (ClassFunction.ofCharacter τ : C → ℂ) := funext fun h => trace_toGL τ h
    rw [this]
    rfl
  have h2 := hle h
  have h3 : W.character = fun _ => 1 := by
    funext g
    show LinearMap.trace ℂ ℂ (r g) = 1
    simp [r]
  rwa [h3] at h2

end BrauerElem

/-- **Brauer's elementary-subgroup datum** (corrected form of `BrauerData`; Serre, *Linear Representations of
Finite Groups*, §§10–11; Milne, *CFT*, VIII, §10, p. 262): for the trace $\chi$ of every complex representation of a
finite group $G$ there are elementary subgroups $H_i$, integers $m_i$ and characters $\varphi_i$ of representations
of $H_i$ with $1 = \sum_i m_i\,\mathrm{Ind}_{H_i}\varphi_i$ and $\chi|_{H_i}\varphi_i$ in the $\mathbb Z$-span of
characters of $H_i$ induced from linear characters of subgroups of $H_i$ (`brauerSpan`). -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (Brauer's theorem, elementary-subgroup data, corrected)"]
structure BrauerDataElementary : Prop where
  data : ∀ (G : Type) [Group G] [Fintype G] (n : ℕ) (ρ : G →* GL (Fin n) ℂ),
    ∃ (ι : Type) (s : Finset ι) (H : ι → Subgroup G) (m : ι → ℤ) (φ : ∀ i, H i → ℂ),
      (∀ i ∈ s, IsElementary (H i)) ∧
      (∀ i ∈ s, ∃ (k : ℕ) (τ : H i →* GL (Fin k) ℂ),
        φ i = fun h => Matrix.trace ((τ h : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ)) ∧
      (∀ g, ∑ i ∈ s, (m i : ℂ) * indFun (H i) (φ i) g = 1) ∧
      ∀ i ∈ s, (fun h : H i => Matrix.trace ((ρ (h : G) : GL (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) * φ i h) ∈ brauerSpan (H i)

/-- **Brauer's elementary-subgroup datum** (corrected form of `BrauerData`), proved from the ported Tau Ceti theory
of Brauer induction. -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (Brauer's theorem, elementary-subgroup data, corrected)"]
theorem brauerDataElementary : BrauerDataElementary where
  data G _ _ n ρ := by
    obtain ⟨N, c, g, hsum⟩ := Submodule.mem_span_set'.mp (BrauerElem.one_mem_span_elemSet G)
    have hg : ∀ i, ∃ (C : Subgroup G) (_ : IsElementary C) (k : ℕ) (τ : C →* GL (Fin k) ℂ),
        (g i : G → ℂ) = indFun C (fun h => Matrix.trace ((τ h : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ)) :=
      fun i => (g i).2
    choose C hC k τ hτ using hg
    refine ⟨Fin N, Finset.univ, C, c,
      fun i h => Matrix.trace ((τ i h : GL (Fin (k i)) ℂ) : Matrix (Fin (k i)) (Fin (k i)) ℂ),
      fun i _ => hC i, fun i _ => ⟨k i, τ i, rfl⟩, fun x => ?_, fun i _ => ?_⟩
    · have := congrFun hsum x
      simp only [Finset.sum_apply, zsmul_eq_mul, hτ] at this
      exact this
    · have hmem := BrauerElem.character_mem_brauerSpan
        (Representation.tprod (BrauerElem.ofGL (ρ.comp (C i).subtype)) (BrauerElem.ofGL (τ i)))
      rw [Representation.char_tensor] at hmem
      convert hmem using 1
      funext h
      simp only [Pi.mul_apply, BrauerElem.character_ofGL, MonoidHom.comp_apply, Subgroup.coe_subtype]

namespace BrauerElem

open TauCeti in
/-- Transitivity of induction on `brauerSpan`: `Ind_C^G` maps `brauerSpan C` into `brauerSpan G`. -/
lemma indFun_mem_brauerSpan {G : Type} [Group G] [Fintype G] (C : Subgroup G) {f : C → ℂ}
    (hf : f ∈ brauerSpan C) : indFun C f ∈ brauerSpan G := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨L', ψ, rfl⟩ := hx
    have hf' : (fun g : C => (Fintype.card L' : ℂ)⁻¹ *
        ∑ x : C, if h : x * g * x⁻¹ ∈ L' then (ψ ⟨_, h⟩ : ℂ) else 0) = indFun L' (fun l => (ψ l : ℂ)) := by
      funext g; simp [indFun, Nat.card_eq_fintype_card]
    rw [hf']
    obtain ⟨L, hLT, rfl⟩ : ∃ L ≤ C, L.subgroupOf C = L' :=
      ⟨L'.map C.subtype, Subgroup.map_subtype_le L',
        Subgroup.comap_map_eq_self_of_injective C.subtype_injective L'⟩
    let ψ' : L →* ℂˣ := ψ.comp (Subgroup.subgroupOfEquivOfLe hLT).symm.toMonoidHom
    have hψ' : (fun l : L => (ψ' l : ℂ)) ∈ ClassFunction ℂ L :=
      MonoidHom.comp_mem_classFunction ψ' (fun u : ℂˣ => (u : ℂ))
    have hψ : (fun l : L.subgroupOf C => (ψ l : ℂ)) ∈ ClassFunction ℂ (L.subgroupOf C) :=
      MonoidHom.comp_mem_classFunction ψ (fun u : ℂˣ => (u : ℂ))
    have key := Subgroup.indClassFun_indClassFun_subgroupOf L hLT (ClassFunction.mem_iff.mp hψ')
    have hfun : (fun x => (fun l : L => (ψ' l : ℂ)) (Subgroup.subgroupOfEquivOfLe hLT x)) =
        fun h => (ψ h : ℂ) := by
      funext x
      simp [ψ']
    rw [hfun] at key
    have hin : indFun (L.subgroupOf C) (fun l => (ψ l : ℂ)) =
        Subgroup.indClassFun (L.subgroupOf C) (fun l => (ψ l : ℂ)) :=
      funext fun g => (BrauerTC.indClassFun_eq_indFun _ _ hψ g).symm
    have hcl := Subgroup.indClassFun_mem_classFunction (L.subgroupOf C) hψ
    rw [hin, show indFun C (Subgroup.indClassFun (L.subgroupOf C) fun l => (ψ l : ℂ)) =
        Subgroup.indClassFun C (Subgroup.indClassFun (L.subgroupOf C) fun l => (ψ l : ℂ)) from
      funext fun g => (BrauerTC.indClassFun_eq_indFun C _ hcl g).symm, key,
      show Subgroup.indClassFun L (fun l : L => (ψ' l : ℂ)) = indFun L (fun l : L => (ψ' l : ℂ)) from
      funext fun g => BrauerTC.indClassFun_eq_indFun L _ hψ' g]
    exact indFun_mem_zspan L (Submodule.subset_span ⟨ψ', rfl⟩)
  | zero => rw [indFun_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : indFun C (x + y) = indFun C x + indFun C y := indFun_add C x y
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [indFun_zsmul]; exact Submodule.smul_mem _ _ hx

end BrauerElem

/-- **Brauer's induction theorem from the corrected elementary-subgroup datum** (Milne, *CFT*, VIII, §10, p. 262;
Serre, §10.5): Frobenius reciprocity (`indFun_mul_class`) and transitivity of induction
(`BrauerElem.indFun_mem_brauerSpan`). This is the corrected form of `brauerInduction_of_brauerData`, whose hypothesis
fails (`not_brauerData`). -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (Brauer's induction theorem, from the corrected elementary-subgroup data)"]
theorem brauerInduction_of_brauerDataElementary (h : BrauerDataElementary) : BrauerInduction where
  span G _ _ _ n ρ := by
    obtain ⟨ι, s, H, m, φ, -, -, h1, hmem⟩ := h.data G n ρ
    set χ : G → ℂ := fun g => Matrix.trace ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hχdef
    have hχ : ∀ x g, χ (x * g * x⁻¹) = χ g := fun x g => by
      simp only [hχdef, map_mul, map_inv, Units.val_mul]
      rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have : χ = ∑ i ∈ s, m i • indFun (H i) (fun h : H i => χ (h : G) * φ i h) := by
      funext g
      simp only [Finset.sum_apply, Pi.smul_apply]
      simp_rw [indFun_mul_class (H _) χ hχ, zsmul_eq_mul]
      calc χ g = χ g * ∑ i ∈ s, (m i : ℂ) * indFun (H i) (φ i) g := by rw [h1 g, mul_one]
        _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (BrauerElem.indFun_mem_brauerSpan (H i) (hmem i hi))

/-- The corrected datum holds, so `BrauerInduction` follows from it unconditionally (it is also proved directly,
`brauerInduction`). -/
theorem brauerInduction_of_brauerDataElementary_uncond : BrauerInduction :=
  brauerInduction_of_brauerDataElementary brauerDataElementary

end NumberFieldKB.MilneCFT.Ch8
