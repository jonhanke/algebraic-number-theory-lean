import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3ArtinMaps
import NumberFieldKB.MilneCFT.LocalCFT.AutoCompatible
import NumberFieldKB.MilneCFT.LocalCFT.UniverseTransport
import NumberFieldKB.MilneCFT.LocalCFT.ReciprocityTauCeti

/-!
# Milne, *Class Field Theory*, Chapter III, Lemma 3.2 (proved)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, p. 107.

`lemma3_2` proves the named statement `Lemma3_2 K Ω` unconditionally. Both local Artin maps are Tau Ceti's
(`tauCetiArtin`, by uniqueness `isLocalArtinMap_unique_univ`). Part (i) is Tau Ceti's norm functoriality
`artinMap_norm` of the absolute Artin maps, read through the restriction maps to $L$ and the identification
`separableClosureRingEquiv` of the separable closures of $E$ and $K$. Part (ii) follows from (i) since
$\mathrm{Nm}_{E/K}(a) = a^{[E:K]}$ for $a \in K^\times$.
-/

open scoped ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch3

open NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT TauCeti TauCeti.ClassFieldTheory

set_option synthInstance.maxHeartbeats 400000

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Core

variable (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra K E] [FiniteDimensional K E] [Algebra E Ω] [IsScalarTower K E Ω] [IsSepClosure E Ω]

/-- The core of (i), for Tau Ceti's Artin maps. -/
theorem tauCetiArtin_norm (L : FiniteAbelianExt K Ω) (L' : FiniteAbelianExt E Ω)
    (hLL' : ∀ x : Ω, x ∈ L.toField ↔ x ∈ L'.toField) (a : Eˣ) (x : Ω) (hx : x ∈ L.toField) :
    ((tauCetiArtin L (Units.map (Algebra.norm K (S := E)) a) ⟨x, hx⟩ : L.toField) : Ω) =
      ((tauCetiArtin L' a ⟨x, (hLL' x).1 hx⟩ : L'.toField) : Ω) := by
  have _ : ValuativeExtension K E := valuativeExtension_of_finite K E
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E Ω
  let iota : E →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let e := separableClosureRingEquiv K E iota
  let ι' := sepEmb L'
  let c : L.toField →+* L'.toField :=
    { toFun := fun y => ⟨y.1, (hLL' _).1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ι : L.toField →ₐ[K] SeparableClosure K :=
    { toRingHom := e.toRingHom.comp (ι'.toRingHom.comp c)
      commutes' := fun r => by
        have h1 : c (algebraMap K L.toField r) = algebraMap E L'.toField (algebraMap K E r) :=
          Subtype.ext (by simp [c, IsScalarTower.algebraMap_apply K E Ω])
        change e (ι' (c (algebraMap K L.toField r))) = _
        rw [h1, AlgHom.commutes, ← IsScalarTower.algebraMap_apply K E (SeparableClosure E)]
        exact separableClosureRingEquiv_algebraMap_base K E iota r }
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap E a)
  have hnorm := TauCeti.ClassFieldTheory.artinMap_norm E iota a τ hτ
  set σK := absoluteGaloisGroupExtend K E iota τ
  have hK : tauCetiArtin L (Algebra.normUnits K a) =
      ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σK) := by
    apply (abelianizationOfEquiv Gal(L.toField/K)).injective
    rw [abelianizationOfEquiv_apply, abelianizationOfEquiv_apply, abelianizationOf_tauCetiArtin L ι,
      artinMap_restrict K L.toField ι _ σK hnorm]
    rfl
  have hE : tauCetiArtin L' a = ι'.restrictNormalHom (absoluteGaloisGroupRestrictEquiv E τ) := by
    apply (abelianizationOfEquiv Gal(L'.toField/E)).injective
    rw [abelianizationOfEquiv_apply, abelianizationOfEquiv_apply, abelianizationOf_tauCetiArtin L' ι',
      artinMap_restrict E L'.toField ι' a τ hτ]
    rfl
  change ((tauCetiArtin L (Algebra.normUnits K a) ⟨x, hx⟩ : L.toField) : Ω) = _
  set y : L.toField := ⟨x, hx⟩
  have key : ι (tauCetiArtin L (Algebra.normUnits K a) y) = e (ι' (tauCetiArtin L' a (c y))) := by
    rw [hK, hE, AlgHom.restrictNormalHom_commutes, AlgHom.restrictNormalHom_commutes]
    exact absoluteGaloisGroupExtend_apply_separableClosureRingEquiv K E iota τ (ι' (c y))
  have key2 : c (tauCetiArtin L (Algebra.normUnits K a) y) = tauCetiArtin L' a (c y) :=
    ι'.injective (e.injective key)
  exact congrArg Subtype.val key2

end Core

theorem isLocalArtinMap_tauCetiArtin {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {Ω' : Type} [Field Ω'] [Algebra F Ω'] [IsSepClosure F Ω'] :
    IsLocalArtinMap (fun L : FiniteAbelianExt F Ω' => tauCetiArtin L) :=
  ⟨galRestrict_tauCetiArtin, fun hπ L hL => isFrobenius_tauCetiArtin hπ L hL, ker_tauCetiArtin,
    surjective_tauCetiArtin⟩

variable (K Ω) in
/-- **Lemma 3.2** (Milne, *CFT*, III, p. 107; Milne: "proof to be added"), proved unconditionally. For a finite
extension $E/K$ of local fields inside $\Omega$ and $L \supseteq E$ finite abelian over $K$: (i)
$\phi_{L/K}(\mathrm{Nm}_{E/K}\,a) = \phi_{L/E}(a)$ for $a \in E^\times$ (`tauCetiArtin_norm`, from Tau Ceti's
norm functoriality of the absolute Artin maps); (ii) $\phi_{L/E}(a) = \phi_{L/K}(a)^{[E:K]}$ for
$a \in K^\times$, from (i) since $\mathrm{Nm}_{E/K}(a) = a^{[E:K]}$. Arbitrary local Artin maps are Tau Ceti's
by uniqueness. -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 3.2, p. 107"]
theorem lemma3_2 : Lemma3_2 K Ω := by
  refine ⟨fun E _ _ _ _ _ _ _ _ _ φK φE hK hE L L' hLL' => ?_⟩
  have h1 : φK = fun L : FiniteAbelianExt K Ω => tauCetiArtin L :=
    isLocalArtinMap_unique_univ hK isLocalArtinMap_tauCetiArtin
  have h2 : φE = fun L : FiniteAbelianExt E Ω => tauCetiArtin L :=
    isLocalArtinMap_unique_univ hE isLocalArtinMap_tauCetiArtin
  subst h1 h2
  have hi : ∀ (a : Eˣ) (x : Ω) (hx : x ∈ L.toField),
      ((tauCetiArtin L (Units.map (Algebra.norm K (S := E)) a) ⟨x, hx⟩ : L.toField) : Ω) =
        ((tauCetiArtin L' a ⟨x, (hLL' x).1 hx⟩ : L'.toField) : Ω) :=
    fun a x hx => tauCetiArtin_norm E L L' hLL' a x hx
  refine ⟨hi, fun a x hx => ?_⟩
  have := hi (Units.map (algebraMap K E).toMonoidHom a) x hx
  have hn : Units.map (Algebra.norm K (S := E)) (Units.map (algebraMap K E).toMonoidHom a) =
      a ^ Module.finrank K E := Algebra.normUnits_unitsMap_algebraMap K a
  rw [hn, map_pow] at this
  exact this.symm

end NumberFieldKB.MilneCFT.Ch3
