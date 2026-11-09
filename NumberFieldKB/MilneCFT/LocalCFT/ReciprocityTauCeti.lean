import NumberFieldKB.MilneCFT.LocalCFT.Basic
import NumberFieldKB.MilneCFT.LocalCFT.UnramifiedTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.Reciprocity
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.Unramified
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.ArtinMap

/-!
# The local reciprocity law from Tau Ceti (Milne, *CFT*, I, Theorem 1.1)

Tau Ceti constructs, for a nonarchimedean local field $K$ (in `Type`) and a finite Galois extension $L/K$ with an
embedding $\iota : L\to K^{\mathrm{sep}}$, the local Artin map `TauCeti.ClassFieldTheory.localArtinMap K L ι` :
$K^\times\to\mathrm{Gal}(L/K)^{\mathrm{ab}}$ (ported under `NumberFieldKB/TauCetiPort/` from Tau Ceti main
`85f3eb55`, Apache 2.0), with kernel the norm group (`ker_localArtinMap`), surjective (`surjective_localArtinMap`),
independent of $\iota$ (`localArtinMap_eq_of_iota`), the restrictions of one absolute Artin map (`artinMap_restrict`),
and sending a uniformizer to Frobenius when $L/K$ is unramified (`localArtinMap_uniformizer`).

This file assembles our family $\phi_L : K^\times\to\mathrm{Gal}(L/K)$ over the finite abelian extensions
$L\subseteq\Omega$ (`tauCetiArtin`) and proves the named statement `LocalReciprocityExistence`
(`localReciprocityExistence`). Tau Ceti's local class field theory is stated for $K$ in `Type` (universe $0$), so
the theorem is for $K$ in `Type`.
-/

open scoped ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

open TauCeti TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-! ### The abelianization of an abelian Galois group -/

/-- For a commutative group, `Abelianization.of` is an isomorphism. -/
def abelianizationOfEquiv (G : Type*) [Group G] [IsMulCommutative G] : G ≃* Abelianization G :=
  MulEquiv.ofBijective Abelianization.of
    ⟨(MonoidHom.ker_eq_bot_iff _).1 ((Abelianization.ker_of (G := G)).trans (commutator_eq_bot G)),
     fun y => QuotientGroup.induction_on y fun g => ⟨g, rfl⟩⟩

@[simp] theorem abelianizationOfEquiv_apply (G : Type*) [Group G] [IsMulCommutative G] (g : G) :
    abelianizationOfEquiv G g = Abelianization.of g := rfl

/-! ### The family of local Artin maps -/

variable (L : FiniteAbelianExt K Ω)

instance : Algebra.IsSeparable K L.toField :=
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  Algebra.isSeparable_tower_bot_of_isSeparable K L.toField Ω

/-- An embedding of $L$ into Tau Ceti's separable closure `SeparableClosure K`. -/
def sepEmb : L.toField →ₐ[K] SeparableClosure K := IsSepClosed.lift

/-- **The local Artin map** $\phi_L : K^\times\to\mathrm{Gal}(L/K)$ from Tau Ceti's `localArtinMap`, through
$\mathrm{Gal}(L/K)\cong\mathrm{Gal}(L/K)^{\mathrm{ab}}$ ($L/K$ is abelian). -/
def tauCetiArtin : Kˣ →* Gal(L.toField/K) :=
  (abelianizationOfEquiv Gal(L.toField/K)).symm.toMonoidHom.comp
    (MonoidHom.toAdditive.symm (localArtinMap K L.toField (sepEmb L)))

theorem abelianizationOf_tauCetiArtin (ι : L.toField →ₐ[K] SeparableClosure K) (a : Kˣ) :
    Abelianization.of (tauCetiArtin L a) = (localArtinMap K L.toField ι (Additive.ofMul a)).toMul := by
  rw [localArtinMap_eq_of_iota K L.toField ι (sepEmb L), ← abelianizationOfEquiv_apply]
  exact (abelianizationOfEquiv Gal(L.toField/K)).apply_symm_apply
    ((localArtinMap K L.toField (sepEmb L) (Additive.ofMul a)).toMul)

/-- The kernel of `tauCetiArtin L` is the norm group. -/
theorem ker_tauCetiArtin : (tauCetiArtin L).ker = normGroup L.toField := by
  ext a
  rw [MonoidHom.mem_ker, ← (abelianizationOfEquiv Gal(L.toField/K)).injective.eq_iff, map_one,
    abelianizationOfEquiv_apply, abelianizationOf_tauCetiArtin L (sepEmb L)]
  change (localArtinMap K L.toField (sepEmb L) (Additive.ofMul a)).toMul = 1 ↔ _
  rw [toMul_eq_one, localArtinMap_eq_zero_iff, TauCeti.mem_normGroup_iff]
  simp only [normGroup, MonoidHom.mem_range, Units.ext_iff, Units.coe_map]

theorem surjective_tauCetiArtin : Function.Surjective (tauCetiArtin L) := by
  intro g
  obtain ⟨a, ha⟩ :=
    surjective_localArtinMap K L.toField (sepEmb L) (Additive.ofMul (Abelianization.of g))
  refine ⟨a.toMul, (abelianizationOfEquiv Gal(L.toField/K)).injective ?_⟩
  rw [abelianizationOfEquiv_apply, abelianizationOfEquiv_apply, abelianizationOf_tauCetiArtin L (sepEmb L)]
  simp [ha]

/-- **Compatibility with restriction**: for $L\subseteq L'$, restricting $\phi_{L'}(a)$ to $L$ gives $\phi_L(a)$. Both
are restrictions of one absolute Artin symbol (`artinMap_restrict`), for compatible embeddings. -/
theorem galRestrict_tauCetiArtin (L L' : FiniteAbelianExt K Ω) (h : L.toField ≤ L'.toField) (a : Kˣ) :
    galRestrict h (tauCetiArtin L' a) = tauCetiArtin L a := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (artinMap K a)
  set ι' := sepEmb L'
  set ι : L.toField →ₐ[K] SeparableClosure K := ι'.comp (IntermediateField.inclusion h)
  set τ := absoluteGaloisGroupRestrictEquiv K σ
  have h' : tauCetiArtin L' a = ι'.restrictNormalHom τ := by
    apply (abelianizationOfEquiv Gal(L'.toField/K)).injective
    rw [abelianizationOfEquiv_apply, abelianizationOfEquiv_apply, abelianizationOf_tauCetiArtin L' ι',
      artinMap_restrict K L'.toField ι' a σ hσ]
    rfl
  have h1 : tauCetiArtin L a = ι.restrictNormalHom τ := by
    apply (abelianizationOfEquiv Gal(L.toField/K)).injective
    rw [abelianizationOfEquiv_apply, abelianizationOfEquiv_apply, abelianizationOf_tauCetiArtin L ι,
      artinMap_restrict K L.toField ι a σ hσ]
    rfl
  rw [h', h1]
  refine AlgEquiv.ext fun x => ?_
  apply ι.injective
  change ι _ = ι _
  rw [AlgHom.restrictNormalHom_commutes]
  change ι' (IntermediateField.inclusion h (galRestrict h (ι'.restrictNormalHom τ) x)) = _
  have : IntermediateField.inclusion h (galRestrict h (ι'.restrictNormalHom τ) x) =
      ι'.restrictNormalHom τ (IntermediateField.inclusion h x) :=
    Subtype.ext (galRestrict_apply h _ x)
  rw [this, AlgHom.restrictNormalHom_commutes]
  rfl

/-! ### Frobenius -/

/-- **Condition (a) of Theorem 1.1**: for a prime element $\pi$ and $L/K$ unramified, $\phi_L(\pi)$ is the Frobenius
element. From Tau Ceti's `localArtinMap_uniformizer` and the residue-field description of Tau Ceti's
`frobeniusAlgEquiv` (`residueField_toAlgEquiv_frobeniusAlgEquiv`). -/
theorem isFrobenius_tauCetiArtin {π : 𝒪[K]} (hπ : Irreducible π) (L : FiniteAbelianExt K Ω)
    (hL : IsUnramifiedExt L.toField) : IsFrobenius L.toField (tauCetiArtin L (primeUnit hπ)) := by
  let _ : ValuativeRel L.toField := TauCeti.finiteIntermediateFieldValuativeRel K Ω L.toField
  let _ : TopologicalSpace L.toField := TauCeti.finiteIntermediateFieldTopology K Ω L.toField
  have : ValuativeExtension K L.toField := TauCeti.finiteIntermediateField_valuativeExtension K Ω L.toField
  have : IsNonarchimedeanLocalField L.toField :=
    TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toField
  have hU : TauCeti.IsUnramified K L.toField := (isUnramified_iff_isUnramifiedExt L.toField).2 hL
  have hπU : IsUniformizer (K := K) (primeUnit hπ) :=
    (isUniformizer_iff_exists_irreducible K _).2 ⟨π, hπ, rfl⟩
  have hφ : tauCetiArtin L (primeUnit hπ) = frobeniusAlgEquiv (K := K) (L := L.toField) := by
    apply (abelianizationOfEquiv Gal(L.toField/K)).injective
    rw [abelianizationOfEquiv_apply, abelianizationOfEquiv_apply, abelianizationOf_tauCetiArtin L (sepEmb L),
      localArtinMap_uniformizer K L.toField (sepEmb L) hπU]
    rfl
  rw [hφ]
  set f := TauCeti.integerRingEquivIntegralClosure K L.toField
  set σ := frobeniusAlgEquiv (K := K) (L := L.toField)
  intro x hx
  set x' : 𝒪[L.toField] := f.symm ⟨x, hx⟩ with hx'
  have hxx : (x' : L.toField) = x := by rw [hx', TauCeti.coe_integerRingEquivIntegralClosure_symm_apply]
  have hv := TauCeti.valuation_frobeniusAlgEquiv_sub_pow (K := K) (L := L.toField) x'
  have hm : σ • x' - x' ^ Nat.card 𝓀[K] ∈ 𝓂[L.toField] := by
    exact (Valuation.mem_maximalIdeal_iff (v := ValuativeRel.valuation L.toField)).2 (by simpa [σ] using hv)
  have hmem : σ • x' - x' ^ Nat.card 𝓀[K] ∈ 𝓂[K].map (algebraMap 𝒪[K] 𝒪[L.toField]) := by
    rw [(TauCeti.isUnramified_iff_map_maximalIdeal_eq K L.toField).1 hU]
    exact hm
  refine ⟨f (σ • x' - x' ^ Nat.card 𝓀[K]), ?_, ?_⟩
  · have he : ((f : 𝒪[L.toField] →+* integers L.toField)).comp (algebraMap 𝒪[K] 𝒪[L.toField]) =
        algebraMap 𝒪[K] (integers L.toField) := RingHom.ext fun y => f.commutes y
    rw [← he, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hmem
  · rw [TauCeti.coe_integerRingEquivIntegralClosure_apply]
    simp [hxx, σ]

variable (K Ω) in
/-- **Theorem 1.1 (local reciprocity law), existence, proved** (Milne, *CFT*, I, Theorem 1.1, p. 20; proved in
Chapter III, Theorem 3.4): the named statement `LocalReciprocityExistence` holds for every nonarchimedean local field
$K$ in `Type`, with the family `tauCetiArtin` built from Tau Ceti's `localArtinMap` (ported). -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1 (existence)"]
theorem localReciprocityExistence : LocalReciprocityExistence K Ω :=
  ⟨⟨tauCetiArtin, ⟨galRestrict_tauCetiArtin, fun hπ L hL => isFrobenius_tauCetiArtin hπ L hL,
    ker_tauCetiArtin, surjective_tauCetiArtin⟩⟩⟩

end NumberFieldKB.MilneCFT.LocalCFT
