import NumberFieldKB.MilneCFT.LocalCFT.UniverseTransport
import NumberFieldKB.MilneCFT.LocalCFT.ReciprocityTauCeti

/-!
# Transport of the local Artin map along an isomorphism of separable closures

Milne, *CFT*, I, Theorem 1.1. A $K$-isomorphism $e : \Omega \simeq \Omega'$ of separable closures carries the finite
abelian extensions of $\Omega$ to those of $\Omega'$ (`FiniteAbelianExt.mapEquiv`), with the same norm groups
(`normGroup_map`). Conjugating by the induced isomorphisms $L \simeq e(L)$ turns a family satisfying the conditions of
Theorem 1.1 for $\Omega'$ into one for $\Omega$ (`pullbackArtin`, `isLocalArtinMap_pullback`). Since Tau Ceti's local
reciprocity is stated for `Type`, this gives existence for a separable closure in any universe
(`localReciprocityExistence_univ`), and identifies every local Artin map with the pullback of the Tau Ceti one
(`eq_pullback_tauCetiArtin`).
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

section Transport

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω Ω' : Type*} [Field Ω] [Algebra K Ω] [Field Ω'] [Algebra K Ω']

/-- A $K$-isomorphism of finite extensions induces an $\mathcal O_K$-isomorphism of their rings of integers. -/
def integersEquiv {L : IntermediateField K Ω} {L' : IntermediateField K Ω'} (g : L ≃ₐ[K] L') :
    integers L ≃ₐ[𝒪[K]] integers L' :=
  (AlgEquiv.subalgebraMap (g.restrictScalars 𝒪[K]) (integralClosure 𝒪[K] L)).trans
    (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv (g.restrictScalars 𝒪[K])))

@[simp] theorem coe_integersEquiv {L : IntermediateField K Ω} {L' : IntermediateField K Ω'}
    (g : L ≃ₐ[K] L') (x : integers L) : ((integersEquiv g x : integers L') : L') = g (x : L) := rfl

theorem integersEquiv_comp {L : IntermediateField K Ω} {L' : IntermediateField K Ω'} (g : L ≃ₐ[K] L') :
    ((integersEquiv g).toAlgHom : integers L →+* integers L').comp
      (algebraMap 𝒪[K] (integers L)) = algebraMap 𝒪[K] (integers L') :=
  RingHom.ext fun y => (integersEquiv g).commutes y

/-- Unramifiedness is invariant under $K$-isomorphism. -/
theorem isUnramifiedExt_of_equiv {L : IntermediateField K Ω} {L' : IntermediateField K Ω'}
    (g : L ≃ₐ[K] L') (h : IsUnramifiedExt L) : IsUnramifiedExt L' := by
  unfold IsUnramifiedExt at *
  have := h.map_bijective ((integersEquiv g).toAlgHom : integers L →+* integers L')
    (integersEquiv g).bijective
  rw [Ideal.map_map, integersEquiv_comp] at this
  exact this

/-- The Frobenius condition is invariant under $K$-isomorphism (conjugating $\sigma$). -/
theorem isFrobenius_of_equiv {L : IntermediateField K Ω} {L' : IntermediateField K Ω'}
    (g : L ≃ₐ[K] L') {σ : Gal(L/K)} (h : IsFrobenius L σ) : IsFrobenius L' (g.autCongr σ) := by
  intro x hx
  have hx0 : g.symm x ∈ integers L := by
    exact IsIntegral.map (g.symm.restrictScalars 𝒪[K] : L' →ₐ[𝒪[K]] L) hx
  obtain ⟨y, hy, hyx⟩ := h (g.symm x) hx0
  refine ⟨integersEquiv g y, ?_, ?_⟩
  · have := Ideal.mem_map_of_mem ((integersEquiv g).toAlgHom : integers L →+* integers L') hy
    rw [Ideal.map_map, integersEquiv_comp] at this
    exact this
  · rw [coe_integersEquiv, hyx]
    simp

end Transport

section Pullback

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω Ω' : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [Field Ω'] [Algebra K Ω']
  [IsSepClosure K Ω']

/-- The $K$-isomorphism $L \simeq e(L)$ induced by $e : \Omega \simeq \Omega'$. -/
def FiniteAbelianExt.equivMapEquiv (e : Ω ≃ₐ[K] Ω') (L : FiniteAbelianExt K Ω) :
    L.toField ≃ₐ[K] (L.mapEquiv e).toField :=
  IntermediateField.equivMap L.toField (e : Ω →ₐ[K] Ω')

@[simp] theorem coe_equivMapEquiv_apply (e : Ω ≃ₐ[K] Ω') (L : FiniteAbelianExt K Ω) (x : L.toField) :
    (((FiniteAbelianExt.equivMapEquiv e L) x : (L.mapEquiv e).toField) : Ω') = e x := rfl

theorem coe_equivMapEquiv_symm_apply (e : Ω ≃ₐ[K] Ω') (L : FiniteAbelianExt K Ω)
    (y : (L.mapEquiv e).toField) :
    (((FiniteAbelianExt.equivMapEquiv e L).symm y : L.toField) : Ω) = e.symm (y : Ω') := by
  apply e.injective
  rw [e.apply_symm_apply]
  exact congrArg (fun z : (L.mapEquiv e).toField => (z : Ω')) ((FiniteAbelianExt.equivMapEquiv e L).apply_symm_apply y)

variable (e : Ω ≃ₐ[K] Ω')

/-- **Pullback of a family of local Artin maps** along a $K$-isomorphism $e : \Omega \simeq \Omega'$ of separable
closures (Milne, *CFT*, I, Theorem 1.1): $\phi_L(a)$ is the conjugate of $\phi'_{e(L)}(a)$ by $L \simeq e(L)$. -/
def pullbackArtin (φ' : ∀ L' : FiniteAbelianExt K Ω', Kˣ →* Gal(L'.toField/K)) :
    ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K) :=
  fun L => ((FiniteAbelianExt.equivMapEquiv e L).symm.autCongr : _ ≃* _).toMonoidHom.comp (φ' (L.mapEquiv e))

variable (φ' : ∀ L' : FiniteAbelianExt K Ω', Kˣ →* Gal(L'.toField/K))

theorem coe_pullbackArtin_apply (L : FiniteAbelianExt K Ω) (a : Kˣ) (x : L.toField) :
    ((pullbackArtin e φ' L a x : L.toField) : Ω) =
      e.symm ((φ' (L.mapEquiv e) a ⟨e x, ⟨x, x.2, rfl⟩⟩ : (L.mapEquiv e).toField) : Ω') := by
  change (((FiniteAbelianExt.equivMapEquiv e L).symm (φ' (L.mapEquiv e) a
    (FiniteAbelianExt.equivMapEquiv e L x)) : L.toField) : Ω) = _
  rw [coe_equivMapEquiv_symm_apply]
  rfl

/-- **Theorem 1.1, transport** (Milne, *CFT*, I, Theorem 1.1): the pullback of a family satisfying the conditions of
Theorem 1.1 for $\Omega'$ satisfies them for $\Omega$. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1 (conditions (a), (b); transport along an isomorphism of separable closures)"]
theorem isLocalArtinMap_pullback (hφ' : IsLocalArtinMap φ') : IsLocalArtinMap (pullbackArtin e φ') where
  compat L L2 h a := by
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    have h' : (L.mapEquiv e).toField ≤ (L2.mapEquiv e).toField := IntermediateField.map_mono _ h
    rw [galRestrict_apply, coe_pullbackArtin_apply, coe_pullbackArtin_apply]
    have := congrArg (fun σ : Gal((L.mapEquiv e).toField/K) => ((σ ⟨e x, ⟨x, x.2, rfl⟩⟩ : (L.mapEquiv e).toField) : Ω'))
      (hφ'.compat (L.mapEquiv e) (L2.mapEquiv e) h' a)
    simp only [galRestrict_apply] at this
    rw [← this]
    rfl
  frobenius {π} hπ L hL := by
    have := hφ'.frobenius hπ (L.mapEquiv e)
      (isUnramifiedExt_of_equiv (FiniteAbelianExt.equivMapEquiv e L) hL)
    exact isFrobenius_of_equiv (FiniteAbelianExt.equivMapEquiv e L).symm this
  ker_eq L := by
    have h1 : (pullbackArtin e φ' L).ker = (φ' (L.mapEquiv e)).ker := by
      ext a
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact map_eq_one_iff ((FiniteAbelianExt.equivMapEquiv e L).symm.autCongr : _ ≃* _) (MulEquiv.injective _)
    rw [h1, hφ'.ker_eq]
    have : FiniteDimensional K (L.toField.map (e : Ω →ₐ[K] Ω')) := (L.mapEquiv e).finiteDimensional
    exact normGroup_map e L.toField
  surjective L := by
    show Function.Surjective (((FiniteAbelianExt.equivMapEquiv e L).symm.autCongr : _ ≃* _) ∘ φ' (L.mapEquiv e))
    exact (MulEquiv.surjective _).comp (hφ'.surjective _)

end Pullback

section Existence

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

variable (K) in
/-- **Theorem 1.1 (local reciprocity law), existence, any universe** (Milne, *CFT*, I, Theorem 1.1): the named
statement `LocalReciprocityExistence` holds for a separable closure $\Omega$ of $K$ in any universe, by pulling back the
Tau Ceti family `tauCetiArtin` for `SeparableClosure K` along `IsSepClosure.equiv`. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1 (existence)"]
theorem localReciprocityExistence_univ : LocalReciprocityExistence K Ω :=
  ⟨⟨pullbackArtin (IsSepClosure.equiv K Ω (SeparableClosure K)) tauCetiArtin,
    isLocalArtinMap_pullback _ _ ⟨galRestrict_tauCetiArtin, fun hπ L hL => isFrobenius_tauCetiArtin hπ L hL,
      ker_tauCetiArtin, surjective_tauCetiArtin⟩⟩⟩

/-- **Theorem 1.1 with uniqueness** (Milne, *CFT*, I, Theorem 1.1, 1.13): every local Artin map for a separable closure
$\Omega$ in any universe is the pullback of the Tau Ceti one. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1 (uniqueness) and Theorem 1.13"]
theorem eq_pullback_tauCetiArtin {φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}
    (hφ : IsLocalArtinMap φ) :
    φ = pullbackArtin (IsSepClosure.equiv K Ω (SeparableClosure K)) tauCetiArtin :=
  isLocalArtinMap_unique_univ hφ
    (isLocalArtinMap_pullback _ _ ⟨galRestrict_tauCetiArtin, fun hπ L hL => isFrobenius_tauCetiArtin hπ L hL,
      ker_tauCetiArtin, surjective_tauCetiArtin⟩)

end Existence

end NumberFieldKB.MilneCFT.LocalCFT

