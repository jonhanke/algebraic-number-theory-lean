import NumberFieldKB.MilneCFT.Ch5Complements
import NumberFieldKB.YamaguchiPort.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldExists
import NumberFieldKB.YamaguchiPort.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldDegree
import NumberFieldKB.YamaguchiPort.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldPrincipalization

/-!
# The principal ideal theorem, from Yamaguchi's small Hilbert class field (Milne, *CFT*, V, Theorem 3.17)

`NumberFieldKB.MilneCFT.principalIdealTheorem` proves `PrincipalIdealTheorem K` for every number field `K`.
The proof compares an arbitrary Hilbert class field `H` (`HilbertClassField.IsHilbertClassField K H`) with the
small Hilbert class field `E` of the ported Yamaguchi library (`ClassFieldTheory.exists_smallHilbertClassField`):
`H` embeds in the separable closure as an everywhere unramified finite abelian extension, hence embeds in `E`
by maximality; both have degree the class number, so `H ≃ₐ[K] E`, and principality of extended ideals
(`ClassFieldTheory.ideals_becomePrincipalInSmallHilbertClassField`) is transported along this isomorphism.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped nonZeroDivisors IsMulCommutative

noncomputable section

set_option linter.style.haveILetI false

namespace NumberFieldKB.MilneCFT

/-- Unramifiedness of a prime of `𝓞 K` transports along a `K`-isomorphism of number fields. -/
theorem isUnramifiedIn_of_algEquiv {K L M : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M) (p : Ideal (𝓞 K))
    (h : Algebra.IsUnramifiedIn (𝓞 L) p) : Algebra.IsUnramifiedIn (𝓞 M) p := by
  let E : 𝓞 L ≃ₐ[𝓞 K] 𝓞 M := RingOfIntegers.mapAlgEquiv e
  intro Q hQ hlies
  have hQ' : (Q.comap E).IsPrime := Ideal.comap_isPrime E.toRingEquiv.toRingHom Q
  have hl : (Q.comap E).LiesOver p := by
    constructor
    have := hlies.over
    rw [this]
    ext x
    simp only [Ideal.mem_comap]
    rw [← E.commutes x]
  have h1 := h (Q.comap E) hQ' hl
  exact Algebra.FormallyUnramified.of_equiv
    (Localization.localAlgEquiv (Q.comap E) Q E rfl)

/-- Being unramified at the infinite places transports along a `K`-isomorphism of number fields. -/
theorem isUnramifiedAtInfinitePlaces_of_algEquiv {K L M : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M)
    (h : IsUnramifiedAtInfinitePlaces K L) : IsUnramifiedAtInfinitePlaces K M := by
  letI : Algebra M L := e.symm.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower K M L := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap K L x = e.symm (algebraMap K M x)
    simp
  haveI : Algebra.IsAlgebraic M L := Algebra.IsAlgebraic.of_finite M L
  exact IsUnramifiedAtInfinitePlaces.bot K M L

/-- Principality of extended ideals transports along a `K`-isomorphism of number fields. -/
theorem map_isPrincipal_of_algEquiv {K L M : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M) (I : Ideal (𝓞 K))
    (h : (I.map (algebraMap (𝓞 K) (𝓞 M))).IsPrincipal) :
    (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
  let E : 𝓞 L ≃ₐ[𝓞 K] 𝓞 M := RingOfIntegers.mapAlgEquiv e
  obtain ⟨g, hg⟩ := h
  refine ⟨⟨E.symm g, ?_⟩⟩
  have : I.map (algebraMap (𝓞 K) (𝓞 L)) =
      (I.map (algebraMap (𝓞 K) (𝓞 M))).map (E.symm.toRingEquiv : 𝓞 M →+* 𝓞 L) := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun x => (E.symm.commutes x).symm
  rw [this, hg]
  show _ = Ideal.span _
  rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]
  rfl

/-- **Principal ideal theorem** (Milne, *CFT*, V, Theorem 3.17): every ideal of $\mathcal O_K$ becomes principal in
the Hilbert class field. Proved from the small Hilbert class field of the ported Yamaguchi library
(`ClassFieldTheory.exists_smallHilbertClassField`, `ClassFieldTheory.ideals_becomePrincipalInSmallHilbertClassField`):
any Hilbert class field `H` is `K`-isomorphic to it. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.17"]
theorem principalIdealTheorem (K : Type) [Field K] [NumberField K] : PrincipalIdealTheorem K := by
  refine ⟨fun H _ _ _ _ hH I => ?_⟩
  obtain ⟨E, hE⟩ := ClassFieldTheory.exists_smallHilbertClassField K
  obtain ⟨ψc, -⟩ := hH.exists_artin
  have hcomm : ∀ a b : Gal(H/K), a * b = b * a := fun a b => by
    obtain ⟨x, rfl⟩ := ψc.surjective a
    obtain ⟨y, rfl⟩ := ψc.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  have hdeg : Module.finrank K H = NumberField.classNumber K := by
    rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr ψc.toEquiv.symm]
    rw [Nat.card_eq_fintype_card]
    rfl
  -- embed `H` into the separable closure
  haveI : Algebra.IsSeparable K H := inferInstance
  let φ : H →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let F : IntermediateField K (SeparableClosure K) := φ.fieldRange
  let ψ : H ≃ₐ[K] F := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional K F := LinearEquiv.finiteDimensional ψ.toLinearEquiv
  haveI : IsGalois K F := IsGalois.of_algEquiv ψ
  haveI : IsMulCommutative Gal(F/K) := .of_comm fun a b => by
    apply (AlgEquiv.autCongr ψ).symm.injective
    rw [map_mul, map_mul]
    exact hcomm _ _
  haveI : IsAbelianGalois K F := {}
  let Fx : ClassFieldTheory.FiniteAbelianExtension K := ⟨F, inferInstance, inferInstance⟩
  have : NumberField Fx.1 := NumberField.of_module_finite K Fx.1
  have hF : ClassFieldTheory.IsEverywhereUnramified K Fx.1 :=
    ⟨fun v => isUnramifiedIn_of_algEquiv ψ v.asIdeal (hH.isUnramifiedIn v),
      isUnramifiedAtInfinitePlaces_of_algEquiv ψ hH.isUnramifiedAtInfinitePlaces⟩
  obtain ⟨g⟩ := hE.2 Fx hF
  let f : H →ₐ[K] E := g.comp ψ.toAlgHom
  have hinj : Function.Injective f := f.toRingHom.injective
  have hfr : Module.finrank K H = Module.finrank K E :=
    hdeg.trans (ClassFieldTheory.smallHilbertClassField_degree_eq_classNumber K E hE).symm
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) hfr).mp hinj
  let e : H ≃ₐ[K] E := AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  exact map_isPrincipal_of_algEquiv e I
    (ClassFieldTheory.ideals_becomePrincipalInSmallHilbertClassField K E hE I)

end NumberFieldKB.MilneCFT
