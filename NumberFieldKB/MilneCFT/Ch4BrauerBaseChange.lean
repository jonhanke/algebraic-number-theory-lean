import NumberFieldKB.TauCetiPort.Algebra.CrossedProduct.BaseChange.Algebra
import NumberFieldKB.TauCetiPort.Algebra.CrossedProduct.Comparison
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.CentralSimple.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.BaseChange

/-!
# Base change of crossed products along a linearly disjoint extension

Core algebraic lemma: let `E/Z` be finite Galois, `L/Z` any extension and `F/L` finite Galois, with a ring
embedding `ι : E → F` compatible with `Z → L` and an isomorphism `ρ : Gal(F/L) ≃ Gal(E/Z)` intertwined by `ι`.
Then for every cocycle `d` of `Gal(E/Z)`, `L ⊗_Z (E/Z, d) ≅ (F/L, d ∘ ρ)` as `L`-algebras.
-/

open scoped TensorProduct

noncomputable section

universe u

namespace NumberFieldKB.MilneCFT.BrauerBaseChange

open TauCeti

section Core

variable {Z L E F : Type u} [Field Z] [Field L] [Field E] [Field F]
  [Algebra Z L] [Algebra Z E] [Algebra L F]
  [FiniteDimensional Z E] [IsGalois Z E] [FiniteDimensional L F] [IsGalois L F]
  (ι : E →+* F) (hι : ∀ z : Z, ι (algebraMap Z E z) = algebraMap L F (algebraMap Z L z))
  (ρ : (F ≃ₐ[L] F) ≃* (E ≃ₐ[Z] E)) (hρ : ∀ g x, ι (ρ g x) = g (ι x))
  (d : TwoCocycle Z E)

/-- The cocycle `d` read on `Gal(F/L)` through `ρ` and `ι`. -/
abbrev comapCocycle : TwoCocycle L F :=
  d.comap ρ.toMonoidHom ι hρ

/-- `Z`-algebra structure on the crossed product over `L`, through `Z → L`. -/
@[reducible] def algebraZ : Algebra Z (CrossedProduct (comapCocycle ι ρ hρ d)) :=
  Algebra.compHom _ (algebraMap Z L)

attribute [local instance] algebraZ

instance : IsScalarTower Z L (CrossedProduct (comapCocycle ι ρ hρ d)) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The coefficient map `E → (F/L, d')`, `x ↦ ι x`, as a `Z`-algebra map. -/
def coeffHom : E →ₐ[Z] CrossedProduct (comapCocycle ι ρ hρ d) where
  toRingHom := (CrossedProduct.inc (comapCocycle ι ρ hρ d)).toRingHom.comp ι
  commutes' z := by
    change CrossedProduct.inc _ (ι (algebraMap Z E z)) = algebraMap L _ (algebraMap Z L z)
    rw [hι, AlgHom.commutes]

theorem coeffHom_apply (x : E) :
    coeffHom ι hι ρ hρ d x = CrossedProduct.inc (comapCocycle ι ρ hρ d) (ι x) := rfl

/-- The `Z`-algebra map `(E/Z, d) → (F/L, d')`, `x · u_σ ↦ ι(x) · u_{ρ⁻¹ σ}`. -/
def crossedHom : CrossedProduct d →ₐ[Z] CrossedProduct (comapCocycle ι ρ hρ d) :=
  CrossedProduct.lift (coeffHom ι hι ρ hρ d)
    (fun σ ↦ CrossedProduct.basis (comapCocycle ι ρ hρ d) (ρ.symm σ))
    (fun σ x ↦ by
      rw [coeffHom_apply, coeffHom_apply, CrossedProduct.basis_mul_inc, ← hρ, MulEquiv.apply_symm_apply])
    (fun σ τ ↦ by
      rw [CrossedProduct.basis_mul_basis, coeffHom_apply, map_mul ρ.symm σ τ]
      congr 2
      simp [comapCocycle, TwoCocycle.comap_toFun])
    (by
      rw [map_one ρ.symm, CrossedProduct.basis_one, coeffHom_apply]
      congr 1
      simp [comapCocycle, TwoCocycle.comap_toFun])

/-- The `L`-algebra map `L ⊗_Z (E/Z, d) → (F/L, d')`. -/
def tensorHom : L ⊗[Z] CrossedProduct d →ₐ[L] CrossedProduct (comapCocycle ι ρ hρ d) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (crossedHom ι hι ρ hρ d)
    fun l _ ↦ Algebra.commutes l _

theorem tensorHom_bijective : Function.Bijective (tensorHom ι hι ρ hρ d) := by
  have hinj : Function.Injective (tensorHom ι hι ρ hρ d) :=
    RingHom.injective (tensorHom ι hι ρ hρ d).toRingHom
  refine ⟨hinj, ?_⟩
  have hcard : Module.finrank Z E = Module.finrank L F := by
    rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr ρ.toEquiv).symm
  have hdim : Module.finrank L (L ⊗[Z] CrossedProduct d) =
      Module.finrank L (CrossedProduct (comapCocycle ι ρ hρ d)) := by
    rw [Module.finrank_baseChange, CrossedProduct.finrank_eq_finrank_sq,
      CrossedProduct.finrank_eq_finrank_sq, hcard]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (tensorHom ι hι ρ hρ d).toLinearMap)).1 hinj

/-- **Base change of a crossed product along a linearly disjoint extension.** -/
def tensorEquiv : L ⊗[Z] CrossedProduct d ≃ₐ[L] CrossedProduct (comapCocycle ι ρ hρ d) :=
  AlgEquiv.ofBijective _ (tensorHom_bijective ι hι ρ hρ d)

include hι in
theorem baseChange_crossedProductClass_of_equiv :
    BrauerGroup.baseChange Z L (BrauerGroup.crossedProductClass d) =
      BrauerGroup.crossedProductClass (comapCocycle ι ρ hρ d) := by
  rw [BrauerGroup.crossedProductClass_def, BrauerGroup.crossedProductClass_def,
    BrauerGroup.baseChange_mk]
  exact BrauerGroup.mk_eq_mk_of_algEquiv (tensorEquiv ι hι ρ hρ d)

end Core

/-! ### The cohomological side -/

section Cohomology

open ClassFieldTheory ContCohomology

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
  (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
  (F : IntermediateField L (SeparableClosure L)) [FiniteDimensional L F] [IsGalois L F]
  (ι : E →+* F) (hιτ : ∀ x : E, ((ι x : F) : SeparableClosure L) = τ x)
  (π : (F ≃ₐ[L] F) →* (E ≃ₐ[K] E)) (hπ : ∀ g x, ι (π g x) = g (ι x))

include hιτ hπ in
/-- Restricting the image in `G_K` of `g ∈ G_L` to `E` is `π` of the restriction of `g` to `F`. -/
theorem restrictNormalHom_absoluteGaloisGroupMap (g : AbsoluteGaloisGroup L) :
    AlgEquiv.restrictNormalHom E (absoluteGaloisGroupMap τ g) =
      π (AlgEquiv.restrictNormalHom F g) := by
  refine AlgEquiv.ext fun x ↦ ι.injective (Subtype.ext ?_)
  rw [hπ, hιτ]
  have h1 : ((AlgEquiv.restrictNormalHom E (absoluteGaloisGroupMap τ g) x : E) :
      SeparableClosure K) = absoluteGaloisGroupMap τ g x :=
    AlgEquiv.restrictNormal_commutes _ E x
  have h2 : ((AlgEquiv.restrictNormalHom F g (ι x) : F) : SeparableClosure L) = g (ι x) :=
    AlgEquiv.restrictNormal_commutes _ F (ι x)
  rw [h1, absoluteGaloisGroupMap_commutes, h2, hιτ]

include hιτ in
/-- **Base change of an inflated class.** Pulling the inflation of a cocycle `c` of `Gal(E/K)` back along
`τ` gives the inflation of `c` read on `Gal(F/L)` through `π` and `ι`. -/
theorem explicitMap2_inflateH2 (c : TwoCocycle K E) :
    explicitMap2 (AbsoluteGaloisGroup K) (UnitsCoeff K) (AbsoluteGaloisGroup L) (UnitsCoeff L)
        (absoluteGaloisGroupMap τ) (unitsCoeffBaseChange τ) continuous_of_discreteTopology
        (unitsCoeffBaseChange_smul τ) (c.inflateH2 E) =
      (c.comap π ι hπ).inflateH2 F := by
  rw [TwoCocycle.inflateH2_def, TwoCocycle.inflateH2_def]
  refine (explicitMap2_mk _ _ _ _ _ _ _ _ _).trans (congrArg (H2pi _ _) ?_)
  refine Subtype.ext (funext fun p ↦ ?_)
  obtain ⟨g, h⟩ := p
  refine (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ g h).trans ?_
  refine Additive.toMul.injective (Units.ext ?_)
  simp only [TwoCocycle.coe_inflateZ2, toMul_unitsCoeffBaseChange, toMul_ofMul,
    TwoCocycle.inflate_toFun, TwoCocycle.comap_toFun, Units.coe_map]
  rw [restrictNormalHom_absoluteGaloisGroupMap τ E F ι hιτ π hπ,
    restrictNormalHom_absoluteGaloisGroupMap τ E F ι hιτ π hπ]
  simp only [MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, IntermediateField.coe_val]
  exact (hιτ _).symm

end Cohomology

/-! ### The compositum and the descent field -/

section Construction

open ClassFieldTheory ContCohomology Polynomial

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
  (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]

/-- **The compositum of `L` and `τ(E)`**: a finite Galois subextension `F` of `Lˢ/L` into which `τ` maps
`E`, generated over `L` by the image of `E` (an `L`-automorphism of `F` fixing it is trivial). -/
theorem exists_compositum :
    ∃ (F : IntermediateField L (SeparableClosure L)) (_ : FiniteDimensional L F) (_ : IsGalois L F)
      (ι : E →+* F) (_ : ∀ x : E, ((ι x : F) : SeparableClosure L) = τ x),
      ∀ g : F ≃ₐ[L] F, (∀ x : E, g (ι x) = ι x) → g = 1 := by
  obtain ⟨p, hpsep, hpsplit⟩ := IsGalois.is_separable_splitting_field K E
  set q := p.map (algebraMap K L) with hq
  have hq0 : q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).2 hpsep.ne_zero
  have hqs : (q.map (algebraMap L (SeparableClosure L))).Splits :=
    IsSepClosed.splits_codomain q hpsep.map
  set F := IntermediateField.adjoin L (q.rootSet (SeparableClosure L)) with hF
  haveI : q.IsSplittingField L F := IntermediateField.adjoin_rootSet_isSplittingField hqs
  haveI : FiniteDimensional L F := Polynomial.IsSplittingField.finiteDimensional F q
  haveI : IsGalois L F := IsGalois.of_separable_splitting_field (p := q) hpsep.map
  have hroot : ∀ y : SeparableClosure L, aeval y p = 0 → y ∈ q.rootSet (SeparableClosure L) :=
    fun y hy ↦ (mem_rootSet_of_ne hq0).2 (by rwa [hq, aeval_map_algebraMap])
  have hmem : ∀ x : E, τ x ∈ F := by
    have htop : Algebra.adjoin K (p.rootSet E) ≤
        ((F.restrictScalars K).toSubalgebra.comap (τ.comp E.val)) := by
      refine Algebra.adjoin_le fun r hr ↦ ?_
      have hr' := (mem_rootSet_of_ne hpsep.ne_zero).1 hr
      show τ (E.val r) ∈ F
      refine IntermediateField.subset_adjoin L _ (hroot _ ?_)
      rw [aeval_algHom_apply, aeval_algHom_apply, hr', map_zero, map_zero]
    rw [Polynomial.IsSplittingField.adjoin_rootSet] at htop
    exact fun x ↦ htop Algebra.mem_top
  let ι : E →+* F := (τ.comp E.val).toRingHom.codRestrict F hmem
  have hgen : ∀ y ∈ q.rootSet (SeparableClosure L), ∃ x : E, τ x = y := by
    intro y hy
    have hy' := (mem_rootSet_of_ne hq0).1 hy
    rw [hq, aeval_map_algebraMap] at hy'
    have hsplitE : (p.map (algebraMap K E)).Splits := Polynomial.IsSplittingField.splits E p
    obtain ⟨x, hx⟩ := hsplitE.mem_range_of_isRoot ((Polynomial.map_ne_zero_iff
      (algebraMap K E).injective).2 hpsep.ne_zero) (i := (τ.comp E.val).toRingHom) (x := y) (by
        rw [IsRoot.def, Polynomial.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
          eval_map_algebraMap]
        exact hy')
    exact ⟨x, hx⟩
  refine ⟨F, inferInstance, inferInstance, ι, fun x ↦ rfl, fun g hg ↦ ?_⟩
  have hext : (F.val.comp g.toAlgHom : F →ₐ[L] SeparableClosure L) = F.val := by
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    obtain ⟨x, rfl⟩ := hgen y hy
    have h1 : (⟨τ x, IntermediateField.subset_adjoin L _ hy⟩ : F) = ι x := rfl
    rw [AlgHom.comp_apply, h1, AlgEquiv.coe_toAlgHom, hg x]
  exact AlgEquiv.ext fun y ↦ Subtype.ext (by simpa using congrArg (· y) hext)

variable (F : IntermediateField L (SeparableClosure L)) [FiniteDimensional L F] [IsGalois L F]
  (ι : E →+* F) (hιτ : ∀ x : E, ((ι x : F) : SeparableClosure L) = τ x)

include hιτ in
theorem exists_aut (g : F ≃ₐ[L] F) : ∃ σ : E ≃ₐ[K] E, ∀ x, ι (σ x) = g (ι x) := by
  obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := L) (K₁ := F) (SeparableClosure L) g
  refine ⟨AlgEquiv.restrictNormalHom E (absoluteGaloisGroupMap τ g'), fun x ↦ Subtype.ext ?_⟩
  have h1 : ((AlgEquiv.restrictNormalHom E (absoluteGaloisGroupMap τ g') x : E) :
      SeparableClosure K) = absoluteGaloisGroupMap τ g' x :=
    AlgEquiv.restrictNormal_commutes _ E x
  have h2 : ((AlgEquiv.restrictNormalHom F g' (ι x) : F) : SeparableClosure L) = g' (ι x) :=
    AlgEquiv.restrictNormal_commutes _ F (ι x)
  rw [hιτ, h1, absoluteGaloisGroupMap_commutes, h2, hιτ]

omit [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L F] [IsGalois L F] in
theorem aut_unique {σ σ' : E ≃ₐ[K] E} (h : ∀ x, ι (σ x) = ι (σ' x)) : σ = σ' :=
  AlgEquiv.ext fun x ↦ ι.injective (h x)

include hιτ in
/-- **Restriction `Gal(F/L) → Gal(E/K)`** along `ι`. -/
theorem exists_restriction :
    ∃ π : (F ≃ₐ[L] F) →* (E ≃ₐ[K] E), ∀ g x, ι (π g x) = g (ι x) := by
  choose σ hσ using exists_aut τ E F ι hιτ
  refine ⟨{ toFun := σ, map_one' := ?_, map_mul' := ?_ }, hσ⟩
  · exact aut_unique E F ι fun x ↦ by rw [hσ]; rfl
  · intro g h
    exact aut_unique E F ι fun x ↦ by rw [hσ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hσ, hσ]

variable (π : (F ≃ₐ[L] F) →* (E ≃ₐ[K] E)) (hπ : ∀ g x, ι (π g x) = g (ι x))

omit [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L F] [IsGalois L F] in
include hπ in
theorem restriction_injective (hgen : ∀ g : F ≃ₐ[L] F, (∀ x : E, g (ι x) = ι x) → g = 1) :
    Function.Injective π :=
  (injective_iff_map_eq_one π).2 fun g hg ↦ hgen g fun x ↦ by rw [← hπ, hg]; rfl

include hιτ hπ in
/-- **Scalar extension of a crossed product along an arbitrary extension.** For `F ⊆ Lˢ` finite Galois
over `L`, receiving `E` through `ι` (compatible with `τ`) and generated by its image, the scalar
extension to `L` of the crossed product of `c` is the crossed product of `c` read on `Gal(F/L)`. -/
theorem baseChange_crossedProductClass_comap
    (hinj : Function.Injective π) (c : TwoCocycle K E) :
    BrauerGroup.baseChange K L (BrauerGroup.crossedProductClass c) =
      BrauerGroup.crossedProductClass (c.comap π ι hπ) := by
  set Z : IntermediateField K E := IntermediateField.fixedField π.range with hZ
  have hbot : ∀ z : Z, ι (z : E) ∈ (⊥ : IntermediateField L F) := fun z ↦
    (IsGalois.mem_bot_iff_fixed _).2 fun f ↦ by
      rw [← hπ]
      congr 1
      exact (IntermediateField.mem_fixedField_iff _ _).1 z.2 (π f) ⟨f, rfl⟩
  let j : Z →+* L := (IntermediateField.botEquiv L F).toRingHom.comp
    ((ι.comp (IntermediateField.val Z).toRingHom).codRestrict (⊥ : IntermediateField L F) hbot)
  have hj : ∀ z : Z, algebraMap L F (j z) = ι (z : E) := fun z ↦ by
    have h := congrArg Subtype.val ((IntermediateField.botEquiv L F).symm_apply_apply
      ⟨ι (z : E), hbot z⟩)
    rw [IntermediateField.botEquiv_symm] at h
    exact h
  letI : Algebra Z L := j.toAlgebra
  have hτK : ∀ k : K, ι (algebraMap K E k) = algebraMap L F (algebraMap K L k) := fun k ↦ by
    apply Subtype.ext
    rw [hιτ]
    change τ (algebraMap K (SeparableClosure K) k) =
      algebraMap L (SeparableClosure L) (algebraMap K L k)
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower K Z L := IsScalarTower.of_algebraMap_eq fun k ↦ by
    apply (algebraMap L F).injective
    rw [← hτK]
    exact (hj (algebraMap K Z k)).symm
  have hιZ : ∀ z : Z, ι (algebraMap Z E z) = algebraMap L F (algebraMap Z L z) := fun z ↦ (hj z).symm
  let ρ : (F ≃ₐ[L] F) ≃* (E ≃ₐ[Z] E) := (MonoidHom.ofInjective hinj).trans
    ((MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField π.range).symm).trans
      (IntermediateField.fixingSubgroupEquiv Z))
  have hρπ : ∀ g x, ρ g x = π g x := fun _ _ ↦ rfl
  have hρ : ∀ g x, ι (ρ g x) = g (ι x) := fun g x ↦ by rw [hρπ, hπ]
  have hcoc : (c.restrict Z).comap ρ.toMonoidHom ι hρ = c.comap π ι hπ := by
    refine TwoCocycle.ext (funext₂ fun g h ↦ ?_)
    rfl
  calc BrauerGroup.baseChange K L (BrauerGroup.crossedProductClass c)
      = BrauerGroup.baseChange Z L (BrauerGroup.baseChange K Z (BrauerGroup.crossedProductClass c)) :=
        (DFunLike.congr_fun (BrauerGroup.baseChange_comp K Z L) _).symm
    _ = BrauerGroup.baseChange Z L (BrauerGroup.crossedProductClass (c.restrict Z)) := by
        rw [BrauerGroup.baseChange_crossedProductClass]
    _ = BrauerGroup.crossedProductClass ((c.restrict Z).comap ρ.toMonoidHom ι hρ) :=
        baseChange_crossedProductClass_of_equiv ι hιZ ρ hρ (c.restrict Z)
    _ = BrauerGroup.crossedProductClass (c.comap π ι hπ) := by rw [hcoc]

end Construction

/-! ### The comparison commutes with base change -/

section Main

open ClassFieldTheory ContCohomology

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- **The crossed-product identification commutes with base change**, along every field extension
`L/K` (finite or not, algebraic or not): Tau Ceti's `brauerGroupEquivBr` carries scalar extension
`[A] ↦ [L ⊗_K A]` of central simple algebras to Tau Ceti's cohomological base change `brBaseChange`.
Tau Ceti proves this for finite separable `L/K` (`TauCeti.brauerCohomologyEquiv_baseChange`); here the
class is written as a crossed product over a finite Galois `E ⊆ Kˢ`, `L ⊗_K E` is replaced by the
compositum `F = L · τ(E)` inside `Lˢ`, and the descent field `Z = E^{Gal(F/L)} ⊆ L` splits the
extension into a finite step (Tau Ceti's centralizer argument) and a linearly disjoint one. -/
theorem brauerGroupEquivBr_baseChange (x : BrauerGroup.{u, u} K) :
    brauerGroupEquivBr L (Additive.ofMul (BrauerGroup.baseChange K L x)) =
      brBaseChange K L (brauerGroupEquivBr K (Additive.ofMul x)) := by
  obtain ⟨g, rfl⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq x
  haveI := g.finiteDimensional
  haveI := g.isGalois
  rw [GaloisCocycle.brauerClass_def]
  let τ : SeparableClosure K →ₐ[K] SeparableClosure L := IsSepClosed.lift
  obtain ⟨F, _, _, ι, hιτ, hgen⟩ := exists_compositum τ g.extension
  obtain ⟨π, hπ⟩ := exists_restriction τ g.extension F ι hιτ
  rw [baseChange_crossedProductClass_comap τ g.extension F ι hιτ π hπ
      (restriction_injective g.extension F ι π hπ hgen) g.cocycle,
    brauerGroupEquivBr_apply, brauerGroupEquivBr_apply, brauerExplicitH2Equiv_crossedProductClass,
    brauerExplicitH2Equiv_crossedProductClass, brBaseChange_apply K L τ, AddEquiv.symm_apply_apply,
    explicitMap2_inflateH2 τ g.extension F ι hιτ π hπ]

end Main

end NumberFieldKB.MilneCFT.BrauerBaseChange
