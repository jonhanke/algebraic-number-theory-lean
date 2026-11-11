import Mathlib.Tactic.Have
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3UnramifiedInv

/-!
# Milne, *Class Field Theory*, Chapter III §1: the invariant maps are compatible with inflation

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

`theorem_1_7_infl`: for $K \subseteq L \subseteq E$ finite unramified Galois, $\mathrm{inv}_{E/K} \circ
\mathrm{Inf} = \mathrm{inv}_{L/K}$ (p. 99), so the finite-level maps of `theorem_1_7` define
$\mathrm{inv}_K$ on $H^2(K^{\mathrm{un}}/K) = \varinjlim H^2(L/K)$. Ingredients: $\delta$ and
$H^1(G, \mathbb Q/\mathbb Z) \simeq \operatorname{Hom}(G, \mathbb Q/\mathbb Z)$ are natural for inflation
along any group homomorphism (`h2IntToHom_natural`), and $\mathrm{ord}_E$ restricts to $\mathrm{ord}_L$
(`ord_incl`, from display (26)).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

section Natural

variable {G G' : Type} [Group G] [Group G'] (f : G →* G')

/-- The identity map from the restriction along `f` of a trivial module to the trivial module. -/
noncomputable def trivRes (M : Type) [AddCommGroup M] [Module ℤ M] :
    res f (Rep.of (Representation.trivial ℤ G' M)) ⟶ Rep.of (Representation.trivial ℤ G M) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- Inflation along `f` as a morphism of the short exact sequences of cochain complexes. -/
noncomputable def seqZQmap :
    ((seqZQ G').map (cochainsFunctor ℤ G')) ⟶ ((seqZQ G).map (cochainsFunctor ℤ G)) where
  τ₁ := cochainsMap f (trivRes f ℤ)
  τ₂ := cochainsMap f (trivRes f ℚ)
  τ₃ := cochainsMap f (trivRes f QZ)
  comm₁₂ := by
    ext i
    rfl
  comm₂₃ := by
    ext i
    rfl

variable [Fintype G] [Fintype G']

theorem h2IntToHom_apply_delta (w : groupCohomology (seqZQ G).X₃ 1) :
    h2IntToHom.hom ((δ (seqZQ_shortExact G) 1 2 rfl).hom w) = (H1IsoOfIsTrivial (seqZQ G).X₃).hom.hom w := by
  have := @lemma_3_3c G _ _
  unfold h2IntToHom
  have h : (inv (δ (seqZQ_shortExact G) 1 2 rfl)).hom ((δ (seqZQ_shortExact G) 1 2 rfl).hom w) = w := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.hom_inv_id]; rfl
  exact congrArg (H1IsoOfIsTrivial (seqZQ G).X₃).hom.hom h

theorem delta_natural (w : groupCohomology (seqZQ G').X₃ 1) :
    (map f (trivRes f ℤ) 2).hom ((δ (seqZQ_shortExact G') 1 2 rfl).hom w) =
      (δ (seqZQ_shortExact G) 1 2 rfl).hom ((map f (trivRes f QZ) 1).hom w) := by
  have := HomologicalComplex.HomologySequence.δ_naturality (seqZQmap f)
    (map_cochainsFunctor_shortExact (seqZQ_shortExact G')) (map_cochainsFunctor_shortExact (seqZQ_shortExact G)) 1 2 rfl
  exact congr($(this).hom w)

theorem h1_natural (w : H1 (seqZQ G').X₃) (σ : G) :
    (H1IsoOfIsTrivial (seqZQ G).X₃).hom.hom ((map f (trivRes f QZ) 1).hom w) (Additive.ofMul σ) =
      (H1IsoOfIsTrivial (seqZQ G').X₃).hom.hom w (Additive.ofMul (f σ)) := by
  refine H1_induction_on w fun z => ?_
  erw [H1π_comp_map_apply]
  erw [H1IsoOfIsTrivial_H1π_apply_apply, H1IsoOfIsTrivial_H1π_apply_apply]
  rfl

/-- Naturality of `h2IntToHom` for inflation along `f`. -/
theorem h2IntToHom_natural (y : groupCohomology (seqZQ G').X₁ 2) (σ : G) :
    h2IntToHom.hom ((map f (trivRes f ℤ) 2).hom y) (Additive.ofMul σ) =
      h2IntToHom.hom y (Additive.ofMul (f σ)) := by
  have := @lemma_3_3c G' _ _
  obtain ⟨w, rfl⟩ := ConcreteCategory.bijective_of_isIso (δ (seqZQ_shortExact G') 1 2 rfl) |>.2 y
  rw [delta_natural, h2IntToHom_apply_delta]
  have e := h2IntToHom_apply_delta (G := G) ((map f (trivRes f QZ) 1).hom w)
  erw [e]
  exact h1_natural f w σ

end Natural

section Compat

variable {G G' : Type} [Group G] [Group G'] (f : G →* G')

/-- Inflation commutes with a compatible pair of maps to the trivial module `ℤ`. -/
theorem map_comm_ord {A : Rep ℤ G'} {B : Rep ℤ G} (φ : res f A ⟶ B) (a : A ⟶ (seqZQ G').X₁)
    (b : B ⟶ (seqZQ G).X₁) (hab : ∀ x, b.hom (φ.hom x) = (trivRes f ℤ).hom (a.hom x))
    (x : groupCohomology A 2) :
    (map (MonoidHom.id G) b 2).hom ((map f φ 2).hom x) =
      (map f (trivRes f ℤ) 2).hom ((map (MonoidHom.id G') a 2).hom x) := by
  have e1 := map_comp f (MonoidHom.id G) φ b 2
  have e2 := map_comp (MonoidHom.id G') f a (trivRes f ℤ) 2
  have e3 : map (f.comp (MonoidHom.id G)) ((resFunctor (MonoidHom.id G)).map φ ≫ b) 2 =
      map ((MonoidHom.id G').comp f) ((resFunctor f).map a ≫ trivRes f ℤ) 2 :=
    map_congr rfl (LinearMap.ext fun y => hab y) 2
  have := e1.symm.trans (e3.trans e2)
  exact congr($(this).hom x)

end Compat

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The inclusion `L^× → E^×` for `L ≤ E`. -/
noncomputable abbrev inclUnits {L E : IntermediateField K Ω} (h : L ≤ E) : Lˣ →* Eˣ :=
  Units.map (IntermediateField.inclusion h).toRingHom.toMonoidHom

theorem inclUnits_embUnits {L E : IntermediateField K Ω} (h : L ≤ E) (a : Kˣ) :
    inclUnits h (embUnits L a) = embUnits E a :=
  Units.ext rfl

/-- The inclusion `L^× → E^×` maps `U_L` into `U_E`. -/
theorem inclUnits_mem_unitsL {L E : IntermediateField K Ω} (h : L ≤ E) {x : Lˣ} (hx : x ∈ unitsL L) :
    inclUnits h x ∈ unitsL E := by
  have key : ∀ y : L, y ∈ integers L → IntermediateField.inclusion h y ∈ integers E := by
    intro y hy
    have hy' : IsIntegral 𝒪[K] y := hy
    exact hy'.map ((IntermediateField.inclusion h).restrictScalars 𝒪[K])
  exact ⟨key _ hx.1, key _ hx.2⟩

theorem ord_embUnits (h26 : UnitPrimeDecomposition K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    (hM : IsUnramifiedExt M) {v : Additive Mˣ →+ ℤ} (hv : IsNormalizedOrd M v) {π : 𝒪[K]}
    (hπ : Irreducible π) : v (Additive.ofMul (embUnits M (primeUnit hπ))) = 1 := by
  have hnn : 0 ≤ v (Additive.ofMul (embUnits M (primeUnit hπ))) := by
    apply hv.nonneg
    have e : ((embUnits M (primeUnit hπ) : Mˣ) : M) = algebraMap 𝒪[K] M π :=
      (IsScalarTower.algebraMap_apply 𝒪[K] K M π).symm
    rw [e]
    exact isIntegral_algebraMap
  obtain ⟨y, hy⟩ := hv.surj 1
  obtain ⟨u, hu, m, hm⟩ := h26.decomp M hM hπ (Additive.toMul y)
  have h0 := (hv.ker u).2 hu
  have : y = Additive.ofMul u + m • Additive.ofMul (embUnits M (primeUnit hπ)) := by
    apply Additive.toMul.injective
    simp [hm]
  rw [this, map_add, map_zsmul, h0, zero_add, smul_eq_mul] at hy
  exact Int.eq_one_of_mul_eq_one_left hnn hy

/-- `ord_E` restricted to `L^×` is `ord_L`. -/
theorem ord_incl (h26 : UnitPrimeDecomposition K Ω) {L E : IntermediateField K Ω} (h : L ≤ E)
    [FiniteDimensional K L] [FiniteDimensional K E] (hL : IsUnramifiedExt L) (hE : IsUnramifiedExt E)
    {vL : Additive Lˣ →+ ℤ} (hvL : IsNormalizedOrd L vL) {vE : Additive Eˣ →+ ℤ} (hvE : IsNormalizedOrd E vE)
    (x : Lˣ) : vE (Additive.ofMul (inclUnits h x)) = vL (Additive.ofMul x) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨u, hu, m, rfl⟩ := h26.decomp L hL hπ x
  have h1 : vE (Additive.ofMul (inclUnits h u)) = 0 := (hvE.ker _).2 (inclUnits_mem_unitsL h hu)
  have h2 : vL (Additive.ofMul u) = 0 := (hvL.ker u).2 hu
  have e1 : Additive.ofMul (inclUnits h (u * embUnits L (primeUnit hπ) ^ m)) =
      Additive.ofMul (inclUnits h u) + m • Additive.ofMul (embUnits E (primeUnit hπ)) := by
    rw [map_mul, map_zpow, inclUnits_embUnits]; rfl
  have e2 : Additive.ofMul (u * embUnits L (primeUnit hπ) ^ m) =
      Additive.ofMul u + m • Additive.ofMul (embUnits L (primeUnit hπ)) := rfl
  rw [e1, e2, map_add, map_add, map_zsmul, map_zsmul, h1, h2, ord_embUnits h26 E hE hvE hπ,
    ord_embUnits h26 L hL hvL hπ]

/-- **Theorem 1.7** (p. 99–100), compatibility with inflation: for $K \subseteq L \subseteq E$ with $L$, $E$ finite
unramified Galois over $K$, $\mathrm{inv}_{E/K} \circ \mathrm{Inf} = \mathrm{inv}_{L/K}$ ("all the maps in the
definition of inv are compatible with Inf", p. 99). Here $\mathrm{Frob}_{L/K}$ is written as the restriction of
$\mathrm{Frob}_{E/K}$ to $L$ (the restriction of a Frobenius element is a Frobenius element). The identity holds for
every $\sigma \in \operatorname{Gal}(E/K)$ in place of $\mathrm{Frob}_{E/K}$, so no Frobenius hypothesis is
needed. -/
@[kb "milne2020cft" "v4.03, Ch. III, §1, inv compatible with Inf, p. 99"]
theorem theorem_1_7_infl (h26 : UnitPrimeDecomposition K Ω)
    {L E : IntermediateField K Ω} (h : L ≤ E) [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K E]
    [IsGalois K E] (hL : IsUnramifiedExt L) (hE : IsUnramifiedExt E)
    {vL : Additive Lˣ →+ ℤ} (hvL : IsNormalizedOrd L vL) {vE : Additive Eˣ →+ ℤ} (hvE : IsNormalizedOrd E vE)
    (σE : Gal(E/K)) (x : H2 L) :
    invK E hvE σE ((inflK h).hom x) = invK L hvL (galRestrict h σE) x := by
  have hnat := h2IntToHom_natural (galRestrict h) ((map (MonoidHom.id Gal(L/K)) (ordRep hvL) 2).hom x) σE
  refine Eq.trans ?_ hnat
  unfold invK invOf
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 2
  unfold inflK
  refine map_comm_ord (galRestrict h) _ (ordRep hvL) (ordRep hvE) (fun y => ?_) x
  exact ord_incl h26 h hL hE hvL hvE (Additive.toMul y)

end NumberFieldKB.MilneCFT.Ch3
