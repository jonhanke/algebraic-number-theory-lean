import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2CupExists
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.GroupCohomology.Corestriction
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Milne, *Class Field Theory*, Chapter II §1: formal properties of cup products

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Proposition 1.39 (p. 73–74): associativity, graded commutativity, compatibility with restriction, corestriction
and inflation of cup products. By uniqueness (`cupProductFamily_cup_unique`) every family agrees with the
explicit family `cupProductFamilyOfCochains` of the cochain formula, so the statements are proved for `cupH`.
-/

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits MonoidalCategory

variable {G : Type} [Group G]

/-- Every cup-product family is the one given by the cochain formula (uniqueness, Prop. 1.38). -/
lemma cup_eq_cupH (c : CupProductFamily G) (M N : Rep ℤ G) (r s n : ℕ) (h : r + s = n)
    (x : groupCohomology M r) (y : groupCohomology N s) :
    c.cup M N r s n h x y = cupH h x y := by
  have hc := cupProductFamily_cup_unique c cupProductFamilyOfCochains
  rw [hc]
  rfl

/-! ### Product of an ordered tuple -/

lemma fprod_eq_prod {r : ℕ} (a : Fin r → G) : fprod a = (List.ofFn a).prod := by
  unfold fprod Fin.partialProd
  simp only [Fin.val_last]
  rw [List.take_of_length_le (by simp)]

lemma fprod_append {r s n : ℕ} (h : r + s = n) (g : Fin n → G) :
    fprod g = fprod (hdF h g) * fprod (tlF h g) := by
  subst h
  rw [fprod_eq_prod, fprod_eq_prod, fprod_eq_prod, List.ofFn_add, List.prod_append]
  rfl

lemma fprod_map {K : Type} [Group K] (f : K →* G) {r : ℕ} (a : Fin r → K) :
    fprod (f ∘ a) = f (fprod a) := by
  rw [fprod_eq_prod, fprod_eq_prod, map_list_prod, List.map_ofFn]

/-! ### (a) Associativity -/

lemma cupC_assoc {M N P : Rep ℤ G} {r s t a b n : ℕ} (h1 : r + s = a) (h2 : a + t = n)
    (h3 : s + t = b) (h4 : r + b = n) (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N)
    (χ : (Fin t → G) → P) (x : Fin n → G) :
    (α_ M N P).hom.hom (cupC h2 (cupC h1 φ ψ) χ x) = cupC h4 φ (cupC h3 ψ χ) x := by
  subst h1 h3 h2
  have e1 : hdF (rfl : r + s = r + s) (hdF (rfl : r + s + t = r + s + t) x) = hdF h4 x := by
    funext i
    simp only [hdF]
    congr 1
  have e2 : tlF (rfl : r + s = r + s) (hdF (rfl : r + s + t = r + s + t) x) =
      hdF (rfl : s + t = s + t) (tlF h4 x) := by
    funext i
    simp only [hdF, tlF]
    congr 1
  have e3 : tlF (rfl : r + s + t = r + s + t) x = tlF (rfl : s + t = s + t) (tlF h4 x) := by
    funext i
    simp only [tlF]
    exact congrArg x (Fin.ext (by simp; omega))
  have e4 : fprod (hdF (rfl : r + s + t = r + s + t) x) =
      fprod (hdF h4 x) * fprod (hdF (rfl : s + t = s + t) (tlF h4 x)) := by
    rw [fprod_append (rfl : r + s = r + s) (hdF (rfl : r + s + t = r + s + t) x), e1, e2]
  simp only [cupC_apply, rtmul, e1, e2, e3, e4, map_mul, Module.End.mul_apply]
  rw [tensor_ρ_tmul]
  rfl

lemma cocyclesMap_cupZ_assoc {M N P : Rep ℤ G} {r s t : ℕ} (z₁ : cocycles M r) (z₂ : cocycles N s)
    (z₃ : cocycles P t) :
    cocyclesMap (MonoidHom.id G) (α_ M N P).hom (r + s + t)
        (cupZ (rfl : r + s + t = r + s + t) (cupZ (rfl : r + s = r + s) z₁ z₂) z₃) =
      cupZ (by omega : r + (s + t) = r + s + t) z₁ (cupZ (rfl : s + t = s + t) z₂ z₃) := by
  apply iCocycles_injective
  funext x
  rw [iCocycles_cocyclesMap]
  erw [iCocycles_cupZ]
  rw [iCocycles_cupZ, iCocycles_cupZ, iCocycles_cupZ]
  exact cupC_assoc rfl rfl rfl _ _ _ _ x

/-- **(a) Associativity** of the cup product, for the cochain-formula cup products. -/
theorem cupH_assoc {M N P : Rep ℤ G} (r s t : ℕ) (x : groupCohomology M r)
    (y : groupCohomology N s) (z : groupCohomology P t) :
    (functor ℤ G (r + s + t)).map (α_ M N P).hom
        (cupH (rfl : r + s + t = r + s + t) (cupH (rfl : r + s = r + s) x y) z) =
      cupH (by omega : r + (s + t) = r + s + t) x (cupH (rfl : s + t = s + t) y z) := by
  refine groupCohomology_induction_on x fun z₁ => groupCohomology_induction_on y fun z₂ =>
    groupCohomology_induction_on z fun z₃ => ?_
  rw [cupH_π, cupH_π, functor_map_π, cupH_π, cupH_π, cocyclesMap_cupZ_assoc]

/-! ### (c), (e) Restriction and inflation (maps along a group homomorphism) -/

lemma iCocycles_cocyclesMap_hom {K : Type} [Group K] (f : K →* G) (A : Rep ℤ G) (m : ℕ)
    (z : cocycles A m) (x : Fin m → K) :
    iCocycles (res f A) m (cocyclesMap f (𝟙 (res f A)) m z) x = iCocycles A m z (f ∘ x) := by
  have := congr($(HomologicalComplex.cyclesMap_i (cochainsMap f (𝟙 (res f A))) m) z)
  exact congrFun this x

lemma cupC_hom {K : Type} [Group K] (f : K →* G) {M N : Rep ℤ G} {r s n : ℕ} (h : r + s = n)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) (x : Fin n → K) :
    cupC h φ ψ (f ∘ x) =
      cupC (M := res f M) (N := res f N) h (fun a => φ (f ∘ a)) (fun b => ψ (f ∘ b)) x := by
  rw [cupC_apply, cupC_apply]
  have e : fprod (hdF h (f ∘ x)) = f (fprod (hdF h x)) := fprod_map f (hdF h x)
  simp only [rtmul]
  rw [e]
  rfl

lemma cocyclesMap_cupZ_hom {K : Type} [Group K] (f : K →* G) {M N : Rep ℤ G} {r s n : ℕ}
    (h : r + s = n) (z₁ : cocycles M r) (z₂ : cocycles N s) :
    cocyclesMap f (𝟙 (res f (M ⊗ N))) n (cupZ h z₁ z₂) =
      cupZ (M := res f M) (N := res f N) h (cocyclesMap f (𝟙 (res f M)) r z₁)
        (cocyclesMap f (𝟙 (res f N)) s z₂) := by
  apply iCocycles_injective
  funext x
  rw [iCocycles_cocyclesMap_hom]
  erw [iCocycles_cupZ]
  have h2 := congrFun (iCocycles_cupZ (M := res f M) (N := res f N) h
    (cocyclesMap f (𝟙 (res f M)) r z₁) (cocyclesMap f (𝟙 (res f N)) s z₂)) x
  refine (cupC_hom f h _ _ x).trans (Eq.trans ?_ h2.symm)
  congr 1 <;> funext a <;> exact (iCocycles_cocyclesMap_hom _ _ _ _ a).symm

/-- Compatibility of the cup product with maps along a group homomorphism `f : K → G` (restriction when `f`
is the inclusion of a subgroup, inflation when `f` is a quotient map). -/
theorem cupH_hom {K : Type} [Group K] (f : K →* G) {M N : Rep ℤ G} (r s n : ℕ) (h : r + s = n)
    (x : groupCohomology M r) (y : groupCohomology N s) :
    map f (𝟙 (res f (M ⊗ N))) n (cupH h x y) =
      cupH (M := res f M) (N := res f N) h (map f (𝟙 (res f M)) r x) (map f (𝟙 (res f N)) s y) := by
  refine groupCohomology_induction_on x fun z₁ => groupCohomology_induction_on y fun z₂ => ?_
  have e1 := π_map_apply f (𝟙 (res f M)) r z₁
  have e2 := π_map_apply f (𝟙 (res f N)) s z₂
  have e3 := π_map_apply f (𝟙 (res f (M ⊗ N))) n (cupZ h z₁ z₂)
  have e4 := cupH_π (M := res f M) (N := res f N) h (cocyclesMap f (𝟙 (res f M)) r z₁)
    (cocyclesMap f (𝟙 (res f N)) s z₂)
  have e5 := cocyclesMap_cupZ_hom f h z₁ z₂
  rw [cupH_π]
  erw [e1, e2, e3, e4, e5]
  rfl

/-! ### (b) Graded commutativity

By dimension shifting. First the analogue of `cup_zero_left` on the right: `y ∪ m` for an invariant `m`. -/

set_option backward.isDefEq.respectTransparency false in
/-- The `G`-map `N ⟶ N ⊗ M`, `n ↦ n ⊗ m`, for an invariant element `m` of `M`. -/
noncomputable def tensorRightOfAux {k : Type} [CommRing k] {M : Rep k G} (m : M.ρ.invariants)
    (N : Rep k G) : N ⟶ N ⊗ M :=
  Rep.ofHom ⟨(TensorProduct.mk k N M).flip (m : M), fun g => by
    refine LinearMap.ext fun n => ?_
    change N.ρ g n ⊗ₜ[k] (m : M) = TensorProduct.map (N.ρ g) (M.ρ g) (n ⊗ₜ[k] (m : M))
    rw [TensorProduct.map_tmul, m.2 g]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The `G`-map `N ⟶ N ⊗ M`, `n ↦ n ⊗ m`, for an invariant element `m` of `M`. -/
noncomputable def tensorRightOf {M : Rep ℤ G} (m : M.ρ.invariants) (N : Rep ℤ G) : N ⟶ N ⊗ M :=
  tensorRightOfAux m N

set_option backward.isDefEq.respectTransparency false in
lemma tensorRightOf_apply {M : Rep ℤ G} (m : M.ρ.invariants) (N : Rep ℤ G) (n : N) :
    (tensorRightOf m N).hom n = rtmul (A := N) (B := M) n (m : M) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `n ↦ n ⊗ m` as a morphism of short complexes `seq15 N ⟶ (seq15 N).map (tensorRight M)`. -/
noncomputable def seq15HomR {M : Rep ℤ G} (m : M.ρ.invariants) (N : Rep ℤ G) :
    seq15 N ⟶ (seq15 N).map (tensorRight M) where
  τ₁ := tensorRightOf m N
  τ₂ := tensorRightOf m (indG G N)
  τ₃ := tensorRightOf m (mStar N)
  comm₁₂ := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
    rfl
  comm₂₃ := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
    rfl

/-- Naturality of the connecting homomorphism, on elements. -/
lemma delta_nat_apply {S S' : ShortComplex (Rep ℤ G)} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (F : S ⟶ S') (i : ℕ) (y : groupCohomology S.X₃ i) :
    (functor ℤ G (i + 1)).map F.τ₁ (δ hS i (i + 1) rfl y) =
      δ hS' i (i + 1) rfl ((functor ℤ G i).map F.τ₃ y) :=
  congrArg (fun φ => φ.hom y) (δ_naturality hS hS' F i (i + 1) rfl)

set_option backward.isDefEq.respectTransparency false in
/-- **Bidegree $(s, 0)$ is forced**: $y \cup m$ is the image of $y$ under $n \mapsto n \otimes m$. -/
theorem cup_zero_right (c : CupProductFamily G) (M : Rep ℤ G) (m : M.ρ.invariants) (s : ℕ) :
    ∀ (N : Rep ℤ G) (y : groupCohomology N s),
      c.cup N M s 0 s (add_zero s) y ((H0Iso M).inv m) =
        (groupCohomology.functor ℤ G s).map (tensorRightOf m N) y := by
  induction s with
  | zero =>
    intro N y
    obtain ⟨n, rfl⟩ : ∃ n, y = (H0Iso N).inv n := ⟨(H0Iso N).hom y, by simp⟩
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback (H0Iso (N ⊗ M)).hom)
    rw [c.zero N M n m]
    have := congrArg (fun φ => φ.hom ((H0Iso N).inv n))
      (map_id_comp_H0Iso_hom (tensorRightOf m N))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    refine Eq.trans ?_ this.symm
    simp only [Iso.inv_hom_id_apply]
    rfl
  | succ s ih =>
    intro N y
    obtain ⟨y', rfl⟩ := delta_surjective N s y
    have h1 := c.delta_left (seq15 N) (seq15_shortExact N) M (seq15_tensorRight M N) s 0 s
      (add_zero s) y' ((H0Iso M).inv m)
    refine h1.trans ?_
    have h2 : c.cup (seq15 N).X₃ M s 0 s (add_zero s) y' ((H0Iso M).inv m) =
        (groupCohomology.functor ℤ G s).map (tensorRightOf m (mStar N)) y' := ih (mStar N) y'
    rw [h2]
    exact (delta_nat_apply (seq15_shortExact N) (seq15_tensorRight M N) (seq15HomR m N) s y').symm

/-- The braiding as a morphism of short complexes `S ⊗ N ⟶ N ⊗ S`. -/
noncomputable def braidHom (S : ShortComplex (Rep ℤ G)) (N : Rep ℤ G) :
    S.map (tensorRight N) ⟶ S.map (tensorLeft N) where
  τ₁ := (β_ S.X₁ N).hom
  τ₂ := (β_ S.X₂ N).hom
  τ₃ := (β_ S.X₃ N).hom
  comm₁₂ := (BraidedCategory.braiding_naturality_left S.f N).symm
  comm₂₃ := (BraidedCategory.braiding_naturality_left S.g N).symm

lemma tensorLeftOf_braid {M : Rep ℤ G} (m : M.ρ.invariants) (N : Rep ℤ G) :
    tensorLeftOf m N ≫ (β_ M N).hom = tensorRightOf m N := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  rfl

/-- **(b) Graded commutativity**, for any family of cup products, by dimension shifting. -/
theorem cup_comm_aux (c : CupProductFamily G) : ∀ (r : ℕ) (M N : Rep ℤ G) (s n : ℕ) (h : r + s = n)
    (h' : s + r = n) (x : groupCohomology M r) (y : groupCohomology N s),
    (functor ℤ G n).map (β_ M N).hom (c.cup M N r s n h x y) =
      (-1 : ℤ) ^ (r * s) • c.cup N M s r n h' y x := by
  intro r
  induction r with
  | zero =>
    intro M N s n h h' x y
    have hn : s = n := by omega
    subst hn
    obtain ⟨m, rfl⟩ : ∃ m, x = (H0Iso M).inv m := ⟨(H0Iso M).hom x, by simp⟩
    rw [cup_zero_left c M m s N y, cup_zero_right c M m s N y, zero_mul, pow_zero]
    erw [one_smul]
    exact congrArg (fun φ => φ.hom y) (show (functor ℤ G s).map (tensorLeftOf m N) ≫
        (functor ℤ G s).map (β_ M N).hom = (functor ℤ G s).map (tensorRightOf m N) by
      rw [← Functor.map_comp, tensorLeftOf_braid])
  | succ r ih =>
    intro M N s n h h' x y
    obtain ⟨x', rfl⟩ := delta_surjective M r x
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
    have hm : r + s = m := by omega
    have hm' : s + r = m := by omega
    have h1 := c.delta_left (seq15 M) (seq15_shortExact M) N (seq15_tensorRight N M) r s m hm x' y
    have h2 := c.delta_right N (seq15 M) (seq15_shortExact M) (seq15_tensorLeft N M) s r m hm' y x'
    have h3 := ih (seq15 M).X₃ N s m hm hm' x' y
    have e1 : c.cup M N (r + 1) s (m + 1) h (δ (seq15_shortExact M) r (r + 1) rfl x') y =
        δ (seq15_tensorRight N M) m (m + 1) rfl (c.cup (seq15 M).X₃ N r s m hm x' y) := h1
    have e2 : c.cup N M s (r + 1) (m + 1) h' y (δ (seq15_shortExact M) r (r + 1) rfl x') =
        (-1 : ℤ) ^ s • δ (seq15_tensorLeft N M) m (m + 1) rfl
          (c.cup N (seq15 M).X₃ s r m hm' y x') := h2
    rw [e1, e2]
    have h4 := delta_nat_apply (seq15_tensorRight N M) (seq15_tensorLeft N M)
      (braidHom (seq15 M) N) m (c.cup (seq15 M).X₃ N r s m hm x' y)
    refine h4.trans ?_
    change δ (seq15_tensorLeft N M) m (m + 1) rfl
        ((functor ℤ G m).map (β_ (seq15 M).X₃ N).hom (c.cup (seq15 M).X₃ N r s m hm x' y)) = _
    rw [h3, map_zsmul]
    have hsign : (-1 : ℤ) ^ ((r + 1) * s) * (-1 : ℤ) ^ s = (-1 : ℤ) ^ (r * s) := by
      rw [← pow_add, show (r + 1) * s + s = r * s + 2 * s by ring, pow_add, pow_mul]
      simp
    erw [smul_smul, hsign]
    rfl

/-- **(b) Graded commutativity** for the cochain-formula cup products stated for any family. -/
theorem cup_comm (c : CupProductFamily G) (M N : Rep ℤ G) (r s : ℕ) (x : groupCohomology M r)
    (y : groupCohomology N s) :
    (functor ℤ G (r + s)).map (β_ M N).hom (c.cup M N r s (r + s) rfl x y) =
      (-1 : ℤ) ^ (r * s) • c.cup N M s r (r + s) (by omega) y x :=
  cup_comm_aux c r M N s (r + s) rfl (by omega) x y

/-! ### (d) Corestriction

Corestriction `cor` is identified with the (ported) Tau Ceti corestriction, which commutes with connecting
homomorphisms and is natural in the coefficients; the proof is then dimension shifting in `y`. -/

section Cor

variable (H : Subgroup G) [Fintype (G ⧸ H)] [H.FiniteIndex]

section
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open scoped Classical in
lemma coindToSelf_eq_counit (M : Rep ℤ G) :
    coindToSelf H M = (Rep.coindResAdjunction.{0, 0, 0} ℤ H).counit.app M := by
  have key : ∀ φ : coind H.subtype (res H.subtype M),
      (coindToSelf H M).hom φ = ((Rep.coindResAdjunction.{0, 0, 0} ℤ H).counit.app M).hom φ := by
    intro φ
    rw [Subgroup.coindResAdjunction_counit_app_hom_apply]
    set E := QuotientGroup.quotientRightRelEquivQuotientLeftRel H with hE
    have hs : ∀ q : G ⧸ H, ((((E.symm q).out)⁻¹ : G) : G ⧸ H) = q := by
      intro q
      have h1 : E (E.symm q) = q := E.apply_symm_apply q
      conv_rhs => rw [← h1]
      conv_rhs => rw [← Quotient.out_eq (E.symm q)]
      rfl
    rw [coindToSelf_indep H M φ (fun q => ((E.symm q).out)⁻¹) hs]
    convert Fintype.sum_equiv E.symm (fun q => M.ρ ((E.symm q).out)⁻¹ (φ.1 ((E.symm q).out)⁻¹⁻¹))
      (fun p : Quotient (QuotientGroup.rightRel H) => M.ρ p.out⁻¹ (φ.1 p.out))
      (fun q => by simp)
  apply Rep.hom_ext
  exact DFunLike.ext' (funext key)

end

/-- Milne's corestriction `cor` is the (ported) Tau Ceti corestriction. -/
lemma cor_eq_corestriction (M : Rep ℤ G) (r : ℕ) :
    cor H M r = TauCeti.groupCohomology.corestriction H M r := by
  rw [cor, coindToSelf_eq_counit]
  exact (Iso.inv_comp_eq _).2 (TauCeti.groupCohomology.coindIso_hom_comp_corestriction H M r).symm

/-- Corestriction commutes with connecting homomorphisms. -/
lemma cor_delta {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) (i : ℕ)
    (w : groupCohomology (res H.subtype X.X₃) i) :
    cor H X.X₁ (i + 1) (δ ((Rep.shortExact_res H.subtype).2 hX) i (i + 1) rfl w) =
      δ hX i (i + 1) rfl (cor H X.X₃ i w) := by
  rw [cor_eq_corestriction, cor_eq_corestriction]
  exact congrArg (fun φ => φ.hom w)
    (TauCeti.groupCohomology.δ_comp_corestriction H hX i (i + 1) rfl)

/-- Corestriction is natural in the coefficients. -/
lemma cor_natural {M M' : Rep ℤ G} (φ : M ⟶ M') (r : ℕ) (x : groupCohomology (res H.subtype M) r) :
    cor H M' r (map (MonoidHom.id H) ((resFunctor H.subtype).map φ) r x) =
      map (MonoidHom.id G) φ r (cor H M r x) := by
  rw [cor_eq_corestriction, cor_eq_corestriction]
  exact congrArg (fun ψ => ψ.hom x) (TauCeti.groupCohomology.map_comp_corestriction H φ r)

end Cor

/-- Restriction (change of group) commutes with connecting homomorphisms. -/
lemma res_delta {K : Type} [Group K] (f : K →* G) {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact)
    (i : ℕ) (y : groupCohomology S.X₃ i) :
    map f (𝟙 (res f S.X₁)) (i + 1) (δ hS i (i + 1) rfl y) =
      δ ((Rep.shortExact_res f).2 hS) i (i + 1) rfl (map f (𝟙 (res f S.X₃)) i y) :=
  congrArg (fun φ => φ.hom y)
    (TauCeti.groupCohomology.δ_naturality f hS ((Rep.shortExact_res f).2 hS)
      (𝟙 (S.map (resFunctor f))) i (i + 1) rfl)

lemma map_res_H0Iso_inv {K : Type} [Group K] (f : K →* G) (N : Rep ℤ G) (n : N.ρ.invariants) :
    map f (𝟙 (res f N)) 0 ((H0Iso N).inv n) =
      (H0Iso (res f N)).inv ⟨(n : N), fun k => n.2 (f k)⟩ := by
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback (H0Iso (res f N)).hom)
  rw [Iso.inv_hom_id_apply]
  apply Subtype.ext
  have := map_H0Iso_hom_f_apply f (𝟙 (res f N)) ((H0Iso N).inv n)
  erw [Iso.inv_hom_id_apply] at this
  exact this

lemma res_tensorRightOf (H : Subgroup G) {M : Rep ℤ G} (m : M.ρ.invariants) (N : Rep ℤ G) :
    (resFunctor H.subtype).map (tensorRightOf m N) =
      tensorRightOf (M := res H.subtype M) ⟨(m : M), fun k => m.2 (H.subtype k)⟩ (res H.subtype N) :=
  rfl

/-- **(d)** for the cochain-formula cup products, by dimension shifting in `y`. -/
theorem cupH_cor (H : Subgroup G) [Fintype (G ⧸ H)] [H.FiniteIndex] (M : Rep ℤ G) (r : ℕ)
    (x : groupCohomology (res H.subtype M) r) :
    ∀ (s : ℕ) (N : Rep ℤ G) (n : ℕ) (h : r + s = n) (y : groupCohomology N s),
      cor H (M ⊗ N) n (cupH (M := res H.subtype M) (N := res H.subtype N) h x
          (map H.subtype (𝟙 (res H.subtype N)) s y)) =
        cupH h (cor H M r x) y := by
  intro s
  induction s with
  | zero =>
    intro N n h y
    have hn : r = n := by omega
    subst hn
    obtain ⟨m, rfl⟩ : ∃ m, y = (H0Iso N).inv m := ⟨(H0Iso N).hom y, by simp⟩
    rw [map_res_H0Iso_inv]
    have h1 : cupH h x ((H0Iso (res H.subtype N)).inv ⟨(m : N), fun k => m.2 (H.subtype k)⟩) =
        (groupCohomology.functor ℤ H r).map (tensorRightOf (M := res H.subtype N)
          ⟨(m : N), fun k => m.2 (H.subtype k)⟩ (res H.subtype M)) x :=
      cup_zero_right (cupProductFamilyOfCochains (G := H)) (res H.subtype N) _ r
        (res H.subtype M) x
    have h2 : cupH h (cor H M r x) ((H0Iso N).inv m) =
        (groupCohomology.functor ℤ G r).map (tensorRightOf m M) (cor H M r x) :=
      cup_zero_right (cupProductFamilyOfCochains (G := G)) N m r M (cor H M r x)
    rw [h1, h2]
    exact cor_natural H (tensorRightOf m M) r x
  | succ s ih =>
    intro N n h y
    obtain ⟨y', rfl⟩ := delta_surjective N s y
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
    have hm : r + s = m := by omega
    have hS := seq15_shortExact N
    have E1 : cupH (M := res H.subtype M) (N := res H.subtype N) h x
        (map H.subtype (𝟙 (res H.subtype N)) (s + 1) (δ hS s (s + 1) rfl y')) =
        (-1 : ℤ) ^ r • δ ((Rep.shortExact_res H.subtype).2 (seq15_tensorLeft M N)) m (m + 1) rfl
          (cupH (M := res H.subtype M) (N := res H.subtype (seq15 N).X₃) hm x
            (map H.subtype (𝟙 (res H.subtype (seq15 N).X₃)) s y')) := by
      refine (congrArg (fun z => cupH (M := res H.subtype M) (N := res H.subtype N) h x z)
        (res_delta H.subtype hS s y')).trans ?_
      exact (cupProductFamilyOfCochains (G := H)).delta_right (res H.subtype M)
        ((seq15 N).map (resFunctor H.subtype)) ((Rep.shortExact_res H.subtype).2 hS)
        ((Rep.shortExact_res H.subtype).2 (seq15_tensorLeft M N)) r s m hm x
        (map H.subtype (𝟙 (res H.subtype (seq15 N).X₃)) s y')
    have E2 : cor H (M ⊗ N) (m + 1)
        (δ ((Rep.shortExact_res H.subtype).2 (seq15_tensorLeft M N)) m (m + 1) rfl
          (cupH (M := res H.subtype M) (N := res H.subtype (seq15 N).X₃) hm x
            (map H.subtype (𝟙 (res H.subtype (seq15 N).X₃)) s y'))) =
        δ (seq15_tensorLeft M N) m (m + 1) rfl
          (cor H (M ⊗ (seq15 N).X₃) m
            (cupH (M := res H.subtype M) (N := res H.subtype (seq15 N).X₃) hm x
              (map H.subtype (𝟙 (res H.subtype (seq15 N).X₃)) s y'))) :=
      cor_delta H (X := (seq15 N).map (tensorLeft M)) (seq15_tensorLeft M N) m _
    have E3 := ih (seq15 N).X₃ m hm y'
    have E4 : cupH h (cor H M r x) (δ hS s (s + 1) rfl y') =
        (-1 : ℤ) ^ r • δ (seq15_tensorLeft M N) m (m + 1) rfl
          (cupH hm (cor H M r x) y') :=
      (cupProductFamilyOfCochains (G := G)).delta_right M (seq15 N) hS (seq15_tensorLeft M N)
        r s m hm (cor H M r x) y'
    refine (congrArg (fun z => cor H (M ⊗ N) (m + 1) z) E1).trans (Eq.trans ?_ E4.symm)
    refine Eq.trans (map_zsmul (cor H (M ⊗ N) (m + 1)).hom _ _) ?_
    exact congrArg (fun z => (-1 : ℤ) ^ r • z)
      (E2.trans (congrArg (fun z => δ (seq15_tensorLeft M N) m (m + 1) rfl z) E3))

/-- **Proposition 1.39** (Milne, CFT v4.03, Ch. II, p. 73–74): associativity, graded commutativity, and
compatibility of cup products with restriction, corestriction and inflation. Every family of cup products is the
cochain-formula family (`cupProductFamily_cup_unique`); (a), (c), (e) are checked on cochains
(`cupC_assoc`, `cupC_hom`), (b) and (d) by dimension shifting (`cup_comm_aux`, `cupH_cor`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.39, p. 73–74"]
theorem prop1_39 : Prop1_39 where
  assoc_cup G _ c M N P r s t x y z := by
    rw [cupProductFamily_cup_unique c cupProductFamilyOfCochains]
    exact cupH_assoc r s t x y z
  comm_cup G _ c M N r s x y := cup_comm c M N r s x y
  res_cup G _ H cG cH M N r s x y := by
    rw [cupProductFamily_cup_unique cG cupProductFamilyOfCochains,
      cupProductFamily_cup_unique cH cupProductFamilyOfCochains]
    exact cupH_hom H.subtype r s (r + s) rfl x y
  cor_cup G _ H _ cG cH M N r s x y := by
    have : H.FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
    rw [cupProductFamily_cup_unique cG cupProductFamilyOfCochains,
      cupProductFamily_cup_unique cH cupProductFamilyOfCochains]
    exact cupH_cor H M r x s N (r + s) rfl y
  inf_cup G _ H _ cG cQ M N r s x y := by
    rw [cupProductFamily_cup_unique cG cupProductFamilyOfCochains,
      cupProductFamily_cup_unique cQ cupProductFamilyOfCochains]
    exact cupH_hom (QuotientGroup.mk' H) r s (r + s) rfl x y

end NumberFieldKB.MilneCFT
