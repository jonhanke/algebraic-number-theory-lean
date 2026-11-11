import Mathlib.Algebra.Torsor.Defs
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Tate
import NumberFieldKB.MilneCFT.Ch2Exact

/-!
# Milne, *Class Field Theory*, Chapter II §3: the Herbrand quotient

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Milne (p. 81): for a finite cyclic group $G$ and a $G$-module $M$ whose cohomology groups are finite, the Herbrand
quotient is $h(M) = |H^0_T(G, M)| / |H^1_T(G, M)|$.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits


/-! ## An exact hexagon of abelian groups -/

section Hexagon

lemma card_eq_range_mul_range {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (h : Function.Exact f g) :
    Nat.card B = Nat.card f.range * Nat.card g.range := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  have h2 : Nat.card (B ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv
  have h3 : g.ker = f.range := (AddMonoidHom.exact_iff.1 h)
  rw [h1, h2, h3, mul_comm]

lemma finite_iff_card_ne_zero (A : Type*) [Zero A] : Finite A ↔ Nat.card A ≠ 0 := by
  rw [Nat.card_ne_zero]; exact ⟨fun h => ⟨⟨0⟩, h⟩, fun h => h.2⟩

lemma hexagon {A1 A2 A3 A4 A5 A6 : Type*} [AddCommGroup A1] [AddCommGroup A2] [AddCommGroup A3]
    [AddCommGroup A4] [AddCommGroup A5] [AddCommGroup A6]
    (f1 : A1 →+ A2) (f2 : A2 →+ A3) (f3 : A3 →+ A4) (f4 : A4 →+ A5) (f5 : A5 →+ A6) (f6 : A6 →+ A1)
    (e1 : Function.Exact f6 f1) (e2 : Function.Exact f1 f2) (e3 : Function.Exact f2 f3)
    (e4 : Function.Exact f3 f4) (e5 : Function.Exact f4 f5) (e6 : Function.Exact f5 f6) :
    ((Finite A1 ∧ Finite A4 → Finite A2 ∧ Finite A5 → Finite A3 ∧ Finite A6) ∧
      (Finite A1 ∧ Finite A4 → Finite A3 ∧ Finite A6 → Finite A2 ∧ Finite A5) ∧
      (Finite A2 ∧ Finite A5 → Finite A3 ∧ Finite A6 → Finite A1 ∧ Finite A4)) ∧
    (Finite A1 ∧ Finite A4 → Finite A2 ∧ Finite A5 → Finite A3 ∧ Finite A6 →
      (Nat.card A2 : ℚ) / Nat.card A5 =
        ((Nat.card A1 : ℚ) / Nat.card A4) * ((Nat.card A3 : ℚ) / Nat.card A6)) := by
  have n1 := card_eq_range_mul_range f6 f1 e1
  have n2 := card_eq_range_mul_range f1 f2 e2
  have n3 := card_eq_range_mul_range f2 f3 e3
  have n4 := card_eq_range_mul_range f3 f4 e4
  have n5 := card_eq_range_mul_range f4 f5 e5
  have n6 := card_eq_range_mul_range f5 f6 e6
  simp only [finite_iff_card_ne_zero, n1, n2, n3, n4, n5, n6, ne_eq, mul_eq_zero]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · tauto
  · tauto
  · tauto
  · intro h1 h2 h3
    have : ∀ x : ℕ, x ≠ 0 → (x : ℚ) ≠ 0 := fun x hx => by exact_mod_cast hx
    have a1 := this _ (by tauto : Nat.card f1.range ≠ 0)
    have a2 := this _ (by tauto : Nat.card f2.range ≠ 0)
    have a3 := this _ (by tauto : Nat.card f3.range ≠ 0)
    have a4 := this _ (by tauto : Nat.card f4.range ≠ 0)
    have a5 := this _ (by tauto : Nat.card f5.range ≠ 0)
    have a6 := this _ (by tauto : Nat.card f6.range ≠ 0)
    push_cast
    field_simp

lemma card_mul_of_exact {A K H B : Type*} [AddCommGroup A] [AddCommGroup K] [AddCommGroup H]
    [AddCommGroup B] (f : A →+ K) (π : K →+ H) (hs : Function.Surjective π)
    (ex : Function.Exact f π) (ι : K →+ B) (hι : Function.Injective ι) :
    Nat.card K = Nat.card (ι.comp f).range * Nat.card H := by
  rw [card_eq_range_mul_range f π ex]
  congr 1
  · rw [AddMonoidHom.range_comp]
    exact Nat.card_congr (AddSubgroup.equivMapOfInjective f.range ι hι).toEquiv
  · rw [AddMonoidHom.range_eq_top_of_surjective _ hs]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv

lemma card_range_lin {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (f : M →ₗ[ℤ] N) : Nat.card f.toAddMonoidHom.range = Nat.card (LinearMap.range f) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp)

open Rep.FiniteCyclicGroup in
theorem herbrand_core {G : Type} [CommGroup G] [Fintype G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep ℤ G) [Finite A] :
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 1) = Nat.card (groupCohomology A 2) := by
  let S2 := normHomCompSub A g
  let S1 := subCompNormHom A g
  have hs2 : Function.Surjective (groupCohomologyπEven A g hg 2 even_two).hom := by
    unfold groupCohomologyπEven
    have h1 : Function.Surjective (normHomCompSub A g).homologyπ.hom :=
      (ModuleCat.epi_iff_surjective _).1 inferInstance
    have h2 : Function.Surjective (normHomCompSub A g).moduleCatCyclesIso.inv.hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    have h3 : Function.Surjective (groupCohomologyIsoEven A g hg 2 even_two).inv.hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    exact h3.comp (h1.comp h2)
  have hs1 : Function.Surjective (groupCohomologyπOdd A g hg 1 odd_one).hom := by
    unfold groupCohomologyπOdd
    have h1 : Function.Surjective (subCompNormHom A g).homologyπ.hom :=
      (ModuleCat.epi_iff_surjective _).1 inferInstance
    have h2 : Function.Surjective (subCompNormHom A g).moduleCatCyclesIso.inv.hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    have h3 : Function.Surjective (groupCohomologyIsoOdd A g hg 1 odd_one).inv.hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    exact h3.comp (h1.comp h2)
  have ex2 : Function.Exact S2.moduleCatToCycles.toAddMonoidHom
      (groupCohomologyπEven A g hg 2 even_two).hom.toAddMonoidHom := by
    intro x
    refine (groupCohomologyπEven_eq_zero_iff A g hg 2 even_two x).trans ?_
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a, Subtype.ext ha⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  have ex1 : Function.Exact S1.moduleCatToCycles.toAddMonoidHom
      (groupCohomologyπOdd A g hg 1 odd_one).hom.toAddMonoidHom := by
    intro x
    refine (groupCohomologyπOdd_eq_zero_iff A g hg 1 odd_one x).trans ?_
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a, Subtype.ext ha⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  have c2 := card_mul_of_exact _ _ hs2 ex2 (LinearMap.ker S2.g.hom).subtype.toAddMonoidHom
    Subtype.val_injective
  have c1 := card_mul_of_exact _ _ hs1 ex1 (LinearMap.ker S1.g.hom).subtype.toAddMonoidHom
    Subtype.val_injective
  have R2 : Nat.card ((LinearMap.ker S2.g.hom).subtype.toAddMonoidHom.comp
        S2.moduleCatToCycles.toAddMonoidHom).range = Nat.card (LinearMap.range S2.f.hom) :=
    card_range_lin S2.f.hom
  have R1 : Nat.card ((LinearMap.ker S1.g.hom).subtype.toAddMonoidHom.comp
        S1.moduleCatToCycles.toAddMonoidHom).range = Nat.card (LinearMap.range S1.f.hom) :=
    card_range_lin S1.f.hom
  rw [R2] at c2
  rw [R1] at c1
  have kA1 := card_eq_ker_mul_range S2.g.hom
  have kA2 := card_eq_ker_mul_range S1.g.hom
  have e1 : Nat.card (LinearMap.range S2.g.hom) = Nat.card (LinearMap.range S1.f.hom) := rfl
  have p1 : 0 < Nat.card (LinearMap.range S1.f.hom) := Nat.card_pos
  have p2 : 0 < Nat.card (LinearMap.range S2.f.hom) := Nat.card_pos
  have c2' : Nat.card (LinearMap.ker S2.g.hom) =
      Nat.card (LinearMap.range S2.f.hom) * Nat.card (groupCohomology A 2) := c2
  have c1' : Nat.card (LinearMap.ker S1.g.hom) =
      Nat.card (LinearMap.range S1.f.hom) * Nat.card (groupCohomology A 1) := c1
  rw [c2', e1] at kA1
  rw [c1'] at kA2
  have := kA2.symm.trans kA1
  have h12 : (Nat.card (LinearMap.range S2.f.hom) * Nat.card (LinearMap.range S1.f.hom)) *
      Nat.card (groupCohomology A 1) = (Nat.card (LinearMap.range S2.f.hom) *
      Nat.card (LinearMap.range S1.f.hom)) * Nat.card (groupCohomology A 2) := by
    calc _ = Nat.card (LinearMap.range S1.f.hom) * Nat.card (groupCohomology A 1) *
          Nat.card (LinearMap.range S2.f.hom) := by ring
      _ = _ := this
      _ = _ := by ring
  exact ⟨Finite.of_surjective _ hs1, Finite.of_surjective _ hs2,
    Nat.eq_of_mul_eq_mul_left (Nat.mul_pos p2 p1) h12⟩


end Hexagon

section Herbrand

variable {G : Type} [Group G] [Fintype G]

/-! ## The Herbrand quotient -/

/-- The Herbrand quotient is **defined** (p. 81) when $H^0_T(G, M)$ and $H^1(G, M)$ are finite. -/
@[kb "milne2020cft" "v4.03, Ch. II, §3, definition of the Herbrand quotient, p. 81"]
def HerbrandDefined (M : Rep ℤ G) : Prop :=
  Finite (tateCohomology M 0) ∧ Finite (tateCohomology M 1)

/-- The **Herbrand quotient** (p. 81) of a module over a finite cyclic group:
$h(M) = |H^0_T(G, M)| / |H^1_T(G, M)|$ (meaningful when `HerbrandDefined M`). Milne writes $H^1$ for
$H^1_T = H^1$ (Mathlib's `TateCohomology.isoGroupCohomology`). This is a new definition for any finite cyclic
group; QuadFormsKB's `QuadFormsKB.HN.herbrand0` and `QuadFormsKB.HN.herbrandM1` treat an involution of an
abelian group (order 2) concretely, by indices. -/
@[kb "milne2020cft" "v4.03, Ch. II, §3, definition of the Herbrand quotient, p. 81"]
noncomputable def herbrandQuotient (M : Rep ℤ G) : ℚ :=
  (Nat.card (tateCohomology M 0) : ℚ) / Nat.card (tateCohomology M 1)

/-- **Proposition 3.6** (p. 81). Let $G$ be finite cyclic and $0 \to M' \to M \to M'' \to 0$ exact. If two of
$h(M'), h(M), h(M'')$ are defined, so is the third, and $h(M) = h(M')h(M'')$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 3.6, p. 81"]
theorem prop_3_6 [IsCyclic G] {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact) :
    ((HerbrandDefined S.X₁ → HerbrandDefined S.X₂ → HerbrandDefined S.X₃) ∧
      (HerbrandDefined S.X₁ → HerbrandDefined S.X₃ → HerbrandDefined S.X₂) ∧
      (HerbrandDefined S.X₂ → HerbrandDefined S.X₃ → HerbrandDefined S.X₁)) ∧
    (HerbrandDefined S.X₁ → HerbrandDefined S.X₂ → HerbrandDefined S.X₃ →
      herbrandQuotient S.X₂ = herbrandQuotient S.X₁ * herbrandQuotient S.X₃) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  set P1 := periodicity g hg S.X₁ 0
  set P2 := periodicity g hg S.X₂ 0
  have nat := periodicity_naturality g hg S.f 0
  have nat' : ∀ x, ((tateCohomologyFunctor (0 + 2)).map S.f).hom (P1.hom.hom x) =
      P2.hom.hom (((tateCohomologyFunctor 0).map S.f).hom x) := fun x => by
    have := congrArg (fun φ => φ.hom x) nat
    simpa using this
  have hi : ∀ z, P1.hom.hom (P1.inv.hom z) = z := fun z => by
    have := congrArg (fun φ => φ.hom z) P1.inv_hom_id
    simpa using this
  have hi' : ∀ z, P1.inv.hom (P1.hom.hom z) = z := fun z => by
    have := congrArg (fun φ => φ.hom z) P1.hom_inv_id
    simpa using this
  have hi2' : ∀ z, P2.inv.hom (P2.hom.hom z) = z := fun z => by
    have := congrArg (fun φ => φ.hom z) P2.hom_inv_id
    simpa using this
  let f6 : tateCohomology S.X₃ 1 →ₗ[ℤ] tateCohomology S.X₁ 0 :=
    P1.inv.hom ∘ₗ (TateCohomology.δ hS 1).hom
  have e1 : Function.Exact f6 ((tateCohomologyFunctor 0).map S.f).hom := by
    have ex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (TateCohomology.exact₁ hS 1)
    intro x
    constructor
    · intro hx
      have h0 : ((tateCohomologyFunctor (0 + 2)).map S.f).hom (P1.hom.hom x) = 0 := by
        rw [nat', hx]; simp
      obtain ⟨y, hy⟩ := (ex _).1 h0
      refine ⟨y, ?_⟩
      show P1.inv.hom ((TateCohomology.δ hS 1).hom y) = x
      rw [show (TateCohomology.δ hS 1).hom y = P1.hom.hom x from hy]
      exact hi' x
    · rintro ⟨y, rfl⟩
      have h1 : ((tateCohomologyFunctor (0 + 2)).map S.f).hom ((TateCohomology.δ hS 1).hom y) = 0 := by
        have := congrArg (fun φ => φ.hom y) (TateCohomology.δ_map hS 1)
        simpa using this
      have h2 : P2.hom.hom (((tateCohomologyFunctor 0).map S.f).hom (f6 y)) = 0 := by
        rw [← nat']
        show ((tateCohomologyFunctor (0 + 2)).map S.f).hom (P1.hom.hom (P1.inv.hom _)) = 0
        rw [hi]; exact h1
      have := congrArg P2.inv.hom h2
      rw [hi2'] at this
      simpa using this
  have e6 : Function.Exact ((tateCohomologyFunctor 1).map S.g).hom f6 := by
    have ex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (TateCohomology.exact₃ hS 1)
    intro y
    rw [← ex y]
    show P1.inv.hom ((TateCohomology.δ hS 1).hom y) = 0 ↔ _
    constructor
    · intro h
      have := congrArg P1.hom.hom h
      rw [hi] at this
      simpa using this
    · intro h
      rw [h]; simp
  have e2 : Function.Exact ((tateCohomologyFunctor 0).map S.f).hom ((tateCohomologyFunctor 0).map S.g).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 ((TateCohomology.map_tateComplexFunctor_shortExact hS).homology_exact₂ 0)
  have e5 : Function.Exact ((tateCohomologyFunctor 1).map S.f).hom ((tateCohomologyFunctor 1).map S.g).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 ((TateCohomology.map_tateComplexFunctor_shortExact hS).homology_exact₂ 1)
  have e3 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (TateCohomology.exact₃ hS 0)
  have e4 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (TateCohomology.exact₁ hS 0)
  have H := hexagon ((tateCohomologyFunctor 0).map S.f).hom.toAddMonoidHom
    ((tateCohomologyFunctor 0).map S.g).hom.toAddMonoidHom
    (TateCohomology.δ hS 0).hom.toAddMonoidHom
    ((tateCohomologyFunctor 1).map S.f).hom.toAddMonoidHom
    ((tateCohomologyFunctor 1).map S.g).hom.toAddMonoidHom f6.toAddMonoidHom e1 e2 e3 e4 e5 e6
  unfold HerbrandDefined herbrandQuotient
  obtain ⟨⟨H1, H2, H3⟩, H4⟩ := H
  refine ⟨⟨fun a b => ?_, fun a b => ?_, fun a b => ?_⟩, fun a b c => ?_⟩
  · exact H1 a b
  · exact H2 a b
  · exact H3 a b
  · exact H4 a b c

/-- **Proposition 3.8** (p. 82). If $M$ is finite, then $h(M)$ is defined and $h(M) = 1$ ($G$ finite cyclic). -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 3.8, p. 82"]
theorem prop_3_8 [IsCyclic G] (M : Rep ℤ G) [Finite M] :
    HerbrandDefined M ∧ herbrandQuotient M = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨f1, f2, hc⟩ := @herbrand_core G IsCyclic.commGroup _ g hg M _
  let e1 := (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M
  let e0 := periodicity g hg M 0 ≪≫ (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 2).app M
  have c1 : Nat.card (tateCohomology M 1) = Nat.card (groupCohomology M 1) :=
    Nat.card_congr e1.toLinearEquiv.toEquiv
  have c0 : Nat.card (tateCohomology M 0) = Nat.card (groupCohomology M 2) :=
    Nat.card_congr e0.toLinearEquiv.toEquiv
  have fin1 : Finite (tateCohomology M 1) := @Finite.of_equiv _ _ f1 e1.toLinearEquiv.toEquiv.symm
  have fin0 : Finite (tateCohomology M 0) := @Finite.of_equiv _ _ f2 e0.toLinearEquiv.toEquiv.symm
  refine ⟨⟨fin0, fin1⟩, ?_⟩
  unfold herbrandQuotient
  rw [c0, c1, hc]
  have : 0 < Nat.card (groupCohomology M 2) := Nat.card_pos
  have : (Nat.card (groupCohomology M 2) : ℚ) ≠ 0 := by positivity
  field_simp

omit [Fintype G] in
lemma rep_exact_function {S : ShortComplex (Rep ℤ G)} (h : S.Exact) :
    Function.Exact S.f.hom S.g.hom := by
  have := h.map (forget₂ (Rep ℤ G) (ModuleCat ℤ))
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 this

/-- **Corollary 3.9** (p. 82). Let $\alpha : M \to N$ be a homomorphism of modules over a finite cyclic group with
finite kernel and cokernel. If either $h(M)$ or $h(N)$ is defined, then so is the other, and they are equal. -/
@[kb "milne2020cft" "v4.03, Ch. II, Cor. 3.9, p. 82"]
theorem cor_3_9 [IsCyclic G] {M N : Rep ℤ G} (α : M ⟶ N) (hker : Finite (LinearMap.ker α.hom.toLinearMap))
    (hcoker : Finite (N ⧸ LinearMap.range α.hom.toLinearMap)) :
    (HerbrandDefined M ↔ HerbrandDefined N) ∧
      (HerbrandDefined M → herbrandQuotient M = herbrandQuotient N) := by
  let e := factorThruImage α
  let ι := image.ι α
  have fac' : ∀ x, ι.hom (e.hom x) = α.hom x := fun x => by
    exact congrArg (fun φ => φ.hom x) (image.fac α)
  let K : Rep ℤ G := kernel e
  let C : Rep ℤ G := cokernel ι
  let Sa : ShortComplex (Rep ℤ G) := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  let Sb : ShortComplex (Rep ℤ G) := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hSa : Sa.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel e) inferInstance inferInstance
  have hSb : Sb.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel ι) inferInstance inferInstance
  have exa := rep_exact_function (ShortComplex.exact_kernel e)
  have exb := rep_exact_function (ShortComplex.exact_cokernel ι)
  have hιinj : Function.Injective ι.hom := (Rep.mono_iff_injective ι).1 inferInstance
  have hKinj : Function.Injective (kernel.ι e).hom := (Rep.mono_iff_injective _).1 inferInstance
  have hesurj : Function.Surjective e.hom := (Rep.epi_iff_surjective e).1 inferInstance
  have hπsurj : Function.Surjective (cokernel.π ι).hom := (Rep.epi_iff_surjective _).1 inferInstance
  have finK : Finite (K : Rep ℤ G) := by
    refine Finite.of_injective (β := LinearMap.ker α.hom.toLinearMap)
      (fun x => ⟨(kernel.ι e).hom x, ?_⟩) ?_
    · have h0 : e.hom ((kernel.ι e).hom x) = 0 := (exa _).2 ⟨x, rfl⟩
      show α.hom _ = 0
      rw [← fac', h0]; simp
    · intro x y hxy
      exact hKinj (congrArg Subtype.val hxy)
  have finC : Finite (C : Rep ℤ G) := by
    have hle : LinearMap.range α.hom.toLinearMap ≤ LinearMap.ker (cokernel.π ι).hom.toLinearMap := by
      rintro _ ⟨x, rfl⟩
      show (cokernel.π ι).hom (α.hom x) = 0
      rw [← fac']
      exact (exb _).2 ⟨_, rfl⟩
    refine Finite.of_surjective
      ((LinearMap.range α.hom.toLinearMap).liftQ (cokernel.π ι).hom.toLinearMap hle) ?_
    intro c
    obtain ⟨n, rfl⟩ := hπsurj c
    exact ⟨Submodule.Quotient.mk n, rfl⟩
  obtain ⟨dK, qK⟩ := prop_3_8 K
  obtain ⟨dC, qC⟩ := prop_3_8 C
  have ha := prop_3_6 hSa
  have hb := prop_3_6 hSb
  have fwd : HerbrandDefined M → HerbrandDefined (image α) := fun hM => ha.1.1 dK hM
  have bwd : HerbrandDefined (image α) → HerbrandDefined M := fun hI => ha.1.2.1 dK hI
  have fwd2 : HerbrandDefined (image α) → HerbrandDefined N := fun hI => hb.1.2.1 hI dC
  have bwd2 : HerbrandDefined N → HerbrandDefined (image α) := fun hN => hb.1.2.2 hN dC
  refine ⟨⟨fun hM => fwd2 (fwd hM), fun hN => bwd (bwd2 hN)⟩, fun hM => ?_⟩
  have hI := fwd hM
  have hN := fwd2 hI
  have e1 := ha.2 dK hM hI
  have e2 := hb.2 hI hN dC
  rw [e1, e2, qK, qC]
  simp
  rfl

end Herbrand

end NumberFieldKB.MilneCFT
