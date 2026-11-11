import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import QuadFormsKB.Citation

/-!
# Milne, *Class Field Theory*, Chapter II §1: cochains, products, normalized cocycles

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Milne defines $H^r(G, M)$ as the derived functors of $M \mapsto M^G$ and proves (Proposition 1.17) that it is
computed by inhomogeneous cochains; Mathlib's `groupCohomology` is defined by inhomogeneous cochains. The
$G$-modules are Mathlib's `Rep ℤ G`.

* Remark 1.19 (normalized 2-cocycles) and Proposition 1.25 (cohomology commutes with products) are proved.
* Remark 1.10 (the cohomology functors are a universal $\delta$-functor) and Remark 1.14 (acyclic resolutions
  compute cohomology) are recorded as named statements.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits

variable {G : Type} [Group G]

/-! ## Remark 1.19: normalized 2-cocycles -/

/-- **Remark 1.19** (p. 66), the computation: for $m \in M$ let $\varphi_m : G \to M$ be the constant map
$\sigma \mapsto m$; then $(d^1\varphi_m)(\sigma, \tau) = \sigma m - m + m = \sigma m$, in particular
$(d^1\varphi_m)(1, 1) = m$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.19, p. 66"]
theorem remark_1_19_d (M : Rep ℤ G) (m : M) (σ τ : G) :
    (d₁₂ M).hom (fun _ => m) (σ, τ) = M.ρ σ m := by
  simp

/-- **Remark 1.19** (p. 66): every class in $H^2(G, M)$ is represented by a normalized 2-cocycle, that is, a
2-cocycle $\varphi$ with $\varphi(1, 1) = 0$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.19, p. 66"]
theorem remark_1_19 (M : Rep ℤ G) (x : H2 M) :
    ∃ φ : cocycles₂ M, H2π M φ = x ∧ (φ : G × G → M) (1, 1) = 0 := by
  induction x using H2_induction_on with
  | h f =>
    set m : M := (f : G × G → M) (1, 1)
    have hd : (d₁₂ M).hom (fun _ => m) ∈ coboundaries₂ M := ⟨fun _ => m, rfl⟩
    refine ⟨f - ⟨(d₁₂ M).hom (fun _ => m), coboundaries₂_le_cocycles₂ M hd⟩, ?_, ?_⟩
    · rw [map_sub, sub_eq_self, H2π_eq_zero_iff]
      exact hd
    · change (f : G × G → M) (1, 1) - (d₁₂ M).hom (fun _ => m) (1, 1) = 0
      rw [remark_1_19_d]
      simp [m]

/-! ## Proposition 1.25: cohomology of products -/

set_option backward.isDefEq.respectTransparency false in
/-- $H^r(G, -)$ is an additive functor. -/
instance functor_additive (r : ℕ) : (functor ℤ G r).Additive where
  map_add {X Y f g} := by
    change HomologicalComplex.homologyMap ((cochainsFunctor ℤ G).map (f + g)) r =
      HomologicalComplex.homologyMap ((cochainsFunctor ℤ G).map f) r +
        HomologicalComplex.homologyMap ((cochainsFunctor ℤ G).map g) r
    rw [(cochainsFunctor ℤ G).map_add, HomologicalComplex.homologyMap_add]

section ProductHelpers

universe u v

/-- The family of short complexes `T j`, viewed as a short complex in `Discrete ι ⥤ C`. -/
noncomputable def famSC {C : Type u} [Category.{v} C] [Abelian C] {ι : Type}
    (T : ι → ShortComplex C) : ShortComplex (Discrete ι ⥤ C) where
  X₁ := Discrete.functor fun j => (T j).X₁
  X₂ := Discrete.functor fun j => (T j).X₂
  X₃ := Discrete.functor fun j => (T j).X₃
  f := Discrete.natTrans fun j => (T j.as).f
  g := Discrete.natTrans fun j => (T j.as).g
  zero := by ext ⟨j⟩; exact (T j).zero

/-- In an abelian category with exact products, homology commutes with products of short complexes. -/
theorem isIso_lift_homologyMap {C : Type u} [Category.{v} C] [Abelian C] {ι : Type}
    [HasProductsOfShape ι C] [HasExactLimitsOfShape (Discrete ι) C]
    (S : ShortComplex C) (T : ι → ShortComplex C) (p : ∀ j, S ⟶ T j)
    (h₁ : IsIso (Pi.lift fun j => (p j).τ₁)) (h₂ : IsIso (Pi.lift fun j => (p j).τ₂))
    (h₃ : IsIso (Pi.lift fun j => (p j).τ₃)) :
    IsIso (Pi.lift fun j => ShortComplex.homologyMap (p j) :
      S.homology ⟶ ∏ᶜ fun j => (T j).homology) := by
  let T' := famSC T
  let u : S ⟶ T'.map lim :=
    { τ₁ := Pi.lift fun j => (p j).τ₁
      τ₂ := Pi.lift fun j => (p j).τ₂
      τ₃ := Pi.lift fun j => (p j).τ₃
      comm₁₂ := by
        apply Pi.hom_ext; intro j
        simp [T', famSC]
        have a := Pi.lift_comp_π (fun j => (p j).τ₁) j
        have b := Pi.lift_comp_π (fun j => (p j).τ₂) j
        erw [← Category.assoc, a, b]
        exact (p j).comm₁₂
      comm₂₃ := by
        apply Pi.hom_ext; intro j
        simp [T', famSC]
        have a := Pi.lift_comp_π (fun j => (p j).τ₂) j
        have b := Pi.lift_comp_π (fun j => (p j).τ₃) j
        erw [← Category.assoc, a, b]
        exact (p j).comm₂₃ }
  have : IsIso u.τ₁ := h₁
  have : IsIso u.τ₂ := h₂
  have : IsIso u.τ₃ := h₃
  have hu : IsIso u := ShortComplex.isIso_of_isIso u
  have key : ∀ j, p j = u ≫ T'.mapNatTrans (lim.π (C := C) ⟨j⟩) := by
    intro j
    ext
    · exact (Pi.lift_comp_π (fun j => (p j).τ₁) j).symm
    · exact (Pi.lift_comp_π (fun j => (p j).τ₂) j).symm
    · exact (Pi.lift_comp_π (fun j => (p j).τ₃) j).symm
  let e := T'.mapHomologyIso (lim (J := Discrete ι) (C := C))
  let gi : ∀ j : ι, T'.homology.obj ⟨j⟩ ≅ (T j).homology := fun j =>
    (T'.mapHomologyIso ((evaluation (Discrete ι) C).obj ⟨j⟩)).symm
  let g : ∀ j : ι, T'.homology.obj ⟨j⟩ ⟶ (T j).homology := fun j => (gi j).hom
  have hH : ∀ j, ShortComplex.homologyMap (p j) = ShortComplex.homologyMap u ≫ e.hom ≫
      limit.π T'.homology ⟨j⟩ ≫ g j := by
    intro j
    rw [key j]
    erw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_mapNatTrans]
    rfl
  have h1 : Pi.lift (fun j => ShortComplex.homologyMap (p j)) = ShortComplex.homologyMap u ≫
      e.hom ≫ (Pi.lift fun j => limit.π T'.homology ⟨j⟩) ≫ Limits.Pi.map g := by
    apply Pi.hom_ext; intro j
    simp only [Category.assoc, Pi.lift_comp_π, hH]
    erw [Pi.map_π, Pi.lift_comp_π_assoc]
  have h2 : (Pi.lift fun j => limit.π T'.homology ⟨j⟩) =
      (HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := T'.homology))).hom := by
    apply Pi.hom_ext; intro j
    simp
    erw [HasLimit.isoOfNatIso_hom_π]
    simp [Discrete.natIsoFunctor]
  have hL : IsIso (Pi.lift fun j => limit.π T'.homology ⟨j⟩) := by
    rw [h2]; infer_instance
  rw [h1]
  have : IsIso (ShortComplex.homologyMap u) := inferInstance
  have : IsIso e.hom := inferInstance
  have : IsIso (Limits.Pi.map g) := inferInstanceAs (IsIso (Limits.Pi.mapIso gi).hom)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
    (@IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hL inferInstance))

/-- Elements of a product under a product-preserving functor to `Type` are families. -/
theorem pi_elem_bij {ι : Type} {D : Type*} [Category D] [HasProductsOfShape ι D]
    (M : ι → D) (U : D ⥤ Type) [PreservesLimit (Discrete.functor M) U] :
    Function.Bijective (fun x : U.obj (∏ᶜ M) => fun j => U.map (Pi.π M j) x) := by
  have : IsIso (piComparison U M) := inferInstance
  have h : Function.Bijective
      (piComparison U M ≫ (Types.productIso (fun j => U.obj (M j))).hom) :=
    (isIso_iff_bijective _).1 inferInstance
  convert h using 1
  funext x j
  have h1 := ConcreteCategory.congr_hom (Types.productIso_hom_comp_eval (fun j => U.obj (M j)) j)
    (piComparison U M x)
  have h2 := ConcreteCategory.congr_hom (piComparison_comp_π U M j) x
  simp only [ConcreteCategory.comp_apply] at h1 h2 ⊢
  exact h2.symm.trans h1.symm

/-- The cochains of a product of `G`-modules are the product of the cochains, degreewise. -/
theorem cochains_pi_isIso {ι : Type} (M : ι → Rep ℤ G) (k : ℕ) :
    IsIso (Pi.lift fun j => ((cochainsFunctor ℤ G).map (Pi.π M j)).f k) := by
  let UR : Rep ℤ G ⥤ Type := forget₂ (Rep ℤ G) (ModuleCat ℤ) ⋙ forget (ModuleCat ℤ)
  have hR : Function.Bijective (fun x : UR.obj (∏ᶜ M) => fun j => UR.map (Pi.π M j) x) :=
    pi_elem_bij M UR
  have hQ := pi_elem_bij (fun j => (inhomogeneousCochains (M j)).X k) (forget (ModuleCat ℤ))
  rw [ConcreteCategory.isIso_iff_bijective]
  refine (Function.Bijective.of_comp_iff' hQ _).1 ?_
  have hcomp : ((fun y => fun j => (forget (ModuleCat ℤ)).map
      (Pi.π (fun j => (inhomogeneousCochains (M j)).X k) j) y) ∘
      ⇑(ConcreteCategory.hom (Pi.lift fun j => ((cochainsFunctor ℤ G).map (Pi.π M j)).f k))) =
      fun x => fun j σ => UR.map (Pi.π M j) (x σ) := by
    funext x j
    have := ConcreteCategory.congr_hom (Pi.lift_comp_π
      (fun j => ((cochainsFunctor ℤ G).map (Pi.π M j)).f k) j) x
    exact this
  rw [hcomp]
  obtain ⟨hinj, hsurj⟩ := hR
  constructor
  · intro x y hxy
    funext σ
    apply hinj
    funext j
    exact congrFun (congrFun hxy j) σ
  · intro g
    choose f hf using fun σ => hsurj (fun j => g j σ)
    refine ⟨f, ?_⟩
    funext j σ
    exact congrFun (hf σ) j

end ProductHelpers

/-- **Proposition 1.25** (p. 68). For every family $(M_i)_{i \in I}$ of $G$-modules,
$H^r(G, \prod_i M_i) \simeq \prod_i H^r(G, M_i)$: the map induced by the projections is an isomorphism. The product
$\prod_i M_i$ (diagonal action) is the categorical product in `Rep ℤ G`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.25, p. 68"]
theorem prop_1_25 {ι : Type} (M : ι → Rep ℤ G) (r : ℕ) :
    IsIso (Pi.lift fun i => (functor ℤ G r).map (Pi.π M i) :
      groupCohomology (∏ᶜ M) r ⟶ ∏ᶜ fun i => groupCohomology (M i) r) := by
  exact isIso_lift_homologyMap
    ((HomologicalComplex.shortComplexFunctor _ _ r).obj ((cochainsFunctor ℤ G).obj (∏ᶜ M)))
    (fun i => (HomologicalComplex.shortComplexFunctor _ _ r).obj ((cochainsFunctor ℤ G).obj (M i)))
    (fun i => (HomologicalComplex.shortComplexFunctor _ _ r).map
      ((cochainsFunctor ℤ G).map (Pi.π M i)))
    (cochains_pi_isIso M _) (cochains_pi_isIso M _) (cochains_pi_isIso M _)

/-- **Proposition 1.25**, the special case of a direct sum of two modules (p. 68):
$H^r(G, M \oplus N) = H^r(G, M) \oplus H^r(G, N)$. As Milne notes, this follows directly from the additivity of
$H^r(G, -)$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.25 (direct sums), p. 68"]
theorem prop_1_25_biprod (M N : Rep ℤ G) (r : ℕ) :
    IsIso (biprod.lift ((functor ℤ G r).map biprod.fst) ((functor ℤ G r).map biprod.snd) :
      groupCohomology (M ⊞ N) r ⟶ groupCohomology M r ⊞ groupCohomology N r) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts (functor ℤ G r)
  have h : IsIso ((functor ℤ G r).mapBiprod M N).hom := inferInstance
  rw [Functor.mapBiprod_hom] at h
  exact h

/-! ## Remark 1.14: acyclic resolutions -/

/-- **Remark 1.14** (p. 63), as a named statement. Let $0 \to M \xrightarrow{\varepsilon} J^0 \to J^1 \to \cdots$
be an exact sequence of $G$-modules with $H^s(G, J^r) = 0$ for all $s > 0$ and all $r$. Then
$H^r(G, M) \simeq H^r((J^\bullet)^G)$ for all $r$. The resolution is a cochain complex `J` with an augmentation
`ε : M ⟶ J.X 0` such that `0 → M → J⁰ → J¹ → ⋯` is exact; $(J^\bullet)^G$ is `J` mapped by the invariants functor
`Rep.invariantsFunctor`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.14, p. 63"]
structure Remark1_14 : Prop where
  iso : ∀ (G : Type) [Group G] (M : Rep ℤ G) (J : CochainComplex (Rep ℤ G) ℕ) (ε : M ⟶ J.X 0),
    ∀ hε : ε ≫ J.d 0 1 = 0, Mono ε → (ShortComplex.mk ε (J.d 0 1) hε).Exact →
    (∀ n : ℕ, (J.sc (n + 1)).Exact) →
    (∀ r s : ℕ, 0 < s → IsZero (groupCohomology (J.X r) s)) →
    ∀ r : ℕ, Nonempty (groupCohomology M r ≅
      (((Rep.invariantsFunctor ℤ G).mapHomologicalComplex _).obj J).homology r)

end NumberFieldKB.MilneCFT
