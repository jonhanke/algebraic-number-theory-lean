import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Class Field Theory*, Chapter II: the axiomatic characterization of (co)homology

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Milne characterizes the cohomology functors $H^r(G, -)$ with their connecting maps by the properties 1.6
($H^0 = (-)^G$), 1.7 (vanishing on injectives in positive degrees) and 1.9 (functorial long exact sequences)
(Remark 1.10), the homology functors dually (Remark 2.5), and right derived functors in general (Remark A.12).
Mathlib has neither $\delta$-functors nor this universal property, so we define cohomological and homological
$\delta$-functors and record the three remarks as named statements.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

section Delta

variable (C : Type u₁) [Category.{v₁} C] [Abelian C] (D : Type u₂) [Category.{v₂} D] [Abelian D]

/-- A **cohomological $\delta$-functor** $C \to D$ (the structure of properties 1.9 and A.11, p. 61, p. 94): additive
functors $T^r$, $r \ge 0$, and for each short exact sequence $0 \to A \to B \to C \to 0$ connecting maps
$\delta^r : T^r(C) \to T^{r+1}(A)$, such that $0 \to T^0(A) \to T^0(B) \to T^0(C) \to T^1(A) \to \cdots$ is exact
and the connecting maps are natural in morphisms of short exact sequences. -/
@[kb "milne2020cft" "v4.03, Ch. II, 1.9 and Prop. A.11 (δ-functors), p. 61, p. 94"]
structure CohomDeltaFunctor where
  /-- The functors $T^r$. -/
  T : ℕ → C ⥤ D
  additive : ∀ n, (T n).Additive
  /-- The connecting maps. -/
  δ : ∀ (S : ShortComplex C), S.ShortExact → ∀ n : ℕ, (T n).obj S.X₃ ⟶ (T (n + 1)).obj S.X₁
  comp_δ : ∀ S hS n, (T n).map S.g ≫ δ S hS n = 0
  δ_comp : ∀ S hS n, δ S hS n ≫ (T (n + 1)).map S.f = 0
  mono₀ : ∀ (S : ShortComplex C), S.ShortExact → Mono ((T 0).map S.f)
  exact₂ : ∀ (S : ShortComplex C), S.ShortExact → ∀ n, (S.map (T n)).Exact
  exact₃ : ∀ S hS n, (ShortComplex.mk _ _ (comp_δ S hS n)).Exact
  exact₁ : ∀ S hS n, (ShortComplex.mk _ _ (δ_comp S hS n)).Exact
  naturality : ∀ (S₁ S₂ : ShortComplex C) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ),
    δ S₁ h₁ n ≫ (T (n + 1)).map φ.τ₁ = (T n).map φ.τ₃ ≫ δ S₂ h₂ n

attribute [instance] CohomDeltaFunctor.additive

/-- A **homological $\delta$-functor** $C \to D$ (property 2.4, p. 66): additive functors $T_r$, $r \ge 0$, and
connecting maps $\delta_r : T_{r+1}(C) \to T_r(A)$ for short exact sequences $0 \to A \to B \to C \to 0$, with
$\cdots \to T_1(C) \to T_0(A) \to T_0(B) \to T_0(C) \to 0$ exact and natural connecting maps. -/
@[kb "milne2020cft" "v4.03, Ch. II, 2.4 (homological δ-functors), p. 66"]
structure HomDeltaFunctor where
  /-- The functors $T_r$. -/
  T : ℕ → C ⥤ D
  additive : ∀ n, (T n).Additive
  /-- The connecting maps. -/
  δ : ∀ (S : ShortComplex C), S.ShortExact → ∀ n : ℕ, (T (n + 1)).obj S.X₃ ⟶ (T n).obj S.X₁
  comp_δ : ∀ S hS n, (T (n + 1)).map S.g ≫ δ S hS n = 0
  δ_comp : ∀ S hS n, δ S hS n ≫ (T n).map S.f = 0
  epi₀ : ∀ (S : ShortComplex C), S.ShortExact → Epi ((T 0).map S.g)
  exact₂ : ∀ (S : ShortComplex C), S.ShortExact → ∀ n, (S.map (T n)).Exact
  exact₃ : ∀ S hS n, (ShortComplex.mk _ _ (comp_δ S hS n)).Exact
  exact₁ : ∀ S hS n, (ShortComplex.mk _ _ (δ_comp S hS n)).Exact
  naturality : ∀ (S₁ S₂ : ShortComplex C) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ),
    δ S₁ h₁ n ≫ (T n).map φ.τ₁ = (T (n + 1)).map φ.τ₃ ≫ δ S₂ h₂ n

attribute [instance] HomDeltaFunctor.additive

variable {C D}

/-- An isomorphism of cohomological $\delta$-functors: natural isomorphisms $T_1^r \simeq T_2^r$ commuting with the
connecting maps. -/
def CohomDeltaFunctor.IsDeltaIso (T₁ T₂ : CohomDeltaFunctor C D) (φ : ∀ n, T₁.T n ≅ T₂.T n) : Prop :=
  ∀ (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ),
    T₁.δ S hS n ≫ (φ (n + 1)).hom.app S.X₁ = (φ n).hom.app S.X₃ ≫ T₂.δ S hS n

/-- An isomorphism of homological $\delta$-functors. -/
def HomDeltaFunctor.IsDeltaIso (T₁ T₂ : HomDeltaFunctor C D) (φ : ∀ n, T₁.T n ≅ T₂.T n) : Prop :=
  ∀ (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ),
    T₁.δ S hS n ≫ (φ n).hom.app S.X₁ = (φ (n + 1)).hom.app S.X₃ ≫ T₂.δ S hS n

/-- Effaceability: $T^r(I) = 0$ for $r > 0$ and $I$ injective (property 1.7, A.12 (b)). -/
def CohomDeltaFunctor.Effaceable (T : CohomDeltaFunctor C D) : Prop :=
  ∀ (I : C), Injective I → ∀ n : ℕ, 0 < n → IsZero ((T.T n).obj I)

/-- Coeffaceability: $T_r(P) = 0$ for $r > 0$ and $P$ projective (property 2.2). -/
def HomDeltaFunctor.Coeffaceable (T : HomDeltaFunctor C D) : Prop :=
  ∀ (P : C), Projective P → ∀ n : ℕ, 0 < n → IsZero ((T.T n).obj P)

end Delta

/-- **Remark A.12** (p. 95), as a named statement. Let $C$ be an abelian category with enough injectives and
$F : C \to D$ a functor. The right derived functors of $F$ are characterized up to unique isomorphism by
(a) $R^0F = F$, (b) $R^rF(I) = 0$ for $r > 0$ and $I$ injective, (c) the long exact sequences of A.11: for any two
cohomological $\delta$-functors $T_1, T_2$ with $e_i : T_i^0 \simeq F$ satisfying (b), there is a unique
isomorphism of $\delta$-functors $T_1 \simeq T_2$ which is $e_2^{-1} \circ e_1$ in degree $0$. Stated for categories
with objects in `Type 1` and morphisms in `Type` (this covers `Rep ℤ G` and `ModuleCat ℤ`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark A.12, p. 95"]
structure RemarkA_12 : Prop where
  unique : ∀ (C : Type 1) [Category.{0} C] [Abelian C] [EnoughInjectives C] (D : Type 1) [Category.{0} D]
    [Abelian D] (F : C ⥤ D) (T₁ T₂ : CohomDeltaFunctor C D) (e₁ : T₁.T 0 ≅ F) (e₂ : T₂.T 0 ≅ F),
    T₁.Effaceable → T₂.Effaceable →
    ∃! φ : ∀ n, T₁.T n ≅ T₂.T n, φ 0 = e₁ ≪≫ e₂.symm ∧ T₁.IsDeltaIso T₂ φ

/-- **Proposition A.11** (p. 94–95), as a named statement. Let $C$ be an abelian category with enough injectives
(injective resolutions) and $F : C \to D$ a left exact additive functor. A short exact sequence
$0 \to A \to B \to C \to 0$ gives rise to a long exact sequence
$0 \to F(A) \to F(B) \to F(C) \to R^1F(A) \to \cdots \to R^rF(A) \to R^rF(B) \to R^rF(C) \to \cdots$, functorially
in the short exact sequence: the right derived functors (Mathlib's `Functor.rightDerived`) are the functors of a
cohomological $\delta$-functor. Milne refers to Bucur–Deleanu 7.6. Stated with the universes of `RemarkA_12`. -/
@[kb "milne2020cft" "v4.03, Ch. II, App. A, Prop. A.11, p. 94–95"]
structure PropA_11 : Prop where
  exists_delta : ∀ (C : Type 1) [Category.{0} C] [Abelian C] [HasInjectiveResolutions C] (D : Type 1)
    [Category.{0} D] [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F],
    ∃ T : CohomDeltaFunctor C D, Nonempty (∀ n, T.T n ≅ F.rightDerived n)

/-- **Remark 1.10** (p. 61), as a named statement. The cohomology functors $H^r(G, -)$ with their connecting maps
are uniquely determined by 1.6 ($H^0(G, M) = M^G$), 1.7 (vanishing on injectives for $r > 0$) and 1.9 (long exact
sequences): any two cohomological $\delta$-functors `Rep ℤ G ⥤ ModuleCat ℤ` with these properties are
isomorphic by a unique isomorphism of $\delta$-functors compatible with the identifications in degree $0$. (Mathlib's
`groupCohomology.functor` with `groupCohomology.δ` is one of them.) -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.10, p. 61"]
structure Remark1_10 : Prop where
  unique : ∀ (G : Type) [Group G] (T₁ T₂ : CohomDeltaFunctor (Rep.{0} ℤ G) (ModuleCat.{0} ℤ))
    (e₁ : T₁.T 0 ≅ Rep.invariantsFunctor ℤ G) (e₂ : T₂.T 0 ≅ Rep.invariantsFunctor ℤ G),
    T₁.Effaceable → T₂.Effaceable →
    ∃! φ : ∀ n, T₁.T n ≅ T₂.T n, φ 0 = e₁ ≪≫ e₂.symm ∧ T₁.IsDeltaIso T₂ φ

/-- **Proposition 1.5** (p. 60): the category of $G$-modules has enough injectives. Transported from Mathlib's
`ModuleCat` instance along `Rep.equivalenceModuleMonoidAlgebra` (Remark 1.1). -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.5, p. 60"]
theorem prop_1_5 (G : Type) [Group G] : EnoughInjectives (Rep.{0} ℤ G) :=
  EnoughInjectives.of_equivalence (Rep.equivalenceModuleMonoidAlgebra (k := ℤ) (G := G)).functor

/-- Remark 1.10 is the case $C = $ `Rep ℤ G`, $F = (-)^G$ of Remark A.12 (with Proposition 1.5). -/
theorem remark_1_10_of_remarkA_12 (h : RemarkA_12) : Remark1_10 :=
  ⟨fun G _ T₁ T₂ e₁ e₂ h₁ h₂ => by
    have := prop_1_5 G
    exact h.unique (Rep.{0} ℤ G) (ModuleCat.{0} ℤ) _ T₁ T₂ e₁ e₂ h₁ h₂⟩

/-- **Remark 2.5** (p. 67), as a named statement. The homology functors $H_r(G, -)$ with their connecting maps are
uniquely determined by 2.1 ($H_0(G, M) = M_G$), 2.2 (vanishing on projectives for $r > 0$) and 2.4 (long exact
sequences). (Mathlib's `groupHomology.functor` with `groupHomology.δ` is one such $\delta$-functor.) -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 2.5, p. 67"]
structure Remark2_5 : Prop where
  unique : ∀ (G : Type) [Group G] (T₁ T₂ : HomDeltaFunctor (Rep.{0} ℤ G) (ModuleCat.{0} ℤ))
    (e₁ : T₁.T 0 ≅ Rep.coinvariantsFunctor ℤ G) (e₂ : T₂.T 0 ≅ Rep.coinvariantsFunctor ℤ G),
    T₁.Coeffaceable → T₂.Coeffaceable →
    ∃! φ : ∀ n, T₁.T n ≅ T₂.T n, φ 0 = e₁ ≪≫ e₂.symm ∧ T₁.IsDeltaIso T₂ φ

end NumberFieldKB.MilneCFT
