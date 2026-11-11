import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import QuadFormsKB.Citation
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Milne, Class Field Theory, Chapter II: results in Mathlib

Chapter II ("Cohomology") of J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography
key `milne2020cft`) treats group cohomology.  This file cites the items of that chapter, and of its
appendix on homological algebra, which are already available in Mathlib.

Convention.
* When one Mathlib declaration states the book's item in essentially the book's form, the
  declaration is tagged directly with `attribute [kb "milne2020cft" ...]`, with a comment saying
  which item it is and how the form differs.
* When the book's form differs, a short restating theorem in the book's form is proved from the
  Mathlib results, and that theorem carries the tag.
* A $G$-module is a `Rep ℤ G`.  The page in each locator is the printed page of the book.
* Mathlib's `Rep k G` is a structure whose cohomology `groupCohomology A n` is a `ModuleCat k`;
  for $k = ℤ$ this is the abelian group $H^n(G, A)$ of the book.
-/

open CategoryTheory

namespace NumberFieldKB.MilneCFT

/-! ### Section 1: definitions and basic properties -/

-- Definition of a $G$-module and of a $G$-homomorphism (p. 57): a $G$-module is `Rep ℤ G`, and
-- the $G$-homomorphisms are the morphisms `A ⟶ B` of `Rep ℤ G`.
attribute [kb "milne2020cft" "v4.03, Ch. II, §1, Def. of G-module, p. 57"] Rep

-- Trivial action (p. 57): `Rep.IsTrivial` is the property that every element of $G$ acts as the
-- identity, and `Rep.trivial` is the $G$-module with the trivial action on a given group.
attribute [kb "milne2020cft" "v4.03, Ch. II, §1, Def. of trivial action, p. 57"]
  Rep.IsTrivial Rep.trivial

-- Remark 1.1: $G$-modules are the same as $\mathbb{Z}[G]$-modules.  Mathlib states this as an
-- equivalence of categories `Rep k G ≌ ModuleCat (MonoidAlgebra k G)`, here for $k = ℤ$.
attribute [kb "milne2020cft" "v4.03, Ch. II, Rem. 1.1, p. 57"] Rep.equivalenceModuleMonoidAlgebra

-- Definition of $\mathrm{Ind}_H^G$ (p. 58): Milne's $\mathrm{Ind}_H^G N$ is the module of
-- $H$-equivariant functions $G \to N$, which is Mathlib's coinduced module `Rep.coind` (not the
-- induced module `Rep.ind`).  The function `Rep.coind φ` is taken for `φ = H.subtype`.
attribute [kb "milne2020cft" "v4.03, Ch. II, §1, Def. of Ind_H^G, p. 58"] Rep.coind

/-- Lemma 1.2 of Milne: for a subgroup $H$ of $G$, a $G$-module $M$ and an $H$-module $N$,
(a) $\mathrm{Hom}_H(M, N) \cong \mathrm{Hom}_G(M, \mathrm{Ind}_H^G N)$, and (b) the functor
$\mathrm{Ind}_H^G$ is exact.

Part (a) restates `Rep.resCoindHomEquiv`, where Milne's $\mathrm{Ind}_H^G$ is `Rep.coind H.subtype`
and the restriction is `Rep.res H.subtype`.  Part (b) is the preservation of short exact sequences
by `Rep.coindFunctor`, which is a right adjoint (so preserves finite limits) and preserves
epimorphisms along a subgroup. -/
@[kb "milne2020cft" "v4.03, Ch. II, Lem. 1.2, p. 58"]
theorem lemma_1_2 (G : Type) [Group G] (H : Subgroup G) :
    (∀ (M : Rep ℤ G) (N : Rep ℤ H),
      Nonempty ((Rep.res H.subtype M ⟶ N) ≃ (M ⟶ Rep.coind H.subtype N))) ∧
    (∀ S : ShortComplex (Rep ℤ H), S.ShortExact →
      (S.map (Rep.coindFunctor ℤ H.subtype)).ShortExact) := by
  refine ⟨fun M N => ⟨(Rep.resCoindHomEquiv H.subtype M N).toEquiv⟩, fun S hS => ?_⟩
  have := hS.mono_f
  have := hS.epi_g
  have : (Rep.coindFunctor ℤ H.subtype).PreservesZeroMorphisms := inferInstance
  have hF : Limits.PreservesLimit (Limits.parallelPair S.g 0) (Rep.coindFunctor ℤ H.subtype) :=
    inferInstance
  have hm : Mono ((Rep.coindFunctor ℤ H.subtype).map S.f) := inferInstance
  have he : Epi ((Rep.coindFunctor ℤ H.subtype).map S.g) := inferInstance
  exact { exact := hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f hF
          mono_f := hm
          epi_g := he }

-- Definition of an injective $G$-module (p. 60): an injective object of the category `Rep ℤ G`.
attribute [kb "milne2020cft" "v4.03, Ch. II, §1, Def. of injective G-module, p. 60"] Injective

-- Definition of the cohomology groups (pp. 60-61) as the right derived functors of
-- $M \mapsto M^G$, equivalently $H^n(G, M) = \mathrm{Ext}^n_{\mathbb{Z}[G]}(\mathbb{Z}, M)$.
-- Mathlib defines `groupCohomology` by the standard (bar) complex and proves the comparison with
-- $\mathrm{Ext}$ in `groupCohomologyIsoExt`; the comparison with the derived functor of
-- invariants is not cited here.
attribute [kb "milne2020cft" "v4.03, Ch. II, §1, Def. of cohomology groups, p. 60"]
  groupCohomology
attribute [kb "milne2020cft" "v4.03, Ch. II, §1, Def. of cohomology groups, p. 61"]
  groupCohomologyIsoExt

-- Proposition 1.11 (Shapiro's lemma): $H^n(G, \mathrm{Ind}_H^G N) \cong H^n(H, N)$.
attribute [kb "milne2020cft" "v4.03, Ch. II, Prop. 1.11, p. 62"] groupCohomology.coindIso

-- Lemma 1.15: the standard resolution of $\mathbb{Z}$ by free $\mathbb{Z}[G]$-modules is exact.
-- Mathlib states this as `QuasiIso` of the augmentation `εToSingle₀` from the standard complex
-- to the complex concentrated in degree $0$ at the trivial module (after forgetting to modules).
attribute [kb "milne2020cft" "v4.03, Ch. II, Lem. 1.15, p. 63"]
  Rep.standardComplex.quasiIso_forget₂_εToSingle₀

-- Proposition 1.16: $H^n(G, M)$ is computed by any projective resolution of the trivial module
-- $\mathbb{Z}$, as the cohomology of $\mathrm{Hom}_G(P_\bullet, M)$.
attribute [kb "milne2020cft" "v4.03, Ch. II, Prop. 1.16, p. 64"] groupCohomologyIso

-- Proposition 1.17: $H^n(G, M)$ is the cohomology of the complex of inhomogeneous cochains
-- $C^n(G, M) = \mathrm{Map}(G^n, M)$ with the usual differential.  The complex is
-- `groupCohomology.inhomogeneousCochains` (degree $n$ is `(Fin n → G) → M`, indices from $0$),
-- `d_comp_d` says $d \circ d = 0$, and `inhomogeneousCochainsIso` identifies it with
-- $\mathrm{Hom}_G(\text{bar resolution}, M)$.
attribute [kb "milne2020cft" "v4.03, Ch. II, Prop. 1.17, p. 64"]
  groupCohomology.inhomogeneousCochains groupCohomology.inhomogeneousCochains.d_comp_d
  groupCohomology.inhomogeneousCochainsIso

-- Example 1.18 (a): $H^1(G, M)$ is crossed homomorphisms modulo principal ones, and equals
-- $\mathrm{Hom}(G, M)$ for a trivial action.  `mem_cocycles₁_iff` is the crossed-homomorphism
-- condition $f(gh) = f(g) + g f(h)$, `H1Iso` the quotient description and `H1IsoOfIsTrivial` the
-- trivial-action case (`Additive G →+ A`).
attribute [kb "milne2020cft" "v4.03, Ch. II, Ex. 1.18(a), p. 65"]
  groupCohomology.H1Iso groupCohomology.mem_cocycles₁_iff groupCohomology.H1IsoOfIsTrivial

-- Example 1.20: cohomology of a finite cyclic group.  Mathlib gives the odd-degree case
-- (kernel of the norm modulo the image of $\sigma - 1$) with the criterion for vanishing of a
-- class; the even-degree case is `groupCohomologyIsoEven` (not cited here).
attribute [kb "milne2020cft" "v4.03, Ch. II, Ex. 1.20, p. 66"]
  Rep.FiniteCyclicGroup.groupCohomologyIsoOdd
  Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff

-- Remark 1.21: the connecting homomorphism is computed on cochains by lifting, applying the
-- differential and pulling back.  This is `groupCohomology.δ_apply`.
attribute [kb "milne2020cft" "v4.03, Ch. II, Rem. 1.21, p. 66"] groupCohomology.δ_apply

/-- Proposition 1.22 of Milne (Hilbert's Theorem 90): for a finite Galois extension $L/K$,
$H^1(\mathrm{Gal}(L/K), L^\times) = 0$.

This restates `groupCohomology.H1ofAutOnUnitsUnique` (the group is a singleton) as the vanishing
of the object `groupCohomology (Rep.ofAlgebraAutOnUnits K L) 1`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.22, p. 67"]
theorem prop_1_22 (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] : Limits.IsZero (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 1) := by
  have := groupCohomology.H1ofAutOnUnitsUnique K L
  exact ModuleCat.isZero_of_subsingleton _

-- Corollary 1.23: if $L/K$ is cyclic Galois with generator $\sigma$ and $N(x) = 1$ then
-- $x = y/\sigma y$ for some $y \in L^\times$.  Mathlib phrases the generator by the hypothesis
-- that every element of the Galois group lies in `Subgroup.zpowers g`.
attribute [kb "milne2020cft" "v4.03, Ch. II, Cor. 1.23, p. 67"]
  groupCohomology.exists_div_of_norm_eq_one

-- Example 1.27 (b), (c): restriction and inflation.  `resNatTrans` is the natural transformation
-- from $H^n(G, -)$ to $H^n(H, \mathrm{Res}\,-)$ for a homomorphism $H \to G$; `infNatTrans` is the
-- inflation from $H^n(G/N, M^N)$ to $H^n(G, M)$.
attribute [kb "milne2020cft" "v4.03, Ch. II, Ex. 1.27(b), p. 69"] groupCohomology.resNatTrans
attribute [kb "milne2020cft" "v4.03, Ch. II, Ex. 1.27(c), p. 69"] groupCohomology.infNatTrans

-- Maps of cohomology induced by a compatible pair $(f : G \to H, A \to B)$ (p. 68).
attribute [kb "milne2020cft" "v4.03, Ch. II, §1, Compatible pairs, p. 68"] groupCohomology.map

-- Definition of the tensor product of $G$-modules (p. 73), with the diagonal action.
attribute [kb "milne2020cft" "v4.03, Ch. II, §1, Def. of tensor product of G-modules, p. 73"]
  Representation.tprod

/-! ### Section 2: homology -/

-- Definition of a projective object (p. 74).
attribute [kb "milne2020cft" "v4.03, Ch. II, §2, Def. of projective object, p. 74"] Projective

-- Definition of the homology groups (p. 75) and the comparison with
-- $\mathrm{Tor}^{\mathbb{Z}[G]}_n(M, \mathbb{Z})$.
attribute [kb "milne2020cft" "v4.03, Ch. II, §2, Def. of homology groups, p. 75"]
  groupHomology groupHomologyIsoTor

/-- Proposition 2.7 of Milne: $H_1(G, \mathbb{Z}) \cong G^{\mathrm{ab}}$.

This restates `groupHomology.H1AddEquivOfIsTrivial`, which identifies $H_1(G, A)$ for a trivial
module $A$ with $G^{\mathrm{ab}} \otimes_{\mathbb{Z}} A$, composed with `TensorProduct.rid`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 2.7, p. 77"]
theorem prop_2_7 (G : Type) [Group G] :
    Nonempty (groupHomology (Rep.trivial ℤ G ℤ) 1 ≃+ Additive (Abelianization G)) :=
  ⟨(groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv⟩

/-! ### Section 3: Tate cohomology -/

-- Definition of the norm map $N_G : M \to M$, $m \mapsto \sum_{g \in G} g m$ (p. 77), for a
-- finite group.
attribute [kb "milne2020cft" "v4.03, Ch. II, §3, Def. of the norm map, p. 77"] Rep.norm

-- Definition of the Tate cohomology groups (p. 78) for a finite group, indexed by `ℤ`.
attribute [kb "milne2020cft" "v4.03, Ch. II, §3, Def. of Tate cohomology, p. 78"] tateCohomology

-- The long exact sequence of Tate cohomology (p. 78): `δ` is the connecting map and `exact₁`,
-- `exact₃` are exactness at the two terms flanking it.  The comparisons with group cohomology in
-- positive degrees and with group homology in degrees $\le -2$ are
-- `TateCohomology.isoGroupCohomology` and `TateCohomology.isoGroupHomology` (with the shift
-- $\hat H^{-n-1} = H_n$).
attribute [kb "milne2020cft" "v4.03, Ch. II, §3, Long exact sequence of Tate cohomology, p. 78"]
  TateCohomology.δ TateCohomology.exact₁ TateCohomology.exact₃
  TateCohomology.isoGroupCohomology TateCohomology.isoGroupHomology

/-! ### Section 4: infinite groups -/

-- Definitions of directed set, direct system and direct limit (p. 86).
attribute [kb "milne2020cft" "v4.03, Ch. II, §4, Def. of directed set, p. 86"] IsDirected
attribute [kb "milne2020cft" "v4.03, Ch. II, §4, Def. of direct system, p. 86"] DirectedSystem
attribute [kb "milne2020cft" "v4.03, Ch. II, §4, Def. of direct limit, p. 86"] Module.DirectLimit

/-- Lemma 4.1 of Milne: direct limits of abelian groups are exact.

This restates the instance of Grothendieck's axiom `AB5` for `ModuleCat ℤ` (filtered colimits are
exact), proved in Mathlib for modules over any ring. -/
@[kb "milne2020cft" "v4.03, Ch. II, Lem. 4.1, p. 86"]
theorem lemma_4_1 : AB5 (ModuleCat.{0} ℤ) := inferInstance

-- Definition of a profinite group (p. 86).
attribute [kb "milne2020cft" "v4.03, Ch. II, §4, Def. of profinite group, p. 86"] ProfiniteGrp

-- Definition of continuous cohomology (p. 87) of a topological group in a topological module.
attribute [kb "milne2020cft" "v4.03, Ch. II, §4, Def. of continuous cohomology, p. 87"]
  continuousCohomology

/-! ### Appendix: homological algebra -/

-- Definition of an additive category (p. 90): a preadditive category with finite biproducts.
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Def. of additive category, p. 90"]
  Preadditive Limits.HasFiniteBiproducts

-- Definitions of kernel and cokernel (p. 91).
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Def. of kernel and cokernel, p. 91"]
  Limits.kernel Limits.cokernel

-- Definition of a monomorphism (p. 91).
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Def. of monomorphism, p. 91"] Mono

-- Definition of the image of a morphism (p. 91).
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Def. of image, p. 91"] Limits.image

-- Definition of an abelian category (p. 91).
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Def. of abelian category, p. 91"] Abelian

/-- Definition of an exact functor (p. 91 of Milne): an additive functor between abelian
categories is exact if it takes exact sequences to exact sequences.

Mathlib has no bundled predicate with this name.  This restates the equivalence, for an additive
functor, of "preserves exact sequences" (the book's definition) with "preserves short exact
sequences" (`Functor.exact_tfae`); the latter is also equivalent to preserving finite limits and
finite colimits. -/
@[kb "milne2020cft" "v4.03, Ch. II, App. A, Def. of exact functor, p. 91"]
theorem def_exact_functor {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] :
    (∀ S : ShortComplex C, S.Exact → (S.map F).Exact) ↔
      (∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact) :=
  ((Functor.exact_tfae F).out 2 1)

-- Lemma A.1 (the snake lemma, extended): for a commutative diagram with exact rows, the sequence
-- $\ker a \to \ker b \to \ker c \to \mathrm{coker}\, a \to \mathrm{coker}\, b \to
-- \mathrm{coker}\, c$ is exact.  `SnakeInput` is the diagram, `snake_lemma` the six-term exact
-- sequence.  The two extra zeros of Milne's extended statement are present as `mono_L₀_f` (when the
-- first row is short exact on the left) and `epi_L₃_g` (when the second row is short exact on the
-- right).
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Lem. A.1, p. 89"]
  ShortComplex.SnakeInput ShortComplex.SnakeInput.snake_lemma
  ShortComplex.SnakeInput.mono_L₀_f ShortComplex.SnakeInput.epi_L₃_g

-- Proposition A.3 (a module over a PID is injective iff it is divisible), one direction and only
-- over $\mathbb{Z}$: a divisible abelian group satisfies Baer's criterion (`Module.Baer`, which
-- is equivalent to injectivity by `Module.Baer.injective`).  The converse (injective implies
-- divisible) and the case of a general PID are not in Mathlib in this form.
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Prop. A.3, p. 91"] Module.Baer.of_divisible

-- Definition of an injective resolution (p. 92).
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Def. of injective resolution, p. 92"]
  InjectiveResolution

-- Proposition A.4: the category of modules over a PID (here: over any ring) has enough
-- injectives, `ModuleCat.enoughInjectives`.
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Prop. A.4, p. 92"] ModuleCat.enoughInjectives

-- Proposition A.5: a right adjoint of a functor preserving monomorphisms preserves injective
-- objects.
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Prop. A.5, p. 92"]
  Adjunction.map_injective Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms

-- Lemma A.6: any morphism lifts to a morphism of injective resolutions.  `HasInjectiveResolutions`
-- is existence of injective resolutions, and `InjectiveResolution.desc` is the lift.
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Lem. A.6, p. 93"]
  HasInjectiveResolutions InjectiveResolution.desc

-- Definition of homotopic morphisms of complexes (p. 93).
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Def. of homotopic morphisms, p. 93"] Homotopy

-- Remark A.7: $R^0F \cong F$ for a left exact functor $F$.
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Rem. A.7, p. 93"]
  Functor.rightDerivedZeroIsoSelf

-- Proposition A.8: two lifts are homotopic (`descHomotopy`); this makes the right derived functors
-- independent of the choice of resolutions.
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Prop. A.8, p. 93"]
  InjectiveResolution.descHomotopy

-- Definition of right derived functors (p. 94).
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Def. of right derived functors, p. 94"]
  Functor.rightDerived

-- After Proposition A.8 (p. 94): $R^nF(X)$ is computed by any injective resolution of $X$, up to a well-defined
-- isomorphism.  (Lemma A.10 itself, homotopy of two extensions, is `lemma_A_10` in `Ch2Appendix.lean`.)
attribute [kb "milne2020cft"
    "v4.03, Ch. II, App. A, after Prop. A.8 (R^rF computed by any injective resolution), p. 94"]
  InjectiveResolution.isoRightDerivedObj

-- Definition of Ext (p. 95): Mathlib's `Abelian.Ext X Y n` is a Yoneda-style Ext type, not defined
-- by derived functors; its comparison with derived functors is in the next items.
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Def. of Ext, p. 95"] Abelian.Ext

-- Proposition A.13: $\mathrm{Ext}^n(X, Y)$ is computed by a projective resolution of $X$ as the
-- cohomology of $\mathrm{Hom}(P_\bullet, Y)$.  Mathlib states this for the linear Ext functor
-- `Ext R C n` and a projective resolution `P`; the book's balanced statement (computing by an
-- injective resolution of $Y$) is not cited.
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Prop. A.13, p. 95"]
  ProjectiveResolution.isoExt

-- Example A.14: $H^n(G, M) \cong \mathrm{Ext}^n_{\mathbb{Z}[G]}(\mathbb{Z}, M)$.
attribute [kb "milne2020cft" "v4.03, Ch. II, App. A, Ex. A.14, p. 96"] groupCohomologyIsoExt

end NumberFieldKB.MilneCFT
