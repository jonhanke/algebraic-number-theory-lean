import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Quaternion

/-!
# Milne, Class Field Theory, Chapter IV: results in Mathlib

Chapter IV ("Brauer groups") of J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography
key `milne2020cft`) develops the theory of semisimple, simple and central simple algebras, the
Brauer group of a field, and the Brauer group of a local field.  This file cites the items of that
chapter which are already available in Mathlib (and, for the quaternion algebras of Example 1.12
and Exercise 5.7, in QuadFormsKB).

Convention.
* When one Mathlib declaration states the book's item in essentially the book's form, the
  declaration is tagged directly with `attribute [kb "milne2020cft" ...]`, with a comment saying
  which item it is and how the form differs.
* When the book's form differs, a short restating theorem in the book's form is proved from the
  Mathlib results, and that theorem carries the tag.
* Milne's standing setting is a field $k$, finite dimensional $k$-algebras and finitely generated
  modules.  Mathlib states most of these results for general rings and modules; these are more
  general than the book, and in particular imply the book's statements.
* The page in each locator is the printed page of the book (printed page = pdf page − 9).
-/

universe u

namespace NumberFieldKB.MilneCFT.Ch4

/-! ### Section 1: Semisimple modules and algebras -/

-- Definition of a faithful module (p. 119): $M$ is faithful over $A$ if only $0 \in A$ acts as
-- zero on $M$.  Mathlib's `FaithfulSMul A M` says that distinct elements of $A$ act differently
-- on $M$, which for a module is the same condition (stated for general `SMul`).
attribute [kb "milne2020cft" "v4.03, Ch. IV, §1, def. of faithful module, p. 119"] FaithfulSMul

-- Theorem 1.2 (Jordan–Hölder), existence part and uniqueness part, p. 120.  Mathlib states
-- the uniqueness part for any `JordanHolderLattice` (`CompositionSeries.jordan_holder`) in
-- terms of `CompositionSeries.Equivalent`; the submodule lattice of a module is one.  The
-- existence part is `exists_compositionSeries_of_isNoetherian_isArtinian` (for modules that are
-- Noetherian and Artinian).  Both are tagged directly; the combined form for finitely generated
-- modules over an Artinian ring is `thm_1_2` below.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Thm. 1.2, p. 120"]
  CompositionSeries.jordan_holder exists_compositionSeries_of_isNoetherian_isArtinian

/-- Theorem 1.2 of Milne (Jordan–Hölder): a finitely generated module $M$ over an Artinian ring
$A$ (e.g. a finite dimensional algebra over a field) has a composition series, and any two
composition series of $M$ are equivalent.  Combines `exists_compositionSeries_of_isNoetherian_isArtinian`
and `CompositionSeries.jordan_holder` for the lattice of submodules; a finitely generated module
over an Artinian ring is Noetherian and Artinian. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 1.2, p. 120"]
theorem thm_1_2 (A : Type*) [Ring A] [IsArtinianRing A] (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    (∃ s : CompositionSeries (Submodule A M), s.head = ⊥ ∧ s.last = ⊤) ∧
      ∀ s₁ s₂ : CompositionSeries (Submodule A M), s₁.head = s₂.head → s₁.last = s₂.last →
        s₁.Equivalent s₂ :=
  ⟨exists_compositionSeries_of_isNoetherian_isArtinian A M,
    fun s₁ s₂ hb ht => CompositionSeries.jordan_holder s₁ s₂ hb ht⟩

open Set in
/-- Variant of `exists_sSupIndep_disjoint_sSup_atoms` with the atoms taken from a given set `t`. -/
theorem exists_sSupIndep_isCompl_of_subset {α : Type*} [CompleteLattice α] [IsModularLattice α]
    [IsCompactlyGenerated α] (t : Set α) (ht : ∀ a ∈ t, IsAtom a) (htop : sSup t = ⊤) (b : α) :
    ∃ s ⊆ t, sSupIndep s ∧ IsCompl b (sSup s) := by
  have zorn := zorn_subset
    (S := {s : Set α | sSupIndep s ∧ Disjoint b (sSup s) ∧ s ⊆ t})
    fun c hc1 hc2 =>
      ⟨⋃₀ c,
        ⟨iSupIndep_sUnion_of_directed hc2.directedOn fun s hs => (hc1 hs).1, ?_,
          fun a ⟨s, sc, as⟩ => (hc1 sc).2.2 as⟩,
        fun _ => Set.subset_sUnion_of_mem⟩
  swap
  · rw [sSup_sUnion, ← sSup_image, DirectedOn.disjoint_sSup_right]
    · rintro _ ⟨s, hs, rfl⟩
      exact (hc1 hs).2.1
    · rw [directedOn_image]
      exact hc2.directedOn.mono @fun s t => sSup_le_sSup
  simp_rw [maximal_subset_iff] at zorn
  obtain ⟨s, ⟨s_ind, b_inf_Sup_s, s_t⟩, s_max⟩ := zorn
  refine ⟨s, s_t, s_ind, ⟨b_inf_Sup_s, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩⟩
  rw [← htop, sSup_le_iff]
  intro a ha
  rw [← inf_eq_left]
  refine ((ht a ha).le_iff.mp inf_le_left).resolve_left fun con => (ht a ha).1 ?_
  rw [← con, eq_comm, inf_eq_left]
  refine (le_sSup ?_).trans le_sup_right
  rw [← disjoint_iff] at con
  have a_dis_Sup_s : Disjoint a (sSup s) := con.mono_right le_sup_right
  rw [s_max ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩ Set.subset_union_left]
  · exact Set.mem_union_right _ (Set.mem_singleton _)
  · rw [sSup_union, sSup_singleton]
    exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain rfl | xa := eq_or_ne x a
    · simp only [Set.mem_singleton, Set.insert_sdiff_of_mem, Set.union_singleton]
      exact con.mono_right ((sSup_le_sSup Set.sdiff_subset).trans le_sup_right)
    · have h : (s ∪ {a}) \ {x} = s \ {x} ∪ {a} := by
        simp only [Set.union_singleton]
        rw [Set.insert_sdiff_of_notMem]
        rw [Set.mem_singleton_iff]
        exact Ne.symm xa
      rw [h, sSup_union, sSup_singleton]
      apply
        (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left
          (a_dis_Sup_s.mono_right _).symm
      rw [← sSup_insert, Set.insert_sdiff_singleton, Set.insert_eq_of_mem (hx.resolve_right xa)]
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain hx | rfl := hx
    · exact s_t hx
    · exact ha

/-- Proposition 1.4 of Milne: let $V = \sum_{i \in I} S_i$ be a sum of simple submodules and $W$ a
submodule.  Then there is a subset $J \subseteq I$ with $V = W \oplus \bigoplus_{i \in J} S_i$: the
family $(S_i)_{i \in J}$ is independent and its sum is a complement of $W$.  (Milne's proof: Zorn's
lemma on the subsets $J$ with direct sum meeting $W$ in $0$, as in Mathlib's
`exists_sSupIndep_disjoint_sSup_atoms`.) -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 1.4, p. 120"]
theorem prop_1_4 {A V : Type*} [Ring A] [AddCommGroup V] [Module A V] {ι : Type*}
    (S : ι → Submodule A V) (hS : ∀ i, IsSimpleModule A (S i)) (hV : ⨆ i, S i = ⊤)
    (W : Submodule A V) :
    ∃ J : Set ι, iSupIndep (fun i : J => S i) ∧ IsCompl W (⨆ i ∈ J, S i) := by
  obtain ⟨s, hst, hind, hc⟩ := exists_sSupIndep_isCompl_of_subset (Set.range S)
    (by rintro _ ⟨i, rfl⟩; exact isSimpleModule_iff_isAtom.mp (hS i)) (by rw [sSup_range, hV]) W
  choose g hg using fun a : s => hst a.2
  refine ⟨Set.range g, ?_, ?_⟩
  · have hinj : Function.Injective g := fun a b h => Subtype.ext (by rw [← hg a, ← hg b, h])
    have : (fun i : Set.range g => S i) = ((↑) : s → Submodule A V) ∘
        (Equiv.ofInjective g hinj).symm := by
      funext x
      obtain ⟨i, a, ha⟩ := x
      subst ha
      simp only [Function.comp_apply]
      rw [show (⟨g a, a, rfl⟩ : Set.range g) = Equiv.ofInjective g hinj a from rfl,
        Equiv.symm_apply_apply, hg]
    rw [this]
    exact ((sSupIndep_iff s).mp hind).comp (Equiv.injective _)
  · have : (⨆ i ∈ Set.range g, S i) = sSup s := by
      rw [iSup_range, sSup_eq_iSup']
      simp [hg]
    rw [this]; exact hc

/-- Corollary 1.5 of Milne: for a module $V$ the following are equivalent: (a) $V$ is semisimple
(`IsSemisimpleModule A V`, which is by definition that every submodule has a complement, i.e.
the submodule lattice is complemented); (b) $V$ is a sum of simple submodules (the sum of all
simple submodules is $V$); (c) $V$ is a sum of some family of simple submodules; (d) every
submodule of $V$ has a complement. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 1.5, p. 121"]
theorem cor_1_5 (A V : Type*) [Ring A] [AddCommGroup V] [Module A V] :
    List.TFAE
      [IsSemisimpleModule A V,
       sSup { m : Submodule A V | IsSimpleModule A m } = ⊤,
       ∃ T : Set (Submodule A V), (∀ N ∈ T, IsSimpleModule A N) ∧ sSup T = ⊤,
       ∀ W : Submodule A V, ∃ W' : Submodule A V, IsCompl W W'] := by
  tfae_have 1 → 2 := fun h => IsSemisimpleModule.sSup_simples_eq_top A V
  tfae_have 2 → 3 := fun h => ⟨_, fun N hN => hN, h⟩
  tfae_have 3 → 1 := by
    rintro ⟨T, hT, hTop⟩
    refine IsSemisimpleModule.of_sSup_simples_eq_top (top_unique ?_)
    rw [← hTop]
    exact sSup_le_sSup fun N hN => hT N hN
  tfae_have 1 → 4 := fun h W => exists_isCompl W
  tfae_have 4 → 1 := fun h => by
    have : ComplementedLattice (Submodule A V) := ⟨h⟩
    exact ⟨⟩
  tfae_finish

-- Definition of semisimple module (p. 120): a module that is a direct sum of simple modules
-- (equivalently, by Cor. 1.5, in which each submodule has a complement).  Mathlib's
-- `IsSemisimpleModule` is the complemented-lattice condition (Cor. 1.5(d)); the equivalence with
-- the sum-of-simples form is `cor_1_5` above.
attribute [kb "milne2020cft" "v4.03, Ch. IV, §1, def. of semisimple module, p. 120"]
  IsSemisimpleModule

-- Corollary 1.6 (p. 121): (a) submodules and (b) quotient modules of semisimple modules are
-- semisimple (Mathlib instances `IsSemisimpleModule.submodule` and
-- `IsSemisimpleModule.quotient`; also `IsSemisimpleModule.of_injective` and
-- `IsSemisimpleModule.of_surjective` for images under maps).  (c) A module generated by
-- semisimple submodules is semisimple (`isSemisimpleModule_of_isSemisimpleModule_submodule`);
-- for finite families the sum is also semisimple by the instance on finite sums
-- (`IsSemisimpleModule.sup`).
attribute [kb "milne2020cft" "v4.03, Ch. IV, Cor. 1.6, p. 121"]
  IsSemisimpleModule.submodule IsSemisimpleModule.quotient
  IsSemisimpleModule.of_injective IsSemisimpleModule.of_surjective
  isSemisimpleModule_of_isSemisimpleModule_submodule IsSemisimpleModule.sup

-- Definition of isotypic modules and isotypic components (p. 121): a module is isotypic of type
-- $S$ if all its simple submodules are isomorphic to $S$ (`IsIsotypicOfType`; `IsIsotypic`
-- without specifying $S$).  The isotypic component of $V$ of type $S$ is the sum of all
-- submodules of $V$ isomorphic to $S$ (`isotypicComponent`).
attribute [kb "milne2020cft" "v4.03, Ch. IV, §1, def. of isotypic module, p. 121"]
  IsIsotypicOfType IsIsotypic

attribute [kb "milne2020cft" "v4.03, Ch. IV, §1, def. of isotypic component, p. 121"]
  isotypicComponent

-- Proposition 1.7 (p. 121): in a semisimple module the submodules stable under all
-- endomorphisms (`Submodule.IsFullyInvariant`) are exactly the sums of isotypic components
-- (`isotypicComponents` is the set of nonzero isotypic components).  Stated for any semisimple
-- module (Milne: finitely generated module over a finite dimensional algebra).
attribute [kb "milne2020cft" "v4.03, Ch. IV, Prop. 1.7, p. 121"]
  isFullyInvariant_iff_sSup_isotypicComponents

/-- Section 1.8 of Milne: for an $A$-algebra structure, $\mathrm{End}_A(A) \cong A^{\mathrm{opp}}$
(a map is determined by the image of $1$, and $a \mapsto (x \mapsto xa)$).  Mathlib has the
algebra isomorphism `AlgEquiv.moduleEndSelf`; here it is restated together with the matrix
form $\mathrm{End}_A(A^n) \cong M_n(A^{\mathrm{opp}})$, which follows by composing with
`Module.endVecAlgEquivMatrixEnd`. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §1, 1.8, p. 122"]
theorem sec_1_8 (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] (n : ℕ) :
    Nonempty (Aᵐᵒᵖ ≃ₐ[R] Module.End A A) ∧
      Nonempty (Module.End A (Fin n → A) ≃ₐ[R] Matrix (Fin n) (Fin n) Aᵐᵒᵖ) :=
  ⟨⟨AlgEquiv.moduleEndSelf R (A := A)⟩,
    ⟨(endVecAlgEquivMatrixEnd (Fin n) R A A).trans
      (AlgEquiv.mapMatrix (AlgEquiv.moduleEndSelf R (A := A)).symm)⟩⟩

-- Definition of semisimple algebra (p. 122): an algebra $A$ is semisimple if $A_A$ (the algebra as
-- a module over itself) is a semisimple module.  Mathlib's `IsSemisimpleRing A` is by definition
-- `IsSemisimpleModule A A`.
attribute [kb "milne2020cft" "v4.03, Ch. IV, §1, def. of semisimple algebra, p. 122"]
  IsSemisimpleRing

-- Definition of simple algebra (p. 122): an algebra with no two-sided ideals other than $0$ and
-- $A$ (and $A \ne 0$).  Mathlib's `IsSimpleRing A` says that the lattice of two-sided ideals is a
-- simple order, i.e. $A$ is nontrivial and has only the trivial two-sided ideals.
attribute [kb "milne2020cft" "v4.03, Ch. IV, §1, def. of simple algebra, p. 122"]
  IsSimpleRing

/-- Proposition 1.9 of Milne: let $A$ be a semisimple algebra.  The isotypic components of $A_A$
are two-sided ideals, and they are the minimal nonzero two-sided ideals; every two-sided ideal of
$A$ is a sum of isotypic components.  Mathlib phrases two-sided ideals through fully invariant
submodules of $A_A$ (`isFullyInvariant_iff_isTwoSided`) and has no single statement in the book's
form, so this is restated from `isFullyInvariant_iff_sSup_isotypicComponents`,
`mem_isotypicComponents_iff` and `isFullyInvariant_iff_le_imp_isotypicComponent_le`. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 1.9, p. 122"]
theorem prop_1_9 (A : Type*) [Ring A] [IsSemisimpleRing A] :
    (∀ c ∈ isotypicComponents A A, Ideal.IsTwoSided c ∧ c ≠ ⊥ ∧
      ∀ J : Ideal A, J.IsTwoSided → J ≤ c → J = ⊥ ∨ J = c) ∧
    (∀ J : Ideal A, J.IsTwoSided → ∃ s ⊆ isotypicComponents A A, J = sSup s) := by
  refine ⟨fun c hc => ?_, fun J hJ => ?_⟩
  · obtain ⟨hiso, hinv, hne⟩ := mem_isotypicComponents_iff.mp hc
    refine ⟨isFullyInvariant_iff_isTwoSided.mp hinv, hne, fun J hJ hle => ?_⟩
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le J with h | ⟨S, hSJ, hS⟩
    · exact Or.inl h
    · right
      refine le_antisymm hle ?_
      have hSc : S ≤ c := hSJ.trans hle
      have h1 := (eq_isotypicComponent_iff (S := S) hne).mpr
        ⟨isIsotypic_submodule_iff.mp hiso S hSc, hinv⟩
      rw [h1]
      exact (isFullyInvariant_iff_le_imp_isotypicComponent_le.mp
        (isFullyInvariant_iff_isTwoSided.mpr hJ) S hSJ)
  · exact isFullyInvariant_iff_sSup_isotypicComponents.mp (isFullyInvariant_iff_isTwoSided.mpr hJ)

-- Example 1.10 (p. 122): a division ring is a simple algebra (`DivisionRing.isSimpleRing`), and a
-- finitely generated module over a division algebra is free (`Module.Free.of_divisionRing`)
-- with a well defined dimension (`mk_eq_mk_of_basis'`: any two bases have the same cardinality).
attribute [kb "milne2020cft" "v4.03, Ch. IV, Ex. 1.10, p. 122"]
  DivisionRing.isSimpleRing Module.Free.of_divisionRing mk_eq_mk_of_basis'

-- Example 1.11 (p. 123): if $D$ is a simple algebra, so is the matrix algebra $M_n(D)$, for
-- $n \ge 1$.  Mathlib states this for any simple ring $D$ and finite nonempty index type.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Ex. 1.11, p. 123"] IsSimpleRing.matrix

/-- Example 1.13(a) of Milne: the centralizer of the scalar matrices in $M_n(k)$ is all of
$M_n(k)$ (scalar matrices are central). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 1.13(a), p. 123"]
theorem ex_1_13_a (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] :
    Set.centralizer (Set.range (algebraMap k (Matrix n n k))) = Set.univ := by
  ext M
  simp only [Set.mem_centralizer_iff, Set.mem_range, Set.mem_univ, iff_true]
  rintro _ ⟨c, rfl⟩
  exact Algebra.commutes c M

-- Example 1.13(b) (p. 123): the center of $M_n(k)$ is the scalar matrices $k$.  Mathlib proves
-- that the matrix algebra over a central algebra is central (`Algebra.IsCentral.matrix`),
-- whose proof is the equality of subalgebras `Matrix.subalgebraCenter_eq_scalarAlgHom_map`;
-- the case of the central algebra $k$ over itself gives the book's statement.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Ex. 1.13(b), p. 123"]
  Algebra.IsCentral.matrix Matrix.subalgebraCenter_eq_scalarAlgHom_map

/-- Example 1.13(c) of Milne: the centralizer of the diagonal matrices in $M_n(k)$ is the algebra
of diagonal matrices. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 1.13(c), p. 123"]
theorem ex_1_13_c (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] :
    Set.centralizer (Set.range (Matrix.diagonal : (n → k) → Matrix n n k)) =
      Set.range (Matrix.diagonal : (n → k) → Matrix n n k) := by
  ext M
  simp only [Set.mem_centralizer_iff, Set.mem_range]
  constructor
  · intro h
    refine ⟨fun i => M i i, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · have := congrFun (congrFun (h (Matrix.diagonal (Pi.single i 1)) ⟨_, rfl⟩) i) j
      simp [Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply] at this
      have h0 := this (Ne.symm hij)
      simp [hij, h0]
  · rintro ⟨d, rfl⟩ _ ⟨e, rfl⟩
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _

/-- Theorem 1.14 of Milne (double centralizer theorem): let $M$ be a faithful semisimple
$A$-module and $B = \mathrm{End}_A(M)$.  If $M$ is finitely generated over $B$ then the map
$A \to \mathrm{End}_B(M)$ is bijective.  Mathlib's `Module.Finite.toModuleEnd_moduleEnd_surjective`
gives surjectivity for any semisimple module finite over its endomorphism ring; injectivity is
faithfulness.  Milne assumes $A$ a finite dimensional $k$-algebra and $M$ finitely generated over
$A$, which makes $M$ finite over $B \supseteq k$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 1.14, p. 124"]
theorem thm_1_14 (A M : Type*) [Ring A] [AddCommGroup M] [Module A M] [IsSemisimpleModule A M]
    [FaithfulSMul A M] [Module.Finite (Module.End A M) M] :
    Function.Bijective (Module.toModuleEnd (Module.End A M) (S := A) M) := by
  refine ⟨fun a b hab => eq_of_smul_eq_smul (α := M) fun m => ?_,
    Module.Finite.toModuleEnd_moduleEnd_surjective⟩
  exact congrArg (fun f => f m) hab

-- Lemma 1.15 (p. 124): Jacobson density for finitely many vectors.  For a semisimple module $M$
-- over $A$, every $\mathrm{End}_A(M)$-linear endomorphism $f$ of $M$ and every finite set of
-- vectors, some $a \in A$ acts like $f$ on those vectors.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Lem. 1.15, p. 124"] jacobson_density

-- Lemma 1.16 (Schur's lemma, p. 124): a nonzero homomorphism between simple modules is an
-- isomorphism (`LinearMap.bijective_or_eq_zero`), so the endomorphism ring of a simple module is a
-- division ring (`Module.End.instDivisionRing`).
attribute [kb "milne2020cft" "v4.03, Ch. IV, Lem. 1.16, p. 124"]
  LinearMap.bijective_or_eq_zero Module.End.instDivisionRing

/-- Theorem 1.17 of Milne (Wedderburn): a finite dimensional simple algebra $A$ over a field $K$ is
isomorphic to a matrix algebra $M_n(D)$ over a (finite dimensional) division $K$-algebra $D$.
Restates `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`, using that a finite dimensional
algebra over a field is Artinian.  Milne's uniqueness of $n$ and of $D$ up to isomorphism is
not included. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 1.17, p. 124"]
theorem thm_1_17 (K : Type*) (A : Type u) [Field K] [Ring A] [Algebra K A] [IsSimpleRing A]
    [FiniteDimensional K A] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : FiniteDimensional K D), Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) D) := by
  have := IsArtinianRing.of_finite K A
  exact IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A

/-- Proposition 1.18 of Milne: a finite dimensional simple algebra over a field is semisimple.
Mathlib: for a simple ring, semisimple is equivalent to Artinian
(`IsSimpleRing.isSemisimpleRing_iff_isArtinianRing`), and a finite dimensional algebra over a field
is Artinian. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 1.18, p. 125"]
theorem prop_1_18 (K A : Type*) [Field K] [Ring A] [Algebra K A] [IsSimpleRing A]
    [FiniteDimensional K A] : IsSemisimpleRing A :=
  IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr (IsArtinianRing.of_finite K A)

-- Theorem 1.19 (p. 125).  Mathlib: a ring is simple and Artinian if and only if it is
-- semisimple, isotypic (as a module over itself) and nontrivial.  (Matched by position in
-- Milne's numbering 1.19, 1.20, 1.21; the exact assertions of the book were not rechecked.)
attribute [kb "milne2020cft" "v4.03, Ch. IV, Thm. 1.19, p. 125"] isSimpleRing_isArtinianRing_iff

-- Corollary 1.20 (p. 125): over a simple Artinian algebra every module is isotypic, in particular
-- all simple modules are isomorphic.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Cor. 1.20, p. 125"] IsSimpleRing.isIsotypic

-- Corollary 1.21, first assertion (p. 125): a finitely generated isotypic semisimple module is
-- isomorphic to $S^n$ for a simple module $S$ (`IsIsotypic.linearEquiv_fun`; the version for
-- arbitrary modules, with a direct sum of copies of $S$, is `IsIsotypic.linearEquiv_finsupp`).
attribute [kb "milne2020cft" "v4.03, Ch. IV, Cor. 1.21, p. 125"]
  IsIsotypic.linearEquiv_fun IsIsotypic.linearEquiv_finsupp

/-! ### Section 2: Central simple algebras -/

-- Example 2.1 (p. 126): $M_n(A) \cong A \otimes_k M_n(k)$.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Ex. 2.1, p. 126"] matrixEquivTensor

-- Example 2.2 (p. 126): $M_m(k) \otimes_k M_n(k) \cong M_{mn}(k)$ (Kronecker product).
attribute [kb "milne2020cft" "v4.03, Ch. IV, Ex. 2.2, p. 126"] Matrix.kroneckerAlgEquiv

-- Corollary 2.4 (p. 127): the center of a simple algebra is a field.  Mathlib states this for any
-- simple ring.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Cor. 2.4, p. 127"] IsSimpleRing.isField_center

-- Definition of central algebra and central simple algebra (p. 127): a $k$-algebra whose center
-- is $k$ (`Algebra.IsCentral`), and one which is also simple and finite dimensional.  Mathlib
-- has the bundled structure `CSA`, whose fields are central, simple and finite dimensional.
attribute [kb "milne2020cft" "v4.03, Ch. IV, §2, def. of central algebra, p. 127"]
  Algebra.IsCentral

attribute [kb "milne2020cft" "v4.03, Ch. IV, §2, def. of central simple algebra, p. 127"]
  CSA

/-! ### Section 3: Definition of the Brauer group -/

-- Definition of similarity and of the Brauer group (p. 130).  Milne calls central simple
-- algebras $A$ and $B$ similar if $A \otimes_k M_n(k) \cong B \otimes_k M_m(k)$ for some
-- $n, m \ge 1$; Mathlib's `IsBrauerEquivalent` requires $M_n(A) \cong M_m(B)$ as $k$-algebras.
-- These agree via `matrixEquivTensor` ($M_n(A) \cong A \otimes_k M_n(k)$, Example 2.1); the
-- comparison is proved in another file.  `BrauerGroup k` is the set of similarity classes
-- (quotient of `CSA k`).
attribute [kb "milne2020cft" "v4.03, Ch. IV, §3, def. of similarity, p. 130"] IsBrauerEquivalent

attribute [kb "milne2020cft" "v4.03, Ch. IV, §3, def. of the Brauer group, p. 130"] BrauerGroup

/-- Lemma 3.9 of Milne: let $D$ be a division algebra, finite dimensional and central over a field
$K$, with $D \ne K$.  Then there is an element $x \in D \setminus K$ which is separable over $K$,
and then $K[x] = $ `Algebra.adjoin K {x}` is a separable subfield of $D$ different from $K$.
Restates `JacobsonNoether.exists_separable_and_not_isCentral'` (Jacobson–Noether, which needs only
that $D$ is algebraic over $K$) with the hypothesis $D \ne K$ as `finrank K D ≠ 1`, and records the
element $x$ and that the subalgebra it generates is not $K$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Lem. 3.9, p. 134"]
theorem lemma_3_9 (K D : Type*) [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (h : Module.finrank K D ≠ 1) :
    ∃ x : D, x ∉ Set.range (algebraMap K D) ∧ IsSeparable K x ∧
      Algebra.adjoin K {x} ≠ ⊥ := by
  have hbot : (⊥ : Subalgebra K D) ≠ ⊤ := by
    intro hb
    apply h
    rw [← Subalgebra.finrank_bot (F := K) (E := D), hb]
    exact (Subalgebra.topEquiv.toLinearEquiv.finrank_eq).symm
  obtain ⟨x, hx, hsep⟩ := JacobsonNoether.exists_separable_and_not_isCentral' (L := K) (D := D) hbot
  refine ⟨x, ?_, hsep, ?_⟩
  · intro hr
    exact hx (Algebra.mem_bot.mpr hr)
  · intro hb
    exact hx (hb ▸ Algebra.self_mem_adjoin_singleton K x)

/-! ### Section 4: Brauer groups of local fields -/

-- Theorem 4.1 (p. 138): every finite division ring is commutative (Wedderburn's little theorem);
-- Mathlib: it is a field.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Thm. 4.1, p. 138"] littleWedderburn

/-! ### Section 5: Semisimple algebras and the Wedderburn theorem -/

-- Example 5.1 (p. 141): a finite product of simple (Artinian) algebras is semisimple.  Mathlib
-- has the instance that a finite product of semisimple rings is semisimple; a simple Artinian ring
-- is semisimple (`IsSimpleRing.instIsSemisimpleRing`).
attribute [kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.1, p. 141"]
  instIsSemisimpleRingForallOfFinite

-- Theorem 5.3 (p. 142): for a semisimple module $M$ finitely generated over a ring $A$,
-- $\mathrm{End}_A(M)$ is a finite product of matrix algebras over division algebras.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Thm. 5.3, p. 142"]
  IsSemisimpleModule.exists_end_algEquiv_pi_matrix_divisionRing

-- Theorem 5.4 (p. 142), Wedderburn's theorem for semisimple algebras: a finite dimensional
-- semisimple algebra is a finite product of matrix algebras over (finite dimensional) division
-- algebras.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Thm. 5.4, p. 142"]
  IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite

/-! ### Quaternion algebras (QuadFormsKB) -/

-- Example 1.12 (p. 123): quaternion algebras $(a,b)_K$ are either division algebras or
-- isomorphic to $M_2(K)$.  QuadFormsKB: $(a,b)_K$ is a division algebra iff the Hilbert symbol is
-- $-1$, and $(a,b)_K \cong M_2(K)$ iff the Hilbert symbol is $1$.
attribute [kb "milne2020cft" "v4.03, Ch. IV, Ex. 1.12, p. 123"]
  QuadFormsKB.Quat.hilbertSymbol_eq_neg_one_iff_division
  QuadFormsKB.Quat.nonempty_algEquiv_matrix_iff

-- Exercise 5.7 (p. 144), parts (b) and (c): the quaternion algebra $(a,b)_K$ has a nonzero
-- element of reduced norm zero iff the Hilbert symbol is $1$ (b), in which case it is
-- isomorphic to $M_2(K)$ (c).  (Part (j) is in `Ch4CiteQuat.lean`.)
attribute [kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(b), p. 144"]
  QuadFormsKB.Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero

attribute [kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(c), p. 144"]
  QuadFormsKB.Quat.nonempty_algEquiv_matrix_of_hilbertSymbol

end NumberFieldKB.MilneCFT.Ch4
