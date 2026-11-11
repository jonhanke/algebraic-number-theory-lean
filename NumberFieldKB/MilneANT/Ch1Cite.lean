import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
import Mathlib.RingTheory.Localization.AtPrime.Basic
import QuadFormsKB.Citation
import Mathlib.Data.Fintype.Inv

/-!
# Milne, Algebraic Number Theory, Chapter 1: results in Mathlib

Chapter 1 of J. S. Milne, *Algebraic Number Theory* (version 3.08, 2020; bibliography key
`milne2020ant`) collects preliminaries from commutative algebra.  This file cites the items of
that chapter which are already available in Mathlib.

Convention.
* When one Mathlib declaration states the book's result in essentially the book's form, the
  declaration is tagged directly with `attribute [kb "milne2020ant" ...]`, with a comment saying
  which item it is and how the form differs.
* When the book's form differs (several Mathlib results combined, a different packaging of the
  hypotheses, an equivalence versus one direction), a short restating theorem in the book's form
  is proved from the Mathlib results, and that theorem carries the tag.
* The page in each locator is the printed page of the book, which is the page of the file minus
  two.
-/

namespace NumberFieldKB.MilneANT

-- Proposition 1.1, first half: every ideal of a product ring is a product of ideals.
-- Mathlib writes the ideal as the product of its two images under the coordinate projections.
attribute [kb "milne2020ant" "v3.08, Prop. 1.1, p. 15"] Ideal.ideal_prod_eq

-- Proposition 1.1, second half: the prime ideals of a product ring.
-- Mathlib states this as an equivalence for an arbitrary ideal of the product.
attribute [kb "milne2020ant" "v3.08, Prop. 1.1, p. 15"] Ideal.ideal_prod_prime

/-- Proposition 1.3 of Milne: for a commutative ring $A$ the following are equivalent: $A$ is
noetherian (every ideal is finitely generated); every ascending chain of ideals eventually
becomes constant; every nonempty set of ideals has a maximal element.

This restates `monotone_stabilizes_iff_noetherian` and `set_has_maximal_iff_noetherian`, which are
stated for modules, by taking $A$ as a module over itself.  Mathlib's definition of
`IsNoetherianRing` is the module condition, which is equivalent to the book's definition by
`isNoetherianRing_iff_ideal_fg`. -/
@[kb "milne2020ant" "v3.08, Prop. 1.3, p. 15"]
theorem prop_1_3_tfae (A : Type*) [CommRing A] :
    List.TFAE [IsNoetherianRing A,
      ∀ f : ℕ →o Ideal A, ∃ n, ∀ m, n ≤ m → f n = f m,
      ∀ S : Set (Ideal A), S.Nonempty → ∃ M ∈ S, ∀ I ∈ S, ¬ M < I] := by
  tfae_have 1 ↔ 2 := (monotone_stabilizes_iff_noetherian (R := A) (M := A)).symm
  tfae_have 1 ↔ 3 := (set_has_maximal_iff_noetherian (R := A) (M := A)).symm
  tfae_finish

/-- Proposition 1.4 of Milne: every nonzero element of a noetherian integral domain that is not a
unit is a product of irreducible elements.

This restates `WfDvdMonoid.exists_factors` (with `IsNoetherianRing.wfDvdMonoid`).  Mathlib
produces a factorization only up to associates; here one irreducible factor is multiplied by the
unit to obtain an exact equality of the product with $a$. -/
@[kb "milne2020ant" "v3.08, Prop. 1.4, p. 16"]
theorem prop_1_4 {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (a : A) (ha : a ≠ 0) (hu : ¬ IsUnit a) :
    ∃ f : Multiset A, (∀ b ∈ f, Irreducible b) ∧ f.prod = a := by
  classical
  obtain ⟨f, hf, h⟩ := WfDvdMonoid.exists_factors a ha
  obtain ⟨u, hu'⟩ := h
  have hne : f ≠ 0 := by
    rintro rfl
    apply hu
    simp at hu'
    rw [← hu']
    exact u.isUnit
  obtain ⟨b, g, rfl⟩ : ∃ b g, f = b ::ₘ g := by
    obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hne
    exact ⟨b, f.erase b, (Multiset.cons_erase hb).symm⟩
  refine ⟨(b * u) ::ₘ g, ?_, ?_⟩
  · intro c hc
    rcases Multiset.mem_cons.1 hc with rfl | hc
    · exact (irreducible_mul_isUnit u.isUnit).2 (hf b (Multiset.mem_cons_self _ _))
    · exact hf c (Multiset.mem_cons_of_mem hc)
  · rw [← hu', Multiset.prod_cons, Multiset.prod_cons]; ring

/-- Proposition 1.6 of Milne: for a module $M$ over a ring $A$ the following are equivalent:
$M$ is noetherian; every ascending chain of submodules eventually becomes constant; every
nonempty set of submodules has a maximal element.

This restates `monotone_stabilizes_iff_noetherian` and `set_has_maximal_iff_noetherian`.  Mathlib
also has `isNoetherian_iff`, the well-foundedness form of the chain condition. -/
@[kb "milne2020ant" "v3.08, Prop. 1.6, p. 17"]
theorem prop_1_6_tfae (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] :
    List.TFAE [IsNoetherian A M,
      ∀ f : ℕ →o Submodule A M, ∃ n, ∀ m, n ≤ m → f n = f m,
      ∀ S : Set (Submodule A M), S.Nonempty → ∃ N ∈ S, ∀ P ∈ S, ¬ N < P] := by
  tfae_have 1 ↔ 2 := (monotone_stabilizes_iff_noetherian).symm
  tfae_have 1 ↔ 3 := (set_has_maximal_iff_noetherian).symm
  tfae_finish

/-- Proposition 1.7 of Milne: if a submodule $N$ of a module $M$ and the quotient $M/N$ are both
noetherian, then $M$ is noetherian.

This restates one direction of the equivalence `isNoetherian_iff_submodule_quotient`. -/
@[kb "milne2020ant" "v3.08, Prop. 1.7, p. 17"]
theorem prop_1_7 {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (N : Submodule A M) (hN : IsNoetherian A N) (hq : IsNoetherian A (M ⧸ N)) :
    IsNoetherian A M :=
  (isNoetherian_iff_submodule_quotient N).2 ⟨hN, hq⟩

-- Proposition 1.8: over a noetherian ring every finitely generated module is noetherian.
-- Mathlib's theorem has the book's hypotheses (noetherian ring, finite module) as arguments.
attribute [kb "milne2020ant" "v3.08, Prop. 1.8, p. 17"] isNoetherian_of_isNoetherianRing_of_finite

/-- Lemma 1.9(a) of Milne (Nakayama's lemma): let $A$ be a local ring, $\mathfrak a$ a proper
ideal and $M$ a finitely generated $A$-module.  If $\mathfrak a M = M$ then $M = 0$.

This restates `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`.  Mathlib is more general: it
asks only that the ideal lie inside the Jacobson radical; in a local ring that radical is the
maximal ideal, which contains every proper ideal.  Part (b) is `lemma_1_9_b`. -/
@[kb "milne2020ant" "v3.08, Lemma 1.9 (a), p. 17"]
theorem lemma_1_9_a {A : Type*} [CommRing A] [IsLocalRing A] (a : Ideal A) (ha : a ≠ ⊤)
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (h : a • (⊤ : Submodule A M) = ⊤) : Subsingleton M := by
  have hj : a ≤ (⊥ : Ideal A).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal ha
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot a ⊤
    (Module.Finite.fg_top (R := A) (M := M)) h.ge hj
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Submodule A M) := this ▸ Submodule.mem_top
  have hy : y ∈ (⊥ : Submodule A M) := this ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at hx hy
  rw [hx, hy]

/-- Lemma 1.9(b) of Milne (Nakayama's lemma): let $A$ be a local ring, $\mathfrak a$ a proper
ideal and $M$ a finitely generated $A$-module.  If $N$ is a submodule of $M$ with
$N + \mathfrak a M = M$ then $N = M$.

This restates `Submodule.le_of_le_smul_of_le_jacobson_bot`; as for part (a), Mathlib only needs
the ideal to lie in the Jacobson radical. -/
@[kb "milne2020ant" "v3.08, Lemma 1.9 (b), p. 17"]
theorem lemma_1_9_b {A : Type*} [CommRing A] [IsLocalRing A] (a : Ideal A) (ha : a ≠ ⊤)
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Submodule A M) (h : N ⊔ a • (⊤ : Submodule A M) = ⊤) : N = ⊤ := by
  have hj : a ≤ (⊥ : Ideal A).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal ha
  have := Submodule.le_of_le_smul_of_le_jacobson_bot (N := N) (N' := ⊤)
    (Module.Finite.fg_top (R := A) (M := M)) hj (by rw [h])
  exact top_le_iff.1 this

/-- Proposition 1.11 of Milne: let $S$ be a multiplicative subset of a ring $A$ and $B$ the ring
of fractions $S^{-1}A$.  For an ideal $\mathfrak a$ of $B$, extending the contraction
$\mathfrak a \cap A$ back to $B$ gives $\mathfrak a$.  For a prime ideal $\mathfrak p$ of $A$ that
is disjoint from $S$, contracting the extension $\mathfrak p B$ gives $\mathfrak p$.

This restates `IsLocalization.map_under` and `IsLocalization.under_map_of_isPrime_disjoint`.
Mathlib is more general than the book: $A$ need not be an integral domain, and $B$ is any ring
with the localization property rather than a subring of the field of fractions. -/
@[kb "milne2020ant" "v3.08, Prop. 1.11, p. 18"]
theorem prop_1_11 {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A)
    [IsLocalization S B] :
    (∀ J : Ideal B, Ideal.map (algebraMap A B) (J.comap (algebraMap A B)) = J) ∧
    (∀ p : Ideal A, p.IsPrime → Disjoint (S : Set A) p →
      (Ideal.map (algebraMap A B) p).comap (algebraMap A B) = p) :=
  ⟨fun J => IsLocalization.map_under S B J,
   fun _ hp hd => IsLocalization.under_map_of_isPrime_disjoint S B hp hd⟩

-- Proposition 1.12: extension of ideals is a bijection from the primes of $A$ disjoint from $S$
-- to the primes of $S^{-1}A$, with inverse given by contraction.  Mathlib packages this as an
-- order isomorphism between the two sets of primes.
attribute [kb "milne2020ant" "v3.08, Prop. 1.12, p. 19"] IsLocalization.orderIsoOfPrime

-- Example 1.13(a): the localization at a prime ideal is a local ring.  Part (b) of the example,
-- the lists of prime ideals of particular rings, is a set of computations and is not
-- formalized here.
attribute [kb "milne2020ant" "v3.08, Example 1.13 (a), p. 19"]
  IsLocalization.AtPrime.isLocalRing

-- Example 1.13(a): the maximal ideal of the localization at a prime ideal $\mathfrak p$ is
-- $\mathfrak p A_{\mathfrak p}$.  Part (b) of the example is not formalized here.
attribute [kb "milne2020ant" "v3.08, Example 1.13 (a), p. 19"]
  IsLocalization.AtPrime.map_eq_maximalIdeal

/-- Theorem 1.14 of Milne (Chinese remainder theorem): let $\mathfrak a_1, \dots, \mathfrak a_n$
be ideals of a ring $A$ that are relatively prime in pairs.  Then for all elements $x_1, \dots,
x_n$ the congruences $x \equiv x_i \pmod{\mathfrak a_i}$ have a simultaneous solution; the natural
map $A \to \prod A/\mathfrak a_i$ is surjective with kernel $\bigcap \mathfrak a_i$; and the
intersection equals the product $\prod \mathfrak a_i$.

This restates `Ideal.exists_forall_sub_mem_ideal` and
`Ideal.prod_eq_iInf_of_pairwise_isCoprime` (Mathlib also has the isomorphism form
`Ideal.quotientInfRingEquivPiQuotient`).  Relatively prime means `IsCoprime`, that is
$\mathfrak a_i + \mathfrak a_j = A$. -/
@[kb "milne2020ant" "v3.08, Thm. 1.14, p. 20"]
theorem thm_1_14 {A ι : Type*} [CommRing A] [Fintype ι] (a : ι → Ideal A)
    (h : Pairwise (Function.onFun IsCoprime a)) :
    (∀ x : ι → A, ∃ r : A, ∀ i, r - x i ∈ a i) ∧
    Function.Surjective (RingHom.pi fun i => Ideal.Quotient.mk (a i)) ∧
    RingHom.ker (RingHom.pi fun i => Ideal.Quotient.mk (a i)) = ⨅ i, a i ∧
    (⨅ i, a i) = ∏ i, a i := by
  refine ⟨Ideal.exists_forall_sub_mem_ideal h, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal h
      fun i => (Ideal.Quotient.mk_surjective (y i)).choose
    refine ⟨r, funext fun i => ?_⟩
    have := (Ideal.Quotient.mk_surjective (y i)).choose_spec
    simp only [RingHom.pi_apply]
    rw [← this, Ideal.Quotient.eq]
    exact hr i
  · ext x
    simp [RingHom.mem_ker, funext_iff, RingHom.pi_apply, Ideal.Quotient.eq_zero_iff_mem]
  · have := Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) (J := a)
      (by simpa using h.set_pairwise _)
    simpa using this.symm

/-- Theorem 1.15 of Milne (Chinese remainder theorem for modules): let $\mathfrak a_1, \dots,
\mathfrak a_n$ be ideals of a ring $A$ that are relatively prime in pairs, and $M$ an
$A$-module.  Then the map $M \to \prod M/\mathfrak a_i M$ is surjective with kernel
$\mathfrak a M$, where $\mathfrak a = \bigcap \mathfrak a_i$.

This restates `Ideal.pi_tensorProductMk_quotient_surjective` and
`Ideal.ker_tensorProductMk_quotient`, which are stated with the tensor products
$(A/\mathfrak a_i) \otimes_A M$, using the identification of $M/\mathfrak a_i M$ with that tensor
product given by `TensorProduct.quotTensorEquivQuotSMul` (as in the book's proof).  The book
also writes the kernel as $\prod \mathfrak a_i \cdot M$, which is the same ideal by
`thm_1_14`. -/
@[kb "milne2020ant" "v3.08, Thm. 1.15, p. 20"]
theorem thm_1_15 {A ι : Type*} [CommRing A] [Finite ι] (a : ι → Ideal A)
    (h : Pairwise (Function.onFun IsCoprime a))
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Surjective (LinearMap.pi fun i => (a i • (⊤ : Submodule A M)).mkQ) ∧
    LinearMap.ker (LinearMap.pi fun i => (a i • (⊤ : Submodule A M)).mkQ) =
      (⨅ i, a i) • (⊤ : Submodule A M) := by
  let g : M →ₗ[A] ((i : ι) → TensorProduct A (A ⧸ a i) M) :=
    LinearMap.pi fun i => (TensorProduct.mk A (A ⧸ a i) M) 1
  let e : ((i : ι) → TensorProduct A (A ⧸ a i) M) ≃ₗ[A]
      ((i : ι) → M ⧸ (a i • (⊤ : Submodule A M))) :=
    LinearEquiv.piCongrRight fun i => TensorProduct.quotTensorEquivQuotSMul M (a i)
  have hf : (LinearMap.pi fun i => (a i • (⊤ : Submodule A M)).mkQ) =
      (e : _ →ₗ[A] _) ∘ₗ g := by
    ext m i
    simp [e, g]
  have hs := Ideal.pi_tensorProductMk_quotient_surjective M a h
  have hk := Ideal.ker_tensorProductMk_quotient M a h
  rw [hf]
  refine ⟨e.surjective.comp hs, ?_⟩
  rw [LinearEquiv.ker_comp]
  exact hk

-- Lemma 1.17: the tensor product of two surjective linear maps is surjective.
attribute [kb "milne2020ant" "v3.08, Lemma 1.17, p. 22"] TensorProduct.map_surjective

end NumberFieldKB.MilneANT
