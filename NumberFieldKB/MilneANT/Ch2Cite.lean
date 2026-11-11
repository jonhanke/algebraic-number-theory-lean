import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import QuadFormsKB.Citation
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Milne, Algebraic Number Theory, Chapter 2: results in Mathlib

Chapter 2 of J. S. Milne, *Algebraic Number Theory* (version 3.08, 2020; bibliography key
`milne2020ant`) treats rings of integers.  This file cites the items of that chapter which are
already available in Mathlib.

Convention.
* When one Mathlib declaration states the book's result in essentially the book's form, the
  declaration is tagged directly with `attribute [kb "milne2020ant" ...]`, with a comment saying
  which item it is and how the form differs.
* When the book's form differs (several Mathlib results combined, a different packaging of the
  hypotheses, an equivalence versus one direction, a statement for a number field versus a general
  field), a short restating theorem in the book's form is proved from the Mathlib results, and
  that theorem carries the tag.
* The page in each locator is the printed page of the book, which is the page of the file minus
  two.
* Where an audit row says that only part of an item is in Mathlib, only that part is cited and
  the comment says which part is left.
-/

namespace NumberFieldKB.MilneANT

/-- Theorem 2.1 of Milne: the elements of a field $L$ that are integral over a subring $A$ form a
ring.

This restates the definition `integralClosure`, which is a subalgebra of $L$ over $A$ whose
elements are exactly the integral ones (closure under sums and products is `IsIntegral.add` and
`IsIntegral.mul`).  Mathlib needs only commutative rings, not an integral domain inside a field. -/
@[kb "milne2020ant" "v3.08, Thm. 2.1, p. 25"]
theorem thm_2_1 (A L : Type*) [CommRing A] [CommRing L] [Algebra A L] :
    ∃ S : Subalgebra A L, ∀ x : L, x ∈ S ↔ IsIntegral A x :=
  ⟨integralClosure A L, fun _ => Iff.rfl⟩

/-- Theorem 2.2 of Milne (the symmetric function theorem): every symmetric polynomial in $r$
variables over a ring $A$ is a polynomial, with coefficients in $A$, in the elementary symmetric
polynomials $S_1, \dots, S_r$.

This restates `MvPolynomial.esymmAlgHom_surjective`.  Variables are indexed from $0$ by `Fin r`,
so the polynomial $S_{i+1}$ of the book is `MvPolynomial.esymm (Fin r) A (i + 1)` for
$i = 0, \dots, r - 1$.  The substitution of the $S_i$ into $Q$ is `MvPolynomial.bind₁`. -/
@[kb "milne2020ant" "v3.08, Thm. 2.2, p. 25"]
theorem thm_2_2 {A : Type*} [CommRing A] (r : ℕ) (P : MvPolynomial (Fin r) A)
    (hP : P.IsSymmetric) :
    ∃ Q : MvPolynomial (Fin r) A,
      MvPolynomial.bind₁ (fun i : Fin r => MvPolynomial.esymm (Fin r) A (i + 1)) Q = P := by
  obtain ⟨Q, hQ⟩ := MvPolynomial.esymmAlgHom_surjective A (σ := Fin r) (n := r) (by simp)
    ⟨P, (MvPolynomial.mem_symmetricSubalgebra _).2 hP⟩
  refine ⟨Q, ?_⟩
  have h1 := congrArg Subtype.val hQ
  have h2 : (MvPolynomial.symmetricSubalgebra (Fin r) A).val.comp
      (MvPolynomial.esymmAlgHom (Fin r) A r) =
      MvPolynomial.bind₁ (fun i : Fin r => MvPolynomial.esymm (Fin r) A (i + 1)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.esymmAlgHom]
  rw [← h2]
  exact h1

/-- Proposition 2.3 of Milne: let $\alpha_1, \dots, \alpha_n$ be the roots, in a field containing
an integral domain $A$, of a monic polynomial over $A$.  Then every polynomial in the $\alpha_i$
with coefficients in $A$ is integral over $A$.

This restates `roots_mem_integralClosure` together with the closure of the integral elements under
the ring operations (`integralClosure` is a subalgebra).  Mathlib needs neither the symmetric
function theorem nor an algebraically closed field; the algebraic closure assumption is kept here
only to match the book. -/
@[kb "milne2020ant" "v3.08, Prop. 2.3, p. 26"]
theorem prop_2_3 {A Ω : Type*} [CommRing A] [IsDomain A] [Field Ω] [IsAlgClosed Ω]
    [Algebra A Ω] {n : ℕ} (f : Polynomial A) (hf : f.Monic) (α : Fin n → Ω)
    (hα : ∀ i, α i ∈ f.aroots Ω) (g : MvPolynomial (Fin n) A) :
    IsIntegral A (MvPolynomial.aeval α g) := by
  have : (MvPolynomial.aeval α : MvPolynomial (Fin n) A →ₐ[A] Ω).range ≤ integralClosure A Ω := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact roots_mem_integralClosure hf (hα i))
  exact this ⟨g, rfl⟩

/-- Proposition 2.4 of Milne: an element $\alpha$ of a field $L$ containing $A$ is integral over
$A$ if and only if there is a nonzero finitely generated $A$-submodule $M$ of $L$ with
$\alpha M \subseteq M$.

This restates `isIntegral_of_smul_mem_submodule` for the direction from a stable module to
integrality, and the finite generation of $A[\alpha]$ for an integral element (which is stable
under multiplication by $\alpha$) for the other direction. -/
@[kb "milne2020ant" "v3.08, Prop. 2.4, p. 26"]
theorem prop_2_4 {A L : Type*} [CommRing A] [Field L] [Algebra A L] (α : L) :
    IsIntegral A α ↔ ∃ M : Submodule A L, M ≠ ⊥ ∧ M.FG ∧ ∀ m ∈ M, α * m ∈ M := by
  constructor
  · intro h
    refine ⟨Subalgebra.toSubmodule (Algebra.adjoin A {α}), ?_, ?_, ?_⟩
    · intro h0
      have : (1 : L) ∈ Subalgebra.toSubmodule (Algebra.adjoin A {α}) :=
        (Algebra.adjoin A {α}).one_mem
      rw [h0] at this
      simp at this
    · exact h.fg_adjoin_singleton
    · intro m hm
      exact Subalgebra.mul_mem _ (Algebra.self_mem_adjoin_singleton A α) hm
  · rintro ⟨M, h0, hfg, hM⟩
    exact isIntegral_of_smul_mem_submodule (R := A) (A := L) (M := L) M h0 hfg α
      (fun m hm => by simpa using hM m hm)

-- Definition 2.5, first sentence: the integral closure of $A$ in $L$ (the ring of elements of
-- $L$ integral over $A$).  Mathlib defines it as a subalgebra.
attribute [kb "milne2020ant" "v3.08, Def. 2.5, p. 28"] integralClosure

-- Definition 2.5, second sentence: the ring of integers of a number field, the integral closure
-- of the integers in the field.
attribute [kb "milne2020ant" "v3.08, Def. 2.5, p. 28"] NumberField.RingOfIntegers

/-- Proposition 2.6 of Milne: let $K$ be the field of fractions of an integral domain $A$ and
$L$ a field containing $K$.  If $\alpha \in L$ is algebraic over $K$, then there is a nonzero
$d \in A$ such that $d\alpha$ is integral over $A$.

This restates `IsAlgebraic.exists_integral_multiple`, which asks for algebraicity over $A$; that
is equivalent to algebraicity over $K$ by `IsFractionRing.isAlgebraic_iff`. -/
@[kb "milne2020ant" "v3.08, Prop. 2.6, p. 28"]
theorem prop_2_6 {A K L : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (α : L) (hα : IsAlgebraic K α) :
    ∃ d : A, d ≠ 0 ∧ IsIntegral A (algebraMap A L d * α) := by
  obtain ⟨y, hy, hint⟩ := ((IsFractionRing.isAlgebraic_iff A K L).2 hα).exists_integral_multiple
  exact ⟨y, hy, by simpa [Algebra.smul_def] using hint⟩

/-- Corollary 2.7 of Milne: let $A$ be an integral domain with field of fractions $K$, and let
$L$ be an algebraic extension field of $K$.  Then $L$ is the field of fractions of the integral
closure of $A$ in $L$.

This restates `integralClosure.isFractionRing_of_algebraic`, which asks for $L$ algebraic over
$A$ with the structure map injective; both follow from the hypotheses here. -/
@[kb "milne2020ant" "v3.08, Cor. 2.7, p. 28"]
theorem cor_2_7 {A K L : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L] : IsFractionRing (integralClosure A L) L := by
  have : Algebra.IsAlgebraic A L :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff A K L).2 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  refine integralClosure.isFractionRing_of_algebraic ?_
  intro x hx
  rw [IsScalarTower.algebraMap_apply A K L] at hx
  have := (map_eq_zero_iff _ (algebraMap K L).injective).1 hx
  exact (map_eq_zero_iff _ (IsFractionRing.injective A K)).1 this

-- Definition 2.8: a ring is integrally closed if it equals its integral closure in its field of
-- fractions.  Mathlib's class `IsIntegrallyClosed` is this notion.
attribute [kb "milne2020ant" "v3.08, Def. 2.8, p. 28"] IsIntegrallyClosed

-- Proposition 2.9: a unique factorization domain is integrally closed.  The book's remark that
-- this covers principal ideal domains follows from the instance that a principal ideal domain
-- is a unique factorization domain.
attribute [kb "milne2020ant" "v3.08, Prop. 2.9, p. 28"]
  UniqueFactorizationMonoid.instIsIntegrallyClosed

/-- Proposition 2.11 of Milne: let $A$ be an integrally closed integral domain with field of
fractions $K$, and $L$ a finite extension of $K$.  An element $\alpha$ of $L$ is integral over
$A$ if and only if its minimal polynomial over $K$ has all its coefficients in $A$.

This restates `minpoly.isIntegrallyClosed_eq_field_fractions'` for the forward direction; the
converse is proved by lifting the minimal polynomial to a monic polynomial over $A$. -/
@[kb "milne2020ant" "v3.08, Prop. 2.11, p. 29"]
theorem prop_2_11 {A K L : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] (α : L) :
    IsIntegral A α ↔ ∀ n, (minpoly K α).coeff n ∈ Set.range (algebraMap A K) := by
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩
  · intro h
    have hl : minpoly K α ∈ Polynomial.lifts (algebraMap A K) :=
      Polynomial.lifts_iff_coeff_lifts _ |>.2 h
    obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).1 hl
    have hm : q.Monic := Polynomial.monic_of_injective (IsFractionRing.injective A K)
      (hq ▸ minpoly.monic (Algebra.IsIntegral.isIntegral (R := K) α))
    refine ⟨q, hm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq]
    exact minpoly.aeval K α

/-- Remark 2.12 of Milne, forward direction only: if $\alpha$ is an integral element of a number
field (in particular of $\mathbb{Q}[\sqrt{d}]$), then its trace and its norm to $\mathbb{Q}$ are
integers.

This restates `Algebra.isIntegral_trace` and `Algebra.isIntegral_norm` together with the fact that
$\mathbb{Z}$ is integrally closed.  The converse for quadratic fields (an element whose trace and
norm are integers is integral) is the other half of the remark and is not proved here. -/
@[kb "milne2020ant" "v3.08, Remark 2.12, p. 29"]
theorem remark_2_12_forward (K : Type*) [Field K] [NumberField K] (α : K)
    (hα : IsIntegral ℤ α) :
    (∃ t : ℤ, (t : ℚ) = Algebra.trace ℚ K α) ∧ (∃ n : ℤ, (n : ℚ) = Algebra.norm ℚ α) := by
  constructor
  · exact (IsIntegrallyClosed.isIntegral_iff (K := ℚ)).1 (Algebra.isIntegral_trace hα)
  · exact (IsIntegrallyClosed.isIntegral_iff (K := ℚ)).1 (Algebra.isIntegral_norm ℚ hα)

-- Proposition 2.13: an algebra that is integral and finitely generated as an algebra is finitely
-- generated as a module.  Mathlib states it with the two hypotheses as typeclass arguments.
attribute [kb "milne2020ant" "v3.08, Prop. 2.13, p. 29"] Algebra.IsIntegral.finite

-- Lemma 2.14: if $B$ is a finitely generated $A$-module and $C$ a finitely generated
-- $B$-module, then $C$ is a finitely generated $A$-module.
attribute [kb "milne2020ant" "v3.08, Lemma 2.14, p. 30"] Module.Finite.trans

-- Proposition 2.15: transitivity of integrality, if $B$ is integral over $A$ and $C$ is integral
-- over $B$ then $C$ is integral over $A$.  Mathlib states it for rings in general, not only
-- integral domains.
attribute [kb "milne2020ant" "v3.08, Prop. 2.15, p. 30"] Algebra.IsIntegral.trans

/-- Corollary 2.16 of Milne: the integral closure of an integral domain $A$ in an algebraic
extension field $L$ of its field of fractions $K$ is integrally closed.

The proof follows the book: by `cor_2_7` the field $L$ is the field of fractions of the integral
closure, and the integral closure of the integral closure is trivial (`integralClosure_idem`).
Mathlib's `integralClosure.isIntegrallyClosedOfFiniteExtension` is the same statement for finite
extensions. -/
@[kb "milne2020ant" "v3.08, Cor. 2.16, p. 30"]
theorem cor_2_16 {A K L : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L] : IsIntegrallyClosed (integralClosure A L) :=
  letI : IsFractionRing (integralClosure A L) L := cor_2_7 (A := A) (K := K)
  (IsIntegrallyClosed.integralClosure_eq_bot_iff L).mp integralClosure_idem

/-- Remark 2.17 of Milne: the ring of integers of a number field is integrally closed.

Mathlib provides this as an instance with an automatically generated name, found here by
instance search. -/
@[kb "milne2020ant" "v3.08, Remark 2.17, p. 30"]
theorem remark_2_17 (K : Type*) [Field K] [NumberField K] :
    IsIntegrallyClosed (NumberField.RingOfIntegers K) := inferInstance

-- Proposition 2.19, trace: for a finite field extension $L/K$ and $\beta \in L$, the trace of
-- $\beta$ is $r$ times the sum of the roots of its minimal polynomial, where $r$ is the degree
-- of $L$ over $K[\beta]$.  Mathlib states this after mapping into a field over which the minimal
-- polynomial splits.
attribute [kb "milne2020ant" "v3.08, Prop. 2.19, p. 31"] trace_eq_sum_roots

-- Proposition 2.19, norm: the norm of $\beta$ is the $r$-th power of the product of the roots of
-- its minimal polynomial.  Same form as the trace statement.
attribute [kb "milne2020ant" "v3.08, Prop. 2.19, p. 31"] Algebra.norm_eq_prod_roots

-- Corollary 2.20, trace: for a finite separable extension the trace is the sum of the images
-- under all the embeddings.  Mathlib uses an algebraically closed target field instead of a big
-- Galois extension.
attribute [kb "milne2020ant" "v3.08, Cor. 2.20, p. 32"] trace_eq_sum_embeddings

-- Corollary 2.20, norm: the norm is the product of the images under all the embeddings.
attribute [kb "milne2020ant" "v3.08, Cor. 2.20, p. 32"] Algebra.norm_eq_prod_embeddings

/-- Corollary 2.21 of Milne: let $A$ be an integrally closed integral domain with field of
fractions $K$, and $L$ a finite extension of $K$.  If $\beta \in L$ is integral over $A$, then the
trace and the norm of $\beta$ from $L$ to $K$ lie in $A$.

This restates `Algebra.isIntegral_trace` and `Algebra.isIntegral_norm` (integrality over $A$)
together with the fact that $A$ is integrally closed. -/
@[kb "milne2020ant" "v3.08, Cor. 2.21, p. 32"]
theorem cor_2_21 {A K L : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] (β : L) (hβ : IsIntegral A β) :
    (∃ a : A, algebraMap A K a = Algebra.trace K L β) ∧
    (∃ a : A, algebraMap A K a = Algebra.norm K β) := by
  constructor
  · exact (IsIntegrallyClosed.isIntegral_iff (K := K)).1 (Algebra.isIntegral_trace hβ)
  · exact (IsIntegrallyClosed.isIntegral_iff (K := K)).1 (Algebra.isIntegral_norm K hβ)

-- Lemma 2.23: changing the family by a matrix multiplies the discriminant by the square of the
-- determinant.  Mathlib writes the new family as the row vector of old elements times the
-- matrix (with the entries mapped into the larger ring); this is the book's formula up to the
-- indexing convention of the matrix.
attribute [kb "milne2020ant" "v3.08, Lemma 2.23, p. 33"] Algebra.discr_of_matrix_vecMul

-- Proposition 2.26, first part: the discriminant of a basis is the square of the determinant of
-- the matrix of the embeddings of the basis elements.  Mathlib uses an algebraically closed
-- field in place of a big Galois extension.
attribute [kb "milne2020ant" "v3.08, Prop. 2.26, p. 34"]
  Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two

-- Proposition 2.26, second part: for a finite separable extension the discriminant of a basis is
-- nonzero.
attribute [kb "milne2020ant" "v3.08, Prop. 2.26, p. 34"] Algebra.discr_not_zero_of_basis

-- Corollary 2.27, only the case of a number field (the integers as base ring): the discriminant
-- of a number field is nonzero.  The book states it for the integral closure of a general ring
-- $A$ which is free over $A$; that general case is not packaged in Mathlib and is not cited here.
attribute [kb "milne2020ant" "v3.08, Cor. 2.27, p. 34"] NumberField.discr_ne_zero

-- Remark 2.28(a): for a finite separable extension the trace pairing is nondegenerate.  Part (b),
-- that the discriminant of an inseparable extension is zero, is not cited here (Mathlib has that
-- the trace itself vanishes, `Algebra.trace_eq_zero_of_not_isSeparable`).
attribute [kb "milne2020ant" "v3.08, Remark 2.28 (a), p. 34"] traceForm_nondegenerate

-- Proposition 2.29, the sandwich: the integral closure lies inside the module spanned by the
-- trace dual basis of a basis of integral elements.  The first inclusion of the book (the
-- module spanned by the basis itself lies in the integral closure) is immediate.
attribute [kb "milne2020ant" "v3.08, Prop. 2.29, p. 35"]
  IsIntegralClosure.range_le_span_dualBasis

/-- Proposition 2.29 of Milne, the conclusion: let $A$ be an integrally closed integral domain
with field of fractions $K$, and $C$ the integral closure of $A$ in a finite separable extension
$L$ of $K$ of degree $m$.  If $A$ is noetherian then $C$ is a finitely generated $A$-module; if
$A$ is a principal ideal domain then $C$ is a free $A$-module of rank $m$.

This restates `IsIntegralClosure.finite`, `IsIntegralClosure.module_free` and
`IsIntegralClosure.rank`.  The sandwich between free modules used in the proof is
`IsIntegralClosure.range_le_span_dualBasis`.  Mathlib asks explicitly that $L$ be torsion free
over $A$, which holds automatically in the book's setting. -/
@[kb "milne2020ant" "v3.08, Prop. 2.29, p. 35"]
theorem prop_2_29 {A K L C : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree A L] [CommRing C] [Algebra C L] [Algebra A C]
    [IsScalarTower A C L] [IsIntegralClosure C A L] :
    (IsNoetherianRing A → Module.Finite A C) ∧
    (IsPrincipalIdealRing A → Module.Free A C ∧ Module.finrank A C = Module.finrank K L) :=
  ⟨fun _ => IsIntegralClosure.finite A K L C,
   fun _ => ⟨IsIntegralClosure.module_free A K L C, IsIntegralClosure.rank A K L C⟩⟩

/-- Corollary 2.30 of Milne: the ring of integers of a number field $L$ is the largest subring
of $L$ that is finitely generated as a $\mathbb{Z}$-module.

Stated as: the ring of integers is a finitely generated $\mathbb{Z}$-module (this is
`IsIntegralClosure.finite`), and every subring of $L$ that is a finitely generated
$\mathbb{Z}$-module consists of elements of the ring of integers (this is `IsIntegral.of_mem_of_fg`).
A subring of $L$ is the same as a $\mathbb{Z}$-subalgebra. -/
@[kb "milne2020ant" "v3.08, Cor. 2.30, p. 35"]
theorem cor_2_30 (L : Type*) [Field L] [NumberField L] :
    Module.Finite ℤ (NumberField.RingOfIntegers L) ∧
    ∀ B : Subalgebra ℤ L, Module.Finite ℤ B →
      ∀ b ∈ B, b ∈ Set.range (algebraMap (NumberField.RingOfIntegers L) L) := by
  refine ⟨inferInstance, fun B hB b hb => ?_⟩
  have hint : IsIntegral ℤ b := by
    refine IsIntegral.of_mem_of_fg B ?_ b hb
    exact Module.Finite.iff_fg.1 hB
  exact ⟨⟨b, hint⟩, rfl⟩

-- Definition 2.32: an integral basis of a number field is a $\mathbb{Z}$-basis of its ring of
-- integers.  The declaration is the chosen such basis.
attribute [kb "milne2020ant" "v3.08, Def. 2.32, p. 36"] NumberField.RingOfIntegers.basis

-- Proposition 2.34, second equality: the discriminant of the power basis of a separable
-- extension is a sign times the norm of the derivative of the minimal polynomial at the
-- generator.  Mathlib states it for a power basis of a finite separable extension.
attribute [kb "milne2020ant" "v3.08, Prop. 2.34, p. 37"] Algebra.discr_powerBasis_eq_norm

-- Proposition 2.34, first equality: the discriminant of the power basis is the product of the
-- squared differences of the roots (the images of the generator under the embeddings into an
-- algebraically closed field).
attribute [kb "milne2020ant" "v3.08, Prop. 2.34, p. 37"] Algebra.discr_powerBasis_eq_prod

-- Remark 2.42, the part that is formalized: isomorphic number fields have the same discriminant.
-- The claims about the degree, the four cubic fields of discriminant $4027$ and the discriminant
-- bound for polynomials are not formalized.  This is the version for ring isomorphisms.
attribute [kb "milne2020ant" "v3.08, Remark 2.42, p. 40"] NumberField.discr_eq_discr_of_ringEquiv

-- Remark 2.42: the same statement for isomorphisms over the rationals.
attribute [kb "milne2020ant" "v3.08, Remark 2.42, p. 40"] NumberField.discr_eq_discr_of_algEquiv

end NumberFieldKB.MilneANT
