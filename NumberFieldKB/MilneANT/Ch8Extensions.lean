import NumberFieldKB.MilneANT.Ch8Basic
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: extending absolute values; finiteness theorems

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Completions are Mathlib's `AbsoluteValue.Completion` (the uniform completion of `WithAbs v`); an absolute value $w$ of
$L$ *extends* $v$ when `w.LiesOver v` (its restriction to $K$ is $v$), and then $L_w$ is a $K_v$-algebra by
`AbsoluteValue.Completion.algebraOfLiesOver`.

* **Proposition 8.1** (`Prop8_1`), **Proposition 8.2** (`Prop8_2`), **Remark 8.3** (`Remark8_3`): named statements.
* **Corollary 8.4** (`cor_8_4`, proved from `Prop8_2`).
* **Theorem 8.42** (`Theorem8_42`, named statement), **Theorem 8.43** (`thm_8_43`, Hermite, from Mathlib).

Lemma 8.6 to Aside 8.9 are in `Ch8ProductFormula.lean`.
-/

open NumberField IsDedekindDomain
open scoped TensorProduct Polynomial

namespace NumberFieldKB.MilneANT

noncomputable section

/-- Milne's standing hypothesis in Chapter 8 (p. 135): the absolute value is archimedean, or nonarchimedean and
discrete (its values on $K^\times$ form a discrete subgroup of $\mathbb R_{>0}$, equivalently $1$ is isolated among
them: some $r < 1$ bounds every value $< 1$). -/
def IsArchOrDiscrete {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : Prop :=
  ¬ IsNonarchimedean v ∨ ∃ r : ℝ, r < 1 ∧ ∀ x : K, v x < 1 → v x ≤ r

/-- The extensions of `v` to `L`. -/
abbrev Extensions {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L] (v : AbsoluteValue K ℝ) :=
  {w : AbsoluteValue L ℝ // w.LiesOver v}

/-- The completion $L_w$ of an extension $w$ of $v$ as a $K_v$-algebra. -/
@[instance_reducible]
def extAlgebra {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] (v : AbsoluteValue K ℝ)
    (w : Extensions L v) : Algebra v.Completion w.1.Completion :=
  haveI := w.2
  AbsoluteValue.Completion.algebraOfLiesOver v w.1

/-- **Proposition 8.1** (named statement): let $|\cdot|$ be an absolute value on $K$ (archimedean or discrete
nonarchimedean), $L = K[\alpha]$ a finite separable extension, $f$ the minimal polynomial of $\alpha$ over $K$. There
is a natural one-to-one correspondence between the extensions of $|\cdot|$ to $L$ and the monic irreducible factors of
$f$ in $\hat K[X]$: the extension $w$ corresponds to the minimal polynomial of $\alpha$ over $\hat K$ in $L_w$. -/
@[kb "milne2020ant" "v3.08, Prop. 8.1, p. 136"]
structure Prop8_1 : Prop where
  bij : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : AbsoluteValue K ℝ) (_ : IsArchOrDiscrete v) (α : L) (_ : IntermediateField.adjoin K {α} = ⊤),
    ∃ Φ : Extensions L v ≃ {g : v.Completion[X] // g.Monic ∧ Irreducible g ∧
        g ∣ (minpoly K α).map (algebraMap K v.Completion)},
      ∀ w : Extensions L v,
        letI := extAlgebra v w
        (Φ w).1 = minpoly v.Completion (α : w.1.Completion)

/-- **Proposition 8.2** (named statement): let $|\cdot|$ be an absolute value on $K$ (archimedean or discrete
nonarchimedean) and $L/K$ finite separable. Then $|\cdot|$ has finitely many extensions $|\cdot|_1, \dots,
|\cdot|_g$ to $L$, and $L \otimes_K \hat K \cong \prod_i L_i$ ($L_i$ the completion for $|\cdot|_i$), by
$a \otimes b \mapsto (a b, \dots, a b)$. Written with the factors in the order $\hat K \otimes_K L$. -/
@[kb "milne2020ant" "v3.08, Prop. 8.2, p. 136"]
structure Prop8_2 : Prop where
  finite : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : AbsoluteValue K ℝ) (_ : IsArchOrDiscrete v), Finite (Extensions L v)
  tensor : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : AbsoluteValue K ℝ) (_ : IsArchOrDiscrete v),
    letI : ∀ w : Extensions L v, Algebra v.Completion w.1.Completion := extAlgebra v
    ∃ e : v.Completion ⊗[K] L ≃ₐ[v.Completion] ((w : Extensions L v) → w.1.Completion),
      ∀ (b : v.Completion) (a : L) (w : Extensions L v),
        e (b ⊗ₜ a) w = algebraMap v.Completion w.1.Completion b * (a : w.1.Completion)

/-- The determinant of a block diagonal matrix with blocks of possibly different sizes is the product of the
determinants of the blocks. -/
theorem det_blockDiagonal'_aux {F : Type*} [CommRing F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (A : ∀ i, Matrix (κ i) (κ i) F) :
    (Matrix.blockDiagonal' A).det = ∏ i, (A i).det := by
  classical
  let _ : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have hb : (Matrix.blockDiagonal' A).BlockTriangular Sigma.fst := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hij
    have : i ≠ j := ne_of_gt hij
    simp [Matrix.blockDiagonal'_apply, this]
  rw [hb.det_fintype]
  refine Finset.prod_congr rfl fun k _ => ?_
  let e : {a : Σ i, κ i // a.1 = k} ≃ κ k :=
    { toFun := fun a => a.2 ▸ a.1.2
      invFun := fun x => ⟨⟨k, x⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨i, a⟩, h⟩
        subst h
        rfl
      right_inv := fun x => rfl }
  rw [← Matrix.det_reindex_self e]
  congr 1
  ext x y
  obtain ⟨x, hx⟩ := e.surjective x
  obtain ⟨y, hy⟩ := e.surjective y
  subst hx hy
  simp [e, Matrix.toSquareBlock_def, Matrix.blockDiagonal'_apply]

/-- The norm and trace of an element of a finite product of finite-dimensional algebras over a field are the
product, respectively the sum, of the componentwise norms and traces. -/
theorem norm_trace_pi_aux {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, CommRing (M i)] [∀ i, Algebra F (M i)] [∀ i, Module.Finite F (M i)]
    (x : ∀ i, M i) :
    Algebra.norm F x = ∏ i, Algebra.norm F (x i) ∧
      Algebra.trace F _ x = ∑ i, Algebra.trace F _ (x i) := by
  have hl : Algebra.lmul F (∀ i, M i) x =
      LinearMap.pi (fun i => (Algebra.lmul F (M i) (x i)).comp (LinearMap.proj i)) := by
    ext y i
    simp
  let b := fun i => Module.finBasis F (M i)
  have hm : LinearMap.toMatrix (Pi.basis b) (Pi.basis b) (Algebra.lmul F (∀ i, M i) x) =
      Matrix.blockDiagonal' (fun i => LinearMap.toMatrix (b i) (b i) (Algebra.lmul F (M i) (x i))) := by
    rw [hl]
    ext ⟨i, a⟩ ⟨j, c⟩
    by_cases h : i = j
    · subst h
      simp [LinearMap.toMatrix_apply, Matrix.blockDiagonal'_apply, Pi.basis_apply, Pi.basis_repr]
    · simp [LinearMap.toMatrix_apply, Matrix.blockDiagonal'_apply, h, Pi.basis_apply, Pi.basis_repr]
  constructor
  · rw [Algebra.norm_apply, ← LinearMap.det_toMatrix (Pi.basis b), hm, det_blockDiagonal'_aux]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Algebra.norm_apply, LinearMap.det_toMatrix]
  · rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace F (Pi.basis b), hm,
      Matrix.trace_blockDiagonal']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace F (b i)]

/-- **Corollary 8.4** (proved from `Prop8_2`): in the situation of Proposition 8.2, for $\alpha \in L$,
$\mathrm{Nm}_{L/K}\alpha = \prod_i \mathrm{Nm}_{L_i/\hat K}\alpha$ and $\mathrm{Tr}_{L/K}\alpha =
\sum_i\mathrm{Tr}_{L_i/\hat K}\alpha$ (equalities in $\hat K$). -/
@[kb "milne2020ant" "v3.08, Cor. 8.4, p. 136"]
theorem cor_8_4 (h : Prop8_2) (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (v : AbsoluteValue K ℝ) (hv : IsArchOrDiscrete v) (α : L) :
    letI : ∀ w : Extensions L v, Algebra v.Completion w.1.Completion := extAlgebra v
    haveI := h.finite K L v hv
    haveI := Fintype.ofFinite (Extensions L v)
    algebraMap K v.Completion (Algebra.norm K α) =
        ∏ w : Extensions L v, Algebra.norm v.Completion (α : w.1.Completion) ∧
      algebraMap K v.Completion (Algebra.trace K L α) =
        ∑ w : Extensions L v, Algebra.trace v.Completion w.1.Completion (α : w.1.Completion) := by
  classical
  let _ : ∀ w : Extensions L v, Algebra v.Completion w.1.Completion := extAlgebra v
  have := h.finite K L v hv
  have := Fintype.ofFinite (Extensions L v)
  obtain ⟨e, he⟩ := h.tensor K L v hv
  have hfin : ∀ w : Extensions L v, Module.Finite v.Completion w.1.Completion := fun w =>
    Module.Finite.of_surjective ((LinearMap.proj w).comp e.toLinearMap)
      ((Function.surjective_eval w).comp e.surjective)
  have hα : e ((1 : v.Completion) ⊗ₜ[K] α) = fun w : Extensions L v => (α : w.1.Completion) := by
    funext w
    simp [he]
  have hn : Algebra.norm v.Completion ((1 : v.Completion) ⊗ₜ[K] α) =
      algebraMap K v.Completion (Algebra.norm K α) := by
    rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul,
      LinearMap.det_baseChange]
  have ht : Algebra.trace v.Completion _ ((1 : v.Completion) ⊗ₜ[K] α) =
      algebraMap K v.Completion (Algebra.trace K L α) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
      LinearMap.trace_baseChange]
  have hp := norm_trace_pi_aux (F := v.Completion) (fun w : Extensions L v => (α : w.1.Completion))
  rw [← hα, Algebra.norm_eq_of_algEquiv, Algebra.trace_eq_of_algEquiv, hn, ht] at hp
  convert hp using 3 <;> congr!

/-- **Remark 8.3** (named statement): let $L/K$ be an extension of number fields with $\mathcal O_L =
\mathcal O_K[\alpha]$ and $\mathfrak p$ a prime of $K$. The extensions of $\lVert\cdot\rVert_{\mathfrak p}$ to $L$
correspond to the primes $\mathfrak P_i = (\mathfrak p, g_i(\alpha))$ above $\mathfrak p$ (Kummer–Dedekind): every
extension is equivalent to the $\mathfrak P$-adic absolute value of exactly one prime $\mathfrak P \mid \mathfrak p$,
and for each such $\mathfrak P$ the corresponding irreducible factor of $f$ over $K_{\mathfrak p}$ (Proposition 8.1),
the minimal polynomial of $\alpha$ over $K_{\mathfrak p}$ in $L_w$, has degree $e(\mathfrak P/\mathfrak p)
f(\mathfrak P/\mathfrak p)$, the degree of $g_i^{e_i}$. -/
@[kb "milne2020ant" "v3.08, Rem. 8.3, p. 136"]
structure Remark8_3 : Prop where
  corr : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (α : 𝓞 L)
    (_ : Algebra.adjoin (𝓞 K) {α} = ⊤) (𝔭 : HeightOneSpectrum (𝓞 K)),
    (∀ w : Extensions L (FinitePlace.mk 𝔭).1, ∃! P : HeightOneSpectrum (𝓞 L),
      P.asIdeal.LiesOver 𝔭.asIdeal ∧ w.1.IsEquiv (FinitePlace.mk P).1) ∧
    ∀ P : HeightOneSpectrum (𝓞 L), P.asIdeal.LiesOver 𝔭.asIdeal →
      ∃ w : Extensions L (FinitePlace.mk 𝔭).1, w.1.IsEquiv (FinitePlace.mk P).1 ∧
        letI := extAlgebra (FinitePlace.mk 𝔭).1 w
        (minpoly (FinitePlace.mk 𝔭).1.Completion ((α : L) : w.1.Completion)).natDegree =
          P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)

/-! ## Theorems 8.42 and 8.43 -/

/-- **Theorem 8.42** (named statement): for a number field $K$, an integer $N$ and a finite set $S$ of finite primes
of $K$, there are only finitely many extensions $L \supseteq K$ of degree $N$ unramified outside $S$, up to
$K$-isomorphism. Stated inside a fixed algebraic closure $\bar K$ (subfields of $\bar K$ are the extensions up to
$K$-isomorphism); "unramified outside $S$" refers to the finite primes (Milne's $S$ is a set of primes of $K$; the
infinite places impose no finiteness condition). -/
@[kb "milne2020ant" "v3.08, Thm. 8.42, p. 151"]
structure Theorem8_42 : Prop where
  finite : ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))),
    {L : IntermediateField K (AlgebraicClosure K) | FiniteDimensional K L ∧ Module.finrank K L = N ∧
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ S → Algebra.IsUnramifiedIn (𝓞 L) 𝔭.asIdeal}.Finite

/-- **Theorem 8.43** (Hermite, 1857): there are only finitely many number fields with a given discriminant, up to
isomorphism: inside an algebraic closure of $\mathbb Q$, finitely many subfields have discriminant $d$. From Mathlib's
`NumberField.finite_of_discr_bdd` (which bounds $|d_K|$ instead of fixing it). -/
@[kb "milne2020ant" "v3.08, Thm. 8.43, p. 151"]
theorem thm_8_43 (d : ℤ) :
    {K : {F : IntermediateField ℚ (AlgebraicClosure ℚ) // FiniteDimensional ℚ F} |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      NumberField.discr K = d}.Finite := by
  refine (NumberField.finite_of_discr_bdd (AlgebraicClosure ℚ) d.natAbs).subset ?_
  intro K hK
  simp only [Set.mem_setOf_eq] at hK ⊢
  rw [hK, Int.abs_eq_natAbs]

end

end NumberFieldKB.MilneANT
