import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: the primes of a number field; the product formula

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

* **Prime (place) of a field** (prose definition, p. 111; `MilnePlace`): an equivalence class of nontrivial absolute
  values. **Lying over** (prose definition, p. 112; `MilnePlace.LiesOver`): the restriction of $|\cdot|_w$ to $K$ is
  equivalent to $|\cdot|_v$.
* **Theorem 7.14** (`Theorem7_14`, `thm_7_14`): the primes of a number field are exactly the finite places
  (one for each nonzero prime ideal) and the infinite places (one for each real embedding and each conjugate pair of
  complex embeddings). Milne proves it in Chapter 8. The exhaustiveness (every nontrivial absolute value is
  equivalent to one of Mathlib's places) is the named statement `Theorem7_14`; that the map from Mathlib's places to
  primes is injective is proved (`placeOf_injective`).
* **Lemma 7.16** (`lemma_7_16a`, `Lemma7_16b`): finitely many primes lie over a given one; the norm formula
  $\prod_{w \mid v} |\alpha|_w = |\operatorname{Nm}_{L/K}\alpha|_v$ (named statement; Milne proves it in Chapter 8).
* **Remark 7.17** (`Remark7_17a`, `Remark7_17b`): the product formula for function fields (named statements).
-/

open NumberField

namespace NumberFieldKB.MilneANT

/-! ## Primes (places) of a field -/

/-- Equivalence of absolute values (`AbsoluteValue.IsEquiv`), as a setoid on the nontrivial real absolute values of
$K$. -/
def absValueSetoid (K : Type*) [Field K] : Setoid {v : AbsoluteValue K ℝ // v.IsNontrivial} where
  r v w := v.1.IsEquiv w.1
  iseqv := ⟨fun v => AbsoluteValue.IsEquiv.refl v.1, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **Prime (place) of a field** (prose definition, Milne p. 111): an equivalence class of (nontrivial) absolute
values on $K$. Milne says "an equivalence class of absolute values"; the trivial absolute value, which is equivalent
only to itself, is tacitly excluded (it gives no prime of a number field in Theorem 7.14). -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of a prime of a number field, p. 111"]
def MilnePlace (K : Type*) [Field K] : Type _ := Quotient (absValueSetoid K)

/-- The restriction of an absolute value of $L$ to a subfield $K$ (via `algebraMap K L`). -/
def AbsoluteValue.restrictMilne {K L : Type*} [Field K] [Field L] [Algebra K L] (w : AbsoluteValue L ℝ) :
    AbsoluteValue K ℝ :=
  w.comp (algebraMap K L).injective

/-- **A prime $w$ of $L$ lies over (divides) a prime $v$ of $K$** (prose definition, Milne p. 112): the restriction of
$|\cdot|_w$ to $K$ is equivalent to $|\cdot|_v$. Well defined on classes. -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of w dividing v, p. 112"]
def MilnePlace.LiesOver {K L : Type*} [Field K] [Field L] [Algebra K L] (w : MilnePlace L) (v : MilnePlace K) :
    Prop :=
  Quotient.liftOn₂ w v (fun w v => (AbsoluteValue.restrictMilne (K := K) w.1).IsEquiv v.1) <| by
    intro w₁ v₁ w₂ v₂ hw hv
    apply propext
    constructor
    · intro h x y
      have := hw (algebraMap K L x) (algebraMap K L y)
      exact (this.symm.trans (h x y)).trans (hv x y)
    · intro h x y
      have := hw (algebraMap K L x) (algebraMap K L y)
      exact (this.trans (h x y)).trans (hv x y).symm

/-! ## Theorem 7.14 -/

section NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Every finite place of a number field is a nontrivial absolute value. -/
theorem FinitePlace.isNontrivial_milne (w : FinitePlace K) : w.1.IsNontrivial := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (FinitePlace.maximalIdeal w).ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 hx0
  · have h := (FinitePlace.norm_lt_one_iff_mem K (FinitePlace.maximalIdeal w) x).2 hx
    rw [FinitePlace.norm_embedding_eq] at h
    exact h.ne

/-- Every infinite place of a number field is a nontrivial absolute value. -/
theorem InfinitePlace.isNontrivial_milne (w : InfinitePlace K) : w.1.IsNontrivial := by
  refine ⟨2, by norm_num, ?_⟩
  have h : w (2 : K) = 2 := by exact_mod_cast w.map_natCast 2
  change w (2 : K) ≠ 1
  rw [h]; norm_num

/-- The absolute value of one of Mathlib's places of $K$ (a finite place $\lVert\cdot\rVert_{\mathfrak p}$ or an
infinite place $|\sigma(\cdot)|$). -/
noncomputable def placeAbv : FinitePlace K ⊕ InfinitePlace K → AbsoluteValue K ℝ
  | .inl w => w.1
  | .inr w => w.1

theorem placeAbv_isNontrivial (w : FinitePlace K ⊕ InfinitePlace K) : (placeAbv K w).IsNontrivial := by
  cases w with
  | inl w => exact FinitePlace.isNontrivial_milne K w
  | inr w => exact InfinitePlace.isNontrivial_milne K w

/-- The prime of $K$ defined by one of Mathlib's places. -/
noncomputable def placeOf (w : FinitePlace K ⊕ InfinitePlace K) : MilnePlace K :=
  Quotient.mk _ ⟨placeAbv K w, placeAbv_isNontrivial K w⟩

/-- A finite place is never equivalent to an infinite place. -/
private theorem finite_infinite_aux (w : FinitePlace K) (u : InfinitePlace K)
    (h : (placeAbv K (.inl w)).IsEquiv (placeAbv K (.inr u))) : False := by
  have h1 : u.1 (2 : K) ≤ 1 := by
    have : (placeAbv K (.inl w)) (2 : K) ≤ 1 := by
      change w.1 (2 : K) ≤ 1
      have := FinitePlace.norm_le_one K (FinitePlace.maximalIdeal w) (2 : 𝓞 K)
      rw [map_ofNat] at this
      rw [FinitePlace.norm_embedding_eq] at this
      exact this
    exact h.le_one_iff.1 this
  have h2 : u (2 : K) = 2 := by exact_mod_cast u.map_natCast 2
  change u (2 : K) ≤ 1 at h1
  rw [h2] at h1; norm_num at h1

/-- **Theorem 7.14, uniqueness part**: distinct places of Mathlib (finite places, one per nonzero prime ideal;
infinite places, one per real embedding or conjugate pair of complex embeddings) give distinct primes. -/
@[kb "milne2020ant" "v3.08, Thm. 7.14, p. 111"]
theorem placeOf_injective : Function.Injective (placeOf K) := by
  intro a b hab
  have h : (placeAbv K a).IsEquiv (placeAbv K b) := Quotient.exact hab
  cases a with
  | inl w₁ =>
    cases b with
    | inl w₂ =>
      congr 1
      rw [← FinitePlace.mk_maximalIdeal w₁, ← FinitePlace.mk_maximalIdeal w₂]
      congr 1
      refine IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
      rw [← FinitePlace.norm_lt_one_iff_mem K, ← FinitePlace.norm_lt_one_iff_mem K,
        FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding_eq]
      exact h.lt_one_iff
    | inr w₂ => exact (finite_infinite_aux K w₁ w₂ h).elim
  | inr w₁ =>
    cases b with
    | inl w₂ => exact (finite_infinite_aux K w₂ w₁ h.symm).elim
    | inr w₂ =>
      congr 1
      exact InfinitePlace.eq_iff_isEquiv.2 h

/-- **Theorem 7.14, existence part** (named statement; Milne proves it in Chapter 8): every nontrivial absolute value
on the number field $K$ is equivalent to a finite place (the $\mathfrak p$-adic absolute value of a nonzero prime ideal
$\mathfrak p$) or to an infinite place ($|\sigma(\cdot)|$ for an embedding $\sigma : K \to \mathbb C$). -/
@[kb "milne2020ant" "v3.08, Thm. 7.14, p. 111"]
structure Theorem7_14 : Prop where
  exists_isEquiv : ∀ v : AbsoluteValue K ℝ, v.IsNontrivial →
    (∃ w : FinitePlace K, v.IsEquiv w.1) ∨ ∃ w : InfinitePlace K, v.IsEquiv w.1

/-- **Theorem 7.14.** There is exactly one prime of the number field $K$ for each nonzero prime ideal
(`FinitePlace K`, in bijection with the nonzero prime ideals by `NumberField.FinitePlace.equivHeightOneSpectrum`),
for each real embedding, and for each conjugate pair of complex embeddings (`InfinitePlace K`, see
`NumberField.InfinitePlace.mkReal` and `NumberField.InfinitePlace.mkComplex`): the map from these to primes is a
bijection. Conditional on the existence part `Theorem7_14`. -/
@[kb "milne2020ant" "v3.08, Thm. 7.14, p. 111"]
theorem thm_7_14 (h : Theorem7_14 K) : Function.Bijective (placeOf K) := by
  refine ⟨placeOf_injective K, fun q => ?_⟩
  induction q using Quotient.inductionOn with
  | h v =>
    rcases h.exists_isEquiv v.1 v.2 with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact ⟨.inl w, Quotient.sound hw.symm⟩
    · exact ⟨.inr w, Quotient.sound hw.symm⟩

end NumberField

/-! ## Lemma 7.16 -/

section Extension

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in
/-- If the finite place of `P` lies over (the class of) `a`, then `x ∈ 𝓞 K` lies in the pullback of `P`
iff `a x < 1`. -/
private theorem under_iff_aux (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (a : AbsoluteValue K ℝ)
    (h : (AbsoluteValue.restrictMilne (K := K) (FinitePlace.mk P).1).IsEquiv a) (x : 𝓞 K) :
    x ∈ (P.under (𝓞 K)).asIdeal ↔ a (algebraMap (𝓞 K) K x) < 1 := by
  rw [← h.lt_one_iff]
  change algebraMap (𝓞 K) (𝓞 L) x ∈ P.asIdeal ↔ _
  rw [← FinitePlace.norm_lt_one_iff_mem L P]
  have : algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap K L (algebraMap (𝓞 K) K x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [this]
  rfl

/-- **Lemma 7.16(a).** Each prime of $K$ extends to only finitely many primes of $L$. Conditional on Theorem 7.14 for
$L$ (as in the book, which proves both in Chapter 8). -/
@[kb "milne2020ant" "v3.08, Lemma 7.16, p. 112"]
theorem lemma_7_16a (hL : Theorem7_14 L) (v : MilnePlace K) :
    {w : MilnePlace L | w.LiesOver v}.Finite := by
  induction v using Quotient.inductionOn with
  | h a =>
  have hQ : {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L) |
      (placeOf L (.inl (FinitePlace.mk P))).LiesOver (Quotient.mk (absValueSetoid K) a)}.Finite := by
    by_cases hne : ({P : IsDedekindDomain.HeightOneSpectrum (𝓞 L) |
      (placeOf L (.inl (FinitePlace.mk P))).LiesOver (Quotient.mk (absValueSetoid K) a)}).Nonempty
    · obtain ⟨P0, hP0⟩ := hne
      have hm : (P0.under (𝓞 K)).asIdeal.IsMaximal := (P0.under (𝓞 K)).isMaximal
      have hfin := IsDedekindDomain.primesOver_finite (A := 𝓞 K) (B := 𝓞 L)
        (P0.under (𝓞 K)).asIdeal
      refine Set.Finite.of_finite_image (f := fun P => P.asIdeal) ?_
        (fun P _ Q _ h => IsDedekindDomain.HeightOneSpectrum.ext h)
      refine hfin.subset ?_
      rintro _ ⟨P, hP, rfl⟩
      refine ⟨P.isPrime, ⟨?_⟩⟩
      refine Ideal.ext fun x => ?_
      have h1 := under_iff_aux K L P0 a hP0 x
      have h2 := under_iff_aux K L P a hP x
      change x ∈ (P0.under (𝓞 K)).asIdeal ↔ x ∈ Ideal.under (𝓞 K) P.asIdeal
      exact h1.trans h2.symm
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]; exact Set.finite_empty
  have hS : {w : MilnePlace L | w.LiesOver (Quotient.mk (absValueSetoid K) a)} ⊆
      (fun P => placeOf L (.inl (FinitePlace.mk P))) '' {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L) |
      (placeOf L (.inl (FinitePlace.mk P))).LiesOver (Quotient.mk (absValueSetoid K) a)} ∪
      Set.range (fun u : InfinitePlace L => placeOf L (.inr u)) := by
    intro w hw
    obtain ⟨y, rfl⟩ := (thm_7_14 L hL).2 w
    cases y with
    | inl w' =>
      left
      refine ⟨FinitePlace.maximalIdeal w', ?_, ?_⟩
      · simpa using hw
      · simp
    | inr u => right; exact ⟨u, rfl⟩
  exact ((hQ.image _).union (Set.finite_range _)).subset hS

/-- Milne's normalized absolute value at one of Mathlib's places (p. 112): $\lVert\cdot\rVert_{\mathfrak p}$
($= (N\mathfrak p)^{-\operatorname{ord}_{\mathfrak p}}$) at a finite place, $|\sigma(\cdot)|$ at a real place and
$|\sigma(\cdot)|^2$ at a complex place. -/
@[kb "milne2020ant" "v3.08, Ch. 7, p. 112 and Ch. 8, definition in prose (normalized absolute value), p. 137"]
noncomputable def normalizedAbv {F : Type*} [Field F] [NumberField F] : FinitePlace F ⊕ InfinitePlace F → F → ℝ
  | .inl w => fun x => w x
  | .inr w => fun x => w x ^ w.mult

/-- **Lemma 7.16(b)** (named statement; Milne proves it in Chapter 8, see Proposition 8.7): for every prime $v$ of $K$
and $\alpha \in L$, $\prod_{w \mid v} |\alpha|_w = |\operatorname{Nm}_{L/K} \alpha|_v$, with the normalized absolute
values. -/
@[kb "milne2020ant" "v3.08, Lemma 7.16, p. 112"]
structure Lemma7_16b : Prop where
  prod_eq : ∀ (v : FinitePlace K ⊕ InfinitePlace K) (α : L),
    ∏ᶠ (w : {w : FinitePlace L ⊕ InfinitePlace L // (placeOf L w).LiesOver (placeOf K v)}), normalizedAbv w.1 α =
      normalizedAbv v (Algebra.norm K α)

end Extension

/-! ## Remark 7.17: the product formula for function fields (named statements) -/

/-- **Remark 7.17(a)** (named statement). Let $K$ be a finite extension of $k(T)$ with $k$ a finite field. The primes
of $K$ are the normalized discrete valuations $\operatorname{ord}_v : K^\times \twoheadrightarrow \mathbb Z$ (Mathlib:
surjective valuations $v : K \to \mathbb Z_{\mathrm m 0}$, with $v(a) = \exp(-\operatorname{ord}_v a)$, so that
$\operatorname{ord}_v(a) = -\log v(a)$). With $|a|_v = (1/Nv)^{\operatorname{ord}_v(a)}$, $Nv$ the number of elements of
the residue field, $\prod_v |a|_v = 1$ for every $a \in K^\times$ (and the product is finite). -/
@[kb "milne2020ant" "v3.08, Remark 7.17, p. 112"]
structure Remark7_17a (k K : Type*) [Field k] [Finite k] [Field K] [Algebra (RatFunc k) K]
    [FiniteDimensional (RatFunc k) K] : Prop where
  finite : ∀ a : K, a ≠ 0 →
    {v : {v : Valuation K (WithZero (Multiplicative ℤ)) // Function.Surjective v} | v.1 a ≠ 1}.Finite
  prod_eq_one : ∀ a : K, a ≠ 0 →
    ∏ᶠ (v : {v : Valuation K (WithZero (Multiplicative ℤ)) // Function.Surjective v}),
      (Nat.card (IsLocalRing.ResidueField v.1.valuationSubring) : ℝ) ^ (WithZero.log (v.1 a)) = 1

/-- **Remark 7.17(b)** (named statement). Let $K$ be a finite extension of $k(T)$ with $k$ algebraically closed, and
consider the primes of $K$ trivial on $k$: the normalized discrete valuations $\operatorname{ord}_v$ of $K$ trivial on
$k^\times$. Then $\sum_v \operatorname{ord}_v(a) = 0$ for every $a \in K^\times$ (a finite sum). -/
@[kb "milne2020ant" "v3.08, Remark 7.17, p. 112"]
structure Remark7_17b (k K : Type*) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FiniteDimensional (RatFunc k) K] : Prop where
  finite : ∀ a : K, a ≠ 0 →
    {v : {v : Valuation K (WithZero (Multiplicative ℤ)) // Function.Surjective v ∧ ∀ c : k, c ≠ 0 → v (algebraMap k K c) = 1} |
      v.1 a ≠ 1}.Finite
  sum_eq_zero : ∀ a : K, a ≠ 0 →
    ∑ᶠ (v : {v : Valuation K (WithZero (Multiplicative ℤ)) // Function.Surjective v ∧ ∀ c : k, c ≠ 0 → v (algebraMap k K c) = 1}),
      WithZero.log (v.1 a) = 0

end NumberFieldKB.MilneANT
