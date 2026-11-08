import NumberFieldKB.MilneANT.Ch7OstrowskiFinite
import NumberFieldKB.MilneANT.Ch7OstrowskiInfinite
import NumberFieldKB.MilneANT.Ch7OstrowskiComplete

/-!
# Milne, *Algebraic Number Theory*, Theorem 7.14: the primes of a number field

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Milne states Theorem 7.14 (p. 111) and proves it in Chapter 8 through Proposition 8.1 applied to $K/\mathbb Q$. We
assemble it from two halves, following the same two inputs as Milne (Ostrowski's theorem for $\mathbb Q$, which is
Mathlib's `Rat.AbsoluteValue.equiv_real_of_unbounded`, and Ostrowski's theorem for complete archimedean fields,
Remark 7.49(a)):

* nonarchimedean absolute values are finite places (`exists_finitePlace_isEquiv`, unconditional);
* archimedean absolute values are infinite places (`exists_infinitePlace_isEquiv_of_remark_7_49a`, from
  Remark 7.49(a) applied to the completion).

This discharges the named statement `Theorem7_14` (`theorem7_14_of_remark_7_49a`), hence gives the bijection of
Theorem 7.14 and Lemma 7.16(a) with the same single input; with Remark 7.49(a) proved (`remark_7_49a`, by Artin's
lemma and Mathlib's Gelfand–Mazur theorem) all three are unconditional (`theorem7_14`, `thm_7_14_unconditional`,
`lemma_7_16a_unconditional`).
-/

open NumberField

namespace NumberFieldKB.MilneANT

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Theorem 7.14, existence part**, from Ostrowski's theorem on complete archimedean fields (`Remark7_49a`):
every nontrivial absolute value on a number field is equivalent to a finite or an infinite place. -/
@[kb "milne2020ant" "v3.08, Thm. 7.14, p. 111"]
theorem theorem7_14_of_remark_7_49a (h : Remark7_49a) : Theorem7_14 K where
  exists_isEquiv v hv := by
    by_cases hna : IsNonarchimedean v
    · exact .inl (exists_finitePlace_isEquiv v hv hna)
    · exact .inr (exists_infinitePlace_isEquiv_of_remark_7_49a h v hna)

/-- **Theorem 7.14** (from `Remark7_49a`): the map from Mathlib's places (finite places, one for each nonzero prime
ideal; infinite places, one for each real embedding and each conjugate pair of complex embeddings) to the primes of
$K$ (classes of nontrivial absolute values) is a bijection. -/
@[kb "milne2020ant" "v3.08, Thm. 7.14, p. 111"]
theorem thm_7_14_of_remark_7_49a (h : Remark7_49a) : Function.Bijective (placeOf K) :=
  thm_7_14 K (theorem7_14_of_remark_7_49a K h)

/-- **Lemma 7.16(a)** (from `Remark7_49a`): each prime of $K$ has only finitely many primes of $L$ above it. -/
@[kb "milne2020ant" "v3.08, Lemma 7.16, p. 112"]
theorem lemma_7_16a_of_remark_7_49a (h : Remark7_49a) (v : MilnePlace K) :
    {w : MilnePlace L | w.LiesOver v}.Finite :=
  lemma_7_16a K L (theorem7_14_of_remark_7_49a L h) v

/-! ## Unconditional forms (Remark 7.49(a) is proved in `Ch7OstrowskiComplete.lean`) -/

/-- **Theorem 7.14, existence part** (unconditional): every nontrivial absolute value on a number field is
equivalent to a finite place or to an infinite place. -/
@[kb "milne2020ant" "v3.08, Thm. 7.14, p. 111"]
theorem theorem7_14 : Theorem7_14 K := theorem7_14_of_remark_7_49a K remark_7_49a

/-- **Theorem 7.14** (unconditional): there is exactly one prime of the number field $K$ for each nonzero prime
ideal, each real embedding and each conjugate pair of complex embeddings. -/
@[kb "milne2020ant" "v3.08, Thm. 7.14, p. 111"]
theorem thm_7_14_unconditional : Function.Bijective (placeOf K) := thm_7_14 K (theorem7_14 K)

/-- **Lemma 7.16(a)** (unconditional): each prime of $K$ has only finitely many primes of $L$ above it. -/
@[kb "milne2020ant" "v3.08, Lemma 7.16, p. 112"]
theorem lemma_7_16a_unconditional (v : MilnePlace K) : {w : MilnePlace L | w.LiesOver v}.Finite :=
  lemma_7_16a K L (theorem7_14 L) v

end NumberFieldKB.MilneANT
