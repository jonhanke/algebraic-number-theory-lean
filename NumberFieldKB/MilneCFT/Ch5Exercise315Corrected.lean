import NumberFieldKB.MilneCFT.Ch5NormLimitationUncond
import NumberFieldKB.MilneCFT.Ch5Exercise315Counter
import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Milne, *Class Field Theory*, Chapter V, Exercise 3.15, corrected and proved

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Exercise 3.15,
p. 160.

As printed (named statement `Exercise3_15`) the existence clause assumes only
$i(K_{\mathfrak m,1}) \cap I^{S\cup S(\mathfrak m)} \subseteq H$, and is false (`not_exercise3_15_rat`: $K = \mathbb Q$,
$S = \{2\}$, $\mathfrak m = 3\infty$); this is an erratum of the book, confirmed by Jon Hanke (2026-11-08): the primes of
$S$, which split completely in an $S$-class field, must be put into $H$. The corrected statement
(`Exercise3_15Corrected`) assumes $(P_\mathfrak m\cdot\langle S\rangle) \cap I^{S\cup S(\mathfrak m)} \subseteq H$ in
the existence clause and keeps the uniqueness and the converse unchanged; it is proved here from
`exercise3_15_exists`, `exercise3_15_unique` and `exercise3_15_isSClassField` (`exercise3_15_corrected`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

/-- **Exercise 3.15, corrected** (Milne, *CFT*, V, Exercise 3.15, p. 160; the hypothesis of the existence clause
corrected, an erratum confirmed by Jon Hanke, 2026-11-08): for $S$ finite and disjoint from $S(\mathfrak m)$ and
$(P_\mathfrak m\cdot\langle S\rangle) \cap I^{S\cup S(\mathfrak m)} \subseteq H \subseteq I^{S\cup S(\mathfrak m)}$ an
$S$-class field $L$ exists, with $I^{S\cup S(\mathfrak m)}/H \cong \mathrm{Gal}(L/K)$; it is unique up to
$K$-isomorphism; and every finite abelian $L$ in which the primes of $S$ split completely is the $S$-class field of some
$H$ (for some $\mathfrak m$). -/
@[kb "milne2020cft" "Ch. V, Exercise 3.15 (corrected)"]
structure Exercise3_15Corrected : Prop where
  exists_field : ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ),
    S.Finite → Disjoint S m.finiteSupport → H ≤ sIdeals (S ∪ m.finiteSupport) →
    (rayPrincipal m ⊔ Subgroup.closure (primeUnitIdeal '' S)) ⊓ sIdeals (S ∪ m.finiteSupport) ≤ H →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      IsSClassField S m H L ∧
        Nonempty (sIdeals (S ∪ m.finiteSupport) ⧸ H.subgroupOf (sIdeals (S ∪ m.finiteSupport)) ≃* Gal(L/K))
  unique : ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (L L' : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field L'] [NumberField L']
    [Algebra K L'] [IsAbelianGalois K L'], S.Finite → IsSClassField S m H L → IsSClassField S m H L' →
      Nonempty (L ≃ₐ[K] L')
  isSClassField : ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L], S.Finite → (∀ v ∈ S, v ∈ splitPrimes K L) →
      ∃ (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ), Disjoint S m.finiteSupport ∧
        IsSClassField S m H L

/-- **Exercise 3.15, corrected**, proved (Milne, *CFT*, V, Exercise 3.15, p. 160). -/
@[kb "milne2020cft" "Ch. V, Exercise 3.15 (corrected form, proved)"]
theorem exercise3_15_corrected : Exercise3_15Corrected K :=
  ⟨fun S m H _ hdisj hH hP => exercise3_15_exists S m H hdisj hH hP,
    fun S m H L L' _ _ _ _ _ _ _ _ hS h h' => exercise3_15_unique S m H L L' hS h h',
    fun S L _ _ _ _ hS hsplit => exercise3_15_isSClassField S L hS hsplit⟩

end NumberFieldKB.MilneCFT
