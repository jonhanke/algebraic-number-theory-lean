import NumberFieldKB.MilneCFT.Ch7.Cohomology
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# Milne, *Class Field Theory*, Chapter VII §§5–6: reductions of the second inequality

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

`Thm51For F L` is the conclusion of Theorem 5.1 for one Galois extension $L/F$ of number fields: (a) the index
$(\mathbb I_F : F^\times\mathrm{Nm}(\mathbb I_L))$ is finite and divides $[L:F]$; (b) $H^1(G, C_L) = 0$; (c)
$H^2(G, C_L)$ is finite of order dividing $[L:F]$. Milne's "it suffices to prove the theorem when ..." are the
implications below, quantified over all number fields.

* **Lemma 5.3** (`Lemma5_3`): it suffices to treat $p$-groups.
* **Lemma 5.4** (`Lemma5_4`): for $p$-groups it suffices to treat cyclic groups of order $p$.
* **Lemma 6.1** (`Lemma6_1`): for the second inequality (a) for cyclic extensions of prime degree $p$, it suffices to
  treat base fields containing a primitive $p$-th root of $1$.

These are named statements (their proofs use restriction to Sylow subgroups, inflation–restriction in degrees $1$ and
$2$ for idele class groups, and norm compatibilities in towers, which are not formalized here).
-/

open IsDedekindDomain NumberField CategoryTheory CategoryTheory.Limits

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

/-- The conclusion of Theorem 5.1 for a Galois extension $L/F$ of number fields. -/
def Thm51For (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L] : Prop :=
  ((principalNormIdeles F L).FiniteIndex ∧ (principalNormIdeles F L).index ∣ Module.finrank F L) ∧
    IsZero (groupCohomology (ideleClassRep F L) 1) ∧
    (Finite (groupCohomology (ideleClassRep F L) 2) ∧
      Nat.card (groupCohomology (ideleClassRep F L) 2) ∣ Module.finrank F L)

/-- **Lemma 5.3** (named statement; Milne, *CFT*, Chapter VII, p. 212): it suffices to prove Theorem 5.1 when the
Galois group is a $p$-group, $p$ prime. -/
@[kb "milne2020cft" "Ch. VII, Lemma 5.3 (input)"]
structure Lemma5_3 : Prop where
  reduce : (∀ (p : ℕ) (_ : p.Prime) (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
      [IsGalois F L], IsPGroup p Gal(L/F) → Thm51For F L) →
    ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L], Thm51For F L

/-- **Lemma 5.4** (named statement; Milne, *CFT*, Chapter VII, p. 213): it suffices to prove Theorem 5.1 when the
Galois group is cyclic of prime order: then it holds for every Galois extension whose group is a $p$-group. -/
@[kb "milne2020cft" "Ch. VII, Lemma 5.4 (input)"]
structure Lemma5_4 : Prop where
  reduce : ∀ p : ℕ, p.Prime →
    (∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L],
      Nat.card Gal(L/F) = p → Thm51For F L) →
    ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L],
      IsPGroup p Gal(L/F) → Thm51For F L

/-- **Lemma 6.1** (named statement; Milne, *CFT*, Chapter VII, p. 214): it suffices to prove the second inequality
(Theorem 5.1 (a)) for cyclic extensions of prime degree $p$ when the base field contains a primitive $p$-th root of $1$
(by base change to $K[\zeta_p]$, of degree prime to $p$). -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.1 (input)"]
structure Lemma6_1 : Prop where
  reduce : ∀ p : ℕ, p.Prime →
    (∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L],
      (∃ ζ : F, IsPrimitiveRoot ζ p) → Nat.card Gal(L/F) = p →
        (principalNormIdeles F L).FiniteIndex ∧ (principalNormIdeles F L).index ∣ p) →
    ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L],
      Nat.card Gal(L/F) = p → (principalNormIdeles F L).FiniteIndex ∧ (principalNormIdeles F L).index ∣ p

end NumberFieldKB.MilneCFT.Ch7
