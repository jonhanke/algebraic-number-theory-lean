import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Special

/-!
# Milne, Class Field Theory, Chapter IV, Example 2.14 (e): the Brauer group of a number field

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV, Example 2.14 (e) (Albert, Brauer, Hasse, Noether): for a number field $K$ there is an
exact sequence
$$0 \to \mathrm{Br}(K) \to \bigoplus_v \mathrm{Br}(K_v) \xrightarrow{\ \sum\ } \mathbb Q/\mathbb Z \to 0,$$
the sum over all primes of $K$, including the infinite ones.  Milne: "This statement is of the same
depth as that of the main theorems of class field theory" (it is proved in Chapter VIII §4, job
`cft-VIII`).  It is a named statement here.

Formalization.  The first map is the product of the base-change maps $\mathrm{Br}(K) \to \mathrm{Br}(K_v)$
(`baseChange`), to the completions `v.adicCompletion K` at the finite primes and `w.Completion` at
the infinite ones.  The second map is the sum of local invariants $\mathrm{inv}_v$: isomorphisms
$\mathrm{Br}(K_v) \cong \mathbb Q/\mathbb Z$ at the finite primes and injections at the infinite ones.
The local invariants are quantified existentially (their construction is §4 and Chapter III), so
this records exactness for *some* family of local invariants with those properties, which is how
Milne's example states it.

Locators give the printed page of the book (printed page = pdf page − 9).
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch4

/-- Example 2.14 (e) of Milne (named statement; Albert–Brauer–Hasse–Noether): the sequence
$0 \to \mathrm{Br}(K) \to \bigoplus_v \mathrm{Br}(K_v) \to \mathbb Q/\mathbb Z \to 0$ is exact.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.brLocalization_injective`
(`TauCeti/NumberTheory/ClassFieldTheory/Global/Brauer/SumFormula.lean:135`),
`TauCeti.ClassFieldTheory.range_brLocalization`
(`TauCeti/NumberTheory/ClassFieldTheory/Global/Brauer/Exactness.lean:75`),
`TauCeti.ClassFieldTheory.sumLocalInv_surjective`
(`TauCeti/NumberTheory/ClassFieldTheory/Global/Brauer/Sequence.lean:84`) and `TauCeti.ClassFieldTheory.invMap`
(`TauCeti/NumberTheory/ClassFieldTheory/Brauer/Invariant.lean:200`) at Tau Ceti commit `7ed979dc`. Needed to apply it
here: identify Mathlib's Brauer group of a number field with Tau Ceti's (`brauerGroupEquivBr`), match the base change
maps, and match Tau Ceti's direct sums of finite support with our finite sums; our statement asks for some family of
local invariants, and Tau Ceti fixes one. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 2.14(e), p. 130"]
structure Example2_14e (K : Type) [Field K] [NumberField K] : Prop where
  exact : ∃ (invf : ∀ v : HeightOneSpectrum (𝓞 K),
      Additive (BrauerGroup.{0, 0} (v.adicCompletion K)) →+ QZ)
    (invi : ∀ w : InfinitePlace K, Additive (BrauerGroup.{0, 0} w.Completion) →+ QZ),
    (∀ v, Function.Bijective (invf v)) ∧ (∀ w, Function.Injective (invi w)) ∧
    -- the image of a global class has only finitely many nonzero components
    (∀ x : BrauerGroup.{0, 0} K,
      Set.Finite {v : HeightOneSpectrum (𝓞 K) | baseChange (v.adicCompletion K) x ≠ 1}) ∧
    -- exactness at Br(K)
    Function.Injective (fun x : BrauerGroup.{0, 0} K =>
      ((fun v : HeightOneSpectrum (𝓞 K) => baseChange (v.adicCompletion K) x),
        (fun w : InfinitePlace K => baseChange w.Completion x))) ∧
    -- the composite is zero
    (∀ x : BrauerGroup.{0, 0} K,
      (∑ᶠ v : HeightOneSpectrum (𝓞 K), invf v (Additive.ofMul (baseChange (v.adicCompletion K) x)))
        + ∑ w : InfinitePlace K, invi w (Additive.ofMul (baseChange w.Completion x)) = 0) ∧
    -- exactness in the middle
    (∀ (y : ∀ v : HeightOneSpectrum (𝓞 K), BrauerGroup.{0, 0} (v.adicCompletion K))
        (z : ∀ w : InfinitePlace K, BrauerGroup.{0, 0} w.Completion),
        Set.Finite {v | y v ≠ 1} →
        (∑ᶠ v, invf v (Additive.ofMul (y v))) + ∑ w, invi w (Additive.ofMul (z w)) = 0 →
        ∃ x : BrauerGroup.{0, 0} K, (∀ v, baseChange (v.adicCompletion K) x = y v) ∧
          ∀ w, baseChange w.Completion x = z w) ∧
    -- surjectivity of the sum
    (∀ q : QZ, ∃ (y : ∀ v : HeightOneSpectrum (𝓞 K), BrauerGroup.{0, 0} (v.adicCompletion K))
        (z : ∀ w : InfinitePlace K, BrauerGroup.{0, 0} w.Completion),
        Set.Finite {v | y v ≠ 1} ∧
          (∑ᶠ v, invf v (Additive.ofMul (y v))) + ∑ w, invi w (Additive.ofMul (z w)) = q)

end NumberFieldKB.MilneCFT.Ch4
