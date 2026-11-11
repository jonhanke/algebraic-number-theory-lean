import NumberFieldKB.MilneANT.Ch8DedekindProof
import NumberFieldKB.MilneANT.Ch8Jordan
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: the Dedekind consequences, unconditionally

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

The named statement `DedekindFrobenius` is proved (`dedekindFrobenius`, `Ch8DedekindProof.lean`), so the results of
`Ch8Dedekind.lean` and `Ch8Jordan.lean` stated with the hypothesis `hD : DedekindFrobenius` hold unconditionally.
The natural-density forms (Examples 8.36, 8.37) take the named statement `Theorem8_31`, which is proved
(`theorem8_31`); their hypothesis-free versions are in `Ch8Thm831Consumers.lean`.
-/

open NumberField IsDedekindDomain Polynomial UniqueFactorizationMonoid
open scoped Classical

namespace NumberFieldKB.MilneANT

noncomputable section

/-- **Theorem 8.23** (Dedekind), unconditional. -/
@[kb "milne2020ant" "v3.08, Thm. 8.23, p. 145"]
theorem thm_8_23' {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X]) (hf : f.Monic)
    (𝔭 : HeightOneSpectrum (𝓞 K))
    (hsq : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))) :
    ∃ σ : (f.map (algebraMap (𝓞 K) K)).Gal,
      (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts =
        (normalizedFactors (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))).map natDegree :=
  thm_8_23 dedekindFrobenius f hf 𝔭 hsq

/-- **Example 8.25**, unconditional: the Galois group of $X^5 - X - 1$ over $\mathbb Q$ is $S_5$. -/
@[kb "milne2020ant" "v3.08, Ex. 8.25, p. 146"]
theorem example_8_25' : Function.Bijective (galPerm (X ^ 5 - X - 1 : ℚ[X])) :=
  example_8_25 dedekindFrobenius

/-- **Densities of factorization types** with Dirichlet density, unconditional. -/
@[kb "milne2020ant" "v3.08, Ex. 8.36 and 8.37 (general principle), p. 148"]
theorem factorizationType_hasDirichletDensity' {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X])
    (hf : f.Monic) (hs : (f.map (algebraMap (𝓞 K) K)).Separable) (τ : Multiset ℕ) :
    (factorizationTypeSet f τ).HasDirichletDensity
      (Nat.card {σ : (f.map (algebraMap (𝓞 K) K)).Gal //
          (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts = τ} /
        Nat.card (f.map (algebraMap (𝓞 K) K)).Gal) :=
  factorizationType_hasDirichletDensity dedekindFrobenius f hf hs τ

/-- **Remark 8.40(d)**, first claim, unconditional. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(d), p. 150"]
theorem remark_8_40d' {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X])
    (hf : f.Monic) (hs : (f.map (algebraMap (𝓞 K) K)).Separable)
    (h : {𝔭 : HeightOneSpectrum (𝓞 K) |
      ¬ (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)).Splits}.Finite) :
    (f.map (algebraMap (𝓞 K) K)).Splits :=
  remark_8_40d dedekindFrobenius f hf hs h

/-- **Remark 8.40(d)**, second claim: the named statement `Remark8_40d` holds. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(d), p. 150"]
theorem remark8_40d_holds : Remark8_40d :=
  remark_8_40d_second dedekindFrobenius

end

end NumberFieldKB.MilneANT
