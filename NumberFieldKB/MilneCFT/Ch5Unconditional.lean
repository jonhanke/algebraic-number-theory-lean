import NumberFieldKB.MilneCFT.Ch5Complements
import NumberFieldKB.MilneCFT.Ch7.ArtinInertiaTauCeti
import NumberFieldKB.MilneCFT.GlobalUnconditional
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Milne, *Class Field Theory*, Chapter V §3: consequences of the existence theorem, unconditional

The named inputs `ReciprocityLaw K` (V 3.5, `reciprocityLaw_ideal`) and `ExistenceTheoremArtin K` (V 3.6, corrected
form, `existenceTheoremArtin`) are proved from the Tau Ceti port. This file restates their
consumers without them; the conditional originals are unchanged.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

variable (K) in
/-- **Theorem 3.6, the existence theorem as stated, unconditional** (Milne, *CFT*, V, Theorem 3.6). -/
@[kb "milne2020cft" "Ch. V, Theorem 3.6"]
theorem existenceTheorem : ExistenceTheorem K :=
  existenceTheorem_of_artin (existenceTheoremArtin K)

/-- **The ray class field exists, unconditional** (Milne, *CFT*, V, §3, p. 158): for every modulus $\mathfrak m$ there
is a finite abelian extension $L_\mathfrak m$, unramified outside $\mathfrak m$, with $C_\mathfrak m \cong
\mathrm{Gal}(L_\mathfrak m/K)$, $[\mathfrak p] \mapsto (\mathfrak p, L_\mathfrak m/K)$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 158 (the ray class field L_m)"]
theorem exists_rayClassField' (m : Modulus K) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L)
      (e : RayClassGroup m ≃* Gal(L/K)), UnramifiedOutside L m ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), e (rayClass m v hv) = artinFrob L v :=
  exists_rayClassField (existenceTheoremArtin K) m

/-- **Remark 3.8, unconditional** (Milne, *CFT*, V, p. 158): every finite abelian extension lies in a ray class
field. -/
@[kb "milne2020cft" "Ch. V, Remark 3.8 (every abelian extension lies in a ray class field)"]
theorem remark_3_8_contained' (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] :
    ∃ (m : Modulus K) (Lm : Type) (_ : Field Lm) (_ : NumberField Lm) (_ : Algebra K Lm)
      (_ : IsAbelianGalois K Lm), IsClassFieldOf Lm m (rayPrincipal m) ∧ Nonempty (L →ₐ[K] Lm) :=
  remark_3_8_contained L (reciprocityLaw_ideal K) (existenceTheoremArtin K)

/-- **Example 3.9, unconditional** (Milne, *CFT*, V, p. 159): the ray class field for $\mathfrak m = 1$ is the Hilbert
class field, and every finite abelian extension unramified at all primes embeds in it. -/
@[kb "milne2020cft" "Ch. V, Example 3.9 (the Hilbert class field)"]
theorem example_3_9_hilbert' :
    ∃ (H : Type) (_ : Field H) (_ : NumberField H) (_ : Algebra K H) (_ : IsAbelianGalois K H),
      HilbertClassField.IsHilbertClassField K H ∧
      ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
        (∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K L) → IsUnramifiedAtInfinitePlaces K L →
          Nonempty (L →ₐ[K] H) :=
  example_3_9_hilbert (reciprocityLaw_ideal K) (existenceTheoremArtin K)

end NumberFieldKB.MilneCFT
