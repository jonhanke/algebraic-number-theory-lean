import NumberFieldKB.MilneCFT.Ch7.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter VII §1: the global Artin map

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

Milne fixes an algebraic closure $\Omega$ of $K$; the finite abelian extensions of $K$ are the intermediate fields
$K\subseteq L\subseteq\Omega$, finite and Galois over $K$ with commutative Galois group (`AbExt K Ω`). The global
Artin map (definition in prose, Chapter VII, §1, p. 201; Chapter V, Proposition 5.2, p. 178) is
$\psi_{L/K}(a) = \prod_v\phi_v(a_v)$, $\phi_v : K_v^\times\to D(w)\subseteq\mathrm{Gal}(L/K)$ the local Artin map of
$L_w/K_v$.

**Definition used here.** `IsGlobalArtinMap K Ω ψ` says that the family $\psi_L : \mathbb I_K\to\mathrm{Gal}(L/K)$
($L$ finite abelian) has the properties of the product of the local Artin maps that characterize it:
(1) $\ker\psi_L$ is open (continuity); (2) $\psi_L(\mathrm{Nm}_{L/K}\mathbb I_L) = 1$ (local Artin maps kill local
norms); (3) at a finite prime $v$ unramified in $L$, $\psi_L(a) = \mathrm{Frob}_v^{\,\mathrm{ord}_v(a)}$ for
$a\in K_v^\times$; (4) compatibility with restriction to subextensions; (5) $\psi_L(K_v^\times)$ is the decomposition
group of a place above $v$ (local Artin maps are onto $\mathrm{Gal}(L_w/K_v)$). Milne's $\psi$ has these properties
(Chapter V, §5, using Chapter I, Theorem 1.1, and Chapter III). Conversely they determine the local components: at a
real place, (2) and (5) force $\phi_v(x) = $ complex conjugation for $x<0$ when $v$ ramifies; at a finite place, (2)–(4)
applied to $L$ and to the subfield $L^{I_v}$ fixed by inertia give conditions (a), (b) of Chapter I, Theorem 1.1 for
$L_w/K_v$, and every finite abelian extension of $K_v$ is a completion of a finite abelian extension of $K$, so the
uniqueness in Theorem 1.1 applies. (This converse uses the existence theorem and is not formalized; the statements of
Chapter VII below quantify over all $\psi$ with these properties.)
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev
open scoped Pointwise

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/-- A finite abelian extension of $K$ inside $\Omega$. -/
structure AbExt where
  /-- The field $L$, $K\subseteq L\subseteq\Omega$. -/
  L : IntermediateField K Ω
  finiteDimensional : FiniteDimensional K L
  isGalois : IsGalois K L
  comm : ∀ σ τ : Gal(L/K), σ * τ = τ * σ

variable {K Ω}

attribute [instance] AbExt.finiteDimensional AbExt.isGalois

/-- A finite extension of $K$ inside $\Omega$ is a number field. -/
instance AbExt.numberField (E : AbExt K Ω) : NumberField E.L :=
  haveI : CharZero E.L := charZero_of_injective_algebraMap (algebraMap K E.L).injective
  { to_charZero := inferInstance
    to_finiteDimensional := Module.Finite.trans K E.L }

/-- Restriction $\mathrm{Gal}(L'/K)\to\mathrm{Gal}(L/K)$ for $L\subseteq L'$ (the same construction as
`NumberFieldKB.MilneCFT.LocalCFT.galRestrict`, there stated for local fields). -/
def galRestrict {L L' : IntermediateField K Ω} (h : L ≤ L') [Normal K L] : Gal(L'/K) →* Gal(L/K) :=
  letI : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  AlgEquiv.restrictNormalHom L

/-- $\mathrm{ord}_v(a)$ for $a\in K_v^\times$: $v(a) = \exp(-\mathrm{ord}_v a)$. -/
def ordAt (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) : ℤ :=
  -WithZero.log (Valued.v (a : v.adicCompletion K))

variable (K Ω) in
/-- A family of homomorphisms $\mathbb I_K\to\mathrm{Gal}(L/K)$, $L$ finite abelian in $\Omega$. -/
abbrev ArtinFamily := ∀ E : AbExt K Ω, IdeleGroup (𝓞 K) K →* Gal(E.L/K)

variable (K Ω) in
/-- **The global Artin map** (definition in prose; Milne, *CFT*, Chapter VII, §1, p. 201, and Chapter V,
Proposition 5.2): the family $\psi_L : \mathbb I_K\to\mathrm{Gal}(L/K)$ over the finite abelian extensions $L$ of $K$
has the characteristic properties of the product of the local Artin maps (see the module docstring). -/
@[kb "milne2020cft" "Ch. VII, §1, p. 201 (global Artin map as the product of the local Artin maps)"]
structure IsGlobalArtinMap (ψ : ∀ E : AbExt K Ω, IdeleGroup (𝓞 K) K →* Gal(E.L/K)) : Prop where
  isOpen_ker : ∀ E, IsOpen ((ψ E).ker : Set (IdeleGroup (𝓞 K) K))
  norm_le_ker : ∀ E, normIdeles K E.L ≤ (ψ E).ker
  unramified : ∀ (E : AbExt K Ω) (v : HeightOneSpectrum (𝓞 K)), v ∈ unramifiedPrimes K E.L →
    ∀ (Q : v.asIdeal.primesOver (𝓞 E.L)) (a : (v.adicCompletion K)ˣ),
      ψ E (IdeleGroup.ofAdicCompletion (𝓞 K) K v a) = frobAt K E.L v Q ^ ordAt v a
  compat : ∀ (E E' : AbExt K Ω) (h : E'.L ≤ E.L) (a : IdeleGroup (𝓞 K) K),
    galRestrict h (ψ E a) = ψ E' a
  range_finite : ∀ (E : AbExt K Ω) (v : HeightOneSpectrum (𝓞 K)) (Q : v.asIdeal.primesOver (𝓞 E.L)),
    ((ψ E).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)).range = MulAction.stabilizer Gal(E.L/K) Q.1
  range_infinite : ∀ (E : AbExt K Ω) (v : InfinitePlace K) (w : InfinitePlace E.L),
    w.comap (algebraMap K E.L) = v →
      ((ψ E).comp (IdeleGroup.ofCompletion (𝓞 K) K v)).range = MulAction.stabilizer Gal(E.L/K) w

end NumberFieldKB.MilneCFT.Ch7
