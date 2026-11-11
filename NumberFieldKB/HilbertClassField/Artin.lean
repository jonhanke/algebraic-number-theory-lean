import NumberFieldKB.HilbertClassField.Basic
import NumberFieldKB.Chebotarev.Unconditional
import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The Artin map of an unramified abelian extension and the existence of the Hilbert class field

* **Every element of the Galois group is a Frobenius element, infinitely often** (`setOf_frobAt_eq_infinite`): for
  $L/K$ finite Galois and $\sigma \in \mathrm{Gal}(L/K)$, infinitely many primes $\mathfrak p$ of $K$ unramified in $L$
  have $\mathrm{Frob}_\mathfrak P = \sigma$ for some $\mathfrak P \mid \mathfrak p$. From the unconditional Chebotarev
  density theorem (`chebotarev_unconditional`): the Chebotarev set of the class of $\sigma$ has positive density, and a
  finite set of primes has density $0$.
* **Surjectivity of an Artin map** (`artin_surjective`): a homomorphism $\psi : \mathrm{Cl}_K \to \mathrm{Gal}(L/K)$
  with $\psi[\mathfrak p] = \mathrm{Frob}_\mathfrak P$ at the unramified primes is surjective.
* **The existence of the Hilbert class field from two named inputs** (`hilbertClassFieldExists_of_inputs`):
  - `UnramifiedArtinReciprocityInput K` (Artin reciprocity for an abelian extension unramified at every place: the
    Frobenius map factors through the class group);
  - `HilbertClassFieldDegreeInput K` (there is an abelian extension unramified at every place, of degree $h_K$).
  Given these, the Artin map is surjective (Chebotarev) between groups of the same order, hence an isomorphism.
  Hence `HilbertClassFieldInput K` (`hilbertClassFieldInput_of_inputs`).
* **The two directions for an explicitly given extension**: under `UnramifiedArtinReciprocityInput K`, every principal
  prime splits completely in every abelian extension unramified at every place (`splitsCompletelyIn_of_isPrincipal`),
  and in one of degree $h_K$ every prime splitting completely is principal (`isHilbertClassField_of_finrank_eq`).
-/

open NumberField IsDedekindDomain Ideal
open NumberFieldKB.Chebotarev
open scoped Pointwise

namespace NumberFieldKB.HilbertClassField

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## §1. Every element of the Galois group is a Frobenius element (Chebotarev) -/

section Frobenius

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **Chebotarev sets are infinite**: the unramified primes of $K$ with a given Frobenius class $C$ form an infinite
set (their Dirichlet density $|C|/|G|$ is positive, `chebotarev_unconditional`; a finite set has density $0$). -/
theorem frobSet_infinite (C : ConjClasses Gal(L/K)) : (frobSet K L C).Infinite := by
  intro hfin
  have h := HasDirichletDensity.unique (chebotarev_unconditional K L C) (hasDirichletDensity_of_finite hfin)
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  haveI : Nonempty (ConjClasses.mk σ).carrier := ⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩
  have h1 : 0 < Nat.card (ConjClasses.mk σ).carrier := Nat.card_pos
  have h2 : 0 < Nat.card Gal(L/K) := Nat.card_pos
  have : (0 : ℝ) < Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K) := by positivity
  linarith

/-- A prime in the Chebotarev set of the class of $\sigma$ has $\mathrm{Frob}_\mathfrak P = \sigma$ for some
$\mathfrak P \mid \mathfrak p$: the Frobenius elements above $\mathfrak p$ are the conjugates of one of them
(Mathlib's `IsArithFrobAt.conj`). -/
theorem exists_frobAt_eq_of_mem_frobSet (σ : Gal(L/K)) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∈ frobSet K L (ConjClasses.mk σ)) : ∃ Q : 𝔭.asIdeal.primesOver (𝓞 L), frobAt K L 𝔭 Q = σ := by
  set Q₀ : 𝔭.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
  have hc := h𝔭.2
  rw [frobClass_eq_mk_frobAt K L 𝔭 Q₀, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hc
  obtain ⟨c, hc⟩ := hc
  have hF := (isArithFrobAt_frobAt K L 𝔭 Q₀).conj c
  rw [hc] at hF
  haveI := Q₀.2.1
  haveI := Q₀.2.2
  let Q : 𝔭.asIdeal.primesOver (𝓞 L) := primesOver.mk 𝔭.asIdeal (c • Q₀.1)
  exact ⟨Q, frobAt_eq_of_isArithFrobAt K L h𝔭.1 Q hF⟩

/-- **Every element of the Galois group is a Frobenius element at infinitely many primes** (Chebotarev): for $L/K$
finite Galois and $\sigma \in \mathrm{Gal}(L/K)$, infinitely many primes $\mathfrak p$ of $K$, unramified in $L$, have
$\mathrm{Frob}_\mathfrak P = \sigma$ for some prime $\mathfrak P$ of $L$ above $\mathfrak p$. -/
@[kb "neukirch1999" "Ch. VII, §13 (Chebotarev: every element of Gal(L|K) is a Frobenius, infinitely often) [unverified locator]"]
theorem setOf_frobAt_eq_infinite (σ : Gal(L/K)) :
    {𝔭 : HeightOneSpectrum (𝓞 K) |
      𝔭 ∈ unramifiedPrimes K L ∧ ∃ Q : 𝔭.asIdeal.primesOver (𝓞 L), frobAt K L 𝔭 Q = σ}.Infinite :=
  (frobSet_infinite K L (ConjClasses.mk σ)).mono fun _ h𝔭 =>
    ⟨h𝔭.1, exists_frobAt_eq_of_mem_frobSet K L σ h𝔭⟩

/-- **The Artin map is surjective** (Chebotarev): a homomorphism $\psi : \mathrm{Cl}_K \to \mathrm{Gal}(L/K)$ with
$\psi[\mathfrak p] = \mathrm{Frob}_\mathfrak P$ for every unramified $\mathfrak p$ and $\mathfrak P \mid \mathfrak p$
is surjective. -/
@[kb "neukirch1999" "Ch. VI, §7 and VII, §13: surjectivity of the Artin map via Chebotarev [unverified locator]"]
theorem artin_surjective (ψ : ClassGroup (𝓞 K) →* Gal(L/K))
    (hψ : ∀ 𝔭 ∈ unramifiedPrimes K L, ∀ Q : 𝔭.asIdeal.primesOver (𝓞 L), ψ (primeClass K 𝔭) = frobAt K L 𝔭 Q) :
    Function.Surjective ψ := by
  intro σ
  obtain ⟨𝔭, h𝔭⟩ := (setOf_frobAt_eq_infinite K L σ).nonempty
  obtain ⟨Q, hQ⟩ := h𝔭.2
  exact ⟨primeClass K 𝔭, (hψ 𝔭 h𝔭.1 Q).trans hQ⟩

end Frobenius

/-! ## §2. The existence theorem from two named inputs -/

section Existence

variable (K : Type) [Field K] [NumberField K]

/-- **Artin reciprocity for abelian extensions unramified at every place** (named input; Neukirch 1999, Ch. VI, §7,
Artin reciprocity with conductor $1$ [unverified locator]; Milne, *Class Field Theory*, Ch. V [unverified locator]): for
every finite Galois extension $H/K$ with abelian group, unramified at every nonzero prime of $\mathcal O_K$ and at every
infinite place, there is a homomorphism $\psi : \mathrm{Cl}_K \to \mathrm{Gal}(H/K)$ with
$\psi[\mathfrak p] = \mathrm{Frob}_\mathfrak P$ for every $\mathfrak p$ and $\mathfrak P \mid \mathfrak p$ (the Artin
map on ideals is trivial on principal ideals). Mathlib has no class field theory.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.rayClassArtinMap`
(`TauCeti/NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Reciprocity.lean:128`),
`TauCeti.ClassFieldTheory.isArithFrobAt_rayClassArtinMap_idealClass` (same file, line 200),
`TauCeti.ClassFieldTheory.isAdmissibleModulus_one_iff`
(`TauCeti/NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Ramification.lean:248`) and
`TauCeti.ClassFieldTheory.hilbertClassArtinEquiv`
(`TauCeti/NumberTheory/ClassFieldTheory/ClassFields/RayClassField.lean:262`) at Tau Ceti commit `7ed979dc`. Needed to
apply it here: use the trivial modulus, which is admissible exactly for extensions unramified everywhere; identify the
ray class group of the trivial modulus with the class group, and our `frobAt` with Tau Ceti's arithmetic Frobenius. -/
@[kb "neukirch1999" "Ch. VI, §7: Artin reciprocity for unramified abelian extensions (input) [unverified locator]"]
structure UnramifiedArtinReciprocityInput : Prop where
  exists_artin : ∀ (H : Type) [Field H] [NumberField H] [Algebra K H] [IsGalois K H],
    (∀ σ τ : Gal(H/K), σ * τ = τ * σ) → (∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∈ unramifiedPrimes K H) →
    IsUnramifiedAtInfinitePlaces K H →
    ∃ ψ : ClassGroup (𝓞 K) →* Gal(H/K),
      ∀ (𝔭 : HeightOneSpectrum (𝓞 K)) (Q : 𝔭.asIdeal.primesOver (𝓞 H)), ψ (primeClass K 𝔭) = frobAt K H 𝔭 Q

/-- **An abelian extension unramified at every place, of degree the class number** (named input; the existence half
of Hilbert class field theory: Neukirch 1999, Ch. VI, §6 [unverified locator]; Milne, *Class Field Theory*, Ch. V
[unverified locator]): there is a finite Galois extension $H/K$ with abelian group, unramified at every nonzero prime
of $\mathcal O_K$ and at every infinite place, with $[H:K] = h_K$.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.finrank_hilbertClassField`
(`TauCeti/NumberTheory/ClassFieldTheory/ClassFields/RayClassField.lean:299`) and
`TauCeti.ClassFieldTheory.isUnramifiedAt_hilbertClassField` (same file, line 348) at Tau Ceti commit `7ed979dc`; also
Yamaguchi (`n-yamaguchi-0729/ClassFieldTheory`) `ClassFieldTheory.exists_smallHilbertClassField`
(`Nyll/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldExists.lean:24`) and
`ClassFieldTheory.smallHilbertClassField_degree_eq_classNumber`
(`Nyll/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldDegree.lean:26`) at Yamaguchi
commit `fbd320c`. Needed to apply it here: take Tau Ceti's Hilbert class field of `K`, a number field inside the
separable closure with abelian Galois group, unramified at the finite places by the second theorem and at the infinite
places by an instance in the same file. -/
@[kb "neukirch1999" "Ch. VI, §6: the Hilbert class field has degree h_K and is unramified (input) [unverified locator]"]
structure HilbertClassFieldDegreeInput : Prop where
  exists_field : ∃ (H : Type) (_ : Field H) (_ : NumberField H) (_ : Algebra K H) (_ : IsGalois K H),
    (∀ σ τ : Gal(H/K), σ * τ = τ * σ) ∧ (∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∈ unramifiedPrimes K H) ∧
      IsUnramifiedAtInfinitePlaces K H ∧ Module.finrank K H = classNumber K

variable {K} {H : Type} [Field H] [NumberField H] [Algebra K H] [IsGalois K H]

/-- **An Artin map onto a group of order $h_K$ is an isomorphism**: if $H/K$ is unramified at every place,
$[H:K] = h_K$ and $\psi : \mathrm{Cl}_K \to \mathrm{Gal}(H/K)$ sends $[\mathfrak p]$ to $\mathrm{Frob}_\mathfrak P$, then
$H$ is a Hilbert class field of $K$. *Proof:* $\psi$ is surjective (`artin_surjective`, Chebotarev) between finite groups
of the same order. -/
@[kb "neukirch1999" "Ch. VI, §6-7: the Artin map Cl_K → Gal(H|K) is an isomorphism [unverified locator]"]
theorem isHilbertClassField_of_finrank_eq (hunr : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∈ unramifiedPrimes K H)
    (hinf : IsUnramifiedAtInfinitePlaces K H) (hdeg : Module.finrank K H = classNumber K)
    (ψ : ClassGroup (𝓞 K) →* Gal(H/K))
    (hψ : ∀ (𝔭 : HeightOneSpectrum (𝓞 K)) (Q : 𝔭.asIdeal.primesOver (𝓞 H)), ψ (primeClass K 𝔭) = frobAt K H 𝔭 Q) :
    IsHilbertClassField K H := by
  have hsurj := artin_surjective K H ψ fun 𝔭 _ Q => hψ 𝔭 Q
  have hcard : Nat.card (ClassGroup (𝓞 K)) ≤ Nat.card Gal(H/K) := by
    rw [IsGalois.card_aut_eq_finrank, hdeg, classNumber, Nat.card_eq_fintype_card]
  exact ⟨hunr, hinf, ⟨MulEquiv.ofBijective ψ (hsurj.bijective_of_nat_card_le hcard), hψ⟩⟩

/-- **Principal primes split completely in every abelian extension unramified at every place**, given Artin
reciprocity (`UnramifiedArtinReciprocityInput K`): $\psi[\mathfrak p] = 1$, so $\mathrm{Frob}_\mathfrak P = 1$. -/
theorem splitsCompletelyIn_of_isPrincipal (hA : UnramifiedArtinReciprocityInput K)
    (hab : ∀ σ τ : Gal(H/K), σ * τ = τ * σ) (hunr : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∈ unramifiedPrimes K H)
    (hinf : IsUnramifiedAtInfinitePlaces K H) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hp : Submodule.IsPrincipal 𝔭.asIdeal) : SplitsCompletelyIn K H 𝔭.asIdeal := by
  obtain ⟨ψ, hψ⟩ := hA.exists_artin H hab hunr hinf
  have Q : 𝔭.asIdeal.primesOver (𝓞 H) := Classical.arbitrary _
  rw [splitsCompletelyIn_iff_frobAt_eq_one K H 𝔭 (hunr 𝔭) Q, ← hψ 𝔭 Q,
    (primeClass_eq_one_iff K 𝔭).mpr hp, map_one]

/-- **The Hilbert class field exists**, from the two named inputs `UnramifiedArtinReciprocityInput K` and
`HilbertClassFieldDegreeInput K` (and the unconditional Chebotarev theorem). -/
@[kb "neukirch1999" "Ch. VI, §6-7: existence of the Hilbert class field, Cl_K ≅ Gal(H|K) [unverified locator]"]
theorem hilbertClassFieldExists_of_inputs (hA : UnramifiedArtinReciprocityInput K)
    (hB : HilbertClassFieldDegreeInput K) : HilbertClassFieldExists K := by
  obtain ⟨H, _, _, _, _, hab, hunr, hinf, hdeg⟩ := hB.exists_field
  obtain ⟨ψ, hψ⟩ := hA.exists_artin H hab hunr hinf
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance,
    isHilbertClassField_of_finrank_eq hunr hinf hdeg ψ hψ⟩

/-- **`HilbertClassFieldInput K` from the two named inputs**: there is a number field $H \supseteq K$
in which every nonzero prime of $\mathcal O_K$ splitting completely is principal. -/
@[kb "neukirch1999" "VI.7.3: a prime splitting completely in the Hilbert class field is principal [unverified locator]"]
theorem hilbertClassFieldInput_of_inputs (hA : UnramifiedArtinReciprocityInput K)
    (hB : HilbertClassFieldDegreeInput K) : HilbertClassFieldInput K :=
  hilbertClassFieldInput_of_exists (hilbertClassFieldExists_of_inputs hA hB)

end Existence

end

end NumberFieldKB.HilbertClassField
