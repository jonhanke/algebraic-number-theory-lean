import NumberFieldKB.Chebotarev.Basic
import NumberFieldKB.Chebotarev.FrobeniusNF

/-!
# The Hilbert class field: definitions, splitting and Frobenius, class number one

Mathlib v4.35.0 has no class field theory. This file sets up what can be proved without it:

* `SplitsCompletelyIn K E 𝔭` and `HilbertClassFieldInput F`: splitting completely, and the weak form of the
  existence of the Hilbert class field (every prime splitting completely in some finite extension is principal).
* **Splitting and Frobenius** (`splitsCompletelyIn_iff_frobAt_eq_one`): for $L/K$ Galois and $\mathfrak p$ unramified in
  $L$, $\mathfrak p$ splits completely in $L$ iff $\mathrm{Frob}_\mathfrak P = 1$ for one (equivalently every)
  $\mathfrak P \mid \mathfrak p$.
* **`IsHilbertClassField K H`**: $H/K$ is Galois, unramified at every finite prime and every infinite place, and the
  Artin map $[\mathfrak p] \mapsto \mathrm{Frob}_\mathfrak p$ is an isomorphism $\mathrm{Cl}_K \cong \mathrm{Gal}(H/K)$.
  Then a nonzero prime of $\mathcal O_K$ is principal iff it splits completely in $H$
  (`isPrincipal_iff_splitsCompletelyIn`), so `IsHilbertClassField K H` gives `HilbertClassFieldInput K`
  (`hilbertClassFieldInput_of_isHilbertClassField`).
* **Class number one**: $H = K$ works (`hilbertClassFieldInput_of_classNumber_eq_one`), in particular for
  $\mathbb Q$, $\mathbb Q(\zeta_3) = \mathbb Q(\sqrt{-3})$ and $\mathbb Q(\zeta_5)$.

The existence of the Hilbert class field and the surjectivity of the Artin map (via Chebotarev) are in
`NumberFieldKB.HilbertClassField.Artin`.

Indexing: primes of $K$ are either ideals `𝔭 : Ideal (𝓞 K)` with `𝔭.IsPrime`, `𝔭 ≠ ⊥` (as in `SplitsCompletelyIn`), or
`HeightOneSpectrum (𝓞 K)` (as in the Chebotarev files); `mem_splitPrimes_iff` relates the two splitting notions.
-/

open NumberField IsDedekindDomain Ideal
open NumberFieldKB.Chebotarev

namespace NumberFieldKB.HilbertClassField

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **A prime of $\mathcal O_K$ splits completely in $E$**: every prime ideal $\mathfrak P$ of $\mathcal O_E$ lying over
$\mathfrak p$ has ramification index $e(\mathfrak P/\mathfrak p) = 1$ and inertia degree $f(\mathfrak P/\mathfrak p) = 1$.
-/
def SplitsCompletelyIn (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (𝔭 : Ideal (𝓞 K)) : Prop :=
  ∀ 𝔓 : Ideal (𝓞 E), 𝔓.IsPrime → 𝔓.LiesOver 𝔭 → 𝔓.ramificationIdx (𝓞 K) = 1 ∧ 𝔓.inertiaDeg (𝓞 K) = 1

/-- **Hilbert class field, weak form** (Neukirch 1999, VI.7.3 [unverified locator]): there is a finite extension $H$ of
$F$ such that every nonzero prime ideal of $\mathcal O_F$ that splits completely in $H$ is principal. Here it is proved for class number one
(`hilbertClassFieldInput_of_classNumber_eq_one`) and derived from the existence of the Hilbert class field
(`hilbertClassFieldInput_of_isHilbertClassField`).

**Proved elsewhere** (recorded, not imported): Yamaguchi
(`n-yamaguchi-0729/ClassFieldTheory`)
`ClassFieldTheory.finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal`
(`Nyll/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldPrimeSplitting.lean:31`) at
Yamaguchi commit `fbd320c`. Needed to apply it here: we need only the direction from splitting completely to principal,
while Yamaguchi proves an equivalence for its small Hilbert class field; one must compare its notion of splitting
completely with our `SplitsCompletelyIn`. -/
@[kb "neukirch1999" "VI.7.3: a prime of F splitting completely in the Hilbert class field is principal [unverified locator]"]
structure HilbertClassFieldInput (F : Type) [Field F] [NumberField F] : Prop where
  exists_field : ∃ (H : Type) (_ : Field H) (_ : NumberField H) (_ : Algebra F H),
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsPrime → 𝔭 ≠ ⊥ → SplitsCompletelyIn F H 𝔭 → Submodule.IsPrincipal 𝔭

/-! ## §1. Class number one -/

section ClassNumberOne

variable {F : Type} [Field F] [NumberField F]

/-- **The Hilbert class field of a field of class number one is the field itself** (weak form): if $\mathcal O_F$ is a
principal ideal domain, $H = F$ satisfies `HilbertClassFieldInput F` (every ideal is principal). -/
@[kb "neukirch1999" "VI.7.3 for class number one: H = F [unverified locator]"]
theorem hilbertClassFieldInput_of_isPrincipalIdealRing [IsPrincipalIdealRing (𝓞 F)] :
    HilbertClassFieldInput F :=
  ⟨⟨F, inferInstance, inferInstance, inferInstance, fun 𝔭 _ _ _ => IsPrincipalIdealRing.principal 𝔭⟩⟩

/-- **Class number one** (`NumberField.classNumber F = 1`): `HilbertClassFieldInput F` holds with $H = F$. -/
@[kb "neukirch1999" "VI.7.3 for class number one: H = F [unverified locator]"]
theorem hilbertClassFieldInput_of_classNumber_eq_one (h : classNumber F = 1) : HilbertClassFieldInput F :=
  haveI := classNumber_eq_one_iff.mp h
  hilbertClassFieldInput_of_isPrincipalIdealRing

/-- `HilbertClassFieldInput ℚ` (Mathlib's `Rat.classNumber_eq`). -/
theorem hilbertClassFieldInput_rat : HilbertClassFieldInput ℚ :=
  hilbertClassFieldInput_of_classNumber_eq_one Rat.classNumber_eq

/-- `HilbertClassFieldInput` for $\mathbb Q(\zeta_3) = \mathbb Q(\sqrt{-3})$, an imaginary quadratic field of class
number one (Mathlib's `IsCyclotomicExtension.Rat.three_pid`). -/
theorem hilbertClassFieldInput_cyclotomic_three : HilbertClassFieldInput (CyclotomicField 3 ℚ) :=
  haveI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) := CyclotomicField.isCyclotomicExtension 3 ℚ
  haveI := IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
  hilbertClassFieldInput_of_isPrincipalIdealRing

/-- `HilbertClassFieldInput` for $\mathbb Q(\zeta_5)$, of class number one (Mathlib's
`IsCyclotomicExtension.Rat.five_pid`). -/
theorem hilbertClassFieldInput_cyclotomic_five : HilbertClassFieldInput (CyclotomicField 5 ℚ) :=
  haveI : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) := CyclotomicField.isCyclotomicExtension 5 ℚ
  haveI := IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)
  hilbertClassFieldInput_of_isPrincipalIdealRing

end ClassNumberOne

/-! ## §2. Splitting completely and Frobenius -/

section Splitting

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The two notions of complete splitting agree: `𝔭 ∈ splitPrimes K L` (Chebotarev files, quantified over
`𝔭.asIdeal.primesOver (𝓞 L)`) iff `SplitsCompletelyIn K L 𝔭.asIdeal`. -/
theorem mem_splitPrimes_iff (𝔭 : HeightOneSpectrum (𝓞 K)) :
    𝔭 ∈ splitPrimes K L ↔ SplitsCompletelyIn K L 𝔭.asIdeal :=
  ⟨fun h 𝔓 h1 h2 => h ⟨𝔓, h1, h2⟩, fun h Q => h Q.1 Q.2.1 Q.2.2⟩

variable [IsGalois K L]

/-- **Splitting via Frobenius**: for $L/K$ Galois, $\mathfrak p$ a nonzero prime of $\mathcal O_K$ unramified in $L$
and $\mathfrak P \mid \mathfrak p$, the prime $\mathfrak p$ splits completely in $L$ iff $\mathrm{Frob}_\mathfrak P = 1$.
*Proof:* $\mathrm{ord}\,\mathrm{Frob}_\mathfrak P = f(\mathfrak P/\mathfrak p)$ (`arithFrobAt_eq_one_iff_nf`), $e = 1$
at every prime above (unramified), and $f$ is the same at every prime above (Galois). -/
theorem splitsCompletelyIn_iff_frobAt_eq_one (𝔭 : HeightOneSpectrum (𝓞 K))
    (h𝔭 : 𝔭 ∈ unramifiedPrimes K L) (Q : 𝔭.asIdeal.primesOver (𝓞 L)) :
    SplitsCompletelyIn K L 𝔭.asIdeal ↔ frobAt K L 𝔭 Q = 1 := by
  haveI := Q.2.1
  haveI := Q.2.2
  haveI := isMaximal_of_mem_primesOver K L 𝔭 Q
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  haveI : Finite (𝓞 L ⧸ Q.1) :=
    finite_quotient_of_ne_bot Q.1 (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1)
  haveI : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := h𝔭 Q.1 Q.2.1 Q.2.2
  change _ ↔ arithFrobAt (𝓞 K) Gal(L/K) Q.1 = 1
  rw [arithFrobAt_eq_one_iff_nf]
  constructor
  · intro h
    exact (h Q.1 Q.2.1 Q.2.2).2
  · intro hf 𝔓 h1 h2
    haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 := h𝔭 𝔓 h1 h2
    refine ⟨Ideal.ramificationIdx_eq_one 𝔓 (𝓞 K), ?_⟩
    rw [Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal 𝔓 Q.1 Gal(L/K)]
    exact hf

end Splitting

/-! ## §3. The Hilbert class field and the Artin isomorphism -/

section HilbertClassField

variable (K : Type) [Field K] [NumberField K]

/-- The ideal class $[\mathfrak p] \in \mathrm{Cl}_K$ of a nonzero prime $\mathfrak p$ of $\mathcal O_K$. -/
def primeClass (𝔭 : HeightOneSpectrum (𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩

/-- $[\mathfrak p] = 1$ iff $\mathfrak p$ is principal (Mathlib's `ClassGroup.mk0_eq_one_iff`). -/
theorem primeClass_eq_one_iff (𝔭 : HeightOneSpectrum (𝓞 K)) :
    primeClass K 𝔭 = 1 ↔ Submodule.IsPrincipal 𝔭.asIdeal :=
  ClassGroup.mk0_eq_one_iff _

variable (H : Type) [Field H] [NumberField H] [Algebra K H] [IsGalois K H]

/-- **$H$ is a Hilbert class field of $K$** (Neukirch 1999, Ch. VI, §6-7 [unverified locator]; Milne, *Class
Field Theory*, V [unverified locator]): $H/K$ is a finite Galois extension, unramified at every nonzero prime of
$\mathcal O_K$ and at every infinite place, and there is an isomorphism $\mathrm{Cl}_K \cong \mathrm{Gal}(H/K)$ (the
Artin map) sending the class of each prime $\mathfrak p$ to its Frobenius $\mathrm{Frob}_\mathfrak P$ (any
$\mathfrak P \mid \mathfrak p$). In particular $\mathrm{Gal}(H/K)$ is abelian, and all Frobenius elements above
$\mathfrak p$ coincide. -/
structure IsHilbertClassField : Prop where
  isUnramifiedIn : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∈ unramifiedPrimes K H
  isUnramifiedAtInfinitePlaces : IsUnramifiedAtInfinitePlaces K H
  exists_artin : ∃ ψ : ClassGroup (𝓞 K) ≃* Gal(H/K),
    ∀ (𝔭 : HeightOneSpectrum (𝓞 K)) (Q : 𝔭.asIdeal.primesOver (𝓞 H)), ψ (primeClass K 𝔭) = frobAt K H 𝔭 Q

variable {K H}

/-- **Principal primes are exactly the primes splitting completely in the Hilbert class field** (Neukirch 1999, VI.7.3
[unverified locator]): if `IsHilbertClassField K H`, a nonzero prime $\mathfrak p$ of $\mathcal O_K$ is principal iff it
splits completely in $H$. *Proof:* $\mathfrak p$ principal $\iff [\mathfrak p] = 1 \iff \mathrm{Frob}_\mathfrak P = 1$
(the Artin map is injective) $\iff \mathfrak p$ splits completely (`splitsCompletelyIn_iff_frobAt_eq_one`). -/
@[kb "neukirch1999" "VI.7.3: p principal iff p splits completely in the Hilbert class field [unverified locator]"]
theorem isPrincipal_iff_splitsCompletelyIn (hH : IsHilbertClassField K H) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Submodule.IsPrincipal 𝔭.asIdeal ↔ SplitsCompletelyIn K H 𝔭.asIdeal := by
  obtain ⟨ψ, hψ⟩ := hH.exists_artin
  have Q : 𝔭.asIdeal.primesOver (𝓞 H) := Classical.arbitrary _
  rw [splitsCompletelyIn_iff_frobAt_eq_one K H 𝔭 (hH.isUnramifiedIn 𝔭) Q, ← hψ 𝔭 Q,
    ← primeClass_eq_one_iff, map_eq_one_iff ψ ψ.injective]

/-- **`IsHilbertClassField K H` gives `HilbertClassFieldInput K`**: every nonzero prime splitting
completely in $H$ is principal. -/
@[kb "neukirch1999" "VI.7.3: a prime splitting completely in the Hilbert class field is principal [unverified locator]"]
theorem hilbertClassFieldInput_of_isHilbertClassField (hH : IsHilbertClassField K H) :
    HilbertClassFieldInput K :=
  ⟨⟨H, inferInstance, inferInstance, inferInstance, fun 𝔭 hp h0 hs =>
    (isPrincipal_iff_splitsCompletelyIn hH ⟨𝔭, hp, h0⟩).mpr hs⟩⟩

variable (K) in
/-- **The Hilbert class field exists** (Hilbert, Furtwängler; Neukirch 1999, Ch. VI, §6 [unverified locator]): there is a
number field $H \supseteq K$ with `IsHilbertClassField K H`. Not proved here: it is
`isHilbertClassField_exists_of_inputs` (`NumberFieldKB.HilbertClassField.Artin`) from two named class-field-theory
inputs. -/
def HilbertClassFieldExists : Prop :=
  ∃ (H : Type) (_ : Field H) (_ : NumberField H) (_ : Algebra K H) (_ : IsGalois K H), IsHilbertClassField K H

/-- The existence of the Hilbert class field gives `HilbertClassFieldInput K`. -/
theorem hilbertClassFieldInput_of_exists (h : HilbertClassFieldExists K) : HilbertClassFieldInput K := by
  obtain ⟨H, _, _, _, _, hH⟩ := h
  exact hilbertClassFieldInput_of_isHilbertClassField hH

end HilbertClassField

end

end NumberFieldKB.HilbertClassField
