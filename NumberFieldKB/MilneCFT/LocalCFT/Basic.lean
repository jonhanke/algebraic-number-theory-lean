import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import QuadFormsKB.Citation
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Norm.Open

/-!
# Local class field theory: the statements (Milne, *Class Field Theory*, Chapter I, §1)

**Setting** (Milne, Chapter I, introduction). $K$ is a nonarchimedean local field (Mathlib's
`IsNonarchimedeanLocalField`), with ring of integers $\mathcal O_K$ = `𝒪[K]`, maximal ideal $\mathfrak m$ = `𝓂[K]` and
residue field $k$ = `𝓀[K]` of $q$ elements. Milne fixes an algebraic closure $K^{\mathrm{al}}$ (a separable closure
when $K$ has characteristic $p$), and "extension of $K$" means "subfield of $K^{\mathrm{al}}$ containing $K$". Here
$K^{\mathrm{al}}$ is a field `Ω` with `IsSepClosure K Ω`, and extensions are `IntermediateField K Ω`.

**The Artin map as a compatible family.** Milne's local Artin map is a homomorphism
$\phi_K : K^\times \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$. Since $\mathrm{Gal}(K^{\mathrm{ab}}/K)$ is the inverse limit
of the groups $\mathrm{Gal}(L/K)$ over the finite abelian extensions $L$ (infinite Galois theory, Milne's Appendix A;
Mathlib's `InfiniteGalois.mulEquivToLimit`), such a homomorphism is the same as a family of homomorphisms
$\phi_L : K^\times \to \mathrm{Gal}(L/K)$ compatible with restriction, $\phi_L(a) = \phi_{L'}(a)|_L$ for
$L \subseteq L'$. The statements below use the family (`IsLocalArtinMap`); $\phi_L$ is Milne's
$a \mapsto \phi_K(a)|_L$, and its kernel and image are Milne's.

**Unramified extensions and Frobenius.** For a finite extension $L$ of $K$, $\mathcal O_L$ is the integral closure of
$\mathcal O_K$ in $L$. $L/K$ is unramified (`IsUnramifiedExt`) if $\mathfrak m\mathcal O_L$ is a maximal ideal
(then it is $\mathfrak m_L$: ramification index $1$; the residue extension is separable because $k$ is finite). The
Frobenius element (`IsFrobenius`) is an element $\sigma$ of $\mathrm{Gal}(L/K)$ with
$\sigma\alpha \equiv \alpha^q \pmod{\mathfrak m_L}$ for all $\alpha \in \mathcal O_L$.

## Named statements (inputs, never axioms)
* `LocalReciprocityExistence` — existence in Theorem 1.1 (the local reciprocity law).
* `LocalExistenceInput` — the hard half of Theorem 1.4 (every open subgroup of finite index is a norm group).
* `NormGroupOpenInput` — Lemma 1.3 (a norm group of finite index is open).
* `UnramifiedInput` — unramified extensions of every degree exist, are abelian, and have a unique Frobenius element
  (Milne, Chapter I, §1, p. 20; *ANT* 7.54).
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-! ## Extensions, norm groups, unramified extensions, Frobenius -/

/-- A **finite abelian extension** of $K$ inside $K^{\mathrm{al}} = \Omega$. -/
structure FiniteAbelianExt where
  /-- The subfield of $\Omega$. -/
  toField : IntermediateField K Ω
  [finiteDimensional : FiniteDimensional K toField]
  [isAbelianGalois : IsAbelianGalois K toField]

attribute [instance] FiniteAbelianExt.finiteDimensional FiniteAbelianExt.isAbelianGalois

variable {K Ω}

/-- The **norm group** $\mathrm{Nm}_{L/K}(L^\times) \subseteq K^\times$ of a finite extension $L$ of $K$ (Milne, *CFT*,
I, §1). -/
@[kb "milne2020cft" "Ch. I, §1 (norm groups, before Corollary 1.2)"]
def normGroup (L : IntermediateField K Ω) [FiniteDimensional K L] : Subgroup Kˣ :=
  (Units.map (Algebra.norm K (S := L))).range

variable (K Ω) in
/-- **Norm groups** (Milne, *CFT*, I, §1, after Theorem 1.1): the subgroups of $K^\times$ of the form
$\mathrm{Nm}(L^\times)$ for a finite abelian extension $L$ of $K$. -/
@[kb "milne2020cft" "Ch. I, §1 (definition of norm groups)"]
def IsNormGroup (N : Subgroup Kˣ) : Prop :=
  ∃ L : FiniteAbelianExt K Ω, normGroup L.toField = N

/-- The ring of integers $\mathcal O_L$ of a finite extension $L$ of $K$: the integral closure of $\mathcal O_K$. -/
abbrev integers (L : IntermediateField K Ω) : Subalgebra 𝒪[K] L := integralClosure 𝒪[K] L

/-- **Unramified finite extension** (Milne, *CFT*, I, §1; *ANT* 7.54): $\mathfrak m_K\mathcal O_L$ is a maximal ideal
of $\mathcal O_L$ (ramification index 1; the residue field extension is separable since $k$ is finite). -/
@[kb "milne2020cft" "Ch. I, §1 (finite unramified extensions)"]
def IsUnramifiedExt (L : IntermediateField K Ω) : Prop :=
  ((𝓂[K]).map (algebraMap 𝒪[K] (integers L))).IsMaximal

/-- **Frobenius element** (Milne, *CFT*, I, §1, p. 20): $\sigma \in \mathrm{Gal}(L/K)$ with
$\sigma\alpha \equiv \alpha^q \pmod{\mathfrak m_K\mathcal O_L}$ for all $\alpha \in \mathcal O_L$, $q = |k|$. For $L/K$
unramified $\mathfrak m_K\mathcal O_L = \mathfrak m_L$ and this is $\mathrm{Frob}_{L/K}$. -/
@[kb "milne2020cft" "Ch. I, §1 (Frobenius element Frob_{L/K})"]
def IsFrobenius (L : IntermediateField K Ω) (σ : Gal(L/K)) : Prop :=
  ∀ x ∈ integers L, ∃ y ∈ (𝓂[K]).map (algebraMap 𝒪[K] (integers L)),
    ((y : L)) = σ x - x ^ Nat.card 𝓀[K]

/-- A prime element $\pi$ of $K$ (an irreducible element of $\mathcal O_K$, i.e. a uniformizer), as a unit of $K$. -/
def primeUnit {π : 𝒪[K]} (hπ : Irreducible π) : Kˣ :=
  Units.mk0 (π : K) (by simpa using hπ.ne_zero)

@[simp] theorem coe_primeUnit {π : 𝒪[K]} (hπ : Irreducible π) : ((primeUnit hπ : Kˣ) : K) = π := rfl

/-- Restriction $\mathrm{Gal}(L'/K) \to \mathrm{Gal}(L/K)$ for $L \subseteq L'$, $L/K$ normal. -/
def galRestrict {L L' : IntermediateField K Ω} (h : L ≤ L') [Normal K L] : Gal(L'/K) →* Gal(L/K) :=
  letI : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  AlgEquiv.restrictNormalHom L

theorem galRestrict_apply {L L' : IntermediateField K Ω} (h : L ≤ L') [Normal K L] (σ : Gal(L'/K)) (x : L) :
    ((galRestrict h σ x : L) : Ω) = (σ (IntermediateField.inclusion h x) : Ω) := by
  let : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  exact congrArg (fun y : L' => (y : Ω)) (AlgEquiv.restrictNormal_commutes σ L x)

/-! ## The local Artin map (Theorem 1.1) -/

/-- **The conditions of Theorem 1.1** (Milne, *CFT*, I) on a family $\phi_L : K^\times \to \mathrm{Gal}(L/K)$, $L$
running over the finite abelian extensions: compatibility with restriction (so the family is one homomorphism
$K^\times \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$, see the module docstring); (a) for every prime element $\pi$ and every
finite unramified $L$, $\phi_L(\pi)$ is the Frobenius element; (b) the kernel of $\phi_L$ is
$\mathrm{Nm}(L^\times)$ and $\phi_L$ is onto, so that $\phi_L$ induces
$K^\times/\mathrm{Nm}(L^\times) \cong \mathrm{Gal}(L/K)$. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1 (conditions (a), (b))"]
structure IsLocalArtinMap (φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)) : Prop where
  compat : ∀ (L L' : FiniteAbelianExt K Ω) (h : L.toField ≤ L'.toField) (a : Kˣ),
    galRestrict h (φ L' a) = φ L a
  frobenius : ∀ {π : 𝒪[K]} (hπ : Irreducible π) (L : FiniteAbelianExt K Ω),
    IsUnramifiedExt L.toField → IsFrobenius L.toField (φ L (primeUnit hπ))
  ker_eq : ∀ L : FiniteAbelianExt K Ω, (φ L).ker = normGroup L.toField
  surjective : ∀ L : FiniteAbelianExt K Ω, Function.Surjective (φ L)

variable (K Ω)

/-- **Local reciprocity law, existence** (named statement; Milne, *CFT*, I, Theorem 1.1, existence part; proved in
Milne Chapter III, Theorem 3.4, or by Lubin–Tate theory, Chapter I, §§2–4): there is a family
$\phi_L : K^\times \to \mathrm{Gal}(L/K)$ satisfying the conditions of Theorem 1.1. Uniqueness follows
(`isLocalArtinMap_unique`, Theorem 1.13).

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.ker_localArtinMap` (`TauCeti/NumberTheory/ClassFieldTheory/Local/Reciprocity.lean:144`),
`TauCeti.ClassFieldTheory.surjective_localArtinMap` (same file, line 151),
`TauCeti.ClassFieldTheory.localArtinMap_uniformizer` (`TauCeti/NumberTheory/ClassFieldTheory/Local/Unramified.lean:342`)
and `TauCeti.ClassFieldTheory.artinMap_restrict` (`TauCeti/NumberTheory/ClassFieldTheory/Local/ArtinMap.lean:132`)
at Tau Ceti commit `7ed979dc`. Needed to apply it here: Tau Ceti proves the kernel, surjectivity and the
uniformizer-to-Frobenius property as separate theorems for each finite extension, and gets compatibility in towers from
its absolute Artin map. One must identify the abelianized Galois group with the Galois group for abelian extensions, and
our `IsFrobenius` with Tau Ceti's Frobenius automorphism.

**Proved here** for $K$ and $\Omega$ in `Type` (Tau Ceti's universe) as `localReciprocityExistence`
(`LocalCFT/ReciprocityTauCeti.lean`), from the ported Tau Ceti files. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1 (existence; input)"]
structure LocalReciprocityExistence : Prop where
  exists_artin : ∃ φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K), IsLocalArtinMap φ

/-- **Lemma 1.3** (named statement; Milne, *CFT*, I, Lemma 1.3): for a finite extension $L$ of $K$, if
$\mathrm{Nm}(L^\times)$ has finite index in $K^\times$ then it is open. (Milne's proof: $U_L$ is compact, so
$\mathrm{Nm}(U_L)$ is closed, of finite index in $U_K$, hence open.)

**Proved here** as `normGroupOpenInput`, from the ported copy under `NumberFieldKB/TauCetiPort/` of Tau Ceti
`TauCeti.isOpen_normGroup` (`TauCeti/NumberTheory/LocalField/Norm/Open.lean:102`) (read at Tau Ceti `7ed979dc`, ported from `67aa1716`).
Needed to apply it here: Tau Ceti proves openness for every finite separable extension of nonarchimedean local fields,
with no finite-index hypothesis, so ours is a weaker statement; one must identify our norm group with Tau Ceti's. -/
@[kb "milne2020cft" "Ch. I, Lemma 1.3 (input)"]
structure NormGroupOpenInput : Prop where
  isOpen : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L], (normGroup L).FiniteIndex →
    IsOpen (normGroup L : Set Kˣ)

/-- **Lemma 1.3, proved** (Milne, *CFT*, I, Lemma 1.3): the named statement `NormGroupOpenInput` holds, from Tau Ceti's
`TauCeti.isOpen_normGroup` (ported, `NumberFieldKB/TauCetiPort/NumberTheory/LocalField/Norm/Open.lean`), which proves
the norm group of every finite separable extension open, with no finite-index hypothesis. A finite extension inside the
separable closure $\Omega$ is separable. -/
@[kb "milne2020cft" "Ch. I, Lemma 1.3"]
theorem normGroupOpenInput : NormGroupOpenInput K Ω := by
  refine ⟨fun L _ _ => ?_⟩
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  exact TauCeti.isOpen_normGroup (K := K) (L := L)

/-- **Local existence theorem, the hard half** (named statement; Milne, *CFT*, I, Theorem 1.4; proved in Chapter III,
§5, or by Lubin–Tate theory, Chapter I, §3): every open subgroup of $K^\times$ of finite index is a norm group. The
converse holds given Theorem 1.1 and Lemma 1.3 (`isNormGroup_iff`).

**Proved elsewhere** (recorded, not imported): Yamaguchi
(`n-yamaguchi-0729/ClassFieldTheory`) `ClassFieldTheory.finiteAbelianLocalExistence_orderIso`
(`Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalExistenceOrderIso.lean:33`) at Yamaguchi
commit `fbd320c`. Needed to apply it here: Yamaguchi gives an order isomorphism onto the open subgroups of finite index
in every characteristic, sending an extension to its norm subgroup; one must identify its finite abelian local
extensions with our `FiniteAbelianExt K Ω`.

**Proved**, in parts of the library that are not included in this release, for $K$ of characteristic zero in `Type` as `localExistenceInput`, from the ported
Tau Ceti `TauCeti.ClassFieldTheory.localAbelianExistence`; and in every characteristic
and universe as `localExistenceInput_yamaguchi`, from the
ported Yamaguchi `ClassFieldTheory.finiteAbelianLocalExistence_orderIso`. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.4 (open subgroups of finite index are norm groups; input)"]
structure LocalExistenceInput : Prop where
  isNormGroup : ∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex → IsNormGroup K Ω H

/-- **Finite unramified extensions** (named statement; Milne, *CFT*, I, §1, p. 20, and *ANT* 7.54): for every
$m \ge 1$ there is a finite unramified extension of $K$ of degree $m$, and it is abelian (Milne: its Galois group is
cyclic, isomorphic to $\mathrm{Gal}(l/k)$); and in a finite unramified abelian extension the Frobenius element is
unique.

**Proved here** as `unramifiedInput` (`LocalCFT/UnramifiedTauCeti.lean`), from the ported Tau Ceti
`TauCeti.unramifiedExtension` and `TauCeti.eq_frobeniusAlgEquiv_of_valuation_sub_pow_lt_one`. -/
@[kb "milne2020cft" "Ch. I, §1, p. 20 (unramified extensions, Gal(L/K) ≅ Gal(l/k); input)"]
structure UnramifiedInput : Prop where
  exists_unramified : ∀ m : ℕ, 1 ≤ m → ∃ L : FiniteAbelianExt K Ω,
    IsUnramifiedExt L.toField ∧ Module.finrank K L.toField = m
  frobenius_unique : ∀ L : FiniteAbelianExt K Ω, IsUnramifiedExt L.toField →
    ∀ σ τ : Gal(L.toField/K), IsFrobenius L.toField σ → IsFrobenius L.toField τ → σ = τ

end NumberFieldKB.MilneCFT.LocalCFT
