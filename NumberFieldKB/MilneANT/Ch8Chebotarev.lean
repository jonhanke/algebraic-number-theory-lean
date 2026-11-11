import NumberFieldKB.MilneANT.Ch8Basic
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: the Chebotarev density theorem and its applications

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

**Which density.** Milne's "density" in Theorem 8.31 and after is the natural density (Definition 8.30,
`HasNaturalDensity`). The KB proves Chebotarev's theorem with Dirichlet density, unconditionally
(`NumberFieldKB.Chebotarev.chebotarev_unconditional`). The natural-density form needs the prime ideal theorem with
characters (a Tauberian argument); it is the **named statement** `Theorem8_31`, proved unconditionally in
`Ch8Thm831.lean` (`theorem8_31`) from the ported Tau Ceti theorem
`NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`. Everything below is stated in Milne's form (natural density) *conditional on* `Theorem8_31`, and in
addition *unconditionally* with Dirichlet density wherever the proof allows; the hypothesis-free natural-density
forms are in `Ch8Thm831Consumers.lean` (primed names). Natural density implies Dirichlet density
(`HasNaturalDensity.hasDirichletDensity`), so the unconditional results are consequences of the conditional ones'
hypotheses, never weaker statements of the same name.

* **Theorem 8.31** (`Theorem8_31`, named statement; `thm_8_31_dirichlet`, proved).
* **Corollary 8.32** (`cor_8_32`, conditional; `cor_8_32_dirichlet`, `cor_8_32_infinite`, proved).
* **Example 8.34** (`example_8_34`, conditional; `example_8_34_dirichlet`, proved): primes in arithmetic progressions.
* **Example 8.35** (`example_8_35`, conditional; `example_8_35_dirichlet`, proved): in a quadratic extension half the
  primes split and half stay prime.

Theorem 8.38, Corollary 8.39 and Remark 8.40 are in `Ch8Applications.lean`.
-/

open NumberField IsDedekindDomain Filter Topology
open NumberFieldKB.Chebotarev

namespace NumberFieldKB.MilneANT

noncomputable section

set_option linter.style.haveILetI false

/-! ## Helpers: densities and finite modifications -/

/-- Natural density is insensitive to finite changes: if the symmetric difference of `S` and `T` is finite, then `S`
and `T` have the same natural density. -/
theorem HasNaturalDensity.congr_finite {K : Type*} [Field K] [NumberField K]
    {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} (hS : HasNaturalDensity S δ)
    (hST : (symmDiff S T).Finite) : HasNaturalDensity T δ := by
  have h1 : (S \ T).Finite := hST.subset fun x hx => Or.inl hx
  have h2 : (T \ S).Finite := hST.subset fun x hx => Or.inr hx
  have key : ∀ (A B : Set (HeightOneSpectrum (𝓞 K))), (A \ B).Finite → ∀ x : ℝ,
      primeCount A x ≤ primeCount B x + (A \ B).ncard := by
    intro A B hAB x
    have hfin : {𝔭 : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x}.Finite :=
      finite_setOf_absNorm_le x
    have hsub : {𝔭 ∈ A | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} ⊆
        {𝔭 ∈ B | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} ∪ (A \ B) := by
      intro p hp
      by_cases hpB : p ∈ B
      · exact Or.inl ⟨hpB, hp.2⟩
      · exact Or.inr ⟨hp.1, hpB⟩
    have hfin' : ({𝔭 ∈ B | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} ∪ (A \ B)).Finite :=
      (hfin.subset fun p hp => hp.2).union hAB
    unfold primeCount
    exact (Set.ncard_le_ncard hsub hfin').trans (Set.ncard_union_le _ _)
  set c : ℝ := ((S \ T).ncard : ℝ) + ((T \ S).ncard : ℝ) with hc
  have hD : Tendsto (fun x : ℝ => (primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp tendsto_primeCount_univ
  have hbound : Tendsto (fun x : ℝ => c / (primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hD
  have hdiff : Tendsto (fun x : ℝ =>
      (primeCount T x : ℝ) / primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x -
      (primeCount S x : ℝ) / primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun x => ?_) hbound
    set D : ℝ := (primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x : ℝ)
    have hD0 : 0 ≤ D := Nat.cast_nonneg _
    have a1 : (primeCount S x : ℝ) ≤ primeCount T x + c := by
      have := key S T h1 x
      have : (primeCount S x : ℝ) ≤ primeCount T x + (S \ T).ncard := by exact_mod_cast this
      have : (0 : ℝ) ≤ (T \ S).ncard := Nat.cast_nonneg _
      linarith
    have a2 : (primeCount T x : ℝ) ≤ primeCount S x + c := by
      have := key T S h2 x
      have : (primeCount T x : ℝ) ≤ primeCount S x + (T \ S).ncard := by exact_mod_cast this
      have : (0 : ℝ) ≤ (S \ T).ncard := Nat.cast_nonneg _
      linarith
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_nonneg hD0]
    exact div_le_div_of_nonneg_right (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩) hD0
  have := hS.add hdiff
  rw [add_zero] at this
  refine this.congr fun x => ?_
  ring

/-- A set with a nonzero Dirichlet density is infinite. -/
theorem infinite_of_hasDirichletDensity {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} (hδ : δ ≠ 0) (h : S.HasDirichletDensity δ) : S.Infinite := by
  intro hfin
  have h0 := NumberFieldKB.Chebotarev.hasDirichletDensity_zero_of_finite hfin
  exact hδ (h.dirichletDensity_eq.symm.trans h0.dirichletDensity_eq)

/-- The conjugacy class of an element of a group in which any two elements commute is a singleton. -/
theorem carrier_mk_eq_singleton {G : Type*} [Group G] (hab : ∀ σ τ : G, σ * τ = τ * σ) (σ : G) :
    (ConjClasses.mk σ).carrier = {σ} := by
  ext g
  simp only [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, Set.mem_singleton_iff]
  constructor
  · intro hc
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    rw [hab c, mul_inv_cancel_right] at hc
    exact hc
  · rintro rfl
    exact IsConj.refl _

/-! ## Theorem 8.31 and Corollary 8.32 -/

/-- **Theorem 8.31 (Chebotarev density theorem)**, Milne's form (named statement): for a finite Galois extension $L/K$ of
number fields with Galois group $G$ and a conjugacy class $C$ of $G$, the set of primes $\mathfrak p$ of $K$ with
$(\mathfrak p, L/K) = C$ has **natural** density $|C|/|G|$. The Frobenius class $(\mathfrak p, L/K)$ is defined for
$\mathfrak p$ unramified in $L$ (`NumberFieldKB.Chebotarev.frobSet` is the set of unramified $\mathfrak p$ with class
$C$; the finitely many ramified primes do not affect a density). Milne refers to his class field theory notes for the
proof. Proved unconditionally: `theorem8_31` (`Ch8Thm831.lean`). The Dirichlet-density form is proved directly
(`thm_8_31_dirichlet`). -/
@[kb "milne2020ant" "v3.08, Thm. 8.31, p. 147"]
structure Theorem8_31 : Prop where
  natural_density : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (C : ConjClasses Gal(L/K)),
    HasNaturalDensity (frobSet K L C) (Nat.card C.carrier / Nat.card Gal(L/K))

section Galois

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **Theorem 8.31 with Dirichlet density** (proved, unconditionally): the library's
`NumberFieldKB.Chebotarev.chebotarev_unconditional`. Milne remarks that "normally one proves this result with a
slightly weaker notion of density". -/
@[kb "milne2020ant" "v3.08, Thm. 8.31 (Dirichlet density), p. 147"]
theorem thm_8_31_dirichlet (C : ConjClasses Gal(L/K)) :
    (frobSet K L C).HasDirichletDensity (Nat.card C.carrier / Nat.card Gal(L/K)) :=
  chebotarev_unconditional K L C

/-- **Corollary 8.32** (conditional on `Theorem8_31`): the primes of $K$ that split completely in $L$ have natural
density $1/[L:K]$. -/
@[kb "milne2020ant" "v3.08, Cor. 8.32, p. 147"]
theorem cor_8_32 (h : Theorem8_31) :
    HasNaturalDensity (splitPrimes K L) (1 / Module.finrank K L) := by
  have h1 : Nat.card (ConjClasses.mk (1 : Gal(L/K))).carrier = 1 := by
    have : (ConjClasses.mk (1 : Gal(L/K))).carrier = {1} := by
      ext g
      simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    rw [this, Nat.card_unique]
  have h2 := h.natural_density K L (ConjClasses.mk 1)
  rw [h1, IsGalois.card_aut_eq_finrank, Nat.cast_one] at h2
  rw [splitPrimes_eq_frobSet_one]
  exact h2

/-- **Corollary 8.32 with Dirichlet density** (proved, unconditionally): the library's
`NumberFieldKB.Chebotarev.splitPrimes_hasDirichletDensity_unconditional`. -/
@[kb "milne2020ant" "v3.08, Cor. 8.32 (Dirichlet density), p. 147"]
theorem cor_8_32_dirichlet :
    (splitPrimes K L).HasDirichletDensity (1 / Module.finrank K L) :=
  splitPrimes_hasDirichletDensity_unconditional K L

/-- **Corollary 8.32, second sentence** (proved, unconditionally): infinitely many primes of $K$ split completely in
$L$. -/
@[kb "milne2020ant" "v3.08, Cor. 8.32, p. 147"]
theorem cor_8_32_infinite : (splitPrimes K L).Infinite := by
  refine infinite_of_hasDirichletDensity ?_ (cor_8_32_dirichlet K L)
  have : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  positivity

/-- Milne p. 147: for abelian $G$ and $\sigma \in G$, the primes with $(\mathfrak p, L/K) = \sigma$ have density
$1/|G|$ (conditional on `Theorem8_31`). -/
@[kb "milne2020ant" "v3.08, Thm. 8.31 (abelian case), p. 147"]
theorem thm_8_31_abelian (h : Theorem8_31) (hab : ∀ σ τ : Gal(L/K), σ * τ = τ * σ) (σ : Gal(L/K)) :
    HasNaturalDensity (frobSet K L (ConjClasses.mk σ)) (1 / Nat.card Gal(L/K)) := by
  have h2 := h.natural_density K L (ConjClasses.mk σ)
  rwa [carrier_mk_eq_singleton hab σ, Nat.card_unique, Nat.cast_one] at h2

end Galois

/-! ## Examples 8.34 and 8.35 -/

/-- The rational prime $p$ below a prime ideal of `𝓞 ℚ` (Mathlib's `Rat.HeightOneSpectrum.natGenerator`). -/
abbrev ratPrime (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator v

section Cyclotomic

variable (n : ℕ) [NeZero n]

/-- Helper instance (Mathlib's instance is not found by search for `ℚ`). -/
instance cyclotomicField_isCyclotomicExtension :
    IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
  CyclotomicField.isCyclotomicExtension n ℚ

/-- Helper instance: $\mathbb Q(\zeta_n)/\mathbb Q$ is Galois. -/
instance cyclotomicField_isGalois : IsGalois ℚ (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.isGalois {n} ℚ _

/-- Helper: in $\mathbb Q(\zeta_n)/\mathbb Q$ the Galois group is abelian. -/
theorem cyclotomic_comm (a b : Gal(CyclotomicField n ℚ/ℚ)) : a * b = b * a := by
  have hirr := Polynomial.cyclotomic.irreducible_rat (n := n) (Nat.pos_of_ne_zero (NeZero.ne n))
  exact (IsCyclotomicExtension.autEquivPow (CyclotomicField n ℚ) hirr).injective
    (by rw [map_mul, map_mul, mul_comm])

/-- Helper: the Galois group of $\mathbb Q(\zeta_n)/\mathbb Q$ has $\varphi(n)$ elements. -/
theorem cyclotomic_card : Nat.card Gal(CyclotomicField n ℚ/ℚ) = n.totient := by
  rw [IsGalois.card_aut_eq_finrank]
  exact IsCyclotomicExtension.Rat.finrank n (CyclotomicField n ℚ)

/-- Helper: for $\gcd(k, n) = 1$ there is $\sigma \in \mathrm{Gal}(\mathbb Q(\zeta_n)/\mathbb Q)$ such that the primes
$p \equiv k \pmod n$ and the primes with Frobenius $\sigma$ differ by finitely many primes. -/
theorem cyclotomic_exists_frob (k : ℕ) (hk : k.Coprime n) :
    ∃ σ : Gal(CyclotomicField n ℚ/ℚ),
      (symmDiff {v : HeightOneSpectrum (𝓞 ℚ) | (ratPrime v : ZMod n) = k}
        (frobSet ℚ (CyclotomicField n ℚ) (ConjClasses.mk σ))).Finite := by
  classical
  set M := CyclotomicField n ℚ
  have hirr := Polynomial.cyclotomic.irreducible_rat (n := n) (Nat.pos_of_ne_zero (NeZero.ne n))
  set e := IsCyclotomicExtension.autEquivPow M hirr with he_def
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ M
  have he : ∀ g, e g = hζ.autToPow ℚ g := fun g => rfl
  have hcomm := cyclotomic_comm n
  set u : (ZMod n)ˣ := ZMod.unitOfCoprime k hk with hu
  refine ⟨e.symm u, ?_⟩
  refine ((finite_compl_unramifiedPrimes ℚ M).union (finite_not_coprime (F := ℚ) n)).subset ?_
  intro v hv
  by_contra hcon
  have hunr : v ∈ unramifiedPrimes ℚ M := by
    by_contra h
    exact hcon (Or.inl h)
  have hcop : (Ideal.absNorm v.asIdeal).Coprime n := by
    by_contra h
    exact hcon (Or.inr h)
  obtain ⟨Q⟩ : Nonempty (v.asIdeal.primesOver (𝓞 M)) := inferInstance
  have hfr : ((hζ.autToPow ℚ (frobAt ℚ M v Q) : (ZMod n)ˣ) : ZMod n) = (ratPrime v : ZMod n) := by
    rw [autToPow_frobAt ℚ n hcop Q, RatIdele.absNorm_asIdeal]
  have key : (ratPrime v : ZMod n) = k ↔ v ∈ frobSet ℚ M (ConjClasses.mk (e.symm u)) := by
    change _ ↔ v ∈ unramifiedPrimes ℚ M ∧ frobClass ℚ M v = _
    rw [frobClass_eq_mk_frobAt ℚ M v Q, ConjClasses.mk_eq_mk_iff_isConj]
    have hconj : IsConj (frobAt ℚ M v Q) (e.symm u) ↔ frobAt ℚ M v Q = e.symm u := by
      constructor
      · intro hc
        obtain ⟨c, hc⟩ := isConj_iff.1 hc
        rw [hcomm c, mul_inv_cancel_right] at hc
        exact hc
      · intro h
        rw [h]
    rw [hconj, e.eq_symm_apply, he, ← Units.val_inj, hfr, hu, ZMod.coe_unitOfCoprime]
    simp [hunr]
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (key.1 h1)
  · exact h2 (key.2 h1)

end Cyclotomic

/-- **Example 8.34 with Dirichlet density** (proved, unconditionally): for $n\ge1$ and $\gcd(k,n) = 1$ the primes
$p \equiv k \pmod n$ have Dirichlet density $1/\varphi(n)$; Milne derives it from Chebotarev for
$\mathbb Q(\zeta_n)/\mathbb Q$, whose Frobenius at $p$ is the class of $p$ in $(\mathbb Z/n)^\times$ (Example 8.18,
`example_8_18`). -/
@[kb "milne2020ant" "v3.08, Ex. 8.34 (Dirichlet density), p. 148"]
theorem example_8_34_dirichlet (n : ℕ) [NeZero n] (k : ℕ) (hk : k.Coprime n) :
    {v : HeightOneSpectrum (𝓞 ℚ) | (ratPrime v : ZMod n) = k}.HasDirichletDensity (1 / n.totient) := by
  obtain ⟨σ, hσ⟩ := cyclotomic_exists_frob n k hk
  have h := cyclotomic_density idelicNormInput ℚ (CyclotomicField n ℚ) n σ
  rw [IsCyclotomicExtension.Rat.finrank n (CyclotomicField n ℚ)] at h
  exact HasDirichletDensity.congr_finite h (by rwa [symmDiff_comm])

/-- **Example 8.34** (conditional on `Theorem8_31`): each arithmetic progression $k, k+n, k+2n,\dots$ with
$\gcd(k, n) = 1$ contains $1/\varphi(n)$ of the primes (natural density). -/
@[kb "milne2020ant" "v3.08, Ex. 8.34, p. 148"]
theorem example_8_34 (h : Theorem8_31) (n : ℕ) [NeZero n] (k : ℕ) (hk : k.Coprime n) :
    HasNaturalDensity {v : HeightOneSpectrum (𝓞 ℚ) | (ratPrime v : ZMod n) = k} (1 / n.totient) := by
  obtain ⟨σ, hσ⟩ := cyclotomic_exists_frob n k hk
  have h2 := h.natural_density ℚ (CyclotomicField n ℚ) (ConjClasses.mk σ)
  rw [carrier_mk_eq_singleton (cyclotomic_comm n) σ, Nat.card_unique, cyclotomic_card, Nat.cast_one] at h2
  exact HasNaturalDensity.congr_finite h2 (by rwa [symmDiff_comm])

/-- **Example 8.34, last claim** (proved, unconditionally): each such progression contains infinitely many primes. -/
@[kb "milne2020ant" "v3.08, Ex. 8.34, p. 148"]
theorem example_8_34_infinite (n : ℕ) [NeZero n] (k : ℕ) (hk : k.Coprime n) :
    {v : HeightOneSpectrum (𝓞 ℚ) | (ratPrime v : ZMod n) = k}.Infinite := by
  refine infinite_of_hasDirichletDensity ?_ (example_8_34_dirichlet n k hk)
  have : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  positivity

section Quadratic

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The primes of $K$ that **remain prime** (are inert) in $L$: $\mathfrak p\mathcal O_L$ is a prime ideal, i.e. there
is one prime above $\mathfrak p$, with $e = 1$ and $f = [L:K]$. -/
def inertPrimes : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | ∀ Q : 𝔭.asIdeal.primesOver (𝓞 L),
    Q.1.ramificationIdx (𝓞 K) = 1 ∧ Q.1.inertiaDeg (𝓞 K) = Module.finrank K L}

/-- Helper: a degree-2 extension of number fields is Galois. -/
theorem isGalois_of_finrank_eq_two (h2 : Module.finrank K L = 2) : IsGalois K L := by
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  infer_instance

/-- Helper: the Galois group of a degree-2 Galois extension is $\{1, \tau\}$ with $\tau \ne 1$. -/
theorem quadratic_exists_nontrivial [IsGalois K L] (h2 : Module.finrank K L = 2) :
    ∃ τ : Gal(L/K), τ ≠ 1 ∧ ∀ g : Gal(L/K), g = 1 ∨ g = τ := by
  have hcard : Nat.card Gal(L/K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨τ, hτ, huniq⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).1 hcard
  refine ⟨τ, hτ, fun g => ?_⟩
  by_cases hg : g = 1
  · exact Or.inl hg
  · exact Or.inr (huniq g hg)

/-- Helper: for a prime unramified in a degree-2 Galois extension, being inert is the same as not splitting
completely. -/
theorem mem_inertPrimes_iff_of_unramified [IsGalois K L] (h2 : Module.finrank K L = 2)
    {𝔭 : HeightOneSpectrum (𝓞 K)} (hunr : 𝔭 ∈ unramifiedPrimes K L) :
    𝔭 ∈ inertPrimes K L ↔ 𝔭 ∉ splitPrimes K L := by
  have hram : ∀ Q : 𝔭.asIdeal.primesOver (𝓞 L), Q.1.ramificationIdx (𝓞 K) = 1 := by
    intro Q
    haveI := Q.2.1
    haveI := Q.2.2
    haveI := finite_quotient_of_ne_bot Q.1 (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1)
    haveI hu : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := hunr Q.1 Q.2.1 Q.2.2
    exact Ideal.ramificationIdx_eq_one_iff.mpr hu
  have hid := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭.asIdeal (𝓞 L) Gal(L/K)
  rw [IsGaloisGroup.card_eq_finrank Gal(L/K) K L, h2] at hid
  obtain ⟨Q₀⟩ : Nonempty (𝔭.asIdeal.primesOver (𝓞 L)) := inferInstance
  have hfQ : ∀ Q : 𝔭.asIdeal.primesOver (𝓞 L),
      Q.1.inertiaDeg (𝓞 K) = 𝔭.asIdeal.inertiaDegIn (𝓞 L) := by
    intro Q
    haveI := Q.2.1
    haveI := Q.2.2
    exact (Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal Q.1 Gal(L/K)).symm
  have hrIn : 𝔭.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
    haveI := Q₀.2.1
    haveI := Q₀.2.2
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal Q₀.1 Gal(L/K)]
    exact hram Q₀
  rw [hrIn, one_mul] at hid
  have hdvd : 𝔭.asIdeal.inertiaDegIn (𝓞 L) ∣ 2 := ⟨_, by rw [← hid]; ring⟩
  constructor
  · intro hin hsp
    have h1 := (hin Q₀).2
    have h3 := (hsp Q₀).2
    rw [h2] at h1
    omega
  · intro hns Q
    refine ⟨hram Q, ?_⟩
    rw [hfQ Q, h2]
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exfalso
      apply hns
      intro Q'
      exact ⟨hram Q', by rw [hfQ Q', h]⟩
    · exact h

/-- Helper: in a degree-2 Galois extension the inert primes and the primes with Frobenius class $\{\tau\}$
($\tau \ne 1$) differ by finitely many primes. -/
theorem quadratic_inert_finite [IsGalois K L] (h2 : Module.finrank K L = 2) {τ : Gal(L/K)} (hτ : τ ≠ 1)
    (hall : ∀ g : Gal(L/K), g = 1 ∨ g = τ) :
    (symmDiff (frobSet K L (ConjClasses.mk τ)) (inertPrimes K L)).Finite := by
  refine (finite_compl_unramifiedPrimes K L).subset ?_
  intro 𝔭 h𝔭
  by_contra hunr'
  have hunr : 𝔭 ∈ unramifiedPrimes K L := not_not.1 hunr'
  have key : 𝔭 ∈ frobSet K L (ConjClasses.mk τ) ↔ 𝔭 ∈ inertPrimes K L := by
    rw [mem_inertPrimes_iff_of_unramified K L h2 hunr, splitPrimes_eq_frobSet_one]
    obtain ⟨Q⟩ : Nonempty (𝔭.asIdeal.primesOver (𝓞 L)) := inferInstance
    have hcl : frobClass K L 𝔭 = ConjClasses.mk (frobAt K L 𝔭 Q) := frobClass_eq_mk_frobAt K L 𝔭 Q
    change (𝔭 ∈ unramifiedPrimes K L ∧ frobClass K L 𝔭 = ConjClasses.mk τ) ↔
      ¬ (𝔭 ∈ unramifiedPrimes K L ∧ frobClass K L 𝔭 = ConjClasses.mk 1)
    rw [hcl, ConjClasses.mk_eq_mk_iff_isConj, ConjClasses.mk_eq_mk_iff_isConj]
    rcases hall (frobAt K L 𝔭 Q) with h | h
    · rw [h]
      constructor
      · rintro ⟨-, hc⟩
        exact absurd (isConj_one_right.1 hc) hτ
      · intro hn
        exact absurd ⟨hunr, IsConj.refl _⟩ hn
    · rw [h]
      constructor
      · rintro _ ⟨-, hc'⟩
        exact hτ (isConj_one_left.1 hc')
      · intro _
        exact ⟨hunr, IsConj.refl _⟩
  rcases h𝔭 with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · exact h3 (key.1 h1)
  · exact h3 (key.2 h1)

/-- **Example 8.35 with Dirichlet density** (proved, unconditionally): in a quadratic extension half the primes split
and half remain prime. -/
@[kb "milne2020ant" "v3.08, Ex. 8.35 (Dirichlet density), p. 148"]
theorem example_8_35_dirichlet (h2 : Module.finrank K L = 2) :
    (splitPrimes K L).HasDirichletDensity (1 / 2) ∧ (inertPrimes K L).HasDirichletDensity (1 / 2) := by
  haveI := isGalois_of_finrank_eq_two K L h2
  obtain ⟨τ, hτ, hall⟩ := quadratic_exists_nontrivial K L h2
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := by
    intro a b
    rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl <;> simp
  have hcard : Nat.card Gal(L/K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  refine ⟨?_, ?_⟩
  · have := cor_8_32_dirichlet K L
    rwa [h2, Nat.cast_ofNat] at this
  · have h := thm_8_31_dirichlet K L (ConjClasses.mk τ)
    rw [carrier_mk_eq_singleton hcomm τ, Nat.card_unique, hcard, Nat.cast_one, Nat.cast_ofNat] at h
    exact HasDirichletDensity.congr_finite h (quadratic_inert_finite K L h2 hτ hall)

/-- **Example 8.35** (conditional on `Theorem8_31`): in a quadratic extension half the primes split and half remain
prime (natural density). -/
@[kb "milne2020ant" "v3.08, Ex. 8.35, p. 148"]
theorem example_8_35 (h : Theorem8_31) (h2 : Module.finrank K L = 2) :
    HasNaturalDensity (splitPrimes K L) (1 / 2) ∧ HasNaturalDensity (inertPrimes K L) (1 / 2) := by
  haveI := isGalois_of_finrank_eq_two K L h2
  obtain ⟨τ, hτ, hall⟩ := quadratic_exists_nontrivial K L h2
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := by
    intro a b
    rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl <;> simp
  have hcard : Nat.card Gal(L/K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  refine ⟨?_, ?_⟩
  · have := cor_8_32 K L h
    rwa [h2, Nat.cast_ofNat] at this
  · have h' := h.natural_density K L (ConjClasses.mk τ)
    rw [carrier_mk_eq_singleton hcomm τ, Nat.card_unique, hcard, Nat.cast_one, Nat.cast_ofNat] at h'
    exact HasNaturalDensity.congr_finite h' (quadratic_inert_finite K L h2 hτ hall)

end Quadratic

end

end NumberFieldKB.MilneANT
