import NumberFieldKB.MilneANT.Ch8Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: decomposition groups in towers; the Frobenius element

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Conventions as in `Ch8Decomposition.lean`: decomposition groups are Mathlib's `MulAction.stabilizer`, Frobenius
elements satisfy Mathlib's `IsArithFrobAt` ($\sigma\alpha \equiv \alpha^q \bmod \mathfrak P$), unique at unramified
primes (`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`).

* **Proposition 8.13** (`prop_8_13a`, `prop_8_13b`, proved).
* **8.14** (`item_8_14_stabilizer`, `item_8_14_frob`, `item_8_14_conjClass`, `item_8_14_abelian`), **8.15**
  (`item_8_15`), **8.16** (`item_8_16`), **8.17** (`item_8_17_injective`, `item_8_17`), all proved; the sentence after
  8.17 is `splitPrimes_sup` (`Ch8Applications.lean`).
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped Pointwise

namespace NumberFieldKB.MilneANT

noncomputable section

/-! ## Proposition 8.13 -/

section Prop813

variable (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
variable (L : IntermediateField K M) (P : Ideal (𝓞 M))

/-- **Proposition 8.13(a)** (proved): the decomposition group $H(\mathfrak P)$ of $\mathfrak P$ over $L$ is
$G(\mathfrak P) \cap H$, where $H = \mathrm{Gal}(M/L)$ is identified with the subgroup of $G = \mathrm{Gal}(M/K)$ fixing
$L$ (`IntermediateField.fixingSubgroup`) by restriction of scalars. -/
@[kb "milne2020ant" "v3.08, Prop. 8.13(a), p. 141"]
theorem prop_8_13a :
    (MulAction.stabilizer (M ≃ₐ[L] M) P).map (AlgEquiv.restrictScalarsHom K) =
      MulAction.stabilizer Gal(M/K) P ⊓ L.fixingSubgroup := by
  ext g
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, Subgroup.mem_inf,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hh, fun x hx => h.commutes ⟨x, hx⟩⟩
  · rintro ⟨hg, hfix⟩
    refine ⟨{ g with commutes' := fun x => hfix x x.2 }, hg, rfl⟩

/-- Restriction to $L$ intertwines the action on ideals: $\bar g\cdot(I\cap\mathcal O_L)=(gI)\cap\mathcal O_L$. -/
theorem smul_under_restrictNormalHom [IsGalois K L] (g : Gal(M/K)) (I : Ideal (𝓞 M)) :
    (AlgEquiv.restrictNormalHom L g) • I.under (𝓞 L) = (g • I).under (𝓞 L) := by
  have key : ∀ (g : Gal(M/K)) (b : 𝓞 L), algebraMap (𝓞 L) (𝓞 M) (AlgEquiv.restrictNormalHom L g • b)
      = g • algebraMap (𝓞 L) (𝓞 M) b := by
    intro g b
    apply Subtype.ext
    change algebraMap L M ((AlgEquiv.restrictNormalHom L g) (b : L)) = g (algebraMap L M (b : L))
    exact AlgEquiv.restrictNormal_commutes g L (b : L)
  ext x
  simp only [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  rw [← map_inv, ← key]

/-- **Proposition 8.13(b)** (proved): if $H$ is normal in $G$ (i.e. $L/K$ is Galois), the decomposition group of
$\mathfrak P_L = \mathfrak P \cap L$ over $K$ is the image of $G(\mathfrak P)$ in $G/H = \mathrm{Gal}(L/K)$. -/
@[kb "milne2020ant" "v3.08, Prop. 8.13(b), p. 141"]
theorem prop_8_13b [IsGalois K L] [P.IsPrime] :
    MulAction.stabilizer Gal(L/K) (P.under (𝓞 L)) =
      (MulAction.stabilizer Gal(M/K) P).map (AlgEquiv.restrictNormalHom L) := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_map]
  constructor
  · intro hσ
    obtain ⟨g₀, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := M)) σ
    have h1 : (g₀ • P).under (𝓞 L) = P.under (𝓞 L) := by
      rw [← smul_under_restrictNormalHom K M L, hσ]
    have hover : (g₀ • P).LiesOver (P.under (𝓞 L)) := ⟨h1.symm⟩
    have hover2 : P.LiesOver (P.under (𝓞 L)) := ⟨rfl⟩
    obtain ⟨h, hh⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.under (𝓞 L)) (g₀ • P) P (M ≃ₐ[L] M)
    refine ⟨AlgEquiv.restrictScalars K h * g₀, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul]
      exact hh
    · rw [map_mul]
      have : AlgEquiv.restrictNormalHom L (AlgEquiv.restrictScalars K h) = 1 := by
        ext x
        have := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K h) L x
        change algebraMap L M _ = algebraMap L M x
        exact this.trans (AlgEquiv.commutes h x)
      rw [this, one_mul]
  · rintro ⟨g, hg, rfl⟩
    rw [smul_under_restrictNormalHom, hg]

end Prop813

/-! ## The Frobenius element: 8.14 to 8.17 -/

section Frobenius

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

-- Prose definition (p. 141): the Frobenius element (P, L/K) at an unramified prime: Mathlib's predicate
-- `IsArithFrobAt` and the element `arithFrobAt` (unique at unramified primes by
-- `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`; in G(P) by `IsArithFrobAt.mem_stabilizer`).
attribute [kb "milne2020ant" "v3.08, Ch. 8, the Frobenius element (P, L/K), p. 141"] IsArithFrobAt arithFrobAt
-- Prose definition (p. 142): the Frobenius class (p, L/K) of a prime of K, the conjugacy class of the Frobenius
-- elements of the primes above it (`item_8_14_conjClass`).
attribute [kb "milne2020ant" "v3.08, Ch. 8, the Frobenius class (p, L/K), p. 142"]
  NumberFieldKB.Chebotarev.frobClass

/-- **8.14, first part** (proved): $G(\tau\mathfrak P) = \tau G(\mathfrak P)\tau^{-1}$. -/
@[kb "milne2020ant" "v3.08, 8.14, p. 141"]
theorem item_8_14_stabilizer (P : Ideal (𝓞 L)) (τ : Gal(L/K)) :
    MulAction.stabilizer Gal(L/K) (τ • P) = (MulAction.stabilizer Gal(L/K) P).map (MulAut.conj τ).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj τ P

/-- **8.14, second part** (proved): if $\sigma = (\mathfrak P, L/K)$ then $\tau\sigma\tau^{-1} = (\tau\mathfrak P, L/K)$
(Mathlib's `IsArithFrobAt.conj`). -/
@[kb "milne2020ant" "v3.08, 8.14, p. 141"]
theorem item_8_14_frob (P : Ideal (𝓞 L)) (σ τ : Gal(L/K)) (h : IsArithFrobAt (𝓞 K) σ P) :
    IsArithFrobAt (𝓞 K) (τ * σ * τ⁻¹) (τ • P) :=
  h.conj τ

/-- **8.14, consequence** (Milne p. 142, proved): for $\mathfrak p$ unramified in $L$, the Frobenius elements
$(\mathfrak P, L/K)$ of the primes $\mathfrak P \mid \mathfrak p$ form exactly one conjugacy class of $G$, the class
$(\mathfrak p, L/K)$ (`NumberFieldKB.Chebotarev.frobClass`). -/
@[kb "milne2020ant" "v3.08, 8.14 (consequence), p. 142"]
theorem item_8_14_conjClass (𝔭 : HeightOneSpectrum (𝓞 K))
    (h𝔭 : 𝔭 ∈ NumberFieldKB.Chebotarev.unramifiedPrimes K L) :
    Set.range (NumberFieldKB.Chebotarev.frobAt K L 𝔭) = (NumberFieldKB.Chebotarev.frobClass K L 𝔭).carrier := by
  ext g
  rw [ConjClasses.mem_carrier_iff_mk_eq]
  constructor
  · rintro ⟨Q, rfl⟩
    exact (NumberFieldKB.Chebotarev.frobClass_eq_mk_frobAt K L 𝔭 Q).symm
  · intro hg
    set Q₀ : 𝔭.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
    rw [NumberFieldKB.Chebotarev.frobClass_eq_mk_frobAt K L 𝔭 Q₀, ConjClasses.mk_eq_mk_iff_isConj,
      isConj_iff] at hg
    obtain ⟨c, hc⟩ := hg
    have h := (NumberFieldKB.Chebotarev.isArithFrobAt_frobAt K L 𝔭 Q₀).conj c⁻¹
    have := Q₀.2.1
    have := Q₀.2.2
    have hl : (c⁻¹ • Q₀.1).LiesOver 𝔭.asIdeal := by
      refine ⟨?_⟩
      ext x
      have hx : x ∈ 𝔭.asIdeal ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ Q₀.1 := by
        conv_lhs => rw [Q₀.2.2.over]
        rfl
      rw [hx]
      simp [Ideal.under]
    refine ⟨⟨c⁻¹ • Q₀.1, inferInstance, hl⟩, ?_⟩
    apply NumberFieldKB.Chebotarev.frobAt_eq_of_isArithFrobAt K L h𝔭
    rw [← hc] at h
    simpa [mul_assoc] using h

/-- **8.14, consequence** (Milne p. 142, proved): if $\mathrm{Gal}(L/K)$ is abelian, $(\mathfrak P, L/K)$ does not
depend on the prime $\mathfrak P \mid \mathfrak p$ (for $\mathfrak p$ unramified). -/
@[kb "milne2020ant" "v3.08, 8.14 (consequence), p. 142"]
theorem item_8_14_abelian (hab : ∀ σ τ : Gal(L/K), σ * τ = τ * σ) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h𝔭 : 𝔭 ∈ NumberFieldKB.Chebotarev.unramifiedPrimes K L) (Q Q' : 𝔭.asIdeal.primesOver (𝓞 L)) :
    NumberFieldKB.Chebotarev.frobAt K L 𝔭 Q = NumberFieldKB.Chebotarev.frobAt K L 𝔭 Q' := by
  have := Q.2.1
  have := Q.2.2
  have := Q'.2.1
  have := Q'.2.2
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal Q.1 Q'.1 Gal(L/K)
  have h := (NumberFieldKB.Chebotarev.isArithFrobAt_frobAt K L 𝔭 Q).conj σ
  rw [hσ] at h
  rw [NumberFieldKB.Chebotarev.frobAt_eq_of_isArithFrobAt K L h𝔭 Q' h, hab σ, mul_inv_cancel_right]

/-- Arithmetic Frobenius elements in a Galois group are unique at a maximal ideal unramified over the base. -/
theorem isArithFrobAt_unique {F : Type} [Field F] [NumberField F] {M : Type} [Field M] [NumberField M]
    [Algebra F M] [IsGalois F M] (Q : Ideal (𝓞 M)) [Q.IsMaximal] [Algebra.IsUnramifiedAt (𝓞 F) Q]
    {a b : Gal(M/F)} (ha : IsArithFrobAt (𝓞 F) a Q) (hb : IsArithFrobAt (𝓞 F) b Q) : a = b := by
  have h := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt ha hb (Ideal.primeCompl_le_nonZeroDivisors Q)
  have : FaithfulSMul Gal(M/F) (𝓞 M) := IsGaloisGroup.faithful (A := 𝓞 F)
  exact FaithfulSMul.eq_of_smul_eq_smul (α := 𝓞 M) fun x => DFunLike.congr_fun h x

/-- **8.15** (proved): in a tower $K \subseteq L \subseteq M$ with $M/K$ Galois and $\mathfrak Q$ a prime of $M$
unramified over $\mathfrak p = \mathfrak Q\cap K$, with $\mathfrak P = \mathfrak Q \cap L$:
$(\mathfrak Q, M/K)^{f(\mathfrak P/\mathfrak p)} = (\mathfrak Q, M/L)$, the latter viewed in $\mathrm{Gal}(M/K)$. -/
@[kb "milne2020ant" "v3.08, 8.15, p. 142"]
theorem item_8_15 (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] (E : IntermediateField K M)
    (Q : Ideal (𝓞 M)) [Q.IsMaximal] [Algebra.IsUnramifiedAt (𝓞 K) Q]
    (σ : Gal(M/K)) (hσ : IsArithFrobAt (𝓞 K) σ Q) (τ : M ≃ₐ[E] M) (hτ : IsArithFrobAt (𝓞 E) τ Q) :
    σ ^ (Q.under (𝓞 E)).inertiaDeg (𝓞 K) = AlgEquiv.restrictScalars K τ := by
  have hne : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField M)
  have : Finite (𝓞 M ⧸ Q) := NumberFieldKB.Chebotarev.finite_quotient_of_ne_bot Q hne
  have : Algebra.IsUnramifiedAt (𝓞 E) Q := Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 K) Q
  have h1 : τ = arithFrobAt (𝓞 E) Gal(M/E) Q :=
    isArithFrobAt_unique Q hτ (IsArithFrobAt.arithFrobAt (𝓞 E) Gal(M/E) Q)
  have h2 : σ = arithFrobAt (𝓞 K) Gal(M/K) Q :=
    isArithFrobAt_unique Q hσ (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(M/K) Q)
  rw [h1, h2]
  exact (NumberFieldKB.Chebotarev.restrictScalars_arithFrobAt_eq_pow Q E).symm

/-- **8.16** (proved): in 8.15, if $L/K$ is Galois then $(\mathfrak Q, M/K)|_L = (\mathfrak P, L/K)$. -/
@[kb "milne2020ant" "v3.08, 8.16, p. 142"]
theorem item_8_16 (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] (E : IntermediateField K M)
    [IsGalois K E] (Q : Ideal (𝓞 M)) [Q.IsMaximal] (σ : Gal(M/K)) (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom E σ) (Q.under (𝓞 E)) := by
  intro x
  have key : algebraMap (𝓞 E) (𝓞 M) (AlgEquiv.restrictNormalHom E σ • x)
      = σ • algebraMap (𝓞 E) (𝓞 M) x := by
    apply Subtype.ext
    change algebraMap E M ((AlgEquiv.restrictNormalHom E σ) (x : E)) = σ (algebraMap E M (x : E))
    exact AlgEquiv.restrictNormal_commutes σ E (x : E)
  rw [Ideal.under_under (A := 𝓞 K) (B := 𝓞 E)]
  have : algebraMap (𝓞 E) (𝓞 M) (AlgEquiv.restrictNormalHom E σ • x -
      x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) ∈ Q := by
    rw [map_sub, map_pow, key]
    exact hσ _
  exact this

/-- If two automorphisms have the same restriction to a Galois subfield $L_1$, then $\sigma^{-1}\tau$ fixes $L_1$ pointwise. -/
theorem mem_fixingSubgroup_of_restrictNormalHom_eq (M : Type) [Field M] [Algebra K M]
    (L₁ : IntermediateField K M) [IsGalois K M] [IsGalois K L₁] {σ τ : Gal(M/K)}
    (h : AlgEquiv.restrictNormalHom L₁ σ = AlgEquiv.restrictNormalHom L₁ τ) :
    σ⁻¹ * τ ∈ L₁.fixingSubgroup := by
  have h' : AlgEquiv.restrictNormalHom L₁ (σ⁻¹ * τ) = 1 := by
    rw [map_mul, map_inv, h]; exact inv_mul_cancel _
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have := AlgEquiv.restrictNormal_commutes (σ⁻¹ * τ) L₁ ⟨x, hx⟩
  have h'' : (σ⁻¹ * τ).restrictNormal L₁ = 1 := h'
  rw [h''] at this
  exact this.symm

/-- **8.17, the canonical map** (proved): for Galois extensions $L_1, L_2$ of $K$ with compositum $M = L_1L_2$ (here
$L_1, L_2$ are subfields of $M$ with $L_1 \sqcup L_2 = M$), $\sigma \mapsto (\sigma|_{L_1}, \sigma|_{L_2})$,
$\mathrm{Gal}(M/K)\to\mathrm{Gal}(L_1/K)\times\mathrm{Gal}(L_2/K)$, is injective. -/
@[kb "milne2020ant" "v3.08, 8.17 (the injective map before it), p. 142"]
theorem item_8_17_injective (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (L₁ L₂ : IntermediateField K M) [IsGalois K L₁] [IsGalois K L₂] (hM : L₁ ⊔ L₂ = ⊤) :
    Function.Injective (fun σ : Gal(M/K) =>
      (AlgEquiv.restrictNormalHom L₁ σ, AlgEquiv.restrictNormalHom L₂ σ)) := by
  intro σ τ h
  simp only [Prod.mk.injEq] at h
  have hmem : σ⁻¹ * τ ∈ (L₁ ⊔ L₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    exact ⟨mem_fixingSubgroup_of_restrictNormalHom_eq K M L₁ h.1,
      mem_fixingSubgroup_of_restrictNormalHom_eq K M L₂ h.2⟩
  rw [hM, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

/-- **8.17** (proved): under the map of `item_8_17_injective`, $(\mathfrak Q, M/K)\mapsto
((\mathfrak P_1, L_1/K), (\mathfrak P_2, L_2/K))$ with $\mathfrak P_i = \mathfrak Q \cap L_i$. -/
@[kb "milne2020ant" "v3.08, 8.17, p. 142"]
theorem item_8_17 (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (L₁ L₂ : IntermediateField K M) [IsGalois K L₁] [IsGalois K L₂]
    (Q : Ideal (𝓞 M)) [Q.IsMaximal] (σ : Gal(M/K)) (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom L₁ σ) (Q.under (𝓞 L₁)) ∧
      IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom L₂ σ) (Q.under (𝓞 L₂)) :=
  ⟨item_8_16 K M L₁ Q σ hσ, item_8_16 K M L₂ Q σ hσ⟩

end Frobenius

end

end NumberFieldKB.MilneANT
