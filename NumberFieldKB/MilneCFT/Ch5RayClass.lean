import NumberFieldKB.MilneCFT.Intro.Theorems
import NumberFieldKB.MilneCFT.Intro.Complements
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Ray class groups (Milne, *Class Field Theory*, Chapter V, §1)

Source: J. S. Milne, *Class Field Theory*, v4.03 (2020), bib key `milne2020cft`. Locators give Milne's printed page
numbers (printed page = pdf page − 9 in Chapter V).

The moduli, the group $I^{S(\mathfrak m)}$, the congruence subgroup $K_{\mathfrak m,1}$ and the ray class group
$C_\mathfrak m$ are those of the Introduction (`Modulus`, `coprimeIdeals`, `congruenceSubgroup`, `RayClassGroup`,
file `Intro/RayClass.lean`). This file adds, for a set $S$ of finite primes:

* `sIdeals S` $= I^S$ (fractional ideals prime to $S$) and `primeToS S` $= K^S$ (elements of $K^\times$ of order $0$ at
  every prime of $S$), with `coprimeIdeals_eq_sIdeals`;
* **Lemma 1.1** (`lemma_1_1`), **Remark 1.2** (`remark_1_2`), **Lemma 1.5** (`lemma_1_5`), **Proposition 1.6**
  (`prop_1_6_integral`, `prop_1_6_eq_iff`); Theorem 1.7 and Example 1.8 are in `Ch5RayClassOrder.lean`;
* the comparison of the Introduction's `Modulus` with Milne's function-valued Definition 1.3 (`modulus_dvd_iff`).

Conventions. A modulus $\mathfrak m = \mathfrak m_0\mathfrak m_\infty$ is a nonzero ideal $\mathfrak m_0$ of
$\mathcal O_K$ and a set $\mathfrak m_\infty$ of real places; Milne's function $\mathfrak m(\mathfrak p)$ is
`Modulus.ord` at finite primes and the indicator of $\mathfrak m_\infty$ at real ones. Signs ($\{\pm\}$) are `ℤˣ`.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## Helper lemmas: multiplicities and the Chinese remainder theorem -/

/-- For nonzero ideals, divisibility is comparison of multiplicities at every prime. -/
theorem ideal_dvd_iff_count {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I ∣ J ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      (Associates.mk v.asIdeal).count (Associates.mk I).factors ≤
        (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
  rw [← Associates.mk_le_mk_iff_dvd, ← Associates.factors_le, Associates.factors_mk _ hI,
    Associates.factors_mk _ hJ, WithTop.coe_le_coe, Multiset.le_iff_count]
  constructor
  · intro h v
    rw [Associates.count_some v.associates_irreducible,
      Associates.count_some v.associates_irreducible]
    exact h ⟨_, v.associates_irreducible⟩
  · rintro h ⟨q, hq⟩
    obtain ⟨q, rfl⟩ := Associates.mk_surjective q
    have hq' := hq
    rw [Associates.irreducible_mk, irreducible_iff_prime] at hq'
    have := h ⟨q, Ideal.isPrime_of_prime hq', hq'.ne_zero⟩
    rw [Associates.count_some hq, Associates.count_some hq] at this
    exact this

/-- The multiplicity of a prime `v` in an ideal, as a natural number. -/
abbrev idealCount (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk J).factors

/-- Multiplicities are additive on nonzero ideals. -/
theorem idealCount_mul (v : HeightOneSpectrum (𝓞 K)) {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealCount v (I * J) = idealCount v I + idealCount v J := by
  unfold idealCount
  have hI' : Associates.mk I ≠ 0 := Associates.mk_ne_zero.2 hI
  have hJ' : Associates.mk J ≠ 0 := Associates.mk_ne_zero.2 hJ
  rw [← Associates.mk_mul_mk]
  exact Associates.count_mul hI' hJ' v.associates_irreducible

theorem intValuation_le_iff_count {v : HeightOneSpectrum (𝓞 K)} {y : 𝓞 K} (hy : y ≠ 0) (n : ℕ) :
    v.intValuation y ≤ WithZero.exp (-(n : ℤ)) ↔ n ≤ idealCount v (Ideal.span {y}) := by
  rw [v.intValuation_if_neg hy, WithZero.exp_le_exp, neg_le_neg_iff, Int.ofNat_le]

/-- An integer whose `v`-adic valuation is at most `exp (-(multiplicity of v in 𝔟))` at every prime lies
in the ideal `𝔟`. -/
theorem mem_of_intValuation_le {𝔟 : Ideal (𝓞 K)} (h𝔟 : 𝔟 ≠ ⊥) {y : 𝓞 K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      v.intValuation y ≤ WithZero.exp (-(idealCount v 𝔟 : ℤ))) : y ∈ 𝔟 := by
  by_cases hy : y = 0
  · rw [hy]; exact zero_mem _
  have hspan : Ideal.span {y} ≠ ⊥ := by simpa using hy
  have : 𝔟 ∣ Ideal.span {y} := by
    rw [ideal_dvd_iff_count h𝔟 hspan]
    intro v
    exact (intValuation_le_iff_count hy _).1 (h v)
  exact (Ideal.span_singleton_le_iff_mem _).1 (Ideal.le_of_dvd this)

/-- Chinese remainder step: for a finite set `S` of primes and a nonzero ideal `𝔟` there is a nonzero
`b ∈ 𝔟` with the same multiplicity as `𝔟` at every prime of `S`. -/
theorem exists_mem_count_eq (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) {𝔟 : Ideal (𝓞 K)}
    (h𝔟 : 𝔟 ≠ ⊥) :
    ∃ b ∈ 𝔟, b ≠ 0 ∧ ∀ v ∈ S, idealCount v (Ideal.span {b}) = idealCount v 𝔟 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨v0, hv0⟩
  · obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔟
    exact ⟨b, hb, hb0, by simp⟩
  choose π hπ using fun v : HeightOneSpectrum (𝓞 K) => v.intValuation_exists_uniformizer
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := hS.toFinset ∪ (Ideal.finite_factors h𝔟).toFinset) (fun v => v.asIdeal)
    (fun v => idealCount v 𝔟 + 1)
    (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => if v.1 ∈ S then π v.1 ^ idealCount v.1 𝔟 else 0)
  have hval : ∀ v ∈ S, v.intValuation y = WithZero.exp (-(idealCount v 𝔟 : ℤ)) := by
    intro v hv
    have h1 := hy v (by simp [hv])
    simp only [hv, ↓reduceIte] at h1
    have h2 : v.intValuation (π v ^ idealCount v 𝔟) = WithZero.exp (-(idealCount v 𝔟 : ℤ)) := by
      rw [map_pow, hπ v, ← WithZero.exp_nsmul]
      congr 1
      simp
    have h3 : v.intValuation (y - π v ^ idealCount v 𝔟) < v.intValuation (π v ^ idealCount v 𝔟) := by
      rw [h2]
      refine lt_of_le_of_lt ((v.intValuation_le_pow_iff_mem _ _).2 h1) ?_
      rw [WithZero.exp_lt_exp]
      omega
    have := Valuation.map_add_eq_of_lt_left v.intValuation h3
    rw [add_sub_cancel] at this
    rw [this, h2]
  have hne : y ≠ 0 := by
    intro h0
    have := hval v0 hv0
    rw [h0, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hle : ∀ v : HeightOneSpectrum (𝓞 K),
      v.intValuation y ≤ WithZero.exp (-(idealCount v 𝔟 : ℤ)) := by
    intro v
    by_cases hv : v ∈ S
    · exact (hval v hv).le
    by_cases hd : v.asIdeal ∣ 𝔟
    · have h1 := hy v (by simp [hd])
      simp only [hv, ↓reduceIte, sub_zero] at h1
      refine ((v.intValuation_le_pow_iff_mem _ _).2 h1).trans ?_
      rw [WithZero.exp_le_exp]
      omega
    · have : idealCount v 𝔟 = 0 := by
        by_contra hc
        exact hd ((Associates.count_ne_zero_iff_dvd h𝔟 v.irreducible).1 hc)
      rw [this]
      simpa using v.intValuation_le_one y
  refine ⟨y, ?_, hne, fun v hv => ?_⟩
  · exact mem_of_intValuation_le h𝔟 hle
  · have := hval v hv
    rw [v.intValuation_if_neg hne, WithZero.exp_inj] at this
    exact_mod_cast neg_inj.1 this

/-- For a finite set `S` of primes and a nonzero ideal `𝔟` there is a nonzero `b` with
`(b) = 𝔟 𝔠` for a nonzero ideal `𝔠` prime to `S`. -/
theorem exists_principal_mul_coprime (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    {𝔟 : Ideal (𝓞 K)} (h𝔟 : 𝔟 ≠ ⊥) :
    ∃ (b : 𝓞 K) (𝔠 : Ideal (𝓞 K)), b ≠ 0 ∧ 𝔠 ≠ ⊥ ∧ Ideal.span {b} = 𝔟 * 𝔠 ∧
      ∀ v ∈ S, ¬ v.asIdeal ∣ 𝔠 := by
  obtain ⟨b, hb, hb0, hcount⟩ := exists_mem_count_eq S hS h𝔟
  have hspan : Ideal.span {b} ≠ ⊥ := by simpa using hb0
  obtain ⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb)
  have h𝔠0 : 𝔠 ≠ ⊥ := by
    rintro rfl
    exact hspan (by simpa using h𝔠)
  refine ⟨b, 𝔠, hb0, h𝔠0, h𝔠, fun v hv hd => ?_⟩
  have h1 := hcount v hv
  rw [h𝔠, idealCount_mul v h𝔟 h𝔠0] at h1
  have h2 : idealCount v 𝔠 = 0 := by omega
  exact (Associates.count_ne_zero_iff_dvd h𝔠0 v.irreducible).2 hd h2

/-! ## Ideals and elements prime to a set of primes (p. 147) -/

/-- $I^S$ (Milne, *CFT*, V, §1, p. 147): the fractional ideals of $K$ with exponent $0$ at every prime of $S$; Milne
defines it as the subgroup generated by the primes not in $S$ (`sIdeals_eq_closure`). -/
@[kb "milne2020cft" "Ch. V, §1, p. 147 (the group I^S)"]
def sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v ∈ S, FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  mul_mem' := by
    intro I J hI hJ v hv
    simp only [Units.val_mul]
    rw [FractionalIdeal.count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv]
    rfl
  one_mem' := by
    intro v _
    simp [FractionalIdeal.count_one]
  inv_mem' := by
    intro I hI v hv
    have : ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        ((I : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv₀ I.ne_zero]; exact I.inv_mul
    show FractionalIdeal.count K v ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 0
    rw [this, FractionalIdeal.count_inv, hI v hv]; rfl

/-- A nonzero prime $\mathfrak p$ of $\mathcal O_K$ as a fractional ideal unit. -/
def primeUnitIdeal (v : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

/-- Milne's definition of $I^S$ (p. 147): the subgroup generated by the primes not in $S$. -/
@[kb "milne2020cft" "Ch. V, §1, p. 147 (I^S is generated by the primes not in S)"]
theorem sIdeals_eq_closure (S : Set (HeightOneSpectrum (𝓞 K))) :
    sIdeals S = Subgroup.closure (primeUnitIdeal '' Sᶜ) := by
  classical
  apply le_antisymm
  · intro I hI
    have hfin : {v : HeightOneSpectrum (𝓞 K) |
        FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0}.Finite :=
      Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := K) (I : FractionalIdeal (𝓞 K)⁰ K))
    have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) I.ne_zero
    have hI' : I = ∏ v ∈ hfin.toFinset, (primeUnitIdeal v) ^
        (FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) := by
      apply Units.ext
      rw [Units.coe_prod]
      conv_lhs => rw [← hfac]
      rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset)]
      · refine Finset.prod_congr rfl fun v _ => ?_
        rw [Units.val_zpow_eq_zpow_val]
        rfl
      · intro v hv
        rw [Function.mem_mulSupport] at hv
        simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
        intro h0
        exact hv (by rw [h0, zpow_zero])
    rw [hI']
    refine Subgroup.prod_mem _ fun v hv => ?_
    have hvS : v ∈ Sᶜ := fun hvS => (Set.Finite.mem_toFinset hfin).1 hv (hI v hvS)
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_image_of_mem _ hvS)) _
  · rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩ v hv
    have hwv : w ≠ v := by rintro rfl; exact hw hv
    exact FractionalIdeal.count_maximal_coprime K v hwv

/-- The finite primes dividing $\mathfrak m$: $S(\mathfrak m)$ without the real primes. -/
def Modulus.finiteSupport (m : Modulus K) : Set (HeightOneSpectrum (𝓞 K)) := {v | v.asIdeal ∣ m.finite}

/-- $I^{S(\mathfrak m)}$ of the Introduction is $I^S$ for $S$ the finite primes dividing $\mathfrak m$. -/
theorem coprimeIdeals_eq_sIdeals (m : Modulus K) : coprimeIdeals m = sIdeals m.finiteSupport :=
  rfl

/-- $K^S$ (Milne, *CFT*, V, §1, p. 147): the $a \in K^\times$ with $(a) \in I^S$, i.e. $\mathrm{ord}_\mathfrak p(a) = 0$
for every $\mathfrak p \in S$ (`mem_primeToS_iff`). (Not the group of $S$-units.) -/
@[kb "milne2020cft" "Ch. V, §1, p. 147 (the group K^S)"]
def primeToS (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ :=
  (sIdeals S).comap (toPrincipalIdeal (𝓞 K) K)

theorem mem_primeToS_iff (S : Set (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    a ∈ primeToS S ↔ ∀ v ∈ S, v.valuation K (a : K) = 1 := by
  refine forall₂_congr fun v _ => ?_
  rw [valuation_eq_exp_neg_count, ← WithZero.exp_zero, WithZero.exp_inj, neg_eq_zero]

/-- $i : K^S \to I^S$, $a \mapsto (a)$ (p. 147). -/
def sPrincipal (S : Set (HeightOneSpectrum (𝓞 K))) : primeToS S →* sIdeals S :=
  (toPrincipalIdeal (𝓞 K) K).subgroupComap (sIdeals S)

/-- The units $U_K = \mathcal O_K^\times$ as a subgroup of $K^\times$. -/
def unitsK (K : Type) [Field K] [NumberField K] : Subgroup Kˣ :=
  (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).range

/-- The principal fractional ideal $(a)$ is trivial exactly when $a$ is a unit of $\mathcal O_K$. -/
theorem toPrincipalIdeal_eq_one_iff (a : Kˣ) :
    toPrincipalIdeal (𝓞 K) K a = 1 ↔ a ∈ unitsK K := by
  constructor
  · intro h
    have hmem : ∀ b : Kˣ, toPrincipalIdeal (𝓞 K) K b = 1 → ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = b := by
      intro b hb
      have : (b : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
        have h1 : (toPrincipalIdeal (𝓞 K) K b : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
          rw [hb]; rfl
        rw [← h1, coe_toPrincipalIdeal]
        exact FractionalIdeal.mem_spanSingleton_self _ _
      exact (FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 this
    obtain ⟨r, hr⟩ := hmem a h
    obtain ⟨s, hs⟩ := hmem a⁻¹ (by rw [map_inv, h, inv_one])
    have hrs : r * s = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, hr, hs, map_one]
      simp
    have hsr : s * r = 1 := by rw [mul_comm]; exact hrs
    refine ⟨⟨r, s, hrs, hsr⟩, ?_⟩
    apply Units.ext
    simpa using hr
  · rintro ⟨u, rfl⟩
    apply Units.ext
    rw [coe_toPrincipalIdeal, Units.val_one]
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    rw [← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.2 u.isUnit,
      FractionalIdeal.coeIdeal_top]

theorem unitsK_le_primeToS (S : Set (HeightOneSpectrum (𝓞 K))) : unitsK K ≤ primeToS S := by
  intro a ha
  show toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S
  rw [(toPrincipalIdeal_eq_one_iff a).2 ha]
  exact (sIdeals S).one_mem

/-- The map $I^S \to C$ to the ideal class group. -/
def sClassMap (S : Set (HeightOneSpectrum (𝓞 K))) : sIdeals S →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (sIdeals S).subtype

/-- Every ideal class contains a nonzero integral ideal prime to a given finite set of primes. -/
theorem exists_integral_rep_coprime (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (c : ClassGroup (𝓞 K)) :
    ∃ (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ∈ (Ideal (𝓞 K))⁰), (∀ v ∈ S, ¬ v.asIdeal ∣ 𝔞) ∧
      ClassGroup.mk0 ⟨𝔞, h𝔞⟩ = c := by
  obtain ⟨⟨𝔟, h𝔟⟩, hc⟩ := ClassGroup.mk0_surjective c⁻¹
  have h𝔟0 : 𝔟 ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.1 h𝔟
  obtain ⟨b, 𝔠, hb, h𝔠, hbc, hcop⟩ := exists_principal_mul_coprime S hS h𝔟0
  have h𝔠' : 𝔠 ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔠
  refine ⟨𝔠, h𝔠', hcop, ?_⟩
  have h1 : ClassGroup.mk0 ⟨𝔟, h𝔟⟩ * ClassGroup.mk0 ⟨𝔠, h𝔠'⟩ = 1 := by
    rw [← map_mul, ← map_one (ClassGroup.mk0 (R := 𝓞 K)), ClassGroup.mk0_eq_mk0_iff]
    exact ⟨1, b, one_ne_zero, hb, by simp [hbc]⟩
  rw [eq_inv_of_mul_eq_one_right h1, hc, inv_inv]

/-- **Lemma 1.1** (Milne, *CFT*, V, p. 147): for a finite set $S$ of prime ideals the sequence
$0 \to U_K \to K^S \xrightarrow{i} I^S \to C \to 0$ is exact: $U_K \to K^S$ is injective (it is an inclusion of
subgroups of $K^\times$, `unitsK_le_primeToS`), the kernel of $i$ is $U_K$, the image of $i$ is the kernel of
$I^S \to C$, and $I^S \to C$ is onto. -/
@[kb "milne2020cft" "Ch. V, Lemma 1.1"]
theorem lemma_1_1 (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    (∀ a : primeToS S, sPrincipal S a = 1 ↔ (a : Kˣ) ∈ unitsK K) ∧
      (sClassMap S).ker = (sPrincipal S).range ∧ Function.Surjective (sClassMap S) := by
  refine ⟨fun a => ?_, ?_, ?_⟩
  · rw [Subtype.ext_iff]
    exact toPrincipalIdeal_eq_one_iff (a : Kˣ)
  · ext I
    constructor
    · intro hI
      have h1 : ClassGroup.mk K (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1 := hI
      rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at h1
      obtain ⟨g, hg⟩ := h1
      have hg0 : g ≠ 0 := by
        rintro rfl
        exact (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ).ne_zero (by rw [hg]; exact map_zero _)
      have hga : toPrincipalIdeal (𝓞 K) K (Units.mk0 g hg0) = (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
        apply Units.ext
        rw [coe_toPrincipalIdeal, hg]
        rfl
      have hmem : Units.mk0 g hg0 ∈ primeToS S := by
        show toPrincipalIdeal (𝓞 K) K (Units.mk0 g hg0) ∈ sIdeals S
        rw [hga]; exact I.2
      exact ⟨⟨Units.mk0 g hg0, hmem⟩, Subtype.ext hga⟩
    · rintro ⟨a, rfl⟩
      show ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K (a : Kˣ)) = 1
      rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
      exact (FractionalIdeal.isPrincipal_iff _).2 ⟨(a : Kˣ), rfl⟩
  · intro c
    obtain ⟨𝔞, h𝔞, hcop, hc⟩ := exists_integral_rep_coprime S hS c
    have h𝔞0 : 𝔞 ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.1 h𝔞
    refine ⟨⟨FractionalIdeal.mk0 K ⟨𝔞, h𝔞⟩, fun v hv => ?_⟩, ?_⟩
    · rw [FractionalIdeal.coe_mk0]
      show FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = 0
      rw [FractionalIdeal.count_coe K v h𝔞0]
      have : idealCount v 𝔞 = 0 := by
        by_contra hne
        exact hcop v hv ((Associates.count_ne_zero_iff_dvd h𝔞0 v.irreducible).1 hne)
      simp [this]
    · show ClassGroup.mk K (FractionalIdeal.mk0 K ⟨𝔞, h𝔞⟩) = c
      rw [ClassGroup.mk_mk0, hc]

/-- **Remark 1.2** (Milne, *CFT*, V, p. 147): for a finite set $S$ of primes, every ideal class is represented by an
integral ideal prime to $S$. -/
@[kb "milne2020cft" "Ch. V, Remark 1.2"]
theorem remark_1_2 (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (c : ClassGroup (𝓞 K)) :
    ∃ (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ∈ (Ideal (𝓞 K))⁰), (∀ v ∈ S, ¬ v.asIdeal ∣ 𝔞) ∧
      ClassGroup.mk0 ⟨𝔞, h𝔞⟩ = c :=
  exists_integral_rep_coprime S hS c

/-! ## Moduli (Definition 1.3, p. 148) -/

/-- **Definition 1.3** (Milne, *CFT*, V, p. 148) compared with the Introduction's `Modulus`: Milne's modulus is a
function $\mathfrak m$ on the primes, $\ge 0$, finitely supported, $\le 1$ at real primes and $0$ at complex ones; the
`Modulus` structure records $\mathfrak m_0 = \prod \mathfrak p^{\mathfrak m(\mathfrak p)}$ (so
$\mathfrak m(\mathfrak p) =$ `m.ord p`) and $\mathfrak m_\infty = \{v \text{ real} : \mathfrak m(v) = 1\}$. Milne's
divisibility, $\mathfrak m(\mathfrak p) \le \mathfrak n(\mathfrak p)$ for all $\mathfrak p$, is `Modulus.Dvd`. -/
@[kb "milne2020cft" "Ch. V, Definition 1.3"]
theorem modulus_dvd_iff (m n : Modulus K) :
    m.Dvd n ↔ (∀ v : HeightOneSpectrum (𝓞 K), m.ord v ≤ n.ord v) ∧ m.infinite ⊆ n.infinite := by
  unfold Modulus.Dvd
  rw [ideal_dvd_iff_count m.finite_ne_bot n.finite_ne_bot]
  rfl

/-- In Definition 1.3, a prime divides $\mathfrak m$ iff $\mathfrak m(\mathfrak p) > 0$. -/
@[kb "milne2020cft" "Ch. V, §1, p. 148 (p divides m iff m(p) > 0)"]
theorem modulus_mem_finiteSupport_iff (m : Modulus K) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ m.finiteSupport ↔ 0 < m.ord v := by
  rw [Nat.pos_iff_ne_zero]
  exact (Associates.count_ne_zero_iff_dvd m.finite_ne_bot v.irreducible).symm

/-- The ideal $\mathfrak m_0$ is the set of integers with $\mathfrak p$-adic valuation at most
$\exp(-\mathfrak m(\mathfrak p))$ at every prime $\mathfrak p$. -/
theorem mem_finite_iff_intValuation (m : Modulus K) (y : 𝓞 K) :
    y ∈ m.finite ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      v.intValuation y ≤ WithZero.exp (-(m.ord v : ℤ)) := by
  constructor
  · intro hy v
    by_cases hy0 : y = 0
    · rw [hy0, map_zero]; exact zero_le
    have hspan : Ideal.span {y} ≠ ⊥ := by simpa using hy0
    refine (intValuation_le_iff_count hy0 _).2 ?_
    have : m.finite ∣ Ideal.span {y} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hy)
    exact (ideal_dvd_iff_count m.finite_ne_bot hspan).1 this v
  · exact fun h => mem_of_intValuation_le m.finite_ne_bot h

/-- An ideal prime to every prime dividing $\mathfrak m_0$ is coprime to $\mathfrak m_0$. -/
theorem sup_eq_top_of_forall_not_dvd (m : Modulus K) {𝔞 : Ideal (𝓞 K)}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.finite → ¬ v.asIdeal ∣ 𝔞) :
    𝔞 ⊔ m.finite = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hMbot : M ≠ ⊥ := by
    rintro rfl
    exact m.finite_ne_bot (le_bot_iff.1 (le_sup_right.trans hle))
  let v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hMbot⟩
  exact h v (Ideal.dvd_iff_le.2 (le_sup_right.trans hle))
    (Ideal.dvd_iff_le.2 (le_sup_left.trans hle))

/-- A nonzero integer outside every prime dividing $\mathfrak m_0$ has a nonzero inverse modulo
$\mathfrak m_0$. -/
theorem exists_mul_sub_one_mem (m : Modulus K) {y : 𝓞 K}
    (hy : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.finite → y ∉ v.asIdeal) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ c * y - 1 ∈ m.finite := by
  have h1 : Ideal.span {y} ⊔ m.finite = ⊤ :=
    sup_eq_top_of_forall_not_dvd m fun v hv hd => hy v hv (Ideal.dvd_span_singleton.1 hd)
  have h2 : (1 : 𝓞 K) ∈ Ideal.span {y} ⊔ m.finite := by rw [h1]; trivial
  obtain ⟨c, z, hz, hcz⟩ := Ideal.mem_span_singleton_sup.1 h2
  by_cases hc : c = 0
  · subst hc
    refine ⟨1, one_ne_zero, ?_⟩
    have hz1 : z = 1 := by simpa using hcz
    rw [hz1] at hz
    rw [(Ideal.eq_top_iff_one _).2 hz]
    trivial
  · refine ⟨c, hc, ?_⟩
    have : c * y - 1 = -z := by linear_combination hcz
    rw [this]
    exact neg_mem hz

/-- Two classes in the ray class group agree exactly when they differ by a principal ideal
$(\alpha)$ with $\alpha \equiv 1 \bmod^\times \mathfrak m$. -/
theorem quotient_mk_eq_iff (m : Modulus K) (A B : coprimeIdeals m) :
    (QuotientGroup.mk A : RayClassGroup m) = QuotientGroup.mk B ↔
      ∃ α ∈ congruenceSubgroup m, toPrincipalIdeal (𝓞 K) K α *
        (A : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = B := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨α, hα, h⟩
    refine ⟨α, hα, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq] at h
    rw [mul_comm]; exact h
  · rintro ⟨α, hα, h⟩
    refine ⟨α, hα, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq, mul_comm]
    exact h

/-! ## Lemma 1.5 and Proposition 1.6 (p. 149) -/

/-- **Lemma 1.5** (Milne, *CFT*, V, p. 149): for a finite set $S$ of prime ideals, every $\alpha \in K^S$ is a quotient
$a/b$ with $a, b \in \mathcal O_K \cap K^S$ (nonzero, not in any prime of $S$). -/
@[kb "milne2020cft" "Ch. V, Lemma 1.5"]
theorem lemma_1_5 (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (α : primeToS S) :
    ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ (∀ v ∈ S, a ∉ v.asIdeal ∧ b ∉ v.asIdeal) ∧
      ((α : Kˣ) : K) = algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b := by
  have hα : ∀ v ∈ S, v.valuation K ((α : Kˣ) : K) = 1 := (mem_primeToS_iff S (α : Kˣ)).1 α.2
  have hαne : ((α : Kˣ) : K) ≠ 0 := (α : Kˣ).ne_zero
  -- the ideal of denominators of `α`
  let 𝔡 : Ideal (𝓞 K) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) K ((α : Kˣ) : K))
    (LinearMap.range (Algebra.linearMap (𝓞 K) K))
  have hmem𝔡 : ∀ r : 𝓞 K, r ∈ 𝔡 ↔ ∃ n : 𝓞 K, algebraMap (𝓞 K) K n =
      ((α : Kˣ) : K) * algebraMap (𝓞 K) K r := by
    intro r
    simp only [𝔡, Submodule.mem_comap, LinearMap.mem_range, LinearMap.toSpanSingleton_apply,
      Algebra.linearMap_apply, Algebra.smul_def]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [hn, mul_comm]⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [hn, mul_comm]⟩
  have h𝔡0 : 𝔡 ≠ ⊥ := by
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (𝓞 K)⁰ ((α : Kˣ) : K)
    intro h
    simp only at hnd
    have hd : (d : 𝓞 K) ∈ 𝔡 := (hmem𝔡 _).2 ⟨n, by
      rw [← hnd]; exact (IsLocalization.mk'_spec K n d).symm⟩
    rw [h] at hd
    exact nonZeroDivisors.coe_ne_zero d (by simp at hd)
  have hcop : ∀ v ∈ S, idealCount v 𝔡 = 0 := by
    intro v hv
    by_contra hne
    have hdvd := (Associates.count_ne_zero_iff_dvd h𝔡0 v.irreducible).1 hne
    obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer ((α : Kˣ) : K) (hα v hv).le
    have hd : (d : 𝓞 K) ∈ 𝔡 := (hmem𝔡 _).2 ⟨n, hnd.symm⟩
    exact d.2 (Ideal.dvd_iff_le.1 hdvd hd)
  obtain ⟨b, hb𝔡, hb0, hbc⟩ := exists_mem_count_eq S hS h𝔡0
  have hbv : ∀ v ∈ S, b ∉ v.asIdeal := by
    intro v hv hbm
    have hspan : Ideal.span {b} ≠ ⊥ := by simpa using hb0
    have h1 : v.asIdeal ∣ Ideal.span {b} := Ideal.dvd_span_singleton.2 hbm
    have h2 : idealCount v (Ideal.span {b}) ≠ 0 :=
      (Associates.count_ne_zero_iff_dvd hspan v.irreducible).2 h1
    rw [hbc v hv, hcop v hv] at h2
    exact h2 rfl
  obtain ⟨a, ha⟩ := (hmem𝔡 b).1 hb𝔡
  have hb1 : ∀ v ∈ S, v.valuation K (algebraMap (𝓞 K) K b) = 1 := fun v hv =>
    (v.valuation_eq_one_iff_notMem (K := K)).2 (hbv v hv)
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
    simpa using hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact mul_ne_zero hαne hbK ha.symm
  refine ⟨a, b, ha0, hb0, fun v hv => ⟨?_, hbv v hv⟩, ?_⟩
  · rw [← v.valuation_eq_one_iff_notMem (K := K), ha, map_mul, hα v hv, hb1 v hv,
      mul_one]
  · rw [ha]; field_simp

/-- A nonzero integral ideal, viewed as a fractional ideal unit, lies in `I^S` if no prime of `S` divides it. -/
theorem mk0_mem_sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) {𝔞 : Ideal (𝓞 K)}
    (h𝔞 : 𝔞 ∈ (Ideal (𝓞 K))⁰) (hcop : ∀ v ∈ S, ¬ v.asIdeal ∣ 𝔞) :
    FractionalIdeal.mk0 K ⟨𝔞, h𝔞⟩ ∈ sIdeals S := by
  intro v hv
  have h𝔞0 : 𝔞 ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.1 h𝔞
  rw [FractionalIdeal.coe_mk0]
  show FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = 0
  rw [FractionalIdeal.count_coe K v h𝔞0]
  have : idealCount v 𝔞 = 0 := by
    by_contra hne
    exact hcop v hv ((Associates.count_ne_zero_iff_dvd h𝔞0 v.irreducible).1 hne)
  simp [this]

/-- Every element of `I^S` becomes integral after multiplication by a nonzero integer outside the primes of `S`. -/
theorem exists_mul_integral (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hI : I ∈ sIdeals S) :
    ∃ (b : 𝓞 K) (𝔞 : Ideal (𝓞 K)), b ≠ 0 ∧ (∀ v ∈ S, b ∉ v.asIdeal) ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b) *
        (I : FractionalIdeal (𝓞 K)⁰ K) = 𝔞 := by
  obtain ⟨𝔞₀, h𝔞₀, hcop, hc⟩ := exists_integral_rep_coprime S hS (ClassGroup.mk K I)
  have hJ : FractionalIdeal.mk0 K ⟨𝔞₀, h𝔞₀⟩ ∈ sIdeals S := mk0_mem_sIdeals S h𝔞₀ hcop
  have hker : (⟨(FractionalIdeal.mk0 K ⟨𝔞₀, h𝔞₀⟩)⁻¹ * I, (sIdeals S).mul_mem ((sIdeals S).inv_mem hJ) hI⟩ :
      sIdeals S) ∈ (sClassMap S).ker := by
    rw [MonoidHom.mem_ker]
    show ClassGroup.mk K ((FractionalIdeal.mk0 K ⟨𝔞₀, h𝔞₀⟩)⁻¹ * I) = 1
    rw [map_mul, map_inv, ClassGroup.mk_mk0, hc, inv_mul_cancel]
  rw [(lemma_1_1 S hS).2.1] at hker
  obtain ⟨x, hx⟩ := hker
  have hx' : toPrincipalIdeal (𝓞 K) K (x : Kˣ) =
      (FractionalIdeal.mk0 K ⟨𝔞₀, h𝔞₀⟩)⁻¹ * I := congrArg Subtype.val hx
  have hIeq : I = FractionalIdeal.mk0 K ⟨𝔞₀, h𝔞₀⟩ * toPrincipalIdeal (𝓞 K) K (x : Kˣ) := by
    rw [hx', mul_inv_cancel_left]
  obtain ⟨a, b, ha0, hb0, hbS, hab⟩ := lemma_1_5 S hS x
  refine ⟨b, 𝔞₀ * Ideal.span {a}, hb0, fun v hv => (hbS v hv).2, ?_⟩
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
  rw [hIeq, Units.val_mul, FractionalIdeal.coe_mk0, coe_toPrincipalIdeal,
    FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton, mul_left_comm,
    ← map_mul (FractionalIdeal.spanSingleton (𝓞 K)⁰), hab]
  congr 2
  field_simp

/-- If a unit of the fractional ideals lies in `I^{S(m)}` and equals a nonzero integral ideal, the ideal is
coprime to `m₀`. -/
theorem sup_eq_top_of_mem_coprimeIdeals (m : Modulus K) {𝔞 : Ideal (𝓞 K)} (h0 : 𝔞 ≠ ⊥)
    (U : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hU : U ∈ coprimeIdeals m)
    (hcoe : (U : FractionalIdeal (𝓞 K)⁰ K) = 𝔞) : 𝔞 ⊔ m.finite = ⊤ := by
  refine sup_eq_top_of_forall_not_dvd m fun v hv hd => ?_
  have h1 := hU v hv
  rw [hcoe, FractionalIdeal.count_coe K v h0] at h1
  have h2 : idealCount v 𝔞 = 0 := by exact_mod_cast h1
  exact (Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 hd h2

/-- The square of a nonzero integer congruent to `1` modulo `m₀` is congruent to `1` modulo `m` (it is
positive at every real place). -/
theorem sq_mem_congruenceSubgroup (m : Modulus K) {t : 𝓞 K} (ht0 : t ≠ 0) (ht : t - 1 ∈ m.finite) :
    ∃ u : Kˣ, u ∈ congruenceSubgroup m ∧ (u : K) = (algebraMap (𝓞 K) K t) ^ 2 := by
  have htK : algebraMap (𝓞 K) K t ≠ 0 := by simpa using ht0
  refine ⟨Units.mk0 _ (pow_ne_zero 2 htK), ⟨fun v hv => ?_, fun v hv => ?_⟩, rfl⟩
  · unfold IsPositiveAt
    simp only [Units.val_mk0, map_pow]
    have : InfinitePlace.embedding_of_isReal (m.isReal_of_mem v hv) (algebraMap (𝓞 K) K t) ≠ 0 := by
      simpa using htK
    positivity
  · have h1 := (mem_finite_iff_intValuation m _).1 ht v
    have h2 : (algebraMap (𝓞 K) K t) ^ 2 - 1 =
        algebraMap (𝓞 K) K (t - 1) * algebraMap (𝓞 K) K (t + 1) := by
      simp only [map_sub, map_add, map_one]; ring
    simp only [Units.val_mk0]
    rw [h2, map_mul, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    calc _ ≤ WithZero.exp (-(m.ord v : ℤ)) * 1 :=
          mul_le_mul' h1 (v.intValuation_le_one _)
      _ = _ := mul_one _

/-- **Proposition 1.6**, first part (Milne, *CFT*, V, p. 149): every class of $C_\mathfrak m$ is represented by an
integral ideal (prime to $\mathfrak m_0$). -/
@[kb "milne2020cft" "Ch. V, Proposition 1.6 (integral representatives)"]
theorem prop_1_6_integral (m : Modulus K) (c : RayClassGroup m) :
    ∃ (𝔞 : Ideal (𝓞 K)) (h0 : 𝔞 ≠ ⊥) (h : 𝔞 ⊔ m.finite = ⊤), idealRayClass m 𝔞 h0 h = c := by
  obtain ⟨I, rfl⟩ := QuotientGroup.mk_surjective c
  have hS : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  obtain ⟨b, 𝔞₁, hb0, hbS, h𝔞₁⟩ :=
    exists_mul_integral m.finiteSupport hS (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) I.2
  obtain ⟨b', hb'0, hb'⟩ := exists_mul_sub_one_mem m (y := b) (fun v hv => hbS v hv)
  have ht0 : b' * b ≠ 0 := mul_ne_zero hb'0 hb0
  obtain ⟨u, hu, hucoe⟩ := sq_mem_congruenceSubgroup m ht0 hb'
  set U : (FractionalIdeal (𝓞 K)⁰ K)ˣ := toPrincipalIdeal (𝓞 K) K u * (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    with hUdef
  have hU : U ∈ coprimeIdeals m := (coprimeIdeals m).mul_mem (rayPrincipal_le m ⟨u, hu, rfl⟩) I.2
  have hUcoe : (U : FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {b' * (b' * b)} * 𝔞₁ : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hUdef, Units.val_mul, coe_toPrincipalIdeal, hucoe, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_span_singleton, ← h𝔞₁, ← mul_assoc,
      ← map_mul (FractionalIdeal.spanSingleton (𝓞 K)⁰)]
    congr 2
    simp only [map_mul]; ring
  have h0 : (Ideal.span {b' * (b' * b)} * 𝔞₁ : Ideal (𝓞 K)) ≠ ⊥ := by
    intro h
    rw [h, FractionalIdeal.coeIdeal_bot] at hUcoe
    exact U.ne_zero hUcoe
  have h1 := sup_eq_top_of_mem_coprimeIdeals m h0 U hU hUcoe
  refine ⟨_, h0, h1, ?_⟩
  show (QuotientGroup.mk _ : RayClassGroup m) = QuotientGroup.mk I
  rw [quotient_mk_eq_iff]
  refine ⟨u⁻¹, (congruenceSubgroup m).inv_mem hu, ?_⟩
  show toPrincipalIdeal (𝓞 K) K u⁻¹ * FractionalIdeal.mk0 K _ = (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  have : FractionalIdeal.mk0 K (⟨_, mem_nonZeroDivisors_of_ne_zero h0⟩ : (Ideal (𝓞 K))⁰) = U :=
    Units.ext hUcoe.symm
  rw [this, hUdef, map_inv, inv_mul_cancel_left]

/-- The sign of $a$ at a real place $v$, as an element of $\{\pm 1\} = \mathbb Z^\times$ ($+1$ if $a > 0$). -/
def signAt (v : InfinitePlace K) (hv : v.IsReal) (a : K) : ℤˣ :=
  if 0 < InfinitePlace.embedding_of_isReal hv a then 1 else -1

/-- Two nonzero elements have the same sign at a real place exactly when their quotient is positive there. -/
theorem signAt_eq_iff (v : InfinitePlace K) (hv : v.IsReal) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    signAt v hv x = signAt v hv y ↔ IsPositiveAt K v hv (x / y) := by
  unfold signAt IsPositiveAt
  rw [map_div₀]
  have hx' : InfinitePlace.embedding_of_isReal hv x ≠ 0 := by simpa using hx
  have hy' : InfinitePlace.embedding_of_isReal hv y ≠ 0 := by simpa using hy
  generalize InfinitePlace.embedding_of_isReal hv x = ex at *
  generalize InfinitePlace.embedding_of_isReal hv y = ey at *
  rw [div_pos_iff]
  by_cases h1 : 0 < ex <;> by_cases h2 : 0 < ey
  · simp [h1, h2]
  · have : ey < 0 := lt_of_le_of_ne (not_lt.1 h2) hy'
    simp [h1, h2, this, h1.not_gt]
  · have : ex < 0 := lt_of_le_of_ne (not_lt.1 h1) hx'
    simp [h1, h2, this, h2.not_gt]
  · have h1' : ex < 0 := lt_of_le_of_ne (not_lt.1 h1) hx'
    have h2' : ey < 0 := lt_of_le_of_ne (not_lt.1 h2) hy'
    simp [h1, h2, h1', h2']

/-- A quotient `a / b` of integers congruent to `1` modulo `m₀` with equal signs at the real places of `m` is
congruent to `1` modulo `m`. -/
theorem div_mem_congruenceSubgroup (m : Modulus K) {a b : 𝓞 K} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : a - 1 ∈ m.finite) (hb : b - 1 ∈ m.finite)
    (hsign : ∀ (v : InfinitePlace K) (hv : v ∈ m.infinite),
      signAt v (m.isReal_of_mem v hv) (algebraMap (𝓞 K) K a) =
        signAt v (m.isReal_of_mem v hv) (algebraMap (𝓞 K) K b)) :
    ∃ u : Kˣ, u ∈ congruenceSubgroup m ∧
      (u : K) = algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha0
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
  refine ⟨Units.mk0 _ (div_ne_zero haK hbK), ⟨fun v hv => ?_, fun v hv => ?_⟩, rfl⟩
  · exact (signAt_eq_iff v (m.isReal_of_mem v hv) haK hbK).1 (hsign v hv)
  · have hab : a - b ∈ m.finite := by
      have := Ideal.sub_mem _ ha hb
      rwa [sub_sub_sub_cancel_right] at this
    have hbv : b ∉ v.asIdeal := by
      intro hbm
      have hle : m.finite ≤ v.asIdeal := Ideal.dvd_iff_le.1 hv
      have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
        have := Ideal.sub_mem _ hbm (hle hb)
        simpa using this
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    have hvb : v.valuation K (algebraMap (𝓞 K) K b) = 1 :=
      (v.valuation_eq_one_iff_notMem (K := K)).2 hbv
    have h2 : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b - 1 =
        algebraMap (𝓞 K) K (a - b) / algebraMap (𝓞 K) K b := by
      rw [map_sub]; field_simp
    simp only [Units.val_mk0]
    rw [h2, map_div₀, hvb, div_one, HeightOneSpectrum.valuation_of_algebraMap]
    exact (mem_finite_iff_intValuation m _).1 hab v

/-- If `α ≡ 1 mod^× m` and `α y = x` for integers with `y` prime to `m₀`, then `x ≡ y mod m₀`. -/
theorem sub_mem_finite_of_congruence (m : Modulus K) {α : Kˣ} (hα : α ∈ congruenceSubgroup m)
    {x y : 𝓞 K} (hy : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.finite → y ∉ v.asIdeal)
    (hxy : (α : K) * algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K x) : x - y ∈ m.finite := by
  rw [mem_finite_iff_intValuation]
  intro v
  by_cases hv : v.asIdeal ∣ m.finite
  · have h1 := hα.2 v hv
    have hvy : v.valuation K (algebraMap (𝓞 K) K y) = 1 :=
      (v.valuation_eq_one_iff_notMem (K := K)).2 (hy v hv)
    have h2 : algebraMap (𝓞 K) K (x - y) = ((α : K) - 1) * algebraMap (𝓞 K) K y := by
      rw [map_sub, ← hxy]; ring
    have h3 : v.valuation K (algebraMap (𝓞 K) K (x - y)) = v.intValuation (x - y) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
    rw [← h3, h2, map_mul, hvy, mul_one]
    exact h1
  · have h0 : m.ord v = 0 := by
      by_contra hne
      exact hv ((modulus_mem_finiteSupport_iff m v).2 (Nat.pos_of_ne_zero hne))
    rw [h0]
    simpa using v.intValuation_le_one _

/-- **Proposition 1.6**, second part (Milne, *CFT*, V, p. 149): two integral ideals $\mathfrak a, \mathfrak b$ prime to
$\mathfrak m_0$ have the same class in $C_\mathfrak m$ iff $a\mathfrak a = b\mathfrak b$ for some nonzero
$a, b \in \mathcal O_K$ with $a \equiv b \equiv 1 \bmod \mathfrak m_0$ and $a, b$ of the same sign at every real
prime dividing $\mathfrak m$. -/
@[kb "milne2020cft" "Ch. V, Proposition 1.6 (equivalence of integral ideals)"]
theorem prop_1_6_eq_iff (m : Modulus K) (𝔞 𝔟 : Ideal (𝓞 K)) (ha0 : 𝔞 ≠ ⊥) (ha : 𝔞 ⊔ m.finite = ⊤)
    (hb0 : 𝔟 ≠ ⊥) (hb : 𝔟 ⊔ m.finite = ⊤) :
    idealRayClass m 𝔞 ha0 ha = idealRayClass m 𝔟 hb0 hb ↔
      ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ Ideal.span {a} * 𝔞 = Ideal.span {b} * 𝔟 ∧
        a - 1 ∈ m.finite ∧ b - 1 ∈ m.finite ∧
        ∀ (v : InfinitePlace K) (hv : v ∈ m.infinite),
          signAt v (m.isReal_of_mem v hv) (algebraMap (𝓞 K) K a) =
            signAt v (m.isReal_of_mem v hv) (algebraMap (𝓞 K) K b) := by
  unfold idealRayClass
  rw [quotient_mk_eq_iff]
  have hS : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  constructor
  · rintro ⟨α, hα, h⟩
    have h' : FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = 𝔟 := by
      have := congrArg Units.val h
      simpa [coe_toPrincipalIdeal] using this
    have hαS : α ∈ primeToS m.finiteSupport := rayPrincipal_le m ⟨α, hα, rfl⟩
    obtain ⟨x, y, hx0, hy0, hxy, hαxy⟩ := lemma_1_5 m.finiteSupport hS ⟨α, hαS⟩
    have hαxy' : (α : K) = algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K y := hαxy
    have hyS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.finite → y ∉ v.asIdeal :=
      fun v hv => (hxy v hv).2
    obtain ⟨c, hc0, hc⟩ := exists_mul_sub_one_mem m hyS
    have hxK : algebraMap (𝓞 K) K x ≠ 0 := by simpa using hx0
    have hyK : algebraMap (𝓞 K) K y ≠ 0 := by simpa using hy0
    have hcK : algebraMap (𝓞 K) K c ≠ 0 := by simpa using hc0
    have hαy : (α : K) * algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K x := by
      rw [hαxy']; field_simp
    refine ⟨c * x, c * y, mul_ne_zero hc0 hx0, mul_ne_zero hc0 hy0, ?_, ?_, hc, ?_⟩
    · apply FractionalIdeal.coeIdeal_injective (K := K)
      beta_reduce
      rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton, ← h',
        ← mul_assoc, ← map_mul (FractionalIdeal.spanSingleton (𝓞 K)⁰)]
      congr 2
      rw [map_mul, map_mul, ← hαy]; ring
    · have h2 : c * x - 1 = c * (x - y) + (c * y - 1) := by ring
      rw [h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _
        (sub_mem_finite_of_congruence m hα hyS hαy)) hc
    · intro v hv
      have hcx : algebraMap (𝓞 K) K (c * x) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hcK hxK
      have hcy : algebraMap (𝓞 K) K (c * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hcK hyK
      rw [signAt_eq_iff v _ hcx hcy]
      have h3 : algebraMap (𝓞 K) K (c * x) / algebraMap (𝓞 K) K (c * y) = (α : K) := by
        rw [hαxy', map_mul, map_mul]; field_simp
      rw [h3]
      exact hα.1 v hv
  · rintro ⟨a, b, ha0, hb0, hab, ha1, hb1, hsign⟩
    obtain ⟨u, hu, hucoe⟩ := div_mem_congruenceSubgroup m ha0 hb0 ha1 hb1 hsign
    refine ⟨u, hu, Units.ext ?_⟩
    have hab' := congrArg (fun J : Ideal (𝓞 K) => (J : FractionalIdeal (𝓞 K)⁰ K)) hab
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at hab'
    have hbK : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
    rw [Units.val_mul, coe_toPrincipalIdeal, hucoe]
    show FractionalIdeal.spanSingleton (𝓞 K)⁰ _ * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =
      (𝔟 : FractionalIdeal (𝓞 K)⁰ K)
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) *
          (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
        = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b)⁻¹ *
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) *
            (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) := by
          rw [← mul_assoc, ← map_mul (FractionalIdeal.spanSingleton (𝓞 K)⁰), div_eq_inv_mul]
      _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b)⁻¹ *
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b) *
            (𝔟 : FractionalIdeal (𝓞 K)⁰ K)) := by rw [hab']
      _ = (𝔟 : FractionalIdeal (𝓞 K)⁰ K) := by
          rw [← mul_assoc, ← map_mul (FractionalIdeal.spanSingleton (𝓞 K)⁰), inv_mul_cancel₀ hbK,
            map_one, one_mul]

/-- The class group as integral ideals modulo $\mathfrak a \sim \mathfrak b \iff a\mathfrak a = b\mathfrak b$
(Milne, *CFT*, V, p. 149, after Proposition 1.6; the case $\mathfrak m = 1$, Mathlib's `ClassGroup.mk0_eq_mk0_iff`). -/
@[kb "milne2020cft" "Ch. V, §1, p. 149 (the class group via integral ideals)"]
theorem classGroup_mk0_eq_iff (𝔞 𝔟 : (Ideal (𝓞 K))⁰) :
    ClassGroup.mk0 𝔞 = ClassGroup.mk0 𝔟 ↔
      ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ Ideal.span {a} * (𝔞 : Ideal (𝓞 K)) = Ideal.span {b} * 𝔟 := by
  rw [ClassGroup.mk0_eq_mk0_iff]
  simp only [exists_prop]

end NumberFieldKB.MilneCFT
