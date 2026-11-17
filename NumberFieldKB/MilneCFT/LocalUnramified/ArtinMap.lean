import NumberFieldKB.MilneCFT.Ch3Unramified
import NumberFieldKB.MilneCFT.Ch3UnramifiedTauCeti
import NumberFieldKB.MilneCFT.Ch3ArtinMaps
import NumberFieldKB.MilneCFT.Ch3Lemma32
import NumberFieldKB.MilneCFT.LocalCFT.UnramifiedTauCeti

/-!
# The unramified local Artin map

Source: J. S. Milne, *Class Field Theory*, v4.03 (bib key `milne2020cft`), Chapter I, §1 (Theorem 1.1 (a), (b)
for unramified extensions) and Chapter III, Lemma 3.7 and Proposition 1.9.

For a finite unramified extension $L/K$ with Frobenius element $\sigma$, the map
$\phi_{L/K} : K^\times \to \operatorname{Gal}(L/K)$, $a \mapsto \sigma^{\mathrm{ord}_K(a)}$ (`unramifiedArtin`) is
onto with kernel $\mathrm{Nm}(L^\times) = U_K\cdot\pi^{n\mathbb Z}$, $n = [L:K]$, so it induces
$K^\times/\mathrm{Nm}(L^\times) \simeq \operatorname{Gal}(L/K)$ (`unramified_reciprocity`). This is the unramified
case of the local reciprocity law, proved without any named input; by Lemma 3.7 (`Ch3.lemma_3_7`) every family
satisfying the conditions of Theorem 1.1 restricts to it on unramified extensions (`isLocalArtinMap_unramified`),
in particular the library's local Artin map `LocalCFT.tauCetiArtin` (`tauCetiArtin_eq_unramifiedArtin`).

The inputs used are the ones the library proves through the Tau Ceti port: Proposition 1.2 (`Ch3.prop1_2`), display (26)
(`Ch3.unitPrimeDecomposition`), the cyclicity of unramified Galois groups (`Ch3.unramifiedCyclic`) and
`LocalCFT.unramifiedInput`.

* `ordK` — the normalized valuation $\mathrm{ord}_K : K^\times \to \mathbb Z$, independent of the prime element
  (`ordK_eq_of_irreducible`).
* `mem_normGroup_unramified` — $a \in \mathrm{Nm}(L^\times) \iff [L:K] \mid \mathrm{ord}_K(a)$ (from Proposition 1.2 and
  display (26)).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.LocalUnramified

open NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT NumberFieldKB.MilneCFT.Ch3

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section OrdK

theorem ordK_exists {π : 𝒪[K]} (hπ : Irreducible π) (x : Kˣ) :
    ∃ k : ℤ, x * primeUnit hπ ^ (-k) ∈ unitGroup K := by
  obtain ⟨u, hu, k, rfl⟩ := exists_unit_zpow π hπ x
  refine ⟨k, ?_⟩
  rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  exact hu

theorem ordK_unique {π : 𝒪[K]} (hπ : Irreducible π) {x : Kˣ} {m m' : ℤ}
    (h : x * primeUnit hπ ^ (-m) ∈ unitGroup K) (h' : x * primeUnit hπ ^ (-m') ∈ unitGroup K) : m = m' := by
  have h1 := mul_mem h' (inv_mem h)
  have e : x * primeUnit hπ ^ (-m') * (x * primeUnit hπ ^ (-m))⁻¹ = primeUnit hπ ^ (m - m') := by
    rw [← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv, ← zpow_neg, ← zpow_add]
    congr 1; ring
  rw [e] at h1
  have := zpow_primeUnit_mem_unitGroup hπ h1
  omega

/-- The **order** $\mathrm{ord}_K(x)$ of $x \in K^\times$ (Milne, Chapter I, §1, p. 28): the exponent $k$ with
$x \in U_K\pi^k$, for a prime element $\pi$. It does not depend on $\pi$ (`ordK_eq_of_irreducible`). -/
@[kb "milne2020cft" "Ch. I, §1, p. 28 (the order ord(a) of a ∈ K^×)"]
noncomputable def ordK {π : 𝒪[K]} (hπ : Irreducible π) (x : Kˣ) : ℤ :=
  Classical.choose (ordK_exists hπ x)

theorem ordK_eq_iff {π : 𝒪[K]} (hπ : Irreducible π) (x : Kˣ) (m : ℤ) :
    ordK hπ x = m ↔ x * primeUnit hπ ^ (-m) ∈ unitGroup K :=
  ⟨fun h => h ▸ Classical.choose_spec (ordK_exists hπ x),
   fun h => ordK_unique hπ (Classical.choose_spec (ordK_exists hπ x)) h⟩

theorem ordK_mul {π : 𝒪[K]} (hπ : Irreducible π) (x y : Kˣ) :
    ordK hπ (x * y) = ordK hπ x + ordK hπ y := by
  rw [ordK_eq_iff]
  have hx := (ordK_eq_iff hπ x _).1 rfl
  have hy := (ordK_eq_iff hπ y _).1 rfl
  have e : x * y * primeUnit hπ ^ (-(ordK hπ x + ordK hπ y)) =
      (x * primeUnit hπ ^ (-ordK hπ x)) * (y * primeUnit hπ ^ (-ordK hπ y)) := by
    rw [neg_add, zpow_add]; exact mul_mul_mul_comm _ _ _ _
  rw [e]; exact mul_mem hx hy

theorem ordK_unit_mul_zpow {π : 𝒪[K]} (hπ : Irreducible π) {u : Kˣ} (hu : u ∈ unitGroup K) (k : ℤ) :
    ordK hπ (u * primeUnit hπ ^ k) = k := by
  rw [ordK_eq_iff, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  exact hu

theorem ordK_of_mem_unitGroup {π : 𝒪[K]} (hπ : Irreducible π) {u : Kˣ} (hu : u ∈ unitGroup K) :
    ordK hπ u = 0 := by
  simpa using ordK_unit_mul_zpow hπ hu 0

theorem ordK_primeUnit {π : 𝒪[K]} (hπ : Irreducible π) : ordK hπ (primeUnit hπ) = 1 := by
  simpa using ordK_unit_mul_zpow hπ (one_mem _) 1

/-- Two prime elements differ by a unit: $\pi' = w\pi$ with $w \in U_K$. -/
theorem primeUnit_eq_unit_mul {π π' : 𝒪[K]} (hπ : Irreducible π) (hπ' : Irreducible π') :
    ∃ w ∈ unitGroup K, primeUnit hπ' = w * primeUnit hπ := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[K] hπ hπ'
  refine ⟨Units.map ((Valuation.integer (ValuativeRel.valuation K)).subtype : 𝒪[K] →* K) w, ⟨w, rfl⟩, ?_⟩
  apply Units.ext
  simp only [coe_primeUnit, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass]
  rw [← hw]
  simp [mul_comm]

/-- $\mathrm{ord}_K$ does not depend on the prime element. -/
theorem ordK_eq_of_irreducible {π π' : 𝒪[K]} (hπ : Irreducible π) (hπ' : Irreducible π') (x : Kˣ) :
    ordK hπ x = ordK hπ' x := by
  obtain ⟨w, hw, hww⟩ := primeUnit_eq_unit_mul hπ hπ'
  obtain ⟨u, hu, m, rfl⟩ := exists_unit_zpow π' hπ' x
  rw [ordK_unit_mul_zpow hπ' hu, hww, mul_zpow, ← mul_assoc]
  exact ordK_unit_mul_zpow hπ (mul_mem hu (zpow_mem hw m)) m

end OrdK

/-! ## Norm groups of unramified extensions -/

theorem norm_embUnits_primeUnit (L : IntermediateField K Ω) [FiniteDimensional K L] {π : 𝒪[K]}
    (hπ : Irreducible π) :
    normUnits L (embUnits L (primeUnit hπ)) = primeUnit hπ ^ Module.finrank K L := by
  apply Units.ext
  simp [Algebra.norm_algebraMap]

/-- **The norm group of an unramified extension** (Milne, Chapter III, proof of Theorem 5.1, Step 5, and Chapter I,
§1): for $L/K$ finite unramified of degree $n$, $a \in \mathrm{Nm}(L^\times) \iff n \mid \mathrm{ord}_K(a)$, i.e.
$\mathrm{Nm}(L^\times) = U_K\cdot\pi^{n\mathbb Z}$. -/
@[kb "milne2020cft" "v4.03, Ch. III, §1, Nm(L^×) = U_K π^{nZ} for L/K unramified (from Prop. 1.2 and (26))"]
theorem mem_normGroup_unramified (L : IntermediateField K Ω) [FiniteDimensional K L] (hL : IsUnramifiedExt L)
    {π : 𝒪[K]} (hπ : Irreducible π) (x : Kˣ) :
    x ∈ normGroup L ↔ (Module.finrank K L : ℤ) ∣ ordK hπ x := by
  obtain ⟨u, hu, k, rfl⟩ := exists_unit_zpow π hπ x
  rw [ordK_unit_mul_zpow hπ hu, ← normUnits_range]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨v, hv, m, rfl⟩ := (Ch3.unitPrimeDecomposition K Ω).decomp L hL hπ y
    rw [map_mul, map_zpow, norm_embUnits_primeUnit, ← zpow_natCast, ← zpow_mul] at hy
    have h := ordK_unit_mul_zpow hπ (normUnits_mem_unitGroup L hv) ((Module.finrank K L : ℤ) * m)
    rw [hy, ordK_unit_mul_zpow hπ hu] at h
    exact ⟨m, h⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨v, hv, hvu⟩ := Ch3.prop1_2.surj L hL u hu
    refine ⟨v * embUnits L (primeUnit hπ) ^ m, ?_⟩
    rw [map_mul, map_zpow, norm_embUnits_primeUnit, hvu, ← zpow_natCast, ← zpow_mul]

/-! ## The unramified Artin map -/

/-- **The unramified local Artin map** $\phi_{L/K} : K^\times \to \operatorname{Gal}(L/K)$,
$a \mapsto \sigma^{\mathrm{ord}_K(a)}$ (Milne, Chapter I, Theorem 1.1 (a) and Chapter III, Lemma 3.7), for $\sigma$
the Frobenius element of a finite unramified extension $L/K$. It does not depend on the prime element $\pi$
(`unramifiedArtin_eq_of_irreducible`). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 3.7, p. 109 (the map a ↦ Frob^{ord a})"]
noncomputable def unramifiedArtin {L : IntermediateField K Ω} (σ : Gal(L/K)) {π : 𝒪[K]} (hπ : Irreducible π) :
    Kˣ →* Gal(L/K) where
  toFun x := σ ^ ordK hπ x
  map_one' := by rw [ordK_of_mem_unitGroup hπ (one_mem _), zpow_zero]
  map_mul' x y := by rw [ordK_mul, zpow_add]

theorem unramifiedArtin_apply {L : IntermediateField K Ω} (σ : Gal(L/K)) {π : 𝒪[K]} (hπ : Irreducible π)
    (x : Kˣ) : unramifiedArtin σ hπ x = σ ^ ordK hπ x := rfl

theorem unramifiedArtin_eq_of_irreducible {L : IntermediateField K Ω} (σ : Gal(L/K)) {π π' : 𝒪[K]}
    (hπ : Irreducible π) (hπ' : Irreducible π') : unramifiedArtin σ hπ = unramifiedArtin σ hπ' := by
  ext x
  rw [unramifiedArtin_apply, unramifiedArtin_apply, ordK_eq_of_irreducible hπ hπ']

theorem orderOf_frobenius (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    (hL : IsUnramifiedExt L) {σ : Gal(L/K)} (hσ : IsFrobenius L σ) :
    orderOf σ = Module.finrank K L := by
  have htop : Subgroup.zpowers σ = ⊤ :=
    eq_top_iff.2 fun τ _ => (Ch3.unramifiedCyclic K Ω).frob_generator L hL σ hσ τ
  rw [← Nat.card_zpowers, htop, Nat.card_congr (Subgroup.topEquiv).toEquiv]
  exact IsGalois.card_aut_eq_finrank K L

/-- **Local reciprocity for unramified extensions** (Milne, Chapter I, Theorem 1.1 (a), (b), unramified case;
Chapter III, Lemma 3.7), unconditional. Let $L/K$ be a finite unramified extension of degree $n$ with Frobenius
element $\sigma$, and $\pi$ a prime element of $K$. The map $\phi_{L/K}(a) = \sigma^{\mathrm{ord}_K(a)}$ has kernel
$\mathrm{Nm}(L^\times)$, is onto (so $K^\times/\mathrm{Nm}(L^\times) \simeq \operatorname{Gal}(L/K)$), sends $\pi$ to
$\sigma$ and is trivial on $U_K$. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1 (a), (b) for L/K unramified"]
theorem unramified_reciprocity (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    (hL : IsUnramifiedExt L) {σ : Gal(L/K)} (hσ : IsFrobenius L σ) {π : 𝒪[K]} (hπ : Irreducible π) :
    (unramifiedArtin σ hπ).ker = normGroup L ∧ Function.Surjective (unramifiedArtin σ hπ) ∧
      unramifiedArtin σ hπ (primeUnit hπ) = σ ∧ ∀ u ∈ unitGroup K, unramifiedArtin σ hπ u = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, unramifiedArtin_apply, mem_normGroup_unramified L hL hπ, ← orderOf_frobenius L hL hσ]
    exact orderOf_dvd_iff_zpow_eq_one.symm
  · intro τ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ((Ch3.unramifiedCyclic K Ω).frob_generator L hL σ hσ τ)
    refine ⟨primeUnit hπ ^ k, ?_⟩
    rw [unramifiedArtin_apply, ← one_mul (primeUnit hπ ^ k), ordK_unit_mul_zpow hπ (one_mem _)]
  · rw [unramifiedArtin_apply, ordK_primeUnit, zpow_one]
  · intro u hu
    rw [unramifiedArtin_apply, ordK_of_mem_unitGroup hπ hu, zpow_zero]

/-- The quotient form: $K^\times/\mathrm{Nm}(L^\times) \simeq \operatorname{Gal}(L/K)$ for $L/K$ finite unramified,
induced by `unramifiedArtin`. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1 (b) for L/K unramified: K^×/Nm(L^×) ≅ Gal(L/K)"]
noncomputable def unramifiedReciprocityEquiv (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    (hL : IsUnramifiedExt L) {σ : Gal(L/K)} (hσ : IsFrobenius L σ) {π : 𝒪[K]} (hπ : Irreducible π) :
    Kˣ ⧸ normGroup L ≃* Gal(L/K) :=
  (QuotientGroup.quotientMulEquivOfEq (unramified_reciprocity L hL hσ hπ).1.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (unramified_reciprocity L hL hσ hπ).2.1)

/-- Every family satisfying the conditions of Theorem 1.1 is the unramified Artin map on each finite unramified
abelian extension (Milne, Chapter III, Lemma 3.7). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 3.7, p. 109"]
theorem isLocalArtinMap_unramified {φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}
    (hφ : IsLocalArtinMap φ) (L : FiniteAbelianExt K Ω) (hL : IsUnramifiedExt L.toField)
    {σ : Gal(L.toField/K)} (hσ : IsFrobenius L.toField σ) {π : 𝒪[K]} (hπ : Irreducible π) :
    φ L = unramifiedArtin σ hπ := by
  ext x
  obtain ⟨u, hu, m, rfl⟩ := exists_unit_zpow π hπ x
  rw [Ch3.lemma_3_7 (LocalCFT.unramifiedInput K Ω) hφ L hL hσ hπ hu m, unramifiedArtin_apply, ordK_unit_mul_zpow hπ hu]

/-- **Comparison with the library's local Artin map.** On a finite unramified abelian extension $L/K$, the local
Artin map of the library, `LocalCFT.tauCetiArtin` (from the Tau Ceti port), is the explicit map
$a \mapsto \mathrm{Frob}^{\mathrm{ord}_K(a)}$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 3.7, p. 109 (the library's Artin map on unramified extensions)"]
theorem tauCetiArtin_eq_unramifiedArtin (L : FiniteAbelianExt K Ω) (hL : IsUnramifiedExt L.toField)
    {σ : Gal(L.toField/K)} (hσ : IsFrobenius L.toField σ) {π : 𝒪[K]} (hπ : Irreducible π) :
    LocalCFT.tauCetiArtin L = unramifiedArtin σ hπ :=
  isLocalArtinMap_unramified (φ := fun L : FiniteAbelianExt K Ω => LocalCFT.tauCetiArtin L)
    Ch3.isLocalArtinMap_tauCetiArtin L hL hσ hπ

/-- The library's local Artin map on an unramified extension, evaluated: $\phi_{L/K}(a) = \sigma^{\mathrm{ord}_K(a)}$. -/
theorem tauCetiArtin_apply_of_unramified (L : FiniteAbelianExt K Ω) (hL : IsUnramifiedExt L.toField)
    {σ : Gal(L.toField/K)} (hσ : IsFrobenius L.toField σ) {π : 𝒪[K]} (hπ : Irreducible π) (x : Kˣ) :
    LocalCFT.tauCetiArtin L x = σ ^ ordK hπ x := by
  rw [tauCetiArtin_eq_unramifiedArtin L hL hσ hπ, unramifiedArtin_apply]

end NumberFieldKB.MilneCFT.LocalUnramified
