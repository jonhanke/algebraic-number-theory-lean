import NumberFieldKB.MilneEC.Ch4BSDPeriod
import NumberFieldKB.MilneEC.Ch4Tamagawa

/-!
# Conjecture IV.10.5 against Formal Conjectures' `StrongBSD`: the period and Tamagawa comparisons proved

Milne, *Elliptic Curves* (2006; `milne2006ec`), Chapter IV, Conjecture 10.5, pdf p. 173.
`Ch4BSD.lean` proves `conjecture10_5Corrected_iff_strongBSD` given three named comparisons. Two of them are proved
here:

* `periodComparison` (`Ch4BSDPeriod.lean`): for a minimal equation, Formal Conjectures' discriminant factor is $1$
  and the product over the unique (real) infinite place of $\mathbb Q$ is Milne's $\Omega$.
* `tamagawaComparison`: $c_p = 1$ at good primes (`tamagawaNumberAt_eq_one_of_isGoodPrime`),
  and $c_p$ computed over $\mathbb Q_p$ equals the local Tamagawa number over the adic completion of $\mathbb Q$ at
  $p$ (`tamagawaNumber_adicCompletion_eq`), through Mathlib's $\mathbb Q_p \cong \mathbb Q_{(p)}^\wedge$ and the
  independence of the minimal model (`Tamagawa.tamagawaNumber_minimal_eq`).

The comparison of the Tate–Shafarevich groups stays the named statement `ShaComparison`:
Formal Conjectures' local conditions restrict to $H^1(G_{K_v}, E(\bar K))$, Milne's to $H^1(G_{K_v}, E(\bar K_v))$,
and Mathlib's continuous cohomology has no degree-one cocycle description at this pin. Proved here towards it:
`decompHom_eq_absoluteGaloisGroup_map` (the two restriction maps of Galois groups agree).

Re-exported with only `ShaComparison`: `conjecture10_5Corrected_iff_strongBSD_of_sha`,
`conjecture10_5_iff_strongBSD_of_rank_eq_zero_of_sha`, `not_conjecture10_5_of_strongBSD_of_sha`.
-/

open WeierstrassCurve IsDedekindDomain NumberField Rat.HeightOneSpectrum

namespace NumberFieldKB.MilneEC

/-! ## Tamagawa numbers -/

section Tamagawa

variable (E : WeierstrassCurve ℚ)

/-- $c_p = 1$ at a prime of good reduction. -/
theorem tamagawaNumberAt_eq_one_of_isGoodPrime (p : ℕ) [Fact p.Prime] (hp : IsGoodPrime E p) :
    tamagawaNumberAt E p = 1 := by
  obtain ⟨hp', hgood⟩ := hp
  have :((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p] := hgood
  exact Tamagawa.tamagawaNumber_eq_one_of_hasGoodReduction (R := ℤ_[p]) ((E.baseChange ℚ_[p]).minimal ℤ_[p])

/-- Milne's $c_p$ over $\mathbb Q_p$ is Formal Conjectures' local Tamagawa number over the adic completion of
$\mathbb Q$ at $p$. -/
theorem tamagawaNumber_adicCompletion_eq [E.IsElliptic] (v : HeightOneSpectrum (𝓞 ℚ)) :
    haveI : Fact (primesEquiv v : ℕ).Prime := ⟨(primesEquiv v).2⟩
    FormalConjectures.tamagawaNumber (v.adicCompletion ℚ)
        ((E.toProjective⁄(v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ) |>.integralModel
          (v.adicCompletionIntegers ℚ)) =
      tamagawaNumberAt E (primesEquiv v) := by
  haveI : Fact (primesEquiv v : ℕ).Prime := ⟨(primesEquiv v).2⟩
  set p := primesEquiv v
  let A := v.adicCompletion ℚ
  let RA := v.adicCompletionIntegers ℚ
  let e : ℚ_[p] ≃+* A := (adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.symm
  let eR : ℤ_[p] ≃+* RA := (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv.symm
  have he : ∀ r : ℤ_[p], e (algebraMap ℤ_[p] ℚ_[p] r) = algebraMap RA A (eR r) := fun r => rfl
  set C := (E.baseChange ℚ_[p]).exists_isMinimal ℤ_[p] |>.choose with hC
  set Wp := (E.baseChange ℚ_[p]).minimal ℤ_[p] with hWp
  have hWpC : Wp = C • E.baseChange ℚ_[p] := rfl
  -- the transported minimal model
  have hmin' : (Wp.map (e : ℚ_[p] →+* A)).IsMinimal RA :=
    (MinimalTransport.isMinimal_map_iff e eR he Wp).1 inferInstance
  have hbase : (E.baseChange ℚ_[p]).map (e : ℚ_[p] →+* A) = E.baseChange A :=
    map_baseChange (R := ℚ) (S := ℚ) E (adicCompletion.padicEquiv v).symm.toAlgEquiv.toAlgHom
  have hWpe : Wp.map (e : ℚ_[p] →+* A) = C.map (e : ℚ_[p] →+* A) • E.baseChange A := by
    rw [hWpC, ← map_variableChange, hbase]
  -- its integral model is the transported integral model
  have hint : (Wp.map (e : ℚ_[p] →+* A)).integralModel RA = (Wp.integralModel ℤ_[p]).map (eR : ℤ_[p] →+* RA) := by
    apply WeierstrassCurve.map_injective (f := algebraMap RA A) (IsFractionRing.injective RA A)
    show ((Wp.map (e : ℚ_[p] →+* A)).integralModel RA).baseChange A =
      ((Wp.integralModel ℤ_[p]).map (eR : ℤ_[p] →+* RA)).baseChange A
    rw [baseChange_integralModel_eq]
    conv_lhs => rw [← baseChange_integralModel_eq ℤ_[p] Wp]
    simp only [baseChange, map_map]
    congr 1
  -- Formal Conjectures' minimal model
  set Ca := (E.baseChange A).exists_isMinimal RA |>.choose
  have hWa : (E.baseChange A).minimal RA = (Ca * (C.map (e : ℚ_[p] →+* A))⁻¹) • Wp.map (e : ℚ_[p] →+* A) := by
    rw [hWpe, mul_smul, inv_smul_smul]
    rfl
  have hΔ : (Wp.map (e : ℚ_[p] →+* A)).Δ ≠ 0 := by
    rw [hWpe, variableChange_Δ]
    have : (E.baseChange A).Δ ≠ 0 := by
      simp only [baseChange, map_Δ]
      exact (map_ne_zero _).2 E.isUnit_Δ.ne_zero
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) this
  haveI : ((Ca * (C.map (e : ℚ_[p] →+* A))⁻¹) • Wp.map (e : ℚ_[p] →+* A)).IsMinimal RA := by
    rw [← hWa]; infer_instance
  have h2 := Tamagawa.tamagawaNumber_minimal_eq (R := RA) hΔ (Ca * (C.map (e : ℚ_[p] →+* A))⁻¹)
  have h1 := Tamagawa.tamagawaNumber_map_ringEquiv e eR he (Wp.integralModel ℤ_[p])
  unfold tamagawaNumberAt
  have h3 : ∀ (W₁ W₂ : WeierstrassCurve A) [W₁.IsIntegral RA] [W₂.IsIntegral RA], W₁ = W₂ →
      FormalConjectures.tamagawaNumber A (W₁.integralModel RA).toProjective =
        FormalConjectures.tamagawaNumber A (W₂.integralModel RA).toProjective := by
    intro W₁ W₂ _ _ h
    subst h
    rfl
  rw [h3 _ _ hWa, ← h2, hint, h1]

/-- The named statement `TamagawaComparison` holds. -/
theorem tamagawaComparison : TamagawaComparison := by
  refine ⟨fun E _ => ?_⟩
  norm_cast
  have hbad : tamagawaProductBad E = ∏ᶠ p : Nat.Primes, haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
      tamagawaNumberAt E p := by
    unfold tamagawaProductBad
    refine finprod_congr fun p => ?_
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    split_ifs with hp
    · exact (tamagawaNumberAt_eq_one_of_isGoodPrime E p hp).symm
    · rfl
  rw [hbad]
  unfold FormalConjectures.tamagawaProduct
  rw [← finprod_comp_equiv (primesEquiv (R := 𝓞 ℚ))]
  refine finprod_congr fun v => ?_
  exact (tamagawaNumber_adicCompletion_eq E v).symm

end Tamagawa

/-! ## The Galois maps of the local conditions -/

/-- Milne's map $\operatorname{Gal}(\bar K_v/K_v) \to \operatorname{Gal}(\bar K/K)$ (`decompHom`, 1.9) is Mathlib's
`Field.absoluteGaloisGroup.map` used in Formal Conjectures' local conditions. -/
theorem decompHom_eq_absoluteGaloisGroup_map {K : Type} [Field K] (Kv : Type) [Field Kv] [inst : Algebra K Kv] :
    (Field.absoluteGaloisGroup.map (algebraMap K Kv) :
        Field.absoluteGaloisGroup Kv →* Field.absoluteGaloisGroup K) = decompHom (K := K) Kv := by
  have h0 : (Field.absoluteGaloisGroup.map (algebraMap K Kv) :
      Field.absoluteGaloisGroup Kv →* Field.absoluteGaloisGroup K) =
        @decompHom K _ Kv _ (algebraMap K Kv).toAlgebra := rfl
  have h : (algebraMap K Kv).toAlgebra = inst := Algebra.algebra_ext _ _ (fun _ => rfl)
  rw [h0, h]

/-! ## Conjecture 10.5 against `StrongBSD`, with only the Tate–Shafarevich comparison assumed -/

section BSD

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [Module.Finite ℤ E.toAffine.Point]

/-- **Conjecture 10.5 (corrected normalization) is Formal Conjectures' `StrongBSD` over $\mathbb Q$** for a minimal
equation, given only the named comparison of the Tate–Shafarevich groups. -/
theorem conjecture10_5Corrected_iff_strongBSD_of_sha (hSha : ShaComparison) (hmin : IsMinimalOverRat E) :
    Conjecture10_5Corrected E ↔ FormalConjectures.StrongBSD E.toAffine :=
  conjecture10_5Corrected_iff_strongBSD E hSha periodComparison tamagawaComparison hmin

/-- In rank $0$, Conjecture 10.5 as printed is Formal Conjectures' `StrongBSD`, given only `ShaComparison`. -/
theorem conjecture10_5_iff_strongBSD_of_rank_eq_zero_of_sha (hSha : ShaComparison) (hmin : IsMinimalOverRat E)
    (h0 : rank E = 0) : Conjecture10_5 E ↔ FormalConjectures.StrongBSD E.toAffine :=
  conjecture10_5_iff_strongBSD_of_rank_eq_zero E hSha periodComparison tamagawaComparison hmin h0

/-- In positive rank, `StrongBSD` refutes Conjecture 10.5 as printed, given only `ShaComparison`. -/
theorem not_conjecture10_5_of_strongBSD_of_sha (hSha : ShaComparison) (hmin : IsMinimalOverRat E)
    (hr : 0 < rank E) (h : FormalConjectures.StrongBSD E.toAffine) : ¬ Conjecture10_5 E :=
  not_conjecture10_5_of_strongBSD E hSha periodComparison tamagawaComparison hmin hr h

end BSD

end NumberFieldKB.MilneEC
