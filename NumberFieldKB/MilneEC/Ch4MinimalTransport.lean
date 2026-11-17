import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Minimal Weierstrass models: transport along isomorphisms and uniqueness of the discriminant valuation

Used by the comparisons of Milne's Conjecture IV.10.5 with Formal Conjectures' `StrongBSD`
(`Ch4BSDComparisons.lean`): Milne's invariants are computed over $\mathbb Q_p$, Formal Conjectures' over the adic
completion of $\mathbb Q$ at $p$, and the two are isomorphic (Mathlib's `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`).

* `valuation_map_of_ringEquiv`: an isomorphism of discrete valuation rings, extended to the fraction fields,
  preserves the normalized valuation.
* `isIntegral_map_iff`, `isMinimal_map_iff`: integrality and minimality of a Weierstrass equation are transported.
* `valuation_Δ_eq_of_isMinimal`: two minimal equations of the same curve have discriminants of the same valuation.
* `exists_baseChange_eq_of_isMinimal`: a change of variables between two minimal equations is integral (Silverman,
  *The Arithmetic of Elliptic Curves*, VII.1.3(d) [unverified on this machine]).
-/

open WeierstrassCurve IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

namespace NumberFieldKB.MilneEC.MinimalTransport

private theorem intValuation_irreducible (S : Type*) [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (ϖ : S) (h : Irreducible ϖ) :
    intValuation (maximalIdeal S) ϖ = WithZero.exp (-1 : ℤ) :=
  intValuation_singleton _ h.ne_zero ((irreducible_iff_uniformizer ϖ).mp h)

private theorem intValuation_unit (S : Type*) [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (u : Sˣ) :
    intValuation (maximalIdeal S) (u : S) = 1 :=
  intValuation_eq_one_iff.2 (IsLocalRing.notMem_maximalIdeal.mpr u.isUnit)

private theorem isIntegral_iff_lift (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K]
    (W : WeierstrassCurve K) :
    W.IsIntegral R ↔ ((∃ r, algebraMap R K r = W.a₁) ∧ (∃ r, algebraMap R K r = W.a₂) ∧
      (∃ r, algebraMap R K r = W.a₃) ∧ (∃ r, algebraMap R K r = W.a₄) ∧
      (∃ r, algebraMap R K r = W.a₆)) := by
  constructor
  · rw [isIntegral_iff]
    rintro ⟨Wi, rfl⟩
    exact ⟨⟨Wi.a₁, by simp [baseChange]⟩, ⟨Wi.a₂, by simp [baseChange]⟩, ⟨Wi.a₃, by simp [baseChange]⟩,
      ⟨Wi.a₄, by simp [baseChange]⟩, ⟨Wi.a₆, by simp [baseChange]⟩⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₆⟩
    exact isIntegral_of_exists_lift R h₁ h₂ h₃ h₄ h₆

section Transport

variable {R K R' K' : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K']
  [IsFractionRing R' K'] (e : K ≃+* K') (eR : R ≃+* R')
  (he : ∀ r : R, e (algebraMap R K r) = algebraMap R' K' (eR r))

include he

/-- An isomorphism of discrete valuation rings, extended to their fraction fields, preserves the normalized
valuation. -/
theorem valuation_map_of_ringEquiv (x : K) :
    valuation K' (maximalIdeal R') (e x) = valuation K (maximalIdeal R) x := by
  have hint : ∀ r : R, intValuation (maximalIdeal R') (eR r) = intValuation (maximalIdeal R) r := by
    intro r
    by_cases hr : r = 0
    · simp [hr]
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hr hϖ
    have hϖ' : Irreducible (eR ϖ) := (MulEquiv.irreducible_iff (eR : R ≃* R')).mpr hϖ
    have hu' : intValuation (maximalIdeal R') (eR (u : R)) = 1 :=
      intValuation_unit R' (Units.map (eR : R ≃* R').toMonoidHom u)
    rw [map_mul, map_pow, map_mul, map_pow, map_mul, map_pow, hu', intValuation_unit R u, intValuation_irreducible _ _ hϖ', intValuation_irreducible _ _ hϖ]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  simp only [map_div₀, he, valuation_of_algebraMap, hint]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R'] [IsDiscreteValuationRing R'] [IsFractionRing R' K'] in
theorem lift_iff_map (x : K) :
    (∃ r, algebraMap R K r = x) ↔ ∃ r', algebraMap R' K' r' = e x :=
  ⟨fun ⟨r, hr⟩ => ⟨eR r, by rw [← he, hr]⟩,
   fun ⟨r', hr'⟩ => ⟨eR.symm r', e.injective (by rw [he, eR.apply_symm_apply, hr'])⟩⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R'] [IsDiscreteValuationRing R'] [IsFractionRing R' K'] in
/-- Integrality of a Weierstrass equation is transported along `e`. -/
theorem isIntegral_map_iff (W : WeierstrassCurve K) :
    W.IsIntegral R ↔ (W.map (e : K →+* K')).IsIntegral R' := by
  rw [isIntegral_iff_lift R, isIntegral_iff_lift R']
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, RingHom.coe_coe]
  rw [lift_iff_map e eR he, lift_iff_map e eR he, lift_iff_map e eR he, lift_iff_map e eR he,
    lift_iff_map e eR he]

theorem valuation_Δ_aux_map (V : WeierstrassCurve K) :
    valuation_Δ_aux R' (V.map (e : K →+* K')) = valuation_Δ_aux R V := by
  by_cases h : V.IsIntegral R
  · have h' := (isIntegral_map_iff e eR he V).1 h
    simp only [valuation_Δ_aux, h, h', dite_true]
    apply Subtype.ext
    simp [map_Δ, valuation_map_of_ringEquiv e eR he]
  · have h' : ¬ (V.map (e : K →+* K')).IsIntegral R' := fun hh => h ((isIntegral_map_iff e eR he V).2 hh)
    simp [valuation_Δ_aux, h, h']

/-- Minimality of a Weierstrass equation is transported along `e`. -/
theorem isMinimal_map_iff (W : WeierstrassCurve K) :
    W.IsMinimal R ↔ (W.map (e : K →+* K')).IsMinimal R' := by
  rw [isMinimal_iff, isMinimal_iff]
  have hsurj : ∀ C' : VariableChange K', ∃ C : VariableChange K, C.map (e : K →+* K') = C' := fun C' =>
    ⟨C'.map (e.symm : K' →+* K), by
      have : (e : K →+* K').comp (e.symm : K' →+* K) = RingHom.id K' :=
        RingHom.ext fun x => e.apply_symm_apply x
      rw [VariableChange.map_map, this, VariableChange.map_id]⟩
  have hP : ∀ C : VariableChange K, IsIntegral R' (C.map (e : K →+* K') • W.map (e : K →+* K')) ↔
      IsIntegral R (C • W) := fun C => by
    rw [map_variableChange, ← isIntegral_map_iff e eR he]
  have hf : ∀ C : VariableChange K, valuation_Δ_aux R' (C.map (e : K →+* K') • W.map (e : K →+* K')) =
      valuation_Δ_aux R (C • W) := fun C => by
    rw [map_variableChange, valuation_Δ_aux_map e eR he]
  have h1' : VariableChange.map (1 : VariableChange K) (e : K →+* K') = 1 :=
    (VariableChange.mapHom (e : K →+* K')).map_one
  rw [← h1']
  constructor
  · rintro ⟨a, b⟩
    refine ⟨(hP 1).2 a, fun j' hj' hle => ?_⟩
    obtain ⟨j, rfl⟩ := hsurj j'
    beta_reduce at hle ⊢
    rw [hf, hf] at hle ⊢
    exact b ((hP j).1 hj') hle
  · rintro ⟨a, b⟩
    refine ⟨(hP 1).1 a, fun j hj hle => ?_⟩
    have := b ((hP j).2 hj) (by beta_reduce; rw [hf, hf]; exact hle)
    beta_reduce at this
    rwa [hf, hf] at this

end Transport

section Minimal

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- Two minimal equations of the same curve have discriminants of the same valuation. -/
theorem valuation_Δ_eq_of_isMinimal {W : WeierstrassCurve K} (C : VariableChange K) [W.IsMinimal R]
    [(C • W).IsMinimal R] :
    valuation K (maximalIdeal R) (C • W).Δ = valuation K (maximalIdeal R) W.Δ := by
  have hW := ‹W.IsMinimal R›.val_Δ_maximal
  have hCW := ‹(C • W).IsMinimal R›.val_Δ_maximal
  have hP : IsIntegral R (C • W) := inferInstance
  have hP' : IsIntegral R (C⁻¹ • C • W) := by
    rw [inv_smul_smul]; infer_instance
  have h1 : valuation_Δ_aux R (C • W) ≤ valuation_Δ_aux R W := by
    have := hW.2 (j := C) hP
    rcases le_total (valuation_Δ_aux R W) (valuation_Δ_aux R (C • W)) with h | h
    · have := this (by simpa only [one_smul] using h)
      simpa only [one_smul] using this
    · exact h
  have h2 : valuation_Δ_aux R W ≤ valuation_Δ_aux R (C • W) := by
    have := hCW.2 (j := C⁻¹) hP'
    simp only [inv_smul_smul, one_smul] at this
    rcases le_total (valuation_Δ_aux R (C • W)) (valuation_Δ_aux R W) with h | h
    · exact this h
    · exact h
  have e1 := congrArg Subtype.val (le_antisymm h1 h2)
  rwa [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral] at e1

/-- A change of variables between two minimal equations with nonzero discriminant has a unit `u` and integral
`r, s, t`. (For $\Delta = 0$ every integral equation is minimal and the statement fails.) -/
theorem exists_baseChange_eq_of_isMinimal {W : WeierstrassCurve K} (hΔ : W.Δ ≠ 0) (C : VariableChange K)
    [W.IsMinimal R] [(C • W).IsMinimal R] : ∃ CR : VariableChange R, CR.baseChange K = C := by
  have hv := valuation_Δ_eq_of_isMinimal (R := R) (W := W) C
  rw [variableChange_Δ, map_mul, map_pow] at hv
  have hW0 : valuation K (maximalIdeal R) W.Δ ≠ 0 := by simpa using hΔ
  have hw : valuation K (maximalIdeal R) (↑C.u⁻¹ : K) ^ 12 = 1 := by
    have := hv
    rw [mul_eq_right₀ hW0] at this
    exact this
  have hw0 : valuation K (maximalIdeal R) (↑C.u⁻¹ : K) ≠ 0 := by simp
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hw0
  rw [← ha, ← WithZero.coe_pow, ← WithZero.coe_one, WithZero.coe_inj] at hw
  have ha1 : a = 1 := by
    have h := congrArg Multiplicative.toAdd hw
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_one] at h ⊢
    simpa using h
  have h1 : valuation K (maximalIdeal R) (↑C.u⁻¹ : K) = 1 := by rw [← ha, ha1]; rfl
  have h2 : valuation K (maximalIdeal R) (↑C.u : K) = 1 := by
    have : valuation K (maximalIdeal R) (↑C.u : K) = (valuation K (maximalIdeal R) (↑C.u⁻¹ : K))⁻¹ := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
    rw [this, h1]; simp
  obtain ⟨x, hx⟩ := exists_lift_of_le_one (A := R) (K := K) h1.le
  obtain ⟨y, hy⟩ := exists_lift_of_le_one (A := R) (K := K) h2.le
  have hxy : y * x = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_one, hx, hy]
    simp
  exact variableChange_integral_of_u_integral (W := W) (W' := C • W) (CK := C) rfl
    (u := ⟨y, x, hxy, by rw [mul_comm]; exact hxy⟩) hy

end Minimal

end NumberFieldKB.MilneEC.MinimalTransport
