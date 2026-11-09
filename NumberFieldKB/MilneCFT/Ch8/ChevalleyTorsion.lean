import Mathlib
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.FrobeniusGeneration
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Frobenius.Kummer.LocalUnit

/-!
# Places at which a root of unity is not an `ℓ`-th power

Step 4 of the proof of Chevalley's theorem. Let `ζ` be a primitive
`w`-th root of unity of a number field `F`, `ℓ` a prime dividing `w`, and suppose `F` has no primitive
`ℓw`-th root of unity. Outside any finite set of places there is a place `v ∤ ℓw` at which `ζ` is not an
`ℓ`-th power in `F_v`.

Proof: in `M = F(μ_{ℓw})` (splitting field of `X^{ℓw} - 1`), Frobenius elements at places outside a finite
set generate `Gal(M/F)` (Tau Ceti `closure_isArithFrobAt_eq_top`, solvable by Abel–Ruffini), so one of them
moves a root `α` of `X^ℓ - ζ` (else `α ∈ F`, but `α` is a primitive `ℓw`-th root of unity); Tau Ceti
`apply_eq_self_iff_exists_pow_eq_adicCompletion` then says that `ζ` is not an `ℓ`-th power at that place.
-/

open IsDedekindDomain NumberField Polynomial

namespace NumberFieldKB.MilneCFT.Ch8.Chevalley

/-- **A place at which `ζ_w` is not an `ℓ`-th power.** -/
theorem exists_place_not_pow {F : Type} [Field F] [NumberField F] {w ℓ : ℕ} (hw : 0 < w) (hℓ : ℓ.Prime)
    (hℓw : ℓ ∣ w) {ζ : F} (hζ : IsPrimitiveRoot ζ w) (hmax : ∀ x : F, ¬ IsPrimitiveRoot x (ℓ * w))
    (A : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ A ∧ ((ℓ * w : ℕ) : 𝓞 F) ∉ v.asIdeal ∧
      ¬ ∃ b : v.adicCompletion F, b ^ ℓ = algebraMap F (v.adicCompletion F) ζ := by
  classical
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hn0 : ((ℓ * w : ℕ) : 𝓞 F) ≠ 0 := by
    have : ℓ * w ≠ 0 := by positivity
    exact_mod_cast this
  have hfin := Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr hn0)
  let S0 : Finset (HeightOneSpectrum (𝓞 F)) := A ∪ hfin.toFinset
  let p : F[X] := X ^ (ℓ * w) - C (1 : F)
  let M := p.SplittingField
  have hsep : p.Separable := by
    apply Polynomial.separable_X_pow_sub_C
    · exact_mod_cast (by positivity : ℓ * w ≠ 0)
    · exact one_ne_zero
  have : FiniteDimensional F M := inferInstance
  have : NumberField M := NumberField.of_module_finite F M
  have : IsGalois F M := IsGalois.of_separable_splitting_field hsep
  have : Group.IsSolvable (M ≃ₐ[F] M) := gal_X_pow_sub_C_isSolvable (ℓ * w) (1 : F)
  have hgen := TauCeti.ClassFieldTheory.closure_isArithFrobAt_eq_top (K := F) (L := M) S0
  have hdvd : (X ^ ℓ - C ζ : F[X]) ∣ p := by
    have h := sub_dvd_pow_sub_pow ((X : F[X]) ^ ℓ) (C ζ) w
    rw [← pow_mul, ← C_pow, hζ.pow_eq_one] at h
    exact h
  obtain ⟨α, hα⟩ : ∃ α : M, α ^ ℓ = algebraMap F M ζ := by
    have h1 : Splits (p.map (algebraMap F M)) := SplittingField.splits p
    have hp0 : p.map (algebraMap F M) ≠ 0 := by
      rw [Ne, Polynomial.map_eq_zero_iff (algebraMap F M).injective]
      exact hsep.ne_zero
    have h2 : Splits ((X ^ ℓ - C ζ : F[X]).map (algebraMap F M)) :=
      h1.of_dvd hp0 (Polynomial.map_dvd _ hdvd)
    have hdeg : degree ((X ^ ℓ - C ζ : F[X]).map (algebraMap F M)) ≠ 0 := by
      rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
        degree_X_pow_sub_C hℓ0]
      exact_mod_cast hℓ0.ne'
    obtain ⟨α, hα⟩ := h2.exists_eval_eq_zero hdeg
    refine ⟨α, ?_⟩
    simpa [sub_eq_zero] using hα
  have hnot : ¬ ∃ a : F, a ^ ℓ = ζ := by
    rintro ⟨a, ha⟩
    refine hmax a ?_
    have hdv : orderOf a ∣ ℓ * w := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, ha, hζ.pow_eq_one]
    have hor : orderOf (a ^ ℓ) = w := by rw [ha, ← hζ.eq_orderOf]
    rw [orderOf_pow' _ hℓ0.ne'] at hor
    have : orderOf a = ℓ * w := by
      by_cases hd : ℓ ∣ orderOf a
      · rw [Nat.gcd_eq_right hd] at hor
        have := Nat.div_mul_cancel hd
        rw [hor] at this
        rw [← this, mul_comm]
      · exfalso
        have hc : Nat.Coprime (orderOf a) ℓ :=
          ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd).symm
        rw [hc, Nat.div_one] at hor
        exact hd (hor ▸ hℓw)
    rw [← this]
    exact IsPrimitiveRoot.orderOf a
  obtain ⟨σ, ⟨v, hvS, Q, hσ⟩, hne⟩ : ∃ σ : M ≃ₐ[F] M, σ ∈ {σ : M ≃ₐ[F] M | ∃ v ∉ S0,
      ∃ w : {w : HeightOneSpectrum (𝓞 M) // w.asIdeal.LiesOver v.asIdeal},
        IsArithFrobAt (𝓞 F) σ w.1.asIdeal} ∧ σ α ≠ α := by
    by_contra hall
    push Not at hall
    have hfix : ∀ f : M ≃ₐ[F] M, f α = α := by
      intro f
      have hle : Subgroup.closure {σ : M ≃ₐ[F] M | ∃ v ∉ S0,
          ∃ w : {w : HeightOneSpectrum (𝓞 M) // w.asIdeal.LiesOver v.asIdeal},
            IsArithFrobAt (𝓞 F) σ w.1.asIdeal} ≤ MulAction.stabilizer (M ≃ₐ[F] M) α :=
        Subgroup.closure_le _ |>.2 fun σ hσ => hall σ hσ
      have : f ∈ MulAction.stabilizer (M ≃ₐ[F] M) α := hle (hgen ▸ Subgroup.mem_top f)
      exact this
    obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) α).2 hfix
    apply hnot
    refine ⟨a, (algebraMap F M).injective ?_⟩
    rw [map_pow, ha, hα]
  have hvA : v ∉ A := fun h => hvS (Finset.mem_union_left _ h)
  have hvn : ((ℓ * w : ℕ) : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply hvS
    refine Finset.mem_union_right _ ?_
    rw [Set.Finite.mem_toFinset]
    exact (Ideal.dvd_span_singleton).2 (by simpa using h)
  refine ⟨v, hvA, hvn, ?_⟩
  have hint : IsIntegral ℤ ζ := hζ.isIntegral hw
  let ζ0 : 𝓞 F := ⟨ζ, hint⟩
  have hζeq : algebraMap (𝓞 F) F ζ0 = ζ := rfl
  have hζ0 : IsPrimitiveRoot ζ0 w := by
    refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 F) F) ?_
      (FaithfulSMul.algebraMap_injective (𝓞 F) F)
    rwa [hζeq]
  have hξ : IsPrimitiveRoot (ζ0 ^ (w / ℓ)) ℓ := by
    have := hζ0.pow_of_dvd (p := w / ℓ)
      (Nat.div_pos (Nat.le_of_dvd hw hℓw) hℓ0).ne' (Nat.div_dvd_of_dvd hℓw)
    rwa [Nat.div_div_self hℓw hw.ne'] at this
  have hℓv : (ℓ : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply hvn
    push_cast
    exact v.asIdeal.mul_mem_right _ h
  have hval : v.valuation F ζ = 1 := by
    have hle : v.valuation F (algebraMap (𝓞 F) F ζ0) ≤ 1 := v.valuation_le_one ζ0
    rw [hζeq] at hle
    rcases hle.lt_or_eq with h | h
    · exfalso
      have h2 := pow_lt_one₀ zero_le h hw.ne'
      rw [← map_pow, hζ.pow_eq_one, map_one] at h2
      exact lt_irrefl _ h2
    · exact h
  have := Q.2
  have key := IsArithFrobAt.apply_eq_self_iff_exists_pow_eq_adicCompletion (K := F) (M := M)
    hσ hξ hℓv hval hα
  exact fun h => hne (key.2 h)

end NumberFieldKB.MilneCFT.Ch8.Chevalley
