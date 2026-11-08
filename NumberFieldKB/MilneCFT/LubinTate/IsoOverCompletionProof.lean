import NumberFieldKB.MilneCFT.LubinTate.FrobeniusMinusOne

/-!
# Proposition 3.10 (Milne, CFT, Ch. I): partial progress

Reduction of `LubinTateIsoOverCompletion` to the construction of `θ` once `ε` is fixed. The element `ε`
comes from Lemma 3.11 (`frobeniusMinusOneSurjective`). The named statement `LubinTateThetaConstruction` (open input) records
exactly what is not yet proved. The Yamaguchi port does not cover the statement in the required generality:
it treats only `K = ℚ_p` (`padicCompletedUnramifiedWittRing`) and `K = 𝔽_q((t))`
(`equalCharacteristicCompletedUnramifiedField`), with those concrete `B`, whereas the named statement
quantifies over every `B` with `IsCompletedUnramifiedInt`.
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- What remains of Proposition 3.10 once `ε` with `σ ε = ε u` is given: construction of `θ` with (a)-(d). -/
@[kb "milne2020cft" "Ch. I, Prop. 3.10, construction of θ (input)"]
structure LubinTateThetaConstruction : Prop where
  construct : ∀ (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
    (σ : B ≃+* B), IsCompletedUnramifiedInt K B σ →
    ∀ {π : 𝒪[K]} (hπ : Irreducible π) (u : 𝒪[K]ˣ) {f g : PowerSeries 𝒪[K]}
      (hf : f ∈ lubinTateSeries π (resCard K)) (hg : g ∈ lubinTateSeries ((u : 𝒪[K]) * π) (resCard K))
      (ε : Bˣ), σ ε = ε * algebraMap 𝒪[K] B u →
    ∃ θ : PowerSeries B,
      PowerSeries.constantCoeff θ = 0 ∧ PowerSeries.coeff 1 θ = ε ∧
      PowerSeries.map σ.toRingHom θ = θ.subst (PowerSeries.map (algebraMap 𝒪[K] B)
        (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) hf u).toPowerSeries) ∧
      θ.subst (MvPowerSeries.map (algebraMap 𝒪[K] B)
          (lubinTateFormalGroup (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) hf).toPowerSeries) =
        (MvPowerSeries.map (algebraMap 𝒪[K] B) (lubinTateFormalGroup
          (lubinTateHyp_of_isNonarchimedeanLocalField K ((irreducible_units_mul u).2 hπ)) hg).toPowerSeries).subst
          ![θ.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) B),
            θ.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) B)] ∧
      ∀ a : 𝒪[K], θ.subst (PowerSeries.map (algebraMap 𝒪[K] B)
          (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) hf a).toPowerSeries) =
        (PowerSeries.map (algebraMap 𝒪[K] B) (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K
          ((irreducible_units_mul u).2 hπ)) hg
            a).toPowerSeries).subst θ

/-- The unit `ε` of Proposition 3.10, from Lemma 3.11. -/
theorem exists_epsilon (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
    (σ : B ≃+* B) (h : IsCompletedUnramifiedInt K B σ) (u : 𝒪[K]ˣ) :
    ∃ ε : Bˣ, σ ε = ε * algebraMap 𝒪[K] B u := by
  obtain ⟨b, hb⟩ := (frobeniusMinusOneSurjective (K := K)).mul_surjective B σ h
    (Units.map (algebraMap 𝒪[K] B).toMonoidHom u)
  refine ⟨b, ?_⟩
  have := congrArg (fun x : Bˣ => x * b) hb
  simp only [div_mul_cancel] at this
  simpa [mul_comm] using congrArg Units.val this

/-- Proposition 3.10 reduces to `LubinTateThetaConstruction`. -/
theorem lubinTateIsoOverCompletion_of_theta (H : LubinTateThetaConstruction K) :
    LubinTateIsoOverCompletion K where
  exists_iso B _ _ _ _ σ h π hπ u f g hf hg := by
    obtain ⟨ε, hε⟩ := exists_epsilon K B σ h u
    obtain ⟨θ, h1, h2, h3, h4, h5⟩ := H.construct B σ h hπ u hf hg ε hε
    exact ⟨ε, θ, hε, h1, h2, h3, h4, h5⟩

end NumberFieldKB.MilneCFT.LocalCFT
