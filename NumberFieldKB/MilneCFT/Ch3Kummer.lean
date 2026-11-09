import Mathlib
import QuadFormsKB.Citation

/-!
# Kummer extensions $K[\sqrt[n]{a}]$

If a field $K$ contains a primitive $n$-th root of unity and $\alpha^n \in K$, then $K[\alpha]/K$ is Galois and
cyclic of degree dividing $n$ (`kummer_adjoin`; no irreducibility assumption). Used for Milne, *Class Field
Theory*, Chapter III, Proposition 4.1.
-/
namespace NumberFieldKB.MilneCFT.Ch3
open Polynomial IntermediateField
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
/-- Kummer theory: if $K$ contains a primitive $n$-th root of unity $\zeta$ and $\alpha^n \in K$, $\alpha \ne 0$,
then $K[\alpha]/K$ is finite, Galois and cyclic, of degree dividing $n$. -/
theorem kummer_adjoin {n : ℕ} [NeZero n] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {α : Ω} (hα0 : α ≠ 0)
    (hα : α ^ n ∈ Set.range (algebraMap K Ω)) :
    FiniteDimensional K (IntermediateField.adjoin K {α}) ∧ IsGalois K (IntermediateField.adjoin K {α}) ∧
      IsCyclic Gal(IntermediateField.adjoin K {α}/K) ∧ Module.finrank K (IntermediateField.adjoin K {α}) ∣ n := by
  obtain ⟨a, ha⟩ := hα
  have hζ' : IsPrimitiveRoot (ζ : K) n := IsPrimitiveRoot.coe_units_iff.mpr hζ
  haveI : NeZero (n : K) := hζ'.neZero'
  have hint : IsIntegral K α :=
    ⟨X ^ n - C a, monic_X_pow_sub_C _ (NeZero.ne n), by simp [ha]⟩
  haveI hfd : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
    IntermediateField.adjoin.finiteDimensional hint
  set L := IntermediateField.adjoin K {α} with hL
  let β : L := IntermediateField.AdjoinSimple.gen K α
  have hβ : (β : Ω) = α := rfl
  have hβ0 : β ≠ 0 := fun h => hα0 (by rw [← hβ, h]; rfl)
  have hβn : β ^ n = algebraMap K L a := Subtype.ext (by show α ^ n = algebraMap K Ω a; exact ha.symm)
  have htop : K⟮β⟯ = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    exact hL.symm
  have hζL : IsPrimitiveRoot (algebraMap K L (ζ : K)) n := hζ'.map_of_injective (algebraMap K L).injective
  have hsplit : IsSplittingField K L (X ^ n - C a) := by
    constructor
    · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
      exact X_pow_sub_C_splits_of_isPrimitiveRoot hζL hβn
    · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← htop,
        IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite K β)]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero (NeZero.pos n) a),
        aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C, hβn, sub_self]
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hα0 (pow_eq_zero_iff (NeZero.ne n) |>.1 (by rw [← ha, map_zero]))
  have hsep : (X ^ n - C a).Separable := Polynomial.separable_X_pow_sub_C a (NeZero.ne (n : K)) ha0
  haveI hG : IsGalois K L := IsGalois.of_separable_splitting_field hsep
  have key : ∀ σ : Gal(L/K), ∃ u : rootsOfUnity n K, σ β = algebraMap K L ((u : Kˣ) : K) * β := by
    intro σ
    have h1 : (σ β) ∈ nthRoots n (algebraMap K L a) := by
      rw [mem_nthRoots (NeZero.pos n), ← map_pow, hβn, AlgEquiv.commutes]
    rw [hζL.nthRoots_eq hβn] at h1
    simp only [Multiset.mem_map, Multiset.mem_range] at h1
    obtain ⟨i, _, hi⟩ := h1
    refine ⟨⟨ζ ^ i, (mem_rootsOfUnity n _).2 (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])⟩, ?_⟩
    rw [← hi]
    simp
  have uniq : ∀ u v : rootsOfUnity n K, algebraMap K L ((u : Kˣ) : K) * β = algebraMap K L ((v : Kˣ) : K) * β → u = v := by
    intro u v h
    have := mul_right_cancel₀ hβ0 h
    exact Subtype.ext (Units.ext ((algebraMap K L).injective this))
  let f : Gal(L/K) →* rootsOfUnity n K :=
    MonoidHom.mk' (fun σ => (key σ).choose) (by
      intro σ τ
      apply uniq
      have hσ := (key σ).choose_spec
      have hτ := (key τ).choose_spec
      have e1 : (σ * τ) β = algebraMap K L ((key σ).choose : Kˣ) * (algebraMap K L ((key τ).choose : Kˣ) * β) := by
        calc (σ * τ) β = σ (τ β) := rfl
          _ = σ (algebraMap K L ((key τ).choose : Kˣ) * β) := congrArg σ hτ
          _ = _ := by rw [map_mul, AlgEquiv.commutes]; exact (congrArg _ hσ).trans (by ring)
      rw [← (key (σ * τ)).choose_spec, e1]
      simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
      ring)
  have finj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h1 : σ β = β := by
      have := (key σ).choose_spec
      have h2 : (key σ).choose = 1 := hσ
      rw [this, h2]
      simp
    apply AlgEquiv.ext
    intro x
    have := IntermediateField.algHom_ext_of_eq_adjoin (F := K) (S := L) (s := {α}) hL
      (φ₁ := σ.toAlgHom) (φ₂ := AlgHom.id K L) (fun x hx => by
        simp only [Set.mem_singleton_iff] at hx
        subst hx
        exact h1)
    exact congrArg (fun φ => φ x) this
  refine ⟨hfd, hG, ?_, ?_⟩
  · exact isCyclic_of_injective f finj
  · rw [← IsGalois.card_aut_eq_finrank]
    have := hζ.card_rootsOfUnity'
    rw [← this]
    exact Subgroup.card_dvd_of_injective f finj
end NumberFieldKB.MilneCFT.Ch3
