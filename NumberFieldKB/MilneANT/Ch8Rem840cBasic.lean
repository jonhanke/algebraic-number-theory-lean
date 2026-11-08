import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Remark 8.40(c): the fields `ℚ(⁸√3)` and `ℚ(⁸√48)`

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 8.40(c), p. 150; bib key `milne2020ant`.
The pair `ℚ(⁸√a)`, `ℚ(⁸√(16a))` is the classical example of arithmetically equivalent, non-isomorphic number fields
(R. Perlis, *On the equation ζ_K(s) = ζ_K'(s)*, J. Number Theory 9 (1977); the Galois closure has group of order 32,
and the two stabilizers form a Gassmann pair). We take `a = 3`.

This file sets up the two fields: `L = ℚ[X]/(X⁸ - 3)`, `M = ℚ[X]/(X⁸ - 48)`, both defined by `3`-Eisenstein
polynomials, their generators as algebraic integers, and the minimal polynomials over `ℤ`.
-/

open Polynomial NumberField

namespace NumberFieldKB.MilneANT.Rem840c

/-- `X⁸ - a` over `ℤ`. -/
noncomputable abbrev polyZ (a : ℤ) : ℤ[X] := X ^ 8 - C a

theorem polyZ_monic (a : ℤ) : (polyZ a).Monic := monic_X_pow_sub_C a (by norm_num)

theorem polyZ_natDegree (a : ℤ) : (polyZ a).natDegree = 8 := natDegree_X_pow_sub_C

theorem polyZ_coeff (a : ℤ) (n : ℕ) :
    (polyZ a).coeff n = if n = 8 then 1 else if n = 0 then -a else 0 := by
  unfold polyZ
  rw [coeff_sub, coeff_X_pow, coeff_C]
  by_cases h8 : n = 8
  · subst h8; simp
  · by_cases h0 : n = 0
    · subst h0; simp
    · simp [h8, h0]

/-- `X⁸ - a` is Eisenstein at a prime `q` when `q ∣ a` and `q² ∤ a`. -/
theorem polyZ_isEisensteinAt (a q : ℤ) (hq : Prime q) (h1 : q ∣ a) (h2 : ¬ q ^ 2 ∣ a) :
    (polyZ a).IsEisensteinAt (Ideal.span {q}) where
  leading := by
    rw [(polyZ_monic a).leadingCoeff, Ideal.mem_span_singleton]
    exact hq.not_dvd_one
  mem := by
    intro n hn
    rw [polyZ_natDegree] at hn
    rw [polyZ_coeff, ite_eq_right (by omega), Ideal.mem_span_singleton]
    split_ifs
    · exact (dvd_neg).2 h1
    · exact dvd_zero _
  notMem := by
    rw [polyZ_coeff, ite_eq_right (by omega), ite_eq_left rfl, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    exact h2 ((dvd_neg).1 h)

theorem polyZ_irreducible (a q : ℤ) (hq : Prime q) (h1 : q ∣ a) (h2 : ¬ q ^ 2 ∣ a) :
    Irreducible (polyZ a) :=
  (polyZ_isEisensteinAt a q hq h1 h2).irreducible
    ((Ideal.span_singleton_prime hq.ne_zero).2 hq) (polyZ_monic a).isPrimitive
    (by rw [polyZ_natDegree]; norm_num)

/-- `X⁸ - a` over `ℚ`. -/
noncomputable abbrev polyQ (a : ℤ) : ℚ[X] := X ^ 8 - C (a : ℚ)

theorem polyZ_map (a : ℤ) : (polyZ a).map (Int.castRingHom ℚ) = polyQ a := by
  simp [polyZ, polyQ]

theorem polyQ_irreducible (a q : ℤ) (hq : Prime q) (h1 : q ∣ a) (h2 : ¬ q ^ 2 ∣ a) :
    Irreducible (polyQ a) := by
  rw [← polyZ_map]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (polyZ_monic a).isPrimitive).1
    (polyZ_irreducible a q hq h1 h2)

theorem polyQ_monic (a : ℤ) : (polyQ a).Monic := monic_X_pow_sub_C _ (by norm_num)

theorem prime_three : Prime (3 : ℤ) := Int.prime_three

instance fact_irreducible_three : Fact (Irreducible (polyQ 3)) :=
  ⟨polyQ_irreducible 3 3 prime_three (dvd_refl _) (by decide)⟩

instance fact_irreducible_fortyEight : Fact (Irreducible (polyQ 48)) :=
  ⟨polyQ_irreducible 48 3 prime_three (by decide) (by decide)⟩

/-- `L = ℚ(⁸√3) = ℚ[X]/(X⁸ - 3)`. -/
abbrev L : Type := AdjoinRoot (polyQ 3)

/-- `M = ℚ(⁸√48) = ℚ[X]/(X⁸ - 48)`. -/
abbrev M : Type := AdjoinRoot (polyQ 48)

instance : NumberField L := by
  have : Module.Finite ℚ L := (AdjoinRoot.powerBasis (polyQ_monic 3).ne_zero).finite
  exact ⟨⟩

instance : NumberField M := by
  have : Module.Finite ℚ M := (AdjoinRoot.powerBasis (polyQ_monic 48).ne_zero).finite
  exact ⟨⟩

/-- The power basis `1, θ, …, θ⁷` of `ℚ[X]/(X⁸ - a)`. -/
noncomputable def pb (a : ℤ) [Fact (Irreducible (polyQ a))] : PowerBasis ℚ (AdjoinRoot (polyQ a)) :=
  AdjoinRoot.powerBasis (polyQ_monic a).ne_zero

theorem pb_gen (a : ℤ) [Fact (Irreducible (polyQ a))] : (pb a).gen = AdjoinRoot.root (polyQ a) := by
  simp [pb]

theorem pb_dim (a : ℤ) [Fact (Irreducible (polyQ a))] : (pb a).dim = 8 := by
  rw [pb, AdjoinRoot.powerBasis_dim]; exact natDegree_X_pow_sub_C

theorem finrank_eq (a : ℤ) [Fact (Irreducible (polyQ a))] :
    Module.finrank ℚ (AdjoinRoot (polyQ a)) = 8 := by
  rw [PowerBasis.finrank (pb a), pb_dim]

theorem root_pow_eight (a : ℤ) : (AdjoinRoot.root (polyQ a)) ^ 8 = (a : AdjoinRoot (polyQ a)) := by
  have h := AdjoinRoot.eval₂_root (polyQ a)
  simp only [polyQ, eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h]
  simp

theorem root_isIntegral (a : ℤ) : IsIntegral ℤ (AdjoinRoot.root (polyQ a)) := by
  refine ⟨polyZ a, polyZ_monic a, ?_⟩
  simp only [polyZ, eval₂_sub, eval₂_X_pow, eval₂_C]
  rw [root_pow_eight, sub_eq_zero]
  simp

/-- The generator `θ = ⁸√a` as an algebraic integer. -/
noncomputable def theta (a : ℤ) [Fact (Irreducible (polyQ a))] : 𝓞 (AdjoinRoot (polyQ a)) :=
  ⟨AdjoinRoot.root (polyQ a), root_isIntegral a⟩

theorem minpoly_root (a : ℤ) [Fact (Irreducible (polyQ a))] :
    minpoly ℚ (AdjoinRoot.root (polyQ a)) = polyQ a := by
  rw [← pb_gen]
  exact AdjoinRoot.minpoly_powerBasis_gen_of_monic (polyQ_monic a)

/-- The minimal polynomial of `θ` over `ℤ` is `X⁸ - a`. -/
theorem minpoly_theta (a : ℤ) [Fact (Irreducible (polyQ a))] : minpoly ℤ (theta a) = polyZ a := by
  have h1 : minpoly ℤ (theta a) = minpoly ℤ (AdjoinRoot.root (polyQ a)) :=
    (minpoly.algebraMap_eq (RingOfIntegers.coe_injective) (theta a)).symm
  rw [h1]
  apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  have h2 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (root_isIntegral a)
  rw [algebraMap_int_eq] at h2
  rw [← h2, minpoly_root, polyZ_map]

end NumberFieldKB.MilneANT.Rem840c
