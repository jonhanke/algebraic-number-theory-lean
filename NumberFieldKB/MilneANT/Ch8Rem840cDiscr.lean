import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch8Rem840cBasic

/-!
# Milne, *Algebraic Number Theory*, Remark 8.40(c): the discriminant of `ℚ(⁸√3)`

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 8.40(c), p. 150; bib key `milne2020ant`.
We compute the discriminant of the power basis of `ℚ(⁸√a)`, show that `ℤ[⁸√3]` is the ring of integers of
`L = ℚ(⁸√3)`, and conclude `disc L = -(2²⁴ 3⁷)`.
-/

open Polynomial NumberField
open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT.Rem840c

/-- The discriminant of the power basis `1, θ, …, θ⁷` of `ℚ(⁸√a)`: `disc(X⁸ - a) = 2²⁴ (-a)⁷`. -/
theorem discr_pb (a : ℤ) [Fact (Irreducible (polyQ a))] :
    Algebra.discr ℚ (pb a).basis = (2 ^ 24 * (-a) ^ 7 : ℤ) := by
  rw [Algebra.discr_powerBasis_eq_norm, pb_gen, minpoly_root, finrank_eq]
  have hd : derivative (polyQ a) = C (8 : ℚ) * X ^ 7 := by
    simp [polyQ]
    rw [← C_1, ← C_add]; norm_num
  have hN : Algebra.norm ℚ (AdjoinRoot.root (polyQ a)) = -(a : ℚ) := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (pb a)
    rw [pb_gen, minpoly_root, pb_dim] at this
    rw [this]
    simp [polyQ, coeff_sub]
    norm_num
  rw [hd]
  simp only [map_mul, map_pow, aeval_C, aeval_X, hN]
  have h8 : Algebra.norm ℚ (algebraMap ℚ (AdjoinRoot (polyQ a)) 8) = (8:ℚ) ^ 8 := by
    rw [Algebra.norm_algebraMap, finrank_eq]
  rw [h8]
  push_cast
  norm_num

theorem minpoly_root_int (a : ℤ) [Fact (Irreducible (polyQ a))] :
    minpoly ℤ (AdjoinRoot.root (polyQ a)) = polyZ a := by
  rw [← minpoly_theta a]
  exact minpoly.algebraMap_eq (RingOfIntegers.coe_injective) (theta a)

/-- The minimal polynomial of `θ - 1` over `ℤ` is `(X+1)⁸ - 3`. -/
theorem minpoly_root_sub_one :
    minpoly ℤ (AdjoinRoot.root (polyQ 3) - 1) = (X + 1) ^ 8 - C (3 : ℤ) := by
  have hint : IsIntegral ℤ (AdjoinRoot.root (polyQ 3) - 1) := (root_isIntegral 3).sub isIntegral_one
  have h2 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have h3 := minpoly.sub_algebraMap (A := ℚ) (AdjoinRoot.root (polyQ 3)) 1
  rw [map_one] at h3
  rw [minpoly_root] at h3
  apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [← algebraMap_int_eq, ← h2, h3]
  simp [polyQ, sub_comp]
  rfl

theorem minpoly_root_sub_one_isEisensteinAt :
    (minpoly ℤ (AdjoinRoot.root (polyQ 3) - 1)).IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
  rw [minpoly_root_sub_one]
  have hc : ∀ n, ((X + 1 : ℤ[X]) ^ 8 - C (3 : ℤ)).coeff n
      = (8 : ℕ).choose n - if n = 0 then 3 else 0 := by
    intro n
    rw [coeff_sub, coeff_X_add_one_pow, coeff_C]
  have hdeg : ((X + 1 : ℤ[X]) ^ 8 - C (3 : ℤ)).natDegree = 8 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp
  have hmon : ((X + 1 : ℤ[X]) ^ 8 - C (3 : ℤ)).Monic := by
    have := (polyZ_monic 3).comp_X_add_C (1 : ℤ)
    simpa [polyZ, sub_comp] using this
  refine ⟨?_, ?_, ?_⟩
  · rw [hmon.leadingCoeff, Ideal.mem_span_singleton]; decide
  · intro n hn
    rw [hdeg] at hn
    rw [hc, Ideal.mem_span_singleton]
    interval_cases n <;> decide
  · rw [hc, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    decide

theorem adjoin_root_sub_one :
    Algebra.adjoin ℤ {AdjoinRoot.root (polyQ 3) - 1} = Algebra.adjoin ℤ {AdjoinRoot.root (polyQ 3)} := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)
  · apply Algebra.adjoin_le
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    have h := Subalgebra.add_mem (Algebra.adjoin ℤ {AdjoinRoot.root (polyQ 3) - 1})
      (Algebra.self_mem_adjoin_singleton ℤ (AdjoinRoot.root (polyQ 3) - 1)) (Subalgebra.one_mem _)
    simpa using h

theorem mem_adjoin_root_of_isIntegral (z : L) (hz : IsIntegral ℤ z) :
    z ∈ Algebra.adjoin ℤ {AdjoinRoot.root (polyQ 3)} := by
  have hint : IsIntegral ℤ (pb 3).gen := by rw [pb_gen]; exact root_isIntegral 3
  have H := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hint hz
  rw [discr_pb, pb_gen, Int.cast_smul_eq_zsmul ℚ] at H
  have H1 : ((2 : ℤ) ^ 24 * 3 ^ 7) • z ∈ Algebra.adjoin ℤ {AdjoinRoot.root (polyQ 3)} := by
    have : ((2 : ℤ) ^ 24 * 3 ^ 7) • z = -((2 ^ 24 * (-3) ^ 7 : ℤ) • z) := by
      rw [← neg_smul]; norm_num
    rw [this]
    exact Subalgebra.neg_mem _ H
  -- remove the factor `3 ^ 7`
  have H3 : (3 : ℤ) ^ 7 • ((2 : ℤ) ^ 24 • z) ∈ Algebra.adjoin ℤ {(pb 3).gen} := by
    rw [pb_gen, smul_smul, mul_comm]; exact H1
  have hei3 : (minpoly ℤ (pb 3).gen).IsEisensteinAt (Submodule.span ℤ {(3 : ℤ)}) := by
    rw [pb_gen, minpoly_root_int]
    exact polyZ_isEisensteinAt 3 3 prime_three (dvd_refl _) (by decide)
  have H2 := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (B := pb 3)
    prime_three hint (hz.smul _) H3 hei3
  rw [pb_gen] at H2
  -- remove the factor `2 ^ 24`
  have hint' : IsIntegral ℤ (AdjoinRoot.root (polyQ 3) - 1) :=
    (root_isIntegral 3).sub isIntegral_one
  have hgen : (pb 3).gen ∈ Algebra.adjoin ℚ {AdjoinRoot.root (polyQ 3) - 1} := by
    rw [pb_gen]
    have h := Subalgebra.add_mem (Algebra.adjoin ℚ {AdjoinRoot.root (polyQ 3) - 1})
      (Algebra.self_mem_adjoin_singleton ℚ (AdjoinRoot.root (polyQ 3) - 1)) (Subalgebra.one_mem _)
    simpa using h
  have htop := PowerBasis.adjoin_eq_top_of_gen_mem_adjoin hgen
  let B' : PowerBasis ℚ L := PowerBasis.ofAdjoinEqTop
    (hint'.tower_top) htop
  have hB' : B'.gen = AdjoinRoot.root (polyQ 3) - 1 := rfl
  have hint'' : IsIntegral ℤ B'.gen := by rw [hB']; exact hint'
  have H4 : (2 : ℤ) ^ 24 • z ∈ Algebra.adjoin ℤ {B'.gen} := by
    rw [hB', adjoin_root_sub_one]; exact H2
  have hei2 : (minpoly ℤ B'.gen).IsEisensteinAt (Submodule.span ℤ {(2 : ℤ)}) := by
    rw [hB']; exact minpoly_root_sub_one_isEisensteinAt
  have H5 := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (B := B')
    Int.prime_two hint'' hz H4 hei2
  rwa [hB', adjoin_root_sub_one] at H5

/-- `ℤ[⁸√3]` is the ring of integers of `L` (`X⁸ - 3` is Eisenstein at 3, and `(X+1)⁸ - 3` at 2). -/
theorem adjoin_theta_three_eq_top : Algebra.adjoin ℤ {theta 3} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : algebraMap (𝓞 L) L x ∈ Algebra.adjoin ℤ {AdjoinRoot.root (polyQ 3)} :=
    mem_adjoin_root_of_isIntegral _ x.isIntegral_coe
  let f : 𝓞 L →ₐ[ℤ] L := IsScalarTower.toAlgHom ℤ (𝓞 L) L
  have hmap : (Algebra.adjoin ℤ {theta 3}).map f = Algebra.adjoin ℤ {AdjoinRoot.root (polyQ 3)} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    rfl
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := RingOfIntegers.coe_injective hyx
  rw [← this]; exact hy

theorem isIntegral_theta (a : ℤ) [Fact (Irreducible (polyQ a))] : IsIntegral ℤ (theta a) :=
  IsIntegral.of_finite ℤ _

/-- The ring of integers of `L` has `ℤ`-power basis `1, θ, …, θ⁷`. -/
noncomputable def intPB : PowerBasis ℤ (𝓞 L) :=
  PowerBasis.ofAdjoinEqTop' (isIntegral_theta 3) adjoin_theta_three_eq_top

theorem intPB_dim : intPB.dim = 8 := by
  simp [intPB, minpoly_theta]

theorem intPB_gen : intPB.gen = theta 3 :=
  PowerBasis.ofAdjoinEqTop'_gen _ _

@[kb "milne2020ant" "v3.08, Rem. 8.40(c), p. 150"]
theorem discr_L : NumberField.discr L = -(2 ^ 24 * 3 ^ 7) := by
  apply (algebraMap ℤ ℚ).injective_int
  rw [← NumberField.discr_eq_discr _ intPB.basis, ← Algebra.discr_localizationLocalization ℤ ℤ⁰ L]
  have hd8 : intPB.dim = (pb 3).dim := by rw [intPB_dim, pb_dim]
  rw [← Algebra.discr_reindex ℚ _ (finCongr hd8)]
  have : ((Module.Basis.localizationLocalization ℚ ℤ⁰ L intPB.basis : _ → L) ∘ ⇑(finCongr hd8).symm)
      = (pb 3).basis := by
    ext i
    simp only [Function.comp_apply, Module.Basis.localizationLocalization_apply,
      PowerBasis.basis_eq_pow, intPB_gen, pb_gen]
    rw [map_pow]
    rfl
  rw [this, discr_pb]
  simp

end NumberFieldKB.MilneANT.Rem840c
