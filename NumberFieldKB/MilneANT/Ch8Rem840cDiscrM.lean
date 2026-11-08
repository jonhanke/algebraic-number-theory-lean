import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch8Rem840cBasic
import NumberFieldKB.MilneANT.Ch8Rem840cDiscr

/-!
# Milne, *Algebraic Number Theory*, Remark 8.40(c): the discriminant of `ℚ(⁸√48)`

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 8.40(c), p. 150; bib key `milne2020ant`.
We show `disc M = -(2²⁴ 3⁷)` for `M = ℚ(⁸√48) = ℚ[X]/(X⁸ - 48)`, the same value as for `ℚ(⁸√3)`.

Write `t = ⁸√48`. The ring of integers of `M` is the `ℤ`-lattice `Λ` with basis
`1, t, t²/2, t³/2, t⁴/4, (t⁵+4t)/8, t⁶/8, (t⁷+4t³)/16`.
Strategy: the basis elements are integral; `Λ` is stable under multiplication by `t` and by the integral element
`η = 5t/2 + t³ + 3t⁵/8 + t⁷/8`; every integral `z` has `2⁵² z ∈ ℤ[t]` (discriminant of the power basis and
`3`-Eisenstein), and `22103^k z ∈ ℤ[η - 1]` (`η` generates `M`, with `2`-Eisenstein minimal polynomial of `η - 1`),
hence `z ∈ Λ` by Bezout. Then `disc M` is computed from the basis, whose coordinate matrix with respect to the
power basis is lower triangular with determinant `2⁻¹⁴`.
-/

open Polynomial NumberField
open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT.Rem840c

namespace DiscrM

section Generic

variable {K : Type*} [Field K] [CharZero K]

/-- The candidate `ℤ`-basis of the ring of integers of `ℚ(⁸√48)`, in terms of `t = ⁸√48`. -/
noncomputable def bb (t : K) : Fin 8 → K :=
  ![1, t, t ^ 2 / 2, t ^ 3 / 2, t ^ 4 / 4, (t ^ 5 + 4 * t) / 8, t ^ 6 / 8, (t ^ 7 + 4 * t ^ 3) / 16]

/-- The `ℤ`-span of `bb t`. -/
noncomputable def Lam (t : K) : Submodule ℤ K := Submodule.span ℤ (Set.range (bb t))

omit [CharZero K] in
theorem bb_mem (t : K) (j : Fin 8) : bb t j ∈ Lam t := Submodule.subset_span ⟨j, rfl⟩

omit [CharZero K] in
theorem mem_Lam_of (t x : K) (c : Fin 8 → ℤ) (h : x = ∑ k, (c k : K) * bb t k) : x ∈ Lam t := by
  rw [h]
  refine Submodule.sum_mem _ fun k _ => ?_
  have := Submodule.smul_mem (Lam t) (c k) (bb_mem t k)
  simpa [zsmul_eq_mul] using this

omit [CharZero K] in
theorem one_mem_Lam (t : K) : (1 : K) ∈ Lam t := by
  simpa [bb] using bb_mem t 0

theorem t_mul_mem (t : K) (ht : t ^ 8 = 48) {x : K} (hx : x ∈ Lam t) : t * x ∈ Lam t := by
  refine Submodule.span_induction (p := fun x _ => t * x ∈ Lam t) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact mem_Lam_of t _ ![0, 1, 0, 0, 0, 0, 0, 0] (by simp [Fin.sum_univ_eight, bb])
    · exact mem_Lam_of t _ ![0, 0, 2, 0, 0, 0, 0, 0] (by simp [Fin.sum_univ_eight, bb]; ring)
    · exact mem_Lam_of t _ ![0, 0, 0, 1, 0, 0, 0, 0] (by simp [Fin.sum_univ_eight, bb]; ring)
    · exact mem_Lam_of t _ ![0, 0, 0, 0, 2, 0, 0, 0] (by simp [Fin.sum_univ_eight, bb]; ring)
    · exact mem_Lam_of t _ ![0, -1, 0, 0, 0, 2, 0, 0] (by simp [Fin.sum_univ_eight, bb]; ring)
    · exact mem_Lam_of t _ ![0, 0, 1, 0, 0, 0, 1, 0] (by simp [Fin.sum_univ_eight, bb]; ring)
    · exact mem_Lam_of t _ ![0, 0, 0, -1, 0, 0, 0, 2] (by simp [Fin.sum_univ_eight, bb]; ring)
    · exact mem_Lam_of t _ ![3, 0, 0, 0, 1, 0, 0, 0]
        (by simp [Fin.sum_univ_eight, bb]; linear_combination (1/16) * ht)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]; exact add_mem hx hy
  · intro a x _ hx
    rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

/-- The element `η = (5/2) t + t³ + (3/8) t⁵ + (1/8) t⁷ = b₁ + b₃ + 3 b₅ + 2 b₇`. -/
noncomputable def eta' (t : K) : K :=
  (5 / 2 : K) * t + t ^ 3 + (3 / 8 : K) * t ^ 5 + (1 / 8 : K) * t ^ 7

theorem eta_mul_mem (t : K) (ht : t ^ 8 = 48) {x : K} (hx : x ∈ Lam t) : eta' t * x ∈ Lam t := by
  refine Submodule.span_induction (p := fun x _ => eta' t * x ∈ Lam t) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact mem_Lam_of t _ ![0, 1, 0, 1, 0, 3, 0, 2] (by simp [Fin.sum_univ_eight, bb, eta']; ring)
    · exact mem_Lam_of t _ ![6, 0, 5, 0, 4, 0, 3, 0]
        (by simp [Fin.sum_univ_eight, bb, eta']; linear_combination (1/8) * ht)
    · exact mem_Lam_of t _ ![0, 1, 0, 1, 0, 4, 0, 3]
        (by simp [Fin.sum_univ_eight, bb, eta']; linear_combination (1/16 * t) * ht)
    · exact mem_Lam_of t _ ![9, 0, 6, 0, 5, 0, 4, 0]
        (by simp [Fin.sum_univ_eight, bb, eta']; linear_combination (3/16 + 1/16 * t ^ 2) * ht)
    · exact mem_Lam_of t _ ![0, 2, 0, 1, 0, 5, 0, 4]
        (by simp [Fin.sum_univ_eight, bb, eta']; linear_combination (3/32 * t + 1/32 * t ^ 3) * ht)
    · exact mem_Lam_of t _ ![9, 0, 7, 0, 5, 0, 4, 0]
        (by simp [Fin.sum_univ_eight, bb, eta'];
            linear_combination (3/16 + 3/64 * t ^ 2 + 1/64 * t ^ 4) * ht)
    · exact mem_Lam_of t _ ![0, 3, 0, 2, 0, 6, 0, 5]
        (by simp [Fin.sum_univ_eight, bb, eta'];
            linear_combination (1/8 * t + 3/64 * t ^ 3 + 1/64 * t ^ 5) * ht)
    · exact mem_Lam_of t _ ![12, 0, 9, 0, 7, 0, 5, 0]
        (by simp [Fin.sum_univ_eight, bb, eta'];
            linear_combination (1/4 + 3/32 * t ^ 2 + 3/128 * t ^ 4 + 1/128 * t ^ 6) * ht)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]; exact add_mem hx hy
  · intro a x _ hx
    rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

omit [CharZero K] in
/-- `ℤ[s] ⊆ Λ` as soon as every element of `s` preserves `Λ` under multiplication. -/
theorem adjoin_le_Lam (t : K) (s : Set K) (hs : ∀ a ∈ s, ∀ y ∈ Lam t, a * y ∈ Lam t) {x : K}
    (hx : x ∈ Algebra.adjoin ℤ s) : x ∈ Lam t := by
  have : ∀ y ∈ Lam t, x * y ∈ Lam t := by
    refine Algebra.adjoin_induction (p := fun x _ => ∀ y ∈ Lam t, x * y ∈ Lam t) ?_ ?_ ?_ ?_ hx
    · exact hs
    · intro r y hy
      have := Submodule.smul_mem _ r hy
      simpa [zsmul_eq_mul] using this
    · intro a b _ _ ha hb y hy
      rw [add_mul]; exact add_mem (ha y hy) (hb y hy)
    · intro a b _ _ ha hb y hy
      rw [mul_assoc]; exact ha _ (hb y hy)
  simpa using this 1 (one_mem_Lam t)

theorem bb_isIntegral (t : K) (ht : t ^ 8 = 48) (hti : IsIntegral ℤ t) (j : Fin 8) :
    IsIntegral ℤ (bb t j) := by
  have hβ : IsIntegral ℤ (t ^ 2 / 2) := by
    refine ⟨X ^ 4 - C 3, monic_X_pow_sub_C _ (by norm_num), ?_⟩
    have : (t ^ 2 / 2) ^ 4 = 3 := by linear_combination (1 / 16) * ht
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, this]
    simp
  have h5 : IsIntegral ℤ ((t ^ 5 + 4 * t) / 8) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have : ((t ^ 5 + 4 * t) / 8) ^ 2 = (t ^ 2 / 2) + (t ^ 2 / 2) + (t ^ 2 / 2) ^ 3 := by
      linear_combination (t ^ 2 / 64) * ht
    rw [this]
    exact (hβ.add hβ).add (hβ.pow 3)
  fin_cases j
  · simpa [bb] using isIntegral_one
  · simpa [bb] using hti
  · simpa [bb] using hβ
  · have : t ^ 3 / 2 = t * (t ^ 2 / 2) := by ring
    simpa [bb, this] using hti.mul hβ
  · have : t ^ 4 / 4 = (t ^ 2 / 2) ^ 2 := by ring
    simpa [bb, this] using hβ.pow 2
  · simpa [bb] using h5
  · have : t ^ 6 / 8 = (t ^ 2 / 2) ^ 3 := by ring
    simpa [bb, this] using hβ.pow 3
  · have : (t ^ 7 + 4 * t ^ 3) / 16 = (t ^ 2 / 2) * ((t ^ 5 + 4 * t) / 8) := by ring
    simpa [bb, this] using hβ.mul h5

theorem eta_eq (t : K) : eta' t = bb t 1 + bb t 3 + 3 * bb t 5 + 2 * bb t 7 := by
  simp [bb, eta']; ring

/-- Coordinates of `bb t` in the power basis `1, t, …, t⁷`. -/
def coordMat : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1/2, 0, 0, 0, 0, 0;
     0, 0, 0, 1/2, 0, 0, 0, 0;
     0, 0, 0, 0, 1/4, 0, 0, 0;
     0, 1/2, 0, 0, 0, 1/8, 0, 0;
     0, 0, 0, 0, 0, 0, 1/8, 0;
     0, 0, 0, 1/4, 0, 0, 0, 1/16]

theorem det_coordMat : coordMat.det = 1 / 2 ^ 14 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [Fin.prod_univ_eight, coordMat]; norm_num
  · intro i j hij
    have hij' : i < j := hij
    fin_cases i <;> fin_cases j <;> simp [coordMat] at hij' ⊢

theorem bb_eq_mulVec (t : K) :
    bb t = Matrix.mulVec (coordMat.map (algebraMap ℚ K)) (fun i : Fin 8 => t ^ (i : ℕ)) := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_eight, bb, coordMat] <;> ring

theorem etaRel (t : K) (ht : t ^ 8 = 48) :
    eta' t ^ 8 - 264 * eta' t ^ 6 + 72 * eta' t ^ 4 - 24 * eta' t ^ 2 - 3 = 0 := by
  unfold eta'
  linear_combination ((1/16777216) * t^48 + (3/2097152) * t^46 + (79/4194304) * t^44 + (377/2097152) * t^42 + (11483/8388608) * t^40 + (18337/2097152) * t^38 + (202823/4194304) * t^36 + (493695/2097152) * t^34 + (17105953/16777216) * t^32 + (2073997/524288) * t^30 + (7225211/524288) * t^28 + (2828163/65536) * t^26 + (127256799/1048576) * t^24 + (10006823/32768) * t^22 + (5607321/8192) * t^20 + (11106227/8192) * t^18 + (153590275/65536) * t^16 + (7129481/2048) * t^14 + (8840279/2048) * t^12 + (136345/32) * t^10 + (12698213/4096) * t^8 + (160059/128) * t^6 + (-1795/32) * t^4 + (25/8) * t^2 + (1/16) * t^0) * ht

theorem etaGen (t : K) (ht : t ^ 8 = 48) :
    89087 * eta' t - 218840 * eta' t ^ 3 + 1130109 * eta' t ^ 5 - 4282 * eta' t ^ 7 = 22103 * t := by
  unfold eta'
  linear_combination ((-2141/1048576) * t^41 + (-44961/1048576) * t^39 + (-524545/1048576) * t^37 + (-4481113/1048576) * t^35 + (-30631287/1048576) * t^33 + (-175842471/1048576) * t^31 + (-874776203/1048576) * t^29 + (-3812324691/1048576) * t^27 + (-458500235/32768) * t^25 + (-12521380875/262144) * t^23 + (-4723421931/32768) * t^21 + (-12581952773/32768) * t^19 + (-29406091653/32768) * t^17 + (-7439349639/4096) * t^15 + (-25786808401/8192) * t^13 + (-18617570723/4096) * t^11 + (-10669857009/2048) * t^9 + (-4585429457/1024) * t^7 + (-1133785223/512) * t^5 + (69381) * t^3 + (-133743/32) * t^1) * ht

end Generic

section Special

/-- The generator `t = ⁸√48` of `M`. -/
noncomputable abbrev tM : M := AdjoinRoot.root (polyQ 48)

theorem tM_pow : tM ^ 8 = 48 := by simpa using root_pow_eight 48

theorem tM_isIntegral : IsIntegral ℤ tM := root_isIntegral 48

theorem bbM_isIntegral (j : Fin 8) : IsIntegral ℤ (bb tM j) :=
  bb_isIntegral tM tM_pow tM_isIntegral j

theorem etaM_isIntegral : IsIntegral ℤ (eta' tM) := by
  rw [eta_eq]
  have h := bbM_isIntegral
  have h3 : IsIntegral ℤ (3 : M) := by simpa using isIntegral_algebraMap (R := ℤ) (x := (3 : ℤ)) (A := M)
  have h2 : IsIntegral ℤ (2 : M) := by simpa using isIntegral_algebraMap (R := ℤ) (x := (2 : ℤ)) (A := M)
  exact (((h 1).add (h 3)).add (h3.mul (h 5))).add (h2.mul (h 7))

theorem adjoin_sub_one (x : M) : Algebra.adjoin ℤ {x - 1} = Algebra.adjoin ℤ {x} := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)
  · apply Algebra.adjoin_le
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    have h := Subalgebra.add_mem (Algebra.adjoin ℤ {x - 1})
      (Algebra.self_mem_adjoin_singleton ℤ (x - 1)) (Subalgebra.one_mem _)
    simpa using h

/-- Step 1: `2⁵² z ∈ ℤ[t]` for integral `z` (discriminant of the power basis, `3`-Eisenstein). -/
theorem mem_adjoin_t (z : M) (hz : IsIntegral ℤ z) :
    ((2 : ℤ) ^ 52) • z ∈ Algebra.adjoin ℤ {tM} := by
  have hint : IsIntegral ℤ (pb 48).gen := by rw [pb_gen]; exact root_isIntegral 48
  have H := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hint hz
  rw [discr_pb, pb_gen, Int.cast_smul_eq_zsmul ℚ] at H
  have H1 : ((2 : ℤ) ^ 52 * 3 ^ 7) • z ∈ Algebra.adjoin ℤ {tM} := by
    have : ((2 : ℤ) ^ 52 * 3 ^ 7) • z = -((2 ^ 24 * (-48) ^ 7 : ℤ) • z) := by
      rw [← neg_smul]; norm_num
    rw [this]
    exact Subalgebra.neg_mem _ H
  have H3 : (3 : ℤ) ^ 7 • ((2 : ℤ) ^ 52 • z) ∈ Algebra.adjoin ℤ {(pb 48).gen} := by
    rw [pb_gen, smul_smul, mul_comm]; exact H1
  have hei3 : (minpoly ℤ (pb 48).gen).IsEisensteinAt (Submodule.span ℤ {(3 : ℤ)}) := by
    rw [pb_gen, minpoly_root_int]
    exact polyZ_isEisensteinAt 48 3 prime_three (by decide) (by decide)
  have H2 := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (B := pb 48)
    prime_three hint (hz.smul _) H3 hei3
  rwa [pb_gen] at H2

/-- The minimal polynomial of `η - 1` over `ℤ`. -/
noncomputable def gPoly : ℤ[X] :=
  X ^ 8 + C 8 * X ^ 7 - C 236 * X ^ 6 - C 1528 * X ^ 5 - C 3818 * X ^ 4 - C 4936 * X ^ 3
    - C 3524 * X ^ 2 - C 1336 * X - C 218

theorem gPoly_natDegree : gPoly.natDegree = 8 := by
  unfold gPoly; compute_degree!

theorem gPoly_monic : gPoly.Monic := by
  unfold gPoly; monicity!

theorem gPoly_isEisensteinAt : gPoly.IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gPoly_monic.leadingCoeff, Ideal.mem_span_singleton]; decide
  · intro n hn
    rw [gPoly_natDegree] at hn
    rw [Ideal.mem_span_singleton]
    interval_cases n <;> simp [gPoly, coeff_X_pow, coeff_X]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp [gPoly, coeff_X_pow, coeff_X]

theorem gPoly_irreducible : Irreducible gPoly :=
  gPoly_isEisensteinAt.irreducible (Ideal.span_singleton_prime (by norm_num) |>.2 Int.prime_two)
    gPoly_monic.isPrimitive (by rw [gPoly_natDegree]; norm_num)

theorem aeval_gPoly : aeval (eta' tM - 1) gPoly = 0 := by
  have := etaRel tM tM_pow
  simp only [gPoly, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
  simp
  linear_combination this

theorem minpoly_eta_sub_one : minpoly ℤ (eta' tM - 1) = gPoly := by
  have hint : IsIntegral ℤ (eta' tM - 1) := etaM_isIntegral.sub isIntegral_one
  apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  have h2 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  rw [algebraMap_int_eq] at h2
  rw [← h2]
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast gPoly_monic.isPrimitive).1
      gPoly_irreducible
  · have := aeval_map_algebraMap ℚ (eta' tM - 1) gPoly
    rw [algebraMap_int_eq] at this
    rw [this]; exact aeval_gPoly
  · exact gPoly_monic.map _

/-- Step 3 ingredient: `22103 t ∈ ℤ[η]`. -/
theorem smul_t_mem : (22103 : ℤ) ^ 1 • tM ∈ Algebra.adjoin ℤ {eta' tM} := by
  have hη := Algebra.self_mem_adjoin_singleton ℤ (eta' tM)
  have h := etaGen tM tM_pow
  have : (22103 : ℤ) ^ 1 • tM =
      (89087 : ℤ) • eta' tM - (218840 : ℤ) • eta' tM ^ 3 + (1130109 : ℤ) • eta' tM ^ 5
        - (4282 : ℤ) • eta' tM ^ 7 := by
    simp only [zsmul_eq_mul]
    push_cast
    linear_combination (-1) * h
  rw [this]
  exact sub_mem (add_mem (sub_mem (Subalgebra.smul_mem _ hη _) (Subalgebra.smul_mem _ (pow_mem hη 3) _))
    (Subalgebra.smul_mem _ (pow_mem hη 5) _)) (Subalgebra.smul_mem _ (pow_mem hη 7) _)

theorem exists_pow_smul_mem {y : M} (hy : y ∈ Algebra.adjoin ℤ {tM}) :
    ∃ k : ℕ, (22103 : ℤ) ^ k • y ∈ Algebra.adjoin ℤ {eta' tM} := by
  refine Algebra.adjoin_induction (p := fun y _ => ∃ k : ℕ, (22103 : ℤ) ^ k • y ∈ Algebra.adjoin ℤ {eta' tM})
    ?_ ?_ ?_ ?_ hy
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨1, smul_t_mem⟩
  · intro r
    exact ⟨0, by simp⟩
  · rintro a b _ _ ⟨k1, h1⟩ ⟨k2, h2⟩
    refine ⟨k1 + k2, ?_⟩
    have : (22103 : ℤ) ^ (k1 + k2) • (a + b) =
        (22103 : ℤ) ^ k2 • ((22103 : ℤ) ^ k1 • a) + (22103 : ℤ) ^ k1 • ((22103 : ℤ) ^ k2 • b) := by
      rw [smul_add, smul_smul, smul_smul, pow_add, mul_comm ((22103 : ℤ) ^ k2) ((22103 : ℤ) ^ k1)]
    rw [this]
    exact add_mem (Subalgebra.smul_mem _ h1 _) (Subalgebra.smul_mem _ h2 _)
  · rintro a b _ _ ⟨k1, h1⟩ ⟨k2, h2⟩
    refine ⟨k1 + k2, ?_⟩
    have : (22103 : ℤ) ^ (k1 + k2) • (a * b) =
        ((22103 : ℤ) ^ k1 • a) * ((22103 : ℤ) ^ k2 • b) := by
      rw [smul_mul_smul_comm, pow_add]
    rw [this]
    exact mul_mem h1 h2

theorem adjoin_t_le {x : M} (hx : x ∈ Algebra.adjoin ℤ {tM}) : x ∈ Lam tM :=
  adjoin_le_Lam tM {tM} (by
    rintro a rfl y hy
    exact t_mul_mem tM tM_pow hy) hx

theorem adjoin_eta_le {x : M} (hx : x ∈ Algebra.adjoin ℤ {eta' tM}) : x ∈ Lam tM :=
  adjoin_le_Lam tM {eta' tM} (by
    rintro a rfl y hy
    exact eta_mul_mem tM tM_pow hy) hx

/-- Every algebraic integer of `M` lies in the lattice `Λ`. -/
theorem mem_Lam_of_isIntegral (z : M) (hz : IsIntegral ℤ z) : z ∈ Lam tM := by
  have hA := mem_adjoin_t z hz
  obtain ⟨k, hk⟩ := exists_pow_smul_mem hA
  have hint' : IsIntegral ℤ (eta' tM - 1) := etaM_isIntegral.sub isIntegral_one
  -- `t ∈ ℚ(η - 1)`
  have hgen : (pb 48).gen ∈ Algebra.adjoin ℚ {eta' tM - 1} := by
    rw [pb_gen]
    have hη : eta' tM ∈ Algebra.adjoin ℚ {eta' tM - 1} := by
      have h := Subalgebra.add_mem (Algebra.adjoin ℚ {eta' tM - 1})
        (Algebra.self_mem_adjoin_singleton ℚ (eta' tM - 1)) (Subalgebra.one_mem _)
      simpa using h
    have ht : tM = (22103⁻¹ : ℚ) • ((89087 : ℚ) • eta' tM - (218840 : ℚ) • eta' tM ^ 3
        + (1130109 : ℚ) • eta' tM ^ 5 - (4282 : ℚ) • eta' tM ^ 7) := by
      simp only [Rat.smul_def]
      have h := etaGen tM tM_pow
      have h22 : (22103 : M) ≠ 0 := by norm_num
      push_cast
      field_simp
      linear_combination (-1) * h
    have hmem := Subalgebra.smul_mem _ (sub_mem (add_mem (sub_mem (Subalgebra.smul_mem _ hη (89087 : ℚ))
      (Subalgebra.smul_mem _ (pow_mem hη 3) (218840 : ℚ))) (Subalgebra.smul_mem _ (pow_mem hη 5) (1130109 : ℚ)))
      (Subalgebra.smul_mem _ (pow_mem hη 7) (4282 : ℚ))) (22103⁻¹ : ℚ)
    rw [← ht] at hmem
    exact hmem
  have htop := PowerBasis.adjoin_eq_top_of_gen_mem_adjoin hgen
  let B' : PowerBasis ℚ M := PowerBasis.ofAdjoinEqTop (hint'.tower_top) htop
  have hB' : B'.gen = eta' tM - 1 := rfl
  have hint'' : IsIntegral ℤ B'.gen := by rw [hB']; exact hint'
  have H4 : (2 : ℤ) ^ 52 • ((22103 : ℤ) ^ k • z) ∈ Algebra.adjoin ℤ {B'.gen} := by
    rw [hB', adjoin_sub_one, smul_comm]; exact hk
  have hei2 : (minpoly ℤ B'.gen).IsEisensteinAt (Submodule.span ℤ {(2 : ℤ)}) := by
    rw [hB', minpoly_eta_sub_one]; exact gPoly_isEisensteinAt
  have H5 := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (B := B')
    Int.prime_two hint'' (hz.smul _) H4 hei2
  rw [hB', adjoin_sub_one] at H5
  have hB : (22103 : ℤ) ^ k • z ∈ Lam tM := adjoin_eta_le H5
  have hA' : (2 : ℤ) ^ 52 • z ∈ Lam tM := adjoin_t_le hA
  have hcop : IsCoprime ((2 : ℤ) ^ 52) ((22103 : ℤ) ^ k) :=
    IsCoprime.pow ⟨-11051, 1, by norm_num⟩
  obtain ⟨u, v, huv⟩ := hcop
  have : z = u • ((2 : ℤ) ^ 52 • z) + v • ((22103 : ℤ) ^ k • z) := by
    rw [smul_smul, smul_smul, ← add_smul, huv, one_smul]
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ hA') (Submodule.smul_mem _ _ hB)

theorem discr_bb : Algebra.discr ℚ (bb tM) = -(2 ^ 24 * 3 ^ 7) := by
  rw [bb_eq_mulVec, Algebra.discr_of_matrix_mulVec, det_coordMat]
  have h1 : Algebra.discr ℚ (fun i : Fin 8 => tM ^ (i : ℕ)) = (2 ^ 24 * (-48) ^ 7 : ℤ) := by
    rw [← discr_pb 48, ← Algebra.discr_reindex ℚ (pb 48).basis (finCongr (pb_dim 48))]
    congr 1
    ext i
    simp [PowerBasis.basis_eq_pow, pb_gen]
  rw [h1]
  norm_num

theorem linearIndependent_bb : LinearIndependent ℚ (bb tM) := by
  by_contra h
  have := Algebra.discr_zero_of_not_linearIndependent ℚ (b := bb tM) h
  rw [discr_bb] at this
  norm_num at this

end Special

end DiscrM

open DiscrM

/-- The family `bb tM` as elements of the ring of integers. -/
noncomputable def bZ (i : Fin 8) : 𝓞 M := ⟨bb tM i, bbM_isIntegral i⟩

theorem bZ_linearIndependent : LinearIndependent ℤ bZ := by
  have h : LinearIndependent ℤ (bb tM) := linearIndependent_bb.restrict_scalars' ℤ
  exact LinearIndependent.of_comp (IsScalarTower.toAlgHom ℤ (𝓞 M) M).toLinearMap h

theorem bZ_span : ⊤ ≤ Submodule.span ℤ (Set.range bZ) := by
  intro x _
  let f : 𝓞 M →ₗ[ℤ] M := (IsScalarTower.toAlgHom ℤ (𝓞 M) M).toLinearMap
  have hx : (x : M) ∈ Lam tM := mem_Lam_of_isIntegral _ x.isIntegral_coe
  have hmem : (x : M) ∈ (Submodule.span ℤ (Set.range bZ)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact hx
  obtain ⟨y, hy, hyx⟩ := hmem
  have : y = x := RingOfIntegers.coe_injective hyx
  rw [← this]; exact hy

/-- The explicit `ℤ`-basis of the ring of integers of `M = ℚ(⁸√48)`. -/
noncomputable def intBasisM : Module.Basis (Fin 8) ℤ (𝓞 M) :=
  Module.Basis.mk bZ_linearIndependent bZ_span

@[kb "milne2020ant" "v3.08, Rem. 8.40(c), p. 150"]
theorem discr_M : NumberField.discr M = -(2 ^ 24 * 3 ^ 7) := by
  apply (algebraMap ℤ ℚ).injective_int
  rw [← NumberField.discr_eq_discr _ intBasisM,
    ← Algebra.discr_localizationLocalization ℤ ℤ⁰ M intBasisM]
  have : (Module.Basis.localizationLocalization ℚ ℤ⁰ M intBasisM : Fin 8 → M) = bb tM := by
    ext i
    simp [Module.Basis.localizationLocalization_apply, intBasisM, bZ]
    rfl
  rw [this, discr_bb]
  norm_num

end NumberFieldKB.MilneANT.Rem840c
