import NumberFieldKB.MilneCFT.Intro.ExercisesProofs
import NumberFieldKB.MilneCFT.Ch5RayClassOrder
import NumberFieldKB.MilneANT.Ch2Examples

/-!
# Proof of Milne, *CFT*, Introduction, Example 0.6 / Exercise 0.14

For `F` quadratic with `s² = 6`: (1) `h(F) = 1` (`𝓞F = ℤ[√6]`, Minkowski bound `< 3`, and the only ideal of norm `2` is
`(2 + √6)`); (2) no unit has norm `-1` (mod `3`), so the narrow class number is `2h = 2`
(`example_1_8b_quadratic`); (3) `E = F(√-2, √-3)` is unramified over `F` at all finite primes (the different contains
`2√-2` and `√-3`, hence `8` and `3`) and, being totally complex, ramified at both real places of `F`.
-/

open NumberField IsDedekindDomain Module NumberFieldKB.HilbertClassField NumberFieldKB.Chebotarev
open NumberFieldKB.MilneANT
open scoped nonZeroDivisors

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace NumberFieldKB.MilneCFT.Q6

variable {F : Type} [Field F] [NumberField F]

theorem six_not_sq (q : ℚ) : q ^ 2 ≠ 6 := by
  intro h
  have h1 : IsSquare ((6 : ℕ) : ℚ) := ⟨q, by push_cast; rw [← h]; ring⟩
  obtain ⟨r, hr⟩ := (Rat.isSquare_natCast_iff.1 h1)
  have : r < 3 := by nlinarith
  interval_cases r <;> omega

theorem li {s : F} (hs : s ^ 2 = 6) : LinearIndependent ℚ ![(1 : F), s] := by
  rw [LinearIndependent.pair_iff]
  intro x y h
  simp only [Algebra.smul_def, mul_one] at h
  by_cases hy : y = 0
  · subst hy
    simp at h
    exact ⟨h, rfl⟩
  · exfalso
    apply six_not_sq (-x / y)
    have hy' : algebraMap ℚ F y ≠ 0 := by simpa using hy
    have hsq : algebraMap ℚ F (-x / y) = s := by
      rw [map_div₀, map_neg, div_eq_iff hy']
      linear_combination (-1 : F) * h
    apply (algebraMap ℚ F).injective
    rw [map_pow, hsq, hs]
    simp

/-- The basis `1, s`. -/
def B6 (hF : finrank ℚ F = 2) {s : F} (hs : s ^ 2 = 6) : Basis (Fin 2) ℚ F :=
  basisOfLinearIndependentOfCardEqFinrank (li hs) (by rw [Fintype.card_fin, hF])

theorem B6_zero (hF : finrank ℚ F = 2) {s : F} (hs : s ^ 2 = 6) : B6 hF hs 0 = 1 := by
  simp [B6]

theorem B6_one (hF : finrank ℚ F = 2) {s : F} (hs : s ^ 2 = 6) : B6 hF hs 1 = s := by
  simp [B6]

theorem coord (hF : finrank ℚ F = 2) {s : F} (hs : s ^ 2 = 6) (f : F) :
    ∃ x y : ℚ, f = algebraMap ℚ F x + algebraMap ℚ F y * s := by
  refine ⟨(B6 hF hs).repr f 0, (B6 hF hs).repr f 1, ?_⟩
  have := (B6 hF hs).sum_repr f
  rw [Fin.sum_univ_two, B6_zero, B6_one] at this
  simpa [Algebra.smul_def] using this.symm

theorem coord_unique {s : F} (hs : s ^ 2 = 6) {x y x' y' : ℚ}
    (h : algebraMap ℚ F x + algebraMap ℚ F y * s = algebraMap ℚ F x' + algebraMap ℚ F y' * s) :
    x = x' ∧ y = y' := by
  have hli := li (F := F) hs
  rw [LinearIndependent.pair_iff] at hli
  have := hli (x - x') (y - y') (by
    simp only [Algebra.smul_def, map_sub, mul_one]
    linear_combination h)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- No element of `F` squares to a negative rational. -/
theorem no_neg_sq (hF : finrank ℚ F = 2) {s : F} (hs : s ^ 2 = 6) (f : F) (c : ℚ) (hc : c < 0)
    (h : f ^ 2 = algebraMap ℚ F c) : False := by
  obtain ⟨x, y, rfl⟩ := coord hF hs f
  have e : algebraMap ℚ F (x ^ 2 + 6 * y ^ 2) + algebraMap ℚ F (2 * x * y) * s =
      algebraMap ℚ F c + algebraMap ℚ F 0 * s := by
    simp only [map_add, map_mul, map_pow, map_ofNat, map_zero, zero_mul, add_zero]
    linear_combination h - (algebraMap ℚ F y) ^ 2 * hs
  have := (coord_unique hs e).1
  nlinarith [sq_nonneg x, sq_nonneg y]

theorem norm_coord (hF : finrank ℚ F = 2) {s : F} (hs : s ^ 2 = 6) (a b : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ F a + algebraMap ℚ F b * s) = a ^ 2 - 6 * b ^ 2 := by
  set B := B6 hF hs with hB
  have hB0 : B 0 = 1 := B6_zero hF hs
  have hB1 : B 1 = s := B6_one hF hs
  have hs' : s * s = algebraMap ℚ F 6 := by rw [← sq, hs]; simp
  rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  have e0 : (algebraMap ℚ F a + algebraMap ℚ F b * s) * B 0 = a • B 0 + b • B 1 := by
    rw [hB0, hB1]; simp [Algebra.smul_def]
  have e1 : (algebraMap ℚ F a + algebraMap ℚ F b * s) * B 1 = (6 * b) • B 0 + a • B 1 := by
    rw [hB0, hB1]
    simp only [Algebra.smul_def, map_mul, mul_one]
    have : algebraMap ℚ F 6 = 6 := map_ofNat _ 6
    linear_combination (algebraMap ℚ F b) * hs - (algebraMap ℚ F b) * this
  rw [e0, e1]
  simp
  ring

theorem real_places (hF : finrank ℚ F = 2) {s : F} (hs : s ^ 2 = 6) : ∀ v : InfinitePlace F, v.IsReal := by
  intro v
  rw [← InfinitePlace.mk_embedding v, InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
  set φ := InfinitePlace.embedding v
  ext f
  obtain ⟨x, y, rfl⟩ := coord hF hs f
  have hz : (φ s) ^ 2 = 6 := by rw [← map_pow, hs]; exact map_ofNat φ 6
  have hz' : (starRingEnd ℂ) (φ s) = φ s := by
    rw [Complex.conj_eq_iff_im]
    have h1 : (φ s).re * (φ s).re - (φ s).im * (φ s).im = 6 := by
      have := congrArg Complex.re hz
      simpa [pow_two] using this
    have h2 : (φ s).re * (φ s).im + (φ s).im * (φ s).re = 0 := by
      have := congrArg Complex.im hz
      simpa [pow_two] using this
    by_contra hne
    have hre : (φ s).re = 0 := by
      have : (φ s).im * (2 * (φ s).re) = 0 := by linarith
      exact by simpa [hne] using this
    nlinarith
  simp [map_add, map_mul, hz']

section Integers

variable (hF : finrank ℚ F = 2) (S : 𝓞 F) (hS : S ^ 2 = 6)

include hS in
theorem sK : (S : F) ^ 2 = 6 := by
  have := congrArg (algebraMap (𝓞 F) F) hS
  simpa [map_ofNat] using this

include hF hS in
theorem intcoord (x : 𝓞 F) : ∃ a b : ℤ, x = a + b * S := by
  have hsq : Squarefree (6 : ℤ) := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) by norm_num, Int.squarefree_natCast]
    have h23 : Squarefree (2 * 3 : ℕ) :=
      Nat.squarefree_mul_iff.2 ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
    simpa using h23
  have hSK : (S : F) ^ 2 = ((6 : ℤ) : F) := by rw [sK S hS]; norm_num
  have := (NumberFieldKB.MilneANT.example_2_41 F hF 6 hsq (by norm_num) (S : F) hSK).1
    (by norm_num) (x : F)
  obtain ⟨a, b, hab⟩ := this.1 x.2
  refine ⟨a, b, ?_⟩
  apply RingOfIntegers.coe_injective
  simpa using hab

include hF hS in
theorem norm_int (a b : ℤ) :
    Algebra.norm ℚ (((a : 𝓞 F) + b * S : 𝓞 F) : F) = ((a ^ 2 - 6 * b ^ 2 : ℤ) : ℚ) := by
  have : (((a : 𝓞 F) + b * S : 𝓞 F) : F) = algebraMap ℚ F (a : ℚ) + algebraMap ℚ F (b : ℚ) * (S : F) := by
    simp
  rw [this, norm_coord hF (sK S hS)]
  push_cast
  ring

include hF hS in
/-- Every unit of `𝓞F` has norm `1` (norm `-1` is impossible modulo `3`). -/
theorem unit_norm (u : (𝓞 F)ˣ) : Algebra.norm ℚ ((u : 𝓞 F) : F) = 1 := by
  obtain ⟨a, b, hab⟩ := intcoord hF S hS (u : 𝓞 F)
  obtain ⟨a', b', hab'⟩ := intcoord hF S hS ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  have h1 : Algebra.norm ℚ ((u : 𝓞 F) : F) = ((a ^ 2 - 6 * b ^ 2 : ℤ) : ℚ) := by
    rw [← norm_int hF S hS, ← hab]
  have h2 : Algebra.norm ℚ (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = ((a' ^ 2 - 6 * b' ^ 2 : ℤ) : ℚ) := by
    rw [← norm_int hF S hS, ← hab']
  have h3 : Algebra.norm ℚ ((u : 𝓞 F) : F) * Algebra.norm ℚ (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    rw [← map_mul]
    have : ((u : 𝓞 F) : F) * (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
      simp
    rw [this, map_one]
  rw [h1, h2] at h3
  have h4 : (a ^ 2 - 6 * b ^ 2) * (a' ^ 2 - 6 * b' ^ 2) = 1 := by exact_mod_cast h3
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h4 with h | h
  · rw [h1, h]; simp
  · exfalso
    have h3' : a ^ 2 % 3 = 2 := by omega
    rcases (by omega : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2) with h | h | h <;>
      simp [pow_two, Int.mul_emod, h] at h3'

include hF hS in
theorem discr_rel : ∃ d : ℤ, d ≠ 0 ∧ d ^ 2 * discr F = 24 := by
  have hrk : Module.finrank ℤ (𝓞 F) = 2 := by rw [RingOfIntegers.rank, hF]
  let b : Module.Basis (Fin 2) ℤ (𝓞 F) := Module.finBasisOfFinrankEq ℤ (𝓞 F) hrk
  let v : Fin 2 → 𝓞 F := ![1, S]
  have h1 : Algebra.discr ℤ v = (b.toMatrix v).det ^ 2 * discr F := by
    have := Algebra.discr_of_matrix_vecMul b (b.toMatrix v)
    rw [Module.Basis.toMatrix_map_vecMul] at this
    rw [this, discr_eq_discr F b]
  have h2 : ((Algebra.discr ℤ v : ℤ) : ℚ) = Algebra.discr ℚ (fun i : Fin 2 => (v i : F)) := by
    rw [Algebra.discr_def, Algebra.discr_def, ← eq_intCast (Int.castRingHom ℚ), RingHom.map_det]
    congr 1
    ext i j
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.coe_trace_int]
  have h3 : Algebra.discr ℚ (fun i : Fin 2 => (v i : F)) = 24 := by
    have hsK := sK S hS
    have ht : Algebra.trace ℚ F (S : F) = 0 :=
      trace_eq_zero_of_sq (S : F) 6 (by rw [hsK]; simp) six_not_sq
    have t1 : Algebra.trace ℚ F (algebraMap ℚ F 1) = 2 := by
      rw [Algebra.trace_algebraMap, hF]; simp
    have t5 : Algebra.trace ℚ F (algebraMap ℚ F 6) = 12 := by
      rw [Algebra.trace_algebraMap, hF]; simp; norm_num
    have e00 : ((v 0 : 𝓞 F) : F) * ((v 0 : 𝓞 F) : F) = algebraMap ℚ F 1 := by simp [v]
    have e01 : ((v 0 : 𝓞 F) : F) * ((v 1 : 𝓞 F) : F) = (S : F) := by simp [v]
    have e10 : ((v 1 : 𝓞 F) : F) * ((v 0 : 𝓞 F) : F) = (S : F) := by simp [v]
    have e11 : ((v 1 : 𝓞 F) : F) * ((v 1 : 𝓞 F) : F) = algebraMap ℚ F 6 := by
      simp only [v]
      simp
      rw [← sq, hsK]
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rw [e00, e01, e10, e11, t1, t5, ht]
    norm_num
  refine ⟨(b.toMatrix v).det, ?_, ?_⟩
  · intro h0
    rw [h0] at h1
    have : ((Algebra.discr ℤ v : ℤ) : ℚ) = 24 := by rw [h2, h3]
    rw [h1] at this
    simp at this
  · have : ((Algebra.discr ℤ v : ℤ) : ℚ) = 24 := by rw [h2, h3]
    rw [h1] at this
    exact_mod_cast this

include hF hS in
/-- The only ideal of norm `2` is `(2 + √6)`. -/
theorem norm2_eq (I : Ideal (𝓞 F)) (hI : Ideal.absNorm I = 2) : I = Ideal.span {2 + S} := by
  have hne : I ≠ ⊤ := by
    intro h; rw [h, Ideal.absNorm_top] at hI; norm_num at hI
  have h1 : (1 : 𝓞 F) ∉ I := fun h => hne ((Ideal.eq_top_iff_one I).2 h)
  have h2 : (2 : 𝓞 F) ∈ I := by
    have := Ideal.absNorm_mem I
    rw [hI] at this
    simpa using this
  have hc : Nat.card (𝓞 F ⧸ I) = 2 := by
    rw [← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.1 hc
  have hall : ∀ q : 𝓞 F ⧸ I, q = x ∨ q = y := fun q => by
    have : q ∈ ({x, y} : Set (𝓞 F ⧸ I)) := by rw [hset]; trivial
    simpa using this
  have hz : (0 : 𝓞 F ⧸ I) ≠ 1 := by
    intro h
    apply h1
    exact (Ideal.Quotient.eq_zero_iff_mem).1 h.symm
  have ht : Ideal.Quotient.mk I S = 0 ∨ Ideal.Quotient.mk I S = 1 := by
    have a := hall (Ideal.Quotient.mk I S)
    have b := hall 0
    have c := hall 1
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> aesop
  have h6 : Ideal.Quotient.mk I 6 = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have : (6 : 𝓞 F) = 3 * 2 := by norm_num
    rw [this]
    exact Ideal.mul_mem_left _ _ h2
  have hsq : (Ideal.Quotient.mk I S) ^ 2 = 0 := by
    rw [← map_pow, hS, h6]
  have ht0 : Ideal.Quotient.mk I S = 0 := by
    rcases ht with h | h
    · exact h
    · rw [h, one_pow] at hsq; exact absurd hsq.symm hz
  have hsI : S ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 ht0
  apply le_antisymm
  · intro z hz
    obtain ⟨a, b, rfl⟩ := intcoord hF S hS z
    have haI : ((a : ℤ) : 𝓞 F) ∈ I := by
      have : ((a : ℤ) : 𝓞 F) = ((a : 𝓞 F) + b * S) - b * S := by ring
      rw [this]
      exact I.sub_mem hz (I.mul_mem_left _ hsI)
    have heven : Even a := by
      rcases Int.even_or_odd a with he | ⟨k, hk⟩
      · exact he
      · exfalso
        apply h1
        have e2 : (1 : 𝓞 F) = (a : 𝓞 F) - (k : 𝓞 F) * 2 := by
          have : (a : 𝓞 F) = 2 * k + 1 := by exact_mod_cast hk
          rw [this]; ring
        rw [e2]
        exact I.sub_mem haI (I.mul_mem_left _ h2)
    obtain ⟨k, hk⟩ := heven
    rw [Ideal.mem_span_singleton]
    refine ⟨((3 * b - 2 * k : ℤ) : 𝓞 F) + ((k - b : ℤ) : 𝓞 F) * S, ?_⟩
    have ha : (a : 𝓞 F) = 2 * k := by exact_mod_cast (by omega : a = 2 * k)
    rw [ha]
    push_cast
    linear_combination (-((k : 𝓞 F) - b)) * hS
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact I.add_mem h2 hsI

end Integers

section ClassNumber

variable (hF : finrank ℚ F = 2) (S : 𝓞 F) (hS : S ^ 2 = 6)

include hF hS in
theorem classNumber_eq_one : classNumber F = 1 := by
  have hr := real_places hF (sK S hS)
  obtain ⟨d, hd0, hd⟩ := discr_rel hF S hS
  have hd1 : (1 : ℤ) ≤ d ^ 2 := by nlinarith [sq_pos_of_ne_zero hd0]
  have hDpos : 0 ≤ discr F := by
    by_contra h
    have h' := lt_of_not_ge h
    nlinarith
  have hDle : discr F ≤ 24 := by nlinarith
  have h0 : InfinitePlace.nrComplexPlaces F = 0 := by
    classical
    apply Fintype.card_eq_zero_iff.2
    exact ⟨fun ⟨w, hw⟩ => InfinitePlace.not_isReal_iff_isComplex.2 hw (hr w)⟩
  have hbound : ∀ I : (Ideal (𝓞 F))⁰, ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤
      (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces F *
        ((finrank ℚ F).factorial / (finrank ℚ F : ℝ) ^ finrank ℚ F * Real.sqrt |(discr F : ℝ)|)) →
      Ideal.absNorm (I : Ideal (𝓞 F)) < 3 := by
    intro I hle
    rw [h0, hF] at hle
    have hr5 : Real.sqrt |(discr F : ℝ)| < 5 := by
      rw [Real.sqrt_lt' (by norm_num)]
      have h24 : (discr F : ℝ) ≤ 24 := by exact_mod_cast hDle
      have h00 : (0 : ℝ) ≤ discr F := by exact_mod_cast hDpos
      rw [abs_of_nonneg h00]
      norm_num; linarith
    have : (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) < 3 := by
      refine lt_of_le_of_lt hle ?_
      norm_num [Nat.factorial]
      linarith
    exact_mod_cast this
  unfold classNumber
  rw [Fintype.card_eq_one_iff]
  refine ⟨1, fun C => ?_⟩
  obtain ⟨I, hI, hle⟩ := NumberField.exists_ideal_in_class_of_norm_le (K := F) C
  have hlt := hbound I hle
  have hpos := Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors I)
  have : Ideal.absNorm (I : Ideal (𝓞 F)) = 1 ∨ Ideal.absNorm (I : Ideal (𝓞 F)) = 2 := by omega
  rcases this with h | h
  · rw [← hI, ClassGroup.mk0_eq_one_iff, Ideal.absNorm_eq_one_iff.1 h]
    exact top_isPrincipal
  · rw [← hI, ClassGroup.mk0_eq_one_iff, norm2_eq hF S hS _ h]
    exact ⟨⟨2 + S, rfl⟩⟩

end ClassNumber

section Final

variable {s : F} (hF : finrank ℚ F = 2) (hs : s ^ 2 = 6)

theorem exists_S (hs : s ^ 2 = 6) : ∃ S : 𝓞 F, S ^ 2 = 6 ∧ (S : F) = s :=
  ⟨⟨s, NumberFieldKB.MilneANT.isIntegral_of_sq_eq 6 s (by rw [hs]; simp)⟩,
    RingOfIntegers.ext (by exact hs), rfl⟩

include hF hs in
theorem part1 : classNumber F = 1 := by
  obtain ⟨S, hS, -⟩ := exists_S hs
  exact classNumber_eq_one hF S hS

include hF hs in
theorem part2 : Nat.card (RayClassGroup (narrowModulus F)) = 2 := by
  obtain ⟨S, hS, -⟩ := exists_S hs
  have := (example_1_8b_quadratic hF (real_places hF hs)).1 (fun u => unit_norm hF S hS u)
  rw [this, classNumber_eq_one hF S hS]

section Ramification

variable {s : F} (hF : finrank ℚ F = 2) (hs : s ^ 2 = 6)
variable {E : Type} [Field E] [NumberField E] [Algebra F E]

include hF hs in
theorem finite_unramified (hdeg : finrank F E = 2) (a b : E) (ha : a ^ 2 = -2) (hb : b ^ 2 = -3)
    (𝔭 : HeightOneSpectrum (𝓞 F)) : 𝔭 ∈ unramifiedPrimes F E := by
  intro P hP hlo
  haveI := hP
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  rw [Ideal.dvd_iff_le] at hdvd
  have haint : IsIntegral ℤ a := NumberFieldKB.MilneANT.isIntegral_of_sq_eq (-2) a (by rw [ha]; simp)
  let I : 𝓞 E := ⟨a, haint⟩
  have hI : I ^ 2 = -2 := RingOfIntegers.ext (by push_cast; exact ha)
  have hFa : ∀ f : F, algebraMap F E f ≠ (I : E) := by
    intro f hf
    have hf' : algebraMap F E f = a := hf
    refine no_neg_sq hF hs f (-2) (by norm_num) ?_
    have h2 : f ^ 2 = -2 := (algebraMap F E).injective (by rw [map_pow, hf', ha, map_neg, map_ofNat])
    rw [h2]; simp
  have h1 := mem_differentIdeal_of_quad hdeg I 0 2 (by push_cast; linear_combination hI) hFa
  have hφ : ((1 + b) / 2) ^ 2 + ((-1 : ℤ) : E) * ((1 + b) / 2) + ((1 : ℤ) : E) = 0 := by
    push_cast
    linear_combination (1 / 4 : E) * hb
  let Φ : 𝓞 E := ⟨(1 + b) / 2, isIntegral_of_quad _ (-1) 1 hφ⟩
  have hΦ : Φ ^ 2 + ((-1 : ℤ) : 𝓞 E) * Φ + ((1 : ℤ) : 𝓞 E) = 0 := RingOfIntegers.ext (by
    have h := hφ
    push_cast at h ⊢
    exact h)
  have hFΦ : ∀ f : F, algebraMap F E f ≠ (Φ : E) := by
    intro f hf
    have hf' : algebraMap F E f = (1 + b) / 2 := hf
    refine no_neg_sq hF hs (2 * f - 1) (-3) (by norm_num) ?_
    apply (algebraMap F E).injective
    rw [map_pow, map_sub, map_mul, hf']
    simp only [map_ofNat, map_one, map_neg]
    linear_combination hb
  have h2 := mem_differentIdeal_of_quad hdeg Φ (-1) 1 hΦ hFΦ
  have h1P := hdvd h1
  have h2P := hdvd h2
  have eight : (8 : 𝓞 E) ∈ P := by
    have : (8 : 𝓞 E) = -((2 * I + ((0 : ℤ) : 𝓞 E)) * (2 * I + ((0 : ℤ) : 𝓞 E))) := by
      push_cast; linear_combination (4 : 𝓞 E) * hI
    rw [this]
    exact P.neg_mem (P.mul_mem_left _ h1P)
  have three : (3 : 𝓞 E) ∈ P := by
    have : (3 : 𝓞 E) = -((2 * Φ + ((-1 : ℤ) : 𝓞 E)) * (2 * Φ + ((-1 : ℤ) : 𝓞 E))) := by
      push_cast; linear_combination (4 : 𝓞 E) * hΦ
    rw [this]
    exact P.neg_mem (P.mul_mem_left _ h2P)
  have one : (1 : 𝓞 E) ∈ P := by
    have : (1 : 𝓞 E) = 3 * 3 - 8 := by norm_num
    rw [this]
    exact P.sub_mem (P.mul_mem_left _ three) eight
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2 one)

include hF hs in
theorem infinite_ramified (hdeg : finrank F E = 2) (a : E) (ha : a ^ 2 = -2) (w : InfinitePlace F) :
    InfinitePlace.RamifiesIn E w := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  refine ⟨real_places hF hs w, ?_⟩
  obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (K := E) w
  refine ⟨w', hw', ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hreal
  have h := (InfinitePlace.embedding_of_isReal hreal).map_pow a 2
  have h5 : InfinitePlace.embedding_of_isReal hreal (2 : E) = 2 := map_ofNat _ 2
  rw [ha, map_neg, h5] at h
  have : (0 : ℝ) ≤ (InfinitePlace.embedding_of_isReal hreal a) ^ 2 := sq_nonneg _
  linarith

end Ramification

end Final

end NumberFieldKB.MilneCFT.Q6

namespace NumberFieldKB.MilneCFT

/-- **Example 0.6 / Exercise 0.14** (proved; Milne, *CFT*, Introduction): for `F = ℚ[√6]`, `𝓞F = ℤ[√6]` (Example 2.41)
and the Minkowski bound `√24 / 2 < 3` leaves only ideals of norm `1` and `2`; the only ideal of norm `2` is
`(2 + √6)` (`Q6.norm2_eq`), so `h(F) = 1` (`Q6.classNumber_eq_one`). Every unit has norm `+1`, since `a² - 6b² = -1` is
impossible modulo `3` (`Q6.unit_norm`), so by Ch. V Example 1.8(b) (`example_1_8b_quadratic`) the narrow class number is
`2h = 2`. For `E = F(√-2, √-3)`, the different of `E/F` contains `2√-2` and `√-3` (each generates `E/F` since
`F` is real and so contains neither square root, `Q6.no_neg_sq`), hence `8` and `3` and so `1`: `E/F` is unramified at all finite
primes (`Q6.finite_unramified`); `E` is totally complex while `F` is totally real, so both real places of `F` ramify
(`Q6.infinite_ramified`). -/
@[kb "milne2020cft" "Introduction, Example 0.6 and Exercise 0.14"]
theorem example06 : Example06 where
  classNumber_eq F _ _ hF hs := by
    obtain ⟨s, hs⟩ := hs
    exact Q6.part1 hF hs
  narrow_card F _ _ hF hs := by
    obtain ⟨s, hs⟩ := hs
    exact Q6.part2 hF hs
  unramified F E _ _ _ _ _ hF hs hdeg hab := by
    obtain ⟨s, hs⟩ := hs
    obtain ⟨a, b, ha, hb⟩ := hab
    exact ⟨fun v => Q6.finite_unramified hF hs hdeg a b ha hb v, fun w => Q6.infinite_ramified hF hs hdeg a ha w⟩

end NumberFieldKB.MilneCFT
