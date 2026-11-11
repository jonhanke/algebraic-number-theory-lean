import NumberFieldKB.MilneCFT.Intro.Examples
import NumberFieldKB.MilneCFT.GlobalUnconditional
import NumberFieldKB.MilneCFT.Ch5Complements
import NumberFieldKB.MilneANT.Ch8Examples
import NumberFieldKB.MilneCFT.Intro.Theorems
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real

/-!
# Proofs of Milne, *CFT*, Introduction, Exercises 0.12 and 0.15

* Exercise 0.15: for `L` Galois of degree `4` over `ℚ` containing `i` and `√5`, the family `1, i, √5, i√5` is a basis
  (the trace form is diagonal), so an automorphism is determined by its action on `i` and `√5`; hence only `2` and `5`
  ramify (an inertia element sends `i ↦ ±i`, `√5 ↦ ±√5`, and a sign change puts `2i` or `2√5` in the prime), `2` and `5`
  do ramify (`2 = -i (1+i)^2`, `5 = (√5)^2`), and `L` embeds into `ℚ(ζ₂₀)` (`i = ζ^5`, `√5 = 1 + 2(ζ^4 + ζ^16)`), whose
  Artin map gives the surjection `C_{(20)∞} → Gal(L/ℚ)` by restriction.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped IsMulCommutative

set_option linter.style.haveILetI false

noncomputable section

namespace NumberFieldKB.MilneCFT

section BiquadraticBasis

variable {L : Type} [Field L] [NumberField L] (i b : L)

/-- The trace of a square root of a rational non-square vanishes. -/
theorem trace_eq_zero_of_sq (x : L) (c : ℚ) (hx : x ^ 2 = algebraMap ℚ L c) (hc : ∀ q : ℚ, q ^ 2 ≠ c) :
    Algebra.trace ℚ L x = 0 := by
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℚ) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hc
  have hmin : minpoly ℚ x = Polynomial.X ^ 2 - Polynomial.C c :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hx]) (Polynomial.monic_X_pow_sub_C c two_ne_zero)).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin]
  have : (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℚ).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff, Polynomial.natDegree_X_pow_sub_C]
    simp [Polynomial.coeff_X_pow]
  rw [this]; simp

theorem five_not_sq (q : ℚ) : q ^ 2 ≠ 5 := by
  intro h
  have h1 : IsSquare ((5 : ℕ) : ℚ) := ⟨q, by push_cast; rw [← h]; ring⟩
  obtain ⟨r, hr⟩ := (Rat.isSquare_natCast_iff.1 h1)
  have : r < 3 := by nlinarith
  interval_cases r <;> omega

theorem neg_not_sq (c : ℚ) (hc : c < 0) (q : ℚ) : q ^ 2 ≠ c := by
  intro h; nlinarith [sq_nonneg q]

variable {i b}

/-- The family `1, i, b, i b` is `ℚ`-linearly independent when `i² = -1`, `b² = 5` in a number field
(the trace form is diagonal in it). -/
theorem linearIndependent_biquad' (hi : i ^ 2 = -1) (hb : b ^ 2 = 5) :
    LinearIndependent ℚ ![1, i, b, i * b] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Algebra.smul_def] at hg
  set a0 := algebraMap ℚ L (g 0) with ha0
  set a1 := algebraMap ℚ L (g 1) with ha1
  set a2 := algebraMap ℚ L (g 2) with ha2
  set a3 := algebraMap ℚ L (g 3) with ha3
  set X := a0 * 1 + a1 * i + a2 * b + a3 * (i * b) with hX
  have hX0 : X = 0 := hg
  set n : ℚ := (Module.finrank ℚ L : ℚ) with hn
  have hn0 : n ≠ 0 := by
    rw [hn]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := L)).ne'
  have tq : ∀ (q : ℚ) (x : L), Algebra.trace ℚ L (algebraMap ℚ L q * x) = q * Algebra.trace ℚ L x := by
    intro q x; rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have t1 : Algebra.trace ℚ L 1 = n := by
    have := Algebra.trace_algebraMap (R := ℚ) (S := L) 1
    simpa using this
  have ti : Algebra.trace ℚ L i = 0 :=
    trace_eq_zero_of_sq i (-1) (by simpa using hi) (neg_not_sq _ (by norm_num))
  have tb : Algebra.trace ℚ L b = 0 := trace_eq_zero_of_sq b 5 (by simpa using hb) five_not_sq
  have tib : Algebra.trace ℚ L (i * b) = 0 :=
    trace_eq_zero_of_sq (i * b) (-5) (by rw [mul_pow, hi, hb]; simp) (neg_not_sq _ (by norm_num))
  have e0 : Algebra.trace ℚ L X = n * g 0 := by
    rw [hX, map_add, map_add, map_add, tq, tq, tq, tq, t1, ti, tb, tib]; ring
  have e1 : Algebra.trace ℚ L (i * X) = -(n * g 1) := by
    have : i * X = algebraMap ℚ L (-g 1) * 1 + algebraMap ℚ L (g 0) * i + algebraMap ℚ L (-g 3) * b +
        algebraMap ℚ L (g 2) * (i * b) := by
      simp only [map_neg, ha0, ha1, ha2, ha3, hX]
      linear_combination (algebraMap ℚ L (g 1) + algebraMap ℚ L (g 3) * b) * hi
    rw [this, map_add, map_add, map_add, tq, tq, tq, tq, t1, ti, tb, tib]; ring
  have e2 : Algebra.trace ℚ L (b * X) = n * (5 * g 2) := by
    have : b * X = algebraMap ℚ L (5 * g 2) * 1 + algebraMap ℚ L (5 * g 3) * i + algebraMap ℚ L (g 0) * b +
        algebraMap ℚ L (g 1) * (i * b) := by
      simp only [map_mul, map_ofNat, ha0, ha1, ha2, ha3, hX]
      linear_combination (algebraMap ℚ L (g 2) + algebraMap ℚ L (g 3) * i) * hb
    rw [this, map_add, map_add, map_add, tq, tq, tq, tq, t1, ti, tb, tib]; ring
  have e3 : Algebra.trace ℚ L (i * b * X) = -(n * (5 * g 3)) := by
    have : i * b * X = algebraMap ℚ L (-(5 * g 3)) * 1 + algebraMap ℚ L (5 * g 2) * i +
        algebraMap ℚ L (-g 1) * b + algebraMap ℚ L (g 0) * (i * b) := by
      simp only [map_mul, map_neg, map_ofNat, ha0, ha1, ha2, ha3, hX]
      linear_combination (algebraMap ℚ L (g 1) * b + algebraMap ℚ L (g 3) * b ^ 2) * hi +
        (algebraMap ℚ L (g 2) * i - algebraMap ℚ L (g 3)) * hb
    rw [this, map_add, map_add, map_add, tq, tq, tq, tq, t1, ti, tb, tib]; ring
  rw [hX0, mul_zero, map_zero] at e1 e2 e3
  rw [hX0, map_zero] at e0
  have z0 : g 0 = 0 := (mul_eq_zero.1 e0.symm).resolve_left hn0
  have z1 : g 1 = 0 := (mul_eq_zero.1 (neg_eq_zero.1 e1.symm)).resolve_left hn0
  have z2 : g 2 = 0 := by
    have := (mul_eq_zero.1 e2.symm).resolve_left hn0
    linarith
  have z3 : g 3 = 0 := by
    have := (mul_eq_zero.1 (neg_eq_zero.1 e3.symm)).resolve_left hn0
    linarith
  intro j
  fin_cases j
  · exact z0
  · exact z1
  · exact z2
  · exact z3

theorem linearIndependent_biquad (hi : i ^ 2 = -1) (hb : b ^ 2 = 5) (_hL : Module.finrank ℚ L = 4) :
    LinearIndependent ℚ ![1, i, b, i * b] :=
  linearIndependent_biquad' hi hb

/-- A field of degree `2` over `ℚ` has no element with `u² = -1` together with an element with `v² = 5`. -/
theorem not_biquad_of_finrank_two {F : Type} [Field F] [NumberField F] (hF : Module.finrank ℚ F = 2) (u v : F)
    (hu : u ^ 2 = -1) (hv : v ^ 2 = 5) : False := by
  have := (linearIndependent_biquad' hu hv).fintype_card_le_finrank
  simp [hF] at this

/-- `ℚ(√-5)` contains neither `i` nor `√5`. -/
theorem no_sqrt_in_quadratic {F : Type} [Field F] [NumberField F] (hF : Module.finrank ℚ F = 2) (s : F)
    (hs : s ^ 2 = -5) (r : ℚ) (hr : r = -1 ∨ r = 5) (f : F) (hf : f ^ 2 = algebraMap ℚ F r) : False := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    rcases hr with rfl | rfl <;> simp at hf
  rcases hr with rfl | rfl
  · refine not_biquad_of_finrank_two hF f (s / f) (by simpa using hf) ?_
    rw [div_pow, hs]; have : f ^ 2 = -1 := by simpa using hf
    rw [this]; norm_num
  · refine not_biquad_of_finrank_two hF (s / f) f ?_ (by simpa using hf)
    rw [div_pow, hs]; have : f ^ 2 = 5 := by simpa using hf
    rw [this]; norm_num

variable (i b) in
/-- The basis `1, i, b, i b` of a degree-`4` field. -/
def biquadBasis (hi : i ^ 2 = -1) (hb : b ^ 2 = 5) (hL : Module.finrank ℚ L = 4) : Module.Basis (Fin 4) ℚ L :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_biquad hi hb hL) (by simp [hL])

theorem biquadBasis_apply (hi : i ^ 2 = -1) (hb : b ^ 2 = 5) (hL : Module.finrank ℚ L = 4) (j : Fin 4) :
    biquadBasis i b hi hb hL j = ![1, i, b, i * b] j := by
  simp [biquadBasis]

/-- Two `ℚ`-algebra maps out of `L` that agree on `i` and `b` are equal. -/
theorem algHom_ext_biquad (hi : i ^ 2 = -1) (hb : b ^ 2 = 5) (hL : Module.finrank ℚ L = 4)
    {M : Type} [Field M] [Algebra ℚ M] (f g : L →ₐ[ℚ] M) (h1 : f i = g i) (h2 : f b = g b) : f = g := by
  apply AlgHom.toLinearMap_injective
  apply (biquadBasis i b hi hb hL).ext
  intro j
  rw [biquadBasis_apply]
  fin_cases j <;> simp [h1, h2]

/-- `ℚ⟮i, b⟯ = L`. -/
theorem adjoin_biquad_eq_top (hi : i ^ 2 = -1) (hb : b ^ 2 = 5) (hL : Module.finrank ℚ L = 4) :
    IntermediateField.adjoin ℚ {i, b} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span ℚ (Set.range (biquadBasis i b hi hb hL)) := by
    rw [(biquadBasis i b hi hb hL).span_eq]; trivial
  have hle : Submodule.span ℚ (Set.range (biquadBasis i b hi hb hL)) ≤
      (IntermediateField.adjoin ℚ {i, b}).toSubalgebra.toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra, biquadBasis_apply]
    have hi' : i ∈ IntermediateField.adjoin ℚ {i, b} := IntermediateField.subset_adjoin _ _ (by simp)
    have hb' : b ∈ IntermediateField.adjoin ℚ {i, b} := IntermediateField.subset_adjoin _ _ (by simp)
    fin_cases j
    · exact one_mem _
    · exact hi'
    · exact hb'
    · exact mul_mem hi' hb'
  exact hle hx

end BiquadraticBasis

section Ramification

open NumberFieldKB.MilneANT NumberFieldKB.HilbertClassField

variable {L : Type} [Field L] [NumberField L] {i b : L}

theorem prime_dvd_aux (p : ℕ) (hp : p.Prime) (d : ℤ) (hd : d = -1 ∨ d = 5) (h : (p : ℤ) ∣ 4 * d) :
    p = 2 ∨ p = 5 := by
  have h20 : (p : ℤ) ∣ 20 := by
    rcases hd with rfl | rfl
    · exact dvd_trans h ⟨-5, by norm_num⟩
    · simpa using h
  have h20' : p ∣ 20 := Int.natCast_dvd_natCast.1 (by exact_mod_cast h20)
  have hle : p ≤ 20 := Nat.le_of_dvd (by norm_num) h20'
  have := hp.two_le
  interval_cases p <;> first | omega | (exfalso; revert h20'; norm_num; done) | (exfalso; exact absurd hp (by norm_num))

/-- An inertia element at a prime away from `10` fixes `i` and `b`. -/
theorem inertia_fixes (hi : i ^ 2 = -1) (hb : b ^ 2 = 5) [IsGalois ℚ L]
    (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : ratPrime v ≠ 2) (h5 : ratPrime v ≠ 5)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] (τ : Gal(L/ℚ))
    (hτ : τ ∈ Q.inertia Gal(L/ℚ)) : τ i = i ∧ τ b = b := by
  have hp : (ratPrime v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have key : ∀ (s : L) (d : ℤ), s ^ 2 = d → (d = -1 ∨ d = 5) → τ s = s := by
    intro s d hs hd
    let S : 𝓞 L := ⟨s, isIntegral_of_sq_eq d s hs⟩
    have hS : S ^ 2 = (d : 𝓞 L) := RingOfIntegers.ext (by push_cast; exact hs)
    have hτs : (τ s - s) * (τ s + s) = 0 := by
      have : (τ s) ^ 2 = d := by rw [← map_pow, hs, map_intCast]
      linear_combination this - hs
    rcases mul_eq_zero.1 hτs with h | h
    · exact sub_eq_zero.1 h
    · exfalso
      have h1 := (Ideal.mem_inertia.1 hτ) S
      have e : τ • S - S = -((2 : 𝓞 L) * S) := RingOfIntegers.ext (by
        show τ s - s = -(2 * s)
        have : τ s = -s := eq_neg_of_add_eq_zero_left h
        rw [this]; ring)
      rw [e] at h1
      have h2S : (2 : 𝓞 L) * S ∈ Q := by simpa using Q.neg_mem h1
      have h4 : ((4 * d : ℤ) : 𝓞 L) ∈ Q := by
        have := Q.pow_mem_of_mem h2S 2 (by norm_num)
        convert this using 1
        push_cast
        rw [mul_pow, hS]
        norm_num
      rcases prime_dvd_aux (ratPrime v) hp d hd ((intCast_mem_iff v Q _).1 h4) with h | h
      · exact h2 h
      · exact h5 h
  exact ⟨key i (-1) (by rw [hi]; simp) (Or.inl rfl), key b 5 (by rw [hb]; simp) (Or.inr rfl)⟩

/-- Primes away from `10` are unramified in `ℚ(i, √5)`. -/
theorem biquad_unramified (hi : i ^ 2 = -1) (hb : b ^ 2 = 5) (hL : Module.finrank ℚ L = 4) [IsGalois ℚ L]
    (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : ratPrime v ≠ 2) (h5 : ratPrime v ≠ 5) :
    v ∈ unramifiedPrimes ℚ L := by
  intro Q hQp hQo
  haveI := hQp
  haveI := hQo
  have hQm : Q.IsMaximal := hQp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have := finite_quotient_of_ne_bot Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  refine Ideal.ramificationIdx_eq_one_iff.mp ?_
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q Gal(L/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) v.asIdeal Q, Subgroup.card_eq_one,
    Subgroup.eq_bot_iff_forall]
  intro τ hτ
  obtain ⟨h1, h2'⟩ := inertia_fixes hi hb v h2 h5 Q τ hτ
  have := algHom_ext_biquad hi hb hL (τ : L →ₐ[ℚ] L) (AlgHom.id ℚ L) h1 h2'
  exact AlgEquiv.ext fun x => congrArg (fun f : L →ₐ[ℚ] L => f x) this

/-- A prime `Q` above `p` with `p ∈ Q^2` shows `p` ramifies. -/
theorem not_unramified_of_mem_sq [IsGalois ℚ L] (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hv : v.asIdeal = Ideal.span {(n : 𝓞 ℚ)})
    (H : ∀ (Q : Ideal (𝓞 L)), Q.IsPrime → Q.LiesOver v.asIdeal → (n : 𝓞 L) ∈ Q ^ 2) :
    v ∉ unramifiedPrimes ℚ L := by
  intro hunr
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) v.asIdeal ⊥
    (by
      rw [Ideal.under_bot]
      exact bot_le)
  haveI : Q.IsPrime := hQp
  haveI : Q.LiesOver v.asIdeal := ⟨hQ.symm⟩
  have hu : Algebra.IsUnramifiedAt (𝓞 ℚ) Q := hunr Q hQp inferInstance
  have h1 : Q.ramificationIdx (𝓞 ℚ) = 1 := Ideal.ramificationIdx_eq_one Q (𝓞 ℚ)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot] at h1
  have hle : v.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 L)) ≤ Q :=
    Ideal.map_le_iff_le_comap.2 (Ideal.LiesOver.over (P := Q) (p := v.asIdeal)).le
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ h1
  rw [hv, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, map_natCast]
  exact H Q inferInstance inferInstance

/-- `2` ramifies in `ℚ(i, √5)`. -/
theorem biquad_ramified_two (hi : i ^ 2 = -1) [IsGalois ℚ L] (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v.asIdeal = Ideal.span {(2 : 𝓞 ℚ)}) : v ∉ unramifiedPrimes ℚ L := by
  refine not_unramified_of_mem_sq v 2 (by simpa using hv) ?_
  intro Q hQp hQo
  haveI := hQp
  let S : 𝓞 L := ⟨i, isIntegral_of_sq_eq (-1) i (by rw [hi]; simp)⟩
  have hS : S ^ 2 = -1 := RingOfIntegers.ext (by push_cast; exact hi)
  have h2Q : (2 : 𝓞 L) ∈ Q := by
    have : (2 : 𝓞 ℚ) ∈ v.asIdeal := by rw [hv]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.over_def Q v.asIdeal, Ideal.mem_comap] at this
    simpa only [map_ofNat] using this
  have hprod : (1 + S) * (1 - S) ∈ Q := by
    have : (1 + S) * (1 - S) = 2 := by linear_combination (-1 : 𝓞 L) * hS
    rw [this]; exact h2Q
  have h1S : 1 + S ∈ Q := by
    rcases hQp.mem_or_mem hprod with h | h
    · exact h
    · have : 1 + S = S * (1 - S) := by linear_combination (1 : 𝓞 L) * hS
      rw [this]; exact Q.mul_mem_left _ h
  have : (2 : 𝓞 L) = (-S) * ((1 + S) * (1 + S)) := by linear_combination (S + 2) * hS
  rw [Nat.cast_ofNat, this, pow_two]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul h1S h1S)

/-- `5` ramifies in `ℚ(i, √5)`. -/
theorem biquad_ramified_five (hb : b ^ 2 = 5) [IsGalois ℚ L] (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v.asIdeal = Ideal.span {(5 : 𝓞 ℚ)}) : v ∉ unramifiedPrimes ℚ L := by
  refine not_unramified_of_mem_sq v 5 (by simpa using hv) ?_
  intro Q hQp hQo
  haveI := hQp
  let S : 𝓞 L := ⟨b, isIntegral_of_sq_eq 5 b (by rw [hb]; simp)⟩
  have hS : S ^ 2 = 5 := RingOfIntegers.ext (by push_cast; exact hb)
  have h5Q : (5 : 𝓞 L) ∈ Q := by
    have : (5 : 𝓞 ℚ) ∈ v.asIdeal := by rw [hv]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.over_def Q v.asIdeal, Ideal.mem_comap] at this
    simpa only [map_ofNat] using this
  have hSQ : S ∈ Q := hQp.mem_of_pow_mem 2 (by rw [hS]; exact h5Q)
  have : ((5 : ℕ) : 𝓞 L) = S * S := by push_cast; linear_combination (-1 : 𝓞 L) * hS
  rw [this, pow_two]
  exact Ideal.mul_mem_mul hSQ hSQ

/-- Part (a) of Exercise 0.15 for `ℚ(i, √5)`. -/
theorem biquad_ramified_iff (hi : i ^ 2 = -1) (hb : b ^ 2 = 5) (hL : Module.finrank ℚ L = 4) [IsGalois ℚ L]
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∉ unramifiedPrimes ℚ L ↔ (v.asIdeal = Ideal.span {(2 : 𝓞 ℚ)} ∨ v.asIdeal = Ideal.span {(5 : 𝓞 ℚ)}) := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    apply h
    refine biquad_unramified hi hb hL v (fun h2 => hcon.1 ?_) (fun h5 => hcon.2 ?_)
    · rw [asIdeal_eq_span_ratPrime v, h2]; simp
    · rw [asIdeal_eq_span_ratPrime v, h5]; simp
  · rintro (h | h)
    · exact biquad_ramified_two hi v h
    · exact biquad_ramified_five hb v h

end Ramification

section ArtinPart

open NumberFieldKB.MilneANT

/-- The minimal polynomial of a square root of a rational splits in any field containing a square root. -/
theorem splits_minpoly_of_sq {L E : Type} [Field L] [Field E] [Algebra ℚ L] [Algebra ℚ E] (s : L) (r : E)
    (c : ℚ) (hs : s ^ 2 = algebraMap ℚ L c) (hr : r ^ 2 = algebraMap ℚ E c) :
    ((minpoly ℚ s).map (algebraMap ℚ E)).Splits := by
  have hdvd : minpoly ℚ s ∣ (Polynomial.X ^ 2 - Polynomial.C c) := minpoly.dvd ℚ s (by simp [hs])
  have hmon : ((Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℚ).map (algebraMap ℚ E)).Monic :=
    (Polynomial.monic_X_pow_sub_C c two_ne_zero).map _
  have hsp : ((Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℚ).map (algebraMap ℚ E)).Splits := by
    have : (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℚ).map (algebraMap ℚ E) =
        (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C (-r)) := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hr, map_pow,
        map_neg]
      ring
    rw [this]
    exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)
  exact hsp.of_dvd hmon.ne_zero (Polynomial.map_dvd _ hdvd)

/-- `ℚ(i, √5)` embeds in any field containing `i` and `√5`. -/
theorem biquad_embeds {L : Type} [Field L] [NumberField L] {i b : L} (hi : i ^ 2 = -1) (hb : b ^ 2 = 5)
    (hL : Module.finrank ℚ L = 4) {E : Type} [Field E] [Algebra ℚ E] (i' b' : E) (hi' : i' ^ 2 = -1)
    (hb' : b' ^ 2 = 5) : Nonempty (L →ₐ[ℚ] E) := by
  have hspl : ∀ s ∈ ({i, b} : Set L), IsIntegral ℚ s ∧ ((minpoly ℚ s).map (algebraMap ℚ E)).Splits := by
    intro s hs
    refine ⟨Algebra.IsIntegral.isIntegral s, ?_⟩
    rcases hs with rfl | hs
    · exact splits_minpoly_of_sq s i' (-1) (by rw [hi]; simp) (by rw [hi']; simp)
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact splits_minpoly_of_sq s b' 5 (by rw [hb]; simp) (by rw [hb']; simp)
  obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_adjoin_splits hspl
    ((Algebra.ofId ℚ E).comp (IntermediateField.botEquiv ℚ L).toAlgHom) (adjoin_biquad_eq_top hi hb hL)
  exact ⟨φ⟩

/-- `ℚ(ζ₂₀)` contains `i` and `√5`. -/
theorem cyc20_roots : ∃ i' b' : CyclotomicField 20 ℚ, i' ^ 2 = -1 ∧ b' ^ 2 = 5 := by
  haveI : NeZero 20 := ⟨by norm_num⟩
  haveI : IsCyclotomicExtension {20} ℚ (CyclotomicField 20 ℚ) := CyclotomicField.isCyclotomicExtension 20 ℚ
  have hζ := IsCyclotomicExtension.zeta_spec 20 ℚ (CyclotomicField 20 ℚ)
  set ζ := IsCyclotomicExtension.zeta 20 ℚ (CyclotomicField 20 ℚ)
  have h10 : IsPrimitiveRoot (ζ ^ 10) 2 := by
    simpa using hζ.pow_of_dvd (by norm_num : 10 ≠ 0) (by norm_num : 10 ∣ 20)
  have hi : (ζ ^ 5) ^ 2 = -1 := by rw [← pow_mul]; exact h10.eq_neg_one_of_two_right
  have h5 : IsPrimitiveRoot (ζ ^ 4) 5 := by
    simpa using hζ.pow_of_dvd (by norm_num : 4 ≠ 0) (by norm_num : 4 ∣ 20)
  obtain ⟨ω, hω5, hωsum⟩ : ∃ ω : CyclotomicField 20 ℚ, ω ^ 5 = 1 ∧ 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
    refine ⟨ζ ^ 4, h5.pow_eq_one, ?_⟩
    have := h5.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    linear_combination this
  exact ⟨ζ ^ 5, 1 + 2 * (ω + ω ^ 4), hi, by linear_combination 4 * hωsum + (8 + 4 * ω ^ 3) * hω5⟩

theorem isMulCommutative_gal_of_finrank_four (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (hL : Module.finrank ℚ L = 4) : IsMulCommutative Gal(L/ℚ) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [IsGalois.card_aut_eq_finrank, hL]; norm_num)

/-- Part (c) of Exercise 0.15 for `ℚ(i, √5)`: the Artin map of `ℚ(ζ₂₀)` restricted to `L`. -/
theorem biquad_artin (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] {i b : L} (hi : i ^ 2 = -1)
    (hb : b ^ 2 = 5) (hL : Module.finrank ℚ L = 4) (m : Modulus ℚ) (h1 : m.finite = Ideal.span {(20 : 𝓞 ℚ)})
    (h2 : m.infinite = {v | v.IsReal}) :
    ∃ ψ : RayClassGroup m →* Gal(L/ℚ), Function.Surjective ψ ∧
      ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ m.finite) (Q : v.asIdeal.primesOver (𝓞 L)),
        ψ (rayClass m v hv) = frobAt ℚ L v Q := by
  haveI : IsAbelianGalois ℚ L := { toIsMulCommutative := isMulCommutative_gal_of_finrank_four L hL }
  haveI : NeZero 20 := ⟨by norm_num⟩
  haveI : IsCyclotomicExtension {20} ℚ (CyclotomicField 20 ℚ) := CyclotomicField.isCyclotomicExtension 20 ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField 20 ℚ) := IsCyclotomicExtension.isAbelianGalois {20} ℚ _
  have hm : m = ratModulus 20 (by norm_num) := by
    obtain ⟨f, fne, inf, ir⟩ := m
    simp only at h1 h2
    subst h1 h2
    rfl
  subst hm
  have hC := example_3_10_cyclotomic 20 (by norm_num) (by norm_num) (CyclotomicField 20 ℚ)
  obtain ⟨i', b', hi', hb'⟩ := cyc20_roots
  obtain ⟨φ⟩ := biquad_embeds hi hb hL i' b' hi' hb'
  letI : Algebra L (CyclotomicField 20 ℚ) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ L (CyclotomicField 20 ℚ) := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  refine ⟨(AlgEquiv.restrictNormalHom L).comp
    (rayClassEquivGal (ratModulus 20 (by norm_num)) (CyclotomicField 20 ℚ) hC).toMonoidHom, ?_, ?_⟩
  · intro y
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (CyclotomicField 20 ℚ) y
    exact ⟨(rayClassEquivGal (ratModulus 20 (by norm_num)) (CyclotomicField 20 ℚ) hC).symm g, by simp⟩
  · intro v hv Q
    have hunrC : v ∈ unramifiedPrimes ℚ (CyclotomicField 20 ℚ) := hC.unramifiedOutside.1 v hv
    have hunrL : v ∈ unramifiedPrimes ℚ L := by
      refine biquad_unramified hi hb hL v (fun h2 => hv ?_) (fun h5 => hv ?_)
      · show v.asIdeal ∣ Ideal.span {(20 : 𝓞 ℚ)}
        rw [asIdeal_eq_span_ratPrime v, h2, Ideal.dvd_span_singleton]
        exact Ideal.mem_span_singleton.2 ⟨10, by norm_num⟩
      · show v.asIdeal ∣ Ideal.span {(20 : 𝓞 ℚ)}
        rw [asIdeal_eq_span_ratPrime v, h5, Ideal.dvd_span_singleton]
        exact Ideal.mem_span_singleton.2 ⟨4, by norm_num⟩
    have hfrob : rayClassEquivGal (ratModulus 20 (by norm_num)) (CyclotomicField 20 ℚ) hC (rayClass _ v hv) =
        artinFrob (CyclotomicField 20 ℚ) v :=
      (rayClassEquivGal_mk _ _ hC _).trans (artinMap_prime _ _ v _ rfl)
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hfrob, ← artinFrob_restrict L _ v hunrC,
      artinFrob_eq L v hunrL Q]

/-- **Exercise 0.15** (proved; Milne, *CFT*, Introduction): for `L = ℚ[√-1, √5]`, (a) only `2` and `5` ramify at the
finite primes (and `∞`, which is not a point of `HeightOneSpectrum`), and (c) for `m = (20)∞` the map `p ↦ (p, L/ℚ)`
defines a surjection `C_m → Gal(L/ℚ)`, i.e. an isomorphism `C_m / H ≅ Gal(L/ℚ)` with `H` its kernel. Proof: `1, i, √5,
i√5` is a `ℚ`-basis of `L` (the trace form is diagonal, `linearIndependent_biquad'`), so an inertia
element, which sends `i ↦ ±i`, `√5 ↦ ±√5` and cannot change a sign at a prime not dividing `10`, is trivial
(`biquad_unramified`); `2 = -i(1+i)^2` and `5 = (√5)^2` show `2` and `5` ramify (`biquad_ramified_iff`). For (c), `L`
embeds into `ℚ(ζ₂₀)` (`i = ζ^5`, `√5 = 1 + 2(ζ^4 + ζ^16)`, `biquad_embeds`), `ℚ(ζ₂₀)` is the class field of
`P_{(20)∞}` (`example_3_10_cyclotomic`), and restriction of its Artin isomorphism to `L` is onto and sends the class
of `p` to the Frobenius (`artinFrob_restrict`). -/
@[kb "milne2020cft" "Introduction, Exercise 0.15"]
theorem exercise015 : Exercise015 where
  ramified L _ _ _ hL hab v := by
    obtain ⟨a, b, ha, hb⟩ := hab
    exact biquad_ramified_iff ha hb hL v
  artin L _ _ _ hL hab m h1 h2 := by
    obtain ⟨a, b, ha, hb⟩ := hab
    exact biquad_artin L ha hb hL m h1 h2

end ArtinPart

section HilbertQ5

open NumberFieldKB.HilbertClassField NumberFieldKB.MilneANT

/-- In a degree-`2` extension, an element outside the base field generates. -/
theorem adjoin_eq_top_of_quad {F E : Type} [Field F] [Field E] [Algebra F E] (hdeg : Module.finrank F E = 2)
    (y : E) (hy : ∀ f : F, algebraMap F E f ≠ y) : Algebra.adjoin F {y} = ⊤ := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hli : LinearIndependent F ![1, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    simp only [Algebra.smul_def, mul_one] at h
    by_cases ht : t = 0
    · subst ht
      simp only [map_zero, zero_mul, add_zero] at h
      exact ⟨(map_eq_zero_iff _ (algebraMap F E).injective).1 h, rfl⟩
    · exfalso
      apply hy (-s / t)
      have ht' : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination (-1 : E) * h
  let bas := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdeg])
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ Submodule.span F (Set.range bas) := by rw [bas.span_eq]; trivial
  have hle : Submodule.span F (Set.range bas) ≤ (Algebra.adjoin F {y}).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule]
    simp only [bas, coe_basisOfLinearIndependentOfCardEqFinrank]
    fin_cases j
    · exact Subalgebra.one_mem _
    · exact Algebra.subset_adjoin (Set.mem_singleton y)
  exact hle hz

/-- For a quadratic extension `E/F` of number fields and an algebraic integer `x ∈ 𝓞 E` outside `F` with
`x² + c x + d = 0`, the element `2x + c` lies in the different. -/
theorem mem_differentIdeal_of_quad {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hdeg : Module.finrank F E = 2) (x : 𝓞 E) (c d : ℤ) (hx : x ^ 2 + (c : 𝓞 E) * x + (d : 𝓞 E) = 0)
    (hxF : ∀ f : F, algebraMap F E f ≠ (x : E)) :
    (2 * x + (c : 𝓞 E)) ∈ differentIdeal (𝓞 F) (𝓞 E) := by
  set p : Polynomial (𝓞 F) :=
    Polynomial.X ^ 2 + Polynomial.C (c : 𝓞 F) * Polynomial.X + Polynomial.C (d : 𝓞 F) with hp
  have hpmon : p.Monic := by rw [hp]; monicity!
  have hpnat : p.natDegree = 2 := by rw [hp]; compute_degree!
  have haeval : Polynomial.aeval x p = 0 := by simp [hp, ← hx]
  have hxint : IsIntegral (𝓞 F) x := ⟨p, hpmon, by simpa [Polynomial.aeval_def] using haeval⟩
  have hdvd : minpoly (𝓞 F) x ∣ p := minpoly.isIntegrallyClosed_dvd hxint haeval
  have hnat : 2 ≤ (minpoly (𝓞 F) x).natDegree := by
    have h1 := minpoly.isIntegrallyClosed_eq_field_fractions F E hxint
    have h2 : 2 ≤ (minpoly F (algebraMap (𝓞 E) E x)).natDegree := by
      haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
      rw [minpoly.two_le_natDegree_iff (Algebra.IsIntegral.isIntegral _)]
      rintro ⟨f, hf⟩
      exact hxF f hf
    rw [h1, (minpoly.monic hxint).natDegree_map] at h2
    exact h2
  have hmin : minpoly (𝓞 F) x = p :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxint) hpmon hdvd (by omega)).symm
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hadj : Algebra.adjoin F {algebraMap (𝓞 E) E x} = ⊤ := adjoin_eq_top_of_quad hdeg _ hxF
  have := aeval_derivative_mem_differentIdeal (𝓞 F) F E x hadj
  rw [hmin] at this
  convert this using 1
  simp [hp]
  exact Or.inl one_add_one_eq_two.symm

theorem isIntegral_of_quad {E : Type} [Field E] (x : E) (c d : ℤ) (h : x ^ 2 + (c : E) * x + (d : E) = 0) :
    IsIntegral ℤ x :=
  ⟨Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X + Polynomial.C d, by monicity!, by
    rw [← Polynomial.aeval_def]
    simpa using h⟩

/-- Every finite prime of `F = ℚ(√-5)` is unramified in a quadratic extension containing `i` and `√5`. -/
theorem quad_unramified {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hF : Module.finrank ℚ F = 2) (s : F) (hs : s ^ 2 = -5) (hdeg : Module.finrank F E = 2) (a b : E)
    (ha : a ^ 2 = 5) (hb : b ^ 2 = -1) (𝔭 : HeightOneSpectrum (𝓞 F)) : 𝔭 ∈ unramifiedPrimes F E := by
  intro P hP hlo
  haveI := hP
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  rw [Ideal.dvd_iff_le] at hdvd
  have hbint : IsIntegral ℤ b := isIntegral_of_sq_eq (-1) b (by rw [hb]; simp)
  let I : 𝓞 E := ⟨b, hbint⟩
  have hI : I ^ 2 = -1 := RingOfIntegers.ext (by push_cast; exact hb)
  have hFb : ∀ f : F, algebraMap F E f ≠ (I : E) := by
    intro f hf
    refine no_sqrt_in_quadratic hF s hs (-1) (Or.inl rfl) f ?_
    apply (algebraMap F E).injective
    have hf' : algebraMap F E f = b := hf
    rw [map_pow, hf', hb]; simp
  have h1 := mem_differentIdeal_of_quad hdeg I 0 1 (by push_cast; linear_combination hI) hFb
  have hφ : ((1 + a) / 2) ^ 2 + ((-1 : ℤ) : E) * ((1 + a) / 2) + ((-1 : ℤ) : E) = 0 := by
    push_cast
    linear_combination (1 / 4 : E) * ha
  let Φ : 𝓞 E := ⟨(1 + a) / 2, isIntegral_of_quad _ (-1) (-1) hφ⟩
  have hΦ : Φ ^ 2 + ((-1 : ℤ) : 𝓞 E) * Φ + ((-1 : ℤ) : 𝓞 E) = 0 := RingOfIntegers.ext (by
    have h := hφ
    push_cast at h ⊢
    exact h)
  have hFΦ : ∀ f : F, algebraMap F E f ≠ (Φ : E) := by
    intro f hf
    have hf' : algebraMap F E f = (1 + a) / 2 := hf
    refine no_sqrt_in_quadratic hF s hs 5 (Or.inr rfl) (2 * f - 1) ?_
    apply (algebraMap F E).injective
    rw [map_pow, map_sub, map_mul, hf']
    simp only [map_ofNat, map_one]
    linear_combination ha
  have h2 := mem_differentIdeal_of_quad hdeg Φ (-1) (-1) hΦ hFΦ
  have h1P := hdvd h1
  have h2P := hdvd h2
  have two : (2 : 𝓞 E) ∈ P := by
    have : (2 : 𝓞 E) = -((2 * I + ((0 : ℤ) : 𝓞 E)) * I) := by
      push_cast; linear_combination (2 : 𝓞 E) * hI
    rw [this]
    exact P.neg_mem (P.mul_mem_right _ h1P)
  have five : (5 : 𝓞 E) ∈ P := by
    have : (5 : 𝓞 E) = (2 * Φ + ((-1 : ℤ) : 𝓞 E)) ^ 2 := by
      push_cast; linear_combination (-4 : 𝓞 E) * hΦ
    rw [this]
    exact P.pow_mem_of_mem h2P 2 (by norm_num)
  have one : (1 : 𝓞 E) ∈ P := by
    have : (1 : 𝓞 E) = 5 - 2 * 2 := by norm_num
    rw [this]
    exact P.sub_mem five (P.mul_mem_left _ two)
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2 one)

/-- `F = ℚ(√-5)` has no real place, so every infinite place is unramified in any extension. -/
theorem quad_unramified_infinite {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (s : F) (hs : s ^ 2 = -5) : IsUnramifiedAtInfinitePlaces F E := by
  refine ⟨fun w => ?_⟩
  rw [InfinitePlace.isUnramified_iff]
  right
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hreal
  have h := (InfinitePlace.embedding_of_isReal hreal).map_pow s 2
  have h5 : InfinitePlace.embedding_of_isReal hreal (5 : F) = 5 := map_ofNat _ 5
  rw [hs, map_neg, h5] at h
  have : (0 : ℝ) ≤ (InfinitePlace.embedding_of_isReal hreal s) ^ 2 := sq_nonneg _
  linarith

theorem commutative_of_finrank_two {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] (hdeg : Module.finrank F E = 2) : ∀ σ τ : Gal(E/F), σ * τ = τ * σ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card Gal(E/F) = 2 := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  haveI := isCyclic_of_prime_card hcard
  exact fun σ τ => (isCyclic_of_prime_card hcard).isMulCommutative.is_comm.comm σ τ

/-- **Exercise 0.12**, assuming `h(ℚ(√-5)) = 2`. -/
theorem exercise012_of_classNumber
    (hcn : ∀ (F : Type) [Field F] [NumberField F], Module.finrank ℚ F = 2 → (∃ s : F, s ^ 2 = -5) →
      classNumber F = 2) : Exercise012 := by
  refine ⟨fun F E _ _ _ _ _ _ hF hs hdeg hab => ?_⟩
  obtain ⟨s, hs⟩ := hs
  obtain ⟨a, b, ha, hb⟩ := hab
  have hunr := quad_unramified hF s hs hdeg a b ha hb
  have hinf : IsUnramifiedAtInfinitePlaces F E := quad_unramified_infinite s hs
  have hcomm := commutative_of_finrank_two hdeg
  obtain ⟨ψ, hψ⟩ :=
    (unramifiedArtinReciprocityInput_of_artin (artinReciprocity F)).exists_artin E hcomm hunr hinf
  exact isHilbertClassField_of_finrank_eq hunr hinf (by rw [hdeg, hcn F hF ⟨s, hs⟩]) ψ hψ

end HilbertQ5

end NumberFieldKB.MilneCFT
