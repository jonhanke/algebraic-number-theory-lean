import NumberFieldKB.MilneCFT.Intro.TakagiProof
import NumberFieldKB.MilneCFT.Intro.ExercisesProofs
import NumberFieldKB.MilneCFT.Intro.Examples
import NumberFieldKB.MilneCFT.Ch5RayClassOrder
import NumberFieldKB.MilneCFT.Ch5IdelesChar
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star

/-!
# Proof of Milne, *CFT*, Introduction, Example 0.7

For distinct odd primes `p_1, ..., p_t` with `p_i^* = (-1)^((p_i-1)/2) p_i` and `K` quadratic with `s^2 = ∏ p_i^*`:
the narrow class group `C^+` has `(C^+ : C^{+2}) ≥ 2^(t-1)`.

*Method (characters).* For each `S ⊆ {1..t-1}` let `a_S = ∏_{i∈S} p_i^*` and `E_S = K(√a_S)`. Then `E_S/K` is
quadratic and unramified at all finite primes (the different contains `√a_S` and `√a_{S^c}`, hence `a_S` and `a_{S^c}`,
which are coprime), so by Artin reciprocity (`artinReciprocity`) it gives a character `χ_S : C^+ → {±1}` with
`χ_S([v]) = 1` iff `v` splits in `E_S`. The `χ_S` are pairwise distinct (Bauer: same split primes means
`K`-isomorphic fields), they kill squares, so they are `2^(t-1)` linearly independent characters of `C^+/C^{+2}`.
-/

open NumberField IsDedekindDomain Module NumberFieldKB.HilbertClassField NumberFieldKB.Chebotarev
open NumberFieldKB.MilneANT Polynomial
open scoped nonZeroDivisors

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace NumberFieldKB.MilneCFT.Ex07

/-! ## Quadratic extensions -/

/-- In a quadratic extension `E/F`, every element is `u + v y` for any `y ∉ F`. -/
theorem quad_span {F E : Type} [Field F] [Field E] [Algebra F E] (hdeg : Module.finrank F E = 2)
    (y : E) (hy : ∀ f : F, algebraMap F E f ≠ y) :
    ∀ z : E, ∃ u v : F, z = algebraMap F E u + algebraMap F E v * y := by
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
  intro z
  have hsum := bas.sum_repr z
  rw [Fin.sum_univ_two] at hsum
  have h0 : bas 0 = 1 := by simp [bas]
  have h1 : bas 1 = y := by simp [bas]
  rw [h0, h1] at hsum
  refine ⟨bas.repr z 0, bas.repr z 1, ?_⟩
  calc z = _ := hsum.symm
    _ = _ := by simp only [Algebra.smul_def, mul_one]

/-- `K(√a)` for a non-square `a`. -/
theorem exists_quad_ext (K : Type) [Field K] [NumberField K] (a : K) (ha : ∀ x : K, x ^ 2 ≠ a) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E) (_ : Algebra.IsQuadraticExtension K E)
      (r : E), r ^ 2 = algebraMap K E a := by
  have hirr : Irreducible (X ^ 2 - C a : K[X]) := X_pow_sub_C_irreducible_of_prime Nat.prime_two ha
  haveI : Fact (Irreducible (X ^ 2 - C a : K[X])) := ⟨hirr⟩
  have hf0 : (X ^ 2 - C a : K[X]) ≠ 0 := hirr.ne_zero
  haveI hfin : Module.Finite K (AdjoinRoot (X ^ 2 - C a : K[X])) := (AdjoinRoot.powerBasis hf0).finite
  haveI : CharZero (AdjoinRoot (X ^ 2 - C a : K[X])) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AdjoinRoot (X ^ 2 - C a : K[X]))).injective
  haveI : FiniteDimensional ℚ (AdjoinRoot (X ^ 2 - C a : K[X])) := Module.Finite.trans K _
  haveI : NumberField (AdjoinRoot (X ^ 2 - C a : K[X])) := ⟨⟩
  haveI : Algebra.IsQuadraticExtension K (AdjoinRoot (X ^ 2 - C a : K[X])) :=
    { finrank_eq_two' := by
        rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim]
        exact natDegree_X_pow_sub_C }
  refine ⟨AdjoinRoot (X ^ 2 - C a : K[X]), inferInstance, inferInstance, inferInstance, inferInstance,
    AdjoinRoot.root _, ?_⟩
  have := AdjoinRoot.eval₂_root (X ^ 2 - C a : K[X])
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at this
  rw [AdjoinRoot.algebraMap_eq]
  linear_combination this

/-! ## The character of a quadratic extension unramified at the finite primes -/

section Char

variable {K : Type} [Field K] [NumberField K]

theorem card_two_mul_eq_one {G : Type} [Group G] (hc : Nat.card G = 2) {g h : G} (hg : g ≠ 1) (hh : h ≠ 1) :
    g * h = 1 := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : G)).1 hc
  have hgh : g = h := (huniq g hg).trans (huniq h hh).symm
  subst hgh
  have := pow_card_eq_one' (G := G) (x := g)
  rw [hc] at this
  simpa [sq] using this

/-- The isomorphism of a group of order `2` with `{±1} ⊆ ℚ`. -/
def signHom {G : Type} [Group G] (hc : Nat.card G = 2) : G →* ℚ where
  toFun g := by classical exact if g = 1 then 1 else -1
  map_one' := by simp
  map_mul' g h := by
    classical
    by_cases hg : g = 1
    · simp [hg]
    by_cases hh : h = 1
    · simp [hh, hg]
    · have := card_two_mul_eq_one hc hg hh
      simp [hg, hh, this]

theorem signHom_eq_one_iff {G : Type} [Group G] (hc : Nat.card G = 2) (g : G) :
    signHom hc g = 1 ↔ g = 1 := by
  classical
  show (if g = 1 then (1 : ℚ) else -1) = 1 ↔ _
  by_cases h : g = 1
  · simp [h]
  · simp only [h, ite_false, iff_false]; norm_num

theorem signHom_cases {G : Type} [Group G] (hc : Nat.card G = 2) (g : G) :
    signHom hc g = 1 ∨ signHom hc g = -1 := by
  classical
  show (if g = 1 then (1 : ℚ) else -1) = 1 ∨ (if g = 1 then (1 : ℚ) else -1) = -1
  by_cases h : g = 1 <;> simp [h]

theorem not_dvd_top (v : HeightOneSpectrum (𝓞 K)) : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 K)) :=
  fun h => v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))

/-- A quadratic extension unramified at all finite primes gives a `±1`-valued character of the narrow class group,
which is `1` exactly at the classes of the split primes. -/
theorem exists_char (E : Type) [Field E] [NumberField E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K E) :
    ∃ χ : RayClassGroup (narrowModulus K) →* ℚ, (∀ c, χ c = 1 ∨ χ c = -1) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), ∀ hv : ¬ v.asIdeal ∣ (narrowModulus K).finite,
        (χ (rayClass (narrowModulus K) v hv) = 1 ↔ v ∈ splitPrimes K E) := by
  have hdeg : Module.finrank K E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K E
  haveI : FiniteDimensional K E := Module.finite_of_finrank_pos (by omega)
  haveI : IsGalois K E := inferInstance
  have hcomm := commutative_of_finrank_two hdeg
  have hcard : Nat.card Gal(E/K) = 2 := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  obtain ⟨m, hm1, -, ψ, -, hψ, -⟩ := (artinReciprocity K).exists_artin E hcomm
  have hfin : m.finite = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, ne_bot_of_le_ne_bot m.finite_ne_bot hle⟩
    have hdv : v.asIdeal ∣ m.finite := Ideal.dvd_iff_le.2 hle
    exact ((hm1 v).1 hdv) (hunr v)
  have hdvd : m.Dvd (narrowModulus K) := ⟨by rw [hfin]; exact dvd_rfl, fun w hw => m.isReal_of_mem w hw⟩
  refine ⟨(signHom hcard).comp (ψ.comp (rayClassMap hdvd)), fun c => signHom_cases hcard _, fun v hv => ?_⟩
  have hv' : ¬ v.asIdeal ∣ m.finite := by rw [hfin]; exact not_dvd_top v
  rw [mem_splitPrimes_iff_artin m ψ (fun w _ => hunr w) hψ v hv', MonoidHom.mem_ker]
  exact signHom_eq_one_iff hcard _

end Char

/-! ## Arithmetic of the `p_i^*` -/

section Arith

variable {t : ℕ} (p : Fin t → ℕ)

/-- `p_i^* = (-1)^((p_i-1)/2) p_i`. -/
def pstar (i : Fin t) : ℤ := (-1) ^ ((p i - 1) / 2) * (p i : ℤ)

/-- `a_S = ∏_{i ∈ S} p_i^*`. -/
def aS (S : Finset (Fin t)) : ℤ := ∏ i ∈ S, pstar p i

variable {p}

theorem pstar_natAbs (i : Fin t) : (pstar p i).natAbs = p i := by
  simp [pstar, Int.natAbs_mul, Int.natAbs_pow]

theorem pstar_ne_zero (hp : ∀ i, (p i).Prime ∧ p i ≠ 2) (i : Fin t) : pstar p i ≠ 0 := by
  intro h
  have := pstar_natAbs (p := p) i
  rw [h] at this
  exact (hp i).1.ne_zero (by simpa using this.symm)

theorem aS_ne_zero (hp : ∀ i, (p i).Prime ∧ p i ≠ 2) (S : Finset (Fin t)) : aS p S ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => pstar_ne_zero hp i

theorem pstar_mod4 (hp : ∀ i, (p i).Prime ∧ p i ≠ 2) (i : Fin t) : pstar p i % 4 = 1 := by
  have h1 := (hp i).1
  have h2 := (hp i).2
  have hodd : (p i) % 2 = 1 := by
    rcases h1.eq_two_or_odd with h | h
    · exact absurd h h2
    · exact h
  have h4 : p i % 4 = 1 ∨ p i % 4 = 3 := by omega
  rcases h4 with h | h
  · have : (p i - 1) / 2 = 2 * (p i / 4) := by omega
    rw [pstar, this, pow_mul]
    simp
    omega
  · have : (p i - 1) / 2 = 2 * (p i / 4) + 1 := by omega
    rw [pstar, this, pow_succ, pow_mul]
    simp
    omega

theorem aS_mod4 (hp : ∀ i, (p i).Prime ∧ p i ≠ 2) (S : Finset (Fin t)) : aS p S % 4 = 1 := by
  unfold aS
  refine Finset.prod_induction _ (fun x => x % 4 = 1) (fun a b ha hb => ?_) (by norm_num)
    (fun i _ => pstar_mod4 hp i)
  rw [Int.mul_emod, ha, hb]
  norm_num

theorem pstar_isCoprime (hp : ∀ i, (p i).Prime ∧ p i ≠ 2) (hinj : Function.Injective p) {i j : Fin t}
    (hij : i ≠ j) : IsCoprime (pstar p i) (pstar p j) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, pstar_natAbs, pstar_natAbs]
  exact (Nat.coprime_primes (hp i).1 (hp j).1).2 (hinj.ne hij)

theorem aS_isCoprime (hp : ∀ i, (p i).Prime ∧ p i ≠ 2) (hinj : Function.Injective p) {S U : Finset (Fin t)}
    (h : Disjoint S U) : IsCoprime (aS p S) (aS p U) := by
  unfold aS
  rw [IsCoprime.prod_left_iff]
  intro i hi
  rw [IsCoprime.prod_right_iff]
  intro j hj
  exact pstar_isCoprime hp hinj (fun hij => Finset.disjoint_left.1 h hi (hij ▸ hj))

theorem aS_squarefree (hp : ∀ i, (p i).Prime ∧ p i ≠ 2) (hinj : Function.Injective p) (S : Finset (Fin t)) :
    Squarefree (aS p S) := by
  unfold aS
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i _ j _ hij => (pstar_isCoprime hp hinj hij).isRelPrime)
    (fun i _ => ?_)
  rw [← Int.squarefree_natAbs, pstar_natAbs]
  exact (hp i).1.squarefree

/-- `a_U` is not a rational square for `U ≠ ∅`. -/
theorem aS_not_sq (hp : ∀ i, (p i).Prime ∧ p i ≠ 2) (hinj : Function.Injective p) {U : Finset (Fin t)}
    (hU : U.Nonempty) (q : ℚ) : q ^ 2 ≠ (aS p U : ℚ) := by
  intro h
  have : IsSquare ((aS p U : ℤ) : ℚ) := ⟨q, by rw [← h]; ring⟩
  obtain ⟨r, hr⟩ := Rat.isSquare_intCast_iff.1 this
  have hu : IsUnit r := aS_squarefree hp hinj U r (by rw [hr])
  obtain ⟨i, hi⟩ := hU
  have hunit : IsUnit (aS p U) := by rw [hr]; exact hu.mul hu
  have hprod : pstar p i * aS p (U.erase i) = aS p U := Finset.mul_prod_erase U (pstar p) hi
  have hpu : IsUnit (pstar p i) := isUnit_of_mul_isUnit_left (hprod ▸ hunit)
  have := Int.isUnit_iff_natAbs_eq.1 hpu
  rw [pstar_natAbs] at this
  exact (hp i).1.ne_one this

theorem aS_union_compl (T : Finset (Fin t)) : aS p T * aS p (Finset.univ \ T) = aS p Finset.univ := by
  unfold aS
  rw [mul_comm]
  exact Finset.prod_sdiff (Finset.subset_univ T)

end Arith

/-! ## Unramifiedness -/

section Unram

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- A quadratic extension `E/F` containing `√a` and `√a'` for coprime integers `a, a' ≡ 1 (4)`, neither in `F`, is
unramified at all finite primes: the different contains `a` and `a'` (it contains `2Φ - 1 = √a` for
`Φ = (1 + √a)/2`). -/
theorem quad_unramified_gen (hdeg : Module.finrank F E = 2) (a a' : ℤ) (ha4 : a % 4 = 1) (ha4' : a' % 4 = 1)
    (hcop : IsCoprime a a') (r b : E) (hr : r ^ 2 = (a : E)) (hb : b ^ 2 = (a' : E))
    (hrF : ∀ f : F, algebraMap F E f ≠ r) (hbF : ∀ f : F, algebraMap F E f ≠ b)
    (𝔭 : HeightOneSpectrum (𝓞 F)) : 𝔭 ∈ unramifiedPrimes F E := by
  intro P hP hlo
  haveI := hP
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  rw [Ideal.dvd_iff_le] at hdvd
  have key : ∀ (c : ℤ) (x : E), c % 4 = 1 → x ^ 2 = (c : E) → (∀ f : F, algebraMap F E f ≠ x) →
      (c : 𝓞 E) ∈ P := by
    intro c x hc hx hxF
    obtain ⟨d, rfl⟩ : ∃ d : ℤ, c = 4 * d + 1 := ⟨c / 4, by omega⟩
    have hφ : ((1 + x) / 2) ^ 2 + ((-1 : ℤ) : E) * ((1 + x) / 2) + ((-d : ℤ) : E) = 0 := by
      push_cast at hx ⊢
      linear_combination (1 / 4 : E) * hx
    let Φ : 𝓞 E := ⟨(1 + x) / 2, isIntegral_of_quad _ (-1) (-d) hφ⟩
    have hΦ : Φ ^ 2 + ((-1 : ℤ) : 𝓞 E) * Φ + ((-d : ℤ) : 𝓞 E) = 0 := RingOfIntegers.ext (by
      have h := hφ
      push_cast at h ⊢
      exact h)
    have hFΦ : ∀ f : F, algebraMap F E f ≠ (Φ : E) := by
      intro f hf
      have hf' : algebraMap F E f = (1 + x) / 2 := hf
      refine hxF (2 * f - 1) ?_
      rw [map_sub, map_mul, hf']
      simp only [map_ofNat, map_one]
      ring
    have h2 := hdvd (mem_differentIdeal_of_quad hdeg Φ (-1) (-d) hΦ hFΦ)
    have : ((4 * d + 1 : ℤ) : 𝓞 E) = (2 * Φ + ((-1 : ℤ) : 𝓞 E)) ^ 2 := by
      push_cast
      push_cast at hΦ
      linear_combination (-4 : 𝓞 E) * hΦ
    rw [this]
    exact P.pow_mem_of_mem h2 2 (by norm_num)
  have h1 := key a r ha4 hr hrF
  have h2 := key a' b ha4' hb hbF
  obtain ⟨u, v, huv⟩ := hcop
  have hone : (1 : 𝓞 E) = (u : 𝓞 E) * (a : 𝓞 E) + (v : 𝓞 E) * (a' : 𝓞 E) := by
    exact_mod_cast huv.symm
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by
    rw [hone]
    exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)))

end Unram

/-! ## Data for a quadratic extension `K(√a)` -/

section TDataSec

variable {K : Type} [Field K] [NumberField K]

/-- A quadratic extension `K(√a)` of `K`, unramified at the finite primes, with its `±1`-character on the narrow
class group. -/
structure TData (K : Type) [Field K] [NumberField K] (a : ℤ) where
  E : Type
  [instField : Field E]
  [instNF : NumberField E]
  [instAlg : Algebra K E]
  [instQ : Algebra.IsQuadraticExtension K E]
  r : E
  r_sq : r ^ 2 = (a : E)
  span : ∀ z : E, ∃ u v : K, z = algebraMap K E u + algebraMap K E v * r
  not_mem : ∀ f : K, algebraMap K E f ≠ r
  χ : RayClassGroup (narrowModulus K) →* ℚ
  χ_pm : ∀ c, χ c = 1 ∨ χ c = -1
  χ_split : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ (narrowModulus K).finite),
    χ (rayClass (narrowModulus K) v hv) = 1 ↔ v ∈ splitPrimes K E

attribute [instance] TData.instField TData.instNF TData.instAlg TData.instQ

theorem exists_TData (a : ℤ) (ha : ∀ x : K, x ^ 2 ≠ (a : K))
    (hunr : ∀ (E : Type) [Field E] [NumberField E] [Algebra K E] [Algebra.IsQuadraticExtension K E] (r : E),
      r ^ 2 = (a : E) → ∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K E) :
    Nonempty (TData K a) := by
  obtain ⟨E, _, _, _, _, r, hr⟩ := exists_quad_ext K (a : K) ha
  have hr' : r ^ 2 = (a : E) := by simpa using hr
  have hnm : ∀ f : K, algebraMap K E f ≠ r := by
    intro f hf
    apply ha f
    apply (algebraMap K E).injective
    rw [map_pow, hf, hr]
  have hdeg : Module.finrank K E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K E
  obtain ⟨χ, h1, h2⟩ := exists_char E (hunr E r hr')
  exact ⟨⟨E, r, hr', quad_span hdeg r hnm, hnm, χ, h1, h2⟩⟩

/-- A `K`-embedding `K(√a) → K(√a')` forces `a` or `a a'` to be a square in `K`. -/
theorem TData.sq_or {a a' : ℤ} (D : TData K a) (D' : TData K a') (f : D.E →ₐ[K] D'.E) :
    (∃ u : K, u ^ 2 = (a : K)) ∨ ∃ w : K, w ^ 2 = (a : K) * (a' : K) := by
  obtain ⟨u, v, hy⟩ := D'.span (f D.r)
  have hy2 : (f D.r) ^ 2 = (a : D'.E) := by rw [← map_pow, D.r_sq]; simp
  rw [hy] at hy2
  have hr'2 := D'.r_sq
  have key : algebraMap K D'.E (u ^ 2 + v ^ 2 * (a' : K) - (a : K)) + algebraMap K D'.E (2 * u * v) * D'.r = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_ofNat]
    linear_combination hy2 - (algebraMap K D'.E v) ^ 2 * hr'2
  by_cases huv : u * v = 0
  · have hc : u ^ 2 + v ^ 2 * (a' : K) - (a : K) = 0 := by
      have h0 : (2 * u * v : K) = 0 := by rw [mul_assoc, huv]; simp
      rw [h0, map_zero, zero_mul, add_zero] at key
      exact (map_eq_zero_iff _ (algebraMap K D'.E).injective).1 key
    rcases mul_eq_zero.1 huv with hu | hv
    · right
      subst hu
      exact ⟨v * (a' : K), by linear_combination (a' : K) * hc⟩
    · left
      subst hv
      exact ⟨u, by linear_combination hc⟩
  · exfalso
    have h2 : (2 * u * v : K) ≠ 0 := by
      intro h
      apply huv
      have : 2 * (u * v) = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    apply D'.not_mem (-(u ^ 2 + v ^ 2 * (a' : K) - (a : K)) / (2 * u * v))
    rw [map_div₀, map_neg, div_eq_iff ((_root_.map_ne_zero _).2 h2)]
    linear_combination (-1 : D'.E) * key

end TDataSec

/-! ## The counting argument -/

section Main

variable {K : Type} [Field K] [NumberField K]

/-- A rational number that is a square in the quadratic field `K = ℚ(s)`, `s^2 = D`, is in `ℚ^2 ∪ Dℚ^2`. -/
theorem rat_sq_cases (hK : Module.finrank ℚ K = 2) (D : ℚ) (s : K) (hs : s ^ 2 = (D : K))
    (hsQ : ∀ q : ℚ, (q : K) ≠ s) (q : ℚ) (x : K) (hx : x ^ 2 = (q : K)) :
    (∃ u : ℚ, u ^ 2 = q) ∨ ∃ v : ℚ, D * v ^ 2 = q := by
  have hsQ' : ∀ f : ℚ, algebraMap ℚ K f ≠ s := fun f => by rw [eq_ratCast]; exact hsQ f
  obtain ⟨u, v, hxy⟩ := quad_span hK s hsQ' x
  rw [eq_ratCast, eq_ratCast] at hxy
  rw [hxy] at hx
  have key : (((u ^ 2 + v ^ 2 * D - q : ℚ)) : K) + ((2 * u * v : ℚ) : K) * s = 0 := by
    push_cast
    linear_combination hx - (v : K) ^ 2 * hs
  by_cases huv : u * v = 0
  · have h0 : (2 * u * v : ℚ) = 0 := by rw [mul_assoc, huv]; simp
    rw [h0, Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at key
    rcases mul_eq_zero.1 huv with hu | hv
    · right; subst hu; exact ⟨v, by linear_combination key⟩
    · left; subst hv; exact ⟨u, by linear_combination key⟩
  · exfalso
    have h2 : (2 * u * v : ℚ) ≠ 0 := by
      intro h; apply huv
      have : 2 * (u * v) = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    apply hsQ (-(u ^ 2 + v ^ 2 * D - q) / (2 * u * v))
    have h2' : ((2 * u * v : ℚ) : K) ≠ 0 := by exact_mod_cast h2
    rw [Rat.cast_div, Rat.cast_neg, div_eq_iff h2']
    linear_combination (-1 : K) * key

variable {t : ℕ} {p : Fin t → ℕ}

theorem aS_symmDiff (S U : Finset (Fin t)) :
    aS p S * aS p U = aS p (symmDiff S U) * aS p (S ∩ U) ^ 2 := by
  classical
  have hS : aS p (S \ U) * aS p (S ∩ U) = aS p S := by
    unfold aS
    rw [← Finset.sdiff_inter_self_left S U]
    exact Finset.prod_sdiff Finset.inter_subset_left
  have hU : aS p (U \ S) * aS p (S ∩ U) = aS p U := by
    unfold aS
    rw [Finset.inter_comm, ← Finset.sdiff_inter_self_left U S]
    exact Finset.prod_sdiff Finset.inter_subset_left
  have hD : aS p (symmDiff S U) = aS p (S \ U) * aS p (U \ S) := by
    unfold aS
    rw [symmDiff_def, Finset.sup_eq_union]
    exact Finset.prod_union disjoint_sdiff_sdiff
  rw [hD, ← hS, ← hU]
  ring

/-- **Example 0.7** (Milne, *CFT*, Introduction): genus theory lower bound `(C^+ : C^{+2}) ≥ 2^(t-1)`. -/
@[kb "milne2020cft" "Introduction, Example 0.7"]
theorem example07 : Example07 := ⟨by
  classical
  intro t p hinj hp K _ _ hK ⟨s, hs⟩
  haveI : Finite (RayClassGroup (narrowModulus K)) := (theorem_1_7_card _).1
  set H := Subgroup.closure {x : RayClassGroup (narrowModulus K) | ∃ y, x = y ^ 2} with hH
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simpa using Nat.one_le_iff_ne_zero.2 H.index_ne_zero_of_finite
  let i0 : Fin t := ⟨t - 1, by omega⟩
  let I : Finset (Fin t) := Finset.univ.erase i0
  have hs' : s ^ 2 = ((aS p Finset.univ : ℤ) : K) := by
    rw [hs]; simp [aS, pstar]
  have hsQ : ∀ q : ℚ, (q : K) ≠ s := by
    intro q hq
    apply aS_not_sq hp hinj (U := Finset.univ) ⟨i0, Finset.mem_univ _⟩ q
    apply (algebraMap ℚ K).injective
    rw [map_pow, eq_ratCast, eq_ratCast, hq, hs']
    simp
  have hnsq : ∀ U ⊆ I, U.Nonempty → ∀ x : K, x ^ 2 ≠ ((aS p U : ℤ) : K) := by
    intro U hUI hU x hx
    have hx' : x ^ 2 = (((aS p U : ℤ) : ℚ) : K) := by rw [hx]; simp
    have hs'' : s ^ 2 = (((aS p Finset.univ : ℤ) : ℚ) : K) := by rw [hs']; simp
    rcases rat_sq_cases hK _ s hs'' hsQ _ x hx' with ⟨u, hu⟩ | ⟨v, hv⟩
    · exact aS_not_sq hp hinj hU u hu
    · have hi0 : i0 ∈ Finset.univ \ U := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro h; simpa [I] using hUI h
      have hU0 : ((aS p U : ℤ) : ℚ) ≠ 0 := by exact_mod_cast aS_ne_zero hp U
      have hv0 : v ≠ 0 := by rintro rfl; apply hU0; rw [← hv]; ring
      apply aS_not_sq hp hinj ⟨i0, hi0⟩ v⁻¹
      have hc := aS_union_compl (p := p) U
      have : ((aS p U : ℤ) : ℚ) * ((aS p (Finset.univ \ U) : ℤ) : ℚ) = ((aS p Finset.univ : ℤ) : ℚ) := by
        exact_mod_cast hc
      rw [← this] at hv
      have h1 : ((aS p U : ℤ) : ℚ) * (((aS p (Finset.univ \ U) : ℤ) : ℚ) * v ^ 2) =
          ((aS p U : ℤ) : ℚ) * 1 := by rw [← mul_assoc, hv, mul_one]
      have := mul_left_cancel₀ hU0 h1
      rw [inv_pow]
      exact (eq_inv_of_mul_eq_one_left this).symm
  have hT : ∀ U : I.powerset, U.1.Nonempty → Nonempty (TData K (aS p U.1)) := by
    rintro ⟨U, hUI⟩ hU
    have hUI' : U ⊆ I := Finset.mem_powerset.1 hUI
    refine exists_TData _ (hnsq U hUI' hU) ?_
    intro E _ _ _ _ r hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      have : ((aS p U : ℤ) : E) = 0 := by rw [← hr]; ring
      exact aS_ne_zero hp U (by exact_mod_cast this)
    have hrF : ∀ f : K, algebraMap K E f ≠ r := by
      intro f hf
      apply hnsq U hUI' hU f
      apply (algebraMap K E).injective
      rw [map_pow, hf, hr]; simp
    let b : E := algebraMap K E s / r
    have hb : b ^ 2 = ((aS p (Finset.univ \ U) : ℤ) : E) := by
      have hc := aS_union_compl (p := p) U
      have hsE : (algebraMap K E s) ^ 2 = ((aS p U : ℤ) : E) * ((aS p (Finset.univ \ U) : ℤ) : E) := by
        rw [← map_pow, hs', ← hc]; push_cast; simp
      have hU0E : ((aS p U : ℤ) : E) ≠ 0 := by exact_mod_cast aS_ne_zero hp U
      simp only [b, div_pow, hsE, hr]
      exact mul_div_cancel_left₀ _ hU0E
    have hbF : ∀ f : K, algebraMap K E f ≠ b := by
      intro f hf
      have hf0 : f ≠ 0 := by
        rintro rfl
        have : b = 0 := by rw [← hf, map_zero]
        simp only [b, div_eq_zero_iff, hr0, or_false, map_eq_zero] at this
        have hs0 : s ^ 2 = 0 := by rw [this]; ring
        rw [hs'] at hs0
        exact aS_ne_zero hp Finset.univ (by exact_mod_cast hs0)
      have hs0 : algebraMap K E s ≠ 0 := by
        rw [_root_.map_ne_zero]; rintro rfl
        rw [zero_pow two_ne_zero] at hs'
        exact aS_ne_zero hp Finset.univ (by exact_mod_cast hs'.symm)
      apply hrF (s / f)
      rw [map_div₀, hf]
      simp only [b]
      field_simp
    exact quad_unramified_gen (Algebra.IsQuadraticExtension.finrank_eq_two K E) _ _ (aS_mod4 hp U)
      (aS_mod4 hp _) (aS_isCoprime hp hinj disjoint_sdiff_self_right) r b hr hb hrF hbF
  let χ : I.powerset → (RayClassGroup (narrowModulus K) →* ℚ) := fun U =>
    if h : U.1.Nonempty then (hT U h).some.χ else 1
  have hχpm : ∀ U c, χ U c = 1 ∨ χ U c = -1 := by
    intro U c
    by_cases h : U.1.Nonempty
    · simp only [χ, dite_eq_left h]; exact (hT U h).some.χ_pm c
    · simp [χ, dif_neg h]
  have hHle : ∀ U, H ≤ (χ U).ker := by
    intro U
    rw [hH, Subgroup.closure_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_pow]
    rcases hχpm U y with h | h <;> rw [h] <;> norm_num
  have hgal : ∀ (U : I.powerset) (h : U.1.Nonempty), IsGalois K (hT U h).some.E := by
    intro U h
    haveI : FiniteDimensional K (hT U h).some.E := Module.finite_of_finrank_pos
      (by rw [Algebra.IsQuadraticExtension.finrank_eq_two K]; omega)
    infer_instance
  have hsplit : ∀ (U : I.powerset) (h : U.1.Nonempty) (v : HeightOneSpectrum (𝓞 K)),
      χ U (rayClass (narrowModulus K) v (not_dvd_top v)) = 1 ↔ v ∈ splitPrimes K (hT U h).some.E := by
    intro U h v
    simp only [χ, dite_eq_left h]
    exact (hT U h).some.χ_split v _
  have hnontriv : ∀ (U : I.powerset) (h : U.1.Nonempty), χ U ≠ 1 := by
    intro U h hU
    haveI := hgal U h
    obtain ⟨f⟩ := nonempty_algHom_of_splitPrimes_diff_finite (K := K) (hT U h).some.E K ∅ Set.finite_empty
      (fun v _ => (hsplit U h v).1 (by rw [hU]; rfl))
    have hle := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.toRingHom.injective
    rw [Algebra.IsQuadraticExtension.finrank_eq_two K, Module.finrank_self] at hle
    omega
  have hinjχ : Function.Injective χ := by
    intro U U' hUU'
    by_contra hne
    by_cases h : U.1.Nonempty <;> by_cases h' : U'.1.Nonempty
    · haveI := hgal U h
      haveI := hgal U' h'
      obtain ⟨f⟩ := nonempty_algHom_of_splitPrimes_diff_finite (K := K) (hT U h).some.E (hT U' h').some.E ∅
        Set.finite_empty (fun v hv => (hsplit U h v).1 (by rw [hUU']; exact (hsplit U' h' v).2 hv.1))
      have hUI : U.1 ⊆ I := Finset.mem_powerset.1 U.2
      have hUI' : U'.1 ⊆ I := Finset.mem_powerset.1 U'.2
      rcases (hT U h).some.sq_or (hT U' h').some f with ⟨u, hu⟩ | ⟨w, hw⟩
      · exact hnsq _ hUI h u hu
      · have hsd : symmDiff U.1 U'.1 ⊆ I := by
          rw [symmDiff_def, Finset.sup_eq_union]
          exact Finset.union_subset (Finset.sdiff_subset.trans hUI) (Finset.sdiff_subset.trans hUI')
        have hne' : (symmDiff U.1 U'.1).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h0
          apply hne
          apply Subtype.ext
          rwa [← Finset.bot_eq_empty, symmDiff_eq_bot] at h0
        have hi0 : ((aS p (U.1 ∩ U'.1) : ℤ) : K) ≠ 0 := by exact_mod_cast aS_ne_zero hp _
        apply hnsq _ hsd hne' (w / (aS p (U.1 ∩ U'.1) : ℤ))
        have hk := aS_symmDiff (p := p) U.1 U'.1
        have hk' : ((aS p U.1 : ℤ) : K) * ((aS p U'.1 : ℤ) : K) =
            ((aS p (symmDiff U.1 U'.1) : ℤ) : K) * ((aS p (U.1 ∩ U'.1) : ℤ) : K) ^ 2 := by
          exact_mod_cast hk
        rw [div_pow, hw, hk']
        field_simp
    · exact hnontriv U h (by rw [hUU']; simp [χ, dif_neg h'])
    · exact hnontriv U' h' (by rw [← hUU']; simp [χ, dif_neg h])
    · apply hne
      apply Subtype.ext
      rw [Finset.not_nonempty_iff_eq_empty] at h h'
      rw [h, h']
  let Q := RayClassGroup (narrowModulus K) ⧸ H
  haveI : Fintype Q := Fintype.ofFinite Q
  let ψ : I.powerset → (Q →* ℚ) := fun U => QuotientGroup.lift H (χ U) (hHle U)
  have hψ : Function.Injective ψ := by
    intro U U' h
    apply hinjχ
    refine MonoidHom.ext fun x => ?_
    have := DFunLike.congr_fun h (QuotientGroup.mk x : Q)
    rwa [QuotientGroup.lift_mk, QuotientGroup.lift_mk] at this
  have hli := (linearIndependent_monoidHom Q ℚ).comp ψ hψ
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at hcard
  have hI : Fintype.card I.powerset = 2 ^ (t - 1) := by
    rw [Fintype.card_coe, Finset.card_powerset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  rw [hI] at hcard
  calc 2 ^ (t - 1) ≤ Fintype.card Q := hcard
    _ = H.index := by rw [Subgroup.index, Nat.card_eq_fintype_card]⟩

end Main

end NumberFieldKB.MilneCFT.Ex07
