import NumberFieldKB.ModularCurves.CuspInfinity
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LaurentSeries
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Int

/-!
# The cusps $\infty$ and $0$ of $X_0(N)$ are rational

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf pp. 190–196): the cusps $\infty$ and $0$ of $X_0(N)$
are rational points, i.e. have degree 1.

* `ratMap`: $\mathbb Q((q)) \to \mathbb C((q))$ on coefficients. The $q$-expansions $J$, $J_N$ of $j$, $j_N$ have
  rational coefficients (`IsRatQExp`), so the image of $\mathbb Q(X_0(N))$ under `qExpX0` lies in the subfield
  `ratMap.fieldRange` (`qExpX0_mem_fieldRange`).
* **`deg_cuspInf`**: the residue field of the cusp $\infty$ is $\mathbb Q$ (constant term of the $q$-expansion).
* **`deg_cusp0`**, **`resDegX0_cuspInf`**, **`resDegX0_cusp0`**: degree 1 for $0 = w_N(\infty)$, and residue degree 1
  over the cusp of $X(1)$.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex ModularForm
open scoped MatrixGroups WithZero

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC NumberFieldKB.MilneEC.V

/-- The coefficientwise map $\mathbb Q((q)) \to \mathbb C((q))$. -/
noncomputable def ratMap : LaurentSeries ℚ →+* LaurentSeries ℂ where
  toFun f := f.map (algebraMap ℚ ℂ)
  map_one' := HahnSeries.map_one (algebraMap ℚ ℂ : ℚ →*₀ ℂ)
  map_mul' _ _ := HahnSeries.map_mul (algebraMap ℚ ℂ : ℚ →ₙ+* ℂ)
  map_zero' := HahnSeries.map_zero (algebraMap ℚ ℂ : ℚ →+* ℂ).toZeroHom
  map_add' _ _ := HahnSeries.map_add (algebraMap ℚ ℂ : ℚ →+ ℂ)

theorem ratMap_coeff (g : LaurentSeries ℚ) (n : ℤ) : (ratMap g).coeff n = algebraMap ℚ ℂ (g.coeff n) := rfl

/-- A Laurent series all of whose coefficients are rational is in the image of `ratMap`. -/
theorem mem_range_ratMap {f : LaurentSeries ℂ} (hf : ∀ n, f.coeff n ∈ ratSubring) :
    f ∈ ratMap.range := by
  choose c hc using hf
  have hsupp : Function.support (fun n => c n) ⊆ f.support := by
    intro n hn
    rw [Function.mem_support] at hn
    rw [HahnSeries.mem_support]
    intro h0
    apply hn
    have : algebraMap ℚ ℂ (c n) = 0 := by rw [show algebraMap ℚ ℂ (c n) = f.coeff n from hc n, h0]
    exact (map_eq_zero _).1 this
  refine ⟨⟨fun n => c n, f.isPWO_support.mono hsupp⟩, ?_⟩
  ext n
  exact hc n

theorem qHat_mem_range_ratMap {f : ℍ → ℂ} (hf : IsRatQExp f) : qHat f ∈ ratMap.range := by
  refine mem_range_ratMap fun n => ?_
  rcases lt_or_ge n 0 with hn | hn
  · rw [qHat, ofPowerSeries_coeff_neg _ hn]; exact zero_mem _
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [qHat, HahnSeries.ofPowerSeries_apply_coeff]
    exact hf.rat k

theorem jSer_mem_fieldRange : jSer ∈ ratMap.fieldRange := by
  rw [jSer]
  exact (ratMap.fieldRange).div_mem (qHat_mem_range_ratMap (IsRatQExp.E4.pow 3))
    (qHat_mem_range_ratMap IsRatQExp.disc)

theorem jNSer_mem_fieldRange {N : ℕ} (hN : 1 ≤ N) : jNSer N ∈ ratMap.fieldRange := by
  rw [jNSer]
  exact (ratMap.fieldRange).div_mem (qHat_mem_range_ratMap ((IsRatQExp.E4.pow 3).scaleN hN))
    (qHat_mem_range_ratMap (IsRatQExp.disc.scaleN hN))

theorem qSeriesPoly_mem_fieldRange {N : ℕ} (hN : 1 ≤ N) (G : ℚ[X][X]) :
    qSeriesPoly hN G ∈ ratMap.fieldRange := by
  have hC : ∀ c : ℚ, qSeriesPoly hN (C (C c)) ∈ ratMap.fieldRange := by
    intro c
    have e : qSeriesPoly hN (C (C c)) = ratMap (algebraMap ℚ (LaurentSeries ℚ) c) :=
      RingHom.congr_fun (RingHom.ext_rat ((qSeriesPoly hN).comp (C.comp C))
        (ratMap.comp (algebraMap ℚ (LaurentSeries ℚ)))) c
    rw [e]
    exact ⟨_, rfl⟩
  have hA : ∀ a : ℚ[X], qSeriesPoly hN (C a) ∈ ratMap.fieldRange := by
    intro a
    induction a using Polynomial.induction_on with
    | C c => exact hC c
    | add p q hp hq => rw [C_add, map_add]; exact add_mem hp hq
    | monomial n c ih =>
      rw [pow_succ, ← mul_assoc, C_mul, map_mul, qSeriesPoly_C_X]
      exact mul_mem ih (jSer_mem_fieldRange)
  induction G using Polynomial.induction_on with
  | C a => exact hA a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, qSeriesPoly_X]
    exact mul_mem ih (jNSer_mem_fieldRange hN)

variable {N : ℕ} [NeZero N]

theorem qExpX0_mem_fieldRange (x : X0 N) : qExpX0 N x ∈ ratMap.fieldRange := by
  obtain ⟨G, d, -, rfl⟩ := exists_eq_div (prop2_4' N) x
  rw [map_div₀, qExpX0_coordToX0, qExpX0_coordToX0, qExpCoord_mk, qExpCoord_mk]
  exact (ratMap.fieldRange).div_mem (qSeriesPoly_mem_fieldRange _ _) (qSeriesPoly_mem_fieldRange _ _)

theorem qExpX0_algebraMap (c : ℚ) :
    qExpX0 N (algebraMap ℚ (X0 N) c) = HahnSeries.C (algebraMap ℚ ℂ c) :=
  RingHom.congr_fun (RingHom.ext_rat ((qExpX0 N).comp (algebraMap ℚ (X0 N)))
    ((HahnSeries.C : ℂ →+* LaurentSeries ℂ).comp (algebraMap ℚ ℂ))) c

/-- Every element of $\mathcal O_\infty$ is congruent to a rational constant modulo the maximal ideal. -/
theorem exists_sub_mem_maximalIdeal (y : (cuspInf N).O) :
    ∃ c : ℚ, y - (cuspInf N).ofBase c ∈ IsLocalRing.maximalIdeal (cuspInf N).O := by
  have hy : Valued.v (qExpX0 N (y : X0 N)) ≤ 1 := (mem_cuspInf_O _).1 y.2
  obtain ⟨g, hg⟩ := qExpX0_mem_fieldRange (y : X0 N)
  refine ⟨g.coeff 0, ?_⟩
  have e0 : (1 : ℤᵐ⁰) = WithZero.exp (-(0 : ℤ)) := by rw [neg_zero, WithZero.exp_zero]
  have hneg : ∀ n < 0, (qExpX0 N (y : X0 N)).coeff n = 0 := by
    rw [e0] at hy
    exact (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero ℂ).1 hy
  -- the difference has valuation `< 1`
  set z : (cuspInf N).O := y - (cuspInf N).ofBase (g.coeff 0) with hz
  have hzval : Valued.v (qExpX0 N (z : X0 N)) ≤ WithZero.exp (-(1 : ℤ)) := by
    rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero ℂ]
    intro n hn
    have hz' : qExpX0 N (z : X0 N) =
        qExpX0 N (y : X0 N) - HahnSeries.C (algebraMap ℚ ℂ (g.coeff 0)) := by
      rw [← qExpX0_algebraMap (N := N)]
      simp [hz, PrimeDivisor.ofBase]
    rw [hz', HahnSeries.coeff_sub]
    rcases lt_or_ge n 0 with h0 | h0
    · rw [hneg n h0, HahnSeries.C_apply, HahnSeries.coeff_single]; simp [h0.ne]
    · have : n = 0 := by omega
      subst this
      rw [← hg, ratMap_coeff, HahnSeries.C_apply, HahnSeries.coeff_single]
      simp
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h1 : ((z : X0 N)) * ((u⁻¹ : (cuspInf N).Oˣ) : (cuspInf N).O) = 1 := by
    have : (u : (cuspInf N).O) * ((u⁻¹ : (cuspInf N).Oˣ) : (cuspInf N).O) = 1 := by simp
    rw [hu] at this
    exact congrArg Subtype.val this
  have hw : Valued.v (qExpX0 N (((u⁻¹ : (cuspInf N).Oˣ) : (cuspInf N).O) : X0 N)) ≤ 1 :=
    (mem_cuspInf_O _).1 ((u⁻¹ : (cuspInf N).Oˣ) : (cuspInf N).O).2
  have h2 : Valued.v (qExpX0 N ((z : X0 N) * (((u⁻¹ : (cuspInf N).Oˣ) : (cuspInf N).O) : X0 N))) = 1 := by
    rw [h1, map_one, map_one]
  rw [map_mul, map_mul] at h2
  have h3 : WithZero.exp (-(1 : ℤ)) < (1 : ℤᵐ⁰) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.2 (by norm_num)
  have h4 : Valued.v (qExpX0 N (z : X0 N)) * Valued.v (qExpX0 N
      (((u⁻¹ : (cuspInf N).Oˣ) : (cuspInf N).O) : X0 N)) ≤ WithZero.exp (-(1 : ℤ)) * 1 :=
    mul_le_mul' hzval hw
  rw [h2, mul_one] at h4
  exact absurd h3 (not_lt.2 h4)

/-- **The cusp $\infty$ of $X_0(N)$ is rational**: its residue field is $\mathbb Q$. -/
@[kb "milne2006ec" "Ch. V, §2, the cusps ∞ and 0 of X_0(N) are rational (running text), pdf pp. 190-196"]
theorem deg_cuspInf : (cuspInf N).deg = 1 := by
  let _ : Module ℚ (IsLocalRing.ResidueField (cuspInf N).O) :=
    ((IsLocalRing.residue (cuspInf N).O).comp (cuspInf N).ofBase).toModule
  unfold PrimeDivisor.deg
  refine (finrank_eq_one_iff_of_nonzero' (1 : IsLocalRing.ResidueField (cuspInf N).O) one_ne_zero).2 ?_
  intro w
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
  obtain ⟨c, hc⟩ := exists_sub_mem_maximalIdeal y
  refine ⟨c, ?_⟩
  have := (IsLocalRing.residue_eq_zero_iff _).2 hc
  rw [map_sub, sub_eq_zero] at this
  rw [this]
  change IsLocalRing.residue _ ((cuspInf N).ofBase c) * 1 = _
  rw [mul_one]

/-- **The cusp $0$ of $X_0(N)$ is rational.** -/
@[kb "milne2006ec" "Ch. V, §2, the cusps ∞ and 0 of X_0(N) are rational (running text), pdf pp. 190-196"]
theorem deg_cusp0 : (cusp0 N).deg = 1 := by
  rw [cusp0, frickePlace, PrimeDivisor.deg_comapEquiv, deg_cuspInf]

theorem deg_cuspInf_one : (cuspInf 1).deg = 1 := deg_cuspInf

/-- The residue degree of $\infty$ over the cusp of $X(1)$ ($z \mapsto z$) is 1. -/
theorem resDegX0_cuspInf : resDegX0 (one_mul_one_dvd N) (cuspInf N) = 1 := by
  let := (degeneracy 1 N 1 (one_mul_one_dvd N)).toAlgebra
  have := isScalarTower_rat_degeneracy (one_mul_one_dvd N)
  have := isAlgebraic_degeneracy (one_mul_one_dvd N)
  have h := (cuspInf N).deg_eq_residueDeg_mul (K := X0 1)
  have e : (cuspInf N).comap (K := X0 1) = cuspInf 1 := degeneracyPlace_cuspInf_one
  rw [e, deg_cuspInf, deg_cuspInf_one] at h
  unfold resDegX0
  simpa using h.symm

/-- The residue degree of $0$ over the cusp of $X(1)$ ($z \mapsto z$) is 1. -/
theorem resDegX0_cusp0 : resDegX0 (one_mul_one_dvd N) (cusp0 N) = 1 := by
  let := (degeneracy 1 N 1 (one_mul_one_dvd N)).toAlgebra
  have := isScalarTower_rat_degeneracy (one_mul_one_dvd N)
  have := isAlgebraic_degeneracy (one_mul_one_dvd N)
  have h := (cusp0 N).deg_eq_residueDeg_mul (K := X0 1)
  have e : (cusp0 N).comap (K := X0 1) = cuspInf 1 := degeneracyPlace_cusp0
  rw [e, deg_cusp0, deg_cuspInf_one] at h
  unfold resDegX0
  simpa using h.symm

end NumberFieldKB.ModularCurves
