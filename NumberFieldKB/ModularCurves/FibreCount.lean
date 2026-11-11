import NumberFieldKB.ModularCurves.NormEmbeddings
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Counting the places over a place by embeddings into a valued field

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (the ramification of $j : X_0(N) \to X_0(1)$, pdf p. 196).
The classical computation of the fibres of $j$ expands the conjugates $j_N \circ \gamma$ of $j_N$ in a local
parameter (at a cusp, in fractional powers of $q$). This file is the algebra behind it.

Let $K/F$ be a finite separable extension of function fields over $k$, $P$ a place of $F$, and
$\sigma_1, \dots, \sigma_n : K \to L$ the $n = [K : F]$ distinct $F$-embeddings into a field $L$ with a discrete
valuation $v_L$ which induces $v_P^M$ on $F$ ($M \ge 1$). Then:

* each $\sigma_i$ defines a place $P'_i = $ `placeOf hK hvF (σ i)` of $K$ over $P$ (`restrict_placeOf`), with
  $v_L(\sigma_i z) = \exp(-c_i \operatorname{ord}_{P'_i} z)$, $c_i\, e(P'_i) = M$
  (`valuation_apply_eq_exp`, `ramificationIdx_placeOf_mul`);
* every place $P'$ over $P$ is some $P'_i$, exactly $e(P') f(P')$ times (`card_placeOf_eq`);
* hence $M \sum_{P' \mid P} f(P') = \sum_i M / e(P'_i)$ (`mul_sum_relativeDegree_eq`): the number of geometric points
  over $P$ is $\sum_i 1/e(P'_i)$.

The proof compares $v_L(N_{K/F} z) = v_L(\prod_i \sigma_i z)$ (`algebraMap_norm_eq_prod`) with
$\operatorname{ord}_P(N z) = \sum_{P' \mid P} f(P') \operatorname{ord}_{P'}(z)$ (`ord_norm_place`) for a $z$ with a simple
zero at one $P'$ and units at the other places over $P$ (weak approximation).
-/

open TauCeti
open scoped WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

variable {k F K L : Type*} [Field k] [Field F] [Field K] [Field L] [Algebra k F] [Algebra k K] [Algebra F K]
  [IsScalarTower k F K] [FiniteDimensional F K] [Algebra.IsSeparable F K] [Algebra F L]
  (hK : IsFunctionField k K) {vL : Valuation L ℤᵐ⁰} {P : Place k F} {M : ℕ}
  (hvF : ∀ x : F, vL (algebraMap F L x) = P.valuation x ^ M)

section OnePlace

variable (σ : K →ₐ[F] L)

include hvF in
theorem valuation_algebraMap_comp (x : F) : vL (σ (algebraMap F K x)) = P.valuation x ^ M := by
  rw [AlgHom.commutes, hvF]

include hvF in
theorem valuation_constant_le_one (c : k) : vL (σ (algebraMap k K c)) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply k F K, valuation_algebraMap_comp hvF]
  exact pow_le_one' (P.mem_integers_iff.1 (P.algebraMap_mem_integers c)) M

/-- The valuation ring of $v_L \circ \sigma$. -/
def ringOf : ValuationSubring K := (vL.comap (σ : K →+* L)).valuationSubring

theorem mem_ringOf {z : K} : z ∈ ringOf (vL := vL) σ ↔ vL (σ z) ≤ 1 := Iff.rfl

include hvF in
theorem constant_mem_ringOf (c : k) : algebraMap k K c ∈ ringOf (vL := vL) σ := by
  exact (mem_ringOf σ).2 (valuation_constant_le_one hvF σ c)

include hvF in
theorem ringOf_ne_top (hM : 0 < M) : ringOf (vL := vL) σ ≠ ⊤ := by
  obtain ⟨π, hπ⟩ := P.ord_surjective 1
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  intro htop
  have hmem : (algebraMap F K π)⁻¹ ∈ ringOf (vL := vL) σ := htop ▸ ValuationSubring.mem_top _
  rw [mem_ringOf, map_inv₀, map_inv₀, valuation_algebraMap_comp hvF, P.valuation_eq_exp_neg_ord hπ0, hπ,
    ← WithZero.exp_nsmul, ← WithZero.exp_neg, WithZero.exp_le_one_iff] at hmem
  simp at hmem
  omega

/-- **The place of $K$ defined by an embedding** $\sigma : K \to L$: the valuation ring of $v_L \circ \sigma$. -/
def placeOf (hM : 0 < M) : Place k K :=
  Place.ofValuationSubring hK (constant_mem_ringOf hvF σ) (ringOf_ne_top hvF σ hM)

theorem mem_integers_placeOf (hM : 0 < M) {z : K} :
    z ∈ (placeOf hK hvF σ hM).integers ↔ vL (σ z) ≤ 1 := by
  rw [placeOf, Place.integers_ofValuationSubring]
  rfl

/-- The place defined by $\sigma$ lies over $P$. -/
theorem restrict_placeOf (hM : 0 < M) : (placeOf hK hvF σ hM).restrict k F = P := by
  symm
  refine Place.eq_of_integers_le fun x hx => ?_
  rw [Place.mem_integers_restrict_iff, mem_integers_placeOf, valuation_algebraMap_comp hvF]
  exact pow_le_one' (P.mem_integers_iff.1 hx) M

theorem valuation_unit_eq_one (hM : 0 < M) (u : (placeOf hK hvF σ hM).integersˣ) : vL (σ (u : K)) = 1 := by
  have h1 : vL (σ (u : K)) ≤ 1 := (mem_integers_placeOf hK hvF σ hM).1 (u : (placeOf hK hvF σ hM).integers).2
  have h2 : vL (σ ((u⁻¹ : (placeOf hK hvF σ hM).integersˣ) : K)) ≤ 1 :=
    (mem_integers_placeOf hK hvF σ hM).1
      (((u⁻¹ : (placeOf hK hvF σ hM).integersˣ) : (placeOf hK hvF σ hM).integers)).2
  have hprod : vL (σ (u : K)) * vL (σ ((u⁻¹ : (placeOf hK hvF σ hM).integersˣ) : K)) = 1 := by
    rw [← map_mul, ← map_mul]
    have : ((u : (placeOf hK hvF σ hM).integers) : K) * ((u⁻¹ : (placeOf hK hvF σ hM).integersˣ) : K) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      rfl
    rw [this, map_one, map_one]
  by_contra hne
  have hlt : vL (σ (u : K)) < 1 := lt_of_le_of_ne h1 hne
  have : vL (σ (u : K)) * vL (σ ((u⁻¹ : (placeOf hK hvF σ hM).integersˣ) : K)) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

/-- **$v_L \circ \sigma$ is a multiple of the order at its place**: $v_L(\sigma z) = \exp(-c\operatorname{ord}(z))$ for a
positive integer $c$. -/
theorem exists_valuation_apply_eq_exp (hM : 0 < M) :
    ∃ c : ℤ, 0 < c ∧ ∀ z : K, z ≠ 0 → vL (σ z) = WithZero.exp (-(c * (placeOf hK hvF σ hM).ord z)) := by
  set Q := placeOf hK hvF σ hM
  obtain ⟨t, ht⟩ := Q.exists_isUniformizer
  have ht1 : Q.ord t = 1 := Q.isUniformizer_iff_ord_eq_one.1 ht
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht1
  have hσt0 : vL (σ t) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact (map_ne_zero_iff _ σ.toRingHom.injective).2 ht0
  have htle : vL (σ t) ≤ 1 := (mem_integers_placeOf hK hvF σ hM).1 (Q.mem_integers_iff_ord_nonneg.2 (by omega))
  have htlt : vL (σ t) < 1 := by
    refine lt_of_le_of_ne htle fun heq => ?_
    have hinv : t⁻¹ ∈ Q.integers := by
      rw [mem_integers_placeOf, map_inv₀, map_inv₀, heq, inv_one]
    rw [Q.mem_integers_iff_ord_nonneg, Q.ord_inv, ht1] at hinv
    omega
  obtain ⟨c', hc'⟩ : ∃ c' : ℤ, vL (σ t) = WithZero.exp c' := ⟨WithZero.log (vL (σ t)), (WithZero.exp_log hσt0).symm⟩
  refine ⟨-c', ?_, fun z hz => ?_⟩
  · rw [hc', ← WithZero.exp_zero, WithZero.exp_lt_exp] at htlt
    omega
  obtain ⟨u, hu⟩ := Q.exists_eq_zpow_mul_unit ht hz
  have hz' : vL (σ z) = vL (σ t) ^ Q.ord z := by
    conv_lhs => rw [hu]
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀, valuation_unit_eq_one hK hvF σ hM u, mul_one]
  rw [hz', hc', ← WithZero.exp_zsmul, smul_eq_mul]
  congr 1
  ring

/-- The scaling factor $c$ of $v_L \circ \sigma$: $v_L(\sigma z) = \exp(-c \operatorname{ord}(z))$. -/
def scale (hM : 0 < M) : ℤ := (exists_valuation_apply_eq_exp hK hvF σ hM).choose

theorem scale_pos (hM : 0 < M) : 0 < scale hK hvF σ hM := (exists_valuation_apply_eq_exp hK hvF σ hM).choose_spec.1

theorem valuation_apply_eq_exp (hM : 0 < M) {z : K} (hz : z ≠ 0) :
    vL (σ z) = WithZero.exp (-(scale hK hvF σ hM * (placeOf hK hvF σ hM).ord z)) :=
  (exists_valuation_apply_eq_exp hK hvF σ hM).choose_spec.2 z hz

/-- **$c \cdot e = M$**: the scaling factor times the ramification index of the place of $\sigma$ is $M$. -/
theorem scale_mul_ramificationIdx (hM : 0 < M) :
    scale hK hvF σ hM * Place.ramificationIdx F (placeOf hK hvF σ hM) = M := by
  obtain ⟨π, hπ⟩ := P.ord_surjective 1
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have h1 := valuation_apply_eq_exp hK hvF σ hM ((map_ne_zero_iff _ (algebraMap F K).injective).2 hπ0)
  rw [valuation_algebraMap_comp hvF, P.valuation_eq_exp_neg_ord hπ0, hπ, ← WithZero.exp_nsmul,
    Place.ord_algebraMap_restrict k F (placeOf hK hvF σ hM), restrict_placeOf, hπ, WithZero.exp_inj] at h1
  simp only [nsmul_eq_mul, mul_neg, mul_one, neg_inj] at h1
  exact_mod_cast h1.symm

end OnePlace

theorem prod_exp {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, WithZero.exp_add]

section Count

variable {ι : Type*} [Fintype ι] (σ : ι → (K →ₐ[F] L)) (hσ : Function.Injective σ)
  (hcard : Fintype.card ι = Module.finrank F K) (hM : 0 < M)

open scoped Classical in
include hσ hcard in
/-- **Every place over $P$ comes from exactly $e f$ of the embeddings**: $\#\{i : P'_i = P'\} = e(P') f(P')$. -/
theorem card_placeOf_eq (P' : Place k K) (hP' : P'.restrict k F = P) :
    ((Finset.univ.filter fun i => placeOf hK hvF (σ i) hM = P').card : ℤ) =
      Place.ramificationIdx F P' * Place.relativeDegree k F P' := by
  classical
  obtain ⟨t, ht1, ht0⟩ := Place.exists_ord_eq_one_and_forall_mem_ord_eq_zero P' (fibre (F' := K) P)
  have htne : t ≠ 0 := by rintro rfl; simp at ht1
  have hP'mem : P' ∈ fibre (F' := K) P := mem_fibre.2 hP'
  -- the order of the norm
  have hnorm := ord_norm_place P htne
  rw [Finset.sum_eq_single P' (fun Q hQ hQP => by rw [ht0 Q hQ hQP, mul_zero])
    (fun h => absurd hP'mem h), ht1, mul_one] at hnorm
  -- the valuation of the norm, computed twice
  have hN0 : Algebra.norm F t ≠ 0 := (Algebra.norm_ne_zero_iff).2 htne
  have hv := congrArg vL (algebraMap_norm_eq_prod σ hσ hcard t)
  rw [hvF, P.valuation_eq_exp_neg_ord hN0, hnorm, ← WithZero.exp_nsmul, map_prod] at hv
  rw [Finset.prod_congr rfl fun i _ => valuation_apply_eq_exp hK hvF (σ i) hM htne, prod_exp,
    WithZero.exp_inj] at hv
  have hterm : ∀ i, scale hK hvF (σ i) hM * (placeOf hK hvF (σ i) hM).ord t =
      if placeOf hK hvF (σ i) hM = P' then (M : ℤ) / (Place.ramificationIdx F P' : ℤ) else (0 : ℤ) := by
    intro i
    split_ifs with h
    · have hs := scale_mul_ramificationIdx hK hvF (σ i) hM
      rw [h] at hs ⊢
      rw [ht1, mul_one, ← hs]
      have he : (0 : ℤ) < Place.ramificationIdx F P' := by exact_mod_cast Place.ramificationIdx_pos F P'
      rw [Int.mul_ediv_cancel _ he.ne']
    · rw [ht0 _ (mem_fibre.2 (restrict_placeOf hK hvF (σ i) hM)) h, mul_zero]
  simp only [Finset.sum_neg_distrib, hterm] at hv
  rw [← Finset.sum_filter, Finset.sum_const] at hv
  simp only [nsmul_eq_mul, smul_eq_mul, mul_neg, neg_inj] at hv
  -- `hv : M * f = #{i | P'_i = P'} * (M / e)`; conclude from $c e = M$
  set S := Finset.univ.filter fun i => placeOf hK hvF (σ i) hM = P'
  have hf : (1 : ℤ) ≤ Place.relativeDegree k F P' := by exact_mod_cast Place.one_le_relativeDegree k F P'
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  obtain ⟨i₀, hi₀⟩ : ∃ i, placeOf hK hvF (σ i) hM = P' := by
    by_contra hno
    push_neg at hno
    have hS : S = ∅ := Finset.filter_false_of_mem fun i _ => hno i
    rw [hS, Finset.card_empty, Nat.cast_zero, zero_mul] at hv
    nlinarith
  have hs := scale_mul_ramificationIdx hK hvF (σ i₀) hM
  rw [hi₀] at hs
  have he : (0 : ℤ) < Place.ramificationIdx F P' := by exact_mod_cast Place.ramificationIdx_pos F P'
  have hdiv : (M : ℤ) / Place.ramificationIdx F P' = scale hK hvF (σ i₀) hM := by
    rw [← hs, Int.mul_ediv_cancel _ he.ne']
  rw [hdiv] at hv
  have hc := scale_pos hK hvF (σ i₀) hM
  have key : (S.card : ℤ) * scale hK hvF (σ i₀) hM =
      Place.ramificationIdx F P' * Place.relativeDegree k F P' * scale hK hvF (σ i₀) hM := by
    rw [← hv, ← hs]
    ring
  exact mul_right_cancel₀ hc.ne' key

include hσ hcard in
/-- **Every place over $P$ is the place of some embedding.** -/
theorem exists_placeOf_eq (P' : Place k K) (hP' : P'.restrict k F = P) :
    ∃ i, placeOf hK hvF (σ i) hM = P' := by
  classical
  have h := card_placeOf_eq hK hvF σ hσ hcard hM P' hP'
  have he := Place.ramificationIdx_pos F P'
  have hf := Place.one_le_relativeDegree k F P'
  by_contra hno
  push_neg at hno
  rw [Finset.filter_false_of_mem fun i _ => hno i, Finset.card_empty, Nat.cast_zero] at h
  have : (0 : ℤ) < Place.ramificationIdx F P' * Place.relativeDegree k F P' := by positivity
  omega

include hσ hcard in
/-- **The geometric count of the fibre from the embeddings**: $M \sum_{P' \mid P} f(P') = \sum_i c_i$, where
$c_i = M / e(P'_i)$ is the scaling factor of $v_L \circ \sigma_i$. -/
theorem mul_sum_relativeDegree_eq :
    (M : ℤ) * ∑ P' ∈ fibre (F' := K) P, (Place.relativeDegree k F P' : ℤ) = ∑ i, scale hK hvF (σ i) hM := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := fibre (F' := K) P)
    (g := fun i => placeOf hK hvF (σ i) hM) (fun i _ => mem_fibre.2 (restrict_placeOf hK hvF (σ i) hM)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun P' hP' => ?_
  have hcount := card_placeOf_eq hK hvF σ hσ hcard hM P' (mem_fibre.1 hP')
  have he : (0 : ℤ) < Place.ramificationIdx F P' := by exact_mod_cast Place.ramificationIdx_pos F P'
  have hsc : ∀ i ∈ Finset.univ.filter fun i => placeOf hK hvF (σ i) hM = P',
      scale hK hvF (σ i) hM = (M : ℤ) / Place.ramificationIdx F P' := by
    intro i hi
    have hs := scale_mul_ramificationIdx hK hvF (σ i) hM
    rw [(Finset.mem_filter.1 hi).2] at hs
    rw [← hs, Int.mul_ediv_cancel _ he.ne']
  rw [Finset.sum_congr rfl hsc, Finset.sum_const, nsmul_eq_mul, hcount]
  obtain ⟨i₀, hi₀⟩ := exists_placeOf_eq hK hvF σ hσ hcard hM P' (mem_fibre.1 hP')
  have hs := scale_mul_ramificationIdx hK hvF (σ i₀) hM
  rw [hi₀] at hs
  rw [← hs, Int.mul_ediv_cancel _ he.ne']
  ring

end Count

end NumberFieldKB.ModularCurves
