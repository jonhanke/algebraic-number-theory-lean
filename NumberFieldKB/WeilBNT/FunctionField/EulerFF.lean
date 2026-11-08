import NumberFieldKB.WeilBNT.FunctionField.ZetaInputsProved
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.Complex.Basic

/-!
# Formal Euler products over the places of a function field

For a character $\chi$ of the divisor group of the function field $k$ and a set $T$ of places, the formal power
series
$$\sum_{\mathfrak a\succ0,\ \operatorname{supp}\mathfrak a\subseteq T}\chi(\mathfrak a)\,u^{\deg\mathfrak a}$$
is the product over $v\in T$ of the geometric series
$(1-\chi(v)u^{\deg v})^{-1}=\sum_{m\ge0}\chi(v)^mu^{m\deg v}$ (`eulerFactor`), the product converging in the
coefficientwise (pi) topology of $\mathbb C[[u]]$ (`hasProd_eulerFactor`). This is the Euler product of Weil VII.§7,
(11), in the variable $u=q^{-s}$.
-/

open scoped PowerSeries.WithPiTopology

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

/-- The geometric series $(1-cu^d)^{-1}=\sum_{m\ge0}c^mu^{md}$. -/
def eulerFactor (c : ℂ) (d : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if d ∣ n then c ^ (n / d) else 0

/-- `eulerFactor c d` is the inverse of $1-cu^d$ for $d\ge1$. -/
theorem eulerFactor_mul (c : ℂ) {d : ℕ} (hd : 0 < d) :
    eulerFactor c d * (1 - PowerSeries.C c * PowerSeries.X ^ d) = 1 := by
  ext n
  have h1 : eulerFactor c d * (1 - PowerSeries.C c * PowerSeries.X ^ d) =
      eulerFactor c d - PowerSeries.C c * (eulerFactor c d * PowerSeries.X ^ d) := by ring
  rw [h1, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_one]
  simp only [eulerFactor, PowerSeries.coeff_mk]
  by_cases hdn : d ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hdn
    have hq : (d + m) / d = m / d + 1 := by
      rw [add_comm d m]; exact Nat.add_div_right m hd
    simp [hd.ne', hq, Nat.dvd_add_right (dvd_refl d), pow_succ]
    split_ifs <;> ring
  · replace hdn := not_le.mp hdn
    have h0 : n / d = 0 := Nat.div_eq_of_lt hdn
    by_cases hn : n = 0
    · subst hn; simp [hd.ne']
    · have : ¬ d ∣ n := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h) (by omega)
      simp [hn, this, hdn.not_ge, hd.ne']

open Classical in
/-- The partial L-series $\sum_{\mathfrak a\succ0,\ \operatorname{supp}\mathfrak a\subseteq T}\chi(\mathfrak a)
u^{\deg\mathfrak a}$. -/
def divisorSeries (χ : Multiplicative (Divisor Fq k) →* ℂˣ) (T : Set (Place Fq k)) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    ∑ a ∈ (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset.filter
      (fun a => ∀ v ∈ a.support, v ∈ T), ((χ (Multiplicative.ofAdd a) : ℂˣ) : ℂ)

open Classical in
/-- Helper: the `n`-th coefficient $\sum_{\mathfrak a\succ0,\ \deg\mathfrak a=n,\ \operatorname{supp}\mathfrak a\subseteq U}
\chi(\mathfrak a)$ of the partial L-series (the coefficient formula of `divisorSeries`). -/
def effSum (χ : Multiplicative (Divisor Fq k) →* ℂˣ) (U : Set (Place Fq k)) (n : ℕ) : ℂ :=
  ∑ a ∈ (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset.filter
      (fun a => ∀ v ∈ a.support, v ∈ U), ((χ (Multiplicative.ofAdd a) : ℂˣ) : ℂ)

/-- `divisorSeries` is the series with coefficients `effSum`. -/
theorem divisorSeries_eq (χ : Multiplicative (Divisor Fq k) →* ℂˣ) (T : Set (Place Fq k)) :
    divisorSeries χ T = PowerSeries.mk (effSum χ T) := rfl

/-- Helper: membership in the index finset of `effSum`. -/
theorem mem_effIndex {U : Set (Place Fq k)} {n : ℕ} {a : Divisor Fq k}
    {_ : DecidablePred fun a : Divisor Fq k => ∀ v ∈ a.support, v ∈ U} :
    a ∈ (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset.filter
      (fun a => ∀ v ∈ a.support, v ∈ U) ↔ 0 ≤ a ∧ Divisor.deg a = n ∧ ∀ v ∈ a.support, v ∈ U := by
  simp [Set.Finite.mem_toFinset, and_assoc]

/-- Helper: a place in the support of an effective divisor has degree at most the degree of the divisor. -/
theorem degree_le_deg_of_effective {a : Divisor Fq k} (ha : 0 ≤ a) {v : Place Fq k} (hv : a v ≠ 0) :
    (v.degree : ℤ) ≤ Divisor.deg a := by
  have h0 : 0 ≤ a v := ha v
  have h1 : 1 ≤ a v := by omega
  rw [Divisor.deg_eq_sum]
  have hnn : ∀ w ∈ a.support, 0 ≤ a w * (w.degree : ℤ) := fun w _ =>
    mul_nonneg (ha w) (Nat.cast_nonneg _)
  have := Finset.single_le_sum hnn (Finsupp.mem_support_iff.mpr hv)
  have h2 : (v.degree : ℤ) ≤ a v * v.degree := by nlinarith
  omega

/-- Helper: the value of a divisor character on `b + single v 1`. -/
theorem char_add_single (χ : Multiplicative (Divisor Fq k) →* ℂˣ) (b : Divisor Fq k) (v : Place Fq k) :
    ((χ (Multiplicative.ofAdd (b + Finsupp.single v 1)) : ℂˣ) : ℂ) =
      ((χ (Multiplicative.ofAdd b) : ℂˣ) : ℂ) *
        ((χ (Multiplicative.ofAdd (Finsupp.single v 1)) : ℂˣ) : ℂ) := by
  rw [ofAdd_add, map_mul, Units.val_mul]

open Classical in
/-- Helper: the recursion for the coefficients when a place `v ∉ U` is adjoined, matching
$P_{U\cup\{v\}}\,(1-\chi(v)u^{\deg v})=P_U$. -/
theorem effSum_insert (χ : Multiplicative (Divisor Fq k) →* ℂˣ) (U : Set (Place Fq k)) (v : Place Fq k)
    (hv : v ∉ U) (n : ℕ) :
    effSum χ (insert v U) n = effSum χ U n +
      (if v.degree ≤ n then
        ((χ (Multiplicative.ofAdd (Finsupp.single v 1)) : ℂˣ) : ℂ) * effSum χ (insert v U) (n - v.degree)
      else 0) := by
  unfold effSum
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun a : Divisor Fq k => a v = 0)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext a
    rw [Finset.mem_filter, mem_effIndex, mem_effIndex]
    constructor
    · rintro ⟨⟨h0, h1, h2⟩, h3⟩
      refine ⟨h0, h1, fun w hw => ?_⟩
      rcases h2 w hw with h | h
      · subst h; exact absurd h3 (Finsupp.mem_support_iff.mp hw)
      · exact h
    · rintro ⟨h0, h1, h2⟩
      refine ⟨⟨h0, h1, fun w hw => Or.inr (h2 w hw)⟩, ?_⟩
      by_contra h
      exact hv (h2 v (Finsupp.mem_support_iff.mpr h))
  · by_cases hdn : v.degree ≤ n
    · rw [if_pos hdn, Finset.mul_sum]
      have hcast : (((n - v.degree : ℕ) : ℤ)) = (n : ℤ) - v.degree := by push_cast [Nat.cast_sub hdn]; ring
      refine Finset.sum_nbij' (fun a => a - Finsupp.single v 1) (fun b => b + Finsupp.single v 1)
        ?_ ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_filter, mem_effIndex] at ha
        rw [mem_effIndex]
        obtain ⟨⟨h0, h1, h2⟩, h3⟩ := ha
        have hpos : 0 ≤ a v := h0 v
        refine ⟨?_, ?_, ?_⟩
        · intro w
          by_cases hw : w = v
          · subst hw; simp; omega
          · simp [Finsupp.single_apply, Ne.symm hw]; exact h0 w
        · rw [map_sub, Divisor.deg_single, h1, hcast]; ring
        · intro w hw
          by_cases hwv : w = v
          · exact Or.inl hwv
          · apply h2
            have : (a - Finsupp.single v 1 : Divisor Fq k) w ≠ 0 := Finsupp.mem_support_iff.mp hw
            simp [Finsupp.single_apply, Ne.symm hwv] at this
            exact Finsupp.mem_support_iff.mpr this
      · intro b hb
        rw [mem_effIndex] at hb
        rw [Finset.mem_filter, mem_effIndex]
        obtain ⟨h0, h1, h2⟩ := hb
        have hpos : 0 ≤ b v := h0 v
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · intro w
          by_cases hw : w = v
          · subst hw; simp; omega
          · simp [Finsupp.single_apply, Ne.symm hw]; exact h0 w
        · rw [map_add, Divisor.deg_single, h1, hcast]; ring
        · intro w hw
          by_cases hwv : w = v
          · exact Or.inl hwv
          · apply h2
            have : (b + Finsupp.single v 1 : Divisor Fq k) w ≠ 0 := Finsupp.mem_support_iff.mp hw
            simp [Finsupp.single_apply, Ne.symm hwv] at this
            exact Finsupp.mem_support_iff.mpr this
        · simp; omega
      · intro a _; simp
      · intro b _; simp
      · intro a _
        rw [mul_comm, ← char_add_single, sub_add_cancel]
    · rw [if_neg hdn]
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_filter, mem_effIndex] at ha
      obtain ⟨⟨h0, h1, h2⟩, h3⟩ := ha
      exfalso
      have := degree_le_deg_of_effective h0 h3
      omega

/-- Helper: the only effective divisor supported in the empty set is `0`. -/
theorem eff_empty_aux {n : ℕ} {a : Divisor Fq k}
    {_ : DecidablePred fun a : Divisor Fq k => ∀ v ∈ a.support, v ∈ ((∅ : Finset (Place Fq k)) : Set (Place Fq k))}
    (ha : a ∈ (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset.filter
      (fun a => ∀ v ∈ a.support, v ∈ ((∅ : Finset (Place Fq k)) : Set (Place Fq k)))) :
    a = 0 ∧ (0 : ℤ) = n := by
  rw [mem_effIndex] at ha
  obtain ⟨_, h1, h2⟩ := ha
  have : a = 0 := by
    ext w
    by_contra hw
    simpa using h2 w (Finsupp.mem_support_iff.mpr hw)
  subst this
  exact ⟨rfl, by simpa using h1⟩

open Classical in
/-- Helper: for a finite set `S` of places the product of the Euler factors is the power series of the
partial L-series with support in `S`. -/
theorem prod_eulerFactor_eq (χ : Multiplicative (Divisor Fq k) →* ℂˣ) (S : Finset (Place Fq k)) :
    ∏ v ∈ S, eulerFactor ((χ (Multiplicative.ofAdd (Finsupp.single v 1)) : ℂˣ) : ℂ) v.degree =
      PowerSeries.mk (effSum χ (S : Set (Place Fq k))) := by
  induction S using Finset.induction_on with
  | empty =>
    ext n
    simp only [Finset.prod_empty, PowerSeries.coeff_one, PowerSeries.coeff_mk, effSum]
    by_cases hn : n = 0
    · subst hn
      rw [Finset.sum_eq_single (0 : Divisor Fq k)]
      · simp
      · intro b hb hne
        exact absurd (eff_empty_aux hb).1 hne
      · intro h
        exfalso
        apply h
        simp
    · rw [Finset.sum_eq_zero]
      · simp [hn]
      · intro a ha
        have := eff_empty_aux ha
        exfalso
        exact hn (by exact_mod_cast this.2.symm)
  | insert v S hvS ih =>
    rw [Finset.prod_insert hvS, ih]
    set c := ((χ (Multiplicative.ofAdd (Finsupp.single v 1)) : ℂˣ) : ℂ)
    have key : PowerSeries.mk (effSum χ ((insert v S : Finset (Place Fq k)) : Set (Place Fq k))) *
        (1 - PowerSeries.C c * PowerSeries.X ^ v.degree) = PowerSeries.mk (effSum χ (S : Set (Place Fq k))) := by
      ext n
      have h1 : PowerSeries.mk (effSum χ ((insert v S : Finset (Place Fq k)) : Set (Place Fq k))) *
          (1 - PowerSeries.C c * PowerSeries.X ^ v.degree) =
          PowerSeries.mk (effSum χ ((insert v S : Finset (Place Fq k)) : Set (Place Fq k))) -
          PowerSeries.C c * (PowerSeries.mk (effSum χ ((insert v S : Finset (Place Fq k)) : Set (Place Fq k))) *
            PowerSeries.X ^ v.degree) := by ring
      rw [h1, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
      simp only [PowerSeries.coeff_mk]
      have := effSum_insert χ (S : Set (Place Fq k)) v (by simpa using hvS) n
      rw [Finset.coe_insert]
      split_ifs at this ⊢ <;> linear_combination this
    rw [← key, mul_left_comm, eulerFactor_mul c v.degree_pos, mul_one]

/-- **The Euler product** $\sum_{\mathfrak a\succ0,\ \operatorname{supp}\mathfrak a\subseteq T}\chi(\mathfrak a)
u^{\deg\mathfrak a}=\prod_{v\in T}(1-\chi(v)u^{\deg v})^{-1}$, as an unconditionally convergent product of formal power
series in the coefficientwise topology. -/
theorem hasProd_eulerFactor (χ : Multiplicative (Divisor Fq k) →* ℂˣ) (T : Set (Place Fq k)) :
    HasProd (fun v : T => eulerFactor ((χ (Multiplicative.ofAdd (Finsupp.single (v : Place Fq k) 1)) : ℂˣ) : ℂ)
      (v : Place Fq k).degree) (divisorSeries χ T) := by
  rw [divisorSeries_eq]
  refine (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr fun n => ?_
  have hfin : {v : T | (v : Place Fq k).degree ≤ n}.Finite :=
    (Place.finite_setOf_degree_le (Fq := Fq) (k := k) n).preimage Subtype.val_injective.injOn
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.mpr ⟨hfin.toFinset, fun s hs => ?_⟩
  have hprod : ∏ b ∈ s, eulerFactor ((χ (Multiplicative.ofAdd (Finsupp.single (b : Place Fq k) 1)) : ℂˣ) : ℂ)
      (b : Place Fq k).degree = PowerSeries.mk (effSum χ ((s.map (Function.Embedding.subtype _) : Finset (Place Fq k))
        : Set (Place Fq k))) := by
    rw [← prod_eulerFactor_eq, Finset.prod_map]
    rfl
  beta_reduce
  rw [hprod, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  unfold effSum
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext a
  rw [mem_effIndex, mem_effIndex]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, h1, fun v hv => ?_⟩
    have hvT := h2 v hv
    have hle : (v.degree : ℤ) ≤ n := h1 ▸ degree_le_deg_of_effective h0 (Finsupp.mem_support_iff.mp hv)
    have : (⟨v, hvT⟩ : T) ∈ s :=
      hs (hfin.mem_toFinset.mpr (by exact_mod_cast hle))
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe]
    exact ⟨⟨v, hvT⟩, this, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, h1, fun v hv => ?_⟩
    have := h2 v hv
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at this
    obtain ⟨w, _, rfl⟩ := this
    exact w.2

end NumberFieldKB.WeilBNT.FF
