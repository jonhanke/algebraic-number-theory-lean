import NumberFieldKB.WeilBNT.PFieldUnits
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Weil, *Basic Number Theory*, II.§3: $1+P$ as a $\mathbb Z_p$-module (Prop. 9, Prop. 10: the module structure)

$K$ is a commutative $p$-field (`hK : IsPField K p`), $R$ = `pR hK`, $P$ = `pP hK`, $q$ = `pq hK`, and
$1+P=\{x:\operatorname{mod}_K(x-1)<1\}$, a subgroup of $K^\times$ (`onePlusPUnits hK`).

Weil (p. 33) regards $1+P$ as a multiplicatively written $\mathbb Z_p$-module. This file builds that structure.

* `modK_pow_sub_pow_le`: for $x\in1+P$ and natural numbers $a\equiv b\pmod{p^k}$,
  $\operatorname{mod}_K(x^a-x^b)\le q^{-(k+1)}$ (from I.§4, Lemma 5, `weil_I_4_lemma5`).
* `zpPowVal hK a x` $=x^a=\lim_n x^{a_n}$ for $a\in\mathbb Z_p$, $a_n$ = `PadicInt.appr a n` (natural numbers with
  $a\equiv a_n\pmod{p^n}$); `tendsto_pow_zpPowVal`: $x^{s_n}\to x^a$ for every sequence of natural numbers $s_n\to a$ in
  $\mathbb Z_p$.
* `zpPow hK a u` $=u^a$ on the subgroup $1+P$; `zpPow_natCast`, `zpPow_intCast`: it extends $u\mapsto u^n$;
  `zpPow_add`, `zpPow_mul`, `zpPow_one`, `mul_zpPow`: the module laws; `continuous_zpPow`: $(a,u)\mapsto u^a$ is
  continuous.
* `zpModule`: the resulting `Module ℤ_[p] (Additive (onePlusPUnits hK))` (Weil's multiplicative $\mathbb Z_p$-module).
* `weil_II_3_prop9_torsion`: an element of $1+P$ is a torsion element of this module if and only if it is a root of
  $1$; such roots have $p$-power order.
* `weil_II_3_prop9_torsion_finite` (characteristic $0$): the torsion of $1+P$ is a finite cyclic group of order $p^m$,
  where $m$ is the largest integer such that $K$ contains a primitive $p^m$-th root of $1$ (Prop. 9, last sentence).
* `weil_II_3_prop10_torsionFree` (characteristic $p$): $1+P$ has no torsion (no element $\neq1$ of finite order), as
  required by Prop. 10.
-/

open Topology Filter
open scoped NNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ} [hp : Fact p.Prime]

/-- $1+P=\{u\in K^\times:\operatorname{mod}_K(u-1)<1\}$, a subgroup of $K^\times$. -/
def onePlusPUnits (hK : IsPField K p) : Subgroup Kˣ where
  carrier := {u | modK K ((u : K) - 1) < 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    exact op_mul hK ha hb
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    have h1 := modK_eq_one_of_op hK ha
    have ha0 : (a : K) ≠ 0 := a.ne_zero
    have e : ((a⁻¹ : Kˣ) : K) - 1 = -((a : K) - 1) * (a : K)⁻¹ := by
      rw [Units.val_inv_eq_inv_val]; field_simp; ring
    rw [e, modK_mul, modK_neg, modK_inv ha0, h1, inv_one, mul_one]
    exact ha

theorem mem_onePlusPUnits {hK : IsPField K p} {u : Kˣ} :
    u ∈ onePlusPUnits hK ↔ modK K ((u : K) - 1) < 1 := Iff.rfl

/-- If $\operatorname{mod}_K(y-1)\le c<1$ then $\operatorname{mod}_K(y^n-1)\le c$. -/
theorem modK_pow_sub_one_le (hK : IsPField K p) {y : K} {c : ℝ≥0} (hc : c < 1)
    (hy : modK K (y - 1) ≤ c) (n : ℕ) : modK K (y ^ n - 1) ≤ c := by
  have hy1 : modK K y = 1 := modK_eq_one_of_op hK (lt_of_le_of_lt hy hc)
  induction n with
  | zero => simp
  | succ n ih =>
    have e : y ^ (n + 1) - 1 = y ^ n * (y - 1) + (y ^ n - 1) := by ring
    rw [e]
    refine (isUltrametricMod_of_isPField hK _ _).trans (max_le ?_ ih)
    rw [modK_mul, modK_pow, hy1, one_pow, one_mul]
    exact hy

/-- For $u,v$ of value at most $1$: $\operatorname{mod}_K(u^m-v^m)\le\operatorname{mod}_K(u-v)$. -/
theorem modK_pow_sub_pow_le_sub (hK : IsPField K p) {u v : K} (hu : modK K u ≤ 1) (hv : modK K v ≤ 1)
    (m : ℕ) : modK K (u ^ m - v ^ m) ≤ modK K (u - v) := by
  rw [← geom_sum₂_mul, modK_mul]
  have h1 : modK K (∑ i ∈ Finset.range m, u ^ i * v ^ (m - 1 - i)) ≤ 1 := by
    refine modK_sum_le hK _ _ fun i _ => ?_
    rw [modK_mul, modK_pow, modK_pow]
    calc _ ≤ 1 * 1 := mul_le_mul' (pow_le_one₀ zero_le hu) (pow_le_one₀ zero_le hv)
      _ = 1 := one_mul 1
  calc _ ≤ 1 * modK K (u - v) := mul_le_mul' h1 le_rfl
    _ = _ := one_mul _

/-- Convergence in $K$ is equivalent to the values of differences eventually lying below every $q^{-k}$. -/
theorem tendsto_iff_modK_le (hK : IsPField K p) {ι : Type*} {l : Filter ι} {f : ι → K} {L : K} :
    Tendsto f l (𝓝 L) ↔ ∀ k : ℕ, ∀ᶠ i in l, modK K (f i - L) ≤ qi hK ^ k := by
  constructor
  · intro h k
    have h0 := tendsto_sub_nhds_zero_iff.2 h
    exact hasBasis_nhds_zero_modK.tendsto_right_iff.1 h0 _ (pow_pos (qi_pos hK) k)
  · intro h
    rw [← tendsto_sub_nhds_zero_iff, hasBasis_nhds_zero_modK.tendsto_right_iff]
    intro ε hε
    have ht : Tendsto (fun n : ℕ => qi hK ^ n) atTop (𝓝 0) :=
      NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (qi_lt_one hK)
    obtain ⟨k, hk⟩ := (ht.eventually (ge_mem_nhds hε)).exists
    exact (h k).mono fun i hi => hi.trans hk

/-- Convergence in $\mathbb Z_p$ is equivalent to eventual divisibility of the differences by every power of $p$. -/
theorem tendsto_iff_dvd {ι : Type*} {l : Filter ι} {s : ι → ℤ_[p]} {a : ℤ_[p]} :
    Tendsto s l (𝓝 a) ↔ ∀ k : ℕ, ∀ᶠ n in l, (p : ℤ_[p]) ^ k ∣ s n - a := by
  constructor
  · intro h k
    have hε : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) := zpow_pos (by exact_mod_cast hp.out.pos) _
    filter_upwards [Metric.tendsto_nhds.1 h _ hε] with n hn
    rw [dist_eq_norm] at hn
    exact Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ k).1 hn.le)
  · intro h
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hp1 : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hp1
    filter_upwards [h k] with n hn
    rw [dist_eq_norm]
    have := (PadicInt.norm_le_pow_iff_mem_span_pow (s n - a) k).2 (Ideal.mem_span_singleton.2 hn)
    refine this.trans_lt ?_
    rwa [zpow_neg, zpow_natCast, ← inv_pow]

theorem tendsto_appr (a : ℤ_[p]) : Tendsto (fun n => (PadicInt.appr a n : ℤ_[p])) atTop (𝓝 a) := by
  rw [tendsto_iff_dvd]
  intro k
  filter_upwards [eventually_ge_atTop k] with n hn
  have h2 : (p : ℤ_[p]) ^ k ∣ a - PadicInt.appr a n :=
    (pow_dvd_pow _ hn).trans (Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a))
  have := dvd_neg.2 h2
  rwa [neg_sub] at this

theorem int_dvd_of_dvd_sub {k m n : ℕ} (h : (p : ℤ_[p]) ^ k ∣ (m : ℤ_[p]) - n) :
    (p : ℤ) ^ k ∣ (m : ℤ) - n := by
  rw [← PadicInt.pow_p_dvd_int_iff]
  push_cast
  exact h

/-- The congruence estimate behind the $p$-adic continuity of $a\mapsto x^a$: if $x\in1+P$ and $p^k\mid a-b$ then
$\operatorname{mod}_K(x^a-x^b)\le q^{-(k+1)}$. -/
theorem modK_pow_sub_pow_le (hK : IsPField K p) {x : K} (hx : modK K (x - 1) < 1) {a b k : ℕ}
    (h : ((p : ℤ) ^ k) ∣ ((a : ℤ) - b)) : modK K (x ^ a - x ^ b) ≤ qi hK ^ (k + 1) := by
  have hx1 : modK K x = 1 := modK_eq_one_of_op hK hx
  have hxq : modK K (x - 1) ≤ qi hK := modK_le_qi_of_lt_one hK hx
  have key : ∀ {a b : ℕ}, b ≤ a → ((p : ℤ) ^ k ∣ (a : ℤ) - b) →
      modK K (x ^ a - x ^ b) ≤ qi hK ^ (k + 1) := by
    intro a b hba h
    have h' : p ^ k ∣ a - b := by
      have : ((a - b : ℕ) : ℤ) = (a : ℤ) - b := by push_cast [Nat.cast_sub hba]; ring
      rw [← this] at h
      exact_mod_cast h
    obtain ⟨c, hc⟩ := h'
    have ha : a = b + p ^ k * c := by
      have := Nat.sub_add_cancel hba
      rw [hc] at this
      omega
    have e : x ^ a - x ^ b = x ^ b * ((x ^ (p ^ k)) ^ c - 1) := by
      rw [ha, pow_add, ← pow_mul]; ring
    rw [e, modK_mul, modK_pow, hx1, one_pow, one_mul]
    have h5 := weil_I_4_lemma5 hK k (mem_onePlusP.2 (by simpa using hxq))
    rw [mem_onePlusP] at h5
    exact modK_pow_sub_one_le hK (pow_lt_one₀ zero_le (qi_lt_one hK) (by omega)) h5 c
  rcases le_total b a with hba | hab
  · exact key hba h
  · have h2 : (p : ℤ) ^ k ∣ (b : ℤ) - a := by
      have := dvd_neg.2 h
      rwa [neg_sub] at this
    have := key hab h2
    rwa [← modK_neg, neg_sub] at this

/-- $x^a$ for $x\in1+P$ and $a\in\mathbb Z_p$: the limit of $x^{a_n}$, $a_n$ = `PadicInt.appr a n`. (For $x\notin1+P$
the value is a junk value.) -/
def zpPowVal (_hK : IsPField K p) (a : ℤ_[p]) (x : K) : K :=
  limUnder atTop fun n => x ^ PadicInt.appr a n

/-- The approximating sequence $x^{a_n}$ converges (consecutive terms are congruent modulo $p^n$). -/
theorem tendsto_zpPowVal_appr (hK : IsPField K p) {x : K} (hx : modK K (x - 1) < 1) (a : ℤ_[p]) :
    Tendsto (fun n => x ^ PadicInt.appr a n) atTop (𝓝 (zpPowVal hK a x)) := by
  refine tendsto_nhds_limUnder ?_
  refine exists_tendsto_of_step hK fun n => ?_
  have h1 : (p : ℤ) ^ n ∣ ((a.appr (n + 1) : ℕ) : ℤ) - (a.appr n : ℕ) := by
    have h0 : ((p ^ n : ℕ) : ℤ) ∣ ((a.appr (n + 1) - a.appr n : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 (PadicInt.dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n))
    rw [Nat.cast_sub (PadicInt.appr_mono a (Nat.le_succ n))] at h0
    simpa using h0
  exact (modK_pow_sub_pow_le hK hx h1).trans
    (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (Nat.le_succ n))

/-- Uniform estimate: if $p^k\mid a-m$ then $\operatorname{mod}_K(x^a-x^m)\le q^{-(k+1)}$. -/
theorem modK_zpPowVal_sub_pow_le (hK : IsPField K p) {x : K} (hx : modK K (x - 1) < 1) (a : ℤ_[p])
    {m k : ℕ} (h : (p : ℤ_[p]) ^ k ∣ a - m) :
    modK K (zpPowVal hK a x - x ^ m) ≤ qi hK ^ (k + 1) := by
  have hL' := tendsto_zpPowVal_appr hK hx a
  have hcl : Tendsto (fun n => modK K (x ^ a.appr n - x ^ m)) atTop
      (𝓝 (modK K (zpPowVal hK a x - x ^ m))) :=
    (continuous_modK.tendsto _).comp (hL'.sub_const _)
  refine le_of_tendsto hcl ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  apply modK_pow_sub_pow_le hK hx
  apply int_dvd_of_dvd_sub
  have h2 : (p : ℤ_[p]) ^ k ∣ a - PadicInt.appr a n :=
    (pow_dvd_pow _ hn).trans (Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a))
  have e : (PadicInt.appr a n : ℤ_[p]) - m = (a - m) - (a - PadicInt.appr a n) := by ring
  rw [e]
  exact dvd_sub h h2

/-- $x^{s_n}\to x^a$ for every sequence of natural numbers $s_n$ tending to $a$ in $\mathbb Z_p$. -/
theorem tendsto_pow_zpPowVal (hK : IsPField K p) {x : K} (hx : modK K (x - 1) < 1) (a : ℤ_[p])
    {s : ℕ → ℕ} (hs : Tendsto (fun n => (s n : ℤ_[p])) atTop (𝓝 a)) :
    Tendsto (fun n => x ^ s n) atTop (𝓝 (zpPowVal hK a x)) := by
  rw [tendsto_iff_modK_le hK]
  intro k
  filter_upwards [tendsto_iff_dvd.1 hs k] with n hn
  have h2 : (p : ℤ_[p]) ^ k ∣ a - s n := by
    have := dvd_neg.2 hn
    rwa [neg_sub] at this
  have := modK_zpPowVal_sub_pow_le hK hx a h2
  rw [← modK_neg, neg_sub]
  exact this.trans (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (Nat.le_succ k))

theorem zpPowVal_natCast (hK : IsPField K p) {x : K} (hx : modK K (x - 1) < 1) (n : ℕ) :
    zpPowVal hK (n : ℤ_[p]) x = x ^ n :=
  tendsto_nhds_unique (tendsto_pow_zpPowVal hK hx (n : ℤ_[p]) (s := fun _ => n) tendsto_const_nhds)
    tendsto_const_nhds

theorem zpPowVal_mem (hK : IsPField K p) {x : K} (hx : modK K (x - 1) < 1) (a : ℤ_[p]) :
    modK K (zpPowVal hK a x - 1) < 1 := by
  have hL' := tendsto_zpPowVal_appr hK hx a
  have hcl : Tendsto (fun n => modK K (x ^ a.appr n - 1)) atTop
      (𝓝 (modK K (zpPowVal hK a x - 1))) :=
    (continuous_modK.tendsto _).comp (hL'.sub_const _)
  have : modK K (zpPowVal hK a x - 1) ≤ qi hK :=
    le_of_tendsto hcl (Eventually.of_forall fun n =>
      modK_pow_sub_one_le hK (qi_lt_one hK) (modK_le_qi_of_lt_one hK hx) _)
  exact lt_of_le_of_lt this (qi_lt_one hK)

/-- Joint estimate: if $p^k\mid a-a'$ then
$\operatorname{mod}_K(x^a-y^{a'})\le\max(\operatorname{mod}_K(x-y),q^{-(k+1)})$. -/
theorem modK_zpPowVal_sub_le (hK : IsPField K p) {x y : K} (hx : modK K (x - 1) < 1)
    (hy : modK K (y - 1) < 1) {a a' : ℤ_[p]} {k : ℕ} (h : (p : ℤ_[p]) ^ k ∣ a - a') :
    modK K (zpPowVal hK a x - zpPowVal hK a' y) ≤ max (modK K (x - y)) (qi hK ^ (k + 1)) := by
  have hm : (p : ℤ_[p]) ^ k ∣ a - (a.appr k : ℕ) := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k a)
  have hm' : (p : ℤ_[p]) ^ k ∣ a' - (a'.appr k : ℕ) :=
    Ideal.mem_span_singleton.1 (PadicInt.appr_spec k a')
  have hmm : (p : ℤ_[p]) ^ k ∣ ((a.appr k : ℕ) : ℤ_[p]) - (a'.appr k : ℕ) := by
    have e : ((a.appr k : ℕ) : ℤ_[p]) - (a'.appr k : ℕ) = (a' - (a'.appr k : ℕ)) - (a - (a.appr k : ℕ)) + (a - a') := by
      ring
    rw [e]
    exact dvd_add (dvd_sub hm' hm) h
  have c1 := modK_zpPowVal_sub_pow_le hK hx a hm
  have c2 := modK_zpPowVal_sub_pow_le hK hy a' hm'
  have c3 := modK_pow_sub_pow_le_sub hK (modK_eq_one_of_op hK hx).le (modK_eq_one_of_op hK hy).le (a.appr k)
  have c4 := modK_pow_sub_pow_le hK hy (int_dvd_of_dvd_sub hmm)
  set M := max (modK K (x - y)) (qi hK ^ (k + 1))
  have hA : modK K (zpPowVal hK a x - x ^ a.appr k) ≤ M := c1.trans (le_max_right _ _)
  have hB : modK K (x ^ a.appr k - y ^ a.appr k) ≤ M := c3.trans (le_max_left _ _)
  have hC : modK K (y ^ a.appr k - y ^ a'.appr k) ≤ M := c4.trans (le_max_right _ _)
  have hD : modK K (zpPowVal hK a' y - y ^ a'.appr k) ≤ M := c2.trans (le_max_right _ _)
  have e : zpPowVal hK a x - zpPowVal hK a' y =
      ((zpPowVal hK a x - x ^ a.appr k) + (x ^ a.appr k - y ^ a.appr k)) +
        ((y ^ a.appr k - y ^ a'.appr k) - (zpPowVal hK a' y - y ^ a'.appr k)) := by ring
  rw [e]
  exact (isUltrametricMod_of_isPField hK _ _).trans
    (max_le ((isUltrametricMod_of_isPField hK _ _).trans (max_le hA hB))
      ((modK_sub_le_max hK _ _).trans (max_le hC hD)))

theorem zpPowVal_ne_zero (hK : IsPField K p) {x : K} (hx : modK K (x - 1) < 1) (a : ℤ_[p]) :
    zpPowVal hK a x ≠ 0 := by
  intro h
  have := zpPowVal_mem hK hx a
  rw [h, zero_sub, modK_neg, modK_one'] at this
  exact lt_irrefl _ this

theorem zpPowVal_add (hK : IsPField K p) {x : K} (hx : modK K (x - 1) < 1) (a b : ℤ_[p]) :
    zpPowVal hK (a + b) x = zpPowVal hK a x * zpPowVal hK b x := by
  have h3 := tendsto_pow_zpPowVal hK hx (a + b) (s := fun n => a.appr n + b.appr n)
    (by push_cast; exact (tendsto_appr a).add (tendsto_appr b))
  have h4 := (tendsto_zpPowVal_appr hK hx a).mul (tendsto_zpPowVal_appr hK hx b)
  simp only [pow_add] at h3
  exact tendsto_nhds_unique h3 h4

theorem mul_zpPowVal (hK : IsPField K p) {x y : K} (hx : modK K (x - 1) < 1) (hy : modK K (y - 1) < 1)
    (a : ℤ_[p]) : zpPowVal hK a (x * y) = zpPowVal hK a x * zpPowVal hK a y := by
  have h3 := tendsto_pow_zpPowVal hK (op_mul hK hx hy) a (s := fun n => a.appr n) (tendsto_appr a)
  have h4 := (tendsto_zpPowVal_appr hK hx a).mul (tendsto_zpPowVal_appr hK hy a)
  simp only [mul_pow] at h3
  exact tendsto_nhds_unique h3 h4

theorem one_zpPowVal (hK : IsPField K p) (a : ℤ_[p]) : zpPowVal hK a (1 : K) = 1 := by
  have h1 : modK K ((1 : K) - 1) < 1 := by rw [sub_self, modK_zero']; exact one_pos
  have := tendsto_pow_zpPowVal hK h1 a (s := fun n => a.appr n) (tendsto_appr a)
  simp only [one_pow] at this
  exact tendsto_nhds_unique this tendsto_const_nhds

theorem zpPowVal_pow (hK : IsPField K p) {x : K} (hx : modK K (x - 1) < 1) (m : ℕ) (a : ℤ_[p]) :
    zpPowVal hK a (x ^ m) = zpPowVal hK ((m : ℤ_[p]) * a) x := by
  have h3 := tendsto_pow_zpPowVal hK (op_pow hK hx m) a (s := fun n => a.appr n) (tendsto_appr a)
  have h4 := tendsto_pow_zpPowVal hK hx ((m : ℤ_[p]) * a) (s := fun n => m * a.appr n)
    (by push_cast; exact tendsto_const_nhds.mul (tendsto_appr a))
  simp only [← pow_mul] at h3
  exact tendsto_nhds_unique h3 h4

theorem zpPowVal_mul (hK : IsPField K p) {x : K} (hx : modK K (x - 1) < 1) (a b : ℤ_[p]) :
    zpPowVal hK (a * b) x = zpPowVal hK a (zpPowVal hK b x) := by
  have hy := zpPowVal_mem hK hx b
  have hq : ∀ k : ℕ, qi hK ^ (k + 1) ≤ qi hK ^ k := fun k =>
    pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (Nat.le_succ k)
  have h2 : Tendsto (fun n => zpPowVal hK ((b.appr n : ℤ_[p]) * a) x) atTop
      (𝓝 (zpPowVal hK (b * a) x)) := by
    rw [tendsto_iff_modK_le hK]
    intro k
    filter_upwards [tendsto_iff_dvd.1 (tendsto_appr b) k] with n hn
    have hd : (p : ℤ_[p]) ^ k ∣ (b.appr n : ℤ_[p]) * a - b * a := by
      rw [← sub_mul]; exact dvd_mul_of_dvd_left hn a
    have := modK_zpPowVal_sub_le hK hx hx hd
    rw [sub_self, modK_zero'] at this
    exact this.trans (max_le zero_le (hq k))
  have h3 : Tendsto (fun n => zpPowVal hK a (x ^ b.appr n)) atTop
      (𝓝 (zpPowVal hK a (zpPowVal hK b x))) := by
    rw [tendsto_iff_modK_le hK]
    intro k
    have hc := (tendsto_iff_modK_le hK).1 (tendsto_zpPowVal_appr hK hx b) k
    filter_upwards [hc] with n hn
    have := modK_zpPowVal_sub_le hK (op_pow hK hx (b.appr n)) hy (a := a) (a' := a) (k := k) (by simp)
    exact this.trans (max_le hn (hq k))
  have h4 : ∀ n, zpPowVal hK a (x ^ b.appr n) = zpPowVal hK ((b.appr n : ℤ_[p]) * a) x :=
    fun n => zpPowVal_pow hK hx _ a
  rw [mul_comm]
  exact tendsto_nhds_unique h2 (h3.congr h4)

theorem onePlusPUnits_ext {hK : IsPField K p} {u v : onePlusPUnits hK}
    (h : ((u : Kˣ) : K) = ((v : Kˣ) : K)) : u = v :=
  Subtype.ext (Units.ext h)

/-- $u^a$ for $u\in1+P$ and $a\in\mathbb Z_p$, as an element of the subgroup $1+P$. -/
def zpPow (hK : IsPField K p) (a : ℤ_[p]) (u : onePlusPUnits hK) : onePlusPUnits hK :=
  ⟨Units.mk0 (zpPowVal hK a ((u : Kˣ) : K)) (zpPowVal_ne_zero hK u.2 a), by
    show modK K (zpPowVal hK a ((u : Kˣ) : K) - 1) < 1
    exact zpPowVal_mem hK u.2 a⟩

@[simp] theorem coe_zpPow (hK : IsPField K p) (a : ℤ_[p]) (u : onePlusPUnits hK) :
    (((zpPow hK a u : onePlusPUnits hK) : Kˣ) : K) = zpPowVal hK a ((u : Kˣ) : K) := rfl

theorem zpPow_natCast (hK : IsPField K p) (n : ℕ) (u : onePlusPUnits hK) : zpPow hK (n : ℤ_[p]) u = u ^ n := by
  apply onePlusPUnits_ext
  rw [coe_zpPow, zpPowVal_natCast hK u.2 n]
  simp

theorem zpPow_intCast (hK : IsPField K p) (n : ℤ) (u : onePlusPUnits hK) : zpPow hK (n : ℤ_[p]) u = u ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simpa using zpPow_natCast hK k u
  · apply onePlusPUnits_ext
    have hx := u.2
    have h0 : zpPowVal hK 0 ((u : Kˣ) : K) = 1 := by simpa using zpPowVal_natCast hK hx 0
    have h1 : zpPowVal hK (-(k : ℤ_[p])) ((u : Kˣ) : K) * ((u : Kˣ) : K) ^ k = 1 := by
      have := zpPowVal_add hK hx (-(k : ℤ_[p])) k
      rw [neg_add_cancel, h0, zpPowVal_natCast hK hx k] at this
      exact this.symm
    have h2 := eq_inv_of_mul_eq_one_left h1
    push_cast
    rw [coe_zpPow, h2]
    simp [zpow_neg]

theorem zpPow_zero (hK : IsPField K p) (u : onePlusPUnits hK) : zpPow hK 0 u = 1 := by
  simpa using zpPow_natCast hK 0 u

theorem zpPow_one (hK : IsPField K p) (u : onePlusPUnits hK) : zpPow hK 1 u = u := by
  simpa using zpPow_natCast hK 1 u

theorem zpPow_add (hK : IsPField K p) (a b : ℤ_[p]) (u : onePlusPUnits hK) :
    zpPow hK (a + b) u = zpPow hK a u * zpPow hK b u := by
  apply onePlusPUnits_ext
  simp only [coe_zpPow, Subgroup.coe_mul, Units.val_mul]
  exact zpPowVal_add hK u.2 a b

theorem zpPow_mul (hK : IsPField K p) (a b : ℤ_[p]) (u : onePlusPUnits hK) :
    zpPow hK (a * b) u = zpPow hK a (zpPow hK b u) :=
  onePlusPUnits_ext (zpPowVal_mul hK u.2 a b)

theorem mul_zpPow (hK : IsPField K p) (a : ℤ_[p]) (u v : onePlusPUnits hK) :
    zpPow hK a (u * v) = zpPow hK a u * zpPow hK a v := by
  apply onePlusPUnits_ext
  simp only [coe_zpPow, Subgroup.coe_mul, Units.val_mul]
  exact mul_zpPowVal hK u.2 v.2 a

theorem one_zpPow (hK : IsPField K p) (a : ℤ_[p]) : zpPow hK a 1 = 1 := by
  apply onePlusPUnits_ext
  simp only [coe_zpPow, Subgroup.coe_one, Units.val_one]
  exact one_zpPowVal hK a

/-- $(a,u)\mapsto u^a$ is continuous on $\mathbb Z_p\times(1+P)$ (values in $K$). -/
theorem continuous_zpPow (hK : IsPField K p) :
    Continuous fun q : ℤ_[p] × onePlusPUnits hK => (((zpPow hK q.1 q.2 : onePlusPUnits hK) : Kˣ) : K) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a0, u0⟩
  show Tendsto (fun q : ℤ_[p] × onePlusPUnits hK => zpPowVal hK q.1 ((q.2 : Kˣ) : K)) (𝓝 (a0, u0))
    (𝓝 (zpPowVal hK a0 ((u0 : Kˣ) : K)))
  rw [tendsto_iff_modK_le hK]
  intro k
  have hA : ∀ᶠ q in 𝓝 (a0, u0), (p : ℤ_[p]) ^ k ∣ q.1 - a0 :=
    tendsto_iff_dvd.1 (continuous_fst.tendsto (a0, u0)) k
  have hB : Tendsto (fun q : ℤ_[p] × onePlusPUnits hK => ((q.2 : Kˣ) : K)) (𝓝 (a0, u0))
      (𝓝 ((u0 : Kˣ) : K)) :=
    ((Units.continuous_val.comp continuous_subtype_val).comp continuous_snd).tendsto (a0, u0)
  filter_upwards [hA, (tendsto_iff_modK_le hK).1 hB k] with q hq1 hq2
  have := modK_zpPowVal_sub_le hK q.2.2 u0.2 hq1
  exact this.trans (max_le hq2
    (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (Nat.le_succ k)))

/-- **$1+P$ as a $\mathbb Z_p$-module** (Weil, II.§3, p. 33): `Additive (onePlusPUnits hK)` with $a\cdot u=u^a$. -/
instance zpModule (hK : IsPField K p) : Module ℤ_[p] (Additive (onePlusPUnits hK)) where
  smul a u := Additive.ofMul (zpPow hK a u.toMul)
  one_smul u := zpPow_one hK u.toMul
  mul_smul a b u := zpPow_mul hK a b u.toMul
  smul_zero a := one_zpPow hK a
  smul_add a u v := mul_zpPow hK a u.toMul v.toMul
  add_smul a b u := zpPow_add hK a b u.toMul
  zero_smul u := zpPow_zero hK u.toMul

theorem zpModule_smul_def (hK : IsPField K p) (a : ℤ_[p]) (u : Additive (onePlusPUnits hK)) :
    a • u = Additive.ofMul (zpPow hK a u.toMul) := rfl

/-- If $v\in1+P$ and $v^n=1$ with $n$ prime to $p$ then $v=1$ (injectivity of $x\mapsto x^n$ on $1+P$). -/
theorem eq_one_of_pow_coprime (hK : IsPField K p) (v : onePlusPUnits hK) {n : ℕ}
    (hn : Nat.Coprime n p) (h : v ^ n = 1) : v = 1 := by
  have hb := weil_II_3_prop8_aut hK hn (ν := 1) le_rfl
  have hv : ((v : Kˣ) : K) ∈ onePlusP hK 1 :=
    mem_onePlusP.2 (by simpa using modK_le_qi_of_lt_one hK v.2)
  have h1 : (1 : K) ∈ onePlusP hK 1 := by
    rw [mem_onePlusP, sub_self, modK_zero']; exact zero_le
  have h2 : ((v : Kˣ) : K) ^ n = (1 : K) ^ n := by
    have := congrArg (fun w : onePlusPUnits hK => ((w : Kˣ) : K)) h
    simpa using this
  exact onePlusPUnits_ext (by simpa using hb.injOn hv h1 h2)

/-- **Weil, II.§3, Prop. 9 (torsion)**: an element $u$ of $1+P$ is annihilated by some $a\neq0$ of $\mathbb Z_p$ if and
only if $u$ is a root of $1$, and then $u^{p^k}=1$ for some $k$. -/
@[kb "weil1973bnt" "Ch. II, §3, Prop. 9 (torsion of the Z_p-module 1 + P is its p-power roots of unity)"]
theorem weil_II_3_prop9_torsion (hK : IsPField K p) (u : onePlusPUnits hK) :
    ((∃ a : ℤ_[p], a ≠ 0 ∧ a • Additive.ofMul u = 0) ↔ ∃ n : ℕ, 0 < n ∧ u ^ n = 1) ∧
    ((∃ n : ℕ, 0 < n ∧ u ^ n = 1) ↔ ∃ k : ℕ, u ^ (p ^ k) = 1) := by
  have key : ∀ n : ℕ, 0 < n → u ^ n = 1 → ∃ k, u ^ (p ^ k) = 1 := by
    intro n hn h
    obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
    exact ⟨e, eq_one_of_pow_coprime hK (u ^ (p ^ e))
      ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn').symm (by rw [← pow_mul]; exact h)⟩
  have h2 : (∃ n : ℕ, 0 < n ∧ u ^ n = 1) ↔ ∃ k : ℕ, u ^ (p ^ k) = 1 :=
    ⟨fun ⟨n, hn, h⟩ => key n hn h, fun ⟨k, h⟩ => ⟨p ^ k, pow_pos hp.out.pos k, h⟩⟩
  refine ⟨?_, h2⟩
  constructor
  · rintro ⟨a, ha, h⟩
    have h' : zpPow hK a u = 1 := h
    have hspec := PadicInt.unitCoeff_spec ha
    set w : ℤ_[p]ˣ := PadicInt.unitCoeff ha
    set k := a.valuation
    have hv : zpPow hK ((p : ℤ_[p]) ^ k) u = u ^ (p ^ k) := by
      have := zpPow_natCast hK (p ^ k) u
      simpa using this
    have h3 : zpPow hK (w : ℤ_[p]) (u ^ (p ^ k)) = 1 := by
      rw [← hv, ← zpPow_mul, ← hspec]; exact h'
    have h4 : u ^ (p ^ k) = 1 := by
      have := congrArg (zpPow hK ((w⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) h3
      rw [← zpPow_mul, Units.inv_mul, zpPow_one, one_zpPow] at this
      exact this
    exact h2.2 ⟨k, h4⟩
  · rintro ⟨n, hn, h⟩
    refine ⟨n, Nat.cast_ne_zero.2 hn.ne', ?_⟩
    change Additive.ofMul (zpPow hK (n : ℤ_[p]) u) = Additive.ofMul 1
    rw [zpPow_natCast, h]

/-- A root of $1$ of $p$-power order lies in $1+P$. -/
theorem modK_sub_one_lt_of_pow_prime (hK : IsPField K p) {z : K} {k : ℕ} (hz : z ^ (p ^ k) = 1) :
    modK K (z - 1) < 1 := by
  have hz1 : modK K z = 1 := by
    have : modK K z ^ (p ^ k) = 1 := by rw [← modK_pow, hz, modK_one']
    exact (pow_eq_one_iff_of_nonneg zero_le (pow_pos hp.out.pos k).ne').1 this
  obtain ⟨f, hf, hqf⟩ := weil_I_4_thm6_residue hK
  have h1 : Tendsto (fun n : ℕ => z ^ (pq hK ^ n)) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k] with n hn
    have : p ^ k ∣ pq hK ^ n := by
      rw [hqf, ← pow_mul]; exact pow_dvd_pow p (by nlinarith)
    obtain ⟨c, hc⟩ := this
    rw [hc, pow_mul, hz, one_pow]
  have h2 := tendsto_nhds_unique (teich_tendsto hK hz1) h1
  have h3 := teich_sub_le hK hz1
  rw [h2] at h3
  rw [← modK_neg, neg_sub]
  exact lt_of_le_of_lt h3 (qi_lt_one hK)

theorem modK_choose_le_p (hK : IsPField K p) {i : ℕ} (hi0 : i ≠ 0) (hip : i < p) :
    modK K ((p.choose i : ℕ) : K) ≤ modK K (p : K) := by
  obtain ⟨c, hc⟩ : p ∣ p.choose i := by
    simpa using Nat.Prime.dvd_choose_pow (n := 1) hK.1 hi0 (by simpa using hip.ne)
  rw [hc, Nat.cast_mul, modK_mul]
  calc modK K (p : K) * modK K (c : K) ≤ modK K (p : K) * 1 :=
        mul_le_mul' le_rfl (modK_natCast_le_one hK c)
    _ = _ := mul_one _

/-- If $y\neq0$ is small compared to $p$ then $(1+y)^p\neq1$. -/
theorem pow_prime_ne_one_of_close (hK : IsPField K p) {y : K} (hy0 : y ≠ 0) (hm : modK K y < 1)
    (hc : modK K y ^ (p - 1) < modK K (p : K)) : (1 + y) ^ p ≠ 1 := by
  intro h
  have hmpos : 0 < modK K y := modK_pos_iff.2 hy0
  have hcpos : 0 < modK K (p : K) := lt_of_le_of_lt zero_le hc
  have hp2 : 2 ≤ p := hK.1.two_le
  have hexp : (1 + y) ^ p - 1 =
      (p : K) * y + ∑ i ∈ Finset.range (p - 1), y ^ (i + 2) * (p.choose (i + 2) : K) := by
    have e : p + 1 = (p - 1) + 1 + 1 := by omega
    rw [add_comm, add_pow, e, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, zero_add, pow_one,
      Nat.choose_one_right]
    ring
  set R := ∑ i ∈ Finset.range (p - 1), y ^ (i + 2) * (p.choose (i + 2) : K) with hR
  have hm2 : modK K y ^ 2 < modK K y := by
    rw [pow_two]; exact mul_lt_of_lt_one_right hmpos hm
  have hB1 : modK K (p : K) * modK K y ^ 2 < modK K (p : K) * modK K y :=
    mul_lt_mul_of_pos_left hm2 hcpos
  have hB2 : modK K y ^ p < modK K (p : K) * modK K y := by
    have e : p = (p - 1) + 1 := by omega
    calc modK K y ^ p = modK K y ^ (p - 1) * modK K y := by rw [← pow_succ, ← e]
      _ < modK K (p : K) * modK K y := mul_lt_mul_of_pos_right hc hmpos
  have hRlt : modK K R < modK K ((p : K) * y) := by
    rw [modK_mul]
    refine lt_of_le_of_lt (modK_sum_le hK _ _ (c := max (modK K (p : K) * modK K y ^ 2) (modK K y ^ p))
      fun i hi => ?_) (max_lt hB1 hB2)
    rw [Finset.mem_range] at hi
    rw [modK_mul, modK_pow]
    by_cases hip : i + 2 < p
    · have h2 := modK_choose_le_p hK (by omega : i + 2 ≠ 0) hip
      have h3 : modK K y ^ (i + 2) ≤ modK K y ^ 2 :=
        pow_le_pow_of_le_one zero_le hm.le (by omega)
      refine le_max_of_le_left ?_
      calc modK K y ^ (i + 2) * modK K ((p.choose (i + 2) : ℕ) : K)
          ≤ modK K y ^ 2 * modK K (p : K) := mul_le_mul' h3 h2
        _ = _ := mul_comm _ _
    · have hi' : i + 2 = p := by omega
      rw [hi', Nat.choose_self, Nat.cast_one, modK_one', mul_one]
      exact le_max_right _ _
  have h4 := modK_add_eq_of_lt (isUltrametricMod_of_isPField hK) hRlt
  rw [← hexp, h, sub_self, modK_zero'] at h4
  have : 0 < modK K ((p : K) * y) := by
    rw [modK_mul]; exact mul_pos hcpos hmpos
  rw [← h4] at this
  exact lt_irrefl _ this

/-- In characteristic $0$ there is $N\ge1$ such that no root of $1$ of $p$-power order other than $1$ lies
in $1+P^N$. -/
theorem exists_close_N [CharZero K] (hK : IsPField K p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ ζ : K, (∃ k, ζ ^ (p ^ k) = 1) → modK K (ζ - 1) ≤ qi hK ^ N → ζ = 1 := by
  have hc : 0 < modK K (p : K) := modK_pos_iff.2 (Nat.cast_ne_zero.2 hK.1.ne_zero)
  have ht : Tendsto (fun n : ℕ => qi hK ^ n) atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (qi_lt_one hK)
  obtain ⟨M, hM⟩ := (ht.eventually (gt_mem_nhds hc)).exists
  refine ⟨M + 1, by omega, ?_⟩
  have hq1 : qi hK ^ (M + 1) < 1 := pow_lt_one₀ zero_le (qi_lt_one hK) (by omega)
  rintro ζ ⟨k, hk⟩ hclose
  induction k generalizing ζ with
  | zero => simpa using hk
  | succ k ih =>
    have hη : (ζ ^ p) ^ (p ^ k) = 1 := by rw [← pow_mul, ← pow_succ']; exact hk
    have hη' : modK K (ζ ^ p - 1) ≤ qi hK ^ (M + 1) := modK_pow_sub_one_le hK hq1 hclose p
    have h1 : ζ ^ p = 1 := ih (ζ ^ p) hη hη'
    by_contra hne
    have hy0 : ζ - 1 ≠ 0 := sub_ne_zero.2 hne
    have hp2 : 2 ≤ p := hK.1.two_le
    have hlt : modK K (ζ - 1) ^ (p - 1) < modK K (p : K) := by
      calc modK K (ζ - 1) ^ (p - 1) ≤ (qi hK ^ (M + 1)) ^ (p - 1) :=
            pow_le_pow_left₀ zero_le hclose _
        _ = qi hK ^ ((M + 1) * (p - 1)) := (pow_mul _ _ _).symm
        _ ≤ qi hK ^ M := pow_le_pow_of_le_one zero_le (qi_lt_one hK).le
            ((Nat.le_succ M).trans (Nat.le_mul_of_pos_right _ (by omega)))
        _ < _ := hM
    have := pow_prime_ne_one_of_close hK hy0 (hclose.trans_lt hq1) hlt
    apply this
    rw [add_sub_cancel]
    exact h1

/-- In characteristic $0$ the roots of $1$ of $p$-power order in $K$ form a finite set. -/
theorem finite_pPowRoots [CharZero K] (hK : IsPField K p) :
    {ζ : K | ∃ k, ζ ^ (p ^ k) = 1}.Finite := by
  obtain ⟨N, hN1, hN⟩ := exists_close_N hK
  set S : Set K := {ζ : K | ∃ k, ζ ^ (p ^ k) = 1} with hS
  have hqN : 0 < qi hK ^ N := pow_pos (qi_pos hK) N
  have hSmem : ∀ s ∈ S, modK K s = 1 := by
    rintro s ⟨k, hk⟩
    have : modK K s ^ (p ^ k) = 1 := by rw [← modK_pow, hk, modK_one']
    exact (pow_eq_one_iff_of_nonneg zero_le (pow_pos hp.out.pos k).ne').1 this
  have hsep : ∀ s ∈ S, ∀ s' ∈ S, modK K (s - s') ≤ qi hK ^ N → s = s' := by
    rintro s hs s' hs' h
    obtain ⟨k, hk⟩ := hs
    obtain ⟨k', hk'⟩ := hs'
    have hs'1 := hSmem s' ⟨k', hk'⟩
    have hs'0 : s' ≠ 0 := fun h0 => by rw [h0, modK_zero'] at hs'1; exact zero_ne_one hs'1
    have e1 : s ^ (p ^ (k + k')) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
    have e2 : s' ^ (p ^ (k + k')) = 1 := by rw [add_comm, pow_add, pow_mul, hk', one_pow]
    have hζ : (s / s') ^ (p ^ (k + k')) = 1 := by rw [div_pow, e1, e2, div_one]
    have hmod : modK K (s / s' - 1) ≤ qi hK ^ N := by
      have e : s / s' - 1 = (s - s') * s'⁻¹ := by field_simp
      rw [e, modK_mul, modK_inv hs'0, hs'1, inv_one, mul_one]
      exact h
    exact (div_eq_one_iff_eq hs'0).1 (hN _ ⟨_, hζ⟩ hmod)
  have hcomp : IsCompact (pR hK : Set K) := weil_I_4_thm6_isCompact hK
  let U : K → Set K := fun x => {z | modK K (z - x) < qi hK ^ N}
  have hU : ∀ x ∈ (pR hK : Set K), U x ∈ 𝓝 x := fun x _ =>
    (isOpen_lt (continuous_modK.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds
      (by show modK K (x - x) < _; rw [sub_self, modK_zero']; exact hqN)
  obtain ⟨t, htR, hcover⟩ := hcomp.elim_nhds_subcover U hU
  have hSR : S ⊆ (pR hK : Set K) := fun s hs => mem_pR.2 (hSmem s hs).le
  have hfin : Finite S := by
    have hex : ∀ s : S, ∃ x ∈ t, modK K ((s : K) - x) < qi hK ^ N := fun s => by
      have := hcover (hSR s.2)
      simp only [Set.mem_iUnion] at this
      obtain ⟨x, hx, hxU⟩ := this
      exact ⟨x, hx, hxU⟩
    choose f hft hfU using hex
    refine Finite.of_injective (fun s : S => (⟨f s, hft s⟩ : t)) ?_
    intro s s' h
    have hf : f s = f s' := by simpa using congrArg Subtype.val h
    apply Subtype.ext
    refine hsep _ s.2 _ s'.2 ?_
    have h1 := hfU s
    have h2 := hfU s'
    rw [← hf] at h2
    have e : (s : K) - s' = ((s : K) - f s) - ((s' : K) - f s) := by ring
    rw [e]
    exact (modK_sub_le_max hK _ _).trans (max_le h1.le h2.le)
  exact Set.toFinite S

/-- **Weil, II.§3, Prop. 9 (last assertion)**, characteristic $0$: the roots of $1$ in $1+P$ form a finite cyclic group
of order $p^m$, and $m$ is the largest integer such that $K$ contains a primitive $p^m$-th root of $1$. -/
@[kb "weil1973bnt" "Ch. II, §3, Prop. 9 (the roots of unity in 1 + P: cyclic of order p^m, m maximal)"]
theorem weil_II_3_prop9_torsion_finite [CharZero K] (hK : IsPField K p) :
    ∃ m : ℕ, IsCyclic (CommGroup.torsion (onePlusPUnits hK)) ∧
      Nat.card (CommGroup.torsion (onePlusPUnits hK)) = p ^ m ∧
      IsGreatest {k : ℕ | ∃ ζ : K, IsPrimitiveRoot ζ (p ^ k)} m := by
  set G := onePlusPUnits hK
  set T : Subgroup G := CommGroup.torsion G with hT
  have hmem : ∀ u : G, u ∈ T ↔ ∃ k, u ^ (p ^ k) = 1 := fun u => by
    rw [hT, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact (weil_II_3_prop9_torsion hK u).2
  let f : T →* K := (Units.coeHom K).comp (G.subtype.comp T.subtype)
  have hfinj : Function.Injective f :=
    Units.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  have hroot : ∀ t : T, ∃ k, t ^ (p ^ k) = 1 := fun t => by
    obtain ⟨k, hk⟩ := (hmem t).1 t.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hfin : Finite T := by
    have := (finite_pPowRoots hK).to_subtype
    refine Finite.of_injective (fun t : T => (⟨f t, ?_⟩ : {ζ : K | ∃ k, ζ ^ (p ^ k) = 1})) ?_
    · obtain ⟨k, hk⟩ := hroot t
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    · intro t t' h
      exact hfinj (by simpa using congrArg Subtype.val h)
  have hcyc : IsCyclic T := isCyclic_of_injective_ringHom f hfinj
  have hpg : IsPGroup p T := hroot
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hpg
  refine ⟨m, hcyc, hm, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := T)
    refine ⟨f g, ?_⟩
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_injective f hfinj g, hg, hm]
  · rintro k ⟨ζ, hζ⟩
    have hz1 : ζ ^ (p ^ k) = 1 := hζ.pow_eq_one
    have hlt := modK_sub_one_lt_of_pow_prime hK hz1
    have hζ0 : ζ ≠ 0 := by
      intro h0
      rw [h0, zero_sub, modK_neg, modK_one'] at hlt
      exact lt_irrefl _ hlt
    let w : G := ⟨Units.mk0 ζ hζ0, hlt⟩
    have hwT : w ∈ T := (hmem w).2 ⟨k, Subtype.ext (Units.ext (by simpa [w] using hz1))⟩
    let w' : T := ⟨w, hwT⟩
    have hfw : f w' = ζ := rfl
    have h1 : orderOf w' = p ^ k := by
      rw [← orderOf_injective f hfinj w', hfw]
      exact hζ.eq_orderOf.symm
    have h2 : orderOf w' ∣ Nat.card T := orderOf_dvd_natCard w'
    rw [h1, hm] at h2
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h2

/-- **Weil, II.§3, Prop. 10 (no torsion)**, characteristic $p$: the only root of $1$ in $1+P$ is $1$, so the
$\mathbb Z_p$-module $1+P$ is torsion-free. -/
@[kb "weil1973bnt" "Ch. II, §3, Prop. 10 (in characteristic p, the Z_p-module 1 + P is torsion-free)"]
theorem weil_II_3_prop10_torsionFree [CharP K p] (hK : IsPField K p) (u : onePlusPUnits hK) {n : ℕ}
    (hn : 0 < n) (hu : u ^ n = 1) : u = 1 := by
  obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
  have h1 : u ^ (p ^ e) = 1 :=
    eq_one_of_pow_coprime hK (u ^ (p ^ e)) ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn').symm
      (by rw [← pow_mul]; exact hu)
  have h1' : ((u : Kˣ) : K) ^ (p ^ e) = 1 := by
    have := congrArg (fun w : onePlusPUnits hK => ((w : Kˣ) : K)) h1
    simpa using this
  have h2 : (((u : Kˣ) : K) - 1) ^ (p ^ e) = 0 := by
    rw [sub_pow_char_pow, one_pow, h1', sub_self]
  exact onePlusPUnits_ext (by
    have := (pow_eq_zero_iff (pow_pos hp.out.pos e).ne').1 h2
    simpa [sub_eq_zero] using this)

end NumberFieldKB.WeilBNT.FieldModule
