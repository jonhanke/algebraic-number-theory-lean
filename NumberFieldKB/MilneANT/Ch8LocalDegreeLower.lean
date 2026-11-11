import NumberFieldKB.MilneANT.Ch8Prop810
import NumberFieldKB.MilneANT.Ch7OstrowskiFinite
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Milne, *Algebraic Number Theory*, Remark 8.3: the inequality $e f \le [L_w : K_v]$

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`, pp. 136-138.

**Statement** (`ramificationIdx_mul_inertiaDeg_le_finrank`). Let $L/K$ be an extension of number fields, $\mathfrak P$
a prime of $L$ over a prime $\mathfrak p$ of $K$, and $w$ an extension of the $\mathfrak p$-adic absolute value to $L$
equivalent to the $\mathfrak P$-adic one. Then $e(\mathfrak P/\mathfrak p)\, f(\mathfrak P/\mathfrak p) \le
[L_w : K_{\mathfrak p}]$.

**Proof outline** (Serre's argument; Milne's local degree formula). Let $\omega_1, \dots, \omega_f \in \mathcal O_L$
lift a basis of $\mathcal O_L/\mathfrak P$ over $\mathcal O_K/\mathfrak p$ and $\pi$ a uniformizer at $\mathfrak P$.
Show the $e f$ elements $\pi^i \omega_j$ ($i < e$) satisfy $\delta \max_{ij}\lVert c_{ij}\rVert \le
\lVert \sum c_{ij}\pi^i\omega_j\rVert$ for $c_{ij}\in K_{\mathfrak p}$; this makes them linearly independent over
$K_{\mathfrak p}$, so $e f \le [L_w:K_{\mathfrak p}]$.

1. `stepA_ge`, `stepA` (residue lemma): for $d_j \in K$ not all zero, $w(\sum d_j\omega_j) = \max_j \lVert d_j\rVert$.
   After scaling the maximum to $1$ and clearing denominators by an element of $\mathcal O_K \setminus \mathfrak p$,
   a sum of absolute value $<1$ would lie in $\mathfrak P$, contradicting independence of the residues.
2. `distinct` (value group): $w(\pi)^i\lVert x\rVert \ne w(\pi)^{i'}\lVert x'\rVert$ for $i \ne i'$ in $[0, e)$, by
   comparing $\mathfrak P$-adic valuations ($\mathrm{ord}_{\mathfrak P}\, x = e \cdot \mathrm{ord}_{\mathfrak p}\, x$ on $K$).
3. `le_sum_of_distinct` (ultrametric inequality with distinct values) and `lower_bound_K` combine 1 and 2:
   the lower bound holds for coefficients in $K$.
4. `completion_lower`: the lower bound extends to coefficients in $K_{\mathfrak p}$ by density of $K$
   (the set where it holds is closed), hence the $K_\mathfrak p$-linear map $(c_{ij}) \mapsto \sum c_{ij}\pi^i\omega_j$
   is injective and $e f \le \dim_{K_\mathfrak p} L_w$.

The comparison of $w$ with the $\mathfrak P$-adic valuation uses only `AbsoluteValue.IsEquiv` (`w_le_iff`).
-/

open NumberField IsDedekindDomain

namespace NumberFieldKB.MilneANT
namespace LocalDegree

section NT
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (𝔭 : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L))
  {w : AbsoluteValue L ℝ} (hw : w.IsEquiv (FinitePlace.mk P).1)

include hw in
theorem w_le_iff (x y : L) : w x ≤ w y ↔ P.valuation L x ≤ P.valuation L y := by
  rw [hw x y]
  show ‖FinitePlace.embedding P x‖ ≤ ‖FinitePlace.embedding P y‖ ↔ _
  rw [FinitePlace.norm_embedding', FinitePlace.norm_embedding', NNReal.coe_le_coe]
  exact (WithZeroMulInt.toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal P)).le_iff_le

include hw in
theorem w_eq_iff (x y : L) : w x = w y ↔ P.valuation L x = P.valuation L y := by
  rw [le_antisymm_iff, le_antisymm_iff, w_le_iff P hw, w_le_iff P hw]

include hw in
theorem w_integral_le_one (a : 𝓞 L) : w (a : L) ≤ 1 := by
  have := (w_le_iff P hw (a : L) 1).2 (by simpa using HeightOneSpectrum.valuation_le_one P a)
  simpa using this

include hw in
theorem w_lt_one_iff (a : 𝓞 L) : w (a : L) < 1 ↔ a ∈ P.asIdeal := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), ← not_le, ← not_le]
  have := w_le_iff P hw 1 (a : L)
  simp only [map_one] at this
  exact not_congr this

include hw in
theorem w_add_le (x y : L) : w (x + y) ≤ max (w x) (w y) := by
  rcases le_total (w x) (w y) with h | h
  · rw [max_eq_right h]
    have := (w_le_iff P hw _ _).1 h
    exact (w_le_iff P hw _ _).2 (le_trans (Valuation.map_add _ _ _) (max_le this le_rfl))
  · rw [max_eq_left h]
    have := (w_le_iff P hw _ _).1 h
    exact (w_le_iff P hw _ _).2 (le_trans (Valuation.map_add _ _ _) (max_le le_rfl this))

theorem v_notMem (s : 𝓞 K) :
    (FinitePlace.mk 𝔭).1 (s : K) = 1 ↔ s ∉ 𝔭.asIdeal := by
  have h1 := w_lt_one_iff 𝔭 (w := (FinitePlace.mk 𝔭).1) AbsoluteValue.IsEquiv.rfl s
  have h2 := w_integral_le_one 𝔭 (w := (FinitePlace.mk 𝔭).1) AbsoluteValue.IsEquiv.rfl s
  rw [← h1]
  exact ⟨fun h => by rw [h]; exact lt_irrefl _, fun h => le_antisymm h2 (not_lt.1 h)⟩

end NT

section Comb

variable {L : Type} [Field L] (w : AbsoluteValue L ℝ) (hna : ∀ x y, w (x + y) ≤ max (w x) (w y))

include hna in
theorem sum_lt_of_forall_lt {α : Type*} [DecidableEq α] (s : Finset α) (t : α → L) {M : ℝ} (hM : 0 < M)
    (h : ∀ b ∈ s, w (t b) < M) : w (∑ b ∈ s, t b) < M := by
  induction s using Finset.induction_on with
  | empty => simpa using hM
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (hna _ _) (max_lt (h a (Finset.mem_insert_self _ _))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb)))

include hna in
theorem sum_le_of_forall_le {α : Type*} [DecidableEq α] (s : Finset α) (t : α → L) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ b ∈ s, w (t b) ≤ M) : w (∑ b ∈ s, t b) ≤ M := by
  induction s using Finset.induction_on with
  | empty => simpa using hM
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (hna _ _) (max_le (h a (Finset.mem_insert_self _ _))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb)))

include hna in
theorem le_sum_of_distinct {α : Type*} [DecidableEq α] (s : Finset α) (t : α → L)
    (hd : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → t a ≠ 0 → t b ≠ 0 → w (t a) ≠ w (t b)) :
    ∀ a ∈ s, w (t a) ≤ w (∑ b ∈ s, t b) := by
  intro a ha
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s (fun b => w (t b)) ⟨a, ha⟩
  refine (hmax a ha).trans ?_
  by_cases h0 : t m = 0
  · rw [h0, map_zero]; exact w.nonneg _
  have hpos : 0 < w (t m) := w.pos h0
  have hR : w (∑ b ∈ s.erase m, t b) < w (t m) := by
    refine sum_lt_of_forall_lt w hna _ t hpos fun b hb => ?_
    have hbs := Finset.mem_of_mem_erase hb
    have hbm := Finset.ne_of_mem_erase hb
    rcases eq_or_ne (t b) 0 with h | h
    · rw [h, map_zero]; exact hpos
    · exact lt_of_le_of_ne (hmax b hbs) (hd b hbs m hm hbm h h0)
  by_contra hcon
  rw [not_le] at hcon
  have hsum : t m = (∑ b ∈ s, t b) + -(∑ b ∈ s.erase m, t b) := by
    rw [← Finset.add_sum_erase s t hm]; ring
  have := hna (∑ b ∈ s, t b) (-(∑ b ∈ s.erase m, t b))
  rw [map_neg_eq_map, ← hsum] at this
  exact absurd (lt_of_le_of_lt this (max_lt hcon hR)) (lt_irrefl _)

end Comb

section StepA

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (𝔭 : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L)) [P.asIdeal.LiesOver 𝔭.asIdeal]
  {w : AbsoluteValue L ℝ} (hw : w.IsEquiv (FinitePlace.mk P).1)
  (hwv : ∀ x : K, w (algebraMap K L x) = (FinitePlace.mk 𝔭).1 x)

include hw hwv in
theorem stepA_ge {ι : Type} [Fintype ι] (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ 𝔭.asIdeal) (fun j => Ideal.Quotient.mk P.asIdeal (ω j)))
    (c : ι → K) (j0 : ι) (hc0 : c j0 = 1) (hc : ∀ j, (FinitePlace.mk 𝔭).1 (c j) ≤ 1) :
    1 ≤ w (∑ j, algebraMap K L (c j) * (ω j : L)) := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hex : ∀ j, ∃ (n : 𝓞 K) (d : 𝔭.asIdeal.primeCompl),
      c j * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K n := fun j => by
    apply HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
    have := (w_le_iff 𝔭 (w := (FinitePlace.mk 𝔭).1) AbsoluteValue.IsEquiv.rfl (c j) 1).1
      (by simpa using hc j)
    simpa using this
  choose n d hnd using hex
  set s : 𝓞 K := ∏ j, (d j : 𝓞 K) with hs
  have hs_mem : s ∉ 𝔭.asIdeal := by
    have : s ∈ 𝔭.asIdeal.primeCompl := Submonoid.prod_mem _ (fun j _ => (d j).2)
    exact this
  let b : ι → 𝓞 K := fun j => n j * ∏ k ∈ Finset.univ.erase j, (d k : 𝓞 K)
  have hb : ∀ j, algebraMap (𝓞 K) K (b j) = algebraMap (𝓞 K) K s * c j := fun j => by
    simp only [b, hs, map_mul, map_prod]
    rw [← hnd j, ← Finset.mul_prod_erase Finset.univ (fun k => algebraMap (𝓞 K) K (d k))
      (Finset.mem_univ j)]
    ring
  let A : 𝓞 L := ∑ j, algebraMap (𝓞 K) (𝓞 L) (b j) * ω j
  have hA : (A : L) = algebraMap K L (algebraMap (𝓞 K) K s) * ∑ j, algebraMap K L (c j) * (ω j : L) := by
    simp only [A, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    calc _ = algebraMap K L (algebraMap (𝓞 K) K (b j)) * (ω j : L) := rfl
      _ = _ := by rw [hb j, map_mul]; ring
  have hAw : w (A : L) < 1 := by
    rw [hA, map_mul, hwv]
    have : (FinitePlace.mk 𝔭).1 (algebraMap (𝓞 K) K s) = 1 := (v_notMem 𝔭 s).2 hs_mem
    rw [this, one_mul]
    exact hlt
  have hAP : A ∈ P.asIdeal := (w_lt_one_iff P hw A).1 hAw
  have hzero : ∑ j, (Ideal.Quotient.mk 𝔭.asIdeal (b j)) • Ideal.Quotient.mk P.asIdeal (ω j) = 0 := by
    have : Ideal.Quotient.mk P.asIdeal A = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hAP
    rw [← this]
    simp only [A, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul]
    rfl
  have := Fintype.linearIndependent_iff.1 hω (fun j => Ideal.Quotient.mk 𝔭.asIdeal (b j)) hzero j0
  have hmem : b j0 ∈ 𝔭.asIdeal := Ideal.Quotient.eq_zero_iff_mem.1 this
  have hbs : b j0 = s := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [hb, hc0, mul_one]
  exact hs_mem (hbs ▸ hmem)

include hw hwv in
theorem stepA {ι : Type} [Fintype ι] (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ 𝔭.asIdeal) (fun j => Ideal.Quotient.mk P.asIdeal (ω j)))
    (d : ι → K) (hd : d ≠ 0) :
    ∃ j0, d j0 ≠ 0 ∧ w (∑ j, algebraMap K L (d j) * (ω j : L)) = (FinitePlace.mk 𝔭).1 (d j0) ∧
      ∀ j, (FinitePlace.mk 𝔭).1 (d j) ≤ (FinitePlace.mk 𝔭).1 (d j0) := by
  classical
  obtain ⟨j1, hj1⟩ := Function.ne_iff.1 hd
  obtain ⟨j0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => (FinitePlace.mk 𝔭).1 (d j))
    ⟨j1, Finset.mem_univ _⟩
  have hmax' : ∀ j, (FinitePlace.mk 𝔭).1 (d j) ≤ (FinitePlace.mk 𝔭).1 (d j0) :=
    fun j => hmax j (Finset.mem_univ _)
  have hd0 : d j0 ≠ 0 := by
    intro h0
    have := hmax' j1
    rw [h0, map_zero] at this
    exact hj1 ((AbsoluteValue.eq_zero _).1 (le_antisymm this ((FinitePlace.mk 𝔭).1.nonneg _)))
  have hv0 : 0 < (FinitePlace.mk 𝔭).1 (d j0) := (FinitePlace.mk 𝔭).1.pos hd0
  have hna := w_add_le P hw
  set c : ι → K := fun j => d j / d j0 with hc
  have hdc : ∀ j, algebraMap K L (d j) = algebraMap K L (d j0) * algebraMap K L (c j) := fun j => by
    simp only [hc]
    rw [← map_mul]; congr 1; field_simp
  have hS : ∑ j, algebraMap K L (d j) * (ω j : L) =
      algebraMap K L (d j0) * ∑ j, algebraMap K L (c j) * (ω j : L) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdc j]; ring
  have hcv : ∀ j, (FinitePlace.mk 𝔭).1 (c j) ≤ 1 := fun j => by
    simp only [hc, map_div₀]
    exact (div_le_one hv0).2 (hmax' j)
  have hc0 : c j0 = 1 := by simp [hc, hd0]
  have h1 := stepA_ge 𝔭 P hw hwv ω hω c j0 hc0 hcv
  have h2 : w (∑ j, algebraMap K L (c j) * (ω j : L)) ≤ 1 := by
    refine sum_le_of_forall_le w hna _ _ zero_le_one fun j _ => ?_
    rw [map_mul, hwv]
    calc _ ≤ 1 * 1 := mul_le_mul (hcv j) (w_integral_le_one P hw (ω j)) (w.nonneg _) zero_le_one
      _ = 1 := one_mul 1
  refine ⟨j0, hd0, ?_, hmax'⟩
  rw [hS, map_mul, hwv, le_antisymm h2 h1, mul_one]

include hw hwv in
theorem distinct (π : 𝓞 L) (hπ : P.valuation L (π : L) = WithZero.exp (-1)) (i i' : ℕ)
    (hi : i < P.asIdeal.ramificationIdx (𝓞 K)) (hi' : i' < P.asIdeal.ramificationIdx (𝓞 K))
    (hne : i ≠ i') (x x' : K) (hx : x ≠ 0) (hx' : x' ≠ 0) :
    w (π : L) ^ i * (FinitePlace.mk 𝔭).1 x ≠ w (π : L) ^ i' * (FinitePlace.mk 𝔭).1 x' := by
  intro heq
  have e1 : w ((π : L) ^ i * algebraMap K L x) = w (π : L) ^ i * (FinitePlace.mk 𝔭).1 x := by
    rw [map_mul, map_pow, hwv]
  have e2 : w ((π : L) ^ i' * algebraMap K L x') = w (π : L) ^ i' * (FinitePlace.mk 𝔭).1 x' := by
    rw [map_mul, map_pow, hwv]
  have h := (w_eq_iff P hw _ _).1 (e1.trans (heq.trans e2.symm))
  simp only [map_mul, map_pow, hπ, ← HeightOneSpectrum.valuation_liesOver L 𝔭 P] at h
  have hx0 : 𝔭.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hx0' : 𝔭.valuation K x' ≠ 0 := (Valuation.ne_zero_iff _).2 hx'
  have hl := congrArg WithZero.log h
  rw [WithZero.log_mul (pow_ne_zero _ (WithZero.exp_ne_zero)) (pow_ne_zero _ hx0),
    WithZero.log_mul (pow_ne_zero _ (WithZero.exp_ne_zero)) (pow_ne_zero _ hx0'),
    WithZero.log_pow, WithZero.log_pow, WithZero.log_pow, WithZero.log_pow, WithZero.log_exp] at hl
  simp only [nsmul_eq_mul] at hl
  set a := (𝔭.valuation K x).log
  set a' := (𝔭.valuation K x').log
  have hE : (0 : ℤ) < P.asIdeal.ramificationIdx (𝓞 K) := by omega
  have hk : (P.asIdeal.ramificationIdx (𝓞 K) : ℤ) * (a - a') = (i : ℤ) - i' := by linarith
  have hi2 : (i : ℤ) < P.asIdeal.ramificationIdx (𝓞 K) := by exact_mod_cast hi
  have hi2' : (i' : ℤ) < P.asIdeal.ramificationIdx (𝓞 K) := by exact_mod_cast hi'
  rcases lt_trichotomy (a - a') 0 with h0 | h0 | h0
  · nlinarith
  · rw [h0] at hk
    omega
  · nlinarith

include hw hwv in
theorem lower_bound_K (π : 𝓞 L) (hπ : P.valuation L (π : L) = WithZero.exp (-1))
    {ι : Type} [Fintype ι] (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ 𝔭.asIdeal) (fun j => Ideal.Quotient.mk P.asIdeal (ω j)))
    (c : Fin (P.asIdeal.ramificationIdx (𝓞 K)) → ι → K)
    (i : Fin (P.asIdeal.ramificationIdx (𝓞 K))) (j : ι) :
    w (π : L) ^ (i : ℕ) * (FinitePlace.mk 𝔭).1 (c i j) ≤
      w (∑ a, ∑ b, algebraMap K L (c a b) * ((π : L) ^ (a : ℕ) * (ω b : L))) := by
  classical
  have hna := w_add_le P hw
  set S : Fin (P.asIdeal.ramificationIdx (𝓞 K)) → L :=
    fun a => ∑ b, algebraMap K L (c a b) * (ω b : L) with hSdef
  have hsum : ∑ a, ∑ b, algebraMap K L (c a b) * ((π : L) ^ (a : ℕ) * (ω b : L)) =
      ∑ a : Fin (P.asIdeal.ramificationIdx (𝓞 K)), (π : L) ^ (a : ℕ) * S a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hSdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  -- the value of S a
  have hS : ∀ a, S a ≠ 0 → ∃ b, c a b ≠ 0 ∧ w (S a) = (FinitePlace.mk 𝔭).1 (c a b) := by
    intro a ha
    have hne : c a ≠ 0 := by
      intro h0
      apply ha
      simp [hSdef, h0]
    obtain ⟨b, hb0, hb1, -⟩ := stepA 𝔭 P hw hwv ω hω (c a) hne
    exact ⟨b, hb0, hb1⟩
  have hSle : ∀ a b, (FinitePlace.mk 𝔭).1 (c a b) ≤ w (S a) := by
    intro a b
    by_cases hne : c a = 0
    · simp [hne]
    · obtain ⟨b0, -, hb1, hb2⟩ := stepA 𝔭 P hw hwv ω hω (c a) hne
      exact (hb2 b).trans (le_of_eq hb1.symm)
  have key := le_sum_of_distinct w hna (Finset.univ : Finset (Fin (P.asIdeal.ramificationIdx (𝓞 K))))
    (fun a : Fin (P.asIdeal.ramificationIdx (𝓞 K)) => (π : L) ^ (a : ℕ) * S a) ?_ i
    (Finset.mem_univ _)
  · rw [hsum]
    refine le_trans ?_ key
    rw [map_mul, map_pow]
    exact mul_le_mul_of_nonneg_left (hSle i j) (by positivity)
  · intro a _ b _ hab ha hb
    have hSa : S a ≠ 0 := fun h => ha (by simp [h])
    have hSb : S b ≠ 0 := fun h => hb (by simp [h])
    obtain ⟨a', ha0, ha1⟩ := hS a hSa
    obtain ⟨b', hb0, hb1⟩ := hS b hSb
    rw [map_mul, map_mul, map_pow, map_pow, ha1, hb1]
    exact distinct 𝔭 P hw hwv π hπ a b a.2 b.2 (fun h => hab (Fin.ext h)) _ _ ha0 hb0

end StepA

section Analytic

open Prop81

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : AbsoluteValue K ℝ) (W : Extensions L v)

/-- If $\delta \lVert c_k\rVert \le w(\sum c_k y_k)$ for all coefficients in $K$, then the $y_k$ are linearly
independent over $K_v$ in $L_w$ (so there are at most $\dim_{K_v} L_w$ of them). -/
theorem completion_lower {ι : Type} [Fintype ι] (y : ι → L) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ (c : ι → K) (k : ι), δ * v (c k) ≤ W.1 (∑ k, algebraMap K L (c k) * y k)) :
    letI := extAlgebra v W
    Fintype.card ι ≤ Module.finrank v.Completion W.1.Completion := by
  let _ := extAlgebra v W
  have := W.2
  have : FiniteDimensional v.Completion W.1.Completion := Prop810.finiteDimensional v W.1
  let T : (ι → v.Completion) →ₗ[v.Completion] W.1.Completion :=
    Fintype.linearCombination v.Completion (fun k => ((y k : L) : W.1.Completion))
  have hT : Continuous T := by
    show Continuous fun c : ι → v.Completion => T c
    simp only [T, Fintype.linearCombination_apply]
    exact continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const
  have hclosed : IsClosed {c : ι → v.Completion | ∀ k, δ * ‖c k‖ ≤ ‖T c‖} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_le (continuous_const.mul
      (continuous_norm.comp (continuous_apply k))) (continuous_norm.comp hT)
  have hdense : DenseRange (algebraMap K v.Completion) :=
    (UniformSpace.Completion.denseRange_coe (α := WithAbs v)).comp
      (show Function.Surjective (WithAbs.toAbs v) from fun x => ⟨WithAbs.ofAbs x, rfl⟩).denseRange
      (UniformSpace.Completion.continuous_coe _)
  have hdense' : DenseRange (Pi.map fun (_ : ι) => algebraMap K v.Completion) :=
    DenseRange.piMap fun _ => hdense
  have hsub : Set.range (Pi.map fun (_ : ι) => algebraMap K v.Completion) ⊆
      {c : ι → v.Completion | ∀ k, δ * ‖c k‖ ≤ ‖T c‖} := by
    rintro _ ⟨c, rfl⟩ k
    have h1 : T (Pi.map (fun (_ : ι) => algebraMap K v.Completion) c) =
        ((∑ k, algebraMap K L (c k) * y k : L) : W.1.Completion) := by
      simp only [T, Fintype.linearCombination_apply, Pi.map_apply]
      have := map_sum (coeAlgHom (K := K) W.1) (fun k => algebraMap K L (c k) * y k) Finset.univ
      rw [coeAlgHom_apply] at this
      rw [this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, algebraMap_ext_coe]
      rw [map_mul]
      rfl
    rw [h1, norm_coe_completion]
    simp only [Pi.map_apply]
    rw [norm_algebraMap_completion]
    exact h c k
  have hall : ∀ c : ι → v.Completion, ∀ k, δ * ‖c k‖ ≤ ‖T c‖ := by
    intro c
    have : closure (Set.range (Pi.map fun (_ : ι) => algebraMap K v.Completion)) = Set.univ :=
      hdense'.closure_range
    have hc : c ∈ {c : ι → v.Completion | ∀ k, δ * ‖c k‖ ≤ ‖T c‖} :=
      closure_minimal hsub hclosed (this ▸ Set.mem_univ c)
    exact hc
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    funext k
    have := hall c k
    rw [hc, norm_zero] at this
    have h0 : ‖c k‖ ≤ 0 := by
      by_contra hpos
      rw [not_le] at hpos
      nlinarith
    simpa using h0
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

end Analytic

end LocalDegree

open LocalDegree in
/-- **Remark 8.3 / local degree formula, inequality half** (Milne, pp. 136-138): for a prime $\mathfrak P$ of $L$
over a prime $\mathfrak p$ of $K$ and an extension $w$ of the $\mathfrak p$-adic absolute value to $L$ equivalent to
the $\mathfrak P$-adic one, $e(\mathfrak P/\mathfrak p)\, f(\mathfrak P/\mathfrak p) \le [L_w : K_{\mathfrak p}]$. -/
@[kb "milne2020ant" "v3.08, Rem. 8.3, p. 136"]
theorem ramificationIdx_mul_inertiaDeg_le_finrank (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver 𝔭.asIdeal] (w : Extensions L (FinitePlace.mk 𝔭).1)
    (hw : w.1.IsEquiv (FinitePlace.mk P).1) :
    letI := extAlgebra (FinitePlace.mk 𝔭).1 w
    P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) ≤
      Module.finrank (FinitePlace.mk 𝔭).1.Completion w.1.Completion := by
  classical
  have hf : P.asIdeal.inertiaDeg (𝓞 K) =
      Module.finrank (𝓞 K ⧸ 𝔭.asIdeal) (𝓞 L ⧸ P.asIdeal) :=
    Ideal.inertiaDeg_eq_of_isMaximal 𝔭.asIdeal P.asIdeal
  have hfpos : 0 < Module.finrank (𝓞 K ⧸ 𝔭.asIdeal) (𝓞 L ⧸ P.asIdeal) :=
    hf ▸ Ideal.inertiaDeg_pos _ _
  let _ : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  have : Module.Finite (𝓞 K ⧸ 𝔭.asIdeal) (𝓞 L ⧸ P.asIdeal) := Module.finite_of_finrank_pos hfpos
  let b := Module.finBasis (𝓞 K ⧸ 𝔭.asIdeal) (𝓞 L ⧸ P.asIdeal)
  have hsurj : ∀ j, ∃ x : 𝓞 L, Ideal.Quotient.mk P.asIdeal x = b j := fun j =>
    Ideal.Quotient.mk_surjective (b j)
  choose ω hω using hsurj
  have hli : LinearIndependent (𝓞 K ⧸ 𝔭.asIdeal) (fun j => Ideal.Quotient.mk P.asIdeal (ω j)) := by
    have := b.linearIndependent
    convert this using 1
    funext j
    exact hω j
  obtain ⟨π, hπ0⟩ := P.intValuation_exists_uniformizer
  have hπ : P.valuation L (π : L) = WithZero.exp (-1) := by
    rw [← hπ0]
    exact HeightOneSpectrum.valuation_of_algebraMap (K := L) (v := P) π
  have hπ_ne : (π : L) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hwv : ∀ x : K, w.1 (algebraMap K L x) = (FinitePlace.mk 𝔭).1 x := fun x =>
    DFunLike.congr_fun w.2.under_eq x
  have hπle : w.1 (π : L) ≤ 1 := w_integral_le_one P hw π
  have hπpos : 0 < w.1 (π : L) := w.1.pos hπ_ne
  let y : Fin (P.asIdeal.ramificationIdx (𝓞 K)) × Fin (Module.finrank (𝓞 K ⧸ 𝔭.asIdeal) (𝓞 L ⧸ P.asIdeal)) → L :=
    fun p => (π : L) ^ (p.1 : ℕ) * (ω (p.2) : L)
  have hδ : 0 < w.1 (π : L) ^ P.asIdeal.ramificationIdx (𝓞 K) := pow_pos hπpos _
  have := completion_lower (FinitePlace.mk 𝔭).1 w y hδ (fun c k => by
    have h1 := lower_bound_K 𝔭 P hw hwv π hπ ω hli (fun a b => c (a, b)) k.1 k.2
    have h2 : (∑ k, algebraMap K L (c k) * y k) =
        ∑ a, ∑ b, algebraMap K L (c (a, b)) * ((π : L) ^ (a : ℕ) * (ω b : L)) := by
      rw [Fintype.sum_prod_type]
    rw [h2]
    refine le_trans ?_ h1
    refine mul_le_mul_of_nonneg_right ?_ (AbsoluteValue.nonneg _ _)
    exact pow_le_pow_of_le_one hπpos.le hπle k.1.2.le)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← hf] at this
  exact this

end NumberFieldKB.MilneANT
