import NumberFieldKB.MilneANT.Ch7Basic
import Mathlib.Computability.Reduce
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.RingTheory.Norm.Basic

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: absolute values

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Milne's absolute values are real valued: they are Mathlib's `AbsoluteValue K ℝ` on a field `K`. "Nonarchimedean"
is Mathlib's `IsNonarchimedean v` ($|x+y| \le \max(|x|,|y|)$), "nontrivial" is `AbsoluteValue.IsNontrivial`, and
"equivalent" is `AbsoluteValue.IsEquiv` (equivalent to Milne's three conditions by Proposition 7.8, see
`Ch7Cite.lean`).

* **Corollary 7.3** (`cor_7_3`): in characteristic $\ne 0$ every absolute value is nonarchimedean.
* **Proposition 7.5** (`prop_7_5`): $v = -\log_e|\cdot|$ is an additive valuation, and a multiple of a discrete
  valuation when $v(K^\times)$ is discrete.
* **Discrete absolute value** (prose definition, p. 107; `IsDiscreteAbv`).
* **Proposition 7.6** (`absValuationSubring`, `prop_7_6`): the ring $A = \{|a| \le 1\}$, its units and maximal ideal;
  $|\cdot|$ is discrete iff the maximal ideal is principal, and then $A$ is a discrete valuation ring.
* **Remark 7.7** (`remark_7_7`, `remark_7_7_algebraicClosure`): nondiscrete nonarchimedean absolute values exist.
* **Paragraphs 7.9–7.11** (`para_7_9`, `para_7_10`, `para_7_11`): the strict triangle (isosceles) properties.
* **Lemma 7.19** (`lemma_7_19`) and **Corollary 7.21** (`cor_7_21`): the steps around the weak approximation theorem.
-/

open Real Filter Topology

namespace NumberFieldKB.MilneANT

variable {K : Type*} [Field K]

/-! ## Nonarchimedean absolute values -/

/-- **Corollary 7.3.** If $\operatorname{char} K \ne 0$, then every absolute value on $K$ is nonarchimedean.
(Milne's proof: the set $\{m \cdot 1 : m \in \mathbb Z\}$ is finite, so Proposition 7.2 applies.) -/
@[kb "milne2020ant" "v3.08, Cor. 7.3, p. 106"]
theorem cor_7_3 (h : ringChar K ≠ 0) (v : AbsoluteValue K ℝ) : IsNonarchimedean v := by
  apply isNonarchimedean_of_natCast_le_one
  have : NeZero (ringChar K) := ⟨h⟩
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨C, hC⟩ := (Set.finite_range (fun k : Fin (ringChar K) => v ((k.val : ℕ) : K))).bddAbove
  intro m
  by_contra hm
  replace hm := not_le.mp hm
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hm
  have e : v (((m ^ k : ℕ)) : K) = v (m : K) ^ k := by simp
  have hle : v (((m ^ k : ℕ)) : K) ≤ C := by
    rw [CharP.natCast_eq_natCast_mod K (ringChar K) (m ^ k)]
    exact hC ⟨⟨(m ^ k) % ringChar K, Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩, rfl⟩
  linarith

/-- **Proposition 7.5.** Let $|\cdot|$ be a nontrivial nonarchimedean absolute value on $K$, let $e > 1$ and put
$v(x) = -\log_e |x|$ for $x \ne 0$. Then (a) $v(xy) = v(x) + v(y)$ and (b) $v(x+y) \ge \min(v(x), v(y))$ (for
$x + y \ne 0$). If $v(K^\times)$ is discrete in $\mathbb R$, then $v = c \cdot \operatorname{ord}$ for a real $c > 0$ and
a discrete valuation $\operatorname{ord} : K^\times \twoheadrightarrow \mathbb Z$ (a surjective homomorphism with
$\operatorname{ord}(x + y) \ge \min(\operatorname{ord} x, \operatorname{ord} y)$).

The book's text reads "$v(x) = \log|x|$" in the extracted copy; the minus sign is forced by (b) and by the preceding
sentence $\operatorname{ord}(x) = -\log_e|x|$. -/
@[kb "milne2020ant" "v3.08, Prop. 7.5, p. 107"]
theorem prop_7_5 (v : AbsoluteValue K ℝ) (hna : IsNonarchimedean v) (hnt : v.IsNontrivial) {e : ℝ} (he : 1 < e) :
    (∀ x y : K, x ≠ 0 → y ≠ 0 → -logb e (v (x * y)) = -logb e (v x) + -logb e (v y)) ∧
    (∀ x y : K, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (-logb e (v x)) (-logb e (v y)) ≤ -logb e (v (x + y))) ∧
    (DiscreteTopology (Set.range fun x : Kˣ => -logb e (v (x : K))) →
      ∃ (c : ℝ) (ord : K → ℤ), 0 < c ∧
        Function.Surjective (fun x : Kˣ => ord x) ∧
        (∀ x y : K, x ≠ 0 → y ≠ 0 → ord (x * y) = ord x + ord y) ∧
        (∀ x y : K, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → min (ord x) (ord y) ≤ ord (x + y)) ∧
        ∀ x : K, x ≠ 0 → -logb e (v x) = c * ord x) := by
  have p1 : ∀ x y : K, x ≠ 0 → y ≠ 0 → -logb e (v (x * y)) = -logb e (v x) + -logb e (v y) := by
    intro x y hx hy
    rw [map_mul, Real.logb_mul (v.ne_zero hx) (v.ne_zero hy)]
    ring
  have p2 : ∀ x y : K, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (-logb e (v x)) (-logb e (v y)) ≤ -logb e (v (x + y)) := by
    intro x y hx hy hxy
    have h1 : logb e (v (x + y)) ≤ logb e (max (v x) (v y)) :=
      Real.logb_le_logb_of_le he (v.pos hxy) (hna x y)
    rcases le_total (v x) (v y) with h | h
    · rw [max_eq_right h] at h1
      have := Real.logb_le_logb_of_le he (v.pos hx) h
      rw [min_eq_right (by linarith)]
      linarith
    · rw [max_eq_left h] at h1
      have := Real.logb_le_logb_of_le he (v.pos hy) h
      rw [min_eq_left (by linarith)]
      linarith
  refine ⟨p1, p2, ?_⟩
  · intro hdisc
    classical
    let f : Kˣ → ℝ := fun x => -logb e (v (x : K))
    let S : AddSubgroup ℝ :=
      { carrier := Set.range f
        add_mem' := by
          rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
          exact ⟨a * b, by simp only [f, Units.val_mul]; exact p1 _ _ a.ne_zero b.ne_zero⟩
        zero_mem' := ⟨1, by simp [f]⟩
        neg_mem' := by
          rintro _ ⟨a, rfl⟩
          exact ⟨a⁻¹, by simp [f, Real.logb_inv]⟩ }
    have hS : DiscreteTopology S := hdisc
    have hcyc : IsAddCyclic S := AddSubgroup.isAddCyclic_iff_discreteTopology.2 hS
    obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top S).1 hcyc
    obtain ⟨x₀, hx₀, hx₀1⟩ := hnt
    have hf0 : f (Units.mk0 x₀ hx₀) ≠ 0 := by
      simp only [f, Units.val_mk0, neg_ne_zero]
      intro h0
      rcases Real.logb_eq_zero.1 h0 with h | h | h | h | h | h
      · linarith
      · linarith
      · linarith
      · exact (v.pos hx₀).ne' h
      · exact hx₀1 h
      · linarith [v.pos hx₀]
    have hc : ∃ c : ℝ, 0 < c ∧ AddSubgroup.zmultiples c = S := by
      have hg0 : g ≠ 0 := by
        rintro rfl
        have : f (Units.mk0 x₀ hx₀) ∈ S := ⟨_, rfl⟩
        rw [← hg, AddSubgroup.mem_zmultiples_iff] at this
        obtain ⟨n, hn⟩ := this
        simp at hn
        exact hf0 hn.symm
      rcases lt_or_gt_of_ne hg0 with h | h
      · exact ⟨-g, by linarith, by rw [AddSubgroup.zmultiples_neg]; exact hg⟩
      · exact ⟨g, h, hg⟩
    obtain ⟨c, hc0, hcS⟩ := hc
    have hmem : ∀ x : K, x ≠ 0 → ∃ n : ℤ, (n : ℝ) * c = -logb e (v x) := by
      intro x hx
      have : -logb e (v x) ∈ S := ⟨Units.mk0 x hx, rfl⟩
      rw [← hcS, AddSubgroup.mem_zmultiples_iff] at this
      obtain ⟨n, hn⟩ := this
      exact ⟨n, by rw [← hn, zsmul_eq_mul]⟩
    let ord : K → ℤ := fun x => if hx : x ≠ 0 then Classical.choose (hmem x hx) else 0
    have hord : ∀ x : K, x ≠ 0 → (ord x : ℝ) * c = -logb e (v x) := by
      intro x hx
      simp only [ord, hx, ne_eq, not_false_eq_true, dite_true]
      exact Classical.choose_spec (hmem x hx)
    have hcancel : ∀ n m : ℤ, (n : ℝ) * c = m * c → n = m := by
      intro n m h
      exact_mod_cast mul_right_cancel₀ hc0.ne' h
    refine ⟨c, ord, hc0, ?_, ?_, ?_, ?_⟩
    · intro n
      have : (n : ℝ) * c ∈ S := by
        rw [← hcS, AddSubgroup.mem_zmultiples_iff]
        exact ⟨n, by rw [zsmul_eq_mul]⟩
      obtain ⟨u, hu⟩ := this
      refine ⟨u, hcancel _ _ ?_⟩
      rw [hord _ u.ne_zero]
      exact hu
    · intro x y hx hy
      apply hcancel
      rw [hord _ (mul_ne_zero hx hy), p1 x y hx hy, ← hord x hx, ← hord y hy]
      push_cast; ring
    · intro x y hx hy hxy
      have h2 := p2 x y hx hy hxy
      rw [← hord x hx, ← hord y hy, ← hord _ hxy] at h2
      have : ((min (ord x) (ord y) : ℤ) : ℝ) * c ≤ (ord (x + y) : ℝ) * c := by
        rcases le_total (ord x) (ord y) with h | h
        · have h' : (ord x : ℝ) ≤ ord y := by exact_mod_cast h
          have hle : (ord x : ℝ) * c ≤ ord y * c := by nlinarith
          rw [min_eq_left hle] at h2
          rw [min_eq_left h]
          exact h2
        · have h' : (ord y : ℝ) ≤ ord x := by exact_mod_cast h
          have hle : (ord y : ℝ) * c ≤ ord x * c := by nlinarith
          rw [min_eq_right hle] at h2
          rw [min_eq_right h]
          exact h2
      have := le_of_mul_le_mul_right this hc0
      exact_mod_cast this
    · intro x hx
      rw [← hord x hx]; ring

/-- A gap just below `1` in the value set forces discreteness. -/
private lemma isDiscreteAbv_of_gap (v : AbsoluteValue K ℝ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hgap : ∀ x : K, x ≠ 0 → ¬ (ρ < v x ∧ v x < 1)) : IsDiscreteAbv v := by
  unfold IsDiscreteAbv
  rw [discreteTopology_iff_isOpen_singleton]
  rintro ⟨_, ⟨u, rfl⟩⟩
  rw [isOpen_induced_iff]
  have hu : 0 < v (u : K) := v.pos u.ne_zero
  refine ⟨Set.Ioo (v u * ρ) (v u / ρ), isOpen_Ioo, ?_⟩
  ext ⟨_, ⟨w, rfl⟩⟩
  simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hw : 0 < v (w : K) := v.pos w.ne_zero
    have hx : v ((w : K) / u) = v w / v u := by rw [map_div₀]
    have hx' : v ((u : K) / w) = v u / v w := by rw [map_div₀]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply hgap ((w : K) / u) (div_ne_zero w.ne_zero u.ne_zero)
      rw [hx]
      refine ⟨?_, (div_lt_one hu).2 hlt⟩
      rw [lt_div_iff₀ hu]; linarith
    · apply hgap ((u : K) / w) (div_ne_zero u.ne_zero w.ne_zero)
      rw [hx']
      refine ⟨?_, (div_lt_one hw).2 hgt⟩
      rw [lt_div_iff₀ hw]
      rw [lt_div_iff₀ hρ0] at h2
      linarith
  · intro h
    have h' : v (w : K) = v (u : K) := congrArg Subtype.val h
    rw [h']
    exact ⟨by nlinarith, by rw [lt_div_iff₀ hρ0]; nlinarith⟩

/-- Data of a discrete valuation attached to a nontrivial discrete nonarchimedean absolute value
(from Proposition 7.5). -/
private lemma exists_ord_of_discrete (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hnt : v.IsNontrivial) (hd : IsDiscreteAbv v) :
    ∃ ord : K → ℤ, (∃ p₀ : K, p₀ ≠ 0 ∧ ord p₀ = 1) ∧
      (∀ x y : K, x ≠ 0 → y ≠ 0 → ord (x * y) = ord x + ord y) ∧
      (∀ x : K, x ≠ 0 → (v x ≤ 1 ↔ 0 ≤ ord x)) ∧ (∀ x : K, x ≠ 0 → (v x < 1 ↔ 0 < ord x)) := by
  have hdisc : DiscreteTopology (Set.range fun x : Kˣ => -logb 2 (v (x : K))) := by
    have : DiscreteTopology (Set.range fun x : Kˣ => v (x : K)) := hd
    refine DiscreteTopology.of_continuous_injective
      (f := fun y : Set.range fun x : Kˣ => -logb 2 (v (x : K)) =>
        (⟨(2 : ℝ) ^ (-(y : ℝ)), ?_⟩ : Set.range fun x : Kˣ => v (x : K))) ?_ ?_
    · obtain ⟨_, ⟨u, rfl⟩⟩ := y
      refine ⟨u, ?_⟩
      simp only [neg_neg]
      exact (Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
        (v.pos u.ne_zero)).symm
    · exact Continuous.subtype_mk (by fun_prop) _
    · intro a b hab
      have := congrArg Subtype.val hab
      simp only at this
      have h2 := (Real.rpow_right_inj (by norm_num) (by norm_num)).1 this
      exact Subtype.ext (neg_inj.1 h2)
  obtain ⟨c, ord, hc, hsurj, hmul, -, hval⟩ := (prop_7_5 v hv hnt (e := 2) one_lt_two).2.2 hdisc
  refine ⟨ord, ?_, hmul, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hsurj 1
    exact ⟨u, u.ne_zero, hu⟩
  · intro x hx
    have h := hval x hx
    rw [← Real.logb_nonpos_iff one_lt_two (v.pos hx),
      show logb 2 (v x) = -(c * ord x) by linarith, neg_nonpos, mul_nonneg_iff_of_pos_left hc]
    norm_cast
  · intro x hx
    have h := hval x hx
    rw [← Real.logb_neg_iff one_lt_two (v.pos hx),
      show logb 2 (v x) = -(c * ord x) by linarith, neg_lt_zero, mul_pos_iff_of_pos_left hc]
    norm_cast

/-- **Proposition 7.6.** Let $|\cdot|$ be a nonarchimedean absolute value on $K$. Then
$A = \{a : |a| \le 1\}$ is a subring of $K$ (`absValuationSubring`, a local ring) whose group of units is
$U = \{a : |a| = 1\}$ and whose unique maximal ideal is $\mathfrak m = \{a : |a| < 1\}$. The absolute value is
discrete iff $\mathfrak m$ is principal, in which case $A$ is a discrete valuation ring.

Deviation: for the last clause we assume $|\cdot|$ nontrivial. For the trivial absolute value $A = K$, $\mathfrak m = 0$
is principal and $|K^\times| = \{1\}$ is discrete, but a field is not a discrete valuation ring; Milne's discrete
valuations are surjective onto $\mathbb Z$, so nontriviality is implicit in the book. -/
@[kb "milne2020ant" "v3.08, Prop. 7.6, p. 107"]
theorem prop_7_6 (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    (∀ a : absValuationSubring v hv, IsUnit a ↔ v a = 1) ∧
    (∀ a : absValuationSubring v hv, a ∈ IsLocalRing.maximalIdeal (absValuationSubring v hv) ↔ v a < 1) ∧
    (IsDiscreteAbv v ↔ (IsLocalRing.maximalIdeal (absValuationSubring v hv)).IsPrincipal) ∧
    (IsDiscreteAbv v → v.IsNontrivial → IsDiscreteValuationRing (absValuationSubring v hv)) := by
  classical
  set A := absValuationSubring v hv with hA
  have hmemA : ∀ a : A, v (a : K) ≤ 1 := fun a => a.2
  have hU : ∀ a : A, IsUnit a ↔ v (a : K) = 1 := by
    intro a
    constructor
    · rintro ⟨u, rfl⟩
      have h1 : v ((u : A) : K) ≤ 1 := hmemA _
      have h2 : v (((u⁻¹ : Aˣ) : A) : K) ≤ 1 := hmemA _
      have h3 : v ((u : A) : K) * v (((u⁻¹ : Aˣ) : A) : K) = 1 := by
        rw [← map_mul]
        have e : ((u : A) : K) * (((u⁻¹ : Aˣ) : A) : K) = 1 :=
          congrArg (fun z : A => (z : K)) u.mul_inv
        rw [e, map_one]
      have hp := v.nonneg ((u : A) : K)
      have hq := v.nonneg (((u⁻¹ : Aˣ) : A) : K)
      exact le_antisymm h1 (by nlinarith)
    · intro h
      have ha0 : (a : K) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h
        exact zero_ne_one h
      have hb : v ((a : K)⁻¹) ≤ 1 := by
        rw [map_inv₀, h]
        simp
      exact IsUnit.of_mul_eq_one (⟨(a : K)⁻¹, hb⟩ : A) (Subtype.ext (mul_inv_cancel₀ ha0))
  have hM : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A ↔ v (a : K) < 1 := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hU]
    exact ⟨fun h => lt_of_le_of_ne (hmemA a) h, fun h => h.ne⟩
  have hfwd : IsDiscreteAbv v → (IsLocalRing.maximalIdeal A).IsPrincipal := by
    intro hd
    by_cases hnt : v.IsNontrivial
    · obtain ⟨ord, ⟨p0, hp0, hop0⟩, hmul, hle, hlt⟩ := exists_ord_of_discrete v hv hnt hd
      have hp0A : v p0 ≤ 1 := (hle p0 hp0).2 (by omega)
      refine ⟨⟨⟨p0, hp0A⟩, ?_⟩⟩
      ext a
      rw [hM, Ideal.mem_span_singleton]
      constructor
      · intro ha
        by_cases ha0 : (a : K) = 0
        · exact ⟨0, Subtype.ext (by simp [ha0])⟩
        · have hord : 0 < ord a := (hlt _ ha0).1 ha
          have hb0 : (a : K) / p0 ≠ 0 := div_ne_zero ha0 hp0
          have hrel : ord (a : K) = ord ((a : K) / p0) + 1 := by
            have := hmul ((a : K) / p0) p0 hb0 hp0
            rw [div_mul_cancel₀ _ hp0, hop0] at this
            exact this
          have hbA : v ((a : K) / p0) ≤ 1 := (hle _ hb0).2 (by omega)
          refine ⟨⟨(a : K) / p0, hbA⟩, Subtype.ext ?_⟩
          show (a : K) = p0 * ((a : K) / p0)
          field_simp
      · rintro ⟨c, rfl⟩
        show v (p0 * (c : K)) < 1
        rw [map_mul]
        have h1 : v p0 < 1 := (hlt p0 hp0).2 (by omega)
        have h2 := hmemA c
        calc v p0 * v (c : K) ≤ v p0 * 1 := mul_le_mul_of_nonneg_left h2 (v.nonneg _)
          _ < 1 := by linarith
    · have htriv : ∀ x : K, x ≠ 0 → v x = 1 := by
        intro x hx
        by_contra h
        exact hnt ⟨x, hx, h⟩
      refine ⟨⟨0, ?_⟩⟩
      ext a
      rw [hM, Ideal.mem_span_singleton, zero_dvd_iff]
      constructor
      · intro ha
        by_contra hne
        have : (a : K) ≠ 0 := fun h0 => hne (Subtype.ext h0)
        have := htriv _ this
        linarith
      · rintro rfl
        simp
  have hbwd : (IsLocalRing.maximalIdeal A).IsPrincipal → IsDiscreteAbv v := by
    rintro ⟨⟨p0, hp0⟩⟩
    have hgap : ∀ x : K, x ≠ 0 → v x < 1 → v x ≤ v (p0 : K) := by
      intro x hx hx1
      have hxA : v x ≤ 1 := hx1.le
      have hmem : (⟨x, hxA⟩ : A) ∈ IsLocalRing.maximalIdeal A := (hM _).2 hx1
      rw [hp0, Ideal.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have : x = (p0 : K) * c := congrArg (fun z : A => (z : K)) hc
      rw [this, map_mul]
      calc v (p0 : K) * v (c : K) ≤ v (p0 : K) * 1 :=
            mul_le_mul_of_nonneg_left (hmemA c) (v.nonneg _)
        _ = v (p0 : K) := mul_one _
    have hp1 : v (p0 : K) < 1 :=
      (hM p0).1 (by rw [hp0]; exact Ideal.mem_span_singleton_self p0)
    refine isDiscreteAbv_of_gap v (ρ := max (v (p0 : K)) (1 / 2))
      (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) (max_lt hp1 (by norm_num)) ?_
    rintro x hx ⟨h1, h2⟩
    have h3 := hgap x hx h2
    have h4 := le_max_left (v (p0 : K)) (1 / 2)
    linarith
  refine ⟨hU, hM, ⟨hfwd, hbwd⟩, ?_⟩
  intro hd hnt
  obtain ⟨ord, ⟨p0, hp0, hop0⟩, hmul, hle, hlt⟩ := exists_ord_of_discrete v hv hnt hd
  have hp0A : v p0 ≤ 1 := (hle p0 hp0).2 (by omega)
  have hord1 : ∀ x : K, x ≠ 0 → ord x = 0 → v x = 1 := by
    intro x hx h0
    refine le_antisymm ((hle x hx).2 h0.ge) (not_lt.1 fun h => ?_)
    have := (hlt x hx).1 h
    omega
  have hordpow : ∀ n : ℕ, ord (p0 ^ n) = n := by
    intro n
    induction n with
    | zero =>
      have := hmul 1 1 one_ne_zero one_ne_zero
      simp only [mul_one] at this
      simpa using (by omega : ord 1 = 0)
    | succ n ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero n hp0) hp0, ih, hop0]
      push_cast; ring
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨⟨p0, hp0A⟩, ⟨?_, ?_⟩, ?_⟩
  · intro hu
    have hu' : v p0 = 1 := (hU _).1 hu
    have := (hlt p0 hp0).2 (by omega)
    linarith
  · intro a b hab
    have hab' : p0 = (a : K) * (b : K) := congrArg (fun z : A => (z : K)) hab
    have ha0 : (a : K) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hab'
      exact hp0 hab'
    have hb0 : (b : K) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hab'
      exact hp0 hab'
    have h1 := hmul _ _ ha0 hb0
    rw [← hab', hop0] at h1
    have h2 : 0 ≤ ord (a : K) := (hle _ ha0).1 (hmemA a)
    have h3 : 0 ≤ ord (b : K) := (hle _ hb0).1 (hmemA b)
    by_cases h4 : ord (a : K) = 0
    · exact Or.inl ((hU a).2 (hord1 _ ha0 h4))
    · exact Or.inr ((hU b).2 (hord1 _ hb0 (by omega)))
  · intro x hx
    have hx0 : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
    have hordx : 0 ≤ ord (x : K) := (hle _ hx0).1 (hmemA x)
    refine ⟨(ord (x : K)).toNat, ?_⟩
    have hpn0 : p0 ^ (ord (x : K)).toNat ≠ 0 := pow_ne_zero _ hp0
    have hu0 : (x : K) / p0 ^ (ord (x : K)).toNat ≠ 0 := div_ne_zero hx0 hpn0
    have hrel : ord (x : K) = ord ((x : K) / p0 ^ (ord (x : K)).toNat) + (ord (x : K)).toNat := by
      have := hmul ((x : K) / p0 ^ (ord (x : K)).toNat) _ hu0 hpn0
      rw [div_mul_cancel₀ _ hpn0, hordpow] at this
      exact this
    have hv1 : v ((x : K) / p0 ^ (ord (x : K)).toNat) = 1 := hord1 _ hu0 (by omega)
    have hunit : IsUnit (⟨(x : K) / p0 ^ (ord (x : K)).toNat, hv1.le⟩ : A) := (hU _).2 hv1
    refine ⟨hunit.unit, Subtype.ext ?_⟩
    show p0 ^ (ord (x : K)).toNat * ((x : K) / p0 ^ (ord (x : K)).toNat) = x
    field_simp

/-- If some `a ≠ 0` with `|a| < 1` has `n`-th roots for all `n > 0`, the absolute value is not
discrete: the roots have absolute values accumulating at `1`. -/
private lemma not_isDiscreteAbv_of_roots (v : AbsoluteValue K ℝ) (a : K) (ha0 : a ≠ 0)
    (ha1 : v a < 1) (hroots : ∀ n : ℕ, 0 < n → ∃ z : K, z ^ n = a) : ¬ IsDiscreteAbv v := by
  intro hd
  unfold IsDiscreteAbv at hd
  rw [discreteTopology_iff_isOpen_singleton] at hd
  have h1 := hd ⟨1, ⟨1, by simp⟩⟩
  rw [isOpen_induced_iff] at h1
  obtain ⟨t, ht, hts⟩ := h1
  have h1t : (1 : ℝ) ∈ t := by
    have : (⟨1, ⟨1, by simp⟩⟩ : Set.range fun x : Kˣ => v (x : K)) ∈
        Subtype.val ⁻¹' t := by rw [hts]; rfl
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ht 1 h1t
  set r : ℝ := max (1 - ε / 2) 0 with hr
  have hr1 : r < 1 := max_lt (by linarith) one_pos
  have hr0 : 0 ≤ r := le_max_right _ _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (v.pos ha0) hr1
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hn; linarith [v.pos ha0]
    · exact h
  obtain ⟨z, hz⟩ := hroots n hn0
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0.ne'] at hz
    exact ha0 hz.symm
  have hvz : v z ^ n = v a := by rw [← hz, map_pow]
  have hgt : r < v z := by
    by_contra hle
    rw [not_lt] at hle
    have := pow_le_pow_left₀ (v.nonneg z) hle n
    linarith
  have hlt : v z < 1 := by
    by_contra hge
    rw [not_lt] at hge
    have := one_le_pow₀ hge (n := n)
    linarith
  have hmem : (⟨v z, ⟨Units.mk0 z hz0, rfl⟩⟩ : Set.range fun x : Kˣ => v (x : K)) ∈
      Subtype.val ⁻¹' t := by
    show v z ∈ t
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have : 1 - ε / 2 ≤ r := le_max_left _ _
    constructor <;> linarith
  rw [hts] at hmem
  have := congrArg Subtype.val (Set.mem_singleton_iff.1 hmem)
  simp only at this
  linarith

/-- **Remark 7.7**, on $\overline{\mathbb Q}_p$: the absolute value of the algebraic closure $\overline{\mathbb Q}_p$ of
$\mathbb Q_p$ (Mathlib's `PadicAlgCl p`, normed by the unique extension of $|\cdot|_p$) is nonarchimedean,
nontrivial, and not discrete: $|p^{1/n}| = p^{-1/n} \to 1$. -/
@[kb "milne2020ant" "v3.08, Remark 7.7, p. 107"]
theorem remark_7_7 (p : ℕ) [Fact p.Prime] :
    IsNonarchimedean (NormedField.toAbsoluteValue (PadicAlgCl p)) ∧
    (NormedField.toAbsoluteValue (PadicAlgCl p)).IsNontrivial ∧
    ¬ IsDiscreteAbv (NormedField.toAbsoluteValue (PadicAlgCl p)) := by
  have hnorm_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    have := PadicAlgCl.norm_extends p (p : ℚ_[p])
    rw [Padic.norm_p] at this
    rw [← this]
    simp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm_p
    have : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by linarith)
    linarith
  have hlt : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [hnorm_p]
    exact inv_lt_one_of_one_lt₀ hp1
  refine ⟨PadicAlgCl.isNonarchimedean p, ⟨(p : PadicAlgCl p), hp0, ?_⟩, ?_⟩
  · show ‖(p : PadicAlgCl p)‖ ≠ 1
    exact hlt.ne
  · exact not_isDiscreteAbv_of_roots _ (p : PadicAlgCl p) hp0 hlt
      fun n hn => IsAlgClosed.exists_pow_nat_eq _ hn

/-- **Remark 7.7**, Milne's form: there is a nonarchimedean absolute value on an algebraic closure
$\mathbb Q^{\mathrm{al}}$ of $\mathbb Q$ that extends $|\cdot|_p$ and is not discrete. -/
@[kb "milne2020ant" "v3.08, Remark 7.7, p. 107"]
theorem remark_7_7_algebraicClosure (p : ℕ) [Fact p.Prime] :
    ∃ v : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean v ∧
      (∀ q : ℚ, v (algebraMap ℚ (AlgebraicClosure ℚ) q) = padicNorm p q) ∧ ¬ IsDiscreteAbv v := by
  classical
  let φ : AlgebraicClosure ℚ →+* PadicAlgCl p :=
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := PadicAlgCl p)).toRingHom
  have hφ : Function.Injective φ := φ.injective
  let w : AbsoluteValue (AlgebraicClosure ℚ) ℝ := (NormedField.toAbsoluteValue (PadicAlgCl p)).comp hφ
  have hw : ∀ x, w x = ‖φ x‖ := fun x => rfl
  have hq : ∀ q : ℚ, w (algebraMap ℚ (AlgebraicClosure ℚ) q) = padicNorm p q := by
    intro q
    rw [hw]
    have : φ (algebraMap ℚ (AlgebraicClosure ℚ) q) = algebraMap ℚ_[p] (PadicAlgCl p) (q : ℚ_[p]) := by
      simp [φ]
    rw [this]
    exact (PadicAlgCl.norm_extends p (q : ℚ_[p])).trans (Padic.eq_padicNorm q)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpq : w (p : AlgebraicClosure ℚ) = (p : ℝ)⁻¹ := by
    have := hq (p : ℚ)
    rw [map_natCast] at this
    rw [this, padicNorm.padicNorm_p_of_prime]
    push_cast
    rfl
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    rw [h, map_zero] at hpq
    have : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by linarith)
    linarith
  refine ⟨w, ?_, hq, ?_⟩
  · intro x y
    rw [hw, hw, hw, map_add]
    exact PadicAlgCl.isNonarchimedean p _ _
  · exact not_isDiscreteAbv_of_roots w (p : AlgebraicClosure ℚ) hp0 (by rw [hpq]; exact inv_lt_one_of_one_lt₀ hp1)
      fun n hn => IsAlgClosed.exists_pow_nat_eq _ hn

/-- **Remark 7.7**, value group: $|\overline{\mathbb Q}_p^{\times}| = \{p^r : r \in \mathbb Q\}$ ("in fact one can
show"). -/
@[kb "milne2020ant" "v3.08, Remark 7.7, p. 107"]
theorem remark_7_7_valueGroup (p : ℕ) [Fact p.Prime] :
    Set.range (fun x : (PadicAlgCl p)ˣ => ‖(x : PadicAlgCl p)‖) = {y | ∃ r : ℚ, y = (p : ℝ) ^ (r : ℝ)} := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hnorm_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    have := PadicAlgCl.norm_extends p (p : ℚ_[p])
    rw [Padic.norm_p] at this
    rw [← this]
    simp
  have hpK : (p : PadicAlgCl p) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm_p
    have : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 hp0
    linarith
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    have hx0 : (u : PadicAlgCl p) ≠ 0 := u.ne_zero
    have h1 := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) (u : PadicAlgCl p)
    rw [PadicAlgCl.spectralNorm_eq] at h1
    have ha0 : (minpoly ℚ_[p] (u : PadicAlgCl p)).coeff 0 ≠ 0 :=
      minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral _) hx0
    rw [Padic.norm_eq_zpow_neg_valuation ha0] at h1
    refine ⟨(-((minpoly ℚ_[p] (u : PadicAlgCl p)).coeff 0).valuation : ℚ) /
      (minpoly ℚ_[p] (u : PadicAlgCl p)).natDegree, ?_⟩
    show ‖(u : PadicAlgCl p)‖ = _
    rw [h1, ← Real.rpow_intCast, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  · rintro ⟨r, rfl⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((p : PadicAlgCl p) ^ (-r.num)) r.den_pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow r.den_nz] at hz
      exact zpow_ne_zero _ hpK hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    show ‖z‖ = _
    rw [← pow_left_inj₀ (norm_nonneg z) (by positivity) r.den_nz, ← norm_pow, hz, norm_zpow,
      hnorm_p, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    have : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by exact_mod_cast Rat.mul_den_eq_num r
    rw [this, Real.rpow_intCast, inv_zpow, zpow_neg, inv_inv]

/-! ## Properties of nonarchimedean absolute values (7.9–7.11) -/

section Para

variable (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
include hv

/-- **7.9.** For a nonarchimedean absolute value, $|a + b| = \max(|a|, |b|)$ when $|a| \ne |b|$. -/
@[kb "milne2020ant" "v3.08, 7.9, p. 109"]
theorem para_7_9 {a b : K} (h : v a ≠ v b) : v (a + b) = max (v a) (v b) :=
  hv.add_eq_max_of_ne (fun x => v.map_neg x) h

/-- **7.10.** If $x$ is closer to $b$ than to $a$, then $d(a, x) = d(a, b)$, where $d(a,b) = |a - b|$. -/
@[kb "milne2020ant" "v3.08, 7.10, p. 109"]
theorem para_7_10 {a b x : K} (h : v (x - b) < v (x - a)) : v (a - x) = v (a - b) := by
  have h' : v (x - b) < v (a - x) := by rwa [v.map_sub a x]
  have := hv.add_eq_left_of_lt (fun y => v.map_neg y) h'
  rw [show a - b = (a - x) + (x - b) by ring, this]

/-- **7.11.** If $a_1 + \dots + a_n = 0$, then the maximum of the $|a_i|$ is attained for at least two indices.
Hypothesis added: not all $a_i$ vanish (for a single summand $a_1 = 0$ the claim fails literally). -/
@[kb "milne2020ant" "v3.08, 7.11, p. 109"]
theorem para_7_11 {ι : Type*} (s : Finset ι) (a : ι → K) (hsum : ∑ i ∈ s, a i = 0) (hne : ∃ i ∈ s, a i ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ v (a i) = v (a j) ∧ ∀ k ∈ s, v (a k) ≤ v (a i) := by
  classical
  obtain ⟨i₁, hi₁, hne₁⟩ := hne
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image s (fun i => v (a i)) ⟨i₁, hi₁⟩
  have hpos : 0 < v (a i₀) := lt_of_lt_of_le (v.pos hne₁) (hmax i₁ hi₁)
  by_contra hcon
  have hlt : ∀ j ∈ s, j ≠ i₀ → v (a j) < v (a i₀) := by
    intro j hj hji
    refine lt_of_le_of_ne (hmax j hj) fun heq => hcon ⟨i₀, hi₀, j, hj, hji.symm, heq.symm, hmax⟩
  have := hv.apply_sum_eq_of_lt (g := a) (fun y => v.map_neg y) hi₀ hlt
  rw [hsum, map_zero] at this
  exact hpos.ne this

end Para

/-! ## Weak approximation -/

/-- **Lemma 7.19.** If $|\cdot|_1, \dots, |\cdot|_n$ are nontrivial pairwise inequivalent absolute values on $K$, then
for every $\varepsilon > 0$ there is an element of $K$ within $\varepsilon$ of $1$ for $|\cdot|_{i_0}$ and within
$\varepsilon$ of $0$ for every $|\cdot|_j$, $j \ne i_0$. -/
@[kb "milne2020ant" "v3.08, Lemma 7.19, p. 114"]
theorem lemma_7_19 {ι : Type*} [Finite ι] {v : ι → AbsoluteValue K ℝ} (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) (i₀ : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : K, v i₀ (b - 1) < ε ∧ ∀ j ≠ i₀, v j b < ε := by
  classical
  have := Fintype.ofFinite ι
  have hd := AbsoluteValue.denseRange_algebraMap_pi h hv
  let z : (i : ι) → WithAbs (v i) := fun j => if j = i₀ then 1 else 0
  obtain ⟨b, hb⟩ := Metric.denseRange_iff.1 hd z ε hε
  have hb' := (dist_pi_lt_iff hε).1 hb
  refine ⟨b, ?_, fun j hj => ?_⟩
  · have := hb' i₀
    simp [z, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] at this
    have e : (algebraMap K (WithAbs (v i₀)) b).ofAbs = b := rfl
    rw [e, AbsoluteValue.map_sub] at this
    exact this
  · have := hb' j
    simp [z, hj, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] at this
    have e : (algebraMap K (WithAbs (v j)) b).ofAbs = b := rfl
    rw [e] at this
    exact this

/-- **Corollary 7.21.** Let $|\cdot|_1, \dots, |\cdot|_n$ be nontrivial pairwise inequivalent absolute values on $K$.
If $|a|_1^{r_1} \cdots |a|_n^{r_n} = 1$ for all $a \in K^\times$, with $r_i \in \mathbb R$, then all $r_i = 0$. -/
@[kb "milne2020ant" "v3.08, Cor. 7.21, p. 114"]
theorem cor_7_21 {ι : Type*} [Fintype ι] {v : ι → AbsoluteValue K ℝ} (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) (r : ι → ℝ)
    (hprod : ∀ a : K, a ≠ 0 → ∏ i, v i a ^ r i = 1) : ∀ i, r i = 0 := by
  classical
  have hd := AbsoluteValue.denseRange_algebraMap_pi h hv
  intro i
  obtain ⟨c, hc0, hc1⟩ := h i
  let z : (j : ι) → WithAbs (v j) := fun j => if j = i then WithAbs.toAbs (v j) c else 1
  let F : ((j : ι) → WithAbs (v j)) → ℝ := fun x => ∏ j, ‖x j‖ ^ r j
  have hz : ∀ j, z j ≠ 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa [z] using hc0
    · simp [z, hj]
  have hFz : F z = (v i c) ^ r i := by
    simp only [F, z]
    rw [Finset.prod_eq_single i]
    · simp [WithAbs.norm_eq_apply_ofAbs]
    · intro j _ hj; simp [hj]
    · simp
  have hcont : ContinuousAt F z := by
    have : ∀ j ∈ (Finset.univ : Finset ι),
        ContinuousAt (fun x : (j : ι) → WithAbs (v j) => ‖x j‖ ^ r j) z := fun j _ =>
      ((continuous_apply j).continuousAt.norm).rpow_const (Or.inl (norm_ne_zero_iff.2 (hz j)))
    exact tendsto_finsetProd Finset.univ (fun j hj => (this j hj).tendsto)
  by_contra hri
  have hne : F z ≠ 1 := by
    rw [hFz]
    intro h1
    have hpos : 0 < v i c := (v i).pos hc0
    rw [Real.rpow_def_of_pos hpos, Real.exp_eq_one_iff] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hc1 (Real.eq_one_of_pos_of_log_eq_zero hpos h2)
    · exact hri h2
  have hev1 := hcont.eventually_ne hne
  have hev2 : ∀ᶠ x in 𝓝 z, ∀ j, x j ≠ 0 :=
    eventually_all.2 fun j => (continuous_apply j).continuousAt.eventually_ne (hz j)
  have hmem : z ∈ closure (Set.range (algebraMap K ((j : ι) → WithAbs (v j)))) := hd z
  obtain ⟨x, hx, ⟨b, rfl⟩⟩ := mem_closure_iff_nhds.1 hmem _ (hev1.and hev2)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hx.2 i (by simp)
  apply hx.1
  exact hprod b hb0

end NumberFieldKB.MilneANT
