import Mathlib
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, VII.§5, Lemma 6 (the cut-off integral $\Lambda(s)$)

$N$ is $\mathbb R_+^\times$ with $d\nu(n)=n^{-1}dn$, or the group $\{Q^\nu\}_{\nu\in\mathbb Z}$ ($Q>1$) with
$\nu(\{1\})=1$ (counting measure). $F_1$ is a measurable function on $N$ with $0\le F_1\le1$, and there is a compact
interval $[t_0,t_1]\subset\mathbb R_+^\times$ with $F_1(n)=1$ for $n<t_0$ and $F_1(n)=0$ for $n>t_1$. Then
$\Lambda(s)=\int_NF_1(n)n^s\,d\nu(n)$ converges absolutely for $\operatorname{Re}s>0$; with $\Lambda_0(s)=s^{-1}$
(resp. $\tfrac12(1+Q^{-s})(1-Q^{-s})^{-1}$), $\Lambda-\Lambda_0$ extends to an entire function; and if
$F_1(n)+F_1(n^{-1})=1$ for all $n\in N$, then $\Lambda(s)+\Lambda(-s)=0$.

For $N=\mathbb R_+^\times$, $\Lambda$ is Mathlib's Mellin transform `mellin F₁ s` $=\int_0^\infty t^{s-1}F_1(t)\,dt$
and absolute convergence is `MellinConvergent`. The meromorphic continuation is stated as: there is an entire $g$ with
$\Lambda=\Lambda_0+g$ on $\operatorname{Re}s>0$ (such a $g$ is unique), and the functional equation is
$(\Lambda_0+g)(s)+(\Lambda_0+g)(-s)=0$ away from the poles of $\Lambda_0$.

* **`weil_VII_5_lemma6_real`**: $N=\mathbb R_+^\times$.
* **`weil_VII_5_lemma6_discrete`**: $N=\{Q^\nu\}$; $F_1$ is given on $\mathbb R$ and only its values at the points
  $Q^\nu$ matter.

*Proof* (Weil's). For $f_1=1$ on $(0,1)$, $f_1(1)=\tfrac12$, $f_1=0$ on $(1,\infty)$, $\Lambda=\Lambda_0$. The difference
$F_1-f_1$ is bounded with compact support in $N$, so its transform is entire; $f_1$ and $F_1$ both satisfy
$F(n)+F(n^{-1})=1$, so $F_2=F_1-f_1$ satisfies $F_2(n^{-1})=-F_2(n)$, and $n\mapsto n^{-1}$ gives oddness.
-/

noncomputable section

open MeasureTheory Set

namespace NumberFieldKB.WeilBNT

/-- The Mellin transform only sees a function on `(0, ∞)`. -/
lemma mellin_congr_Ioi {f g : ℝ → ℂ} (h : EqOn f g (Ioi 0)) (s : ℂ) :
    mellin f s = mellin g s := by
  unfold mellin
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by simp only [h ht])

/-- Mellin convergence only depends on a function on `(0, ∞)`. -/
lemma mellinConvergent_congr_Ioi {f g : ℝ → ℂ} (h : EqOn f g (Ioi 0)) {s : ℂ}
    (hf : MellinConvergent f s) : MellinConvergent g s := by
  unfold MellinConvergent at *
  exact hf.congr_fun (fun t ht => by simp only [h ht]) measurableSet_Ioi

/-- A bounded measurable function supported in a compact interval `[a, b]` with `0 < a` has an
everywhere convergent and entire Mellin transform. -/
lemma mellin_compact_support {G : ℝ → ℂ} (hG : Measurable G) (hb : ∀ t, ‖G t‖ ≤ 1) {a b : ℝ}
    (ha : 0 < a) (hz : ∀ t, t ∉ Icc a b → G t = 0) :
    (∀ s : ℂ, MellinConvergent G s) ∧ Differentiable ℂ (mellin G) := by
  have hint : Integrable G := by
    refine Integrable.mono' (g := indicator (Icc a b) fun _ => (1 : ℝ)) ?_
      hG.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    · exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
    · by_cases hm : t ∈ Icc a b
      · simpa [Set.indicator_of_mem hm] using hb t
      · simp [Set.indicator_of_notMem hm, hz t hm]
  have hloc : LocallyIntegrableOn G (Ioi 0) := hint.locallyIntegrable.locallyIntegrableOn _
  have htop : ∀ c : ℝ, G =O[Filter.atTop] (· ^ (-c)) := by
    intro c
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Filter.eventually_gt_atTop b] with t ht
    rw [hz t (fun hm => absurd hm.2 (not_le.2 ht))]
    simp
  have hbot : ∀ c : ℝ, G =O[nhdsWithin 0 (Ioi 0)] (· ^ (-c)) := by
    intro c
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT ha] with t ht
    rw [hz t (fun hm => absurd hm.1 (not_le.2 ht.2))]
    simp
  refine ⟨fun s => mellinConvergent_of_isBigO_rpow hloc (htop (s.re + 1)) (lt_add_one _)
    (hbot (s.re - 1)) (by linarith), fun s => ?_⟩
  exact mellin_differentiableAt_of_isBigO_rpow hloc (htop (s.re + 1)) (lt_add_one _)
    (hbot (s.re - 1)) (by linarith)

/-- **Weil, VII.§5, Lemma 6**, $N=\mathbb R_+^\times$, $d\nu=n^{-1}dn$: $\Lambda(s)=\int_0^\infty F_1(n)n^{s-1}dn$
converges absolutely for $\operatorname{Re}s>0$, $\Lambda=s^{-1}+g$ there with $g$ entire, and if
$F_1(n)+F_1(n^{-1})=1$ then $\Lambda(s)+\Lambda(-s)=0$ for the continuation ($s\ne0$). -/
@[kb "weil1973bnt" "Ch. VII, §5, Lemma 6 (N = R_+^x)"]
theorem weil_VII_5_lemma6_real (F₁ : ℝ → ℝ) (hF : Measurable F₁)
    (h01 : ∀ n : ℝ, 0 < n → 0 ≤ F₁ n ∧ F₁ n ≤ 1) {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁)
    (h1 : ∀ n : ℝ, 0 < n → n < t₀ → F₁ n = 1) (h0 : ∀ n : ℝ, t₁ < n → F₁ n = 0) :
    (∀ s : ℂ, 0 < s.re → MellinConvergent (fun n => (F₁ n : ℂ)) s) ∧
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
        (∀ s : ℂ, 0 < s.re → mellin (fun n => (F₁ n : ℂ)) s = s⁻¹ + g s) ∧
        ((∀ n : ℝ, 0 < n → F₁ n + F₁ n⁻¹ = 1) → ∀ s : ℂ, s ≠ 0 → (s⁻¹ + g s) + ((-s)⁻¹ + g (-s)) = 0) := by
  set I : ℝ → ℂ := indicator (Ioc 0 1) (fun _ => (1 : ℂ)) with hI
  set a := min t₀ 1 with ha_def
  set b := max t₁ 1 with hb_def
  have ha : 0 < a := lt_min ht₀ one_pos
  set F₂ : ℝ → ℂ := fun t => (F₁ t : ℂ) - I t with hF₂
  set G : ℝ → ℂ := indicator (Icc a b) F₂ with hG
  have hI1 : ∀ t, 0 < t → t ≤ 1 → I t = 1 := fun t ht h => by
    simp [hI, Set.indicator_of_mem (show t ∈ Ioc 0 1 from ⟨ht, h⟩)]
  have hI0 : ∀ t, 1 < t → I t = 0 := fun t h => by
    simp [hI, Set.indicator_of_notMem (show t ∉ Ioc 0 1 from fun hh => absurd hh.2 (not_le.2 h))]
  have hF₂out : ∀ t, 0 < t → (t < a ∨ b < t) → F₂ t = 0 := by
    intro t ht hout
    rcases hout with h | h
    · have h1' : t < t₀ := lt_of_lt_of_le h (min_le_left _ _)
      have h2' : t < 1 := lt_of_lt_of_le h (min_le_right _ _)
      simp [hF₂, h1 t ht h1', hI1 t ht h2'.le]
    · have h1' : t₁ < t := lt_of_le_of_lt (le_max_left _ _) h
      have h2' : 1 < t := lt_of_le_of_lt (le_max_right _ _) h
      simp [hF₂, h0 t h1', hI0 t h2']
  have hGF : ∀ t, 0 < t → G t = F₂ t := by
    intro t ht
    by_cases hm : t ∈ Icc a b
    · simp [hG, Set.indicator_of_mem hm]
    · rw [hG, Set.indicator_of_notMem hm]
      refine (hF₂out t ht ?_).symm
      by_cases hta : t < a
      · exact Or.inl hta
      · exact Or.inr (by simpa [mem_Icc, not_lt.1 hta] using hm)
  have hGz : ∀ t, t ∉ Icc a b → G t = 0 := fun t hm => by
    rw [hG, Set.indicator_of_notMem hm]
  have hbound : ∀ t, ‖G t‖ ≤ 1 := by
    intro t
    by_cases hm : t ∈ Icc a b
    · have ht : 0 < t := lt_of_lt_of_le ha hm.1
      rw [hGF t ht]
      obtain ⟨h0', h1'⟩ := h01 t ht
      by_cases h : t ≤ 1
      · simp only [hF₂, hI1 t ht h]
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_le]
        constructor <;> linarith
      · simp only [hF₂, hI0 t (not_le.1 h), sub_zero]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith
    · simp [hGz t hm]
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ measurableSet_Icc
    exact (Complex.measurable_ofReal.comp hF).sub (measurable_const.indicator measurableSet_Ioc)
  obtain ⟨hGconv, hGdiff⟩ := mellin_compact_support hGm hbound ha hGz
  have hH : EqOn (fun n : ℝ => (F₁ n : ℂ)) (fun t => I t + G t) (Ioi 0) := by
    intro t ht
    have ht : 0 < t := ht
    simp only [hGF t ht, hF₂]
    ring
  have hHconv : ∀ s : ℂ, 0 < s.re → MellinConvergent (fun t => I t + G t) s := fun s hs =>
    (hasMellin_add (hasMellin_one_Ioc hs).1 (hGconv s)).1
  refine ⟨fun s hs => mellinConvergent_congr_Ioi hH.symm (hHconv s hs), mellin G, hGdiff, ?_, ?_⟩
  · intro s hs
    rw [mellin_congr_Ioi hH, (hasMellin_add (hasMellin_one_Ioc hs).1 (hGconv s)).2,
      (hasMellin_one_Ioc hs).2, one_div]
  · intro hsum s _
    have hodd : mellin G (-s) = - mellin G s := by
      rw [← mellin_comp_inv]
      have : mellin (fun t => G t⁻¹) s = mellin (fun t => - G t) s := by
        unfold mellin
        refine setIntegral_congr_ae measurableSet_Ioi ?_
        filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with t h1 ht
        have ht : 0 < t := ht
        have h1 : t ≠ 1 := h1
        have key : G t⁻¹ = - G t := by
          rw [hGF t ht, hGF t⁻¹ (inv_pos.2 ht)]
          have hs1 : F₁ t⁻¹ = 1 - F₁ t := by linarith [hsum t ht]
          have hcast : (F₁ t⁻¹ : ℂ) = 1 - F₁ t := by rw [hs1]; push_cast; ring
          rcases lt_or_gt_of_ne h1 with hlt | hgt
          · have e1 := hI1 t ht hlt.le
            have e2 := hI0 t⁻¹ ((one_lt_inv₀ ht).2 hlt)
            simp only [hF₂, e1, e2, hcast]; ring
          · have e1 := hI0 t hgt
            have e2 := hI1 t⁻¹ (inv_pos.2 ht) ((inv_le_one₀ ht).2 hgt.le)
            simp only [hF₂, e1, e2, hcast]; ring
        simp only [key]
      rw [this]
      unfold mellin
      simp [integral_neg]
    rw [inv_neg, hodd]
    ring

/-- Weil's $\Lambda_0$ for $N=\{Q^\nu\}$: $\tfrac12(1+Q^{-s})(1-Q^{-s})^{-1}$. -/
def lambdaZeroDiscrete (Q : ℝ) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (1 + (Q : ℂ) ^ (-s)) * (1 - (Q : ℂ) ^ (-s))⁻¹

/-- `((Q ^ ν : ℝ) : ℂ) ^ s = exp (ν * log Q * s)`. -/
lemma zpow_cpow_eq {Q : ℝ} (hQ : 0 < Q) (ν : ℤ) (s : ℂ) :
    ((Q ^ ν : ℝ) : ℂ) ^ s = Complex.exp (ν * Real.log Q * s) := by
  have hpos : 0 < Q ^ ν := zpow_pos hQ ν
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le,
    Real.log_zpow]
  push_cast
  ring_nf

/-- `(Q : ℂ) ^ (-s) = exp (-(log Q * s))`. -/
lemma cpow_neg_eq {Q : ℝ} (hQ : 0 < Q) (s : ℂ) :
    (Q : ℂ) ^ (-s) = Complex.exp (-(Real.log Q * s)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hQ.ne'), ← Complex.ofReal_log hQ.le]
  congr 1
  ring

/-- The values of Weil's comparison function `f₁` on the points `Q ^ ν`: `1` for `ν < 0`, `1/2` for
`ν = 0`, `0` for `ν > 0`. -/
def discHalf (ν : ℤ) : ℝ := if ν < 0 then 1 else if ν = 0 then 1 / 2 else 0

/-- `f₁ (n) + f₁ (n⁻¹) = 1` for the comparison function. -/
lemma discHalf_add_neg (ν : ℤ) : discHalf ν + discHalf (-ν) = 1 := by
  rcases lt_trichotomy ν 0 with h | h | h
  · have h1 : ¬ (-ν < 0) := by omega
    have h2 : -ν ≠ 0 := by omega
    simp only [discHalf, if_pos h, if_neg h1, if_neg h2]
    norm_num
  · subst h
    norm_num [discHalf]
  · have h1 : -ν < 0 := by omega
    have h2 : ¬ ν < 0 := by omega
    have h3 : ν ≠ 0 := by omega
    simp only [discHalf, if_pos h1, if_neg h2, if_neg h3]
    norm_num

/-- The cut-off sum for the comparison function `f₁` is `lambdaZeroDiscrete`. -/
lemma hasSum_discHalf {Q : ℝ} (hQ : 1 < Q) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun ν : ℤ => (discHalf ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s) (lambdaZeroDiscrete Q s) := by
  have hQ0 : 0 < Q := by linarith
  set r : ℂ := (Q : ℂ) ^ (-s) with hr
  have hrn : ‖r‖ < 1 := by
    rw [hr, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by simpa using hs)
  have hr1 : 1 - r ≠ 0 := by
    intro h
    have : r = 1 := by linear_combination -h
    rw [this] at hrn
    simp at hrn
  have hpos : HasSum (fun n : ℕ => (discHalf (n : ℤ) : ℂ) * ((Q ^ (n : ℤ) : ℝ) : ℂ) ^ s)
      (1 / 2) := by
    have := hasSum_single (f := fun n : ℕ => (discHalf (n : ℤ) : ℂ) * ((Q ^ (n : ℤ) : ℝ) : ℂ) ^ s)
      0 (by
        intro n hn
        have h1 : ¬ ((n : ℤ) < 0) := by omega
        have h2 : (n : ℤ) ≠ 0 := by omega
        simp [discHalf, h1, h2, hn])
    simpa [discHalf] using this
  have hneg : HasSum
      (fun n : ℕ => (discHalf (-((n : ℤ) + 1)) : ℂ) * ((Q ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) ^ s)
      (r * (1 - r)⁻¹) := by
    have h := (hasSum_geometric_of_norm_lt_one hrn).mul_left r
    have e : (fun n : ℕ => (discHalf (-((n : ℤ) + 1)) : ℂ) *
        ((Q ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) ^ s) = fun n : ℕ => r * r ^ n := by
      funext n
      have h1 : -((n : ℤ) + 1) < 0 := by omega
      rw [zpow_cpow_eq hQ0, hr, cpow_neg_eq hQ0]
      simp only [discHalf, h1, if_true]
      rw [← Complex.exp_nat_mul, ← Complex.exp_add, Complex.ofReal_one, one_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact h
  have hlam : lambdaZeroDiscrete Q s = 1 / 2 + r * (1 - r)⁻¹ := by
    unfold lambdaZeroDiscrete
    rw [← hr]
    field_simp
    ring
  rw [hlam]
  exact HasSum.of_nat_of_neg_add_one
    (f := fun ν : ℤ => (discHalf ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s) hpos hneg

/-- The oddness of `lambdaZeroDiscrete` away from its poles. -/
lemma lambdaZeroDiscrete_add_neg {Q : ℝ} (hQ0 : 0 < Q) (s : ℂ) (hs : (Q : ℂ) ^ (-s) ≠ 1) :
    lambdaZeroDiscrete Q s + lambdaZeroDiscrete Q (-s) = 0 := by
  have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hprod : (Q : ℂ) ^ (-s) * (Q : ℂ) ^ (-(-s)) = 1 := by
    rw [← Complex.cpow_add _ _ hQne]
    simp
  unfold lambdaZeroDiscrete
  generalize (Q : ℂ) ^ (-(-s)) = r' at hprod ⊢
  generalize (Q : ℂ) ^ (-s) = r at hprod hs ⊢
  have hr0 : r ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hr' : r' = r⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have h1 : 1 - r ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  have h3 : r - 1 ≠ 0 := sub_ne_zero.2 hs
  subst hr'
  field_simp
  ring

/-- **Weil, VII.§5, Lemma 6**, $N=\{Q^\nu\}_{\nu\in\mathbb Z}$ with counting measure:
$\Lambda(s)=\sum_\nu F_1(Q^\nu)(Q^\nu)^s$ converges absolutely for $\operatorname{Re}s>0$, $\Lambda=\Lambda_0+g$ there with
$g$ entire, and if $F_1(n)+F_1(n^{-1})=1$ on $N$ then $\Lambda(s)+\Lambda(-s)=0$ for the continuation (away from the
poles $Q^{-s}=1$). -/
@[kb "weil1973bnt" "Ch. VII, §5, Lemma 6 (N = Q^Z)"]
theorem weil_VII_5_lemma6_discrete {Q : ℝ} (hQ : 1 < Q) (F₁ : ℝ → ℝ)
    (h01 : ∀ ν : ℤ, 0 ≤ F₁ (Q ^ ν) ∧ F₁ (Q ^ ν) ≤ 1) {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁)
    (h1 : ∀ ν : ℤ, Q ^ ν < t₀ → F₁ (Q ^ ν) = 1) (h0 : ∀ ν : ℤ, t₁ < Q ^ ν → F₁ (Q ^ ν) = 0) :
    (∀ s : ℂ, 0 < s.re → Summable fun ν : ℤ => ‖(F₁ (Q ^ ν) : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s‖) ∧
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
        (∀ s : ℂ, 0 < s.re →
          ∑' ν : ℤ, (F₁ (Q ^ ν) : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s = lambdaZeroDiscrete Q s + g s) ∧
        ((∀ ν : ℤ, F₁ (Q ^ ν) + F₁ ((Q ^ ν)⁻¹) = 1) → ∀ s : ℂ, (Q : ℂ) ^ (-s) ≠ 1 →
          (lambdaZeroDiscrete Q s + g s) + (lambdaZeroDiscrete Q (-s) + g (-s)) = 0) := by
  have hQ0 : 0 < Q := by linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt t₁ hQ
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt t₀⁻¹ hQ
  obtain ⟨N, hNn, hNm⟩ : ∃ N : ℕ, n ≤ N ∧ m ≤ N := ⟨n + m, by omega, by omega⟩
  have hupper : ∀ ν : ℤ, (N : ℤ) < ν → t₁ < Q ^ ν := by
    intro ν hν
    calc t₁ < Q ^ n := hn
      _ = Q ^ (n : ℤ) := (zpow_natCast Q n).symm
      _ < Q ^ ν := zpow_lt_zpow_right₀ hQ (by omega)
  have hlower : ∀ ν : ℤ, ν < -(N : ℤ) → Q ^ ν < t₀ := by
    intro ν hν
    have e1 : Q ^ ν < Q ^ (-(m : ℤ)) := zpow_lt_zpow_right₀ hQ (by omega)
    have e2 : Q ^ (-(m : ℤ)) < t₀ := by
      rw [zpow_neg, zpow_natCast]
      exact inv_lt_of_inv_lt₀ ht₀ hm
    exact e1.trans e2
  set F₂ : ℤ → ℝ := fun ν => F₁ (Q ^ ν) - discHalf ν with hF₂
  have hz : ∀ ν ∉ Finset.Icc (-(N : ℤ)) N, F₂ ν = 0 := by
    intro ν hν
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hν
    rcases hν with h | h
    · have e1 : ν < 0 := by omega
      have e := h1 ν (hlower ν h)
      simp [hF₂, discHalf, e1, e]
    · have e2 : ¬ ν < 0 := by omega
      have e3 : ν ≠ 0 := by omega
      have e := h0 ν (hupper ν h)
      simp [hF₂, discHalf, e2, e3, e]
  have hgsum : ∀ s : ℂ, HasSum (fun ν : ℤ => (F₂ ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s)
      (∑ ν ∈ Finset.Icc (-(N : ℤ)) N, (F₂ ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s) := fun s =>
    hasSum_sum_of_ne_finset_zero (fun ν hν => by rw [hz ν hν]; simp)
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, ∀ s, g s =
      ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, (F₂ ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s := ⟨_, fun s => rfl⟩
  have hterm : ∀ (s : ℂ) (ν : ℤ), (F₁ (Q ^ ν) : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s =
      (F₂ ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s + (discHalf ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s := by
    intro s ν
    simp only [hF₂]
    push_cast
    ring
  have hsumm : ∀ s : ℂ, 0 < s.re →
      HasSum (fun ν : ℤ => (F₁ (Q ^ ν) : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s)
        (g s + lambdaZeroDiscrete Q s) := by
    intro s hs
    have := (hgsum s).add (hasSum_discHalf hQ hs)
    rw [← hg] at this
    have e : (fun ν : ℤ => (F₁ (Q ^ ν) : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s) =
        fun ν : ℤ => (F₂ ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s +
          (discHalf ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s := funext (hterm s)
    rw [e]
    exact this
  have hdiff : Differentiable ℂ g := by
    have : g = fun s => ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, (F₂ ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s :=
      funext hg
    rw [this]
    refine Differentiable.fun_sum (fun ν _ => ?_)
    have hne : ((Q ^ ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (zpow_pos hQ0 ν).ne'
    exact (differentiable_id.const_cpow (Or.inl hne)).const_mul _
  have hgt : ∀ s, g s = ∑' ν : ℤ, (F₂ ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ s := fun s =>
    (hg s).trans (hgsum s).tsum_eq.symm
  refine ⟨fun s hs => summable_norm_iff.2 (hsumm s hs).summable, g, hdiff, ?_, ?_⟩
  · intro s hs
    rw [(hsumm s hs).tsum_eq, add_comm]
  · intro hsum s hs
    have hF₂odd : ∀ ν, F₂ (-ν) = - F₂ ν := by
      intro ν
      have := hsum ν
      rw [← zpow_neg] at this
      have hd := discHalf_add_neg ν
      simp only [hF₂]
      linarith
    have hodd : g (-s) = - g s := by
      rw [hgt, hgt, ← tsum_neg]
      have := Equiv.tsum_eq (Equiv.neg ℤ) (fun ν : ℤ => (F₂ ν : ℂ) * ((Q ^ ν : ℝ) : ℂ) ^ (-s))
      rw [← this]
      refine tsum_congr (fun ν => ?_)
      have e : ((Q ^ (Equiv.neg ℤ ν) : ℝ) : ℂ) ^ (-s) = ((Q ^ ν : ℝ) : ℂ) ^ s := by
        rw [zpow_cpow_eq hQ0, zpow_cpow_eq hQ0]
        congr 1
        simp only [Equiv.neg_apply]
        push_cast
        ring
      simp only [Equiv.neg_apply] at e ⊢
      rw [e, hF₂odd ν]
      push_cast
      ring
    have := lambdaZeroDiscrete_add_neg hQ0 s hs
    rw [hodd]
    linear_combination this

end NumberFieldKB.WeilBNT
