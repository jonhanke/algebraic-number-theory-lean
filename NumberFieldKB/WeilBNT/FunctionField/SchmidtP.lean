import NumberFieldKB.WeilBNT.FunctionField.Idele
import NumberFieldKB.WeilBNT.FunctionField.PlaceSplitting
import NumberFieldKB.WeilBNT.FunctionField.RiemannRochCor

/-!
# F. K. Schmidt's theorem with a finite set of excluded places (Weil VII.§5, Cor. 5 and 6)

For a global function field $k$ over $\mathbb F_q$:

* `Place.exists_not_mem`: $k$ has infinitely many places (no finite set contains them all). Proof: Euclid's
  argument with Riemann's inequality: if $P$ contained every place, an element $f$ with a pole only at $v_0\in P$ and
  zeros at the other places of $P$ would make $\operatorname{div}(1+f)$ a multiple of $v_0$ of degree $0$.
* `exists_valuation_eq`: for a finite set $P$ of places and integers $n_v$ there is $f\in k^\times$ with
  $\operatorname{ord}_v(f)=n_v$ for $v\in P$ (from Riemann–Roch, `weil_VI_2_cor2`, assuming $\mathbb F_q$ is the
  field of constants).
* **`weil_VII_5_cor5_P`**: Weil VII.§5, Cor. 5 in full: for every finite set $P$ of places there is a divisor of degree
  $1$ whose support does not meet $P$ (the case $P=\emptyset$ is `weil_VII_5_cor5_ff`).
* **`weil_VII_5_cor6`**: Weil VII.§5, Cor. 6: the values $\lvert z\rvert_{\mathbb A}$ of the idele norm are exactly
  the powers $q^n$, $n\in\mathbb Z$.
-/

open scoped WithZero NNReal
open Valuation

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

open Divisor

theorem sum_single_one_apply [DecidableEq (Place Fq k)] (P : Finset (Place Fq k)) (w : Place Fq k) :
    (∑ w' ∈ P, Finsupp.single w' (1 : ℤ) : Divisor Fq k) w = if w ∈ P then 1 else 0 := by
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- **A global function field has infinitely many places**: no finite set contains all of them. -/
theorem Place.exists_not_mem (P : Finset (Place Fq k)) : ∃ v : Place Fq k, v ∉ P := by
  classical
  by_contra hall
  push_neg at hall
  obtain ⟨v₀⟩ := Place.nonempty (Fq := Fq) (k := k)
  obtain ⟨γ, hγ⟩ := Divisor.exists_deg_sub_ell_le (Fq := Fq) (k := k)
  set B : Divisor Fq k := ∑ w ∈ P.erase v₀, Finsupp.single w 1 with hB
  set n : ℕ := (((0 : Divisor Fq k).ell : ℤ) + γ + deg B + 1).toNat with hn
  set A : Divisor Fq k := Finsupp.single v₀ (n : ℤ) - B with hA
  have hdegA : deg A = n * v₀.degree - deg B := by
    rw [hA, _root_.map_sub, deg_single]
  have hdeg1 : (n : ℤ) ≤ n * v₀.degree := by
    have : (1 : ℤ) ≤ v₀.degree := by exact_mod_cast v₀.degree_pos
    nlinarith
  have hell : ((0 : Divisor Fq k).ell : ℤ) < A.ell := by
    have := hγ A
    omega
  have hnle : ¬ A.riemannRochSpace ≤ (0 : Divisor Fq k).riemannRochSpace := fun h => by
    have := Submodule.finrank_mono h
    unfold ell at hell
    omega
  obtain ⟨f, hfA, hf0⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hfalg : ¬ IsAlgebraic Fq f := by rwa [← mem_riemannRochSpace_zero_iff]
  set g := 1 + f with hg
  have hgalg : ¬ IsAlgebraic Fq g := by
    intro h
    apply hfalg
    have h1 : IsAlgebraic Fq (g - 1) := h.sub (isAlgebraic_one (R := Fq))
    simpa [hg] using h1
  have hg0 : g ≠ 0 := fun h => hgalg (h ▸ isAlgebraic_zero)
  have hw : ∀ w : Place Fq k, w ≠ v₀ → w.valuation g = 1 := by
    intro w hw
    have hwP : w ∈ P.erase v₀ := Finset.mem_erase.2 ⟨hw, hall w⟩
    have hAw : A w = -1 := by
      rw [hA, Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hw), hB,
        sum_single_one_apply, if_pos hwP]
      rfl
    have hfw : w.valuation f < 1 := by
      have := (mem_riemannRochSpace_iff A f).1 hfA w
      rw [hAw] at this
      refine lt_of_le_of_lt this ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    exact Valuation.map_one_add_of_lt w.valuation hfw
  have hdiv : Divisor.div (Units.mk0 g hg0) = Finsupp.single v₀ (v₀.ord g) := by
    ext w
    by_cases h : w = v₀
    · subst h; simp
    · rw [Divisor.div_apply, Finsupp.single_apply, if_neg (Ne.symm h)]
      exact ord_eq_zero_of_valuation_eq_one w (hw w h)
  have hdeg := Divisor.deg_div_eq_zero (Fq := Fq) (Units.mk0 g hg0)
  rw [hdiv, deg_single] at hdeg
  have hord : v₀.ord g = 0 := by
    have : (v₀.degree : ℤ) ≠ 0 := by exact_mod_cast v₀.degree_pos.ne'
    rcases mul_eq_zero.1 hdeg with h | h
    · exact h
    · exact absurd h this
  have h0 : Divisor.div (Fq := Fq) (Units.mk0 g hg0) = 0 := by rw [hdiv, hord, Finsupp.single_zero]
  exact hgalg ((div_eq_zero_iff (Fq := Fq) _).1 h0)

theorem eq_exp_of_lt_of_le {x : ℤᵐ⁰} {m : ℤ} (h1 : WithZero.exp (m - 1) < x) (h2 : x ≤ WithZero.exp m) :
    x = WithZero.exp m := by
  have hx0 : x ≠ 0 := ne_bot_of_gt h1
  rw [← WithZero.exp_log hx0] at h1 h2 ⊢
  rw [WithZero.exp_lt_exp] at h1
  rw [WithZero.exp_le_exp] at h2
  congr 1
  omega

/-- **Approximation with prescribed orders**: for a finite set $P$ of places and integers $n_v$, there is $f\ne0$ in
$k$ with $v(f)=e^{-n_v}$, i.e. $\operatorname{ord}_v(f)=n_v$, for every $v\in P$ (from Riemann–Roch; $\mathbb F_q$ is
the field of constants). -/
theorem exists_valuation_eq (hc : IsConstantField Fq k) (P : Finset (Place Fq k)) (n : Place Fq k → ℤ) :
    ∃ f : k, f ≠ 0 ∧ ∀ v ∈ P, v.valuation f = WithZero.exp (-n v) := by
  classical
  obtain ⟨u, hu⟩ := Place.exists_not_mem P
  have key : ∀ v ∈ P, ∃ f : k, v.valuation f = WithZero.exp (-n v) ∧
      ∀ w ∈ P, w ≠ v → w.valuation f ≤ WithZero.exp (-n w - 1) := by
    intro v hv
    set C : Divisor Fq k := ∑ w ∈ P, Finsupp.single w (-n w - if w = v then 0 else 1) with hC
    have hCw : ∀ w ∈ P, C w = -n w - if w = v then 0 else 1 := by
      intro w hw
      rw [hC, Finsupp.finsetSum_apply, Finset.sum_eq_single w]
      · simp
      · intro b _ hb; simp [Finsupp.single_apply, hb]
      · intro h; exact absurd hw h
    set N : ℕ := (2 * Rep.genusInt Fq k - deg C + v.degree).toNat with hN
    set A : Divisor Fq k := C + Finsupp.single u (N : ℤ) with hA
    have hAw : ∀ w ∈ P, A w = C w := by
      intro w hw
      have : w ≠ u := fun h => hu (h ▸ hw)
      simp [hA, Finsupp.single_apply, Ne.symm this]
    have hdegu : (N : ℤ) ≤ N * u.degree := by
      have : (1 : ℤ) ≤ u.degree := by exact_mod_cast u.degree_pos
      nlinarith
    have hdegA : deg A = deg C + N * u.degree := by rw [hA, map_add, deg_single]
    set A' : Divisor Fq k := A - Finsupp.single v 1 with hA'
    have hdegA' : deg A' = deg A - v.degree := by rw [hA', _root_.map_sub, deg_single, one_mul]
    have h1 : 2 * Rep.genusInt Fq k - 2 < deg A' := by
      rw [hdegA', hdegA]
      omega
    have h2 : 2 * Rep.genusInt Fq k - 2 < deg A := by
      have := v.degree_pos
      rw [hdegA'] at h1
      omega
    have e1 := weil_VI_2_cor2 hc h1
    have e2 := weil_VI_2_cor2 hc h2
    have hlt : (A'.ell : ℤ) < A.ell := by
      have := v.degree_pos
      rw [hdegA'] at e1
      omega
    have hnle : ¬ A.riemannRochSpace ≤ A'.riemannRochSpace := fun h => by
      have := Submodule.finrank_mono h
      unfold ell at hlt
      omega
    obtain ⟨f, hfA, hfA'⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
    have hle := (mem_riemannRochSpace_iff A f).1 hfA
    have hnot : ¬ ∀ w : Place Fq k, w.valuation f ≤ WithZero.exp (A' w) :=
      fun h => hfA' ((mem_riemannRochSpace_iff _ f).2 h)
    push Not at hnot
    obtain ⟨w, hw⟩ := hnot
    have hwv : w = v := by
      by_contra hne
      have : A' w = A w := by
        simp [hA', Finsupp.single_apply, Ne.symm hne]
      rw [this] at hw
      exact absurd (hle w) (not_le.2 hw)
    subst hwv
    refine ⟨f, ?_, ?_⟩
    · have hAv : A w = -n w := by rw [hAw w hv, hCw w hv, if_pos rfl, sub_zero]
      have hlow : WithZero.exp (-n w - 1) < w.valuation f := by
        have : A' w = -n w - 1 := by simp [hA', hAv]
        rwa [this] at hw
      have hup : w.valuation f ≤ WithZero.exp (-n w) := by have := hle w; rwa [hAv] at this
      exact eq_exp_of_lt_of_le hlow hup
    · intro w' hw' hne
      have := hle w'
      rwa [hAw w' hw', hCw w' hw', if_neg hne] at this
  choose! F hFv hFw using key
  by_cases hP : P.Nonempty
  · set f := ∑ v ∈ P, F v with hf
    have hval : ∀ w ∈ P, w.valuation f = WithZero.exp (-n w) := by
      intro w hw
      have hsplit : f = F w + ∑ v ∈ P.erase w, F v := by
        rw [hf, Finset.add_sum_erase _ _ hw]
      have hrest : w.valuation (∑ v ∈ P.erase w, F v) < WithZero.exp (-n w) := by
        apply Valuation.map_sum_lt _ (WithZero.exp_ne_zero)
        intro v hv
        have hv' := Finset.mem_erase.1 hv
        refine lt_of_le_of_lt (hFw v hv'.2 w hw (Ne.symm hv'.1)) ?_
        rw [WithZero.exp_lt_exp]; omega
      rw [hsplit, Valuation.map_add_eq_of_lt_left, hFv w hw]
      rwa [hFv w hw]
    obtain ⟨w, hw⟩ := hP
    refine ⟨f, fun h0 => ?_, hval⟩
    have := hval w hw
    rw [h0, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  · rw [Finset.not_nonempty_iff_eq_empty] at hP
    exact ⟨1, one_ne_zero, by simp [hP]⟩

/-- **Weil VII.§5, Cor. 5** (F. K. Schmidt), for an arbitrary finite set $P$ of places: if $\mathbb F_q$ is the field
of constants of $k$, there is a divisor of degree $1$ whose support does not meet $P$. -/
@[kb "weil1973bnt" "Ch. VII, §5, Cor. 5 (p. 126), function fields, any finite set P"]
theorem weil_VII_5_cor5_P (hc : IsConstantField Fq k) (P : Finset (Place Fq k)) :
    ∃ a : Divisor Fq k, deg a = 1 ∧ ∀ v ∈ P, a v = 0 := by
  obtain ⟨a₀, ha₀⟩ := weil_VII_5_cor5_ff hc
  obtain ⟨f, hf0, hf⟩ := exists_valuation_eq hc P (fun v => -a₀ v)
  refine ⟨a₀ + Divisor.div (Units.mk0 f hf0), ?_, ?_⟩
  · rw [map_add, Divisor.deg_div_eq_zero, add_zero, ha₀]
  · intro v hv
    rw [Finsupp.add_apply, Divisor.div_apply, Units.val_mk0, Place.ord, hf v hv, WithZero.log_exp]
    ring

/-- **Weil VII.§5, Cor. 6**: if $\mathbb F_q$ is the field of constants of $k$, the values of the idele norm
$z\mapsto\lvert z\rvert_{\mathbb A}$ are exactly the powers $q^n$, $n\in\mathbb Z$: the value group is generated by
$q$. -/
@[kb "weil1973bnt" "Ch. VII, §5, Cor. 6 (p. 127), function fields, idele norm"]
theorem weil_VII_5_cor6 (hc : IsConstantField Fq k) :
    Set.range (FFIdeleGroup.norm (Fq := Fq) (k := k)) = Set.range (fun n : ℤ => (Nat.card Fq : ℝ≥0) ^ n) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, (FFIdeleGroup.norm_eq z).symm⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨a, ha⟩ := weil_VII_5_cor5_ff hc
    obtain ⟨z, hz⟩ := FFIdeleGroup.div_surjective ((-n) • a)
    refine ⟨z, ?_⟩
    rw [FFIdeleGroup.norm_eq, hz, map_zsmul, ha, smul_eq_mul, mul_one, neg_neg]

end NumberFieldKB.WeilBNT.FF
