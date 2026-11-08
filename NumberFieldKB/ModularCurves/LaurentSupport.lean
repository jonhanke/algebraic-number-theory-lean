import Mathlib

/-!
# Laurent series supported on the multiples of $g$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2: the width of a cusp of $X_0(N)$ is read off from which
powers of the local parameter occur. For $g \ge 1$, the Laurent series $\sum_n c_n q^n$ with $c_n = 0$ unless
$g \mid n$ form a subfield of $\mathbb C((q))$ (`supportMultiples g`, the image of $q \mapsto q^g$), and a nonzero
element of it has valuation $\exp(g k)$ for some $k \in \mathbb Z$ (`exists_valuation_eq_of_mem_supportMultiples`).
-/

noncomputable section

namespace NumberFieldKB.ModularCurves

variable {g : ℕ}

/-- $n \mapsto g n$ as an additive map $\mathbb Z \to \mathbb Z$. -/
def mulLeftHom (g : ℕ) : ℤ →+ ℤ := AddMonoidHom.mulLeft (g : ℤ)

theorem mulLeftHom_injective (hg : 0 < g) : Function.Injective (mulLeftHom g) := fun a b h =>
  mul_left_cancel₀ (by exact_mod_cast hg.ne' : (g : ℤ) ≠ 0) h

theorem mulLeftHom_le_iff (hg : 0 < g) (a b : ℤ) : mulLeftHom g a ≤ mulLeftHom g b ↔ a ≤ b :=
  mul_le_mul_iff_of_pos_left (by exact_mod_cast hg : (0 : ℤ) < g)

/-- $q \mapsto q^g$ on $\mathbb C((q))$. -/
def dilateHom (hg : 0 < g) : LaurentSeries ℂ →+* LaurentSeries ℂ :=
  HahnSeries.embDomainRingHom (mulLeftHom g) (mulLeftHom_injective hg) (mulLeftHom_le_iff hg)

/-- The subfield of Laurent series supported on $g\mathbb Z$. -/
def supportMultiples (hg : 0 < g) : Subfield (LaurentSeries ℂ) := (dilateHom hg).fieldRange

theorem dilateHom_coeff (hg : 0 < g) (f : LaurentSeries ℂ) (n : ℤ) :
    (dilateHom hg f).coeff ((g : ℤ) * n) = f.coeff n := by
  have := HahnSeries.embDomain_coeff (f := ⟨⟨mulLeftHom g, mulLeftHom_injective hg⟩, mulLeftHom_le_iff hg _ _⟩)
    (x := f) (a := n)
  exact this

theorem dilateHom_coeff_of_not_dvd (hg : 0 < g) (f : LaurentSeries ℂ) {n : ℤ} (hn : ¬ (g : ℤ) ∣ n) :
    (dilateHom hg f).coeff n = 0 := by
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨m, rfl⟩
  exact hn ⟨m, rfl⟩

theorem coeff_eq_zero_of_mem_supportMultiples (hg : 0 < g) {f : LaurentSeries ℂ} (hf : f ∈ supportMultiples hg)
    {n : ℤ} (hn : ¬ (g : ℤ) ∣ n) : f.coeff n = 0 := by
  obtain ⟨f', rfl⟩ := hf
  exact dilateHom_coeff_of_not_dvd hg f' hn

/-- **A Laurent series supported on $g\mathbb Z$ lies in the subfield.** -/
theorem mem_supportMultiples_of_coeff (hg : 0 < g) {f : LaurentSeries ℂ}
    (hf : ∀ n : ℤ, ¬ (g : ℤ) ∣ n → f.coeff n = 0) : f ∈ supportMultiples hg := by
  classical
  have hbdd : BddBelow (Function.support fun m : ℤ => f.coeff ((g : ℤ) * m)) := by
    refine ⟨-|f.order|, fun m hm => ?_⟩
    have hne : f ≠ 0 := by rintro rfl; exact hm rfl
    have hord := HahnSeries.order_le_of_coeff_ne_zero hm
    by_contra hlt
    rw [not_le] at hlt
    have hg1 : (1 : ℤ) ≤ g := by exact_mod_cast hg
    have : (g : ℤ) * m ≤ m := by nlinarith [abs_nonneg f.order]
    have := neg_abs_le f.order
    omega
  let f' : LaurentSeries ℂ := HahnSeries.ofSuppBddBelow (fun m : ℤ => f.coeff ((g : ℤ) * m)) hbdd
  refine ⟨f', ?_⟩
  ext n
  by_cases hn : (g : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    exact dilateHom_coeff hg f' m
  · rw [dilateHom_coeff_of_not_dvd hg f' hn, hf n hn]

theorem mem_supportMultiples_iff (hg : 0 < g) {f : LaurentSeries ℂ} :
    f ∈ supportMultiples hg ↔ ∀ n : ℤ, ¬ (g : ℤ) ∣ n → f.coeff n = 0 :=
  ⟨fun hf _ hn => coeff_eq_zero_of_mem_supportMultiples hg hf hn, mem_supportMultiples_of_coeff hg⟩

theorem supportMultiples_le {g' : ℕ} (hg : 0 < g) (hg' : 0 < g') (h : g ∣ g') :
    supportMultiples hg' ≤ supportMultiples hg := by
  intro f hf
  rw [mem_supportMultiples_iff] at hf ⊢
  intro n hn
  exact hf n fun h' => hn ((Int.natCast_dvd_natCast.2 h).trans h')

/-- **Valuations in the subfield**: a nonzero Laurent series supported on $g\mathbb Z$ has valuation $\exp(gk)$. -/
theorem exists_valuation_eq_of_mem_supportMultiples (hg : 0 < g) {f : LaurentSeries ℂ}
    (hf : f ∈ supportMultiples hg) (hf0 : f ≠ 0) : ∃ k : ℤ, Valued.v f = WithZero.exp ((g : ℤ) * k) := by
  have hv0 : Valued.v f ≠ 0 := (Valuation.ne_zero_iff _).2 hf0
  set m := WithZero.log (Valued.v f)
  have hm : Valued.v f = WithZero.exp m := (WithZero.exp_log hv0).symm
  -- the coefficient in degree $-m$ is the first nonzero one
  have hcoeff : f.coeff (-m) ≠ 0 := by
    intro h0
    have hle : Valued.v f ≤ WithZero.exp (-(1 - m)) := by
      rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
      intro n hn
      rcases lt_or_eq_of_le (show n ≤ -m by omega) with hlt | heq
      · have hle' : Valued.v f ≤ WithZero.exp (-(-m)) := by rw [neg_neg]; exact le_of_eq hm
        rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero] at hle'
        exact hle' n (by omega)
      · rw [heq]; exact h0
    rw [hm, WithZero.exp_le_exp] at hle
    omega
  have hdvd : (g : ℤ) ∣ -m := by
    by_contra hnd
    exact hcoeff (coeff_eq_zero_of_mem_supportMultiples hg hf hnd)
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨-k, by rw [hm]; congr 1; linarith⟩

end NumberFieldKB.ModularCurves
