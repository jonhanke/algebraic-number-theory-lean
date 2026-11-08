import NumberFieldKB.WeilBNT.FunctionField.HeckeFF
import NumberFieldKB.WeilBNT.FunctionField.ZetaFinal
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# L-series of unramified Hecke characters of a function field (Weil VII.§7, Thm. 6, conductor $0$)

Let $\omega$ be a Hecke character of the function field $k$ that is unramified at every place (conductor
$\mathfrak f=0$). Then $\omega$ factors through the divisor map: `FFHeckeCharacter.divChar` is the character of the
divisor group with $\omega(z)=\chi(\operatorname{div}z)$ (`divChar_div`), trivial on principal divisors
(`divChar_principal`). Its L-series in $u=q^{-s}$ is
$$L(u,\omega)=\sum_{\mathfrak a\succ0}\omega(\mathfrak a)\,u^{\deg\mathfrak a}$$
(`FFHeckeCharacter.lSeries`; formally this is Weil's Euler product $\prod_v(1-\omega(\pi_v)u^{\deg v})^{-1}$, which is
not formalized here).

* **`FFHeckeCharacter.weil_VII_7_thm6_unramified`**: if $\mathbb F_q$ is the field of constants and $\omega$ is
  unramified everywhere and not principal (not of the form $z\mapsto\lvert z\rvert_{\mathbb A}^s$), then $L(u,\omega)$
  is a polynomial of degree at most $2g-2$ (Weil VII.§7, Thm. 6 for $\mathfrak f=0$: the degree bound
  $2g-2+\deg\mathfrak f$; the exact degree and the functional equation need Weil's local constants, Prop. 14, and are
  not formalized).

Proof of the bound: for $n>2g-2$ every divisor class of degree $n$ contains the same number $E$ of effective divisors
($(q-1)E+1=q^{n-g+1}$, Riemann–Roch); a double count over pairs $(\mathfrak a,\mathfrak a')$ of effective divisors of
degree $n$ with $\mathfrak a'\sim\mathfrak a+\mathfrak d_0$ gives $E\,S_n=E\,\chi(\mathfrak d_0)\,S_n$ for the coefficient
$S_n$, where $\mathfrak d_0$ is a divisor of degree $0$ with $\chi(\mathfrak d_0)\ne1$ (it exists because $\omega$ is not
principal).
-/

open scoped WithZero NNReal
open Valuation Filter

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace FFHeckeCharacter

/-- $\omega$ is **principal** (Weil VII.§7) if it is of the form $z\mapsto\lvert z\rvert_{\mathbb A}^{s}$, $s\in\mathbb C$. -/
def IsPrincipal (ω : FFHeckeCharacter Fq k) : Prop :=
  ∃ s : ℂ, ∀ z : FFIdeleGroup Fq k, (ω (QuotientGroup.mk z) : ℂ) = ((FFIdeleGroup.norm z : ℝ) : ℂ) ^ s

/-- The value of $\omega$ on any idele with divisor $\mathfrak a$ (chosen; well defined when $\omega$ is unramified
everywhere, `divChar_div`). -/
def divCharFun (ω : FFHeckeCharacter Fq k) (a : Divisor Fq k) : ℂˣ :=
  ω (QuotientGroup.mk (FFIdeleGroup.div_surjective a).choose)

theorem eq_of_div_eq (ω : FFHeckeCharacter Fq k) (hω : ∀ v, ω.IsUnramifiedAt v) {z w : FFIdeleGroup Fq k}
    (h : FFIdeleGroup.div z = FFIdeleGroup.div w) : ω (QuotientGroup.mk z) = ω (QuotientGroup.mk w) := by
  have hinv : FFIdeleGroup.div w⁻¹ + FFIdeleGroup.div w = 0 := by
    rw [← FFIdeleGroup.div_mul, inv_mul_cancel, FFIdeleGroup.div_one]
  have hdiv : FFIdeleGroup.div (z * w⁻¹) = 0 := by
    rw [FFIdeleGroup.div_mul, h, add_comm]; exact hinv
  have h1 : ω (QuotientGroup.mk (z * w⁻¹)) = 1 := by
    apply ω.eq_one_of_forall_unit hω
    intro v
    have h0 : v.ordC (FFIdeleGroup.comp (z * w⁻¹) v) = 0 := by
      have := congrArg (fun x : Divisor Fq k => x v) hdiv
      simpa using this
    rw [v.valued_eq_exp_neg_ordC (FFIdeleGroup.comp_ne_zero _ v), h0]
    simp
  rw [QuotientGroup.mk_mul, map_mul, QuotientGroup.mk_inv, _root_.map_inv] at h1
  exact mul_inv_eq_one.mp h1

/-- For $\omega$ unramified everywhere, $\omega(z)$ depends only on $\operatorname{div}z$. -/
theorem divCharFun_div (ω : FFHeckeCharacter Fq k) (hω : ∀ v, ω.IsUnramifiedAt v) (z : FFIdeleGroup Fq k) :
    ω.divCharFun (FFIdeleGroup.div z) = ω (QuotientGroup.mk z) := by
  unfold divCharFun
  exact ω.eq_of_div_eq hω (FFIdeleGroup.div_surjective _).choose_spec

/-- **The divisor character** of an everywhere unramified Hecke character: $\chi(\mathfrak a)=\omega(z)$ for any idele
$z$ with $\operatorname{div}z=\mathfrak a$. -/
def divChar (ω : FFHeckeCharacter Fq k) (hω : ∀ v, ω.IsUnramifiedAt v) : Multiplicative (Divisor Fq k) →* ℂˣ where
  toFun a := ω.divCharFun (Multiplicative.toAdd a)
  map_one' := by
    show ω.divCharFun 0 = 1
    have h := ω.divCharFun_div hω 1
    rw [FFIdeleGroup.div_one, QuotientGroup.mk_one, map_one] at h
    exact h
  map_mul' a b := by
    obtain ⟨za, hza⟩ := FFIdeleGroup.div_surjective (Multiplicative.toAdd a)
    obtain ⟨zb, hzb⟩ := FFIdeleGroup.div_surjective (Multiplicative.toAdd b)
    show ω.divCharFun (Multiplicative.toAdd a + Multiplicative.toAdd b) =
      ω.divCharFun (Multiplicative.toAdd a) * ω.divCharFun (Multiplicative.toAdd b)
    rw [← hza, ← hzb, ← FFIdeleGroup.div_mul, ω.divCharFun_div hω, ω.divCharFun_div hω,
      ω.divCharFun_div hω, QuotientGroup.mk_mul, map_mul]

theorem divChar_div (ω : FFHeckeCharacter Fq k) (hω : ∀ v, ω.IsUnramifiedAt v) (z : FFIdeleGroup Fq k) :
    ω.divChar hω (Multiplicative.ofAdd (FFIdeleGroup.div z)) = ω (QuotientGroup.mk z) :=
  ω.divCharFun_div hω z

/-- $\chi$ is trivial on principal divisors. -/
theorem divChar_principal (ω : FFHeckeCharacter Fq k) (hω : ∀ v, ω.IsUnramifiedAt v) (f : kˣ) :
    ω.divChar hω (Multiplicative.ofAdd (Divisor.div f)) = 1 := by
  have h := ω.divChar_div hω (FFIdeleGroup.principal (Fq := Fq) f)
  rw [FFIdeleGroup.div_principal] at h
  rw [h]
  have : (QuotientGroup.mk (FFIdeleGroup.principal (Fq := Fq) f) : FFIdeleClassGroup Fq k) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨f, rfl⟩
  rw [this, map_one]

/-- **The L-series** $L(u,\omega)=\sum_{\mathfrak a\succ0}\chi(\mathfrak a)u^{\deg\mathfrak a}$ of an everywhere unramified
Hecke character, as a formal power series in $u=q^{-s}$. -/
def lSeries (ω : FFHeckeCharacter Fq k) (hω : ∀ v, ω.IsUnramifiedAt v) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    ∑ a ∈ (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset,
      ((ω.divChar hω (Multiplicative.ofAdd a) : ℂˣ) : ℂ)

/-- A non-principal everywhere unramified character is nontrivial on some divisor of degree $0$. -/
theorem exists_deg_zero_divChar_ne_one (ω : FFHeckeCharacter Fq k) (hω : ∀ v, ω.IsUnramifiedAt v)
    (hnp : ¬ ω.IsPrincipal) :
    ∃ d : Divisor Fq k, Divisor.deg d = 0 ∧ ω.divChar hω (Multiplicative.ofAdd d) ≠ 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hex : ∃ d : ℕ, 0 < d ∧ ∃ a : Divisor Fq k, Divisor.deg a = d := by
    obtain ⟨v⟩ := Place.nonempty (Fq := Fq) (k := k)
    refine ⟨v.degree, v.degree_pos, Finsupp.single v 1, ?_⟩
    rw [Divisor.deg_single, one_mul]
  obtain ⟨hd0, a₁, ha₁⟩ := Nat.find_spec hex
  set d := Nat.find hex with hd
  have hdpos : (0 : ℤ) < d := by exact_mod_cast hd0
  have hmult : ∀ a : Divisor Fq k, ∃ m : ℤ, Divisor.deg a = d * m := by
    intro a
    obtain ⟨m, hm⟩ : ∃ m, m = Divisor.deg a / (d : ℤ) := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, r = Divisor.deg a % (d : ℤ) := ⟨_, rfl⟩
    have hr0 : 0 ≤ r := hr ▸ Int.emod_nonneg _ hdpos.ne'
    have hr1 : r < d := hr ▸ Int.emod_lt_of_pos _ hdpos
    have hdec := Int.mul_ediv_add_emod (Divisor.deg a) d
    rw [← hm, ← hr] at hdec
    refine ⟨m, ?_⟩
    by_contra hne
    have hrpos : 0 < r := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · exfalso; apply hne; omega
    have hlt : r.toNat < d := by omega
    apply Nat.find_min hex hlt
    refine ⟨by omega, a - m • a₁, ?_⟩
    rw [_root_.map_sub, map_zsmul, ha₁, smul_eq_mul]
    have : m * (d : ℤ) = d * m := mul_comm _ _
    omega
  have hχdeg : ∀ (a : Divisor Fq k) (m : ℤ), Divisor.deg a = d * m →
      ω.divChar hω (Multiplicative.ofAdd a) = ω.divChar hω (Multiplicative.ofAdd a₁) ^ m := by
    intro a m h
    have := hcon (a - m • a₁) (by rw [_root_.map_sub, map_zsmul, ha₁, h, smul_eq_mul]; ring)
    rw [ofAdd_sub, _root_.map_div, ofAdd_zsmul, map_zpow, div_eq_one] at this
    exact this
  set c : ℂ := ((ω.divChar hω (Multiplicative.ofAdd a₁) : ℂˣ) : ℂ) with hcdef
  have hc0 : c ≠ 0 := Units.ne_zero _
  have hq1 : (1 : ℝ) < Nat.card Fq := by exact_mod_cast Finite.one_lt_card
  have hlogq : 0 < Real.log (Nat.card Fq : ℝ) := Real.log_pos hq1
  apply hnp
  refine ⟨-Complex.log c / (d * (Real.log (Nat.card Fq : ℝ) : ℂ)), fun z => ?_⟩
  obtain ⟨m, hm⟩ := hmult (FFIdeleGroup.div z)
  rw [← ω.divChar_div hω z, hχdeg _ m hm, Units.val_zpow_eq_zpow_val]
  have hn : ((FFIdeleGroup.norm z : ℝ≥0) : ℝ) = (Nat.card Fq : ℝ) ^ (-((d : ℤ) * m)) := by
    rw [FFIdeleGroup.norm_eq, hm]
    push_cast
    rfl
  rw [hn]
  have hx : (((Nat.card Fq : ℝ) ^ (-((d : ℤ) * m)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ (by positivity))
  rw [Complex.cpow_def_of_ne_zero hx, ← Complex.ofReal_log (by positivity), Real.log_zpow]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hl' : (Real.log (Nat.card Fq : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogq.ne'
  have e : (((-((d : ℤ) * m) : ℤ) : ℝ) * Real.log (Nat.card Fq : ℝ) : ℝ) *
      (-Complex.log c / (d * (Real.log (Nat.card Fq : ℝ) : ℂ))) = (m : ℂ) * Complex.log c := by
    push_cast
    have hl2 : Complex.log (Nat.card Fq : ℂ) ≠ 0 := by exact_mod_cast hl'
    field_simp
  rw [e, Complex.exp_int_mul, Complex.exp_log hc0]

theorem deg_eq_zero_of_mem_principalDivisors' {x : Divisor Fq k} (hx : x ∈ principalDivisors Fq k) :
    Divisor.deg x = 0 := by
  obtain ⟨u, rfl⟩ := (mem_principalDivisors_iff x).mp hx
  exact Divisor.deg_div_eq_zero u

open Classical in
theorem card_filter_eq_effClassCount (n : ℤ) (c : Divisor Fq k) (hc : Divisor.deg c = n) :
    ((Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) n).toFinset.filter
      (fun a' => a' - c ∈ principalDivisors Fq k)).card = effClassCount c := by
  rw [← Nat.card_eq_finsetCard]
  unfold effClassCount
  refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h0, _⟩, h⟩
    exact ⟨h0, h⟩
  · rintro ⟨h0, h⟩
    refine ⟨⟨h0, ?_⟩, h⟩
    have := deg_eq_zero_of_mem_principalDivisors' h
    rw [_root_.map_sub] at this
    omega

/-- The coefficients of $L(u,\omega)$ vanish in degrees $n>2g-2$. -/
theorem coeff_lSeries_eq_zero (hc : IsConstantField Fq k) (ω : FFHeckeCharacter Fq k)
    (hω : ∀ v, ω.IsUnramifiedAt v) (hnp : ¬ ω.IsPrincipal) (n : ℕ)
    (hn : 2 * Rep.genusInt Fq k - 2 < n) : PowerSeries.coeff n (ω.lSeries hω) = 0 := by
  classical
  obtain ⟨d₀, hd₀, hχ⟩ := exists_deg_zero_divChar_ne_one ω hω hnp
  have hq : 2 ≤ Nat.card Fq := Finite.one_lt_card
  have hg0 := genusInt_nonneg hc
  have hell : ∀ b : Divisor Fq k, Divisor.deg b = n →
      (b.ell : ℤ) = n - Rep.genusInt Fq k + 1 := fun b hb => by
    rw [weil_VI_2_cor2 hc (by rw [hb]; exact hn), hb]
  have hEall : ∀ b b' : Divisor Fq k, Divisor.deg b = n → Divisor.deg b' = n →
      effClassCount b = effClassCount b' := by
    intro b b' hb hb'
    have h1 := effClassCount_spec_of_fd hc b (Divisor.finiteDimensional_riemannRochSpace b)
    have h2 := effClassCount_spec_of_fd hc b' (Divisor.finiteDimensional_riemannRochSpace b')
    have : b.ell = b'.ell := by
      have := hell b hb
      have := hell b' hb'
      omega
    rw [this] at h1
    have h3 : (Nat.card Fq - 1) * effClassCount b = (Nat.card Fq - 1) * effClassCount b' :=
      Nat.add_right_cancel (h1.trans h2.symm)
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  have hEpos : ∀ b : Divisor Fq k, Divisor.deg b = n → effClassCount b ≠ 0 := by
    intro b hb h0
    have h1 := effClassCount_spec_of_fd hc b (Divisor.finiteDimensional_riemannRochSpace b)
    rw [h0, mul_zero, zero_add] at h1
    have hne : b.ell ≠ 0 := by
      have := hell b hb
      omega
    have h2 := Nat.one_lt_pow hne (by omega : 1 < Nat.card Fq)
    rw [← h1] at h2
    exact lt_irrefl _ h2
  set f : Divisor Fq k → ℂ := fun a => ((ω.divChar hω (Multiplicative.ofAdd a) : ℂˣ) : ℂ) with hf
  have hP : ∀ a a' : Divisor Fq k, a' - (a + d₀) ∈ principalDivisors Fq k → f a' = f a * f d₀ := by
    intro a a' h
    obtain ⟨u, hu⟩ := (mem_principalDivisors_iff _).mp h
    have ha' : a' = a + d₀ + Divisor.div u := by rw [hu]; abel
    simp only [hf]
    rw [ha', ofAdd_add, ofAdd_add, map_mul, map_mul, ω.divChar_principal hω u, mul_one,
      Units.val_mul]
  rw [lSeries, PowerSeries.coeff_mk]
  change ∑ a ∈ (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset, f a = 0
  set A := (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset with hA
  have hmemA : ∀ a, a ∈ A ↔ 0 ≤ a ∧ Divisor.deg a = n := fun a => by simp [hA]
  rcases A.eq_empty_or_nonempty with hAe | ⟨a₀, ha₀⟩
  · rw [hAe, Finset.sum_empty]
  have ha₀n := ((hmemA a₀).mp ha₀).2
  set E := effClassCount a₀ with hE
  have hEc : ∀ c : Divisor Fq k, Divisor.deg c = n → effClassCount c = E := fun c hcn =>
    hEall c a₀ hcn ha₀n
  have key1 : ∑ a ∈ A, ∑ a' ∈ A, (if a' - (a + d₀) ∈ principalDivisors Fq k then f a' else 0) =
      (E : ℂ) * f d₀ * ∑ a ∈ A, f a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hdeg : Divisor.deg (a + d₀) = n := by rw [map_add, hd₀, add_zero]; exact ((hmemA a).mp ha).2
    rw [← Finset.sum_filter,
      Finset.sum_congr rfl (fun a' ha' => hP a a' (Finset.mem_filter.mp ha').2), Finset.sum_const,
      nsmul_eq_mul, hA, card_filter_eq_effClassCount n (a + d₀) hdeg, hEc _ hdeg]
    ring
  have key2 : ∑ a ∈ A, ∑ a' ∈ A, (if a' - (a + d₀) ∈ principalDivisors Fq k then f a' else 0) =
      (E : ℂ) * ∑ a ∈ A, f a := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    have hdeg : Divisor.deg (a' - d₀) = n := by
      rw [_root_.map_sub, hd₀, sub_zero]; exact ((hmemA a').mp ha').2
    have hiff : ∀ a : Divisor Fq k, (a' - (a + d₀) ∈ principalDivisors Fq k ↔
        a - (a' - d₀) ∈ principalDivisors Fq k) := fun a => by
      rw [show a - (a' - d₀) = -(a' - (a + d₀)) by abel, neg_mem_iff]
    rw [Finset.sum_congr rfl (fun a _ => if_congr (hiff a) rfl rfl), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, hA, card_filter_eq_effClassCount n (a' - d₀) hdeg,
      hEc _ hdeg]
  have hEne : (E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hEpos a₀ ha₀n)
  have hfd : f d₀ ≠ 1 := fun h => hχ (Units.val_eq_one.mp h)
  have hz : (E : ℂ) * (∑ a ∈ A, f a) * (1 - f d₀) = 0 := by
    linear_combination key2.symm.trans key1
  rcases mul_eq_zero.mp hz with h | h
  · exact (mul_eq_zero.mp h).resolve_left hEne
  · exact absurd (sub_eq_zero.mp h).symm hfd

/-- **Weil VII.§7, Thm. 6** for conductor $\mathfrak f=0$ (degree bound): if $\mathbb F_q$ is the field of constants
and $\omega$ is an everywhere unramified, non-principal Hecke character, then $L(u,\omega)$ is a polynomial of degree at
most $2g-2+\deg\mathfrak f=2g-2$. -/
@[kb "weil1973bnt" "Ch. VII, §7, Thm. 6 (p. 134), conductor 0: L(u, omega) is a polynomial of degree at most 2g - 2"]
theorem weil_VII_7_thm6_unramified (hc : IsConstantField Fq k) (ω : FFHeckeCharacter Fq k)
    (hω : ∀ v, ω.IsUnramifiedAt v) (hnp : ¬ ω.IsPrincipal) :
    ∃ P : Polynomial ℂ, (P.natDegree : ℤ) ≤ 2 * (genus Fq k : ℤ) - 2 ∧ (P : PowerSeries ℂ) = ω.lSeries hω := by
  classical
  have hg0 := genusInt_nonneg hc
  have hge := genus_eq hc
  by_cases hg : 1 ≤ Rep.genusInt Fq k
  · refine ⟨PowerSeries.trunc ((2 * Rep.genusInt Fq k - 2).toNat + 1) (ω.lSeries hω), ?_, ?_⟩
    · have : (PowerSeries.trunc ((2 * Rep.genusInt Fq k - 2).toNat + 1) (ω.lSeries hω)).natDegree ≤
          (2 * Rep.genusInt Fq k - 2).toNat := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        rw [PowerSeries.coeff_trunc, if_neg (by omega)]
      omega
    · ext m
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with h
      · rfl
      · exact (coeff_lSeries_eq_zero hc ω hω hnp m (by omega)).symm
  · exfalso
    have h0 := coeff_lSeries_eq_zero hc ω hω hnp 0 (by omega)
    have hset : (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) ((0 : ℕ) : ℤ)).toFinset =
        {0} := by
      ext a
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        exact Divisor.eq_zero_of_deg_eq_zero h1 (by simpa using h2)
      · rintro rfl
        simp
    rw [lSeries, PowerSeries.coeff_mk, hset] at h0
    simp at h0

end FFHeckeCharacter

end NumberFieldKB.WeilBNT.FF
