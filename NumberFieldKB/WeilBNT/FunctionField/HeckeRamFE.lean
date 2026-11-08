import NumberFieldKB.WeilBNT.FunctionField.TateLocalFF
import NumberFieldKB.WeilBNT.FunctionField.HeckeRayFF

/-!
# Weil VII.§7 Thm. 6 for ramified quasicharacters of a function field

$k$ is a global function field with field of constants $\mathbb F_q$ and genus $g$, $\omega$ a quasicharacter of
$G_k$ of conductor $\mathfrak f\ne0$, $L(u,\omega)=\sum_{\mathfrak a\succ0,(\mathfrak a,\mathfrak f)=1}\chi_\omega(\mathfrak a)
u^{\deg\mathfrak a}$ (`lSeriesF`), $N=2g-2+\deg\mathfrak f$.

* `gInt_stdPhi`: $\int_U\Phi_\omega(\pi^Du)\omega(\pi^Du)\,d\mu(u)=\mu(U)\chi_\omega(D)$ for $D\succ0$ prime to $\mathfrak f$,
  and $0$ otherwise; so $a_n(\omega,\Phi_\omega)=\mu(U)\,[u^n]L(u,\omega)$ (`aCoef_stdPhi`).
* **`weil_VII_7_thm6_ramified_fe`**: $L(u,\omega)=\kappa\,\omega(b)\,(q^{1/2}u)^NL(1/qu,\omega^{-1})$ with $\kappa$ of
  absolute value $1$ (Prop. 14) and $b=\pi^{\mathfrak c+\mathfrak f}$.
* **`weil_VII_7_thm6_ramified_exact`**: $L(u,\omega)$ is a polynomial of degree exactly $N$.

*Proof* (Weil's). Apply the functional equation of VII.§5 Thm. 2 (`zetaRat_fe`) to $\Phi_\omega$; by Prop. 14 the
Fourier transform is $\kappa\lvert b\rvert^{1/2}\Phi_{\omega^{-1}}(b\,\cdot)$, and both zeta integrals are $\mu(U)$ times the
$L$-polynomials.
-/

open MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal

namespace NumberFieldKB.WeilBNT.FF

noncomputable section

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

set_option linter.unusedSectionVars false

open FFIdeleGroup FFAdeleRing

namespace FFHeckeCharacter

variable (ω : FFHeckeCharacter Fq k)

/-- The unit of $k_v$ given by the $v$-component of an idele. -/
def compUnit (z : FFIdeleGroup Fq k) (v : Place Fq k) : v.Completionˣ := Units.mk0 (comp z v) (comp_ne_zero z v)

open Classical in
/-- $\prod_{v\in S}\mathrm{single}_v(u_v)$. -/
def unitsAt (S : Finset (Place Fq k)) (u : FFIdeleGroup Fq k) : FFIdeleGroup Fq k :=
  ∏ v ∈ S, FFIdeleGroup.single v (compUnit u v)

open Classical in
theorem comp_unitsAt (S : Finset (Place Fq k)) (u : FFIdeleGroup Fq k) (w : Place Fq k) :
    comp (unitsAt S u) w = if w ∈ S then comp u w else 1 := by
  have h : comp (unitsAt S u) w = ∏ v ∈ S, comp (FFIdeleGroup.single v (compUnit u v)) w := by
    show compHom w (unitsAt S u) = _
    rw [unitsAt, map_prod]; rfl
  rw [h]
  split_ifs with hw
  · rw [Finset.prod_eq_single w]
    · rw [comp_single_self]; rfl
    · intro v _ hvw; exact comp_single_ne (Ne.symm hvw) _
    · intro h'; exact absurd hw h'
  · exact Finset.prod_eq_one fun v hv => comp_single_ne (fun h => hw (by rw [h]; exact hv)) _

theorem ev_unitsAt (S : Finset (Place Fq k)) (u : FFIdeleGroup Fq k) :
    ω.ev (unitsAt S u) = ∏ v ∈ S, ((ω.component v (compUnit u v) : ℂˣ) : ℂ) := by
  classical
  rw [unitsAt]
  induction S using Finset.induction_on with
  | empty => simp [ev_one]
  | insert v S hv ih => rw [Finset.prod_insert hv, ev_mul, ih, Finset.prod_insert hv]; rfl

/-- **$\omega$ on $U$ only sees the ramified components**: $\omega(u)=\prod_{v\in S}\omega_v(u_v)$ for $u\in U$. -/
theorem ev_of_mem_integralUnits {u : FFIdeleGroup Fq k} (hu : u ∈ integralUnits) :
    ω.ev u = ∏ v ∈ ω.ramSet, ((ω.component v (compUnit u v) : ℂˣ) : ℂ) := by
  classical
  have hsplit : u = unitsAt ω.ramSet u * ((unitsAt ω.ramSet u)⁻¹ * u) := by rw [mul_inv_cancel_left]
  conv_lhs => rw [hsplit]
  rw [ev_mul, ev_unitsAt]
  have h1 : ω.ev ((unitsAt ω.ramSet u)⁻¹ * u) = 1 := by
    have := ω.eq_one_of_forall_mem_unitFiltration ((unitsAt ω.ramSet u)⁻¹ * u) fun v => ?_
    · show ((ω (QuotientGroup.mk _) : ℂˣ) : ℂ) = 1
      rw [this, Units.val_one]
    have hcomp : comp ((unitsAt ω.ramSet u)⁻¹ * u) v = if v ∈ ω.ramSet then 1 else comp u v := by
      rw [comp_mul]
      have hinv : comp (unitsAt ω.ramSet u)⁻¹ v * comp (unitsAt ω.ramSet u) v = 1 := by
        rw [← comp_mul, inv_mul_cancel, comp_one]
      by_cases hv : v ∈ ω.ramSet
      · rw [comp_unitsAt, if_pos hv] at hinv; rw [if_pos hv]
        rw [hinv]
      · rw [comp_unitsAt, if_neg hv, mul_one] at hinv; rw [if_neg hv, hinv, one_mul]
    have hu1 := (mem_integralUnits_iff u).1 hu v
    rw [hcomp]
    split_ifs with hv
    · simp
    · have h0 : ω.conductorExponent v = 0 := by
        have := (not_congr (ω.mem_ramSet)).1 hv; omega
      refine ⟨hu1, ?_⟩
      rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero, sub_eq_add_neg]
      exact Valuation.map_add_le _ hu1.le (by rw [Valuation.map_neg, map_one])
  rw [h1, mul_one]

end FFHeckeCharacter

namespace FFHeckeCharacter

variable (ω : FFHeckeCharacter Fq k)

theorem ev_piD_eq_rayChar {D : Divisor Fq k} (hD : ∀ v ∈ ω.ramSet, D v = 0) :
    ω.ev (piD D) = ((ω.rayChar (Multiplicative.ofAdd D) : ℂˣ) : ℂ) := by
  have h := ω.rayChar_eq (piD D) fun v hv => by
    rw [comp_piD, hD v ((ω.mem_ramSet).2 (by rw [conductor_apply] at hv; exact_mod_cast hv)), zpow_zero,
      Units.val_one, sub_self, map_zero]
    exact zero_le'
  rw [div_piD] at h
  simp only [ev, h]

open Classical in
/-- The integrand $\Phi_\omega(\pi^Du)\omega(\pi^Du)$ on $U$: $\chi_\omega(D)$ for $D\succ0$ prime to $\mathfrak f$, else $0$. -/
theorem stdPhi_mul_ev {u : FFIdeleGroup Fq k} (hu : u ∈ integralUnits) (D : Divisor Fq k) :
    ω.stdPhi ((piD D * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) * ω.ev (piD D * u) =
      if 0 ≤ D ∧ ∀ v ∈ ω.ramSet, D v = 0 then ((ω.rayChar (Multiplicative.ofAdd D) : ℂˣ) : ℂ) else 0 := by
  unfold stdPhi prodFn
  by_cases h0 : 0 ≤ D
  · have hU : ((piD D * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) ∈ U 0 :=
      (piD_mul_mem_U_iff 0 D hu).2 (by simpa using h0)
    rw [if_pos hU, one_mul]
    by_cases hS : ∀ v ∈ ω.ramSet, D v = 0
    · rw [if_pos ⟨h0, hS⟩]
      have hcomp : ∀ v ∈ ω.ramSet, ((piD D * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) v = comp u v :=
        fun v hv => by
          show comp (piD D * u) v = _
          rw [comp_piD_mul, hS v hv, zpow_zero, Units.val_one, one_mul]
      have hphi : ∀ v ∈ ω.ramSet, ω.phiLoc v (((piD D * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) v) =
          (((ω.component v (compUnit u v))⁻¹ : ℂˣ) : ℂ) := fun v hv => by
        rw [hcomp v hv]
        exact ω.phiLoc_unit v (compUnit u v) ((mem_integralUnits_iff u).1 hu v)
      rw [Finset.prod_congr rfl hphi, ev_mul, ω.ev_piD_eq_rayChar hS, ω.ev_of_mem_integralUnits hu,
        mul_left_comm, ← Finset.prod_mul_distrib]
      rw [Finset.prod_eq_one fun v _ => by rw [← Units.val_mul, inv_mul_cancel, Units.val_one], mul_one]
    · rw [if_neg (fun h => hS h.2)]
      push Not at hS
      obtain ⟨v, hv, hDv⟩ := hS
      rw [Finset.prod_eq_zero hv, zero_mul]
      refine ω.phiLoc_of_ne v ?_
      show Valued.v (comp (piD D * u) v) ≠ 1
      rw [valued_comp_piD_mul D hu, ← WithZero.exp_zero, Ne, WithZero.exp_inj]
      omega
  · have hU : ((piD D * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) ∉ U 0 :=
      fun h => h0 (by simpa using (piD_mul_mem_U_iff 0 D hu).1 h)
    rw [if_neg hU, if_neg (fun h => h0 h.1), zero_mul, zero_mul]

open Classical in
theorem gInt_stdPhi (μ : Measure (FFIdeleGroup Fq k)) (D : Divisor Fq k) :
    gInt μ ω ω.stdPhi D = if 0 ≤ D ∧ ∀ v ∈ ω.ramSet, D v = 0 then
      ((μ integralUnits).toReal : ℂ) * ((ω.rayChar (Multiplicative.ofAdd D) : ℂˣ) : ℂ) else 0 := by
  rw [gInt, setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u hu => ω.stdPhi_mul_ev hu D,
    setIntegral_const]
  split_ifs <;> simp [Measure.real, Complex.real_smul]

/-- $a_n(\omega,\Phi_\omega)=\mu(U)\,[u^n]L(u,\omega)$. -/
theorem aCoef_stdPhi (μ : Measure (FFIdeleGroup Fq k)) (n : ℕ) :
    aCoef μ ω ω.stdPhi n = ((μ integralUnits).toReal : ℂ) * PowerSeries.coeff n ω.lSeriesF := by
  classical
  set A := (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset.filter
    (fun a => ∀ v ∈ ω.ramSet, a v = 0) with hA
  have hmemA : ∀ a, a ∈ A ↔ (0 ≤ a ∧ Divisor.deg a = n) ∧ ∀ v, 0 < ω.conductor v → a v = 0 := fun a => by
    simp only [hA, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, mem_ramSet, conductor_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun v hv => h2 v (by exact_mod_cast hv)⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun v hv => h2 v (by exact_mod_cast hv)⟩
  rw [coeff_lSeriesF_eq_sum ω n A hmemA, Finset.mul_sum, aCoef]
  refine finsum_mem_eq_sum_of_subset _ ?_ ?_ |>.trans (Finset.sum_congr rfl fun D hD => ?_)
  · rintro D ⟨hD, hne⟩
    rw [Function.mem_support, gInt_stdPhi] at hne
    split_ifs at hne with h
    · exact Finset.mem_filter.2 ⟨by simp [h.1, show Divisor.deg D = n from hD], h.2⟩
    · exact absurd rfl hne
  · intro D hD
    exact ((hmemA D).1 (Finset.mem_coe.1 hD)).1.2
  · rw [gInt_stdPhi, if_pos ⟨((hmemA D).1 hD).1.1, (Finset.mem_filter.1 hD).2⟩]

theorem aCoef_stdPhi_neg (μ : Measure (FFIdeleGroup Fq k)) {n : ℤ} (hn : n < 0) :
    aCoef μ ω ω.stdPhi n = 0 := by
  rw [aCoef]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun D hD => ?_
  rw [gInt_stdPhi, if_neg]
  rintro ⟨h0, -⟩
  have := Divisor.deg_mono h0
  rw [map_zero, show Divisor.deg D = n from hD] at this
  omega

end FFHeckeCharacter

/-! ### Translating and twisting the coefficients -/

namespace FFIdeleGroup

theorem mem_cone_empty_iff {a D : Divisor Fq k} {n : ℤ} :
    D ∈ (finite_cone_deg (Fq := Fq) (k := k) ∅ (-a) n).toFinset ↔ -a ≤ D ∧ Divisor.deg D = n := by
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, cone, Finset.notMem_empty, IsEmpty.forall_iff,
    implies_true, true_and]
  exact Iff.rfl

/-- Translation by $\pi^E$: $a_m(\chi,\Psi(\cdot\,\pi^E))=\chi(\pi^E)^{-1}a_{m+\deg E}(\chi,\Psi)$. -/
theorem aCoef_mul_piD (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure] (χ : FFHeckeCharacter Fq k)
    {Ψ : FFAdeleRing Fq k → ℂ} (hs : ∀ x, x ∉ U 0 → Ψ x = 0) (E : Divisor Fq k) (m : ℤ) :
    aCoef μ χ (fun x => Ψ (x * (piD E : FFAdeleRing Fq k))) m =
      (χ.ev (piD E))⁻¹ * aCoef μ χ Ψ (m + Divisor.deg E) := by
  have hs' : ∀ x, x ∉ U E → Ψ (x * (piD E : FFAdeleRing Fq k)) = 0 := fun x hx => hs _ fun h => hx (by
    have := (FFAdeleRing.mul_mem_U_iff 0 (piD E) x).1 h; rwa [div_piD, zero_add] at this)
  rw [aCoef_eq_finset_sum μ χ hs', aCoef_eq_finset_sum μ χ hs, Finset.mul_sum]
  have hg : ∀ D, gInt μ χ (fun x => Ψ (x * (piD E : FFAdeleRing Fq k))) D =
      (χ.ev (piD E))⁻¹ * gInt μ χ Ψ (D + E) := fun D => by
    rw [gInt, gInt, ← integral_const_mul]
    refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u _ => ?_
    have h1 : piD D * u * piD E = piD (D + E) * u := by rw [piD_add]; exact mul_right_comm (piD D) u (piD E)
    have h2 : χ.ev (piD D * u) = χ.ev (piD (D + E) * u) * (χ.ev (piD E))⁻¹ := by
      rw [← h1, FFHeckeCharacter.ev_mul χ (piD D * u), mul_inv_cancel_right₀ (χ.ev_ne_zero _)]
    rw [← Units.val_mul, h1, h2]
    ring
  simp_rw [hg]
  refine Finset.sum_nbij' (fun D => D + E) (fun D => D - E) (fun D hD => ?_) (fun D hD => ?_)
    (fun D _ => add_sub_cancel_right D E) (fun D _ => sub_add_cancel D E) (fun D _ => rfl)
  · rw [mem_cone_empty_iff] at hD ⊢
    refine ⟨fun v => ?_, by rw [map_add, hD.2]⟩
    have := hD.1 v; simp at this ⊢; omega
  · rw [mem_cone_empty_iff] at hD ⊢
    refine ⟨fun v => ?_, by rw [map_sub, hD.2]; ring⟩
    have := hD.1 v; simp at this ⊢; omega

/-- Twisting by $\omega_1$: $a_m(\omega_1\chi^{-1},\Psi)=q^{-m}a_m(\chi^{-1},\Psi)$. -/
theorem aCoef_dual_eq (μ : Measure (FFIdeleGroup Fq k)) (χ : FFHeckeCharacter Fq k)
    {Ψ : FFAdeleRing Fq k → ℂ} (hs : ∀ x, x ∉ U 0 → Ψ x = 0) (m : ℤ) :
    aCoef μ χ.dual Ψ m = (Nat.card Fq : ℂ) ^ (-m) * aCoef μ χ⁻¹ Ψ m := by
  rw [aCoef_eq_finset_sum μ χ.dual hs, aCoef_eq_finset_sum μ χ⁻¹ hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hdeg := (mem_cone_empty_iff.1 hD).2
  rw [gInt, gInt, ← integral_const_mul]
  refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u hu => ?_
  rw [FFHeckeCharacter.ev_dual, omegaS_eq, div_piD_mul D hu, hdeg, uS, Complex.cpow_neg_one, inv_zpow']
  have : χ⁻¹.ev (piD D * u) = (χ.ev (piD D * u))⁻¹ := by
    show (((χ (QuotientGroup.mk _))⁻¹ : ℂˣ) : ℂ) = _
    rw [Units.val_inv_eq_inv_val]; rfl
  rw [this]; ring

end FFIdeleGroup

/-! ### Weil VII.§7 Thm. 6 for ramified quasicharacters -/

namespace FFHeckeCharacter

variable (ψ₀ : AddChar Fq Circle) (ω : FFHeckeCharacter Fq k)

theorem exists_unit_ne_one (hf : ω.conductor ≠ 0) :
    ∃ v : Place Fq k, ∃ u : v.Completionˣ, Valued.v (u : v.Completion) = 1 ∧ ω.component v u ≠ 1 := by
  obtain ⟨v, hv⟩ : ∃ v, ω.conductor v ≠ 0 := by
    by_contra h; push Not at h; exact hf (Finsupp.ext h)
  have : ¬ ω.IsUnramifiedAt v := fun h => hv (by
    rw [conductor_apply, (ω.conductorExponent_eq_zero_iff v).2 h]; rfl)
  unfold IsUnramifiedAt at this
  push Not at this
  exact ⟨v, this⟩

theorem not_isNormOneTrivial (hf : ω.conductor ≠ 0) : ¬ IsNormOneTrivial ω := by
  obtain ⟨v, u, hu, hne⟩ := ω.exists_unit_ne_one hf
  intro h
  have hmem : FFIdeleGroup.single v u ∈ normOne Fq k := by
    rw [mem_normOne_iff, div_single_unit hu, map_zero]
  have := h _ hmem
  exact hne (Units.ext (by simpa [ev] using this))

theorem not_isPrincipal (hf : ω.conductor ≠ 0) : ¬ ω.IsPrincipal := by
  obtain ⟨v, u, hu, hne⟩ := ω.exists_unit_ne_one hf
  rintro ⟨s, hs⟩
  have h1 := hs (FFIdeleGroup.single v u)
  have hn : FFIdeleGroup.norm (FFIdeleGroup.single v u) = 1 := by
    rw [norm_eq_one_iff, div_single_unit hu, map_zero]
  rw [hn, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow] at h1
  exact hne (Units.ext (by simpa using h1))

theorem coeff_zero_lSeriesF : PowerSeries.coeff 0 ω.lSeriesF = 1 := by
  classical
  have hset : ∀ a : Divisor Fq k, a ∈ ({0} : Finset (Divisor Fq k)) ↔
      (0 ≤ a ∧ Divisor.deg a = ((0 : ℕ) : ℤ)) ∧ ∀ v, 0 < ω.conductor v → a v = 0 := by
    intro a
    rw [Finset.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨⟨h1, h2⟩, _⟩; exact Divisor.eq_zero_of_deg_eq_zero h1 (by simpa using h2)
  rw [coeff_lSeriesF_eq_sum ω 0 {0} hset]
  simp

/-- The idele $b$ has $\lvert b\rvert=q^{-N}$, $N=\deg(\mathfrak c+\mathfrak f)$. -/
theorem norm_bIdele : (FFIdeleGroup.norm ω.bIdele : ℝ) =
    (Nat.card Fq : ℝ) ^ (-Divisor.deg (canonical Fq k + ω.conductor)) := by
  rw [bIdele, FFIdeleGroup.norm_piD, NNReal.coe_zpow, NNReal.coe_natCast]

open Classical in
/-- **The coefficient identity** behind Thm. 6: $a_n(\omega,\Phi_\omega)=K\,\check\omega(b)^{-1}q^{n-N}
a_{N-n}(\omega^{-1},\Phi_{\omega^{-1}})$ with $K=\kappa\lvert b\rvert^{1/2}$. -/
theorem aCoef_stdPhi_fe (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (hf : ω.conductor ≠ 0)
    (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure] (n : ℤ) :
    aCoef μ ω ω.stdPhi n = (∏ v ∈ ω.ramSet, ω.kappaV ψ₀ v) *
      ((((FFIdeleGroup.norm ω.bIdele : ℝ) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (ω.dual.ev ω.bIdele)⁻¹ *
      ((Nat.card Fq : ℂ) ^ (-(Divisor.deg (canonical Fq k + ω.conductor) - n)) *
        aCoef μ ω⁻¹ (ω⁻¹).stdPhi (Divisor.deg (canonical Fq k + ω.conductor) - n)) := by
  obtain ⟨b₁, hb⟩ := weil_VII_5_cor5_ff hc
  have hΦ : FFAdeleRing.IsSchwartzBruhat ω.stdPhi :=
    FFAdeleRing.prodFn_isSchwartzBruhat (ω.isPeriodicOn_phiLoc subset_rfl) (fun _ _ => rfl)
  obtain ⟨a', -, hs', -⟩ := FFAdeleRing.isSchwartzBruhat_fourierFF ψ₀ hψ₀ hΦ
  have hdual := aCoef_dual ψ₀ hc hψ₀ μ ω hΦ hs' hb n
  rw [if_neg (ω.not_isNormOneTrivial hf), add_zero] at hdual
  rw [← hdual]
  set K : ℂ := (∏ v ∈ ω.ramSet, ω.kappaV ψ₀ v) * ((((FFIdeleGroup.norm ω.bIdele : ℝ) ^ (1 / 2 : ℝ)) : ℝ) : ℂ)
  have hfun : (fun x => (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ ω.stdPhi x) =
      fun x => K * (ω⁻¹).stdPhi (x * (ω.bIdele : FFAdeleRing Fq k)) :=
    funext fun x => (ω.weil_VII_7_prop14_ff ψ₀ hc hψ₀).2 x
  have hsΨ : ∀ x, x ∉ U 0 → (ω⁻¹).stdPhi x = 0 := fun x hx => by
    simp [stdPhi, FFAdeleRing.prodFn, hx]
  have hsΨb : ∀ x, x ∉ U (canonical Fq k + ω.conductor) →
      (ω⁻¹).stdPhi (x * (ω.bIdele : FFAdeleRing Fq k)) = 0 := fun x hx => hsΨ _ fun h => hx (by
    have := (FFAdeleRing.mul_mem_U_iff 0 ω.bIdele x).1 h; rwa [bIdele, div_piD, zero_add] at this)
  rw [hfun, aCoef_const_mul μ ω.dual hsΨb, bIdele, aCoef_mul_piD μ ω.dual hsΨ, aCoef_dual_eq μ ω hsΨ, ← bIdele]
  ring_nf

end FFHeckeCharacter

namespace FFHeckeCharacter

variable (ψ₀ : AddChar Fq Circle) (ω : FFHeckeCharacter Fq k)

/-- The coefficient identity in terms of the $L$-coefficients ($\mu$ the Haar measure with $\mu(U)=1$). -/
theorem coeff_lSeriesF_fe_aux (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (hf : ω.conductor ≠ 0) (n : ℕ) :
    PowerSeries.coeff n ω.lSeriesF = (∏ v ∈ ω.ramSet, ω.kappaV ψ₀ v) *
      ((((FFIdeleGroup.norm ω.bIdele : ℝ) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (ω.dual.ev ω.bIdele)⁻¹ *
      ((Nat.card Fq : ℂ) ^ (-(Divisor.deg (canonical Fq k + ω.conductor) - n)) *
        aCoef (haarU Fq k) ω⁻¹ (ω⁻¹).stdPhi (Divisor.deg (canonical Fq k + ω.conductor) - n)) := by
  have h := ω.aCoef_stdPhi_fe ψ₀ hc hψ₀ hf (haarU Fq k) n
  rw [aCoef_stdPhi, haarU_integralUnits, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at h
  exact h

theorem const_eq (hc : IsConstantField Fq k) (n : ℤ) :
    (∏ v ∈ ω.ramSet, ω.kappaV ψ₀ v) * ((((FFIdeleGroup.norm ω.bIdele : ℝ) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) *
      (ω.dual.ev ω.bIdele)⁻¹ * (Nat.card Fq : ℂ) ^ (-(Divisor.deg (canonical Fq k + ω.conductor) - n)) =
      (∏ v ∈ ω.ramSet, ω.kappaV ψ₀ v) * ω.ev ω.bIdele *
        ((((Nat.card Fq : ℝ) ^ ((n : ℝ) - (Divisor.deg (canonical Fq k + ω.conductor) : ℝ) / 2)) : ℝ) : ℂ) := by
  have hq0 : (0 : ℝ) < Nat.card Fq := by exact_mod_cast (Nat.card_pos (α := Fq))
  have hqC : (Nat.card Fq : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  set N := Divisor.deg (canonical Fq k + ω.conductor)
  rw [ev_dual, omegaS_eq, bIdele, div_piD, ← bIdele, uS, Complex.cpow_neg_one, mul_inv, inv_inv, inv_zpow',
    norm_bIdele, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
  have hω0 : ω.ev ω.bIdele ≠ 0 := ω.ev_ne_zero _
  have e1 : ((((Nat.card Fq : ℝ) ^ ((n : ℝ) - (N : ℝ) / 2)) : ℝ) : ℂ) =
      ((((Nat.card Fq : ℝ) ^ (((-N : ℤ) : ℝ) * (1 / 2))) : ℝ) : ℂ) * (Nat.card Fq : ℂ) ^ N *
        (Nat.card Fq : ℂ) ^ (-(N - n)) := by
    rw [← cast_rpow_intCast, ← cast_rpow_intCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Real.rpow_add hq0, ← Real.rpow_add hq0]
    congr 2; push_cast; ring
  rw [e1, zpow_neg (Nat.card Fq : ℂ) N, inv_inv]
  ring

/-- **Weil, VII.§7 Thm. 6, functional equation for ramified $\omega$, function fields.** For a quasicharacter
$\omega$ with conductor $\mathfrak f\ne0$ ($\mathbb F_q$ the field of constants), $N=\deg(\mathfrak c+\mathfrak f)
=2g-2+\deg\mathfrak f$, $b=\pi^{\mathfrak c+\mathfrak f}$ and $\kappa=\prod_v\kappa_v$ Weil's constant of
Prop. 14 ($\lvert\kappa\rvert=1$), coefficientwise
$$L(u,\omega)=\kappa\,\omega(b)\,(q^{1/2}u)^NL(1/qu,\omega^{-1}),$$
i.e. $[u^n]L(u,\omega)=\kappa\,\omega(b)\,q^{n-N/2}\,[u^{N-n}]L(u,\omega^{-1})$ for $0\le n\le N$. -/
@[kb "weil1973bnt" "Ch. VII, §7, Thm. 6 (p. 134), ramified ω: functional equation P(u, ω) = κ_ω(b) (q^(1/2) u)^N P(1/qu, ω^-1), N = 2g - 2 + deg f"]
theorem weil_VII_7_thm6_ramified_fe (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (hf : ω.conductor ≠ 0) :
    ‖∏ v ∈ ω.ramSet, ω.kappaV ψ₀ v‖ = 1 ∧
      Divisor.deg (canonical Fq k + ω.conductor) = 2 * (genus Fq k : ℤ) - 2 + Divisor.deg ω.conductor ∧
      ∀ n : ℕ, (n : ℤ) ≤ Divisor.deg (canonical Fq k + ω.conductor) →
        PowerSeries.coeff n ω.lSeriesF = (∏ v ∈ ω.ramSet, ω.kappaV ψ₀ v) * ω.ev ω.bIdele *
          ((((Nat.card Fq : ℝ) ^ ((n : ℝ) - (Divisor.deg (canonical Fq k + ω.conductor) : ℝ) / 2)) : ℝ) : ℂ) *
          PowerSeries.coeff (Divisor.deg (canonical Fq k + ω.conductor) - n).toNat (ω⁻¹).lSeriesF := by
  refine ⟨?_, ?_, fun n hn => ?_⟩
  · rw [norm_prod]
    exact Finset.prod_eq_one fun v hv => ω.norm_kappaV ψ₀ hc hψ₀ hv
  · rw [map_add, (weil_VI_2_cor1 hc).1, genus_eq hc]
  · rw [coeff_lSeriesF_fe_aux ψ₀ ω hc hψ₀ hf n,
      show Divisor.deg (canonical Fq k + ω.conductor) - (n : ℤ) =
        ((Divisor.deg (canonical Fq k + ω.conductor) - n).toNat : ℕ) by omega,
      aCoef_stdPhi, haarU_integralUnits, ENNReal.toReal_one, Complex.ofReal_one, one_mul,
      ← show Divisor.deg (canonical Fq k + ω.conductor) - (n : ℤ) =
        ((Divisor.deg (canonical Fq k + ω.conductor) - n).toNat : ℕ) by omega, ← mul_assoc,
      ω.const_eq ψ₀ hc n, Int.cast_natCast]

/-- **Weil, VII.§7 Thm. 6, exact degree for ramified $\omega$, function fields**: $L(u,\omega)$ is a polynomial of
degree exactly $2g-2+\deg\mathfrak f$. -/
@[kb "weil1973bnt" "Ch. VII, §7, Thm. 6 (p. 134), ramified ω: L(u, ω) is a polynomial of degree exactly 2g - 2 + deg f"]
theorem weil_VII_7_thm6_ramified_exact (hc : IsConstantField Fq k) (hf : ω.conductor ≠ 0) :
    ∃ P : Polynomial ℂ, (P.natDegree : ℤ) = 2 * (genus Fq k : ℤ) - 2 + Divisor.deg ω.conductor ∧
      (P : PowerSeries ℂ) = ω.lSeriesF := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_addChar_ne_one (Fq := Fq)
  obtain ⟨P, hPdeg, hPeq⟩ := weil_VII_7_thm6_degree hc ω (ω.not_isPrincipal hf)
  obtain ⟨hκ, hN, hfe⟩ := ω.weil_VII_7_thm6_ramified_fe ψ₀ hc hψ₀ hf
  set N := Divisor.deg (canonical Fq k + ω.conductor)
  -- `N ≥ 0`, from the coefficient of `u^0`
  have hN0 : 0 ≤ N := by
    by_contra hneg
    have h0 := coeff_lSeriesF_fe_aux ψ₀ ω hc hψ₀ hf 0
    rw [coeff_zero_lSeriesF, aCoef_stdPhi_neg _ _ (by push_cast; omega), mul_zero, mul_zero] at h0
    exact one_ne_zero h0
  have htop := hfe N.toNat (by omega)
  rw [show N - (N.toNat : ℤ) = 0 by omega, Int.toNat_zero, coeff_zero_lSeriesF, mul_one] at htop
  have hne : P.coeff N.toNat ≠ 0 := by
    rw [← Polynomial.coeff_coe, hPeq, htop]
    refine mul_ne_zero (mul_ne_zero ?_ (ω.ev_ne_zero _)) ?_
    · intro h; rw [h, norm_zero] at hκ; exact zero_ne_one hκ
    · exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast (Nat.card_pos (α := Fq))) _).ne'
  refine ⟨P, ?_, hPeq⟩
  have := Polynomial.le_natDegree_of_ne_zero hne
  omega

end FFHeckeCharacter

end

end NumberFieldKB.WeilBNT.FF
