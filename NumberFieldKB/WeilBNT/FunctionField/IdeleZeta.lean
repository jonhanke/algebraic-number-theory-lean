import NumberFieldKB.WeilBNT.FunctionField.IdeleHaar
import NumberFieldKB.WeilBNT.FunctionField.DivisorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Zeta integrals on the ideles of a function field (Weil VII.§4–§5 in characteristic $p$; VII.§5 Cor. 7)

$k$ is a global function field with field of constants $\mathbb F_q$, genus $g$ and $h=\lvert D_0/P\rvert$;
$\mu$ is a Haar measure on $k_{\mathbb A}^\times$ and $\Phi$ a Schwartz–Bruhat function on $k_{\mathbb A}$
(`FFAdeleRing.IsSchwartzBruhat`). Weil's zeta integral (VII.§4 (4)) for $\omega_s(z)=\lvert z\rvert_{\mathbb A}^s$ is
$$Z(\omega_s,\Phi)=\int_{k_{\mathbb A}^\times}\Phi(z)\,\lvert z\rvert_{\mathbb A}^s\,d\mu(z)$$
(`FFIdeleGroup.zetaIntegral`).

* **`FFIdeleGroup.weil_VII_5_thm2_ff`** (Weil VII.§5 Thm. 2 for $\omega=\omega_s$, characteristic $p$, the
  continuation and the pole at $\omega_0$): for $\operatorname{Re}s>1$ the integral converges absolutely and, with
  $u=q^{-s}$,
  $$Z(\omega_s,\Phi)=L(u)+\frac{\alpha}{1-qu}-c_\mu\,\frac{\Phi(0)}{1-u},\qquad c_\mu=\frac{h\,\mu(\prod_v\mathfrak r_v^\times)}{q-1},$$
  for a Laurent polynomial $L$ and a constant $\alpha$. So $Z$ continues to a meromorphic function of $s$
  (a rational function of $q^{-s}$), holomorphic except where $q^{-s}=1$ or $q^{1-s}=1$.
* **`FFIdeleGroup.weil_VII_5_cor7`** (Weil VII.§5 Cor. 7): for Weil's Haar measure ($c_\mu=1$, see below),
  $Z(\omega_s,\Phi)+\Phi(0)(1-q^{-s})^{-1}$ is holomorphic at $s=0$.

**Weil's normalization.** Weil (VII.§5, p. 120) takes on $G_k=k_{\mathbb A}^\times/k^\times$ the measure
$\mu_1\times\nu$ with $\mu_1(G_k^1)=1$ and $\nu(\{1\})=1$ on $N=q^{\mathbb Z}$ (VII.§5 Cor. 6), lifted to
$k_{\mathbb A}^\times$. Since $\prod_v\mathfrak r_v^\times\cap k^\times=\mathbb F_q^\times$ and
$G_k^1/(\text{image of }\prod_v\mathfrak r_v^\times)\cong D_0/P$ has $h$ elements, this measure gives
$\prod_v\mathfrak r_v^\times$ the volume $(q-1)/h$, i.e. $c_\mu=1$. This identification is formalized in
`FunctionField/IdeleQuotient.lean` (`measure_normOne_quotient`: $c_\mu=\nu(G_k^1)$ for the image $\nu$ of $\mu$ on
$G_k$; `weil_VII_5_cor7_quotient`: Cor. 7 for every Haar measure with $\nu(G_k^1)=1$). Here Cor. 7 is stated for the
Haar measure with $\mu(\prod_v\mathfrak r_v^\times)=(q-1)/h$ (`weilIdeleMeasure`), and Thm. 2 for every Haar measure
with the explicit constant $c_\mu$.

**Proof.** $k_{\mathbb A}^\times$ is the disjoint union over the countably many divisors $D$ of the open cosets
$\{\operatorname{div}z=D\}=\pi^D\prod_v\mathfrak r_v^\times$ (`FFIdeleGroup.mem_fiber_iff`). By linearity it suffices to
take $\Phi$ the indicator of $r+U(\mathfrak b)$. Let $T$ be the finite set of places with
$r_v\notin\mathfrak p_v^{-\mathfrak b(v)}$. On the coset over $D$ the integrand is $u^{\deg D}$ times the indicator of a
set whose measure is $0$ unless $D$ lies in the translated cone $D^*+C_T$ ($D(v)=\operatorname{ord}_v r_v$ on $T$,
$D\ge-\mathfrak b$ elsewhere), and is then a constant $M$ independent of $D$ (`piD_mul_mem_cosSet_iff`). So
$Z=M\sum_{D\in D^*+C_T}u^{\deg D}$, which is evaluated by `hasSum_cone` (Riemann–Roch counts of effective divisors
prime to $T$). The coefficient of $(1-u)^{-1}$ is $-Mh/(q-1)$ if $T=\emptyset$ (then $\Phi(0)=1$,
$M=\mu(\prod_v\mathfrak r_v^\times)$) and $0$ otherwise (then $\Phi(0)=0$). This replaces Weil's proof through Poisson
summation on $G_k$ (VII.§5, pp. 121–124) by the equivalent Riemann–Roch count; the functional equation
$Z(\omega,\Phi)=Z(\omega_1\omega^{-1},\hat\Phi)$ and the residue $\Phi'(0)$ at $\omega_1$ are not formalized here.
-/

open MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal

namespace NumberFieldKB.WeilBNT.FF

noncomputable section

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

set_option linter.unusedSectionVars false

open Classical

namespace FFIdeleGroup

/-! ### The quasicharacter `ω_s` and the zeta integral -/

/-- $\omega_s(z)=\lvert z\rvert_{\mathbb A}^s$. -/
def omegaS (s : ℂ) (z : FFIdeleGroup Fq k) : ℂ := ((norm z : ℝ) : ℂ) ^ s

variable (Fq) in
/-- $u=q^{-s}$. -/
def uS (s : ℂ) : ℂ := (Nat.card Fq : ℂ) ^ (-s)

theorem natCard_pos : 0 < (Nat.card Fq : ℝ) := by
  have : 0 < Nat.card Fq := Nat.card_pos
  exact_mod_cast this

/-- $\lvert z\rvert_{\mathbb A}^s=(q^{-s})^{\deg\operatorname{div}z}$. -/
theorem omegaS_eq (s : ℂ) (z : FFIdeleGroup Fq k) : omegaS s z = uS Fq s ^ Divisor.deg (div z) := by
  rw [omegaS, norm_eq, uS]
  set n := Divisor.deg (div z)
  have hq : (0 : ℝ) < Nat.card Fq := natCard_pos
  have h1 : (((Nat.card Fq : ℝ≥0) ^ (-n) : ℝ≥0) : ℝ) = (Nat.card Fq : ℝ) ^ (-n) := by push_cast; rfl
  rw [h1, Complex.ofReal_zpow, Complex.ofReal_natCast, ← Complex.cpow_intCast, ← Complex.cpow_mul,
    ← Complex.cpow_int_mul]
  · congr 1; push_cast; ring
  all_goals
    have him : (Complex.log (Nat.card Fq : ℂ)).im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hq.le, Complex.ofReal_im]
    simp [Complex.mul_im, him, Real.pi_pos, Real.pi_pos.le]

theorem norm_uS (s : ℂ) : ‖uS Fq s‖ = (Nat.card Fq : ℝ) ^ (-s.re) := by
  rw [uS, Complex.norm_natCast_cpow_of_pos Nat.card_pos, Complex.neg_re]

theorem norm_q_mul_uS_lt_one {s : ℂ} (hs : 1 < s.re) : ‖(Nat.card Fq : ℂ) * uS Fq s‖ < 1 := by
  have hq : (1 : ℝ) < Nat.card Fq := by
    have : 1 < Nat.card Fq := Finite.one_lt_card
    exact_mod_cast this
  rw [_root_.norm_mul, norm_uS, Complex.norm_natCast]
  calc (Nat.card Fq : ℝ) * (Nat.card Fq : ℝ) ^ (-s.re) = (Nat.card Fq : ℝ) ^ (1 - s.re) := by
        rw [Real.rpow_sub (by linarith), Real.rpow_one, Real.rpow_neg (by linarith), div_eq_mul_inv]
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)

/-- **Weil's zeta integral** $Z(\omega_s,\Phi)=\int\Phi(z)\lvert z\rvert_{\mathbb A}^s\,d\mu(z)$ (VII.§4 (4)). -/
def zetaIntegral (μ : Measure (FFIdeleGroup Fq k)) (Φ : FFAdeleRing Fq k → ℂ) (s : ℂ) : ℂ :=
  ∫ z, Φ (z : FFAdeleRing Fq k) * omegaS s z ∂μ

theorem continuous_omegaS (s : ℂ) : Continuous (omegaS (Fq := Fq) (k := k) s) := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  refine (continuousAt_const : ContinuousAt (fun _ => omegaS s z) z).congr ?_
  filter_upwards [div_eventually_eq z] with w hw
  rw [omegaS_eq, omegaS_eq, hw]

/-! ### Change of variables on a fibre of the divisor map -/

theorem preimage_fiber (D : Divisor Fq k) :
    (fun u => piD D * u) ⁻¹' {z : FFIdeleGroup Fq k | div z = D} = integralUnits := by
  ext u
  simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_fiber_iff, inv_mul_cancel_left]

theorem setIntegral_fiber {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (FFIdeleGroup Fq k)) [μ.IsMulLeftInvariant] (D : Divisor Fq k)
    (f : FFIdeleGroup Fq k → E) :
    ∫ z in {z | div z = D}, f z ∂μ = ∫ u in integralUnits, f (piD D * u) ∂μ := by
  rw [← preimage_fiber D,
    (measurePreserving_mul_left μ (piD D)).setIntegral_preimage_emb
      (MeasurableEquiv.mulLeft (piD D)).measurableEmbedding]

theorem measure_fiber (μ : Measure (FFIdeleGroup Fq k)) [μ.IsMulLeftInvariant] (D : Divisor Fq k) :
    μ {z | div z = D} = μ integralUnits := by
  have : {z : FFIdeleGroup Fq k | div z = D} = (fun z => (piD D)⁻¹ * z) ⁻¹' integralUnits := by
    ext z; exact mem_fiber_iff D z
  rw [this, measure_preimage_mul]

theorem comp_piD_mul (D : Divisor Fq k) (u : FFIdeleGroup Fq k) (v : Place Fq k) :
    comp (piD D * u) v = ((unif v ^ D v : v.Completionˣ) : v.Completion) * comp u v := by
  rw [comp_mul, comp_piD]

theorem valued_comp_piD_mul (D : Divisor Fq k) {u : FFIdeleGroup Fq k} (hu : u ∈ integralUnits)
    (v : Place Fq k) : Valued.v (comp (piD D * u) v) = WithZero.exp (-D v) := by
  rw [comp_mul, map_mul, valued_comp_piD, (mem_integralUnits_iff u).1 hu v, mul_one]

theorem div_piD_mul (D : Divisor Fq k) {u : FFIdeleGroup Fq k} (hu : u ∈ integralUnits) :
    div (piD D * u) = D := by
  rw [div_mul, div_piD, (mem_integralUnits_iff_div u).1 hu, add_zero]

/-! ### Coset indicators: the local analysis -/

theorem mem_cosSet_iff (b : Divisor Fq k) (r x : FFAdeleRing Fq k) :
    x ∈ FFAdeleRing.cosSet b r ↔ ∀ v : Place Fq k, Valued.v (x v - r v) ≤ WithZero.exp (b v) :=
  Iff.rfl

/-- The places where $r_v\notin\mathfrak p_v^{-\mathfrak b(v)}$. -/
def badSet (b : Divisor Fq k) (r : FFAdeleRing Fq k) : Set (Place Fq k) :=
  {v | WithZero.exp (b v) < Valued.v (r v)}

theorem finite_badSet (b : Divisor Fq k) (r : FFAdeleRing Fq k) : (badSet b r).Finite := by
  have h1 : {v : Place Fq k | ¬ (r v ∈ (v.completionIntegers : Set v.Completion))}.Finite :=
    Filter.eventually_cofinite.1 r.2
  refine (h1.union b.support.finite_toSet).subset fun v hv => ?_
  by_cases hb : v ∈ b.support
  · exact Or.inr hb
  · left
    have hb0 : b v = 0 := Finsupp.notMem_support_iff.1 hb
    intro hr
    have hv' : WithZero.exp (b v) < Valued.v (r v) := hv
    rw [hb0, WithZero.exp_zero] at hv'
    exact absurd (show Valued.v (r v) ≤ 1 from hr) (not_le.2 hv')

/-- $T$, as a finite set. -/
def badT (b : Divisor Fq k) (r : FFAdeleRing Fq k) : Finset (Place Fq k) := (finite_badSet b r).toFinset

theorem mem_badT {b : Divisor Fq k} {r : FFAdeleRing Fq k} {v : Place Fq k} :
    v ∈ badT b r ↔ WithZero.exp (b v) < Valued.v (r v) := by
  rw [badT, Set.Finite.mem_toFinset]; rfl

/-- The vertex $D^*$ of the cone: $\operatorname{ord}_v r_v$ on $T$, $-\mathfrak b$ elsewhere. -/
def Dst (b : Divisor Fq k) (r : FFAdeleRing Fq k) : Divisor Fq k :=
  Finsupp.ofSupportFinite (fun v => if v ∈ badT b r then v.ordC (r v) else -b v) (by
    refine ((badT b r).finite_toSet.union b.support.finite_toSet).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Finset.mem_coe, not_or, Finsupp.mem_support_iff, not_not] at h
    apply hv
    simp [h.1, h.2])

theorem Dst_apply (b : Divisor Fq k) (r : FFAdeleRing Fq k) (v : Place Fq k) :
    Dst b r v = if v ∈ badT b r then v.ordC (r v) else -b v := rfl

/-- Outside $T$: $v(x-r_v)\le e^{\mathfrak b(v)}$ iff $v(x)\le e^{\mathfrak b(v)}$. -/
theorem good_iff {v : Place Fq k} {b : Divisor Fq k} {r : FFAdeleRing Fq k} (hv : v ∉ badT b r)
    (x : v.Completion) :
    Valued.v (x - r v) ≤ WithZero.exp (b v) ↔ Valued.v x ≤ WithZero.exp (b v) := by
  rw [mem_badT, not_lt] at hv
  constructor
  · intro h
    calc Valued.v x = Valued.v ((x - r v) + r v) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (x - r v)) (Valued.v (r v)) := Valuation.map_add _ _ _
      _ ≤ _ := max_le h hv
  · intro h
    exact (Valuation.map_sub _ _ _).trans (max_le h hv)

/-- On $T$: $v(x-r_v)\le e^{\mathfrak b(v)}$ forces $v(x)=v(r_v)$. -/
theorem bad_valued_eq {v : Place Fq k} {b : Divisor Fq k} {r : FFAdeleRing Fq k} (hv : v ∈ badT b r)
    {x : v.Completion} (h : Valued.v (x - r v) ≤ WithZero.exp (b v)) : Valued.v x = Valued.v (r v) :=
  Valuation.map_eq_of_sub_lt _ (h.trans_lt (mem_badT.1 hv))

theorem exp_neg_eq_iff_ordC {v : Place Fq k} {y : v.Completion} (hy : y ≠ 0) (n : ℤ) :
    WithZero.exp (-n) = Valued.v y ↔ n = v.ordC y := by
  rw [v.valued_eq_exp_neg_ordC hy]
  constructor
  · intro h; have := WithZero.exp_injective h; omega
  · intro h; rw [h]

/-- **The key local computation.** For $u\in\prod_v\mathfrak r_v^\times$: $\pi^Du\in r+U(\mathfrak b)$ iff $D$ lies in
the cone $D^*+C_T$ and $\pi^{D^*}u\in r+U(\mathfrak b)$. -/
theorem piD_mul_mem_cosSet_iff (b : Divisor Fq k) (r : FFAdeleRing Fq k) (D : Divisor Fq k)
    {u : FFIdeleGroup Fq k} (hu : u ∈ integralUnits) :
    ((piD D * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) ∈ FFAdeleRing.cosSet b r ↔
      D ∈ cone (badT b r) (Dst b r) ∧
        ((piD (Dst b r) * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) ∈ FFAdeleRing.cosSet b r := by
  simp only [mem_cosSet_iff]
  have hc : ∀ (E : Divisor Fq k) (v : Place Fq k),
      ((piD E * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) v = comp (piD E * u) v := fun _ _ => rfl
  simp only [hc]
  have hgood : ∀ (E : Divisor Fq k) (v : Place Fq k), v ∉ badT b r →
      (Valued.v (comp (piD E * u) v - r v) ≤ WithZero.exp (b v) ↔ -E v ≤ b v) := by
    intro E v hv
    rw [good_iff hv, valued_comp_piD_mul E hu, WithZero.exp_le_exp]
  have hbad : ∀ (E : Divisor Fq k) (v : Place Fq k), v ∈ badT b r →
      Valued.v (comp (piD E * u) v - r v) ≤ WithZero.exp (b v) → E v = Dst b r v := by
    intro E v hv h
    have h1 := bad_valued_eq hv h
    rw [valued_comp_piD_mul E hu] at h1
    have hr0 : r v ≠ 0 := by
      intro h0; rw [mem_badT, h0, map_zero] at hv; exact not_lt_zero' hv
    rw [Dst_apply, if_pos hv]
    exact (exp_neg_eq_iff_ordC hr0 _).1 h1
  have hsame : ∀ (E E' : Divisor Fq k) (v : Place Fq k), E v = E' v →
      comp (piD E * u) v = comp (piD E' * u) v := by
    intro E E' v h
    rw [comp_piD_mul, comp_piD_mul, h]
  constructor
  · intro h
    have hcone : D ∈ cone (badT b r) (Dst b r) := by
      refine ⟨fun v hv => hbad D v hv (h v), fun v => ?_⟩
      by_cases hv : v ∈ badT b r
      · exact (hbad D v hv (h v)).ge
      · rw [Dst_apply, if_neg hv]
        have := (hgood D v hv).1 (h v)
        omega
    refine ⟨hcone, fun v => ?_⟩
    by_cases hv : v ∈ badT b r
    · rw [← hsame D _ v (hcone.1 v hv)]; exact h v
    · rw [hgood _ v hv, Dst_apply, if_neg hv, neg_neg]
  · rintro ⟨hcone, h⟩ v
    by_cases hv : v ∈ badT b r
    · rw [hsame D _ v (hcone.1 v hv)]; exact h v
    · rw [hgood _ v hv]
      have h1 := hcone.2 v
      rw [Dst_apply, if_neg hv] at h1
      omega

theorem cosInd_zero (b : Divisor Fq k) (r : FFAdeleRing Fq k) :
    FFAdeleRing.cosInd b r 0 = if badT b r = ∅ then 1 else 0 := by
  rw [FFAdeleRing.cosInd_apply]
  have : (0 - r ∈ FFAdeleRing.U b) ↔ badT b r = ∅ := by
    rw [zero_sub, (FFAdeleRing.U b).neg_mem_iff, FFAdeleRing.mem_U_iff, Finset.eq_empty_iff_forall_notMem]
    simp only [mem_badT, not_lt]
  by_cases h : badT b r = ∅
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]

/-- When $T=\emptyset$, $\pi^{D^*}u\in r+U(\mathfrak b)$ for every $u\in\prod_v\mathfrak r_v^\times$. -/
theorem piD_Dst_mul_mem_of_empty {b : Divisor Fq k} {r : FFAdeleRing Fq k} (hT : badT b r = ∅)
    {u : FFIdeleGroup Fq k} (hu : u ∈ integralUnits) :
    ((piD (Dst b r) * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) ∈ FFAdeleRing.cosSet b r := by
  intro v
  have hv : v ∉ badT b r := by rw [hT]; exact Finset.notMem_empty v
  show Valued.v (comp (piD (Dst b r) * u) v - r v) ≤ _
  rw [good_iff hv, valued_comp_piD_mul _ hu, Dst_apply, if_neg hv, neg_neg]

/-! ### The integral over one fibre -/

/-- $P_E=\{u : \pi^Eu\in r+U(\mathfrak b)\}$. -/
def cosPre (b : Divisor Fq k) (r : FFAdeleRing Fq k) (E : Divisor Fq k) : Set (FFIdeleGroup Fq k) :=
  {u | ((piD E * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) ∈ FFAdeleRing.cosSet b r}

theorem isOpen_cosPre (b : Divisor Fq k) (r : FFAdeleRing Fq k) (E : Divisor Fq k) :
    IsOpen (cosPre b r E) :=
  (FFAdeleRing.isOpen_cosSet b r).preimage (Units.continuous_val.comp (continuous_const.mul continuous_id))

/-- The constant $M=\mu(\{u\in\prod_v\mathfrak r_v^\times : \pi^{D^*}u\in r+U(\mathfrak b)\})$. -/
def cosMass (μ : Measure (FFIdeleGroup Fq k)) (b : Divisor Fq k) (r : FFAdeleRing Fq k) : ℝ :=
  μ.real (integralUnits ∩ cosPre b r (Dst b r))

theorem inter_cosPre (b : Divisor Fq k) (r : FFAdeleRing Fq k) (D : Divisor Fq k) :
    integralUnits ∩ cosPre b r D =
      if D ∈ cone (badT b r) (Dst b r) then integralUnits ∩ cosPre b r (Dst b r) else ∅ := by
  ext u
  split_ifs with h
  · exact ⟨fun ⟨hu, hp⟩ => ⟨hu, ((piD_mul_mem_cosSet_iff b r D hu).1 hp).2⟩,
      fun ⟨hu, hp⟩ => ⟨hu, (piD_mul_mem_cosSet_iff b r D hu).2 ⟨h, hp⟩⟩⟩
  · simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hu hp
    exact h ((piD_mul_mem_cosSet_iff b r D hu).1 hp).1

theorem cosMass_of_empty (μ : Measure (FFIdeleGroup Fq k)) {b : Divisor Fq k} {r : FFAdeleRing Fq k}
    (hT : badT b r = ∅) : cosMass μ b r = μ.real integralUnits := by
  rw [cosMass, Set.inter_eq_left.2 fun u (hu : u ∈ integralUnits) =>
    (show u ∈ cosPre b r (Dst b r) from piD_Dst_mul_mem_of_empty hT hu)]

/-- **The integral of a coset indicator over the fibre over $D$.** -/
theorem setIntegral_fiber_cosSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (FFIdeleGroup Fq k)) [μ.IsMulLeftInvariant] (b : Divisor Fq k) (r : FFAdeleRing Fq k)
    (D : Divisor Fq k) (c : E) (φ : FFIdeleGroup Fq k → E)
    (hφ : ∀ z, div z = D → φ z = (FFAdeleRing.cosSet b r).indicator (fun _ => c) (z : FFAdeleRing Fq k)) :
    ∫ z in {z | div z = D}, φ z ∂μ = (cone (badT b r) (Dst b r)).indicator (fun _ => cosMass μ b r) D • c := by
  rw [setIntegral_fiber μ D]
  have h1 : ∫ u in integralUnits, φ (piD D * u) ∂μ =
      ∫ u in integralUnits, (cosPre b r D).indicator (fun _ => c) u ∂μ := by
    refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u hu => ?_
    rw [hφ _ (div_piD_mul D hu)]
    simp only [Set.indicator_apply, cosPre, Set.mem_setOf_eq]
  rw [h1, setIntegral_indicator (isOpen_cosPre b r D).measurableSet, setIntegral_const, inter_cosPre]
  unfold cosMass
  split_ifs with h
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, measureReal_empty, zero_smul]

/-- The integrand $\mathbf 1_{r+U(\mathfrak b)}(z)\,\lvert z\rvert^s$. -/
def cosIntegrand (b : Divisor Fq k) (r : FFAdeleRing Fq k) (s : ℂ) (z : FFIdeleGroup Fq k) : ℂ :=
  FFAdeleRing.cosInd b r (z : FFAdeleRing Fq k) * omegaS s z

theorem cosIntegrand_eq (b : Divisor Fq k) (r : FFAdeleRing Fq k) (s : ℂ) {D : Divisor Fq k}
    {z : FFIdeleGroup Fq k} (hz : div z = D) :
    cosIntegrand b r s z =
      (FFAdeleRing.cosSet b r).indicator (fun _ => uS Fq s ^ Divisor.deg D) (z : FFAdeleRing Fq k) := by
  rw [cosIntegrand, omegaS_eq, hz, FFAdeleRing.cosInd]
  simp only [Set.indicator_apply, Pi.one_apply]
  split_ifs <;> simp

theorem norm_cosIntegrand_eq (b : Divisor Fq k) (r : FFAdeleRing Fq k) (s : ℂ) {D : Divisor Fq k}
    {z : FFIdeleGroup Fq k} (hz : div z = D) :
    ‖cosIntegrand b r s z‖ =
      (FFAdeleRing.cosSet b r).indicator (fun _ => ‖uS Fq s‖ ^ Divisor.deg D) (z : FFAdeleRing Fq k) := by
  rw [cosIntegrand_eq b r s hz]
  simp only [Set.indicator_apply]
  split_ifs <;> simp [norm_zpow]

theorem measurable_cosIntegrand (b : Divisor Fq k) (r : FFAdeleRing Fq k) (s : ℂ) :
    Measurable (cosIntegrand (Fq := Fq) (k := k) b r s) := by
  have h1 : Measurable fun z : FFIdeleGroup Fq k => FFAdeleRing.cosInd b r (z : FFAdeleRing Fq k) := by
    have : (fun z : FFIdeleGroup Fq k => FFAdeleRing.cosInd b r (z : FFAdeleRing Fq k)) =
        ((fun z : FFIdeleGroup Fq k => (z : FFAdeleRing Fq k)) ⁻¹' FFAdeleRing.cosSet b r).indicator 1 := by
      ext z; simp [FFAdeleRing.cosInd, Set.indicator_apply]
    rw [this]
    exact measurable_one.indicator
      ((FFAdeleRing.isOpen_cosSet b r).preimage Units.continuous_val).measurableSet
  exact h1.mul (continuous_omegaS s).measurable

theorem integrableOn_fiber_cosIntegrand (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (b : Divisor Fq k) (r : FFAdeleRing Fq k) (s : ℂ) (D : Divisor Fq k) :
    IntegrableOn (cosIntegrand b r s) {z | div z = D} μ := by
  refine IntegrableOn.of_bound (by rw [measure_fiber]; exact measure_integralUnits_lt_top μ)
    (measurable_cosIntegrand b r s).aestronglyMeasurable (‖uS Fq s‖ ^ Divisor.deg D) ?_
  refine ae_restrict_of_forall_mem (measurableSet_fiber D) fun z hz => ?_
  rw [norm_cosIntegrand_eq b r s hz]
  simp only [Set.indicator_apply]
  split_ifs
  · exact le_rfl
  · exact zpow_nonneg (norm_nonneg _) _

theorem iUnion_fiber : (⋃ D : Divisor Fq k, {z : FFIdeleGroup Fq k | div z = D}) = Set.univ := by
  ext z; simp

theorem pairwise_disjoint_fiber :
    Pairwise (Function.onFun Disjoint fun D : Divisor Fq k => {z : FFIdeleGroup Fq k | div z = D}) := by
  intro D E hDE
  refine Set.disjoint_left.2 fun z h1 h2 => hDE ?_
  exact (show div z = D from h1).symm.trans h2

open FFAdeleRing in
/-- **The zeta integral of a coset indicator** (the computation behind Weil VII.§5 Thm. 2 in characteristic $p$):
for $\operatorname{Re}s>1$ it converges absolutely, and with $u=q^{-s}$ it equals $M$ times the series
$\sum_{D\in D^*+C_T}u^{\deg D}$ evaluated by `hasSum_cone`. -/
theorem zetaIntegral_cosInd (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (b : Divisor Fq k) (r : FFAdeleRing Fq k) :
    ∃ (N : ℕ) (α : ℂ), ∀ s : ℂ, 1 < s.re →
      Integrable (cosIntegrand b r s) μ ∧
      zetaIntegral μ (cosInd b r) s = (cosMass μ b r : ℂ) *
        (∑ n ∈ Finset.Ico (-(N : ℤ)) N,
            ({D | D ∈ cone (badT b r) (Dst b r) ∧ Divisor.deg D = n}.ncard : ℂ) * uS Fq s ^ n +
          α * ((Nat.card Fq : ℂ) * uS Fq s) ^ N / (1 - (Nat.card Fq : ℂ) * uS Fq s) +
          (if badT b r = ∅ then -((Nat.card (ClassGroup0 Fq k) : ℂ) / ((Nat.card Fq : ℂ) - 1)) else 0) *
            uS Fq s ^ N / (1 - uS Fq s)) := by
  obtain ⟨N, α, -, hsum⟩ := hasSum_cone hc (badT b r) (Dst b r)
  refine ⟨N, α, fun s hs => ?_⟩
  obtain ⟨hS, hSn⟩ := hsum (uS Fq s) (norm_q_mul_uS_lt_one hs)
  set M := cosMass μ b r
  set C := cone (badT b r) (Dst b r)
  have hpiece : ∀ D : Divisor Fq k, ∫ z in {z | div z = D}, cosIntegrand b r s z ∂μ =
      (M : ℂ) * C.indicator (fun D => uS Fq s ^ Divisor.deg D) D := by
    intro D
    rw [setIntegral_fiber_cosSet μ b r D (uS Fq s ^ Divisor.deg D) _ fun z hz => cosIntegrand_eq b r s hz]
    by_cases h : D ∈ C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.real_smul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul, mul_zero]
  have hpiecen : ∀ D : Divisor Fq k, ∫ z in {z | div z = D}, ‖cosIntegrand b r s z‖ ∂μ =
      M * ‖C.indicator (fun D => uS Fq s ^ Divisor.deg D) D‖ := by
    intro D
    rw [setIntegral_fiber_cosSet μ b r D (‖uS Fq s‖ ^ Divisor.deg D) _ fun z hz => norm_cosIntegrand_eq b r s hz]
    by_cases h : D ∈ C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, smul_eq_mul, norm_zpow]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul, norm_zero, mul_zero]
  have hint : IntegrableOn (cosIntegrand b r s) (⋃ D : Divisor Fq k, {z | div z = D}) μ :=
    integrableOn_iUnion_of_summable_integral_norm (integrableOn_fiber_cosIntegrand μ b r s)
      (by simp_rw [hpiecen]; exact hSn.mul_left M)
  have hHS := hasSum_integral_iUnion (fun D => measurableSet_fiber D) pairwise_disjoint_fiber hint
  simp_rw [hpiece] at hHS
  rw [iUnion_fiber, setIntegral_univ] at hHS
  rw [iUnion_fiber] at hint
  refine ⟨integrableOn_univ.1 hint, ?_⟩
  rw [zetaIntegral]
  exact hHS.unique (hS.mul_left (M : ℂ))

/-! ### Laurent polynomials in `u = q^{-s}` -/

/-- Evaluation $\sum_nc_nu^n$ of a Laurent polynomial $c\in\mathbb C[u,u^{-1}]$ (finitely supported coefficients). -/
def laurentEval (c : ℤ →₀ ℂ) (u : ℂ) : ℂ :=
  Finsupp.liftAddHom (fun n => AddMonoidHom.mulRight (u ^ n)) c

theorem laurentEval_add (c d : ℤ →₀ ℂ) (u : ℂ) :
    laurentEval (c + d) u = laurentEval c u + laurentEval d u := map_add _ _ _

theorem laurentEval_single (n : ℤ) (a u : ℂ) : laurentEval (Finsupp.single n a) u = a * u ^ n := by
  simp [laurentEval]

theorem laurentEval_sum {ι : Type*} (S : Finset ι) (f : ι → ℤ →₀ ℂ) (u : ℂ) :
    laurentEval (∑ i ∈ S, f i) u = ∑ i ∈ S, laurentEval (f i) u := map_sum _ _ _

theorem laurentEval_smul (a : ℂ) (c : ℤ →₀ ℂ) (u : ℂ) : laurentEval (a • c) u = a * laurentEval c u := by
  induction c using Finsupp.induction_linear with
  | zero => simp [laurentEval]
  | add c d hc hd => rw [smul_add, laurentEval_add, laurentEval_add, hc, hd, mul_add]
  | single n b => rw [Finsupp.smul_single, laurentEval_single, laurentEval_single, smul_eq_mul, mul_assoc]

theorem laurentEval_eq_sum (c : ℤ →₀ ℂ) (u : ℂ) :
    laurentEval c u = ∑ n ∈ c.support, c n * u ^ n := by
  rw [laurentEval, Finsupp.liftAddHom_apply, Finsupp.sum]
  rfl

theorem pow_div_one_sub (x : ℂ) (hx : x ≠ 1) (N : ℕ) :
    x ^ N / (1 - x) = 1 / (1 - x) - ∑ j ∈ Finset.range N, x ^ j := by
  rw [geom_sum_eq hx N]
  have h1 : (1 - x) ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have h2 : (x - 1) ≠ 0 := sub_ne_zero.2 hx
  field_simp
  ring

theorem ne_one_of_norm_lt_one {x : ℂ} (hx : ‖x‖ < 1) : x ≠ 1 := by
  rintro rfl; rw [norm_one] at hx; exact lt_irrefl _ hx

theorem norm_uS_lt_one {s : ℂ} (hs : 1 < s.re) : ‖uS Fq s‖ < 1 := by
  have hq : (1 : ℝ) ≤ ‖(Nat.card Fq : ℂ)‖ := by
    rw [Complex.norm_natCast]; exact_mod_cast (show 1 ≤ Nat.card Fq from Nat.card_pos)
  have := norm_q_mul_uS_lt_one (Fq := Fq) hs
  rw [_root_.norm_mul] at this
  calc ‖uS Fq s‖ ≤ ‖(Nat.card Fq : ℂ)‖ * ‖uS Fq s‖ := le_mul_of_one_le_left (norm_nonneg _) hq
    _ < 1 := this

/-- $c_\mu=h\,\mu(\prod_v\mathfrak r_v^\times)/(q-1)$: minus the coefficient of $\Phi(0)(1-q^{-s})^{-1}$. -/
def zetaConst (μ : Measure (FFIdeleGroup Fq k)) : ℂ :=
  (μ.real integralUnits : ℂ) * (Nat.card (ClassGroup0 Fq k) : ℂ) / ((Nat.card Fq : ℂ) - 1)

open FFAdeleRing in
/-- **The zeta integral of a coset indicator, rational form.** -/
theorem zetaIntegral_cosInd_rational (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k))
    [μ.IsHaarMeasure] (b : Divisor Fq k) (r : FFAdeleRing Fq k) :
    ∃ (c : ℤ →₀ ℂ) (α : ℂ), ∀ s : ℂ, 1 < s.re →
      Integrable (cosIntegrand b r s) μ ∧
      zetaIntegral μ (cosInd b r) s = laurentEval c (uS Fq s) + α / (1 - (Nat.card Fq : ℂ) * uS Fq s) -
        zetaConst μ * cosInd b r 0 / (1 - uS Fq s) := by
  obtain ⟨N, α, h⟩ := zetaIntegral_cosInd hc μ b r
  set q : ℂ := (Nat.card Fq : ℂ)
  set M : ℂ := (cosMass μ b r : ℂ)
  set β : ℂ := if badT b r = ∅ then -((Nat.card (ClassGroup0 Fq k) : ℂ) / (q - 1)) else 0
  set a : ℤ → ℂ := fun n => ({D | D ∈ cone (badT b r) (Dst b r) ∧ Divisor.deg D = n}.ncard : ℂ)
  have hq1 : q - 1 ≠ 0 := by
    show (Nat.card Fq : ℂ) - 1 ≠ 0
    rw [sub_ne_zero]; exact_mod_cast (show Nat.card Fq ≠ 1 from (Finite.one_lt_card).ne')
  have hqq : (Nat.card Fq : ℂ) = q := rfl
  have hMβ : M * β = -(zetaConst μ * cosInd b r 0) := by
    rw [cosInd_zero, zetaConst]
    by_cases hT : badT b r = ∅
    · simp only [β, M, if_pos hT, cosMass_of_empty μ hT]
      rw [hqq]
      field_simp
    · simp only [β, if_neg hT]; ring
  refine ⟨∑ n ∈ Finset.Ico (-(N : ℤ)) N, Finsupp.single n (M * a n) +
      ∑ j ∈ Finset.range N, Finsupp.single (j : ℤ) (-(M * α) * q ^ j - M * β), M * α, fun s hs => ?_⟩
  obtain ⟨hint, hval⟩ := h s hs
  refine ⟨hint, ?_⟩
  set u := uS Fq s
  have hu1 : u ≠ 1 := ne_one_of_norm_lt_one (norm_uS_lt_one hs)
  have hqu1 : q * u ≠ 1 := ne_one_of_norm_lt_one (norm_q_mul_uS_lt_one hs)
  rw [hval]
  have e1 := pow_div_one_sub (q * u) hqu1 N
  have e2 := pow_div_one_sub u hu1 N
  have hL : laurentEval (∑ n ∈ Finset.Ico (-(N : ℤ)) N, Finsupp.single n (M * a n) +
      ∑ j ∈ Finset.range N, Finsupp.single (j : ℤ) (-(M * α) * q ^ j - M * β)) u =
      M * ∑ n ∈ Finset.Ico (-(N : ℤ)) N, a n * u ^ n -
        (M * α) * ∑ j ∈ Finset.range N, (q * u) ^ j - (M * β) * ∑ j ∈ Finset.range N, u ^ j := by
    rw [laurentEval_add, laurentEval_sum, laurentEval_sum]
    simp only [laurentEval_single]
    have e3 : ∑ j ∈ Finset.range N, (-(M * α) * q ^ j - M * β) * u ^ (j : ℤ) =
        -(M * α) * ∑ j ∈ Finset.range N, (q * u) ^ j - M * β * ∑ j ∈ Finset.range N, u ^ j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [zpow_natCast, mul_pow]; ring
    have e4 : ∑ n ∈ Finset.Ico (-(N : ℤ)) N, M * a n * u ^ n =
        M * ∑ n ∈ Finset.Ico (-(N : ℤ)) N, a n * u ^ n := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
    rw [e3, e4]; ring
  rw [hL, mul_add, mul_add, mul_div_assoc', mul_div_assoc', ← mul_assoc, ← mul_assoc]
  rw [show M * α * (q * u) ^ N / (1 - q * u) = M * α * ((q * u) ^ N / (1 - q * u)) by ring,
    show M * β * u ^ N / (1 - u) = M * β * (u ^ N / (1 - u)) by ring, e1, e2, hMβ]
  ring

open FFAdeleRing in
/-- **Weil VII.§5 Thm. 2 for $\omega=\omega_s$, characteristic $p$: rationality in $q^{-s}$ and the pole at
$\omega_0$.** For a Haar measure $\mu$ on $k_{\mathbb A}^\times$ and a Schwartz–Bruhat function $\Phi$, the integral
$Z(\omega_s,\Phi)$ converges absolutely for $\operatorname{Re}s>1$, and there are a Laurent polynomial $L$ and
$\alpha\in\mathbb C$ with
$$Z(\omega_s,\Phi)=L(q^{-s})+\frac{\alpha}{1-q^{1-s}}-c_\mu\frac{\Phi(0)}{1-q^{-s}},\qquad
c_\mu=\frac{h\,\mu(\prod_v\mathfrak r_v^\times)}{q-1}.$$ -/
@[kb "weil1973bnt" "Ch. VII, §5, Thm. 2 (p. 121), function fields, ω = ω_s: Z(ω_s, Φ) is a rational function of q^(-s) with the pole -c Φ(0)/(1 - q^(-s)) at ω_0"]
theorem weil_VII_5_thm2_ff_rational (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k))
    [μ.IsHaarMeasure] {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    ∃ (c : ℤ →₀ ℂ) (α : ℂ), ∀ s : ℂ, 1 < s.re →
      Integrable (fun z : FFIdeleGroup Fq k => Φ (z : FFAdeleRing Fq k) * omegaS s z) μ ∧
      zetaIntegral μ Φ s = laurentEval c (uS Fq s) + α / (1 - (Nat.card Fq : ℂ) * uS Fq s) -
        zetaConst μ * Φ 0 / (1 - uS Fq s) := by
  obtain ⟨-, b, n, ρ, -, -, hdec⟩ := exists_decomp hΦ
  have hshape := fun i => zetaIntegral_cosInd_rational hc μ b (ρ i)
  choose c α hcα using hshape
  refine ⟨∑ i, Φ (ρ i) • c i, ∑ i, Φ (ρ i) * α i, fun s hs => ?_⟩
  have hfun : (fun z : FFIdeleGroup Fq k => Φ (z : FFAdeleRing Fq k) * omegaS s z) =
      fun z => ∑ i, Φ (ρ i) * cosIntegrand b (ρ i) s z := by
    ext z
    rw [hdec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cosIntegrand]; ring
  have hint : ∀ i, Integrable (fun z => Φ (ρ i) * cosIntegrand b (ρ i) s z) μ :=
    fun i => ((hcα i s hs).1).const_mul _
  refine ⟨by rw [hfun]; exact integrable_finset_sum _ fun i _ => hint i, ?_⟩
  have hZ : zetaIntegral μ Φ s = ∑ i, Φ (ρ i) * zetaIntegral μ (cosInd b (ρ i)) s := by
    rw [zetaIntegral, hfun, integral_finset_sum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    rfl
  rw [hZ, hdec 0]
  simp only [fun i => (hcα i s hs).2]
  rw [laurentEval_sum]
  simp only [laurentEval_smul, Finset.sum_div, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem uS_ne_zero (s : ℂ) : uS Fq s ≠ 0 := by
  rw [uS]
  exact Complex.cpow_ne_zero_iff.2
    (Or.inl (by exact_mod_cast (show Nat.card Fq ≠ 0 from Nat.card_pos.ne')))

theorem analyticAt_uS (s : ℂ) : AnalyticAt ℂ (uS Fq) s := by
  have hslit : ((Nat.card Fq : ℕ) : ℂ) ∈ Complex.slitPlane :=
    Complex.natCast_mem_slitPlane.2 (Nat.card_pos.ne')
  exact (analyticAt_const.cpow analyticAt_id.neg hslit :)

theorem analyticAt_laurentEval (c : ℤ →₀ ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun s => laurentEval c (uS Fq s)) s := by
  have : (fun s => laurentEval c (uS Fq s)) = ∑ n ∈ c.support, fun s => c n * uS Fq s ^ n := by
    ext s; rw [laurentEval_eq_sum, Finset.sum_apply]
  rw [this]
  exact Finset.analyticAt_sum _ fun n _ => analyticAt_const.mul ((analyticAt_uS s).zpow (uS_ne_zero s))

/-- **Weil VII.§5 Thm. 2 for $\omega=\omega_s$, characteristic $p$: continuation.** $Z(\omega_s,\Phi)$, defined by
the absolutely convergent integral for $\operatorname{Re}s>1$, continues to a meromorphic function on $\mathbb C$,
holomorphic wherever $q^{-s}\ne1$ and $q^{1-s}\ne1$ (that is, except at the quasicharacters $\omega_0$, $\omega_1$),
and $Z(\omega_s,\Phi)+c_\mu\Phi(0)(1-q^{-s})^{-1}$ is holomorphic at $s=0$. -/
@[kb "weil1973bnt" "Ch. VII, §5, Thm. 2 (p. 121), function fields, ω = ω_s: meromorphic continuation, holomorphic except at ω_0 and ω_1"]
theorem weil_VII_5_thm2_ff (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k))
    [μ.IsHaarMeasure] {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ) :
    ∃ Zc : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        Integrable (fun z : FFIdeleGroup Fq k => Φ (z : FFAdeleRing Fq k) * omegaS s z) μ ∧
        zetaIntegral μ Φ s = Zc s) ∧
      MeromorphicOn Zc Set.univ ∧
      (∀ s : ℂ, uS Fq s ≠ 1 → (Nat.card Fq : ℂ) * uS Fq s ≠ 1 → AnalyticAt ℂ Zc s) ∧
      AnalyticAt ℂ (fun s => Zc s + zetaConst μ * Φ 0 * (1 - uS Fq s)⁻¹) 0 := by
  obtain ⟨c, α, h⟩ := weil_VII_5_thm2_ff_rational hc μ hΦ
  set q : ℂ := (Nat.card Fq : ℂ)
  refine ⟨fun s => laurentEval c (uS Fq s) + α / (1 - q * uS Fq s) - zetaConst μ * Φ 0 / (1 - uS Fq s),
    fun s hs => h s hs, fun s _ => ?_, fun s h1 h2 => ?_, ?_⟩
  · have hL := (analyticAt_laurentEval (Fq := Fq) c s).meromorphicAt
    have hA : MeromorphicAt (fun s => α / (1 - q * uS Fq s)) s :=
      analyticAt_const.meromorphicAt.div
        (analyticAt_const.sub (analyticAt_const.mul (analyticAt_uS s))).meromorphicAt
    have hB : MeromorphicAt (fun s => zetaConst μ * Φ 0 / (1 - uS Fq s)) s :=
      analyticAt_const.meromorphicAt.div (analyticAt_const.sub (analyticAt_uS s)).meromorphicAt
    exact (hL.add hA).sub hB
  · refine ((analyticAt_laurentEval c s).add ?_).sub ?_
    · exact analyticAt_const.div (analyticAt_const.sub (analyticAt_const.mul (analyticAt_uS s)))
        (sub_ne_zero.2 (Ne.symm h2))
    · exact analyticAt_const.div (analyticAt_const.sub (analyticAt_uS s)) (sub_ne_zero.2 (Ne.symm h1))
  · have heq : (fun s => laurentEval c (uS Fq s) + α / (1 - q * uS Fq s) - zetaConst μ * Φ 0 / (1 - uS Fq s) +
        zetaConst μ * Φ 0 * (1 - uS Fq s)⁻¹) = fun s => laurentEval c (uS Fq s) + α / (1 - q * uS Fq s) := by
      ext s; rw [div_eq_mul_inv (zetaConst μ * Φ 0)]; ring
    rw [heq]
    have hu0 : uS Fq 0 = 1 := by rw [uS, neg_zero, Complex.cpow_zero]
    refine (analyticAt_laurentEval c 0).add
      (analyticAt_const.div (analyticAt_const.sub (analyticAt_const.mul (analyticAt_uS 0))) ?_)
    rw [hu0, mul_one, sub_ne_zero]
    show (1 : ℂ) ≠ (Nat.card Fq : ℂ)
    exact_mod_cast (show 1 ≠ Nat.card Fq from (Finite.one_lt_card).ne)

/-! ### Weil's normalization and VII.§5 Cor. 7 -/

instance : Nonempty (ClassGroup0 Fq k) := ⟨0⟩

theorem classNumber_pos : 0 < Nat.card (ClassGroup0 Fq k) := by
  have := finite_classGroup0 (Fq := Fq) (k := k)
  exact Nat.card_pos

variable (Fq k) in
/-- **Weil's Haar measure on $k_{\mathbb A}^\times$** (VII.§5, p. 120, in characteristic $p$): the Haar measure with
$\mu(\prod_v\mathfrak r_v^\times)=(q-1)/h$, i.e. $c_\mu=1$; by `measure_normOne_quotient` (`IdeleQuotient.lean`) these
are the Haar measures whose image on $G_k$ gives $G_k^1$ the measure $1$, as Weil requires. -/
def weilIdeleMeasure : Measure (FFIdeleGroup Fq k) :=
  ENNReal.ofReal (((Nat.card Fq : ℝ) - 1) / Nat.card (ClassGroup0 Fq k)) • haarU Fq k

theorem weilIdeleMeasure_coeff_pos : 0 < ((Nat.card Fq : ℝ) - 1) / Nat.card (ClassGroup0 Fq k) := by
  have h1 : (1 : ℝ) < Nat.card Fq := by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card Fq)
  have h2 : (0 : ℝ) < Nat.card (ClassGroup0 Fq k) := by exact_mod_cast classNumber_pos
  exact div_pos (by linarith) h2

instance : (weilIdeleMeasure Fq k).IsHaarMeasure :=
  Measure.IsHaarMeasure.smul _ (ENNReal.ofReal_pos.2 weilIdeleMeasure_coeff_pos).ne' ENNReal.ofReal_ne_top

theorem zetaConst_weilIdeleMeasure : zetaConst (weilIdeleMeasure Fq k) = 1 := by
  have h2 : (0 : ℝ) < Nat.card (ClassGroup0 Fq k) := by exact_mod_cast classNumber_pos
  have hreal : (weilIdeleMeasure Fq k).real integralUnits =
      ((Nat.card Fq : ℝ) - 1) / Nat.card (ClassGroup0 Fq k) := by
    rw [Measure.real, weilIdeleMeasure, Measure.smul_apply, haarU_integralUnits, smul_eq_mul, mul_one,
      ENNReal.toReal_ofReal weilIdeleMeasure_coeff_pos.le]
  rw [zetaConst, hreal]
  have hq1 : (Nat.card Fq : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (show Nat.card Fq ≠ 1 from (Finite.one_lt_card).ne')
  have hh : (Nat.card (ClassGroup0 Fq k) : ℂ) ≠ 0 := by exact_mod_cast classNumber_pos.ne'
  push_cast
  field_simp

/-- **Weil VII.§5 Cor. 7.** Let $k$ be a function field with field of constants $\mathbb F_q$, $\mu$ Weil's Haar
measure on $k_{\mathbb A}^\times$, and $\Phi$ a Schwartz–Bruhat function on $k_{\mathbb A}$. Then the continuation of
$Z(\omega_s,\Phi)$ satisfies: $Z(\omega_s,\Phi)+\Phi(0)(1-q^{-s})^{-1}$ is holomorphic at $s=0$. -/
@[kb "weil1973bnt" "Ch. VII, §5, Cor. 7 (p. 127): Z(ω_s, Φ) + Φ(0)(1 - q^(-s))^(-1) is holomorphic at s = 0"]
theorem weil_VII_5_cor7 (hc : IsConstantField Fq k) {Φ : FFAdeleRing Fq k → ℂ}
    (hΦ : FFAdeleRing.IsSchwartzBruhat Φ) :
    ∃ Zc : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re → zetaIntegral (weilIdeleMeasure Fq k) Φ s = Zc s) ∧
      MeromorphicOn Zc Set.univ ∧
      AnalyticAt ℂ (fun s => Zc s + Φ 0 * (1 - (Nat.card Fq : ℂ) ^ (-s))⁻¹) 0 := by
  obtain ⟨Zc, h1, h2, -, h4⟩ := weil_VII_5_thm2_ff hc (weilIdeleMeasure Fq k) hΦ
  refine ⟨Zc, fun s hs => (h1 s hs).2, h2, ?_⟩
  rw [zetaConst_weilIdeleMeasure, one_mul] at h4
  exact h4

end FFIdeleGroup

end

end NumberFieldKB.WeilBNT.FF
