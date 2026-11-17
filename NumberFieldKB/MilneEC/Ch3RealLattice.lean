import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch3Curve

/-!
# Lattices with real invariants and the real half-period

For a lattice $\Lambda$ (Mathlib's `PeriodPair`) whose invariants $g_2(\Lambda), g_3(\Lambda)$ are real:

* `conj_mem_lattice`: $\bar\Lambda = \Lambda$ (by the rigidity `lattice_eq_of_g_eq` of Chapter III), so
  `weierstrassP_conj`: $\wp(\bar z) = \overline{\wp(z)}$, and likewise $\wp'$;
* `leastRealPeriod_spec`: $\Lambda \cap \mathbb R = \mathbb Z\,\omega_{\mathbb R}$ with $\omega_{\mathbb R} > 0$,
  `leastRealPeriod`;
* `derivWeierstrassP_eq_zero_iff`: for $z \notin \Lambda$, $\wp'(z) = 0$ iff $2z \in \Lambda$ (the points of order 2
  of $E(\Lambda)$, through the isomorphism $\mathbb C/\Lambda \cong E(\Lambda)(\mathbb C)$ of Proposition 3.7 and
  Corollary 3.9);
* `halfPeriod_integral`: with $F(x) = 4x^3 - g_2x - g_3$ and $e = \wp(\omega_{\mathbb R}/2) \in \mathbb R$: $F(e) = 0$,
  $F > 0$ on $(e, \infty)$, and $\int_e^\infty dx/\sqrt{F(x)} = \omega_{\mathbb R}/2$. The substitution is
  $x = \wp(t)$, $t \in (0, \omega_{\mathbb R}/2)$: $\wp$ is real there, $\wp'(t)^2 = F(\wp(t))$, $\wp'$ has no zero
  on $(0, \omega_{\mathbb R}/2)$, and $\wp(t) \to +\infty$ as $t \to 0^+$, so $\wp$ decreases from $+\infty$ to $e$
  and $dx/\sqrt{F(x)} = -dt$.
-/

open Complex Set MeasureTheory

namespace NumberFieldKB.MilneEC.III

/-- The lattice of `L` has **real invariants**: $g_2(\Lambda), g_3(\Lambda) \in \mathbb R$. -/
def HasRealInvariants (L : PeriodPair) : Prop := L.g₂.im = 0 ∧ L.g₃.im = 0

/-- The real cubic $F(x) = 4x^3 - g_2x - g_3$ of a lattice (real parts of the invariants). -/
noncomputable def realCubic (L : PeriodPair) (x : ℝ) : ℝ := 4 * x ^ 3 - L.g₂.re * x - L.g₃.re

/-- The least positive real period $\omega_{\mathbb R}$ of the lattice ($0$ if there is none). -/
noncomputable def leastRealPeriod (L : PeriodPair) : ℝ := sInf {t : ℝ | 0 < t ∧ (t : ℂ) ∈ L.lattice}

variable {L : PeriodPair}

/-- The pair with conjugated periods. -/
noncomputable def conjPair (L : PeriodPair) : PeriodPair where
  ω₁ := starRingEnd ℂ L.ω₁
  ω₂ := starRingEnd ℂ L.ω₂
  indep := by
    have := L.indep.map' (Complex.conjLIE.toLinearEquiv.toLinearMap)
      (LinearEquiv.ker _)
    convert this using 1
    ext i
    fin_cases i <;> simp

lemma conj_mem_conjPair {z : ℂ} (hz : z ∈ L.lattice) :
    (starRingEnd ℂ) z ∈ (conjPair L).lattice := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hz
  exact PeriodPair.mem_lattice.2 ⟨m, n, by simp [conjPair]⟩

lemma mem_conjPair_lattice {z : ℂ} :
    z ∈ (conjPair L).lattice ↔ (starRingEnd ℂ) z ∈ L.lattice := by
  constructor
  · intro hz
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hz
    exact PeriodPair.mem_lattice.2 ⟨m, n, by simp [conjPair]⟩
  · intro hz
    simpa using conj_mem_conjPair hz

lemma conjPair_G (k : ℕ) : (conjPair L).G k = (starRingEnd ℂ) (L.G k) := by
  let e : L.lattice ≃ (conjPair L).lattice :=
    { toFun := fun l => ⟨(starRingEnd ℂ) l, conj_mem_conjPair l.2⟩
      invFun := fun l => ⟨(starRingEnd ℂ) l, mem_conjPair_lattice.1 l.2⟩
      left_inv := fun l => Subtype.ext (by simp)
      right_inv := fun l => Subtype.ext (by simp) }
  have := e.tsum_eq (fun l : (conjPair L).lattice => (((l : ℂ)) ^ k)⁻¹)
  rw [PeriodPair.G, PeriodPair.G, Complex.conj_tsum, ← this]
  congr with l
  simp [e]

/-- A lattice with real invariants is stable under complex conjugation. -/
theorem conj_mem_lattice (h : HasRealInvariants L) {z : ℂ} (hz : z ∈ L.lattice) :
    (starRingEnd ℂ) z ∈ L.lattice := by
  have h2 : (conjPair L).g₂ = L.g₂ := by
    rw [PeriodPair.g₂, PeriodPair.g₂, conjPair_G]
    have : (starRingEnd ℂ) L.g₂ = L.g₂ := Complex.conj_eq_iff_im.2 h.1
    rw [PeriodPair.g₂, map_mul, map_ofNat] at this
    exact this
  have h3 : (conjPair L).g₃ = L.g₃ := by
    rw [PeriodPair.g₃, PeriodPair.g₃, conjPair_G]
    have : (starRingEnd ℂ) L.g₃ = L.g₃ := Complex.conj_eq_iff_im.2 h.2
    rw [PeriodPair.g₃, map_mul, map_ofNat] at this
    exact this
  have := CurveAux.lattice_eq_of_g_eq h2 h3
  exact mem_conjPair_lattice.1 (this ▸ hz)

/-- Conjugation as an involution of the lattice. -/
noncomputable def conjEquiv (h : HasRealInvariants L) : L.lattice ≃ L.lattice where
  toFun l := ⟨(starRingEnd ℂ) l, conj_mem_lattice h l.2⟩
  invFun l := ⟨(starRingEnd ℂ) l, conj_mem_lattice h l.2⟩
  left_inv l := Subtype.ext (by simp)
  right_inv l := Subtype.ext (by simp)

/-- $\wp(\bar z) = \overline{\wp(z)}$ for a lattice with real invariants. -/
theorem weierstrassP_conj (h : HasRealInvariants L) (z : ℂ) :
    L.weierstrassP ((starRingEnd ℂ) z) = (starRingEnd ℂ) (L.weierstrassP z) := by
  have := (conjEquiv h).tsum_eq
    (fun l : L.lattice => 1 / ((starRingEnd ℂ) z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP, Complex.conj_tsum, ← this]
  congr with l
  simp [conjEquiv]

/-- $\wp'(\bar z) = \overline{\wp'(z)}$ for a lattice with real invariants. -/
theorem derivWeierstrassP_conj (h : HasRealInvariants L) (z : ℂ) :
    L.derivWeierstrassP ((starRingEnd ℂ) z) = (starRingEnd ℂ) (L.derivWeierstrassP z) := by
  have := (conjEquiv h).tsum_eq
    (fun l : L.lattice => 2 / ((starRingEnd ℂ) z - (l : ℂ)) ^ 3)
  rw [PeriodPair.derivWeierstrassP, PeriodPair.derivWeierstrassP, map_neg, Complex.conj_tsum,
    ← this]
  congr 1
  congr with l
  simp [conjEquiv, map_ofNat (starRingEnd ℂ) 2]

/-- The real elements of the lattice, as an additive subgroup of `ℝ`. -/
def realPeriods (L : PeriodPair) : AddSubgroup ℝ where
  carrier := {t | (t : ℂ) ∈ L.lattice}
  add_mem' := fun {a b} ha hb => by
    have := L.lattice.add_mem (show (a : ℂ) ∈ L.lattice from ha) (show (b : ℂ) ∈ L.lattice from hb)
    simpa using this
  zero_mem' := by
    show ((0 : ℝ) : ℂ) ∈ L.lattice
    simp
  neg_mem' := fun {a} ha => by
    have := L.lattice.neg_mem (show (a : ℂ) ∈ L.lattice from ha)
    simpa using this

lemma exists_re_ne_zero (L : PeriodPair) : ∃ ω ∈ L.lattice, ω.re ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 := hcon _ L.ω₁_mem_lattice
  have h2 := hcon _ L.ω₂_mem_lattice
  have key := LinearIndependent.pair_iff.1 L.indep L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext <;> simp [h1, h2]; ring)
  have key2 := LinearIndependent.pair_iff.1 L.indep 1 0 (by
    apply Complex.ext
    · simp [h1]
    · simp
      linarith [key.2])
  exact one_ne_zero key2.1

lemma exists_pos_real_period (h : HasRealInvariants L) : ∃ t : ℝ, 0 < t ∧ (t : ℂ) ∈ L.lattice := by
  obtain ⟨ω, hω, hre⟩ := exists_re_ne_zero L
  have hmem : ((2 * ω.re : ℝ) : ℂ) ∈ L.lattice := by
    have := L.lattice.add_mem hω (conj_mem_lattice h hω)
    convert this using 1
    apply Complex.ext <;> simp [two_mul]
  rcases lt_or_gt_of_ne (mul_ne_zero two_ne_zero hre) with hlt | hgt
  · exact ⟨-(2 * ω.re), by linarith, by simpa using L.lattice.neg_mem hmem⟩
  · exact ⟨_, hgt, hmem⟩

lemma realPeriods_structure (h : HasRealInvariants L) :
    ∃ a : ℝ, 0 < a ∧ (a : ℂ) ∈ L.lattice ∧
      ∀ t : ℝ, (t : ℂ) ∈ L.lattice → ∃ n : ℤ, t = n * a := by
  obtain ⟨t₀, ht₀, ht₀m⟩ := exists_pos_real_period h
  have hnd : ¬ Dense (realPeriods L : Set ℝ) := by
    intro hd
    have hcl : IsClosed {t : ℝ | (t : ℂ) ∈ L.lattice} :=
      L.isClosed_lattice.preimage Complex.continuous_ofReal
    have hall : ∀ t : ℝ, (t : ℂ) ∈ L.lattice := by
      intro t
      have : t ∈ closure (realPeriods L : Set ℝ) := hd.closure_eq ▸ Set.mem_univ t
      exact hcl.closure_subset_iff.2 (fun x hx => hx) this
    have hc : (Complex.ofReal ⁻¹' (L.lattice : Set ℂ)).Countable :=
      (CurveAux.lattice_countable L).preimage Complex.ofReal_injective
    have : Complex.ofReal ⁻¹' (L.lattice : Set ℂ) = Set.univ := by
      ext t; simp [hall t]
    rw [this] at hc
    exact Cardinal.not_countable_real hc
  rcases AddSubgroup.dense_or_isCyclic (realPeriods L) with hd | hc
  · exact absurd hd hnd
  obtain ⟨g, hg⟩ := hc.exists_generator
  have hrep : ∀ t : ℝ, (t : ℂ) ∈ L.lattice → ∃ n : ℤ, t = n * g.1 := by
    intro t ht
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (hg ⟨t, ht⟩)
    refine ⟨n, ?_⟩
    have := congrArg Subtype.val hn
    simpa using this.symm
  have hg0 : g.1 ≠ 0 := by
    obtain ⟨n, hn⟩ := hrep t₀ ht₀m
    intro h0
    rw [h0, mul_zero] at hn
    exact ht₀.ne' hn
  have hgm : (g.1 : ℂ) ∈ L.lattice := g.2
  have habs : ((|g.1| : ℝ) : ℂ) ∈ L.lattice := by
    rcases abs_cases g.1 with ⟨e, _⟩ | ⟨e, _⟩
    · rw [e]; exact hgm
    · rw [e]; simpa using L.lattice.neg_mem hgm
  refine ⟨|g.1|, abs_pos.2 hg0, habs, fun t ht => ?_⟩
  obtain ⟨n, hn⟩ := hrep t ht
  rcases abs_cases g.1 with ⟨e, _⟩ | ⟨e, _⟩
  · exact ⟨n, by rw [hn, e]⟩
  · exact ⟨-n, by rw [hn, e]; push_cast; ring⟩

/-- $\Lambda \cap \mathbb R = \mathbb Z\,\omega_{\mathbb R}$ with $\omega_{\mathbb R} > 0$, for a lattice with real
invariants. -/
theorem leastRealPeriod_spec (h : HasRealInvariants L) :
    0 < leastRealPeriod L ∧ ((leastRealPeriod L : ℝ) : ℂ) ∈ L.lattice ∧
      ∀ t : ℝ, (t : ℂ) ∈ L.lattice → ∃ n : ℤ, t = n * leastRealPeriod L := by
  obtain ⟨a, ha0, haH, hall⟩ := realPeriods_structure h
  have hleast : IsLeast {t : ℝ | 0 < t ∧ (t : ℂ) ∈ L.lattice} a := by
    refine ⟨⟨ha0, haH⟩, fun t ⟨ht0, htm⟩ => ?_⟩
    obtain ⟨n, rfl⟩ := hall t htm
    have hn : 0 < n := by
      by_contra hn
      push Not at hn
      have : (n : ℝ) ≤ 0 := by exact_mod_cast hn
      nlinarith
    have hn1 : (1 : ℤ) ≤ n := hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  have heq : leastRealPeriod L = a := hleast.csInf_eq
  rw [heq]
  exact ⟨ha0, haH, hall⟩

/-- The zeros of $\wp'$ off $\Lambda$ are the half-periods: $\wp'(z) = 0 \iff 2z \in \Lambda$ ($z \notin \Lambda$). -/
theorem derivWeierstrassP_eq_zero_iff {z : ℂ} (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z = 0 ↔ 2 * z ∈ L.lattice := by
  constructor
  · intro h0
    have := (Submodule.Quotient.eq _).1 (CurveAux.mk_neg_eq_of_dwp_zero L hz h0)
    simpa [two_mul, sub_neg_eq_add] using this
  · intro h2
    apply CurveAux.dwp_eq_zero_of_mk_neg L
    rw [Submodule.Quotient.eq]
    simpa [two_mul, sub_neg_eq_add] using h2

open Filter Topology

lemma real_notMem_lattice (h : HasRealInvariants L) {t : ℝ} (ht0 : 0 < t)
    (ht : t < leastRealPeriod L) : (t : ℂ) ∉ L.lattice := by
  intro hm
  obtain ⟨hω0, -, hall⟩ := leastRealPeriod_spec h
  obtain ⟨n, hn⟩ := hall t hm
  have hn0 : 0 < n := by
    by_contra hn'
    push Not at hn'
    have : (n : ℝ) ≤ 0 := by exact_mod_cast hn'
    nlinarith
  have hn1 : (1 : ℤ) ≤ n := hn0
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  nlinarith

lemma wp_real (h : HasRealInvariants L) (t : ℝ) :
    L.weierstrassP (t : ℂ) = ((L.weierstrassP (t : ℂ)).re : ℂ) := by
  have := weierstrassP_conj h (t : ℂ)
  rw [Complex.conj_ofReal] at this
  exact (Complex.conj_eq_iff_re.1 this.symm).symm

lemma dwp_real (h : HasRealInvariants L) (t : ℝ) :
    L.derivWeierstrassP (t : ℂ) = ((L.derivWeierstrassP (t : ℂ)).re : ℂ) := by
  have := derivWeierstrassP_conj h (t : ℂ)
  rw [Complex.conj_ofReal] at this
  exact (Complex.conj_eq_iff_re.1 this.symm).symm

lemma hasDerivAt_wp_re {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    HasDerivAt (fun x : ℝ => (L.weierstrassP (x : ℂ)).re) (L.derivWeierstrassP (t : ℂ)).re t := by
  have h1 : DifferentiableAt ℂ L.weierstrassP (t : ℂ) :=
    L.differentiableOn_weierstrassP.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds ht)
  have h2 := h1.hasDerivAt
  rw [L.deriv_weierstrassP] at h2
  exact h2.real_of_complex

lemma continuousAt_dwp_re {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    ContinuousAt (fun x : ℝ => (L.derivWeierstrassP (x : ℂ)).re) t := by
  have h1 : DifferentiableAt ℂ L.derivWeierstrassP (t : ℂ) :=
    L.differentiableOn_derivWeierstrassP.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds ht)
  exact Complex.continuous_re.continuousAt.comp
    (h1.continuousAt.comp Complex.continuous_ofReal.continuousAt)

lemma dwp_re_sq (h : HasRealInvariants L) {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    (L.derivWeierstrassP (t : ℂ)).re ^ 2 = realCubic L (L.weierstrassP (t : ℂ)).re := by
  apply Complex.ofReal_injective
  have hg2 : (L.g₂.re : ℂ) = L.g₂ := Complex.ext (by simp) (by simp [h.1])
  have hg3 : (L.g₃.re : ℂ) = L.g₃ := Complex.ext (by simp) (by simp [h.2])
  unfold realCubic
  push_cast
  rw [← dwp_real h, ← wp_real h, hg2, hg3]
  exact L.derivWeierstrassP_sq _ ht

lemma tendsto_wp_re_zero :
    Tendsto (fun x : ℝ => (L.weierstrassP (x : ℂ)).re) (𝓝[>] 0) atTop := by
  have hc : ContinuousAt (fun x : ℝ => (L.weierstrassPExcept 0 (x : ℂ)).re) 0 := by
    have h0 : ContinuousAt (L.weierstrassPExcept 0) ((0 : ℝ) : ℂ) := by
      simpa using (L.analyticAt_weierstrassPExcept 0).continuousAt
    exact Complex.continuous_re.continuousAt.comp
      (h0.comp Complex.continuous_ofReal.continuousAt)
  have h1 : Tendsto (fun x : ℝ => (x ^ 2)⁻¹) (𝓝[>] 0) atTop := by
    have := (tendsto_pow_atTop (α := ℝ) (n := 2) two_ne_zero).comp tendsto_inv_nhdsGT_zero
    simpa [Function.comp_def, inv_pow] using this
  have h2 := h1.atTop_add (hc.tendsto.mono_left nhdsWithin_le_nhds)
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  have := L.weierstrassPExcept_add ⟨0, L.lattice.zero_mem⟩ (x : ℂ)
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at this
  have h3 := congrArg Complex.re this.symm
  rw [Complex.add_re] at h3
  rw [h3, add_comm]
  congr 1
  have : (1 : ℂ) / (x : ℂ) ^ 2 = (((x ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; simp
  rw [this, Complex.ofReal_re]

/-- **The real half-period integral.** For a lattice with real invariants, $e = \wp(\omega_{\mathbb R}/2)$ is real,
$F(e) = 0$, $F > 0$ on $(e, \infty)$, $1/\sqrt F$ is integrable on $(e, \infty)$ and
$\int_e^\infty dx/\sqrt{F(x)} = \omega_{\mathbb R}/2$, where $F(x) = 4x^3 - g_2x - g_3$. -/
theorem halfPeriod_integral (h : HasRealInvariants L) :
    ∃ e : ℝ, (e : ℂ) = L.weierstrassP ((leastRealPeriod L / 2 : ℝ) : ℂ) ∧ realCubic L e = 0 ∧
      (∀ x, e < x → 0 < realCubic L x) ∧
      IntegrableOn (fun x => (√(realCubic L x))⁻¹) (Ioi e) ∧
      ∫ x in Ioi e, (√(realCubic L x))⁻¹ = leastRealPeriod L / 2 := by
  obtain ⟨hω0, hωm, -⟩ := leastRealPeriod_spec h
  set ω := leastRealPeriod L with hω
  set hh : ℝ := ω / 2 with hhh
  have hh0 : 0 < hh := by positivity
  have hhω : hh < ω := by linarith
  have hnot : ∀ t : ℝ, 0 < t → t < ω → (t : ℂ) ∉ L.lattice := fun t h0 h1 =>
    real_notMem_lattice h h0 h1
  set f : ℝ → ℝ := fun x => (L.weierstrassP (x : ℂ)).re with hf
  set f' : ℝ → ℝ := fun x => (L.derivWeierstrassP (x : ℂ)).re with hf'
  have hder : ∀ t ∈ Ioc 0 hh, HasDerivAt f (f' t) t := fun t ht =>
    hasDerivAt_wp_re (hnot t ht.1 (lt_of_le_of_lt ht.2 hhω))
  have hcont : ContinuousOn f (Ioc 0 hh) := fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hsq : ∀ t ∈ Ioc 0 hh, f' t ^ 2 = realCubic L (f t) := fun t ht =>
    dwp_re_sq h (hnot t ht.1 (lt_of_le_of_lt ht.2 hhω))
  have hne : ∀ t ∈ Ioo 0 hh, f' t ≠ 0 := by
    intro t ht h0
    have ht' : (t : ℂ) ∉ L.lattice := hnot t ht.1 (by linarith [ht.2])
    have : L.derivWeierstrassP (t : ℂ) = 0 := by
      rw [dwp_real h, show (L.derivWeierstrassP (t : ℂ)).re = 0 from h0]; simp
    have h2 := (derivWeierstrassP_eq_zero_iff ht').1 this
    have h3 : ((2 * t : ℝ) : ℂ) ∈ L.lattice := by simpa using h2
    exact hnot (2 * t) (by linarith [ht.1]) (by linarith [ht.2]) h3
  have hcont' : ContinuousOn f' (Ioo 0 hh) := fun t ht =>
    (continuousAt_dwp_re (hnot t ht.1 (by linarith [ht.2]))).continuousWithinAt
  -- sign of f'
  have hneg : ∀ t ∈ Ioo 0 hh, f' t < 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht₁, ht₁'⟩ := hcon
    have hpos1 : 0 < f' t₁ := lt_of_le_of_ne ht₁' (hne t₁ ht₁).symm
    have hallpos : ∀ t ∈ Ioo 0 hh, 0 < f' t := by
      intro t ht
      by_contra hn
      have hlt : f' t < 0 := lt_of_le_of_ne (not_lt.1 hn) (hne t ht)
      have hconn : IsPreconnected (f' '' Ioo 0 hh) := isPreconnected_Ioo.image _ hcont'
      obtain ⟨s, hs, hs0⟩ := hconn.Icc_subset ⟨t, ht, rfl⟩ ⟨t₁, ht₁, rfl⟩ ⟨hlt.le, hpos1.le⟩
      exact hne s hs hs0
    have hmono : StrictMonoOn f (Ioo 0 hh) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioo 0 hh) ?_ ?_
      · exact hcont.mono Ioo_subset_Ioc_self
      · intro x hx
        rw [interior_Ioo] at hx
        rw [(hder x (Ioo_subset_Ioc_self hx)).deriv]
        exact hallpos x hx
    have hev := (tendsto_wp_re_zero (L := L)).eventually (eventually_gt_atTop (f (hh / 2)))
    obtain ⟨δ, hδ, hδ'⟩ := (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < hh / 2 by linarith))).exists
    have := hmono ⟨hδ'.1, by linarith [hδ'.2]⟩ ⟨by linarith, by linarith⟩ hδ'.2
    exact absurd hδ (not_lt.2 this.le)
  have hanti : StrictAntiOn f (Ioc 0 hh) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioc 0 hh) hcont ?_
    intro x hx
    rw [interior_Ioc] at hx
    rw [(hder x (Ioo_subset_Ioc_self hx)).deriv]
    exact hneg x hx
  set e : ℝ := f hh with he
  have himg : f '' Ioo 0 hh = Ioi e := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact hanti ⟨ht.1, ht.2.le⟩ ⟨hh0, le_rfl⟩ ht.2
    · intro hy
      have hy' : e < y := hy
      have hev := (tendsto_wp_re_zero (L := L)).eventually (eventually_gt_atTop y)
      obtain ⟨δ, hδ, hδ'⟩ := (hev.and (Ioo_mem_nhdsGT hh0)).exists
      have hsub : ∀ x ∈ Icc δ hh, x ∈ Ioc 0 hh := fun x hx => ⟨by linarith [hδ'.1, hx.1], hx.2⟩
      obtain ⟨t, ht, hty⟩ := intermediate_value_Ioo' hδ'.2.le (hcont.mono hsub)
        (show y ∈ Ioo (f hh) (f δ) from ⟨hy', hδ⟩)
      exact ⟨t, ⟨by linarith [hδ'.1, ht.1], ht.2⟩, hty⟩
  -- e is real and a root
  have hwhh : (hh : ℂ) ∉ L.lattice := hnot hh hh0 hhω
  have hd0 : f' hh = 0 := by
    have : L.derivWeierstrassP (hh : ℂ) = 0 := by
      rw [derivWeierstrassP_eq_zero_iff hwhh]
      have : (2 : ℂ) * (hh : ℂ) = (ω : ℂ) := by simp [hhh]; ring
      rw [this]; exact hωm
    simp [hf', this]
  have hroot : realCubic L e = 0 := by
    rw [he, ← hsq hh ⟨hh0, le_rfl⟩, hd0]; simp
  have hpos : ∀ x, e < x → 0 < realCubic L x := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ : x ∈ f '' Ioo 0 hh := by rw [himg]; exact hx
    rw [← hsq t (Ioo_subset_Ioc_self ht)]
    have := hne t ht
    positivity
  have hkey : ∀ t ∈ Ioo 0 hh, |f' t| • (√(realCubic L (f t)))⁻¹ = 1 := by
    intro t ht
    rw [← hsq t (Ioo_subset_Ioc_self ht), Real.sqrt_sq_eq_abs, smul_eq_mul]
    exact mul_inv_cancel₀ (abs_ne_zero.2 (hne t ht))
  have hdw : ∀ x ∈ Ioo 0 hh, HasDerivWithinAt f (f' x) (Ioo 0 hh) x := fun x hx =>
    (hder x (Ioo_subset_Ioc_self hx)).hasDerivWithinAt
  have hinj : InjOn f (Ioo 0 hh) := hanti.injOn.mono Ioo_subset_Ioc_self
  refine ⟨e, ?_, hroot, hpos, ?_, ?_⟩
  · exact (wp_real h hh).symm
  · rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hdw hinj]
    refine (integrableOn_const (by simp)).congr_fun (fun t ht => (hkey t ht).symm) measurableSet_Ioo
  · rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hdw hinj,
      setIntegral_congr_fun measurableSet_Ioo hkey]
    simp [Measure.real, hhh]
    linarith

end NumberFieldKB.MilneEC.III
