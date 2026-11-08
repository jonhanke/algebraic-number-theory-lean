import NumberFieldKB.ModularCurves.FunctionField

/-!
# Milne, *Elliptic Curves*, Ch. V, Theorem 2.3: the meromorphic functions on $X_0(N)$ are $\mathbb C(j, j_N)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Theorem 2.3 (pdf p. 192). Milne's proof: for a modular
function $f$ for $\Gamma_0(N)$, the polynomial
$$G_z(Y) = \sum_{\gamma\Gamma_0(N)} f(\gamma^{-1}z) \prod_{\gamma'\Gamma_0(N) \ne \gamma\Gamma_0(N)} \bigl(Y - j_N(\gamma'^{-1}z)\bigr)$$
has $\mathrm{SL}_2(\mathbb Z)$-invariant coefficients, which are modular functions for $\Gamma_0(1)$, hence rational
functions of $j$ (Proposition 2.2, `prop2_2Rational`); at $Y = j_N(z)$ only the term of the trivial coset survives,
so $f = G(j, j_N)/\partial_Y F_N(j, j_N)$.

The coefficients are polynomials in the functions $f \circ \gamma^{-1}$ and $j_N \circ \gamma^{-1}$, each meromorphic at
$i\infty$ but for its own period. Meromorphy at a cusp with a given period is not obviously closed under sums, so we
use a period-free notion, `IsModerate`: holomorphic high in $\mathbb H$ with at most exponential growth. It is closed
under sums and products (`goodSubalgebra`), it follows from meromorphy at $i\infty$
(`isModerate_of_isMeromorphicAtImInfty`), and for $1$-periodic functions it gives meromorphy at $i\infty$ back
(`isMeromorphicAtImInfty_of_isModerate`, Riemann's removable singularity theorem).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex Topology
open scoped Manifold MatrixGroups Real

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-! ### Moderate growth at $i\infty$ -/

/-- $g$ is holomorphic on $\{\operatorname{Im} z \ge A\}$ and $|g(z)| \le C e^{B \operatorname{Im} z}$ there. -/
def IsModerate (g : ℍ → ℂ) : Prop :=
  ∃ A B C : ℝ, 0 ≤ C ∧ ∀ z : ℍ, A ≤ z.im → MDiffAt g z ∧ ‖g z‖ ≤ C * Real.exp (B * z.im)

namespace IsModerate

theorem const (c : ℂ) : IsModerate (fun _ => c) :=
  ⟨0, 0, ‖c‖, norm_nonneg _, fun _ _ => ⟨mdifferentiableAt_const, by simp⟩⟩

theorem add {f g : ℍ → ℂ} (hf : IsModerate f) (hg : IsModerate g) : IsModerate (f + g) := by
  obtain ⟨A1, B1, C1, hC1, h1⟩ := hf
  obtain ⟨A2, B2, C2, hC2, h2⟩ := hg
  refine ⟨max A1 A2, max B1 B2, C1 + C2, by positivity, fun z hz => ?_⟩
  obtain ⟨d1, b1⟩ := h1 z (le_trans (le_max_left _ _) hz)
  obtain ⟨d2, b2⟩ := h2 z (le_trans (le_max_right _ _) hz)
  refine ⟨d1.add d2, ?_⟩
  have hy := z.im_pos
  have e1 : Real.exp (B1 * z.im) ≤ Real.exp (max B1 B2 * z.im) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hy.le)
  have e2 : Real.exp (B2 * z.im) ≤ Real.exp (max B1 B2 * z.im) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hy.le)
  calc ‖(f + g) z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C1 * Real.exp (B1 * z.im) + C2 * Real.exp (B2 * z.im) := add_le_add b1 b2
    _ ≤ (C1 + C2) * Real.exp (max B1 B2 * z.im) := by
        nlinarith [mul_le_mul_of_nonneg_left e1 hC1, mul_le_mul_of_nonneg_left e2 hC2]

theorem mul {f g : ℍ → ℂ} (hf : IsModerate f) (hg : IsModerate g) : IsModerate (f * g) := by
  obtain ⟨A1, B1, C1, hC1, h1⟩ := hf
  obtain ⟨A2, B2, C2, hC2, h2⟩ := hg
  refine ⟨max A1 A2, B1 + B2, C1 * C2, by positivity, fun z hz => ?_⟩
  obtain ⟨d1, b1⟩ := h1 z (le_trans (le_max_left _ _) hz)
  obtain ⟨d2, b2⟩ := h2 z (le_trans (le_max_right _ _) hz)
  refine ⟨d1.mul d2, ?_⟩
  calc ‖(f * g) z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C1 * Real.exp (B1 * z.im)) * (C2 * Real.exp (B2 * z.im)) :=
        mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
    _ = C1 * C2 * Real.exp ((B1 + B2) * z.im) := by
        rw [add_mul, Real.exp_add]; ring

end IsModerate

/-- The functions on $\mathbb H$ that are meromorphic on $\mathbb H$ and of moderate growth at $i\infty$: a
$\mathbb C$-subalgebra of the functions on $\mathbb H$. -/
def goodSubalgebra : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {g | IsMeromorphicOnUpperHalfPlane g ∧ IsModerate g}
  mul_mem' hf hg := ⟨hf.1.mul hg.1, hf.2.mul hg.2⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  algebraMap_mem' c := ⟨MeromorphicOn.const c, IsModerate.const c⟩

/-- Meromorphy at $i\infty$ (for some period) implies moderate growth. -/
theorem isModerate_of_isMeromorphicAtImInfty {g : ℍ → ℂ} (hg : IsMeromorphicAtImInfty g) :
    IsModerate g := by
  obtain ⟨h, hh, hper, hm⟩ := hg
  set G := cuspFunction h g with hGdef
  have hev := eventually_nhdsWithin_iff.mp hm.eventually_analyticAt
  obtain ⟨n, hn⟩ := hm
  set H : ℂ → ℂ := fun q => (q - 0) ^ n • G q with hH
  have hbd : ∀ᶠ q in 𝓝 (0 : ℂ), ‖H q‖ < ‖H 0‖ + 1 :=
    Filter.Tendsto.eventually_lt_const (lt_add_one ‖H 0‖) hn.continuousAt.tendsto.norm
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hbd)
  have hq : ∀ᶠ z : ℍ in atImInfty, ‖Function.Periodic.qParam h (z : ℂ)‖ < ε := by
    have := (UpperHalfPlane.qParam_tendsto_atImInfty (h := h) hh)
    have := this.eventually (Metric.ball_mem_nhds 0 hε)
    simpa using this
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hq
  refine ⟨A, 2 * π * n / h, ‖H 0‖ + 1, by positivity, fun z hz => ?_⟩
  have hqz := hA z hz
  have hq0 : Function.Periodic.qParam h (z : ℂ) ≠ 0 := by simp [Function.Periodic.qParam]
  obtain ⟨han, hHb⟩ := hball (by simpa [dist_eq_norm] using hqz)
  have han' := han hq0
  have hgz : g = fun w : ℍ => G (Function.Periodic.qParam h (w : ℂ)) :=
    funext fun w => (UpperHalfPlane.eq_cuspFunction w hh.ne' hper).symm
  constructor
  · rw [hgz]
    have hq' : MDiffAt (fun w : ℍ => Function.Periodic.qParam h (w : ℂ)) z :=
      (Function.Periodic.differentiable_qParam (h := h) (z : ℂ)).comp_mdifferentiableAt
        (UpperHalfPlane.mdifferentiable_coe z)
    exact DifferentiableAt.comp_mdifferentiableAt
      (f := fun w : ℍ => Function.Periodic.qParam h (w : ℂ)) han'.differentiableAt hq'
  · have hgq : g z = G (Function.Periodic.qParam h (z : ℂ)) := congrFun hgz z
    have hnq : ‖Function.Periodic.qParam h (z : ℂ)‖ = Real.exp (-2 * π * z.im / h) := by
      rw [Function.Periodic.norm_qParam]; rfl
    have hHq : ‖H (Function.Periodic.qParam h (z : ℂ))‖ =
        Real.exp (-2 * π * z.im / h) ^ n * ‖G (Function.Periodic.qParam h (z : ℂ))‖ := by
      simp only [hH, sub_zero, smul_eq_mul, norm_mul, norm_pow, hnq]
    rw [hHq] at hHb
    have hpos : 0 < Real.exp (-2 * π * z.im / h) ^ n := by positivity
    have hinv : Real.exp (2 * π * n / h * z.im) * Real.exp (-2 * π * z.im / h) ^ n = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      have : 2 * π * n / h * z.im + n * (-2 * π * z.im / h) = 0 := by ring
      rw [this, Real.exp_zero]
    rw [hgq]
    have hle : ‖G (Function.Periodic.qParam h (z : ℂ))‖ * Real.exp (-2 * π * z.im / h) ^ n
        ≤ (‖H 0‖ + 1) := by linarith
    calc ‖G (Function.Periodic.qParam h (z : ℂ))‖
        = ‖G (Function.Periodic.qParam h (z : ℂ))‖ * Real.exp (-2 * π * z.im / h) ^ n *
            Real.exp (2 * π * n / h * z.im) := by
          rw [mul_assoc, mul_comm (Real.exp (-2 * π * z.im / h) ^ n), hinv, mul_one]
      _ ≤ (‖H 0‖ + 1) * Real.exp (2 * π * n / h * z.im) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le

/-- A $1$-periodic function of moderate growth is meromorphic at $i\infty$ (Riemann's removable singularity
theorem applied to $q^M g$). -/
theorem isMeromorphicAtImInfty_of_isModerate {g : ℍ → ℂ} (hper : Function.Periodic (g ∘ ofComplex) 1)
    (hg : IsModerate g) : IsMeromorphicAtImInfty g := by
  obtain ⟨A, B, C, hC, hb⟩ := hg
  refine ⟨1, one_pos, hper, ?_⟩
  set G := cuspFunction 1 g with hGdef
  set M : ℕ := ⌈B / (2 * π)⌉₊ with hM
  set A' := max A 1 with hA'
  set r := Real.exp (-2 * π * A') with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hA'1 : 1 ≤ A' := le_max_right _ _
  set F : ℂ → ℂ := fun q => q ^ M * G q with hF
  -- on the punctured disc, `q = 𝕢 (invQParam q)` with `Im (invQParam q) > A'`
  have him : ∀ q : ℂ, q ≠ 0 → ‖q‖ < r → A' < (Function.Periodic.invQParam 1 q).im := by
    intro q hq0 hqr
    rw [Function.Periodic.im_invQParam]
    have hlog : Real.log ‖q‖ < -2 * π * A' := by
      rw [← Real.log_exp (-2 * π * A')]
      exact Real.log_lt_log (norm_pos_iff.2 hq0) hqr
    have hpi := Real.pi_pos
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith
  have hGq : ∀ q : ℂ, q ≠ 0 → G q = g (ofComplex (Function.Periodic.invQParam 1 q)) := by
    intro q hq0
    rw [hGdef, UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
    rfl
  have hdiff : DifferentiableOn ℂ F (Metric.ball 0 r \ {0}) := by
    rintro q ⟨hqr, hq0⟩
    have hq0' : q ≠ 0 := hq0
    have hqr' : ‖q‖ < r := by simpa using hqr
    set w := Function.Periodic.invQParam 1 q
    have hw : A' < w.im := him q hq0' hqr'
    have hw0 : 0 < w.im := by linarith
    have hdw : DifferentiableAt ℂ (g ∘ ofComplex) w := by
      have := (hb (ofComplex w) (by
        rw [UpperHalfPlane.im, ofComplex_apply_of_im_pos hw0]; exact le_trans (le_max_left _ _) hw.le)).1
      rw [UpperHalfPlane.mdifferentiableAt_iff, ofComplex_apply_of_im_pos hw0] at this
      exact this
    have hdG : DifferentiableAt ℂ G q := by
      have := Function.Periodic.differentiableAt_cuspFunction one_ne_zero hper hdw
      rwa [Function.Periodic.qParam_right_inv one_ne_zero hq0'] at this
    exact ((differentiableAt_id.pow M).mul hdG).differentiableWithinAt
  have hbdd : BddAbove (norm ∘ F '' (Metric.ball 0 r \ {0})) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨q, ⟨hqr, hq0⟩, rfl⟩
    have hq0' : q ≠ 0 := hq0
    have hqr' : ‖q‖ < r := by simpa using hqr
    set w := Function.Periodic.invQParam 1 q
    have hw : A' < w.im := him q hq0' hqr'
    have hw0 : 0 < w.im := by linarith
    have hwA : A ≤ (ofComplex w).im := by
      rw [UpperHalfPlane.im, ofComplex_apply_of_im_pos hw0]; exact le_trans (le_max_left _ _) hw.le
    have hgw := (hb (ofComplex w) hwA).2
    have him' : (ofComplex w).im = w.im := by rw [UpperHalfPlane.im, ofComplex_apply_of_im_pos hw0]
    rw [him'] at hgw
    have hnq : ‖q‖ = Real.exp (-2 * π * w.im) := by
      have := Function.Periodic.norm_qParam (h := 1) w
      rw [Function.Periodic.qParam_right_inv one_ne_zero hq0'] at this
      rw [this, div_one]
    simp only [Function.comp_apply, hF, norm_mul, norm_pow, hGq q hq0', hnq]
    have hBM : B ≤ 2 * π * M := by
      have := Nat.le_ceil (B / (2 * π))
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hexp : Real.exp (-2 * π * w.im) ^ M * Real.exp (B * w.im) ≤ 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_one_iff]
      nlinarith
    calc Real.exp (-2 * π * w.im) ^ M * ‖g (ofComplex w)‖
        ≤ Real.exp (-2 * π * w.im) ^ M * (C * Real.exp (B * w.im)) :=
          mul_le_mul_of_nonneg_left hgw (by positivity)
      _ = C * (Real.exp (-2 * π * w.im) ^ M * Real.exp (B * w.im)) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hexp hC
      _ = C := mul_one C
  have hU := Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds 0 hr0) hdiff hbdd
  have hana := hU.analyticAt (Metric.ball_mem_nhds 0 hr0)
  have hmer : MeromorphicAt (fun q => (q ^ M)⁻¹ *
      Function.update F 0 (limUnder (𝓝[≠] (0 : ℂ)) F) q) 0 :=
    ((analyticAt_id.pow M).meromorphicAt.inv).mul hana.meromorphicAt
  refine hmer.congr ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq' : q ≠ 0 := hq
  rw [Function.update_of_ne hq']
  simp only [hF]
  field_simp

/-- Composition with a matrix of $\mathrm{SL}_2(\mathbb Z)$ preserves meromorphy on $\mathbb H$. -/
theorem isMeromorphicOnUpperHalfPlane_comp {f : ℍ → ℂ} (hf : IsMeromorphicOnUpperHalfPlane f)
    (γ : SL(2, ℤ)) : IsMeromorphicOnUpperHalfPlane (fun z => f (γ • z)) := by
  intro x hx
  set μ : ℂ → ℂ := fun w => ((γ • ofComplex w : ℍ) : ℂ) with hμ
  have hmd : MDiff (fun w : ℍ => ((γ • w : ℍ) : ℂ)) := fun z =>
    (UpperHalfPlane.mdifferentiable_coe (γ • z)).comp z (mdiffAt_smul_SL γ z)
  have hμa : AnalyticAt ℂ μ x :=
    (UpperHalfPlane.mdifferentiable_iff.1 hmd).analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hx)
  have hμx : μ x ∈ {z : ℂ | 0 < z.im} := (γ • ofComplex x).im_pos
  have := (hf (μ x) hμx).comp_analyticAt hμa
  convert this using 1
  funext w
  simp only [Function.comp_apply, hμ, ofComplex_apply]

/-- A modular function composed with a matrix of $\mathrm{SL}_2(\mathbb Z)$ lies in `goodSubalgebra`. -/
theorem mem_goodSubalgebra_comp {Γ : Subgroup SL(2, ℤ)} {f : ℍ → ℂ} (hf : IsModularFunction Γ f)
    (γ : SL(2, ℤ)) : (fun z => f (γ • z)) ∈ goodSubalgebra :=
  ⟨isMeromorphicOnUpperHalfPlane_comp hf.meromorphic γ,
    isModerate_of_isMeromorphicAtImInfty (hf.meromorphic_cusps γ)⟩

/-- An $\mathrm{SL}_2(\mathbb Z)$-invariant function of `goodSubalgebra` is a modular function for
$\Gamma_0(1)$. -/
theorem isModularFunction_top_of_mem {g : ℍ → ℂ} (hg : g ∈ goodSubalgebra)
    (hinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), g (γ • z) = g z) : IsModularFunction ⊤ g where
  meromorphic := hg.1
  invariant γ _ z := hinv γ z
  meromorphic_cusps γ := by
    have : (fun z => g (γ • z)) = g := funext (hinv γ)
    rw [this]
    refine isMeromorphicAtImInfty_of_isModerate ?_ hg.2
    intro w
    simp only [Function.comp_apply]
    rcases le_or_gt w.im 0 with hw | hw
    · rw [ofComplex_apply_eq_of_im_nonpos (w := w + 1) (w' := w) (by simpa using hw) hw]
    · have hw1 : 0 < (w + 1).im := by simpa using hw
      have : ofComplex (w + 1) = ModularGroup.T • ofComplex w := by
        ext
        rw [ofComplex_apply_of_im_pos hw1, UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd,
          ofComplex_apply_of_im_pos hw]
        push_cast
        ring
      rw [this, hinv]

/-- Constants are modular functions. -/
theorem isModularFunction_const (Γ : Subgroup SL(2, ℤ)) (c : ℂ) : IsModularFunction Γ (fun _ => c) where
  meromorphic := MeromorphicOn.const c
  invariant _ _ _ := rfl
  meromorphic_cusps _ := isMeromorphicAtImInfty_of_isModerate (fun _ => rfl) (IsModerate.const c)

/-- A nonzero holomorphic function on $\mathbb H$ vanishes only on a discrete set. -/
theorem eventually_codiscrete_ne_zero {g : ℍ → ℂ} (hg : MDiff g) (hg0 : g ≠ 0) :
    ∀ᶠ z in codiscrete ℍ, g z ≠ 0 := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro x
  by_contra hcon
  have hfreq : ∃ᶠ w in 𝓝[≠] x, g w = 0 := (not_eventually.mp hcon).mono fun w hw => not_not.mp hw
  exact hg0 (UpperHalfPlane.eq_zero_of_frequently hg hfreq)

/-- For $0 \ne Q \in \mathbb C[X]$, $Q(j(z)) \ne 0$ off a discrete set. -/
theorem eventually_codiscrete_eval_jFun_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∀ᶠ z in codiscrete ℍ, Q.eval (jFun z) ≠ 0 := by
  refine eventually_codiscrete_ne_zero (fun z => mdiffAt_eval_jFun Q z) fun h0 => hQ ?_
  refine Polynomial.funext fun t => ?_
  obtain ⟨w, rfl⟩ := jFun_surjective t
  simpa using congrFun h0 w

/-! ### Lagrange interpolation over the cosets of $\Gamma_0(N)$ -/

section Interp

open Classical

variable {N : ℕ} [NeZero N] {f : ℍ → ℂ}

/-- $f \circ \gamma^{-1}$ for the coset $c = \gamma\Gamma_0(N)$ (with a chosen representative). -/
noncomputable def cosetFun (N : ℕ) (f : ℍ → ℂ) (c : Cosets N) (z : ℍ) : ℂ := f ((Quotient.out c)⁻¹ • z)

theorem cosetFun_mk (hf : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z, f (γ • z) = f z) (γ : SL(2, ℤ)) (z : ℍ) :
    cosetFun N f (γ : Cosets N) z = f (γ⁻¹ • z) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) γ
  unfold cosetFun
  rw [hh, mul_inv_rev, mul_smul]
  exact hf _ (inv_mem h.2) _

theorem cosetFun_smul (hf : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z, f (γ • z) = f z) (δ : SL(2, ℤ))
    (c : Cosets N) (z : ℍ) : cosetFun N f (δ • c) (δ • z) = cosetFun N f c z := by
  induction c using QuotientGroup.induction_on with
  | H γ =>
    rw [show δ • (γ : Cosets N) = ((δ * γ : SL(2, ℤ)) : Cosets N) from rfl, cosetFun_mk hf,
      cosetFun_mk hf, mul_inv_rev, mul_smul, inv_smul_smul]

/-- Milne's $G_z(Y) = \sum_{c} f(\gamma_c^{-1}z) \prod_{c' \ne c} (Y - j_N(\gamma_{c'}^{-1}z))$. -/
noncomputable def interpPoly (N : ℕ) [NeZero N] (f : ℍ → ℂ) (z : ℍ) : ℂ[X] :=
  ∑ c : Cosets N, C (cosetFun N f c z) * ∏ c' ∈ Finset.univ.erase c, (X - C (cosetRoot N c' z))

theorem interpPoly_smul (hf : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z, f (γ • z) = f z) (δ : SL(2, ℤ))
    (z : ℍ) : interpPoly N f (δ • z) = interpPoly N f z := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Cosets N), ∀ c, σ c = δ⁻¹ • c :=
    ⟨MulAction.toPerm δ⁻¹, fun _ => rfl⟩
  have hr : ∀ c : Cosets N, cosetRoot N c (δ • z) = cosetRoot N (σ c) z := fun c => by
    have := cosetRoot_smul (one_le_of_neZero (N := N)) δ (δ⁻¹ • c) z
    rwa [smul_inv_smul, ← hσ] at this
  have hfc : ∀ c : Cosets N, cosetFun N f c (δ • z) = cosetFun N f (σ c) z := fun c => by
    have := cosetFun_smul hf δ (δ⁻¹ • c) z
    rwa [smul_inv_smul, ← hσ] at this
  unfold interpPoly
  rw [← Equiv.sum_comp σ (fun c => C (cosetFun N f c z) *
    ∏ c' ∈ Finset.univ.erase c, (X - C (cosetRoot N c' z)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hfc]
  refine congrArg (C (cosetFun N f (σ c) z) * ·) ?_
  refine Finset.prod_equiv σ (fun i => ?_) (fun i _ => ?_)
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, σ.injective.eq_iff]
  · rw [hr]

theorem interpPoly_coeff_mem (hf : IsModularFunction (CongruenceSubgroup.Gamma0 N) f) (k : ℕ) :
    (fun z => (interpPoly N f z).coeff k) ∈ goodSubalgebra := by
  classical
  have hN := (one_le_of_neZero (N := N))
  set S := goodSubalgebra
  let fS : Cosets N → S := fun c => ⟨cosetFun N f c, mem_goodSubalgebra_comp hf _⟩
  let rS : Cosets N → S := fun c => ⟨cosetRoot N c, mem_goodSubalgebra_comp (isModularFunction_jN hN) _⟩
  let PS : S[X] := ∑ c, C (fS c) * ∏ c' ∈ Finset.univ.erase c, (X - C (rS c'))
  have key : ∀ z, interpPoly N f z = PS.map ((Pi.evalRingHom (fun _ : ℍ => ℂ) z).comp S.val.toRingHom) := by
    intro z
    simp [PS, interpPoly, Polynomial.map_sum, Polynomial.map_prod, fS, rS]
  have : (fun z => (interpPoly N f z).coeff k) = (PS.coeff k : ℍ → ℂ) := by
    funext z
    rw [key, coeff_map]
    rfl
  rw [this]
  exact (PS.coeff k).2

/-- The coefficients of $G_z(Y)$ are rational functions of $j$ (Proposition 2.2). -/
theorem interpPoly_coeff_rational (hf : IsModularFunction (CongruenceSubgroup.Gamma0 N) f) (k : ℕ) :
    ∃ P Q : ℂ[X], Q ≠ 0 ∧ (fun z => (interpPoly N f z).coeff k) =ᶠ[codiscrete ℍ]
      fun z => P.eval (jFun z) / Q.eval (jFun z) :=
  prop2_2Rational.rational _ (isModularFunction_top_of_mem (interpPoly_coeff_mem hf k)
    fun γ z => by simp only [interpPoly_smul hf.invariant])

theorem interpPoly_natDegree_lt (z : ℍ) : (interpPoly N f z).natDegree < Fintype.card (Cosets N) := by
  classical
  have hpos : 0 < Fintype.card (Cosets N) := Fintype.card_pos
  have hle : (interpPoly N f z).natDegree ≤ Fintype.card (Cosets N) - 1 := by
    unfold interpPoly
    refine natDegree_sum_le_of_forall_le _ _ fun c _ => (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp [Finset.card_erase_of_mem]
  omega

/-- At $Y = j_N(z)$ only the trivial coset contributes: $G_z(j_N(z)) = f(z)\prod_{c \ne 1}(j_N(z) - r_c(z))$. -/
theorem interpPoly_eval_jN (hf : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z, f (γ • z) = f z) (z : ℍ) :
    (interpPoly N f z).eval (jN N z) =
      f z * ∏ c ∈ Finset.univ.erase ((1 : SL(2, ℤ)) : Cosets N), (jN N z - cosetRoot N c z) := by
  classical
  have hN := (one_le_of_neZero (N := N))
  unfold interpPoly
  rw [eval_finsetSum, Finset.sum_eq_single ((1 : SL(2, ℤ)) : Cosets N)]
  · rw [eval_mul, eval_C, eval_prod, cosetFun_mk hf, inv_one, one_smul]
    simp only [eval_sub, eval_X, eval_C]
  · intro c _ hc
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := ((1 : SL(2, ℤ)) : Cosets N))
      (Finset.mem_erase.2 ⟨Ne.symm hc, Finset.mem_univ _⟩), mul_zero]
    rw [eval_sub, eval_X, eval_C, cosetRoot_mk hN, inv_one, one_smul, sub_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Clearing the denominators of the coefficients of $G_z$: $q(j(z))\,G_z(j_N(z)) = \mathrm{Num}(j(z), j_N(z))$ off a
discrete set. -/
theorem exists_num (hf : IsModularFunction (CongruenceSubgroup.Gamma0 N) f) :
    ∃ (Num : ℂ[X][X]) (q : ℂ[X]), q ≠ 0 ∧
      ∀ᶠ z in codiscrete ℍ, q.eval (jFun z) * (interpPoly N f z).eval (jN N z) = evalJJN N Num z := by
  classical
  set m := Fintype.card (Cosets N) with hm
  choose P Q hQ hPQ using fun k => interpPoly_coeff_rational hf k
  refine ⟨∑ k ∈ Finset.range m, C (P k * ∏ l ∈ (Finset.range m).erase k, Q l) * X ^ k,
    ∏ k ∈ Finset.range m, Q k, Finset.prod_ne_zero_iff.2 fun k _ => hQ k, ?_⟩
  filter_upwards [(Filter.eventually_all_finset (Finset.range m)).2 fun k _ => hPQ k,
    (Filter.eventually_all_finset (Finset.range m)).2
      fun k _ => eventually_codiscrete_eval_jFun_ne_zero (hQ k)] with z hz hzQ
  rw [eval_eq_sum_range' (interpPoly_natDegree_lt z), Finset.mul_sum]
  unfold evalJJN
  rw [Polynomial.map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hzk : (interpPoly N f z).coeff k = (P k).eval (jFun z) / (Q k).eval (jFun z) := hz k hk
  rw [hzk]
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_X, Polynomial.map_C, coe_evalRingHom, eval_mul,
    eval_pow, eval_X, eval_C, eval_prod]
  rw [← Finset.mul_prod_erase _ _ hk]
  have h0 := hzQ k hk
  field_simp

end Interp

/-! ### Theorem 2.3 -/

open Classical in
/-- **Theorem 2.3** (Milne V §2, pdf p. 192): every modular function for $\Gamma_0(N)$ is, off a discrete set, a
rational function of $j$ and $j_N$. This proves the named `Thm2_3`. -/
@[kb "milne2006ec" "Ch. V, Theorem 2.3, pdf p. 192"]
theorem thm2_3 : Thm2_3 := by
  refine ⟨fun N hN f hf => ?_⟩
  have : NeZero N := ⟨by omega⟩
  obtain ⟨Nf, qf, hqf, hf'⟩ := exists_num hf
  obtain ⟨N1, q1, hq1, h1'⟩ := exists_num (isModularFunction_const (CongruenceSubgroup.Gamma0 N) 1)
  set e := ((1 : SL(2, ℤ)) : Cosets N) with he
  set D : ℍ → ℂ := fun z => ∏ c ∈ Finset.univ.erase e, (jN N z - cosetRoot N c z) with hDdef
  have hfac : ∀ c ∈ Finset.univ.erase e, MDiff (fun z => jN N z - cosetRoot N c z) :=
    fun c _ => (jN_mdifferentiable hN).sub (cosetRoot_mdiff hN c)
  have hDmd : MDiff D := by
    have := mdiff_finset_prod _ _ hfac
    exact this
  have hD0 : D ≠ 0 := by
    have := finset_prod_ne_zero _ _ hfac fun c hc h0 => by
      apply (Finset.mem_erase.1 hc).1
      apply cosetRoot_injective hN
      funext z
      have := congrFun h0 z
      simp only [Pi.zero_apply, sub_eq_zero] at this
      rw [← this, he, cosetRoot_mk hN, inv_one, one_smul]
    exact this
  have hDev := eventually_codiscrete_ne_zero hDmd hD0
  have hinv1 : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z, (fun _ : ℍ => (1 : ℂ)) (γ • z) = (fun _ => 1) z :=
    fun _ _ _ => rfl
  have hgood : ∀ᶠ z in codiscrete ℍ,
      qf.eval (jFun z) * (f z * D z) = evalJJN N Nf z ∧ q1.eval (jFun z) * D z = evalJJN N N1 z ∧
      D z ≠ 0 ∧ qf.eval (jFun z) ≠ 0 ∧ q1.eval (jFun z) ≠ 0 := by
    filter_upwards [hf', h1', hDev, eventually_codiscrete_eval_jFun_ne_zero hqf,
      eventually_codiscrete_eval_jFun_ne_zero hq1] with z h1 h2 h3 h4 h5
    refine ⟨?_, ?_, h3, h4, h5⟩
    · rw [← h1, interpPoly_eval_jN hf.invariant]
    · rw [← h2, interpPoly_eval_jN hinv1, one_mul]
  have hev : ∀ G : ℂ[X][X], ∀ (q : ℂ[X]) (z : ℍ), evalJJN N (G * C q) z = evalJJN N G z * q.eval (jFun z) := by
    intro G q z
    unfold evalJJN
    rw [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, coe_evalRingHom]
  refine ⟨Nf * C q1, N1 * C qf, ?_, ?_⟩
  · have hτ := (eventually_codiscrete_iff_forall_eventually_nhdsNE.1 hgood) UpperHalfPlane.I
    obtain ⟨z, h1, h2, h3, h4, h5⟩ := hτ.exists
    refine ⟨z, ?_⟩
    rw [hev, ← h2]
    exact mul_ne_zero (mul_ne_zero h5 h3) h4
  · filter_upwards [hgood] with z ⟨h1, h2, h3, h4, h5⟩
    rw [hev, hev, ← h1, ← h2]
    field_simp

end NumberFieldKB.ModularCurves
