import NumberFieldKB.ModularCurves.ComplexForward
import NumberFieldKB.ModularCurves.ComplexQExp

/-!
# The cusp condition for representatives of cusp forms

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Proposition 3.3 and Corollary 3.4 (pdf p. 199), at the cusps.
For $f \in S_2(\Gamma_0(N))$ with representative $h_f = P(j,j_N)/Q(j,j_N)$ and a coset $c$, $\gamma = \gamma_c^{-1}$:
the function $F_c(\tau) = (f|_2\gamma)(N\tau)$ has a $q$-expansion vanishing at $q = 0$, and
$\hat F_c = \sigma_c(h_f) \cdot$ `jDerSer N` (`qHat_slashScale_eq`), by the polynomial identity
$F_c\, Q(j(N\tau), j_N(\gamma N\tau)) = P(\ldots)\, j'(N\tau)$ and the ring map `qMerDHom`. Hence $h_f$ satisfies the
conditions of $L(W)$ at the cusps (`IsRep.forall_infty`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti ModularForm
open scoped WithZero MatrixGroups Manifold

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable {N : ℕ}

theorem tendsto_ofComplex_mul (hN : 1 ≤ N) :
    Tendsto (fun τ : ℍ => ofComplex ((N : ℂ) * τ)) atImInfty atImInfty := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [atImInfty, tendsto_comap_iff]
  have : (UpperHalfPlane.im ∘ fun τ : ℍ => ofComplex ((N : ℂ) * τ)) = fun τ => (N : ℝ) * τ.im := by
    funext τ; exact im_ofComplex_mul hN τ
  rw [this]
  exact tendsto_comap.const_mul_atTop hNpos

/-- A holomorphic $N$-periodic function bounded at $i\infty$ gives, after $\tau \mapsto N\tau$, a function with a
$q$-expansion of period 1. -/
theorem isQExp_scaleN_of_periodic (hN : 1 ≤ N) {f : ℍ → ℂ} (hmd : MDiff f)
    (hper : Function.Periodic (f ∘ ofComplex) (N : ℝ)) (hbd : IsBoundedAtImInfty f) :
    IsQExp (scaleN N f) where
  mdiff := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hf' := UpperHalfPlane.mdifferentiable_iff.1 hmd
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hmaps : Set.MapsTo (fun w : ℂ => (N : ℂ) * w) {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} :=
      fun w hw => by simp [Complex.mul_im]; exact mul_pos hNpos hw
    refine (hf'.comp ((differentiable_id.const_mul _).differentiableOn) hmaps).congr ?_
    intro w hw
    simp only [Function.comp_apply, NumberFieldKB.ModularCurves.scaleN]
    rw [ofComplex_apply_of_im_pos hw]
  periodic := by
    intro w
    simp only [Function.comp_apply, NumberFieldKB.ModularCurves.scaleN]
    rcases le_or_gt w.im 0 with hw | hw
    · rw [ofComplex_apply_eq_of_im_nonpos (w := w + 1) (w' := w) (by simpa using hw) hw]
    · have hw1 : 0 < (w + 1).im := by simpa using hw
      rw [ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
      have := hper ((N : ℂ) * w)
      simp only [Function.comp_apply] at this
      push_cast at this ⊢
      rw [mul_add, mul_one]
      exact this
  bounded := hbd.comp_tendsto (tendsto_ofComplex_mul hN)

/-- A function with a $q$-expansion that tends to $0$ at $i\infty$ has a Laurent expansion of order $\ge 1$. -/
theorem valuation_qHat_le_of_isZeroAtImInfty {F : ℍ → ℂ} (hF : IsQExp F) (h0 : IsZeroAtImInfty F) :
    Valued.v (qHat F) ≤ WithZero.exp (-1 : ℤ) := by
  have hc : (qExpansion 1 F).coeff 0 = 0 := by
    rw [qExpansion_coeff_zero one_pos hF.analytic hF.periodic]
    exact h0.limUnder_eq
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) from rfl, LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
  intro n hn
  rcases lt_or_ge n 0 with hneg | hnn
  · rw [qHat, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
    rintro ⟨k, hk⟩
    have : (0 : ℤ) ≤ k := by exact_mod_cast Nat.zero_le k
    simp at hk
    omega
  · have hn0 : n = 0 := by omega
    subst hn0
    rw [qHat, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, hc]

theorem qHat_smul {F : ℍ → ℂ} (hF : IsQExp F) (a : ℂ) : qHat (a • F) = HahnSeries.C a * qHat F := by
  rw [qHat, UpperHalfPlane.qExpansion_smul hF.analytic, qHat, PowerSeries.smul_eq_C_mul, map_mul,
    HahnSeries.ofPowerSeries_C]

variable (N) [NeZero N]

/-- **The global identity** $P(j, j_N)\,j' = f\,Q(j, j_N)$ for a representative $P(j,j_N)/Q(j,j_N)$ of $f$. -/
theorem rep_identity {f : ℍ → ℂ} (hf : MDiff f) {P Q : ℂ[X][X]} (hQ : mkC N Q ≠ 0)
    (H : IsRep N f hf (mkC N P / mkC N Q)) (z : ℍ) :
    evalJJN N P z * jD z = f z * evalJJN N Q z := by
  set g : ℍ → ℂ := fun z => evalJJN N P z * jD z - f z * evalJJN N Q z
  have hmdP : MDiff (evalJJNC N P) := mdifferentiable_evalJJNHom (N := N) (RingHom.id ℂ) (one_le_N N) P
  have hmdQ : MDiff (evalJJNC N Q) := mdifferentiable_evalJJNHom (N := N) (RingHom.id ℂ) (one_le_N N) Q
  have hg : MDiff g := by
    have e : g = evalJJNC N P * jD - f * evalJJNC N Q := by
      funext w; simp only [g, Pi.sub_apply, Pi.mul_apply, evalJJNC_apply]
    rw [e]
    exact (hmdP.mul mdiff_jD).sub (hf.mul hmdQ)
  suffices h : g = 0 by simpa [g, sub_eq_zero] using congrFun h z
  refine UpperHalfPlane.eq_zero_of_frequently hg (τ := UpperHalfPlane.I) ?_
  -- near $i$ the germ identity holds
  have hgerm := H UpperHalfPlane.I
  have hb : finEmbC UpperHalfPlane.I N (cosetOne N) (mkC N Q) ≠ 0 :=
    (map_ne_zero_iff _ (finEmbC UpperHalfPlane.I N (cosetOne N)).toRingHom.injective).2 hQ
  rw [map_div₀, div_mul_eq_mul_div, div_eq_iff hb, finEmbC_mkC, finEmbC_mkC, polyGerm2, polyGerm2, jDerivGerm,
    ← MeroGerm.mk_mul, ← MeroGerm.mk_mul, MeroGerm.mk_eq_mk] at hgerm
  have hev : ∀ᶠ z in 𝓝[≠] UpperHalfPlane.I, g z = 0 := by
    refine eventually_of_comp_ofComplex (p := fun z => g z = 0) ?_
    filter_upwards [hgerm, nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds UpperHalfPlane.I.im_pos)]
      with w hw him
    simp only [Pi.mul_apply, Function.comp_apply, polyFun2_one] at hw
    have hjw : jD (ofComplex w) = deriv (jFun ∘ ofComplex) w := by
      rw [jD, ofComplex_apply_of_im_pos him]
    simp only [g]
    rw [hjw, hw, sub_self]
  exact hev.frequently

/-- The identity moved to the cusp of $c$: with $\gamma = \gamma_c^{-1}$,
$P(j(w), j_N(\gamma w))\, j'(w) = (f|_2\gamma)(w)\, Q(j(w), j_N(\gamma w))$. -/
theorem rep_identity_coset {f : ℍ → ℂ} (hf : MDiff f) {P Q : ℂ[X][X]} (hQ : mkC N Q ≠ 0)
    (H : IsRep N f hf (mkC N P / mkC N Q)) (c : Cosets N) (w : ℍ) :
    (P.map (evalRingHom (jFun w))).eval (cosetRoot N c w) * jD w =
      (f ∣[(2 : ℤ)] cosetMat N c) w * (Q.map (evalRingHom (jFun w))).eval (cosetRoot N c w) := by
  have h := rep_identity N hf hQ H (cosetMat N c • w)
  have hd := deriv_moebiusC_ne_zero (cosetMat N c) w
  have hj := jD_smul (cosetMat N c) w
  have hs := pullback_eq_slash (cosetMat N c) f w
  have e1 : ∀ G : ℂ[X][X], evalJJN N G (cosetMat N c • w) =
      (G.map (evalRingHom (jFun w))).eval (cosetRoot N c w) := fun G => by
    rw [evalJJN, jFun_smul]
    rfl
  rw [e1, e1] at h
  rw [← hj, ← hs]
  linear_combination deriv (moebiusC (cosetMat N c)) (w : ℂ) * h

/-! ### The $q$-expansion of $F_c(\tau) = (f|_2\gamma)(N\tau)$ -/

section Slash

variable {f : ℍ → ℂ} (hf : IsCuspFormMilne (CongruenceSubgroup.Gamma0 N) 1 f)

omit [NeZero N] in
include hf in
theorem slash_vadd_N (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[(2 : ℤ)] γ) ((N : ℝ) +ᵥ τ) = (f ∣[(2 : ℤ)] γ) τ := by
  obtain ⟨-, hinv0, -⟩ := hf
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z, f (γ • z) * deriv (moebiusC γ) z = f z := fun γ hγ =>
    (weight_two_iff_differential_invariant γ f).1 (by simpa using hinv0 γ hγ)
  have hslash : ∀ δ ∈ CongruenceSubgroup.Gamma0 N, f ∣[(2 : ℤ)] δ = f := fun δ hδ => by
    funext z
    rw [← pullback_eq_slash]
    exact hinv δ hδ z
  set T' : SL(2, ℤ) := ModularGroup.T ^ (N : ℤ)
  have keyT : (f ∣[(2 : ℤ)] γ) ∣[(2 : ℤ)] T' = f ∣[(2 : ℤ)] γ := by
    rw [← SlashAction.slash_mul]
    have : γ * T' = (γ * T' * γ⁻¹) * γ := by simp
    rw [this, SlashAction.slash_mul, hslash _ (conj_T_zpow_mem_Gamma0 N γ)]
  have hc : (T' 1 0 : ℂ) * τ + T' 1 1 = 1 := by
    have h : (T' : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] := ModularGroup.coe_T_zpow (N : ℤ)
    have e10 : (T' 1 0 : ℤ) = 0 := by simpa using congrFun (congrFun h 1) 0
    have e11 : (T' 1 1 : ℤ) = 1 := by simpa using congrFun (congrFun h 1) 1
    rw [e10, e11]; simp
  have := congrFun keyT τ
  have h2 : ((f ∣[(2 : ℤ)] γ) ∣[(2 : ℤ)] T') τ =
      (T' 1 0 * (τ : ℂ) + T' 1 1) ^ (-(2 : ℤ)) * (f ∣[(2 : ℤ)] γ) (T' • τ) :=
    slash_mapGL_apply 2 _ T' τ
  rw [h2, hc, one_zpow, one_mul, UpperHalfPlane.modular_T_zpow_smul] at this
  exact_mod_cast this

omit [NeZero N] in
include hf in
theorem isZeroAtImInfty_slash (γ : SL(2, ℤ)) : IsZeroAtImInfty (f ∣[(2 : ℤ)] γ) := by
  have h := hf.2.2 γ
  refine h.congr' (Eventually.of_forall fun z => ?_)
  have := slash_mapGL_apply 2 f γ z
  rw [show (2 * ((1 : ℕ) : ℤ)) = 2 by norm_num]
  exact this.symm

include hf in
theorem isQExp_slashScale (γ : SL(2, ℤ)) : IsQExp (scaleN N (f ∣[(2 : ℤ)] γ)) :=
  isQExp_scaleN_of_periodic (one_le_N N) (MDifferentiable.slash hf.1 2 (Matrix.SpecialLinearGroup.mapGL ℝ γ))
    (UpperHalfPlane.periodic_comp_ofComplex (slash_vadd_N N hf γ))
    (isZeroAtImInfty_slash N hf γ).boundedAtFilter

include hf in
theorem isZeroAtImInfty_slashScale (γ : SL(2, ℤ)) : IsZeroAtImInfty (scaleN N (f ∣[(2 : ℤ)] γ)) :=
  (isZeroAtImInfty_slash N hf γ).comp (tendsto_ofComplex_mul (one_le_N N))

end Slash

/-! ### The transfer to Laurent series -/

/-- **The expansion of $F_c$**: $\sigma_c(h_f)\cdot$ `jDerSer N` $= \hat F_c$, $F_c(\tau) = (f|_2\gamma_c^{-1})(N\tau)$. -/
theorem cuspEmbC_mul_jDerSer {f : ℍ → ℂ} (hf : IsCuspFormMilne (CongruenceSubgroup.Gamma0 N) 1 f)
    {P Q : ℂ[X][X]} (hQ : mkC N Q ≠ 0) (H : IsRep N f hf.1 (mkC N P / mkC N Q)) (c : Cosets N) :
    @Eq (CuspField N) (cuspEmbC N c (mkC N P / mkC N Q) * jDerSer N)
      (qHat (scaleN N (f ∣[(2 : ℤ)] cosetMat N c))) := by
  have hN := one_le_N N
  set F := scaleN N (f ∣[(2 : ℤ)] cosetMat N c)
  have hFq : IsQExp F := isQExp_slashScale N hf _
  -- the pointwise identity in the variable of the cusp
  have hpt : ∀ τ : ℍ,
      (P.map (evalRingHom (scaleN N cubeE4 τ / scaleN N discFun τ))).eval (numC N c τ / denC N c τ) *
        ((-(2 * Real.pi * Complex.I)) * scaleN N derNum τ / scaleN N discFun τ) =
      F τ * (Q.map (evalRingHom (scaleN N cubeE4 τ / scaleN N discFun τ))).eval (numC N c τ / denC N c τ) := by
    intro τ
    have h := rep_identity_coset N hf.1 hQ H c (ofComplex ((N : ℂ) * τ))
    rw [jN_eq_div N τ, cosetRoot_ofComplex_mul N c τ, jD, deriv_jFun_mul_eq N τ] at h
    rw [show (-(2 * Real.pi * Complex.I)) * scaleN N derNum τ / scaleN N discFun τ =
      -(2 * Real.pi * Complex.I) * scaleN N derNum τ / scaleN N discFun τ by ring]
    exact h
  -- the ring of meromorphic $q$-expansions with denominator $d = \Delta(N\tau)\,\mathrm{den}_c$
  set d : ℍ → ℂ := scaleN N discFun * denC N c
  have hd : IsQExp d := (isQExp_discFun.scaleN hN).mul (isQExp_denC N c)
  have hd0 : ∀ z, d z ≠ 0 := fun z => mul_ne_zero (ModularForm.discriminant_ne_zero _) (denC_ne_zero N c z)
  have hD0 : ∀ z, scaleN N discFun z ≠ 0 := fun z => ModularForm.discriminant_ne_zero _
  let xj := divMerD hd (isQExp_cubeE4.scaleN hN) (isQExp_denC N c) rfl hD0
  let xy := divMerD hd (isQExp_numC N c) (isQExp_discFun.scaleN hN) (mul_comm _ _) (denC_ne_zero N c)
  let xD := divMerD hd ((isQExp_derNum.scaleN hN).smul (-(2 * Real.pi * Complex.I))) (isQExp_denC N c) rfl hD0
  let xF : qMerD d hd := ⟨F, 0, by simpa using hFq⟩
  have hid : evalMerD hd xj xy P * xD = xF * evalMerD hd xj xy Q := by
    apply Subtype.ext
    funext τ
    change (evalMerD hd xj xy P).1 τ * xD.1 τ = F τ * (evalMerD hd xj xy Q).1 τ
    rw [coe_evalMerD, coe_evalMerD]
    have := hpt τ
    simpa [xj, xy, xD, divMerD, Pi.div_apply, Pi.smul_apply, smul_eq_mul, mul_div_assoc] using this
  have hL := congrArg (qMerDHom hd hd0) hid
  rw [map_mul, map_mul, qMerDHom_evalMerD, qMerDHom_evalMerD] at hL
  have ej : qMerDHom hd hd0 xj = jNSer N :=
    qMerDHom_divMerD hd hd0 (isQExp_cubeE4.scaleN hN) (isQExp_discFun.scaleN hN) (isQExp_denC N c) rfl hD0
  have ey : qMerDHom hd hd0 xy = (ySer N c : LaurentSeries ℂ) :=
    qMerDHom_divMerD hd hd0 (isQExp_numC N c) (isQExp_denC N c) (isQExp_discFun.scaleN hN) (mul_comm _ _)
      (denC_ne_zero N c)
  have eD : qMerDHom hd hd0 xD =
      qHat ((-(2 * Real.pi * Complex.I)) • scaleN N derNum) / qHat (scaleN N discFun) :=
    qMerDHom_divMerD hd hd0 ((isQExp_derNum.scaleN hN).smul _) (isQExp_discFun.scaleN hN) (isQExp_denC N c) rfl
      hD0
  have hxF : qMerDHom hd hd0 xF = qHat F := qMerDFun_of_isQExp hd hd0 xF hFq
  rw [ej, ey, eD, hxF, qHat_smul (isQExp_derNum.scaleN hN)] at hL
  -- compare with `cuspEmbC`
  have hb : cuspEmbC N c (mkC N Q) ≠ 0 := (map_ne_zero_iff _ (cuspEmbC N c).toRingHom.injective).2 hQ
  rw [map_div₀, div_mul_eq_mul_div]
  refine (div_eq_iff hb).2 ?_
  rw [cuspEmbC_mkC, cuspEmbC_mkC]
  exact hL

end NumberFieldKB.ModularCurves
