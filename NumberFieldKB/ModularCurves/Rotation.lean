import NumberFieldKB.ModularCurves.FiniteRamification

/-!
# Germs invariant under an elliptic element

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196). Let $g \in \mathrm{SL}_2(\mathbb Z)$ fix
$\tau_0 \in \mathbb H$. Composition with $z \mapsto g z$ is a ring endomorphism `rot g τ₀ hg` of the meromorphic germs
at $\tau_0$, and a $\mathbb Q(j)$-algebra map of `FinField τ₀` (as $j \circ g = j$) which permutes the embeddings:
$\mathrm{rot}_g \circ \sigma_c = \sigma_{g^{-1} c}$ (`rotAlg_comp_finEmb`).

If $g'(\tau_0)$ is a primitive $e$-th root of unity $\zeta$, a nonzero germ $f$ with $f \circ g = f$ has order divisible
by $e$ (`exists_ordVal_eq_of_rot_eq`): $f(gz)/f(z) \to \zeta^{\operatorname{ord} f}$. At $\tau_0 = i$, $g = S$:
$g'(i) = -1$; at $\tau_0 = \rho$, $g = ST$: $g'(\rho) = (\rho + 1)^{-2} = \rho^{-1}$.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped WithZero MatrixGroups

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable (g : SL(2, ℤ))

/-- $z \mapsto g z$ in the coordinate of $\mathbb C$. -/
def moeb (z : ℂ) : ℂ := ((g • ofComplex z : ℍ) : ℂ)

theorem det_SL_GL : (↑(g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g).det_coe

theorem det_pos_SL : 0 < (↑(g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [det_SL_GL]; exact one_pos

theorem analyticAt_moeb (τ : ℍ) : AnalyticAt ℂ (moeb g) (τ : ℂ) :=
  UpperHalfPlane.analyticAt_smul (g := (g : GL (Fin 2) ℝ)) (det_pos_SL g) τ

theorem moeb_coe (τ : ℍ) : moeb g (τ : ℂ) = ((g • τ : ℍ) : ℂ) := by
  rw [moeb, ofComplex_apply]

theorem deriv_moeb (τ : ℍ) : deriv (moeb g) (τ : ℂ) = 1 / denom (g : GL (Fin 2) ℝ) τ ^ 2 := by
  have h := UpperHalfPlane.deriv_smul (g := (g : GL (Fin 2) ℝ)) (det_pos_SL g) τ
  rw [det_SL_GL] at h
  change deriv (fun z => ((((g : GL (Fin 2) ℝ)) • ofComplex z : ℍ) : ℂ)) τ = _
  rw [h]
  simp

variable (τ₀ : ℍ) (hg : g • τ₀ = τ₀)

include hg in
theorem moeb_fixed : moeb g (τ₀ : ℂ) = τ₀ := by rw [moeb_coe, hg]

include hg in
theorem tendsto_moeb : Tendsto (moeb g) (𝓝[≠] (τ₀ : ℂ)) (𝓝[≠] (τ₀ : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := (analyticAt_moeb g τ₀).continuousAt
    rw [ContinuousAt, moeb_fixed g τ₀ hg] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have hU : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), 0 < z.im :=
      nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ₀.im_pos)
    filter_upwards [hU, self_mem_nhdsWithin] with z hz hne
    intro h
    apply hne
    have h1 : g • ofComplex z = g • τ₀ := by
      rw [hg]
      exact UpperHalfPlane.ext h
    have h2 := smul_left_cancel g h1
    have h3 := congrArg (fun w : ℍ => (w : ℂ)) h2
    simp only [ofComplex_apply_of_im_pos hz] at h3
    exact h3

/-- **Composition with $g$** on the meromorphic germs at a fixed point $\tau_0$ of $g$. -/
def rot : MeroGerm (τ₀ : ℂ) →+* MeroGerm (τ₀ : ℂ) where
  toFun a := ⟨a.1.compTendsto (moeb g) (tendsto_moeb g τ₀ hg), by
    obtain ⟨_, f, hf, rfl⟩ := a
    refine ⟨f ∘ moeb g, ?_, (Filter.Germ.coe_compTendsto f _).symm⟩
    exact MeromorphicAt.comp_analyticAt (by rw [moeb_fixed g τ₀ hg]; exact hf) (analyticAt_moeb g τ₀)⟩
  map_one' := rfl
  map_mul' a b := by
    obtain ⟨_, f, hf, rfl⟩ := a
    obtain ⟨_, f', hf', rfl⟩ := b
    rfl
  map_zero' := rfl
  map_add' a b := by
    obtain ⟨_, f, hf, rfl⟩ := a
    obtain ⟨_, f', hf', rfl⟩ := b
    rfl

theorem rot_mk (f : ℂ → ℂ) (hf : MeromorphicAt f (τ₀ : ℂ)) :
    rot g τ₀ hg (MeroGerm.mk f hf) = MeroGerm.mk (f ∘ moeb g)
      (MeromorphicAt.comp_analyticAt (by rw [moeb_fixed g τ₀ hg]; exact hf) (analyticAt_moeb g τ₀)) := rfl

/-- **A $g$-invariant germ has order divisible by $e$**, if $g'(\tau_0)$ is a primitive $e$-th root of unity. -/
theorem exists_ordVal_eq_of_rot_eq {e : ℕ} (he : e ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ e)
    (hd : deriv (moeb g) (τ₀ : ℂ) = ζ)
    {a : MeroGerm (τ₀ : ℂ)} (ha : a ≠ 0) (hfix : rot g τ₀ hg a = a) :
    ∃ n : ℤ, ordVal (τ₀ : ℂ) a = WithZero.exp (-((e : ℤ) * n)) := by
  obtain ⟨f, hf, rfl⟩ := MeroGerm.exists_eq_mk a
  rw [rot_mk, MeroGerm.mk_eq_mk] at hfix
  have htop : meromorphicOrderAt f (τ₀ : ℂ) ≠ ⊤ := by
    intro h
    exact ha (MeroGerm.mk_eq_zero_iff.2 (meromorphicOrderAt_eq_top_iff.1 h))
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
  obtain ⟨h, hha, hh0, hfh⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
  have hG := tendsto_moeb g τ₀ hg
  have hζ0 : ζ ≠ 0 := hζ.ne_zero he
  have hslope : Tendsto (fun z => (moeb g z - τ₀) / (z - τ₀)) (𝓝[≠] (τ₀ : ℂ)) (𝓝 ζ) := by
    have hD : HasDerivAt (moeb g) ζ (τ₀ : ℂ) := hd ▸ (analyticAt_moeb g τ₀).differentiableAt.hasDerivAt
    have := hasDerivAt_iff_tendsto_slope.1 hD
    refine this.congr fun z => ?_
    rw [slope_def_field, moeb_fixed g τ₀ hg]
  have hcont : Tendsto h (𝓝 (τ₀ : ℂ)) (𝓝 (h τ₀)) := hha.continuousAt.tendsto
  have hlim : Tendsto (fun z => ((moeb g z - τ₀) / (z - τ₀)) ^ n * (h (moeb g z) / h z)) (𝓝[≠] (τ₀ : ℂ))
      (𝓝 (ζ ^ n * (h τ₀ / h τ₀))) :=
    (hslope.zpow₀ n (Or.inl hζ0)).mul ((hcont.comp (hG.mono_right nhdsWithin_le_nhds)).div
      (hcont.mono_left nhdsWithin_le_nhds) hh0)
  have hone : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), ((moeb g z - τ₀) / (z - τ₀)) ^ n * (h (moeb g z) / h z) = 1 := by
    have hne : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), h z ≠ 0 :=
      (hcont.eventually_ne hh0).filter_mono nhdsWithin_le_nhds
    filter_upwards [hfh, hG.eventually hfh, hfix, hne, hG.eventually hne, self_mem_nhdsWithin,
      hG.eventually self_mem_nhdsWithin] with z h1 h2 h3 h4 h5 h6 h7
    simp only [Function.comp_apply, smul_eq_mul] at h1 h2 h3
    have hz : z - τ₀ ≠ 0 := sub_ne_zero.2 h6
    have hm : moeb g z - τ₀ ≠ 0 := sub_ne_zero.2 h7
    rw [h3, h1] at h2
    rw [div_zpow, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (zpow_ne_zero _ hz) h4)]
    exact h2.symm
  have hlim1 : Tendsto (fun z => ((moeb g z - τ₀) / (z - τ₀)) ^ n * (h (moeb g z) / h z)) (𝓝[≠] (τ₀ : ℂ))
      (𝓝 1) := tendsto_const_nhds.congr' (hone.mono fun z hz => hz.symm)
  have hpow : ζ ^ n = 1 := by
    have := tendsto_nhds_unique hlim hlim1
    rwa [div_self hh0, mul_one] at this
  obtain ⟨k, rfl⟩ := (hζ.zpow_eq_one_iff_dvd n).1 hpow
  exact ⟨k, by rw [ordVal_mk, ← hn, toVal_coe]⟩

/-! ### Composition with $g$ permutes the embeddings $\sigma_c$ -/

theorem rot_polyToMero (p : ℚ[X]) : rot g τ₀ hg (polyToMero τ₀ p) = polyToMero τ₀ p := by
  rw [polyToMero_eq_mk, rot_mk, MeroGerm.mk_eq_mk]
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [Function.comp_apply, polyFun_apply, moeb, ofComplex_apply, jFun_smul]

theorem rot_comp_ratToMero : (rot g τ₀ hg).comp (ratToMero τ₀) = ratToMero τ₀ :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X]) (RingHom.ext fun p => by
    simp only [RingHom.comp_apply, ratToMero_algebraMap, rot_polyToMero])

/-- Composition with $g$ as a $\mathbb Q(j)$-algebra map ($j \circ g = j$). -/
def rotAlg : FinField τ₀ →ₐ[RatFunc ℚ] FinField τ₀ :=
  { rot g τ₀ hg with
    commutes' := fun x => by
      rw [algebraMap_finField]
      exact congrFun (congrArg DFunLike.coe (rot_comp_ratToMero g τ₀ hg)) x }

theorem rotAlg_apply (a : FinField τ₀) : rotAlg g τ₀ hg a = rot g τ₀ hg a := rfl

variable (N : ℕ) [NeZero N]

theorem rot_rootGerm (c : Cosets N) : rot g τ₀ hg (rootGerm τ₀ N c) = rootGerm τ₀ N (g⁻¹ • c) := by
  rw [rootGerm, rootGerm, rot_mk, MeroGerm.mk_eq_mk]
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [Function.comp_apply, moeb, ofComplex_apply]
  have := cosetRoot_smul (one_le_N N) g⁻¹ c (g • ofComplex z)
  rw [inv_smul_smul] at this
  exact this.symm

/-- **$\mathrm{rot}_g \circ \sigma_c = \sigma_{g^{-1} c}$.** -/
theorem rotAlg_comp_finEmb (c : Cosets N) :
    (rotAlg g τ₀ hg).comp (finEmb τ₀ N c) = finEmb τ₀ N (g⁻¹ • c) :=
  AdjoinRoot.algHom_ext (by
    rw [AlgHom.comp_apply, finEmb_root, finEmb_root, rotAlg_apply]
    exact rot_rootGerm g τ₀ hg N c)

end NumberFieldKB.ModularCurves
