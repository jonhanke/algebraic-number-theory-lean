import NumberFieldKB.ModularCurves.ComplexElliptic

/-!
# Moving the germs of $\mathbb C(X_0(N))$ between points of $\mathbb H$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §3 (Proposition 3.3 and Corollary 3.4, pdf p. 199). For
$g \in \mathrm{SL}_2(\mathbb Z)$ and $\tau \in \mathbb H$, composition with $z \mapsto g z$ maps the meromorphic germs
at $g\tau$ to those at $\tau$ (`transport`), preserving orders (`ordVal_transport`, $g'(\tau) \ne 0$), and carries
the embedding $\sigma_c$ at $g\tau$ to $\sigma_{g^{-1}c}$ at $\tau$ (`transport_finEmbC`). So the order of
$\sigma_c(h)$ at $\tau$ is the order at $\gamma_c^{-1}\tau$ of the germ of $h$ itself, $\sigma_{c_0}(h)$ for the trivial
coset $c_0$ (`finVal_finEmbC_eq`), and that germ is the germ of the function $h(j, j_N)$
(`finEmbC_one_root`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped MatrixGroups WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable (g : SL(2, ℤ)) (τ : ℍ)

theorem tendsto_moeb_smul : Tendsto (moeb g) (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((g • τ : ℍ) : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := (analyticAt_moeb g τ).continuousAt
    rw [ContinuousAt, moeb_coe] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have hU : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
      nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
    filter_upwards [hU, self_mem_nhdsWithin] with z hz hne
    intro h
    apply hne
    have h1 : g • ofComplex z = g • τ := UpperHalfPlane.ext h
    have h2 := smul_left_cancel g h1
    have h3 := congrArg (fun w : ℍ => (w : ℂ)) h2
    simp only [ofComplex_apply_of_im_pos hz] at h3
    exact h3

theorem deriv_moeb_ne_zero : deriv (moeb g) (τ : ℂ) ≠ 0 := by
  rw [deriv_moeb]
  exact one_div_ne_zero (pow_ne_zero _ (denom_ne_zero _ _))

/-- **Composition with $g$**: meromorphic germs at $g\tau$ to meromorphic germs at $\tau$. -/
def transport : MeroGerm ((g • τ : ℍ) : ℂ) →+* MeroGerm (τ : ℂ) where
  toFun a := ⟨a.1.compTendsto (moeb g) (tendsto_moeb_smul g τ), by
    obtain ⟨_, f, hf, rfl⟩ := a
    refine ⟨f ∘ moeb g, ?_, (Filter.Germ.coe_compTendsto f _).symm⟩
    exact MeromorphicAt.comp_analyticAt (by rw [moeb_coe]; exact hf) (analyticAt_moeb g τ)⟩
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

theorem transport_mk (f : ℂ → ℂ) (hf : MeromorphicAt f ((g • τ : ℍ) : ℂ)) :
    transport g τ (MeroGerm.mk f hf) = MeroGerm.mk (f ∘ moeb g)
      (MeromorphicAt.comp_analyticAt (by rw [moeb_coe]; exact hf) (analyticAt_moeb g τ)) := rfl

/-- **Composition with $g$ preserves orders.** -/
theorem ordVal_transport (a : MeroGerm ((g • τ : ℍ) : ℂ)) :
    ordVal (τ : ℂ) (transport g τ a) = ordVal ((g • τ : ℍ) : ℂ) a := by
  obtain ⟨f, hf, rfl⟩ := MeroGerm.exists_eq_mk a
  rw [transport_mk, ordVal_mk, ordVal_mk, meromorphicOrderAt_comp_of_deriv_ne_zero (analyticAt_moeb g τ)
    (deriv_moeb_ne_zero g τ), moeb_coe]

theorem transport_polyToMeroC (p : ℂ[X]) : transport g τ (polyToMeroC (g • τ) p) = polyToMeroC τ p := by
  rw [polyToMeroC_eq_mk, transport_mk, polyToMeroC_eq_mk, MeroGerm.mk_eq_mk]
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [Function.comp_apply, polyFunC_apply, moeb, ofComplex_apply, jFun_smul]

theorem transport_comp_ratToMeroC : (transport g τ).comp (ratToMeroC (g • τ)) = ratToMeroC τ :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℂ[X]) (RingHom.ext fun p => by
    simp only [RingHom.comp_apply, ratToMeroC_algebraMap, transport_polyToMeroC])

/-- Composition with $g$ as a $\mathbb C(j)$-algebra map. -/
def transportAlg : FinField (g • τ) →ₐ[RatFunc ℂ] FinField τ :=
  { transport g τ with
    commutes' := fun x => by
      rw [algebraMap_finFieldC, algebraMap_finFieldC]
      exact congrFun (congrArg DFunLike.coe (transport_comp_ratToMeroC g τ)) x }

theorem transportAlg_apply (a : FinField (g • τ)) : transportAlg g τ a = transport g τ a := rfl

variable (N : ℕ) [NeZero N]

theorem transport_rootGerm (c : Cosets N) : transport g τ (rootGerm (g • τ) N c) = rootGerm τ N (g⁻¹ • c) := by
  rw [rootGerm, rootGerm, transport_mk, MeroGerm.mk_eq_mk]
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [Function.comp_apply, moeb, ofComplex_apply]
  have := cosetRoot_smul (one_le_N N) g⁻¹ c (g • ofComplex z)
  rw [inv_smul_smul] at this
  exact this.symm

/-- **$\mathrm{transport}_g \circ \sigma_c = \sigma_{g^{-1} c}$** on $\mathbb C(X_0(N))$. -/
theorem transportAlg_comp_finEmbC (c : Cosets N) :
    (transportAlg g τ).comp (finEmbC (g • τ) N c) = finEmbC τ N (g⁻¹ • c) :=
  AdjoinRoot.algHom_ext (by
    rw [AlgHom.comp_apply, finEmbC_root, finEmbC_root, transportAlg_apply]
    exact transport_rootGerm g τ N c)

theorem transport_finEmbC (c : Cosets N) (h : X0C N) :
    transport g τ (finEmbC (g • τ) N c h) = finEmbC τ N (g⁻¹ • c) h :=
  congrArg (fun φ : X0C N →ₐ[RatFunc ℂ] FinField τ => φ h) (transportAlg_comp_finEmbC g τ N c)

/-- The trivial coset. -/
abbrev cosetOne : Cosets N := ((1 : SL(2, ℤ)) : Cosets N)

/-- **The order of $\sigma_c(h)$ at $\tau$ is the order of the germ of $h$ at $\gamma_c^{-1}\tau$.** -/
theorem finVal_finEmbC_eq (c : Cosets N) (h : X0C N) :
    finVal τ (finEmbC τ N c h) =
      finVal ((Quotient.out c)⁻¹ • τ) (finEmbC ((Quotient.out c)⁻¹ • τ) N (cosetOne N) h) := by
  set γ := Quotient.out c
  have hc : (γ⁻¹)⁻¹ • cosetOne N = c := by
    rw [inv_inv, cosetOne, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact QuotientGroup.out_eq' c
  have h1 := transport_finEmbC γ⁻¹ τ N (cosetOne N) h
  rw [hc] at h1
  rw [← h1]
  exact ordVal_transport γ⁻¹ τ _

/-- The germ of $j_N$ at $\tau$ is $\sigma_{c_0}(j_N)$. -/
theorem finEmbC_one_root : finEmbC τ N (cosetOne N) (AdjoinRoot.root _) =
    MeroGerm.mk (jN N ∘ ofComplex)
      (analyticAt_comp_ofComplex (jN_mdifferentiable (one_le_N N)) τ).meromorphicAt := by
  rw [finEmbC_root, rootGerm, MeroGerm.mk_eq_mk]
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [Function.comp_apply, cosetOne]
  rw [cosetRoot_mk (one_le_N N), inv_one, one_smul]

end NumberFieldKB.ModularCurves
