import NumberFieldKB.ModularCurves.ComplexEmb
import NumberFieldKB.ModularCurves.FiniteValuation

/-!
# $\mathbb C(j)$ in the meromorphic germs at a point of $\mathbb H$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196). The complex version of
`FiniteFibre.lean` and `FiniteValuation.lean`: $r \mapsto r(j)$ embeds $\mathbb C(j)$ into the germs at
$\tau_0 \in \mathbb H$ (`ratToMeroC`), compatibly with $\mathbb Q(j)$ (`ratToMeroC_comp`), and if $q \in \mathbb C[X]$
is irreducible with $q(j(\tau_0)) = 0$ and $j - j(\tau_0)$ has order $m$ at $\tau_0$, the order valuation induces
$v_q^m$ on $\mathbb C(j)$ (`finVal_algebraMapC`). The embeddings $\sigma_c$ extend to $\mathbb C(X_0(N))$
(`finEmbC`), and stay distinct.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-! ### $\mathbb C(j)$ in the germs at $\tau_0$ -/

/-- $p \mapsto (z \mapsto p(j(z)))$, complex coefficients. -/
def polyFunC : ℂ[X] →+* (ℂ → ℂ) :=
  eval₂RingHom (Pi.constRingHom ℂ ℂ) (jFun ∘ ofComplex)

theorem polyFunC_apply (p : ℂ[X]) (z : ℂ) : polyFunC p z = p.eval (jFun (ofComplex z)) := by
  change Pi.evalRingHom (fun _ : ℂ => ℂ) z (polyFunC p) = _
  rw [polyFunC, coe_eval₂RingHom, Polynomial.hom_eval₂]
  rfl

theorem polyFunC_eq_comp (p : ℂ[X]) : polyFunC p = (fun w : ℂ => p.eval w) ∘ (jFun ∘ ofComplex) :=
  funext fun z => polyFunC_apply p z

theorem analyticAt_polyFunC (p : ℂ[X]) (τ : ℍ) : AnalyticAt ℂ (polyFunC p) (τ : ℂ) := by
  rw [polyFunC_eq_comp]
  exact ((Polynomial.differentiable p).analyticAt _).comp (analyticAt_jFun τ)

variable (τ₀ : ℍ)

/-- $\mathbb C[j] \to$ `MeroGerm τ₀`. -/
def polyToMeroC : ℂ[X] →+* MeroGerm (τ₀ : ℂ) :=
  ((Filter.Germ.coeRingHom (𝓝[≠] (τ₀ : ℂ))).comp polyFunC).codRestrict (meroSubring (τ₀ : ℂ))
    fun p => ⟨polyFunC p, (analyticAt_polyFunC p τ₀).meromorphicAt, rfl⟩

theorem polyToMeroC_eq_mk (p : ℂ[X]) :
    polyToMeroC τ₀ p = MeroGerm.mk (polyFunC p) (analyticAt_polyFunC p τ₀).meromorphicAt := rfl

theorem polyToMeroC_injective : Function.Injective (polyToMeroC τ₀) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [polyToMeroC_eq_mk, MeroGerm.mk_eq_zero_iff] at hp
  have h1 : ∀ᶠ z in 𝓝[≠] τ₀, p.eval (jFun z) = 0 := by
    refine eventually_of_comp_ofComplex (p := fun z => p.eval (jFun z) = 0) ?_
    filter_upwards [hp] with w hw
    rw [← polyFunC_apply]
    exact hw
  by_contra hp0
  have h2 := (eventually_codiscrete_iff_forall_eventually_nhdsNE.1
    (eventually_codiscrete_eval_jFun_ne_zero hp0)) τ₀
  exact (h1.and h2).exists.elim fun _ h => h.2 h.1

/-- $\mathbb C(j) \to$ `MeroGerm τ₀`. -/
def ratToMeroC : RatFunc ℂ →+* MeroGerm (τ₀ : ℂ) :=
  RatFunc.liftRingHom (polyToMeroC τ₀)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyToMeroC_injective τ₀))

theorem ratToMeroC_algebraMap (p : ℂ[X]) :
    ratToMeroC τ₀ (algebraMap ℂ[X] (RatFunc ℂ) p) = polyToMeroC τ₀ p := by
  rw [ratToMeroC, RatFunc.liftRingHom_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

instance : Algebra (RatFunc ℂ) (FinField τ₀) := (ratToMeroC τ₀).toAlgebra

theorem algebraMap_finFieldC (x : RatFunc ℂ) : algebraMap (RatFunc ℂ) (FinField τ₀) x = ratToMeroC τ₀ x := rfl

theorem polyToMeroC_map (p : ℚ[X]) : polyToMeroC τ₀ (p.map (algebraMap ℚ ℂ)) = polyToMero τ₀ p := by
  apply Subtype.ext
  change ((polyFunC (p.map (algebraMap ℚ ℂ)) : ℂ → ℂ) : PGerm (τ₀ : ℂ)) = ((polyFun p : ℂ → ℂ) : PGerm (τ₀ : ℂ))
  congr 1
  funext z
  rw [polyFunC_apply, polyFun_apply, eval_map_algebraMap]

/-- **The two structures are compatible**: $\mathbb Q(j) \to \mathbb C(j) \to$ germs is $\mathbb Q(j) \to$ germs. -/
theorem ratToMeroC_comp :
    (algebraMap (RatFunc ℂ) (FinField τ₀)).comp ratFuncQC = algebraMap (RatFunc ℚ) (FinField τ₀) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply, ratFuncQC_algebraMap, polyQC, algebraMap_finFieldC, algebraMap_finField,
    ratToMeroC_algebraMap, ratToMero_algebraMap]
  exact polyToMeroC_map τ₀ p

/-! ### The order valuation on $\mathbb C(j)$ -/

section Valuation

variable {q : ℂ[X]} (hq : Irreducible q) (hroot : q.eval (jFun τ₀) = 0) {m : ℕ}
  (hm : analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun τ₀) (τ₀ : ℂ) = m)

theorem finVal_polyToMeroC_of_eval_ne_zero {p : ℂ[X]} (hp : p.eval (jFun τ₀) ≠ 0) :
    finVal τ₀ (polyToMeroC τ₀ p) = 1 := by
  rw [finVal, polyToMeroC_eq_mk, ordVal_mk_of_analyticAt (analyticAt_polyFunC p τ₀) (n := 0)]
  · rfl
  · rw [Nat.cast_zero, analyticOrderAt_eq_zero]
    right
    rw [polyFunC_apply, ofComplex_apply]
    exact hp

include hq hroot in
theorem associated_of_eval_eq_zero {p : ℂ[X]} (hp : Irreducible p) (hp0 : p.eval (jFun τ₀) = 0) :
    Associated q p := by
  have h1 := (irreducible_X_sub_C (jFun τ₀)).associated_of_dvd hq (dvd_iff_isRoot.2 hroot)
  have h2 := (irreducible_X_sub_C (jFun τ₀)).associated_of_dvd hp (dvd_iff_isRoot.2 hp0)
  exact h1.symm.trans h2

include hm in
theorem finVal_polyToMeroC_of_root {p : ℂ[X]} (hp : Irreducible p) (hp0 : p.eval (jFun τ₀) = 0) :
    finVal τ₀ (polyToMeroC τ₀ p) = WithZero.exp (-(m : ℤ)) := by
  refine ordVal_mk_of_analyticAt (analyticAt_polyFunC p τ₀) ?_
  have hf : AnalyticAt ℂ (fun w : ℂ => p.eval w) ((jFun ∘ ofComplex) (τ₀ : ℂ)) :=
    (Polynomial.differentiable p).analyticAt _
  rw [polyFunC_eq_comp, hf.analyticOrderAt_comp (analyticAt_jFun τ₀)]
  have hτ : (jFun ∘ ofComplex) (τ₀ : ℂ) = jFun τ₀ := by simp [ofComplex_apply]
  rw [hτ, hm]
  have h1 : analyticOrderAt (fun w : ℂ => p.eval w) (jFun τ₀) = 1 := by
    refine analyticOrderAt_eq_one_of_zero (by rw [← hτ]; exact hf) hp0 ?_
    rw [Polynomial.deriv]
    have h := Polynomial.Separable.aeval_derivative_ne_zero (Irreducible.separable hp) (x := jFun τ₀)
      (by rwa [coe_aeval_eq_eval])
    rwa [coe_aeval_eq_eval] at h
  rw [h1, one_mul]

open scoped Classical in
include hq hroot hm in
/-- The order at $\tau_0$ of $r(j)$ is $m\, v_q(r)$, for polynomials $r \in \mathbb C[X]$. -/
theorem finVal_polyToMeroC (p : ℂ[X]) :
    finVal τ₀ (polyToMeroC τ₀ p) = (Place.adicOfIrreducible hq).valuation (algebraMap ℂ[X] (RatFunc ℂ) p) ^ m := by
  have hm0 := pos_of_order_eq τ₀ hm
  induction p using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp [zero_pow hm0.ne']
  | h₂ u hu =>
    obtain ⟨a, ha, rfl⟩ := Polynomial.isUnit_iff.1 hu
    rw [finVal_polyToMeroC_of_eval_ne_zero τ₀ (by simpa using ha.ne_zero),
      Place.valuation_eq_exp_neg_ord _ (RatFunc.algebraMap_ne_zero (by simpa using ha.ne_zero)),
      Place.ord_adicOfIrreducible_algebraMap hq (by simpa using ha.ne_zero)]
    rw [multiplicity_eq_zero_of_not_dvd (fun h => hq.not_isUnit (isUnit_of_dvd_unit h hu))]
    simp
  | h₃ a p ha hp ih =>
    rw [map_mul, map_mul, map_mul, map_mul, mul_pow, ih]
    congr 1
    by_cases hp0 : p.eval (jFun τ₀) = 0
    · rw [finVal_polyToMeroC_of_root τ₀ hm hp.irreducible hp0, Place.valuation_eq_exp_neg_ord _
        (RatFunc.algebraMap_ne_zero hp.ne_zero), Place.ord_adicOfIrreducible_algebraMap_irreducible hq hp.irreducible,
        ← WithZero.exp_nsmul]
      simp [associated_of_eval_eq_zero τ₀ hq hroot hp.irreducible hp0]
    · rw [finVal_polyToMeroC_of_eval_ne_zero τ₀ hp0, Place.valuation_eq_exp_neg_ord _
        (RatFunc.algebraMap_ne_zero hp.ne_zero), Place.ord_adicOfIrreducible_algebraMap_irreducible hq hp.irreducible,
        ite_eq_right_iff.2 fun hqp => absurd (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hqp.dvd hroot) hp0]
      simp

include hq hroot hm in
/-- **The order valuation at $\tau_0$ induces $v_q^m$ on $\mathbb C(j)$**, where $q(j(\tau_0)) = 0$ and $m$ is the
order of $j - j(\tau_0)$ at $\tau_0$. -/
theorem finVal_algebraMapC (x : RatFunc ℂ) :
    finVal τ₀ (algebraMap (RatFunc ℂ) (FinField τ₀) x) = (Place.adicOfIrreducible hq).valuation x ^ m := by
  rw [algebraMap_finFieldC, ratToMeroC, RatFunc.liftRingHom_apply, map_div₀,
    finVal_polyToMeroC τ₀ hq hroot hm, finVal_polyToMeroC τ₀ hq hroot hm, ← div_pow, ← map_div₀,
    RatFunc.num_div_denom]

end Valuation

/-! ### The embeddings $\sigma_c$ of $\mathbb C(X_0(N))$ -/

variable (N : ℕ) [NeZero N]

/-- **The embedding $\sigma_c$ of $\mathbb C(X_0(N))$ at $\tau_0$**: $j \mapsto j$, $j_N \mapsto j_N \circ
\gamma_c^{-1}$, extending `finEmb`. -/
def finEmbC (c : Cosets N) : X0C N →ₐ[RatFunc ℂ] FinField τ₀ := extC (ratToMeroC_comp τ₀) (finEmb τ₀ N c)

theorem finEmbC_toX0C (c : Cosets N) (z : X0 N) : finEmbC τ₀ N c (toX0C N z) = finEmb τ₀ N c z :=
  extC_toX0C _ _ z

theorem finEmbC_injective : Function.Injective (finEmbC τ₀ N) :=
  extC_injective (ratToMeroC_comp τ₀) (finEmb_injective τ₀ N)

theorem card_cosets_eq_finrankC : Fintype.card (Cosets N) = Module.finrank (RatFunc ℂ) (X0C N) := by
  rw [finrank_X0C, card_cosets]

end NumberFieldKB.ModularCurves
