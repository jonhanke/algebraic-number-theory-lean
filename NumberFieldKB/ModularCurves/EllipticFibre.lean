import NumberFieldKB.ModularCurves.Rotation

/-!
# The fibres of $j : X_0(N) \to X_0(1)$ over $j = 0$ and $j = 1728$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196). Let $g \in \mathrm{SL}_2(\mathbb Z)$ fix
$\tau_0 \in \mathbb H$ with $g'(\tau_0)$ a primitive $e$-th root of unity, and let $j - j(\tau_0)$ have order $e$ at
$\tau_0$ ($\tau_0 = \rho$, $g = ST$, $e = 3$; $\tau_0 = i$, $g = S$, $e = 2$). For the embedding $\sigma_c$ at $\tau_0$:

* if $g$ fixes the coset $c$, the scaling factor of $\sigma_c$ is $e$ (`scale_finEmb_of_fixed`): every element of
  $\sigma_c(\mathbb Q(X_0(N)))$ is invariant under $g$, so its order is divisible by $e$;
* if $g$ moves $c$, the scaling factor is $1$ (`scale_finEmb_of_not_fixed`), given Milne's Proposition 2.2
  (`JInjective`, $j$ is injective on $\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$).

Hence $e \cdot r(P) = \mu + (e - 1)\,\#\{c : g c = c\}$ (`mul_geomCount_eq_of_elliptic`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped WithZero MatrixGroups

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-- See `RiemannHurwitz.lean`: the $\mathbb Q$-algebra structure of $\mathbb Q(t)$ through $\mathbb Q[t]$. -/
local instance (priority := high) ratFuncAlgebraRatEll : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (N : ℕ) [NeZero N] (τ₀ : ℍ) (g : SL(2, ℤ)) (hg : g • τ₀ = τ₀) {e : ℕ} (he : e ≠ 0) {ζ : ℂ}
  (hζ : IsPrimitiveRoot ζ e) (hd : deriv (moeb g) (τ₀ : ℂ) = ζ) {q : ℚ[X]} (hq : Irreducible q)
  (hroot : aeval (jFun τ₀) q = 0)
  (hm : analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun τ₀) (τ₀ : ℂ) = e)

include hg hζ hd in
/-- **A coset fixed by $g$ has scaling factor $e$.** -/
theorem scale_finEmb_of_fixed (c : Cosets N) (hc : g⁻¹ • c = c) :
    scale (isFunctionField_X0 N) (finVal_algebraMap τ₀ hq hroot hm) (finEmb τ₀ N c) (Nat.pos_of_ne_zero he) =
      e := by
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  set hvF := finVal_algebraMap τ₀ hq hroot hm
  set P' := placeOf (isFunctionField_X0 N) hvF (finEmb τ₀ N c) (Nat.pos_of_ne_zero he)
  have hs := scale_mul_ramificationIdx (isFunctionField_X0 N) hvF (finEmb τ₀ N c) (Nat.pos_of_ne_zero he)
  have hpos := scale_pos (isFunctionField_X0 N) hvF (finEmb τ₀ N c) (Nat.pos_of_ne_zero he)
  obtain ⟨π, hπ⟩ := P'.ord_surjective 1
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have hv := valuation_apply_eq_exp (isFunctionField_X0 N) hvF (finEmb τ₀ N c) (Nat.pos_of_ne_zero he) hπ0
  rw [hπ, mul_one] at hv
  have hfix : rot g τ₀ hg (finEmb τ₀ N c π) = finEmb τ₀ N c π := by
    have := congrArg (fun φ : X0 N →ₐ[RatFunc ℚ] FinField τ₀ => φ π) (rotAlg_comp_finEmb g τ₀ hg N c)
    simpa only [AlgHom.comp_apply, rotAlg_apply, hc] using this
  have hne : finEmb τ₀ N c π ≠ 0 := (map_ne_zero_iff _ (finEmb τ₀ N c).toRingHom.injective).2 hπ0
  obtain ⟨n, hn⟩ := exists_ordVal_eq_of_rot_eq g τ₀ hg he hζ hd hne hfix
  change finVal τ₀ _ = _ at hn
  rw [hn, WithZero.exp_inj, neg_inj] at hv
  -- scale = e n and scale * E = e
  have hE := Place.ramificationIdx_pos (RatFunc ℚ) P'
  have he' : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  rw [← hv] at hs hpos ⊢
  have hn1 : n * (Place.ramificationIdx (RatFunc ℚ) P' : ℤ) = 1 := by
    have : (e : ℤ) * (n * Place.ramificationIdx (RatFunc ℚ) P') = e * 1 := by rw [mul_one, ← mul_assoc]; exact hs
    exact mul_left_cancel₀ he'.ne' this
  have hn0 : 0 < n := by
    by_contra h
    have h' := not_lt.1 h
    nlinarith
  have : n = 1 := by
    have hE' : (1 : ℤ) ≤ Place.ramificationIdx (RatFunc ℚ) P' := by exact_mod_cast hE
    nlinarith
  rw [this, mul_one]

/-! ### The order of $m(j_N \circ \gamma_c^{-1})$, $m$ the minimal polynomial of its value at $\tau_0$ -/

omit [NeZero N] in
theorem evalQ2_ratCast (G : ℚ[X][X]) (a : ℚ) (y : ℂ) :
    evalQ2 G (a : ℂ) y = aeval y (G.map (evalRingHom a)) := by
  rw [evalQ2, aeval_def, eval₂_map]
  congr 1
  refine Polynomial.ringHom_ext (fun r => ?_) ?_
  · simp
  · simp

/-- If $j(\tau_0) \in \mathbb Q$, the value $j_N(\gamma_c^{-1}\tau_0)$ is algebraic over $\mathbb Q$ (a root of
$F_N(j(\tau_0), Y)$). -/
theorem isIntegral_cosetRoot {a : ℚ} (ha : jFun τ₀ = a) (c : Cosets N) : IsIntegral ℚ (cosetRoot N c τ₀) := by
  refine ⟨(modPolyQ (prop2_4' N)).map (evalRingHom a), (modPolyQ_monic _).map _, ?_⟩
  have h := evalQ2_modPolyQ_cosetRoot N c τ₀
  rw [ha, evalQ2_ratCast, aeval_def] at h
  exact h

/-- The element $m(j_N)$ of $\mathbb Q(X_0(N))$, for $m \in \mathbb Q[Y]$. -/
def constPolyElt (m : ℚ[X]) : X0 N :=
  AdjoinRoot.mk _ ((m.map (C : ℚ →+* ℚ[X])).map (algebraMap ℚ[X] (RatFunc ℚ)))

omit [NeZero N] in
theorem evalQ2_map_C (m : ℚ[X]) (x y : ℂ) : evalQ2 (m.map (C : ℚ →+* ℚ[X])) x y = aeval y m := by
  rw [evalQ2, eval₂_map, aeval_def]
  congr 1
  ext r
  simp

/-- $\sigma_c(m(j_N))$ is the germ of $m(j_N \circ \gamma_c^{-1})$. -/
theorem finEmb_constPolyElt (c : Cosets N) (m : ℚ[X]) :
    ((finEmb τ₀ N c (constPolyElt N m) : MeroGerm (τ₀ : ℂ)) : PGerm (τ₀ : ℂ)) =
      ((fun z => aeval (cosetRoot N c (ofComplex z)) m : ℂ → ℂ) : PGerm (τ₀ : ℂ)) := by
  have h1 : finEmb τ₀ N c (constPolyElt N m) =
      ((m.map (C : ℚ →+* ℚ[X])).map (algebraMap ℚ[X] (RatFunc ℚ))).eval₂ (algebraMap (RatFunc ℚ) (FinField τ₀))
        (rootGerm τ₀ N c) := AdjoinRoot.lift_mk (h := aeval_rootGerm τ₀ N c) _
  have hcomp : (algebraMap (RatFunc ℚ) (FinField τ₀)).comp (algebraMap ℚ[X] (RatFunc ℚ)) = polyToMero τ₀ :=
    RingHom.ext fun p => ratToMero_algebraMap τ₀ p
  rw [h1, Polynomial.eval₂_map, hcomp, rootGerm, val_eval₂_polyToMero]
  congr 1
  funext z
  exact evalQ2_map_C m _ _

/-- $j_N \circ \gamma_c^{-1} = j \circ B_c$ with $B_c(z) = N \gamma_c^{-1} z$. -/
def cosetMoeb (c : Cosets N) (z : ℂ) : ℂ := (N : ℂ) * moeb (Quotient.out c)⁻¹ z

omit [NeZero N] in
theorem cosetRoot_comp_eq (c : Cosets N) :
    cosetRoot N c ∘ ofComplex = (jFun ∘ ofComplex) ∘ cosetMoeb N c := by
  funext z
  rfl

omit [NeZero N] in
theorem analyticAt_cosetMoeb (c : Cosets N) : AnalyticAt ℂ (cosetMoeb N c) (τ₀ : ℂ) :=
  analyticAt_const.mul (analyticAt_moeb _ τ₀)

theorem deriv_cosetMoeb_ne_zero (c : Cosets N) : deriv (cosetMoeb N c) (τ₀ : ℂ) ≠ 0 := by
  have h := ((analyticAt_moeb (Quotient.out c)⁻¹ τ₀).differentiableAt.hasDerivAt.const_mul (N : ℂ)).deriv
  change deriv (fun z => (N : ℂ) * moeb (Quotient.out c)⁻¹ z) _ ≠ 0
  rw [h, deriv_moeb]
  refine mul_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne N)) (one_div_ne_zero (pow_ne_zero _ ?_))
  exact UpperHalfPlane.denom_ne_zero _ _

/-- The point $w_c = N \gamma_c^{-1} \tau_0$ of $\mathbb H$. -/
def cosetPoint (c : Cosets N) : ℍ := ofComplex (cosetMoeb N c τ₀)

theorem coe_cosetPoint (c : Cosets N) : (cosetPoint N τ₀ c : ℂ) = cosetMoeb N c τ₀ := by
  have hpos : 0 < (cosetMoeb N c τ₀).im := by
    have : (cosetMoeb N c τ₀).im = N * (((Quotient.out c)⁻¹ • τ₀ : ℍ) : ℂ).im := by
      simp [cosetMoeb, moeb_coe]
    rw [this]
    exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) (UpperHalfPlane.im_pos _)
  rw [cosetPoint, ofComplex_apply_of_im_pos hpos]

omit [NeZero N] in
theorem cosetRoot_eq_jFun_cosetPoint (c : Cosets N) : cosetRoot N c τ₀ = jFun (cosetPoint N τ₀ c) := by
  have := congrFun (cosetRoot_comp_eq N c) τ₀
  simp only [Function.comp_apply, ofComplex_apply] at this
  rw [this, cosetPoint]

/-- **The order of $j_N \circ \gamma_c^{-1} - j_N(\gamma_c^{-1}\tau_0)$ at $\tau_0$ is that of $j - j(w_c)$ at
$w_c$.** -/
theorem analyticOrderAt_cosetRoot_sub (c : Cosets N) :
    analyticOrderAt (fun z => (cosetRoot N c ∘ ofComplex) z - cosetRoot N c τ₀) (τ₀ : ℂ) =
      analyticOrderAt (fun w => (jFun ∘ ofComplex) w - jFun (cosetPoint N τ₀ c)) (cosetPoint N τ₀ c : ℂ) := by
  rw [cosetRoot_comp_eq, cosetRoot_eq_jFun_cosetPoint]
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := fun w => (jFun ∘ ofComplex) w - jFun (cosetPoint N τ₀ c))
    (analyticAt_cosetMoeb N τ₀ c) (deriv_cosetMoeb_ne_zero N τ₀ c)
  rw [← coe_cosetPoint] at h
  exact h

include hq hroot hm in
/-- **The scaling factor of $\sigma_c$ divides the order $k$ of $j - j(w_c)$ at $w_c$**, when $j(\tau_0) \in \mathbb Q$.
So it is $1$ if $k$ is prime to $e$. -/
theorem scale_finEmb_eq_one_of_coprime {a : ℚ} (ha : jFun τ₀ = a) (c : Cosets N) {k : ℕ}
    (hk : analyticOrderAt (fun w => (jFun ∘ ofComplex) w - jFun (cosetPoint N τ₀ c)) (cosetPoint N τ₀ c : ℂ) = k)
    (hcop : Nat.Coprime k e) :
    scale (isFunctionField_X0 N) (finVal_algebraMap τ₀ hq hroot hm) (finEmb τ₀ N c) (Nat.pos_of_ne_zero he) =
      1 := by
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  set hvF := finVal_algebraMap τ₀ hq hroot hm
  set y := cosetRoot N c τ₀
  have hy : IsIntegral ℚ y := isIntegral_cosetRoot N τ₀ ha c
  set mp := minpoly ℚ y
  set R : ℂ → ℂ := cosetRoot N c ∘ ofComplex
  have hR : AnalyticAt ℂ R (τ₀ : ℂ) := analyticAt_comp_ofComplex (cosetRoot_mdiff (one_le_N N) c) τ₀
  have hRτ : R (τ₀ : ℂ) = y := by simp [R, y, ofComplex_apply]
  have hF : AnalyticAt ℂ (fun w : ℂ => aeval w mp) (R (τ₀ : ℂ)) := analyticAt_id.aeval_polynomial mp
  have hcomp : AnalyticAt ℂ ((fun w : ℂ => aeval w mp) ∘ R) (τ₀ : ℂ) := hF.comp hR
  have hord : analyticOrderAt ((fun w : ℂ => aeval w mp) ∘ R) (τ₀ : ℂ) = k := by
    rw [hF.analyticOrderAt_comp hR, hRτ]
    have h1 : analyticOrderAt (fun w : ℂ => aeval w mp) y = 1 := by
      refine analyticOrderAt_eq_one_of_zero (by rw [← hRτ]; exact hF) (minpoly.aeval ℚ y) ?_
      rw [Polynomial.deriv_aeval]
      exact (minpoly.irreducible hy).separable.aeval_derivative_ne_zero (minpoly.aeval ℚ y)
    have h2 : analyticOrderAt (fun z => R z - y) (τ₀ : ℂ) = k := by
      rw [← hk, ← analyticOrderAt_cosetRoot_sub]
    rw [h1, one_mul, ← h2]
  -- the valuation of σ_c(m(j_N))
  have hmk : finEmb τ₀ N c (constPolyElt N mp) = MeroGerm.mk ((fun w : ℂ => aeval w mp) ∘ R) hcomp.meromorphicAt :=
    Subtype.ext (finEmb_constPolyElt N τ₀ c mp)
  have hval : finVal τ₀ (finEmb τ₀ N c (constPolyElt N mp)) = WithZero.exp (-(k : ℤ)) := by
    rw [hmk]
    exact ordVal_mk_of_analyticAt hcomp hord
  have hz0 : constPolyElt N mp ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm
  have hv := valuation_apply_eq_exp (isFunctionField_X0 N) hvF (finEmb τ₀ N c) (Nat.pos_of_ne_zero he) hz0
  rw [hval, WithZero.exp_inj, neg_inj] at hv
  have hs := scale_mul_ramificationIdx (isFunctionField_X0 N) hvF (finEmb τ₀ N c) (Nat.pos_of_ne_zero he)
  have hpos := scale_pos (isFunctionField_X0 N) hvF (finEmb τ₀ N c) (Nat.pos_of_ne_zero he)
  set sc := scale (isFunctionField_X0 N) hvF (finEmb τ₀ N c) (Nat.pos_of_ne_zero he)
  have hdk : sc ∣ (k : ℤ) := ⟨_, hv⟩
  have hde : sc ∣ (e : ℤ) := ⟨_, hs.symm⟩
  have hg1 : sc ∣ ((Int.gcd (k : ℤ) (e : ℤ) : ℕ) : ℤ) := Int.dvd_coe_gcd hdk hde
  rw [Int.gcd_natCast_natCast, hcop, Nat.cast_one] at hg1
  exact Int.eq_one_of_dvd_one hpos.le hg1

end NumberFieldKB.ModularCurves
