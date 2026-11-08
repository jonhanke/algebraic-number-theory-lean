import NumberFieldKB.ModularCurves.ComplexFinite
import NumberFieldKB.ModularCurves.EllipticCount

/-!
# The fibres of $j$ over $0$ and $1728$ for $\mathbb C(X_0(N))$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196). The complex version of
`EllipticFibre.lean`/`EllipticCount.lean`. The embeddings $\sigma_c$ of $\mathbb C(X_0(N))$ into the germs at
$\tau_0 \in \{\rho, i\}$ extend those of $\mathbb Q(X_0(N))$, so their scaling factors divide the rational ones
(`scale_extC_dvd`), which are $1$ for the cosets not fixed by the stabilizer; a fixed coset has scaling factor $e$
(rotation invariance, as over $\mathbb Q$). Hence $3\,r(0) = \mu + 2\nu_3$ and $2\,r(1728) = \mu + \nu_2$ also for
the fibres of $j$ on $\mathbb C(X_0(N))$ (`three_mul_geomCountC_placeJ0C`, `two_mul_geomCountC_placeJ1728C`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped MatrixGroups WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-- See `RiemannHurwitz.lean`: the $\mathbb Q$-algebra structure of $\mathbb Q(t)$ through $\mathbb Q[t]$. -/
local instance (priority := high) ratFuncAlgebraRatCEll : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-! ### Rotation commutes with $\mathbb C(j)$ -/

section Rotation

variable (g : SL(2, ℤ)) (τ₀ : ℍ) (hg : g • τ₀ = τ₀)

theorem rot_polyToMeroC (p : ℂ[X]) : rot g τ₀ hg (polyToMeroC τ₀ p) = polyToMeroC τ₀ p := by
  rw [polyToMeroC_eq_mk, rot_mk, MeroGerm.mk_eq_mk]
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [Function.comp_apply, polyFunC_apply, moeb, ofComplex_apply, jFun_smul]

theorem rot_comp_ratToMeroC : (rot g τ₀ hg).comp (ratToMeroC τ₀) = ratToMeroC τ₀ :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℂ[X]) (RingHom.ext fun p => by
    simp only [RingHom.comp_apply, ratToMeroC_algebraMap, rot_polyToMeroC])

/-- Composition with $g$ as a $\mathbb C(j)$-algebra map. -/
def rotAlgC : FinField τ₀ →ₐ[RatFunc ℂ] FinField τ₀ :=
  { rot g τ₀ hg with
    commutes' := fun x => by
      rw [algebraMap_finFieldC]
      exact congrFun (congrArg DFunLike.coe (rot_comp_ratToMeroC g τ₀ hg)) x }

theorem rotAlgC_apply (a : FinField τ₀) : rotAlgC g τ₀ hg a = rot g τ₀ hg a := rfl

variable (N : ℕ) [NeZero N]

theorem finEmbC_root (c : Cosets N) : finEmbC τ₀ N c (AdjoinRoot.root _) = rootGerm τ₀ N c := by
  rw [finEmbC, extC_root, finEmb_root]

/-- **$\mathrm{rot}_g \circ \sigma_c = \sigma_{g^{-1} c}$** on $\mathbb C(X_0(N))$. -/
theorem rotAlgC_comp_finEmbC (c : Cosets N) :
    (rotAlgC g τ₀ hg).comp (finEmbC τ₀ N c) = finEmbC τ₀ N (g⁻¹ • c) :=
  AdjoinRoot.algHom_ext (by
    rw [AlgHom.comp_apply, finEmbC_root, finEmbC_root, rotAlgC_apply]
    exact rot_rootGerm g τ₀ hg N c)

end Rotation

/-! ### The scaling factors -/

variable (N : ℕ) [NeZero N] (τ₀ : ℍ) (g : SL(2, ℤ)) (hg : g • τ₀ = τ₀) {e : ℕ} (he : e ≠ 0) {ζ : ℂ}
  (hζ : IsPrimitiveRoot ζ e) (hd : deriv (moeb g) (τ₀ : ℂ) = ζ) {q : ℂ[X]} (hq : Irreducible q)
  (hroot : q.eval (jFun τ₀) = 0)
  (hm : analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun τ₀) (τ₀ : ℂ) = e)

include hg hζ hd in
/-- **A coset fixed by $g$ has scaling factor $e$** (over $\mathbb C$). -/
theorem scale_finEmbC_of_fixed (c : Cosets N) (hc : g⁻¹ • c = c) :
    scale (isFunctionField_X0C N) (finVal_algebraMapC τ₀ hq hroot hm) (finEmbC τ₀ N c) (Nat.pos_of_ne_zero he) =
      e := by
  set hvF := finVal_algebraMapC τ₀ hq hroot hm
  set P' := placeOf (isFunctionField_X0C N) hvF (finEmbC τ₀ N c) (Nat.pos_of_ne_zero he)
  have hs := scale_mul_ramificationIdx (isFunctionField_X0C N) hvF (finEmbC τ₀ N c) (Nat.pos_of_ne_zero he)
  have hpos := scale_pos (isFunctionField_X0C N) hvF (finEmbC τ₀ N c) (Nat.pos_of_ne_zero he)
  obtain ⟨π, hπ⟩ := P'.ord_surjective 1
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have hv := valuation_apply_eq_exp (isFunctionField_X0C N) hvF (finEmbC τ₀ N c) (Nat.pos_of_ne_zero he) hπ0
  rw [hπ, mul_one] at hv
  have hfix : rot g τ₀ hg (finEmbC τ₀ N c π) = finEmbC τ₀ N c π := by
    have := congrArg (fun φ : X0C N →ₐ[RatFunc ℂ] FinField τ₀ => φ π) (rotAlgC_comp_finEmbC g τ₀ hg N c)
    simpa only [AlgHom.comp_apply, rotAlgC_apply, hc] using this
  have hne : finEmbC τ₀ N c π ≠ 0 := (map_ne_zero_iff _ (finEmbC τ₀ N c).toRingHom.injective).2 hπ0
  obtain ⟨n, hn⟩ := exists_ordVal_eq_of_rot_eq g τ₀ hg he hζ hd hne hfix
  change finVal τ₀ _ = _ at hn
  rw [hn, WithZero.exp_inj, neg_inj] at hv
  have hE := Place.ramificationIdx_pos (RatFunc ℂ) P'
  have he' : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  rw [← hv] at hs hpos ⊢
  have hn1 : n * (Place.ramificationIdx (RatFunc ℂ) P' : ℤ) = 1 := by
    have : (e : ℤ) * (n * Place.ramificationIdx (RatFunc ℂ) P') = e * 1 := by
      rw [mul_one, ← mul_assoc]; exact hs
    exact mul_left_cancel₀ he'.ne' this
  have hn0 : 0 < n := by
    by_contra h
    have h' := not_lt.1 h
    nlinarith
  have : n = 1 := by
    have hE' : (1 : ℤ) ≤ Place.ramificationIdx (RatFunc ℂ) P' := by exact_mod_cast hE
    nlinarith
  rw [this, mul_one]

/-! ### The counts over $j = 0$ and $j = 1728$ -/

omit [NeZero N] in
theorem irreducible_X_C : Irreducible (X : ℂ[X]) := irreducible_X

/-- The place $j = 0$ of $\mathbb C(j)$. -/
def placeJ0C : Place ℂ (RatFunc ℂ) := Place.adicOfIrreducible (k := ℂ) irreducible_X

/-- The place $j = 1728$ of $\mathbb C(j)$. -/
def placeJ1728C : Place ℂ (RatFunc ℂ) := Place.adicOfIrreducible (k := ℂ) (irreducible_X_sub_C (1728 : ℂ))

/-- The geometric count of a fibre of $j$ on $\mathbb C(X_0(N))$: $r(P) = \sum_{P' \mid P} f(P')$. -/
def geomCountC (P : Place ℂ (RatFunc ℂ)) : ℕ :=
  ∑ P' ∈ fibre (F' := X0C N) P, Place.relativeDegree ℂ (RatFunc ℂ) P'

/-- At $\rho$: the scaling factor of $\sigma_c$ on $\mathbb Q(X_0(N))$ is $1$ for a coset not fixed by $ST$. -/
theorem scale_finEmb_rho_of_not_fixed (c : Cosets N) (hc : ¬ (ModularGroup.S * ModularGroup.T) • c = c) :
    scale (isFunctionField_X0 N) (finVal_algebraMap ρ irreducible_X (by simp [jFun_rho])
      (analyticOrderAt_jFun_of_eq_zero ρ jFun_rho)) (finEmb ρ N c) (by norm_num : 0 < 3) = 1 := by
  have hroot : aeval (jFun ρ) (X : ℚ[X]) = 0 := by simp [jFun_rho]
  have hm := analyticOrderAt_jFun_of_eq_zero ρ jFun_rho
  have hw0 : jFun (cosetPoint N ρ c) ≠ 0 := by
    intro h0
    apply hc
    refine (inv_smul_eq_iff' N _ c).1 (smul_eq_of_jFun_cosetPoint_eq N jInjective ρ _
      (fun M hM hfix => commute_ST_of_smul_rho hM hfix) c ?_)
    rw [h0, jFun_rho]
  by_cases hw1 : jFun (cosetPoint N ρ c) = 1728
  · exact scale_finEmb_eq_one_of_coprime N ρ (by norm_num) irreducible_X hroot hm (a := 0)
      (by simp [jFun_rho]) c (k := 2) (by exact_mod_cast analyticOrderAt_jFun_of_eq_1728 _ hw1) (by norm_num)
  · exact scale_finEmb_eq_one_of_coprime N ρ (by norm_num) irreducible_X hroot hm (a := 0)
      (by simp [jFun_rho]) c (k := 1) (by exact_mod_cast analyticOrderAt_jFun_sub_eq_one _ hw0 hw1)
      (by norm_num)

/-- At $i$: the scaling factor of $\sigma_c$ on $\mathbb Q(X_0(N))$ is $1$ for a coset not fixed by $S$. -/
theorem scale_finEmb_I_of_not_fixed (c : Cosets N) (hc : ¬ ModularGroup.S • c = c) :
    scale (isFunctionField_X0 N) (finVal_algebraMap UpperHalfPlane.I irreducible_X_sub_1728
      (by simp [jFun_I]) (analyticOrderAt_jFun_of_eq_1728 _ jFun_I)) (finEmb UpperHalfPlane.I N c)
      (by norm_num : 0 < 2) = 1 := by
  have hroot : aeval (jFun UpperHalfPlane.I) (X - C 1728 : ℚ[X]) = 0 := by simp [jFun_I]
  have hm := analyticOrderAt_jFun_of_eq_1728 _ jFun_I
  have hw1 : jFun (cosetPoint N UpperHalfPlane.I c) ≠ 1728 := by
    intro h0
    apply hc
    refine (inv_smul_eq_iff' N _ c).1 (smul_eq_of_jFun_cosetPoint_eq N jInjective UpperHalfPlane.I _
      (fun M hM hfix => commute_S_of_smul_I hM hfix) c ?_)
    rw [h0, jFun_I]
  by_cases hw0 : jFun (cosetPoint N UpperHalfPlane.I c) = 0
  · exact scale_finEmb_eq_one_of_coprime N UpperHalfPlane.I (by norm_num) irreducible_X_sub_1728 hroot hm
      (a := 1728) (by simp [jFun_I]) c (k := 3) (by exact_mod_cast analyticOrderAt_jFun_of_eq_zero _ hw0)
      (by norm_num)
  · exact scale_finEmb_eq_one_of_coprime N UpperHalfPlane.I (by norm_num) irreducible_X_sub_1728 hroot hm
      (a := 1728) (by simp [jFun_I]) c (k := 1) (by exact_mod_cast analyticOrderAt_jFun_sub_eq_one _ hw0 hw1)
      (by norm_num)

/-- **$3\, r(0) = \mu + 2\nu_3$ for $\mathbb C(X_0(N))$.** -/
theorem three_mul_geomCountC_placeJ0C :
    3 * geomCountC N placeJ0C = (CongruenceSubgroup.Gamma0 N).index + 2 * nu3 N := by
  classical
  have hrootC : (X : ℂ[X]).eval (jFun ρ) = 0 := by simp [jFun_rho]
  have hm : analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun ρ) (ρ : ℂ) = ((3 : ℕ) : ℕ∞) :=
    analyticOrderAt_jFun_of_eq_zero ρ jFun_rho
  set hvC := finVal_algebraMapC ρ irreducible_X hrootC hm
  have hvF := finVal_algebraMap ρ irreducible_X (by simp [jFun_rho]) hm
  have h := mul_sum_relativeDegree_eq (isFunctionField_X0C N) hvC (finEmbC ρ N) (finEmbC_injective ρ N)
    (card_cosets_eq_finrankC N) (by norm_num : 0 < 3)
  have hsc : ∀ c, scale (isFunctionField_X0C N) hvC (finEmbC ρ N c) (by norm_num : 0 < 3) =
      if (ModularGroup.S * ModularGroup.T) • c = c then 3 else 1 := by
    intro c
    split_ifs with hc
    · exact_mod_cast scale_finEmbC_of_fixed N ρ (ModularGroup.S * ModularGroup.T) ST_smul_rho (by norm_num)
        isPrimitiveRoot_rho.inv deriv_moeb_ST_rho irreducible_X hrootC hm c ((inv_smul_eq_iff' N _ c).2 hc)
    · have hd := scale_extC_dvd (ratToMeroC_comp ρ) hvF hvC (finEmb ρ N c) (by norm_num : 0 < 3)
      rw [scale_finEmb_rho_of_not_fixed N c hc] at hd
      exact Int.eq_one_of_dvd_one (scale_pos _ _ _ _).le hd
  rw [Finset.sum_congr rfl fun c _ => hsc c, sum_ite_fixed] at h
  have h' : (3 : ℤ) * geomCountC N placeJ0C = (CongruenceSubgroup.Gamma0 N).index + 2 * nu3 N := by
    rw [geomCountC, Nat.cast_sum]
    convert h using 2
    · rfl
    · unfold nu3
      norm_num
  exact_mod_cast h'

/-- **$2\, r(1728) = \mu + \nu_2$ for $\mathbb C(X_0(N))$.** -/
theorem two_mul_geomCountC_placeJ1728C :
    2 * geomCountC N placeJ1728C = (CongruenceSubgroup.Gamma0 N).index + nu2 N := by
  classical
  have hrootC : (X - C 1728 : ℂ[X]).eval (jFun UpperHalfPlane.I) = 0 := by simp [jFun_I]
  have hm : analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun UpperHalfPlane.I) (UpperHalfPlane.I : ℂ) =
      ((2 : ℕ) : ℕ∞) :=
    analyticOrderAt_jFun_of_eq_1728 _ jFun_I
  set hvC := finVal_algebraMapC UpperHalfPlane.I (irreducible_X_sub_C (1728 : ℂ)) hrootC hm
  have hvF := finVal_algebraMap UpperHalfPlane.I irreducible_X_sub_1728 (by simp [jFun_I]) hm
  have h := mul_sum_relativeDegree_eq (isFunctionField_X0C N) hvC (finEmbC UpperHalfPlane.I N)
    (finEmbC_injective UpperHalfPlane.I N) (card_cosets_eq_finrankC N) (by norm_num : 0 < 2)
  have hsc : ∀ c, scale (isFunctionField_X0C N) hvC (finEmbC UpperHalfPlane.I N c) (by norm_num : 0 < 2) =
      if ModularGroup.S • c = c then 2 else 1 := by
    intro c
    split_ifs with hc
    · exact_mod_cast scale_finEmbC_of_fixed N UpperHalfPlane.I ModularGroup.S S_smul_I (by norm_num)
        isPrimitiveRoot_neg_one deriv_moeb_S_I (irreducible_X_sub_C (1728 : ℂ)) hrootC hm c
        ((inv_smul_eq_iff' N _ c).2 hc)
    · have hd := scale_extC_dvd (ratToMeroC_comp UpperHalfPlane.I) hvF hvC (finEmb UpperHalfPlane.I N c)
        (by norm_num : 0 < 2)
      rw [scale_finEmb_I_of_not_fixed N c hc] at hd
      exact Int.eq_one_of_dvd_one (scale_pos _ _ _ _).le hd
  rw [Finset.sum_congr rfl fun c _ => hsc c, sum_ite_fixed] at h
  have h' : (2 : ℤ) * geomCountC N placeJ1728C = (CongruenceSubgroup.Gamma0 N).index + nu2 N := by
    rw [geomCountC, Nat.cast_sum]
    convert h using 2
    · rfl
    · unfold nu2
      norm_num
  exact_mod_cast h'

end NumberFieldKB.ModularCurves
