import NumberFieldKB.ModularCurves.PlaneModel
import NumberFieldKB.MilneEC.Ch5Rational
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The modular polynomial $F_N(X, Y) \in \mathbb C[X][Y]$ (Milne, *Elliptic Curves*, Ch. V, §2)

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §2 (pdf pp. 192–193). Milne's construction of $F_N$:
the functions $j_N \circ \gamma^{-1}$, for $\gamma\Gamma_0(N)$ running over the cosets of $\Gamma_0(N)$ in
$\Gamma_0(1) = \mathrm{SL}_2(\mathbb Z)$, are permuted by $\mathrm{SL}_2(\mathbb Z)$, so the coefficients of
$$\Phi_z(Y) = \prod_{\gamma\Gamma_0(N)} \bigl(Y - j_N(\gamma^{-1}z)\bigr)$$
are holomorphic $\mathrm{SL}_2(\mathbb Z)$-invariant functions with a pole of finite order at $\infty$, hence
polynomials in $j$ (`key_poly`). This gives $F_N \in \mathbb C[X][Y]$, monic of degree $(\Gamma_0(1) : \Gamma_0(N))$
in $Y$ with $F_N(j(z), Y) = \Phi_z(Y)$, so $F_N(j, j_N) = 0$. The $j_N \circ \gamma^{-1}$ are pairwise distinct
functions (`cosetRoot_injective`, comparing the growth $|j(w)| \sim e^{2\pi \operatorname{Im} w}$ at $i\infty$), so
by the identity theorem every $G$ with $G(j, j_N) = 0$ is divisible by $F_N$.

Main result: `modularPolynomial`, the named `ModularPolynomial N` of `Ch5JFunction`, for every $N \ge 1$.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex
open scoped Manifold MatrixGroups Real

namespace NumberFieldKB.ModularCurves

local notation "Δ" => ModularForm.discriminant

open NumberFieldKB.MilneEC.V

/-! ### Growth of $j$ at $i\infty$ and distinctness of the conjugates of $j_N$ -/

/-- $|e^{-2\pi i w}| = e^{2\pi \operatorname{Im} w}$. -/
lemma norm_inv_exp (w : ℂ) : ‖1 / cexp (2 * π * I * w)‖ = Real.exp (2 * π * w.im) := by
  rw [norm_div, norm_one, Complex.norm_exp, one_div, ← Real.exp_neg]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- $j(w) = e^{-2\pi i w} + O(1)$ as $\operatorname{Im} w \to \infty$, with explicit constants. -/
lemma exists_bound_jFun : ∃ C y0 : ℝ, ∀ w : ℍ, y0 ≤ w.im →
    Real.exp (2 * π * w.im) - C ≤ ‖jFun w‖ ∧ ‖jFun w‖ ≤ Real.exp (2 * π * w.im) + C := by
  obtain ⟨C, y0, h⟩ := isBoundedAtImInfty_iff.1 jFun_sub_inv_q_isBoundedAtImInfty
  refine ⟨C, y0, fun w hw => ?_⟩
  have hb := h w hw
  have e := norm_inv_exp (w : ℂ)
  rw [UpperHalfPlane.coe_im] at e
  constructor
  · have := norm_sub_norm_le (1 / cexp (2 * π * I * w)) (1 / cexp (2 * π * I * w) - jFun w)
    rw [sub_sub_cancel, e] at this
    rw [norm_sub_rev] at hb
    linarith
  · have := norm_le_norm_add_norm_sub' (jFun w) (1 / cexp (2 * π * I * w))
    rw [e] at this
    linarith

/-- If $j_N \circ \beta = j_N$ on $\mathbb H$ for $\beta \in \mathrm{SL}_2(\mathbb Z)$, then $\beta \in \Gamma_0(N)$.
Write $N\beta z = \delta\,(gz + B)/D$ (Hermite normal form, $gD = N$); the growth of $j((gz+B)/D)$ at $i\infty$
is $e^{2\pi (g/D) \operatorname{Im} z}$ and that of $j(Nz)$ is $e^{2\pi N \operatorname{Im} z}$, so $D = 1$ and
$g = \gcd(Na, c) = N$. -/
theorem mem_gamma0_of_jN_smul {N : ℕ} (hN : 1 ≤ N) {β : SL(2, ℤ)} (h : ∀ w : ℍ, jN N (β • w) = jN N w) :
    β ∈ CongruenceSubgroup.Gamma0 N := by
  obtain ⟨δ, g, B, D, hg, hD, hgD, hgcd, hm⟩ := exists_hermite_spec hN β
  have key : ∀ w : ℍ, jFun (affPt g B D hg hD w) = jN N w := by
    intro w
    rw [← h w]
    unfold jN
    rw [hm w, jFun_smul]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hD1 : D = 1 := by
    by_contra hne
    have hD2 : 2 ≤ D := by omega
    have h2g : 2 * g ≤ N := by nlinarith
    obtain ⟨C, y0, hC⟩ := exists_bound_jFun
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have h2gR : 2 * (g : ℝ) ≤ N := by exact_mod_cast h2g
    have hD2R : (2 : ℝ) ≤ D := by exact_mod_cast hD2
    have hev : ∀ᶠ y : ℝ in atTop, (0 < y ∧ y0 ≤ N * y ∧ y0 ≤ g * y / D) ∧
        2 * |C| + 2 ≤ Real.exp (π * N * y) := by
      refine Eventually.and ?_ ?_
      · filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (|y0| / N),
          eventually_ge_atTop (|y0| * D / g)] with y hy1 hy2 hy3
        refine ⟨hy1, ?_, ?_⟩
        · rw [div_le_iff₀ hNpos] at hy2
          nlinarith [le_abs_self y0]
        · rw [le_div_iff₀ hDR]
          rw [div_le_iff₀ hgR] at hy3
          nlinarith [le_abs_self y0]
      · have : Tendsto (fun y : ℝ => π * N * y) atTop atTop :=
          tendsto_id.const_mul_atTop (by positivity)
        exact (Real.tendsto_exp_atTop.comp this).eventually_ge_atTop _
    obtain ⟨y, ⟨hy0, hyN, hyg⟩, hyt⟩ := hev.exists
    let w : ℍ := ⟨I * y, by simpa using hy0⟩
    have hwim : w.im = y := by simp [w, UpperHalfPlane.im]
    have hNw : (ofComplex ((N : ℂ) * w)).im = N * y := by
      have h1 : 0 < ((N : ℂ) * w).im := by
        simp [Complex.mul_im, w]; positivity
      rw [UpperHalfPlane.im, ofComplex_apply_of_im_pos h1]
      simp [Complex.mul_im, w]
    have haffim : (affPt g B D hg hD w).im = g * y / D := by
      rw [UpperHalfPlane.im, affPt_coe, aff_im]
      simp [w]
    have h1 := (hC _ (hNw ▸ hyN)).1
    have h2 := (hC _ (haffim ▸ hyg)).2
    rw [hNw] at h1
    rw [haffim] at h2
    have e1 : jN N w = jFun (ofComplex ((N : ℂ) * w)) := rfl
    rw [key w, e1] at h2
    have hle : 2 * π * (g * y / D) ≤ π * N * y := by
      rw [mul_div_assoc', div_le_iff₀ hDR]
      have : 0 ≤ π * y := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2gR this, mul_le_mul_of_nonneg_left hD2R
        (show 0 ≤ π * N * y by positivity)]
    have ht : Real.exp (2 * π * (g * y / D)) ≤ Real.exp (π * N * y) := Real.exp_le_exp.2 hle
    have hsq : Real.exp (2 * π * (N * y)) = Real.exp (π * N * y) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [hsq] at h1
    have hC0 := le_abs_self C
    have hpos := Real.exp_pos (π * N * y)
    nlinarith
  subst hD1
  have hgN : g = N := by simpa using hgD
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have := Int.gcd_dvd_right (N * β 0 0) (β 1 0)
  rw [← hgcd, hgN] at this
  exact this

/-! ### The conjugates $j_N \circ \gamma^{-1}$ -/

/-- The left cosets $\gamma\Gamma_0(N)$ of $\Gamma_0(N)$ in $\Gamma_0(1) = \mathrm{SL}_2(\mathbb Z)$. -/
abbrev Cosets (N : ℕ) : Type := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N

noncomputable instance (N : ℕ) [NeZero N] : Fintype (Cosets N) := Fintype.ofFinite _

/-- The conjugate $j_N \circ \gamma^{-1}$ attached to a coset $c = \gamma\Gamma_0(N)$ (computed with a chosen
representative; independent of the choice by `cosetRoot_mk`). -/
noncomputable def cosetRoot (N : ℕ) (c : Cosets N) (z : ℍ) : ℂ := jN N ((Quotient.out c)⁻¹ • z)

variable {N : ℕ}

theorem cosetRoot_mk (hN : 1 ≤ N) (γ : SL(2, ℤ)) (z : ℍ) :
    cosetRoot N (γ : Cosets N) z = jN N (γ⁻¹ • z) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) γ
  unfold cosetRoot
  rw [hh, mul_inv_rev, mul_smul]
  exact jN_smul hN (inv_mem h.2) _

theorem cosetRoot_smul (hN : 1 ≤ N) (δ : SL(2, ℤ)) (c : Cosets N) (z : ℍ) :
    cosetRoot N (δ • c) (δ • z) = cosetRoot N c z := by
  induction c using QuotientGroup.induction_on with
  | H γ =>
    rw [show δ • (γ : Cosets N) = ((δ * γ : SL(2, ℤ)) : Cosets N) from rfl, cosetRoot_mk hN,
      cosetRoot_mk hN, mul_inv_rev, mul_smul, inv_smul_smul]

/-- The conjugates $j_N \circ \gamma^{-1}$ of distinct cosets are distinct functions. -/
theorem cosetRoot_injective (hN : 1 ≤ N) : Function.Injective (cosetRoot N) := by
  intro c c' hcc
  induction c using QuotientGroup.induction_on with
  | H γ =>
  induction c' using QuotientGroup.induction_on with
  | H γ' =>
  rw [QuotientGroup.eq]
  apply mem_gamma0_of_jN_smul hN
  intro w
  have := congrFun hcc (γ' • w)
  rw [cosetRoot_mk hN, cosetRoot_mk hN, inv_smul_smul] at this
  rw [mul_smul]
  exact this

theorem cosetRoot_mdiff (hN : 1 ≤ N) (c : Cosets N) : MDiff (cosetRoot N c) := by
  obtain ⟨δ, g, B, D, hg, hD, h⟩ := exists_hermite hN (Quotient.out c)⁻¹
  have : cosetRoot N c = fun z => jFun (affPt g B D hg hD z) := by
    funext z
    unfold cosetRoot jN
    rw [h z, jFun_smul]
  rw [this]
  exact jFun_affPt_mdiff _ _ _ _ _

theorem cosetRoot_disc_bounded (hN : 1 ≤ N) (c : Cosets N) :
    ∃ n : ℕ, IsBoundedAtImInfty (fun z => cosetRoot N c z * Δ z ^ n) :=
  exists_pow_disc_bounded ((isModularFunction_jN hN).meromorphic_cusps (Quotient.out c)⁻¹)

/-! ### Coefficients of products of linear factors -/

theorem mdiff_coeff_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℍ → ℂ)
    (ha : ∀ i, MDiff (a i)) (k : ℕ) : MDiff (fun z : ℍ => ((∏ i ∈ s, (X - C (a i z) : ℂ[X])).coeff k : ℂ)) := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, coeff_one]
    exact mdifferentiable_const
  | insert i s hi ih =>
    simp_rw [Finset.prod_insert hi, mul_comm (X - C _)]
    cases k with
    | zero =>
      simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, mul_neg]
      exact ((ih 0).mul (ha i)).neg
    | succ k =>
      simp only [coeff_mul_X_sub_C]
      exact (ih k).sub ((ih (k + 1)).mul (ha i))

theorem norm_coeff_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℂ) (k : ℕ) :
    ‖(∏ i ∈ s, (X - C (x i))).coeff k‖ ≤ ∏ i ∈ s, (1 + ‖x i‖) := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, coeff_one]
    split_ifs <;> simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_comm (X - C _)]
    have hP : 0 ≤ ∏ i ∈ s, (1 + ‖x i‖) := Finset.prod_nonneg fun _ _ => by positivity
    cases k with
    | zero =>
      simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, mul_neg, norm_neg,
        norm_mul]
      nlinarith [ih 0, norm_nonneg (x i), norm_nonneg ((∏ i ∈ s, (X - C (x i))).coeff 0)]
    | succ k =>
      rw [coeff_mul_X_sub_C]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      nlinarith [ih k, ih (k + 1), norm_nonneg (x i),
        norm_nonneg ((∏ i ∈ s, (X - C (x i))).coeff (k + 1))]

/-! ### The polynomial $\Phi_z(Y) = \prod_{\gamma\Gamma_0(N)} (Y - j_N(\gamma^{-1}z))$ -/

/-- $\Phi_z(Y) = \prod_{\gamma\Gamma_0(N)} (Y - j_N(\gamma^{-1}z)) \in \mathbb C[Y]$. -/
noncomputable def rootPoly (N : ℕ) [NeZero N] (z : ℍ) : ℂ[X] :=
  ∏ c : Cosets N, (X - C (cosetRoot N c z))

variable [NeZero N]

lemma one_le_of_neZero : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)

theorem rootPoly_monic (z : ℍ) : (rootPoly N z).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem rootPoly_natDegree (z : ℍ) : (rootPoly N z).natDegree = Fintype.card (Cosets N) := by
  unfold rootPoly
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

theorem card_cosets : Fintype.card (Cosets N) = (CongruenceSubgroup.Gamma0 N).index := by
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]

theorem rootPoly_smul (δ : SL(2, ℤ)) (z : ℍ) : rootPoly N (δ • z) = rootPoly N z := by
  unfold rootPoly
  have : ∀ c : Cosets N, cosetRoot N c (δ • z) = cosetRoot N (δ⁻¹ • c) z := fun c => by
    have := cosetRoot_smul (one_le_of_neZero (N := N)) δ (δ⁻¹ • c) z
    rwa [smul_inv_smul] at this
  simp_rw [this]
  exact Equiv.prod_comp (MulAction.toPerm δ⁻¹) (fun c => X - C (cosetRoot N c z))

theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (fun z => Δ z) :=
  ModularFormClass.bdd_at_infty CuspForm.discriminant

theorem rootPoly_coeff_bounded (k : ℕ) :
    ∃ n : ℕ, IsBoundedAtImInfty (fun z => (rootPoly N z).coeff k * Δ z ^ n) := by
  classical
  have hN := (one_le_of_neZero : 1 ≤ N)
  choose n hn using fun c : Cosets N => cosetRoot_disc_bounded hN c
  refine ⟨∑ c, n c, ?_⟩
  have hΔ := isBoundedAtImInfty_disc
  have hfac : ∀ c ∈ (Finset.univ : Finset (Cosets N)),
      (fun z => ‖Δ z‖ ^ n c + ‖cosetRoot N c z * Δ z ^ n c‖) =O[atImInfty] (fun _ => (1 : ℝ)) := by
    intro c _
    have h1 : (fun z => ‖Δ z‖ ^ n c) =O[atImInfty] (fun _ => (1 : ℝ)) := by
      simpa using (hΔ.norm_left.pow (n c))
    exact h1.add (hn c).norm_left
  have hprod := Asymptotics.IsBigO.finsetProd hfac
  simp only [Finset.prod_const_one] at hprod
  refine (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)).trans hprod
  rw [one_mul, Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity), norm_mul, norm_pow,
    ← Finset.prod_pow_eq_pow_sum]
  calc ‖(rootPoly N z).coeff k‖ * ∏ c, ‖Δ z‖ ^ n c
      ≤ (∏ c, (1 + ‖cosetRoot N c z‖)) * ∏ c, ‖Δ z‖ ^ n c :=
        mul_le_mul_of_nonneg_right (norm_coeff_prod_le _ _ k) (Finset.prod_nonneg fun _ _ => by positivity)
    _ = ∏ c, (‖Δ z‖ ^ n c + ‖cosetRoot N c z * Δ z ^ n c‖) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun c _ => ?_
        rw [norm_mul, norm_pow]; ring

/-- The coefficients of $\Phi_z$ are polynomials in $j(z)$. -/
theorem exists_coeffPoly (k : ℕ) : ∃ P : ℂ[X], ∀ z, (rootPoly N z).coeff k = P.eval (jFun z) := by
  classical
  obtain ⟨n, hn⟩ := rootPoly_coeff_bounded (N := N) k
  obtain ⟨P, -, hP⟩ := key_poly n (fun z => (rootPoly N z).coeff k)
    (mdiff_coeff_prod _ _ (fun c => cosetRoot_mdiff (one_le_of_neZero (N := N)) c) k)
    (law_zero_of_invariant fun γ z => by simp only [rootPoly_smul]) hn
  exact ⟨P, hP⟩

/-- The polynomial $P_k$ with $P_k(j(z))$ the coefficient of $Y^k$ in $\Phi_z(Y)$. -/
noncomputable def coeffPoly (N : ℕ) [NeZero N] (k : ℕ) : ℂ[X] := (exists_coeffPoly (N := N) k).choose

theorem coeffPoly_eval (k : ℕ) (z : ℍ) : (coeffPoly N k).eval (jFun z) = (rootPoly N z).coeff k :=
  ((exists_coeffPoly (N := N) k).choose_spec z).symm

/-! ### The modular polynomial over $\mathbb C$ -/

/-- Milne's $F_N(X, Y) = \sum_{k \le m} P_k(X)\,Y^k \in \mathbb C[X][Y]$, $m = (\Gamma_0(1) : \Gamma_0(N))$, with
$F_N(j(z), Y) = \Phi_z(Y)$ (`modPolyCx_map`). -/
noncomputable def modPolyCx (N : ℕ) [NeZero N] : ℂ[X][X] :=
  ∑ k ∈ Finset.range (Fintype.card (Cosets N) + 1), C (coeffPoly N k) * X ^ k

theorem modPolyCx_coeff (k : ℕ) :
    (modPolyCx N).coeff k = if k ≤ Fintype.card (Cosets N) then coeffPoly N k else 0 := by
  unfold modPolyCx
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem modPolyCx_map (z : ℍ) : (modPolyCx N).map (evalRingHom (jFun z)) = rootPoly N z := by
  ext k
  rw [coeff_map, modPolyCx_coeff]
  split_ifs with hk
  · rw [coe_evalRingHom, coeffPoly_eval]
  · rw [map_zero, coeff_eq_zero_of_natDegree_lt]
    rw [rootPoly_natDegree]
    omega

theorem coeffPoly_card : coeffPoly N (Fintype.card (Cosets N)) = 1 := by
  apply Polynomial.funext
  intro w
  obtain ⟨z, rfl⟩ := jFun_surjective w
  rw [coeffPoly_eval, ← rootPoly_natDegree z, (rootPoly_monic z).coeff_natDegree, eval_one]

theorem modPolyCx_natDegree : (modPolyCx N).natDegree = Fintype.card (Cosets N) := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [modPolyCx_coeff, if_neg (by omega)]
  · rw [modPolyCx_coeff, if_pos le_rfl, coeffPoly_card]
    exact one_ne_zero

theorem modPolyCx_monic : (modPolyCx N).Monic := by
  rw [Monic, leadingCoeff, modPolyCx_natDegree, modPolyCx_coeff, if_pos le_rfl, coeffPoly_card]

theorem evalJJN_modPolyCx (z : ℍ) : evalJJN N (modPolyCx N) z = 0 := by
  unfold evalJJN
  rw [modPolyCx_map, rootPoly, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ ((1 : SL(2, ℤ)) : Cosets N))
  rw [eval_sub, eval_X, eval_C, cosetRoot_mk one_le_of_neZero, inv_one, one_smul, sub_self]

omit [NeZero N] in
theorem evalJJN_eq_evalJJNC (G : ℂ[X][X]) (z : ℍ) : evalJJN N G z = evalJJNC N G z := by
  rw [evalJJNHom_apply, mapRingHom_id, Polynomial.map_id]

omit [NeZero N] in
theorem mdiff_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, MDiff (f i)) : MDiff (fun z : ℍ => ∏ i ∈ s, f i z) := by
  induction s using Finset.induction_on with
  | empty => simpa using (mdifferentiable_const : MDiff (fun _ : ℍ => (1 : ℂ)))
  | insert i s hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

omit [NeZero N] in
theorem finset_prod_ne_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, MDiff (f i)) (hne : ∀ i ∈ s, f i ≠ 0) : (fun z : ℍ => ∏ i ∈ s, f i z) ≠ 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro h
    have := congrFun h UpperHalfPlane.I
    simp at this
  | insert i s hi ih =>
    intro h
    have hs : ∀ j ∈ s, MDiff (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hfun : (fun z : ℍ => ∏ j ∈ insert i s, f j z) = f i * fun z => ∏ j ∈ s, f j z := by
      funext z
      simp [Finset.prod_insert hi]
    rw [hfun] at h
    rcases mdiff_mul_eq_zero (hf i (Finset.mem_insert_self _ _)) (mdiff_finset_prod s f hs) h with h' | h'
    · exact hne i (Finset.mem_insert_self _ _) h'
    · exact ih hs (fun j hj => hne j (Finset.mem_insert_of_mem hj)) h'

/-- **$F_N$ generates the ideal of $(j, j_N)$**: if $G(j, j_N) = 0$ on $\mathbb H$ then $F_N \mid G$. The remainder
$R = G \bmod F_N$ satisfies $R(j(z), j_N(\gamma^{-1}z)) = 0$ for every coset, so $R(j(z), Y)$, of degree $< m$, has
$m$ distinct roots wherever the conjugates are distinct; by the identity theorem its coefficients vanish. -/
theorem modPolyCx_dvd (G : ℂ[X][X]) (hG : ∀ z, evalJJN N G z = 0) : modPolyCx N ∣ G := by
  classical
  have hN := (one_le_of_neZero (N := N))
  set R := G %ₘ modPolyCx N with hR
  have hRz : ∀ z, evalJJN N R z = 0 := by
    intro z
    have h2 := congrArg (fun P => evalJJNC N P z) (modByMonic_add_div G (modPolyCx N))
    simp only [map_add, map_mul, Pi.add_apply, Pi.mul_apply] at h2
    simp only [← evalJJN_eq_evalJJNC] at h2
    rw [hG, evalJJN_modPolyCx, zero_mul, add_zero] at h2
    exact h2
  have hroot : ∀ z (c : Cosets N), (R.map (evalRingHom (jFun z))).eval (cosetRoot N c z) = 0 := by
    intro z c
    have := hRz ((Quotient.out c)⁻¹ • z)
    unfold evalJJN at this
    rw [jFun_smul] at this
    exact this
  have hF1 : modPolyCx N ≠ 1 := by
    intro h
    have h1 := modPolyCx_natDegree (N := N)
    have h2 : 0 < Fintype.card (Cosets N) := Fintype.card_pos
    rw [h, natDegree_one] at h1
    omega
  have hdeg : ∀ z, (R.map (evalRingHom (jFun z))).natDegree < Fintype.card (Cosets N) := fun z =>
    natDegree_map_le.trans_lt (by
      rw [← modPolyCx_natDegree]
      exact natDegree_modByMonic_lt G modPolyCx_monic hF1)
  obtain ⟨P, hP⟩ : ∃ P : ℍ → ℂ, P = fun z => ∏ p ∈ (Finset.univ : Finset (Cosets N)).offDiag,
      (cosetRoot N p.1 z - cosetRoot N p.2 z) := ⟨_, rfl⟩
  have hPinj : ∀ z, P z ≠ 0 → Function.Injective (fun c => cosetRoot N c z) := by
    intro z hz c c' hcc
    have hcc' : cosetRoot N c z = cosetRoot N c' z := hcc
    by_contra hne
    apply hz
    rw [hP]
    exact Finset.prod_eq_zero (i := (c, c'))
      (Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩) (sub_eq_zero.2 hcc')
  have hfac : ∀ p ∈ (Finset.univ : Finset (Cosets N)).offDiag,
      MDiff (fun z => cosetRoot N p.1 z - cosetRoot N p.2 z) :=
    fun p _ => (cosetRoot_mdiff hN p.1).sub (cosetRoot_mdiff hN p.2)
  have hPmd : MDiff P := hP ▸ mdiff_finset_prod _ _ hfac
  have hP0 : P ≠ 0 := by
    rw [hP]
    refine finset_prod_ne_zero _ _ hfac fun p hp h0 => ?_
    apply (Finset.mem_offDiag.1 hp).2.2
    apply cosetRoot_injective hN
    funext z
    exact sub_eq_zero.1 (congrFun h0 z)
  have hRk : ∀ k, R.coeff k = 0 := by
    intro k
    have hprod : P * (fun z => (R.coeff k).eval (jFun z)) = 0 := by
      funext z
      simp only [Pi.mul_apply, Pi.zero_apply]
      by_cases hz : P z = 0
      · rw [hz, zero_mul]
      · have h0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (hPinj z hz) (hroot z) (hdeg z)
        have := congrArg (fun Q => Q.coeff k) h0
        simp only [coeff_map, coeff_zero, coe_evalRingHom] at this
        rw [this, mul_zero]
    rcases mdiff_mul_eq_zero hPmd (fun z => mdiffAt_eval_jFun (R.coeff k) z) hprod with h | h
    · exact absurd h hP0
    · apply Polynomial.funext
      intro w
      obtain ⟨z, rfl⟩ := jFun_surjective w
      simpa using congrFun h z
  rw [← modByMonic_eq_zero_iff_dvd modPolyCx_monic]
  refine Polynomial.ext fun k => ?_
  rw [hRk k, coeff_zero]

/-- **The modular polynomial exists** (Milne V §2, pdf p. 193): for $N \ge 1$ there is $F_N \in \mathbb C[X][Y]$,
monic of degree $(\Gamma_0(1) : \Gamma_0(N))$ in $Y$, with $F_N(j, j_N) = 0$, dividing every $G$ with
$G(j, j_N) = 0$. This proves the named `ModularPolynomial N`. -/
@[kb "milne2006ec" "Ch. V, §2, the modular polynomial F_N (running text), pdf p. 193"]
theorem modularPolynomial {M : ℕ} (hM : 1 ≤ M) : ModularPolynomial M := by
  have : NeZero M := ⟨by omega⟩
  exact ⟨modPolyCx M, modPolyCx_monic, modPolyCx_natDegree.trans card_cosets, evalJJN_modPolyCx,
    modPolyCx_dvd⟩

end NumberFieldKB.ModularCurves
