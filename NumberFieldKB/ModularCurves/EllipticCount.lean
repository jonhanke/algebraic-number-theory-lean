import NumberFieldKB.ModularCurves.EllipticCommute
import NumberFieldKB.ModularCurves.CuspCountX0
import NumberFieldKB.ModularCurves.JInjective

/-!
# The geometric counts over $j = 0$ and $j = 1728$, and the genus of $X_0(N)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (the genus formula, pdf p. 196); G. Shimura,
*Introduction to the Arithmetic Theory of Automorphic Functions*, Proposition 1.40.

With $\nu_3$ the number of cosets $c \in \mathrm{SL}_2(\mathbb Z)/\Gamma_0(N)$ fixed by $ST$ and $\nu_2$ the number fixed
by $S$ (`nu3`, `nu2`):
* $3\, r(0) = \mu + 2\nu_3$ (`three_mul_geomCount_placeJ0`, at $\tau_0 = \rho$, $e = 3$);
* $2\, r(1728) = \mu + \nu_2$ (`two_mul_geomCount_placeJ1728`, at $\tau_0 = i$, $e = 2$);
* $12\, g(X_0(N)) = 12 + \mu - 3\nu_2 - 4\nu_3 - 6\nu_\infty$ (`genus_formula_X0`).

These use Milne's Proposition 2.2 ($j$ is injective on $\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$, `jInjective`,
proved in `JInjective.lean` from Chapter III) through `smul_eq_of_jFun_cosetPoint_eq`.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped MatrixGroups

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-- See `RiemannHurwitz.lean`: the $\mathbb Q$-algebra structure of $\mathbb Q(t)$ through $\mathbb Q[t]$. -/
local instance (priority := high) ratFuncAlgebraRatCount : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-! ### The elliptic elements and their derivatives -/

theorem S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [UpperHalfPlane.modular_S_smul]; ext; simp

theorem ST_smul_rho : (ModularGroup.S * ModularGroup.T) • ρ = ρ :=
  ModularGroup.stabilizer_ρ.mpr (by simp)

theorem deriv_moeb_S_I : deriv (moeb ModularGroup.S) (UpperHalfPlane.I : ℂ) = -1 := by
  rw [deriv_moeb]
  simp [denom, GL_apply, ModularGroup.coe_S]

theorem deriv_moeb_ST_rho : deriv (moeb (ModularGroup.S * ModularGroup.T)) (ρ : ℂ) = (ρ : ℂ)⁻¹ := by
  rw [deriv_moeb]
  have hd : denom ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) ρ = ρ + 1 := by
    simp [denom, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hd]
  have hsq := UpperHalfPlane.ρ_sq
  have : ((ρ : ℂ) + 1) ^ 2 = ρ := by linear_combination hsq
  rw [this, one_div]

theorem isPrimitiveRoot_neg_one : IsPrimitiveRoot (-1 : ℂ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)

theorem isPrimitiveRoot_rho : IsPrimitiveRoot (ρ : ℂ) 3 := by
  have hsq := UpperHalfPlane.ρ_sq
  have hpos := ρ.im_pos
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by linear_combination ((ρ : ℂ) - 1) * hsq) ?_
  intro l hl hl3
  interval_cases l
  · intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  · intro h
    rw [hsq] at h
    have := congrArg Complex.im h
    simp at this
    linarith

/-! ### The counts -/

variable (N : ℕ) [NeZero N]

open scoped Classical in
/-- $\nu_2$: the number of cosets fixed by $S$ (the elliptic points of order $2$ of $\Gamma_0(N)$). -/
def nu2 : ℕ := (Finset.univ.filter fun c : Cosets N => ModularGroup.S • c = c).card

open scoped Classical in
/-- $\nu_3$: the number of cosets fixed by $ST$ (the elliptic points of order $3$ of $\Gamma_0(N)$). -/
def nu3 : ℕ := (Finset.univ.filter fun c : Cosets N => (ModularGroup.S * ModularGroup.T) • c = c).card

omit [NeZero N] in
theorem inv_smul_eq_iff' (g : SL(2, ℤ)) (c : Cosets N) : g⁻¹ • c = c ↔ g • c = c := by
  rw [inv_smul_eq_iff, eq_comm]

open scoped Classical in
/-- $\sum_c (\text{$e$ if $g c = c$, else $1$}) = \mu + (e - 1)\#\{c : g c = c\}$. -/
theorem sum_ite_fixed (g : SL(2, ℤ)) (e : ℤ) :
    ∑ c : Cosets N, (if g • c = c then e else 1) =
      (CongruenceSubgroup.Gamma0 N).index + (e - 1) * (Finset.univ.filter fun c : Cosets N => g • c = c).card := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one,
    Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ, card_cosets,
    Nat.cast_sub (Finset.card_le_univ _ |>.trans_eq (by rw [card_cosets]))]
  ring

/-- **$3\, r(0) = \mu + 2\nu_3$.** -/
theorem three_mul_geomCount_placeJ0 :
    3 * geomCount N placeJ0 = (CongruenceSubgroup.Gamma0 N).index + 2 * nu3 N := by
  classical
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  have hroot : aeval (jFun ρ) (X : ℚ[X]) = 0 := by simp [jFun_rho]
  have hm : analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun ρ) (ρ : ℂ) = ((3 : ℕ) : ℕ∞) :=
    analyticOrderAt_jFun_of_eq_zero ρ jFun_rho
  set hvF := finVal_algebraMap ρ irreducible_X hroot hm
  have h := mul_sum_relativeDegree_eq (isFunctionField_X0 N) hvF (finEmb ρ N) (finEmb_injective ρ N)
    (card_cosets_eq_finrank N) (by norm_num : 0 < 3)
  have hsc : ∀ c, scale (isFunctionField_X0 N) hvF (finEmb ρ N c) (by norm_num : 0 < 3) =
      if (ModularGroup.S * ModularGroup.T) • c = c then 3 else 1 := by
    intro c
    split_ifs with hc
    · exact_mod_cast scale_finEmb_of_fixed N ρ (ModularGroup.S * ModularGroup.T) ST_smul_rho (by norm_num)
        isPrimitiveRoot_rho.inv deriv_moeb_ST_rho irreducible_X hroot hm c ((inv_smul_eq_iff' N _ c).2 hc)
    · have hw0 : jFun (cosetPoint N ρ c) ≠ 0 := by
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
  rw [Finset.sum_congr rfl fun c _ => hsc c, sum_ite_fixed] at h
  have h' : (3 : ℤ) * geomCount N placeJ0 = (CongruenceSubgroup.Gamma0 N).index + 2 * nu3 N := by
    rw [geomCount, Nat.cast_sum]
    convert h using 2
    · rfl
    · unfold nu3
      norm_num
  exact_mod_cast h'

/-- **$2\, r(1728) = \mu + \nu_2$.** -/
theorem two_mul_geomCount_placeJ1728 :
    2 * geomCount N placeJ1728 = (CongruenceSubgroup.Gamma0 N).index + nu2 N := by
  classical
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  have hroot : aeval (jFun UpperHalfPlane.I) (X - C 1728 : ℚ[X]) = 0 := by simp [jFun_I]
  have hm : analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun UpperHalfPlane.I) (UpperHalfPlane.I : ℂ) =
      ((2 : ℕ) : ℕ∞) :=
    analyticOrderAt_jFun_of_eq_1728 _ jFun_I
  set hvF := finVal_algebraMap UpperHalfPlane.I irreducible_X_sub_1728 hroot hm
  have h := mul_sum_relativeDegree_eq (isFunctionField_X0 N) hvF (finEmb UpperHalfPlane.I N)
    (finEmb_injective UpperHalfPlane.I N) (card_cosets_eq_finrank N) (by norm_num : 0 < 2)
  have hsc : ∀ c, scale (isFunctionField_X0 N) hvF (finEmb UpperHalfPlane.I N c) (by norm_num : 0 < 2) =
      if ModularGroup.S • c = c then 2 else 1 := by
    intro c
    split_ifs with hc
    · exact_mod_cast scale_finEmb_of_fixed N UpperHalfPlane.I ModularGroup.S S_smul_I (by norm_num)
        isPrimitiveRoot_neg_one deriv_moeb_S_I irreducible_X_sub_1728 hroot hm c ((inv_smul_eq_iff' N _ c).2 hc)
    · have hw1 : jFun (cosetPoint N UpperHalfPlane.I c) ≠ 1728 := by
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
  rw [Finset.sum_congr rfl fun c _ => hsc c, sum_ite_fixed] at h
  have h' : (2 : ℤ) * geomCount N placeJ1728 = (CongruenceSubgroup.Gamma0 N).index + nu2 N := by
    rw [geomCount, Nat.cast_sum]
    convert h using 2
    · rfl
    · unfold nu2
      norm_num
  exact_mod_cast h'

/-- **The genus of $X_0(N)$** (Milne, Ch. V, §2, pdf p. 196; Shimura, Proposition 1.40): $12 g = 12 + \mu - 3\nu_2 - 4\nu_3 - 6\nu_\infty$, i.e.
$g = 1 + \mu/12 - \nu_2/4 - \nu_3/3 - \nu_\infty/2$, with $\mu = (\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N))$, $\nu_2$, $\nu_3$
the numbers of cosets fixed by $S$, $ST$, and $\nu_\infty = \sum_{d \mid N} \varphi(\gcd(d, N/d))$. -/
@[kb "milne2006ec" "Ch. V, §2, the genus formula for X_0(N), pdf p. 196"]
theorem genus_formula_X0 :
    12 * MilneEC.genus ℚ (X0 N) = 12 + (CongruenceSubgroup.Gamma0 N).index - 3 * nu2 N - 4 * nu3 N -
      6 * ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d)) := by
  classical
  refine genus_formula_of_fibres N (nu2 N) (nu3 N) _ (fun P' hP' => ?_) (geomCount_infty_eq N)
    (three_mul_geomCount_placeJ0 N) (two_mul_geomCount_placeJ1728 N)
  convert restrict_mem_of_ramified N P' hP'

end NumberFieldKB.ModularCurves
