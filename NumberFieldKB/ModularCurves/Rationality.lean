import NumberFieldKB.ModularCurves.ModularPolynomial
import NumberFieldKB.MilneEC.Ch5LevelOne
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# The modular polynomial has rational coefficients (Milne, *Elliptic Curves*, Ch. V, Proposition 2.4)

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Proposition 2.4 (pdf p. 193). Milne proves that
$F_N \in \mathbb Q[X, Y]$ by letting $\mathrm{Gal}(\mathbb Q(\zeta_N)/\mathbb Q)$ act on the $q$-expansions of the
conjugates $j(\alpha z)$. We use a linear-algebra route that needs only the rational $q$-expansions of
$E_4(z)$, $E_6(z)$, $E_4(Nz)$ and $E_6(Nz)$:

* clearing denominators with $j = E_4^3/\Delta$ and $\Delta = (E_4^3 - E_6^2)/1728$, the relation
  $G(j, j_N) = 0$ for $G = \sum g_{ab}X^aY^b$ becomes $\sum g_{ab}\,u_{ab} = 0$, where
  $u_{ab}(z) = E_4^{3a}\Delta^{D-a}(z)\,E_4^{3b}\Delta^{m-b}(Nz)$ has a $q$-expansion with rational
  coefficients (`isRatQExp_u`);
* take a $\mathbb Q$-linear map $\pi : \mathbb C \to \mathbb Q$ with $\pi|_{\mathbb Q} = \mathrm{id}$ and apply it
  to the coefficients of $F_N$. Since the $q$-expansions of the $u_{ab}$ are rational, the projected polynomial
  $G$ still satisfies $G(j, j_N) = 0$ (`evalJJN_projPoly`); it is monic of degree $m$ in $Y$ because $F_N$ is, so
  $F_N \mid G$ forces $G = F_N$.

Main result: `prop2_4`, the named `Prop2_4 N` of `Ch5JFunction`, for every $N \ge 1$.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex ModularForm
open scoped Manifold MatrixGroups Real

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

local notation "Δ" => ModularForm.discriminant

/-! ### Functions with a $q$-expansion -/

/-- A function on $\mathbb H$ with a $q$-expansion of period $1$: holomorphic, $1$-periodic, bounded at
$i\infty$. -/
structure IsQExp (f : ℍ → ℂ) : Prop where
  mdiff : MDiff f
  periodic : Function.Periodic (f ∘ ofComplex) 1
  bounded : IsBoundedAtImInfty f

/-- The rational numbers inside $\mathbb C$, as a subring. -/
noncomputable abbrev ratSubring : Subring ℂ := (algebraMap ℚ ℂ).range

/-- A function with a $q$-expansion whose coefficients are rational. -/
structure IsRatQExp (f : ℍ → ℂ) : Prop extends IsQExp f where
  rat : ∀ n, (qExpansion 1 f).coeff n ∈ ratSubring

namespace IsQExp

theorem analytic {f : ℍ → ℂ} (hf : IsQExp f) : AnalyticAt ℂ (cuspFunction 1 f) 0 :=
  analyticAt_cuspFunction_zero one_pos hf.periodic hf.mdiff hf.bounded

theorem add {f g : ℍ → ℂ} (hf : IsQExp f) (hg : IsQExp g) : IsQExp (f + g) where
  mdiff := hf.mdiff.add hg.mdiff
  periodic := hf.periodic.add hg.periodic
  bounded := hf.bounded.add hg.bounded

theorem mul {f g : ℍ → ℂ} (hf : IsQExp f) (hg : IsQExp g) : IsQExp (f * g) where
  mdiff := hf.mdiff.mul hg.mdiff
  periodic := hf.periodic.mul hg.periodic
  bounded := hf.bounded.mul hg.bounded

theorem smul {f : ℍ → ℂ} (hf : IsQExp f) (c : ℂ) : IsQExp (c • f) where
  mdiff := hf.mdiff.const_smul c
  periodic := fun w => congrArg (fun x => c • x) (hf.periodic w)
  bounded := by
    have : c • f = (fun _ => c) * f := by funext z; simp
    rw [this]
    exact (Filter.const_boundedAtFilter _ c).mul hf.bounded

theorem one : IsQExp (1 : ℍ → ℂ) where
  mdiff := mdifferentiable_const
  periodic := fun _ => rfl
  bounded := Filter.const_boundedAtFilter _ 1

theorem pow {f : ℍ → ℂ} (hf : IsQExp f) (n : ℕ) : IsQExp (f ^ n) := by
  induction n with
  | zero => simpa using one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem of_modularForm {k : ℤ} (f : ModularForm 𝒮ℒ k) : IsQExp f where
  mdiff := f.holo'
  periodic := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  bounded := ModularFormClass.bdd_at_infty f

end IsQExp

namespace IsRatQExp

theorem add {f g : ℍ → ℂ} (hf : IsRatQExp f) (hg : IsRatQExp g) : IsRatQExp (f + g) where
  toIsQExp := hf.toIsQExp.add hg.toIsQExp
  rat n := by
    rw [qExpansion_add hf.analytic hg.analytic, map_add]
    exact add_mem (hf.rat n) (hg.rat n)

theorem mul {f g : ℍ → ℂ} (hf : IsRatQExp f) (hg : IsRatQExp g) : IsRatQExp (f * g) where
  toIsQExp := hf.toIsQExp.mul hg.toIsQExp
  rat n := by
    rw [qExpansion_mul hf.analytic hg.analytic, PowerSeries.coeff_mul]
    exact sum_mem fun p _ => mul_mem (hf.rat p.1) (hg.rat p.2)

theorem smul {f : ℍ → ℂ} (hf : IsRatQExp f) (c : ℚ) : IsRatQExp ((c : ℂ) • f) where
  toIsQExp := hf.toIsQExp.smul c
  rat n := by
    rw [qExpansion_smul hf.analytic, map_smul, smul_eq_mul]
    exact mul_mem ⟨c, rfl⟩ (hf.rat n)

theorem one : IsRatQExp (1 : ℍ → ℂ) where
  toIsQExp := IsQExp.one
  rat n := by
    rw [qExpansion_one, PowerSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem pow {f : ℍ → ℂ} (hf : IsRatQExp f) (n : ℕ) : IsRatQExp (f ^ n) := by
  induction n with
  | zero => simpa using one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem sub {f g : ℍ → ℂ} (hf : IsRatQExp f) (hg : IsRatQExp g) : IsRatQExp (f - g) := by
  have : f - g = f + ((-1 : ℚ) : ℂ) • g := by funext z; simp [sub_eq_add_neg]
  rw [this]
  exact hf.add (hg.smul _)

theorem E4 : IsRatQExp (E₄ : ℍ → ℂ) where
  toIsQExp := IsQExp.of_modularForm E₄
  rat n := by
    rw [E4_coeff]
    split_ifs
    · exact one_mem _
    · exact ⟨240 * (ArithmeticFunction.sigma 3 n : ℚ), by simp⟩

theorem E6 : IsRatQExp (E₆ : ℍ → ℂ) where
  toIsQExp := IsQExp.of_modularForm E₆
  rat n := by
    rw [E6_coeff]
    split_ifs
    · exact one_mem _
    · exact ⟨-504 * (ArithmeticFunction.sigma 5 n : ℚ), by simp⟩

theorem disc : IsRatQExp (fun z => Δ z) := by
  have : (fun z => Δ z) = ((1 / 1728 : ℚ) : ℂ) • ((E₄ : ℍ → ℂ) ^ 3 - (E₆ : ℍ → ℂ) ^ 2) := by
    funext z
    simp [discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [this]
  exact ((E4.pow 3).sub (E6.pow 2)).smul _

end IsRatQExp

/-! ### The substitution $z \mapsto Nz$ -/

/-- $f(Nz)$. -/
noncomputable def scaleN (N : ℕ) (f : ℍ → ℂ) (z : ℍ) : ℂ := f (ofComplex ((N : ℂ) * z))

variable {N : ℕ}

lemma im_ofComplex_mul (hN : 1 ≤ N) (z : ℍ) : (ofComplex ((N : ℂ) * z)).im = N * z.im := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 0 < ((N : ℂ) * z).im := by
    simp [Complex.mul_im]; exact mul_pos hNpos z.im_pos
  rw [UpperHalfPlane.im, ofComplex_apply_of_im_pos h1]
  simp [Complex.mul_im]

theorem IsQExp.scaleN (hN : 1 ≤ N) {f : ℍ → ℂ} (hf : IsQExp f) : IsQExp (scaleN N f) where
  mdiff := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hf' := UpperHalfPlane.mdifferentiable_iff.1 hf.mdiff
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
      have hper : Function.Periodic (f ∘ ofComplex) (N : ℝ) := by
        simpa using hf.periodic.nat_mul N
      have := hper ((N : ℂ) * w)
      simp only [Function.comp_apply] at this
      push_cast at this ⊢
      rw [mul_add, mul_one]
      exact this
  bounded := by
    obtain ⟨M, A, h⟩ := isBoundedAtImInfty_iff.1 hf.bounded
    refine isBoundedAtImInfty_iff.2 ⟨M, |A|, fun z hz => h _ ?_⟩
    rw [im_ofComplex_mul hN]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : z.im ≤ N * z.im := le_mul_of_one_le_left z.im_pos.le hN1
    linarith [le_abs_self A]

lemma qParam_mul (hN : 1 ≤ N) (z : ℍ) :
    Function.Periodic.qParam 1 ((ofComplex ((N : ℂ) * z) : ℍ) : ℂ) = Function.Periodic.qParam 1 (z : ℂ) ^ N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 0 < ((N : ℂ) * z).im := by
    simp [Complex.mul_im]; exact mul_pos hNpos z.im_pos
  rw [ofComplex_apply_of_im_pos h1]
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Uniqueness of $q$-expansions, for a plain function on $\mathbb H$ (Mathlib's `qExpansion_coeff_unique` is
stated for bundled function classes). -/
lemma qExpansion_coeff_unique' {g : ℍ → ℂ} {c : ℕ → ℂ} (hg : AnalyticAt ℂ (cuspFunction 1 g) 0)
    (hsum : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion 1 g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos hg hsum).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction 1 g)
      (.ofScalars ℂ fun m ↦ (qExpansion 1 g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  have h3 := h1.eq_formalMultilinearSeries h2
  have h4 := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff m) h3
  simpa using h4

/-- The coefficients of $f(q^N)$ from those of $f(q)$. -/
def dilateCoeff (N : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ := if N ∣ n then c (n / N) else 0

theorem IsRatQExp.scaleN (hN : 1 ≤ N) {f : ℍ → ℂ} (hf : IsRatQExp f) : IsRatQExp (scaleN N f) where
  toIsQExp := hf.toIsQExp.scaleN hN
  rat n := by
    have hsum : ∀ τ : ℍ, HasSum (fun m => dilateCoeff N (fun k => (qExpansion 1 f).coeff k) m •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (NumberFieldKB.ModularCurves.scaleN N f τ) := by
      intro τ
      have h0 := hasSum_qExpansion one_pos hf.periodic hf.mdiff hf.bounded (ofComplex ((N : ℂ) * τ))
      rw [qParam_mul hN] at h0
      show HasSum _ (f (ofComplex ((N : ℂ) * τ)))
      have hinj : Function.Injective (fun m : ℕ => N * m) := fun a b hab =>
        Nat.eq_of_mul_eq_mul_left (by omega) hab
      rw [← hinj.hasSum_iff]
      · convert h0 using 1
        funext m
        simp only [Function.comp_apply, dilateCoeff, dvd_mul_right, if_true,
          Nat.mul_div_cancel_left _ (by omega : 0 < N), ← pow_mul]
      · intro x hx
        simp only [dilateCoeff]
        rw [if_neg, zero_smul]
        rintro ⟨k, rfl⟩
        exact hx ⟨k, rfl⟩
    rw [← qExpansion_coeff_unique' (hf.toIsQExp.scaleN hN).analytic hsum n]
    simp only [dilateCoeff]
    split_ifs
    · exact hf.rat _
    · exact zero_mem _

/-! ### Clearing denominators -/

/-- $u_{ab}(z) = E_4^{3a}\Delta^{D-a}(z)\,E_4^{3b}\Delta^{m-b}(Nz)$. -/
noncomputable def uFun (N D m a b : ℕ) : ℍ → ℂ :=
  ((E₄ : ℍ → ℂ) ^ (3 * a) * (fun z => Δ z) ^ (D - a)) *
    scaleN N ((E₄ : ℍ → ℂ) ^ (3 * b) * (fun z => Δ z) ^ (m - b))

theorem isRatQExp_u (hN : 1 ≤ N) (D m a b : ℕ) : IsRatQExp (uFun N D m a b) :=
  ((IsRatQExp.E4.pow _).mul (IsRatQExp.disc.pow _)).mul
    (((IsRatQExp.E4.pow _).mul (IsRatQExp.disc.pow _)).scaleN hN)

/-- With $j = E_4^3/\Delta$: $\Delta(z)^D\Delta(Nz)^m\,G(j(z), j_N(z)) = \sum_{a, b} g_{ab}\,u_{ab}(z)$ when
$\deg_X G \le D$, $\deg_Y G \le m$. -/
theorem clear_denoms (G : ℂ[X][X]) {D m : ℕ} (hm : G.natDegree ≤ m)
    (hD : ∀ b, (G.coeff b).natDegree ≤ D) (z : ℍ) :
    Δ z ^ D * Δ (ofComplex ((N : ℂ) * z)) ^ m * evalJJN N G z =
      ∑ p ∈ Finset.range (m + 1) ×ˢ Finset.range (D + 1),
        (G.coeff p.1).coeff p.2 * uFun N D m p.2 p.1 z := by
  rw [Finset.sum_product]
  set w := ofComplex ((N : ℂ) * z) with hw
  have hjN : jN N z = jFun w := rfl
  unfold evalJJN
  rw [eval_eq_sum_range' (n := m + 1) (lt_of_le_of_lt natDegree_map_le (by omega)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' : b ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
  rw [coeff_map, coe_evalRingHom, eval_eq_sum_range' (n := D + 1) (by have := hD b; omega),
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  simp only [uFun, scaleN, Pi.mul_apply, Pi.pow_apply]
  rw [hjN, ← hw]
  have e1 : jFun z ^ a * Δ z ^ D = E₄ z ^ (3 * a) * Δ z ^ (D - a) := by
    have : Δ z ^ D = Δ z ^ a * Δ z ^ (D - a) := by rw [← pow_add, Nat.add_sub_cancel' ha']
    rw [this, ← mul_assoc, ← mul_pow, jFun_mul_disc, ← pow_mul]
  have e2 : jFun w ^ b * Δ w ^ m = E₄ w ^ (3 * b) * Δ w ^ (m - b) := by
    have : Δ w ^ m = Δ w ^ b * Δ w ^ (m - b) := by rw [← pow_add, Nat.add_sub_cancel' hb']
    rw [this, ← mul_assoc, ← mul_pow, jFun_mul_disc, ← pow_mul]
  calc Δ z ^ D * Δ w ^ m * ((G.coeff b).coeff a * jFun z ^ a * jFun w ^ b)
      = (G.coeff b).coeff a * (jFun z ^ a * Δ z ^ D) * (jFun w ^ b * Δ w ^ m) := by ring
    _ = _ := by rw [e1, e2]; ring

/-- $q$-expansions of finite linear combinations. -/
theorem qExpansion_sum_smul {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (f : ι → ℍ → ℂ)
    (hf : ∀ i, IsQExp (f i)) :
    IsQExp (∑ i ∈ s, c i • f i) ∧ qExpansion 1 (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • qExpansion 1 (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨?_, qExpansion_zero 1⟩
    simpa using IsQExp.one.smul 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    refine ⟨((hf i).smul _).add ih.1, ?_⟩
    rw [qExpansion_add ((hf i).smul _).analytic ih.1.analytic, qExpansion_smul (hf i).analytic, ih.2]

/-! ### Proposition 2.4 -/

/-- Apply a $\mathbb Q$-linear $\pi : \mathbb C \to \mathbb Q$ to the coefficients of $P \in \mathbb C[X]$, of degree
at most $D$. -/
noncomputable def projX (pr : ℂ →ₗ[ℚ] ℚ) (D : ℕ) (P : ℂ[X]) : ℚ[X] :=
  ∑ a ∈ Finset.range (D + 1), C (pr (P.coeff a)) * X ^ a

theorem projX_coeff (pr : ℂ →ₗ[ℚ] ℚ) {D : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ D) (a : ℕ) :
    (projX pr D P).coeff a = pr (P.coeff a) := by
  unfold projX
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with ha
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by simp at ha; omega), map_zero]

/-- Apply $\pi$ to the coefficients of $F \in \mathbb C[X][Y]$ with $\deg_X F \le D$, $\deg_Y F \le m$. -/
noncomputable def projPoly (pr : ℂ →ₗ[ℚ] ℚ) (D m : ℕ) (F : ℂ[X][X]) : ℚ[X][X] :=
  ∑ b ∈ Finset.range (m + 1), C (projX pr D (F.coeff b)) * X ^ b

theorem projPoly_coeff (pr : ℂ →ₗ[ℚ] ℚ) {D m : ℕ} {F : ℂ[X][X]} (hm : F.natDegree ≤ m)
    (hD : ∀ b, (F.coeff b).natDegree ≤ D) (b a : ℕ) :
    ((projPoly pr D m F).coeff b).coeff a = pr ((F.coeff b).coeff a) := by
  unfold projPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hb
  · exact projX_coeff pr (hD b) a
  · rw [coeff_eq_zero_of_natDegree_lt (p := F) (by simp at hb; omega), coeff_zero, coeff_zero,
      map_zero]

/-- **Proposition 2.4** (Milne V §2, pdf p. 193): the modular polynomial $F_N$ has rational coefficients. For every
$N \ge 1$ there is a monic $F \in \mathbb Q[X][Y]$ of degree $(\Gamma_0(1) : \Gamma_0(N))$ in $Y$ whose image in
$\mathbb C[X][Y]$ vanishes at $(j, j_N)$ and divides every $G$ with $G(j, j_N) = 0$. This proves the named
`Prop2_4 N`. -/
@[kb "milne2006ec" "Ch. V, Proposition 2.4, pdf p. 193"]
theorem prop2_4 {N : ℕ} (hN : 1 ≤ N) : Prop2_4 N := by
  obtain ⟨F, hFm, hFdeg, hF0, hFdvd⟩ := (modularPolynomial hN).exists_poly
  set m := F.natDegree with hmdef
  set D := (Finset.range (m + 1)).sup fun b => (F.coeff b).natDegree with hDdef
  have hD : ∀ b, (F.coeff b).natDegree ≤ D := by
    intro b
    by_cases hb : b ≤ m
    · exact Finset.le_sup (f := fun b => (F.coeff b).natDegree) (Finset.mem_range.2 (by omega))
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  obtain ⟨pr, hpr⟩ := (Algebra.linearMap ℚ ℂ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap ℚ ℂ).injective)
  have hprr : ∀ r : ℚ, pr (algebraMap ℚ ℂ r) = r := fun r => LinearMap.congr_fun hpr r
  set Fq := projPoly pr D m F with hFq
  set G := Fq.map (mapRingHom (algebraMap ℚ ℂ)) with hG
  have hGc : ∀ b a, (G.coeff b).coeff a = algebraMap ℚ ℂ (pr ((F.coeff b).coeff a)) := by
    intro b a
    rw [hG, coeff_map, coe_mapRingHom, coeff_map, hFq, projPoly_coeff pr le_rfl hD]
  have hGm : G.natDegree ≤ m := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro b hb
    refine Polynomial.ext fun a => ?_
    rw [hGc, coeff_eq_zero_of_natDegree_lt (p := F) hb]
    simp
  have hGD : ∀ b, (G.coeff b).natDegree ≤ D := by
    intro b
    rw [natDegree_le_iff_coeff_eq_zero]
    intro a ha
    rw [hGc, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hD b) ha), map_zero, map_zero]
  -- the functions u_{ab} and the two linear combinations
  set s := Finset.range (m + 1) ×ˢ Finset.range (D + 1) with hs
  have hu : ∀ p : ℕ × ℕ, IsRatQExp (uFun N D m p.2 p.1) := fun p => isRatQExp_u hN D m p.2 p.1
  choose r hr using fun (p : ℕ × ℕ) (n : ℕ) => (hu p).rat n
  set HF := ∑ p ∈ s, (F.coeff p.1).coeff p.2 • uFun N D m p.2 p.1 with hHF
  set HG := ∑ p ∈ s, (G.coeff p.1).coeff p.2 • uFun N D m p.2 p.1 with hHG
  have hHF0 : HF = 0 := by
    funext z
    have := clear_denoms (N := N) F le_rfl hD z
    rw [hF0 z, mul_zero] at this
    simp only [hHF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact this.symm
  obtain ⟨hHFq, hHFe⟩ := qExpansion_sum_smul s (fun p => (F.coeff p.1).coeff p.2)
    (fun p => uFun N D m p.2 p.1) fun p => (hu p).toIsQExp
  obtain ⟨hHGq, hHGe⟩ := qExpansion_sum_smul s (fun p => (G.coeff p.1).coeff p.2)
    (fun p => uFun N D m p.2 p.1) fun p => (hu p).toIsQExp
  have hHG0 : HG = 0 := by
    rw [← qExpansion_eq_zero_iff one_pos hHGq.periodic hHGq.mdiff hHGq.bounded]
    rw [hHGe]
    ext n
    have hFn := congrArg (fun P => PowerSeries.coeff n P) hHFe
    simp only [← hHF, hHF0, qExpansion_zero, map_zero, map_sum, map_smul, smul_eq_mul] at hFn
    simp only [map_sum, map_smul, smul_eq_mul, map_zero]
    simp only [hGc, ← hr]
    simp only [← hr] at hFn
    have h1 : ∑ p ∈ s, algebraMap ℚ ℂ (pr ((F.coeff p.1).coeff p.2)) * algebraMap ℚ ℂ (r p n) =
        algebraMap ℚ ℂ (pr (∑ p ∈ s, (F.coeff p.1).coeff p.2 * algebraMap ℚ ℂ (r p n))) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← map_mul, mul_comm ((F.coeff p.1).coeff p.2), ← Algebra.smul_def, map_smul, smul_eq_mul,
        mul_comm]
    rw [h1, ← hFn, map_zero, map_zero]
  have hG0 : ∀ z, evalJJN N G z = 0 := by
    intro z
    have h := clear_denoms (N := N) G hGm hGD z
    have h2 : (∑ p ∈ s, (G.coeff p.1).coeff p.2 * uFun N D m p.2 p.1 z) = HG z := by
      simp [hHG, Finset.sum_apply]
    rw [h2, hHG0, Pi.zero_apply] at h
    rcases mul_eq_zero.1 h with h' | h'
    · exfalso
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact ModularForm.discriminant_ne_zero z (pow_eq_zero_iff'.1 h'').1
      · exact ModularForm.discriminant_ne_zero _ (pow_eq_zero_iff'.1 h'').1
    · exact h'
  have hGlead : G.coeff m = 1 := by
    refine Polynomial.ext fun a => ?_
    rw [hGc, show F.coeff m = 1 from hFm.coeff_natDegree, coeff_one]
    split_ifs
    · simpa using congrArg (algebraMap ℚ ℂ) (hprr 1)
    · rw [map_zero, map_zero]
  have hGdeg : G.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hGm (by rw [hGlead]; exact one_ne_zero)
  have hGmonic : G.Monic := by rw [Monic, leadingCoeff, hGdeg, hGlead]
  have hGF : G = F := eq_of_monic_of_dvd_of_natDegree_le hFm hGmonic (hFdvd G hG0) hGdeg.le
  have hinj : Function.Injective (mapRingHom (algebraMap ℚ ℂ) : ℚ[X] →+* ℂ[X]) := by
    rw [coe_mapRingHom]
    exact map_injective _ (algebraMap ℚ ℂ).injective
  refine ⟨Fq, ?_, ?_, ?_, ?_⟩
  · have := leadingCoeff_map_of_injective hinj Fq
    rw [← hG, hGmonic.leadingCoeff] at this
    exact hinj (by rw [← this, map_one])
  · rw [← natDegree_map_eq_of_injective hinj Fq, ← hG, hGdeg]
    exact hFdeg
  · rw [← hG, hGF]; exact hF0
  · rw [← hG, hGF]; exact hFdvd

end NumberFieldKB.ModularCurves
