import NumberFieldKB.ModularCurves.Theorem23
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# Modular functions with rational $q$-expansions lie in $\mathbb Q(j, j_M)$

A complement to Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Theorem 2.3 and Proposition 2.4 (pdf pp. 192–193),
used for the Hecke correspondences: if $f = A/B$ is a modular function for $\Gamma_0(M)$ with $A$, $B$ holomorphic on
$\mathbb H$ with rational $q$-expansions, then $f = P(j, j_M)/Q(j, j_M)$ with $P, Q \in \mathbb Q[X][Y]$
(`exists_rat_frac`). In particular $j_d \in \mathbb Q(j, j_M)$ for $d \mid M$ (`exists_rat_jN_of_dvd`).

Proof: Theorem 2.3 gives $P, Q$ over $\mathbb C$; reduce them modulo $F_M$ (so $\deg_Y < m$), normalize a coefficient
of $Q$ to $1$, and apply a $\mathbb Q$-linear $\pi : \mathbb C \to \mathbb Q$ to the coefficients, as in the proof of
Proposition 2.4 (`proj_identity`). The projected $Q$ is nonzero of $Y$-degree $< m$, so $F_M \nmid Q$ and
$Q(j, j_M) \ne 0$.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex Topology ModularForm
open scoped Manifold MatrixGroups Real

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

local notation "Δ" => ModularForm.discriminant

/-- **The projection argument.** A linear relation $\sum_i c_i u_i = 0$ between functions with rational
$q$-expansions stays true after applying a $\mathbb Q$-linear $\pi : \mathbb C \to \mathbb Q$ to the coefficients. -/
theorem proj_identity {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (u : ι → ℍ → ℂ)
    (hu : ∀ i, IsRatQExp (u i)) (h0 : ∑ i ∈ s, c i • u i = 0) (pr : ℂ →ₗ[ℚ] ℚ) :
    ∑ i ∈ s, algebraMap ℚ ℂ (pr (c i)) • u i = 0 := by
  choose r hr using fun (i : ι) (n : ℕ) => (hu i).rat n
  obtain ⟨-, hc⟩ := qExpansion_sum_smul s c u fun i => (hu i).toIsQExp
  obtain ⟨hq, hpe⟩ := qExpansion_sum_smul s (fun i => algebraMap ℚ ℂ (pr (c i))) u fun i => (hu i).toIsQExp
  rw [← qExpansion_eq_zero_iff one_pos hq.periodic hq.mdiff hq.bounded, hpe]
  ext n
  have hn := congrArg (fun P => PowerSeries.coeff n P) hc
  simp only [h0, qExpansion_zero, map_zero, map_sum, map_smul, smul_eq_mul] at hn
  simp only [map_sum, map_smul, smul_eq_mul, map_zero, ← hr]
  simp only [← hr] at hn
  have h1 : ∑ i ∈ s, algebraMap ℚ ℂ (pr (c i)) * algebraMap ℚ ℂ (r i n) =
      algebraMap ℚ ℂ (pr (∑ i ∈ s, c i * algebraMap ℚ ℂ (r i n))) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_mul, mul_comm (c i), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  rw [h1, ← hn, map_zero, map_zero]

/-- A modular function for $\Gamma \supseteq \Gamma'$ is one for $\Gamma'$. -/
theorem IsModularFunction.mono {Γ Γ' : Subgroup SL(2, ℤ)} {f : ℍ → ℂ} (hf : IsModularFunction Γ f)
    (h : Γ' ≤ Γ) : IsModularFunction Γ' f where
  meromorphic := hf.meromorphic
  invariant γ hγ z := hf.invariant γ (h hγ) z
  meromorphic_cusps := hf.meromorphic_cusps

theorem gamma0_le_of_dvd {d M : ℕ} (hd : d ∣ M) :
    CongruenceSubgroup.Gamma0 M ≤ CongruenceSubgroup.Gamma0 d := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.2 hd) hγ

variable {M : ℕ} [NeZero M]

/-- $F_M$ with complex coefficients, as the image of the rational one. -/
noncomputable abbrev modPolyCM (M : ℕ) [NeZero M] : ℂ[X][X] :=
  (modPoly M).map (mapRingHom (algebraMap ℚ ℂ))

theorem modPolyCM_monic : (modPolyCM M).Monic := modPoly_monic.map _

theorem evalJJN_modPolyCM (z : ℍ) : evalJJN M (modPolyCM M) z = 0 :=
  (prop2_4' M).exists_poly.choose_spec.2.2.1 z

theorem natDegree_modPolyCM : (modPolyCM M).natDegree = (modPoly M).natDegree := by
  rw [natDegree_map_eq_of_injective]
  rw [coe_mapRingHom]
  exact map_injective _ (algebraMap ℚ ℂ).injective

theorem evalJJN_modByMonic (G : ℂ[X][X]) (z : ℍ) : evalJJN M (G %ₘ modPolyCM M) z = evalJJN M G z := by
  have h := congrArg (fun P => evalJJNC M P z) (modByMonic_add_div G (modPolyCM M))
  simp only [map_add, map_mul, Pi.add_apply, Pi.mul_apply] at h
  simp only [← evalJJN_eq_evalJJNC] at h
  rw [evalJJN_modPolyCM, zero_mul, add_zero] at h
  exact h

theorem mdiff_evalJJN (G : ℂ[X][X]) : MDiff (evalJJN M G) := by
  have : evalJJN M G = evalJJNC M G := funext fun z => evalJJN_eq_evalJJNC G z
  rw [this]
  exact mdifferentiable_evalJJNHom (RingHom.id ℂ) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)) G

/-- **Modular functions with rational $q$-expansions are in $\mathbb Q(j, j_M)$.** If $A$, $B$ have rational
$q$-expansions, $B \ne 0$, and $A/B$ is a modular function for $\Gamma_0(M)$, then $A\,Q(j, j_M) = B\,P(j, j_M)$ for
some $P, Q \in \mathbb Q[X][Y]$ with $Q(j, j_M) \ne 0$. -/
theorem exists_rat_frac {A B : ℍ → ℂ} (hA : IsRatQExp A) (hB : IsRatQExp B) (hB0 : B ≠ 0)
    (hf : IsModularFunction (CongruenceSubgroup.Gamma0 M) (A / B)) :
    ∃ P Q : ℚ[X][X], evalJJNRat M Q ≠ 0 ∧ ∀ z, A z * evalJJNRat M Q z = B z * evalJJNRat M P z := by
  classical
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  -- Theorem 2.3 over ℂ
  obtain ⟨P, Q, ⟨z0, hz0⟩, hPQ⟩ := thm2_3.rational M hM (A / B) hf
  have hQ0 : evalJJN M Q ≠ 0 := fun h => hz0 (congrFun h z0)
  have hcross : ∀ z, A z * evalJJN M Q z = B z * evalJJN M P z := by
    have hg : MDiff (fun z => A z * evalJJN M Q z - B z * evalJJN M P z) :=
      (hA.mdiff.mul (mdiff_evalJJN Q)).sub (hB.mdiff.mul (mdiff_evalJJN P))
    have hev : ∀ᶠ z in codiscrete ℍ, A z * evalJJN M Q z - B z * evalJJN M P z = 0 := by
      filter_upwards [hPQ, eventually_codiscrete_ne_zero hB.mdiff hB0,
        eventually_codiscrete_ne_zero (mdiff_evalJJN Q) hQ0] with z h1 h2 h3
      simp only [Pi.div_apply] at h1
      rw [div_eq_div_iff h2 h3] at h1
      rw [sub_eq_zero]
      linear_combination h1
    have hfreq : ∃ᶠ z in 𝓝[≠] UpperHalfPlane.I, A z * evalJJN M Q z - B z * evalJJN M P z = 0 :=
      ((eventually_codiscrete_iff_forall_eventually_nhdsNE.1 hev) UpperHalfPlane.I).frequently
    have h0 := UpperHalfPlane.eq_zero_of_frequently hg hfreq
    intro z
    exact sub_eq_zero.1 (congrFun h0 z)
  -- reduce modulo F_M
  set F := modPolyCM M with hF
  set m := F.natDegree with hm
  have hm1 : 1 ≤ m := by
    rw [hm, natDegree_modPolyCM, modPoly_natDegree]
    exact Nat.one_le_iff_ne_zero.mpr (CongruenceSubgroup.Gamma0 M).index_ne_zero_of_finite
  have hF1 : F ≠ 1 := by
    intro h
    have : m = 0 := by rw [hm, h, natDegree_one]
    omega
  set P' := P %ₘ F
  set Q' := Q %ₘ F
  have hP' : ∀ z, evalJJN M P' z = evalJJN M P z := evalJJN_modByMonic P
  have hQ' : ∀ z, evalJJN M Q' z = evalJJN M Q z := evalJJN_modByMonic Q
  have hQ'0 : Q' ≠ 0 := by
    intro h
    apply hz0
    rw [← hQ', h]
    simp [evalJJN]
  obtain ⟨b0, hb0⟩ : ∃ b0, Q'.coeff b0 ≠ 0 := by
    by_contra! H
    exact hQ'0 (Polynomial.ext fun b => by rw [H b, coeff_zero])
  obtain ⟨a0, ha0⟩ : ∃ a0, (Q'.coeff b0).coeff a0 ≠ 0 := by
    by_contra! H
    exact hb0 (Polynomial.ext fun a => by rw [H a, coeff_zero])
  set κ := ((Q'.coeff b0).coeff a0)⁻¹ with hκ
  set P'' := C (C κ) * P' with hP''
  set Q'' := C (C κ) * Q' with hQ''
  have hcoeffκ : ∀ (G : ℂ[X][X]) b a, ((C (C κ) * G).coeff b).coeff a = κ * (G.coeff b).coeff a := by
    intro G b a
    rw [coeff_C_mul, coeff_C_mul]
  have hQ''1 : (Q''.coeff b0).coeff a0 = 1 := by
    rw [hQ'', hcoeffκ, hκ, inv_mul_cancel₀ ha0]
  have hevκ : ∀ (G : ℂ[X][X]) z, evalJJN M (C (C κ) * G) z = κ * evalJJN M G z := by
    intro G z
    rw [evalJJN_eq_evalJJNC, evalJJN_eq_evalJJNC, map_mul, Pi.mul_apply]
    congr 1
    simp [evalJJNHom]
  have hcross'' : ∀ z, A z * evalJJN M Q'' z = B z * evalJJN M P'' z := by
    intro z
    rw [hevκ, hevκ, hP', hQ']
    linear_combination κ * hcross z
  have hdegP : P''.natDegree < m :=
    lt_of_le_of_lt (natDegree_C_mul_le _ _) (natDegree_modByMonic_lt P modPolyCM_monic hF1)
  have hdegQ : Q''.natDegree < m :=
    lt_of_le_of_lt (natDegree_C_mul_le _ _) (natDegree_modByMonic_lt Q modPolyCM_monic hF1)
  -- the degree bound in X
  set D := (Finset.range (m + 1)).sup fun b => max (P''.coeff b).natDegree (Q''.coeff b).natDegree with hD
  have hDP : ∀ b, (P''.coeff b).natDegree ≤ D := by
    intro b
    by_cases hb : b ≤ m
    · exact le_trans (le_max_left _ _)
        (Finset.le_sup (f := fun b => max (P''.coeff b).natDegree (Q''.coeff b).natDegree)
          (Finset.mem_range.2 (by omega)))
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  have hDQ : ∀ b, (Q''.coeff b).natDegree ≤ D := by
    intro b
    by_cases hb : b ≤ m
    · exact le_trans (le_max_right _ _)
        (Finset.le_sup (f := fun b => max (P''.coeff b).natDegree (Q''.coeff b).natDegree)
          (Finset.mem_range.2 (by omega)))
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  -- the projection
  obtain ⟨pr, hpr⟩ := (Algebra.linearMap ℚ ℂ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap ℚ ℂ).injective)
  have hprr : ∀ r : ℚ, pr (algebraMap ℚ ℂ r) = r := fun r => LinearMap.congr_fun hpr r
  set Pq := projPoly pr D m P'' with hPq
  set Qq := projPoly pr D m Q'' with hQq
  set GP := Pq.map (mapRingHom (algebraMap ℚ ℂ)) with hGP
  set GQ := Qq.map (mapRingHom (algebraMap ℚ ℂ)) with hGQ
  have hGPc : ∀ b a, (GP.coeff b).coeff a = algebraMap ℚ ℂ (pr ((P''.coeff b).coeff a)) := by
    intro b a
    rw [hGP, coeff_map, coe_mapRingHom, coeff_map, hPq, projPoly_coeff pr hdegP.le hDP]
  have hGQc : ∀ b a, (GQ.coeff b).coeff a = algebraMap ℚ ℂ (pr ((Q''.coeff b).coeff a)) := by
    intro b a
    rw [hGQ, coeff_map, coe_mapRingHom, coeff_map, hQq, projPoly_coeff pr hdegQ.le hDQ]
  have hGm : ∀ (G : ℂ[X][X]) (G' : ℂ[X][X]), G'.natDegree < m →
      (∀ b a, (G.coeff b).coeff a = algebraMap ℚ ℂ (pr ((G'.coeff b).coeff a))) → G.natDegree < m := by
    intro G G' hG' hc
    have : G.natDegree ≤ m - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro b hb
      refine Polynomial.ext fun a => ?_
      rw [hc, coeff_eq_zero_of_natDegree_lt (p := G') (by omega)]
      simp
    omega
  have hGD : ∀ (G : ℂ[X][X]) (G' : ℂ[X][X]), (∀ b, (G'.coeff b).natDegree ≤ D) →
      (∀ b a, (G.coeff b).coeff a = algebraMap ℚ ℂ (pr ((G'.coeff b).coeff a))) →
      ∀ b, (G.coeff b).natDegree ≤ D := by
    intro G G' hG' hc b
    rw [natDegree_le_iff_coeff_eq_zero]
    intro a ha
    rw [hc, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hG' b) ha), map_zero, map_zero]
  have hGPm := hGm GP P'' hdegP hGPc
  have hGQm := hGm GQ Q'' hdegQ hGQc
  -- the linear relation and its projection
  set s := Finset.range (m + 1) ×ˢ Finset.range (D + 1) with hs
  have hu : ∀ p : ℕ × ℕ, IsRatQExp (uFun M D m p.2 p.1) := fun p => isRatQExp_u hM D m p.2 p.1
  set c : (ℕ × ℕ) ⊕ (ℕ × ℕ) → ℂ := Sum.elim (fun p => (Q''.coeff p.1).coeff p.2)
    (fun p => -(P''.coeff p.1).coeff p.2) with hc
  set u : (ℕ × ℕ) ⊕ (ℕ × ℕ) → ℍ → ℂ := Sum.elim (fun p => A * uFun M D m p.2 p.1)
    (fun p => B * uFun M D m p.2 p.1) with hu'
  have hu2 : ∀ i, IsRatQExp (u i) := by
    rintro (p | p)
    · exact hA.mul (hu p)
    · exact hB.mul (hu p)
  have hexpand : ∀ (G : ℂ[X][X]) (E : ℍ → ℂ), G.natDegree ≤ m → (∀ b, (G.coeff b).natDegree ≤ D) →
      ∀ z, Δ z ^ D * Δ (ofComplex ((M : ℂ) * z)) ^ m * (E z * evalJJN M G z) =
        ∑ p ∈ s, (G.coeff p.1).coeff p.2 * (E z * uFun M D m p.2 p.1 z) := by
    intro G E hGm' hGD' z
    have := clear_denoms (N := M) G hGm' hGD' z
    calc Δ z ^ D * Δ (ofComplex ((M : ℂ) * z)) ^ m * (E z * evalJJN M G z)
        = E z * (Δ z ^ D * Δ (ofComplex ((M : ℂ) * z)) ^ m * evalJJN M G z) := by ring
      _ = _ := by rw [this, Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
  have hrel : ∑ i ∈ s.disjSum s, c i • u i = 0 := by
    funext z
    rw [Finset.sum_disjSum]
    simp only [hc, hu', Sum.elim_inl, Sum.elim_inr, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
      Pi.mul_apply, smul_eq_mul, Pi.zero_apply, neg_mul, Finset.sum_neg_distrib]
    rw [← hexpand Q'' A hdegQ.le hDQ z, ← hexpand P'' B hdegP.le hDP z, hcross'' z]
    ring
  have hrel' := proj_identity (s.disjSum s) c u hu2 hrel pr
  have hcrossq : ∀ z, A z * evalJJN M GQ z = B z * evalJJN M GP z := by
    intro z
    have := congrFun hrel' z
    rw [Finset.sum_disjSum] at this
    simp only [hc, hu', Sum.elim_inl, Sum.elim_inr, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
      Pi.mul_apply, smul_eq_mul, Pi.zero_apply, map_neg, neg_mul, Finset.sum_neg_distrib] at this
    simp only [← hGQc, ← hGPc] at this
    rw [← hexpand GQ A hGQm.le (hGD GQ Q'' hDQ hGQc) z, ← hexpand GP B hGPm.le (hGD GP P'' hDP hGPc) z]
      at this
    have hΔ : Δ z ^ D * Δ (ofComplex ((M : ℂ) * z)) ^ m ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (ModularForm.discriminant_ne_zero z))
        (pow_ne_zero _ (ModularForm.discriminant_ne_zero _))
    have h2 : Δ z ^ D * Δ (ofComplex ((M : ℂ) * z)) ^ m *
        (A z * evalJJN M GQ z - B z * evalJJN M GP z) = 0 := by
      rw [mul_sub]; linear_combination this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hΔ
    · exact sub_eq_zero.1 h
  refine ⟨Pq, Qq, ?_, fun z => ?_⟩
  · -- `Qq` is nonzero of degree `< m`, so `F_M ∤ Qq`
    intro h0
    have hmem : Qq ∈ RingHom.ker (evalJJNRat M) := h0
    rw [ker_evalJJNRat_modPoly, Ideal.mem_span_singleton] at hmem
    have hQq0 : Qq ≠ 0 := by
      intro hq
      have := hGQc b0 a0
      rw [hQ''1, ← map_one (algebraMap ℚ ℂ), hprr, map_one, hGQ, hq, Polynomial.map_zero, coeff_zero,
        coeff_zero] at this
      exact zero_ne_one this
    have hdeg := natDegree_le_of_dvd hmem hQq0
    have hQqdeg : Qq.natDegree < m := by
      rw [← natDegree_map_eq_of_injective (f := mapRingHom (algebraMap ℚ ℂ)) (by
        rw [coe_mapRingHom]; exact map_injective _ (algebraMap ℚ ℂ).injective) Qq]
      exact hGQm
    rw [hm, natDegree_modPolyCM] at hQqdeg
    omega
  · rw [evalJJNHom_apply, evalJJNHom_apply]
    exact hcrossq z

/-- **$j_d \in \mathbb Q(j, j_M)$ for $d \mid M$**: $j_d\,Q(j, j_M) = P(j, j_M)$ with $P, Q \in \mathbb Q[X][Y]$,
$Q(j, j_M) \ne 0$. -/
theorem exists_rat_jN_of_dvd {d : ℕ} (hd : d ∣ M) :
    ∃ P Q : ℚ[X][X], evalJJNRat M Q ≠ 0 ∧ ∀ z, jN d z * evalJJNRat M Q z = evalJJNRat M P z := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne M (Nat.eq_zero_of_zero_dvd hd)
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
  set A := scaleN d ((E₄ : ℍ → ℂ) ^ 3) with hA
  set B := scaleN d (fun z => Δ z) with hB
  have hAr : IsRatQExp A := (IsRatQExp.E4.pow 3).scaleN hd1
  have hBr : IsRatQExp B := IsRatQExp.disc.scaleN hd1
  have hBz : ∀ z, B z ≠ 0 := fun z => ModularForm.discriminant_ne_zero _
  have hB0 : B ≠ 0 := fun h => hBz UpperHalfPlane.I (congrFun h _)
  have hAB : A / B = jN d := by
    funext z
    simp only [Pi.div_apply, hA, hB, scaleN, Pi.pow_apply]
    rw [div_eq_iff (ModularForm.discriminant_ne_zero _), ← jFun_mul_disc]
    rfl
  have hf : IsModularFunction (CongruenceSubgroup.Gamma0 M) (A / B) := by
    rw [hAB]
    exact IsModularFunction.mono (isModularFunction_jN hd1) (gamma0_le_of_dvd hd)
  obtain ⟨P, Q, hQ, hPQ⟩ := exists_rat_frac hAr hBr hB0 hf
  refine ⟨P, Q, hQ, fun z => ?_⟩
  have h1 := hPQ z
  have hAz : A z = jN d z * B z := by
    have := congrFun hAB z
    simp only [Pi.div_apply] at this
    rw [div_eq_iff (hBz z)] at this
    exact this
  rw [hAz, mul_comm (jN d z), mul_assoc] at h1
  exact mul_left_cancel₀ (hBz z) h1

end NumberFieldKB.ModularCurves
