import NumberFieldKB.MilneEC.Ch4Prop81Local
import NumberFieldKB.MilneEC.Ch4Prop82

/-!
# Proposition 8.1: explicit classes in $H^1(\mathbb Q, E[2])$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 8.1 (pdf p. 151).
For $E : y^2 = x^3 + px$ and $u \in \bar{\mathbb Q}^\times$ with $u^2 \in \mathbb Q$, the crossed homomorphism
$\kappa(u) : \sigma \mapsto [\sigma u \ne u]\,T$ with values in $\{0, T\} = E[\varphi] \subset E[2]$ (`kap`).

* `kapFun_mul`, `kapFun_congr`: $\kappa(uw) = \kappa(u) + \kappa(w)$, and $\kappa$ depends only on the automorphisms
  fixing $u$.
* `H1π_kap_root`: for $r^2 = -p$, $\kappa(r)$ is the principal crossed homomorphism of $T_r = (r, 0)$.
* `kap_mem_selmer`: for $u^2 = d \in$ `isogenySelmer (-4p)`, the class of $\kappa(u)$ lies in the Selmer group
  (local points from the quartic torsors, `local_point_of_torsor`).
* `exists_kummer_T`: the Kummer class of $T$ is represented by a continuous crossed homomorphism whose `psi`
  part is the character of $\sqrt p$.
-/

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

-- the algebra structure of `Ch4Selmer` on an algebraic closure, not `DivisionRing.toRatAlgebra`
attribute [local instance 2000] AlgebraicClosure.instAlgebra

namespace NumberFieldKB.MilneEC.Prop81

attribute [local instance] charZero_adicCompletion_rat charZero_completion_rat

variable {p : ℕ} [hp : Fact p.Prime]

/-- $E[2](\bar{\mathbb Q})$ as a $G_{\mathbb Q}$-module. -/
noncomputable abbrev M2 (p : ℕ) : Rep ℤ (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  torsionRep (curveP p) (AlgebraicClosure ℚ) 2

/-- The point $T$ as an element of $E[2]$. -/
noncomputable def Tm : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2 := ⟨ptT, two_smul_ptT⟩

theorem rho_coe (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (m : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2) :
    (((M2 p).ρ σ m : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2) : (EC p (AlgebraicClosure ℚ)).Point) =
      Point.map (W' := (curveP p).toAffine) (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
        (m : (EC p (AlgebraicClosure ℚ)).Point) := rfl

theorem rho_Tm (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : (M2 p).ρ σ Tm = Tm :=
  Subtype.ext (map_ptT _)

theorem Tm_add_Tm : (Tm : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2) + Tm = 0 :=
  Subtype.ext ptT_add_self

theorem Tm_ne_zero : (Tm : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2) ≠ 0 := fun h =>
  ptT_ne_zero (congrArg Subtype.val h)

theorem two_smul_coe (m : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2) :
    (2 : ℤ) • (m : (EC p (AlgebraicClosure ℚ)).Point) = 0 := m.2

/-- The function $\sigma \mapsto [\sigma u \ne u]\,T$. -/
noncomputable def kapFun (u : AlgebraicClosure ℚ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → torsionPoints (curveP p) (AlgebraicClosure ℚ) 2 :=
  fun σ => if σ u = u then 0 else Tm

/-- A square root of a rational number. -/
def IsRatSqrt (u : AlgebraicClosure ℚ) : Prop := ∃ d : ℚ, u ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) d

theorem kapFun_mem {u : AlgebraicClosure ℚ} (hu : IsRatSqrt u) : kapFun (p := p) u ∈ cocycles₁ (M2 p) := by
  rw [mem_cocycles₁_iff]
  intro g h
  by_cases u0 : u = 0
  · simp [kapFun, u0]
  have hne : -u ≠ u := (ne_neg_of_ne_zero u0).symm
  have hT := rho_Tm (p := p) g
  simp only [kapFun, AlgEquiv.mul_apply]
  rcases sq_fixed_sign hu h with hh | hh <;> rcases sq_fixed_sign hu g with hg | hg
  · simp [hh, hg]
  · simp [hh, hg, hne]
  · simp [hh, hg, hne, hT]
  · simp only [hh, map_neg, hg, neg_neg, if_true, hne, if_false, hT]
    rw [Tm_add_Tm]

/-- The crossed homomorphism $\kappa(u)$. -/
noncomputable def kap {u : AlgebraicClosure ℚ} (hu : IsRatSqrt u) : cocycles₁ (M2 p) :=
  ⟨kapFun u, kapFun_mem hu⟩

theorem kap_apply {u : AlgebraicClosure ℚ} (hu : IsRatSqrt u) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (kap (p := p) hu : _ → _) σ = kapFun u σ := rfl

theorem kap_cont {u : AlgebraicClosure ℚ} (hu : IsRatSqrt u) : kap (p := p) hu ∈ contCocycles₁ (M2 p) := by
  obtain ⟨U, hU⟩ := exists_openSubgroup_fixing (K := ℚ) (L := AlgebraicClosure ℚ) {u} (Set.toFinite _)
  let _ : TopologicalSpace (M2 p) := ⊥
  have _ : DiscreteTopology (M2 p) := ⟨rfl⟩
  show Continuous (kapFun (p := p) u)
  refine continuous_of_openSubgroup _ U fun g h hh => ?_
  simp only [kapFun, AlgEquiv.mul_apply, hU h hh u rfl]

theorem kapFun_congr {u w : AlgebraicClosure ℚ}
    (h : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ u = u ↔ σ w = w) :
    kapFun (p := p) u = kapFun w := by
  funext σ; simp only [kapFun, h σ]

theorem kapFun_mul {u w : AlgebraicClosure ℚ} (hu : IsRatSqrt u) (hw : IsRatSqrt w) (u0 : u ≠ 0) (w0 : w ≠ 0) :
    kapFun (p := p) (u * w) = kapFun u + kapFun w := by
  funext σ
  have hneu : -u ≠ u := (ne_neg_of_ne_zero u0).symm
  have hnew : -w ≠ w := (ne_neg_of_ne_zero w0).symm
  have huw : u * w ≠ 0 := mul_ne_zero u0 w0
  have hneuw : -(u * w) ≠ u * w := (ne_neg_of_ne_zero huw).symm
  simp only [kapFun, Pi.add_apply, map_mul]
  rcases sq_fixed_sign hu σ with hs | hs <;> rcases sq_fixed_sign hw σ with ht | ht
  · simp [hs, ht]
  · simp [hs, ht, hnew, hneuw]
  · simp [hs, ht, hneu, hneuw]
  · simp only [hs, ht, neg_mul_neg, if_true, hneu, hnew, if_false]
    rw [Tm_add_Tm]

theorem kapFun_algebraMap (q : ℚ) : kapFun (p := p) (algebraMap ℚ (AlgebraicClosure ℚ) q) = 0 := by
  funext σ; simp [kapFun]

/-- Two square roots whose product is rational are fixed by the same automorphisms. -/
theorem fixed_iff_of_mul_rat {u w : AlgebraicClosure ℚ} (hu : IsRatSqrt u) (hw : IsRatSqrt w) (u0 : u ≠ 0)
    (w0 : w ≠ 0) {q : ℚ} (hq : u * w = algebraMap ℚ (AlgebraicClosure ℚ) q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : σ u = u ↔ σ w = w := by
  have hσ : σ u * σ w = u * w := by rw [← map_mul, hq, σ.commutes]
  have hneu : -u ≠ u := (ne_neg_of_ne_zero u0).symm
  have hnew : -w ≠ w := (ne_neg_of_ne_zero w0).symm
  have huw : u * w ≠ 0 := mul_ne_zero u0 w0
  rcases sq_fixed_sign hu σ with hs | hs <;> rcases sq_fixed_sign hw σ with ht | ht
  · simp [hs, ht]
  · rw [hs, ht] at hσ; exfalso; apply huw; linear_combination -hσ / 2
  · rw [hs, ht] at hσ; exfalso; apply huw; linear_combination -hσ / 2
  · simp [hs, ht, hneu, hnew]

/-- For $r^2 = -p$, $\kappa(r)$ is principal: it is $\sigma \mapsto \sigma T_r - T_r$. -/
theorem H1π_kap_root {r : AlgebraicClosure ℚ} (hr : r ^ 2 = -(p : AlgebraicClosure ℚ)) (hu : IsRatSqrt r) :
    H1π (M2 p) (kap hu) = 0 := by
  rw [H1π_eq_zero_iff]
  have hrns := nonsingular (p := p) (L := AlgebraicClosure ℚ) (x := r) (y := 0)
    (by linear_combination (-r) * hr)
  have r0 := root_ne_zero hr
  refine ⟨(⟨Point.some r 0 hrns, two_smul_root hrns⟩ : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2), ?_⟩
  funext σ
  rw [d₀₁_hom_apply]
  apply Subtype.ext
  show Point.map (W' := (curveP p).toAffine) (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
      (Point.some r 0 hrns) - Point.some r 0 hrns =
        ((kapFun (p := p) r σ : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2) :
          (EC p (AlgebraicClosure ℚ)).Point)
  rw [Point.map_some]
  simp only [kapFun]
  rcases sq_fixed_sign hu σ with hs | hs
  · rw [if_pos hs]
    show _ = (0 : (EC p (AlgebraicClosure ℚ)).Point)
    rw [sub_eq_zero]
    exact some_eq_some' hs (by simp)
  · rw [if_neg (by rw [hs]; exact (ne_neg_of_ne_zero r0).symm)]
    have hneg : -Point.some r 0 hrns = Point.some r 0 hrns := by
      rw [neg_eq_iff_add_eq_zero, root_add_self]
    rw [sub_eq_add_neg, hneg]
    have hns' := nonsingular (p := p) (L := AlgebraicClosure ℚ) (x := -r) (y := 0)
      (by linear_combination r * hr)
    have key : ∀ h' : (EC p (AlgebraicClosure ℚ)).Nonsingular (σ r) (σ 0),
        Point.some (σ r) (σ 0) h' + Point.some r 0 hrns = ptT := by
      intro h'
      have e : Point.some (σ r) (σ 0) h' = Point.some (-r) 0 hns' := some_eq_some' hs (by simp)
      rw [e, add_comm]
      exact root_add_neg_root hr hrns _
    exact key _

/-! ### Selmer membership of $\kappa(u)$ -/

/-- Local triviality of $\kappa(u)$ at a field $F \supseteq \mathbb Q$ where the quartic
$N^2 = dM^4 - (4p/d)e^4$ is solvable. -/
theorem loc_kap (F : Type) [Field F] {_ : Algebra ℚ F} [CharZero F] {u : AlgebraicClosure ℚ} {d : ℚ}
    (hd : d ≠ 0) (hu : u ^ 2 = (d : AlgebraicClosure ℚ)) (hts : TorsorSolvable F (-4 * p) d) :
    locTorsion F (curveP p) 2 (H1π (M2 p) (kap (p := p) ⟨d, by rw [hu, eq_ratCast]⟩)) = 0 := by
  rw [locTorsion_eq_zero_iff]
  have hu' : (closureEmb F u) ^ 2 = (d : AlgebraicClosure F) := by rw [← map_pow, hu, map_ratCast]
  obtain ⟨P, hP⟩ := local_point_of_torsor (p := p) (F := F) hd hu' hts
  refine ⟨P, fun σ => ?_⟩
  have e := hP σ
  simp only [gact] at e
  rw [e, kap_apply]
  simp only [kapFun, decompHom_fixed_iff]
  split_ifs
  · rfl
  · exact map_ptT _

/-- For $u^2 = d$ with $d$ in the Selmer group of $\hat\varphi$ (local solvability of
$N^2 = dM^4 - (4p/d)e^4$), the class of $\kappa(u)$ lies in $S^{(2)}(E/\mathbb Q)$. -/
theorem kap_mem_selmer {u : AlgebraicClosure ℚ} {d : ℚ} (hu : u ^ 2 = (d : AlgebraicClosure ℚ))
    (hd : d ∈ isogenySelmer (-4 * p)) :
    H1π (M2 p) (kap (p := p) ⟨d, by rw [hu, eq_ratCast]⟩) ∈ selmerGroup ℚ (curveP p) 2 := by
  obtain ⟨hfin, hinf⟩ := places_of_mem_isogenySelmer hd
  rw [mem_selmerGroup_iff]
  refine ⟨⟨_, kap_cont _, rfl⟩, fun v => ?_, fun w => ?_⟩
  · exact loc_kap _ hd.1 hu (hfin v)
  · exact loc_kap _ hd.1 hu (hinf w)

/-! ### The Kummer class of $T$ -/

instance curveP_isElliptic' : (curveP p).IsElliptic := curveP_isElliptic hp.out.ne_zero

theorem map_pointT : Point.map (W' := (curveP p).toAffine) (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (IsogenyDescent.pointT p) =
    (ptT : (EC p (AlgebraicClosure ℚ)).Point) := by
  unfold IsogenyDescent.pointT ptT
  rw [Point.map_some]
  exact some_eq_some' (by simp) (by simp)

/-- **The Kummer class of $T$.**  It is the class of a continuous crossed homomorphism $w$ whose `psi` part is
the character of a square root $x_p$ of $p$: $w(\sigma) = \sigma Q - Q$ for a half $Q = (x_p, y)$ of $T$. -/
theorem exists_kummer_T :
    ∃ (w : cocycles₁ (M2 p)) (xp : AlgebraicClosure ℚ), w ∈ contCocycles₁ (M2 p) ∧
      H1π (M2 p) w = kummerMap (curveP p) lemma2_1 2 two_ne_zero (IsogenyDescent.pointT p) ∧
      xp ^ 2 = (p : AlgebraicClosure ℚ) ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        psi ((w σ : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2) : (EC p (AlgebraicClosure ℚ)).Point) = 0 ↔
          σ xp = xp := by
  obtain ⟨Q, hQ⟩ := Lemma2_1.surjective_baseChange (curveP p) lemma2_1 (AlgebraicClosure ℚ) 2 two_ne_zero
    (Point.map (W' := (curveP p).toAffine) (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (IsogenyDescent.pointT p))
  have hQ' : (2 : ℤ) • Q = Point.map (W' := (curveP p).toAffine) (Algebra.ofId ℚ (AlgebraicClosure ℚ))
      (IsogenyDescent.pointT p) := hQ
  let c : cocycles₁ (pointsRep (curveP p) (AlgebraicClosure ℚ)) :=
    ⟨d₀₁ (pointsRep (curveP p) (AlgebraicClosure ℚ)) Q, coboundaries₁_le_cocycles₁ _ ⟨Q, rfl⟩⟩
  have hcoe : ∀ σ, (c σ : (EC p (AlgebraicClosure ℚ)).Point) =
      Point.map (W' := (curveP p).toAffine) (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) Q - Q :=
    fun σ => by
      change (d₀₁ (pointsRep (curveP p) (AlgebraicClosure ℚ)) Q) σ = _
      rw [d₀₁_hom_apply]
      rfl
  have hc : ∀ σ, (2 : ℤ) • (c σ : (EC p (AlgebraicClosure ℚ)).Point) = 0 := fun σ => by
    rw [hcoe, smul_sub, ← map_zsmul, hQ', map_ofId_fixed, sub_self]
  obtain ⟨b, hb⟩ := exists_torsionCocycle (curveP p) (AlgebraicClosure ℚ) 2 c hc
  have hkum := kummerMap_apply (curveP p) lemma2_1 2 two_ne_zero (IsogenyDescent.pointT p) Q hQ' b
    (fun σ => (hb σ).trans (hcoe σ))
  have hcont : b ∈ contCocycles₁ (M2 p) := by
    have hfun : (torsionIncl (curveP p) (AlgebraicClosure ℚ) 2).hom ∘ (b : _ → _) = (c : _ → _) :=
      funext fun σ => hb σ
    have hc' : @Continuous _ _ _ ⊥ (c : _ → _) :=
      continuous_of_mem_coboundaries₁ _ (pointsRep_isDiscreteModule (curveP p) (AlgebraicClosure ℚ)) c
        ⟨Q, rfl⟩
    exact (continuous_bot_comp_iff _ _ (torsionIncl_hom_injective (curveP p) (AlgebraicClosure ℚ) 2)).1
      (hfun ▸ hc')
  obtain ⟨x, y, h, hQe, hx2, hxc⟩ := halving_T Q (hQ'.trans map_pointT)
  have hx0 : x ≠ 0 := by
    rintro rfl; apply p_ne_zero (L := AlgebraicClosure ℚ) (p := p); rw [← hx2]; ring
  refine ⟨b, x, hcont, hkum.symm, hx2, fun σ => ?_⟩
  have hbσ : ((b σ : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2) : (EC p (AlgebraicClosure ℚ)).Point) =
      Point.map (W' := (curveP p).toAffine) (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) Q - Q :=
    (hb σ).trans (hcoe σ)
  have h2e : (2 : ℤ) • ((b σ : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2) :
      (EC p (AlgebraicClosure ℚ)).Point) = 0 := (b σ).2
  have hσx : σ x = xc (Q + ((b σ : torsionPoints (curveP p) (AlgebraicClosure ℚ) 2) :
      (EC p (AlgebraicClosure ℚ)).Point)) := by
    rw [hbσ, add_sub_cancel, xc_map, hQe]; rfl
  rw [hσx, hxc _ h2e]
  split_ifs with hψ
  · exact iff_of_true hψ rfl
  · simp only [hψ, false_iff]
    exact (ne_neg_of_ne_zero hx0).symm

end NumberFieldKB.MilneEC.Prop81
