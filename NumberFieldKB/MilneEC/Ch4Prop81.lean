import NumberFieldKB.MilneEC.Ch4Prop81Classes

/-!
# Proposition 8.1: $S^{(2)}(E/\mathbb Q) \cong (\mathbb Z/2)^3$ for $E : Y^2 = X^3 + pX$, $p \equiv 1 \bmod 8$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 8.1 (pdf p. 151),
quoting Silverman (1986), X.4.9 and X.6.2.  This file proves the named statement `Prop8_1` for the
Galois-cohomological Selmer group `selmerGroup ℚ (curveP p) 2` (`prop_8_1`), and hence Proposition 8.2 with no
named input (`prop_8_2`).

## Proof
Write $E[2] = \{0, T, T_+, T_-\}$ and `psi` $: E[2] \to \mathbb Z/2$ for the map with kernel $\{0, T\} = E[\varphi]$.
For a class $c = [z] \in S^{(2)}$:

1. $\sigma \mapsto$ `psi` $z(\sigma)$ is a continuous homomorphism, so it is the character of $\sqrt{d_1}$ for some
   $d_1 \in \mathbb Q^\times$ (`exists_sqrt_of_hom`).  At every place the local triviality of $c$ gives a point of
   $N^2 = d_1M^4 + (p/d_1)e^4$ (`torsor_p_of_local`), so $d_1 \in \{1, p\}\,\mathbb Q^{\times 2}$
   (`prop_8_1_explicit`).  Subtracting the Kummer class of $T$ when $d_1 \equiv p$ (`exists_kummer_T`), we may
   assume $z$ takes values in $\{0, T\}$.
2. Then $z = \kappa(\sqrt{d_2})$ (`exists_sqrt_of_hom` again), and the local triviality gives a point of
   $N^2 = d_2M^4 - (4p/d_2)e^4$ at every place (`torsor_neg4p_of_local`), so $d_2 \in \pm 2^{\{0,1\}} p^{\{0,1\}}
   \mathbb Q^{\times 2}$; $\kappa(\sqrt{-p})$ is principal (`H1π_kap_root`), so $[z] = [\kappa(\sqrt{\pm 2^{b}})]$.

Hence $S^{(2)}$ is the image of $\Phi(a, b, e) = [\kappa(\sqrt{(-1)^a 2^b})] + e\,\delta(T)$
(`Phi_mem`, `exists_Phi_eq`).  $\Phi$ is injective (`Phi_injective`): the `psi` part detects $e$ (since $p$ is not a
square), and $\kappa(\sqrt{d})$ is principal only for $d \in \mathbb Q^{\times 2} \cup -p\,\mathbb Q^{\times 2}$.
So $\#S^{(2)} = 8$, and a group killed by $2$ with $8$ elements is $(\mathbb Z/2)^3$.
-/

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

attribute [local instance 2000] AlgebraicClosure.instAlgebra

namespace NumberFieldKB.MilneEC.Prop81

attribute [local instance] charZero_adicCompletion_rat charZero_completion_rat

variable {p : ℕ} [hp : Fact p.Prime]

local notation "Qb" => AlgebraicClosure ℚ
local notation "GQ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

/-! ### Rational squares -/

theorem nonneg_of_isSquare {q : ℚ} (h : IsSquare q) : 0 ≤ q := by
  obtain ⟨r, rfl⟩ := h; exact mul_self_nonneg r

theorem not_isSquare_of_odd (ℓ : ℕ) [Fact ℓ.Prime] {q : ℚ} (hq : q ≠ 0) (h : Odd (padicValRat ℓ q)) :
    ¬ IsSquare q := by
  rintro ⟨r, rfl⟩
  have hr : r ≠ 0 := by rintro rfl; simp at hq
  rw [padicValRat.mul hr hr] at h
  exact (Int.not_even_iff_odd.2 h) ⟨_, rfl⟩

theorem not_isSquare_p : ¬ IsSquare (p : ℚ) := by
  refine not_isSquare_of_odd p (by exact_mod_cast hp.out.ne_zero) ?_
  rw [padicValRat.self hp.out.one_lt]; exact odd_one

/-! ### Kummer data -/

/-- A cocycle with values in $E[2]$ composed with `psi` is a homomorphism. -/
theorem psi_cocycle (z : cocycles₁ (M2 p)) (σ τ : GQ) :
    psi (((z : _ → _) (σ * τ) : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) =
      psi (((z : _ → _) σ : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) +
        psi (((z : _ → _) τ : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) := by
  have hz := (mem_cocycles₁_iff (A := M2 p) z.1).1 z.2 σ τ
  have : (((z : _ → _) (σ * τ) : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) =
      Point.map (W' := (curveP p).toAffine) (σ : Qb →ₐ[ℚ] Qb)
        (((z : _ → _) τ : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) +
      (((z : _ → _) σ : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) := by
    rw [show (z : _ → _) (σ * τ) = z.1 (σ * τ) from rfl, hz]; rfl
  rw [this, psi_add _ _ (by rw [← map_zsmul, two_smul_coe, map_zero]) (two_smul_coe _), psi_map, add_comm]

theorem isOpen_of_cont (z : cocycles₁ (M2 p)) (hz : z ∈ contCocycles₁ (M2 p))
    (f : torsionPoints (curveP p) Qb 2 → ZMod 2) : IsOpen {σ : GQ | f ((z : _ → _) σ) = 0} := by
  have hz' : @Continuous GQ (M2 p) _ ⊥ (z : GQ → M2 p) := hz
  exact continuous_def.1 hz' {m | f m = 0} trivial

/-- The `psi` part of a continuous cocycle is the character of a square root of a rational number. -/
theorem exists_sqrt_psi (z : cocycles₁ (M2 p)) (hz : z ∈ contCocycles₁ (M2 p)) :
    ∃ u : Qb, u ≠ 0 ∧ IsRatSqrt u ∧
      ∀ σ : GQ, σ u = u ↔ psi (((z : _ → _) σ : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) = 0 :=
  exists_sqrt_of_hom ℚ _ (psi_cocycle z) (isOpen_of_cont z hz fun m => psi (m : (EC p (AlgebraicClosure ℚ)).Point))

/-- Values of a cocycle in the kernel of `psi` are $0$ or $T$. -/
theorem eq_zero_or_T (m : torsionPoints (curveP p) Qb 2) (h : psi (m : (EC p (AlgebraicClosure ℚ)).Point) = 0) : m = 0 ∨ m = Tm := by
  rcases two_torsion_cases (m : (EC p (AlgebraicClosure ℚ)).Point) m.2 with h0 | hT | ⟨r, hr, er, he⟩
  · left; exact Subtype.ext h0
  · right; exact Subtype.ext hT
  · rw [he, psi_root hr er] at h; exact absurd h one_ne_zero

/-- A continuous cocycle with values in $\{0, T\}$ is $\kappa(u)$ for a square root $u$ of a rational number. -/
theorem exists_sqrt_kap (z : cocycles₁ (M2 p)) (hz : z ∈ contCocycles₁ (M2 p))
    (hψ : ∀ σ, psi (((z : _ → _) σ : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) = 0) :
    ∃ (u : Qb) (hu : IsRatSqrt u), u ≠ 0 ∧ z = kap (p := p) hu := by
  let f : torsionPoints (curveP p) Qb 2 → ZMod 2 := fun m => if m = 0 then 0 else 1
  have hf : ∀ σ τ : GQ, f ((z : _ → _) (σ * τ)) = f ((z : _ → _) σ) + f ((z : _ → _) τ) := by
    intro σ τ
    have hz' := (mem_cocycles₁_iff (A := M2 p) z.1).1 z.2 σ τ
    have e : (z : _ → _) (σ * τ) = (M2 p).ρ σ ((z : _ → _) τ) + (z : _ → _) σ := hz'
    rw [e]
    have hT : (torsionRepresentation (curveP p) Qb 2) σ Tm = Tm := rho_Tm σ
    rcases eq_zero_or_T _ (hψ σ) with h1 | h1 <;> rcases eq_zero_or_T _ (hψ τ) with h2 | h2 <;>
      simp only [h1, h2, map_zero, hT, add_zero, zero_add, Tm_add_Tm, f, Tm_ne_zero, if_true,
        if_false] <;> decide
  obtain ⟨u, u0, hu, hfix⟩ := exists_sqrt_of_hom ℚ _ hf (isOpen_of_cont z hz f)
  refine ⟨u, hu, u0, ?_⟩
  apply cocycles₁_ext
  intro σ
  rw [kap_apply]
  simp only [kapFun]
  rcases eq_zero_or_T _ (hψ σ) with h1 | h1
  · rw [if_pos ((hfix σ).2 (by simp [f, h1])), h1]
  · rw [if_neg (fun h => by have := (hfix σ).1 h; simp [f, h1, Tm_ne_zero] at this), h1]

/-! ### The local conditions at the places of $\mathbb Q$ -/

theorem psi_local (F : Type) [Field F] {_ : Algebra ℚ F} [CharZero F] (z : cocycles₁ (M2 p)) {u : Qb}
    {d : ℚ} (hd : d ≠ 0) (hu : u ^ 2 = (d : Qb))
    (hfix : ∀ σ : GQ, σ u = u ↔ psi (((z : _ → _) σ : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) = 0)
    (hloc : locTorsion F (curveP p) 2 (H1π (M2 p) z) = 0) : TorsorSolvable F p d := by
  rw [locTorsion_eq_zero_iff] at hloc
  obtain ⟨P, hP⟩ := hloc
  have hu' : (closureEmb F u) ^ 2 = (d : AlgebraicClosure F) := by rw [← map_pow, hu, map_ratCast]
  have hP' : ∀ σ, gact (p := p) σ P - P = Point.map (W' := (curveP p).toAffine) (closureEmb F)
      (((z : _ → _) (decompHom F σ) : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) := fun σ => (hP σ).symm
  refine torsor_p_of_local (F := F) hd hu' P (fun σ => ?_) (fun σ => ?_)
  · rw [hP', ← map_zsmul, two_smul_coe, map_zero]
  · rw [hP', psi_map, ← hfix, decompHom_fixed_iff]

theorem kap_local (F : Type) [Field F] {_ : Algebra ℚ F} [CharZero F] {u : Qb} (hu0 : IsRatSqrt u) {d : ℚ}
    (hd : d ≠ 0) (hu : u ^ 2 = (d : Qb))
    (hloc : locTorsion F (curveP p) 2 (H1π (M2 p) (kap (p := p) hu0)) = 0) : TorsorSolvable F (-4 * p) d := by
  rw [locTorsion_eq_zero_iff] at hloc
  obtain ⟨P, hP⟩ := hloc
  have hu' : (closureEmb F u) ^ 2 = (d : AlgebraicClosure F) := by rw [← map_pow, hu, map_ratCast]
  refine torsor_neg4p_of_local (F := F) hd hu' P (fun σ => ?_)
  have e : gact (p := p) σ P - P = _ := (hP σ).symm
  rw [e, kap_apply]
  simp only [kapFun, decompHom_fixed_iff]
  split_ifs
  · rfl
  · exact map_ptT _

/-! ### The map $\Phi$ -/

/-- Square roots of $-1$ and $2$. -/
theorem exists_sqrt_rat (d : ℚ) : ∃ u : Qb, u ^ 2 = (d : Qb) :=
  IsAlgClosed.exists_pow_nat_eq (d : Qb) two_pos

/-- The rational number $(-1)^a 2^b$. -/
def dv (a b : ZMod 2) : ℚ := (if a = 1 then -1 else 1) * (if b = 1 then 2 else 1)

theorem dv_ne_zero (a b : ZMod 2) : dv a b ≠ 0 := by
  unfold dv; split_ifs <;> norm_num

theorem padicValRat_dv (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (a b : ZMod 2) : padicValRat ℓ (dv a b) = 0 := by
  have h2 : padicValRat ℓ (2 : ℚ) = 0 := by
    have := IsogenyDescent.padicValRat_natCast_prime_ne (Fact.out : ℓ.Prime) Nat.prime_two hℓ
    exact_mod_cast this
  unfold dv
  split_ifs <;> simp [padicValRat.neg, h2, padicValRat.mul]

/-- $(-1)^a 2^b (-1)^{a'} 2^{b'}$ is a square only for $(a, b) = (a', b')$. -/
theorem eq_of_isSquare_dv {a b a' b' : ZMod 2} (h : IsSquare (dv a b * dv a' b')) : a = a' ∧ b = b' := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  have n2 : ¬ IsSquare (2 : ℚ) := not_isSquare_of_odd 2 (by norm_num) (by rw [hv2]; exact odd_one)
  have hneg : ∀ q : ℚ, q < 0 → ¬ IsSquare q := fun q hq hs => absurd (nonneg_of_isSquare hs) (not_le.2 hq)
  have n2' : ∀ q : ℚ, q = 2 → ¬ IsSquare q := fun q hq => hq ▸ n2
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp only [dv] at h <;> norm_num at h <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd h (by rintro ⟨r, hr⟩; have : r ≤ 2 := by nlinarith
                         interval_cases r <;> omega)
    | exact (hneg _ (by norm_num) h).elim

/-- $-p\,(-1)^a 2^b (-1)^{a'} 2^{b'}$ is never a square. -/
theorem not_isSquare_neg_p_dv (hp2 : p ≠ 2) (a b a' b' : ZMod 2) :
    ¬ IsSquare (dv a b * dv a' b' * (-(p : ℚ))) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine not_isSquare_of_odd p (mul_ne_zero (mul_ne_zero (dv_ne_zero a b) (dv_ne_zero a' b'))
    (neg_ne_zero.2 hp0)) ?_
  rw [padicValRat.mul (mul_ne_zero (dv_ne_zero a b) (dv_ne_zero a' b')) (neg_ne_zero.2 hp0),
    padicValRat.mul (dv_ne_zero a b) (dv_ne_zero a' b'), padicValRat_dv p hp2, padicValRat_dv p hp2,
    padicValRat.neg, padicValRat.self hp.out.one_lt]
  exact odd_one

/-- Fixed square roots of $-1$ and $2$ in $\bar{\mathbb Q}$. -/
noncomputable def ri : Qb := Classical.choose (exists_sqrt_rat (-1))
noncomputable def r2 : Qb := Classical.choose (exists_sqrt_rat 2)

theorem ri_sq : ri ^ 2 = ((-1 : ℚ) : Qb) := Classical.choose_spec (exists_sqrt_rat (-1))
theorem r2_sq : r2 ^ 2 = ((2 : ℚ) : Qb) := Classical.choose_spec (exists_sqrt_rat 2)

/-- The square root $\sqrt{(-1)^a 2^b}$. -/
noncomputable def rv (a b : ZMod 2) : Qb := (if a = 1 then ri else 1) * (if b = 1 then r2 else 1)

theorem rv_sq (a b : ZMod 2) : rv a b ^ 2 = (dv a b : Qb) := by
  unfold rv dv
  rw [mul_pow]
  split_ifs <;> simp [ri_sq, r2_sq]

theorem rv_isRatSqrt (a b : ZMod 2) : IsRatSqrt (rv a b) := ⟨dv a b, by rw [rv_sq, eq_ratCast]⟩

theorem ne_zero_of_sq {u : Qb} {d : ℚ} (hu : u ^ 2 = (d : Qb)) (hd : d ≠ 0) : u ≠ 0 := by
  rintro rfl; apply hd; exact_mod_cast (by rw [← hu]; ring : ((d : ℚ) : Qb) = 0)

theorem dv_mem (hp8 : p % 8 = 1) (a b : ZMod 2) : dv a b ∈ isogenySelmer (-4 * p) := by
  rw [(prop_8_1_explicit p hp8).2]
  refine ⟨dv_ne_zero a b, fun ℓ hℓ h2 _ => ?_⟩
  have := Fact.mk hℓ
  rw [padicValRat_dv ℓ h2]; exact ⟨0, rfl⟩

/-- The Kummer class $\delta(T)$ of the $2$-torsion point $T$. -/
noncomputable def sP (p : ℕ) [Fact p.Prime] : H1 (M2 p) :=
  kummerMap (curveP p) lemma2_1 2 two_ne_zero (IsogenyDescent.pointT p)

theorem sP_mem : sP p ∈ selmerGroup ℚ (curveP p) 2 :=
  (exact_23 ℚ (curveP p) lemma2_1 2 two_ne_zero).1 ⟨_, rfl⟩

/-- $\Phi(a, b, e) = [\kappa(\sqrt{(-1)^a 2^b})] + e\,\delta(T)$. -/
noncomputable def Phi (v : Fin 3 → ZMod 2) : H1 (M2 p) :=
  H1π (M2 p) (kap (p := p) (rv_isRatSqrt (v 0) (v 1))) + (v 2).val • sP p

theorem Phi_mem (hp8 : p % 8 = 1) (v : Fin 3 → ZMod 2) : Phi (p := p) v ∈ selmerGroup ℚ (curveP p) 2 :=
  add_mem (kap_mem_selmer (rv_sq (v 0) (v 1)) (dv_mem hp8 _ _)) (AddSubgroup.nsmul_mem _ sP_mem _)

/-! ### Injectivity of $\Phi$ -/

/-- `psi` as a homomorphism on $E[2]$. -/
noncomputable def psiHom : torsionPoints (curveP p) Qb 2 →+ ZMod 2 where
  toFun m := psi (m : (EC p (AlgebraicClosure ℚ)).Point)
  map_zero' := rfl
  map_add' m m' := psi_add _ _ m.2 m'.2

theorem psiHom_apply (m : torsionPoints (curveP p) Qb 2) :
    psiHom m = psi (m : (EC p (AlgebraicClosure ℚ)).Point) := rfl

theorem psiHom_kapFun (u : Qb) (σ : GQ) : psiHom (kapFun (p := p) u σ) = 0 := by
  unfold kapFun; split_ifs
  · exact map_zero _
  · exact psi_T (p := p)

theorem psiHom_coboundary (m : torsionPoints (curveP p) Qb 2) (σ : GQ) :
    psiHom ((M2 p).ρ σ m - m) = 0 := by
  rw [map_sub, psiHom_apply, psiHom_apply, rho_coe, psi_map, sub_self]

theorem torsion_add_self (x : torsionPoints (curveP p) Qb 2) : x + x = 0 :=
  Subtype.ext (by rw [AddSubgroup.coe_add, ← two_zsmul]; exact x.2)

theorem torsion_neg (x : torsionPoints (curveP p) Qb 2) : -x = x := by
  rw [neg_eq_iff_add_eq_zero]; exact torsion_add_self x

theorem fixed_iff_of_kapFun_eq {u w : Qb} (h : kapFun (p := p) u = kapFun w) (σ : GQ) :
    σ u = u ↔ σ w = w := by
  have := congrFun h σ
  simp only [kapFun] at this
  split_ifs at this with h1 h2 h2
  · exact iff_of_true h1 h2
  · exact absurd this.symm Tm_ne_zero
  · exact absurd this Tm_ne_zero
  · exact iff_of_false h1 h2

/-- For $r^2 = -p$, $\kappa(r)(\sigma) = \sigma T_r - T_r$. -/
theorem kapFun_root {r : Qb} (hr : (EC p (AlgebraicClosure ℚ)).Nonsingular r 0) (er : r ^ 2 = -(p : Qb))
    (σ : GQ) : ((kapFun (p := p) r σ : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) =
      Point.map (W' := (curveP p).toAffine) (σ : Qb →ₐ[ℚ] Qb) (Point.some r 0 hr) - Point.some r 0 hr := by
  have hrsq : IsRatSqrt r := ⟨-(p : ℚ), by rw [er, eq_ratCast]; push_cast; ring⟩
  rw [Point.map_some]
  simp only [kapFun]
  rcases sq_fixed_sign hrsq σ with hs | hs
  · rw [if_pos hs]
    show (0 : (EC p (AlgebraicClosure ℚ)).Point) = _
    rw [eq_comm, sub_eq_zero]; exact some_eq_some' hs (by simp)
  · rw [if_neg (by rw [hs]; exact (ne_neg_of_ne_zero (root_ne_zero er)).symm)]
    have hneg : -Point.some r 0 hr = Point.some r 0 hr := by
      rw [neg_eq_iff_add_eq_zero, root_add_self]
    rw [sub_eq_add_neg, hneg]
    have hns' := nonsingular (p := p) (L := AlgebraicClosure ℚ) (x := -r) (y := 0)
      (by linear_combination r * er)
    have key : ∀ h' : (EC p (AlgebraicClosure ℚ)).Nonsingular (σ r) (σ 0),
        Point.some (σ r) (σ 0) h' + Point.some r 0 hr = ptT := by
      intro h'
      have e : Point.some (σ r) (σ 0) h' = Point.some (-r) 0 hns' := some_eq_some' hs (by simp)
      rw [e, add_comm]
      exact root_add_neg_root er hr _
    exact (key _).symm

/-- Two rational square roots whose squares have square product define the same $\kappa$. -/
theorem kapFun_eq_of_isSquare {u t : Qb} {d d' : ℚ} (hu : u ^ 2 = (d : Qb)) (ht : t ^ 2 = (d' : Qb))
    (hd : d ≠ 0) (hd' : d' ≠ 0) (h : IsSquare (d * d')) : kapFun (p := p) u = kapFun t := by
  obtain ⟨k, hk⟩ := h
  have u0 := ne_zero_of_sq hu hd
  have t0 := ne_zero_of_sq ht hd'
  have hu' : IsRatSqrt u := ⟨d, by rw [hu, eq_ratCast]⟩
  have ht' : IsRatSqrt t := ⟨d', by rw [ht, eq_ratCast]⟩
  have hsq : (u * t - (k : Qb)) * (u * t + (k : Qb)) = 0 := by
    have : ((d * d' : ℚ) : Qb) = ((k * k : ℚ) : Qb) := by rw [hk]
    push_cast at this
    linear_combination hu * t ^ 2 + (d : Qb) * ht + this
  apply kapFun_congr
  rcases mul_eq_zero.1 hsq with h0 | h0
  · exact fixed_iff_of_mul_rat hu' ht' u0 t0 (q := k) (by rw [eq_ratCast]; linear_combination h0)
  · exact fixed_iff_of_mul_rat hu' ht' u0 t0 (q := -k) (by rw [eq_ratCast]; push_cast; linear_combination h0)

theorem Phi_injective (hp8 : p % 8 = 1) : Function.Injective (Phi (p := p)) := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp8
  intro v v' hvv
  obtain ⟨w, xp, -, hwK, hxp, hwψ⟩ := exists_kummer_T (p := p)
  let Z : (Fin 3 → ZMod 2) → cocycles₁ (M2 p) := fun v =>
    kap (p := p) (rv_isRatSqrt (v 0) (v 1)) + (v 2).val • w
  have hZ : ∀ v, H1π (M2 p) (Z v) = Phi v := fun v => by
    simp only [Z, Phi, map_add, map_nsmul, hwK, sP]
  have h0 : H1π (M2 p) (Z v - Z v') = 0 := by rw [map_sub, hZ, hZ, hvv, sub_self]
  rw [H1π_eq_zero_iff] at h0
  obtain ⟨m, hm⟩ := h0
  have hmσ : ∀ σ, (M2 p).ρ σ m - m = ((Z v - Z v' : cocycles₁ (M2 p)) : _ → _) σ := fun σ => by
    rw [← d₀₁_hom_apply]; exact congrFun hm σ
  have hZσ : ∀ σ, ((Z v - Z v' : cocycles₁ (M2 p)) : _ → _) σ =
      kapFun (rv (v 0) (v 1)) σ + (v 2).val • (w : _ → _) σ -
        (kapFun (rv (v' 0) (v' 1)) σ + (v' 2).val • (w : _ → _) σ) := fun σ => rfl
  have hχ : ∀ σ : GQ, psiHom ((w : _ → _) σ) = if σ xp = xp then 0 else 1 := by
    intro σ
    rw [psiHom_apply]
    split_ifs with h
    · exact (hwψ σ).2 h
    · have hval : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact hval _ (fun e => h ((hwψ σ).1 e))
  -- the `psi` part detects the last coordinate
  have h2 : v 2 = v' 2 := by
    by_contra hne
    obtain ⟨σ, hσ⟩ : ∃ σ : GQ, σ xp ≠ xp := by
      by_contra hall
      push_neg at hall
      obtain ⟨k, hk⟩ := mem_range_of_fixed (K := ℚ) hall
      apply not_isSquare_p (p := p)
      refine ⟨k, (algebraMap ℚ Qb).injective ?_⟩
      rw [map_mul _ k k, hk, ← sq, hxp, eq_ratCast]; push_cast; ring
    have := congrArg psiHom (hmσ σ)
    rw [psiHom_coboundary, hZσ, map_sub, map_add, map_add, map_nsmul, map_nsmul, psiHom_kapFun,
      psiHom_kapFun, hχ, if_neg hσ] at this
    apply hne
    simp only [zero_add, nsmul_eq_mul, mul_one, ZMod.natCast_val, ZMod.cast_id', id] at this
    linear_combination -this
  set a := v 0 with ha
  set b := v 1 with hb
  set a' := v' 0 with ha'
  set b' := v' 1 with hb'
  have hprod : ∀ σ, kapFun (p := p) (rv a b * rv a' b') σ = (M2 p).ρ σ m - m := by
    intro σ
    rw [hmσ σ, hZσ, kapFun_mul (rv_isRatSqrt a b) (rv_isRatSqrt a' b')
      (ne_zero_of_sq (rv_sq a b) (dv_ne_zero a b)) (ne_zero_of_sq (rv_sq a' b') (dv_ne_zero a' b')), h2]
    rw [Pi.add_apply, sub_eq_add_neg, neg_add, torsion_neg, torsion_neg ((v' 2).val • _)]
    rw [show ∀ x y z : torsionPoints (curveP p) Qb 2, x + z + (y + z) = x + y + (z + z) by
      intro x y z; abel, torsion_add_self, add_zero]
  have hdd : (rv a b * rv a' b') ^ 2 = ((dv a b * dv a' b' : ℚ) : Qb) := by
    rw [mul_pow, rv_sq, rv_sq]; push_cast; ring
  have hrr : IsRatSqrt (rv a b * rv a' b') := ⟨_, by rw [hdd, eq_ratCast]⟩
  have hfin : (∀ σ : GQ, σ (rv a b * rv a' b') = rv a b * rv a' b') → v = v' := by
    intro hfix
    obtain ⟨k, hk⟩ := mem_range_of_fixed (K := ℚ) hfix
    have : IsSquare (dv a b * dv a' b') := ⟨k, (algebraMap ℚ Qb).injective (by
      rw [map_mul _ k k, hk, ← sq, hdd, eq_ratCast])⟩
    obtain ⟨e1, e2⟩ := eq_of_isSquare_dv this
    funext i; fin_cases i
    · exact e1
    · exact e2
    · exact h2
  rcases two_torsion_cases (m : (EC p (AlgebraicClosure ℚ)).Point) m.2 with hm0 | hmT | ⟨r, hr, er, hmr⟩
  · refine hfin fun σ => ?_
    have := hprod σ
    have hm' : m = 0 := Subtype.ext hm0
    rw [hm', map_zero, sub_zero] at this
    simp only [kapFun] at this
    by_contra hne; rw [if_neg hne] at this; exact Tm_ne_zero this
  · refine hfin fun σ => ?_
    have := hprod σ
    have hm' : m = Tm := Subtype.ext hmT
    rw [hm', rho_Tm, sub_self] at this
    simp only [kapFun] at this
    by_contra hne; rw [if_neg hne] at this; exact Tm_ne_zero this
  · exfalso
    have hrsq : IsRatSqrt r := ⟨-(p : ℚ), by rw [er, eq_ratCast]; push_cast; ring⟩
    have hkr : kapFun (p := p) (rv a b * rv a' b') = kapFun r := by
      funext σ
      rw [hprod σ]
      apply Subtype.ext
      rw [AddSubgroup.coe_sub, rho_coe, hmr, kapFun_root hr er]
    obtain ⟨k, hk⟩ := mul_mem_range_of_same_sign hrr hrsq (fixed_iff_of_kapFun_eq hkr)
    apply not_isSquare_neg_p_dv hp2 a b a' b'
    refine ⟨k, (algebraMap ℚ Qb).injective ?_⟩
    rw [map_mul _ k k, hk, ← sq, mul_pow, hdd, er, eq_ratCast]
    push_cast; ring

/-! ### Every Selmer class is a value of $\Phi$ -/

/-- The exponents of the class of $d_2$, in the coordinates of $\Phi$. -/
theorem dv_spec {s : ℚ} (hs : s = 1 ∨ s = -1) {e₂ eₚ : ℕ} (he₂ : e₂ < 2) (heₚ : eₚ < 2) :
    dv ((if s = -1 then 1 else 0) + (if eₚ = 1 then 1 else 0)) (if e₂ = 1 then 1 else 0) *
      (if eₚ = 1 then -(p : ℚ) else 1) = s * 2 ^ e₂ * (p : ℚ) ^ eₚ := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases hs with rfl | rfl <;> interval_cases e₂ <;> interval_cases eₚ <;> norm_num [dv, h11] <;> ring

theorem exists_Phi_eq (hp8 : p % 8 = 1) (c : H1 (M2 p)) (hc : c ∈ selmerGroup ℚ (curveP p) 2) :
    ∃ v, Phi (p := p) v = c := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp8
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hval : ∀ x y : ZMod 2, (x = 0 ↔ y = 0) → x = y := by decide
  obtain ⟨hcont, -, -⟩ := (mem_selmerGroup_iff ℚ (curveP p) 2 c).1 hc
  have hloc := (mem_selmerGroup_iff ℚ (curveP p) 2 c).1 hc
  obtain ⟨z, hz, rfl⟩ := (mem_H1cont_iff _ _).1 hcont
  obtain ⟨w, xp, hwc, hwK, hxp, hwψ⟩ := exists_kummer_T (p := p)
  have hxp' : xp ^ 2 = ((p : ℚ) : Qb) := by rw [hxp]; push_cast; rfl
  -- the `psi` part of `z` is the character of `√1` or `√p`
  obtain ⟨u₁, u₁0, ⟨d₁, hd₁⟩, hfix₁⟩ := exists_sqrt_psi z hz
  have hd₁' : u₁ ^ 2 = (d₁ : Qb) := by rw [hd₁, eq_ratCast]
  have hd₁0 : d₁ ≠ 0 := by
    rintro rfl; apply u₁0; rw [Rat.cast_zero] at hd₁'; exact pow_eq_zero_iff two_ne_zero |>.1 hd₁'
  have hsel : d₁ ∈ isogenySelmer p := mem_isogenySelmer_of_places hd₁0
    (fun v => psi_local _ z hd₁0 hd₁' hfix₁ (hloc.2.1 v)) (fun w => psi_local _ z hd₁0 hd₁' hfix₁ (hloc.2.2 w))
  rw [(prop_8_1_explicit p hp8).1] at hsel
  obtain ⟨-, hsq⟩ := hsel
  obtain ⟨e, z', hz', hzz', hψ'⟩ : ∃ (e : ZMod 2) (z' : cocycles₁ (M2 p)), z' ∈ contCocycles₁ (M2 p) ∧
      H1π (M2 p) z = H1π (M2 p) z' + e.val • sP p ∧
      ∀ σ, psi (((z' : _ → _) σ : torsionPoints (curveP p) Qb 2) : (EC p (AlgebraicClosure ℚ)).Point) = 0 := by
    rcases hsq with hsq | hsq
    · refine ⟨0, z, hz, by simp, fun σ => (hfix₁ σ).1 ?_⟩
      have h1 : (1 : Qb) ^ 2 = ((1 : ℚ) : Qb) := by simp
      have : kapFun (p := p) u₁ = kapFun 1 :=
        kapFun_eq_of_isSquare hd₁' h1 hd₁0 one_ne_zero (by rwa [mul_one])
      exact (fixed_iff_of_kapFun_eq this σ).2 (map_one σ)
    · refine ⟨1, z - w, sub_mem hz hwc, ?_, fun σ => ?_⟩
      · rw [map_sub, hwK]
        simp [sP, ZMod.val_one]
      · have hk : kapFun (p := p) u₁ = kapFun xp :=
          kapFun_eq_of_isSquare hd₁' hxp' hd₁0 hp0 (by rwa [mul_comm])
        have hiff := fixed_iff_of_kapFun_eq hk σ
        have h1 : psiHom ((z : _ → _) σ) = psiHom ((w : _ → _) σ) :=
          hval _ _ ((hfix₁ σ).symm.trans (hiff.trans (hwψ σ).symm))
        show psiHom (((z - w : cocycles₁ (M2 p)) : _ → _) σ) = 0
        show psiHom ((z : _ → _) σ - (w : _ → _) σ) = 0
        rw [map_sub, h1, sub_self]
  have hS' : H1π (M2 p) z' ∈ selmerGroup ℚ (curveP p) 2 := by
    have : H1π (M2 p) z' = H1π (M2 p) z - e.val • sP p := by rw [hzz']; abel
    rw [this]
    exact sub_mem hc (AddSubgroup.nsmul_mem _ sP_mem _)
  -- `z'` is `κ(u₂)`
  obtain ⟨u₂, hu₂, u₂0, rfl⟩ := exists_sqrt_kap z' hz' hψ'
  obtain ⟨d₂, hd₂⟩ := id hu₂
  have hd₂' : u₂ ^ 2 = (d₂ : Qb) := by rw [hd₂, eq_ratCast]
  have hd₂0 : d₂ ≠ 0 := by
    rintro rfl; apply u₂0; rw [Rat.cast_zero] at hd₂'; exact pow_eq_zero_iff two_ne_zero |>.1 hd₂'
  have hloc' := (mem_selmerGroup_iff ℚ (curveP p) 2 _).1 hS'
  have hsel₂ : d₂ ∈ isogenySelmer (-4 * p) := mem_isogenySelmer_of_places hd₂0
    (fun v => kap_local _ hu₂ hd₂0 hd₂' (hloc'.2.1 v)) (fun w => kap_local _ hu₂ hd₂0 hd₂' (hloc'.2.2 w))
  rw [(prop_8_1_explicit p hp8).2] at hsel₂
  obtain ⟨-, hev⟩ := hsel₂
  obtain ⟨s, e₂, eₚ, hs, he₂, heₚ, hsq₂⟩ := IsogenyDescent.exists_class (p := p) hp2 hd₂0 hev
  set a : ZMod 2 := (if s = -1 then 1 else 0) + (if eₚ = 1 then 1 else 0) with ha
  set b : ZMod 2 := if e₂ = 1 then 1 else 0 with hb
  -- the correction factor `√(-p)` or `1`
  set q : Qb := if eₚ = 1 then ri * xp else 1 with hq
  have hq2 : q ^ 2 = (((if eₚ = 1 then -(p : ℚ) else 1) : ℚ) : Qb) := by
    rw [hq]; split_ifs
    · rw [mul_pow, ri_sq, hxp']; push_cast; ring
    · simp
  have hq0' : (if eₚ = 1 then -(p : ℚ) else 1) ≠ 0 := by split_ifs <;> simp [hp0]
  have hqr : IsRatSqrt q := ⟨_, by rw [hq2, eq_ratCast]⟩
  have hq0 : q ≠ 0 := ne_zero_of_sq hq2 hq0'
  have hrv0 : rv a b ≠ 0 := ne_zero_of_sq (rv_sq a b) (dv_ne_zero a b)
  have ht2 : (rv a b * q) ^ 2 = ((dv a b * (if eₚ = 1 then -(p : ℚ) else 1) : ℚ) : Qb) := by
    rw [mul_pow, rv_sq, hq2]; push_cast; ring
  have hkap : kapFun (p := p) u₂ = kapFun (rv a b) + kapFun q := by
    rw [← kapFun_mul (rv_isRatSqrt a b) hqr hrv0 hq0]
    refine kapFun_eq_of_isSquare hd₂' ht2 hd₂0 (mul_ne_zero (dv_ne_zero a b) hq0') ?_
    rw [ha, hb, dv_spec hs he₂ heₚ]
    exact hsq₂
  have hq_cls : H1π (M2 p) (kap (p := p) hqr) = 0 := by
    by_cases he : eₚ = 1
    · have hq' : q ^ 2 = -(p : Qb) := by rw [hq2, if_pos he]; push_cast; ring
      exact H1π_kap_root hq' hqr
    · have : kap (p := p) hqr = 0 := by
        apply cocycles₁_ext; intro σ
        rw [kap_apply, hq, if_neg he]
        simp [kapFun]
        rfl
      rw [this, map_zero]
  have hcls : H1π (M2 p) (kap (p := p) hu₂) = H1π (M2 p) (kap (p := p) (rv_isRatSqrt a b)) := by
    have : kap (p := p) hu₂ = kap (p := p) (rv_isRatSqrt a b) + kap (p := p) hqr := by
      apply cocycles₁_ext; intro σ
      show kapFun u₂ σ = kapFun (rv a b) σ + kapFun q σ
      rw [hkap]; rfl
    rw [this, map_add, hq_cls, add_zero]
  refine ⟨![a, b, e], ?_⟩
  rw [hzz', hcls]
  rfl

/-! ### Proposition 8.1 -/

theorem H1_add_self (x : H1 (M2 p)) : x + x = 0 := by
  induction x using H1_induction_on with
  | h z =>
    rw [← map_add]
    have : z + z = 0 := by
      apply cocycles₁_ext; intro σ
      exact torsion_add_self _
    rw [this, map_zero]

end NumberFieldKB.MilneEC.Prop81

namespace NumberFieldKB.MilneEC

open Prop81

/-- **Proposition 8.1** (Milne, *Elliptic Curves*, Ch. IV, Proposition 8.1, pdf p. 151; Silverman 1986, X.6.2):
for a prime $p \equiv 1 \pmod 8$, the $2$-Selmer group of $E : Y^2 = X^3 + pX$ is $(\mathbb Z/2)^3$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 8.1, pdf p. 151"]
theorem prop_8_1 : Prop8_1 := by
  refine ⟨fun p hpr hp8 => ?_⟩
  have := Fact.mk hpr
  let S := selmerGroup ℚ (curveP p) 2
  let f : (Fin 3 → ZMod 2) → S := fun v => ⟨Phi v, Phi_mem hp8 v⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v v' h => Phi_injective hp8 (congrArg Subtype.val h), fun c => ?_⟩
    obtain ⟨v, hv⟩ := exists_Phi_eq hp8 c.1 c.2
    exact ⟨v, Subtype.ext hv⟩
  let e := Equiv.ofBijective f hf
  have : Finite S := Finite.of_equiv _ e
  refine addEquiv_fin_zmod_two_of_card (fun x => Subtype.ext (H1_add_self (p := p) x.1)) 3 ?_
  rw [← Nat.card_congr e]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- **Proposition 8.2** (Milne, *Elliptic Curves*, Ch. IV, Proposition 8.2, pdf p. 152), with no named input: for
a prime $p \equiv 1 \pmod 8$ such that $2$ is not a fourth power modulo $p$, $\operatorname{rank} E(\mathbb Q) = 0$
and $Ш(E/\mathbb Q)_2 \cong (\mathbb Z/2)^2$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 8.2, pdf p. 152"]
theorem prop_8_2 : Prop8_2 := prop_8_2_of_prop_8_1 prop_8_1

end NumberFieldKB.MilneEC
