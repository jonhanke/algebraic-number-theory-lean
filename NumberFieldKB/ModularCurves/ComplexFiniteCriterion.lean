import NumberFieldKB.ModularCurves.ComplexLocal
import NumberFieldKB.ModularCurves.ComplexCanonical

/-!
# $h \in L(W)$ at the finite places iff $h\,j'$ is holomorphic on $\mathbb H$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Proposition 3.3 and Corollary 3.4 (pdf p. 199), at the points
of $\mathbb H$. For $h \in \mathbb C(X_0(N))$ write $h_\tau = \sigma_{c_0}(h)$ for its germ at $\tau \in \mathbb H$.
If $j - j(\tau)$ has order $m$ at $\tau$, then $j'$ has order $m - 1$ there (`finVal_jDerivGerm`); at the place
$P'$ of $\sigma_c$, with scaling factor $s$ and $s\,e(P') = m$, $\operatorname{ord}_\tau \sigma_c(h) = s
\operatorname{ord}_{P'}(h)$, so $h_\tau j'$ is holomorphic iff $s \operatorname{ord}_{P'} h + m - 1 \ge 0$ iff
$\operatorname{ord}_{P'} h \ge 1 - e(P') = -W_{P'}$ (`finVal_mul_jDerivGerm_le_one_iff`). Every place over a finite
place of $\mathbb C(j)$ is such a $P'$, at a point $\gamma_c^{-1}\tau_0$ for the trivial coset
(`finVal_finEmbC_eq`). Hence (`forall_finite_iff`): $\operatorname{ord}_{P'} h \ge -W_{P'}$ at every place over a finite
place iff $h_\tau j'$ is holomorphic at every $\tau \in \mathbb H$.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped MatrixGroups WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-- The order of $j - j(\tau)$ at $\tau$: $3$ if $j(\tau) = 0$, $2$ if $j(\tau) = 1728$, $1$ otherwise. -/
def jOrder (t : ℂ) : ℕ := if t = 0 then 3 else if t = 1728 then 2 else 1

theorem jOrder_pos (t : ℂ) : 0 < jOrder t := by
  unfold jOrder; split_ifs <;> norm_num

theorem analyticOrderAt_jFun_sub_eq_jOrder (τ : ℍ) :
    analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun τ) (τ : ℂ) = jOrder (jFun τ) := by
  unfold jOrder
  split_ifs with h0 h1
  · exact_mod_cast analyticOrderAt_jFun_of_eq_zero τ h0
  · exact_mod_cast analyticOrderAt_jFun_of_eq_1728 τ h1
  · exact_mod_cast analyticOrderAt_jFun_sub_eq_one τ h0 h1

theorem analyticAt_deriv_jFun (τ : ℍ) : AnalyticAt ℂ (deriv (jFun ∘ ofComplex)) (τ : ℂ) :=
  (analyticAt_jFun τ).deriv

/-- The germ of $j'$ at $\tau$. -/
def jDerivGerm (τ : ℍ) : FinField τ :=
  MeroGerm.mk (deriv (jFun ∘ ofComplex)) (analyticAt_deriv_jFun τ).meromorphicAt

/-- **$j'$ has order $m - 1$ at $\tau$**, $m$ the order of $j - j(\tau)$. -/
theorem finVal_jDerivGerm (τ : ℍ) :
    finVal τ (jDerivGerm τ) = WithZero.exp (-((jOrder (jFun τ) : ℤ) - 1)) := by
  have h := (analyticAt_jFun τ).analyticOrderAt_deriv_add_one
  have hτ : (jFun ∘ ofComplex) (τ : ℂ) = jFun τ := by simp [ofComplex_apply]
  rw [hτ, analyticOrderAt_jFun_sub_eq_jOrder] at h
  have hm := jOrder_pos (jFun τ)
  have hd : analyticOrderAt (deriv (jFun ∘ ofComplex)) (τ : ℂ) = ((jOrder (jFun τ) - 1 : ℕ) : ℕ∞) := by
    generalize ha : analyticOrderAt (deriv (jFun ∘ ofComplex)) (τ : ℂ) = a at h
    induction a using ENat.recTopCoe with
    | top => simp at h
    | coe n =>
      have h' : n + 1 = jOrder (jFun τ) := by exact_mod_cast h
      congr 1
      omega
  rw [finVal, jDerivGerm, ordVal_mk_of_analyticAt (analyticAt_deriv_jFun τ) hd]
  congr 2
  push_cast [Nat.cast_sub hm]
  ring

variable (N : ℕ) [NeZero N]

/-- The place $j = j(\tau)$ of $\mathbb C(j)$ and the valuation hypothesis at $\tau$. -/
theorem finVal_algebraMapC_at (τ : ℍ) (x : RatFunc ℂ) :
    finVal τ (algebraMap (RatFunc ℂ) (FinField τ) x) =
      (Place.adicOfIrreducible (irreducible_X_sub_C (jFun τ))).valuation x ^ jOrder (jFun τ) :=
  finVal_algebraMapC τ (irreducible_X_sub_C (jFun τ)) (by simp) (analyticOrderAt_jFun_sub_eq_jOrder τ) x

/-- The place of $\mathbb C(X_0(N))$ of $\sigma_c$ at $\tau$. -/
def placeAt (τ : ℍ) (c : Cosets N) : Place ℂ (X0C N) :=
  placeOf (isFunctionField_X0C N) (finVal_algebraMapC_at τ) (finEmbC τ N c) (jOrder_pos (jFun τ))

theorem restrict_placeAt (τ : ℍ) (c : Cosets N) :
    (placeAt N τ c).restrict ℂ (RatFunc ℂ) = Place.adicOfIrreducible (irreducible_X_sub_C (jFun τ)) :=
  restrict_placeOf _ _ _ _

theorem restrict_placeAt_ne_infty (τ : ℍ) (c : Cosets N) :
    (placeAt N τ c).restrict ℂ (RatFunc ℂ) ≠ Place.infty ℂ := by
  rw [restrict_placeAt]
  exact Place.adicOfIrreducible_ne_infty _

/-- **The local criterion at a point of $\mathbb H$.** -/
theorem finVal_mul_jDerivGerm_le_one_iff (τ : ℍ) (c : Cosets N) {h : X0C N} (hh : h ≠ 0) :
    finVal τ (finEmbC τ N c h * jDerivGerm τ) ≤ 1 ↔
      1 - (Place.ramificationIdx (RatFunc ℂ) (placeAt N τ c) : ℤ) ≤ (placeAt N τ c).ord h := by
  have hv := valuation_apply_eq_exp (isFunctionField_X0C N) (finVal_algebraMapC_at τ) (finEmbC τ N c)
    (jOrder_pos (jFun τ)) hh
  have hs := scale_mul_ramificationIdx (isFunctionField_X0C N) (finVal_algebraMapC_at τ) (finEmbC τ N c)
    (jOrder_pos (jFun τ))
  have hpos := scale_pos (isFunctionField_X0C N) (finVal_algebraMapC_at τ) (finEmbC τ N c) (jOrder_pos (jFun τ))
  change finVal τ (finEmbC τ N c h) = _ at hv
  rw [map_mul, hv, finVal_jDerivGerm, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
  change _ ↔ 1 - (Place.ramificationIdx (RatFunc ℂ) (placeOf _ _ _ _) : ℤ) ≤ (placeOf _ _ _ _).ord h
  set s := scale (isFunctionField_X0C N) (finVal_algebraMapC_at τ) (finEmbC τ N c) (jOrder_pos (jFun τ))
  set e : ℤ := (Place.ramificationIdx (RatFunc ℂ)
    (placeOf (isFunctionField_X0C N) (finVal_algebraMapC_at τ) (finEmbC τ N c) (jOrder_pos (jFun τ))) : ℤ)
  set v := (placeOf (isFunctionField_X0C N) (finVal_algebraMapC_at τ) (finEmbC τ N c) (jOrder_pos (jFun τ))).ord h
  constructor
  · intro H
    by_contra hlt
    push_neg at hlt
    have : s * (v + e) ≤ 0 := by nlinarith
    nlinarith
  · intro H
    nlinarith

/-- Every place of $\mathbb C(X_0(N))$ over a finite place of $\mathbb C(j)$ is the place of some $\sigma_c$ at some
$\tau_0$. -/
theorem exists_placeAt (P' : Place ℂ (X0C N)) (hP : P'.restrict ℂ (RatFunc ℂ) ≠ Place.infty ℂ) :
    ∃ τ₀ c, placeAt N τ₀ c = P' := by
  obtain ⟨q, hq, hP'⟩ :=
    (Place.eq_infty_or_exists_eq_adicOfIrreducible (P'.restrict ℂ (RatFunc ℂ))).resolve_left hP
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root q (degree_pos_of_irreducible hq).ne'
  obtain ⟨τ₀, rfl⟩ := jFun_surjective t
  have hassoc : Associated (X - C (jFun τ₀)) q :=
    (irreducible_X_sub_C _).associated_of_dvd hq (dvd_iff_isRoot.2 ht)
  have hres : P'.restrict ℂ (RatFunc ℂ) = Place.adicOfIrreducible (irreducible_X_sub_C (jFun τ₀)) := by
    rw [hP', Place.adicOfIrreducible_eq_adicOfIrreducible_iff]
    exact hassoc.symm
  obtain ⟨c, hc⟩ := exists_placeOf_eq (isFunctionField_X0C N) (finVal_algebraMapC_at τ₀) (finEmbC τ₀ N)
    (finEmbC_injective τ₀ N) (card_cosets_eq_finrankC N) (jOrder_pos (jFun τ₀)) P' hres
  exact ⟨τ₀, c, hc⟩

/-- **The finite part of $L(W)$**: for $h \ne 0$, $\operatorname{ord}_{P'} h \ge -W_{P'}$ at every place over a finite
place of $\mathbb C(j)$ iff the germ of $h\,j'$ at every $\tau \in \mathbb H$ is holomorphic. -/
theorem forall_finite_iff {h : X0C N} (hh : h ≠ 0) :
    (∀ P' : Place ℂ (X0C N), P'.restrict ℂ (RatFunc ℂ) ≠ Place.infty ℂ →
      -(canonicalW N).coeff P' ≤ P'.ord h) ↔
    ∀ τ : ℍ, finVal τ (finEmbC τ N (cosetOne N) h * jDerivGerm τ) ≤ 1 := by
  constructor
  · intro H τ
    rw [finVal_mul_jDerivGerm_le_one_iff N τ (cosetOne N) hh]
    have := H (placeAt N τ (cosetOne N)) (restrict_placeAt_ne_infty N τ _)
    rw [coeff_canonicalW_of_ne_infty N _ (restrict_placeAt_ne_infty N τ _)] at this
    linarith
  · intro H P' hP
    obtain ⟨τ₀, c, rfl⟩ := exists_placeAt N P' hP
    rw [coeff_canonicalW_of_ne_infty N _ hP]
    have h1 := (finVal_mul_jDerivGerm_le_one_iff N τ₀ c hh).1
    suffices finVal τ₀ (finEmbC τ₀ N c h * jDerivGerm τ₀) ≤ 1 by linarith [h1 this]
    set τ₁ := (Quotient.out c)⁻¹ • τ₀
    have hj : jFun τ₁ = jFun τ₀ := jFun_smul _ _
    rw [map_mul, finVal_finEmbC_eq, finVal_jDerivGerm, ← hj, ← finVal_jDerivGerm, ← map_mul]
    exact H τ₁

end NumberFieldKB.ModularCurves
