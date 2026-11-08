import NumberFieldKB.ModularCurves.ComplexElliptic

/-!
# $j : X_0(N) \to X_0(1)$ over $\mathbb C$ is unramified away from $0, 1728, \infty$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196). The complex version of
`FiniteRamification.lean`: a finite place of $\mathbb C(j)$ is $j = t$ for some $t \in \mathbb C$, $t = j(\tau_0)$
($j$ is onto); if $t \ne 0, 1728$, $j - t$ has a simple zero at $\tau_0$, so the scaling factor $c$ and the
ramification index $e$ of every place over $j = t$ satisfy $c\,e = 1$.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable (N : ℕ) [NeZero N]

/-- **$j$ is unramified away from $0, 1728, \infty$** (on $\mathbb C(X_0(N))$). -/
theorem ramificationIdxC_eq_one_of_ne (P' : Place ℂ (X0C N)) (h0 : P'.restrict ℂ (RatFunc ℂ) ≠ placeJ0C)
    (h1728 : P'.restrict ℂ (RatFunc ℂ) ≠ placeJ1728C) (hinf : P'.restrict ℂ (RatFunc ℂ) ≠ Place.infty ℂ) :
    Place.ramificationIdx (RatFunc ℂ) P' = 1 := by
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible (P'.restrict ℂ (RatFunc ℂ)) with h | ⟨q, hq, hP⟩
  · exact absurd h hinf
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root q (degree_pos_of_irreducible hq).ne'
  obtain ⟨τ₀, rfl⟩ := jFun_surjective t
  have hroot : q.eval (jFun τ₀) = 0 := ht
  have hassoc : Associated (X - C (jFun τ₀)) q :=
    (irreducible_X_sub_C _).associated_of_dvd hq (dvd_iff_isRoot.2 hroot)
  have ht0 : jFun τ₀ ≠ 0 := by
    intro h
    apply h0
    rw [hP, placeJ0C, Place.adicOfIrreducible_eq_adicOfIrreducible_iff]
    rw [h, map_zero, sub_zero] at hassoc
    exact hassoc.symm
  have ht1728 : jFun τ₀ ≠ 1728 := by
    intro h
    apply h1728
    rw [hP, placeJ1728C, Place.adicOfIrreducible_eq_adicOfIrreducible_iff]
    rw [h] at hassoc
    exact hassoc.symm
  have hm := analyticOrderAt_jFun_sub_eq_one τ₀ ht0 ht1728
  have hvF : ∀ x : RatFunc ℂ, finVal τ₀ (algebraMap (RatFunc ℂ) (FinField τ₀) x) =
      (P'.restrict ℂ (RatFunc ℂ)).valuation x ^ (1 : ℕ) := by
    intro x
    rw [hP]
    exact finVal_algebraMapC τ₀ hq hroot (m := 1) (by exact_mod_cast hm) x
  obtain ⟨i, hi⟩ := exists_placeOf_eq (isFunctionField_X0C N) hvF (finEmbC τ₀ N) (finEmbC_injective τ₀ N)
    (card_cosets_eq_finrankC N) Nat.one_pos P' rfl
  have hs := scale_mul_ramificationIdx (isFunctionField_X0C N) hvF (finEmbC τ₀ N i) Nat.one_pos
  rw [hi] at hs
  have hpos := scale_pos (isFunctionField_X0C N) hvF (finEmbC τ₀ N i) Nat.one_pos
  have he := Place.ramificationIdx_pos (RatFunc ℂ) P'
  push_cast at hs
  have : (Place.ramificationIdx (RatFunc ℂ) P' : ℤ) = 1 := by
    have he' : (1 : ℤ) ≤ Place.ramificationIdx (RatFunc ℂ) P' := by exact_mod_cast he
    nlinarith
  exact_mod_cast this

open scoped Classical in
/-- The ramification of $j$ on $\mathbb C(X_0(N))$ lies over $0, 1728, \infty$. -/
theorem restrictC_mem_of_ramified (P' : Place ℂ (X0C N)) (h : 1 < Place.ramificationIdx (RatFunc ℂ) P') :
    P'.restrict ℂ (RatFunc ℂ) ∈ ({placeJ0C, placeJ1728C, Place.infty ℂ} : Finset (Place ℂ (RatFunc ℂ))) := by
  by_contra hmem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
  rw [ramificationIdxC_eq_one_of_ne N P' hmem.1 hmem.2.1 hmem.2.2] at h
  exact lt_irrefl _ h

end NumberFieldKB.ModularCurves
