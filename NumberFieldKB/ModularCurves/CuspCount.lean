import NumberFieldKB.ModularCurves.CuspDegree

/-!
# Counting the cusps of $X_0(N)$ over the cusp of $X(1)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196): the degree of $X_0(N) \to X(1)$ is the sum of
the widths of the cusps.

* `ord_unif_pos_of_comap_eq`, `residueDeg_pos_of_comap_eq` (general): ramification indices and residue degrees of
  places in a finite separable extension of function fields are positive.
* **`add_one_le_index`**: for $N > 1$, the cusps $\infty$ (width 1) and $0$ (width $N$) give
  $N + 1 \le (\Gamma_0(1) : \Gamma_0(N))$.
* **`placesAbove_cuspInf_eq`**: if $(\Gamma_0(1) : \Gamma_0(N)) = N + 1$ (the case $N = p$ prime), then $\infty$ and
  $0$ are the only places of $X_0(N)$ over the cusp of $X(1)$.
-/

open scoped WithZero

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC

section Positivity

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

attribute [local instance] PrimeDivisor.isDVR

/-- **Ramification indices are positive**: $e(Q/P) = \operatorname{ord}_Q(t_P) \ge 1$ for $Q$ over $P$. -/
theorem ord_unif_pos_of_comap_eq (Q : PrimeDivisor k L) (P : PrimeDivisor k K) (hQ : Q.comap (K := K) = P) :
    0 < Q.ord (algebraMap K L P.unif) := by
  let : Algebra P.O L := ((algebraMap K L).comp (algebraMap P.O K)).toAlgebra
  have : IsScalarTower P.O K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨v, rfl⟩ := (exists_placeOver_iff P Q).2 hQ
  rw [ord_placeOver_unif]
  have : v.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.O) := liesOver_maximalIdeal v
  have : Module.Finite P.O (integralClosure P.O L) := IsIntegralClosure.finite P.O K L _
  have : Algebra.IsIntegral P.O (integralClosure P.O L) := Algebra.IsIntegral.of_finite _ _
  exact_mod_cast Ideal.ramificationIdx_pos P.O v.asIdeal

/-- **Residue degrees are positive**: $f(Q/P) \ge 1$ for $Q$ over $P$. -/
theorem residueDeg_pos_of_comap_eq (Q : PrimeDivisor k L) (P : PrimeDivisor k K) (hQ : Q.comap (K := K) = P) :
    0 < Q.residueDeg (K := K) := by
  let : Algebra P.O L := ((algebraMap K L).comp (algebraMap P.O K)).toAlgebra
  have : IsScalarTower P.O K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨v, rfl⟩ := (exists_placeOver_iff P Q).2 hQ
  rw [residueDeg_placeOver]
  have : Module.Finite P.O (integralClosure P.O L) := IsIntegralClosure.finite P.O K L _
  exact Ideal.inertiaDeg_pos v.asIdeal P.O

end Positivity

/-! ### The place at infinity of $k(t)$ -/

section Infinity

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- **The place of $k(t)$ where $t$ has a pole is unique**, transported along a ring map $\varphi : k(t) \to L$ onto
`L` over `k` (Mathlib's Ostrowski theorem `RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X`). -/
theorem eq_of_not_mem_O (φ : RatFunc k →+* L) (hφ : Function.Surjective φ)
    (hc : ∀ c : k, φ (algebraMap k (RatFunc k) c) = algebraMap k L c) {P P' : PrimeDivisor k L}
    (hP : φ RatFunc.X ∉ P.O) (hP' : φ RatFunc.X ∉ P'.O) : P = P' := by
  classical
  have key : ∀ Q : PrimeDivisor k L, φ RatFunc.X ∉ Q.O →
      (Q.O.valuation.comap φ).IsEquiv (RatFunc.inftyValuation k) := by
    intro Q hQ
    have : (Q.O.valuation.comap φ).IsTrivialOn k := by
      refine ⟨fun a ha => ?_⟩
      have hunit : IsUnit (⟨algebraMap k L a, Q.algebraMap_mem a⟩ : Q.O) := by
        refine IsUnit.of_mul_eq_one (⟨algebraMap k L a⁻¹, Q.algebraMap_mem a⁻¹⟩ : Q.O) ?_
        apply Subtype.ext
        change algebraMap k L a * algebraMap k L a⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ ha, map_one]
      rw [Valuation.comap_apply, hc]
      exact (ValuationSubring.valuation_eq_one_iff _ _).mp hunit
    refine RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X ?_
    rw [Valuation.comap_apply]
    by_contra h
    exact hQ ((ValuationSubring.valuation_le_one_iff _ _).1 (not_lt.1 h))
  have he := (key P hP).trans (key P' hP').symm
  apply PrimeDivisor.ext_O
  ext y
  obtain ⟨f, rfl⟩ := hφ y
  rw [← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff]
  have := he f 1
  simpa only [Valuation.comap_apply, map_one] using this

end Infinity

/-! ### The cusps of $X_0(N)$ over the cusp of $X(1)$ -/

section X0

variable {N : ℕ} [NeZero N]

theorem Gamma0_one_eq_top' : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp only [Subgroup.mem_top, iff_true]
  rw [CongruenceSubgroup.Gamma0_mem]
  exact Subsingleton.elim _ _

/-- $\mathbb Q(X(1)) = \mathbb Q(j)$: the map $\mathbb Q(t) \to \mathbb Q(X_0(1))$, $t \mapsto j$, is onto. -/
theorem algebraMap_X0_one_surjective : Function.Surjective (algebraMap (RatFunc ℚ) (X0 1)) := by
  have h1 : Module.finrank (RatFunc ℚ) (X0 1) = 1 := by
    rw [finrank_X0, Gamma0_one_eq_top', Subgroup.index_top]
  intro y
  have := (Subalgebra.bot_eq_top_of_finrank_eq_one h1)
  have hy : y ∈ (⊥ : Subalgebra (RatFunc ℚ) (X0 1)) := this ▸ Algebra.mem_top
  obtain ⟨f, hf⟩ := Algebra.mem_bot.1 hy
  exact ⟨f, hf⟩

theorem not_mem_cuspInf_O_jX0 : jX0 (prop2_4' N) ∉ (cuspInf N).O := by
  intro h
  rw [mem_cuspInf_O, qExpX0_jX0, valuation_jSer, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

/-- **$X(1)$ has exactly one cusp**: every place of $\mathbb Q(X(1))$ where $j$ has a pole is the cusp $\infty$. -/
theorem eq_cuspInf_one {P : PrimeDivisor ℚ (X0 1)} (hP : IsCusp P) : P = cuspInf 1 := by
  refine eq_of_not_mem_O (algebraMap (RatFunc ℚ) (X0 1)) algebraMap_X0_one_surjective
    (fun c => by rw [← RingHom.comp_apply]; exact RingHom.congr_fun (RingHom.ext_rat _ _) c) ?_ ?_
  · rw [algebraMap_X_X0]; exact hP
  · rw [algebraMap_X_X0]
    exact not_mem_cuspInf_O_jX0

/-- A place of $X_0(N)$ is a cusp iff it lies over the cusp $\infty$ of $X(1)$. -/
theorem isCusp_iff_degeneracyPlace_eq (Q : PrimeDivisor ℚ (X0 N)) :
    IsCusp Q ↔ degeneracyPlace (one_mul_one_dvd N) Q = cuspInf 1 := by
  have e := isCusp_comap_forget_iff (N := 1) (M := N) (one_mul_one_dvd N) Q
  change IsCusp (degeneracyPlace (one_mul_one_dvd N) Q) ↔ IsCusp Q at e
  rw [← e]
  constructor
  · exact eq_cuspInf_one
  · intro h
    rw [h]
    exact not_mem_cuspInf_O_jX0

/-- The terms of the fundamental identity over the cusp of $X(1)$. -/
theorem ramIndex_mul_resDeg_pos {Q : PrimeDivisor ℚ (X0 N)} (hQ : Q ∈ placesAbove (one_mul_one_dvd N) (cuspInf 1)) :
    1 ≤ ramIndex (one_mul_one_dvd N) (cuspInf 1) Q * (resDegX0 (one_mul_one_dvd N) Q : ℤ) := by
  let := (degeneracy 1 N 1 (one_mul_one_dvd N)).toAlgebra
  have := isScalarTower_rat_degeneracy (one_mul_one_dvd N)
  have := isAlgebraic_degeneracy (one_mul_one_dvd N)
  have : FiniteDimensional (X0 1) (X0 N) := finiteDimensional_degeneracy (one_mul_one_dvd N)
  have hc : Q.comap (K := X0 1) = cuspInf 1 := (mem_placesAbove _ _ Q).1 hQ
  have h1 : 0 < ramIndex (one_mul_one_dvd N) (cuspInf 1) Q := ord_unif_pos_of_comap_eq Q _ hc
  have h2 : 0 < resDegX0 (one_mul_one_dvd N) Q := residueDeg_pos_of_comap_eq Q _ hc
  have : (1 : ℤ) ≤ resDegX0 (one_mul_one_dvd N) Q := by exact_mod_cast h2
  nlinarith

/-- The fundamental identity over the cusp of $X(1)$, in terms of `resDegX0`. -/
theorem sum_cusps_eq_index :
    ∑ Q ∈ placesAbove (one_mul_one_dvd N) (cuspInf 1),
      ramIndex (one_mul_one_dvd N) (cuspInf 1) Q * (resDegX0 (one_mul_one_dvd N) Q : ℤ) =
      (CongruenceSubgroup.Gamma0 N).index := by
  have h := sum_ramIndex_mul_residueDeg_forget (one_mul_one_dvd N) (cuspInf 1)
  rw [Gamma0_one_eq_top', Subgroup.relIndex_top_right] at h
  exact h

/-- **The cusps $\infty$ and $0$ bound the index**: for $N > 1$, $N + 1 \le (\Gamma_0(1) : \Gamma_0(N))$ (the widths
$1$ and $N$ of the cusps $\infty$ and $0$ in Milne's $\sum$ of the widths of the cusps $= (\Gamma_0(1):\Gamma_0(N))$). -/
@[kb "milne2006ec" "Ch. V, §2, the degree of X_0(N) → X(1) is the sum of the widths of the cusps, pdf p. 196"]
theorem add_one_le_index (hN : 1 < N) : N + 1 ≤ (CongruenceSubgroup.Gamma0 N).index := by
  classical
  have hsub : ({cuspInf N, cusp0 N} : Finset _) ⊆ placesAbove (one_mul_one_dvd N) (cuspInf 1) := by
    intro Q hQ
    rw [mem_placesAbove]
    rcases Finset.mem_insert.1 hQ with rfl | hQ
    · exact degeneracyPlace_cuspInf_one
    · rw [Finset.mem_singleton.1 hQ]; exact degeneracyPlace_cusp0
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun Q =>
    ramIndex (one_mul_one_dvd N) (cuspInf 1) Q * (resDegX0 (one_mul_one_dvd N) Q : ℤ))
    (fun Q hQ _ => le_trans zero_le_one (ramIndex_mul_resDeg_pos hQ))
  rw [sum_cusps_eq_index, Finset.sum_pair (cuspInf_ne_cusp0 hN), ramIndex_cuspInf, ramIndex_cusp0,
    resDegX0_cuspInf, resDegX0_cusp0] at hle
  push_cast at hle
  omega

/-- **If $(\Gamma_0(1) : \Gamma_0(N)) = N + 1$, the cusps of $X_0(N)$ are exactly $\infty$ and $0$** (both rational).
This is the case $N = p$ prime, where the index is $p + 1$ (Tau Ceti, `Gamma0_prime_index`; not importable here). -/
@[kb "milne2006ec" "Ch. V, §2, the cusps of X_0(p) (running text), pdf p. 196"]
theorem isCusp_iff_of_index_eq (hN : 1 < N) (hi : (CongruenceSubgroup.Gamma0 N).index = N + 1)
    (Q : PrimeDivisor ℚ (X0 N)) : IsCusp Q ↔ Q = cuspInf N ∨ Q = cusp0 N := by
  classical
  rw [isCusp_iff_degeneracyPlace_eq]
  constructor
  · intro hQ
    by_contra hne
    push Not at hne
    have hmem : Q ∈ placesAbove (one_mul_one_dvd N) (cuspInf 1) := (mem_placesAbove _ _ Q).2 hQ
    have hsub : ({Q, cuspInf N, cusp0 N} : Finset _) ⊆ placesAbove (one_mul_one_dvd N) (cuspInf 1) := by
      intro R hR
      rw [mem_placesAbove]
      rcases Finset.mem_insert.1 hR with rfl | hR
      · exact hQ
      rcases Finset.mem_insert.1 hR with rfl | hR
      · exact degeneracyPlace_cuspInf_one
      · rw [Finset.mem_singleton.1 hR]; exact degeneracyPlace_cusp0
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun Q =>
      ramIndex (one_mul_one_dvd N) (cuspInf 1) Q * (resDegX0 (one_mul_one_dvd N) Q : ℤ))
      (fun Q hQ _ => le_trans zero_le_one (ramIndex_mul_resDeg_pos hQ))
    rw [sum_cusps_eq_index, Finset.sum_insert (by simp [hne.1, hne.2]),
      Finset.sum_pair (cuspInf_ne_cusp0 hN), ramIndex_cuspInf, ramIndex_cusp0,
      resDegX0_cuspInf, resDegX0_cusp0, hi] at hle
    have := ramIndex_mul_resDeg_pos hmem
    push_cast at hle
    omega
  · rintro (rfl | rfl)
    · exact degeneracyPlace_cuspInf_one
    · exact degeneracyPlace_cusp0

end X0

end NumberFieldKB.ModularCurves
