import NumberFieldKB.MilneEC.LocalPoints

/-!
# Kummer approximation: reductions

`KummerApprox W Kv n` (`LocalPoints.lean`) says every point of $E(K_v)$ is $nS + T$ with $S \in E(K_v)$ and $T$
algebraic. This file proves:

* `KummerApprox.mul`, `kummerApprox_of_prime`: it is multiplicative in $n$, so prime $n$ suffice.
* `kummerApprox_of_coprime`: if $\operatorname{Gal}(\bar K_v/K_v)$ is finite of order $d$ prime to $n$, then
  $E(K_v) = nE(K_v)$ (the class of $\sigma \mapsto \sigma Q - Q$, $nQ = R$, in $H^1$ of a finite group is killed by
  both $d$ and $n$).
* `card_gal_completion_rat`: at the real place of $\mathbb Q$ the Galois group has order $2$. So at the real place
  only $n = 2$ is left.
-/

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine NumberField
open scoped Classical

namespace NumberFieldKB.MilneEC

section General

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (Kv : Type) [Field Kv] [Algebra K Kv]

theorem kummerApprox_one : KummerApprox W Kv 1 := fun R => ⟨R, 0, by simp⟩

/-- **Kummer approximation is multiplicative**: from $a$ and $b$ to $ab$. -/
theorem KummerApprox.mul {a b : ℕ} (ha : KummerApprox W Kv a) (hb : KummerApprox W Kv b) :
    KummerApprox W Kv (a * b) := by
  intro R
  obtain ⟨S, T, hR⟩ := ha R
  obtain ⟨S', T', hS⟩ := hb S
  refine ⟨S', a • T' + T, ?_⟩
  rw [hR, hS, map_add, map_nsmul, nsmul_add, mul_comm, mul_nsmul, add_assoc]

/-- **Prime $n$ suffice.** -/
theorem kummerApprox_of_prime (h : ∀ p : ℕ, p.Prime → KummerApprox W Kv p) (n : ℕ) (hn : 0 < n) :
    KummerApprox W Kv n := by
  induction n using induction_on_primes with
  | zero => exact absurd hn (lt_irrefl 0)
  | one => exact kummerApprox_one W Kv
  | prime_mul p a hp ih =>
    exact (h p hp).mul W Kv (ih (Nat.pos_of_mul_pos_left hn))

variable [CharZero Kv] [W.IsElliptic]

/-- **Coprime to the Galois group**: if $\operatorname{Gal}(\bar K_v/K_v)$ is finite of order prime to $n$, then
every point of $E(K_v)$ is divisible by $n$ in $E(K_v)$. -/
theorem kummerApprox_of_coprime [Finite (AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv)] (n : ℕ) (hn : 0 < n)
    (hcop : Nat.Coprime (Nat.card (AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv)) n) :
    KummerApprox W Kv n := by
  classical
  intro R
  letI : Fintype (AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv) := Fintype.ofFinite _
  let G := AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv
  let ρ := (localPointsRep Kv W).ρ
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨Q, hQ⟩ := Lemma2_1.surjective_baseChange W lemma2_1 (AlgebraicClosure Kv) n hn0 (inclPoints W Kv R)
  have hQ' : n • Q = inclPoints W Kv R := by simpa only [natCast_zsmul] using hQ
  let s : G → (localPointsRep Kv W) := fun σ => ρ σ Q - Q
  have hsn : ∀ σ, n • s σ = 0 := fun σ => by
    change n • (ρ σ Q - Q) = 0
    rw [nsmul_sub, ← map_nsmul, hQ']
    exact sub_eq_zero.2 (inclPoints_fixed W Kv σ R)
  let t := ∑ τ, s τ
  have hρt : ∀ σ, ρ σ t = t - Nat.card G • s σ := fun σ => by
    have hsum : ∑ τ : G, s (σ * τ) = t := Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun _ => rfl)
    have hterm : ∀ τ : G, ρ σ (s τ) = s (σ * τ) - s σ := fun τ => by
      change ρ σ (ρ τ Q - Q) = (ρ (σ * τ) Q - Q) - (ρ σ Q - Q)
      rw [map_sub, map_mul, Module.End.mul_apply]
      abel
    rw [map_sum]
    simp only [hterm, Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hus : ∀ σ, (u * (Nat.card G : ℤ)) • s σ = s σ := fun σ => by
    have h0 : (n : ℤ) • s σ = 0 := by rw [natCast_zsmul]; exact hsn σ
    calc (u * (Nat.card G : ℤ)) • s σ = (u * (Nat.card G : ℤ) + v * n) • s σ := by
          rw [add_smul, mul_smul v, h0, smul_zero, add_zero]
      _ = s σ := by rw [huv, one_smul]
  let Q' := Q + u • t
  have hfix : ∀ σ, ρ σ Q' = Q' := fun σ => by
    change ρ σ (Q + u • t) = Q + u • t
    rw [map_add, map_zsmul, hρt σ, smul_sub, ← natCast_zsmul, smul_smul, hus σ]
    change ρ σ Q + (u • t - (ρ σ Q - Q)) = _
    abel
  obtain ⟨S, hS⟩ := exists_inclPoints_of_forall_fixed W Kv Q' hfix
  have hnt : n • t = 0 := by
    change n • ∑ τ, s τ = 0
    rw [Finset.smul_sum]
    exact Finset.sum_eq_zero fun σ _ => hsn σ
  refine ⟨S, 0, ?_⟩
  rw [map_zero, add_zero, hS]
  change _ = n • (Q + u • t)
  rw [nsmul_add, smul_comm n u t, hnt, smul_zero, add_zero, hQ']

end General

/-! ## The real place of $\mathbb Q$ -/

section Real

attribute [-instance] DivisionRing.toRatAlgebra

/-- The completion of $\mathbb Q$ at its infinite place has characteristic zero. A local instance only: the library
declares the global instance `charZero_completion` for every number field (`MilneCFT/Ch8/Theorem612Uncond.lean`). -/
theorem charZero_completion_infinitePlace_rat (w : InfinitePlace ℚ) : CharZero w.Completion :=
  charZero_of_injective_algebraMap (algebraMap ℚ w.Completion).injective

attribute [local instance] charZero_completion_infinitePlace_rat

/-- At the real place of $\mathbb Q$, $[\bar K_v : K_v] = 2$. -/
theorem finrank_algebraicClosure_completion_rat (w : InfinitePlace ℚ) :
    Module.finrank w.Completion (AlgebraicClosure w.Completion) = 2 := by
  have hw : w.IsReal := Subsingleton.elim Rat.infinitePlace w ▸ Rat.isReal_infinitePlace
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  letI : Algebra w.Completion ℂ := ((algebraMap ℝ ℂ).comp e.toRingHom).toAlgebra
  have hfin : Module.finrank w.Completion ℂ = 2 := by
    rw [Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl ℂ) (by ext; rfl), Complex.finrank_real_complex]
  haveI : Module.Finite w.Completion ℂ := Module.finite_of_finrank_eq_succ hfin
  haveI : IsAlgClosure w.Completion ℂ := ⟨inferInstance, inferInstance⟩
  let f : AlgebraicClosure w.Completion ≃ₐ[w.Completion] ℂ := IsAlgClosure.equiv _ _ _
  exact f.toLinearEquiv.finrank_eq.trans hfin

/-- At the real place of $\mathbb Q$, $\operatorname{Gal}(\bar K_v/K_v)$ has order $2$. -/
theorem card_gal_completion_rat (w : InfinitePlace ℚ) :
    Nat.card (AlgebraicClosure w.Completion ≃ₐ[w.Completion] AlgebraicClosure w.Completion) = 2 := by
  have h := finrank_algebraicClosure_completion_rat w
  haveI : FiniteDimensional w.Completion (AlgebraicClosure w.Completion) := Module.finite_of_finrank_eq_succ h
  rw [IsGalois.card_aut_eq_finrank, h]

instance (w : InfinitePlace ℚ) :
    Finite (AlgebraicClosure w.Completion ≃ₐ[w.Completion] AlgebraicClosure w.Completion) := by
  have h := finrank_algebraicClosure_completion_rat w
  haveI : FiniteDimensional w.Completion (AlgebraicClosure w.Completion) := Module.finite_of_finrank_eq_succ h
  infer_instance

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The real place needs only $n = 2$**: `KummerApprox E Kv 2` at the real place gives `LocalPointsInjectiveAt`
(odd primes are prime to $|\operatorname{Gal}(\mathbb C/\mathbb R)| = 2$). -/
theorem localPointsInjectiveAt_real_of_kummerApprox_two (w : InfinitePlace ℚ)
    (h2 : KummerApprox E w.Completion 2) : LocalPointsInjectiveAt E w.Completion := by
  refine localPointsInjectiveAt_of_kummerApprox E w.Completion
    (kummerApprox_of_prime E w.Completion fun p hp => ?_)
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact h2
  · refine kummerApprox_of_coprime E w.Completion p hp.pos ?_
    rw [card_gal_completion_rat]
    exact (Nat.coprime_primes Nat.prime_two hp).2 (by rintro rfl; exact (Nat.not_even_iff_odd.2 hodd) even_two)

end Real

/-! ## Assembly -/

section Assembly

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] charZero_completion_infinitePlace_rat

/-- **Kummer approximation at the finite places for prime $\ell$** (named statement,
proved as `finiteKummerPrime` in `LocalPointsPadic.lean`): for an elliptic curve $E/\mathbb Q$, a prime $p$ and a prime $\ell$, every point of $E(\mathbb Q_p)$ is $\ell S + T$ with
$S \in E(\mathbb Q_p)$ and $T$ a point with coordinates algebraic over $\mathbb Q$. (True: $\ell E(\mathbb Q_p)$ is
open and the algebraic points are dense.) -/
structure FiniteKummerPrime : Prop where
  holds : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ),
    ℓ.Prime → KummerApprox E (v.adicCompletion ℚ) ℓ

/-- **`LocalPointsInjective` from Kummer approximation**: at the real place for $n = 2$ and at the finite places
for prime $n$. The real-place hypothesis is proved in `LocalPointsReal.lean`. -/
theorem localPointsInjective_of_kummer
    (hR : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (w : InfinitePlace ℚ), KummerApprox E w.Completion 2)
    (hF : FiniteKummerPrime) : LocalPointsInjective := by
  refine ⟨fun E _ => ⟨fun v => ?_, fun w => localPointsInjectiveAt_real_of_kummerApprox_two E w (hR E w)⟩⟩
  exact localPointsInjectiveAt_of_kummerApprox E _ (kummerApprox_of_prime E _ fun ℓ hℓ => hF.holds E v ℓ hℓ)

end Assembly

end NumberFieldKB.MilneEC
