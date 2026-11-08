import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch2Stickelberger

/-!
# Milne, *Algebraic Number Theory*, Chapter 3: factorization of primes in examples

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), pp. 63–66; bib key `milne2020ant`.

* **Remark 3.43** (`remark_3_43`): Kummer–Dedekind under a discriminant condition at $p$. Mathlib's Kummer–Dedekind
  theorem (`KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map` and its companions)
  is stated under the conductor condition $(\mathfrak f \cap \mathbb Z) + p\mathbb Z = \mathbb Z$, where
  $\mathfrak f$ is the conductor of $\mathbb Z[\alpha]$; `remark_3_43` shows that Milne's discriminant condition
  implies it. Formalized for $A = \mathbb Z$ (Milne: any Dedekind domain $A$).
* **Example 3.44** (`example_3_44_i`, `_ii_split`, `_ii_inert`, `_iii_split`, `_iii_inert`): splitting of primes in
  $\mathbb Q(\sqrt m)$.
* **Example 3.45** (`example_3_45`): for an odd prime $p$: $p \equiv 1 \bmod 4$ iff $(p)$ splits in $\mathbb Z[i]$
  iff $p = a^2 + b^2$.
* **Remark 3.50** (`remark_3_50_split`; named statement `GaloisDeterminedBySplitPrimes`): the split primes of
  $\mathbb Q(\sqrt m)$, and Galois number fields are determined by their sets of split primes (Milne's
  Theorem 8.38).
* **Proposition 3.53** (`prop_3_53_irreducible`, `prop_3_53`): Eisenstein polynomials are irreducible and give
  totally ramified primes, $\mathfrak pB = \mathfrak P^m$ with $\mathfrak P = (\mathfrak p, \alpha)$.

Splitting types of a prime number $p$ in a quadratic field $K$ (Milne, p. 63): $(p)$ *splits* if
$p\mathcal O_K = \mathfrak p_1\mathfrak p_2$ with $\mathfrak p_1 \ne \mathfrak p_2$ prime, *stays prime* if
$p\mathcal O_K$ is prime, *ramifies* if $p\mathcal O_K = \mathfrak p^2$.
-/

open NumberField Polynomial Module RingOfIntegers
open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT

private lemma quad_eval {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (b c : ℤ)
    (hmin : minpoly ℤ θ = X ^ 2 + C b * X + C c) :
    θ ^ 2 + (b : 𝓞 K) * θ + (c : 𝓞 K) = 0 := by
  have := minpoly.aeval ℤ θ
  rw [hmin] at this
  simpa using this

private lemma mem_monicFactorsMod_of_dvd {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (p : ℕ)
    [Fact p.Prime] {Q : ℤ[X]}
    (hirr : Irreducible (Q.map (Int.castRingHom (ZMod p)))) (hmon : (Q.map (Int.castRingHom (ZMod p))).Monic)
    (hdvd : Q.map (Int.castRingHom (ZMod p)) ∣ (minpoly ℤ θ).map (Int.castRingHom (ZMod p))) :
    Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p := by
  classical
  unfold monicFactorsMod
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic θ.isIntegral))]
  exact ⟨hirr, hmon, hdvd⟩

private lemma prime_of_factor {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (p : ℕ)
    [Fact p.Prime] (hp : ¬ p ∣ RingOfIntegers.exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    (Ideal.span {(p : 𝓞 K), aeval θ Q}).IsPrime := by
  rw [← NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hp hQ]
  exact ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm _).prop.1

private lemma quad_map_factor {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (p : ℕ) [Fact p.Prime]
    (b c : ℤ) (hmin : minpoly ℤ θ = X ^ 2 + C b * X + C c)
    (r1 r2 : ℤ) (h1 : (p : ℤ) ∣ b + r1 + r2) (h2 : (p : ℤ) ∣ c - r1 * r2) :
    (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) =
      ((X - C r1) * (X - C r2) : ℤ[X]).map (Int.castRingHom (ZMod p)) := by
  have hb' : ((b + r1 + r2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h1
  have hc' : ((c - r1 * r2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h2
  have : (X ^ 2 + C b * X + C c : ℤ[X]) = (X - C r1) * (X - C r2) +
      (C (b + r1 + r2) * X + C (c - r1 * r2)) := by
    simp only [C_add, C_sub, C_mul]; ring
  have e1 : (Int.castRingHom (ZMod p)) (b + r1 + r2) = 0 := hb'
  have e2 : (Int.castRingHom (ZMod p)) (c - r1 * r2) = 0 := hc'
  rw [hmin, this]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, e1, e2]
  simp

private lemma monic_map_X_sub_C (p : ℕ) [Fact p.Prime] (r : ℤ) :
    ((X - C r : ℤ[X]).map (Int.castRingHom (ZMod p))).Monic ∧
      Irreducible ((X - C r : ℤ[X]).map (Int.castRingHom (ZMod p))) := by
  have : (X - C r : ℤ[X]).map (Int.castRingHom (ZMod p)) = X - C (r : ZMod p) := by simp
  rw [this]
  exact ⟨monic_X_sub_C _, irreducible_X_sub_C _⟩

private lemma factor_dvd {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (p : ℕ) [Fact p.Prime]
    (b c : ℤ) (hmin : minpoly ℤ θ = X ^ 2 + C b * X + C c)
    (r1 r2 : ℤ) (h1 : (p : ℤ) ∣ b + r1 + r2) (h2 : (p : ℤ) ∣ c - r1 * r2) :
    (X - C r1 : ℤ[X]).map (Int.castRingHom (ZMod p)) ∣ (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) ∧
    (X - C r2 : ℤ[X]).map (Int.castRingHom (ZMod p)) ∣ (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) := by
  rw [quad_map_factor θ p b c hmin r1 r2 h1 h2, Polynomial.map_mul]
  exact ⟨dvd_mul_right _ _, dvd_mul_left _ _⟩

/-- Kummer--Dedekind, split case. -/
theorem kummer_split {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) (b c : ℤ) (hmin : minpoly ℤ θ = X ^ 2 + C b * X + C c)
    (r1 r2 : ℤ) (h1 : (p : ℤ) ∣ b + r1 + r2) (h2 : (p : ℤ) ∣ c - r1 * r2)
    (h3 : ¬ (p : ℤ) ∣ r1 - r2) :
    ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ Ideal.span {(p : 𝓞 K)} = P * Q := by
  obtain ⟨hd1, hd2⟩ := factor_dvd θ p b c hmin r1 r2 h1 h2
  have hQ1 : (X - C r1 : ℤ[X]).map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p :=
    mem_monicFactorsMod_of_dvd θ p (monic_map_X_sub_C p r1).2 (monic_map_X_sub_C p r1).1 hd1
  have hQ2 : (X - C r2 : ℤ[X]).map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p :=
    mem_monicFactorsMod_of_dvd θ p (monic_map_X_sub_C p r2).2 (monic_map_X_sub_C p r2).1 hd2
  have hPpr := prime_of_factor θ p hp hQ1
  have hQpr := prime_of_factor θ p hp hQ2
  have hPeq : aeval θ (X - C r1 : ℤ[X]) = θ - r1 := by simp
  have hQeq : aeval θ (X - C r2 : ℤ[X]) = θ - r2 := by simp
  rw [hPeq] at hPpr
  rw [hQeq] at hQpr
  have hev := quad_eval θ b c hmin
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  have hk1c : ((b : 𝓞 K) + r1 + r2) = (p : 𝓞 K) * k1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hk1
  have hk2c : ((c : 𝓞 K) - r1 * r2) = (p : 𝓞 K) * k2 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hk2
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd
    (Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)).irreducible).2 h3 |>.symm
  have huvc : (u : 𝓞 K) * ((r1 : 𝓞 K) - r2) + (v : 𝓞 K) * (p : 𝓞 K) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) huv
  refine ⟨Ideal.span {(p : 𝓞 K), θ - r1}, Ideal.span {(p : 𝓞 K), θ - r2}, hPpr, hQpr, ?_, ?_⟩
  · intro hPQ
    have hb : θ - r2 ∈ Ideal.span {(p : 𝓞 K), θ - r1} := by
      rw [hPQ]; exact Ideal.subset_span (by simp)
    have ha : θ - r1 ∈ Ideal.span {(p : 𝓞 K), θ - r1} := Ideal.subset_span (by simp)
    have hp0 : (p : 𝓞 K) ∈ Ideal.span {(p : 𝓞 K), θ - r1} := Ideal.subset_span (by simp)
    have h1' : ((r1 : 𝓞 K) - r2) ∈ Ideal.span {(p : 𝓞 K), θ - r1} := by
      have := Ideal.sub_mem _ hb ha
      convert this using 1; ring
    have : (1 : 𝓞 K) ∈ Ideal.span {(p : 𝓞 K), θ - r1} := by
      rw [← huvc]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1') (Ideal.mul_mem_left _ _ hp0)
    exact hPpr.ne_top ((Ideal.eq_top_iff_one _).2 this)
  · apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem]
      have hpP : (p : 𝓞 K) ∈ Ideal.span {(p : 𝓞 K), θ - r1} := Ideal.subset_span (by simp)
      have haP : θ - r1 ∈ Ideal.span {(p : 𝓞 K), θ - r1} := Ideal.subset_span (by simp)
      have hpQ : (p : 𝓞 K) ∈ Ideal.span {(p : 𝓞 K), θ - r2} := Ideal.subset_span (by simp)
      have hbQ : θ - r2 ∈ Ideal.span {(p : 𝓞 K), θ - r2} := Ideal.subset_span (by simp)
      have e1 := Ideal.mul_mem_mul hpP hpQ
      have e2 := Ideal.mul_mem_mul hpP hbQ
      have e3 := Ideal.mul_mem_mul haP hpQ
      have key : (p : 𝓞 K) = (-(u : 𝓞 K)) * ((θ - r1) * p - p * (θ - r2)) + (v : 𝓞 K) * (p * p) := by
        linear_combination (-(p : 𝓞 K)) * huvc
      have hm := Ideal.add_mem _ (Ideal.mul_mem_left _ (-(u : 𝓞 K)) (Ideal.sub_mem _ e3 e2))
        (Ideal.mul_mem_left _ (v : 𝓞 K) e1)
      rwa [← key] at hm
    · rw [Ideal.mul_le]
      intro x hx y hy
      rw [Ideal.mem_span_pair] at hx hy
      obtain ⟨c1, d1, rfl⟩ := hx
      obtain ⟨c2, d2, rfl⟩ := hy
      rw [Ideal.mem_span_singleton']
      refine ⟨c1 * c2 * p + c1 * d2 * (θ - r2) + d1 * c2 * (θ - r1) +
        d1 * d2 * (-(k1 : 𝓞 K) * θ - k2), ?_⟩
      linear_combination (-(d1 * d2)) * (hev - θ * hk1c - hk2c)

/-- Kummer--Dedekind, inert case. -/
theorem kummer_inert {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    (hirr : Irreducible ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))) :
    (Ideal.span {(p : 𝓞 K)}).IsPrime := by
  have hQ : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p :=
    mem_monicFactorsMod_of_dvd θ p hirr ((minpoly.monic θ.isIntegral).map _) dvd_rfl
  have := prime_of_factor θ p hp hQ
  rw [minpoly.aeval] at this
  simpa using this

/-- Kummer--Dedekind, ramified case. -/
theorem kummer_ramified {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) (b c : ℤ) (hmin : minpoly ℤ θ = X ^ 2 + C b * X + C c)
    (r u v : ℤ) (hu : b + 2 * r = p * u) (hv : r ^ 2 + b * r + c = p * v) (hvp : ¬ (p : ℤ) ∣ v) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} = P ^ 2 := by
  have h1 : (p : ℤ) ∣ b + r + r := ⟨u, by linarith⟩
  have h2 : (p : ℤ) ∣ c - r * r := ⟨v - r * u, by linear_combination hv - r * hu⟩
  obtain ⟨hd1, -⟩ := factor_dvd θ p b c hmin r r h1 h2
  have hQ1 : (X - C r : ℤ[X]).map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p :=
    mem_monicFactorsMod_of_dvd θ p (monic_map_X_sub_C p r).2 (monic_map_X_sub_C p r).1 hd1
  have hPpr := prime_of_factor θ p hp hQ1
  have hPeq : aeval θ (X - C r : ℤ[X]) = θ - r := by simp
  rw [hPeq] at hPpr
  have hev := quad_eval θ b c hmin
  have huc : (b : 𝓞 K) + 2 * r = p * u := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hu
  have hvc : (r : 𝓞 K) ^ 2 + b * r + c = p * v := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hv
  obtain ⟨x, y, hxy⟩ := (Irreducible.coprime_iff_not_dvd
    (Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)).irreducible).2 hvp |>.symm
  have hxyc : (x : 𝓞 K) * v + (y : 𝓞 K) * p = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hxy
  refine ⟨Ideal.span {(p : 𝓞 K), θ - r}, hPpr, ?_⟩
  rw [pow_two]
  apply le_antisymm
  · rw [Ideal.span_singleton_le_iff_mem]
    have hpP : (p : 𝓞 K) ∈ Ideal.span {(p : 𝓞 K), θ - r} := Ideal.subset_span (by simp)
    have haP : θ - r ∈ Ideal.span {(p : 𝓞 K), θ - r} := Ideal.subset_span (by simp)
    have e1 := Ideal.mul_mem_mul hpP hpP
    have e2 := Ideal.mul_mem_mul hpP haP
    have e3 := Ideal.mul_mem_mul haP haP
    have key : (p : 𝓞 K) = (x : 𝓞 K) * (-((θ - r) * (θ - r)) - u * ((p : 𝓞 K) * (θ - r))) +
        (y : 𝓞 K) * (p * p) := by
      linear_combination (-(p : 𝓞 K)) * hxyc + (x : 𝓞 K) * (hev - θ * huc + r * huc - hvc)
    have hm := Ideal.add_mem _ (Ideal.mul_mem_left _ (x : 𝓞 K)
      (Ideal.sub_mem _ ((Ideal.neg_mem_iff _).2 e3) (Ideal.mul_mem_left _ (u : 𝓞 K) e2)))
      (Ideal.mul_mem_left _ (y : 𝓞 K) e1)
    rwa [← key] at hm
  · rw [Ideal.mul_le]
    intro s hs t ht
    rw [Ideal.mem_span_pair] at hs ht
    obtain ⟨c1, d1, rfl⟩ := hs
    obtain ⟨c2, d2, rfl⟩ := ht
    rw [Ideal.mem_span_singleton']
    refine ⟨c1 * c2 * p + c1 * d2 * (θ - r) + d1 * c2 * (θ - r) +
      d1 * d2 * (-(u : 𝓞 K) * (θ - r) - v), ?_⟩
    linear_combination (-(d1 * d2)) * (hev - θ * huc + r * huc - hvc)

/-! ### Index and discriminant of a quadratic element -/

private lemma split_discr_eq_det_sq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {m : ℕ}
    (b : Basis (Fin m) A B) (γ : Fin m → B) :
    Algebra.discr A γ = (b.toMatrix γ).det ^ 2 * Algebra.discr A b := by
  rw [← Algebra.discr_of_matrix_vecMul b (b.toMatrix γ), Basis.toMatrix_map_vecMul]

private lemma split_index_formula {B : Type*} [CommRing B] {m : ℕ} (b : Basis (Fin m) ℤ B)
    (γ : Fin m → B) (hne : Algebra.discr ℤ γ ≠ 0) :
    Algebra.discr ℤ γ = ((Submodule.span ℤ (Set.range γ)).toAddSubgroup.index : ℤ) ^ 2 *
          Algebra.discr ℤ b := by
  have hD := split_discr_eq_det_sq b γ
  have hli : LinearIndependent ℤ γ := by
    by_contra hn
    exact hne (Algebra.discr_zero_of_not_linearIndependent ℤ hn)
  let N := Submodule.span ℤ (Set.range γ)
  let bN : Basis (Fin m) ℤ N.toAddSubgroup := Basis.span hli
  have hidx := AddSubgroup.index_eq_natAbs_det b N.toAddSubgroup bN
  have hbN : ∀ i, (bN i : B) = γ i := fun i => congrArg Subtype.val (Basis.span_apply hli i)
  have hdet : (b.det fun i => (bN i : B)) = (b.toMatrix γ).det := by
    rw [show (fun i => (bN i : B)) = γ from funext hbN, Basis.det_apply]
  rw [hidx, hdet, hD]
  simp [sq_abs]

private lemma split_discr_cast (K : Type*) [Field K] [NumberField K] {n : ℕ} (γ : Fin n → 𝓞 K) :
    ((Algebra.discr ℤ γ : ℤ) : ℚ) = Algebra.discr ℚ (fun i => (γ i : K)) := by
  rw [Algebra.discr_def, Algebra.discr_def]
  rw [← eq_intCast (algebraMap ℤ ℚ), RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply]
  rw [← map_mul]
  exact (Algebra.trace_localization ℤ ℤ⁰ (Rₘ := ℚ) (Sₘ := K) (γ i * γ j)).symm

/-- If the discriminant of `1, α, …, α^{n-1}` is a nonzero integer `d`, then `d = ι² disc K` with `ι` in the
conductor of `ℤ[α]` (pulled back to `ℤ`). -/
private lemma split_exists_index (K : Type*) [Field K] [NumberField K] (α : 𝓞 K) (d : ℤ)
    (hd : Algebra.discr ℚ (fun i : Fin (Module.finrank ℚ K) => (α : K) ^ (i : ℕ)) = d) (hd0 : d ≠ 0) :
    ∃ ι : ℤ, d = ι ^ 2 * discr K ∧ ι ∈ (conductor ℤ α).comap (algebraMap ℤ (𝓞 K)) := by
  set n := Module.finrank ℚ K with hn
  let γ : Fin n → 𝓞 K := fun i => α ^ (i : ℕ)
  have hγ : Algebra.discr ℚ (fun i => (γ i : K)) = d := by
    rw [← hd]; simp [γ]
  have hcast : Algebra.discr ℤ γ = d := by
    have := split_discr_cast K γ
    rw [hγ] at this
    exact_mod_cast this
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = n := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hn, RingOfIntegers.rank]
  let b : Basis (Fin n) ℤ (𝓞 K) :=
    (RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq hcard)
  have hb : Algebra.discr ℤ b = discr K := discr_eq_discr K b
  have hne : Algebra.discr ℤ γ ≠ 0 := by rw [hcast]; exact hd0
  have hform := split_index_formula b γ hne
  set N := Submodule.span ℤ (Set.range γ) with hN
  set ι := N.toAddSubgroup.index with hι
  refine ⟨ι, by rw [← hcast, hform, hb], ?_⟩
  have hNle : ∀ x ∈ N, x ∈ Algebra.adjoin ℤ {α} := by
    intro x hx
    refine (Submodule.span_le (p := (Algebra.adjoin ℤ {α}).toSubmodule)).2 ?_ hx
    rintro _ ⟨i, rfl⟩
    exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ α) _
  rw [Ideal.mem_comap]
  intro x
  have : ι • x ∈ N.toAddSubgroup := N.toAddSubgroup.nsmul_index_mem x
  have h2 := hNle _ this
  simpa [nsmul_eq_mul] using h2

private lemma sup_top_of_mem (I : Ideal ℤ) (p : ℕ) [Fact p.Prime] (ι : ℤ) (hι : ι ∈ I)
    (hpι : ¬ (p : ℤ) ∣ ι) : I ⊔ Ideal.span {(p : ℤ)} = ⊤ := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hcop : IsCoprime ι (p : ℤ) := by
    apply IsCoprime.symm
    exact (Irreducible.coprime_iff_not_dvd hp'.irreducible).2 hpι
  obtain ⟨u, v, huv⟩ := hcop
  rw [Ideal.eq_top_iff_one]
  rw [← huv]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hι))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

private lemma not_dvd_exponent_of_index {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (p : ℕ)
    [Fact p.Prime] (ι : ℤ) (hι : ι ∈ (conductor ℤ θ).comap (algebraMap ℤ (𝓞 K)))
    (hpι : ¬ (p : ℤ) ∣ ι) : ¬ p ∣ RingOfIntegers.exponent θ :=
  RingOfIntegers.not_dvd_exponent_iff.2 (codisjoint_iff.2 (sup_top_of_mem _ p ι hι hpι))

/-- **Remark 3.43**, for $A = \mathbb Z$. Let $K = \mathbb Q(\alpha)$ with $\alpha \in \mathcal O_K$, $n = [K:\mathbb Q]$,
and $p$ a prime number such that $D(1, \alpha, \dots, \alpha^{n-1}) = a \cdot \mathrm{disc}(\mathcal O_K/\mathbb Z)$
with $p \nmid a$. Then the conductor of $\mathbb Z[\alpha]$ in $\mathcal O_K$ meets $\mathbb Z$ in an ideal prime to
$p$, so the conclusion of Theorem 3.41 (Kummer–Dedekind, in Mathlib under exactly this condition) holds at $p$. -/
@[kb "milne2020ant" "v3.08, Remark 3.43, p. 63"]
theorem remark_3_43 (K : Type*) [Field K] [NumberField K] (α : 𝓞 K) (hα : IntermediateField.adjoin ℚ {(α : K)} = ⊤)
    (p : ℕ) [Fact p.Prime] (a : ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (hD : Algebra.discr ℚ (fun i : Fin (Module.finrank ℚ K) => (α : K) ^ (i : ℕ)) = a * discr K) :
    (conductor ℤ α).comap (algebraMap ℤ (𝓞 K)) ⊔ Ideal.span {(p : ℤ)} = ⊤ := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha (dvd_zero _)
  obtain ⟨ι, hι, hmem⟩ := split_exists_index K α (a * discr K) (by rw [hD]; push_cast; ring)
    (mul_ne_zero ha0 (discr_ne_zero K))
  have hι2 : ι ^ 2 = a := (mul_right_cancel₀ (discr_ne_zero K) hι).symm
  have hpι : ¬ (p : ℤ) ∣ ι := by
    intro h
    exact ha (hι2 ▸ Dvd.dvd.pow h two_ne_zero)
  exact sup_top_of_mem _ p ι hmem hpι

/-! ### Quadratic helper lemmas -/

private lemma rat_int_of_isIntegral' (q : ℚ) (h : IsIntegral ℤ q) : ∃ z : ℤ, (z : ℚ) = q := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨z, by simpa using hz⟩

private lemma no_rat_sqrt' (m : ℤ) (hm : Squarefree m) (hm1 : m ≠ 1) :
    ¬ ∃ q : ℚ, q ^ 2 = (m : ℚ) := by
  rintro ⟨q, hq⟩
  have hi : IsIntegral ℤ q := by
    refine ⟨X ^ 2 - C (R := ℤ) m, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    simp only [eq_intCast, algebraMap_int_eq]
    linear_combination hq
  obtain ⟨z, rfl⟩ := rat_int_of_isIntegral' q hi
  have h2 : z * z = m := by exact_mod_cast (by rw [← hq]; ring : (z : ℚ) * z = m)
  have hu : IsUnit z := hm z ⟨1, by rw [mul_one]; exact h2.symm⟩
  rcases Int.isUnit_iff.1 hu with rfl | rfl <;> simp_all

/-- The discriminant of `1, θ` for a quadratic element `θ` with no rational root. -/
private lemma quad_discr (K : Type*) [Field K] [NumberField K] (n : ℕ) (hn : n = 2)
    (hK : Module.finrank ℚ K = n) (θ : K) (b c : ℤ) (h : θ ^ 2 + b * θ + c = 0)
    (hno : ∀ q : ℚ, q ^ 2 + b * q + c ≠ 0) :
    Algebra.discr ℚ (fun i : Fin n => θ ^ (i : ℕ)) = ((b ^ 2 - 4 * c : ℤ) : ℚ) := by
  subst hn
  have hli : LinearIndependent ℚ ![(1 : K), θ] := by
    rw [LinearIndependent.pair_iff]
    intro x y hxy
    by_cases hy : y = 0
    · subst hy
      simp at hxy
      exact ⟨hxy, rfl⟩
    · exfalso
      have hθ : θ = algebraMap ℚ K (-x / y) := by
        simp only [Algebra.smul_def, mul_one] at hxy
        have hy' : (algebraMap ℚ K y) ≠ 0 := by simpa using hy
        rw [map_div₀, map_neg]
        field_simp
        linear_combination hxy
      apply hno (-x / y)
      apply (algebraMap ℚ K).injective
      rw [map_zero, map_add, map_add, map_pow, map_mul, ← hθ]
      simpa using h
  let bs : Basis (Fin 2) ℚ K := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  have hbs : ∀ i, bs i = ![(1 : K), θ] i := by
    intro i; simp [bs]
  have htr : Algebra.trace ℚ K θ = -(b : ℚ) := by
    rw [Algebra.trace_eq_matrix_trace bs, Matrix.trace, Fin.sum_univ_two]
    simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
    have e0 : θ * bs 0 = bs 1 := by rw [hbs, hbs]; simp
    have e1 : θ * bs 1 = (-(c : ℚ)) • bs 0 + (-(b : ℚ)) • bs 1 := by
      rw [hbs, hbs]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, map_neg]
      simp
      linear_combination h
    rw [e0, e1]
    simp [Basis.repr_self]
  have htr1 : Algebra.trace ℚ K 1 = 2 := by
    simpa [hK] using Algebra.trace_algebraMap (S := K) (1 : ℚ)
  have htr2 : Algebra.trace ℚ K (θ * θ) = (b : ℚ) ^ 2 - 2 * c := by
    have : θ * θ = -(b : ℚ) • θ + (-(c : ℚ)) • (1 : K) := by
      simp only [Algebra.smul_def, eq_ratCast]
      simp
      linear_combination h
    rw [this, map_add, map_smul, map_smul, htr, htr1]
    simp
    ring
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Fin.isValue]
  simp [htr, htr1, htr2]
  ring

private lemma isIntegral_of_quad {K : Type*} [Field K] (x : K) (b c : ℤ) (h : x ^ 2 + b * x + c = 0) :
    IsIntegral ℤ x := by
  refine ⟨X ^ 2 + C b * X + C c, by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
  simp only [eq_intCast, algebraMap_int_eq]
  exact_mod_cast h

private lemma quad_minpoly {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (b c : ℤ)
    (h : θ ^ 2 + (b : 𝓞 K) * θ + c = 0) (hno : ∀ q : ℚ, q ^ 2 + b * q + c ≠ 0) :
    minpoly ℤ θ = X ^ 2 + C b * X + C c := by
  have hmon : (X ^ 2 + C b * X + C c : ℤ[X]).Monic := by monicity!
  have hirr : Irreducible (X ^ 2 + C b * X + C c : ℤ[X]) := by
    rw [hmon.irreducible_iff_irreducible_map_fraction_map (K := ℚ)]
    have hm : (X ^ 2 + C b * X + C c : ℤ[X]).map (algebraMap ℤ ℚ) =
        X ^ 2 + C (b : ℚ) * X + C (c : ℚ) := by simp
    rw [hm]
    apply irreducible_of_degree_le_three_of_not_isRoot
    · have : (X ^ 2 + C (b : ℚ) * X + C (c : ℚ)).natDegree = 2 := by compute_degree!
      rw [this]; simp
    · intro x hx
      apply hno x
      simpa [IsRoot] using hx
  have hd := minpoly.isIntegrallyClosed_dvd θ.isIntegral
    (p := (X ^ 2 + C b * X + C c : ℤ[X])) (by simpa using h)
  exact eq_of_monic_of_associated (minpoly.monic θ.isIntegral) hmon
    ((minpoly.irreducible θ.isIntegral).associated_of_dvd hirr hd)

private lemma quad_pkg {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (θ : 𝓞 K)
    (b c : ℤ) (h : θ ^ 2 + (b : 𝓞 K) * θ + c = 0) (hno : ∀ q : ℚ, q ^ 2 + b * q + c ≠ 0) :
    minpoly ℤ θ = X ^ 2 + C b * X + C c ∧
      ∃ ι : ℤ, b ^ 2 - 4 * c = ι ^ 2 * discr K ∧ ι ∈ (conductor ℤ θ).comap (algebraMap ℤ (𝓞 K)) := by
  refine ⟨quad_minpoly θ b c h hno, ?_⟩
  have hK' : (θ : K) ^ 2 + b * (θ : K) + c = 0 := by
    have := congrArg (algebraMap (𝓞 K) K) h
    simpa using this
  have hd := quad_discr K (Module.finrank ℚ K) hK rfl (θ : K) b c hK' hno
  refine split_exists_index K θ (b ^ 2 - 4 * c) hd ?_
  intro h0
  apply hno (-(b : ℚ) / 2)
  have h0' : ((b : ℚ)) ^ 2 - 4 * c = 0 := by exact_mod_cast h0
  linear_combination (-1 / 4 : ℚ) * h0'

private lemma sdata (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (m : ℤ)
    (hm : Squarefree m) (hm1 : m ≠ 1) (s : K) (hs : s ^ 2 = m) :
    ∃ S : 𝓞 K, (S : K) = s ∧ minpoly ℤ S = X ^ 2 + C (0 : ℤ) * X + C (-m) ∧
      ∃ ι : ℤ, 4 * m = ι ^ 2 * discr K ∧ ι ∈ (conductor ℤ S).comap (algebraMap ℤ (𝓞 K)) := by
  have hK0 : s ^ 2 + ((0 : ℤ) : K) * s + ((-m : ℤ) : K) = 0 := by
    push_cast; rw [hs]; ring
  have hint : IsIntegral ℤ s := isIntegral_of_quad s 0 (-m) hK0
  obtain ⟨S, hS⟩ : ∃ S : 𝓞 K, algebraMap (𝓞 K) K S = s := ⟨⟨s, hint⟩, rfl⟩
  have h : S ^ 2 + ((0 : ℤ) : 𝓞 K) * S + ((-m : ℤ) : 𝓞 K) = 0 := by
    apply IsFractionRing.injective (𝓞 K) K
    simpa [hS] using hK0
  have hno : ∀ q : ℚ, q ^ 2 + ((0 : ℤ) : ℚ) * q + ((-m : ℤ) : ℚ) ≠ 0 := by
    intro q hq
    apply no_rat_sqrt' m hm hm1
    refine ⟨q, ?_⟩
    push_cast at hq
    linarith
  obtain ⟨hmin, ι, hι, hmem⟩ := quad_pkg hK S 0 (-m) h hno
  exact ⟨S, hS, hmin, ι, by rw [← hι]; ring, hmem⟩

private lemma wdata (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (m : ℤ)
    (hm : Squarefree m) (hm1 : m ≠ 1) (s : K) (hs : s ^ 2 = m) (hm4 : m % 4 = 1) :
    ∃ W : 𝓞 K, (W : K) = (1 + s) / 2 ∧
      minpoly ℤ W = X ^ 2 + C (-1 : ℤ) * X + C (-(m / 4)) ∧
      ∃ ι : ℤ, m = ι ^ 2 * discr K ∧ ι ∈ (conductor ℤ W).comap (algebraMap ℤ (𝓞 K)) := by
  obtain ⟨k, hk⟩ : ∃ k, m = 4 * k + 1 := ⟨m / 4, by omega⟩
  have hk' : m / 4 = k := by omega
  rw [hk']
  have hs' : s ^ 2 = 4 * k + 1 := by rw [hs, hk]; push_cast; ring
  have hK0 : ((1 + s) / 2) ^ 2 + ((-1 : ℤ) : K) * ((1 + s) / 2) + ((-k : ℤ) : K) = 0 := by
    push_cast
    field_simp
    linear_combination hs'
  have hint : IsIntegral ℤ ((1 + s) / 2) := isIntegral_of_quad _ (-1) (-k) hK0
  obtain ⟨W, hW⟩ : ∃ W : 𝓞 K, algebraMap (𝓞 K) K W = (1 + s) / 2 := ⟨⟨(1 + s) / 2, hint⟩, rfl⟩
  have h : W ^ 2 + ((-1 : ℤ) : 𝓞 K) * W + ((-k : ℤ) : 𝓞 K) = 0 := by
    apply IsFractionRing.injective (𝓞 K) K
    simpa [hW] using hK0
  have hno : ∀ q : ℚ, q ^ 2 + ((-1 : ℤ) : ℚ) * q + ((-k : ℤ) : ℚ) ≠ 0 := by
    intro q hq
    apply no_rat_sqrt' m hm hm1
    refine ⟨2 * q - 1, ?_⟩
    push_cast at hq
    rw [hk]; push_cast
    linear_combination 4 * hq
  obtain ⟨hmin, ι, hι, hmem⟩ := quad_pkg hK W (-1) (-k) h hno
  exact ⟨W, hW, hmin, ι, by rw [hk]; linear_combination hι, hmem⟩

/-! ### Integer lemmas -/

private lemma prime_sq_not_dvd (m : ℤ) (hm : Squarefree m) (p : ℕ) [Fact p.Prime] :
    ¬ ((p : ℤ) * p ∣ m) := by
  intro h
  have h1 := (Fact.out : p.Prime).two_le
  rcases Int.isUnit_iff.1 (hm _ h) with h | h <;> omega

private lemma odd_prime_ndvd_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro h
  have : p ∣ 2 := by exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) this
  have := (Fact.out : p.Prime).two_le
  omega

private lemma odd_prime_not_dvd_index (m : ℤ) (hm : Squarefree m) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ι D : ℤ) (h : 4 * m = ι ^ 2 * D) : ¬ (p : ℤ) ∣ ι := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  rintro ⟨t, rfl⟩
  have hd : (p : ℤ) * p ∣ 4 * m := ⟨t ^ 2 * D, by rw [h]; ring⟩
  have h2 : IsCoprime (p : ℤ) 2 := (Irreducible.coprime_iff_not_dvd hp'.irreducible).2
    (odd_prime_ndvd_two p hp2)
  have h3 : IsCoprime ((p : ℤ) * p) (2 * 2) := (h2.mul_left h2).mul_right (h2.mul_left h2)
  have h4 : IsCoprime ((p : ℤ) * p) 4 := by simpa using h3
  exact prime_sq_not_dvd m hm p (h4.dvd_of_dvd_mul_left (by rwa [mul_comm] at hd))

private lemma no_prime_eq_mul {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P Q I : Ideal R) (hI : I.IsPrime) (hI0 : I ≠ ⊥) (hP : P.IsPrime) (hQ : Q.IsPrime)
    (h : I = P * Q) : False := by
  have key : ∀ P Q : Ideal R, Q.IsPrime → P * Q = I → P ≤ I → False := by
    intro P Q hQ h h'
    have h1 : P ≤ P * Q := h ▸ h'
    have h2 : P * Q ≤ P := Ideal.mul_le_left
    have hP0 : P ≠ ⊥ := by
      rintro rfl
      rw [Ideal.bot_mul] at h
      exact hI0 h.symm
    have : P * Q = P * ⊤ := by rw [Ideal.mul_top]; exact le_antisymm h2 h1
    exact hQ.ne_top (mul_left_cancel₀ hP0 this)
  rcases (Ideal.IsPrime.mul_le hI).1 h.ge with h' | h'
  · exact key P Q hQ h.symm h'
  · exact key Q P hP (by rw [mul_comm]; exact h.symm) h'

/-! ### Quadratic fields: splitting types -/

private lemma odd_split_of_leg {K : Type*} [Field K] [NumberField K] (m : ℤ) (S : 𝓞 K) (p : ℕ)
    [Fact p.Prime] (hp2 : p ≠ 2) (hpm : ¬ (p : ℤ) ∣ m) (hex : ¬ p ∣ RingOfIntegers.exponent S)
    (hmin : minpoly ℤ S = X ^ 2 + C (0 : ℤ) * X + C (-m)) (hleg : legendreSym p m = 1) :
    ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ Ideal.span {(p : 𝓞 K)} = P * Q := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hm0 : (m : ZMod p) ≠ 0 := fun h => hpm ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
  obtain ⟨y, hy⟩ := (legendreSym.eq_one_iff p hm0).1 hleg
  set r : ℤ := (y.val : ℤ) with hr
  have hrc : (r : ZMod p) = y := by simp [hr]
  have hdiv : (p : ℤ) ∣ r ^ 2 - m := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hrc, hy]; ring
  have h2 := odd_prime_ndvd_two p hp2
  apply kummer_split S p hex 0 (-m) hmin r (-r)
  · simp
  · convert hdiv using 1; ring
  · intro h
    have h' : (p : ℤ) ∣ 2 * r := by convert h using 1; ring
    rcases hp'.dvd_or_dvd h' with h'' | h''
    · exact h2 h''
    · apply hpm
      have h5 : (p : ℤ) ∣ r ^ 2 := dvd_pow h'' two_ne_zero
      have := dvd_sub h5 hdiv
      simpa using this

private lemma odd_inert_of_leg {K : Type*} [Field K] [NumberField K] (m : ℤ) (S : 𝓞 K) (p : ℕ)
    [Fact p.Prime] (hex : ¬ p ∣ RingOfIntegers.exponent S)
    (hmin : minpoly ℤ S = X ^ 2 + C (0 : ℤ) * X + C (-m)) (hleg : legendreSym p m = -1) :
    (Ideal.span {(p : 𝓞 K)}).IsPrime := by
  apply kummer_inert S p hex
  rw [hmin]
  have hmap : ((X ^ 2 + C (0 : ℤ) * X + C (-m) : ℤ[X])).map (Int.castRingHom (ZMod p)) =
      X ^ 2 - C (m : ZMod p) := by simp [sub_eq_add_neg]
  rw [hmap]
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 2 - C (m : ZMod p)).natDegree = 2 := by compute_degree!
    rw [this]; simp
  · intro y hy
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hy
    exact (legendreSym.eq_neg_one_iff p).1 hleg ⟨y, by linear_combination (-1 : ZMod p) * hy⟩

/-- `X² - X - k` modulo 2 is irreducible for `k` odd. -/
private lemma irr_mod_two (k : ℤ) (hk : k % 2 = 1) :
    Irreducible ((X ^ 2 + C (-1 : ℤ) * X + C (-k) : ℤ[X]).map (Int.castRingHom (ZMod 2))) := by
  have hk2 : (k : ZMod 2) = 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    push_cast
    have : (2 : ZMod 2) = 0 := rfl
    simp [this]
  have hmap : ((X ^ 2 + C (-1 : ℤ) * X + C (-k) : ℤ[X])).map (Int.castRingHom (ZMod 2)) =
      X ^ 2 + C (-1 : ZMod 2) * X + C (-(k : ZMod 2)) := by
    rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
    simp
  rw [hmap, hk2]
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 2 + C (-1 : ZMod 2) * X + C (-1 : ZMod 2)).natDegree = 2 := by compute_degree!
    rw [this]; simp
  · intro y hy
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C, eval_mul] at hy
    revert y
    decide

private lemma odd_data (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (m : ℤ)
    (hm : Squarefree m) (hm1 : m ≠ 1) (s : K) (hs : s ^ 2 = m) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ S : 𝓞 K, ¬ p ∣ RingOfIntegers.exponent S ∧
      minpoly ℤ S = X ^ 2 + C (0 : ℤ) * X + C (-m) := by
  obtain ⟨S, -, hmin, ι, hι, hmem⟩ := sdata K hK m hm hm1 s hs
  exact ⟨S, not_dvd_exponent_of_index S p ι hmem (odd_prime_not_dvd_index m hm p hp2 ι _ hι), hmin⟩

private lemma ramified_of_dvd_m (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (m : ℤ) (hm : Squarefree m) (hm1 : m ≠ 1) (s : K) (hs : s ^ 2 = m) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hpm : (p : ℤ) ∣ m) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} = P ^ 2 := by
  obtain ⟨S, hex, hmin⟩ := odd_data K hK m hm hm1 s hs p hp2
  obtain ⟨m', hm'⟩ := hpm
  refine kummer_ramified S p hex 0 (-m) hmin 0 0 (-m') (by simp) (by rw [hm']; push_cast; ring) ?_
  rintro ⟨t, ht⟩
  apply prime_sq_not_dvd m hm p
  exact ⟨-t, by rw [hm']; linear_combination (-(p : ℤ)) * ht⟩

private lemma prime_sq_ne_mul {R : Type*} [CommRing R] [IsDedekindDomain R] (A P Q : Ideal R)
    (hA : A.IsPrime) (hA0 : A ≠ ⊥) (hP : P.IsPrime) (hQ : Q.IsPrime) (hPQ : P ≠ Q)
    (h : A * A = P * Q) : False := by
  have hne : P * Q ≠ ⊥ := by rw [← h]; exact mul_ne_zero hA0 hA0
  have hP0 : P ≠ ⊥ := fun h0 => hne (by rw [h0, Ideal.bot_mul])
  have hQ0 : Q ≠ ⊥ := fun h0 => hne (by rw [h0, Ideal.mul_bot])
  have hle : P * Q ≤ A := h ▸ Ideal.mul_le_left
  rcases (Ideal.IsPrime.mul_le hA).1 hle with h' | h'
  · have hPA : A = P := ((Ideal.IsPrime.isMaximal hP hP0).eq_of_le hA.ne_top h').symm
    rw [← hPA] at h
    exact hPQ (hPA.symm.trans (mul_left_cancel₀ hA0 h))
  · have hQA : A = Q := ((Ideal.IsPrime.isMaximal hQ hQ0).eq_of_le hA.ne_top h').symm
    rw [← hQA] at h
    exact hPQ ((mul_right_cancel₀ hA0 h).symm.trans hQA)

private lemma span_ne_bot {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    Ideal.span {(p : 𝓞 K)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

section Quadratic

variable {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) {m : ℤ} (hm : Squarefree m)
  (hm1 : m ≠ 1) {s : K} (hs : s ^ 2 = m)
include hK hm hm1 hs

/-- **Example 3.44 (i).** In a quadratic field $K = \mathbb Q(\sqrt m)$, a prime number dividing
$\mathrm{disc}(\mathcal O_K/\mathbb Z)$ ramifies: $p\mathcal O_K = \mathfrak p^2$. -/
@[kb "milne2020ant" "v3.08, Example 3.44 (i), p. 63"]
theorem example_3_44_i (p : ℕ) [Fact p.Prime] (hp : (p : ℤ) ∣ discr K) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} = P ^ 2 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h4 : m % 4 ≠ 0 := by
      intro h0
      have := hm 2 ⟨m / 4, by omega⟩
      rcases Int.isUnit_iff.1 this with h | h <;> omega
    have hm4 : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hm4 with h1 | h23
    · exfalso
      obtain ⟨W, -, -, ι, hι, -⟩ := wdata K hK m hm hm1 s hs h1
      obtain ⟨t, ht⟩ := hp
      have : m = 2 * (ι ^ 2 * t) := by rw [hι, ht]; push_cast; ring
      generalize ι ^ 2 * t = X at this
      omega
    · obtain ⟨S, -, hmin, ι, hι, hmem⟩ := sdata K hK m hm hm1 s hs
      have hnd : ¬ ((2 : ℕ) : ℤ) ∣ ι := by
        rintro ⟨t, rfl⟩
        have h4' : m = t ^ 2 * discr K := by
          have : 4 * m = 4 * (t ^ 2 * discr K) := by rw [hι]; push_cast; ring
          exact Int.eq_of_mul_eq_mul_left (by norm_num) this
        have hu := hm t ⟨discr K, by rw [h4']; ring⟩
        have ht1 : t ^ 2 = 1 := by
          rcases Int.isUnit_iff.1 hu with h | h <;> rw [h] <;> norm_num
        rw [ht1, one_mul] at h4'
        rcases prop_2_40_b K with h | h <;> omega
      have hex := not_dvd_exponent_of_index S 2 ι hmem hnd
      rcases (by omega : m % 4 = 2 ∨ m % 4 = 3) with h | h
      · exact kummer_ramified S 2 hex 0 (-m) hmin 0 0 (-(m / 2)) (by simp)
          (by push_cast; omega) (by push_cast; omega)
      · exact kummer_ramified S 2 hex 0 (-m) hmin 1 1 ((1 - m) / 2) (by norm_num)
          (by push_cast; omega) (by push_cast; omega)
  · obtain ⟨S, -, hmin, ι, hι, hmem⟩ := sdata K hK m hm hm1 s hs
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
    have hpm : (p : ℤ) ∣ m := by
      have h4 : (p : ℤ) ∣ 4 * m := by rw [hι]; exact Dvd.dvd.mul_left hp _
      rcases hp'.dvd_or_dvd h4 with h | h
      · exfalso
        have h22 : (p : ℤ) ∣ 2 * 2 := by norm_num; exact h
        rcases hp'.dvd_or_dvd h22 with h5 | h5 <;> exact odd_prime_ndvd_two p hp2 h5
      · exact h
    exact ramified_of_dvd_m K hK m hm hm1 s hs p hp2 hpm

/-- **Example 3.44 (ii)**, splitting. For an odd prime $p \nmid m$, $(p)$ is the product of two distinct prime ideals
of $\mathcal O_K$ iff $m$ is a square modulo $p$, i.e. $\left(\frac mp\right) = 1$. -/
@[kb "milne2020ant" "v3.08, Example 3.44 (ii), p. 63"]
theorem example_3_44_ii_split (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : ¬ (p : ℤ) ∣ m) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ Ideal.span {(p : 𝓞 K)} = P * Q) ↔
      legendreSym p m = 1 := by
  obtain ⟨S, hex, hmin⟩ := odd_data K hK m hm hm1 s hs p hp2
  constructor
  · rintro ⟨P, Q, hP, hQ, -, h⟩
    have hm0 : (m : ZMod p) ≠ 0 := fun h => hpm ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
    rcases legendreSym.eq_one_or_neg_one p hm0 with h1 | h1
    · exact h1
    · exact (no_prime_eq_mul P Q _ (odd_inert_of_leg m S p hex hmin h1) (span_ne_bot p) hP hQ h).elim
  · exact odd_split_of_leg m S p hp2 hpm hex hmin

/-- **Example 3.44 (ii)**, inertia. For an odd prime $p \nmid m$, $(p)$ is a prime ideal of $\mathcal O_K$ iff $m$ is
not a square modulo $p$, i.e. $\left(\frac mp\right) = -1$. -/
@[kb "milne2020ant" "v3.08, Example 3.44 (ii), p. 63"]
theorem example_3_44_ii_inert (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : ¬ (p : ℤ) ∣ m) :
    (Ideal.span {(p : 𝓞 K)}).IsPrime ↔ legendreSym p m = -1 := by
  obtain ⟨S, hex, hmin⟩ := odd_data K hK m hm hm1 s hs p hp2
  constructor
  · intro hpr
    have hm0 : (m : ZMod p) ≠ 0 := fun h => hpm ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
    rcases legendreSym.eq_one_or_neg_one p hm0 with h1 | h1
    · obtain ⟨P, Q, hP, hQ, -, h⟩ := odd_split_of_leg m S p hp2 hpm hex hmin h1
      exact (no_prime_eq_mul P Q _ hpr (span_ne_bot p) hP hQ h).elim
    · exact h1
  · exact odd_inert_of_leg m S p hex hmin

/-- **Example 3.44 (iii)**, splitting of $2$. If $m \equiv 1 \bmod 4$, then $(2)$ is the product of two distinct prime
ideals of $\mathcal O_K$ iff $m \equiv 1 \bmod 8$. -/
@[kb "milne2020ant" "v3.08, Example 3.44 (iii), p. 63"]
theorem example_3_44_iii_split (hm4 : m % 4 = 1) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ Ideal.span {(2 : 𝓞 K)} = P * Q) ↔ m % 8 = 1 := by
  obtain ⟨W, -, hmin, ι, hι, hmem⟩ := wdata K hK m hm hm1 s hs hm4
  have hnd : ¬ ((2 : ℕ) : ℤ) ∣ ι := by
    rintro ⟨t, rfl⟩
    have : m = 4 * (t ^ 2 * discr K) := by rw [hι]; push_cast; ring
    generalize t ^ 2 * discr K = X at this
    omega
  have hex := not_dvd_exponent_of_index W 2 ι hmem hnd
  have hsplit : m % 8 = 1 → ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {((2 : ℕ) : 𝓞 K)} = P * Q := fun h =>
    kummer_split W 2 hex (-1) (-(m / 4)) hmin 0 1 (by norm_num) (by push_cast; clear hex hnd hι hmem hmin; omega)
      (by norm_num)
  have hinert : m % 8 = 5 → (Ideal.span {((2 : ℕ) : 𝓞 K)}).IsPrime := fun h =>
    kummer_inert W 2 hex (by rw [hmin]; exact irr_mod_two (m / 4) (by omega))
  constructor
  · rintro ⟨P, Q, hP, hQ, -, h⟩
    by_contra hne8
    have := hinert (by omega)
    simp only [Nat.cast_ofNat] at this
    exact no_prime_eq_mul P Q _ this (by simpa using span_ne_bot (K := K) 2) hP hQ h
  · intro h
    simpa using hsplit h

/-- **Example 3.44 (iii)**, inertia of $2$. If $m \equiv 1 \bmod 4$, then $(2)$ is a prime ideal of $\mathcal O_K$ iff
$m \equiv 5 \bmod 8$. -/
@[kb "milne2020ant" "v3.08, Example 3.44 (iii), p. 63"]
theorem example_3_44_iii_inert (hm4 : m % 4 = 1) :
    (Ideal.span {(2 : 𝓞 K)}).IsPrime ↔ m % 8 = 5 := by
  obtain ⟨W, -, hmin, ι, hι, hmem⟩ := wdata K hK m hm hm1 s hs hm4
  have hnd : ¬ ((2 : ℕ) : ℤ) ∣ ι := by
    rintro ⟨t, rfl⟩
    have : m = 4 * (t ^ 2 * discr K) := by rw [hι]; push_cast; ring
    generalize t ^ 2 * discr K = X at this
    omega
  have hex := not_dvd_exponent_of_index W 2 ι hmem hnd
  constructor
  · intro hpr
    by_contra hne5
    obtain ⟨P, Q, hP, hQ, -, h⟩ := kummer_split W 2 hex (-1) (-(m / 4)) hmin 0 1 (by norm_num)
      (by push_cast; clear hex hnd hι hmem hmin; omega) (by norm_num)
    simp only [Nat.cast_ofNat] at h
    exact no_prime_eq_mul P Q _ hpr (by simpa using span_ne_bot (K := K) 2) hP hQ h
  · intro h
    have := kummer_inert W 2 hex (by rw [hmin]; exact irr_mod_two (m / 4) (by omega))
    simpa using this

/-- **Remark 3.50**, first assertion. The set $\mathrm{Spl}(K)$ of prime numbers splitting in $K = \mathbb Q(\sqrt m)$
consists of the odd primes $p \nmid m$ with $\left(\frac mp\right) = 1$, together possibly with $2$: an odd prime $p$
splits iff $p \nmid m$ and $\left(\frac mp\right) = 1$. -/
@[kb "milne2020ant" "v3.08, Remark 3.50, p. 65"]
theorem remark_3_50_split (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ Ideal.span {(p : 𝓞 K)} = P * Q) ↔
      ¬ (p : ℤ) ∣ m ∧ legendreSym p m = 1 := by
  constructor
  · intro hsp
    have hpm : ¬ (p : ℤ) ∣ m := by
      intro hpm
      obtain ⟨P, Q, hP, hQ, hPQ, h⟩ := hsp
      obtain ⟨R, hR, hRe⟩ := ramified_of_dvd_m K hK m hm hm1 s hs p hp2 hpm
      rw [hRe, pow_two] at h
      exact prime_sq_ne_mul R P Q hR (fun h0 => span_ne_bot p (by rw [hRe, h0]; simp)) hP hQ hPQ h
    exact ⟨hpm, (example_3_44_ii_split hK hm hm1 hs p hp2 hpm).1 hsp⟩
  · rintro ⟨hpm, hleg⟩
    exact (example_3_44_ii_split hK hm hm1 hs p hp2 hpm).2 hleg

end Quadratic

/-- The set $\mathrm{Spl}(K)$ of prime numbers that split completely in a number field $K$: $p\mathcal O_K$ is a
product of $[K:\mathbb Q]$ distinct primes, i.e. every prime $\mathfrak P \mid p$ has $e = f = 1$. -/
def splitPrimesQ (K : Type*) [Field K] [NumberField K] : Set ℕ :=
  {p | p.Prime ∧ ∀ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1}

/-- **Remark 3.50**, second assertion (named statement; Milne's Theorem 8.38, a consequence of the Chebotarev density
theorem): two Galois number fields $K$, $K'$ are isomorphic iff $\mathrm{Spl}(K) = \mathrm{Spl}(K')$. -/
@[kb "milne2020ant" "v3.08, Remark 3.50 and Thm. 8.38, p. 65"]
structure GaloisDeterminedBySplitPrimes : Prop where
  iff : ∀ (K K' : Type) [Field K] [NumberField K] [IsGalois ℚ K] [Field K'] [NumberField K'] [IsGalois ℚ K'],
    Nonempty (K ≃ₐ[ℚ] K') ↔ splitPrimesQ K = splitPrimesQ K'

private lemma gauss_prime_of_norm (π : GaussianInt) (hn : Prime π.norm) : Prime π := by
  rw [← irreducible_iff_prime]
  refine ⟨fun h => hn.not_isUnit ((Zsqrtd.isUnit_iff_norm_isUnit π).1 h), fun a b hab => ?_⟩
  have : π.norm = a.norm * b.norm := by rw [hab, Zsqrtd.norm_mul]
  rcases hn.irreducible.isUnit_or_isUnit this with h | h
  · exact Or.inl ((Zsqrtd.isUnit_iff_norm_isUnit a).2 h)
  · exact Or.inr ((Zsqrtd.isUnit_iff_norm_isUnit b).2 h)

/-- **Example 3.45.** For an odd prime $p$ the following are equivalent: (a) $p \equiv 1 \bmod 4$; (b) $(p)$ splits in
$\mathbb Z[i]$, i.e. is the product of two distinct prime ideals; (c) $p = a^2 + b^2$ for some integers $a, b$. -/
@[kb "milne2020ant" "v3.08, Example 3.45, p. 64"]
theorem example_3_45 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    [p % 4 = 1,
      ∃ P Q : Ideal GaussianInt, P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ Ideal.span {(p : GaussianInt)} = P * Q,
      ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2].TFAE := by
  have hp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  tfae_have 1 → 3 := by
    intro h
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
    exact ⟨a, b, by exact_mod_cast hab.symm⟩
  tfae_have 3 → 1 := by
    rintro ⟨a, b, h⟩
    have h1 : (p : ℤ) % 4 = 1 := by
      have h2 : (p : ℤ) % 2 = 1 := by exact_mod_cast hodd
      have ha : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
        have : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
        rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
      have hb : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
        have : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
        rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
      omega
    omega
  tfae_have 1 → 2 := by
    intro h
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
    set π : GaussianInt := ⟨a, b⟩ with hπ
    have hN : π.norm = p := by
      simp [hπ, Zsqrtd.norm_def]
      nlinarith [hab]
    have hπp : Prime π := gauss_prime_of_norm π (by rw [hN]; exact hp')
    have hcp : Prime (star π) := by
      apply gauss_prime_of_norm
      rw [Zsqrtd.norm_conj]
      rw [hN]; exact hp'
    refine ⟨Ideal.span {π}, Ideal.span {star π}, (Ideal.span_singleton_prime hπp.ne_zero).2 hπp,
      (Ideal.span_singleton_prime hcp.ne_zero).2 hcp, ?_, ?_⟩
    · intro heq
      have hd : π ∣ star π := Ideal.span_singleton_le_span_singleton.1 heq.ge
      have hnd : ∀ z : GaussianInt, π ∣ z → (p : ℤ) ∣ z.norm := by
        intro z hz
        rw [← hN]
        exact map_dvd Zsqrtd.normMonoidHom hz
      have h2 : ¬ (p : ℤ) ∣ 2 := by
        intro h
        have : p ∣ 2 := by exact_mod_cast h
        have := Nat.le_of_dvd (by norm_num) this
        have := hp.two_le
        omega
      have ha : (p : ℤ) ∣ a := by
        have h1 : π ∣ (⟨2 * a, 0⟩ : GaussianInt) := by
          have : (⟨2 * a, 0⟩ : GaussianInt) = π + star π := by
            ext <;> simp [hπ]; ring
          rw [this]; exact dvd_add dvd_rfl hd
        have := hnd _ h1
        simp only [Zsqrtd.norm_def] at this
        have h3 : (p : ℤ) ∣ (2 * a) * (2 * a) := by convert this using 1; ring
        rcases hp'.dvd_or_dvd h3 with h | h <;>
        rcases hp'.dvd_or_dvd h with h | h
        all_goals first | exact absurd h h2 | exact h
      have hb : (p : ℤ) ∣ b := by
        have h1 : π ∣ (⟨0, 2 * b⟩ : GaussianInt) := by
          have : (⟨0, 2 * b⟩ : GaussianInt) = π - star π := by
            ext <;> simp [hπ]; ring
          rw [this]; exact dvd_sub dvd_rfl hd
        have := hnd _ h1
        simp only [Zsqrtd.norm_def] at this
        have h3 : (p : ℤ) ∣ (2 * b) * (2 * b) := by convert this using 1; ring
        rcases hp'.dvd_or_dvd h3 with h | h <;>
        rcases hp'.dvd_or_dvd h with h | h
        all_goals first | exact absurd h h2 | exact h
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd'⟩ := hb
      have : (p : ℤ) * (p * (c ^ 2 + d ^ 2)) = p * 1 := by
        have e : (p : ℤ) = a ^ 2 + b ^ 2 := by exact_mod_cast hab.symm
        rw [hc, hd'] at e
        linear_combination (-1 : ℤ) * e
      have h4 := mul_left_cancel₀ hp'.ne_zero this
      have h5 := Int.eq_one_of_mul_eq_one_right (by positivity) h4
      have : (p : ℤ) ≥ 2 := by exact_mod_cast hp.two_le
      omega
    · rw [Ideal.span_singleton_mul_span_singleton, ← Zsqrtd.norm_eq_mul_conj, hN]
      simp
  tfae_have 2 → 1 := by
    rintro ⟨P, Q, hP, hQ, hPQ, h⟩
    by_contra h1
    have h3 : p % 4 = 3 := by omega
    have hpr : Prime (p : GaussianInt) := GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p |>.2 h3
    have hI : (Ideal.span {(p : GaussianInt)}).IsPrime := (Ideal.span_singleton_prime hpr.ne_zero).2 hpr
    have hne : (Ideal.span {(p : GaussianInt)}) ≠ ⊥ := by
      simpa using hpr.ne_zero
    have key : ∀ P Q : Ideal GaussianInt, Q.IsPrime → P * Q = Ideal.span {(p : GaussianInt)} →
        P ≤ Ideal.span {(p : GaussianInt)} → False := by
      intro P Q hQ h h'
      have h1 : P ≤ P * Q := h ▸ h'
      have h2 : P * Q ≤ P := Ideal.mul_le_left
      have hP0 : P ≠ ⊥ := by
        rintro rfl
        simp at h
        exact hne h.symm
      have : P * Q = P * ⊤ := by rw [Ideal.mul_top]; exact le_antisymm h2 h1
      exact hQ.ne_top (mul_left_cancel₀ hP0 this)
    have hPQ' : P * Q ≤ Ideal.span {(p : GaussianInt)} := h.ge
    rcases (Ideal.IsPrime.mul_le hI).1 hPQ' with h' | h'
    · exact key P Q hQ h.symm h'
    · exact key Q P hP (by rw [mul_comm]; exact h.symm) h'
  tfae_finish

section Eisenstein

variable {A K L B : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing B] [IsDomain B]
  [Algebra B L] [Algebra A B] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsIntegralClosure B A L]

/-- Decomposition of `p S` at a prime `P` above `p`. -/
private lemma eis_decomp {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ ⊥) (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    P ≠ ⊥ ∧ ∃ I : Ideal S, ¬ I ≤ P ∧ p.map (algebraMap R S) = P ^ P.ramificationIdx R * I := by
  have hpS : p.map (algebraMap R S) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  have hP0 : P ≠ ⊥ := ne_bot_of_le_ne_bot hpS (Ideal.map_le_of_le_comap (P.over_def p).le)
  have hPm : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  obtain ⟨I, hI, hmap⟩ := Ideal.eq_prime_pow_mul_coprime hpS P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p P hpS] at hmap
  refine ⟨hP0, I, ?_, hmap⟩
  intro hle
  rw [sup_of_le_left hle] at hI
  exact (inferInstance : P.IsPrime).ne_top hI

private lemma eis_not_mem {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ ⊥) (P : Ideal S) [P.IsPrime] [P.LiesOver p] (a : R) (ha : a ∈ p) (ha2 : a ∉ p ^ 2) :
    algebraMap R S a ∉ P ^ (P.ramificationIdx R + 1) := by
  intro h
  obtain ⟨hP0, I, hI, hmap⟩ := eis_decomp p hp P
  have hdvd : p ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 (by simpa [Ideal.span_singleton_le_iff_mem p] using ha)
  obtain ⟨J, hJ⟩ := hdvd
  have hJp : ¬ J ≤ p := by
    intro hle
    apply ha2
    have : Ideal.span {a} ≤ p * p := by rw [hJ]; exact Ideal.mul_mono_right hle
    rw [sq]
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  have hmapa : Ideal.span {algebraMap R S a} = p.map (algebraMap R S) * J.map (algebraMap R S) := by
    rw [← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton]
  have hd : P ^ (P.ramificationIdx R + 1) ∣ Ideal.span {algebraMap R S a} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h)
  rw [hmapa, hmap, mul_assoc, pow_succ] at hd
  have hne : P ^ P.ramificationIdx R ≠ 0 := pow_ne_zero _ hP0
  rw [mul_dvd_mul_iff_left hne] at hd
  rcases (Ideal.prime_of_isPrime hP0 inferInstance).dvd_or_dvd hd with h1 | h1
  · exact hI (Ideal.dvd_iff_le.1 h1)
  · apply hJp
    have := Ideal.dvd_iff_le.1 h1
    rw [Ideal.map_le_iff_le_comap] at this
    rw [P.over_def p]
    exact this

/-- the polynomial identity. -/
private lemma eis_identity {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (f : R[X])
    (hmon : f.Monic) (α : S) (hα : aeval α f = 0) (n : ℕ) (hn : f.natDegree = n + 1) :
    α ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), algebraMap R S (f.coeff i) * α ^ i = 0 := by
  rw [aeval_eq_sum_range, hn, Finset.sum_range_succ] at hα
  have hc : f.coeff (n + 1) = 1 := by rw [← hn]; exact hmon
  simp only [hc, Algebra.smul_def, map_one, one_mul] at hα
  rw [add_comm]; exact hα

private lemma eis_mem_P {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (f : R[X]) (hmon : f.Monic) (hf : f.IsEisensteinAt p) (hdeg : 0 < f.natDegree)
    (α : S) (hα : aeval α f = 0) (P : Ideal S) [P.IsPrime] [P.LiesOver p] : α ∈ P := by
  obtain ⟨n, hn⟩ : ∃ n, f.natDegree = n + 1 := ⟨f.natDegree - 1, by omega⟩
  have hE := eis_identity f hmon α hα n hn
  have hmemP : ∀ a ∈ p, algebraMap R S a ∈ P := fun a ha => by
    have h1 : a ∈ P.under R := by rw [← P.over_def p]; exact ha
    exact h1
  have hcoef : ∀ i < n + 1, f.coeff i ∈ p := fun i hi => hf.mem (by omega)
  have h1 : α ^ (n + 1) = -∑ i ∈ Finset.range (n + 1), algebraMap R S (f.coeff i) * α ^ i := by
    rw [eq_neg_iff_add_eq_zero]; exact hE
  refine (inferInstance : P.IsPrime).mem_of_pow_mem (n + 1) ?_
  rw [h1]
  refine P.neg_mem (P.sum_mem fun i hi => ?_)
  exact P.mul_mem_right _ (hmemP _ (hcoef i (Finset.mem_range.1 hi)))

private lemma eis_core {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ ⊥) (f : R[X]) (hmon : f.Monic) (hf : f.IsEisensteinAt p) (hdeg : 0 < f.natDegree)
    (α : S) (hα : aeval α f = 0) (P : Ideal S) [P.IsPrime] [P.LiesOver p] (k : ℕ) (hk : 1 ≤ k)
    (hαk : α ∈ P ^ k) (hmk : P.ramificationIdx R + 1 ≤ f.natDegree * k) :
    algebraMap R S (f.coeff 0) ∈ P ^ (P.ramificationIdx R + 1) := by
  obtain ⟨hP0, I, hI, hmap⟩ := eis_decomp p hp P
  obtain ⟨n, hn⟩ : ∃ n, f.natDegree = n + 1 := ⟨f.natDegree - 1, by omega⟩
  have hE := eis_identity f hmon α hα n hn
  have hmemPe : ∀ a ∈ p, algebraMap R S a ∈ P ^ P.ramificationIdx R := fun a ha => by
    have : algebraMap R S a ∈ p.map (algebraMap R S) := Ideal.mem_map_of_mem _ ha
    rw [hmap] at this
    exact (Ideal.mul_le_inf this).1
  have hcoef : ∀ i < n + 1, f.coeff i ∈ p := fun i hi => hf.mem (by omega)
  have hαP : α ∈ P := Ideal.pow_le_self (by omega) hαk
  rw [Finset.sum_range_succ'] at hE
  have h0 : algebraMap R S (f.coeff 0) = -(α ^ (n + 1) +
      ∑ i ∈ Finset.range n, algebraMap R S (f.coeff (i + 1)) * α ^ (i + 1)) := by
    rw [eq_neg_iff_add_eq_zero]
    simp only [pow_zero, mul_one] at hE
    rw [← hE]; ring
  rw [h0]
  refine Submodule.neg_mem _ (Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i hi => ?_))
  · have h2 : α ^ (n + 1) ∈ (P ^ k) ^ (n + 1) := Ideal.pow_mem_pow hαk _
    rw [← pow_mul] at h2
    refine Ideal.pow_le_pow_right ?_ h2
    rw [hn] at hmk; nlinarith
  · rw [pow_succ _ (P.ramificationIdx R)]
    exact Ideal.mul_mem_mul (hmemPe _ (hcoef _ (by have := Finset.mem_range.1 hi; omega)))
      (Ideal.pow_le_self (Nat.succ_ne_zero i) (Ideal.pow_mem_pow hαP _))

private lemma eis_ram_ge {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ ⊥) (f : R[X]) (hmon : f.Monic) (hf : f.IsEisensteinAt p) (hdeg : 0 < f.natDegree)
    (α : S) (hα : aeval α f = 0) (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    f.natDegree ≤ P.ramificationIdx R := by
  by_contra hlt
  rw [not_le] at hlt
  have hαP := eis_mem_P p f hmon hf hdeg α hα P
  exact eis_not_mem p hp P (f.coeff 0) (hf.mem hdeg) hf.notMem
    (eis_core p hp f hmon hf hdeg α hα P 1 le_rfl (by simpa using hαP) (by omega))

/-- **Proposition 3.53**, irreducibility. A monic polynomial over a Dedekind domain $A$ that is Eisenstein at a
nonzero prime $\mathfrak p$ (coefficients other than the leading one in $\mathfrak p$, constant term not in
$\mathfrak p^2$) is irreducible over the field of fractions $K$. -/
@[kb "milne2020ant" "v3.08, Prop. 3.53, p. 66"]
theorem prop_3_53_irreducible (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) (f : A[X]) (hmon : f.Monic)
    (hf : f.IsEisensteinAt p) (hdeg : 0 < f.natDegree) : Irreducible (f.map (algebraMap A K)) := by
  have hirr : Irreducible f := hf.irreducible inferInstance hmon.isPrimitive hdeg
  exact (hmon.irreducible_iff_irreducible_map_fraction_map).1 hirr

/-- **Proposition 3.53**, total ramification. Let $f \in A[X]$ be monic of degree $m \ge 1$ and Eisenstein at the
nonzero prime $\mathfrak p$ of the Dedekind domain $A$, let $\alpha \in B$ be a root of $f$ generating $L$ over $K$
($L$ finite separable over $K$, $B$ the integral closure of $A$ in $L$). Then $\mathfrak p$ is totally ramified in
$L$: $\mathfrak pB = \mathfrak P^m$ with $\mathfrak P = (\mathfrak p, \alpha) = \mathfrak pB + \alpha B$ prime. -/
@[kb "milne2020ant" "v3.08, Prop. 3.53, p. 66"]
theorem prop_3_53 (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) (f : A[X]) (hmon : f.Monic)
    (hf : f.IsEisensteinAt p) (hdeg : 0 < f.natDegree) (α : B) (hα : aeval α f = 0)
    (hgen : IntermediateField.adjoin K {algebraMap B L α} = ⊤) :
    (p.map (algebraMap A B) ⊔ Ideal.span {α}).IsPrime ∧
      p.map (algebraMap A B) = (p.map (algebraMap A B) ⊔ Ideal.span {α}) ^ f.natDegree := by
  have : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
  have : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have hinj : Function.Injective (algebraMap A B) := by
    have h : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    rw [IsScalarTower.algebraMap_eq A B L] at h
    exact Function.Injective.of_comp h
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  have : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
  have : Module.IsTorsionFree A B := inferInstance
  have : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  have hirr := prop_3_53_irreducible (K := K) p hp f hmon hf hdeg
  have hrank : Module.finrank A B = f.natDegree := by
    rw [← IsFractionRing.finrank_eq A K B L]
    have hint : IsIntegral K (algebraMap B L α) := by
      refine ⟨f.map (algebraMap A K), hmon.map _, ?_⟩
      rw [← aeval_def, aeval_map_algebraMap, aeval_algebraMap_apply, hα, map_zero]
    have hmin : minpoly K (algebraMap B L α) = f.map (algebraMap A K) := by
      refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (hmon.map _)).symm
      rw [aeval_map_algebraMap, aeval_algebraMap_apply, hα, map_zero]
    have := IntermediateField.adjoin.finrank hint
    rw [hgen, IntermediateField.finrank_top', hmin, hmon.natDegree_map] at this
    exact this
  -- the unique prime
  let P0 : p.primesOver B := Classical.choice inferInstance
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p B
  rw [hrank] at hsum
  have hge : ∀ Q : p.primesOver B, f.natDegree ≤ Q.1.ramificationIdx A := fun Q =>
    eis_ram_ge p hp f hmon hf hdeg α hα Q.1
  have hpos : ∀ Q : p.primesOver B, 0 < Q.1.inertiaDeg A := fun Q => Ideal.inertiaDeg_pos _ _
  have hle : ∀ Q : p.primesOver B, Q.1.ramificationIdx A * Q.1.inertiaDeg A ≤ f.natDegree := by
    intro Q
    rw [← hsum]
    exact Finset.single_le_sum (f := fun q : p.primesOver B =>
      q.1.ramificationIdx A * q.1.inertiaDeg A) (fun _ _ => Nat.zero_le _) (Finset.mem_univ Q)
  have huniq : ∀ Q : p.primesOver B, Q = P0 := by
    intro Q
    by_contra hne
    have h2 : ∑ q ∈ ({Q, P0} : Finset (p.primesOver B)),
        q.1.ramificationIdx A * q.1.inertiaDeg A ≤ f.natDegree := by
      rw [← hsum]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair hne] at h2
    have h3 := hge Q
    have h4 := hge P0
    have h5 := hpos Q
    have h6 := hpos P0
    nlinarith
  have heq : P0.1.ramificationIdx A = f.natDegree := by
    have := hle P0
    have := hge P0
    have := hpos P0
    nlinarith
  have : P0.1.IsPrime := inferInstance
  have : P0.1.LiesOver p := inferInstance
  obtain ⟨hP0, I, hI, hmap⟩ := eis_decomp p hp P0.1
  have hIt : I = ⊤ := by
    by_contra hIne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hIne
    have hpm : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
    have hpM : p ≤ M.comap (algebraMap A B) := by
      rw [← Ideal.map_le_iff_le_comap, hmap]
      exact (Ideal.mul_le_right).trans hIM
    have hMl : M.LiesOver p :=
      ⟨(hpm.eq_of_le (Ideal.comap_ne_top _ hM.ne_top) hpM)⟩
    have := huniq ⟨M, hM.isPrime, hMl⟩
    exact hI (hIM.trans (by rw [show M = P0.1 from congrArg Subtype.val this]))
  rw [hIt, Ideal.mul_top, heq] at hmap
  have hαP : α ∈ P0.1 := eis_mem_P p f hmon hf hdeg α hα P0.1
  have hm1 : 1 ≤ f.natDegree := hdeg
  have hα2 : α ∉ P0.1 ^ 2 := by
    intro h2
    refine eis_not_mem p hp P0.1 (f.coeff 0) (hf.mem hdeg) hf.notMem ?_
    exact eis_core p hp f hmon hf hdeg α hα P0.1 2 (by norm_num) h2 (by omega)
  have hQP : p.map (algebraMap A B) ⊔ Ideal.span {α} ≤ P0.1 := by
    refine sup_le ?_ ?_
    · rw [hmap]; exact Ideal.pow_le_self (by omega)
    · rwa [Ideal.span_singleton_le_iff_mem]
  have hQd : p.map (algebraMap A B) ⊔ Ideal.span {α} ∣ P0.1 ^ f.natDegree := by
    rw [← hmap]; exact Ideal.dvd_iff_le.2 le_sup_left
  obtain ⟨i, hi, hass⟩ := (dvd_prime_pow (Ideal.prime_of_isPrime hP0 inferInstance) _).1 hQd
  rw [associated_iff_eq] at hass
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hass
    rw [hass] at hQP
    exact (inferInstance : P0.1.IsPrime).ne_top (top_le_iff.1 (by simpa using hQP))
  have hi1 : i = 1 := by
    by_contra hne
    apply hα2
    have : α ∈ p.map (algebraMap A B) ⊔ Ideal.span {α} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [hass] at this
    exact Ideal.pow_le_pow_right (by omega) this
  rw [hi1, pow_one] at hass
  rw [hass]
  exact ⟨inferInstance, hmap⟩

end Eisenstein

end NumberFieldKB.MilneANT
