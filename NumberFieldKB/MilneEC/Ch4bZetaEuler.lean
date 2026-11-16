import NumberFieldKB.MilneEC.Ch4bZetaAffine

/-!
# Milne, Elliptic Curves, Chapter IV §9: Proposition 9.8, the zeta function of an affine curve through point counts

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 9.8, pdf p. 162.

For a finitely generated algebra $R$ over $\mathbb F_p$ (for an affine plane curve $C : f = 0$,
$R = \mathbb F_p[X, Y]/(f)$), the Euler product $Z(C, T) = \prod_{\mathfrak p} (1 - T^{\deg \mathfrak p})^{-1}$ over the
maximal ideals of $R$ (`eulerZeta`, multiplied out) equals $\exp\bigl(\sum_{m \ge 1} N_m T^m / m\bigr)$, where
$N_m = \#\operatorname{Hom}_{\mathbb F_p}(R, \mathbb F_{p^m})$ (`homCount`).

**Milne's proof, followed here.** Each factor is an exponential: $(1 - T^d)^{-1} = \exp\bigl(\sum_{d \mid m} d\,T^m/m\bigr)$
(the logarithmic derivative of both sides is $\sum_{d \mid m} d\,T^m$), so the product over the maximal ideals is
$\exp\bigl(\sum_m \sum_{\deg \mathfrak p \mid m} \deg \mathfrak p \, T^m / m\bigr)$.  And
$N_m = \sum_{\deg \mathfrak p \mid m} \deg \mathfrak p$: a homomorphism $R \to \mathbb F_{p^m}$ has a maximal kernel
$\mathfrak p$, and there are exactly $\deg \mathfrak p$ embeddings of $R/\mathfrak p = \mathbb F_{p^{\deg \mathfrak p}}$ in
$\mathbb F_{p^m}$ when $\deg \mathfrak p \mid m$, none otherwise.  Since only finitely many maximal ideals have degree at
most $M$ (`finite_maxDeg_le`), the coefficients up to $T^M$ are those of a finite product, which is how the infinite
product is handled here.

## Main results
* `eulerZeta_eq_expSeries`: the identity for every finitely generated $\mathbb F_p$-algebra (Milne states it for affine
  plane curves; the proof is the same).
* `prop9_8`: the named statement `Prop9_8` holds.
* `example_9_7_unconditional`: $Z(\mathbb A^1, T) = 1/(1 - pT)$.
* `theorem_9_10_of_prop9_9`: Theorem 9.10 for an elliptic curve over $\mathbb F_p$, conditional on `Prop9_9` only.
-/

open PowerSeries

namespace NumberFieldKB.MilneEC

variable {p : ℕ} [Fact p.Prime]

/-! ### One Euler factor -/

/-- $m \mapsto d$ if $d \mid m$, else $0$: the coefficients of the logarithmic derivative of $(1 - T^d)^{-1}$. -/
noncomputable def divSeries (d : ℕ) : ℕ → ℚ := fun m => if d ∣ m then (d : ℚ) else 0

/-- The series $(1 - T^d)^{-1} = \sum_{n \ge 0} T^{dn}$. -/
noncomputable def geomPow (d : ℕ) : PowerSeries ℚ := PowerSeries.mk fun m => if d ∣ m then 1 else 0

theorem expSeries_zero : expSeries (fun _ => (0 : ℚ)) = 1 := by
  have hL : logDerivSeries (fun _ => (0 : ℚ)) = 0 := by
    ext n; simp [logDerivSeries]
  refine ode_unique (logDerivSeries (fun _ => (0 : ℚ))) (by simp [logDerivSeries]) ?_ (expSeries_ode _) ?_
  · simp [constantCoeff_expSeries]
  · rw [hL]; simp

theorem expSeries_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℚ) :
    ∏ i ∈ s, expSeries (a i) = expSeries (fun m => ∑ i ∈ s, a i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expSeries_zero.symm
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, ih, expSeries_add]
    congr 1
    funext m
    rw [Finset.sum_insert hi]

/-- For $d \le n$: $d \mid n - d \iff d \mid n$. -/
private lemma dvd_sub_self_iff' {d n : ℕ} (h : d ≤ n) : d ∣ n - d ↔ d ∣ n := by
  have h1 : d ∣ d + (n - d) ↔ d ∣ n - d := Nat.dvd_add_right (dvd_refl d)
  rw [Nat.add_sub_of_le h] at h1
  exact h1.symm

/-- $L \cdot (1 - T^d) = d T^d$ for the logarithmic derivative $L$ of $(1 - T^d)^{-1}$. -/
private lemma logDeriv_divSeries_mul (d : ℕ) (hd : 1 ≤ d) :
    logDerivSeries (divSeries d) * (1 - X ^ d) = C (d : ℚ) * X ^ d := by
  have hd0 : d ≠ 0 := by omega
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_C_mul_X_pow]
  simp only [logDerivSeries, divSeries, coeff_mk]
  by_cases h1 : d ≤ n
  · have hn0 : n ≠ 0 := by omega
    have hdiv := dvd_sub_self_iff' h1
    by_cases h2 : d ∣ n
    · have h3 := hdiv.2 h2
      by_cases h4 : n = d
      · simp [h4, hd0]
      · have h5 : n - d ≠ 0 := by omega
        simp [h1, hn0, h2, h3, h4, h5]
    · have h3 : ¬ d ∣ n - d := fun h => h2 (hdiv.1 h)
      have h4 : n ≠ d := fun h => h2 (h ▸ dvd_refl d)
      simp [h1, hn0, h2, h3, h4]
  · by_cases hn : n = 0
    · subst hn
      simp [h1, Ne.symm hd0]
    · have h2 : ¬ d ∣ n := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      have h4 : n ≠ d := by omega
      simp [h1, hn, h2, h4]

/-- $(1 - T^d) \cdot \sum_n T^{dn} = 1$. -/
private lemma geomPow_mul (d : ℕ) (hd : 1 ≤ d) : geomPow d * (1 - X ^ d) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one]
  simp only [geomPow, coeff_mk]
  by_cases h1 : d ≤ n
  · have hn0 : n ≠ 0 := by omega
    have hdiv := dvd_sub_self_iff' h1
    by_cases h2 : d ∣ n
    · simp [h1, hn0, h2, hdiv.2 h2]
    · have h3 : ¬ d ∣ n - d := fun h => h2 (hdiv.1 h)
      simp [h1, hn0, h2, h3]
  · by_cases hn : n = 0
    · subst hn
      simp [h1]
    · have h2 : ¬ d ∣ n := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      simp [h1, hn, h2]

/-- $(1 - T^d)^{-1} = \exp\bigl(\sum_{d \mid m} d\,T^m/m\bigr)$ for $d \ge 1$. -/
theorem geomPow_eq_expSeries (d : ℕ) (hd : 1 ≤ d) : geomPow d = expSeries (divSeries d) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  set Z := expSeries (divSeries (e + 1)) with hZ
  have hode := expSeries_ode (divSeries (e + 1))
  rw [← hZ] at hode
  have hL1 := logDeriv_divSeries_mul (e + 1) hd
  have hXpow : X * d⁄dX ((X : PowerSeries ℚ) ^ (e + 1)) = C ((e + 1 : ℕ) : ℚ) * X ^ (e + 1) := by
    simp [Derivation.leibniz_pow, derivative_X, map_natCast] <;> ring
  have hV : X * d⁄dX (Z * (1 - X ^ (e + 1))) = 0 := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_sub, Derivation.map_one_eq_zero]
    linear_combination (-Z) * hXpow + (1 - X ^ (e + 1)) * hode + Z * hL1
  have hV' : d⁄dX (Z * (1 - X ^ (e + 1))) = 0 := by
    rcases mul_eq_zero.1 hV with h | h
    · exact absurd h X_ne_zero
    · exact h
  have hZ1 : Z * (1 - X ^ (e + 1)) = 1 := by
    refine derivative.ext (by rw [hV', Derivation.map_one_eq_zero]) ?_
    simp [hZ, constantCoeff_expSeries]
  have hne : (1 - (X : PowerSeries ℚ) ^ (e + 1)) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp at this
  exact (mul_right_cancel₀ hne (hZ1.trans (geomPow_mul (e + 1) hd).symm)).symm

/-- The coefficients of $\exp\bigl(\sum a_m T^m/m\bigr)$ up to $T^M$ depend only on $a_1, \dots, a_M$. -/
theorem coeff_expSeries_congr (a b : ℕ → ℚ) (M : ℕ) (h : ∀ m, 1 ≤ m → m ≤ M → a m = b m) (n : ℕ)
    (hn : n ≤ M) : coeff n (expSeries a) = coeff n (expSeries b) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_expSeries]
    | succ k =>
      have e1 := congrArg (coeff (k + 1)) (expSeries_ode a)
      have e2 := congrArg (coeff (k + 1)) (expSeries_ode b)
      rw [coeff_succ_X_mul, coeff_derivative, coeff_mul] at e1 e2
      have hs : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1),
            coeff x.1 (expSeries a) * coeff x.2 (logDerivSeries a) =
          ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1),
            coeff x.1 (expSeries b) * coeff x.2 (logDerivSeries b) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        by_cases h0 : x.2 = 0
        · have : ∀ c : ℕ → ℚ, coeff x.2 (logDerivSeries c) = 0 := fun c => by
            simp [logDerivSeries, h0]
          rw [this, this]; simp
        · have : ∀ c : ℕ → ℚ, coeff x.2 (logDerivSeries c) = c x.2 := fun c => by
            simp [logDerivSeries, h0]
          rw [this, this, ih x.1 (by omega) (by omega), h x.2 (by omega) (by omega)]
      have : coeff (k + 1) (expSeries a) * ((k : ℚ) + 1) =
          coeff (k + 1) (expSeries b) * ((k : ℚ) + 1) := by
        rw [e1, e2]; exact hs
      exact mul_right_cancel₀ (by positivity) this

/-! ### Counting homomorphisms and divisors -/

section Count

variable (R : Type*) [CommRing R] [Algebra (ZMod p) R] [Algebra.FiniteType (ZMod p) R]

/-- The kernel of an algebra map from a ring to a finite field is maximal. -/
private lemma ker_isMaximal' {K : Type*} [Field K] [Algebra (ZMod p) K] [Finite K]
    (φ : R →ₐ[ZMod p] K) : (RingHom.ker (φ : R →+* K)).IsMaximal := by
  haveI : (RingHom.ker (φ : R →+* K)).IsPrime := RingHom.ker_isPrime _
  haveI : Finite (R ⧸ RingHom.ker (φ : R →+* K)) :=
    Finite.of_injective (RingHom.kerLift (φ : R →+* K)) (RingHom.kerLift_injective _)
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

/-- Algebra maps with kernel $\mathfrak p$ are the algebra maps out of the residue field. -/
private noncomputable def fiberEquiv' {K : Type*} [Field K] [Algebra (ZMod p) K]
    (𝔭 : MaximalSpectrum R) :
    {φ : R →ₐ[ZMod p] K // RingHom.ker (φ : R →+* K) = 𝔭.asIdeal} ≃
      (R ⧸ 𝔭.asIdeal →ₐ[ZMod p] K) where
  toFun φ := Ideal.Quotient.liftₐ 𝔭.asIdeal φ.1 (fun a ha => by
    have : a ∈ RingHom.ker (φ.1 : R →+* K) := by rw [φ.2]; exact ha
    exact RingHom.mem_ker.1 this)
  invFun ψ := ⟨ψ.comp (Ideal.Quotient.mkₐ (ZMod p) 𝔭.asIdeal), by
    haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
    letI : Field (R ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
    have hinj : Function.Injective ψ := (ψ : R ⧸ 𝔭.asIdeal →+* K).injective
    ext x
    rw [RingHom.mem_ker]
    show ψ (Ideal.Quotient.mk 𝔭.asIdeal x) = 0 ↔ x ∈ 𝔭.asIdeal
    rw [map_eq_zero_iff ψ hinj, Ideal.Quotient.eq_zero_iff_mem]⟩
  left_inv φ := Subtype.ext (AlgHom.ext fun x => rfl)
  right_inv ψ := Ideal.Quotient.algHom_ext (ZMod p) (AlgHom.ext fun x => rfl)

/-- The number of algebra maps with kernel $\mathfrak p$ to $\mathbb F_{p^k}$. -/
private lemma card_fiber' (k : ℕ) [NeZero k] (𝔭 : MaximalSpectrum R) :
    Nat.card {φ : R →ₐ[ZMod p] GaloisField p k //
      RingHom.ker (φ : R →+* GaloisField p k) = 𝔭.asIdeal} =
      if maxDeg (p := p) R 𝔭 ∣ k then maxDeg (p := p) R 𝔭 else 0 := by
  rw [Nat.card_congr (fiberEquiv' (p := p) R 𝔭)]
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  letI : Field (R ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  haveI : Module.Finite (ZMod p) (R ⧸ 𝔭.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing (ZMod p) (R ⧸ 𝔭.asIdeal)
  have hk : Module.finrank (ZMod p) (GaloisField p k) = k := GaloisField.finrank p (NeZero.ne k)
  split_ifs with h
  · have h' : Module.finrank (ZMod p) (R ⧸ 𝔭.asIdeal) ∣ Module.finrank (ZMod p) (GaloisField p k) := by
      rw [hk]; exact h
    exact FiniteField.natCard_algHom_of_finrank_dvd (F := ZMod p) (K := R ⧸ 𝔭.asIdeal)
      (L := GaloisField p k) h'
  · have hne : IsEmpty (R ⧸ 𝔭.asIdeal →ₐ[ZMod p] GaloisField p k) := by
      rw [← not_nonempty_iff]
      intro hne
      have := (FiniteField.nonempty_algHom_iff_finrank_dvd (F := ZMod p) (K := R ⧸ 𝔭.asIdeal)
        (L := GaloisField p k)).1 hne
      rw [hk] at this
      exact h this
    exact Nat.card_of_isEmpty

/-- **Counting homomorphisms** (pdf p. 162): for $k \ge 1$,
$N_k = \#\operatorname{Hom}(R, \mathbb F_{p^k}) = \sum_{\deg \mathfrak p \mid k} \deg \mathfrak p$, the sum over any finite
set of maximal ideals containing all those of degree at most $k$. -/
theorem homCount_eq_sum (k : ℕ) (hk : 1 ≤ k) (S : Finset (MaximalSpectrum R))
    (hS : ∀ 𝔭, maxDeg (p := p) R 𝔭 ≤ k → 𝔭 ∈ S) :
    (homCount (p := p) R k : ℚ) = ∑ 𝔭 ∈ S, divSeries (maxDeg (p := p) R 𝔭) k := by
  haveI : NeZero k := ⟨by omega⟩
  haveI := finite_algHom (p := p) R (K := GaloisField p k)
  classical
  let F : (R →ₐ[ZMod p] GaloisField p k) → MaximalSpectrum R := fun φ =>
    ⟨RingHom.ker (φ : R →+* GaloisField p k), ker_isMaximal' (p := p) R φ⟩
  have hmem : ∀ φ, F φ ∈ S := by
    intro φ
    apply hS
    have hc := card_fiber' (p := p) R k (F φ)
    haveI : Nonempty {ψ : R →ₐ[ZMod p] GaloisField p k //
        RingHom.ker (ψ : R →+* GaloisField p k) = (F φ).asIdeal} := ⟨⟨φ, rfl⟩⟩
    have hpos := Nat.card_pos (α := {ψ : R →ₐ[ZMod p] GaloisField p k //
        RingHom.ker (ψ : R →+* GaloisField p k) = (F φ).asIdeal})
    rw [hc] at hpos
    split_ifs at hpos with h
    · exact Nat.le_of_dvd hk h
    · omega
  let F' : (R →ₐ[ZMod p] GaloisField p k) → S := fun φ => ⟨F φ, hmem φ⟩
  have e1 : (R →ₐ[ZMod p] GaloisField p k) ≃ Σ y : S, {φ // F' φ = y} :=
    (Equiv.sigmaFiberEquiv F').symm
  have e2 : ∀ y : S, {φ // F' φ = y} ≃ {φ : R →ₐ[ZMod p] GaloisField p k //
      RingHom.ker (φ : R →+* GaloisField p k) = y.1.asIdeal} := fun y =>
    Equiv.subtypeEquivRight fun φ => ⟨fun h => congrArg (fun z : S => z.1.asIdeal) h,
      fun h => Subtype.ext (MaximalSpectrum.ext h)⟩
  have hfib : ∀ y : S, Nat.card {φ // F' φ = y} =
      if maxDeg (p := p) R y.1 ∣ k then maxDeg (p := p) R y.1 else 0 := fun y =>
    (Nat.card_congr (e2 y)).trans (card_fiber' (p := p) R k y.1)
  unfold homCount
  rw [Nat.card_congr e1, Nat.card_sigma, Finset.sum_congr rfl (fun y _ => hfib y), Nat.cast_sum,
    ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold divSeries
  split_ifs <;> simp

/-- Up to $T^M$, the Euler product is the finite product over any finite set of maximal ideals containing all those
of degree at most $M$. -/
theorem coeff_eulerZeta_eq_prod (M : ℕ) (S : Finset (MaximalSpectrum R))
    (hS : ∀ 𝔭, maxDeg (p := p) R 𝔭 ≤ M → 𝔭 ∈ S) (n : ℕ) (hn : n ≤ M) :
    coeff n (eulerZeta (p := p) R) = coeff n (∏ 𝔭 ∈ S, geomPow (maxDeg (p := p) R 𝔭)) := by
  classical
  have hdeg := one_le_maxDeg (p := p) R
  have hbound : ∀ D : MaximalSpectrum R →₀ ℕ,
      D.sum (fun 𝔭 m => m * maxDeg (p := p) R 𝔭) = n → ∀ 𝔭, D 𝔭 ≠ 0 → 𝔭 ∈ S := by
    intro D hD 𝔭 h𝔭
    apply hS
    have h1 : D 𝔭 * maxDeg (p := p) R 𝔭 ≤ n :=
      le_of_le_of_eq (Finset.single_le_sum (f := fun 𝔮 => D 𝔮 * maxDeg (p := p) R 𝔮)
        (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.2 h𝔭)) hD
    have h2 : maxDeg (p := p) R 𝔭 ≤ D 𝔭 * maxDeg (p := p) R 𝔭 :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h𝔭)
    omega
  have hsub : ∀ D : MaximalSpectrum R →₀ ℕ,
      D.sum (fun 𝔭 m => m * maxDeg (p := p) R 𝔭) = n → D.support ⊆ S :=
    fun D hD 𝔭 h𝔭 => hbound D hD 𝔭 (Finsupp.mem_support_iff.1 h𝔭)
  have hsumS : ∀ D : MaximalSpectrum R →₀ ℕ, D.support ⊆ S →
      D.sum (fun 𝔭 m => m * maxDeg (p := p) R 𝔭) = ∑ 𝔭 ∈ S, D 𝔭 * maxDeg (p := p) R 𝔭 :=
    fun D h => Finsupp.sum_of_support_subset D h _ (fun _ _ => zero_mul _)
  let A := (Finset.finsuppAntidiag S n).filter
    fun l : MaximalSpectrum R →₀ ℕ => ∀ 𝔭 ∈ S, maxDeg (p := p) R 𝔭 ∣ l 𝔭
  have hA : ∀ l, l ∈ A ↔ (S.sum l = n ∧ l.support ⊆ S) ∧ ∀ 𝔭 ∈ S, maxDeg (p := p) R 𝔭 ∣ l 𝔭 :=
    fun l => by simp only [A, Finset.mem_filter, Finset.mem_finsuppAntidiag]
  have hrhs : coeff n (∏ 𝔭 ∈ S, geomPow (maxDeg (p := p) R 𝔭)) = (A.card : ℚ) := by
    rw [PowerSeries.coeff_prod]
    simp only [geomPow, coeff_mk, Finset.prod_boole, Finset.sum_boole]
    rfl
  have hlhs : Nat.card {D : MaximalSpectrum R →₀ ℕ //
      D.sum (fun 𝔭 m => m * maxDeg (p := p) R 𝔭) = n} = A.card := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun D => ⟨Finsupp.onFinset D.1.support (fun 𝔭 => D.1 𝔭 * maxDeg (p := p) R 𝔭)
          (fun 𝔭 h => Finsupp.mem_support_iff.2 (fun h0 => h (by rw [h0, zero_mul]))), ?_⟩
        invFun := fun l => ⟨Finsupp.onFinset l.1.support (fun 𝔭 => l.1 𝔭 / maxDeg (p := p) R 𝔭)
          (fun 𝔭 h => Finsupp.mem_support_iff.2 (fun h0 => h (by rw [h0, Nat.zero_div]))), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [hA]
      refine ⟨⟨?_, Finsupp.support_onFinset_subset.trans (hsub D.1 D.2)⟩, ?_⟩
      · exact (hsumS D.1 (hsub D.1 D.2)).symm.trans D.2
      · intro 𝔭 _
        rw [Finsupp.onFinset_apply]
        exact dvd_mul_left _ _
    · obtain ⟨l, hl⟩ := l
      obtain ⟨⟨hl3, hl4⟩, hl2⟩ := (hA l).1 hl
      have hDsub : (Finsupp.onFinset l.support (fun 𝔭 => l 𝔭 / maxDeg (p := p) R 𝔭)
          (fun 𝔭 h => Finsupp.mem_support_iff.2 (fun h0 => h (by rw [h0, Nat.zero_div])))).support ⊆ S :=
        Finsupp.support_onFinset_subset.trans hl4
      show Finsupp.sum _ _ = n
      rw [hsumS _ hDsub, ← hl3]
      refine Finset.sum_congr rfl fun 𝔭 h𝔭 => ?_
      rw [Finsupp.onFinset_apply]
      exact Nat.div_mul_cancel (hl2 𝔭 h𝔭)
    · intro D
      refine Subtype.ext (Finsupp.ext fun 𝔭 => ?_)
      simp only [Finsupp.onFinset_apply]
      exact Nat.mul_div_cancel _ (Nat.lt_of_lt_of_le Nat.zero_lt_one (hdeg 𝔭))
    · rintro ⟨l, hl⟩
      obtain ⟨⟨hl3, hl4⟩, hl2⟩ := (hA l).1 hl
      refine Subtype.ext (Finsupp.ext fun 𝔭 => ?_)
      simp only [Finsupp.onFinset_apply]
      by_cases h : 𝔭 ∈ S
      · exact Nat.div_mul_cancel (hl2 𝔭 h)
      · have : l 𝔭 = 0 := Finsupp.notMem_support_iff.1 (fun h' => h (hl4 h'))
        rw [this]; simp
  rw [hrhs]
  unfold eulerZeta
  rw [coeff_mk, hlhs]

/-- **Proposition 9.8** (pdf p. 162) for every finitely generated $\mathbb F_p$-algebra $R$:
$\prod_{\mathfrak p} (1 - T^{\deg \mathfrak p})^{-1} = \exp\bigl(\sum_{m \ge 1} N_m T^m/m\bigr)$ with
$N_m = \#\operatorname{Hom}_{\mathbb F_p}(R, \mathbb F_{p^m})$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 9.8, pdf p. 162"]
theorem eulerZeta_eq_expSeries :
    eulerZeta (p := p) R = expSeries fun m => (homCount (p := p) R m : ℚ) := by
  ext n
  have hfin := finite_maxDeg_le (p := p) R n
  let S := hfin.toFinset
  have hS : ∀ 𝔭, maxDeg (p := p) R 𝔭 ≤ n → 𝔭 ∈ S := fun 𝔭 h => hfin.mem_toFinset.2 h
  have hprod : ∏ 𝔭 ∈ S, geomPow (maxDeg (p := p) R 𝔭) =
      ∏ 𝔭 ∈ S, expSeries (divSeries (maxDeg (p := p) R 𝔭)) :=
    Finset.prod_congr rfl fun 𝔭 _ => geomPow_eq_expSeries _ (one_le_maxDeg (p := p) R 𝔭)
  rw [coeff_eulerZeta_eq_prod (p := p) R n S hS n le_rfl, hprod, expSeries_finset_sum]
  refine coeff_expSeries_congr _ _ n (fun m hm1 hmn => ?_) n le_rfl
  exact (homCount_eq_sum (p := p) R m hm1 S (fun 𝔭 h => hS 𝔭 (h.trans hmn))).symm

end Count

/-- **Proposition 9.8** (pdf p. 162): the named statement `Prop9_8` holds. -/
@[kb "milne2006ec" "Ch. IV, Proposition 9.8, pdf p. 162"]
theorem prop9_8 : Prop9_8 p :=
  ⟨fun f _ => by
    haveI : Algebra.FiniteType (ZMod p) (planeCurveRing p f) := by
      haveI : Algebra.FiniteType (ZMod p) (Polynomial (Polynomial (ZMod p))) := inferInstance
      exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (ZMod p) (Ideal.span {f}))
        Ideal.Quotient.mk_surjective
    exact eulerZeta_eq_expSeries (p := p) (planeCurveRing p f)⟩

/-- **Example 9.7** (pdf p. 160), unconditional: $Z(\mathbb A^1, T) = 1/(1 - pT)$. -/
@[kb "milne2006ec" "Ch. IV, Example 9.7, pdf p. 160"]
theorem example_9_7_unconditional :
    eulerZeta (p := p) (planeCurveRing p Polynomial.X) * (1 - C (p : ℚ) * X) = 1 :=
  example_9_7 prop9_8

/-- **Theorem 9.10** (pdf p. 163) by Milne's proof, conditional only on Proposition 9.9 (`Prop9_9`). -/
@[kb "milne2006ec" "Ch. IV, Theorem 9.10, pdf p. 163"]
theorem theorem_9_10_of_prop9_9 (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] (h99 : Prop9_9 W) :
    Theorem9_10 W :=
  theorem_9_10 prop9_8 W h99

end NumberFieldKB.MilneEC
