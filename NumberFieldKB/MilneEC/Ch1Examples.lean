import NumberFieldKB.MilneEC.Ch1Intersection

/-!
# Milne, Elliptic Curves, Chapter I, Section 1: examples of affine plane curves

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §1: irreducible components (p. 14), Examples 1.1,
1.2, Remark 1.4, Examples 1.5, 1.6 (pdf pp. 14–16).  Conventions as in `Ch1Affine`.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC

variable {k : Type*} [Field k]

/-- Evaluation at a point is multiplicative. -/
theorem evalAt_mul {K : Type*} [Field K] [Algebra k K] (f g : MvPolynomial (Fin 2) k) (P : K × K) :
    evalAt (f * g) P = evalAt f P * evalAt g P := by
  simp [evalAt]

/-- The irreducible components (p. 14): for `f ≠ 0`, $C_f(K) = \bigcup C_{f_i}(K)$, the union over
the irreducible factors $f_i$ of `f`. -/
@[kb "milne2006ec" "Ch. I, §1, C_f(K) is the union of its irreducible components, pdf p. 14"]
theorem affinePoints_eq_iUnion_components {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) (K : Type*)
    [Field K] [Algebra k K] :
    affinePoints f K = ⋃ (g : MvPolynomial (Fin 2) k) (_ : IsComponent f g), affinePoints g K := by
  ext P
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro hP
    obtain ⟨s, hs, u, hu⟩ := WfDvdMonoid.exists_factors f hf
    have h0 : evalAt f P = 0 := hP
    rw [← hu] at h0
    have h1 : evalAt s.prod P = 0 := by
      rw [evalAt_mul] at h0
      have : evalAt (u : MvPolynomial (Fin 2) k) P ≠ 0 := by
        intro h
        have h' := evalAt_mul (↑u⁻¹ : MvPolynomial (Fin 2) k) (u : MvPolynomial (Fin 2) k) P
        rw [Units.inv_mul, h, mul_zero] at h'
        simp [evalAt] at h'
      exact (mul_eq_zero.mp h0).resolve_right this
    have h2 : ((s.map (fun g => evalAt g P)).prod) = 0 := by
      rw [← h1]
      unfold evalAt
      rw [map_multiset_prod]
    obtain ⟨g, hg, hz⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h2)
    exact ⟨g, ⟨hs g hg, (Multiset.dvd_prod hg).trans ⟨u, hu.symm⟩⟩, hz⟩
  · rintro ⟨g, ⟨hg, hdvd⟩, hP⟩
    obtain ⟨c, rfl⟩ := hdvd
    have : evalAt g P = 0 := hP
    show evalAt (g * c) P = 0
    rw [evalAt_mul, this, zero_mul]

/-- Mapping along an injective ring homomorphism preserves the total degree. -/
theorem totalDegree_map_of_injective {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hf : Function.Injective f) {σ : Type*} (p : MvPolynomial σ R) :
    (map f p).totalDegree = p.totalDegree := by
  simp [totalDegree, support_map_of_injective p hf]

/-- If the image of a polynomial under a field homomorphism is a unit, so is the polynomial. -/
theorem isUnit_of_isUnit_map {K₁ K₂ : Type*} [Field K₁] [Field K₂] (f : K₁ →+* K₂)
    {h : MvPolynomial (Fin 2) K₁} (hu : IsUnit (map f h)) : IsUnit h := by
  rw [isUnit_iff_totalDegree_of_isReduced] at hu ⊢
  obtain ⟨h1, h2⟩ := hu
  rw [totalDegree_map_of_injective f f.injective] at h2
  refine ⟨?_, h2⟩
  rw [coeff_map] at h1
  rw [isUnit_iff_ne_zero] at h1 ⊢
  intro h0
  apply h1
  rw [h0, map_zero]

/-- A polynomial whose coefficients all lie in the image of `k` is the image of a polynomial over
`k`. -/
theorem exists_map_eq_of_coeff_mem_range {L : Type*} [Field L] [Algebra k L]
    (g : MvPolynomial (Fin 2) L) (h : ∀ d, ∃ y : k, algebraMap k L y = g.coeff d) :
    ∃ g₀ : MvPolynomial (Fin 2) k, map (algebraMap k L) g₀ = g := by
  choose c hc using h
  refine ⟨∑ d ∈ g.support, monomial d (c d), ?_⟩
  rw [map_sum]
  simp only [map_monomial, hc]
  exact g.as_sum.symm

section QuadraticExtension

variable {L : Type*} [Field L] [Algebra k L]

/-- A nontrivial automorphism of a degree two extension has order two. -/
theorem aut_sq_eq_one (hL : Module.finrank k L = 2) (σ : L ≃ₐ[k] L) (hσ : σ ≠ 1) (x : L) :
    σ (σ x) = x := by
  have hfin : FiniteDimensional k L := Module.finite_of_finrank_pos (by omega)
  have hle : Nat.card (L ≃ₐ[k] L) ≤ 2 := by
    have := hL ▸ (AlgEquiv.card_le (F := k) (K := L))
    rwa [← Nat.card_eq_fintype_card] at this
  have hge : 1 < Nat.card (L ≃ₐ[k] L) := by
    have : Finite (L ≃ₐ[k] L) := inferInstance
    exact Finite.one_lt_card_iff_nontrivial.mpr ⟨σ, 1, hσ⟩
  have hcard : Nat.card (L ≃ₐ[k] L) = 2 := le_antisymm hle hge
  have h1 : σ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := L ≃ₐ[k] L) (x := σ)
    rwa [hcard] at this
  have := congrArg (fun τ : L ≃ₐ[k] L => τ x) h1
  simpa [pow_two] using this

/-- An element of a degree two extension fixed by a nontrivial automorphism lies in the base
field. -/
theorem fixed_mem_range (hL : Module.finrank k L = 2) (σ : L ≃ₐ[k] L) (hσ : σ ≠ 1) {x : L}
    (hx : σ x = x) : ∃ y : k, algebraMap k L y = x := by
  by_contra hne
  push Not at hne
  have hfin : FiniteDimensional k L := Module.finite_of_finrank_pos (by omega)
  have hli : LinearIndependent k ![(1 : L), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 : algebraMap k L s + algebraMap k L t * x = 0 := by
      simpa [Algebra.smul_def] using hst
    by_cases ht : t = 0
    · subst ht
      simp at h0
      exact ⟨h0, rfl⟩
    · exfalso
      apply hne (-s / t)
      have htL : algebraMap k L t ≠ 0 := by simpa using ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -h0
  let hb := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hL])
  have hid : σ.toLinearMap = LinearMap.id := by
    apply hb.ext
    intro i
    fin_cases i <;> simp [hb, hx]
  apply hσ
  ext y
  have := LinearMap.congr_fun hid y
  simpa using this

/-- Hilbert's Theorem 90 for a degree two extension: an element of norm one is a quotient
`d / σ d`. -/
theorem exists_div_of_norm_one (σ : L ≃ₐ[k] L) (hσ : σ ≠ 1) (hsq : ∀ x, σ (σ x) = x) (r : L)
    (hr : r * σ r = 1) : ∃ d : L, d ≠ 0 ∧ σ d * r = d := by
  by_cases h : 1 + r = 0
  · have hr1 : r = -1 := by linear_combination h
    have : ∃ θ : L, σ θ ≠ θ := by
      by_contra hcon
      push Not at hcon
      exact hσ (AlgEquiv.ext hcon)
    obtain ⟨θ, hθ⟩ := this
    refine ⟨θ - σ θ, sub_ne_zero.mpr (Ne.symm hθ), ?_⟩
    rw [map_sub, hsq, hr1]
    ring
  · refine ⟨1 + r, h, ?_⟩
    have : σ r = r⁻¹ := by
      have hr0 : r ≠ 0 := by
        rintro rfl
        simp at hr
      field_simp
      linear_combination hr
    rw [map_add, map_one, this]
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    field_simp
    ring

end QuadraticExtension

/-- **Example 1.1** (p. 14), in general form: let `L/k` be an extension of degree 2 with nontrivial
automorphism `σ` (Milne: $L = \mathbb Q[\sqrt 2]$, $k = \mathbb Q$), and let $f_1 \in L[X, Y]$ be
irreducible with no constant multiple in $k[X, Y]$.  Then $f = f_1 \bar f_1$ lies in $k[X, Y]$, and the
curve $C_f$ is irreducible but not geometrically irreducible. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.1, pdf p. 14"]
theorem example_1_1 {L : Type*} [Field L] [Algebra k L] (hL : Module.finrank k L = 2)
    (σ : L ≃ₐ[k] L) (hσ : σ ≠ 1) (f₁ : MvPolynomial (Fin 2) L) (hirr : Irreducible f₁)
    (hnot : ∀ c : L, c ≠ 0 → C c * f₁ ∉ Set.range (map (algebraMap k L))) :
    ∃ f : MvPolynomial (Fin 2) k, map (algebraMap k L) f = f₁ * map (σ : L →+* L) f₁ ∧
      IsIrreducibleCurve f ∧ ¬ IsGeometricallyIrreducible f := by
  have hfin : FiniteDimensional k L := Module.finite_of_finrank_pos (by omega)
  have hsq := aut_sq_eq_one hL σ hσ
  set σr : L →+* L := (σ : L →+* L) with hσr
  have hσσ : σr.comp σr = RingHom.id L := by
    ext x; exact hsq x
  have hσk : σr.comp (algebraMap k L) = algebraMap k L := by
    ext y; exact σ.commutes y
  have hmm : ∀ g : MvPolynomial (Fin 2) L, map σr (map σr g) = g := by
    intro g; rw [map_map, hσσ, map_id]
  have hfix : ∀ g₀ : MvPolynomial (Fin 2) k,
      map σr (map (algebraMap k L) g₀) = map (algebraMap k L) g₀ := by
    intro g₀; rw [map_map, hσk]
  have hcoef : ∀ g : MvPolynomial (Fin 2) L, map σr g = g → ∃ g₀ : MvPolynomial (Fin 2) k,
      map (algebraMap k L) g₀ = g := by
    intro g hg
    apply exists_map_eq_of_coeff_mem_range
    intro d
    have := congrArg (fun p : MvPolynomial (Fin 2) L => p.coeff d) hg
    simp only [coeff_map] at this
    exact fixed_mem_range hL σ hσ this
  have hirr' : Irreducible (map σr f₁) :=
    (MulEquiv.irreducible_iff (mapEquiv (Fin 2) σ.toRingEquiv).toMulEquiv).mpr hirr
  have hf₁0 : f₁ ≠ 0 := hirr.ne_zero
  have hF0 : f₁ * map σr f₁ ≠ 0 := mul_ne_zero hf₁0 hirr'.ne_zero
  -- the two factors are not associated
  have hna : ¬ Associated f₁ (map σr f₁) := by
    rintro ⟨u, hu⟩
    obtain ⟨r, hr, hur⟩ := (isUnit_iff_eq_C_of_isReduced).mp u.isUnit
    rw [hur] at hu
    have hr0 : r ≠ 0 := hr.ne_zero
    have h1 := congrArg (map σr) hu
    rw [map_mul, map_C, hmm] at h1
    have h2 : f₁ * C (r * σ r) = f₁ * 1 := by
      calc f₁ * C (r * σ r) = f₁ * C r * C (σr r) := by rw [C_mul, mul_assoc]; rfl
        _ = map σr f₁ * C (σr r) := by rw [hu]
        _ = f₁ * 1 := by rw [h1, mul_one]
    have h3 : r * σ r = 1 := by
      have := mul_left_cancel₀ hf₁0 h2
      rw [← map_one C] at this
      exact C_injective _ _ this
    obtain ⟨d, hd0, hd⟩ := exists_div_of_norm_one σ hσ hsq r h3
    have hg : map σr (C d * f₁) = C d * f₁ := by
      rw [map_mul, map_C, ← hu, mul_left_comm, ← C_mul]
      have : σr d * r = d := hd
      rw [this]
      exact mul_comm _ _
    obtain ⟨g₀, hg₀⟩ := hcoef _ hg
    exact hnot d hd0 ⟨g₀, hg₀⟩
  -- the polynomial `f`
  have hFinv : map σr (f₁ * map σr f₁) = f₁ * map σr f₁ := by
    rw [map_mul, hmm, mul_comm]
  obtain ⟨f₀, hf₀⟩ := hcoef _ hFinv
  have hrel : IsRelPrime f₁ (map σr f₁) :=
    hirr.isRelPrime_iff_not_dvd.mpr fun hd => hna (hirr.associated_of_dvd hirr' hd)
  refine ⟨f₀, hf₀, ?_, ?_⟩
  · -- irreducibility over `k`
    have claim : ∀ a b : MvPolynomial (Fin 2) k, f₀ = a * b →
        f₁ ∣ map (algebraMap k L) a → IsUnit b := by
      intro a b hab hdvd
      obtain ⟨m, hm⟩ := hdvd
      have hdvd2 : map σr f₁ ∣ map (algebraMap k L) a := by
        refine ⟨map σr m, ?_⟩
        rw [← map_mul, ← hm, hfix]
      obtain ⟨m', hm'⟩ := hrel.mul_dvd ⟨m, hm⟩ hdvd2
      have h4 : f₁ * map σr f₁ = (f₁ * map σr f₁) * (m' * map (algebraMap k L) b) := by
        calc f₁ * map σr f₁ = map (algebraMap k L) f₀ := hf₀.symm
          _ = map (algebraMap k L) a * map (algebraMap k L) b := by rw [hab, map_mul]
          _ = _ := by rw [hm']; ring
      have h5 : m' * map (algebraMap k L) b = 1 := by
        have := mul_left_cancel₀ hF0 (h4.symm.trans (mul_one _).symm)
        exact this
      exact isUnit_of_isUnit_map (algebraMap k L)
        (IsUnit.of_mul_eq_one m' (by rw [mul_comm]; exact h5))
    refine ⟨?_, fun a b hab => ?_⟩
    · intro hu
      have hF : IsUnit (f₁ * map σr f₁) := by
        rw [← hf₀]
        exact hu.map (map (algebraMap k L))
      exact hirr.not_isUnit (isUnit_of_mul_isUnit_left hF)
    · have hprod : f₁ ∣ map (algebraMap k L) a * map (algebraMap k L) b :=
        ⟨map σr f₁, by rw [← map_mul, ← hab, hf₀]⟩
      rcases hirr.prime.dvd_or_dvd hprod with h | h
      · exact Or.inr (claim a b hab h)
      · exact Or.inl (claim b a (by rw [hab, mul_comm]) h)
  · intro hg
    have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
    let τ : L →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
    have hbase : baseChange (AlgebraicClosure k) f₀ =
        map (τ : L →+* AlgebraicClosure k) f₁ * map ((τ : L →+* AlgebraicClosure k).comp σr) f₁ := by
      have h1 : baseChange (AlgebraicClosure k) f₀ =
          map (τ : L →+* AlgebraicClosure k) (map (algebraMap k L) f₀) := by
        rw [map_map, AlgHom.comp_algebraMap]
      rw [h1, hf₀, map_mul, map_map]
    rcases hg.isUnit_or_isUnit hbase with h | h
    · exact hirr.not_isUnit (isUnit_of_isUnit_map _ h)
    · exact hirr.not_isUnit (isUnit_of_isUnit_map _ h)

/-- The polynomial $X^p - cY^p$ is irreducible over `k` when `p` is prime and `c` is not a `p`-th
power in `k` (specialise `Y = 1` and use that the polynomial is monic in `X`). -/
theorem irreducible_pow_sub {p : ℕ} (hp : p.Prime) (c : k) (hc : ∀ b : k, b ^ p ≠ c) :
    Irreducible (X 0 ^ p - C c * X 1 ^ p : MvPolynomial (Fin 2) k) := by
  have h : finSuccEquiv k 1 (X 0 ^ p - C c * X 1 ^ p : MvPolynomial (Fin 2) k) =
      Polynomial.X ^ p - Polynomial.C (C c * X 0 ^ p) := by
    have h1 : (X 1 : MvPolynomial (Fin 2) k) = X (Fin.succ 0) := rfl
    have hC : finSuccEquiv k 1 (C c : MvPolynomial (Fin 2) k) = Polynomial.C (C c) := by
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
      rfl
    simp [h1, finSuccEquiv_X_zero, finSuccEquiv_X_succ, hC]
  have hmon : (Polynomial.X ^ p - Polynomial.C (C c * X 0 ^ p) :
      Polynomial (MvPolynomial (Fin 1) k)).Monic :=
    Polynomial.monic_X_pow_sub_C _ hp.ne_zero
  have hirr : Irreducible ((Polynomial.X ^ p - Polynomial.C (C c * X 0 ^ p) :
      Polynomial (MvPolynomial (Fin 1) k)).map (MvPolynomial.eval (fun _ => (1 : k)))) := by
    have : ((Polynomial.X ^ p - Polynomial.C (C c * X 0 ^ p) :
        Polynomial (MvPolynomial (Fin 1) k)).map (MvPolynomial.eval (fun _ => (1 : k)))) =
        Polynomial.X ^ p - Polynomial.C c := by
      simp
    rw [this]
    exact X_pow_sub_C_irreducible_of_prime hp hc
  have := hmon.irreducible_of_irreducible_map _ _ hirr
  rw [← h] at this
  exact (MulEquiv.irreducible_iff (finSuccEquiv k 1).toMulEquiv).mp this

/-- A linear form `X + αY` vanishing at a point is not a unit. -/
theorem not_isUnit_of_eval_eq_zero {K : Type*} [Field K] {g : MvPolynomial (Fin 2) K} (x : Fin 2 → K)
    (hx : eval x g = 0) : ¬ IsUnit g := by
  intro h
  have := (h.map (eval x)).ne_zero
  exact this hx

/-- **Example 1.1** (p. 14), the instance: the curve $X^2 - 2Y^2 = 0$ is irreducible over
$\mathbb Q$ but not geometrically irreducible (it is the pair of lines $(X - \sqrt2 Y)(X + \sqrt 2 Y)$). -/
@[kb "milne2006ec" "Ch. I, Ex. 1.1, pdf p. 14"]
theorem example_1_1_X_sq_sub_two_Y_sq :
    IsIrreducibleCurve (X 0 ^ 2 - 2 * X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) ∧
      ¬ IsGeometricallyIrreducible (X 0 ^ 2 - 2 * X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) := by
  have e : (X 0 ^ 2 - 2 * X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) = X 0 ^ 2 - C 2 * X 1 ^ 2 := by
    rw [map_ofNat]
  rw [e]
  refine ⟨irreducible_pow_sub Nat.prime_two 2 ?_, ?_⟩
  · intro b hb
    apply irrational_sqrt_two
    refine ⟨|b|, ?_⟩
    have h' : (b : ℝ) ^ 2 = 2 := by exact_mod_cast hb
    push_cast
    rw [← h', Real.sqrt_sq_eq_abs]
  · intro hirr
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (2 : AlgebraicClosure ℚ) (by norm_num : 0 < 2)
    have hfac : baseChange (AlgebraicClosure ℚ) (X 0 ^ 2 - C 2 * X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) =
        (X 0 - C α * X 1) * (X 0 + C α * X 1) := by
      simp only [baseChange, map_sub, map_pow, map_mul, map_X, map_C]
      have : (algebraMap ℚ (AlgebraicClosure ℚ)) 2 = α ^ 2 := by rw [hα]; simp
      rw [this, map_pow]
      ring
    have := hirr.isUnit_or_isUnit (a := (X 0 - C α * X 1)) (b := (X 0 + C α * X 1)) hfac
    rcases this with h | h
    · exact not_isUnit_of_eval_eq_zero (![α, 1] : Fin 2 → AlgebraicClosure ℚ) (by simp) h
    · exact not_isUnit_of_eval_eq_zero (![-α, 1] : Fin 2 → AlgebraicClosure ℚ) (by simp) h

/-- **Example 1.2** (p. 14): let `k` have characteristic `p ≠ 0` and let `a ∈ k` not be a `p`-th power.
Then $f = X^p + aY^p$ is irreducible in `k[X, Y]`, but over $k^{\mathrm{al}}$ it equals $(X + \alpha Y)^p$
with $\alpha^p = a$; so `f` does not define an affine plane curve. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.2, pdf p. 14"]
theorem example_1_2 (p : ℕ) [Fact p.Prime] [CharP k p] (a : k) (ha : ∀ b : k, b ^ p ≠ a) :
    Irreducible (X 0 ^ p + C a * X 1 ^ p : MvPolynomial (Fin 2) k) ∧
    (∀ α : AlgebraicClosure k, α ^ p = algebraMap k _ a →
      baseChange (AlgebraicClosure k) (X 0 ^ p + C a * X 1 ^ p : MvPolynomial (Fin 2) k) =
        (X 0 + C α * X 1) ^ p) ∧
    ¬ IsAffinePlaneCurve (X 0 ^ p + C a * X 1 ^ p : MvPolynomial (Fin 2) k) := by
  have hcharp : CharP (AlgebraicClosure k) p :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  have key : ∀ α : AlgebraicClosure k, α ^ p = algebraMap k _ a →
      baseChange (AlgebraicClosure k) (X 0 ^ p + C a * X 1 ^ p : MvPolynomial (Fin 2) k) =
        (X 0 + C α * X 1) ^ p := by
    intro α hα
    rw [add_pow_char, mul_pow, ← C_pow, hα]
    simp [baseChange]
  refine ⟨?_, key, ?_⟩
  · have e : (X 0 ^ p + C a * X 1 ^ p : MvPolynomial (Fin 2) k) = X 0 ^ p - C (-a) * X 1 ^ p := by
      rw [map_neg]; ring
    rw [e]
    refine irreducible_pow_sub (Fact.out : p.Prime) (-a) fun b hb => ha (-b) ?_
    rw [neg_pow, neg_one_pow_char, hb]
    ring
  · rintro ⟨-, hsq⟩
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k (AlgebraicClosure k) a)
      (Fact.out : p.Prime).pos
    rw [key α hα] at hsq
    have hdvd : (X 0 + C α * X 1 : MvPolynomial (Fin 2) (AlgebraicClosure k)) *
        (X 0 + C α * X 1) ∣ (X 0 + C α * X 1) ^ p := by
      rw [← sq]
      exact pow_dvd_pow _ (Fact.out : p.Prime).two_le
    exact not_isUnit_of_eval_eq_zero (![-α, 1] : Fin 2 → AlgebraicClosure k) (by simp) (hsq _ hdvd)

/-- **Remark 1.4** (p. 15): a point on two components of a curve is singular: if `P` lies on $C_{f_1}$
and on $C_{f_2}$, then `P` is a singular point of $C_{f_1 f_2}$. -/
@[kb "milne2006ec" "Ch. I, Rem. 1.4, pdf p. 15"]
theorem remark_1_4 (f₁ f₂ : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K]
    {P : K × K} (h₁ : P ∈ affinePoints f₁ K) (h₂ : P ∈ affinePoints f₂ K) :
    IsSingularPoint (f₁ * f₂) P := by
  simp only [affinePoints, Set.mem_ofPred_eq] at h₁ h₂
  refine ⟨?_, ?_, ?_⟩
  · simp [affinePoints, evalAt_mul, h₁]
  · simp [dX, evalAt, Derivation.leibniz] at *
    simp [h₁, h₂]
  · simp [dY, evalAt, Derivation.leibniz] at *
    simp [h₁, h₂]

/-- The polynomial $Y^2 - (X^3 + aX + b)$ of the curve $Y^2 = X^3 + aX + b$. -/
noncomputable def shortWeierstrass (a b : k) : MvPolynomial (Fin 2) k :=
  X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 + C b)

/-- The cubic $X^3 + aX + b$ as a one-variable polynomial. -/
noncomputable def shortCubic (a b : k) : Polynomial k :=
  Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b

/-- Singular points of a short Weierstrass equation, in terms of the coordinates. -/
theorem isSingularPoint_shortWeierstrass_iff (a b : k) {K : Type*} [Field K] [Algebra k K]
    (P : K × K) :
    IsSingularPoint (shortWeierstrass a b) P ↔
      P.2 ^ 2 = P.1 ^ 3 + algebraMap k K a * P.1 + algebraMap k K b ∧
      3 * P.1 ^ 2 + algebraMap k K a = 0 ∧ 2 * P.2 = 0 := by
  simp only [IsSingularPoint, shortWeierstrass, affinePoints, Set.mem_ofPred_eq, evalAt, dX, dY]
  simp
  rw [sub_eq_zero]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  constructor <;> intro h <;> linear_combination (-1 : K) * h

/-- Common roots of the cubic and its derivative are the multiple roots. -/
theorem sq_dvd_shortCubic_iff (a b : k) {K : Type*} [Field K] [Algebra k K] (α : K) :
    (Polynomial.X - Polynomial.C α) ^ 2 ∣ (shortCubic a b).map (algebraMap k K) ↔
      α ^ 3 + algebraMap k K a * α + algebraMap k K b = 0 ∧
        3 * α ^ 2 + algebraMap k K a = 0 := by
  have hmonic : (shortCubic a b).Monic := by
    unfold shortCubic
    monicity!
  have hne : (shortCubic a b).map (algebraMap k K) ≠ 0 := (hmonic.map _).ne_zero
  rw [← Polynomial.le_rootMultiplicity_iff hne]
  have := Polynomial.one_lt_rootMultiplicity_iff_isRoot (t := α) hne
  rw [show (2 ≤ Polynomial.rootMultiplicity α ((shortCubic a b).map (algebraMap k K))) ↔
    (1 < Polynomial.rootMultiplicity α ((shortCubic a b).map (algebraMap k K))) from Iff.rfl, this]
  simp [shortCubic]
  intro _
  norm_num

/-- Existence of a common root of the cubic and its derivative when `4a^3 + 27b^2 = 0`. -/
theorem exists_common_root {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (a b : Ω) (h2 : (2 : Ω) ≠ 0)
    (h : 4 * a ^ 3 + 27 * b ^ 2 = 0) : ∃ α : Ω, α ^ 3 + a * α + b = 0 ∧ 3 * α ^ 2 + a = 0 := by
  by_cases ha : a = 0
  · subst ha
    by_cases hb : b = 0
    · exact ⟨0, by simp [hb], by simp⟩
    · have h27 : (27 : Ω) = 0 := by
        have : (27 : Ω) * b ^ 2 = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero 2 hb)
      have h3 : (3 : Ω) = 0 := by
        have : (3 : Ω) ^ 3 = 0 := by norm_num; exact h27
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (-b) (by norm_num : 0 < 3)
      exact ⟨α, by linear_combination hα, by simp [h3]⟩
  · have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
    set α : Ω := -3 * b / (2 * a) with hαdef
    have hα'' : 2 * a * α + 3 * b = 0 := by
      rw [hαdef]; field_simp; ring
    have hs : 3 * α ^ 2 + a = 0 := by
      have : 4 * a ^ 2 * (3 * α ^ 2 + a) = 0 := by
        linear_combination h + 3 * (2 * a * α - 3 * b) * hα''
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by
      have : (4 : Ω) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2) (pow_ne_zero 2 ha))
    refine ⟨α, ?_, hs⟩
    have : 8 * a ^ 3 * (α ^ 3 + a * α + b) = 0 := by
      linear_combination (-b) * h +
        ((2 * a * α) ^ 2 - 3 * b * (2 * a * α) + 9 * b ^ 2 + 4 * a ^ 3) * hα''
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by
      have : (8 : Ω) = 2 ^ 3 := by norm_num
      rw [this]; exact pow_ne_zero 3 h2) (pow_ne_zero 3 ha))

/-- **Example 1.5** (p. 15), characteristic not 2: the curve $Y^2 = X^3 + aX + b$ is nonsingular if and
only if $X^3 + aX + b$ has no multiple root in $k^{\mathrm{al}}$, if and only if $4a^3 + 27b^2 \neq 0$. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.5, pdf p. 15"]
theorem example_1_5 (hk : ringChar k ≠ 2) (a b : k) :
    (IsNonsingularCurve (shortWeierstrass a b) ↔
      ∀ α : AlgebraicClosure k, ¬ (Polynomial.X - Polynomial.C α) ^ 2 ∣
        (shortCubic a b).map (algebraMap k (AlgebraicClosure k))) ∧
    (IsNonsingularCurve (shortWeierstrass a b) ↔ 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) := by
  have h2 : (2 : AlgebraicClosure k) ≠ 0 := by
    have := Ring.two_ne_zero hk
    intro h
    apply this
    apply (algebraMap k (AlgebraicClosure k)).injective
    rw [map_ofNat, map_zero]
    exact h
  have key : IsNonsingularCurve (shortWeierstrass a b) ↔ ∀ α : AlgebraicClosure k,
      ¬ (α ^ 3 + algebraMap k _ a * α + algebraMap k _ b = 0 ∧
        3 * α ^ 2 + algebraMap k _ a = 0) := by
    constructor
    · rintro h α ⟨h1, h2'⟩
      have hP : ((α, 0) : AlgebraicClosure k × AlgebraicClosure k) ∈
          affinePoints (shortWeierstrass a b) (AlgebraicClosure k) := by
        simp [affinePoints, evalAt, shortWeierstrass]
        linear_combination (-1 : AlgebraicClosure k) * h1
      have hsing : IsSingularPoint (shortWeierstrass a b)
          ((α, 0) : AlgebraicClosure k × AlgebraicClosure k) := by
        rw [isSingularPoint_shortWeierstrass_iff]
        refine ⟨?_, h2', by simp⟩
        simp
        linear_combination (-1 : AlgebraicClosure k) * h1
      exact (isSingularPoint_iff_not_nonsingular _ hP).mp hsing (h _ hP)
    · intro h P hP
      by_contra hns
      have hsing := (isSingularPoint_iff_not_nonsingular _ hP).mpr hns
      rw [isSingularPoint_shortWeierstrass_iff] at hsing
      obtain ⟨e1, e2, e3⟩ := hsing
      have hy : P.2 = 0 := (mul_eq_zero.mp e3).resolve_left h2
      apply h P.1
      refine ⟨?_, e2⟩
      rw [hy] at e1
      linear_combination (-1 : AlgebraicClosure k) * e1
  refine ⟨key.trans (forall_congr' fun α => not_congr (sq_dvd_shortCubic_iff a b α).symm), ?_⟩
  rw [key]
  constructor
  · intro h hzero
    have : (4 : AlgebraicClosure k) * (algebraMap k _ a) ^ 3 + 27 * (algebraMap k _ b) ^ 2 = 0 := by
      have := congrArg (algebraMap k (AlgebraicClosure k)) hzero
      simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at this
      exact this
    obtain ⟨α, hα⟩ := exists_common_root _ _ h2 this
    exact h α hα
  · rintro h α ⟨h1, h2'⟩
    apply h
    apply (algebraMap k (AlgebraicClosure k)).injective
    simp only [map_add, map_mul, map_pow, map_ofNat, map_zero]
    linear_combination (4 * (algebraMap k _ a) ^ 2 + 3 * α * (2 * (algebraMap k _ a) * α - 3 * algebraMap k _ b)) * h2' - 9 * (2 * (algebraMap k _ a) * α - 3 * algebraMap k _ b) * h1

/-- **Example 1.5**, footnote 3 (p. 15): $4a^3 + 27b^2$ is the negative of the discriminant of
$X^3 + aX + b$ in the usual normalization (Mathlib's `Polynomial.discr`). -/
@[kb "milne2006ec" "Ch. I, Ex. 1.5, footnote 3, pdf p. 15"]
theorem example_1_5_discr (a b : k) : (shortCubic a b).discr = -(4 * a ^ 3 + 27 * b ^ 2) := by
  have h : (shortCubic a b).degree = 3 := by
    unfold shortCubic
    compute_degree!
  rw [Polynomial.discr_of_degree_eq_three h]
  have c3 : (shortCubic a b).coeff 3 = 1 := by simp [shortCubic]
  have c2 : (shortCubic a b).coeff 2 = 0 := by simp [shortCubic]
  have c1 : (shortCubic a b).coeff 1 = a := by simp [shortCubic]
  have c0 : (shortCubic a b).coeff 0 = b := by simp [shortCubic]
  rw [c3, c2, c1, c0]
  ring

/-- **Example 1.5** (p. 15), characteristic 2: the curve $Y^2 = X^3 + aX + b$ always has a singular
point in $k^{\mathrm{al}}$, namely $(\alpha, \beta)$ with $3\alpha^2 + a = 0$ and
$\beta^2 = \alpha^3 + a\alpha + b$. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.5, characteristic 2, pdf p. 15"]
theorem example_1_5_char_two [CharP k 2] (a b : k) :
    ∃ P : AlgebraicClosure k × AlgebraicClosure k, IsSingularPoint (shortWeierstrass a b) P ∧
      3 * P.1 ^ 2 + algebraMap k _ a = 0 ∧
      P.2 ^ 2 = P.1 ^ 3 + algebraMap k _ a * P.1 + algebraMap k _ b := by
  have : CharP (AlgebraicClosure k) 2 :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective 2
  have h2 : (2 : AlgebraicClosure k) = 0 := CharP.cast_eq_zero _ 2
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k (AlgebraicClosure k) a)
    (by norm_num : 0 < 2)
  have hα3 : 3 * α ^ 2 + algebraMap k (AlgebraicClosure k) a = 0 := by
    linear_combination 3 * hα + 2 * algebraMap k (AlgebraicClosure k) a * h2
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq
    (α ^ 3 + algebraMap k (AlgebraicClosure k) a * α + algebraMap k (AlgebraicClosure k) b)
    (by norm_num : 0 < 2)
  refine ⟨(α, β), ?_, hα3, hβ⟩
  rw [isSingularPoint_shortWeierstrass_iff]
  exact ⟨hβ, hα3, by simp [h2]⟩

/-- The translate of a polynomial to the origin is the polynomial itself. -/
theorem translate_origin (f : MvPolynomial (Fin 2) k) : translate f ((0, 0) : k × k) = f := by
  unfold translate
  have : (![X 0 + C (((0, 0) : k × k).1), X 1 + C (((0, 0) : k × k).2)] :
      Fin 2 → MvPolynomial (Fin 2) k) = X := by
    ext i; fin_cases i <;> simp
  rw [this]
  exact aeval_X_left_apply f

/-- Homogeneous components of the nodal cubic polynomial. -/
theorem cusp_homogeneousComponent (a : k) (m : ℕ) :
    homogeneousComponent m (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) =
      if m = 2 then X 1 ^ 2 - C a * X 0 ^ 2 else if m = 3 then -X 0 ^ 3 else 0 := by
  have h2 : (X 1 ^ 2 - C a * X 0 ^ 2 : MvPolynomial (Fin 2) k).IsHomogeneous 2 :=
    (isHomogeneous_X_pow _ _).sub (by
      simpa using (isHomogeneous_C_mul_X_pow a (0 : Fin 2) 2))
  have h3 : (-X 0 ^ 3 : MvPolynomial (Fin 2) k).IsHomogeneous 3 :=
    (isHomogeneous_X_pow _ _).neg
  have e : (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) =
      (X 1 ^ 2 - C a * X 0 ^ 2) + (-X 0 ^ 3) := by ring
  rw [e, map_add, homogeneousComponent_of_mem h2, homogeneousComponent_of_mem h3]
  by_cases hm2 : m = 2
  · subst hm2; simp
  · by_cases hm3 : m = 3
    · subst hm3; simp
    · simp [hm2, hm3]

/-- The order of the polynomial $Y^2 - (X^3 + aX^2)$ is 2. -/
theorem cusp_order (a : k) :
    order (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) = 2 := by
  have hne : X 1 ^ 2 - C a * X 0 ^ 2 ≠ (0 : MvPolynomial (Fin 2) k) := by
    intro h
    have := congrArg (fun p : MvPolynomial (Fin 2) k => p.coeff (Finsupp.single 1 2)) h
    have hs : (Finsupp.single (0 : Fin 2) 2) ≠ Finsupp.single 1 2 := by
      intro h'
      have := congrArg (· 0) h'
      simp at this
    simp [coeff_X_pow, coeff_C_mul, hs] at this
  apply le_antisymm
  · apply Nat.sInf_le
    simp only [Set.mem_ofPred_eq, cusp_homogeneousComponent]
    simpa using hne
  · apply le_csInf ⟨2, by simp only [Set.mem_ofPred_eq, cusp_homogeneousComponent]; simpa using hne⟩
    intro b hb
    by_contra hlt
    apply hb
    rw [cusp_homogeneousComponent]
    have h1 : b ≠ 2 := by omega
    have h2 : b ≠ 3 := by omega
    simp [h1, h2]

/-- The lowest form of $Y^2 - (X^3 + aX^2)$ is $Y^2 - aX^2$. -/
theorem cusp_lowestForm (a : k) :
    lowestForm (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) =
      X 1 ^ 2 - C a * X 0 ^ 2 := by
  unfold lowestForm
  rw [cusp_order, cusp_homogeneousComponent]
  simp

/-- **Example 1.6** (p. 16): the curve $Y^2 = X^3 + aX^2$ has a singular point at the origin, of
multiplicity 2, where the lowest form of `f` is $Y^2 - aX^2$.  If $a \neq 0$ and the characteristic is not 2,
the origin is a node with tangent lines $Y = \pm\alpha X$, $\alpha^2 = a$; the tangent lines are defined
over `k` if and only if `a` is a square in `k`.  (In characteristic 2, $Y^2 - aX^2 = (Y - \alpha X)^2$ and the
origin is not a node: Milne's statement needs the characteristic not 2.)
The case $a = 0$ is the cusp of Example 1.12 (`example_1_12_isCusp`). -/
@[kb "milne2006ec" "Ch. I, Ex. 1.6, pdf p. 16"]
theorem example_1_6 (a : k) :
    IsSingularPoint (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) ((0, 0) : k × k) ∧
    multiplicityAt (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) ((0, 0) : k × k) = 2 ∧
    lowestForm (translate (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k)
      ((0, 0) : k × k)) = X 1 ^ 2 - C a * X 0 ^ 2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [affinePoints, evalAt]
  · simp [dX, evalAt]
  · simp [dY, evalAt]
  · rw [multiplicityAt, translate_origin, cusp_order]
  · rw [translate_origin, cusp_lowestForm]

/-- The exponent vectors of `X 0` and `X 1` are distinct. -/
theorem single_zero_ne_single_one : (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 1 := by
  intro h'
  have := congrArg (· 0) h'
  simp at this

/-- The linear form $Y - cX$ has total degree one. -/
theorem linForm_totalDegree (c : k) : (X 1 - C c * X 0 : MvPolynomial (Fin 2) k).totalDegree = 1 := by
  apply le_antisymm
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)
  · have hs : Finsupp.single (1 : Fin 2) 1 ∈ (X 1 - C c * X 0 : MvPolynomial (Fin 2) k).support := by
      rw [mem_support_iff]
      simp [coeff_C_mul, coeff_X, single_zero_ne_single_one]
    simpa using le_totalDegree hs

/-- The linear form $Y - cX$ is irreducible. -/
theorem linForm_irreducible (c : k) : Irreducible (X 1 - C c * X 0 : MvPolynomial (Fin 2) k) := by
  apply irreducible_of_totalDegree_eq_one (linForm_totalDegree c)
  intro x hx
  have := hx (Finsupp.single 1 1)
  simp [coeff_C_mul, coeff_X, single_zero_ne_single_one] at this
  exact isUnit_iff_ne_zero.mpr this

/-- Two linear forms $Y - cX$ and $Y - dX$ with $c \ne d$ do not divide each other. -/
theorem linForm_not_dvd {c d : k} (h : c ≠ d) :
    ¬ (X 1 - C c * X 0 : MvPolynomial (Fin 2) k) ∣ (X 1 - C d * X 0) := by
  rintro ⟨g, hg⟩
  have := congrArg (MvPolynomial.eval (![1, c] : Fin 2 → k)) hg
  simp at this
  exact h (by linear_combination this)

/-- The linear form $Y - cX$ is homogeneous of degree one. -/
theorem linForm_isHomogeneous (c : k) :
    (X 1 - C c * X 0 : MvPolynomial (Fin 2) k).IsHomogeneous 1 :=
  (isHomogeneous_X _ _).sub (by simpa using isHomogeneous_C_mul_X c (0 : Fin 2))

/-- Factorisation of the lowest form of the nodal cubic over an extension. -/
theorem cusp_lowestForm_factor (a : k) {Ω : Type*} [Field Ω] [Algebra k Ω] {α : Ω}
    (hα : α ^ 2 = algebraMap k Ω a) :
    baseChange Ω (lowestForm (translate (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) :
      MvPolynomial (Fin 2) k) ((0, 0) : k × k))) = (X 1 - C α * X 0) * (X 1 + C α * X 0) := by
  rw [translate_origin, cusp_lowestForm]
  simp only [baseChange, map_sub, map_pow, map_mul, map_X, map_C]
  rw [← hα, map_pow]
  ring

/-- A homogeneous polynomial of degree one in two variables is a linear form. -/
theorem eq_linear_of_isHomogeneous_one {L : MvPolynomial (Fin 2) k} (hL : L.IsHomogeneous 1) :
    L = C (L.coeff (Finsupp.single 0 1)) * X 0 + C (L.coeff (Finsupp.single 1 1)) * X 1 := by
  ext d
  rw [show ∀ p q : MvPolynomial (Fin 2) k, (p + q).coeff d = p.coeff d + q.coeff d from
    fun _ _ => rfl, coeff_C_mul, coeff_C_mul, coeff_X, coeff_X]
  by_cases hd : d.degree = 1
  · have h01 : d 0 + d 1 = 1 := by
      have := hd
      rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
    have : d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 := by
      rcases Nat.lt_or_ge (d 0) 1 with h | h
      · right
        ext i; fin_cases i <;> simp <;> omega
      · left
        ext i; fin_cases i <;> simp <;> omega
    rcases this with rfl | rfl
    · simp [single_zero_ne_single_one.symm]
    · simp [single_zero_ne_single_one]
  · rw [hL.coeff_eq_zero hd]
    have h0 : d ≠ Finsupp.single 0 1 := by
      rintro rfl; apply hd; simp [Finsupp.degree_single]
    have h1 : d ≠ Finsupp.single 1 1 := by
      rintro rfl; apply hd; simp [Finsupp.degree_single]
    simp [h0.symm, h1.symm]

/-- The linear form $Y + \alpha X$ is $Y - (-\alpha) X$. -/
theorem linForm_plus {Ω : Type*} [Field Ω] (α : Ω) :
    (X 1 + C α * X 0 : MvPolynomial (Fin 2) Ω) = X 1 - C (-α) * X 0 := by
  rw [map_neg]; ring

/-- Each square root of `a` gives a tangent line $Y = \beta X$ at the origin of $Y^2 = X^3 + aX^2$. -/
theorem cusp_isTangent (a : k) {Ω : Type*} [Field Ω] [Algebra k Ω] {β : Ω}
    (hβ : β ^ 2 = algebraMap k Ω a) :
    IsTangentAt (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) ((0, 0) : k × k)
      (X 1 - C β * X 0) := by
  refine ⟨(linForm_irreducible β).ne_zero, linForm_isHomogeneous β, ?_⟩
  rw [cusp_lowestForm_factor a hβ]
  exact dvd_mul_right _ _

/-- **Example 1.6** (p. 16), the node: for $a \neq 0$ in characteristic not 2, the origin is a node of
$Y^2 = X^3 + aX^2$, the tangent lines are $Y = \pm\alpha X$ with $\alpha^2 = a$ in $k^{\mathrm{al}}$, and
they are defined over `k` if and only if `a` is a square in `k`. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.6, node, pdf p. 16"]
theorem example_1_6_node (hk : ringChar k ≠ 2) {a : k} (ha : a ≠ 0) :
    IsNode (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) ((0, 0) : k × k) ∧
    (∀ α : AlgebraicClosure k, α ^ 2 = algebraMap k _ a →
      IsTangentAt (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) ((0, 0) : k × k)
        (X 1 - C α * X 0) ∧
      IsTangentAt (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) ((0, 0) : k × k)
        (X 1 + C α * X 0)) ∧
    ((∃ c : k, c ^ 2 = a) ↔ ∃ L : MvPolynomial (Fin 2) k,
      IsTangentAt (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) ((0, 0) : k × k) L) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k (AlgebraicClosure k) a)
      (by norm_num : 0 < 2)
    have hα0 : α ≠ 0 := by
      rintro rfl
      exact ha ((algebraMap k (AlgebraicClosure k)).injective (by simpa using hα.symm))
    have h2 : (2 : AlgebraicClosure k) ≠ 0 := by
      have := Ring.two_ne_zero hk
      intro h
      apply this
      apply (algebraMap k (AlgebraicClosure k)).injective
      rw [map_ofNat, map_zero]
      exact h
    obtain ⟨hs, hm, -⟩ := example_1_6 a
    refine ⟨⟨hs, ?_⟩, hm⟩
    rw [cusp_lowestForm_factor a hα, linForm_plus]
    refine squarefree_mul_iff.mpr ⟨(linForm_irreducible α).isRelPrime_iff_not_dvd.mpr
      (linForm_not_dvd ?_), (linForm_irreducible α).squarefree, (linForm_irreducible _).squarefree⟩
    intro h
    apply hα0
    have : (2 : AlgebraicClosure k) * α = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  · intro α hα
    refine ⟨cusp_isTangent a hα, ?_⟩
    rw [linForm_plus]
    exact cusp_isTangent a (by rw [neg_sq]; exact hα)
  · constructor
    · rintro ⟨c, hc⟩
      exact ⟨_, cusp_isTangent a (Ω := k) (β := c) (by simpa using hc)⟩
    · rintro ⟨L, hL0, hLh, hdvd⟩
      simp only [baseChange, Algebra.algebraMap_self, map_id, translate_origin,
        cusp_lowestForm] at hdvd
      obtain ⟨M, hM⟩ := hdvd
      have hlin := eq_linear_of_isHomogeneous_one hLh
      set u := L.coeff (Finsupp.single 0 1) with hu
      set v := L.coeff (Finsupp.single 1 1) with hv
      have hev := congrArg (MvPolynomial.eval (![v, -u] : Fin 2 → k)) hM
      rw [hlin] at hev
      simp at hev
      have huv : u ≠ 0 ∨ v ≠ 0 := by
        by_contra hcon
        simp only [not_or, not_not] at hcon
        apply hL0
        rw [hlin, hcon.1, hcon.2]; simp
      have hv0 : v ≠ 0 := by
        intro h0
        rcases huv with h | h
        · apply h
          rw [h0] at hev
          simpa using hev
        · exact h h0
      refine ⟨u / v, ?_⟩
      field_simp
      linear_combination hev

/-- In characteristic 2 the origin is never a node of $Y^2 = X^3 + aX^2$ (the correction to
Example 1.6). -/
theorem example_1_6_not_node_char_two [CharP k 2] (a : k) :
    ¬ IsNode (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 ^ 2) : MvPolynomial (Fin 2) k) ((0, 0) : k × k) := by
  rintro ⟨⟨-, hsq⟩, -⟩
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k (AlgebraicClosure k) a)
    (by norm_num : 0 < 2)
  have : CharP (AlgebraicClosure k) 2 :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective 2
  rw [cusp_lowestForm_factor a hα, linForm_plus] at hsq
  have hneg : -α = α := CharTwo.neg_eq α
  rw [hneg] at hsq
  exact (linForm_irreducible α).not_isUnit
    ((squarefree_mul_iff.mp hsq).1 dvd_rfl dvd_rfl)

end NumberFieldKB.MilneEC
