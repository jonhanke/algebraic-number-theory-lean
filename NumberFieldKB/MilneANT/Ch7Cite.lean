import NumberFieldKB.MilneANT.Ch7Basic

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: results in Mathlib

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

This file cites the items of Chapter 7 that are available
in Mathlib, following the convention of the Chapter 1–4 citation files:
* when one Mathlib declaration states the book's result in essentially the book's form, the declaration is tagged
  with `attribute [kb "milne2020ant" ...]`, with a comment saying which item it is and how the form differs;
* when the book's form differs, a short restating theorem in the book's form is proved from Mathlib and tagged.
-/

open Filter Topology

namespace NumberFieldKB.MilneANT

/-! ## Absolute values -/

-- Prose definition (p. 105): an absolute value on a field, real valued.
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of an absolute value, p. 105"] AbsoluteValue
-- Prose definition (p. 105): nonarchimedean, `|x + y| ≤ max(|x|, |y|)`.
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of a nonarchimedean absolute value, p. 105"]
  IsNonarchimedean

/-- **Proposition 7.2.** An absolute value $|\cdot|$ on a field $K$ is nonarchimedean iff it takes bounded values on
$\{m \cdot 1 : m \in \mathbb Z\}$. (Mathlib has the normed-field form
`isUltrametricDist_iff_forall_norm_natCast_le_one`, with the bound $1$ on the naturals.) -/
@[kb "milne2020ant" "v3.08, Prop. 7.2, p. 106"]
theorem prop_7_2 {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v ↔ BddAbove (Set.range fun m : ℤ => v m) := by
  constructor
  · intro hna
    refine ⟨1, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact hna.apply_intCast_le_one (by simp) (by simp) (fun a => by simp)
  · rintro ⟨C, hC⟩
    apply isNonarchimedean_of_natCast_le_one
    intro m
    by_contra hm
    replace hm := not_le.mp hm
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hm
    have e : v (((m ^ k : ℕ)) : K) = v (m : K) ^ k := by simp
    have hle : v (((m ^ k : ℕ)) : K) ≤ C := by
      have := hC ⟨((m ^ k : ℕ) : ℤ), rfl⟩
      simpa using this
    linarith

/-- **Proposition 7.8.** Let $|\cdot|_1, |\cdot|_2$ be absolute values on $K$ with $|\cdot|_1$ nontrivial. The
following are equivalent: (a) they define the same topology on $K$ (the identity of $K$ is a homeomorphism between
the two topologies, Mathlib's `WithAbs`); (b) $|\alpha|_1 < 1 \Rightarrow |\alpha|_2 < 1$; (c) $|\cdot|_2 = |\cdot|_1^a$
for some $a > 0$. From Mathlib's `AbsoluteValue.isEquiv_iff_isHomeomorph`, `AbsoluteValue.isEquiv_of_lt_one_imp` and
`AbsoluteValue.isEquiv_iff_exists_rpow_eq`. -/
@[kb "milne2020ant" "v3.08, Prop. 7.8, p. 108"]
theorem prop_7_8 {K : Type*} [Field K] (v₁ v₂ : AbsoluteValue K ℝ) (h₁ : v₁.IsNontrivial) :
    List.TFAE [IsHomeomorph (WithAbs.congr v₁ v₂ (.refl K)),
      ∀ α : K, v₁ α < 1 → v₂ α < 1,
      ∃ a : ℝ, 0 < a ∧ ∀ x : K, v₂ x = v₁ x ^ a] := by
  tfae_have 1 ↔ 3 := by
    rw [← AbsoluteValue.isEquiv_iff_isHomeomorph, AbsoluteValue.isEquiv_iff_exists_rpow_eq]
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨c, hc, fun x => (congrFun h x).symm⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨c, hc, funext fun x => (h x).symm⟩
  tfae_have 1 ↔ 2 := by
    rw [← AbsoluteValue.isEquiv_iff_isHomeomorph]
    exact ⟨fun h α => h.lt_one_iff.1, fun h => AbsoluteValue.isEquiv_of_lt_one_imp h₁ h⟩
  tfae_finish

-- Prose definition (p. 109): equivalent absolute values. Mathlib's `IsEquiv` is order agreement, equivalent to
-- Milne's conditions by Proposition 7.8 (`prop_7_8`).
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of equivalent absolute values, p. 109"]
  AbsoluteValue.IsEquiv
-- Prose definition (p. 108): the p-adic absolute value and the p-adic topology.
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of the p-adic absolute value, p. 105"] padicNorm
-- Prose definition (p. 110): the normalized absolute value on the rationals.
attribute [kb "milne2020ant" "v3.08, Ch. 7, the normalized absolute value on Q, p. 110"] Rat.AbsoluteValue.real

-- Theorem 7.12 (Ostrowski): a nontrivial absolute value on the rationals is equivalent to the real absolute value or
-- to the p-adic one for exactly one prime p. Mathlib states the disjunction without splitting by archimedean.
attribute [kb "milne2020ant" "v3.08, Thm. 7.12, p. 110"] Rat.AbsoluteValue.equiv_real_or_padic

/-- The `p`-adic norm of a nonzero natural number, as a real number. -/
private lemma padicNorm_nat_real (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    (padicNorm p (n : ℚ) : ℝ) = (((p : ℝ) ^ n.factorization p))⁻¹ := by
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat,
    ← Nat.factorization_def n (Fact.out)]
  push_cast
  rw [zpow_neg, zpow_natCast]

/-- Product of `p`-adic norms of a nonzero natural over a finite set of primes containing its prime factors. -/
private lemma prod_padicNorm_nat (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) (hn : n ≠ 0)
    (hsub : n.primeFactors ⊆ s) :
    ∏ p ∈ s, (padicNorm p (n : ℚ) : ℝ) = ((n : ℝ))⁻¹ := by
  have h1 : ∏ p ∈ s, (padicNorm p (n : ℚ) : ℝ) =
      ∏ p ∈ s, (((p : ℝ) ^ n.factorization p))⁻¹ := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have := hs p hp
    have : Fact p.Prime := ⟨this⟩
    rw [padicNorm_nat_real p n hn]
  rw [h1, Finset.prod_inv_distrib]
  congr 1
  have h2 : n.factorization.prod (fun p k => p ^ k) = n := Nat.prod_factorization_pow_eq_self hn
  rw [Finsupp.prod_of_support_subset n.factorization (s := s)
    (by rw [Nat.support_factorization]; exact hsub) (fun p k => p ^ k) (fun _ _ => pow_zero _)] at h2
  exact_mod_cast h2

/-- **Theorem 7.13 (product formula for $\mathbb Q$).** For every nonzero rational number $a$,
$|a|_\infty \cdot \prod_p |a|_p = 1$, the product over all primes being finite. -/
@[kb "milne2020ant" "v3.08, Thm. 7.13, p. 111"]
theorem thm_7_13 (a : ℚ) (ha : a ≠ 0) :
    (Function.mulSupport fun p : Nat.Primes => (padicNorm p a : ℝ)).Finite ∧
      |(a : ℝ)| * ∏ᶠ p : Nat.Primes, (padicNorm p a : ℝ) = 1 := by
  have hnum : a.num.natAbs ≠ 0 := Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 ha)
  have hden : a.den ≠ 0 := a.den_nz
  set N := a.num.natAbs * a.den with hN
  have hN0 : N ≠ 0 := Nat.mul_ne_zero hnum hden
  have hsub1 : a.num.natAbs.primeFactors ⊆ N.primeFactors := Nat.primeFactors_mono (dvd_mul_right _ _) hN0
  have hsub2 : a.den.primeFactors ⊆ N.primeFactors := Nat.primeFactors_mono (dvd_mul_left _ _) hN0
  have habs : |a| = (a.num.natAbs : ℚ) / (a.den : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den a]
    rw [abs_div, Nat.abs_cast, Nat.cast_natAbs, Int.cast_abs]
  have hpn : ∀ p : ℕ, p.Prime → (padicNorm p a : ℝ) =
      (padicNorm p (a.num.natAbs : ℚ) : ℝ) / (padicNorm p (a.den : ℚ) : ℝ) := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    have e : padicNorm p a = padicNorm p (a.num.natAbs : ℚ) / padicNorm p (a.den : ℚ) := by
      rw [← padicNorm.div, ← habs]
      rcases abs_choice a with h | h
      · rw [h]
      · rw [h, padicNorm.neg]
    rw [e]; push_cast; rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset Nat.Primes, T = N.primeFactors.subtype Nat.Prime := ⟨_, rfl⟩
  have hms : (Function.mulSupport fun p : Nat.Primes => (padicNorm p a : ℝ)) ⊆
      (T : Set Nat.Primes) := by
    intro p hp
    rw [Finset.mem_coe, hT]
    refine Finset.mem_subtype.2 ?_
    by_contra hnot
    apply hp
    have h1 : a.num.natAbs.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact fun h => hnot (hsub1 h)
    have h2 : a.den.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact fun h => hnot (hsub2 h)
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    simp only
    rw [hpn p p.2, padicNorm_nat_real p _ hnum, padicNorm_nat_real p _ hden, h1, h2]
    simp
  refine ⟨(Finset.finite_toSet _).subset hms, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hms]
  have e1 := Finset.prod_subtype_eq_prod_filter (s := N.primeFactors) (p := Nat.Prime)
    (fun p : ℕ => (padicNorm p a : ℝ))
  have e2 : (N.primeFactors.filter Nat.Prime) = N.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [e2] at e1
  have e3 : ∏ p ∈ T, (padicNorm (p : ℕ) a : ℝ) =
      ∏ p ∈ N.primeFactors, (padicNorm p a : ℝ) := by rw [hT]; exact e1
  have hpr : ∀ p ∈ N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  show |(a : ℝ)| * ∏ p ∈ T, (padicNorm (p : ℕ) a : ℝ) = 1
  rw [e3, Finset.prod_congr rfl (fun p hp => hpn p (hpr p hp)), Finset.prod_div_distrib,
    prod_padicNorm_nat _ hpr _ hnum hsub1, prod_padicNorm_nat _ hpr _ hden hsub2]
  have : |(a : ℝ)| = (a.num.natAbs : ℝ) / (a.den : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) habs
    simpa using this
  rw [this]
  have h1 : (a.num.natAbs : ℝ) ≠ 0 := by exact_mod_cast hnum
  have h2 : (a.den : ℝ) ≠ 0 := by exact_mod_cast hden
  field_simp

/-! ## Places of a number field -/

-- Prose definitions (p. 112): finite primes (one per nonzero prime ideal) and infinite primes (real embeddings,
-- conjugate pairs of complex embeddings). Milne's primes as classes of absolute values: `MilnePlace` (Ch7Places).
attribute [kb "milne2020ant" "v3.08, Ch. 7, finite primes of a number field, p. 112"] NumberField.FinitePlace
attribute [kb "milne2020ant" "v3.08, Ch. 7, infinite primes of a number field, p. 112"] NumberField.InfinitePlace
-- Prose definition (p. 112): w lies over v (restriction equivalent). Mathlib's `AbsoluteValue.LiesOver` asks for
-- equality of the restriction; Milne's equivalence version is `MilnePlace.LiesOver` (Ch7Places).
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of w dividing v, p. 112"] AbsoluteValue.LiesOver

-- Theorem 7.15 (product formula): Mathlib uses `w(x)^(mult w)` at the infinite places, which is Milne's normalized
-- absolute value (the square of the modulus at a complex place).
attribute [kb "milne2020ant" "v3.08, Thm. 7.15, p. 112"] NumberField.prod_abs_eq_one

/-! ## Weak approximation -/

-- Lemma 7.18.
attribute [kb "milne2020ant" "v3.08, Lemma 7.18, p. 113"] AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
-- Theorem 7.20 (weak approximation): the diagonal image of K is dense in the product of copies of K with the
-- topologies of the absolute values; the number field case for the infinite places separately.
attribute [kb "milne2020ant" "v3.08, Thm. 7.20, p. 114"] AbsoluteValue.denseRange_algebraMap_pi
attribute [kb "milne2020ant" "v3.08, Thm. 7.20, p. 114"] NumberField.InfinitePlace.denseRange_algebraMap_pi

/-! ## Completions -/

-- Prose definitions (p. 114): Cauchy sequences and complete valued fields.
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of a Cauchy sequence, p. 114"] CauchySeq
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of a complete field, p. 114"] CompleteSpace

/-- **Theorem 7.23.** Let $K$ be a field with an absolute value (here: a normed field). The completion $\hat K$ is a
complete valued field with an absolute-value-preserving homomorphism $K \to \hat K$, universal: every homomorphism
$K \to L$ into a complete valued field preserving the absolute value extends uniquely to a homomorphism
$\hat K \to L$ preserving the absolute value. From Mathlib's `UniformSpace.Completion.extensionHom`.

Uniqueness is among absolute-value-preserving homomorphisms (the morphisms of valued fields); among all ring
homomorphisms it fails, e.g. for $K = \mathbb Q(i) \subset \mathbb C = L$ there are discontinuous automorphisms of
$\mathbb C$ fixing $\mathbb Q(i)$. -/
@[kb "milne2020ant" "v3.08, Thm. 7.23, p. 115"]
theorem thm_7_23 (K : Type*) [NormedField K] (L : Type*) [NormedField L] [CompleteSpace L] (f : K →+* L)
    (hf : ∀ x, ‖f x‖ = ‖x‖) :
    ∃! g : UniformSpace.Completion K →+* L, (∀ x : K, g x = f x) ∧ ∀ y, ‖g y‖ = ‖y‖ := by
  have hiso : Isometry f := AddMonoidHomClass.isometry_of_norm f hf
  refine ⟨UniformSpace.Completion.extensionHom f hiso.continuous, ⟨fun x => ?_, fun y => ?_⟩, ?_⟩
  · exact UniformSpace.Completion.extensionHom_coe f hiso.continuous x
  · induction y using UniformSpace.Completion.induction_on with
    | hp =>
      have hc : Continuous (UniformSpace.Completion.extensionHom f hiso.continuous) :=
        UniformSpace.Completion.continuous_extension
      exact isClosed_eq hc.norm continuous_norm
    | ih a =>
      rw [UniformSpace.Completion.extensionHom_coe, UniformSpace.Completion.norm_coe, hf]
  · rintro g ⟨hg, hn⟩
    have hgc : Continuous g := (AddMonoidHomClass.isometry_of_norm g hn).continuous
    refine RingHom.ext fun y => ?_
    refine UniformSpace.Completion.ext' hgc (UniformSpace.Completion.continuous_extension) ?_ y
    intro a
    rw [hg]
    exact (UniformSpace.Completion.extensionHom_coe f hiso.continuous a).symm

-- Remark 7.24(b): the image of K in its completion is dense.
attribute [kb "milne2020ant" "v3.08, Remark 7.24, p. 115"] UniformSpace.Completion.denseRange_coe
-- Prose definition (p. 115): the ring of p-adic integers.
attribute [kb "milne2020ant" "v3.08, Ch. 7, the ring of p-adic integers, p. 115"] PadicInt
-- Prose definition (p. 116): a local uniformizing parameter.
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of a local uniformizing parameter, p. 116"]
  Valuation.IsUniformizer

/-! ## Newton's lemma -/

-- Theorem 7.32 (Newton's lemma): Mathlib proves it for the p-adic integers (with a strict bound and uniqueness).
attribute [kb "milne2020ant" "v3.08, Thm. 7.32, p. 120"] hensels_lemma
-- Prose definition (p. 121): strictly coprime polynomials, (g, h) = A[X].
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of strictly coprime, p. 121"] IsCoprime
-- Prose definition (p. 122): the norm of a polynomial, the Gauss norm with c = 1; see also `polyNorm` (Ch7Krasner).
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of the norm of a polynomial, p. 122"] Polynomial.gaussNorm

/-! ## Extensions of nonarchimedean absolute values -/

-- Theorem 7.38: existence (the spectral norm extends the absolute value) and uniqueness of the extension to an
-- algebraic extension of a complete nonarchimedean field; Mathlib does not assume the absolute value discrete.
attribute [kb "milne2020ant" "v3.08, Thm. 7.38, p. 123"] spectralNorm_extends
attribute [kb "milne2020ant" "v3.08, Thm. 7.38, p. 123"] spectralNorm_unique_field_norm_ext
attribute [kb "milne2020ant" "v3.08, Thm. 7.38, p. 123"] isNonarchimedean_spectralNorm

/-- **Theorem 7.38**, the formula $|\beta|_L = |\operatorname{Nm}_{L/K}\beta|_K^{1/n}$ for a finite extension $L$ of
degree $n$ of a complete nonarchimedean field $K$, with the spectral norm (the unique extension). -/
@[kb "milne2020ant" "v3.08, Thm. 7.38, p. 123"]
theorem thm_7_38_norm (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] (β : L) :
    spectralNorm K L β = ‖Algebra.norm K β‖ ^ (1 / (Module.finrank K L : ℝ)) := by
  have hint : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have h1 := Algebra.norm_eq_norm_adjoin K β
  have h2 : Algebra.norm K (IntermediateField.AdjoinSimple.gen K β) =
      (-1) ^ (minpoly K β).natDegree * (minpoly K β).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    simpa [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen,
      IntermediateField.adjoin.powerBasis_dim, IntermediateField.adjoin.finrank hint] using this
  have h3 : ‖Algebra.norm K β‖ = ‖(minpoly K β).coeff 0‖ ^ Module.finrank (IntermediateField.adjoin K {β}) L := by
    rw [h1, h2, norm_pow, norm_mul, norm_pow, norm_neg, norm_one]
    simp
  have hd : Module.finrank K L = (minpoly K β).natDegree * Module.finrank (IntermediateField.adjoin K {β}) L := by
    rw [← IntermediateField.adjoin.finrank hint, Module.finrank_mul_finrank]
  rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, h3, hd, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  have hm : (0 : ℝ) < Module.finrank (IntermediateField.adjoin K {β}) L := by
    exact_mod_cast Module.finrank_pos
  have hn : (0 : ℝ) < (minpoly K β).natDegree := by
    exact_mod_cast minpoly.natDegree_pos hint
  push_cast
  field_simp

-- Corollary 7.40: the absolute value extends uniquely to any algebraic (possibly infinite) extension.
attribute [kb "milne2020ant" "v3.08, Cor. 7.40, p. 124"] spectralNorm_unique_field_norm_ext
attribute [kb "milne2020ant" "v3.08, Cor. 7.40, p. 124"] spectralMulAlgNorm
-- Remark 7.41: the completion of an algebraic closure of the p-adic numbers is algebraically closed.
attribute [kb "milne2020ant" "v3.08, Remark 7.41, p. 124"] PadicComplex.isAlgClosed

-- Prose definition (p. 129): Eisenstein polynomials (Mathlib: at the maximal ideal, constant term not in its square).
attribute [kb "milne2020ant" "v3.08, Ch. 7, definition of an Eisenstein polynomial, p. 129"]
  Polynomial.IsEisensteinAt

/-! ## Locally compact fields -/

-- Proposition 7.46: the valuation ring is compact iff the residue field is finite (Mathlib also records
-- completeness and the discrete valuation ring property).
attribute [kb "milne2020ant" "v3.08, Prop. 7.46, p. 126"]
  Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
-- Corollary 7.47: balls, hence the powers of p and A, are compact in a nonarchimedean local field.
attribute [kb "milne2020ant" "v3.08, Cor. 7.47, p. 126"] IsNonarchimedeanLocalField.isCompact_closedBall

/-! ## Krasner's lemma -/

-- Proposition 7.60 (Krasner's lemma), and its validity over complete fields.
attribute [kb "milne2020ant" "v3.08, Prop. 7.60, p. 131"] IsKrasner.krasner
attribute [kb "milne2020ant" "v3.08, Prop. 7.60, p. 131"] IsKrasner.of_completeSpace

end NumberFieldKB.MilneANT
