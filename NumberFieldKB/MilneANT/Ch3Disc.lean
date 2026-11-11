import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Smooth.Field
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Lemmas 3.36–3.38 and Remark 3.39: discriminants and ramification

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), pp. 60–62; bib key `milne2020ant`.

* **Lemma 3.36** (`lemma_3_36`): a basis of $B$ over $A$ reduces to a basis of $B/\mathfrak aB$ over $A/\mathfrak a$
  whose discriminant is the reduction of the discriminant.
* **Lemma 3.37** (`lemma_3_37`): $\mathrm{disc}(\prod B_i/A) = \prod \mathrm{disc}(B_i/A)$.
* **Lemma 3.38** (`lemma_3_38`): over a perfect field, a finite algebra is reduced iff its discriminant is nonzero.
* **Remark 3.39 (a)** (`remark_3_39_a_le`, `remark_3_39_a_eq`): for a number field $K$ and a prime $p$,
  $\mathrm{ord}_p(\mathrm{disc}\,\mathcal O_K) \ge \sum_{\mathfrak P \mid p} f_{\mathfrak P}(e_{\mathfrak P} - 1)$, with
  equality when $p$ divides no $e_{\mathfrak P}$. Milne states this for a free extension $B/A$ of Dedekind domains;
  it is formalized here for $A = \mathbb Z$, $B = \mathcal O_K$.
* **Remark 3.39 (b)** (`relDiscr`, `remark_3_39_b`, `relDiscr_int`): the discriminant ideal of $\mathcal O_L$ over
  $\mathcal O_K$ without freeness; a prime ramifies iff it divides it.
-/

open scoped nonZeroDivisors
open NumberField UniqueFactorizationMonoid

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

open scoped TensorProduct

namespace NumberFieldKB.MilneANT

/-- Determinant of a block-diagonal matrix with blocks indexed by a sigma type. -/
private theorem det_blockDiagonal' {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : ∀ i, Matrix (κ i) (κ i) R) :
    (Matrix.blockDiagonal' M).det = ∏ i, (M i).det := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [(Matrix.blockTriangular_blockDiagonal' M).det_fintype]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine Eq.trans ?_ (Matrix.det_submatrix_equiv_self (Equiv.sigmaSubtype k) (M k))
  congr 1
  ext ⟨⟨k1, r⟩, h1⟩ ⟨⟨k2, s⟩, h2⟩
  simp only at h1 h2
  subst h1 h2
  simp [Matrix.toSquareBlock_def, Equiv.sigmaSubtype]

/-- The trace on a finite product of free algebras is the sum of the traces. -/
private theorem trace_pi_aux {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Module.Basis (κ i) A (B i)) (x : ∀ i, B i) :
    Algebra.trace A (∀ i, B i) x = ∑ i, Algebra.trace A (B i) (x i) := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  have : x * Pi.basis b ⟨i, r⟩ = Pi.single i (x i * b i r) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this]
  simp

private theorem discr_ne_zero_iff_nd {k B : Type*} [Field k] [CommRing B] [Algebra k B] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k B) :
    Algebra.discr k b ≠ 0 ↔ (Algebra.traceForm k B).Nondegenerate := by
  rw [Algebra.discr_def, Algebra.traceMatrix_of_basis,
    ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]

/-- **Lemma 3.36.** Let $B$ be an $A$-algebra with a finite basis $e_1, \dots, e_m$ and $\mathfrak a$ an ideal of
$A$. Then the images $\bar e_1, \dots, \bar e_m$ form a basis of $B/\mathfrak aB$ over $A/\mathfrak a$, and
$D(\bar e_1, \dots, \bar e_m) \equiv D(e_1, \dots, e_m) \pmod{\mathfrak a}$. -/
@[kb "milne2020ant" "v3.08, Lemma 3.36, p. 60"]
theorem lemma_3_36 {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι A B) (a : Ideal A) :
    ∃ e' : Module.Basis ι (A ⧸ a) (B ⧸ a.map (algebraMap A B)),
      (∀ i, e' i = Ideal.Quotient.mk _ (e i)) ∧
        Algebra.discr (A ⧸ a) e' = Ideal.Quotient.mk a (Algebra.discr A e) := by
  let E := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B a
  let e' : Module.Basis ι (A ⧸ a) (B ⧸ a.map (algebraMap A B)) :=
    (e.baseChange (A ⧸ a)).map E.symm.toLinearEquiv
  have happ : ∀ i, e' i = Ideal.Quotient.mk _ (e i) := by
    intro i
    simp only [e', Module.Basis.map_apply, Module.Basis.baseChange_apply]
    exact (E.symm_apply_eq).2 (by simp [E])
  have hrepr : ∀ y i, e'.repr (Ideal.Quotient.mk _ y) i = Ideal.Quotient.mk a (e.repr y i) := by
    intro y i
    simp only [e', Module.Basis.map_repr, LinearEquiv.trans_apply]
    have : E.symm.toLinearEquiv.symm (Ideal.Quotient.mk _ y) = 1 ⊗ₜ[A] y := by
      simp [E]
    rw [this, Module.Basis.baseChange_repr_tmul]
    simp [Algebra.smul_def]
  refine ⟨e', happ, ?_⟩
  have key : ∀ y : B, Algebra.leftMulMatrix e' (Ideal.Quotient.mk _ y)
      = (Algebra.leftMulMatrix e y).map (Ideal.Quotient.mk a) := by
    intro y
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
      happ, ← map_mul, hrepr]
  have htr : ∀ y : B, Algebra.trace (A ⧸ a) (B ⧸ a.map (algebraMap A B))
      (Ideal.Quotient.mk (a.map (algebraMap A B)) y)
      = Ideal.Quotient.mk a (Algebra.trace A B y) := by
    intro y
    rw [Algebra.trace_eq_matrix_trace e', Algebra.trace_eq_matrix_trace e, key, Matrix.trace,
      Matrix.trace, map_sum]
    rfl
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, happ, ← map_mul, htr]

/-- **Lemma 3.37.** Let $B_1, \dots, B_g$ be $A$-algebras that are free of finite rank, with bases $b_i$. The
discriminant of $\prod_i B_i$ (with the union of the bases) is the product of the discriminants of the $B_i$. -/
@[kb "milne2020ant" "v3.08, Lemma 3.37, p. 60"]
theorem lemma_3_37 {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*}
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Module.Basis (κ i) A (B i)) :
    Algebra.discr A (Pi.basis b) = ∏ i, Algebra.discr A (b i) := by
  have : Algebra.traceMatrix A (Pi.basis b)
      = Matrix.blockDiagonal' (fun i => Algebra.traceMatrix A (b i)) := by
    ext ⟨i, r⟩ ⟨j, s⟩
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Pi.basis_apply,
      Matrix.blockDiagonal'_apply, trace_pi_aux b]
    by_cases h : i = j
    · subst h
      rw [Finset.sum_eq_single i]
      · simp
      · intro x _ hx
        simp [Pi.single_eq_of_ne hx]
      · simp
    · simp only [h, dite_false]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : x = i
      · subst hx
        simp [Pi.single_eq_of_ne h]
      · simp [Pi.single_eq_of_ne hx]
  rw [Algebra.discr_def, this, det_blockDiagonal']
  rfl

/-- **Lemma 3.38.** Let $k$ be a perfect field and $B$ a finite-dimensional commutative $k$-algebra with basis $b$.
Then $B$ is reduced iff $\mathrm{disc}(B/k) = D(b) \ne 0$. -/
@[kb "milne2020ant" "v3.08, Lemma 3.38, p. 61"]
theorem lemma_3_38 {k B : Type*} [Field k] [PerfectField k] [CommRing B] [Algebra k B] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι k B) : IsReduced B ↔ Algebra.discr k b ≠ 0 := by
  classical
  rw [discr_ne_zero_iff_nd]
  constructor
  · intro hred
    have hfin : Module.Finite k B := Module.Finite.of_basis b
    have : IsArtinianRing B := IsArtinianRing.of_finite k B
    let f : B ≃ₐ[k] ∀ m : MaximalSpectrum B, B ⧸ m.asIdeal :=
      (IsArtinianRing.equivPi B).restrictScalars k
    have : ∀ m : MaximalSpectrum B, Module.Finite k (B ⧸ m.asIdeal) := fun m =>
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    let _ : ∀ m : MaximalSpectrum B, Field (B ⧸ m.asIdeal) := fun m => Ideal.Quotient.field _
    have : Finite (MaximalSpectrum B) := inferInstance
    have := Fintype.ofFinite (MaximalSpectrum B)
    let b' := Pi.basis (fun m : MaximalSpectrum B => Module.finBasis k (B ⧸ m.asIdeal))
    have h1 : Algebra.discr k b' ≠ 0 := by
      rw [lemma_3_37, Finset.prod_ne_zero_iff]
      intro m _
      exact Algebra.discr_not_zero_of_basis k _
    have h2 := Algebra.discr_eq_discr_of_algEquiv b' f.symm
    have h3 : Algebra.discr k (b'.map f.symm.toLinearEquiv) ≠ 0 := by
      have : (b'.map f.symm.toLinearEquiv : _ → B) = f.symm ∘ b' := by
        ext i; simp
      rw [this, ← h2]; exact h1
    exact (discr_ne_zero_iff_nd _).1 h3
  · intro hnd
    rw [isReduced_iff]
    intro x hx
    refine hnd.1 x fun y => ?_
    rw [Algebra.traceForm_apply]
    exact (Algebra.isNilpotent_trace_of_isNilpotent
      ((Commute.all x y).isNilpotent_mul_right (show IsNilpotent x from hx))).eq_zero

section PrimeValuation

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]

open scoped Classical in
private theorem padicValNat_absNorm_prime_aux (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    padicValNat p Q.absNorm =
      if Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) then Q.inertiaDeg ℤ else 0 := by
  split_ifs with h
  · have : Q.LiesOver (Ideal.span {(p : ℤ)}) := h.2
    rw [← Ideal.pow_inertiaDeg p Q, padicValNat.prime_pow]
  · by_contra hne
    have hdvd : p ∣ Q.absNorm := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr hne)
    obtain ⟨P, hPm, hPu, hPQ⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp.out Q hdvd
    have hQm : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ
    have hPQ' : P = Q := (hQm.eq_of_le hPm.ne_top (Ideal.dvd_iff_le.mp hPQ)).symm
    subst hPQ'
    exact h ⟨hPm.isPrime, ⟨hPu.symm⟩⟩

open scoped Classical in
/-- The `p`-adic valuation of the absolute norm of a nonzero ideal, as a sum over the primes above `p`. -/
private theorem padicValNat_absNorm_eq_sum (T : Finset (Ideal (𝓞 K)))
    (hT : ∀ Q, Q ∈ T ↔ Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    padicValNat p I.absNorm =
      ∑ P ∈ T, P.inertiaDeg ℤ * (normalizedFactors I).count P := by
  have hprod : (normalizedFactors I).prod = I := by
    have := prod_normalizedFactors hI
    exact associated_iff_eq.mp this
  have hprime : ∀ Q ∈ normalizedFactors I, Q.IsPrime := fun Q hQ =>
    Ideal.isPrime_of_prime (prime_of_normalized_factor Q hQ)
  have hne : ∀ Q ∈ normalizedFactors I, Q ≠ ⊥ := fun Q hQ =>
    (prime_of_normalized_factor Q hQ).ne_zero
  have h1 : padicValNat p I.absNorm
      = ((normalizedFactors I).map fun Q => padicValNat p Q.absNorm).sum := by
    conv_lhs => rw [← hprod]
    rw [map_multiset_prod]
    have key : ∀ s : Multiset (Ideal (𝓞 K)), (∀ Q ∈ s, Q ≠ ⊥) →
        padicValNat p (s.map Ideal.absNorm).prod = (s.map fun Q => padicValNat p Q.absNorm).sum := by
      intro s
      induction s using Multiset.induction with
      | empty => simp
      | cons a s ih =>
        intro h
        have ha : a.absNorm ≠ 0 := fun h0 => h a (Multiset.mem_cons_self _ _)
          (Ideal.absNorm_eq_zero_iff.mp h0)
        have hs : (s.map Ideal.absNorm).prod ≠ 0 := by
          refine Multiset.prod_ne_zero ?_
          intro h0
          obtain ⟨b, hb, hb0⟩ := Multiset.mem_map.mp h0
          exact h b (Multiset.mem_cons_of_mem hb) (Ideal.absNorm_eq_zero_iff.mp hb0)
        simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
        have : NeZero a.absNorm := ⟨ha⟩
        have : NeZero (s.map Ideal.absNorm).prod := ⟨hs⟩
        rw [padicValNat.mul ha hs, ih fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ)]
    exact key _ hne
  rw [h1]
  have h2 : ((normalizedFactors I).map fun Q => padicValNat p Q.absNorm).sum
      = ∑ Q ∈ (normalizedFactors I).toFinset,
          (normalizedFactors I).count Q * padicValNat p Q.absNorm := by
    rw [Finset.sum_multiset_map_count]
    simp
  rw [h2]
  have h3 : ∀ Q ∈ (normalizedFactors I).toFinset,
      padicValNat p Q.absNorm = if Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) then
        Q.inertiaDeg ℤ else 0 := by
    intro Q hQ
    have hQ' := Multiset.mem_toFinset.mp hQ
    have := hprime Q hQ'
    exact padicValNat_absNorm_prime_aux K p Q (hne Q hQ')
  let F : Ideal (𝓞 K) → ℕ := fun Q =>
    (normalizedFactors I).count Q *
      if Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) then Q.inertiaDeg ℤ else 0
  have e1 : ∑ Q ∈ (normalizedFactors I).toFinset,
      (normalizedFactors I).count Q * padicValNat p Q.absNorm
      = ∑ Q ∈ (normalizedFactors I).toFinset ∪ T, F Q := by
    rw [← Finset.sum_subset Finset.subset_union_left (f := F)]
    · exact Finset.sum_congr rfl fun Q hQ => by simp only [F, h3 Q hQ]
    · intro Q _ hQ
      have : (normalizedFactors I).count Q = 0 :=
        Multiset.count_eq_zero.mpr fun h => hQ (Multiset.mem_toFinset.mpr h)
      simp [F, this]
  have e2 : ∑ Q ∈ T, Q.inertiaDeg ℤ * (normalizedFactors I).count Q
      = ∑ Q ∈ (normalizedFactors I).toFinset ∪ T, F Q := by
    rw [← Finset.sum_subset Finset.subset_union_right (f := F)]
    · refine Finset.sum_congr rfl fun Q hQ => ?_
      have hS := (hT Q).mp hQ
      simp only [F, hS, ite_true]
      ring
    · intro Q _ hQ
      have : Q ∉ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := fun h => hQ ((hT Q).mpr h)
      simp [F, this]
  rw [e1, e2]

private theorem le_count_of_pow_dvd {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P I : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (hI : I ≠ ⊥) (n : ℕ) (h : P ^ n ∣ I) :
    n ≤ (normalizedFactors I).count P := by
  classical
  have h1 := emultiplicity_eq_count_normalizedFactors
    (UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.prime_of_isPrime hP inferInstance)) hI
  rw [normalize_eq] at h1
  have h2 := pow_dvd_iff_le_emultiplicity.mp h
  rw [h1] at h2
  exact_mod_cast h2

private theorem span_ne_bot_aux : Ideal.span {(p : ℤ)} ≠ ⊥ :=
  Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast hp.out.ne_zero)

/-- `P ^ e ∣ p𝓞` where `e` is the ramification index, with the complementary factor coprime to `P`. -/
private theorem exists_pow_ramificationIdx_mul (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ Q : Ideal (𝓞 K), P ⊔ Q = ⊤ ∧
      (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) = P ^ (P.ramificationIdx ℤ) * Q := by
  have hpne := span_ne_bot_aux p
  have hp0 : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hpne
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpne P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  obtain ⟨Q, hQ1, hQ⟩ := Ideal.eq_prime_pow_mul_coprime hp0 P
  refine ⟨Q, hQ1, ?_⟩
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (Ideal.span {(p : ℤ)}) P hp0]
  exact hQ

private theorem exists_trace_ne_zero_of_nilpotent_ker {F W k : Type*} [Field F] [Finite F]
    [CommRing W] [Algebra F W] [Module.Finite F W] [Field k] [Algebra F k] [Module.Finite F k]
    [Algebra.IsSeparable F k] (π : W →ₐ[F] k) (hπ : Function.Surjective π)
    (hnil : IsNilpotent (RingHom.ker (π : W →+* k))) (e : ℕ)
    (hcard : Nat.card W = Nat.card k ^ e) (he : (e : F) ≠ 0) :
    ∃ w : W, Algebra.trace F W w ≠ 0 := by
  have : Algebra.FormallyEtale F k := Algebra.FormallyEtale.of_isSeparable F k
  let σ : k →ₐ[F] W := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id F k) π hπ hnil
  let _ : Algebra k W := σ.toRingHom.toAlgebra
  have : IsScalarTower F k W := IsScalarTower.of_algebraMap_eq fun x => (σ.commutes x).symm
  have : Module.Finite k W := Module.Finite.of_restrictScalars_finite F k W
  have hfin : Finite k := Module.finite_of_finite F
  have hfinW : Finite W := Module.finite_of_finite F
  have hrank : Module.finrank k W = e := by
    have h1 := Module.natCard_eq_pow_finrank (K := k) (V := W)
    rw [hcard] at h1
    have : 1 < Nat.card k := Finite.one_lt_card
    exact (Nat.pow_right_injective this h1).symm
  obtain ⟨u, hu⟩ : ∃ u : k, Algebra.trace F k u ≠ 0 := by
    by_contra h
    push Not at h
    exact Algebra.trace_ne_zero F k (LinearMap.ext h)
  refine ⟨algebraMap k W u, ?_⟩
  rw [← Algebra.trace_trace (S := k), Algebra.trace_algebraMap, hrank, map_nsmul]
  simpa [nsmul_eq_mul] using ⟨he, hu⟩

private theorem exists_intTrace_notMem (P Q : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (e : ℕ) (he0 : 0 < e)
    (hPQ : P ^ e * Q = (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)))
    (hcop : IsCoprime (P ^ e) Q)
    (hcard : Nat.card (𝓞 K ⧸ P ^ e) = Nat.card (𝓞 K ⧸ P) ^ e)
    (hep : ¬ p ∣ e) :
    ∃ x ∈ Q, Algebra.intTrace ℤ (𝓞 K) x ∉ Ideal.span {(p : ℤ)} := by
  have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal := by
    have : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp.out)
    exact Ideal.IsPrime.isMaximal this (span_ne_bot_aux p)
  let F := ℤ ⧸ Ideal.span {(p : ℤ)}
  let _ : Field F := Ideal.Quotient.field _
  have hle1 : Ideal.span {(p : ℤ)} ≤ (P ^ e).comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, ← hPQ]
    exact Ideal.mul_le_left
  have hle2 : Ideal.span {(p : ℤ)} ≤ P.comap (algebraMap ℤ (𝓞 K)) := hle1.trans
    (Ideal.comap_mono (Ideal.pow_le_self he0.ne' : P ^ e ≤ P))
  have hleQ : Ideal.span {(p : ℤ)} ≤ Q.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, ← hPQ]
    exact Ideal.mul_le_right
  let _ : Algebra F (𝓞 K ⧸ P ^ e) := Ideal.Quotient.algebraQuotientOfLEComap hle1
  let _ : Algebra F (𝓞 K ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap hle2
  let _ : Algebra F (𝓞 K ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap hleQ
  have : IsScalarTower ℤ F (𝓞 K ⧸ P ^ e) := .of_algebraMap_eq' rfl
  have : IsScalarTower ℤ F (𝓞 K ⧸ P) := .of_algebraMap_eq' rfl
  have : IsScalarTower ℤ F (𝓞 K ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite F (𝓞 K ⧸ P ^ e) := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.Finite F (𝓞 K ⧸ P) := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.Finite F (𝓞 K ⧸ Q) := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Finite F := Finite.of_equiv _ (Int.quotientSpanNatEquivZMod p).symm.toEquiv
  let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field _
  have : Algebra.IsSeparable F (𝓞 K ⧸ P) := inferInstance
  let π : (𝓞 K ⧸ P ^ e) →ₐ[F] (𝓞 K ⧸ P) :=
    { Ideal.Quotient.factor (Ideal.pow_le_self he0.ne') with
      commutes' := fun x => by
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk (P ^ e) z, rfl⟩
  have hnil : IsNilpotent (RingHom.ker (π : (𝓞 K ⧸ P ^ e) →+* (𝓞 K ⧸ P))) := by
    refine ⟨e, ?_⟩
    have hker : RingHom.ker (π : (𝓞 K ⧸ P ^ e) →+* (𝓞 K ⧸ P))
        ≤ P.map (Ideal.Quotient.mk (P ^ e)) := by
      intro x hx
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
      have : Ideal.Quotient.mk P z = 0 := hx
      exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (P ^ e))
        (Ideal.Quotient.eq_zero_iff_mem.mp this)
    have h2 : (RingHom.ker (π : (𝓞 K ⧸ P ^ e) →+* (𝓞 K ⧸ P))) ^ e ≤ ⊥ := by
      refine (Ideal.pow_right_mono hker e).trans ?_
      rw [← Ideal.map_pow, Ideal.map_quotient_self]
    rw [Ideal.zero_eq_bot]
    exact le_bot_iff.mp h2
  have he : (e : F) ≠ 0 := by
    intro h
    apply hep
    have h' : Ideal.Quotient.mk (Ideal.span {(p : ℤ)}) (e : ℤ) = 0 := by
      simpa using h
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h'
    exact_mod_cast h'
  obtain ⟨w, hw⟩ := exists_trace_ne_zero_of_nilpotent_ker π hπ hnil e hcard he
  let E : (𝓞 K ⧸ (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K))) ≃ₐ[F]
      ((𝓞 K ⧸ P ^ e) × 𝓞 K ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hPQ.symm).trans
        (Ideal.quotientMulEquivQuotientProd (P ^ e) Q hcop),
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (E.symm (w, 0))
  refine ⟨y, ?_, ?_⟩
  · have := congr((E $hy).2)
    simp at this
    simpa [E, Ideal.Quotient.eq_zero_iff_mem] using this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain, hy,
      Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa using hw

private theorem padicValInt_discr_eq_sum (T : Finset (Ideal (𝓞 K)))
    (hT : ∀ Q, Q ∈ T ↔ Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) :
    padicValInt p (discr K) =
      ∑ P ∈ T, P.inertiaDeg ℤ * (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := by
  have hD : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  rw [← padicValNat_absNorm_eq_sum K p T hT _ hD, absNorm_differentIdeal K]
  rfl

end PrimeValuation

/-- **Remark 3.39 (a)**, inequality, for $A = \mathbb Z$. For a number field $K$ and a prime number $p$,
$$\mathrm{ord}_p(\mathrm{disc}(\mathcal O_K/\mathbb Z)) \ge \sum_{\mathfrak P \mid p} f(\mathfrak P/p)\,(e(\mathfrak P/p) - 1).$$
-/
@[kb "milne2020ant" "v3.08, Remark 3.39 (a), p. 62"]
theorem remark_3_39_a_le (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    ∑ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) |>.toFinset,
        P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1)
      ≤ padicValInt p (discr K) := by
  classical
  rw [padicValInt_discr_eq_sum K p _ (fun Q => Set.mem_toFinset)]
  refine Finset.sum_le_sum fun P hP => ?_
  rw [Set.mem_toFinset] at hP
  obtain ⟨hPp, hPo⟩ := hP
  have hpne := span_ne_bot_aux p
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpne P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal hPp hP0
  have hD : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨Q, -, hQ⟩ := exists_pow_ramificationIdx_mul K p P
  refine Nat.mul_le_mul_left _ (le_count_of_pow_dvd P _ hP0 hD _ ?_)
  exact pow_sub_one_dvd_differentIdeal ℤ P _ hpne ⟨Q, hQ⟩

/-- **Remark 3.39 (a)**, equality, for $A = \mathbb Z$: if $p$ divides none of the ramification indices
$e(\mathfrak P/p)$, then
$\mathrm{ord}_p(\mathrm{disc}(\mathcal O_K/\mathbb Z)) = \sum_{\mathfrak P \mid p} f(\mathfrak P/p)(e(\mathfrak P/p) - 1)$. -/
@[kb "milne2020ant" "v3.08, Remark 3.39 (a), p. 62"]
theorem remark_3_39_a_eq (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (htame : ∀ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      ¬ p ∣ P.ramificationIdx ℤ) :
    ∑ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) |>.toFinset,
        P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1)
      = padicValInt p (discr K) := by
  classical
  rw [padicValInt_discr_eq_sum K p _ (fun Q => Set.mem_toFinset)]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Set.mem_toFinset] at hP
  have htP := htame P hP
  obtain ⟨hPp, hPo⟩ := hP
  have hpne := span_ne_bot_aux p
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpne P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal hPp hP0
  have hD : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨Q, hQ1, hQ⟩ := exists_pow_ramificationIdx_mul K p P
  set e := P.ramificationIdx ℤ with he_def
  have he0 : 0 < e := by
    have hp0 : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot hpne
    have h := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (Ideal.span {(p : ℤ)}) P hp0
    have h1 : P ^ 1 ∣ (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) := by
      rw [pow_one, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
      exact (Ideal.LiesOver.over (p := Ideal.span {(p : ℤ)}) (P := P)).le
    have := le_count_of_pow_dvd P _ hP0 hp0 1 h1
    rw [← h] at this
    exact this
  have hcop : IsCoprime (P ^ e) Q := (Ideal.isCoprime_iff_sup_eq.mpr hQ1).pow_left
  have hcard : Nat.card (𝓞 K ⧸ P ^ e) = Nat.card (𝓞 K ⧸ P) ^ e := by
    have := map_pow (Ideal.absNorm (S := 𝓞 K)) P e
    simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  obtain ⟨x, hxQ, hx⟩ := exists_intTrace_notMem K p P Q e he0 hQ.symm hcop hcard htP
  have hnd : ¬ P ^ e ∣ differentIdeal ℤ (𝓞 K) :=
    not_dvd_differentIdeal_of_intTrace_notMem ℤ (P ^ e) Q hQ.symm x hxQ hx
  have hcount : (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P = e - 1 := by
    refine Ideal.count_normalizedFactors_eq (p := P) ?_ ?_
    · exact Ideal.dvd_iff_le.mp (pow_sub_one_dvd_differentIdeal ℤ P _ hpne ⟨Q, hQ⟩)
    · rw [Nat.sub_add_cancel he0]
      exact fun h => hnd (Ideal.dvd_iff_le.mpr h)
  rw [hcount]

/-- **The relative discriminant ideal** $\mathrm{disc}(B/A)$ of an extension $B/A$ of Dedekind domains, without
assuming $B$ free over $A$ (Milne, Remark 3.39 (b)): here the relative norm $N_{B/A}(\mathfrak D_{B/A})$ of the
different ideal (Mathlib's `Ideal.relNorm` and `differentIdeal`).

*Deviation:* Milne defines it locally, as $\prod_{\mathfrak p} \mathfrak p^{m(\mathfrak p)}$ with
$(\mathfrak pA_{\mathfrak p})^{m(\mathfrak p)} = \mathrm{disc}(B_{\mathfrak p}/A_{\mathfrak p})$; the norm of the
different is the standard equivalent global description. `relDiscr_int` compares it with the usual discriminant for
$A = \mathbb Z$, and `remark_3_39_b` proves Milne's claimed property. -/
@[kb "milne2020ant" "v3.08, Remark 3.39 (b) (definition of disc(B/A) as an ideal), p. 62"]
noncomputable def relDiscr (A B : Type*) [CommRing A] [IsDedekindDomain A] [CommRing B]
    [IsDedekindDomain B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] : Ideal A :=
  Ideal.relNorm A (differentIdeal A B)

/-- For $\mathbb Z \subseteq \mathcal O_K$, the discriminant ideal `relDiscr` is the principal ideal generated by the
discriminant of $K$. -/
@[kb "milne2020ant" "v3.08, Remark 3.39 (b) (agreement with the usual discriminant), p. 62"]
theorem relDiscr_int (K : Type*) [Field K] [NumberField K] :
    relDiscr ℤ (𝓞 K) = Ideal.span {discr K} := by
  unfold relDiscr
  rw [Ideal.relNorm_int, absNorm_differentIdeal K]
  exact Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs _).symm

/-- **Remark 3.39 (b).** A nonzero prime $\mathfrak p$ of $A$ ramifies in $B$ (some prime $\mathfrak P \mid \mathfrak p$
is ramified) iff $\mathfrak p$ divides the discriminant ideal $\mathrm{disc}(B/A)$. Ramified is Mathlib's
`¬ Algebra.IsUnramifiedAt A P`, which for finite residue fields means $e(\mathfrak P/\mathfrak p) > 1$. -/
@[kb "milne2020ant" "v3.08, Remark 3.39 (b), p. 62"]
theorem remark_3_39_b {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B]
    [IsDedekindDomain B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    (∃ (P : Ideal B) (_ : P.IsPrime), P.LiesOver p ∧ ¬ Algebra.IsUnramifiedAt A P) ↔ p ∣ relDiscr A B := by
  classical
  have hD : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  have hpm : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
  constructor
  · rintro ⟨P, hP, hPp, hPun⟩
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
    have hPm : P.IsMaximal := hP.isMaximal hP0
    have hdvd : P ∣ differentIdeal A B := dvd_differentIdeal_iff.mpr hPun
    have h1 := Ideal.relNorm_mono A (Ideal.dvd_iff_le.mp hdvd)
    rw [Ideal.relNorm_eq_pow_of_isMaximal P p] at h1
    have h2 : p ^ P.inertiaDeg A ≤ p := Ideal.pow_le_self (Ideal.inertiaDeg_pos P A).ne'
    exact Ideal.dvd_iff_le.mpr (h1.trans h2)
  · intro h
    have hrn : Ideal.relNorm A (differentIdeal A B)
        = ((normalizedFactors (differentIdeal A B)).map (Ideal.relNorm A)).prod := by
      conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hD]
      exact map_multiset_prod _ _
    have hpprime : Prime p := Ideal.prime_of_isPrime hp inferInstance
    unfold relDiscr at h
    rw [hrn] at h
    obtain ⟨_, hmem, hdv⟩ := hpprime.exists_mem_multiset_dvd h
    obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hmem
    have hQprime : Prime Q := prime_of_normalized_factor Q hQ
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    have hQ0 : Q ≠ ⊥ := hQprime.ne_zero
    have hQm : Q.IsMaximal := hQp.isMaximal hQ0
    have hq0 : Q.under A ≠ ⊥ := Ideal.under_ne_bot A hQ0
    have hqm : (Q.under A).IsMaximal := (Ideal.IsPrime.under A Q).isMaximal hq0
    rw [Ideal.relNorm_eq_pow_of_isMaximal Q (Q.under A)] at hdv
    have hdq : p ∣ Q.under A := hpprime.dvd_of_dvd_pow hdv
    have hpq : p = Q.under A := (hqm.eq_of_le hpm.ne_top (Ideal.dvd_iff_le.mp hdq)).symm
    have hlie : Q.LiesOver p := ⟨hpq⟩
    refine ⟨Q, hQp, hlie, ?_⟩
    exact dvd_differentIdeal_iff.mp (dvd_of_mem_normalizedFactors hQ)

end NumberFieldKB.MilneANT
