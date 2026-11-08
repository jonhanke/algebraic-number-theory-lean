import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 2: examples of rings of integers

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`; printed page numbers.

* **Example 2.10** (`example_2_10_a_int`, `example_2_10_a_gaussianInt`, `example_2_10_b`, `example_2_10_c`):
  $\mathbb Z$ and $\mathbb Z[i]$ are integrally closed; unique factorization fails in $\mathbb Z[\sqrt{-3}]$; the
  integral closure of the ring of symmetric polynomials $k[S_1, \dots, S_m]$ in $k(X_1, \dots, X_m)$ is
  $k[X_1, \dots, X_m]$.
* **Monogenic number fields** (`IsMonogenic`, Milne's footnote 3 on p. 39, a definition in prose).
* **Examples 2.36, 2.37, 2.39**: $X^3 - X - 1$, $X^3 + X + 1$, $X^5 - X - 1$ are irreducible with square-free
  discriminants $-23$, $-31$, $2869 = 19\cdot 151$, so $\mathbb Z[\alpha]$ is the ring of integers.
* **Example 2.38** (Dedekind): for a root $\alpha$ of $X^3 + X^2 - 2X + 8$, $D(1,\alpha,\alpha^2) = -2012$,
  $\mathcal O_K \neq \mathbb Z[\alpha]$, $\mathrm{disc}(\mathcal O_K/\mathbb Z) = -503$, and $K$ is not monogenic.

Throughout, "a root $\alpha$ of $f$ generating $K$" is a hypothesis on an element `α : 𝓞 K` of a number field `K`
with `f(α) = 0` and `ℚ⟮α⟯ = ⊤`.
-/

open Polynomial NumberField IntermediateField

namespace NumberFieldKB.MilneANT

/-- **Example 2.10 (a)**, first half: $\mathbb Z$ is integrally closed (it is a principal ideal domain). -/
@[kb "milne2020ant" "v3.08, Example 2.10 (a), p. 29"]
theorem example_2_10_a_int : IsIntegrallyClosed ℤ := inferInstance

/-- **Example 2.10 (a)**, second half: the Gaussian integers $\mathbb Z[i]$ are integrally closed (a principal ideal
domain). -/
@[kb "milne2020ant" "v3.08, Example 2.10 (a), p. 29"]
theorem example_2_10_a_gaussianInt : IsIntegrallyClosed GaussianInt := inferInstance

private lemma irred_of_norm_four (x : ℤ√(-3)) (hx : x.norm = 4) : Irreducible x := by
  have hnu : ¬ IsUnit x := by
    rw [Zsqrtd.isUnit_iff_norm_isUnit, hx]
    decide
  refine ⟨hnu, fun a b hab => ?_⟩
  have h := congrArg Zsqrtd.norm hab
  rw [Zsqrtd.norm_mul, hx] at h
  have ha : 0 ≤ a.norm := by
    rw [Zsqrtd.norm_def]; nlinarith [sq_nonneg a.re, sq_nonneg a.im]
  have hb : 0 ≤ b.norm := by
    rw [Zsqrtd.norm_def]; nlinarith [sq_nonneg b.re, sq_nonneg b.im]
  have hne : ∀ y : ℤ√(-3), y.norm ≠ 2 := by
    intro y hy
    rw [Zsqrtd.norm_def] at hy
    have h1 : y.re * y.re + 3 * y.im * y.im = 2 := by linarith
    have him1 : y.im ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith [mul_self_nonneg y.re]
    have him2 : 0 ≤ y.im := by
      by_contra hc; push Not at hc; nlinarith [mul_self_nonneg y.re]
    have him : y.im = 0 := le_antisymm him1 him2
    rw [him] at h1
    have h3 : y.re ≤ 1 := by
      by_contra hc; push Not at hc; nlinarith
    have h4 : -1 ≤ y.re := by
      by_contra hc; push Not at hc; nlinarith
    interval_cases y.re <;> omega
  have hd : a.norm ∣ 4 := ⟨b.norm, h⟩
  have hle : a.norm ≤ 4 := Int.le_of_dvd (by norm_num) hd
  have : a.norm = 0 ∨ a.norm = 1 ∨ a.norm = 2 ∨ a.norm = 3 ∨ a.norm = 4 := by omega
  rcases this with h0 | h1 | h2 | h3 | h4
  · rw [h0] at h; omega
  · left; rw [Zsqrtd.isUnit_iff_norm_isUnit, h1]; decide
  · exact absurd h2 (hne a)
  · rw [h3] at h; omega
  · right; rw [Zsqrtd.isUnit_iff_norm_isUnit]
    rw [h4] at h
    have : b.norm = 1 := by omega
    rw [this]; decide

/-- **Example 2.10 (b).** Unique factorization fails in $\mathbb Z[\sqrt{-3}]$: $4 = 2\cdot 2 = (1+\sqrt{-3})(1-\sqrt{-3})$
with all four factors irreducible, $2$ not associated to $1 \pm \sqrt{-3}$, and so $\mathbb Z[\sqrt{-3}]$ is not a
unique factorization domain. -/
@[kb "milne2020ant" "v3.08, Example 2.10 (b), p. 29"]
theorem example_2_10_b :
    (2 * 2 : ℤ√(-3)) = ⟨1, 1⟩ * ⟨1, -1⟩ ∧ Irreducible (2 : ℤ√(-3)) ∧ Irreducible (⟨1, 1⟩ : ℤ√(-3)) ∧
      Irreducible (⟨1, -1⟩ : ℤ√(-3)) ∧ ¬ Associated (2 : ℤ√(-3)) ⟨1, 1⟩ ∧
      ¬ Associated (2 : ℤ√(-3)) ⟨1, -1⟩ ∧ ¬ UniqueFactorizationMonoid (ℤ√(-3)) := by
  have h2 : Irreducible (2 : ℤ√(-3)) := irred_of_norm_four 2 (by decide)
  have hnd : ∀ c : ℤ, ∀ y : ℤ√(-3), y.re = c → c % 2 = 1 → ¬ (2 : ℤ√(-3)) ∣ y := by
    rintro c y hy hc ⟨z, hz⟩
    have := congrArg Zsqrtd.re hz
    simp at this
    omega
  refine ⟨by ext <;> simp, h2, irred_of_norm_four _ (by decide), irred_of_norm_four _ (by decide), ?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    exact hnd 1 ⟨1, 1⟩ rfl rfl ⟨u, hu.symm⟩
  · rintro ⟨u, hu⟩
    exact hnd 1 ⟨1, -1⟩ rfl rfl ⟨u, hu.symm⟩
  · intro hU
    have hp : Prime (2 : ℤ√(-3)) := (UniqueFactorizationMonoid.irreducible_iff_prime).1 h2
    have hdvd : (2 : ℤ√(-3)) ∣ ⟨1, 1⟩ * ⟨1, -1⟩ := ⟨2, by ext <;> simp⟩
    rcases hp.dvd_or_dvd hdvd with h | h
    · exact hnd 1 _ rfl rfl h
    · exact hnd 1 _ rfl rfl h

private lemma X_isIntegral_symm (k : Type*) [Field k] (m : ℕ) (i : Fin m) :
    IsIntegral (MvPolynomial.symmetricSubalgebra (Fin m) k) (MvPolynomial.X i : MvPolynomial (Fin m) k) := by
  set S := MvPolynomial.symmetricSubalgebra (Fin m) k with hS
  let q : (MvPolynomial (Fin m) k)[X] := ∏ j : Fin m, (X - C (MvPolynomial.X j))
  have hqm : q.Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)
  have hcoef : ∀ n, q.coeff n ∈ Set.range S.val.toRingHom := by
    intro n
    refine ⟨⟨q.coeff n, ?_⟩, rfl⟩
    rw [MvPolynomial.mem_symmetricSubalgebra]
    intro σ
    have h1 : q.map ((MvPolynomial.rename σ : MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k) :
        MvPolynomial (Fin m) k →+* MvPolynomial (Fin m) k) = q := by
      simp only [q, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        RingHom.coe_coe, MvPolynomial.rename_X]
      exact Equiv.prod_comp σ (fun j => (X - C (MvPolynomial.X j) : (MvPolynomial (Fin m) k)[X]))
    have := congrArg (fun p => p.coeff n) h1
    simpa [coeff_map] using this
  obtain ⟨p, hp⟩ := (Polynomial.lifts_iff_coeff_lifts q).2 hcoef
  have hpm : p.Monic := Polynomial.monic_of_injective (f := S.val.toRingHom) Subtype.val_injective
    (by have hp' : p.map S.val.toRingHom = q := hp
        rw [hp']; exact hqm)
  refine ⟨p, hpm, ?_⟩
  have : eval₂ (algebraMap S (MvPolynomial (Fin m) k)) (MvPolynomial.X i) p
      = eval (MvPolynomial.X i) (p.map S.val.toRingHom) := by
    rw [eval_map]; rfl
  have hp' : p.map S.val.toRingHom = q := hp
  rw [this, hp']
  simp only [q, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

private lemma isIntegral_symm (k : Type*) [Field k] (m : ℕ) (r : MvPolynomial (Fin m) k) :
    IsIntegral (MvPolynomial.symmetricSubalgebra (Fin m) k) r := by
  set S := MvPolynomial.symmetricSubalgebra (Fin m) k with hS
  induction r using MvPolynomial.induction_on with
  | C a =>
    have : (MvPolynomial.C a : MvPolynomial (Fin m) k) = algebraMap S _ ⟨MvPolynomial.C a, S.algebraMap_mem a⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap
  | add p q hp hq => exact hp.add hq
  | mul_X p i hp => exact hp.mul (X_isIntegral_symm k m i)

/-- **Example 2.10 (c).** Let $k$ be a field, $R = k[X_0, \dots, X_{m-1}]$ and $F = k(X_0, \dots, X_{m-1})$ its field of
fractions. An element of $F$ is integral over the subring $k[S_1, \dots, S_m]$ of symmetric polynomials iff it lies
in $R$: the integral closure of $k[S_1, \dots, S_m]$ in $F$ is $k[X_0, \dots, X_{m-1}]$. (Indices are $0$-based.) -/
@[kb "milne2020ant" "v3.08, Example 2.10 (c), p. 29"]
theorem example_2_10_c (k : Type*) [Field k] (m : ℕ) (x : FractionRing (MvPolynomial (Fin m) k)) :
    ((algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))).comp
        (MvPolynomial.symmetricSubalgebra (Fin m) k).val.toRingHom).IsIntegralElem x ↔
      x ∈ Set.range (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))) := by
  constructor
  · rintro ⟨p, hp, hev⟩
    have hint : IsIntegral (MvPolynomial (Fin m) k) x := by
      refine ⟨p.map (MvPolynomial.symmetricSubalgebra (Fin m) k).val.toRingHom, hp.map _, ?_⟩
      rw [eval₂_map]
      exact hev
    exact IsIntegrallyClosed.isIntegral_iff.1 hint
  · rintro ⟨r, rfl⟩
    obtain ⟨p, hp, hev⟩ := isIntegral_symm k m r
    refine ⟨p, hp, ?_⟩
    have := Polynomial.hom_eval₂ p
      (algebraMap (MvPolynomial.symmetricSubalgebra (Fin m) k) (MvPolynomial (Fin m) k))
      (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))) r
    exact this.symm.trans (by rw [hev, map_zero])

/-- **Monogenic number field** (Milne, footnote 3 on p. 39, a definition in prose): a number field $K$ is monogenic
if $\mathcal O_K = \mathbb Z[\alpha]$ for some $\alpha \in \mathcal O_K$, i.e. the subring generated by $\alpha$ is
all of $\mathcal O_K$. Mathlib has no such predicate. -/
@[kb "milne2020ant" "v3.08, Ch. 2, footnote 3 (definition in prose: monogenic), p. 39"]
def IsMonogenic (K : Type*) [Field K] [NumberField K] : Prop :=
  ∃ α : 𝓞 K, Algebra.adjoin ℤ {α} = ⊤

/-- The companion matrix of the monic polynomial with coefficients `a`. -/
private def compMat (m : ℕ) (a : Fin m → ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j => if (j : ℕ) + 1 = m then -a i else if (i : ℕ) = j + 1 then 1 else 0

private lemma trace_pow_pb {K : Type*} [Field K] [NumberField K] (pb : PowerBasis ℚ K)
    (a : Fin pb.dim → ℤ) (ha : ∀ i : Fin pb.dim, (minpoly ℚ pb.gen).coeff i = (a i : ℚ)) (k : ℕ) :
    Algebra.trace ℚ K (pb.gen ^ k) = ((Matrix.trace ((compMat pb.dim a) ^ k) : ℤ) : ℚ) := by
  have hL : Algebra.leftMulMatrix pb.basis pb.gen = (compMat _ a).map (Int.cast : ℤ → ℚ) := by
    rw [PowerBasis.leftMulMatrix]
    refine Matrix.ext fun i j => ?_
    simp only [compMat, Matrix.of_apply, Matrix.map_apply, PowerBasis.minpolyGen_eq, ha]
    split_ifs <;> simp
  rw [Algebra.trace_eq_matrix_trace pb.basis, map_pow, hL]
  have := (Int.castRingHom ℚ).mapMatrix.map_pow (compMat pb.dim a) k
  simp only [RingHom.mapMatrix_apply] at this
  change Matrix.trace ((compMat pb.dim a).map (Int.castRingHom ℚ) ^ k) = _
  rw [← this]
  simp [Matrix.trace]

private lemma trace_pow_eq_aux {K : Type*} [Field K] [NumberField K] (α : K) (hgen : ℚ⟮α⟯ = ⊤)
    (m : ℕ) (hm : (minpoly ℚ α).natDegree = m) (a : Fin m → ℤ)
    (ha : ∀ i : Fin m, (minpoly ℚ α).coeff i = (a i : ℚ)) (k : ℕ) :
    Algebra.trace ℚ K (α ^ k) = ((Matrix.trace ((compMat m a) ^ k) : ℤ) : ℚ) := by
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have hadj : Algebra.adjoin ℚ {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hgen]
    rfl
  subst hm
  exact trace_pow_pb (PowerBasis.ofAdjoinEqTop hint hadj) a ha k

private lemma cast_discr {K : Type*} [Field K] [NumberField K] {n : ℕ} (v : Fin n → 𝓞 K) :
    ((Algebra.discr ℤ v : ℤ) : ℚ) = Algebra.discr ℚ (fun i : Fin n => (v i : K)) := by
  rw [Algebra.discr_def, Algebra.discr_def, ← eq_intCast (Int.castRingHom ℚ), RingHom.map_det]
  congr 1
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.coe_trace_int]

private lemma discr_eq_det_sq {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (𝓞 K)) (v : Fin n → 𝓞 K) :
    Algebra.discr ℤ v = (b.toMatrix v).det ^ 2 * discr K := by
  have := Algebra.discr_of_matrix_vecMul b (b.toMatrix v)
  rw [Module.Basis.toMatrix_map_vecMul] at this
  rw [this, discr_eq_discr K b]

/-- If the discriminant of a family `v` of `n = [K:ℚ]` integers is a squarefree integer, then `v` is
a `ℤ`-basis of `𝓞 K`. -/
private lemma basis_of_squarefree_discr {K : Type*} [Field K] [NumberField K] (n : ℕ)
    (hn : Module.finrank ℚ K = n) (v : Fin n → 𝓞 K) (d : ℤ) (hd : Squarefree d)
    (hdisc : Algebra.discr ℚ (fun i : Fin n => (v i : K)) = d) :
    LinearIndependent ℤ v ∧ Submodule.span ℤ (Set.range v) = ⊤ := by
  have hrk : Module.finrank ℤ (𝓞 K) = n := by rw [RingOfIntegers.rank, hn]
  let b : Module.Basis (Fin n) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrk
  have h1 := discr_eq_det_sq b v
  have h4 : Algebra.discr ℤ v = d := by
    have h3 := cast_discr v
    rw [hdisc] at h3
    exact_mod_cast h3
  have h5 : (b.toMatrix v).det * (b.toMatrix v).det ∣ d := by
    rw [← h4, h1, sq]
    exact ⟨discr K, rfl⟩
  have h6 : IsUnit (b.toMatrix v).det := hd _ h5
  have h7 : IsUnit (b.det v) := by
    rwa [Module.Basis.det_apply]
  exact (Module.Basis.is_basis_iff_det b).2 h7

/-- If the discriminant of `1, α, …, α^{n-1}` is a squarefree integer `d`, then `ℤ[α] = 𝓞 K`. -/
lemma adjoin_eq_top_of_squarefree_discr {K : Type*} [Field K] [NumberField K] (n : ℕ)
    (hn : Module.finrank ℚ K = n) (α : 𝓞 K) (d : ℤ) (hd : Squarefree d)
    (hdisc : Algebra.discr ℚ (fun i : Fin n => (α : K) ^ (i : ℕ)) = d) :
    Algebra.adjoin ℤ {α} = ⊤ := by
  let v : Fin n → 𝓞 K := fun i => α ^ (i : ℕ)
  obtain ⟨_, hspan⟩ := basis_of_squarefree_discr n hn v d hd (by simpa [v] using hdisc)
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span ℤ (Set.range v) := by rw [hspan]; trivial
  have hle : Submodule.span ℤ (Set.range v) ≤ Subalgebra.toSubmodule (Algebra.adjoin ℤ {α}) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Subalgebra.pow_mem (Algebra.adjoin ℤ {α}) (Algebra.subset_adjoin (Set.mem_singleton α)) _
  exact hle hx


private lemma discr_eq_det_comp {K : Type*} [Field K] [NumberField K] (α : K) (hgen : ℚ⟮α⟯ = ⊤)
    (m : ℕ) (hm : (minpoly ℚ α).natDegree = m) (a : Fin m → ℤ)
    (ha : ∀ i : Fin m, (minpoly ℚ α).coeff i = (a i : ℚ)) :
    Algebra.discr ℚ (fun i : Fin m => α ^ (i : ℕ)) =
      ((Matrix.of fun i j : Fin m => Matrix.trace ((compMat m a) ^ ((i : ℕ) + j))).det : ℤ) := by
  rw [Algebra.discr_def, ← eq_intCast (Int.castRingHom ℚ), RingHom.map_det]
  congr 1
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, ← pow_add,
    trace_pow_eq_aux α hgen m hm a ha]

private lemma finrank_eq_natDegree {K : Type*} [Field K] [NumberField K] (α : K) (hgen : ℚ⟮α⟯ = ⊤) :
    Module.finrank ℚ K = (minpoly ℚ α).natDegree := by
  have h1 := IntermediateField.adjoin.finrank (K := ℚ) (x := α) (Algebra.IsIntegral.isIntegral _)
  rw [hgen, IntermediateField.finrank_top'] at h1
  exact h1

private lemma example_core {K : Type*} [Field K] [NumberField K] (α : 𝓞 K) (hgen : ℚ⟮(α : K)⟯ = ⊤)
    (m : ℕ) (hdeg : (minpoly ℚ (α : K)).natDegree = m) (a : Fin m → ℤ)
    (ha : ∀ i : Fin m, (minpoly ℚ (α : K)).coeff i = (a i : ℚ)) (d : ℤ) (hd : Squarefree d)
    (hdet : (Matrix.of fun i j : Fin m => Matrix.trace ((compMat m a) ^ ((i : ℕ) + j))).det = d) :
    Algebra.discr ℚ (fun i : Fin m => (α : K) ^ (i : ℕ)) = d ∧ Algebra.adjoin ℤ {α} = ⊤ := by
  have h := discr_eq_det_comp (α : K) hgen m hdeg a ha
  rw [hdet] at h
  exact ⟨h, adjoin_eq_top_of_squarefree_discr m ((finrank_eq_natDegree _ hgen).trans hdeg) α d hd h⟩

private lemma no_rat_root (a b c : ℤ) (hc : c ≠ 0) (B : ℤ) (hB : |c| ≤ B)
    (hz : ∀ z : ℤ, -B ≤ z → z ≤ B → z ^ 3 + a * z ^ 2 + b * z + c ≠ 0) (x : ℚ) :
    x ^ 3 + a * x ^ 2 + b * x + c ≠ 0 := by
  intro h
  have hi : IsIntegral ℤ x := by
    refine ⟨X ^ 3 + C (R := ℤ) a * X ^ 2 + C (R := ℤ) b * X + C (R := ℤ) c, by monicity!, ?_⟩
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    simp only [eq_intCast, algebraMap_int_eq]
    linear_combination h
  obtain ⟨z, hz'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  simp only [eq_intCast] at hz'
  subst hz'
  have h2 : z ^ 3 + a * z ^ 2 + b * z + c = 0 := by exact_mod_cast h
  have hdvd : z ∣ c := ⟨-(z ^ 2 + a * z + b), by linear_combination h2⟩
  have := Int.le_of_dvd (abs_pos.2 hc) ((abs_dvd_abs _ _).2 hdvd)
  have h3 := abs_le.1 (this.trans hB)
  exact hz z h3.1 h3.2 h2

private lemma sqfree_int (n : ℤ) (h : Squarefree n.natAbs) : Squarefree n := Int.squarefree_natAbs.1 h

private lemma det3_236 : (Matrix.of fun i j : Fin 3 =>
    Matrix.trace ((compMat 3 ![-1, -1, 0]) ^ ((i : ℕ) + j))).det = -23 := by
  decide +kernel

private lemma det3_237 : (Matrix.of fun i j : Fin 3 =>
    Matrix.trace ((compMat 3 ![1, 1, 0]) ^ ((i : ℕ) + j))).det = -31 := by
  decide +kernel

private lemma det5_239 : (Matrix.of fun i j : Fin 5 =>
    Matrix.trace ((compMat 5 ![-1, -1, 0, 0, 0]) ^ ((i : ℕ) + j))).det = 2869 := by
  decide +kernel

private lemma det3_238 : (Matrix.of fun i j : Fin 3 =>
    Matrix.trace ((compMat 3 ![8, -2, 1]) ^ ((i : ℕ) + j))).det = -2012 := by
  decide +kernel

private lemma irr238 : Irreducible (X ^ 3 + X ^ 2 - 2 * X + 8 : ℚ[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 3 + X ^ 2 - 2 * X + 8 : ℚ[X]).natDegree = 3 := by compute_degree!
    rw [this]; decide
  · intro x hx
    have := no_rat_root 1 (-2) 8 (by norm_num) 8 (by norm_num)
      (by intro z h1 h2; interval_cases z <;> norm_num) x
    apply this
    simp [IsRoot] at hx
    push_cast
    linarith

private lemma hK238 {K : Type*} [Field K] [NumberField K] (α : 𝓞 K)
    (hα : α ^ 3 + α ^ 2 - 2 * α + 8 = 0) :
    (α : K) ^ 3 + (α : K) ^ 2 - 2 * (α : K) + 8 = 0 := by
  have h := congrArg (fun x : 𝓞 K => (x : K)) hα
  push_cast at h
  exact h

private lemma discr238 {K : Type*} [Field K] [NumberField K] (α : 𝓞 K)
    (hα : α ^ 3 + α ^ 2 - 2 * α + 8 = 0) (hgen : ℚ⟮(α : K)⟯ = ⊤) :
    Module.finrank ℚ K = 3 ∧ Algebra.discr ℚ (fun i : Fin 3 => (α : K) ^ (i : ℕ)) = -2012 := by
  have hroot : aeval (α : K) (X ^ 3 + X ^ 2 - 2 * X + 8 : ℚ[X]) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, map_ofNat]
    exact hK238 α hα
  have hmin : minpoly ℚ (α : K) = X ^ 3 + X ^ 2 - 2 * X + 8 :=
    (minpoly.eq_of_irreducible_of_monic irr238 hroot (by monicity!)).symm
  have hdeg : (minpoly ℚ (α : K)).natDegree = 3 := by rw [hmin]; compute_degree!
  refine ⟨(finrank_eq_natDegree _ hgen).trans hdeg, ?_⟩
  have h := discr_eq_det_comp (α : K) hgen 3 hdeg ![8, -2, 1] (by
    intro i; fin_cases i <;> simp [hmin, coeff_X, coeff_X_pow])
  rw [det3_238] at h
  exact_mod_cast h

/-- `β = (α + α²)/2` is an algebraic integer. -/
private lemma exists_beta {K : Type*} [Field K] [NumberField K] (α : 𝓞 K)
    (hα : α ^ 3 + α ^ 2 - 2 * α + 8 = 0) :
    ∃ β : 𝓞 K, 2 * β = α + α ^ 2 ∧ α ^ 2 = 2 * β - α ∧ α * β = α - 4 ∧ β * β = β - 2 * α - 2 := by
  have hK := hK238 α hα
  have hint : IsIntegral ℤ (((α : K) + (α : K) ^ 2) / 2) := by
    refine ⟨X ^ 3 - C (R := ℤ) 2 * X ^ 2 + C (R := ℤ) 3 * X - C (R := ℤ) 10, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    simp only [eq_intCast, algebraMap_int_eq]
    push_cast
    linear_combination (1 / 8 : K) * ((α : K) ^ 3 + 2 * (α : K) ^ 2 - (α : K) - 10) * hK
  have hKA : (algebraMap (𝓞 K) K α) ^ 3 + (algebraMap (𝓞 K) K α) ^ 2 - 2 * algebraMap (𝓞 K) K α + 8 = 0 := hK
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 K, algebraMap (𝓞 K) K β =
      (algebraMap (𝓞 K) K α + (algebraMap (𝓞 K) K α) ^ 2) / 2 := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨β, ?_, ?_, ?_, ?_⟩ <;> apply (IsFractionRing.injective (𝓞 K) K) <;>
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, hβ]
  · ring
  · ring
  · linear_combination (1 / 2 : K) * hKA
  · linear_combination (1 / 4 : K) * (algebraMap (𝓞 K) K α + 1) * hKA

private lemma basis238 {K : Type*} [Field K] [NumberField K] (α β : 𝓞 K)
    (hα : α ^ 3 + α ^ 2 - 2 * α + 8 = 0) (hgen : ℚ⟮(α : K)⟯ = ⊤) (hβ : 2 * β = α + α ^ 2) :
    discr K = -503 ∧ LinearIndependent ℤ ![1, α, β] ∧
      Submodule.span ℤ (Set.range ![1, α, β]) = ⊤ := by
  obtain ⟨hrk, hD⟩ := discr238 α hα hgen
  have hβK : 2 * (β : K) = (α : K) + (α : K) ^ 2 := by
    have h := congrArg (fun x : 𝓞 K => (x : K)) hβ
    push_cast at h
    exact h
  let v : Fin 3 → 𝓞 K := ![1, α, β]
  let P : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 1 / 2; 0, 0, 1 / 2]
  have hv : Algebra.discr ℚ (fun i : Fin 3 => (v i : K)) = -503 := by
    have h := Algebra.discr_of_matrix_vecMul (fun i : Fin 3 => (α : K) ^ (i : ℕ)) P
    have e : Matrix.vecMul (fun i : Fin 3 => (α : K) ^ (i : ℕ)) (P.map (algebraMap ℚ K)) =
        fun i : Fin 3 => (v i : K) := by
      funext i
      fin_cases i
      · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, P, v]
      · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, P, v]
      · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, P, v]
        linear_combination (-1 / 2 : K) * hβK
    rw [e, hD] at h
    rw [h]
    have : P.det = 1 / 2 := by
      rw [Matrix.det_fin_three]; simp [P]
    rw [this]; norm_num
  have hsq : Squarefree (-503 : ℤ) := sqfree_int _ (by decide +kernel)
  obtain ⟨hli, hspan⟩ := basis_of_squarefree_discr 3 hrk v (-503) hsq hv
  refine ⟨?_, hli, hspan⟩
  let bv : Module.Basis (Fin 3) ℤ (𝓞 K) := Module.Basis.mk hli (le_of_eq hspan.symm)
  have h1 := discr_eq_discr K bv
  have h2 : Algebra.discr ℤ bv = Algebra.discr ℤ v := by
    congr 1
    exact Module.Basis.coe_mk _ _
  have h3 := cast_discr v
  rw [hv] at h3
  rw [← h1, h2]
  exact_mod_cast h3

/-- If `θ` is a root of a monic polynomial `g` of degree `n` over `ℤ`, then `ℤ[θ]` is spanned by
`1, θ, …, θ^{n-1}`. -/
private lemma mem_span_pow_of_monic {A : Type*} [CommRing A] [Algebra ℤ A] (θ : A) (g : ℤ[X])
    (hg : g.Monic) (n : ℕ) (hn0 : 0 < n) (hn : g.natDegree = n) (hroot : aeval θ g = 0) (y : A)
    (hy : y ∈ Algebra.adjoin ℤ {θ}) :
    y ∈ Submodule.span ℤ (Set.range fun i : Fin n => θ ^ (i : ℕ)) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := hy
  have hdecomp : aeval θ p = aeval θ (p %ₘ g) := by
    conv_lhs => rw [← modByMonic_add_div p g]
    simp [hroot]
  have hlt : (p %ₘ g).natDegree < n := by
    rw [← hn]
    refine natDegree_modByMonic_lt p hg ?_
    rintro rfl
    simp at hn
    omega
  change aeval θ p ∈ _
  rw [hdecomp, aeval_eq_sum_range' hlt]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hmem : θ ^ i ∈ Submodule.span ℤ (Set.range fun i : Fin n => θ ^ (i : ℕ)) :=
    Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩
  have h2 := Submodule.smul_mem (Submodule.span ℤ (Set.range fun i : Fin n => θ ^ (i : ℕ)))
    ((p %ₘ g).coeff i) hmem
  simpa [Algebra.smul_def, zsmul_eq_mul] using h2

private lemma F_even (y z : ℤ) :
    (y * (2 * y ^ 2 + z ^ 2) - z * (-y ^ 2 + 2 * y * z - 2 * z ^ 2)) % 2 = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, y = 2 * a + y % 2 := ⟨y / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, z = 2 * b + z % 2 := ⟨z / 2, by omega⟩
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  have hz : z % 2 = 0 ∨ z % 2 = 1 := by omega
  rw [ha, hb]
  rcases hy with hy | hy <;> rcases hz with hz | hz <;> rw [hy, hz] <;> ring_nf <;> omega

private lemma nogen238 {K : Type*} [Field K] [NumberField K] (α β : 𝓞 K)
    (R1 : α ^ 2 = 2 * β - α) (R2 : α * β = α - 4) (R3 : β * β = β - 2 * α - 2)
    (hrk : Module.finrank ℚ K = 3)
    (hli : LinearIndependent ℤ ![1, α, β])
    (hspan : Submodule.span ℤ (Set.range ![1, α, β]) = ⊤) (θ : 𝓞 K) :
    Algebra.adjoin ℤ {θ} ≠ ⊤ := by
  intro htop
  let v : Fin 3 → 𝓞 K := ![1, α, β]
  let bv : Module.Basis (Fin 3) ℤ (𝓞 K) := Module.Basis.mk hli (le_of_eq hspan.symm)
  have hθ : θ ∈ Submodule.span ℤ (Set.range v) := by rw [hspan]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hθ
  obtain ⟨c, hc⟩ := hθ
  obtain ⟨x, y, z, hθeq⟩ : ∃ x y z : ℤ, θ = (x : 𝓞 K) + (y : 𝓞 K) * α + (z : 𝓞 K) * β :=
    ⟨c 0, c 1, c 2, by rw [← hc]; simp [Fin.sum_univ_three, v, zsmul_eq_mul]⟩
  clear hc c
  let θ' : 𝓞 K := (y : 𝓞 K) * α + (z : 𝓞 K) * β
  have hθθ' : θ = θ' + (x : 𝓞 K) := by rw [hθeq]; ring
  have htop' : Algebra.adjoin ℤ {θ'} = ⊤ := by
    rw [eq_top_iff, ← htop]
    apply Algebra.adjoin_le
    rw [Set.singleton_subset_iff, hθθ']
    refine add_mem (Algebra.self_mem_adjoin_singleton ℤ θ') ?_
    have : (x : 𝓞 K) = algebraMap ℤ (𝓞 K) x := by simp
    rw [this]
    exact Subalgebra.algebraMap_mem _ x
  have hcp := Algebra.aeval_charpoly_leftMulMatrix bv θ'
  have hgm : (Algebra.leftMulMatrix bv θ').charpoly.Monic := Matrix.charpoly_monic _
  have hgd : (Algebra.leftMulMatrix bv θ').charpoly.natDegree = 3 := by
    rw [Matrix.charpoly_natDegree_eq_dim]; simp
  have hspan' : ⊤ ≤ Submodule.span ℤ (Set.range fun i : Fin 3 => θ' ^ (i : ℕ)) := by
    intro y' _
    exact mem_span_pow_of_monic θ' _ hgm 3 (by norm_num) hgd hcp y' (by rw [htop']; trivial)
  have hcard : Fintype.card (Fin 3) = Module.finrank ℤ (𝓞 K) := by
    simp [RingOfIntegers.rank, hrk]
  have hliw := linearIndependent_of_top_le_span_of_card_eq_finrank hspan' hcard
  have hunit := (Module.Basis.is_basis_iff_det bv).1 ⟨hliw, top_le_iff.1 hspan'⟩
  rw [Module.Basis.det_apply] at hunit
  let P : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, -8 * y * z - 2 * z ^ 2;
    0, y, -y ^ 2 + 2 * y * z - 2 * z ^ 2; 0, z, 2 * y ^ 2 + z ^ 2]
  have hw : ∀ j : Fin 3, θ' ^ (j : ℕ) = ∑ i, P i j • bv i := by
    intro j
    fin_cases j
    · simp [Fin.sum_univ_three, P, bv]
    · simp [Fin.sum_univ_three, P, bv, θ', zsmul_eq_mul]
    · simp [Fin.sum_univ_three, P, bv, θ', zsmul_eq_mul]
      linear_combination (y : 𝓞 K) ^ 2 * R1 + 2 * (y : 𝓞 K) * z * R2 + (z : 𝓞 K) ^ 2 * R3
  have hmat : bv.toMatrix (fun i : Fin 3 => θ' ^ (i : ℕ)) = P := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hw j, Module.Basis.repr_sum_self]
  rw [hmat] at hunit
  have key : P.det = y * (2 * y ^ 2 + z ^ 2) - z * (-y ^ 2 + 2 * y * z - 2 * z ^ 2) := by
    rw [Matrix.det_fin_three]; simp [P]; ring
  rw [key] at hunit
  have := F_even y z
  rcases Int.isUnit_iff.1 hunit with h | h <;> omega

/-- **Example 2.36.** $X^3 - X - 1$ is irreducible over $\mathbb Q$; for a root $\alpha$ generating the number field
$K$, $D(1, \alpha, \alpha^2) = -23$, and $\mathbb Z[\alpha] = \mathcal O_K$. -/
@[kb "milne2020ant" "v3.08, Example 2.36, p. 38"]
theorem example_2_36 : Irreducible (X ^ 3 - X - 1 : ℚ[X]) ∧
    ∀ (K : Type*) [Field K] [NumberField K] (α : 𝓞 K), α ^ 3 - α - 1 = 0 → ℚ⟮(α : K)⟯ = ⊤ →
      Algebra.discr ℚ (fun i : Fin 3 => (α : K) ^ (i : ℕ)) = -23 ∧ Algebra.adjoin ℤ {α} = ⊤ := by
  have irr : Irreducible (X ^ 3 - X - 1 : ℚ[X]) := X_pow_sub_X_sub_one_irreducible_rat (by norm_num)
  refine ⟨irr, fun K _ _ α hα hgen => ?_⟩
  have hroot : aeval (α : K) (X ^ 3 - X - 1 : ℚ[X]) = 0 := by
    have := congrArg (fun x : 𝓞 K => (x : K)) hα
    simpa using this
  have hmin : minpoly ℚ (α : K) = X ^ 3 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic irr hroot (by monicity!)).symm
  have hdeg : (minpoly ℚ (α : K)).natDegree = 3 := by rw [hmin]; compute_degree!
  have := example_core α hgen 3 hdeg ![-1, -1, 0] (by
    intro i; fin_cases i <;> simp [hmin, coeff_X, coeff_one, coeff_X_pow]) (-23)
    (sqfree_int _ (by decide +kernel)) det3_236
  exact_mod_cast this

/-- **Example 2.37.** $X^3 + X + 1$ is irreducible over $\mathbb Q$; for a root $\alpha$ generating the number field
$K$, $D(1, \alpha, \alpha^2) = -31$, and $\mathbb Z[\alpha] = \mathcal O_K$. -/
@[kb "milne2020ant" "v3.08, Example 2.37, p. 38"]
theorem example_2_37 : Irreducible (X ^ 3 + X + 1 : ℚ[X]) ∧
    ∀ (K : Type*) [Field K] [NumberField K] (α : 𝓞 K), α ^ 3 + α + 1 = 0 → ℚ⟮(α : K)⟯ = ⊤ →
      Algebra.discr ℚ (fun i : Fin 3 => (α : K) ^ (i : ℕ)) = -31 ∧ Algebra.adjoin ℤ {α} = ⊤ := by
  have irr : Irreducible (X ^ 3 + X + 1 : ℚ[X]) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · have : (X ^ 3 + X + 1 : ℚ[X]).natDegree = 3 := by compute_degree!
      rw [this]; decide
    · intro x hx
      have := no_rat_root 0 1 1 (by norm_num) 1 (by norm_num)
        (by intro z h1 h2; interval_cases z <;> norm_num) x
      apply this
      simp [IsRoot] at hx
      push_cast
      linarith
  refine ⟨irr, fun K _ _ α hα hgen => ?_⟩
  have hroot : aeval (α : K) (X ^ 3 + X + 1 : ℚ[X]) = 0 := by
    have := congrArg (fun x : 𝓞 K => (x : K)) hα
    simpa using this
  have hmin : minpoly ℚ (α : K) = X ^ 3 + X + 1 :=
    (minpoly.eq_of_irreducible_of_monic irr hroot (by monicity!)).symm
  have hdeg : (minpoly ℚ (α : K)).natDegree = 3 := by rw [hmin]; compute_degree!
  have := example_core α hgen 3 hdeg ![1, 1, 0] (by
    intro i; fin_cases i <;> simp [hmin, coeff_X, coeff_one, coeff_X_pow]) (-31)
    (sqfree_int _ (by decide +kernel)) det3_237
  exact_mod_cast this

/-- **Example 2.38** (Dedekind), the computational part. $X^3 + X^2 - 2X + 8$ is irreducible over $\mathbb Q$; for a
root $\alpha$ generating $K$, $D(1, \alpha, \alpha^2) = -2012 = -4 \cdot 503$, $\mathbb Z[\alpha] \neq \mathcal O_K$,
and $\mathrm{disc}(\mathcal O_K/\mathbb Z) = -503$. -/
@[kb "milne2020ant" "v3.08, Example 2.38, p. 39"]
theorem example_2_38 : Irreducible (X ^ 3 + X ^ 2 - 2 * X + 8 : ℚ[X]) ∧
    ∀ (K : Type*) [Field K] [NumberField K] (α : 𝓞 K), α ^ 3 + α ^ 2 - 2 * α + 8 = 0 → ℚ⟮(α : K)⟯ = ⊤ →
      Algebra.discr ℚ (fun i : Fin 3 => (α : K) ^ (i : ℕ)) = -2012 ∧ Algebra.adjoin ℤ {α} ≠ ⊤ ∧
        discr K = -503 := by
  refine ⟨irr238, fun K _ _ α hα hgen => ?_⟩
  obtain ⟨hrk, hD⟩ := discr238 α hα hgen
  obtain ⟨β, h1, R1, R2, R3⟩ := exists_beta α hα
  obtain ⟨hdK, hli, hspan⟩ := basis238 α β hα hgen h1
  exact ⟨hD, nogen238 α β R1 R2 R3 hrk hli hspan α, hdK⟩

/-- **Example 2.38** (Dedekind), the non-monogenic part: the field $K$ generated by a root of
$X^3 + X^2 - 2X + 8$ has no integral basis of the form $1, \theta, \theta^2$ (it is not monogenic). -/
@[kb "milne2020ant" "v3.08, Example 2.38 and footnote 3, p. 39"]
theorem example_2_38_not_monogenic (K : Type*) [Field K] [NumberField K] (α : 𝓞 K)
    (hα : α ^ 3 + α ^ 2 - 2 * α + 8 = 0) (hgen : ℚ⟮(α : K)⟯ = ⊤) : ¬ IsMonogenic K := by
  rintro ⟨θ, hθ⟩
  obtain ⟨hrk, hD⟩ := discr238 α hα hgen
  obtain ⟨β, h1, R1, R2, R3⟩ := exists_beta α hα
  obtain ⟨hdK, hli, hspan⟩ := basis238 α β hα hgen h1
  exact nogen238 α β R1 R2 R3 hrk hli hspan θ hθ

/-- **Example 2.39.** $X^5 - X - 1$ is irreducible over $\mathbb Q$; for a root $\alpha$ generating $K$,
$D(1, \alpha, \dots, \alpha^4) = 2869 = 19 \cdot 151$ (square-free), and $\mathbb Z[\alpha] = \mathcal O_K$.

Milne deduces irreducibility from irreducibility modulo $3$; here it may also be taken from Mathlib's
`Polynomial.X_pow_sub_X_sub_one_irreducible_rat` (Selmer). -/
@[kb "milne2020ant" "v3.08, Example 2.39, p. 39"]
theorem example_2_39 : Irreducible (X ^ 5 - X - 1 : ℚ[X]) ∧
    ∀ (K : Type*) [Field K] [NumberField K] (α : 𝓞 K), α ^ 5 - α - 1 = 0 → ℚ⟮(α : K)⟯ = ⊤ →
      Algebra.discr ℚ (fun i : Fin 5 => (α : K) ^ (i : ℕ)) = 2869 ∧ Algebra.adjoin ℤ {α} = ⊤ := by
  have irr : Irreducible (X ^ 5 - X - 1 : ℚ[X]) := X_pow_sub_X_sub_one_irreducible_rat (by norm_num)
  refine ⟨irr, fun K _ _ α hα hgen => ?_⟩
  have hroot : aeval (α : K) (X ^ 5 - X - 1 : ℚ[X]) = 0 := by
    have := congrArg (fun x : 𝓞 K => (x : K)) hα
    simpa using this
  have hmin : minpoly ℚ (α : K) = X ^ 5 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic irr hroot (by monicity!)).symm
  have hdeg : (minpoly ℚ (α : K)).natDegree = 5 := by rw [hmin]; compute_degree!
  have := example_core α hgen 5 hdeg ![-1, -1, 0, 0, 0] (by
    intro i; fin_cases i <;> simp [hmin, coeff_X, coeff_one, coeff_X_pow]) 2869
    (sqfree_int _ (by decide +kernel)) det5_239
  exact_mod_cast this

private lemma rat_int_of_isIntegral (q : ℚ) (h : IsIntegral ℤ q) : ∃ z : ℤ, (z : ℚ) = q := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨z, by simpa using hz⟩

private lemma no_rat_sqrt (m : ℤ) (hm : Squarefree m) (hm1 : m ≠ 1) :
    ¬ ∃ q : ℚ, q ^ 2 = (m : ℚ) := by
  rintro ⟨q, hq⟩
  have hi : IsIntegral ℤ q := by
    refine ⟨X ^ 2 - C (R := ℤ) m, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    simp only [eq_intCast, algebraMap_int_eq]
    linear_combination hq
  obtain ⟨z, rfl⟩ := rat_int_of_isIntegral q hi
  have h2 : z * z = m := by exact_mod_cast (by rw [← hq]; ring : (z : ℚ) * z = m)
  have hu : IsUnit z := hm z ⟨1, by rw [mul_one]; exact h2.symm⟩
  rcases Int.isUnit_iff.1 hu with rfl | rfl <;> simp_all

/-- Rational numbers `v` with `m * v^2 ∈ ℤ`, `m` squarefree, are integers. -/
private lemma int_of_mul_sq (m : ℤ) (hm : Squarefree m) (v : ℚ) (l : ℤ) (h : (m : ℚ) * v ^ 2 = l) :
    ∃ j : ℤ, (j : ℚ) = v := by
  have hm0 : m ≠ 0 := by rintro rfl; exact not_squarefree_zero hm
  have hden : (v.den : ℤ) * v.den ∣ m := by
    have h1 : (m : ℚ) * (v.num : ℚ) ^ 2 = l * (v.den : ℚ) ^ 2 := by
      have : v = (v.num : ℚ) / v.den := (Rat.num_div_den v).symm
      have hd : (v.den : ℚ) ≠ 0 := by exact_mod_cast v.den_nz
      rw [this] at h
      field_simp at h
      linarith
    have h2 : m * v.num ^ 2 = l * (v.den : ℤ) ^ 2 := by exact_mod_cast h1
    have h3 : ((v.den : ℤ) ^ 2) ∣ m * v.num ^ 2 := ⟨l, by rw [h2]; ring⟩
    have hcop : IsCoprime ((v.den : ℤ) ^ 2) (v.num ^ 2) := by
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := v.reduced
      rw [Int.gcd_comm]
      simpa [Int.gcd] using this
    have := hcop.dvd_of_dvd_mul_right h3
    rwa [sq] at this
  have hu := hm _ hden
  have : (v.den : ℤ) = 1 := by
    rcases Int.isUnit_iff.1 hu with h | h
    · exact h
    · omega
  have hd1 : v.den = 1 := by exact_mod_cast this
  exact ⟨v.num, Rat.coe_int_num_of_den_eq_one hd1⟩

private lemma exists_uv {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (m : ℤ)
    (hm : Squarefree m) (hm1 : m ≠ 1) (s : K) (hs : s ^ 2 = m) (x : K) :
    ∃ u v : ℚ, x = u + v * s := by
  have hli : LinearIndependent ℚ ![(1 : K), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simp at hab
      exact ⟨hab, rfl⟩
    · exfalso
      have hs' : s = algebraMap ℚ K (-a / b) := by
        simp only [Algebra.smul_def, mul_one] at hab
        have hb' : (algebraMap ℚ K b) ≠ 0 := by simpa using hb
        rw [map_div₀, map_neg]
        field_simp
        linear_combination hab
      apply no_rat_sqrt m hm hm1
      refine ⟨-a / b, ?_⟩
      apply (algebraMap ℚ K).injective
      rw [map_pow, ← hs', hs]
      simp
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hK])
  have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), s]) := by rw [hspan]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc]
  simp [Fin.sum_univ_two, Algebra.smul_def]

private lemma integral_cond {K : Type*} [Field K] [NumberField K] (m : ℤ)
    (hm : Squarefree m) (hm1 : m ≠ 1) (s : K) (hs : s ^ 2 = m) (u v : ℚ)
    (hx : IsIntegral ℤ ((u : K) + v * s)) :
    ∃ k j l : ℤ, u = k / 2 ∧ v = j / 2 ∧ k ^ 2 - m * j ^ 2 = 4 * l := by
  by_cases hv : v = 0
  · subst hv
    have h1 : IsIntegral ℤ (algebraMap ℚ K u) := by simpa using hx
    have h2 : IsIntegral ℤ u := isIntegral_algebraMap_iff.1 h1
    obtain ⟨z, hz⟩ := rat_int_of_isIntegral u h2
    refine ⟨2 * z, 0, z ^ 2, ?_, by simp, by ring⟩
    rw [← hz]; push_cast; ring
  · set x : K := (u : K) + v * s with hxdef
    have hsq : ∀ q : ℚ, algebraMap ℚ K q ≠ s := by
      intro q hq
      apply no_rat_sqrt m hm hm1
      refine ⟨q, ?_⟩
      apply (algebraMap ℚ K).injective
      rw [map_pow, hq, hs]
      simp
    have hxnot : x ∉ (algebraMap ℚ K).range := by
      rintro ⟨q, hq⟩
      apply hsq ((q - u) / v)
      have hvK : (v : K) ≠ 0 := by simpa using hv
      rw [map_div₀, map_sub, hq]
      simp only [eq_ratCast]
      rw [hxdef]
      field_simp
      ring
    have hxint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    obtain ⟨a1, ha1⟩ : ∃ a1 : ℚ, a1 = 2 * u := ⟨_, rfl⟩
    obtain ⟨a0, ha0⟩ : ∃ a0 : ℚ, a0 = u ^ 2 - m * v ^ 2 := ⟨_, rfl⟩
    set g : ℚ[X] := X ^ 2 - C a1 * X + C a0 with hg
    have hgmonic : g.Monic := by rw [hg]; monicity!
    have hgdeg : g.natDegree = 2 := by rw [hg]; compute_degree!
    have hgroot : aeval x g = 0 := by
      simp only [hg, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
      have : (v : K) ^ 2 * s ^ 2 = (v : K) ^ 2 * m := by rw [hs]
      simp only [eq_ratCast, hxdef, ha1, ha0]
      push_cast
      linear_combination (v : K) ^ 2 * hs
    have hdvd : minpoly ℚ x ∣ g := minpoly.dvd ℚ x hgroot
    have hle : (minpoly ℚ x).natDegree ≤ 2 := hgdeg ▸ natDegree_le_of_dvd hdvd hgmonic.ne_zero
    have hne1 : (minpoly ℚ x).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]; exact hxnot
    have hpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hxint
    have hge : g.natDegree ≤ (minpoly ℚ x).natDegree := by omega
    have heq : g = minpoly ℚ x :=
      eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxint) hgmonic hdvd hge
    have hZ := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx
    set c0 := (minpoly ℤ x).coeff 0
    set c1 := (minpoly ℤ x).coeff 1
    have e0 : (u ^ 2 - m * v ^ 2) = (c0 : ℚ) := by
      have := congrArg (fun p => p.coeff 0) (heq.trans hZ)
      simp only [hg, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C, coeff_map] at this
      rw [← ha0]
      simpa [c0] using this
    have e1 : (-(2 * u)) = (c1 : ℚ) := by
      have := congrArg (fun p => p.coeff 1) (heq.trans hZ)
      simp only [hg, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C, coeff_map] at this
      rw [← ha1]
      simpa [c1] using this
    have hu : u = ((-c1 : ℤ) : ℚ) / 2 := by push_cast; linarith
    have hint2 : (m : ℚ) * (2 * v) ^ 2 = ((c1 ^ 2 - 4 * c0 : ℤ) : ℚ) := by
      push_cast
      have : u = -(c1 : ℚ) / 2 := by linarith
      rw [← e0, this]
      ring
    obtain ⟨j, hj⟩ := int_of_mul_sq m hm (2 * v) _ hint2
    refine ⟨-c1, j, c0, hu, by rw [hj]; ring, ?_⟩
    have : (((-c1 : ℤ) : ℚ)) ^ 2 - (m : ℚ) * (j : ℚ) ^ 2 = 4 * (c0 : ℚ) := by
      push_cast
      rw [hj]
      have := hint2
      push_cast at this
      linarith
    exact_mod_cast this

private lemma parity_23 (m k j l : ℤ) (h : k ^ 2 - m * j ^ 2 = 4 * l) (hm : m % 4 = 2 ∨ m % 4 = 3) :
    k % 2 = 0 ∧ j % 2 = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, m = 4 * c + m % 4 := ⟨m / 4, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, k = 2 * a + k % 2 := ⟨k / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, j = 2 * b + j % 2 := ⟨j / 2, by omega⟩
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rw [hc, ha, hb] at h
  rcases hk with hk | hk <;> rcases hj with hj | hj <;> rcases hm with hm | hm <;>
    rw [hk, hj, hm] at h <;> ring_nf at h <;> omega

private lemma parity_1 (m k j l : ℤ) (h : k ^ 2 - m * j ^ 2 = 4 * l) (hm : m % 4 = 1) :
    k % 2 = j % 2 := by
  obtain ⟨c, hc⟩ : ∃ c, m = 4 * c + m % 4 := ⟨m / 4, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, k = 2 * a + k % 2 := ⟨k / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, j = 2 * b + j % 2 := ⟨j / 2, by omega⟩
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rw [hc, ha, hb] at h
  rcases hk with hk | hk <;> rcases hj with hj | hj <;>
    rw [hk, hj, hm] at h <;> ring_nf at h <;> omega

/-- **Example 2.41.** Let $K = \mathbb Q(\sqrt m)$ with $m \ne 1$ a square-free integer ($s \in K$, $s^2 = m$). If
$m \equiv 2, 3 \bmod 4$, then $\{1, \sqrt m\}$ is an integral basis: the algebraic integers of $K$ are the
$a + b\sqrt m$, $a, b \in \mathbb Z$. If $m \equiv 1 \bmod 4$, then $\{1, (1+\sqrt m)/2\}$ is an integral basis.
(QuadFormsKB proves the same description as `QuadFormsKB.Binary.isIntegral_iff`, for $\mathbb Q(\sqrt D)$ with $D$ a
fundamental discriminant, citing Marcus.) -/
@[kb "milne2020ant" "v3.08, Example 2.41, p. 39"]
theorem example_2_41 (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (m : ℤ)
    (hm : Squarefree m) (hm1 : m ≠ 1) (s : K) (hs : s ^ 2 = m) :
    (m % 4 = 2 ∨ m % 4 = 3 → ∀ x : K, IsIntegral ℤ x ↔ ∃ a b : ℤ, x = a + b * s) ∧
      (m % 4 = 1 → ∀ x : K, IsIntegral ℤ x ↔ ∃ a b : ℤ, x = a + b * ((1 + s) / 2)) := by
  have hint : ∀ a : ℤ, IsIntegral ℤ (a : K) := fun a => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := a)
  have hsint : IsIntegral ℤ s := by
    refine ⟨X ^ 2 - C (R := ℤ) m, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    simp only [eq_intCast, algebraMap_int_eq]
    rw [hs]; simp
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  constructor
  · intro hmod x
    constructor
    · intro hx
      obtain ⟨u, v, rfl⟩ := exists_uv hK m hm hm1 s hs x
      obtain ⟨k, j, l, hu, hv, hkj⟩ := integral_cond m hm hm1 s hs u v hx
      obtain ⟨hk, hj⟩ := parity_23 m k j l hkj hmod
      refine ⟨k / 2, j / 2, ?_⟩
      have e1 : (u : ℚ) = ((k / 2 : ℤ) : ℚ) := by
        rw [hu]; have : (k : ℚ) = 2 * ((k / 2 : ℤ) : ℚ) := by exact_mod_cast (by omega : k = 2 * (k / 2))
        rw [this]; ring
      have e2 : (v : ℚ) = ((j / 2 : ℤ) : ℚ) := by
        rw [hv]; have : (j : ℚ) = 2 * ((j / 2 : ℤ) : ℚ) := by exact_mod_cast (by omega : j = 2 * (j / 2))
        rw [this]; ring
      rw [e1, e2]
      simp
    · rintro ⟨a, b, rfl⟩
      exact (hint a).add ((hint b).mul hsint)
  · intro hmod x
    constructor
    · intro hx
      obtain ⟨u, v, rfl⟩ := exists_uv hK m hm hm1 s hs x
      obtain ⟨k, j, l, hu, hv, hkj⟩ := integral_cond m hm hm1 s hs u v hx
      have hp := parity_1 m k j l hkj hmod
      refine ⟨(k - j) / 2, j, ?_⟩
      have e1 : (k : ℚ) - j = 2 * (((k - j) / 2 : ℤ) : ℚ) := by
        exact_mod_cast (by omega : k - j = 2 * ((k - j) / 2))
      have : ((u : ℚ) : K) = (((k - j) / 2 : ℤ) : K) + (j : K) / 2 := by
        have : (u : ℚ) = (((k - j) / 2 : ℤ) : ℚ) + (j : ℚ) / 2 := by
          rw [hu]; linarith
        rw [this]; push_cast; ring
      rw [this, hv]
      push_cast
      field_simp
      ring
    · rintro ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, m = 4 * c + 1 := ⟨m / 4, by omega⟩
      have hy : IsIntegral ℤ ((1 + s) / 2) := by
        refine ⟨X ^ 2 - X - C (R := ℤ) c, by monicity!, ?_⟩
        simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
        simp only [eq_intCast, algebraMap_int_eq]
        have hs' : s ^ 2 = 4 * c + 1 := by rw [hs, hc]; push_cast; ring
        field_simp
        linear_combination hs'
      exact (hint a).add ((hint b).mul hy)

end NumberFieldKB.MilneANT
