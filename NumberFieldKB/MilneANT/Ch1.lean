import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 1: the items not in Mathlib

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers.

* **Remark 1.2** (`remark_1_2_ideal_eq_pi`, `remark_1_2_isPrime_pi_iff`): in a finite product of rings
  $A_1 \times \dots \times A_m$ every ideal is a product $\mathfrak a_1 \times \dots \times \mathfrak a_m$, and
  such a product is prime iff one factor is prime and all the others are the whole ring.
* **Remark 1.5** (`remark_1_5`): the ring of all algebraic integers is not noetherian.
* **Theorem 1.18** (`thm_1_18`): for $K/k$ finite separable and $\Omega/k$ any field extension,
  $\Omega \otimes_k K$ is a finite product of finite separable field extensions $\Omega_i$ of $\Omega$; the image
  $\alpha_i$ of a primitive element $\alpha$ generates $\Omega_i$, and the minimal polynomial of $\alpha$ is the
  product of the minimal polynomials of the $\alpha_i$.
* **Example 1.19** (`example_1_19`): for a number field $K$, $\mathbb C \otimes_{\mathbb Q} K \cong \mathbb C^r$
  with coordinates indexed by the $r = [K:\mathbb Q]$ embeddings $\sigma : K \to \mathbb C$ and
  $1 \otimes \beta \mapsto (\sigma\beta)_\sigma$.

The tensor products are written $\Omega \otimes_k K$ (scalars extended on the left, so that Mathlib's
`Algebra.TensorProduct.leftAlgebra` makes it an $\Omega$-algebra); Milne writes $K \otimes_k \Omega$, which is
canonically isomorphic (`Algebra.TensorProduct.comm`).
-/

open Polynomial TensorProduct IntermediateField

namespace NumberFieldKB.MilneANT

/-- **Remark 1.2, ideals.** Every ideal $I$ of a finite product $\prod_i A_i$ of commutative rings is the product
of the ideals $\mathfrak a_i = \pi_i(I)$ (its images under the projections). -/
@[kb "milne2020ant" "v3.08, Remark 1.2, p. 15"]
theorem remark_1_2_ideal_eq_pi {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, CommRing (A i)]
    (I : Ideal (∀ i, A i)) : I = Ideal.pi (fun i => I.map (Pi.evalRingHom A i)) := by
  exact (Ideal.piOrderIso.symm_apply_apply I).symm

/-- **Remark 1.2, prime ideals.** A product ideal $\mathfrak a_1 \times \dots \times \mathfrak a_m$ of a finite
product of commutative rings is prime iff there is a $j$ with $\mathfrak a_j$ prime in $A_j$ and
$\mathfrak a_i = A_i$ for all $i \ne j$. -/
@[kb "milne2020ant" "v3.08, Remark 1.2, p. 15"]
theorem remark_1_2_isPrime_pi_iff {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, CommRing (A i)]
    (a : ∀ i, Ideal (A i)) :
    (Ideal.pi a).IsPrime ↔ ∃ j, (a j).IsPrime ∧ ∀ i, i ≠ j → a i = ⊤ := by
  classical
  constructor
  · intro hP
    have hne : ∀ i, ∀ j, i ≠ j → a i ≠ ⊤ → a j ≠ ⊤ → False := by
      intro i j hij hi hj
      have hm : (Pi.single i (1 : A i) : ∀ i, A i) * (1 - Pi.single i 1) ∈ Ideal.pi a := by
        have : (Pi.single i (1 : A i) : ∀ i, A i) * (1 - Pi.single i 1) = 0 := by
          ext l
          by_cases h : l = i
          · subst h; simp
          · simp [h]
        rw [this]; exact Ideal.zero_mem _
      rcases hP.mem_or_mem hm with h | h
      · have := (Ideal.mem_pi _ _).1 h i
        simp at this
        exact hi ((Ideal.eq_top_iff_one _).2 this)
      · have := (Ideal.mem_pi _ _).1 h j
        simp [hij.symm] at this
        exact hj ((Ideal.eq_top_iff_one _).2 this)
    have hex : ∃ j, a j ≠ ⊤ := by
      by_contra hcon
      push Not at hcon
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one, Ideal.mem_pi]
      intro i
      rw [Pi.one_apply, ← Ideal.eq_top_iff_one]
      exact hcon i
    obtain ⟨j, hj⟩ := hex
    have hall : ∀ i, i ≠ j → a i = ⊤ := by
      intro i hij
      by_contra h
      exact hne i j hij h hj
    refine ⟨j, ?_, hall⟩
    refine Ideal.isPrime_iff.2 ⟨hj, fun {u v} huv => ?_⟩
    have hm : (Pi.single j u : ∀ i, A i) * Pi.single j v ∈ Ideal.pi a := by
      rw [← Pi.single_mul, Ideal.mem_pi]
      intro l
      by_cases h : l = j
      · subst h; simpa using huv
      · simp [h]
    rcases hP.mem_or_mem hm with h | h
    · left; simpa using (Ideal.mem_pi _ _).1 h j
    · right; simpa using (Ideal.mem_pi _ _).1 h j
  · rintro ⟨j, hj, hall⟩
    refine Ideal.isPrime_iff.2 ⟨?_, fun {x y} hxy => ?_⟩
    · intro htop
      rw [Ideal.eq_top_iff_one, Ideal.mem_pi] at htop
      exact hj.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using htop j))
    · have h := (Ideal.mem_pi _ _).1 hxy j
      rcases hj.mem_or_mem (by simpa using h) with h | h
      · left
        rw [Ideal.mem_pi]
        intro l
        by_cases hl : l = j
        · subst hl; exact h
        · rw [hall l hl]; trivial
      · right
        rw [Ideal.mem_pi]
        intro l
        by_cases hl : l = j
        · subst hl; exact h
        · rw [hall l hl]; trivial

/-- Helper for Remark 1.5: the real-looking root $2^{1/2^n}$ in $\mathbb C$. -/
private noncomputable def r15 (n : ℕ) : ℂ := (2 : ℂ) ^ ((1 : ℂ) / 2 ^ n)

private lemma r15_pow (n : ℕ) : r15 n ^ (2 ^ n) = 2 := by
  unfold r15
  rw [← Complex.cpow_nat_mul]
  have : ((2 ^ n : ℕ) : ℂ) * ((1 : ℂ) / 2 ^ n) = 1 := by
    push_cast
    field_simp
  rw [this, Complex.cpow_one]

private lemma r15_sq (n : ℕ) : r15 (n + 1) ^ 2 = r15 n := by
  unfold r15
  rw [← Complex.cpow_nat_mul]
  congr 1
  push_cast
  field_simp
  ring

private lemma r15_ne (n : ℕ) : r15 n ≠ 0 := by
  intro h
  have := r15_pow n
  rw [h, zero_pow (by positivity)] at this
  norm_num at this

private lemma r15_int (n : ℕ) : IsIntegral ℤ (r15 n) := by
  have h : IsIntegral ℤ (r15 n ^ (2 ^ n)) := by
    rw [r15_pow]
    have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (2 : ℤ))
    simpa using this
  exact IsIntegral.of_pow (by positivity) h

/-- **Remark 1.5.** The ring of all algebraic integers (the integral closure of $\mathbb Z$ in $\mathbb C$) is not
noetherian: the ideals $(2^{1/2^n})$ form a strictly ascending chain, since $2^{1/2^{n+1}}/2^{1/2^n}$ is not an
algebraic integer (its $2^{n+1}$-th power is $1/2$). Milne's reason: "$\sqrt\alpha$ can always be extracted". -/
@[kb "milne2020ant" "v3.08, Remark 1.5, p. 16"]
theorem remark_1_5 : ¬ IsNoetherianRing (integralClosure ℤ ℂ) := by
  intro hN
  let ρ : ℕ → integralClosure ℤ ℂ := fun n => ⟨r15 n, r15_int n⟩
  have hρ : ∀ n, ρ (n + 1) ^ 2 = ρ n := fun n => Subtype.ext (r15_sq n)
  have hmono : Monotone (fun n => Ideal.span {ρ n}) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨ρ (n + 1), by rw [← hρ n]; ring⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.2 hN) ⟨_, hmono⟩
  have h1 : Ideal.span {ρ (n + 1)} ≤ Ideal.span {ρ n} := by
    have := hn (n + 1) (by omega)
    exact this.symm.le
  rw [Ideal.span_singleton_le_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have hc' : (r15 (n + 1)) = r15 n * (c : ℂ) := congrArg Subtype.val hc
  have hcr : (c : ℂ) * r15 (n + 1) = 1 := by
    have hne := r15_ne (n + 1)
    apply mul_left_cancel₀ hne
    have h2 : r15 (n + 1) = (c : ℂ) * r15 (n + 1) ^ 2 := by rw [r15_sq, mul_comm]; exact hc'
    linear_combination (-1 : ℂ) * h2
  have hinv : IsIntegral ℤ ((2 : ℂ)⁻¹) := by
    have h3 : (2 : ℂ)⁻¹ = (c : ℂ) ^ (2 ^ (n + 1)) := by
      have := r15_pow (n + 1)
      have h4 : ((c : ℂ) * r15 (n + 1)) ^ (2 ^ (n + 1)) = 1 := by rw [hcr]; simp
      rw [mul_pow, this] at h4
      exact inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact h4)
    rw [h3]
    exact c.2.pow _
  have hq : IsIntegral ℤ ((2 : ℚ)⁻¹) := by
    rw [← isIntegral_algebraMap_iff (A := ℚ) (B := ℂ)]
    simpa using hinv
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
  have : ((y : ℚ)) * 2 = 1 := by
    rw [show ((y : ℚ)) = algebraMap ℤ ℚ y from rfl, hy]; norm_num
  have : (y : ℤ) * 2 = 1 := by exact_mod_cast this
  omega

/-- Helper for Theorem 1.18: base change of `AdjoinRoot`. -/
private noncomputable def ch1TensorAdjoinRoot {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (f : k[X]) : Ω ⊗[k] AdjoinRoot f ≃ₐ[Ω] AdjoinRoot (f.map (algebraMap k Ω)) :=
  (AdjoinRoot.tensorAlgEquiv f (f.map Algebra.TensorProduct.includeRight.toRingHom) rfl).trans
    (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid k Ω Ω) _ _ (by
      rw [Polynomial.map_map]
      apply Associated.of_eq
      congr 1
      ext x
      simp [Algebra.algebraMap_eq_smul_one]))

private lemma ch1TensorAdjoinRoot_root {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (f : k[X]) :
    ch1TensorAdjoinRoot (Ω := Ω) f (1 ⊗ₜ AdjoinRoot.root f) = AdjoinRoot.root _ := by
  rw [ch1TensorAdjoinRoot, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root,
    AdjoinRoot.coe_mapAlgEquiv]
  simp [AdjoinRoot.map]
  exact AdjoinRoot.lift_root _

/-- Helper for Theorem 1.18: Chinese remainder theorem for `AdjoinRoot` of a product of
pairwise coprime polynomials. -/
private noncomputable def ch1CRT {Ω : Type*} [Field Ω] {ι : Type*} [Fintype ι]
    (g : ι → Polynomial Ω) (hcop : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (F : Polynomial Ω)
    (hF : F = ∏ i, g i) : AdjoinRoot F ≃ₐ[Ω] ∀ i, AdjoinRoot (g i) :=
  have h1 : Ideal.span {F} = ⨅ i, Ideal.span ({g i} : Set (Polynomial Ω)) := by
    rw [Ideal.iInf_span_singleton hcop, hF]
  have h2 : Pairwise (Function.onFun IsCoprime fun i => Ideal.span ({g i} : Set (Polynomial Ω))) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).2 (hcop i j hij)
  AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq h1).trans
      (Ideal.quotientInfRingEquivPiQuotient (fun i => Ideal.span ({g i} : Set (Polynomial Ω))) h2))
    (fun x => by
      ext i
      have : algebraMap Ω (AdjoinRoot F) x = Ideal.Quotient.mk (Ideal.span {F}) (C x) := rfl
      rw [this]
      rfl)

private lemma ch1CRT_root {Ω : Type*} [Field Ω] {ι : Type*} [Fintype ι] (g : ι → Polynomial Ω)
    (hcop : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (F : Polynomial Ω) (hF : F = ∏ i, g i) (i : ι) :
    ch1CRT g hcop F hF (AdjoinRoot.root F) i = AdjoinRoot.root (g i) := by
  have : AdjoinRoot.root F = Ideal.Quotient.mk (Ideal.span {F}) X := rfl
  rw [this]
  rfl

/-- Helper for Theorem 1.18: a monic separable polynomial is the product of its distinct monic
irreducible factors, which are pairwise coprime. -/
private lemma ch1_factor {Ω : Type*} [Field Ω] (F : Polynomial Ω) (hm : F.Monic)
    (hs : F.Separable) :
    ∃ (n : ℕ) (g : Fin n → Polynomial Ω), (∀ i, Irreducible (g i)) ∧ (∀ i, (g i).Monic) ∧
      (∀ i j, i ≠ j → IsCoprime (g i) (g j)) ∧ F = ∏ i, g i := by
  classical
  have hF0 : F ≠ 0 := hm.ne_zero
  have hnd : (UniqueFactorizationMonoid.normalizedFactors F).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hF0).1 hs.squarefree
  set s := (UniqueFactorizationMonoid.normalizedFactors F).toFinset with hsdef
  have hmem : ∀ x ∈ s, x ∈ UniqueFactorizationMonoid.normalizedFactors F := fun x hx =>
    Multiset.mem_toFinset.1 hx
  have hirr : ∀ x ∈ s, Irreducible x := fun x hx =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor x (hmem x hx)
  have hmon : ∀ x ∈ s, x.Monic := fun x hx => by
    have h1 := UniqueFactorizationMonoid.normalize_normalized_factor x (hmem x hx)
    have h2 := Polynomial.monic_normalize (hirr x hx).ne_zero
    rwa [h1] at h2
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun i => hirr _ (s.equivFin.symm i).2,
    fun i => hmon _ (s.equivFin.symm i).2, ?_, ?_⟩
  · intro i j hij
    have hirri := hirr _ (s.equivFin.symm i).2
    rw [hirri.coprime_iff_not_dvd]
    intro hdvd
    have hassoc : Associated (s.equivFin.symm i).1 (s.equivFin.symm j).1 :=
      hirri.associated_of_dvd (hirr _ (s.equivFin.symm j).2) hdvd
    have heq := Polynomial.eq_of_monic_of_associated (hmon _ (s.equivFin.symm i).2)
      (hmon _ (s.equivFin.symm j).2) hassoc
    exact hij (s.equivFin.symm.injective (Subtype.ext heq))
  · have hprod : ∏ i : Fin s.card, (s.equivFin.symm i).1 = ∏ x ∈ s, x := by
      rw [← Finset.prod_coe_sort s (fun x => x)]
      exact Fintype.prod_equiv s.equivFin.symm _ _ (fun _ => rfl)
    rw [hprod]
    have hs' : ∏ x ∈ s, x = (UniqueFactorizationMonoid.normalizedFactors F).prod := by
      rw [hsdef, Finset.prod, Multiset.toFinset_val, hnd.dedup, Multiset.map_id']
    rw [hs']
    symm
    have hmo : ((UniqueFactorizationMonoid.normalizedFactors F).prod).Monic := by
      have := monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors F) id
        (fun x hx => hmon x (Multiset.mem_toFinset.2 hx))
      simpa using this
    exact Polynomial.eq_of_monic_of_associated hmo hm
      (UniqueFactorizationMonoid.prod_normalizedFactors hF0)

universe u in
/-- Helper for Theorem 1.18 (`thm_1_18`), with the fields $\Omega_i$ in the universe `u` of $\Omega$. -/
private theorem thm_1_18_aux {k K : Type*} {Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K]
    [Algebra k Ω] [FiniteDimensional k K] [Algebra.IsSeparable k K] (α : K) (hα : k⟮α⟯ = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (Ωi : ι → Type u) (_ : ∀ i, Field (Ωi i))
      (_ : ∀ i, Algebra Ω (Ωi i))
      (_ : ∀ i, FiniteDimensional Ω (Ωi i)) (_ : ∀ i, Algebra.IsSeparable Ω (Ωi i))
      (e : Ω ⊗[k] K ≃ₐ[Ω] ∀ i, Ωi i),
      (∀ i, Ω⟮e (1 ⊗ₜ α) i⟯ = ⊤) ∧
        (minpoly k α).map (algebraMap k Ω) = ∏ i, minpoly Ω (e (1 ⊗ₜ α) i) := by
  classical
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hFm : ((minpoly k α).map (algebraMap k Ω)).Monic := (minpoly.monic hint).map _
  have hFs : ((minpoly k α).map (algebraMap k Ω)).Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable k α)
  obtain ⟨n, g, hirr, hmon, hcop, hprod⟩ := ch1_factor _ hFm hFs
  have : ∀ i, Fact (Irreducible (g i)) := fun i => ⟨hirr i⟩
  -- `K ≃ k[X]/(f)`
  let e0 : AdjoinRoot (minpoly k α) ≃ₐ[k] K :=
    (IntermediateField.adjoinRootEquivAdjoin k hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  have he0 : e0 (AdjoinRoot.root _) = α := by
    simp [e0, IntermediateField.adjoinRootEquivAdjoin_apply_root]
  let e : Ω ⊗[k] K ≃ₐ[Ω] ∀ i, AdjoinRoot (g i) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[Ω] Ω) e0.symm).trans
      ((ch1TensorAdjoinRoot (minpoly k α)).trans (ch1CRT g hcop _ hprod))
  have he : ∀ i, e (1 ⊗ₜ α) i = AdjoinRoot.root (g i) := by
    intro i
    have : e0.symm α = AdjoinRoot.root _ := by rw [AlgEquiv.symm_apply_eq, he0]
    simp only [e, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, this,
      map_one]
    rw [ch1TensorAdjoinRoot_root, ch1CRT_root]
  have hminpoly : ∀ i, minpoly Ω (AdjoinRoot.root (g i)) = g i := by
    intro i
    rw [AdjoinRoot.minpoly_root (hirr i).ne_zero, (hmon i).leadingCoeff]
    simp
  have htop : ∀ i, Ω⟮AdjoinRoot.root (g i)⟯ = ⊤ := fun i =>
    IntermediateField.adjoin_eq_top_of_algebra Ω {AdjoinRoot.root (g i)} AdjoinRoot.adjoinRoot_eq_top
  have hsep : ∀ i, Algebra.IsSeparable Ω (AdjoinRoot (g i)) := by
    intro i
    have hsepel : IsSeparable Ω (AdjoinRoot.root (g i)) := by
      unfold IsSeparable
      rw [hminpoly i]
      exact hFs.of_dvd (hprod ▸ Finset.dvd_prod_of_mem g (Finset.mem_univ i))
    rw [← separableClosure.eq_top_iff, eq_top_iff, ← htop i,
      IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hsepel
  refine ⟨Fin n, inferInstance, fun i => AdjoinRoot (g i), inferInstance, inferInstance,
    fun i => (AdjoinRoot.powerBasis (hirr i).ne_zero).finite, hsep, e, ?_, ?_⟩
  · intro i
    rw [he i]
    exact htop i
  · simp only [he, hminpoly]
    exact hprod

universe u in
/-- **Theorem 1.18.** Let $K/k$ be a finite separable field extension with primitive element $\alpha$
($k(\alpha) = K$), and let $\Omega$ be any field extension of $k$. Then $\Omega \otimes_k K$ is isomorphic, as an
$\Omega$-algebra, to a finite product $\prod_i \Omega_i$ of finite separable field extensions of $\Omega$;
the image $\alpha_i$ of $1 \otimes \alpha$ in $\Omega_i$ generates $\Omega_i$ over $\Omega$, and the minimal
polynomial $f$ of $\alpha$ over $k$ factors over $\Omega$ as the product of the minimal polynomials $f_i$ of the
$\alpha_i$.

The fields $\Omega_i$ are taken in the universe of $\Omega$. -/
@[kb "milne2020ant" "v3.08, Thm. 1.18, p. 24"]
theorem thm_1_18 {k K : Type*} {Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
    [FiniteDimensional k K] [Algebra.IsSeparable k K] (α : K) (hα : k⟮α⟯ = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (Ωi : ι → Type u) (_ : ∀ i, Field (Ωi i)) (_ : ∀ i, Algebra Ω (Ωi i))
      (_ : ∀ i, FiniteDimensional Ω (Ωi i)) (_ : ∀ i, Algebra.IsSeparable Ω (Ωi i))
      (e : Ω ⊗[k] K ≃ₐ[Ω] ∀ i, Ωi i),
      (∀ i, Ω⟮e (1 ⊗ₜ α) i⟯ = ⊤) ∧
        (minpoly k α).map (algebraMap k Ω) = ∏ i, minpoly Ω (e (1 ⊗ₜ α) i) :=
  thm_1_18_aux α hα

/-- **Example 1.19.** For a number field $K$ there is an isomorphism of $\mathbb C$-algebras
$\mathbb C \otimes_{\mathbb Q} K \cong \mathbb C^{\mathrm{Hom}(K,\mathbb C)}$ whose composite with
$\beta \mapsto 1 \otimes \beta$ and the projection to the factor of $\sigma$ is $\sigma$, i.e.
$\sum a_j\alpha^j \mapsto \sum a_j \alpha_i^j$ where $\alpha_i = \sigma_i(\alpha)$ are the conjugates of $\alpha$.
(Milne indexes the factors by the conjugates $\alpha_1, \dots, \alpha_r$ of a generator $\alpha$; here they are
indexed by the embeddings $\sigma_i$, $\sigma_i(\alpha) = \alpha_i$.) -/
@[kb "milne2020ant" "v3.08, Example 1.19, p. 24"]
theorem example_1_19 (K : Type*) [Field K] [NumberField K] :
    ∃ e : ℂ ⊗[ℚ] K ≃ₐ[ℂ] ((K →ₐ[ℚ] ℂ) → ℂ), ∀ (β : K) (σ : K →ₐ[ℚ] ℂ), e (1 ⊗ₜ β) σ = σ β := by
  classical
  let Φ : ℂ ⊗[ℚ] K →ₐ[ℂ] ((K →ₐ[ℚ] ℂ) → ℂ) :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ ((K →ₐ[ℚ] ℂ) → ℂ))
      (AlgHom.pi (fun σ : K →ₐ[ℚ] ℂ => σ)) (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (β : K) (σ : K →ₐ[ℚ] ℂ), Φ (1 ⊗ₜ β) σ = σ β := by
    intro β σ
    simp [Φ, Algebra.TensorProduct.lift_tmul]
  have hdim : Module.finrank ℂ (ℂ ⊗[ℚ] K) = Module.finrank ℂ ((K →ₐ[ℚ] ℂ) → ℂ) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, AlgHom.card ℚ K ℂ]
  have hsurj : Function.Surjective Φ := by
    show Function.Surjective Φ.toLinearMap
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨ℓ, hℓ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hℓ
    set c : (K →ₐ[ℚ] ℂ) → ℂ := fun σ => ℓ (Pi.single σ 1) with hc
    have hℓy : ∀ y : (K →ₐ[ℚ] ℂ) → ℂ, ℓ y = ∑ σ, c σ * y σ := by
      intro y
      conv_lhs => rw [pi_eq_sum_univ y]
      simp [hc, map_sum, mul_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have hzero : ∑ σ, c σ • σ.toLinearMap = (0 : K →ₗ[ℚ] ℂ) := by
      ext β
      have h1 : ℓ (Φ (1 ⊗ₜ β)) = 0 := hker (LinearMap.mem_range_self Φ.toLinearMap (1 ⊗ₜ β))
      rw [hℓy] at h1
      simpa [hΦ] using h1
    have hli := linearIndependent_toLinearMap ℚ K ℂ
    have hc0 := Fintype.linearIndependent_iff.1 hli c hzero
    refine LinearMap.ext fun y => ?_
    rw [hℓy]
    simp [hc0]
  have hbij : Function.Bijective Φ :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj, hsurj⟩
  exact ⟨AlgEquiv.ofBijective Φ hbij, fun β σ => hΦ β σ⟩


end NumberFieldKB.MilneANT
