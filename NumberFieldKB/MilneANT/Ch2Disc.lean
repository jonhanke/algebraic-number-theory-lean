import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 2: discriminants and integral bases

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`; printed page numbers.

Milne's discriminant $D(\beta_1, \dots, \beta_m) = \det(\mathrm{Tr}_{B/A}(\beta_i\beta_j))$ is Mathlib's
`Algebra.discr A β`; the discriminant $\mathrm{disc}(B/A)$ of a free algebra is `Algebra.discr A b` for a basis `b`
(well defined up to the square of a unit, Lemma 2.23 = `Algebra.discr_of_matrix_vecMul`).

* **Proposition 2.24** (`prop_2_24`): when $\mathrm{disc}(B/A) \neq 0$, elements $\gamma_1, \dots, \gamma_m$ form a
  basis iff $(D(\gamma)) = (\mathrm{disc}(B/A))$ as ideals of $A$.
* **Remark 2.25** (`remark_2_25`): over $\mathbb Z$, the $\gamma_i$ span a submodule $N$ of finite index iff
  $D(\gamma) \ne 0$, and then $D(\gamma) = (B:N)^2\,\mathrm{disc}(B/\mathbb Z)$.
* **Remark 2.33 (b)** (`remark_2_33_b`): the trace dual of $A[\beta]$ is $f'(\beta)^{-1}A[\beta]$, with basis
  $\beta^i/f'(\beta)$ (Euler).
* **Example 2.35** (`example_2_35`, `example_2_35_deg_two` … `_five`): the discriminant of $X^n + aX + b$.
* **Proposition 2.43** (`prop_2_43`): $\sum A\beta_i \subseteq B \subseteq \sum A\,\beta_i/d$, $d = D(\beta)$.
-/

open Polynomial Module

namespace NumberFieldKB.MilneANT

/-- Lemma 2.23 in the form used below: $D(\gamma) = \det(M)^2 D(b)$ with $M$ the matrix of $\gamma$ in the basis $b$. -/
private lemma discr_eq_det_sq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {m : ℕ}
    (b : Basis (Fin m) A B) (γ : Fin m → B) :
    Algebra.discr A γ = (b.toMatrix γ).det ^ 2 * Algebra.discr A b := by
  rw [← Algebra.discr_of_matrix_vecMul b (b.toMatrix γ), Basis.toMatrix_map_vecMul]

private lemma det_ne_zero_of_linearIndependent {B : Type*} [CommRing B] {m : ℕ}
    (b : Basis (Fin m) ℤ B) (γ : Fin m → B) (hli : LinearIndependent ℤ γ) :
    (b.toMatrix γ).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv
  have hsum : ∑ j, v j • γ j = 0 := by
    apply b.repr.injective
    ext i
    have := congrFun hMv i
    simp only [Matrix.mulVec, dotProduct, Basis.toMatrix_apply] at this
    simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    simpa [mul_comm] using this
  exact funext (Fintype.linearIndependent_iff.mp hli v hsum)

/-- **Proposition 2.24.** Let $A$ be an integral domain and $B$ an $A$-algebra that is free of rank $m$ (basis
$b$) with $\mathrm{disc}(B/A) = D(b) \ne 0$. Elements $\gamma_1, \dots, \gamma_m$ of $B$ form a basis of $B$ over $A$
iff the principal ideals $(D(\gamma_1, \dots, \gamma_m))$ and $(\mathrm{disc}(B/A))$ of $A$ are equal.

Milne also assumes $B$ is a domain containing $A$; neither is needed. -/
@[kb "milne2020ant" "v3.08, Prop. 2.24, p. 33"]
theorem prop_2_24 {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] {m : ℕ}
    (b : Basis (Fin m) A B) (hb : Algebra.discr A b ≠ 0) (γ : Fin m → B) :
    (∃ b' : Basis (Fin m) A B, ⇑b' = γ) ↔
      Ideal.span {Algebra.discr A γ} = Ideal.span {Algebra.discr A b} := by
  have hdet : (∃ b' : Basis (Fin m) A B, ⇑b' = γ) ↔ IsUnit (b.toMatrix γ).det := by
    rw [← Basis.det_apply, ← Basis.is_basis_iff_det]
    constructor
    · rintro ⟨b', rfl⟩
      exact ⟨b'.linearIndependent, b'.span_eq⟩
    · rintro ⟨hli, hsp⟩
      exact ⟨Basis.mk hli hsp.ge, by simp⟩
  rw [hdet, discr_eq_det_sq b γ, Ideal.span_singleton_eq_span_singleton]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.pow 2
    exact ⟨u⁻¹, by rw [← hu, mul_right_comm, Units.mul_inv, one_mul]⟩
  · rintro ⟨u, hu⟩
    have h1 : (b.toMatrix γ).det ^ 2 * (u : A) = 1 := by
      apply mul_right_cancel₀ hb
      linear_combination hu
    exact isUnit_iff_exists_inv.2 ⟨(b.toMatrix γ).det * u, by rw [← mul_assoc, ← pow_two]; exact h1⟩

/-- **Remark 2.25.** Let $B$ be a commutative ring that is free of rank $m$ as a $\mathbb Z$-module, with basis
$b$ and $\mathrm{disc}(B/\mathbb Z) = D(b) \ne 0$ (the hypothesis of Proposition 2.24, which the remark specializes
to $A = \mathbb Z$), and let $\gamma_1, \dots, \gamma_m \in B$ span the subgroup $N$. Then $N$ has finite index in $B$
iff $D(\gamma) \ne 0$, in which case $D(\gamma) = (B : N)^2 \cdot \mathrm{disc}(B/\mathbb Z)$.

(Without $\mathrm{disc}(B/\mathbb Z) \ne 0$ the equivalence fails: $B = \mathbb Z[\varepsilon]/(\varepsilon^2)$,
$\gamma = (1, \varepsilon)$ has $D(\gamma) = 0$ and $N = B$.) -/
@[kb "milne2020ant" "v3.08, Remark 2.25, p. 34"]
theorem remark_2_25 {B : Type*} [CommRing B] {m : ℕ} (b : Basis (Fin m) ℤ B) (hb : Algebra.discr ℤ b ≠ 0)
    (γ : Fin m → B) :
    ((Submodule.span ℤ (Set.range γ)).toAddSubgroup.FiniteIndex ↔ Algebra.discr ℤ γ ≠ 0) ∧
      (Algebra.discr ℤ γ ≠ 0 →
        Algebra.discr ℤ γ = ((Submodule.span ℤ (Set.range γ)).toAddSubgroup.index : ℤ) ^ 2 *
          Algebra.discr ℤ b) := by
  have hD := discr_eq_det_sq b γ
  have : Module.Free ℤ B := Module.Free.of_basis b
  have : Module.Finite ℤ B := Module.Finite.of_basis b
  have hli_of : Algebra.discr ℤ γ ≠ 0 → LinearIndependent ℤ γ := fun h => by
    by_contra hn
    exact h (Algebra.discr_zero_of_not_linearIndependent ℤ hn)
  have hfi : (Submodule.span ℤ (Set.range γ)).toAddSubgroup.FiniteIndex ↔
      LinearIndependent ℤ γ := by
    rw [AddSubgroup.finiteIndex_iff_finite_quotient]
    change Finite (B ⧸ Submodule.span ℤ (Set.range γ)) ↔ _
    rw [Submodule.finiteQuotient_iff, linearIndependent_iff_card_eq_finrank_span,
      Module.finrank_eq_card_basis b]
    simp only [Set.finrank, Fintype.card_fin]
    exact eq_comm
  constructor
  · rw [hfi]
    constructor
    · intro hli
      rw [hD]
      exact mul_ne_zero (pow_ne_zero _ (det_ne_zero_of_linearIndependent b γ hli)) hb
    · exact hli_of
  · intro hne
    have hli := hli_of hne
    let N := Submodule.span ℤ (Set.range γ)
    let bN : Basis (Fin m) ℤ N.toAddSubgroup := Basis.span hli
    have hidx := AddSubgroup.index_eq_natAbs_det b N.toAddSubgroup bN
    have hbN : ∀ i, (bN i : B) = γ i := fun i => congrArg Subtype.val (Basis.span_apply hli i)
    have hdet : (b.det fun i => (bN i : B)) = (b.toMatrix γ).det := by
      rw [show (fun i => (bN i : B)) = γ from funext hbN, Basis.det_apply]
    rw [hidx, hdet, hD]
    simp [sq_abs]

section Dual

variable {A K L : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- **Remark 2.33 (b)** (Euler). Let $A$ be an integrally closed domain with field of fractions $K$, $L/K$ finite
separable, and $\beta \in L$ integral over $A$ with $L = K[\beta]$; let $f$ be the minimal polynomial of $\beta$ over
$K$ and $m = [L:K]$. The trace dual
$C^* = \{x \in L \mid \mathrm{Tr}_{L/K}(xc) \in A \text{ for all } c \in C\}$ of $C = A[\beta]$ is the free
$A$-module with basis $\beta^i/f'(\beta)$, $0 \le i < m$, i.e. $C^* = f'(\beta)^{-1}A[\beta]$; in particular
$A[\beta] \subseteq B \subseteq f'(\beta)^{-1}A[\beta]$ for the integral closure $B$ of $A$ in $L$.

Milne states it for $A = \mathbb Z$ and also writes the general $A$; the trace dual is
`(Algebra.traceForm K L).dualSubmodule`. -/
@[kb "milne2020ant" "v3.08, Remark 2.33 (b), p. 36"]
theorem remark_2_33_b (β : L) (hβ : IsIntegral A β) (hgen : IntermediateField.adjoin K {β} = ⊤) :
    (Algebra.traceForm K L).dualSubmodule (Submodule.span A (Set.range fun i : Fin (finrank K L) => β ^ (i : ℕ))) =
      Submodule.span A (Set.range fun i : Fin (finrank K L) =>
        β ^ (i : ℕ) / aeval β (derivative (minpoly K β))) ∧
    Submodule.span A (Set.range fun i : Fin (finrank K L) => β ^ (i : ℕ)) ≤
        (integralClosure A L).toSubmodule ∧
      (integralClosure A L).toSubmodule ≤ Submodule.span A (Set.range fun i : Fin (finrank K L) =>
        β ^ (i : ℕ) / aeval β (derivative (minpoly K β))) := by
  have hKβ : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hgen' : Algebra.adjoin K {β} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hKβ.isAlgebraic, hgen]
    rfl
  let pb := PowerBasis.ofAdjoinSimpleEqTop hKβ hgen
  have pbgen : pb.gen = β := PowerBasis.ofAdjoinSimpleEqTop_gen hKβ hgen
  have hdeg : natDegree (minpoly A β) = finrank K L := by
    have h0 : natDegree (minpoly K β) = natDegree (minpoly A β) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hβ, (minpoly.monic hβ).natDegree_map]
    rw [← h0, ← pbgen, pb.natDegree_minpoly, pb.finrank]
  have hS : Subalgebra.toSubmodule (Algebra.adjoin A {β}) =
      Submodule.span A (Set.range fun i : Fin (finrank K L) => β ^ (i : ℕ)) := by
    rw [← Submodule.span_range_natDegree_eq_adjoin (minpoly.monic hβ) (minpoly.aeval _ _)]
    congr; ext y
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_range, hdeg]
    exact ⟨fun ⟨a, b, c⟩ ↦ ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ ↦ ⟨a, b, c⟩⟩
  have hdual := traceForm_dualSubmodule_adjoin (A := A) (K := K) hgen' hβ
  have h1 : (Algebra.traceForm K L).dualSubmodule
      (Submodule.span A (Set.range fun i : Fin (finrank K L) => β ^ (i : ℕ))) =
      Submodule.span A (Set.range fun i : Fin (finrank K L) =>
        β ^ (i : ℕ) / aeval β (derivative (minpoly K β))) := by
    rw [← hS, hdual, hS, Submodule.smul_span]
    congr 1
    ext y
    simp [div_eq_inv_mul, Set.mem_smul_set]
  refine ⟨h1, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (hβ.pow _)
  · intro x hx
    rw [← h1]
    refine (LinearMap.BilinForm.mem_dualSubmodule _).2 fun y hy => ?_
    rw [← hS] at hy
    have hy' : IsIntegral A y := adjoin_le_integralClosure hβ hy
    have hxy : IsIntegral A (x * y) := hx.mul hy'
    have ht : IsIntegral A (Algebra.trace K L (x * y)) := Algebra.isIntegral_trace hxy
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral ht
    rw [Submodule.mem_one]
    exact ⟨a, ha⟩

open Matrix in
/-- **Proposition 2.43.** Let $A$ be an integrally closed domain with field of fractions $K$ (Milne: a principal
ideal domain), $L/K$ finite separable, $B$ the integral closure of $A$ in $L$, and $\beta_1, \dots, \beta_m$ a basis
of $L$ over $K$ consisting of elements of $B$, with discriminant $d = D(\beta_1, \dots, \beta_m)$. Then
$$A\beta_1 + \dots + A\beta_m \subseteq B \subseteq A(\beta_1/d) + \dots + A(\beta_m/d).$$
Milne's proof only uses that $A$ is integrally closed, which is the hypothesis here. -/
@[kb "milne2020ant" "v3.08, Prop. 2.43, p. 40"]
theorem prop_2_43 {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Basis ι K L) (hβ : ∀ i, IsIntegral A (β i)) :
    Submodule.span A (Set.range β) ≤ (integralClosure A L).toSubmodule ∧
      (integralClosure A L).toSubmodule ≤
        Submodule.span A (Set.range fun i => (Algebra.discr K β)⁻¹ • β i) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hβ i
  · intro x hx
    have hx' : IsIntegral A x := hx
    set T := Algebra.traceMatrix K β with hT
    set d := Algebra.discr K β with hd
    have hdd : d = T.det := Algebra.discr_def K β
    have hTe : ∀ i j, T i j = Algebra.trace K L (β i * β j) := by
      intro i j; simp [hT, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    have hTint : ∀ i j, ∃ a : A, algebraMap A K a = T i j := fun i j => by
      rw [hTe]
      exact IsIntegrallyClosed.algebraMap_eq_of_integral (Algebra.isIntegral_trace ((hβ i).mul (hβ j)))
    choose a0 ha using hTint
    let a : Matrix ι ι A := a0
    have hxint : ∀ i, ∃ s : A, algebraMap A K s = Algebra.trace K L (x * β i) := fun i =>
      IsIntegrallyClosed.algebraMap_eq_of_integral (Algebra.isIntegral_trace (hx'.mul (hβ i)))
    choose s hs using hxint
    set c : ι → K := fun j => β.repr x j with hc
    have hTc : T *ᵥ c = fun i => algebraMap A K (s i) := by
      ext i
      rw [hs]
      have hxi : x * β i = ∑ j, c j • (β j * β i) := by
        conv_lhs => rw [← β.sum_repr x]
        rw [Finset.sum_mul]
        simp [hc]
      rw [hxi, map_sum]
      simp [Matrix.mulVec, dotProduct, hTe, mul_comm]
    have hTa : T = a.map (algebraMap A K) := by
      ext i j; exact (ha i j).symm
    have h1 : d • c = (T.adjugate) *ᵥ (T *ᵥ c) := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, hdd]
    have hadj : T.adjugate = (a.adjugate).map (algebraMap A K) := by
      rw [hTa]
      exact (RingHom.map_adjugate (algebraMap A K) a).symm
    set r : ι → A := a.adjugate *ᵥ s with hr
    have h2 : ∀ j, d * c j = algebraMap A K (r j) := by
      intro j
      have := congrFun h1 j
      rw [hTc, hadj] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [this, hr]
      have := (algebraMap A K).map_mulVec a.adjugate s j
      exact this.symm
    have hd0 : d ≠ 0 := Algebra.discr_not_zero_of_basis K β
    rw [← β.sum_repr x]
    refine Submodule.sum_mem _ fun j _ => ?_
    have : β.repr x j • β j = r j • (d⁻¹ • β j) := by
      rw [← algebraMap_smul K (r j), smul_smul, ← h2 j]
      congr 1
      show β.repr x j = d * c j * d⁻¹
      field_simp
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end Dual

section Trinomial

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- $\mathrm{Nm}(t - \beta) = f(t)$ for a power basis generator $\beta$ with minimal polynomial $f$. -/
private lemma norm_sub_gen (pb : PowerBasis F L) (t : F) :
    Algebra.norm F (algebraMap F L t - pb.gen) = (minpoly F pb.gen).eval t := by
  rw [Algebra.norm_eq_matrix_det pb.basis, ← charpoly_leftMulMatrix pb, Matrix.eval_charpoly]
  congr 1
  rw [map_sub, AlgHom.commutes]
  simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]

private lemma norm_affine (pb : PowerBasis F L) (e c : F) (hc : c ≠ 0) :
    Algebra.norm F (algebraMap F L e + algebraMap F L c * pb.gen) =
      (-c) ^ pb.dim * (minpoly F pb.gen).eval (-e / c) := by
  have := pb.finite
  have h : algebraMap F L e + algebraMap F L c * pb.gen =
      algebraMap F L (-c) * (algebraMap F L (-e / c) - pb.gen) := by
    simp only [map_neg, map_div₀]
    have : (algebraMap F L c) ≠ 0 := by simpa using hc
    field_simp
    ring
  rw [h, map_mul, Algebra.norm_algebraMap, norm_sub_gen, pb.finrank]

private lemma trinomial_aux (K a b s : F) (k : ℕ) (hs : K * a * s = -((K + 1) * b)) :
    (K * a) ^ (k + 1) * (s ^ (k + 1) + a * s + b) =
      ((K + 1) ^ (k + 1) * b ^ k + (-1) ^ k * K ^ k * a ^ (k + 1)) * ((-1) ^ (k + 1) * b) := by
  have hpow : (K * a * s) ^ (k + 1) = (-1) ^ (k + 1) * ((K + 1) ^ (k + 1) * b ^ (k + 1)) := by
    rw [hs, show -((K + 1) * b) = (-1) * ((K + 1) * b) by ring, mul_pow, mul_pow]
  have h2 : ((-1 : F) ^ k) * (-1) ^ (k + 1) = -1 := by
    rw [← pow_add, show k + (k + 1) = 2 * k + 1 by ring, pow_succ, pow_mul]; simp
  linear_combination hpow + ((K * a) ^ k * a) * hs - (K ^ k * a ^ (k + 1) * b) * h2

/-- $\mathrm{Nm}(f'(\beta))$ for $f = X^{k+1} + aX + b$ the minimal polynomial of $\beta$ ($k \ge 1$). -/
private lemma trinomial_norm (pb : PowerBasis F L) (k : ℕ) (hk : pb.dim = k + 1) (hk1 : 1 ≤ k)
    (a b : F) (hf : minpoly F pb.gen = X ^ (k + 1) + C a * X + C b) :
    Algebra.norm F (aeval pb.gen (derivative (minpoly F pb.gen))) =
      ((k : F) + 1) ^ (k + 1) * b ^ k + (-1) ^ k * (k : F) ^ k * a ^ (k + 1) := by
  have := pb.finite
  set g := pb.gen with hg
  have hroot : g ^ (k + 1) + algebraMap F L a * g + algebraMap F L b = 0 := by
    have := minpoly.aeval F g
    rw [hf] at this
    simpa using this
  have hderiv : aeval g (derivative (minpoly F g)) = ((k : L) + 1) * g ^ k + algebraMap F L a := by
    rw [hf]
    simp
  have hNg : Algebra.norm F g = (-1) ^ (k + 1) * b := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    rw [hk, hf] at this
    simpa [coeff_X_pow, coeff_C] using this
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 := pb.natDegree_minpoly
    rw [← hg, h0, minpoly.zero, natDegree_X, hk] at h1
    omega
  have hb : b ≠ 0 := by
    intro hb0
    have : Algebra.norm F g = 0 := by rw [hNg, hb0, mul_zero]
    exact hg0 (Algebra.norm_eq_zero_iff.mp this)
  have hrel : g * aeval g (derivative (minpoly F g)) =
      algebraMap F L (-((k + 1 : F) * b)) + algebraMap F L (-((k : F) * a)) * g := by
    rw [hderiv]
    simp only [map_neg, map_mul, map_add, map_one, map_natCast]
    linear_combination ((k : L) + 1) * hroot
  have hmul := congrArg (Algebra.norm F) hrel
  rw [map_mul, hNg] at hmul
  have hne : ((-1 : F) ^ (k + 1) * b) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hb
  apply mul_right_cancel₀ hne
  rw [mul_comm, hmul]
  by_cases hc : (-((k : F) * a)) = 0
  · have hka : (k : F) * a = 0 := by simpa using hc
    rw [hc, map_zero, zero_mul, add_zero, Algebra.norm_algebraMap, pb.finrank, hk]
    have h0 : (k : F) ^ k * a ^ (k + 1) = 0 := by
      rw [show (k : F) ^ k * a ^ (k + 1) = ((k : F) * a) ^ k * a by ring, hka,
        zero_pow (by omega), zero_mul]
    have : (-1 : F) ^ k * (k : F) ^ k * a ^ (k + 1) = 0 := by
      rw [mul_assoc, h0, mul_zero]
    rw [this, show (-(((k : F) + 1) * b)) = (-1) * (((k : F) + 1) * b) by ring, mul_pow, mul_pow]
    ring
  · rw [norm_affine pb _ _ hc, hk, hf]
    have hk0 : ((k : F)) * a ≠ 0 := fun h => hc (by rw [h, neg_zero])
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
    have hs : (k : F) * a * (-(-(((k : F) + 1) * b)) / (-((k : F) * a))) = -(((k : F) + 1) * b) := by
      have hk' : (k : F) ≠ 0 := left_ne_zero_of_mul hk0
      have ha' : a ≠ 0 := right_ne_zero_of_mul hk0
      field_simp
    rw [neg_neg]
    exact trinomial_aux (k : F) a b _ k hs

/-- **Example 2.35.** Let $L = F[\beta]$ where $\beta$ has minimal polynomial $f = X^n + aX + b$ over the field $F$
($n \ge 2$), assumed separable. Then the discriminant of $f$ (Milne's $D(1, \beta, \dots, \beta^{n-1})$) is
$$\mathrm{disc}(X^n + aX + b) = (-1)^{n(n-1)/2}\bigl(n^n b^{n-1} + (-1)^{n-1}(n-1)^{n-1}a^n\bigr).$$ -/
@[kb "milne2020ant" "v3.08, Example 2.35, p. 37–38"]
theorem example_2_35 [Algebra.IsSeparable F L] (pb : PowerBasis F L) (hn : 2 ≤ pb.dim) (a b : F)
    (hf : minpoly F pb.gen = X ^ pb.dim + C a * X + C b) :
    Algebra.discr F pb.basis = (-1) ^ (pb.dim * (pb.dim - 1) / 2) *
      ((pb.dim : F) ^ pb.dim * b ^ (pb.dim - 1) +
        (-1) ^ (pb.dim - 1) * ((pb.dim : F) - 1) ^ (pb.dim - 1) * a ^ pb.dim) := by
  obtain ⟨k, hk⟩ : ∃ k, pb.dim = k + 1 := ⟨pb.dim - 1, by omega⟩
  have hf' : minpoly F pb.gen = X ^ (k + 1) + C a * X + C b := by rw [← hk]; exact hf
  have := pb.finite
  rw [Algebra.discr_powerBasis_eq_norm, trinomial_norm pb k hk (by omega) a b hf', pb.finrank, hk]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

/-- **Example 2.35, $n = 2$:** $\mathrm{disc}(X^2 + aX + b) = a^2 - 4b$. -/
@[kb "milne2020ant" "v3.08, Example 2.35, p. 38"]
theorem example_2_35_deg_two [Algebra.IsSeparable F L] (pb : PowerBasis F L) (hn : pb.dim = 2) (a b : F)
    (hf : minpoly F pb.gen = X ^ 2 + C a * X + C b) :
    Algebra.discr F pb.basis = a ^ 2 - 4 * b := by
  rw [example_2_35 pb (by omega) a b (by rw [hn]; exact hf), hn]
  norm_num
  ring

/-- **Example 2.35, $n = 3$:** $\mathrm{disc}(X^3 + aX + b) = -27b^2 - 4a^3$. -/
@[kb "milne2020ant" "v3.08, Example 2.35, p. 38"]
theorem example_2_35_deg_three [Algebra.IsSeparable F L] (pb : PowerBasis F L) (hn : pb.dim = 3) (a b : F)
    (hf : minpoly F pb.gen = X ^ 3 + C a * X + C b) :
    Algebra.discr F pb.basis = -27 * b ^ 2 - 4 * a ^ 3 := by
  rw [example_2_35 pb (by omega) a b (by rw [hn]; exact hf), hn]
  norm_num
  ring

/-- **Example 2.35, $n = 4$:** $\mathrm{disc}(X^4 + aX + b) = 256b^3 - 27a^4$. -/
@[kb "milne2020ant" "v3.08, Example 2.35, p. 38"]
theorem example_2_35_deg_four [Algebra.IsSeparable F L] (pb : PowerBasis F L) (hn : pb.dim = 4) (a b : F)
    (hf : minpoly F pb.gen = X ^ 4 + C a * X + C b) :
    Algebra.discr F pb.basis = 256 * b ^ 3 - 27 * a ^ 4 := by
  rw [example_2_35 pb (by omega) a b (by rw [hn]; exact hf), hn]
  norm_num
  ring

/-- **Example 2.35, $n = 5$:** $\mathrm{disc}(X^5 + aX + b) = 5^5 b^4 + 4^4 a^5$. -/
@[kb "milne2020ant" "v3.08, Example 2.35, p. 38"]
theorem example_2_35_deg_five [Algebra.IsSeparable F L] (pb : PowerBasis F L) (hn : pb.dim = 5) (a b : F)
    (hf : minpoly F pb.gen = X ^ 5 + C a * X + C b) :
    Algebra.discr F pb.basis = 5 ^ 5 * b ^ 4 + 4 ^ 4 * a ^ 5 := by
  rw [example_2_35 pb (by omega) a b (by rw [hn]; exact hf), hn]
  norm_num

end Trinomial

end NumberFieldKB.MilneANT
