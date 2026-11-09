import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Tensor
import NumberFieldKB.MilneCFT.Ch4Modules

/-!
# Milne, Class Field Theory, Chapter IV, §2: the Brauer group

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV, §2: similarity of central simple algebras, the group structure of $\mathrm{Br}(k)$,
Remark 2.13, Example 2.14 (a), (c), the base-change homomorphism $\mathrm{Br}(k) \to \mathrm{Br}(L)$,
the subgroup $\mathrm{Br}(L/k)$ and splitting fields.

Reuse.  Mathlib defines `CSA K` (finite-dimensional central simple $K$-algebras),
`IsBrauerEquivalent` ($M_n(A) \cong M_m(B)$ for some $n, m \neq 0$) and the set
`BrauerGroup K` (the quotient), but not its group structure (a TODO in
`Mathlib/Algebra/BrauerGroup/Defs.lean`).  We put the group structure on Mathlib's
`BrauerGroup K` and prove that Mathlib's equivalence is Milne's similarity
($A \otimes_k M_n(k) \cong B \otimes_k M_m(k)$), `isBrauerEquivalent_iff_milne`.

Universes.  Everything (the field, the algebras, the extension fields) lives in one universe
`u`; Milne's set-theoretic Remark 2.13 (b) is handled by this.

Locators give the printed page of the book (printed page = pdf page − 9).
-/

open scoped TensorProduct

namespace NumberFieldKB.MilneCFT.Ch4

universe u

variable {K : Type u} [Field K]

/-! ### Operations on central simple algebras -/

namespace CSA

/-- The tensor product $A \otimes_K B$ of two central simple algebras (Cor. 2.8). -/
noncomputable def tensor (A B : CSA.{u, u} K) : CSA.{u, u} K where
  toAlgCat := AlgCat.of K (A ⊗[K] B)

/-- The opposite algebra $A^{\mathrm{opp}}$ of a central simple algebra. -/
noncomputable def op (A : CSA.{u, u} K) : CSA.{u, u} K where
  toAlgCat := AlgCat.of K Aᵐᵒᵖ

variable (K) in
/-- The field $K$ as a central simple $K$-algebra. -/
noncomputable def base : CSA.{u, u} K where
  toAlgCat := AlgCat.of K K

variable (K) in
/-- The matrix algebra $M_n(K)$ ($n \neq 0$) as a central simple $K$-algebra. -/
noncomputable def matrix (n : ℕ) [NeZero n] : CSA.{u, u} K where
  toAlgCat := AlgCat.of K (Matrix (Fin n) (Fin n) K)

end CSA

/-! ### Similarity -/

/-- Milne's definition of similarity agrees with Mathlib's `IsBrauerEquivalent`: two central
simple $K$-algebras $A, B$ are similar if $A \otimes_K M_n(K) \cong B \otimes_K M_m(K)$ for some
$n, m \neq 0$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §2, def. of similar algebras, p. 130"]
theorem isBrauerEquivalent_iff_milne (A B : CSA.{u, u} K) :
    IsBrauerEquivalent A B ↔
      ∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧
        Nonempty (A ⊗[K] Matrix (Fin n) (Fin n) K ≃ₐ[K] B ⊗[K] Matrix (Fin m) (Fin m) K) := by
  constructor
  · rintro ⟨n, m, hn, hm, ⟨e⟩⟩
    exact ⟨n, m, hn, hm, ⟨(matrixEquivTensor (Fin n) K A).symm.trans
      (e.trans (matrixEquivTensor (Fin m) K B))⟩⟩
  · rintro ⟨n, m, hn, hm, ⟨e⟩⟩
    exact ⟨n, m, hn, hm, ⟨(matrixEquivTensor (Fin n) K A).trans
      (e.trans (matrixEquivTensor (Fin m) K B).symm)⟩⟩

theorem isBrauerEquivalent_of_algEquiv {A B : CSA.{u, u} K} (e : A ≃ₐ[K] B) :
    IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

/-- Matrix algebras over `A` of sizes `n` and `p` combine into a matrix algebra over `A` of size
`n * p`. -/
noncomputable def matMat (n p : ℕ) (A : Type*) [Ring A] [Algebra K A] :
    Matrix (Fin n) (Fin n) (Matrix (Fin p) (Fin p) A) ≃ₐ[K] Matrix (Fin (n * p)) (Fin (n * p)) A :=
  (Matrix.compAlgEquiv (Fin n) (Fin p) A K).trans
    (Matrix.reindexAlgEquiv K A finProdFinEquiv)

/-- The Kronecker product of matrix algebras. -/
noncomputable def kronMat (n p : ℕ) (A B : Type*) [Ring A] [Algebra K A] [Ring B] [Algebra K B] :
    Matrix (Fin n) (Fin n) A ⊗[K] Matrix (Fin p) (Fin p) B ≃ₐ[K]
      Matrix (Fin (n * p)) (Fin (n * p)) (A ⊗[K] B) :=
  (Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin p) K K A B).trans
    (Matrix.reindexAlgEquiv K (A ⊗[K] B) finProdFinEquiv)

theorem isBrauerEquivalent_tensor {A A' B B' : CSA.{u, u} K} (h : IsBrauerEquivalent A A')
    (h' : IsBrauerEquivalent B B') : IsBrauerEquivalent (CSA.tensor A B) (CSA.tensor A' B') := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  obtain ⟨p, q, hp, hq, ⟨e'⟩⟩ := h'
  exact ⟨n * p, m * q, mul_ne_zero hn hp, mul_ne_zero hm hq,
    ⟨(kronMat n p A B).symm.trans ((Algebra.TensorProduct.congr e e').trans (kronMat m q A' B'))⟩⟩

theorem isBrauerEquivalent_op {A A' : CSA.{u, u} K} (h : IsBrauerEquivalent A A') :
    IsBrauerEquivalent (CSA.op A) (CSA.op A') := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨AlgEquiv.mopMatrix.trans (e.op.trans AlgEquiv.mopMatrix.symm)⟩⟩

/-! ### The group structure -/

namespace BrauerGroup

noncomputable instance : Mul (BrauerGroup.{u, u} K) :=
  ⟨Quotient.map₂ CSA.tensor fun _ _ h _ _ h' => isBrauerEquivalent_tensor h h'⟩

noncomputable instance : One (BrauerGroup.{u, u} K) :=
  ⟨Quotient.mk (Brauer.CSA_Setoid K) (CSA.base K)⟩

noncomputable instance : Inv (BrauerGroup.{u, u} K) :=
  ⟨Quotient.map CSA.op fun _ _ h => isBrauerEquivalent_op h⟩

/-- The class $[A] \in \mathrm{Br}(K)$ of a central simple algebra. -/
abbrev mk (A : CSA.{u, u} K) : BrauerGroup.{u, u} K := Quotient.mk (Brauer.CSA_Setoid K) A

theorem mk_mul_mk (A B : CSA.{u, u} K) : mk A * mk B = mk (CSA.tensor A B) := rfl

theorem one_def : (1 : BrauerGroup.{u, u} K) = mk (CSA.base K) := rfl

theorem inv_mk (A : CSA.{u, u} K) : (mk A)⁻¹ = mk (CSA.op A) := rfl

theorem mk_eq_mk_iff (A B : CSA.{u, u} K) : mk A = mk B ↔ IsBrauerEquivalent A B :=
  Quotient.eq (r := Brauer.CSA_Setoid K)

theorem mul_assoc' (x y z : BrauerGroup.{u, u} K) : x * y * z = x * (y * z) := by
  induction x using Quotient.inductionOn with | _ A => ?_
  induction y using Quotient.inductionOn with | _ B => ?_
  induction z using Quotient.inductionOn with | _ C => ?_
  show mk A * mk B * mk C = mk A * (mk B * mk C)
  rw [mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_eq_mk_iff]
  exact isBrauerEquivalent_of_algEquiv (Algebra.TensorProduct.assoc K K K A B C)

theorem one_mul' (x : BrauerGroup.{u, u} K) : 1 * x = x := by
  induction x using Quotient.inductionOn with | _ A => ?_
  show mk (CSA.base K) * mk A = mk A
  rw [mk_mul_mk, mk_eq_mk_iff]
  exact isBrauerEquivalent_of_algEquiv (Algebra.TensorProduct.lid K A)

theorem mul_one' (x : BrauerGroup.{u, u} K) : x * 1 = x := by
  induction x using Quotient.inductionOn with | _ A => ?_
  show mk A * mk (CSA.base K) = mk A
  rw [mk_mul_mk, mk_eq_mk_iff]
  exact isBrauerEquivalent_of_algEquiv (Algebra.TensorProduct.rid K K A)

theorem mul_comm' (x y : BrauerGroup.{u, u} K) : x * y = y * x := by
  induction x using Quotient.inductionOn with | _ A => ?_
  induction y using Quotient.inductionOn with | _ B => ?_
  show mk A * mk B = mk B * mk A
  rw [mk_mul_mk, mk_mul_mk, mk_eq_mk_iff]
  exact isBrauerEquivalent_of_algEquiv (Algebra.TensorProduct.comm K A B)

/-- `M₁(A) ≃ A`. -/
def matOne (A : Type*) [Ring A] [Algebra K A] : Matrix (Fin 1) (Fin 1) A ≃ₐ[K] A where
  toFun M := M 0 0
  invFun a := Matrix.of fun _ _ => a
  left_inv M := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    rfl
  right_inv a := rfl
  map_mul' M N := by simp [Matrix.mul_apply]
  map_add' M N := rfl
  commutes' r := by simp [Matrix.algebraMap_matrix_apply]

/-- A central simple algebra isomorphic to a nonzero-size matrix algebra over `K` is Brauer
equivalent to `K`. -/
theorem isBrauerEquivalent_base_of_matrix {A : CSA.{u, u} K} {n : ℕ} (hn : n ≠ 0)
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) K) : IsBrauerEquivalent A (CSA.base K) :=
  ⟨1, n, one_ne_zero, hn, ⟨(matOne A).trans e⟩⟩

theorem inv_mul_cancel' (x : BrauerGroup.{u, u} K) : x⁻¹ * x = 1 := by
  induction x using Quotient.inductionOn with | _ A => ?_
  show (mk A)⁻¹ * mk A = 1
  rw [inv_mk, mk_mul_mk, one_def, mk_eq_mk_iff]
  obtain ⟨-, ⟨e⟩⟩ := cor_2_9 (K := K) A
  have hn : Module.finrank K A ≠ 0 := Module.finrank_pos.ne'
  exact isBrauerEquivalent_base_of_matrix hn
    ((Algebra.TensorProduct.comm K (Aᵐᵒᵖ) A).trans e)

/-- The Brauer group of $K$ (Milne, §2, p. 130): the similarity classes of central simple
$K$-algebras with $[A][B] = [A \otimes_K B]$, identity $[M_n(K)]$ and inverse
$[A]^{-1} = [A^{\mathrm{opp}}]$ (by Cor. 2.9). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §2, def. of the Brauer group, p. 130"]
noncomputable instance instCommGroup : CommGroup (BrauerGroup.{u, u} K) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'
  mul_comm := mul_comm'

/-- $[M_n(K)]$ is the identity of $\mathrm{Br}(K)$, and $[A] = 1$ if and only if $A$ is a
matrix algebra over $K$. -/
theorem mk_eq_one_iff (A : CSA.{u, u} K) :
    mk A = 1 ↔ ∃ n : ℕ, n ≠ 0 ∧ Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  rw [one_def, mk_eq_mk_iff]
  constructor
  · rintro ⟨p, q, hp, hq, ⟨e⟩⟩
    have : IsArtinianRing A := IsArtinianRing.of_finite K A
    obtain ⟨r, hr, D, _, _, _, ⟨f⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
    have g : Matrix (Fin (p * r)) (Fin (p * r)) D ≃ₐ[K] Matrix (Fin q) (Fin q) K :=
      (matMat p r D).symm.trans (f.mapMatrix.symm.trans e)
    obtain ⟨-, ⟨d⟩⟩ := cor_1_22 D K (mul_ne_zero hp hr.out) hq g
    exact ⟨r, hr.out, ⟨f.trans d.mapMatrix⟩⟩
  · rintro ⟨n, hn, ⟨e⟩⟩
    exact isBrauerEquivalent_base_of_matrix hn e

end BrauerGroup

/-! ### Remark 2.13 -/

/-- Remark 2.13 (a) of Milne, existence: every similarity class is represented by a central
division algebra. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Rem. 2.13(a), p. 130"]
theorem remark_2_13a_exists (x : BrauerGroup.{u, u} K) :
    ∃ D : CSA.{u, u} K, (∀ d : D, d ≠ 0 → IsUnit d) ∧ BrauerGroup.mk D = x := by
  induction x using Quotient.inductionOn with | _ A => ?_
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨r, hr, D, _, _, _, ⟨f⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  have hcen : Algebra.IsCentral K D := by
    refine ⟨fun z hz => ?_⟩
    have hw : f.symm (Matrix.diagonal fun _ => z) ∈ Subalgebra.center K A := by
      rw [Subalgebra.mem_center_iff]
      intro b
      apply f.injective
      simp only [map_mul, AlgEquiv.apply_symm_apply]
      ext i j
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
      exact Subalgebra.mem_center_iff.mp hz _
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out (K := K) hw)
    have h2 := congrArg f hc
    rw [AlgEquiv.commutes, AlgEquiv.apply_symm_apply] at h2
    have h3 := congrFun (congrFun h2 ⟨0, Nat.pos_of_ne_zero hr.out⟩) ⟨0, Nat.pos_of_ne_zero hr.out⟩
    refine Algebra.mem_bot.mpr ⟨c, ?_⟩
    simp [Matrix.algebraMap_matrix_apply] at h3
    exact h3
  let Dc : CSA.{u, u} K := { toAlgCat := AlgCat.of K D }
  refine ⟨Dc, fun d hd => hd.isUnit, ?_⟩
  show BrauerGroup.mk Dc = BrauerGroup.mk A
  rw [BrauerGroup.mk_eq_mk_iff]
  exact ⟨r, 1, hr.out, one_ne_zero, ⟨f.symm.trans (BrauerGroup.matOne A).symm⟩⟩

theorem cor_1_22_of_units (D D' : CSA.{u, u} K) (hD : ∀ d : D, d ≠ 0 → IsUnit d)
    (hD' : ∀ d : D', d ≠ 0 → IsUnit d) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (e : Matrix (Fin n) (Fin n) D ≃ₐ[K] Matrix (Fin m) (Fin m) D') :
    n = m ∧ Nonempty (D ≃ₐ[K] D') := by
  letI : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (hD a h)
  letI : DivisionRing D' := DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (hD' a h)
  exact cor_1_22 D D' hn hm e

/-- Remark 2.13 (a) of Milne, uniqueness: two central division algebras represent the same
similarity class if and only if they are isomorphic. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Rem. 2.13(a), p. 130"]
theorem remark_2_13a_unique (D D' : CSA.{u, u} K) (hD : ∀ d : D, d ≠ 0 → IsUnit d)
    (hD' : ∀ d : D', d ≠ 0 → IsUnit d) :
    BrauerGroup.mk D = BrauerGroup.mk D' ↔ Nonempty (D ≃ₐ[K] D') := by
  rw [BrauerGroup.mk_eq_mk_iff]
  constructor
  · rintro ⟨n, m, hn, hm, ⟨e⟩⟩
    exact (cor_1_22_of_units D D' hD hD' hn hm e).2
  · rintro ⟨e⟩
    exact isBrauerEquivalent_of_algEquiv e

/-- Remark 2.13 (a) of Milne, the finer statement: every central simple algebra is $M_n(D)$ for a
central division algebra $D$ (Wedderburn), and $D$ is determined by the similarity class of $A$:
if $A \cong M_n(D)$, $A' \cong M_{n'}(D')$ with $A, A'$ similar and $D, D'$ division algebras,
then $D \cong D'$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Rem. 2.13(a), p. 130"]
theorem remark_2_13a_matrix (A A' : CSA.{u, u} K) (h : IsBrauerEquivalent A A')
    (D D' : Type u) [DivisionRing D] [Algebra K D] [FiniteDimensional K D] [DivisionRing D']
    [Algebra K D'] [FiniteDimensional K D'] {n n' : ℕ} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) D) (e' : A' ≃ₐ[K] Matrix (Fin n') (Fin n') D') :
    Nonempty (D ≃ₐ[K] D') := by
  obtain ⟨p, q, hp, hq, ⟨g⟩⟩ := h
  have G : Matrix (Fin (p * n)) (Fin (p * n)) D ≃ₐ[K] Matrix (Fin (q * n')) (Fin (q * n')) D' :=
    (matMat p n D).symm.trans
      (e.mapMatrix.symm.trans (g.trans (e'.mapMatrix.trans (matMat q n' D'))))
  exact (cor_1_22 D D' (mul_ne_zero hp hn) (mul_ne_zero hq hn') G).2

/-! ### Example 2.14 (a), (c) -/

/-- Example 2.14 (a) of Milne: the Brauer group of an algebraically closed field is $0$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 2.14(a), p. 130"]
theorem example_2_14a [IsAlgClosed K] (x : BrauerGroup.{u, u} K) : x = 1 := by
  induction x using Quotient.inductionOn with | _ A => ?_
  show BrauerGroup.mk A = 1
  rw [BrauerGroup.mk_eq_one_iff]
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K A
  exact ⟨n, hn.out, ⟨e⟩⟩

/-- Example 2.14 (c) of Milne: the Brauer group of a finite field is $0$ (Wedderburn's theorem
4.1 that finite division rings are commutative). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 2.14(c), p. 130"]
theorem example_2_14c [Finite K] (x : BrauerGroup.{u, u} K) : x = 1 := by
  obtain ⟨D, hD, rfl⟩ := remark_2_13a_exists x
  letI : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (hD a h)
  have : Finite D := Module.finite_of_finite K
  letI : Field D := littleWedderburn D
  have hsurj : Function.Surjective (algebraMap K D) := fun d => by
    have hd : d ∈ Subalgebra.center K D := Subalgebra.mem_center_iff.2 fun b => mul_comm b d
    exact Algebra.mem_bot.mp (Algebra.IsCentral.out hd)
  have e : D ≃ₐ[K] K :=
    (AlgEquiv.ofBijective (Algebra.ofId K D) ⟨RingHom.injective _, hsurj⟩).symm
  exact (BrauerGroup.mk_eq_mk_iff _ _).2 (isBrauerEquivalent_of_algEquiv e)

/-! ### Extension of the base field -/

section BaseChange

variable (L : Type u) [Field L] [Algebra K L]

instance (A : Type u) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A] :
    Algebra.IsCentral L (L ⊗[K] A) :=
  (prop_2_15 A L).1

instance (A : Type u) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A] :
    IsSimpleRing (L ⊗[K] A) :=
  (prop_2_15 A L).2

/-- The base change $A \otimes_K L$ (written `L ⊗[K] A`) of a central simple $K$-algebra, a
central simple $L$-algebra (Prop. 2.15). -/
noncomputable def CSA.baseChange (A : CSA.{u, u} K) : CSA.{u, u} L where
  toAlgCat := AlgCat.of L (L ⊗[K] A)

/-- Base change commutes with matrix algebras, as `K`-algebras. -/
noncomputable def bcMatK (n : ℕ) (A : Type u) [Ring A] [Algebra K A] :
    L ⊗[K] Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin n) (Fin n) (L ⊗[K] A) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (matrixEquivTensor (Fin n) K A)).trans
    ((Algebra.TensorProduct.assoc K K K L A (Matrix (Fin n) (Fin n) K)).symm.trans
      (matrixEquivTensor (Fin n) K (L ⊗[K] A)).symm)

/-- Base change commutes with matrix algebras, as `L`-algebras. -/
noncomputable def bcMat (n : ℕ) (A : Type u) [Ring A] [Algebra K A] :
    L ⊗[K] Matrix (Fin n) (Fin n) A ≃ₐ[L] Matrix (Fin n) (Fin n) (L ⊗[K] A) :=
  AlgEquiv.ofRingEquiv (f := (bcMatK L n A).toRingEquiv) fun l => by
    have h1 : algebraMap L (L ⊗[K] Matrix (Fin n) (Fin n) A) l = l ⊗ₜ[K] 1 := rfl
    show bcMatK L n A (algebraMap L _ l) = _
    rw [h1]
    have h2 : bcMatK L n A (l ⊗ₜ[K] 1) = (matrixEquivTensor (Fin n) K (L ⊗[K] A)).symm
        ((l ⊗ₜ[K] (1 : A)) ⊗ₜ[K] (1 : Matrix (Fin n) (Fin n) K)) := by
      simp only [bcMatK, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, map_one]
      rw [Algebra.TensorProduct.one_def (A := A), Algebra.TensorProduct.assoc_symm_tmul]
      rfl
    rw [h2, matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.smul_one_eq_diagonal, Matrix.algebraMap_eq_diagonal]
    rfl

theorem isBrauerEquivalent_baseChange {A B : CSA.{u, u} K} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (CSA.baseChange L A) (CSA.baseChange L B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨(bcMat L n A).symm.trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl e).trans (bcMat L m B))⟩⟩

/-- The underlying map $\mathrm{Br}(K) \to \mathrm{Br}(L)$, $[A] \mapsto [A \otimes_K L]$. -/
noncomputable def baseChangeFun : BrauerGroup.{u, u} K → BrauerGroup.{u, u} L :=
  Quotient.map (CSA.baseChange L) fun _ _ h => isBrauerEquivalent_baseChange L h

theorem baseChangeFun_one : baseChangeFun (K := K) L 1 = 1 := by
  show BrauerGroup.mk (CSA.baseChange L (CSA.base K)) = BrauerGroup.mk (CSA.base L)
  rw [BrauerGroup.mk_eq_mk_iff]
  exact isBrauerEquivalent_of_algEquiv (Algebra.TensorProduct.rid K L L)

/-- `(L ⊗ A) ⊗_L (L ⊗ B) ≅ L ⊗ (A ⊗ B)` as `L`-algebras. -/
noncomputable def bcTensor (A B : Type u) [Ring A] [Algebra K A] [Ring B] [Algebra K B] :
    (L ⊗[K] A) ⊗[L] (L ⊗[K] B) ≃ₐ[L] L ⊗[K] (A ⊗[K] B) :=
  ((Algebra.TensorProduct.assoc K L L (L ⊗[K] A) L B).symm.trans
    ((Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L L (L ⊗[K] A))
      (AlgEquiv.refl : B ≃ₐ[K] B)).trans (Algebra.TensorProduct.assoc K K L L A B)))

theorem baseChangeFun_mul (x y : BrauerGroup.{u, u} K) :
    baseChangeFun L (x * y) = baseChangeFun L x * baseChangeFun L y := by
  induction x using Quotient.inductionOn with | _ A => ?_
  induction y using Quotient.inductionOn with | _ B => ?_
  show BrauerGroup.mk (CSA.baseChange L (CSA.tensor A B)) =
    BrauerGroup.mk (CSA.tensor (CSA.baseChange L A) (CSA.baseChange L B))
  rw [BrauerGroup.mk_eq_mk_iff]
  exact isBrauerEquivalent_of_algEquiv (bcTensor L A B).symm

/-- The homomorphism $\mathrm{Br}(K) \to \mathrm{Br}(L)$, $[A] \mapsto [A \otimes_K L]$, for a
field $L$ containing $K$ (Milne, after Cor. 2.16). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §2, the homomorphism Br(k) → Br(L), p. 131"]
noncomputable def baseChange : BrauerGroup.{u, u} K →* BrauerGroup.{u, u} L where
  toFun := baseChangeFun L
  map_one' := baseChangeFun_one L
  map_mul' := baseChangeFun_mul L

theorem baseChange_mk (A : CSA.{u, u} K) :
    baseChange L (BrauerGroup.mk A) = BrauerGroup.mk (CSA.baseChange L A) := rfl

variable (K) in
/-- $\mathrm{Br}(L/K)$, the kernel of $\mathrm{Br}(K) \to \mathrm{Br}(L)$ (Milne, after
Cor. 2.16). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §2, def. of Br(L/k), p. 131"]
noncomputable def relBrauer : Subgroup (BrauerGroup.{u, u} K) :=
  (baseChange (K := K) L).ker

/-- A central simple $K$-algebra $A$ is *split by* $L$ ($L$ is a *splitting field* for $A$) if
$A \otimes_K L$ is a matrix algebra over $L$ (Milne, after Cor. 2.16). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §2, def. of split by L, splitting field, p. 131"]
def IsSplitBy (A : Type u) [Ring A] [Algebra K A] : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)

/-- $\mathrm{Br}(L/K)$ consists of the classes split by $L$ (Milne, after Cor. 2.16). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §2, Br(L/k) = classes split by L, p. 131"]
theorem mk_mem_relBrauer_iff (A : CSA.{u, u} K) :
    BrauerGroup.mk A ∈ relBrauer K L ↔ IsSplitBy (K := K) L A := by
  rw [relBrauer, MonoidHom.mem_ker, baseChange_mk, BrauerGroup.mk_eq_one_iff]
  rfl

end BaseChange

end NumberFieldKB.MilneCFT.Ch4
