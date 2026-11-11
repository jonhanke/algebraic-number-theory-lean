import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Algebra.RingQuot
import QuadFormsKB.Citation

/-!
# Milne, *Class Field Theory*, Chapter VIII §5: the algebra $A(a,b;\zeta)$

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §5 (pdf p. 255),
recalling Chapter IV, §5. Locators give Milne's printed page numbers (printed page = pdf page − 9).

For a field $K$, elements $a, b \in K$ and $\zeta \in K^\times$, $A(a,b;\zeta)$ is the $K$-algebra with generators $i, j$
and relations
$$i^n = a,\qquad j^n = b,\qquad ij = \zeta ji .$$
Milne takes $a, b \in K^\times$ and $\zeta$ a primitive $n$th root of $1$; the definition (a quotient of the free
algebra on two generators) needs neither hypothesis, so it is stated without them.

* `SymbolAlgebra n a b ζ`: the algebra $A(a,b;\zeta)$, with generators `SymbolAlgebra.i`, `SymbolAlgebra.j` and the
  three relations (`i_pow`, `j_pow`, `i_mul_j`).
* `SymbolAlgebra.lift`: the universal property (a pair of elements satisfying the relations).
* **5.7, the algebra part** (p. 246): $A(b,a;\zeta) \cong A(a,b;\zeta^{-1})$ (`swapEquiv`) and
  $A(a,b;\zeta)^{\mathrm{opp}} \cong A(a,b;\zeta^{-1})$ (`opEquiv`).
* "In the case that $n = 2$, $A(a,b;-1)$ is the quaternion algebra $H(a,b)$" (p. 246): `quaternionEquiv`, an
  isomorphism with Mathlib's `QuaternionAlgebra K a 0 b`.

Not formalized: that $A(a,b;\zeta)$ is central simple of degree $n$ when $a, b \ne 0$ and $\zeta$ is a primitive $n$th
root of $1$ (Milne, IV.5), and its class in the Brauer group.
-/

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type*} [Field K]

/-- The relations $i^n = a$, $j^n = b$, $ij = \zeta ji$ on the free algebra on two generators
(`FreeAlgebra.ι K 0` $= i$, `FreeAlgebra.ι K 1` $= j$). -/
inductive SymbolRel (n : ℕ) (a b : K) (ζ : Kˣ) : FreeAlgebra K (Fin 2) → FreeAlgebra K (Fin 2) → Prop
  | i_pow : SymbolRel n a b ζ (FreeAlgebra.ι K 0 ^ n) (algebraMap K _ a)
  | j_pow : SymbolRel n a b ζ (FreeAlgebra.ι K 1 ^ n) (algebraMap K _ b)
  | i_mul_j : SymbolRel n a b ζ (FreeAlgebra.ι K 0 * FreeAlgebra.ι K 1)
      ((ζ : K) • (FreeAlgebra.ι K 1 * FreeAlgebra.ι K 0))

/-- **The algebra $A(a,b;\zeta)$** (definition in prose; Milne, *CFT*, VIII, §5, p. 246, and IV, §5): the $K$-algebra with
generators $i, j$ and relations $i^n = a$, $j^n = b$, $ij = \zeta ji$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, §5, the algebra A(a,b;ζ), p. 246"]
def SymbolAlgebra (n : ℕ) (a b : K) (ζ : Kˣ) : Type _ :=
  RingQuot (SymbolRel n a b ζ)

namespace SymbolAlgebra

variable (n : ℕ) (a b : K) (ζ : Kˣ)

instance : Ring (SymbolAlgebra n a b ζ) := inferInstanceAs (Ring (RingQuot (SymbolRel n a b ζ)))

instance : Algebra K (SymbolAlgebra n a b ζ) := inferInstanceAs (Algebra K (RingQuot (SymbolRel n a b ζ)))

/-- The quotient map from the free algebra. -/
def mkₐ : FreeAlgebra K (Fin 2) →ₐ[K] SymbolAlgebra n a b ζ := RingQuot.mkAlgHom K (SymbolRel n a b ζ)

/-- The generator $i$. -/
def i : SymbolAlgebra n a b ζ := mkₐ n a b ζ (FreeAlgebra.ι K 0)

/-- The generator $j$. -/
def j : SymbolAlgebra n a b ζ := mkₐ n a b ζ (FreeAlgebra.ι K 1)

theorem i_pow : i n a b ζ ^ n = algebraMap K _ a := by
  have h := RingQuot.mkAlgHom_rel K (SymbolRel.i_pow (n := n) (a := a) (b := b) (ζ := ζ))
  rw [map_pow, AlgHom.commutes] at h
  exact h

theorem j_pow : j n a b ζ ^ n = algebraMap K _ b := by
  have h := RingQuot.mkAlgHom_rel K (SymbolRel.j_pow (n := n) (a := a) (b := b) (ζ := ζ))
  rw [map_pow, AlgHom.commutes] at h
  exact h

theorem i_mul_j : i n a b ζ * j n a b ζ = (ζ : K) • (j n a b ζ * i n a b ζ) := by
  have h := RingQuot.mkAlgHom_rel K (SymbolRel.i_mul_j (n := n) (a := a) (b := b) (ζ := ζ))
  rw [map_mul, map_smul, map_mul] at h
  exact h

private theorem j_mul_i_aux (u : Kˣ) :
    j n a b u * i n a b u = ((u⁻¹ : Kˣ) : K) • (i n a b u * j n a b u) := by
  rw [i_mul_j n a b u, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

variable {n a b ζ}

/-- **The universal property**: elements $x, y$ of a $K$-algebra with $x^n = a$, $y^n = b$, $xy = \zeta yx$ define a
homomorphism $A(a,b;\zeta) \to B$ with $i \mapsto x$, $j \mapsto y$. -/
def lift {B : Type*} [Ring B] [Algebra K B] (x y : B) (hx : x ^ n = algebraMap K B a)
    (hy : y ^ n = algebraMap K B b) (hxy : x * y = (ζ : K) • (y * x)) : SymbolAlgebra n a b ζ →ₐ[K] B :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K ![x, y], by
    intro u v h
    cases h with
    | i_pow => simpa using hx
    | j_pow => simpa using hy
    | i_mul_j => simpa using hxy⟩

@[simp]
theorem lift_i {B : Type*} [Ring B] [Algebra K B] (x y : B) (hx : x ^ n = algebraMap K B a)
    (hy : y ^ n = algebraMap K B b) (hxy : x * y = (ζ : K) • (y * x)) : lift x y hx hy hxy (i n a b ζ) = x := by
  show RingQuot.liftAlgHom K _ (RingQuot.mkAlgHom K _ _) = x
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  simp

@[simp]
theorem lift_j {B : Type*} [Ring B] [Algebra K B] (x y : B) (hx : x ^ n = algebraMap K B a)
    (hy : y ^ n = algebraMap K B b) (hxy : x * y = (ζ : K) • (y * x)) : lift x y hx hy hxy (j n a b ζ) = y := by
  show RingQuot.liftAlgHom K _ (RingQuot.mkAlgHom K _ _) = y
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  simp

/-- Two homomorphisms out of $A(a,b;\zeta)$ that agree on $i$ and $j$ are equal. -/
theorem algHom_ext {B : Type*} [Ring B] [Algebra K B] {f g : SymbolAlgebra n a b ζ →ₐ[K] B}
    (hi : f (i n a b ζ) = g (i n a b ζ)) (hj : f (j n a b ζ) = g (j n a b ζ)) : f = g := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext k
  fin_cases k
  · exact hi
  · exact hj

private theorem opHom_ext {B : Type*} [Ring B] [Algebra K B] {f g : (SymbolAlgebra n a b ζ)ᵐᵒᵖ →ₐ[K] B}
    (hi : f (MulOpposite.op (i n a b ζ)) = g (MulOpposite.op (i n a b ζ)))
    (hj : f (MulOpposite.op (j n a b ζ)) = g (MulOpposite.op (j n a b ζ))) : f = g := by
  apply AlgHom.opComm.symm.injective
  apply algHom_ext <;> simpa using ‹_›

variable (n a b ζ)

/-- **5.7, first isomorphism** (Milne, *CFT*, VIII, 5.7, p. 246): $A(b,a;\zeta) \cong A(a,b;\zeta^{-1})$, by
$i' \mapsto j$, $j' \mapsto i$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, 5.7, A(b,a;ζ) ≅ A(a,b;ζ⁻¹), p. 246"]
def swapEquiv : SymbolAlgebra n b a ζ ≃ₐ[K] SymbolAlgebra n a b ζ⁻¹ :=
  AlgEquiv.ofAlgHom
    (lift (j n a b ζ⁻¹) (i n a b ζ⁻¹) (j_pow _ _ _ _) (i_pow _ _ _ _) (by
      simpa using j_mul_i_aux n a b ζ⁻¹))
    (lift (j n b a ζ) (i n b a ζ) (j_pow _ _ _ _) (i_pow _ _ _ _) (j_mul_i_aux n b a ζ))
    (algHom_ext (by simp) (by simp)) (algHom_ext (by simp) (by simp))

@[simp] theorem swapEquiv_i : swapEquiv n a b ζ (i n b a ζ) = j n a b ζ⁻¹ := by
  simp [swapEquiv]

@[simp] theorem swapEquiv_j : swapEquiv n a b ζ (j n b a ζ) = i n a b ζ⁻¹ := by
  simp [swapEquiv]

/-- **5.7, second isomorphism** (Milne, *CFT*, VIII, 5.7, p. 246): $A(a,b;\zeta)^{\mathrm{opp}} \cong A(a,b;\zeta^{-1})$,
by $i \mapsto i$, $j \mapsto j$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, 5.7, A(a,b;ζ)^opp ≅ A(a,b;ζ⁻¹), p. 246"]
def opEquiv : (SymbolAlgebra n a b ζ)ᵐᵒᵖ ≃ₐ[K] SymbolAlgebra n a b ζ⁻¹ :=
  AlgEquiv.ofAlgHom
    (AlgHom.opComm (lift (n := n) (a := a) (b := b) (ζ := ζ)
      (MulOpposite.op (i n a b ζ⁻¹)) (MulOpposite.op (j n a b ζ⁻¹))
      (by rw [← MulOpposite.op_pow, i_pow]; rfl) (by rw [← MulOpposite.op_pow, j_pow]; rfl)
      (by
        rw [← MulOpposite.op_mul, ← MulOpposite.op_mul]
        have := j_mul_i_aux n a b ζ⁻¹
        rw [inv_inv] at this
        rw [this]
        rfl)))
    (lift (n := n) (a := a) (b := b) (ζ := ζ⁻¹)
      (MulOpposite.op (i n a b ζ)) (MulOpposite.op (j n a b ζ))
      (by rw [← MulOpposite.op_pow, i_pow]; rfl) (by rw [← MulOpposite.op_pow, j_pow]; rfl)
      (by
        rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, j_mul_i_aux n a b ζ]
        rfl))
    (algHom_ext (by simp) (by simp)) (opHom_ext (by simp) (by simp))

@[simp] theorem opEquiv_i : opEquiv n a b ζ (MulOpposite.op (i n a b ζ)) = i n a b ζ⁻¹ := by
  simp [opEquiv]

@[simp] theorem opEquiv_j : opEquiv n a b ζ (MulOpposite.op (j n a b ζ)) = j n a b ζ⁻¹ := by
  simp [opEquiv]

/-- "In the case that $n = 2$, $A(a,b;-1)$ is the quaternion algebra $H(a,b)$" (Milne, *CFT*, VIII, §5, p. 246): an
isomorphism with Mathlib's quaternion algebra `QuaternionAlgebra K a 0 b` ($i^2 = a$, $j^2 = b$, $ij = -ji$) sending $i, j$ to
its basis elements `⟨0, 1, 0, 0⟩` and `⟨0, 0, 1, 0⟩`. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, §5, A(a,b;−1) = H(a,b), p. 246"]
def quaternionEquiv : SymbolAlgebra 2 a b (-1) ≃ₐ[K] QuaternionAlgebra K a 0 b :=
  AlgEquiv.ofAlgHom
    (lift (n := 2) (a := a) (b := b) (ζ := -1)
      (⟨0, 1, 0, 0⟩ : QuaternionAlgebra K a 0 b) ⟨0, 0, 1, 0⟩
      (by ext <;> simp [pow_two]) (by ext <;> simp [pow_two]) (by ext <;> simp))
    (QuaternionAlgebra.Basis.liftHom
      ({ i := i 2 a b (-1)
         j := j 2 a b (-1)
         k := i 2 a b (-1) * j 2 a b (-1)
         i_mul_i := by simp [← pow_two, i_pow, Algebra.algebraMap_eq_smul_one]
         j_mul_j := by simp [← pow_two, j_pow, Algebra.algebraMap_eq_smul_one]
         i_mul_j := rfl
         j_mul_i := by
           have := i_mul_j 2 a b (-1)
           rw [this]
           simp } : QuaternionAlgebra.Basis (SymbolAlgebra 2 a b (-1)) a 0 b))
    (QuaternionAlgebra.hom_ext (by simp [QuaternionAlgebra.Basis.self, QuaternionAlgebra.Basis.lift])
      (by simp [QuaternionAlgebra.Basis.self, QuaternionAlgebra.Basis.lift]))
    (algHom_ext (by simp [QuaternionAlgebra.Basis.lift]) (by simp [QuaternionAlgebra.Basis.lift]))

@[simp] theorem quaternionEquiv_i : quaternionEquiv a b (i 2 a b (-1)) = (⟨0, 1, 0, 0⟩ : QuaternionAlgebra K a 0 b) := by
  simp [quaternionEquiv]

@[simp] theorem quaternionEquiv_j : quaternionEquiv a b (j 2 a b (-1)) = (⟨0, 0, 1, 0⟩ : QuaternionAlgebra K a 0 b) := by
  simp [quaternionEquiv]

end SymbolAlgebra

end NumberFieldKB.MilneCFT.Ch8
