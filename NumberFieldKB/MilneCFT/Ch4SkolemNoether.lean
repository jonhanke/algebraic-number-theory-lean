import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Have
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Tensor
import NumberFieldKB.MilneCFT.Ch4Modules

/-!
# Milne, Class Field Theory, Chapter IV, §2: the Noether–Skolem theorem

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV, §2: Theorem 2.10 (Skolem, Noether) and Corollaries 2.11, 2.12, and the example
$\mathrm{Aut}(M_n(k)) = \mathrm{PGL}_n(k)$.

Milne's proof: two homomorphisms $f, g : A \to B$ make $B$ into two modules over the simple
algebra $A \otimes_k B^{\mathrm{opp}}$ (Prop. 2.6) of the same dimension; these are isomorphic
(Cor. 1.21), and an isomorphism is right multiplication-compatible, hence is left multiplication
by an invertible element $b$ with $f(a) b = b g(a)$.

All algebras are finite dimensional over the field $K$ (Milne's convention).  Locators give the
printed page of the book (printed page = pdf page − 9).
-/

namespace NumberFieldKB.MilneCFT.Ch4

universe u v w

variable {K : Type u} [Field K]

open scoped TensorProduct

/-- Right multiplication as a `K`-algebra homomorphism `Bᵐᵒᵖ → End_K(B)`. -/
def mulRightOp (B : Type w) [Ring B] [Algebra K B] : Bᵐᵒᵖ →ₐ[K] Module.End K B where
  toFun b := LinearMap.mulRight K b.unop
  map_one' := by ext v; simp
  map_mul' x y := by ext v; simp [mul_assoc]
  map_zero' := by ext v; simp
  map_add' x y := by ext v; simp [mul_add]
  commutes' r := by
    ext v
    simp [Algebra.algebraMap_eq_smul_one]

/-- The algebra homomorphism `A ⊗ Bᵐᵒᵖ → End_K(B)`, `a ⊗ b' ↦ (v ↦ f a * v * b')`. -/
noncomputable def actHom {A : Type v} {B : Type w} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f : A →ₐ[K] B) : (A ⊗[K] Bᵐᵒᵖ) →ₐ[K] Module.End K B :=
  Algebra.TensorProduct.lift ((Algebra.lmul K B).comp f)
    (mulRightOp B) (fun a b => by
      ext v
      simp [mulRightOp, mul_assoc])

theorem actHom_apply {A : Type v} {B : Type w} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f : A →ₐ[K] B) (a : A) (b : Bᵐᵒᵖ) (v : B) :
    actHom f (a ⊗ₜ[K] b) v = f a * v * b.unop := by
  simp [actHom, mulRightOp, mul_assoc]

/-- `B` as a module over `A ⊗ Bᵐᵒᵖ` through an algebra map to `End_K(B)`. -/
def TwistMod {A : Type v} (B : Type w) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (_ρ : (A ⊗[K] Bᵐᵒᵖ) →ₐ[K] Module.End K B) : Type w := B

section twist
variable {A : Type v} {B : Type w} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  (ρ : (A ⊗[K] Bᵐᵒᵖ) →ₐ[K] Module.End K B)

instance : AddCommGroup (TwistMod B ρ) := inferInstanceAs (AddCommGroup B)
instance : Module K (TwistMod B ρ) := inferInstanceAs (Module K B)
instance : Module (A ⊗[K] Bᵐᵒᵖ) (TwistMod B ρ) :=
  Module.compHom B ρ.toRingHom
instance [FiniteDimensional K B] : FiniteDimensional K (TwistMod B ρ) :=
  inferInstanceAs (FiniteDimensional K B)
instance : IsScalarTower K (A ⊗[K] Bᵐᵒᵖ) (TwistMod B ρ) :=
  ⟨fun k r v => by
    show ρ (k • r) v = k • ρ r v
    rw [map_smul]; rfl⟩

theorem twist_smul (r : A ⊗[K] Bᵐᵒᵖ) (v : TwistMod B ρ) :
    r • v = (ρ r v : B) := rfl

/-- Identity, into the module synonym. -/
def tw (b : B) : TwistMod B ρ := b

/-- Identity, out of the module synonym. -/
def un {ρ : (A ⊗[K] Bᵐᵒᵖ) →ₐ[K] Module.End K B} (v : TwistMod B ρ) : B := v

end twist

/-- Theorem 2.10 of Milne (Skolem, Noether): let $f, g : A \to B$ be homomorphisms of
$K$-algebras with $A$ simple and $B$ central simple.  Then there is an invertible $b \in B$ with
$f(a) = b\, g(a)\, b^{-1}$ for all $a \in A$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 2.10, p. 129"]
theorem thm_2_10 (A : Type v) (B : Type w) [Ring A] [Algebra K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B]
    [FiniteDimensional K B] (f g : A →ₐ[K] B) :
    ∃ b : Bˣ, ∀ a : A, f a = b * g a * ↑b⁻¹ := by
  have : IsSimpleRing (A ⊗[K] Bᵐᵒᵖ) :=
    isSimpleRing_tensorProduct_of_isCentral_right A Bᵐᵒᵖ
  have _i1 : IsScalarTower K (A ⊗[K] Bᵐᵒᵖ) (TwistMod B (actHom f)) := inferInstance
  have _i2 : IsScalarTower K (A ⊗[K] Bᵐᵒᵖ) (TwistMod B (actHom g)) := inferInstance
  have hne : Nonempty (TwistMod B (actHom g) ≃ₗ[A ⊗[K] Bᵐᵒᵖ] TwistMod B (actHom f)) :=
    cor_1_21 (K := K) (A := A ⊗[K] Bᵐᵒᵖ) (TwistMod B (actHom g))
      (TwistMod B (actHom f)) rfl
  obtain ⟨φ⟩ := hne
  obtain ⟨u, hu⟩ : ∃ u : B, u = un (φ (tw (actHom g) 1)) := ⟨_, rfl⟩
  have h1 : ∀ b : B, un (φ (tw (actHom g) b)) = u * b := by
    intro b
    have e : tw (actHom g) b = ((1 : A) ⊗ₜ[K] MulOpposite.op b) • tw (actHom g) 1 := by
      change b = actHom g ((1 : A) ⊗ₜ[K] MulOpposite.op b) 1
      rw [actHom_apply]; simp
    rw [e, map_smul]
    change actHom f ((1 : A) ⊗ₜ[K] MulOpposite.op b) (un (φ (tw (actHom g) 1))) = u * b
    rw [actHom_apply, ← hu]; simp
  have h2 : ∀ a : A, un (φ (tw (actHom g) (g a))) = f a * u := by
    intro a
    have e : tw (actHom g) (g a) = (a ⊗ₜ[K] (1 : Bᵐᵒᵖ)) • tw (actHom g) 1 := by
      change g a = actHom g (a ⊗ₜ[K] (1 : Bᵐᵒᵖ)) 1
      rw [actHom_apply]; simp
    rw [e, map_smul]
    change actHom f (a ⊗ₜ[K] (1 : Bᵐᵒᵖ)) (un (φ (tw (actHom g) 1))) = f a * u
    rw [actHom_apply, ← hu]; simp
  have hcomm : ∀ a : A, u * g a = f a * u := fun a => by rw [← h1, h2]
  obtain ⟨w', hw⟩ := φ.surjective (tw (actHom f) 1)
  have huw : u * un w' = 1 := by
    have := h1 (un w')
    change un (φ w') = _ at this
    rw [hw] at this
    exact this.symm
  have hwu : un w' * u = 1 := by
    have := φ.injective (a₁ := tw (actHom g) (un w' * u)) (a₂ := tw (actHom g) 1) (by
      change un (φ (tw (actHom g) (un w' * u))) = un (φ (tw (actHom g) 1))
      rw [h1, ← hu, ← mul_assoc, huw, one_mul])
    exact this
  refine ⟨⟨u, un w', huw, hwu⟩, fun a => ?_⟩
  show f a = u * g a * un w'
  rw [hcomm, mul_assoc, huw, mul_one]

/-- Corollary 2.11 of Milne: let $A$ be a central simple $K$-algebra and $B_1, B_2$ simple
$K$-subalgebras of $A$.  Every isomorphism $f : B_1 \to B_2$ is induced by an inner automorphism
of $A$: there is an invertible $a \in A$ with $f(b) = a b a^{-1}$ for all $b \in B_1$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 2.11, p. 129"]
theorem cor_2_11 (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (B₁ B₂ : Subalgebra K A) [IsSimpleRing B₁] [IsSimpleRing B₂]
    (f : B₁ ≃ₐ[K] B₂) : ∃ a : Aˣ, ∀ b : B₁, (f b : A) = a * b * ↑a⁻¹ := by
  obtain ⟨a, ha⟩ := thm_2_10 (K := K) B₁ A (B₂.val.comp f.toAlgHom) B₁.val
  exact ⟨a, fun b => ha b⟩

/-- Corollary 2.12 of Milne: every automorphism of a central simple $K$-algebra is inner. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 2.12, p. 129"]
theorem cor_2_12 (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (σ : A ≃ₐ[K] A) : ∃ a : Aˣ, ∀ x : A, σ x = a * x * ↑a⁻¹ := by
  obtain ⟨a, ha⟩ := thm_2_10 (K := K) A A σ.toAlgHom (AlgHom.id K A)
  exact ⟨a, fun x => ha x⟩

/-- The example after Corollary 2.12 of Milne: the automorphism group of $M_n(K)$ is
$\mathrm{PGL}_n(K) = \mathrm{GL}_n(K)/K^\times I_n$.  Stated as: every $K$-algebra automorphism
of $M_n(K)$ is conjugation by an invertible matrix, and conjugation by $g$ is the identity if and
only if $g$ is a nonzero scalar matrix. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §2, Aut(M_n(k)) = PGL_n(k) (after Cor. 2.12), p. 129"]
theorem aut_matrix_eq_pgl (n : ℕ) :
    (∀ σ : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K,
        ∃ g : (Matrix (Fin n) (Fin n) K)ˣ, ∀ x, σ x = (g : Matrix (Fin n) (Fin n) K) * x * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) ∧
      ∀ g : (Matrix (Fin n) (Fin n) K)ˣ,
        (∀ x, (g : Matrix (Fin n) (Fin n) K) * x * (↑g⁻¹ : Matrix (Fin n) (Fin n) K) = x) ↔
          ∃ c : Kˣ, (g : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) (c : K) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun σ => ⟨1, fun x => Subsingleton.elim _ _⟩, fun g => ?_⟩
    exact ⟨fun _ => ⟨1, Subsingleton.elim _ _⟩, fun _ x => Subsingleton.elim _ _⟩
  have : NeZero n := ⟨hn.ne'⟩
  refine ⟨fun σ => cor_2_12 (Matrix (Fin n) (Fin n) K) σ, fun g => ⟨fun h => ?_, ?_⟩⟩
  · have hc : (g : Matrix (Fin n) (Fin n) K) ∈ Set.range (Matrix.scalar (Fin n)) := by
      rw [Matrix.mem_range_scalar_iff_commute_single']
      intro i j
      have := h (Matrix.single i j (1 : K))
      show Matrix.single i j (1 : K) * g = g * Matrix.single i j (1 : K)
      calc Matrix.single i j (1 : K) * g
          = (g * Matrix.single i j (1 : K) * ↑g⁻¹) * g := by rw [this]
        _ = g * Matrix.single i j (1 : K) := by
          rw [mul_assoc, Units.inv_mul, mul_one]
    obtain ⟨c, hc⟩ := hc
    have hdet : IsUnit (Matrix.det (g : Matrix (Fin n) (Fin n) K)) :=
      (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    have hd : Matrix.det (g : Matrix (Fin n) (Fin n) K) = c ^ n := by
      rw [← hc]; simp [Matrix.scalar_apply]
    rw [hd] at hdet
    have hcu : IsUnit c := (isUnit_pow_iff hn.ne').mp hdet
    exact ⟨hcu.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩
  · rintro ⟨c, hc⟩ x
    have hcomm : (g : Matrix (Fin n) (Fin n) K) * x = x * g := by
      rw [hc]
      exact (Matrix.scalar_commute (n := Fin n) (c : K) (fun _ => Commute.all _ _) x).eq
    rw [hcomm, mul_assoc, Units.mul_inv, mul_one]

end NumberFieldKB.MilneCFT.Ch4
