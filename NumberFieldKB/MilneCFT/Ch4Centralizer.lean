import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4SkolemNoether
import NumberFieldKB.MilneCFT.Ch4Brauer

/-!
# Milne, Class Field Theory, Chapter IV, §3: maximal subfields

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV, §3, "Maximal subfields": the centralizer theorem in a central simple algebra
(Thm. 3.1) and Corollaries 3.3–3.5; splitting fields (Cor. 3.6–3.10, Prop. 2.17) are in
`Ch4Splitting.lean`.

A *subfield* of a $K$-algebra $A$ containing $K$ is a `Subalgebra K A` that is a field
(`IsField`).  All algebras are finite dimensional over $K$ (Milne's convention).
Locators give the printed page of the book (printed page = pdf page − 9).
-/

open scoped TensorProduct

namespace NumberFieldKB.MilneCFT.Ch4

universe u v

variable {K : Type u} [Field K]

/-! ### Helper lemmas for Theorem 3.1 -/

/-- Over a field, the tensor product of injective algebra maps is injective. -/
lemma centralizer_map_injective {A : Type v} {A' : Type*} {C C' : Type*} [Ring C]
    [Algebra K C] [Ring C'] [Algebra K C'] [Ring A] [Algebra K A] [Ring A'] [Algebra K A']
    (f : C →ₐ[K] A) (g : C' →ₐ[K] A') (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.map f g) := by
  have := TensorProduct.map_injective_of_flat_flat (R := K) f.toLinearMap g.toLinearMap hf hg
  have h : ⇑(Algebra.TensorProduct.map f g) =
      ⇑(TensorProduct.map f.toLinearMap g.toLinearMap) := by
    funext t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [h]; exact this

lemma range_map_bot_right {A : Type v} {A' : Type*} [Ring A] [Algebra K A] [Ring A']
    [Algebra K A'] (X : Subalgebra K A) :
    (Algebra.TensorProduct.map X.val (⊥ : Subalgebra K A').val).range =
      ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A').comp X.val).range := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨k, hk⟩ := Algebra.mem_bot.mp y.2
      refine ⟨k • x, ?_⟩
      have hy : (y : A') = algebraMap K A' k := hk.symm
      simp [hy, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add s t hs ht => rw [map_add]; exact Subalgebra.add_mem _ hs ht
  · rintro _ ⟨x, rfl⟩
    exact ⟨x ⊗ₜ 1, by simp⟩

lemma range_map_bot_left {A : Type v} {A' : Type*} [Ring A] [Algebra K A] [Ring A']
    [Algebra K A'] (Y : Subalgebra K A') :
    (Algebra.TensorProduct.map (⊥ : Subalgebra K A).val Y.val).range =
      ((Algebra.TensorProduct.includeRight : A' →ₐ[K] A ⊗[K] A').comp Y.val).range := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨k, hk⟩ := Algebra.mem_bot.mp x.2
      refine ⟨k • y, ?_⟩
      have hx : (x : A) = algebraMap K A k := hk.symm
      simp [hx, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add s t hs ht => rw [map_add]; exact Subalgebra.add_mem _ hs ht
  · rintro _ ⟨y, rfl⟩
    exact ⟨1 ⊗ₜ y, by simp⟩

/-- Proposition 2.3 as an algebra isomorphism. -/
noncomputable def centralizerRangeEquiv {A : Type v} {A' : Type*} [Ring A] [Algebra K A]
    [Ring A'] [Algebra K A'] (X : Subalgebra K A) (Y : Subalgebra K A') :
    (Subalgebra.centralizer K (X : Set A) ⊗[K] Subalgebra.centralizer K (Y : Set A')) ≃ₐ[K]
      Subalgebra.centralizer K
        (((Algebra.TensorProduct.map X.val Y.val).range : Subalgebra K (A ⊗[K] A')) :
          Set (A ⊗[K] A')) :=
  (AlgEquiv.ofInjective _ (centralizer_map_injective (K := K) _ _ Subtype.val_injective
    Subtype.val_injective)).trans (Subalgebra.equivOfEq _ _ (prop_2_3 A A' X Y).symm)

/-- The centralizer of `⊥` is everything. -/
noncomputable def centralizerBotEquiv (A : Type v) [Ring A] [Algebra K A] :
    Subalgebra.centralizer K ((⊥ : Subalgebra K A) : Set A) ≃ₐ[K] A :=
  AlgEquiv.ofBijective (Subalgebra.val _) ⟨Subtype.val_injective, fun a =>
    ⟨⟨a, by
      rw [Subalgebra.mem_centralizer_iff]
      rintro z hz
      obtain ⟨k, rfl⟩ := Algebra.mem_bot.mp hz
      exact Algebra.commutes k a⟩, rfl⟩⟩

/-- Conjugate subalgebras have isomorphic centralizers. -/
lemma centralizer_conj_equiv {T B : Type*} [Ring T] [Algebra K T] [Ring B] [Algebra K B]
    (f g : B →ₐ[K] T) (u : Tˣ) (hu : ∀ b, f b = u * g b * ↑u⁻¹) :
    Nonempty (Subalgebra.centralizer K (g.range : Set T) ≃ₐ[K]
      Subalgebra.centralizer K (f.range : Set T)) := by
  let φ : T ≃ₐ[K] T :=
    { toFun := fun x => u * x * ↑u⁻¹
      invFun := fun x => ↑u⁻¹ * x * u
      left_inv := fun x => by simp [mul_assoc]
      right_inv := fun x => by simp [mul_assoc]
      map_mul' := fun x y => by simp [mul_assoc]
      map_add' := fun x y => by simp [mul_add, add_mul]
      commutes' := fun r => by
        simp [Algebra.algebraMap_eq_smul_one] }
  have hmap : (Subalgebra.centralizer K (g.range : Set T)).map φ.toAlgHom =
      Subalgebra.centralizer K (f.range : Set T) := by
    ext x
    simp only [Subalgebra.mem_map, Subalgebra.mem_centralizer_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩ z ⟨b, rfl⟩
      have h := hy (g b) ⟨b, rfl⟩
      have e1 : f b * φ.toAlgHom y = u * (g b * y) * ↑u⁻¹ := by
        rw [hu b]; simp [φ, mul_assoc]
      have e2 : φ.toAlgHom y * f b = u * (y * g b) * ↑u⁻¹ := by
        rw [hu b]; simp [φ, mul_assoc]
      change f b * φ.toAlgHom y = φ.toAlgHom y * f b
      rw [e1, e2, h]
    · intro hx
      refine ⟨↑u⁻¹ * x * u, ?_, by simp [φ, mul_assoc]⟩
      rintro z ⟨b, rfl⟩
      have h := hx (f b) ⟨b, rfl⟩
      have hg : g b = ↑u⁻¹ * f b * u := by rw [hu b]; simp [mul_assoc]
      have e1 : g b * (↑u⁻¹ * x * u) = ↑u⁻¹ * (f b * x) * u := by
        rw [hg]; simp [mul_assoc]
      have e2 : (↑u⁻¹ * x * u) * g b = ↑u⁻¹ * (x * f b) * u := by
        rw [hg]; simp [mul_assoc]
      change g b * (↑u⁻¹ * x * u) = (↑u⁻¹ * x * u) * g b
      rw [e1, e2, h]
  exact ⟨(AlgEquiv.subalgebraMap φ _).trans (Subalgebra.equivOfEq _ _ hmap)⟩

/-- Right multiplication, as a `K`-algebra homomorphism `Bᵐᵒᵖ → End_K(B)`. -/
noncomputable def mulRightHom (B : Type*) [Ring B] [Algebra K B] :
    Bᵐᵒᵖ →ₐ[K] Module.End K B where
  toFun x := LinearMap.mulRight K x.unop
  map_one' := by ext z; simp
  map_mul' x y := by ext z; simp [mul_assoc]
  map_zero' := by ext z; simp
  map_add' x y := by ext z; simp [mul_add]
  commutes' r := by
    ext z
    change z * algebraMap K B r = algebraMap K (Module.End K B) r z
    rw [Module.algebraMap_end_apply, Algebra.smul_def, Algebra.commutes]

lemma mulRightHom_injective (B : Type*) [Ring B] [Algebra K B] :
    Function.Injective (mulRightHom (K := K) B) := by
  intro x y h
  have := LinearMap.congr_fun h 1
  simpa [mulRightHom] using this

lemma range_mulRightHom (B : Type*) [Ring B] [Algebra K B] :
    (mulRightHom (K := K) B).range =
      Subalgebra.centralizer K
        (((Algebra.lmul K B).range : Subalgebra K (Module.End K B)) : Set (Module.End K B)) := by
  ext φ
  constructor
  · rintro ⟨x, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    ext z
    simp [mulRightHom, mul_assoc]
  · intro h
    rw [Subalgebra.mem_centralizer_iff] at h
    refine ⟨MulOpposite.op (φ 1), ?_⟩
    ext z
    have := LinearMap.congr_fun (h (Algebra.lmul K B z) ⟨z, rfl⟩) 1
    simpa [mulRightHom] using this

/-- The centralizer of left multiplications in `End_K(B)` is `Bᵐᵒᵖ` (right multiplications). -/
noncomputable def centralizerLmulEquiv (B : Type*) [Ring B] [Algebra K B] :
    Bᵐᵒᵖ ≃ₐ[K] Subalgebra.centralizer K
        (((Algebra.lmul K B).range : Subalgebra K (Module.End K B)) : Set (Module.End K B)) :=
  (AlgEquiv.ofInjective _ (mulRightHom_injective (K := K) B)).trans
    (Subalgebra.equivOfEq _ _ (range_mulRightHom (K := K) B))

/-- Key lemma: simplicity of the centralizer and the dimension formula. -/
theorem dim_formula_and_simple (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (B : Subalgebra K A) [IsSimpleRing B] :
    IsSimpleRing (Subalgebra.centralizer K (B : Set A)) ∧
      Module.finrank K B * Module.finrank K (Subalgebra.centralizer K (B : Set A)) =
        Module.finrank K A := by
  classical
  have hdpos : 0 < Module.finrank K B := Module.finrank_pos
  let bB := Module.finBasis K B
  let eE : Module.End K B ≃ₐ[K] Matrix (Fin (Module.finrank K B)) (Fin (Module.finrank K B)) K :=
    LinearMap.toMatrixAlgEquiv bB
  haveI : Nonempty (Fin (Module.finrank K B)) := ⟨⟨0, hdpos⟩⟩
  haveI hEs : IsSimpleRing (Module.End K B) :=
    IsSimpleRing.of_ringEquiv eE.symm.toRingEquiv inferInstance
  have hEdim : Module.finrank K (Module.End K B) =
      Module.finrank K B * Module.finrank K B := by
    rw [eE.toLinearEquiv.finrank_eq, Module.finrank_matrix]; simp
  obtain ⟨f, hf⟩ : ∃ f : B →ₐ[K] A ⊗[K] Module.End K B,
      f = (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] Module.End K B).comp B.val :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : B →ₐ[K] A ⊗[K] Module.End K B,
      g = (Algebra.TensorProduct.includeRight : Module.End K B →ₐ[K] A ⊗[K] Module.End K B).comp
        (Algebra.lmul K B) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu⟩ := thm_2_10 (K := K) B (A ⊗[K] Module.End K B) f g
  obtain ⟨e1⟩ := centralizer_conj_equiv f g u hu
  have hFr : (Algebra.TensorProduct.map B.val (⊥ : Subalgebra K (Module.End K B)).val).range =
      f.range := by
    rw [range_map_bot_right, hf]
  have hGr : (Algebra.TensorProduct.map (⊥ : Subalgebra K A).val
      (Algebra.lmul K B).range.val).range = g.range := by
    rw [range_map_bot_left, hg, AlgHom.range_comp, AlgHom.range_comp, Subalgebra.range_val]
  let eF := (centralizerRangeEquiv (K := K) B (⊥ : Subalgebra K (Module.End K B))).trans
    (Subalgebra.equivOfEq _ _ (by rw [hFr]))
  let eG := (centralizerRangeEquiv (K := K) (⊥ : Subalgebra K A) (Algebra.lmul K B).range).trans
    (Subalgebra.equivOfEq _ _ (by rw [hGr]))
  let eFull : (Subalgebra.centralizer K (B : Set A) ⊗[K] Module.End K B) ≃ₐ[K]
      (A ⊗[K] Bᵐᵒᵖ) :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl) (centralizerBotEquiv (K := K)
      (Module.End K B)).symm).trans eF |>.trans e1.symm |>.trans eG.symm).trans
      (Algebra.TensorProduct.congr (centralizerBotEquiv (K := K) A)
        (centralizerLmulEquiv (K := K) B).symm)
  haveI : IsSimpleRing (A ⊗[K] Bᵐᵒᵖ) := prop_2_6 A Bᵐᵒᵖ (Or.inl inferInstance)
  haveI hCE : IsSimpleRing (Subalgebra.centralizer K (B : Set A) ⊗[K] Module.End K B) :=
    IsSimpleRing.of_ringEquiv eFull.symm.toRingEquiv this
  let eM : Matrix (Fin (Module.finrank K B)) (Fin (Module.finrank K B))
      (Subalgebra.centralizer K (B : Set A)) ≃ₐ[K]
      (Subalgebra.centralizer K (B : Set A) ⊗[K] Module.End K B) :=
    (matrixEquivTensor (Fin (Module.finrank K B)) K (Subalgebra.centralizer K (B : Set A))).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl) eE.symm)
  haveI hMat : IsSimpleRing (Matrix (Fin (Module.finrank K B)) (Fin (Module.finrank K B))
      (Subalgebra.centralizer K (B : Set A))) :=
    IsSimpleRing.of_ringEquiv eM.symm.toRingEquiv hCE
  refine ⟨⟨(TwoSidedIdeal.orderIsoMatrix (n := Fin (Module.finrank K B))).isSimpleOrder⟩, ?_⟩
  have h1 := eFull.toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct, hEdim,
    ← (MulOpposite.opLinearEquiv K (M := B)).finrank_eq] at h1
  have : Module.finrank K B * (Module.finrank K B *
      Module.finrank K (Subalgebra.centralizer K (B : Set A))) =
      Module.finrank K B * Module.finrank K A := by
    calc _ = Module.finrank K (Subalgebra.centralizer K (B : Set A)) *
          (Module.finrank K B * Module.finrank K B) := by ring
      _ = _ := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hdpos this

/-- A commutative subalgebra of a finite-dimensional division algebra is a field. -/
lemma isField_of_comm {D : Type v} [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (L : Subalgebra K D) (hc : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) : IsField L where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm a b := Subtype.ext (hc a a.2 b b.2)
  mul_inv_cancel {a} ha := by
    have hinj : Function.Injective (LinearMap.mulLeft K a) := fun y z h => by
      have : a * y = a * z := h
      exact mul_left_cancel₀ ha this
    obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
    exact ⟨b, hb⟩

/-- Theorem 3.1 of Milne: let $B$ be a simple $K$-subalgebra of a central simple $K$-algebra
$A$.  Then the centralizer $C = C_A(B)$ is simple, $B$ is the centralizer of $C$, and
$[B : K][C : K] = [A : K]$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 3.1, p. 132"]
theorem thm_3_1 (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (B : Subalgebra K A) [IsSimpleRing B] :
    IsSimpleRing (Subalgebra.centralizer K (B : Set A)) ∧
      Subalgebra.centralizer K (Subalgebra.centralizer K (B : Set A) : Set A) = B ∧
      Module.finrank K B * Module.finrank K (Subalgebra.centralizer K (B : Set A)) =
        Module.finrank K A := by
  obtain ⟨hs, hdim⟩ := dim_formula_and_simple A B
  refine ⟨hs, ?_, hdim⟩
  haveI := hs
  obtain ⟨_, hdim2⟩ := dim_formula_and_simple A (Subalgebra.centralizer K (B : Set A))
  have hle : B ≤ Subalgebra.centralizer K
      (Subalgebra.centralizer K (B : Set A) : Set A) := fun b hb => by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    exact ((Subalgebra.mem_centralizer_iff (R := K)).mp hg b hb).symm
  have hpos : 0 < Module.finrank K (Subalgebra.centralizer K (B : Set A)) :=
    Module.finrank_pos
  have hfr : Module.finrank K B = Module.finrank K
      (Subalgebra.centralizer K (Subalgebra.centralizer K (B : Set A) : Set A)) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hdim2, mul_comm, hdim]
  exact (Subalgebra.eq_of_le_of_finrank_eq hle hfr).symm

/-- Corollary 3.3 of Milne: if in Theorem 3.1 the subalgebra $B$ has centre $K$, then so does its
centralizer $C$, and the multiplication map $B \otimes_K C \to A$, $b \otimes c \mapsto bc$, is an
isomorphism. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.3, p. 132"]
theorem cor_3_3 (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (B : Subalgebra K A) [IsSimpleRing B] [Algebra.IsCentral K B] :
    Algebra.IsCentral K (Subalgebra.centralizer K (B : Set A)) ∧
      Function.Bijective (Algebra.TensorProduct.lift B.val
        (Subalgebra.centralizer K (B : Set A)).val
        (fun b c => (c.2 b b.2 : (b : A) * c = c * b))) := by
  obtain ⟨hs, hbc, hdim⟩ := thm_3_1 (K := K) A B
  have hCc : Algebra.IsCentral K (Subalgebra.centralizer K (B : Set A)) := by
    refine ⟨fun z hz => ?_⟩
    have hz' := Subalgebra.mem_center_iff.mp hz
    have hzB : (z : A) ∈ B := by
      have : (z : A) ∈ Subalgebra.centralizer K
          (Subalgebra.centralizer K (B : Set A) : Set A) := by
        rw [Subalgebra.mem_centralizer_iff]
        intro g hg
        exact congrArg Subtype.val (hz' ⟨g, hg⟩)
      rwa [hbc] at this
    have hw : (⟨z, hzB⟩ : B) ∈ Subalgebra.center K B := by
      rw [Subalgebra.mem_center_iff]
      intro b
      exact Subtype.ext (z.2 b b.2)
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hw)
    refine Algebra.mem_bot.mpr ⟨k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨hCc, ?_⟩
  haveI := hs
  have hT := cor_2_8 (K := K) B (Subalgebra.centralizer K (B : Set A))
  set Φ := Algebra.TensorProduct.lift B.val (Subalgebra.centralizer K (B : Set A)).val
    (fun b c => (c.2 b b.2 : (b : A) * c = c * b)) with hΦ
  haveI := hT.2
  have hinj : Function.Injective Φ := RingHom.injective Φ.toRingHom
  refine ⟨hinj, ?_⟩
  have hfr : Module.finrank K (B ⊗[K] Subalgebra.centralizer K (B : Set A)) =
      Module.finrank K A := by
    rw [Module.finrank_tensorProduct, hdim]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := Φ.toLinearMap) hfr).mp hinj

/-- Corollary 3.4 of Milne: let $L$ be a subfield of a central simple $K$-algebra $A$ containing
$K$.  The following are equivalent: (a) $L$ equals its centralizer in $A$; (b)
$[A : K] = [L : K]^2$; (c) $L$ is a maximal commutative $K$-subalgebra of $A$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.4, p. 133"]
theorem cor_3_4 (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (L : Subalgebra K A) (hL : IsField L) :
    List.TFAE
      [Subalgebra.centralizer K (L : Set A) = L,
       Module.finrank K A = Module.finrank K L ^ 2,
       ∀ L' : Subalgebra K A, L ≤ L' → (∀ x ∈ L', ∀ y ∈ L', x * y = y * x) → L' = L] := by
  have hLs : IsSimpleRing L := @DivisionRing.isSimpleRing L hL.toField.toDivisionRing
  have hLc : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hL.mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hle : L ≤ Subalgebra.centralizer K (L : Set A) := fun x hx => by
    rw [Subalgebra.mem_centralizer_iff]
    exact fun g hg => hLc g hg x hx
  obtain ⟨_, hdim⟩ := dim_formula_and_simple A L
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  tfae_have 1 → 2 := by
    intro h
    rw [h] at hdim
    rw [← hdim]; ring
  tfae_have 2 → 1 := by
    intro h
    have hfr : Module.finrank K L = Module.finrank K (Subalgebra.centralizer K (L : Set A)) := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [hdim, h]; ring
    exact (Subalgebra.eq_of_le_of_finrank_eq hle hfr).symm
  tfae_have 1 → 3 := by
    intro h L' hLL' hc
    apply le_antisymm _ hLL'
    intro x hx
    have : x ∈ Subalgebra.centralizer K (L : Set A) := by
      rw [Subalgebra.mem_centralizer_iff]
      exact fun g hg => hc g (hLL' hg) x hx
    rwa [h] at this
  tfae_have 3 → 1 := by
    intro h
    apply le_antisymm _ hle
    intro a ha
    have ha' := (Subalgebra.mem_centralizer_iff (R := K)).mp ha
    have hs : ∀ b ∈ (L : Set A) ∪ {a}, ∀ c ∈ (L : Set A) ∪ {a}, Commute b c := by
      rintro b (hb | hb) c (hc | hc)
      · exact hLc b hb c hc
      · rw [Set.mem_singleton_iff.mp hc]; exact ha' b hb
      · rw [Set.mem_singleton_iff.mp hb]; exact (ha' c hc).symm
      · rw [Set.mem_singleton_iff.mp hb, Set.mem_singleton_iff.mp hc]
    have h1 : ∀ b ∈ (L : Set A) ∪ {a}, ∀ y ∈ Algebra.adjoin K ((L : Set A) ∪ {a}),
        Commute b y := fun b hb y hy =>
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy (fun c hc => hs b hb c hc)
    have hcomm : ∀ x ∈ Algebra.adjoin K ((L : Set A) ∪ {a}),
        ∀ y ∈ Algebra.adjoin K ((L : Set A) ∪ {a}), x * y = y * x := fun x hx y hy =>
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy (fun b hb => (h1 b hb x hx).symm)
    have hLL' : L ≤ Algebra.adjoin K ((L : Set A) ∪ {a}) :=
      fun x hx => Algebra.subset_adjoin (Or.inl hx)
    have heq := h _ hLL' hcomm
    have : a ∈ Algebra.adjoin K ((L : Set A) ∪ {a}) := Algebra.subset_adjoin (Or.inr rfl)
    rwa [heq] at this
  tfae_finish

/-- Corollary 3.5 of Milne: the maximal subfields containing $K$ of a central division
$K$-algebra $D$ are exactly those of degree $\sqrt{[D : K]}$ over $K$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.5, p. 133"]
theorem cor_3_5 (D : Type v) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (L : Subalgebra K D) (hL : IsField L) :
    (∀ L' : Subalgebra K D, IsField L' → L ≤ L' → L' = L) ↔
      Module.finrank K D = Module.finrank K L ^ 2 := by
  have key := cor_3_4 (K := K) D L hL
  have hbc : Module.finrank K D = Module.finrank K L ^ 2 ↔
      ∀ L' : Subalgebra K D, L ≤ L' → (∀ x ∈ L', ∀ y ∈ L', x * y = y * x) → L' = L :=
    key.out 2 3
  constructor
  · intro H
    rw [hbc]
    intro L' hle hc
    exact H L' (isField_of_comm L' hc) hle
  · intro h
    have hc := hbc.mp h
    intro L' hL' hle
    exact hc L' hle (fun x hx y hy => congrArg Subtype.val (hL'.mul_comm ⟨x, hx⟩ ⟨y, hy⟩))

end NumberFieldKB.MilneCFT.Ch4
