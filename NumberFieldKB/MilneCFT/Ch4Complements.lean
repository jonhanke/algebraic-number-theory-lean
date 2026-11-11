import Mathlib.Algebra.QuaternionBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Unramified.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4SkolemNoether
import NumberFieldKB.MilneCFT.Ch4Brauer
import QuadFormsKB.Tamagawa.Quaternion

/-!
# Milne, Class Field Theory, Chapter IV, §5: complements

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV, §5: semisimple algebras under separable base change (Prop. 5.6) and the quaternion
algebra exercise (Exercise 5.7, the parts not already in QuadFormsKB).

Quaternion algebras.  Milne's $H(a, b)$ (basis $1, i, j, k = ij$ with $i^2 = a$, $j^2 = b$,
$ij = -ji$) is Mathlib's `ℍ[F,a,b]` (`QuaternionAlgebra F a 0 b`).  Parts (b), (c), (j) of
Exercise 5.7 are cited from QuadFormsKB in `Ch4Cite.lean`/`Ch4CiteQuat.lean`.

Locators give the printed page of the book (printed page = pdf page − 9).
-/

open scoped TensorProduct Quaternion

namespace NumberFieldKB.MilneCFT.Ch4

universe u v

variable {K : Type u} [Field K]

universe w

/-- Key lemma for Prop. 5.6. -/
theorem isSemisimpleRing_tensor_of_isCentral {Z : Type u} [Field Z] (E : Type v) [CommRing E]
    [Algebra Z E] [IsReduced E] (A : Type w) [Ring A] [Algebra Z A] [Algebra.IsCentral Z A]
    [IsSimpleRing A] [IsArtinianRing (E ⊗[Z] A)] : IsSemisimpleRing (E ⊗[Z] A) := by
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson]
  rw [eq_bot_iff]
  intro x hx
  have hspan := twoSidedIdeal_eq_span_of_isCentral E A
    (Ring.jacobson (E ⊗[Z] A)).toTwoSided
  have hxI : x ∈ ((Ring.jacobson (E ⊗[Z] A)).toTwoSided : Set (E ⊗[Z] A)) := by
    simpa using hx
  rw [hspan] at hxI
  have hgen : ∀ y ∈ {y : E ⊗[Z] A | ∃ (a : E) (b : A),
      a ⊗ₜ[Z] (1 : A) ∈ (Ring.jacobson (E ⊗[Z] A)).toTwoSided ∧ y = a ⊗ₜ[Z] b}, y = 0 := by
    rintro y ⟨e, b, he, rfl⟩
    have he' : e ⊗ₜ[Z] (1 : A) ∈ Ring.jacobson (E ⊗[Z] A) := by simpa using he
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := E ⊗[Z] A)
    have hpow : (e ⊗ₜ[Z] (1 : A)) ^ n ∈ (Ring.jacobson (E ⊗[Z] A)) ^ n :=
      Ideal.pow_mem_pow he' n
    have h0 : (e ⊗ₜ[Z] (1 : A)) ^ n = 0 := by
      rw [Ideal.jacobson_bot, hn] at *
      simpa using hpow
    have h1 : (e ^ n) ⊗ₜ[Z] (1 : A) = 0 := by
      rw [← h0, Algebra.TensorProduct.tmul_pow, one_pow]
    have h2 : e ^ n = 0 := by
      have hinj : Function.Injective (Algebra.TensorProduct.includeLeft (R := Z) (S := Z)
          (A := E) (B := A)) :=
        Algebra.TensorProduct.includeLeft_injective (algebraMap Z A).injective
      apply hinj
      simpa using h1
    have : e = 0 := IsReduced.eq_zero e ⟨n, h2⟩
    simp [this]
  have hz : ∀ y ∈ Submodule.span Z {y : E ⊗[Z] A | ∃ (a : E) (b : A),
      a ⊗ₜ[Z] (1 : A) ∈ (Ring.jacobson (E ⊗[Z] A)).toTwoSided ∧ y = a ⊗ₜ[Z] b}, y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul r y _ hy => simp [hy]
  exact hz x hxI


section Simple


/-- The center of a simple `K`-algebra is a field. -/
@[reducible] noncomputable def centerField (A : Type v) [Ring A] [Algebra K A] [IsSimpleRing A] :
    Field (Subalgebra.center K A) := by
  refine Field.ofIsUnitOrEqZero fun z => ?_
  by_cases hz : z = 0
  · exact Or.inr hz
  · refine Or.inl ?_
    have hmem : z.1 ∈ Subring.center A := by
      rw [Subring.mem_center_iff]
      exact fun g => (Subalgebra.mem_center_iff.mp z.2 g)
    have hne : (⟨z.1, hmem⟩ : Subring.center A) ≠ 0 := by
      intro h
      apply hz
      exact Subtype.ext (congrArg Subtype.val h)
    obtain ⟨y, hy⟩ := (IsSimpleRing.isField_center A).mul_inv_cancel hne
    refine IsUnit.of_mul_eq_one (⟨y.1, ?_⟩ : Subalgebra.center K A) ?_
    · rw [Subalgebra.mem_center_iff]
      exact fun g => Subring.mem_center_iff.mp y.2 g
    · apply Subtype.ext
      exact congrArg Subtype.val hy

end Simple


section Reduced


theorem isReduced_tensor_separable (Z : Type v) [Field Z] [Algebra K Z]
    (K' : Type u) [Field K'] [Algebra K K'] [Algebra.IsSeparable K K'] :
    IsReduced (Z ⊗[K] K') := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg (R := K) (C := Z) (A := K')
  intro B hB
  obtain ⟨s, hs⟩ := hB
  let L := IntermediateField.adjoin K (s : Set K')
  haveI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hBL : B ≤ L.toSubalgebra := by
    rw [← hs]
    exact IntermediateField.algebra_adjoin_le_adjoin K _
  let ι : B →ₐ[K] L := Subalgebra.inclusion hBL
  have hι : Function.Injective ι := Subalgebra.inclusion_injective hBL
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  haveI : IsReduced (Z ⊗[K] L) := Algebra.FormallyUnramified.isReduced_of_field Z (Z ⊗[K] L)
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id K Z) ι)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hι)

end Reduced

section Simple2


theorem isSemisimpleRing_tensor_of_isCentral_over {Z : Type v} [Field Z] [Algebra K Z]
    (A : Type v) [Ring A] [Algebra K A] [Algebra Z A] [IsScalarTower K Z A]
    [Algebra.IsCentral Z A] [IsSimpleRing A] [FiniteDimensional K A]
    (K' : Type u) [Field K'] [Algebra K K'] [Algebra.IsSeparable K K'] :
    IsSemisimpleRing (K' ⊗[K] A) := by
  haveI : Algebra.FormallyUnramified K K' := Algebra.FormallyUnramified.of_isSeparable K K'
  haveI : IsReduced (Z ⊗[K] K') := isReduced_tensor_separable Z K'
  let e : K' ⊗[K] A ≃+* (Z ⊗[K] K') ⊗[Z] A :=
    (Algebra.TensorProduct.comm K K' A).toRingEquiv.trans
      ((Algebra.TensorProduct.congr ((Algebra.TensorProduct.rid Z Z A).restrictScalars K).symm
        (AlgEquiv.refl : K' ≃ₐ[K] K')).toRingEquiv.trans
      ((Algebra.TensorProduct.assoc (R := K) (S := Z) (A := A) Z Z K').toRingEquiv.trans
        (Algebra.TensorProduct.comm Z A (Z ⊗[K] K')).toRingEquiv))
  have hart : IsArtinianRing (K' ⊗[K] A) := IsArtinianRing.of_finite K' _
  have : IsArtinianRing ((Z ⊗[K] K') ⊗[Z] A) := RingEquiv.isArtinianRing e
  exact e.isSemisimpleRing_iff.mpr (isSemisimpleRing_tensor_of_isCentral (Z ⊗[K] K') A)

theorem isSemisimpleRing_tensor_of_isSimpleRing (A : Type v) [Ring A] [Algebra K A]
    [IsSimpleRing A] [FiniteDimensional K A] (K' : Type u) [Field K'] [Algebra K K']
    [Algebra.IsSeparable K K'] : IsSemisimpleRing (K' ⊗[K] A) := by
  letI : Field (Subalgebra.center K A) := centerField A
  letI : Algebra (Subalgebra.center K A) A :=
    RingHom.toAlgebra' ((Subalgebra.center K A).val : Subalgebra.center K A →+* A)
      (fun c x => (Subalgebra.mem_center_iff.mp c.2 x).symm)
  haveI : IsScalarTower K (Subalgebra.center K A) A := ⟨fun k z a => by
    show ((k • z : Subalgebra.center K A) : A) * a = k • ((z : A) * a)
    simp⟩
  haveI : Algebra.IsCentral (Subalgebra.center K A) A := ⟨fun w hw => by
    rw [Subalgebra.mem_center_iff] at hw
    have hw' : w ∈ Subalgebra.center K A := Subalgebra.mem_center_iff.mpr hw
    rw [Algebra.mem_bot]
    exact ⟨⟨w, hw'⟩, rfl⟩⟩
  exact @isSemisimpleRing_tensor_of_isCentral_over K _ (Subalgebra.center K A) _ _ A _ _ _
    (by assumption) (by assumption) _ _ K' _ _ _

end Simple2

/-- Proposition 5.6 of Milne: if $A$ is a semisimple $K$-algebra and $K'$ is a separable
(algebraic) extension of $K$, then $A \otimes_K K'$ is semisimple.  (Milne's statement writes
$A \otimes_k F$ for $A \otimes_k k'$.) -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 5.6, p. 143"]
theorem prop_5_6 (A : Type v) [Ring A] [Algebra K A] [IsSemisimpleRing A] [FiniteDimensional K A]
    (K' : Type u) [Field K'] [Algebra K K'] [Algebra.IsSeparable K K'] :
    IsSemisimpleRing (K' ⊗[K] A) := by
  obtain ⟨n, D, d, _, _, _, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite K A
  let e' : K' ⊗[K] A ≃+* Π i, K' ⊗[K] Matrix (Fin (d i)) (Fin (d i)) (D i) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K' ≃ₐ[K'] K') e).toRingEquiv.trans
      (Algebra.TensorProduct.piRight K K' K' (fun i => Matrix (Fin (d i)) (Fin (d i)) (D i))).toRingEquiv
  rw [e'.isSemisimpleRing_iff]
  haveI : ∀ i, IsSemisimpleRing (K' ⊗[K] Matrix (Fin (d i)) (Fin (d i)) (D i)) := fun i => by
    haveI := hd i
    exact isSemisimpleRing_tensor_of_isSimpleRing _ K'
  infer_instance

section Quaternion

variable {F : Type u} [Field F]

/-- Exercise 5.7 (f) of Milne: $H(a, b)$ is central simple over $F$ (characteristic $\neq 2$,
$a, b \neq 0$). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(f), p. 144"]
theorem exercise_5_7f (h2 : (2 : F) ≠ 0) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    Algebra.IsCentral F ℍ[F,a,b] ∧ IsSimpleRing ℍ[F,a,b] := by
  constructor
  · refine ⟨fun z hz => ?_⟩
    rw [Subalgebra.mem_center_iff] at hz
    have h1 := hz ⟨0, 1, 0, 0⟩
    have h2' := hz ⟨0, 0, 1, 0⟩
    have e1 := congrArg QuaternionAlgebra.imJ h1
    have e2 := congrArg QuaternionAlgebra.imK h1
    have e3 := congrArg QuaternionAlgebra.imI h2'
    have e4 := congrArg QuaternionAlgebra.imK h2'
    simp at e1 e2 e3 e4
    have hK : z.imK = 0 := by
      have : (2 * a) * z.imK = 0 := by linear_combination e1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero h2 ha)
      · exact h
    have hJ : z.imJ = 0 := by
      have : 2 * z.imJ = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_left h2
    have hI : z.imI = 0 := by
      have : 2 * z.imI = 0 := by linear_combination -e4
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [Algebra.mem_bot]
    refine ⟨z.re, ?_⟩
    ext <;> simp [hK, hJ, hI]
  · by_cases hx : ∃ x : ℍ[F,a,b], x ≠ 0 ∧ QuadFormsKB.Quat.nrd x = 0
    · have hs := (QuadFormsKB.Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 ha hb).2 hx
      obtain ⟨e⟩ := QuadFormsKB.Quat.nonempty_algEquiv_matrix_of_hilbertSymbol h2 ha hb hs
      exact IsSimpleRing.of_ringEquiv e.toRingEquiv.symm inferInstance
    · push Not at hx
      have hu : ∀ x : ℍ[F,a,b], IsUnit x ∨ x = 0 := by
        intro x
        by_cases h0 : x = 0
        · exact Or.inr h0
        · exact Or.inl ((QuadFormsKB.Quat.isUnit_iff_nrd_ne_zero x).2 (hx x h0))
      let : DivisionRing ℍ[F,a,b] := DivisionRing.ofIsUnitOrEqZero hu
      infer_instance

/-- $H(1, b) \cong M_2(F)$ for $b \neq 0$ (used in Exercise 5.7 (a) and (h)). -/
theorem quat_one_matrix (h2 : (2 : F) ≠ 0) {b : F} (hb : b ≠ 0) :
    Nonempty (ℍ[F,1,b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  refine QuadFormsKB.Quat.nonempty_algEquiv_matrix_of_hilbertSymbol h2 one_ne_zero hb ?_
  rw [QuadFormsKB.Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 one_ne_zero hb]
  refine ⟨⟨1, 1, 0, 0⟩, fun h => ?_, ?_⟩
  · have := congrArg QuaternionAlgebra.re h
    simp at this
  · rw [QuadFormsKB.Quat.nrd_mk]; ring

/-- In a central division algebra of dimension `4`, every element outside `F` is quadratic. -/
theorem quad_of_div (A : Type v) [DivisionRing A] [Algebra F A] [Algebra.IsCentral F A]
    [FiniteDimensional F A] (hA : Module.finrank F A = 4) (x : A)
    (hx : x ∉ (algebraMap F A).range) : ∃ c₁ c₀ : F, x * x + c₁ • x + c₀ • (1 : A) = 0 := by
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  set S := Algebra.adjoin F {x} with hS
  have hSle : Module.finrank F S ≤ 4 := by
    rw [← hA]
    exact Submodule.finrank_le (Subalgebra.toSubmodule S)
  have hcomm : ∀ a b : A, a ∈ S → b ∈ S → a * b = b * a := by
    intro a b ha hb
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (a := a) (s := {x}) hb
      (by intro g hg; rw [Set.mem_singleton_iff.mp hg]; exact (Algebra.commute_of_mem_adjoin_self ha).symm))
  have hdle : Module.finrank F S ≤ 2 := by
    by_contra hlt
    push Not at hlt
    by_cases hST : S = ⊤
    · -- A is commutative, contradicting centrality
      have hcen : Subalgebra.center F A = ⊤ := by
        rw [eq_top_iff]
        intro a _
        rw [Subalgebra.mem_center_iff]
        intro b
        have ha : a ∈ S := hST ▸ Algebra.mem_top
        have hb : b ∈ S := hST ▸ Algebra.mem_top
        exact hcomm b a hb ha
      rw [Algebra.IsCentral.center_eq_bot] at hcen
      have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hcen
      omega
    · obtain ⟨w, hw⟩ : ∃ w : A, w ∉ S := by
        by_contra h
        push Not at h
        exact hST (eq_top_iff.mpr fun a _ => h a)
      -- S is closed under inverses
      have hinv : ∀ s : A, s ∈ S → s ≠ 0 → s⁻¹ ∈ S := by
        intro s hs hs0
        let g : S →ₗ[F] S :=
          { toFun := fun t => ⟨s * t, S.mul_mem hs t.2⟩
            map_add' := fun t t' => by ext; simp [mul_add]
            map_smul' := fun r t => by ext; simp }
        have hg : Function.Injective g := by
          intro t t' h
          have := congrArg Subtype.val h
          apply Subtype.ext
          exact mul_left_cancel₀ hs0 this
        obtain ⟨t, ht⟩ := (LinearMap.injective_iff_surjective.mp hg) ⟨1, S.one_mem⟩
        have : s * (t : A) = 1 := congrArg Subtype.val ht
        have : s⁻¹ = (t : A) := by
          exact inv_eq_of_mul_eq_one_right this
        rw [this]; exact t.2
      let f : S × S →ₗ[F] A :=
        (Subalgebra.val S).toLinearMap.coprod
          ((LinearMap.mulRight F w) ∘ₗ (Subalgebra.val S).toLinearMap)
      have hf : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        rintro ⟨s, s'⟩ h
        simp only [f, LinearMap.coprod_apply, AlgHom.toLinearMap_apply, Subalgebra.coe_val,
          LinearMap.comp_apply, LinearMap.mulRight_apply] at h
        by_cases hs' : (s' : A) = 0
        · have : (s : A) = 0 := by simpa [hs'] using h
          exact Prod.ext (Subtype.ext this) (Subtype.ext hs')
        · exfalso
          apply hw
          have hsw : (s' : A) * w = -(s : A) := eq_neg_of_add_eq_zero_right h
          have : w = -((s' : A)⁻¹ * s) := by
            calc w = (s' : A)⁻¹ * ((s' : A) * w) := by
                  rw [← mul_assoc, inv_mul_cancel₀ hs', one_mul]
              _ = -((s' : A)⁻¹ * s) := by rw [hsw, mul_neg]
          rw [this]
          exact S.neg_mem (S.mul_mem (hinv _ s'.2 hs') s.2)
      have := LinearMap.finrank_le_finrank_of_injective hf
      rw [Module.finrank_prod, hA] at this
      omega
  have hmem1 : (1 : A) ∈ S := S.one_mem
  have hmemx : x ∈ S := Algebra.subset_adjoin rfl
  have hmemxx : x * x ∈ S := S.mul_mem hmemx hmemx
  let v : Fin 3 → S := ![⟨1, hmem1⟩, ⟨x, hmemx⟩, ⟨x * x, hmemxx⟩]
  have hnli : ¬ LinearIndependent F v := fun h => by
    have := h.fintype_card_le_finrank
    simp at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hnli
  obtain ⟨g, hg, i, hi⟩ := hnli
  simp only [Fin.sum_univ_three, v] at hg
  have hg' := congrArg Subtype.val hg
  simp at hg'
  by_cases h2' : g 2 = 0
  · exfalso
    rw [h2', zero_smul, add_zero] at hg'
    by_cases h1' : g 1 = 0
    · rw [h1', zero_smul, add_zero] at hg'
      have h0 : g 0 ≠ 0 := by
        fin_cases i <;> simp_all
      have : (1 : A) = 0 := by
        have := congrArg (fun t => (g 0)⁻¹ • t) hg'
        simp [smul_smul, inv_mul_cancel₀ h0] at this
      exact one_ne_zero this
    · apply hx
      refine ⟨-(g 0 / g 1), ?_⟩
      have := congrArg (fun t => (g 1)⁻¹ • t) hg'
      simp only [smul_add, smul_smul, inv_mul_cancel₀ h1', one_smul, smul_zero] at this
      rw [Algebra.algebraMap_eq_smul_one]
      have e : x = -((g 1)⁻¹ * g 0) • (1 : A) := by
        rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
        exact this
      rw [div_eq_inv_mul]
      exact e.symm
  · refine ⟨g 1 / g 2, g 0 / g 2, ?_⟩
    have := congrArg (fun t => (g 2)⁻¹ • t) hg'
    simp only [smul_add, smul_smul, inv_mul_cancel₀ h2', one_smul, smul_zero] at this
    rw [div_eq_inv_mul, div_eq_inv_mul]
    rw [← this]
    abel


/-- A central division algebra of dimension `4` over `F` (characteristic `≠ 2`) is a quaternion
algebra. -/
theorem quat_of_div (h2 : (2 : F) ≠ 0) (A : Type v) [DivisionRing A] [Algebra F A]
    [Algebra.IsCentral F A] [FiniteDimensional F A] (hA : Module.finrank F A = 4) :
    ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (A ≃ₐ[F] ℍ[F,a,b]) := by
  obtain ⟨x, hx⟩ : ∃ x : A, x ∉ (algebraMap F A).range := by
    by_contra h
    push Not at h
    have hbt : (⊥ : Subalgebra F A) = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact h a
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbt
    omega
  obtain ⟨c₁, c₀, hc⟩ := quad_of_div A hA x hx
  set y : A := x + (c₁ / 2) • (1 : A) with hy_def
  have hy : y * y = ((c₁ / 2) ^ 2 - c₀) • (1 : A) := by
    have : y * y = x * x + c₁ • x + (c₁ / 2) ^ 2 • (1 : A) := by
      simp only [hy_def, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
        smul_smul]
      have e : c₁ / 2 * 2 = c₁ := by field_simp
      match_scalars <;> first | ring1 | linear_combination e
    rw [this]
    have hxx : x * x = -(c₁ • x) - c₀ • (1 : A) := by
      rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← hc]; abel
    rw [hxx]
    match_scalars <;> ring
  have hyr : y ∉ (algebraMap F A).range := by
    rintro ⟨r, hr⟩
    apply hx
    refine ⟨r - c₁ / 2, ?_⟩
    rw [map_sub, hr, hy_def, Algebra.algebraMap_eq_smul_one (A := A) (c₁ / 2)]
    abel
  have hy0 : y ≠ 0 := fun h => hyr ⟨0, by rw [h]; simp⟩
  set a : F := (c₁ / 2) ^ 2 - c₀ with ha_def
  have ha : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at hy
    exact hy0 (mul_self_eq_zero.mp hy)
  obtain ⟨w, hw⟩ : ∃ w : A, w * y ≠ y * w := by
    by_contra h
    push Not at h
    apply hyr
    have : y ∈ Subalgebra.center F A := Subalgebra.mem_center_iff.mpr h
    rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at this
    exact this
  set z : A := y * w - w * y with hz_def
  have hz0 : z ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hyz : y * z = -(z * y) := by
    have e1 : y * (y * w) = a • w := by rw [← mul_assoc, hy, smul_mul_assoc, one_mul]
    have e2 : (w * y) * y = a • w := by rw [mul_assoc, hy, mul_smul_comm, mul_one]
    have : y * z + z * y = 0 := by
      simp only [hz_def, mul_sub, sub_mul]
      rw [e1, e2, ← mul_assoc y w y]
      abel
    exact eq_neg_of_add_eq_zero_left this
  have hyzne : y * z ≠ 0 := mul_ne_zero hy0 hz0
  have h2smul : ∀ t : A, (2 : F) • t = 0 → t = 0 := fun t ht => (smul_eq_zero.mp ht).resolve_left h2
  have hzr : z ∉ (algebraMap F A).range := by
    rintro ⟨r, hr⟩
    have hc' : y * z = z * y := by rw [← hr]; exact (Algebra.commutes r y).symm
    apply hyzne
    apply h2smul
    rw [two_smul]
    nth_rewrite 2 [hc']
    rw [hyz]; abel
  obtain ⟨d₁, d₀, hd⟩ := quad_of_div A hA z hzr
  have hzz : z * z = -(d₁ • z) - d₀ • (1 : A) := by
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← hd]; abel
  have hyzz : y * (z * z) = (z * z) * y := by
    calc y * (z * z) = (y * z) * z := by rw [mul_assoc]
      _ = -(z * y) * z := by rw [hyz]
      _ = -(z * (y * z)) := by rw [neg_mul, mul_assoc]
      _ = -(z * -(z * y)) := by rw [hyz]
      _ = (z * z) * y := by rw [mul_neg, neg_neg, mul_assoc]
  have hd1 : d₁ = 0 := by
    have key : (2 * d₁) • (y * z) = 0 := by
      have h3 : y * (z * z) = (z * z) * y := hyzz
      rw [hzz] at h3
      have e1 : y * (-(d₁ • z) - d₀ • (1 : A)) = -(d₁ • (y * z)) - d₀ • y := by
        simp [mul_sub, mul_smul_comm]
      have e2 : (-(d₁ • z) - d₀ • (1 : A)) * y = -(d₁ • (z * y)) - d₀ • y := by
        simp [sub_mul, smul_mul_assoc]
      rw [e1, e2] at h3
      have hzy : z * y = -(y * z) := by rw [hyz, neg_neg]
      rw [hzy, smul_neg, neg_neg] at h3
      have h5 : -(d₁ • (y * z)) = d₁ • (y * z) := sub_left_inj.mp h3
      rw [two_mul, add_smul]
      nth_rewrite 2 [← h5]
      exact add_neg_cancel _
    have : 2 * d₁ = 0 := (smul_eq_zero.mp key).resolve_right hyzne
    exact (mul_eq_zero.mp this).resolve_left h2
  set b : F := -d₀ with hb_def
  have hzb : z * z = b • (1 : A) := by
    rw [hzz, hd1, zero_smul, neg_zero, zero_sub, hb_def, neg_smul]
  have hb : b ≠ 0 := by
    intro h
    rw [h, zero_smul] at hzb
    exact hz0 (mul_self_eq_zero.mp hzb)
  let B : QuaternionAlgebra.Basis A a 0 b :=
    { i := y
      j := z
      k := y * z
      i_mul_i := by rw [hy]; simp
      j_mul_j := hzb
      i_mul_j := rfl
      j_mul_i := by rw [zero_smul, zero_sub, hyz, neg_neg] }
  have hsimple := (exercise_5_7f h2 ha hb).2
  let φ := B.liftHom
  have hinj : Function.Injective φ := RingHom.injective φ.toRingHom
  have hrank : Module.finrank F ℍ[F,a,b] = Module.finrank F A := by
    rw [QuaternionAlgebra.finrank_eq_four, hA]
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := φ.toLinearMap)).mp hinj
  exact ⟨a, b, ha, hb, ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩⟩

theorem quat_of_central_simple (h2 : (2 : F) ≠ 0) (A : Type v) [Ring A] [Algebra F A]
    [Algebra.IsCentral F A] [IsSimpleRing A] [FiniteDimensional F A]
    (hA : Module.finrank F A = 4) :
    ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (A ≃ₐ[F] ℍ[F,a,b]) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  obtain ⟨r, hr, D, _, _, _, ⟨f⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F A
  have hdim : r * r * Module.finrank F D = 4 := by
    have := f.toLinearEquiv.finrank_eq
    rw [hA, Module.finrank_matrix] at this
    simpa using this.symm
  have hDpos : 0 < Module.finrank F D := Module.finrank_pos
  have hr0 : r ≠ 0 := hr.out
  have hr2 : r ≤ 2 := by nlinarith
  rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
  · -- division case
    have hk : Module.finrank F D = 4 := by omega
    let e : A ≃ₐ[F] D := f.trans (BrauerGroup.matOne D)
    have hU : ∀ x : A, IsUnit x ∨ x = 0 := by
      intro x
      by_cases hx : x = 0
      · exact Or.inr hx
      · refine Or.inl ?_
        have : e x ≠ 0 := fun h => hx (e.injective (by rw [h, map_zero]))
        exact (isUnit_map_iff e x).mp (isUnit_iff_ne_zero.mpr this)
    letI : DivisionRing A := DivisionRing.ofIsUnitOrEqZero hU
    exact quat_of_div h2 A hA
  · -- split case
    have hk : Module.finrank F D = 1 := by omega
    have hbt : (⊥ : Subalgebra F D) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hk
    let eD : F ≃ₐ[F] D := AlgEquiv.ofBijective (Algebra.ofId F D)
      ⟨(algebraMap F D).injective, fun d => by
        have : d ∈ (⊥ : Subalgebra F D) := hbt ▸ Algebra.mem_top
        exact Algebra.mem_bot.mp this⟩
    obtain ⟨g⟩ := quat_one_matrix h2 (one_ne_zero (α := F))
    exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨(f.trans eD.symm.mapMatrix).trans g.symm⟩⟩

/-- Exercise 5.7 (a) of Milne: every central simple $F$-algebra of dimension $4$ is isomorphic
to some $H(a, b)$, $a, b \neq 0$ (characteristic $\neq 2$). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(a), p. 144"]
theorem exercise_5_7a (h2 : (2 : F) ≠ 0) (A : Type v) [Ring A] [Algebra F A]
    [Algebra.IsCentral F A] [IsSimpleRing A] [FiniteDimensional F A]
    (hA : Module.finrank F A = 4) :
    ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (A ≃ₐ[F] ℍ[F,a,b]) := by
  obtain ⟨a, b, ha, hb, e⟩ := quat_of_central_simple h2 A hA
  exact ⟨a, b, ha, hb, e⟩

/-- scaled basis -/
def scaleBasis (a b x y : F) : QuaternionAlgebra.Basis ℍ[F,a,b] (a * x ^ 2) 0 (b * y ^ 2) where
  i := ⟨0, x, 0, 0⟩
  j := ⟨0, 0, y, 0⟩
  k := ⟨0, 0, 0, x * y⟩
  i_mul_i := by ext <;> simp <;> ring
  j_mul_j := by ext <;> simp <;> ring
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp <;> ring

def unscaleBasis (a b : F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    QuaternionAlgebra.Basis ℍ[F,a * x ^ 2,b * y ^ 2] a 0 b where
  i := ⟨0, x⁻¹, 0, 0⟩
  j := ⟨0, 0, y⁻¹, 0⟩
  k := ⟨0, 0, 0, x⁻¹ * y⁻¹⟩
  i_mul_i := by ext <;> simp <;> field_simp
  j_mul_j := by ext <;> simp <;> field_simp
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp <;> ring

/-- Exercise 5.7 (d) of Milne: $H(a, b) \cong H(ax^2, by^2)$ for $x, y \in F^\times$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(d), p. 144"]
theorem exercise_5_7d (a b : F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    Nonempty (ℍ[F,a,b] ≃ₐ[F] ℍ[F,a * x ^ 2,b * y ^ 2]) := by
  refine ⟨AlgEquiv.ofAlgHom (QuaternionAlgebra.Basis.liftHom (unscaleBasis a b hx hy))
    (QuaternionAlgebra.Basis.liftHom (scaleBasis a b x y)) ?_ ?_⟩
  · ext <;> simp [QuaternionAlgebra.Basis.lift, scaleBasis, unscaleBasis] <;> field_simp
  · ext <;> simp [QuaternionAlgebra.Basis.lift, scaleBasis, unscaleBasis] <;> field_simp

/-- The quaternion basis of `ℍ[L,a,b]` over `F`. -/
def baseBasis (a b : F) (L : Type v) [Field L] [Algebra F L] :
    QuaternionAlgebra.Basis ℍ[L,algebraMap F L a,algebraMap F L b] a 0 b where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, 0, 1⟩
  i_mul_i := by ext <;> simp [Algebra.algebraMap_eq_smul_one]
  j_mul_j := by ext <;> simp [Algebra.algebraMap_eq_smul_one]
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

/-- The quaternion basis of `L ⊗ ℍ[F,a,b]` over `L`. -/
noncomputable def tensorBasis (a b : F) (L : Type v) [Field L] [Algebra F L] :
    QuaternionAlgebra.Basis (L ⊗[F] ℍ[F,a,b]) (algebraMap F L a) 0 (algebraMap F L b) where
  i := 1 ⊗ₜ ⟨0, 1, 0, 0⟩
  j := 1 ⊗ₜ ⟨0, 0, 1, 0⟩
  k := 1 ⊗ₜ ⟨0, 0, 0, 1⟩
  i_mul_i := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have : (⟨0, 1, 0, 0⟩ * ⟨0, 1, 0, 0⟩ : ℍ[F,a,b]) = a • 1 := by ext <;> simp
    rw [this, zero_smul, add_zero, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def,
      Algebra.algebraMap_eq_smul_one (A := L), smul_assoc, one_smul]
  j_mul_j := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have : (⟨0, 0, 1, 0⟩ * ⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) = b • 1 := by ext <;> simp
    rw [this, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def,
      Algebra.algebraMap_eq_smul_one (A := L), smul_assoc, one_smul]
  i_mul_j := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ext <;> simp
  j_mul_i := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, zero_smul, zero_sub, ← TensorProduct.tmul_neg]
    congr 1
    ext <;> simp

/-- Exercise 5.7 (e) of Milne: $H(a, b) \otimes_F L$ is the quaternion algebra over $L$ defined by
$a, b$ regarded as elements of $L$.  (Written `L ⊗[F] ℍ[F,a,b]`, see `Ch4Tensor.lean`.) -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(e), p. 144"]
theorem exercise_5_7e (a b : F) (L : Type v) [Field L] [Algebra F L] :
    Nonempty (L ⊗[F] ℍ[F,a,b] ≃ₐ[L] ℍ[L,algebraMap F L a,algebraMap F L b]) := by
  refine ⟨AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId L ℍ[L,algebraMap F L a,algebraMap F L b])
      (baseBasis a b L).liftHom (fun l x => (Algebra.commutes l _)))
    (tensorBasis a b L).liftHom ?_ ?_⟩
  · ext <;> simp [QuaternionAlgebra.Basis.lift, tensorBasis, baseBasis]
  · apply Algebra.TensorProduct.ext
    · ext
    · apply QuaternionAlgebra.hom_ext
      · simp [QuaternionAlgebra.Basis.lift, tensorBasis, baseBasis]
      · simp [QuaternionAlgebra.Basis.lift, tensorBasis, baseBasis]

/-- Exercise 5.7 (g) of Milne: $H(a, 1 - a) \cong M_2(F)$ if $a, 1 - a \in F^\times$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(g), p. 144"]
theorem exercise_5_7g (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (ha' : 1 - a ≠ 0) :
    Nonempty (ℍ[F,a,1 - a] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  refine QuadFormsKB.Quat.nonempty_algEquiv_matrix_of_hilbertSymbol h2 ha ha' ?_
  rw [QuadFormsKB.Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 ha ha']
  refine ⟨⟨1, 1, 1, 0⟩, fun h => ?_, ?_⟩
  · have := congrArg QuaternionAlgebra.re h
    simp at this
  · rw [QuadFormsKB.Quat.nrd_mk]; ring

/-- Exercise 5.7 (h) of Milne: $H(1, b) \cong M_2(F)$ and $H(a, -a) \cong M_2(F)$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(h), p. 144"]
theorem exercise_5_7h (h2 : (2 : F) ≠ 0) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (ℍ[F,1,b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) ∧
      Nonempty (ℍ[F,a,-a] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · refine QuadFormsKB.Quat.nonempty_algEquiv_matrix_of_hilbertSymbol h2 one_ne_zero hb ?_
    rw [QuadFormsKB.Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 one_ne_zero hb]
    refine ⟨⟨1, 1, 0, 0⟩, fun h => ?_, ?_⟩
    · have := congrArg QuaternionAlgebra.re h
      simp at this
    · rw [QuadFormsKB.Quat.nrd_mk]; ring
  · have ha' : -a ≠ 0 := neg_ne_zero.2 ha
    refine QuadFormsKB.Quat.nonempty_algEquiv_matrix_of_hilbertSymbol h2 ha ha' ?_
    rw [QuadFormsKB.Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 ha ha']
    refine ⟨⟨0, 1, 1, 0⟩, fun h => ?_, ?_⟩
    · have := congrArg QuaternionAlgebra.imI h
      simp at this
    · rw [QuadFormsKB.Quat.nrd_mk]; ring

/-- Exercise 5.7 (i) of Milne: $H(a, b) \cong H(a, b)^{\mathrm{opp}}$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(i), p. 144"]
theorem exercise_5_7i (a b : F) : Nonempty (ℍ[F,a,b] ≃ₐ[F] ℍ[F,a,b]ᵐᵒᵖ) := by
  exact ⟨QuaternionAlgebra.starAe⟩

/-- $H(a, b)$ as an element of `CSA F` (characteristic $\neq 2$, $a, b \neq 0$). -/
noncomputable def quaternionCSA (h2 : (2 : F) ≠ 0) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    CSA.{u, u} F :=
  haveI := (exercise_5_7f h2 ha hb).1
  haveI := (exercise_5_7f h2 ha hb).2
  { toAlgCat := AlgCat.of F ℍ[F,a,b] }

/-- The swap isomorphism basis: `ℍ[F,b,a]` carries a quaternion basis for `(a, 0, b)`. -/
def swapBasis (a b : F) : QuaternionAlgebra.Basis ℍ[F,b,a] a 0 b where
  i := ⟨0, 0, 1, 0⟩
  j := ⟨0, 1, 0, 0⟩
  k := ⟨0, 0, 0, -1⟩
  i_mul_i := by ext <;> simp
  j_mul_j := by ext <;> simp
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

/-- $H(a, b) \cong H(b, a)$ (swap $i$ and $j$). -/
theorem nonempty_quat_swap (a b : F) : Nonempty (ℍ[F,a,b] ≃ₐ[F] ℍ[F,b,a]) := by
  refine ⟨AlgEquiv.ofAlgHom (swapBasis a b).liftHom (swapBasis b a).liftHom ?_ ?_⟩
  · ext <;> simp [QuaternionAlgebra.Basis.lift, swapBasis]
  · ext <;> simp [QuaternionAlgebra.Basis.lift, swapBasis]

theorem commute_liftHom {A : Type*} [Ring A] [Algebra F A] {c₁ c₂ c₃ d₁ d₂ d₃ : F}
    (q : QuaternionAlgebra.Basis A c₁ c₂ c₃) (q' : QuaternionAlgebra.Basis A d₁ d₂ d₃)
    (hii : Commute q.i q'.i) (hij : Commute q.i q'.j) (hik : Commute q.i q'.k)
    (hji : Commute q.j q'.i) (hjj : Commute q.j q'.j) (hjk : Commute q.j q'.k)
    (hki : Commute q.k q'.i) (hkj : Commute q.k q'.j) (hkk : Commute q.k q'.k)
    (x : ℍ[F,c₁,c₂,c₃]) (y : ℍ[F,d₁,d₂,d₃]) : Commute (q.liftHom x) (q'.liftHom y) := by
  simp only [QuaternionAlgebra.Basis.liftHom_apply]
  have key : ∀ z : A, Commute z q'.i → Commute z q'.j → Commute z q'.k →
      Commute z (q'.lift y) := by
    intro z h1 h2 h3
    unfold QuaternionAlgebra.Basis.lift
    exact (((Algebra.commute_algebraMap_right _ z).add_right (h1.smul_right _)).add_right
      (h2.smul_right _)).add_right (h3.smul_right _)
  unfold QuaternionAlgebra.Basis.lift
  exact (((Algebra.commute_algebraMap_left _ _).add_left
    ((key _ hii hij hik).smul_left _)).add_left ((key _ hji hjj hjk).smul_left _)).add_left
    ((key _ hki hkj hkk).smul_left _)

theorem tmul_eq_of_neg {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]
    {p p' : M} {q q' : N} (h1 : p = -p') (h2 : q = -q') :
    p ⊗ₜ[F] q = p' ⊗ₜ[F] q' := by
  subst h1 h2
  rw [TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]

/-- The copy of $H(aa', b)$ inside $H(a, b) \otimes H(a', b)$. -/
noncomputable def prodBasisB (a a' b : F) :
    QuaternionAlgebra.Basis (ℍ[F,a,b] ⊗[F] ℍ[F,a',b]) (a * a') 0 b where
  i := (⟨0, 1, 0, 0⟩ : ℍ[F,a,b]) ⊗ₜ (⟨0, 1, 0, 0⟩ : ℍ[F,a',b])
  j := (⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) ⊗ₜ 1
  k := (⟨0, 0, 0, 1⟩ : ℍ[F,a,b]) ⊗ₜ (⟨0, 1, 0, 0⟩ : ℍ[F,a',b])
  i_mul_i := by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    have h1 : (⟨0, 1, 0, 0⟩ * ⟨0, 1, 0, 0⟩ : ℍ[F,a,b]) = a • 1 := by ext <;> simp
    have h2 : (⟨0, 1, 0, 0⟩ * ⟨0, 1, 0, 0⟩ : ℍ[F,a',b]) = a' • 1 := by ext <;> simp
    rw [h1, h2, zero_smul, add_zero, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      smul_smul, Algebra.TensorProduct.one_def, mul_comm a' a, TensorProduct.smul_tmul']
  j_mul_j := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have h1 : (⟨0, 0, 1, 0⟩ * ⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) = b • 1 := by ext <;> simp
    rw [h1, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  i_mul_j := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    ext <;> simp
  j_mul_i := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, zero_smul, zero_sub, ← TensorProduct.neg_tmul]
    congr 1
    ext <;> simp

/-- The copy of $H(b^2, a')$ inside $H(a, b) \otimes H(a', b)$. -/
noncomputable def prodBasisC (a a' b : F) :
    QuaternionAlgebra.Basis (ℍ[F,a,b] ⊗[F] ℍ[F,a',b]) (1 * b ^ 2) 0 (a' * 1 ^ 2) where
  i := (⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) ⊗ₜ (⟨0, 0, 1, 0⟩ : ℍ[F,a',b])
  j := (1 : ℍ[F,a,b]) ⊗ₜ (⟨0, 1, 0, 0⟩ : ℍ[F,a',b])
  k := (⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) ⊗ₜ (⟨0, 0, 0, -1⟩ : ℍ[F,a',b])
  i_mul_i := by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    have h1 : (⟨0, 0, 1, 0⟩ * ⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) = b • 1 := by ext <;> simp
    have h2 : (⟨0, 0, 1, 0⟩ * ⟨0, 0, 1, 0⟩ : ℍ[F,a',b]) = b • 1 := by ext <;> simp
    rw [h1, h2, zero_smul, add_zero, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      smul_smul, Algebra.TensorProduct.one_def]
    congr 1
    simp only [one_mul]
    rw [sq]
  j_mul_j := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have h1 : (⟨0, 1, 0, 0⟩ * ⟨0, 1, 0, 0⟩ : ℍ[F,a',b]) = a' • 1 := by ext <;> simp
    rw [h1, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def]
    simp
  i_mul_j := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    ext <;> simp
  j_mul_i := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, zero_smul, zero_sub,
      ← TensorProduct.tmul_neg]
    congr 1
    ext <;> simp

theorem prodBasis_commute (a a' b : F) (x : ℍ[F,a * a',0,b]) (y : ℍ[F,1 * b ^ 2,0,a' * 1 ^ 2]) :
    Commute ((prodBasisB a a' b).liftHom x) ((prodBasisC a a' b).liftHom y) := by
  refine commute_liftHom _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ x y <;>
  · unfold Commute SemiconjBy
    simp only [prodBasisB, prodBasisC, Algebra.TensorProduct.tmul_mul_tmul]
    first
      | (congr 1 <;> (ext <;> simp); done)
      | (apply tmul_eq_of_neg <;> (ext <;> simp); done)

theorem nonempty_algEquiv_prod (h2 : (2 : F) ≠ 0) {a a' b : F} (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hb : b ≠ 0) :
    Nonempty (ℍ[F,a * a',b] ⊗[F] ℍ[F,1 * b ^ 2,a' * 1 ^ 2] ≃ₐ[F] ℍ[F,a,b] ⊗[F] ℍ[F,a',b]) := by
  have hB := exercise_5_7f h2 (mul_ne_zero ha ha') hb
  have hb2 : (1 * b ^ 2 : F) ≠ 0 := by simpa using hb
  have ha1 : (a' * 1 ^ 2 : F) ≠ 0 := by simpa using ha'
  have hC := exercise_5_7f h2 hb2 ha1
  have hA := exercise_5_7f h2 ha hb
  have hA' := exercise_5_7f h2 ha' hb
  haveI := hB.1
  haveI := hB.2
  haveI := hC.1
  haveI := hC.2
  haveI := hA.1
  haveI := hA.2
  haveI := hA'.1
  haveI := hA'.2
  let Φ := Algebra.TensorProduct.lift (prodBasisB a a' b).liftHom (prodBasisC a a' b).liftHom
    (fun x y => prodBasis_commute a a' b x y)
  have hinj : Function.Injective Φ := RingHom.injective Φ.toRingHom
  have hrank : Module.finrank F (ℍ[F,a * a',b] ⊗[F] ℍ[F,1 * b ^ 2,a' * 1 ^ 2]) =
      Module.finrank F (ℍ[F,a,b] ⊗[F] ℍ[F,a',b]) := by
    rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct]
    simp only [QuaternionAlgebra.finrank_eq_four]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := Φ.toLinearMap)).1 hinj
  exact ⟨AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩

theorem brauer_quat_mul_left (h2 : (2 : F) ≠ 0) {a a' b : F} (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hb : b ≠ 0) :
    BrauerGroup.mk (quaternionCSA h2 (mul_ne_zero ha ha') hb) =
      BrauerGroup.mk (quaternionCSA h2 ha hb) * BrauerGroup.mk (quaternionCSA h2 ha' hb) := by
  have hb2 : (1 * b ^ 2 : F) ≠ 0 := by simpa using hb
  have ha1 : (a' * 1 ^ 2 : F) ≠ 0 := by simpa using ha'
  have hC : BrauerGroup.mk (quaternionCSA h2 hb2 ha1) = 1 := by
    rw [BrauerGroup.mk_eq_one_iff]
    obtain ⟨e1⟩ := exercise_5_7d (1 : F) a' (x := b) (y := 1) hb one_ne_zero
    obtain ⟨e2, -⟩ := exercise_5_7h h2 (one_ne_zero (α := F)) ha'
    exact ⟨2, two_ne_zero, ⟨e1.symm.trans e2.some⟩⟩
  obtain ⟨e⟩ := nonempty_algEquiv_prod h2 ha ha' hb
  calc BrauerGroup.mk (quaternionCSA h2 (mul_ne_zero ha ha') hb)
      = BrauerGroup.mk (quaternionCSA h2 (mul_ne_zero ha ha') hb) *
        BrauerGroup.mk (quaternionCSA h2 hb2 ha1) := by rw [hC, mul_one]
    _ = BrauerGroup.mk (CSA.tensor (quaternionCSA h2 (mul_ne_zero ha ha') hb)
          (quaternionCSA h2 hb2 ha1)) := BrauerGroup.mk_mul_mk _ _
    _ = BrauerGroup.mk (CSA.tensor (quaternionCSA h2 ha hb) (quaternionCSA h2 ha' hb)) :=
        (BrauerGroup.mk_eq_mk_iff _ _).2 (isBrauerEquivalent_of_algEquiv e)
    _ = _ := (BrauerGroup.mk_mul_mk _ _).symm

/-- Exercise 5.7 (k) of Milne: the map $\{a, b\} \mapsto [H(a, b)]$, $K_2 F \to \mathrm{Br}(F)$, is
well defined: $[H(a, b)]$ is multiplicative in each variable and $[H(u, 1 - u)] = 1$ (the defining
relations of Milnor's $K_2 F$, recalled by Milne before the exercise). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 5.7(k), p. 145"]
theorem exercise_5_7k (h2 : (2 : F) ≠ 0) :
    (∀ (a a' b : F) (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0),
        BrauerGroup.mk (quaternionCSA h2 (mul_ne_zero ha ha') hb) =
          BrauerGroup.mk (quaternionCSA h2 ha hb) * BrauerGroup.mk (quaternionCSA h2 ha' hb)) ∧
      (∀ (a b b' : F) (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0),
        BrauerGroup.mk (quaternionCSA h2 ha (mul_ne_zero hb hb')) =
          BrauerGroup.mk (quaternionCSA h2 ha hb) * BrauerGroup.mk (quaternionCSA h2 ha hb')) ∧
      ∀ (u : F) (hu : u ≠ 0) (hu' : 1 - u ≠ 0),
        BrauerGroup.mk (quaternionCSA h2 hu hu') = 1 := by
  have swap : ∀ {a b : F} (ha : a ≠ 0) (hb : b ≠ 0),
      BrauerGroup.mk (quaternionCSA h2 ha hb) = BrauerGroup.mk (quaternionCSA h2 hb ha) :=
    fun ha hb => (BrauerGroup.mk_eq_mk_iff _ _).2
      (isBrauerEquivalent_of_algEquiv (nonempty_quat_swap _ _).some)
  refine ⟨fun a a' b ha ha' hb => brauer_quat_mul_left h2 ha ha' hb, ?_, ?_⟩
  · intro a b b' ha hb hb'
    rw [swap ha (mul_ne_zero hb hb'), brauer_quat_mul_left h2 hb hb' ha, ← swap ha hb,
      ← swap ha hb']
  · intro u hu hu'
    rw [BrauerGroup.mk_eq_one_iff]
    exact ⟨2, two_ne_zero, exercise_5_7g h2 hu hu'⟩

end Quaternion

end NumberFieldKB.MilneCFT.Ch4
