import Mathlib.Computability.Reduce
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import QuadFormsKB.Citation
import NumberFieldKB.TauCetiPort.Algebra.CrossedProduct.Comparison
import NumberFieldKB.TauCetiPort.Algebra.CrossedProduct.CentralSimple
import NumberFieldKB.TauCetiPort.Algebra.CrossedProduct.Cohomology
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.CentralSimple.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.Invariant
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.Unramified

/-!
# Milne, Class Field Theory, Chapter IV, §4: the invariant of a cyclic division algebra

Let `D` be a central division algebra of degree `d²` over a nonarchimedean local field `K`, let `L ⊆ D` be a
`K`-subfield, unramified of degree `d` (Milne, *CFT* v4.03, Ch. IV, §4, p. 140), and let `α ∈ Dˣ` induce the
Frobenius of `L/K` by conjugation, `α x α⁻¹ = σ(x)`. Then `α^d = a ∈ Kˣ`, `D` is the cyclic algebra
`(L/K, σ, a)`, and the invariant of `D` is `ord_K(a) / d = ord(α) / d`.

The proof builds the crossed-product isomorphism `(L, Gal(L/K), z_a) ≅ D` from `CrossedProduct.lift`, where `z_a` is
Tau Ceti's carry cocycle of `a`, and then compares the cohomology class of `z_a` (`relBrInfl_H2π`) with the
unramified class of `a` (`unramifiedClass`), whose invariant is `v_K(a)/d` (`unramifiedInv_unramifiedClass`).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch4

open TauCeti ClassFieldTheory groupCohomology

section Algebra

variable {K L D : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

/-- **A cyclic algebra is a crossed product.** Let `g` generate `Gal(L/K)`, let `z` be a `2`-cocycle with the carry
values `a` (for `i + j ≥ n`) and `1` (otherwise) at `(gⁱ, gʲ)`, and let `ι : L → D`, `α ∈ Dˣ` satisfy
`ι(g x) = α ι(x) α⁻¹` and `α^n = a`. If `dim_K D = [L:K]²`, then `D` is the crossed product `(L, Gal(L/K), z)`. -/
theorem nonempty_crossedProduct_algEquiv (g : L ≃ₐ[K] L) (hg : ∀ σ : L ≃ₐ[K] L, σ ∈ Subgroup.zpowers g)
    (z : TwoCocycle K L) (a : Kˣ)
    (hz : ∀ i j, i < orderOf g → j < orderOf g →
      (z.toFun (g ^ i) (g ^ j) : L) = if orderOf g ≤ i + j then algebraMap K L a else 1)
    (hdim : Module.finrank K D = Module.finrank K L ^ 2)
    (ι : L →ₐ[K] D) (α : Dˣ) (hα : ∀ x : L, ι (g x) = α * ι x * ↑α⁻¹)
    (ha : (α : D) ^ orderOf g = algebraMap K D a) :
    Nonempty (CrossedProduct z ≃ₐ[K] D) := by
  classical
  have hn : 0 < orderOf g := orderOf_pos g
  have hex : ∀ σ : L ≃ₐ[K] L, ∃ i, i < orderOf g ∧ g ^ i = σ := fun σ ↦ by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg σ)
    refine ⟨(k % orderOf g).toNat, ?_, ?_⟩
    · have := Int.emod_lt_of_pos k (Int.natCast_pos.2 hn)
      have := Int.emod_nonneg k (Int.natCast_pos.2 hn).ne'
      omega
    · rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (Int.natCast_pos.2 hn).ne'),
        zpow_mod_orderOf]
  let idx : (L ≃ₐ[K] L) → ℕ := fun σ ↦ (hex σ).choose
  have idx_pow : ∀ i, i < orderOf g → idx (g ^ i) = i := fun i hi ↦ by
    have h := (hex (g ^ i)).choose_spec
    exact pow_injOn_Iio_orderOf (by simpa using h.1) (by simpa using hi) h.2
  let u : (L ≃ₐ[K] L) → D := fun σ ↦ ((α ^ idx σ : Dˣ) : D)
  have hu_pow : ∀ i, i < orderOf g → u (g ^ i) = (α : D) ^ i := fun i hi ↦ by
    simp [u, idx_pow i hi]
  have hconj : ∀ (i : ℕ) (x : L), ι ((g ^ i) x) = ((α ^ i : Dˣ) : D) * ι x * ((α ^ i)⁻¹ : Dˣ) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ', AlgEquiv.mul_apply, hα, ih, pow_succ', mul_inv_rev]
      simp only [Units.val_mul, mul_assoc]
  have hf : ∀ σ x, u σ * ι x = ι (σ x) * u σ := fun σ x ↦ by
    obtain ⟨i, hi, rfl⟩ := hex σ
    rw [hu_pow i hi, hconj]
    simp only [mul_assoc, Units.val_pow_eq_pow_val]
    have : ((α ^ i)⁻¹ : Dˣ) * (α : D) ^ i = 1 := by simp
    rw [this]
    simp
  have hu : ∀ σ τ, u σ * u τ = ι (z.toFun σ τ) * u (σ * τ) := fun σ τ ↦ by
    obtain ⟨i, hi, rfl⟩ := hex σ
    obtain ⟨j, hj, rfl⟩ := hex τ
    rw [hu_pow i hi, hu_pow j hj, ← pow_add, hz i j hi hj]
    by_cases hij : orderOf g ≤ i + j
    · have hlt : i + j - orderOf g < orderOf g := by
        have : i < orderOf g := hi
        omega
      have : g ^ i * g ^ j = g ^ (i + j - orderOf g) := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
        rw [← pow_add, hk, pow_add, pow_orderOf_eq_one, one_mul]
        congr 1
        omega
      rw [this, hu_pow _ hlt]
      simp only [hij, ↓reduceIte]
      rw [AlgHom.commutes, ← ha, ← pow_add]
      congr 1
      omega
    · simp only [hij, ↓reduceIte]
      rw [map_one, one_mul, ← pow_add, hu_pow _ (by omega)]
  have hu₁ : u 1 = ι (z.toFun 1 1) := by
    have h := hz 0 0 hn hn
    simp only [pow_zero] at h
    rw [h]
    simp only [show ¬ orderOf g ≤ 0 + 0 by omega, ↓reduceIte, map_one]
    simpa using hu_pow 0 hn
  let F := CrossedProduct.lift ι u hf hu hu₁
  have hinj : Function.Injective F := RingHom.injective (F : CrossedProduct z →+* D)
  have hfin : Module.finrank K (CrossedProduct z) = Module.finrank K D := by
    rw [CrossedProduct.finrank_eq_finrank_sq, hdim]
  exact ⟨AlgEquiv.ofBijective F
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (F : CrossedProduct z →ₗ[K] D)) hfin).1 hinj⟩⟩

end Algebra

section Invariant

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The invariant of a cyclic division algebra** (Milne, *CFT*, IV, §4, p. 140). Let `D` be a central division
algebra of degree `d²` over a local field `K`, `L ⊆ Kˢ` the unramified extension of degree `d` with a `K`-embedding
`ι : L → D`, and `α ∈ Dˣ` an element inducing the Frobenius of `L/K` on `ι(L)` by conjugation. Then
`α^d = a ∈ Kˣ` is a scalar (hypothesis `ha`), `D ≅ (L/K, σ, a)` is the cyclic algebra, and the invariant of `D` is
`ord_K(a) / d`. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §4, the invariant of a cyclic division algebra, p. 140"]
theorem invMap_brauerGroupEquivBr_of_conj
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    [IsUnramified K L]
    (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D]
    {d : ℕ} (hL : Module.finrank K L = d) (hD : Module.finrank K D = d ^ 2)
    (ι : L →ₐ[K] D) (α : Dˣ)
    (hα : ∀ x : L, ι (TauCeti.frobeniusAlgEquiv (K := K) (L := L) x) = α * ι x * ↑α⁻¹)
    (a : Kˣ) (ha : (α : D) ^ d = algebraMap K D a) :
    TauCeti.ClassFieldTheory.invMap K (TauCeti.ClassFieldTheory.brauerGroupEquivBr K
        (Additive.ofMul (BrauerGroup.mk (CSA.of K D)))) =
      (((TauCeti.normalizedValuation K a).toAdd / d : ℚ) : AddCircle (1 : ℚ)) := by
  classical
  set g := TauCeti.frobeniusAlgEquiv (K := K) (L := L) with hgdef
  have hg : ∀ σ : L ≃ₐ[K] L, σ ∈ Subgroup.zpowers g := fun σ ↦ by
    rw [hgdef, zpowers_frobeniusAlgEquiv]
    exact Subgroup.mem_top σ
  have hord : orderOf g = d := by
    rw [hgdef, orderOf_frobeniusAlgEquiv, IsUnramified.inertiaDegree_eq_finrank, hL]
  obtain ⟨zM, hzM, hval⟩ := exists_H2π_eq_cyclicClass hg a
  let z : TwoCocycle K L :=
    ⟨fun σ τ ↦ Additive.toMul (zM (σ, τ)), isMulCocycle₂_of_mem_cocycles₂ _ zM.2⟩
  have hzc : z.toCocycles₂ = zM := cocycles₂_ext fun _ _ ↦ rfl
  obtain ⟨e⟩ := nonempty_crossedProduct_algEquiv g hg z a
    (fun i j hi hj ↦ by
      have h : ((z.toFun (g ^ i) (g ^ j) : Lˣ) : L) = _ := congrArg Units.val (hval i j hi hj)
      split_ifs at h ⊢ <;> simpa using h)
    (by rw [hL, hD]) ι α hα (by rw [hord]; exact ha)
  have hmk : BrauerGroup.mk (CSA.of K D) = BrauerGroup.crossedProductClass z :=
    (BrauerGroup.mk_eq_mk_of_algEquiv (A := BrauerGroup.crossedProductCSA z) (B := CSA.of K D) e).symm
  have hcoc : relBrCocycle K L L.val zM = z.inflateZ2 L := by
    refine Subtype.ext (funext fun p ↦ ?_)
    rw [relBrCocycle_apply]
    rfl
  have key : brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.mk (CSA.of K D))) =
      relBrInfl K L L.val (cyclicClass hg (Additive.ofMul a)) := by
    rw [hmk, brauerGroupEquivBr_apply, brauerExplicitH2Equiv_crossedProductClass, ← hzM,
      relBrInfl_H2π, hcoc]
    rfl
  rw [key, invMap_relBrInfl, ← unramifiedClass_eq_cyclicClass K L hg, unramifiedInv_unramifiedClass, hL]

end Invariant

end NumberFieldKB.MilneCFT.Ch4
