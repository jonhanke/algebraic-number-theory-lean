import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4PeriodIndex
import NumberFieldKB.MilneCFT.Ch4OrdD
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Norm.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.ResidueCorrespondence
import NumberFieldKB.TauCetiPort.FieldTheory.GaloisCohomology.Cyclic

/-!
# Milne, Class Field Theory, Chapter IV, §4: a central division algebra over a local field has an invariant

For a central division algebra `D` of degree `d²` over a nonarchimedean local field `K` (in `Type`), the unramified
extension `L₀` of `K` of degree `d` (Tau Ceti's `unramifiedExtension`) splits `D`, because the order of `[D]` divides
`d` (Cor. 3.17) and Tau Ceti's local invariant shows that a field of degree divisible by the order kills the class
(`brBaseChange_eq_zero_of_dvd_finrank`). By Cor. 3.7, `L₀` embeds in `D` (`exists_unramified_algHom`). Its image is
a maximal subfield unramified over `K`, the Frobenius of `L₀` is an inner automorphism (Skolem–Noether), and
`ord(α)` of a conjugating element is a local invariant in Milne's sense (p. 140).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch4

open TauCeti ClassFieldTheory


section Embedding

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The unramified extension of degree `f` of `K` inside `SeparableClosure K`. -/
noncomputable abbrev unramL (f : ℕ) : IntermediateField K (SeparableClosure K) :=
  unramifiedExtension K (SeparableClosure K) f

set_option synthInstance.maxHeartbeats 400000 in
/-- **The unramified extension of degree `d` embeds in a central division algebra of degree `d²`** over a
nonarchimedean local field (Milne, *CFT*, IV, §4, p. 140: "D contains a maximal subfield unramified over K"). -/
theorem exists_unramified_algHom (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] {d : ℕ} (hd : Module.finrank K D = d ^ 2) :
    Nonempty (unramL K d →ₐ[K] D) := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    have := Module.finrank_pos (R := K) (M := D)
    rw [hd] at this
    simp at this
  let _ := algebraicExtensionValuativeRel K (unramL K d)
  let _ := algebraicExtensionNormedFieldTopology K (unramL K d)
  have := finiteExtension_isNonarchimedeanLocalField K (unramL K d)
  have := algebraicExtension_valuativeExtension K (unramL K d)
  have hfr : Module.finrank K (unramL K d) = d := finrank_unramifiedExtension hd0
  have hexp : BrauerGroup.mk (CSA.of K D) ^ d = 1 :=
    (exponentDividesDegree K).pow_deg_eq_one (CSA.of K D) d hd
  have hx : d • brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.mk (CSA.of K D))) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, hexp, ofMul_one, map_zero]
  have hbc := brBaseChange_eq_zero_of_dvd_finrank K (unramL K d) hfr.symm.dvd _ hx
  have hker : BrauerGroup.baseChange K (unramL K d) (BrauerGroup.mk (CSA.of K D)) = 1 := by
    have e := BrauerBaseChange.brauerGroupEquivBr_baseChange K (unramL K d) (BrauerGroup.mk (CSA.of K D))
    rw [hbc] at e
    have := (brauerGroupEquivBr (unramL K d)).injective (e.trans (map_zero _).symm)
    exact Additive.ofMul.injective this
  have hsplit : IsSplitBy (K := K) (unramL K d) (CSA.of K D) :=
    (mk_mem_relBrauer_iff (K := K) (L := unramL K d) (CSA.of K D)).1
      (by rw [relBrauer, MonoidHom.mem_ker]; exact hker)
  exact (cor_3_7 D (unramL K d) hd hfr).1 hsplit

end Embedding

section CyclicPower

variable {K : Type} [Field K]

/-- Iterating a conjugation: if `ι (g x) = α ι(x) α⁻¹` then `ι (gᵏ x) = αᵏ ι(x) α⁻ᵏ`. -/
theorem conj_pow {L D : Type} [Field L] [Algebra K L] [Ring D] [Algebra K D] (ι : L →ₐ[K] D)
    (g : L ≃ₐ[K] L) (α : Dˣ) (hα : ∀ x, ι (g x) = α * ι x * ↑α⁻¹) (k : ℕ) (x : L) :
    ι ((g ^ k) x) = ↑(α ^ k) * ι x * ↑(α ^ k)⁻¹ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, hα, ih, pow_succ', mul_inv_rev]
    simp only [Units.val_mul]
    noncomm_ring

/-- **The `d`-th power of a conjugating element is central** (Milne, *CFT*, IV, §4, p. 140, in the description of
`D` as the cyclic algebra `(L/K, σ, α^d)`): let `L` be a maximal subfield of a central simple `D`
(`[D : K] = [L : K]²`), `g` a generator of `Gal(L/K)` of order `d = [L : K]` and `α` with
`ι(g x) = α ι(x) α⁻¹`. Then `αᵈ ∈ Kˣ`. -/
theorem exists_pow_eq_algebraMap {L D : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Ring D] [Algebra K D] [Algebra.IsCentral K D] [IsSimpleRing D] [FiniteDimensional K D] {d : ℕ}
    (hL : Module.finrank K L = d) (hD : Module.finrank K D = d ^ 2) (ι : L →ₐ[K] D)
    (g : L ≃ₐ[K] L) (hg : ∀ σ : L ≃ₐ[K] L, σ ∈ Subgroup.zpowers g) (hgd : g ^ d = 1)
    (α : Dˣ) (hα : ∀ x, ι (g x) = α * ι x * ↑α⁻¹) :
    ∃ a : Kˣ, ((α ^ d : Dˣ) : D) = algebraMap K D a := by
  have hd0 : 0 < d := by
    rw [← hL]
    exact Module.finrank_pos
  have hinj : Function.Injective ι := ι.toRingHom.injective
  let B : Subalgebra K D := ι.range
  let e : L ≃ₐ[K] B := AlgEquiv.ofInjective ι hinj
  have hBfield : IsField B := e.symm.toMulEquiv.isField (Field.toIsField L)
  let _ : Field B := hBfield.toField
  have hBsimple : IsSimpleRing B := inferInstance
  have hBdim : Module.finrank K B = d := by rw [← e.toLinearEquiv.finrank_eq, hL]
  obtain ⟨-, -, hdim⟩ := thm_3_1 D B
  set C := Subalgebra.centralizer K (B : Set D)
  have hCdim : Module.finrank K C = d := by
    rw [hBdim, hD, pow_two] at hdim
    exact Nat.eq_of_mul_eq_mul_left hd0 hdim
  have hBC : B ≤ C := by
    intro x hx y hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    rw [← map_mul, ← map_mul, mul_comm]
  have hCB : C = B := (Subalgebra.eq_of_le_of_finrank_eq hBC (by rw [hBdim, hCdim])).symm
  -- `αᵈ` centralizes `B`
  have hmem : ((α ^ d : Dˣ) : D) ∈ C := by
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    have h1 := conj_pow ι g α hα d u
    rw [hgd, AlgEquiv.one_apply] at h1
    calc ι u * ↑(α ^ d) = ↑(α ^ d) * ι u * ↑(α ^ d)⁻¹ * ↑(α ^ d) := by rw [← h1]
      _ = ↑(α ^ d) * ι u := by rw [mul_assoc, Units.inv_mul, mul_one]
  rw [hCB] at hmem
  obtain ⟨b, hb'⟩ := hmem
  have hb : ι b = ↑(α ^ d) := hb'
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact (α ^ d).ne_zero hb.symm
  -- `b` is fixed by `g`
  have hgb : g b = b := by
    apply hinj
    rw [hα, hb]
    have : ↑α * ↑(α ^ d) * ↑α⁻¹ = ((α * α ^ d * α⁻¹ : Dˣ) : D) := by simp
    rw [this, ← pow_succ', pow_succ, mul_inv_cancel_right]
  let bu : Lˣ := Units.mk0 b hb0
  obtain ⟨a, ha⟩ := TauCeti.exists_unitsMap_eq_of_smul_eq hg (x := bu)
    (Units.ext (by simpa [bu] using hgb))
  refine ⟨a, ?_⟩
  have hab : algebraMap K L a = b := by
    have := congrArg Units.val ha
    simpa [bu] using this
  rw [← hb, ← hab, ι.commutes]

end CyclicPower


section Invariant

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- On an unramified subfield `ι(L₀)` of a central simple `D` of degree `d²`, `[L₀ : K] = d`, Milne's `ord` is the
normalized valuation of `L₀`: `ord(ι y) = ord_K(N y)/d = f·v(y)/d = v(y)`. -/
theorem ordD_algHom_eq {L₀ D : Type} [Field L₀] [ValuativeRel L₀] [TopologicalSpace L₀]
    [IsNonarchimedeanLocalField L₀] [Algebra K L₀] [ValuativeExtension K L₀] [FiniteDimensional K L₀]
    [IsUnramified K L₀] [DivisionRing D] [Algebra K D] [FiniteDimensional K D] {d : ℕ}
    (hL : Module.finrank K L₀ = d) (ι : L₀ →ₐ[K] D) (y : L₀) (hy : y ≠ 0) :
    ordD K D (ι y) = ((normalizedValuation L₀ (Units.mk0 y hy)).toAdd : ℚ) := by
  have hd0 : (d : ℚ) ≠ 0 := by
    rw [← hL]
    exact_mod_cast (Module.finrank_pos (R := K) (M := L₀)).ne'
  let e : L₀ ≃ₐ[K] ι.range := AlgEquiv.ofInjective ι ι.toRingHom.injective
  have hB : IsField ι.range := e.symm.toMulEquiv.isField (Field.toIsField L₀)
  have h1 := ordD_eq (K := K) (D := D) (E := ι.range) hB (e y)
  have hey : ((e y : ι.range) : D) = ι y := rfl
  rw [hey] at h1
  rw [h1, Algebra.norm_eq_of_algEquiv, ← e.toLinearEquiv.finrank_eq, hL]
  have hN : Algebra.norm K y ≠ 0 := (Algebra.norm_ne_zero_iff).2 hy
  rw [ordK_eq_toAdd hN]
  have h2 := toAdd_normalizedValuation_norm (K := K) (Units.mk0 y hy)
  have h3 : Units.mk0 (Algebra.norm K y) hN = Algebra.normUnits K (Units.mk0 y hy) :=
    Units.ext (by rw [Algebra.coe_normUnits]; rfl)
  rw [h3, h2, IsUnramified.inertiaDegree_eq_finrank, hL]
  push_cast
  field_simp

/-- A local invariant from an embedded unramified field: if `ι : L₀ → D` embeds an unramified extension of degree
`d` into a central simple `D` of degree `d²`, and `α` conjugates `ι` by the Frobenius of `L₀`, then `ord(α)` is a
local invariant of `D` (Milne, *CFT*, IV, §4, p. 140). -/
theorem isLocalInvariant_of_algHom {L₀ D : Type} [Field L₀] [ValuativeRel L₀] [TopologicalSpace L₀]
    [IsNonarchimedeanLocalField L₀] [Algebra K L₀] [ValuativeExtension K L₀] [FiniteDimensional K L₀]
    [IsGalois K L₀] [IsUnramified K L₀] [DivisionRing D] [Algebra K D] [FiniteDimensional K D] {d : ℕ}
    (hL : Module.finrank K L₀ = d) (hD : Module.finrank K D = d ^ 2) (ι : L₀ →ₐ[K] D) (α : Dˣ)
    (hα : ∀ x, ι (frobeniusAlgEquiv (K := K) (L := L₀) x) = α * ι x * ↑α⁻¹) :
    IsLocalInvariant K D (ordD K D (α : D)) := by
  set g := frobeniusAlgEquiv (K := K) (L := L₀)
  let e : L₀ ≃ₐ[K] ι.range := AlgEquiv.ofInjective ι ι.toRingHom.injective
  have hB : IsField ι.range := e.symm.toMulEquiv.isField (Field.toIsField L₀)
  have he : ∀ y, ((e y : ι.range) : D) = ι y := fun _ => rfl
  let σ : ι.range ≃ₐ[K] ι.range := (e.symm.trans g).trans e
  have hσ : ∀ y, ((σ (e y) : ι.range) : D) = ι (g y) := fun y => by
    simp [σ, he]
  have hq : Nat.card 𝓀[K] ≠ 0 := Nat.card_pos.ne'
  refine ⟨ι.range, hB, σ, α, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← e.toLinearEquiv.finrank_eq, hL, hD]
  · intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : y ≠ 0 := by rintro rfl; exact hx (map_zero e)
    exact ⟨_, by rw [he, ordD_algHom_eq hL ι y hy]⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hσ, he]
    by_cases hy : y = 0
    · left
      rw [hy, map_zero, map_zero, zero_pow hq]
    by_cases hz : g y - y ^ Nat.card 𝓀[K] = 0
    · left
      rw [sub_eq_zero.1 hz, map_pow]
    right
    rw [he, ordD_algHom_eq hL ι y hy] at hx
    have hint : y ∈ 𝒪[L₀] := by
      have := (mem_integer_iff_toAdd_normalizedValuation_nonneg (Units.mk0 y hy)).2 (by exact_mod_cast hx)
      simpa using this
    have hv := valuation_frobeniusAlgEquiv_sub_pow (K := K) (L := L₀) ⟨y, hint⟩
    have h2 : ι (g y) - ι y ^ Nat.card 𝓀[K] = ι (g y - y ^ Nat.card 𝓀[K]) := by
      rw [map_sub, map_pow]
    rw [h2, ordD_algHom_eq hL ι _ hz]
    have hlt : ValuativeRel.valuation L₀ (g y - y ^ Nat.card 𝓀[K]) < 1 := by simpa using hv
    have h3 := (toAdd_normalizedValuation_le_iff_valuation_le (Units.mk0 _ hz) 1).not
    simp only [map_one, toAdd_one, Units.val_one, Units.val_mk0, not_le] at h3
    exact_mod_cast h3.2 hlt
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hσ, he]
    exact hα y

/-- **Every central division algebra over a nonarchimedean local field has a local invariant** (Milne, *CFT*, IV,
§4, p. 140), for `K` in `Type`: the second field of `LocalDivisionAlgebraFacts`. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §4, existence of the local invariant, p. 140"]
theorem exists_isLocalInvariant (D : Type) [Ring D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] [Nontrivial D] (hD : IsDivisionAlgebra D) : ∃ r : ℚ, IsLocalInvariant K D r := by
  let _ : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (hD a h)
  set d := TauCeti.Algebra.deg K D with hd
  have hdD : Module.finrank K D = d ^ 2 := (TauCeti.Algebra.deg_sq ..).symm
  have hd0 : d ≠ 0 := by
    intro h0
    have := Module.finrank_pos (R := K) (M := D)
    rw [hdD, h0] at this
    simp at this
  obtain ⟨ι⟩ := exists_unramified_algHom K D hdD
  let _ := algebraicExtensionValuativeRel K (unramL K d)
  let _ := algebraicExtensionNormedFieldTopology K (unramL K d)
  have := finiteExtension_isNonarchimedeanLocalField K (unramL K d)
  have := algebraicExtension_valuativeExtension K (unramL K d)
  have := isUnramified_unramifiedExtension (K := K) (Ω := SeparableClosure K) hd0
  have hfr : Module.finrank K (unramL K d) = d := finrank_unramifiedExtension hd0
  obtain ⟨b, hb⟩ := thm_2_10 (K := K) (unramL K d) D
    (ι.comp (frobeniusAlgEquiv (K := K) (L := unramL K d)).toAlgHom) ι
  exact ⟨_, isLocalInvariant_of_algHom hfr hdD ι b hb⟩

end Invariant

end NumberFieldKB.MilneCFT.Ch4
