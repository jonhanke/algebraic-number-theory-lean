import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4LocalInvariant
import NumberFieldKB.MilneCFT.Ch4CyclicInvariant
import NumberFieldKB.MilneCFT.Ch4InvariantNormalize
import NumberFieldKB.MilneCFT.Ch4BrauerTauCeti

/-!
# Milne, Class Field Theory, Chapter IV, §4: the local invariant of a division algebra (for `K : Type`)

Let `K` be a nonarchimedean local field and `D` a central division algebra over `K` of degree `d²`. Milne defines the
invariant of `D` (p. 140) as `ord(α) mod ℤ`, where `L ⊆ D` is a maximal subfield unramified over `K`, `σ` its
Frobenius and `σ x = α x α⁻¹`. We show that every such `ord(α)` is, modulo `ℤ`, Tau Ceti's cohomological invariant
`inv_K [D]` (`invMap K` read through `brauerGroupEquivBr K`): the triple can be moved to the unramified extension of
degree `d` inside `Kˢ` (`exists_algHom_of_isLocalInvariant`), `αᵈ = a ∈ Kˣ` (`exists_pow_eq_algebraMap`), `D` is the
cyclic crossed product `(L/K, σ, a)` whose invariant is `v(a)/d` (`invMap_brauerGroupEquivBr_of_conj`), and
`ord(α) = v(a)/d`. This proves the named statement `LocalDivisionAlgebraFacts K` and, since `inv_K` is then Tau
Ceti's invariant, Proposition 4.3 (`Prop4_3`) and Remark 4.4 (a) (`Remark4_4a`), for `K` in `Type`.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch4

open TauCeti ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem ordD_pow {D : Type} [Ring D] [Algebra K D] [FiniteDimensional K D] (hD : IsDivisionAlgebra D)
    {x : D} (hx : x ≠ 0) (n : ℕ) : ordD K D (x ^ n) = n * ordD K D x := by
  have : Nontrivial D := ⟨⟨x, 0, hx⟩⟩
  have hdom := isDomain_of_isDivisionAlgebra hD
  induction n with
  | zero => simp [ordD_one]
  | succ n ih =>
    rw [pow_succ, ordD_mul hD (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

theorem ordD_algebraMap_eq {D : Type} [Ring D] [Algebra K D] [FiniteDimensional K D] [Nontrivial D] (a : K) :
    ordD K D (algebraMap K D a) = ordK K a := by
  unfold ordD
  rw [Algebra.norm_algebraMap, ordK_pow]
  have : (Module.finrank K D : ℚ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := K) (M := D)).ne'
  push_cast
  field_simp

set_option synthInstance.maxHeartbeats 400000 in
/-- **The invariant of the standard triple.** If the unramified extension `L₀` of degree `d` inside `Kˢ` embeds in a
central division algebra `D` of degree `d²` by `ι`, and `α` conjugates `ι` by the Frobenius of `L₀`, then
`ord(α) mod ℤ` is Tau Ceti's invariant of `[D]` (Milne, *CFT*, IV, §4, p. 140). -/
theorem coe_ordD_eq_invMap (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (L₀ : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L₀]
    [IsGalois K L₀] [ValuativeRel L₀] [TopologicalSpace L₀] [IsNonarchimedeanLocalField L₀]
    [ValuativeExtension K L₀] [IsUnramified K L₀] {d : ℕ} (hL : Module.finrank K L₀ = d)
    (hD : Module.finrank K D = d ^ 2) (ι : L₀ →ₐ[K] D) (α : Dˣ)
    (hα : ∀ x : L₀, ι (frobeniusAlgEquiv (K := K) (L := L₀) x) = α * ι x * ↑α⁻¹) :
    ((ordD K D (α : D) : ℚ) : AddCircle (1 : ℚ)) =
      invMap K (brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.mk (CSA.of K D)))) := by
  set g := frobeniusAlgEquiv (K := K) (L := L₀)
  have hg : ∀ σ : L₀ ≃ₐ[K] L₀, σ ∈ Subgroup.zpowers g := fun σ => by
    rw [zpowers_frobeniusAlgEquiv]; exact Subgroup.mem_top σ
  have hord : orderOf g = d := by
    rw [orderOf_frobeniusAlgEquiv, IsUnramified.inertiaDegree_eq_finrank, hL]
  have hgd : g ^ d = 1 := hord ▸ pow_orderOf_eq_one g
  obtain ⟨a, ha⟩ := exists_pow_eq_algebraMap hL hD ι g hg hgd α hα
  have ha' : (α : D) ^ d = algebraMap K D a := by simpa using ha
  rw [invMap_brauerGroupEquivBr_of_conj K L₀ D hL hD ι α hα a ha']
  congr 1
  have hdiv : IsDivisionAlgebra D := fun x hx => isUnit_iff_ne_zero.2 hx
  have hd0 : (d : ℚ) ≠ 0 := by
    rw [← hL]; exact_mod_cast (Module.finrank_pos (R := K) (M := L₀)).ne'
  have h1 := ordD_pow (K := K) hdiv α.ne_zero d
  rw [ha', ordD_algebraMap_eq, ordK_eq_toAdd a.ne_zero] at h1
  have : Units.mk0 (a : K) a.ne_zero = a := Units.ext rfl
  rw [this] at h1
  field_simp
  linarith

set_option synthInstance.maxHeartbeats 400000 in
/-- **Every local invariant is Tau Ceti's invariant modulo `ℤ`** (Milne, *CFT*, IV, §4, p. 140: the invariant
"depends only on the isomorphism class of `D`"), for `K` in `Type`. -/
theorem coe_eq_invMap_of_isLocalInvariant (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] {r : ℚ} (h : IsLocalInvariant K D r) :
    ((r : ℚ) : AddCircle (1 : ℚ)) =
      invMap K (brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.mk (CSA.of K D)))) := by
  obtain ⟨L, -, -, -, hdim, -⟩ := id h
  set d := Module.finrank K L
  have hd0 : d ≠ 0 := by
    intro h0
    have := Module.finrank_pos (R := K) (M := D)
    rw [hdim, h0] at this
    simp at this
  let _ := algebraicExtensionValuativeRel K (unramL K d)
  let _ := algebraicExtensionNormedFieldTopology K (unramL K d)
  have := finiteExtension_isNonarchimedeanLocalField K (unramL K d)
  have := algebraicExtension_valuativeExtension K (unramL K d)
  have := isUnramified_unramifiedExtension (K := K) (Ω := SeparableClosure K) hd0
  have hfr : Module.finrank K (unramL K d) = d := finrank_unramifiedExtension hd0
  obtain ⟨ι, α, hα, hr⟩ := exists_algHom_of_isLocalInvariant hfr hdim h
  rw [hr]
  exact coe_ordD_eq_invMap D (unramL K d) hfr hdim ι α hα

theorem nontrivial_of_isLocalInvariant {D : Type} [Ring D] [Algebra K D] {r : ℚ}
    (h : IsLocalInvariant K D r) : Nontrivial D := by
  obtain ⟨L, hLf, -⟩ := h
  obtain ⟨x, y, hxy⟩ := hLf.exists_pair_ne
  exact ⟨⟨x, y, fun e => hxy (Subtype.ext e)⟩⟩

variable (K) in
/-- **The facts of Milne, *CFT*, IV, §4, pp. 139–140** (`LocalDivisionAlgebraFacts`), for `K` in `Type`: `ord` is
ultrametric on `D`, `D` has a local invariant, and the invariant is well defined modulo `ℤ` on isomorphism classes. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §4, valuation and unramified maximal subfield of D, pp. 139-140"]
theorem localDivisionAlgebraFacts : LocalDivisionAlgebraFacts K where
  ordD_add _ _ _ _ _ hD α β hα hβ hαβ := ordD_add_le hD α β hα hβ hαβ
  exists_invariant D _ _ _ _ _ hD := exists_isLocalInvariant D hD
  invariant_wellDefined D D' _ _ _ _ _ _ _ _ hD hD' e r r' hr hr' := by
    have := nontrivial_of_isLocalInvariant hr
    have := nontrivial_of_isLocalInvariant hr'
    let _ : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun a => by
      by_cases h : a = 0
      · exact Or.inr h
      · exact Or.inl (hD a h)
    let _ : DivisionRing D' := DivisionRing.ofIsUnitOrEqZero fun a => by
      by_cases h : a = 0
      · exact Or.inr h
      · exact Or.inl (hD' a h)
    have h1 := coe_eq_invMap_of_isLocalInvariant D hr
    have h2 := coe_eq_invMap_of_isLocalInvariant D' hr'
    have hmk : BrauerGroup.mk (CSA.of K D) = BrauerGroup.mk (CSA.of K D') :=
      BrauerGroup.mk_eq_mk_of_algEquiv e
    rw [hmk, ← h2] at h1
    obtain ⟨k, hk⟩ := (QuotientAddGroup.eq).1 h1
    refine ⟨-k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    push_cast
    linarith

/-- On every Brauer class, Milne's `inv_K` (defined from `LocalDivisionAlgebraFacts`) is Tau Ceti's invariant. -/
theorem invK_eq_invMap (h : LocalDivisionAlgebraFacts K) (x : BrauerGroup.{0, 0} K) :
    invK h x = addCircleEquivQZ (invMap K (brauerGroupEquivBr K (Additive.ofMul x))) := by
  obtain ⟨D, hD, rfl⟩ := remark_2_13a_exists x
  obtain ⟨r, hr⟩ := h.exists_invariant D hD
  rw [invK_eq h D hD r hr]
  let _ : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (hD a h)
  have hmk : BrauerGroup.mk D = BrauerGroup.mk (CSA.of K D) :=
    BrauerGroup.mk_eq_mk_of_algEquiv AlgEquiv.refl
  rw [hmk, ← coe_eq_invMap_of_isLocalInvariant D hr]
  rfl

variable (K) in
/-- **Proposition 4.3** (Milne, *CFT*, IV, p. 141; Hasse), for `K` in `Type`: `inv_K : Br(K) → ℚ/ℤ` is a
bijection. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 4.3, p. 141"]
theorem prop4_3 : Prop4_3 K where
  facts := localDivisionAlgebraFacts K
  bijective := by
    have : invK (localDivisionAlgebraFacts K) =
        addCircleEquivQZ ∘ invMap K ∘ brauerGroupEquivBr K ∘ Additive.ofMul := funext (invK_eq_invMap _)
    rw [this]
    exact addCircleEquivQZ.bijective.comp ((invMap K).bijective.comp
      ((brauerGroupEquivBr K).bijective.comp Additive.ofMul.bijective))

variable (K) in
/-- **Remark 4.4 (a)** (Milne, *CFT*, IV, p. 141), for `K` in `Type`: `inv_K` is a homomorphism. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Rem. 4.4(a), p. 141"]
theorem remark4_4a : Remark4_4a K where
  facts := localDivisionAlgebraFacts K
  map_mul x y := by
    rw [invK_eq_invMap, invK_eq_invMap, invK_eq_invMap, ofMul_mul, map_add, map_add, map_add]

end NumberFieldKB.MilneCFT.Ch4
