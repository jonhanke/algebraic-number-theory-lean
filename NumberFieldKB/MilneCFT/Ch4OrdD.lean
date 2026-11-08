import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Special
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Norm.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.AlgebraicExtension.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.FiniteExtension.Basic

/-!
# Milne, Class Field Theory, Chapter IV, §4: `ord` on a division algebra is ultrametric

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV, §4, p. 139: for a central division algebra $D$ over a nonarchimedean local field $K$,
"it is possible to verify" that $\mathrm{ord}$ (`ordD`) satisfies the ultrametric inequality
$\mathrm{ord}(\alpha+\beta) \ge \min(\mathrm{ord}\,\alpha, \mathrm{ord}\,\beta)$.
Centrality is not needed for the proof given here.

For a subalgebra $E \subseteq D$ which is a field, $\mathrm{Nm}_{D/K}(x) = \mathrm{Nm}_{E/K}(x)^{[D:E]}$
(`norm_eq_norm_pow`), so $\mathrm{ord}(x) = \mathrm{ord}_K(\mathrm{Nm}_{E/K}x)/[E:K]$ (`ordD_eq`).
By the valuation theory of the finite extension $E/K$ (Tau Ceti port: `algebraicExtensionValuativeRel`,
`toAdd_normalizedValuation_norm`), $\mathrm{ord}(x) \ge 0$ iff $x$ is integral over $\mathcal O_K$
(`ordD_nonneg_iff`), and $\mathrm{ord}(x) > 0$ iff the valuation of $x$ is $< 1$ (`ordD_pos_iff`).
For $\gamma \in D$ with $\mathrm{ord}\,\gamma \ge 0$ take $E = K[\gamma]$: $1 + \gamma$ is integral, so
$\mathrm{ord}(1+\gamma) \ge 0$ (`ordD_one_add_nonneg`); the general inequality (`ordD_add_le`)
follows by multiplicativity of `ordD` (`ordD_mul`).

The helper theorems that need `[Nontrivial D]` are stated with it; `ordD_add_le` derives it from
$\alpha \neq 0$.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch4

universe u

/-! ### Elementary properties of `ordK` -/

section LocalAux

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- On nonzero elements, `ordK` is the additive normalized valuation of Tau Ceti. -/
theorem ordK_eq_toAdd {a : K} (ha : a ≠ 0) :
    ordK K a = (TauCeti.normalizedValuation K (Units.mk0 a ha)).toAdd := by
  rw [TauCeti.toAdd_normalizedValuation_eq_neg_log]; rfl

theorem ordK_one : ordK K (1 : K) = 0 := by
  rw [ordK_eq_toAdd one_ne_zero]
  have : Units.mk0 (1 : K) one_ne_zero = 1 := Units.ext (by simp)
  simp [this]

/-- `ordK` is additive on products of nonzero elements. -/
theorem ordK_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordK K (a * b) = ordK K a + ordK K b := by
  rw [ordK_eq_toAdd ha, ordK_eq_toAdd hb, ordK_eq_toAdd (mul_ne_zero ha hb)]
  have : Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb :=
    Units.ext (by simp)
  rw [this, map_mul, toAdd_mul]

/-- For `a ≠ 0`, `0 ≤ ordK a` iff the valuation is `≤ 1`. -/
theorem ordK_nonneg_iff {a : K} (ha : a ≠ 0) :
    0 ≤ ordK K a ↔ ValuativeRel.valuation K a ≤ 1 := by
  rw [ordK_eq_toAdd ha, ← Valuation.mem_integer_iff,
    ← TauCeti.mem_integer_iff_toAdd_normalizedValuation_nonneg (Units.mk0 a ha)]
  rfl

/-- For `a ≠ 0`, `0 < ordK a` iff the valuation is `< 1`. -/
theorem ordK_pos_iff {a : K} (ha : a ≠ 0) :
    0 < ordK K a ↔ ValuativeRel.valuation K a < 1 := by
  have hinv : ordK K a⁻¹ = - ordK K a := by
    have := ordK_mul ha (inv_ne_zero ha)
    rw [mul_inv_cancel₀ ha, ordK_one] at this
    omega
  have h2 := ordK_nonneg_iff (inv_ne_zero ha)
  rw [hinv, map_inv₀, inv_le_one_iff₀] at h2
  have h3 : (0 < ordK K a) ↔ ¬ (0 ≤ - ordK K a) := by omega
  rw [h3, h2]
  have : ValuativeRel.valuation K a ≠ 0 := by simpa using ha
  constructor
  · intro h; by_contra hc; push Not at hc
    exact h (Or.inr (by simpa using hc))
  · intro h hh
    rcases hh with hh | hh
    · exact this (le_antisymm hh zero_le)
    · exact absurd hh (not_le.2 h)

end LocalAux

/-! ### Norms from a finite extension field -/

section FieldLevel

open TauCeti

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem ordK_norm_eq_mul_aux {F : Type u} [Field F] [Algebra K F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeExtension K F]
    (x : F) (hx : x ≠ 0) :
    ordK K (Algebra.norm K x) = (inertiaDegree K F : ℤ) * ordK F x := by
  have := finite_of_valuativeExtension K F
  have hn : Algebra.norm K x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  rw [ordK_eq_toAdd hn, ordK_eq_toAdd hx]
  have h := toAdd_normalizedValuation_norm (K := K) (L := F) (Units.mk0 x hx)
  have e : Algebra.normUnits K (Units.mk0 x hx) = Units.mk0 _ hn := Units.ext (by simp)
  rw [e] at h
  simpa using h

variable (F : Type u) [Field F] [Algebra K F] [FiniteDimensional K F]

/-- For `x ≠ 0` in a finite extension field `F/K`: `0 ≤ ord_K(Nm x)` iff `x` is integral over
`𝒪[K]`. -/
theorem ordK_norm_nonneg_iff_isIntegral {x : F} (hx : x ≠ 0) :
    0 ≤ ordK K (Algebra.norm K x) ↔ IsIntegral 𝒪[K] x := by
  letI := algebraicExtensionValuativeRel K F
  letI := algebraicExtensionNormedFieldTopology K F
  haveI := finiteExtension_isNonarchimedeanLocalField K F
  haveI := algebraicExtension_valuativeExtension K F
  rw [ordK_norm_eq_mul_aux x hx,
    mul_nonneg_iff_of_pos_left (by exact_mod_cast inertiaDegree_pos (K := K) (L := F)),
    ordK_nonneg_iff hx,
    Valuation.Integers.isIntegral_iff_valuation_le_one
      (Valuation.integer.integers (ValuativeRel.valuation K))]

/-- For `x ≠ 0` in a finite extension field `F/K`: `0 < ord_K(Nm x)` iff the valuation of `x`
(the spectral valuation `algebraicExtensionValuativeRel K F`) is `< 1`. -/
theorem ordK_norm_pos_iff_valuation_lt_one {x : F} (hx : x ≠ 0) :
    0 < ordK K (Algebra.norm K x) ↔
      (letI := algebraicExtensionValuativeRel K F; ValuativeRel.valuation F x < 1) := by
  letI := algebraicExtensionValuativeRel K F
  letI := algebraicExtensionNormedFieldTopology K F
  haveI := finiteExtension_isNonarchimedeanLocalField K F
  haveI := algebraicExtension_valuativeExtension K F
  rw [ordK_norm_eq_mul_aux x hx,
    mul_pos_iff_of_pos_left (by exact_mod_cast inertiaDegree_pos (K := K) (L := F)),
    ordK_pos_iff hx]

end FieldLevel

/-! ### Norms from a subfield of a division algebra -/

section Subfield

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D : Type u} [Ring D] [Algebra K D] [FiniteDimensional K D] (E : Subalgebra K D)

/-- **Norm from a subfield.** For a subalgebra `E ⊆ D` which is a field and `x ∈ E`,
`Nm_{D/K}(x) = Nm_{E/K}(x) ^ [D : E]`, where `D` is a left `E`-vector space. -/
theorem norm_eq_norm_pow (hE : IsField E) (x : E) :
    Algebra.norm K (x : D) = (Algebra.norm K x) ^ Module.finrank E D := by
  letI : Field E := hE.toField
  have hfree : Module.Free E D := inferInstance
  have h1 : (Algebra.lmul K D (x : D)) = ((x • LinearMap.id : D →ₗ[E] D)).restrictScalars K := by
    ext y; rfl
  rw [Algebra.norm_apply, h1, LinearMap.det_restrictScalars, LinearMap.det_smul]
  simp

/-- `[D : K] = [E : K] [D : E]` for a subalgebra `E ⊆ D` which is a field. -/
theorem finrank_eq_finrank_mul (hE : IsField E) :
    Module.finrank K D = Module.finrank K E * Module.finrank E D := by
  letI : Field E := hE.toField
  exact (Module.finrank_mul_finrank K E D).symm

/-- **`ord` on a subfield.** For `x ∈ E`, `ord(x) = ord_K(Nm_{E/K} x) / [E : K]`. -/
theorem ordD_eq [Nontrivial D] (hE : IsField E) (x : E) :
    ordD K D (x : D) = (ordK K (Algebra.norm K x) : ℚ) / Module.finrank K E := by
  letI : Field E := hE.toField
  have hm : Module.finrank E D ≠ 0 := by
    have : Module.Finite E D := Module.Finite.of_restrictScalars_finite K E D
    exact (Module.finrank_pos (R := E) (M := D)).ne'
  have hk : Module.finrank K E ≠ 0 := (Module.finrank_pos (R := K) (M := E)).ne'
  unfold ordD
  rw [norm_eq_norm_pow E hE, ordK_pow, finrank_eq_finrank_mul E hE]
  push_cast
  field_simp

/-- `ord(x) ≥ 0` iff `x` is integral over `𝒪[K]`, for `0 ≠ x ∈ E`. -/
theorem ordD_nonneg_iff [Nontrivial D] (hE : IsField E) {x : E} (hx : x ≠ 0) :
    0 ≤ ordD K D (x : D) ↔ IsIntegral 𝒪[K] x := by
  letI : Field E := hE.toField
  have hk : (0 : ℚ) < Module.finrank K E := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := E))
  rw [ordD_eq E hE, le_div_iff₀ hk, zero_mul, ← Int.cast_zero, Int.cast_le]
  exact ordK_norm_nonneg_iff_isIntegral E hx

/-- `ord(x) > 0` iff the valuation of `x` (spectral valuation of the finite extension field `E/K`)
is `< 1`, for `0 ≠ x ∈ E`. -/
theorem ordD_pos_iff [Nontrivial D] (hE : IsField E) {x : E} (hx : x ≠ 0) :
    0 < ordD K D (x : D) ↔
      (letI : Field E := hE.toField
       letI := TauCeti.algebraicExtensionValuativeRel K E
       ValuativeRel.valuation E x < 1) := by
  letI : Field E := hE.toField
  have hk : (0 : ℚ) < Module.finrank K E := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := E))
  rw [ordD_eq E hE, lt_div_iff₀ hk, zero_mul, ← Int.cast_zero, Int.cast_lt]
  exact ordK_norm_pos_iff_valuation_lt_one E hx

/-- `ord(x) > 0` iff `Nm_{E/K}(x)` lies in the maximal ideal, i.e. has valuation `< 1` in `K`. -/
theorem ordD_pos_iff_norm [Nontrivial D] (hE : IsField E) {x : E} (hx : x ≠ 0) :
    0 < ordD K D (x : D) ↔ ValuativeRel.valuation K (Algebra.norm K x) < 1 := by
  letI : Field E := hE.toField
  have hk : (0 : ℚ) < Module.finrank K E := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := E))
  rw [ordD_eq E hE, lt_div_iff₀ hk, zero_mul, ← Int.cast_zero, Int.cast_lt]
  exact ordK_pos_iff (Algebra.norm_ne_zero_iff.mpr hx)

end Subfield

/-! ### Multiplicativity and the ultrametric inequality -/

section Division

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D : Type u} [Ring D] [Algebra K D] [FiniteDimensional K D]

/-- The reduced norm of a nonzero element of a division algebra is nonzero. -/
theorem norm_ne_zero_of_isDivisionAlgebra (hD : IsDivisionAlgebra D) {x : D} (hx : x ≠ 0) :
    Algebra.norm K x ≠ 0 := by
  obtain ⟨u, rfl⟩ := hD x hx
  exact (u.isUnit.map (Algebra.norm K)).ne_zero

/-- `ordD` is additive on products of nonzero elements of a division algebra. -/
theorem ordD_mul (hD : IsDivisionAlgebra D) {a b : D} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordD K D (a * b) = ordD K D a + ordD K D b := by
  unfold ordD
  rw [map_mul, ordK_mul (norm_ne_zero_of_isDivisionAlgebra hD ha)
    (norm_ne_zero_of_isDivisionAlgebra hD hb)]
  push_cast; ring

theorem ordD_one : ordD K D (1 : D) = 0 := by simp [ordD, ordK_one]

theorem isDomain_of_isDivisionAlgebra (hD : IsDivisionAlgebra D) [Nontrivial D] : IsDomain D := by
  letI : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (hD a h)
  infer_instance

/-- The subalgebra `K[γ]` of a (nontrivial) division algebra is a field. -/
theorem isField_adjoin_singleton (hD : IsDivisionAlgebra D) [Nontrivial D] (γ : D) :
    IsField (Algebra.adjoin K {γ}) := by
  haveI := isDomain_of_isDivisionAlgebra hD
  refine ⟨⟨0, 1, zero_ne_one⟩, fun a b => ?_, fun {a} ha => ?_⟩
  · exact Subtype.ext (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (s := {γ}) b.2
      (fun c hc => by
        rw [Set.mem_singleton_iff] at hc; subst hc
        exact (Algebra.commute_of_mem_adjoin_self a.2).symm))
  · obtain ⟨u, hu⟩ := FiniteDimensional.isUnit K (K := Algebra.adjoin K {γ}) ha
    exact ⟨↑u⁻¹, by rw [← hu]; exact u.mul_inv⟩

/-- If `ord γ ≥ 0` and `1 + γ ≠ 0` then `ord (1 + γ) ≥ 0`. -/
theorem ordD_one_add_nonneg (hD : IsDivisionAlgebra D) [Nontrivial D] {γ : D} (hγ : γ ≠ 0)
    (h1 : 1 + γ ≠ 0) (h : 0 ≤ ordD K D γ) : 0 ≤ ordD K D (1 + γ) := by
  have hE := isField_adjoin_singleton (K := K) hD γ
  set E := Algebra.adjoin K {γ}
  let x : E := ⟨γ, Algebra.self_mem_adjoin_singleton K γ⟩
  have hx : x ≠ 0 := fun h0 => hγ (congrArg Subtype.val h0)
  have hx1 : 1 + x ≠ 0 := fun h0 => h1 (congrArg Subtype.val h0)
  letI : Field E := hE.toField
  have hint : IsIntegral 𝒪[K] x := (ordD_nonneg_iff E hE hx).1 h
  have hint1 : IsIntegral 𝒪[K] (1 + x) := isIntegral_one.add hint
  exact (ordD_nonneg_iff E hE hx1).2 hint1

private theorem ordD_add_le_aux (hD : IsDivisionAlgebra D) [Nontrivial D] {α β : D}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α + β ≠ 0) (hle : ordD K D α ≤ ordD K D β) :
    ordD K D α ≤ ordD K D (α + β) := by
  obtain ⟨u, hu⟩ := hD α hα
  set δ : D := ↑u⁻¹ * β with hδ
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hβ
    have := congrArg (fun z => (u : D) * z) h0
    simpa [hδ, ← mul_assoc] using this
  have hsum : α + β = α * (1 + δ) := by
    rw [← hu, mul_add, mul_one, hδ, ← mul_assoc, Units.mul_inv, one_mul]
  have h1δ : 1 + δ ≠ 0 := by
    intro h0; apply hαβ; rw [hsum, h0, mul_zero]
  have hinv : ordD K D (↑u⁻¹ : D) = - ordD K D α := by
    have hu0 : (↑u⁻¹ : D) ≠ 0 := (u⁻¹).ne_zero
    have := ordD_mul (K := K) hD hα hu0
    rw [← hu, Units.mul_inv, ordD_one] at this
    rw [← hu]; linarith
  have hδord : 0 ≤ ordD K D δ := by
    rw [hδ, ordD_mul hD (u⁻¹).ne_zero hβ, hinv]; linarith
  have := ordD_one_add_nonneg (K := K) hD hδ0 h1δ hδord
  rw [hsum, ordD_mul hD hα h1δ]
  linarith

/-- **`ord` is ultrametric on a division algebra** (Milne, p. 139: "it is possible to verify";
centrality is not needed). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §4, ord on D is ultrametric, p. 139"]
theorem ordD_add_le (hD : IsDivisionAlgebra D) (α β : D) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hαβ : α + β ≠ 0) : min (ordD K D α) (ordD K D β) ≤ ordD K D (α + β) := by
  haveI : Nontrivial D := ⟨⟨α, 0, hα⟩⟩
  rcases le_total (ordD K D α) (ordD K D β) with h | h
  · rw [min_eq_left h]; exact ordD_add_le_aux hD hα hβ hαβ h
  · rw [min_eq_right h, add_comm]
    exact ordD_add_le_aux hD hβ hα (by rwa [add_comm]) h

end Division

end NumberFieldKB.MilneCFT.Ch4
