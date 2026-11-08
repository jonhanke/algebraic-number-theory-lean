import NumberFieldKB.Pontryagin.CompactOrthogonality
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Pontryagin duality for discrete commutative groups
* `charactersSeparate_of_discrete`: the characters of a discrete commutative group separate points. This is the
  injectivity of the circle: Mathlib's `CharacterModule.exists_character_apply_ne_zero_of_ne_zero` (homomorphisms into
  $\mathbb Q/\mathbb Z$ separate points; $\mathbb Q/\mathbb Z$ is divisible, hence injective), composed with the
  embedding $\mathbb Q/\mathbb Z\hookrightarrow\mathbb R/\mathbb Z\cong\mathbb T$.
* **`pontryaginDuality_discrete`**: for a discrete commutative group $G$, the canonical map $G\to G^{**}$ is an
  isomorphism of topological groups. Injective by the above; onto because the evaluations form a subgroup of the
  characters of the compact group $G^*$ that separates its points, so it contains every character
  (`mem_of_separates`, Stone–Weierstrass and orthogonality); open because $G^{**}$ is the dual of a compact group,
  hence discrete.
-/

open Topology

noncomputable section

namespace NumberFieldKB.Pontryagin

/-- The embedding $\mathbb Q/\mathbb Z\to\mathbb R/\mathbb Z$. -/
def ratCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    intro q hq
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simp⟩)

lemma ratCircleToReal_injective : Function.Injective ratCircleToReal := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    change ((q : ℝ) : AddCircle (1 : ℝ)) = 0 at hx
    rw [AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨k, hk⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    refine ⟨k, ?_⟩
    have : ((k : ℚ) : ℝ) = (q : ℝ) := by simpa using hk
    have hq : (k : ℚ) = q := by exact_mod_cast this
    simpa using hq

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- **The characters of a discrete commutative group separate points.** -/
theorem charactersSeparate_of_discrete : CharactersSeparate G := by
  intro g hg
  have ha : Additive.ofMul g ≠ 0 := hg
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  let f : G →* Circle :=
    { toFun := fun x => AddCircle.toCircle (ratCircleToReal (c (Additive.ofMul x)))
      map_one' := by
        change AddCircle.toCircle (ratCircleToReal (c 0)) = 1
        rw [map_zero, map_zero, AddCircle.toCircle_zero]
      map_mul' := fun x y => by
        change AddCircle.toCircle (ratCircleToReal (c (Additive.ofMul x + Additive.ofMul y))) = _
        rw [map_add, map_add, AddCircle.toCircle_add] }
  refine ⟨⟨f, continuous_of_discreteTopology⟩, ?_⟩
  change AddCircle.toCircle (ratCircleToReal (c (Additive.ofMul g))) ≠ 1
  intro h
  rw [← AddCircle.toCircle_zero (T := (1 : ℝ))] at h
  have h1 := AddCircle.injective_toCircle one_ne_zero h
  rw [← map_zero ratCircleToReal] at h1
  exact hc (ratCircleToReal_injective h1)

/-- The image of `dualEval` separates the points of the dual group (always true: characters are functions). -/
lemma range_dualEval_separates {A : Type*} [CommGroup A] [TopologicalSpace A] [LocallyCompactSpace A]
    (x y : PontryaginDual A) (hxy : x ≠ y) : ∃ ψ ∈ (dualEval A).toMonoidHom.range, ψ x ≠ ψ y := by
  by_contra hcon
  push Not at hcon
  exact hxy (PontryaginDual.ext fun a => hcon (dualEval A a) ⟨a, rfl⟩)

/-- **Pontryagin duality for discrete commutative groups**: $G\to G^{**}$ is an isomorphism of topological groups. -/
theorem pontryaginDuality_discrete : PontryaginDualityStatement G := by
  refine pontryaginDualityStatement_of_bijective_of_isOpenMap ⟨?_, ?_⟩ ?_
  · exact dualEval_injective_iff.mpr charactersSeparate_of_discrete
  · intro ψ
    obtain ⟨g, hg⟩ := mem_of_separates (dualEval G).toMonoidHom.range range_dualEval_separates ψ
    exact ⟨g, hg⟩
  · intro U _
    exact isOpen_discrete _

end NumberFieldKB.Pontryagin
