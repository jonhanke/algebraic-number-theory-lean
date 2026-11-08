import Mathlib.Topology.Algebra.PontryaginDual
import QuadFormsKB.Citation

/-!
# Pontryagin duality: the evaluation map and the statement of the duality theorem

$G$ is a locally compact commutative group (written multiplicatively, as in Mathlib; Weil writes it additively),
$G^*$ = Mathlib's `PontryaginDual G` (continuous homomorphisms into the circle, compact-open topology).

* `dualEval G : G →ₜ* G**`, $g\mapsto(\chi\mapsto\chi(g))$, the canonical map of Weil II.§5 (p. 38). Continuity in $g$
  uses the local compactness of $G$ (joint continuity of evaluation on $G\times G^*$).
* `CharactersSeparate G`: the characters separate the points of $G$ (equivalently `dualEval G` is injective,
  `dualEval_injective_iff`).
* `PontryaginDualityStatement G`: the precise statement of the duality theorem, $G\to G^{**}$ is an isomorphism of
  topological groups (`dualEval G` is bijective and a homeomorphism). It is a statement, not an assumption: it is
  proved here for discrete groups (`NumberFieldKB.Pontryagin.Discrete`) and, given the Peter–Weyl input, for compact
  groups (`NumberFieldKB.Pontryagin.Compact`). The general case (locally compact Hausdorff groups) is proved in
  `NumberFieldKB.Pontryagin.Unconditional` (`Unconditional.lean`).
-/

open Topology

noncomputable section

namespace NumberFieldKB.Pontryagin

variable (G : Type*) [CommGroup G] [TopologicalSpace G]

/-- The characters of $G$ separate points: every $g\ne1$ has a character $\chi$ with $\chi(g)\ne1$. -/
def CharactersSeparate : Prop := ∀ g : G, g ≠ 1 → ∃ χ : PontryaginDual G, χ g ≠ 1

variable [LocallyCompactSpace G]

/-- Evaluation at a point, as a character of the dual group. -/
def evalChar (g : G) : PontryaginDual (PontryaginDual G) where
  toFun χ := χ g
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_eval_const (F := C(G, Circle)) g).comp
      (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous

/-- The canonical map $G\to G^{**}$, $g\mapsto(\chi\mapsto\chi(g))$, a continuous homomorphism. -/
def dualEval : G →ₜ* PontryaginDual (PontryaginDual G) where
  toFun := evalChar G
  map_one' := by ext χ; exact congrArg Subtype.val (map_one χ)
  map_mul' g h := by ext χ; exact congrArg Subtype.val (map_mul χ g h)
  continuous_toFun := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    have h : Continuous fun p : G × PontryaginDual G => (p.2 : G →ₜ* Circle).toContinuousMap p.1 :=
      continuous_eval.comp
        (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp continuous_snd).prodMk
          continuous_fst)
    exact h

variable {G}

@[simp]
theorem dualEval_apply (g : G) (χ : PontryaginDual G) : dualEval G g χ = χ g := rfl

/-- `dualEval G` is injective iff the characters of $G$ separate points. -/
theorem dualEval_injective_iff : Function.Injective (dualEval G) ↔ CharactersSeparate G := by
  constructor
  · intro h g hg
    by_contra hcon
    push Not at hcon
    exact hg (h (by ext χ; simp [hcon χ]))
  · intro h
    rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hne
    obtain ⟨χ, hχ⟩ := h g hne
    exact hχ (by simpa using congrArg (fun ψ => ψ χ) hg)

variable (G) in
/-- **The Pontryagin duality theorem for $G$** (Weil II.§5, p. 38: "$G$ may be identified with $(G^*)^*$"), as a
statement: the canonical map $G\to G^{**}$ is an isomorphism of topological groups. -/
def PontryaginDualityStatement : Prop :=
  ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G), ⇑e = dualEval G

/-- A bijective `dualEval` that is an open map gives the duality statement. -/
theorem pontryaginDualityStatement_of_bijective_of_isOpenMap (hb : Function.Bijective (dualEval G))
    (ho : IsOpenMap (dualEval G)) : PontryaginDualityStatement G := by
  let e₀ : G ≃* PontryaginDual (PontryaginDual G) := MulEquiv.ofBijective (dualEval G) hb
  let h₀ : G ≃ₜ PontryaginDual (PontryaginDual G) :=
    (Equiv.ofBijective _ hb).toHomeomorphOfContinuousOpen (dualEval G).continuous ho
  exact ⟨{ e₀ with
    continuous_toFun := (dualEval G).continuous
    continuous_invFun := h₀.symm.continuous }, rfl⟩

end NumberFieldKB.Pontryagin
