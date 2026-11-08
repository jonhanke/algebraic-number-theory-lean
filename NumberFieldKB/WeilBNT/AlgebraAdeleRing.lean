import NumberFieldKB.WeilBNT.AlgebraAdeleTopology

/-!
# Weil, *Basic Number Theory*, IV.§1, text p. 62: the adele ring of an algebra (number fields)

Notation as in `NumberFieldKB.WeilBNT.AlgebraAdeleTopology`: $k$ a number field (`F`), $\mathcal A$ a
finite-dimensional $k$-algebra, $\mathcal A_{\mathbb A}=k_{\mathbb A}\otimes_k\mathcal A$ with the topology of
$k_{\mathbb A}^n$ in a basis (`algAdeleTop`).

* **`weil_IV_1_text62_algebra`**: $\mathcal A_{\mathbb A}$ is a topological ring and a topological $k_{\mathbb A}$-module
  (so a topological $k_{\mathbb A}$-algebra), and for $\mathcal A\neq0$ the map $t\mapsto t\cdot1$ is injective with
  closed image: $k_{\mathbb A}\cdot1$ is a closed subring isomorphic to $k_{\mathbb A}$.
* For a finite extension $k'/k$, $(k'/k)_{\mathbb A}=k'\otimes_kk_{\mathbb A}$ is the case $\mathcal A=k'$ (the
  $k_{\mathbb A}$-algebra structure is Mathlib's tensor product algebra); its identification with $k'_{\mathbb A}$ is
  IV.§1 Thm. 1 (`weil_IV_1_thm1`).
-/

open IsDedekindDomain NumberField QuadFormsKB.Tamagawa.Measure.Weil Topology
open scoped TensorProduct

noncomputable section

namespace NumberFieldKB.WeilBNT

attribute [local instance] adelesAlgebra algAdeleTop

attribute [local instance] continuous_mul_algAdele continuous_add_algAdele t2Space_algAdele t2Space_adeles

variable {F : Type} [Field F] [NumberField F] {A : Type} [Ring A] [Algebra F A] [FiniteDimensional F A]

/-- The coordinates of $t\cdot1$ are $t\cdot\operatorname{diag}(c_j)$, $c$ the coordinates of $1\in\mathcal A$. -/
theorem coordsA_algebraMap (t : Adeles F) (j : AIdx F A) :
    coordsA F A (algebraMap (Adeles F) (Adeles F ⊗[F] A) t) j =
      t * diag F ((Module.finBasis F A).equivFun (1 : A) j) := by
  have h1 : algebraMap (Adeles F) (Adeles F ⊗[F] A) t = t • ((1 : Adeles F) ⊗ₜ[F] (1 : A)) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  rw [h1, map_smul, coords_tmul]
  rfl

/-- **Weil, IV.§1, text p. 62.** $\mathcal A_{\mathbb A}$ is a topological ring and a topological $k_{\mathbb A}$-module,
and $k_{\mathbb A}\to\mathcal A_{\mathbb A}$, $t\mapsto t\cdot1$, is injective with closed image. -/
@[kb "weil1973bnt" "Ch. IV, §1, text p.62 (the adele ring of an algebra is a topological algebra containing k_A as a closed subring)"]
theorem weil_IV_1_text62_algebra [Nontrivial A] :
    IsTopologicalRing (Adeles F ⊗[F] A) ∧ ContinuousSMul (Adeles F) (Adeles F ⊗[F] A) ∧
      Function.Injective (algebraMap (Adeles F) (Adeles F ⊗[F] A)) ∧
      IsClosed (Set.range (algebraMap (Adeles F) (Adeles F ⊗[F] A))) := by
  set c := (Module.finBasis F A).equivFun (1 : A) with hc
  have hc0 : c ≠ 0 := by
    intro h
    have : (1 : A) = 0 := (Module.finBasis F A).equivFun.injective (by rw [← hc, h, map_zero])
    exact one_ne_zero this
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  have hu : IsUnit (diag F (c i)) := (isUnit_iff_ne_zero.2 hi).map (diagRingHom F)
  obtain ⟨u, hu'⟩ := hu
  have hneg : ContinuousNeg (Adeles F ⊗[F] A) := by
    refine ⟨continuous_induced_rng.2 ?_⟩
    have : (coordsA F A ∘ fun x : Adeles F ⊗[F] A => -x) = fun x => -coordsA F A x :=
      funext fun x => map_neg _ _
    rw [this]
    exact continuous_coordsA.neg
  have hring : IsTopologicalRing (Adeles F ⊗[F] A) := {}
  refine ⟨hring, ?_, ?_, ?_⟩
  · refine ⟨continuous_induced_rng.2 ?_⟩
    have : (coordsA F A ∘ fun p : Adeles F × (Adeles F ⊗[F] A) => p.1 • p.2) = fun p =>
        p.1 • coordsA F A p.2 := funext fun p => map_smul _ _ _
    rw [this]
    exact continuous_fst.smul (continuous_coordsA.comp continuous_snd)
  · intro t t' h
    have := congrArg (fun x => coordsA F A x i) h
    simp only [coordsA_algebraMap] at this
    rw [← hu'] at this
    exact (Units.mul_left_inj u).1 this
  · have key : Set.range (algebraMap (Adeles F) (Adeles F ⊗[F] A)) =
        coordsA F A ⁻¹' {y | ∀ j, y j * diag F (c i) = y i * diag F (c j)} := by
      ext x
      simp only [Set.mem_range, Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨t, rfl⟩ j
        rw [coordsA_algebraMap, coordsA_algebraMap]
        ring
      · intro h
        refine ⟨coordsA F A x i * ↑u⁻¹, (coordsA F A).injective ?_⟩
        funext j
        rw [coordsA_algebraMap]
        change coordsA F A x i * ↑u⁻¹ * diag F (c j) = _
        have := h j
        rw [← hu'] at this
        have hinv : (↑u : Adeles F) * ↑u⁻¹ = 1 := u.mul_inv
        calc coordsA F A x i * ↑u⁻¹ * diag F (c j) = (coordsA F A x i * diag F (c j)) * ↑u⁻¹ := by ring
          _ = (coordsA F A x j * ↑u) * ↑u⁻¹ := by rw [this]
          _ = _ := by rw [mul_assoc, hinv, mul_one]
    rw [key]
    refine IsClosed.preimage continuous_coordsA ?_
    have : {y : AIdx F A → Adeles F | ∀ j, y j * diag F (c i) = y i * diag F (c j)} =
        ⋂ j, {y | y j * diag F (c i) = y i * diag F (c j)} := by
      ext y; simp
    rw [this]
    exact isClosed_iInter fun j =>
      isClosed_eq ((continuous_apply j).mul continuous_const) ((continuous_apply i).mul continuous_const)

end NumberFieldKB.WeilBNT
