import NumberFieldKB.WeilBNT.FieldClassificationB
import NumberFieldKB.WeilBNT.PFieldStructure
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Weil, *Basic Number Theory*, I.§4, text p. 21: the list of local fields

A *local field* (Weil, p. 21) is a commutative nondiscrete locally compact field.

* **`weil_I_4_text_p21`**: a local field $F$ is isomorphic as a topological field to $\mathbb R$ or to $\mathbb C$, or
  is a finite extension of $\mathbb Q_p$ for some prime $p$ (a continuous embedding $\mathbb Q_p\to F$ with $F$ of finite
  dimension over its image), or is isomorphic as a topological field to a field of formal Laurent series
  $\mathbb F_q((T))$ over a finite field.

*Proof* (Weil's): characteristic $0$ is Thm. 5 (b) (`weil_I_3_thm5_b`), a commutative finite extension of $\mathbb R$
being $\mathbb R$ or $\mathbb C$ ($\mathbb C$ is algebraically closed); characteristic $p$ is Thm. 8 (`weil_I_4_thm8`).
-/

open Topology

noncomputable section

namespace NumberFieldKB.WeilBNT.FieldModule

/-- A commutative finite extension of $\mathbb R$ (given by a continuous embedding with a basis) is isomorphic
as a topological field to $\mathbb R$ or to $\mathbb C$. -/
theorem real_extension_cases {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    (f : ℝ →+* F) (hf : Continuous f) (δ : ℕ) (b : Fin δ → F)
    (hb : Function.Bijective (fun c : Fin δ → ℝ => ∑ i, f (c i) * b i)) :
    (∃ e : F ≃+* ℝ, Continuous e ∧ Continuous e.symm) ∨
    (∃ e : F ≃+* ℂ, Continuous e ∧ Continuous e.symm) := by
  letI : Algebra ℝ F := f.toAlgebra
  haveI : ContinuousSMul ℝ F :=
    ⟨by
      have : (fun x : ℝ × F => x.1 • x.2) = fun x => f x.1 * x.2 := by
        funext x; exact Algebra.smul_def _ _
      rw [this]
      exact (hf.comp continuous_fst).mul continuous_snd⟩
  have hfun : (Fintype.linearCombination ℝ b : (Fin δ → ℝ) →ₗ[ℝ] F) =
      fun c : Fin δ → ℝ => ∑ i, f (c i) * b i := by
    funext c
    simp [Fintype.linearCombination_apply, Algebra.smul_def]
    rfl
  let L : (Fin δ → ℝ) ≃ₗ[ℝ] F :=
    LinearEquiv.ofBijective (Fintype.linearCombination ℝ b) (by rw [← hfun] at hb; exact hb)
  haveI : FiniteDimensional ℝ F := Module.Finite.equiv L
  have hrank : Module.finrank ℝ F = δ := by simpa using L.finrank_eq.symm
  haveI : Algebra.IsAlgebraic ℝ F := Algebra.IsAlgebraic.of_finite ℝ F
  let φ : F →ₐ[ℝ] ℂ := IsAlgClosed.lift
  have hφ : Function.Injective φ := φ.injective
  have hle : Module.finrank ℝ F ≤ 2 := by
    have := LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hφ
    simpa using this
  have hpos : 0 < Module.finrank ℝ F := Module.finrank_pos
  have hcase : Module.finrank ℝ F = 1 ∨ Module.finrank ℝ F = 2 := by omega
  rcases hcase with h1 | h2
  · left
    have hbij : Function.Bijective (algebraMap ℝ F) := by
      have : (⊥ : Subalgebra ℝ F) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
      refine ⟨(algebraMap ℝ F).injective, fun x => ?_⟩
      have hx : x ∈ (⊤ : Subalgebra ℝ F) := trivial
      rw [← this] at hx
      exact Algebra.mem_bot.1 hx
    let g : ℝ ≃ₐ[ℝ] F := AlgEquiv.ofBijective (Algebra.ofId ℝ F) hbij
    refine ⟨g.symm.toRingEquiv, ?_, ?_⟩
    · exact LinearMap.continuous_of_finiteDimensional g.symm.toLinearMap
    · exact hf
  · right
    have hbij : Function.Bijective φ := by
      refine ⟨hφ, ?_⟩
      have hsurj : LinearMap.range φ.toLinearMap = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [LinearMap.finrank_range_of_inj hφ, h2]
        simp
      intro y
      have : y ∈ LinearMap.range φ.toLinearMap := by rw [hsurj]; trivial
      exact this
    let g : F ≃ₐ[ℝ] ℂ := AlgEquiv.ofBijective φ hbij
    refine ⟨g.toRingEquiv, ?_, ?_⟩
    · exact LinearMap.continuous_of_finiteDimensional g.toLinearMap
    · exact LinearMap.continuous_of_finiteDimensional g.symm.toLinearMap

@[kb "weil1973bnt" "Ch. I, §4, text p. 21 (the local fields)"]
theorem weil_I_4_text_p21 {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] :
    (∃ e : F ≃+* ℝ, Continuous e ∧ Continuous e.symm) ∨
    (∃ e : F ≃+* ℂ, Continuous e ∧ Continuous e.symm) ∨
    (∃ (p : ℕ) (_ : Fact p.Prime) (f : ℚ_[p] →+* F) (δ : ℕ) (b : Fin δ → F), Continuous f ∧
      Function.Bijective (fun c : Fin δ → ℚ_[p] => ∑ i, f (c i) * b i)) ∨
    (∃ (p : ℕ) (_ : Fact p.Prime) (f : ℕ), ∃ e : F ≃+* LaurentSeries (GaloisField p f),
      Continuous e ∧ Continuous e.symm) := by
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hp | h0
  · have hF : IsPField F (ringChar F) := by
      refine ⟨hp, ?_⟩
      have : ((ringChar F : ℕ) : F) = 0 := by simp
      rw [this, modK_zero]
      exact zero_lt_one
    obtain ⟨f, -, hf⟩ := weil_I_4_thm6_residue hF
    haveI : Fact (ringChar F).Prime := ⟨hp⟩
    exact Or.inr (Or.inr (Or.inr ⟨ringChar F, inferInstance, f, weil_I_4_thm8 hF hf⟩))
  · haveI : CharZero F := (CharP.ringChar_zero_iff_CharZero F).1 h0
    rcases weil_I_3_thm5_b (K := F) with ⟨p, hp, f, δ, b, hfc, -, hb, -⟩ | ⟨f, δ, b, hfc, -, hb, -⟩
    · exact Or.inr (Or.inr (Or.inl ⟨p, hp, f, δ, b, hfc, hb⟩))
    · rcases real_extension_cases f hfc δ b hb with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

end NumberFieldKB.WeilBNT.FieldModule
