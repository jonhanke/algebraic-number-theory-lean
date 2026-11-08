import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Torsion
import NumberFieldKB.MilneCFT.Ch4Splitting
import NumberFieldKB.MilneCFT.Ch4BrauerBaseChange
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.Restriction
import NumberFieldKB.TauCetiPort.Algebra.CentralSimple.MaximalSubfield.Separable

/-!
# Milne, Class Field Theory, Chapter IV, Cor. 3.17: the exponent divides the degree

We prove the named statement `ExponentDividesDegree K` of `Ch4Torsion.lean` for every field `K`.

Proof.  A central simple algebra `A` with `[A : K] = n²` is Brauer equivalent to a central division
algebra `D` of degree `d` with `n = r d` (Wedderburn).  By the Köthe–Noether theorem
(`TauCeti.Algebra.exists_isSplittingField_isSeparable_finrank_eq_deg`, ported in
`TauCetiPort/Algebra/CentralSimple/MaximalSubfield/Separable.lean`) there is a finite separable
field `L / K` of degree `d` splitting `D`.  Under Tau Ceti's identification `brauerGroupEquivBr`, base
change corresponds to the cohomological base change (`brauerGroupEquivBr_baseChange`), which is
restriction (`brBaseChange_eq_brRes`); corestriction after restriction is multiplication by
`[L : K] = d` (`brCor_brRes`).  Hence `d • [A] = 0`, so `n • [A] = 0`.
-/

open scoped TensorProduct

namespace NumberFieldKB.MilneCFT.Ch4

universe u

open TauCeti ClassFieldTheory

/-- **Exponent divides degree** (Milne, Cor. 3.17, non-Galois case): if `A` is a central simple
`K`-algebra with `[A : K] = n²`, then `[A]ⁿ = 1` in `Br(K)`.  Proved for every field `K` (all
universe-`u` central simple algebras), from the ported Köthe–Noether theorem and Tau Ceti's
cohomological Brauer group. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.17 (exponent divides degree), p. 138"]
theorem exponentDividesDegree (K : Type u) [Field K] : ExponentDividesDegree K := by
  refine ⟨fun A n hn => ?_⟩
  obtain ⟨D, hD, hmk⟩ := remark_2_13a_exists (BrauerGroup.mk A)
  letI : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (hD a h)
  have hAD : IsBrauerEquivalent A D := (BrauerGroup.mk_eq_mk_iff A D).1 hmk.symm
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨r, hr, D', _, _, _, ⟨f⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  obtain ⟨g⟩ := remark_2_13a_matrix A D hAD D' D hr.out one_ne_zero f
    (BrauerGroup.matOne D).symm
  -- degrees
  set d := TauCeti.Algebra.deg K (D : Type u) with hd
  have hdD : Module.finrank K D' = d ^ 2 := by
    rw [g.toLinearEquiv.finrank_eq, hd, TauCeti.Algebra.deg_sq]
  have h1 : Module.finrank K A = r * r * Module.finrank K D' := by
    rw [f.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp
  have hnrd : n = r * d := by
    have : n ^ 2 = (r * d) ^ 2 := by rw [← hn, h1, hdD]; ring
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) this
  -- Köthe–Noether
  obtain ⟨L, _, _, φ, hfd, hsep, hdeg, hsplit⟩ :=
    TauCeti.Algebra.exists_isSplittingField_isSeparable_finrank_eq_deg K (D : Type u)
  -- the class dies over `L`
  have hker : BrauerGroup.baseChange K L (BrauerGroup.mk D) = 1 := by
    have := (BrauerGroup.mk_mem_ker_baseChange_iff_isSplittingField (K := K) (L := L)
      (A := (D : Type u))).2 hsplit
    exact this
  let e := BrauerBaseChange.brauerGroupEquivBr_baseChange K L (BrauerGroup.mk D)
  rw [hker] at e
  let σ : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have hres : brRes K L σ (brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.mk D))) = 0 := by
    rw [← brBaseChange_eq_brRes K L σ, ← e]
    exact map_zero _
  have hcor := brCor_brRes K L σ (brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.mk D)))
  rw [hres, map_zero, hdeg] at hcor
  have hdx : d • brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.mk D)) = 0 := hcor.symm
  have hnx : n • brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.mk D)) = 0 := by
    rw [hnrd, mul_smul, hdx, smul_zero]
  rw [← map_nsmul, map_eq_zero_iff _ (brauerGroupEquivBr K).injective, ← ofMul_pow] at hnx
  rw [← hmk]
  exact Additive.ofMul.injective hnx

end NumberFieldKB.MilneCFT.Ch4
