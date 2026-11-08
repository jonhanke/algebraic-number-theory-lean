import NumberFieldKB.WeilBNT.FunctionField.ZetaInputsProved
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# The constant field extension $k\mathbb F_{q^n}$ (Weil VII.§5, proof of Cor. 5)

* **`exists_constantPoly`**: there is a monic irreducible separable $f\in\mathbb F_q[X]$ of degree $n$ that splits in
  every finite extension of $\mathbb F_q$ of degree divisible by $n$ (the minimal polynomial of a generator of
  $\mathbb F_{q^n}$).
* **`irreducible_map_of_isConstantField`**: if $\mathbb F_q$ is the field of constants of $k$, such an $f$ stays
  irreducible over $k$ (the coefficients of a monic factor are algebraic over $\mathbb F_q$).
* **`ConstExt f`** $=k[X]/(f)$, a field, a global function field over $\mathbb F_q$
  (`instFunctionField`), separable of degree $n$ over $k$.
-/

open scoped Polynomial
open Polynomial

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

/-- A monic irreducible separable polynomial of degree $n$ over $\mathbb F_q$ splitting in every finite extension of
degree divisible by $n$. -/
theorem exists_constantPoly (n : ℕ) (hn : 0 < n) :
    ∃ f : Fq[X], f.Monic ∧ Irreducible f ∧ f.natDegree = n ∧ f.Separable ∧
      ∀ (L : Type*) [Field L] [Algebra Fq L] [Finite L], n ∣ Module.finrank Fq L →
        (f.map (algebraMap Fq L)).Splits := by
  obtain ⟨p, hp⟩ := CharP.exists Fq
  have : Fact p.Prime := ⟨CharP.char_is_prime Fq p⟩
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element Fq (FiniteField.Extension Fq p n)
  have hint : IsIntegral Fq θ := .of_finite Fq θ
  refine ⟨minpoly Fq θ, minpoly.monic hint, minpoly.irreducible hint, ?_,
    PerfectField.separable_of_irreducible (minpoly.irreducible hint), ?_⟩
  · rw [← IntermediateField.adjoin.finrank hint, hθ,
      IntermediateField.finrank_top', FiniteField.finrank_extension]
  · intro L _ _ _ hdvd
    obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
      (F := Fq) (K := FiniteField.Extension Fq p n) (L := L)
      (by rwa [FiniteField.finrank_extension])
    have hs : ((minpoly Fq θ).map (algebraMap Fq (FiniteField.Extension Fq p n))).Splits :=
      Normal.splits inferInstance θ
    have := hs.map (φ : FiniteField.Extension Fq p n →+* L)
    rwa [Polynomial.map_map, show (φ : FiniteField.Extension Fq p n →+* L).comp
      (algebraMap Fq (FiniteField.Extension Fq p n)) = algebraMap Fq L from
      φ.comp_algebraMap] at this

/-- If $\mathbb F_q$ is algebraically closed in $k$, a monic irreducible $f\in\mathbb F_q[X]$ stays irreducible
over $k$. -/
theorem irreducible_map_of_isConstantField (hc : IsConstantField Fq k) {f : Fq[X]} (hm : f.Monic)
    (hirr : Irreducible f) : Irreducible (f.map (algebraMap Fq k)) := by
  have hFm : (f.map (algebraMap Fq k)).Monic := hm.map _
  have hpos : 0 < f.natDegree := hirr.natDegree_pos
  have hnu : ¬ IsUnit (f.map (algebraMap Fq k)) :=
    not_isUnit_of_natDegree_pos _ (by rwa [hm.natDegree_map])
  obtain ⟨g, gm, gi, gd⟩ := exists_monic_irreducible_factor _ hnu
  have hint : ∀ i, IsIntegral Fq (g.coeff i) := fun i =>
    Polynomial.isIntegral_coeff_of_dvd f g hm gm gd i
  have hlift : g ∈ Polynomial.lifts (algebraMap Fq k) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact hc _ (hint i).isAlgebraic
  obtain ⟨g₀, hg₀, -, hg₀m⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift gm
  have hdvd : g₀ ∣ f := by
    rw [← Polynomial.map_dvd_map (algebraMap Fq k) (algebraMap Fq k).injective hg₀m, hg₀]
    exact gd
  obtain ⟨h, hh⟩ := hdvd
  rcases hirr.isUnit_or_isUnit hh with h1 | h1
  · exact absurd (hg₀ ▸ h1.map (Polynomial.mapRingHom (algebraMap Fq k))) gi.not_isUnit
  · have : f.map (algebraMap Fq k) = g * h.map (algebraMap Fq k) := by
      rw [hh, Polynomial.map_mul, hg₀]
    rw [this]
    exact (irreducible_mul_isUnit (h1.map (Polynomial.mapRingHom (algebraMap Fq k)))).2 gi

variable (k) in
/-- **The constant field extension** $k[X]/(f)$. -/
abbrev ConstExt (f : Fq[X]) : Type _ := AdjoinRoot (f.map (algebraMap Fq k))

section ConstExt

variable (f : Fq[X]) [Fact (Irreducible (f.map (algebraMap Fq k)))]

example : IsScalarTower (RatFunc Fq) k (ConstExt k f) := inferInstance

example : IsScalarTower Fq (RatFunc Fq) (ConstExt k f) := inferInstance

example : IsScalarTower Fq k (ConstExt k f) := inferInstance

theorem finrank_constExt (hm : f.Monic) : Module.finrank k (ConstExt k f) = f.natDegree := by
  have hne : f.map (algebraMap Fq k) ≠ 0 := (hm.map _).ne_zero
  rw [(AdjoinRoot.powerBasis hne).finrank]
  simp [AdjoinRoot.powerBasis_dim, hm.natDegree_map]

theorem finiteDimensional_constExt (hm : f.Monic) : FiniteDimensional k (ConstExt k f) := by
  have hne : f.map (algebraMap Fq k) ≠ 0 := (hm.map _).ne_zero
  exact (AdjoinRoot.powerBasis hne).finite

/-- $k[X]/(f)$ is a global function field over $\mathbb F_q$. -/
theorem functionField_constExt (hm : f.Monic) : FunctionField Fq (ConstExt k f) := by
  have := finiteDimensional_constExt (k := k) f hm
  exact FiniteDimensional.trans (RatFunc Fq) k (ConstExt k f)

theorem isSeparable_constExt (hm : f.Monic) (hs : f.Separable) :
    Algebra.IsSeparable k (ConstExt k f) := by
  have hne : f.map (algebraMap Fq k) ≠ 0 := (hm.map _).ne_zero
  have := finiteDimensional_constExt (k := k) f hm
  have h1 : IsSeparable k (AdjoinRoot.root (f.map (algebraMap Fq k))) := by
    have : minpoly k (AdjoinRoot.root (f.map (algebraMap Fq k))) = f.map (algebraMap Fq k) := by
      rw [AdjoinRoot.minpoly_root hne, (hm.map _).leadingCoeff]; simp
    rw [IsSeparable, this]; exact hs.map
  have h2 := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k
    (ConstExt k f)).2 h1
  refine ⟨fun x => ?_⟩
  apply IntermediateField.isSeparable_of_mem_isSeparable k (ConstExt k f)
    (L := IntermediateField.adjoin k {AdjoinRoot.root (f.map (algebraMap Fq k))})
  apply IntermediateField.algebra_adjoin_le_adjoin
  rw [AdjoinRoot.adjoinRoot_eq_top]; trivial

end ConstExt

end NumberFieldKB.WeilBNT.FF
