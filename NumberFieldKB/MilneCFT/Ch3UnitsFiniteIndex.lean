import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Lattice

/-!
# Milne, *Class Field Theory*, Chapter III, proof of Lemma 2.5: $U_L$ is compact (open subgroups of finite index)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Ch. III, proof of
Lemma 2.5, p. 104. We prove `UnitsOpenFiniteIndex` elementarily: reduction modulo $c\,\mathcal O_L$ maps
$U_L$ to the units of the finite ring $\mathcal O_L/c\mathcal O_L$, with kernel inside $V$.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The ring of integers of a finite intermediate field is finite over `𝒪[K]`. -/
theorem integers_moduleFinite (L : IntermediateField K Ω) [FiniteDimensional K L] :
    Module.Finite 𝒪[K] (integers L) := by
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have : Algebra.IsSeparable K L := inferInstance
  exact IsIntegralClosure.finite 𝒪[K] K L (integers L)

/-- The reduction quotient `𝒪_L / c𝒪_L` is finite for nonzero `c ∈ 𝒪[K]`. -/
theorem finite_integers_quotient (L : IntermediateField K Ω) [FiniteDimensional K L]
    (c : 𝒪[K]) (hc : c ≠ 0) :
    Finite (integers L ⧸ Ideal.span {algebraMap 𝒪[K] (integers L) c}) := by
  have := integers_moduleFinite L
  have hJ : Ideal.span {c} ≠ ⊥ := by simpa using hc
  have : Finite (𝒪[K] ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient hJ
  have : Finite (integers L ⧸ (Ideal.span {c}) • (⊤ : Submodule 𝒪[K] (integers L))) :=
    Submodule.finite_quotient_smul (Ideal.span {c}) (Module.finite_def.1 inferInstance)
  have hle : (Ideal.span {c}) • (⊤ : Submodule 𝒪[K] (integers L)) ≤
      (Ideal.span {algebraMap 𝒪[K] (integers L) c}).restrictScalars 𝒪[K] := by
    rw [Submodule.smul_le]
    intro r hr s _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    simp only [Submodule.restrictScalars_mem]
    rw [Ideal.mem_span_singleton']
    exact ⟨a • s, by simp [Algebra.smul_def, mul_comm, mul_left_comm]⟩
  exact Finite.of_surjective
    (Submodule.mapQ ((Ideal.span {c}) • (⊤ : Submodule 𝒪[K] (integers L)))
      ((Ideal.span {algebraMap 𝒪[K] (integers L) c}).restrictScalars 𝒪[K]) LinearMap.id hle)
    (by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨Submodule.Quotient.mk y, rfl⟩)

/-- The unit group `U_L` mapped into the units of `𝒪_L`. -/
def unitsLToUnits (L : IntermediateField K Ω) : unitsL L →* (integers L)ˣ where
  toFun u := ⟨⟨u.1, u.2.1⟩, ⟨((u.1⁻¹ : Lˣ) : L), u.2.2⟩,
    Subtype.ext (by simp), Subtype.ext (by simp)⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

variable (K Ω) in
/-- **$U_L$ is compact** (Milne, *CFT*, Ch. III, proof of Lemma 2.5, p. 104), in the form used: a subgroup
of $U_L$ containing $1 + c\mathcal O_L$ for a nonzero $c\in\mathfrak m_K$ has finite index. -/
@[kb "milne2020cft" "v4.03, Ch. III, proof of Lemma 2.5, U_L compact, p. 104"]
theorem unitsOpenFiniteIndex : UnitsOpenFiniteIndex K Ω := by
  refine ⟨fun L _ V _ ⟨c, hc0, _, hV⟩ => ?_⟩
  have := finite_integers_quotient L c hc0
  set I := Ideal.span {algebraMap 𝒪[K] (integers L) c} with hI
  let φ : unitsL L →* (integers L ⧸ I)ˣ :=
    (Units.map (Ideal.Quotient.mk I).toMonoidHom).comp (unitsLToUnits L)
  have : Finite φ.range := Finite.of_injective _ (Subtype.val_injective (p := (· ∈ φ.range)))
  have hker : φ.ker ≤ V.subgroupOf (unitsL L) := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have h1 : Ideal.Quotient.mk I (unitsLToUnits L u : integers L) = 1 := by
      have := congrArg Units.val hu
      simpa [φ] using this
    have h2 : (unitsLToUnits L u : integers L) - 1 ∈ I := by
      rw [← Ideal.Quotient.eq]; simpa using h1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
    have h3 : (u.1 : L) = 1 + algebraMap K L c * (y : L) := by
      have := congrArg (fun z : integers L => (z : L)) hy
      simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one] at this
      have e : ((algebraMap 𝒪[K] (integers L) c : integers L) : L) = algebraMap K L c := rfl
      rw [e] at this
      have e2 : ((unitsLToUnits L u : integers L) : L) = (u.1 : Lˣ) := rfl
      rw [e2] at this
      linear_combination -this
    have hne : 1 + algebraMap K L c * (y : L) ≠ 0 := by
      rw [← h3]; exact u.1.ne_zero
    have := hV (y : L) y.2 hne
    rw [Subgroup.mem_subgroupOf]
    convert this using 1
    exact Units.ext h3
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  exact Subgroup.finiteIndex_of_le hker
