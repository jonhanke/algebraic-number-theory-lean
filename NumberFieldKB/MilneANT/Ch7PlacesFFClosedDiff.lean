import NumberFieldKB.MilneANT.Ch7PlacesFFClosedZeros
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Remark 7.17(b), part 2: separating elements via Kähler differentials

Over the perfect field $k$ (algebraically closed), every element $\xi\in K$ is a quotient of separating elements.
This is the Kähler differential trick of `NumberFieldKB/WeilBNT/FunctionField/ProductFormula.lean`, re-proved here
with `[Finite Fq]` replaced by `PerfectField k` (the proofs are unchanged):

* `FFClosed.Sep.kaehler_eq_span`: $\Omega_{K/k}=K\,dx$ for a separating $x$;
* `FFClosed.Sep.D_x_ne_zero`: $dx\neq0$;
* `FFClosed.Sep.ofDNeZero`: if $dz\neq0$ then $z$ is separating.
-/

open scoped Polynomial nonZeroDivisors
open IntermediateField KaehlerDifferential NumberFieldKB.WeilBNT.FF

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace NumberFieldKB.MilneANT.FFClosed

universe u v

variable {k : Type u} {K : Type v} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

/-- $K$ is essentially of finite type over $k$. -/
theorem essFiniteType_ff : Algebra.EssFiniteType k K := by
  have h2 : Algebra.EssFiniteType k[X] (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization (S := RatFunc k) (nonZeroDivisors k[X])
  have : Algebra.EssFiniteType k (RatFunc k) := Algebra.EssFiniteType.comp k k[X] (RatFunc k)
  exact Algebra.EssFiniteType.comp k (RatFunc k) K

namespace Sep

variable (s : SeparatingElement k K)

/-- The elements $a$ with $da\in K\,dx$ form an intermediate field containing $x$. -/
def dSpanField : IntermediateField k K where
  carrier := {a | D k K a ∈ Submodule.span K {D k K s.x}}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Derivation.leibniz] at *
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact add_mem ha hb
  algebraMap_mem' := by
    intro c
    simp only [Set.mem_ofPred_eq, Derivation.map_algebraMap]
    exact zero_mem _
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Derivation.leibniz_inv] at *
    exact Submodule.smul_mem _ _ ha

theorem adjoin_le_dSpanField : k⟮s.x⟯ ≤ dSpanField s := by
  rw [adjoin_simple_le_iff]
  exact Submodule.subset_span rfl

/-- **$\Omega_{K/k}=K\,dx$** for a separating element $x$. -/
theorem kaehler_eq_span : Submodule.span K {D k K s.x} = ⊤ := by
  let L := k⟮s.x⟯
  haveI : FiniteDimensional L K := FunctionField.finiteDimensional_of_adjoin_transcendental s.transcendental
  haveI : Algebra.IsSeparable L K := s.isSeparable
  haveI : Algebra.FormallyUnramified L K := Algebra.FormallyUnramified.of_isSeparable L K
  rw [eq_top_iff]
  rintro ω -
  have hker : ω ∈ LinearMap.ker (KaehlerDifferential.map k L K K) := by
    rw [LinearMap.mem_ker]
    exact Subsingleton.elim _ _
  rw [← KaehlerDifferential.range_mapBaseChange] at hker
  obtain ⟨t, rfl⟩ := hker
  induction t with
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul b y =>
    rw [KaehlerDifferential.mapBaseChange_tmul]
    refine Submodule.smul_mem _ b ?_
    have hy : y ∈ Submodule.span L (Set.range (D k L)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [KaehlerDifferential.map_D]
      exact adjoin_le_dSpanField s a.2
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul]
      have : c • (KaehlerDifferential.map k k L K) y = (algebraMap L K c) • (KaehlerDifferential.map k k L K) y :=
        (algebraMap_smul K c _).symm
      rw [this]
      exact Submodule.smul_mem _ _ hy

/-- $dx\neq0$: otherwise $\Omega_{K/k}=0$, $K/k$ would be unramified and so algebraic. -/
theorem D_x_ne_zero : D k K s.x ≠ 0 := by
  intro h0
  have hsub : Subsingleton (Ω[K⁄k]) := by
    refine ⟨fun a b => ?_⟩
    have h := kaehler_eq_span s
    rw [h0, Submodule.span_singleton_eq_bot.mpr rfl] at h
    have ha : a ∈ (⊥ : Submodule K Ω[K⁄k]) := h ▸ Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule K Ω[K⁄k]) := h ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  haveI := essFiniteType_ff (k := k) (K := K)
  haveI : Algebra.FormallyUnramified k K := ⟨hsub⟩
  have hsep : Algebra.IsSeparable k K := Algebra.FormallyUnramified.isSeparable k K
  exact s.transcendental (Algebra.IsSeparable.isAlgebraic k K |>.isAlgebraic s.x)

include s in
/-- **An element with $dz\neq0$ is separating.** -/
def ofDNeZero (z : K) (hz : D k K z ≠ 0) : SeparatingElement k K where
  x := z
  transcendental := by
    intro halg
    have hint : IsIntegral k z := halg.isIntegral
    have hsep : (minpoly k z).Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hint)
    have h := (D k K).map_aeval (minpoly k z) z
    rw [minpoly.aeval, map_zero] at h
    exact hz ((smul_eq_zero.mp h.symm).resolve_left (hsep.aeval_derivative_ne_zero (minpoly.aeval k z)))
  isSeparable := by
    have htr : Transcendental k z := by
      intro halg
      have hint : IsIntegral k z := halg.isIntegral
      have hsep : (minpoly k z).Separable :=
        PerfectField.separable_of_irreducible (minpoly.irreducible hint)
      have h := (D k K).map_aeval (minpoly k z) z
      rw [minpoly.aeval, map_zero] at h
      exact hz ((smul_eq_zero.mp h.symm).resolve_left (hsep.aeval_derivative_ne_zero (minpoly.aeval k z)))
    let L := k⟮z⟯
    haveI : FiniteDimensional L K := FunctionField.finiteDimensional_of_adjoin_transcendental htr
    haveI : Algebra.FormallyUnramified L K := by
      refine ⟨⟨fun a b => ?_⟩⟩
      suffices h : ∀ c : Ω[K⁄L], c = 0 by rw [h a, h b]
      intro c
      obtain ⟨ω, rfl⟩ := KaehlerDifferential.map_surjective k L K c
      have hspan : Submodule.span K {D k K z} = ⊤ := by
        have hmem : D k K z ∈ Submodule.span K {D k K s.x} := by
          rw [kaehler_eq_span s]; trivial
        obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
        have ht0 : t ≠ 0 := by
          rintro rfl
          exact hz (by rw [← ht, zero_smul])
        rw [eq_top_iff, ← kaehler_eq_span s, Submodule.span_le, Set.singleton_subset_iff]
        refine Submodule.mem_span_singleton.mpr ⟨t⁻¹, ?_⟩
        rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      have hmem : ω ∈ Submodule.span K {D k K z} := by rw [hspan]; trivial
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hmem
      rw [map_smul, KaehlerDifferential.map_D]
      have : D L K (algebraMap K K z) = 0 := by
        have hz' : algebraMap K K z = algebraMap L K (AdjoinSimple.gen k z) := rfl
        rw [hz', Derivation.map_algebraMap]
      rw [this, smul_zero]
    exact Algebra.FormallyUnramified.isSeparable L K

@[simp] theorem ofDNeZero_x (z : K) (hz : D k K z ≠ 0) : (ofDNeZero s z hz).x = z := rfl

end Sep

end NumberFieldKB.MilneANT.FFClosed
