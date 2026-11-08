import NumberFieldKB.WeilBNT.FunctionField.FundamentalIdentity
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The product formula for a global function field (Weil VI.§1, text p. 97)

**`Divisor.deg_div_eq_zero`**: for every $\xi\in k^\times$, $\deg\operatorname{div}(\xi)=0$. In Weil this is the
product formula $\prod_v|\xi|_v=1$ (IV.§4 Thm. 5) read through $|\xi|_v=q^{-\deg(v)\operatorname{ord}_v\xi}$.

Route. `FundamentalIdentity.lean` proves it for separating elements. Any $\xi$ is a quotient of separating elements:
with $d$ the universal derivation of $k/\mathbb F_q$ (Kähler differentials),

* `kaehler_eq_span`: $\Omega_{k/\mathbb F_q}=k\,dx$ for a separating $x$ (since $\Omega_{k/\mathbb F_q(x)}=0$ and
  $d\,\mathbb F_q(x)\subset k\,dx$), and $dx\neq0$ (else $k/\mathbb F_q$ would be unramified, hence algebraic);
* `separatingElement_of_D_ne_zero`: if $dz\ne0$ then $z$ is separating ($z$ is transcendental since $d$ kills separable
  algebraic elements, and $\Omega_{k/\mathbb F_q(z)}=\Omega_{k/\mathbb F_q}/k\,dz=0$);
* so if $d\xi=0$ then $d(x\xi)=\xi\,dx\neq0$ and $x\xi$ is separating: $\xi=(x\xi)/x$.
-/

open scoped Polynomial
open IntermediateField KaehlerDifferential

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

/-- $k$ is essentially of finite type over $\mathbb F_q$. -/
theorem essFiniteType_ff : Algebra.EssFiniteType Fq k := by
  have h2 : Algebra.EssFiniteType Fq[X] (RatFunc Fq) :=
    Algebra.EssFiniteType.of_isLocalization (S := RatFunc Fq) (nonZeroDivisors Fq[X])
  have : Algebra.EssFiniteType Fq (RatFunc Fq) := Algebra.EssFiniteType.comp Fq Fq[X] (RatFunc Fq)
  exact Algebra.EssFiniteType.comp Fq (RatFunc Fq) k

namespace SeparatingElement

variable (s : SeparatingElement Fq k)

/-- The elements $a$ with $da\in k\,dx$ form an intermediate field containing $x$. -/
def dSpanField : IntermediateField Fq k where
  carrier := {a | D Fq k a ∈ Submodule.span k {D Fq k s.x}}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Derivation.leibniz] at *
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact add_mem ha hb
  algebraMap_mem' := by
    intro c
    simp only [Set.mem_setOf_eq, Derivation.map_algebraMap]
    exact zero_mem _
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Derivation.leibniz_inv] at *
    exact Submodule.smul_mem _ _ ha

theorem adjoin_le_dSpanField : Fq⟮s.x⟯ ≤ s.dSpanField := by
  rw [adjoin_simple_le_iff]
  exact Submodule.subset_span rfl

/-- **$\Omega_{k/\mathbb F_q}=k\,dx$** for a separating element $x$. -/
theorem kaehler_eq_span : Submodule.span k {D Fq k s.x} = ⊤ := by
  let K := Fq⟮s.x⟯
  haveI : FiniteDimensional K k := FunctionField.finiteDimensional_of_adjoin_transcendental s.transcendental
  haveI : Algebra.IsSeparable K k := s.isSeparable
  haveI : Algebra.FormallyUnramified K k := Algebra.FormallyUnramified.of_isSeparable K k
  rw [eq_top_iff]
  rintro ω -
  have hker : ω ∈ LinearMap.ker (KaehlerDifferential.map Fq K k k) := by
    rw [LinearMap.mem_ker]
    exact Subsingleton.elim _ _
  rw [← KaehlerDifferential.range_mapBaseChange] at hker
  obtain ⟨t, rfl⟩ := hker
  induction t with
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul b y =>
    rw [KaehlerDifferential.mapBaseChange_tmul]
    refine Submodule.smul_mem _ b ?_
    have hy : y ∈ Submodule.span K (Set.range (D Fq K)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [KaehlerDifferential.map_D]
      exact s.adjoin_le_dSpanField a.2
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul]
      have : c • (KaehlerDifferential.map Fq Fq K k) y = (algebraMap K k c) • (KaehlerDifferential.map Fq Fq K k) y :=
        (algebraMap_smul k c _).symm
      rw [this]
      exact Submodule.smul_mem _ _ hy

/-- $dx\neq0$: otherwise $\Omega_{k/\mathbb F_q}=0$, $k/\mathbb F_q$ would be unramified and so algebraic. -/
theorem D_x_ne_zero : D Fq k s.x ≠ 0 := by
  intro h0
  have hsub : Subsingleton (Ω[k⁄Fq]) := by
    refine ⟨fun a b => ?_⟩
    have h := s.kaehler_eq_span
    rw [h0, Submodule.span_singleton_eq_bot.mpr rfl] at h
    have ha : a ∈ (⊥ : Submodule k Ω[k⁄Fq]) := h ▸ Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule k Ω[k⁄Fq]) := h ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  haveI := essFiniteType_ff (Fq := Fq) (k := k)
  haveI : Algebra.FormallyUnramified Fq k := ⟨hsub⟩
  have hsep : Algebra.IsSeparable Fq k := Algebra.FormallyUnramified.isSeparable Fq k
  exact s.transcendental (Algebra.IsSeparable.isAlgebraic Fq k |>.isAlgebraic s.x)

include s in
/-- **An element with $dz\neq0$ is separating.** -/
def ofDNeZero (z : k) (hz : D Fq k z ≠ 0) : SeparatingElement Fq k where
  x := z
  transcendental := by
    intro halg
    have hint : IsIntegral Fq z := halg.isIntegral
    have hsep : (minpoly Fq z).Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hint)
    have h := (D Fq k).map_aeval (minpoly Fq z) z
    rw [minpoly.aeval, map_zero] at h
    exact hz ((smul_eq_zero.mp h.symm).resolve_left (hsep.aeval_derivative_ne_zero (minpoly.aeval Fq z)))
  isSeparable := by
    have htr : Transcendental Fq z := by
      intro halg
      have hint : IsIntegral Fq z := halg.isIntegral
      have hsep : (minpoly Fq z).Separable :=
        PerfectField.separable_of_irreducible (minpoly.irreducible hint)
      have h := (D Fq k).map_aeval (minpoly Fq z) z
      rw [minpoly.aeval, map_zero] at h
      exact hz ((smul_eq_zero.mp h.symm).resolve_left (hsep.aeval_derivative_ne_zero (minpoly.aeval Fq z)))
    let L := Fq⟮z⟯
    haveI : FiniteDimensional L k := FunctionField.finiteDimensional_of_adjoin_transcendental htr
    haveI : Algebra.FormallyUnramified L k := by
      refine ⟨⟨fun a b => ?_⟩⟩
      suffices h : ∀ c : Ω[k⁄L], c = 0 by rw [h a, h b]
      intro c
      obtain ⟨ω, rfl⟩ := KaehlerDifferential.map_surjective Fq L k c
      -- ω is a multiple of dz
      have hspan : Submodule.span k {D Fq k z} = ⊤ := by
        have hmem : D Fq k z ∈ Submodule.span k {D Fq k s.x} := by
          rw [s.kaehler_eq_span]; trivial
        obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
        have ht0 : t ≠ 0 := by
          rintro rfl
          exact hz (by rw [← ht, zero_smul])
        rw [eq_top_iff, ← s.kaehler_eq_span, Submodule.span_le, Set.singleton_subset_iff]
        refine Submodule.mem_span_singleton.mpr ⟨t⁻¹, ?_⟩
        rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      have hmem : ω ∈ Submodule.span k {D Fq k z} := by rw [hspan]; trivial
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hmem
      rw [map_smul, KaehlerDifferential.map_D]
      have : D L k (algebraMap k k z) = 0 := by
        have hz' : algebraMap k k z = algebraMap L k (AdjoinSimple.gen Fq z) := rfl
        rw [hz', Derivation.map_algebraMap]
      rw [this, smul_zero]
    exact Algebra.FormallyUnramified.isSeparable L k

@[simp] theorem ofDNeZero_x (z : k) (hz : D Fq k z ≠ 0) : (ofDNeZero s z hz).x = z := rfl

end SeparatingElement

namespace Divisor

/-- **The product formula** (Weil VI.§1, text p. 97, from IV.§4 Thm. 5): principal divisors have degree $0$. -/
@[kb "weil1973bnt" "Ch. VI, text p.97 (deg div ξ = 0, the product formula), function fields"]
theorem deg_div_eq_zero (f : kˣ) : deg (div f : Divisor Fq k) = 0 := by
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k)
  by_cases hf : D Fq k (f : k) = 0
  · have hxf : D Fq k (s.x * f) ≠ 0 := by
      rw [Derivation.leibniz, hf, smul_zero, zero_add]
      intro h
      exact s.D_x_ne_zero ((smul_eq_zero.mp h).resolve_left f.ne_zero)
    let t := s.ofDNeZero (s.x * f) hxf
    have ht : t.unit = s.unit * f := by ext; simp [t, SeparatingElement.unit]
    have h1 := t.deg_div
    rw [ht, div_mul, map_add, s.deg_div, zero_add] at h1
    exact h1
  · exact (s.ofDNeZero (f : k) hf).deg_div

end Divisor

end NumberFieldKB.WeilBNT.FF
