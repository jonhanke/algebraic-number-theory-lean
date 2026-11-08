import NumberFieldKB.WeilBNT.FunctionField.Place
import Mathlib.NumberTheory.FunctionField
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.Integral

/-!
# Separating elements and Dedekind models of a global function field (Weil III.§2 Lemma 1)

$k$ is a global function field over the finite field $\mathbb F_q$: Mathlib's `FunctionField Fq k` ($k$ finite over
$\mathbb F_q(T)$, `RatFunc Fq`), with compatible $\mathbb F_q$-algebra structure.

* **`SeparatingElement Fq k`**: an element $x\in k$ transcendental over $\mathbb F_q$ with $k/\mathbb F_q(x)$
  separable (bundled so that instances on its model ring can be stated).
* **`weil_III_2_lemma1`** (Weil III.§2 Lemma 1, characteristic $p$): such an element exists, i.e. $k$ is a separable
  extension of a rational function field $\mathbb F_q(x)$. Proof: Mathlib's separating transcendence basis over a
  perfect field (`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`), which has one element since $k$ is
  algebraic over $\mathbb F_q(T)$. (Weil states it over $\mathbb F_p$; with $\mathbb F_q=\mathbb F_p$ it is his
  statement, and $\mathbb F_q(x)/\mathbb F_p(x)$ is separable.)
* **`SeparatingElement.inv`**: $x^{-1}$ is again separating.
* **`SeparatingElement.modelRing`**: the integral closure $A_x$ of $\mathbb F_q[x]$ in $k$; it is a Dedekind domain
  with fraction field $k$ (`instIsDedekindDomain`, `instIsFractionRing`), and every place with $v(x)\le1$ contains it
  (`valuation_le_one_of_valuation_x_le_one`).
-/

open scoped Polynomial nonZeroDivisors
open IntermediateField

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable (Fq k : Type*) [Field Fq] [Field k] [Algebra Fq k]

/-- **A separating element** of $k/\mathbb F_q$: transcendental, with $k/\mathbb F_q(x)$ separable. -/
structure SeparatingElement where
  /-- The element $x$. -/
  x : k
  transcendental : Transcendental Fq x
  isSeparable : Algebra.IsSeparable Fq⟮x⟯ k

variable {Fq k}

/-- **Weil III.§2 Lemma 1** (function fields): a global function field is separable over a rational subfield
$\mathbb F_q(x)$. -/
@[kb "weil1973bnt" "Ch. III, §2, Lemma 1 (p. 48)"]
theorem weil_III_2_lemma1 [Finite Fq] [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k]
    [FunctionField Fq k] : Nonempty (SeparatingElement Fq k) := by
  have h2 : Algebra.EssFiniteType Fq[X] (RatFunc Fq) :=
    Algebra.EssFiniteType.of_isLocalization (S := RatFunc Fq) (nonZeroDivisors Fq[X])
  have : Algebra.EssFiniteType Fq (RatFunc Fq) := Algebra.EssFiniteType.comp Fq Fq[X] (RatFunc Fq)
  have : Algebra.EssFiniteType Fq k := Algebra.EssFiniteType.comp Fq (RatFunc Fq) k
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField Fq k
  set x0 : k := algebraMap (RatFunc Fq) k RatFunc.X with hx0
  have htr : Transcendental Fq x0 :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc Fq) k).injective).2
      (RatFunc.transcendental_X (K := Fq))
  have hind : AlgebraicIndependent Fq (fun _ : PUnit.{u_2 + 1} => x0) :=
    algebraicIndependent_unique_type_iff.2 htr
  have hb : IsTranscendenceBasis Fq (fun _ : PUnit.{u_2 + 1} => x0) := by
    rw [hind.isTranscendenceBasis_iff_isAlgebraic]
    have h1 : Algebra.IsAlgebraic Fq⟮x0⟯ k := FunctionField.Algebra.IsAlgebraic.adjoin_algebraMap_X
    rw [Set.range_const, ← IntermediateField.isAlgebraic_adjoin_iff_top]
    exact h1
  have hcard : Cardinal.mk s = Cardinal.mk PUnit.{u_2 + 1} := hs.cardinalMk_eq hb
  have h1 : s.card = 1 := by simpa using hcard
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h1
  refine ⟨⟨x, ?_, ?_⟩⟩
  · exact hs.1.transcendental ⟨x, by simp⟩
  · rw [Finset.coe_singleton] at hsep
    exact hsep

theorem adjoin_inv_le (y : k) : Fq⟮y⁻¹⟯ ≤ Fq⟮y⟯ := by
  rw [IntermediateField.adjoin_simple_le_iff]
  exact inv_mem (IntermediateField.mem_adjoin_simple_self Fq y)

theorem adjoin_inv_eq (y : k) : Fq⟮y⁻¹⟯ = Fq⟮y⟯ := by
  refine le_antisymm (adjoin_inv_le y) ?_
  simpa using adjoin_inv_le (Fq := Fq) y⁻¹

theorem isSeparable_of_eq {E F : IntermediateField Fq k} (h : E = F) (hE : Algebra.IsSeparable E k) :
    Algebra.IsSeparable F k := by
  subst h; exact hE

namespace SeparatingElement

variable (s : SeparatingElement Fq k)

theorem x_ne_zero : s.x ≠ 0 := by
  intro h
  apply s.transcendental
  rw [h]
  exact isAlgebraic_zero

/-- $x^{-1}$ is separating when $x$ is. -/
def inv : SeparatingElement Fq k where
  x := s.x⁻¹
  transcendental := fun h => s.transcendental (by simpa using h.inv)
  isSeparable := isSeparable_of_eq (adjoin_inv_eq s.x).symm s.isSeparable

@[simp] theorem inv_x : s.inv.x = s.x⁻¹ := rfl

/-- The $\mathbb F_q[X]$-algebra structure on $k$ with $X\mapsto x$ (not an instance). -/
def polyAlgebra : Algebra Fq[X] k := (Polynomial.aeval s.x).toRingHom.toAlgebra

/-- **The model ring $A_x$**: the integral closure of $\mathbb F_q[x]$ in $k$. -/
def modelRing : Subring k :=
  @Subalgebra.toSubring _ _ _ _ s.polyAlgebra (@integralClosure Fq[X] k _ _ s.polyAlgebra)

theorem x_mem_modelRing : s.x ∈ s.modelRing := by
  let _ := s.polyAlgebra
  have h : IsIntegral Fq[X] (algebraMap Fq[X] k Polynomial.X) := isIntegral_algebraMap
  have e : algebraMap Fq[X] k Polynomial.X = s.x := Polynomial.aeval_X s.x
  rw [e] at h
  exact h

theorem algebraMap_mem_modelRing (c : Fq) : algebraMap Fq k c ∈ s.modelRing := by
  let _ := s.polyAlgebra
  have h : IsIntegral Fq[X] (algebraMap Fq[X] k (Polynomial.C c)) := isIntegral_algebraMap
  have e : algebraMap Fq[X] k (Polynomial.C c) = algebraMap Fq k c := by
    rw [show algebraMap Fq[X] k (Polynomial.C c) = Polynomial.aeval s.x (Polynomial.C c) from rfl]
    exact Polynomial.aeval_C _ _
  rw [e] at h
  exact h

variable [Finite Fq] [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

theorem model_aux [inst : Algebra Fq[X] k] (h : ∀ p, algebraMap Fq[X] k p = Polynomial.aeval s.x p) :
    IsDedekindDomain (integralClosure Fq[X] k) ∧ IsFractionRing (integralClosure Fq[X] k) k := by
  let K := Fq⟮s.x⟯
  let e : RatFunc Fq ≃ₐ[Fq] K := RatFunc.algEquivOfTranscendental s.x s.transcendental
  letI : Algebra Fq[X] K :=
    (e.toRingEquiv.toRingHom.comp (algebraMap Fq[X] (RatFunc Fq))).toAlgebra
  haveI : IsFractionRing Fq[X] K :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors Fq[X])
      (AlgEquiv.ofRingEquiv (R := Fq[X]) (A₁ := RatFunc Fq) (A₂ := K) (f := e.toRingEquiv)
        (fun r => rfl))
  haveI : IsScalarTower Fq[X] K k := by
    refine IsScalarTower.of_algebraMap_eq fun p => ?_
    rw [h]
    have : algebraMap Fq[X] K p = Polynomial.aeval (IntermediateField.AdjoinSimple.gen Fq s.x) p := by
      exact RatFunc.algEquivOfTranscendental_algebraMap s.x s.transcendental p
    rw [this]
    have := Polynomial.aeval_algHom_apply (K.val) (IntermediateField.AdjoinSimple.gen Fq s.x) p
    simpa using this.symm
  haveI : FiniteDimensional K k := FunctionField.finiteDimensional_of_adjoin_transcendental s.transcendental
  haveI := s.isSeparable
  exact ⟨IsIntegralClosure.isDedekindDomain Fq[X] K k (integralClosure Fq[X] k),
    IsIntegralClosure.isFractionRing_of_finite_extension Fq[X] K k (integralClosure Fq[X] k)⟩

instance instIsDedekindDomain : IsDedekindDomain s.modelRing :=
  (model_aux s (inst := s.polyAlgebra) fun _ => rfl).1

instance instIsFractionRing : IsFractionRing s.modelRing k :=
  (model_aux s (inst := s.polyAlgebra) fun _ => rfl).2

/-- Every place with $v(x)\le1$ contains the model ring $A_x$. -/
theorem valuation_le_one_of_valuation_x_le_one (v : Place Fq k) (hv : v.valuation s.x ≤ 1)
    (a : s.modelRing) : v.valuation (a : k) ≤ 1 := by
  have hc : ∀ c : Fq, v.valuation (algebraMap Fq k c) ≤ 1 := fun c =>
    (Place.mem_integers_iff v).1 (v.algebraMap_mem_integers c)
  let g : Fq →+* v.valuation.integer :=
    { toFun := fun c => ⟨algebraMap Fq k c, hc c⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let φ : Fq[X] →+* v.valuation.integer :=
    Polynomial.eval₂RingHom g ⟨s.x, hv⟩
  have hφ : (algebraMap v.valuation.integer k).comp φ = (Polynomial.aeval s.x).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp [φ, g]; rfl
    · simp [φ]; rfl
  have ha : @IsIntegral Fq[X] k _ _ s.polyAlgebra (a : k) := a.2
  obtain ⟨f, hf, hfa⟩ := ha
  have hint : IsIntegral v.valuation.integer (a : k) := by
    refine ⟨f.map φ, hf.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hφ]
    exact hfa
  exact (Valuation.integer.integers v.valuation).mem_of_integral hint

end SeparatingElement

end NumberFieldKB.WeilBNT.FF
