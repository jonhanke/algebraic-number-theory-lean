import NumberFieldKB.WeilBNT.FunctionField.ZetaInputsProved
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The degree of the zero divisor of a separating element

For a separating element $x$ of $k/\mathbb F_q$ (`SeparatingElement`), the zeros of $x$ are the places of the
primes of the model $A_x$ over $(X)\subset\mathbb F_q[X]$, with $\operatorname{ord}_v(x)=e$ and $\deg v=f$. The
fundamental identity $\sum e f=[k:\mathbb F_q(x)]$ (Mathlib `Ideal.sum_ramification_inertia_eq_finrank`, for a
finite flat extension) therefore gives

* **`SeparatingElement.deg_zeros`**: $\deg\,(x)_0=[k:\mathbb F_q(x)]$, and
* **`SeparatingElement.deg_div`**: $\deg\operatorname{div}(x)=0$ (the poles are the zeros of $x^{-1}$, again
  separating, with $\mathbb F_q(x^{-1})=\mathbb F_q(x)$).

This is the separating case of the product formula (Weil VI.§1, text p. 97, deduced there from IV.§4 Thm. 5).
-/

open scoped Polynomial
open IsDedekindDomain IntermediateField

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace Divisor

/-- The positive part $\mathfrak a^+=\sup(\mathfrak a,0)$ of a divisor. -/
def pos (a : Divisor Fq k) : Divisor Fq k :=
  Finsupp.mapRange (fun n : ℤ => max n 0) (by simp) a

@[simp] theorem pos_apply (a : Divisor Fq k) (v : Place Fq k) : a.pos v = max (a v) 0 := rfl

theorem pos_sub_pos_neg (a : Divisor Fq k) : a.pos - (-a).pos = a := by
  ext v
  simp only [Finsupp.coe_sub, Pi.sub_apply, pos_apply, Finsupp.coe_neg, Pi.neg_apply]
  omega

theorem div_inv (u : kˣ) : div u⁻¹ = -(div u : Divisor Fq k) := by
  have h := div_mul (Fq := Fq) u⁻¹ u
  rw [inv_mul_cancel, div_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem mem_support_pos (a : Divisor Fq k) (v : Place Fq k) : v ∈ a.pos.support ↔ 0 < a v := by
  rw [Finsupp.mem_support_iff, pos_apply]
  omega

end Divisor

namespace SeparatingElement

variable (s : SeparatingElement Fq k)

/-- $x$ as a unit of $k$. -/
def unit : kˣ := Units.mk0 s.x s.x_ne_zero

@[simp] theorem coe_unit : (s.unit : k) = s.x := rfl

theorem inv_unit : s.inv.unit = s.unit⁻¹ := by
  ext
  simp [unit]

/-- The model ring $A_x$ is a finite $\mathbb F_q[X]$-module of rank $[k:\mathbb F_q(x)]$. -/
theorem model_finite_finrank :
    letI := s.polyAlgebra
    Module.Finite Fq[X] (integralClosure Fq[X] k) ∧
      Module.finrank Fq[X] (integralClosure Fq[X] k) = Module.finrank Fq⟮s.x⟯ k := by
  letI := s.polyAlgebra
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
    show Polynomial.aeval s.x p = _
    have : algebraMap Fq[X] K p = Polynomial.aeval (IntermediateField.AdjoinSimple.gen Fq s.x) p := by
      exact RatFunc.algEquivOfTranscendental_algebraMap s.x s.transcendental p
    rw [this]
    have := Polynomial.aeval_algHom_apply (K.val) (IntermediateField.AdjoinSimple.gen Fq s.x) p
    simpa using this.symm
  haveI : FiniteDimensional K k := FunctionField.finiteDimensional_of_adjoin_transcendental s.transcendental
  haveI : Algebra.IsSeparable K k := s.isSeparable
  haveI : IsFractionRing (integralClosure Fq[X] k) k := (model_aux s (fun _ => rfl)).2
  exact ⟨IsIntegralClosure.finite Fq[X] K k (integralClosure Fq[X] k),
    (IsFractionRing.finrank_eq Fq[X] K (integralClosure Fq[X] k) k).symm⟩

/-- $|\mathbb F_q[X]/(X)|=q$. -/
theorem card_quot_X : Nat.card (Fq[X] ⧸ Ideal.span {(Polynomial.X : Fq[X])}) = Nat.card Fq := by
  have e := (Polynomial.quotientSpanXSubCAlgEquiv (R := Fq) 0).toEquiv
  simp only [map_zero, sub_zero] at e
  exact Nat.card_congr e

theorem _root_.NumberFieldKB.WeilBNT.FF.Place.ord_pos_iff (v : Place Fq k) {f : k} (hf : f ≠ 0) :
    0 < v.ord f ↔ v.valuation f < 1 := by
  have hv : v.valuation f ≠ 0 := by simpa using hf
  rw [Place.ord, ← WithZero.exp_log hv]
  simp only [WithZero.log_exp, Left.neg_pos_iff]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]

/-- **$\deg(x)_0=[k:\mathbb F_q(x)]$** for a separating element $x$. -/
theorem deg_zeros : Divisor.deg (Divisor.div (Fq := Fq) s.unit).pos =(Module.finrank Fq⟮s.x⟯ k : ℤ) := by
  classical
  letI := s.polyAlgebra
  let B := integralClosure Fq[X] k
  obtain ⟨hfin, hrank⟩ := s.model_finite_finrank
  haveI : IsDedekindDomain B := (model_aux s (fun _ => rfl)).1
  haveI : IsFractionRing B k := (model_aux s (fun _ => rfl)).2
  let p : Ideal Fq[X] := Ideal.span {Polynomial.X}
  haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  have hinj : Function.Injective (algebraMap Fq[X] k) :=
    transcendental_iff_injective.mp s.transcendental
  haveI : Module.IsTorsionFree Fq[X] B := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r b hrb => ?_
    have h1 : algebraMap Fq[X] k r * (b : k) = 0 := by
      have := congrArg Subtype.val hrb
      rwa [Subalgebra.coe_smul, Algebra.smul_def] at this
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr (Subtype.ext h)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p B
  rw [hrank] at hsum
  -- the element x in B
  let xB : B := algebraMap Fq[X] B Polynomial.X
  have hxB : algebraMap B k xB = s.x := by
    show algebraMap Fq[X] k Polynomial.X = s.x
    exact Polynomial.aeval_X s.x
  have hxB0 : xB ≠ 0 := by
    intro h
    apply s.x_ne_zero
    rw [← hxB, h, map_zero]
  have hpmap : p.map (algebraMap Fq[X] B) = Ideal.span {xB} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hpmap0 : p.map (algebraMap Fq[X] B) ≠ ⊥ := by
    rw [hpmap, Ne, Ideal.span_singleton_eq_bot]
    exact hxB0
  -- the place of a prime over p
  have hne : ∀ q : p.primesOver B, q.1 ≠ ⊥ := by
    intro q hq
    apply hpmap0
    rw [eq_bot_iff]
    have := Ideal.map_le_of_le_comap (q.2.2.over).le (f := algebraMap Fq[X] B)
    rw [hq] at this
    exact this
  let P : p.primesOver B → HeightOneSpectrum B := fun q => ⟨q.1, q.2.1, hne q⟩
  let φ : p.primesOver B → Place Fq k := fun q => Place.ofHeightOneSpectrum B (P q)
  have hval : ∀ q : p.primesOver B, (φ q).valuation s.x =
      WithZero.exp (-(q.1.ramificationIdx Fq[X] : ℤ)) := by
    intro q
    show (P q).valuation k s.x = _
    rw [← hxB, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hxB0,
      Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p q.1 hpmap0, hpmap]
  have hord : ∀ q : p.primesOver B, (φ q).ord s.x = q.1.ramificationIdx Fq[X] := by
    intro q
    rw [Place.ord, hval, WithZero.log_exp, neg_neg]
  have hdeg : ∀ q : p.primesOver B, (φ q).degree = q.1.inertiaDeg Fq[X] := by
    intro q
    obtain ⟨g, hg⟩ := Place.exists_bijective_residue_ofHeightOneSpectrum (Fq := Fq) (k := k) B (P q)
    have h1 : Nat.card (B ⧸ q.1) = Nat.card Fq ^ (φ q).degree := by
      rw [← Place.card_residueField]
      exact Nat.card_congr (Equiv.ofBijective g hg)
    haveI : q.1.IsMaximal := (q.2.1).isMaximal (hne q)
    have h2 := Ideal.cardQuot_pow_inertiaDeg p q.1
    rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, card_quot_X] at h2
    have hq2 : 2 ≤ Nat.card Fq := Finite.one_lt_card
    exact Nat.pow_right_injective hq2 (h1.symm.trans (by rw [← h2]))
  rw [Divisor.deg_eq_sum, ← hsum, Nat.cast_sum]
  symm
  refine Finset.sum_bij (fun q _ => φ q) ?_ ?_ ?_ ?_
  · intro q _
    rw [Divisor.mem_support_pos, Divisor.div_apply, coe_unit, hord]
    exact_mod_cast Ideal.ramificationIdx_pos_of_isDedekindDomain q.1 hpmap0
  · intro q₁ _ q₂ _ h
    have := Place.ofHeightOneSpectrum_injective (Fq := Fq) (k := k) B h
    exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal this)
  · intro v hv
    rw [Divisor.mem_support_pos, Divisor.div_apply, coe_unit, Place.ord_pos_iff v s.x_ne_zero] at hv
    have hle : ∀ a : B, v.valuation (algebraMap B k a) ≤ 1 := fun a =>
      s.valuation_le_one_of_valuation_x_le_one v hv.le ⟨a.1, a.2⟩
    obtain ⟨Q, rfl⟩ := Place.exists_eq_ofHeightOneSpectrum B v hle
    have hxQ : xB ∈ Q.asIdeal := by
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := k)]
      convert hv using 2 <;> first | rfl | exact hxB
    have hlies : Q.asIdeal.LiesOver p := by
      constructor
      refine (hpmax.eq_of_le (Ideal.IsPrime.under Fq[X] Q.asIdeal).ne_top ?_)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hxQ
    refine ⟨⟨Q.asIdeal, Q.isPrime, hlies⟩, Finset.mem_univ _, rfl⟩
  · intro q _
    rw [Divisor.pos_apply, Divisor.div_apply, coe_unit, hord, hdeg]
    push_cast
    rw [max_eq_left (by positivity)]

/-- **The product formula for a separating element**: $\deg\operatorname{div}(x)=0$. -/
theorem deg_div : Divisor.deg (Divisor.div (Fq := Fq) s.unit) = 0 := by
  have h1 := s.deg_zeros
  have h2 := s.inv.deg_zeros
  rw [inv_unit, Divisor.div_inv] at h2
  have e : Module.finrank Fq⟮s.inv.x⟯ k = Module.finrank Fq⟮s.x⟯ k := by
    rw [inv_x, adjoin_inv_eq]
  rw [e] at h2
  rw [← Divisor.pos_sub_pos_neg (Divisor.div s.unit), map_sub, h1, h2, sub_self]

end SeparatingElement

end NumberFieldKB.WeilBNT.FF
