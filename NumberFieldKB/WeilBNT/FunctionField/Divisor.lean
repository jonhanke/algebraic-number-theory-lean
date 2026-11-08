import NumberFieldKB.WeilBNT.FunctionField.PlaceDedekind
import NumberFieldKB.WeilBNT.FunctionField.Separating
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# All places of a global function field: finiteness, residue fields, divisors (Weil III.§1, VI.§1)

$k$ is a global function field over the finite field $\mathbb F_q$ (`FunctionField Fq k`). Every result here is
about *all* places of $k$ (`Place Fq k`), independent of any model; the proofs choose a separating element $x$
(`weil_III_2_lemma1`) and use the two Dedekind models $A_x$, $A_{x^{-1}}$: every place contains one of them.

* **`Place.exists_model`**: every place is the place of a nonzero prime of $A_x$ or of $A_{x^{-1}}$.
* **`weil_III_1_thm3_ff`** (III.§1 Thm. 3, function fields): for $\xi\ne0$, $|\xi|_v=1$ for almost all places $v$
  (Weil states $|\xi|_v\le1$; equality follows by applying it to $\xi^{-1}$).
* **`Place.nonempty`**: $k$ has a place.
* **`Place.residueField`** $\kappa(v)=\mathfrak r_v/\mathfrak p_v$, an $\mathbb F_q$-algebra, finite
  (**`Place.finite_residueField`**); **`Place.degree`** $\deg v=[\kappa(v):\mathbb F_q]\ge1$ and
  **`Place.card_residueField`** $q_v=|\kappa(v)|=q^{\deg v}$ (Weil VI.§1, p. 96, with $q=|\mathbb F_q|$; Weil takes
  $\mathbb F_q$ to be the full field of constants, which changes no statement here).
* **`Divisor Fq k`** $=\bigoplus_v\mathbb Z\,v$ (finitely supported functions on places), with Weil's order
  $\mathfrak a\succ\mathfrak b$ (`≤` of `Finsupp`, reversed), **`Divisor.deg`** $\deg\mathfrak a=\sum a(v)\deg v$, a
  homomorphism to $\mathbb Z$, nonzero (**`Divisor.deg_ne_zero`**); **`Divisor.div`** $\operatorname{div}(\xi)
  =\sum_v\operatorname{ord}_v(\xi)\,v$ for $\xi\in k^\times$, a homomorphism `kˣ →* Additive Divisor`.
-/

open scoped WithZero Polynomial
open Valuation IsDedekindDomain

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace Place

/-- Every place contains one of the two models $A_x$, $A_{x^{-1}}$ and is the place of a nonzero prime there. -/
theorem exists_model (s : SeparatingElement Fq k) (v : Place Fq k) :
    (∃ p : HeightOneSpectrum s.modelRing, v = ofHeightOneSpectrum s.modelRing p) ∨
      (∃ p : HeightOneSpectrum s.inv.modelRing, v = ofHeightOneSpectrum s.inv.modelRing p) := by
  rcases le_total (v.valuation s.x) 1 with h | h
  · left
    exact exists_eq_ofHeightOneSpectrum _ v (fun a =>
      s.valuation_le_one_of_valuation_x_le_one v h a)
  · right
    have h' : v.valuation s.inv.x ≤ 1 := by
      rw [SeparatingElement.inv_x, map_inv₀]
      exact inv_le_one_of_one_le₀ h
    exact exists_eq_ofHeightOneSpectrum _ v (fun a =>
      s.inv.valuation_le_one_of_valuation_x_le_one v h' a)

/-- **Weil III.§1 Thm. 3** (function fields): a nonzero element has $|\xi|_v=1$ at almost all places. -/
@[kb "weil1973bnt" "Ch. III, §1, Thm. 3 (p. 47), function field case"]
theorem weil_III_1_thm3_ff {f : k} (hf : f ≠ 0) : {v : Place Fq k | v.valuation f ≠ 1}.Finite := by
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k)
  refine ((finite_setOf_valuation_ne_one_of_le_one s.modelRing hf).union
    (finite_setOf_valuation_ne_one_of_le_one s.inv.modelRing hf)).subset ?_
  intro v hv
  rcases exists_model s v with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ⟨fun a => valuation_ofHeightOneSpectrum_algebraMap_le_one _ p a, hv⟩
  · exact Or.inr ⟨fun a => valuation_ofHeightOneSpectrum_algebraMap_le_one _ p a, hv⟩

theorem nonempty : Nonempty (Place Fq k) := by
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k)
  have hnf : ¬ IsField s.modelRing := by
    letI := s.polyAlgebra
    have key : ¬ IsField (integralClosure Fq[X] k) := by
      intro h
      refine Polynomial.not_isField Fq (isField_of_isIntegral_of_isField ?_ h)
      intro a b hab
      have : Polynomial.aeval s.x a = Polynomial.aeval s.x b := congrArg Subtype.val hab
      have hinj : Function.Injective (Polynomial.aeval (R := Fq) s.x) :=
        transcendental_iff_injective.mp s.transcendental
      exact hinj this
    exact key
  obtain ⟨M, hM⟩ := Ideal.exists_maximal s.modelRing
  have hne : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM hnf
  exact ⟨ofHeightOneSpectrum s.modelRing ⟨M, hM.isPrime, hne⟩⟩

variable (v : Place Fq k)

/-- $\mathbb F_q\to\mathfrak r_v$. -/
instance : Algebra Fq v.integers :=
  ((algebraMap Fq k).codRestrict v.integers.toSubring v.algebraMap_mem_integers).toAlgebra

/-- The residue field $\kappa(v)=\mathfrak r_v/\mathfrak p_v$. -/
abbrev residueField : Type _ := IsLocalRing.ResidueField v.integers

theorem mem_maximalIdeal_of_valuation_lt_one (w : Place Fq k) (z : w.integers)
    (h : w.valuation (z : k) < 1) : z ∈ IsLocalRing.maximalIdeal w.integers := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, rfl⟩
  have h1 : ((u : w.integers) : k) * (((u⁻¹ : w.integers ˣ) : w.integers) : k) = 1 := by
    exact congrArg Subtype.val u.mul_inv
  have h2 : w.valuation (((u⁻¹ : w.integers ˣ) : w.integers) : k) ≤ 1 :=
    ((u⁻¹ : w.integers ˣ) : w.integers).2
  have h3 : w.valuation ((u : w.integers) : k) * w.valuation (((u⁻¹ : w.integers ˣ) : w.integers) : k) ≤
      w.valuation ((u : w.integers) : k) := mul_le_of_le_one_right' h2
  rw [← map_mul, h1, map_one] at h3
  exact absurd (lt_of_le_of_lt h3 h) (lt_irrefl _)

/-- Helper: for a nonzero prime $\mathfrak p$ of a Dedekind model $A$, the residue field of its place is
$A/\mathfrak p$: there is a bijective ring map $A/\mathfrak p\to\kappa(v_{\mathfrak p})$. -/
theorem exists_bijective_residue_ofHeightOneSpectrum (A : Type*) [CommRing A] [IsDedekindDomain A]
    [Algebra A k] [IsFractionRing A k] (p : HeightOneSpectrum A) :
    ∃ φ : A ⧸ p.asIdeal →+* (ofHeightOneSpectrum (Fq := Fq) (k := k) A p).residueField,
      Function.Bijective φ := by
  set w : Place Fq k := ofHeightOneSpectrum (Fq := Fq) (k := k) A p with hw
  have hle : ∀ a : A, w.valuation (algebraMap A k a) ≤ 1 := fun a =>
    valuation_ofHeightOneSpectrum_algebraMap_le_one A p a
  let φ : A →+* w.integers := (algebraMap A k).codRestrict w.integers.toSubring (fun a => hle a)
  let ψ : A →+* w.residueField := (IsLocalRing.residue w.integers).comp φ
  have hlt : ∀ a : A, w.valuation (algebraMap A k a) < 1 ↔ a ∈ p.asIdeal := fun a =>
    HeightOneSpectrum.valuation_lt_one_iff_mem p a
  have hker : p.asIdeal ≤ RingHom.ker ψ := by
    intro a ha
    rw [RingHom.mem_ker]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr
      (mem_maximalIdeal_of_valuation_lt_one w (φ a) ((hlt a).mpr ha))
  have hmax : p.asIdeal.IsMaximal := p.isPrime.isMaximal p.ne_bot
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    have hr : (r : k) ∈ (p.valuation k).valuationSubring := r.2
    rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hr
    obtain ⟨a, s, hs, hx⟩ := hr
    have hs0 : algebraMap A k s ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := (IsFractionRing.injective A k) (by simpa using h0)
      rw [this]
      exact zero_mem _
    obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv (x := s) hs
    have hs1 : w.valuation (algebraMap A k s) = 1 :=
      le_antisymm (hle s) (not_lt.mp fun h => hs ((hlt s).mp h))
    refine ⟨a * y, ?_⟩
    show IsLocalRing.residue w.integers (φ (a * y)) = IsLocalRing.residue w.integers r
    rw [← sub_eq_zero, ← _root_.map_sub]
    refine (IsLocalRing.residue_eq_zero_iff _).mpr (mem_maximalIdeal_of_valuation_lt_one w _ ?_)
    have hI : algebraMap A k i = 1 - algebraMap A k y * algebraMap A k s := by
      have := congrArg (algebraMap A k) hyi
      simp only [map_add, map_mul, map_one] at this
      linear_combination this
    have hval : (((φ (a * y) - r : w.integers)) : k) =
        -(algebraMap A k a * (algebraMap A k s)⁻¹ * algebraMap A k i) := by
      show algebraMap A k (a * y) - (r : k) = _
      rw [hx, hI, map_mul]
      field_simp
      ring
    rw [hval, Valuation.map_neg, map_mul, map_mul, map_inv₀, hs1, inv_one, mul_one]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) ((hlt i).mpr hi)
  letI : Field (A ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  refine ⟨Ideal.Quotient.lift p.asIdeal ψ (fun a ha => hker ha),
    RingHom.injective _, fun y => ?_⟩
  obtain ⟨a, ha⟩ := hsurj y
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

/-- Helper: the residue field of the place of a nonzero prime $\mathfrak p$ of a model $A$ is finite as soon
as $A/\mathfrak p$ is (it is a quotient of $A/\mathfrak p$). -/
theorem finite_residueField_ofHeightOneSpectrum (A : Type*) [CommRing A] [IsDedekindDomain A]
    [Algebra A k] [IsFractionRing A k] (p : HeightOneSpectrum A) [Finite (A ⧸ p.asIdeal)] :
    Finite (ofHeightOneSpectrum (Fq := Fq) (k := k) A p).residueField := by
  set w : Place Fq k := ofHeightOneSpectrum (Fq := Fq) (k := k) A p with hw
  have hle : ∀ a : A, w.valuation (algebraMap A k a) ≤ 1 := fun a =>
    valuation_ofHeightOneSpectrum_algebraMap_le_one A p a
  let φ : A →+* w.integers := (algebraMap A k).codRestrict w.integers.toSubring (fun a => hle a)
  let ψ : A →+* w.residueField := (IsLocalRing.residue w.integers).comp φ
  have hlt : ∀ a : A, w.valuation (algebraMap A k a) < 1 ↔ a ∈ p.asIdeal := fun a =>
    HeightOneSpectrum.valuation_lt_one_iff_mem p a
  have hker : p.asIdeal ≤ RingHom.ker ψ := by
    intro a ha
    rw [RingHom.mem_ker]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr
      (mem_maximalIdeal_of_valuation_lt_one w (φ a) ((hlt a).mpr ha))
  have hmax : p.asIdeal.IsMaximal := p.isPrime.isMaximal p.ne_bot
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    have hr : (r : k) ∈ (p.valuation k).valuationSubring := r.2
    rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hr
    obtain ⟨a, s, hs, hx⟩ := hr
    have hs0 : algebraMap A k s ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := (IsFractionRing.injective A k) (by simpa using h0)
      rw [this]
      exact zero_mem _
    obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv (x := s) hs
    have hs1 : w.valuation (algebraMap A k s) = 1 :=
      le_antisymm (hle s) (not_lt.mp fun h => hs ((hlt s).mp h))
    refine ⟨a * y, ?_⟩
    show IsLocalRing.residue w.integers (φ (a * y)) = IsLocalRing.residue w.integers r
    rw [← sub_eq_zero, ← _root_.map_sub]
    refine (IsLocalRing.residue_eq_zero_iff _).mpr (mem_maximalIdeal_of_valuation_lt_one w _ ?_)
    have hI : algebraMap A k i = 1 - algebraMap A k y * algebraMap A k s := by
      have := congrArg (algebraMap A k) hyi
      simp only [map_add, map_mul, map_one] at this
      linear_combination this
    have hval : (((φ (a * y) - r : w.integers)) : k) =
        -(algebraMap A k a * (algebraMap A k s)⁻¹ * algebraMap A k i) := by
      show algebraMap A k (a * y) - (r : k) = _
      rw [hx, hI, map_mul]
      field_simp
      ring
    rw [hval, Valuation.map_neg, map_mul, map_mul, map_inv₀, hs1, inv_one, mul_one]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) ((hlt i).mpr hi)
  refine Finite.of_surjective (Ideal.Quotient.lift p.asIdeal ψ (fun a ha => hker ha)) ?_
  intro y
  obtain ⟨a, ha⟩ := hsurj y
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

/-- Helper: $\mathbb F_q[X]$ has finite quotients by nonzero ideals. -/
theorem hasFiniteQuotients_polynomial : Ring.HasFiniteQuotients Fq[X] := by
  refine ⟨fun {I} hI => ?_⟩
  obtain ⟨g, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  have hg : g ≠ 0 := by
    rintro rfl
    exact hI (by simp)
  haveI : Module.Finite Fq (AdjoinRoot g) := (AdjoinRoot.powerBasis hg).finite
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite Fq
  exact this

/-- Helper: the quotient of the model ring by a nonzero prime is finite (the model ring is a finite
$\mathbb F_q[X]$-module). -/
theorem finite_quotient_model (s : SeparatingElement Fq k) (p : HeightOneSpectrum s.modelRing) :
    Finite (s.modelRing ⧸ p.asIdeal) := by
  let K := IntermediateField.adjoin Fq {s.x}
  let e : RatFunc Fq ≃ₐ[Fq] K := RatFunc.algEquivOfTranscendental s.x s.transcendental
  letI : Algebra Fq[X] K :=
    (e.toRingEquiv.toRingHom.comp (algebraMap Fq[X] (RatFunc Fq))).toAlgebra
  haveI : IsFractionRing Fq[X] K :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors Fq[X])
      (AlgEquiv.ofRingEquiv (R := Fq[X]) (A₁ := RatFunc Fq) (A₂ := K) (f := e.toRingEquiv)
        (fun r => rfl))
  letI := s.polyAlgebra
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
  haveI : Module.Finite Fq[X] (integralClosure Fq[X] k) :=
    IsIntegralClosure.finite Fq[X] K k (integralClosure Fq[X] k)
  haveI := hasFiniteQuotients_polynomial (Fq := Fq)
  have h := Ring.HasFiniteQuotients.of_module_finite Fq[X] (integralClosure Fq[X] k)
  exact h.finiteQuotient (I := p.asIdeal) p.ne_bot

/-- **The residue field of a place is finite.** -/
instance finite_residueField : Finite v.residueField := by
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k)
  rcases exists_model s v with ⟨p, hp⟩ | ⟨p, hp⟩
  · subst hp
    haveI := finite_quotient_model s p
    exact finite_residueField_ofHeightOneSpectrum s.modelRing p
  · subst hp
    haveI := finite_quotient_model s.inv p
    exact finite_residueField_ofHeightOneSpectrum s.inv.modelRing p

/-- **The degree** $\deg v=[\kappa(v):\mathbb F_q]$. -/
def degree : ℕ := Module.finrank Fq v.residueField

theorem degree_pos : 0 < v.degree := by
  haveI : Module.Finite Fq v.residueField := Module.Finite.of_finite
  exact Module.finrank_pos

/-- $q_v=|\kappa(v)|=q^{\deg v}$. -/
theorem card_residueField : Nat.card v.residueField = Nat.card Fq ^ v.degree := by
  haveI : Fintype v.residueField := Fintype.ofFinite _
  haveI : Fintype Fq := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank

end Place

variable (Fq k) in
/-- **Divisors** of $k$ (Weil VI.§1, p. 96): formal finite sums $\sum a(v)\,v$ over all places. -/
abbrev Divisor : Type _ := Place Fq k →₀ ℤ

namespace Divisor

/-- **The degree** $\deg\mathfrak a=\sum_v a(v)\deg v$, as a homomorphism to $\mathbb Z$. -/
def deg : Divisor Fq k →+ ℤ :=
  Finsupp.liftAddHom fun v => (zmultiplesHom ℤ (v.degree : ℤ))

theorem deg_single (v : Place Fq k) (n : ℤ) : deg (Finsupp.single v n) = n * v.degree := by
  simp [deg]

/-- The degree is a nontrivial morphism to $\mathbb Z$ (Weil VI.§1, p. 96). -/
@[kb "weil1973bnt" "Ch. VI, §1, text p. 96 (divisors, the degree)"]
theorem deg_ne_zero : deg (Fq := Fq) (k := k) ≠ 0 := by
  obtain ⟨v⟩ := Place.nonempty (Fq := Fq) (k := k)
  intro h
  have h1 := deg_single v 1
  rw [h] at h1
  have := v.degree_pos
  simp at h1
  omega

theorem ord_eq_zero_of_valuation_eq_one (v : Place Fq k) {f : k} (h : v.valuation f = 1) :
    v.ord f = 0 := by
  simp [Place.ord, h]

/-- **The divisor of $\xi\in k^\times$**: $\operatorname{div}(\xi)=\sum_v\operatorname{ord}_v(\xi)\,v$. -/
def div (f : kˣ) : Divisor Fq k :=
  Finsupp.ofSupportFinite (fun v => v.ord (f : k)) (by
    refine (Place.weil_III_1_thm3_ff (Fq := Fq) f.ne_zero).subset ?_
    intro v hv h1
    exact hv (ord_eq_zero_of_valuation_eq_one v h1))

@[simp] theorem div_apply (f : kˣ) (v : Place Fq k) : div f v = v.ord (f : k) := rfl

theorem div_mul (f g : kˣ) : div (f * g) = (div f + div g : Divisor Fq k) := by
  ext v
  have hf : v.valuation (f : k) ≠ 0 := by simp
  have hg : v.valuation (g : k) ≠ 0 := by simp
  simp only [div_apply, Finsupp.add_apply, Units.val_mul, Place.ord, map_mul]
  rw [WithZero.log_mul hf hg]
  ring

theorem div_one : div (1 : kˣ) = (0 : Divisor Fq k) := by
  ext v
  simp [Place.ord]

open IntermediateField in
/-- Helper: the coefficients of the minimal polynomial over $\mathbb F_q(x)$ of an element of the model ring
$A_x$ lie in $\mathbb F_q[x]$ (integral closedness of $\mathbb F_q[X]$). -/
theorem coeff_minpoly_mem (s : SeparatingElement Fq k) {f : k} (hf : f ∈ s.modelRing) (i : ℕ) :
    ∃ p : Fq[X], algebraMap Fq⟮s.x⟯ k ((minpoly Fq⟮s.x⟯ f).coeff i) = Polynomial.aeval s.x p := by
  let K := Fq⟮s.x⟯
  let e : RatFunc Fq ≃ₐ[Fq] K := RatFunc.algEquivOfTranscendental s.x s.transcendental
  letI : Algebra Fq[X] K :=
    (e.toRingEquiv.toRingHom.comp (algebraMap Fq[X] (RatFunc Fq))).toAlgebra
  haveI : IsFractionRing Fq[X] K :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors Fq[X])
      (AlgEquiv.ofRingEquiv (R := Fq[X]) (A₁ := RatFunc Fq) (A₂ := K) (f := e.toRingEquiv)
        (fun r => rfl))
  letI := s.polyAlgebra
  haveI : IsScalarTower Fq[X] K k := by
    refine IsScalarTower.of_algebraMap_eq fun p => ?_
    show Polynomial.aeval s.x p = _
    have : algebraMap Fq[X] K p = Polynomial.aeval (IntermediateField.AdjoinSimple.gen Fq s.x) p := by
      exact RatFunc.algEquivOfTranscendental_algebraMap s.x s.transcendental p
    rw [this]
    have := Polynomial.aeval_algHom_apply (K.val) (IntermediateField.AdjoinSimple.gen Fq s.x) p
    simpa using this.symm
  have hint : IsIntegral Fq[X] f := hf
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hint, Polynomial.coeff_map]
  refine ⟨(minpoly Fq[X] f).coeff i, ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  rfl

/-- Helper: a polynomial expression in $x$ equal to one in $x^{-1}$ is a constant. -/
theorem const_of_aeval_eq (s : SeparatingElement Fq k) (p q : Fq[X])
    (h : Polynomial.aeval s.x p = Polynomial.aeval s.x⁻¹ q) :
    ∃ c : Fq, Polynomial.aeval s.x p = algebraMap Fq k c := by
  have hx : s.x ≠ 0 := s.x_ne_zero
  have hinj : Function.Injective (Polynomial.aeval s.x : Fq[X] →ₐ[Fq] k) :=
    transcendental_iff_injective.mp s.transcendental
  have h1 : Polynomial.eval₂ (algebraMap Fq k) s.x q.reverse * (s.x⁻¹) ^ q.natDegree =
      Polynomial.eval₂ (algebraMap Fq k) s.x⁻¹ q := by
    letI : Invertible s.x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
    have := Polynomial.eval₂_reverse_mul_pow (algebraMap Fq k) s.x⁻¹ q
    simpa [invOf_eq_inv] using this
  have h2 : Polynomial.aeval s.x q.reverse = Polynomial.aeval s.x (Polynomial.X ^ q.natDegree * p) := by
    rw [map_mul, map_pow, Polynomial.aeval_X, h]
    have h1' : Polynomial.aeval s.x q.reverse * (s.x⁻¹) ^ q.natDegree = Polynomial.aeval s.x⁻¹ q := h1
    rw [← h1', mul_comm (Polynomial.aeval s.x q.reverse), ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hx, one_pow, one_mul]
  have h3 := hinj h2
  by_cases hp : p = 0
  · exact ⟨0, by simp [hp]⟩
  · have hdeg : q.reverse.natDegree ≤ q.natDegree := Polynomial.reverse_natDegree_le q
    rw [h3, Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hp,
      Polynomial.natDegree_X_pow] at hdeg
    have h0 : p.natDegree = 0 := by omega
    refine ⟨p.coeff 0, ?_⟩
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    simp

open IntermediateField in
/-- An element with no poles ($v(f)\le1$ at every place) is a constant (algebraic over $\mathbb F_q$). -/
theorem isAlgebraic_of_forall_valuation_le_one (f : k) (h : ∀ v : Place Fq k, v.valuation f ≤ 1) :
    IsAlgebraic Fq f := by
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k)
  have hmem : ∀ t : SeparatingElement Fq k, f ∈ t.modelRing := by
    intro t
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := k) (R := t.modelRing) f
      (fun p => h (Place.ofHeightOneSpectrum t.modelRing p))
    rw [← ha]
    exact a.2
  have hA := hmem s
  have hB := hmem s.inv
  haveI : FiniteDimensional Fq⟮s.x⟯ k :=
    FunctionField.finiteDimensional_of_adjoin_transcendental s.transcendental
  have hint : IsIntegral Fq⟮s.x⟯ f := IsIntegral.of_finite _ _
  have hE : ∀ (E F : IntermediateField Fq k), E = F → ∀ i,
      algebraMap E k ((minpoly E f).coeff i) = algebraMap F k ((minpoly F f).coeff i) := by
    rintro E F rfl i
    rfl
  have hc : ∀ i, ∃ c : Fq, algebraMap Fq⟮s.x⟯ k ((minpoly Fq⟮s.x⟯ f).coeff i) = algebraMap Fq k c := by
    intro i
    obtain ⟨p, hp⟩ := coeff_minpoly_mem s hA i
    obtain ⟨q, hq⟩ := coeff_minpoly_mem s.inv hB i
    have := hE Fq⟮s.x⟯ Fq⟮s.inv.x⟯ (adjoin_inv_eq s.x).symm i
    rw [hp, hq] at this
    obtain ⟨c, hc⟩ := const_of_aeval_eq s p q this
    exact ⟨c, by rw [hp, hc]⟩
  have hlift : (minpoly Fq⟮s.x⟯ f).map (algebraMap Fq⟮s.x⟯ k) ∈ Polynomial.lifts (algebraMap Fq k) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨c, hc⟩ := hc n
    exact ⟨c, by rw [Polynomial.coeff_map]; exact hc.symm⟩
  obtain ⟨P, hP⟩ := (Polynomial.mem_lifts _).mp hlift
  have hmonic : ((minpoly Fq⟮s.x⟯ f).map (algebraMap Fq⟮s.x⟯ k)).Monic := (minpoly.monic hint).map _
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
    rw [← hP] at hmonic
    simp at hmonic
  refine ⟨P, hP0, ?_⟩
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, hP, Polynomial.eval_map, ← Polynomial.aeval_def]
  exact minpoly.aeval _ f

/-- An element has no zeros or poles iff it is a constant (algebraic over $\mathbb F_q$). -/
theorem div_eq_zero_iff (f : kˣ) : div f = (0 : Divisor Fq k) ↔ IsAlgebraic Fq (f : k) := by
  constructor
  · intro h
    refine isAlgebraic_of_forall_valuation_le_one _ fun v => ?_
    have h0 : v.ord (f : k) = 0 := by
      simpa using congrArg (fun d : Divisor Fq k => d v) h
    have hne : v.valuation (f : k) ≠ 0 := by simp
    have : v.valuation (f : k) = 1 := by
      have h1 : WithZero.log (v.valuation (f : k)) = 0 := by
        simpa [Place.ord] using h0
      rw [← WithZero.exp_log hne, h1]
      simp
    exact this.le
  · intro h
    ext v
    by_contra hne
    have hne' : v.valuation (f : k) ≠ 1 := fun h1 =>
      hne (by simpa using ord_eq_zero_of_valuation_eq_one v h1)
    exact Valuation.transcendental_of_ne_one (v := v.valuation) Fq (f : k) f.ne_zero hne' h

end Divisor

end NumberFieldKB.WeilBNT.FF
