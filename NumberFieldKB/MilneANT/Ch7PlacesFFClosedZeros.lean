import NumberFieldKB.MilneANT.Ch7Places
import NumberFieldKB.WeilBNT.FunctionField.PlaceDedekind
import NumberFieldKB.WeilBNT.FunctionField.Separating
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int

/-!
# Remark 7.17(b), part 1: places over an algebraically closed field and the fundamental identity

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 7.17(b), p. 112; bib key `milne2020ant`.

This file carries over the Weil-track arguments for a global function field over a finite field
(`NumberFieldKB/WeilBNT/FunctionField/{Place,PlaceDedekind,Separating,FundamentalIdentity}.lean`) to a function
field $K$ over an *algebraically closed* field $k$; the generic lemmas of those files are imported, the ones stated
under `[Finite Fq]` are re-proved here with that hypothesis removed.

* `FFClosed.exists_separating`: $K$ has a separating element (`WeilBNT.FF.SeparatingElement`).
* `FFClosed.placeOf`, `FFClosed.exists_eq_placeOf`, `FFClosed.placeOf_injective`: places of $K/k$ (surjective
  valuations trivial on $k$, `WeilBNT.FF.Place k K`) at the primes of a Dedekind model $A$ with $k^\times \subset A^\times$.
* `FFClosed.sum_max_ord`: for a separating $x$, $\sum_v \max(\operatorname{ord}_v x, 0) = [K : k(x)]$ (a finite
  sum). Proof: the places with $v(x)<1$ are the primes of the integral closure $B$ of $k[X]$ in $K$ over $(X)$, with
  $\operatorname{ord}_v x = e$, and every residue degree is $1$ because $k[X]/(X) \cong k$ is algebraically closed;
  then the fundamental identity `Ideal.sum_ramification_inertia_eq_finrank`.
-/

open scoped Polynomial nonZeroDivisors WithZero
open IsDedekindDomain IntermediateField NumberFieldKB.WeilBNT.FF

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace NumberFieldKB.MilneANT.FFClosed

universe u v

variable {k : Type u} {K : Type v} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

/-- A function field over an algebraically closed (hence perfect) field has a separating element. -/
theorem exists_separating : Nonempty (SeparatingElement k K) := by
  have h2 : Algebra.EssFiniteType k[X] (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization (S := RatFunc k) (nonZeroDivisors k[X])
  have : Algebra.EssFiniteType k (RatFunc k) := Algebra.EssFiniteType.comp k k[X] (RatFunc k)
  have : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k (RatFunc k) K
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  set x0 : K := algebraMap (RatFunc k) K RatFunc.X with hx0
  have htr : Transcendental k x0 :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc k) K).injective).2
      (RatFunc.transcendental_X (K := k))
  have hind : AlgebraicIndependent k (fun _ : PUnit.{v + 1} => x0) :=
    algebraicIndependent_unique_type_iff.2 htr
  have hb : IsTranscendenceBasis k (fun _ : PUnit.{v + 1} => x0) := by
    rw [hind.isTranscendenceBasis_iff_isAlgebraic]
    have h1 : Algebra.IsAlgebraic k⟮x0⟯ K := FunctionField.Algebra.IsAlgebraic.adjoin_algebraMap_X
    rw [Set.range_const, ← IntermediateField.isAlgebraic_adjoin_iff_top]
    exact h1
  have hcard : Cardinal.mk s = Cardinal.mk PUnit.{v + 1} := hs.cardinalMk_eq hb
  have h1 : s.card = 1 := by simpa using hcard
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h1
  refine ⟨⟨x, ?_, ?_⟩⟩
  · exact hs.1.transcendental ⟨x, by simp⟩
  · rw [Finset.coe_singleton] at hsep
    exact hsep

/-! ### Places at the primes of a Dedekind model -/

section Generic

variable (A : Type*) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
  (hA : ∀ c : k, c ≠ 0 → ∃ u : Aˣ, algebraMap A K u = algebraMap k K c)

/-- The place of $K/k$ at a nonzero prime of a Dedekind model $A$ of $K$ containing $k^\times$ as units: the adic
valuation. -/
def placeOf (p : HeightOneSpectrum A) : Place k K where
  valuation := p.valuation K
  valuation_surjective := p.valuation_surjective K
  isTrivialOn := ⟨fun c hc => by
    obtain ⟨u, hu⟩ := hA c hc
    rw [← hu, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro h
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)⟩

@[simp] theorem placeOf_valuation (p : HeightOneSpectrum A) : (placeOf A hA p).valuation = p.valuation K := rfl

theorem placeOf_injective : Function.Injective (placeOf (k := k) (K := K) A hA) := by
  intro p q h
  exact HeightOneSpectrum.valuation_injective (K := K) (congrArg Place.valuation h)

/-- Every place whose valuation ring contains the model $A$ is the place of a nonzero prime of $A$. -/
theorem exists_eq_placeOf (v : Place k K)
    (hv : ∀ a : A, v.valuation (algebraMap A K a) ≤ 1) :
    ∃ p : HeightOneSpectrum A, v = placeOf A hA p := by
  let I : Ideal A :=
    { carrier := {a | v.valuation (algebraMap A K a) < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at *
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv c)) ha }
  have hmem : ∀ a, a ∈ I ↔ v.valuation (algebraMap A K a) < 1 := fun a => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have := (hmem 1).mp (h ▸ Submodule.mem_top)
      simp at this
    · rw [hmem, map_mul, map_mul] at hab
      rw [hmem, hmem]
      by_contra hc
      push Not at hc
      have ha1 : v.valuation (algebraMap A K a) = 1 := le_antisymm (hv a) hc.1
      have hb1 : v.valuation (algebraMap A K b) = 1 := le_antisymm (hv b) hc.2
      rw [ha1, hb1] at hab
      simp at hab
  have hne : I ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := v.valuation_surjective (WithZero.exp (-1))
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := A) x
    have hxlt : v.valuation x < 1 := by
      rw [hx, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
    have hx0 : v.valuation x ≠ 0 := by rw [hx]; exact WithZero.exp_ne_zero
    have hb0 : v.valuation (algebraMap A K b) ≠ 0 := by
      intro h0
      rw [← hab, map_div₀, h0] at hx0
      simp at hx0
    have hxb : v.valuation x * v.valuation (algebraMap A K b) = v.valuation (algebraMap A K a) := by
      rw [← map_mul, ← hab, div_mul_cancel₀]
      intro h0
      apply hb0
      rw [h0, map_zero]
    by_cases ha : a ∈ I
    · rw [hbot, Ideal.mem_bot] at ha
      subst ha
      rw [map_zero, map_zero] at hxb
      exact hx0 ((mul_eq_zero.mp hxb).resolve_right hb0)
    · rw [hmem, not_lt] at ha
      have : v.valuation x * v.valuation (algebraMap A K b) < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_right' (hv b)) hxlt
      rw [hxb] at this
      exact absurd ha (not_le.mpr this)
  let p : HeightOneSpectrum A := ⟨I, hprime, hne⟩
  refine ⟨p, (Place.eq_of_integers_le (v := placeOf A hA p) (w := v) ?_).symm⟩
  show (p.valuation K).valuationSubring ≤ v.integers
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rintro x ⟨a, s, hs, rfl⟩
  have hs1 : v.valuation (algebraMap A K s) = 1 := by
    refine le_antisymm (hv s) (not_lt.mp fun h => hs ((hmem s).mpr h))
  show v.valuation (algebraMap A K a * (algebraMap A K s)⁻¹) ≤ 1
  rw [map_mul, map_inv₀, hs1]
  simpa using hv a

end Generic

/-! ### The model ring of a separating element -/

namespace Sep

variable (s : SeparatingElement k K)

theorem model_aux [inst : Algebra k[X] K] (h : ∀ p, algebraMap k[X] K p = Polynomial.aeval s.x p) :
    IsDedekindDomain (integralClosure k[X] K) ∧ IsFractionRing (integralClosure k[X] K) K ∧
      Module.Finite k[X] (integralClosure k[X] K) ∧
      Module.finrank k[X] (integralClosure k[X] K) = Module.finrank k⟮s.x⟯ K := by
  let L := k⟮s.x⟯
  let e : RatFunc k ≃ₐ[k] L := RatFunc.algEquivOfTranscendental s.x s.transcendental
  letI : Algebra k[X] L :=
    (e.toRingEquiv.toRingHom.comp (algebraMap k[X] (RatFunc k))).toAlgebra
  haveI : IsFractionRing k[X] L :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors k[X])
      (AlgEquiv.ofRingEquiv (R := k[X]) (A₁ := RatFunc k) (A₂ := L) (f := e.toRingEquiv)
        (fun r => rfl))
  haveI : IsScalarTower k[X] L K := by
    refine IsScalarTower.of_algebraMap_eq fun p => ?_
    rw [h]
    have : algebraMap k[X] L p = Polynomial.aeval (IntermediateField.AdjoinSimple.gen k s.x) p := by
      exact RatFunc.algEquivOfTranscendental_algebraMap s.x s.transcendental p
    rw [this]
    have := Polynomial.aeval_algHom_apply (L.val) (IntermediateField.AdjoinSimple.gen k s.x) p
    simpa using this.symm
  haveI : FiniteDimensional L K := FunctionField.finiteDimensional_of_adjoin_transcendental s.transcendental
  haveI := s.isSeparable
  haveI : IsFractionRing (integralClosure k[X] K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension k[X] L K (integralClosure k[X] K)
  exact ⟨IsIntegralClosure.isDedekindDomain k[X] L K (integralClosure k[X] K), inferInstance,
    IsIntegralClosure.finite k[X] L K (integralClosure k[X] K),
    (IsFractionRing.finrank_eq k[X] L (integralClosure k[X] K) K).symm⟩

/-- Every place with $v(x)\le1$ contains the model ring $A_x$. -/
theorem valuation_le_one_of_valuation_x_le_one (v : Place k K) (hv : v.valuation s.x ≤ 1)
    (a : s.modelRing) : v.valuation (a : K) ≤ 1 := by
  have hc : ∀ c : k, v.valuation (algebraMap k K c) ≤ 1 := fun c =>
    (Place.mem_integers_iff v).1 (v.algebraMap_mem_integers c)
  let g : k →+* v.valuation.integer :=
    { toFun := fun c => ⟨algebraMap k K c, hc c⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let φ : k[X] →+* v.valuation.integer :=
    Polynomial.eval₂RingHom g ⟨s.x, hv⟩
  have hφ : (algebraMap v.valuation.integer K).comp φ = (Polynomial.aeval s.x).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp [φ, g]; rfl
    · simp [φ]; rfl
  have ha : @IsIntegral k[X] K _ _ s.polyAlgebra (a : K) := a.2
  obtain ⟨f, hf, hfa⟩ := ha
  have hint : IsIntegral v.valuation.integer (a : K) := by
    refine ⟨f.map φ, hf.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hφ]
    exact hfa
  exact (Valuation.integer.integers v.valuation).mem_of_integral hint

theorem ord_pos_iff (v : Place k K) {f : K} (hf : f ≠ 0) :
    0 < v.ord f ↔ v.valuation f < 1 := by
  have hv : v.valuation f ≠ 0 := by simpa using hf
  rw [Place.ord, ← WithZero.exp_log hv]
  simp only [WithZero.log_exp, Left.neg_pos_iff]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]

/-- **Fundamental identity for a separating element**: the zeros of $x$ form a finite set of places and
$\sum_v \max(\operatorname{ord}_v x,0)=[K:k(x)]$. -/
theorem sum_max_ord :
    (Function.support fun v : Place k K => max (v.ord s.x) 0).Finite ∧
      ∑ᶠ v : Place k K, max (v.ord s.x) 0 = (Module.finrank k⟮s.x⟯ K : ℤ) := by
  classical
  letI := s.polyAlgebra
  let B := integralClosure k[X] K
  obtain ⟨hded, hfrac, hfin, hrank⟩ := model_aux s (inst := s.polyAlgebra) (fun _ => rfl)
  haveI : IsDedekindDomain B := hded
  haveI : IsFractionRing B K := hfrac
  let p : Ideal k[X] := Ideal.span {Polynomial.X}
  haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  have hinj : Function.Injective (algebraMap k[X] K) :=
    transcendental_iff_injective.mp s.transcendental
  haveI : Module.IsTorsionFree k[X] B := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r b hrb => ?_
    have h1 : algebraMap k[X] K r * (b : K) = 0 := by
      have := congrArg Subtype.val hrb
      rwa [Subalgebra.coe_smul, Algebra.smul_def] at this
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr (Subtype.ext h)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p B
  rw [hrank] at hsum
  -- units
  have hA : ∀ c : k, c ≠ 0 → ∃ u : Bˣ, algebraMap B K u = algebraMap k K c := by
    intro c hc
    have hu : IsUnit (algebraMap k[X] B (Polynomial.C c)) :=
      (Polynomial.isUnit_C.mpr (IsUnit.mk0 c hc)).map _
    refine ⟨hu.unit, ?_⟩
    show algebraMap k[X] K (Polynomial.C c) = _
    exact Polynomial.aeval_C _ _
  -- the element x in B
  let xB : B := algebraMap k[X] B Polynomial.X
  have hxB : algebraMap B K xB = s.x := by
    show algebraMap k[X] K Polynomial.X = s.x
    exact Polynomial.aeval_X s.x
  have hxB0 : xB ≠ 0 := by
    intro h
    apply s.x_ne_zero
    rw [← hxB, h, map_zero]
  have hpmap : p.map (algebraMap k[X] B) = Ideal.span {xB} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hpmap0 : p.map (algebraMap k[X] B) ≠ ⊥ := by
    rw [hpmap, Ne, Ideal.span_singleton_eq_bot]
    exact hxB0
  have hne : ∀ q : p.primesOver B, q.1 ≠ ⊥ := by
    intro q hq
    apply hpmap0
    rw [eq_bot_iff]
    have := Ideal.map_le_of_le_comap (q.2.2.over).le (f := algebraMap k[X] B)
    rw [hq] at this
    exact this
  let P : p.primesOver B → HeightOneSpectrum B := fun q => ⟨q.1, q.2.1, hne q⟩
  let φ : p.primesOver B → Place k K := fun q => placeOf B hA (P q)
  have hval : ∀ q : p.primesOver B, (φ q).valuation s.x =
      WithZero.exp (-(q.1.ramificationIdx k[X] : ℤ)) := by
    intro q
    show (P q).valuation K s.x = _
    rw [← hxB, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hxB0,
      Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p q.1 hpmap0, hpmap]
  have hord : ∀ q : p.primesOver B, (φ q).ord s.x = q.1.ramificationIdx k[X] := by
    intro q
    rw [Place.ord, hval, WithZero.log_exp, neg_neg]
  -- residue degrees are 1
  have hdeg : ∀ q : p.primesOver B, q.1.inertiaDeg k[X] = 1 := by
    intro q
    haveI : q.1.IsMaximal := (q.2.1).isMaximal (hne q)
    haveI : q.1.LiesOver p := q.2.2
    rw [Ideal.inertiaDeg_eq_of_isMaximal p q.1]
    have hp : (Ideal.span {Polynomial.X - Polynomial.C (0 : k)} : Ideal k[X]) = p := by
      simp [p]
    let e : (k[X] ⧸ p) ≃+* k :=
      (Ideal.quotEquivOfEq hp.symm).trans (Polynomial.quotientSpanXSubCAlgEquiv (R := k) 0).toRingEquiv
    letI : Field (k[X] ⧸ p) := Ideal.Quotient.field p
    haveI : IsAlgClosed (k[X] ⧸ p) := IsAlgClosed.of_ringEquiv k _ e.symm
    haveI : Algebra.IsIntegral (k[X] ⧸ p) (B ⧸ q.1) := inferInstance
    exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hφinj : Function.Injective φ := by
    intro q₁ q₂ h
    have := placeOf_injective (k := k) (K := K) B hA h
    exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal this)
  let S : Finset (Place k K) := Finset.univ.image φ
  have hsupp : (Function.support fun v : Place k K => max (v.ord s.x) 0) ⊆ ↑S := by
    intro v hv
    simp only [Function.mem_support] at hv
    have hpos : 0 < v.ord s.x := by omega
    rw [ord_pos_iff v s.x_ne_zero] at hpos
    have hle : ∀ a : B, v.valuation (algebraMap B K a) ≤ 1 := fun a =>
      valuation_le_one_of_valuation_x_le_one s v hpos.le ⟨a.1, a.2⟩
    obtain ⟨Q, rfl⟩ := exists_eq_placeOf B hA v hle
    have hxQ : xB ∈ Q.asIdeal := by
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
      convert hpos using 2
      rfl
    have hlies : Q.asIdeal.LiesOver p := by
      constructor
      refine (hpmax.eq_of_le (Ideal.IsPrime.under k[X] Q.asIdeal).ne_top ?_)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hxQ
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨Q.asIdeal, Q.isPrime, hlies⟩, Finset.mem_univ _, rfl⟩)
  refine ⟨S.finite_toSet.subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image (fun a _ b _ h => hφinj h)]
  have hsum' : (∑ q : p.primesOver B, (q.1.ramificationIdx k[X] : ℤ)) = (Module.finrank k⟮s.x⟯ K : ℤ) := by
    rw [← hsum]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hdeg q, Nat.cast_one, mul_one]
  rw [← hsum']
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hord]
  exact max_eq_left (by positivity)

end Sep

end NumberFieldKB.MilneANT.FFClosed
