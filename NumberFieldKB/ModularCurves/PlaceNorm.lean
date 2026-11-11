import NumberFieldKB.ModularCurves.PlaceFundamental
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Orders of norms: $\operatorname{ord}_P(N_{L/K}\,g) = \sum_{Q \mid P} f(Q/P)\operatorname{ord}_Q(g)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §7 (correspondences act on divisor classes) and Ch. I, §4.
For a finite separable extension $L/K$ of function fields over `k`, a place $P$ of $K$ and $g \in L^\times$, the order
at $P$ of the norm of $g$ is $\sum_{Q \mid P} f(Q/P)\operatorname{ord}_Q(g)$ (`ord_norm`). Hence the push-forward of
the divisor of $g$ is the divisor of its norm, and push-forward preserves principal divisors.

The proof is local at $P$, with $B$ the integral closure of $\mathcal O_P$ in $L$: Mathlib's relative norm of ideals
sends a prime $\mathfrak q$ of $B$ to $\mathfrak m_P^{f(\mathfrak q)}$ (`Ideal.relNorm_eq_pow_of_isMaximal`) and
the ideal $(b)$ to $(N b)$ (`Ideal.relNorm_singleton`); the factorization of $(b)$ into primes of $B$ gives the
formula for $b \in B$, and $L$ is the field of fractions of $B$.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC

/-- The order of $r \in R$ at a height-one prime $v$ is the multiplicity of $v$ in $(r)$. -/
theorem ordV_valuation_algebraMap {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    ordV (v.valuation K) (algebraMap R K r) =
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors := by
  rw [ordV, valuation_of_algebraMap, intValuation_if_neg v hr, WithZero.log_exp, neg_neg]

section Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.ord_mul (P : PrimeDivisor k K) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) : P.ord (x * y) = P.ord x + P.ord y := by
  rw [P.ord_eq_ordV_valuation (mul_ne_zero hx hy), P.ord_eq_ordV_valuation hx, P.ord_eq_ordV_valuation hy,
    ordV_mul _ hx hy]

theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.ord_div (P : PrimeDivisor k K) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) : P.ord (x / y) = P.ord x - P.ord y := by
  rw [P.ord_eq_ordV_valuation (div_ne_zero hx hy), P.ord_eq_ordV_valuation hx, P.ord_eq_ordV_valuation hy,
    ordV_div _ hx hy]

end Place

section Extension

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

attribute [local instance] PrimeDivisor.isDVR

variable (P : PrimeDivisor k K) [Algebra P.O L] [IsScalarTower P.O K L]

instance finite_integralClosure : Module.Finite P.O (integralClosure P.O L) :=
  IsIntegralClosure.finite P.O K L _

omit [Algebra k L] [IsScalarTower k K L] in
/-- There are finitely many places of `L` over `P`, i.e. nonzero primes of the integral closure. -/
theorem finite_heightOneSpectrum : Finite (HeightOneSpectrum (integralClosure P.O L)) := by
  have : Algebra.IsIntegral P.O (integralClosure P.O L) := Algebra.IsIntegral.of_finite _ _
  have hfin := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal P.O) (integralClosure P.O L)
  have : Finite ((IsLocalRing.maximalIdeal P.O).primesOver (integralClosure P.O L)) := hfin.to_subtype
  refine Finite.of_injective
    (fun v => (⟨v.asIdeal, v.isPrime, liesOver_maximalIdeal v⟩ :
      (IsLocalRing.maximalIdeal P.O).primesOver (integralClosure P.O L))) fun v w h => ?_
  exact HeightOneSpectrum.ext (congrArg Subtype.val h)

/-- A sum over the places over `P` is a sum over the nonzero primes of the integral closure. -/
theorem sum_places_eq [Fintype (HeightOneSpectrum (integralClosure P.O L))] (S : Finset (PrimeDivisor k L))
    (hS : ∀ Q, Q ∈ S ↔ Q.comap (K := K) = P) (F : PrimeDivisor k L → ℤ) :
    ∑ Q ∈ S, F Q = ∑ v, F (placeOver P v) := by
  symm
  refine Finset.sum_bij (fun v _ => placeOver P v) ?_ ?_ ?_ ?_
  · intro v _
    rw [hS]
    exact comap_placeOver P v
  · intro v _ w _ h
    exact placeOver_injective P h
  · intro Q hQ
    obtain ⟨v, rfl⟩ := (exists_placeOver_iff P Q).2 ((hS Q).1 hQ)
    exact ⟨v, Finset.mem_univ _, rfl⟩
  · intro v _
    rfl

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

omit [Algebra k L] [IsScalarTower k K L] in
theorem isSeparable_fractionRing :
    Algebra.IsSeparable (FractionRing P.O) (FractionRing (integralClosure P.O L)) := by
  have H : RingHom.comp (algebraMap (FractionRing P.O) (FractionRing (integralClosure P.O L)))
      ↑(FractionRing.algEquiv P.O K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv (integralClosure P.O L) L).symm.toRingEquiv
          (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors P.O)
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, Function.comp_apply,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply P.O (integralClosure P.O L) L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

omit [Algebra k L] [IsScalarTower k K L] in
/-- **The relative norm of an ideal** of the integral closure: $N(I) = \mathfrak m_P^{\sum_v f_v\, n_v(I)}$. -/
theorem relNorm_eq_pow [Fintype (HeightOneSpectrum (integralClosure P.O L))] (I : Ideal (integralClosure P.O L))
    (hI : I ≠ ⊥) :
    Ideal.relNorm P.O I = IsLocalRing.maximalIdeal P.O ^ ∑ v : HeightOneSpectrum (integralClosure P.O L),
      v.asIdeal.inertiaDeg P.O * (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  have := isSeparable_fractionRing (L := L) P
  have hfac := Ideal.finprod_heightOneSpectrum_factorization hI
  rw [finprod_eq_prod_of_fintype] at hfac
  conv_lhs => rw [← hfac]
  rw [map_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  have : v.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.O) := liesOver_maximalIdeal v
  have : v.asIdeal.IsMaximal := v.isMaximal
  rw [HeightOneSpectrum.maxPowDividing, map_pow,
    Ideal.relNorm_eq_pow_of_isMaximal v.asIdeal (IsLocalRing.maximalIdeal P.O), ← pow_mul]

/-- The order of $b \in B$ at the place of a prime $v$ is the multiplicity of $v$ in $(b)$. -/
theorem ord_placeOver_algebraMap (v : HeightOneSpectrum (integralClosure P.O L)) {b : integralClosure P.O L}
    (hb : b ≠ 0) :
    (placeOver P v).ord (algebraMap _ L b) =
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b} : Ideal _)).factors := by
  have hb' : algebraMap (integralClosure P.O L) L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).2 hb
  rw [placeOver, ord_toPrimeDivisor _ v hb', ordV_valuation_algebraMap v hb]

omit [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Algebra P.O L] [IsScalarTower P.O K L] in
/-- The order at $P$ of $a \in \mathcal O_P$ is the exponent of $\mathfrak m_P$ in $(a)$. -/
theorem ord_algebraMap_of_span_eq {a : P.O} (ha : a ≠ 0) {n : ℕ}
    (hn : Ideal.span {a} = IsLocalRing.maximalIdeal P.O ^ n) :
    P.ord (algebraMap P.O K a) = n := by
  have ha' : algebraMap P.O K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective P.O K)).2 ha
  rw [P.ord_eq_ordV_valuation ha', PrimeDivisor.valuation,
    ordV_valuation_algebraMap (IsDiscreteValuationRing.maximalIdeal P.O) ha]
  change ((Associates.mk (IsLocalRing.maximalIdeal P.O)).count
    (Associates.mk (Ideal.span {a} : Ideal P.O)).factors : ℤ) = n
  have hirr : Irreducible (Associates.mk (IsLocalRing.maximalIdeal P.O)) :=
    (IsDiscreteValuationRing.maximalIdeal P.O).associates_irreducible
  have hm0 : Associates.mk (IsLocalRing.maximalIdeal P.O) ≠ 0 := hirr.ne_zero
  rw [hn, Associates.mk_pow, Associates.count_pow hm0 hirr, Associates.count_self hirr, mul_one]

/-- **The order of a norm** for $b$ in the integral closure: $\operatorname{ord}_P(N b) =
\sum_v f_v \operatorname{ord}_v(b)$. -/
theorem ord_norm_algebraMap [Fintype (HeightOneSpectrum (integralClosure P.O L))]
    {b : integralClosure P.O L} (hb : b ≠ 0) :
    P.ord (Algebra.norm K (algebraMap _ L b)) =
      ∑ v, (v.asIdeal.inertiaDeg P.O : ℤ) * (placeOver P v).ord (algebraMap _ L b) := by
  have hb' : algebraMap (integralClosure P.O L) L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).2 hb
  set a := Algebra.intNorm P.O (integralClosure P.O L) b
  have hna : algebraMap P.O K a = Algebra.norm K (algebraMap _ L b) := Algebra.algebraMap_intNorm b
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hna
    exact (Algebra.norm_ne_zero_iff.2 hb') hna.symm
  have hspan : Ideal.span {a} = IsLocalRing.maximalIdeal P.O ^ ∑ v : HeightOneSpectrum (integralClosure P.O L),
      v.asIdeal.inertiaDeg P.O *
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b} : Ideal _)).factors := by
    rw [← relNorm_eq_pow P _ ((Ideal.span_singleton_eq_bot).not.2 hb), Ideal.relNorm_singleton]
  rw [← hna, ord_algebraMap_of_span_eq P ha hspan]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [ord_placeOver_algebraMap P v hb]

/-- **The order of a norm** (Milne V §7): $\operatorname{ord}_P(N_{L/K}\, g) = \sum_{Q \mid P}
f(Q/P)\operatorname{ord}_Q(g)$ for $g \in L^\times$; `S` lists exactly the places of $L$ over $P$. -/
theorem ord_norm (S : Finset (PrimeDivisor k L)) (hS : ∀ Q, Q ∈ S ↔ Q.comap (K := K) = P) {g : L}
    (hg : g ≠ 0) :
    P.ord (Algebra.norm K g) = ∑ Q ∈ S, (Q.residueDeg (K := K) : ℤ) * Q.ord g := by
  have := finite_heightOneSpectrum (L := L) P
  let := Fintype.ofFinite (HeightOneSpectrum (integralClosure P.O L))
  rw [sum_places_eq P S hS]
  simp_rw [residueDeg_placeOver]
  obtain ⟨b, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := integralClosure P.O L) g
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hg
  have hb' : algebraMap (integralClosure P.O L) L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).2 hb0
  have hs' : algebraMap (integralClosure P.O L) L s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).2 hs0
  have hNs : Algebra.norm K (algebraMap (integralClosure P.O L) L s) ≠ 0 := (Algebra.norm_ne_zero_iff).2 hs'
  have hdiv : Algebra.norm K (algebraMap (integralClosure P.O L) L b / algebraMap _ L s) =
      Algebra.norm K (algebraMap (integralClosure P.O L) L b) / Algebra.norm K (algebraMap _ L s) := by
    refine eq_div_of_mul_eq hNs ?_
    rw [← map_mul, div_mul_cancel₀ _ hs']
  rw [hdiv, P.ord_div ((Algebra.norm_ne_zero_iff).2 hb') ((Algebra.norm_ne_zero_iff).2 hs'),
    ord_norm_algebraMap P hb0, ord_norm_algebraMap P hs0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [PrimeDivisor.ord_div _ hb' hs', mul_sub]

end Extension

section Push

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

omit [FiniteDimensional K L] in
/-- The coefficient of a push-forward at $P$: $(\pi_* D)(P) = \sum_{Q \mid P} f(Q/P)\, D(Q)$. -/
theorem pushDiv_apply (P : PrimeDivisor k K) (S : Finset (PrimeDivisor k L))
    (hS : ∀ Q, Q ∈ S ↔ Q.comap (K := K) = P) (D : Divisor k L) :
    pushDiv (K := K) D P = ∑ Q ∈ S, (Q.residueDeg (K := K) : ℤ) * D Q := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [map_add, Finsupp.add_apply, hD, hE, ← Finset.sum_add_distrib]; simp [mul_add]
  | single Q n =>
    simp only [pushDiv, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, Finsupp.smul_apply,
      smul_eq_mul]
    by_cases hQ : Q.comap (K := K) = P
    · rw [Finset.sum_eq_single Q (fun Q' _ hne => by simp [Ne.symm hne])
        (fun hn => absurd ((hS Q).2 hQ) hn)]
      simp [hQ, mul_comm]
    · have h0 : ∀ Q' ∈ S, (Q'.residueDeg (K := K) : ℤ) * (Finsupp.single Q n) Q' = 0 := by
        intro Q' hQ'
        have hne : Q ≠ Q' := fun e => hQ (e ▸ (hS Q').1 hQ')
        simp [hne]
      rw [Finset.sum_eq_zero h0]
      simp [hQ]

/-- **Push-forward of a principal divisor**: $\pi_* \operatorname{div}(g) = \operatorname{div}(N_{L/K}\, g)$. -/
theorem isDivisorOf_pushDiv {D : Divisor k L} {g : L} (hD : IsDivisorOf D g) :
    IsDivisorOf (pushDiv (K := K) D) (Algebra.norm K g) := by
  refine ⟨(Algebra.norm_ne_zero_iff).2 hD.1, fun P => ?_⟩
  let : Algebra P.O L := ((algebraMap K L).comp (algebraMap P.O K)).toAlgebra
  have : IsScalarTower P.O K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := finite_heightOneSpectrum (L := L) P
  let := Fintype.ofFinite (HeightOneSpectrum (integralClosure P.O L))
  classical
  let S : Finset (PrimeDivisor k L) := Finset.univ.image (placeOver P)
  have hS : ∀ Q, Q ∈ S ↔ Q.comap (K := K) = P := by
    intro Q
    rw [← exists_placeOver_iff P Q]
    simp [S]
  rw [pushDiv_apply P S hS, ord_norm P S hS hD.1]
  exact Finset.sum_congr rfl fun Q _ => by rw [hD.2]

theorem pushDiv_principal {D : Divisor k L} (hD : D ∈ principalDivisors) :
    pushDiv (K := K) D ∈ principalDivisors := by
  have hle : (principalDivisors (k := k) (K := L)) ≤
      (principalDivisors (k := k) (K := K)).comap (pushDiv (K := K)) := by
    refine (AddSubgroup.closure_le _).2 fun E ⟨f, hf⟩ => ?_
    exact AddSubgroup.subset_closure ⟨_, isDivisorOf_pushDiv hf⟩
  exact hle hD

end Push

end NumberFieldKB.ModularCurves
