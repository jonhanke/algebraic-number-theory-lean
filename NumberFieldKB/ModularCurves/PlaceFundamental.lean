import NumberFieldKB.ModularCurves.PlaceRamification
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The fundamental identity for places in a finite separable extension of function fields

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. I, §4 (prime divisors, pdf p. 45) and Ch. V, §2 (the degree of
$X_0(N) \to X_0(1)$ as a sum of ramification indices). For a finite separable extension $L/K$ of function fields over
`k` and a place $P$ of $K$ (Milne's `MilneEC.PrimeDivisor`), the places $Q$ of $L$ over $P$ satisfy
$$\sum_{Q \mid P} e(Q/P)\, f(Q/P) = [L : K],$$
with $e(Q/P) = \operatorname{ord}_Q(t_P)$ and $f(Q/P)$ the residue degree (`PrimeDivisor.residueDeg`).

The proof is local at $P$: the integral closure $B$ of the discrete valuation ring $\mathcal O_P$ in $L$ is a
Dedekind domain, finite over $\mathcal O_P$; the places over $P$ are the localizations of $B$ at its nonzero primes
(`exists_toPrimeDivisor_iff`); and the ramification indices and residue degrees of places are Mathlib's
`Ideal.ramificationIdx` and `Ideal.inertiaDeg` of those primes. Then Mathlib's
`Ideal.sum_ramification_inertia_eq_finrank` gives the identity. This covers the cusps of $X_0(N)$ as well as the
points of $Y_0(N)$, with no chart at infinity.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC

section Dedekind

variable {k R K : Type*} [Field k] [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Algebra k K]

/-- Milne's $\operatorname{ord}$ at the place $R_v$ is the order of the $v$-adic valuation. -/
theorem ord_toPrimeDivisor (hk : ∀ c : k, ∃ r : R, algebraMap R K r = algebraMap k K c)
    (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    (HeightOneSpectrum.toPrimeDivisor k hk v).ord x = ordV (v.valuation K) x := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  refine PrimeDivisor.ord_eq_ordV _ _ (valuationSubringAtPrime_eq_valuationSubring v) hπ0 ?_ hx
  rw [ordV, hπ, WithZero.log_exp, neg_neg]

end Dedekind

section Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.O_eq_valuationSubring (P : PrimeDivisor k K) :
    P.O = P.valuation.valuationSubring := by
  ext x
  exact P.mem_O_iff_valuation_le_one x

/-- Milne's $\operatorname{ord}_P$ is the order of the normalized valuation of $P$. -/
theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.ord_eq_ordV_valuation (P : PrimeDivisor k K) {x : K}
    (hx : x ≠ 0) : P.ord x = ordV P.valuation x := by
  have := P.isDVR
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal P.O).valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  refine PrimeDivisor.ord_eq_ordV _ _ P.O_eq_valuationSubring hπ0 ?_ hx
  rw [ordV, PrimeDivisor.valuation, hπ, WithZero.log_exp, neg_neg]

theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.ordV_valuation_unif (P : PrimeDivisor k K) :
    ordV P.valuation P.unif = 1 := by
  rw [← P.ord_eq_ordV_valuation P.unif_ne_zero, P.ord_unif]

end Place


section Extension

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L]

attribute [local instance] PrimeDivisor.isDVR

/-- **Changing the base place in the residue degree**: if $\pi Q = P$, the residue degree $f(Q/P)$ may be computed
with any local homomorphism $\mathcal O_P \to \mathcal O_Q$ compatible with $K \subseteq L$. -/
theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.residueDeg_eq_of_comap_eq [Algebra.IsAlgebraic K L]
    (Q : PrimeDivisor k L) (P : PrimeDivisor k K) (hQ : Q.comap (K := K) = P) (ψ : P.O →+* Q.O)
    (hψ : ∀ x : P.O, (ψ x : L) = algebraMap K L x) :
    ∃ _ : IsLocalHom ψ, Q.residueDeg (K := K) =
      letI := (IsLocalRing.ResidueField.map ψ).toAlgebra
      Module.finrank (IsLocalRing.ResidueField P.O) (IsLocalRing.ResidueField Q.O) := by
  subst hQ
  obtain rfl : ψ = Q.comapHom (K := K) := RingHom.ext fun x => Subtype.ext (hψ x)
  exact ⟨inferInstance, rfl⟩

variable (P : PrimeDivisor k K) [Algebra P.O L] [IsScalarTower P.O K L]

theorem algebraMap_mem_integralClosure (c : k) : algebraMap k L c ∈ integralClosure P.O L := by
  have : algebraMap k L c = algebraMap P.O L (P.ofBase c) := by
    rw [IsScalarTower.algebraMap_apply P.O K L, IsScalarTower.algebraMap_apply k K L]
    rfl
  rw [this]
  exact isIntegral_algebraMap

theorem exists_integralClosure_eq (c : k) :
    ∃ b : integralClosure P.O L, algebraMap (integralClosure P.O L) L b = algebraMap k L c :=
  ⟨⟨_, algebraMap_mem_integralClosure P c⟩, rfl⟩

/-- **The places over a place**: a place $Q$ of $L$ lies over $P$ iff its valuation ring contains the integral
closure of $\mathcal O_P$ in $L$. -/
theorem comap_eq_iff [Algebra.IsAlgebraic K L] (Q : PrimeDivisor k L) :
    Q.comap (K := K) = P ↔ ∀ b : integralClosure P.O L, (b : L) ∈ Q.O := by
  constructor
  · rintro rfl b
    let φ : (Q.comap (K := K)).O →+* Q.O := Q.comapHom
    have hc : (algebraMap Q.O L).comp φ = algebraMap (Q.comap (K := K)).O L := by
      refine RingHom.ext fun x => ?_
      change algebraMap K L x = _
      rw [IsScalarTower.algebraMap_apply (Q.comap (K := K)).O K L]
      rfl
    obtain ⟨f, hfm, hf⟩ := b.2
    have hint : IsIntegral Q.O (b : L) :=
      ⟨f.map φ, hfm.map φ, by rw [Polynomial.eval₂_map, hc]; exact hf⟩
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Q.O) (K := L)).1 hint
    rw [← hz]
    exact z.2
  · intro h
    have hle : P.O ≤ (Q.comap (K := K)).O := by
      intro x hx
      rw [PrimeDivisor.mem_comap_O]
      have := h ⟨algebraMap P.O L ⟨x, hx⟩, isIntegral_algebraMap⟩
      change algebraMap P.O L ⟨x, hx⟩ ∈ Q.O at this
      rwa [IsScalarTower.algebraMap_apply P.O K L] at this
    exact (PrimeDivisor.ext_O
      (ValuationSubring.eq_of_le_of_ne_top P.O hle (PrimeDivisor.O_ne_top _))).symm

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

instance isDedekindDomain_integralClosure : IsDedekindDomain (integralClosure P.O L) :=
  integralClosure.isDedekindDomain P.O K L

instance isFractionRing_integralClosure : IsFractionRing (integralClosure P.O L) L :=
  integralClosure.isFractionRing_of_finite_extension K L

/-- The place of `L` at a nonzero prime of the integral closure of $\mathcal O_P$. -/
noncomputable def placeOver (v : HeightOneSpectrum (integralClosure P.O L)) : PrimeDivisor k L :=
  HeightOneSpectrum.toPrimeDivisor k (exists_integralClosure_eq P) v

theorem placeOver_injective : Function.Injective (placeOver (L := L) P) :=
  HeightOneSpectrum.toPrimeDivisor_injective (exists_integralClosure_eq P)

theorem exists_placeOver_iff (Q : PrimeDivisor k L) :
    (∃ v, placeOver P v = Q) ↔ Q.comap (K := K) = P := by
  change (∃ v, HeightOneSpectrum.toPrimeDivisor k (exists_integralClosure_eq P) v = Q) ↔ _
  rw [comap_eq_iff, exists_toPrimeDivisor_iff]
  rfl

theorem comap_placeOver (v : HeightOneSpectrum (integralClosure P.O L)) :
    (placeOver P v).comap (K := K) = P :=
  (exists_placeOver_iff P _).1 ⟨v, rfl⟩


omit [Algebra k L] [Algebra K L] [IsScalarTower k K L] [IsScalarTower P.O K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] in
variable {P} in
/-- A nonzero prime of the integral closure lies over the maximal ideal of $\mathcal O_P$. -/
theorem liesOver_maximalIdeal (v : HeightOneSpectrum (integralClosure P.O L)) :
    v.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.O) := by
  constructor
  have hne : v.asIdeal.under P.O ≠ ⊥ := Ideal.under_ne_bot P.O v.ne_bot
  exact (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)).symm

instance isTorsionFree_integralClosure : Module.IsTorsionFree P.O (integralClosure P.O L) := by
  refine Module.isTorsionFree_iff_algebraMap_injective.2 fun a b hab => ?_
  have h := congrArg (fun x : integralClosure P.O L => (x : L)) hab
  change algebraMap P.O L a = algebraMap P.O L b at h
  rw [IsScalarTower.algebraMap_apply P.O K L, IsScalarTower.algebraMap_apply P.O K L] at h
  exact IsFractionRing.injective P.O K ((algebraMap K L).injective h)

/-- **Ramification indices agree**: $\operatorname{ord}_Q(t_P)$ is Mathlib's ramification index of the prime of the
integral closure at $Q$. -/
theorem ord_placeOver_unif (v : HeightOneSpectrum (integralClosure P.O L)) :
    (placeOver P v).ord (algebraMap K L P.unif) = v.asIdeal.ramificationIdx P.O := by
  have : v.asIdeal.LiesOver (IsDiscreteValuationRing.maximalIdeal P.O).asIdeal := liesOver_maximalIdeal v
  have hv := valuation_liesOver L (IsDiscreteValuationRing.maximalIdeal P.O) v P.unif
  have ht0 : algebraMap K L P.unif ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).2 P.unif_ne_zero
  rw [placeOver, ord_toPrimeDivisor _ v ht0, ordV, ← hv, WithZero.log_pow, nsmul_eq_mul]
  have h1 := P.ordV_valuation_unif
  rw [ordV, PrimeDivisor.valuation] at h1
  rw [← mul_neg, h1, mul_one]


/-- **Residue degrees agree**: $f(Q/P)$ is Mathlib's inertia degree of the prime of the integral closure at $Q$. -/
theorem residueDeg_placeOver (v : HeightOneSpectrum (integralClosure P.O L)) :
    (placeOver P v).residueDeg (K := K) = v.asIdeal.inertiaDeg P.O := by
  let B := integralClosure P.O L
  let Bv := valuationSubringAtPrime L v
  let ψ : P.O →+* (placeOver P v).O := (algebraMap B Bv).comp (algebraMap P.O B)
  have hψ : ∀ x : P.O, ((ψ x : (placeOver P v).O) : L) = algebraMap K L x := fun x => by
    change algebraMap P.O L x = _
    rw [IsScalarTower.algebraMap_apply P.O K L]
    rfl
  obtain ⟨hloc, h⟩ := (placeOver P v).residueDeg_eq_of_comap_eq P (comap_placeOver P v) ψ hψ
  rw [h]
  have : v.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.O) := liesOver_maximalIdeal v
  have : v.asIdeal.IsMaximal := v.isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal P.O)]
  let := (IsLocalRing.ResidueField.map ψ).toAlgebra
  let j : IsLocalRing.ResidueField (placeOver P v).O ≃+* B ⧸ v.asIdeal :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal Bv).symm.toRingEquiv
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl (IsLocalRing.ResidueField P.O)) j ?_
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk v.asIdeal (algebraMap P.O B a) =
    (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal Bv).symm
      (IsLocalRing.residue Bv (ψ a))
  exact (((IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal Bv).symm_apply_eq).2 rfl).symm


/-- **The fundamental identity for places** (Milne V §2, running text): for a finite separable extension $L/K$ and a
place $P$ of $K$, $\sum_{Q \mid P} e(Q/P)\,f(Q/P) = [L : K]$, with $e(Q/P) = \operatorname{ord}_Q(t_P)$. Here `S`
is any finite set listing exactly the places of $L$ over $P$. -/
theorem sum_ord_mul_residueDeg (S : Finset (PrimeDivisor k L))
    (hS : ∀ Q, Q ∈ S ↔ Q.comap (K := K) = P) :
    ∑ Q ∈ S, Q.ord (algebraMap K L P.unif) * (Q.residueDeg (K := K) : ℤ) = Module.finrank K L := by
  let B := integralClosure P.O L
  let p := IsLocalRing.maximalIdeal P.O
  have : Module.Finite P.O B := IsIntegralClosure.finite P.O K L B
  have : Algebra.IsIntegral P.O B := Algebra.IsIntegral.of_finite _ _
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field P.O
  let : Fintype (p.primesOver B) := Set.Finite.fintype (IsDedekindDomain.primesOver_finite p B)
  have key := Ideal.sum_ramification_inertia_eq_finrank p B
  have hrank : Module.finrank K L = Module.finrank P.O B := IsFractionRing.finrank_eq P.O K B L
  let toH : p.primesOver B → HeightOneSpectrum B := fun q =>
    haveI := q.2.2
    ⟨q.1, q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 q.1⟩
  rw [hrank, ← key, Nat.cast_sum]
  symm
  refine Finset.sum_bij (fun q _ => placeOver P (toH q)) ?_ ?_ ?_ ?_
  · intro q _
    rw [hS]
    exact comap_placeOver P _
  · intro q1 _ q2 _ h
    exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal (placeOver_injective P h))
  · intro Q hQ
    obtain ⟨v, rfl⟩ := (exists_placeOver_iff P Q).2 ((hS Q).1 hQ)
    exact ⟨⟨v.asIdeal, v.isPrime, liesOver_maximalIdeal v⟩, Finset.mem_univ _, rfl⟩
  · intro q _
    rw [ord_placeOver_unif, residueDeg_placeOver]
    push_cast
    rfl

/-- $\operatorname{ord}_Q(x) = e\,\operatorname{ord}_P(x)$ for $x \in K$, $Q$ the place of a prime over $P$. -/
theorem ord_placeOver (v : HeightOneSpectrum (integralClosure P.O L)) {x : K} (hx : x ≠ 0) :
    (placeOver P v).ord (algebraMap K L x) = v.asIdeal.ramificationIdx P.O * P.ord x := by
  have : v.asIdeal.LiesOver (IsDiscreteValuationRing.maximalIdeal P.O).asIdeal := liesOver_maximalIdeal v
  have hv := valuation_liesOver L (IsDiscreteValuationRing.maximalIdeal P.O) v x
  have hx0 : algebraMap K L x ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).2 hx
  rw [placeOver, ord_toPrimeDivisor _ v hx0, ordV, ← hv, WithZero.log_pow, nsmul_eq_mul,
    P.ord_eq_ordV_valuation hx, ordV, PrimeDivisor.valuation]
  ring

end Extension

section Pullback

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **Orders pull back with the ramification index**: for a place $Q$ of $L$ over $P$ and $x \in K^\times$,
$\operatorname{ord}_Q(x) = e(Q/P)\operatorname{ord}_P(x)$ with $e(Q/P) = \operatorname{ord}_Q(t_P)$. -/
theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.ord_algebraMap_of_comap_eq (Q : PrimeDivisor k L)
    (P : PrimeDivisor k K) (hQ : Q.comap (K := K) = P) {x : K} (hx : x ≠ 0) :
    Q.ord (algebraMap K L x) = Q.ord (algebraMap K L P.unif) * P.ord x := by
  let : Algebra P.O L := ((algebraMap K L).comp (algebraMap P.O K)).toAlgebra
  have : IsScalarTower P.O K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨v, rfl⟩ := (exists_placeOver_iff P Q).2 hQ
  rw [ord_placeOver P v hx, ord_placeOver_unif]

end Pullback


/-! ### The fundamental identity on $X_0$ and degrees of pullbacks -/

section X0

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- **The fundamental identity for $X_0(M) \to X_0(N)$**, $z \mapsto z$ ($N \mid M$), at every place $P$ of
$X_0(N)$ over $\mathbb Q$, cusps included: $\sum_{Q \mid P} e(Q/P)\,f(Q/P) = (\Gamma_0(N) : \Gamma_0(M))$. -/
@[kb "milne2006ec" "Ch. V, §2, the degree of X_0(N) → X_0(1) as a sum of ramification indices (running text), pdf p. 196"]
theorem sum_ramIndex_mul_residueDeg_forget (h : 1 * N ∣ M) (P : PrimeDivisor ℚ (X0 N)) :
    letI := forgetAlgebra N M h
    haveI := isAlgebraic_degeneracy h
    ∑ Q ∈ placesAbove h P, ramIndex h P Q * (Q.residueDeg (K := X0 N) : ℤ) =
      (CongruenceSubgroup.Gamma0 M).relIndex (CongruenceSubgroup.Gamma0 N) := by
  let := forgetAlgebra N M h
  have := isAlgebraic_degeneracy h
  have := isScalarTower_rat_degeneracy h
  have : FiniteDimensional (X0 N) (X0 M) := finite_forget h
  let : Algebra P.O (X0 M) := ((algebraMap (X0 N) (X0 M)).comp (algebraMap P.O (X0 N))).toAlgebra
  have : IsScalarTower P.O (X0 N) (X0 M) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← finrank_forget h]
  exact sum_ord_mul_residueDeg P (placesAbove h P) (fun Q => mem_placesAbove h P Q)


theorem deg_single_place (Q : PrimeDivisor ℚ (X0 M)) (n : ℤ) :
    Divisor.deg (Finsupp.single Q n) = n * Q.deg := by
  simp only [Divisor.deg, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, smul_eq_mul]

/-- **Pullback multiplies degrees by the degree of the map**: for $z \mapsto z$, $X_0(M) \to X_0(N)$,
$\deg \pi^* D = (\Gamma_0(N) : \Gamma_0(M)) \deg D$ for every divisor $D$ of $X_0(N)$, cusps included. -/
theorem deg_pullX0 (h : 1 * N ∣ M) (D : Divisor ℚ (X0 N)) :
    Divisor.deg (pullX0 h D) =
      (CongruenceSubgroup.Gamma0 M).relIndex (CongruenceSubgroup.Gamma0 N) * Divisor.deg D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [map_add, map_add, hD, hE, map_add, mul_add]
  | single P n =>
    let := forgetAlgebra N M h
    have := isAlgebraic_degeneracy h
    have := isScalarTower_rat_degeneracy h
    have hsum := sum_ramIndex_mul_residueDeg_forget h P
    simp only [pullX0, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, map_zsmul, map_sum,
      deg_single_place, smul_eq_mul]
    have hdeg : ∀ Q ∈ placesAbove h P, ramIndex h P Q * (Q.deg : ℤ) =
        ramIndex h P Q * (Q.residueDeg (K := X0 N) : ℤ) * P.deg := by
      intro Q hQ
      have hc : Q.comap (K := X0 N) = P := (mem_placesAbove h P Q).1 hQ
      rw [Q.deg_eq_residueDeg_mul (K := X0 N), hc]
      push_cast
      ring
    rw [Finset.sum_congr rfl hdeg, ← Finset.sum_mul, hsum]
    ring

/-- **$T(p)$ multiplies degrees by $(\Gamma_0(N) : \Gamma_0(pN))$** on divisors of $X_0(N)$, cusps included. -/
theorem deg_heckeX0 (N p : ℕ) [NeZero N] [NeZero p] (D : Divisor ℚ (X0 N)) :
    Divisor.deg (heckeX0 N p D) =
      (CongruenceSubgroup.Gamma0 (p * N)).relIndex (CongruenceSubgroup.Gamma0 N) * Divisor.deg D := by
  rw [heckeX0, AddMonoidHom.comp_apply, deg_pushX0, deg_pullX0]

/-- The coefficient of the pullback at a place $Q$: $(\pi^*D)(Q) = D(\pi Q)\, e(Q/\pi Q)$. -/
theorem pullX0_apply {d : ℕ} (h : d * N ∣ M) (D : Divisor ℚ (X0 N)) (Q : PrimeDivisor ℚ (X0 M)) :
    pullX0 h D Q = D (degeneracyPlace h Q) * ramIndex h (degeneracyPlace h Q) Q := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [map_add, Finsupp.add_apply, hD, hE, Finsupp.add_apply, add_mul]
  | single P n =>
    simp only [pullX0, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, Finsupp.smul_apply,
      Finsupp.finsetSum_apply, smul_eq_mul]
    by_cases hQ : degeneracyPlace h Q = P
    · subst hQ
      rw [Finset.sum_eq_single Q (fun Q' _ hne => by simp [hne])
        (fun hn => absurd ((mem_placesAbove h _ Q).2 rfl) hn)]
      simp
    · have h0 : ∀ Q' ∈ placesAbove h P, (Finsupp.single Q' (ramIndex h P Q')) Q = 0 := by
        intro Q' hQ'
        have hne : Q' ≠ Q := fun e => hQ (e ▸ (mem_placesAbove h P Q').1 hQ')
        simp [hne]
      rw [Finset.sum_eq_zero h0]
      simp [Ne.symm hQ]

/-- **Pullback of a principal divisor**: $\pi^* \operatorname{div}(f) = \operatorname{div}(f \circ \pi)$. -/
theorem isDivisorOf_pullX0 (h : 1 * N ∣ M) {D : Divisor ℚ (X0 N)} {f : X0 N} (hD : IsDivisorOf D f) :
    IsDivisorOf (pullX0 h D) (degeneracy N M 1 h f) := by
  refine ⟨(map_ne_zero_iff _ (degeneracy N M 1 h).injective).2 hD.1, fun Q => ?_⟩
  let := forgetAlgebra N M h
  have := isAlgebraic_degeneracy h
  have := isScalarTower_rat_degeneracy h
  have : FiniteDimensional (X0 N) (X0 M) := finite_forget h
  rw [pullX0_apply, hD.2, ramIndex, mul_comm]
  exact (Q.ord_algebraMap_of_comap_eq (degeneracyPlace h Q) rfl hD.1).symm

theorem pullX0_principal (h : 1 * N ∣ M) {D : Divisor ℚ (X0 N)} (hD : D ∈ principalDivisors) :
    pullX0 h D ∈ principalDivisors := by
  have hle : (principalDivisors (k := ℚ) (K := X0 N)) ≤
      (principalDivisors (k := ℚ) (K := X0 M)).comap (pullX0 h) := by
    refine (AddSubgroup.closure_le _).2 fun E ⟨f, hf⟩ => ?_
    exact AddSubgroup.subset_closure ⟨_, isDivisorOf_pullX0 h hf⟩
  exact hle hD

end X0

end NumberFieldKB.ModularCurves
