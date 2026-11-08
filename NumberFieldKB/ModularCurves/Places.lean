import NumberFieldKB.ModularCurves.Ramification
import NumberFieldKB.MilneEC.Ch1Example46

/-!
# The points of $X_0(N)$ over $\mathbb Q$ as places: $Y_0(N)$ and the cusps

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. I, §4 (pdf pp. 44–45) and Ch. V, §2 (pdf p. 195). The closed
points of the nonsingular projective curve $X_0(N)$ over $\mathbb Q$ are the prime divisors (places) of
$\mathbb Q(X_0(N))$ (`MilneEC.PrimeDivisor`, Milne's definition, p. 45). Here:

* For a Dedekind domain `R` with field of fractions `K`, every height-one prime `v` gives a place
  (`HeightOneSpectrum.toPrimeDivisor`, the localization $R_v$, Mathlib's `valuationSubringAtPrime`), injectively,
  and the places obtained are exactly those whose valuation ring contains `R` (`exists_toPrimeDivisor_iff`).
* For $X_0(N)$: the closed points of $Y_0(N)$ (`Y0Point N`) are the places of $\mathbb Q(X_0(N))$ at which $j$ is
  finite (`Y0Point.toPlace`, `exists_toPlace_iff`); the other places are the **cusps** (`IsCusp`).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC

section General

variable {k R K : Type*} [Field k] [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Algebra k K]

theorem mem_valuationSubringAtPrime_iff (v : HeightOneSpectrum R) (x : K) :
    x ∈ valuationSubringAtPrime K v ↔ v.valuation K x ≤ 1 := by
  rw [valuationSubringAtPrime_eq_valuationSubring]
  rfl

theorem algebraMap_mem_valuationSubringAtPrime (v : HeightOneSpectrum R) (r : R) :
    algebraMap R K r ∈ valuationSubringAtPrime K v := by
  rw [mem_valuationSubringAtPrime_iff]
  exact v.valuation_le_one r

/-- A height-one prime is recovered from its valuation ring: $r \in v$ iff $r = 0$ or $1/r \notin R_v$. -/
theorem mem_asIdeal_iff_inv_not_mem (v : HeightOneSpectrum R) (r : R) :
    r ∈ v.asIdeal ↔ r = 0 ∨ (algebraMap R K r)⁻¹ ∉ valuationSubringAtPrime K v := by
  rw [mem_valuationSubringAtPrime_iff, map_inv₀, ← valuation_lt_one_iff_mem (K := K)]
  by_cases hr : r = 0
  · simp [hr]
  · have h0 : v.valuation K (algebraMap R K r) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr
    simp only [hr, false_or, not_le]
    constructor
    · intro h
      exact one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 h0, h⟩
    · intro h
      exact (one_lt_inv_iff₀.1 h).2

theorem valuationSubringAtPrime_injective :
    Function.Injective (fun v : HeightOneSpectrum R => valuationSubringAtPrime K v) := by
  intro v w h
  apply HeightOneSpectrum.ext
  ext r
  rw [mem_asIdeal_iff_inv_not_mem (K := K), mem_asIdeal_iff_inv_not_mem (K := K)]
  simp only at h
  rw [h]

variable (k) in
/-- **The place of a height-one prime** $v$ of a Dedekind domain $R \supseteq k$ with field of fractions $K$:
the discrete valuation ring $R_v \subseteq K$. -/
noncomputable def HeightOneSpectrum.toPrimeDivisor
    (hk : ∀ c : k, ∃ r : R, algebraMap R K r = algebraMap k K c) (v : HeightOneSpectrum R) :
    PrimeDivisor k K where
  O := valuationSubringAtPrime K v
  algebraMap_mem c := by
    obtain ⟨r, hr⟩ := hk c
    rw [← hr]
    exact algebraMap_mem_valuationSubringAtPrime v r
  isDVR := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot _

theorem HeightOneSpectrum.toPrimeDivisor_injective
    (hk : ∀ c : k, ∃ r : R, algebraMap R K r = algebraMap k K c) :
    Function.Injective (HeightOneSpectrum.toPrimeDivisor (K := K) k hk) := fun _ _ h =>
  valuationSubringAtPrime_injective (congrArg PrimeDivisor.O h)

/-- The valuation ring of a place is not all of `K` (a discrete valuation ring is not a field). -/
theorem PrimeDivisor.O_ne_top (p : PrimeDivisor k K) : p.O ≠ ⊤ := by
  intro h
  haveI := p.isDVR
  obtain ⟨x, hx, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (IsDiscreteValuationRing.not_a_field p.O)
  have hx' : (x : K)⁻¹ ∈ p.O := by
    have : (x : K)⁻¹ ∈ (⊤ : ValuationSubring K) := trivial
    rwa [← h] at this
  have hxK : (x : K) ≠ 0 := fun e => hx0 (Subtype.ext e)
  apply (IsLocalRing.mem_maximalIdeal x).1 hx
  refine IsUnit.of_mul_eq_one (⟨_, hx'⟩ : p.O) (Subtype.ext ?_)
  simp [hxK]

/-- **The places containing `R` come from height-one primes**: a place whose valuation ring contains `R` is
$R_v$ for a (unique) height-one prime $v$ of `R`. -/
theorem exists_toPrimeDivisor_iff (hk : ∀ c : k, ∃ r : R, algebraMap R K r = algebraMap k K c)
    (p : PrimeDivisor k K) :
    (∃ v, HeightOneSpectrum.toPrimeDivisor k hk v = p) ↔ ∀ r : R, algebraMap R K r ∈ p.O := by
  constructor
  · rintro ⟨v, rfl⟩ r
    exact algebraMap_mem_valuationSubringAtPrime v r
  intro hR
  let φ : R →+* p.O := (algebraMap R K).codRestrict p.O.toSubring hR
  let P : Ideal R := (IsLocalRing.maximalIdeal p.O).comap φ
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  -- an element of `R` outside `P` is a unit of `p.O`
  have hunit : ∀ s : R, s ∉ P → (algebraMap R K s)⁻¹ ∈ p.O := by
    intro s hs
    have hu : IsUnit (φ s) := by
      by_contra h
      exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu⟩ := hu
    have e : (((u⁻¹ : p.Oˣ) : p.O) : K) = (algebraMap R K s)⁻¹ := by
      rw [PrimeDivisor.coe_unit_inv, hu]
      rfl
    rw [← e]
    exact ((u⁻¹ : p.Oˣ) : p.O).2
  have hP0 : P ≠ ⊥ := by
    intro hP
    apply PrimeDivisor.O_ne_top p
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : b ∉ P := by
      rw [hP, Ideal.mem_bot]
      exact nonZeroDivisors.ne_zero hb
    rw [div_eq_mul_inv]
    exact mul_mem (hR a) (hunit b hb0)
  let v : HeightOneSpectrum R := ⟨P, inferInstance, hP0⟩
  refine ⟨v, ?_⟩
  have hle : valuationSubringAtPrime K v ≤ p.O := by
    intro x hx
    rw [mem_valuationSubringAtPrime_iff] at hx
    obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer v x hx
    have hd0 : algebraMap R K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 fun h => d.2 (h ▸ P.zero_mem)
    have : x = algebraMap R K n * (algebraMap R K d)⁻¹ := by
      rw [← hnd, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
    rw [this]
    exact mul_mem (hR n) (hunit d d.2)
  have heq := ValuationSubring.eq_of_le_of_ne_top _ hle (PrimeDivisor.O_ne_top p)
  exact PrimeDivisor.ext_O heq

end General

/-! ### The places of $\mathbb Q(X_0(N))$ -/

open Polynomial

variable {N : ℕ} [NeZero N]

theorem algebraMap_Y0_C (c : ℚ) :
    algebraMap (Y0Ring N) (X0 N) (algebraMap ℚ[X] (Y0Ring N) (C c)) = algebraMap ℚ (X0 N) c := by
  rw [← IsScalarTower.algebraMap_apply, algebraMap_polyX0_eq]
  simp

theorem exists_Y0_eq_algebraMap (c : ℚ) :
    ∃ r : Y0Ring N, algebraMap (Y0Ring N) (X0 N) r = algebraMap ℚ (X0 N) c :=
  ⟨_, algebraMap_Y0_C c⟩

/-- **The closed points of $Y_0(N)$ are places of $\mathbb Q(X_0(N))$**: the point $P$ gives the discrete
valuation ring $\mathcal O(Y_0(N))_P$. -/
@[kb "milne2006ec" "Ch. V, §2, points of X_0(N) over Q as places of Q(X_0(N)) (running text), pdf p. 195"]
noncomputable def Y0Point.toPlace (P : Y0Point N) : PrimeDivisor ℚ (X0 N) :=
  HeightOneSpectrum.toPrimeDivisor ℚ exists_Y0_eq_algebraMap P

theorem Y0Point.toPlace_injective : Function.Injective (Y0Point.toPlace (N := N)) :=
  HeightOneSpectrum.toPrimeDivisor_injective exists_Y0_eq_algebraMap

/-- Integrality over $\mathbb Q[j]$ forces membership in any valuation ring containing $j$. -/
theorem mem_O_of_isIntegral (p : PrimeDivisor ℚ (X0 N)) (hj : jX0 (prop2_4' N) ∈ p.O) {x : X0 N}
    (hx : IsIntegral ℚ[X] x) : x ∈ p.O := by
  let φ : ℚ[X] →+* p.O := eval₂RingHom p.ofBase ⟨jX0 (prop2_4' N), hj⟩
  have hc : (algebraMap p.O (X0 N)).comp φ = algebraMap ℚ[X] (X0 N) := by
    rw [algebraMap_polyX0_eq]
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (RingHom.ext_rat (((algebraMap p.O (X0 N)).comp φ).comp C)
        (((aeval (jX0 (prop2_4' N))).toRingHom).comp C)) a
    · simp [φ]
  obtain ⟨f, hfm, hf⟩ := hx
  have hint : IsIntegral p.O x := ⟨f.map φ, hfm.map φ, by rw [eval₂_map, hc]; exact hf⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := p.O) (K := X0 N)).1 hint
  rw [← hy]
  exact y.2

/-- **The places of $\mathbb Q(X_0(N))$ where $j$ is finite are exactly the points of $Y_0(N)$.** -/
theorem exists_toPlace_iff (p : PrimeDivisor ℚ (X0 N)) :
    (∃ P : Y0Point N, P.toPlace = p) ↔ jX0 (prop2_4' N) ∈ p.O := by
  show (∃ v, HeightOneSpectrum.toPrimeDivisor ℚ (exists_Y0_eq_algebraMap (N := N)) v = p) ↔ _
  rw [exists_toPrimeDivisor_iff (R := Y0Ring N) (K := X0 N)]
  constructor
  · intro h
    simpa [jY0] using h (jY0 N)
  · intro hj r
    exact mem_O_of_isIntegral p hj r.2

/-- A **cusp** of $X_0(N)$ over $\mathbb Q$: a place of $\mathbb Q(X_0(N))$ at which $j$ has a pole. -/
@[kb "milne2006ec" "Ch. V, §2, the cusps X_0(N) ∖ Y_0(N) (running text), pdf p. 195"]
def IsCusp (p : PrimeDivisor ℚ (X0 N)) : Prop := jX0 (prop2_4' N) ∉ p.O

theorem bijective_placeSum :
    Function.Bijective (Sum.elim Y0Point.toPlace Subtype.val :
      Y0Point N ⊕ {p : PrimeDivisor ℚ (X0 N) // IsCusp p} → PrimeDivisor ℚ (X0 N)) := by
  constructor
  · rintro (P | ⟨p, hp⟩) (Q | ⟨q, hq⟩) h
    · exact congrArg Sum.inl (Y0Point.toPlace_injective h)
    · exact absurd ((exists_toPlace_iff q).1 ⟨P, h⟩) hq
    · exact absurd ((exists_toPlace_iff p).1 ⟨Q, h.symm⟩) hp
    · exact congrArg Sum.inr (Subtype.ext h)
  · intro p
    by_cases h : jX0 (prop2_4' N) ∈ p.O
    · obtain ⟨P, hP⟩ := (exists_toPlace_iff p).2 h
      exact ⟨Sum.inl P, hP⟩
    · exact ⟨Sum.inr ⟨p, h⟩, rfl⟩

/-- **The points of $X_0(N)$ over $\mathbb Q$** (the places of $\mathbb Q(X_0(N))$) are the closed points of
$Y_0(N)$ together with the cusps. -/
@[kb "milne2006ec" "Ch. V, §2, X_0(N) = Y_0(N) ∪ {cusps} (running text), pdf p. 195"]
noncomputable def placeEquiv :
    PrimeDivisor ℚ (X0 N) ≃ Y0Point N ⊕ {p : PrimeDivisor ℚ (X0 N) // IsCusp p} :=
  (Equiv.ofBijective _ bijective_placeSum).symm

end NumberFieldKB.ModularCurves
