import NumberFieldKB.WeilBNT.FunctionField.Place
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Places and Dedekind models (Weil III.§1, function-field case)

A place is determined by its valuation, up to equivalence, and by its valuation ring (`Place.eq_of_isEquiv`,
`Place.integers_injective`, `Place.eq_of_integers_le`; Tau Ceti has the same three statements as
`TauCeti.Place.eq_of_isEquiv`, `integers_injective`, `eq_of_integers_le` in
`TauCeti/FieldTheory/FunctionField/Place/Basic.lean`, restated here for our `Place`).

For a Dedekind domain $A\subset k$ with fraction field $k$ (a *model*), the places whose valuation ring contains
$A$ are exactly the places at the nonzero primes of $A$, each exactly once:
* **`Place.exists_eq_ofHeightOneSpectrum`**: if $v(a)\le1$ for all $a\in A$, then $v$ is the place of a (unique)
  nonzero prime $\mathfrak p=\{a\in A: v(a)<1\}$;
* **`Place.ofHeightOneSpectrum_injective`**, **`Place.valuation_ofHeightOneSpectrum_algebraMap_le_one`**.
* **`Place.finite_setOf_valuation_ne_one_of_le_one`**: for $f\ne0$ in $k$, only finitely many places with
  $A\subset\mathfrak r_v$ have $v(f)\ne1$.
-/

open scoped WithZero
open Valuation IsDedekindDomain

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

namespace Place

variable {Fq k : Type*} [Field Fq] [Field k] [Algebra Fq k]

/-- Two equivalent surjective `ℤᵐ⁰`-valued valuations are equal (direct argument; same statement as Tau Ceti's
`eq_of_isEquiv_of_surjective`, adapted from Tau Ceti, Apache 2.0). -/
private theorem eq_of_isEquiv_of_surjective' {F : Type*} [Field F] {v w : Valuation F ℤᵐ⁰}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) : v = w := by
  obtain ⟨t, ht⟩ := hv (WithZero.exp (-1))
  have ht0 : t ≠ 0 := fun h' => WithZero.exp_ne_zero (ht.symm.trans (h' ▸ map_zero v))
  have hwt0 : w t ≠ 0 := fun h' => ht0 (v.zero_iff.mp (h.eq_zero.mpr h'))
  have hwt1 : w t < 1 := h.lt_one_iff_lt_one.mp
    (by rw [ht, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num))
  obtain ⟨n, hn⟩ : ∃ n : ℤ, w t = WithZero.exp (-n) :=
    ⟨-WithZero.log (w t), by simp [WithZero.exp_log hwt0]⟩
  have hnpos : 0 < n := by
    rw [hn, ← WithZero.exp_zero] at hwt1
    have := WithZero.exp_lt_exp.mp hwt1
    omega
  have key : ∀ x : F, x ≠ 0 → ∀ a : ℤ, v x = WithZero.exp a → w x = WithZero.exp (n * a) := by
    intro x hx a hxa
    have h1 : v (x * t ^ a) = 1 := by
      rw [map_mul, map_zpow₀, ht, hxa, ← WithZero.exp_zsmul, smul_eq_mul, ← WithZero.exp_add]
      simp
    have h2 : w (x * t ^ a) = 1 := h.eq_one_iff_eq_one.mp h1
    rw [map_mul, map_zpow₀, hn, ← WithZero.exp_zsmul, smul_eq_mul] at h2
    have : w x = (WithZero.exp (a * -n))⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [this, ← WithZero.exp_neg]
    congr 1
    ring
  obtain ⟨y, hy⟩ := hw (WithZero.exp 1)
  have hy0 : y ≠ 0 := fun h' => WithZero.exp_ne_zero (hy.symm.trans (h' ▸ map_zero w))
  have hvy0 : v y ≠ 0 := by simpa using hy0
  have h3 := key y hy0 (WithZero.log (v y)) (by simp [WithZero.exp_log hvy0])
  rw [hy, WithZero.exp_inj] at h3
  have hn1 : n = 1 := Int.eq_one_of_mul_eq_one_right hnpos.le h3.symm
  refine Valuation.ext fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hvx : v x ≠ 0 := by simpa using hx
  rw [key x hx (WithZero.log (v x)) (by simp [WithZero.exp_log hvx]), hn1, one_mul,
    WithZero.exp_log hvx]

/-- Two places with equivalent valuations are equal (normalization). -/
theorem eq_of_isEquiv {v w : Place Fq k} (h : v.valuation.IsEquiv w.valuation) : v = w :=
  ext (eq_of_isEquiv_of_surjective' v.valuation_surjective w.valuation_surjective h)

/-- A place is determined by its valuation ring. -/
theorem integers_injective : Function.Injective (integers : Place Fq k → ValuationSubring k) :=
  fun _ _ h => eq_of_isEquiv ((Valuation.isEquiv_iff_valuationSubring _ _).mpr h)

/-- The valuation ring of a place is a maximal proper subring: containment of valuation rings is equality of
places. -/
theorem eq_of_integers_le {v w : Place Fq k} (h : v.integers ≤ w.integers) : v = w :=
  integers_injective (ValuationSubring.eq_of_le_of_ne_top _ h w.integers_ne_top)

/-- $\mathfrak r_v$ is integrally closed in $k$. -/
theorem mem_integers_of_isIntegral (v : Place Fq k) {R : Type*} [CommRing R] [Algebra R k]
    (hR : ∀ r : R, algebraMap R k r ∈ v.integers) {y : k} (hy : IsIntegral R y) : y ∈ v.integers := by
  let f : R →+* v.valuation.integer := (algebraMap R k).codRestrict _ hR
  obtain ⟨p, hm, hp⟩ := hy
  have hI : v.valuation.Integers v.valuation.integer := Valuation.integer.integers v.valuation
  refine hI.mem_of_integral (x := y) ⟨p.map f, hm.map f, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hp

section Model

variable [Finite Fq] (A : Type*) [CommRing A] [IsDedekindDomain A] [Algebra A k] [IsFractionRing A k]

theorem valuation_ofHeightOneSpectrum_algebraMap_le_one (p : HeightOneSpectrum A) (a : A) :
    (ofHeightOneSpectrum (Fq := Fq) A p).valuation (algebraMap A k a) ≤ 1 :=
  p.valuation_le_one _

theorem ofHeightOneSpectrum_injective :
    Function.Injective (ofHeightOneSpectrum (Fq := Fq) (k := k) A) := by
  intro p q h
  exact HeightOneSpectrum.valuation_injective (K := k) (congrArg Place.valuation h)

/-- **Every place whose valuation ring contains the model $A$ is the place of a nonzero prime of $A$.** -/
theorem exists_eq_ofHeightOneSpectrum (v : Place Fq k)
    (hv : ∀ a : A, v.valuation (algebraMap A k a) ≤ 1) :
    ∃ p : HeightOneSpectrum A, v = ofHeightOneSpectrum A p := by
  let I : Ideal A :=
    { carrier := {a | v.valuation (algebraMap A k a) < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at *
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv c)) ha }
  have hmem : ∀ a, a ∈ I ↔ v.valuation (algebraMap A k a) < 1 := fun a => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have := (hmem 1).mp (h ▸ Submodule.mem_top)
      simp at this
    · rw [hmem, map_mul, map_mul] at hab
      rw [hmem, hmem]
      by_contra hc
      push Not at hc
      have ha1 : v.valuation (algebraMap A k a) = 1 := le_antisymm (hv a) hc.1
      have hb1 : v.valuation (algebraMap A k b) = 1 := le_antisymm (hv b) hc.2
      rw [ha1, hb1] at hab
      simp at hab
  have hne : I ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := v.valuation_surjective (WithZero.exp (-1))
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := A) x
    have hxlt : v.valuation x < 1 := by
      rw [hx, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
    have hx0 : v.valuation x ≠ 0 := by rw [hx]; exact WithZero.exp_ne_zero
    have hb0 : v.valuation (algebraMap A k b) ≠ 0 := by
      intro h0
      rw [← hab, map_div₀, h0] at hx0
      simp at hx0
    have hxb : v.valuation x * v.valuation (algebraMap A k b) = v.valuation (algebraMap A k a) := by
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
      have : v.valuation x * v.valuation (algebraMap A k b) < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_right' (hv b)) hxlt
      rw [hxb] at this
      exact absurd ha (not_le.mpr this)
  let p : HeightOneSpectrum A := ⟨I, hprime, hne⟩
  refine ⟨p, (eq_of_integers_le (v := ofHeightOneSpectrum (Fq := Fq) A p) (w := v) ?_).symm⟩
  show (p.valuation k).valuationSubring ≤ v.integers
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rintro x ⟨a, s, hs, rfl⟩
  have hs1 : v.valuation (algebraMap A k s) = 1 := by
    refine le_antisymm (hv s) (not_lt.mp fun h => hs ((hmem s).mpr h))
  show v.valuation (algebraMap A k a * (algebraMap A k s)⁻¹) ≤ 1
  rw [map_mul, map_inv₀, hs1]
  simpa using hv a

/-- For $f\ne0$, only finitely many places containing the model have $v(f)\ne1$. -/
theorem finite_setOf_valuation_ne_one_of_le_one {f : k} (hf : f ≠ 0) :
    {v : Place Fq k | (∀ a : A, v.valuation (algebraMap A k a) ≤ 1) ∧ v.valuation f ≠ 1}.Finite := by
  have hfin : ({p : HeightOneSpectrum A | 1 < p.valuation k f} ∪
      {p : HeightOneSpectrum A | 1 < p.valuation k f⁻¹}).Finite :=
    (HeightOneSpectrum.Support.finite (K := k) A f).union (HeightOneSpectrum.Support.finite (K := k) A f⁻¹)
  refine (hfin.image (ofHeightOneSpectrum (Fq := Fq) (k := k) A)).subset ?_
  rintro v ⟨hv, hne⟩
  obtain ⟨p, rfl⟩ := exists_eq_ofHeightOneSpectrum A v hv
  refine ⟨p, ?_, rfl⟩
  have hne' : p.valuation k f ≠ 1 := hne
  rcases lt_or_gt_of_ne hne' with h | h
  · right
    show 1 < p.valuation k f⁻¹
    rw [map_inv₀]
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hf), h⟩
  · exact Or.inl h

end Model

end Place

end NumberFieldKB.WeilBNT.FF
