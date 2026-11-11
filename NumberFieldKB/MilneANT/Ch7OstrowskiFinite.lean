import NumberFieldKB.MilneANT.Ch7Places
import NumberFieldKB.MilneANT.Ch7Basic
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Milne, *Algebraic Number Theory*, Theorem 7.14: the finite primes

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

Every nontrivial nonarchimedean absolute value on a number field $K$ is equivalent to the $\mathfrak p$-adic absolute
value of a nonzero prime ideal (`exists_finitePlace_isEquiv`). The argument is Milne's for $\mathbb Q$ (Theorem 7.12,
case (ii)) carried over to $\mathcal O_K$: $\mathcal O_K$ lies in the valuation ring, $\mathfrak p = \{x \in \mathcal O_K
: |x| < 1\}$ is a nonzero prime, and the two absolute values have the same elements of value $< 1$.
-/

open NumberField IsDedekindDomain

namespace NumberFieldKB.MilneANT

/-- A nonarchimedean absolute value is at most one on the ring of integers of a number field. -/
theorem abv_le_one_of_nonarch {K : Type*} [Field K] [NumberField K] (v : AbsoluteValue K ℝ)
    (hna : IsNonarchimedean v) (x : 𝓞 K) : v (algebraMap (𝓞 K) K x) ≤ 1 := by
  have hint : IsIntegral ℤ (algebraMap (𝓞 K) K x) := x.isIntegral_coe
  have hint' : IsIntegral (absValuationSubring v hna) (algebraMap (𝓞 K) K x) :=
    hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  rw [← hy]
  exact y.2

/-- **Theorem 7.14, finite primes**: every nonarchimedean nontrivial absolute value on a number field is equivalent
to the absolute value of a finite place (the $\mathfrak p$-adic absolute value of a nonzero prime ideal). -/
@[kb "milne2020ant" "v3.08, Thm. 7.14, p. 111"]
theorem exists_finitePlace_isEquiv {K : Type*} [Field K] [NumberField K] (v : AbsoluteValue K ℝ)
    (hv : v.IsNontrivial) (hna : IsNonarchimedean v) : ∃ w : FinitePlace K, v.IsEquiv w.1 := by
  have hle := abv_le_one_of_nonarch v hna
  let P : Ideal (𝓞 K) :=
    { carrier := {x | v (algebraMap (𝓞 K) K x) < 1}
      add_mem' := fun {a b} ha hb => by
        have := hna (algebraMap (𝓞 K) K a) (algebraMap (𝓞 K) K b)
        show v (algebraMap (𝓞 K) K (a + b)) < 1
        rw [map_add]
        exact lt_of_le_of_lt this (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        show v (algebraMap (𝓞 K) K (c • x)) < 1
        rw [smul_eq_mul, map_mul, map_mul]
        have h1 := hle c
        have h2 : v (algebraMap (𝓞 K) K x) < 1 := hx
        calc v _ * v _ ≤ 1 * v (algebraMap (𝓞 K) K x) :=
              mul_le_mul_of_nonneg_right h1 (v.nonneg _)
          _ < 1 := by rw [one_mul]; exact h2 }
  have hmem : ∀ x, x ∈ P ↔ v (algebraMap (𝓞 K) K x) < 1 := fun x => Iff.rfl
  have hprime : P.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have := (hmem 1).1 (h ▸ Submodule.mem_top)
      simp at this
    · rw [hmem, map_mul, map_mul] at hab
      by_contra hcon
      push Not at hcon
      rw [hmem, hmem, not_lt, not_lt] at hcon
      have := one_le_mul_of_one_le_of_one_le hcon.1 hcon.2
      linarith
  have hv1 : ∀ x : 𝓞 K, x ∉ P → v (algebraMap (𝓞 K) K x) = 1 := fun x hx =>
    le_antisymm (hle x) (not_lt.1 (fun h => hx ((hmem x).2 h)))
  have hne : P ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx0, hx1⟩ := hv
    apply hx1
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hx0
      rw [← hab]; simp
    have hnb : ∀ y : 𝓞 K, y ≠ 0 → y ∉ P := fun y hy hyP => by
      rw [hbot] at hyP
      exact hy (by simpa using hyP)
    rw [← hab, map_div₀, hv1 a (hnb a ha0), hv1 b (hnb b hb0)]
    simp
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨P, hprime, hne⟩
  have hwlt : ∀ x : 𝓞 K, (FinitePlace.mk 𝔭).1 (algebraMap (𝓞 K) K x) < 1 ↔ x ∈ P := fun x =>
    FinitePlace.norm_lt_one_iff_mem K 𝔭 x
  have hwle : ∀ x : 𝓞 K, (FinitePlace.mk 𝔭).1 (algebraMap (𝓞 K) K x) ≤ 1 := fun x =>
    FinitePlace.norm_le_one K 𝔭 x
  have hw1 : ∀ x : 𝓞 K, x ∉ P → (FinitePlace.mk 𝔭).1 (algebraMap (𝓞 K) K x) = 1 := fun x hx =>
    le_antisymm (hwle x) (not_lt.1 (fun h => hx ((hwlt x).1 h)))
  refine ⟨FinitePlace.mk 𝔭, ?_⟩
  refine (AbsoluteValue.isEquiv_of_lt_one_imp (FinitePlace.isNontrivial_milne K _) ?_).symm
  intro x hx
  obtain ⟨n, d, h | h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := K) 𝔭 x
  · have hd : d.1 ∉ P := d.2
    have e1 := congrArg (FinitePlace.mk 𝔭).1 h
    rw [map_mul, hw1 d.1 hd, mul_one] at e1
    have hn : n ∈ P := (hwlt n).1 (by rw [← e1]; exact hx)
    have e2 := congrArg v h
    rw [map_mul, hv1 d.1 hd, mul_one] at e2
    rw [e2]
    exact (hmem n).1 hn
  · have hd : d.1 ∉ P := d.2
    have e1 := congrArg (FinitePlace.mk 𝔭).1 h
    rw [map_mul, hw1 d.1 hd] at e1
    have := mul_le_mul_of_nonneg_left (hwle n) ((FinitePlace.mk 𝔭).1.nonneg x)
    rw [mul_one] at this
    linarith

end NumberFieldKB.MilneANT
