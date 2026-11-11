import NumberFieldKB.MilneCFT.Ch5Ideles
import NumberFieldKB.MilneCFT.Ch7.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Topology.Algebra.Group.Units

/-!
# Open subgroups of the ideles and finite sets of primes (for Milne, *CFT*, Chapter VII, Lemma 9.3)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII,
proof of Lemma 9.3 (p. 224).

* `exists_finset_of_isOpen`: an open subgroup $U$ of $\mathbb I_K$ contains
  $\prod_{v\in S_0}\{1\}\times\prod_{v\notin S_0}U_v$ (with $1$ at the infinite places) for a finite set $S_0$ of
  primes (the topology of the ideles: `exists_box_units`).
* `exists_finite_classGroup_generators`: finitely many primes generate the ideal class group.
* `finite_primes_dvd`: a nonzero natural number lies in only finitely many primes.
-/

open IsDedekindDomain NumberField NumberFieldKB.HilbertClassField
open scoped Topology nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]

/-- An open subgroup of $\mathbb I_K$ contains every idele that is $1$ at the infinite places and at the primes of
some finite set $S_0$, and a unit at all primes. -/
theorem exists_finset_of_isOpen (U : Subgroup (IdeleGroup (𝓞 K) K))
    (hU : IsOpen (U : Set (IdeleGroup (𝓞 K) K))) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ x : IdeleGroup (𝓞 K) K,
      (∀ w : InfinitePlace K, (x : AdeleRing (𝓞 K) K).1 w = 1) →
      (∀ v ∈ S₀, (x : AdeleRing (𝓞 K) K).2 v = 1) →
      (∀ v, Valued.v ((x : AdeleRing (𝓞 K) K).2 v) = 1) → x ∈ U := by
  classical
  set e := Homeomorph.prodUnits (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) with he
  have hU1 : (U : Set (IdeleGroup (𝓞 K) K)) ∈ 𝓝 (1 : IdeleGroup (𝓞 K) K) := hU.mem_nhds U.one_mem
  have himg : e '' (U : Set (IdeleGroup (𝓞 K) K)) ∈ 𝓝 ((1 : (InfiniteAdeleRing K)ˣ), (1 : (FiniteAdeleRing (𝓞 K) K)ˣ)) := by
    have h := e.map_nhds_eq (1 : IdeleGroup (𝓞 K) K)
    have h1 : e (1 : IdeleGroup (𝓞 K) K) = (1, 1) := rfl
    rw [h1] at h
    rw [← h]
    exact Filter.image_mem_map hU1
  rw [nhds_prod_eq, Filter.mem_prod_iff] at himg
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := himg
  obtain ⟨S, ε, hε, hbox⟩ := exists_box_units ht₂
  refine ⟨S, fun x h1 h2 h3 => ?_⟩
  have hinf : (e x).1 = 1 := by
    apply Units.ext
    funext w
    exact h1 w
  have hv1 : ∀ v, Valued.v (((e x).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := h3
  have hinv : ∀ v, Valued.v ((((e x).2⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
    intro v
    have h := QuadFormsKB.Tamagawa.Measure.Weil.valued_mul_inv (e x).2 v
    rw [hv1 v, one_mul] at h
    exact h
  have hone : ∀ v ∈ S, ((e x).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := h2
  have hmem : e x ∈ e '' (U : Set (IdeleGroup (𝓞 K) K)) := by
    refine hsub ⟨?_, hbox _ (fun v => (hv1 v).le) (fun v => (hinv v).le) ?_ ?_⟩
    · rw [hinf]; exact mem_of_mem_nhds ht₁
    · intro v hv
      rw [hone v hv, sub_self, map_zero]
      exact zero_lt_iff.2 (hε v)
    · intro v hv
      have hm : ((e x).2 : FiniteAdeleRing (𝓞 K) K) v *
          ((((e x).2⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
        rw [show ((e x).2 : FiniteAdeleRing (𝓞 K) K) v *
          ((((e x).2⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) =
          ((((e x).2 * (e x).2⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ)) : FiniteAdeleRing (𝓞 K) K) v from rfl,
          mul_inv_cancel]
        rfl
      rw [hone v hv, one_mul] at hm
      rw [hm, sub_self, map_zero]
      exact zero_lt_iff.2 (hε v)
  obtain ⟨y, hy, hyx⟩ := hmem
  rwa [← e.injective hyx]

variable (K) in
/-- Finitely many primes generate the ideal class group (every class is the class of an integral ideal, a product
of primes, and the class group is finite). -/
theorem exists_finite_classGroup_generators : ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧
    Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤ := by
  classical
  have hfin : (Set.range (primeClass K)).Finite := Set.toFinite _
  have htop : Subgroup.closure (Set.range (primeClass K)) = ⊤ := by
    rw [eq_top_iff]
    rintro c -
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    obtain ⟨I, hI⟩ := I
    have key : ∀ (J : Ideal (𝓞 K)) (hJ : J ∈ (Ideal (𝓞 K))⁰),
        ClassGroup.mk0 ⟨J, hJ⟩ ∈ Subgroup.closure (Set.range (primeClass K)) := by
      intro J
      induction J using UniqueFactorizationMonoid.induction_on_prime with
      | h₁ => intro hJ; exact absurd rfl (nonZeroDivisors.ne_zero hJ)
      | h₂ J hJu =>
        intro hJ
        have : (⟨J, hJ⟩ : (Ideal (𝓞 K))⁰) = 1 := by
          apply Subtype.ext
          exact (Ideal.isUnit_iff.1 hJu).trans Ideal.one_eq_top.symm
        rw [this, map_one]; exact Subgroup.one_mem _
      | h₃ a p ha hp ih =>
        intro hJ
        have hp0 : p ≠ ⊥ := hp.ne_zero
        have ha0 : a ≠ 0 := fun h => by simp [h] at hJ
        have hpa : p ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hp.ne_zero
        have haa : a ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero ha0
        have : (⟨p * a, hJ⟩ : (Ideal (𝓞 K))⁰) = ⟨p, hpa⟩ * ⟨a, haa⟩ := rfl
        rw [this, map_mul]
        refine Subgroup.mul_mem _ ?_ (ih haa)
        have := Ideal.isPrime_of_prime hp
        exact Subgroup.subset_closure ⟨⟨p, this, hp.ne_zero⟩, rfl⟩
    exact key I hI
  obtain ⟨t, -, ht, hct⟩ := Set.exists_subset_image_finite_and (f := primeClass K) (s := Set.univ)
    (p := fun t => Subgroup.closure t = ⊤) |>.1
    ⟨Set.range (primeClass K), by simp, hfin, htop⟩
  exact ⟨t, ht, hct⟩

variable (K) in
/-- A nonzero natural number lies in only finitely many primes of $\mathcal O_K$. -/
theorem finite_primes_dvd (n : ℕ) (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : (n : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : Ideal.span {(n : 𝓞 K)} ≠ 0 := by simpa using h0
  refine (Ideal.finite_factors h1).subset ?_
  intro v hv
  show v.asIdeal ∣ Ideal.span {(n : 𝓞 K)}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

end NumberFieldKB.MilneCFT.Ch7
