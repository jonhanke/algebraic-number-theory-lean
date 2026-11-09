import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Quaternion
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Tamagawa.SquareClassDuality

/-!
# Milne, *Class Field Theory*, Chapter VIII, Example 4.4

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §4, Example 4.4
(pdf p. 250, printed p. 241). Locators give Milne's printed page numbers (printed page = pdf page − 9).

"(a) For a finite cyclic extension of number fields $L/K$, the fundamental exact sequence becomes identified with
$0 \to K^\times/\mathrm{Nm}(L^\times) \to \bigoplus_v K_v^\times/\mathrm{Nm}(L_v^\times) \to \frac1n\mathbb Z/\mathbb Z
\to 0$, $n = [L:K]$. (b) Let $D$ be a division algebra over a number field $K$, and let $i_v = \mathrm{inv}_v(D \otimes_K
K_v)$. Then: $i_v = 0$ for all but finitely many $v$; $i_v = 0$ if $v$ is complex; $i_v \in \frac12\mathbb Z/\mathbb Z$
if $v$ is real; and $\sum i_v \equiv 0 \bmod \mathbb Z$. The family $(i_v)$ determines the isomorphism class of $D$, and
any family $(i_v)$ satisfying the conditions is the family of invariants of the division algebra. [...] For example, to
give a quaternion algebra over $\mathbb Q$ is the same as to give a set of primes of $\mathbb Q$ having an even finite
number of elements."

## What is formalized

* (a), the target: for $L/K$ cyclic of degree $n$, the image of Corollary 4.3's sum map is
  $\frac1n\mathbb Z/\mathbb Z$ (`Ch8.corollary4_3_cyclic_target`, proved). The identification of the local and global
  relative Brauer groups with norm residue groups ($H^2 \cong \hat H^0$ for cyclic groups) is not formalized here.
* (b), the quaternion case, for the quaternion algebra $H(a,b) = (a,b)_F$ ($a, b \ne 0$) over a number field $F$, with
  the ramification set $\mathrm{Ram}(a,b) = \{v : H(a,b) \otimes F_v \text{ is a division algebra}\}$ (QuadFormsKB
  `Quat.IsRamifiedAt`; equal to $\{v : (a,b)_v = -1\}$, `Quat.isRamifiedAt_iff`):
  - `example_4_4b_ramified_finite_even`: $\mathrm{Ram}(a,b)$ is finite of even cardinality (from Hilbert reciprocity,
    QuadFormsKB `Quat.ramified_finite_even`; Milne's $\sum_v i_v = 0$ with $i_v \in \{0, \frac12\}$);
  - `example_4_4b_exists_ramified`: over $\mathbb Q$, every finite set of places of even cardinality is
    $\mathrm{Ram}(a,b)$ for some $a, b \in \mathbb Q^\times$ (from the prescribed Hilbert symbols theorem, QuadFormsKB
    `PresNF.exists_prescribed_hilbert`).

That $\mathrm{Ram}(a,b)$ determines $H(a,b)$ up to isomorphism is `example_4_4b_algEquiv_iff_ramified`, and the whole
statement over $\mathbb Q$ is `example_4_4b_rat` (both in `Ch8/Example44Ram.lean`). The general statement (b) for
division algebras of degree $n$ is in Tau Ceti (`TauCeti.ClassFieldTheory.brLocalization_injective`,
`range_brLocalization`), not re-proved here.
-/

open NumberField IsDedekindDomain QuadFormsKB

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

/-- **Example 4.4 (b), quaternion algebras: the ramification set is finite and even** (Milne, *CFT*, VIII, Example 4.4,
p. 241): for $a, b \in F^\times$, $F$ a number field, the set of places where $H(a,b)$ ramifies is finite of even
cardinality. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Example 4.4(b), quaternion case: Ram finite and even, p. 241"]
theorem example_4_4b_ramified_finite_even {F : Type} [Field F] [NumberField F] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : NFPlace F | Quat.IsRamifiedAt a b v}.Finite ∧ Even {v : NFPlace F | Quat.IsRamifiedAt a b v}.ncard :=
  Quat.ramified_finite_even ha hb

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

theorem nonsq_fin (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) (hx : v.valuation ℚ x = WithZero.exp (-1 : ℤ)) :
    ¬ IsSquare (algebraMap ℚ (v.adicCompletion ℚ) x) := by
  rintro ⟨c, hc⟩
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 ℚ) (K := ℚ) (v := v) x
  have h2 : Valued.v (c * c) = WithZero.exp (-1 : ℤ) := by
    have h' : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) x) = v.valuation ℚ x := h
    rw [← hc, ← hx]; exact h'
  rw [map_mul] at h2
  have hm : Valued.v c ≠ 0 := by
    intro h0; rw [h0] at h2; exact absurd h2.symm WithZero.exp_ne_zero
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v c = WithZero.exp n :=
    ⟨WithZero.log (Valued.v c), (WithZero.exp_log hm).symm⟩
  rw [hn, ← WithZero.exp_add] at h2
  have := WithZero.exp_injective h2
  omega

theorem exists_neg_fin (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ)
    (hx : v.valuation ℚ x = WithZero.exp (-1 : ℤ)) :
    ∃ y : v.adicCompletion ℚ, y ≠ 0 ∧ hilbertSymbol (v.adicCompletion ℚ) (algebraMap ℚ _ x) y = -1 := by
  have hx0 : x ≠ 0 := by intro h; rw [h, map_zero] at hx; exact absurd hx.symm WithZero.exp_ne_zero
  have hd0 : algebraMap ℚ (v.adicCompletion ℚ) x ≠ 0 := (map_ne_zero _).mpr hx0
  set d : (v.adicCompletion ℚ)ˣ := Units.mk0 _ hd0
  have hy : (QuotientGroup.mk d : SqDual.SqCl (v.adicCompletion ℚ)) ≠ 1 := fun h1 =>
    nonsq_fin v x hx ((SqDual.mk_eq_one_iff_isSquare _ d).mp h1)
  obtain ⟨y, hy'⟩ := SqDual.hilbCl_nondeg_fin v _ hy
  induction y using QuotientGroup.induction_on with
  | H u =>
    refine ⟨u, u.ne_zero, ?_⟩
    rw [SqDual.hilbCl_mk, hilbertSymbol_comm] at hy'
    exact hy'

theorem exists_neg_inf (w : InfinitePlace ℚ) (x : ℚ) (hx : x < 0) :
    ∃ y : w.Completion, y ≠ 0 ∧ hilbertSymbol w.Completion (algebraMap ℚ _ x) y = -1 := by
  have hw : w.IsReal := by
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    exact Rat.isReal_infinitePlace
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hex : e (algebraMap ℚ w.Completion x) = (x : ℝ) := by
    rw [eq_ratCast (algebraMap ℚ w.Completion) x]; exact map_ratCast e x
  have hd0 : algebraMap ℚ w.Completion x ≠ 0 := (map_ne_zero _).mpr hx.ne
  set d : w.Completion ˣ := Units.mk0 _ hd0
  have hy : (QuotientGroup.mk d : SqDual.SqCl w.Completion) ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := (SqDual.mk_eq_one_iff_isSquare _ d).mp h1
    have h3 : e (algebraMap ℚ w.Completion x) = e c * e c := by
      rw [← map_mul]; exact congrArg e hc
    rw [hex] at h3
    have : (x : ℝ) < 0 := by exact_mod_cast hx
    nlinarith [mul_self_nonneg (e c)]
  obtain ⟨y, hy'⟩ := SqDual.hilbCl_nondeg_inf w _ hy
  induction y using QuotientGroup.induction_on with
  | H u =>
    refine ⟨u, u.ne_zero, ?_⟩
    rw [SqDual.hilbCl_mk, hilbertSymbol_comm] at hy'
    exact hy'

/-- **Example 4.4 (b), quaternion algebras over $\mathbb Q$: every even finite set of places occurs** (Milne, *CFT*,
VIII, Example 4.4, p. 241): for a finite set $T$ of places of $\mathbb Q$ with an even number of elements there are
$a, b \in \mathbb Q^\times$ such that $H(a,b)$ ramifies exactly at $T$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Example 4.4(b), quaternion algebras over Q and even sets of places, p. 241"]
theorem example_4_4b_exists_ramified (T : Set (NFPlace ℚ)) (hT : T.Finite) (hE : Even T.ncard) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧ {v : NFPlace ℚ | Quat.IsRamifiedAt a b v} = T := by
  classical
  haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom
      Rat.ringOfIntegersEquiv.symm.surjective
  have hTf : (NFPlace.finite ⁻¹' T : Set (HeightOneSpectrum (𝓞 ℚ))).Finite :=
    hT.preimage (fun x _ y _ h => NFPlace.finite.inj h)
  let π : HeightOneSpectrum (𝓞 ℚ) → 𝓞 ℚ := fun v => Submodule.IsPrincipal.generator v.asIdeal
  have hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal = Ideal.span {π v} := fun v =>
    (Ideal.span_singleton_generator _).symm
  have hπ0 : ∀ v : HeightOneSpectrum (𝓞 ℚ), π v ≠ 0 := by
    intro v h
    apply v.ne_bot
    rw [hπ v, h, Ideal.span_singleton_eq_bot.mpr rfl]
  let P : ℚ := ∏ v ∈ hTf.toFinset, algebraMap (𝓞 ℚ) ℚ (π v)
  have hP0 : P ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).mpr (hπ0 w)
  let s : ℚ := if ∃ w, NFPlace.infinite w ∈ T then -1 else 1
  let a : ℚ := s * |P|
  have hs0 : s ≠ 0 := by simp only [s]; split_ifs <;> norm_num
  have ha : a ≠ 0 := mul_ne_zero hs0 (abs_ne_zero.mpr hP0)
  have hneg : ∀ w : InfinitePlace ℚ, NFPlace.infinite w ∈ T → a < 0 := by
    intro w hw
    have : s = -1 := by simp only [s]; rw [if_pos ⟨w, hw⟩]
    simp only [a, this]
    have := abs_pos.mpr hP0
    linarith
  have hval : ∀ v : HeightOneSpectrum (𝓞 ℚ), NFPlace.finite v ∈ T →
      v.valuation ℚ a = WithZero.exp (-1 : ℤ) := by
    intro v hv
    have hs : v.valuation ℚ s = 1 := by
      simp only [s]; split_ifs <;> simp
    have habs : v.valuation ℚ |P| = v.valuation ℚ P := by
      rcases abs_choice P with h | h <;> rw [h]
      simp
    have hPv : v.valuation ℚ P = WithZero.exp (-1 : ℤ) := by
      simp only [P]
      rw [map_prod, Finset.prod_eq_single v]
      · rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_singleton v (hπ0 v) (hπ v)
      · intro w _ hwv
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
        intro hmem
        have hle : w.asIdeal ≤ v.asIdeal := by
          rw [hπ w, Ideal.span_singleton_le_iff_mem]; exact hmem
        exact hwv (HeightOneSpectrum.ext
          (Ideal.IsMaximal.eq_of_le (w.isPrime.isMaximal w.ne_bot) v.isPrime.ne_top hle))
      · intro hv'; exact absurd (hTf.mem_toFinset.mpr hv) hv'
    simp only [a]
    rw [map_mul, hs, habs, hPv, one_mul]
  let ε : Unit → NFPlace ℚ → ℤ := fun _ v => if v ∈ T then -1 else 1
  have hset : {v : NFPlace ℚ | ε () v = -1} = T := by
    ext v; by_cases h : v ∈ T <;> simp [ε, h]
  obtain ⟨b, hb0, hb⟩ := PresNF.exists_prescribed_hilbert (F := ℚ) (ι := Unit) (fun _ => a)
    (fun _ => ha) ε (fun _ v => by by_cases h : v ∈ T <;> simp [ε, h])
    (hT.subset fun v ⟨_, hi⟩ => by by_contra h; simp [ε, h] at hi)
    (fun _ => by rw [hset]; exact hE)
    (by
      intro v
      cases v with
      | infinite w =>
        dsimp only [NFPlace.atPlace]
        by_cases h : NFPlace.infinite w ∈ T
        · obtain ⟨y, hy0, hy⟩ := exists_neg_inf w a (hneg w h)
          exact ⟨y, hy0, fun _ => by simp only [ε, if_pos h]; exact hy⟩
        · exact ⟨1, one_ne_zero, fun _ => by
            simp only [ε, if_neg h]; exact hilbertSymbol_one_right _ _⟩
      | finite v =>
        dsimp only [NFPlace.atPlace]
        by_cases h : NFPlace.finite v ∈ T
        · obtain ⟨y, hy0, hy⟩ := exists_neg_fin v a (hval v h)
          exact ⟨y, hy0, fun _ => by simp only [ε, if_pos h]; exact hy⟩
        · exact ⟨1, one_ne_zero, fun _ => by
            simp only [ε, if_neg h]; exact hilbertSymbol_one_right _ _⟩)
  refine ⟨a, b, ha, hb0, ?_⟩
  ext v
  rw [Set.mem_setOf_eq, Quat.isRamifiedAt_iff ha hb0, hb () v]
  by_cases h : v ∈ T <;> simp [ε, h]

end NumberFieldKB.MilneCFT.Ch8
