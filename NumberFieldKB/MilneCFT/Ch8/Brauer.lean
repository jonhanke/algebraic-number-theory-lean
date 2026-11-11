import NumberFieldKB.MilneCFT.Ch8.Basic
import NumberFieldKB.MilneCFT.Ch7
import NumberFieldKB.MilneCFT.Ch4
import NumberFieldKB.Chebotarev.Unconditional
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# Milne, *Class Field Theory*, Chapter VIII §4: the fundamental exact sequence and the fundamental class

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §4,
printed pp. 239–243 (printed page = pdf page − 9).

* $\mathrm{Br}(L/K) = H^2(\mathrm{Gal}(L/K), L^\times)$ and $H^2(L/K) = H^2(\mathrm{Gal}(L/K), C_L)$ (definitions in
  prose, p. 239): `Ch4.relBrauer` (Chapter IV, the classes split by $L$; Chapter IV, Theorem 3.14 identifies it with
  $H^2$) and `H2C` (Mathlib's `groupCohomology` of Chapter VII's $G$-module `ideleClassRep`).
* **Lemma 4.1** (`lemma_4_1`, `lemma_4_1_density`): proved, from the Chebotarev density theorem (Milne uses the
  reciprocity law).
* **Theorem 4.2** (the fundamental exact sequence): Chapter IV's named `Ch4.Example2_14e` (same statement).
* **Example 4.5** (`example_4_5`): proved.
* **Theorem 4.7** (`Theorem4_7`), **Theorem 4.8** (norm limitation, `Theorem4_8`): named statements. (Chapter VII's named
  `NormLimitation` would follow from Theorem 4.8 and transitivity of the idèle class norm in arbitrary towers, which
  NumberFieldKB has only for Galois towers.)
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev Filter
open scoped Topology

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable (K : Type) [Field K] [NumberField K]

/-- $H^2(L/K) = H^2(\mathrm{Gal}(L/K), C_L)$ (definition in prose; Milne, *CFT*, VIII, §4, p. 239). -/
@[kb "milne2020cft" "Ch. VIII, §4, p. 239 (H^2(L/K) = H^2(Gal(L/K), C_L))"]
abbrev H2C (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :=
  groupCohomology (Ch7.ideleClassRep K L) 2

/-- For a prime `v` unramified in `L` and `Q` above it, the Frobenius element `frobAt K L v Q` has order the residue
degree $f(Q \mid v)$. -/
theorem orderOf_frobAt_eq_inertiaDeg (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ unramifiedPrimes K L) (Q : v.asIdeal.primesOver (𝓞 L)) :
    orderOf (frobAt K L v Q) = Q.1.inertiaDeg (𝓞 K) := by
  haveI := Q.2.1
  haveI := isMaximal_of_mem_primesOver K L v Q
  haveI : Finite (𝓞 L ⧸ Q.1) :=
    finite_quotient_of_ne_bot Q.1 (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.1)
  haveI : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := hv Q.1 Q.2.1 Q.2.2
  exact orderOf_arithFrobAt_nf Q.1

/-- In a commutative Galois group, the Frobenius class of `v` is `mk g` iff `frobAt K L v Q = g`. -/
theorem frobClass_eq_mk_iff (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (hcyc : IsCyclic Gal(L/K)) (v : HeightOneSpectrum (𝓞 K)) (Q : v.asIdeal.primesOver (𝓞 L))
    (g : Gal(L/K)) : frobClass K L v = ConjClasses.mk g ↔ frobAt K L v Q = g := by
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  rw [frobClass_eq_mk_frobAt K L v Q, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq]

/-- **Lemma 4.1** (Milne, *CFT*, VIII, Lemma 4.1, p. 240): if $L/K$ is cyclic of degree $n$, then $n = n_0 =
\mathrm{lcm}(n_v)$, the least common multiple of the local degrees $n_v = e f$: every common multiple of the local
degrees at the finite primes is divisible by $n$. -/
@[kb "milne2020cft" "Ch. VIII, Lemma 4.1, p. 240"]
theorem lemma_4_1 (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (hcyc : IsCyclic Gal(L/K))
    (m : ℕ) (hm : ∀ (v : HeightOneSpectrum (𝓞 K)) (Q : v.asIdeal.primesOver (𝓞 L)),
      Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K) ∣ m) :
    Module.finrank K L ∣ m := by
  classical
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hn : orderOf g = Module.finrank K L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ← IsGaloisGroup.card_eq_finrank Gal(L/K) K L, Nat.card_eq_fintype_card]
  have hd := chebotarev_unconditional K L (ConjClasses.mk g)
  have hne : (frobSet K L (ConjClasses.mk g)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hd
    have h0 := tendsto_nhds_unique hd (NumberField.Set.hasDirichletDensity_empty (K := K))
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    have hc : Nat.card (ConjClasses.mk g).carrier = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨⟨g, ConjClasses.mem_carrier_mk⟩⟩⟩
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq] at ha hb
      exact Subtype.ext (ha.trans hb.symm)
    rw [hc] at h0
    have : (0 : ℝ) < ((1 : ℕ) : ℝ) / (Nat.card Gal(L/K) : ℝ) := by
      have : 0 < Nat.card Gal(L/K) := Nat.card_pos
      positivity
    simp only [Nat.cast_one] at h0 this
    linarith
  obtain ⟨v, hvu, hvc⟩ := hne
  obtain ⟨Q⟩ : Nonempty (v.asIdeal.primesOver (𝓞 L)) := inferInstance
  have h1 := (frobClass_eq_mk_iff K L hcyc v Q g).1 hvc
  have h2 := orderOf_frobAt_eq_inertiaDeg K L hvu Q
  rw [h1, hn] at h2
  rw [h2]
  exact (Dvd.intro_left _ rfl).trans (hm v Q)

/-- **Lemma 4.1, the analytic refinement** (Milne, *CFT*, VIII, Lemma 4.1, bracketed remark, p. 240): for $L/K$
cyclic of degree $n$, the set of primes $v$ (unramified, with $L_w/K_v$ cyclic of order $n$, i.e. $f = n$) has
Dirichlet density $\varphi(n)/n$. -/
@[kb "milne2020cft" "Ch. VIII, Lemma 4.1, p. 240 (density φ(n)/n)"]
theorem lemma_4_1_density (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (hcyc : IsCyclic Gal(L/K)) :
    {v : HeightOneSpectrum (𝓞 K) | v ∈ unramifiedPrimes K L ∧
        ∀ Q : v.asIdeal.primesOver (𝓞 L), Q.1.inertiaDeg (𝓞 K) = Module.finrank K L}.HasDirichletDensity
      ((Module.finrank K L).totient / Module.finrank K L) := by
  classical
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  haveI : Fintype Gal(L/K) := Fintype.ofFinite _
  have hcard : Fintype.card Gal(L/K) = Module.finrank K L := by
    rw [← IsGaloisGroup.card_eq_finrank Gal(L/K) K L, Nat.card_eq_fintype_card]
  set n := Module.finrank K L with hnn
  let ι := {g : Gal(L/K) // orderOf g = n}
  let S : ι → Set (HeightOneSpectrum (𝓞 K)) := fun g => frobSet K L (ConjClasses.mk g.1)
  have hset : {v : HeightOneSpectrum (𝓞 K) | v ∈ unramifiedPrimes K L ∧
        ∀ Q : v.asIdeal.primesOver (𝓞 L), Q.1.inertiaDeg (𝓞 K) = n} = ⋃ g, S g := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, S, frobSet]
    constructor
    · rintro ⟨hv, hf⟩
      obtain ⟨Q⟩ : Nonempty (v.asIdeal.primesOver (𝓞 L)) := inferInstance
      have ho := orderOf_frobAt_eq_inertiaDeg K L hv Q
      rw [hf Q] at ho
      exact ⟨⟨frobAt K L v Q, ho⟩, hv, (frobClass_eq_mk_iff K L hcyc v Q _).2 rfl⟩
    · rintro ⟨g, hv, hc⟩
      refine ⟨hv, fun Q => ?_⟩
      have h1 := (frobClass_eq_mk_iff K L hcyc v Q g.1).1 hc
      rw [← orderOf_frobAt_eq_inertiaDeg K L hv Q, h1, g.2]
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro g h hgh
    refine Set.disjoint_left.2 fun v hg hh => hgh ?_
    obtain ⟨Q⟩ : Nonempty (v.asIdeal.primesOver (𝓞 L)) := inferInstance
    have e1 := (frobClass_eq_mk_iff K L hcyc v Q g.1).1 hg.2
    have e2 := (frobClass_eq_mk_iff K L hcyc v Q h.1).1 hh.2
    exact Subtype.ext (e1.symm.trans e2)
  have hden : ∀ g : ι, (S g).HasDirichletDensity (1 / (n : ℝ)) := by
    intro g
    have := chebotarev_unconditional K L (ConjClasses.mk g.1)
    have hc : Nat.card (ConjClasses.mk g.1).carrier = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨⟨g.1, ConjClasses.mem_carrier_mk⟩⟩⟩
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq] at ha hb
      exact Subtype.ext (ha.trans hb.symm)
    rw [hc, Nat.card_eq_fintype_card, hcard] at this
    simpa using this
  have hιcard : Fintype.card ι = n.totient := by
    rw [← IsCyclic.card_orderOf_eq_totient (α := Gal(L/K)) (d := n) (by rw [hcard])]
    rw [Fintype.card_subtype]
  rw [hset]
  have hsum : (⋃ g, S g).HasDirichletDensity (∑ g : ι, 1 / (n : ℝ)) := by
    rw [hasDirichletDensity_iff]
    have : Filter.Tendsto (fun s => ∑ g : ι, dirichletRatio (S g) s) (𝓝[>] 1)
        (nhds (∑ g : ι, 1 / (n : ℝ))) :=
      tendsto_finsetSum _ fun g _ => (hasDirichletDensity_iff _ _).1 (hden g)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    exact (dirichletRatio_iUnion S hdisj hs).symm
  convert hsum using 1
  rw [Finset.sum_const, Finset.card_univ, hιcard, nsmul_eq_mul]
  ring

/-- **Theorem 4.2, the fundamental exact sequence** (Milne, *CFT*, VIII, Theorem 4.2, p. 241): for every number field
$K$ the sequence $0 \to \mathrm{Br}(K) \to \bigoplus_v \mathrm{Br}(K_v) \xrightarrow{\Sigma} \mathbb Q/\mathbb Z \to 0$
is exact. This is the same statement as Chapter IV, Example 2.14 (e), which is a named statement there
(`Ch4.Example2_14e`); this theorem is the pointer. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 4.2, p. 241 (input: Ch. IV Example 2.14 (e))"]
theorem theorem_4_2 (h : Ch4.Example2_14e K) : Ch4.Example2_14e K := h

section Example45Helpers

open Polynomial

/-- Helper for `example_4_5`. -/
theorem ex45_nsq (n : ℕ) (h : ¬ IsSquare n) (q : ℚ) : q ^ 2 ≠ n := by
  intro hq
  apply h
  have : IsSquare (n : ℚ) := ⟨q, by rw [← hq]; ring⟩
  exact (Rat.isSquare_natCast_iff).1 this

/-- Helper for `example_4_5`. -/
theorem ex45_ns13 : ¬ IsSquare (13:ℕ) := by
  rintro ⟨r, hr⟩; have : r ≤ 4 := by nlinarith
  interval_cases r <;> omega
/-- Helper for `example_4_5`. -/
theorem ex45_ns17 : ¬ IsSquare (17:ℕ) := by
  rintro ⟨r, hr⟩; have : r ≤ 5 := by nlinarith
  interval_cases r <;> omega
/-- Helper for `example_4_5`. -/
theorem ex45_ns221 : ¬ IsSquare (221:ℕ) := by
  rintro ⟨r, hr⟩; have : r ≤ 15 := by nlinarith
  interval_cases r <;> omega

/-- Helper for `example_4_5`. -/
theorem ex45_pbtest (L : Type) [Field L] [CharZero L] (s : L) (hs : IsIntegral ℚ s) (h2 : (minpoly ℚ s).natDegree = 2)
   (x : L) (hx : x ∈ IntermediateField.adjoin ℚ {s}) : ∃ a b : ℚ, x = (a : L) + b * s := by
  let pb := IntermediateField.adjoin.powerBasis hs
  have hd : pb.dim = 2 := by simp [pb, IntermediateField.adjoin.powerBasis_dim, h2]
  obtain ⟨f, hf, hxf⟩ := pb.exists_eq_aeval (⟨x, hx⟩ : IntermediateField.adjoin ℚ {s})
  rw [hd] at hf
  have := Polynomial.eq_X_add_C_of_natDegree_le_one (show f.natDegree ≤ 1 by omega)
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  have h3 := congrArg (fun y : IntermediateField.adjoin ℚ {s} => (y : L)) hxf
  simp only at h3
  rw [h3, this]
  simp [pb, IntermediateField.adjoin.powerBasis_gen]
  ring

/-- Helper for `example_4_5`. -/
theorem ex45_partA (L : Type) [Field L] [NumberField L] (s t : L) (hs : s ^ 2 = 13) (ht : t ^ 2 = 17)
    (hg : IntermediateField.adjoin ℚ ({s, t} : Set L) = ⊤) : Module.finrank ℚ L = 4 := by
  have hsI : IsIntegral ℚ s := Algebra.IsIntegral.isIntegral s
  have q13 : Irreducible (X ^ 2 - C (13 : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => ex45_nsq 13 ex45_ns13 b (by exact_mod_cast hb))
  have hmin : minpoly ℚ s = X ^ 2 - C (13 : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic q13 (by simp [hs]) (monic_X_pow_sub_C _ two_ne_zero)).symm
  have h2 : (minpoly ℚ s).natDegree = 2 := by rw [hmin, natDegree_X_pow_sub_C]
  have hF : Module.finrank ℚ (IntermediateField.adjoin ℚ {s}) = 2 := by
    rw [IntermediateField.adjoin.finrank hsI, h2]
  set F := IntermediateField.adjoin ℚ {s} with hFdef
  have key : ∀ b : F, b ^ 2 ≠ (17 : F) := by
    intro b hb
    have hb' : ((b : L)) ^ 2 = 17 := by
      have h := congrArg (fun y : F => (y : L)) hb
      simp only [IntermediateField.coe_pow] at h
      rw [h]; norm_cast
    obtain ⟨a, c, hac⟩ := ex45_pbtest L s hsI h2 b b.2
    rw [hac] at hb'
    have e1 : ((a ^ 2 + 13 * c ^ 2 - 17 : ℚ) : L) + ((2 * a * c : ℚ) : L) * s = 0 := by
      push_cast
      linear_combination hb' - (c : L) ^ 2 * hs
    by_cases hc : (2 * a * c : ℚ) = 0
    · rw [hc] at e1
      simp at e1
      have e2 : a ^ 2 + 13 * c ^ 2 = 17 := by
        have : ((a ^ 2 + 13 * c ^ 2 : ℚ) : L) = ((17 : ℚ) : L) := by
          push_cast; linear_combination e1
        exact_mod_cast this
      rcases mul_eq_zero.1 (show (2 * a) * c = 0 by linarith) with h | h
      · have : a = 0 := by linarith
        subst this
        have : (13 * c) ^ 2 = (221 : ℕ) := by push_cast; linarith
        exact ex45_nsq 221 ex45_ns221 _ this
      · subst h
        have : a ^ 2 = (17 : ℕ) := by push_cast; linarith
        exact ex45_nsq 17 ex45_ns17 _ this
    · have hq : ((2 * a * c : ℚ) : L) ≠ 0 := by exact_mod_cast hc
      have hs' : ∃ r : ℚ, s = (r : L) := by
        refine ⟨-(a ^ 2 + 13 * c ^ 2 - 17) / (2 * a * c), ?_⟩
        rw [Rat.cast_div, eq_div_iff hq]
        push_cast at e1 ⊢
        linear_combination e1
      obtain ⟨r, hr⟩ := hs'
      rw [hr] at hs
      exact ex45_nsq 13 ex45_ns13 r (by exact_mod_cast hs)
  have ht' : IsIntegral F t := Algebra.IsIntegral.isIntegral t
  have q17 : Irreducible (X ^ 2 - C (17 : F)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two key
  have hmin' : minpoly F t = X ^ 2 - C (17 : F) :=
    (minpoly.eq_of_irreducible_of_monic q17 (by
      simp
      have h17 : ((17 : F) : L) = 17 := by norm_cast
      rw [h17, ht, sub_self]) (monic_X_pow_sub_C _ two_ne_zero)).symm
  have htop : IntermediateField.adjoin F {t} = ⊤ := by
    have h1 := IntermediateField.adjoin_adjoin_left ℚ {s} {t}
    rw [Set.singleton_union, ← hFdef] at h1
    apply IntermediateField.restrictScalars_injective ℚ
    rw [h1, hg]; rfl
  have hF2 : Module.finrank F L = 2 := by
    rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank ht', hmin',
      natDegree_X_pow_sub_C]
  rw [← Module.finrank_mul_finrank ℚ F L, hF, hF2]


/-- Helper for `example_4_5`. -/
theorem ex45_isSquare_of_hensel (p : ℕ) [Fact p.Prime] (u a : ℤ)
    (h : ‖((a ^ 2 - u : ℤ) : ℤ_[p])‖ < ‖((2 * a : ℤ) : ℤ_[p])‖ ^ 2) :
    IsSquare ((u : ℤ) : ℚ_[p]) := by
  let F : Polynomial ℤ_[p] := X ^ 2 - C (u : ℤ_[p])
  have hF : F.aeval (a : ℤ_[p]) = ((a ^ 2 - u : ℤ) : ℤ_[p]) := by
    simp [F]
  have hF' : F.derivative.aeval (a : ℤ_[p]) = ((2 * a : ℤ) : ℤ_[p]) := by
    simp [F]
    left; norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := (a : ℤ_[p])) (by rw [hF, hF']; exact h)
  simp only [F, map_sub, map_pow, aeval_X, aeval_C] at hz
  refine ⟨(z : ℚ_[p]), ?_⟩
  have h1 : z ^ 2 = u := by
    have := hz; simp at this; linear_combination this
  have h2 : ((z ^ 2 : ℤ_[p]) : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) := by rw [h1]
  push_cast at h2
  rw [← h2]; ring

/-- Helper for `example_4_5`. -/
theorem ex45_isSquare_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (u a : ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (h : (p : ℤ) ∣ a ^ 2 - u) : IsSquare ((u : ℤ) : ℚ_[p]) := by
  apply ex45_isSquare_of_hensel
  have h1 : ‖((a ^ 2 - u : ℤ) : ℤ_[p])‖ < 1 := PadicInt.norm_int_lt_one_iff_dvd _ |>.2 h
  have h2 : ‖((2 * a : ℤ) : ℤ_[p])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd _).1 hlt
    rcases (Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)).dvd_or_dvd this with h3 | h3
    · have : p ∣ 2 := by exact_mod_cast h3
      exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
    · exact ha h3
  rw [h2]; simpa using h1

/-- Helper for `example_4_5`. -/
theorem ex45_isSquare_17_two : IsSquare ((17 : ℤ) : ℚ_[2]) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply ex45_isSquare_of_hensel 2 17 1
  have h1 : ‖(((1:ℤ) ^ 2 - 17 : ℤ) : ℤ_[2])‖ ≤ ((2:ℝ) ^ (-(4:ℤ) : ℤ)) :=
    (PadicInt.norm_int_le_pow_iff_dvd).2 (by norm_num)
  have h2 : ‖((2 * 1 : ℤ) : ℤ_[2])‖ = 2⁻¹ := by
    have := PadicInt.norm_p (p := 2)
    simpa using this
  rw [h2]
  have : ((2:ℝ) ^ (-(4:ℤ) : ℤ)) = 1 / 16 := by norm_num
  rw [this] at h1
  refine lt_of_le_of_lt h1 ?_
  norm_num

/-- Helper for `example_4_5`. -/
theorem ex45_isSquare_of_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (u : ℤ) (hu : (u : ZMod p) ≠ 0)
    (h : IsSquare (u : ZMod p)) : IsSquare ((u : ℤ) : ℚ_[p]) := by
  obtain ⟨r, hr⟩ := h
  apply ex45_isSquare_odd p hp u (r.val : ℤ)
  · intro hd
    have : ((r.val : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    simp at this
    apply hu; rw [hr, this]; ring
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hr]; ring

/-- Helper for `example_4_5`. -/
theorem ex45_sq_13_17_221 (p : ℕ) [Fact p.Prime] :
    IsSquare (13 : ℚ_[p]) ∨ IsSquare (17 : ℚ_[p]) ∨ IsSquare (13 * 17 : ℚ_[p]) := by
  have hp := (Fact.out : p.Prime)
  by_cases h2 : p = 2
  · subst h2
    right; left
    exact_mod_cast ex45_isSquare_17_two
  by_cases h13 : p = 13
  · subst h13
    right; left
    have := ex45_isSquare_odd 13 (by norm_num) 17 2 (by norm_num) (by norm_num)
    exact_mod_cast this
  by_cases h17 : p = 17
  · subst h17
    left
    have := ex45_isSquare_odd 17 (by norm_num) 13 8 (by norm_num) (by norm_num)
    exact_mod_cast this
  have nz : ∀ n : ℕ, n.Prime → p ≠ n → ((n : ℤ) : ZMod p) ≠ 0 := by
    intro n hn hne h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hn).1 (by exact_mod_cast h))
  have n13 := nz 13 (by norm_num) (Ne.symm (Ne.symm h13))
  have n17 := nz 17 (by norm_num) h17
  have n221 : (((13 * 17 : ℤ)) : ZMod p) ≠ 0 := by
    push_cast at n13 n17
    have := mul_ne_zero n13 n17
    norm_num at this ⊢
    exact this
  have e := legendreSym.mul p 13 17
  have c13 := legendreSym.eq_one_or_neg_one p n13
  have c17 := legendreSym.eq_one_or_neg_one p n17
  by_cases a13 : legendreSym p 13 = 1
  · left
    have := ex45_isSquare_of_zmod p h2 13 n13 ((legendreSym.eq_one_iff p n13).1 a13)
    exact_mod_cast this
  by_cases a17 : legendreSym p 17 = 1
  · right; left
    have := ex45_isSquare_of_zmod p h2 17 n17 ((legendreSym.eq_one_iff p n17).1 a17)
    exact_mod_cast this
  right; right
  have b13 : legendreSym p 13 = -1 := c13.resolve_left a13
  have b17 : legendreSym p 17 = -1 := c17.resolve_left a17
  have : legendreSym p (13 * 17) = 1 := by rw [e, b13, b17]; norm_num
  have := ex45_isSquare_of_zmod p h2 (13 * 17) n221 ((legendreSym.eq_one_iff p n221).1 this)
  exact_mod_cast this

end Example45Helpers

/-- **Example 4.5** (Milne, *CFT*, VIII, Example 4.5, p. 241): for $L = \mathbb Q[\sqrt{13},\sqrt{17}]$, $[L:\mathbb Q]
= 4$ but every local degree is $1$ or $2$: at every prime $p$ one of $13$, $17$, $13\cdot17$ is a square in
$\mathbb Q_p$ (so the decomposition group, a subgroup of $(\mathbb Z/2)^2$, has order at most $2$), and all three are
positive (the real prime splits). Stated for the completions $\mathbb Q_p$ (Mathlib's `ℚ_[p]`). -/
@[kb "milne2020cft" "Ch. VIII, Example 4.5, p. 241"]
theorem example_4_5 :
    (∀ (L : Type) [Field L] [NumberField L] (s t : L), s ^ 2 = 13 → t ^ 2 = 17 →
      IntermediateField.adjoin ℚ ({s, t} : Set L) = ⊤ → Module.finrank ℚ L = 4) ∧
    (∀ p : ℕ, [Fact p.Prime] → IsSquare (13 : ℚ_[p]) ∨ IsSquare (17 : ℚ_[p]) ∨ IsSquare (13 * 17 : ℚ_[p])) :=
  ⟨fun L _ _ s t hs ht hg => ex45_partA L s t hs ht hg, fun p _ => ex45_sq_13_17_221 p⟩

/-- **Theorem 4.7** (named statement; Milne, *CFT*, VIII, Theorem 4.7, p. 242): for every finite Galois extension
$L/K$ of number fields, $H^2(L/K) = H^2(\mathrm{Gal}(L/K), C_L)$ is cyclic of order $n = [L:K]$ (with a canonical
generator $u_{L/K}$, the fundamental class, characterized by $\mathrm{inv}_{L/K}(u_{L/K}) = 1/n$; the invariant map
is not formalized).

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.ClassFormation.isAddCyclic_H2`
(`TauCeti/NumberTheory/ClassFieldTheory/Formation/ClassFormation.lean:170`),
`TauCeti.ClassFieldTheory.ClassFormation.natCard_H2` (same file, line 125) and
`TauCeti.ClassFieldTheory.globalClassFormation` (`TauCeti/NumberTheory/ClassFieldTheory/Global/ClassFormation.lean:267`)
at Tau Ceti commit `7ed979dc`. Needed to apply it here: Tau Ceti proves the axioms of a class formation for the global
case; one must identify our second cohomology group of the idele class group with the corresponding group for a layer,
using `TauCeti.ClassFieldTheory.ideleClassCohomologyEquiv`. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 4.7, p. 242 (input)"]
structure Theorem4_7 : Prop where
  cyclic : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    IsAddCyclic (H2C K L) ∧ Nat.card (H2C K L) = Module.finrank K L

/-- **Theorem 4.8, the norm limitation theorem** (named statement; Milne, *CFT*, VIII, Theorem 4.8, p. 242): let $E$ be
a finite extension of $K$ (not necessarily Galois) and $M$ the maximal subextension of $E$ abelian over $K$. Then
$\mathrm{Nm}_{E/K}C_E = \mathrm{Nm}_{M/K}C_M$ (Chapter VII's `normClasses`). -/
@[kb "milne2020cft" "Ch. VIII, Theorem 4.8, p. 242 (norm limitation theorem; input)"]
structure Theorem4_8 : Prop where
  eq : ∀ (E : Type) [Field E] [NumberField E] [Algebra K E] (M : IntermediateField K E) [IsGalois K M],
    (∀ σ τ : Gal(M/K), σ * τ = τ * σ) →
    (∀ F : IntermediateField K E, IsGalois K F → (∀ σ τ : Gal(F/K), σ * τ = τ * σ) → F ≤ M) →
      Ch7.normClasses K E = Ch7.normClasses K M

end NumberFieldKB.MilneCFT.Ch8
