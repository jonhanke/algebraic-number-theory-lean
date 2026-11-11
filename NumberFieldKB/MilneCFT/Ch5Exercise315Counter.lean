import NumberFieldKB.MilneCFT.Ch5Complements
import NumberFieldKB.MilneCFT.Ch5LSeries
import NumberFieldKB.MilneCFT.Ch5Artin
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat

/-!
# Milne, *Class Field Theory*, Chapter V, Exercise 3.15: the existence clause is false as formalized

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Exercise 3.15 (p. 160).

The named statement `Exercise3_15` (`Ch5Complements.lean`) asks, in its `exists_field` clause, for an $S$-class field
for every $H$ with $i(K_{\mathfrak m,1}) \cap I^{S\cup S(\mathfrak m)} \subseteq H \subseteq I^{S\cup S(\mathfrak m)}$.
That hypothesis does not force the classes of the primes in $S$ into $H$, but the primes of $S$ must split completely
in an $S$-class field. Counterexample (`not_exercise3_15_rat`): $K = \mathbb Q$, $S = \{2\}$,
$\mathfrak m = 3\cdot\infty$, $H = i(\mathbb Q_{\mathfrak m,1}) \cap I^{\{2,3\}}$. An $S$-class field $L$ would satisfy:
every prime $p \ne 2, 3$ splitting in $\mathbb Q(\zeta_3)$ ($p \equiv 1 \bmod 3$, so $(p) \in H$) splits in $L$, hence
$\mathbb Q(\zeta_3) \hookrightarrow L$ (Bauer, `nonempty_algHom_of_splitPrimes_diff_finite`); but $2$ splits completely
in $L$, so a residue field of $L$ above $2$ is $\mathbb F_2$ and would contain a root of $X^2 + X + 1$
(`not_isPrimitiveRoot_three_of_two_split`).

The corrected existence clause, with hypothesis $(i(K_{\mathfrak m,1}) \cdot \langle S\rangle) \cap I^{S\cup S(\mathfrak m)}
\subseteq H$, and the other two clauses are proved in `Ch5NormLimitationUncond.lean` (`exercise3_15_exists`,
`exercise3_15_unique`, `exercise3_15_isSClassField`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev

noncomputable section

namespace NumberFieldKB.MilneCFT

/-- If $2$ splits completely in a number field $L$, then $L$ contains no primitive cube root of unity: a residue
field of $L$ above $2$ is $\mathbb F_2$, where $X^2 + X + 1$ has no root. -/
theorem not_isPrimitiveRoot_three_of_two_split (L : Type) [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv2 : MilneANT.ratPrime v = 2) (hs : v ∈ splitPrimes ℚ L)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) : False := by
  obtain ⟨Q⟩ : Nonempty (v.asIdeal.primesOver (𝓞 L)) := inferInstance
  obtain ⟨hQp, hQl⟩ := Q.2
  have := hQp
  have := hQl
  have hf : Q.1.inertiaDeg (𝓞 ℚ) = 1 := (hs Q).2
  have : Q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q.1 v.asIdeal
  have := v.isMaximal
  have hcard := Ideal.cardQuot_pow_inertiaDeg v.asIdeal Q.1
  rw [hf, pow_one] at hcard
  have hv : v.asIdeal.cardQuot = 2 := by
    rw [← Ideal.absNorm_apply, asIdeal_eq_span_ratPrime v, hv2, Ideal.absNorm_span_singleton]
    have h1 : ((2 : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) 2 := by simp
    rw [h1, Algebra.norm_algebraMap, RingOfIntegers.rank, Module.finrank_self]
    norm_num
  let F := 𝓞 L ⧸ Q.1
  let _ : Field F := Ideal.Quotient.field Q.1
  have hF : Nat.card F = 2 := by
    rw [← hv, hcard]; rfl
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  let _ : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 := by rw [Fintype.card_eq_nat_card, hF]
  let z : 𝓞 L := ⟨ζ, hζ.isIntegral (by norm_num)⟩
  have hz : z ^ 2 + z + 1 = 0 := by
    apply RingOfIntegers.coe_injective
    have := hζ.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    push_cast
    change ζ ^ 2 + ζ + 1 = 0
    linear_combination this
  set x : F := Ideal.Quotient.mk Q.1 z
  have hx : x ^ 2 + x + 1 = 0 := by
    change Ideal.Quotient.mk Q.1 z ^ 2 + Ideal.Quotient.mk Q.1 z + 1 = 0
    rw [← map_pow, ← map_add, ← map_one (Ideal.Quotient.mk Q.1), ← map_add, hz, map_zero]
  have hxx : x ^ 2 = x := by
    have := FiniteField.pow_card x
    rwa [hFc] at this
  have h2 : (2 : F) = 0 := by
    have := FiniteField.cast_card_eq_zero F
    rwa [hFc] at this
  have : (1 : F) = 0 := by
    linear_combination hx - hxx - x * h2
  exact one_ne_zero this

/-- A prime $p \ne 3$ with $(p) \in i(\mathbb Q_{3\infty,1})$ satisfies $p \equiv 1 \bmod 3$. -/
theorem ratPrime_eq_one_of_mem_rayPrincipal_three (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ MilneANT.ratPrime v ∣ 3)
    (hmem : primeUnitIdeal v ∈ rayPrincipal (ratModulus 3 (by norm_num))) :
    (MilneANT.ratPrime v : ZMod 3) = 1 := by
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  set p := MilneANT.ratPrime v with hpdef
  let a : ℚˣ := Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 fun h => hv (h ▸ dvd_refl _)
  have ha : a ∈ Gm 3 (by norm_num) := by
    rw [mem_Gm]
    refine ⟨?_, ?_⟩
    · simpa [a] using hcop
    · simp [a]
  have hT : Theta 3 (by norm_num) ⟨a, ha⟩ = 1 := by
    rw [Theta_eq_one_iff]
    obtain ⟨c, hc, hca⟩ := hmem
    exact ⟨c, hc, by rw [hca]; exact (toPrincipalIdeal_ratPrime v).symm⟩
  rw [Theta_iff_Psi, Psi_eq_one_iff] at hT
  have habs : (absU (a : ℚˣ) : ℚ) = (p : ℚ) := by
    rw [absU_coe]; simp [a]
  rw [habs] at hT
  simp only [Rat.num_natCast, Rat.den_natCast] at hT
  have : ((1 : ℤ) : ZMod 3) = ((p : ℤ) : ZMod 3) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by simpa using hT)
  simpa using this.symm

/-- **Exercise 3.15 (`exists_field`) is false as formalized** (Milne, *CFT*, V, Exercise 3.15, p. 160; see the module
docstring): for $K = \mathbb Q$, $S = \{2\}$, $\mathfrak m = 3\cdot\infty$ and
$H = i(\mathbb Q_{\mathfrak m,1}) \cap I^{\{2,3\}}$ there is no $S$-class field. Hence `Exercise3_15 ℚ` fails. -/
@[kb "milne2020cft" "Ch. V, Exercise 3.15 (counterexample to the existence clause as formalized)"]
theorem not_exercise3_15_rat : ¬ Exercise3_15 ℚ := by
  intro h
  obtain ⟨v2, hv2, -⟩ := exists_prime_toPrincipalIdeal 2 Nat.prime_two
  have h3 : (3 : ℕ) ≠ 0 := by norm_num
  have hsupp := ratModulus_finiteSupport 3 h3
  have hdisj : Disjoint ({v2} : Set (HeightOneSpectrum (𝓞 ℚ))) (ratModulus 3 h3).finiteSupport := by
    rw [Set.disjoint_singleton_left, hsupp]
    intro hd
    have : MilneANT.ratPrime v2 ∣ 3 := hd
    rw [hv2] at this
    norm_num at this
  obtain ⟨L, _, _, alg, _, hL, -⟩ := h.exists_field {v2} (ratModulus 3 h3)
    (rayPrincipal (ratModulus 3 h3) ⊓ sIdeals ({v2} ∪ (ratModulus 3 h3).finiteSupport))
    (Set.finite_singleton _) hdisj inf_le_right le_rfl
  obtain rfl : alg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  let M := CyclotomicField 3 ℚ
  have : IsCyclotomicExtension {3} ℚ M := CyclotomicField.isCyclotomicExtension 3 ℚ
  have : IsGalois ℚ M := IsCyclotomicExtension.isGalois {3} ℚ M
  have hfin : ({v2} ∪ (ratModulus 3 h3).finiteSupport).Finite :=
    (Set.finite_singleton _).union (Ideal.finite_factors (ratModulus 3 h3).finite_ne_bot)
  obtain ⟨f⟩ := nonempty_algHom_of_splitPrimes_diff_finite M L _ hfin (fun v hv => by
    have hvS : v ∉ ({v2} : Set _) := fun h' => hv.2 (Or.inl h')
    have hvm : v ∉ (ratModulus 3 h3).finiteSupport := fun h' => hv.2 (Or.inr h')
    have hH := (hL.splits_iff v hvS hvm).1 hv.1
    have hv3 : ¬ MilneANT.ratPrime v ∣ 3 := fun h' => hvm (by rw [hsupp]; exact h')
    exact (mem_splitPrimes_cyclotomic_iff 3 M v hv3).2
      (ratPrime_eq_one_of_mem_rayPrincipal_three v hv3 hH.1))
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ M
  exact not_isPrimitiveRoot_three_of_two_split L v2 hv2 (hL.split v2 rfl) _ (hζ.map_of_injective f.injective)

end NumberFieldKB.MilneCFT
