import NumberFieldKB.MilneCFT.Ch8.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Milne, *Class Field Theory*, Chapter VIII §1: $16$ and eighth powers; Remark 1.5

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §1–§2,
printed pp. 229–231 (printed page = pdf page − 9).

* **Exercise 1.3** (`exercise_1_3`): $16$ is an $8$th power in $\mathbb R$ and in $\mathbb Q_p$ for every odd $p$, but
  not in $\mathbb Q$; and (`not_eighth_power_padic_two`, Example 2.2 (i)) not in $\mathbb Q_2$.
* **Remark 1.5**: named statements `Remark1_5a`, `Remark1_5aRat`; `not_mem_powSet_sixteen` (the update to the
  example); `remark_1_5b` (proved).
-/

open NumberField IsDedekindDomain

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type} [Field K] [NumberField K]

/-- Hensel lifting of square roots: for an odd prime $p$ and an integer $a$ whose reduction mod $p$ is a nonzero
square, $a$ is a square in $\mathbb Q_p$. -/
theorem exists_sq_padic_of_isSquare_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ℤ)
    (hsq : IsSquare (a : ZMod p)) (ha : (a : ZMod p) ≠ 0) : ∃ y : ℚ_[p], y ^ 2 = (a : ℚ_[p]) := by
  obtain ⟨r, hr⟩ := hsq
  obtain ⟨a0, ha0⟩ := ZMod.intCast_surjective r
  have hpp := (Fact.out : p.Prime)
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  have hdvd : (p : ℤ) ∣ a0 ^ 2 - a := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; rw [hr, ha0]; ring
  have hmod0 : ¬ (p : ℤ) ∣ a0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h; apply ha; rw [hr, ← ha0, h]; ring
  have hn1 : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → ‖(z : ℤ_[p])‖ = 1 := fun z h =>
    le_antisymm (PadicInt.norm_le_one _) (not_lt.mp (mt (PadicInt.norm_int_lt_one_iff_dvd z).mp h))
  have hnd : ¬ (p : ℤ) ∣ 2 * a0 := by
    intro h
    rcases hpz.dvd_or_dvd h with h | h
    · have : p ∣ 2 := by exact_mod_cast h
      exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
    · exact hmod0 h
  let F : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C a
  have h1 : ‖F.aeval (a0 : ℤ_[p])‖ < ‖F.derivative.aeval (a0 : ℤ_[p])‖ ^ 2 := by
    have e1 : F.aeval (a0 : ℤ_[p]) = ((a0 ^ 2 - a : ℤ) : ℤ_[p]) := by simp [F]
    have e2 : F.derivative.aeval (a0 : ℤ_[p]) = ((2 * a0 : ℤ) : ℤ_[p]) := by
      simp [F, map_ofNat]
    rw [e1, e2, hn1 _ hnd]
    simpa using (PadicInt.norm_int_lt_one_iff_dvd _).mpr hdvd
  obtain ⟨z, hz, -⟩ := hensels_lemma h1
  refine ⟨(z : ℚ_[p]), ?_⟩
  have : z ^ 2 = (a : ℤ_[p]) := by
    simpa [F, sub_eq_zero] using hz
  have := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) this
  simpa using this

/-- For an odd prime $p$, $16$ is an $8$th power in $\mathbb Q_p$: one of $2, -2, -1$ is a square mod $p$, and the
factorization $X^8 - 16 = (X^2-2)(X^2+2)(X^2+2X+2)(X^2-2X+2)$ gives $x = y$ (if $y^2 = \pm 2$) or $x = 1 + i$ (if
$i^2 = -1$). -/
theorem sixteen_eighth_power_padic (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ∃ x : ℚ_[p], x ^ 8 = 16 := by
  have hpp := (Fact.out : p.Prime)
  have hne : ∀ a : ℤ, a = 2 ∨ a = -2 ∨ a = -1 → (a : ZMod p) ≠ 0 := by
    intro a ha h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have hpz : (p : ℤ) ∣ 2 := by
      rcases ha with rfl | rfl | rfl
      · exact h
      · simpa using h
      · have : (p : ℤ) ∣ 1 := by simpa using h
        have := Int.eq_one_of_dvd_one (by positivity) this
        norm_cast at this
        exact absurd this hpp.one_lt.ne'
    have : p ∣ 2 := by exact_mod_cast hpz
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have : p % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h | h
      · exact absurd h hp
      · exact h
    omega
  rcases h8 with h | h | h | h
  · obtain ⟨y, hy⟩ := exists_sq_padic_of_isSquare_zmod p hp 2
      (by simpa using (ZMod.exists_sq_eq_two_iff hp).mpr (Or.inl h)) (by simpa using hne 2 (Or.inl rfl))
    refine ⟨y, ?_⟩
    have : y ^ 8 = (y ^ 2) ^ 4 := by ring
    rw [this, hy]; norm_num
  · obtain ⟨y, hy⟩ := exists_sq_padic_of_isSquare_zmod p hp (-2)
      (by simpa using (ZMod.exists_sq_eq_neg_two_iff hp).mpr (Or.inr h))
      (by simpa using hne (-2) (Or.inr (Or.inl rfl)))
    refine ⟨y, ?_⟩
    have : y ^ 8 = (y ^ 2) ^ 4 := by ring
    rw [this, hy]; norm_num
  · obtain ⟨i, hi⟩ := exists_sq_padic_of_isSquare_zmod p hp (-1)
      (by simpa using ZMod.exists_sq_eq_neg_one_iff.mpr (by omega))
      (by simpa using hne (-1) (Or.inr (Or.inr rfl)))
    refine ⟨1 + i, ?_⟩
    have hi' : i ^ 2 = -1 := by simpa using hi
    have h2 : (1 + i) ^ 2 = 2 * i := by linear_combination hi'
    have : (1 + i) ^ 8 = ((1 + i) ^ 2) ^ 4 := by ring
    rw [this, h2]
    have : (2 * i) ^ 4 = 16 * (i ^ 2) ^ 2 := by ring
    rw [this, hi']; norm_num
  · obtain ⟨y, hy⟩ := exists_sq_padic_of_isSquare_zmod p hp 2
      (by simpa using (ZMod.exists_sq_eq_two_iff hp).mpr (Or.inr h)) (by simpa using hne 2 (Or.inl rfl))
    refine ⟨y, ?_⟩
    have : y ^ 8 = (y ^ 2) ^ 4 := by ring
    rw [this, hy]; norm_num

/-- $16$ is not an $8$th power in $\mathbb Q$. -/
theorem sixteen_not_eighth_power_rat : ¬ ∃ x : ℚ, x ^ 8 = 16 := by
  rintro ⟨x, hx⟩
  have h1 : (x ^ 2) ^ 4 = 2 ^ 4 := by rw [← pow_mul]; norm_num [hx]
  have h2 : x ^ 2 = 2 :=
    (pow_left_inj₀ (sq_nonneg x) (by norm_num) (by norm_num)).mp h1
  have h3 : (|(x : ℝ)|) ^ 2 = 2 := by
    rw [sq_abs]; exact_mod_cast h2
  have h4 : |(x : ℝ)| = Real.sqrt 2 := by
    rw [← h3, Real.sqrt_sq (abs_nonneg _)]
  apply irrational_sqrt_two
  rw [← h4]
  exact ⟨|x|, by push_cast; rfl⟩

/-- **Exercise 1.3** (Milne, *CFT*, VIII, Exercise 1.3, p. 229): $16$ is an $8$th power in $\mathbb R$ and in
$\mathbb Q_p$ for every odd prime $p$, but not in $\mathbb Q$. -/
@[kb "milne2020cft" "Ch. VIII, Exercise 1.3, p. 229"]
theorem exercise_1_3 :
    (∃ x : ℝ, x ^ 8 = 16) ∧ (∀ p : ℕ, [Fact p.Prime] → p ≠ 2 → ∃ x : ℚ_[p], x ^ 8 = 16) ∧
      ¬ ∃ x : ℚ, x ^ 8 = 16 := by
  refine ⟨⟨Real.sqrt 2, ?_⟩, fun p _ hp => sixteen_eighth_power_padic p hp, sixteen_not_eighth_power_rat⟩
  have : Real.sqrt 2 ^ 8 = (Real.sqrt 2 ^ 2) ^ 4 := by ring
  rw [this, Real.sq_sqrt (by norm_num)]; norm_num

/-- $16$ is not an $8$th power in $\mathbb Q_2$ (Milne, *CFT*, VIII, Example 2.2 (i), p. 231): $8\,\mathrm{ord}_2(x) =
\mathrm{ord}_2(16) = 4$ is impossible. -/
@[kb "milne2020cft" "Ch. VIII, Example 2.2 (i), p. 231 (16 is not an 8th power in Q_2)"]
theorem not_eighth_power_padic_two : ¬ ∃ x : ℚ_[2], x ^ 8 = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨x, hx⟩
  have h16 : (16 : ℚ_[2]) = (2 : ℚ_[2]) ^ 4 := by norm_num
  have := congrArg Padic.valuation hx
  rw [h16, Padic.valuation_pow, Padic.valuation_pow] at this
  have h2 : (2 : ℚ_[2]).valuation = 1 := by
    have := Padic.valuation_p (p := 2)
    simpa using this
  rw [h2] at this
  omega

/-- The group $P(n,S)$ of Remark 1.5 (Milne, *CFT*, VIII, p. 230): the $a \in K^\times$ with $a \in K_v^{\times n}$ for
all (finite) primes $v \notin S$. (The infinite primes are not constrained here; for $K = \mathbb Q$, $n = 8$ the real
condition is automatic for the elements below.) -/
def powSet (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) : Set Kˣ :=
  {a | ∀ v ∉ S, IsLocalPow n (a : K) v}

variable (K) in
/-- **Remark 1.5 (a)** (named statement; Milne, *CFT*, VIII, Remark 1.5 (a), p. 230, citing Artin–Tate): for a finite
set $S$ of primes and $n \ge 1$, either $P(n,S) = K^{\times n}$ or $P(n,S) = K^{\times n} \sqcup a_0K^{\times n}$ for
some $a_0 \in K^\times$. -/
@[kb "milne2020cft" "Ch. VIII, Remark 1.5 (a), p. 230 (input)"]
structure Remark1_5a : Prop where
  dichotomy : ∀ (n : ℕ), 0 < n → ∀ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite →
    (powSet n S = Set.range (fun b : Kˣ => b ^ n)) ∨
      ∃ a₀ : Kˣ, powSet n S = Set.range (fun b : Kˣ => b ^ n) ∪ Set.range (fun b : Kˣ => a₀ * b ^ n)

/-- The element $16$ of $\mathbb Q^\times$ (as a unit; the numeral `16 : ℚˣ` does not elaborate). -/
def sixteenUnit : ℚˣ := Units.mk0 16 (by norm_num)

/-- **Remark 1.5 (a), the example $K = \mathbb Q$, $n = 8$** (named statement; Milne, *CFT*, VIII, Remark 1.5 (a),
p. 230, citing Artin–Tate p. 96 and Trost 1934): $P(8,S) = \mathbb Q^{\times 8} \sqcup 16\,\mathbb Q^{\times 8}$.
*Update:* this needs $2 \in S$: $16 \notin \mathbb Q_2^{\times 8}$ (`not_eighth_power_padic_two`), so for $2 \notin S$,
$16 \notin P(8,S)$ (`not_mem_powSet_sixteen`). Stated for $S \ni (2)$. -/
@[kb "milne2020cft" "Ch. VIII, Remark 1.5 (a), p. 230 (P(8,S) for Q; input)"]
structure Remark1_5aRat : Prop where
  eq : ∀ S : Set (HeightOneSpectrum (𝓞 ℚ)), S.Finite → (∃ v ∈ S, (2 : 𝓞 ℚ) ∈ v.asIdeal) →
    powSet 8 S = Set.range (fun b : ℚˣ => b ^ 8) ∪ Set.range (fun b : ℚˣ => sixteenUnit * b ^ 8)

/-- The kernel of reduction $(\mathbb Z/2^{s+2})^\times \to (\mathbb Z/4)^\times$ (the units $\equiv 1 \bmod 4$) is
cyclic, generated by $5$ (it has order $2^s = \operatorname{ord}(5)$). -/
theorem isCyclic_ker_unitsMap_four (s : ℕ) (h4 : 4 ∣ 2 ^ (s + 2)) :
    IsCyclic (ZMod.unitsMap h4).ker := by
  set f := ZMod.unitsMap h4 with hf
  have hcop : Nat.Coprime 5 (2 ^ (s + 2)) := by
    apply Nat.Coprime.pow_right
    norm_num
  let g : (ZMod (2 ^ (s + 2)))ˣ := ZMod.unitOfCoprime 5 hcop
  have hgv : (g : ZMod (2 ^ (s + 2))) = 5 := by simp [g]
  have hg : g ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    simp only [hf, ZMod.unitsMap_def, Units.coe_map, hgv]
    show (ZMod.castHom h4 (ZMod 4)) 5 = 1
    rw [map_ofNat]
    decide
  have hord : orderOf g = 2 ^ s := by
    rw [← orderOf_units, hgv]
    exact ZMod.orderOf_five s
  have hcard : Nat.card f.ker = 2 ^ s := by
    have h1 : Nat.card (ZMod (2 ^ (s + 2)))ˣ = 2 ^ (s + 1) := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ Nat.prime_two]
      simp
    have h2 : Nat.card (ZMod 4)ˣ = 2 := by
      rw [Nat.card_eq_fintype_card]; decide
    have h3 : Nat.card ((ZMod (2 ^ (s + 2)))ˣ ⧸ f.ker) = 2 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
        (ZMod.unitsMap_surjective h4)).toEquiv, h2]
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [h1, h3] at this
    have h22 : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    rw [h22] at this
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) this).symm
  have hle : Subgroup.zpowers g ≤ f.ker := (Subgroup.zpowers_le).mpr hg
  have heq : Subgroup.zpowers g = f.ker := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard, Nat.card_zpowers, hord]
  rw [← heq]
  infer_instance

/-- **Remark 1.5 (b)** (Milne, *CFT*, VIII, Remark 1.5 (b), p. 231): if $\sqrt{-1} \in K$, then $K[\zeta_{2^t}]$ is
cyclic over $K$ for every $t$ (so Theorem 1.4 applies to every $n$). -/
@[kb "milne2020cft" "Ch. VIII, Remark 1.5 (b), p. 231"]
theorem remark_1_5b (hi : ∃ i : K, i ^ 2 = -1) (t : ℕ) :
    IsCyclic (CyclotomicField (2 ^ t) K ≃ₐ[K] CyclotomicField (2 ^ t) K) := by
  obtain ⟨i, hi⟩ := hi
  set L := CyclotomicField (2 ^ t) K with hL
  have hζ := IsCyclotomicExtension.zeta_spec (2 ^ t) K L
  have hinj := hζ.autToPow_injective K
  rcases Nat.lt_or_ge t 2 with ht | ht
  · have : IsCyclic (ZMod (2 ^ t))ˣ := (ZMod.isCyclic_units_two_pow_iff t).mpr (by omega)
    exact isCyclic_of_injective (hζ.autToPow K) hinj
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
    have h4 : 4 ∣ 2 ^ (s + 2) := ⟨2 ^ s, by ring⟩
    have hker := isCyclic_ker_unitsMap_four s h4
    have hmem : ∀ σ : L ≃ₐ[K] L, hζ.autToPow K σ ∈ (ZMod.unitsMap h4).ker := by
      intro σ
      have ha : (2 ^ s : ℕ) ≠ 0 := by positivity
      have hdiv : (2 ^ s : ℕ) ∣ 2 ^ (s + 2) := pow_dvd_pow 2 (by omega)
      have hquot : 2 ^ (s + 2) / 2 ^ s = 4 := by
        rw [pow_add, Nat.mul_div_cancel_left _ (by positivity)]; norm_num
      have hη : IsPrimitiveRoot (IsCyclotomicExtension.zeta (2 ^ (s + 2)) K L ^ (2 ^ s))  4 := by
        simpa [hquot] using hζ.pow_of_dvd ha hdiv
      have hη2 : (IsCyclotomicExtension.zeta (2 ^ (s + 2)) K L ^ (2 ^ s)) ^ 2 = -1 := by
        have := (hη.pow_of_dvd (p := 2) (by norm_num) (by norm_num))
        exact IsPrimitiveRoot.eq_neg_one_of_two_right (by simpa using this)
      have hfix : σ (IsCyclotomicExtension.zeta (2 ^ (s + 2)) K L ^ (2 ^ s)) =
          IsCyclotomicExtension.zeta (2 ^ (s + 2)) K L ^ (2 ^ s) := by
        have hi' : (algebraMap K L i) ^ 2 = -1 := by
          rw [← map_pow, hi]; simp
        have : (IsCyclotomicExtension.zeta (2 ^ (s + 2)) K L ^ (2 ^ s)) ^ 2 = (algebraMap K L i) ^ 2 := by
          rw [hη2, hi']
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h
        · rw [h]; exact σ.commutes i
        · rw [h, map_neg]; congr 1; exact σ.commutes i
      have hspec := hζ.autToPow_spec K σ
      have h1 : IsCyclotomicExtension.zeta (2 ^ (s + 2)) K L ^
          ((hζ.autToPow K σ : ZMod (2 ^ (s + 2))).val * 2 ^ s) =
          IsCyclotomicExtension.zeta (2 ^ (s + 2)) K L ^ (2 ^ s) := by
        rw [pow_mul, hspec, ← map_pow, hfix]
      obtain ⟨w, hw⟩ := hζ.isUnit (by positivity)
      have hord : orderOf w = 2 ^ (s + 2) := by
        rw [← orderOf_units, hw]; exact hζ.eq_orderOf.symm
      have h1' : w ^ ((hζ.autToPow K σ : ZMod (2 ^ (s + 2))).val * 2 ^ s) = w ^ (2 ^ s) := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hw]; exact h1
      replace h1 := pow_eq_pow_iff_modEq.mp h1'
      rw [hord] at h1
      have h2 : 2 ^ s * (hζ.autToPow K σ : ZMod (2 ^ (s + 2))).val ≡ 2 ^ s * 1 [MOD 2 ^ s * 4] := by
        rw [show 2 ^ s * 4 = 2 ^ (s + 2) by ring, mul_one, mul_comm]
        exact h1
      have h3 := (Nat.ModEq.mul_left_cancel' ha) h2
      rw [MonoidHom.mem_ker]
      apply Units.ext
      show (ZMod.castHom h4 (ZMod 4)) (hζ.autToPow K σ : ZMod (2 ^ (s + 2))) = 1
      rw [← ZMod.natCast_zmod_val (hζ.autToPow K σ : ZMod (2 ^ (s + 2))), map_natCast]
      exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr h3
    let ψ := (hζ.autToPow K).codRestrict (ZMod.unitsMap h4).ker hmem
    have hψ : Function.Injective ψ := by
      intro a b hab
      apply hinj
      exact congrArg Subtype.val hab
    exact isCyclic_of_injective ψ hψ

/-- Why `Remark1_5aRat` needs $2 \in S$: if the prime $(2)$ of $\mathbb Q$ is not in $S$, then $16 \notin P(8,S)$,
since $16$ is not an $8$th power in $\mathbb Q_2$. -/
theorem not_mem_powSet_sixteen (S : Set (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ v ∈ S, (2 : 𝓞 ℚ) ∉ v.asIdeal) :
    sixteenUnit ∉ powSet 8 S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  let v₀ : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  have hv₀ : (Rat.HeightOneSpectrum.primesEquiv v₀ : ℕ) = 2 := by
    exact congrArg Subtype.val
      (Equiv.apply_symm_apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) ⟨2, Nat.prime_two⟩)
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v₀ : ℕ)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v₀).2⟩
  have hgen : Rat.HeightOneSpectrum.natGenerator v₀ = 2 := hv₀
  have h2 : (2 : 𝓞 ℚ) ∈ v₀.asIdeal := by
    have := (Rat.HeightOneSpectrum.natGenerator_dvd_iff v₀ (n := 2)).mp (by rw [hgen])
    rw [show ((2 : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) (2 : 𝓞 ℚ) by
        rw [map_ofNat]; norm_num,
      Ideal.apply_mem_of_equiv_iff] at this
    exact this
  have hv : v₀ ∉ S := fun hmem => hS v₀ hmem h2
  obtain ⟨x, hx⟩ := h v₀ hv
  have key : ∀ (q : ℕ) [Fact q.Prime], q = 2 → ¬ ∃ y : ℚ_[q], y ^ 8 = 16 := by
    intro q _ hq
    subst hq
    exact not_eighth_power_padic_two
  have hx' := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v₀) hx
  have hfun : ∀ y : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v₀ : ℕ)], y ^ 8 = 16 → False := fun y hy =>
    key _ hv₀ ⟨y, hy⟩
  refine hfun (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v₀ x) ?_
  have hc := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v₀).commutes ((sixteenUnit : ℚˣ) : ℚ)
  rw [← map_pow, hx']
  refine hc.trans ?_
  exact map_ofNat (algebraMap ℚ _) 16

end NumberFieldKB.MilneCFT.Ch8
