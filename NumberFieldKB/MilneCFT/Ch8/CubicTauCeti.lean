import NumberFieldKB.MilneCFT.Ch8.Cubic
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Cyclotomic.Three.CubicReciprocity
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Cyclotomic.Three.RationalResidue

/-!
# Milne, *Class Field Theory*, VIII Example 5.13, Exercise 5.16 and §10: cubic reciprocity from Tau Ceti

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §5 and §10.
The proofs use the port of Tau Ceti's cubic reciprocity (`NumberFieldKB.TauCetiPort`, README section "Cubic
reciprocity, Jacobi sums and power residue symbols").

## Example 5.13
A quadratic field $K$ containing a primitive cube root of $1$ is $\mathbb Q(\zeta_3)$ (`isCyclotomicExtension_three`),
so Tau Ceti's statements for `IsCyclotomicExtension {3} ℚ K` apply to $K$ itself; no transport is needed.
* `cubSym a b` is Tau Ceti's cubic residue symbol $(a/b)_3$ at the ideal $(b)$ (`Ideal.powerResidueSymbolIdeal`).
* Tau Ceti's law is for primary primes of different norms. We add the conjugate case $(\bar\rho/\rho) = (\rho/\bar\rho)$
  (`cubSym_conj_comm`: $\bar\rho \equiv t = \rho + \bar\rho \pmod\rho$ is a rational integer, to which Tau Ceti's
  reciprocity with rational integers applies, and Galois equivariance of the symbol), induction on primary elements
  (`primary_induction`: $\gamma = -\rho\delta$ with $\rho$ a primary prime and $\delta$ primary) to pass from primes to
  products in each argument (`cubSym_comm_layer2`, `cubSym_comm_primary`), and the normalization $a \equiv \pm 1$
  versus primary $\equiv 2 \pmod 3$ (`cubSym_comm`).
* `elt_eq_cubSym` compares `powerResidueElt 3` (Chapter VIII, defined through valuations) with `cubSym`: both are
  multiplicative in the denominator, and agree on primes since the defining congruence of
  `powerResidue` is the one of Tau Ceti's `Ideal.powerResidueSymbol` (`powerResidue_prime`).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open TauCeti Ideal
open scoped NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

namespace CubicTC

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

theorem ideal_congr {I J : Ideal (𝓞 K)} (h : I = J) (x : 𝓞 K) :
    Ideal.powerResidueSymbolIdeal I 3 (Ideal.Quotient.mk I x) =
      Ideal.powerResidueSymbolIdeal J 3 (Ideal.Quotient.mk J x) := by
  subst h; rfl

/-- Induction on primary elements. -/
theorem primary_induction {Q : 𝓞 K → Prop} (h1 : Q (-1))
    (hstep : ∀ ρ δ : 𝓞 K, Prime ρ → IsPrimaryEisenstein ρ → IsPrimaryEisenstein δ → δ ≠ 0 →
      Q δ → Q (-(ρ * δ)))
    {γ : 𝓞 K} (hγ0 : γ ≠ 0) (hγ : IsPrimaryEisenstein γ) : Q γ := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have := IsCyclotomicExtension.Rat.three_pid K
  suffices ∀ β γ : 𝓞 K, Associated β γ → γ ≠ 0 → IsPrimaryEisenstein γ → Q γ from
    this γ γ (Associated.refl γ) hγ0 hγ
  intro β
  induction β using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro γ hβγ hγ0 _
    exact absurd (hβγ.eq_zero_iff.mp rfl) hγ0
  | h₂ β hβ =>
    intro γ hβγ _ hγ
    have hu : IsUnit γ := hβγ.isUnit hβ
    have h1' : ¬ hζ.toInteger - 1 ∣ 1 := fun h ↦
      hζ.zeta_sub_one_prime'.not_isUnit (isUnit_of_dvd_one h)
    have hγ' : γ = -1 := by
      have := (hζ.existsUnique_isPrimaryEisenstein_unit_mul h1').unique
        (y₁ := hu.unit) (y₂ := -1) (by simpa using hγ)
        (by simpa using (isPrimaryEisenstein_intCast_iff (K := K) (a := -1)).mpr (by decide))
      simpa using congrArg Units.val this
    rw [hγ']
    exact h1
  | h₃ β ρ hβ0 hρ ih =>
    intro γ hβγ hγ0 hγ
    obtain ⟨u, rfl⟩ := hβγ
    have hρ3 : Algebra.norm ℤ ρ ≠ 3 := by
      intro h
      have hc := hγ.absNorm_span_singleton_coprime_three
      rw [Ideal.absNorm_span_singleton] at hc
      have h' := map_dvd (Algebra.norm ℤ) ((dvd_mul_right ρ β).trans (dvd_mul_right (ρ * β) u))
      rw [h] at h'
      have h3 : 3 ∣ (Algebra.norm ℤ (ρ * β * u)).natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr h'
        simpa using this
      exact absurd (Nat.Coprime.eq_one_of_dvd hc.symm h3) (by norm_num)
    obtain ⟨ρ', ⟨⟨w, rfl⟩, hρ'⟩, -⟩ := hρ.existsUnique_associated_isPrimaryEisenstein hρ3
    set δ : 𝓞 K := ((-(w⁻¹ * u) : (𝓞 K)ˣ) : 𝓞 K) * β with hδ
    have hγδ : ρ * β * u = -(ρ * w * δ) := by
      simp only [hδ, Units.val_neg, Units.val_mul]
      linear_combination (ρ * β * u) * (Units.mul_inv w).symm
    rw [hγδ] at hγ hγ0 ⊢
    have hδ' : IsPrimaryEisenstein δ := by
      have h := hρ'.three_dvd_sub_one_of_mul (w := -δ) (by simpa [mul_comm] using hγ)
      rw [isPrimaryEisenstein_iff, show δ - 2 = -(-δ - 1) - 3 by ring]
      exact (dvd_neg.mpr h).sub dvd_rfl
    have hδ0 : δ ≠ 0 := by
      intro h
      apply hγ0
      rw [h]; ring
    have hρ'p : Prime (ρ * w) := Associated.prime ⟨w, rfl⟩ hρ
    exact hstep (ρ * w) δ hρ'p hρ' hδ' hδ0
      (ih δ ⟨-(w⁻¹ * u), by rw [hδ, mul_comm]⟩ hδ0 hδ')

/-- The cubic residue symbol `(a / b)₃` at the principal ideal `b 𝓞 K`. -/
def cubSym (a b : 𝓞 K) : 𝓞 K :=
  Ideal.powerResidueSymbolIdeal (Ideal.span {b}) 3 (Ideal.Quotient.mk _ a)

theorem cubSym_mul_left (a a' b : 𝓞 K) : cubSym (a * a') b = cubSym a b * cubSym a' b := by
  simp [cubSym]

theorem cubSym_neg_left (a b : 𝓞 K) : cubSym (-a) b = cubSym a b := by
  simp only [cubSym, map_neg]
  exact Ideal.powerResidueSymbolIdeal_neg (by decide) _

theorem cubSym_neg_right (a b : 𝓞 K) : cubSym a (-b) = cubSym a b := by
  unfold cubSym
  exact ideal_congr (Ideal.span_singleton_neg b) a

theorem cubSym_mul_right (a b b' : 𝓞 K) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    cubSym a (b * b') = cubSym a b * cubSym a b' := by
  have h := Ideal.powerResidueSymbolIdeal_mul_right (n := 3) (𝔞 := Ideal.span {b})
    (𝔟 := Ideal.span {b'}) (by simpa using hb) (by simpa using hb') a
  rw [ideal_congr (Ideal.span_singleton_mul_span_singleton b b') a] at h
  exact h

theorem cubSym_unit_right (a b : 𝓞 K) (hb : IsUnit b) : cubSym a b = 1 := by
  unfold cubSym
  rw [ideal_congr (Ideal.span_singleton_eq_top.mpr hb) a]
  exact Ideal.powerResidueSymbolIdeal_top _

theorem norm_ne_three {x : 𝓞 K} (hx : IsPrimaryEisenstein x) : Algebra.norm ℤ x ≠ 3 := by
  intro h
  have hc := hx.absNorm_span_singleton_coprime_three
  rw [Ideal.absNorm_span_singleton, h] at hc
  exact absurd hc (by decide)

/-- The nontrivial automorphism of `𝓞 K`. -/
def conj : 𝓞 K ≃+* 𝓞 K :=
  MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) ((IsCyclotomicExtension.Rat.galEquivZMod 3 K).symm (-1))

theorem conj_pow_two {x : 𝓞 K} (hx : x ^ 3 = 1) : conj x = x ^ 2 := by
  have hs := IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq 3 K
    ((IsCyclotomicExtension.Rat.galEquivZMod 3 K).symm (-1)) hx
  rw [MulEquiv.apply_symm_apply] at hs
  exact hs

theorem conj_eq (x : 𝓞 K) : ∃ a b : ℤ, x = a + b * (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger ∧
    conj x = a + b * (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger ^ 2 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  obtain ⟨a, b, hab⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  refine ⟨a, b, hab.symm, ?_⟩
  rw [← hab, map_add, map_mul, map_intCast, map_intCast,
    conj_pow_two hζ.toInteger_cube_eq_one]

theorem conj_conj (x : 𝓞 K) : conj (conj x) = x := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  obtain ⟨a, b, rfl, h⟩ := conj_eq x
  have h3 := hζ.toInteger_cube_eq_one
  rw [h, map_add, map_mul, map_intCast, map_intCast, map_pow, conj_pow_two h3]
  have : (hζ.toInteger ^ 2) ^ 2 = hζ.toInteger := by
    calc (hζ.toInteger ^ 2) ^ 2 = hζ.toInteger ^ 3 * hζ.toInteger := by ring
      _ = hζ.toInteger := by rw [h3, one_mul]
  rw [this]

theorem add_conj (x : 𝓞 K) : ∃ t : ℤ, x + conj x = t := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  obtain ⟨a, b, rfl, h⟩ := conj_eq x
  have h2 : hζ.toInteger ^ 2 = -hζ.toInteger - 1 := IsCyclotomicExtension.Rat.Three.eta_sq hζ
  refine ⟨2 * a - b, ?_⟩
  rw [h, h2]
  push_cast
  ring

theorem mul_conj (x : 𝓞 K) : ∃ n : ℤ, x * conj x = n ∧ Algebra.norm ℤ x = n := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  obtain ⟨a, b, rfl, h⟩ := conj_eq x
  have h2 : hζ.toInteger ^ 2 = -hζ.toInteger - 1 := IsCyclotomicExtension.Rat.Three.eta_sq hζ
  have h3 := hζ.toInteger_cube_eq_one
  refine ⟨a ^ 2 - a * b + b ^ 2, ?_, hζ.norm_intCast_add_intCast_mul_toInteger_of_three a b⟩
  rw [h]
  push_cast
  linear_combination (b ^ 2) * h3 + (a * b) * h2

theorem conj_prime {x : 𝓞 K} (hx : Prime x) : Prime (conj x) :=
  (MulEquiv.prime_iff (conj (K := K)).toMulEquiv).mpr hx

theorem conj_primary {x : 𝓞 K} (hx : IsPrimaryEisenstein x) : IsPrimaryEisenstein (conj x) := by
  obtain ⟨c, hc⟩ := hx
  refine ⟨conj c, ?_⟩
  have := congrArg conj hc
  rw [map_sub, map_mul, map_ofNat, map_ofNat] at this
  exact this

theorem conj_cs (a b : 𝓞 K) : conj (cubSym a b) = cubSym (conj a) (conj b) := by
  have h := Ideal.map_powerResidueSymbolIdeal (n := 3) (Ideal.span {b}) (conj (K := K)) a
  rw [Ideal.map_span, Set.image_singleton] at h
  unfold cubSym
  rw [h]

theorem cubSym_conj_comm {ρ : 𝓞 K} (hρ : Prime ρ) (hp : IsPrimaryEisenstein ρ) :
    cubSym (conj ρ) ρ = cubSym ρ (conj ρ) := by
  obtain ⟨t, ht⟩ := add_conj ρ
  have h3t : ¬ (3 : ℤ) ∣ t := by
    intro h3
    obtain ⟨c, hc⟩ := id hp
    obtain ⟨c', hc'⟩ := conj_primary hp
    have h4 : (3 : ℤ) ∣ t - 1 := by
      refine (NumberField.RingOfIntegers.intCast_dvd_intCast (K := K) (m := 3) (n := t - 1)).mp ?_
      refine ⟨c + c' + 1, ?_⟩
      push_cast
      rw [← ht]
      linear_combination hc + hc'
    omega
  have hmk : Ideal.Quotient.mk (Ideal.span {ρ}) (conj ρ) =
      Ideal.Quotient.mk (Ideal.span {ρ}) (t : 𝓞 K) := by
    rw [Ideal.Quotient.eq, ← ht]
    have : conj ρ - (ρ + conj ρ) = -ρ := by ring
    rw [this]
    exact (Ideal.span {ρ}).neg_mem (Ideal.mem_span_singleton_self ρ)
  have hL : cubSym (conj ρ) ρ = cubSym (t : 𝓞 K) ρ := by
    unfold cubSym
    rw [hmk]
  have hrec : cubSym (t : 𝓞 K) ρ = cubSym ρ (t : 𝓞 K) := hp.cubic_reciprocity_intCast hρ h3t
  have hz : conj (cubSym ρ (t : 𝓞 K)) = cubSym ρ (t : 𝓞 K) := by
    rw [conj_cs, map_intCast]
    have hmk' : Ideal.Quotient.mk (Ideal.span {(t : 𝓞 K)}) (conj ρ) =
        Ideal.Quotient.mk (Ideal.span {(t : 𝓞 K)}) (-ρ) := by
      rw [Ideal.Quotient.eq]
      have : conj ρ - -ρ = (t : 𝓞 K) := by rw [← ht]; ring
      rw [this]
      exact Ideal.mem_span_singleton_self _
    have : cubSym (conj ρ) (t : 𝓞 K) = cubSym (-ρ) (t : 𝓞 K) := by
      unfold cubSym
      rw [hmk']
    rw [this, cubSym_neg_left]
  have := conj_cs (conj ρ) ρ
  rw [conj_conj] at this
  rw [← this, hL, hrec, hz]

theorem cubSym_one_left (b : 𝓞 K) : cubSym 1 b = 1 := by
  simp [cubSym]

theorem dvd_norm_natAbs {σ : 𝓞 K} : σ ∣ (((Algebra.norm ℤ σ).natAbs : ℕ) : 𝓞 K) := by
  rw [← Ideal.absNorm_span_singleton, ← Ideal.mem_span_singleton]
  exact Ideal.absNorm_mem _

theorem cubSym_comm_prime {ρ σ : 𝓞 K} (hρ : Prime ρ) (hσ : Prime σ) (hρp : IsPrimaryEisenstein ρ)
    (hσp : IsPrimaryEisenstein σ) (hn : ¬ ρ ∣ σ) : cubSym σ ρ = cubSym ρ σ := by
  by_cases hN : Algebra.norm ℤ ρ = Algebra.norm ℤ σ
  · obtain ⟨n, hn1, hn2⟩ := mul_conj ρ
    have hσn : σ ∣ (n : 𝓞 K) := by
      have h := dvd_norm_natAbs (σ := σ)
      rw [← hN, hn2] at h
      rcases Int.natAbs_eq n with h' | h'
      · rw [h'] at *; simpa using h
      · have : (n : 𝓞 K) = -((n.natAbs : ℕ) : 𝓞 K) := by
          rw [← Int.cast_natCast, ← Int.cast_neg, ← h']
        rw [this]; exact h.neg_right
    rw [← hn1] at hσn
    rcases hσ.dvd_or_dvd hσn with h | h
    · exact absurd (hσ.irreducible.dvd_symm hρ.irreducible h) hn
    · have hassoc : Associated σ (conj ρ) :=
        hσ.irreducible.associated_of_dvd (conj_prime hρ).irreducible h
      have := (hσ.existsUnique_associated_isPrimaryEisenstein (norm_ne_three hσp)).unique
        (y₁ := σ) (y₂ := conj ρ) ⟨Associated.refl σ, hσp⟩ ⟨hassoc, conj_primary hρp⟩
      rw [this]
      exact cubSym_conj_comm hρ hρp
  · exact hρp.cubic_reciprocity hσp hρ hσ hN

theorem cubSym_comm_layer2 {ρ : 𝓞 K} (hρ : Prime ρ) (hρp : IsPrimaryEisenstein ρ) {x : 𝓞 K}
    (hx0 : x ≠ 0) (hx : IsPrimaryEisenstein x) (hnd : ¬ ρ ∣ x) : cubSym x ρ = cubSym ρ x := by
  revert hnd
  refine primary_induction (Q := fun x => ¬ ρ ∣ x → cubSym x ρ = cubSym ρ x) ?_ ?_ hx0 hx
  · intro _
    rw [cubSym_neg_left, cubSym_neg_right, cubSym_one_left, cubSym_unit_right _ _ isUnit_one]
  · intro σ δ hσ hσp hδp hδ0 ih hnd
    have h1 : ¬ ρ ∣ σ := fun h => hnd (by rw [dvd_neg]; exact h.mul_right _)
    have h2 : ¬ ρ ∣ δ := fun h => hnd (by rw [dvd_neg]; exact h.mul_left _)
    rw [cubSym_neg_left, cubSym_neg_right, cubSym_mul_left, cubSym_mul_right _ _ _ hσ.ne_zero hδ0,
      ih h2, cubSym_comm_prime hρ hσ hρp hσp h1]

omit [IsCyclotomicExtension {3} ℚ K] in
theorem exists_sign {a : 𝓞 K}
    (h : a - 1 ∈ Ideal.span {(3 : 𝓞 K)} ∨ a + 1 ∈ Ideal.span {(3 : 𝓞 K)}) :
    ∃ a' : 𝓞 K, (a' = a ∨ a' = -a) ∧ IsPrimaryEisenstein a' := by
  rcases h with h | h
  · rw [Ideal.mem_span_singleton] at h
    refine ⟨-a, Or.inr rfl, ?_⟩
    rw [isPrimaryEisenstein_iff, show -a - 2 = -(a - 1) - 3 by ring]
    exact (dvd_neg.mpr h).sub dvd_rfl
  · rw [Ideal.mem_span_singleton] at h
    refine ⟨a, Or.inl rfl, ?_⟩
    rw [isPrimaryEisenstein_iff, show a - 2 = (a + 1) - 3 by ring]
    exact h.sub dvd_rfl

theorem cubSym_comm_primary {x y : 𝓞 K} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : IsPrimaryEisenstein x)
    (hy : IsPrimaryEisenstein y) (hxy : IsCoprime x y) : cubSym x y = cubSym y x := by
  revert hxy
  refine primary_induction (Q := fun y => IsCoprime x y → cubSym x y = cubSym y x) ?_ ?_ hy0 hy
  · intro _
    rw [cubSym_neg_left, cubSym_neg_right, cubSym_one_left, cubSym_unit_right _ _ isUnit_one]
  · intro σ δ hσ hσp hδp hδ0 ih hxy
    rw [IsCoprime.neg_right_iff, IsCoprime.mul_right_iff] at hxy
    have h1 : ¬ σ ∣ x := fun h => hσ.not_isUnit (hxy.1.symm.isUnit_of_dvd' dvd_rfl h)
    rw [cubSym_neg_left, cubSym_neg_right, cubSym_mul_left, cubSym_mul_right _ _ _ hσ.ne_zero hδ0,
      ih hxy.2, cubSym_comm_layer2 hσ hσp hx0 hx h1]

/-- Cubic reciprocity for coprime `a, b ≡ ±1 (mod 3)` in `ℤ[ω]`. -/
theorem cubSym_comm {a b : 𝓞 K} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : IsCoprime a b)
    (ha : a - 1 ∈ Ideal.span {(3 : 𝓞 K)} ∨ a + 1 ∈ Ideal.span {(3 : 𝓞 K)})
    (hb : b - 1 ∈ Ideal.span {(3 : 𝓞 K)} ∨ b + 1 ∈ Ideal.span {(3 : 𝓞 K)}) :
    cubSym a b = cubSym b a := by
  obtain ⟨a', ha', hap⟩ := exists_sign ha
  obtain ⟨b', hb', hbp⟩ := exists_sign hb
  have hsa : ∀ c, cubSym a' c = cubSym a c := by
    intro c; rcases ha' with rfl | rfl
    · rfl
    · exact cubSym_neg_left _ _
  have hsb : ∀ c, cubSym c b' = cubSym c b := by
    intro c; rcases hb' with rfl | rfl
    · rfl
    · exact cubSym_neg_right _ _
  have hsa' : ∀ c, cubSym c a' = cubSym c a := by
    intro c; rcases ha' with rfl | rfl
    · rfl
    · exact cubSym_neg_right _ _
  have hsb' : ∀ c, cubSym b' c = cubSym b c := by
    intro c; rcases hb' with rfl | rfl
    · rfl
    · exact cubSym_neg_left _ _
  have ha0' : a' ≠ 0 := by rcases ha' with rfl | rfl <;> simpa using ha0
  have hb0' : b' ≠ 0 := by rcases hb' with rfl | rfl <;> simpa using hb0
  have hab' : IsCoprime a' b' := by
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;>
      simpa [IsCoprime.neg_left_iff, IsCoprime.neg_right_iff] using hab
  have := cubSym_comm_primary ha0' hb0' hap hbp hab'
  rw [hsa, hsb, hsa', hsb'] at this
  exact this

/-! ### Comparison with `powerResidueElt` -/

section Bridge

open NumberFieldKB.MilneCFT.Ch8 IsDedekindDomain
open scoped nonZeroDivisors

theorem powerResidue_pow_three (a : K) (v : HeightOneSpectrum (𝓞 K)) :
    powerResidue 3 a v ^ 3 = 1 := by
  unfold powerResidue
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_pow _

theorem powerResidue_ne_zero (a : K) (v : HeightOneSpectrum (𝓞 K)) :
    powerResidue 3 a v ≠ 0 := by
  intro h
  have := powerResidue_pow_three a v
  rw [h] at this
  simp at this

/-- The prime ideal `(ρ)` as a point of the spectrum. -/
def specOf {ρ : 𝓞 K} (hρ : Prime ρ) : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {ρ}
  isPrime := (Ideal.span_singleton_prime hρ.ne_zero).mpr hρ
  ne_bot := by simpa using hρ.ne_zero

theorem powerResidue_prime {ρ a : 𝓞 K} (hρ : Prime ρ) (h3 : ¬ ρ ∣ 3) (ha : ¬ ρ ∣ a) :
    powerResidue 3 (a : K) (specOf hρ) = ((cubSym a ρ : 𝓞 K) : K) := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  set v := specOf hρ with hv
  have hvI : v.asIdeal = Ideal.span {ρ} := rfl
  have hmax : (Ideal.span {ρ}).IsMaximal := v.isMaximal
  have h3v : ((3 : ℕ) : 𝓞 K) ∉ v.asIdeal := by
    rw [hvI, Ideal.mem_span_singleton]; simpa using h3
  have hav : a ∉ v.asIdeal := by
    rw [hvI, Ideal.mem_span_singleton]; exact ha
  have hval : v.valuation K (a : K) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := K) (r := a)).2 hav
  have hvS : v ∉ Sset 3 {(a : K)} := (notMem_Sset_iff v 3 (a : K)).2 ⟨h3v, hval⟩
  have hN : (Ideal.absNorm (Ideal.span {ρ})).Coprime 3 := by
    have h := NumberFieldKB.MilneCFT.Ch8.dvd_absNorm_sub_one v (n := 3) (by norm_num) hζ h3v
    rw [hvI] at h
    have h1 : 1 ≤ Ideal.absNorm (Ideal.span {ρ}) := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [Ideal.absNorm_eq_zero_iff] at h0
      exact hρ.ne_zero (by simpa using h0)
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
    omega
  have hxne : Ideal.Quotient.mk (Ideal.span {ρ}) a ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact ha
  have hcs : cubSym a ρ = Ideal.powerResidueSymbol (Ideal.span {ρ}) 3 (Ideal.Quotient.mk _ a) := by
    unfold cubSym
    rw [Ideal.powerResidueSymbolIdeal_of_isMaximal]
  have hpow := Ideal.powerResidueSymbol_pow_eq_one hN hxne
  have hm : Ideal.Quotient.mk (Ideal.span {ρ})
      (Ideal.powerResidueSymbol (Ideal.span {ρ}) 3 (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk (Ideal.span {ρ}) (a ^ ((Ideal.absNorm (Ideal.span {ρ}) - 1) / 3)) := by
    rw [Ideal.mk_powerResidueSymbol hN hxne, map_pow]
  rw [hcs]
  refine (powerResidue_unique 3 (by norm_num) _ hζ (a : K) v hvS _ ⟨?_, ?_⟩).symm
  · have h := congrArg (fun z : 𝓞 K => (z : K)) hpow
    simpa using h
  · rw [hvI]
    have h := (v.valuation_lt_one_iff_mem (K := K)
      (Ideal.powerResidueSymbol (Ideal.span {ρ}) 3 (Ideal.Quotient.mk _ a) -
        a ^ ((Ideal.absNorm (Ideal.span {ρ}) - 1) / 3))).2 (by
          rw [hvI]; exact Ideal.Quotient.eq.mp hm)
    simpa using h

open Classical in
theorem mulSupport_finite (a b : K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => if v ∈ Sset 3 {a} then (1 : K) else
      powerResidue 3 a v ^ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ b)).Finite := by
  refine (Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 K)⁰ b))).subset ?_
  intro v hv
  intro h
  apply hv
  simp [h]

theorem elt_mul (a b₁ b₂ : K) (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0) :
    powerResidueElt 3 a (b₁ * b₂) = powerResidueElt 3 a b₁ * powerResidueElt 3 a b₂ := by
  unfold powerResidueElt
  rw [← finprod_mul_distrib (mulSupport_finite a b₁) (mulSupport_finite a b₂)]
  refine finprod_congr fun v => ?_
  by_cases hv : v ∈ Sset 3 {a}
  · simp [hv]
  · simp only [hv, if_false]
    rw [map_mul, FractionalIdeal.count_mul,
      zpow_add₀ (powerResidue_ne_zero a v)]
    · exact (FractionalIdeal.spanSingleton_ne_zero_iff).mpr h₁
    · exact (FractionalIdeal.spanSingleton_ne_zero_iff).mpr h₂

theorem elt_unit (a : K) (u : 𝓞 K) (hu : IsUnit u) : powerResidueElt 3 a (u : K) = 1 := by
  unfold powerResidueElt
  have : FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K) = 1 := by
    rw [← FractionalIdeal.coeIdeal_top, ← Ideal.span_singleton_eq_top.mpr hu,
      FractionalIdeal.coeIdeal_span_singleton]
  simp only [this, FractionalIdeal.count_one, zpow_zero, ite_self, finprod_one]

open Classical in
theorem elt_prime {ρ : 𝓞 K} (hρ : Prime ρ) (a : K) :
    powerResidueElt 3 a (ρ : K) =
      if specOf hρ ∈ Sset 3 {a} then 1 else powerResidue 3 a (specOf hρ) := by
  unfold powerResidueElt
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (ρ : K) =
      ((specOf hρ).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
    show _ = ((Ideal.span {ρ} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [FractionalIdeal.coeIdeal_span_singleton]
  rw [hspan]
  classical
  rw [finprod_eq_single _ (specOf hρ)]
  · by_cases hv : specOf hρ ∈ Sset 3 {a}
    · simp [hv]
    · simp [hv, FractionalIdeal.count_self]
  · intro w hw
    by_cases hS : w ∈ Sset 3 {a}
    · simp [hS]
    · simp only [hS, if_false]
      rw [FractionalIdeal.count_maximal K w (specOf hρ)]
      simp [hw.symm]

theorem elt_eq_cubSym (a : 𝓞 K) {b : 𝓞 K} (hb0 : b ≠ 0) (hab : IsCoprime a b)
    (h3b : IsCoprime (3 : 𝓞 K) b) :
    powerResidueElt 3 (a : K) (b : K) = ((cubSym a b : 𝓞 K) : K) := by
  have := IsCyclotomicExtension.Rat.three_pid K
  revert hb0 hab h3b
  induction b using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ b hb =>
    intro _ _ _
    rw [elt_unit _ b hb, cubSym_unit_right _ _ hb]
    simp
  | h₃ b ρ hb0 hρ ih =>
    intro _ hab h3b
    rw [IsCoprime.mul_right_iff] at hab h3b
    have hρ0 : (ρ : K) ≠ 0 := by
      simpa using hρ.ne_zero
    have hb0' : (b : K) ≠ 0 := by simpa using hb0
    rw [mul_comm ρ b]
    push_cast
    rw [elt_mul _ _ _ hb0' hρ0, cubSym_mul_right _ _ _ hb0 hρ.ne_zero, ih hb0 hab.2 h3b.2]
    have h1 : ¬ ρ ∣ a := fun h => hρ.not_isUnit (hab.1.symm.isUnit_of_dvd' dvd_rfl h)
    have h2 : ¬ ρ ∣ 3 := fun h => hρ.not_isUnit (h3b.1.symm.isUnit_of_dvd' dvd_rfl h)
    have hS : specOf hρ ∉ Sset 3 {(a : K)} := by
      rw [notMem_Sset_iff]
      refine ⟨?_, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) (v := specOf hρ)
        (r := a)).2 ?_⟩
      · show ((3 : ℕ) : 𝓞 K) ∉ Ideal.span {ρ}
        rw [Ideal.mem_span_singleton]; simpa using h2
      · show a ∉ Ideal.span {ρ}
        rw [Ideal.mem_span_singleton]; exact h1
    rw [elt_prime hρ, if_neg hS, powerResidue_prime hρ h2 h1]
    push_cast
    ring

end Bridge

/-- **Cubic reciprocity in terms of `powerResidueElt`.** -/
theorem cubic_reciprocity_elt {a b : 𝓞 K} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : IsCoprime a b)
    (ha : a - 1 ∈ Ideal.span {(3 : 𝓞 K)} ∨ a + 1 ∈ Ideal.span {(3 : 𝓞 K)})
    (hb : b - 1 ∈ Ideal.span {(3 : 𝓞 K)} ∨ b + 1 ∈ Ideal.span {(3 : 𝓞 K)}) :
    NumberFieldKB.MilneCFT.Ch8.powerResidueElt 3 (a : K) (b : K) =
      NumberFieldKB.MilneCFT.Ch8.powerResidueElt 3 (b : K) (a : K) := by
  have h3 : ∀ {c : 𝓞 K}, (c - 1 ∈ Ideal.span {(3 : 𝓞 K)} ∨ c + 1 ∈ Ideal.span {(3 : 𝓞 K)}) →
      IsCoprime (3 : 𝓞 K) c := by
    intro c hc
    rcases hc with h | h
    · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp h
      exact ⟨-d, 1, by linear_combination hd⟩
    · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp h
      exact ⟨d, -1, by linear_combination (-1 : 𝓞 K) * hd⟩
  rw [elt_eq_cubSym a hb0 hab (h3 hb), elt_eq_cubSym b ha0 hab.symm (h3 ha), cubSym_comm ha0 hb0 hab ha hb]

omit [IsCyclotomicExtension {3} ℚ K] in
/-- A number field of degree $2$ containing a primitive cube root of $1$ is $\mathbb Q(\zeta_3)$. -/
theorem isCyclotomicExtension_three (h : Module.finrank ℚ K = 2) {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    IsCyclotomicExtension {3} ℚ K := by
  have hS := hζ.adjoin_isCyclotomicExtension ℚ
  have hfr : Module.finrank ℚ (Algebra.adjoin ℚ {ζ}) = 2 := by
    rw [IsCyclotomicExtension.finrank (n := 3) (Algebra.adjoin ℚ {ζ})
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    rw [Nat.totient_prime Nat.prime_three]
  have htop : Algebra.adjoin ℚ {ζ} = ⊤ := by
    apply Algebra.toSubmodule_eq_top.1
    apply Submodule.eq_top_of_finrank_eq
    rw [Subalgebra.finrank_toSubmodule, hfr, h]
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨ζ, hζ⟩, fun x => ?_⟩
  have hx : x ∈ Algebra.adjoin ℚ {ζ} := by rw [htop]; trivial
  exact Algebra.adjoin_mono (by simpa using hζ.pow_eq_one) hx

/-- Cubes in `(ℤ/p)ˣ`. -/
theorem exists_cube_iff {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) {a : ZMod p} (ha : a ≠ 0) :
    (∃ x : ZMod p, x ^ 3 = a) ↔ a ^ ((p - 1) / 3) = 1 := by
  have hp1 := (Fact.out : p.Prime).one_lt
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x ≠ 0 := by rintro rfl; simp at ha
    rw [← pow_mul, Nat.mul_div_cancel' (by omega)]
    exact ZMod.pow_card_sub_one_eq_one hx
  · intro h
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    let u : (ZMod p)ˣ := Units.mk0 a ha
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).2 (hg u)
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    have hu : u ^ ((p - 1) / 3) = 1 := Units.ext (by simpa [u] using h)
    rw [← hk, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hord] at hu
    obtain ⟨c, hc⟩ := hu
    have h3 : 3 ∣ k := by
      have hm : 0 < (p - 1) / 3 := by omega
      have : (p - 1) / 3 * 3 = p - 1 := Nat.div_mul_cancel (by omega)
      refine ⟨c, ?_⟩
      have h2 : k * ((p - 1) / 3) = (3 * c) * ((p - 1) / 3) := by
        rw [hc]; nlinarith
      exact Nat.eq_of_mul_eq_mul_right hm h2
    obtain ⟨j, rfl⟩ := h3
    refine ⟨((g ^ j : (ZMod p)ˣ) : ZMod p), ?_⟩
    have : (g ^ j) ^ 3 = u := by rw [← hk, ← pow_mul, mul_comm]
    simpa [u] using congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) this

/-- A split prime `p ≡ 1 (mod 3)` is `π π̄`: a primary prime `π` with `ℤ[ω] / π = ℤ/p`. -/
theorem exists_prime_over {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ (π : 𝓞 K) (φ : 𝓞 K →+* ZMod p), Prime π ∧ IsPrimaryEisenstein π ∧
      RingHom.ker φ = Ideal.span {π} ∧ Ideal.absNorm (Ideal.span {π}) = p := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hp1 := (Fact.out : p.Prime).one_lt
  have := IsCyclotomicExtension.Rat.three_pid K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card (ZMod p)ˣ := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]; omega
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := (ZMod p)ˣ) 3 h3
  have hω : IsPrimitiveRoot (g : ZMod p) 3 :=
    (IsPrimitiveRoot.coe_units_iff).2 (IsPrimitiveRoot.iff_orderOf.2 hg)
  have hsum := hω.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
  have hy : Polynomial.aeval (g : ZMod p) (minpoly ℤ hζ.integralPowerBasis.gen) = 0 := by
    rw [hζ.integralPowerBasis_gen, hζ.minpoly_toInteger_eq_X_sq_add_X_add_one]
    simp
    linear_combination hsum
  let φ : 𝓞 K →+* ZMod p := (hζ.integralPowerBasis.lift (g : ZMod p) hy).toRingHom
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨(n : 𝓞 K), by simp [φ]⟩
  have hmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  set π0 := Submodule.IsPrincipal.generator (RingHom.ker φ) with hπ0
  have hker : Ideal.span {π0} = RingHom.ker φ := Ideal.span_singleton_generator _
  have hpker : ((p : ℕ) : 𝓞 K) ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker]; simp
  have hπ00 : π0 ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hker
    rw [← hker] at hpker
    simp at hpker
    exact (Fact.out : p.Prime).ne_zero hpker
  have hprime0 : Prime π0 := by
    rw [← Ideal.span_singleton_prime hπ00, hker]
    exact hmax.isPrime
  have habs : Ideal.absNorm (Ideal.span {π0}) = p := by
    rw [hker, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv, Nat.card_zmod]
  have hN : Algebra.norm ℤ π0 ≠ 3 := by
    intro h
    rw [Ideal.absNorm_span_singleton, h] at habs
    simp at habs
    omega
  obtain ⟨π, ⟨hassoc, hprim⟩, -⟩ := hprime0.existsUnique_associated_isPrimaryEisenstein hN
  have hspan : Ideal.span {π} = Ideal.span {π0} :=
    (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm
  refine ⟨π, φ, hassoc.prime hprime0, hprim, ?_, ?_⟩
  · rw [hspan, hker]
  · rw [hspan, habs]

theorem two_cube_iff_symbol {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) {π : 𝓞 K} {φ : 𝓞 K →+* ZMod p}
    (hπ : Prime π) (hker : RingHom.ker φ = Ideal.span {π}) (habs : Ideal.absNorm (Ideal.span {π}) = p) :
    (∃ x : ZMod p, x ^ 3 = 2) ↔ cubSym ((2 : ℤ) : 𝓞 K) π = 1 := by
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmax : (Ideal.span {π}).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal (by simpa using hπ.ne_zero)
  have hN : (Ideal.absNorm (Ideal.span {π})).Coprime 3 := by
    rw [habs]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)).symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hx : Ideal.Quotient.mk (Ideal.span {π}) (2 : 𝓞 K) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, ← hker, RingHom.mem_ker]
    rw [map_ofNat]; exact h2
  have hcs : cubSym ((2 : ℤ) : 𝓞 K) π =
      Ideal.powerResidueSymbol (Ideal.span {π}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
    unfold cubSym
    rw [Ideal.powerResidueSymbolIdeal_of_isMaximal]
    norm_num
  rw [hcs, exists_cube_iff hp h2, Ideal.powerResidueSymbol_eq_iff hN hx (one_pow 3), habs]
  have hmk : (Ideal.Quotient.mk (Ideal.span {π}) (2 : 𝓞 K)) ^ ((p - 1) / 3) =
      Ideal.Quotient.mk (Ideal.span {π}) ((2 : 𝓞 K) ^ ((p - 1) / 3)) := by rw [map_pow]
  rw [hmk, Ideal.Quotient.eq, ← hker, RingHom.mem_ker, map_sub, map_one, map_pow, map_ofNat,
    sub_eq_zero, eq_comm]

theorem two_dvd_iff (a b : ℤ) :
    (2 : 𝓞 K) ∣ (a : 𝓞 K) + b * (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger ↔
      (2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b := by
  have := (IsCyclotomicExtension.zeta_spec 3 ℚ K).intCast_dvd_intCast_add_intCast_mul_toInteger_iff
    (m := 2) (a := a) (b := b) (by decide)
  simpa using this

theorem norm_two : Algebra.norm ℤ (2 : 𝓞 K) = 4 := by
  have h : (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 := by simp
  rw [h, Algebra.norm_algebraMap, finrank_ringOfIntegers_three]
  norm_num

theorem absNorm_span_two : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 4 := by
  rw [Ideal.absNorm_span_singleton, norm_two]; rfl

theorem span_two_maximal : (Ideal.span {(2 : 𝓞 K)}).IsMaximal := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  rw [Ideal.isMaximal_iff]
  refine ⟨?_, ?_⟩
  · rw [Ideal.mem_span_singleton]
    intro h
    have := (two_dvd_iff (K := K) 1 0).1 (by simpa using h)
    omega
  · intro J x hJ hx hxJ
    obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
    rw [Ideal.mem_span_singleton, two_dvd_iff] at hx
    obtain ⟨n, hn, hn2⟩ := mul_conj ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)
    rw [hζ.norm_intCast_add_intCast_mul_toInteger_of_three] at hn2
    have hnJ : (n : 𝓞 K) ∈ J := by rw [← hn]; exact J.mul_mem_right _ hxJ
    have hodd : ¬ (2 : ℤ) ∣ n := by
      rw [← hn2]
      intro h
      apply hx
      have h' : ((a ^ 2 - a * b + b ^ 2 : ℤ) : ZMod 2) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
      have ha : ∀ a b : ZMod 2, a ^ 2 - a * b + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
      push_cast at h'
      obtain ⟨h1, h2⟩ := ha _ _ h'
      exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 2).1 h1, (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).1 h2⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have h2J : (2 : 𝓞 K) ∈ J := hJ (Ideal.mem_span_singleton_self _)
    have : (1 : 𝓞 K) = (n : 𝓞 K) - (m : 𝓞 K) * 2 := by
      rw [hm]; push_cast; ring
    rw [this]
    exact J.sub_mem hnJ (J.mul_mem_left _ h2J)

theorem sym_two_iff {π : 𝓞 K} (hodd : Odd (Ideal.absNorm (Ideal.span {π}))) :
    cubSym π ((2 : ℤ) : 𝓞 K) = 1 ↔ (2 : 𝓞 K) ∣ π - 1 := by
  have hmax := span_two_maximal (K := K)
  have hN : (Ideal.absNorm (Ideal.span {(2 : 𝓞 K)})).Coprime 3 := by
    rw [absNorm_span_two]; decide
  have hx : Ideal.Quotient.mk (Ideal.span {(2 : 𝓞 K)}) π ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    intro h2
    have h := map_dvd (Algebra.norm ℤ) h2
    rw [norm_two] at h
    rw [Ideal.absNorm_span_singleton] at hodd
    have h4 : (4 : ℕ) ∣ (Algebra.norm ℤ π).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h
      simpa using this
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcs : cubSym π ((2 : ℤ) : 𝓞 K) =
      Ideal.powerResidueSymbol (Ideal.span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) := by
    unfold cubSym
    have : ((2 : ℤ) : 𝓞 K) = 2 := by norm_num
    rw [this, Ideal.powerResidueSymbolIdeal_of_isMaximal]
  rw [hcs, Ideal.powerResidueSymbol_eq_iff hN hx (one_pow 3), absNorm_span_two]
  norm_num
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {(2 : 𝓞 K)})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton, ← dvd_neg, neg_sub]

theorem norm_nonneg' (z : 𝓞 K) : 0 ≤ Algebra.norm ℤ z := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  obtain ⟨a, b, rfl, -⟩ := conj_eq z
  rw [hζ.norm_intCast_add_intCast_mul_toInteger_of_three]
  nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

/-- The element `(x + 3y) + 6y ω` of norm `x² + 27 y²`. -/
def gam (x y : ℤ) : 𝓞 K :=
  ((x + 3 * y : ℤ) : 𝓞 K) + ((6 * y : ℤ) : 𝓞 K) * (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

theorem gam_mul (x y : ℤ) : gam (K := K) x y * gam x (-y) = ((x ^ 2 + 27 * y ^ 2 : ℤ) : 𝓞 K) := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have h2 : hζ.toInteger ^ 2 = -hζ.toInteger - 1 := IsCyclotomicExtension.Rat.Three.eta_sq hζ
  unfold gam
  push_cast
  linear_combination (-36 * (y : 𝓞 K) ^ 2) * h2

theorem norm_gam (x y : ℤ) : Algebra.norm ℤ (gam (K := K) x y) = x ^ 2 + 27 * y ^ 2 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  unfold gam
  rw [hζ.norm_intCast_add_intCast_mul_toInteger_of_three]
  ring

/-- The key divisibility. -/
theorem two_dvd_of_dvd_gam {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) {π : 𝓞 K} (hπ : Prime π)
    (hπp : IsPrimaryEisenstein π) (habs : Ideal.absNorm (Ideal.span {π}) = p) {x y : ℤ}
    (hxy : (p : ℤ) = x ^ 2 + 27 * y ^ 2) (hdiv : π ∣ gam x y) : (2 : 𝓞 K) ∣ π - 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hp1 := (Fact.out : p.Prime).one_lt
  have hp2 : p ≠ 2 := by omega
  have hpodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hNπ : Algebra.norm ℤ π = p := by
    rw [Ideal.absNorm_span_singleton] at habs
    have := norm_nonneg' π
    omega
  obtain ⟨c, hc⟩ := hdiv
  have hNc : Algebra.norm ℤ c = 1 := by
    have h := congrArg (Algebra.norm ℤ) hc
    rw [norm_gam, map_mul, hNπ, ← hxy] at h
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact (mul_right_cancel₀ hp0 (by linarith : (1 : ℤ) * p = Algebra.norm ℤ c * p)).symm
  have hunit : IsUnit c := by
    obtain ⟨n, hn1, hn2⟩ := mul_conj c
    rw [hNc] at hn2
    rw [← hn2] at hn1
    have h1 : c * conj c = 1 := by simpa using hn1
    exact ⟨⟨c, conj c, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hassoc : Associated π (gam x y) := ⟨hunit.unit, by simpa using hc.symm⟩
  -- the primary sign
  have hx3 : x % 3 = 1 ∨ x % 3 = 2 := by
    have hp3 : (p : ℤ) % 3 = 1 := by omega
    rw [hxy] at hp3
    by_contra hcon
    have h0 : x % 3 = 0 := by omega
    obtain ⟨k, hk⟩ : ∃ k, x = 3 * k := ⟨x / 3, by omega⟩
    subst hk
    have : (3 * k) ^ 2 + 27 * y ^ 2 = 3 * (3 * k ^ 2 + 9 * y ^ 2) := by ring
    omega
  have hxodd : (x + 3 * y) % 2 = 1 := by
    have hp2' : ((p : ℤ)) % 2 = 1 := by omega
    rw [hxy] at hp2'
    rcases Int.emod_two_eq_zero_or_one x with h1 | h1 <;> rcases Int.emod_two_eq_zero_or_one y with h2 | h2 <;>
      simp [pow_two, Int.add_emod, Int.mul_emod, h1, h2] at hp2' ⊢
  have hdvd : (2 : 𝓞 K) ∣ gam (K := K) x y - 1 := by
    have : gam (K := K) x y - 1 = ((x + 3 * y - 1 : ℤ) : 𝓞 K) + ((6 * y : ℤ) : 𝓞 K) * hζ.toInteger := by
      unfold gam; push_cast; ring
    rw [this]
    exact (two_dvd_iff _ _).2 ⟨by omega, ⟨3 * y, by ring⟩⟩
  rcases hx3 with h | h
  · -- `-γ` is primary
    have hprim : IsPrimaryEisenstein (-gam (K := K) x y) := by
      have : -gam (K := K) x y = ((-(x + 3 * y) : ℤ) : 𝓞 K) + ((-(6 * y) : ℤ) : 𝓞 K) * hζ.toInteger := by
        unfold gam; push_cast; ring
      rw [this, hζ.isPrimaryEisenstein_add_mul_iff]
      constructor <;> unfold Int.ModEq <;> omega
    have hass' : Associated π (-gam (K := K) x y) := hassoc.trans (by simp)
    have := (hπ.existsUnique_associated_isPrimaryEisenstein (norm_ne_three hπp)).unique
      ⟨Associated.refl π, hπp⟩ ⟨hass', hprim⟩
    rw [this]
    have h2 : (2 : 𝓞 K) ∣ (-gam (K := K) x y) - 1 := by
      have : (-gam (K := K) x y) - 1 = -(gam (K := K) x y - 1) - 2 := by ring
      rw [this]
      exact (dvd_neg.2 hdvd).sub dvd_rfl
    exact h2
  · have hprim : IsPrimaryEisenstein (gam (K := K) x y) := by
      unfold gam
      rw [hζ.isPrimaryEisenstein_add_mul_iff]
      constructor <;> unfold Int.ModEq <;> omega
    have := (hπ.existsUnique_associated_isPrimaryEisenstein (norm_ne_three hπp)).unique
      ⟨Associated.refl π, hπp⟩ ⟨hassoc, hprim⟩
    rw [this]
    exact hdvd

/-- Gauss/Jacobi: `2` is a cube mod `p` iff `p = x² + 27 y²`, in `ℚ(ζ₃)`. -/
theorem two_cube_iff_sq_add {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    (∃ x : ZMod p, x ^ 3 = 2) ↔ ∃ x y : ℤ, (p : ℤ) = x ^ 2 + 27 * y ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)
  obtain ⟨π, φ, hπ, hπp, hker, habs⟩ :=
    exists_prime_over (K := CyclotomicField 3 ℚ) hp3
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd (Ideal.absNorm (Ideal.span {π})) := by
    rw [habs]
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · exact h
  have hrec : cubSym ((2 : ℤ) : 𝓞 (CyclotomicField 3 ℚ)) π =
      cubSym π ((2 : ℤ) : 𝓞 (CyclotomicField 3 ℚ)) :=
    hπp.cubic_reciprocity_intCast hπ (by decide)
  rw [two_cube_iff_symbol hp3 hπ hker habs, hrec, sym_two_iff hodd]
  constructor
  · intro h2
    obtain ⟨a, b, hab⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) π
    rw [← hab, hζ.isPrimaryEisenstein_add_mul_iff] at hπp
    have hN : Algebra.norm ℤ π = p := by
      rw [Ideal.absNorm_span_singleton] at habs
      have := norm_nonneg' π
      omega
    rw [← hab, hζ.norm_intCast_add_intCast_mul_toInteger_of_three] at hN
    have h2' : (2 : 𝓞 (CyclotomicField 3 ℚ)) ∣ ((a - 1 : ℤ) : 𝓞 (CyclotomicField 3 ℚ)) +
        (b : 𝓞 (CyclotomicField 3 ℚ)) * hζ.toInteger := by
      rw [← hab] at h2
      convert h2 using 1
      push_cast; ring
    obtain ⟨ha2, hb2⟩ := (two_dvd_iff _ _).1 h2'
    obtain ⟨ha3, hb3⟩ := hπp
    unfold Int.ModEq at ha3 hb3
    obtain ⟨y, hy⟩ : ∃ y, b = 6 * y := ⟨b / 6, by omega⟩
    refine ⟨a - 3 * y, y, ?_⟩
    rw [← hN, hy]
    ring
  · rintro ⟨x, y, hxy⟩
    have hdvd : π ∣ gam (K := CyclotomicField 3 ℚ) x y * gam x (-y) := by
      rw [gam_mul, ← hxy]
      have := dvd_norm_natAbs (σ := π)
      rw [← Ideal.absNorm_span_singleton, habs] at this
      exact_mod_cast this
    rcases hπ.dvd_or_dvd hdvd with h | h
    · exact two_dvd_of_dvd_gam hp3 hπ hπp habs hxy h
    · exact two_dvd_of_dvd_gam hp3 hπ hπp habs (y := -y) (by rw [hxy]; ring) h

end CubicTC

/-- **Example 5.13, the cubic reciprocity law** (Milne, *CFT*, VIII, Example 5.13, p. 249; Eisenstein), proved from
Tau Ceti's cubic reciprocity: see the module docstring. -/
@[kb "milne2020cft" "Ch. VIII, Example 5.13, p. 249 (cubic reciprocity)"]
theorem example5_13 : Example5_13 := by
  refine ⟨fun K _ _ hfr ζ hζ a b ha0 hb0 hab ha hb => ?_⟩
  have := CubicTC.isCyclotomicExtension_three hfr hζ
  exact CubicTC.cubic_reciprocity_elt ha0 hb0 hab ha hb

/-- **Exercise 5.16** (Milne, *CFT*, VIII, Exercise 5.16, p. 250; Gauss/Jacobi): for a prime $p \equiv 1 \pmod 3$,
$2$ is a cube modulo $p$ iff $p = x^2 + 27y^2$; proved from cubic reciprocity in $\mathbb Q(\zeta_3)$
(`CubicTC.two_cube_iff_sq_add`). -/
@[kb "milne2020cft" "Ch. VIII, Exercise 5.16, p. 250"]
theorem exercise5_16 : Exercise5_16 :=
  ⟨fun _ hp hp3 => CubicTC.two_cube_iff_sq_add hp hp3⟩

end NumberFieldKB.MilneCFT.Ch8
