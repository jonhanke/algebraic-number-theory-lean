import NumberFieldKB.MilneCFT.Ch8.Eisenstein.LocalGlobal
import NumberFieldKB.MilneCFT.Ch8.Prop512

/-!
# The completion of $\mathbb Q(\zeta_p)$ at $\lambda = (\zeta - 1)$

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §5,
Proposition 5.12 (p. 248) and its setting: $K = \mathbb Q(\zeta_p)$, $\lambda = 1 - \zeta$, $K_\lambda$ the completion.

For $K = \mathbb Q(\zeta_p)$ and the prime `lamPlace hζ` $= (\zeta - 1)$ of $\mathcal O_K$:

* `lamPlace_irreducible`, `lamPlace_p_eq`, `lamPlace_card_residue`: the hypotheses of `prop_5_12` hold for the
  completion $K_\lambda$ (`(lamPlace hζ).adicCompletion K`), with uniformizer $\lambda = 1 - \zeta$,
  $p = \varepsilon \lambda^{p-1}$ and residue field $\mathbb F_p$;
* `hilbertPairing_intCast_primary`: in $K_\lambda$, the Hilbert pairing $(a, c\,w) = 1$ for rational integers $a, c$
  prime to $p$ and $w \equiv 1 \pmod{\lambda^2}$. This is the local input to Eisenstein reciprocity: by Fermat,
  $a^{p-1}, c^{p-1} \in U^{(p-1)}$, and Proposition 5.12 (b) kills $U^{(i)} \times U^{(j)}$ for $i + j \ge p + 1$.
-/

open scoped ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.Eisenstein

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- The prime $\lambda = (\zeta - 1)$ of $\mathcal O_K$, $K = \mathbb Q(\zeta_p)$. -/
def lamPlace : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {hζ.toInteger - 1}
  isPrime := IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one' p hζ
  ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hp.out.one_lt

theorem lamPlace_asIdeal : (lamPlace hζ).asIdeal = Ideal.span {hζ.toInteger - 1} := rfl

theorem absNorm_lamPlace : Ideal.absNorm (lamPlace hζ).asIdeal = p := by
  have hK : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by rw [zero_add, pow_one]; infer_instance
  have hζ' : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by rw [zero_add, pow_one]; exact hζ
  have := IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one p 0 hζ'
  rw [lamPlace_asIdeal]
  convert this using 4

/-- The completion $K_\lambda$. -/
abbrev Klam : Type := (lamPlace hζ).adicCompletion K

/-- The residue field of $K_\lambda$ has $p$ elements. -/
theorem lamPlace_card_residue : Nat.card 𝓀[(Klam hζ)] = p := by
  rw [HeightOneSpectrum.natCard_residueField_adicCompletion_eq_absNorm, absNorm_lamPlace]

/-- The valuation of $1 - \zeta$ at $\lambda$ is $\exp(-1)$. -/
theorem valued_one_sub_zeta :
    Valued.v (algebraMap K (Klam hζ) (1 - ζ)) = WithZero.exp (-1) := by
  have hz : algebraMap (𝓞 K) K hζ.toInteger = ζ := hζ.coe_toInteger
  have h1 : (1 - ζ : K) = algebraMap (𝓞 K) K (-(hζ.toInteger - 1)) := by
    rw [map_neg, map_sub, map_one, hz]; ring
  rw [h1, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply,
    HeightOneSpectrum.valuation_of_algebraMap]
  have hne : -(hζ.toInteger - 1) ≠ 0 :=
    neg_ne_zero.mpr (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hp.out.one_lt)
  refine HeightOneSpectrum.intValuation_singleton _ hne ?_
  rw [lamPlace_asIdeal, Ideal.span_singleton_neg]

theorem one_sub_zeta_ne_zero : (algebraMap K (Klam hζ) (1 - ζ)) ≠ 0 := by
  intro h
  have := valued_one_sub_zeta hζ
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

/-- $1 - \zeta$ as a unit of $K_\lambda$. -/
def lamUnitK : (Klam hζ)ˣ := Units.mk0 _ (one_sub_zeta_ne_zero hζ)

theorem lamUnitK_isUniformizer : TauCeti.IsUniformizer (Klam hζ) (lamUnitK hζ) :=
  (lamPlace hζ).isUniformizer_iff_valued_eq_exp_neg_one.mpr (valued_one_sub_zeta hζ)

/-- The uniformizer $\lambda = 1 - \zeta$ of $K_\lambda$, as an element of the ring of integers. -/
def lamInt : 𝒪[(Klam hζ)] :=
  ((TauCeti.isUniformizer_iff_exists_irreducible (Klam hζ) _).mp (lamUnitK_isUniformizer hζ)).choose

theorem lamPlace_irreducible : Irreducible (lamInt hζ) :=
  ((TauCeti.isUniformizer_iff_exists_irreducible (Klam hζ) _).mp (lamUnitK_isUniformizer hζ)).choose_spec.1

theorem coe_lamInt : ((lamInt hζ : 𝒪[(Klam hζ)]) : (Klam hζ)) = 1 - algebraMap K (Klam hζ) ζ := by
  unfold lamInt
  rw [((TauCeti.isUniformizer_iff_exists_irreducible (Klam hζ) _).mp (lamUnitK_isUniformizer hζ)).choose_spec.2]
  simp [lamUnitK]

/-- The image of an element of $\mathcal O_K$ in the ring of integers of $K_\lambda$. -/
def toLamInt (x : 𝓞 K) : 𝒪[(Klam hζ)] :=
  ⟨algebraMap (𝓞 K) (Klam hζ) x, HeightOneSpectrum.algebraMap_mem_integer_adicCompletion _ x⟩

theorem coe_toLamInt (x : 𝓞 K) : ((toLamInt hζ x : 𝒪[(Klam hζ)]) : (Klam hζ)) = algebraMap K (Klam hζ) (x : K) := by
  simp [toLamInt, IsScalarTower.algebraMap_apply (𝓞 K) K (Klam hζ)]

/-- The ring map $\mathcal O_K \to \mathcal O_{K_\lambda}$. -/
def toLamIntHom : 𝓞 K →+* 𝒪[(Klam hζ)] where
  toFun := toLamInt hζ
  map_one' := Subtype.ext (by simp [toLamInt])
  map_mul' x y := Subtype.ext (by simp [toLamInt])
  map_zero' := Subtype.ext (by simp [toLamInt])
  map_add' x y := Subtype.ext (by simp [toLamInt])

/-- $p = \varepsilon\lambda^{p-1}$ in $\mathcal O_{K_\lambda}$ with $\varepsilon$ a unit. -/
theorem lamPlace_p_eq (hp2 : p ≠ 2) :
    ∃ ε : 𝒪[(Klam hζ)], IsUnit ε ∧ (p : 𝒪[(Klam hζ)]) = ε * lamInt hζ ^ (p - 1) := by
  obtain ⟨u, hu⟩ := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ
  refine ⟨toLamIntHom hζ (u : 𝓞 K), (u.isUnit.map (toLamIntHom hζ)), ?_⟩
  have hev : Even (p - 1) := hp.out.even_sub_one hp2
  have hl : lamInt hζ = toLamIntHom hζ (-(hζ.toInteger - 1)) := by
    apply Subtype.ext
    rw [coe_lamInt]
    change _ = ((toLamInt hζ _ : 𝒪[(Klam hζ)]) : (Klam hζ))
    rw [coe_toLamInt, show ((-(hζ.toInteger - 1) : 𝓞 K) : K) = 1 - ζ by
      have hz : ((hζ.toInteger : 𝓞 K) : K) = ζ := hζ.coe_toInteger
      push_cast; simp only [hz]; ring, map_sub, map_one]
  rw [hl, ← map_pow, neg_pow, hev.neg_one_pow, one_mul, ← map_mul, mul_comm, hu, map_natCast]

/-! ### The local symbol of a rational integer against a primary element -/

variable {Ω : Type} [Field Ω] [Algebra (Klam hζ) Ω] [IsSepClosure (Klam hζ) Ω]

/-- A rational integer prime to $p$ raised to the power $p - 1$ lies in $U^{(p-1)}$: $a^{p-1} = 1 + \lambda^{p-1} c$. -/
theorem intCast_pow_mem_U (hp2 : p ≠ 2) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    ∃ c : 𝒪[(Klam hζ)], ((algebraMap K (Klam hζ) (a : K)) ^ (p - 1) : (Klam hζ)) = 1 + ((lamInt hζ : 𝒪[(Klam hζ)]) : (Klam hζ)) ^ (p - 1) * c := by
  obtain ⟨ε, hε, hpe⟩ := lamPlace_p_eq hζ hp2
  have hF : (p : ℤ) ∣ a ^ (p - 1) - 1 := by
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    have := Int.ModEq.pow_card_sub_one_eq_one hp.out (n := a)
      ((hpZ.irreducible.coprime_iff_not_dvd.mpr ha).symm)
    exact (Int.ModEq.dvd this.symm)
  obtain ⟨d, hd⟩ := hF
  refine ⟨ε * (d : 𝒪[(Klam hζ)]), ?_⟩
  have h1 : ((a : K) : K) ^ (p - 1) = 1 + (p : K) * (d : K) := by
    have : (a ^ (p - 1) : ℤ) = 1 + p * d := by rw [← hd]; ring
    exact_mod_cast this
  rw [← map_pow, h1, map_add, map_one, map_mul]
  congr 1
  have hp' : algebraMap K (Klam hζ) (p : K) = ((ε * lamInt hζ ^ (p - 1) : 𝒪[(Klam hζ)]) : (Klam hζ)) := by
    rw [← hpe]; simp
  rw [hp', map_intCast]
  push_cast
  ring

/-- **The local symbol $(a, c\,w)_\lambda = 1$** for rational integers $a, c$ prime to $p$ and $w \equiv 1
\pmod{\lambda^2}$ in $K_\lambda$ (from Proposition 5.12 (b)). -/
theorem hilbertPairing_intCast_primary (hp2 : p ≠ 2) {ζl : (Klam hζ)ˣ} (hζl : IsPrimitiveRoot ζl p)
    {φ : ∀ M : LocalCFT.FiniteAbelianExt (Klam hζ) Ω, (Klam hζ)ˣ →* Gal(M.toField/(Klam hζ))}
    (hφ : LocalCFT.IsLocalArtinMap φ) (a c : (Klam hζ)ˣ) (w : (Klam hζ)ˣ)
    (ha : ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ (a : (Klam hζ)) = algebraMap K (Klam hζ) (n : K))
    (hc : ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ (c : (Klam hζ)) = algebraMap K (Klam hζ) (n : K))
    (hw : ∃ d : 𝒪[(Klam hζ)], (w : (Klam hζ)) = 1 + ((lamInt hζ : 𝒪[(Klam hζ)]) : (Klam hζ)) ^ 2 * d) :
    hilbertPairing hζl hφ a (c * w) = 1 := by
  obtain ⟨ε, hε, hpe⟩ := lamPlace_p_eq hζ hp2
  obtain ⟨-, hb, -, -⟩ := prop_5_12 (Ω := Ω) hp2 hζl hφ (lamPlace_irreducible hζ) hε hpe
    (lamPlace_card_residue hζ)
  have hS := hilbertPairing_isSteinberg hζl hφ
  have hU : ∀ x : (Klam hζ)ˣ, (∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ (x : (Klam hζ)) = algebraMap K (Klam hζ) (n : K)) →
      ∃ c : 𝒪[(Klam hζ)], ((x ^ (p - 1) : (Klam hζ)ˣ) : (Klam hζ)) = 1 + ((lamInt hζ : 𝒪[(Klam hζ)]) : (Klam hζ)) ^ (p - 1) * c := by
    rintro x ⟨n, hn, hx⟩
    obtain ⟨c, hc⟩ := intCast_pow_mem_U hζ hp2 hn
    exact ⟨c, by rw [Units.val_pow_eq_pow_val, hx, hc]⟩
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  -- `(a, c)^((p-1)^2) = 1`
  have hac : hilbertPairing hζl hφ (a ^ (p - 1)) (c ^ (p - 1)) = 1 :=
    hb (p - 1) (p - 1) (by omega) (by omega) (by omega) _ _ (hU a ha) (hU c hc)
  -- `(a, w)^(p-1) = 1`
  have haw : hilbertPairing hζl hφ (a ^ (p - 1)) w = 1 :=
    hb (p - 1) 2 (by omega) (by omega) (by omega) _ _ (hU a ha) hw
  simp only [map_pow, MonoidHom.pow_apply, ← pow_mul] at hac haw
  have hcop : Nat.Coprime (p - 1) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have key : ∀ z : (Klam hζ)ˣ, z ^ p = 1 → z ^ (p - 1) = 1 → z = 1 := by
    intro z h1 h2
    have : z ^ Nat.gcd (p - 1) p = 1 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
    rwa [hcop, pow_one] at this
  have hw1 : hilbertPairing hζl hφ a w = 1 := key _ (hS.pow_eq_one _ _) haw
  have hc1 : hilbertPairing hζl hφ a c = 1 := by
    have h1 : hilbertPairing hζl hφ a c ^ (p - 1) = 1 := by
      refine key _ ?_ (by rw [← pow_mul]; exact hac)
      rw [← pow_mul, mul_comm, pow_mul, hS.pow_eq_one, one_pow]
    exact key _ (hS.pow_eq_one _ _) h1
  rw [map_mul, hc1, hw1, one_mul]

end NumberFieldKB.MilneCFT.Ch8.Eisenstein
