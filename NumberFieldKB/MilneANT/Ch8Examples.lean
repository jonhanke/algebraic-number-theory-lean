import NumberFieldKB.MilneANT.Ch8Chebotarev

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: Frobenius in cyclotomic and quadratic fields

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

* **Example 8.18** (`example_8_18`, proved): in $\mathbb Q(\zeta_n)$, for $p \nmid n$, the Frobenius at $p$ is
  $\zeta_n \mapsto \zeta_n^p$, it is the unique such element, and its order is the order of $p$ in
  $(\mathbb Z/n)^\times$.
* **Example 8.19** (`example_8_19`, proved): in $\mathbb Q(\sqrt d)$, for an odd prime $p \nmid d$, the Frobenius at
  $p$ acts on $\sqrt d$ by the Legendre symbol $\left(\frac dp\right)$; it is trivial iff $p$ splits iff $d$ is a square
  modulo $p$.
* The quadratic reciprocity law derived from them (pp. 143–144) is Mathlib's `legendreSym.quadratic_reciprocity`,
  `ZMod.exists_sq_eq_neg_one_iff` and `ZMod.exists_sq_eq_two_iff` (tagged).
-/

open NumberField IsDedekindDomain
open NumberFieldKB.Chebotarev

namespace NumberFieldKB.MilneANT

noncomputable section

/-- Helper: every arithmetic Frobenius element at a prime above $\mathfrak p$ with $N\mathfrak p$ prime to $m$ sends
a primitive $m$-th root of unity $\zeta$ to $\zeta^{N\mathfrak p}$. -/
theorem arithFrob_zeta {F M : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} F M] [IsGalois F M]
    {v : HeightOneSpectrum (𝓞 F)} (hv : (Ideal.absNorm v.asIdeal).Coprime m)
    (Q : v.asIdeal.primesOver (𝓞 M)) {σ : Gal(M/F)} (hσ : IsArithFrobAt (𝓞 F) σ Q.1) :
    σ (IsCyclotomicExtension.zeta m F M) =
      IsCyclotomicExtension.zeta m F M ^ Ideal.absNorm v.asIdeal := by
  have hζ := IsCyclotomicExtension.zeta_spec m F M
  set ζ := IsCyclotomicExtension.zeta m F M
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let z : 𝓞 M := ⟨ζ, (hζ.isIntegral hm).tower_top⟩
  have hz : z ^ m = 1 := by
    apply RingOfIntegers.ext
    show algebraMap (𝓞 M) M (z ^ m) = algebraMap (𝓞 M) M 1
    rw [map_pow, map_one]
    exact hζ.pow_eq_one
  have := Q.2.2
  have := Q.2.1
  have hQ : ((m : ℕ) : 𝓞 M) ∉ Q.1 := by
    intro h
    have h' : (m : 𝓞 F) ∈ Q.1.under (𝓞 F) := by
      rw [Ideal.mem_comap, map_natCast]; exact h
    rw [← Ideal.over_def Q.1 v.asIdeal] at h'
    exact natCast_notMem_of_coprime hv h'
  have hfr := hσ.apply_of_pow_eq_one hz hQ
  have hcard : Nat.card (𝓞 F ⧸ Q.1.under (𝓞 F)) = Ideal.absNorm v.asIdeal := by
    rw [← Ideal.over_def Q.1 v.asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard] at hfr
  have e1 : ((MulSemiringAction.toAlgHom (𝓞 F) (𝓞 M) σ z : 𝓞 M) : M) = σ ζ := rfl
  have e2 : ((z ^ Ideal.absNorm v.asIdeal : 𝓞 M) : M) = ζ ^ Ideal.absNorm v.asIdeal := by
    show algebraMap (𝓞 M) M (z ^ _) = _
    rw [map_pow]; rfl
  rw [← e1, hfr, e2]

/-- Helper: powers of a primitive root of unity depend only on the exponent modulo $m$. -/
theorem zeta_pow_eq_of_natCast_eq {M : Type} [Field M] {m : ℕ} [NeZero m] {ζ : M}
    (hζ : IsPrimitiveRoot ζ m) {a b : ℕ} (h : (a : ZMod m) = b) : ζ ^ a = ζ ^ b := by
  have e : ∀ c : ℕ, ζ ^ c = ζ ^ (c % m) := fun c => by
    conv_lhs => rw [← Nat.mod_add_div c m, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  rw [e a, e b, ← ZMod.val_natCast (n := m) (a := a), ← ZMod.val_natCast (n := m) (a := b), h]

/-- Helper: an integer lies in a prime of `𝓞 K` above the prime `v` of `𝓞 ℚ` iff it is divisible by `ratPrime v`. -/
theorem intCast_mem_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ))
    (Q : Ideal (𝓞 K)) [Q.LiesOver v.asIdeal] (m : ℤ) :
    (m : 𝓞 K) ∈ Q ↔ (ratPrime v : ℤ) ∣ m := by
  have h1 : (m : 𝓞 K) ∈ Q ↔ (m : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [Ideal.over_def Q v.asIdeal, Ideal.mem_comap, map_intCast]
  rw [h1, ← Ideal.mem_span_singleton, Rat.HeightOneSpectrum.span_natGenerator]
  set e : 𝓞 ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  constructor
  · intro h
    have := Ideal.mem_map_of_mem e h
    rwa [map_intCast] at this
  · intro h
    obtain ⟨x, hx, hxm⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).1 h
    have : x = (m : 𝓞 ℚ) := e.injective (by rw [hxm, map_intCast, Int.cast_id])
    rwa [this] at hx

/-- Helper: in a quadratic Galois extension of `ℚ`, a nontrivial automorphism sends `s` with `s ^ 2 = d`,
`s ∉ ℚ`, to `-s`. -/
theorem quad_aut_neg {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (hK : Module.finrank ℚ K = 2)
    (d : ℤ) (s : K) (hs : s ^ 2 = d) (hsQ : s ∉ Set.range (algebraMap ℚ K)) (g : Gal(K/ℚ)) (hg : g ≠ 1) :
    g s = -s := by
  have hcard : Nat.card Gal(K/ℚ) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK]
  obtain ⟨τ, hτ, huniq⟩ := (Nat.card_eq_two_iff' (1 : Gal(K/ℚ))).1 hcard
  have hall : ∀ g : Gal(K/ℚ), g = 1 ∨ g = τ := fun g => by
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr (huniq g hg)
  have hgs : (g s - s) * (g s + s) = 0 := by
    have : (g s) ^ 2 = d := by rw [← map_pow, hs, map_intCast]
    linear_combination this - hs
  rcases mul_eq_zero.1 hgs with h | h
  · exfalso
    apply hsQ
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    have hgτ : g = τ := (hall g).resolve_left hg
    rcases hall f with rfl | rfl
    · rfl
    · rw [← hgτ]; exact sub_eq_zero.1 h
  · exact eq_neg_of_add_eq_zero_left h

/-- Helper: a root `s` of `X ^ 2 - d` is an algebraic integer. -/
theorem isIntegral_of_sq_eq {K : Type} [Field K] (d : ℤ) (s : K) (hs : s ^ 2 = d) : IsIntegral ℤ s :=
  ⟨Polynomial.X ^ 2 - Polynomial.C d, Polynomial.monic_X_pow_sub_C d two_ne_zero, by
    rw [← Polynomial.aeval_def]
    simp [hs]⟩

/-- Helper: for an odd prime `p ∤ d`, `2 √d` lies in no prime of `𝓞 K` above `p`. -/
theorem two_mul_notMem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ))
    (Q : Ideal (𝓞 K)) [Q.LiesOver v.asIdeal] (hp2 : ratPrime v ≠ 2) (d : ℤ)
    (hpd : ¬ (ratPrime v : ℤ) ∣ d) (S : 𝓞 K) (hS : S ^ 2 = (d : 𝓞 K)) : (2 : 𝓞 K) * S ∉ Q := by
  intro h
  have hp : Prime (ratPrime v : ℤ) := Nat.prime_iff_prime_int.1 (Rat.HeightOneSpectrum.prime_natGenerator v)
  have h4 : ((4 * d : ℤ) : 𝓞 K) ∈ Q := by
    have := Q.pow_mem_of_mem h 2 (by norm_num)
    convert this using 1
    push_cast
    rw [mul_pow, hS]
    norm_num
  rcases hp.dvd_or_dvd ((intCast_mem_iff v Q _).1 h4) with h1 | h1
  · apply hp2
    have h2 : (ratPrime v : ℤ) ∣ ((2 : ℕ) : ℤ) ^ 2 := by simpa using h1
    have := hp.dvd_of_dvd_pow h2
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) Nat.prime_two).1
      (Int.natCast_dvd_natCast.1 this)
  · exact hpd h1

/-- Helper: an odd prime `p ∤ d` is unramified in a quadratic field containing `√d`. -/
theorem isUnramifiedAt_quadratic {K : Type} [Field K] [NumberField K] [IsGalois ℚ K]
    (hK : Module.finrank ℚ K = 2) (d : ℤ) (s : K) (hs : s ^ 2 = d) (hsQ : s ∉ Set.range (algebraMap ℚ K))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hp2 : ratPrime v ≠ 2) (hpd : ¬ (ratPrime v : ℤ) ∣ d)
    (Q : Ideal (𝓞 K)) [hQp : Q.IsPrime] [hQo : Q.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 ℚ) Q := by
  have hQm : Q.IsMaximal := hQp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have := finite_quotient_of_ne_bot Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  refine Ideal.ramificationIdx_eq_one_iff.mp ?_
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q Gal(K/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(K/ℚ)) v.asIdeal Q, Subgroup.card_eq_one,
    Subgroup.eq_bot_iff_forall]
  intro τ hτ
  by_contra hne
  have hτs := quad_aut_neg hK d s hs hsQ τ hne
  let S : 𝓞 K := ⟨s, isIntegral_of_sq_eq d s hs⟩
  have hS : S ^ 2 = (d : 𝓞 K) := RingOfIntegers.ext (by push_cast; exact hs)
  have h1 := (Ideal.mem_inertia.1 hτ) S
  apply two_mul_notMem v Q hp2 d hpd S hS
  have e : τ • S - S = -((2 : 𝓞 K) * S) := RingOfIntegers.ext (by
    show τ s - s = -(2 * s)
    rw [hτs]; ring)
  rw [e] at h1
  simpa using Q.neg_mem h1

/-- Helper: every arithmetic Frobenius element at a prime above an odd prime `p ∤ d` acts on `√d` by the
Legendre symbol. -/
theorem arithFrob_sqrt {K : Type} [Field K] [NumberField K] [IsGalois ℚ K]
    (hK : Module.finrank ℚ K = 2) (d : ℤ) (s : K) (hs : s ^ 2 = d) (hsQ : s ∉ Set.range (algebraMap ℚ K))
    (v : HeightOneSpectrum (𝓞 ℚ)) [Fact (ratPrime v).Prime] (hp2 : ratPrime v ≠ 2)
    (hpd : ¬ (ratPrime v : ℤ) ∣ d) (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (σ : Gal(K/ℚ)) (hσ : IsArithFrobAt (𝓞 ℚ) σ Q) :
    σ s = (legendreSym (ratPrime v) d : K) * s := by
  let S : 𝓞 K := ⟨s, isIntegral_of_sq_eq d s hs⟩
  have hS : S ^ 2 = (d : 𝓞 K) := RingOfIntegers.ext (by push_cast; exact hs)
  have hN : Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) = ratPrime v := by
    have hN0 : Ideal.absNorm v.asIdeal = ratPrime v := RatIdele.absNorm_asIdeal v
    rw [← hN0, ← Ideal.over_def Q v.asIdeal, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
  have h1 : σ • S - S ^ ratPrime v ∈ Q := by
    have := hσ S
    rwa [hN] at this
  have hodd : Odd (ratPrime v) := (Fact.out : (ratPrime v).Prime).odd_of_ne_two hp2
  have hSp : S ^ ratPrime v = (d : 𝓞 K) ^ (ratPrime v / 2) * S := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, show (2 * k + 1) / 2 = k by omega, pow_succ, pow_mul, hS]
  have hd0 : (d : ZMod (ratPrime v)) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hε := legendreSym.eq_one_or_neg_one (ratPrime v) hd0
  have hEuler : ((d ^ (ratPrime v / 2) - legendreSym (ratPrime v) d : ℤ) : 𝓞 K) ∈ Q := by
    refine (intCast_mem_iff v Q _).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ (ratPrime v)).1 ?_)
    push_cast
    rw [legendreSym.eq_pow, sub_self]
  have key : ∀ η : ℤ, (η = 1 ∨ η = -1) → σ s = η * s → η = legendreSym (ratPrime v) d := by
    intro η hη hση
    by_contra hne
    have hσS : σ • S = (η : 𝓞 K) * S := RingOfIntegers.ext (by
      show σ s = (η : K) * s
      exact hση)
    have hX : ((η - legendreSym (ratPrime v) d : ℤ) : 𝓞 K) * S ∈ Q := by
      have e : ((η - legendreSym (ratPrime v) d : ℤ) : 𝓞 K) * S =
          (σ • S - S ^ ratPrime v) +
            ((d ^ (ratPrime v / 2) - legendreSym (ratPrime v) d : ℤ) : 𝓞 K) * S := by
        rw [hσS, hSp]; push_cast; ring
      rw [e]
      exact Q.add_mem h1 (Q.mul_mem_right _ hEuler)
    apply two_mul_notMem v Q hp2 d hpd S hS
    rcases hη with rfl | rfl <;> rcases hε with h | h <;> rw [h] at hne hX
    · exact absurd rfl hne
    · have : (2 : 𝓞 K) * S = ((1 - -1 : ℤ) : 𝓞 K) * S := by push_cast; ring
      rw [this]; exact hX
    · have : (2 : 𝓞 K) * S = -(((-1 - 1 : ℤ) : 𝓞 K) * S) := by push_cast; ring
      rw [this]; exact Q.neg_mem hX
    · exact absurd rfl hne
  by_cases hσ1 : σ = 1
  · have := key 1 (Or.inl rfl) (by rw [hσ1]; simp)
    rw [← this, hσ1]; simp
  · have := key (-1) (Or.inr rfl) (by rw [quad_aut_neg hK d s hs hsQ σ hσ1]; simp)
    rw [← this, quad_aut_neg hK d s hs hsQ σ hσ1]; simp

/-- Helper: equal powers of a primitive root of unity have exponents equal modulo $m$. -/
theorem natCast_eq_of_zeta_pow_eq {M : Type} [Field M] {m : ℕ} [NeZero m] {ζ : M}
    (hζ : IsPrimitiveRoot ζ m) {a b : ℕ} (h : ζ ^ a = ζ ^ b) : (a : ZMod m) = b := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have e : ∀ c : ℕ, ζ ^ c = ζ ^ (c % m) := fun c => by
    conv_lhs => rw [← Nat.mod_add_div c m, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  rw [e a, e b] at h
  have := hζ.pow_inj (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) h
  rw [← ZMod.natCast_mod a m, ← ZMod.natCast_mod b m, this]

/-- **Example 8.18** (proved): let $K = \mathbb Q(\zeta_n)$ and $p \nmid n$ a prime (here a prime `v` of
`𝓞 ℚ` with $p$ = `ratPrime v`), and $Q$ a prime of $K$ above $p$. The Frobenius $\sigma = (Q, K/\mathbb Q)$ satisfies
$\sigma(\zeta_n) = \zeta_n^p$; it is the unique element with $\sigma\alpha \equiv \alpha^p \bmod Q$ for all integers
$\alpha$; and its order is the order of $p$ in $(\mathbb Z/n)^\times$. -/
@[kb "milne2020ant" "v3.08, Ex. 8.18, p. 143"]
theorem example_8_18 (n : ℕ) [NeZero n] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [IsGalois ℚ K] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ ratPrime v ∣ n) (Q : v.asIdeal.primesOver (𝓞 K)) :
    frobAt ℚ K v Q (IsCyclotomicExtension.zeta n ℚ K) = IsCyclotomicExtension.zeta n ℚ K ^ ratPrime v ∧
      (∀ σ : Gal(K/ℚ), IsArithFrobAt (𝓞 ℚ) σ Q.1 → σ = frobAt ℚ K v Q) ∧
      orderOf (frobAt ℚ K v Q) = orderOf (ratPrime v : ZMod n) := by
  classical
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  set ζ := IsCyclotomicExtension.zeta n ℚ K
  have : Fact (ratPrime v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hN : Ideal.absNorm v.asIdeal = ratPrime v := RatIdele.absNorm_asIdeal v
  have hcop : (Ideal.absNorm v.asIdeal).Coprime n := by
    rw [hN]; exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hv
  have hfrob : frobAt ℚ K v Q ζ = ζ ^ ratPrime v := by
    have := arithFrob_zeta n hcop Q (isArithFrobAt_frobAt ℚ K v Q)
    rwa [hN] at this
  have hunits : ∀ σ : Gal(K/ℚ), σ ζ = ζ ^ ratPrime v →
      ((hζ.autToPow ℚ σ : (ZMod n)ˣ) : ZMod n) = (ratPrime v : ZMod n) := by
    intro σ h
    have s1 := hζ.autToPow_spec ℚ σ
    rw [h] at s1
    have := natCast_eq_of_zeta_pow_eq hζ s1
    rwa [ZMod.natCast_zmod_val] at this
  refine ⟨hfrob, ?_, ?_⟩
  · intro σ hσ
    have h1 := arithFrob_zeta n hcop Q hσ
    rw [hN] at h1
    exact (hζ.autToPow_injective ℚ) (Units.ext ((hunits σ h1).trans (hunits _ hfrob).symm))
  · rw [← orderOf_injective _ (hζ.autToPow_injective ℚ), ← orderOf_units, hunits _ hfrob]

/-- **Example 8.19** (proved): let $K = \mathbb Q(\sqrt d)$ be a quadratic field ($s \in K$ with $s^2 = d$, $d$ not a
square), $p$ an odd prime not dividing $d$ (so unramified in $K$), and $Q$ a prime of $K$ above $p$. The Frobenius
$\sigma = (Q, K/\mathbb Q)$ satisfies $\sigma(\sqrt d) = \left(\frac dp\right)\sqrt d$; so, identifying
$\mathrm{Gal}(K/\mathbb Q)$ with $\{\pm1\}$, $(p, K/\mathbb Q) = \left(\frac dp\right)$, and it is $+1$ iff $p$ splits
in $K$ iff $d$ is a square modulo $p$.

*Restriction.* Milne allows any unramified $p$, including $p = 2$ when $d \equiv 1 \bmod 4$; the Legendre symbol
$\left(\frac d2\right)$ is not defined, so $p$ is odd here. -/
@[kb "milne2020ant" "v3.08, Ex. 8.19, p. 143"]
theorem example_8_19 (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (hK : Module.finrank ℚ K = 2)
    (d : ℤ) (s : K) (hs : s ^ 2 = d) (hsQ : s ∉ Set.range (algebraMap ℚ K)) (v : HeightOneSpectrum (𝓞 ℚ)) (hp2 : ratPrime v ≠ 2)
    (hpd : ¬ (ratPrime v : ℤ) ∣ d) (Q : v.asIdeal.primesOver (𝓞 K)) :
    haveI : Fact (ratPrime v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    frobAt ℚ K v Q s = (legendreSym (ratPrime v) d : K) * s ∧
      (frobAt ℚ K v Q = 1 ↔ v ∈ splitPrimes ℚ K) ∧
      (v ∈ splitPrimes ℚ K ↔ IsSquare (d : ZMod (ratPrime v))) := by
  classical
  have hfact : Fact (ratPrime v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hunr : v ∈ unramifiedPrimes ℚ K := fun Q' hQ' hQo' =>
    isUnramifiedAt_quadratic hK d s hs hsQ v hp2 hpd Q'
  have := Q.2.1
  have := Q.2.2
  have h1 : frobAt ℚ K v Q s = (legendreSym (ratPrime v) d : K) * s :=
    arithFrob_sqrt hK d s hs hsQ v hp2 hpd Q.1 _ (isArithFrobAt_frobAt ℚ K v Q)
  have hd0 : (d : ZMod (ratPrime v)) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hε := legendreSym.eq_one_or_neg_one (ratPrime v) hd0
  have hs0 : s ≠ 0 := fun h => hsQ ⟨0, by rw [h]; simp⟩
  have hfe : frobAt ℚ K v Q = 1 ↔ legendreSym (ratPrime v) d = 1 := by
    constructor
    · intro h
      rw [h] at h1
      rcases hε with h2 | h2
      · exact h2
      · exfalso
        rw [h2] at h1
        apply hs0
        have h3 : (2 : K) * s = 0 := by simp at h1; linear_combination h1
        exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
    · intro h
      by_contra hne
      have h2 := quad_aut_neg hK d s hs hsQ _ hne
      rw [h2, h] at h1
      apply hs0
      have h3 : (2 : K) * s = 0 := by simp at h1; linear_combination -h1
      exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
  have hsplit : v ∈ splitPrimes ℚ K ↔ frobAt ℚ K v Q = 1 := by
    rw [splitPrimes_eq_frobSet_one]
    change (v ∈ unramifiedPrimes ℚ K ∧ frobClass ℚ K v = ConjClasses.mk 1) ↔ _
    rw [frobClass_eq_mk_frobAt ℚ K v Q, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left]
    exact ⟨fun h => h.2, fun h => ⟨hunr, h⟩⟩
  refine ⟨h1, hsplit.symm, ?_⟩
  rw [hsplit, hfe]
  exact legendreSym.eq_one_iff (ratPrime v) hd0

-- Quadratic reciprocity (Milne pp. 143–144, derived from Examples 8.18 and 8.19): Mathlib.
attribute [kb "milne2020ant" "v3.08, Ch. 8, the quadratic reciprocity law, p. 143"]
  legendreSym.quadratic_reciprocity ZMod.exists_sq_eq_neg_one_iff ZMod.exists_sq_eq_two_iff

end

end NumberFieldKB.MilneANT
