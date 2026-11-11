import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Kummer descent along $K(\mu_N)/K$ up to roots of unity

For an abelian Galois extension $L/K$ containing a primitive $N$-th root of unity $\zeta$, $N = nw$, such that every
$e \mid N$ with $\zeta^{N/e} \in K$ divides $w$ (for $L = K(\mu_N)$ and $w = \#\mu(K)$ this holds), an element
$a \in K^\times$ that is an $N$-th power in $L$ is, in $K$, an $n$-th power up to a $w$-th root of unity.

Proof: $c_\sigma = \sigma\beta/\beta \in \mu_N$ is a cocycle; for $G$ abelian $c_\tau^{\chi(\sigma)-1} = \tau(c_\sigma)/c_\sigma$,
so $c^g$ is a coboundary in $\mu_N$ for $g = \gcd(N, \chi(\sigma) - 1)$, and $g \mid w$; then $\beta^w/\eta$ is fixed by
$G$ for a suitable $\eta \in \mu_N$. (Step 3 of the proof of Chevalley's theorem.)
-/

namespace NumberFieldKB.MilneCFT.Ch8

/-- **Kummer descent up to roots of unity.** -/
theorem exists_eq_mul_pow_of_pow_eq {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (hab : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) {n w : ℕ} (hn : 0 < n) (hw : 0 < w)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (n * w))
    (hfix : ∀ e : ℕ, e ∣ n * w → (∀ σ : L ≃ₐ[K] L, σ (ζ ^ (n * w / e)) = ζ ^ (n * w / e)) → e ∣ w)
    {a : K} (ha : a ≠ 0) {β : L} (hβ : β ^ (n * w) = algebraMap K L a) :
    ∃ b ξ : K, ξ ^ w = 1 ∧ a = ξ * b ^ n := by
  classical
  have hN : 0 < n * w := Nat.mul_pos hn hw
  have : NeZero (n * w) := ⟨hN.ne'⟩
  set N := n * w with hNdef
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  -- Step 1
  have hk : ∀ σ : L ≃ₐ[K] L, ∃ k : ℕ, ∀ ξ : L, ξ ^ N = 1 → σ ξ = ξ ^ k := by
    intro σ
    have hσ : IsPrimitiveRoot (σ ζ) N := hζ.map_of_injective σ.injective
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hσ.pow_eq_one
    refine ⟨i, fun ξ hξ => ?_⟩
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hξ
    rw [← hj, map_pow, ← hi, ← pow_mul, ← pow_mul, mul_comm]
  choose k hk using hk
  -- Step 2
  have hA0 : algebraMap K L a ≠ 0 := by simpa using ha
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hA0 hβ.symm
  set c : (L ≃ₐ[K] L) → L := fun σ => σ β / β with hc
  have hcmul : ∀ σ, σ β = c σ * β := fun σ => by simp [hc, hβ0]
  have hcN : ∀ σ, c σ ^ N = 1 := by
    intro σ
    simp only [hc]
    rw [div_pow, ← map_pow, hβ, AlgEquiv.commutes, div_self hA0]
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ h
    have := hcN σ
    rw [h, zero_pow hN.ne'] at this
    exact zero_ne_one this
  have hroot0 : ∀ η : L, η ^ N = 1 → η ≠ 0 := by
    intro η h h0
    rw [h0, zero_pow hN.ne'] at h
    exact zero_ne_one h
  have hcoc : ∀ σ τ : L ≃ₐ[K] L, σ (c τ) * c σ = τ (c σ) * c τ := by
    intro σ τ
    have h1 : (σ * τ) β = (τ * σ) β := by rw [hab σ τ]
    simp only [AlgEquiv.mul_apply] at h1
    simp only [map_mul, hcmul σ, hcmul τ] at h1
    have := mul_right_cancel₀ hβ0 (by linear_combination h1 :
      σ (c τ) * (c σ) * β = τ (c σ) * c τ * β)
    exact this
  have hcpow : ∀ σ τ : L ≃ₐ[K] L, c τ ^ ((k σ : ℤ) - 1) = τ (c σ) / c σ := by
    intro σ τ
    have h := hcoc σ τ
    rw [hk σ (c τ) (hcN τ)] at h
    have e1 : c τ ^ ((k σ : ℤ) - 1) = c τ ^ (k σ) / c τ := by
      rw [zpow_sub₀ (hc0 τ), zpow_natCast, zpow_one]
    rw [e1, div_eq_div_iff (hc0 τ) (hc0 σ)]
    linear_combination h
  -- the ideal
  let P : ℤ → Prop := fun m => ∃ η : L, η ^ N = 1 ∧ ∀ τ : L ≃ₐ[K] L, c τ ^ m = τ η / η
  let I : Ideal ℤ :=
    { carrier := {m | P m}
      add_mem' := by
        rintro m1 m2 ⟨η1, h1, e1⟩ ⟨η2, h2, e2⟩
        refine ⟨η1 * η2, by rw [mul_pow, h1, h2, one_mul], fun τ => ?_⟩
        rw [zpow_add₀ (hc0 τ), e1, e2, map_mul, div_mul_div_comm]
      zero_mem' := ⟨1, one_pow _, fun τ => by simp⟩
      smul_mem' := by
        rintro z m ⟨η, h, e⟩
        refine ⟨η ^ z, ?_, fun τ => ?_⟩
        · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]
        · rw [smul_eq_mul, mul_comm, zpow_mul, e, div_zpow, map_zpow₀] }
  have hmemI : ∀ m, m ∈ I ↔ P m := fun m => Iff.rfl
  have hNI : (N : ℤ) ∈ I := ⟨1, one_pow _, fun τ => by simp [zpow_natCast, hcN]⟩
  have hkI : ∀ σ, ((k σ : ℤ) - 1) ∈ I := fun σ => ⟨c σ, hcN σ, fun τ => hcpow σ τ⟩
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmem : ∀ m : ℤ, m ∈ I ↔ g ∣ m := fun m => by
    rw [hg, Ideal.submodule_span_eq, Ideal.mem_span_singleton]
  set d : ℕ := g.natAbs with hd
  have hdg : (d : ℤ) ∣ g := Int.natAbs_dvd.2 dvd_rfl
  have hgd : g ∣ (d : ℤ) := Int.dvd_natAbs.2 dvd_rfl
  have hdN : d ∣ N := by
    have := hdg.trans ((hmem _).1 hNI)
    exact_mod_cast this
  have hdI : (d : ℤ) ∈ I := (hmem _).2 hgd
  have hdw : d ∣ w := by
    apply hfix d hdN
    intro σ
    set ξ := ζ ^ (N / d) with hξ
    have hξN : ξ ^ N = 1 := by
      rw [hξ, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hξd : ξ ^ d = 1 := by
      rw [hξ, ← pow_mul, Nat.div_mul_cancel hdN, hζ.pow_eq_one]
    obtain ⟨t, ht⟩ := hdg.trans ((hmem _).1 (hkI σ))
    rw [hk σ ξ hξN]
    have ξ0 : ξ ≠ 0 := hroot0 ξ hξN
    have : ξ ^ (k σ : ℤ) = ξ := by
      have e : (k σ : ℤ) = ((k σ : ℤ) - 1) + 1 := by ring
      rw [e, zpow_add_one₀ ξ0, ht, zpow_mul, zpow_natCast, hξd, one_zpow, one_mul]
    rwa [zpow_natCast] at this
  obtain ⟨η, hη, hcη⟩ := (hmemI _).1 hdI
  obtain ⟨e, he⟩ := hdw
  have hη0 := hroot0 η hη
  set η' := η ^ e with hη'
  have hη'N : η' ^ N = 1 := by
    rw [hη', ← pow_mul, mul_comm, pow_mul, hη, one_pow]
  have hη'0 := hroot0 η' hη'N
  have hcw : ∀ τ : L ≃ₐ[K] L, c τ ^ w = τ η' / η' := by
    intro τ
    have h := hcη τ
    rw [zpow_natCast] at h
    rw [he, pow_mul, h, div_pow, hη', map_pow]
  set γ := β ^ w / η' with hγ
  have hγfix : ∀ τ : L ≃ₐ[K] L, τ γ = γ := by
    intro τ
    have hτ : τ η' ≠ 0 := by simpa using hη'0
    have h1 : τ (β ^ w) = c τ ^ w * β ^ w := by
      rw [map_pow, hcmul τ, mul_pow]
    rw [hγ, map_div₀, h1, hcw τ]
    field_simp
  have hγmem : γ ∈ (⊥ : IntermediateField K L) := (IsGalois.mem_bot_iff_fixed γ).2 hγfix
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.1 hγmem
  have hb0 : b ≠ 0 := by
    rintro rfl
    have : γ = 0 := by rw [← hb]; simp
    rw [hγ, div_eq_zero_iff] at this
    rcases this with h | h
    · exact hβ0 (pow_eq_zero_iff hw.ne' |>.1 h)
    · exact hη'0 h
  have hbn : (b ^ n) ≠ 0 := pow_ne_zero _ hb0
  have hβw : β ^ w = algebraMap K L b * η' := by
    rw [hb, hγ]; field_simp
  have hAn : algebraMap K L a = algebraMap K L (b ^ n) * η' ^ n := by
    rw [← hβ, hNdef, mul_comm n w, pow_mul, hβw, mul_pow, map_pow]
  refine ⟨b, a / b ^ n, ?_, ?_⟩
  · apply (algebraMap K L).injective
    have hx : algebraMap K L (a / b ^ n) = η' ^ n := by
      rw [map_div₀, hAn]
      have : algebraMap K L (b ^ n) ≠ 0 := by simpa using hbn
      field_simp
    rw [map_pow, hx, map_one, ← pow_mul]
    exact hη'N
  · field_simp

end NumberFieldKB.MilneCFT.Ch8
