import NumberFieldKB.WeilBNT.LocalQuotients

/-!
# Weil, *Basic Number Theory*, Chapter V, §3: products of ideals locally, numerator and denominator

$k$ is a number field, $\mathfrak r$ its ring of integers (Weil's maximal order), and the fractional ideals of $k$ are
Mathlib's nonzero `FractionalIdeal (𝓞 k)⁰ k`.

* **Text p. 86**: $(\mathfrak a\mathfrak b)_v=\mathfrak a_v\mathfrak b_v$ for the local components at a finite place $v$;
  here for ideals of $\mathfrak r$, with $\mathfrak a_v=\mathfrak a\,r_v$ (`localIdeal`): `weil_V_3_text86`.
* **Cor. 2 of Thm. 3** (p. 87): every fractional ideal $\mathfrak n$ can be written in one and only one way as
  $\mathfrak b\mathfrak c^{-1}$ with $\mathfrak b,\mathfrak c$ mutually prime ideals of $\mathfrak r$
  ($\mathfrak b+\mathfrak c=\mathfrak r$), the numerator and the denominator of $\mathfrak n$: `weil_V_3_numDen`.
  "$\mathfrak n=\mathfrak b\mathfrak c^{-1}$" is stated as $\mathfrak n\mathfrak c=\mathfrak b$ with $\mathfrak c\ne0$.

Weil reads Cor. 2 off the exponents ($b(v)=\max(a(v),0)$, $c(v)=\max(-a(v),0)$). The proof here is the same computation
without exponents: $\mathfrak c=(\mathfrak r+\mathfrak n)^{-1}$ (exponents $-\min(0,a(v))$) and $\mathfrak b=\mathfrak n\mathfrak c$;
then $\mathfrak b+\mathfrak c=(\mathfrak n+\mathfrak r)(\mathfrak r+\mathfrak n)^{-1}=\mathfrak r$, and conversely
$\mathfrak b+\mathfrak c=\mathfrak r$ and $\mathfrak n\mathfrak c=\mathfrak b$ force $\mathfrak r+\mathfrak n=\mathfrak c^{-1}$.
-/

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

/-- **Weil, V.§3, text p. 86**: $(\mathfrak a\mathfrak b)_v=\mathfrak a_v\mathfrak b_v$ at every finite place $v$. -/
@[kb "weil1973bnt" "Ch. V, §3, text p. 86 ((ab)_v = a_v b_v), for ideals of the maximal order"]
theorem weil_V_3_text86 (𝔞 𝔟 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) :
    localIdeal K (𝔞 * 𝔟) v = localIdeal K 𝔞 v * localIdeal K 𝔟 v :=
  Ideal.map_mul _ _ _

/-- **Weil, V.§3, Cor. 2 of Thm. 3** (p. 87): a nonzero fractional ideal $\mathfrak n$ of $k$ is $\mathfrak b\mathfrak c^{-1}$
for one and only one pair of mutually prime ideals $\mathfrak b,\mathfrak c$ of $\mathfrak r$ (with $\mathfrak c\ne0$).
The hypothesis $\mathfrak n\ne0$ (Weil: $\{0\}$ is not a fractional ideal) is not needed: for $\mathfrak n=0$ the unique
pair is $(0,\mathfrak r)$. -/
@[kb "weil1973bnt" "Ch. V, §3, Cor. 2 of Thm. 3 (p. 87)"]
theorem weil_V_3_numDen (𝔫 : FractionalIdeal (𝓞 K)⁰ K) :
    ∃! p : Ideal (𝓞 K) × Ideal (𝓞 K), p.1 ⊔ p.2 = ⊤ ∧ p.2 ≠ ⊥ ∧
      𝔫 * (p.2 : FractionalIdeal (𝓞 K)⁰ K) = (p.1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have hJ0 : (1 + 𝔫 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro h
    have : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤ 0 := h ▸ le_add_right le_rfl
    exact one_ne_zero (le_antisymm this zero_le)
  have hJJ : (1 + 𝔫 : FractionalIdeal (𝓞 K)⁰ K) * (1 + 𝔫)⁻¹ = 1 := mul_inv_cancel₀ hJ0
  have key : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), (p.1 ⊔ p.2 = ⊤ ∧ p.2 ≠ ⊥ ∧
        𝔫 * (p.2 : FractionalIdeal (𝓞 K)⁰ K) = (p.1 : FractionalIdeal (𝓞 K)⁰ K)) →
        (p.2 : FractionalIdeal (𝓞 K)⁰ K) = (1 + 𝔫)⁻¹ := by
    rintro ⟨b, c⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    have : (1 + 𝔫 : FractionalIdeal (𝓞 K)⁰ K) * (c : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
      rw [add_mul, one_mul, h3, ←FractionalIdeal.coeIdeal_sup, sup_comm, h1,
        FractionalIdeal.coeIdeal_top]
    exact eq_inv_of_mul_eq_one_right this
  have h1 : (1 + 𝔫 : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ≤ 1 := by
    have := FractionalIdeal.inv_anti_mono (one_ne_zero) hJ0 (le_add_right le_rfl)
    simpa using this
  obtain ⟨c, hc⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp h1
  have h2 : 𝔫 * (1 + 𝔫)⁻¹ ≤ 1 := by
    calc 𝔫 * (1 + 𝔫)⁻¹ ≤ (1 + 𝔫) * (1 + 𝔫)⁻¹ := by
          gcongr
          exact le_add_left le_rfl
      _ = 1 := hJJ
  obtain ⟨b, hb⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp h2
  have hex : (b ⊔ c = ⊤ ∧ c ≠ ⊥ ∧
      𝔫 * (c : FractionalIdeal (𝓞 K)⁰ K) = (b : FractionalIdeal (𝓞 K)⁰ K)) := by
    refine ⟨?_, ?_, ?_⟩
    · apply FractionalIdeal.coeIdeal_injective (K := K)
      show ((b ⊔ c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      rw [FractionalIdeal.coeIdeal_sup, hb, hc, FractionalIdeal.coeIdeal_top]
      calc 𝔫 * (1 + 𝔫)⁻¹ + (1 + 𝔫)⁻¹ = (1 + 𝔫) * (1 + 𝔫)⁻¹ := by
            rw [add_mul, one_mul, add_comm]
        _ = 1 := hJJ
    · intro h
      have h0 := (FractionalIdeal.coeIdeal_eq_zero (K := K) (I := c)).mpr h
      exact inv_ne_zero hJ0 (hc ▸ h0)
    · rw [hb, hc]
  refine ⟨(b, c), hex, ?_⟩
  rintro ⟨b', c'⟩ hq
  have e : (c' : FractionalIdeal (𝓞 K)⁰ K) = c := by
    rw [hc]; exact key _ hq
  have e2 : (b' : FractionalIdeal (𝓞 K)⁰ K) = b := by
    rw [← hq.2.2, e, hex.2.2]
  rw [FractionalIdeal.coeIdeal_injective e, FractionalIdeal.coeIdeal_injective e2]

end NumberFieldKB.WeilBNT
