import NumberFieldKB.MilneCFT.Ch7.SecondInequalityKey
import NumberFieldKB.MilneCFT.Ch7.KummerEmbed
import NumberFieldKB.MilneCFT.Ch7.NormIso
import NumberFieldKB.MilneCFT.Ch7.Reductions

/-!
# Milne, *Class Field Theory*, Chapter VII §6: the second inequality for extensions of prime degree

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII,
§6 (pp. 214–218).

Milne's §6 proves the second inequality $(\mathbb I_K : K^\times\mathrm{Nm}(\mathbb I_L))\mid[L:K]$ for $L/K$ cyclic
of prime degree $p$ with $\zeta_p\in K$: write $L = K[a^{1/p}]$, choose $S$ so large that $a$ is an $S$-unit, so that
$L$ embeds in $M = K[U(S)^{1/p}]$ (`exists_kummer_embedding`), and apply the boxed formula to the image of $L$
(`secondInequality_kummer`'s ingredients); the norm group does not change under the $K$-isomorphism
(`principalNormIdeles_eq_of_algEquiv`). Lemma 6.1 then removes the hypothesis $\zeta_p\in K$.

* **`secondInequality_prime_zeta`**: the hypothesis of Lemma 6.1, from Lemmas 6.2, 6.4, 6.9, Propositions 6.8,
  6.10 and Kummer theory (`KummerAppendix`).
* **`secondInequality_prime`**: Theorem 5.1 (a) for every Galois extension of prime degree $p$, adding Lemma 6.1.
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

/-- **The second inequality for cyclic extensions of prime degree with $\zeta_p$ in the base** (Milne, *CFT*,
Chapter VII, §6, pp. 215–218): conditional on Lemmas 6.2, 6.4, 6.9, Propositions 6.8, 6.10 and Kummer theory
(`KummerAppendix`); Lemmas 6.6, 6.7 and the $S$-unit index are proved. -/
@[kb "milne2020cft" "Ch. VII, §6, second inequality for degree p with ζ_p in K (from Lemmas 6.2, 6.4, 6.9, Props 6.8, 6.10, App. A.3)"]
theorem secondInequality_prime_zeta (K : Type) [Field K] [NumberField K]
    (h62 : ∀ (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M]
      [NumberField M] [Algebra K M] [IsGalois K M], Lemma6_2 p S M)
    (h64 : ∀ (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M]
      [NumberField M] [Algebra K M] [IsGalois K M], Lemma6_4 p S M)
    (h69 : ∀ (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M]
      [NumberField M] [Algebra K M] [IsGalois K M], Lemma6_9 p S M)
    (h68 : Prop6_8 K) (h610 : Prop6_10 K) (hKum : KummerAppendix K)
    {p : ℕ} (hp : p.Prime) (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (hcard : Nat.card Gal(L/K) = p) :
    (principalNormIdeles K L).FiniteIndex ∧ (principalNormIdeles K L).index ∣ p := by
  obtain ⟨S, M, _, _, _, _, -, hset, hdeg, φ, -⟩ := exists_kummer_embedding hKum hp hζ L hcard
  rw [(sUnitIndex K).index p S hp hζ hset.finite] at hdeg
  let e : L ≃ₐ[K] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  have key := secondInequality_key' (h62 p S M) (h64 p S M) h68
    (lemma_6_7_of_lemma_6_9 h610 (h69 p S M)) hset hdeg φ.fieldRange
  have hdegL : Module.finrank K φ.fieldRange = p := by
    rw [← e.toLinearEquiv.finrank_eq, ← IsGalois.card_aut_eq_finrank, hcard]
  rw [principalNormIdeles_eq_of_algEquiv K L φ.fieldRange e]
  exact hdegL ▸ key

/-- **Theorem 5.1 (a) for Galois extensions of prime degree** (Milne, *CFT*, Chapter VII, Lemma 6.1 and §6): for
every Galois extension $L/F$ of number fields of prime degree $p$, $(\mathbb I_F : F^\times\mathrm{Nm}(\mathbb I_L))$
is finite and divides $p$. Conditional on Lemma 6.1 (reduction to $\zeta_p\in F$) and, for every number field,
Lemmas 6.2, 6.4, 6.9, Propositions 6.8, 6.10 and Kummer theory (`KummerAppendix`). -/
@[kb "milne2020cft" "Ch. VII, Thm. 5.1 (a) for prime degree (Lemma 6.1 and §6)"]
theorem secondInequality_prime (h61 : Lemma6_1)
    (h62 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 F))) (M : Type) [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], Lemma6_2 p S M)
    (h64 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 F))) (M : Type) [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], Lemma6_4 p S M)
    (h69 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 F))) (M : Type) [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], Lemma6_9 p S M)
    (h68 : ∀ (F : Type) [Field F] [NumberField F], Prop6_8 F)
    (h610 : ∀ (F : Type) [Field F] [NumberField F], Prop6_10 F)
    (hKum : ∀ (F : Type) [Field F] [NumberField F], KummerAppendix F)
    {p : ℕ} (hp : p.Prime) (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [IsGalois F L] (hcard : Nat.card Gal(L/F) = p) :
    (principalNormIdeles F L).FiniteIndex ∧ (principalNormIdeles F L).index ∣ p :=
  h61.reduce p hp (fun F L _ _ _ _ _ _ hζ hc =>
    secondInequality_prime_zeta F (h62 F) (h64 F) (h69 F) (h68 F) (h610 F) (hKum F) hp hζ L hc) F L hcard

end NumberFieldKB.MilneCFT.Ch7
