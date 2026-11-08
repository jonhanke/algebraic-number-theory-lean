import NumberFieldKB.MilneCFT.Ch7.SecondInequalityPrime
import NumberFieldKB.MilneCFT.Ch7.Reciprocity

/-!
# Milne, *Class Field Theory*, Chapter VII, Theorem 5.1 (the second inequality) from §§5–6

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII,
§§5–6 (pp. 212–218) and §8 (p. 221).

Milne's proof of Theorem 5.1: by Lemma 5.3 it suffices to treat $p$-groups, by Lemma 5.4 cyclic groups of order $p$;
for those, Lemma 5.2 (proved here from Theorem 4.3) shows that (a), (b), (c) are equivalent, and (a) is the second
inequality for prime degree (`secondInequality_prime`: Lemma 6.1 and §6).

* `thm51For_prime`: Theorem 5.1 for Galois extensions of prime degree.
* **`theorem5_1_of_section6`**: Theorem 5.1 from Theorem 4.3, Lemmas 5.3, 5.4, 6.1 and the inputs of §6.
* **`reciprocity_of_section6`**: Milne's reciprocity law for $L/K$ (p. 221) from Theorem 8.1 (a) and the above.
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

/-- **Theorem 5.1 for Galois extensions of prime degree** (Milne, *CFT*, Chapter VII, Lemma 5.2 and §6): conditional
on Theorem 4.3, Lemma 6.1 and, for every number field, Lemmas 6.2, 6.4, 6.9, Propositions 6.8, 6.10 and Kummer
theory (`KummerAppendix`). -/
theorem thm51For_prime (h43 : ∀ (F : Type) [Field F] [NumberField F], Theorem4_3 F) (h61 : Lemma6_1)
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
    [IsGalois F L] (hcard : Nat.card Gal(L/F) = p) : Thm51For F L := by
  have : Fact p.Prime := ⟨hp⟩
  have hc : IsCyclic Gal(L/F) := isCyclic_of_prime_card hcard
  have hdeg : Module.finrank F L = p := by rw [← IsGalois.card_aut_eq_finrank, hcard]
  obtain ⟨hab, hbc, -⟩ := lemma_5_2 F L (h43 F) hc
  have ha : (principalNormIdeles F L).FiniteIndex ∧ (principalNormIdeles F L).index ∣ Module.finrank F L := by
    rw [hdeg]
    exact secondInequality_prime h61 h62 h64 h69 h68 h610 hKum hp F L hcard
  exact ⟨ha, hab.1 ha, hbc.1 (hab.1 ha)⟩

/-- **Theorem 5.1** (the second inequality, $H^1(G,C_L) = 0$, $|H^2(G,C_L)|\mid[L:K]$; Milne, *CFT*, Chapter VII,
pp. 212–218), by Milne's proof: conditional on Theorem 4.3 (the first inequality for cyclic extensions), the reductions
Lemmas 5.3, 5.4, 6.1, and, for every number field, Lemmas 6.2, 6.4, 6.9, Propositions 6.8, 6.10 and Kummer theory
(`KummerAppendix`). Lemma 5.2, Lemmas 6.5–6.7, the $S$-unit index, the Kummer embedding and the boxed formula of §6
are proved. -/
@[kb "milne2020cft" "Ch. VII, Thm. 5.1 (from Thm. 4.3, Lemmas 5.3, 5.4, 6.1 and §6)"]
theorem theorem5_1_of_section6 (K : Type) [Field K] [NumberField K]
    (h43 : ∀ (F : Type) [Field F] [NumberField F], Theorem4_3 F) (h53 : Lemma5_3) (h54 : Lemma5_4)
    (h61 : Lemma6_1)
    (h62 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 F))) (M : Type) [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], Lemma6_2 p S M)
    (h64 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 F))) (M : Type) [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], Lemma6_4 p S M)
    (h69 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 F))) (M : Type) [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], Lemma6_9 p S M)
    (h68 : ∀ (F : Type) [Field F] [NumberField F], Prop6_8 F)
    (h610 : ∀ (F : Type) [Field F] [NumberField F], Prop6_10 F)
    (hKum : ∀ (F : Type) [Field F] [NumberField F], KummerAppendix F) : Theorem5_1 K := by
  have hall : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L],
      Thm51For F L :=
    h53.reduce fun p hp F L _ _ _ _ _ _ hpg =>
      h54.reduce p hp (fun F L _ _ _ _ _ _ hcard =>
        thm51For_prime h43 h61 h62 h64 h69 h68 h610 hKum hp F L hcard) F L hpg
  exact ⟨fun L _ _ _ _ => (hall K L).1, fun L _ _ _ _ => (hall K L).2.1, fun L _ _ _ _ => (hall K L).2.2⟩

/-- **The reciprocity law from Theorem 8.1 (a) and the inputs of §§4–6** (Milne, *CFT*, Chapter VII, p. 221): for a
global Artin map $\psi$ trivial on $K^\times$ and every finite abelian $L/K$, $\psi_{L/K}$ is surjective with kernel
$K^\times\mathrm{Nm}(\mathbb I_L)$. Theorem 5.1 enters through `theorem5_1_of_section6`. -/
@[kb "milne2020cft" "Ch. VII, §8, p. 221 (reciprocity law from Thm. 8.1 (a), Thm. 5.1 via §§5–6)"]
theorem reciprocity_of_section6 (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω]
    (h43 : ∀ (F : Type) [Field F] [NumberField F], Theorem4_3 F) (h53 : Lemma5_3) (h54 : Lemma5_4)
    (h61 : Lemma6_1)
    (h62 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 F))) (M : Type) [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], Lemma6_2 p S M)
    (h64 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 F))) (M : Type) [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], Lemma6_4 p S M)
    (h69 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 F))) (M : Type) [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], Lemma6_9 p S M)
    (h68 : ∀ (F : Type) [Field F] [NumberField F], Prop6_8 F)
    (h610 : ∀ (F : Type) [Field F] [NumberField F], Prop6_10 F)
    (hKum : ∀ (F : Type) [Field F] [NumberField F], KummerAppendix F)
    (h81 : Theorem8_1a K Ω)
    (ψ : ∀ E : AbExt K Ω, IdeleGroup (𝓞 K) K →* Gal(E.L/K)) (hψ : IsGlobalArtinMap K Ω ψ) (E : AbExt K Ω) :
    Function.Surjective (ψ E) ∧ (ψ E).ker = principalNormIdeles K E.L :=
  reciprocity_of_thm_8_1a (theorem5_1_of_section6 K h43 h53 h54 h61 h62 h64 h69 h68 h610 hKum) h81 ψ hψ E

end NumberFieldKB.MilneCFT.Ch7
