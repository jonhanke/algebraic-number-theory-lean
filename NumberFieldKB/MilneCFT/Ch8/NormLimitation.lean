import NumberFieldKB.MilneCFT.Ch8.Brauer
import NumberFieldKB.MilneCFT.Ch7.NormTransitivity
import NumberFieldKB.MilneCFT.Ch7.ExistenceProof
import NumberFieldKB.MilneCFT.Ch7.KeyCase
import NumberFieldKB.MilneCFT.Ch7.SUnitIndex
import NumberFieldKB.MilneCFT.Ch7.IdelicExistence
import NumberFieldKB.MilneCFT.Ch7.IdealExistence

/-!
# The norm limitation theorem in the form used by the existence theorem

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter VIII,
Theorem 4.8 (the norm limitation theorem, p. 242) and Chapter VII, Lemma 9.4 and Theorem 9.5 (pp. 225–226).

Milne proves the existence theorem (Chapter VII, Theorem 9.5) assuming the norm limitation theorem "which is not
proved until the next chapter" (p. 225). Chapter VII's input `NormLimitation` is the form used in Lemma 9.4; Chapter
VIII's `Theorem4_8` is Milne's statement $\mathrm{Nm}_{E/K}C_E = \mathrm{Nm}_{M/K}C_M$. The step between them is the
tower law for idele class norms in a tower that need not be Galois (`Ch7.normClasses_comp`, proved).

* `exists_maxAbelian`: a finite extension $E/K$ has a largest subextension abelian over $K$.
* **`normLimitation_of_theorem4_8`**: Chapter VIII, Theorem 4.8 implies Chapter VII's `NormLimitation`.
* **`theorem9_5_of_theorem4_8`**: the existence theorem from Lemma 9.3, the reciprocity law and Chapter VIII,
  Theorem 4.8 (Milne's route).
* `theorem9_5_of_section6`, `idelicExistence_of_section6`, `exists_hilbertClassField_of_section6`,
  `existenceTheoremArtin_of_section6`: the existence theorem and its consequences from the inputs of Chapter VII §6
  (the $S$-unit index is no longer an input: `Ch7.sUnitIndex`).
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

/-- **A largest abelian subextension exists** (Milne, *CFT*, Chapter VIII, Theorem 4.8, "the maximal subextension of
$E$ abelian over $K$"): for a finite extension $E/K$ of number fields there is an intermediate field $M$, Galois and
abelian over $K$, containing every intermediate field that is Galois and abelian over $K$. (It is the compositum of
those fields; here, one of maximal degree, which contains every other by `IsAbelianGalois.sup`.) -/
theorem exists_maxAbelian (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] :
    ∃ M : IntermediateField K E, IsAbelianGalois K M ∧
      ∀ F : IntermediateField K E, IsGalois K F → (∀ σ τ : Gal(F/K), σ * τ = τ * σ) → F ≤ M := by
  have hex : ∃ n : ℕ, ∃ F : IntermediateField K E, IsAbelianGalois K F ∧
      Module.finrank K E - Module.finrank K F = n :=
    ⟨_, ⊥, inferInstance, rfl⟩
  classical
  let n := Nat.find hex
  obtain ⟨M, hM, hMn⟩ := Nat.find_spec hex
  refine ⟨M, hM, fun F hFg hFc => ?_⟩
  haveI : IsAbelianGalois K F := { toIsGalois := hFg, toIsMulCommutative := ⟨⟨hFc⟩⟩ }
  haveI := hM
  have hsup : IsAbelianGalois K ↥(M ⊔ F) := inferInstance
  have hle : M ≤ M ⊔ F := le_sup_left
  have hrank_le : Module.finrank K M ≤ Module.finrank K ↥(M ⊔ F) :=
    IntermediateField.finrank_le_of_le_right hle
  have hrank_E : Module.finrank K ↥(M ⊔ F) ≤ Module.finrank K E :=
    (M ⊔ F).toSubalgebra.toSubmodule.finrank_le
  have hmin := Nat.find_min' hex ⟨M ⊔ F, hsup, rfl⟩
  have heq : Module.finrank K M = Module.finrank K ↥(M ⊔ F) := by omega
  have := IntermediateField.eq_of_le_of_finrank_eq hle heq
  rw [this]
  exact le_sup_right

variable (K : Type) [Field K] [NumberField K]

/-- **Chapter VIII, Theorem 4.8 gives Chapter VII's `NormLimitation`** (Milne, *CFT*, Chapter VII, proof of
Lemma 9.4: $\mathrm{Nm}_{M/K}C_M = \mathrm{Nm}_{L/K}C_L = \mathrm{Nm}_{K'/K}U'$ for $M$ the maximal abelian
subextension of $L/K$). For a tower $K\subseteq K'\subseteq L$, $\mathrm{Nm}_{K'/K}(\mathrm{Nm}_{L/K'}C_L) =
\mathrm{Nm}_{L/K}C_L$ (`Ch7.normClasses_comp`), which by Theorem 4.8 is the norm group $\mathrm{Nm}_{M/K}C_M$. -/
@[kb "milne2020cft" "Ch. VIII, Thm. 4.8 ⇒ Ch. VII norm limitation as used in Lemma 9.4"]
theorem normLimitation_of_theorem4_8 (h48 : Theorem4_8 K) : Ch7.NormLimitation K := by
  refine ⟨fun K' _ _ _ L _ _ _ _ _ => ?_⟩
  obtain ⟨M, hM, hmax⟩ := exists_maxAbelian K L
  have hc : ∀ σ τ : Gal(M/K), σ * τ = τ * σ := fun σ τ => mul_comm' σ τ
  refine ⟨Ch7.normClasses K M, ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, hc, rfl⟩, ?_⟩
  rw [Ch7.normClasses_comp K K' L, h48.eq L M hc hmax]

/-- **The existence theorem from Lemma 9.3, the reciprocity law and the norm limitation theorem of Chapter VIII**
(Milne, *CFT*, Chapter VII, Theorem 9.5, with the norm limitation theorem in Milne's form, Chapter VIII, Theorem 4.8):
every open subgroup of finite index of $C_K$ is a norm group. -/
@[kb "milne2020cft" "Ch. VII, Thm. 9.5 (from Lemma 9.3, the reciprocity law and Ch. VIII, Thm. 4.8)"]
theorem theorem9_5_of_theorem4_8
    (h93 : ∀ (F : Type) [Field F] [NumberField F], Ch7.Lemma9_3 F)
    (hR : ∀ (F : Type) [Field F] [NumberField F], Ch7.ReciprocityLaw F)
    (h48 : ∀ (F : Type) [Field F] [NumberField F], Theorem4_8 F) : Ch7.Theorem9_5 K :=
  Ch7.theorem9_5_of_lemmas h93 hR (fun F _ _ => normLimitation_of_theorem4_8 F (h48 F)) K

/-- **The existence theorem with Lemma 9.3 proved** (Milne, *CFT*, Chapter VII, Theorem 9.5, following Milne's proof
of Lemma 9.3, `Ch7.lemma_9_3_of_section6`): conditional on the reciprocity law, Lemma 6.4, Propositions 6.8 and 6.10,
Kummer theory (`Ch7.KummerAppendix`) and the norm limitation theorem of Chapter VIII (Theorem 4.8), every open
subgroup of finite index of $C_K$ is a norm group. The $S$-unit index is proved (`Ch7.sUnitIndex`). -/
@[kb "milne2020cft" "Ch. VII, Thm. 9.5 (Lemma 9.3 from §6, Ch. VIII, Thm. 4.8)"]
theorem theorem9_5_of_section6
    (hR : ∀ (F : Type) [Field F] [NumberField F], Ch7.ReciprocityLaw F)
    (h64 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
      (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M], Ch7.Lemma6_4 p S M)
    (h68 : ∀ (F : Type) [Field F] [NumberField F], Ch7.Prop6_8 F)
    (h610 : ∀ (F : Type) [Field F] [NumberField F], Ch7.Prop6_10 F)
    (hKum : ∀ (F : Type) [Field F] [NumberField F], Ch7.KummerAppendix F)
    (h48 : ∀ (F : Type) [Field F] [NumberField F], Theorem4_8 F) : Ch7.Theorem9_5 K :=
  theorem9_5_of_theorem4_8 K
    (fun F _ _ => Ch7.lemma_9_3_of_section6 F (hR F) (h64 F) (h68 F) (h610 F) (hKum F) (Ch7.sUnitIndex F)) hR h48

/-- **The existence theorem of Chapter V (Theorem 5.5) from the reciprocity law and the inputs of Chapter VII §6**
(Milne, *CFT*): conditional on the idelic reciprocity law (Chapter V, Theorem 5.3, for every number field), Lemma 6.4,
Propositions 6.8 and 6.10, Kummer theory (`Ch7.KummerAppendix`) and the norm
limitation theorem (Chapter VIII, Theorem 4.8): for every open subgroup $N$ of finite index of $C_K$ there is a finite
abelian $L/K$, unique up to isomorphism, with $\mathrm{Nm}(C_L) = N$. -/
@[kb "milne2020cft" "Ch. V, Thm. 5.5 (from Thm. 5.3, Ch. VII §6 and §9, Ch. VIII Thm. 4.8)"]
theorem idelicExistence_of_section6
    (hR : ∀ (F : Type) [Field F] [NumberField F], IdelicReciprocity F)
    (h64 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
      (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M], Ch7.Lemma6_4 p S M)
    (h68 : ∀ (F : Type) [Field F] [NumberField F], Ch7.Prop6_8 F)
    (h610 : ∀ (F : Type) [Field F] [NumberField F], Ch7.Prop6_10 F)
    (hKum : ∀ (F : Type) [Field F] [NumberField F], Ch7.KummerAppendix F)
    (h48 : ∀ (F : Type) [Field F] [NumberField F], Theorem4_8 F) : IdelicExistence K :=
  idelicExistence_of_theorem9_5 (hR K)
    (theorem9_5_of_section6 K (fun F _ _ => reciprocityLaw_of_idelic (hR F)) h64 h68 h610 hKum h48)

/-- **The Hilbert class field from the reciprocity law and the inputs of Chapter VII** (Milne, *CFT*, Chapter V,
Example 3.9, with the existence theorem proved as in Chapter VII): conditional on the idelic reciprocity law (Chapter V,
Theorem 5.3), Lemma 6.4, Propositions 6.8 and 6.10, Kummer theory, the norm limitation theorem
(Chapter VIII, Theorem 4.8) and `ArtinInertia` (local–global compatibility at inertia), every number field $K$ has a
Hilbert class field. -/
@[kb "milne2020cft" "Ch. V, Example 3.9 (from Thm. 5.3, Ch. VII §6, §9, Ch. VIII Thm. 4.8)"]
theorem exists_hilbertClassField_of_section6
    (hR : ∀ (F : Type) [Field F] [NumberField F], IdelicReciprocity F)
    (h64 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
      (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M], Ch7.Lemma6_4 p S M)
    (h68 : ∀ (F : Type) [Field F] [NumberField F], Ch7.Prop6_8 F)
    (h610 : ∀ (F : Type) [Field F] [NumberField F], Ch7.Prop6_10 F)
    (hKum : ∀ (F : Type) [Field F] [NumberField F], Ch7.KummerAppendix F)
    (h48 : ∀ (F : Type) [Field F] [NumberField F], Theorem4_8 F) (hI : ArtinInertia K) :
    ∃ (H : Type) (_ : Field H) (_ : NumberField H) (_ : Algebra K H) (_ : IsAbelianGalois K H),
      HilbertClassField.IsHilbertClassField K H :=
  exists_hilbertClassField_of_idelic K (hR K) (idelicExistence_of_section6 K hR h64 h68 h610 hKum h48) hI

/-- **The ideal-theoretic existence theorem with the Artin isomorphism** (Milne, *CFT*, Chapter V, Theorem 3.6 and the
note after it, via Remark 5.8 and Chapter VII): conditional on the idelic reciprocity law (Theorem 5.3), the inputs of
Chapter VII §6, the norm limitation theorem (Chapter VIII, Theorem 4.8) and `ArtinInertia`. -/
@[kb "milne2020cft" "Ch. V, Thm. 3.6 (from Thm. 5.3, Ch. VII §6, §9, Ch. VIII Thm. 4.8)"]
theorem existenceTheoremArtin_of_section6
    (hR : ∀ (F : Type) [Field F] [NumberField F], IdelicReciprocity F)
    (h64 : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
      (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M], Ch7.Lemma6_4 p S M)
    (h68 : ∀ (F : Type) [Field F] [NumberField F], Ch7.Prop6_8 F)
    (h610 : ∀ (F : Type) [Field F] [NumberField F], Ch7.Prop6_10 F)
    (hKum : ∀ (F : Type) [Field F] [NumberField F], Ch7.KummerAppendix F)
    (h48 : ∀ (F : Type) [Field F] [NumberField F], Theorem4_8 F) (hI : ArtinInertia K) :
    ExistenceTheoremArtin K :=
  existenceTheoremArtin_of_idelic K (hR K) (idelicExistence_of_section6 K hR h64 h68 h610 hKum h48) hI

end NumberFieldKB.MilneCFT.Ch8
