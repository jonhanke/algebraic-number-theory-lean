import NumberFieldKB.MilneCFT.Ch2TateTheorem
import NumberFieldKB.MilneCFT.Ch2Example314
import NumberFieldKB.MilneCFT.Ch2Example314TauCeti
import NumberFieldKB.MilneCFT.Ch3Artin
import NumberFieldKB.MilneCFT.Ch7.ExistenceTauCeti
import NumberFieldKB.MilneCFT.Ch7.KeyCase
import NumberFieldKB.MilneCFT.Ch8.ReciprocityLaw
import NumberFieldKB.MilneCFT.Ch8.H2TauCeti
import NumberFieldKB.HilbertClassField.TauCeti
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Milne, *Class Field Theory*: the global theorems without their discharged named inputs

The named inputs `IdelicReciprocity` (V 5.3), `IdelicExistence` (V 5.5), `Ch7.ReciprocityLaw`, `Ch7.Theorem9_5`,
`Ch7.Lemma9_3`, `Ch7.NormLimitation`, `Ch8.Theorem4_7`, `Thm3_11` (Tate's theorem) and `LocalCFT.KroneckerWeber` are
proved from the Tau Ceti port (see `Ch5IdelicReciprocityTauCeti.lean`, `Ch7/ExistenceTauCeti.lean`,
`Ch8/H2TauCeti.lean`, `Ch2TateTheorem.lean`, `LubinTate/KroneckerWeberTauCeti.lean`). This file restates their
consumers without those hypotheses; the conditional originals are unchanged.
-/

open NumberField IsDedekindDomain CategoryTheory Rep
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

variable (K) in
/-- **Theorem 3.5, the reciprocity law, unconditional** (Milne, *CFT*, V, Theorem 3.5): every finite abelian extension
has a defining modulus. From the idèlic reciprocity law (`reciprocityLaw_ideal_of_idelic`). -/
@[kb "milne2020cft" "Ch. V, Theorem 3.5"]
theorem reciprocityLaw_ideal : ReciprocityLaw K :=
  reciprocityLaw_ideal_of_idelic (K := K) (idelicReciprocity K)

variable (K) in
/-- **Theorem 0.8 (Artin reciprocity), unconditional** (Milne, *CFT*, Introduction, Theorem 0.8). -/
@[kb "milne2020cft" "Introduction, Theorem 0.8"]
theorem artinReciprocity : ArtinReciprocity K :=
  artinReciprocity_of_reciprocityLaw (K := K) (reciprocityLaw_ideal K)

/-- **Theorem 5.3(b) with idèle classes, unconditional** (Milne, *CFT*, V, p. 179):
$C_K/\mathrm{Nm}(C_L) \cong \mathrm{Gal}(L/K)$. -/
@[kb "milne2020cft" "Ch. V, Theorem 5.3 (C_K/Nm(C_L) ≅ Gal(L/K))"]
theorem theorem_5_3_classes' (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] :
    ∃ φ : IdeleClassGroup (𝓞 K) K →* Gal(L/K), Function.Surjective φ ∧ φ.ker = normGroupC K L :=
  theorem_5_3_classes (idelicReciprocity K) L

/-- **Summary 5.10, unconditional** (Milne, *CFT*, V, p. 181). -/
@[kb "milne2020cft" "Ch. V, Summary 5.10"]
theorem summary_5_10' (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] :
    ∃! φ : IdeleGroup (𝓞 K) K →* Gal(L/K), IsIdelicArtinMap L φ ∧
      (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧ Function.Surjective φ ∧
      φ.ker = ideleNormGroup L :=
  summary_5_10 (idelicReciprocity K) L

/-- **Corollary 5.6, unconditional** (Milne, *CFT*, V, p. 179). -/
@[kb "milne2020cft" "Ch. V, Corollary 5.6"]
theorem cor_5_6' (Ω : Type) [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω) [NumberField L₁] [NumberField L₂] [IsAbelianGalois K L₁]
    [IsAbelianGalois K L₂] [NumberField ↥(L₁ ⊔ L₂)] [NumberField ↥(L₁ ⊓ L₂)] [IsAbelianGalois K ↥(L₁ ⊓ L₂)] :
    (L₁ ≤ L₂ ↔ normGroupC K L₂ ≤ normGroupC K L₁) ∧
      normGroupC K ↥(L₁ ⊔ L₂) = normGroupC K L₁ ⊓ normGroupC K L₂ ∧
      normGroupC K ↥(L₁ ⊓ L₂) = normGroupC K L₁ ⊔ normGroupC K L₂ ∧
      (∀ N : Subgroup (IdeleClassGroup (𝓞 K) K), (IsOpen (N : Set (IdeleClassGroup (𝓞 K) K)) ∧ N.FiniteIndex) ↔
        IsNormGroupC N) :=
  cor_5_6 (idelicReciprocity K) (idelicExistence K) Ω L₁ L₂

/-- **Example 3.14, unconditional** (Milne, *CFT*, II, p. 85): for a finite Galois extension $L/K$ of nonarchimedean
local fields, $H^r_T(G,\mathbb Z) \simeq H^{r+2}_T(G, L^\times)$ for all $r$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 3.14, p. 85"]
theorem example_3_14' (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (r : ℤ) :
    Nonempty (tateCohomology (trivial ℤ (L ≃ₐ[K] L) ℤ) r ≅
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) (r + 2)) :=
  example_3_14 thm3_11 example3_14 K L r

end NumberFieldKB.MilneCFT

namespace NumberFieldKB.MilneCFT.Ch3

open LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Theorem 3.1, without Tate's theorem as a hypothesis** (Milne, *CFT*, III, Theorem 3.1, p. 107): given the system
of invariant maps `s`, $H^r_T(G,\mathbb Z)\simeq H^{r+2}_T(G, L^\times)$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 3.1, p. 107"]
theorem theorem_3_1' (s : InvariantSystem K Ω) (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L] (r : ℤ) :
    Nonempty (tateCohomology (trivial ℤ Gal(L/K) ℤ) r ≅
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) (r + 2)) :=
  theorem_3_1 thm3_11 s L r

/-- **Theorem 3.1 ($r=-2$), without Tate's theorem as a hypothesis** (Milne, *CFT*, III, p. 107). -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 3.1 (r = -2), p. 107"]
theorem theorem_3_1_ab' (s : InvariantSystem K Ω) (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L] :
    Nonempty (Additive (Abelianization Gal(L/K)) ≃+ Additive (Kˣ ⧸ normGroup L)) :=
  theorem_3_1_ab thm3_11 s L

end NumberFieldKB.MilneCFT.Ch3

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]

/-- **Lemma 9.1, unconditional** (Milne, *CFT*, VII, p. 223): a subgroup containing a norm group is a norm group. -/
@[kb "milne2020cft" "Ch. VII, Lemma 9.1"]
theorem lemma_9_1' {U V : Subgroup (IdeleClassGroup (𝓞 K) K)} (hU : IsNormGroup K U) (hUV : U ≤ V) :
    IsNormGroup K V :=
  lemma_9_1 K (ch7_reciprocityLaw K) hU hUV

/-- **Lemma 9.4, unconditional** (Milne, *CFT*, VII, p. 225). -/
@[kb "milne2020cft" "Ch. VII, Lemma 9.4"]
theorem lemma_9_4' (U : Subgroup (IdeleClassGroup (𝓞 K) K))
    (K' : Type) [Field K'] [NumberField K'] [Algebra K K']
    (hU' : IsNormGroup K' (U.comap (ideleClassNorm K K'))) : IsNormGroup K U :=
  lemma_9_4 K (ch7_reciprocityLaw K) (normLimitation K) U K' hU'

/-- **The norm index for abelian extensions, unconditional**: $(C_K : \mathrm{Nm}(C_M)) = [M:K]$. -/
@[kb "milne2020cft" "Ch. VII, Theorem 5.1 (norm index, abelian case)"]
theorem index_normClasses' (M : Type) [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (hc : ∀ σ τ : Gal(M/K), σ * τ = τ * σ) :
    (normClasses K M).index = Module.finrank K M :=
  index_normClasses (ch7_reciprocityLaw K) M hc

end NumberFieldKB.MilneCFT.Ch7

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type} [Field K] [NumberField K]

/-- **5.5, unconditional** (Milne, *CFT*, VIII, 5.5, p. 245): for $a \in K^\times$ there is a modulus $\mathfrak m$
with support in $S(a)$ such that $(a/\mathfrak b)$ depends only on the class of $\mathfrak b$ in $C_\mathfrak m$. -/
@[kb "milne2020cft" "Ch. VIII, 5.5, p. 245"]
theorem item_5_5' (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K)
    (ha : a ≠ 0) : ∃ m : Modulus K, m.finiteSupport ⊆ Sset n {a} ∧
      ∀ b b' : (FractionalIdeal (𝓞 K)⁰ K)ˣ, b ∈ sIdeals (Sset n {a}) → b' ∈ sIdeals (Sset n {a}) →
        b * b'⁻¹ ∈ rayPrincipal m → powerResidueIdeal n a b = powerResidueIdeal n a b' :=
  item_5_5 (reciprocityLaw_ideal K) n hn ζ hζ a ha

end NumberFieldKB.MilneCFT.Ch8
