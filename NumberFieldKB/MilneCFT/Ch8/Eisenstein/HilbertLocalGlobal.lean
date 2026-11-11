import NumberFieldKB.MilneCFT.Ch8.Eisenstein.CompletionIso
import NumberFieldKB.MilneCFT.Ch8.Eisenstein.Reciprocity
import NumberFieldKB.MilneCFT.Ch8.Eisenstein.PairingTransport
import NumberFieldKB.MilneCFT.Ch8.Prop512Full
import NumberFieldKB.MilneCFT.LocalCFT.ReciprocityTauCeti
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Local–global compatibility of the Hilbert symbol at $\lambda$, and Proposition 5.12 in full

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Proposition 5.2
(p. 178) and Chapter VIII, Proposition 5.12 (p. 248).

`hilbertLocalGlobal` proves the named input `HilbertLocalGlobal` in the setting of `prop_5_12_full`: $K = \mathbb
Q(\zeta_p)$, a local field $K_l$ with an embedding $\iota$, uniformizer $\iota(1 - \zeta)$ and residue field $\mathbb
F_p$, an idèlic Artin map $\varphi$ of $K(\zeta^{1/p})/K$ trivial on $K^\times$, and the prime $v \ni \zeta - 1$. Proof:
$K_l$ is the completion $K_\lambda$ (`exists_completion_equiv`), the global symbol at $\lambda$ is the local pairing of
$K_\lambda$ (`hilbertArtin_eq_hilbertPairing`), and local pairings correspond along the isomorphism
(`hilbertPairing_map_equiv`).

`prop_5_12_full_unconditional` is `prop_5_12_full` with the hypothesis `HilbertLocalGlobal` discharged.
-/

open scoped ValuativeRel
open NumberField IsDedekindDomain NumberFieldKB.MilneCFT.LocalCFT

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.Eisenstein

variable {Kl : Type} [Field Kl] [ValuativeRel Kl] [TopologicalSpace Kl] [IsNonarchimedeanLocalField Kl]
variable {Ω : Type} [Field Ω] [Algebra Kl Ω] [IsSepClosure Kl Ω]

/-- **Local–global compatibility of the Hilbert symbol at $\lambda$** (the named input `HilbertLocalGlobal`), proved
under the hypotheses of `prop_5_12_full`. -/
@[kb "milne2020cft" "v4.03, Ch. V, Prop. 5.2, p. 178 (local-global compatibility at λ; proved)"]
theorem hilbertLocalGlobal {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (ι : K →+* Kl)
    {ζl : Klˣ} (hζl : IsPrimitiveRoot ζl p) (hιζ : (ζl : Kl) = ι ζ)
    {φ : ∀ L : FiniteAbelianExt Kl Ω, Klˣ →* Gal(L.toField/Kl)} (hφ : IsLocalArtinMap φ)
    {lam : 𝒪[Kl]} (hlam : Irreducible lam) (hlamζ : (lam : Kl) = 1 - ι ζ) (hres : Nat.card 𝓀[Kl] = p)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L)
    (hα : α ^ p = algebraMap K L ζ)
    (φg : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφg : IsIdelicArtinMap L φg)
    (hφgK : ∀ c : Kˣ, φg (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (hζ.toInteger - 1 : 𝓞 K) ∈ v.asIdeal) :
    HilbertLocalGlobal ι hζl hιζ hφ L α φg v := by
  -- `v = λ`
  have hvl : v = lamPlace hζ := by
    have hle : (lamPlace hζ).asIdeal ≤ v.asIdeal := by
      rw [lamPlace_asIdeal, Ideal.span_le, Set.singleton_subset_iff]; exact hv
    exact (HeightOneSpectrum.ext ((lamPlace hζ).isMaximal.eq_of_le v.isPrime.ne_top hle)).symm
  subst hvl
  obtain ⟨e, he, heι⟩ := exists_completion_equiv hζ hlam hlamζ hres
  set Kq := Klam hζ
  obtain ⟨φq, hφq⟩ := (localReciprocityExistence Kq (SeparableClosure Kq)).exists_artin
  have hζ0 : IsUnit ζ := hζ.isUnit hp.out.ne_zero
  set ζv : Kqˣ := unitAt (lamPlace hζ) hζ0.unit
  have hζv : IsPrimitiveRoot ζv p := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    exact hζ.map_of_injective (algebraMap K Kq).injective
  refine ⟨fun b => ?_⟩
  have hloc := hilbertArtin_eq_hilbertPairing L hζ (a := hζ0.unit) hα φg hφg hφgK (lamPlace hζ) hζv hφq b
  have htr := hilbertPairing_map_equiv e he hζv hζl hφq hφ (unitAt (lamPlace hζ) hζ0.unit) (unitAt (lamPlace hζ) b)
  have hζe : Units.map e.toMonoidHom (unitAt (lamPlace hζ) hζ0.unit) = ζl := by
    apply Units.ext
    change e (algebraMap K Kq ζ) = _
    rw [heι, hιζ]
  have hbe : Units.map e.toMonoidHom (unitAt (lamPlace hζ) b) = Units.map ι.toMonoidHom b := by
    apply Units.ext
    change e (algebraMap K Kq b) = ι b
    rw [heι]
  rw [hζe, hbe] at htr
  rw [htr, ← hloc, heι]

/-- **`HilbertLocalGlobal` for the canonical Artin maps**, with no hypothesis on the maps: `hilbertLocalGlobal` applied to
a local Artin map of $K_l$ given by `localReciprocityExistence` (from Tau Ceti's local reciprocity law) and to Tau Ceti's
idèlic Artin map `idelicArtinTauCeti` (`isIdelicArtinMap_tauCeti`, trivial on $K^\times$ by
`idelicArtinTauCeti_principal`). The general `hilbertLocalGlobal` holds for every pair of maps satisfying the
predicates `IsLocalArtinMap`, `IsIdelicArtinMap`; this instance shows that those conditions are met. -/
@[kb "milne2020cft" "v4.03, Ch. V, Prop. 5.2, p. 178 (local-global compatibility at λ, canonical Artin maps; proved)"]
theorem hilbertLocalGlobal_canonical {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (ι : K →+* Kl)
    {ζl : Klˣ} (hζl : IsPrimitiveRoot ζl p) (hιζ : (ζl : Kl) = ι ζ)
    {lam : 𝒪[Kl]} (hlam : Irreducible lam) (hlamζ : (lam : Kl) = 1 - ι ζ) (hres : Nat.card 𝓀[Kl] = p)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L)
    (hα : α ^ p = algebraMap K L ζ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (hζ.toInteger - 1 : 𝓞 K) ∈ v.asIdeal) :
    HilbertLocalGlobal ι hζl hιζ (localReciprocityExistence (K := Kl) (Ω := Ω)).exists_artin.choose_spec L α
      (idelicArtinTauCeti L) v :=
  hilbertLocalGlobal hζ ι hζl hιζ _ hlam hlamζ hres L α hα (idelicArtinTauCeti L) (isIdelicArtinMap_tauCeti L)
    (idelicArtinTauCeti_principal L) v hv

/-- **Milne, *CFT*, VIII, Proposition 5.12, in full** (p. 248), unconditionally: `prop_5_12_full` with the named input
`HilbertLocalGlobal` discharged by `hilbertLocalGlobal`. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Prop. 5.12, p. 248 (unconditional)"]
theorem prop_5_12_full_unconditional {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (ι : K →+* Kl)
    {ζl : Klˣ} (hζl : IsPrimitiveRoot ζl p) (hιζ : (ζl : Kl) = ι ζ)
    {φ : ∀ L : FiniteAbelianExt Kl Ω, Klˣ →* Gal(L.toField/Kl)} (hφ : IsLocalArtinMap φ)
    {lam ε : 𝒪[Kl]} (hlam : Irreducible lam) (hlamζ : (lam : Kl) = 1 - ι ζ) (hε : IsUnit ε)
    (hplam : (p : 𝒪[Kl]) = ε * lam ^ (p - 1)) (hres : Nat.card 𝓀[Kl] = p)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L)
    (hα : α ^ p = algebraMap K L ζ) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (φg : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφg : IsIdelicArtinMap L φg)
    (hφgK : ∀ c : Kˣ, φg (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (hζ.toInteger - 1 : 𝓞 K) ∈ v.asIdeal) :
    IsExplicitPairing (hilbertPairing hζl hφ) p (lamUnit hlam) (etaUnit hlam) ζl (fun i _ => i) ∧
      (∀ i j, 1 ≤ i → 1 ≤ j → p + 1 ≤ i + j → ∀ u w : Klˣ,
        (∃ c : 𝒪[Kl], (u : Kl) = 1 + (lam : Kl) ^ i * c) → (∃ c : 𝒪[Kl], (w : Kl) = 1 + (lam : Kl) ^ j * c) →
        hilbertPairing hζl hφ u w = 1) ∧
      (∀ P' : Klˣ →* Klˣ →* Klˣ, IsSteinbergPairing P' p →
        P' (etaUnit hlam p) (lamUnit hlam) = ζl → P' = hilbertPairing hζl hφ) :=
  prop_5_12_full hp2 hζ ι hζl hιζ hφ hlam hlamζ hε hplam hres L α hα hgen φg hφg hφgK v hv
    (hilbertLocalGlobal hζ ι hζl hιζ hφ hlam hlamζ hres L α hα φg hφg hφgK v hv)

end NumberFieldKB.MilneCFT.Ch8.Eisenstein
