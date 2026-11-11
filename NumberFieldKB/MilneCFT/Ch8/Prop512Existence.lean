import NumberFieldKB.MilneCFT.Ch8.Prop512Full
import NumberFieldKB.MilneCFT.LocalCFT.ReciprocityTauCeti
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Milne, *Class Field Theory*, VIII, Proposition 5.12 without a local Artin map hypothesis

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §5,
Proposition 5.12, p. 248.

`prop_5_12_full` (Prop512Full.lean) took a local Artin map `φ` of $K_\lambda$ with `IsLocalArtinMap φ` as data. Its
existence is `LocalCFT.LocalReciprocityExistence`, now proved (`LocalCFT.localReciprocityExistence`, from the ported
Tau Ceti local reciprocity law). `prop_5_12_of_existence` therefore states the result with that hypothesis discharged:
there is a local Artin map `φ` of $K_\lambda$ for which, given the named input `HilbertLocalGlobal` for `φ`, all of
Milne's (a)–(c) hold and the Hilbert pairing built from `φ` is the unique Steinberg pairing with
$(\eta_p, \lambda) = \zeta$. The input `HilbertLocalGlobal` (local–global compatibility, Milne V, Prop. 5.2) is now
proved under these hypotheses (`Eisenstein.hilbertLocalGlobal`, Ch8/Eisenstein/HilbertLocalGlobal.lean), and
`Eisenstein.prop_5_12_full_unconditional` is the form with it discharged. The idèlic Artin map `φg` and its
triviality on $K^\times$ stay hypotheses of the statement (they are the data the global symbol is built from).
-/

open scoped ValuativeRel
open NumberField IsDedekindDomain NumberFieldKB.MilneCFT.LocalCFT

namespace NumberFieldKB.MilneCFT.Ch8

variable {Kl : Type} [Field Kl] [ValuativeRel Kl] [TopologicalSpace Kl] [IsNonarchimedeanLocalField Kl]
variable (Ω : Type) [Field Ω] [Algebra Kl Ω] [IsSepClosure Kl Ω]

/-- **Milne, *CFT*, VIII, Proposition 5.12**, with the local Artin map hypothesis of `prop_5_12_full` discharged by
`LocalCFT.localReciprocityExistence`: there is a local Artin map `φ` of $K_\lambda$ such that, under the named input
`HilbertLocalGlobal` for `φ`, the conclusions of `prop_5_12_full` hold. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Prop. 5.12, p. 248"]
theorem prop_5_12_of_existence {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (ι : K →+* Kl)
    {ζl : Klˣ} (hζl : IsPrimitiveRoot ζl p) (hιζ : (ζl : Kl) = ι ζ)
    {lam ε : 𝒪[Kl]} (hlam : Irreducible lam) (hlamζ : (lam : Kl) = 1 - ι ζ) (hε : IsUnit ε)
    (hplam : (p : 𝒪[Kl]) = ε * lam ^ (p - 1)) (hres : Nat.card 𝓀[Kl] = p)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L)
    (hα : α ^ p = algebraMap K L ζ) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (φg : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφg : IsIdelicArtinMap L φg)
    (hφgK : ∀ c : Kˣ, φg (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (hζ.toInteger - 1 : 𝓞 K) ∈ v.asIdeal) :
    ∃ (φ : ∀ L : FiniteAbelianExt Kl Ω, Klˣ →* Gal(L.toField/Kl)) (hφ : IsLocalArtinMap φ),
      HilbertLocalGlobal ι hζl hιζ hφ L α φg v →
        IsExplicitPairing (hilbertPairing hζl hφ) p (lamUnit hlam) (etaUnit hlam) ζl (fun i _ => i) ∧
          (∀ i j, 1 ≤ i → 1 ≤ j → p + 1 ≤ i + j → ∀ u w : Klˣ,
            (∃ c : 𝒪[Kl], (u : Kl) = 1 + (lam : Kl) ^ i * c) → (∃ c : 𝒪[Kl], (w : Kl) = 1 + (lam : Kl) ^ j * c) →
            hilbertPairing hζl hφ u w = 1) ∧
          (∀ P' : Klˣ →* Klˣ →* Klˣ, IsSteinbergPairing P' p →
            P' (etaUnit hlam p) (lamUnit hlam) = ζl → P' = hilbertPairing hζl hφ) := by
  obtain ⟨φ, hφ⟩ := (localReciprocityExistence Kl Ω).exists_artin
  exact ⟨φ, hφ, fun hLG =>
    prop_5_12_full (Ω := Ω) hp2 hζ ι hζl hιζ hφ hlam hlamζ hε hplam hres L α hα hgen φg hφg hφgK v hv hLG⟩

end NumberFieldKB.MilneCFT.Ch8
