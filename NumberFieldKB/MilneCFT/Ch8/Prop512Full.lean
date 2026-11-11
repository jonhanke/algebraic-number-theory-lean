import NumberFieldKB.MilneCFT.Ch8.Prop512
import NumberFieldKB.MilneCFT.Ch8.Prop512Normalization
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Milne, *Class Field Theory*, VIII, Proposition 5.12 in full, from local–global compatibility

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §5,
Proposition 5.12, p. 248.

`prop_5_12` (Prop512.lean) proves everything in Proposition 5.12 for the local Hilbert pairing except the value
$(\eta_p, \lambda) = \zeta$, which it reduces to $(\zeta, \eta_{p-1})$. `hilbertArtin_zeta_eta` (Prop512Normalization.lean)
computes the value $(\zeta, \eta_{p-1})_\lambda = \zeta$ for the **global** symbol of $\mathbb Q(\zeta_p)$ at $\lambda$.
The two are joined by one cited fact, the named input `HilbertLocalGlobal`.

**`HilbertLocalGlobal`** (named input). The local symbol of $K_\lambda$, built from a local Artin map, agrees on
global elements with Milne's global symbol at $\lambda$, built from an idèlic Artin map: for $b \in \mathbb Q(\zeta)^\times$,
$\iota((\zeta, b)_\lambda) = (\iota\zeta, \iota b)$. This is the compatibility of the local Artin map of $K_\lambda$ with the
$\lambda$-component of the global Artin map (Milne, *CFT*, V, Prop. 5.2, p. 178: the idèlic Artin map is the product of the local Artin maps;
in Tau Ceti the global Artin map is built from the local ones). It is stated only for the first argument $\zeta$, the
one case used. It is not definitionally equal to the conclusion: it relates two differently defined symbols, and the
value of neither is assumed.

**`prop_5_12_full`**: given `HilbertLocalGlobal`, the local Hilbert pairing satisfies all of Milne's (a)–(c),
including $(\eta_p, \lambda) = \zeta$ with $\lambda = 1 - \zeta$. It is the unique Steinberg pairing of exponent $p$
with this value.

*Proof of `HilbertLocalGlobal`.* It is proved, under the hypotheses of `prop_5_12_full`, by
`Eisenstein.hilbertLocalGlobal` (Ch8/Eisenstein/HilbertLocalGlobal.lean): the abstract local field is the completion
of $\mathbb Q(\zeta_p)$ at $\lambda$ (`Eisenstein.exists_completion_equiv`), the global symbol at $\lambda$ is the
local pairing of the completion (`Eisenstein.hilbertArtin_eq_hilbertPairing`, from Tau Ceti's global class field
theory), and local pairings correspond along isomorphisms (`Eisenstein.hilbertPairing_map_equiv`). The unconditional
form of this proposition is `Eisenstein.prop_5_12_full_unconditional`. This file keeps the conditional form so that
the reduction stays separate from the proof of the input.
-/

open scoped ValuativeRel
open NumberField IsDedekindDomain NumberFieldKB.MilneCFT.LocalCFT

namespace NumberFieldKB.MilneCFT.Ch8

variable {Kl : Type} [Field Kl] [ValuativeRel Kl] [TopologicalSpace Kl] [IsNonarchimedeanLocalField Kl]
variable {Ω : Type} [Field Ω] [Algebra Kl Ω] [IsSepClosure Kl Ω]

/-- **Local–global compatibility of the Hilbert symbol at $\lambda$** (named input; see the module docstring): for an
embedding $\iota : K \to K_\lambda$ of $K = \mathbb Q(\zeta_p)$ into the local field, the local pairing
`hilbertPairing hζl hφ` and the global symbol `hilbertArtin L φg α v` (first argument $\zeta$, $\alpha^p = \zeta$)
agree on $(\zeta, b)$, $b \in K^\times$. -/
@[kb "milne2020cft" "v4.03, Ch. V, Prop. 5.2, p. 178 (local-global compatibility of Artin maps; proved, Eisenstein.hilbertLocalGlobal)"]
structure HilbertLocalGlobal {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K] (ι : K →+* Kl)
    {ζ : K} {ζl : Klˣ} (hζl : IsPrimitiveRoot ζl p) (hιζ : (ζl : Kl) = ι ζ)
    {φ : ∀ L : FiniteAbelianExt Kl Ω, Klˣ →* Gal(L.toField/Kl)} (hφ : IsLocalArtinMap φ)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L)
    (φg : IdeleGroup (𝓞 K) K →* Gal(L/K)) (v : HeightOneSpectrum (𝓞 K)) : Prop where
  compat : ∀ b : Kˣ, ι (hilbertArtin L φg α v b) = (hilbertPairing hζl hφ ζl (Units.map ι.toMonoidHom b) : Kl)

/-- **Milne, *CFT*, VIII, Proposition 5.12, in full** (p. 248), conditional on the named input `HilbertLocalGlobal`
(and on the local and idèlic Artin maps, given as data with their properties). Let $p$ be an odd prime, $K = \mathbb Q(\zeta)$,
$\iota : K \to K_\lambda$ into a local field with uniformizer $\lambda = \iota(1 - \zeta)$, $p = \varepsilon\lambda^{p-1}$
and residue field $\mathbb F_p$. Then the Hilbert pairing of $K_\lambda$ satisfies (a)–(c) with
$(\eta_p, \lambda) = \zeta$, and is the unique Steinberg pairing of exponent $p$ with this value. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Prop. 5.12, p. 248"]
theorem prop_5_12_full {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (ι : K →+* Kl)
    {ζl : Klˣ} (hζl : IsPrimitiveRoot ζl p) (hιζ : (ζl : Kl) = ι ζ)
    {φ : ∀ L : FiniteAbelianExt Kl Ω, Klˣ →* Gal(L.toField/Kl)} (hφ : IsLocalArtinMap φ)
    {lam ε : 𝒪[Kl]} (hlam : Irreducible lam) (hlamζ : (lam : Kl) = 1 - ι ζ) (hε : IsUnit ε)
    (hplam : (p : 𝒪[Kl]) = ε * lam ^ (p - 1)) (hres : Nat.card 𝓀[Kl] = p)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L)
    (hα : α ^ p = algebraMap K L ζ) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (φg : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφg : IsIdelicArtinMap L φg)
    (hφgK : ∀ c : Kˣ, φg (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (hζ.toInteger - 1 : 𝓞 K) ∈ v.asIdeal)
    (hLG : HilbertLocalGlobal ι hζl hιζ hφ L α φg v) :
    IsExplicitPairing (hilbertPairing hζl hφ) p (lamUnit hlam) (etaUnit hlam) ζl (fun i _ => i) ∧
      (∀ i j, 1 ≤ i → 1 ≤ j → p + 1 ≤ i + j → ∀ u w : Klˣ,
        (∃ c : 𝒪[Kl], (u : Kl) = 1 + (lam : Kl) ^ i * c) → (∃ c : 𝒪[Kl], (w : Kl) = 1 + (lam : Kl) ^ j * c) →
        hilbertPairing hζl hφ u w = 1) ∧
      (∀ P' : Klˣ →* Klˣ →* Klˣ, IsSteinbergPairing P' p →
        P' (etaUnit hlam p) (lamUnit hlam) = ζl → P' = hilbertPairing hζl hφ) := by
  obtain ⟨h1, h2, h3, h4⟩ := prop_5_12 (Ω := Ω) hp2 hζl hφ hlam hε hplam hres
  -- the value
  have hb0 : (1 - (1 - ζ) ^ (p - 1) : K) ≠ 0 := by
    intro h0
    have := congrArg ι h0
    rw [map_sub, map_one, map_pow, map_sub, map_one, map_zero, ← hlamζ] at this
    have hk : (etaUnit hlam (p - 1) : Kl) = 0 := by
      rw [etaUnit_val hlam (by have := hp.out.two_le; omega)]; exact this
    exact (etaUnit hlam (p - 1)).ne_zero hk
  set b : Kˣ := Units.mk0 _ hb0
  have hglob := hilbertArtin_zeta_eta hp2 hζ L α hα hgen φg hφg hφgK v hv b rfl
  have hcomp := hLG.compat b
  rw [hglob, ← hιζ] at hcomp
  have he1 : etaUnit hlam 1 = ζl := by
    apply Units.ext
    rw [etaUnit_val hlam le_rfl, pow_one, hlamζ, hιζ]; ring
  have hep : etaUnit hlam (p - 1) = Units.map ι.toMonoidHom b := by
    apply Units.ext
    rw [etaUnit_val hlam (by have := hp.out.two_le; omega)]
    simp [b, hlamζ]
  have hval : hilbertPairing hζl hφ (etaUnit hlam p) (lamUnit hlam) = ζl := by
    rw [h4, he1, hep]
    exact Units.ext hcomp.symm
  rw [hval] at h1
  refine ⟨h1, h2, fun P' hP' hP'v => h3 P' hP' (hP'v.trans hval.symm)⟩

end NumberFieldKB.MilneCFT.Ch8
