import NumberFieldKB.MilneCFT.Ch8.ReciprocityLaw
import NumberFieldKB.MilneCFT.Ch8.HilbertPairingArtin
import NumberFieldKB.MilneCFT.Ch5IdelicReciprocityTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.ArtinMapTransport
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# The global Hilbert symbol at a finite place is the local Hilbert pairing of the completion

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Proposition 5.2
(p. 178: the idèlic Artin map is the product of the local Artin maps) and Chapter VIII, Remark 5.9 (the Hilbert
symbol from the local Artin map).

Let $K$ be a number field containing a primitive $p$-th root of unity, $L = K(\beta)$ with $\beta^p = a$, and
$\varphi : I_K \to \mathrm{Gal}(L/K)$ an idèlic Artin map (properties (a), (b) of Summary 5.10, trivial on $K^\times$).
For a finite place $v$ with completion $K_v$, the global symbol `hilbertArtin L φ β v b` (Milne VIII 5.9) is, read in
$K_v$, the local Hilbert pairing `hilbertPairing` of $K_v$ (built from any local Artin map of $K_v$) at
$(a, b)$: `hilbertArtin_eq_hilbertPairing`.

Proof: $\varphi$ is Tau Ceti's idèlic Artin map (`idelicArtin_unique`), whose value on the idèle concentrated at $v$
is the local Artin symbol of $K_v$ restricted to $L$ along an embedding $j : L \to \overline{K_v}$
(`TauCeti.ClassFieldTheory.globalArtinMap_local`, `localArtinAt_eq_of_mk_eq_artinMap`); and every local Artin map
of $K_v$ is the Tau Ceti one (`eq_pullback_tauCetiArtin`), whose finite restrictions are those of the absolute local
Artin map (`TauCeti.ClassFieldTheory.artinMap_restrict`). Both symbols are then $\tau(\gamma)/\gamma$ for a
representative $\tau$ of the absolute Artin symbol of $b$ and a $p$-th root $\gamma$ of $a$ in $\overline{K_v}$
(`hilbertPairing_eq_of_artinMap`, `idelicArtinTauCeti_ofAdicCompletion_apply`).
-/

open scoped ValuativeRel
open NumberField IsDedekindDomain NumberFieldKB.MilneCFT.LocalCFT

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.Eisenstein

/-! ### The local side -/

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {Ω : Type} [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
variable {p : ℕ} [Fact p.Prime] {ζ : Fˣ}

/-- Two $p$-th roots of $a$ in a field extension of $F$ differ by a $p$-th root of unity of $F$, so an
$F$-automorphism multiplies them by the same factor. -/
theorem apply_eq_of_pthRoot {E : Type} [Field E] [Algebra F E] (hζ : IsPrimitiveRoot ζ p) {a : Fˣ} {γ γ₀ : E}
    (hγ : γ ^ p = algebraMap F E a) (hγ₀ : γ₀ ^ p = algebraMap F E a) (τ : E ≃ₐ[F] E) (u : F)
    (h₀ : τ γ₀ = algebraMap F E u * γ₀) : τ γ = algebraMap F E u * γ := by
  have hζ' : IsPrimitiveRoot (ζ : F) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζE : IsPrimitiveRoot (algebraMap F E ζ) p := hζ'.map_of_injective (algebraMap F E).injective
  have hγ₀0 : γ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out : p.Prime).ne_zero] at hγ₀
    exact a.ne_zero ((map_eq_zero _).mp hγ₀.symm)
  have h1 : (γ / γ₀) ^ p = 1 := by rw [div_pow, hγ, hγ₀, div_self]; simp
  obtain ⟨i, -, hi⟩ := hζE.eq_pow_of_pow_eq_one h1
  have hγeq : γ = algebraMap F E ((ζ : F) ^ i) * γ₀ := by
    rw [map_pow, hi, div_mul_cancel₀ _ hγ₀0]
  rw [hγeq, map_mul, AlgEquiv.commutes, h₀]
  ring

/-- **The local Hilbert pairing through the absolute local Artin map.** If $\tau \in G_F$ represents the absolute
Artin symbol of $b$ (Tau Ceti's `artinMap F`), then for every local Artin map `φ` and every $p$-th root $\gamma$ of
$a$ in $\overline F$, $\tau(\gamma) = (a, b)\,\gamma$. -/
theorem hilbertPairing_eq_of_artinMap (hζ : IsPrimitiveRoot ζ p)
    {φ : ∀ L : FiniteAbelianExt F Ω, Fˣ →* Gal(L.toField/F)} (hφ : IsLocalArtinMap φ) (a b : Fˣ)
    (τ : Field.absoluteGaloisGroup F)
    (hτ : (τ : Field.absoluteGaloisGroupAbelianization F) = TauCeti.ClassFieldTheory.artinMap F b)
    {γ : AlgebraicClosure F} (hγ : γ ^ p = algebraMap F (AlgebraicClosure F) a) :
    DFunLike.coe (F := Gal(AlgebraicClosure F/F)) τ γ =
      algebraMap F (AlgebraicClosure F) (hilbertPairing hζ hφ a b : F) * γ := by
  set e := IsSepClosure.equiv F Ω (SeparableClosure F)
  set α : Ω := pthRoot hζ a
  have hα : α ^ p = algebraMap F Ω a := pthRoot_pow hζ a
  set L' := kummerExt hζ hα
  have hαL : α ∈ L'.toField := by rw [kummerExt_toField]; exact IntermediateField.mem_adjoin_simple_self F _
  have hspec := hilbertSymbolArtin_spec hζ hφ a b L' hαL hα
  have hspec' : ((pullbackArtin e tauCetiArtin L' b ⟨α, hαL⟩ : L'.toField) : Ω) =
      algebraMap F Ω (hilbertSymbolArtin hζ φ a b) * α := by
    rw [← eq_pullback_tauCetiArtin Ω hφ]; exact hspec
  rw [coe_pullbackArtin_apply] at hspec'
  set L'' := L'.mapEquiv e
  set y : L''.toField := ⟨e α, ⟨α, hαL, rfl⟩⟩
  -- `hspec : e.symm (tauCetiArtin L'' b y) = (a,b) α`
  have h2 : ((tauCetiArtin L'' b y : L''.toField) : SeparableClosure F) =
      algebraMap F (SeparableClosure F) (hilbertSymbolArtin hζ φ a b : F) * e α := by
    have := congrArg e hspec'
    rw [AlgEquiv.apply_symm_apply, map_mul, AlgEquiv.commutes] at this
    exact this
  -- the Tau Ceti local Artin map is restriction of the absolute one
  let ι : L''.toField →ₐ[F] SeparableClosure F := L''.toField.val
  have h3 := abelianizationOf_tauCetiArtin L'' ι b
  rw [TauCeti.ClassFieldTheory.artinMap_restrict F L''.toField ι b τ hτ] at h3
  have h4 : tauCetiArtin L'' b =
      ι.restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv F τ) :=
    (abelianizationOfEquiv _).injective h3
  have h5 : ((tauCetiArtin L'' b y : L''.toField) : SeparableClosure F) =
      TauCeti.absoluteGaloisGroupRestrictEquiv F τ (e α) := by
    rw [h4]
    exact ι.restrictNormalHom_commutes _ y
  rw [h5] at h2
  -- read in the algebraic closure
  set γ₀ : AlgebraicClosure F := ((e α : SeparableClosure F) : AlgebraicClosure F)
  have hγ₀ : γ₀ ^ p = algebraMap F (AlgebraicClosure F) a := by
    have : (e α) ^ p = algebraMap F (SeparableClosure F) a := by rw [← map_pow, hα, AlgEquiv.commutes]
    change ((e α : SeparableClosure F) : AlgebraicClosure F) ^ p = _
    rw [← IntermediateField.coe_pow, this]; rfl
  have h6 : DFunLike.coe (F := Gal(AlgebraicClosure F/F)) τ γ₀ =
      algebraMap F (AlgebraicClosure F) (hilbertSymbolArtin hζ φ a b : F) * γ₀ := by
    have h7 := TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply F
      (τ : Gal(AlgebraicClosure F/F)) (e α)
    refine h7.symm.trans ?_
    rw [h2]; rfl
  exact apply_eq_of_pthRoot hζ hγ hγ₀ τ _ h6

end Local

/-! ### The global side -/

section Global

variable {K : Type} [Field K] [NumberField K]
variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- **Tau Ceti's idèlic Artin map on an idèle concentrated at $v$.** If $\tau \in G_{K_v}$ represents the absolute
local Artin symbol of $x \in K_v^\times$, then for every $K$-embedding $j : L \to \overline{K_v}$,
$j(\varphi(x)(y)) = \tau(j(y))$. -/
theorem idelicArtinTauCeti_ofAdicCompletion_apply (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ)
    (τ : Field.absoluteGaloisGroup (v.adicCompletion K))
    (hτ : (τ : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      TauCeti.ClassFieldTheory.artinMap (v.adicCompletion K) x)
    (j : L →ₐ[K] AlgebraicClosure (v.adicCompletion K)) (y : L) :
    j (idelicArtinTauCeti L (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) y) = τ.toRingEquiv (j y) := by
  let σ : Gal(L/K) := j.restrictNormalHom (AlgEquiv.restrictScalarsHom K τ)
  have hσ : ∀ y, j (σ y) = τ.toRingEquiv (j y) := fun y => j.restrictNormalHom_commutes _ y
  have h1 := TauCeti.ClassFieldTheory.localArtinAt_eq_of_mk_eq_artinMap v τ hτ j σ hσ
  have h2 : Abelianization.of (idelicArtinTauCeti L (IdeleGroup.ofAdicCompletion (𝓞 K) K v x)) =
      TauCeti.ClassFieldTheory.localArtinAt K L v x := by
    rw [of_idelicArtinTauCeti, TauCeti.ClassFieldTheory.globalArtinMap_local]
    rfl
  rw [h1] at h2
  rw [(abelianizationOfEquiv Gal(L/K)).injective h2]
  exact hσ y

variable {p : ℕ} [Fact p.Prime]

/-- **Local–global compatibility of the Hilbert symbol at a finite place** (Milne, *CFT*, V, Prop. 5.2 with VIII,
5.9): for $L = K(\beta)$, $\beta^p = a$, an idèlic Artin map $\varphi$ of $L/K$ trivial on $K^\times$, and a finite
place $v$, the global symbol $(a, b)_v$ = `hilbertArtin L φ β v b`, read in $K_v$, is the local Hilbert pairing of
$K_v$ at $(a, b)$, for every local Artin map of $K_v$. -/
@[kb "milne2020cft" "v4.03, Ch. V, Prop. 5.2, p. 178 (local-global compatibility of the Hilbert symbol)"]
theorem hilbertArtin_eq_hilbertPairing {ζ : K} (hζ : IsPrimitiveRoot ζ p) {a : Kˣ} {β : L}
    (hβ : β ^ p = algebraMap K L a)
    (φg : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφg : IsIdelicArtinMap L φg)
    (hφgK : ∀ c : Kˣ, φg (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1) (v : HeightOneSpectrum (𝓞 K))
    {Ω : Type} [Field Ω] [Algebra (v.adicCompletion K) Ω] [IsSepClosure (v.adicCompletion K) Ω]
    {ζv : (v.adicCompletion K)ˣ} (hζv : IsPrimitiveRoot ζv p)
    {φ : ∀ M : FiniteAbelianExt (v.adicCompletion K) Ω, (v.adicCompletion K)ˣ →* Gal(M.toField/(v.adicCompletion K))}
    (hφ : IsLocalArtinMap φ) (b : Kˣ) :
    algebraMap K (v.adicCompletion K) (hilbertArtin L φg β v b) =
      (hilbertPairing hζv hφ (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom b) : v.adicCompletion K) := by
  set Kv := v.adicCompletion K
  have hφg' : φg = idelicArtinTauCeti L :=
    idelicArtin_unique L φg _ hφg (isIdelicArtinMap_tauCeti L) hφgK (idelicArtinTauCeti_principal L)
  set x : Kvˣ := Units.map (algebraMap K Kv).toMonoidHom b
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap Kv x)
  let j : L →ₐ[K] AlgebraicClosure Kv := IsAlgClosed.lift
  have hglob := idelicArtinTauCeti_ofAdicCompletion_apply L v x τ hτ j β
  subst hφg'
  have hspec := hilbertArtin_spec L p (Fact.out : p.Prime).pos ζ hζ (a : K) a.ne_zero β hβ
    (idelicArtinTauCeti L) v b
  rw [hspec, map_mul, AlgHom.commutes] at hglob
  have hjβ : (j β) ^ p = algebraMap Kv (AlgebraicClosure Kv) (Units.map (algebraMap K Kv).toMonoidHom a) := by
    rw [← map_pow, hβ, AlgHom.commutes, IsScalarTower.algebraMap_apply K Kv (AlgebraicClosure Kv)]
    rfl
  have hloc := hilbertPairing_eq_of_artinMap hζv hφ _ x τ hτ hjβ
  have hβ0 : j β ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at hjβ
    exact (Units.map (algebraMap K Kv).toMonoidHom a).ne_zero ((map_eq_zero _).mp hjβ.symm)
  have : algebraMap Kv (AlgebraicClosure Kv) (algebraMap K Kv (hilbertArtin L (idelicArtinTauCeti L) β v b)) =
      algebraMap Kv (AlgebraicClosure Kv) (hilbertPairing hζv hφ (Units.map (algebraMap K Kv).toMonoidHom a) x : Kv) := by
    rw [← IsScalarTower.algebraMap_apply K Kv (AlgebraicClosure Kv)]
    refine mul_right_cancel₀ hβ0 ?_
    rw [← hloc]
    exact hglob
  exact (algebraMap Kv (AlgebraicClosure Kv)).injective this

end Global

end NumberFieldKB.MilneCFT.Ch8.Eisenstein
