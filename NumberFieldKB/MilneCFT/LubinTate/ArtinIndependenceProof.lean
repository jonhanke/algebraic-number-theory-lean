import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.LubinTate.ArtinMap
import NumberFieldKB.MilneCFT.LubinTate.LocalKroneckerWeberCFT
import NumberFieldKB.MilneCFT.LubinTate.ExtensionYamaguchi
import NumberFieldKB.MilneCFT.LocalCFT.ReciprocityTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.UnconditionalYamaguchi
import NumberFieldKB.MilneCFT.LubinTate.ArtinIndependenceAux

/-!
# Milne, *Class Field Theory*, Chapter I, Theorem 3.9, reduced to the explicit reciprocity law

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

`LubinTateArtinIndependence` (Theorem 3.9: $K_\pi K^{\mathrm{un}}$ and $\phi_\pi$ do not depend on $\pi$) is proved here
from the named statement `LubinTateExplicitReciprocity`: the local Artin map of Theorem 1.1 (any family with
`IsLocalArtinMap`, unique by `isLocalArtinMap_unique_unconditional`) acts on $\Lambda_n$ through $[u^{-1}]_f$ for every
unit $u$. Milne derives this (the local Artin map of §1 is $\phi_\pi$, p. 40–44) from Theorem 3.9 itself, whose proof
uses Proposition 3.10 (the isomorphism $\theta$ over $\widehat{K^{\mathrm{un}}}$) to compare $\phi_\pi$ and $\phi_\varpi$
on $K_\varpi$. What is missing in the library for a proof of `LubinTateExplicitReciprocity`: the evaluation of $\theta$
at the torsion points $\Lambda_{f,n}$ in the completion of $K^{\mathrm{al}}$ (neither Tau Ceti nor the Yamaguchi port
treat a general local field; Yamaguchi covers $\mathbb Q_p$ and $\mathbb F_q((t))$).

The other parts are unconditional consequences of local class field theory: the field equality is local
Kronecker–Weber (`localKroneckerWeber`), $\phi_\pi$ is the local Artin map (`tauCetiArtin`; $\pi$ is a norm from
every $K_{\pi,n}$, `isNorm_succ`), and a family with Milne's properties is unique (an automorphism of
$K_{\pi,n}K_m$ is determined by its actions on $K_{\pi,n}$ and on $K_m$).
-/

open scoped ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Explicit reciprocity law for Lubin–Tate extensions** (named statement; Milne, *CFT*, I, §3, p. 40 and
Theorem 3.9 with Theorem 1.1: the local Artin map is $\phi_\pi$ for every prime $\pi$) [unverified page]: for every
local Artin map $\phi$, every prime element $\pi$, every finite abelian $L \supseteq K_{\pi,n}$ and every unit $u$,
$\phi_L(u)$ acts on $\Lambda_n$ by $[u^{-1}]_f$. -/
@[kb "milne2020cft" "Ch. I, §3, p. 40 and Theorem 3.9 (explicit reciprocity; input)"]
structure LubinTateExplicitReciprocity : Prop where
  torsion : ∀ (φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)), IsLocalArtinMap φ →
    ∀ {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) (L : FiniteAbelianExt K Ω) (hL : ltField Ω π n ≤ L.toField)
      (u : 𝒪[K]ˣ) (α : Ω) (hα : α ∈ ltTorsion Ω π n),
      ((φ L (unitToK u) ⟨α, hL (mem_ltField hα)⟩ : L.toField) : Ω) = ltAct hπ n ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) α

/-! ## Theorem 3.9 from the explicit reciprocity law -/

section ArtinIndependence

variable {K Ω}

/-- The local Artin map of Theorem 1.1 (Tau Ceti's) acts on $\Lambda_n$ as $\phi_\pi$ should: $\phi_L(u\pi^m)$ acts
by $[u^{-1}]_f$ (the $\pi^m$ part acts trivially since $\pi$ is a norm from $K_{\pi,n}$, and the unit part is the
explicit reciprocity law). -/
theorem tauCetiArtin_torsion (h : LubinTateExplicitReciprocity K Ω) {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)
    (L : FiniteAbelianExt K Ω) (hL : ltField Ω π n ≤ L.toField) (u : 𝒪[K]ˣ) (m : ℤ) (α : Ω)
    (hα : α ∈ ltTorsion Ω π n) :
    ((tauCetiArtin L (unitToK u * primeUnit hπ ^ m) ⟨α, hL (mem_ltField hα)⟩ : L.toField) : Ω) =
      ltAct hπ n ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) α := by
  have hx : α ∈ ltField Ω π n := mem_ltField hα
  rw [map_mul, map_zpow]
  show ((tauCetiArtin L (unitToK u) ((tauCetiArtin L (primeUnit hπ) ^ m) ⟨α, hL hx⟩) : L.toField) : Ω) = _
  rw [zpow_apply_eq_of_apply_eq _ _ (tauCetiArtin_primeUnit_apply hπ n L hL ⟨α, hL hx⟩ hx) m]
  exact h.torsion (fun L => tauCetiArtin L) isLocalArtinMap_tauCeti_family hπ n L hL u α hα

/-- Existence of $\phi_\pi$: the family of Tau Ceti local Artin maps has Milne's properties. -/
theorem isLubinTateArtin_tauCetiArtin (h : LubinTateExplicitReciprocity K Ω) {π : 𝒪[K]}
    (hπ : Irreducible π) : IsLubinTateArtin (Ω := Ω) hπ (fun L => tauCetiArtin L) where
  compat L L' hLL' _ a := galRestrict_tauCetiArtin L L' hLL' a
  frobenius L hL σ hσ u m := tauCetiArtin_frobenius hπ L hL σ hσ u m
  torsion n L hL _ u m α hα := tauCetiArtin_torsion h hπ n L hL u m α hα

/-- Uniqueness of $\phi_\pi$: any family with the properties of `IsLubinTateArtin` agrees with the local Artin map
of Theorem 1.1 on every finite abelian extension inside $K_\pi K^{\mathrm{un}}$. Such an extension lies in
$K_{\pi,n+1} K_{m!}$, a finite abelian extension, and an automorphism of the compositum is determined by its
actions on $K_{\pi,n+1}$ (generated by the torsion points $\Lambda_{n+1}$) and on the unramified $K_{m!}$. -/
theorem eq_tauCetiArtin_of_isLubinTateArtin (h : LubinTateExplicitReciprocity K Ω) {π : 𝒪[K]}
    (hπ : Irreducible π) {φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}
    (hφ : IsLubinTateArtin (Ω := Ω) hπ φ) (L : FiniteAbelianExt K Ω)
    (hL : L.toField ≤ ltTower Ω π ⊔ unramifiedClosure K Ω) : φ L = tauCetiArtin L := by
  obtain ⟨n, m, hLnm⟩ := exists_le_ltField_sup hπ L.toField hL
  have hm : m.factorial ≠ 0 := Nat.factorial_ne_zero _
  set A := ltFieldExt (lubinTateExtensionTheorem K Ω) hπ (n := n + 1) (by omega) with hA
  set B := unrExt (K := K) (Ω := Ω) m.factorial hm with hB
  set N := A.sup B with hNdef
  have hAN : A.toField ≤ N.toField := le_sup_left
  have hBN : B.toField ≤ N.toField := le_sup_right
  have hLN : L.toField ≤ N.toField := hLnm.trans (sup_le_sup_right (ltField_le_succ hπ n) _)
  have hBun : B.toField ≤ unramifiedClosure K Ω := by
    rw [unramifiedClosure_eq_iSup]
    exact le_iSup (fun k : ℕ => TauCeti.unramifiedExtension K Ω k.factorial) m
  have hNle : N.toField ≤ ltTower Ω π ⊔ unramifiedClosure K Ω :=
    sup_le ((le_iSup (ltField Ω π) (n + 1)).trans le_sup_left) (hBun.trans le_sup_right)
  have hBunr : IsUnramifiedExt B.toField := isUnramifiedExt_unrExt m.factorial hm
  have hρ := isFrobenius_tauCetiArtin hπ B hBunr
  have hmain : ∀ a : Kˣ, φ N a = tauCetiArtin N a := by
    intro a
    obtain ⟨u0, hu0, k, rfl⟩ := exists_unit_zpow π hπ a
    obtain ⟨u, hu⟩ := mem_unitGroup.1 hu0
    have hu0' : u0 = unitToK u := Units.ext hu.symm
    subst hu0'
    set σ := φ N (unitToK u * primeUnit hπ ^ k) with hσ
    set τ := tauCetiArtin N (unitToK u * primeUnit hπ ^ k) with hτ
    have hB' : ∀ x : N.toField, (x : Ω) ∈ B.toField → σ x = τ x := by
      intro x hx
      have e1 : galRestrict hBN σ = tauCetiArtin B (primeUnit hπ) ^ k := by
        rw [hσ, hφ.compat B N hBN hNle]
        exact hφ.frobenius B hBunr _ hρ u k
      have e2 : galRestrict hBN τ = tauCetiArtin B (primeUnit hπ) ^ k := by
        rw [hτ, galRestrict_tauCetiArtin B N hBN]
        exact tauCetiArtin_frobenius hπ B hBunr _ hρ u k
      apply Subtype.ext
      have h1 := galRestrict_apply hBN σ ⟨x, hx⟩
      have h2 := galRestrict_apply hBN τ ⟨x, hx⟩
      rw [e1] at h1
      rw [e2] at h2
      exact h1.symm.trans h2
    have hA' : ∀ x : Ω, ∀ hx : x ∈ N.toField, x ∈ ltTorsion Ω π (n + 1) → σ ⟨x, hx⟩ = τ ⟨x, hx⟩ := by
      intro x hx hxS
      apply Subtype.ext
      rw [hσ, hτ]
      exact (hφ.torsion (n + 1) N hAN hNle u k x hxS).trans
        (tauCetiArtin_torsion h hπ (n + 1) N hAN u k x hxS).symm
    have hg : σ⁻¹ * τ = 1 := by
      have : Algebra.IsAlgebraic K Ω := by
        have : Algebra.IsSeparable K Ω := IsSepClosure.separable
        exact Algebra.IsSeparable.isAlgebraic K Ω
      refine eq_one_of_fixes_sup (M₁ := A.toField) (M₂ := B.toField) hAN hBN le_rfl _ ?_ ?_
      · refine fix_of_adjoin (ltTorsion Ω π (n + 1)) (fun x hx => hAN (mem_ltField hx))
          (fun x _ => Algebra.IsAlgebraic.isAlgebraic x) _ ?_
        intro x hx hxS
        rw [AlgEquiv.mul_apply, ← hA' x hx hxS, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
      · intro x hx
        rw [AlgEquiv.mul_apply, ← hB' x hx, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    exact inv_mul_eq_one.1 hg
  refine MonoidHom.ext fun a => ?_
  rw [← hφ.compat L N hLN hNle a, hmain a, galRestrict_tauCetiArtin L N hLN a]

variable (K Ω) in
/-- **Theorem 3.9** (Milne, *CFT*, I, Theorem 3.9), from the explicit reciprocity law
`LubinTateExplicitReciprocity`: $K_\pi K^{\mathrm{un}}$ and $\phi_\pi$ do not depend on the prime element $\pi$,
and $\phi_\pi$ exists. The field equality is local Kronecker–Weber (`ltTower_sup_unramifiedClosure_eq`); $\phi_\pi$
is the local Artin map of Theorem 1.1 (`tauCetiArtin`), and any family with Milne's properties equals it
(`eq_tauCetiArtin_of_isLubinTateArtin`). -/
@[kb "milne2020cft" "Ch. I, Theorem 3.9 (from the explicit reciprocity law)"]
theorem lubinTateArtinIndependence_of (h : LubinTateExplicitReciprocity K Ω) :
    LubinTateArtinIndependence K Ω where
  exists_artin hπ := ⟨_, isLubinTateArtin_tauCetiArtin h hπ⟩
  field_eq hπ hϖ := ltTower_sup_unramifiedClosure_eq hπ hϖ
  artin_eq {π ϖ} hπ hϖ φ ψ hφ hψ L hL := by
    have hL' : L.toField ≤ ltTower Ω ϖ ⊔ unramifiedClosure K Ω := by
      rw [← ltTower_sup_unramifiedClosure_eq hπ hϖ]; exact hL
    rw [eq_tauCetiArtin_of_isLubinTateArtin h hπ hφ L hL,
      eq_tauCetiArtin_of_isLubinTateArtin h hϖ hψ L hL']

end ArtinIndependence

end NumberFieldKB.MilneCFT.LocalCFT
