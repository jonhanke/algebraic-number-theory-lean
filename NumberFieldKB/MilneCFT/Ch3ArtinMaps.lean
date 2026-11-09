import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Artin
import NumberFieldKB.MilneCFT.Ch3Unramified
import NumberFieldKB.MilneCFT.Ch2Cup

/-!
# Milne, *Class Field Theory*, Chapter III §3: properties of the local Artin map

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

The local Artin map is Chapter I's encoding: a family $\phi_L : K^\times \to \operatorname{Gal}(L/K)$ over the finite
abelian extensions $L \subseteq \Omega$ satisfying `IsLocalArtinMap`. Milne's statements for Galois $L/K$ with
$\operatorname{Gal}(L/K)^{\mathrm{ab}}$ are stated here for abelian $L/K$ (for Galois $L$, $\operatorname{Gal}(L/K)^{
\mathrm{ab}} = \operatorname{Gal}(L^{\mathrm{ab}}/K)$ with $L^{\mathrm{ab}}$ the largest abelian subextension).

* `Lemma3_2` — Lemma 3.2 (named; Milne: "proof to be added"), for a finite extension $E/K$ of local fields.
* `item_3_3` — (3.3): compatibility of $\phi_{L/K}$ and $\phi_{E/K}$ under restriction.
* `Prop3_6` — Proposition 3.6 (named): $\chi(\phi_{L/K}(a)) = \mathrm{inv}_K(a \cup \delta\chi)$.
* `lemma_3_7` — Lemma 3.7: for $L/K$ unramified, $\phi_{L/K}(a) = \mathrm{Frob}^{\mathrm{ord}_K(a)}$, proved from
  Chapter I.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory MonoidalCategory Rep groupCohomology Limits NumberFieldKB.MilneCFT
  NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

variable (K Ω) in
/-- **Lemma 3.2** (named statement; Milne, p. 107, "proof to be added"). Let $E/K$ be a finite extension of local
fields inside $\Omega$ and $L \supseteq E$ finite, with $L/K$ abelian (Milne: Galois, with $\operatorname{Gal}^{
\mathrm{ab}}$). Then (i) $\phi_{L/K}(\mathrm{Nm}_{E/K}\,a) = \phi_{L/E}(a)$ in $\operatorname{Gal}(L/K) \supseteq
\operatorname{Gal}(L/E)$ for $a \in E^\times$; (ii) $\phi_{L/E}(a) = \mathrm{Ver}(\phi_{L/K}(a))$ for $a \in K^\times$,
where for abelian $\operatorname{Gal}(L/K)$ the transfer to $\operatorname{Gal}(L/E)$ is $g \mapsto g^{[E:K]}$.
Elements of the Galois groups are compared through their action on $L \subseteq \Omega$; $L$ is given both as an
extension of $K$ and of $E$ (same subset of $\Omega$). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 3.2, p. 107 (input)"]
structure Lemma3_2 : Prop where
  compat : ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra K E] [FiniteDimensional K E] [Algebra E Ω] [IsScalarTower K E Ω] [IsSepClosure E Ω]
    (φK : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K))
    (φE : ∀ L : FiniteAbelianExt E Ω, Eˣ →* Gal(L.toField/E)), IsLocalArtinMap φK → IsLocalArtinMap φE →
    ∀ (L : FiniteAbelianExt K Ω) (L' : FiniteAbelianExt E Ω) (hLL' : ∀ x : Ω, x ∈ L.toField ↔ x ∈ L'.toField),
      (∀ (a : Eˣ) (x : Ω) (hx : x ∈ L.toField),
        ((φK L (Units.map (Algebra.norm K (S := E)) a) ⟨x, hx⟩ : L.toField) : Ω) =
          ((φE L' a ⟨x, (hLL' x).1 hx⟩ : L'.toField) : Ω)) ∧
      (∀ (a : Kˣ) (x : Ω) (hx : x ∈ L.toField),
        ((φE L' (Units.map (algebraMap K E).toMonoidHom a) ⟨x, (hLL' x).1 hx⟩ :
            L'.toField) : Ω) = (((φK L a ^ Module.finrank K E) ⟨x, hx⟩ : L.toField) : Ω))

/-- **(3.3)** (p. 108). Let $L \supseteq E \supseteq K$ with $L$ and $E$ abelian over $K$ (Milne: Galois). Then
$\phi_{L/K}(a)|_E = \phi_{E/K}(a)$. For Chapter I's local Artin map this is the compatibility condition. -/
@[kb "milne2020cft" "v4.03, Ch. III, (3.3), p. 108"]
theorem item_3_3 {φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)} (hφ : IsLocalArtinMap φ)
    (E L : FiniteAbelianExt K Ω) (h : E.toField ≤ L.toField) (a : Kˣ) :
    galRestrict h (φ L a) = φ E a :=
  hφ.compat E L h a

/-- The bilinear map $(m, k) \mapsto m^k$ on $L^\times \times \mathbb Z$. -/
noncomputable def unitsIntBil (L : IntermediateField K Ω) : Additive Lˣ →ₗ[ℤ] ℤ →ₗ[ℤ] Additive Lˣ :=
  LinearMap.mk₂ ℤ (fun (m : Additive Lˣ) (k : ℤ) => k • m)
    (fun m m' k => smul_add k m m') (fun c m k => smul_comm k c m)
    (fun m k k' => add_smul k k' m) (fun c m k => mul_smul c k m)

/-- The isomorphism $L^\times \otimes \mathbb Z \to L^\times$ of $\operatorname{Gal}(L/K)$-modules. -/
noncomputable def tensorIntToSelf (L : IntermediateField K Ω) :
    Rep.ofAlgebraAutOnUnits K L ⊗ trivial ℤ Gal(L/K) ℤ ⟶ Rep.ofAlgebraAutOnUnits K L :=
  Rep.ofHom ⟨TensorProduct.lift (unitsIntBil L), fun g => by
    apply TensorProduct.ext'
    intro m k
    change TensorProduct.lift (unitsIntBil L) ((Rep.ofAlgebraAutOnUnits K L).ρ g m ⊗ₜ[ℤ]
        (Representation.trivial ℤ Gal(L/K) ℤ g k)) =
      (Rep.ofAlgebraAutOnUnits K L).ρ g (TensorProduct.lift (unitsIntBil L) (m ⊗ₜ[ℤ] k))
    erw [TensorProduct.lift.tmul, TensorProduct.lift.tmul]
    exact (map_zsmul ((Rep.ofAlgebraAutOnUnits K L).ρ g) k m).symm⟩

/-- $a \in K^\times = H^0(\operatorname{Gal}(L/K), L^\times)$. -/
noncomputable def unitsH0 (L : IntermediateField K Ω) (a : Kˣ) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 0 :=
  (H0Iso (Rep.ofAlgebraAutOnUnits K L)).inv.hom ⟨Additive.ofMul (embUnits L a), fun σ =>
    congrArg Additive.ofMul (gal_smul_embUnits L σ a)⟩

variable (K Ω) in
/-- **Proposition 3.6** (named statement; Milne, p. 109, citing Serre): for a finite abelian $L/K$, a character
$\chi \in \operatorname{Hom}(\operatorname{Gal}(L/K), \mathbb Q/\mathbb Z)$ and $a \in K^\times$,
$\chi(\phi_{L/K}(a)) = \mathrm{inv}_K(a \cup \delta\chi)$, where $\delta\chi \in H^2(G, \mathbb Z)$ is the image of
$\chi$ under $\operatorname{Hom}(G, \mathbb Q/\mathbb Z) = H^1(G, \mathbb Q/\mathbb Z) \xrightarrow{\delta}
H^2(G, \mathbb Z)$, the cup product $H^0(G, L^\times) \times H^2(G, \mathbb Z) \to H^2(G, L^\times \otimes
\mathbb Z) = H^2(G, L^\times)$ is the one of Chapter II, Proposition 1.38, and $\mathrm{inv}_K$ restricted to
$H^2(L/K)$ is $\mathrm{inv}_{L/K}$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Prop. 3.6, p. 109 (input)"]
structure Prop3_6 : Prop where
  formula : ∀ (φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)), IsLocalArtinMap φ →
    ∀ (s : InvariantSystem K Ω) (L : FiniteAbelianExt K Ω) (c : CupProductFamily Gal(L.toField/K))
      (χ : Additive Gal(L.toField/K) →+ QZ) (a : Kˣ),
      χ (Additive.ofMul (φ L a)) =
        s.invK L.toField (((functor ℤ Gal(L.toField/K) 2).map (tensorIntToSelf L.toField)).hom
          (c.cup _ _ 0 2 2 rfl (unitsH0 L.toField a)
            ((δ (seqZQ_shortExact Gal(L.toField/K)) 1 2 rfl).hom
              ((H1IsoOfIsTrivial (seqZQ Gal(L.toField/K)).X₃).inv.hom χ))))

/-- **Lemma 3.7** (p. 109). If $L/K$ is unramified (finite abelian), $\phi_{L/K}$ sends $a \in K^\times$ to
$\mathrm{Frob}^{\mathrm{ord}_K(a)}$: writing $a = u\pi^m$ with $u \in U_K$ ($m = \mathrm{ord}_K(a)$),
$\phi_{L/K}(a) = \sigma^m$ for the Frobenius element $\sigma$. Milne derives it from Proposition 3.6; here it follows
from Chapter I (units act trivially on unramified extensions, `artin_unit_eq_one`, and the Frobenius element is
unique, `UnramifiedInput`). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 3.7, p. 109"]
theorem lemma_3_7 (hU : UnramifiedInput K Ω) {φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}
    (hφ : IsLocalArtinMap φ) (L : FiniteAbelianExt K Ω) (hL : IsUnramifiedExt L.toField)
    {σ : Gal(L.toField/K)} (hσ : IsFrobenius L.toField σ) {π : 𝒪[K]} (hπ : Irreducible π) {u : Kˣ}
    (hu : u ∈ unitGroup K) (m : ℤ) : φ L (u * primeUnit hπ ^ m) = σ ^ m := by
  rw [map_mul, artin_unit_eq_one hU hφ hu L hL, one_mul, map_zpow,
    hU.frobenius_unique L hL _ _ (hφ.frobenius hπ L hL) hσ]

end NumberFieldKB.MilneCFT.Ch3
