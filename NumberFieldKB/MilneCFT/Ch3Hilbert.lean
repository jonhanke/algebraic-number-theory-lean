import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Stable
import NumberFieldKB.MilneCFT.Ch3Ramified
import NumberFieldKB.MilneCFT.Ch3Unramified
import NumberFieldKB.MilneCFT.Ch3Kummer
import NumberFieldKB.MilneCFT.Ch2Cup

/-!
# Milne, *Class Field Theory*, Chapter III §4: the Hilbert symbol

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Milne works with the absolute Galois group $G = \operatorname{Gal}(K^{\mathrm{al}}/K)$; here everything is at
finite level, in $\operatorname{Gal}(M/K)$ for a finite Galois $M/K$ containing the $n$-th roots used (Milne's
classes are inflated from such levels). Cup products are a family `c : CupProductFamily` with Milne's properties
(Chapter II, Proposition 1.38: there is exactly one), and $\mathrm{inv}$ is the system of invariant maps of
Theorem 2.1.

* `muRep` ($\mu_n(M)$), `kummerClass` ($\delta b \in H^1(\operatorname{Gal}(M/K), \mu_n)$, the class of
  $\sigma \mapsto \sigma\beta/\beta$), `charClass`.
* `charKummerPairing` — the pairing $(\chi, b) = \mathrm{inv}(\chi \cup \delta b)$ of Steps 2–3 (p. 112).
* `hilbertSymbol` — the Hilbert symbol $(a, b) \in \mu_n(K)$ of Step 4 (p. 113), with `hilbertInv_mem`
  ($\mathrm{inv}(\delta a \cup \delta b) \in \frac1n\mathbb Z/\mathbb Z$).
* `Thm4_4`, `Prop4_3`, `Remark4_5`, `Remark4_6` — named statements; `prop_4_1` — Proposition 4.1, proved from
  Theorem 4.4 (c), (d) and Kummer theory (`kummer_adjoin`).
-/

open scoped ValuativeRel
namespace NumberFieldKB.MilneCFT.Ch3
open CategoryTheory MonoidalCategory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

/-- $n \cdot x = 0$ in $H^r(G, A)$ when $n$ kills $A$. -/
theorem nsmul_groupCohomology_eq_zero {G : Type} [Group G] (A : Rep ℤ G) (n : ℕ) (hA : ∀ a : A, n • a = 0)
    (r : ℕ) (x : groupCohomology A r) : n • x = 0 := by
  have h0 : ((n : ℤ) • 𝟙 A : A ⟶ A) = 0 := by
    apply Rep.hom_ext; ext a
    change (n : ℤ) • a = 0
    rw [natCast_zsmul]; exact hA a
  have h1 : (functor ℤ G r).map ((n : ℤ) • 𝟙 A) = (n : ℤ) • 𝟙 _ := by
    change (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) r).map
        ((cochainsFunctor ℤ G).map ((n : ℤ) • 𝟙 A)) = _
    rw [Functor.map_zsmul, Functor.map_zsmul, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  rw [h0, Functor.map_zero] at h1
  have := congrArg (fun f => f.hom x) h1
  rw [← natCast_zsmul]
  exact this.symm

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

variable (n : ℕ)

theorem rootsOfUnity_stable (M : IntermediateField K Ω) :
    ∀ (σ : Gal(M/K)), ∀ x ∈ unitsSub M (rootsOfUnity n M),
      (Rep.ofAlgebraAutOnUnits K M).ρ σ x ∈ unitsSub M (rootsOfUnity n M) := by
  intro σ x hx
  change Additive.toMul (α := Mˣ) x ∈ rootsOfUnity n M at hx
  change (σ • Additive.toMul (α := Mˣ) x) ∈ rootsOfUnity n M
  rw [mem_rootsOfUnity] at hx ⊢
  rw [← smul_pow', hx, smul_one]

/-- The $\operatorname{Gal}(M/K)$-module $\mu_n(M)$ of $n$-th roots of unity in $M$. -/
noncomputable abbrev muRep (M : IntermediateField K Ω) : Rep ℤ Gal(M/K) :=
  stableRep (Rep.ofAlgebraAutOnUnits K M) (unitsSub M (rootsOfUnity n M)) (rootsOfUnity_stable n M)

/-- The Kummer cocycle $\sigma \mapsto \sigma\beta/\beta$ of $\beta \in M^\times$ with $\beta^n \in K$. -/
noncomputable def kummerFun (M : IntermediateField K Ω) (β : Mˣ) (hβ : ∀ σ : Gal(M/K), σ • β ^ n = β ^ n) :
    Gal(M/K) → muRep n M := fun σ =>
  ⟨Additive.ofMul ((σ • β) * β⁻¹), by
    change ((σ • β) * β⁻¹ : Mˣ) ∈ rootsOfUnity n M
    rw [mem_rootsOfUnity, mul_pow, ← smul_pow', hβ σ, inv_pow, mul_inv_cancel]⟩

theorem kummerFun_mem (M : IntermediateField K Ω) (β : Mˣ) (hβ : ∀ σ : Gal(M/K), σ • β ^ n = β ^ n) :
    kummerFun n M β hβ ∈ cocycles₁ (muRep n M) := by
  rw [mem_cocycles₁_iff]
  intro σ τ
  apply Subtype.ext
  apply Additive.toMul.injective
  change ((σ * τ) • β) * β⁻¹ = (σ • ((τ • β) * β⁻¹)) * ((σ • β) * β⁻¹)
  rw [mul_smul, smul_mul', smul_inv']
  group

/-- The Kummer class $\delta\beta \in H^1(\operatorname{Gal}(M/K), \mu_n)$ of $b = \beta^n \in K^\times$. -/
noncomputable def kummerClass (M : IntermediateField K Ω) (β : Mˣ) (hβ : ∀ σ : Gal(M/K), σ • β ^ n = β ^ n) :
    H1 (muRep n M) :=
  (H1π (muRep n M)).hom ⟨kummerFun n M β hβ, kummerFun_mem n M β hβ⟩

/-- $\mu_n(M)$ is killed by $n$. -/
theorem muRep_nsmul (M : IntermediateField K Ω) (x : muRep n M) : n • x = 0 := by
  apply Subtype.ext
  apply Additive.toMul.injective
  change (Additive.toMul (α := Mˣ) x.1) ^ n = 1
  exact (mem_rootsOfUnity _ _).1 x.2

/-- The action of $\mathbb Z/n$ on $\mu_n(M)$: $k \mapsto (\zeta \mapsto \zeta^k)$. -/
noncomputable def zmodAct (M : IntermediateField K Ω) : ZMod n →+ (muRep n M →+ muRep n M) :=
  ZMod.lift n ⟨zmultiplesHom _ (AddMonoidHom.id _), by
    ext x; simp [muRep_nsmul n M x]⟩

/-- The bilinear map $(k, \zeta) \mapsto \zeta^k$. -/
noncomputable def zmodMuBil (M : IntermediateField K Ω) : ZMod n →ₗ[ℤ] muRep n M →ₗ[ℤ] muRep n M :=
  LinearMap.mk₂ ℤ (fun (k : ZMod n) (x : muRep n M) => zmodAct n M k x)
    (fun k k' x => by simp) (fun c k x => by rw [map_zsmul]; rfl)
    (fun k x x' => by simp) (fun c k x => map_zsmul _ c x)

/-- The map $\mathbb Z/n \otimes \mu_n \to \mu_n$, $k \otimes \zeta \mapsto \zeta^k$, of
$\operatorname{Gal}(M/K)$-modules ($\mathbb Z/n$ with trivial action). -/
noncomputable def zmodMu (M : IntermediateField K Ω) :
    Rep.trivial ℤ Gal(M/K) (ZMod n) ⊗ muRep n M ⟶ muRep n M :=
  Rep.ofHom ⟨TensorProduct.lift (zmodMuBil n M), fun σ => by
    apply TensorProduct.ext'
    intro k x
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective k
    change TensorProduct.lift (zmodMuBil n M) ((Representation.trivial ℤ Gal(M/K) (ZMod n) σ (m : ZMod n)) ⊗ₜ
      ((muRep n M).ρ σ x)) = (muRep n M).ρ σ (TensorProduct.lift (zmodMuBil n M) ((m : ZMod n) ⊗ₜ x))
    simp only [Representation.trivial_apply]
    simp [zmodMuBil, zmodAct, ZMod.lift_coe, map_zsmul]⟩

/-- The class of a character $\chi : \operatorname{Gal}(M/K) \to \mathbb Z/n$ in
$H^1(\operatorname{Gal}(M/K), \mathbb Z/n) \simeq \operatorname{Hom}(\operatorname{Gal}(M/K), \mathbb Z/n)$. -/
noncomputable def charClass (M : IntermediateField K Ω) (χ : Additive Gal(M/K) →+ ZMod n) :
    H1 (Rep.trivial ℤ Gal(M/K) (ZMod n)) :=
  (H1IsoOfIsTrivial (Rep.trivial ℤ Gal(M/K) (ZMod n))).inv.hom χ

/-- **The pairing $(\chi, b)$** (Milne, p. 112, Steps 2–3, definition in prose), at finite level: for a finite
Galois $M/K$, a character $\chi : \operatorname{Gal}(M/K) \to \mathbb Z/n$ and $b = \beta^n$ with $\beta \in M$,
$(\chi, b) = \mathrm{inv}_{M/K}(\chi \cup \delta b) \in \frac1n\mathbb Z/\mathbb Z$, where $\delta b \in
H^1(\operatorname{Gal}(M/K), \mu_n)$ is the Kummer class $\sigma \mapsto \sigma\beta/\beta$, the cup product
lands in $H^2(\mathbb Z/n \otimes \mu_n) = H^2(\mu_n)$, and $H^2(\mu_n) \to H^2(M/K)$. Milne works with the
absolute Galois group; at finite level $M$ must contain the $n$-th roots used. The cup product is any family `c`
with Milne's properties (unique by Chapter II, Proposition 1.38). -/
@[kb "milne2020cft" "v4.03, Ch. III, §4, Steps 2–3, the pairing (χ, b), p. 112"]
noncomputable def charKummerPairing (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) (χ : Additive Gal(M/K) →+ ZMod n) (β : Mˣ)
    (hβ : ∀ σ : Gal(M/K), σ • β ^ n = β ^ n) : QZ :=
  s.invK M ((functor ℤ Gal(M/K) 2).map (zmodMu n M ≫ stableIncl _ _ _)
    (c.cup _ _ 1 1 2 rfl (charClass n M χ) (kummerClass n M β hβ)))

section Symbol

variable [NeZero n]

/-- The image of a primitive $n$-th root of unity $\zeta \in K$ in $M$. -/
noncomputable def zetaM (M : IntermediateField K Ω) (ζ : Kˣ) : Mˣ := Units.map (algebraMap K M).toMonoidHom ζ

theorem zetaM_prim (M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (zetaM M ζ) n :=
  hζ.map_of_injective (Units.map_injective (algebraMap K M).injective)

theorem mem_zpowers_zetaM (M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (x : muRep n M) :
    Additive.toMul (α := Mˣ) x.1 ∈ Subgroup.zpowers (zetaM M ζ) := by
  rw [(zetaM_prim n M hζ).zpowers_eq]
  exact x.2

/-- If $K$ contains a primitive $n$-th root of unity, $\operatorname{Gal}(M/K)$ acts trivially on $\mu_n(M)$. -/
theorem muRep_trivial (M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (σ : Gal(M/K))
    (x : muRep n M) : (muRep n M).ρ σ x = x := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_zetaM n M hζ x)
  apply Subtype.ext
  apply Additive.toMul.injective
  change σ • Additive.toMul (α := Mˣ) x.1 = Additive.toMul (α := Mˣ) x.1
  rw [← hi, smul_zpow']
  congr 1
  apply Units.ext
  exact σ.commutes _

/-- The discrete logarithm $\mu_n(M) \to \mathbb Z/n$ to the base $\zeta$. -/
noncomputable def muLog (M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) : muRep n M →+ ZMod n where
  toFun x := (zetaM_prim n M hζ).zmodEquivZPowers.symm
    (Additive.ofMul ⟨Additive.toMul (α := Mˣ) x.1, mem_zpowers_zetaM n M hζ x⟩)
  map_zero' := by
    rw [← map_zero (zetaM_prim n M hζ).zmodEquivZPowers.symm]
    rfl
  map_add' x y := by
    rw [← map_add]
    rfl

/-- The pairing $\mu_n \otimes \mu_n \to \mu_n$, $\zeta^i \otimes \zeta^j \mapsto \zeta^{ij}$. -/
noncomputable def muMuBil (M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) :
    muRep n M →ₗ[ℤ] muRep n M →ₗ[ℤ] muRep n M :=
  LinearMap.mk₂ ℤ (fun x y => zmodAct n M (muLog n M hζ x) y)
    (fun x x' y => by simp) (fun c x y => by erw [map_zsmul, map_zsmul]; rfl)
    (fun x y y' => by simp) (fun c x y => map_zsmul _ c y)

/-- The isomorphism $\mu_n \otimes \mu_n \to \mu_n$ of Milne's Step 4 (depending on $\zeta$), as a map of
$\operatorname{Gal}(M/K)$-modules. -/
noncomputable def muMu (M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) :
    muRep n M ⊗ muRep n M ⟶ muRep n M :=
  Rep.ofHom ⟨TensorProduct.lift (muMuBil n M hζ), fun σ => by
    apply TensorProduct.ext'
    intro x y
    change TensorProduct.lift (muMuBil n M hζ) (((muRep n M).ρ σ x) ⊗ₜ ((muRep n M).ρ σ y)) =
      (muRep n M).ρ σ (TensorProduct.lift (muMuBil n M hζ) (x ⊗ₜ y))
    rw [muRep_trivial n M hζ σ x, muRep_trivial n M hζ σ y, muRep_trivial n M hζ σ]⟩

/-- The invariant of the Hilbert symbol: $\mathrm{inv}_{M/K}$ of the image of $\delta a \cup \delta b$ in
$H^2(M/K)$, an element of $\frac1n\mathbb Z/\mathbb Z$. -/
noncomputable def hilbertInv (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (α β : Mˣ)
    (hα : ∀ σ : Gal(M/K), σ • α ^ n = α ^ n) (hβ : ∀ σ : Gal(M/K), σ • β ^ n = β ^ n) : QZ :=
  s.invK M ((functor ℤ Gal(M/K) 2).map (muMu n M hζ ≫ stableIncl _ _ _)
    (c.cup _ _ 1 1 2 rfl (kummerClass n M α hα) (kummerClass n M β hβ)))

theorem hilbertInv_mem (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (α β : Mˣ)
    (hα : ∀ σ : Gal(M/K), σ • α ^ n = α ^ n) (hβ : ∀ σ : Gal(M/K), σ • β ^ n = β ^ n) :
    hilbertInv n s M c hζ α β hα hβ ∈ qzOver n := by
  apply mem_qzOver_of_nsmul n (Nat.pos_of_neZero n)
  set z := c.cup _ _ 1 1 2 rfl (kummerClass n M α hα) (kummerClass n M β hβ)
  have h := nsmul_groupCohomology_eq_zero (muRep n M) n (muRep_nsmul n M) 2
    (((functor ℤ Gal(M/K) 2).map (muMu n M hζ)).hom z)
  show n • s.invK M (((functor ℤ Gal(M/K) 2).map (muMu n M hζ ≫ stableIncl _ _ _)).hom z) = 0
  rw [Functor.map_comp]
  change n • s.invK M (((functor ℤ Gal(M/K) 2).map (stableIncl _ _ _)).hom
    (((functor ℤ Gal(M/K) 2).map (muMu n M hζ)).hom z)) = 0
  set w := ((functor ℤ Gal(M/K) 2).map (muMu n M hζ)).hom z
  have h2 := congrArg (((functor ℤ Gal(M/K) 2).map (stableIncl _ _ _)).hom) h
  exact ((map_nsmul (s.invK M) n _).symm.trans
    (congrArg (s.invK M) (((map_nsmul _ n w).symm.trans h2).trans (map_zero _)))).trans (map_zero _)

theorem fixed_of_pow_eq (M : IntermediateField K Ω) {a : Kˣ} {α : Mˣ} (hα : α ^ n = embUnits M a)
    (σ : Gal(M/K)) : σ • α ^ n = α ^ n := by
  rw [hα, gal_smul_embUnits]

/-- **The Hilbert symbol** $(a, b) \in \mu_n(K)$ (Milne, p. 113, definition in prose, Step 4), at finite level:
$K$ contains a primitive $n$-th root of unity $\zeta$, $M/K$ is finite Galois and contains $n$-th roots $\alpha$,
$\beta$ of $a$, $b$; the cup product $\delta a \cup \delta b \in H^2(\operatorname{Gal}(M/K), \mu_n \otimes
\mu_n)$ of the Kummer classes, mapped by $\mu_n \otimes \mu_n \simeq \mu_n$ ($\zeta^i \otimes \zeta^j \mapsto
\zeta^{ij}$) to $H^2(\operatorname{Gal}(M/K), \mu_n) \to H^2(M/K)$, has invariant $k/n$; the symbol is
$\zeta^k$. -/
@[kb "milne2020cft" "v4.03, Ch. III, §4, Step 4, the Hilbert symbol (a,b), p. 113"]
noncomputable def hilbertSymbol (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b : Kˣ} {α β : Mˣ}
    (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b) : Kˣ :=
  ζ ^ (AddSubgroup.mem_zmultiples_iff.1
    (hilbertInv_mem n s M c hζ α β (fixed_of_pow_eq n M hα) (fixed_of_pow_eq n M hβ))).choose

end Symbol

variable (K Ω) in
/-- **Theorem 4.4** (named statement; Milne, p. 113), at finite level. Let $K$ contain a primitive $n$-th root of
unity $\zeta$. The Hilbert symbol (`hilbertSymbol`, computed in any finite Galois $M/K$ containing the $n$-th roots
used) satisfies: (a) it is bimultiplicative; (b) it is skew-symmetric, $(b, a) = (a, b)^{-1}$; (c) it is
nondegenerate: if $(a, b) = 1$ for all $b$ then $a \in K^{\times n}$, and if $(a, b) = 1$ for all $a$ then
$b \in K^{\times n}$; (d) $(a, b) = 1$ iff $b$ is a norm from $K[\sqrt[n]{a}]$. In (c), "for all $b$" ranges over all
$M$ and all $n$-th roots in $M$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 4.4, p. 113 (input)"]
structure Thm4_4 : Prop where
  mul_left : ∀ (n : ℕ) [NeZero n] (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a a' b : Kˣ}
    {α α' β : Mˣ} (hα : α ^ n = embUnits M a) (hα' : α' ^ n = embUnits M a') (hβ : β ^ n = embUnits M b),
    hilbertSymbol n s M c hζ (a := a * a') (α := α * α') (by rw [mul_pow, hα, hα', map_mul]) hβ =
      hilbertSymbol n s M c hζ hα hβ * hilbertSymbol n s M c hζ hα' hβ
  mul_right : ∀ (n : ℕ) [NeZero n] (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b b' : Kˣ}
    {α β β' : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b) (hβ' : β' ^ n = embUnits M b'),
    hilbertSymbol n s M c hζ hα (b := b * b') (β := β * β') (by rw [mul_pow, hβ, hβ', map_mul]) =
      hilbertSymbol n s M c hζ hα hβ * hilbertSymbol n s M c hζ hα hβ'
  skew : ∀ (n : ℕ) [NeZero n] (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b : Kˣ}
    {α β : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b),
    hilbertSymbol n s M c hζ hβ hα = (hilbertSymbol n s M c hζ hα hβ)⁻¹
  nondeg_left : ∀ (n : ℕ) [NeZero n] (s : InvariantSystem K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (a : Kˣ),
    (∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] (c : CupProductFamily Gal(M/K))
      (b : Kˣ) (α β : Mˣ) (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b),
      hilbertSymbol n s M c hζ hα hβ = 1) → ∃ x : Kˣ, x ^ n = a
  nondeg_right : ∀ (n : ℕ) [NeZero n] (s : InvariantSystem K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (b : Kˣ),
    (∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] (c : CupProductFamily Gal(M/K))
      (a : Kˣ) (α β : Mˣ) (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b),
      hilbertSymbol n s M c hζ hα hβ = 1) → ∃ x : Kˣ, x ^ n = b
  norm : ∀ (n : ℕ) [NeZero n] (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b : Kˣ}
    {α β : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b)
    [FiniteDimensional K (IntermediateField.adjoin K {((α : M) : Ω)})],
    hilbertSymbol n s M c hζ hα hβ = 1 ↔ b ∈ normGroup (IntermediateField.adjoin K {((α : M) : Ω)})

/-- **Proposition 4.1** (p. 110). Let $K$ be a local field containing a primitive $n$-th root of $1$. Any element of
$K^\times$ that is a norm from every cyclic extension of $K$ of degree dividing $n$ is an $n$-th power. Proved from
Theorem 4.4 (c), (d) (named), as in Milne, with Kummer theory (`kummer_adjoin`). -/
@[kb "milne2020cft" "v4.03, Ch. III, Prop. 4.1, p. 110"]
theorem prop_4_1 (h44 : Thm4_4 K Ω) (s : InvariantSystem K Ω) {n : ℕ} [NeZero n] {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ n) (b : Kˣ)
    (hb : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L], IsCyclic Gal(L/K) →
      Module.finrank K L ∣ n → b ∈ normGroup L) :
    ∃ x : Kˣ, x ^ n = b := by
  refine h44.nondeg_right n s hζ b fun M _ _ c a α β hα hβ => ?_
  have hα0 : ((α : M) : Ω) ≠ 0 := by simp
  have hαK : ((α : M) : Ω) ^ n ∈ Set.range (algebraMap K Ω) := by
    refine ⟨a, ?_⟩
    have := congrArg (fun u : Mˣ => ((u : M) : Ω)) hα
    simp only [Units.val_pow_eq_pow_val, IntermediateField.coe_pow] at this
    rw [this]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := kummer_adjoin hζ hα0 hαK
  exact (h44.norm n s M c hζ hα hβ).2 (hb _ h3 h4)

variable (K Ω) in
/-- **Proposition 4.3** (named statement; Milne, p. 112): the left kernel of the pairing $(\chi, b)$ is zero. At
finite level: if $M/K$ is finite Galois and contains an $n$-th root of every $b \in K^\times$ ($n \ne 0$ in $K$),
and $(\chi, b) = 0$ for all $b$, then $\chi = 0$. (Milne's proof: $(\chi, b) = \chi(\phi_K(b))$, Proposition 3.6,
and the image of the local Artin map is dense.) -/
@[kb "milne2020cft" "v4.03, Ch. III, Prop. 4.3, p. 112 (input)"]
structure Prop4_3 : Prop where
  left_kernel : ∀ (n : ℕ) [NeZero n], (n : K) ≠ 0 → ∀ (s : InvariantSystem K Ω) (M : IntermediateField K Ω)
    [FiniteDimensional K M] [IsGalois K M] (c : CupProductFamily Gal(M/K)),
    (∀ b : Kˣ, ∃ β : Mˣ, β ^ n = embUnits M b) → ∀ χ : Additive Gal(M/K) →+ ZMod n,
    (∀ (b : Kˣ) (β : Mˣ) (hβ : β ^ n = embUnits M b),
      charKummerPairing n s M c χ β (fixed_of_pow_eq n M hβ) = 0) → χ = 0

variable (K Ω) in
/-- **Remark 4.6** (named statement; Milne, p. 114), first part: the pairing $(\chi, b)$ of Step 2 is nondegenerate;
the right kernel is zero as well: if $(\chi, b) = 0$ for every character $\chi$ then $b \in K^{\times n}$ (finite
level as in `Prop4_3`). (Milne deduces it from the existence theorem: $K^\times/K^{\times n}$ and
$\operatorname{Hom}(G, \mathbb Z/n)$ have the same order. The second part, Poitou–Tate duality for every finite
$G$-module, is not formalized: it needs cohomology of the absolute Galois group with arbitrary finite coefficients.)

**Statement correction (2026-11-05).** Milne's pairing is on the absolute Galois group, where
every character of order dividing $n$ is seen. At finite level the earlier version (hypothesis only: $M$ contains an
$n$-th root of every $b \in K^\times$) was false: for $K = \mathbb Q_5$, $n = 3$, $M = \mathbb Q_5(\zeta_3,
\sqrt[3]{5})$, every element of $K^\times$ has a cube root in $M$ (units of $\mathbb Z_5$ are cubes), but
$\operatorname{Gal}(M/K) \simeq S_3$ has no nonzero character to $\mathbb Z/3$, so the hypothesis on $b = 5$ holds
vacuously while $5$ is not a cube. The corrected statement also assumes that $M$ contains every finite abelian
extension of $K$ of exponent dividing $n$ (so that $\operatorname{Hom}(\operatorname{Gal}(M/K), \mathbb Z/n) =
\operatorname{Hom}(G_K, \mathbb Z/n)$), which is the finite-level form of Milne's statement. -/
@[kb "milne2020cft" "v4.03, Ch. III, Remark 4.6, p. 114 (input)"]
structure Remark4_6 : Prop where
  right_kernel : ∀ (n : ℕ) [NeZero n], (n : K) ≠ 0 → ∀ (s : InvariantSystem K Ω) (M : IntermediateField K Ω)
    [FiniteDimensional K M] [IsGalois K M] (c : CupProductFamily Gal(M/K)),
    (∀ b : Kˣ, ∃ β : Mˣ, β ^ n = embUnits M b) →
    (∀ L : FiniteAbelianExt K Ω, (∀ σ : Gal(L.toField/K), σ ^ n = 1) → L.toField ≤ M) →
    ∀ (b : Kˣ) (β : Mˣ) (hβ : β ^ n = embUnits M b),
    (∀ χ : Additive Gal(M/K) →+ ZMod n, charKummerPairing n s M c χ β (fixed_of_pow_eq n M hβ) = 0) →
      ∃ x : Kˣ, x ^ n = b

variable (K Ω) in
/-- **Remark 4.5** (named statement; Milne, p. 114): the Hilbert symbol and the local Artin map are related by
$\phi_K(b)(a^{1/n}) = (a, b)\,a^{1/n}$. Stated as Milne writes it, for a local Artin map in Chapter I's sense and the
symbol of `hilbertSymbol`, for $a^{1/n} = \alpha$ in a finite abelian $L \subseteq M$ (Milne leaves the proof, "an
exercise in cup-products starting from Proposition 3.6", to the reader; the sign conventions are his). -/
@[kb "milne2020cft" "v4.03, Ch. III, Remark 4.5, p. 114 (input)"]
structure Remark4_5 : Prop where
  artin_hilbert : ∀ (φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)), IsLocalArtinMap φ →
    ∀ (n : ℕ) [NeZero n] (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
      [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b : Kˣ}
      {α β : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b) (L : FiniteAbelianExt K Ω)
      (hαL : ((α : M) : Ω) ∈ L.toField),
      ((φ L b ⟨((α : M) : Ω), hαL⟩ : L.toField) : Ω) =
        algebraMap K Ω (hilbertSymbol n s M c hζ hα hβ : K) * ((α : M) : Ω)

end NumberFieldKB.MilneCFT.Ch3
