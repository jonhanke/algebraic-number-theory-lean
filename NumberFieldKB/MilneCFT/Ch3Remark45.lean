import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Prop43

/-!
# Milne, *Class Field Theory*, Chapter III §4: Remark 4.5

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

Remark 4.5 (p. 114): $\phi_K(b)(a^{1/n}) = (a, b)\, a^{1/n}$. Proof. When $\mu_n \subseteq K$ the Kummer cocycle
$\kappa_\alpha : g \mapsto g\alpha/\alpha$ is a character; with $\chi_\alpha = \log_\zeta \circ \kappa_\alpha$ the cup
product $\delta a \cup \delta b$ is $(\chi_\alpha \cup \delta b)$ pushed along $\mu_n \otimes \mu_n \simeq
\mathbb Z/n \otimes \mu_n$ (`hilbertInv_eq_charKummerPairing`), so by `charKummerPairing_eq` the invariant is
$\chi_\alpha(\phi_K(b))/n$, i.e. $(a,b) = \zeta^{\chi_\alpha(\phi_K(b))}$, which is $\phi_K(b)\alpha/\alpha$.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory MonoidalCategory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT
open TauCeti.ClassFieldTheory

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
variable (n : ℕ) [NeZero n]

section Step2

variable (M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n)

/-- The discrete logarithm $\mu_n(M) \to \mathbb Z/n$ as a map of $\operatorname{Gal}(M/K)$-modules
($\mathbb Z/n$ trivial; $\mu_n(M)$ is trivial when $\mu_n \subseteq K$). -/
noncomputable def muLogHom : muRep n M ⟶ Rep.trivial ℤ Gal(M/K) (ZMod n) :=
  Rep.ofHom ⟨(muLog n M hζ).toIntLinearMap, fun σ => by
    refine LinearMap.ext fun x => ?_
    change muLog n M hζ ((muRep n M).ρ σ x) = muLog n M hζ x
    rw [muRep_trivial n M hζ σ x]⟩

/-- The character $\chi_\alpha = \log_\zeta \circ \kappa_\alpha$ of the Kummer cocycle. -/
noncomputable def kummerChar (α : Mˣ) (hα : ∀ σ : Gal(M/K), σ • α ^ n = α ^ n) :
    Additive Gal(M/K) →+ ZMod n :=
  AddMonoidHom.mk' (fun g => muLog n M hζ (kummerFun n M α hα g.toMul)) (fun g h => by
    have := (mem_cocycles₁_iff _).1 (kummerFun_mem n M α hα) g.toMul h.toMul
    change muLog n M hζ (kummerFun n M α hα (g.toMul * h.toMul)) = _
    rw [this, map_add, muRep_trivial n M hζ, add_comm])

theorem kummerChar_apply (α : Mˣ) (hα : ∀ σ : Gal(M/K), σ • α ^ n = α ^ n) (g : Gal(M/K)) :
    kummerChar n M hζ α hα (Additive.ofMul g) = muLog n M hζ (kummerFun n M α hα g) := rfl

theorem map_kummerClass (α : Mˣ) (hα : ∀ σ : Gal(M/K), σ • α ^ n = α ^ n) :
    ((functor ℤ Gal(M/K) 1).map (muLogHom n M hζ)).hom (kummerClass n M α hα) =
      charClass n M (kummerChar n M hζ α hα) := by
  unfold kummerClass charClass
  rw [functor_map]
  erw [H1π_comp_map_apply]
  rw [H1IsoOfIsTrivial_inv_apply]
  congr 1

theorem logTensor_zmodMu :
    (muLogHom n M hζ ⊗ₘ 𝟙 (muRep n M)) ≫ zmodMu n M = muMu n M hζ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  rfl

theorem hilbertInv_eq_charKummerPairing (s : InvariantSystem K Ω) (M : IntermediateField K Ω)
    [FiniteDimensional K M] [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ n) (α β : Mˣ) (hα : ∀ σ : Gal(M/K), σ • α ^ n = α ^ n)
    (hβ : ∀ σ : Gal(M/K), σ • β ^ n = β ^ n) :
    hilbertInv n s M c hζ α β hα hβ =
      charKummerPairing n s M c (kummerChar n M hζ α hα) β hβ := by
  unfold hilbertInv charKummerPairing
  congr 1
  rw [← map_kummerClass n M hζ α hα]
  have h := c.natural (muLogHom n M hζ) (𝟙 (muRep n M)) 1 1 2 rfl (kummerClass n M α hα)
    (kummerClass n M β hβ)
  have hid : ((functor ℤ Gal(M/K) 1).map (𝟙 (muRep n M))).hom (kummerClass n M β hβ) =
      kummerClass n M β hβ := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [hid] at h
  rw [h, ← logTensor_zmodMu n M hζ, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  rfl

end Step2

section Final

theorem zeta_pow_muLog (M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (x : muRep n M) :
    zetaM M ζ ^ (muLog n M hζ x).val = Additive.toMul (α := Mˣ) x.1 := by
  have h := (zetaM_prim n M hζ).zmodEquivZPowers.apply_symm_apply
    (Additive.ofMul (⟨Additive.toMul (α := Mˣ) x.1, mem_zpowers_zetaM n M hζ x⟩ : Subgroup.zpowers (zetaM M ζ)))
  change (zetaM_prim n M hζ).zmodEquivZPowers (muLog n M hζ x) = _ at h
  rw [← ZMod.natCast_zmod_val (muLog n M hζ x), (zetaM_prim n M hζ).zmodEquivZPowers_apply_coe_nat] at h
  have := congrArg (fun z : Additive (Subgroup.zpowers (zetaM M ζ)) => ((Additive.toMul z : Subgroup.zpowers (zetaM M ζ)) : Mˣ)) h
  simpa using this

theorem gal_smul_eq (M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (α : Mˣ)
    (hα : ∀ σ : Gal(M/K), σ • α ^ n = α ^ n) (g : Gal(M/K)) :
    g • α = zetaM M ζ ^ (kummerChar n M hζ α hα (Additive.ofMul g)).val * α := by
  rw [kummerChar_apply, zeta_pow_muLog]
  change g • α = (g • α) * α⁻¹ * α
  rw [inv_mul_cancel_right]

theorem artin_apply_eq (L : FiniteAbelianExt K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (b : Kˣ) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = TauCeti.ClassFieldTheory.artinMap K b)
    (y : M) (x : L.toField) (hxy : (x : Ω) = (y : Ω)) :
    ((tauCetiArtin L b x : L.toField) : Ω) =
      (((embM M).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ) y : M) : Ω) := by
  have hart : tauCetiArtin L b =
      (embM L.toField).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ) := by
    apply (abelianizationOfEquiv Gal(L.toField/K)).injective
    rw [abelianizationOfEquiv_apply, abelianizationOfEquiv_apply,
      abelianizationOf_tauCetiArtin L (embM L.toField), artinMap_restrict K L.toField (embM L.toField) b σ hσ]
    rfl
  apply (sepEquiv K Ω).injective
  have e1 : ∀ z : L.toField, sepEquiv K Ω (z : Ω) = embM L.toField z := fun _ => rfl
  have e2 : ∀ z : M, sepEquiv K Ω (z : Ω) = embM M z := fun _ => rfl
  rw [e1, e2, hart, AlgHom.restrictNormalHom_commutes, AlgHom.restrictNormalHom_commutes, ← e1, ← e2, hxy]

variable (K Ω) in
/-- **Remark 4.5** (Milne, *CFT*, III, p. 114), proved unconditionally: $\phi_K(b)(a^{1/n}) = (a, b)\,a^{1/n}$.
Every local Artin map is Tau Ceti's (`isLocalArtinMap_unique_unconditional`); with $\chi_\alpha = \log_\zeta \circ
\kappa_\alpha$ one has $\mathrm{inv}(\delta a \cup \delta b) = (\chi_\alpha, b) = \chi_\alpha(\phi_K(b))/n$
(`hilbertInv_eq_charKummerPairing`, `charKummerPairing_eq`), so $(a, b) = \zeta^{\chi_\alpha(\phi_K(b))}$ and
$\phi_K(b)\alpha = \zeta^{\chi_\alpha(\phi_K(b))}\alpha$ by definition of $\chi_\alpha$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Remark 4.5, p. 114"]
theorem remark4_5 : Remark4_5 K Ω := by
  refine ⟨fun φ hφ n _ s M _ _ c ζ hζ a b α β hα hβ L hαL => ?_⟩
  have hφ' : φ = fun L => tauCetiArtin L :=
    isLocalArtinMap_unique_unconditional (hφ := hφ) (hψ := isLocalArtinMap_tauCetiArtin)
  subst hφ'
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap K b)
  set τ := (embM M).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ) with hτ
  set χ := kummerChar n M hζ α (fixed_of_pow_eq n M hα) with hχ
  have h1 := hilbertInv_eq_charKummerPairing n s M c hζ α β (fixed_of_pow_eq n M hα)
    (fixed_of_pow_eq n M hβ)
  have h2 := charKummerPairing_eq n s M c χ β b hβ σ hσ
  have hk := (AddSubgroup.mem_zmultiples_iff.1
    (hilbertInv_mem n s M c hζ α β (fixed_of_pow_eq n M hα) (fixed_of_pow_eq n M hβ))).choose_spec
  set k := (AddSubgroup.mem_zmultiples_iff.1
    (hilbertInv_mem n s M c hζ α β (fixed_of_pow_eq n M hα) (fixed_of_pow_eq n M hβ))).choose with hkdef
  have hsym : hilbertSymbol n s M c hζ hα hβ = ζ ^ k := rfl
  have hkz : ((k : ℤ) : ZMod n) = χ (Additive.ofMul τ) := by
    apply zmodToQZ_injective n
    rw [← h2, ← h1, ← hk, zmodToQZ, ZMod.lift_coe]
    rfl
  have hζk : ζ ^ k = ζ ^ (((χ (Additive.ofMul τ)).val : ℕ) : ℤ) := by
    have h3 : ((k : ℤ) : ZMod n) = ((((χ (Additive.ofMul τ)).val : ℕ) : ℤ) : ZMod n) := by
      rw [hkz]; simp
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h3
    have h4 := (hζ.zpow_eq_one_iff_dvd _).2 h3
    rw [zpow_sub, mul_inv_eq_one] at h4
    exact h4.symm
  have hτα := gal_smul_eq n M hζ α (fixed_of_pow_eq n M hα) τ
  have hΩ := artin_apply_eq L M b σ hσ (α : M) ⟨((α : M) : Ω), hαL⟩ rfl
  rw [hΩ, hsym, hζk, zpow_natCast]
  change (((τ • α : Mˣ) : M) : Ω) = _
  rw [hτα]
  simp [zetaM]
  rfl

end Final

end NumberFieldKB.MilneCFT.Ch3

