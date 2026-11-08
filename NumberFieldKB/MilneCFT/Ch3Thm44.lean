import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Remark45
import NumberFieldKB.MilneCFT.Ch3Remark46
import NumberFieldKB.MilneCFT.Ch2CupProps
import NumberFieldKB.MilneCFT.LocalCFT.Consequences

/-!
# Milne, *Class Field Theory*, Chapter III, Theorem 4.4: the Hilbert symbol

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

Key formula (`hilbertSymbol_eq_artin`): for any representative $\sigma \in G_K$ of the Artin symbol of $b$, with
$\tau = \sigma|_M$, $(a, b) = \zeta^{\chi_\alpha(\tau)}$ (from Remark 4.5). Then (a) bimultiplicativity follows from
additivity of $\chi_\alpha$ in $\alpha$ and in $\tau$; (b) skew-symmetry from graded commutativity of the cup product
(Proposition 1.39) and the symmetry of $\mu_n \otimes \mu_n \to \mu_n$; (d) from $\chi_\alpha(\tau) = 0 \iff \tau\alpha
= \alpha$ and $\ker\phi_{K(\alpha)} = \mathrm{Nm}$; (c) from the Artin symbols exhausting $\operatorname{Gal}(K(\alpha)/K)$
and Galois theory, the second half by skew-symmetry.
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

section ZetaVal

variable {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n)
include hζ

theorem zpow_eq_val {k : ℤ} {z : ZMod n} (h : (k : ZMod n) = z) : ζ ^ k = ζ ^ z.val := by
  have h3 : ((k : ℤ) : ZMod n) = ((((z).val : ℕ) : ℤ) : ZMod n) := by rw [h]; simp
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h3
  have h4 := (hζ.zpow_eq_one_iff_dvd _).2 h3
  rw [zpow_sub, mul_inv_eq_one] at h4
  exact h4.symm.trans (zpow_natCast _ _)

theorem zeta_val_add (x y : ZMod n) : ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  have := zpow_eq_val n hζ (k := (x.val : ℤ) + (y.val : ℤ)) (z := x + y) (by push_cast; simp)
  rw [zpow_add, zpow_natCast, zpow_natCast] at this
  exact this.symm

theorem zeta_val_neg (x : ZMod n) : ζ ^ (-x).val = (ζ ^ x.val)⁻¹ := by
  have := zpow_eq_val n hζ (k := -(x.val : ℤ)) (z := -x) (by push_cast; simp)
  rw [zpow_neg, zpow_natCast] at this
  exact this.symm

end ZetaVal

/-- If $\mathrm{inv} = z/n$ then the Hilbert symbol is $\zeta^{z}$. -/
theorem hilbertSymbol_eq_of (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b : Kˣ}
    {α β : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b) (z : ZMod n)
    (hz : hilbertInv n s M c hζ α β (fixed_of_pow_eq n M hα) (fixed_of_pow_eq n M hβ) = zmodToQZ n z) :
    hilbertSymbol n s M c hζ hα hβ = ζ ^ z.val := by
  have hk := (AddSubgroup.mem_zmultiples_iff.1
    (hilbertInv_mem n s M c hζ α β (fixed_of_pow_eq n M hα) (fixed_of_pow_eq n M hβ))).choose_spec
  set k := (AddSubgroup.mem_zmultiples_iff.1
    (hilbertInv_mem n s M c hζ α β (fixed_of_pow_eq n M hα) (fixed_of_pow_eq n M hβ))).choose with hkdef
  have hsym : hilbertSymbol n s M c hζ hα hβ = ζ ^ k := rfl
  have h1 : zmodToQZ n ((k : ℤ) : ZMod n) =
      hilbertInv n s M c hζ α β (fixed_of_pow_eq n M hα) (fixed_of_pow_eq n M hβ) := by
    rw [← hk, zmodToQZ, ZMod.lift_coe]
    rfl
  have hkz : ((k : ℤ) : ZMod n) = z := zmodToQZ_injective n (h1.trans hz)
  rw [hsym]
  exact zpow_eq_val n hζ hkz

/-- **Key formula** (from Remark 4.5): $(a, b) = \zeta^{\chi_\alpha(\tau)}$, $\tau = \sigma|_M$ for any
representative $\sigma$ of the Artin symbol of $b$. -/
theorem hilbertSymbol_eq_artin (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b : Kˣ}
    {α β : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = TauCeti.ClassFieldTheory.artinMap K b) :
    hilbertSymbol n s M c hζ hα hβ =
      ζ ^ (kummerChar n M hζ α (fixed_of_pow_eq n M hα)
        (Additive.ofMul ((embM M).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ)))).val := by
  apply hilbertSymbol_eq_of
  rw [hilbertInv_eq_charKummerPairing, charKummerPairing_eq n s M c _ β b hβ σ hσ]

/-- $\tau\alpha = \zeta^{\chi_\alpha(\tau)}\alpha$ (restatement of `gal_smul_eq`) gives: the symbol is trivial iff
$\tau\alpha = \alpha$. -/
theorem hilbertSymbol_eq_one_iff (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b : Kˣ}
    {α β : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = TauCeti.ClassFieldTheory.artinMap K b) :
    hilbertSymbol n s M c hζ hα hβ = 1 ↔
      ((embM M).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ)) • α = α := by
  have e : ∀ m : ℕ, zetaM M ζ ^ m = 1 ↔ ζ ^ m = 1 := fun m => by
    have : zetaM M ζ ^ m = Units.map (algebraMap K M).toMonoidHom (ζ ^ m) :=
      (map_pow (Units.map (algebraMap K M).toMonoidHom) ζ m).symm
    rw [this, ← map_one (Units.map (algebraMap K M).toMonoidHom)]
    exact (Units.map_injective (algebraMap K M).injective).eq_iff
  rw [hilbertSymbol_eq_artin n s M c hζ hα hβ σ hσ,
    gal_smul_eq n M hζ α (fixed_of_pow_eq n M hα), mul_eq_right, e]

theorem hilbertInv_eq_zmod (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b : Kˣ}
    {α β : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = TauCeti.ClassFieldTheory.artinMap K b) :
    hilbertInv n s M c hζ α β (fixed_of_pow_eq n M hα) (fixed_of_pow_eq n M hβ) =
      zmodToQZ n (kummerChar n M hζ α (fixed_of_pow_eq n M hα)
        (Additive.ofMul ((embM M).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ)))) := by
  rw [hilbertInv_eq_charKummerPairing, charKummerPairing_eq n s M c _ β b hβ σ hσ]

theorem hilbertSymbol_mul_right (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b b' : Kˣ}
    {α β β' : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b) (hβ' : β' ^ n = embUnits M b') :
    hilbertSymbol n s M c hζ hα (b := b * b') (β := β * β') (by rw [mul_pow, hβ, hβ', map_mul]) =
      hilbertSymbol n s M c hζ hα hβ * hilbertSymbol n s M c hζ hα hβ' := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap K b)
  obtain ⟨σ', hσ'⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap K b')
  have hσσ : ((σ * σ' : Field.absoluteGaloisGroup K) : Field.absoluteGaloisGroupAbelianization K) =
      TauCeti.ClassFieldTheory.artinMap K (b * b') := by
    rw [map_mul, ← hσ, ← hσ']; rfl
  rw [hilbertSymbol_eq_artin n s M c hζ hα _ (σ * σ') hσσ, hilbertSymbol_eq_artin n s M c hζ hα hβ σ hσ,
    hilbertSymbol_eq_artin n s M c hζ hα hβ' σ' hσ', map_mul, map_mul, ofMul_mul, map_add,
    zeta_val_add n hζ]

theorem kummerChar_mul (M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (α α' : Mˣ)
    (hα : ∀ σ : Gal(M/K), σ • α ^ n = α ^ n) (hα' : ∀ σ : Gal(M/K), σ • α' ^ n = α' ^ n)
    (hαα' : ∀ σ : Gal(M/K), σ • (α * α') ^ n = (α * α') ^ n) (g : Additive Gal(M/K)) :
    kummerChar n M hζ (α * α') hαα' g = kummerChar n M hζ α hα g + kummerChar n M hζ α' hα' g := by
  have : kummerFun n M (α * α') hαα' g.toMul = kummerFun n M α hα g.toMul + kummerFun n M α' hα' g.toMul := by
    apply Subtype.ext
    apply Additive.toMul.injective
    change (g.toMul • (α * α')) * (α * α')⁻¹ = ((g.toMul • α) * α⁻¹) * ((g.toMul • α') * α'⁻¹)
    rw [smul_mul', mul_inv_rev, mul_comm α'⁻¹ α⁻¹]
    exact mul_mul_mul_comm _ _ _ _
  change muLog n M hζ (kummerFun n M (α * α') hαα' g.toMul) = muLog n M hζ (kummerFun n M α hα g.toMul) +
    muLog n M hζ (kummerFun n M α' hα' g.toMul)
  rw [this, map_add]

theorem hilbertSymbol_mul_left (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a a' b : Kˣ}
    {α α' β : Mˣ} (hα : α ^ n = embUnits M a) (hα' : α' ^ n = embUnits M a') (hβ : β ^ n = embUnits M b) :
    hilbertSymbol n s M c hζ (a := a * a') (α := α * α') (by rw [mul_pow, hα, hα', map_mul]) hβ =
      hilbertSymbol n s M c hζ hα hβ * hilbertSymbol n s M c hζ hα' hβ := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap K b)
  rw [hilbertSymbol_eq_artin n s M c hζ _ hβ σ hσ, hilbertSymbol_eq_artin n s M c hζ hα hβ σ hσ,
    hilbertSymbol_eq_artin n s M c hζ hα' hβ σ hσ,
    kummerChar_mul n M hζ α α' (fixed_of_pow_eq n M hα) (fixed_of_pow_eq n M hα'), zeta_val_add n hζ]

theorem zmodAct_eq (M : IntermediateField K Ω) (k : ZMod n) (y : muRep n M) :
    zmodAct n M k y = ((k.val : ℤ)) • y := by
  have : k = ((k.val : ℤ) : ZMod n) := by simp
  conv_lhs => rw [this]
  rw [zmodAct, ZMod.lift_coe]
  rfl

theorem braid_muMu(M : IntermediateField K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) :
    (β_ (muRep n M) (muRep n M)).hom ≫ muMu n M hζ = muMu n M hζ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  change TensorProduct.lift (muMuBil n M hζ) (y ⊗ₜ x) = TensorProduct.lift (muMuBil n M hζ) (x ⊗ₜ y)
  change zmodAct n M (muLog n M hζ y) x = zmodAct n M (muLog n M hζ x) y
  rw [zmodAct_eq, zmodAct_eq]
  apply Subtype.ext
  apply Additive.toMul.injective
  change Additive.toMul ((((muLog n M hζ y).val : ℕ) : ℤ) • x.1) =
    Additive.toMul ((((muLog n M hζ x).val : ℕ) : ℤ) • y.1)
  have key : ∀ (u v : Mˣ) (i j : ℕ), zetaM M ζ ^ i = u → zetaM M ζ ^ j = v →
      u ^ (j : ℤ) = v ^ (i : ℤ) := by
    intro u v i j hu hv
    subst hu hv
    simp only [zpow_natCast]
    rw [← pow_mul, ← pow_mul, mul_comm]
  have e1 : ∀ (k : ℤ) (w : Additive Mˣ), Additive.toMul (k • w) = Additive.toMul w ^ k :=
    fun k w => toMul_zsmul _ _
  exact (e1 _ _).trans ((key _ _ _ _ (zeta_pow_muLog n M hζ x) (zeta_pow_muLog n M hζ y)).trans (e1 _ _).symm)

theorem aux_neg {A B : ModuleCat ℤ} (F : A ⟶ B) (P : A ⟶ A) (Z W : A)
    (h1 : ConcreteCategory.hom P Z = -W) (h2 : P ≫ F = F) :
    ConcreteCategory.hom F W = - ConcreteCategory.hom F Z := by
  have : ConcreteCategory.hom F Z = ConcreteCategory.hom F (ConcreteCategory.hom P Z) := by
    rw [← ConcreteCategory.comp_apply, h2]
  rw [this, h1, map_neg, neg_neg]

/-- Graded commutativity of the cup product (Proposition 1.39) and the symmetry of $\mu_n \otimes \mu_n \to \mu_n$:
$\mathrm{inv}(\delta b \cup \delta a) = -\mathrm{inv}(\delta a \cup \delta b)$. -/
theorem hilbertInv_swap (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (α β : Mˣ)
    (hα : ∀ σ : Gal(M/K), σ • α ^ n = α ^ n) (hβ : ∀ σ : Gal(M/K), σ • β ^ n = β ^ n) :
    hilbertInv n s M c hζ β α hβ hα = - hilbertInv n s M c hζ α β hα hβ := by
  unfold hilbertInv
  have h := prop1_39.comm_cup _ c (muRep n M) (muRep n M) 1 1 (kummerClass n M α hα) (kummerClass n M β hβ)
  set F := (functor ℤ Gal(M/K) 2).map (muMu n M hζ ≫ stableIncl _ _ _) with hF
  set Z := c.cup _ _ 1 1 2 rfl (kummerClass n M α hα) (kummerClass n M β hβ) with hZ
  set W := c.cup _ _ 1 1 2 rfl (kummerClass n M β hβ) (kummerClass n M α hα) with hW
  have hb : (ConcreteCategory.hom ((functor ℤ Gal(M/K) 2).map (β_ (muRep n M) (muRep n M)).hom)) Z = - W := by
    erw [h]
    exact (neg_one_zsmul _) |>.trans rfl
  have e : (functor ℤ Gal(M/K) 2).map (β_ (muRep n M) (muRep n M)).hom ≫ F = F := by
    rw [hF, ← Functor.map_comp, ← Category.assoc, braid_muMu]
  have hFW := aux_neg F _ Z W hb e
  show s.invK M (ConcreteCategory.hom F W) = - s.invK M (ConcreteCategory.hom F Z)
  exact (congrArg (s.invK M) hFW).trans (map_neg _ _)

theorem hilbertSymbol_skew (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b : Kˣ}
    {α β : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b) :
    hilbertSymbol n s M c hζ hβ hα = (hilbertSymbol n s M c hζ hα hβ)⁻¹ := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap K b)
  rw [hilbertSymbol_eq_artin n s M c hζ hα hβ σ hσ, ← zeta_val_neg n hζ]
  apply hilbertSymbol_eq_of
  rw [hilbertInv_swap, hilbertInv_eq_zmod n s M c hζ hα hβ σ hσ, map_neg]

/-! ### Kummer extensions as finite abelian extensions -/

theorem ne_zero_of_pow_eq' {α : Ω} {a : Kˣ} (hα : α ^ n = algebraMap K Ω a) : α ≠ 0 := by
  intro h
  rw [h, zero_pow (NeZero.ne n)] at hα
  exact a.ne_zero ((_root_.map_eq_zero _).mp hα.symm)

/-- $K(\alpha)$ for $\alpha^n = a$ ($K \ni \zeta_n$) as a finite abelian extension (Kummer theory). -/
noncomputable def kExt {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {α : Ω} {a : Kˣ} (hα : α ^ n = algebraMap K Ω a) :
    FiniteAbelianExt K Ω :=
  have h := kummer_adjoin hζ (α := α) (ne_zero_of_pow_eq' n hα) ⟨a, hα.symm⟩
  have : FiniteDimensional K (IntermediateField.adjoin K {α}) := h.1
  have : IsGalois K (IntermediateField.adjoin K {α}) := h.2.1
  have : IsCyclic Gal(IntermediateField.adjoin K {α}/K) := h.2.2.1
  have : IsAbelianGalois K (IntermediateField.adjoin K {α}) := IsAbelianGalois.of_isCyclic K _
  ⟨IntermediateField.adjoin K {α}⟩

theorem kExt_toField {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {α : Ω} {a : Kˣ} (hα : α ^ n = algebraMap K Ω a) :
    (kExt n hζ hα).toField = IntermediateField.adjoin K {α} := rfl

theorem coe_pow_eq (M : IntermediateField K Ω) {a : Kˣ} {α : Mˣ} (hα : α ^ n = embUnits M a) :
    ((α : M) : Ω) ^ n = algebraMap K Ω a := by
  have := congrArg (fun u : Mˣ => ((u : M) : Ω)) hα
  simp only [Units.val_pow_eq_pow_val, IntermediateField.coe_pow] at this
  rw [this]; rfl

/-- The unit of $M$ given by a nonzero element of $\Omega$ lying in $M$. -/
noncomputable def unitOfMem (M : IntermediateField K Ω) {x : Ω} (hx : x ∈ M) (h0 : x ≠ 0) : Mˣ :=
  Units.mk0 ⟨x, hx⟩ (fun h => h0 (congrArg Subtype.val h))

theorem unitOfMem_pow (M : IntermediateField K Ω) {x : Ω} (hx : x ∈ M) (h0 : x ≠ 0) {a : Kˣ}
    (h : x ^ n = algebraMap K Ω a) : (unitOfMem M hx h0) ^ n = embUnits M a :=
  Units.ext (Subtype.ext (by simpa [unitOfMem] using h))

/-- The local Artin symbol of $b$ on $L$ acts on $\alpha \in L \cap M$ as $\tau = \sigma|_M$. -/
theorem artin_apply_unit (L : FiniteAbelianExt K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (b : Kˣ) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = TauCeti.ClassFieldTheory.artinMap K b)
    (α : Mˣ) (x : L.toField) (hx : (x : Ω) = ((α : M) : Ω)) :
    ((tauCetiArtin L b x : L.toField) : Ω) =
      ((((embM M).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ)) • α : Mˣ) : M) := by
  exact artin_apply_eq L M b σ hσ (α : M) x hx

theorem tauCetiArtin_kExt_eq_one_iff {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (M : IntermediateField K Ω)
    [FiniteDimensional K M] [IsGalois K M] {a b : Kˣ} {α : Mˣ} (hα : α ^ n = embUnits M a)
    (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = TauCeti.ClassFieldTheory.artinMap K b) :
    tauCetiArtin (kExt n hζ (coe_pow_eq n M hα)) b = 1 ↔
      ((embM M).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ)) • α = α := by
  set L := kExt n hζ (coe_pow_eq n M hα) with hL
  have hmem : ((α : M) : Ω) ∈ L.toField := IntermediateField.mem_adjoin_simple_self K _
  have hb := artin_apply_unit L M b σ hσ α ⟨((α : M) : Ω), hmem⟩ rfl
  constructor
  · intro h
    rw [h] at hb
    exact Units.ext (Subtype.ext hb.symm)
  · intro h
    have hfix : tauCetiArtin L b ⟨((α : M) : Ω), hmem⟩ = ⟨((α : M) : Ω), hmem⟩ :=
      Subtype.ext (by rw [hb, h])
    have := IntermediateField.algHom_ext_of_eq_adjoin (F := K) (S := L.toField)
      (s := {((α : M) : Ω)}) rfl (φ₁ := (tauCetiArtin L b).toAlgHom) (φ₂ := AlgHom.id K _)
      (fun x hx => by
        simp only [Set.mem_singleton_iff] at hx
        subst hx
        exact hfix)
    exact AlgEquiv.ext fun x => congrArg (fun φ => φ x) this

theorem hilbertSymbol_norm (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (c : CupProductFamily Gal(M/K)) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) {a b : Kˣ}
    {α β : Mˣ} (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b)
    [FiniteDimensional K (IntermediateField.adjoin K {((α : M) : Ω)})] :
    hilbertSymbol n s M c hζ hα hβ = 1 ↔ b ∈ normGroup (IntermediateField.adjoin K {((α : M) : Ω)}) := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap K b)
  rw [hilbertSymbol_eq_one_iff n s M c hζ hα hβ σ hσ, ← tauCetiArtin_kExt_eq_one_iff n hζ M hα σ hσ]
  have this := ker_tauCetiArtin (kExt n hζ (coe_pow_eq n M hα))
  have h2 : b ∈ (tauCetiArtin (kExt n hζ (coe_pow_eq n M hα))).ker ↔
      b ∈ normGroup (kExt n hζ (coe_pow_eq n M hα)).toField := by rw [this]
  exact MonoidHom.mem_ker.symm.trans h2

theorem nondeg_left_aux (s : InvariantSystem K Ω) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) (a : Kˣ)
    (H : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] (c : CupProductFamily Gal(M/K))
      (b : Kˣ) (α β : Mˣ) (hα : α ^ n = embUnits M a) (hβ : β ^ n = embUnits M b),
      hilbertSymbol n s M c hζ hα hβ = 1) : ∃ x : Kˣ, x ^ n = a := by
  have hζ' : IsPrimitiveRoot (ζ : K) n := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have : NeZero (n : K) := hζ'.neZero'
  have : NeZero (n : Ω) := ⟨by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero _).mpr (NeZero.ne _)⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨α0, hα0⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K Ω a) n
  set L := kExt n hζ hα0 with hL
  have hmem : α0 ∈ L.toField := IntermediateField.mem_adjoin_simple_self K _
  have hfix : ∀ g : Gal(L.toField/K), g ⟨α0, hmem⟩ = ⟨α0, hmem⟩ := by
    intro g
    obtain ⟨b, rfl⟩ := surjective_tauCetiArtin L g
    obtain ⟨β0, hβ0⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K Ω b) n
    set L' := kExt n hζ hβ0 with hL'
    set F := L.sup L' with hF
    have hα0F : α0 ∈ F.toField :=
      (le_sup_left : L.toField ≤ L.toField ⊔ L'.toField) hmem
    have hβ0F : β0 ∈ F.toField :=
      (le_sup_right : L'.toField ≤ L.toField ⊔ L'.toField) (IntermediateField.mem_adjoin_simple_self K _)
    have hne : α0 ≠ 0 := ne_zero_of_pow_eq' n hα0
    have hne' : β0 ≠ 0 := ne_zero_of_pow_eq' n hβ0
    let α : F.toField ˣ := unitOfMem F.toField hα0F hne
    let β : F.toField ˣ := unitOfMem F.toField hβ0F hne'
    have hα : α ^ n = embUnits F.toField a := unitOfMem_pow n F.toField hα0F hne hα0
    have hβ : β ^ n = embUnits F.toField b := unitOfMem_pow n F.toField hβ0F hne' hβ0
    obtain ⟨c⟩ := cupProductFamily_nonempty Gal(F.toField/K)
    have h1 := H F.toField c b α β hα hβ
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap K b)
    have h2 := (hilbertSymbol_eq_one_iff n s F.toField c hζ hα hβ σ hσ).1 h1
    apply Subtype.ext
    rw [artin_apply_unit L F.toField b σ hσ α ⟨α0, hmem⟩ rfl, h2]
    rfl
  obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L.toField) ⟨α0, hmem⟩).2 hfix
  have hyΩ : algebraMap K Ω y = α0 := congrArg Subtype.val hy
  have hyn : y ^ n = (a : K) := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hyΩ, hα0]
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hyn
    exact a.ne_zero hyn.symm
  exact ⟨Units.mk0 y hy0, Units.ext hyn⟩

variable (K Ω) in
/-- **Theorem 4.4** (Milne, *CFT*, III, p. 113): the Hilbert symbol is bimultiplicative, skew-symmetric,
nondegenerate, and $(a, b) = 1$ iff $b$ is a norm from $K[\sqrt[n]{a}]$. Proved from Remark 4.5 (the key formula
$(a, b) = \zeta^{\chi_\alpha(\phi_K(b))}$, `hilbertSymbol_eq_artin`), graded commutativity of cup products
(Proposition 1.39), and Tau Ceti's local Artin map. -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 4.4, p. 113"]
theorem thm4_4 : Thm4_4 K Ω := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n _ s M _ _ c ζ hζ a a' b α α' β hα hα' hβ
    exact hilbertSymbol_mul_left n s M c hζ hα hα' hβ
  · intro n _ s M _ _ c ζ hζ a b b' α β β' hα hβ hβ'
    exact hilbertSymbol_mul_right n s M c hζ hα hβ hβ'
  · intro n _ s M _ _ c ζ hζ a b α β hα hβ
    exact hilbertSymbol_skew n s M c hζ hα hβ
  · intro n _ s ζ hζ a H
    exact nondeg_left_aux n s hζ a H
  · intro n _ s ζ hζ b H
    refine nondeg_left_aux n s hζ b ?_
    intro M _ _ c b' α β hα hβ
    have h1 := hilbertSymbol_skew n s M c hζ hα hβ
    have h2 := H M c b' β α hβ hα
    exact inv_eq_one.1 (h1.symm.trans h2)
  · intro n _ s M _ _ c ζ hζ a b α β hα hβ _
    exact hilbertSymbol_norm n s M c hζ hα hβ

end NumberFieldKB.MilneCFT.Ch3
