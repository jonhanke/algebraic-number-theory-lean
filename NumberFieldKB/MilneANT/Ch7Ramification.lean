import NumberFieldKB.MilneANT.Ch7Integral

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: ramification groups

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Setting (Milne p. 130): $K$ complete with respect to a discrete absolute value, $L/K$ finite Galois with group $G$,
$B = \{\alpha \in L : |\alpha| \le 1\}$ with maximal ideal $\mathfrak p = (\Pi)$. As in `Ch7Extensions.lean`, $A$ is a
complete discrete valuation ring with fraction field $K$, $B$ is the integral closure of $A$ in $L$ (a local ring,
`isLocalRing_integralClosure`), and $\mathfrak p$ is its maximal ideal. Milne's condition $|\sigma\alpha - \alpha| < |\Pi|^i$
is $\operatorname{ord}_L(\sigma\alpha - \alpha) \ge i + 1$, i.e. $\sigma\alpha - \alpha \in \mathfrak p^{i+1}$.

* **Ramification groups** (prose definition, p. 130; `ramificationGroupMilne`): $G_i = \{\sigma : \sigma\alpha - \alpha \in
  \mathfrak p^{i+1}\ \forall \alpha \in B\}$; $G_0$ is the inertia group.
* **Lemma 7.57** (`lemma_7_57_normal`, `lemma_7_57_eq_bot`; also `ramificationGroupMilne_antitone`).
* **Theorem 7.58** (`thm_7_58a`, `thm_7_58b`).
* **Corollary 7.59** (`cor_7_59_units`, `cor_7_59_additive`, `cor_7_59_isSolvable`).
-/

open IsLocalRing

universe u v w

namespace NumberFieldKB.MilneANT

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]

/-- The defining condition of $G_i$: $\sigma\beta - \beta \in \mathfrak p^{i+1}$ for every $\beta \in B$ (written with
$\beta' = \sigma\beta$, which again lies in $B$). -/
def IsInRamificationGroupMilne (i : ℕ) (σ : L ≃ₐ[K] L) : Prop :=
  ∀ b b' : integralClosure A L, (b' : L) = σ b → b' - b ∈ maximalIdeal (integralClosure A L) ^ (i + 1)

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
open Pointwise

section Helpers

/-- The restriction of $\sigma \in G$ to a ring automorphism of $B$. -/
private noncomputable abbrev resB (σ : L ≃ₐ[K] L) : integralClosure A L ≃ₐ[A] integralClosure A L :=
  galRestrict A K L (integralClosure A L) σ

private lemma coe_resB (σ : L ≃ₐ[K] L) (b : integralClosure A L) :
    ((resB A K L σ b : integralClosure A L) : L) = σ b :=
  algebraMap_galRestrict_apply A σ b

private lemma resB_mul (σ τ : L ≃ₐ[K] L) (b : integralClosure A L) :
    resB A K L (σ * τ) b = resB A K L σ (resB A K L τ b) := by
  show galRestrict A K L (integralClosure A L) (σ * τ) b = _
  rw [map_mul]; rfl

private lemma resB_one (b : integralClosure A L) : resB A K L 1 b = b := by
  show galRestrict A K L (integralClosure A L) 1 b = _
  rw [map_one]; rfl

private lemma isIn_iff (i : ℕ) (σ : L ≃ₐ[K] L) :
    IsInRamificationGroupMilne A K L i σ ↔
      ∀ b : integralClosure A L, resB A K L σ b - b ∈ maximalIdeal (integralClosure A L) ^ (i + 1) := by
  constructor
  · intro h b
    exact h b _ (coe_resB A K L σ b)
  · intro h b b' hb
    have : b' = resB A K L σ b := Subtype.ext (by rw [hb, coe_resB])
    rw [this]; exact h b

private lemma resB_mem_max_iff (σ : L ≃ₐ[K] L) (x : integralClosure A L) :
    resB A K L σ x ∈ maximalIdeal (integralClosure A L) ↔ x ∈ maximalIdeal (integralClosure A L) := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr (MulEquiv.isUnit_map (resB A K L σ).toRingEquiv.toMulEquiv)

/-- The action of $G$ on $B$ through the restriction maps. -/
private noncomputable def actB : MulSemiringAction (L ≃ₐ[K] L) (integralClosure A L) :=
  MulSemiringAction.compHom _ (galRestrict A K L (integralClosure A L)).toMonoidHom

private lemma resB_mem_pow (n : ℕ) (σ : L ≃ₐ[K] L) {x : integralClosure A L}
    (hx : x ∈ maximalIdeal (integralClosure A L) ^ n) :
    resB A K L σ x ∈ maximalIdeal (integralClosure A L) ^ n := by
  set f : integralClosure A L →+* integralClosure A L := (resB A K L σ).toRingEquiv.toRingHom
  have hc : (maximalIdeal (integralClosure A L)).comap f = maximalIdeal (integralClosure A L) := by
    ext y
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (MulEquiv.isUnit_map (resB A K L σ).toRingEquiv.toMulEquiv)
  have h1 : (maximalIdeal (integralClosure A L)).map f ≤ maximalIdeal (integralClosure A L) :=
    Ideal.map_le_iff_le_comap.mpr hc.ge
  have h2 : ((maximalIdeal (integralClosure A L)) ^ n).map f ≤ maximalIdeal (integralClosure A L) ^ n := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono h1 n
  exact h2 (Ideal.mem_map_of_mem f hx)

end Helpers

theorem isInRamificationGroupMilne_one (i : ℕ) : IsInRamificationGroupMilne A K L i 1 := by
  intro b b' hb
  have : b' = b := Subtype.ext (by simpa using hb)
  simp [this]

theorem isInRamificationGroupMilne_mul (i : ℕ) {σ τ : L ≃ₐ[K] L} (hσ : IsInRamificationGroupMilne A K L i σ)
    (hτ : IsInRamificationGroupMilne A K L i τ) : IsInRamificationGroupMilne A K L i (σ * τ) := by
  rw [isIn_iff] at *
  intro b
  have h : resB A K L (σ * τ) b - b =
      resB A K L σ (resB A K L τ b - b) + (resB A K L σ b - b) := by
    rw [resB_mul, map_sub]; abel
  rw [h]
  exact Ideal.add_mem _ (resB_mem_pow A K L _ σ (hτ b)) (hσ b)

theorem isInRamificationGroupMilne_inv (i : ℕ) {σ : L ≃ₐ[K] L} (hσ : IsInRamificationGroupMilne A K L i σ) :
    IsInRamificationGroupMilne A K L i σ⁻¹ := by
  rw [isIn_iff] at *
  intro b
  have h1 : resB A K L σ (resB A K L σ⁻¹ b) = b := by
    rw [← resB_mul]; simp
  have := hσ (resB A K L σ⁻¹ b)
  rw [h1] at this
  have h2 := Ideal.neg_mem_iff _ |>.mpr this
  simpa using h2

/-- **Ramification groups** (prose definition, Milne p. 130): for $i \ge 0$,
$G_i = \{\sigma \in G : |\sigma\alpha - \alpha| < |\Pi|^i \text{ for all } \alpha \in B\}$. $G_0$ is the inertia group,
$G_1$ the ramification group, and $G_i$ ($i > 1$) are the higher ramification groups. -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of the ramification groups, p. 130"]
def ramificationGroupMilne (i : ℕ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | IsInRamificationGroupMilne A K L i σ}
  one_mem' := isInRamificationGroupMilne_one A K L i
  mul_mem' := isInRamificationGroupMilne_mul A K L i
  inv_mem' := isInRamificationGroupMilne_inv A K L i

/-- $G \supset G_0 \supset G_1 \supset \cdots$ (Milne p. 130). -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of the ramification groups, p. 130"]
theorem ramificationGroupMilne_antitone : Antitone (ramificationGroupMilne A K L) := by
  intro i j hij σ hσ
  have hσ' : IsInRamificationGroupMilne A K L j σ := hσ
  show IsInRamificationGroupMilne A K L i σ
  rw [isIn_iff] at *
  intro b
  exact Ideal.pow_le_pow_right (Nat.succ_le_succ hij) (hσ' b)

/-- **Lemma 7.57**, first part: the ramification groups $G_i$ are normal subgroups of $G$. -/
@[kb "milne2020ant" "v3.08, Lemma 7.57, p. 130"]
theorem lemma_7_57_normal (i : ℕ) : (ramificationGroupMilne A K L i).Normal := by
  refine ⟨fun σ hσ τ => ?_⟩
  have hσ' : IsInRamificationGroupMilne A K L i σ := hσ
  show IsInRamificationGroupMilne A K L i (τ * σ * τ⁻¹)
  rw [isIn_iff] at *
  intro b
  have h1 : resB A K L τ (resB A K L τ⁻¹ b) = b := by
    rw [← resB_mul]; simp
  have h : resB A K L (τ * σ * τ⁻¹) b - b =
      resB A K L τ (resB A K L σ (resB A K L τ⁻¹ b) - resB A K L τ⁻¹ b) := by
    rw [map_sub, h1, resB_mul, resB_mul]
  rw [h]
  exact resB_mem_pow A K L _ τ (hσ' _)

/-- **Lemma 7.57**, second part: $G_i = \{1\}$ for $i$ large enough. -/
@[kb "milne2020ant" "v3.08, Lemma 7.57, p. 130"]
theorem lemma_7_57_eq_bot : ∃ N : ℕ, ∀ i ≥ N, ramificationGroupMilne A K L i = ⊥ := by
  have : IsNoetherianRing (integralClosure A L) :=
    IsIntegralClosure.isNoetherianRing A K L (integralClosure A L)
  have : Algebra.IsAlgebraic A L := (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K)).mpr
      (inferInstance : Algebra.IsAlgebraic K L)
  have : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  have key : ∀ σ : L ≃ₐ[K] L, ∃ N : ℕ, σ ≠ 1 → ∀ i ≥ N, σ ∉ ramificationGroupMilne A K L i := by
    intro σ
    by_cases hσ : σ = 1
    · exact ⟨0, fun h => absurd hσ h⟩
    obtain ⟨x, hx⟩ : ∃ x : L, σ x ≠ x := by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext h)
    obtain ⟨a, ha, hax⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) x).exists_integral_multiple
    have hmem : a • x ∈ integralClosure A L := hax
    set b : integralClosure A L := ⟨a • x, hmem⟩
    have hne : resB A K L σ b - b ≠ 0 := by
      intro h
      have h' : ((resB A K L σ b : integralClosure A L) : L) = (b : L) := by
        rw [sub_eq_zero.mp h]
      rw [coe_resB] at h'
      change σ (a • x) = a • x at h'
      rw [show a • x = algebraMap K L (algebraMap A K a) * x by
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A K L], map_mul,
        AlgEquiv.commutes] at h'
      have ha' : algebraMap K L (algebraMap A K a) ≠ 0 :=
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr
          ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha)
      exact hx (mul_left_cancel₀ ha' h')
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (integralClosure A L))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    have : resB A K L σ b - b ∉ ⨅ n : ℕ, maximalIdeal (integralClosure A L) ^ n := by
      rw [hbot]; simpa using hne
    rw [Submodule.mem_iInf] at this
    push Not at this
    obtain ⟨n, hn⟩ := this
    refine ⟨n, fun _ i hi hmemG => ?_⟩
    have h1 : IsInRamificationGroupMilne A K L i σ := hmemG
    rw [isIn_iff] at h1
    exact hn (Ideal.pow_le_pow_right (by omega) (h1 b))
  choose N hN using key
  refine ⟨Finset.univ.sup N, fun i hi => ?_⟩
  rw [eq_bot_iff]
  intro σ hσ
  by_contra h
  exact hN σ h i (le_trans (Finset.le_sup (Finset.mem_univ σ)) hi) hσ

/-- **Theorem 7.58(a)**, Galois part. Assume the residue field extension $l/k$ is separable. Reduction modulo
$\mathfrak p$ is a surjective homomorphism $G \to \operatorname{Gal}(l/k)$ with kernel $G_0$, so
$G/G_0 \cong \operatorname{Gal}(l/k)$. The statement about the fixed field of $G_0$ is `thm_7_58a_fixedField`
(in `Ch7RamificationFields.lean`). -/
@[kb "milne2020ant" "v3.08, Thm. 7.58, p. 130"]
theorem thm_7_58a [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] :
    ∃ φ : (L ≃ₐ[K] L) →* (ResidueField (integralClosure A L) ≃ₐ[ResidueField A] ResidueField (integralClosure A L)),
      (∀ (σ : L ≃ₐ[K] L) (b b' : integralClosure A L), (b' : L) = σ b → φ σ (residue _ b) = residue _ b') ∧
      Function.Surjective φ ∧ φ.ker = ramificationGroupMilne A K L 0 := by
  classical
  let B := integralClosure A L
  let _ : MulSemiringAction (L ≃ₐ[K] L) B := actB A K L
  have hsmul : ∀ (g : L ≃ₐ[K] L) (b : B), g • b = resB A K L g b := fun _ _ => rfl
  have : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  have : SMulCommClass (L ≃ₐ[K] L) A B :=
    ⟨fun g a b => by rw [hsmul, hsmul, map_smul]⟩
  have : SMulDistribClass (L ≃ₐ[K] L) B L :=
    ⟨fun g b l => by
      rw [Algebra.smul_def, Algebra.smul_def]
      change g (algebraMap B L b * l) = algebraMap B L (resB A K L g b) * g l
      rw [map_mul]; congr 1; exact (coe_resB A K L g b).symm⟩
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : Algebra.IsInvariant A B (L ≃ₐ[K] L) :=
    (IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) A B K L).isInvariant
  have hstab : ∀ g : L ≃ₐ[K] L, g • maximalIdeal B = maximalIdeal B := by
    intro g
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hsmul]
    exact resB_mem_max_iff A K L g⁻¹ x
  let φ : (L ≃ₐ[K] L) →* (ResidueField (integralClosure A L) ≃ₐ[ResidueField A]
      ResidueField (integralClosure A L)) :=
    { toFun := fun σ => ResidueField.mapAlgEquiv' (resB A K L σ)
      map_one' := by
        refine AlgEquiv.ext fun x => ?_
        obtain ⟨b, rfl⟩ := residue_surjective x
        change residue B (resB A K L 1 b) = residue B b
        rw [resB_one]
      map_mul' := fun σ τ => by
        refine AlgEquiv.ext fun x => ?_
        obtain ⟨b, rfl⟩ := residue_surjective x
        change residue B (resB A K L (σ * τ) b) = residue B (resB A K L σ (resB A K L τ b))
        rw [resB_mul] }
  have hφ : ∀ σ b, φ σ (residue B b) = residue B (resB A K L σ b) := fun _ _ => rfl
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro σ b b' hb
    have : b' = resB A K L σ b := Subtype.ext (by rw [hb, coe_resB])
    rw [this, hφ]
  · intro τ
    obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[K] L) (maximalIdeal A)
      (maximalIdeal B) τ
    refine ⟨g.1, AlgEquiv.ext fun x => ?_⟩
    obtain ⟨b, rfl⟩ := residue_surjective x
    rw [hφ]
    have := congrArg (fun f => f (residue B b)) hg
    exact this
  · ext σ
    rw [MonoidHom.mem_ker]
    change φ σ = 1 ↔ IsInRamificationGroupMilne A K L 0 σ
    rw [isIn_iff]
    have key : ∀ b, φ σ (residue B b) = residue B b ↔
        resB A K L σ b - b ∈ maximalIdeal B ^ (0 + 1) := by
      intro b
      rw [zero_add, pow_one, hφ]
      exact Ideal.Quotient.eq (I := maximalIdeal B)
    constructor
    · intro h b
      rw [← key]
      rw [h]; rfl
    · intro h
      refine AlgEquiv.ext fun x => ?_
      obtain ⟨b, rfl⟩ := residue_surjective x
      exact (key b).mpr (h b)


section Uniformizer

include K in
/-- $\mathfrak p$ is generated by a nonzero element. -/
private lemma exists_uniformizer :
    ∃ ϖ : integralClosure A L, maximalIdeal (integralClosure A L) = Ideal.span {ϖ} ∧ ϖ ≠ 0 := by
  have hD : IsDedekindDomain (integralClosure A L) :=
    IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)
  have hp := maximalIdeal_isPrincipal_of_isDedekindDomain (R := integralClosure A L)
  refine ⟨Submodule.IsPrincipal.generator (maximalIdeal _),
    (Ideal.span_singleton_generator _).symm, fun h0 => ?_⟩
  have hP : maximalIdeal (integralClosure A L) = ⊥ := by
    rw [← Ideal.span_singleton_generator (maximalIdeal (integralClosure A L)), h0]; simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmem : algebraMap A (integralClosure A L) π ∈ maximalIdeal (integralClosure A L) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hπ.not_isUnit (IsLocalHom.map_nonunit _ hu)
  rw [hP, Ideal.mem_bot] at hmem
  have h1 : algebraMap A L π = 0 := by
    have := congrArg Subtype.val hmem
    simpa using this
  rw [IsScalarTower.algebraMap_apply A K L] at h1
  exact hπ.ne_zero (by simpa using h1)

private lemma resB_inv_apply (σ : L ≃ₐ[K] L) (x : integralClosure A L) :
    resB A K L σ (resB A K L σ⁻¹ x) = x := by
  rw [← resB_mul]; simp

private lemma cancel_mem {ϖ : integralClosure A L}
    (hϖ : maximalIdeal (integralClosure A L) = Ideal.span {ϖ}) (hne : ϖ ≠ 0) (n : ℕ)
    (x : integralClosure A L) :
    ϖ ^ n * x ∈ maximalIdeal (integralClosure A L) ^ (n + 1) ↔ x ∈ maximalIdeal (integralClosure A L) := by
  rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero _ hne)]

private lemma residue_resB {σ : L ≃ₐ[K] L} (hσ : σ ∈ ramificationGroupMilne A K L 0)
    (x : integralClosure A L) :
    residue (integralClosure A L) (resB A K L σ x) = residue (integralClosure A L) x := by
  have h : IsInRamificationGroupMilne A K L 0 σ := hσ
  rw [isIn_iff] at h
  have := h x
  rw [zero_add, pow_one] at this
  exact (Ideal.Quotient.eq (I := maximalIdeal (integralClosure A L))).mpr this

end Uniformizer

/-- **Theorem 7.58(b)**, the inclusion proved here: for $i \ge 1$ (indeed any $i$), $G_i$ is contained in
$\{\sigma \in G_0 : |\sigma\Pi - \Pi| < |\Pi|^i\}$. -/
@[kb "milne2020ant" "v3.08, Thm. 7.58, p. 131"]
theorem thm_7_58b_le (ϖ : integralClosure A L) (i : ℕ) (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ ramificationGroupMilne A K L i) :
    σ ∈ ramificationGroupMilne A K L 0 ∧
      ∀ ϖ' : integralClosure A L, (ϖ' : L) = σ ϖ → ϖ' - ϖ ∈ maximalIdeal (integralClosure A L) ^ (i + 1) := by
  refine ⟨ramificationGroupMilne_antitone A K L (Nat.zero_le i) hσ, fun ϖ' hϖ' => ?_⟩
  exact hσ ϖ ϖ' hϖ'

/-- **Theorem 7.58(b)** (named statement). Assume $l/k$ separable and let $\Pi$ generate $\mathfrak p$. For $i \ge 1$,
$G_i = \{\sigma \in G_0 : |\sigma\Pi - \Pi| < |\Pi|^i\}$. Milne's proof uses $B = A_0[\Pi]$ for the valuation ring
$A_0$ of the maximal unramified subextension $K_0$ (Remark 7.56 for $L/K_0$), which rests on Proposition 7.50 and
Corollary 7.51 (named statements `Prop7_50`, `Cor7_51`); the inclusion $\subseteq$ is proved (`thm_7_58b_le`). -/
@[kb "milne2020ant" "v3.08, Thm. 7.58, p. 131"]
structure Theorem7_58b : Prop where
  mem_iff : ∀ [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
    (ϖ : integralClosure A L), maximalIdeal (integralClosure A L) = Ideal.span {ϖ} → ∀ (i : ℕ), 1 ≤ i →
    ∀ σ : L ≃ₐ[K] L, σ ∈ ramificationGroupMilne A K L i ↔ σ ∈ ramificationGroupMilne A K L 0 ∧
      ∀ ϖ' : integralClosure A L, (ϖ' : L) = σ ϖ → ϖ' - ϖ ∈ maximalIdeal (integralClosure A L) ^ (i + 1)

/-- **Corollary 7.59**, $G_0/G_1 \hookrightarrow l^\times$: there is a homomorphism $G_0 \to l^\times$ with kernel $G_1$
(Milne: $\sigma \mapsto \sigma\Pi/\Pi \bmod \mathfrak p$). Assumes $l/k$ separable, as in Theorem 7.58; conditional on
Theorem 7.58(b). -/
@[kb "milne2020ant" "v3.08, Cor. 7.59, p. 131"]
theorem cor_7_59_units (h : Theorem7_58b A K L)
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] :
    ∃ θ : ramificationGroupMilne A K L 0 →* (ResidueField (integralClosure A L))ˣ,
      θ.ker = (ramificationGroupMilne A K L 1).subgroupOf (ramificationGroupMilne A K L 0) := by
  obtain ⟨ϖ, hϖ, hne⟩ := exists_uniformizer A K L
  have hex : ∀ σ : ramificationGroupMilne A K L 0, ∃ u : integralClosure A L,
      resB A K L σ.1 ϖ = ϖ * u := by
    intro σ
    have h1 : resB A K L σ.1 ϖ ∈ maximalIdeal (integralClosure A L) :=
      (resB_mem_max_iff A K L σ.1 ϖ).mpr (hϖ ▸ Ideal.mem_span_singleton_self ϖ)
    rw [hϖ, Ideal.mem_span_singleton] at h1
    exact h1
  choose u hu using hex
  have hunit : ∀ σ : ramificationGroupMilne A K L 0, IsUnit (u σ) := by
    intro σ
    have h1 := hu σ⁻¹
    have h2 : ϖ = resB A K L σ.1 (resB A K L (σ⁻¹ : ramificationGroupMilne A K L 0).1 ϖ) :=
      (resB_inv_apply A K L σ.1 ϖ).symm
    rw [h1, map_mul, hu σ] at h2
    have h3 : ϖ * 1 = ϖ * (u σ * resB A K L σ.1 (u σ⁻¹)) := by rw [mul_one, ← mul_assoc]; exact h2
    exact isUnit_iff_exists_inv.mpr ⟨_, (mul_left_cancel₀ hne h3).symm⟩
  have hmul : ∀ σ τ : ramificationGroupMilne A K L 0,
      u (σ * τ) = u σ * resB A K L σ.1 (u τ) := by
    intro σ τ
    apply mul_left_cancel₀ hne
    have : resB A K L (σ * τ).1 ϖ = resB A K L σ.1 (resB A K L τ.1 ϖ) := resB_mul A K L _ _ _
    rw [hu (σ * τ), hu τ, map_mul, hu σ] at this
    rw [this]; ring
  let θ : ramificationGroupMilne A K L 0 →* (ResidueField (integralClosure A L))ˣ :=
    MonoidHom.mk' (fun σ => Units.map (residue (integralClosure A L)).toMonoidHom (hunit σ).unit)
      (fun σ τ => by
        refine Units.ext ?_
        simp only [Units.coe_map, Units.val_mul, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe,
          MonoidHom.coe_ofClass]
        rw [hmul, map_mul, residue_resB A K L σ.2])
  refine ⟨θ, ?_⟩
  ext σ
  have hθ : θ σ = 1 ↔ residue (integralClosure A L) (u σ) = 1 := by
    rw [Units.ext_iff]; simp [θ]
  have hG1 : σ ∈ (ramificationGroupMilne A K L 1).subgroupOf (ramificationGroupMilne A K L 0) ↔
      resB A K L σ.1 ϖ - ϖ ∈ maximalIdeal (integralClosure A L) ^ (1 + 1) := by
    rw [Subgroup.mem_subgroupOf, h.mem_iff ϖ hϖ 1 le_rfl]
    refine ⟨fun hh => hh.2 _ (coe_resB A K L σ.1 ϖ), fun hh => ⟨σ.2, fun ϖ' h' => ?_⟩⟩
    have : ϖ' = resB A K L σ.1 ϖ := Subtype.ext (by rw [h', coe_resB])
    rw [this]; exact hh
  rw [MonoidHom.mem_ker, hθ, hG1]
  have e := cancel_mem A L hϖ hne 1 (u σ - 1)
  have e2 : ϖ ^ 1 * (u σ - 1) = resB A K L σ.1 ϖ - ϖ := by rw [hu σ]; ring
  rw [e2] at e
  rw [e, ← map_one (residue (integralClosure A L))]
  exact Ideal.Quotient.eq (I := maximalIdeal (integralClosure A L))

/-- **Corollary 7.59**, $G_i/G_{i+1} \hookrightarrow l$ for $i \ge 1$: there is a homomorphism from $G_i$ to the
additive group of $l$ with kernel $G_{i+1}$ (Milne: $\sigma\Pi = \Pi + a\Pi^{i+1}$, $\sigma \mapsto a \bmod \mathfrak p$).
Conditional on Theorem 7.58(b). -/
@[kb "milne2020ant" "v3.08, Cor. 7.59, p. 131"]
theorem cor_7_59_additive (h : Theorem7_58b A K L)
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] (i : ℕ) (hi : 1 ≤ i) :
    ∃ θ : ramificationGroupMilne A K L i →* Multiplicative (ResidueField (integralClosure A L)),
      θ.ker = (ramificationGroupMilne A K L (i + 1)).subgroupOf (ramificationGroupMilne A K L i) := by
  obtain ⟨ϖ, hϖ, hne⟩ := exists_uniformizer A K L
  have hG0 : ∀ σ : ramificationGroupMilne A K L i, σ.1 ∈ ramificationGroupMilne A K L 0 :=
    fun σ => ramificationGroupMilne_antitone A K L (Nat.zero_le i) σ.2
  have hex : ∀ σ : ramificationGroupMilne A K L i, ∃ a : integralClosure A L,
      resB A K L σ.1 ϖ - ϖ = ϖ ^ (i + 1) * a := by
    intro σ
    have h1 : resB A K L σ.1 ϖ - ϖ ∈ maximalIdeal (integralClosure A L) ^ (i + 1) :=
      (isIn_iff A K L i σ.1).mp σ.2 ϖ
    rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    exact h1
  choose a ha using hex
  have hv : ∀ σ : ramificationGroupMilne A K L i,
      resB A K L σ.1 ϖ = ϖ * (1 + ϖ ^ i * a σ) := by
    intro σ
    have := ha σ
    linear_combination this
  have hmul : ∀ σ τ : ramificationGroupMilne A K L i,
      a (σ * τ) = (1 + ϖ ^ i * a σ) ^ (i + 1) * resB A K L σ.1 (a τ) + a σ := by
    intro σ τ
    apply mul_left_cancel₀ (pow_ne_zero (i + 1) hne)
    have e1 : resB A K L (σ * τ).1 ϖ - ϖ =
        resB A K L σ.1 (resB A K L τ.1 ϖ - ϖ) + (resB A K L σ.1 ϖ - ϖ) := by
      have : resB A K L (σ * τ).1 ϖ = resB A K L σ.1 (resB A K L τ.1 ϖ) := resB_mul A K L _ _ _
      rw [this, map_sub]; ring
    rw [ha (σ * τ), ha τ, ha σ, map_mul, map_pow, hv σ] at e1
    rw [e1, mul_pow]; ring
  have hϖP : ϖ ∈ maximalIdeal (integralClosure A L) := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have hres : ∀ σ : ramificationGroupMilne A K L i,
      residue (integralClosure A L) (1 + ϖ ^ i * a σ) = 1 := by
    intro σ
    have h0 : residue (integralClosure A L) ϖ = 0 := (residue_eq_zero_iff _).mpr hϖP
    rw [map_add, map_one, map_mul, map_pow, h0, zero_pow (by omega), zero_mul, add_zero]
  let θ : ramificationGroupMilne A K L i →* Multiplicative (ResidueField (integralClosure A L)) :=
    MonoidHom.mk' (fun σ => Multiplicative.ofAdd (residue (integralClosure A L) (a σ)))
      (fun σ τ => by
        show Multiplicative.ofAdd (residue (integralClosure A L) (a (σ * τ))) =
          Multiplicative.ofAdd (residue (integralClosure A L) (a σ) +
            residue (integralClosure A L) (a τ))
        rw [hmul, map_add, map_mul, map_pow, hres, one_pow, one_mul,
          residue_resB A K L (hG0 σ), add_comm])
  refine ⟨θ, ?_⟩
  ext σ
  have hθ : θ σ = 1 ↔ a σ ∈ maximalIdeal (integralClosure A L) := by
    show Multiplicative.ofAdd (residue (integralClosure A L) (a σ)) = 1 ↔ _
    rw [ofAdd_eq_one]; exact residue_eq_zero_iff _
  have hG1 : σ ∈ (ramificationGroupMilne A K L (i + 1)).subgroupOf (ramificationGroupMilne A K L i) ↔
      resB A K L σ.1 ϖ - ϖ ∈ maximalIdeal (integralClosure A L) ^ (i + 1 + 1) := by
    rw [Subgroup.mem_subgroupOf, h.mem_iff ϖ hϖ (i + 1) (by omega)]
    refine ⟨fun hh => hh.2 _ (coe_resB A K L σ.1 ϖ), fun hh => ⟨hG0 σ, fun ϖ' h' => ?_⟩⟩
    have : ϖ' = resB A K L σ.1 ϖ := Subtype.ext (by rw [h', coe_resB])
    rw [this]; exact hh
  rw [MonoidHom.mem_ker, hθ, hG1, ha σ]
  exact (cancel_mem A L hϖ hne (i + 1) (a σ)).symm


/-- **Corollary 7.59**, last assertion: if the residue field $k$ is finite, then $\operatorname{Gal}(L/K)$ is
solvable. Conditional on Theorem 7.58(b). -/
@[kb "milne2020ant" "v3.08, Cor. 7.59, p. 131"]
theorem cor_7_59_isSolvable (h : Theorem7_58b A K L) [Finite (ResidueField A)] :
    Group.IsSolvable (L ≃ₐ[K] L) := by
  have hfin : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have : Module.Finite (ResidueField A) (ResidueField (integralClosure A L)) := inferInstance
  have : Finite (ResidueField (integralClosure A L)) := Module.finite_of_finite (ResidueField A)
  have hsep : Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L)) := inferInstance
  obtain ⟨N, hN⟩ := lemma_7_57_eq_bot A K L
  have step : ∀ i, 1 ≤ i → Group.IsSolvable (ramificationGroupMilne A K L (i + 1)) →
      Group.IsSolvable (ramificationGroupMilne A K L i) := by
    intro i hi hs
    obtain ⟨θ, hθ⟩ := cor_7_59_additive A K L h i hi
    have : Group.IsSolvable ((ramificationGroupMilne A K L (i + 1)).subgroupOf
        (ramificationGroupMilne A K L i)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (ramificationGroupMilne_antitone A K L (Nat.le_succ i))).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (ramificationGroupMilne_antitone A K L (Nat.le_succ i))).injective
    exact Group.isSolvable_of_ker_le_range (Subgroup.subtype _) θ
      (by rw [hθ]; intro x hx; exact ⟨⟨x, hx⟩, rfl⟩)
  have hdown : ∀ d i, 1 ≤ i → N ≤ i + d → Group.IsSolvable (ramificationGroupMilne A K L i) := by
    intro d
    induction d with
    | zero =>
      intro i _ hi
      have : Subsingleton (ramificationGroupMilne A K L i) := by
        rw [hN i (by omega)]; infer_instance
      infer_instance
    | succ d ih =>
      intro i hi hNi
      exact step i hi (ih (i + 1) (by omega) (by omega))
  have h1 : Group.IsSolvable (ramificationGroupMilne A K L 1) := hdown N 1 le_rfl (by omega)
  have h0 : Group.IsSolvable (ramificationGroupMilne A K L 0) := by
    obtain ⟨θ, hθ⟩ := cor_7_59_units A K L h
    have : Group.IsSolvable ((ramificationGroupMilne A K L 1).subgroupOf (ramificationGroupMilne A K L 0)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (ramificationGroupMilne_antitone A K L (Nat.zero_le 1))).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (ramificationGroupMilne_antitone A K L (Nat.zero_le 1))).injective
    exact Group.isSolvable_of_ker_le_range (Subgroup.subtype _) θ
      (by rw [hθ]; intro x hx; exact ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨φ, -, -, hker⟩ := thm_7_58a A K L
  have : Group.IsSolvable (ResidueField (integralClosure A L) ≃ₐ[ResidueField A]
      ResidueField (integralClosure A L)) := inferInstance
  exact Group.isSolvable_of_ker_le_range (Subgroup.subtype _) φ
    (by rw [hker]; intro x hx; exact ⟨⟨x, hx⟩, rfl⟩)

end NumberFieldKB.MilneANT
