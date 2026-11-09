import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Local
import NumberFieldKB.MilneCFT.Ch2Lemma33

/-!
# Milne, *Class Field Theory*, Chapter III §1: the invariant map

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

**The invariant map** (p. 99). For an unramified extension $L/K$ with group $G$, Milne defines
$\mathrm{inv}_{L/K}$ as the composite
$$H^2(G, L^\times) \xrightarrow{\ \mathrm{ord}_L\ } H^2(G, \mathbb Z) \xleftarrow[\simeq]{\ \delta\ }
H^1(G, \mathbb Q/\mathbb Z) \simeq \operatorname{Hom}(G, \mathbb Q/\mathbb Z) \xrightarrow{f \mapsto f(\sigma)}
\mathbb Q/\mathbb Z,\qquad \sigma = \mathrm{Frob}_{L/K}.$$
The construction only uses a $G$-map $v : M \to \mathbb Z$ and an element $\sigma \in G$; `invOf M v σ` is this
composite for any finite group $G$, any $G$-module $M$ (the inverse of $\delta$ is Chapter II, Lemma 3.3 (c),
`lemma_3_3c`).

**Relative situations.** Milne's §§1–2 also use the invariant maps of extensions $M/F$ with $K \subseteq F \subseteq
M$ (Proposition 1.8, Theorem 2.1, Lemma 2.7). The library has no local-field structure on an intermediate field, so
the base $F$ is encoded by the subgroup $H = \operatorname{Gal}(M/F) \subseteq \operatorname{Gal}(M/K)$ ($F = M^H$,
`baseOf M H`), and $H^2(M/F)$ is `H2rel M H` $= H^2(H, M^\times)$. The normalized valuation $\mathrm{ord}_M$
(`IsNormalizedOrd`), the Frobenius element of $M/F$ (`IsFrobeniusOver`, $\sigma a \equiv a^{q_F} \bmod
\mathfrak m_M$ with $q_F = |\mathcal O_F/\mathfrak m_F|$) and unramifiedness of $M/F$ (`IsUnramifiedOver`, trivial
inertia group in $H$) are characterized by their defining properties; `invRel M H v σ` is the invariant map of
$M/F$ built from them.

**Infinite extensions.** Milne's $H^2(K^{\mathrm{un}}/K)$ and $H^2(K^{\mathrm{al}}/K)$ are direct limits of the
$H^2(L/K)$ over finite subextensions along inflation (Chapter II, Proposition 4.2). Statements about them are
formalized at finite level: a map out of the direct limit is a family of maps compatible with inflation
(`inflRel`).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

/-! ## The invariant map of a $G$-map $v : M \to \mathbb Z$ and an element $\sigma$ -/

section Generic

variable {G : Type} [Group G] [Fintype G]

/-- The class $\frac{a}{b} \bmod \mathbb Z$ in $\mathbb Q/\mathbb Z$. -/
noncomputable def qz (q : ℚ) : QZ := QuotientAddGroup.mk q

/-- The subgroup $\frac1n\mathbb Z/\mathbb Z$ of $\mathbb Q/\mathbb Z$. -/
noncomputable def qzOver (n : ℕ) : AddSubgroup QZ := AddSubgroup.zmultiples (qz (1 / n))

theorem qz_zsmul (n : ℤ) (q : ℚ) : n • qz q = qz (n * q) := by
  rw [qz, qz, ← QuotientAddGroup.mk_zsmul, zsmul_eq_mul]

theorem qz_nsmul (n : ℕ) (q : ℚ) : n • qz q = qz (n * q) := by
  rw [qz, qz, ← QuotientAddGroup.mk_nsmul, nsmul_eq_mul]

theorem qz_add (p q : ℚ) : qz (p + q) = qz p + qz q := rfl

theorem qz_eq_zero_iff (q : ℚ) : qz q = 0 ↔ ∃ z : ℤ, (z : ℚ) = q := by
  rw [qz, QuotientAddGroup.eq_zero_iff]
  simp only [AddMonoidHom.mem_range, Int.coe_castAddHom]

/-- $\frac1n \bmod \mathbb Z$ has order $n$. -/
theorem addOrderOf_qz_inv (n : ℕ) (hn : 0 < n) : addOrderOf (qz (1 / n)) = n := by
  rw [addOrderOf_eq_iff hn]
  refine ⟨?_, fun m hm hm0 => ?_⟩
  · rw [qz_nsmul, qz_eq_zero_iff]
    exact ⟨1, by push_cast; field_simp⟩
  · rw [qz_nsmul, Ne, qz_eq_zero_iff]
    rintro ⟨z, hz⟩
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    have h1 : (0 : ℚ) < z := by rw [hz]; positivity
    have h2 : (z : ℚ) < 1 := by
      rw [hz, mul_one_div, div_lt_one hn']; exact_mod_cast hm
    have : (0 : ℤ) < z := by exact_mod_cast h1
    have : z < 1 := by exact_mod_cast h2
    omega

/-- $\frac1n\mathbb Z/\mathbb Z$ has $n$ elements. -/
theorem card_qzOver (n : ℕ) (hn : 0 < n) : Nat.card (qzOver n) = n := by
  rw [qzOver, Nat.card_zmultiples, addOrderOf_qz_inv n hn]

instance : (seqZQ G).X₃.IsTrivial :=
  inferInstanceAs (Rep.of (Representation.trivial ℤ G QZ)).IsTrivial

/-- The isomorphism $H^2(G, \mathbb Z) \simeq \operatorname{Hom}(G, \mathbb Q/\mathbb Z)$: the inverse of the
connecting isomorphism $\delta : H^1(G, \mathbb Q/\mathbb Z) \to H^2(G, \mathbb Z)$ of
$0 \to \mathbb Z \to \mathbb Q \to \mathbb Q/\mathbb Z \to 0$ (Chapter II, Lemma 3.3 (c)), followed by
$H^1(G, \mathbb Q/\mathbb Z) \simeq \operatorname{Hom}(G, \mathbb Q/\mathbb Z)$. -/
noncomputable def h2IntToHom :
    groupCohomology (seqZQ G).X₁ 2 ⟶ ModuleCat.of ℤ (Additive G →+ QZ) :=
  @CategoryTheory.inv _ _ _ _ (δ (seqZQ_shortExact G) 1 2 rfl) lemma_3_3c ≫
    (H1IsoOfIsTrivial (seqZQ G).X₃).hom

/-- **The invariant map** of a $G$-map $v : M \to \mathbb Z$ and $\sigma \in G$ (Milne, p. 99, definition in prose):
$H^2(G, M) \xrightarrow{v} H^2(G, \mathbb Z) \simeq \operatorname{Hom}(G, \mathbb Q/\mathbb Z)
\xrightarrow{f \mapsto f(\sigma)} \mathbb Q/\mathbb Z$. -/
@[kb "milne2020cft" "v4.03, Ch. III, §1, the invariant map (composite), p. 99"]
noncomputable def invOf (M : Rep ℤ G) (v : M ⟶ (seqZQ G).X₁) (σ : G) : groupCohomology M 2 →+ QZ where
  toFun x := h2IntToHom.hom ((groupCohomology.map (MonoidHom.id G) v 2).hom x) (Additive.ofMul σ)
  map_zero' := by simp
  map_add' x y := by simp

theorem mem_qzOver_of_nsmul (n : ℕ) (hn : 0 < n) (y : QZ) (h : n • y = 0) : y ∈ qzOver n := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective y
  change n • qz q = 0 at h
  rw [qz_nsmul, qz_eq_zero_iff] at h
  obtain ⟨z, hz⟩ := h
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨z, ?_⟩
  rw [qz_zsmul, hz]
  change qz _ = qz _
  congr 1
  have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Evaluation at a generator $\sigma$ of a cyclic group of order $n$ is injective on
$\operatorname{Hom}(G, \mathbb Q/\mathbb Z)$, with image $\frac1n\mathbb Z/\mathbb Z$. -/
theorem eval_injective {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    Function.Injective (fun f : Additive G →+ QZ => f (Additive.ofMul σ)) := by
  intro f g hfg
  refine AddMonoidHom.ext fun τ => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hσ (Additive.toMul τ))
  have : τ = k • Additive.ofMul σ := by rw [← ofMul_zpow, hk]; rfl
  simp only at hfg
  rw [this, map_zsmul, map_zsmul, hfg]

theorem eval_range {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (y : QZ) :
    (∃ f : Additive G →+ QZ, f (Additive.ofMul σ) = y) ↔ y ∈ qzOver (Nat.card G) := by
  have hn : 0 < Nat.card G := Nat.card_pos
  constructor
  · rintro ⟨f, rfl⟩
    apply mem_qzOver_of_nsmul _ hn
    rw [← map_nsmul, ← ofMul_pow, pow_card_eq_one', ofMul_one, map_zero]
  · intro hy
    have hy' : (Nat.card G : ℤ) • y = 0 := by
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hy
      have hq : qz ((Nat.card G : ℚ) * (1 / (Nat.card G : ℚ))) = 0 :=
        (qz_eq_zero_iff _).2 ⟨1, by push_cast; field_simp⟩
      rw [smul_comm, natCast_zsmul, qz_nsmul, hq, smul_zero]
    have hg : ∀ x : Additive G, x ∈ AddSubgroup.zmultiples (Additive.ofMul σ) := fun x => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hσ (Additive.toMul x))
      exact AddSubgroup.mem_zmultiples_iff.2 ⟨k, by rw [← ofMul_zpow, hk]; rfl⟩
    let e := zmodAddEquivOfGenerator (G := Additive G) hg (n := Nat.card G) rfl
    let φ : ZMod (Nat.card G) →+ QZ := ZMod.lift _ ⟨zmultiplesHom QZ y, by simpa using hy'⟩
    refine ⟨φ.comp e.symm.toAddMonoidHom, ?_⟩
    have h1 : e.symm (Additive.ofMul σ) = ((1 : ℤ) : ZMod (Nat.card G)) := by
      rw [Int.cast_one]; exact zmodAddEquivOfGenerator_symm_apply_generator hg rfl
    change φ (e.symm (Additive.ofMul σ)) = y
    rw [h1, ZMod.lift_coe]
    simp

/-- $H^2(G, \mathbb Z) \to \operatorname{Hom}(G, \mathbb Q/\mathbb Z)$ is bijective. -/
theorem h2IntToHom_bijective {G : Type} [Group G] [Fintype G] :
    Function.Bijective (h2IntToHom (G := G)).hom := by
  let e := (@asIso _ _ _ _ (δ (seqZQ_shortExact G) 1 2 rfl) lemma_3_3c).symm ≪≫
    H1IsoOfIsTrivial (seqZQ G).X₃
  exact ConcreteCategory.bijective_of_isIso e.hom

end Generic

/-! ## Local definitions -/

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **The normalized valuation** $\mathrm{ord}_M : M^\times \to \mathbb Z$ of a finite extension $M$ of $K$,
characterized by: surjective, kernel $U_M$, nonnegative on $\mathcal O_M$; it is invariant under
$\operatorname{Gal}(M/K)$ (recorded as a condition; it follows from uniqueness). -/
@[kb "milne2020cft" "v4.03, Ch. III, §1, the valuation ord_L, p. 99"]
structure IsNormalizedOrd (M : IntermediateField K Ω) (v : Additive Mˣ →+ ℤ) : Prop where
  ker : ∀ x : Mˣ, v (Additive.ofMul x) = 0 ↔ x ∈ unitsL M
  surj : Function.Surjective v
  nonneg : ∀ x : Mˣ, (x : M) ∈ integers M → 0 ≤ v (Additive.ofMul x)
  gal : ∀ (σ : Gal(M/K)) (x : Mˣ), v (Additive.ofMul (σ • x)) = v (Additive.ofMul x)

/-- $\mathrm{ord}_M$ as a map of $\operatorname{Gal}(M/K)$-modules $M^\times \to \mathbb Z$. -/
noncomputable def ordRep {M : IntermediateField K Ω} {v : Additive Mˣ →+ ℤ} (hv : IsNormalizedOrd M v) :
    Rep.ofAlgebraAutOnUnits K M ⟶ (seqZQ Gal(M/K)).X₁ :=
  Rep.ofHom ⟨v.toIntLinearMap, fun σ => by
    ext x
    exact hv.gal σ (Additive.toMul x)⟩

/-- $\mathrm{ord}_M$ as a map of $H$-modules, $H \subseteq \operatorname{Gal}(M/K)$. -/
noncomputable def ordRepRel {M : IntermediateField K Ω} {v : Additive Mˣ →+ ℤ} (hv : IsNormalizedOrd M v)
    (H : Subgroup Gal(M/K)) : res H.subtype (Rep.ofAlgebraAutOnUnits K M) ⟶ (seqZQ H).X₁ :=
  Rep.ofHom ⟨v.toIntLinearMap, fun σ => by
    ext x
    exact hv.gal σ (Additive.toMul x)⟩

/-- **The invariant map** $\mathrm{inv}_{M/K} : H^2(M/K) \to \mathbb Q/\mathbb Z$ (Milne, p. 99, definition in
prose) for a finite Galois extension $M/K$, a normalized valuation $v = \mathrm{ord}_M$ and an element $\sigma$
(Milne: $M/K$ unramified and $\sigma = \mathrm{Frob}_{M/K}$). -/
@[kb "milne2020cft" "v4.03, Ch. III, §1, definition of the invariant map inv_{L/K}, p. 99"]
noncomputable def invK (M : IntermediateField K Ω) [FiniteDimensional K M] {v : Additive Mˣ →+ ℤ}
    (hv : IsNormalizedOrd M v) (σ : Gal(M/K)) : H2 M →+ QZ :=
  invOf (Rep.ofAlgebraAutOnUnits K M) (ordRep hv) σ

/-- Milne's $H^2(M/F) = H^2(\operatorname{Gal}(M/F), M^\times)$ for $F = M^H$, $H \subseteq \operatorname{Gal}(M/K)$. -/
noncomputable abbrev H2rel (M : IntermediateField K Ω) (H : Subgroup Gal(M/K)) : ModuleCat ℤ :=
  groupCohomology (res H.subtype (Rep.ofAlgebraAutOnUnits K M)) 2

/-- The relative invariant map $\mathrm{inv}_{M/F}$, $F = M^H$, built from $v = \mathrm{ord}_M$ and $\sigma \in H$
(Milne: $M/F$ unramified, $\sigma = \mathrm{Frob}_{M/F}$). -/
noncomputable def invRel (M : IntermediateField K Ω) [FiniteDimensional K M] {v : Additive Mˣ →+ ℤ}
    (hv : IsNormalizedOrd M v) (H : Subgroup Gal(M/K)) (σ : H) : H2rel M H →+ QZ :=
  letI := Fintype.ofFinite H
  invOf (res H.subtype (Rep.ofAlgebraAutOnUnits K M)) (ordRepRel hv H) σ

/-- The fixed field $F = M^H \subseteq \Omega$ of a subgroup $H \subseteq \operatorname{Gal}(M/K)$. -/
noncomputable def baseOf (M : IntermediateField K Ω) (H : Subgroup Gal(M/K)) : IntermediateField K Ω :=
  (IntermediateField.fixedField H).map M.val

/-- **Frobenius element of $M/F$**, $F = M^H$: $\sigma \in H$ with $\sigma a \equiv a^{q_F} \pmod{\mathfrak m_M}$ for
all $a \in \mathcal O_M$, where $q_F$ is the order of the residue field of $F$ (Chapter I's `residueFieldL`). For
$H = \operatorname{Gal}(M/K)$ and $M/K$ unramified this is Chapter I's `IsFrobenius`. -/
@[kb "milne2020cft" "v4.03, Ch. III, §1, Frobenius element Frob_{L/K}, p. 99"]
def IsFrobeniusOver (M : IntermediateField K Ω) (H : Subgroup Gal(M/K)) (σ : Gal(M/K)) : Prop :=
  σ ∈ H ∧ ∀ a ∈ integers M, ∃ y ∈ maxIdealL M,
    (y : M) = σ a - a ^ Nat.card (residueFieldL (baseOf M H))

/-- **$M/F$ is unramified**, $F = M^H$ ($M/F$ Galois with group $H$): the inertia group
$\{\sigma \in H : \sigma a \equiv a \bmod \mathfrak m_M \ \forall a \in \mathcal O_M\}$ is trivial. -/
def IsUnramifiedOver (M : IntermediateField K Ω) (H : Subgroup Gal(M/K)) : Prop :=
  ∀ σ ∈ H, (∀ a ∈ integers M, ∃ y ∈ maxIdealL M, (y : M) = σ a - a) → σ = 1

/-! ## Inflation and restriction -/

/-- **Inflation** $H^2(M/F) \to H^2(E/F)$ for $M \subseteq E$ finite Galois over $K$ and $F = M^H$ (Milne, II, 1.27
(c)): $\operatorname{Gal}(E/F) = H' = \{\tau : \tau|_M \in H\}$ maps onto $H$ by restriction, and
$M^\times \subseteq E^\times$. -/
noncomputable def inflRel {M E : IntermediateField K Ω} (h : M ≤ E) [Normal K M] (H : Subgroup Gal(M/K)) :
    H2rel M H ⟶ H2rel E (H.comap (galRestrict h)) :=
  groupCohomology.map ((galRestrict h).subgroupComap H)
    (Rep.ofHom ⟨(AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive
      (Units.map (IntermediateField.inclusion h).toRingHom.toMonoidHom))), fun σ => by
    ext x
    apply Units.ext
    apply Subtype.ext
    exact galRestrict_apply h σ.1 ((Additive.toMul (α := Mˣ) x : Mˣ) : M)⟩) 2

/-- **Restriction** $H^2(M/F) \to H^2(M/F')$ for $F \subseteq F' \subseteq M$, i.e. $H' \subseteq H$ (Milne, II,
1.27 (b)). -/
noncomputable def resRel (M : IntermediateField K Ω) {H' H : Subgroup Gal(M/K)} (h : H' ≤ H) :
    H2rel M H ⟶ H2rel M H' :=
  groupCohomology.map (Subgroup.inclusion h) (𝟙 _) 2

end NumberFieldKB.MilneCFT.Ch3
