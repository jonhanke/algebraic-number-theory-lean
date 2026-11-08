import NumberFieldKB.MilneCFT.LocalCFT.Basic

/-!
# Local class field theory: consequences of the main theorems (Milne, *Class Field Theory*, Chapter I, §1)

From the conditions of Theorem 1.1 (`IsLocalArtinMap`) alone: the index formula
$(K^\times : \mathrm{Nm}(L^\times)) = [L:K]$ (Theorem 1.1 (b)) and Corollary 1.2 (a)–(e). From the named statements
`LocalReciprocityExistence`, `NormGroupOpenInput` (Lemma 1.3), `LocalExistenceInput` (Theorem 1.4) and
`UnramifiedInput`: Theorem 1.4 in full (`isNormGroup_iff`), Corollary 1.5, Theorem 1.13 (uniqueness of the Artin map)
and Theorem 1.1 (existence and uniqueness, `localReciprocityLaw`).

Also the definitions in prose of §1: the unit filtration $U_K \supseteq 1 + \mathfrak m \supseteq 1 + \mathfrak m^2
\supseteq \cdots$ (Milne 1.9, display (7)), the conductor (1.9) and the norm topology (1.10).
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-! ## Composita and intersections of finite abelian extensions -/

instance finiteDimensional_inf (L L' : IntermediateField K Ω) [FiniteDimensional K L] :
    FiniteDimensional K ↑(L ⊓ L') :=
  Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : L ⊓ L' ≤ L)).toLinearMap
    (IntermediateField.inclusion (inf_le_left : L ⊓ L' ≤ L)).injective

instance isAbelianGalois_inf (L L' : IntermediateField K Ω) [IsAbelianGalois K L] [FiniteDimensional K L] :
    IsAbelianGalois K ↑(L ⊓ L') :=
  IsAbelianGalois.of_algHom (IntermediateField.inclusion (inf_le_left : L ⊓ L' ≤ L))

/-- The compositum $LL'$ of two finite abelian extensions. -/
def FiniteAbelianExt.sup (L L' : FiniteAbelianExt K Ω) : FiniteAbelianExt K Ω where
  toField := L.toField ⊔ L'.toField

/-- The intersection $L \cap L'$ of two finite abelian extensions. -/
def FiniteAbelianExt.inf (L L' : FiniteAbelianExt K Ω) : FiniteAbelianExt K Ω where
  toField := L.toField ⊓ L'.toField

/-! ## Theorem 1.1 (b), index formula, and Corollary 1.2 -/

section ArtinMap

variable {φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)} (hφ : IsLocalArtinMap φ)
include hφ

/-- **Theorem 1.1 (b), "in particular"** (Milne, *CFT*, I): $(K^\times : \mathrm{Nm}(L^\times)) = [L:K]$. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1 (b), index formula"]
theorem index_normGroup (L : FiniteAbelianExt K Ω) :
    (normGroup L.toField).index = Module.finrank K L.toField := by
  rw [← hφ.ker_eq L, Subgroup.index_ker, MonoidHom.range_eq_top.2 (hφ.surjective L), Subgroup.card_top,
    IsGalois.card_aut_eq_finrank]

/-- Helper: $L \subseteq L' \Rightarrow \mathrm{Nm}(L'^\times) \subseteq \mathrm{Nm}(L^\times)$ (via the Artin map). -/
theorem normGroup_anti_aux {L L' : FiniteAbelianExt K Ω} (h : L.toField ≤ L'.toField) :
    normGroup L'.toField ≤ normGroup L.toField := by
  intro a ha
  rw [← hφ.ker_eq] at ha ⊢
  rw [MonoidHom.mem_ker] at ha ⊢
  rw [← hφ.compat L L' h a, ha, map_one]

/-- Helper: Corollary 1.2 (c), proved before (b) because (b) uses it. -/
theorem normGroup_sup_aux (L L' : FiniteAbelianExt K Ω) :
    normGroup (L.toField ⊔ L'.toField) = normGroup L.toField ⊓ normGroup L'.toField := by
  apply le_antisymm
  · exact le_inf (normGroup_anti_aux hφ (L := L) (L' := L.sup L') le_sup_left)
      (normGroup_anti_aux hφ (L := L') (L' := L.sup L') le_sup_right)
  · intro a ha
    have h1 : φ L a = 1 := by
      have : a ∈ (φ L).ker := by rw [hφ.ker_eq]; exact ha.1
      exact this
    have h2 : φ L' a = 1 := by
      have : a ∈ (φ L').ker := by rw [hφ.ker_eq]; exact ha.2
      exact this
    change a ∈ normGroup (L.sup L').toField
    rw [← hφ.ker_eq, MonoidHom.mem_ker]
    apply IntermediateField.restrictNormalHomSupProd_injective L.toField L'.toField
    erw [map_one]
    refine Prod.ext ?_ ?_
    · exact (hφ.compat L (L.sup L') le_sup_left a).trans h1
    · exact (hφ.compat L' (L.sup L') le_sup_right a).trans h2

/-- **Corollary 1.2 (b)** (Milne, *CFT*, I): $L \subseteq L' \iff \mathrm{Nm}(L^\times) \supseteq \mathrm{Nm}(L'^\times)$. -/
@[kb "milne2020cft" "Ch. I, Corollary 1.2 (b)"]
theorem le_iff_normGroup_le (L L' : FiniteAbelianExt K Ω) :
    L.toField ≤ L'.toField ↔ normGroup L'.toField ≤ normGroup L.toField := by
  refine ⟨normGroup_anti_aux hφ, fun h => ?_⟩
  have h1 : normGroup (L.toField ⊔ L'.toField) = normGroup L'.toField := by
    rw [normGroup_sup_aux hφ]; exact inf_eq_right.2 h
  have h2 : Module.finrank K ↑(L.toField ⊔ L'.toField) = Module.finrank K L'.toField := by
    calc _ = (normGroup (L.sup L').toField).index := (index_normGroup hφ (L.sup L')).symm
      _ = (normGroup L'.toField).index := by rw [show normGroup (L.sup L').toField = _ from h1]
      _ = _ := index_normGroup hφ L'
  have h3 : L'.toField = L.toField ⊔ L'.toField :=
    IntermediateField.eq_of_le_of_finrank_eq (le_sup_right) h2.symm
  rw [h3]; exact le_sup_left

/-- **Corollary 1.2 (a)** (Milne, *CFT*, I): $L \mapsto \mathrm{Nm}(L^\times)$ is injective on finite abelian
extensions (it is onto the norm groups by definition). -/
@[kb "milne2020cft" "Ch. I, Corollary 1.2 (a)"]
theorem normGroup_injective {L L' : FiniteAbelianExt K Ω} (h : normGroup L.toField = normGroup L'.toField) :
    L.toField = L'.toField :=
  le_antisymm ((le_iff_normGroup_le hφ L L').2 h.ge) ((le_iff_normGroup_le hφ L' L).2 h.le)

/-- **Corollary 1.2 (c)** (Milne, *CFT*, I): $\mathrm{Nm}((LL')^\times) = \mathrm{Nm}(L^\times) \cap
\mathrm{Nm}(L'^\times)$. -/
@[kb "milne2020cft" "Ch. I, Corollary 1.2 (c)"]
theorem normGroup_sup (L L' : FiniteAbelianExt K Ω) :
    normGroup (L.toField ⊔ L'.toField) = normGroup L.toField ⊓ normGroup L'.toField :=
  normGroup_sup_aux hφ L L'

/-- **Corollary 1.2 (e)** (Milne, *CFT*, I): every subgroup of $K^\times$ containing a norm group is a norm group. -/
@[kb "milne2020cft" "Ch. I, Corollary 1.2 (e)"]
theorem isNormGroup_of_le (L : FiniteAbelianExt K Ω) {H : Subgroup Kˣ} (hH : normGroup L.toField ≤ H) :
    IsNormGroup K Ω H := by
  classical
  let S : Subgroup Gal(L.toField/K) := H.map (φ L)
  let E : IntermediateField K L.toField := IntermediateField.fixedField S
  let M : IntermediateField K Ω := E.map L.toField.val
  have : FiniteDimensional K M := (E.equivMap L.toField.val).toLinearEquiv.finiteDimensional
  have : IsAbelianGalois K M := IsAbelianGalois.of_algHom (E.equivMap L.toField.val).symm.toAlgHom
  have hML : M ≤ L.toField := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := E.mem_map.1 hx
    exact y.2
  have key : ∀ τ : Gal(L.toField/K), galRestrict hML τ = 1 ↔ τ ∈ S := by
    intro τ
    have h0 : τ ∈ S ↔ τ ∈ IntermediateField.fixingSubgroup E := by
      rw [IntermediateField.fixingSubgroup_fixedField]
    rw [h0, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h y hy
      have hx : L.toField.val y ∈ M := E.mem_map.2 ⟨y, hy, rfl⟩
      have h1 := galRestrict_apply hML τ ⟨L.toField.val y, hx⟩
      rw [h] at h1
      exact Subtype.ext h1.symm
    · intro h
      ext x
      rw [galRestrict_apply, AlgEquiv.one_apply]
      obtain ⟨y, hy, hyx⟩ := E.mem_map.1 x.2
      have hxy : IntermediateField.inclusion hML x = y := Subtype.ext hyx.symm
      rw [hxy, h y hy]
      exact hyx
  refine ⟨⟨M⟩, ?_⟩
  ext a
  change a ∈ normGroup M ↔ a ∈ H
  rw [← hφ.ker_eq ⟨M⟩, MonoidHom.mem_ker, ← hφ.compat ⟨M⟩ ⟨L.toField⟩ hML a, key]
  constructor
  · rintro ⟨h, hh, hha⟩
    have : h⁻¹ * a ∈ normGroup L.toField := by
      rw [← hφ.ker_eq L, MonoidHom.mem_ker, map_mul, map_inv, hha, inv_mul_cancel]
    have := mul_mem hh (hH this)
    simpa using this
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- **Corollary 1.2 (d)** (Milne, *CFT*, I): $\mathrm{Nm}((L \cap L')^\times) = \mathrm{Nm}(L^\times) \cdot
\mathrm{Nm}(L'^\times)$. -/
@[kb "milne2020cft" "Ch. I, Corollary 1.2 (d)"]
theorem normGroup_inf (L L' : FiniteAbelianExt K Ω) :
    normGroup (L.toField ⊓ L'.toField) = normGroup L.toField ⊔ normGroup L'.toField := by
  obtain ⟨M, hM⟩ := isNormGroup_of_le hφ L (le_sup_left : normGroup L.toField ≤ normGroup L.toField ⊔ normGroup L'.toField)
  have hML : M.toField ≤ L.toField :=
    (le_iff_normGroup_le hφ M L).2 (hM ▸ le_sup_left)
  have hML' : M.toField ≤ L'.toField :=
    (le_iff_normGroup_le hφ M L').2 (hM ▸ le_sup_right)
  apply le_antisymm
  · rw [← hM]
    exact normGroup_anti_aux hφ (L := M) (L' := L.inf L') (le_inf hML hML')
  · exact sup_le (normGroup_anti_aux hφ (L := L.inf L') (L' := L) inf_le_left)
      (normGroup_anti_aux hφ (L := L.inf L') (L' := L') inf_le_right)

end ArtinMap

/-! ## Theorem 1.4 and Corollary 1.5 from the named statements -/

/-- **Theorem 1.4, local existence theorem** (Milne, *CFT*, I): the norm groups in $K^\times$ are exactly the open
subgroups of finite index. Conditional on Theorem 1.1 (existence) and the hard half of Theorem 1.4; Lemma 1.3 is
proved (`normGroupOpenInput`, from Tau Ceti). -/
@[kb "milne2020cft" "Ch. I, Theorem 1.4"]
theorem isNormGroup_iff (h1 : LocalReciprocityExistence K Ω)
    (h4 : LocalExistenceInput K Ω) (H : Subgroup Kˣ) :
    IsNormGroup K Ω H ↔ IsOpen (H : Set Kˣ) ∧ H.FiniteIndex := by
  obtain ⟨φ, hφ⟩ := h1.exists_artin
  constructor
  · rintro ⟨L, rfl⟩
    have hfi : (normGroup L.toField).FiniteIndex :=
      ⟨by rw [index_normGroup hφ L]; exact Module.finrank_pos.ne'⟩
    exact ⟨(normGroupOpenInput K Ω).isOpen L.toField hfi, hfi⟩
  · rintro ⟨ho, hfi⟩
    exact h4.isNormGroup H ho hfi

/-- **Corollary 1.5 (a)** (Milne, *CFT*, I): $L \mapsto \mathrm{Nm}(L^\times)$ is a bijection from the finite
abelian extensions of $K$ onto the open subgroups of finite index of $K^\times$. ((b)–(d) of Corollary 1.5 are
`le_iff_normGroup_le`, `normGroup_sup`, `normGroup_inf`.) -/
@[kb "milne2020cft" "Ch. I, Corollary 1.5 (a)"]
theorem existsUnique_normGroup_eq (h1 : LocalReciprocityExistence K Ω)
    (h4 : LocalExistenceInput K Ω) (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ)) (hfi : H.FiniteIndex) :
    ∃ L : FiniteAbelianExt K Ω, normGroup L.toField = H ∧
      ∀ L' : FiniteAbelianExt K Ω, normGroup L'.toField = H → L'.toField = L.toField := by
  obtain ⟨φ, hφ⟩ := h1.exists_artin
  obtain ⟨L, hL⟩ := h4.isNormGroup H hH hfi
  exact ⟨L, hL, fun L' h' => normGroup_injective hφ (h'.trans hL.symm)⟩

/-- **Corollary 1.5 (e)** (Milne, *CFT*, I): a subgroup of $K^\times$ containing an open subgroup of finite index is
open of finite index. -/
@[kb "milne2020cft" "Ch. I, Corollary 1.5 (e)"]
theorem isOpen_finiteIndex_of_le {H H' : Subgroup Kˣ} (hH : IsOpen (H : Set Kˣ)) (hfi : H.FiniteIndex)
    (hle : H ≤ H') : IsOpen (H' : Set Kˣ) ∧ H'.FiniteIndex :=
  ⟨Subgroup.isOpen_mono hle hH, Subgroup.finiteIndex_of_le hle⟩

/-! ## The unit filtration -/

variable (K) in
/-- **The unit filtration** (Milne, *CFT*, I, 1.9, display (7)): $U^{(0)} = U_K = \mathcal O_K^\times$ and
$U^{(n)} = 1 + \mathfrak m^n$ for $n \ge 1$, as subgroups of $K^\times$. -/
@[kb "milne2020cft" "Ch. I, 1.9, display (7) (the groups U_K ⊇ 1 + m ⊇ 1 + m^n)"]
def unitFiltration (n : ℕ) : Subgroup Kˣ where
  carrier := {x | ∃ u : 𝒪[K], (u : K) = x ∧ ∃ w : 𝒪[K], (w : K) = (x⁻¹ : Kˣ) ∧ u - 1 ∈ 𝓂[K] ^ n}
  mul_mem' := by
    rintro x y ⟨u, hu, w, hw, huw⟩ ⟨v, hv, z, hz, hvz⟩
    refine ⟨u * v, by simp [hu, hv], w * z, by simp [hw, hz, mul_comm], ?_⟩
    have : u * v - 1 = (u - 1) * v + (v - 1) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ huw) hvz
  one_mem' := ⟨1, by simp, 1, by simp, by simp⟩
  inv_mem' := by
    rintro x ⟨u, hu, w, hw, huw⟩
    refine ⟨w, hw, u, by simp [hu], ?_⟩
    have huw1 : u * w = 1 := by
      apply Subtype.val_injective
      simp [hu, hw]
    have : w - 1 = -((u - 1) * w) := by linear_combination huw1
    rw [this]
    exact Ideal.neg_mem_iff _ |>.2 (Ideal.mul_mem_right _ _ huw)

/-- **The conductor** of a finite abelian extension $L/K$ (Milne, *CFT*, I, 1.9): $0$ if $L/K$ is unramified,
otherwise the least $f$ with $1 + \mathfrak m^f \subseteq \ker\phi_{L/K} = \mathrm{Nm}(L^\times)$. (Milne defines it
with the kernel of the Artin map; by Theorem 1.1 (b) this kernel is the norm group, which is used here so that the
definition does not depend on the Artin map.) -/
@[kb "milne2020cft" "Ch. I, 1.9 (conductor of a finite abelian extension)"]
def conductor (L : FiniteAbelianExt K Ω) : ℕ :=
  open Classical in
  if IsUnramifiedExt L.toField then 0 else sInf {f : ℕ | unitFiltration K f ≤ normGroup L.toField}

variable (K Ω) in
/-- **The norm topology** on $K^\times$ (Milne, *CFT*, I, 1.10): the topology for which the norm groups form a
fundamental system of neighbourhoods of $1$, i.e. generated by the cosets of norm groups. -/
@[kb "milne2020cft" "Ch. I, 1.10 (norm topology)", instance_reducible]
def normTopology : TopologicalSpace Kˣ :=
  TopologicalSpace.generateFrom
    {S | ∃ (L : FiniteAbelianExt K Ω) (a : Kˣ), S = (fun x => a * x) '' (normGroup L.toField : Set Kˣ)}

end NumberFieldKB.MilneCFT.LocalCFT
