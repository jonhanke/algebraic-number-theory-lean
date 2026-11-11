import NumberFieldKB.MilneCFT.GlobalUnconditional
import NumberFieldKB.MilneCFT.Ch5Unconditional
import NumberFieldKB.MilneCFT.Ch5Complements
import NumberFieldKB.MilneCFT.Intro.Theorems
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Takagi's and Furtwängler's theorems, unconditional (Milne, *Class Field Theory*, Introduction)

* **Theorem 0.5 (Takagi)** (`takagiTheorem`) and **Theorem 0.4 (Furtwängler)** (`furtwanglerTheorem`) are proved from
  Artin reciprocity (`artinReciprocity`), the ray class field (`exists_rayClassField'`) and the Bauer-type comparison of
  Galois extensions through their split primes (`nonempty_algHom_of_splitPrimes_diff_finite`).

*Construction.* For a subgroup $H \subseteq C_\mathfrak m$ let $L_\mathfrak m$ be the ray class field with Artin
isomorphism $e : C_\mathfrak m \cong \mathrm{Gal}(L_\mathfrak m/K)$ and $F$ the fixed field of $e(H)$. Then $F$ is a
class field for $(\mathfrak m, H)$ with $\mathrm{Gal}(F/K) \cong C_\mathfrak m/H$.
*Uniqueness.* Two class fields for $(\mathfrak m, H)$ have the same split primes outside the finite set of primes
dividing $\mathfrak m_0$, hence are $K$-isomorphic (`classField_algEquiv`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField
open scoped IsMulCommutative

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## Uniqueness -/

/-- **Uniqueness of class fields**: two class fields for the same `(m, H)` are `K`-isomorphic. -/
theorem classField_algEquiv {m : Modulus K} {H : Subgroup (RayClassGroup m)} {L L' : Type}
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [Field L'] [NumberField L'] [Algebra K L'] [IsGalois K L']
    (hL : IsClassField L m H) (hL' : IsClassField L' m H) : Nonempty (L ≃ₐ[K] L') := by
  have hS : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  obtain ⟨f⟩ := nonempty_algHom_of_splitPrimes_diff_finite (K := K) L L' m.finiteSupport hS
    (fun v hv => (hL.splits_iff v (show ¬ v.asIdeal ∣ m.finite from hv.2)).2
      ((hL'.splits_iff v (show ¬ v.asIdeal ∣ m.finite from hv.2)).1 hv.1))
  obtain ⟨g⟩ := nonempty_algHom_of_splitPrimes_diff_finite (K := K) L' L m.finiteSupport hS
    (fun v hv => (hL'.splits_iff v (show ¬ v.asIdeal ∣ m.finite from hv.2)).2
      ((hL.splits_iff v (show ¬ v.asIdeal ∣ m.finite from hv.2)).1 hv.1))
  exact ⟨AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective₂ f g).1⟩

/-! ## Subfields of the ray class field -/

/-- Unramifiedness outside `m` passes to subfields. -/
theorem unramifiedOutside_subfield {Lm : Type} [Field Lm] [NumberField Lm] [Algebra K Lm] [IsAbelianGalois K Lm]
    (F : IntermediateField K Lm) {m : Modulus K} (h : UnramifiedOutside Lm m) : UnramifiedOutside F m := by
  refine ⟨fun v hv => unramifiedPrimes_subset_of_tower K F Lm (h.1 v hv), fun w hw hram => ?_⟩
  obtain ⟨hr, w', hw', hc⟩ := hram
  obtain ⟨w'', rfl⟩ := InfinitePlace.comap_surjective (K := Lm) w'
  refine h.2 w hw ⟨hr, w'', ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq K F Lm, InfinitePlace.comap_comp]
    exact hw'
  · rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hreal
    exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.IsReal.comap _ hreal)

/-- Frobenius elements are compatible with an isomorphism onto a subfield of an abelian extension. -/
theorem autCongr_artinFrob {Lm : Type} [Field Lm] [NumberField Lm] [Algebra K Lm] [IsAbelianGalois K Lm]
    (F : IntermediateField K Lm) (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (σ : L ≃ₐ[K] F) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ unramifiedPrimes K Lm) :
    AlgEquiv.autCongr σ (artinFrob L v) = artinFrob F v := by
  let φ : L →ₐ[K] Lm := F.val.comp σ.toAlgHom
  letI : Algebra L Lm := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K L Lm := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  rw [artinFrob_restrict L Lm v hv, artinFrob_restrict F Lm v hv]
  ext x
  have h := AlgEquiv.restrictNormal_commutes (artinFrob Lm v) L (σ.symm x)
  have h2 : algebraMap L Lm (σ.symm x) = (x : Lm) := by
    show φ (σ.symm x) = _
    simp [φ]
  simp only [AlgEquiv.restrictNormalHom_apply, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
  rw [h2] at h
  have h3 : ((σ (AlgEquiv.restrictNormal (artinFrob Lm v) L (σ.symm x)) : F) : Lm) =
      algebraMap L Lm (AlgEquiv.restrictNormal (artinFrob Lm v) L (σ.symm x)) := rfl
  exact h3.trans h

/-- **Construction**: for every `(m, H)` there is an abelian extension `Lm` (the ray class field) and a subfield `F`
with `Gal(F/K) ≅ C_m / H`, a class field for `(m, H)`. -/
theorem exists_subfield_classField (m : Modulus K) (H : Subgroup (RayClassGroup m)) :
    ∃ (Lm : Type) (_ : Field Lm) (_ : NumberField Lm) (_ : Algebra K Lm) (_ : IsAbelianGalois K Lm)
      (F : IntermediateField K Lm) (Φ : RayClassGroup m →* Gal(F/K)),
      UnramifiedOutside Lm m ∧ UnramifiedOutside F m ∧ Function.Surjective Φ ∧ Φ.ker = H ∧
      (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), Φ (rayClass m v hv) = artinFrob F v) ∧
      IsClassField F m H := by
  obtain ⟨Lm, _, _, _, _, e, hunr, he⟩ := exists_rayClassField' m
  obtain ⟨F, hFix⟩ : ∃ F : IntermediateField K Lm,
      F.fixingSubgroup = H.map (e : RayClassGroup m →* Gal(Lm/K)) :=
    ⟨IntermediateField.fixedField (H.map (e : RayClassGroup m →* Gal(Lm/K))),
      IntermediateField.fixingSubgroup_fixedField _⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : RayClassGroup m →* Gal(F/K),
      Φ = (AlgEquiv.restrictNormalHom F).comp (e : RayClassGroup m →* Gal(Lm/K)) := ⟨_, rfl⟩
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Lm y
    exact ⟨e.symm g, by rw [hΦ]; simp⟩
  have hker : Φ.ker = H := by
    ext c
    rw [hΦ, MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, hFix]
    exact ⟨fun h => by
      obtain ⟨d, hd, hdc⟩ := h
      exact (e.injective hdc) ▸ hd, fun h => ⟨c, h, rfl⟩⟩
  have hfrob : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite),
      Φ (rayClass m v hv) = artinFrob F v := by
    intro v hv
    rw [hΦ, MonoidHom.comp_apply, artinFrob_restrict F Lm v (hunr.1 v hv)]
    exact congrArg _ (he v hv)
  have hUF : UnramifiedOutside F m := unramifiedOutside_subfield F hunr
  refine ⟨Lm, inferInstance, inferInstance, inferInstance, inferInstance, F, Φ, hunr, hUF, hsurj, hker, hfrob,
    ⟨fun σ τ => mul_comm σ τ, fun v hv => hUF.1 v hv, fun v hv => ?_⟩⟩
  rw [mem_splitPrimes_iff_artinFrob_eq_one F v (hUF.1 v hv), ← hfrob v hv, ← MonoidHom.mem_ker, hker]

/-- A class field for `(m, H)`, as a type, together with the unramifiedness outside `m`. -/
theorem exists_classField_unramified (m : Modulus K) (H : Subgroup (RayClassGroup m)) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      IsClassField L m H ∧ UnramifiedOutside L m := by
  obtain ⟨Lm, _, _, _, _, F, Φ, -, hUF, -, -, -, hF⟩ := exists_subfield_classField m H
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, hF, hUF⟩

/-- **The Artin isomorphism of a class field**: `C_m / H ≅ Gal(L/K)`, sending the class of `[p]` to `(p, L/K)`. -/
theorem IsClassField.exists_equiv {m : Modulus K} {H : Subgroup (RayClassGroup m)} {L : Type}
    [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (hL : IsClassField L m H) :
    ∃ Ψ : RayClassGroup m ⧸ H ≃* Gal(L/K),
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite),
        Ψ (QuotientGroup.mk (rayClass m v hv)) = artinFrob L v := by
  obtain ⟨Lm, _, _, _, _, F, Φ, hU, -, hsurj, hker, hfrob, hF⟩ := exists_subfield_classField m H
  obtain ⟨σ⟩ := classField_algEquiv hL hF
  let ΨF : RayClassGroup m ⧸ H ≃* Gal(F/K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective Φ hsurj)
  refine ⟨ΨF.trans (AlgEquiv.autCongr σ).symm, fun v hv => ?_⟩
  have h1 : ΨF (QuotientGroup.mk (rayClass m v hv)) = Φ (rayClass m v hv) := rfl
  rw [MulEquiv.trans_apply, h1, hfrob v hv, MulEquiv.symm_apply_eq,
    ← autCongr_artinFrob F L σ v (hU.1 v hv)]

/-! ## Theorem 0.5 (Takagi) -/

/-- **Theorem 0.5 (Takagi)** (Milne, *Class Field Theory*, Introduction, Theorem 0.5), unconditional: class fields
exist and are unique, every finite abelian extension is a class field, and $\mathrm{Gal}(L/K) \cong C_\mathfrak m/H$
with $f(\mathfrak P/\mathfrak p)$ the order of $[\mathfrak p]$ in $C_\mathfrak m/H$. Proved from `artinReciprocity`,
`exists_rayClassField'` and the Bauer-type comparison `nonempty_algHom_of_splitPrimes_diff_finite`. -/
@[kb "milne2020cft" "Introduction, Theorem 0.5"]
theorem takagiTheorem (K : Type) [Field K] [NumberField K] : TakagiTheorem K where
  exists_classField m H := by
    obtain ⟨L, _, _, _, _, hL, -⟩ := exists_classField_unramified m H
    exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hL⟩
  unique m H L L' _ _ _ _ _ _ _ _ hL hL' := classField_algEquiv hL hL'
  isClassField_of_abelian L _ _ _ _ hab := isClassField_of_artin (artinReciprocity K) hab
  galois_equiv m H L _ _ _ _ hL := by
    haveI : IsAbelianGalois K L := { toIsMulCommutative := ⟨⟨hL.comm⟩⟩ }
    obtain ⟨Ψ, -⟩ := hL.exists_equiv
    exact ⟨Ψ.symm⟩
  inertiaDeg_eq m H L _ _ _ _ hL v hv Q := by
    haveI : IsAbelianGalois K L := { toIsMulCommutative := ⟨⟨hL.comm⟩⟩ }
    obtain ⟨Ψ, hΨ⟩ := hL.exists_equiv
    have hvu : v ∈ unramifiedPrimes K L := hL.unramified v hv
    rw [← orderOf_frobAt_eq v hvu Q, ← MulEquiv.orderOf_eq Ψ (QuotientGroup.mk (rayClass m v hv)), hΨ v hv,
      artinFrob_eq L v hvu Q]

/-! ## Theorem 0.4 (Furtwängler) -/

section Furtwangler

variable (K) in
/-- The subgroup of $C_{(1)}$ corresponding to a subgroup of the class group. -/
def oneRayGroup (H : Subgroup (ClassGroup (𝓞 K))) : Subgroup (RayClassGroup (Modulus.one K)) :=
  H.comap (rayClassGroupOneEquiv K : RayClassGroup (Modulus.one K) →* ClassGroup (𝓞 K))

theorem not_dvd_modulus_one (v : HeightOneSpectrum (𝓞 K)) : ¬ v.asIdeal ∣ (Modulus.one K).finite :=
  fun hv => v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd hv))

theorem mem_oneRayGroup_iff (H : Subgroup (ClassGroup (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) :
    rayClass (Modulus.one K) v (not_dvd_modulus_one v) ∈ oneRayGroup K H ↔ primeClass K v ∈ H := by
  show rayClassGroupOneEquiv K _ ∈ H ↔ _
  exact iff_of_eq (congrArg (· ∈ H)
    (rayClassGroupEquivClassGroup_rayClass (Modulus.one K) rfl rfl v (not_dvd_modulus_one v)))

theorem isClassField_one_of {H : Subgroup (ClassGroup (𝓞 K))} {L : Type} [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (hL : IsUnramifiedClassField (K := K) L H) :
    IsClassField L (Modulus.one K) (oneRayGroup K H) :=
  ⟨hL.comm, fun v _ => hL.unramified v, fun v _ =>
    (hL.splits_iff v).trans (mem_oneRayGroup_iff H v).symm⟩

theorem isUnramifiedClassField_of_one {H : Subgroup (ClassGroup (𝓞 K))} {L : Type} [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (hL : IsClassField L (Modulus.one K) (oneRayGroup K H))
    (hU : UnramifiedOutside L (Modulus.one K)) : IsUnramifiedClassField (K := K) L H := by
  refine ⟨hL.comm, fun v => hL.unramified v (not_dvd_modulus_one v), ⟨fun w' => ?_⟩, fun v => ?_⟩
  · by_contra hcon
    obtain ⟨hc, hr⟩ := InfinitePlace.isRamified_iff.1 hcon
    exact hU.2 (w'.comap (algebraMap K L)) (fun h => h) ⟨hr, w', rfl, hc⟩
  · exact (hL.splits_iff v (not_dvd_modulus_one v)).trans (mem_oneRayGroup_iff H v)

/-- The identification $C_{(1)}/H' \cong \mathrm{Cl}_K/H$. -/
def oneQuotientEquiv (H : Subgroup (ClassGroup (𝓞 K))) :
    RayClassGroup (Modulus.one K) ⧸ oneRayGroup K H ≃* ClassGroup (𝓞 K) ⧸ H :=
  QuotientGroup.congr _ _ (rayClassGroupOneEquiv K)
    (Subgroup.map_comap_eq_self_of_surjective (rayClassGroupOneEquiv K).surjective H)

/-- **Theorem 0.4 (Furtwängler)** (Milne, *Class Field Theory*, Introduction, Theorem 0.4), unconditional: it is the
case $\mathfrak m = (1)$ of Theorem 0.5 (`takagiTheorem`), together with Artin reciprocity for unramified
extensions (`unramifiedArtinReciprocityInput_of_artin`). -/
@[kb "milne2020cft" "Introduction, Theorem 0.4"]
theorem furtwanglerTheorem (K : Type) [Field K] [NumberField K] : FurtwanglerTheorem K where
  exists_classField H := by
    obtain ⟨L, _, _, _, _, hL, hU⟩ := exists_classField_unramified (Modulus.one K) (oneRayGroup K H)
    exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, isUnramifiedClassField_of_one hL hU⟩
  unique H L L' _ _ _ _ _ _ _ _ hL hL' := classField_algEquiv (isClassField_one_of hL) (isClassField_one_of hL')
  isClassField_of_unramified L _ _ _ _ hab hunr hinf := by
    obtain ⟨ψ, hψ⟩ := (unramifiedArtinReciprocityInput_of_artin (artinReciprocity K)).exists_artin L hab hunr hinf
    refine ⟨ψ.ker, hab, hunr, hinf, fun v => ?_⟩
    have Q : v.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
    rw [mem_splitPrimes_iff, splitsCompletelyIn_iff_frobAt_eq_one K L v (hunr v) Q, MonoidHom.mem_ker, hψ v Q]
  galois_equiv H L _ _ _ _ hL := by
    obtain ⟨e⟩ := (takagiTheorem K).galois_equiv _ _ L (isClassField_one_of hL)
    exact ⟨e.trans (oneQuotientEquiv H)⟩
  inertiaDeg_eq H L _ _ _ _ hL v Q := by
    rw [(takagiTheorem K).inertiaDeg_eq _ _ L (isClassField_one_of hL) v (not_dvd_modulus_one v) Q,
      ← MulEquiv.orderOf_eq (oneQuotientEquiv H)]
    congr 1
    show (QuotientGroup.mk (rayClassGroupOneEquiv K _) : ClassGroup (𝓞 K) ⧸ H) = _
    exact congrArg _
      (rayClassGroupEquivClassGroup_rayClass (Modulus.one K) rfl rfl v (not_dvd_modulus_one v))

end Furtwangler

end NumberFieldKB.MilneCFT
