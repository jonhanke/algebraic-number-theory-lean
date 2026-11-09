/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Ramification
public import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.Conductor.Basic
public import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Herbrand.ArtinConductor
public import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup

import NumberFieldKB.TauCetiPort.FieldTheory.Galois.Abelian.Basic
import NumberFieldKB.TauCetiPort.GroupTheory.Abelianization.Basic
import all NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.ArtinMap
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.Conductor.UpperNumbering

/-!
# Local conductors of a global abelian extension

This file collects, from a newer version of Tau Ceti than the one the neighbouring ported files
come from, the statements identifying the exponents of the conductor of a global abelian extension
with local conductor exponents (`exponent_abelianConductor`,
`exponent_abelianConductor_fixedField`, `exponent_abelianConductor_fixedField_ker`), together with
the helper lemmas they need that the older ported files lack:

* `TauCeti.GlobalNumberFields.Modulus.exponent_eq_multiplicity`,
* `TauCeti.GlobalNumberFields.Modulus.exists_exponent_eq_and_forall_ne`,
* `TauCeti.GlobalNumberFields.ideleCongruenceSubgroup.inv_ofAdicCompletion_mul_mem`,
* `OpenSubgroup.exponent_ideleClassConductor_le_iff`,
* `TauCeti.ClassFieldTheory.exponent_abelianConductor_le_iff`,
* `TauCeti.ClassFieldTheory.mem_normGroup_fixedField_iff`,
* `TauCeti.abelianization_of_restrictNormalHom_fixedField_eq_one_iff`.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace Modulus

/-- **The exponent is the multiplicity of the prime in the finite part**, in the normalization of
Mathlib's `multiplicity`, which `Ideal.finprod_heightOneSpectrum_pow_multiplicity` uses to recover
an ideal from its prime factors. -/
theorem exponent_eq_multiplicity (𝔪 : Modulus K) (v : HeightOneSpectrum (𝓞 K)) :
    𝔪.exponent v = multiplicity v.asIdeal 𝔪.finitePart := by
  rw [exponent_def, Ideal.count_associates_factors_eq 𝔪.finitePart_ne_zero v.isPrime v.ne_bot,
    v.count_normalizedFactors_eq_multiplicity 𝔪.finitePart_ne_bot]

/-- **Changing the exponent at one place.** For a modulus `𝔪`, a finite place `v` and `n : ℕ`,
there is a modulus with the infinite part of `𝔪`, with exponent `n` at `v`, and with the exponents
of `𝔪` at every other finite place. -/
theorem exists_exponent_eq_and_forall_ne (𝔪 : Modulus K) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ∃ 𝔫 : Modulus K, 𝔫.infinitePart = 𝔪.infinitePart ∧ 𝔫.exponent v = n ∧
      ∀ v' ≠ v, 𝔫.exponent v' = 𝔪.exponent v' := by
  -- Write `𝔪 = v ^ e * J` and replace `v ^ e` by `v ^ n`.
  obtain ⟨J, hJ⟩ := 𝔪.pow_exponent_dvd_finitePart v
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact 𝔪.finitePart_ne_bot (by rw [hJ, Ideal.mul_bot])
  have hv0 : Associates.mk v.asIdeal ≠ 0 := by simpa using v.ne_bot
  let 𝔫 : Modulus K := ⟨v.asIdeal ^ n * J, mul_ne_zero (pow_ne_zero n v.ne_bot) hJ0, 𝔪.infinitePart⟩
  have hcount (k : ℕ) (v' : HeightOneSpectrum (𝓞 K)) :
      (Associates.mk v'.asIdeal).count (Associates.mk (v.asIdeal ^ k * J)).factors =
        k * (Associates.mk v'.asIdeal).count (Associates.mk v.asIdeal).factors +
          (Associates.mk v'.asIdeal).count (Associates.mk J).factors := by
    rw [← Associates.mk_mul_mk, Associates.mk_pow,
      Associates.count_mul (pow_ne_zero _ hv0) (by simpa using hJ0) v'.associates_irreducible,
      Associates.count_pow hv0 v'.associates_irreducible]
  have h𝔪 (v' : HeightOneSpectrum (𝓞 K)) : 𝔪.exponent v' =
      (Associates.mk v'.asIdeal).count (Associates.mk (v.asIdeal ^ 𝔪.exponent v * J)).factors := by
    rw [exponent_def, ← hJ]
  have h𝔫 (v' : HeightOneSpectrum (𝓞 K)) : 𝔫.exponent v' =
      (Associates.mk v'.asIdeal).count (Associates.mk (v.asIdeal ^ n * J)).factors :=
    exponent_def _ _
  refine ⟨𝔫, rfl, ?_, fun v' hv' ↦ ?_⟩
  · have := h𝔪 v
    rw [hcount, Associates.count_self v.associates_irreducible, mul_one] at this
    rw [h𝔫, hcount, Associates.count_self v.associates_irreducible, mul_one]
    omega
  · have hne : Associates.mk v'.asIdeal ≠ Associates.mk v.asIdeal := fun h ↦ hv' <|
      HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 h))
    rw [h𝔫, h𝔪, hcount, hcount, Associates.count_eq_zero_of_ne v'.associates_irreducible
      v.associates_irreducible hne, mul_zero, mul_zero]

end Modulus

/-- **Removing the component at one place from a congruence idele.** Let `v` be a finite place
and let the modulus `𝔪` impose, away from `v`, no condition that `𝔫` does not. Dividing an idele
of the congruence subgroup of `𝔫` by the idele concentrated at `v` with the same `v`-component
gives an idele of the congruence subgroup of `𝔪`. -/
theorem ideleCongruenceSubgroup.inv_ofAdicCompletion_mul_mem {𝔪 𝔫 : Modulus K}
    {v : HeightOneSpectrum (𝓞 K)} (hexp : ∀ v' ≠ v, 𝔪.exponent v' ≤ 𝔫.exponent v')
    (hinf : 𝔪.infinitePart ⊆ 𝔫.infinitePart) {x : IdeleGroup (𝓞 K) K}
    (hx : x ∈ ideleCongruenceSubgroup 𝔫) :
    (IdeleGroup.ofAdicCompletion (𝓞 K) K v (v.ideleFiniteCoord x))⁻¹ * x ∈
      ideleCongruenceSubgroup 𝔪 := by
  -- The coordinates of the quotient are `1` at `v` and those of `x` at every other place.
  have hfin (v' : HeightOneSpectrum (𝓞 K)) (hv' : v' ≠ v) :
      v'.ideleFiniteCoord ((IdeleGroup.ofAdicCompletion (𝓞 K) K v (v.ideleFiniteCoord x))⁻¹ * x) =
        v'.ideleFiniteCoord x := by
    rw [map_mul, map_inv, ideleFiniteCoord_ofAdicCompletion_of_ne v' hv', inv_one, one_mul]
  have hv : v.ideleFiniteCoord
      ((IdeleGroup.ofAdicCompletion (𝓞 K) K v (v.ideleFiniteCoord x))⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, ideleFiniteCoord_ofAdicCompletion_self, inv_mul_cancel]
  refine mem_ideleCongruenceSubgroup_iff.2 ⟨fun v' _ ↦ ?_, fun v' _ ↦ ?_, fun w hw ↦ ?_⟩
  · rcases eq_or_ne v' v with rfl | hne
    · rw [hv, Units.val_one, map_one]
    · rw [hfin v' hne]
      exact ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hx v'
  · rcases eq_or_ne v' v with rfl | hne
    · rw [hv, Units.val_one, sub_self, map_zero]
      exact zero_le
    · rw [hfin v' hne]
      exact ((mem_unitFiltration_adicCompletion_iff v').1 (TauCeti.unitFiltration_antitone
        (hexp v' hne) (ideleCongruenceSubgroup.ideleFiniteCoord_mem_unitFiltration hx v'))).2
  · rw [map_mul, map_inv, InfinitePlace.ideleInfiniteCoord_ofAdicCompletion, inv_one, one_mul]
    exact ideleCongruenceSubgroup.extensionEmbeddingOfIsReal_pos hx (hinf hw)

end TauCeti.GlobalNumberFields

namespace OpenSubgroup

open TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The exponents of the conductor are local.** The exponent of a finite place `v` in the
conductor of `U` is at most `n` exactly when `U` contains the class of every idele concentrated at
`v` whose component lies in `U(K_v, n)`. -/
theorem exponent_ideleClassConductor_le_iff {U : OpenSubgroup (IdeleClassGroup (𝓞 K) K)}
    {v : HeightOneSpectrum (𝓞 K)} {n : ℕ} :
    U.ideleClassConductor.exponent v ≤ n ↔
      ∀ u ∈ TauCeti.unitFiltration (v.adicCompletion K) n,
        (IdeleGroup.ofAdicCompletion (𝓞 K) K v u : IdeleClassGroup (𝓞 K) K) ∈ U := by
  refine ⟨fun h u hu ↦ raySubgroup_ideleClassConductor_le U <| mem_raySubgroup_iff.2
    ⟨_, ofAdicCompletion_mem_ideleCongruenceSubgroup_iff.2
      (TauCeti.unitFiltration_antitone h hu), rfl⟩, fun h ↦ ?_⟩
  -- Lower the exponent of `v` in the conductor to `n`. A congruence idele for the resulting
  -- modulus `𝔫` is its component at `v`, which lies in `U` by hypothesis, times a congruence
  -- idele for the conductor, so `𝔫` is a multiple of the conductor.
  obtain ⟨𝔫, hinf, hv, hne⟩ := U.ideleClassConductor.exists_exponent_eq_and_forall_ne v n
  have hray : raySubgroup 𝔫 ≤ U.toSubgroup := fun c hc ↦ by
    obtain ⟨x, hx, rfl⟩ := mem_raySubgroup_iff.1 hc
    have hy := ideleCongruenceSubgroup.inv_ofAdicCompletion_mul_mem
      (fun v' hv' ↦ (hne v' hv').ge) hinf.ge hx
    have hmem := U.mul_mem
      (h _ (hv ▸ ideleCongruenceSubgroup.ideleFiniteCoord_mem_unitFiltration hx v))
      (raySubgroup_ideleClassConductor_le U (mem_raySubgroup_iff.2 ⟨_, hy, rfl⟩))
    rwa [map_mul, map_inv, QuotientGroup.mk'_apply, mul_inv_cancel_left] at hmem
  exact hv ▸ Modulus.exponent_mono (ideleClassConductor_dvd_iff.2 hray) v

end OpenSubgroup

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

omit [IsGalois K L] in
/-- **Trivial abelianized restriction to a fixed field.** Let `L/K` be finite and `H` a subgroup
of `Gal(L/K)` whose fixed field is abelian over `K`. The restriction of `σ ∈ Gal(L/K)` to the
fixed field of `H` has trivial image in the abelianization exactly when `σ ∈ H`. -/
theorem abelianization_of_restrictNormalHom_fixedField_eq_one_iff [FiniteDimensional K L]
    (H : Subgroup Gal(L/K)) [IsAbelianGalois K (IntermediateField.fixedField H)]
    (σ : Gal(L/K)) :
    Abelianization.of (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) σ) = 1 ↔
      σ ∈ H := by
  rw [← map_one Abelianization.of, Abelianization.of_injective.eq_iff, ← MonoidHom.mem_ker,
    IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]

end TauCeti

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {M : Type*} [Field M] [Algebra K M] [FiniteDimensional K M] [IsAbelianGalois K M]

/-- **Norms from a subextension of an abelian extension.** Let `M/K` be a finite abelian extension
and `H` a subgroup of `Gal(M/K)`. If `σ ∈ Gal(M/K)` is the norm residue symbol of `u ∈ Kˣ`, then
`u` is a norm from the fixed field of `H` exactly when `σ ∈ H`. -/
theorem mem_normGroup_fixedField_iff (H : Subgroup Gal(M/K)) {u : Kˣ} {σ : Gal(M/K)}
    (hσ : Abelianization.of σ = normResidue K M u) :
    u ∈ normGroup K (IntermediateField.fixedField H) ↔ σ ∈ H := by
  have := IsAbelianGalois.tower_bot K (IntermediateField.fixedField H) M
  let ι : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap K u)
  -- `σ` is the restriction of a representative `τ` of the absolute Artin symbol of `u`, and the
  -- Artin symbol of `u` for the fixed field is the restriction of `σ`.
  have hστ : σ = ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K τ) := by
    refine Abelianization.of_injective ?_
    rw [hσ, normResidue_mk K M ι, artinMap_restrict K M ι u τ hτ, toMul_ofMul]
  rw [← localArtinMap_eq_zero_iff K _ (ι.comp (IntermediateField.fixedField H).val),
    artinMap_restrict K _ _ u τ hτ, ← AlgHom.restrictNormalHom_restrictNormalHom, ← hστ,
    IntermediateField.restrictNormalHom_val, ofMul_eq_zero,
    abelianization_of_restrictNormalHom_fixedField_eq_one_iff]

end TauCeti.ClassFieldTheory

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField TauCeti.GlobalNumberFields
open scoped AdicCompletionExtension

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L] {𝔪 : Modulus K}

omit [IsAbelianGalois K L] in
/-- **The exponents of the conductor are local.** The exponent of a finite place `v` of `K` in the
conductor of `L/K` is at most `n` exactly when the class of every idele concentrated at `v` with
component in `U(K_v, n)` is a norm from `L`. -/
theorem exponent_abelianConductor_le_iff (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} :
    (abelianConductor K L).exponent v ≤ n ↔
      ∀ u ∈ TauCeti.unitFiltration (v.adicCompletion K) n,
        (IdeleGroup.ofAdicCompletion (𝓞 K) K v u : IdeleClassGroup (𝓞 K) K) ∈
          (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  rw [abelianConductor]
  -- The open subgroup `⟨N_{L/K}(C_L), _⟩` coerces to `N_{L/K}(C_L)` by projection.
  exact OpenSubgroup.exponent_ideleClassConductor_le_iff

section LocalConductor

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- **Idele classes concentrated at one place that are norms.** For an abelian extension `L/K`, a
finite place `v` of `K` and a place `w` of `L` above it, the class of the idele concentrated at
`v` with component `u` is a norm from `L` exactly when `u` is a norm from `L_w`. -/
theorem ofAdicCompletion_mem_range_ideleClassNormMap_iff (u : (v.adicCompletion K)ˣ) :
    (IdeleGroup.ofAdicCompletion (𝓞 K) K v u : IdeleClassGroup (𝓞 K) K) ∈
        (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range ↔
      u ∈ normGroup (v.adicCompletion K) (w.adicCompletion L) := by
  rw [← globalArtinMap_eq_zero_iff K L IsSepClosed.lift, globalArtinMap_local, ofMul_eq_zero,
    localArtinAt_eq_one_iff_mem_normGroup v w]

/-- **The exponents of the conductor are the local conductor exponents.** For an
abelian extension `L/K`, a finite place `v` of `K` and a place `w` of `L` above it, the exponent
of `v` in the conductor of `L/K` is the conductor exponent of `L_w/K_v`. -/
theorem exponent_abelianConductor :
    (abelianConductor K L).exponent v =
      conductorExponent (v.adicCompletion K) (w.adicCompletion L) :=
  eq_of_forall_ge_iff fun n ↦ by
    rw [exponent_abelianConductor_le_iff, conductorExponent_le_iff]
    exact forall₂_congr fun u _ ↦ ofAdicCompletion_mem_range_ideleClassNormMap_iff v w u

open _root_.IntermediateField TauCeti.LocalFieldsRamification
open scoped Pointwise

/-- **Idele classes concentrated at one place that are norms from a subextension.** Let `L/K` be
abelian, `H` a subgroup of `Gal(L/K)`, `v` a finite place of `K` and `w` a place of `L` above it.
The class of the idele concentrated at `v` with component `u` is a norm from the fixed field of
`H` exactly when `u` is a norm from the fixed field in `L_w` of the subgroup of `Gal(L_w/K_v)`
corresponding to `H` under the decomposition group of `w`. -/
theorem ofAdicCompletion_mem_range_ideleClassNormMap_fixedField_iff (H : Subgroup Gal(L/K))
    (u : (v.adicCompletion K)ˣ) :
    (IdeleGroup.ofAdicCompletion (𝓞 K) K v u : IdeleClassGroup (𝓞 K) K) ∈
        (ideleClassNormMap K (fixedField H) :
          IdeleClassGroup (𝓞 (fixedField H)) (fixedField H) →* IdeleClassGroup (𝓞 K) K).range ↔
      u ∈ normGroup (v.adicCompletion K) (fixedField (H.comap
        ((MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
          (HeightOneSpectrum.decompositionEquiv v w).symm.toMonoidHom))) := by
  have := IsAbelianGalois.tower_bot K (fixedField H) L
  have := HeightOneSpectrum.isAbelianGalois_adicCompletion v w
  obtain ⟨ρ, hρ⟩ : ∃ ρ, Abelianization.of ρ =
      normResidue (v.adicCompletion K) (w.adicCompletion L) u :=
    QuotientGroup.mk_surjective _
  -- Both sides say that the local Artin symbol of `u`, an element of the decomposition group of
  -- `w`, lies in `H`.
  rw [mem_normGroup_fixedField_iff _ hρ, ← globalArtinMap_eq_zero_iff K _ IsSepClosed.lift,
    globalArtinMap_local, ofMul_eq_zero, ← localArtinAt_comp v (fixedField H).val,
    MonoidHom.comp_apply, localArtinAt_eq_map_normResidue v w, ← hρ, Abelianization.map_of,
    Abelianization.map_of, IntermediateField.restrictNormalHom_val,
    abelianization_of_restrictNormalHom_fixedField_eq_one_iff, Subgroup.mem_comap]

/-- **The conductor of a subextension at a finite place.** Let `L/K` be abelian, `H` a subgroup
of `Gal(L/K)`, `v` a finite place of `K` and `w` a place of `L` above it. The exponent of `v` in
the conductor of the fixed field of `H` is the conductor exponent of the fixed field in `L_w` of
the subgroup of `Gal(L_w/K_v)` corresponding to `H` under the decomposition group of `w`. -/
theorem exponent_abelianConductor_fixedField (H : Subgroup Gal(L/K)) :
    (abelianConductor K (fixedField H)).exponent v =
      conductorExponent (v.adicCompletion K) (fixedField (H.comap
        ((MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
          (HeightOneSpectrum.decompositionEquiv v w).symm.toMonoidHom))) :=
  eq_of_forall_ge_iff fun n ↦ by
    rw [exponent_abelianConductor_le_iff, conductorExponent_le_iff]
    exact forall₂_congr fun u _ ↦
      ofAdicCompletion_mem_range_ideleClassNormMap_fixedField_iff v w H u

/-- **The conductor of a character at a finite place is a local Artin conductor.** Let `L/K` be
abelian, `χ` a homomorphism on `Gal(L/K)`, `v` a finite place of `K` and `w` a place of `L` above
it. The exponent of `v` in the conductor of the fixed field of `ker χ` is the Artin conductor
exponent of `χ` restricted to `Gal(L_w/K_v)`, the decomposition group of `w`. -/
theorem exponent_abelianConductor_fixedField_ker {A : Type*} [MulOneClass A]
    (χ : Gal(L/K) →* A) :
    (abelianConductor K (fixedField χ.ker)).exponent v =
      artinConductorExponent (v.adicCompletion K) (w.adicCompletion L)
        (χ.comp ((MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
          (HeightOneSpectrum.decompositionEquiv v w).symm.toMonoidHom)) := by
  have := HeightOneSpectrum.isAbelianGalois_adicCompletion v w
  rw [exponent_abelianConductor_fixedField v w, MonoidHom.comap_ker,
    conductorExponent_fixedField_ker]

end LocalConductor

end TauCeti.ClassFieldTheory
