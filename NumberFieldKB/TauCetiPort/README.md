This directory contains files ported from Tau Ceti (https://github.com/TauCetiProject/TauCeti), licensed under the
Apache License 2.0, with module names prefixed `NumberFieldKB.TauCetiPort.` instead of `TauCeti.`; the sections below
list the source commits and the changes made in porting.

# Port of Tau Ceti's proof of Bochner's theorem

Source: Tau Ceti, main `7ed979dc2eacd36a3962e1fdf3b481323fb3fb8b` (2026-11-04), Apache License 2.0, copyright
the Tau Ceti contributors (headers kept in every file).

Contents: the import closure of `TauCeti/Analysis/Bochner/LocallyCompactGroup.lean` (42 files), at the same relative
paths, module names prefixed `NumberFieldKB.TauCetiPort.` instead of `TauCeti.`. Declaration names and namespaces are
unchanged, so the port can be replaced by an import of Tau Ceti once both repositories share a toolchain (Tau Ceti:
Lean `v4.36.0-rc2`; here: `v4.35.0`, Mathlib `v4.35.0`).

Changes for Mathlib `v4.35.0` (proofs only, no statement changed):
- `MeasureTheory/Measure/AbsolutelyContinuous.lean`: `_root_.tsum_le_tsum` → `ENNReal.tsum_le_tsum`.
- `MeasureTheory/Measure/FiniteMeasureExt.lean`: `_root_.add_apply`, `_root_.smul_apply` →
  `BoundedContinuousFunction.add_apply`, `BoundedContinuousFunction.smul_apply`; `ContinuousMap.coe_ofClass` →
  `ContinuousMap.coe_coe`.
- `MeasureTheory/Integral/PeakFunction.lean`: `integral_pos_of_hasCompactSupport_nonneg_ne_zero` →
  `integral_pos_of_hasCompactSupport_nonneg_nonzero`.
- `Analysis/PositiveDefinite/Limits.lean`: `isClosed_setOfPred_posSemidef` → `Matrix.posSemidef_is_closed`.
- `Analysis/Fourier/Pontryagin/Uniqueness.lean`: local lemma `BoundedContinuousFunction.finsetSum_apply'` (evaluation
  of a finite sum of bounded continuous functions; `FunLike.coe_sum` on Tau Ceti's Mathlib) and adjusted `simp` lists.

Consumers: `NumberFieldKB.Pontryagin.bochnerTheorem` (`NumberFieldKB/Pontryagin/BochnerProof.lean`) discharges the
named input `NumberFieldKB.Pontryagin.BochnerTheorem` from
`TauCeti.IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq_of_continuousAt` and
`MeasureTheory.FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq_of_innerRegular`.

# Port of Tau Ceti's local fields, Tate cohomology and idele norm groups (class field theory)

Source: Tau Ceti, main `67aa17161ba1908f8a85182bfdf2d4ccaf21171c` (2026-11-04), Apache License 2.0, copyright the Tau Ceti
contributors (headers kept in every file). Same conventions as above: same relative paths, module names prefixed
`NumberFieldKB.TauCetiPort.`, declaration names and namespaces unchanged. The `module`/`public import` syntax is kept
(Lean v4.35.0 supports it).

Contents (290 files, the union of the import closures of):
- `NumberTheory/LocalField/Norm/Open` (norm groups of local fields are open; `isOpen_normGroup`,
  `exists_unitFiltration_le_normGroup`), `NumberTheory/LocalField/PowerSubgroup/Open`
  (`isOpen_of_natCast_index_ne_zero`), `NumberTheory/LocalField/Norm/Unramified/Basic`
  (`map_normUnits_unitFiltration`), `NumberTheory/LocalField/Herbrand/UpperQuotient`
  (`LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`): 90 files;
- `RepresentationTheory/Homological/TateCohomology/TrivialityCriterion` (`TateCohomology.isZero_of_forall_isPGroup`):
  82 files;
- `NumberTheory/NumberField/Global/Ideles/Norm/Open` (`GlobalNumberFields.isOpen_range_ideleNormMap`,
  `exists_ideleCongruenceSubgroup_le_range_ideleNormMap`): 186 files (78 shared with the above).

New file, not from Tau Ceti: `MathlibBackport/IsApply.lean` registers `IsOneApplyEqSelf`/`IsMulApplyEqComp` for
`Module.End R M` and `M ≃ₗ[R] M` (instances present on Mathlib master `a1f75768`, absent in v4.35.0; proofs `rfl`).
Imported by `RepresentationTheory/FDRep/Basic`, `RingTheory/Semisimple/DoubleCentralizer`,
`RepresentationTheory/RelativeNorm`.

Statement of changes for Mathlib v4.35.0 (proofs and imports only; no statement changed). 56 of the 290 files differ
from upstream beyond the import paths.
- **Universe declarations hoisted to file scope** (Lean v4.35.0 scopes `universe u` to the enclosing namespace; Tau
  Ceti's toolchain does not), with nothing else changed, in:
  `RepresentationTheory/CharacterTable/ClassFunction`, `CategoryTheory/Linear/FullyFaithful`, `CategoryTheory/Skeletal`,
  `RepresentationTheory/Induction/{Restriction,Transitivity,Permutation}`, `RepresentationTheory/AsModule`,
  `RepresentationTheory/Coinduced`, `RepresentationTheory/Rep/OfMulAction`, `Algebra/MonoidAlgebra/TensorProduct`,
  `Algebra/Homology/ShortComplex/{Biproduct,ShortExact}`, `CategoryTheory/Exact/KernelCokernelPair`,
  `RingTheory/KrullSchmidt/Indecomposable`, `RingTheory/Semisimple/Schur`, `LinearAlgebra/TensorProduct/{Basic,Basis}`,
  `LinearAlgebra/Trace/Pi`, `RepresentationTheory/Invariants`, `GroupTheory/Index/Basic`,
  `RepresentationTheory/FiniteIndex`, `RepresentationTheory/Augmentation/Basic`,
  `RepresentationTheory/Homological/Resolution`, `Algebra/Homology/Ext/ProjectiveResolution`,
  `RepresentationTheory/Homological/GroupCohomology/{Resolution,Shapiro}`,
  `Topology/Algebra/RestrictedProduct/{TopologicalSpace,ContinuousRng}`, `RingTheory/NormTrace/{Pi,BaseChange}`,
  `NumberTheory/NumberField/LocalGlobal/Semilocal/Norm/Trace`. (Also applied, with other changes below, in
  `RepresentationTheory/Induction/Projection`, `RepresentationTheory/FDRep/Basic`, `RepresentationTheory/Irreducible`,
  `RingTheory/Semisimple/DoubleCentralizer`.)
- **Mathlib modules absent in v4.35.0:** `Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion` →
  `Mathlib.RingTheory.DedekindDomain.AdicValuation` (master split the file on 2026-10-09) in
  `RingTheory/DedekindDomain/{Factorization,AdicValuation/Completion}`,
  `NumberTheory/NumberField/Global/Approximation/Weak`; `Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification`
  → `Mathlib.NumberTheory.RamificationInertia.Valuation` (same lemmas `intValuation_liesOver`, `valuation_liesOver`) in
  `RingTheory/DedekindDomain/ValuationOfNeZero`; `Mathlib.FieldTheory.IsRealClosed.Real` (the instance
  `IsRealClosed ℝ`) dropped in `NumberTheory/NumberField/InfinitePlace/Completion/Norm`:
  `IsRealClosed.exists_eq_pow_of_nonneg` replaced by the real `n`-th root (`Real.rpow_inv_natCast_pow`), importing
  `Mathlib.Analysis.SpecialFunctions.Pow.Real`.
- **`AbsoluteValue.Completion` is a structure on master, the completion itself in v4.35.0:**
  `NumberTheory/NumberField/InfinitePlace/Completion/DecompositionGroup` drops the wrapper
  (`AbsoluteValue.Completion.equiv`, `continuous_ofCompletion`, `continuous_toCompletion`, `toCompletion_injective` are
  identities here); `NumberTheory/NumberField/InfinitePlace/Completion/Basic`: `AbsoluteValue.Completion.algebraMap_def`
  → `UniformSpace.Completion.algebraMap_def`.
- **Renamed Mathlib lemmas** (master name → v4.35.0 name): `Nat.multiplicity_le_self`, `mul_multiplicity_le`,
  `Nat.multiplicity_mul`, `multiplicity_dvd_iff_le` → `padicValNat_le_self`, `mul_padicValNat_le`, `padicValNat.mul`,
  `padicValNat_dvd_iff_le` (master renamed the `padicValNat` lemmas on 2026-10-28), in `NumberTheory/Padics/PadicValNat`,
  `NumberTheory/LocalField/NatCastValuation`, `RepresentationTheory/Homological/GroupCohomology/Corestriction`;
  `isLocalHom_of_le_jacobson`, `Ideal.isUnit_of_sub_one_mem_jacobson`, `Submodule.le_of_le_smul_of_le_jacobson` (stated
  with `Ring.jacobson`) → the `_bot` versions (stated with `jacobson ⊥`; `Ideal.jacobson_bot`) in
  `RingTheory/Henselian/Basic`, `RingTheory/Norm/Henselian`, `RingTheory/LocalRing/Monogenic`;
  `IntermediateField.le_fixedField_iff_le_fixingSubgroup` → `IntermediateField.le_iff_le` in
  `FieldTheory/Normal/Embeddings`, `NumberTheory/NumberField/InfinitePlace/Completion/DecompositionGroup`;
  `finrank_eq_one_iff_of_ne_zero'` → `finrank_eq_one_iff_of_nonzero'` in `RepresentationTheory/Irreducible`;
  `Int.even_natCast`, `Int.odd_natCast` → `Int.even_coe_nat`, `Int.odd_coe_nat` in
  `RepresentationTheory/Homological/TateCohomology/Periodic`; `Sylow.isPGroup` → `Sylow.isPGroup'` in
  `RepresentationTheory/Homological/TateCohomology/TrivialityCriterion`.
- **`mul_apply_eq_comp` for endomorphisms:** `Module.End.mul_apply` used instead in `LinearAlgebra/End/Basic`,
  `RepresentationTheory/Induction/Projection`, `RepresentationTheory/RelativeNorm` (where `simp [← mul_apply_eq_comp]`
  loops in v4.35.0; one `simp` call replaced by `Finset.sum_congr` and `rw`) and
  `RepresentationTheory/Homological/TateCohomology/Coinduced` (one `simp` call replaced by explicit rewrites).
- **Instance search:** a local `Finite` instance on `{I | I ∣ J}` from the `Fintype` on the subtype in
  `RingTheory/DedekindDomain/{Factorization,RamificationLocus}`; `mem_connectedComponentIn` given its membership
  argument with an explicit type in `Topology/ConnectedComponents`.

Consumers (named inputs of Milne's *Class Field Theory* now proved):
- `NumberFieldKB.MilneCFT.LocalCFT.finiteIndexOpenInput` (`MilneCFT/LocalCFT/Complements.lean`) from
  `TauCeti.isOpen_of_natCast_index_ne_zero`;
- `NumberFieldKB.MilneCFT.LocalCFT.normGroupOpenInput` (`MilneCFT/LocalCFT/Basic.lean`) from `TauCeti.isOpen_normGroup`;
- `NumberFieldKB.MilneCFT.prop4_12b` (`MilneCFT/Ch5IdelesChar.lean`) from `TauCeti.exists_unitFiltration_le_normGroup`;
- `NumberFieldKB.MilneCFT.thm3_10` (`MilneCFT/Ch2TateTriviality.lean`) from
  `TauCeti.TateCohomology.isZero_of_forall_isPGroup`.

# Port of Tau Ceti's Hasse–Arf theorem (class field theory)

Source: Tau Ceti, main `85f3eb5579df5ca44ba8cd0921d614b41ab72174` (shallow clone of 2026-11-05; the commit `67aa1716`
of the previous section could not be re-fetched), Apache License 2.0, copyright the Tau Ceti contributors (headers
kept in every file). Contents: the 74 files of the import closure of
`TauCeti/NumberTheory/LocalField/Herbrand/HasseArf/Abelian.lean` not ported in the previous section (175 files in all).
Universe declarations were hoisted to the top of the file (Tau Ceti's toolchain allows them inline; this one does not).

Used by: `NumberFieldKB.MilneCFT.LocalCFT.hasseArf` (`MilneCFT/LubinTate/HasseArfTauCeti.lean`) discharges the named
input `LocalCFT.HasseArf` from `TauCeti.LocalFieldsRamification.hasseArf`;
`NumberFieldKB.MilneCFT.LocalCFT.herbrandQuotient` (`MilneCFT/LubinTate/HerbrandTauCeti.lean`, from the previous section) discharges
`LocalCFT.HerbrandQuotient` from `TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`.

Changes for Mathlib `v4.35.0` (proofs and binders only; no statement changed):
- `GroupTheory/Commutator`: `mem_of_adjacent_of_commutator` gets an explicit `{m : ℕ}` binder (autoImplicit is off);
  induction alternative `ind` → `h`.
- `GroupTheory/Elementary`: `Sylow.isPGroup` → `Sylow.isPGroup'`.
- `GroupTheory/Solvable`: `Subgroup.derivedSeries*` → root `derivedSeries*`; `DerivedWordArgs.node` gets an explicit
  `{n : ℕ}` binder.
- `NumberTheory/Padics/PadicIntegers`: bridge `multiplicity` and `padicValNat` with `Nat.padicValNat_def`.
- `NumberTheory/Padics/RingHoms`: removed a now-unneeded `rw [Nat.padicValNat_def]` (`Padic.valuation_natCast` gives
  `padicValNat` here).
- `NumberTheory/LocalField/Padic`: `Nat.multiplicity_self` → `padicValNat_self`; private backport
  `units_isSquare_coe_iff` of Mathlib's `Units.isSquare_coe_iff`.
- `NumberTheory/LocalField/Norm/Herbrand`: restored a docstring fragment that the universe-hoisting script had moved out
  of its docstring (comment only; the script now skips comments). The file now equals upstream.

# Port of Tau Ceti's local reciprocity and local class formation (class field theory)

Source: Tau Ceti main `85f3eb5579df5ca44ba8cd0921d614b41ab72174`; 254 files of the import closure of `ClassFieldTheory/Local/Reciprocity` and `ClassFieldTheory/Local/ClassFormation` not ported before.

Changes for Mathlib `v4.35.0` (proofs and binders only; no statement changed):
- `RepresentationTheory/Coinvariants`: `one_apply_eq_self` → `Module.End.one_apply` in a `simp only` (no `IsOneApplyEqSelf` instance here).
- `Algebra/AddCircle`: `AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq` → `..._eq_top` (name in this Mathlib).
- `FieldTheory/Galois/FixedField`, `FieldTheory/Galois/AbsoluteGaloisGroup/Basic`, `.../Extension`: `IntermediateField.le_fixedField_iff_le_fixingSubgroup` → `IntermediateField.le_iff_le` (old name in this Mathlib).
- `NumberTheory/LocalField/Unramified/Existence`: `X_pow_sub_X_ne_zero` → `FiniteField.X_pow_card_sub_X_ne_zero _` (3 uses).
- `RepresentationTheory/Homological/ContCohomology/Coinduced/Discrete`: `IsZeroApply`/`IsAddApply`/`IsSMulApply` instances take explicit `G A` arguments (the carrier is an explicit `outParam` here).
- `NumberTheory/ClassFieldTheory/Formation/Basic`: imports `MathlibBackport.IsApply` for the `IsMulApplyEqComp` instance on `Module.End`.
- `RepresentationTheory/Homological/ContCohomology/InnerConjugation`: in two `simp only` lists, `ContinuousMap.coe_ofClass` → `ContinuousMap.coe_coe, ContinuousMap.id_apply, ContinuousMap.coe_mulRight`.

# Port of Tau Ceti's local Artin map, unramified reciprocity and local existence (class field theory)

Source: Tau Ceti main `85f3eb5579df5ca44ba8cd0921d614b41ab72174`; 114 files of the import closure of `ClassFieldTheory/Local/Unramified`, `ClassFieldTheory/Local/ArtinMap` and `ClassFieldTheory/LocalExistence/Existence` not ported before.

Changes for Mathlib `v4.35.0` (proofs and binders only; no statement changed except as noted):
- `RingTheory/Valuation/ValueGroupTransport`: this Mathlib's `Valuation.IsEquiv.orderMonoidIso` is Tau Ceti's `orderMonoidIso₀` (value group with zero). New local `IsEquiv.valueGroupIso : v.valueGroup ≃*o w.valueGroup` (built with `MulEquiv.unzero`) plays the role of Tau Ceti's group-level `orderMonoidIso`; `orderMonoidIso_coe`, `orderMonoidIso_symm_eq`, `orderMonoidIso_self`, `orderMonoidIso_trans_eq` are stated and proved for it (statements mention `valueGroupIso` instead of `orderMonoidIso` because of the name clash).
- `RingTheory/Valuation/CharacteristicGroup`: `orderMonoidIso₀` → `orderMonoidIso`; the group-level `orderMonoidIso` → `valueGroupIso`.
- `Algebra/Polynomial/XPowSubC`: `irreducible_X_pow_sub_C_of_prime` → `X_pow_sub_C_irreducible_of_prime`.
- `NumberTheory/ClassFieldTheory/Formation/AbsoluteArtinMap`, `Topology/Algebra/Group/TopologicalAbelianization/Lift`: `Abelianization.commutator_le_ker` → `commutator_subset_ker`.
- `NumberTheory/Supernatural`: `Nat.multiplicity_mul`/`Nat.eq_iff_prime_multiplicity_eq` → `padicValNat.mul`/`Nat.eq_iff_prime_padicValNat_eq`; dropped `Nat.padicValNat_def` rewrites that are no longer needed.
- `Topology/Algebra/Group/Profinite/Generation`: added `rfl` after `simp` in `convergesToOne_iff` (set-difference vs set-builder form).
- `NumberTheory/ClassFieldTheory/ClassField`, `NumberTheory/LocalField/Unramified/ZHat`, `.../Unramified/Inertia/Basic`: `le_fixedField_iff_le_fixingSubgroup` → `IntermediateField.le_iff_le`.
- `FieldTheory/Kummer/Extension`: `natDegree_X_pow_sub_C` takes no explicit argument.
- `Topology/Algebra/Group/Profinite/Order`, `.../Index/Basic`, `.../ProP/Order`: `multiplicity` lemmas → `padicValNat` lemmas (`padicValNat_dvd_iff_le`, `padicValNat.prime_pow`, `padicValNat.eq_zero_of_not_dvd`, `dvd_iff_padicValNat_ne_zero`, `padicValNat_prime_prime_pow`).
- `Topology/Algebra/Group/Profinite/Sylow/Basic`, `.../Sylow/Existence`: `Sylow.isPGroup` → `isPGroup'`.
- `Topology/Algebra/Group/Profinite/Sylow/Containment`: `maximal_isPGroup.eq_of_ge` → `is_maximal'`.
- `NumberTheory/LocalField/Unramified/Maximal`: `X_pow_sub_X_ne_zero` → `FiniteField.X_pow_card_sub_X_ne_zero _`.


# Port of Tau Ceti's global class field theory (class field theory)

Source: Tau Ceti main `e8758b7b2f82b9b1c3f33b992ab8f499b510240f`; 314 files of the import closure of the targets above not ported before.

Changes for Mathlib `v4.35.0` (proofs and binders only; no statement changed except as noted):
- `Data/ZMod/Units`: `ZMod.isUnit_intCast_iff_isCoprime` -> `ZMod.coe_int_isUnit_iff_isCoprime` (3 uses; same argument order, `IsCoprime (d : ℤ) a`).
- `RingTheory/Ideal/Norm/AbsNorm`: in this Mathlib `Ideal.absNorm` needs `[Infinite R]`; added `[Infinite R]` (and `[Infinite R']`) binders to `absNorm_comap_of_ringEquiv`, `absNorm_map_of_ringEquiv`, `natCast_notMem_of_coprime_absNorm` and `Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem` (a hypothesis added, so these statements are weaker than upstream; the consumers use `ℤ`/`𝓞 K`). `absNorm_of_ne_bot`/`absNorm_eq_natCard` -> `absNorm_apply` followed by `Submodule.cardQuot_apply`.
- `FieldTheory/Galois/GaloisClosure`, `NumberTheory/Cyclotomic/CyclotomicCharacter`, `NumberTheory/ClassFieldTheory/KummerLayer`: `le_fixedField_iff_le_fixingSubgroup` -> `IntermediateField.le_iff_le`.
- `NumberTheory/NumberField/IntegralSqrt`: `irreducible_X_pow_sub_C_of_prime` / `..._iff_of_prime` -> `X_pow_sub_C_irreducible_of_prime` / `X_pow_sub_C_irreducible_iff_of_prime`.
- `NumberTheory/ClassFieldTheory/Local/ExplicitCyclotomicSymbol/Basic`: `multiplicity_dvd_iff_le` -> `padicValNat_dvd_iff_le`.
- `RepresentationTheory/Homological/GroupCohomology/PrimeIndex`, `NumberTheory/ClassFieldTheory/Formation/InvariantKernel`: `Sylow.isPGroup` -> `Sylow.isPGroup'`.
- `NumberTheory/NumberField/Global/Adeles/FiniteBaseChange`, `.../BaseChange`: `Countable.of_moduleFinite` -> `Finsupp.Countable.of_moduleFinite`.
- `LinearAlgebra/End/LocallyNilpotent`, `NumberTheory/NumberField/Units/Log/Embedding`: import `MathlibBackport.IsApply` for the `IsMulApplyEqComp` instance on `Module.End`.
- `RepresentationTheory/Induction/Conjugate`: the `variable` line in `section Representation` binds `{V : Type*}` explicitly (autoImplicit is off).
- `Topology/Algebra/Star/Completion` (`instStarModule`), `Topology/Algebra/UniformRing` (`instIsScalarTowerMul`, `instSMulCommClassMul`): `by fun_prop` continuity arguments of `isClosed_eq` (timeouts) replaced by explicit `continuous_const_smul`/`continuous_star`/`Continuous.mul` terms.
- `NumberTheory/NumberField/Frobenius/DecompositionGroup`: `Subgroup.isCyclic_iff_exists_zpowers_eq` -> `..._eq_top`.
- `NumberTheory/ClassFieldTheory/Local/Cyclotomic`: `X_pow_sub_X_ne_zero` -> `FiniteField.X_pow_card_sub_X_ne_zero _`.
- `NumberTheory/NumberField/PrimeIdeal`: imports `Mathlib.Algebra.CharZero.Infinite` (the `Infinite (𝓞 K)` instance that `absNorm` needs here).
- `NumberTheory/NumberField/Cyclotomic/NormValuation`: dropped `simp only [Nat.padicValNat_def]`; `multiplicity` lemmas -> `padicValNat` lemmas (`padicValNat.mul`, `padicValNat.prime_pow`, `padicValNat.pow`, `padicValNat_primes`, and `by simp` for `padicValNat p 0 = 0`, `padicValNat p 1 = 0`).
- `NumberTheory/NumberField/Cyclotomic/LocalDegree`: `multiplicity_dvd_iff_le`, `Nat.multiplicity_mul`, `pow_multiplicity_dvd` -> `padicValNat_dvd_iff_le`, `padicValNat.mul`, `pow_padicValNat_dvd`; `multiplicity ℓ a` -> `padicValNat ℓ a` in a local `have`.
- `NumberTheory/ClassFieldTheory/Global/Cyclotomic/ProductFormula`: `multiplicity_eq_zero_of_not_dvd` -> `padicValNat.eq_zero_of_not_dvd`.
- `NumberTheory/NumberField/LocalGlobal/DecompositionGroup`, `NumberTheory/ClassFieldTheory/Global/IdeleClass/SecondInequality`: `le_fixedField_iff_le_fixingSubgroup` -> `IntermediateField.le_iff_le`.
- `NumberTheory/ClassFieldTheory/Global/PrescribedInvariant`: `Polynomial.X_pow_sub_X_ne_zero` -> `FiniteField.X_pow_card_sub_X_ne_zero _`; `QuotientGroup.eq_one_iff` gets `(N := L.relativeTop)` so that `hu` unifies.

The `[Infinite S]` binder of `Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem` is on the section `variable` line of
`RingTheory/Ideal/Norm/AbsNorm`. This is the only change to statements in this section; it is forced by the toolchain
(`Ideal.absNorm` of Mathlib v4.35.0 is only defined for infinite rings), and every use in the port and in
NumberFieldKB is for `ℤ` or `𝓞 K`.

Note on versions: the 650 files of this closure ported in the three previous sections were copied from older Tau Ceti commits
(`67aa1716`, `85f3eb55`) and were not re-copied; the 314 new files build against them.

Used by (named inputs of Milne's *Class Field Theory* proved from this port):
- `NumberFieldKB.MilneCFT.idelicReciprocity` (`MilneCFT/Ch5IdelicReciprocityTauCeti.lean`) from
  `TauCeti.ClassFieldTheory.ideleClassArtinMap`, `ker_ideleClassArtinMap`, `ideleClassArtinMap_surjective`,
  `globalArtinMap_eq_zero_of_forall_eq_one`, `globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt`,
  `localArtinAt_eq_one_of_normalizedValuation_eq_one`, `normGroup_le_ker_localArtinAt`,
  `infiniteLocalArtinAt_eq_one_of_{isComplex,pos,isUnramified}` and `GlobalNumberFields.isOpen_range_ideleNormMap`;
- `NumberFieldKB.MilneCFT.Ch7.theorem9_5`, `Ch7.lemma9_3`, `Ch7.normLimitation`, `idelicExistence`,
  `ch7_reciprocityLaw` (`MilneCFT/Ch7/ExistenceTauCeti.lean`) from `globalAbelianExistence`,
  `isAbelianGalois_classField_iff`, `globalNormSubgroup_eq_range_classField` and `ideleClassNormMap_comp`;
- `NumberFieldKB.MilneCFT.Ch8.theorem4_7` (`MilneCFT/Ch8/H2TauCeti.lean`) from `globalClassFormation`,
  `ClassFormation.isAddCyclic_H2`, `ClassFormation.natCard_H2` and `globalLayerCohomologyEquiv`, with the comparison of
  Galois actions on adeles through `AdeleRing.ringHom_ext`;
- `NumberFieldKB.MilneCFT.thm3_11` (`MilneCFT/Ch2TateTheorem.lean`) from
  `TauCeti.TateCohomology.cup_bijective_of_forall_isPGroup` (file ported in an earlier section);
- `NumberFieldKB.MilneCFT.LocalCFT.kroneckerWeber` (`MilneCFT/LubinTate/KroneckerWeberTauCeti.lean`) from
  `TauCeti.ClassFieldTheory.kroneckerWeber`;
- `NumberFieldKB.HilbertClassField.hilbertClassFieldDegreeInput` (`HilbertClassField/TauCeti.lean`) from
  `hilbertClassField`, `finrank_hilbertClassField` and `isUnramifiedAt_hilbertClassField`.

## Central simple algebras

Source: Tau Ceti main `e8758b7b2f82b9b1c3f33b992ab8f499b510240f`; the 59 files of the import closure of `ClassFieldTheory/Brauer/CentralSimple/Invariant` not ported before. Universe declarations were hoisted to the top of the file (Tau Ceti's toolchain allows them inline; this one does not); no Mathlib module was missing.

Changes for Mathlib `v4.35.0` (proofs and binders only; no statement changed):
- `Algebra/Group/ElementaryTwoQuotient/Basic`: the variables `M` and `H` were auto-bound upstream; explicit `{M : Type*}` / `{H : Type*}` binders added to `elementaryTwoQuotientLiftEquiv`, `elementaryTwoQuotientLinearLiftEquiv` and `elementaryTwoQuotientLinearLiftEquiv_symm_mk` (autoImplicit is off here).
- `Algebra/CrossedProduct/Splitting/Class`: imports `MathlibBackport.IsApply` for the `IsMulApplyEqComp` instance on `Module.End`.
- `Algebra/CrossedProduct/Inflation`: `le_fixedField_iff_le_fixingSubgroup` -> `IntermediateField.le_iff_le`.

Also ported, unchanged from upstream: `NumberTheory/ClassFieldTheory/Global/Brauer/Exactness` (`range_brLocalization`,
`exists_br_of_sum_eq_zero`; its closure was otherwise already ported).

Consumer: `NumberFieldKB.MilneCFT.Ch4.example2_14e_of_brauerBaseChange` (`MilneCFT/Ch4BrauerTauCeti.lean`) proves
Milne IV Example 2.14(e) from `brauerGroupEquivBr`, `brLocalization_injective`, `sumLocalInv_brLocalization_eq_zero`,
`exists_br_of_sum_eq_zero`, `sumLocalInv_surjective`, `invMap`, `infiniteInvMap_injective` and the named comparison
`Ch4.BrauerBaseChangeTauCeti` (base change of `brauerGroupEquivBr` to the completions, which Tau Ceti proves only for
finite extensions in `Algebra/CrossedProduct/BaseChange/Naturality`, not ported).

## Scalar extension of crossed products

Source: Tau Ceti main `e8758b7b2f82b9b1c3f33b992ab8f499b510240f`. Ported verbatim (no change needed for Mathlib
`v4.35.0`): the closure of `Algebra/CrossedProduct/BaseChange/Algebra` and `Algebra/CrossedProduct/Restriction`, 8 files
(`Algebra/Algebra/Opposite`, `Algebra/BrauerGroup/{BaseChange,Centralizer}`,
`Algebra/CentralSimple/{BaseChange,Subfield,Centralizer/Basic}`, `Algebra/CrossedProduct/Restriction`,
`Algebra/CrossedProduct/BaseChange/Algebra`).

Consumers: `NumberFieldKB.MilneCFT.BrauerBaseChange.brauerGroupEquivBr_baseChange` (`MilneCFT/Ch4BrauerBaseChange.lean`)
proves that `brauerGroupEquivBr` commutes with base change along every field extension (Tau Ceti's
`Algebra/CrossedProduct/BaseChange/Naturality` covers finite separable extensions only and was not needed); it discharges
`Ch4.BrauerBaseChangeTauCeti`. `MilneCFT/Ch8/LocalRelBrTauCeti.lean` uses the already ported `semilocalEquiv`,
`infiniteSemilocalEquiv`, `finrank_adicCompletion`, `invMap_brRes`; `MilneCFT/Ch8/NormLimitationTauCeti.lean` uses
`ClassFormation.artinMap_groundNorm`, `levelNorm_ideleClassLevelEquiv` and `globalClassFormation`.

# Port of Tau Ceti's function-field Riemann–Roch theorem

Source: Tau Ceti, main `e8758b7b2f82b9b1c3f33b992ab8f499b510240f` (shallow clone of 2026-11-05), Apache License 2.0,
copyright the Tau Ceti contributors (headers kept in every file).

Contents: the import closure of `TauCeti/FieldTheory/FunctionField/Differential/CanonicalDivisor.lean`
(`TauCeti.exists_isRiemannRochDivisor`, Stichtenoth Theorem 1.5.15) and of `Place/OfValuationSubring.lean`
(83 files under `Algebra/`, `AlgebraicGeometry/WeilDivisor/`, `FieldTheory/`, `LinearAlgebra/Dimension/`, `RingTheory/`),
at the same relative paths, module names prefixed `NumberFieldKB.TauCetiPort.`. Declaration names and namespaces
unchanged. It includes `TauCeti.genus`, `TauCeti.genus_ratFunc`, `TauCeti.Divisor.degree_principal`.

Changes for Mathlib `v4.35.0` (proofs and imports only, no statement changed):
- `Algebra/Polynomial/CommonXPower.lean`: `natTrailingDegree_mem_support_of_ne_zero` →
  `natTrailingDegree_mem_support_of_nonzero`.
- `RingTheory/Algebraic/LinearIndependent.lean`: shim `LinearIndependent.smul_of_isRightRegular` (absent here).
- `RingTheory/Valuation/NontrivialComap.lean`: shim `Valuation.exists_map_eq_of_map_sum_eq_zero` (absent here).
- `RingTheory/DedekindDomain/AdicValuation/Basic.lean`, `RingTheory/DedekindDomain/Factorization.lean`,
  `AlgebraicGeometry/WeilDivisor/Dedekind/Basic.lean`: import `Mathlib.RingTheory.DedekindDomain.AdicValuation`
  (the module `...AdicValuation.Completion` does not exist here).
- `RingTheory/DedekindDomain/Factorization.lean`: the finiteness of `{I | I ∣ span {n}}` from the `Fintype` subtype.
- `AlgebraicGeometry/WeilDivisor/FixedDegree/Basic.lean`: `variable {d : ℕ}` (Tau Ceti builds with auto-bound
  implicits, this repository with `autoImplicit = false`).
- `FieldTheory/FunctionField/Place/RatFunc/Basic.lean`: `RatFunc.inftyValuation_of_ne_zero` →
  `RatFunc.inftyValuation_of_nonzero`.
- `FieldTheory/FunctionField/Differential/Weil.lean`: `mul_apply_eq_comp`, `one_apply_eq_self` →
  `Module.End.mul_apply`, `Module.End.one_apply`.
- `FieldTheory/FunctionField/Differential/Dimension.lean`: `finrank_eq_one_iff_of_ne_zero'` →
  `finrank_eq_one_iff_of_nonzero'`.

Consumers: `NumberFieldKB/ModularCurves/Genus.lean` (Milne's genus, Riemann–Roch and principal divisors over an
arbitrary constant field, through the bridge `MilneEC.primeDivisorEquivPlace`).

# Port of Tau Ceti's labels of the cusps of Γ₀(N)

Source: Tau Ceti, main `e8758b7` (as above).

- `Data/Int/GCD.lean`: verbatim (the congruence `n ∣ c d' - c' d + j c c'` and `gcd(c, n)`).
- `NumberTheory/ModularForms/CongruenceSubgroups/Cusp/Label.lean`: an extract of
  `NumberTheory/ModularForms/CongruenceSubgroups/Cusp/Count.lean` (`TauCeti.gamma0CuspLabel`,
  `coe_gamma0CuspLabel_fst`, `coe_gamma0CuspLabel_snd_mul`, `gamma0CuspLabel_eq_iff_exists_dvd`,
  `gamma0CuspLabel_surjective`) and of `Data/ZMod/Units.lean` (`TauCeti.ZMod.unitOfIsCoprime_div_eq_iff`), verbatim;
  left out: the cusp orbits of `PSL(2, ℝ)` (they need Tau Ceti's Fuchsian group library) and the squarefree case.

Consumer: `NumberFieldKB/ModularCurves/CuspCountX0.lean` (the label classes of the cosets of Γ₀(N) are the orbits of
T; the number of cusps of X_0(N) is `∑_{g ∣ N} φ(gcd(g, N/g))`, `geomCount_infty_eq`).

# Port of Tau Ceti's quadratic congruence counts

Source: Tau Ceti, main `e8758b7` (as above).

Files (same relative paths, module names prefixed `NumberFieldKB.TauCetiPort.`): the import closure of
`NumberTheory/LegendreSymbol/QuadraticCongruence.lean` (`TauCeti.ZMod.natCard_sq_add_one_eq_zero`,
`TauCeti.ZMod.natCard_sq_sub_self_add_one_eq_zero`) not ported before:
- `Data/ZMod/Count.lean`
- `Data/ZMod/LocalRing.lean`
- `Data/ZMod/PrincipalUnits.lean`
- `NumberTheory/LegendreSymbol/QuadraticCongruence.lean`
- `NumberTheory/Multiquadratic/Legendre/PrimeDiscriminant/Basic.lean`
- `NumberTheory/Multiquadratic/Prime/Discriminant/Basic.lean`
- `RingTheory/Henselian/Basic.lean`

Changes for Mathlib `v4.35.0` (proofs only, no statement changed):
- `RingTheory/Henselian/Basic.lean`: `isLocalHom_of_le_jacobson` → `isLocalHom_of_le_jacobson_bot J` (three uses, in
  `exists_mem_eval_eq_zero` and the two later Hensel lemmas).

Consumer: the elliptic point counts ν₂, ν₃ of X_0(N) (NumberFieldKB/ModularCurves, in progress).

# Port of Tau Ceti's genus of a smooth projective plane curve

Source: Tau Ceti, main `e8758b7` (as above).
Contents: the import closure of `FieldTheory/FunctionField/PlaneCurve/Projective.lean`
(`TauCeti.genus_eq_of_isHomogeneous_of_aeval_insertNth_eq_zero`,
`TauCeti.isIntegrallyClosedIn_of_isHomogeneous_of_aeval_insertNth_eq_zero`: a function field generated by a point of
a nonsingular projective plane curve of degree `d` has genus `(d - 1)(d - 2)/2`; Stichtenoth Cor. 3.4.14, Fulton §8.3)
not ported before: 81 files under `Algebra/`, `Data/`, `FieldTheory/` (including `FunctionField/ConstantExtension/`,
`FunctionField/PlaneCurve/`, `FunctionField/Differential/{Kaehler,Comparison,RatFunc/Basic}`), `LinearAlgebra/`,
`Order/`, `RingTheory/` and `Topology/`, same relative paths, module names prefixed `NumberFieldKB.TauCetiPort.`.

Changes for Mathlib `v4.35.0` (proofs only, no statement changed):
- `RingTheory/Kaehler/BaseChange.lean`: `finrank_eq_one_iff_of_ne_zero` → `finrank_eq_one_iff_of_nonzero`.
- `RingTheory/LocalRing/MaximalIdeal/Square.lean`, `RingTheory/RegularLocalRing/Basic.lean`:
  `Submodule.le_of_le_smul_of_le_jacobson`, `Submodule.eq_bot_of_le_smul_of_le_jacobson` → the `_bot` variants, with
  the hypothesis `I ≤ jacobson ⊥` given directly by `jacobson_eq_maximalIdeal`.
- `RingTheory/KrullDimension/Fiber.lean`: `IsLocalRing.local_hom_tfae` → `IsLocalRing.local_hom_TFAE`.
- `FieldTheory/FunctionField/ConstantExtension/ResidueField.lean`: `Polynomial.IsRoot.map` takes the ring
  homomorphism as an implicit argument here (`hroot.map (f := ...)`).
- `Topology/KrullDimension/ClosedCover.lean`: explicit arguments for `IsEmbedding.homeomorphOfSubsetRange`, and the
  step of an `LTSeries` unfolded with `show`.

Consumer: `NumberFieldKB/ModularCurves/PlaneSingular.lean` (Milne, Remark V.2.6: the plane model `F_N = 0` is singular).


# Port of Tau Ceti's Peter–Weyl, Hermite and elliptic curve files

Source: Tau Ceti main (2026-11-05), Apache License 2.0, copyright the Tau Ceti contributors (headers kept in every file).
64 files copied into `NumberFieldKB/TauCetiPort/`, same relative paths, module names prefixed `NumberFieldKB.TauCetiPort.`,
universes hoisted.

Contents (three closures) and consumers:
- `RepresentationTheory/Compact/RepresentativeDensity` (Peter-Weyl); consumer `NumberFieldKB.Pontryagin.peterWeylTheorem`
  (`NumberFieldKB/Pontryagin/PeterWeyl.lean`).
- `NumberTheory/NumberField/Discriminant/RamifiedSupport/Hermite`; consumer `NumberFieldKB.MilneANT.theorem8_42`
  (`MilneANT/Ch8Thm842.lean`).
- `AlgebraicGeometry/EllipticCurve/Affine/{Point/ToClass,CoordinateRing}`; consumer
  `NumberFieldKB.MilneANT.ellipticCoordinateRingInput` (`MilneANT/Ch3EllipticProof.lean`).

Changes for Mathlib `v4.35.0` (proofs and imports only; no statement changed):
- `RepresentationTheory/Compact/Haar`: `FiniteMeasure.mass_ne_zero_iff` -> `FiniteMeasure.mass_nonzero_iff`;
  `toMeasure_normalize_eq_of_ne_zero` -> `toMeasure_normalize_eq_of_nonzero`.
- `RepresentationTheory/Compact/Averaging`: `ContinuousMap.coe_ofClass` -> `ContinuousMap.coe_coe`.
- `RingTheory/Algebraic/LinearIndependent`: `LinearIndependent.smul_of_isRightRegular` is absent; replaced by a direct
  proof via `Fintype.linearIndependent_iff` (`c ^ N` is a nonzero element of a domain).
- Bridge `MilneANT/Ch3EllipticProof`: `linear_combination` coefficient, `MilneEC.III.CurveAux.exists_lattice_with_g`,
  Dedekind domain by instance search.

## Stichtenoth Theorem 1.1.6: discrete valuation rings of function fields

Source: Tau Ceti main `d0b6fe9d754d0f7ecd76905a71d276bdf47efe00` (2026-11-05). The 9 files of the import closure of
`FieldTheory/FunctionField/Place/OfValuationSubring` not ported before (the other 11 of its 20 files were already
ported): `Algebra/Polynomial/CommonXPower`, `RingTheory/Valuation/{ValuationSubring,
LinearIndependent,IsTrivialOn,Sum,Polynomial}`, `FieldTheory/FunctionField/Place/{Basic,Adic,OfValuationSubring}`.
Copied unchanged apart from the changes listed below; no universe hoisting was needed.

Changes for Mathlib `v4.35.0` (proofs only, no statement changed; the other 8 files are verbatim):
- `Algebra/Polynomial/CommonXPower`: `natTrailingDegree_mem_support_of_ne_zero` -> `natTrailingDegree_mem_support_of_nonzero`.

Used by: Aside 8.9, function-field completeness, via `TauCeti.isDiscreteValuationRing_of_isFunctionField`,
`TauCeti.Place.ofValuationSubring` and `TauCeti.Place.integers_ofValuationSubring` (axioms: propext, Classical.choice,
Quot.sound).

## Chebotarev density theorem with natural density

Source: Tau Ceti main `46d83ed52f90f2512c10a961e61288ff927bf497` (2026-11-05), Apache License 2.0, copyright the Tau
Ceti contributors (headers kept). The import closure of `NumberTheory/Chebotarev/PrimeCounting/FrobeniusPrimeCount`
has 300 files; 118 were already ported, the other 182 were copied: the arithmetic Dirichlet series library (`NumberTheory/ArithmeticDirichletSeries/*`),
the Wiener–Ikehara theorem (`NumberTheory/LSeries/WienerIkehara/*`), ray class counting
(`NumberTheory/NumberField/Global/{RayClass,Counting}/*`), the geometry-of-numbers lattice-point counts, Bochner
positive-definite Fourier analysis used by Wiener–Ikehara, and `NumberTheory/Chebotarev/*`.

New file, not from Tau Ceti: `MathlibBackport/SchwartzCompactSupport.lean`, Mathlib master's
`Mathlib/Analysis/Distribution/SchwartzSpace/CompactSupport.lean` (commit `6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b`,
Terence Tao, Apache 2.0) verbatim, absent in v4.35.0; imported by `NumberTheory/LSeries/WienerIkehara/Approximation`
instead of the Mathlib module. (The other missing module, `Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion`,
was already replaced by `RingTheory/DedekindDomain/AdicValuation/Completion` of an earlier port.)

Changes for Mathlib `v4.35.0`:
- **Added instance arguments `[Infinite R]` / `[Infinite (𝓞 K)]`** (the only statement-level change): Mathlib v4.35.0
  defines `Ideal.absNorm` only for `[IsDedekindDomain S] [Infinite S]` (master drops `Infinite`), so declarations
  mentioning `Ideal.absNorm` over a general ring need it to typecheck: `RingTheory/Ideal/Quotient/HasFiniteQuotients/Norm`
  (`TauCeti.instNorthcottAbsNormNonZeroDivisors`) and the `[IsDedekindDomain (𝓞 K)]` declarations of
  `NumberTheory/ArithmeticDirichletSeries/EulerProduct/Basic` (`absNorm_primeIdealPow`, `localArithmeticFactor`,
  `localArithmeticFactor_def`, the `IsDedekindDomain` section). Every use is at the ring of integers of a number
  field, where the instance is found automatically.
- `HasFiniteQuotients/Norm`: proof via `Ring.HasFiniteQuotients.finite_absNorm_le` (absent: `Ideal.absNorm_of_ne_bot`).
- `ArithmeticDirichletSeries/NormCoeff`: `Ring.HasFiniteQuotients.finite_absNorm_eq` -> `Ideal.finite_setOfPred_absNorm_eq`;
  `_root_.zero_apply` -> `ArithmeticFunction.zero_apply`.
- `ArithmeticDirichletSeries/Estimates`: `Ring.HasFiniteQuotients.finite_absNorm_le₀` -> `Ideal.finite_setOfPred_absNorm_le₀`.
- `ArithmeticDirichletSeries/Weight`: `simp` also given `Ideal.absNorm_eq_zero_iff` (`normTwist` bad primes).
- `ArithmeticDirichletSeries/ZetaSumPartition`: `Summable.tsum_union_of_disjoint` -> `Summable.tsum_union_disjoint`.
- `RingTheory/DedekindDomain/Totient`: `absNorm_eq_natCard` -> `absNorm_apply, Submodule.cardQuot_apply`.
- `Algebra/Module/ZLattice/Basic`: `_root_.smul_apply` -> `Measure.smul_apply`.
- `Analysis/Complex/PowerSeries/Log/Deriv`: `Nat.strong_induction_on` alternative `ind` -> `h`.
- `GroupTheory/FiniteAbelian/CharacterOrthogonality`: `Abelianization.commutator_le_ker` ->
  `Abelianization.commutator_subset_ker`.

Consumer: `NumberFieldKB.MilneANT.theorem8_31` (`MilneANT/Ch8Thm831.lean`) proves the named statement
`MilneANT.Theorem8_31` from `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`.

## Cubic reciprocity, Jacobi sums and power residue symbols

Source: Tau Ceti main `d0b6fe9d` (Apache License 2.0; headers kept). The 29 files of the import closure of
`NumberTheory/NumberField/Cyclotomic/Three/{CubicReciprocity,RationalResidue}` and `NumberTheory/JacobiSum/Cubic` not
ported before: `NumberTheory/JacobiSum/{Basic,Cubic}`, `NumberTheory/GaussSum/Basic`, `NumberTheory/MulChar/Basic`,
`NumberTheory/LegendreSymbol/Complex`, `NumberTheory/NumberField/Cyclotomic/{RootsOfUnity,Quadratic}`,
`NumberTheory/NumberField/Cyclotomic/Three/{Basic,Primary,JacobiSum,CubicReciprocity,RationalResidue}`,
`NumberTheory/NumberField/Ideal/RootsOfUnity`,
`NumberTheory/NumberField/PowerResidueSymbol/{Basic,JacobiSum,Ideal,StickelbergerPhi}`, `FieldTheory/Galois/Basic`,
`LinearAlgebra/Dimension/IsQuadraticExtension`, `LinearAlgebra/Matrix/{Commute,RationalCanonicalFormFinTwo}`,
`LinearAlgebra/Matrix/Adjugate/{Basic,FinTwo}`, `LinearAlgebra/Matrix/Charpoly/FinTwo`,
`LinearAlgebra/Matrix/Trace/FinTwo`, `RingTheory/Norm/Quadratic`, `RingTheory/Ideal/{GoingUp,Quotient/Coprime}`,
`RingTheory/IntegralClosure/Map`. No Mathlib module was missing (the
`AdicValuation.Completion` import is already rewritten in the ported `AdicValuation/Basic`).

Changes for Mathlib `v4.35.0` (proofs and imports only; no statement changed):
- `RingTheory/Ideal/Norm/AbsNorm`: new backport lemma `Ideal.absNorm_eq_natCard [Infinite R] (I) : absNorm I =
  Nat.card (R ⧸ I)` (Mathlib master name; proof `absNorm_apply` + `Submodule.cardQuot_apply`).
- `NumberTheory/NumberField/Ideal/RootsOfUnity`: `Ideal.absNorm_eq_natCard` replaced by `absNorm_apply` +
  `Submodule.cardQuot_apply` in two proofs.
- `NumberTheory/NumberField/PowerResidueSymbol/JacobiSum`: imports the ported `RingTheory/Ideal/Norm/AbsNorm` (for the
  backport lemma).
- `NumberTheory/GaussSum/Basic`: `_root_.pow_apply` (generic `IsPowApply`) -> `AddChar.pow_apply` (two proofs).

## Quadratic conductor

Source: Tau Ceti (Apache License 2.0; headers kept). The 52 files of the import closure of
`NumberTheory/Multiquadratic/Cyclotomic/Conductor` (`mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd`) and
`NumberTheory/Multiquadratic/Quadratic/Discriminant` (`discr_adjoin_singleton_eq_fundamentalDiscriminant`) not ported
before, among them `NumberTheory/FundamentalDiscriminant`,
`NumberTheory/Multiquadratic/{Prime,FundamentalDiscriminant,Legendre,CandidateGenusField,Cyclotomic,Quadratic}/...`,
`NumberTheory/DirichletCharacter/{Basic,Conductor,GaussSum,Quadratic,Subgroup}`,
`NumberTheory/LegendreSymbol/{JacobiSymbol,KroneckerSymbol,ZModChar,SquareClass,NormForm}`,
`NumberTheory/NumberField/Quadratic/{Basic,RingOfIntegers}`, `NumberTheory/NumberField/Cyclotomic/GaussSum`,
`Algebra/{QuadraticDiscriminant,Polynomial/QuadraticDiscriminant}`, `FieldTheory/{Minpoly,Trace,
IntermediateField/{Quadratic,Rescale,Adjoin/Square}}`. 47 of the 52 files are verbatim; five need small proof edits for
Mathlib `v4.35.0` (no statement changed):
- `Algebra/BigOperators/Finset/SymmDiff`: closing `rfl` after the `rw` (`S ∆ D` unfolds to `(S ⊔ D) \ (S ⊓ D)` here, versus
  `(S ∪ D) \ (S ∩ D)`).
- `NumberTheory/Multiquadratic/Quadratic/Subfield`: `simp only [Finset.sup_eq_union, Finset.inf_eq_inter]` before `ring`
  for the same reason.
- `NumberTheory/DirichletCharacter/GaussSum`: `hχ.inv` (`IsPrimitive.inv`, absent) replaced by `(conductor_inv χ).trans hχ`.
- `NumberTheory/LegendreSymbol/KroneckerSymbol`: `Int.odd_natCast` -> `Int.odd_coe_nat`.
- `NumberTheory/Multiquadratic/Legendre/PrimeDiscriminant/Dirichlet/Group`: `ZMod.isUnit_intCast_iff_isCoprime` ->
  `ZMod.coe_int_isUnit_iff_isCoprime`.

Consumer: `NumberFieldKB.MilneCFT.example3_11` (`MilneCFT/Ch5Example311Uncond.lean`) discharges the named input
`Example3_11` from `discr_adjoin_singleton_eq_fundamentalDiscriminant` and
`mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd`.

## Brauer induction

Tau Ceti source: `TauCeti.RepresentationTheory.Induction.Brauer.Induction` (Brauer's induction theorem,
`character_mem_indCharacterSpanInt_isElementary`) and `TauCeti.RepresentationTheory.Induction.Monomial` (irreducible
characters of finite nilpotent groups are induced from linear characters). 65 new modules: `LinearAlgebra/{Span/IntegralDescent,End/FiniteOrder}`,
`Algebra/{Subalgebra/Center,Matrix/Pi,Group/ConjFinite,Module/Submodule/Quotient}`, `Data/Fintype/BigOperators`,
`CategoryTheory/{Simple/Endomorphism,Preadditive/Indecomposable}`, `GroupTheory/{Nilpotent,DoubleCoset/Identity}`,
`RingTheory/{IntegralClosure/Rat,SimpleModule/Isotypic,CompositionSeries/{Basic,Multiplicity,Additivity},
Semisimple/{CentralCharacter,RegularIsotypicComponent,Multiplicity,Trace/Basic,HomDimension}}`, and under
`RepresentationTheory/`: `CharacterTable/{ClassSum/{Basic,Basis,Integral,Representation},Wedderburn,BlockRepresentation,
Pairing,Independence,Completeness,CentralCharacter,Values,Degree,Table,VirtualCharacter,Determined}`, `LinearCharacter/Basic`,
`Semisimple`, `Maschke`, `Rep/DirectSum/Basic`, `Induction/{VirtualCharacter,Ideal,PElementary,Brauer/{PSection,Induction},
FrobeniusReciprocity,Spanning,Inertia,LiesOver,Monomial,Clifford/{Basic,FullInertia,LiesOver,Correspondence,Injectivity,
Surjectivity},FiniteDimensional/{Adjunction,Unit},Mackey/{Decomposition,Hom,Intertwining,Irreducible,Endomorphism,
Sufficient,Split}}`.

Fixes for Mathlib `v4.35.0` / Lean `v4.35.0` (no statement of a theorem used downstream changed):
- New file `RepresentationTheory/IrreducibleFiniteDimensional` (not in Tau Ceti): `Representation.IsIrreducible.finiteDimensional'`,
  an irreducible representation of a finite group is finite-dimensional (newer Mathlib has this implicitly; the pinned
  `Representation.char_orthonormal` requires `[FiniteDimensional]`). Not an instance (`ρ` is not determined by `V`).
- `CharacterTable/Pairing`: `characterPairing_ofCharacter_{orthonormal,self,eq_zero}` take explicit `[FiniteDimensional k V]`
  (and `W`) hypotheses; `CharacterTable/{Independence,Completeness}`: supply them via `finiteDimensional'`.
- `LinearCharacter/Basic`: `mul_apply_eq_comp` -> `Module.End.mul_apply`; `finrank_eq_one_iff_of_ne_zero` -> `_of_nonzero`.
- `CategoryTheory/Preadditive/Indecomposable`: `finrank_eq_one_iff_of_ne_zero'` -> `_of_nonzero'`.
- `Induction/Mackey/Irreducible`: `CategoryTheory.isIso_iff_ne_zero` -> `Simple.mono_isIso_iff_nonzero`; added `universe u`
  before `namespace FDRep` section.
- `Induction/Ideal`: added `universe u v` after the first `end ClassFunction` (universe declarations are scoped to the
  closed namespace here).

Consumer: `NumberFieldKB.MilneCFT.Ch8.brauerInduction` (`MilneCFT/Ch8/BrauerInductionTauCeti.lean`).

## Ray class ideal count

Source: Tau Ceti (Apache License 2.0; headers kept). The 36 files of the import closure of
`NumberTheory/NumberField/Global/RayClass/Count/Asymptotic` (`isBigO_rayClassIdealCountingFunction_sub`) not ported
before:
- `Order/Northcott/Basic`, `Algebra/Module/ZLattice/Basic`, `MeasureTheory/Group/Measure`,
  `MeasureTheory/Measure/Haar/Hausdorff`, `Topology/Frontier`, `Topology/MetricSpace/{DiscreteAddSubgroup,LipschitzParametrizable}`,
  `NumberTheory/GeometryOfNumbers/{BoundaryCount,LatticePointCount}`;
- `RingTheory/NormTrace/Prod`, `RingTheory/Ideal/Quotient/Totient`, `RingTheory/DedekindDomain/Totient`;
- `NumberTheory/NumberField/{FractionalIdeal,Units/Dirichlet}`,
  `NumberTheory/NumberField/CanonicalEmbedding/{IdealLattice,SignCut,UnitAction,NormLeOneLipschitz,MulVolume,NormLeOne}`;
- `NumberTheory/NumberField/Global/Counting/{CongruenceLattice,Ray/Coset,Ray/Ideal/Set,Ray/Ideal/Count}`,
  `.../Counting/RayFundamentalDomain/{Basic,IntegerSet,Orbit,Lipschitz,LatticeCount,Volume,MainTerm}`;
- `NumberTheory/NumberField/Global/RayClass/{MainTerm,ClassNumber,Count/Basic,Count/Reindex,Count/Asymptotic}`.

34 of the 36 files are verbatim up to import paths; two need small edits for Mathlib `v4.35.0` (no statement changed):
- `Algebra/Module/ZLattice/Basic`: `_root_.smul_apply` -> `Measure.smul_apply` (no `IsSMulApply` instance for measures).
- `RingTheory/DedekindDomain/Totient`: imports the ported `RingTheory/Ideal/Norm/AbsNorm` for the backport
  `Ideal.absNorm_eq_natCard`.

Consumer: `NumberFieldKB.MilneCFT.Ch6.prop2_8` (`MilneCFT/Ch6/Prop28TauCeti.lean`).

## Prime number theorem in arithmetic progressions

Source: Tau Ceti `NumberTheory/Chebotarev/PrimeCounting/PrimesCongruent` (`tendsto_primeCount_primesCongruent`, the prime
number theorem in arithmetic progressions; Apache License 2.0, headers kept). 150 new modules (closure of 306 files, 156
already ported),
under `NumberTheory/`:
- `ArithmeticDirichletSeries/{Basic,NormCoeff,Weight,Counting,VonMangoldt,HigherPrimePowers,Trivial,AbelSummation,Regroup,
  Estimates,Cancellation,Convergence,ZetaSumPartition,ResidueDegree(+/NaturalDensity),Deriv,Transfer,NaturalDensity}`, `Prime/*`,
  `Convolution/Basic`, `EulerProduct/{Basic,Data,Analytic,Restrict,Branch,ThreeFourOne,Logarithm/*}`, `DirichletDensity/*`;
- `LSeries/{Conjugate,Twist,SumCoeff,Summable,Continuity,Positivity,ThreeFourOne,Nonvanishing}` and `LSeries/WienerIkehara/*`
  (Wiener-Ikehara tauberian theorem), `LFunctions/PrimeIdealBoundary`, `AbelSummation`;
- `Chebotarev/{FrobeniusPrimeSet,SplitsCompletely,PrimesAboveRamifiedPrimes,PrimesCongruent,TaggedFixedField,
  CyclotomicRamification}`, `Chebotarev/{PrimeCounting,GaloisCharacter,Crossing,FixedField,Density}/*`;
- `NumberField/{AlgEquiv,DirichletDensityBounds,DedekindZeta,Frobenius/{FiberCount,FixedField/Fiber},Cyclotomic/{Finrank,Compositum},
  Global/RayClass/Character/{Sum,Weight,PartialSums,Cancellation}}`, `NumberField/RingOfIntegers/Transport`, `Cyclotomic/FixedField`;
and `Analysis/` (`Asymptotics`, `Bochner`, `Fourier`, `PositiveDefinite`, `SpecialFunctions`, `Complex/{HalfPlaneIdentity,PowerSeries,BranchLogRoot}`,
`Distribution/SchwartzSpace/Cutoff`, ...), `Algebra/Order/BigOperators`, `GroupTheory/{FiniteAbelian,SpecificGroups/Cyclic}`,
`RingTheory/{Ideal/Quotient/HasFiniteQuotients/Norm,PowerSeries/Log}`, `Data/{ZMod/Count,Set/Restrict}`, `Topology/Algebra/Order`.

Backport: `MathlibBackport/SchwartzSpaceCompactSupport` is Mathlib master's `Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport`
(absent in `v4.35.0`; verbatim, header kept, compiles unchanged). `Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion` was not
needed (only already ported files reference it, through the port's own `Completion`).

Fixes for Mathlib `v4.35.0` (no statement changed except the two noted hypotheses):
- `NumberTheory/LSeries/WienerIkehara/Approximation`: import the backport instead of the Mathlib module.
- `Analysis/Complex/PowerSeries/Log/Deriv`: `induction ... with | ind` -> `| h` (renamed case of `Nat.strong_induction_on`).
- `GroupTheory/FiniteAbelian/CharacterOrthogonality`: `Abelianization.commutator_le_ker` -> `Abelianization.commutator_subset_ker`.
- `RingTheory/Ideal/Quotient/HasFiniteQuotients/Norm`: `Ideal.absNorm_of_ne_bot` -> `Ideal.absNorm_apply`; the instance
  `instNorthcottAbsNormNonZeroDivisors` gains the hypothesis `[Infinite R]` (v4.35 `Ideal.absNorm` requires it; automatic for `𝓞 K`).
- `ArithmeticDirichletSeries/NormCoeff`: `Ring.HasFiniteQuotients.finite_absNorm_eq` -> `Ideal.finite_setOfPred_absNorm_eq`;
  `_root_.zero_apply` -> `ArithmeticFunction.zero_apply`.
- `ArithmeticDirichletSeries/Estimates`: `Ring.HasFiniteQuotients.finite_absNorm_le₀` -> `Ideal.finite_setOfPred_absNorm_le₀`.
- `ArithmeticDirichletSeries/ZetaSumPartition`: `Summable.tsum_union_of_disjoint` -> `Summable.tsum_union_disjoint`.
- `ArithmeticDirichletSeries/Weight`: `badPrimes_normTwist` simp set gains `Ideal.absNorm_eq_zero_iff`.
- `ArithmeticDirichletSeries/EulerProduct/Basic`: import `Mathlib.Algebra.CharZero.Infinite`; extra hypothesis `[Infinite (𝓞 K)]` on
  `absNorm_primeIdealPow`, `localArithmeticFactor`, `localArithmeticFactor_def`, `localArithmeticFactor_delta` (needed by `absNorm`
  for a general field `K`; automatic for number fields).

Consumer: `NumberFieldKB.MilneCFT.Ch6` Remark 4.2 (a).

## Global conductor–discriminant formula

Source: Tau Ceti main, shallow clone of 2026-11-05 (Lean `v4.36.0-rc2`; Apache License 2.0;
headers kept). The 21 files of the import closure of
`NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/ConductorDiscriminant`
(`relDiscr_eq_finprod_finitePart_abelianConductor`) not ported before:
- `Algebra/GroupWithZero/Indicator`, `Algebra/Order/Field/Basic`, `GroupTheory/FiniteAbelian/Duality`,
  `RepresentationTheory/Homological/ContCohomology/Map/DegreeTwo`, `Topology/Compactness/Compact`,
  `Topology/Separation/InvFunOn`, `RingTheory/Localization/Finiteness`, `RingTheory/Ideal/Norm/RelNorm`,
  `RingTheory/DedekindDomain/{AdicValuation/Multiplicity,Different/DualFamily,Discriminant/Valuation}`;
- `NumberTheory/LocalField/{Herbrand/ArtinConductor,Different/AlgEquiv,Discriminant/Basic,Discriminant/Conductor}`,
  `NumberTheory/ClassFieldTheory/Local/Conductor/UpperNumbering`;
- `NumberTheory/NumberField/LocalGlobal/{Different/Basic,Different/Exponent,RamificationGroup,Discriminant}`;
- `NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/ConductorDiscriminant`.

All 21 are verbatim up to import paths, except one added import line in `ConductorDiscriminant`
(`public import ...AdmissibleModulus.LocalConductor`). The ported `Ramification`, `Modulus`, `AdmissibleModulus/Basic`,
`Local/ArtinMap`, `Galois/Abelian/Basic`, `Ideles/Congruence` and `Ideles/Ray/OpenSubgroup` predate upstream lemmas
that `ConductorDiscriminant` needs; rather than overwrite them, the new file
`NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/LocalConductor.lean` (ours, not an upstream path) collects those
lemmas with their upstream proofs and names: `Modulus.exponent_eq_multiplicity`,
`Modulus.exists_exponent_eq_and_forall_ne`, `ideleCongruenceSubgroup.inv_ofAdicCompletion_mul_mem`,
`OpenSubgroup.exponent_ideleClassConductor_le_iff`, `exponent_abelianConductor_le_iff`, `mem_normGroup_fixedField_iff`,
`abelianization_of_restrictNormalHom_fixedField_eq_one_iff`, and the `section LocalConductor` of upstream
`Ramification.lean` (`exponent_abelianConductor`, `exponent_abelianConductor_fixedField`,
`exponent_abelianConductor_fixedField_ker`, ...). It uses `import all` on `AdmissibleModulus/Basic` (the body of
`abelianConductor` is unfolded) and one `omit [IsAbelianGalois K L] in` (an unused instance; the statement is more
general).

Consumer: `NumberFieldKB.MilneCFT.theorem3_27` (`MilneCFT/Ch5Theorem327Uncond.lean`).

## Primary elements of the cyclotomic integers

Source: the same Tau Ceti clone. `NumberTheory/NumberField/Cyclotomic/EisensteinPrimary.lean` (verbatim; imports only
Mathlib): `TauCeti.IsEisensteinPrimary` and the primary normalisation `ζ ^ c α`
(`IsPrimitiveRoot.isEisensteinPrimary_toInteger_pow_mul_iff`). Consumer: the named input
`NumberFieldKB.MilneCFT.Ch8.EisensteinReciprocity` and `Ch8.theorem5_14_of_eisensteinReciprocity`
(`MilneCFT/Ch8/FurtwanglerEisenstein.lean`).

