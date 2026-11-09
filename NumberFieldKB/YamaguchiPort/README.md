# Port of Yamaguchi's class field theory library (local existence, local Kronecker–Weber, small Hilbert class field)

Source: Naganori Yamaguchi, *ClassFieldTheory* (`https://github.com/n-yamaguchi-0729/ClassFieldTheory`), main
`fbd320cd8b1b06487c58227e92eb135794267709` (2026-10-21), Lean `v4.35.0-rc2`, Mathlib `065356127b1d`. Apache License 2.0;
copyright Naganori Yamaguchi (code written with OpenAI Codex), upstream headers kept in every file; the library's
`NOTICE` credits adaptations from pi1 (`chrisflav/pi1`) and Anthropic's Fermat's Last Theorem project, whose
per-file headers are also kept.

Conventions (as for `NumberFieldKB/TauCetiPort/`): same relative paths, module names `Nyll.X` renamed
`NumberFieldKB.YamaguchiPort.X`; declaration names and namespaces unchanged (`ClassFieldTheory`, `LocalFieldTheory`,
`LubinTate`, `KroneckerWeber`, ...), so the port can be replaced by a dependency on Yamaguchi's library once both share
a toolchain.

Contents (1,084 files, 439,346 lines): the union of the import closures of
- `ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalExistenceOrderIso`
  (`ClassFieldTheory.finiteAbelianLocalExistence_orderIso`, local existence in every characteristic);
- `ClassFieldTheory/KroneckerWeber/LocalCyclotomicEmbedding` (`KroneckerWeber.exists_localCyclotomicEmbedding`, local
  Kronecker–Weber over $\mathbb Q_p$);
- `ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassField{Exists,Degree,Principalization}`
  (`ClassFieldTheory.exists_smallHilbertClassField`, `smallHilbertClassField_degree_eq_classNumber`,
  `ideals_becomePrincipalInSmallHilbertClassField`);
- `GaloisCohomology/GroupTheory/Transfer/Witt` (`commutatorTransfer_eq_one_of_finite_abelianization`, Furtwängler's
  transfer theorem).
The first two together are 581 files.

## Statement of changes for Mathlib v4.35.0 (proofs and instance names only; no statement weakened)

- **`IsAddTorsionFree` / `IsMulTorsionFree` renamed `HasUniqueDiv` / `HasUniqueRoots`** (Mathlib 2026-09-29: the old
  classes, "`n • ·` is injective", got the new names; the old names now denote a weaker commuting-element form), in
  `ValuedFieldTheory/LocalField/Analytic/{LogExpComposition,FieldUnitLogUniqueness}`,
  `.../LogExpSeries/FormalCoreBase/PowerSeriesComposition`, `GaloisCohomology/ProfiniteIntegers/CyclotomicTorsionQuotient`,
  `ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/{CyclotomicZHatBaseChange,FinitePlaceCyclotomicFrobeniusLift}`.
  Same mathematical hypothesis.
- **`IntermediateField.adjoin_induction`**: motive argument named `motive` (was `p`), and the element is given
  explicitly where `apply` needs it, in `ValuedFieldTheory/Valuation/Completion/AbsoluteValueExtensions`,
  `ValuedFieldTheory/Ramification/HilbertRamification/AlgebraicLocalization`,
  `ClassFieldTheory/KummerTheory/Concrete/SUnitPreparation/FullSUnitKummerExtension`.
- **`CategoryTheory.End` is a structure** here (Mathlib 2026-09-12; a type synonym of `X ⟶ X` upstream), so
  `Rep.norm A : End A` is used as a morphism through `.asHom`: `A.norm.toModuleCatHom` →
  `(Rep.Hom.toModuleCatHom A.norm.asHom)` in `GaloisCohomology/Cyclic/TateComparison`; `X.norm.hom` →
  `X.norm.asHom.hom` and `X.norm.toModuleCatHom` → `X.norm.asHom.toModuleCatHom` (by `sed`) in
  `GaloisCohomology/Cyclic/{NormKernelVanishing,TateH0/NormImage,Herbrand/HerbrandLowDegree/TateComparison}`,
  `GaloisCohomology/Kummer/Abstract/KummerCyclicOperator`,
  `ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/{Core,CyclicNormQuotient,FieldRepresentation,TotallyRamified}`,
  `.../Reciprocity/Construction/{FixedTowerUnitDescent,UnitCohomologyAxiom,UniversalNormDescent}`,
  `ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/HasseNormPrinciple`,
  `ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitExtensionNorm`,
  `ClassFieldTheory/LocalClassFieldTheory/ClassFormation/CohomologyBridge`,
  `ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport`.
- **`ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm`**: Mathlib v4.35.0 has a
  new instance `IsLocalRing.ResidueField.algebraOfIsIntegral`, which instance search finds for the residue degree
  `Module.finrank 𝓀[K] 𝓀[E]` in `localBaseValuation_comp_normToBase_range_eq_residueFinrank`, while the cited lemma
  `v_normUnits_eq_residue_finrank_mul_of_isSeparable` uses `ResidueField.instModule`. Added the lemma
  `LocalClassFieldTheory.residueField_module_eq` (the two module structures are equal, through the scalar tower over
  $\mathcal O_K$), used after `convert` at the two places the proof applied the lemma by `exact`; raised
  `synthInstance.maxHeartbeats` (file) and `maxHeartbeats` (that theorem). The statement is unchanged as text; its
  residue degree is the same number. Its consumer
  `ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalHenselianValuation` elaborates the degree with
  `instModule`: `exact` → `convert ... using 3` closed by `residueField_module_eq.symm`. Same comparison in
  `.../LocalReciprocity/FixedFieldLocalData` (`change ... at hnormInt` → `replace hnormInt ... := by convert ...`; file
  `synthInstance.maxHeartbeats` raised).
- **`NumberField.LiesOver.completionMap`, `continuous_completionMap`** take `v w` explicitly here:
  `ClassFieldTheory/AlgebraicNumberTheory/Adele/InfinitePlaceTensorBlock`, `.../Idele/BaseChange` (`_ _` added).
- **`HeightOneSpectrum.valuation_liesOver`** is stated with `W.asIdeal.ramificationIdx (𝓞 K)` here (upstream:
  `w.asIdeal.ramificationIdx' W.asIdeal`): `ClassFieldTheory/AlgebraicNumberTheory/Completion/AdicCompletionComparison`
  rewrites with Mathlib's `Ideal.ramificationIdx'_eq_ramificationIdx`; same in
  `.../Completion/UnramifiedComparison/IdealToCompletion`.
- `synthInstance.maxHeartbeats` raised to 200000 (instance search is slower here):
  `ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldReciprocity/BigActual`.
- `Function.Injective.isMulTorsionFree` → `Function.Injective.hasUniqueRoots` (with the class rename above) in
  `ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/{CyclotomicZHatBaseChange,FinitePlaceCyclotomicFrobeniusLift}`.
- **`ClassFieldTheory/AlgebraicNumberTheory/Adele/IntegralTensorSupport/Lattice`**: three `omit [NumberField K] in`
  removed (Lean v4.35.0 reports the section variable as referenced by the statements, through
  `RelativeAdeleBasisIndex`), so `exists_integral_relativeBasis_scale`, `chosenRelativeBasisIntegralScale_ne_zero` and
  `chosenRelativeBasisIntegralScale_isIntegral` carry the hypothesis `[NumberField K]`. The only change of a statement
  in the port: an added hypothesis on internal lemmas, held at every use (all in this closure are over number fields).
