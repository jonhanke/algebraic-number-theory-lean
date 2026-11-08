import NumberFieldKB.Pontryagin.Unconditional
import NumberFieldKB.WeilBNT.CompactCharacters

/-!
# Weil, *Basic Number Theory*, II.§5 (pp. 38–39) and VII.§2 (p. 105): the rows that need Pontryagin duality

The duality theory is in `NumberFieldKB/Pontryagin/`. What is proved:

* II.§5, p. 38, $G\cong G^{**}$: for **discrete** groups (`weil_II_5_text38_duality_discrete`) and for **compact**
  groups (`weil_II_5_text38_duality_compact`). For every locally compact commutative group see
  `NumberFieldKB.WeilBNT.weil_II_5_text38_duality` (`NumberFieldKB/WeilBNT/PontryaginRowsGeneral.lean`).
* II.§5, p. 38, "$G$ is compact iff $G^*$ is discrete, and $G$ discrete iff $G^*$ compact": Mathlib has the direct
  implications (instances on `PontryaginDual`); the converses follow from the duality statement for $G$
  (`weil_II_5_text38_compact_of_discrete_dual`, `weil_II_5_text38_discrete_of_compact_dual`).
* II.§5, p. 38, annihilators: $H^*$ is closed and $H^*\cong(G/H)^*$ (unconditional); $H^{**}=H$ given the duality
  statement for $G/H$, for discrete $G$, and for compact $G$.
* II.§5, p. 39: $H$ open ⇒ $H^*$ compact, $H$ compact ⇒ $H^*$ open (unconditional).
* VII.§2, p. 105: compact $G$ with $\alpha(G)=1$ has the counting measure as dual measure; dually,
  discrete $G$ with counting measure has the normalized Haar measure of $G^*$ as dual measure (unconditional).
* VII.§3, Lemma 4, third assertion: its hypothesis `CharactersSeparatePoints` holds for every compact commutative
  group (`charactersSeparatePoints_of_compact`, `weil_VII_3_lemma4_converse_compact`).

All rows are unconditional. The compact cases were first proved given the Peter–Weyl theorem (the named input
`NumberFieldKB.Pontryagin.PeterWeylTheorem`); they now use the separation of points by characters,
`NumberFieldKB.Pontryagin.Unconditional.charactersSeparate`, which follows from Bochner's theorem
(`NumberFieldKB.Pontryagin.bochnerTheorem`).
-/

open Topology NumberFieldKB.Pontryagin MeasureTheory

noncomputable section

namespace NumberFieldKB.WeilBNT

universe u

section Duality

/-- **Weil, II.§5, p. 38**, discrete groups: $G$ is canonically the dual of $G^*$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (G may be identified with the dual of G*; discrete groups)"]
theorem weil_II_5_text38_duality_discrete {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G] :
    PontryaginDualityStatement G :=
  pontryaginDuality_discrete

/-- **Weil, II.§5, p. 38**, compact groups: $G$ is canonically the dual of $G^*$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (G may be identified with the dual of G*; compact groups)"]
theorem weil_II_5_text38_duality_compact {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] : PontryaginDualityStatement G :=
  Unconditional.pontryaginDuality

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- **Weil, II.§5, p. 38**: if $G^*$ is discrete then $G$ is compact (from the duality statement for $G$). -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (G* discrete implies G compact, given duality for G)"]
theorem weil_II_5_text38_compact_of_discrete_dual (hD : PontryaginDualityStatement G)
    [DiscreteTopology (PontryaginDual G)] : CompactSpace G := by
  obtain ⟨e, -⟩ := hD
  exact e.toHomeomorph.symm.compactSpace

/-- **Weil, II.§5, p. 38**: if $G^*$ is compact then $G$ is discrete (from the duality statement for $G$). -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (G* compact implies G discrete, given duality for G)"]
theorem weil_II_5_text38_discrete_of_compact_dual (hD : PontryaginDualityStatement G)
    [CompactSpace (PontryaginDual G)] : DiscreteTopology G := by
  obtain ⟨e, -⟩ := hD
  exact e.toHomeomorph.symm.discreteTopology

end Duality

section Annihilators

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- **Weil, II.§5, p. 38**: the annihilator $H^*$ of a subgroup is a closed subgroup of $G^*$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (the annihilator H* is a closed subgroup of G*)"]
theorem weil_II_5_text38_annihilator_closed (H : Subgroup G) :
    IsClosed (annihilator H : Set (PontryaginDual G)) :=
  isClosed_annihilator H

/-- **Weil, II.§5, p. 38**: for a closed subgroup $H$, $H^*$ is isomorphic (as a topological group) to the dual of
$G/H$, by $\psi\mapsto\psi\circ q$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (H* is isomorphic to the dual of G/H)"]
theorem weil_II_5_text38_annihilator_dual (H : Subgroup G) [IsClosed (H : Set G)] :
    ∃ e : PontryaginDual (G ⧸ H) ≃ₜ* annihilator H, ∀ ψ g, (e ψ).1 g = ψ (g : G ⧸ H) :=
  ⟨annihilatorEquiv H, fun _ _ => rfl⟩

/-- **Weil, II.§5, p. 38**: the subgroup of $G$ associated with $H^*$ is $H$ itself, given the duality statement for
$G/H$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (the subgroup associated with H* is H; given duality for G/H)"]
theorem weil_II_5_text38_double_annihilator (H : Subgroup G) [IsClosed (H : Set G)]
    (hD : PontryaginDualityStatement (G ⧸ H)) :
    {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H := by
  obtain ⟨e, he⟩ := hD
  have hinj : Function.Injective (dualEval (G ⧸ H)) := by rw [← he]; exact e.injective
  exact doubleAnnihilator_eq H (dualEval_injective_iff.mp hinj)

/-- **Weil, II.§5, p. 38**, discrete groups: the subgroup associated with $H^*$ is $H$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (the subgroup associated with H* is H; discrete groups)"]
theorem weil_II_5_text38_double_annihilator_discrete {G : Type*} [CommGroup G] [TopologicalSpace G]
    [DiscreteTopology G] (H : Subgroup G) :
    {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H :=
  doubleAnnihilator_eq_of_discrete H

/-- **Weil, II.§5, p. 38**, compact groups: the subgroup associated with $H^*$ is $H$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (the subgroup associated with H* is H; compact groups)"]
theorem weil_II_5_text38_double_annihilator_compact {G : Type u} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (H : Subgroup G) [IsClosed (H : Set G)] :
    {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H :=
  Unconditional.doubleAnnihilator_eq H

/-- **Weil, II.§5, p. 39**: if $H$ is open in $G$, then $H^*$ is compact. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.39 (H open implies H* compact)"]
theorem weil_II_5_text39_compact_of_open (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsCompact (annihilator H : Set (PontryaginDual G)) :=
  isCompact_annihilator_of_isOpen H hH

/-- **Weil, II.§5, p. 39**: if $H$ is compact, then $H^*$ is open in $G^*$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.39 (H compact implies H* open)"]
theorem weil_II_5_text39_open_of_compact (H : Subgroup G) (hH : IsCompact (H : Set G)) :
    IsOpen (annihilator H : Set (PontryaginDual G)) :=
  isOpen_annihilator_of_isCompact H hH

end Annihilators

section DualMeasure

/-- **Weil, VII.§2, p. 105**: if $G$ is compact and $\alpha(G)=1$, the dual measure is the counting measure on the
discrete group $G^*$. -/
@[kb "weil1973bnt" "Ch. VII, §2, text p.105 (compact group: the dual of α with α(G) = 1 is counting measure)"]
theorem weil_VII_2_text105_compact {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (α : Measure G) [α.IsHaarMeasure] [IsProbabilityMeasure α] [MeasurableSpace (PontryaginDual G)]
    [MeasurableSingletonClass (PontryaginDual G)] :
    IsDualMeasure α (Measure.count : Measure (PontryaginDual G)) :=
  Unconditional.isDualMeasure_count_of_compact α

/-- **Weil, VII.§2, p. 105**, the dual case: for a discrete group with counting measure, the dual measure is the
Haar measure of total mass $1$ on the compact group $G^*$. -/
@[kb "weil1973bnt" "Ch. VII, §2, text p.105 (inversion and dual measure; discrete groups with counting measure)"]
theorem weil_VII_2_text105_discrete {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (β : Measure (PontryaginDual G)) [IsProbabilityMeasure β] [β.IsMulLeftInvariant] :
    IsDualMeasure (Measure.count : Measure G) β :=
  isDualMeasure_of_discrete β

end DualMeasure

section Lemma4

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]

/-- The characters of a compact commutative group separate points, in the form `CharactersSeparatePoints` used by
VII.§3, Lemma 4 (continuous morphisms into $\mathbb C^\times$). -/
theorem charactersSeparatePoints_of_compact : CharactersSeparatePoints G := by
  constructor
  intro g hg
  obtain ⟨χ, hχ⟩ := Unconditional.charactersSeparate g hg
  refine ⟨Circle.toUnits.comp (χ : G →* Circle), ?_, ?_⟩
  · rw [Units.continuous_iff]
    refine ⟨continuous_subtype_val.comp χ.continuous, ?_⟩
    have : (fun x => ((Circle.toUnits.comp (χ : G →* Circle) x)⁻¹ : ℂˣ).val) =
        fun x => ((χ x⁻¹ : Circle) : ℂ) := by
      funext x; simp [map_inv]
    rw [this]
    exact continuous_subtype_val.comp (χ.continuous.comp continuous_inv)
  · intro h
    apply hχ
    have := congrArg Units.val h
    simpa using Circle.ext this

/-- **Weil, VII.§3, Lemma 4, third assertion** for compact commutative groups: if all characters have finite order,
the open subgroups form a basis of neighbourhoods of $1$. -/
@[kb "weil1973bnt" "Ch. VII, §3, Lemma 4, third assertion (compact commutative groups)"]
theorem weil_VII_3_lemma4_converse_compact
    (hfin : ∀ χ : G →* ℂˣ, Continuous χ → ∃ n : ℕ, 0 < n ∧ ∀ g, χ g ^ n = 1)
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) : ∃ H : OpenSubgroup G, (H : Set G) ⊆ U :=
  weil_VII_3_lemma4_converse charactersSeparatePoints_of_compact hfin hU

end Lemma4

end NumberFieldKB.WeilBNT
