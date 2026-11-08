import NumberFieldKB.Pontryagin.Unconditional
import NumberFieldKB.Pontryagin.Poisson
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, II.§5 and VII.§2: duality for every locally compact commutative group

The rows of Weil II.§5 (pp. 38–39) and VII.§2 (p. 105) that need the duality theorem for a general locally compact
commutative group. They are unconditional: Bochner's theorem, once a named input, is proved in
`NumberFieldKB.Pontryagin.BochnerProof` (the proof of Tau Ceti, ported), and the rows below are the theorems of
`NumberFieldKB.Pontryagin.Unconditional`. The special cases (discrete and compact groups) are in
`NumberFieldKB.WeilBNT.PontryaginRows`. The rows of VII.§2, pp. 105–106, on a discrete subgroup $\Gamma$ with
$G/\Gamma$ compact (quotient measure, "admissible for $(G,\Gamma)$", Poisson summation) are at the end
(`NumberFieldKB/Pontryagin/QuotientMeasure.lean`, `NumberFieldKB/Pontryagin/Poisson.lean`).

Groups are written multiplicatively (Weil writes them additively); $G^*$ = Mathlib's `PontryaginDual G`.
-/

open MeasureTheory Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

open NumberFieldKB.Pontryagin

universe u

section Duality

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G]

/-- **Weil, II.§5, p. 38**: $G$ may be identified with the dual of $G^*$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (G may be identified with the dual of G*)"]
theorem weil_II_5_text38_duality : PontryaginDualityStatement G :=
  Unconditional.pontryaginDuality

/-- **Weil, II.§5, p. 38**: $G$ is compact iff $G^*$ is discrete. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (G compact iff G* discrete)"]
theorem weil_II_5_text38_compact_iff :
    CompactSpace G ↔ DiscreteTopology (PontryaginDual G) :=
  Unconditional.compactSpace_iff_discreteTopology_dual

/-- **Weil, II.§5, p. 38** ("and conversely"): $G$ is discrete iff $G^*$ is compact. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (G discrete iff G* compact)"]
theorem weil_II_5_text38_discrete_iff :
    DiscreteTopology G ↔ CompactSpace (PontryaginDual G) :=
  Unconditional.discreteTopology_iff_compactSpace_dual

end Duality

section Annihilators

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] (H : Subgroup G) [IsClosed (H : Set G)]

omit [T2Space G] in
/-- **Weil, II.§5, p. 38**: the subgroup of $G$ associated with $H^*$ is $H$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (the subgroup associated with H* is H)"]
theorem weil_II_5_text38_double_annihilator_general :
    {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H :=
  Unconditional.doubleAnnihilator_eq H

/-- **Weil, II.§5, p. 38**: $H$ is isomorphic, as a topological group, to the dual of $G^*/H^*$. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.38 (H is isomorphic to the dual of G*/H*)"]
theorem weil_II_5_text38_subgroup_dual_quotient :
    Nonempty (H ≃ₜ* PontryaginDual (PontryaginDual G ⧸ annihilator H)) :=
  ⟨Unconditional.subgroupEquivDualQuotient H⟩

omit [T2Space G] in
/-- **Weil, II.§5, p. 39**: $H$ is open iff $H^*$ is compact. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.39 (H open iff H* compact)"]
theorem weil_II_5_text39_open_iff :
    IsOpen (H : Set G) ↔ IsCompact (annihilator H : Set (PontryaginDual G)) :=
  Unconditional.isOpen_iff_isCompact_annihilator H

/-- **Weil, II.§5, p. 39**: $H$ is compact iff $H^*$ is open. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.39 (H compact iff H* open)"]
theorem weil_II_5_text39_compact_iff :
    IsCompact (H : Set G) ↔ IsOpen (annihilator H : Set (PontryaginDual G)) :=
  Unconditional.isCompact_iff_isOpen_annihilator H

omit [T2Space G] in
/-- **Weil, II.§5, p. 39**: $G/H$ is compact iff $H^*$ is discrete. -/
@[kb "weil1973bnt" "Ch. II, §5, text p.39 (G/H compact iff H* discrete)"]
theorem weil_II_5_text39_quotient_compact_iff :
    CompactSpace (G ⧸ H) ↔ DiscreteTopology (annihilator H) :=
  Unconditional.compactSpace_quotient_iff H

end Annihilators

section DualMeasure

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (α : Measure G) [α.IsHaarMeasure] [α.Regular]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- **Weil, VII.§2, p. 105**: there is a Haar measure $\alpha^*$ on $G^*$, the dual measure, with
$\Phi(g)=\int\Phi^*(g^*)\langle-g,g^*\rangle\,d\alpha^*$ for every admissible $\Phi$. -/
@[kb "weil1973bnt" "Ch. VII, §2, text p.105 (the dual measure exists and Fourier inversion holds)"]
theorem weil_VII_2_text105_dual_measure :
    ∃ β : Measure (PontryaginDual G), β.IsHaarMeasure ∧ β.Regular ∧ IsDualMeasure α β :=
  Unconditional.exists_isDualMeasure α

/-- **Weil, VII.§2, p. 105**: the dual measure is unique among regular Haar measures. -/
@[kb "weil1973bnt" "Ch. VII, §2, text p.105 (the dual measure is unique)"]
theorem weil_VII_2_text105_dual_measure_unique (β β' : Measure (PontryaginDual G))
    [β.IsHaarMeasure] [β.Regular] [β'.IsHaarMeasure] [β'.Regular] (h : IsDualMeasure α β)
    (h' : IsDualMeasure α β') : β = β' :=
  Unconditional.isDualMeasure_unique α β β' h h'

omit [α.IsHaarMeasure] [α.Regular] in
/-- **Weil, VII.§2, p. 105**: if $\alpha$ is replaced by $c\alpha$, its dual is replaced by $c^{-1}\alpha^*$. -/
@[kb "weil1973bnt" "Ch. VII, §2, text p.105 (the dual of cα is c⁻¹α*)"]
theorem weil_VII_2_text105_dual_smul {β : Measure (PontryaginDual G)} (h : IsDualMeasure α β) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) : IsDualMeasure (c • α) (c⁻¹ • β) :=
  isDualMeasure_smul h hc0 hct

omit [α.IsHaarMeasure] [α.Regular] in
/-- **Weil, VII.§2, p. 105**: under an identification $\iota:G\cong G^*$ there is a self-dual Haar measure, and it is
unique. -/
@[kb "weil1973bnt" "Ch. VII, §2, text p.105 (under G ≅ G* there is a unique self-dual Haar measure)"]
theorem weil_VII_2_text105_selfDual (ι : G ≃ₜ* PontryaginDual G) :
    (∃ α' : Measure G, α'.IsHaarMeasure ∧ α'.Regular ∧ IsDualMeasure α' (α'.map ι)) ∧
      ∀ α₁ α₂ : Measure G, α₁.IsHaarMeasure → α₁.Regular → α₂.IsHaarMeasure → α₂.Regular →
        IsDualMeasure α₁ (α₁.map ι) → IsDualMeasure α₂ (α₂.map ι) → α₁ = α₂ :=
  ⟨Unconditional.exists_isDualMeasure_map_self ι, fun α₁ α₂ _ _ _ _ h₁ h₂ =>
    Unconditional.isDualMeasure_map_self_unique ι α₁ α₂ h₁ h₂⟩

end DualMeasure

section Poisson

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (α : Measure G) [α.IsHaarMeasure] [α.Regular]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

/-- **Weil, VII.§2, p. 105**: the quotient measure $\bar\alpha$ on $G/\Gamma$ (of $\alpha$ by the counting measure of
$\Gamma$): a Haar measure on $G/\Gamma$ with $\int_Gf\,d\alpha=\int_{G/\Gamma}\sum_\gamma f(g\gamma)\,d\bar\alpha$ for
continuous compactly supported $f$; Weil's $\alpha(G/\Gamma)$ is `quotientMeasure Γ α univ`. -/
@[kb "weil1973bnt" "Ch. VII, §2, text p.105 (the quotient measure on G/Γ and α(G/Γ))"]
theorem weil_VII_2_text105_quotient_measure :
    (quotientMeasure Γ α).IsHaarMeasure ∧ IsFiniteMeasure (quotientMeasure Γ α) ∧
      ∀ f : G → ℂ, Continuous f → HasCompactSupport f →
        ∫ g, f g ∂α = ∫ x, periodize Γ f x ∂(quotientMeasure Γ α) :=
  ⟨inferInstance, inferInstance, fun _ hfc hf => integral_eq_integral_periodize Γ α hfc hf⟩

omit [α.IsHaarMeasure] [α.Regular] [CompactSpace (G ⧸ Γ)] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [DiscreteTopology Γ] in
/-- **Weil, VII.§2, p. 105**: $\Phi$ is admissible for $(G,\Gamma)$ iff it is admissible for $G$ and
$\sum_\gamma\Phi(g\gamma)$, $\sum_{\gamma^*}\Phi^*(g^*\gamma^*)$ converge absolutely and uniformly on compact sets
(the definition `NumberFieldKB.Pontryagin.IsAdmissibleFor`). -/
@[kb "weil1973bnt" "Ch. VII, §2, text p.105 (admissible for (G, Γ))"]
theorem weil_VII_2_text105_admissible_pair [MeasurableSpace (PontryaginDual G)] (β : Measure (PontryaginDual G))
    (Φ : G → ℂ) :
    IsAdmissibleFor α β Γ Φ ↔ AbstractFourier.IsAdmissible α β Φ ∧ (∀ g : G, Summable fun γ : Γ => ‖Φ (g * γ)‖) ∧
      (∀ K : Set G, IsCompact K → SummableUniformlyOn (fun (γ : Γ) (g : G) => Φ (g * γ)) K) ∧
      (∀ χ : PontryaginDual G, Summable fun γ : annihilator Γ => ‖AbstractFourier.fourierLCA α Φ (χ * γ)‖) ∧
      (∀ K : Set (PontryaginDual G), IsCompact K → SummableUniformlyOn
        (fun (γ : annihilator Γ) (χ : PontryaginDual G) => AbstractFourier.fourierLCA α Φ (χ * γ)) K) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

/-- **Weil, VII.§2, p. 106, Poisson summation formula (1)**: if $\alpha(G/\Gamma)=1$ and $\Phi$ is admissible for
$(G,\Gamma)$, then $\sum_{\gamma\in\Gamma}\Phi(\gamma)=\sum_{\gamma^*\in\Gamma^*}\Phi^*(\gamma^*)$. -/
@[kb "weil1973bnt" "Ch. VII, §2, text p.106 (Poisson summation formula (1))"]
theorem weil_VII_2_text106_poisson [MeasurableSpace (PontryaginDual G)] (β : Measure (PontryaginDual G))
    (hα : quotientMeasure Γ α Set.univ = 1) {Φ : G → ℂ} (hΦ : IsAdmissibleFor α β Γ Φ) :
    ∑' γ : Γ, Φ γ = ∑' χ : annihilator Γ, AbstractFourier.fourierLCA α Φ χ :=
  poisson_summation Γ α β hα hΦ

end Poisson

end NumberFieldKB.WeilBNT
