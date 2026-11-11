import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3UnramifiedInv
import NumberFieldKB.MilneCFT.Ch2Example314
import NumberFieldKB.MilneCFT.Ch2Herbrand

/-!
# Milne, *Class Field Theory*, Chapter III §2: the cohomology of ramified extensions

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

**Theorem 2.1 at finite level.** Milne's $\mathrm{inv}_K : H^2(K^{\mathrm{al}}/K) \simeq \mathbb Q/\mathbb Z$ with the
commutative diagram (28), and the relation (29) $\mathrm{inv}_L \circ \mathrm{Res} = [L:K]\,\mathrm{inv}_K$, are
recorded as a *system of invariant maps* (`InvariantSystem`): for every finite Galois $M/K$ a map
$\mathrm{inv}_{M/K} : H^2(M/K) \to \mathbb Q/\mathbb Z$ and, for every subgroup $H$ of $\operatorname{Gal}(M/K)$, a
map $\mathrm{inv}_{M/M^H} : H^2(M/M^H) \to \mathbb Q/\mathbb Z$, injective with image $\frac1n\mathbb Z/\mathbb Z$
($n$ the degree), compatible with inflation, satisfying (29) for restriction, and equal to the invariant map of §1
when the extension is unramified. A family of injective maps compatible with inflation is the same as an injective
map on $H^2(K^{\mathrm{al}}/K) = \varinjlim H^2(M/K)$ (inflation is injective on $H^2$ by Hilbert's Theorem 90).
`Thm2_1` (named statement) says that one and only one such system exists.

## Contents
* `InvariantSystem`, `Thm2_1` (named), `fundClass` (the local fundamental class $u_{L/K}$, definition in prose,
  p. 105), `H2nonGalois` (the group $H^2(L/K)$ of a non-Galois extension, p. 105, definition in prose).
* Lemma 2.2 (proved from the system), Lemma 2.3 (stated; proof below), Lemma 2.4 (named), Lemma 2.5, Lemma 2.6,
  (30) and Lemma 2.7 (proved from the system).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Restriction** $\mathrm{Res} : H^2(M/K) \to H^2(M/M^H)$ (Milne, II, 1.27 (b): the map defined by the inclusion
$H \hookrightarrow \operatorname{Gal}(M/K)$; Mathlib's `groupCohomology.map H.subtype`). -/
noncomputable def resK (M : IntermediateField K Ω) (H : Subgroup Gal(M/K)) : H2 M ⟶ H2rel M H :=
  groupCohomology.map H.subtype (𝟙 _) 2

/-- **Corestriction** $\mathrm{Cor} : H^2(M/M^H) \to H^2(M/K)$ (Milne, II, Example 1.29; Chapter II's `cor`). -/
noncomputable def corK (M : IntermediateField K Ω) [FiniteDimensional K M] (H : Subgroup Gal(M/K)) :
    H2rel M H ⟶ H2 M :=
  letI := Fintype.ofFinite (Gal(M/K) ⧸ H)
  cor H (Rep.ofAlgebraAutOnUnits K M) 2

variable (K Ω)

/-- **A system of invariant maps** (Milne, Chapter III, Theorem 2.1 and (29), at finite level; see the module
docstring). Fields:
* `invK M` : $H^2(M/K) \to \mathbb Q/\mathbb Z$ and `inv M H` : $H^2(M/M^H) \to \mathbb Q/\mathbb Z$;
* injective with image $\frac1{[M:K]}\mathbb Z/\mathbb Z$, resp. $\frac1{|H|}\mathbb Z/\mathbb Z$ (diagram (28),
  bottom row);
* compatible with inflation (`inflK`, `inflRel`);
* `res_top`, `res`: (29), $\mathrm{inv}_{M/M^H} \circ \mathrm{Res} = (\operatorname{Gal}(M/K) : H)\cdot
  \mathrm{inv}_{M/K}$, and the same for $H' \subseteq H$;
* `unramified_top`, `unramified`: on unramified extensions they are the invariant maps of §1 (`invK`, `invRel`),
  defined with the normalized valuation and the Frobenius element. -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 2.1 and (29), the invariant maps inv_{L/K}, p. 103–105"]
structure InvariantSystem where
  invK : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M], H2 M →+ QZ
  inv : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] (H : Subgroup Gal(M/K)),
    H2rel M H →+ QZ
  injective_top : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M],
    Function.Injective (invK M)
  range_top : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M],
    (invK M).range = qzOver (Module.finrank K M)
  injective : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] (H : Subgroup Gal(M/K)),
    Function.Injective (inv M H)
  range : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] (H : Subgroup Gal(M/K)),
    (inv M H).range = qzOver (Nat.card H)
  infl_top : ∀ (M E : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] [FiniteDimensional K E]
    [IsGalois K E] (h : M ≤ E) (x : H2 M), invK E ((inflK h).hom x) = invK M x
  infl : ∀ (M E : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] [FiniteDimensional K E]
    [IsGalois K E] (h : M ≤ E) (H : Subgroup Gal(M/K)) (x : H2rel M H),
    inv E (H.comap (galRestrict h)) ((inflRel h H).hom x) = inv M H x
  res_top : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] (H : Subgroup Gal(M/K))
    (x : H2 M), inv M H ((resK M H).hom x) = H.index • invK M x
  res : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] {H' H : Subgroup Gal(M/K)}
    (h : H' ≤ H) (x : H2rel M H), inv M H' ((resRel M h).hom x) = H'.relIndex H • inv M H x
  unramified_top : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M], IsUnramifiedExt M →
    ∀ {v : Additive Mˣ →+ ℤ} (hv : IsNormalizedOrd M v) {σ : Gal(M/K)}, IsFrobenius M σ →
      invK M = Ch3.invK M hv σ
  unramified : ∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] (H : Subgroup Gal(M/K)),
    IsUnramifiedOver M H → ∀ {v : Additive Mˣ →+ ℤ} (hv : IsNormalizedOrd M v) {σ : Gal(M/K)}
      (hσ : IsFrobeniusOver M H σ), inv M H = invRel M hv H ⟨σ, hσ.1⟩

/-- **Theorem 2.1** (named statement; Milne, p. 103), at finite level: for every local field $K$ there is a
canonical isomorphism $\mathrm{inv}_K : H^2(K^{\mathrm{al}}/K) \to \mathbb Q/\mathbb Z$ such that for every finite
Galois $L/K$ of degree $n$ the diagram (28) commutes, defining $\mathrm{inv}_{L/K} : H^2(L/K) \simeq
\frac1n\mathbb Z/\mathbb Z$; with (29) for restriction to every finite extension. Recorded as: there is exactly one
`InvariantSystem` (canonical: unique given the normalization on unramified extensions). Milne's proof: Lemma 2.2
(from Theorem 1.7 and Proposition 1.8) and Lemma 2.6 ($|H^2(L/K)| = n$, from the Herbrand quotients of Lemma 2.5 and
solvability of local Galois groups), which together show $H^2(K^{\mathrm{un}}/K) \simeq H^2(K^{\mathrm{al}}/K)$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 2.1, p. 103 (input)"]
structure Thm2_1 : Prop where
  exists_unique : Nonempty (InvariantSystem K Ω) ∧
    ∀ s t : InvariantSystem K Ω, (∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M],
      s.invK M = t.invK M) ∧ (∀ (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M]
        (H : Subgroup Gal(M/K)), s.inv M H = t.inv M H)

variable {K Ω}

/-! ## The fundamental class -/

theorem exists_inv_eq (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] : ∃ u : H2 M, s.invK M u = qz (1 / Module.finrank K M) := by
  have : qz (1 / Module.finrank K M) ∈ (s.invK M).range := by
    rw [s.range_top]; exact AddSubgroup.mem_zmultiples _
  exact this

theorem exists_inv_eq_rel (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (H : Subgroup Gal(M/K)) : ∃ u : H2rel M H, s.inv M H u = qz (1 / Nat.card H) := by
  have : qz (1 / Nat.card H) ∈ (s.inv M H).range := by
    rw [s.range]; exact AddSubgroup.mem_zmultiples _
  exact this

/-- **The local fundamental class** $u_{L/K} \in H^2(L/K)$ (Milne, p. 101 for unramified $L$, p. 105 in general,
definition in prose): the element with $\mathrm{inv}_{L/K}(u_{L/K}) = \frac1{[L:K]} \bmod \mathbb Z$. -/
@[kb "milne2020cft" "v4.03, Ch. III, §2, the fundamental class u_{L/K}, p. 105"]
noncomputable def fundClass (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] : H2 M :=
  (exists_inv_eq s M).choose

theorem invK_fundClass (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] : s.invK M (fundClass s M) = qz (1 / Module.finrank K M) :=
  (exists_inv_eq s M).choose_spec

/-- The fundamental class $u_{M/F} \in H^2(M/F)$ of $M$ over $F = M^H$. -/
noncomputable def fundClassRel (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (H : Subgroup Gal(M/K)) : H2rel M H :=
  (exists_inv_eq_rel s M H).choose

theorem inv_fundClassRel (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (H : Subgroup Gal(M/K)) : s.inv M H (fundClassRel s M H) = qz (1 / Nat.card H) :=
  (exists_inv_eq_rel s M H).choose_spec

/-- **$H^2$ of a non-Galois extension** (Milne, p. 105, definition in prose: "we define $H^2(L/K)$ to be the kernel of
the restriction map" $H^2(K^{\mathrm{al}}/K) \to H^2(K^{\mathrm{al}}/L)$), at finite level: for $L \subseteq M$ with
$M/K$ finite Galois, the kernel of $\mathrm{Res} : H^2(M/K) \to H^2(M/L)$. (By the inflation–restriction sequence
this does not depend on $M$, and equals the image of $H^2(L/K)$ when $L/K$ is Galois.) -/
@[kb "milne2020cft" "v4.03, Ch. III, §2, H^2(L/K) for L/K not Galois, p. 105"]
noncomputable def H2nonGalois {L M : IntermediateField K Ω} (h : L ≤ M) : AddSubgroup (H2 M) :=
  (resK M (galOver h)).hom.toAddMonoidHom.ker

/-- $(G : H)\cdot\frac1{[M:K]} = \frac1{|H|}$ in $\mathbb Q/\mathbb Z$. -/
theorem index_smul_qz (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M]
    (H : Subgroup Gal(M/K)) : H.index • qz (1 / Module.finrank K M) = qz (1 / Nat.card H) := by
  rw [qz_nsmul, ← IsGalois.card_aut_eq_finrank, ← H.card_mul_index]
  have : (H.index : ℚ) ≠ 0 := by exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := H))
  congr 1
  push_cast
  field_simp

/-! ## Lemmas 2.2–2.7 -/

/-- **Lemma 2.2** (p. 103). If $L/K$ is Galois of finite degree $n$, then $H^2(L/K)$ contains a subgroup canonically
isomorphic to $\frac1n\mathbb Z/\mathbb Z$. Proved here from the system of invariant maps (Milne derives it from
Theorem 1.7 and Proposition 1.8 before constructing $\mathrm{inv}_K$, as a step towards Theorem 2.1). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 2.2, p. 103"]
theorem lemma_2_2 (s : InvariantSystem K Ω) (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] :
    ∃ f : qzOver (Module.finrank K L) →+ H2 L, Function.Injective f ∧ ∀ y, s.invK L (f y) = y := by
  let e : H2 L ≃+ (s.invK L).range := AddMonoidHom.ofInjective (s.injective_top L)
  let e' : H2 L ≃+ qzOver (Module.finrank K L) := e.trans (AddEquiv.addSubgroupCongr (s.range_top L))
  refine ⟨e'.symm.toAddMonoidHom, e'.symm.injective, fun y => ?_⟩
  have : (e' (e'.symm y) : QZ) = y := by rw [e'.apply_symm_apply]
  exact this

/-- **Lemma 2.6** (p. 105). For $L/K$ finite Galois of degree $n$, $H^2(L/K)$ has order $n$. Proved here from the
system of invariant maps; the cyclic case is also proved from Lemma 2.5 (`lemma_2_6_cyclic`), as in Milne's proof
(which then inducts on $[L:K]$ using solvability of $\operatorname{Gal}(L/K)$). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 2.6, p. 105"]
theorem lemma_2_6 (s : InvariantSystem K Ω) (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] :
    Nat.card (H2 L) = Module.finrank K L := by
  let e : H2 L ≃+ (s.invK L).range := AddMonoidHom.ofInjective (s.injective_top L)
  rw [Nat.card_congr e.toEquiv, s.range_top L]
  exact card_qzOver _ Module.finrank_pos

/-- **Lemma 2.7, (31)** (p. 106): for $L \supseteq E \supseteq K$ with $L/K$ finite Galois,
$\mathrm{Res}(u_{L/K}) = u_{L/E}$ ($E = L^H$). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 2.7 (31), p. 106"]
theorem lemma_2_7_res (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (H : Subgroup Gal(M/K)) : (resK M H).hom (fundClass s M) = fundClassRel s M H := by
  apply s.injective M H
  rw [s.res_top, invK_fundClass, inv_fundClassRel, index_smul_qz]

/-- Restriction $H^2(M/K) \to H^2(M/M^H)$ is onto (Milne, p. 105, from the diagram (28) and (29)). -/
theorem resK_surjective (s : InvariantSystem K Ω) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (H : Subgroup Gal(M/K)) : Function.Surjective (resK M H).hom := by
  intro x
  have hx : s.inv M H x ∈ qzOver (Nat.card H) := by rw [← s.range]; exact ⟨x, rfl⟩
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  refine ⟨k • fundClass s M, s.injective M H ?_⟩
  rw [map_zsmul, lemma_2_7_res, map_zsmul, inv_fundClassRel, hk]

/-- $\mathrm{Cor} \circ \mathrm{Res} = (G : H)$ on $H^2(M/K)$ (Chapter II, Proposition 1.30). -/
theorem corK_resK (h127a : Example1_27a) (M : IntermediateField K Ω) [FiniteDimensional K M]
    (H : Subgroup Gal(M/K)) (y : H2 M) : (corK M H).hom ((resK M H).hom y) = (H.index : ℤ) • y := by
  let _ := Fintype.ofFinite (Gal(M/K) ⧸ H)
  have := prop_1_30_map H h127a (Rep.ofAlgebraAutOnUnits K M) 2
  exact congrArg (fun f => f.hom y) this

/-- **(30)** (p. 105): $\mathrm{inv}_K \circ \mathrm{Cor} = \mathrm{inv}_L$, at finite level: for $K \subseteq E =
M^H \subseteq M$, $\mathrm{inv}_{M/K}(\mathrm{Cor}\,x) = \mathrm{inv}_{M/E}(x)$. Milne's proof: Res is onto (by
(28)), and $\mathrm{Cor} \circ \mathrm{Res} = [E:K]$ (Chapter II, Proposition 1.30, for Mathlib's restriction via
the named Example II.1.27 (a)). -/
@[kb "milne2020cft" "v4.03, Ch. III, §2, (30) inv_K ∘ Cor = inv_L, p. 105"]
theorem eq_30 (s : InvariantSystem K Ω) (h127a : Example1_27a) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] (H : Subgroup Gal(M/K)) (x : H2rel M H) : s.invK M ((corK M H).hom x) = s.inv M H x := by
  obtain ⟨y, rfl⟩ := resK_surjective s M H x
  rw [corK_resK h127a, map_zsmul, s.res_top, natCast_zsmul]

/-- **Lemma 2.7, (32)** (p. 106): $\mathrm{Cor}(u_{L/E}) = [E:K]\,u_{L/K}$ ($E = L^H$, $[E:K] = (G:H)$). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 2.7 (32), p. 106"]
theorem lemma_2_7_cor (s : InvariantSystem K Ω) (h127a : Example1_27a) (M : IntermediateField K Ω)
    [FiniteDimensional K M] [IsGalois K M] (H : Subgroup Gal(M/K)) :
    (corK M H).hom (fundClassRel s M H) = H.index • fundClass s M := by
  apply s.injective_top M
  rw [eq_30 s h127a, inv_fundClassRel, map_nsmul, invK_fundClass, index_smul_qz]

/-- **Lemma 2.7, (33)** (p. 106): if moreover $E/K$ is Galois, $\mathrm{Inf}(u_{E/K}) = [L:E]\,u_{L/K}$. Here the
small field is $M$ and the big one $E$: $\mathrm{Inf}(u_{M/K}) = [E:M]\,u_{E/K}$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 2.7 (33), p. 106"]
theorem lemma_2_7_infl (s : InvariantSystem K Ω) {M E : IntermediateField K Ω} (h : M ≤ E) [FiniteDimensional K M]
    [IsGalois K M] [FiniteDimensional K E] [IsGalois K E] :
    (inflK h).hom (fundClass s M) = (Module.finrank K E / Module.finrank K M) • fundClass s E := by
  apply s.injective_top E
  rw [s.infl_top, invK_fundClass, map_nsmul, invK_fundClass, qz_nsmul]
  obtain ⟨d, hd⟩ := IntermediateField.finrank_dvd_of_le_right h
  have hM : 0 < Module.finrank K M := Module.finrank_pos
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · have := (Module.finrank_pos (R := K) (M := E)); rw [hd, h0] at this; simp at this
    · exact h0
  rw [hd, Nat.mul_div_cancel_left _ hM]
  congr 1
  push_cast
  field_simp

end NumberFieldKB.MilneCFT.Ch3
