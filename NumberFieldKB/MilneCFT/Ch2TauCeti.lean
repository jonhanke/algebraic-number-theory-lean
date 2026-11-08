import NumberFieldKB.MilneCFT.Ch2Corestriction
import NumberFieldKB.MilneCFT.Ch2Tate
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.GroupCohomology.InflationRestriction
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.GroupCohomology.Shapiro
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.GroupHomology.Transfer.Abelianization

/-!
# Milne, *Class Field Theory*, Chapter II: named statements proved from the Tau Ceti port

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter II.

* `prop1_34` — **Proposition 1.34** (inflation–restriction in degree $r$), from Tau Ceti's
  `TauCeti.groupCohomology.mono_HInfRes_f` and `TauCeti.groupCohomology.HInfRes_exact`
  (`RepresentationTheory/Homological/GroupCohomology/InflationRestriction.lean`).
* `example1_27a` — **Example 1.27 (a)** (Shapiro's isomorphism is restriction followed by evaluation at $1$), from
  Tau Ceti's `TauCeti.groupCohomology.coindIso_hom` (`.../GroupCohomology/Shapiro.lean`).
* `prop3_2` — **Proposition 3.2** (corestriction and restriction on $H_1(-,\mathbb Z)$ are the maps of
  abelianizations induced by the inclusion and the transfer), from Tau Ceti's
  `TauCeti.groupHomology.H1AddEquivOfIsTrivial_transfer` (`.../GroupHomology/Transfer/Abelianization.lean`) and
  Mathlib's naturality of $H_1 \cong G^{\mathrm{ab}} \otimes A$.

All Tau Ceti files are ported under `NumberFieldKB/TauCetiPort/` (Apache 2.0).
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits

/-- **Proposition 1.34, proved** (Milne, *CFT*, II, Prop. 1.34, p. 71): if $H^j(H, M) = 0$ for $0 < j < r$, then
$0 \to H^r(G/H, M^H) \to H^r(G, M) \to H^r(H, M)$ is exact. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.34, p. 71"]
theorem prop1_34 : Prop1_34 := by
  refine ⟨fun G _ H _ M r _ hM => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne r)).symm⟩
  have hA : ∀ i < n, IsZero (groupCohomology (res H.subtype M) (i + 1)) :=
    fun i hi => hM (i + 1) (Nat.succ_pos i) (by omega)
  exact ⟨TauCeti.groupCohomology.mono_HInfRes_f M n hA, TauCeti.groupCohomology.HInfRes_exact M n hA⟩

/-- **Example 1.27 (a), proved** (Milne, *CFT*, II, Example 1.27 (a), pp. 68–69): Shapiro's isomorphism
$H^r(G, \operatorname{Ind}_H^G M) \to H^r(H, M)$ is the map induced by $H \hookrightarrow G$ and
$\varphi \mapsto \varphi(1)$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.27 (a), p. 68–69"]
theorem example1_27a : Example1_27a :=
  ⟨fun _ _ H M r => (TauCeti.groupCohomology.coindIso_hom H M r).symm⟩

open groupHomology in
/-- Milne's restriction on $H_1$ (`resH1`, through `Coind` and `indCoindIso`) is Tau Ceti's homological transfer. -/
theorem resH1_eq_transfer {G : Type} [Group G] [DecidableEq G] (H : Subgroup G) [H.FiniteIndex]
    (M : Rep ℤ G) : resH1 H M = TauCeti.groupHomology.transfer M H 1 := by
  obtain rfl : ‹DecidableEq G› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  unfold resH1 TauCeti.groupHomology.transfer
  congr 2

open groupHomology in
/-- **Proposition 3.2, proved** (Milne, *CFT*, II, Prop. 3.2, pp. 79–80): on $H_1(-, \mathbb Z) \simeq (-)^{ab}$,
corestriction is the map induced by the inclusion and restriction is the transfer. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 3.2, p. 79–80"]
theorem prop3_2 : Prop3_2 := by
  refine ⟨fun G _ _ H x => ?_, fun G _ _ _ H g => ?_⟩
  · exact TauCeti.groupHomology.H1AddEquivOfIsTrivial_map (A := Rep.trivial ℤ H ℤ) (B := Rep.trivial ℤ G ℤ)
      H.subtype (𝟙 _) x
  · rw [resH1_eq_transfer]
    have h := TauCeti.groupHomology.H1AddEquivOfIsTrivial_transfer (k := ℤ) H (Rep.trivial ℤ G ℤ)
      ((H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).symm (Additive.ofMul (Abelianization.of g) ⊗ₜ[ℤ] 1))
    rw [AddEquiv.apply_symm_apply] at h
    refine h.trans ?_
    simp

end NumberFieldKB.MilneCFT
