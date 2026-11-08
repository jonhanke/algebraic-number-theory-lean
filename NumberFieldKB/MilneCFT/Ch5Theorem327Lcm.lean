import NumberFieldKB.MilneCFT.Ch5CharactersUncond
import NumberFieldKB.MilneCFT.Ch5ConductorUncond

/-!
# Milne, *Class Field Theory*, V Theorem 3.27: the conductor is the lcm of the character conductors

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Theorem 3.27,
p. 165.

`Theorem3_27` has two fields: `disc` (the conductor–discriminant formula $\mathfrak d_{L/K} =
\prod_\chi \mathfrak f_0(\chi)$, a local statement, not proved here) and `lcm`
($\mathfrak f(L/K) = \mathrm{lcm}_\chi \mathfrak f(\chi\circ\psi_{L/K})$). This file proves the second one
(`theorem3_27_lcm`), unconditionally:
* `aft_iff_tc`: $\psi_{L/K}$ factors through $C_\mathfrak m$ iff $W_\mathfrak m$ is in the kernel of Tau Ceti's
  idèlic Artin map (unramifiedness outside $\mathfrak m$ follows, `unramified_of_idelesW`);
* `aft_iff_forall_fixedField`: $L \subseteq L_\mathfrak m$ iff every $L^{\ker\chi} \subseteq L_\mathfrak m$
  (characters separate the points of $\mathrm{Gal}(L/K)$, and the Artin map of $L^{\ker\chi}$ is the restriction
  of that of $L$, `tc_restrict`);
* `aft_iff_dvd`: $\psi_{M/K}$ factors through $C_\mathfrak m$ iff the conductor of $M$ divides $\mathfrak m$;
* Remark 3.28 (`remark3_28`): $\mathfrak f(\chi\circ\psi_{L/K}) = \mathfrak f(L^{\ker\chi}/K)$.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT
namespace T327

variable {K : Type} [Field K] [NumberField K]

/-- $\psi_{L/K}$ factors through $C_\mathfrak m$ iff $W_\mathfrak m \subseteq \ker\phi_{L/K}$. -/
theorem aft_iff_tc (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (m : Modulus K) :
    ArtinFactorsThrough L m ↔ idelesW m ≤ (idelicArtinTauCeti L).ker := by
  rw [artinFactorsThrough_iff (idelicReciprocity K) L m, idelicArtinOf_idelicReciprocity L]
  exact ⟨fun h => h.2, fun h => ⟨fun v hv => unramified_of_idelesW L m h hv, h⟩⟩

/-- If $\mathfrak c$ is the conductor of $M$, then $\psi_{M/K}$ factors through $C_\mathfrak m$ iff
$\mathfrak c \mid \mathfrak m$. -/
theorem aft_iff_dvd (M : Type) [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M] {c : Modulus K}
    (hc : IsArtinConductor M c) (m : Modulus K) : ArtinFactorsThrough M m ↔ c.Dvd m := by
  refine ⟨hc.2 m, fun h => ?_⟩
  exact (aft_iff_tc M m).2 ((idelesW_le_of_dvd h).trans ((aft_iff_tc M c).1 hc.1))

/-- Tau Ceti's Artin map of a subextension is the restriction of that of `L`. -/
theorem tc_restrict (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (F : IntermediateField K L) [IsAbelianGalois K F] (x : IdeleGroup (𝓞 K) K) :
    AlgEquiv.restrictNormalHom F (idelicArtinTauCeti L x) = idelicArtinTauCeti F x := by
  apply Abelianization.of_injective
  have h1 := TauCeti.ClassFieldTheory.globalArtinMap_comp K L F.val IsSepClosed.lift
  have h2 := congrArg (fun G => G (Additive.ofMul (x : IdeleClassGroup (𝓞 K) K))) h1
  simp only [AddMonoidHom.comp_apply] at h2
  conv_rhs => rw [idelicArtinTauCeti_apply, TauCeti.ClassFieldTheory.of_ideleClassArtinMap K F
    (IsSepClosed.lift.comp F.val), ← h2]
  rw [← IntermediateField.restrictNormalHom_val, ← Abelianization.map_of, of_idelicArtinTauCeti]
  rfl

/-- Characters to `ℂˣ` separate the points of a finite abelian Galois group. -/
theorem eq_one_of_forall_char (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (σ : Gal(L/K)) (h : ∀ χ : Gal(L/K) →* ℂˣ, χ σ = 1) : σ = 1 := by
  let _ : CommGroup Gal(L/K) := { (inferInstance : Group Gal(L/K)) with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  by_contra hσ
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Gal(L/K) ℂ hσ
  exact hχ (h χ)

/-- $L \subseteq L_\mathfrak m$ iff $L^{\ker\chi}\subseteq L_\mathfrak m$ for every character $\chi$. -/
theorem aft_iff_forall_fixedField (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (m : Modulus K) :
    ArtinFactorsThrough L m ↔
      ∀ χ : Gal(L/K) →* ℂˣ, ArtinFactorsThrough (IntermediateField.fixedField χ.ker) m := by
  simp only [aft_iff_tc]
  constructor
  · intro h χ x hx
    rw [MonoidHom.mem_ker, ← tc_restrict, MonoidHom.mem_ker.1 (h hx), map_one]
  · intro h x hx
    rw [MonoidHom.mem_ker]
    refine eq_one_of_forall_char L _ fun χ => ?_
    have := MonoidHom.mem_ker.1 (h χ hx)
    rw [← tc_restrict] at this
    exact (restrictNormalHom_fixedField_eq_one_iff L χ _).1 this

/-- **Theorem 3.27, the lcm part** (Milne, *CFT*, V, Theorem 3.27, p. 165): $\mathfrak f(L/K)$ is the least
common multiple of the conductors $\mathfrak f(\chi\circ\psi_{L/K})$ — in the form of the field `lcm` of
`Theorem3_27`. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.27 (conductor = lcm of the conductors of the characters)"]
theorem theorem3_27_lcm (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (f : (Gal(L/K) →* ℂˣ) → Modulus K) (hf : ∀ χ, IsCharConductor (charOfGal L χ) (f χ)) (g : Modulus K) :
    IsArtinConductor L g ↔ ∀ m : Modulus K, g.Dvd m ↔ ∀ χ, (f χ).Dvd m := by
  -- each `f χ` is the conductor of the fixed field of `ker χ`
  have hcond : ∀ χ : Gal(L/K) →* ℂˣ, IsArtinConductor (IntermediateField.fixedField χ.ker) (f χ) := by
    intro χ
    obtain ⟨c, hc⟩ := exists_artinConductor (K := K) (IntermediateField.fixedField χ.ker)
    have := (remark3_28 K).conductor_eq L χ (f χ) c (hf χ) hc
    rw [this]
    exact hc
  have key : ∀ m : Modulus K, ArtinFactorsThrough L m ↔ ∀ χ, (f χ).Dvd m := fun m => by
    rw [aft_iff_forall_fixedField]
    exact forall_congr' fun χ => aft_iff_dvd _ (hcond χ) m
  constructor
  · intro hg m
    rw [← key]
    exact (aft_iff_dvd L hg m).symm
  · intro h
    refine ⟨(key g).2 ((h g).1 ⟨dvd_refl _, subset_rfl⟩), fun m hm => (h m).2 ((key m).1 hm)⟩

end T327
end NumberFieldKB.MilneCFT
