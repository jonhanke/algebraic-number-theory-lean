import NumberFieldKB.MilneCFT.Ch5Cor4_13
import NumberFieldKB.MilneCFT.Ch5CharactersUncond

/-!
# The conductor of Milne, *CFT*, V, Remark 3.8, is Tau Ceti's `abelianConductor`

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Remark 3.8 (p. 158).

For a finite abelian extension $E/K$ of number fields, a modulus $\mathfrak m$ of $K$ satisfies our
`ArtinFactorsThrough E m` (the primes outside $\mathfrak m$ are unramified and $\psi_{E/K}$ kills $i(K_{\mathfrak m,1})$)
exactly when Tau Ceti's `IsAdmissibleModulus K E` holds for the same modulus (`artinFactorsThrough_iff_isAdmissible`).
Hence the conductor `IsArtinConductor E g` of Remark 3.8 has the finite part of Tau Ceti's
`TauCeti.ClassFieldTheory.abelianConductor K E` (`finite_eq_abelianConductor_finitePart`).

* `Modulus.toTauCeti`: our modulus as Tau Ceti's (the same ideal, the finite set of the same real places), a section of
  `Modulus.ofTauCeti` (`Modulus.ofTauCeti_toTauCeti`).
* The comparison goes through $W_\mathfrak m$ (`idelesW_ofTauCeti`), the kernel of the idèlic Artin map
  (`ker_idelicArtinTauCeti`, Tau Ceti's `ker_ideleClassArtinMap`) and `artinFactorsThrough_iff`.
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

open Classical in
/-- Our modulus as Tau Ceti's: the same finite part, and the (finite) set of its real places. -/
def Modulus.toTauCeti (m : Modulus K) : TauCeti.GlobalNumberFields.Modulus K where
  finitePart := m.finite
  finitePart_ne_bot := m.finite_ne_bot
  infinitePart := Finset.univ.filter fun w => w.1 ∈ m.infinite

theorem Modulus.mem_toTauCeti_infinitePart (m : Modulus K) (w : {w : InfinitePlace K // w.IsReal}) :
    w ∈ (Modulus.toTauCeti m).infinitePart ↔ w.1 ∈ m.infinite := by
  simp [Modulus.toTauCeti]

theorem Modulus.ofTauCeti_toTauCeti (m : Modulus K) : Modulus.ofTauCeti (Modulus.toTauCeti m) = m := by
  obtain ⟨f, hf, inf, hinf⟩ := m
  simp only [Modulus.ofTauCeti, Modulus.toTauCeti, Finset.mem_filter, Finset.mem_univ, true_and, Modulus.mk.injEq,
    true_and]
  ext w
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hinf w h, h⟩⟩

theorem idelesW_eq_ideleCongruenceSubgroup (m : Modulus K) :
    idelesW m = TauCeti.GlobalNumberFields.ideleCongruenceSubgroup (Modulus.toTauCeti m) := by
  conv_lhs => rw [← Modulus.ofTauCeti_toTauCeti m]
  exact idelesW_ofTauCeti _

variable (E : Type) [Field E] [NumberField E] [Algebra K E] [IsAbelianGalois K E]

/-- An idèle lies in $K^\times\mathrm{Nm}(\mathbb I_E)$ iff its class is a norm of an idèle class of $E$ (Tau Ceti's
norm map). -/
theorem mem_ideleNormGroup_iff_tauCeti (x : IdeleGroup (𝓞 K) K) :
    x ∈ ideleNormGroup (K := K) E ↔ (x : IdeleClassGroup (𝓞 K) K) ∈
      (TauCeti.GlobalNumberFields.ideleClassNormMap K E :
        IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K).range := by
  rw [← ker_idelicArtinTauCeti, MonoidHom.mem_ker, idelicArtinTauCeti_apply, ← MonoidHom.mem_ker,
    TauCeti.ClassFieldTheory.ker_ideleClassArtinMap]

/-- **Remark 3.8's "the Artin map factors through $C_\mathfrak m$" is Tau Ceti's admissibility.** -/
theorem artinFactorsThrough_iff_isAdmissible (m : Modulus K) :
    ArtinFactorsThrough E m ↔
      TauCeti.ClassFieldTheory.IsAdmissibleModulus K E (Modulus.toTauCeti m) := by
  rw [artinFactorsThrough_iff (idelicReciprocity K) E m, idelicArtinOf_idelicReciprocity,
    ker_idelicArtinTauCeti, TauCeti.ClassFieldTheory.isAdmissibleModulus_iff]
  have hW : idelesW m ≤ ideleNormGroup (K := K) E ↔
      TauCeti.GlobalNumberFields.raySubgroup (Modulus.toTauCeti m) ≤
        (TauCeti.GlobalNumberFields.ideleClassNormMap K E :
          IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K).range := by
    rw [idelesW_eq_ideleCongruenceSubgroup]
    constructor
    · intro h c hc
      obtain ⟨x, hx, rfl⟩ := TauCeti.GlobalNumberFields.mem_raySubgroup_iff.1 hc
      exact (mem_ideleNormGroup_iff_tauCeti E x).1 (h hx)
    · intro h x hx
      exact (mem_ideleNormGroup_iff_tauCeti E x).2
        (h (TauCeti.GlobalNumberFields.mem_raySubgroup_iff.2 ⟨x, hx, rfl⟩))
  constructor
  · rintro ⟨-, h⟩
    exact hW.1 h
  · intro h
    have h' := hW.2 h
    refine ⟨fun v hv => unramified_of_idelesW E m ?_ hv, h'⟩
    rwa [ker_idelicArtinTauCeti]

/-- **The conductor of Remark 3.8 has the finite part of Tau Ceti's `abelianConductor`.** -/
theorem finite_eq_abelianConductor_finitePart {g : Modulus K} (hg : IsArtinConductor E g) :
    g.finite = (TauCeti.ClassFieldTheory.abelianConductor K E).finitePart := by
  set c := TauCeti.ClassFieldTheory.abelianConductor K E
  -- `c ∣ g`: `g` is admissible.
  have h1 : c ∣ Modulus.toTauCeti g :=
    (TauCeti.ClassFieldTheory.isAdmissibleModulus_iff_abelianConductor_dvd _).1
      ((artinFactorsThrough_iff_isAdmissible E g).1 hg.1)
  -- `g ∣ c`: `c` is admissible, so the Artin map factors through `C_c`.
  have h2 : g.Dvd (Modulus.ofTauCeti c) := by
    refine hg.2 _ ((artinFactorsThrough_iff_isAdmissible E _).2 ?_)
    refine (TauCeti.ClassFieldTheory.isAdmissibleModulus_iff_abelianConductor_dvd _).2 ?_
    refine TauCeti.GlobalNumberFields.Modulus.dvd_iff.2 ⟨dvd_refl _, fun w hw => ?_⟩
    exact (Modulus.mem_toTauCeti_infinitePart _ w).2 ⟨w.2, hw⟩
  exact dvd_antisymm h2.1 (TauCeti.GlobalNumberFields.Modulus.dvd_iff.1 h1).1

end NumberFieldKB.MilneCFT
