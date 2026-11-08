import NumberFieldKB.MilneCFT.Ch5ConductorBridge
import NumberFieldKB.MilneCFT.Ch5Theorem327Lcm
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.ConductorDiscriminant

/-!
# Milne, *Class Field Theory*, Chapter V, Theorem 3.27 (Führerdiskriminantenproduktformel), unconditional

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Theorem 3.27 (p. 165). Milne omits the proof of the discriminant part ("it is really a statement about local fields").

* `theorem3_27_disc`: $\mathfrak d_{L/K} = \prod_{\chi\in\hat G}\mathfrak f_0(\chi\circ\psi_{L/K})$. From Tau Ceti's global
  conductor–discriminant formula `TauCeti.ClassFieldTheory.relDiscr_eq_finprod_finitePart_abelianConductor`
  (`ClassFieldTheory/Global/AdmissibleModulus/ConductorDiscriminant.lean`: the local formula
  $\sum_\psi f(\psi) = \delta(L_w/K_v)$ of Serre, *Corps locaux*, VI §3, the character dictionary
  $v(\mathfrak f(\chi)) = f(\chi|_{D_w})$ by local reciprocity and Hasse–Arf, and the localization of the different),
  with `remark3_28` ($\mathfrak f(\chi\circ\psi_{L/K})$ is the conductor of $L^{\ker\chi}$) and
  `finite_eq_abelianConductor_finitePart` (our conductor of Remark 3.8 is Tau Ceti's `abelianConductor`). Our
  `relDiscr` (the relative norm of the different) is Tau Ceti's `relDiscr` by definition.
* `theorem3_27`: the named statement `Theorem3_27 K`, with the `lcm` part `T327.theorem3_27_lcm`.
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-- **Theorem 3.27, the discriminant part** (Milne, *CFT*, V, Theorem 3.27, p. 165): for a finite abelian $L/K$ with
group $G$, $\mathfrak d_{L/K} = \prod_{\chi\in\hat G}\mathfrak f_0(\chi\circ\psi_{L/K})$. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.27 (discriminant part)"]
theorem theorem3_27_disc (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (f : (Gal(L/K) →* ℂˣ) → Modulus K) (hf : ∀ χ, IsCharConductor (charOfGal L χ) (f χ)) :
    relDiscr K L = ∏ᶠ χ : Gal(L/K) →* ℂˣ, (f χ).finite := by
  have key := TauCeti.ClassFieldTheory.relDiscr_eq_finprod_finitePart_abelianConductor (K := K) (L := L) ℂ
  change TauCeti.relDiscr (𝓞 K) (𝓞 L) = _
  rw [key]
  refine finprod_congr fun χ => ?_
  obtain ⟨g, hg⟩ := exists_artinConductor (K := K) (IntermediateField.fixedField χ.ker)
  rw [(remark3_28 K).conductor_eq L χ (f χ) g (hf χ) hg, finite_eq_abelianConductor_finitePart _ hg]

variable (K) in
/-- **Theorem 3.27, the conductor-discriminant formula** (Milne, *CFT*, V, Theorem 3.27, p. 165), unconditional: the
named statement `Theorem3_27 K`. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.27"]
theorem theorem3_27 : Theorem3_27 K where
  disc := fun L _ _ _ _ f hf => theorem3_27_disc L f hf
  lcm := fun L _ _ _ _ f hf g => T327.theorem3_27_lcm L f hf g

end NumberFieldKB.MilneCFT
