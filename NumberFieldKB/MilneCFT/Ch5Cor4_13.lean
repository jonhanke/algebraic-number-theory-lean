import NumberFieldKB.MilneCFT.Ch5IdelesChar
import NumberFieldKB.Ideles.RelativeNormTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Ideles.Norm.Open

/-!
# Milne, *Class Field Theory*, Chapter V, Corollary 4.13, from Tau Ceti

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

Tau Ceti proves that for every finite extension $L/K$ of number fields some idele congruence subgroup lies in
$\mathrm{Nm}_{L/K}\mathbb I_L$ (`TauCeti.GlobalNumberFields.exists_ideleCongruenceSubgroup_le_range_ideleNormMap`,
ported under `NumberFieldKB/TauCetiPort/`, Tau Ceti main `67aa1716`, Apache 2.0). This file translates it:

* **`Modulus.ofTauCeti`**: Tau Ceti's modulus `TauCeti.GlobalNumberFields.Modulus K` (a nonzero ideal and a finite set
  of real places) as ours (`Modulus K`: the same ideal, the set of the same real places).
* **`idelesW_ofTauCeti`**: our $W_\mathfrak m$ (`idelesW`) is Tau Ceti's `ideleCongruenceSubgroup` for the same
  modulus. The conditions agree place by place: units outside the support, $\equiv 1 \bmod \mathfrak p^{\mathrm{ord}}$ at
  the primes of the support (our `Modulus.ord` and Tau Ceti's `Modulus.exponent` are the same multiplicity), positive at
  the real places of the modulus.
* **`cor4_13`**: Corollary 4.13 unconditional, with the idele norm comparison
  `NumberFieldKB.Ideles.ideleRelNorm_eq_ideleNormMap`.
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-- Tau Ceti's modulus as ours: the same finite part, and the real places of its infinite part. -/
def Modulus.ofTauCeti (𝔪 : TauCeti.GlobalNumberFields.Modulus K) : Modulus K where
  finite := 𝔪.finitePart
  finite_ne_bot := 𝔪.finitePart_ne_bot
  infinite := {w | ∃ hw : w.IsReal, ⟨w, hw⟩ ∈ 𝔪.infinitePart}
  isReal_of_mem := fun _ ⟨hw, _⟩ => hw

/-- **Our $W_\mathfrak m$ is Tau Ceti's idele congruence subgroup** for the same modulus. -/
theorem idelesW_ofTauCeti (𝔪 : TauCeti.GlobalNumberFields.Modulus K) :
    idelesW (Modulus.ofTauCeti 𝔪) = TauCeti.GlobalNumberFields.ideleCongruenceSubgroup 𝔪 := by
  ext x
  rw [TauCeti.GlobalNumberFields.mem_ideleCongruenceSubgroup_iff]
  constructor
  · rintro ⟨⟨hinf, hfin⟩, hunit⟩
    refine ⟨fun v hv => hunit v hv, fun v hv => hfin v hv, fun w hw => ?_⟩
    exact hinf w.1 ⟨w.2, hw⟩
  · rintro ⟨hunit, hfin, hinf⟩
    refine ⟨⟨fun w hw => ?_, fun v hv => hfin v hv⟩, fun v hv => hunit v hv⟩
    obtain ⟨hw', hmem⟩ := hw
    exact hinf ⟨w, hw'⟩ hmem

variable (K) in
/-- **Corollary 4.13, unconditional** (Milne, *CFT*, V, Corollary 4.13, p. 177): for every finite extension $L/K$ of
number fields there is a modulus $\mathfrak m$ with $W_\mathfrak m\subseteq\mathrm{Nm}_{L/K}(\mathbb I_L)$. From Tau
Ceti's `exists_ideleCongruenceSubgroup_le_range_ideleNormMap` through `idelesW_ofTauCeti` and the idele norm
comparison `NumberFieldKB.Ideles.ideleRelNorm_eq_ideleNormMap`. -/
@[kb "milne2020cft" "Ch. V, Corollary 4.13"]
theorem cor4_13 : Cor4_13 K := by
  refine ⟨fun L _ _ _ => ?_⟩
  obtain ⟨𝔪, h𝔪⟩ := TauCeti.GlobalNumberFields.exists_ideleCongruenceSubgroup_le_range_ideleNormMap K L
  refine ⟨Modulus.ofTauCeti 𝔪, ?_⟩
  rw [idelesW_ofTauCeti]
  intro y hy
  obtain ⟨x, hx⟩ := h𝔪 hy
  exact ⟨x, (NumberFieldKB.Ideles.ideleRelNorm_eq_ideleNormMap (Module.finBasis K L) x).trans hx⟩

end NumberFieldKB.MilneCFT
