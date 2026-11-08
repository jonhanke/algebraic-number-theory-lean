import NumberFieldKB.MilneCFT.LubinTate.HerbrandTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Herbrand.HasseArf.Abelian

/-!
# The Hasse–Arf theorem from Tau Ceti (Milne, *CFT*, I, Theorem 4.6)

Tau Ceti proves that every upper ramification break of a finite abelian extension of nonarchimedean local fields is
an integer (`TauCeti.LocalFieldsRamification.hasseArf`, `TauCeti/NumberTheory/LocalField/Herbrand/HasseArf/Abelian`,
ported under `NumberFieldKB/TauCetiPort/` from Tau Ceti main `85f3eb55`, Apache 2.0). Our named statement `HasseArf`
is in the lower numbering: if $G_i\ne G_{i+1}$ then $\varphi(i)\in\mathbb Z$. The Herbrand function carries lower
breaks to upper breaks (`TauCeti.LocalFieldsRamification.upperJump_herbrand_iff`), and our filtrations and Herbrand
function are Tau Ceti's (`ramificationGroup_eq_lowerRamificationGroup`, `herbrandPhi_eq_herbrand`,
`LubinTate/HerbrandTauCeti.lean`), so `hasseArf` proves the named statement.
-/

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

open TauCeti.LocalFieldsRamification

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Theorem 4.6 (Hasse–Arf), proved** (Milne, *CFT*, I, Theorem 4.6, p. 47; Serre, *Local Fields*, V.7): the named
statement `HasseArf` holds: for a finite abelian extension $L/K$ inside $\Omega$, if $G_i\ne G_{i+1}$ then
$\varphi_{L/K}(i)$ is an integer. From Tau Ceti's `TauCeti.LocalFieldsRamification.hasseArf` (ported), with $L$
given Tau Ceti's local-field structure. -/
@[kb "milne2020cft" "Ch. I, Theorem 4.6"]
theorem hasseArf : HasseArf K Ω := by
  refine ⟨fun L i hne => ?_⟩
  let _ : ValuativeRel L.toField := TauCeti.finiteIntermediateFieldValuativeRel K Ω L.toField
  let _ : TopologicalSpace L.toField := TauCeti.finiteIntermediateFieldTopology K Ω L.toField
  have : ValuativeExtension K L.toField := TauCeti.finiteIntermediateField_valuativeExtension K Ω L.toField
  have : IsNonarchimedeanLocalField L.toField :=
    TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toField
  have hi : (-1 : ℝ) ≤ ((i : ℤ) : ℝ) := by
    have : (0 : ℝ) ≤ ((i : ℤ) : ℝ) := by exact_mod_cast Int.natCast_nonneg i
    linarith
  -- The lower break at `i`, in Tau Ceti's numbering.
  have hlt : lowerRamificationGroup K L.toField ((i : ℤ) + 1) < lowerRamificationGroup K L.toField (i : ℤ) := by
    have h1 := ramificationGroup_eq_lowerRamificationGroup L.toField i
    have h2 := ramificationGroup_eq_lowerRamificationGroup L.toField (i + 1)
    push_cast at h2
    rw [← h1, ← h2]
    refine lt_of_le_of_ne ?_ (Ne.symm hne)
    rw [h1, h2]
    exact lowerRamificationGroup_antitone K L.toField (by omega)
  have hlow : LowerJump K L.toField ⟨(i : ℤ), hi⟩ := (lowerJump_intCast_iff K L.toField hi).2 hlt
  have hup := (upperJump_herbrand_iff K L.toField _).2 hlow
  obtain ⟨z, hz⟩ := TauCeti.LocalFieldsRamification.hasseArf K L.toField hup
  refine ⟨z, ?_⟩
  have hi' : (-1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  rw [herbrandPhi_eq_herbrand L.toField (i : ℝ) hi', ← hz]
  congr 2

end NumberFieldKB.MilneCFT.LocalCFT
