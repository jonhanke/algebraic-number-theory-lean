import NumberFieldKB.HeckeL.Dedekind
import QuadFormsKB.Weil.NonArch

/-!
# The Fourier transform of a factorizable Schwartz–Bruhat function

The function `SchwartzBruhat.fourier` is the function $\hat\Phi = \hat f_\infty\otimes\bigotimes_v\hat f_v$. Here it is again
a factorizable Schwartz–Bruhat function (`SchwartzBruhat.fourierSB`, `coe_fourierSB`): $\hat f_v$ is locally
constant with compact support (`IsSchwartzBruhatLC.fourierV`), hence a finite combination of coset
indicators (QuadFormsKB's `isSchwartzBruhatV_of_mem_SBK`), and $\hat f_v = \mathbf 1_{\mathcal O_v}$ wherever
$f_v = \mathbf 1_{\mathcal O_v}$ and $v\nmid\mathfrak d_F$ (`fourierV_charO`). So the Euler product applies to
$\hat\Phi$.
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Set WithZero
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

open GlobalZeta LocalZeta

/-- **A locally constant compactly supported function on $F_v$ is a finite combination of coset indicators.** -/
theorem isSchwartzBruhatV_of_isSchwartzBruhatLC {v : HeightOneSpectrum (𝓞 F)} {f : v.adicCompletion F → ℂ}
    (hf : IsSchwartzBruhatLC v f) : IsSchwartzBruhatV v f := by
  obtain ⟨N, hN⟩ := hf.exists_support
  obtain ⟨M, hM⟩ := hf.exists_uniform
  refine QuadFormsKB.WeilRep.isSchwartzBruhatV_of_mem_SBK v ⟨‖HN.ϖ v ^ (-N)‖, ‖HN.ϖ v ^ M‖,
    norm_pos_iff.mpr (zpow_ne_zero _ (HN.ϖ_ne_zero v)), fun x hx => ?_, fun x h hh => hM x h ?_⟩
  · rw [Valued.toNormedField.norm_le_iff, valued_ϖ_zpow, neg_neg]
    exact hN x hx
  · rwa [Valued.toNormedField.norm_le_iff, valued_ϖ_zpow] at hh

/-- At a place $v\nmid\mathfrak d_F$: $\hat{\mathbf 1}_{\mathcal O_v} = \mathbf 1_{\mathcal O_v}$. -/
theorem fourierV_charO_of_diffExp {v : HeightOneSpectrum (𝓞 F)} (hd : diffExp v = 0) :
    fourierV v (ballIndV v 0 0) = ballIndV v 0 0 := by
  rw [fourierV_charO, volO_toReal, hd]
  funext y
  simp

/-- **The Fourier transform of a factorizable Schwartz–Bruhat function**, as a factorizable Schwartz–Bruhat function
(`coe_fourierSB`). -/
def _root_.NumberFieldKB.SchwartzBruhat.fourierSB (Φ : SchwartzBruhat F) : SchwartzBruhat F where
  fInf := SchwartzBruhat.fourierInfSchwartz Φ.fInf
  fv := fun v => fourierV v (Φ.fv v)
  S := Φ.S ∪ diffSet F
  isSchwartzBruhat := fun v _ => isSchwartzBruhatV_of_isSchwartzBruhatLC (sb_isSchwartzBruhatLC_all Φ v).fourierV
  eq_charO := fun v hv => by
    simp only [Finset.mem_union, not_or] at hv
    rw [Φ.eq_charO v hv.1, fourierV_charO_of_diffExp (diffExp_eq_zero hv.2)]

theorem coe_fourierSB (Φ : SchwartzBruhat F) : (Φ.fourierSB : Adeles F → ℂ) = Φ.fourier := by
  funext y
  rw [SchwartzBruhat.apply, SchwartzBruhat.fourier]
  congr 1
  change SchwartzBruhat.fourierInfSchwartz Φ.fInf y.1 = _
  rw [SchwartzBruhat.coe_fourierInfSchwartz]

end

end NumberFieldKB.HeckeL
