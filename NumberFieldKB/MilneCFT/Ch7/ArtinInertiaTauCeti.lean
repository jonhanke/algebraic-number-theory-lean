import NumberFieldKB.MilneCFT.Ch7.HilbertIdelic
import NumberFieldKB.MilneCFT.Ch7.IdealExistence
import NumberFieldKB.MilneCFT.Ch7.ExistenceTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.Conductor.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# The named input `ArtinInertia` (Milne, *CFT*, V, Proposition 5.2 with local class field theory), proved from Tau Ceti

`ArtinInertia K`: for a finite abelian $L/K$, if the idèlic Artin map is trivial on the units of $K_v$ then $v$ is
unramified in $L$, and if it is trivial on $K_w^\times$ at a real place $w$ then $w$ does not ramify. Proved here
(`artinInertia`) as follows. By the uniqueness in Summary 5.10 (`idelicArtin_unique`) the map is Tau Ceti's
(`idelicArtinTauCeti`); its restriction to $K_v^\times$ is the local Artin symbol (`globalArtinMap_local`,
`globalArtinMap_infiniteLocal`), whose kernel is the local norm group (`localArtinAt_eq_one_iff_mem_normGroup`,
`infiniteLocalArtinAt_eq_one_iff_mem_normGroup`).

* Finite places: if every unit of $K_v$ is a norm from $L_w$, the conductor exponent of $L_w/K_v$ is $0$, so $L_w/K_v$ is
  unramified (`conductorExponent_eq_zero_iff`); its ramification index is the global one
  (`ramificationIndex_adicCompletion`), so $w$ is unramified over $v$ (Mathlib's `Ideal.ramificationIdx_eq_one_iff`).
* Real places: if $w$ ramifies there is a complex place above, where the norms from $\mathbb C$ are the positive reals
  (`Completion.mem_normGroup_iff_of_isRamified`); $-1$ is not one.

With it, Chapter V's corrected existence theorem `ExistenceTheoremArtin` (Theorem 3.6) holds unconditionally
(`existenceTheoremArtin`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped IsMulCommutative AdicCompletionExtension

noncomputable section

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

theorem eq_idelicArtinTauCeti {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφ : IsIdelicArtinMap L φ)
    (hK : ∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) : φ = idelicArtinTauCeti L :=
  idelicArtin_unique L φ _ hφ (isIdelicArtinMap_tauCeti L) hK (idelicArtinTauCeti_principal L)

/-- **The named input `ArtinInertia`, proved** from Tau Ceti's local–global compatibility and local class field theory
(ported). -/
@[kb "milne2020cft" "Ch. V, Prop. 5.2 with Ch. I, Thm. 1.1 (inertia)"]
theorem artinInertia : ArtinInertia K := by
  refine ⟨fun L _ _ _ _ φ hφ hK v hv => ?_, fun L _ _ _ _ φ hφ hK w hw hw1 => ?_⟩
  · rw [eq_idelicArtinTauCeti K φ hφ hK] at hv
    intro P hP hlo
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    let w : HeightOneSpectrum (𝓞 L) := ⟨P, hP, hP0⟩
    have : w.asIdeal.LiesOver v.asIdeal := hlo
    have : w.asIdeal.IsMaximal := w.isMaximal
    -- every unit of `K_v` is a local norm from `L_w`
    have hnorm : TauCeti.unitFiltration (v.adicCompletion K) 0 ≤
        TauCeti.normGroup (v.adicCompletion K) (w.adicCompletion L) := by
      intro u hu
      rw [HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff] at hu
      have h1 := hv u hu
      rw [idelicArtinTauCeti_eq_one_iff,
        TauCeti.ClassFieldTheory.globalArtinMap_local, ofMul_eq_zero] at h1
      exact (TauCeti.ClassFieldTheory.localArtinAt_eq_one_iff_mem_normGroup v w u).1 h1
    have hc : TauCeti.ClassFieldTheory.conductorExponent (v.adicCompletion K) (w.adicCompletion L) = 0 :=
      Nat.eq_zero_of_le_zero ((TauCeti.ClassFieldTheory.conductorExponent_le_iff _ _).2 hnorm)
    have hunr := (TauCeti.ClassFieldTheory.conductorExponent_eq_zero_iff (v.adicCompletion K) (w.adicCompletion L)).1 hc
    have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      rw [← HeightOneSpectrum.ramificationIndex_adicCompletion (K := K) (L := L) v w]
      exact (TauCeti.isUnramified_iff_ramificationIndex_eq_one _ _).1 hunr
    exact (Ideal.ramificationIdx_eq_one_iff).1 he
  · rw [eq_idelicArtinTauCeti K φ hφ hK] at hw1
    rintro ⟨-, w', hw', hc⟩
    have : w'.LiesOver w := by subst hw'; infer_instance
    have hram : w'.IsRamified K := InfinitePlace.isRamified_iff.mpr ⟨hc, by rw [hw']; exact hw⟩
    have h1 := hw1 (-1)
    rw [idelicArtinTauCeti_eq_one_iff,
      TauCeti.ClassFieldTheory.globalArtinMap_infiniteLocal, ofMul_eq_zero] at h1
    have hmem := (TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_one_iff_mem_normGroup w w' (-1)).1 h1
    rw [InfinitePlace.Completion.mem_normGroup_iff_of_isRamified hram hw] at hmem
    simp at hmem
    norm_num at hmem

/-- **Theorem 3.6 (the existence theorem, in the corrected form with the Artin map), unconditional** (Milne, *CFT*, V,
Theorem 3.6). -/
@[kb "milne2020cft" "Ch. V, Theorem 3.6"]
theorem existenceTheoremArtin : ExistenceTheoremArtin K :=
  existenceTheoremArtin_of_idelic (K := K) (idelicReciprocity K) (idelicExistence K) (artinInertia K)

end NumberFieldKB.MilneCFT
