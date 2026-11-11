import NumberFieldKB.MilneCFT.Ch8.Quadratic
import NumberFieldKB.Ideles.RelativeNormTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.HasseNorm.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter VIII, Theorem 3.1 (the Hasse norm theorem) from the Tau Ceti port

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, Theorem 3.1,
p. 234.

The named statement `HasseNormTheorem` is proved here (`hasseNormTheorem`) from Tau Ceti's cyclic Hasse norm theorem
`TauCeti.ClassFieldTheory.isGlobalNorm_iff_isLocalNormEverywhere` (ported under `NumberFieldKB/TauCetiPort/`, Apache
2.0, the Tau Ceti contributors; its proof is Milne's: $H^1(G, C_L) = 0$).

Milne's local norms here (`IsLocalNorm`, `IsLocalNormInf`) are those of Chapter VII: $a$ is a local norm at $v$ when the
idèle with component $a$ at $v$ and $1$ elsewhere is a norm from $\mathbb I_L$. Tau Ceti's (`IsFiniteLocalNorm`,
`IsInfiniteLocalNorm`) are norms from the étale algebra $K_v\otimes_KL$. The two agree by Tau Ceti's placewise
description of the idèle norms, `mem_range_ideleNormMap_iff` (`isLocalNorm_iff`, `isLocalNormInf_iff`). The
finiteness of the non-norm places follows from Tau Ceti's `exists_unit_preimages_of_isUnramifiedAt` (units at an
unramified place are local norms).
-/

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- Chapter VII's norm ideles are Tau Ceti's: $\mathrm{Nm}_{L/K}(\mathbb I_L)$. -/
theorem normIdeles_eq_range_ideleNormMap :
    Ch7.normIdeles K L = (TauCeti.GlobalNumberFields.ideleNormMap K L).toMonoidHom.range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (Ideles.ideleRelNorm_eq_ideleNormMap (Module.finBasis K L) y).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, Ideles.ideleRelNorm_eq_ideleNormMap (Module.finBasis K L) y⟩

/-- An element of $K_v^\times$ lies in Chapter VII's local norm group exactly when it is a norm from
$K_v\otimes_KL$. -/
theorem mem_localNormGroup_iff (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    x ∈ Ch7.localNormGroup L v ↔
      x ∈ (TauCeti.Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range := by
  classical
  change IdeleGroup.ofAdicCompletion (𝓞 K) K v x ∈ Ch7.normIdeles K L ↔ _
  rw [normIdeles_eq_range_ideleNormMap, TauCeti.GlobalNumberFields.mem_range_ideleNormMap_iff]
  constructor
  · rintro ⟨h, -⟩
    simpa [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self] using h v
  · intro h
    refine ⟨fun v' => ?_, fun w => ?_⟩
    · by_cases hv : v' = v
      · subst hv
        simpa [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self] using h
      · rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne v' hv]
        exact one_mem _
    · simp

/-- An element of $K_w^\times$ ($w$ infinite) lies in Chapter VII's local norm group exactly when it is a norm from
$K_w\otimes_KL$. -/
theorem mem_localNormGroupInf_iff (w : InfinitePlace K) (x : w.Completionˣ) :
    x ∈ Ch7.localNormGroupInf L w ↔
      x ∈ (TauCeti.Algebra.normUnits w.Completion (S := w.Completion ⊗[K] L)).range := by
  classical
  change IdeleGroup.ofCompletion (𝓞 K) K w x ∈ Ch7.normIdeles K L ↔ _
  rw [normIdeles_eq_range_ideleNormMap, TauCeti.GlobalNumberFields.mem_range_ideleNormMap_iff]
  constructor
  · rintro ⟨-, h⟩
    simpa using h w
  · intro h
    refine ⟨fun v => ?_, fun w' => ?_⟩
    · simp
    · by_cases hw : w' = w
      · subst hw
        simpa using h
      · simp [hw]

/-- Milne's local norm at a finite prime is Tau Ceti's. -/
theorem isLocalNorm_iff (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    IsLocalNorm K L a v ↔ TauCeti.GlobalNumberFields.IsFiniteLocalNorm K L v a :=
  mem_localNormGroup_iff K L v _

/-- Milne's local norm at an infinite prime is Tau Ceti's. -/
theorem isLocalNormInf_iff (a : Kˣ) (w : InfinitePlace K) :
    IsLocalNormInf K L a w ↔ TauCeti.GlobalNumberFields.IsInfiniteLocalNorm K L w a :=
  mem_localNormGroupInf_iff K L w _

/-- An element of $K^\times$ is a local norm at all but finitely many finite primes (those unramified in $L$ at which
it is a unit). -/
theorem finite_not_isLocalNorm (a : Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | ¬ IsLocalNorm K L a v}.Finite := by
  have hu := TauCeti.eventually_isUnramifiedAt_liesOver K L
  have hx := (FiniteAdeleRing.isUnit_iff.mp
    (IdeleGroup.toFiniteIdele (𝓞 K) K (IdeleGroup.unitEmbedding (𝓞 K) K a)).isUnit).2
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, IsLocalNorm K L a v := by
    filter_upwards [hu, hx] with v hv hxv
    rw [isLocalNorm_iff, TauCeti.GlobalNumberFields.isFiniteLocalNorm_def,
      TauCeti.mem_range_normUnits_adicCompletion_iff]
    have hval : Valued.v ((Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a :
        (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      have h1 : v.valuation K (a : K) = 1 := by simpa using hxv
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a : K)).trans h1
    obtain ⟨u, hu, -⟩ := TauCeti.exists_unit_preimages_of_isUnramifiedAt K L v _ hval (by
      obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
        (S := 𝓞 L) v.asIdeal
      have hP0 := Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩
      exact ⟨⟨⟨P, hP.isPrime, hP0⟩, hPv⟩, hv _⟩)
    exact ⟨u, hu⟩
  exact Filter.eventually_cofinite.mp hev

/-- **Theorem 3.1, the Hasse norm theorem, unconditional** (Milne, *CFT*, VIII, Theorem 3.1, p. 234): for a cyclic
extension $L/K$ of number fields and $a\in K^\times$, $a$ is a local norm at almost every prime, and if it is a local
norm everywhere it is a norm from $L$. From Tau Ceti's cyclic Hasse norm theorem (ported). -/
@[kb "milne2020cft" "Ch. VIII, Theorem 3.1, p. 234 (Hasse norm theorem)"]
theorem hasseNormTheorem : HasseNormTheorem K where
  almost_all L _ _ _ _ _ a := finite_not_isLocalNorm K L a
  norm L _ _ _ _ hc a hfin hinf := by
    haveI : IsCyclic Gal(L/K) := hc
    have hloc : TauCeti.GlobalNumberFields.IsLocalNormEverywhere K L a :=
      ⟨fun v => (isLocalNorm_iff K L a v).1 (hfin v), fun w => (isLocalNormInf_iff K L a w).1 (hinf w)⟩
    obtain ⟨y, hy⟩ := TauCeti.mem_normGroup_iff.1
      ((TauCeti.ClassFieldTheory.isGlobalNorm_iff_isLocalNormEverywhere K L a).2 hloc)
    exact ⟨y, hy⟩

end NumberFieldKB.MilneCFT.Ch8
