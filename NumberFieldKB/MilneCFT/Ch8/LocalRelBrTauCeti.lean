import NumberFieldKB.MilneCFT.Ch8.SplitsOverRing
import NumberFieldKB.MilneCFT.Ch4BrauerTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.LocalGlobal.Separable
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.Invariant
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.InfinitePlace
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Places.Semilocal
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Milne, *Class Field Theory*, VIII §4: the local relative Brauer groups, from Tau Ceti

Proves the named inputs `Ch8.LocalRelBrOrder` and `Ch8.RelativeHasse` of Corollary VIII.4.3.
-/

open IsDedekindDomain NumberField TauCeti.ClassFieldTheory
open scoped TensorProduct AdicCompletionExtension

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

section Finite

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **The kernel of $\mathrm{Br}(K_v)\to\mathrm{Br}(L_w)$** at a finite place: a class dies in $L_w$ exactly when
$e f$ times its local invariant vanishes ($[L_w:K_v]=ef$, and restriction multiplies the invariant by the degree). -/
theorem baseChange_adicCompletion_eq_one_iff (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (x : BrauerGroup.{0, 0} (v.adicCompletion K)) :
    Ch4.baseChange (w.adicCompletion L) x = 1 ↔
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) •
        invMap (v.adicCompletion K) (brauerGroupEquivBr _ (Additive.ofMul x)) = 0 := by
  have : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  have := HeightOneSpectrum.adicCompletion_isSeparable v w
  let σ : w.adicCompletion L →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  rw [← Ch4.brauerGroupEquivBr_eq_zero_iff, Ch4.baseChange_eq_tauCeti,
    BrauerBaseChange.brauerGroupEquivBr_baseChange, brBaseChange_eq_brRes _ _ σ,
    ← AddEquiv.map_eq_zero_iff (invMap (w.adicCompletion L)), invMap_brRes,
    HeightOneSpectrum.finrank_adicCompletion]

attribute [local instance] Fintype.ofFinite

variable (L) in
theorem nonempty_liesOver (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} := by
  obtain ⟨w, hw⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
  exact ⟨⟨w, ⟨congrArg HeightOneSpectrum.asIdeal hw.symm⟩⟩⟩

/-- **$\mathrm{Br}(L_v/K_v)$ at a finite place**: a class of $\mathrm{Br}(K_v)$ is split by $K_v\otimes_KL$ exactly
when it dies in every completion $L_w$, $w\mid v$ (by $K_v\otimes_KL\cong\prod_{w\mid v}L_w$, Tau Ceti's
`semilocalEquiv`). -/
theorem mem_localRelBr_adicCompletion_iff (v : HeightOneSpectrum (𝓞 K))
    (x : BrauerGroup.{0, 0} (v.adicCompletion K)) :
    x ∈ localRelBr K L (v.adicCompletion K) ↔
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Ch4.baseChange (w.1.adicCompletion L) x = 1 := by
  haveI := nonempty_liesOver L v
  have key : ∀ A : CSA.{0, 0} (v.adicCompletion K),
      SplitsOverRing (v.adicCompletion K ⊗[K] L) A ↔
        ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
          Ch4.baseChange (w.1.adicCompletion L) (Ch4.BrauerGroup.mk A) = 1 := fun A ↦ by
    rw [SplitsOverRing.congr (TauCeti.semilocalEquiv L v) A, splitsOverRing_pi_iff]
    exact forall_congr' fun w ↦ splitsOverRing_field_iff _ A
  constructor
  · rintro ⟨A, rfl, hA⟩
    exact (key A).1 hA
  · intro h
    induction x using Quotient.inductionOn with
    | h A => exact ⟨A, rfl, (key A).2 h⟩

/-- A subgroup of the Brauer group of a local field cut out by `n • inv = 0`, of order `n`. -/
theorem exists_subgroup_card_torsion (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (hn : 0 < n) :
    ∃ S : Subgroup (BrauerGroup.{0, 0} F),
      (∀ x, x ∈ S ↔ n • invMap F (brauerGroupEquivBr F (Additive.ofMul x)) = 0) ∧ Nat.card S = n := by
  let φ : Additive (BrauerGroup.{0, 0} F) →+ AddCircle (1 : ℚ) :=
    (invMap F).toAddMonoidHom.comp (brauerGroupEquivBr F).toAddMonoidHom
  let S : Subgroup (BrauerGroup.{0, 0} F) :=
    { carrier := {x | n • φ (Additive.ofMul x) = 0}
      mul_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, ofMul_mul, map_add, smul_add] at ha hb ⊢
        rw [ha, hb, add_zero]
      one_mem' := by simp
      inv_mem' := fun {a} ha ↦ by
        simp only [Set.mem_setOf_eq, ofMul_inv, map_neg, smul_neg] at ha ⊢
        rw [ha, neg_zero] }
  refine ⟨S, fun x ↦ Iff.rfl, ?_⟩
  let E : BrauerGroup.{0, 0} F ≃ Ch4.QZ :=
    Additive.ofMul.trans (((brauerGroupEquivBr F).trans (invMap F)).trans Ch4.addCircleEquivQZ).toEquiv
  have e : S ≃ {q : Ch4.QZ // n • q = 0} :=
    E.subtypeEquiv fun x ↦ by
      change n • φ (Additive.ofMul x) = 0 ↔ n • Ch4.addCircleEquivQZ (φ (Additive.ofMul x)) = 0
      rw [← map_nsmul Ch4.addCircleEquivQZ, AddEquiv.map_eq_zero_iff]
  rw [Nat.card_congr e, natCard_torsion_QZ n hn]

/-- The finite-place half of `LocalRelBrOrder`: $\mathrm{Br}(L_v/K_v)$ is a subgroup of order $e f$. -/
theorem localRelBrOrder_finite [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ S : Subgroup (BrauerGroup.{0, 0} (v.adicCompletion K)),
      (S : Set _) = localRelBr K L (v.adicCompletion K) ∧
        Nat.card S = Ch7.localDegree K L (.inr v) := by
  set n := Ch7.localDegree K L (.inr v) with hn_def
  have hn : 0 < n := localDegree_pos K L _
  have hef : ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      w.1.asIdeal.ramificationIdx (𝓞 K) * w.1.asIdeal.inertiaDeg (𝓞 K) = n := by
    intro w
    haveI := w.2
    set Q := Classical.arbitrary (v.asIdeal.primesOver (𝓞 L))
    haveI := Q.2.1
    haveI := Q.2.2
    show _ = Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K)
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.1.asIdeal Gal(L/K),
      ← Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.1.asIdeal Gal(L/K),
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q.1 Gal(L/K),
      Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal Q.1 Gal(L/K)]
  obtain ⟨S, hS, hcard⟩ := exists_subgroup_card_torsion (v.adicCompletion K) n hn
  refine ⟨S, Set.ext fun x ↦ ?_, hcard⟩
  rw [SetLike.mem_coe, hS, mem_localRelBr_adicCompletion_iff]
  obtain ⟨w0⟩ := nonempty_liesOver L v
  constructor
  · intro h w
    haveI := w.2
    rw [baseChange_adicCompletion_eq_one_iff, hef]
    exact h
  · intro h
    haveI := w0.2
    have := (baseChange_adicCompletion_eq_one_iff v w0.1 x).1 (h w0)
    rwa [hef] at this

end Finite

/-! ### Infinite places -/

section Infinite

open scoped NumberField.LiesOver

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Fintype.ofFinite

variable (L) in
theorem nonempty_liesOver_infinite (v : InfinitePlace K) :
    Nonempty {w : InfinitePlace L // w.LiesOver v} := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  exact ⟨⟨w, (InfinitePlace.liesOver_iff_comap_eq).2 hw⟩⟩

/-- **$\mathrm{Br}(L_v/K_v)$ at an infinite place**: a class of $\mathrm{Br}(K_v)$ is split by $K_v\otimes_KL$
exactly when it dies in every completion $L_w$, $w\mid v$ (Tau Ceti's `infiniteSemilocalEquiv`). -/
theorem mem_localRelBr_completion_iff (v : InfinitePlace K) (x : BrauerGroup.{0, 0} v.Completion) :
    x ∈ localRelBr K L v.Completion ↔
      ∀ w : {w : InfinitePlace L // w.LiesOver v}, Ch4.baseChange w.1.Completion x = 1 := by
  haveI := nonempty_liesOver_infinite L v
  have key : ∀ A : CSA.{0, 0} v.Completion,
      SplitsOverRing (v.Completion ⊗[K] L) A ↔
        ∀ w : {w : InfinitePlace L // w.LiesOver v},
          Ch4.baseChange w.1.Completion (Ch4.BrauerGroup.mk A) = 1 := fun A ↦ by
    rw [SplitsOverRing.congr (TauCeti.GlobalNumberFields.infiniteSemilocalEquiv L v) A,
      splitsOverRing_pi_iff]
    exact forall_congr' fun w ↦ splitsOverRing_field_iff _ A
  constructor
  · rintro ⟨A, rfl, hA⟩
    exact (key A).1 hA
  · intro h
    induction x using Quotient.inductionOn with
    | h A => exact ⟨A, rfl, (key A).2 h⟩

omit [NumberField L] in
/-- The Brauer group of a complex completion is trivial. -/
theorem brauerGroup_eq_one_of_isComplex (w : InfinitePlace L) (hw : w.IsComplex)
    (y : BrauerGroup.{0, 0} w.Completion) : y = 1 := by
  rw [← Ch4.brauerGroupEquivBr_eq_zero_iff]
  exact infiniteInvMap_injective w ((infiniteInvMap_eq_zero_of_isComplex w hw _).trans (map_zero _).symm)

/-- Base change along an extension of degree one is injective. -/
theorem baseChange_injective_of_finrank_eq_one {F M : Type} [Field F] [Field M] [Algebra F M]
    (h : Module.finrank F M = 1) : Function.Injective (Ch4.baseChange (K := F) M) := by
  have hb := Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h
  let ψ : F ≃ₐ[F] M := AlgEquiv.ofBijective (Algebra.ofId F M) hb
  letI : Algebra M F := ψ.symm.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower F M F := IsScalarTower.of_algebraMap_eq fun a ↦ (ψ.symm_apply_apply a).symm
  have hc := DFunLike.congr_fun (TauCeti.BrauerGroup.baseChange_comp F M F)
  rw [TauCeti.BrauerGroup.baseChange_self] at hc
  intro x y hxy
  rw [Ch4.baseChange_eq_tauCeti, Ch4.baseChange_eq_tauCeti] at hxy
  have := congrArg (TauCeti.BrauerGroup.baseChange M F) hxy
  rwa [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, hc, hc] at this

omit [NumberField K] in
/-- The Brauer group of a real completion has two elements. -/
theorem natCard_brauerGroup_of_isReal (v : InfinitePlace K) (hv : v.IsReal) :
    Nat.card (BrauerGroup.{0, 0} v.Completion) = 2 := by
  let E : BrauerGroup.{0, 0} v.Completion → AddCircle (1 : ℚ) := fun y ↦
    infiniteInvMap v (brauerGroupEquivBr _ (Additive.ofMul y))
  have hE : Function.Injective E :=
    (infiniteInvMap_injective v).comp ((brauerGroupEquivBr _).injective.comp Additive.ofMul.injective)
  have hrange : Set.range E = (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (2 : ℤ) : Set _) := by
    rw [← range_infiniteInvMap_of_isReal v hv]
    refine Set.ext fun q ↦ ⟨fun ⟨y, hy⟩ ↦ ⟨_, hy⟩, fun ⟨b, hb⟩ ↦ ?_⟩
    exact ⟨Additive.toMul ((brauerGroupEquivBr _).symm b), by simp [E, hb]⟩
  rw [Nat.card_congr ((Equiv.ofInjective E hE).trans (Set.equivOfEq hrange))]
  have e : (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (2 : ℤ) : Set _) ≃ {q : Ch4.QZ // 2 • q = 0} :=
    Ch4.addCircleEquivQZ.toEquiv.subtypeEquiv fun q ↦ by
      change (2 : ℤ) • q = 0 ↔ 2 • Ch4.addCircleEquivQZ q = 0
      rw [← map_nsmul Ch4.addCircleEquivQZ, AddEquiv.map_eq_zero_iff, ← natCast_zsmul]
      rfl
  rw [Nat.card_congr e, natCard_torsion_QZ 2 two_pos]

/-- The infinite-place half of `LocalRelBrOrder`. -/
theorem localRelBrOrder_infinite [IsGalois K L] (v : InfinitePlace K) :
    ∃ S : Subgroup (BrauerGroup.{0, 0} v.Completion),
      (S : Set _) = localRelBr K L v.Completion ∧ Nat.card S = Ch7.localDegree K L (.inl v) := by
  by_cases h : InfinitePlace.RamifiesIn L v
  · have hdeg : Ch7.localDegree K L (.inl v) = 2 := by simp [Ch7.localDegree, h]
    obtain ⟨hv, w0, hw0, hc⟩ := h
    have hall : ∀ w : {w : InfinitePlace L // w.LiesOver v}, w.1.IsComplex := fun w ↦ by
      obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := K)
        (hw0.trans ((InfinitePlace.liesOver_iff_comap_eq).1 w.2).symm)
      rw [← hσ]
      exact InfinitePlace.isComplex_smul_iff.2 hc
    refine ⟨⊤, Set.ext fun x ↦ ?_, ?_⟩
    · simp only [Subgroup.coe_top, Set.mem_univ, true_iff]
      exact (mem_localRelBr_completion_iff v x).2 fun w ↦
        brauerGroup_eq_one_of_isComplex _ (hall w) _
    · rw [hdeg, Subgroup.card_top, natCard_brauerGroup_of_isReal v hv]
  · have hdeg : Ch7.localDegree K L (.inl v) = 1 := by simp [Ch7.localDegree, h]
    have hfin : ∀ w : {w : InfinitePlace L // w.LiesOver v},
        Module.finrank v.Completion w.1.Completion = 1 := fun w ↦ by
      haveI := w.2
      have hcomap := (InfinitePlace.liesOver_iff_comap_eq).1 w.2
      refine InfinitePlace.IsUnramified.finrank_eq_one v (InfinitePlace.isUnramified_iff.2 ?_)
      rcases v.isReal_or_isComplex with hv | hv
      · left
        rcases w.1.isReal_or_isComplex with hw | hw
        · exact hw
        · exact absurd ⟨hv, w.1, hcomap, hw⟩ h
      · right
        rw [hcomap]
        exact hv
    refine ⟨⊥, Set.ext fun x ↦ ?_, by rw [hdeg, Subgroup.card_bot]⟩
    rw [SetLike.mem_coe, Subgroup.mem_bot, mem_localRelBr_completion_iff]
    obtain ⟨w0⟩ := nonempty_liesOver_infinite L v
    constructor
    · rintro rfl w
      exact map_one _
    · intro hx
      exact baseChange_injective_of_finrank_eq_one (hfin w0) ((hx w0).trans (map_one _).symm)

end Infinite

/-! ### The named inputs of Corollary VIII.4.3 -/

section Inputs

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- **`LocalRelBrOrder`, proved** (Milne, *CFT*, VIII §4, p. 240; local class field theory through Tau Ceti's local
invariant): for $L/K$ Galois, $\mathrm{Br}(L_v/K_v)$ is a subgroup of $\mathrm{Br}(K_v)$ of order the local degree
$n_v$ at every place $v$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, §4, p. 240, Br(L_v/K_v) of order n_v"]
theorem localRelBrOrder [IsGalois K L] : LocalRelBrOrder K L where
  finite v := localRelBrOrder_finite v
  infinite v := localRelBrOrder_infinite v

open scoped NumberField.LiesOver in
/-- **`RelativeHasse`, proved** (Milne, *CFT*, VIII, Theorem 4.2 for $L$, read over $K$): a class of $\mathrm{Br}(K)$
whose localizations are all split by $K_v\otimes_KL$ is split by $L$. Its image in $\mathrm{Br}(L)$ is trivial at
every place $w$ of $L$ (the localization at $w$ factors through $K_v$, $w\mid v$, and dies in $L_w$), hence trivial by
the Hasse principle for $L$ (`Ch4.example2_14e L`). -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Thm. 4.2 for L, read over K"]
theorem relativeHasse [IsGalois K L] : RelativeHasse K L where
  mem_relBrauer x hfin hinf := by
    obtain ⟨-, -, -, -, -, hinj, -⟩ := (Ch4.example2_14e L).exact
    rw [Ch4.relBrauer, MonoidHom.mem_ker]
    apply hinj
    refine Prod.ext (funext fun u ↦ ?_) (funext fun u ↦ ?_)
    · set v := HeightOneSpectrum.under (𝓞 K) u
      have h := (mem_localRelBr_adicCompletion_iff v _).1 (hfin v) ⟨u, inferInstance⟩
      change Ch4.baseChange (u.adicCompletion L) (Ch4.baseChange L x) =
        Ch4.baseChange (u.adicCompletion L) 1
      rw [map_one]
      change Ch4.baseChange (u.adicCompletion L) (Ch4.baseChange (v.adicCompletion K) x) = 1 at h
      rw [Ch4.baseChange_eq_tauCeti, Ch4.baseChange_eq_tauCeti] at h ⊢
      rw [← MonoidHom.comp_apply, TauCeti.BrauerGroup.baseChange_comp] at h ⊢
      exact h
    · set v := u.comap (algebraMap K L)
      haveI : u.LiesOver v := (InfinitePlace.liesOver_iff_comap_eq).2 rfl
      have h := (mem_localRelBr_completion_iff v _).1 (hinf v) ⟨u, inferInstance⟩
      change Ch4.baseChange u.Completion (Ch4.baseChange L x) = Ch4.baseChange u.Completion 1
      rw [map_one]
      change Ch4.baseChange u.Completion (Ch4.baseChange v.Completion x) = 1 at h
      rw [Ch4.baseChange_eq_tauCeti, Ch4.baseChange_eq_tauCeti] at h ⊢
      rw [← MonoidHom.comp_apply, TauCeti.BrauerGroup.baseChange_comp] at h ⊢
      exact h

/-- **Corollary 4.3, unconditional** (Milne, *CFT*, VIII, Cor. 4.3, p. 241): for a finite Galois extension $L/K$ of
number fields, $0\to\mathrm{Br}(L/K)\to\bigoplus_v\mathrm{Br}(L_v/K_v)\to\frac1{n_0}\mathbb Z/\mathbb Z\to0$ is
exact. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Cor. 4.3, p. 241"]
theorem corollary4_3 [IsGalois K L] : Corollary4_3 K L :=
  corollary4_3_of K L (Ch4.example2_14e K) (localRelBrOrder K L) (relativeHasse K L)

end Inputs

end NumberFieldKB.MilneCFT.Ch8
