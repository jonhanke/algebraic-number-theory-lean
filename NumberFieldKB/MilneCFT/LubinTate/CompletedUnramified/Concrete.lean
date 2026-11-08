import NumberFieldKB.MilneCFT.LubinTate.CompletedUnramified.Completion
import NumberFieldKB.MilneCFT.LubinTate.CompletedUnramified.UnramifiedIntegers
import NumberFieldKB.MilneCFT.LubinTate.Complements

/-!
# The completed integers of the maximal unramified extension

Let `K` be a nonarchimedean local field and `Ω` a separably closed extension of `K`.  Write `Run` for
the integers of the maximal unramified extension `Kun` of `K` inside `Ω`, and `Bun` for the completion
of `Run` with respect to the powers of its maximal ideal.  This file shows that `Bun`, together with
the extension `frobBun` of the Frobenius automorphism, has all the properties Milne asks of his ring
`B` and automorphism `σ` (the structure `IsCompletedUnramifiedInt`): it is a complete discrete
valuation ring in which a uniformizer of `K` stays a uniformizer, its residue field is algebraically
closed, every element is a root of a monic polynomial over the integers of `K` modulo the maximal
ideal, and the automorphism fixes the integers of `K` and acts as the `q`-th power map modulo the
maximal ideal.

We also show that `Run` embeds into `Bun`, that `K` acts on the fraction field `Fun` of `Bun`, that the
Frobenius extends to an automorphism `frobFun` of `Fun` fixing `K`, and that the maximal unramified
extension embeds `K`-linearly into `Fun` (`jun`) compatibly with Frobenius.
-/

open scoped ValuativeRel

open Polynomial

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

namespace NumberFieldKB.MilneCFT.CompletedUnramified

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

/-- The completion of the integers of the maximal unramified extension. -/
abbrev Bun : Type := C (Run K Ω)

/-- The Frobenius automorphism of `Bun`, the extension of that of `Run`. -/
def frobBun : Bun K Ω ≃+* Bun K Ω := completionMap (frobRun K Ω)

theorem algebraMap_run_bun_injective : Function.Injective (algebraMap (Run K Ω) (Bun K Ω)) :=
  AdicCompletion.of_injective (IsLocalRing.maximalIdeal (Run K Ω)) (Run K Ω)

theorem algebraMap_oint_bun (a : 𝒪[K]) :
    algebraMap 𝒪[K] (Bun K Ω) a = algebraMap (Run K Ω) (Bun K Ω) (algebraMap 𝒪[K] (Run K Ω) a) :=
  rfl

theorem isCompletedUnramifiedInt : LocalCFT.IsCompletedUnramifiedInt K (Bun K Ω) (frobBun K Ω) where
  complete := completion_isAdicComplete
  irreducible π hπ := by
    have hne : algebraMap 𝒪[K] (Bun K Ω) π ≠ 0 := by
      rw [algebraMap_oint_bun]
      intro h
      exact (irreducible_algebraMap K Ω hπ).ne_zero (algebraMap_run_bun_injective K Ω (h.trans (map_zero _).symm))
    rw [algebraMap_oint_bun]
    exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
      (by rw [← algebraMap_oint_bun]; exact hne)
      (maximalIdeal_completion_eq_span (irreducible_algebraMap K Ω hπ))
  residue_isAlgClosed := by
    haveI := residue_isAlgClosed K Ω
    exact IsAlgClosed.of_ringEquiv (IsLocalRing.ResidueField (Run K Ω))
      (IsLocalRing.ResidueField (Bun K Ω))
      (RingEquiv.ofBijective _ (completion_residue_bijective (R := Run K Ω)))
  residue_algebraic b := by
    obtain ⟨x, hx⟩ := (completion_residue_bijective (R := Run K Ω)).2 (IsLocalRing.residue _ b)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.map_residue] at hx
    have hba : b - algebraMap (Run K Ω) (Bun K Ω) r ∈ IsLocalRing.maximalIdeal (Bun K Ω) := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hx, sub_self]
    have hint : IsIntegral 𝒪[K] r := IsIntegralClosure.isIntegral 𝒪[K] (Kun K Ω) r
    obtain ⟨P, hP, hPr⟩ := hint
    refine ⟨P, hP, ?_⟩
    have hcomp : (algebraMap (Run K Ω) (Bun K Ω)).comp (algebraMap 𝒪[K] (Run K Ω)) =
        algebraMap 𝒪[K] (Bun K Ω) := RingHom.ext fun a => (algebraMap_oint_bun K Ω a).symm
    have h1 : eval₂ (algebraMap 𝒪[K] (Bun K Ω)) (algebraMap (Run K Ω) (Bun K Ω) r) P = 0 := by
      have := Polynomial.hom_eval₂ P (algebraMap 𝒪[K] (Run K Ω)) (algebraMap (Run K Ω) (Bun K Ω)) r
      rw [hcomp, hPr, map_zero] at this
      exact this.symm
    have h2 := Polynomial.sub_dvd_eval_sub b (algebraMap (Run K Ω) (Bun K Ω) r)
      (P.map (algebraMap 𝒪[K] (Bun K Ω)))
    rw [eval_map, eval_map, h1, sub_zero] at h2
    obtain ⟨c, hc⟩ := h2
    rw [aeval_def]
    have h4 : eval₂ (algebraMap 𝒪[K] (Bun K Ω)) b P ∈ IsLocalRing.maximalIdeal (Bun K Ω) := by
      rw [hc]
      exact Ideal.mul_mem_right _ _ hba
    exact h4
  frob_fix a := by
    rw [algebraMap_oint_bun, frobBun, completionMap_algebraMap, frobRun_algebraMap]
  frob_mod b := by
    exact completionMap_sub_pow_mem (frobRun K Ω) (Nat.card 𝓀[K]) (frobRun_sub_pow_mem K Ω) b

/-- The fraction field of `Bun`. -/
abbrev Fun : Type := FractionRing (Bun K Ω)

theorem oint_fun_injective :
    Function.Injective ((algebraMap (Bun K Ω) (Fun K Ω)).comp (algebraMap 𝒪[K] (Bun K Ω))) := by
  intro a b h
  have h1 : algebraMap (Bun K Ω) (Fun K Ω) (algebraMap 𝒪[K] (Bun K Ω) a) =
      algebraMap (Bun K Ω) (Fun K Ω) (algebraMap 𝒪[K] (Bun K Ω) b) := h
  have h2 := IsFractionRing.injective (Bun K Ω) (Fun K Ω) h1
  rw [algebraMap_oint_bun, algebraMap_oint_bun] at h2
  have h3 := algebraMap_run_bun_injective K Ω h2
  have h4 := congrArg (fun z : Run K Ω => (((z : Kun K Ω)) : Ω)) h3
  have h5 : algebraMap K Ω (algebraMap 𝒪[K] K a) = algebraMap K Ω (algebraMap 𝒪[K] K b) := h4
  exact IsFractionRing.injective 𝒪[K] K ((algebraMap K Ω).injective h5)

/-- The ring map from `K` to the fraction field of `Bun`. -/
def kToFun : K →+* Fun K Ω := IsFractionRing.lift (A := 𝒪[K]) (oint_fun_injective K Ω)

/-- `K` acts on the fraction field of `B` through the fraction field of `𝒪[K]`. -/
instance algebraKFun : Algebra K (Fun K Ω) := (kToFun K Ω).toAlgebra

theorem algebraKFun_apply (a : 𝒪[K]) :
    algebraMap K (Fun K Ω) a = algebraMap (Bun K Ω) (Fun K Ω) (algebraMap 𝒪[K] (Bun K Ω) a) :=
  IsFractionRing.lift_algebraMap (A := 𝒪[K]) (K := K) (oint_fun_injective K Ω) a

/-- The Frobenius automorphism of the fraction field of `Bun`. -/
def frobFun : Fun K Ω ≃+* Fun K Ω := IsFractionRing.ringEquivOfRingEquiv (frobBun K Ω)

theorem frobFun_algebraMap (b : Bun K Ω) :
    frobFun K Ω (algebraMap (Bun K Ω) (Fun K Ω) b) = algebraMap (Bun K Ω) (Fun K Ω) (frobBun K Ω b) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b

theorem frobFun_algebraMap_K (c : K) : frobFun K Ω (algebraMap K (Fun K Ω) c) = algebraMap K (Fun K Ω) c := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[K]) c
  have hb' : (algebraMap 𝒪[K] K b) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hb (IsFractionRing.injective 𝒪[K] K (by simpa using h))
  have key : ∀ x : 𝒪[K], frobFun K Ω (algebraMap K (Fun K Ω) (algebraMap 𝒪[K] K x)) =
      algebraMap K (Fun K Ω) (algebraMap 𝒪[K] K x) := by
    intro x
    rw [show algebraMap K (Fun K Ω) (algebraMap 𝒪[K] K x) = _ from algebraKFun_apply K Ω x,
      frobFun_algebraMap]
    have := (isCompletedUnramifiedInt K Ω).frob_fix x
    rw [this]
  rw [map_div₀, map_div₀, key, key]

instance isFractionRing_run : IsFractionRing (Run K Ω) (Kun K Ω) := by
  haveI : Algebra.IsAlgebraic K (Kun K Ω) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨f, -, hf⟩ := TauCeti.mem_maximalUnramifiedExtension_iff.1 x.2
    have h := Algebra.IsAlgebraic.isAlgebraic (R := K)
      (⟨(x : Ω), hf⟩ : TauCeti.unramifiedExtension K Ω f)
    have h0 : IsAlgebraic K (x : Ω) :=
      (isAlgebraic_algebraMap_iff (R := K) (S := TauCeti.unramifiedExtension K Ω f) (A := Ω)
        (a := ⟨(x : Ω), hf⟩) (Subtype.val_injective)).2 h
    exact (isAlgebraic_algebraMap_iff (R := K) (S := Kun K Ω) (A := Ω) (a := x)
      (Subtype.val_injective)).1 h0
  haveI : Algebra.IsAlgebraic 𝒪[K] (Kun K Ω) := (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
  exact integralClosure.isFractionRing_of_algebraic (A := 𝒪[K]) (L := Kun K Ω)
    (fun x hx => (injective_iff_map_eq_zero (algebraMap 𝒪[K] K)).1
      (IsFractionRing.injective 𝒪[K] K) x
      ((injective_iff_map_eq_zero (algebraMap K (Kun K Ω))).1
        (algebraMap K (Kun K Ω)).injective _ (by exact hx)))

/-- The underlying ring map of `jun`. -/
def junHom : Kun K Ω →+* Fun K Ω :=
  IsFractionRing.lift (A := Run K Ω)
    (g := (algebraMap (Bun K Ω) (Fun K Ω)).comp (algebraMap (Run K Ω) (Bun K Ω)))
    ((IsFractionRing.injective (Bun K Ω) (Fun K Ω)).comp (algebraMap_run_bun_injective K Ω))

theorem junHom_algebraMap (r : Run K Ω) :
    junHom K Ω (algebraMap (Run K Ω) (Kun K Ω) r) =
      algebraMap (Bun K Ω) (Fun K Ω) (algebraMap (Run K Ω) (Bun K Ω) r) :=
  IsFractionRing.lift_algebraMap (A := Run K Ω) (K := Kun K Ω) _ r

/-- The maximal unramified extension embeds in the fraction field of its completed integers. -/
def jun : Kun K Ω →ₐ[K] Fun K Ω where
  toRingHom := junHom K Ω
  commutes' c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[K]) c
    have key : ∀ x : 𝒪[K], junHom K Ω (algebraMap K (Kun K Ω) (algebraMap 𝒪[K] K x)) =
        algebraMap K (Fun K Ω) (algebraMap 𝒪[K] K x) := by
      intro x
      have h1 : algebraMap K (Kun K Ω) (algebraMap 𝒪[K] K x) =
          algebraMap (Run K Ω) (Kun K Ω) (algebraMap 𝒪[K] (Run K Ω) x) := by
        rw [← IsScalarTower.algebraMap_apply 𝒪[K] K, ← IsScalarTower.algebraMap_apply 𝒪[K] (Run K Ω)]
      rw [h1, junHom_algebraMap]
      exact (algebraKFun_apply K Ω x).symm
    change junHom K Ω (algebraMap K (Kun K Ω) _) = algebraMap K (Fun K Ω) _
    simp only [map_div₀, key]

theorem jun_frob (x : Kun K Ω) :
    jun K Ω (TauCeti.maximalUnramifiedFrobenius K Ω x) = frobFun K Ω (jun K Ω x) := by
  have : (junHom K Ω).comp (TauCeti.maximalUnramifiedFrobenius K Ω : Kun K Ω →+* Kun K Ω) =
      (frobFun K Ω : Fun K Ω →+* Fun K Ω).comp (junHom K Ω) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Run K Ω)) (RingHom.ext fun r => ?_)
    have h : TauCeti.maximalUnramifiedFrobenius K Ω (algebraMap (Run K Ω) (Kun K Ω) r) =
        algebraMap (Run K Ω) (Kun K Ω) (frobRun K Ω r) := Subtype.ext (coe_frobRun K Ω r).symm
    change junHom K Ω (TauCeti.maximalUnramifiedFrobenius K Ω (algebraMap (Run K Ω) (Kun K Ω) r)) =
      frobFun K Ω (junHom K Ω (algebraMap (Run K Ω) (Kun K Ω) r))
    rw [h, junHom_algebraMap, junHom_algebraMap, frobFun_algebraMap]
    rfl
  exact RingHom.congr_fun this x

end NumberFieldKB.MilneCFT.CompletedUnramified
