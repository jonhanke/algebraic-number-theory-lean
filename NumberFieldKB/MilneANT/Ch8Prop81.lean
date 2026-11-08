import NumberFieldKB.MilneANT.Ch8Extensions
import NumberFieldKB.MilneANT.Ch8CompleteUnique
import NumberFieldKB.MilneANT.Ch8CompleteExists
import NumberFieldKB.MilneANT.Ch8TensorFactor
import NumberFieldKB.MilneANT.Ch7OstrowskiComplete

/-!
# Milne, *Algebraic Number Theory*, Propositions 8.1 and 8.2 and Corollary 8.4, unconditional

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`, pp. 135–136.

Let $|\cdot|$ be an absolute value on a field $K$, $L = K[\alpha]$ a finite separable extension and $f$ the minimal
polynomial of $\alpha$. Following Milne's proof:

* to a monic irreducible factor $g$ of $f$ in $\hat K[X]$ attach the absolute value on $L$ obtained from the unique
  extension of the norm of $\hat K$ to the finite extension $\hat K[X]/(g)$ (Theorem 7.38, existence
  `exists_absoluteValue_extension`, uniqueness `absoluteValue_eq_of_complete`), through $L \to \hat K[X]/(g)$,
  $\alpha \mapsto X$ (`psi`);
* to an extension $w$ attach the minimal polynomial of $\alpha$ over $\hat K$ in $L_w$ (`phi`);
* these are mutually inverse (`corrEquiv`), and $\hat K[X]/(\varphi(w)) \to L_w$ is an isomorphism
  (`hMap_bijective`: its image is complete and contains $L$, hence is $L_w$);
* with $\hat K \otimes_K L \cong \prod_g \hat K[X]/(g)$ (`exists_tensor_algEquiv_pi`) this gives Proposition 8.2.

Milne assumes $|\cdot|$ archimedean or discrete (his Theorem 7.38 is proved only in those cases); here the extension
theorem is available for every complete field, so `prop_8_1` and `prop_8_2` discharge the named statements
`Prop8_1` and `Prop8_2` without using that hypothesis.
-/

open scoped Polynomial TensorProduct
namespace NumberFieldKB.MilneANT
noncomputable section

namespace Prop81

section Basic

variable {K L : Type} [Field K] [Field L] [Algebra K L] (v : AbsoluteValue K ℝ)

theorem norm_algebraMap_completion (c : K) : ‖algebraMap K v.Completion c‖ = v c := by
  show ‖((WithAbs.toAbs v c : WithAbs v) : v.Completion)‖ = _
  rw [UniformSpace.Completion.norm_coe]
  rfl

theorem norm_coe_completion (w : AbsoluteValue L ℝ) (a : L) : ‖(a : w.Completion)‖ = w a := by
  show ‖((WithAbs.toAbs w a : WithAbs w) : w.Completion)‖ = _
  rw [UniformSpace.Completion.norm_coe]
  rfl

theorem norm_algebraMap_ext (w : Extensions L v) (x : v.Completion) :
    letI := extAlgebra v w
    ‖algebraMap v.Completion w.1.Completion x‖ = ‖x‖ := by
  let := extAlgebra v w
  have := w.2
  rw [AbsoluteValue.Completion.algebraMap_apply v w.1]
  exact (UniformSpace.Completion.isometry_mapRingHom
    (WithAbs.isometry_map v w.1)).norm_map_of_map_zero (map_zero _) x

theorem algebraMap_ext_coe (w : Extensions L v) (a : K) :
    letI := extAlgebra v w
    algebraMap v.Completion w.1.Completion (algebraMap K v.Completion a) =
      ((algebraMap K L a : L) : w.1.Completion) := by
  let := extAlgebra v w
  have := w.2
  rw [← IsScalarTower.algebraMap_apply K v.Completion w.1.Completion]
  rfl

/-- Extension of an isometric ring map `L → M` to the completion `L_w`, compatible with `K̂`. -/
theorem exists_completion_lift (w : Extensions L v) {M : Type} [Field M] [Algebra K M]
    [Algebra v.Completion M] [IsScalarTower K v.Completion M] (W : AbsoluteValue M ℝ)
    (hW : ∀ c : v.Completion, W (algebraMap v.Completion M c) = ‖c‖) [CompleteSpace (WithAbs W)]
    (φ : L →ₐ[K] M) (hφ : ∀ a, W (φ a) = w.1 a) :
    letI := extAlgebra v w
    ∃ J : w.1.Completion →+* M, (∀ a : L, J a = φ a) ∧ (∀ x, W (J x) = ‖x‖) ∧
      ∀ c, J (algebraMap v.Completion w.1.Completion c) = algebraMap v.Completion M c := by
  let := extAlgebra v w
  have := w.2
  let ψ : WithAbs w.1 →+* WithAbs W := WithAbs.map w.1 W φ.toRingHom
  have hψ : Isometry ψ := by
    rw [AddMonoidHomClass.isometry_iff_norm]
    intro x
    show W (φ x.ofAbs) = w.1 x.ofAbs
    exact hφ _
  let J0 : w.1.Completion →+* WithAbs W := UniformSpace.Completion.extensionHom ψ hψ.continuous
  have hJ0 : Isometry J0 := hψ.completion_extension
  have hJ0coe : ∀ a : WithAbs w.1, J0 a = ψ a := fun a =>
    UniformSpace.Completion.extensionHom_coe ψ hψ.continuous a
  refine ⟨(WithAbs.equiv W).toRingHom.comp J0, fun a => ?_, fun x => ?_, fun c => ?_⟩
  · exact congrArg WithAbs.ofAbs (hJ0coe (WithAbs.toAbs w.1 a))
  · show ‖J0 x‖ = ‖x‖
    exact hJ0.norm_map_of_map_zero (map_zero _) x
  · let f2 : v.Completion →+* WithAbs W :=
      (WithAbs.equiv W).symm.toRingHom.comp (algebraMap v.Completion M)
    have hf2 : Isometry f2 := by
      rw [AddMonoidHomClass.isometry_iff_norm]
      intro x
      exact hW x
    have hf1 : Isometry (J0.comp (algebraMap v.Completion w.1.Completion)) := by
      refine hJ0.comp ?_
      rw [AddMonoidHomClass.isometry_iff_norm]
      exact norm_algebraMap_ext v w
    have key : (J0.comp (algebraMap v.Completion w.1.Completion) : v.Completion → WithAbs W) = f2 := by
      refine UniformSpace.Completion.ext hf1.continuous hf2.continuous fun k => ?_
      show J0 (algebraMap v.Completion w.1.Completion (k : v.Completion)) = _
      have e1 : (k : v.Completion) = algebraMap K v.Completion k.ofAbs := rfl
      have e2 : algebraMap v.Completion w.1.Completion (algebraMap K v.Completion k.ofAbs) =
          ((WithAbs.toAbs w.1 (algebraMap K L k.ofAbs) : WithAbs w.1) : w.1.Completion) :=
        algebraMap_ext_coe v w k.ofAbs
      rw [e1, e2, hJ0coe]
      show WithAbs.toAbs W (φ (algebraMap K L k.ofAbs)) = WithAbs.toAbs W (algebraMap v.Completion M
        (algebraMap K v.Completion k.ofAbs))
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K v.Completion M]
    have := congrFun key c
    exact congrArg WithAbs.ofAbs this

end Basic

end Prop81

/-- **Existence of the extension** of the absolute value of a complete field to a finite extension
(Milne, Theorem 7.38), now unconditional by Ostrowski's theorem (`remark_7_49a`). -/
@[kb "milne2020ant" "v3.08, Thm. 7.38, p. 123"]
theorem exists_absoluteValue_extension {E F : Type} [NormedField E] [CompleteSpace E] [Field F]
    [Algebra E F] [FiniteDimensional E F] :
    ∃ w : AbsoluteValue F ℝ, ∀ c : E, w (algebraMap E F c) = ‖c‖ :=
  exists_absoluteValue_extension_of_remark_7_49a remark_7_49a

instance instFactIrredFactor {E : Type*} [Field E] {f : E[X]} (g : MonicIrredFactors E f) :
    Fact (Irreducible g.1) := ⟨g.2.2.1⟩

instance instFiniteDimensionalFactor {E : Type*} [Field E] {f : E[X]} (g : MonicIrredFactors E f) :
    FiniteDimensional E (AdjoinRoot g.1) :=
  (AdjoinRoot.powerBasis g.2.1.ne_zero).finite

namespace Prop81

section Corr

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (v : AbsoluteValue K ℝ) {α : L}

/-- The monic irreducible factors of the minimal polynomial of `α` over the completion `K̂`. -/
abbrev Fac (v : AbsoluteValue K ℝ) (α : L) :=
  MonicIrredFactors v.Completion ((minpoly K α).map (algebraMap K v.Completion))

/-- The chosen extension of the norm of `K̂` to `K̂[X]/(g)`. -/
def absOfFactor (g : Fac v α) : AbsoluteValue (AdjoinRoot g.1) ℝ :=
  Classical.choose (exists_absoluteValue_extension (E := v.Completion) (F := AdjoinRoot g.1))

omit [FiniteDimensional K L] in
theorem absOfFactor_spec (g : Fac v α) (c : v.Completion) :
    absOfFactor v g (algebraMap v.Completion (AdjoinRoot g.1) c) = ‖c‖ :=
  Classical.choose_spec
    (exists_absoluteValue_extension (E := v.Completion) (F := AdjoinRoot g.1)) c

/-- Step 1 (Psi): the extension of `v` to `L` attached to a factor `g`. -/
def psi (hα : IntermediateField.adjoin K {α} = ⊤) (g : Fac v α) : Extensions L v :=
  ⟨(absOfFactor v g).comp (toAdjoinRoot v.Completion hα g).toRingHom.injective, by
    refine ⟨?_⟩
    ext c
    show absOfFactor v g (toAdjoinRoot v.Completion hα g (algebraMap K L c)) = v c
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K v.Completion (AdjoinRoot g.1),
      absOfFactor_spec, norm_algebraMap_completion]⟩

theorem psi_apply (hα : IntermediateField.adjoin K {α} = ⊤) (g : Fac v α) (a : L) :
    (psi v hα g).1 a = absOfFactor v g (toAdjoinRoot v.Completion hα g a) := rfl

/-- The canonical `K`-algebra map from `L` to its completion `L_w`. -/
def coeAlgHom (w : AbsoluteValue L ℝ) : L →ₐ[K] w.Completion where
  toFun a := (a : w.Completion)
  map_one' := rfl
  map_mul' a b := UniformSpace.Completion.coe_mul (WithAbs.toAbs w a) (WithAbs.toAbs w b)
  map_zero' := rfl
  map_add' a b := UniformSpace.Completion.coe_add (WithAbs.toAbs w a) (WithAbs.toAbs w b)
  commutes' _ := rfl

omit [FiniteDimensional K L] in
theorem coeAlgHom_apply (w : AbsoluteValue L ℝ) (a : L) : coeAlgHom (K := K) w a = (a : w.Completion) :=
  rfl

theorem isIntegral_coe (w : Extensions L v) (a : L) :
    letI := extAlgebra v w
    IsIntegral v.Completion (a : w.1.Completion) := by
  let := extAlgebra v w
  have := w.2
  have h1 : IsIntegral K (a : w.1.Completion) :=
    (Algebra.IsIntegral.isIntegral a).map (coeAlgHom (K := K) w.1)
  exact h1.tower_top

/-- Step 2 (Phi): the factor attached to an extension `w`. -/
def phi (w : Extensions L v) (α : L) : Fac v α :=
  letI := extAlgebra v w
  haveI := w.2
  ⟨minpoly v.Completion (α : w.1.Completion), minpoly.monic (isIntegral_coe v w α),
    minpoly.irreducible (isIntegral_coe v w α),
    minpoly.dvd v.Completion _ (by
      rw [Polynomial.aeval_map_algebraMap]
      have := Polynomial.aeval_algHom_apply (coeAlgHom (K := K) w.1) α (minpoly K α)
      rw [coeAlgHom_apply] at this
      rw [this, minpoly.aeval, map_zero])⟩

theorem phi_val (w : Extensions L v) (α : L) :
    letI := extAlgebra v w
    (phi v w α).1 = minpoly v.Completion (α : w.1.Completion) := rfl

/-- Step 3: the `K̂`-algebra map `K̂[X]/(Phi w) → L_w` sending the root to `α`. -/
def hMap (w : Extensions L v) (α : L) :
    letI := extAlgebra v w
    AdjoinRoot (phi v w α).1 →ₐ[v.Completion] w.1.Completion :=
  letI := extAlgebra v w
  AdjoinRoot.liftAlgHom (phi v w α).1 (Algebra.ofId v.Completion _) (α : w.1.Completion)
    (minpoly.aeval v.Completion (α : w.1.Completion))

theorem hMap_root (w : Extensions L v) (α : L) :
    letI := extAlgebra v w
    hMap v w α (AdjoinRoot.root (phi v w α).1) = (α : w.1.Completion) := by
  let := extAlgebra v w
  exact AdjoinRoot.lift_root (minpoly.aeval v.Completion (α : w.1.Completion))

theorem hMap_toAdjoinRoot (hα : IntermediateField.adjoin K {α} = ⊤) (w : Extensions L v) (a : L) :
    letI := extAlgebra v w
    hMap v w α (toAdjoinRoot v.Completion hα (phi v w α) a) = (a : w.1.Completion) := by
  let := extAlgebra v w
  have := w.2
  have key : ((hMap v w α).restrictScalars K).comp (toAdjoinRoot v.Completion hα (phi v w α)) =
      coeAlgHom (K := K) w.1 := by
    refine PowerBasis.algHom_ext (powerBasisOfAdjoinEqTop hα) ?_
    rw [show (powerBasisOfAdjoinEqTop hα).gen = α from PowerBasis.ofAdjoinSimpleEqTop_gen _ hα]
    show hMap v w α (toAdjoinRoot v.Completion hα (phi v w α) α) = _
    rw [toAdjoinRoot_self, hMap_root]
    rfl
  exact congrArg (fun f => f a) key

/-- The absolute value `x ↦ ‖h x‖` on `K̂[X]/(Phi w)`. -/
def absOfMap (w : Extensions L v) (α : L) : AbsoluteValue (AdjoinRoot (phi v w α).1) ℝ :=
  letI := extAlgebra v w
  (NormedField.toAbsoluteValue w.1.Completion).comp (hMap v w α).toRingHom.injective

theorem absOfMap_apply (w : Extensions L v) (α : L) (x : AdjoinRoot (phi v w α).1) :
    letI := extAlgebra v w
    absOfMap v w α x = ‖hMap v w α x‖ := rfl

theorem absOfMap_spec (w : Extensions L v) (α : L) (c : v.Completion) :
    absOfMap v w α (algebraMap v.Completion (AdjoinRoot (phi v w α).1) c) = ‖c‖ := by
  let := extAlgebra v w
  rw [absOfMap_apply, AlgHom.commutes]
  exact norm_algebraMap_ext v w c

/-- Step 3: `Psi (Phi w) = w`. -/
theorem psi_phi (hα : IntermediateField.adjoin K {α} = ⊤) (w : Extensions L v) :
    psi v hα (phi v w α) = w := by
  let := extAlgebra v w
  refine Subtype.ext (AbsoluteValue.ext fun a => ?_)
  rw [psi_apply, absoluteValue_eq_of_complete (absOfFactor v (phi v w α)) (absOfMap v w α)
    (absOfFactor_spec v _) (absOfMap_spec v w α), absOfMap_apply, hMap_toAdjoinRoot v hα w a,
    norm_coe_completion]

/-- Step 4: `Phi (Psi g) = g`. -/
theorem phi_psi (hα : IntermediateField.adjoin K {α} = ⊤) (g : Fac v α) :
    phi v (psi v hα g) α = g := by
  let w := psi v hα g
  let := extAlgebra v w
  have := w.2
  have : CompleteSpace (WithAbs (absOfFactor v g)) :=
    completeSpace_withAbs_of_complete _ (absOfFactor_spec v g)
  obtain ⟨J, hJ1, -, hJ3⟩ := exists_completion_lift v w (M := AdjoinRoot g.1) (absOfFactor v g)
    (absOfFactor_spec v g) (toAdjoinRoot v.Completion hα g) (fun a => rfl)
  let J' : w.1.Completion →ₐ[v.Completion] AdjoinRoot g.1 :=
    { J with commutes' := hJ3 }
  apply Subtype.ext
  show minpoly v.Completion ((α : L) : w.1.Completion) = g.1
  rw [← minpoly.algHom_eq J' J'.toRingHom.injective]
  have : J' ((α : L) : w.1.Completion) = AdjoinRoot.root g.1 := by
    show J _ = _
    rw [hJ1, toAdjoinRoot_self]
  rw [this, AdjoinRoot.minpoly_root g.2.1.ne_zero, g.2.1.leadingCoeff]
  simp

/-- The correspondence of Proposition 8.1 as an equivalence. -/
def corrEquiv (hα : IntermediateField.adjoin K {α} = ⊤) : Extensions L v ≃ Fac v α where
  toFun w := phi v w α
  invFun g := psi v hα g
  left_inv w := psi_phi v hα w
  right_inv g := phi_psi v hα g

/-- Step 6 (key): the map `K̂[X]/(Phi w) → L_w` is bijective. -/
theorem hMap_bijective (hα : IntermediateField.adjoin K {α} = ⊤) (w : Extensions L v) :
    Function.Bijective (hMap v w α) := by
  let := extAlgebra v w
  have := w.2
  refine ⟨(hMap v w α).toRingHom.injective, ?_⟩
  have : CompleteSpace (WithAbs (absOfMap v w α)) :=
    completeSpace_withAbs_of_complete _ (absOfMap_spec v w α)
  obtain ⟨J, hJ1, hJ2, -⟩ := exists_completion_lift v w (M := AdjoinRoot (phi v w α).1)
    (absOfMap v w α) (absOfMap_spec v w α) (toAdjoinRoot v.Completion hα (phi v w α))
    (fun a => by rw [absOfMap_apply, hMap_toAdjoinRoot v hα w a, norm_coe_completion])
  let H : w.1.Completion →+* w.1.Completion := (hMap v w α).toRingHom.comp J
  have hH : Isometry H := by
    rw [AddMonoidHomClass.isometry_iff_norm]
    intro x
    show ‖hMap v w α (J x)‖ = ‖x‖
    rw [← absOfMap_apply]
    exact hJ2 x
  have key : (H : w.1.Completion → w.1.Completion) = id := by
    refine UniformSpace.Completion.ext hH.continuous continuous_id fun a => ?_
    show hMap v w α (J (a : w.1.Completion)) = (a : w.1.Completion)
    exact (congrArg (hMap v w α) (hJ1 a.ofAbs)).trans (hMap_toAdjoinRoot v hα w a.ofAbs)
  intro y
  exact ⟨J y, congrFun key y⟩

end Corr

end Prop81

section Main

open Prop81

/-- **Proposition 8.1** (Milne, p. 136). -/
@[kb "milne2020ant" "v3.08, Prop. 8.1, p. 136"]
theorem prop_8_1 : Prop8_1 := by
  refine ⟨fun K L _ _ _ _ _ v _ α hα => ⟨corrEquiv v hα, fun w => rfl⟩⟩

/-- **Proposition 8.2** (Milne, p. 136). -/
@[kb "milne2020ant" "v3.08, Prop. 8.2, p. 136"]
theorem prop_8_2 : Prop8_2 := by
  refine ⟨fun K L _ _ _ _ _ v _ => ?_, fun K L _ _ _ _ _ v _ => ?_⟩
  · obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
    exact Finite.of_equiv _ (corrEquiv v hα).symm
  · obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
    obtain ⟨e0, he0⟩ := exists_tensor_algEquiv_pi v.Completion hα
    let := fun w : Extensions L v => extAlgebra v w
    let e1 : (w : Extensions L v) → AdjoinRoot (phi v w α).1 ≃ₐ[v.Completion] w.1.Completion :=
      fun w => AlgEquiv.ofBijective (hMap v w α) (hMap_bijective v hα w)
    refine ⟨e0.trans ((AlgEquiv.piCongrLeft v.Completion (fun g : Fac v α => AdjoinRoot g.1)
      (corrEquiv v hα)).symm.trans (AlgEquiv.piCongrRight e1)), fun b a w => ?_⟩
    show hMap v w α (e0 (b ⊗ₜ a) (phi v w α)) = _
    rw [he0, map_mul, AlgHom.commutes, hMap_toAdjoinRoot v hα w a]

/-- **Corollary 8.4**, unconditional. -/
@[kb "milne2020ant" "v3.08, Cor. 8.4, p. 136"]
theorem cor_8_4_unconditional (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (v : AbsoluteValue K ℝ) (hv : IsArchOrDiscrete v) (α : L) :
    letI : ∀ w : Extensions L v, Algebra v.Completion w.1.Completion := extAlgebra v
    haveI := prop_8_2.finite K L v hv
    haveI := Fintype.ofFinite (Extensions L v)
    algebraMap K v.Completion (Algebra.norm K α) =
        ∏ w : Extensions L v, Algebra.norm v.Completion (α : w.1.Completion) ∧
      algebraMap K v.Completion (Algebra.trace K L α) =
        ∑ w : Extensions L v, Algebra.trace v.Completion w.1.Completion (α : w.1.Completion) :=
  cor_8_4 prop_8_2 K L v hv α

end Main

end
end NumberFieldKB.MilneANT
