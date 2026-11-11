import NumberFieldKB.Ideles.RelativeNorm
import NumberFieldKB.Ideles.Bridge
import NumberFieldKB.MilneCFT.Ch2
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter VII §2: the Galois action on adeles, ideles and idele classes

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

$L/K$ is a finite extension of number fields and $G = \mathrm{Aut}_K(L)$ (`L ≃ₐ[K] L`, Milne's
$\mathrm{Gal}(L/K)$ when $L/K$ is Galois). Milne (p. 203) defines the action of $G$ on $\prod_{w\mid v}L_w$ by
transporting the action of $G$ on the first factor of $L\otimes_KK_v$ through $L\otimes_KK_v\cong\prod_{w\mid v}L_w$,
and endows $\mathbb I_L$ with the action for which the inclusions $\prod_{w\mid v}L_w^\times\to\mathbb I_L$ are
$G$-maps (p. 205). Equivalently, $G$ acts on $\mathbb A_L\cong L\otimes_K\mathbb A_K$ through the first factor; this is
the definition used here, with QuadFormsKB's base change $\Psi : \mathbb A_K^\iota = L\otimes_K\mathbb A_K\cong\mathbb A_L$
(`adeleBaseChange`, for the basis `Module.finBasis K L`):

* `galAdele σ` $=\Psi\circ(\sigma\otimes1)\circ\Psi^{-1}$, a ring automorphism of $\mathbb A_L$ (QuadFormsKB's
  `Adeles L`), characterized by: additive, $\mathbb A_K$-linear ($\sigma(\iota(t)y) = \iota(t)\sigma(y)$,
  `galAdele_adeleMap_mul`) and equal to $\sigma$ on $L$ (`galAdele_diag`). It is continuous (`continuous_galAdele`).
* The resulting actions (`MulSemiringAction`, `MulDistribMulAction`) of $G$ on Mathlib's adele ring
  `AdeleRing (𝓞 L) L`, idele group `IdeleGroup (𝓞 L) L` and idele class group `IdeleClassGroup (𝓞 L) L`; the
  inclusion $\iota : \mathbb I_K\to\mathbb I_L$ (`ideleIncl`) has image fixed by $G$.
* The $G$-modules (Chapter II) `ideleRep K L` $=\mathbb I_L$, `ideleClassRep K L` $= C_L$, `unitRep K L` $= L^\times$
  (Mathlib's `Rep.ofAlgebraAutOnUnits`), as `Rep ℤ (L ≃ₐ[K] L)`.
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding
open QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.Ideles

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ## The action on QuadFormsKB's adeles -/

/-- The matrix of $\sigma$ in the basis `Module.finBasis K L`: $\sigma(b_j) = \sum_iM_{ij}b_i$. -/
def galMatrix (σ : L ≃ₐ[K] L) : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K :=
  LinearMap.toMatrix (Module.finBasis K L) (Module.finBasis K L) σ.toLinearMap

variable {K L}

/-- $\sigma\otimes1$ on $\mathbb A_L = L\otimes_K\mathbb A_K$: in the coordinates $\Psi^{-1}(y)\in\mathbb A_K^\iota$,
multiplication by the matrix of $\sigma$. -/
def galAdeleFun (σ : L ≃ₐ[K] L) (y : Adeles L) : Adeles L :=
  adeleBaseChange (Module.finBasis K L) (fun i => ∑ j, diagRing K (galMatrix K L σ i j) *
    (adeleBaseChange (Module.finBasis K L)).symm y j)

/-- **Closed formula**: $\sigma(\sum_jb_j\iota(a_j)) = \sum_j\sigma(b_j)\iota(a_j)$. -/
theorem galAdeleFun_adeleBaseChange (σ : L ≃ₐ[K] L) (a : AdeleSpace K (Fin (Module.finrank K L))) :
    galAdeleFun σ (adeleBaseChange (Module.finBasis K L) a) =
      ∑ j, diagRing L (σ (Module.finBasis K L j)) * adeleMap K L (a j) := by
  have hcb : ∀ j, σ (Module.finBasis K L j) =
      ∑ i, galMatrix K L σ i j • Module.finBasis K L i := fun j => by
    simp only [galMatrix, LinearMap.toMatrix_apply, AlgEquiv.toLinearMap_apply]
    exact ((Module.finBasis K L).sum_repr (σ (Module.finBasis K L j))).symm
  unfold galAdeleFun
  rw [ContinuousAddEquiv.symm_apply_apply]
  simp only [adeleBaseChange_apply, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hι : ∀ i, adeleMap K L (diagRing K (galMatrix K L σ i j)) =
      diagRing L (algebraMap K L (galMatrix K L σ i j)) := fun i => adeleMap_diag _
  simp only [hι]
  rw [hcb j, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul]
  ring

/-- Closed formula in terms of the coordinates $\Psi^{-1}(y)$. -/
theorem galAdeleFun_eq (σ : L ≃ₐ[K] L) (y : Adeles L) :
    galAdeleFun σ y = ∑ j, diagRing L (σ (Module.finBasis K L j)) *
      adeleMap K L ((adeleBaseChange (Module.finBasis K L)).symm y j) := by
  have := galAdeleFun_adeleBaseChange σ ((adeleBaseChange (Module.finBasis K L)).symm y)
  rwa [ContinuousAddEquiv.apply_symm_apply] at this

variable (K) in
/-- Expansion $y = \sum_jb_j\iota(a_j)$ with $a = \Psi^{-1}(y)$. -/
theorem adele_expand (y : Adeles L) :
    y = ∑ j, diagRing L (Module.finBasis K L j) *
      adeleMap K L ((adeleBaseChange (Module.finBasis K L)).symm y j) := by
  have := adeleBaseChange_apply (Module.finBasis K L) ((adeleBaseChange (Module.finBasis K L)).symm y)
  rwa [ContinuousAddEquiv.apply_symm_apply] at this

/-- $\sigma$ acts on $L\subset\mathbb A_L$ as $\sigma$. -/
theorem galAdeleFun_diag (σ : L ≃ₐ[K] L) (x : L) : galAdeleFun σ (diagRing L x) = diagRing L (σ x) := by
  have hs : (adeleBaseChange (Module.finBasis K L)).symm (diagRing L x) =
      diagVec K (Fin (Module.finrank K L)) ((Module.finBasis K L).equivFun x) := by
    have := adeleBaseChange_diag (Module.finBasis K L) ((Module.finBasis K L).equivFun x)
    rw [LinearEquiv.symm_apply_apply] at this
    rw [diagRing_apply, ← this, ContinuousAddEquiv.symm_apply_apply]
  rw [galAdeleFun_eq, hs]
  have hι : ∀ c : K, adeleMap K L (diagRing K c) = diagRing L (algebraMap K L c) := fun c => adeleMap_diag c
  simp only [diagVec_apply, ← diagRing_apply, hι, ← map_mul, ← map_sum]
  congr 1
  conv_rhs => rw [← (Module.finBasis K L).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, mul_comm]
  rfl

/-- $\sigma$ is $\mathbb A_K$-linear. -/
theorem galAdeleFun_adeleMap_mul (σ : L ≃ₐ[K] L) (t : Adeles K) (y : Adeles L) :
    galAdeleFun σ (adeleMap K L t * y) = adeleMap K L t * galAdeleFun σ y := by
  have h : (adeleBaseChange (Module.finBasis K L)).symm (adeleMap K L t * y) =
      fun i => t * (adeleBaseChange (Module.finBasis K L)).symm y i := by
    have := adeleBaseChange_smul (Module.finBasis K L) t ((adeleBaseChange (Module.finBasis K L)).symm y)
    rw [ContinuousAddEquiv.apply_symm_apply] at this
    rw [← this, ContinuousAddEquiv.symm_apply_apply]
  rw [galAdeleFun_eq, galAdeleFun_eq, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

theorem galAdeleFun_add (σ : L ≃ₐ[K] L) (y z : Adeles L) :
    galAdeleFun σ (y + z) = galAdeleFun σ y + galAdeleFun σ z := by
  simp only [galAdeleFun_eq, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- $\sigma$ commutes with finite sums. -/
theorem galAdeleFun_sum {ι : Type*} (σ : L ≃ₐ[K] L) (s : Finset ι) (f : ι → Adeles L) :
    galAdeleFun σ (∑ i ∈ s, f i) = ∑ i ∈ s, galAdeleFun σ (f i) :=
  map_sum (AddMonoidHom.mk' (galAdeleFun σ) (galAdeleFun_add σ)) f s

/-- $\sigma(d\,\iota(a)) = \sigma(d)\,\iota(a)$ for $d\in L$, $a\in\mathbb A_K$. -/
theorem galAdeleFun_diag_mul_adeleMap (σ : L ≃ₐ[K] L) (d : L) (a : Adeles K) :
    galAdeleFun σ (diagRing L d * adeleMap K L a) = diagRing L (σ d) * adeleMap K L a := by
  rw [mul_comm, galAdeleFun_adeleMap_mul, galAdeleFun_diag, mul_comm]

/-- $\sigma(c\,z) = \sigma(c)\,\sigma(z)$ for $c\in L$. -/
theorem galAdeleFun_diag_mul (σ : L ≃ₐ[K] L) (c : L) (z : Adeles L) :
    galAdeleFun σ (diagRing L c * z) = diagRing L (σ c) * galAdeleFun σ z := by
  conv_lhs => rw [adele_expand K z]
  rw [Finset.mul_sum, galAdeleFun_sum, galAdeleFun_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← map_mul, galAdeleFun_diag_mul_adeleMap, map_mul, map_mul]
  ring

theorem galAdeleFun_mul (σ : L ≃ₐ[K] L) (y z : Adeles L) :
    galAdeleFun σ (y * z) = galAdeleFun σ y * galAdeleFun σ z := by
  conv_lhs => rw [adele_expand K y]
  rw [Finset.sum_mul, galAdeleFun_sum, galAdeleFun_eq σ y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, mul_left_comm, galAdeleFun_adeleMap_mul, galAdeleFun_diag_mul]
  ring

theorem galAdeleFun_one_apply (y : Adeles L) : galAdeleFun (1 : L ≃ₐ[K] L) y = y := by
  rw [galAdeleFun_eq]
  simp only [AlgEquiv.one_apply]
  exact (adele_expand K y).symm

theorem galAdeleFun_mul_apply (σ τ : L ≃ₐ[K] L) (y : Adeles L) :
    galAdeleFun (σ * τ) y = galAdeleFun σ (galAdeleFun τ y) := by
  rw [galAdeleFun_eq τ y, galAdeleFun_sum, galAdeleFun_eq (σ * τ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [galAdeleFun_diag_mul_adeleMap]
  rfl

theorem continuous_galAdeleFun (σ : L ≃ₐ[K] L) : Continuous (galAdeleFun σ) :=
  (adeleBaseChange (Module.finBasis K L)).continuous.comp
    (continuous_pi fun _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp
        (adeleBaseChange (Module.finBasis K L)).symm.continuous))

/-- $\sigma(\iota(t)) = \iota(t)$. -/
theorem galAdeleFun_adeleMap (σ : L ≃ₐ[K] L) (t : Adeles K) :
    galAdeleFun σ (adeleMap K L t) = adeleMap K L t := by
  have h1 : galAdeleFun σ 1 = 1 := by
    have := galAdeleFun_diag σ 1
    simpa using this
  have := galAdeleFun_adeleMap_mul σ t 1
  simpa [h1] using this

/-- **The action of $\sigma\in G$ on $\mathbb A_L$** (Milne, *CFT*, Chapter VII, §2, p. 203): a ring automorphism. -/
@[kb "milne2020cft" "Ch. VII, §2, p. 203 (the action of G on the completions of L, via L ⊗_K K_v)"]
def galAdele (σ : L ≃ₐ[K] L) : Adeles L ≃+* Adeles L where
  toFun := galAdeleFun σ
  invFun := galAdeleFun σ⁻¹
  left_inv y := by rw [← galAdeleFun_mul_apply, inv_mul_cancel, galAdeleFun_one_apply]
  right_inv y := by rw [← galAdeleFun_mul_apply, mul_inv_cancel, galAdeleFun_one_apply]
  map_mul' := galAdeleFun_mul σ
  map_add' := galAdeleFun_add σ

instance : MulSemiringAction (L ≃ₐ[K] L) (Adeles L) where
  smul σ y := galAdele σ y
  one_smul := galAdeleFun_one_apply
  mul_smul := galAdeleFun_mul_apply
  smul_zero σ := map_zero (galAdele σ)
  smul_add σ := map_add (galAdele σ)
  smul_one σ := map_one (galAdele σ)
  smul_mul σ := map_mul (galAdele σ)

/-! ## Mathlib's adeles, ideles and idele classes -/

/-- The action on Mathlib's adele ring, transported along `adeleRingEquiv`. -/
instance instMulSemiringActionAdeleRing : MulSemiringAction (L ≃ₐ[K] L) (AdeleRing (𝓞 L) L) where
  smul σ y := (adeleRingEquiv L).symm (σ • adeleRingEquiv L y)
  one_smul y := by
    show (adeleRingEquiv L).symm ((1 : L ≃ₐ[K] L) • adeleRingEquiv L y) = y
    rw [one_smul, RingEquiv.symm_apply_apply]
  mul_smul σ τ y := by
    show (adeleRingEquiv L).symm ((σ * τ) • adeleRingEquiv L y) =
      (adeleRingEquiv L).symm (σ • adeleRingEquiv L ((adeleRingEquiv L).symm (τ • adeleRingEquiv L y)))
    rw [mul_smul, RingEquiv.apply_symm_apply]
  smul_zero σ := by
    show (adeleRingEquiv L).symm (σ • adeleRingEquiv L 0) = 0
    rw [map_zero, smul_zero, map_zero]
  smul_add σ y z := by
    show (adeleRingEquiv L).symm (σ • adeleRingEquiv L (y + z)) =
      (adeleRingEquiv L).symm (σ • adeleRingEquiv L y) + (adeleRingEquiv L).symm (σ • adeleRingEquiv L z)
    rw [map_add, smul_add, map_add]
  smul_one σ := by
    show (adeleRingEquiv L).symm (σ • adeleRingEquiv L 1) = 1
    rw [map_one, smul_one, map_one]
  smul_mul σ y z := by
    show (adeleRingEquiv L).symm (σ • adeleRingEquiv L (y * z)) =
      (adeleRingEquiv L).symm (σ • adeleRingEquiv L y) * (adeleRingEquiv L).symm (σ • adeleRingEquiv L z)
    rw [map_mul, smul_mul', map_mul]

/-- The action commutes with `adeleRingEquiv`. -/
theorem adeleRingEquiv_smul (σ : L ≃ₐ[K] L) (y : AdeleRing (𝓞 L) L) :
    adeleRingEquiv L (σ • y) = σ • adeleRingEquiv L y :=
  RingEquiv.apply_symm_apply (adeleRingEquiv L) _

/-- The action on the ideles `IdeleGroup (𝓞 L) L` $=\mathbb A_L^\times$. -/
instance instMulDistribMulActionIdeleGroup : MulDistribMulAction (L ≃ₐ[K] L) (IdeleGroup (𝓞 L) L) where
  smul σ x := Units.map (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (AdeleRing (𝓞 L) L) σ).toMonoidHom x
  one_smul x := Units.ext (one_smul (L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L))
  mul_smul σ τ x := Units.ext (mul_smul σ τ (x : AdeleRing (𝓞 L) L))
  smul_mul σ x y := Units.ext (smul_mul' σ (x : AdeleRing (𝓞 L) L) (y : AdeleRing (𝓞 L) L))
  smul_one σ := Units.ext (smul_one σ)

theorem val_smul_idele (σ : L ≃ₐ[K] L) (x : IdeleGroup (𝓞 L) L) :
    ((σ • x : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L) = σ • (x : AdeleRing (𝓞 L) L) :=
  rfl

/-- $\sigma$ maps the principal idele of $\xi\in L^\times$ to that of $\sigma(\xi)$. -/
theorem smul_unitEmbedding (σ : L ≃ₐ[K] L) (ξ : Lˣ) :
    σ • IdeleGroup.unitEmbedding (𝓞 L) L ξ = IdeleGroup.unitEmbedding (𝓞 L) L (Units.map σ ξ) := by
  refine Units.ext ((adeleRingEquiv L).injective ?_)
  change adeleRingEquiv L (σ • algebraMap L (AdeleRing (𝓞 L) L) (ξ : L)) =
    adeleRingEquiv L (algebraMap L (AdeleRing (𝓞 L) L) (σ (ξ : L)))
  rw [adeleRingEquiv_smul, adeleRingEquiv_algebraMap, adeleRingEquiv_algebraMap]
  exact galAdeleFun_diag σ _

theorem continuous_smul_idele (σ : L ≃ₐ[K] L) : Continuous fun x : IdeleGroup (𝓞 L) L => σ • x := by
  have hc : Continuous fun y : AdeleRing (𝓞 L) L => σ • y :=
    (continuous_adeleRingEquiv_symm L).comp ((continuous_galAdeleFun σ).comp (continuous_adeleRingEquiv L))
  exact Units.continuous_iff.mpr ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩

/-- The principal ideles are stable under $G$. -/
theorem principalSubgroup_le_comap (σ : L ≃ₐ[K] L) :
    IdeleGroup.principalSubgroup (𝓞 L) L ≤
      (IdeleGroup.principalSubgroup (𝓞 L) L).comap
        (MulDistribMulAction.toMonoidHom (IdeleGroup (𝓞 L) L) σ) := by
  intro x hx
  obtain ⟨ξ, rfl⟩ := hx
  rw [Subgroup.mem_comap, MulDistribMulAction.toMonoidHom_apply, smul_unitEmbedding]
  exact ⟨_, rfl⟩

/-- The action on the idele class group $C_L = \mathbb I_L/L^\times$ (the principal ideles are stable). -/
instance instMulDistribMulActionIdeleClassGroup :
    MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup (𝓞 L) L) where
  smul σ x := QuotientGroup.map _ _ (MulDistribMulAction.toMonoidHom (IdeleGroup (𝓞 L) L) σ)
    (principalSubgroup_le_comap σ) x
  one_smul x := QuotientGroup.induction_on x fun x =>
    congrArg QuotientGroup.mk (one_smul (L ≃ₐ[K] L) x)
  mul_smul σ τ x := QuotientGroup.induction_on x fun x =>
    congrArg QuotientGroup.mk (mul_smul σ τ x)
  smul_mul σ x y := QuotientGroup.induction_on x fun x => QuotientGroup.induction_on y fun y =>
    congrArg QuotientGroup.mk (smul_mul' σ x y)
  smul_one σ := congrArg QuotientGroup.mk (smul_one σ)

theorem smul_mk (σ : L ≃ₐ[K] L) (x : IdeleGroup (𝓞 L) L) :
    σ • (QuotientGroup.mk x : IdeleClassGroup (𝓞 L) L) = QuotientGroup.mk (σ • x) :=
  rfl

variable (K L) in
/-- The inclusion $\mathbb I_K\hookrightarrow\mathbb I_L$ induced by QuadFormsKB's `adeleMap K L`. -/
def ideleIncl : IdeleGroup (𝓞 K) K →* IdeleGroup (𝓞 L) L :=
  ((ideleGroupEquiv L).symm.toMulEquiv.toMonoidHom.comp (Units.map (adeleMap K L).toMonoidHom)).comp
    (ideleGroupEquiv K).toMulEquiv.toMonoidHom

/-- The image of $\mathbb I_K$ is fixed by $G$. -/
theorem smul_ideleIncl (σ : L ≃ₐ[K] L) (x : IdeleGroup (𝓞 K) K) : σ • ideleIncl K L x = ideleIncl K L x := by
  refine Units.ext ((adeleRingEquiv L).injective ?_)
  change adeleRingEquiv L (σ • (adeleRingEquiv L).symm (adeleMap K L (adeleRingEquiv K x))) =
    adeleRingEquiv L ((adeleRingEquiv L).symm (adeleMap K L (adeleRingEquiv K x)))
  rw [adeleRingEquiv_smul, RingEquiv.apply_symm_apply]
  exact galAdeleFun_adeleMap σ _

/-! ## The $G$-modules -/

variable (K L) in
/-- $\mathbb I_L$ as a $G$-module (Milne, *CFT*, Chapter VII, §2, p. 205). -/
@[kb "milne2020cft" "Ch. VII, §2, p. 205 (the G-module I_L)"]
abbrev ideleRep : Rep ℤ (L ≃ₐ[K] L) := Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleGroup (𝓞 L) L)

variable (K L) in
/-- $C_L = \mathbb I_L/L^\times$ as a $G$-module (Milne, *CFT*, Chapter VII, §1, p. 201). -/
@[kb "milne2020cft" "Ch. VII, §1, p. 201 (the G-module C_L)"]
abbrev ideleClassRep : Rep ℤ (L ≃ₐ[K] L) := Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup (𝓞 L) L)

variable (K L) in
/-- $L^\times$ as a $G$-module (Mathlib's `Rep.ofAlgebraAutOnUnits`). -/
abbrev unitRep : Rep ℤ (L ≃ₐ[K] L) := Rep.ofAlgebraAutOnUnits K L

end NumberFieldKB.MilneCFT.Ch7
