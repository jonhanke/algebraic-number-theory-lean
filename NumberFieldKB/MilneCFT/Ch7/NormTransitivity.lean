import NumberFieldKB.MilneCFT.Ch7.Lemma45Aux

/-!
# Transitivity of the idele norm in arbitrary towers

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII,
§9 (Lemma 9.4 uses $\mathrm{Nm}_{K'/K}\circ\mathrm{Nm}_{L/K'} = \mathrm{Nm}_{L/K}$ on idele class groups for a tower
$K\subseteq K'\subseteq L$ with $K'/K$ not necessarily Galois); Neukirch, *Algebraic Number Theory*, Ch. VI, (2.5)
[unverified locator].

The library's idele norm `ideleNorm K L` is the determinant of multiplication on $\mathbb A_L\cong\mathbb A_K^n$
(base change along a $K$-basis of $L$). Earlier the tower law was proved only for Galois towers
(`Lemma45Aux.ideleNorm_comp`, through $\mathrm{Nm} = \prod_\sigma\sigma$). Here it is proved for every tower:

* `adeleAlgebra`: $\mathbb A_L$ is an $\mathbb A_K$-algebra through the natural map $\iota:\mathbb A_K\to\mathbb A_L$;
  `adeleBasis b`: the base change isomorphism $\Psi:\mathbb A_K^\iota\cong\mathbb A_L$ is $\mathbb A_K$-linear, so it
  is a basis of $\mathbb A_L$ over $\mathbb A_K$.
* `adeleLmat_eq_leftMulMatrix`, `adeleDet_eq_algebraNorm`, `coe_adeleNorm`: the matrix of multiplication is Mathlib's
  `Algebra.leftMulMatrix`, and the adelic norm is Mathlib's `Algebra.norm` $\mathbb A_L\to\mathbb A_K$ (in particular
  it does not depend on the basis).
* **`ideleNorm_comp`**, **`ideleClassNorm_comp`**: $\mathrm{Nm}_{K'/K}\circ\mathrm{Nm}_{L/K'} = \mathrm{Nm}_{L/K}$ on
  ideles and on idele classes, from Mathlib's general tower law `Algebra.norm_norm` for free algebras.
* `normClasses_comp`: $\mathrm{Nm}_{K'/K}(\mathrm{Nm}_{L/K'}C_L) = \mathrm{Nm}_{L/K}C_L$.
-/

open IsDedekindDomain NumberField
open QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.Ideles

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

namespace NormTransitivity

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- $\mathbb A_K$ as an $\mathbb A_k$-algebra through the natural map $\iota:\mathbb A_k\to\mathbb A_K$ (a local
instance of this file). -/
abbrev adeleAlgebra : Algebra (Adeles k) (Adeles K) := (adeleMap k K).toAlgebra

attribute [local instance] adeleAlgebra

theorem adeleAlgebra_algebraMap (t : Adeles k) : algebraMap (Adeles k) (Adeles K) t = adeleMap k K t := rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k K)

/-- The base change isomorphism $\Psi : \mathbb A_k^\iota\to\mathbb A_K$ as an $\mathbb A_k$-linear equivalence. -/
def adeleBaseChangeLin : (ι → Adeles k) ≃ₗ[Adeles k] Adeles K where
  toFun a := adeleBaseChange b a
  invFun y := (adeleBaseChange b).symm y
  map_add' a a' := map_add (adeleBaseChange b) a a'
  map_smul' t a := by
    change adeleBaseChange b (fun i => t * a i) = adeleMap k K t * adeleBaseChange b a
    exact adeleBaseChange_smul b t a
  left_inv a := (adeleBaseChange b).symm_apply_apply a
  right_inv y := (adeleBaseChange b).apply_symm_apply y

/-- The basis $(\Psi(e_i))_i = (b_i)_i$ of $\mathbb A_K$ over $\mathbb A_k$. -/
def adeleBasis : Module.Basis ι (Adeles k) (Adeles K) :=
  Module.Basis.ofEquivFun (adeleBaseChangeLin b).symm

omit [DecidableEq ι] in
theorem adeleBasis_repr (y : Adeles K) (i : ι) :
    (adeleBasis b).repr y i = (adeleBaseChange b).symm y i := by
  simp [adeleBasis, adeleBaseChangeLin]

theorem adeleBasis_apply (j : ι) : adeleBasis b j = diagRing K (b j) := by
  rw [adeleBasis, Module.Basis.coe_ofEquivFun]
  change adeleBaseChange b (Pi.single j 1) = _
  exact adeleBaseChange_single b j

/-- The matrix of multiplication by $y$ in the coordinates $b$ is Mathlib's `Algebra.leftMulMatrix` for the basis
`adeleBasis b`. -/
theorem adeleLmat_eq_leftMulMatrix (y : Adeles K) :
    adeleLmat b y = Algebra.leftMulMatrix (adeleBasis b) y := by
  refine Matrix.ext fun i j => ?_
  rw [Algebra.leftMulMatrix_eq_repr_mul, adeleBasis_apply, adeleBasis_repr]
  rfl

/-- **The adelic norm is Mathlib's algebra norm** $\mathbb A_K\to\mathbb A_k$. -/
theorem adeleDet_eq_algebraNorm (y : Adeles K) :
    adeleDet b y = Algebra.norm (Adeles k) y := by
  rw [adeleDet_apply, Algebra.norm_eq_matrix_det (adeleBasis b), adeleLmat_eq_leftMulMatrix]

theorem coe_adeleNorm (y : (Adeles K)ˣ) :
    ((adeleNorm b y : (Adeles k)ˣ) : Adeles k) = Algebra.norm (Adeles k) (y : Adeles K) := by
  rw [← adeleDet_eq_algebraNorm b]
  rfl

instance free_adeles : Module.Free (Adeles k) (Adeles K) :=
  Module.Free.of_basis (adeleBasis (Module.finBasis k K))

end NormTransitivity

open NormTransitivity

attribute [local instance] adeleAlgebra

variable (K K' L : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L] [NumberField L]
  [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]

instance NormTransitivity.isScalarTower_adeles : IsScalarTower (Adeles K) (Adeles K') (Adeles L) :=
  IsScalarTower.of_algebraMap_eq fun t => (Lemma45Aux.adeleMap_comp t).symm

/-- **Transitivity of the idele norm** (Milne, *CFT*, Chapter VII, used in Lemma 9.4): for any tower
$K\subseteq K'\subseteq L$ of number fields (not necessarily Galois),
$\mathrm{Nm}_{K'/K}\circ\mathrm{Nm}_{L/K'} = \mathrm{Nm}_{L/K}$ on $\mathbb I_L$. -/
@[kb "milne2020cft" "Ch. VII, §9 (Nm_{K'/K} ∘ Nm_{L/K'} = Nm_{L/K}, used in Lemma 9.4)"]
theorem ideleNorm_comp (x : IdeleGroup (𝓞 L) L) :
    ideleNorm K K' (ideleNorm K' L x) = ideleNorm K L x := by
  apply (ideleGroupEquiv K).injective
  simp only [ideleNorm, MonoidHom.coe_coe, ContinuousMonoidHom.coe_toMonoidHom]
  rw [ideleGroupEquiv_ideleRelNorm, ideleGroupEquiv_ideleRelNorm, ideleGroupEquiv_ideleRelNorm]
  refine Units.ext ?_
  rw [coe_adeleNorm, coe_adeleNorm, coe_adeleNorm]
  exact Algebra.norm_norm

/-- **Transitivity of the idele class norm**: $\mathrm{Nm}_{K'/K}\circ\mathrm{Nm}_{L/K'} = \mathrm{Nm}_{L/K}$ on
$C_L$. -/
@[kb "milne2020cft" "Ch. VII, §9 (Nm_{K'/K} ∘ Nm_{L/K'} = Nm_{L/K} on idele classes, used in Lemma 9.4)"]
theorem ideleClassNorm_comp (x : IdeleClassGroup (𝓞 L) L) :
    ideleClassNorm K K' (ideleClassNorm K' L x) = ideleClassNorm K L x := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    change ((ideleNorm K K' (ideleNorm K' L y) : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) =
      ((ideleNorm K L y : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K)
    rw [ideleNorm_comp]

/-- $\mathrm{Nm}_{K'/K}(\mathrm{Nm}_{L/K'}C_L) = \mathrm{Nm}_{L/K}C_L$. -/
theorem normClasses_comp :
    (normClasses K' L).map (ideleClassNorm K K') = normClasses K L := by
  rw [normClasses, normClasses, ← MonoidHom.range_comp]
  congr 1
  exact MonoidHom.ext fun x => ideleClassNorm_comp K K' L x

/-- $\mathrm{Nm}_{K'/K}(\mathrm{Nm}_{L/K'}\mathbb I_L) = \mathrm{Nm}_{L/K}\mathbb I_L$. -/
theorem normIdeles_comp :
    (normIdeles K' L).map (ideleNorm K K') = normIdeles K L := by
  rw [normIdeles, normIdeles, ← MonoidHom.range_comp]
  congr 1
  exact MonoidHom.ext fun x => ideleNorm_comp K K' L x

end NumberFieldKB.MilneCFT.Ch7
