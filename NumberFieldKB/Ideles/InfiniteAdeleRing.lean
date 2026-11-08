import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# The infinite adele ring as the mixed space, topologically

$F$ is a number field. Mathlib's infinite adele ring `InfiniteAdeleRing F` $=\prod_{v\mid\infty}F_v$ (a product over the
infinite places, each completion its own type) and its mixed space $\mathbb R^{r_1}\times\mathbb C^{r_2}$
(`mixedEmbedding.mixedSpace F`, the infinite part of QuadFormsKB's `Adeles F`) are related in Mathlib only by the ring
isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace`. This file adds:

* **`InfiniteAdeleRing.homeomorph_mixedSpace`**: a homeomorphism with the same underlying map
  (`InfiniteAdeleRing.coe_homeomorph_mixedSpace`); it is built from the isometries
  $F_v\cong\mathbb R$, $F_v\cong\mathbb C$, so the underlying equivalence is Mathlib's by `rfl`;
* `continuous_ringEquiv_mixedSpace`, `continuous_ringEquiv_mixedSpace_symm`;
* **`InfiniteAdeleRing.norm_eq_norm_ringEquiv_mixedSpace`**: Mathlib's norm on the infinite adele ring,
  $\prod_v\|x_v\|^{m_v}$ ($m_v = 1$ at real, $2$ at complex places), is the norm `mixedEmbedding.norm` of the image in the
  mixed space.
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace

namespace NumberFieldKB.Ideles

noncomputable section

variable (F : Type*) [Field F]

open scoped Classical in
/-- **The infinite adele ring is homeomorphic to the mixed space** $\mathbb R^{r_1}\times\mathbb C^{r_2}$, through the
same map as Mathlib's ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace` (`coe_homeomorph_mixedSpace`). Built
place by place from the isometries $F_v\cong\mathbb R$ ($v$ real) and $F_v\cong\mathbb C$ ($v$ complex). -/
def InfiniteAdeleRing.homeomorph_mixedSpace : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => v.IsReal) fun v => v.Completion).trans
    ((Homeomorph.piCongrRight fun v : {v : InfinitePlace F // v.IsReal} =>
        (Completion.isometryEquivRealOfIsReal v.2).toHomeomorph).prodCongr
      ((Homeomorph.piCongrRight fun v : {v : InfinitePlace F // ¬ v.IsReal} =>
        (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ) (Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex))))

theorem InfiniteAdeleRing.toEquiv_homeomorph_mixedSpace :
    (InfiniteAdeleRing.homeomorph_mixedSpace F).toEquiv =
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv := rfl

@[simp] theorem InfiniteAdeleRing.coe_homeomorph_mixedSpace :
    (InfiniteAdeleRing.homeomorph_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
      NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F := rfl

@[simp] theorem InfiniteAdeleRing.coe_homeomorph_mixedSpace_symm :
    ((InfiniteAdeleRing.homeomorph_mixedSpace F).symm : mixedEmbedding.mixedSpace F → InfiniteAdeleRing F) =
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := rfl

/-- Mathlib's ring isomorphism from the infinite adele ring to the mixed space is continuous. -/
theorem continuous_ringEquiv_mixedSpace :
    Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) :=
  (InfiniteAdeleRing.homeomorph_mixedSpace F).continuous

/-- The inverse of Mathlib's ring isomorphism from the infinite adele ring to the mixed space is continuous. -/
theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm :=
  (InfiniteAdeleRing.homeomorph_mixedSpace F).symm.continuous

/-- The component of `ringEquiv_mixedSpace x` at the infinite place $w$ has the norm of $x_w$. -/
theorem normAtPlace_ringEquiv_mixedSpace (x : InfiniteAdeleRing F) (w : InfinitePlace F) :
    mixedEmbedding.normAtPlace w (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ‖x w‖ := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _
  · rw [mixedEmbedding.normAtPlace_apply_of_isComplex hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

variable {F} [NumberField F]

/-- **Mathlib's norm on the infinite adele ring is the norm of the mixed space**:
$\prod_{v\mid\infty}\|x_v\|^{m_v} = N(x)$ with $N$ = `mixedEmbedding.norm`
($\prod_{\text{real}}|x_w|\prod_{\text{complex}}|x_w|^2$). -/
theorem InfiniteAdeleRing.norm_eq_norm_ringEquiv_mixedSpace (x : InfiniteAdeleRing F) :
    ‖x‖ = mixedEmbedding.norm (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  rw [NumberField.InfiniteAdeleRing.norm_def, mixedEmbedding.norm_apply]
  exact Finset.prod_congr rfl fun w _ => by rw [normAtPlace_ringEquiv_mixedSpace]

end

end NumberFieldKB.Ideles
