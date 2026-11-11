import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Corestriction
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.GroupCohomology.DimensionShift
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Milne, *Class Field Theory*, Chapter II, Example 1.27 (d)

The map $H^r(G, M) \to H^r(G, M)$ defined by the compatible pair
($\sigma \mapsto g_0\sigma g_0^{-1}$, $m \mapsto g_0^{-1}m$) is the identity. Proof by dimension shifting
(Milne, p. 69): induction on $r$, using the coinduced sequence $0 \to M \to \operatorname{Coind} M \to Q \to 0$,
the naturality of the connecting map under change of group, and surjectivity of the connecting map.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology

variable {G : Type} [Group G]

/-- `conjCompat` is natural in the representation. -/
lemma conjCompat_naturality (g₀ : G) {A B : Rep ℤ G} (φ : A ⟶ B) :
    conjCompat g₀ A ≫ φ = (resFunctor (MulAut.conj g₀).toMonoidHom).map φ ≫ conjCompat g₀ B := by
  apply Rep.hom_ext
  ext m
  change φ.hom (A.ρ g₀⁻¹ m) = B.ρ g₀⁻¹ (φ.hom m)
  exact Rep.hom_comm_apply φ g₀⁻¹ m

/-- **Example 1.27 (d)** (p. 69): for every group $G$, $g_0 \in G$, $G$-module $M$ and $r \ge 0$, the map
$H^r(G, M) \to H^r(G, M)$ defined by the compatible pair ($\sigma \mapsto g_0\sigma g_0^{-1}$,
$m \mapsto g_0^{-1}m$) is the identity. Proved by dimension shifting from the case $r = 0$
(`example_1_27d_zero`), using the coinduced sequence `dimensionShiftUpSES`, naturality of the connecting map under
change of group (`TauCeti.groupCohomology.δ_naturality`), and surjectivity of $\delta$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.27 (d), p. 69"]
theorem example1_27d : Example1_27d := by
  refine ⟨fun G _ g₀ M r => ?_⟩
  induction r generalizing M with
  | zero => exact example_1_27d_zero g₀ M
  | succ r ih =>
    let X : CategoryTheory.ShortComplex (Rep ℤ G) :=
      CategoryTheory.ShortComplex.mk (Rep.coindBotUnit M) (Rep.dimensionShiftUpπ M)
        (Rep.coindBotUnit_comp_dimensionShiftUpπ M)
    have hX : X.ShortExact := by
      simpa only [Rep.dimensionShiftUpSES_def] using Rep.dimensionShiftUpSES_shortExact M
    let Φ : X.map (resFunctor (MulAut.conj g₀).toMonoidHom) ⟶ X :=
      { τ₁ := conjCompat g₀ X.X₁
        τ₂ := conjCompat g₀ X.X₂
        τ₃ := conjCompat g₀ X.X₃
        comm₁₂ := conjCompat_naturality g₀ X.f
        comm₂₃ := conjCompat_naturality g₀ X.g }
    have hnat := TauCeti.groupCohomology.δ_naturality (MulAut.conj g₀).toMonoidHom hX hX Φ r (r + 1) rfl
    have hepi : Epi (δ hX r (r + 1) rfl) :=
      epi_δ_of_isZero hX r (_root_.groupCohomology.isZero_coindBot_succ M.V r)
    have h3 : map (MulAut.conj g₀).toMonoidHom Φ.τ₃ r = 𝟙 _ := ih X.X₃
    rw [h3, Category.id_comp] at hnat
    exact (cancel_epi (δ hX r (r + 1) rfl)).1 (by rw [hnat, Category.comp_id])

end NumberFieldKB.MilneCFT
