import NumberFieldKB.MilneCFT.Ch6.RayZeta
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.RayClass.Basic

/-!
# Our moduli and ray class groups versus Tau Ceti's

The Introduction's `Modulus` (a nonzero ideal and a set of real places) and `RayClassGroup m`
($I^{S(\mathfrak m)}/P_\mathfrak m$) against Tau Ceti's `TauCeti.GlobalNumberFields.Modulus` (a nonzero ideal and a
finset of real places) and `RayClassGroup` (`idealsPrimeTo 𝔪 ⧸ ray 𝔪`):

* `toTC m`: the Tau Ceti modulus with the same finite part and the same real places;
* `coprimeIdeals_eq`, `congruenceSubgroup_eq`: the two groups of ideals prime to $\mathfrak m$, and the two groups of
  elements $\equiv 1 \bmod^\times \mathfrak m$, coincide;
* `rayEquiv m : RayClassGroup m ≃* TauCeti.GlobalNumberFields.RayClassGroup (toTC m)`, sending the class of an integral
  ideal to its Tau Ceti class (`rayEquiv_idealRayClass`).
-/

open NumberField IsDedekindDomain

noncomputable section

namespace NumberFieldKB.MilneCFT.RayBridge

open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- The Tau Ceti modulus with the same finite part and the same real places. -/
def toTC (m : Modulus K) : TauCeti.GlobalNumberFields.Modulus K where
  finitePart := m.finite
  finitePart_ne_bot := m.finite_ne_bot
  infinitePart := by
    classical
    exact Finset.univ.filter (fun w : {w : InfinitePlace K // w.IsReal} => w.1 ∈ m.infinite)

theorem toTC_finitePart (m : Modulus K) : (toTC m).finitePart = m.finite := rfl

theorem mem_toTC_infinitePart (m : Modulus K) (w : {w : InfinitePlace K // w.IsReal}) :
    w ∈ (toTC m).infinitePart ↔ w.1 ∈ m.infinite := by
  classical
  simp [toTC]

theorem coprimeIdeals_eq (m : Modulus K) :
    coprimeIdeals m = TauCeti.GlobalNumberFields.idealsPrimeTo (toTC m) := by
  ext I
  rw [TauCeti.NumberFieldArithmetic.mem_idealsAway_iff]
  constructor
  · intro h v hv
    exact h v ((TauCeti.GlobalNumberFields.Modulus.mem_support_iff _ v).mp hv)
  · intro h v hv
    exact h v ((TauCeti.GlobalNumberFields.Modulus.mem_support_iff _ v).mpr hv)

theorem congruenceSubgroup_eq (m : Modulus K) :
    congruenceSubgroup m = TauCeti.GlobalNumberFields.congruenceSubgroup (toTC m) := by
  ext x
  rw [TauCeti.GlobalNumberFields.mem_congruenceSubgroup]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v hv => h2 v hv, fun w hw => ?_⟩
    exact h1 w.1 ((mem_toTC_infinitePart m w).mp hw)
  · rintro ⟨h2, h1⟩
    refine ⟨fun v hv => ?_, fun v hv => h2 v hv⟩
    exact h1 ⟨v, m.isReal_of_mem v hv⟩ ((mem_toTC_infinitePart m _).mpr hv)

/-- The two ideal groups, identified. -/
def idealsEquiv (m : Modulus K) :
    coprimeIdeals m ≃* TauCeti.GlobalNumberFields.idealsPrimeTo (toTC m) :=
  MulEquiv.subgroupCongr (coprimeIdeals_eq m)

theorem map_rayPrincipal (m : Modulus K) :
    ((rayPrincipal m).subgroupOf (coprimeIdeals m)).map (idealsEquiv m).toMonoidHom =
      TauCeti.GlobalNumberFields.ray (toTC m) := by
  ext I
  rw [TauCeti.GlobalNumberFields.mem_ray_iff]
  constructor
  · rintro ⟨J, hJ, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hJ
    obtain ⟨x, hx, hxJ⟩ := hJ
    refine ⟨x, ?_, hxJ⟩
    rw [← TauCeti.GlobalNumberFields.mem_congruenceSubgroup, ← congruenceSubgroup_eq]
    exact hx
  · rintro ⟨x, hx, hxI⟩
    refine ⟨(idealsEquiv m).symm I, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    refine ⟨x, ?_, hxI⟩
    rw [congruenceSubgroup_eq]
    exact hx

/-- **The two ray class groups are isomorphic.** -/
def rayEquiv (m : Modulus K) :
    RayClassGroup m ≃* TauCeti.GlobalNumberFields.RayClassGroup (toTC m) :=
  QuotientGroup.congr _ _ (idealsEquiv m) (map_rayPrincipal m)

theorem rayEquiv_mk (m : Modulus K) (I : coprimeIdeals m) :
    rayEquiv m (QuotientGroup.mk I) =
      TauCeti.GlobalNumberFields.rayClassMk (toTC m) (idealsEquiv m I) := rfl

/-- An integral ideal prime to $\mathfrak m_0$ is prime to the Tau Ceti modulus. -/
theorem mem_integralIdealsPrimeTo (m : Modulus K) {𝔞 : Ideal (𝓞 K)} (h0 : 𝔞 ≠ ⊥)
    (h : 𝔞 ⊔ m.finite = ⊤) : 𝔞 ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo (toTC m) :=
  TauCeti.GlobalNumberFields.Modulus.mem_integralIdealsPrimeTo.mpr
    (TauCeti.GlobalNumberFields.Modulus.isCoprimeTo_iff_sup_eq_top.mpr ⟨h0, h⟩)

theorem rayEquiv_idealRayClass (m : Modulus K) (𝔞 : Ideal (𝓞 K)) (h0 : 𝔞 ≠ ⊥) (h : 𝔞 ⊔ m.finite = ⊤) :
    rayEquiv m (idealRayClass m 𝔞 h0 h) =
      TauCeti.GlobalNumberFields.idealClass (toTC m) ⟨𝔞, mem_integralIdealsPrimeTo m h0 h⟩ := by
  rw [TauCeti.GlobalNumberFields.idealClass_apply]
  rfl

end NumberFieldKB.MilneCFT.RayBridge
