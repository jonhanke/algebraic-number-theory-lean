import NumberFieldKB.MilneANT.Ch7Remark753
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Hensel's lemma in the integral closure of a complete DVR in an algebraic separable extension

Source: J. S. Milne, *Algebraic Number Theory*, v3.08, Prop. 7.31 / Thm. 7.38 (finite extensions of complete
fields are complete), and the remark that Hensel's lemma persists for algebraic extensions.

Let $A$ be a complete DVR with fraction field $K$ and $L/K$ a separable algebraic extension, $B$ the integral
closure of $A$ in $L$.

* `isAdicComplete_of_pow`: if $R$ is $I^e$-adically complete ($e>0$) it is $I$-adically complete.
* `isAdicComplete_integralClosure`: for $L/K$ finite separable, $B$ is $\mathfrak m_B$-adically complete
  ($B$ is finite free over $A$, so $\mathfrak m_A B = \mathfrak m_B^e$-adically complete).
* `henselianLocalRing_integralClosure_of_finite`, then `henselianLocalRing_integralClosure` for $L/K$
  algebraic (possibly infinite): a monic $G\in B[X]$ and its approximate root live in a finite subextension.
* `hensel_of_algebraic`: the form for polynomials over $A$.
-/

open IsLocalRing Polynomial

universe u v w

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneANT.HenselExt

theorem smod_iff {R : Type*} [CommRing R] (J : Ideal R) (x y : R) :
    x ≡ y [SMOD (J • ⊤ : Submodule R R)] ↔ x - y ∈ J := by
  rw [SModEq.sub_mem]
  simp [smul_eq_mul]

/-- If `R` is `I^e`-adically complete (`e > 0`) then it is `I`-adically complete. -/
theorem isAdicComplete_of_pow {R : Type*} [CommRing R] (I : Ideal R) {e : ℕ} (he : 0 < e)
    [IsAdicComplete (I ^ e) R] : IsAdicComplete I R := by
  have hle : ∀ n, I ^ (e * n) ≤ I ^ n := fun n =>
    Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n he)
  have : IsHausdorff I R := ⟨fun x hx => by
    refine IsHausdorff.haus (inferInstance : IsHausdorff (I ^ e) R) x fun n => ?_
    rw [smod_iff, sub_zero]
    have := (smod_iff _ _ _).1 (hx (e * n))
    rw [sub_zero] at this
    rw [pow_mul] at this
    exact this⟩
  have : IsPrecomplete I R := ⟨fun f hf => by
    have hf' : ∀ {m n}, m ≤ n → f (e * m) ≡ f (e * n) [SMOD ((I ^ e) ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      rw [smod_iff, ← pow_mul]
      have := (smod_iff _ _ _).1 (hf (Nat.mul_le_mul_left e hmn))
      exact this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I ^ e) (fun n => f (e * n)) hf'
    refine ⟨L, fun n => ?_⟩
    rw [smod_iff]
    have h1 := (smod_iff _ _ _).1 (hL n)
    rw [← pow_mul] at h1
    have h2 := (smod_iff _ _ _).1 (hf (Nat.le_mul_of_pos_left n he))
    have : f n - L = (f n - f (e * n)) + (f (e * n) - L) := by ring
    rw [this]
    exact Ideal.add_mem _ h2 (hle n h1)⟩
  exact ⟨⟩

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

section Finite

variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

include K

/-- For `L/K` finite separable, `B = integralClosure A L` is `𝔪_B`-adically complete. -/
theorem isAdicComplete_integralClosure :
    IsAdicComplete (maximalIdeal (integralClosure A L)) (integralClosure A L) := by
  have hfin : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L (integralClosure A L)
  have := Remark753.isDVR_of_finite A K L
  have := Remark753.torsionFree_integralClosure A K L
  have := isLocalHom_algebraMap_integralClosure A L
  have hfree : Module.Free A (integralClosure A L) := inferInstance
  have hc : IsAdicComplete (maximalIdeal A) (integralClosure A L) :=
    Remark753.isAdicComplete_of_equiv_pi (maximalIdeal A)
      (Module.Free.chooseBasis A (integralClosure A L)).equivFun
  have hc' : IsAdicComplete (Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A))
      (integralClosure A L) :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal A) (integralClosure A L)).mpr hc
  rw [Remark753.map_maximalIdeal_eq_pow (A := A) (B := integralClosure A L)] at hc'
  have hpos : 0 < (maximalIdeal (integralClosure A L)).ramificationIdx A := by
    by_contra h0
    have h0' : (maximalIdeal (integralClosure A L)).ramificationIdx A = 0 := by omega
    have hle : Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A) ≤
        maximalIdeal (integralClosure A L) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal x).1 hx (isUnit_of_map_unit _ _ hu)
    rw [Remark753.map_maximalIdeal_eq_pow (A := A) (B := integralClosure A L), h0', pow_zero] at hle
    exact (Ideal.IsMaximal.ne_top inferInstance) (top_le_iff.1 (by simpa using hle))
  exact isAdicComplete_of_pow _ hpos

/-- Hensel's lemma in `B = integralClosure A L` for `L/K` finite separable (Milne, Prop. 7.31 / Thm. 7.38). -/
theorem henselianLocalRing_integralClosure_of_finite : HenselianLocalRing (integralClosure A L) := by
  have := isAdicComplete_integralClosure A K L
  have H := IsAdicComplete.henselianRing (integralClosure A L) (maximalIdeal (integralClosure A L))
  exact ⟨fun G hG b h1 h2 => H.is_henselian G hG b h1 (h2.map _)⟩

end Finite

section Algebraic

variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L] [Algebra.IsSeparable K L]

include K

/-- **Hensel's lemma for algebraic extensions**: `B = integralClosure A L` is Henselian for `L/K` separable
algebraic (not necessarily finite). A monic `G ∈ B[X]` and `b` lie in the integral closure of a finite subextension. -/
theorem henselianLocalRing_integralClosure : HenselianLocalRing (integralClosure A L) := by
  classical
  have hint : Algebra.IsIntegral K L := inferInstance
  refine ⟨fun G hG b h1 h2 => ?_⟩
  let S : Set L := insert (b : L) ((fun c : integralClosure A L => (c : L)) '' (G.coeffs : Set _))
  have hSfin : S.Finite := Set.Finite.insert _ (Set.Finite.image _ (Finset.finite_toSet _))
  have : Finite S := hSfin.to_subtype
  let F : IntermediateField K L := IntermediateField.adjoin K S
  have : FiniteDimensional K F := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hSF : ∀ x ∈ S, x ∈ F := fun x hx => IntermediateField.subset_adjoin K S hx
  let ι : integralClosure A F →ₐ[A] integralClosure A L := Remark753.mapB A K F L F.val
  have hι : ∀ x, ((ι x : integralClosure A L) : L) = (x : F) := fun x => rfl
  have : IsLocalHom ι := Remark753.mapB_isLocalHom A K F L F.val
  have hιinj : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun z : integralClosure A L => (z : L)) hxy
    exact Subtype.ext_iff.mp (by simpa [hι] using this)
  -- lifting elements of `B` lying in `F`
  have hlift : ∀ x : integralClosure A L, (x : L) ∈ F → ∃ y : integralClosure A F, ι y = x := by
    intro x hx
    have hxi : IsIntegral A (⟨(x : L), hx⟩ : F) := by
      refine (isIntegral_algHom_iff (F.val.restrictScalars A) F.val.injective).1 ?_
      exact x.2
    exact ⟨⟨⟨(x : L), hx⟩, hxi⟩, Subtype.ext rfl⟩
  obtain ⟨bF, hbF⟩ := hlift b (hSF _ (Set.mem_insert _ _))
  have hGlift : G ∈ Polynomial.lifts (ι : integralClosure A F →+* integralClosure A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : G.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · obtain ⟨y, hy⟩ := hlift (G.coeff n)
        (hSF _ (Set.mem_insert_of_mem _ ⟨_, Polynomial.coeff_mem_coeffs hn, rfl⟩))
      exact ⟨y, hy⟩
  obtain ⟨GF, hGF, -, hGFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hGlift hG
  have hev : ∀ (p : (integralClosure A F)[X]) (x : integralClosure A F),
      ι (p.eval x) = (p.map (ι : integralClosure A F →+* integralClosure A L)).eval (ι x) := by
    intro p x
    rw [Polynomial.eval_map]
    exact (Polynomial.eval₂_at_apply (ι : integralClosure A F →+* integralClosure A L) x).symm
  have hH := henselianLocalRing_integralClosure_of_finite A K F
  have e1 : GF.eval bF ∈ maximalIdeal (integralClosure A F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map ι
    rw [hev, hbF, hGF] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 this
  have e2 : IsUnit (GF.derivative.eval bF) := by
    refine isUnit_of_map_unit ι _ ?_
    rw [hev, hbF, ← Polynomial.derivative_map, hGF]
    exact h2
  obtain ⟨a, ha, hab⟩ := hH.is_henselian GF hGFm bF e1 e2
  refine ⟨ι a, ?_, ?_⟩
  · rw [Polynomial.IsRoot] at ha ⊢
    have := hev GF a
    rw [ha, map_zero, hGF] at this
    exact this.symm
  · have : ι a - b = ι (a - bF) := by rw [map_sub, hbF]
    rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hab (isUnit_of_map_unit ι _ hu)

/-- Hensel's lemma for polynomials over `A` with roots in `integralClosure A L`, `L/K` separable algebraic. -/
theorem hensel_of_algebraic (g : A[X]) (hg : g.Monic) (b : integralClosure A L)
    (h1 : aeval b g ∈ maximalIdeal (integralClosure A L))
    (h2 : IsUnit (aeval b (derivative g))) :
    ∃ a : integralClosure A L, aeval a g = 0 ∧ a - b ∈ maximalIdeal (integralClosure A L) := by
  have H := henselianLocalRing_integralClosure A K L
  obtain ⟨a, ha, hab⟩ := H.is_henselian (g.map (algebraMap A (integralClosure A L))) (hg.map _) b
    (by rwa [Polynomial.eval_map_algebraMap])
    (by rwa [Polynomial.derivative_map, Polynomial.eval_map_algebraMap])
  refine ⟨a, ?_, hab⟩
  rwa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at ha

end Algebraic

end NumberFieldKB.MilneANT.HenselExt
