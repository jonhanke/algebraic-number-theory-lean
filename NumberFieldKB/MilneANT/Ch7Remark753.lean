import NumberFieldKB.MilneANT.Ch7Thm758aFixed
import NumberFieldKB.MilneANT.Ch7Hensel

/-!
# Milne, *Algebraic Number Theory*, Remark 7.53: unramified extensions and separable extensions of the residue field

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`,
Remark 7.53, p. 129, and the proof of Proposition 7.50, p. 127.

Setting as in `Ch7Extensions.lean`: $A$ is a complete discrete valuation ring with fraction field $K$ and residue
field $k$ (both perfect), $B$ is the integral closure of $A$ in a finite extension $L$ of $K$, $l = B/\mathfrak p_L$.
The named statement `Remark7_53` has two parts, both proved here.

* **Essential surjectivity** (`Remark753.exists_lift`). A finite separable extension $k'/k$ is the residue field of an
  unramified extension. Choose a primitive element $\bar a$ of $k'$ with minimal polynomial $\bar g$, lift $\bar g$ to
  a monic $g \in A[X]$ of the same degree; $g$ is irreducible over $A$ (its reduction is), hence over $K$ (Gauss), and
  $L = K[X]/(g)$. The residue of the class of $X$ is a root of $\bar g$ in $l$, so $[l:k] \ge \deg g = [L:K]$, while
  $[l:k] = f \le ef = [L:K]$ (Cor. 7.42). Hence $f = n$ and $k' \cong l$ (`Remark753.exists_lift`).
* **Full faithfulness** (`Remark753.hom_equiv`). For unramified $L, L'$ choose $\alpha \in B$ whose residue generates
  $l$ over $k$; then $L = K(\alpha)$ and the minimal polynomial $g$ of $\alpha$ over $A$ reduces to the (separable)
  minimal polynomial $\bar g$ of $\bar\alpha$. $K$-homomorphisms $L \to L'$ correspond to roots of $g$ in $B'$, and
  $k$-homomorphisms $l \to l'$ to roots of $\bar g$ in $l'$. Reduction maps the first set injectively (two roots that
  are congruent modulo $\mathfrak p_{L'}$ contradict separability of $\bar g$) and surjectively (Hensel's lemma in
  $B'$, which is $\mathfrak m_A$-adically complete as a finite free $A$-module and has $\mathfrak m_A B' = \mathfrak p_{L'}$
  since $e = 1$).
-/

open IsLocalRing Polynomial

universe u v w

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneANT

namespace Remark753

/-! ## Completeness of a finite free module over a complete ring -/

theorem isAdicComplete_pi {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {ι : Type*} [Fintype ι] : IsAdicComplete I (ι → R) := by
  classical
  rw [← AdicCompletion.of_bijective_iff]
  have h1 : (AdicCompletion.piEquivOfFintype I (fun _ : ι => R)) ∘ (AdicCompletion.of I (ι → R)) =
      fun x i => AdicCompletion.of I R (x i) := by
    funext x
    rw [Function.comp_apply, AdicCompletion.piEquivOfFintype_apply]
    ext i n
    simp [AdicCompletion.pi]
    rfl
  have h2 : Function.Bijective (fun (x : ι → R) i => AdicCompletion.of I R (x i)) := by
    have := AdicCompletion.of_bijective I R
    exact ⟨fun x y h => funext fun i => this.1 (congrFun h i),
      fun y => ⟨fun i => (this.2 (y i)).choose, funext fun i => (this.2 (y i)).choose_spec⟩⟩
  rw [← h1] at h2
  exact (Function.Bijective.of_comp_iff' (AdicCompletion.piEquivOfFintype I (fun _ : ι => R)).bijective _).mp h2

theorem isAdicComplete_of_equiv_pi {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] (ι → R)) :
    IsAdicComplete I M := by
  have := isAdicComplete_pi I (R := R) (ι := ι)
  classical
  rw [← AdicCompletion.of_bijective_iff]
  have h1 : AdicCompletion.of I M =
      (AdicCompletion.congr I e).symm ∘ (AdicCompletion.of I (ι → R)) ∘ e := by
    funext x
    simp only [Function.comp_apply]
    rw [LinearEquiv.eq_symm_apply, AdicCompletion.congr_apply, AdicCompletion.map_of]
    rfl
  rw [h1]
  exact ((AdicCompletion.congr I e).symm.bijective.comp
    ((AdicCompletion.of_bijective I (ι → R)).comp e.bijective))

/-! ## Hensel's lemma in the integral closure of an unramified extension -/

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

section Infra

variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

include K

theorem isDedekindDomain_of_finite [Module.Finite A (integralClosure A L)] :
    IsDedekindDomain (integralClosure A L) := by
  have : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
  have : Algebra.IsIntegral A (integralClosure A L) :=
    IsIntegralClosure.isIntegral_algebra A L
  have : IsNoetherianRing (integralClosure A L) := by
    have : IsNoetherian A (integralClosure A L) := inferInstance
    exact isNoetherianRing_iff.mpr (isNoetherian_of_tower A this)
  exact
    { ‹IsNoetherianRing (integralClosure A L)›,
      Ring.DimensionLEOne.of_isIntegral A (integralClosure A L),
      (isIntegrallyClosed_iff L).mpr fun {x} hx =>
        ⟨IsIntegralClosure.mk' (integralClosure A L) x (isIntegral_trans (R := A) _ hx),
          IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain (integralClosure A L) }

theorem isDVR_of_finite [Module.Finite A (integralClosure A L)] :
    IsDiscreteValuationRing (integralClosure A L) := by
  have hDed := isDedekindDomain_of_finite A K L
  have hnf : ¬ IsField (integralClosure A L) := by
    intro h
    have hinj : Function.Injective (algebraMap A (integralClosure A L)) :=
      by
        have h1 : Function.Injective (algebraMap A L) := by
          rw [IsScalarTower.algebraMap_eq A K L]
          exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
        rw [IsScalarTower.algebraMap_eq A (integralClosure A L) L] at h1
        rw [RingHom.coe_comp] at h1
        exact Function.Injective.of_comp h1
    exact IsDiscreteValuationRing.not_isField A
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr h)
  have : IsNoetherianRing (integralClosure A L) := inferInstance
  exact ((IsDiscreteValuationRing.TFAE (integralClosure A L) hnf).out 3 1).mp hDed

theorem torsionFree_integralClosure : Module.IsTorsionFree A (integralClosure A L) := by
  have : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
  exact IsIntegralClosure.isTorsionFree A L

end Infra

/-- In a DVR `B` over a DVR `A`, `m B = P ^ e`. -/
theorem map_maximalIdeal_eq_pow {A B : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.IsTorsionFree A B] :
    Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ (maximalIdeal B).ramificationIdx A := by
  have hlies : (maximalIdeal B).LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    ext x
    simp [Ideal.under, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hm0 : maximalIdeal A ≠ ⊥ := fun h =>
    IsDiscreteValuationRing.not_isField A (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  have hne : Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hm0
  have hP0 : maximalIdeal B ≠ ⊥ := fun h =>
    IsDiscreteValuationRing.not_isField B (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  have hDed : IsDedekindDomain B := inferInstance
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hPϖ := hirr.maximalIdeal_eq
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hirr
  have hk' : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ k := by
    rw [hk, hPϖ, Ideal.span_singleton_pow]
  have hlt := Ideal.pow_succ_lt_pow hP0 k
  have he : (maximalIdeal A).ramificationIdx' (maximalIdeal B) = k :=
    Ideal.ramificationIdx'_spec (le_of_eq hk') (by rw [hk']; exact not_le_of_gt hlt)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) hm0, he, hk']

section Infra2

variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

include K

/-- For an unramified `L/K` (`K` perfect), `𝔪_A B = 𝔭_L`. -/
theorem map_maximalIdeal_eq [Algebra.IsSeparable K L] (hL : IsUnramifiedMilne A K L) :
    Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A) = maximalIdeal (integralClosure A L) := by
  have hfin : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L (integralClosure A L)
  have := isDVR_of_finite A K L
  have := torsionFree_integralClosure A K L
  have := isLocalHom_algebraMap_integralClosure A L
  have h := map_maximalIdeal_eq_pow (A := A) (B := integralClosure A L)
  have hef := cor_7_42 A K L
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have he : ramIdxMilne A L = 1 := by
    have h1 : ramIdxMilne A L * Module.finrank K L = 1 * Module.finrank K L := by
      rw [one_mul]
      have := hL
      unfold IsUnramifiedMilne at this
      rw [this] at hef
      exact hef
    exact Nat.eq_of_mul_eq_mul_right hn h1
  rw [h]
  have : (maximalIdeal (integralClosure A L)).ramificationIdx A = 1 := he
  rw [this, pow_one]

/-- **Hensel's lemma in `B`** for an unramified `L/K` (`B` is finite free over the complete `A`, so `𝔪_A`-adically
complete, and `𝔪_A B = 𝔭_L`). -/
theorem hensel_integralClosure [Algebra.IsSeparable K L] (hL : IsUnramifiedMilne A K L)
    (G : (integralClosure A L)[X]) (hG : G.Monic) (b : integralClosure A L)
    (h1 : G.eval b ∈ maximalIdeal (integralClosure A L))
    (h2 : IsUnit (G.derivative.eval b)) :
    ∃ a : integralClosure A L, G.IsRoot a ∧ a - b ∈ maximalIdeal (integralClosure A L) := by
  have hfin : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L (integralClosure A L)
  have := torsionFree_integralClosure A K L
  have hfree : Module.Free A (integralClosure A L) := inferInstance
  have hc : IsAdicComplete (maximalIdeal A) (integralClosure A L) :=
    isAdicComplete_of_equiv_pi (maximalIdeal A) (Module.Free.chooseBasis A (integralClosure A L)).equivFun
  have hc' : IsAdicComplete (Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A))
      (integralClosure A L) :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal A) (integralClosure A L)).mpr hc
  rw [map_maximalIdeal_eq A K L hL] at hc'
  have := IsAdicComplete.henselianRing (integralClosure A L) (maximalIdeal (integralClosure A L))
  exact this.is_henselian G hG b h1 (h2.map _)

end Infra2

/-! ## Essential surjectivity -/

section Lift

variable (k' : Type u) [Field k'] [Algebra (ResidueField A) k'] [FiniteDimensional (ResidueField A) k']
  [Algebra.IsSeparable (ResidueField A) k']

/-- Core of the lifting: `L = K[X]/(g)` for a monic lift `g` of the minimal polynomial of a primitive element of
`k'` is unramified with residue field `k'`. -/
theorem lift_core [PerfectField K] (L : Type v) [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    (g : A[X]) (hgmon : g.Monic) (α : L) (hα : aeval α g = 0)
    (pb : PowerBasis (ResidueField A) k')
    (hg : g.map (algebraMap A (ResidueField A)) = minpoly (ResidueField A) pb.gen)
    (hdeg : g.natDegree = Module.finrank K L) :
    IsUnramifiedMilne A K L ∧
      Nonempty (ResidueField (integralClosure A L) ≃ₐ[ResidueField A] k') := by
  classical
  have hsep : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hfin : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L (integralClosure A L)
  have : Module.Finite (ResidueField A) (ResidueField (integralClosure A L)) := inferInstance
  have hαint : IsIntegral A α := ⟨g, hgmon, by rwa [← aeval_def]⟩
  let b : integralClosure A L := ⟨α, hαint⟩
  have hb0 : aeval b g = 0 := by
    have h := Polynomial.aeval_algHom_apply (integralClosure A L).val b g
    exact Subtype.ext (h.symm.trans hα)
  have hroot : aeval (residue _ b) (minpoly (ResidueField A) pb.gen) = 0 := by
    rw [← hg, Polynomial.aeval_map_algebraMap (ResidueField A)]
    have h := Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom A (integralClosure A L) (ResidueField (integralClosure A L))) b g
    rw [hb0, map_zero] at h
    exact h
  let φ : k' →ₐ[ResidueField A] ResidueField (integralClosure A L) := pb.lift (residue _ b) hroot
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  have hdim : (minpoly (ResidueField A) pb.gen).natDegree = pb.dim := PowerBasis.natDegree_minpoly pb
  have hk'dim : Module.finrank (ResidueField A) k' = g.natDegree := by
    rw [pb.finrank, ← hdim, ← hg, hgmon.natDegree_map]
  have hle : Module.finrank K L ≤ Module.finrank (ResidueField A) (ResidueField (integralClosure A L)) := by
    rw [← hdeg, ← hk'dim]
    exact LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hφinj
  have hef := cor_7_42 A K L
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hge : resDegMilne A L ≤ Module.finrank K L := by
    rw [← hef]
    refine Nat.le_mul_of_pos_left _ ?_
    rcases Nat.eq_zero_or_pos (ramIdxMilne A L) with h | h
    · rw [h, zero_mul] at hef; omega
    · exact h
  rw [Thm758aFixed.resDeg_eq_finrank] at hge
  have hU : IsUnramifiedMilne A K L := by
    unfold IsUnramifiedMilne
    rw [Thm758aFixed.resDeg_eq_finrank]
    exact le_antisymm hge hle
  refine ⟨hU, ⟨(AlgEquiv.ofBijective φ ⟨hφinj, ?_⟩).symm⟩⟩
  have heq : Module.finrank (ResidueField A) k' =
      Module.finrank (ResidueField A) (ResidueField (integralClosure A L)) := by
    rw [hk'dim, hdeg]; exact le_antisymm hle hge
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq (f := φ.toLinearMap)).mp hφinj

/-- **Essential surjectivity**: every finite separable extension `k'` of `k` is the residue field of a finite
unramified extension of `K`. -/
theorem exists_lift [PerfectField K] :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra K L) (_ : Algebra A L) (_ : IsScalarTower A K L),
      FiniteDimensional K L ∧ IsUnramifiedMilne A K L ∧
        Nonempty (ResidueField (integralClosure A L) ≃ₐ[ResidueField A] k') := by
  classical
  let pb : PowerBasis (ResidueField A) k' := Field.powerBasisOfFiniteOfSeparable (ResidueField A) k'
  have hint : IsIntegral (ResidueField A) pb.gen := Algebra.IsIntegral.isIntegral pb.gen
  have hg₀m : (minpoly (ResidueField A) pb.gen).Monic := minpoly.monic hint
  have hlift : minpoly (ResidueField A) pb.gen ∈ Polynomial.lifts (algebraMap A (ResidueField A)) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => residue_surjective _
  obtain ⟨g, hgmap, hgdeg, hgmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hg₀m
  have hgirr : Irreducible g :=
    Polynomial.Monic.irreducible_of_irreducible_map (algebraMap A (ResidueField A)) g hgmon
      (by rw [hgmap]; exact minpoly.irreducible hint)
  have hKirr : Irreducible (g.map (algebraMap A K)) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hgmon).mp hgirr
  have : Fact (Irreducible (g.map (algebraMap A K))) := ⟨hKirr⟩
  have hne : g.map (algebraMap A K) ≠ 0 := hKirr.ne_zero
  let pbL := AdjoinRoot.powerBasis hne
  have : FiniteDimensional K (AdjoinRoot (g.map (algebraMap A K))) := pbL.finite
  have hdeg : g.natDegree = Module.finrank K (AdjoinRoot (g.map (algebraMap A K))) := by
    rw [pbL.finrank]
    show g.natDegree = (g.map (algebraMap A K)).natDegree
    rw [hgmon.natDegree_map]
  have hα : aeval (AdjoinRoot.root (g.map (algebraMap A K))) g = 0 := by
    rw [← Polynomial.aeval_map_algebraMap K, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  obtain ⟨hU, hiso⟩ := lift_core A K k' (AdjoinRoot (g.map (algebraMap A K))) g hgmon _ hα pb hgmap hdeg
  exact ⟨AdjoinRoot (g.map (algebraMap A K)), inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hU, hiso⟩

end Lift

/-! ## Full faithfulness -/

theorem algHom_ext_of_adjoin_eq_top {F E E' : Type*} [Field F] [Field E] [Algebra F E] [Field E']
    [Algebra F E'] (x : E) (hx : IsIntegral F x) (h : IntermediateField.adjoin F {x} = ⊤)
    (f g : E →ₐ[F] E') (hfg : f x = g x) : f = g := by
  have h1 : Algebra.adjoin F {x} = ⊤ := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hx.isAlgebraic
    rw [← this, h]; exact IntermediateField.top_toSubalgebra
  exact AlgHom.ext_of_adjoin_eq_top h1 (by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]; exact hfg)

theorem exists_algHom_of_adjoin_eq_top {F E E' : Type*} [Field F] [Field E] [Algebra F E] [Field E']
    [Algebra F E'] (x : E) (hx : IsIntegral F x) (h : IntermediateField.adjoin F {x} = ⊤)
    (y : E') (hy : aeval y (minpoly F x) = 0) : ∃ f : E →ₐ[F] E', f x = y := by
  let pb := IntermediateField.adjoin.powerBasis hx
  have hgen : minpoly F pb.gen = minpoly F x := by
    exact IntermediateField.minpoly_gen F x
  let f0 : IntermediateField.adjoin F {x} →ₐ[F] E' := pb.lift y (by rw [hgen]; exact hy)
  let e : E ≃ₐ[F] IntermediateField.adjoin F {x} :=
    IntermediateField.topEquiv.symm.trans (IntermediateField.equivOfEq h.symm)
  refine ⟨f0.comp e.toAlgHom, ?_⟩
  have : e x = pb.gen := rfl
  show f0 (e x) = y
  rw [this]
  exact pb.lift_gen y _

section HomEquiv

variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
  (L' : Type*) [Field L'] [Algebra K L'] [Algebra A L'] [IsScalarTower A K L'] [FiniteDimensional K L']

/-- A `K`-homomorphism `L → L'` restricts to an `A`-algebra homomorphism of the integral closures. -/
noncomputable def mapB (σ : L →ₐ[K] L') : integralClosure A L →ₐ[A] integralClosure A L' :=
  ((σ.restrictScalars A).comp (integralClosure A L).val).codRestrict (integralClosure A L')
    (fun x => by
      have hx : IsIntegral A (x : L) := x.2
      exact hx.map (σ.restrictScalars A))

theorem mapB_coe (σ : L →ₐ[K] L') (x : integralClosure A L) :
    ((mapB A K L L' σ x : integralClosure A L') : L') = σ (x : L) := rfl

instance mapB_isLocalHom (σ : L →ₐ[K] L') : IsLocalHom (mapB A K L L' σ) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hx
  have hy' : σ (x : L) * (y : L') = 1 := by
    have := congrArg (fun z : integralClosure A L' => (z : L')) hy
    simpa [mapB_coe] using this
  have hxne : (x : L) ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hy'
    exact zero_ne_one hy'
  have hcoe : σ ((x : L)⁻¹) = (y : L') := by
    rw [map_inv₀]
    exact (eq_inv_of_mul_eq_one_right hy').symm
  have hint : IsIntegral A ((x : L)⁻¹) := by
    refine (isIntegral_algHom_iff (σ.restrictScalars A) σ.injective).1 ?_
    show IsIntegral A (σ ((x : L)⁻¹))
    rw [hcoe]; exact y.2
  refine isUnit_iff_exists_inv.2 ⟨⟨(x : L)⁻¹, hint⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ hxne

/-- The reduction of a `K`-homomorphism `L → L'`: the induced `k`-homomorphism of residue fields. -/
noncomputable def redHom (σ : L →ₐ[K] L') :
    ResidueField (integralClosure A L) →ₐ[ResidueField A] ResidueField (integralClosure A L') :=
  ResidueField.mapAlgHom' (mapB A K L L' σ)

theorem redHom_residue (σ : L →ₐ[K] L') (b : integralClosure A L) :
    redHom A K L L' σ (residue _ b) = residue _ (mapB A K L L' σ b) :=
  ResidueField.mapAlgHom'_residue _ _

theorem aeval_residue (E : Type v) [Field E] [Algebra A E] (b : integralClosure A E) (p : A[X]) :
    aeval (residue (integralClosure A E) b) p = residue (integralClosure A E) (aeval b p) :=
  (Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom A (integralClosure A E) (ResidueField (integralClosure A E))) b p)

theorem aeval_val (E : Type v) [Field E] [Algebra A E] (b : integralClosure A E) (p : A[X]) :
    aeval (b : E) p = ((aeval b p : integralClosure A E) : E) :=
  (Polynomial.aeval_algHom_apply (integralClosure A E).val b p)

theorem separable_reduction (E : Type v) [Field E] [Algebra A E] (g : A[X])
    (hs : (g.map (algebraMap A (ResidueField A))).Separable) :
    ((g.map (algebraMap A (integralClosure A E))).map (residue (integralClosure A E))).Separable := by
  rw [Polynomial.map_map]
  have hcomp : (residue (integralClosure A E)).comp (algebraMap A (integralClosure A E)) =
      (algebraMap (ResidueField A) (ResidueField (integralClosure A E))).comp
        (algebraMap A (ResidueField A)) := RingHom.ext fun _ => rfl
  rw [hcomp, ← Polynomial.map_map]
  exact hs.map

include K in
/-- For an unramified `L/K` (with `k` perfect) there is `β ∈ B` generating `L` over `K` whose residue generates `l`
over `k`, and whose minimal polynomial over `A` has separable reduction. -/
theorem exists_generator [Algebra.IsSeparable K L] [PerfectField (ResidueField A)] (hL : IsUnramifiedMilne A K L) :
    ∃ β : integralClosure A L, IntermediateField.adjoin K {(β : L)} = ⊤ ∧
      IntermediateField.adjoin (ResidueField A) {residue (integralClosure A L) β} = ⊤ ∧
      ((minpoly A (β : L)).map (algebraMap A (ResidueField A))).Separable := by
  classical
  have hfinB : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have : Module.Finite (ResidueField A) (ResidueField (integralClosure A L)) := inferInstance
  have hsepl : Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨βb, hβb⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField (integralClosure A L))
  obtain ⟨β, rfl⟩ := residue_surjective βb
  have hn' : Module.finrank (ResidueField A) (ResidueField (integralClosure A L)) =
      Module.finrank K L := by
    rw [← Thm758aFixed.resDeg_eq_finrank]; exact hL
  have hint0 : IsIntegral A (β : L) := β.2
  have hgm := minpoly.monic hint0
  have hKdeg : (minpoly K (β : L)).natDegree = (minpoly A (β : L)).natDegree := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hint0, hgm.natDegree_map]
  have hdegle : (minpoly A (β : L)).natDegree ≤ Module.finrank K L := by
    rw [← hKdeg]; exact minpoly.natDegree_le (β : L)
  have haev0 : aeval β (minpoly A (β : L)) = 0 := by
    have h := Polynomial.aeval_algHom_apply (integralClosure A L).val β (minpoly A (β : L))
    have h' : aeval (β : L) (minpoly A (β : L)) = 0 := minpoly.aeval A (β : L)
    exact Subtype.ext (h.symm.trans h')
  have hroot : aeval (residue _ β) ((minpoly A (β : L)).map (algebraMap A (ResidueField A))) = 0 := by
    rw [Polynomial.aeval_map_algebraMap (ResidueField A), aeval_residue A L β _, haev0, map_zero]
  have hdvd := minpoly.dvd (ResidueField A) (residue _ β) hroot
  have hminpoly_deg : (minpoly (ResidueField A) (residue _ β)).natDegree = Module.finrank K L := by
    rw [← hn', ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _), hβb,
      IntermediateField.finrank_top']
  have heq : (minpoly A (β : L)).map (algebraMap A (ResidueField A)) =
      minpoly (ResidueField A) (residue _ β) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (Algebra.IsIntegral.isIntegral _))
      (hgm.map _) hdvd (by rw [hgm.natDegree_map, hminpoly_deg]; exact hdegle)
  have hgdeg : (minpoly A (β : L)).natDegree = Module.finrank K L := by
    have := congrArg Polynomial.natDegree heq
    rw [hgm.natDegree_map, hminpoly_deg] at this
    exact this
  have hsepg : ((minpoly A (β : L)).map (algebraMap A (ResidueField A))).Separable := by
    rw [heq]; exact Algebra.IsSeparable.isSeparable (ResidueField A) (residue _ β)
  have hadj : IntermediateField.adjoin K {(β : L)} = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq
    · exact le_top
    · rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _), hKdeg, hgdeg,
        IntermediateField.finrank_top']
  exact ⟨β, hadj, hβb, hsepg⟩

/-- **Full faithfulness**: for finite unramified `L, L'`, reduction is a bijection
`Hom_K(L, L') → Hom_k(l, l')`. -/
theorem hom_equiv [PerfectField K] [PerfectField (ResidueField A)]
    (hL : IsUnramifiedMilne A K L) (hL' : IsUnramifiedMilne A K L') :
    ∃ Φ : (L →ₐ[K] L') ≃
        (ResidueField (integralClosure A L) →ₐ[ResidueField A] ResidueField (integralClosure A L')),
      ∀ (σ : L →ₐ[K] L') (b : integralClosure A L) (b' : integralClosure A L'), (b' : L') = σ b →
        Φ σ (residue _ b) = residue _ b' := by
  classical
  have hsep : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hsep' : Algebra.IsSeparable K L' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hfinB : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have : Module.Finite (ResidueField A) (ResidueField (integralClosure A L)) := inferInstance
  obtain ⟨α, hαK, hαk, hsepg⟩ := exists_generator A K L hL
  have hαint : IsIntegral A (α : L) := α.2
  set g := minpoly A (α : L) with hg
  have hgm : g.Monic := minpoly.monic hαint
  have hgK : minpoly K (α : L) = g.map (algebraMap A K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hαint
  have haev0 : aeval α g = 0 := by
    have h := Polynomial.aeval_algHom_apply (integralClosure A L).val α g
    have h' : aeval (α : L) g = 0 := minpoly.aeval A (α : L)
    exact Subtype.ext (h.symm.trans h')
  have hroot_mapB : ∀ σ : L →ₐ[K] L', aeval (mapB A K L L' σ α) g = 0 := fun σ => by
    have h := Polynomial.aeval_algHom_apply (mapB A K L L' σ) α g
    rw [haev0, map_zero] at h
    exact h
  have hinj : Function.Injective (redHom A K L L') := by
    intro σ τ hστ
    have h1 : residue _ (mapB A K L L' σ α) = residue _ (mapB A K L L' τ α) := by
      rw [← redHom_residue, ← redHom_residue, hστ]
    have hsame : mapB A K L L' σ α = mapB A K L L' τ α := by
      by_contra hne
      have hmax : mapB A K L L' τ α - mapB A K L L' σ α ∈ maximalIdeal (integralClosure A L') :=
        (Ideal.Quotient.eq (I := maximalIdeal (integralClosure A L'))).1 h1.symm
      exact Thm758aFixed.not_separable_of_two_roots (g.map (algebraMap A (integralClosure A L')))
        (mapB A K L L' σ α) (mapB A K L L' τ α)
        (by rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]; exact hroot_mapB σ)
        (by rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]; exact hroot_mapB τ)
        hne hmax (separable_reduction A L' g hsepg)
    exact algHom_ext_of_adjoin_eq_top (α : L) (Algebra.IsIntegral.isIntegral _) hαK σ τ
      (congrArg Subtype.val hsame)
  have hsurj : Function.Surjective (redHom A K L L') := by
    intro ψ
    have hr0 : aeval (ψ (residue _ α)) (g.map (algebraMap A (ResidueField A))) = 0 := by
      have h1 : aeval (residue _ α) (g.map (algebraMap A (ResidueField A))) = 0 := by
        rw [Polynomial.aeval_map_algebraMap (ResidueField A), aeval_residue A L, haev0, map_zero]
      have := Polynomial.aeval_algHom_apply ψ (residue _ α) (g.map (algebraMap A (ResidueField A)))
      rw [h1, map_zero] at this
      exact this
    obtain ⟨β, hβ⟩ := residue_surjective (ψ (residue _ α))
    have hr1 : aeval (residue _ β) g = 0 := by
      rw [hβ, ← Polynomial.aeval_map_algebraMap (ResidueField A)]
      exact hr0
    have hGm : (g.map (algebraMap A (integralClosure A L'))).Monic := hgm.map _
    have hGβ : (g.map (algebraMap A (integralClosure A L'))).eval β ∈
        maximalIdeal (integralClosure A L') := by
      rw [← residue_eq_zero_iff, Polynomial.eval_map_algebraMap, ← aeval_residue A L']
      exact hr1
    have hGd : IsUnit ((g.map (algebraMap A (integralClosure A L'))).derivative.eval β) := by
      have hne : aeval (ψ (residue _ α)) (derivative (g.map (algebraMap A (ResidueField A)))) ≠ 0 :=
        hsepg.aeval_derivative_ne_zero hr0
      rw [Polynomial.derivative_map, Polynomial.aeval_map_algebraMap (ResidueField A), ← hβ,
        aeval_residue A L'] at hne
      rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap, ← notMem_maximalIdeal]
      intro hm
      exact hne ((residue_eq_zero_iff _).2 hm)
    obtain ⟨β₀, hβ₀, hβ₀β⟩ := hensel_integralClosure A K L' hL' _ hGm β hGβ hGd
    have hres : residue (integralClosure A L') β₀ = ψ (residue _ α) := by
      rw [← hβ]
      exact (Ideal.Quotient.eq (I := maximalIdeal (integralClosure A L'))).2 hβ₀β
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at hβ₀
    have hβ₀L : aeval (β₀ : L') (minpoly K (α : L)) = 0 := by
      rw [hgK, Polynomial.aeval_map_algebraMap K, aeval_val A L', hβ₀]
      rfl
    obtain ⟨σ, hσ⟩ := exists_algHom_of_adjoin_eq_top (α : L) (Algebra.IsIntegral.isIntegral _) hαK
      (β₀ : L') hβ₀L
    refine ⟨σ, ?_⟩
    refine algHom_ext_of_adjoin_eq_top (residue (integralClosure A L) α)
      (Algebra.IsIntegral.isIntegral _) hαk _ _ ?_
    rw [redHom_residue, ← hres]
    congr 1
    exact Subtype.ext hσ
  refine ⟨Equiv.ofBijective (redHom A K L L') ⟨hinj, hsurj⟩, fun σ b b' hb' => ?_⟩
  show redHom A K L L' σ (residue _ b) = residue _ b'
  rw [redHom_residue]
  congr 1
  exact Subtype.ext hb'.symm

end HomEquiv

end Remark753

/-- **Remark 7.53.** Reduction is an equivalence between the category of finite unramified extensions of $K$ and that
of finite separable extensions of $k$ (for $K$ and $k$ perfect): fully faithful (`Remark753.hom_equiv`) and essentially
surjective (`Remark753.exists_lift`). Discharges the named statement `Remark7_53`. -/
@[kb "milne2020ant" "v3.08, Remark 7.53, p. 129"]
theorem remark_7_53 (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    [PerfectField K] [PerfectField (ResidueField A)] : Remark7_53 A K :=
  ⟨fun L _ _ _ _ _ L' _ _ _ _ _ hL hL' => Remark753.hom_equiv A K L L' hL hL',
    fun k' _ _ _ _ => Remark753.exists_lift A K k'⟩

end NumberFieldKB.MilneANT
