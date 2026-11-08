import NumberFieldKB.MilneANT.Ch7Integral

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: extensions of a complete discretely valued field

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Setting. Milne's $K$ is complete with respect to a discrete absolute value, with discrete valuation ring $A$. Here
$A$ is a discrete valuation ring that is complete for its maximal ideal (`IsAdicComplete (maximalIdeal A) A`; for a
discrete valuation ring this is completeness for the absolute value) and $K$ is its field of fractions. For an
extension $L$ of $K$, Milne's ring $B = \{\alpha \in L : |\alpha| \le 1\}$ is the integral closure of $A$ in $L$
(Milne p. 124: "the valuation ring $B$ of $L$ is the integral closure of the valuation ring $A$ of $K$"); it is a local
ring (`isLocalRing_integralClosure`), its maximal ideal is $\mathfrak p_L$, and its residue field is the residue field
$l$ of $L$. The ramification index $e$ and residue degree $f$ are Mathlib's `Ideal.ramificationIdx` and
`Ideal.inertiaDeg` of the maximal ideal of $B$ over $A$.

* Definitions in prose (p. 124, p. 131): `ramIdxMilne`, `resDegMilne`, `IsTotallyRamifiedMilne` ($e = n$),
  `IsUnramifiedMilne` ($f = n$), `IsWildlyRamifiedMilne` ($p \mid e$), `IsTamelyRamifiedMilne`.
* **Corollary 7.42** (`cor_7_42`): $n = ef$.
* **Proposition 7.50**, **Corollaries 7.51, 7.52**, **Remark 7.53**, **Example 7.54**: unramified extensions
  (named statements `Prop7_50`, `Cor7_51`, `Cor7_52`, `Remark7_53`, `Example7_54`).
* **Proposition 7.55** (`prop_7_55`) and **Remark 7.56** (`remark_7_56`): totally ramified extensions and Eisenstein
  polynomials.
-/

open IsLocalRing Polynomial

universe u v w

namespace NumberFieldKB.MilneANT

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

/-! ## Ramification index and residue degree -/

section Defs

variable (L : Type w) [Field L] [Algebra A L]

/-- The ramification index $e$ of $L$ over $K$ (Milne p. 124): the ramification index of the maximal ideal of $B$ (the
integral closure of $A$ in $L$) over $A$. -/
noncomputable def ramIdxMilne : ℕ := (maximalIdeal (integralClosure A L)).ramificationIdx A

/-- The residue degree $f$ of $L$ over $K$ (Milne p. 124): the degree of the residue field of $L$ over that of $K$. -/
noncomputable def resDegMilne : ℕ := (maximalIdeal (integralClosure A L)).inertiaDeg A

variable [Algebra K L]

/-- **Totally ramified extension** (prose definition, Milne p. 124): $L/K$ finite with $e = n = [L : K]$
(equivalently $\mathfrak p B = \mathfrak P^n$). -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of totally ramified, p. 124"]
def IsTotallyRamifiedMilne : Prop := ramIdxMilne A L = Module.finrank K L

/-- **Unramified extension** (prose definition, Milne p. 124): $L/K$ finite with $f = n = [L : K]$. -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of unramified, p. 124"]
def IsUnramifiedMilne : Prop := resDegMilne A L = Module.finrank K L

/-- **Wildly ramified extension** (prose definition, Milne p. 131): $p \mid e$, where $p$ is the characteristic of the
residue field $k$. (If $\operatorname{char} k = 0$ this never holds, since $e \ge 1$.) -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of wildly ramified, p. 131"]
def IsWildlyRamifiedMilne : Prop := ringChar (ResidueField A) ∣ ramIdxMilne A L

/-- **Tamely ramified extension** (prose definition, Milne p. 131): not wildly ramified. -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of tamely ramified, p. 131"]
def IsTamelyRamifiedMilne : Prop := ¬ IsWildlyRamifiedMilne A L

end Defs

/-! ## Corollary 7.42 -/

section Helpers

variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

include K

/-- If the integral closure `B` of `A` in `L` is finite over `A`, it is a Dedekind domain (no separability needed). -/
private theorem isDedekindDomain_of_finite [Module.Finite A (integralClosure A L)] :
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

/-- **Corollary 7.42**, assuming `B` is finite over `A`. -/
private theorem ef_eq_finrank_of_finite [Module.Finite A (integralClosure A L)] :
    ramIdxMilne A L * resDegMilne A L = Module.finrank K L := by
  have : IsDedekindDomain A := inferInstance
  have : IsDomain (integralClosure A L) := inferInstance
  have : IsDedekindDomain (integralClosure A L) := isDedekindDomain_of_finite A K L
  have : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
  have : Module.IsTorsionFree A (integralClosure A L) := IsIntegralClosure.isTorsionFree A L
  have : Module.Free A (integralClosure A L) := inferInstance
  have hrank : Module.finrank A (integralClosure A L) = Module.finrank K L := by
    have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A L) (nonZeroDivisors A)) L :=
      IsIntegralClosure.isLocalization A K L (integralClosure A L)
    let b := Module.Basis.localizationLocalization K (nonZeroDivisors A) L (Module.Free.chooseBasis A (integralClosure A L))
    rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis b]
  set P := maximalIdeal (integralClosure A L) with hP
  have hlies : P.LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    ext x
    simp [Ideal.under, hP, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have huniq : ∀ q : (maximalIdeal A).primesOver (integralClosure A L), q.1 = P := by
    intro q
    obtain ⟨hq, hql⟩ := q.2
    have hq0 : q.1 ≠ ⊥ := by
      intro h
      have := hql.over
      rw [h, Ideal.under_bot] at this
      exact (IsDiscreteValuationRing.not_isField A)
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr this)
    exact (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal hq hq0))
  have : Unique ((maximalIdeal A).primesOver (integralClosure A L)) :=
    { default := ⟨P, inferInstance, hlies⟩
      uniq := fun q => Subtype.ext (huniq q) }
  have := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal A) (integralClosure A L)
  rw [Fintype.sum_unique] at this
  rw [huniq default] at this
  rw [← hrank, ← this]
  rfl

/-- The integral closure of the complete discrete valuation ring `A` in a finite separable extension `L` of `K` is a
finite `A`-module (`IsIntegralClosure.finite`). -/
private theorem finite_integralClosure [Algebra.IsSeparable K L] : Module.Finite A (integralClosure A L) :=
  IsIntegralClosure.finite A K L (integralClosure A L)

/-- If `B` is finite over `A` then `B` is a discrete valuation ring. -/
private theorem isDVR_of_finite [Module.Finite A (integralClosure A L)] :
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

end Helpers

/-- **Corollary 7.42.** Let $L$ be a finite separable extension of $K$ of degree $n$. Then $n = ef$, where $e$ is the
ramification index and $f$ the degree of the residue field extension. -/
@[kb "milne2020ant" "v3.08, Cor. 7.42, p. 124"]
theorem cor_7_42 (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    ramIdxMilne A L * resDegMilne A L = Module.finrank K L := by
  have : Module.Finite A (integralClosure A L) :=
    IsIntegralClosure.finite A K L (integralClosure A L)
  exact ef_eq_finrank_of_finite A K L

/-! ## Generic ring-theoretic lemmas for totally ramified extensions -/

section Generic

/-- Nakayama step: if `B` is finite over the DVR `A`, `P = (ϖ)` is the maximal ideal of `B`, `P^e ⊆ 𝔪 B`, and the
residue map `A → B/P` is surjective, then `B = A[ϖ]`. -/
private theorem adjoin_eq_top_of_residue_surjective {A B : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Module.Finite A B]
    (ϖ : B) (hϖ : maximalIdeal B = Ideal.span {ϖ}) (e : ℕ)
    (hmap : maximalIdeal B ^ e ≤ Ideal.map (algebraMap A B) (maximalIdeal A))
    (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B) :
    Algebra.adjoin A {ϖ} = ⊤ := by
  set M : Subalgebra A B := Algebra.adjoin A {ϖ} with hM
  have hϖM : ϖ ∈ M := Algebra.subset_adjoin rfl
  have key : ∀ k : ℕ, ∀ b : B, ∃ x ∈ M, b - x ∈ maximalIdeal B ^ k := by
    intro k
    induction k with
    | zero => intro b; exact ⟨0, M.zero_mem, by simp⟩
    | succ k ih =>
      intro b
      obtain ⟨x, hx, hbx⟩ := ih b
      rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hbx
      obtain ⟨y, hy⟩ := hbx
      obtain ⟨a, ha⟩ := hres y
      refine ⟨x + ϖ ^ k * algebraMap A B a, M.add_mem hx (M.mul_mem (M.pow_mem hϖM k) (M.algebraMap_mem a)), ?_⟩
      rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
      rw [hϖ, Ideal.mem_span_singleton'] at ha
      obtain ⟨z, hz⟩ := ha
      refine ⟨z, ?_⟩
      have : b - (x + ϖ ^ k * algebraMap A B a) = (b - x) - ϖ ^ k * algebraMap A B a := by ring
      rw [this, ← hy]
      have : y = z * ϖ + algebraMap A B a := by rw [hz]; ring
      rw [this]; ring
  have hfg : (⊤ : Submodule A B).FG := Module.finite_def.mp inferInstance
  have h1 : (⊤ : Submodule A B) ≤ Subalgebra.toSubmodule M ⊔ maximalIdeal A • (⊤ : Submodule A B) := by
    intro b _
    obtain ⟨x, hx, hbx⟩ := key (e) b
    have hbx' : b - x ∈ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A)) :=
      hmap hbx
    rw [← Ideal.smul_top_eq_map] at hbx'
    have : b = x + (b - x) := by ring
    rw [this]
    exact Submodule.add_mem_sup hx hbx'
  have := Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson _) h1
  rw [eq_top_iff]
  intro b _
  exact this (Submodule.mem_top)

/-- Residue degree one means the residue map `A → B/P` is surjective. -/
private theorem residue_surjective_of_inertiaDeg_eq_one {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (h : (maximalIdeal B).inertiaDeg A = 1) :
    ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B := by
  have hlies : (maximalIdeal B).LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    ext x
    simp [Ideal.under, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  let : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field _
  have h2 : Module.finrank (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B) = 1 := by
    rw [← h]
    exact (Ideal.inertiaDeg_eq_of_isFractionRing (maximalIdeal A) (maximalIdeal B)
      (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B)).symm
  rw [finrank_eq_one_iff_of_nonzero' (1 : B ⧸ maximalIdeal B) one_ne_zero] at h2
  intro b
  obtain ⟨c, hc⟩ := h2 (Ideal.Quotient.mk _ b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  rw [← hc, Algebra.smul_def]
  simp

/-- In a DVR `B` over a DVR `A` (with `m` the maximal ideal of `A`), `m B = P ^ e`. -/
private theorem map_maximalIdeal_eq_pow {A B : Type*} [CommRing A] [IsDomain A]
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

end Generic

section EisensteinLower

variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

include K

/-- If `L = K(α)` for a root `α` of an Eisenstein polynomial over `A` (and `B` is finite over `A`), then `[L : K] ≤ e`. -/
private theorem finrank_le_ramIdx_of_eisenstein [Module.Finite A (integralClosure A L)] (α : L)
    (hα : IntermediateField.adjoin K {α} = ⊤) (f : A[X]) (hf : f.IsEisensteinAt (maximalIdeal A))
    (h0 : aeval α f = 0) : Module.finrank K L ≤ ramIdxMilne A L := by
  have hDVR := isDVR_of_finite A K L
  have : Module.IsTorsionFree A (integralClosure A L) := by
    have : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
    exact IsIntegralClosure.isTorsionFree A L
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure A L)
  have hPϖ := hirr.maximalIdeal_eq
  have hmap := map_maximalIdeal_eq_pow (A := A) (B := integralClosure A L)
  set e := ramIdxMilne A L with he
  have hmap' : Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A) = Ideal.span {ϖ ^ e} := by
    have hmap2 : Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A) =
        maximalIdeal (integralClosure A L) ^ e := hmap
    rw [hmap2, hPϖ, Ideal.span_singleton_pow]
  have hϖ0 : ϖ ≠ 0 := hirr.ne_zero
  -- the polynomial
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf.leading (by simp)
  have hcd : IsUnit f.leadingCoeff := IsLocalRing.notMem_maximalIdeal.mp hf.leading
  have hd : 0 < f.natDegree := by
    by_contra h
    have h' : f.natDegree = 0 := by omega
    have hC : f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h'
    rw [hC, aeval_C] at h0
    have h1 : f.coeff 0 = 0 := by
      have hinj : Function.Injective (algebraMap A L) := by
        rw [IsScalarTower.algebraMap_eq A K L]
        exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
      exact hinj (by simpa using h0)
    apply hf.leading
    rw [Polynomial.leadingCoeff, h', h1]
    exact Submodule.zero_mem _
  obtain ⟨d', hd'⟩ : ∃ d', f.natDegree = d' + 1 := ⟨f.natDegree - 1, by omega⟩
  -- integrality
  have hint : IsIntegral A α := by
    obtain ⟨u, hu⟩ := hcd
    have h2 := (isIntegral_leadingCoeff_smul f α h0).smul (↑u⁻¹ : A)
    have h3 : (↑u⁻¹ : A) • (f.leadingCoeff • α) = α := by
      rw [smul_smul, ← hu]; simp
    rwa [h3] at h2
  set β : integralClosure A L := ⟨α, hint⟩ with hβdef
  have hβ : aeval β f = 0 := by
    apply Subtype.val_injective
    have := Polynomial.aeval_algHom_apply (integralClosure A L).val β f
    simpa [hβdef, h0] using this.symm
  -- coefficients
  have hcP : ∀ a : A, a ∈ maximalIdeal A → algebraMap A (integralClosure A L) a ∈ maximalIdeal (integralClosure A L) := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    exact fun h => ha (IsLocalHom.map_nonunit _ h)
  have hcdvd : ∀ i, i < f.natDegree → ϖ ^ e ∣ algebraMap A (integralClosure A L) (f.coeff i) := by
    intro i hi
    have : algebraMap A (integralClosure A L) (f.coeff i) ∈ Ideal.span {ϖ ^ e} := by
      rw [← hmap']; exact Ideal.mem_map_of_mem _ (hf.mem hi)
    exact Ideal.mem_span_singleton.mp this
  have hc0 : ¬ ϖ ^ (e + 1) ∣ algebraMap A (integralClosure A L) (f.coeff 0) := by
    intro hdv
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
    have hπm := hπ.maximalIdeal_eq
    have h00 : f.coeff 0 ∈ maximalIdeal A := hf.mem (by omega)
    rw [hπm, Ideal.mem_span_singleton'] at h00
    obtain ⟨t, ht⟩ := h00
    by_cases htm : t ∈ maximalIdeal A
    · apply hf.notMem
      rw [pow_two, ← ht]
      have : π ∈ maximalIdeal A := by rw [hπm]; exact Ideal.mem_span_singleton_self π
      exact Ideal.mul_mem_mul htm this
    · have htu : IsUnit t := IsLocalRing.notMem_maximalIdeal.mp htm
      obtain ⟨v, hv⟩ := htu
      have hπdvd : ϖ ^ (e + 1) ∣ algebraMap A (integralClosure A L) π := by
        have : π = f.coeff 0 * (↑v⁻¹ : A) := by
          rw [← ht, ← hv]
          linear_combination (-π) * (Units.mul_inv v)
        rw [this, map_mul]
        exact Dvd.dvd.mul_right hdv _
      have hmem : ϖ ^ e ∈ Ideal.span {algebraMap A (integralClosure A L) π} := by
        have : Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A) =
            Ideal.span {algebraMap A (integralClosure A L) π} := by
          rw [hπm, Ideal.map_span, Set.image_singleton]
        rw [← this, hmap']
        exact Ideal.mem_span_singleton_self _
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hmem
      obtain ⟨z, hz⟩ := hπdvd
      have : ϖ ^ e * 1 = ϖ ^ e * (ϖ * (z * y)) := by
        calc ϖ ^ e * 1 = ϖ ^ e := mul_one _
          _ = _ := by rw [hz] at hy; linear_combination hy
      have h1 := mul_left_cancel₀ (pow_ne_zero e hϖ0) this
      exact hirr.not_isUnit (IsUnit.of_mul_eq_one (z * y) h1.symm)
  -- the degree bound
  have hdeg : Module.finrank K L ≤ f.natDegree := by
    have hintK : IsIntegral K α := IsIntegral.of_finite K α
    have h1 : Module.finrank K L = (minpoly K α).natDegree := by
      rw [← IntermediateField.finrank_top' (F := K) (E := L), ← hα,
        IntermediateField.adjoin.finrank hintK]
    have hne : f.map (algebraMap A K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (IsFractionRing.injective A K)).mpr hf0
    have h2 := minpoly.degree_le_of_ne_zero K α hne (by rwa [Polynomial.aeval_map_algebraMap])
    have h3 := Polynomial.natDegree_le_natDegree h2
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective A K)] at h3
    rwa [h1]
  -- expand the equation
  have hexp := hβ
  rw [aeval_eq_sum_range, hd', Finset.sum_range_succ,
    Finset.sum_range_succ' (fun i => f.coeff i • β ^ i) d'] at hexp
  set T := ∑ i ∈ Finset.range d', f.coeff (i + 1) • β ^ (i + 1) with hT
  have hcdB : IsUnit (algebraMap A (integralClosure A L) f.leadingCoeff) := hcd.map _
  have hlead : f.coeff (d' + 1) = f.leadingCoeff := by rw [Polynomial.leadingCoeff, hd']
  have hTP : T ∈ maximalIdeal (integralClosure A L) := by
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (hcP _ (hf.mem (by have := Finset.mem_range.mp hi; omega)))
  have hc0P : algebraMap A (integralClosure A L) (f.coeff 0) ∈ maximalIdeal (integralClosure A L) :=
    hcP _ (hf.mem (by omega))
  have hβP : β ∈ maximalIdeal (integralClosure A L) := by
    by_contra hnot
    have hu : IsUnit β := IsLocalRing.notMem_maximalIdeal.mp hnot
    have hlast : algebraMap A (integralClosure A L) f.leadingCoeff * β ^ (d' + 1) ∈
        maximalIdeal (integralClosure A L) := by
      have : algebraMap A (integralClosure A L) f.leadingCoeff * β ^ (d' + 1) = -(T + algebraMap A (integralClosure A L) (f.coeff 0)) := by
        rw [← hlead]
        simp only [Algebra.smul_def, pow_zero, mul_one] at hexp
        linear_combination hexp
      rw [this]
      exact Ideal.neg_mem_iff _ |>.mpr (Ideal.add_mem _ hTP hc0P)
    exact (IsLocalRing.notMem_maximalIdeal.mpr (hcdB.mul (hu.pow _))) hlast
  have hβ0 : β ≠ 0 := by
    intro h
    have := Polynomial.coeff_zero_eq_aeval_zero' (A := integralClosure A L) f
    rw [← h, hβ] at this
    apply hf.notMem
    have h00 : f.coeff 0 = 0 := by
      apply FaithfulSMul.algebraMap_injective A (integralClosure A L)
      rw [this, map_zero]
    rw [h00]; exact Submodule.zero_mem _
  obtain ⟨w, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hβ0 hirr
  have hϖβ : ϖ ∣ β := by
    rw [hPϖ] at hβP
    exact Ideal.mem_span_singleton.mp hβP
  have hwd : w * (d' + 1) ≤ e := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h1 : ϖ ^ (e + 1) ∣ β ^ (d' + 1) := by
      rw [hu, mul_pow, ← pow_mul]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hlt) _
    have h2 : ϖ ^ (e + 1) ∣ T := by
      refine Finset.dvd_sum fun i hi => ?_
      rw [Algebra.smul_def, pow_succ ϖ e]
      exact mul_dvd_mul (hcdvd _ (by have := Finset.mem_range.mp hi; omega))
        (dvd_pow hϖβ (Nat.succ_ne_zero i))
    have h3 : ϖ ^ (e + 1) ∣ algebraMap A (integralClosure A L) (f.coeff 0) := by
      have : algebraMap A (integralClosure A L) (f.coeff 0) =
          -(T + algebraMap A (integralClosure A L) f.leadingCoeff * β ^ (d' + 1)) := by
        rw [← hlead]
        simp only [Algebra.smul_def, pow_zero, mul_one] at hexp
        linear_combination hexp
      rw [this, dvd_neg]
      exact dvd_add h2 (Dvd.dvd.mul_left h1 _)
    exact hc0 h3
  have hw : 1 ≤ w := by
    by_contra h
    have : w = 0 := by omega
    rw [this, pow_zero, mul_one] at hu
    exact (IsLocalRing.notMem_maximalIdeal.mpr (hu ▸ u.isUnit)) hβP
  calc Module.finrank K L ≤ f.natDegree := hdeg
    _ = d' + 1 := hd'
    _ ≤ w * (d' + 1) := Nat.le_mul_of_pos_left _ hw
    _ ≤ e := hwd

end EisensteinLower

section TotallyRamifiedLemmas

variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

include K

/-- If `L/K` is totally ramified (and `B` is finite over `A`), a uniformizer generates `B` over `A`. -/
private theorem adjoin_uniformizer_eq_top [Module.Finite A (integralClosure A L)]
    (hL : IsTotallyRamifiedMilne A K L) (ϖ : integralClosure A L)
    (hϖ : maximalIdeal (integralClosure A L) = Ideal.span {ϖ}) :
    Algebra.adjoin A {ϖ} = ⊤ := by
  have hDVR := isDVR_of_finite A K L
  have : Module.IsTorsionFree A (integralClosure A L) := by
    have : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
    exact IsIntegralClosure.isTorsionFree A L
  have hef := ef_eq_finrank_of_finite A K L
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hL' : ramIdxMilne A L = Module.finrank K L := hL
  have hf : resDegMilne A L = 1 := by
    rw [hL'] at hef
    exact Nat.eq_of_mul_eq_mul_left hn (by rw [mul_one]; exact hef)
  have hmap := map_maximalIdeal_eq_pow (A := A) (B := integralClosure A L)
  exact adjoin_eq_top_of_residue_surjective ϖ hϖ _ (le_of_eq hmap.symm)
    (residue_surjective_of_inertiaDeg_eq_one hf)

/-- A totally ramified `L/K` (with `B` finite over `A`) is generated by a root of an Eisenstein polynomial. -/
private theorem exists_eisenstein_of_totally_ramified [Module.Finite A (integralClosure A L)]
    (hL : IsTotallyRamifiedMilne A K L) :
    ∃ α : L, IntermediateField.adjoin K {α} = ⊤ ∧
      ∃ f : A[X], f.IsEisensteinAt (maximalIdeal A) ∧ aeval α f = 0 := by
  have hTFL : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
  have hDVR := isDVR_of_finite A K L
  have : Module.IsTorsionFree A (integralClosure A L) := by
    have : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
    exact IsIntegralClosure.isTorsionFree A L
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure A L)
  have hPϖ := hirr.maximalIdeal_eq
  have hϖ0 : ϖ ≠ 0 := hirr.ne_zero
  have hM : Algebra.adjoin A {ϖ} = ⊤ := adjoin_uniformizer_eq_top A K L hL ϖ hPϖ
  have hL' : ramIdxMilne A L = Module.finrank K L := hL
  have hmap := map_maximalIdeal_eq_pow (A := A) (B := integralClosure A L)
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  set n := Module.finrank K L with hn_def
  have hmap' : Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A) = Ideal.span {ϖ ^ n} := by
    have hmap2 : Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A) =
        maximalIdeal (integralClosure A L) ^ n := by rw [← hL']; exact hmap
    rw [hmap2, hPϖ, Ideal.span_singleton_pow]
  set α : L := (ϖ : L) with hαdef
  have hint : IsIntegral A α := ϖ.2
  have hval : ∀ p : A[X], aeval α p = ((aeval ϖ p : integralClosure A L) : L) := fun p =>
    Polynomial.aeval_algHom_apply (integralClosure A L).val ϖ p
  -- `α` generates `L`
  have hα : IntermediateField.adjoin K {α} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : IsFractionRing (integralClosure A L) L :=
      IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := integralClosure A L) x
    have hmemB : ∀ c : integralClosure A L, (c : L) ∈ IntermediateField.adjoin K {α} := by
      intro c
      have hc : c ∈ Algebra.adjoin A {ϖ} := by rw [hM]; trivial
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hc
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact IntermediateField.mem_adjoin_simple_self K α
      · intro r
        have : ((algebraMap A (integralClosure A L) r : integralClosure A L) : L) =
            algebraMap K L (algebraMap A K r) := by
          rw [← IsScalarTower.algebraMap_apply A K L]; rfl
        rw [this]
        exact IntermediateField.algebraMap_mem _ _
      · intro y z _ _ hy hz
        exact add_mem hy hz
      · intro y z _ _ hy hz
        exact mul_mem hy hz
    exact div_mem (hmemB a) (hmemB b)
  -- the minimal polynomial
  set g := minpoly A α with hg
  have hgmonic : g.Monic := minpoly.monic hint
  have hgdeg : g.natDegree = n := by
    have hintK : IsIntegral K α := IsIntegral.of_finite K α
    have h1 : Module.finrank K L = (minpoly K α).natDegree := by
      rw [← IntermediateField.finrank_top' (F := K) (E := L), ← hα,
        IntermediateField.adjoin.finrank hintK]
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hint,
      Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective A K)] at h1
    exact h1.symm
  have hgϖ : aeval ϖ g = 0 := by
    apply Subtype.val_injective
    rw [← hval]
    exact minpoly.aeval A α
  -- coefficients lie in the maximal ideal
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπm := hπ.maximalIdeal_eq
  have hπmem : π ∈ maximalIdeal A := by rw [hπm]; exact Ideal.mem_span_singleton_self π
  have hspan : Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A) =
      Ideal.span {algebraMap A (integralClosure A L) π} := by
    rw [hπm, Ideal.map_span, Set.image_singleton]
  have hcoeff : ∀ i, i < n → g.coeff i ∈ maximalIdeal A := by
    obtain ⟨y, hy⟩ : ∃ y, ϖ ^ n = algebraMap A (integralClosure A L) π * y := by
      have : ϖ ^ n ∈ Ideal.span {algebraMap A (integralClosure A L) π} := by
        rw [← hspan, hmap']; exact Ideal.mem_span_singleton_self _
      exact Ideal.mem_span_singleton.mp this
    obtain ⟨q, hq⟩ : ∃ q : A[X], aeval ϖ q = y := by
      have : y ∈ Algebra.adjoin A {ϖ} := by rw [hM]; trivial
      rwa [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at this
    have hz : aeval α (X ^ n - C π * q) = 0 := by
      rw [hval]
      have : aeval ϖ (X ^ n - C π * q) = 0 := by
        simp only [map_sub, map_pow, aeval_X, map_mul, aeval_C, hq]
        rw [hy, sub_self]
      rw [this]; rfl
    obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd hint hz
    let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
    have hmod := congrArg (Polynomial.map (Ideal.Quotient.mk (maximalIdeal A))) hh
    have hπ0 : Ideal.Quotient.mk (maximalIdeal A) π = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hπmem
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_C,
      hπ0, map_zero, zero_mul, sub_zero, Polynomial.map_mul] at hmod
    have hdvd : g.map (Ideal.Quotient.mk (maximalIdeal A)) ∣ (X : (A ⧸ maximalIdeal A)[X]) ^ n :=
      ⟨_, hmod⟩
    obtain ⟨j, hj, hass⟩ := (dvd_prime_pow Polynomial.prime_X n).mp hdvd
    have hmon : (g.map (Ideal.Quotient.mk (maximalIdeal A))).Monic := hgmonic.map _
    have heq := Polynomial.eq_of_monic_of_associated hmon (Polynomial.monic_X_pow j) hass
    have hjn : j = n := by
      have := hgmonic.natDegree_map (Ideal.Quotient.mk (maximalIdeal A))
      have h2 := congrArg Polynomial.natDegree heq
      rw [Polynomial.natDegree_X_pow] at h2
      rw [hgdeg] at this
      omega
    intro i hi
    have := congrArg (fun p => Polynomial.coeff p i) heq
    simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow] at this
    rw [hjn] at this
    simp only [show i ≠ n from by omega, ite_false] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  refine ⟨α, hα, g, ⟨?_, fun {i} hi => hcoeff i (by rwa [hgdeg] at hi), ?_⟩, minpoly.aeval A α⟩
  · rw [hgmonic.leadingCoeff]
    exact fun h => (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · intro h2
    obtain ⟨d', hd'⟩ : ∃ d', n = d' + 1 := ⟨n - 1, by omega⟩
    have hrange : Finset.range n = Finset.range (d' + 1) := by rw [hd']
    have hexp := hgϖ
    rw [aeval_eq_sum_range, Finset.sum_range_succ, hgmonic.coeff_natDegree, hgdeg, hrange,
      Finset.sum_range_succ' (fun i => g.coeff i • ϖ ^ i) d'] at hexp
    set T := ∑ i ∈ Finset.range d', g.coeff (i + 1) • ϖ ^ (i + 1) with hT
    have hϖβ : ϖ ∣ ϖ := dvd_rfl
    have hc0 : ϖ ^ (n + 1) ∣ algebraMap A (integralClosure A L) (g.coeff 0) := by
      have hmem : algebraMap A (integralClosure A L) (g.coeff 0) ∈
          Ideal.map (algebraMap A (integralClosure A L)) (maximalIdeal A ^ 2) := Ideal.mem_map_of_mem _ h2
      rw [Ideal.map_pow, hmap', Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← pow_mul] at hmem
      exact (pow_dvd_pow ϖ (by omega)).trans hmem
    have hTd : ϖ ^ (n + 1) ∣ T := by
      refine Finset.dvd_sum fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      have h1 : ϖ ^ n ∣ algebraMap A (integralClosure A L) (g.coeff (i + 1)) := by
        have : algebraMap A (integralClosure A L) (g.coeff (i + 1)) ∈ Ideal.span {ϖ ^ n} := by
          rw [← hmap']; exact Ideal.mem_map_of_mem _ (hcoeff _ (by omega))
        exact Ideal.mem_span_singleton.mp this
      rw [Algebra.smul_def, pow_succ ϖ n]
      exact mul_dvd_mul h1 (dvd_pow_self ϖ (Nat.succ_ne_zero i))
    have hfin : ϖ ^ n = -(T + algebraMap A (integralClosure A L) (g.coeff 0)) := by
      simp only [Algebra.smul_def, pow_zero, mul_one, map_one, one_mul] at hexp
      linear_combination hexp
    have hd : ϖ ^ (n + 1) ∣ ϖ ^ n := by
      rw [hfin, dvd_neg]; exact dvd_add hTd hc0
    obtain ⟨z, hz⟩ := hd
    have : ϖ ^ n * 1 = ϖ ^ n * (ϖ * z) := by
      calc ϖ ^ n * 1 = ϖ ^ n := mul_one _
        _ = _ := by linear_combination hz
    have h1 := mul_left_cancel₀ (pow_ne_zero n hϖ0) this
    exact hirr.not_isUnit (IsUnit.of_mul_eq_one z h1.symm)

end TotallyRamifiedLemmas

/-! ## Unramified extensions (named statements) -/

section Unramified

variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The residue field $k'$ of an intermediate field $K'$ of $L/K$, as a subring of the residue field $l$ of $L$: the
image in $l = B/\mathfrak p_L$ of the elements of $B$ that lie in $K'$. -/
noncomputable def residueRange (K' : IntermediateField K L) : Subring (ResidueField (integralClosure A L)) :=
  (K'.toSubalgebra.toSubring.comap (integralClosure A L).val.toRingHom).map (residue (integralClosure A L))

/-- **Proposition 7.50** (named statement). Let $K$ and its residue field $k$ be perfect, and let $L$ be an algebraic
extension of $K$ with residue field $l$. Sending a finite unramified extension $K' \subset L$ of $K$ to its residue
field $k' \subset l$ (`residueRange`) is a bijection onto the finite extensions of $k$ contained in $l$; moreover
(a) $K' \subset K'' \iff k' \subset k''$, and (b) $K'$ is Galois over $K$ iff $k'$ is Galois over $k$, in which case
reduction gives an isomorphism $\operatorname{Gal}(K'/K) \cong \operatorname{Gal}(k'/k)$. -/
@[kb "milne2020ant" "v3.08, Prop. 7.50, p. 127"]
structure Prop7_50 [PerfectField K] [PerfectField (ResidueField A)] [Algebra.IsAlgebraic K L] : Prop where
  exists_unique : ∀ k' : IntermediateField (ResidueField A) (ResidueField (integralClosure A L)),
    FiniteDimensional (ResidueField A) k' →
    ∃! K' : IntermediateField K L, FiniteDimensional K K' ∧ IsUnramifiedMilne A K K' ∧
      residueRange A K L K' = k'.toSubalgebra.toSubring
  residueRange_finite : ∀ K' : IntermediateField K L, FiniteDimensional K K' → IsUnramifiedMilne A K K' →
    ∃ k' : IntermediateField (ResidueField A) (ResidueField (integralClosure A L)),
      FiniteDimensional (ResidueField A) k' ∧ residueRange A K L K' = k'.toSubalgebra.toSubring
  le_iff : ∀ K' K'' : IntermediateField K L, FiniteDimensional K K' → IsUnramifiedMilne A K K' →
    FiniteDimensional K K'' → IsUnramifiedMilne A K K'' →
    (K' ≤ K'' ↔ residueRange A K L K' ≤ residueRange A K L K'')
  isGalois_iff : ∀ (K' : IntermediateField K L)
    (k' : IntermediateField (ResidueField A) (ResidueField (integralClosure A L))),
    FiniteDimensional K K' → IsUnramifiedMilne A K K' → residueRange A K L K' = k'.toSubalgebra.toSubring →
    (IsGalois K K' ↔ IsGalois (ResidueField A) k')
  galEquiv : ∀ (K' : IntermediateField K L)
    (k' : IntermediateField (ResidueField A) (ResidueField (integralClosure A L))),
    FiniteDimensional K K' → IsUnramifiedMilne A K K' → residueRange A K L K' = k'.toSubalgebra.toSubring →
    IsGalois K K' →
    ∃ φ : (K' ≃ₐ[K] K') ≃* (k' ≃ₐ[ResidueField A] k'),
      ∀ (σ : K' ≃ₐ[K] K') (b : integralClosure A L) (hb : (b : L) ∈ K') (b' : integralClosure A L),
        (b' : L) = (σ ⟨b, hb⟩ : L) → ∀ hmem : residue _ b ∈ k',
          ((φ σ ⟨residue _ b, hmem⟩ : k') : ResidueField (integralClosure A L)) = residue _ b'

/-- **Corollary 7.51** (named statement). In the situation of Proposition 7.50, there is an unramified extension $K_0$
of $K$ contained in $L$ that contains every other (finite) unramified extension of $K$ in $L$ ("unramified" for an
infinite $K_0$: all its finite subextensions are unramified). When $k$ is finite, $K_0$ is obtained from $K$ by
adjoining all roots of $1$ in $L$ of order prime to the characteristic of $k$. -/
@[kb "milne2020ant" "v3.08, Cor. 7.51, p. 128"]
structure Cor7_51 [PerfectField K] [PerfectField (ResidueField A)] [Algebra.IsAlgebraic K L] : Prop where
  exists_max : ∃ K₀ : IntermediateField K L,
    (∀ K' : IntermediateField K L, FiniteDimensional K K' → K' ≤ K₀ → IsUnramifiedMilne A K K') ∧
    ∀ K' : IntermediateField K L, FiniteDimensional K K' → IsUnramifiedMilne A K K' → K' ≤ K₀
  rootsOfUnity : Finite (ResidueField A) →
    let K₀ := IntermediateField.adjoin K
      {ζ : L | ∃ n : ℕ, 0 < n ∧ ¬ ringChar (ResidueField A) ∣ n ∧ ζ ^ n = 1}
    (∀ K' : IntermediateField K L, FiniteDimensional K K' → K' ≤ K₀ → IsUnramifiedMilne A K K') ∧
    ∀ K' : IntermediateField K L, FiniteDimensional K K' → IsUnramifiedMilne A K K' → K' ≤ K₀

end Unramified

/-- **Corollary 7.52** (named statement). Let $K$ and $k$ be perfect. The residue field of an algebraic closure
$K^{\mathrm{al}}$ of $K$ is an algebraic closure of $k$, and there is a subfield $K^{\mathrm{un}}$ of $K^{\mathrm{al}}$
such that a subfield $L$ of $K^{\mathrm{al}}$ finite over $K$ is unramified iff $L \subset K^{\mathrm{un}}$. -/
@[kb "milne2020ant" "v3.08, Cor. 7.52, p. 128"]
structure Cor7_52 [PerfectField K] [PerfectField (ResidueField A)] : Prop where
  isAlgClosed : IsAlgClosed (ResidueField (integralClosure A (AlgebraicClosure K)))
  isAlgebraic : Algebra.IsAlgebraic (ResidueField A) (ResidueField (integralClosure A (AlgebraicClosure K)))
  exists_un : ∃ Kun : IntermediateField K (AlgebraicClosure K),
    ∀ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L →
      (IsUnramifiedMilne A K L ↔ L ≤ Kun)

/-- **Remark 7.53** (named statement): reduction is an equivalence between the category of finite unramified
extensions of $K$ and that of finite separable extensions of $k$. Stated as: (full faithfulness) for finite unramified
$L, L'$ the reduction map $\operatorname{Hom}_K(L, L') \to \operatorname{Hom}_k(l, l')$, characterized by
$\bar\sigma(\bar b) = \overline{\sigma(b)}$, is a bijection; (essential surjectivity) every finite separable extension
$k'$ of $k$ is the residue field of a finite unramified extension of $K$. -/
@[kb "milne2020ant" "v3.08, Remark 7.53, p. 129"]
structure Remark7_53 [PerfectField K] [PerfectField (ResidueField A)] : Prop where
  hom_equiv : ∀ (L : Type v) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (L' : Type v) [Field L'] [Algebra K L'] [Algebra A L'] [IsScalarTower A K L'] [FiniteDimensional K L'],
    IsUnramifiedMilne A K L → IsUnramifiedMilne A K L' →
    ∃ Φ : (L →ₐ[K] L') ≃
        (ResidueField (integralClosure A L) →ₐ[ResidueField A] ResidueField (integralClosure A L')),
      ∀ (σ : L →ₐ[K] L') (b : integralClosure A L) (b' : integralClosure A L'), (b' : L') = σ b →
        Φ σ (residue _ b) = residue _ b'
  exists_lift : ∀ (k' : Type u) [Field k'] [Algebra (ResidueField A) k'] [FiniteDimensional (ResidueField A) k']
    [Algebra.IsSeparable (ResidueField A) k'],
    ∃ (L : Type v) (_ : Field L) (_ : Algebra K L) (_ : Algebra A L) (_ : IsScalarTower A K L),
      FiniteDimensional K L ∧ IsUnramifiedMilne A K L ∧
        Nonempty (ResidueField (integralClosure A L) ≃ₐ[ResidueField A] k')

/-- **Example 7.54** (named statement). Let $K$ be a local field of characteristic zero ($A$ complete with finite
residue field $k$ of order $q$). For each $n \ge 1$ there is an unramified extension $K_n$ of $K$ of degree $n$, unique
up to $K$-isomorphism; it is the splitting field of $X^{q^n} - X$, and $\operatorname{Gal}(K_n/K)$ is cyclic of order
$n$, generated by the Frobenius element $\sigma$, which is determined by $\sigma\beta \equiv \beta^q \pmod{\mathfrak p}$
for all $\beta \in B$. -/
@[kb "milne2020ant" "v3.08, Example 7.54, p. 129"]
structure Example7_54 [CharZero K] [Finite (ResidueField A)] : Prop where
  exists_unramified : ∀ n : ℕ, 0 < n →
    ∃ (L : Type v) (_ : Field L) (_ : Algebra K L) (_ : Algebra A L) (_ : IsScalarTower A K L),
      Module.finrank K L = n ∧ IsUnramifiedMilne A K L
  unique : ∀ (L : Type v) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (L' : Type v) [Field L'] [Algebra K L'] [Algebra A L'] [IsScalarTower A K L'],
    Module.finrank K L = Module.finrank K L' → 0 < Module.finrank K L →
    IsUnramifiedMilne A K L → IsUnramifiedMilne A K L' → Nonempty (L ≃ₐ[K] L')
  isSplittingField : ∀ (L : Type v) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L],
    0 < Module.finrank K L → IsUnramifiedMilne A K L →
    IsSplittingField K L (X ^ (Nat.card (ResidueField A) ^ Module.finrank K L) - X)
  frobenius : ∀ (L : Type v) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L],
    0 < Module.finrank K L → IsUnramifiedMilne A K L →
    IsGalois K L ∧ ∃ σ : L ≃ₐ[K] L,
      (∀ b b' : integralClosure A L, (b' : L) = σ b →
        b' - b ^ Nat.card (ResidueField A) ∈ maximalIdeal (integralClosure A L)) ∧
      orderOf σ = Module.finrank K L ∧ Subgroup.zpowers σ = ⊤ ∧
      ∀ τ : L ≃ₐ[K] L, (∀ b b' : integralClosure A L, (b' : L) = τ b →
        b' - b ^ Nat.card (ResidueField A) ∈ maximalIdeal (integralClosure A L)) → τ = σ

/-! ## Totally ramified extensions -/

section TotallyRamified

/- Milne's standing assumption from p. 127 on is that $K$ is perfect, so finite extensions of $K$ are separable; we
assume `Algebra.IsSeparable K L` (used for the finiteness of $B$ over $A$). -/
variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- **Proposition 7.55.** Let $L$ be a finite (separable, as $K$ is perfect in Milne's setting) extension of $K$. Then $L/K$ is totally ramified iff $L = K[\alpha]$ for
a root $\alpha$ of an Eisenstein polynomial. Milne's Eisenstein polynomial $a_0X^n + \dots + a_n$ over $K$ has
$|a_0| = 1$, $|a_i| < 1$ and $|a_n| = |\pi|$, i.e. it lies in $A[X]$ and is Eisenstein at the maximal ideal of $A$
(Mathlib's `Polynomial.IsEisensteinAt`, whose condition $a_n \notin \mathfrak m^2$ is $|a_n| = |\pi|$ in a discrete
valuation ring). -/
@[kb "milne2020ant" "v3.08, Prop. 7.55, p. 129"]
theorem prop_7_55 :
    IsTotallyRamifiedMilne A K L ↔
      ∃ α : L, IntermediateField.adjoin K {α} = ⊤ ∧
        ∃ f : A[X], f.IsEisensteinAt (maximalIdeal A) ∧ aeval α f = 0 := by
  have hfin := finite_integralClosure A K L
  constructor
  · exact exists_eisenstein_of_totally_ramified A K L
  · rintro ⟨α, hα, f, hf, h0⟩
    have h1 := finrank_le_ramIdx_of_eisenstein A K L α hα f hf h0
    have h2 := ef_eq_finrank_of_finite A K L
    have hn : 0 < Module.finrank K L := Module.finrank_pos
    have hf1 : 1 ≤ resDegMilne A L := by
      rcases Nat.eq_zero_or_pos (resDegMilne A L) with h | h
      · rw [h, mul_zero] at h2; omega
      · exact h
    have h3 : ramIdxMilne A L ≤ Module.finrank K L := by
      calc ramIdxMilne A L = ramIdxMilne A L * 1 := (mul_one _).symm
        _ ≤ ramIdxMilne A L * resDegMilne A L := Nat.mul_le_mul_left _ hf1
        _ = _ := h2
    exact le_antisymm h3 h1

/-- **Remark 7.56.** Let $L/K$ be finite (separable) and totally ramified, and let $\Pi$ be a prime element of $B$. Then
$B = A[\Pi]$. -/
@[kb "milne2020ant" "v3.08, Remark 7.56, p. 130"]
theorem remark_7_56 (hL : IsTotallyRamifiedMilne A K L) (ϖ : integralClosure A L)
    (hϖ : maximalIdeal (integralClosure A L) = Ideal.span {ϖ}) :
    Algebra.adjoin A {ϖ} = ⊤ := by
  have hfin := finite_integralClosure A K L
  exact adjoin_uniformizer_eq_top A K L hL ϖ hϖ

end TotallyRamified

end NumberFieldKB.MilneANT
