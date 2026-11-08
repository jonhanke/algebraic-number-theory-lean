import NumberFieldKB.MilneCFT.Ch7.Basic

/-!
# Milne, *Class Field Theory*, Chapter VII §4: Lemma 4.2

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).
-/

open IsDedekindDomain NumberField NumberFieldKB.HilbertClassField
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K]

/-- The prime $v$ as an invertible fractional ideal. -/
def primeUnit (v : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- If the primes in `S` generate the class group, every finitely supported exponent vector is realised,
away from `S`, by the valuations of a principal ideal. -/
theorem exists_principal_count (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤)
    (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    ∃ c : Kˣ, ∀ v ∉ S,
      FractionalIdeal.count K v (toPrincipalIdeal (𝓞 K) K c : FractionalIdeal (𝓞 K)⁰ K) = n v := by
  let f := QuotientGroup.mk' (toPrincipalIdeal (𝓞 K) K).range
  have h1 : (Subgroup.closure (primeUnit K '' S)).map f = ⊤ := by
    rw [MonoidHom.map_closure, Set.image_image]
    have : (fun v => f (primeUnit K v)) = fun v => (ClassGroup.equiv K) (primeClass K v) := by
      funext v
      simp only [primeClass, ClassGroup.equiv_mk0]
      rfl
    rw [this, ← Set.image_image (ClassGroup.equiv K) (fun v => primeClass K v) S]
    have h2 := MonoidHom.map_closure (ClassGroup.equiv K).toMonoidHom
      ((fun v => primeClass K v) '' S)
    have h3 : (⊤ : Subgroup (ClassGroup (𝓞 K))).map (ClassGroup.equiv K).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ (ClassGroup.equiv K).toEquiv.surjective
    rw [hS, h3] at h2
    exact h2.symm
  let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := n.prod (fun v k => primeUnit K v ^ k)
  have hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      n.prod (fun v k => (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ k) := by
    simp only [J, Finsupp.prod, Units.coe_prod, Units.val_zpow_eq_zpow_val]
    rfl
  have hmem : f J ∈ (Subgroup.closure (primeUnit K '' S)).map f := by rw [h1]; trivial
  obtain ⟨P, hP, hPJ⟩ := Subgroup.mem_map.mp hmem
  have hq : P⁻¹ * J ∈ (toPrincipalIdeal (𝓞 K) K).range := by
    rw [← QuotientGroup.eq]; exact hPJ
  obtain ⟨c, hc⟩ := hq
  have hJe : J = P * toPrincipalIdeal (𝓞 K) K c := by rw [hc]; group
  have hP0' : ∀ Q ∈ Subgroup.closure (primeUnit K '' S), ∀ v ∉ S,
      FractionalIdeal.count K v (Q : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    intro Q hQ v hv
    induction hQ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      have : w ≠ v := fun h => hv (h ▸ hw)
      exact FractionalIdeal.count_maximal_coprime K v this
    | one => simp [FractionalIdeal.count_one]
    | mul x y _ _ hx hy =>
      rw [Units.val_mul, FractionalIdeal.count_mul K v x.ne_zero y.ne_zero, hx, hy]; rfl
    | inv x _ hx =>
      have : ((x⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
          ((x : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
        rw [← mul_eq_one_iff_eq_inv₀ x.ne_zero]; exact x.inv_mul
      rw [this, FractionalIdeal.count_inv, hx]; rfl
  refine ⟨c, fun v hv => ?_⟩
  have := FractionalIdeal.count_finsuppProd K v n
  rw [← hJ, hJe, Units.val_mul, FractionalIdeal.count_mul K v P.ne_zero (toPrincipalIdeal (𝓞 K) K c).ne_zero,
    hP0' P hP v hv, zero_add] at this
  exact this

/-- **Lemma 4.2** (Milne, *CFT*, Chapter VII, p. 210): if the set $S$ of finite primes of $K$ contains a set of
generators of the ideal class group, then $\mathbb I_K = K^\times\cdot\mathbb I_S$ (all infinite primes are in $S$;
Milne takes $S$ finite, which is not needed). -/
@[kb "milne2020cft" "Ch. VII, Lemma 4.2"]
theorem lemma_4_2 (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤) :
    IdeleGroup.principalSubgroup (𝓞 K) K ⊔ idelesS S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  let a : (FiniteAdeleRing (𝓞 K) K)ˣ := (MulEquiv.prodUnits x).2
  have hfin : (fun v => Valued.v ((a : FiniteAdeleRing (𝓞 K) K) v)).HasFiniteMulSupport :=
    FiniteAdeleRing.hasFiniteMulSupport_valued a
  have hxv : ∀ v, ((x : AdeleRing (𝓞 K) K).2 v) = (a : FiniteAdeleRing (𝓞 K) K) v := fun v => rfl
  have hsupp : (Function.support fun v => -WithZero.log (Valued.v ((x : AdeleRing (𝓞 K) K).2 v))).Finite := by
    refine hfin.subset ?_
    intro v hv
    simp only [Function.mem_support, ne_eq, neg_eq_zero] at hv
    simp only [Function.mem_mulSupport, ne_eq]
    intro h
    apply hv
    rw [hxv, h]; simp
  obtain ⟨c, hc⟩ := exists_principal_count K S hS (Finsupp.ofSupportFinite _ hsupp)
  have hy : (IdeleGroup.unitEmbedding (𝓞 K) K c⁻¹ * x) ∈ idelesS S := by
    intro v hv
    have h1 := hc v hv
    rw [Finsupp.ofSupportFinite_coe] at h1
    have h2 := NumberFieldKB.MilneCFT.valuation_eq_exp_neg_count v c
    rw [h1] at h2
    have hne : Valued.v ((x : AdeleRing (𝓞 K) K).2 v) ≠ 0 := by
      rw [hxv]
      exact (Valuation.ne_zero_iff _).mpr ((FiniteAdeleRing.isUnit_iff.mp a.isUnit).1 v)
    change Valued.v ((IdeleGroup.unitEmbedding (𝓞 K) K c⁻¹ : AdeleRing (𝓞 K) K).2 v *
      (x : AdeleRing (𝓞 K) K).2 v) = 1
    have h3 : (IdeleGroup.unitEmbedding (𝓞 K) K c⁻¹ : AdeleRing (𝓞 K) K).2 v =
        ((c⁻¹ : Kˣ) : K) := rfl
    rw [h3, map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Units.val_inv_eq_inv_val,
      map_inv₀, h2]
    conv_lhs => rw [← WithZero.exp_log hne]
    rw [← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have : x = IdeleGroup.unitEmbedding (𝓞 K) K c * (IdeleGroup.unitEmbedding (𝓞 K) K c⁻¹ * x) := by
    rw [← mul_assoc, ← map_mul]; simp
  rw [this]
  exact Subgroup.mul_mem_sup ⟨c, rfl⟩ hy

end NumberFieldKB.MilneCFT.Ch7
