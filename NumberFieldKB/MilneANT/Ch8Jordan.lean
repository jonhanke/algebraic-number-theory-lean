import NumberFieldKB.MilneANT.Ch8Dedekind

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: Remark 8.40(d), second claim

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

An irreducible polynomial of degree $> 1$ over a number field has no root modulo infinitely many primes: its Galois
group acts transitively on $n > 1$ roots, so contains a fixed-point-free element (Jordan); by Chebotarev the primes
with that Frobenius class have positive density, and modulo such a prime (with $f \bmod \mathfrak p$ squarefree) the
factorization type has no part $1$ (`DedekindFrobenius`), so $f \bmod \mathfrak p$ has no root.
-/

open NumberField IsDedekindDomain Polynomial UniqueFactorizationMonoid
open NumberFieldKB.Chebotarev
open scoped Classical

namespace NumberFieldKB.MilneANT

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **Jordan's lemma**: a finite group acting transitively on a finite set with more than one point contains an
element without fixed points (Burnside's lemma: the average number of fixed points is one, but the identity fixes
more than one point). -/
theorem exists_fixedPoint_free {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [MulAction.IsPretransitive G X] [Finite X] (h : 1 < Nat.card X) : ∃ g : G, ∀ x : X, g • x ≠ x := by
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite X
  by_contra hcon
  push Not at hcon
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  haveI : Nonempty X := Nat.card_pos_iff.1 (by omega) |>.1
  haveI : Subsingleton (MulAction.orbitRel.Quotient G X) :=
    (MulAction.pretransitive_iff_subsingleton_quotient G X).1 inferInstance
  have hor : Fintype.card (MulAction.orbitRel.Quotient G X) = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.2 inferInstance) (Fintype.card_pos_iff.2 ⟨Quotient.mk'' (Classical.arbitrary X)⟩)
  rw [hor, one_mul] at hb
  have hlt : ∑ g : G, 1 < ∑ g : G, Fintype.card (MulAction.fixedBy X g) := by
    refine Finset.sum_lt_sum (fun g _ => ?_) ⟨1, Finset.mem_univ _, ?_⟩
    · obtain ⟨x, hx⟩ := hcon g
      exact Fintype.card_pos_iff.2 ⟨⟨x, hx⟩⟩
    · have : Fintype.card (MulAction.fixedBy X (1 : G)) = Fintype.card X := by
        simp
      rw [this]
      rw [Nat.card_eq_fintype_card] at h
      exact h
  rw [hb] at hlt
  simp at hlt

/-- The splitting field over `K` of the image of `f` in `K[X]`. -/
abbrev SFj {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X]) : Type :=
  (f.map (algebraMap (𝓞 K) K)).SplittingField

/-- The splitting field over a number field of a polynomial is a number field. -/
instance instNumberFieldSplittingFieldJ {K : Type} [Field K] [NumberField K] (g : K[X]) :
    NumberField g.SplittingField := by
  haveI : CharZero g.SplittingField := inferInstance
  haveI : FiniteDimensional ℚ g.SplittingField := Module.Finite.trans K _
  exact NumberField.mk

/-- In characteristic zero the splitting field of a polynomial over a number field is Galois. -/
instance instIsGaloisSplittingFieldJ {K : Type} [Field K] [NumberField K] (g : K[X]) :
    IsGalois K g.SplittingField :=
  { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField
    to_normal := SplittingField.instNormal g }

/-- The Galois group of an irreducible polynomial acts transitively on its roots in its splitting field (Mathlib's
`galAction_isPretransitive`, transported to the action `galActionAux` on the roots in the splitting field). -/
theorem isPretransitive_galActionAux {F : Type} [Field F] (p : F[X]) (hp : Irreducible p) :
    MulAction.IsPretransitive p.Gal (p.rootSet p.SplittingField) := by
  have H : ∀ x y : p.rootSet p.SplittingField, ∃ g : p.Gal, g • x = y := by
    intro x y
    haveI : Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩
    have h := Polynomial.Gal.galAction_isPretransitive p p.SplittingField hp
    obtain ⟨g, hg⟩ := h.exists_smul_eq (Polynomial.Gal.rootsEquivRootsAux p p.SplittingField x)
      (Polynomial.Gal.rootsEquivRootsAux p p.SplittingField y)
    refine ⟨g, ?_⟩
    apply (Polynomial.Gal.rootsEquivRootsAux p p.SplittingField).injective
    have hg2 : Polynomial.Gal.rootsEquivRootsAux p p.SplittingField
        (@SMul.smul _ _ (Polynomial.Gal.galActionAux p).toSMul g
          ((Polynomial.Gal.rootsEquivRootsAux p p.SplittingField).symm
            (Polynomial.Gal.rootsEquivRootsAux p p.SplittingField x))) =
        Polynomial.Gal.rootsEquivRootsAux p p.SplittingField y := hg
    rw [Equiv.symm_apply_apply] at hg2
    exact hg2
  exact ⟨H⟩

section Copied

variable {K : Type} [Field K] [NumberField K]

/-- The reduction of an integral polynomial splits in the splitting field of its image over `K`. -/
theorem splits_map_splittingFieldJ (f : (𝓞 K)[X]) :
    (f.map (algebraMap (𝓞 K) (f.map (algebraMap (𝓞 K) K)).SplittingField)).Splits := by
  have h := SplittingField.splits (f.map (algebraMap (𝓞 K) K))
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h

/-- A Frobenius element at a prime above `𝔭`, as a permutation of the roots, has the cycle type given by the
factorization of `f` modulo `𝔭` (this is `DedekindFrobenius` applied to the splitting field). -/
theorem frob_partitionJ (hD : DedekindFrobenius) (f : (𝓞 K)[X]) (hf : f.Monic)
    (𝔭 : HeightOneSpectrum (𝓞 K))
    (hsq : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)))
    (Q : 𝔭.asIdeal.primesOver (𝓞 (f.map (algebraMap (𝓞 K) K)).SplittingField)) :
    (galPerm (f.map (algebraMap (𝓞 K) K))
        (frobAt K (f.map (algebraMap (𝓞 K) K)).SplittingField 𝔭 Q)).partition.parts =
      (normalizedFactors (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))).map natDegree := by
  haveI := Q.2.1
  haveI := Q.2.2
  exact hD.partition_eq K _ f hf (splits_map_splittingFieldJ f) 𝔭 hsq Q.1 _
    (isArithFrobAt_frobAt K _ 𝔭 Q)

/-- If `f` is separable over `K`, then `f` modulo `𝔭` is squarefree for all but finitely many primes `𝔭`. -/
theorem finite_not_squarefreeJ (f : (𝓞 K)[X]) (hs : (f.map (algebraMap (𝓞 K) K)).Separable) :
    {𝔭 : HeightOneSpectrum (𝓞 K) |
      ¬ Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))}.Finite := by
  obtain ⟨a, b, hab⟩ := hs
  obtain ⟨d1, hd1, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (𝓞 K)) a
  obtain ⟨d2, hd2, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (𝓞 K)) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors (𝓞 K)) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors (𝓞 K)) b
  have hd : d1 * d2 ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hd1) (nonZeroDivisors.ne_zero hd2)
  have key : C d2 * A * f + C d1 * B * derivative f = C (d1 * d2) := by
    apply Polynomial.map_injective (algebraMap (𝓞 K) K) (IsFractionRing.injective _ _)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← derivative_map, hA, hB,
      ← algebraMap_smul K d1, ← algebraMap_smul K d2, smul_eq_C_mul, map_mul]
    linear_combination (C (algebraMap (𝓞 K) K d1) * C (algebraMap (𝓞 K) K d2)) * hab
  refine (Ideal.finite_factors (I := Ideal.span {d1 * d2}) ?_).subset ?_
  · simpa using hd
  intro 𝔭 h𝔭
  by_contra hnd
  apply h𝔭
  have hdn : d1 * d2 ∉ 𝔭.asIdeal := by
    intro h
    exact hnd ((Ideal.dvd_iff_le).2 ((Ideal.span_singleton_le_iff_mem _).2 h))
  apply Polynomial.Separable.squarefree
  have hu : algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2) ≠ 0 := by
    rwa [Ne, Ideal.algebraMap_residueField_eq_zero]
  have h2 := congrArg (Polynomial.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)) key
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← derivative_map] at h2
  refine ⟨C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2))⁻¹ *
      (C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField d2) * A.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)),
    C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2))⁻¹ *
      (C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField d1) * B.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)), ?_⟩
  linear_combination (C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2))⁻¹) * h2 +
    (by rw [← C_mul, inv_mul_cancel₀ hu, C_1] : C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2))⁻¹ *
      C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2)) = (1 : _[X]))

end Copied

/-- The cycle type (fixed points included) of an element of the Galois group, as a permutation of the roots. -/
def cycJ {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X]) (σ : SFj f ≃ₐ[K] SFj f) : Multiset ℕ :=
  (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts

/-- The cycle type is a class function. -/
theorem cycJ_eq_of_isConj {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X]) {σ τ : SFj f ≃ₐ[K] SFj f}
    (h : IsConj σ τ) : cycJ f σ = cycJ f τ := by
  have := Equiv.Perm.partition_eq_of_isConj.1
    (MonoidHom.map_isConj (MulAction.toPermHom (SFj f ≃ₐ[K] SFj f)
      ((f.map (algebraMap (𝓞 K) K)).rootSet (SFj f))) h)
  exact congrArg Nat.Partition.parts this

/-- A permutation has a fixed point if its cycle type, with fixed points included, has a part equal to `1`. -/
theorem exists_fixed_of_one_mem_parts {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    (h : 1 ∈ σ.partition.parts) : ∃ x, σ x = x := by
  rw [Equiv.Perm.parts_partition, Multiset.mem_add] at h
  rcases h with h | h
  · have := Equiv.Perm.two_le_of_mem_cycleType h
    omega
  · have hne : Fintype.card α - σ.support.card ≠ 0 := by
      intro h0
      rw [h0] at h
      simp at h
    by_contra hall
    push Not at hall
    apply hne
    have : σ.support = Finset.univ := Finset.eq_univ_of_forall fun x => by simpa using hall x
    rw [this, Finset.card_univ]
    simp

/-- **Remark 8.40(d)**, second claim, proved from `DedekindFrobenius`. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(d), p. 150"]
theorem remark_8_40d_second (hD : DedekindFrobenius) : Remark8_40d := by
  refine ⟨fun K _ _ f hf hirr hdeg hfin => ?_⟩
  have hgsep : (f.map (algebraMap (𝓞 K) K)).Separable := hirr.separable
  have hgdeg : (f.map (algebraMap (𝓞 K) K)).natDegree = f.natDegree := hf.natDegree_map _
  haveI : MulAction.IsPretransitive (f.map (algebraMap (𝓞 K) K)).Gal
      ((f.map (algebraMap (𝓞 K) K)).rootSet (SFj f)) :=
    isPretransitive_galActionAux _ hirr
  have hcard : 1 < Nat.card ((f.map (algebraMap (𝓞 K) K)).rootSet (SFj f)) := by
    rw [Nat.card_eq_fintype_card, Polynomial.card_rootSet_eq_natDegree hgsep (SplittingField.splits _), hgdeg]
    exact hdeg
  obtain ⟨σ, hσ⟩ := exists_fixedPoint_free (G := (f.map (algebraMap (𝓞 K) K)).Gal) hcard
  have hσ' : ∀ x, galPerm (f.map (algebraMap (𝓞 K) K)) σ x ≠ x := hσ
  let σ' : SFj f ≃ₐ[K] SFj f := σ
  set cl : ConjClasses (SFj f ≃ₐ[K] SFj f) := ConjClasses.mk σ' with hcl
  have hdens := thm_8_31_dirichlet K (SFj f) cl
  have hinf : (frobSet K (SFj f) cl).Infinite := by
    refine infinite_of_hasDirichletDensity ?_ hdens
    have h1 : 0 < Nat.card cl.carrier :=
      Nat.card_pos_iff.2 ⟨⟨⟨σ', ConjClasses.mem_carrier_iff_mk_eq.2 rfl⟩⟩, inferInstance⟩
    have h2 : 0 < Nat.card (SFj f ≃ₐ[K] SFj f) := Nat.card_pos
    positivity
  apply hinf
  refine ((hfin.union ((finite_not_squarefreeJ f hgsep).union
    (finite_compl_unramifiedPrimes K (SFj f)))).subset ?_)
  intro 𝔭 h𝔭
  by_contra hn
  simp only [Set.mem_union, not_or] at hn
  obtain ⟨hn1, hn2, hn3⟩ := hn
  have hsq : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)) := by
    by_contra h
    exact hn2 h
  apply hn1
  intro x hx
  obtain ⟨Q⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 (SFj f))))
  have hfp := frob_partitionJ hD f hf 𝔭 hsq Q
  have hconj : IsConj σ' (frobAt K (SFj f) 𝔭 Q) := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, ← frobClass_eq_mk_frobAt K _ 𝔭 Q]
    exact h𝔭.2.symm
  have hcyc : cycJ f (frobAt K (SFj f) 𝔭 Q) = cycJ f σ' := cycJ_eq_of_isConj f hconj.symm
  have h1mem : (1 : ℕ) ∈ (normalizedFactors (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))).map natDegree := by
    have hne : f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField) ≠ 0 :=
      (hf.map _).ne_zero
    refine Multiset.mem_map.2 ⟨X - C x, ?_, natDegree_X_sub_C x⟩
    rw [Polynomial.mem_normalizedFactors_iff hne]
    exact ⟨irreducible_X_sub_C x, monic_X_sub_C x, dvd_iff_isRoot.2 hx⟩
  rw [← hfp] at h1mem
  change 1 ∈ (cycJ f (frobAt K (SFj f) 𝔭 Q)) at h1mem
  rw [hcyc] at h1mem
  obtain ⟨y, hy⟩ := exists_fixed_of_one_mem_parts _ h1mem
  exact hσ' y hy

end

end NumberFieldKB.MilneANT
