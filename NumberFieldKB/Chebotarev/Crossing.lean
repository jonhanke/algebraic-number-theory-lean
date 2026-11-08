import NumberFieldKB.Chebotarev.Basic

/-!
# Field theory for the crossing argument

Step 2 of the proof of the Chebotarev density theorem (the cyclic case): $[L(\zeta_\ell):L] = \ell-1$ when $\ell\nmid d_L$, and the crossing field
$E = M^{\langle\gamma\rangle}$ over which $M$ is cyclotomic.
-/

open NumberField IsDedekindDomain Filter Topology Set

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Cyclic

open Polynomial in
/-- If the prime `ℓ` does not divide the discriminant of the number field `L`, the cyclotomic polynomial
$\Phi_\ell$ is irreducible over `L`. (The shifted polynomial $\Phi_\ell(X+1)$ is Eisenstein at a prime of
the ring of integers above `ℓ`, since `ℓ` is unramified; then apply Gauss's lemma.) -/
theorem irreducible_cyclotomic_of_not_dvd_discr (L : Type) [Field L] [NumberField L]
    (ℓ : ℕ) [hℓp : Fact ℓ.Prime] (hℓ : ¬ (ℓ : ℤ) ∣ NumberField.discr L) :
    Irreducible (cyclotomic ℓ L) := by
  have hp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓp.out
  have hpMax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L)
    (Ideal.span {(ℓ : ℤ)})
  have hQp : Q.IsPrime := hQ.isPrime
  have hmem : ((ℓ : ℤ) : 𝓞 L) ∈ Q := by
    have : (ℓ : ℤ) ∈ Q.under ℤ := by
      rw [← Ideal.LiesOver.over (p := Ideal.span {(ℓ : ℤ)}) (P := Q)]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  have hunr := (NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L) hp).mp hℓ Q hQp hmem
  have he : Q.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := ℤ)
  have he' : (Ideal.span {(ℓ : ℤ)}).ramificationIdx' Q = 1 := by
    have hne : Ideal.span {(ℓ : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (R := ℤ) (S := 𝓞 L) _ _ hne]
    exact he
  have hnot : ((ℓ : ℤ) : 𝓞 L) ∉ Q ^ 2 := by
    intro h
    apply (Ideal.ramificationIdx'_ne_one_iff (R := ℤ) (S := 𝓞 L) (p := Ideal.span {(ℓ : ℤ)})
      (P := Q) (by rw [Ideal.map_span]; simpa using hmem)).mpr
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; simpa using h
    exact he'
  set g : ℤ[X] := (cyclotomic ℓ ℤ).comp (X + 1) with hgdef
  have hg := cyclotomic_comp_X_add_one_isEisensteinAt ℓ
  have hgm : g.Monic := by
    rw [hgdef, show (X + 1 : ℤ[X]) = X + C 1 by simp]
    refine (cyclotomic.monic ℓ ℤ).comp (monic_X_add_C 1) fun h => ?_
    rw [natDegree_X_add_C] at h
    exact zero_ne_one h.symm
  have hg0 : g.coeff 0 = ℓ := by
    rw [coeff_zero_eq_eval_zero, hgdef, eval_comp]
    simp [eval_one_cyclotomic_prime]
  set f : (𝓞 L)[X] := g.map (algebraMap ℤ (𝓞 L)) with hfdef
  have hfm : f.Monic := hgm.map _
  have hfd : f.natDegree = g.natDegree := hgm.natDegree_map _
  have hgd : g.natDegree = ℓ - 1 := by
    rw [hgdef, natDegree_comp]
    simp [natDegree_cyclotomic, Nat.totient_prime hℓp.out]
  have hfe : f.IsEisensteinAt Q := by
    refine hfm.isEisensteinAt_of_mem_of_notMem hQp.ne_top (fun {n} hn => ?_) ?_
    · rw [hfdef, coeff_map]
      have := hg.mem (n := n) (by rw [← hfd]; exact hn)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
      rw [← hc]
      simp only [zsmul_eq_mul, map_mul, eq_intCast, Int.cast_id]
      exact Ideal.mul_mem_left _ _ (by simpa using hmem)
    · rw [hfdef, coeff_map, hg0]; simpa using hnot
  have hfirr : Irreducible f :=
    hfe.irreducible hQp hfm.isPrimitive (by rw [hfd, hgd]; have := hℓp.out.two_le; omega)
  have hf : f = taylor (1 : 𝓞 L) (cyclotomic ℓ (𝓞 L)) := by
    simp [hfdef, hgdef, taylor_apply, Polynomial.map_comp, map_cyclotomic]
  have hirr : Irreducible (cyclotomic ℓ (𝓞 L)) := by
    rw [hf] at hfirr
    exact (MulEquiv.irreducible_iff (f := (taylorEquiv (1 : 𝓞 L)).toMulEquiv)).mp hfirr
  have := ((cyclotomic.monic ℓ (𝓞 L)).irreducible_iff_irreducible_map_fraction_map (K := L)).mp hirr
  simpa [map_cyclotomic] using this

/-- **Linear disjointness from $\mathbb Q(\zeta_\ell)$**: if the prime $\ell$ does not divide
the discriminant of `L`, then $[L(\zeta_\ell):L] = \ell - 1$. (Every subfield $\ne\mathbb Q$ of $\mathbb Q(\zeta_\ell)$
is ramified at $\ell$, $\mathbb Q(\zeta_\ell)/\mathbb Q$ being totally ramified there, while $\ell$ is unramified in
`L`; so $L \cap \mathbb Q(\zeta_\ell) = \mathbb Q$.) The cyclic case needs only this for `L`: then
$\mathrm{Gal}(L(\zeta_\ell)/K) \to \mathrm{Gal}(L/K)\times\mathrm{Gal}(K(\zeta_\ell)/K)$ is injective between groups of
orders $n(\ell-1)$ and at most $n(\ell-1)$, hence bijective. -/
theorem finrank_cyclotomic_of_not_dvd_discr (L M : Type) [Field L] [NumberField L] [Field M] [Algebra L M]
    (ℓ : ℕ) [Fact ℓ.Prime] [IsCyclotomicExtension {ℓ} L M] (hℓ : ¬ (ℓ : ℤ) ∣ NumberField.discr L) :
    Module.finrank L M = ℓ - 1 := by
  rw [IsCyclotomicExtension.finrank (n := ℓ) M (irreducible_cyclotomic_of_not_dvd_discr L ℓ hℓ),
    Nat.totient_prime (Fact.out)]

/-- An automorphism of `M / K` restricts to the identity on a normal intermediate field `F` if and only if
it fixes `F` pointwise. -/
theorem restrictNormalHom_eq_one_iff_mem_fixingSubgroup {K M : Type} [Field K] [Field M] [Algebra K M]
    (F : IntermediateField K M) [Normal K F] (g : Gal(M/K)) :
    AlgEquiv.restrictNormalHom F g = 1 ↔ g ∈ IntermediateField.fixingSubgroup F := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := AlgEquiv.restrictNormal_commutes g F ⟨x, hx⟩
    have h' : g.restrictNormal F = 1 := h
    rw [h'] at this
    simpa using this.symm
  · intro h
    ext x
    have := AlgEquiv.restrictNormal_commutes g F x
    exact this.trans (h x x.2)

/-- **The crossing field.** Inside a Galois extension $M/K$, let `L` and `Z`
be Galois subextensions with $L \vee Z = M$ and $Z = K(\zeta_\ell)$ cyclotomic. If $\gamma \in \mathrm{Gal}(M/K)$
has $\operatorname{ord}(\gamma|_L) \mid \operatorname{ord}(\gamma|_Z)$, then $\langle\gamma\rangle$ meets
$\mathrm{Gal}(M/Z)$ trivially, so `M` is the cyclotomic extension $E(\zeta_\ell)$ of $E = M^{\langle\gamma\rangle}$. -/
theorem isCyclotomicExtension_fixedField_zpowers (K M : Type) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] (L Z : IntermediateField K M) [IsGalois K L] [IsGalois K Z]
    (hLZ : L ⊔ Z = ⊤) (ℓ : ℕ) [NeZero ℓ] [IsCyclotomicExtension {ℓ} K Z] (γ : Gal(M/K))
    (hγ : orderOf (AlgEquiv.restrictNormalHom L γ) ∣ orderOf (AlgEquiv.restrictNormalHom Z γ)) :
    IsCyclotomicExtension {ℓ} (IntermediateField.fixedField (Subgroup.zpowers γ)) M := by
  classical
  set E := IntermediateField.fixedField (Subgroup.zpowers γ) with hE
  have key : ∀ g ∈ Subgroup.zpowers γ, g ∈ IntermediateField.fixingSubgroup Z → g = 1 := by
    rintro g ⟨j, rfl⟩ hg
    have h1 : (AlgEquiv.restrictNormalHom Z γ) ^ j = 1 := by
      rw [← map_zpow]; exact (restrictNormalHom_eq_one_iff_mem_fixingSubgroup Z _).mpr hg
    have h3 : (orderOf (AlgEquiv.restrictNormalHom L γ) : ℤ) ∣ j :=
      (Int.natCast_dvd_natCast.mpr hγ).trans (orderOf_dvd_iff_zpow_eq_one.mpr h1)
    have h2 : (AlgEquiv.restrictNormalHom L γ) ^ j = 1 := orderOf_dvd_iff_zpow_eq_one.mp h3
    have hgL : γ ^ j ∈ IntermediateField.fixingSubgroup L :=
      (restrictNormalHom_eq_one_iff_mem_fixingSubgroup L _).mp (by rw [map_zpow]; exact h2)
    have h4 : γ ^ j ∈ IntermediateField.fixingSubgroup (L ⊔ Z) := by
      rw [IntermediateField.fixingSubgroup_sup]; exact ⟨hgL, hg⟩
    rw [hLZ, IntermediateField.fixingSubgroup_top] at h4
    exact h4
  have hEZ : E ⊔ Z = ⊤ := by
    have h5 : IntermediateField.fixingSubgroup (E ⊔ Z) = ⊥ := by
      rw [IntermediateField.fixingSubgroup_sup, hE, IntermediateField.fixingSubgroup_fixedField]
      rw [eq_bot_iff]
      intro g hg
      exact key g hg.1 hg.2
    rw [← IsGalois.fixedField_fixingSubgroup (E ⊔ Z), h5, IntermediateField.fixedField_bot]
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {ℓ}) K Z
      (Set.mem_singleton ℓ) (NeZero.ne ℓ)
    exact ⟨Z.val r, hr.map_of_injective Z.val.injective⟩
  · have hZ : Z ≤ IntermediateField.adjoin K {b : M | b ^ ℓ = 1} := by
      intro z hz
      have hZc : IsCyclotomicExtension {ℓ} K Z := inferInstance
      have h := ((IsCyclotomicExtension.iff_singleton ℓ K Z).mp hZc).2 ⟨z, hz⟩
      have h' : (Z.val ⟨z, hz⟩) ∈ (Algebra.adjoin K {b : Z | b ^ ℓ = 1}).map Z.val :=
        ⟨_, h, rfl⟩
      rw [AlgHom.map_adjoin] at h'
      refine (IntermediateField.algebra_adjoin_le_adjoin K _) (Algebra.adjoin_mono ?_ h')
      rintro _ ⟨b, hb, rfl⟩
      simpa [← map_pow] using congrArg Z.val (show b ^ ℓ = 1 from hb)
    set T : IntermediateField E M := IntermediateField.adjoin E {b : M | b ^ ℓ = 1} with hTdef
    have hT : T = ⊤ := by
      have hle : E ⊔ Z ≤ T.restrictScalars K := by
        refine sup_le (fun x hx => ?_) (hZ.trans (IntermediateField.adjoin_le_iff.mpr ?_))
        · exact T.algebraMap_mem ⟨x, hx⟩
        · exact fun b hb => IntermediateField.subset_adjoin E _ hb
      rw [hEZ] at hle
      exact IntermediateField.restrictScalars_eq_top_iff.mp (top_le_iff.mp hle)
    intro x
    have hx : x ∈ T := by rw [hT]; trivial
    have := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := E)
      (S := {b : M | b ^ ℓ = 1}) (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)
    rw [← this]
    exact hx

end Cyclic

end

end NumberFieldKB.Chebotarev
