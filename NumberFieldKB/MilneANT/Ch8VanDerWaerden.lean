import NumberFieldKB.MilneANT.Ch8GaloisGroups

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: Theorem 8.20 (van der Waerden)

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

Proves the named statement `Theorem8_20` (with the correction recorded there: $F_1$ is the irreducible factor of
$F(X,t)$ divisible by $X - \theta$).
-/

open Polynomial
open scoped Classical

namespace NumberFieldKB.MilneANT

noncomputable section

namespace VanDerWaerden

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ} (c : Fin n → E)

/-- The linear form $\theta = \sum_i c_i t_i$. -/
def theta : MvPolynomial (Fin n) E := ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i

/-- Permuting the variables of $\theta$ permutes the coefficients. -/
lemma rename_theta (τ : Equiv.Perm (Fin n)) :
    MvPolynomial.rename (R := E) τ (theta c) = ∑ j, MvPolynomial.C (c (τ⁻¹ j)) * MvPolynomial.X j := by
  simp only [theta, map_sum, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]
  rw [← Equiv.sum_comp τ (fun j => MvPolynomial.C (c (τ⁻¹ j)) * MvPolynomial.X j)]
  simp

/-- The coefficient of a variable in a permuted $\theta$. -/
lemma coeff_rename_theta (τ : Equiv.Perm (Fin n)) (k : Fin n) :
    (MvPolynomial.rename (R := E) τ (theta c)).coeff (Finsupp.single k 1) = c (τ⁻¹ k) := by
  rw [rename_theta, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Finsupp.single_left_inj]

/-- The permuted forms $\sigma_t \theta$ are pairwise distinct when the $c_i$ are. -/
lemma rename_theta_injective (hc : Function.Injective c) {τ τ' : Equiv.Perm (Fin n)}
    (h : MvPolynomial.rename (R := E) τ (theta c) = MvPolynomial.rename (R := E) τ' (theta c)) :
    τ = τ' := by
  have : ∀ k, τ⁻¹ k = τ'⁻¹ k := fun k => by
    apply hc
    rw [← coeff_rename_theta c τ k, ← coeff_rename_theta c τ' k, h]
  exact inv_injective (Equiv.ext this)

/-- A field automorphism acts on $\theta$ through the inverse permutation. -/
lemma map_theta (g : E →+* E) (γ : Equiv.Perm (Fin n)) (h : ∀ i, g (c i) = c (γ i)) :
    MvPolynomial.map g (theta c) = MvPolynomial.rename (R := E) (γ⁻¹ : Equiv.Perm (Fin n)) (theta c) := by
  rw [rename_theta]
  simp only [theta, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, h]
  simp

variable (K) in
/-- The permutations induced by automorphisms of `E` over `K` on the family `c`. -/
def stab : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {τ | ∃ g : E ≃ₐ[K] E, ∀ i, g (c i) = c (τ i)}
  mul_mem' := by
    rintro τ₁ τ₂ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    exact ⟨g₁ * g₂, fun i => by simp [h₁, h₂]⟩
  one_mem' := ⟨1, fun i => by simp⟩
  inv_mem' := by
    rintro τ ⟨g, h⟩
    refine ⟨g⁻¹, fun i => ?_⟩
    have := h (τ⁻¹ i)
    simp at this
    rw [← this]
    simp

variable (K) in
/-- $P = \prod_{\tau \in G'}(X - \tau_t\theta)$. -/
def P : (MvPolynomial (Fin n) E)[X] :=
  ∏ τ : stab K c, (X - C (MvPolynomial.rename (R := E) (τ : Equiv.Perm (Fin n)) (theta c)))

lemma monic_P : (P K c).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- `P` is invariant under automorphisms acting on the coefficients. -/
lemma map_P (hst : ∀ g : E ≃ₐ[K] E, ∃ γ : Equiv.Perm (Fin n), ∀ i, g (c i) = c (γ i))
    (g : E ≃ₐ[K] E) :
    (P K c).map (MvPolynomial.map (g : E →+* E)) = P K c := by
  obtain ⟨γ, hγ⟩ := hst g
  have hmem : γ⁻¹ ∈ stab K c := (stab K c).inv_mem ⟨g, hγ⟩
  have key : ∀ τ : stab K c,
      (X - C (MvPolynomial.rename (R := E) (τ : Equiv.Perm (Fin n)) (theta c))).map
        (MvPolynomial.map (g : E →+* E)) =
      X - C (MvPolynomial.rename (R := E) ((τ * ⟨γ⁻¹, hmem⟩ : stab K c) : Equiv.Perm (Fin n)) (theta c)) := by
    intro τ
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, MvPolynomial.map_rename,
      map_theta c _ γ hγ, MvPolynomial.rename_rename]
    rfl
  rw [P, Polynomial.map_prod, Finset.prod_congr rfl (fun τ _ => key τ)]
  exact Equiv.prod_comp (Equiv.mulRight (⟨γ⁻¹, hmem⟩ : stab K c))
    (fun τ : stab K c => X - C (MvPolynomial.rename (R := E) (τ : Equiv.Perm (Fin n)) (theta c)))

/-- `P` has coefficients in `K[t]`: it is the image of a monic polynomial over `K[t]`. -/
lemma P_lifts [IsGalois K E] [FiniteDimensional K E]
    (hst : ∀ g : E ≃ₐ[K] E, ∃ γ : Equiv.Perm (Fin n), ∀ i, g (c i) = c (γ i)) :
    ∃ Q : (MvPolynomial (Fin n) K)[X], Q.Monic ∧
      Q.map (MvPolynomial.map (algebraMap K E)) = P K c := by
  have hl : P K c ∈ Polynomial.lifts (MvPolynomial.map (algebraMap K E)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 ha
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro g
    have := congrArg (fun q => (q.coeff k).coeff m) (map_P c hst g)
    simpa [Polynomial.coeff_map, MvPolynomial.coeff_map] using this
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (monic_P c)
  exact ⟨Q, hQm, hQ⟩

/-- Renaming variables by `σ`, as a ring endomorphism of `E[t]`. -/
abbrev renE (σ : Equiv.Perm (Fin n)) : MvPolynomial (Fin n) E →+* MvPolynomial (Fin n) E :=
  (MvPolynomial.rename (R := E) σ).toRingHom

/-- `X - a` divides `X - b` only if `a = b`. -/
lemma X_sub_C_dvd_X_sub_C {A : Type*} [CommRing A] [IsDomain A] {a b : A}
    (h : (X - C a : A[X]) ∣ X - C b) : a = b := by
  rw [dvd_iff_isRoot] at h
  simpa [sub_eq_zero] using h

/-- Renaming the variables of `P` by `σ` fixes `P` exactly when `σ` is in the group `stab`. -/
lemma P_map_rename_iff (hc : Function.Injective c) (σ : Equiv.Perm (Fin n)) :
    (P K c).map (renE σ) = P K c ↔ σ ∈ stab K c := by
  constructor
  · intro h
    have h1 : X - C (MvPolynomial.rename (R := E) σ (theta c)) ∣ P K c := by
      rw [← h, P, Polynomial.map_prod]
      have := Finset.dvd_prod_of_mem
        (fun τ : stab K c => (X - C (MvPolynomial.rename (R := E) (τ : Equiv.Perm (Fin n)) (theta c))).map
          (renE σ)) (Finset.mem_univ (1 : stab K c))
      simpa [renE] using this
    rw [P, (prime_X_sub_C _).dvd_finsetProd_iff] at h1
    obtain ⟨τ, -, hτ⟩ := h1
    have := rename_theta_injective c hc (X_sub_C_dvd_X_sub_C hτ)
    rw [this]
    exact τ.2
  · intro hσ
    have key : ∀ τ : stab K c,
        (X - C (MvPolynomial.rename (R := E) (τ : Equiv.Perm (Fin n)) (theta c))).map (renE σ) =
        X - C (MvPolynomial.rename (R := E) ((⟨σ, hσ⟩ * τ : stab K c) : Equiv.Perm (Fin n)) (theta c)) := by
      intro τ
      simp only [renE, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.rename_rename]
      rfl
    rw [P, Polynomial.map_prod, Finset.prod_congr rfl (fun τ _ => key τ)]
    exact Equiv.prod_comp (Equiv.mulLeft (⟨σ, hσ⟩ : stab K c))
      (fun τ : stab K c => X - C (MvPolynomial.rename (R := E) (τ : Equiv.Perm (Fin n)) (theta c)))

/-- Automorphisms over `K` commute with the inclusion `K[t] → E[t]`. -/
lemma map_comp_map (g : E ≃ₐ[K] E) :
    (MvPolynomial.map (σ := Fin n) (g : E →+* E)).comp (MvPolynomial.map (algebraMap K E)) =
      MvPolynomial.map (algebraMap K E) := by
  refine RingHom.ext fun p => ?_
  have h : (g : E →+* E).comp (algebraMap K E) = algebraMap K E := RingHom.ext g.commutes
  rw [RingHom.comp_apply, MvPolynomial.map_map, h]

/-- A polynomial over `E[t]` fixed by the Galois group and divisible by `X - θ` is divisible by `P`. -/
lemma P_dvd (hc : Function.Injective c) {H : (MvPolynomial (Fin n) E)[X]}
    (hH : ∀ g : E ≃ₐ[K] E, H.map (MvPolynomial.map (g : E →+* E)) = H)
    (hθ : X - C (theta c) ∣ H) : P K c ∣ H := by
  apply Fintype.prod_dvd_of_isRelPrime
  · intro τ τ' hne
    show IsRelPrime _ _
    rw [(irreducible_X_sub_C _).isRelPrime_iff_not_dvd]
    intro hd
    exact hne (Subtype.ext (rename_theta_injective c hc (X_sub_C_dvd_X_sub_C hd)))
  · intro τ
    obtain ⟨g, hg⟩ := (stab K c).inv_mem τ.2
    have h1 := Polynomial.map_dvd (MvPolynomial.map (g : E →+* E)) hθ
    rw [hH g, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      map_theta c _ _ (fun i => hg i), inv_inv] at h1
    exact h1

/-- An irreducible polynomial `F₁` over a unique factorization domain `R` with a root `θ` in an extension
domain `S` divides every polynomial over `R` with root `θ` (Gauss's lemma, working in the fraction
fields). -/
lemma dvd_of_root_gen {R S : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
    [CommRing S] [IsDomain S] (ι : R →+* S) (hinj : Function.Injective ι) (θ : S)
    {F₁ Q : R[X]} (hirr : Irreducible F₁) (hF : X - C θ ∣ F₁.map ι)
    (hQr : X - C θ ∣ Q.map ι) : F₁ ∣ Q := by
  have hdeg : F₁.natDegree ≠ 0 := by
    intro h0
    have hne : F₁.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hirr.ne_zero
    have := Polynomial.natDegree_le_of_dvd hF hne
    rw [natDegree_X_sub_C, Polynomial.natDegree_map_eq_of_injective hinj, h0] at this
    omega
  have hprim : F₁.IsPrimitive := hirr.isPrimitive hdeg
  have hφinj : Function.Injective ((algebraMap S (FractionRing S)).comp ι) :=
    (IsFractionRing.injective S (FractionRing S)).comp hinj
  obtain ⟨ψ, hψ⟩ : ∃ ψ : FractionRing R →+* FractionRing S,
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap S (FractionRing S)).comp ι :=
    ⟨IsFractionRing.lift hφinj, RingHom.ext fun x => by
      simp only [RingHom.comp_apply]
      exact IsFractionRing.lift_algebraMap (A := R) (K := FractionRing R)
        (g := (algebraMap S (FractionRing S)).comp ι) hφinj x⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : (FractionRing R)[X] →+* FractionRing S,
      ∀ p, φ p = Polynomial.eval₂ ψ (algebraMap S (FractionRing S) θ) p :=
    ⟨Polynomial.eval₂RingHom ψ (algebraMap S (FractionRing S) θ), fun p => rfl⟩
  have hroot : ∀ p : R[X], X - C θ ∣ p.map ι → φ (p.map (algebraMap R (FractionRing R))) = 0 := by
    intro p hp
    have h0 : (p.map ι).eval θ = 0 := dvd_iff_isRoot.1 hp
    rw [hφ, Polynomial.eval₂_map, hψ, ← Polynomial.hom_eval₂, Polynomial.eval₂_eq_eval_map, h0,
      map_zero]
  have hirrL : Irreducible (F₁.map (algebraMap R (FractionRing R))) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map).1 hirr
  have hmax := PrincipalIdealRing.isMaximal_of_irreducible hirrL
  have hle : Ideal.span {F₁.map (algebraMap R (FractionRing R))} ≤ RingHom.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    exact hroot _ hF
  have heq := hmax.eq_of_le (RingHom.ker_ne_top φ) hle
  have hQmem : Q.map (algebraMap R (FractionRing R)) ∈
      Ideal.span {F₁.map (algebraMap R (FractionRing R))} := by
    have h := RingHom.mem_ker.2 (hroot _ hQr)
    rw [← heq] at h
    exact h
  exact hprim.dvd_of_fraction_map_dvd_fraction_map (K := FractionRing R)
    (Ideal.mem_span_singleton.1 hQmem)

/-- The core of van der Waerden's theorem, for any family `c` of elements of `E` permuted by the Galois
group. -/
theorem main_iff [IsGalois K E] [FiniteDimensional K E] (hc : Function.Injective c)
    (hst : ∀ g : E ≃ₐ[K] E, ∃ γ : Equiv.Perm (Fin n), ∀ i, g (c i) = c (γ i))
    {F₁ : (MvPolynomial (Fin n) K)[X]} (hirr : Irreducible F₁)
    (hθ : X - C (theta c) ∣ F₁.map (MvPolynomial.map (algebraMap K E)))
    (σ : Equiv.Perm (Fin n)) :
    F₁.map (MvPolynomial.rename (R := K) σ).toRingHom = F₁ ↔ σ ∈ stab K c := by
  set ι : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) E := MvPolynomial.map (algebraMap K E) with hι
  have hinj : Function.Injective ι := MvPolynomial.map_injective _ (algebraMap K E).injective
  obtain ⟨Q, hQm, hQP⟩ := P_lifts c hst
  have hθP : X - C (theta c) ∣ P K c := by
    have := Finset.dvd_prod_of_mem
      (fun τ : stab K c => X - C (MvPolynomial.rename (R := E) (τ : Equiv.Perm (Fin n)) (theta c)))
      (Finset.mem_univ (1 : stab K c))
    simpa [P] using this
  have h1 : F₁ ∣ Q := dvd_of_root_gen ι hinj _ hirr hθ (hQP ▸ hθP)
  have h2 : F₁.map ι ∣ P K c := hQP ▸ Polynomial.map_dvd ι h1
  have h3 : P K c ∣ F₁.map ι :=
    P_dvd c hc (fun g => by rw [Polynomial.map_map, map_comp_map]) hθ
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd h2 h3
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
  obtain ⟨r', hr', hrr⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hr
  have hU : (↑u : (MvPolynomial (Fin n) E)[X]).map (renE σ) = ↑u := by
    rw [← hru, hrr]
    simp [renE]
  have hcomm : (F₁.map (MvPolynomial.rename (R := K) σ).toRingHom).map ι = (F₁.map ι).map (renE σ) := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun p => MvPolynomial.map_rename _ _ p
  have key : (F₁.map (MvPolynomial.rename (R := K) σ).toRingHom = F₁) ↔
      (P K c).map (renE σ) = P K c := by
    rw [← (Polynomial.map_injective ι hinj).eq_iff, hcomm, ← hu, Polynomial.map_mul, hU]
    exact (mul_left_inj' u.ne_zero).symm
  rw [key]
  exact P_map_rename_iff c hc σ

end VanDerWaerden

open VanDerWaerden in
/-- **Theorem 8.20 holds** (van der Waerden). -/
@[kb "milne2020ant" "v3.08, Thm. 8.20, p. 144"]
theorem thm_8_20 : Theorem8_20 := by
  constructor
  intro K _ f hf n e F₁ θ F ι hirr _ hθ σ
  have : IsGalois K f.SplittingField := IsGalois.of_separable_splitting_field hf
  let c : Fin n → f.SplittingField := fun i => (e i : f.SplittingField)
  have hc : Function.Injective c := fun i j h => e.injective (Subtype.ext h)
  have hst : ∀ g : f.SplittingField ≃ₐ[K] f.SplittingField,
      ∃ γ : Equiv.Perm (Fin n), ∀ i, g (c i) = c (γ i) := by
    intro g
    have hmem : ∀ i, ∃ j, g (c i) = c j := by
      intro i
      have h := Polynomial.mem_rootSet.1 (e i).2
      refine ⟨e.symm ⟨g (c i), Polynomial.mem_rootSet.2 ⟨h.1, ?_⟩⟩, ?_⟩
      · have := Polynomial.aeval_algHom_apply (g : f.SplittingField →ₐ[K] f.SplittingField) (c i) f
        simp only [AlgEquiv.coe_toAlgHom] at this
        rw [this]
        have h2 := h.2
        simp only [c] at *
        rw [h2, map_zero]
      · simp [c]
    choose γf hγf using hmem
    have hinj : Function.Injective γf := fun i j h => by
      apply hc
      apply g.injective
      rw [hγf, hγf, h]
    exact ⟨Equiv.ofBijective γf (Finite.injective_iff_bijective.1 hinj), hγf⟩
  exact main_iff c hc hst hirr hθ σ

end

end NumberFieldKB.MilneANT
