import NumberFieldKB.Chebotarev.DensityTools
import NumberFieldKB.Chebotarev.FrobeniusPrimes
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Unramified.Locus

/-!
# Deuring's descent

The step shared by Step 2 (the cyclic case) and Step 3 (the general case) of the proof of the Chebotarev density theorem: for $\sigma\in G = \mathrm{Gal}(L/K)$ and
$E = L^{\langle\sigma\rangle}$, if the primes of $E$ with Frobenius $\sigma$ (for $L/E$) have Dirichlet density
$1/\operatorname{ord}\sigma$, then the primes of $K$ with Frobenius class $[\sigma]$ have density $1/|C_G(\sigma)|$.

*Proof.* Restrict the primes of $E$ to those of degree one over $K$ lying over primes of $K$ unramified in $L$ (density
unchanged: `hasDirichletDensity_inertiaDeg_eq_one`, finitely many ramified primes); by Deuring's count
(`deuring_count`) each unramified $\mathfrak p$ has $|C_G(\sigma)|/\operatorname{ord}\sigma$ of them above it if
$\mathrm{Frob}_{\mathfrak p} = [\sigma]$ and none otherwise; conclude with the descent lemma
`hasDirichletDensity_of_fiber_card`.
-/

open NumberField IsDedekindDomain Filter Topology Set

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Deuring

/-- A subset of a set of density zero has density zero. -/
theorem hasDirichletDensity_zero_of_subset {F : Type} [Field F] [NumberField F]
    {A Z : Set (HeightOneSpectrum (𝓞 F))} (hAZ : A ⊆ Z) (hZ : Z.HasDirichletDensity 0) :
    A.HasDirichletDensity 0 := by
  rw [hasDirichletDensity_iff] at hZ ⊢
  have hpos := eventually_primeIdealZetaSum_univ_pos (F := F)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hZ ?_ ?_
  · filter_upwards [hpos] with s hs
    exact div_nonneg (A.primeIdealZetaSum_nonneg s) hs.le
  · filter_upwards [hpos, self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
    exact div_le_div_of_nonneg_right (primeIdealZetaSum_mono hAZ hs1) hs.le

/-- Removing a set of density zero does not change the density. -/
theorem hasDirichletDensity_sdiff_of_zero {F : Type} [Field F] [NumberField F]
    {A B : Set (HeightOneSpectrum (𝓞 F))} {δ : ℝ} (hA : A.HasDirichletDensity δ)
    (hB : B.HasDirichletDensity 0) : (A \ B).HasDirichletDensity δ := by
  have h1 : (A ∩ B).HasDirichletDensity 0 := hasDirichletDensity_zero_of_subset inter_subset_right hB
  have h2 := HasDirichletDensity.diff inter_subset_left hA h1
  have h3 : A \ (A ∩ B) = A \ B := by
    ext x; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
  rwa [sub_zero, h3] at h2

/-- Only finitely many primes of a finite extension lie above a finite set of primes. -/
theorem finite_liesOver_of_finite (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] (Z : Set (HeightOneSpectrum (𝓞 K))) (hZ : Z.Finite) :
    {P : HeightOneSpectrum (𝓞 E) | ∃ 𝔭 ∈ Z, P.asIdeal.LiesOver 𝔭.asIdeal}.Finite := by
  have : {P : HeightOneSpectrum (𝓞 E) | ∃ 𝔭 ∈ Z, P.asIdeal.LiesOver 𝔭.asIdeal} =
      ⋃ 𝔭 ∈ Z, {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.LiesOver 𝔭.asIdeal} := by
    ext; simp
  rw [this]
  refine hZ.biUnion fun 𝔭 _ => ?_
  exact Set.Finite.subset ((IsDedekindDomain.primesOver_finite 𝔭.asIdeal (𝓞 E)).preimage
    (f := HeightOneSpectrum.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h))
    (fun P hP => ⟨P.isPrime, hP⟩)

/-- A prime of `E` over a prime of `K` unramified in `L` is unramified in `L`. -/
theorem mem_unramifiedPrimes_of_liesOver (K E L : Type) [Field K] [NumberField K] [Field E]
    [NumberField E] [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [IsGalois K L] [IsGalois E L]
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ unramifiedPrimes K L) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) : P ∈ unramifiedPrimes E L := by
  intro Q hQ hQE
  haveI : Q.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans Q P.asIdeal 𝔭.asIdeal
  haveI := h𝔭 Q hQ this
  exact Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 K) Q

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **Deuring's descent.** If the primes of $E = L^{\langle\sigma\rangle}$ with Frobenius $\sigma$ (for $L/E$) have
density $1/\operatorname{ord}\sigma$, then the primes of `K` with Frobenius class $[\sigma]$ have density
$1/|C_G(\sigma)|$. -/
theorem hasDirichletDensity_frobSet_of_fixedField (σ : Gal(L/K))
    (h : (frobSet (IntermediateField.fixedField (Subgroup.zpowers σ)) L
        (ConjClasses.mk (toFixedFieldGal K L σ))).HasDirichletDensity (1 / orderOf σ)) :
    (frobSet K L (ConjClasses.mk σ)).HasDirichletDensity
      (1 / Nat.card (Subgroup.centralizer ({σ} : Set Gal(L/K)))) := by
  classical
  set E := IntermediateField.fixedField (Subgroup.zpowers σ) with hE
  set S := frobSet E L (ConjClasses.mk (toFixedFieldGal K L σ)) with hS
  set D : Set (HeightOneSpectrum (𝓞 E)) := {P | P.asIdeal.inertiaDeg (𝓞 K) = 1} with hD
  set R : Set (HeightOneSpectrum (𝓞 E)) :=
    {P | ∃ 𝔭 ∈ (unramifiedPrimes K L)ᶜ, P.asIdeal.LiesOver 𝔭.asIdeal} with hR
  set T := (S \ Dᶜ) \ R with hTdef
  have hD1 : D.HasDirichletDensity 1 := hasDirichletDensity_inertiaDeg_eq_one (F := K) E
  have hDc : Dᶜ.HasDirichletDensity 0 := by simpa using HasDirichletDensity.compl hD1
  have hRfin : R.Finite := finite_liesOver_of_finite K E _ (finite_compl_unramifiedPrimes K L)
  have hT : T.HasDirichletDensity (1 / orderOf σ) :=
    hasDirichletDensity_sdiff_of_zero (hasDirichletDensity_sdiff_of_zero h hDc)
      (hasDirichletDensity_zero_of_finite hRfin)
  -- the count
  have hle : Subgroup.zpowers σ ≤ Subgroup.centralizer ({σ} : Set Gal(L/K)) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]
  have hdvd : orderOf σ ∣ Nat.card (Subgroup.centralizer ({σ} : Set Gal(L/K))) := by
    rw [← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le hle
  have hcpos : 0 < Nat.card (Subgroup.centralizer ({σ} : Set Gal(L/K))) := Nat.card_pos
  have hc : 0 < Nat.card (Subgroup.centralizer ({σ} : Set Gal(L/K))) / orderOf σ :=
    Nat.div_pos (Nat.le_of_dvd hcpos hdvd) (orderOf_pos σ)
  have hdeg : ∀ P ∈ T, P.asIdeal.inertiaDeg (𝓞 K) = 1 := fun P hP => by
    have := hP.1.2
    simpa [hD] using this
  have hfib : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      {P ∈ T | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard =
        if 𝔭 ∈ frobSet K L (ConjClasses.mk σ) then
          Nat.card (Subgroup.centralizer ({σ} : Set Gal(L/K))) / orderOf σ else 0 := by
    intro 𝔭
    by_cases h𝔭 : 𝔭 ∈ unramifiedPrimes K L
    · have key : {P ∈ T | P.asIdeal.LiesOver 𝔭.asIdeal} =
          {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.LiesOver 𝔭.asIdeal ∧
            P.asIdeal.inertiaDeg (𝓞 K) = 1 ∧
            frobClass _ L P = ConjClasses.mk (toFixedFieldGal K L σ)} := by
        ext P
        simp only [Set.mem_ofPred_eq, hTdef, hS, hD, hR, frobSet, Set.mem_sdiff, mem_compl_iff, not_exists,
          not_and, not_not]
        constructor
        · rintro ⟨⟨⟨⟨_, hf⟩, hd⟩, _⟩, hl⟩
          exact ⟨hl, hd, hf⟩
        · rintro ⟨hl, hd, hf⟩
          refine ⟨⟨⟨⟨mem_unramifiedPrimes_of_liesOver K E L h𝔭 hl, hf⟩, hd⟩, ?_⟩, hl⟩
          intro 𝔭' h𝔭' hl'
          exfalso
          apply h𝔭'
          have : 𝔭' = 𝔭 := HeightOneSpectrum.ext (hl'.over.trans hl.over.symm)
          rw [this]; exact h𝔭
      rw [key, deuring_count K L σ h𝔭]
      by_cases hf : frobClass K L 𝔭 = ConjClasses.mk σ
      · simp only [hf, ↓reduceIte, frobSet, Set.mem_ofPred_eq, h𝔭, and_self]
      · simp only [hf, ↓reduceIte, frobSet, Set.mem_ofPred_eq, and_false]
    · have key : {P ∈ T | P.asIdeal.LiesOver 𝔭.asIdeal} = ∅ := by
        exact Set.eq_empty_of_forall_notMem fun P hP => hP.1.2 ⟨𝔭, h𝔭, hP.2⟩
      rw [key, ncard_empty]
      simp only [frobSet, Set.mem_ofPred_eq, h𝔭, false_and, ↓reduceIte]
  have := hasDirichletDensity_of_fiber_card (F := K) E T (frobSet K L (ConjClasses.mk σ)) _ hc hdeg
    hfib hT
  convert this using 1
  rw [Nat.cast_div hdvd (by exact_mod_cast (orderOf_pos σ).ne')]
  have h1 : (orderOf σ : ℝ) ≠ 0 := by exact_mod_cast (orderOf_pos σ).ne'
  have h2 : (Nat.card (Subgroup.centralizer ({σ} : Set Gal(L/K))) : ℝ) ≠ 0 := by
    exact_mod_cast hcpos.ne'
  field_simp

end Deuring

end

end NumberFieldKB.Chebotarev
