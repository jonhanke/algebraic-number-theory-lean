import NumberFieldKB.MilneANT.Ch8Chebotarev
import NumberFieldKB.MilneANT.Ch8Density

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: applications of the Chebotarev density theorem

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Galois extensions $L, M$ of $K$ are taken as intermediate fields of a common number field $\Omega$ (Milne works in an
algebraic closure; one can take $\Omega = LM$). All results here are proved unconditionally, from Chebotarev's
theorem with Dirichlet density (`thm_8_31_dirichlet`).

* **Theorem 8.38** (`thm_8_38`), with the step `splitPrimes_sup` ($\mathrm{Spl}(LM/K) = \mathrm{Spl}(L/K)\cap
  \mathrm{Spl}(M/K)$, also the sentence after 8.17).
* **Corollary 8.39** (`cor_8_39`).
* **Remark 8.40(a)** (`remark_8_40a_finite`, `remark_8_40a_dirichlet`, `remark_8_40a_natural`), **(b)**
  (`remark_8_40b`, existence of the bound).
-/

open NumberField IsDedekindDomain
open NumberFieldKB.Chebotarev

namespace NumberFieldKB.MilneANT

noncomputable section

open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω] [Algebra K Ω]

/-- Primes of `K` that split completely in `M` split completely in any subfield `L` of `M` (multiplicativity of the
ramification index and inertia degree in towers). -/
theorem splitPrimes_subset_of_tower (L M : Type) [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] :
    splitPrimes K M ⊆ splitPrimes K L := by
  intro 𝔭 h𝔭 Q
  obtain ⟨R, -, hR, hRo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q.1 (⊥ : Ideal (𝓞 M))
    (by
      intro x hx
      have : x = 0 := (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 M)) (by simpa using hx)
      simp [this])
  haveI := hR
  haveI : R.LiesOver Q.1 := ⟨hRo.symm⟩
  haveI : R.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans R Q.1 𝔭.asIdeal
  haveI := Q.2.1
  haveI := Q.2.2
  obtain ⟨he, hf⟩ := h𝔭 ⟨R, hR, inferInstance⟩
  have he' := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 L) (T := 𝓞 M) Q.1 R
  have hf' := Ideal.inertiaDeg_tower (R := 𝓞 K) (S := 𝓞 L) (T := 𝓞 M) Q.1 R
  rw [he] at he'
  rw [hf] at hf'
  exact ⟨Nat.eq_one_of_mul_eq_one_right he'.symm, Nat.eq_one_of_mul_eq_one_right hf'.symm⟩

/-- Primes that split completely in a larger intermediate field split completely in a smaller one. -/
theorem splitPrimes_antitone {L M : IntermediateField K Ω} (h : L ≤ M) :
    splitPrimes K ↥M ⊆ splitPrimes K ↥L := by
  letI : Algebra L M := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact splitPrimes_subset_of_tower L M

open scoped Pointwise in
/-- For a Galois extension `F/K` of number fields and a prime `Q` of `F` above `𝔭`, the decomposition group of `Q` has
order `e f` (ramification index times inertia degree). -/
theorem card_stabilizer_eq_ramificationIdx_mul_inertiaDeg (F : Type) [Field F] [NumberField F] [Algebra K F]
    [IsGalois K F] (𝔭 : HeightOneSpectrum (𝓞 K)) (Q : 𝔭.asIdeal.primesOver (𝓞 F)) :
    Nat.card (MulAction.stabilizer Gal(F/K) Q.1) =
      Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K) := by
  haveI := Q.2.1
  haveI := Q.2.2
  haveI := finite_quotient_of_ne_bot Q.1 (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1)
  have hu : Q.1.under (𝓞 K) = 𝔭.asIdeal := (Ideal.LiesOver.over (P := Q.1) (p := 𝔭.asIdeal)).symm
  haveI : Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 F) 𝔭.asIdeal :=
    hasSep_congr hu (hasSeparableResidueFieldsAt_under Q.1)
  haveI : 𝔭.asIdeal.IsPrime := 𝔭.isPrime
  rw [Ideal.card_stabilizer_eq (G := Gal(F/K)) 𝔭.asIdeal Q.1,
    Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal Q.1 Gal(F/K),
    Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal Q.1 Gal(F/K)]

open scoped Pointwise in
/-- Restriction to a Galois subextension maps the decomposition group of `R` into that of `R ∩ L`. -/
theorem restrictNormalHom_mem_stabilizer (L N : Type) [Field L] [NumberField L] [Field N] [NumberField N]
    [Algebra K L] [Algebra K N] [Algebra L N] [IsScalarTower K L N] [IsGalois K L] [IsGalois K N]
    (R : Ideal (𝓞 N)) {σ : Gal(N/K)} (hσ : σ ∈ MulAction.stabilizer Gal(N/K) R) :
    AlgEquiv.restrictNormalHom L σ ∈ MulAction.stabilizer Gal(L/K) (R.under (𝓞 L)) := by
  have hc : ∀ (g : Gal(N/K)) (b : 𝓞 L),
      algebraMap (𝓞 L) (𝓞 N) (AlgEquiv.restrictNormalHom L g • b) = g • algebraMap (𝓞 L) (𝓞 N) b := by
    intro g b
    apply Subtype.ext
    change algebraMap L N ((AlgEquiv.restrictNormalHom L g) (b : L)) = g (algebraMap L N (b : L))
    exact AlgEquiv.restrictNormal_commutes g L (b : L)
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
    ← map_inv, hc, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, MulAction.mem_stabilizer_iff.mp hσ]

/-- $\mathrm{Spl}(LM/K) = \mathrm{Spl}(L/K) \cap \mathrm{Spl}(M/K)$ for Galois $L, M$ (step of the proof of
Theorem 8.38, Milne p. 149; also the sentence after 8.17, p. 142). -/
@[kb "milne2020ant" "v3.08, Thm. 8.38 (proof), p. 149; sentence after 8.17, p. 142"]
theorem splitPrimes_sup (L M : IntermediateField K Ω) [IsGalois K L] [IsGalois K M] :
    splitPrimes K ↥(L ⊔ M) = splitPrimes K L ∩ splitPrimes K M := by
  letI : Algebra L ↥(L ⊔ M) := (IntermediateField.inclusion le_sup_left).toAlgebra
  letI : Algebra M ↥(L ⊔ M) := (IntermediateField.inclusion le_sup_right).toAlgebra
  haveI : IsScalarTower K L ↥(L ⊔ M) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K M ↥(L ⊔ M) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply Set.Subset.antisymm
  · exact fun 𝔭 h => ⟨splitPrimes_antitone le_sup_left h, splitPrimes_antitone le_sup_right h⟩
  · rintro 𝔭 ⟨hL, hM⟩ R
    haveI := R.2.1
    haveI := R.2.2
    let QL : 𝔭.asIdeal.primesOver (𝓞 L) := ⟨R.1.under (𝓞 L), inferInstance, inferInstance⟩
    let QM : 𝔭.asIdeal.primesOver (𝓞 M) := ⟨R.1.under (𝓞 M), inferInstance, inferInstance⟩
    have hL1 : Nat.card (MulAction.stabilizer Gal(L/K) QL.1) = 1 := by
      rw [card_stabilizer_eq_ramificationIdx_mul_inertiaDeg L 𝔭 QL, (hL QL).1, (hL QL).2]
    have hM1 : Nat.card (MulAction.stabilizer Gal(M/K) QM.1) = 1 := by
      rw [card_stabilizer_eq_ramificationIdx_mul_inertiaDeg M 𝔭 QM, (hM QM).1, (hM QM).2]
    obtain ⟨hLs, -⟩ := Nat.card_eq_one_iff_unique.mp hL1
    obtain ⟨hMs, -⟩ := Nat.card_eq_one_iff_unique.mp hM1
    have hN1 : Nat.card (MulAction.stabilizer Gal(↥(L ⊔ M)/K) R.1) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
      apply IntermediateField.restrictNormalHomSupProd_injective L M
      refine Prod.ext ?_ ?_
      · exact congrArg Subtype.val (hLs.elim
          ⟨_, restrictNormalHom_mem_stabilizer L _ R.1 a.2⟩
          ⟨_, restrictNormalHom_mem_stabilizer L _ R.1 b.2⟩)
      · exact congrArg Subtype.val (hMs.elim
          ⟨_, restrictNormalHom_mem_stabilizer M _ R.1 a.2⟩
          ⟨_, restrictNormalHom_mem_stabilizer M _ R.1 b.2⟩)
    rw [card_stabilizer_eq_ramificationIdx_mul_inertiaDeg _ 𝔭 R] at hN1
    exact ⟨Nat.eq_one_of_mul_eq_one_right hN1, Nat.eq_one_of_mul_eq_one_left hN1⟩

/-- If the primes splitting completely in `M` but not in `L` form a set of Dirichlet density zero, then `L ⊆ M`
(comparison of the densities $1/[M:K]$ and $1/[LM:K]$ of Corollary 8.32). -/
theorem le_of_density_sdiff_zero (L M : IntermediateField K Ω) [IsGalois K L] [IsGalois K M]
    (h : (splitPrimes K M \ splitPrimes K L).HasDirichletDensity 0) : L ≤ M := by
  have hsup := splitPrimes_sup L M
  have hT : splitPrimes K ↥(L ⊔ M) ⊆ splitPrimes K M := by
    rw [hsup]; exact Set.inter_subset_right
  have hd := HasDirichletDensity.diff hT (cor_8_32_dirichlet K M) (cor_8_32_dirichlet K ↥(L ⊔ M))
  have hset : splitPrimes K M \ splitPrimes K ↥(L ⊔ M) = splitPrimes K M \ splitPrimes K L := by
    rw [hsup, Set.sdiff_inter_self_eq_sdiff]
  rw [hset] at hd
  have heq := HasDirichletDensity.unique hd h
  have hM : (0 : ℝ) < Module.finrank K M := by exact_mod_cast Module.finrank_pos
  have hLM : (0 : ℝ) < Module.finrank K ↥(L ⊔ M) := by exact_mod_cast Module.finrank_pos
  have hrank : Module.finrank K M = Module.finrank K ↥(L ⊔ M) := by
    have : (1 : ℝ) / Module.finrank K M = 1 / Module.finrank K ↥(L ⊔ M) := by linarith
    rw [one_div, one_div, inv_inj] at this
    exact_mod_cast this
  have hMeq : M = L ⊔ M := IntermediateField.eq_of_le_of_finrank_eq le_sup_right hrank
  exact hMeq ▸ le_sup_left

/-- **Theorem 8.38** (proved, unconditionally, from Chebotarev with Dirichlet density): for Galois extensions $L$ and
$M$ of $K$, $L \subseteq M$ iff $\mathrm{Spl}(L/K) \supseteq \mathrm{Spl}(M/K)$. -/
@[kb "milne2020ant" "v3.08, Thm. 8.38, p. 149"]
theorem thm_8_38 (L M : IntermediateField K Ω) [IsGalois K L] [IsGalois K M] :
    L ≤ M ↔ splitPrimes K M ⊆ splitPrimes K L := by
  refine ⟨splitPrimes_antitone, fun h => le_of_density_sdiff_zero L M ?_⟩
  rw [Set.sdiff_eq_empty.mpr h]
  exact hasDirichletDensity_zero_of_finite Set.finite_empty

/-- **Corollary 8.39** (proved): Galois extensions $L, M$ of $K$ are equal iff $\mathrm{Spl}(M/K) = \mathrm{Spl}(L/K)$. -/
@[kb "milne2020ant" "v3.08, Cor. 8.39, p. 150"]
theorem cor_8_39 (L M : IntermediateField K Ω) [IsGalois K L] [IsGalois K M] :
    L = M ↔ splitPrimes K M = splitPrimes K L := by
  refine ⟨fun h => by rw [h], fun h => le_antisymm ?_ ?_⟩
  · exact (thm_8_38 L M).mpr h.le
  · exact (thm_8_38 M L).mpr h.ge

/-- **Remark 8.40(a), Dirichlet density form** (proved): Galois extensions $L, M$ of $K$ are equal if
$\mathrm{Spl}(M/K)$ and $\mathrm{Spl}(L/K)$ differ by a set of Dirichlet density zero. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(a) (Dirichlet density), p. 150"]
theorem remark_8_40a_dirichlet (L M : IntermediateField K Ω) [IsGalois K L] [IsGalois K M]
    (h : (symmDiff (splitPrimes K M) (splitPrimes K L)).HasDirichletDensity 0) : L = M := by
  refine le_antisymm (le_of_density_sdiff_zero L M ?_) (le_of_density_sdiff_zero M L ?_)
  · refine hasDirichletDensity_zero_of_subset ?_ h
    rw [symmDiff_def]
    exact Set.subset_union_left
  · rw [symmDiff_comm] at h
    refine hasDirichletDensity_zero_of_subset ?_ h
    rw [symmDiff_def]
    exact Set.subset_union_left

/-- **Remark 8.40(a)** (proved): Galois extensions $L, M$ of $K$ are equal if $\mathrm{Spl}(M/K)$ and
$\mathrm{Spl}(L/K)$ differ by at worst a finite set of primes. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(a), p. 150"]
theorem remark_8_40a_finite (L M : IntermediateField K Ω) [IsGalois K L] [IsGalois K M]
    (h : (symmDiff (splitPrimes K M) (splitPrimes K L)).Finite) : L = M :=
  remark_8_40a_dirichlet L M (hasDirichletDensity_zero_of_finite h)

/-- **Remark 8.40(a)** (proved): Galois extensions $L, M$ of $K$ are equal if $\mathrm{Spl}(M/K)$ and
$\mathrm{Spl}(L/K)$ differ by at worst a set of primes of natural density zero. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(a), p. 150"]
theorem remark_8_40a_natural (L M : IntermediateField K Ω) [IsGalois K L] [IsGalois K M]
    (h : HasNaturalDensity (symmDiff (splitPrimes K M) (splitPrimes K L)) 0) : L = M :=
  remark_8_40a_dirichlet L M h.hasDirichletDensity

/-- **Remark 8.40(b)**, existence part (proved from Theorem 8.38): for Galois $L, M$ over $K$ there is a bound $B$
such that, if every prime of norm at most $B$ that splits in $M$ also splits in $L$, then $L \subseteq M$. Milne's point,
that $B$ can be computed from the discriminants (effective Chebotarev, Lagarias–Odlyzko), is not formalized. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(b), p. 150"]
theorem remark_8_40b (L M : IntermediateField K Ω) [IsGalois K L] [IsGalois K M] :
    ∃ B : ℕ, (∀ 𝔭 ∈ splitPrimes K M, Ideal.absNorm 𝔭.asIdeal ≤ B → 𝔭 ∈ splitPrimes K L) → L ≤ M := by
  by_cases hLM : L ≤ M
  · exact ⟨0, fun _ => hLM⟩
  · obtain ⟨𝔭, hM, hL⟩ := Set.not_subset.mp
      (fun h : splitPrimes K M ⊆ splitPrimes K L => hLM ((thm_8_38 L M).mpr h))
    exact ⟨Ideal.absNorm 𝔭.asIdeal, fun h => absurd (h 𝔭 hM le_rfl) hL⟩

end

end NumberFieldKB.MilneANT
