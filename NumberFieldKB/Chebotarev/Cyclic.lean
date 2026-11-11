import NumberFieldKB.Chebotarev.Cyclotomic
import NumberFieldKB.Chebotarev.Descent
import NumberFieldKB.Chebotarev.Crossing
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# Step 2 of the proof of Chebotarev's theorem: the cyclic case, by field crossing

$L/K$ cyclic of degree $n$, $\sigma\in G = \mathrm{Gal}(L/K)$. Choose a prime $\ell\nmid d_L$ with
$n^k\mid\ell-1$ (`exists_prime_one_mod_not_dvd_discr`) and put $M = L(\zeta_\ell)$, so $[M:L] = \ell-1$
(`finrank_cyclotomic_of_not_dvd_discr`) and $\mathrm{Gal}(M/K)\cong G\times\mathrm{Gal}(K(\zeta_\ell)/K)$
(`resProd_bijective`). For each $\tau$ with $\operatorname{ord}\sigma\mid\operatorname{ord}\tau$, the element
$\gamma = (\sigma,\tau)$ fixes a field $E$ over which $M$ is cyclotomic (`isCyclotomicExtension_fixedField_zpowers`), so
the cyclotomic case (Step 1) and Deuring's descent give $\{\mathrm{Frob}_{M/K} = \gamma\}$ density $1/(n(\ell-1))$
(`hasDirichletDensity_frobSet_crossing`). These sets are disjoint and lie in $\{\mathrm{Frob}_{L/K} = \sigma\}$
(`frobClass_restrict`); counting the $\tau$ (`card_dvd_orderOf_ge`) gives `cyclic_lowerBound`, and letting
$k\to\infty$, `cyclic_density`.
-/

open NumberField IsDedekindDomain Filter Topology Set

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section FieldSide
open IntermediateField
variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]

/-- The image of `L` in `M`, as an intermediate field of `M/K`. -/
abbrev imageField (K L M : Type*) [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M] : IntermediateField K M := (IsScalarTower.toAlgHom K L M).fieldRange

/-- For $M = L(\zeta_\ell)$, the cyclotomic field $Z = K(\zeta_\ell) \subseteq M$ satisfies $L \vee Z = M$. -/
theorem exists_crossing [CharZero K] [FiniteDimensional K M] (ℓ : ℕ) [NeZero ℓ] [IsCyclotomicExtension {ℓ} L M] :
    ∃ Z : IntermediateField K M, IsCyclotomicExtension {ℓ} K Z ∧ imageField K L M ⊔ Z = ⊤ := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot L M (Set.mem_singleton ℓ) (NeZero.ne ℓ)
  have : Algebra.IsIntegral K M := inferInstance
  refine ⟨K⟮ζ⟯, hζ.intermediateField_adjoin_isCyclotomicExtension K, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Algebra.adjoin L ({ζ} : Set M) := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (le_sup_right : K⟮y⟯ ≤ _) (mem_adjoin_simple_self K y)
  | algebraMap a =>
    exact (le_sup_left : imageField K L M ≤ _) ⟨a, rfl⟩
  | add a b _ _ ha hb => exact add_mem (ha trivial) (hb trivial)
  | mul a b _ _ ha hb => exact mul_mem (ha trivial) (hb trivial)


section galois
variable [CharZero K] [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M] [IsGalois K L]

/-- The image of a Galois extension is Galois. -/
instance isGalois_imageField : IsGalois K (imageField K L M) :=
  .of_algEquiv (IsScalarTower.toAlgHom K L M).equivFieldRange

/-- The compositum of two Galois subextensions is Galois. -/
theorem isGalois_of_crossing (Z : IntermediateField K M) [IsGalois K Z]
    (hLZ : imageField K L M ⊔ Z = ⊤) : IsGalois K M := by
  have : Normal K (imageField K L M ⊔ Z : IntermediateField K M) := inferInstance
  rw [hLZ] at this
  have : Normal K M := Normal.of_algEquiv (IntermediateField.topEquiv (F := K) (E := M))
  exact ⟨⟩


/-- Restriction $\mathrm{Gal}(M/K)\to\mathrm{Gal}(L/K)\times\mathrm{Gal}(Z/K)$ to the two factors. -/
def resProd (Z : IntermediateField K M) [Normal K Z] [Normal K (imageField K L M)] :
    Gal(M/K) →* Gal(imageField K L M/K) × Gal(Z/K) :=
  (AlgEquiv.restrictNormalHom (imageField K L M)).prod (AlgEquiv.restrictNormalHom Z)

/-- The restriction to the two factors is injective when $L \vee Z = M$. -/
theorem resProd_injective [IsGalois K M] (Z : IntermediateField K M) [Normal K Z]
    (hLZ : imageField K L M ⊔ Z = ⊤) : Function.Injective (resProd (L := L) Z) := by
  rw [resProd, ← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_prod, IntermediateField.restrictNormalHom_ker,
    IntermediateField.restrictNormalHom_ker, ← IntermediateField.fixingSubgroup_sup, hLZ,
    IntermediateField.fixingSubgroup_top]

/-- $|\mathrm{Gal}(L'/K)| = [L:K]$ for the image $L'$ of `L`. -/
theorem natCard_gal_imageField : Nat.card Gal(imageField K L M/K) = Module.finrank K L := by
  rw [IsGalois.card_aut_eq_finrank]
  exact (AlgEquiv.toLinearEquiv (IsScalarTower.toAlgHom K L M).equivFieldRange).finrank_eq.symm

/-- $|\mathrm{Gal}(K(\zeta_\ell)/K)| \le \ell - 1$. -/
theorem natCard_gal_le (ℓ : ℕ) [Fact ℓ.Prime] (Z : IntermediateField K M) [IsCyclotomicExtension {ℓ} K Z] :
    Nat.card Gal(Z/K) ≤ ℓ - 1 := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K Z (Set.mem_singleton ℓ) (NeZero.ne ℓ)
  have h := Nat.card_le_card_of_injective _ (hζ.autToPow_injective K)
  have h2 : Nat.card (ZMod ℓ)ˣ = ℓ - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rwa [h2] at h


/-- $\mathrm{Gal}(K(\zeta_\ell)/K)$ is cyclic for a prime $\ell$. -/
theorem isCyclic_gal (ℓ : ℕ) [Fact ℓ.Prime] (Z : IntermediateField K M) [IsCyclotomicExtension {ℓ} K Z] :
    IsCyclic Gal(Z/K) := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K Z (Set.mem_singleton ℓ) (NeZero.ne ℓ)
  haveI : IsCyclic (ZMod ℓ)ˣ := inferInstance
  exact isCyclic_of_injective (hζ.autToPow K) (hζ.autToPow_injective K)

/-- If $[M:L] = \ell - 1$, the restriction to the two factors is bijective and
$|\mathrm{Gal}(K(\zeta_\ell)/K)| = \ell - 1$. -/
theorem resProd_bijective [IsGalois K M] (ℓ : ℕ) [Fact ℓ.Prime] (hM : Module.finrank L M = ℓ - 1)
    (Z : IntermediateField K M) [IsCyclotomicExtension {ℓ} K Z] [IsGalois K Z]
    (hLZ : imageField K L M ⊔ Z = ⊤) :
    Function.Bijective (resProd (L := L) Z) ∧ Nat.card Gal(Z/K) = ℓ - 1 := by
  have hinj := resProd_injective (L := L) Z hLZ
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hΓ : Nat.card Gal(M/K) = Module.finrank K L * (ℓ - 1) := by
    rw [IsGalois.card_aut_eq_finrank, ← hM]; exact (Module.finrank_mul_finrank K L M).symm
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, natCard_gal_imageField, hΓ] at h1
  have h2 := natCard_gal_le (K := K) (M := M) ℓ Z
  have h3 : Nat.card Gal(Z/K) = ℓ - 1 := by
    refine le_antisymm h2 ?_
    exact Nat.le_of_mul_le_mul_left h1 hn
  refine ⟨hinj.bijective_of_nat_card_le ?_, h3⟩
  rw [Nat.card_prod, natCard_gal_imageField, hΓ, h3]

end galois

end FieldSide

section Cyclic

/-- **Density of one crossing class.** In an abelian $M/K$ with $M = L \vee K(\zeta_\ell)$, an element $\gamma$ with
$\operatorname{ord}(\gamma|_L)\mid\operatorname{ord}(\gamma|_Z)$ has Frobenius density $1/[M:K]$ (the cyclotomic case over
$E = M^{\langle\gamma\rangle}$, then Deuring's descent). -/
theorem hasDirichletDensity_frobSet_crossing (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] (L Z : IntermediateField K M) [IsGalois K L] [IsGalois K Z]
    (hLZ : L ⊔ Z = ⊤) (ℓ : ℕ) [NeZero ℓ] [IsCyclotomicExtension {ℓ} K Z]
    (hcomm : ∀ x y : Gal(M/K), x * y = y * x) (γ : Gal(M/K))
    (hγ : orderOf (AlgEquiv.restrictNormalHom L γ) ∣ orderOf (AlgEquiv.restrictNormalHom Z γ))
    (hN : IdelicNormInput) :
    (frobSet K M (ConjClasses.mk γ)).HasDirichletDensity (1 / Nat.card Gal(M/K)) := by
  haveI := isCyclotomicExtension_fixedField_zpowers K M L Z hLZ ℓ γ hγ
  have h1 := cyclotomic_density hN (IntermediateField.fixedField (Subgroup.zpowers γ)) M ℓ
    (toFixedFieldGal K M γ)
  have h2 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers γ)) M = orderOf γ := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
  rw [h2] at h1
  have h3 := hasDirichletDensity_frobSet_of_fixedField K M γ h1
  have h4 : Subgroup.centralizer ({γ} : Set Gal(M/K)) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm _ _
  rw [h4] at h3
  have h5 : Nat.card (⊤ : Subgroup Gal(M/K)) = Nat.card Gal(M/K) := Subgroup.card_top
  rwa [h5] at h3




/-- The two restriction maps to `L` and to its image in `M` agree up to the isomorphism `L ≃ imageField`. -/
theorem autCongr_restrictNormalHom (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] [IsGalois K L] [IsGalois K M] (γ : Gal(M/K)) :
    AlgEquiv.autCongr (IsScalarTower.toAlgHom K L M).equivFieldRange (AlgEquiv.restrictNormalHom L γ) =
      AlgEquiv.restrictNormalHom (imageField K L M) γ := by
  ext y
  obtain ⟨x, rfl⟩ := (IsScalarTower.toAlgHom K L M).equivFieldRange.surjective y
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.restrictNormalHom_apply]
  exact AlgEquiv.restrictNormal_commutes γ L x

/-- Monotonicity of Dirichlet ratios for `s > 1`. -/
theorem dirichletRatio_mono {F : Type} [Field F] [NumberField F] {S T : Set (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) {s : ℝ} (hs : 1 < s) : dirichletRatio S s ≤ dirichletRatio T s := by
  unfold dirichletRatio
  refine div_le_div_of_nonneg_right ?_ ((Set.univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum_nonneg s)
  have h := primeIdealZetaSum_union_disjoint (S := S) (T := T \ S) Set.disjoint_sdiff_right hs
  rw [Set.union_sdiff_cancel hST] at h
  have := (T \ S).primeIdealZetaSum_nonneg s
  linarith

/-- **The crossing argument, for a fixed auxiliary prime** $\ell$ with $n^k \mid \ell - 1$ and $[L(\zeta_\ell):L] = \ell-1$. -/
theorem cyclic_lowerBound_aux (hN : IdelicNormInput) (K L M : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [IsGalois K L] [IsCyclic Gal(L/K)] (σ : Gal(L/K)) (k : ℕ) (hk : 0 < k)
    (ℓ : ℕ) [Fact ℓ.Prime] [IsCyclotomicExtension {ℓ} L M] (hM : Module.finrank L M = ℓ - 1)
    (hdiv : (Module.finrank K L) ^ k ∣ ℓ - 1) :
    ∀ b < (1 - ((Module.finrank K L).primeFactors.card : ℝ) / 2 ^ k) / Module.finrank K L,
      ∀ᶠ s in 𝓝[>] 1, b ≤ dirichletRatio (frobSet K L (ConjClasses.mk σ)) s := by
  classical
  intro b hb
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
  obtain ⟨Z, hZ, hLZ⟩ := exists_crossing (K := K) (L := L) (M := M) ℓ
  haveI hZgal : IsGalois K Z := IsCyclotomicExtension.isGalois {ℓ} K Z
  haveI hMgal : IsGalois K M := isGalois_of_crossing (L := L) Z hLZ
  obtain ⟨hbij, hZcard⟩ := resProd_bijective (L := L) ℓ hM Z hLZ
  haveI hcycZ : IsCyclic Gal(Z/K) := isCyclic_gal ℓ Z
  set e := (IsScalarTower.toAlgHom K L M).equivFieldRange with he
  haveI : IsCyclic Gal(imageField K L M/K) :=
    isCyclic_of_surjective (AlgEquiv.autCongr e) (AlgEquiv.autCongr e).surjective
  have hcomm : ∀ x y : Gal(M/K), x * y = y * x := by
    intro x y
    apply hbij.1
    rw [map_mul, map_mul]
    exact Prod.ext ((IsCyclic.commGroup (α := Gal(imageField K L M/K))).mul_comm _ _)
      ((IsCyclic.commGroup (α := Gal(Z/K))).mul_comm _ _)
  set n := Module.finrank K L with hn_def
  have hn : 0 < n := Module.finrank_pos
  have hcardG : Nat.card Gal(L/K) = n := IsGalois.card_aut_eq_finrank K L
  have hd : orderOf σ ∣ n := hcardG ▸ orderOf_dvd_natCard σ
  set σ' := AlgEquiv.autCongr e σ with hσ'_def
  have hσ' : orderOf σ' = orderOf σ := MulEquiv.orderOf_eq _ _
  -- the good elements of `Gal(Z/K)`
  haveI : Fintype Gal(Z/K) := Fintype.ofFinite _
  let ι := {τ : Gal(Z/K) // orderOf σ ∣ orderOf τ}
  choose γ hγ using fun τ : ι => hbij.2 (σ', τ.1)
  have hγ1 : ∀ τ : ι, AlgEquiv.restrictNormalHom (imageField K L M) (γ τ) = σ' :=
    fun τ => congrArg Prod.fst (hγ τ)
  have hγ2 : ∀ τ : ι, AlgEquiv.restrictNormalHom Z (γ τ) = τ.1 := fun τ => congrArg Prod.snd (hγ τ)
  have hγL : ∀ τ : ι, AlgEquiv.restrictNormalHom L (γ τ) = σ := by
    intro τ
    apply (AlgEquiv.autCongr e).injective
    rw [autCongr_restrictNormalHom K L M, hγ1]
  have hΓ : Nat.card Gal(M/K) = n * (ℓ - 1) := by
    rw [IsGalois.card_aut_eq_finrank, ← hM]; exact (Module.finrank_mul_finrank K L M).symm
  have hdens : ∀ τ : ι, (frobSet K M (ConjClasses.mk (γ τ))).HasDirichletDensity
      (1 / (Nat.card Gal(M/K))) := fun τ =>
    hasDirichletDensity_frobSet_crossing K M (imageField K L M) Z hLZ ℓ hcomm (γ τ)
      (by rw [hγ1, hγ2, hσ']; exact τ.2) hN
  have hsub : ∀ τ : ι, frobSet K M (ConjClasses.mk (γ τ)) ⊆ frobSet K L (ConjClasses.mk σ) := by
    intro τ 𝔭 h𝔭
    refine ⟨unramifiedPrimes_subset_of_tower K L M h𝔭.1, ?_⟩
    rw [frobClass_restrict K L M h𝔭.1, h𝔭.2]
    exact congrArg ConjClasses.mk (hγL τ)
  have hdisj : Pairwise (Function.onFun Disjoint fun τ : ι => frobSet K M (ConjClasses.mk (γ τ))) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro 𝔭 ⟨_, ha⟩ ⟨_, hb⟩
    apply hab
    obtain ⟨c, hc⟩ := isConj_iff.1 ((ConjClasses.mk_eq_mk_iff_isConj).1 (ha.symm.trans hb))
    rw [hcomm c (γ a), mul_inv_cancel_right] at hc
    have h2 := hγ2 b
    rw [← hc, hγ2 a] at h2
    exact Subtype.ext h2
  -- counting the good elements
  have hcount : (1 - (n.primeFactors.card : ℝ) / 2 ^ k) * (ℓ - 1 : ℕ) ≤ Fintype.card ι := by
    letI : CommGroup Gal(Z/K) := IsCyclic.commGroup
    have h := card_dvd_orderOf_ge Gal(Z/K) hn hk hd (by rw [hZcard]; exact hdiv)
    rw [hZcard] at h
    have h2 : {τ : Gal(Z/K) | orderOf σ ∣ orderOf τ}.ncard = Fintype.card ι := by
      rw [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card]
      exact Fintype.card_congr (Equiv.refl _)
    rw [h2] at h
    exact h
  have hpos : (0 : ℝ) < (ℓ - 1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hℓ.one_lt
  have hlim : Tendsto (fun s => ∑ τ : ι, dirichletRatio (frobSet K M (ConjClasses.mk (γ τ))) s)
      (𝓝[>] 1) (𝓝 (∑ _ : ι, 1 / (Nat.card Gal(M/K) : ℝ))) :=
    tendsto_finsetSum _ fun τ _ => (hasDirichletDensity_iff _ _).1 (hdens τ)
  have hb' : b < ∑ _ : ι, 1 / (Nat.card Gal(M/K) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hΓ]
    refine lt_of_lt_of_le hb ?_
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Nat.cast_mul, div_le_iff₀ hn']
    have : (Fintype.card ι : ℝ) * (1 / (↑n * ↑(ℓ - 1 : ℕ))) * n = Fintype.card ι / (ℓ - 1 : ℕ) := by
      field_simp
    rw [this, le_div_iff₀ hpos]
    exact hcount
  filter_upwards [hlim.eventually (lt_mem_nhds hb'), self_mem_nhdsWithin] with s hs hs1
  have hs1 : 1 < s := hs1
  refine hs.le.trans ?_
  rw [← dirichletRatio_iUnion _ hdisj hs1]
  exact dirichletRatio_mono (Set.iUnion_subset hsub) hs1

/-- *Proved* (conditional on `IdelicNormInput`). **The lower bound for the cyclic case.** For $L/K$ cyclic of degree `n`, $\sigma \in G$ and `k ≥ 1`,
the lower Dirichlet density of $\{\mathrm{Frob}_{\mathfrak p} = \sigma\}$ is at least $(1 - \omega(n)/2^k)/n$.
(Field crossing with $M = L(\zeta_\ell)$, $n^k \mid \ell - 1$: Step 2 of the proof of Chebotarev's theorem.) -/
theorem cyclic_lowerBound (hN : IdelicNormInput) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsCyclic Gal(L/K)] (σ : Gal(L/K)) (k : ℕ) :
    ∀ b < (1 - ((Module.finrank K L).primeFactors.card : ℝ) / 2 ^ k) / Module.finrank K L,
      ∀ᶠ s in 𝓝[>] 1, b ≤ dirichletRatio (frobSet K L (ConjClasses.mk σ)) s := by
  intro b hb
  set k' := max k 1 with hk'
  have hk'pos : 0 < k' := lt_max_of_lt_right one_pos
  have hn : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have hb' : b < (1 - ((Module.finrank K L).primeFactors.card : ℝ) / 2 ^ k') / Module.finrank K L := by
    refine lt_of_lt_of_le hb ?_
    refine div_le_div_of_nonneg_right ?_ hn.le
    have : (2 : ℝ) ^ k ≤ 2 ^ k' := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    have h0 : (0 : ℝ) ≤ ((Module.finrank K L).primeFactors.card : ℝ) := Nat.cast_nonneg _
    have := div_le_div_of_nonneg_left h0 (by positivity) this
    linarith
  obtain ⟨ℓ, hℓ, hdiv, hdisc⟩ := exists_prime_one_mod_not_dvd_discr L ((Module.finrank K L) ^ k')
    (pow_pos Module.finrank_pos _)
  haveI := Fact.mk hℓ
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  exact cyclic_lowerBound_aux hN K L (CyclotomicField ℓ L) σ k' hk'pos ℓ
    (finrank_cyclotomic_of_not_dvd_discr L (CyclotomicField ℓ L) ℓ hdisc) hdiv b hb'

/-- *Proved* from `cyclic_lowerBound`, `finite_compl_unramifiedPrimes` and
`tendsto_primeIdealZetaSum_univ_atTop`, via `hasDirichletDensity_of_partition_iUnion`. **The cyclic case (Step 2)**: for $L/K$ cyclic, each $\sigma \in G$ has density
$1/[L:K]$. -/
theorem cyclic_density (hN : IdelicNormInput) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsCyclic Gal(L/K)] (σ : Gal(L/K)) :
    (frobSet K L (ConjClasses.mk σ)).HasDirichletDensity (1 / Module.finrank K L) := by
  classical
  set n := Module.finrank K L with hn_def
  have hn : 0 < n := Module.finrank_pos
  have hcomm : ∀ x y : Gal(L/K), x * y = y * x := (IsCyclic.commGroup (α := Gal(L/K))).mul_comm
  -- the Chebotarev sets of the elements partition the unramified primes
  have hdisj : Pairwise (Function.onFun Disjoint fun τ : Gal(L/K) => frobSet K L (ConjClasses.mk τ)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro 𝔭 ⟨_, ha⟩ ⟨_, hb⟩
    apply hab
    obtain ⟨c, hc⟩ := isConj_iff.1 ((ConjClasses.mk_eq_mk_iff_isConj).1 (ha.symm.trans hb))
    rw [hcomm c a, mul_inv_cancel_right] at hc
    exact hc
  have hU : (⋃ τ : Gal(L/K), frobSet K L (ConjClasses.mk τ)) = unramifiedPrimes K L := by
    ext 𝔭
    simp only [Set.mem_iUnion, frobSet, Set.mem_ofPred_eq]
    refine ⟨fun ⟨_, h, _⟩ => h, fun h => ?_⟩
    obtain ⟨g, hg⟩ := ConjClasses.exists_rep (frobClass K L 𝔭)
    exact ⟨g, h, hg.symm⟩
  -- the unramified primes have density 1
  have hP := tendsto_primeIdealZetaSum_univ_atTop (F := K)
  have huniv : (univ : Set (HeightOneSpectrum (𝓞 K))).HasDirichletDensity 1 := by
    rw [hasDirichletDensity_iff]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hP.eventually_gt_atTop 0] with s hs
    exact (div_self hs.ne').symm
  have hunr : (unramifiedPrimes K L).HasDirichletDensity 1 := by
    refine HasDirichletDensity.congr_finite huniv ((finite_compl_unramifiedPrimes K L).subset ?_)
    intro 𝔭 h𝔭
    rcases h𝔭 with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd (Set.mem_univ 𝔭) h
  rw [← hU] at hunr
  have hsum : ∑ _τ : Gal(L/K), (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank, nsmul_eq_mul, ← hn_def]
    field_simp
  refine hasDirichletDensity_of_partition_iUnion _ hdisj hunr (fun _ => 1 / (n : ℝ)) hsum ?_ σ
  -- lower bounds from `cyclic_lowerBound`, letting `k → ∞`
  intro τ b hb
  have hlim : Tendsto (fun k : ℕ => (1 - (n.primeFactors.card : ℝ) / 2 ^ k) / n) atTop
      (𝓝 (1 / n)) := by
    have h0 : Tendsto (fun k : ℕ => (n.primeFactors.card : ℝ) / 2 ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    rw [sub_zero] at this
    exact this.div_const _
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hlim).1 b hb).exists
  exact cyclic_lowerBound hN K L τ k b hk

end Cyclic

end

end NumberFieldKB.Chebotarev
