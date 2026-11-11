import NumberFieldKB.MilneCFT.Ch5ConductorUncond2
import NumberFieldKB.MilneCFT.Ch8.NormLimitationTauCeti
import NumberFieldKB.MilneCFT.Ch7.ArtinInertiaTauCeti
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter V, Theorem 3.16 (the norm limitation theorem, ideal form), unconditional

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Theorem 3.16 (p. 161), Chapter VIII, Theorem 4.8.

`normLimitation`: for a finite extension $L/K$ with maximal abelian subextension $L'$ and every defining modulus
$\mathfrak m$ of $L'/K$, $i(K_{\mathfrak m,1})\,\mathrm{Nm}_{L/K}(I_L^{S(\mathfrak m)}) =
i(K_{\mathfrak m,1})\,\mathrm{Nm}_{L'/K}(I_{L'}^{S(\mathfrak m)})$.

* $\subseteq$: $\mathrm{Nm}_{L/K}(\mathfrak P)=\mathfrak p^{f(\mathfrak P/\mathfrak p)}$ and
  $f(\mathfrak P/\mathfrak p)=f(\mathfrak P/\mathfrak P')f(\mathfrak P'/\mathfrak p)$ (`normIdeals_le_of_tower`).
* $\supseteq$: an ideal of the right side lies in the kernel of the Artin map of $L'$, so lifts to an idèle $x\in I_\mathfrak m$
  of $K^\times\mathrm{Nm}(I_{L'})$; by the idèlic norm limitation theorem (`Ch8.theorem4_8`,
  $\mathrm{Nm}\,C_L=\mathrm{Nm}\,C_{L'}$) $x\in K^\times\mathrm{Nm}(I_L)$, and weak approximation
  (`exists_mul_close_above_pos_of_dvd`) moves the norm into $I_L^{S(\mathfrak m)}$ with the right signs
  (`mem_takagi_of_mem_ideleNormGroup`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev NumberFieldKB.Ideles
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

section Idelic

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- An idèle of $I_\mathfrak m$ in $K^\times\mathrm{Nm}(I_L)$ has its ideal in the Takagi group
$i(K_{\mathfrak m,1})\,\mathrm{Nm}(I_L^{S(\mathfrak m)})$ (for any finite $L/K$, not necessarily abelian). -/
theorem mem_takagi_of_mem_ideleNormGroup (m : Modulus K) {x : IdeleGroup (𝓞 K) K} (hx : x ∈ idelesMod m)
    (hxN : x ∈ ideleNormGroup L) :
    ideleToIdeal K x ∈ rayPrincipal m ⊔ normIdeals K L m.finiteSupport := by
  classical
  have hfin : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  obtain ⟨p, ⟨c, rfl⟩, r, ⟨y, rfl⟩, hpr⟩ := Subgroup.mem_sup.mp hxN
  let R : Finset (InfinitePlace L) := Finset.univ.filter
    (fun u => u.IsReal ∧ u.comap (algebraMap K L) ∈ m.infinite)
  obtain ⟨β, hβ1, hβ2, hβ3⟩ := exists_mul_close_above_pos_of_dvd L y m.finiteSupport hfin
    (hfin.toFinset.sup m.ord) R
  set z := IdeleGroup.unitEmbedding (𝓞 L) L β * y with hz
  set c' : Kˣ := c * (Units.map (Algebra.norm K : L →* K) β)⁻¹ with hc'
  have hNz : ideleNormMap K L z = IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (Algebra.norm K : L →* K) β) *
      ideleNormMap K L y := by
    rw [hz, map_mul, (ideleNormMap_comm (K := K) L).1]
  have hxz : x = IdeleGroup.unitEmbedding (𝓞 K) K c' * ideleNormMap K L z := by
    rw [hNz, hc', map_mul, map_inv, ← hpr]
    simp [mul_assoc]
  have hNzm : ideleNormMap K L z ∈ idelesMod m := by
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · refine isPosAt_ideleNormMap_of_forall' L z w (m.isReal_of_mem w hw) fun u hu => ?_
      rcases u.isReal_or_isComplex with hur | huc
      · refine Or.inr ⟨hur, hβ3 u ?_ hur⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hur, hu ▸ hw⟩
      · exact Or.inl huc
    · refine (hβ2 v hv).trans (WithZero.exp_le_exp.mpr ?_)
      have : m.ord v ≤ hfin.toFinset.sup m.ord := Finset.le_sup (f := m.ord) (hfin.mem_toFinset.mpr hv)
      omega
  have hc'm : c' ∈ congruenceSubgroup m := by
    rw [mem_congruenceSubgroup_iff_mem_idelesMod]
    have : IdeleGroup.unitEmbedding (𝓞 K) K c' = x * (ideleNormMap K L z)⁻¹ := by
      rw [hxz]; group
    rw [this]
    exact mul_mem hx (inv_mem hNzm)
  have hzs : ideleToIdeal L z ∈ sIdeals (primesAbove K L m.finiteSupport) := by
    intro w hw
    rw [count_ideleToIdeal, hβ1 w ⟨primeBelow K L w, hw, rfl⟩, WithZero.log_one]
    simp
  refine Subgroup.mem_sup.mpr ⟨toPrincipalIdeal (𝓞 K) K c', ⟨c', hc'm, rfl⟩,
    idealNorm K L (ideleToIdeal L z), ⟨_, hzs, rfl⟩, ?_⟩
  rw [← (ideleNormMap_comm (K := K) L).2, ← ideleToIdeal_unitEmbedding, ← map_mul, ← hxz]

end Idelic

section Classes

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

theorem ideleClassNorm_mk (y : IdeleGroup (𝓞 L) L) :
    Ch7.ideleClassNorm K L (y : IdeleClassGroup (𝓞 L) L) =
      ((ideleNormMap K L y : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) := by
  change Ideles.ideleClassRelNorm (Module.finBasis K L) (y : IdeleClassGroup (𝓞 L) L) = _
  rw [Ideles.ideleClassRelNorm_mk]
  rfl

/-- $x\in K^\times\mathrm{Nm}(I_L)$ iff the class of $x$ lies in $\mathrm{Nm}(C_L)$. -/
theorem mem_ideleNormGroup_iff (x : IdeleGroup (𝓞 K) K) :
    x ∈ ideleNormGroup L ↔ (x : IdeleClassGroup (𝓞 K) K) ∈ Ch7.normClasses K L := by
  constructor
  · intro hx
    obtain ⟨p, hp, r, ⟨y, rfl⟩, rfl⟩ := Subgroup.mem_sup.mp hx
    refine ⟨(y : IdeleClassGroup (𝓞 L) L), ?_⟩
    rw [ideleClassNorm_mk, QuotientGroup.mk_mul]
    have : (p : IdeleClassGroup (𝓞 K) K) = 1 := (QuotientGroup.eq_one_iff _).2 hp
    rw [this]
    exact (one_mul ((ideleNormMap K L y : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K)).symm
  · rintro ⟨c, hc⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    rw [ideleClassNorm_mk] at hc
    have h1 : x / ideleNormMap K L y ∈ IdeleGroup.principalSubgroup (𝓞 K) K :=
      QuotientGroup.eq_iff_div_mem.mp hc.symm
    have h2 : x * (ideleNormMap K L y)⁻¹ ∈ IdeleGroup.principalSubgroup (𝓞 K) K := by
      rwa [div_eq_mul_inv] at h1
    exact Subgroup.mem_sup.mpr ⟨_, h2, ideleNormMap K L y, ⟨y, rfl⟩, inv_mul_cancel_right x _⟩

end Classes

section Tower

variable (L : Type) [Field L] [NumberField L] [Algebra K L] (L' : IntermediateField K L)

/-- $\mathrm{Nm}_{L/K}(I_L^S)\subseteq\mathrm{Nm}_{L'/K}(I_{L'}^S)$ for $K\subseteq L'\subseteq L$: on a prime $\mathfrak P$
of $L$ over $\mathfrak P'$ over $\mathfrak p\notin S$, $\mathrm{Nm}_{L/K}\mathfrak P=\mathfrak p^{f(\mathfrak P/\mathfrak p)}=
\mathrm{Nm}_{L'/K}(\mathfrak P'^{f(\mathfrak P/\mathfrak P')})$. -/
theorem normIdeals_le_of_tower (S : Set (HeightOneSpectrum (𝓞 K))) :
    normIdeals K L S ≤ normIdeals K L' S := by
  unfold normIdeals
  rw [sIdeals_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  set w' : HeightOneSpectrum (𝓞 L') := primeBelow L' L w with hw'
  have hww : primeBelow K L' w' = primeBelow K L w :=
    HeightOneSpectrum.ext (by simp [primeBelow, QuadFormsKB.Tamagawa.Measure.Weil.underPlace, hw',
      Ideal.under_under])
  have hw'S : w' ∈ (primesAbove K L' S)ᶜ := by
    show primeBelow K L' w' ∉ S
    rw [hww]; exact hw
  refine ⟨primeUnitIdeal w' ^ (w.asIdeal.inertiaDeg (𝓞 L')), pow_mem ?_ _, ?_⟩
  · rw [sIdeals_eq_closure]
    exact Subgroup.subset_closure ⟨w', hw'S, rfl⟩
  · show idealNorm K L' _ = idealNorm K L _
    rw [map_pow, idealNorm_primeUnitIdeal, idealNorm_primeUnitIdeal, hww, ← pow_mul]
    congr 1
    have : w.asIdeal.LiesOver w'.asIdeal := ⟨rfl⟩
    exact (Ideal.inertiaDeg_tower (R := 𝓞 K) (S := 𝓞 L') w'.asIdeal w.asIdeal).symm

end Tower

variable (K) in
/-- **Theorem 3.16, the norm limitation theorem** (Milne, *CFT*, V, Theorem 3.16, p. 161; Grant and Leitzel 1969),
unconditional: for a finite extension $L/K$ with maximal abelian subextension $L'$ and every defining modulus $\mathfrak m$
of $L'/K$, $i(K_{\mathfrak m,1})\cdot\mathrm{Nm}_{L/K}(I_L^{S(\mathfrak m)}) =
i(K_{\mathfrak m,1})\cdot\mathrm{Nm}_{L'/K}(I_{L'}^{S(\mathfrak m)})$. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.16"]
theorem normLimitation : NormLimitation K where
  eq L _ _ _ L' _ hmax m hdm := by
    apply le_antisymm
    · exact sup_le_sup_left (normIdeals_le_of_tower L L' _) _
    · have hfac : ArtinFactorsThrough L' m := by
        refine ⟨fun v hv => ?_, fun a ha ha' => ?_⟩
        · have := hdm.finiteSupport_eq
          rw [this] at hv
          exact not_not.mp hv
        · have : (⟨_, ha'⟩ : sIdeals m.finiteSupport) ∈ (artinMap L' m.finiteSupport).ker := by
            rw [hdm.ker_eq, Subgroup.mem_subgroupOf]
            exact (le_sup_left : rayPrincipal m ≤ _) ⟨a, ha, rfl⟩
          exact this
      obtain ⟨hm, hW⟩ := (artinFactorsThrough_iff (idelicReciprocity K) L' m).1 hfac
      intro g hg
      have hgS : g ∈ sIdeals m.finiteSupport := takagiGroup_le_sIdeals L' m hg
      have hker : (⟨g, hgS⟩ : sIdeals m.finiteSupport) ∈ (artinMap L' m.finiteSupport).ker := by
        rw [hdm.ker_eq, Subgroup.mem_subgroupOf]
        exact hg
      obtain ⟨x, hx, hxg⟩ := exists_mem_idelesMod_ideleToIdeal m g hgS
      have hφ : idelicArtinOf (idelicReciprocity K) L' x = 1 := by
        rw [idelicArtinOf_eq_artinTot (idelicReciprocity K) L' m hm hW x hx, hxg]
        exact MonoidHom.mem_ker.1 hker
      have hxN' : x ∈ ideleNormGroup L' := by
        rw [← (idelicArtinOf_spec (idelicReciprocity K) L').2.2.2]
        exact hφ
      have h48 := (Ch8.theorem4_8 K).eq L L' (fun σ τ => by
          have := ‹IsAbelianGalois K L'›
          exact IsMulCommutative.is_comm.comm σ τ)
        (fun F hG hc => by
          have : IsMulCommutative Gal(F/K) := ⟨⟨hc⟩⟩
          have : IsAbelianGalois K F := {}
          exact hmax F inferInstance)
      have hxL : x ∈ ideleNormGroup L :=
        (mem_ideleNormGroup_iff L x).2 (by
          rw [h48]; exact (mem_ideleNormGroup_iff L' x).1 hxN')
      have := mem_takagi_of_mem_ideleNormGroup L m hx hxL
      rwa [hxg] at this

/-! ## Exercise 3.15 (S-class fields): the parts that are true as stated -/

section Exercise315

theorem ex315_sIdeals_anti {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) : sIdeals T ≤ sIdeals S :=
  fun _ hI v hv => hI v (h hv)

theorem ex315_primeUnitIdeal_mem {T : Set (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ T) : primeUnitIdeal v ∈ sIdeals T := by
  rw [sIdeals_eq_closure]
  exact Subgroup.subset_closure ⟨v, hv, rfl⟩

theorem ex315_finite_support (m : Modulus K) : m.finiteSupport.Finite :=
  Ideal.finite_factors m.finite_ne_bot

/-- Two $S$-class fields for the same data embed in each other (Chebotarev, `nonempty_algHom_of_splitPrimes_diff_finite`). -/
theorem exercise3_15_algHom (S : Set (HeightOneSpectrum (𝓞 K))) (m : Modulus K)
    (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hS : S.Finite)
    (A B : Type) [Field A] [NumberField A] [Algebra K A] [IsAbelianGalois K A]
    [Field B] [NumberField B] [Algebra K B] [IsAbelianGalois K B]
    (hA : IsSClassField S m H A) (hB : IsSClassField S m H B) : Nonempty (A →ₐ[K] B) := by
  refine nonempty_algHom_of_splitPrimes_diff_finite A B (S ∪ m.finiteSupport)
    (hS.union (ex315_finite_support m)) (fun v hv => ?_)
  have hvS : v ∉ S := fun h => hv.2 (Or.inl h)
  have hvm : v ∉ m.finiteSupport := fun h => hv.2 (Or.inr h)
  exact (hA.splits_iff v hvS hvm).2 ((hB.splits_iff v hvS hvm).1 hv.1)

/-- **Exercise 3.15, uniqueness** (Milne, *CFT*, V, Exercise 3.15, p. 160): the $S$-class field is unique up to
$K$-isomorphism. This is the `unique` field of `Exercise3_15 K`. -/
@[kb "milne2020cft" "Ch. V, Exercise 3.15 (uniqueness)"]
theorem exercise3_15_unique (S : Set (HeightOneSpectrum (𝓞 K))) (m : Modulus K)
    (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (L L' : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field L'] [NumberField L']
    [Algebra K L'] [IsAbelianGalois K L'] (hS : S.Finite) (h : IsSClassField S m H L)
    (h' : IsSClassField S m H L') : Nonempty (L ≃ₐ[K] L') := by
  obtain ⟨f⟩ := exercise3_15_algHom S m H hS L L' h h'
  obtain ⟨g⟩ := exercise3_15_algHom S m H hS L' L h' h
  have h1 : Module.finrank K L ≤ Module.finrank K L' :=
    LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.toRingHom.injective
  have h2 : Module.finrank K L' ≤ Module.finrank K L :=
    LinearMap.finrank_le_finrank_of_injective (f := g.toLinearMap) g.toRingHom.injective
  have heq : Module.finrank K L = Module.finrank K L' := le_antisymm h1 h2
  exact ⟨AlgEquiv.ofBijective f ⟨f.toRingHom.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) heq).1
      f.toRingHom.injective⟩⟩

/-- **Exercise 3.15, every finite abelian extension is an $S$-class field** (Milne, *CFT*, V, Exercise 3.15, p. 160):
the `isSClassField` field of `Exercise3_15 K`. Take a defining modulus $\mathfrak m$ of $L/K$ (its support is the set of
ramified primes, disjoint from $S$ since the primes of $S$ split) and $H$ the kernel of the Artin map on
$I^{S\cup S(\mathfrak m)}$. -/
@[kb "milne2020cft" "Ch. V, Exercise 3.15 (every L is an S-class field)"]
theorem exercise3_15_isSClassField (S : Set (HeightOneSpectrum (𝓞 K)))
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (hS : S.Finite)
    (hsplit : ∀ v ∈ S, v ∈ splitPrimes K L) :
    ∃ (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ), Disjoint S m.finiteSupport ∧
      IsSClassField S m H L := by
  have _ := hS
  obtain ⟨m, hdm⟩ := (reciprocityLaw_ideal_of_idelic K (idelicReciprocity K)).exists_definingModulus L
  have hunr : ∀ v ∈ S, v ∈ unramifiedPrimes K L := fun v hv => by
    have := hsplit v hv
    rw [splitPrimes_eq_frobSet_one (K := K) (L := L)] at this
    exact this.1
  have hdisj : Disjoint S m.finiteSupport :=
    Set.disjoint_left.2 fun v hvS hvm => by
      rw [hdm.finiteSupport_eq] at hvm
      exact hvm (hunr v hvS)
  have hunr' : ∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L := fun v hv => by
    rw [hdm.finiteSupport_eq] at hv
    exact not_not.mp hv
  refine ⟨m, (artinMap L (S ∪ m.finiteSupport)).ker.map (sIdeals (S ∪ m.finiteSupport)).subtype, hdisj,
    ⟨hsplit, ⟨hunr', fun w hw hr => hw ((hdm.infinite_iff w).2 hr)⟩, ?_⟩⟩
  intro v hvS hvm
  have hvT : v ∉ S ∪ m.finiteSupport := by
    rintro (h | h)
    · exact hvS h
    · exact hvm h
  rw [mem_splitPrimes_iff_artinFrob_eq_one L v (hunr' v hvm)]
  constructor
  · intro h
    refine ⟨⟨primeUnitIdeal v, ex315_primeUnitIdeal_mem hvT⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    rw [artinMap_prime L _ v _ rfl]
    exact h
  · rintro ⟨x, hx, hxe⟩
    rw [← artinMap_prime L (S ∪ m.finiteSupport) v x hxe]
    exact MonoidHom.mem_ker.1 hx

/-- **Exercise 3.15, existence, with the corrected hypothesis.** The `exists_field` clause of `Exercise3_15 K` assumes only
$\mathrm{rayPrincipal}\ \mathfrak m\ \cap I^{S\cup S(\mathfrak m)}\subseteq H$; this is too weak for the primes of $S$ to
split completely (example: $K=\mathbb Q$, $S=\{2\}$, $\mathfrak m=3\infty$, $H=\mathrm{rayPrincipal}\ \mathfrak m\cap
I^{\{2,3\}}$; then the splitting primes outside $S\cup\{3\}$ are the primes $\equiv1\bmod 3$, so by Chebotarev $L=\mathbb
Q(\zeta_3)$, in which $2$ is inert). The correct hypothesis (the image of $K_{\mathfrak m,1}$ in $I^S$, Milne's $i$) is
$(P_\mathfrak m\cdot\langle S\rangle)\cap I^{S\cup S(\mathfrak m)}\subseteq H$, under which the $S$-class field exists. -/
@[kb "milne2020cft" "Ch. V, Exercise 3.15 (existence, corrected hypothesis)"]
theorem exercise3_15_exists (S : Set (HeightOneSpectrum (𝓞 K))) (m : Modulus K)
    (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hdisj : Disjoint S m.finiteSupport)
    (hH : H ≤ sIdeals (S ∪ m.finiteSupport))
    (hP : (rayPrincipal m ⊔ Subgroup.closure (primeUnitIdeal '' S)) ⊓ sIdeals (S ∪ m.finiteSupport) ≤ H) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      IsSClassField S m H L ∧
        Nonempty (sIdeals (S ∪ m.finiteSupport) ⧸ H.subgroupOf (sIdeals (S ∪ m.finiteSupport)) ≃* Gal(L/K)) := by
  classical
  set T := S ∪ m.finiteSupport with hT
  set C := Subgroup.closure (primeUnitIdeal '' S) with hC
  set H1 := (rayPrincipal m ⊔ H) ⊔ C with hH1
  have hSm : ∀ v ∈ S, v ∉ m.finiteSupport := fun v hv => Set.disjoint_left.1 hdisj hv
  have hCle : C ≤ sIdeals m.finiteSupport := by
    rw [hC, Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    exact ex315_primeUnitIdeal_mem (hSm v hv)
  have hTle : sIdeals T ≤ sIdeals m.finiteSupport := ex315_sIdeals_anti Set.subset_union_right
  have hcong : IsCongruenceSubgroupMod m H1 :=
    ⟨le_sup_of_le_left le_sup_left,
      sup_le (sup_le (rayPrincipal_le m) (hH.trans hTle)) hCle⟩
  obtain ⟨L, _, _, _, _, hL, -⟩ := (existenceTheoremArtin K).exists_field m H1 hcong
  -- an element of `I^T` lying in `H1` lies in `H`
  have key : ∀ u ∈ sIdeals T, u ∈ H1 → u ∈ H := by
    intro u hu hu1
    obtain ⟨a, ha, s, hs, rfl⟩ := Subgroup.mem_sup.1 hu1
    obtain ⟨p, hp, h, hh, rfl⟩ := Subgroup.mem_sup.1 ha
    have e : p * h * s = h * (p * s) := by rw [mul_assoc, mul_left_comm]
    have hps : p * s ∈ sIdeals T := by
      have : p * s = h⁻¹ * (p * h * s) := by rw [e, inv_mul_cancel_left]
      rw [this]
      exact mul_mem (inv_mem (hH hh)) hu
    rw [e]
    exact mul_mem hh (hP ⟨Subgroup.mem_sup.2 ⟨p, hp, s, hs, rfl⟩, hps⟩)
  have hker : ∀ u (hu : u ∈ sIdeals m.finiteSupport), artinMap L m.finiteSupport ⟨u, hu⟩ = 1 ↔ u ∈ H1 := by
    intro u hu
    have := congrArg (fun G => (⟨u, hu⟩ : sIdeals m.finiteSupport) ∈ G) hL.ker_eq
    simpa [Subgroup.mem_subgroupOf] using this
  have hfrob : ∀ v, v ∉ m.finiteSupport → v ∉ T → (v ∈ splitPrimes K L ↔ primeUnitIdeal v ∈ H) := by
    intro v hvm hvT
    rw [mem_splitPrimes_iff_artinFrob_eq_one L v (hL.unramifiedOutside.1 v hvm), ← artinMap_prime L m.finiteSupport v
      ⟨primeUnitIdeal v, ex315_primeUnitIdeal_mem hvm⟩ rfl,
      hker _ (ex315_primeUnitIdeal_mem hvm)]
    exact ⟨key _ (ex315_primeUnitIdeal_mem hvT), fun h => Subgroup.mem_sup_left (Subgroup.mem_sup_right h)⟩
  have hSsplit : ∀ v ∈ S, v ∈ splitPrimes K L := by
    intro v hv
    rw [mem_splitPrimes_iff_artinFrob_eq_one L v (hL.unramifiedOutside.1 v (hSm v hv)),
      ← artinMap_prime L m.finiteSupport v ⟨primeUnitIdeal v, ex315_primeUnitIdeal_mem (hSm v hv)⟩ rfl,
      hker _ (ex315_primeUnitIdeal_mem (hSm v hv))]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨v, hv, rfl⟩)
  -- the Artin map restricted to `I^T`
  let ψ : sIdeals T →* Gal(L/K) := (artinMap L m.finiteSupport).comp (Subgroup.inclusion hTle)
  have hdec : sIdeals m.finiteSupport ≤ sIdeals T ⊔ C := by
    rw [sIdeals_eq_closure m.finiteSupport, Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    by_cases hvS : v ∈ S
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨v, hvS, rfl⟩)
    · exact Subgroup.mem_sup_left (ex315_primeUnitIdeal_mem (by
        rintro (h | h)
        · exact hvS h
        · exact hv h))
  have hsurj : Function.Surjective ψ := by
    intro σ
    obtain ⟨x, hx⟩ := hL.surjective σ
    obtain ⟨y, hy, s, hs, hxys⟩ := Subgroup.mem_sup.1 (hdec x.2)
    refine ⟨⟨y, hy⟩, ?_⟩
    have hs' : s ∈ sIdeals m.finiteSupport := hCle hs
    have h1 : artinMap L m.finiteSupport ⟨s, hs'⟩ = 1 :=
      (hker s hs').2 (Subgroup.mem_sup_right hs)
    have hxe : x = (⟨y, hTle hy⟩ : sIdeals m.finiteSupport) * ⟨s, hs'⟩ := Subtype.ext hxys.symm
    rw [← hx, hxe, map_mul, h1, mul_one]
    rfl
  have hkerψ : H.subgroupOf (sIdeals T) = ψ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => (hker x.1 (hTle x.2)).2 (Subgroup.mem_sup_left (Subgroup.mem_sup_right h)),
      fun h => key x.1 x.2 ((hker x.1 (hTle x.2)).1 h)⟩
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨hSsplit, hL.unramifiedOutside, fun v hvS hvm => hfrob v hvm (by
      rintro (h | h)
      · exact hvS h
      · exact hvm h)⟩,
    ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)⟩⟩

end Exercise315

end NumberFieldKB.MilneCFT
