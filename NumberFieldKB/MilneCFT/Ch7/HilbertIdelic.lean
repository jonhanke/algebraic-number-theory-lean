import NumberFieldKB.MilneCFT.Ch7.IdealReciprocityKer
import NumberFieldKB.MilneCFT.Ch7.Basic
import NumberFieldKB.MilneCFT.Ch7.IdelicExistence
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
# The Hilbert class field from the idelic theorems (Milne, *CFT*, Chapter V, Example 3.9 via §5)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Example 3.9 (p. 159), Theorem 5.3, Theorem 5.5, Remark 5.8 (pp. 178–180), Proposition 4.6 (p. 173).

The Hilbert class field is the class field of the open subgroup $N_1 = K^\times\cdot\prod_v\mathcal O_v^\times\cdot
\prod_{w\mid\infty}K_w^\times / K^\times$ of $C_K$ (`classesN1`), whose quotient is the class group
(Proposition 4.6 for $\mathfrak m = 1$). Given $H$ with $\mathrm{Nm}(C_H) = N_1$ (Theorem 5.5):

* $H$ is unramified at every finite and real place: the Artin map of $H$ is trivial on $\mathcal O_v^\times$ and on
  $K_w^\times$, and by the named input `ArtinInertia` (local–global compatibility and local class field theory) this
  forces $H/K$ to be unramified there;
* the ideal-theoretic Artin map $I_K\to\mathrm{Gal}(H/K)$ is onto with kernel the principal ideals (the reciprocity
  half of Remark 5.8 with $\mathfrak m = 1$, `artinMap_surjective_of_idelic`, `ker_artinMap_le_of_idelic`), so it
  induces $\mathrm{Cl}_K\cong\mathrm{Gal}(H/K)$, $[\mathfrak p]\mapsto\mathrm{Frob}_\mathfrak p$.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

/-- **Inertia and the idelic Artin map** (named statement; Milne, *CFT*, Chapter V, Proposition 5.2: the restriction
of the global Artin map to $K_v^\times$ is the local Artin map; with local class field theory, Chapter I, Theorem 1.1,
and Chapter III: the local Artin map sends $\mathcal O_v^\times$ onto the inertia group, and at a real place
$K_w^\times$ onto the decomposition group [unverified locator]): for a finite abelian $L/K$, if the idelic Artin map
is trivial on the units $\mathcal O_v^\times$ of $K_v$ then $v$ is unramified in $L$, and if it is trivial on
$K_w^\times$ for a real place $w$ then $w$ does not ramify in $L$. -/
@[kb "milne2020cft" "Ch. V, Prop. 5.2 with Ch. I, Thm. 1.1 (inertia; input) [unverified locator]"]
structure ArtinInertia : Prop where
  finite : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)), IsIdelicArtinMap L φ →
    (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) → ∀ v : HeightOneSpectrum (𝓞 K),
    (∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = 1) → v ∈ unramifiedPrimes K L
  real : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)), IsIdelicArtinMap L φ →
    (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) → ∀ w : InfinitePlace K, w.IsReal →
    (∀ t : w.Completionˣ, φ (IdeleGroup.ofCompletion (𝓞 K) K w t) = 1) → ¬ InfinitePlace.RamifiesIn L w

/-- $N_1 = K^\times\cdot\mathbb I_\emptyset / K^\times\subseteq C_K$, with $\mathbb I_\emptyset =
\prod_{w\mid\infty}K_w^\times\times\prod_v\mathcal O_v^\times$ (`Ch7.idelesS ∅`). -/
def classesN1 : Subgroup (IdeleClassGroup (𝓞 K) K) :=
  (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K)))).map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))

variable {K} in
theorem mem_principalSubgroup_iff (x : IdeleGroup (𝓞 K) K) :
    x ∈ IdeleGroup.principalSubgroup (𝓞 K) K ↔ ∃ a : Kˣ, IdeleGroup.unitEmbedding (𝓞 K) K a = x := Iff.rfl

variable {K} in
theorem mem_idelesS_empty_iff (x : IdeleGroup (𝓞 K) K) :
    x ∈ Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) ↔ ∀ v, Valued.v (ideleFinAt x v) = 1 :=
  ⟨fun h v => h v (Set.notMem_empty v), fun h v _ => h v⟩

variable {K} in
theorem isOpen_idelesS_empty :
    IsOpen (Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) : Set (IdeleGroup (𝓞 K) K)) := by
  have h : (Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) : Set (IdeleGroup (𝓞 K) K)) =
      (fun x => (Homeomorph.prodUnits (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) x).2) ⁻¹'
        (finiteIdeleUnits K : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
    ext x
    exact mem_idelesS_empty_iff x
  rw [h]
  exact (aside_4_5 (K := K)).1.preimage (continuous_snd.comp (Homeomorph.prodUnits).continuous)

theorem isOpen_classesN1 : IsOpen (classesN1 K : Set (IdeleClassGroup (𝓞 K) K)) := by
  have hA : IsOpen ((IdeleGroup.principalSubgroup (𝓞 K) K ⊔
      Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K)) :
        Set (IdeleGroup (𝓞 K) K)) :=
    Subgroup.isOpen_mono le_sup_right (isOpen_idelesS_empty (K := K))
  have := (QuotientGroup.isOpenMap_coe (N := IdeleGroup.principalSubgroup (𝓞 K) K)) _ hA
  exact this

variable {K} in
theorem sup_principal_idelesS_eq_comap :
    IdeleGroup.principalSubgroup (𝓞 K) K ⊔ Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) =
      (Subgroup.comap (ideleToIdeal K) (toPrincipalIdeal (𝓞 K) K).range) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨a, (ideleToIdeal_unitEmbedding a).symm⟩
    · intro x hx
      have : ideleToIdeal K x = 1 := (item_4_1 (K := K)).2 x |>.2 ((mem_idelesS_empty_iff x).1 hx)
      show ideleToIdeal K x ∈ (toPrincipalIdeal (𝓞 K) K).range
      rw [this]; exact one_mem _
  · intro x hx
    obtain ⟨a, ha⟩ := hx
    have hs : x * (IdeleGroup.unitEmbedding (𝓞 K) K a)⁻¹ ∈ Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) := by
      rw [mem_idelesS_empty_iff, ← (item_4_1 (K := K)).2, map_mul, map_inv, ideleToIdeal_unitEmbedding, ← ha,
        mul_inv_cancel]
    have : x = x * (IdeleGroup.unitEmbedding (𝓞 K) K a)⁻¹ * IdeleGroup.unitEmbedding (𝓞 K) K a := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_right hs) (Subgroup.mem_sup_left ⟨a, rfl⟩)

theorem finiteIndex_classesN1 : (classesN1 K).FiniteIndex := by
  have h1 : classesN1 K = (IdeleGroup.principalSubgroup (𝓞 K) K ⊔
      Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K)))).map
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) := rfl
  have h2 : (classesN1 K).comap (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) =
      IdeleGroup.principalSubgroup (𝓞 K) K ⊔ Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) := by
    rw [h1, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.2 le_sup_left
  have h3 : (classesN1 K).index = (toPrincipalIdeal (𝓞 K) K).range.index := by
    rw [← Subgroup.index_comap_of_surjective (classesN1 K) (QuotientGroup.mk'_surjective _), h2,
      sup_principal_idelesS_eq_comap]
    exact Subgroup.index_comap_of_surjective _ (item_4_1 (K := K)).1
  refine ⟨?_⟩
  rw [h3]
  have : Finite (ClassGroup (𝓞 K)) := inferInstance
  have hf : Finite ((FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ (toPrincipalIdeal (𝓞 K) K).range) :=
    Finite.of_equiv (ClassGroup (𝓞 K)) (ClassGroup.equiv K).toEquiv
  exact Nat.card_pos.ne'

theorem comap_classesN1 :
    (classesN1 K).comap (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) =
      IdeleGroup.principalSubgroup (𝓞 K) K ⊔ Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) := by
  rw [classesN1, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  exact sup_eq_left.2 le_sup_left

section Main

variable {K} (hR : IdelicReciprocity K) (H : Type) [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H]

include hR

theorem ker_idelicArtinOf_eq (hN : normGroupC K H = classesN1 K) :
    (idelicArtinOf hR H).ker =
      IdeleGroup.principalSubgroup (𝓞 K) K ⊔ Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) := by
  rw [(idelicArtinOf_spec hR H).2.2.2, ← comap_normGroupC (K := K) H, hN, comap_classesN1]

theorem idelesS_empty_le_ker (hN : normGroupC K H = classesN1 K) :
    Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) ≤ (idelicArtinOf hR H).ker := by
  rw [ker_idelicArtinOf_eq hR H hN]; exact le_sup_right

omit hR in
theorem ofAdic_mem_idelesS_empty (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    IdeleGroup.ofAdicCompletion (𝓞 K) K v u ∈ Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) := by
  rw [mem_idelesS_empty_iff]
  intro w
  by_cases h : w = v
  · subst h; rw [ideleFinAt_ofAdic_self]; exact hu
  · rw [ideleFinAt_ofAdic_ne h, map_one]

omit hR in
theorem ofCompletion_mem_idelesS_empty (w : InfinitePlace K) (t : w.Completionˣ) :
    IdeleGroup.ofCompletion (𝓞 K) K w t ∈ Ch7.idelesS (∅ : Set (HeightOneSpectrum (𝓞 K))) := by
  rw [mem_idelesS_empty_iff]
  intro v
  have : ideleFinAt (IdeleGroup.ofCompletion (𝓞 K) K w t) v = 1 := rfl
  rw [this, map_one]

theorem normIdeals_one_le (hN : normGroupC K H = classesN1 K) :
    normIdeals K H (Modulus.one K).finiteSupport ≤ rayPrincipal (Modulus.one K) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨y, rfl⟩ := (item_4_1 (K := H)).1 a
  rw [← (ideleNormMap_comm (K := K) H).2]
  have hn : ideleNormMap K H y ∈ (idelicArtinOf hR H).ker := by
    rw [(idelicArtinOf_spec hR H).2.2.2]
    exact Subgroup.mem_sup_right ⟨y, rfl⟩
  rw [ker_idelicArtinOf_eq hR H hN] at hn
  obtain ⟨p, ⟨c, rfl⟩, s, hs, hps⟩ := Subgroup.mem_sup.mp hn
  have h1 : ideleToIdeal K s = 1 := ((item_4_1 (K := K)).2 s).2 ((mem_idelesS_empty_iff s).1 hs)
  rw [← hps, map_mul, h1, mul_one, ideleToIdeal_unitEmbedding]
  exact ⟨c, (congruenceSubgroup_eq_top (Modulus.one K) rfl rfl) ▸ Subgroup.mem_top c, rfl⟩

end Main

/-- **The Hilbert class field from the idelic reciprocity law and existence theorem** (Milne, *CFT*, Chapter V,
Example 3.9, via Theorems 5.3, 5.5 and Remark 5.8): conditional on `IdelicReciprocity`, `IdelicExistence` and
`ArtinInertia`, $K$ has a Hilbert class field: a finite abelian extension, unramified at all finite and infinite
places, with the Artin isomorphism $\mathrm{Cl}_K\cong\mathrm{Gal}(H/K)$. -/
@[kb "milne2020cft" "Ch. V, Example 3.9 (Hilbert class field, from Thms. 5.3, 5.5)"]
theorem exists_hilbertClassField_of_idelic (hR : IdelicReciprocity K) (hE : IdelicExistence K)
    (hI : ArtinInertia K) :
    ∃ (H : Type) (_ : Field H) (_ : NumberField H) (_ : Algebra K H) (_ : IsAbelianGalois K H),
      HilbertClassField.IsHilbertClassField K H := by
  obtain ⟨H, _, _, _, _, hN⟩ := hE.exists_field (classesN1 K) (isOpen_classesN1 K) (finiteIndex_classesN1 K)
  have hspec := idelicArtinOf_spec hR H
  have hunrH : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K H := fun v =>
    hI.finite H _ hspec.1 hspec.2.1 v fun u hu =>
      idelesS_empty_le_ker hR H hN (ofAdic_mem_idelesS_empty v u hu)
  have hrealH : ∀ w : InfinitePlace K, w.IsReal → ¬ InfinitePlace.RamifiesIn H w := fun w hw =>
    hI.real H _ hspec.1 hspec.2.1 w hw fun t => idelesS_empty_le_ker hR H hN (ofCompletion_mem_idelesS_empty w t)
  have hinfH : IsUnramifiedAtInfinitePlaces K H := by
    refine ⟨fun w' => ?_⟩
    by_contra hcon
    obtain ⟨hc, hr⟩ := InfinitePlace.isRamified_iff.1 hcon
    exact hrealH _ hr ⟨hr, w', rfl, hc⟩
  have hnd : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (Modulus.one K).finite := fun v hv =>
    v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd hv))
  have hsupp : (Modulus.one K).finiteSupport = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun v hv => hnd v hv
  have hm : ∀ v, v ∉ (Modulus.one K).finiteSupport → v ∈ unramifiedPrimes K H := fun v _ => hunrH v
  have hW : idelesW (Modulus.one K) ≤ (idelicArtinOf hR H).ker := by
    intro x hx
    refine idelesS_empty_le_ker hR H hN ?_
    rw [mem_idelesS_empty_iff]
    intro v
    exact hx.2 v (by rw [hsupp]; exact Set.notMem_empty v)
  have hsurj := artinMap_surjective_of_idelic hR H (Modulus.one K) hm hW
  have hker' : (artinMap H (Modulus.one K).finiteSupport).ker =
      (rayPrincipal (Modulus.one K)).subgroupOf (sIdeals (Modulus.one K).finiteSupport) := by
    apply le_antisymm
    · refine le_trans (ker_artinMap_le_of_idelic H hR (Modulus.one K) hm hW (fun w hw => hw.elim)) ?_
      intro g hg
      rw [Subgroup.mem_subgroupOf] at hg ⊢
      exact sup_le le_rfl (normIdeals_one_le hR H hN) hg
    · refine le_trans ?_ (le_ker_artinMap_of_idelic hR H (Modulus.one K) hm hW)
      intro g hg
      rw [Subgroup.mem_subgroupOf] at hg ⊢
      exact Subgroup.mem_sup_left hg
  refine ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, ⟨hunrH, hinfH, ?_⟩⟩
  let m := Modulus.one K
  let f : coprimeIdeals m →* Gal(H/K) := artinMap H m.finiteSupport
  have hker : (rayPrincipal m).subgroupOf (coprimeIdeals m) = f.ker := hker'.symm
  let e : RayClassGroup m ≃* Gal(H/K) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  refine ⟨(rayClassGroupOneEquiv K).symm.trans e, fun 𝔭 Q => ?_⟩
  have hv := hnd 𝔭
  have h1 : (rayClassGroupOneEquiv K).symm (HilbertClassField.primeClass K 𝔭) = rayClass m 𝔭 hv :=
    (MulEquiv.symm_apply_eq _).2 (rayClassGroupEquivClassGroup_rayClass m rfl rfl 𝔭 hv).symm
  show e ((rayClassGroupOneEquiv K).symm (HilbertClassField.primeClass K 𝔭)) = _
  rw [h1, ← artinFrob_eq H 𝔭 (hunrH 𝔭) Q]
  exact artinMap_prime H m.finiteSupport 𝔭 (coprimePrime m 𝔭 hv) rfl

end NumberFieldKB.MilneCFT
