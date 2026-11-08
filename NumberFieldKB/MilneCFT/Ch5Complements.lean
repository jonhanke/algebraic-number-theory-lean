import NumberFieldKB.MilneCFT.Ch5MainIdeal
import NumberFieldKB.HilbertClassField.ClassNumberOne

/-!
# Consequences and complements of the main theorems (Milne, *Class Field Theory*, Chapter V, §3, pp. 158–168)

* **Corollary 3.7** (`cor_3_7`, from the existence theorem with the Artin isomorphism);
* **Remark 3.8**: the conductor `IsArtinConductor` (smallest modulus through which the Artin map factors), the named
  statement `Remark3_8` (existence; divisible exactly by the ramified primes), and the proved consequences
  `remark_3_8_subfield` (subfields of $L_\mathfrak m$ are those of conductor dividing $\mathfrak m$) and
  `remark_3_8_contained` (every abelian extension lies in a ray class field);
* **Example 3.9** (`example_3_9_hilbert`, `example_3_9_rat`, named `Example3_9_sqrt_neg5`), **Example 3.10**
  (`example_3_10_kroneckerWeber`), **Example 3.11** (named), **Remark 3.12** (named), **Exercise 3.15** (named);
* **Theorem 3.16** (norm limitation, named), **Theorem 3.17** (principal ideal theorem, named), **Proposition 3.18**
  (Mathlib's transfer), **Theorem 3.19** (named), **Remark 3.20** (named);
* **Theorem 3.23** (Chebotarev, proved in this library), **Corollary 3.24**, **Theorem 3.25**, **Remark 3.26**;
* characters of ideals: cotrained and primitive characters, the conductor of a character (p. 165), **Theorem 3.27**
  (conductor-discriminant formula, named), **Remark 3.28** (named), **Example 3.30** (Mathlib's discriminant);
* the power residue symbol (p. 166).

Theorem 3.33 (Wei: special values of automorphic functions on Shimura varieties) is not stated: the library has no
Shimura varieties or automorphic functions. Its setting (the Verlagerung for an index-2 subgroup, CM fields) is in
`NumberFieldKB.MilneCFT.Ch5IndexTwoTransfer`.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## Helpers: comparing number fields through primes -/

/-- The primes of `K` splitting completely in a number field only depend on it up to `K`-isomorphism. -/
theorem splitPrimes_congr_algEquiv {L M : Type} [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M) : splitPrimes K L = splitPrimes K M := by
  apply Set.Subset.antisymm
  · letI : Algebra M L := e.symm.toAlgHom.toRingHom.toAlgebra
    haveI : IsScalarTower K M L := IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap K L x = e.symm (algebraMap K M x)
      simp
    exact MilneANT.splitPrimes_subset_of_tower M L
  · letI : Algebra L M := e.toAlgHom.toRingHom.toAlgebra
    haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap K M x = e (algebraMap K L x)
      simp
    exact MilneANT.splitPrimes_subset_of_tower L M

/-- **Comparison of Galois extensions through split primes**: if `L` and `M` are finite Galois extensions of `K`
and all but finitely many primes splitting completely in `M` split completely in `L`, then `L` embeds into `M`. -/
theorem nonempty_algHom_of_splitPrimes_diff_finite (L M : Type) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (h : splitPrimes K M \ S ⊆ splitPrimes K L) :
    Nonempty (L →ₐ[K] M) := by
  let A := AlgebraicClosure K
  let φL : L →ₐ[K] A := IsAlgClosed.lift
  let φM : M →ₐ[K] A := IsAlgClosed.lift
  let L' : IntermediateField K A := φL.fieldRange
  let M' : IntermediateField K A := φM.fieldRange
  let eL : L ≃ₐ[K] L' := AlgEquiv.ofInjectiveField φL
  let eM : M ≃ₐ[K] M' := AlgEquiv.ofInjectiveField φM
  haveI : IsGalois K L' := IsGalois.of_algEquiv eL
  haveI : IsGalois K M' := IsGalois.of_algEquiv eM
  haveI : FiniteDimensional K L' := Module.Finite.equiv eL.toLinearEquiv
  haveI : FiniteDimensional K M' := Module.Finite.equiv eM.toLinearEquiv
  let Ω : IntermediateField K A := L' ⊔ M'
  haveI : FiniteDimensional K Ω := IntermediateField.finiteDimensional_sup L' M'
  haveI : NumberField Ω := { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans K Ω }
  let L'' : IntermediateField K Ω := IntermediateField.restrict (le_sup_left : L' ≤ Ω)
  let M'' : IntermediateField K Ω := IntermediateField.restrict (le_sup_right : M' ≤ Ω)
  let eL' : L ≃ₐ[K] L'' := eL.trans (IntermediateField.restrictAlgEquiv _)
  let eM' : M ≃ₐ[K] M'' := eM.trans (IntermediateField.restrictAlgEquiv _)
  haveI : IsGalois K L'' := IsGalois.of_algEquiv eL'
  haveI : IsGalois K M'' := IsGalois.of_algEquiv eM'
  have hL : splitPrimes K L'' = splitPrimes K L := (splitPrimes_congr_algEquiv eL').symm
  have hM : splitPrimes K M'' = splitPrimes K M := (splitPrimes_congr_algEquiv eM').symm
  have hle : L'' ≤ M'' := by
    refine MilneANT.le_of_density_sdiff_zero L'' M'' ?_
    rw [hL, hM]
    exact hasDirichletDensity_zero_of_subset (fun v hv => by
      by_contra hvS
      exact hv.2 (h ⟨hv.1, hvS⟩)) (hasDirichletDensity_zero_of_finite hS)
  exact ⟨((eM'.symm : M'' →ₐ[K] M).comp (IntermediateField.inclusion hle)).comp (eL' : L →ₐ[K] L'')⟩
section Helpers
open scoped IsMulCommutative

/-- In an abelian group two elements are conjugate iff they are equal. -/
theorem isConj_abelian {G : Type} [Group G] (h : ∀ a b : G, a * b = b * a) {a b : G} : IsConj a b ↔ a = b := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    rw [mul_assoc, h a, mul_inv_cancel_left]
  · rintro rfl
    exact ⟨1, by simp⟩

/-- A prime unramified in a finite abelian extension splits completely iff its Frobenius element is trivial. -/
theorem mem_splitPrimes_iff_artinFrob_eq_one (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ unramifiedPrimes K L) :
    v ∈ splitPrimes K L ↔ artinFrob L v = 1 := by
  have Q : v.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
  rw [HilbertClassField.mem_splitPrimes_iff, HilbertClassField.splitsCompletelyIn_iff_frobAt_eq_one K L v hv Q,
    ← artinFrob_eq L v hv Q]

/-- **Compatibility of Frobenius elements with restriction** to an abelian subextension. -/
theorem artinFrob_restrict (L M : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M] [Algebra L M] [IsScalarTower K L M]
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ unramifiedPrimes K M) :
    artinFrob L v = AlgEquiv.restrictNormalHom L (artinFrob M v) := by
  have h := frobClass_restrict K L M hv
  have e1 : frobClass K L v = ConjClasses.mk (artinFrob L v) := rfl
  have e2 : frobClass K M v = ConjClasses.mk (artinFrob M v) := rfl
  rw [e1, e2] at h
  have h' : ConjClasses.mk (artinFrob L v) = ConjClasses.mk (AlgEquiv.restrictNormalHom L (artinFrob M v)) := h
  rwa [ConjClasses.mk_eq_mk_iff_isConj, isConj_abelian (fun a b : Gal(L/K) => mul_comm a b)] at h'

/-- **Comparison of abelian extensions through Frobenius elements**: if `L` is unramified outside the finite set `S`
and, outside `S`, a trivial Frobenius element in `M` forces a trivial Frobenius element in `L` (and `M` is unramified
outside `S`), then `L` embeds into `M`. -/
theorem nonempty_algHom_of_artinFrob (L M : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M] (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) (hL : ∀ v, v ∉ S → v ∈ unramifiedPrimes K L) (hM : ∀ v, v ∉ S → v ∈ unramifiedPrimes K M)
    (h : ∀ v, v ∉ S → artinFrob M v = 1 → artinFrob L v = 1) : Nonempty (L →ₐ[K] M) := by
  refine nonempty_algHom_of_splitPrimes_diff_finite L M S hS (fun v hv => ?_)
  have hvS : v ∉ S := hv.2
  rw [mem_splitPrimes_iff_artinFrob_eq_one L v (hL v hvS)]
  exact h v hvS ((mem_splitPrimes_iff_artinFrob_eq_one M v (hM v hvS)).1 hv.1)

/-- **Compatibility of the Artin map with restriction** to an abelian subextension. -/
theorem artinMap_restrict (L M : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M] [Algebra L M] [IsScalarTower K L M]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, v ∉ S → v ∈ unramifiedPrimes K M) (x : sIdeals S) :
    artinMap L S x = AlgEquiv.restrictNormalHom L (artinMap M S x) := by
  obtain ⟨x, hx⟩ := x
  have hmem : ∀ y ∈ Subgroup.closure (primeUnitIdeal '' Sᶜ), y ∈ sIdeals S := fun y hy => by
    rw [sIdeals_eq_closure]; exact hy
  have key : ∀ y : (FractionalIdeal (𝓞 K)⁰ K)ˣ, y ∈ Subgroup.closure (primeUnitIdeal '' Sᶜ) →
      ∀ hy : y ∈ sIdeals S,
        artinMap L S ⟨y, hy⟩ = AlgEquiv.restrictNormalHom L (artinMap M S ⟨y, hy⟩) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy' =>
      intro hyS
      obtain ⟨w, hw, rfl⟩ := hy'
      rw [artinMap_prime L S w _ rfl, artinMap_prime M S w _ rfl]
      exact artinFrob_restrict L M w (hS w hw)
    | one =>
      intro h
      have : (⟨1, h⟩ : sIdeals S) = 1 := rfl
      rw [this, map_one, map_one, map_one]
    | mul y z hy hz ihy ihz =>
      intro h
      have : (⟨y * z, h⟩ : sIdeals S) = ⟨y, hmem y hy⟩ * ⟨z, hmem z hz⟩ := rfl
      rw [this, map_mul, map_mul, map_mul, ihy (hmem y hy), ihz (hmem z hz)]
    | inv y hy ihy =>
      intro h
      have : (⟨y⁻¹, h⟩ : sIdeals S) = (⟨y, hmem y hy⟩ : sIdeals S)⁻¹ := rfl
      rw [this, map_inv, map_inv, map_inv, ihy (hmem y hy)]
  exact key x (by rw [← sIdeals_eq_closure]; exact hx) hx

/-- In a class field of $P_\mathfrak m$, a prime $\mathfrak p \nmid \mathfrak m_0$ with trivial Frobenius element has a
trivial class in $C_\mathfrak m$. -/
theorem rayClass_eq_one_of_artinFrob_eq_one {m : Modulus K} (M : Type) [Field M] [NumberField M] [Algebra K M]
    [IsAbelianGalois K M] (hM : IsClassFieldOf M m (rayPrincipal m)) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ m.finite) (h : artinFrob M v = 1) : rayClass m v hv = 1 := by
  have h1 : artinMap M m.finiteSupport (coprimePrime m v hv) = 1 :=
    (artinMap_prime M m.finiteSupport v (coprimePrime m v hv) rfl).trans h
  have h2 : (coprimePrime m v hv : sIdeals m.finiteSupport) ∈ (artinMap M m.finiteSupport).ker := h1
  rw [hM.ker_eq] at h2
  exact (QuotientGroup.eq_one_iff _).2 h2

end Helpers

/-- $\mathrm{Nm}(C_{L,m}) = i(K_{\mathfrak m,1})\cdot\mathrm{Nm}(I_L^{S(\mathfrak m)}) \bmod i(K_{\mathfrak m,1})$, a subgroup of
$C_\mathfrak m$ (Milne, *CFT*, V, §3, p. 158). -/
@[kb "milne2020cft" "Ch. V, §3, p. 158 (the subgroup Nm(C_{L,m}) of C_m)"]
def normRayClass (m : Modulus K) (L : Type) [Field L] [NumberField L] [Algebra K L] : Subgroup (RayClassGroup m) :=
  ((rayPrincipal m ⊔ normIdeals K L m.finiteSupport).subgroupOf (coprimeIdeals m)).map (QuotientGroup.mk' _)

/-! ## Helpers for Corollary 3.7: the norm group is the fixing subgroup -/

section NormGroup

open scoped IsMulCommutative

/-- The primes of a number field above a finite set of primes of the base field form a finite set. -/
theorem finite_primesAbove_of_finite (F : Type) [Field F] [NumberField F] [Algebra K F]
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) : (primesAbove K F S).Finite := by
  have hsub : primesAbove K F S ⊆ ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 F) | primeBelow K F w = v} :=
    fun w hw => Set.mem_biUnion hw rfl
  refine Set.Finite.subset (hS.biUnion fun v _ => ?_) hsub
  let f : {w : HeightOneSpectrum (𝓞 F) // primeBelow K F w = v} → v.asIdeal.primesOver (𝓞 F) :=
    fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  exact Set.finite_coe_iff.1 (Finite.of_injective f hf)

/-- **The Artin map of the top field over an intermediate field is onto** (Chebotarev): every automorphism of `Lm`
over `F` is the Artin automorphism of an ideal of `F` prime to the primes above the finite set `S`. -/
theorem exists_artinMap_eq (Lm : Type) [Field Lm] [NumberField Lm] [Algebra K Lm] [IsAbelianGalois K Lm]
    (F : IntermediateField K Lm) {S : Set (HeightOneSpectrum (𝓞 K))} (hSfin : S.Finite) (τ : Gal(Lm/F)) :
    ∃ a : sIdeals (primesAbove K F S), artinMap Lm (primesAbove K F S) a = τ := by
  haveI : IsAbelianGalois F Lm := IsAbelianGalois.tower_top K F Lm
  obtain ⟨v', hv', hnot⟩ :=
    ((HilbertClassField.frobSet_infinite F Lm (ConjClasses.mk τ)).sdiff (finite_primesAbove_of_finite F hSfin)).nonempty
  have hfrob : artinFrob Lm v' = τ := by
    have e1 : frobClass F Lm v' = ConjClasses.mk (artinFrob Lm v') := rfl
    have h2 := hv'.2
    rw [e1, ConjClasses.mk_eq_mk_iff_isConj, isConj_abelian (fun a b : Gal(Lm/F) => mul_comm a b)] at h2
    exact h2
  refine ⟨⟨primeUnitIdeal v', ?_⟩, ?_⟩
  · rw [sIdeals_eq_closure]
    exact Subgroup.subset_closure ⟨v', hnot, rfl⟩
  · exact (artinMap_prime Lm _ v' _ rfl).trans hfrob

/-- **Image of the norm group under the Artin map** (Milne, *CFT*, V, proof of Corollary 3.7, from Proposition 3.3 and
Chebotarev): the Artin automorphisms of the norms from `F` are the automorphisms of `Lm` fixing `F`. -/
theorem mem_fixingSubgroup_iff_exists_norm (Lm : Type) [Field Lm] [NumberField Lm] [Algebra K Lm]
    [IsAbelianGalois K Lm] (F : IntermediateField K Lm) {S : Set (HeightOneSpectrum (𝓞 K))} (hSfin : S.Finite)
    (hS : ∀ v, v ∉ S → v ∈ unramifiedPrimes K Lm) (τ : Gal(Lm/K)) :
    τ ∈ F.fixingSubgroup ↔ ∃ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ normIdeals K F S ∧
      artinMap Lm S b = τ := by
  haveI : IsAbelianGalois F Lm := IsAbelianGalois.tower_top K F Lm
  constructor
  · intro hτ
    obtain ⟨a, ha⟩ := exists_artinMap_eq Lm F hSfin (F.fixingSubgroupEquiv ⟨τ, hτ⟩)
    refine ⟨⟨idealNorm K F a, idealNorm_mem_sIdeals K F S a a.2⟩, ⟨a, a.2, rfl⟩, ?_⟩
    rw [← prop_3_3 Lm F S hS a _ rfl, ha]
    ext x
    exact congrArg (fun f => f x) (IntermediateField.coe_fixingSubgroupEquiv_apply (K := F) ⟨τ, hτ⟩)
  · rintro ⟨b, ⟨a, ha, hab⟩, rfl⟩
    rw [← prop_3_3 Lm F S hS ⟨a, ha⟩ b hab.symm]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact (artinMap Lm (primesAbove K F S) ⟨a, ha⟩).commutes ⟨y, hy⟩

/-- **The Artin isomorphism** $C_\mathfrak m \cong \mathrm{Gal}(L_\mathfrak m/K)$ of a class field of $P_\mathfrak m$. -/
def rayClassEquivGal (m : Modulus K) (Lm : Type) [Field Lm] [NumberField Lm] [Algebra K Lm]
    [IsAbelianGalois K Lm] (hLm : IsClassFieldOf Lm m (rayPrincipal m)) : RayClassGroup m ≃* Gal(Lm/K) :=
  let f : coprimeIdeals m →* Gal(Lm/K) := artinMap Lm m.finiteSupport
  have hker : (rayPrincipal m).subgroupOf (coprimeIdeals m) = f.ker := hLm.ker_eq.symm
  (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective f hLm.surjective)

theorem rayClassEquivGal_mk (m : Modulus K) (Lm : Type) [Field Lm] [NumberField Lm] [Algebra K Lm]
    [IsAbelianGalois K Lm] (hLm : IsClassFieldOf Lm m (rayPrincipal m)) (y : coprimeIdeals m) :
    rayClassEquivGal m Lm hLm (QuotientGroup.mk y) = artinMap Lm m.finiteSupport y := rfl

/-- **The image of $\mathrm{Nm}(C_{F,\mathfrak m})$ in $\mathrm{Gal}(L_\mathfrak m/K)$ is $\mathrm{Gal}(L_\mathfrak m/F)$**
(Milne, *CFT*, V, proof of Corollary 3.7). -/
theorem mem_normRayClass_iff (m : Modulus K) (Lm : Type) [Field Lm] [NumberField Lm] [Algebra K Lm]
    [IsAbelianGalois K Lm] (hLm : IsClassFieldOf Lm m (rayPrincipal m)) (F : IntermediateField K Lm)
    (c : RayClassGroup m) :
    c ∈ normRayClass m F ↔ rayClassEquivGal m Lm hLm c ∈ F.fixingSubgroup := by
  have hfin : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  have hS : ∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K Lm := hLm.unramifiedOutside.1
  let ψ : coprimeIdeals m →* Gal(Lm/K) := artinMap Lm m.finiteSupport
  have hker : ψ.ker = (rayPrincipal m).subgroupOf (coprimeIdeals m) := hLm.ker_eq
  have hN : ∀ n ∈ normIdeals K F m.finiteSupport, n ∈ coprimeIdeals m := fun n hn => by
    rw [coprimeIdeals_eq_sIdeals]; exact normIdeals_le K F _ hn
  induction c using QuotientGroup.induction_on with | H y => ?_
  rw [rayClassEquivGal_mk, mem_fixingSubgroup_iff_exists_norm Lm F hfin hS]
  constructor
  · rintro ⟨y', hy', hyc⟩
    have hy'' : (y' : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ rayPrincipal m ⊔ normIdeals K F m.finiteSupport := hy'
    obtain ⟨p, hp, n, hn, hpn⟩ := Subgroup.mem_sup.1 hy''
    refine ⟨⟨n, normIdeals_le K F _ hn⟩, hn, ?_⟩
    have hP : (⟨p, rayPrincipal_le m hp⟩ : coprimeIdeals m) ∈ ψ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]; exact hp
    have h1 : y' = (⟨p, rayPrincipal_le m hp⟩ : coprimeIdeals m) * ⟨n, hN n hn⟩ := Subtype.ext hpn.symm
    have h2 : ψ y' = ψ ⟨n, hN n hn⟩ := by
      rw [h1, map_mul, MonoidHom.mem_ker.1 hP, one_mul]
    have h3 : ψ y = ψ y' := by
      have : (QuotientGroup.mk y : RayClassGroup m) = QuotientGroup.mk y' := hyc.symm
      have h4 := congrArg (rayClassEquivGal m Lm hLm) this
      rwa [rayClassEquivGal_mk, rayClassEquivGal_mk] at h4
    exact (h3.trans h2).symm
  · rintro ⟨b, hb, hby⟩
    have hbc : (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ coprimeIdeals m := hN _ hb
    have hker' : (y * (⟨b, hbc⟩ : coprimeIdeals m)⁻¹) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : ψ ⟨b, hbc⟩ = ψ y := hby
      rw [this, mul_inv_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hker'
    refine ⟨y, ?_, rfl⟩
    show (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ rayPrincipal m ⊔ normIdeals K F m.finiteSupport
    have : (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) * (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹) * b := by
      rw [inv_mul_cancel_right]
    rw [this]
    exact Subgroup.mul_mem_sup (by simpa using hker') hb

end NormGroup

/-! ## Corollary 3.7 -/

/-- **Corollary 3.7** (Milne, *CFT*, V, p. 158; proved from the existence theorem with the Artin isomorphism and the
Chebotarev density theorem): fix $\mathfrak m$ and a ray class field $L_\mathfrak m$ (the class field of
$i(K_{\mathfrak m,1})$). Then $L \mapsto \mathrm{Nm}(C_{L,\mathfrak m})$ is a bijection from the subextensions of
$L_\mathfrak m/K$ to the subgroups of $C_\mathfrak m$, with $L_1 \subseteq L_2 \iff \mathrm{Nm}(C_{L_1,\mathfrak m})
\supseteq \mathrm{Nm}(C_{L_2,\mathfrak m})$, $\mathrm{Nm}(C_{L_1L_2,\mathfrak m}) = \mathrm{Nm}(C_{L_1,\mathfrak m}) \cap
\mathrm{Nm}(C_{L_2,\mathfrak m})$ and $\mathrm{Nm}(C_{L_1\cap L_2,\mathfrak m}) = \mathrm{Nm}(C_{L_1,\mathfrak m})\cdot
\mathrm{Nm}(C_{L_2,\mathfrak m})$. -/
@[kb "milne2020cft" "Ch. V, Corollary 3.7"]
theorem cor_3_7 (hE : ExistenceTheoremArtin K) (m : Modulus K) (Lm : Type) [Field Lm] [NumberField Lm]
    [Algebra K Lm] [IsAbelianGalois K Lm] (hLm : IsClassFieldOf Lm m (rayPrincipal m)) :
    Function.Bijective (fun F : IntermediateField K Lm => normRayClass m F) ∧
      (∀ F₁ F₂ : IntermediateField K Lm, F₁ ≤ F₂ ↔ normRayClass m F₂ ≤ normRayClass m F₁) ∧
      (∀ F₁ F₂ : IntermediateField K Lm,
        normRayClass m ↥(F₁ ⊔ F₂) = normRayClass m F₁ ⊓ normRayClass m F₂) ∧
      (∀ F₁ F₂ : IntermediateField K Lm,
        normRayClass m ↥(F₁ ⊓ F₂) = normRayClass m F₁ ⊔ normRayClass m F₂) := by
  have _ := hE
  let e := rayClassEquivGal m Lm hLm
  have hkey : ∀ F : IntermediateField K Lm,
      normRayClass m F = F.fixingSubgroup.comap (e : RayClassGroup m →* Gal(Lm/K)) := fun F =>
    Subgroup.ext fun c => mem_normRayClass_iff m Lm hLm F c
  let Φ : IntermediateField K Lm ≃o (Subgroup (RayClassGroup m))ᵒᵈ :=
    IsGalois.intermediateFieldEquivSubgroup.trans e.comapSubgroup.dual
  have hΦ : ∀ F : IntermediateField K Lm, (Φ F).ofDual = normRayClass m F := fun F => (hkey F).symm
  refine ⟨?_, fun F₁ F₂ => ?_, fun F₁ F₂ => ?_, fun F₁ F₂ => ?_⟩
  · have : (fun F : IntermediateField K Lm => normRayClass m F) = OrderDual.ofDual ∘ Φ :=
      funext fun F => (hΦ F).symm
    rw [this]
    exact OrderDual.ofDual.bijective.comp Φ.bijective
  · rw [← hΦ, ← hΦ, OrderDual.ofDual_le_ofDual, Φ.le_iff_le]
  · rw [← hΦ, ← hΦ, ← hΦ, Φ.map_sup, ofDual_sup]
  · rw [← hΦ, ← hΦ, ← hΦ, Φ.map_inf, ofDual_inf]

/-! ## Remark 3.8: the conductor -/

section Conductor

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- **The Artin map factors through $C_\mathfrak m$** (Milne, *CFT*, V, Remark 3.8): the primes not dividing
$\mathfrak m_0$ are unramified in $L$ and $\psi_{L/K} : I^{S(\mathfrak m)} \to \mathrm{Gal}(L/K)$ is trivial on
$i(K_{\mathfrak m,1})$. -/
def ArtinFactorsThrough (m : Modulus K) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L) ∧
    ∀ a : Kˣ, a ∈ congruenceSubgroup m → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals m.finiteSupport,
      artinMap L m.finiteSupport ⟨_, h⟩ = 1

/-- **The conductor** $\mathfrak f(L/K)$ (Milne, *CFT*, V, Remark 3.8, p. 158): the smallest modulus (for
divisibility) such that $\psi_{L/K}$ factors through $C_\mathfrak f$. -/
@[kb "milne2020cft" "Ch. V, Remark 3.8 (conductor of an abelian extension)"]
def IsArtinConductor (f : Modulus K) : Prop :=
  ArtinFactorsThrough L f ∧ ∀ m : Modulus K, ArtinFactorsThrough L m → f.Dvd m

/-- Enlarging a modulus (in the sense of divisibility) shrinks the congruence subgroup. -/
theorem congruenceSubgroup_le_of_dvd {f m : Modulus K} (hd : f.Dvd m) :
    congruenceSubgroup m ≤ congruenceSubgroup f := by
  rintro a ⟨h1, h2⟩
  refine ⟨fun v hv => h1 v (hd.2 hv), fun v hv => ?_⟩
  have hvm : v.asIdeal ∣ m.finite := hv.trans hd.1
  refine (h2 v hvm).trans ?_
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  unfold Modulus.ord
  refine Associates.count_le_count_of_le ?_ (Associates.irreducible_mk.2 v.irreducible) ?_
  · exact (Associates.mk_ne_zero.2 m.finite_ne_bot)
  · exact Associates.mk_le_mk_iff_dvd.2 hd.1

/-- The Artin map of a finite abelian extension with a defining modulus factors through that modulus. -/
theorem IsDefiningModulus.artinFactorsThrough {m : Modulus K} (h : IsDefiningModulus L m) :
    ArtinFactorsThrough L m := by
  refine ⟨fun v hv => ?_, fun a ha ha' => ?_⟩
  · by_contra hc
    exact hv (show v ∈ m.finiteSupport by rw [h.finiteSupport_eq]; exact hc)
  · have : (⟨_, ha'⟩ : sIdeals m.finiteSupport) ∈ (artinMap L m.finiteSupport).ker := by
      rw [h.ker_eq, Subgroup.mem_subgroupOf]
      exact (le_sup_left : rayPrincipal m ≤ _) ⟨a, ha, rfl⟩
    exact this

/-- If the Artin map factors through `f` and `f` divides `m`, then it factors through `m`. -/
theorem ArtinFactorsThrough.of_dvd {f m : Modulus K} (h : ArtinFactorsThrough L f) (hd : f.Dvd m) :
    ArtinFactorsThrough L m := by
  refine ⟨fun v hv => h.1 v (fun hvf => hv ?_), fun a ha ha' => ?_⟩
  · exact (show v.asIdeal ∣ m.finite from hvf.trans hd.1)
  · have hsub : f.finiteSupport ⊆ m.finiteSupport := fun v hv => (hv.trans hd.1 : v.asIdeal ∣ m.finite)
    exact h.2 a (congruenceSubgroup_le_of_dvd hd ha) (fun v hv => ha' v (hsub hv))

/-- **A finite abelian extension whose Artin map factors through `m` embeds into any extension `M` that is
unramified outside `m` and in which a trivial Frobenius element at `v ∤ m` means a trivial class in `C_m`**
(the Chebotarev argument of Milne, *CFT*, V, Remark 3.8). -/
theorem nonempty_algHom_of_artinFactorsThrough {m : Modulus K} (hL : ArtinFactorsThrough L m)
    (M : Type) [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    (hMu : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finiteSupport → v ∈ unramifiedPrimes K M)
    (hM : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), artinFrob M v = 1 →
      rayClass m v hv = 1) : Nonempty (L →ₐ[K] M) := by
  refine nonempty_algHom_of_artinFrob L M m.finiteSupport (Ideal.finite_factors m.finite_ne_bot) hL.1 hMu ?_
  intro v hvS hM1
  have hv : ¬ v.asIdeal ∣ m.finite := hvS
  have h2 : coprimePrime m v hv ∈ (rayPrincipal m).subgroupOf (coprimeIdeals m) :=
    (QuotientGroup.eq_one_iff _).1 (hM v hv hM1)
  rw [Subgroup.mem_subgroupOf] at h2
  obtain ⟨a, ha, hax⟩ := h2
  have hmem : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals m.finiteSupport := by
    rw [hax]; exact (coprimePrime m v hv).2
  have h3 := hL.2 a ha hmem
  have h4 : artinMap L m.finiteSupport (coprimePrime m v hv) = artinFrob L v :=
    artinMap_prime L m.finiteSupport v (coprimePrime m v hv) rfl
  rw [← h4, ← h3]
  exact congrArg _ (Subtype.ext hax.symm)

variable (K) in
/-- **Remark 3.8** (named statement; Milne, *CFT*, V, Remark 3.8, p. 158): every finite abelian extension has a
conductor $\mathfrak f(L/K)$, and it is divisible exactly by the primes (finite and real) ramifying in $L$. -/
@[kb "milne2020cft" "Ch. V, Remark 3.8 (input)"]
structure Remark3_8 : Prop where
  exists_conductor : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
    ∃ f : Modulus K, IsArtinConductor L f
  support : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (f : Modulus K),
    IsArtinConductor L f → (f.finiteSupport = (unramifiedPrimes K L)ᶜ ∧
      ∀ w : InfinitePlace K, w ∈ f.infinite ↔ InfinitePlace.RamifiesIn L w)

/-- **Remark 3.8**, "the subfields of the ray class field $L_\mathfrak m$ containing $K$ are those with conductor
$\mathfrak f \mid \mathfrak m$" (Milne, *CFT*, V, p. 158, with footnote 3: proved by the Chebotarev density theorem):
a finite abelian extension $L/K$ with conductor $\mathfrak f$ embeds in $L_\mathfrak m$ iff $\mathfrak f \mid \mathfrak m$. -/
@[kb "milne2020cft" "Ch. V, Remark 3.8 (subfields of L_m are those with conductor dividing m)"]
theorem remark_3_8_subfield (m : Modulus K) (Lm : Type) [Field Lm] [NumberField Lm] [Algebra K Lm]
    [IsAbelianGalois K Lm] (hLm : IsClassFieldOf Lm m (rayPrincipal m)) (f : Modulus K)
    (hf : IsArtinConductor L f) : Nonempty (L →ₐ[K] Lm) ↔ f.Dvd m := by
  constructor
  · rintro ⟨φ⟩
    letI : Algebra L Lm := φ.toRingHom.toAlgebra
    haveI : IsScalarTower K L Lm := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
    refine hf.2 m ⟨fun v hv => unramifiedPrimes_subset_of_tower K L Lm (hLm.unramifiedOutside.1 v hv),
      fun a ha ha' => ?_⟩
    have h1 : artinMap Lm m.finiteSupport ⟨_, ha'⟩ = 1 := by
      have : (⟨_, ha'⟩ : sIdeals m.finiteSupport) ∈ (artinMap Lm m.finiteSupport).ker := by
        rw [hLm.ker_eq, Subgroup.mem_subgroupOf]
        exact ⟨a, ha, rfl⟩
      exact this
    rw [artinMap_restrict L Lm m.finiteSupport (fun v hv => hLm.unramifiedOutside.1 v hv), h1, map_one]
  · intro hd
    exact nonempty_algHom_of_artinFactorsThrough L (ArtinFactorsThrough.of_dvd L hf.1 hd) Lm hLm.unramifiedOutside.1
      (fun v hv h => rayClass_eq_one_of_artinFrob_eq_one Lm hLm v hv h)

/-- **Remark 3.8**, "every abelian extension of $K$ is contained in $L_\mathfrak m$ for some $\mathfrak m$" (Milne,
*CFT*, V, p. 158; proved from the reciprocity law, the existence theorem and Chebotarev). -/
@[kb "milne2020cft" "Ch. V, Remark 3.8 (every abelian extension lies in a ray class field)"]
theorem remark_3_8_contained (hR : ReciprocityLaw K) (hE : ExistenceTheoremArtin K) :
    ∃ (m : Modulus K) (Lm : Type) (_ : Field Lm) (_ : NumberField Lm) (_ : Algebra K Lm)
      (_ : IsAbelianGalois K Lm), IsClassFieldOf Lm m (rayPrincipal m) ∧ Nonempty (L →ₐ[K] Lm) := by
  obtain ⟨m, hm⟩ := hR.exists_definingModulus L
  obtain ⟨Lm, _, _, _, _, hLm, -⟩ := hE.exists_field m (rayPrincipal m) ⟨le_rfl, rayPrincipal_le m⟩
  exact ⟨m, Lm, inferInstance, inferInstance, inferInstance, inferInstance, hLm,
    nonempty_algHom_of_artinFactorsThrough L hm.artinFactorsThrough Lm hLm.unramifiedOutside.1
      (fun v hv h => rayClass_eq_one_of_artinFrob_eq_one Lm hLm v hv h)⟩

end Conductor

/-! ## Examples 3.9–3.11 -/

/-- **Example 3.9** (Milne, *CFT*, V, p. 159): the ray class field for $\mathfrak m = 1$ is the Hilbert class field: it
is unramified at all primes, including the real ones, with Artin isomorphism $C \cong \mathrm{Gal}(H/K)$
(`IsHilbertClassField`), and every finite abelian extension of $K$ unramified at all primes embeds in it. Proved from
the reciprocity law and the existence theorem with the Artin isomorphism. -/
@[kb "milne2020cft" "Ch. V, Example 3.9 (the Hilbert class field)"]
theorem example_3_9_hilbert (hR : ReciprocityLaw K) (hE : ExistenceTheoremArtin K) :
    ∃ (H : Type) (_ : Field H) (_ : NumberField H) (_ : Algebra K H) (_ : IsAbelianGalois K H),
      HilbertClassField.IsHilbertClassField K H ∧
      ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
        (∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K L) → IsUnramifiedAtInfinitePlaces K L →
          Nonempty (L →ₐ[K] H) := by
  obtain ⟨H, _, _, _, _, hH, -⟩ :=
    hE.exists_field (Modulus.one K) (rayPrincipal (Modulus.one K)) ⟨le_rfl, rayPrincipal_le _⟩
  have hnd : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (Modulus.one K).finite := fun v hv =>
    v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd hv))
  have hunrH : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K H := fun v =>
    hH.unramifiedOutside.1 v (hnd v)
  have hinfH : IsUnramifiedAtInfinitePlaces K H := by
    refine ⟨fun w' => ?_⟩
    by_contra hcon
    obtain ⟨hc, hr⟩ := InfinitePlace.isRamified_iff.1 hcon
    exact hH.unramifiedOutside.2 (w'.comap (algebraMap K H)) (fun h => h) ⟨hr, w', rfl, hc⟩
  refine ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, ⟨hunrH, hinfH, ?_⟩, ?_⟩
  · let m := Modulus.one K
    let f : coprimeIdeals m →* Gal(H/K) := artinMap H m.finiteSupport
    have hker : (rayPrincipal m).subgroupOf (coprimeIdeals m) = f.ker := hH.ker_eq.symm
    let e : RayClassGroup m ≃* Gal(H/K) :=
      (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective f hH.surjective)
    refine ⟨(rayClassGroupOneEquiv K).symm.trans e, fun 𝔭 Q => ?_⟩
    have hv := hnd 𝔭
    have h1 : (rayClassGroupOneEquiv K).symm (HilbertClassField.primeClass K 𝔭) = rayClass m 𝔭 hv :=
      (MulEquiv.symm_apply_eq _).2 (rayClassGroupEquivClassGroup_rayClass m rfl rfl 𝔭 hv).symm
    show e ((rayClassGroupOneEquiv K).symm (HilbertClassField.primeClass K 𝔭)) = _
    rw [h1, ← artinFrob_eq H 𝔭 (hunrH 𝔭) Q]
    exact artinMap_prime H m.finiteSupport 𝔭 (coprimePrime m 𝔭 hv) rfl
  · intro L _ _ _ _ hunr hinf
    obtain ⟨mL, hmL⟩ := hR.exists_definingModulus L
    have h0 : mL.finite = ⊤ := by
      by_contra h
      obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal mL.finite h
      have hne : p ≠ ⊥ := fun e => mL.finite_ne_bot (le_bot_iff.mp (e ▸ hle))
      let v : HeightOneSpectrum (𝓞 K) := ⟨p, hp.isPrime, hne⟩
      have hv : v ∈ mL.finiteSupport := Ideal.dvd_iff_le.mpr hle
      rw [hmL.finiteSupport_eq] at hv
      exact hv (hunr v)
    have hi : mL.infinite = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
      obtain ⟨hr, w', hw', hc⟩ := (hmL.infinite_iff w).mp hw
      exact (InfinitePlace.isRamified_iff.mpr ⟨hc, hw' ▸ hr⟩) (hinf.isUnramified w')
    have hmeq : mL = Modulus.one K := by
      cases mL
      simp only at h0 hi
      subst h0 hi
      rfl
    subst hmeq
    exact nonempty_algHom_of_artinFactorsThrough L hmL.artinFactorsThrough H hH.unramifiedOutside.1
      (fun v hv h => rayClass_eq_one_of_artinFrob_eq_one H hH v hv h)

/-- The structure map $\mathbb Z \to \mathcal O_{\mathbb Q}$ is surjective. -/
theorem algebraMap_int_ratInt_surjective : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := by
  intro x
  exact ⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by simp)⟩

/-- The ring of integers of $\mathbb Q$ is formally unramified over $\mathbb Z$ (the structure map is surjective). -/
instance formallyUnramified_int_ringOfIntegers_rat : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
  Algebra.FormallyUnramified.of_surjective (A := ℤ) (Algebra.ofId ℤ (𝓞 ℚ)) algebraMap_int_ratInt_surjective

/-- **Example 3.9** (Milne, *CFT*, V, p. 159): the Hilbert class field of $\mathbb Q$ is $\mathbb Q$: $\mathbb Q$ is its own
Hilbert class field (class number one, `HilbertClassField.isHilbertClassField_self_of_classNumber_eq_one`), and $\mathbb Q$
has no nontrivial extension unramified at all finite primes (Minkowski, Mathlib's
`NumberField.exists_not_isUnramifiedIn`). -/
@[kb "milne2020cft" "Ch. V, Example 3.9 (the Hilbert class field of Q is Q)"]
theorem example_3_9_rat :
    HilbertClassField.IsHilbertClassField ℚ ℚ ∧
      ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ unramifiedPrimes ℚ L) → Module.finrank ℚ L = 1 := by
  refine ⟨HilbertClassField.isHilbertClassField_self_of_classNumber_eq_one Rat.classNumber_eq, ?_⟩
  intro L _ _ _ h
  by_contra hne
  obtain ⟨p, hp, hnu⟩ := NumberField.exists_not_isUnramifiedIn (K := L) (𝒪 := 𝓞 L) hne
  unfold Algebra.IsUnramifiedIn at hnu
  push Not at hnu
  obtain ⟨P, hP, hlo, hnP⟩ := hnu
  have := hP
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    exact hnP Algebra.isUnramifiedAt_bot
  let q : Ideal (𝓞 ℚ) := P.under (𝓞 ℚ)
  have hqp : q.IsPrime := Ideal.IsPrime.under (𝓞 ℚ) P
  have hq : q ≠ ⊥ := by
    intro h0
    have : P.LiesOver (⊥ : Ideal (𝓞 ℚ)) := ⟨h0.symm⟩
    exact hPbot (Ideal.eq_bot_of_liesOver_bot (𝓞 ℚ) P)
  let v : HeightOneSpectrum (𝓞 ℚ) := ⟨q, hqp, hq⟩
  have h1 : Algebra.IsUnramifiedAt (𝓞 ℚ) P := h v P hP ⟨rfl⟩
  have : Algebra.IsUnramifiedAt ℤ q := inferInstance
  exact hnP (Algebra.IsUnramifiedAt.comp (R := ℤ) q P)

/-- **Example 3.9** (named statement; Milne, *CFT*, V, p. 159): the Hilbert class field of $\mathbb Q(\sqrt{-5})$ is
$\mathbb Q(\sqrt{-1}, \sqrt 5)$. Stated for $K = \mathbb Q(s)$, $s^2 = -5$, and a quadratic extension $H$ of $K$
containing $i$ with $i^2 = -1$ (then $H = K(i) = K(\sqrt 5)$). -/
@[kb "milne2020cft" "Ch. V, Example 3.9 (Hilbert class field of Q(√-5); input)"]
structure Example3_9_sqrt_neg5 : Prop where
  isHilbertClassField : ∀ (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H]
    [IsGalois K H] (s : K) (i : H), s ^ 2 = -5 → Module.finrank ℚ K = 2 → i ^ 2 = -1 →
    Module.finrank K H = 2 → HilbertClassField.IsHilbertClassField K H

/-! ## Helpers for the examples over the rationals -/

section RatExamples

/-- A nonzero prime ideal of $\mathcal O_{\mathbb Q}$ is generated by its rational prime. -/
theorem asIdeal_eq_span_ratPrime (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((MilneANT.ratPrime v : ℕ) : 𝓞 ℚ)} := by
  have h1 := Rat.HeightOneSpectrum.span_natGenerator v
  ext x
  rw [Ideal.mem_span_singleton, ← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)),
    ← h1, Ideal.mem_span_singleton, ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast]

/-- A natural number lies in a prime ideal of $\mathcal O_{\mathbb Q}$ iff its rational prime divides it. -/
theorem natCast_mem_iff_ratPrime_dvd (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ v.asIdeal ↔ MilneANT.ratPrime v ∣ n := by
  rw [asIdeal_eq_span_ratPrime v, Ideal.mem_span_singleton,
    ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast, map_natCast]
  exact Int.natCast_dvd_natCast

/-- The principal ideal generated by a rational prime is the corresponding prime ideal. -/
theorem toPrincipalIdeal_ratPrime (v : HeightOneSpectrum (𝓞 ℚ)) :
    toPrincipalIdeal (𝓞 ℚ) ℚ (Units.mk0 ((MilneANT.ratPrime v : ℕ) : ℚ)
      (Nat.cast_ne_zero.mpr (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero)) = primeUnitIdeal v := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change _ = ((v.asIdeal : Ideal (𝓞 ℚ)) : FractionalIdeal (𝓞 ℚ)⁰ ℚ)
  rw [asIdeal_eq_span_ratPrime v, FractionalIdeal.coeIdeal_span_singleton]
  simp

/-- Every nonzero ideal of $\mathcal O_{\mathbb Q}$ is generated by a positive natural number. -/
theorem exists_nat_eq_span (I : Ideal (𝓞 ℚ)) (hI : I ≠ ⊥) :
    ∃ n : ℕ, n ≠ 0 ∧ I = Ideal.span {(n : 𝓞 ℚ)} := by
  haveI : IsPrincipalIdealRing (𝓞 ℚ) := NumberField.classNumber_eq_one_iff.1 Rat.classNumber_eq
  set g := Submodule.IsPrincipal.generator I with hgdef
  have hI' : Ideal.span {g} = I := Ideal.span_singleton_generator I
  set e := Rat.ringOfIntegersEquiv with he
  have key : g = ((e g).natAbs : 𝓞 ℚ) ∨ g = -((e g).natAbs : 𝓞 ℚ) := by
    rcases Int.natAbs_eq (e g) with h | h
    · left
      exact e.injective (by rw [map_natCast]; exact h)
    · right
      exact e.injective (by rw [map_neg, map_natCast]; exact h)
  refine ⟨(e g).natAbs, ?_, ?_⟩
  · intro h0
    have h1 : e g = 0 := Int.natAbs_eq_zero.1 h0
    have h2 : g = 0 := e.injective (by rw [h1, map_zero])
    apply hI
    rw [← hI', h2]
    simp
  · rw [← hI', Ideal.span_singleton_eq_span_singleton]
    rcases key with h | h
    · exact Associated.of_eq h
    · exact ⟨-1, by rw [h]; simp⟩

/-- A nonzero integer congruent to `1` modulo `m₀` and positive at the real places of `m` is $\equiv 1 \bmod^\times \mathfrak m$. -/
theorem mem_congruenceSubgroup_of_integral {K : Type} [Field K] [NumberField K] (m : Modulus K) (t : 𝓞 K)
    (ht0 : t ≠ 0) (ht : t - 1 ∈ m.finite)
    (hpos : ∀ (v : InfinitePlace K) (hv : v ∈ m.infinite),
      IsPositiveAt K v (m.isReal_of_mem v hv) (algebraMap (𝓞 K) K t)) :
    Units.mk0 (algebraMap (𝓞 K) K t) (by simpa using ht0) ∈ congruenceSubgroup m := by
  refine ⟨fun v hv => hpos v hv, fun v hv => ?_⟩
  have h1 := (mem_finite_iff_intValuation m _).1 ht v
  have h2 : algebraMap (𝓞 K) K t - 1 = algebraMap (𝓞 K) K (t - 1) := by
    rw [map_sub, map_one]
  simp only [Units.val_mk0]
  rw [h2, HeightOneSpectrum.valuation_of_algebraMap]
  exact h1

/-- Helper: a prime of the rationals not dividing `m` is unramified in the cyclotomic field of level `m`
(Mathlib's discriminant criterion; compare `mem_unramifiedPrimes_cyclotomic` in the file on `L`-series). -/
theorem unramifiedPrimes_cyclotomic_of_not_dvd (m : ℕ) [NeZero m] (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ MilneANT.ratPrime v ∣ m) : v ∈ unramifiedPrimes ℚ L := by
  have hp : (MilneANT.ratPrime v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have hpz : Prime (MilneANT.ratPrime v : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnd : ¬ (MilneANT.ratPrime v : ℤ) ∣ NumberField.discr L := by
    intro h
    have h1 : MilneANT.ratPrime v ∣ (NumberField.discr L).natAbs := by
      simpa [Int.natCast_dvd] using h
    rw [IsCyclotomicExtension.Rat.natAbs_discr m L] at h1
    have h2 : MilneANT.ratPrime v ∣ m ^ m.totient :=
      h1.trans (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _)))
    exact hv (hp.dvd_of_dvd_pow h2)
  have key := (NumberField.not_dvd_discr_iff_forall_liesOver L (𝓞 L) hpz).mp hnd
  intro Q hQ hQo
  have hpv : ((MilneANT.ratPrime v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
    (natCast_mem_iff_ratPrime_dvd v _).2 dvd_rfl
  have hQm : Q.IsMaximal := hQ.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have hpQ : (MilneANT.ratPrime v : ℤ) ∈ Q.under ℤ := by
    have h1 : ((MilneANT.ratPrime v : ℕ) : 𝓞 ℚ) ∈ Q.under (𝓞 ℚ) := by
      rw [← Ideal.LiesOver.over (p := v.asIdeal) (P := Q)]; exact hpv
    rw [Ideal.mem_comap] at h1 ⊢
    simpa using h1
  have hmax : (Ideal.span {(MilneANT.ratPrime v : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime hpz.ne_zero).mpr hpz |>.isMaximal (by simpa using hpz.ne_zero)
  have heq : Ideal.span {(MilneANT.ratPrime v : ℤ)} = Q.under ℤ :=
    hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      (by rw [Ideal.span_singleton_le_iff_mem]; exact hpQ)
  have : Q.LiesOver (Ideal.span {(MilneANT.ratPrime v : ℤ)}) := ⟨heq⟩
  have := key Q hQm inferInstance
  exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ Q

/-- The real place of the rationals is positive at `q` iff `0 < q`. -/
theorem isPositiveAt_rat_iff (v : InfinitePlace ℚ) (hv : v.IsReal) (q : ℚ) : IsPositiveAt ℚ v hv q ↔ 0 < q := by
  unfold IsPositiveAt
  rw [Subsingleton.elim (InfinitePlace.embedding_of_isReal hv) (Rat.castHom ℝ)]
  simp

end RatExamples

/-- **Example 3.10** (Milne, *CFT*, V, p. 159): the reciprocity law implies the **Kronecker–Weber theorem**: every finite
abelian extension of $\mathbb Q$ embeds in a cyclotomic field. (Proof: a defining modulus $\infty^\epsilon(m)$ of $L$; the
primes $p \equiv 1 \bmod m$ are in $i(\mathbb Q_{\infty(m),1})$, so they split in $L$; they are the primes splitting in
$\mathbb Q(\zeta_m)$; by Chebotarev, $L \subseteq \mathbb Q(\zeta_m)$.) -/
@[kb "milne2020cft" "Ch. V, Example 3.10 (Kronecker–Weber from the reciprocity law)"]
theorem example_3_10_kroneckerWeber (hR : ReciprocityLaw ℚ) (L : Type) [Field L] [NumberField L]
    [IsAbelianGalois ℚ L] : ∃ m : ℕ, 0 < m ∧ Nonempty (L →ₐ[ℚ] CyclotomicField m ℚ) := by
  obtain ⟨mL, hm⟩ := hR.exists_definingModulus L
  obtain ⟨n, hn, hfin⟩ := exists_nat_eq_span mL.finite mL.finite_ne_bot
  haveI : NeZero n := ⟨hn⟩
  haveI : IsAbelianGalois ℚ (CyclotomicField n ℚ) :=
    { toIsGalois := inferInstance, toIsMulCommutative := ⟨⟨MilneANT.cyclotomic_comm n⟩⟩ }
  refine ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  have hndiv : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ mL.finiteSupport → ¬ MilneANT.ratPrime v ∣ n := by
    intro v hv hdvd
    apply hv
    show v.asIdeal ∣ mL.finite
    rw [hfin, Ideal.dvd_span_singleton]
    exact (natCast_mem_iff_ratPrime_dvd v n).2 hdvd
  refine nonempty_algHom_of_artinFrob L (CyclotomicField n ℚ) mL.finiteSupport
    (Ideal.finite_factors mL.finite_ne_bot) hm.artinFactorsThrough.1
    (fun v hv => unramifiedPrimes_cyclotomic_of_not_dvd n _ v (hndiv v hv)) ?_
  intro v hvS h1
  have hunr : v ∈ unramifiedPrimes ℚ (CyclotomicField n ℚ) :=
    unramifiedPrimes_cyclotomic_of_not_dvd n _ v (hndiv v hvS)
  obtain ⟨Q⟩ : Nonempty (v.asIdeal.primesOver (𝓞 (CyclotomicField n ℚ))) := inferInstance
  have hfrob : frobAt ℚ (CyclotomicField n ℚ) v Q = 1 := by
    rw [← artinFrob_eq _ v hunr Q]; exact h1
  have h8 := (MilneANT.example_8_18 n (CyclotomicField n ℚ) v (hndiv v hvS) Q).1
  rw [hfrob] at h8
  set p := MilneANT.ratPrime v with hp
  have hpp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have h9 : IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ 1 =
      IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ p := by
    rw [pow_one]; exact h8
  have h10 := MilneANT.natCast_eq_of_zeta_pow_eq (IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)) h9
  have h11 : n ∣ p - 1 := by
    have : 1 ≡ p [MOD n] := (ZMod.natCast_eq_natCast_iff 1 p n).1 (by simpa using h10)
    exact (Nat.modEq_iff_dvd' hpp.one_lt.le).1 this
  -- the integer `p` is `≡ 1 mod^× mL`
  have ht : ((p : ℕ) : 𝓞 ℚ) - 1 ∈ mL.finite := by
    rw [hfin, Ideal.mem_span_singleton]
    have : ((p : ℕ) : 𝓞 ℚ) - 1 = ((p - 1 : ℕ) : 𝓞 ℚ) := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [this]
    exact Nat.cast_dvd_cast h11
  have ht0 : ((p : ℕ) : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hcs := mem_congruenceSubgroup_of_integral mL _ ht0 ht (fun w hw => by
    rw [isPositiveAt_rat_iff]
    have : algebraMap (𝓞 ℚ) ℚ ((p : ℕ) : 𝓞 ℚ) = (p : ℚ) := map_natCast _ _
    rw [this]
    exact_mod_cast hpp.pos)
  set a : ℚˣ := Units.mk0 (algebraMap (𝓞 ℚ) ℚ ((p : ℕ) : 𝓞 ℚ)) (by simpa using ht0) with ha
  have hpid : toPrincipalIdeal (𝓞 ℚ) ℚ a = primeUnitIdeal v := by
    rw [← toPrincipalIdeal_ratPrime v]
    congr 1
  have hmem : toPrincipalIdeal (𝓞 ℚ) ℚ a ∈ sIdeals mL.finiteSupport := by
    rw [hpid]; exact (coprimePrime mL v hvS).2
  have h12 := hm.artinFactorsThrough.2 a hcs hmem
  rw [← artinMap_prime L mL.finiteSupport v ⟨_, hmem⟩ hpid]
  exact h12

open scoped IsMulCommutative in
/-- The Artin map only depends on the underlying fractional ideal (not on the set `S`). -/
theorem artinMap_congr (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (S S' : Set (HeightOneSpectrum (𝓞 K))) (x : sIdeals S) (y : sIdeals S')
    (h : (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = y) : artinMap L S x = artinMap L S' y := by
  change (∏ᶠ v : HeightOneSpectrum (𝓞 K), artinFrob L v ^
      FractionalIdeal.count K v ((x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) =
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinFrob L v ^
      FractionalIdeal.count K v ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
  rw [h]

/-- The primes of $\mathbb Q$ dividing the modulus `ratModulus m` are those whose rational prime divides `m`. -/
theorem ratModulus_finiteSupport (m : ℕ) (hm : m ≠ 0) :
    (ratModulus m hm).finiteSupport = {v : HeightOneSpectrum (𝓞 ℚ) | MilneANT.ratPrime v ∣ m} := by
  ext v
  show v.asIdeal ∣ Ideal.span {(m : 𝓞 ℚ)} ↔ _
  rw [Ideal.dvd_span_singleton]
  exact natCast_mem_iff_ratPrime_dvd v m

/-- **The Artin map of $\mathbb Q(\zeta_m)$ on principal ideals** (from Milne, *CFT*, V, Example 3.2): for $a$ prime to
$m$, the Artin automorphism of the ideal $(a)$ acts on $\zeta_m$ through $\Psi(a)$, the class of $|a|$ modulo $m$. -/
theorem autToPow_artinMap_rat (m : ℕ) (hm : m ≠ 0) [NeZero m] (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsAbelianGalois ℚ L] (a : Gm m hm)
    (x : sIdeals (ratModulus m hm).finiteSupport)
    (hx : (x : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) = toPrincipalIdeal (𝓞 ℚ) ℚ (a : ℚˣ)) :
    (IsCyclotomicExtension.zeta_spec m ℚ L).autToPow ℚ (artinMap L (ratModulus m hm).finiteSupport x) =
      Psi m hm a := by
  have ha := (mem_Gm m hm _).1 ((absU_mem m hm _).2 a.2)
  set q : ℚ := (absU (a : ℚˣ) : ℚ) with hq
  have hqpos : 0 < q := absU_pos _
  have hnum : 0 < q.num := Rat.num_pos.2 hqpos
  set r := q.num.natAbs with hr
  set s := q.den with hs
  have hr0 : 0 < r := Int.natAbs_pos.2 hnum.ne'
  have hs0 : 0 < s := q.den_pos
  have hrz : ((r : ℕ) : ℤ) = q.num := Int.natAbs_of_nonneg hnum.le
  have hrs : ((r : ℚ) / s) = q := by
    have : (r : ℚ) = (q.num : ℚ) := by exact_mod_cast hrz
    rw [this, hs]; exact Rat.num_div_den q
  have hT : toPrincipalIdeal (𝓞 ℚ) ℚ (Units.mk0 ((r : ℚ) / s) (by positivity)) =
      toPrincipalIdeal (𝓞 ℚ) ℚ (a : ℚˣ) := by
    rw [← T_absU (a : ℚˣ)]
    congr 1
    apply Units.ext
    rw [Units.val_mk0]
    exact hrs.trans hq
  let x' : sIdeals {v : HeightOneSpectrum (𝓞 ℚ) | MilneANT.ratPrime v ∣ m} :=
    ⟨x.1, by rw [← ratModulus_finiteSupport m hm]; exact x.2⟩
  have h1 := example_3_2 m L r s ha.1 ha.2 hr0 hs0 x' (by rw [hT]; exact hx)
  rw [artinMap_congr L _ {v : HeightOneSpectrum (𝓞 ℚ) | MilneANT.ratPrime v ∣ m} x x' rfl, h1]
  apply Units.ext
  have hrZ : ((r : ℕ) : ZMod m) = (q.num : ZMod m) := by rw [← hrz]; simp
  have hP : ((Psi m hm a : (ZMod m)ˣ) : ZMod m) = (q.num : ZMod m) * ((q.den : ℕ) : ZMod m)⁻¹ := rfl
  rw [hP, Units.val_mul, ← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, hrZ]

/-- **Example 3.10** (Milne, *CFT*, V, p. 159, with footnote 4: from Example 1.8(c) and *ANT* 8.18): for $m$ odd or
divisible by $4$, $\mathbb Q(\zeta_m)$ is the ray class field of $\mathbb Q$ for the modulus $\infty(m)$: the Artin map
induces $C_{\infty(m)} \cong \mathrm{Gal}(\mathbb Q(\zeta_m)/\mathbb Q)$. -/
@[kb "milne2020cft" "Ch. V, Example 3.10 (Q(ζ_m) is the ray class field for ∞(m))"]
theorem example_3_10_cyclotomic (m : ℕ) (hm : m ≠ 0) (hm2 : m % 4 ≠ 2) (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsAbelianGalois ℚ L] :
    IsClassFieldOf L (ratModulus m hm) (rayPrincipal (ratModulus m hm)) := by
  have _ := hm2
  haveI : NeZero m := ⟨hm⟩
  have hirr := Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hm)
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ L
  have hinj : Function.Injective (hζ.autToPow ℚ) := fun g h hgh =>
    (IsCyclotomicExtension.autEquivPow L hirr).injective hgh
  refine ⟨⟨fun v hv => unramifiedPrimes_cyclotomic_of_not_dvd m L v ?_, fun w hw => ?_⟩, ?_, ?_⟩
  · intro hdvd
    apply hv
    rw [ratModulus_finiteSupport m hm]
    exact hdvd
  · exfalso
    apply hw
    show w.IsReal
    rw [Subsingleton.elim w Rat.infinitePlace]
    exact Rat.isReal_infinitePlace
  · intro σ
    obtain ⟨a, ha⟩ := Psi_surj m hm (hζ.autToPow ℚ σ)
    refine ⟨⟨toPrincipalIdeal (𝓞 ℚ) ℚ (a : ℚˣ), a.2⟩, hinj ?_⟩
    rw [autToPow_artinMap_rat m hm L a _ rfl, ha]
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    obtain ⟨c, hc⟩ := T_surj (x : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ)
    have hcG : c ∈ Gm m hm := by
      show toPrincipalIdeal (𝓞 ℚ) ℚ c ∈ coprimeIdeals (ratModulus m hm)
      rw [hc]; exact x.2
    have key := autToPow_artinMap_rat m hm L ⟨c, hcG⟩ x hc.symm
    have h1 : artinMap L (ratModulus m hm).finiteSupport x = 1 ↔ Psi m hm ⟨c, hcG⟩ = 1 := by
      rw [← key, ← map_one (hζ.autToPow ℚ)]
      exact hinj.eq_iff.symm
    rw [h1, ← Theta_iff_Psi, Theta_eq_one_iff]
    constructor
    · rintro ⟨d, hd, hdc⟩
      exact ⟨d, hd, by rw [hdc, hc]⟩
    · rintro ⟨d, hd, hdx⟩
      exact ⟨d, hd, by rw [hdx, hc]⟩

/-- The modulus of $\mathbb Q$ with finite part $(n)$ and infinite part the real place if `inf`. -/
def ratModulusOf (n : ℕ) (hn : n ≠ 0) (inf : Bool) : Modulus ℚ where
  finite := Ideal.span {(n : 𝓞 ℚ)}
  finite_ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  infinite := if inf then {v | v.IsReal} else ∅
  isReal_of_mem := fun v h => by
    cases inf
    · simp at h
    · simpa using h

/-- **Example 3.11** (named statement; Milne, *CFT*, V, p. 159): for $d \ne 1$ a square-free integer, the conductor of
$\mathbb Q(\sqrt d)$ is $|\Delta|$ if $d > 0$ and $\infty|\Delta|$ if $d < 0$, $\Delta$ the discriminant. Milne computes it
as the smallest $m$ with $\mathbb Q(\sqrt d) \subseteq \mathbb Q(\zeta_m)$ ($m = |\Delta|$, `mem_cyclotomic`). -/
@[kb "milne2020cft" "Ch. V, Example 3.11 (input)"]
structure Example3_11 : Prop where
  mem_cyclotomic : ∀ (L : Type) [Field L] [NumberField L] (d : ℤ) (s : L), Squarefree d → d ≠ 1 → s ^ 2 = d →
    Module.finrank ℚ L = 2 →
      Nonempty (L →ₐ[ℚ] CyclotomicField (discr L).natAbs ℚ) ∧
        ∀ n : ℕ, 0 < n → Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) → (discr L).natAbs ∣ n
  conductor : ∀ (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] (d : ℤ) (s : L), Squarefree d → d ≠ 1 →
    s ^ 2 = d → Module.finrank ℚ L = 2 →
      IsArtinConductor L (ratModulusOf (discr L).natAbs (by
        have : discr L ≠ 0 := discr_ne_zero L
        omega) (decide (d < 0)))

/-! ## Remark 3.12 and Exercise 3.15 -/

/-- The Takagi group $T(L/K, \mathfrak m) = i(K_{\mathfrak m,1})\cdot\mathrm{Nm}_{L/K}(I_L^{S(\mathfrak m)})$ (Milne, *CFT*,
V, Remark 3.12, p. 160). -/
@[kb "milne2020cft" "Ch. V, Remark 3.12 (the Takagi group)"]
def takagiGroup (L : Type) [Field L] [NumberField L] [Algebra K L] (m : Modulus K) :
    Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  rayPrincipal m ⊔ normIdeals K L m.finiteSupport

variable (K) in
/-- **Remark 3.12** (named statement; Milne, *CFT*, V, Remark 3.12, p. 160, Takagi and Artin): for a finite abelian
$L/K$ with conductor $\mathfrak f$ and moduli $\mathfrak m$ divisible by $\mathfrak f$ with $S(\mathfrak m)$ the set of
ramified primes, the Takagi group $T(L/K,\mathfrak m)$ does not depend on $\mathfrak m$,
$(I^{S(\mathfrak m)} : T(L/K,\mathfrak m)) = [L:K]$, and $T(L/K,\mathfrak m)$ is the kernel of the Artin map. -/
@[kb "milne2020cft" "Ch. V, Remark 3.12 (input)"]
structure Ch5Remark3_12 : Prop where
  takagi : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (f m : Modulus K),
    IsArtinConductor L f → f.Dvd m → m.finiteSupport = (unramifiedPrimes K L)ᶜ →
      takagiGroup L m = takagiGroup L f ∧
        ((takagiGroup L m).subgroupOf (sIdeals m.finiteSupport)).index = Module.finrank K L ∧
        (artinMap L m.finiteSupport).ker = (takagiGroup L m).subgroupOf (sIdeals m.finiteSupport)

/-- **$S$-class field** (Milne, *CFT*, V, Exercise 3.15, p. 160): for a finite set $S$ of primes disjoint from
$S(\mathfrak m)$ and $i(K_{\mathfrak m,1}) \cap I^{S \cup S(\mathfrak m)} \subseteq H \subseteq I^{S\cup S(\mathfrak m)}$:
(a) $L/K$ is finite abelian and the primes of $S$ split completely in $L$; (b) the primes (finite or real) not dividing
$\mathfrak m$ do not ramify in $L$; (c) the primes not in $S \cup S(\mathfrak m)$ that split in $L$ are those in $H$. -/
@[kb "milne2020cft" "Ch. V, Exercise 3.15 (S-class field)"]
structure IsSClassField (S : Set (HeightOneSpectrum (𝓞 K))) (m : Modulus K)
    (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] : Prop where
  split : ∀ v ∈ S, v ∈ splitPrimes K L
  unramified : UnramifiedOutside L m
  splits_iff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ m.finiteSupport →
    (v ∈ splitPrimes K L ↔ primeUnitIdeal v ∈ H)

variable (K) in
/-- **Exercise 3.15** (named statement; Milne, *CFT*, V, Exercise 3.15, p. 160): an $S$-class field exists for every
$H$ as above, it is unique (up to $K$-isomorphism), $I^{S\cup S(\mathfrak m)}/H \cong \mathrm{Gal}(L/K)$, and every
finite abelian $L$ in which the primes of $S$ split completely is the $S$-class field of some $H$ (for some
$\mathfrak m$). -/
@[kb "milne2020cft" "Ch. V, Exercise 3.15 (input)"]
structure Exercise3_15 : Prop where
  exists_field : ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ),
    S.Finite → Disjoint S m.finiteSupport → H ≤ sIdeals (S ∪ m.finiteSupport) →
    rayPrincipal m ⊓ sIdeals (S ∪ m.finiteSupport) ≤ H →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      IsSClassField S m H L ∧
        Nonempty (sIdeals (S ∪ m.finiteSupport) ⧸ H.subgroupOf (sIdeals (S ∪ m.finiteSupport)) ≃* Gal(L/K))
  unique : ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (L L' : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field L'] [NumberField L']
    [Algebra K L'] [IsAbelianGalois K L'], S.Finite → IsSClassField S m H L → IsSClassField S m H L' →
      Nonempty (L ≃ₐ[K] L')
  isSClassField : ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L], S.Finite → (∀ v ∈ S, v ∈ splitPrimes K L) →
      ∃ (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ), Disjoint S m.finiteSupport ∧
        IsSClassField S m H L

/-! ## The norm limitation theorem and the principal ideal theorem -/

variable (K) in
/-- **Theorem 3.16, the norm limitation theorem** (named statement; Milne, *CFT*, V, Theorem 3.16, p. 161; Grant and
Leitzel 1969): for a finite extension $L/K$ with maximal abelian subextension $L'$, and every defining modulus
$\mathfrak m$ of $L'/K$, $i(K_{\mathfrak m,1})\cdot\mathrm{Nm}_{L/K}(I_L^{S(\mathfrak m)}) =
i(K_{\mathfrak m,1})\cdot\mathrm{Nm}_{L'/K}(I_{L'}^{S(\mathfrak m)})$. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.16 (input)"]
structure NormLimitation : Prop where
  eq : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] (L' : IntermediateField K L) [IsAbelianGalois K L'],
    (∀ F : IntermediateField K L, IsAbelianGalois K F → F ≤ L') → ∀ m : Modulus K, IsDefiningModulus L' m →
      rayPrincipal m ⊔ normIdeals K L m.finiteSupport = rayPrincipal m ⊔ normIdeals K L' m.finiteSupport

variable (K) in
/-- **Theorem 3.17, the principal ideal theorem** (named statement; Milne, *CFT*, V, Theorem 3.17, p. 161; Hilbert's
conjecture, proved by Furtwängler 1930 from Artin's reduction and Theorem 3.19): every ideal of $K$ becomes principal
in the Hilbert class field of $K$.

**Proved** as `principalIdealTheorem`, in parts of the library that are not included in this release: a
Hilbert class field is $K$-isomorphic to the small Hilbert class field of the ported Yamaguchi library, where
principalization is proved (`ClassFieldTheory.ideals_becomePrincipalInSmallHilbertClassField`). -/
@[kb "milne2020cft" "Ch. V, Theorem 3.17 (input)"]
structure PrincipalIdealTheorem : Prop where
  isPrincipal : ∀ (H : Type) [Field H] [NumberField H] [Algebra K H] [IsGalois K H],
    HilbertClassField.IsHilbertClassField K H →
      ∀ I : Ideal (𝓞 K), (I.map (algebraMap (𝓞 K) (𝓞 H))).IsPrincipal

/-- **Proposition 3.18** (Milne, *CFT*, V, p. 162; Mathlib's `MonoidHom.transfer`): for $H \subseteq G$ of finite index,
the Verlagerung $V : G \to H/H'$ is a homomorphism (`MonoidHom.transfer` of the abelianization map) and does not depend
on the choice of coset representatives: for every transversal $T$ it is computed by the products over $T$
(Mathlib's `MonoidHom.transfer_def`). Mathlib uses left cosets $gH$, Milne right cosets $Hg$. -/
@[kb "milne2020cft" "Ch. V, Proposition 3.18"]
theorem prop_3_18 {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] (T : H.LeftTransversal) (g : G) :
    (Abelianization.of : H →* Abelianization H).transfer g =
      Subgroup.leftTransversals.diff (Abelianization.of : H →* Abelianization H) T (g • T) :=
  MonoidHom.transfer_def _ T g

/-- **Theorem 3.19** (named statement; Milne, *CFT*, V, Theorem 3.19, p. 163; Furtwängler 1930, Witt 1954): for a finite
group $G$ with commutator subgroup $H$, the transfer $V : G^{ab} \to H^{ab}$ is zero.

**Proved** as `theorem3_19`, in parts of the library that are not included in this release, from the ported Yamaguchi
`GroupTheory.Transfer.Witt.commutatorTransfer_eq_one_of_finite_abelianization` (Witt's proof). -/
@[kb "milne2020cft" "Ch. V, Theorem 3.19 (input)"]
structure Theorem3_19 : Prop where
  transfer_eq_one : ∀ (G : Type) [Group G] [Finite G] (g : G),
    (Abelianization.of : commutator G →* Abelianization (commutator G)).transfer g = 1

variable (K) in
/-- **Remark 3.20** (named statement; Milne, *CFT*, V, Remark 3.20, p. 163): there is a finite extension $L$ of $K$ of
degree dividing the class number $h$ in which every ideal of $K$ becomes principal.

**Proved elsewhere** (recorded, not imported): Yamaguchi
(`n-yamaguchi-0729/ClassFieldTheory`) `ClassFieldTheory.exists_smallHilbertClassField`
(`Nyll/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldExists.lean:24`),
`ClassFieldTheory.smallHilbertClassField_degree_eq_classNumber`
(`Nyll/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldDegree.lean:26`) and
`ClassFieldTheory.ideals_becomePrincipalInSmallHilbertClassField`
(`Nyll/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldPrincipalization.lean:25`) at
Yamaguchi commit `fbd320c`. Needed to apply it here: take Yamaguchi's small Hilbert class field of `K`, which has
degree equal to the class number and in which every ideal becomes principal; one must identify the extension type
used there with our `L`.

**Proved** as `remark3_20`, in parts of the library that are not included in this release, from the ported Yamaguchi
theorems. -/
@[kb "milne2020cft" "Ch. V, Remark 3.20 (input)"]
structure Remark3_20 : Prop where
  exists_field : ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
    Module.finrank K L ∣ classNumber K ∧ ∀ I : Ideal (𝓞 K), (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal

/-- **Remark 3.20 from the principal ideal theorem** (the Hilbert class field has degree $h$). -/
theorem remark3_20_of_principalIdealTheorem (hP : PrincipalIdealTheorem K)
    (hH : HilbertClassField.HilbertClassFieldExists K) : Remark3_20 K := by
  obtain ⟨H, _, _, _, _, hHcf⟩ := hH
  obtain ⟨ψ, -⟩ := hHcf.exists_artin
  refine ⟨⟨H, inferInstance, inferInstance, inferInstance, ?_, fun I => hP.isPrincipal H hHcf I⟩⟩
  refine dvd_of_eq ?_
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr ψ.toEquiv.symm, Nat.card_eq_fintype_card]
  rfl

/-! ## The Chebotarev density theorem and applications (pp. 164–165) -/

/-- **Theorem 3.23, the Chebotarev density theorem** (Milne, *CFT*, V, p. 164; proved in this library,
`NumberFieldKB.Chebotarev.chebotarev_unconditional`): for a finite Galois extension $L/K$ and a conjugacy class $C$ of
$G = \mathrm{Gal}(L/K)$, the primes $\mathfrak p$ with $(\mathfrak p, L/K) = C$ have (Dirichlet) density $|C|/|G|$. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.23"]
theorem theorem_3_23 (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (C : ConjClasses Gal(L/K)) :
    (frobSet K L C).HasDirichletDensity (Nat.card C.carrier / Nat.card Gal(L/K)) :=
  chebotarev_unconditional K L C

open scoped IsMulCommutative in
/-- **Theorem 3.23, abelian case** (Milne, *CFT*, V, p. 164): if $G$ is abelian, the primes $\mathfrak p$ with
$(\mathfrak p, L/K) = \sigma$ have density $1/(G:1)$. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.23 (abelian case)"]
theorem theorem_3_23_abelian (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (σ : Gal(L/K)) :
    {v : HeightOneSpectrum (𝓞 K) | v ∈ unramifiedPrimes K L ∧ artinFrob L v = σ}.HasDirichletDensity
      (1 / Nat.card Gal(L/K)) := by
  have h := chebotarev_unconditional K L (ConjClasses.mk σ)
  have hc : (ConjClasses.mk σ).carrier = {σ} := by
    ext τ
    simp only [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
      isConj_abelian (fun a b : Gal(L/K) => mul_comm a b), Set.mem_singleton_iff]
  have hset : frobSet K L (ConjClasses.mk σ) =
      {v : HeightOneSpectrum (𝓞 K) | v ∈ unramifiedPrimes K L ∧ artinFrob L v = σ} := by
    ext v
    simp only [frobSet, Set.mem_ofPred_eq]
    refine and_congr_right fun _ => ?_
    have : frobClass K L v = ConjClasses.mk (artinFrob L v) := rfl
    rw [this, ConjClasses.mk_eq_mk_iff_isConj, isConj_abelian (fun a b : Gal(L/K) => mul_comm a b)]
  rw [hset, hc] at h
  simpa using h

open Polynomial in
/-- **Corollary 3.24** (Milne, *CFT*, V, p. 164): a polynomial that splits into linear factors modulo $\mathfrak p$ for
all but finitely many primes $\mathfrak p$ splits in $K[X]$. Stated for monic $f \in \mathcal O_K[X]$ (a polynomial of
$K[X]$ becomes one after scaling the variable); no separability is assumed. -/
@[kb "milne2020cft" "Ch. V, Corollary 3.24"]
theorem cor_3_24 (f : Polynomial (𝓞 K)) (hf : f.Monic)
    (h : {v : HeightOneSpectrum (𝓞 K) |
      ¬ (f.map (algebraMap (𝓞 K) v.asIdeal.ResidueField)).Splits}.Finite) :
    (f.map (algebraMap (𝓞 K) K)).Splits := by
  classical
  refine Splits.of_splits_algebraMap (A := AlgebraicClosure K) (IsAlgClosed.splits _) ?_
  intro α hα
  have hfα : aeval α f = 0 := by
    rw [mem_rootSet] at hα
    have := hα.2
    rwa [aeval_map_algebraMap] at this
  have hint : IsIntegral (𝓞 K) α := ⟨f, hf, by rwa [aeval_def] at hfα⟩
  have hintK : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  set g := minpoly (𝓞 K) α with hg
  have hgdvd : g ∣ f := minpoly.isIntegrallyClosed_dvd hint hfα
  have hgmonic : g.Monic := minpoly.monic hint
  have hKg : minpoly K α = g.map (algebraMap (𝓞 K) K) := by
    have := minpoly.isIntegrallyClosed_eq_field_fractions' (K := K) hint
    exact this
  have hsep : (g.map (algebraMap (𝓞 K) K)).Separable := by
    rw [← hKg]; exact Algebra.IsSeparable.isSeparable K α
  have hspl : (g.map (algebraMap (𝓞 K) K)).Splits := by
    refine MilneANT.remark_8_40d' g hgmonic hsep (h.subset ?_)
    intro v hv hsplit
    apply hv
    exact (Splits.of_dvd hsplit (hf.map _).ne_zero (Polynomial.map_dvd _ hgdvd))
  rw [← hKg] at hspl
  have hdeg : (minpoly K α).natDegree ≤ 1 :=
    hspl.natDegree_le_one_of_irreducible (minpoly.irreducible (hintK))
  have := minpoly.mem_range_of_degree_eq_one K α (by
    have h1 := minpoly.natDegree_pos hintK
    exact (degree_eq_iff_natDegree_eq_of_pos one_pos).2 (le_antisymm hdeg h1))
  exact this


/-- $\mathrm{Spl}_S(L/K)$ (Milne, *CFT*, V, p. 164): the primes of $K$ not in $S$ that split completely in $L$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 164 (Spl_S(L/K))"]
def splitPrimesOutside (L : Type) [Field L] [NumberField L] [Algebra K L] (S : Set (HeightOneSpectrum (𝓞 K))) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  splitPrimes K L \ S

/-- **Remark 3.26(b)** (Milne, *CFT*, V, p. 164): in Theorem 3.25, $S$ can be any set of primes of density $0$. -/
@[kb "milne2020cft" "Ch. V, Remark 3.26(b)"]
theorem remark_3_26b {Ω : Type} [Field Ω] [NumberField Ω] [Algebra K Ω] (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M] (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.HasDirichletDensity 0) :
    L ≤ M ↔ splitPrimesOutside M S ⊆ splitPrimesOutside L S := by
  constructor
  · intro h v hv
    exact ⟨(MilneANT.thm_8_38 L M).1 h hv.1, hv.2⟩
  · intro h
    refine MilneANT.le_of_density_sdiff_zero L M (hasDirichletDensity_zero_of_subset ?_ hS)
    intro v hv
    by_contra hvS
    exact hv.2 (h ⟨hv.1, hvS⟩).1

/-- **Theorem 3.25** (Milne, *CFT*, V, p. 164): for Galois extensions $L, M$ of $K$ (inside a common number field
$\Omega$) and a finite set $S$ of primes, $L \subseteq M \iff \mathrm{Spl}_S(L/K) \supseteq \mathrm{Spl}_S(M/K)$; hence
$L = M \iff \mathrm{Spl}_S(L/K) = \mathrm{Spl}_S(M/K)$. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.25"]
theorem theorem_3_25 {Ω : Type} [Field Ω] [NumberField Ω] [Algebra K Ω] (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M] (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    (L ≤ M ↔ splitPrimesOutside M S ⊆ splitPrimesOutside L S) ∧
      (L = M ↔ splitPrimesOutside L S = splitPrimesOutside M S) := by
  have h0 : S.HasDirichletDensity 0 := hasDirichletDensity_zero_of_finite hS
  refine ⟨remark_3_26b L M S h0, ?_⟩
  constructor
  · rintro rfl; rfl
  · intro h
    exact le_antisymm ((remark_3_26b L M S h0).2 h.ge) ((remark_3_26b M L S h0).2 h.le)

/-- **Theorem 3.25, the step from 1.12** (Milne, *CFT*, V, p. 164): $\mathrm{Spl}_S(LM/K) = \mathrm{Spl}_S(L/K) \cap
\mathrm{Spl}_S(M/K)$. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.25 (Spl_S(LM/K) = Spl_S(L/K) ∩ Spl_S(M/K))"]
theorem splitPrimesOutside_sup {Ω : Type} [Field Ω] [NumberField Ω] [Algebra K Ω] (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M] (S : Set (HeightOneSpectrum (𝓞 K))) :
    splitPrimesOutside ↥(L ⊔ M) S = splitPrimesOutside L S ∩ splitPrimesOutside M S := by
  unfold splitPrimesOutside
  rw [MilneANT.splitPrimes_sup L M]
  ext v
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  tauto

/-! ## Helpers for Remark 3.26(a): split primes over `ℚ` through `ℤ` -/

/-- The inertia degree of a maximal ideal of $\mathcal O_{\mathbb Q}$ over $\mathbb Z$ is $1$. -/
theorem inertiaDeg_ratInt (q : Ideal (𝓞 ℚ)) [q.IsMaximal] : q.inertiaDeg ℤ = 1 := by
  have hp : (q.under ℤ).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ) q
  have hpos : 0 < q.inertiaDeg ℤ := Ideal.inertiaDeg_pos q ℤ
  rw [Ideal.inertiaDeg_eq_of_isMaximal (q.under ℤ) q] at hpos ⊢
  letI : Field (ℤ ⧸ q.under ℤ) := Ideal.Quotient.field _
  letI : Field ((𝓞 ℚ) ⧸ q) := Ideal.Quotient.field _
  have hle : Module.finrank (ℤ ⧸ q.under ℤ) ((𝓞 ℚ) ⧸ q) ≤ 1 := by
    refine finrank_le_one (1 : (𝓞 ℚ) ⧸ q) (fun w => ?_)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨z, rfl⟩ := algebraMap_int_ratInt_surjective x
    refine ⟨Ideal.Quotient.mk _ z, ?_⟩
    rw [Algebra.smul_def]
    simp
  omega

/-- The prime of `ℤ` below a prime of `𝓞 ℚ` is generated by the rational prime. -/
theorem under_int_eq_span_ratPrime (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal.under ℤ = Ideal.span {(MilneANT.ratPrime v : ℤ)} := by
  ext z
  rw [Ideal.under, Ideal.mem_comap, asIdeal_eq_span_ratPrime v, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv]
  simp

/-- A prime of `𝓞 N` lies over `(p)` in `ℤ` iff it lies over the prime `v` of `𝓞 ℚ` with `ratPrime v = p`. -/
theorem liesOver_int_iff (N : Type) [Field N] [NumberField N] (v : HeightOneSpectrum (𝓞 ℚ)) (P : Ideal (𝓞 N)) :
    P.LiesOver (Ideal.span {(MilneANT.ratPrime v : ℤ)}) ↔ P.LiesOver v.asIdeal := by
  have hv := under_int_eq_span_ratPrime v
  constructor
  · intro h
    refine ⟨?_⟩
    apply Ideal.comap_injective_of_surjective (algebraMap ℤ (𝓞 ℚ)) algebraMap_int_ratInt_surjective
    have h2 := h.over
    have h3 := Ideal.under_under (A := ℤ) (B := 𝓞 ℚ) P
    change v.asIdeal.under ℤ = (P.under (𝓞 ℚ)).under ℤ
    rw [hv, h3, ← h2]
  · intro h
    refine ⟨?_⟩
    rw [← hv, h.over, Ideal.under_under]

/-- The ramification index and the inertia degree of a prime over `v` are the same over `ℤ` and over `𝓞 ℚ`. -/
theorem ramificationIdx_inertiaDeg_int_eq (N : Type) [Field N] [NumberField N] (v : HeightOneSpectrum (𝓞 ℚ))
    (P : Ideal (𝓞 N)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    P.ramificationIdx ℤ = P.ramificationIdx (𝓞 ℚ) ∧ P.inertiaDeg ℤ = P.inertiaDeg (𝓞 ℚ) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI := v.isPrime
  have he := Ideal.ramificationIdx_tower (R := ℤ) (S := 𝓞 ℚ) (T := 𝓞 N) v.asIdeal P
  have hf := Ideal.inertiaDeg_tower (R := ℤ) (S := 𝓞 ℚ) (T := 𝓞 N) v.asIdeal P
  have h1 : v.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one v.asIdeal ℤ
  rw [h1, one_mul] at he
  rw [inertiaDeg_ratInt v.asIdeal, one_mul] at hf
  exact ⟨he, hf⟩

/-- Complete splitting over `ℚ`, in terms of the primes of `𝓞 N` above `(p)` in `ℤ`. -/
theorem mem_splitPrimes_rat_iff (N : Type) [Field N] [NumberField N] (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ splitPrimes ℚ N ↔ ∀ P ∈ (Ideal.span {(MilneANT.ratPrime v : ℤ)}).primesOver (𝓞 N),
      P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1 := by
  constructor
  · intro h P hP
    obtain ⟨hPp, hPl⟩ := hP
    haveI := hPp
    haveI := (liesOver_int_iff N v P).1 hPl
    rw [(ramificationIdx_inertiaDeg_int_eq N v P).1, (ramificationIdx_inertiaDeg_int_eq N v P).2]
    exact h ⟨P, hPp, inferInstance⟩
  · intro h Q
    obtain ⟨hPp, hPl⟩ := Q.2
    haveI := hPp
    haveI := hPl
    have hl : Q.1.LiesOver (Ideal.span {(MilneANT.ratPrime v : ℤ)}) := (liesOver_int_iff N v Q.1).2 hPl
    rw [← (ramificationIdx_inertiaDeg_int_eq N v Q.1).1, ← (ramificationIdx_inertiaDeg_int_eq N v Q.1).2]
    exact h Q.1 ⟨hPp, hl⟩

/-- A prime of `ℚ` that splits completely in a number field does not divide its discriminant. -/
theorem not_dvd_discr_of_mem_splitPrimes (N : Type) [Field N] [NumberField N] (v : HeightOneSpectrum (𝓞 ℚ))
    (h : v ∈ splitPrimes ℚ N) : ¬ (MilneANT.ratPrime v : ℤ) ∣ NumberField.discr N := by
  have hpz : Prime (MilneANT.ratPrime v : ℤ) :=
    Nat.prime_iff_prime_int.mp (Rat.HeightOneSpectrum.prime_natGenerator v)
  rw [NumberField.not_dvd_discr_iff_isUnramifiedIn N (𝓞 N) hpz,
    Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro P _ hl
  exact ((mem_splitPrimes_rat_iff N v).1 h P ⟨‹_›, hl⟩).1

/-- Complete splitting over `ℚ` is determined by the numbers of primes of each type (ramification index, inertia
degree) above `p`. -/
theorem mem_splitPrimes_rat_iff_ncard (N : Type) [Field N] [NumberField N] (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ splitPrimes ℚ N ↔ ∀ e f : ℕ, ¬ (e = 1 ∧ f = 1) →
      {P ∈ (Ideal.span {(MilneANT.ratPrime v : ℤ)}).primesOver (𝓞 N) |
        P.ramificationIdx ℤ = e ∧ P.inertiaDeg ℤ = f}.ncard = 0 := by
  have hfin : ((Ideal.span {(MilneANT.ratPrime v : ℤ)}).primesOver (𝓞 N)).Finite :=
    (Set.toFinite (v.asIdeal.primesOver (𝓞 N))).subset fun P hP =>
      ⟨hP.1, (liesOver_int_iff N v P).1 hP.2⟩
  rw [mem_splitPrimes_rat_iff]
  constructor
  · intro h e f hef
    have : {P ∈ (Ideal.span {(MilneANT.ratPrime v : ℤ)}).primesOver (𝓞 N) |
        P.ramificationIdx ℤ = e ∧ P.inertiaDeg ℤ = f} = ∅ := by
      ext P
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hP he hf
      exact hef (he ▸ hf ▸ h P hP)
    rw [this, Set.ncard_empty]
  · intro h P hP
    by_contra hne
    have h0 := h _ _ hne
    have hfin' : {Q ∈ (Ideal.span {(MilneANT.ratPrime v : ℤ)}).primesOver (𝓞 N) |
        Q.ramificationIdx ℤ = P.ramificationIdx ℤ ∧ Q.inertiaDeg ℤ = P.inertiaDeg ℤ}.Finite :=
      hfin.subset fun x hx => hx.1
    have hpos := (Set.ncard_pos hfin').2 ⟨P, hP, rfl, rfl⟩
    omega

/-- **Remark 3.26(a)** (Milne, *CFT*, V, p. 164, citing Cassels–Fröhlich p. 363; proved from the named statement
`MilneANT.Remark8_40c`): Theorem 3.25 fails without the Galois hypothesis: there are number fields $L, M$ with
$\mathrm{Spl}(M/\mathbb Q) \subseteq \mathrm{Spl}(L/\mathbb Q)$ (in fact equal) and no $\mathbb Q$-embedding $L \to M$. -/
@[kb "milne2020cft" "Ch. V, Remark 3.26(a)"]
theorem remark_3_26a (h : MilneANT.Remark8_40c) :
    ∃ (L M : Type) (_ : Field L) (_ : NumberField L) (_ : Field M) (_ : NumberField M),
      splitPrimes ℚ M = splitPrimes ℚ L ∧ IsEmpty (L →ₐ[ℚ] M) := by
  obtain ⟨L, M, _, _, _, _, hiso, hrank, hdisc, hcount⟩ := h.exists_pair
  refine ⟨L, M, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · ext v
    have hp : (MilneANT.ratPrime v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
    by_cases hd : (MilneANT.ratPrime v : ℤ) ∣ NumberField.discr L
    · exact iff_of_false (fun hM => not_dvd_discr_of_mem_splitPrimes M v hM (hdisc ▸ hd))
        (fun hL => not_dvd_discr_of_mem_splitPrimes L v hL hd)
    · rw [mem_splitPrimes_rat_iff_ncard M v, mem_splitPrimes_rat_iff_ncard L v]
      refine forall_congr' fun e => forall_congr' fun f => imp_congr_right fun _ => ?_
      rw [hcount _ hp hd e f]
  · refine ⟨fun φ => hiso.false ?_⟩
    have hinj : Function.Injective φ := φ.toRingHom.injective
    have hbij : Function.Bijective φ :=
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := φ.toLinearMap)).1 hinj⟩
    exact (AlgEquiv.ofBijective φ hbij).toRingEquiv

open Polynomial in
/-- **Remark 3.26(c)** (Milne, *CFT*, V, p. 165, citing Cassels–Fröhlich p. 363, 6.2; proved from the library's
`MilneANT.remark8_40d_holds`): an irreducible polynomial with a root modulo $\mathfrak p$ for almost all $\mathfrak p$ has
a root in $K$. Stated for monic $f \in \mathcal O_K[X]$ irreducible over $K$. -/
@[kb "milne2020cft" "Ch. V, Remark 3.26(c)"]
theorem remark_3_26c (f : Polynomial (𝓞 K)) (hf : f.Monic) (hirr : Irreducible (f.map (algebraMap (𝓞 K) K)))
    (h : {v : HeightOneSpectrum (𝓞 K) | ∀ x : v.asIdeal.ResidueField,
      (f.map (algebraMap (𝓞 K) v.asIdeal.ResidueField)).eval x ≠ 0}.Finite) :
    ∃ x : K, (f.map (algebraMap (𝓞 K) K)).eval x = 0 := by
  have hdeg : f.natDegree ≤ 1 := by
    by_contra hlt
    exact MilneANT.remark8_40d_holds.not_root_cofinite K f hf hirr (by omega) h
  have hdeg' : (f.map (algebraMap (𝓞 K) K)).natDegree = f.natDegree := hf.natDegree_map _
  have hpos := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  have h1 : (f.map (algebraMap (𝓞 K) K)).degree = 1 := by
    rw [degree_eq_natDegree hirr.ne_zero]
    have : (f.map (algebraMap (𝓞 K) K)).natDegree = 1 := by omega
    rw [this]; rfl
  obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one h1
  exact ⟨x, hx⟩

/-- **Remark 3.26(e)** (Milne, *CFT*, V, p. 165): for a finite Galois extension $L/K$ and a conjugacy class $C$ there is a
prime $\mathfrak p$ of $K$, unramified in $L$, with $(\mathfrak p, L/K) = C$ (indeed infinitely many). The bound on
$N\mathfrak p$ (Ahn–Kwon) is not formalized. -/
@[kb "milne2020cft" "Ch. V, Remark 3.26(e)"]
theorem remark_3_26e (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (C : ConjClasses Gal(L/K)) : (frobSet K L C).Infinite :=
  HilbertClassField.frobSet_infinite K L C

end NumberFieldKB.MilneCFT
