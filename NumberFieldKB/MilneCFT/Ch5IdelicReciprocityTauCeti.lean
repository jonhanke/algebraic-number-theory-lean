import NumberFieldKB.MilneCFT.Ch5IdelicMain
import NumberFieldKB.MilneCFT.Ch5Cor4_13
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.Reciprocity
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.LocalArtin.Compatibility
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.LocalArtin.Frobenius
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.LocalArtin.InfinitePlace

/-!
# Milne, *Class Field Theory*, Chapter V, Theorem 5.3 (the reciprocity law), proved from Tau Ceti

The named statement `NumberFieldKB.MilneCFT.IdelicReciprocity` (Milne V, Theorem 5.3 with Proposition 5.2 and
Summary 5.10) is proved here (`idelicReciprocity`) from Tau Ceti's global class field theory (ported under
`NumberFieldKB/TauCetiPort/`, Apache 2.0, the Tau Ceti contributors).

For a finite abelian extension $L/K$ of number fields the homomorphism is Tau Ceti's idele-class Artin map
`TauCeti.ClassFieldTheory.ideleClassArtinMap K L : C_K →* Gal(L/K)` composed with the quotient map $I_K \to C_K$
(`idelicArtinTauCeti`). Both libraries use Mathlib's `IdeleGroup` and `IdeleClassGroup`, so no identification of idèles
is needed. The properties:

* kernel and surjectivity: `ker_ideleClassArtinMap`, `ideleClassArtinMap_surjective`, and the comparison of the
  idèle norms `NumberFieldKB.Ideles.ideleRelNorm_eq_ideleNormMap`;
* openness of the kernel: Tau Ceti's `isOpen_range_ideleNormMap` (the kernel contains the open norm group);
* condition (a) of Summary 5.10 (idèles that are units at the unramified primes, close to one at the ramified ones and
  positive at the real places ramified in $L$ have trivial symbol): Tau Ceti's local–global formula
  `globalArtinMap_eq_zero_of_forall_eq_one`, with at an unramified prime
  `localArtinAt_eq_one_of_normalizedValuation_eq_one`, at a ramified prime the openness of the local norm group
  (`exists_unitFiltration_le_normGroup`, `normGroup_le_ker_localArtinAt`), and at the infinite places
  `infiniteLocalArtinAt_eq_one_of_isComplex`, `infiniteLocalArtinAt_eq_one_of_pos`,
  `infiniteLocalArtinAt_eq_one_of_isUnramified`;
* condition (b) (Frobenius at the unramified primes): `globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt` and
  `isUniformizer_iff_valued_eq_exp_neg_one`.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped IsMulCommutative AdicCompletionExtension

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]
variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- **The idèlic Artin map from Tau Ceti**: Tau Ceti's Artin map `ideleClassArtinMap K L` on idèle classes, composed
with the quotient map from the idèles. -/
def idelicArtinTauCeti : IdeleGroup (𝓞 K) K →* Gal(L/K) :=
  (TauCeti.ClassFieldTheory.ideleClassArtinMap K L).comp (QuotientGroup.mk' _)

theorem idelicArtinTauCeti_apply (x : IdeleGroup (𝓞 K) K) :
    idelicArtinTauCeti L x =
      TauCeti.ClassFieldTheory.ideleClassArtinMap K L (x : IdeleClassGroup (𝓞 K) K) := rfl

/-- The symbol is read in `Gal(L/K)^ab` through Tau Ceti's `globalArtinMap`. -/
theorem of_idelicArtinTauCeti (x : IdeleGroup (𝓞 K) K) :
    Abelianization.of (idelicArtinTauCeti L x) =
      (TauCeti.ClassFieldTheory.globalArtinMap K L IsSepClosed.lift
        (.ofMul (x : IdeleClassGroup (𝓞 K) K))).toMul :=
  TauCeti.ClassFieldTheory.of_ideleClassArtinMap K L IsSepClosed.lift _

theorem idelicArtinTauCeti_eq_one_iff (x : IdeleGroup (𝓞 K) K) :
    idelicArtinTauCeti L x = 1 ↔
      TauCeti.ClassFieldTheory.globalArtinMap K L IsSepClosed.lift
        (.ofMul (x : IdeleClassGroup (𝓞 K) K)) = 0 := by
  rw [← Abelianization.of_injective.eq_iff, of_idelicArtinTauCeti, map_one, toMul_eq_one]

/-- The kernel of the idèlic Artin map is $K^\times \cdot \mathrm{Nm}_{L/K}(I_L)$. -/
theorem ker_idelicArtinTauCeti : (idelicArtinTauCeti L).ker = ideleNormGroup (K := K) L := by
  ext x
  rw [MonoidHom.mem_ker, idelicArtinTauCeti_apply, ← MonoidHom.mem_ker,
    TauCeti.ClassFieldTheory.ker_ideleClassArtinMap]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    change TauCeti.GlobalNumberFields.ideleClassNormMap K L (y : IdeleClassGroup (𝓞 L) L) = _ at hc
    rw [TauCeti.GlobalNumberFields.ideleClassNormMap_mk] at hc
    obtain ⟨a, ha⟩ := QuotientGroup.eq.mp hc
    have hx : x = TauCeti.GlobalNumberFields.ideleNormMap K L y *
        IdeleGroup.unitEmbedding (𝓞 K) K a := by
      rw [ha]; simp
    rw [hx]
    refine mul_mem (Subgroup.mem_sup_right ⟨y, ?_⟩) (Subgroup.mem_sup_left ⟨a, rfl⟩)
    exact (Ideles.ideleRelNorm_eq_ideleNormMap (Module.finBasis K L) y)
  · intro hx
    obtain ⟨p, hp, q, ⟨y, rfl⟩, rfl⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := hp
    refine ⟨(y : IdeleClassGroup (𝓞 L) L), ?_⟩
    change TauCeti.GlobalNumberFields.ideleClassNormMap K L (y : IdeleClassGroup (𝓞 L) L) = _
    rw [TauCeti.GlobalNumberFields.ideleClassNormMap_mk]
    have hy : (ideleNormMap K L : IdeleGroup (𝓞 L) L →* IdeleGroup (𝓞 K) K) y =
        TauCeti.GlobalNumberFields.ideleNormMap K L y :=
      Ideles.ideleRelNorm_eq_ideleNormMap (Module.finBasis K L) y
    rw [hy, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 K) K) _).2 ⟨a, rfl⟩]
    exact (one_mul (_ : IdeleClassGroup (𝓞 K) K)).symm

theorem idelicArtinTauCeti_surjective : Function.Surjective (idelicArtinTauCeti L (K := K)) :=
  (TauCeti.ClassFieldTheory.ideleClassArtinMap_surjective K L).comp (QuotientGroup.mk'_surjective _)

theorem idelicArtinTauCeti_principal (a : Kˣ) :
    idelicArtinTauCeti L (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 := by
  rw [idelicArtinTauCeti_apply,
    (QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 K) K) _).2 ⟨a, rfl⟩, map_one]

theorem isOpen_ker_idelicArtinTauCeti :
    IsOpen ((idelicArtinTauCeti L (K := K)).ker : Set (IdeleGroup (𝓞 K) K)) := by
  refine Subgroup.isOpen_mono ?_ (TauCeti.GlobalNumberFields.isOpen_range_ideleNormMap K L)
  rw [ker_idelicArtinTauCeti]
  rintro _ ⟨y, rfl⟩
  refine Subgroup.mem_sup_right ⟨y, ?_⟩
  exact Ideles.ideleRelNorm_eq_ideleNormMap (Module.finBasis K L) y

/-! ### Condition (a) of Summary 5.10 -/

/-- At a prime unramified in `L`, units of the completion have trivial local Artin symbol. -/
theorem localArtinAt_eq_one_of_unramified {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ unramifiedPrimes K L)
    {u : (v.adicCompletion K)ˣ} (hu : Valued.v (u : v.adicCompletion K) = 1) :
    TauCeti.ClassFieldTheory.localArtinAt K L v u = 1 := by
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := hv w.asIdeal w.isPrime inferInstance
  refine TauCeti.ClassFieldTheory.localArtinAt_eq_one_of_normalizedValuation_eq_one _ w ?_
  have h := HeightOneSpectrum.normalizedValuationWithZero_adicCompletion (K := K)
    (v := w.under (𝓞 K)) (u : (w.under (𝓞 K)).adicCompletion K)
  rw [hu, inv_one, TauCeti.normalizedValuationWithZero_coe] at h
  exact_mod_cast h

/-- At every finite prime, units close enough to one have trivial local Artin symbol. -/
theorem exists_localArtinAt_eq_one (v : HeightOneSpectrum (𝓞 K)) : ∃ n : ℕ, ∀ u : (v.adicCompletion K)ˣ,
    Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)) →
      TauCeti.ClassFieldTheory.localArtinAt K L v u = 1 := by
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
  obtain ⟨n, hn⟩ := TauCeti.exists_unitFiltration_le_normGroup
    (K := (w.under (𝓞 K)).adicCompletion K) (L := w.adicCompletion L)
  refine ⟨n + 1, fun u hu => ?_⟩
  refine TauCeti.ClassFieldTheory.normGroup_le_ker_localArtinAt _ w (hn ?_)
  rw [HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff]
  have hlt : WithZero.exp (-((n + 1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  refine ⟨val_eq_one_of_sub_one_le Valued.v hlt hu, hu.trans (WithZero.exp_le_exp.mpr ?_)⟩
  push_cast; omega

/-- At an infinite place, the conditions of Summary 5.10(a) give a trivial local Artin symbol. -/
theorem infiniteLocalArtinAt_eq_one (v : InfinitePlace K) (x : v.Completionˣ)
    (hx : ∀ hv : v.IsReal, InfinitePlace.RamifiesIn L v → IsPosAt v hv (x : v.Completion)) :
    TauCeti.ClassFieldTheory.infiniteLocalArtinAt K L v x = 1 := by
  rcases v.isReal_or_isComplex with hv | hv
  · by_cases hr : InfinitePlace.RamifiesIn L v
    · exact TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_one_of_pos hv (hx hv hr)
    · obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
      have : w.LiesOver v := by subst hw; infer_instance
      have hwr : w.IsReal := by
        by_contra h
        exact hr ⟨hv, w, hw, InfinitePlace.not_isReal_iff_isComplex.mp h⟩
      exact TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_one_of_isUnramified v w
        (InfinitePlace.isUnramified_iff.mpr (Or.inl hwr)) x
  · exact TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_one_of_isComplex hv x

theorem idelicArtinTauCeti_local_ramified : ∃ n : ℕ, ∀ u : IdeleGroup (𝓞 K) K,
    (∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K L → Valued.v (ideleFinAt u v) = 1) →
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ unramifiedPrimes K L →
      Valued.v (ideleFinAt u v - 1) ≤ WithZero.exp (-(n : ℤ))) →
    (∀ (w : InfinitePlace K) (hw : w.IsReal), InfinitePlace.RamifiesIn L w → IsPosAt w hw (ideleInfAt u w)) →
    idelicArtinTauCeti L u = 1 := by
  classical
  choose N hN using exists_localArtinAt_eq_one (K := K) L
  let S := (finite_compl_unramifiedPrimes K L).toFinset
  refine ⟨S.sup N, fun u h1 h2 h3 => ?_⟩
  rw [idelicArtinTauCeti_eq_one_iff]
  refine TauCeti.ClassFieldTheory.globalArtinMap_eq_zero_of_forall_eq_one K L _ (fun v => ?_) (fun w => ?_)
  · by_cases hv : v ∈ unramifiedPrimes K L
    · exact localArtinAt_eq_one_of_unramified L hv (h1 v hv)
    · refine hN v _ ((h2 v hv).trans (WithZero.exp_le_exp.mpr ?_))
      have : N v ≤ S.sup N := Finset.le_sup ((finite_compl_unramifiedPrimes K L).mem_toFinset.mpr hv)
      omega
  · exact infiniteLocalArtinAt_eq_one L w _ (fun hw hr => h3 w hw hr)

/-! ### Condition (b) of Summary 5.10 -/

theorem idelicArtinTauCeti_frobenius (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ unramifiedPrimes K L)
    (π : (v.adicCompletion K)ˣ) (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1)) :
    idelicArtinTauCeti L (IdeleGroup.ofAdicCompletion (𝓞 K) K v π) = artinFrob L v := by
  obtain ⟨Q, hQ, hQv⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  have hQ' : Q ∈ v.asIdeal.primesOver (𝓞 L) := ⟨hQ, hQv⟩
  have : Algebra.IsUnramifiedAt (𝓞 K) Q := hv Q hQ hQv
  have hfrob := isArithFrobAt_frobAt K L v ⟨Q, hQ'⟩
  have hu : TauCeti.IsUniformizer (v.adicCompletion K) π :=
    (HeightOneSpectrum.isUniformizer_iff_valued_eq_exp_neg_one v).mpr hπ
  apply Abelianization.of_injective
  rw [of_idelicArtinTauCeti, artinFrob_eq L v hv ⟨Q, hQ'⟩, ← IdeleClassGroup.ofAdicCompletion_apply,
    TauCeti.ClassFieldTheory.globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt L _ v Q hfrob,
    (TauCeti.isUniformizer_def π).1 hu]
  simp

/-- The Tau Ceti idèlic Artin map has the properties (a), (b) of Summary 5.10. -/
theorem isIdelicArtinMap_tauCeti : IsIdelicArtinMap L (idelicArtinTauCeti L (K := K)) where
  isOpen_ker := isOpen_ker_idelicArtinTauCeti L
  local_ramified := idelicArtinTauCeti_local_ramified L
  frobenius := idelicArtinTauCeti_frobenius L

variable (K) in
/-- **Theorem 5.3, the reciprocity law, proved** (Milne, *CFT*, V, Theorem 5.3, p. 178, with Proposition 5.2 and
Summary 5.10): for every finite abelian extension $L/K$ of number fields there is a homomorphism
$\phi_{L/K} : I_K \to \mathrm{Gal}(L/K)$ with the properties of Summary 5.10, trivial on $K^\times$, surjective, with
kernel $K^\times\cdot\mathrm{Nm}(I_L)$. From Tau Ceti's global reciprocity (ported). -/
@[kb "milne2020cft" "Ch. V, Theorem 5.3"]
theorem idelicReciprocity : IdelicReciprocity K where
  exists_artin L _ _ _ _ := ⟨idelicArtinTauCeti L, isIdelicArtinMap_tauCeti L, idelicArtinTauCeti_principal L,
    idelicArtinTauCeti_surjective L, ker_idelicArtinTauCeti L⟩

end NumberFieldKB.MilneCFT
