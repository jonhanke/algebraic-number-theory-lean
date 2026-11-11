import NumberFieldKB.MilneCFT.Ch7.ExistenceTauCeti
import NumberFieldKB.MilneCFT.Ch7.LocalNormTauCeti
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWang
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances

/-!
# Milne, *CFT*, VIII, Theorem 2.3: partial result

**Proved here** (all from Tau Ceti's global class field theory, `NumberFieldKB/TauCetiPort/`):
* `T23.mem_normClasses_finite_iff`, `T23.mem_normClasses_infinite_iff`: local-global compatibility of norm
  groups. For abelian `L/K`, the class in `C_K` of the idele concentrated at `v` (resp. `w`) with component `x`
  lies in `N_{L/K}(C_L)` iff `x` is in `localNormGroup L v` (resp. `localNormGroupInf L w`). Proof: kernel of the
  global Artin map is the norm group (`ker_globalArtinMap`), its restriction to `K_v^×` is the local Artin symbol
  (`globalArtinMap_local`, `globalArtinMap_infiniteLocal`), and the local norm group is the kernel of the local
  Artin symbol (`localNormGroup_eq_ker_localArtinAt`, `T23.localNormGroupInf_eq_ker`).
* `theorem2_3_of_existsU`: `Theorem2_3 K` follows from `ExistsU K`, the existence of an open subgroup `U` of finite
  index of `C_K` with `U ∩ K_v^× = N_v` (the existence theorem `Ch7.theorem9_5` supplies `L`).

**Missing** (so no unconditional headline `Theorem2_3` yet): `ExistsU K`. Classically it is built from the image
of `∏_{v∈S} N_v × ∏_{w∈T} N'_w × ∏_{p∈P} (1+𝔭) × ∏_{other} units` in `C_K`; that `U ∩ K_v^× = N_v` needs
Chevalley's theorem (`ChevalleyCongruence`, stated below, not proved: Tau Ceti has the Kummer/Frobenius
ingredients for prime exponent over a field containing `ζ_p`, `exists_auxiliaryPlaces_unitLocalPowerClassMap_surjective`,
but not the theorem itself), plus openness and finite index of `U` in `C_K`.
-/

open IsDedekindDomain NumberField
open scoped Classical NumberField.LiesOver

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8
namespace T23

variable {K : Type} [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- A separable-closure embedding of `L`. -/
theorem exists_embedding : Nonempty (L →ₐ[K] SeparableClosure K) :=
  ⟨IsSepClosed.lift⟩

/-- **Local–global compatibility at a finite place**: the class of the idele concentrated at `v` with
component `x` is a global norm iff `x` is a local norm. -/
theorem mem_normClasses_finite_iff [IsMulCommutative Gal(L/K)] (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (IdeleGroup.ofAdicCompletion (𝓞 K) K v x : IdeleClassGroup (𝓞 K) K) ∈ Ch7.normClasses K L ↔
      x ∈ Ch7.localNormGroup L v := by
  obtain ⟨ι⟩ := exists_embedding (K := K) L
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hP0 := Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, hP.isPrime, hP0⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := hPv
  rw [Ch7.normClasses_eq_tauCeti, ← TauCeti.ClassFieldTheory.globalArtinMap_eq_zero_iff K L ι,
    TauCeti.ClassFieldTheory.globalArtinMap_local, ofMul_eq_zero,
    Ch7.localNormGroup_eq_ker_localArtinAt K L v w, MonoidHom.mem_ker]

/-- For abelian `L/K` the archimedean local norm group is the kernel of the archimedean Artin symbol. -/
theorem localNormGroupInf_eq_ker [IsMulCommutative Gal(L/K)] (v : InfinitePlace K) :
    Ch7.localNormGroupInf L v = (TauCeti.ClassFieldTheory.infiniteLocalArtinAt K L v).ker := by
  ext x
  rw [Ch8.mem_localNormGroupInf_iff, TauCeti.mem_range_normUnits_completion_iff, MonoidHom.mem_ker]
  constructor
  · rintro ⟨u, rfl⟩
    refine finprod_induction (fun y => TauCeti.ClassFieldTheory.infiniteLocalArtinAt K L v y = 1)
      (map_one _) (fun a b ha hb => by rw [map_mul, ha, hb, one_mul]) (fun w' => ?_)
    haveI := w'.2
    exact (TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_one_iff_mem_normGroup v w'.1 _).2
      (TauCeti.mem_normGroup_iff.2 ⟨u w', rfl⟩)
  · intro hx
    obtain ⟨w0, hw0⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
    have hw0l : w0.LiesOver v := by subst hw0; infer_instance
    haveI := hw0l
    obtain ⟨b, hb⟩ := TauCeti.mem_normGroup_iff.1
      ((TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_one_iff_mem_normGroup v w0 x).1 hx)
    let W : {w : InfinitePlace L // w.LiesOver v} := ⟨w0, hw0l⟩
    refine ⟨Pi.mulSingle W b, ?_⟩
    rw [finprod_eq_single _ W fun w' hw' => by simp [Pi.mulSingle_eq_of_ne hw']]
    rw [Pi.mulSingle_eq_same]
    ext
    simp [hb]

/-- **Local–global compatibility at an infinite place.** -/
theorem mem_normClasses_infinite_iff [IsMulCommutative Gal(L/K)] (v : InfinitePlace K)
    (x : v.Completionˣ) :
    (IdeleGroup.ofCompletion (𝓞 K) K v x : IdeleClassGroup (𝓞 K) K) ∈ Ch7.normClasses K L ↔
      x ∈ Ch7.localNormGroupInf L v := by
  obtain ⟨ι⟩ := exists_embedding (K := K) L
  rw [Ch7.normClasses_eq_tauCeti, ← TauCeti.ClassFieldTheory.globalArtinMap_eq_zero_iff K L ι,
    TauCeti.ClassFieldTheory.globalArtinMap_infiniteLocal, ofMul_eq_zero,
    localNormGroupInf_eq_ker L v, MonoidHom.mem_ker]

end T23

section Reduction

variable (K : Type) [Field K] [NumberField K]

/-- **The global input of Theorem 2.3**: for open subgroups `N_v ⊆ K_v^×` of finite index at finitely many
places there is an open subgroup `U` of finite index of the idele class group `C_K` with
`U ∩ K_v^× = N_v` (where `K_v^× ↪ C_K` is the embedding as ideles concentrated at `v`). Named statement (the
missing input; classically from Chevalley's congruence theorem for S-units, `ChevalleyCongruence`). -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.3, p. 232 (global input: open subgroup with prescribed local traces)"]
structure ExistsU : Prop where
  exists_U : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (N' : ∀ w : InfinitePlace K, Subgroup w.Completionˣ),
    (∀ v ∈ S, IsOpen (N v : Set (v.adicCompletion K)ˣ) ∧ (N v).FiniteIndex) →
    (∀ w ∈ T, IsOpen (N' w : Set w.Completionˣ) ∧ (N' w).FiniteIndex) →
    ∃ U : Subgroup (IdeleClassGroup (𝓞 K) K), IsOpen (U : Set (IdeleClassGroup (𝓞 K) K)) ∧ U.FiniteIndex ∧
      (∀ v ∈ S, ∀ x : (v.adicCompletion K)ˣ,
        (IdeleGroup.ofAdicCompletion (𝓞 K) K v x : IdeleClassGroup (𝓞 K) K) ∈ U ↔ x ∈ N v) ∧
      ∀ w ∈ T, ∀ x : w.Completionˣ,
        (IdeleGroup.ofCompletion (𝓞 K) K w x : IdeleClassGroup (𝓞 K) K) ∈ U ↔ x ∈ N' w

/-- **Theorem 2.3 from the global input `ExistsU`** and the existence theorem (Theorem 9.5), via the
local–global compatibility of norm groups. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.3, p. 232 (from ExistsU)"]
theorem theorem2_3_of_existsU (h : ExistsU K) : Theorem2_3 K := by
  refine ⟨fun S T N N' hN hN' => ?_⟩
  obtain ⟨U, hUo, hUf, hUS, hUT⟩ := h.exists_U S T N N' hN hN'
  obtain ⟨L, _, _, _, _, hab, hUL⟩ := (Ch7.theorem9_5 K).isNormGroup U hUo hUf
  haveI : IsMulCommutative Gal(L/K) := ⟨⟨hab⟩⟩
  haveI : IsAbelianGalois K L := { toIsGalois := inferInstance, toIsMulCommutative := inferInstance }
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, fun v hv => ?_, fun w hw => ?_⟩
  · ext x
    rw [← T23.mem_normClasses_finite_iff L v x, ← hUL, hUS v hv x]
  · ext x
    rw [← T23.mem_normClasses_infinite_iff L w x, ← hUL, hUT w hw x]

/-- **Chevalley's theorem on congruence subgroups of `S`-units** (the arithmetic input still missing for
`ExistsU`; proved classically by Kummer theory and the existence of primes at which a given `S`-unit is not
a power residue): every subgroup `H` of finite index of the `S`-units of `K` contains all `S`-units that are
congruent to `1` at the primes of a suitable finite set `P` of primes outside `S`. Named statement (not yet used). -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.3, p. 232 (Chevalley's congruence theorem for S-units; input)"]
structure ChevalleyCongruence : Prop where
  congr : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (H : Subgroup Kˣ),
    H ≤ (S : Set (HeightOneSpectrum (𝓞 K))).unit K →
    H.relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) ≠ 0 →
    ∀ B : Finset (HeightOneSpectrum (𝓞 K)), ∃ P : Finset (HeightOneSpectrum (𝓞 K)),
      Disjoint P (S ∪ B) ∧
        ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
          (∀ 𝔭 ∈ P, Valued.v (algebraMap K (𝔭.adicCompletion K) (a : K) - 1) < 1) → a ∈ H

end Reduction
end NumberFieldKB.MilneCFT.Ch8
