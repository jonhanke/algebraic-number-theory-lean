import NumberFieldKB.MilneCFT.Ch7.KummerSetting
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.SInteger

/-!
# Milne, *Class Field Theory*, Chapter VII §9: the existence theorem

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

Norm groups are `IsNormGroup K U` ($U = \mathrm{Nm}(C_L)$, $L/K$ finite abelian; Chapter V, p. 179).

* `ReciprocityLaw K` (named statement; Chapter V, Theorem 5.3 (b), with its compatibility with restriction, in the
  form used in §9): for $L/K$ finite abelian there is a surjection $\psi : C_K\to\mathrm{Gal}(L/K)$ with kernel
  $\mathrm{Nm}(C_L)$, and for an intermediate field $M$ its composite with restriction has kernel $\mathrm{Nm}(C_M)$.
* **Lemma 9.1** (`lemma_9_1`): a subgroup containing a norm group is a norm group (from the reciprocity law).
* **Proposition 9.2** (`prop_9_2`): the case $T = \emptyset$ of Proposition 6.10.
* **Lemma 9.3** (`Lemma9_3`, named statement), **Lemma 9.4** (`lemma_9_4`, from the norm limitation theorem, named
  statement `NormLimitation` of Chapter VIII, and Lemma 9.1), **Theorem 9.5** (`Theorem9_5`, named statement: the
  existence theorem).
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K]

/-- **The reciprocity law** (named statement; Milne, *CFT*, Chapter V, Theorem 5.3 (b), and the compatibility of the
Artin maps with restriction, Proposition 5.2): for every finite abelian extension $L/K$ there is a surjective
homomorphism $\psi : C_K\to\mathrm{Gal}(L/K)$ with kernel $\mathrm{Nm}_{L/K}(C_L)$ such that for every intermediate
field $K\subseteq M\subseteq L$, $\psi$ followed by restriction to $M$ has kernel $\mathrm{Nm}_{M/K}(C_M)$.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.ker_ideleClassArtinMap` (`TauCeti/NumberTheory/ClassFieldTheory/Global/Reciprocity.lean:281`),
`TauCeti.ClassFieldTheory.ideleClassArtinMap_surjective` (same file, line 293) and
`TauCeti.ClassFieldTheory.globalArtinMap_comp` (same file, line 227) at Tau Ceti commit `7ed979dc`. Needed to apply it
here: for the intermediate field, apply the kernel theorem to that field and use compatibility of the Artin maps with
restriction; one must identify our idele class group with Tau Ceti's and our group of norm classes with the range of
its idele class norm map. -/
@[kb "milne2020cft" "Ch. V, Thm. 5.3 (b) (input, as used in Ch. VII §9)"]
structure ReciprocityLaw : Prop where
  exists_artin : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : Gal(L/K), σ * τ = τ * σ) →
    ∃ ψ : IdeleClassGroup (𝓞 K) K →* Gal(L/K), Function.Surjective ψ ∧ ψ.ker = normClasses K L ∧
      ∀ (M : IntermediateField K L) [Normal K M], ((AlgEquiv.restrictNormalHom M).comp ψ).ker = normClasses K M

/-- **Lemma 9.1** (Milne, *CFT*, Chapter VII, p. 223; from the reciprocity law): if $U$ is a norm group and
$V\supseteq U$, then $V$ is a norm group. -/
@[kb "milne2020cft" "Ch. VII, Lemma 9.1"]
theorem lemma_9_1 (hR : ReciprocityLaw K) {U V : Subgroup (IdeleClassGroup (𝓞 K) K)} (hU : IsNormGroup K U)
    (hUV : U ≤ V) : IsNormGroup K V := by
  obtain ⟨L, iF, iN, iA, iG, hc, rfl⟩ := hU
  obtain ⟨ψ, hsurj, hker, hres⟩ := hR.exists_artin L hc
  set H : Subgroup Gal(L/K) := V.map ψ with hH
  have hHn : H.Normal := ⟨fun n hn g => by
    have h : g * n * g⁻¹ = n := by rw [hc g n]; simp
    rw [h]; exact hn⟩
  let M : IntermediateField K L := IntermediateField.fixedField H
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro σ τ
    obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L τ
    rw [← map_mul, ← map_mul, hc a b]
  · rw [← hres M]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
    constructor
    · intro hx
      exact Subgroup.mem_map_of_mem ψ hx
    · rintro ⟨y, hy, hyx⟩
      have h1 : y⁻¹ * x ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      rw [hker] at h1
      have := V.mul_mem hy (hUV h1)
      simpa using this

/-- **Proposition 9.2** (Milne, *CFT*, Chapter VII, p. 224): let $K$ contain a primitive $n$-th root of $1$ and let
$S$ be a finite set of primes containing those dividing $n$ and enough primes to generate the class group. Every
$a\in K^\times$ that is an $n$-th power in $K_v$ for all $v\in S$ (and all infinite $v$) and a unit at all $v\notin S$
is an $n$-th power in $K$. The case $T=\emptyset$ of Proposition 6.10 (as Milne's footnote notes, only Lemma 4.5 is
needed); conditional on Proposition 6.10. -/
@[kb "milne2020cft" "Ch. VII, Prop. 9.2"]
theorem prop_9_2 (h610 : Prop6_10 K)
    (n : ℕ) (hn : 0 < n) (hζ : ∃ ζ : K, IsPrimitiveRoot ζ n)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hSfin : S.Finite)
    (hSn : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hScl : Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤)
    (a : Kˣ) (hainf : ∀ w : InfinitePlace K, IsPowAtInf w n (a : K)) (haS : ∀ v ∈ S, IsPowAt v n (a : K))
    (haU : ∀ v, v ∉ S → v.valuation K (a : K) = 1) :
    ∃ c : Kˣ, c ^ n = a := by
  have hsurj : Function.Surjective (sUnitsToLocalQuot S (∅ : Set (HeightOneSpectrum (𝓞 K)))
      (Set.disjoint_empty S) n) := fun y => ⟨1, funext fun v => v.2.elim⟩
  exact h610.isPow n hn hζ S ∅ hSfin Set.finite_empty (Set.disjoint_empty S) hSn hScl hsurj a hainf
    haS (fun v hv _ => haU v hv)

/-- **Lemma 9.3** (named statement; key case of the existence theorem; Milne, *CFT*, Chapter VII, p. 224): if $K$
contains a primitive $p$-th root of $1$ ($p$ prime), every open subgroup $V$ of $C_K$ such that $C_K/V$ is a finite
group killed by $p$ is a norm group.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.exists_abelianLayer_globalNormSubgroup_eq_of_pow_mem`
(`TauCeti/NumberTheory/ClassFieldTheory/GlobalExistence/Kummer.lean:127`) and
`TauCeti.ClassFieldTheory.exists_intermediateField_range_ideleClassNormMap_eq_of_pow_mem` (same file, line 149) at Tau
Ceti commit `7ed979dc`. Needed to apply it here: Tau Ceti states the root of unity hypothesis as having enough roots of
unity, and obtains a layer of the absolute Galois group or an intermediate field; convert this to our notion of a norm
group (a finite abelian extension), using `TauCeti.ClassFieldTheory.isAbelianGalois_classField_iff`. -/
@[kb "milne2020cft" "Ch. VII, Lemma 9.3 (input)"]
structure Lemma9_3 : Prop where
  isNormGroup : ∀ (p : ℕ), p.Prime → (∃ ζ : K, IsPrimitiveRoot ζ p) →
    ∀ V : Subgroup (IdeleClassGroup (𝓞 K) K), IsOpen (V : Set (IdeleClassGroup (𝓞 K) K)) → V.FiniteIndex →
      (∀ c : IdeleClassGroup (𝓞 K) K, c ^ p ∈ V) → IsNormGroup K V

/-- **The norm limitation theorem** (named statement; Milne, *CFT*, Chapter VIII, used in Chapter VII, Lemma 9.4):
for a finite extension $K'/K$ of number fields, $\mathrm{Nm}(C_{K'}) = \mathrm{Nm}(C_M)$ for the maximal abelian
subextension $M$ of a Galois closure, and in particular $\mathrm{Nm}_{K'/K}(C_{K'})$ contains a norm group; here in the
form used by Lemma 9.4: if $L/K'$ is finite abelian, $\mathrm{Nm}_{L/K}(C_L)$ contains a norm group of $K$.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.GlobalNumberFields.isOpen_range_ideleClassNormMap`
(`TauCeti/NumberTheory/NumberField/Global/Ideles/Norm/Open.lean:136`) and
`TauCeti.ClassFieldTheory.globalAbelianExistence`
(`TauCeti/NumberTheory/ClassFieldTheory/GlobalExistence/Existence.lean:213`) at Tau Ceti commit `7ed979dc`. Needed to
apply it here: the statement as written has no abelian hypothesis on `L` over `K'`, so it follows from openness and
finite index of the norm image together with the existence theorem, not from the norm limitation theorem itself;
one must also check that the idele class norm maps are compatible in the tower. -/
@[kb "milne2020cft" "Ch. VIII, norm limitation theorem (input, as used in Ch. VII, Lemma 9.4)"]
structure NormLimitation : Prop where
  contains : ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (L : Type) [Field L] [NumberField L]
    [Algebra K' L] [Algebra K L] [IsScalarTower K K' L], ∃ U : Subgroup (IdeleClassGroup (𝓞 K) K),
      IsNormGroup K U ∧ U ≤ (normClasses K' L).map (ideleClassNorm K K')

/-- **Lemma 9.4** (Milne, *CFT*, Chapter VII, p. 225; uses the norm limitation theorem and Lemma 9.1): let $U$ be an
open subgroup of finite index in $C_K$. If for some finite extension $K'/K$ the subgroup
$U' = \mathrm{Nm}_{K'/K}^{-1}(U)$ of $C_{K'}$ is a norm group, then $U$ is a norm group. -/
@[kb "milne2020cft" "Ch. VII, Lemma 9.4"]
theorem lemma_9_4 (hR : ReciprocityLaw K) (hNL : NormLimitation K) (U : Subgroup (IdeleClassGroup (𝓞 K) K))
    (K' : Type) [Field K'] [NumberField K'] [Algebra K K']
    (hU' : IsNormGroup K' (U.comap (ideleClassNorm K K'))) : IsNormGroup K U := by
  obtain ⟨L, iF, iN, iA, iG, hc, hUL⟩ := hU'
  letI : Algebra K L := ((algebraMap K' L).comp (algebraMap K K')).toAlgebra
  have : IsScalarTower K K' L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨W, hW, hWle⟩ := hNL.contains K' L
  refine lemma_9_1 K hR hW (hWle.trans ?_)
  rw [← hUL]
  exact Subgroup.map_comap_le _ _

/-- **Theorem 9.5** (the existence theorem; named statement; Milne, *CFT*, Chapter VII, p. 226, and Chapter V,
Theorem 5.5): every open subgroup $U$ of finite index in $C_K$ is a norm group. (Milne's statement says "subgroup of
finite index"; his proof, through Lemma 9.3, uses that $U$ is open, as in Chapter V, Theorem 5.5.)

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.globalAbelianExistence`
(`TauCeti/NumberTheory/ClassFieldTheory/GlobalExistence/Existence.lean:213`) at Tau Ceti commit `7ed979dc`. Needed to
apply it here: this is the existence half of `IdelicExistence`; our norm group notion asks for a Galois extension
with commutative Galois group, which comes from `TauCeti.ClassFieldTheory.isAbelianGalois_classField_iff`. -/
@[kb "milne2020cft" "Ch. VII, Thm. 9.5 (input)"]
structure Theorem9_5 : Prop where
  isNormGroup : ∀ U : Subgroup (IdeleClassGroup (𝓞 K) K), IsOpen (U : Set (IdeleClassGroup (𝓞 K) K)) →
    U.FiniteIndex → IsNormGroup K U

end NumberFieldKB.MilneCFT.Ch7
