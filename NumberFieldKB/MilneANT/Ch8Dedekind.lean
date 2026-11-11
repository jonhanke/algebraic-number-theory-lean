import NumberFieldKB.MilneANT.Ch8GaloisGroups
import NumberFieldKB.MilneANT.Ch8Chebotarev
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Polynomial.Selmer
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: Dedekind's theorem and its consequences

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

* **Theorem 8.23** (Dedekind; `thm_8_23`, proved from the named statement `DedekindFrobenius`, the Frobenius form
  that Milne's proof establishes: the cycle type of a Frobenius element on the roots is the factorization type modulo
  $\mathfrak p$).
* **Example 8.25** (`example_8_25`) and **Example 8.27** (`example_8_27`, with the correction
  $f = -15f_1+10f_2+6f_3$), conditional on `DedekindFrobenius`.
* **Examples 8.36, 8.37** (`factorizationType_hasDirichletDensity`, `example_8_36`, `example_8_37_D8`): densities of
  factorization types.
* **Remark 8.40** (c) (`Remark8_40c`, named statement), (d) (`remark_8_40d`, conditional on `DedekindFrobenius`;
  `Remark8_40d`, named statement; `remark_8_40d_example`, proved), (e) (`Remark8_40e`, named statement).
-/

open NumberField IsDedekindDomain Polynomial UniqueFactorizationMonoid
open NumberFieldKB.Chebotarev
open scoped Classical

namespace NumberFieldKB.MilneANT

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! ## Theorem 8.23 (Dedekind) -/

/-- **Frobenius and factorization modulo $\mathfrak p$** (named statement; the content of Milne's proof of Theorem
8.23): let $L/K$ be a Galois extension of number fields, $f \in \mathcal O_K[X]$ monic and split in $L$,
$\mathfrak p$ a prime of $K$ such that $f \bmod \mathfrak p$ is squarefree (distinct irreducible factors), and
$\mathfrak P$ a prime of $L$ above $\mathfrak p$. Then any Frobenius element $\sigma$ at $\mathfrak P$
($\sigma\alpha\equiv\alpha^{N\mathfrak p} \bmod \mathfrak P$), as a permutation of the roots of $f$ in $L$, has cycle
type (fixed points included) the degrees of the irreducible factors of $f \bmod \mathfrak p$. -/
@[kb "milne2020ant" "v3.08, Thm. 8.23 (proof), p. 145"]
structure DedekindFrobenius : Prop where
  partition_eq : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (f : (𝓞 K)[X]) (_ : f.Monic) (_ : (f.map (algebraMap (𝓞 K) L)).Splits)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (_ : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)))
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver 𝔭.asIdeal] (σ : Gal(L/K)) (_ : IsArithFrobAt (𝓞 K) σ P),
    (rootPerm (f.map (algebraMap (𝓞 K) K)) (E := L) σ).partition.parts =
      (normalizedFactors (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))).map natDegree

section Dedekind

variable {K : Type} [Field K] [NumberField K]

/-- The splitting field over a number field of a polynomial is a number field. -/
instance instNumberFieldSplittingField (g : K[X]) : NumberField g.SplittingField := by
  haveI : CharZero g.SplittingField := inferInstance
  haveI : FiniteDimensional ℚ g.SplittingField := Module.Finite.trans K _
  exact NumberField.mk

/-- In characteristic zero the splitting field of a polynomial over a number field is Galois. -/
instance instIsGaloisSplittingField (g : K[X]) : IsGalois K g.SplittingField :=
  { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField
    to_normal := SplittingField.instNormal g }

/-- `galPerm` is the permutation of the roots in the splitting field induced by the automorphism. -/
theorem galPerm_eq_rootPerm (g : K[X]) (σ : g.Gal) :
    galPerm g σ = rootPerm g (G := g.SplittingField ≃ₐ[K] g.SplittingField) (E := g.SplittingField) σ := rfl

/-- The reduction of an integral polynomial splits in the splitting field of its image over `K`. -/
theorem splits_map_splittingField (f : (𝓞 K)[X]) :
    (f.map (algebraMap (𝓞 K) (f.map (algebraMap (𝓞 K) K)).SplittingField)).Splits := by
  have h := SplittingField.splits (f.map (algebraMap (𝓞 K) K))
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h

/-- A Frobenius element at a prime above `𝔭`, as a permutation of the roots, has the cycle type given by the
factorization of `f` modulo `𝔭` (this is `DedekindFrobenius` applied to the splitting field). -/
theorem frob_partition (hD : DedekindFrobenius) (f : (𝓞 K)[X]) (hf : f.Monic)
    (𝔭 : HeightOneSpectrum (𝓞 K))
    (hsq : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)))
    (Q : 𝔭.asIdeal.primesOver (𝓞 (f.map (algebraMap (𝓞 K) K)).SplittingField)) :
    (galPerm (f.map (algebraMap (𝓞 K) K))
        (frobAt K (f.map (algebraMap (𝓞 K) K)).SplittingField 𝔭 Q)).partition.parts =
      (normalizedFactors (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))).map natDegree := by
  haveI := Q.2.1
  haveI := Q.2.2
  exact hD.partition_eq K _ f hf (splits_map_splittingField f) 𝔭 hsq Q.1 _
    (isArithFrobAt_frobAt K _ 𝔭 Q)

/-- If `f` is separable over `K`, then `f` modulo `𝔭` is squarefree for all but finitely many primes `𝔭` (a Bezout
identity `a f + b f' = d` with `d` a nonzero integer of `K` shows `f` is separable modulo every prime not dividing
`d`). -/
theorem finite_not_squarefree (f : (𝓞 K)[X]) (hs : (f.map (algebraMap (𝓞 K) K)).Separable) :
    {𝔭 : HeightOneSpectrum (𝓞 K) |
      ¬ Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))}.Finite := by
  obtain ⟨a, b, hab⟩ := hs
  obtain ⟨d1, hd1, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (𝓞 K)) a
  obtain ⟨d2, hd2, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (𝓞 K)) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors (𝓞 K)) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors (𝓞 K)) b
  have hd : d1 * d2 ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hd1) (nonZeroDivisors.ne_zero hd2)
  have key : C d2 * A * f + C d1 * B * derivative f = C (d1 * d2) := by
    apply Polynomial.map_injective (algebraMap (𝓞 K) K) (IsFractionRing.injective _ _)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← derivative_map, hA, hB,
      ← algebraMap_smul K d1, ← algebraMap_smul K d2, smul_eq_C_mul, map_mul]
    linear_combination (C (algebraMap (𝓞 K) K d1) * C (algebraMap (𝓞 K) K d2)) * hab
  refine (Ideal.finite_factors (I := Ideal.span {d1 * d2}) ?_).subset ?_
  · simpa using hd
  intro 𝔭 h𝔭
  by_contra hnd
  apply h𝔭
  have hdn : d1 * d2 ∉ 𝔭.asIdeal := by
    intro h
    exact hnd ((Ideal.dvd_iff_le).2 ((Ideal.span_singleton_le_iff_mem _).2 h))
  apply Polynomial.Separable.squarefree
  have hu : algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2) ≠ 0 := by
    rwa [Ne, Ideal.algebraMap_residueField_eq_zero]
  have h2 := congrArg (Polynomial.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)) key
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← derivative_map] at h2
  refine ⟨C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2))⁻¹ *
      (C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField d2) * A.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)),
    C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2))⁻¹ *
      (C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField d1) * B.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)), ?_⟩
  linear_combination (C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2))⁻¹) * h2 +
    (by rw [← C_mul, inv_mul_cancel₀ hu, C_1] : C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2))⁻¹ *
      C (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField (d1 * d2)) = (1 : _[X]))

/-- **Theorem 8.23** (Dedekind; proved from `DedekindFrobenius`): let $f \in \mathcal O_K[X]$ be monic of degree $n$
with Galois group $G$ over the number field $K$, and $\mathfrak p$ a prime of $K$ with
$f \equiv f_1\cdots f_r \bmod \mathfrak p$, the $f_i$ distinct irreducible polynomials over $k = \mathcal O_K/\mathfrak p$
of degrees $n_i$. Then $G$ contains a permutation of the roots that is a product of disjoint cycles of lengths $n_i$.
(The residue field is Mathlib's `Ideal.ResidueField`, isomorphic to $\mathcal O_K/\mathfrak p$.) -/
@[kb "milne2020ant" "v3.08, Thm. 8.23, p. 145"]
theorem thm_8_23 (hD : DedekindFrobenius) (f : (𝓞 K)[X]) (hf : f.Monic) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hsq : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))) :
    ∃ σ : (f.map (algebraMap (𝓞 K) K)).Gal,
      (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts =
        (normalizedFactors (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))).map natDegree := by
  obtain ⟨Q⟩ := (inferInstance :
    Nonempty (𝔭.asIdeal.primesOver (𝓞 (f.map (algebraMap (𝓞 K) K)).SplittingField)))
  exact ⟨_, frob_partition hD f hf 𝔭 hsq Q⟩

end Dedekind

/-! ## Cycle types in small symmetric groups -/

section PermCounts

set_option linter.unusedSectionVars false

/-- Conjugating a permutation by an equivalence of the underlying types preserves its cycle type. -/
theorem cycleType_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (π : Equiv.Perm α) : (e.permCongr π).cycleType = π.cycleType := by
  have h := Equiv.Perm.cycleType_extendDomain (g := π) (p := fun _ : β => True)
    (e.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm)
  rw [← h]
  congr 1

theorem parts_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (π : Equiv.Perm α) : (e.permCongr π).partition.parts = π.partition.parts := by
  rw [Equiv.Perm.parts_partition, Equiv.Perm.parts_partition, cycleType_permCongr,
    ← Equiv.Perm.sum_cycleType, ← Equiv.Perm.sum_cycleType, cycleType_permCongr, Fintype.card_congr e]

/-- Classification of permutations of a three element set. -/
theorem classify3 (π : Equiv.Perm (Fin 3)) :
    (π = 1 ∧ π.partition.parts = {1, 1, 1}) ∨ (π ≠ 1 ∧ π ^ 2 = 1 ∧ π.partition.parts = {2, 1}) ∨
      (π ^ 2 ≠ 1 ∧ π ^ 3 = 1 ∧ π.partition.parts = {3}) := by
  revert π
  decide


section S3

variable {G α : Type*} [Group G] [Fintype G] [Fintype α] [DecidableEq α]

theorem classify3_perm (hα : Fintype.card α = 3) (π : Equiv.Perm α) :
    (π = 1 ∧ π.partition.parts = {1, 1, 1}) ∨ (π ≠ 1 ∧ π ^ 2 = 1 ∧ π.partition.parts = {2, 1}) ∨
      (π ^ 2 ≠ 1 ∧ π ^ 3 = 1 ∧ π.partition.parts = {3}) := by
  let e : α ≃ Fin 3 := Fintype.equivFinOfCardEq hα
  have h := classify3 (e.permCongr π)
  have hm : ∀ n : ℕ, (e.permCongr π) ^ n = e.permCongrHom (π ^ n) := fun n =>
    (map_pow e.permCongrHom π n).symm
  have key : ∀ n : ℕ, (e.permCongr π) ^ n = 1 ↔ π ^ n = 1 := fun n => by
    rw [hm, EmbeddingLike.map_eq_one_iff]
  have key1 : e.permCongr π = 1 ↔ π = 1 := by
    simpa using key 1
  simp only [ne_eq, parts_permCongr, key1, key 2, key 3] at h
  exact h

variable (φ : G →* Equiv.Perm α) (hφ : Function.Injective φ) (hα : Fintype.card α = 3)

include hφ hα

theorem parts_eq_triv_iff (σ : G) : (φ σ).partition.parts = {1, 1, 1} ↔ σ = 1 := by
  constructor
  · intro h
    rcases classify3_perm hα (φ σ) with ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
    · exact hφ (by rw [h1, map_one])
    · rw [h] at h3; exact absurd h3 (by decide)
    · rw [h] at h3; exact absurd h3 (by decide)
  · rintro rfl
    rcases classify3_perm hα (φ 1) with ⟨-, h1⟩ | ⟨h2, -⟩ | ⟨h2, -, -⟩
    · exact h1
    · exact absurd (map_one φ) h2
    · rw [map_one] at h2; simp at h2

theorem count3_triv : (Finset.univ.filter fun σ : G => (φ σ).partition.parts = {1, 1, 1}).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨1, ?_⟩
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact parts_eq_triv_iff φ hφ hα σ

theorem count3_two (hG : Fintype.card G = 2) :
    (Finset.univ.filter fun σ : G => (φ σ).partition.parts = {2, 1}).card = 1 := by
  have h2 : ∀ σ : G, σ ^ 2 = 1 := fun σ => hG ▸ pow_card_eq_one
  have : (Finset.univ.filter fun σ : G => (φ σ).partition.parts = {2, 1}) = Finset.univ.erase 1 := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true]
    constructor
    · intro h
      rintro rfl
      exact absurd ((parts_eq_triv_iff φ hφ hα 1).2 rfl) (by rw [h]; decide)
    · intro hne
      rcases classify3_perm hα (φ σ) with ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨h1, -, -⟩
      · exact absurd (hφ (show φ σ = φ 1 by rw [h1, map_one])) hne
      · exact h3
      · exact absurd (by rw [← map_pow, h2, map_one]) h1
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hG]

theorem count3_three (hG : Fintype.card G = 3) :
    (Finset.univ.filter fun σ : G => (φ σ).partition.parts = {3}).card = 2 := by
  have h3 : ∀ σ : G, σ ^ 3 = 1 := fun σ => hG ▸ pow_card_eq_one
  have : (Finset.univ.filter fun σ : G => (φ σ).partition.parts = {3}) = Finset.univ.erase 1 := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true]
    constructor
    · intro h
      rintro rfl
      exact absurd ((parts_eq_triv_iff φ hφ hα 1).2 rfl) (by rw [h]; decide)
    · intro hne
      rcases classify3_perm hα (φ σ) with ⟨h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, -, h3'⟩
      · exact absurd (hφ (show φ σ = φ 1 by rw [h1, map_one])) hne
      · have h2' : σ ^ 2 = 1 := hφ (by rw [map_pow, h2, map_one])
        exact absurd (by
          calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
            _ = 1 := by rw [h3 σ, h2']; simp) hne
      · exact h3'
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hG]

theorem count3_six (hG : Fintype.card G = 6) (τ : Multiset ℕ) :
    (Finset.univ.filter fun σ : G => (φ σ).partition.parts = τ).card =
      Fintype.card {π : Equiv.Perm (Fin 3) // π.partition.parts = τ} := by
  have hb : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hφ, ?_⟩
    rw [hG, Fintype.card_perm, hα]
    rfl
  let e : α ≃ Fin 3 := Fintype.equivFinOfCardEq hα
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr ?_
  exact (Equiv.subtypeEquiv (Equiv.ofBijective φ hb) (p := fun σ : G => (φ σ).partition.parts = τ)
      (q := fun π : Equiv.Perm α => π.partition.parts = τ) (fun _ => Iff.rfl)).trans
    (Equiv.subtypeEquiv e.permCongr (p := fun π : Equiv.Perm α => π.partition.parts = τ)
      (q := fun π : Equiv.Perm (Fin 3) => π.partition.parts = τ) (fun π => by rw [parts_permCongr]))

end S3

example : Fintype.card {π : Equiv.Perm (Fin 3) // π.partition.parts = {2, 1}} = 3 := by decide
example : Fintype.card {π : Equiv.Perm (Fin 3) // π.partition.parts = {3}} = 2 := by decide


/-! ### The dihedral group of order 8 in the symmetric group on four letters -/

/-- The eight elements of a dihedral subgroup of order eight of `S₄`. -/
def D4set : Finset (Equiv.Perm (Fin 4)) :=
  {1, finRotate 4, finRotate 4 ^ 2, finRotate 4 ^ 3, Equiv.swap 0 2, finRotate 4 * Equiv.swap 0 2,
    finRotate 4 ^ 2 * Equiv.swap 0 2, finRotate 4 ^ 3 * Equiv.swap 0 2}

theorem D4set_mul : ∀ a ∈ D4set, ∀ b ∈ D4set, a * b ∈ D4set := by
  unfold D4set
  decide

theorem D4set_inv : ∀ a ∈ D4set, a⁻¹ ∈ D4set := by
  unfold D4set
  decide

def D4 : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {π | π ∈ D4set}
  one_mem' := by unfold D4set; decide
  mul_mem' := fun {a b} ha hb => D4set_mul a ha b hb
  inv_mem' := fun {a} ha => D4set_inv a ha

theorem card_D4set : D4set.card = 8 := by
  unfold D4set
  decide

/-- A subgroup of order eight of `S₄` is a Sylow `2`-subgroup. -/
def sylowOfCard8 (H : Subgroup (Equiv.Perm (Fin 4))) (h : Nat.card H = 8) : Sylow 2 (Equiv.Perm (Fin 4)) :=
  (IsPGroup.of_card (p := 2) (n := 3) (G := H) (by simpa using h)).toSylow (by
    have h1 := Subgroup.card_mul_index H
    have h2 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [h, h2] at h1
    have : H.index = 3 := by omega
    rw [this]
    decide)

theorem coe_sylowOfCard8 (H : Subgroup (Equiv.Perm (Fin 4))) (h : Nat.card H = 8) :
    (sylowOfCard8 H h : Subgroup (Equiv.Perm (Fin 4))) = H := rfl

theorem card_conj {β : Type*} [Fintype β] [DecidableEq β] (K H : Subgroup (Equiv.Perm β)) (g : Equiv.Perm β)
    (hmem : ∀ x, x ∈ H ↔ g⁻¹ * x * g ∈ K) (τ : Multiset ℕ) :
    Nat.card {π : Equiv.Perm β // π ∈ H ∧ π.partition.parts = τ} =
      Nat.card {π : Equiv.Perm β // π ∈ K ∧ π.partition.parts = τ} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g⁻¹).toEquiv ?_)
  intro π
  have hc : (g⁻¹ * π * g).partition.parts = π.partition.parts := by
    have : IsConj π (g⁻¹ * π * g) := isConj_iff.2 ⟨g⁻¹, by simp⟩
    exact congrArg Nat.Partition.parts (Equiv.Perm.partition_eq_of_isConj.1 this.symm)
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply, inv_inv, hc]
  rw [hmem]

theorem count_D8 {G : Type*} [Group G] [Fintype G] (ψ : G →* Equiv.Perm (Fin 4))
    (hψ : Function.Injective ψ) (hG : Fintype.card G = 8) (τ : Multiset ℕ) :
    (Finset.univ.filter fun σ : G => (ψ σ).partition.parts = τ).card =
      (D4set.filter fun π => π.partition.parts = τ).card := by
  have hH : Nat.card ψ.range = 8 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm, Nat.card_eq_fintype_card, hG]
  have hD : Nat.card D4 = 8 := by
    calc Nat.card D4 = Nat.card (↑D4set : Set (Equiv.Perm (Fin 4))) := rfl
      _ = 8 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, card_D4set]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 4)) (sylowOfCard8 D4 hD) (sylowOfCard8 ψ.range hH)
  have hmem : ∀ x, x ∈ ψ.range ↔ g⁻¹ * x * g ∈ D4 := by
    intro x
    have h1 : x ∈ ((g • sylowOfCard8 D4 hD : Sylow 2 _) : Set (Equiv.Perm (Fin 4))) ↔
        x ∈ ((sylowOfCard8 ψ.range hH : Sylow 2 _) : Set (Equiv.Perm (Fin 4))) := by rw [hg]
    rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem] at h1
    have e : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
      simp
    rw [e] at h1
    exact h1.symm
  have e1 : Fintype.card {σ : G // (ψ σ).partition.parts = τ} =
      Fintype.card {π : Equiv.Perm (Fin 4) // π ∈ ψ.range ∧ π.partition.parts = τ} :=
    Fintype.card_congr ((Equiv.subtypeEquiv (MonoidHom.ofInjective hψ).toEquiv
      (q := fun r : ψ.range => (r : Equiv.Perm (Fin 4)).partition.parts = τ) (fun σ => Iff.rfl)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun π => π ∈ ψ.range) (fun π => π.partition.parts = τ)))
  rw [← Fintype.card_subtype, e1, ← Nat.card_eq_fintype_card, card_conj D4 ψ.range g hmem τ,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

section S4

variable {G α : Type*} [Group G] [Fintype G] [Fintype α] [DecidableEq α]

theorem count4_D8 (φ : G →* Equiv.Perm α) (hφ : Function.Injective φ) (hα : Fintype.card α = 4)
    (hG : Fintype.card G = 8) (τ : Multiset ℕ) :
    (Finset.univ.filter fun σ : G => (φ σ).partition.parts = τ).card =
      (D4set.filter fun π => π.partition.parts = τ).card := by
  let e : α ≃ Fin 4 := Fintype.equivFinOfCardEq hα
  have := count_D8 (e.permCongrHom.toMonoidHom.comp φ) (e.permCongrHom.injective.comp hφ) hG τ
  rw [← this]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show _ = _ ↔ (e.permCongr (φ σ)).partition.parts = τ
  rw [parts_permCongr]

end S4

theorem D4_count_one : (D4set.filter fun π => π.partition.parts = {1, 1, 1, 1}).card = 1 := by
  unfold D4set
  decide

theorem D4_count_two_one_one : (D4set.filter fun π => π.partition.parts = {2, 1, 1}).card = 2 := by
  unfold D4set
  decide

theorem D4_count_two_two : (D4set.filter fun π => π.partition.parts = {2, 2}).card = 3 := by
  unfold D4set
  decide

theorem D4_count_four : (D4set.filter fun π => π.partition.parts = {4}).card = 2 := by
  unfold D4set
  decide


end PermCounts

/-! ## Reduction of integer polynomials modulo rational primes -/

section Reduction

/-- Every rational prime lies under some prime ideal of the ring of integers of a number field. -/
theorem exists_heightOneSpectrum_mem (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal := by
  have hmax : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := by
    have : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact (Ideal.span_singleton_prime this.ne_zero |>.mpr this).isMaximal (by simpa using this.ne_zero)
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have : x = 0 := by simpa using hx
      simp [this])
  have hmem : ((p : ℕ) : 𝓞 K) ∈ Q := by
    have : ((p : ℕ) : ℤ) ∈ Ideal.span {((p : ℕ) : ℤ)} := Ideal.mem_span_singleton_self _
    have h2 := hl.symm
    rw [Ideal.under_def] at h2
    rw [h2] at this
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  intro h
  rw [h] at hmem
  have : ((p : ℕ) : 𝓞 K) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

/-- The residue field of a prime of `𝓞 ℚ` above `p` is `ZMod p`: there is a bijective ring map from `ZMod p`,
compatible with the maps from `ℤ`. -/
theorem exists_zmod_ringHom (p : ℕ) [hp : Fact p.Prime] (𝔭 : HeightOneSpectrum (𝓞 ℚ))
    (hmem : ((p : ℕ) : 𝓞 ℚ) ∈ 𝔭.asIdeal) :
    ∃ ψ : ZMod p →+* 𝔭.asIdeal.ResidueField, Function.Bijective ψ ∧
      ψ.comp (Int.castRingHom (ZMod p)) =
        (algebraMap (𝓞 ℚ) 𝔭.asIdeal.ResidueField).comp (Int.castRingHom (𝓞 ℚ)) := by
  haveI := 𝔭.isPrime
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  have h0 : ((p : ℕ) : 𝔭.asIdeal.ResidueField) = 0 := by
    have := (Ideal.algebraMap_residueField_eq_zero (I := 𝔭.asIdeal)).2 hmem
    simpa using this
  haveI : CharP 𝔭.asIdeal.ResidueField p := (CharP.charP_iff_prime_eq_zero hp.out).2 h0
  let ψ := ZMod.castHom (dvd_refl p) 𝔭.asIdeal.ResidueField
  have hcomp : ψ.comp (Int.castRingHom (ZMod p)) =
      (algebraMap (𝓞 ℚ) 𝔭.asIdeal.ResidueField).comp (Int.castRingHom (𝓞 ℚ)) :=
    RingHom.ext_int _ _
  refine ⟨ψ, ⟨ψ.injective, fun x => ?_⟩, hcomp⟩
  obtain ⟨z, rfl⟩ := Ideal.algebraMap_residueField_surjective 𝔭.asIdeal x
  obtain ⟨n, rfl⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) z
  refine ⟨(n : ZMod p), ?_⟩
  have := congrArg (fun φ => φ n) hcomp
  simp at this ⊢

/-- Transporting a polynomial along a field isomorphism does not change the degrees of its normalized
irreducible factors. -/
theorem natDegree_normalizedFactors_map {F k : Type*} [Field F] [Field k] [DecidableEq F] [DecidableEq k]
    (e : F ≃+* k) (P : F[X]) :
    (normalizedFactors (P.map (e : F →+* k))).map natDegree = (normalizedFactors P).map natDegree := by
  by_cases hP : P = 0
  · simp [hP]
  have hirr : ∀ q ∈ normalizedFactors P, Irreducible (q.map (e : F →+* k)) := by
    intro q hq
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e).toMulEquiv).2 (irreducible_of_normalized_factor q hq)
  have hassoc : Associated P (normalizedFactors P).prod := (prod_normalizedFactors hP).symm
  have h1 : Associated (P.map (e : F →+* k))
      (((normalizedFactors P).map (Polynomial.map (e : F →+* k))).prod) := by
    have := hassoc.map (Polynomial.mapRingHom (e : F →+* k))
    simpa [map_multiset_prod, Multiset.map_map, Function.comp_def] using this
  rw [h1.normalizedFactors_eq, normalizedFactors_prod_eq _ (by simpa using hirr)]
  simp [Multiset.map_map, natDegree_normalize, natDegree_map]

theorem squarefree_mulEquiv {A B : Type*} [CommMonoid A] [CommMonoid B] (E : A ≃* B) {a : A}
    (h : Squarefree a) : Squarefree (E a) := by
  intro y hy
  have : E.symm y * E.symm y ∣ a := by
    have := map_dvd E.symm hy
    simpa using this
  simpa using (h _ this).map E

/-- Transporting a polynomial along a field isomorphism preserves being squarefree. -/
theorem squarefree_map_ringEquiv {F k : Type*} [Field F] [Field k] (e : F ≃+* k) {P : F[X]} :
    Squarefree (P.map (e : F →+* k)) ↔ Squarefree P := by
  refine ⟨fun h => ?_, fun h => squarefree_mulEquiv (Polynomial.mapEquiv e).toMulEquiv h⟩
  have := squarefree_mulEquiv (Polynomial.mapEquiv e.symm).toMulEquiv h
  simpa [Polynomial.map_map] using this

/-- **Theorem 8.23 for integer polynomials**: if the reduction of a monic `P ∈ ℤ[X]` modulo a prime `p` is squarefree,
the Galois group of `P` over `ℚ` contains a permutation of the roots with cycle type the degrees of the irreducible
factors of `P` modulo `p`. -/
theorem thm_8_23_zmod (hD : DedekindFrobenius) (p : ℕ) [Fact p.Prime] (P : ℤ[X]) (hP : P.Monic)
    (hsq : Squarefree (P.map (Int.castRingHom (ZMod p)))) :
    ∃ σ : (P.map (Int.castRingHom ℚ)).Gal,
      (galPerm (P.map (Int.castRingHom ℚ)) σ).partition.parts =
        (normalizedFactors (P.map (Int.castRingHom (ZMod p)))).map natDegree := by
  obtain ⟨𝔭, h𝔭⟩ := exists_heightOneSpectrum_mem ℚ p Fact.out
  obtain ⟨ψ, hψ, hcomp⟩ := exists_zmod_ringHom p 𝔭 h𝔭
  let e : ZMod p ≃+* 𝔭.asIdeal.ResidueField := RingEquiv.ofBijective ψ hψ
  set F : (𝓞 ℚ)[X] := P.map (Int.castRingHom (𝓞 ℚ)) with hF
  have hFm : F.Monic := hP.map _
  have hred : F.map (algebraMap (𝓞 ℚ) 𝔭.asIdeal.ResidueField) =
      (P.map (Int.castRingHom (ZMod p))).map (e : ZMod p →+* 𝔭.asIdeal.ResidueField) := by
    rw [hF, Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact hcomp.symm
  have hsq' : Squarefree (F.map (algebraMap (𝓞 ℚ) 𝔭.asIdeal.ResidueField)) := by
    rw [hred]
    exact (squarefree_map_ringEquiv e).2 hsq
  have hex : ∃ σ : (F.map (algebraMap (𝓞 ℚ) ℚ)).Gal,
      (galPerm (F.map (algebraMap (𝓞 ℚ) ℚ)) σ).partition.parts =
        (normalizedFactors (P.map (Int.castRingHom (ZMod p)))).map natDegree := by
    obtain ⟨σ, hσ⟩ := thm_8_23 hD F hFm 𝔭 hsq'
    refine ⟨σ, hσ.trans ?_⟩
    rw [hred]
    exact natDegree_normalizedFactors_map e _
  have hm : F.map (algebraMap (𝓞 ℚ) ℚ) = P.map (Int.castRingHom ℚ) := by
    rw [hF, Polynomial.map_map]
    congr 1
  rw [hm] at hex
  exact hex

/-- The degrees of the normalized factors of an irreducible polynomial. -/
theorem nf_deg_irreducible {k : Type*} [Field k] [DecidableEq k] {Q : k[X]} (hQ : Irreducible Q) :
    (normalizedFactors Q).map natDegree = {Q.natDegree} := by
  rw [normalizedFactors_irreducible hQ]
  simp [natDegree_normalize]

/-- The degrees of the normalized factors of a product of two irreducible polynomials. -/
theorem nf_deg_mul {k : Type*} [Field k] [DecidableEq k] {Q₁ Q₂ : k[X]} (h₁ : Irreducible Q₁)
    (h₂ : Irreducible Q₂) :
    (normalizedFactors (Q₁ * Q₂)).map natDegree = {Q₁.natDegree, Q₂.natDegree} := by
  rw [normalizedFactors_mul h₁.ne_zero h₂.ne_zero, normalizedFactors_irreducible h₁,
    normalizedFactors_irreducible h₂]
  simp [natDegree_normalize]

/-- A product of two irreducible polynomials of different degrees is squarefree. -/
theorem squarefree_mul_of_natDegree_ne {k : Type*} [Field k] [DecidableEq k] {Q₁ Q₂ : k[X]}
    (h₁ : Irreducible Q₁) (h₂ : Irreducible Q₂) (hd : Q₁.natDegree ≠ Q₂.natDegree) :
    Squarefree (Q₁ * Q₂) := by
  refine (squarefree_iff_nodup_normalizedFactors (mul_ne_zero h₁.ne_zero h₂.ne_zero)).2 ?_
  rw [normalizedFactors_mul h₁.ne_zero h₂.ne_zero, normalizedFactors_irreducible h₁,
    normalizedFactors_irreducible h₂]
  simp only [Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton,
    and_true]
  intro h
  exact hd (by simpa [natDegree_normalize] using congrArg natDegree h)

/-- The degrees of the normalized factors of `g * h`, where `g` is irreducible of degree `2` and `h` is irreducible
of odd degree or a product of two irreducible polynomials of odd degree. -/
theorem nf_deg_quad_mul {k : Type*} [Field k] [DecidableEq k] (g h : k[X]) (hg : Irreducible g)
    (hg2 : g.natDegree = 2) (hh0 : h ≠ 0)
    (hh : (Irreducible h ∧ Odd h.natDegree) ∨ ∃ h₁ h₂ : k[X], h = h₁ * h₂ ∧ Irreducible h₁ ∧
      Odd h₁.natDegree ∧ Irreducible h₂ ∧ Odd h₂.natDegree) :
    ∃ O : Multiset ℕ, 1 ≤ O.sum ∧ (∀ x ∈ O, Odd x) ∧
      (normalizedFactors (g * h)).map natDegree = 2 ::ₘ O := by
  rw [normalizedFactors_mul hg.ne_zero hh0, Multiset.map_add, normalizedFactors_irreducible hg]
  rcases hh with ⟨hirr, hodd⟩ | ⟨h₁, h₂, rfl, hi₁, ho₁, hi₂, ho₂⟩
  · refine ⟨{h.natDegree}, by rw [Multiset.sum_singleton]; exact hodd.pos, by simpa using hodd, ?_⟩
    rw [normalizedFactors_irreducible hirr]
    simp [natDegree_normalize, hg2]
  · refine ⟨{h₁.natDegree, h₂.natDegree}, ?_, ?_, ?_⟩
    · simpa using Nat.le_add_right_of_le ho₁.pos
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [ho₁, ho₂]
    · rw [normalizedFactors_mul hi₁.ne_zero hi₂.ne_zero, normalizedFactors_irreducible hi₁,
        normalizedFactors_irreducible hi₂]
      simp [natDegree_normalize, hg2]
      exact Multiset.cons_swap _ _ _

end Reduction

/-! ## Helpers for Examples 8.25 and 8.27 -/

section GaloisHelpers

/-- The permutation representation of the Galois group of a polynomial on its roots is injective (the roots
generate the splitting field). -/
theorem galPerm_injective {F : Type*} [Field F] (g : F[X]) :
    Function.Injective (MulAction.toPermHom g.Gal (g.rootSet g.SplittingField)) := by
  rw [injective_iff_map_eq_one]
  intro ϕ hϕ
  have h1 : ∀ x ∈ g.rootSet g.SplittingField, ϕ x = x := by
    intro x hx
    exact congrArg (fun π : Equiv.Perm (g.rootSet g.SplittingField) => (π ⟨x, hx⟩ : g.SplittingField)) hϕ
  have h2 : ϕ.toAlgHom = (1 : g.Gal).toAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (SplittingField.adjoin_rootSet g) (fun x hx => h1 x hx)
  exact AlgEquiv.ext fun y => congrArg (fun φ : g.SplittingField →ₐ[F] g.SplittingField => φ y) h2

/-- A separable polynomial over a field of characteristic zero has as many roots in its splitting field as its
degree. -/
theorem card_rootSet_splittingField {F : Type*} [Field F] [CharZero F] (g : F[X]) (hs : g.Separable) :
    Fintype.card (g.rootSet g.SplittingField) = g.natDegree :=
  card_rootSet_eq_natDegree hs (SplittingField.splits g)


/-- The residues of the coefficients `-15, 10, 6` modulo `2`, `3`, `5`. -/
theorem zmod_cast_facts :
    ((-15 : ℤ) : ZMod 2) = 1 ∧ ((10 : ℤ) : ZMod 2) = 0 ∧ ((6 : ℤ) : ZMod 2) = 0 ∧
    ((-15 : ℤ) : ZMod 3) = 0 ∧ ((10 : ℤ) : ZMod 3) = 1 ∧ ((6 : ℤ) : ZMod 3) = 0 ∧
    ((-15 : ℤ) : ZMod 5) = 0 ∧ ((10 : ℤ) : ZMod 5) = 0 ∧ ((6 : ℤ) : ZMod 5) = 1 := by decide

/-- `X ^ 2 + X + 1` has no root in `ZMod 2`. -/
theorem zmod2_no_root_quad : ∀ x : ZMod 2, x ^ 2 + x + 1 ≠ 0 := by decide

/-- `X ^ 3 + X ^ 2 + 1` has no root in `ZMod 2`. -/
theorem zmod2_no_root_cubic : ∀ x : ZMod 2, x ^ 3 + x ^ 2 + 1 ≠ 0 := by decide

/-- A permutation of a five element set of cycle type `(3, 2)` has a cube of cycle type `(2, 1, 1, 1)`. -/
theorem pow3_fin5 : ∀ ρ : Equiv.Perm (Fin 5), ρ.partition.parts = {3, 2} →
    (ρ ^ 3).partition.parts = {2, 1, 1, 1} := by
  decide +kernel

theorem pow3_perm {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α = 5) (ρ : Equiv.Perm α)
    (h : ρ.partition.parts = {3, 2}) : (ρ ^ 3).partition.parts = {2, 1, 1, 1} := by
  let e : α ≃ Fin 5 := Fintype.equivFinOfCardEq hα
  have h1 := pow3_fin5 (e.permCongr ρ) (by rw [parts_permCongr]; exact h)
  have h2 : (e.permCongr ρ) ^ 3 = e.permCongr (ρ ^ 3) := (map_pow e.permCongrHom ρ 3).symm
  rw [h2, parts_permCongr] at h1
  exact h1

/-- A permutation of cycle type `(2, 1, 1, 1)` is a transposition. -/
theorem isSwap_of_parts {α : Type*} [Fintype α] [DecidableEq α] (π : Equiv.Perm α)
    (h : π.partition.parts = {2, 1, 1, 1}) : π.IsSwap := by
  rw [Equiv.Perm.isSwap_iff_cycleType, ← Equiv.Perm.filter_parts_partition_eq_cycleType, h]
  decide +kernel

/-- An irreducible polynomial of prime degree over a field of characteristic zero whose Galois group contains an
element acting as a transposition on the roots has Galois group the full symmetric group. -/
theorem bijective_galPerm_of_swap {F : Type*} [Field F] [CharZero F] (g : F[X]) (hirr : Irreducible g)
    (hdeg : g.natDegree.Prime) (τ : g.Gal) (hτ : (galPerm g τ).IsSwap) : Function.Bijective (galPerm g) := by
  have hα : Fintype.card (g.rootSet g.SplittingField) = g.natDegree :=
    card_rootSet_splittingField g hirr.separable
  have hinj := galPerm_injective g
  set φ := MulAction.toPermHom g.Gal (g.rootSet g.SplittingField) with hφ
  have htop : φ.range = ⊤ :=
    Equiv.Perm.subgroup_eq_top_of_swap_mem (by rw [hα]; exact hdeg) (by
      have h2 := Polynomial.Gal.prime_degree_dvd_card hirr hdeg
      rw [hα]
      convert h2 using 1
      rw [Fintype.card_eq_nat_card]
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm) ⟨τ, rfl⟩ hτ
  refine ⟨hinj, fun y => ?_⟩
  have : y ∈ φ.range := htop ▸ Subgroup.mem_top y
  exact this

/-- A product of odd numbers is odd. -/
theorem odd_multiset_prod (O : Multiset ℕ) (hO : ∀ x ∈ O, Odd x) : Odd O.prod := by
  induction O using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (hO a (Multiset.mem_cons_self _ _)).mul (ih fun x hx => hO x (Multiset.mem_cons_of_mem hx))

/-- If a permutation has cycle type `2` together with odd cycle lengths `O` (fixed points included), then its
`∏ O`-th power is a transposition (the odd cycles die, the `2`-cycle survives). -/
theorem isSwap_pow_of_parts {α : Type*} [Fintype α] [DecidableEq α] (π : Equiv.Perm α) (O : Multiset ℕ)
    (hO : ∀ x ∈ O, Odd x) (h : π.partition.parts = 2 ::ₘ O) : (π ^ O.prod).IsSwap := by
  have hct : π.cycleType = (2 ::ₘ O).filter (2 ≤ ·) := by
    rw [← h, Equiv.Perm.filter_parts_partition_eq_cycleType]
  have h2mem : 2 ∈ π.cycleType := by
    rw [hct]
    simp
  have hcount : Multiset.count 2 π.cycleType = 1 := by
    rw [hct, Multiset.count_filter_of_pos (by norm_num), Multiset.count_cons_self]
    have : 2 ∉ O := fun h2 => (Nat.not_odd_iff_even.2 even_two) (hO 2 h2)
    simp [Multiset.count_eq_zero_of_notMem this]
  obtain ⟨c, hc, hcc⟩ := Multiset.mem_map.1 (Equiv.Perm.cycleType_def π ▸ h2mem)
  have hc' : c ∈ π.cycleFactorsFinset := hc
  have hcard : c.support.card = 2 := hcc
  have hswap : c.IsSwap := Equiv.Perm.card_support_eq_two.1 hcard
  have hcyc : c.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc').1
  have hct_c : c.cycleType = {2} := by rw [hcyc.cycleType, hcard]
  have hsub : (π * c⁻¹).cycleType = π.cycleType - {2} := by
    rw [Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub hc', hct_c]
  have hdisj : Equiv.Perm.Disjoint (π * c⁻¹) c := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc'
  have hcomm : Commute (π * c⁻¹) c := hdisj.commute
  have hπ : π = (π * c⁻¹) * c := by simp
  have hm : Odd O.prod := odd_multiset_prod O hO
  have hc'm : (π * c⁻¹) ^ O.prod = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType]
    apply Multiset.lcm_dvd.2
    intro ℓ hℓ
    rw [hsub] at hℓ
    have hℓ' : ℓ ∈ π.cycleType := Multiset.mem_of_le tsub_le_self hℓ
    have hne : ℓ ≠ 2 := by
      rintro rfl
      have h0 : Multiset.count 2 (π.cycleType - {2}) = 0 := by
        rw [Multiset.count_sub, hcount]
        simp
      exact (Multiset.count_pos.2 hℓ).ne' h0
    rw [hct, Multiset.mem_filter] at hℓ'
    rcases Multiset.mem_cons.1 hℓ'.1 with h2 | hO'
    · exact absurd h2 hne
    · exact Multiset.dvd_prod hO'
  have hc2 : c ^ O.prod = c := by
    obtain ⟨k, hk⟩ := hm
    have : c ^ 2 = 1 := by rw [← hswap.orderOf]; exact pow_orderOf_eq_one c
    rw [hk, pow_succ, pow_mul, this, one_pow, one_mul]
  have hfin : π ^ O.prod = c :=
    calc π ^ O.prod = ((π * c⁻¹) * c) ^ O.prod := by rw [← hπ]
      _ = (π * c⁻¹) ^ O.prod * c ^ O.prod := hcomm.mul_pow _
      _ = c := by rw [hc'm, hc2, one_mul]
  rw [hfin]
  exact hswap

/-- A subgroup of the symmetric group containing a permutation moving every point in a single cycle is
transitive. -/
theorem isPretransitive_of_cycle {α : Type*} [Fintype α] [DecidableEq α] (H : Subgroup (Equiv.Perm α))
    (σ : Equiv.Perm α) (hσ : σ ∈ H) (hc : σ.IsCycle) (hs : σ.support = Finset.univ) :
    MulAction.IsPretransitive H α := by
  refine ⟨fun x y => ?_⟩
  have hx : σ x ≠ x := Equiv.Perm.mem_support.1 (hs ▸ Finset.mem_univ x)
  have hy : σ y ≠ y := Equiv.Perm.mem_support.1 (hs ▸ Finset.mem_univ y)
  obtain ⟨i, hi⟩ := hc.exists_pow_eq hx hy
  exact ⟨⟨σ ^ i, H.pow_mem hσ i⟩, hi⟩

/-- A permutation of cycle type `(n)` with `n ≥ 2` is a cycle whose support is everything. -/
theorem isCycle_of_parts_single {α : Type*} [Fintype α] [DecidableEq α] (π : Equiv.Perm α) (n : ℕ)
    (hn : 2 ≤ n) (h : π.partition.parts = {n}) : π.IsCycle ∧ π.support = Finset.univ := by
  have hct : π.cycleType = {n} := by
    rw [← Equiv.Perm.filter_parts_partition_eq_cycleType, h]
    simp [hn]
  have hcard : Fintype.card α = n := by
    have := π.partition.parts_sum
    rw [h] at this
    simpa using this.symm
  refine ⟨Equiv.Perm.card_cycleType_eq_one.1 (by simp [hct]), ?_⟩
  apply Finset.eq_univ_of_card
  rw [← Equiv.Perm.sum_cycleType, hct, hcard]
  simp

/-- A polynomial over a field of characteristic zero whose Galois group contains an `n`-cycle, an element of cycle
type `(1, n - 1)` and an element of cycle type `2` plus odd cycle lengths has the full symmetric group as its
Galois group (Lemma 8.26 together with the power trick of Example 8.27). -/
theorem bijective_galPerm_of_types {F : Type*} [Field F] [CharZero F] (g : F[X]) (n : ℕ) (hn : 2 ≤ n)
    (σ₁ σ₂ σ₃ : g.Gal) (O : Multiset ℕ) (hO : ∀ x ∈ O, Odd x)
    (h₁ : (galPerm g σ₁).partition.parts = {n}) (h₂ : (galPerm g σ₂).partition.parts = {1, n - 1})
    (h₃ : (galPerm g σ₃).partition.parts = 2 ::ₘ O) : Function.Bijective (galPerm g) := by
  have hcard : Fintype.card (g.rootSet g.SplittingField) = n := by
    have := (galPerm g σ₁).partition.parts_sum
    rw [h₁] at this
    simpa using this.symm
  have hinj := galPerm_injective g
  set φ := MulAction.toPermHom g.Gal (g.rootSet g.SplittingField) with hφ
  obtain ⟨hcyc, hsupp⟩ := isCycle_of_parts_single (φ σ₁) n hn h₁
  have htop : φ.range = ⊤ :=
    lemma_8_26 φ.range (isPretransitive_of_cycle φ.range (φ σ₁) ⟨σ₁, rfl⟩ hcyc hsupp)
      ⟨φ σ₂, ⟨σ₂, rfl⟩, (h₂.trans (Multiset.pair_comm _ _)).trans (by rw [hcard])⟩
      ⟨(φ σ₃) ^ O.prod, φ.range.pow_mem ⟨σ₃, rfl⟩ _, isSwap_pow_of_parts _ O hO h₃⟩
  refine ⟨hinj, fun y => ?_⟩
  have : y ∈ φ.range := htop ▸ Subgroup.mem_top y
  exact this

end GaloisHelpers

/-! ## Examples 8.25 and 8.27 -/

/-- **Example 8.25** (conditional on `DedekindFrobenius`): the Galois group of $X^5 - X - 1$ over $\mathbb Q$ is
$S_5$ (all permutations of the five roots). Modulo $2$ it is $(X^2+X+1)(X^3+X^2+1)$ and modulo $3$ it is
irreducible, so $G$ contains a $5$-cycle and a permutation of type $(2,3)$, whose cube is a transposition. -/
@[kb "milne2020ant" "v3.08, Ex. 8.25, p. 146"]
theorem example_8_25 (hD : DedekindFrobenius) :
    Function.Bijective (galPerm (X ^ 5 - X - 1 : ℚ[X])) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : ℤ[X] := X ^ 5 - X - 1 with hP
  have hPm : P.Monic := by
    rw [hP]
    monicity!
  have hPQ : P.map (Int.castRingHom ℚ) = X ^ 5 - X - 1 := by simp [hP]
  have hirr : Irreducible (X ^ 5 - X - 1 : ℚ[X]) := X_pow_sub_X_sub_one_irreducible_rat (by norm_num)
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have := CharP.cast_eq_zero ((ZMod 2)[X]) 2
    simpa using this
  have hP2 : P.map (Int.castRingHom (ZMod 2)) = (X ^ 2 + X + 1) * (X ^ 3 + X ^ 2 + 1) := by
    simp only [hP, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    linear_combination (-(X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X])) * h2
  have hA : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · have : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
      rw [this]; decide
    · intro x
      simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
      exact zmod2_no_root_quad x
  have hB : Irreducible (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · have : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!
      rw [this]; decide
    · intro x
      simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
      exact zmod2_no_root_cubic x
  have hAm : (X ^ 2 + X + 1 : (ZMod 2)[X]).Monic := by monicity!
  have hBm : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).Monic := by monicity!
  have hnf : normalizedFactors ((X ^ 2 + X + 1) * (X ^ 3 + X ^ 2 + 1) : (ZMod 2)[X]) =
      {X ^ 2 + X + 1, X ^ 3 + X ^ 2 + 1} := by
    have := normalizedFactors_prod_eq ({X ^ 2 + X + 1, X ^ 3 + X ^ 2 + 1} : Multiset (ZMod 2)[X]) (by
      intro a ha
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
      rcases ha with rfl | rfl
      exacts [hA, hB])
    simpa [hAm.normalize_eq_self, hBm.normalize_eq_self] using this
  have hne : (X ^ 2 + X + 1 : (ZMod 2)[X]) ≠ X ^ 3 + X ^ 2 + 1 := by
    intro h
    have := congrArg natDegree h
    have h1 : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    have h2 : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!
    omega
  have hsq : Squarefree (P.map (Int.castRingHom (ZMod 2))) := by
    rw [hP2]
    refine (squarefree_iff_nodup_normalizedFactors (mul_ne_zero hA.ne_zero hB.ne_zero)).2 ?_
    rw [hnf]
    simpa using hne
  obtain ⟨ρ, hρ⟩ := thm_8_23_zmod hD 2 P hPm hsq
  rw [hP2, hnf] at hρ
  have hρ' : (galPerm (P.map (Int.castRingHom ℚ)) ρ).partition.parts = {3, 2} := by
    rw [hρ]
    have h1 : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    have h2 : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!
    simp [h1, h2]
    decide
  have hcard : Fintype.card ((P.map (Int.castRingHom ℚ)).rootSet (P.map (Int.castRingHom ℚ)).SplittingField) = 5 := by
    have := (galPerm (P.map (Int.castRingHom ℚ)) ρ).partition.parts_sum
    rw [hρ'] at this
    simpa using this.symm
  have hτ := pow3_perm hcard _ hρ'
  suffices H : ∀ g : ℚ[X], g = P.map (Int.castRingHom ℚ) → Function.Bijective (galPerm g) from
    H _ hPQ.symm
  intro g hg
  subst hg
  refine bijective_galPerm_of_swap _ (hPQ ▸ hirr) ?_ (ρ ^ 3) ?_
  · rw [hPQ]
    have : (X ^ 5 - X - 1 : ℚ[X]).natDegree = 5 := by compute_degree!
    rw [this]; norm_num
  · have hpow : galPerm (P.map (Int.castRingHom ℚ)) (ρ ^ 3) = galPerm (P.map (Int.castRingHom ℚ)) ρ ^ 3 :=
      map_pow (MulAction.toPermHom (P.map (Int.castRingHom ℚ)).Gal _) ρ 3
    rw [hpow]
    exact isSwap_of_parts _ hτ

/-- **Example 8.27** (conditional on `DedekindFrobenius`): if $f_1, f_2, f_3 \in \mathbb Z[X]$ are monic of degree
$n$ with (a) $f_1$ irreducible modulo $2$, (b) $f_2 \equiv$ (degree $1$)(irreducible of degree $n-1$) modulo $3$,
(c) $f_3 \equiv$ (irreducible of degree $2$)(one or two irreducible factors of odd degree) modulo $5$, with distinct
roots modulo $5$, then $f = -15f_1 + 10f_2 + 6f_3$ has Galois group $S_n$.

*Correction.* Milne writes $f = 15f_1 + 10f_2 + 6f_3$, which has leading coefficient $31$, so is not monic and
Theorem 8.23 (stated for monic polynomials) does not apply as stated; $-15f_1 + 10f_2 + 6f_3$ is monic and has the
same reductions modulo $2$, $3$, $5$. -/
@[kb "milne2020ant" "v3.08, Ex. 8.27, p. 146"]
theorem example_8_27 (hD : DedekindFrobenius) (n : ℕ) (f₁ f₂ f₃ : ℤ[X])
    (h₁ : f₁.Monic) (h₂ : f₂.Monic) (h₃ : f₃.Monic)
    (d₁ : f₁.natDegree = n) (d₂ : f₂.natDegree = n) (d₃ : f₃.natDegree = n)
    (ha : Irreducible (f₁.map (Int.castRingHom (ZMod 2))))
    (hb : ∃ a b : (ZMod 3)[X], f₂.map (Int.castRingHom (ZMod 3)) = a * b ∧ a.natDegree = 1 ∧ Irreducible b ∧
      b.natDegree = n - 1)
    (hc : Squarefree (f₃.map (Int.castRingHom (ZMod 5))) ∧
      ∃ g h : (ZMod 5)[X], f₃.map (Int.castRingHom (ZMod 5)) = g * h ∧ Irreducible g ∧ g.natDegree = 2 ∧
        ((Irreducible h ∧ Odd h.natDegree) ∨
          ∃ h₁ h₂ : (ZMod 5)[X], h = h₁ * h₂ ∧ Irreducible h₁ ∧ Odd h₁.natDegree ∧ Irreducible h₂ ∧
            Odd h₂.natDegree)) :
    let f : ℚ[X] := (-15 * f₁ + 10 * f₂ + 6 * f₃).map (Int.castRingHom ℚ)
    Function.Bijective (galPerm f) := by
  intro f
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set P : ℤ[X] := -15 * f₁ + 10 * f₂ + 6 * f₃ with hP
  have hPe : P = C (-15) * f₁ + C 10 * f₂ + C 6 * f₃ := by simp [hP]
  have hPm : P.Monic := by
    refine monic_of_natDegree_le_of_coeff_eq_one n ?_ ?_
    · rw [hPe]
      exact (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
        (max_le ((natDegree_C_mul_le _ _).trans d₁.le) ((natDegree_C_mul_le _ _).trans d₂.le)))
        ((natDegree_C_mul_le _ _).trans d₃.le))
    · rw [hPe]
      have c1 := h₁.coeff_natDegree
      have c2 := h₂.coeff_natDegree
      have c3 := h₃.coeff_natDegree
      rw [d₁] at c1
      rw [d₂] at c2
      rw [d₃] at c3
      simp only [coeff_add, coeff_C_mul, c1, c2, c3]
      norm_num
  have hcast := zmod_cast_facts
  have hP2 : P.map (Int.castRingHom (ZMod 2)) = f₁.map (Int.castRingHom (ZMod 2)) := by
    rw [hPe]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom, hcast.1,
      hcast.2.1, hcast.2.2.1, map_zero, map_one, zero_mul, one_mul, add_zero]
  have hP3 : P.map (Int.castRingHom (ZMod 3)) = f₂.map (Int.castRingHom (ZMod 3)) := by
    rw [hPe]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom,
      hcast.2.2.2.1, hcast.2.2.2.2.1, hcast.2.2.2.2.2.1, map_zero, map_one, zero_mul, one_mul, add_zero,
      zero_add]
  have hP5 : P.map (Int.castRingHom (ZMod 5)) = f₃.map (Int.castRingHom (ZMod 5)) := by
    rw [hPe]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom,
      hcast.2.2.2.2.2.2.1, hcast.2.2.2.2.2.2.2.1, hcast.2.2.2.2.2.2.2.2, map_zero, map_one, zero_mul,
      one_mul, add_zero, zero_add]
  -- the prime 2: an `n`-cycle
  have hsq2 : Squarefree (P.map (Int.castRingHom (ZMod 2))) := by
    rw [hP2]
    exact ha.squarefree
  obtain ⟨σ₁, hσ₁⟩ := thm_8_23_zmod hD 2 P hPm hsq2
  rw [hP2, nf_deg_irreducible ha, h₁.natDegree_map, d₁] at hσ₁
  -- the prime 5: a transposition after a power
  obtain ⟨g', h', hgh, hgirr, hg2, hh⟩ := hc.2
  have hsq5 : Squarefree (P.map (Int.castRingHom (ZMod 5))) := by
    rw [hP5]
    exact hc.1
  obtain ⟨σ₃, hσ₃⟩ := thm_8_23_zmod hD 5 P hPm hsq5
  have hh0 : h' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hgh
    exact (h₃.map _).ne_zero hgh
  obtain ⟨O, hO1, hOodd, hOnf⟩ := nf_deg_quad_mul g' h' hgirr hg2 hh0 hh
  rw [hP5, hgh, hOnf] at hσ₃
  have hcard1 : Fintype.card ((P.map (Int.castRingHom ℚ)).rootSet (P.map (Int.castRingHom ℚ)).SplittingField) = n := by
    have := (galPerm (P.map (Int.castRingHom ℚ)) σ₁).partition.parts_sum
    rw [hσ₁] at this
    simpa using this.symm
  have hcard3 : 2 + O.sum = Fintype.card ((P.map (Int.castRingHom ℚ)).rootSet (P.map (Int.castRingHom ℚ)).SplittingField) := by
    have := (galPerm (P.map (Int.castRingHom ℚ)) σ₃).partition.parts_sum
    rw [hσ₃] at this
    simpa using this
  have hn3 : 3 ≤ n := by omega
  -- the prime 3: a cycle of type `(n - 1, 1)`
  obtain ⟨a, b, hab, ha1, hbirr, hbdeg⟩ := hb
  have haba : Irreducible a := by
    refine Polynomial.irreducible_of_degree_eq_one ?_
    have := (Polynomial.degree_eq_iff_natDegree_eq_of_pos Nat.one_pos).2 ha1
    simpa using this
  have hsq3 : Squarefree (P.map (Int.castRingHom (ZMod 3))) := by
    rw [hP3, hab]
    exact squarefree_mul_of_natDegree_ne haba hbirr (by rw [ha1, hbdeg]; omega)
  obtain ⟨σ₂, hσ₂⟩ := thm_8_23_zmod hD 3 P hPm hsq3
  rw [hP3, hab, nf_deg_mul haba hbirr, ha1, hbdeg] at hσ₂
  show Function.Bijective (galPerm (P.map (Int.castRingHom ℚ)))
  exact bijective_galPerm_of_types _ n (by omega) σ₁ σ₂ σ₃ O hOodd hσ₁ hσ₂ hσ₃

/-! ## Examples 8.36 and 8.37: densities of factorization types -/

section FactorizationTypes

variable {K : Type} [Field K] [NumberField K]

/-- The **factorization type** of $f$ modulo $\mathfrak p$: the multiset of degrees of the irreducible factors of
$f \bmod \mathfrak p$, recorded for the primes where $f \bmod \mathfrak p$ is squarefree. -/
def factorizationTypeSet (f : (𝓞 K)[X]) (τ : Multiset ℕ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)) ∧
    (normalizedFactors (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))).map natDegree = τ}

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! ### Additivity of densities over finite disjoint unions -/

theorem primeCount_union_disjoint {A B : Set (HeightOneSpectrum (𝓞 K))} (h : Disjoint A B) (x : ℝ) :
    primeCount (A ∪ B) x = primeCount A x + primeCount B x := by
  unfold primeCount
  have hfin := finite_setOf_absNorm_le (K := K) x
  have hu : {𝔭 ∈ A ∪ B | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} =
      {𝔭 ∈ A | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} ∪ {𝔭 ∈ B | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} := by
    ext 𝔭
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [hu]
  exact Set.ncard_union_eq (h.mono (fun _ h => h.1) (fun _ h => h.1)) (hfin.subset fun _ h => h.2)
    (hfin.subset fun _ h => h.2)

/-- Natural density is additive over disjoint unions. -/
theorem HasNaturalDensity.disjoint_union {A B : Set (HeightOneSpectrum (𝓞 K))} {a b : ℝ}
    (hA : HasNaturalDensity A a) (hB : HasNaturalDensity B b) (h : Disjoint A B) :
    HasNaturalDensity (A ∪ B) (a + b) := by
  unfold HasNaturalDensity at *
  refine (hA.add hB).congr fun x => ?_
  rw [primeCount_union_disjoint h]
  push_cast
  ring

/-- Natural density is additive over finite pairwise disjoint families. -/
theorem HasNaturalDensity.finset_iUnion {ι : Type*} (S : ι → Set (HeightOneSpectrum (𝓞 K))) (a : ι → ℝ)
    (hS : Pairwise (Function.onFun Disjoint S)) (h : ∀ i, HasNaturalDensity (S i) (a i)) (s : Finset ι) :
    HasNaturalDensity (⋃ i ∈ s, S i) (∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simpa using hasNaturalDensity_zero_of_finite (K := K) Set.finite_empty
  | insert j s hj ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
    refine (h j).disjoint_union ih ?_
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hS (fun hij => hj (hij ▸ hi))

/-- Dirichlet density is additive over finite pairwise disjoint families. -/
theorem hasDirichletDensity_finset_iUnion {ι : Type*} (S : ι → Set (HeightOneSpectrum (𝓞 K))) (a : ι → ℝ)
    (hS : Pairwise (Function.onFun Disjoint S)) (h : ∀ i, (S i).HasDirichletDensity (a i)) (s : Finset ι) :
    (⋃ i ∈ s, S i).HasDirichletDensity (∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simpa using hasDirichletDensity_zero_of_finite (F := K) Set.finite_empty
  | insert j s hj ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
    refine NumberFieldKB.Chebotarev.HasDirichletDensity.disjoint_union (h j) ih ?_
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hS (fun hij => hj (hij ▸ hi))

/-! ### Cycle types of Galois elements -/

/-- The splitting field over `K` of the image of `f` in `K[X]`. -/
abbrev SF (f : (𝓞 K)[X]) : Type := (f.map (algebraMap (𝓞 K) K)).SplittingField

/-- The cycle type (fixed points included) of an element of the Galois group, as a permutation of the roots. -/
def cyc (f : (𝓞 K)[X]) (σ : SF f ≃ₐ[K] SF f) : Multiset ℕ :=
  (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts

/-- The cycle type is a class function. -/
theorem cyc_eq_of_isConj (f : (𝓞 K)[X]) {σ τ : SF f ≃ₐ[K] SF f} (h : IsConj σ τ) : cyc f σ = cyc f τ := by
  have := Equiv.Perm.partition_eq_of_isConj.1
    (MonoidHom.map_isConj (MulAction.toPermHom (SF f ≃ₐ[K] SF f)
      ((f.map (algebraMap (𝓞 K) K)).rootSet (SF f))) h)
  exact congrArg Nat.Partition.parts this

/-- The classes of the Galois group containing an element of cycle type `τ`. -/
def typeClasses (f : (𝓞 K)[X]) (τ : Multiset ℕ) : Set (ConjClasses (SF f ≃ₐ[K] SF f)) :=
  {C | ∃ σ ∈ C.carrier, cyc f σ = τ}

theorem mem_typeClasses_mk {f : (𝓞 K)[X]} {τ : Multiset ℕ} {σ : SF f ≃ₐ[K] SF f} :
    ConjClasses.mk σ ∈ typeClasses f τ ↔ cyc f σ = τ := by
  constructor
  · rintro ⟨σ', h1, h2⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at h1
    rw [cyc_eq_of_isConj f h1.symm]
    exact h2
  · intro h
    exact ⟨σ, ConjClasses.mem_carrier_iff_mk_eq.2 rfl, h⟩

/-- The number of elements of cycle type `τ` is the sum of the sizes of the classes of type `τ`. -/
theorem card_cyc_eq_sum (f : (𝓞 K)[X]) (τ : Multiset ℕ) :
    Nat.card {σ : SF f ≃ₐ[K] SF f // cyc f σ = τ} =
      ∑ C : typeClasses f τ, Nat.card (C.1.carrier) := by
  have hmem : ∀ (C : typeClasses f τ) (σ : SF f ≃ₐ[K] SF f), σ ∈ C.1.carrier → cyc f σ = τ := by
    intro C σ hσ
    obtain ⟨σ', h1, h2⟩ := C.2
    rw [ConjClasses.mem_carrier_iff_mk_eq] at h1 hσ
    rw [← h2]
    exact cyc_eq_of_isConj f (ConjClasses.mk_eq_mk_iff_isConj.1 (hσ.trans h1.symm))
  rw [← Nat.card_sigma]
  refine Nat.card_congr
    { toFun := fun σ => ⟨⟨ConjClasses.mk σ.1, mem_typeClasses_mk.2 σ.2⟩,
        ⟨σ.1, ConjClasses.mem_carrier_iff_mk_eq.2 rfl⟩⟩
      invFun := fun p => ⟨p.2.1, hmem p.1 p.2.1 p.2.2⟩
      left_inv := fun σ => rfl
      right_inv := ?_ }
  rintro ⟨⟨C, hC⟩, σ, hσ⟩
  have : ConjClasses.mk σ = C := ConjClasses.mem_carrier_iff_mk_eq.1 hσ
  subst this
  rfl

/-- Away from finitely many primes (the ramified ones and those where `f` is not squarefree), the primes with
factorization type `τ` are exactly the primes whose Frobenius class has cycle type `τ`. -/
theorem factorizationTypeSet_symmDiff_finite (hD : DedekindFrobenius) (f : (𝓞 K)[X]) (hf : f.Monic)
    (hs : (f.map (algebraMap (𝓞 K) K)).Separable) (τ : Multiset ℕ) :
    (symmDiff (factorizationTypeSet f τ)
      (⋃ C : typeClasses f τ, frobSet K (SF f) C.1)).Finite := by
  refine ((finite_not_squarefree f hs).union (finite_compl_unramifiedPrimes K (SF f))).subset ?_
  intro 𝔭 h𝔭
  by_contra hn
  have hsq : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)) := by
    by_contra h
    exact hn (Or.inl h)
  have hun : 𝔭 ∈ unramifiedPrimes K (SF f) := by
    by_contra h
    exact hn (Or.inr h)
  obtain ⟨Q⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 (SF f))))
  have hfp : cyc f (frobAt K (SF f) 𝔭 Q) =
      (normalizedFactors (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))).map natDegree :=
    frob_partition hD f hf 𝔭 hsq Q
  have key : 𝔭 ∈ factorizationTypeSet f τ ↔ 𝔭 ∈ ⋃ C : typeClasses f τ, frobSet K (SF f) C.1 := by
    constructor
    · intro h
      rw [Set.mem_iUnion]
      refine ⟨⟨frobClass K (SF f) 𝔭, ?_⟩, hun, rfl⟩
      rw [frobClass_eq_mk_frobAt K _ 𝔭 Q, mem_typeClasses_mk, hfp]
      exact h.2
    · intro h
      obtain ⟨C, hun', hC⟩ := Set.mem_iUnion.1 h
      refine ⟨hsq, ?_⟩
      rw [← hfp]
      have := C.2
      rw [← hC, frobClass_eq_mk_frobAt K _ 𝔭 Q, mem_typeClasses_mk] at this
      exact this
  rcases Set.mem_symmDiff.1 h𝔭 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (key.1 h1)
  · exact h2 (key.2 h1)

theorem frobSet_typeClasses_pairwise_disjoint (f : (𝓞 K)[X]) (τ : Multiset ℕ) :
    Pairwise (Function.onFun Disjoint (fun C : typeClasses f τ => frobSet K (SF f) C.1)) := by
  intro C C' hne
  rw [Function.onFun, Set.disjoint_left]
  intro 𝔭 h1 h2
  exact hne (Subtype.ext (h1.2.symm.trans h2.2))

/-- **Densities of factorization types** (Milne pp. 147–148: "the Chebotarev density theorem implies"; conditional on
`DedekindFrobenius`, Dirichlet density): for $f \in \mathcal O_K[X]$ monic and separable with Galois group $G$, the
primes modulo which $f$ factors with degrees $\lambda$ have Dirichlet density
$|\{\sigma \in G : \sigma \text{ has cycle type } \lambda\}|/|G|$. -/
@[kb "milne2020ant" "v3.08, Ex. 8.36 and 8.37 (general principle), p. 148"]
theorem factorizationType_hasDirichletDensity (hD : DedekindFrobenius) (f : (𝓞 K)[X]) (hf : f.Monic)
    (hs : (f.map (algebraMap (𝓞 K) K)).Separable) (τ : Multiset ℕ) :
    (factorizationTypeSet f τ).HasDirichletDensity
      (Nat.card {σ : (f.map (algebraMap (𝓞 K) K)).Gal //
          (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts = τ} /
        Nat.card (f.map (algebraMap (𝓞 K) K)).Gal) := by
  have hU := hasDirichletDensity_finset_iUnion (K := K)
    (fun C : typeClasses f τ => frobSet K (SF f) C.1)
    (fun C => (Nat.card C.1.carrier : ℝ) / Nat.card (SF f ≃ₐ[K] SF f))
    (frobSet_typeClasses_pairwise_disjoint f τ) (fun C => thm_8_31_dirichlet K (SF f) C.1) Finset.univ
  simp only [Finset.mem_univ, Set.iUnion_true] at hU
  rw [← Finset.sum_div, ← Nat.cast_sum, ← card_cyc_eq_sum] at hU
  exact NumberFieldKB.Chebotarev.HasDirichletDensity.congr_finite hU
    (by rw [symmDiff_comm]; exact factorizationTypeSet_symmDiff_finite hD f hf hs τ)

/-- The same with natural density (conditional on `DedekindFrobenius` and `Theorem8_31`). -/
@[kb "milne2020ant" "v3.08, Ex. 8.36 and 8.37 (general principle), p. 148"]
theorem factorizationType_hasNaturalDensity (hD : DedekindFrobenius) (hC : Theorem8_31) (f : (𝓞 K)[X])
    (hf : f.Monic) (hs : (f.map (algebraMap (𝓞 K) K)).Separable) (τ : Multiset ℕ) :
    HasNaturalDensity (factorizationTypeSet f τ)
      (Nat.card {σ : (f.map (algebraMap (𝓞 K) K)).Gal //
          (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts = τ} /
        Nat.card (f.map (algebraMap (𝓞 K) K)).Gal) := by
  have hU := HasNaturalDensity.finset_iUnion (K := K)
    (fun C : typeClasses f τ => frobSet K (SF f) C.1)
    (fun C => (Nat.card C.1.carrier : ℝ) / Nat.card (SF f ≃ₐ[K] SF f))
    (frobSet_typeClasses_pairwise_disjoint f τ) (fun C => hC.natural_density K (SF f) C.1) Finset.univ
  simp only [Finset.mem_univ, Set.iUnion_true] at hU
  rw [← Finset.sum_div, ← Nat.cast_sum, ← card_cyc_eq_sum] at hU
  exact HasNaturalDensity.congr_finite hU
    (by rw [symmDiff_comm]; exact factorizationTypeSet_symmDiff_finite hD f hf hs τ)

/-- The natural density of a factorization type, once the number of elements of the Galois group of that cycle type
is known. -/
theorem hasNaturalDensity_of_count (hD : DedekindFrobenius) (hC : Theorem8_31) (f : (𝓞 K)[X])
    (hf : f.Monic) (hs : (f.map (algebraMap (𝓞 K) K)).Separable) (τ : Multiset ℕ) (c n : ℕ) (δ : ℝ)
    (hc : (Finset.univ.filter fun σ : (f.map (algebraMap (𝓞 K) K)).Gal =>
      (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts = τ).card = c)
    (hn : Nat.card (f.map (algebraMap (𝓞 K) K)).Gal = n) (h : (c : ℝ) / n = δ) :
    HasNaturalDensity (factorizationTypeSet f τ) δ := by
  have := factorizationType_hasNaturalDensity hD hC f hf hs τ
  rw [Nat.card_eq_fintype_card (α := {σ : (f.map (algebraMap (𝓞 K) K)).Gal //
    (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts = τ}), Fintype.card_subtype, hc, hn, h] at this
  exact this

/-- **Example 8.36** (conditional on `DedekindFrobenius` and `Theorem8_31`): for a monic separable cubic
$f \in \mathbb Z[X]$ (Milne: "a cubic with coefficients in $\mathbb Q$"; a rational cubic becomes monic integral after
scaling the variable, which changes finitely many reductions) with Galois group $G$:
* $G = 1$: $f$ splits modulo (density) all primes;
* $G = C_2$: $f$ splits for $1/2$ of the primes, has an irreducible factor of degree $2$ for $1/2$;
* $G = A_3$: $f$ splits for $1/3$ of the primes and stays irreducible for $2/3$;
* $G = S_3$: $f$ splits for $1/6$, has a factor of degree $2$ for $1/2$, stays irreducible for $1/3$.
Subgroups of $S_3$ are determined up to conjugacy by their order, so $G$ is identified by $|G|$. -/
@[kb "milne2020ant" "v3.08, Ex. 8.36, p. 148"]
theorem example_8_36 (hD : DedekindFrobenius) (hC : Theorem8_31) (f : (𝓞 ℚ)[X]) (hf : f.Monic)
    (h3 : f.natDegree = 3) (hs : (f.map (algebraMap (𝓞 ℚ) ℚ)).Separable) :
    let G := (f.map (algebraMap (𝓞 ℚ) ℚ)).Gal
    (Nat.card G = 1 → HasNaturalDensity (factorizationTypeSet f {1, 1, 1}) 1) ∧
    (Nat.card G = 2 → HasNaturalDensity (factorizationTypeSet f {1, 1, 1}) (1 / 2) ∧
      HasNaturalDensity (factorizationTypeSet f {2, 1}) (1 / 2)) ∧
    (Nat.card G = 3 → HasNaturalDensity (factorizationTypeSet f {1, 1, 1}) (1 / 3) ∧
      HasNaturalDensity (factorizationTypeSet f {3}) (2 / 3)) ∧
    (Nat.card G = 6 → HasNaturalDensity (factorizationTypeSet f {1, 1, 1}) (1 / 6) ∧
      HasNaturalDensity (factorizationTypeSet f {2, 1}) (1 / 2) ∧
      HasNaturalDensity (factorizationTypeSet f {3}) (1 / 3)) := by
  dsimp only
  have hdeg : (f.map (algebraMap (𝓞 ℚ) ℚ)).natDegree = 3 := by
    rw [natDegree_map_eq_of_injective (IsFractionRing.injective (𝓞 ℚ) ℚ)]
    exact h3
  set g := f.map (algebraMap (𝓞 ℚ) ℚ) with hg
  have hcard : Fintype.card (g.rootSet g.SplittingField) = 3 :=
    (card_rootSet_splittingField g hs).trans hdeg
  have hφ := galPerm_injective g
  have key := hasNaturalDensity_of_count hD hC f hf hs
  have hN : ∀ n : ℕ, Nat.card g.Gal = n → Fintype.card g.Gal = n := fun n h => by
    rwa [← Nat.card_eq_fintype_card]
  refine ⟨fun h1 => key _ 1 1 1 (count3_triv _ hφ hcard) h1 (by norm_num), fun h2 => ?_, fun h3 => ?_,
    fun h6 => ?_⟩
  · exact ⟨key _ 1 2 _ (count3_triv _ hφ hcard) h2 (by norm_num),
      key _ 1 2 _ (count3_two _ hφ hcard (hN 2 h2)) h2 (by norm_num)⟩
  · exact ⟨key _ 1 3 _ (count3_triv _ hφ hcard) h3 (by norm_num),
      key _ 2 3 _ (count3_three _ hφ hcard (hN 3 h3)) h3 (by norm_num)⟩
  · exact ⟨key _ 1 6 _ (count3_triv _ hφ hcard) h6 (by norm_num),
      key {2, 1} 3 6 _ ((count3_six _ hφ hcard (hN 6 h6) {2, 1}).trans (by decide)) h6 (by norm_num),
      key {3} 2 6 _ ((count3_six _ hφ hcard (hN 6 h6) {3}).trans (by decide)) h6 (by norm_num)⟩

/-- **Example 8.37, the $D_8$ case** (conditional on `DedekindFrobenius` and `Theorem8_31`): if a monic quartic
$f \in \mathbb Z[X]$ has Galois group $D_8$ (a subgroup of order $8$ of $S_4$), then $f$ splits modulo $p$ for $1/8$
of the primes, is a quadratic times two linear factors for $1/4$, a product of two quadratics for $3/8$, and stays
irreducible for $1/4$. (The tables of Example 8.37 are the cycle-type counts used in the proof; the
book's table (b) has a gap.) -/
@[kb "milne2020ant" "v3.08, Ex. 8.37, p. 148"]
theorem example_8_37_D8 (hD : DedekindFrobenius) (hC : Theorem8_31) (f : (𝓞 ℚ)[X]) (hf : f.Monic)
    (h4 : f.natDegree = 4) (hs : (f.map (algebraMap (𝓞 ℚ) ℚ)).Separable)
    (hG : Nat.card (f.map (algebraMap (𝓞 ℚ) ℚ)).Gal = 8) :
    HasNaturalDensity (factorizationTypeSet f {1, 1, 1, 1}) (1 / 8) ∧
      HasNaturalDensity (factorizationTypeSet f {2, 1, 1}) (1 / 4) ∧
      HasNaturalDensity (factorizationTypeSet f {2, 2}) (3 / 8) ∧
      HasNaturalDensity (factorizationTypeSet f {4}) (1 / 4) := by
  have hdeg : (f.map (algebraMap (𝓞 ℚ) ℚ)).natDegree = 4 := by
    rw [natDegree_map_eq_of_injective (IsFractionRing.injective (𝓞 ℚ) ℚ)]
    exact h4
  set g := f.map (algebraMap (𝓞 ℚ) ℚ) with hg
  have hcard : Fintype.card (g.rootSet g.SplittingField) = 4 :=
    (card_rootSet_splittingField g hs).trans hdeg
  have hφ := galPerm_injective g
  have key := hasNaturalDensity_of_count hD hC f hf hs
  have hN : Fintype.card g.Gal = 8 := by
    rwa [← Nat.card_eq_fintype_card]
  exact ⟨key _ 1 8 _ ((count4_D8 _ hφ hcard hN _).trans D4_count_one) hG (by norm_num),
    key _ 2 8 _ ((count4_D8 _ hφ hcard hN _).trans D4_count_two_one_one) hG (by norm_num),
    key _ 3 8 _ ((count4_D8 _ hφ hcard hN _).trans D4_count_two_two) hG (by norm_num),
    key _ 2 8 _ ((count4_D8 _ hφ hcard hN _).trans D4_count_four) hG (by norm_num)⟩

end FactorizationTypes

/-! ## Remark 8.40 (b)–(e) -/

section Remark840

/-- **Remark 8.40(c)** (named statement): Corollary 8.39 fails without the Galois hypothesis: there are
non-isomorphic extensions $L, M$ of $\mathbb Q$ of the same degree with the same discriminant and with every prime
not dividing the discriminant decomposing the same way in both (in particular $\mathrm{Spl}(L/\mathbb Q) =
\mathrm{Spl}(M/\mathbb Q)$). "Decomposing the same way" is recorded as: for every pair $(e, f)$, the same number of
primes above $p$ have ramification index $e$ and residue degree $f$. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(c), p. 150"]
structure Remark8_40c : Prop where
  exists_pair : ∃ (L M : Type) (_ : Field L) (_ : NumberField L) (_ : Field M) (_ : NumberField M),
    IsEmpty (L ≃+* M) ∧ Module.finrank ℚ L = Module.finrank ℚ M ∧ discr L = discr M ∧
    ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ discr L → ∀ e f : ℕ,
      {P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 L) | P.ramificationIdx ℤ = e ∧ P.inertiaDeg ℤ = f}.ncard =
        {P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 M) | P.ramificationIdx ℤ = e ∧ P.inertiaDeg ℤ = f}.ncard

/-- If `f` modulo `𝔭` is squarefree and splits into linear factors, a Frobenius element at any prime above `𝔭`
acts trivially on the roots, hence is the identity. -/
theorem frobAt_eq_one_of_splits (hD : DedekindFrobenius) {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X])
    (hf : f.Monic) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hsq : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)))
    (hspl : (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)).Splits)
    (Q : 𝔭.asIdeal.primesOver (𝓞 (SF f))) : frobAt K (SF f) 𝔭 Q = 1 := by
  have hp := frob_partition hD f hf 𝔭 hsq Q
  have hne : f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField) ≠ 0 := (hf.map _).ne_zero
  have h1 : ∀ a ∈ (galPerm (f.map (algebraMap (𝓞 K) K)) (frobAt K (SF f) 𝔭 Q)).partition.parts, a = 1 := by
    intro a ha
    rw [hp, Multiset.mem_map] at ha
    obtain ⟨q, hq, rfl⟩ := ha
    exact (Splits.of_dvd hspl hne (dvd_of_mem_normalizedFactors hq)).natDegree_eq_one_of_irreducible
      (irreducible_of_normalized_factor q hq)
  have h2 : (galPerm (f.map (algebraMap (𝓞 K) K)) (frobAt K (SF f) 𝔭 Q)).cycleType = 0 := by
    rw [← Equiv.Perm.filter_parts_partition_eq_cycleType]
    exact Multiset.filter_eq_nil.2 (fun a ha => by rw [h1 a ha]; decide)
  have h3 := Equiv.Perm.cycleType_eq_zero.1 h2
  exact galPerm_injective (f.map (algebraMap (𝓞 K) K))
    (h3.trans (map_one (MulAction.toPermHom (f.map (algebraMap (𝓞 K) K)).Gal
      ((f.map (algebraMap (𝓞 K) K)).rootSet (f.map (algebraMap (𝓞 K) K)).SplittingField))).symm)

/-- **Remark 8.40(d)**, first claim (conditional on `DedekindFrobenius`): if a monic $f \in \mathcal O_K[X]$,
separable over $K$, splits into linear factors modulo $\mathfrak p$ for all but finitely many primes $\mathfrak p$, then
$f$ splits into linear factors over $K$. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(d), p. 150"]
theorem remark_8_40d (hD : DedekindFrobenius) {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X])
    (hf : f.Monic) (hs : (f.map (algebraMap (𝓞 K) K)).Separable)
    (h : {𝔭 : HeightOneSpectrum (𝓞 K) |
      ¬ (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)).Splits}.Finite) :
    (f.map (algebraMap (𝓞 K) K)).Splits := by
  set g := f.map (algebraMap (𝓞 K) K) with hg
  have hsub : (splitPrimes K (SF f))ᶜ ⊆ ({𝔭 : HeightOneSpectrum (𝓞 K) |
        ¬ Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))} ∪
      {𝔭 : HeightOneSpectrum (𝓞 K) | ¬ (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)).Splits}) ∪
      (unramifiedPrimes K (SF f))ᶜ := by
    intro 𝔭 h𝔭
    by_contra hn
    have hsq : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)) := by
      by_contra h
      exact hn (Or.inl (Or.inl h))
    have hspl : (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)).Splits := by
      by_contra h
      exact hn (Or.inl (Or.inr h))
    have hun : 𝔭 ∈ unramifiedPrimes K (SF f) := by
      by_contra h
      exact hn (Or.inr h)
    obtain ⟨Q⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 (SF f))))
    apply h𝔭
    rw [splitPrimes_eq_frobSet_one]
    refine ⟨hun, ?_⟩
    rw [frobClass_eq_mk_frobAt K _ 𝔭 Q, frobAt_eq_one_of_splits hD f hf 𝔭 hsq hspl Q]
  have hfin : (splitPrimes K (SF f))ᶜ.Finite :=
    (((finite_not_squarefree f hs).union h).union (finite_compl_unramifiedPrimes K (SF f))).subset hsub
  have h1 : (splitPrimes K (SF f)).HasDirichletDensity 1 := by
    refine NumberFieldKB.Chebotarev.HasDirichletDensity.congr_finite
      (hasDirichletDensity_univ (F := K)) ?_
    have : symmDiff (Set.univ : Set (HeightOneSpectrum (𝓞 K))) (splitPrimes K (SF f)) =
        (splitPrimes K (SF f))ᶜ := by
      ext x
      simp [Set.mem_symmDiff]
    rw [this]
    exact hfin
  have h2 := cor_8_32_dirichlet K (SF f)
  have h3 : (1 : ℝ) = 1 / (Module.finrank K (SF f) : ℝ) :=
    NumberFieldKB.Chebotarev.HasDirichletDensity.unique h1 h2
  have hpos : (0 : ℝ) < Module.finrank K (SF f) := by exact_mod_cast Module.finrank_pos
  have h4 : Module.finrank K (SF f) = 1 := by
    have : (Module.finrank K (SF f) : ℝ) = 1 := by
      field_simp at h3
      linarith
    exact_mod_cast this
  have hbot := Subalgebra.bot_eq_top_of_finrank_eq_one h4
  have hbij : Function.Bijective (algebraMap K (SF f)) := by
    refine ⟨(algebraMap K (SF f)).injective, fun y => ?_⟩
    have : y ∈ (⊤ : Subalgebra K (SF f)) := Algebra.mem_top
    rw [← hbot, Algebra.mem_bot] at this
    exact this
  let e : K ≃+* SF f := RingEquiv.ofBijective (algebraMap K (SF f)) hbij
  have h5 := (SplittingField.splits g).map e.symm.toRingHom
  rwa [Polynomial.map_map, show e.symm.toRingHom.comp (algebraMap K (SF f)) = RingHom.id K from by
    ext x; exact e.symm_apply_apply x, Polynomial.map_id] at h5

/-- **Remark 8.40(d)**, second claim (named statement): an irreducible polynomial $f \in K[X]$ of degree $> 1$ over a
number field cannot have a root modulo $\mathfrak p$ for all but finitely many $\mathfrak p$. Stated for monic
$f \in \mathcal O_K[X]$. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(d), p. 150"]
structure Remark8_40d : Prop where
  not_root_cofinite : ∀ (K : Type) [Field K] [NumberField K] (f : (𝓞 K)[X]) (_ : f.Monic)
    (_ : Irreducible (f.map (algebraMap (𝓞 K) K))) (_ : 1 < f.natDegree),
    ¬ {𝔭 : HeightOneSpectrum (𝓞 K) |
      ∀ x : 𝔭.asIdeal.ResidueField, (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)).eval x ≠ 0}.Finite

/-- **Remark 8.40(d)**, the counterexample (proved): $(X^2-2)(X^2-3)(X^2-6)$ is reducible and has a root modulo every
prime $p$ (one of $2, 3, 6$ is a square modulo $p$). -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(d), p. 150"]
theorem remark_8_40d_example (p : ℕ) [Fact p.Prime] :
    ∃ x : ZMod p, ((X ^ 2 - 2) * (X ^ 2 - 3) * (X ^ 2 - 6) : (ZMod p)[X]).eval x = 0 := by
  by_cases h2 : (2 : ZMod p) = 0
  · exact ⟨0, by simp [h2]⟩
  by_cases h3 : (3 : ZMod p) = 0
  · exact ⟨0, by simp [h3]⟩
  by_cases hs2 : IsSquare (2 : ZMod p)
  · obtain ⟨x, hx⟩ := hs2
    have : x ^ 2 = 2 := by rw [sq, ← hx]
    exact ⟨x, by simp [this]⟩
  by_cases hs3 : IsSquare (3 : ZMod p)
  · obtain ⟨x, hx⟩ := hs3
    have : x ^ 2 = 3 := by rw [sq, ← hx]
    exact ⟨x, by simp [this]⟩
  have h6 : IsSquare ((2 : ZMod p) * 3) := by
    rw [← quadraticChar_one_iff_isSquare (mul_ne_zero h2 h3), map_mul,
      quadraticChar_neg_one_iff_not_isSquare.2 hs2, quadraticChar_neg_one_iff_not_isSquare.2 hs3]
    norm_num
  obtain ⟨x, hx⟩ := h6
  refine ⟨x, ?_⟩
  have : x ^ 2 = 6 := by rw [sq, ← hx]; norm_num
  simp [this]

/-- **Remark 8.40(e)** (named statement): there are polynomials $f \in \mathbb Q[X]$ irreducible over $\mathbb Q$ but
reducible over $\mathbb Q_p$ for every prime $p$ and over $\mathbb R$. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(e), p. 150"]
structure Remark8_40e : Prop where
  exists_poly : ∃ f : ℚ[X], Irreducible f ∧ (∀ p : ℕ, (hp : p.Prime) →
      haveI := Fact.mk hp; ¬ Irreducible (f.map (algebraMap ℚ ℚ_[p]))) ∧
    ¬ Irreducible (f.map (algebraMap ℚ ℝ))

end Remark840

end

end NumberFieldKB.MilneANT
