import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Unramified

/-!
# Milne, *Class Field Theory*, Chapter III §5: the existence theorem

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

* `isNormGroup_iff_ch3` — the definition of norm groups (p. 115) is Chapter I's `IsNormGroup`.
* `theorem_5_1` — Theorem 5.1, from Chapter I's named statement `LocalExistenceInput` (Chapter I, Theorem 1.4,
  the same theorem).
* `step_5` — Step 5 of Milne's proof: every subgroup of finite index of $K^\times$ containing $U_K$ is a norm group
  (the norm group of the unramified extension of the corresponding degree), proved from Proposition 1.2 and display
  (26) (named statements of §1) and Chapter I's `UnramifiedInput`.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Norm groups** (Milne, p. 115, definition in prose): a subgroup $N$ of $K^\times$ is a norm group if there is a
finite abelian extension $L/K$ with $\mathrm{Nm}_{L/K}(L^\times) = N$. This is Chapter I's `IsNormGroup`. -/
@[kb "milne2020cft" "v4.03, Ch. III, §5, definition of norm groups, p. 115"]
theorem isNormGroup_iff_ch3 (N : Subgroup Kˣ) :
    IsNormGroup K Ω N ↔ ∃ L : FiniteAbelianExt K Ω, normGroup L.toField = N := Iff.rfl

/-- **Theorem 5.1, existence theorem** (p. 115). Every open subgroup of finite index in $K^\times$ is a norm group.
Derived from Chapter I's named statement `LocalExistenceInput` (Chapter I, Theorem 1.4, the same theorem). Milne
proves it (for $K$ of characteristic zero) from Proposition 4.1 by Steps 1–5; Step 5 is `step_5`. -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 5.1, p. 115"]
theorem theorem_5_1 (h : LocalExistenceInput K Ω) (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfi : H.FiniteIndex) : IsNormGroup K Ω H :=
  h.isNormGroup H hopen hfi

/-- The additive subgroup of exponents `k` with `p^k ∈ I`. -/
def expSubgroup (I : Subgroup Kˣ) (p : Kˣ) : AddSubgroup ℤ where
  carrier := {k | p ^ k ∈ I}
  zero_mem' := by simp
  add_mem' := fun {a b} (ha : p ^ a ∈ I) (hb : p ^ b ∈ I) => by
    show p ^ (a + b) ∈ I
    rw [zpow_add]; exact I.mul_mem ha hb
  neg_mem' := fun {a} (ha : p ^ a ∈ I) => by
    show p ^ (-a) ∈ I
    rw [zpow_neg]; exact I.inv_mem ha

/-- There is `e > 0` with `p^k ∈ I ↔ e ∣ k`. -/
theorem exists_exp_gen (I : Subgroup Kˣ) [I.FiniteIndex] (p : Kˣ) :
    ∃ e : ℕ, 0 < e ∧ ∀ k : ℤ, p ^ k ∈ I ↔ (e : ℤ) ∣ k := by
  obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic (expSubgroup I p)).exists_generator
  set a : ℤ := g.1 with ha_def
  have hdvd : ∀ k : ℤ, p ^ k ∈ I ↔ a ∣ k := by
    intro k
    constructor
    · intro hk
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (hg ⟨k, hk⟩)
      have := congrArg Subtype.val hn
      exact ⟨n, by simpa [mul_comm] using this.symm⟩
    · rintro ⟨c, rfl⟩
      have : c • a ∈ expSubgroup I p := (expSubgroup I p).zsmul_mem g.2 c
      have h2 : c • a = a * c := by simp [mul_comm]
      rw [h2] at this
      exact this
  refine ⟨a.natAbs, ?_, fun k => by rw [hdvd]; exact (Int.natAbs_dvd.symm)⟩
  rcases Nat.eq_zero_or_pos a.natAbs with h | h
  · have ha0 : a = 0 := Int.natAbs_eq_zero.1 h
    have := (hdvd (I.index : ℤ)).1 (by simpa using I.pow_index_mem p)
    have hi : (I.index : ℤ) ≠ 0 := by exact_mod_cast Subgroup.FiniteIndex.index_ne_zero (H := I)
    rw [ha0] at this
    exact absurd (zero_dvd_iff.1 this) hi
  · exact h

/-- **Step 5** of the proof of Theorem 5.1 (p. 116): every subgroup $I$ of finite index of $K^\times$ that contains
$U_K$ is a norm group: it is the norm group of the unramified extension of degree $e$, where $\pi^{e\mathbb Z} =
\pi^{\mathbb Z} \cap I$. -/
@[kb "milne2020cft" "v4.03, Ch. III, §5, proof of Thm. 5.1, Step 5, p. 116"]
theorem step_5 (h26 : UnitPrimeDecomposition K Ω) (hU : UnramifiedInput K Ω)
    (I : Subgroup Kˣ) [I.FiniteIndex] (hI : unitGroup K ≤ I) : IsNormGroup K Ω I := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨e, he, hk⟩ := exists_exp_gen I (primeUnit hπ)
  obtain ⟨L, hLu, hLd⟩ := hU.exists_unramified e he
  refine ⟨L, ?_⟩
  have hnorm : ∀ m : ℤ, normUnits L.toField (embUnits L.toField (primeUnit hπ) ^ m)
      = primeUnit hπ ^ ((e : ℤ) * m) := by
    intro m
    rw [map_zpow, zpow_mul, zpow_natCast]
    congr 1
    apply Units.ext
    simp [Algebra.norm_algebraMap, hLd]
  rw [← normUnits_range]
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨v, hv, m, rfl⟩ := h26.decomp L.toField hLu hπ y
    rw [map_mul, hnorm]
    refine I.mul_mem (hI (normUnits_mem_unitGroup _ hv)) ((hk _).2 ⟨m, rfl⟩)
  · intro x hx
    obtain ⟨u, hu, k, rfl⟩ := exists_unit_zpow π hπ x
    have hpk : primeUnit hπ ^ k ∈ I := by
      have := I.mul_mem (I.inv_mem (hI hu)) hx
      simpa using this
    obtain ⟨j, hj⟩ := (hk k).1 hpk
    obtain ⟨v, hv, hvu⟩ := prop1_2.surj L.toField hLu u hu
    refine ⟨v * embUnits L.toField (primeUnit hπ) ^ j, ?_⟩
    rw [map_mul, hnorm, hvu, hj]

end NumberFieldKB.MilneCFT.Ch3
