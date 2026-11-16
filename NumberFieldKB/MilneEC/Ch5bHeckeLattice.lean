import Mathlib.GroupTheory.IndexNSmul
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Finset.NatDivisors
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter V, Section 4: Hecke operators on lattices

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, subsection "Definition of the Hecke operators"
(pdf pp. 208–210).

* `LatticeC`: Milne's set $\mathcal L$ of lattices in $\mathbb C$ (the $\mathbb Z$-span of an $\mathbb R$-basis of
  $\mathbb C$; Mathlib's `PeriodPair.lattice`).
* `LatDiv`: the free abelian group $\mathcal D$ on $\mathcal L$.
* `heckeT n`, `heckeR n`: Milne's $T(n)[\Lambda] = \sum_{(\Lambda : \Lambda') = n} [\Lambda']$ and
  $R(n)[\Lambda] = [n\Lambda]$.
* Proposition 4.11 (`prop_4_11_a`, `prop_4_11_b`), Corollary 4.12 (`cor_4_12`), Corollary 4.13 (`cor_4_13`).
* Functions on lattices: the linear extension $F : \mathcal D \to \mathbb C$ (`latFnExt`), the action
  $T \cdot F$ (`heckeActFn`), homogeneity of weight $-2k$ (`IsHomogeneousLat`), $R(n) \cdot F = n^{-2k} F$
  (`heckeR_act_of_homogeneous`) and Proposition 4.14 (`prop_4_14`, `prop_4_14_a`, `prop_4_14_b`).

Milne defines $T(n)$ and $R(n)$ for $n \ge 1$; here `heckeT 0 = 0` and `heckeR 0 = 0` (there is no sublattice of
infinite index in a lattice), and the statements carry $n \ge 1$ as Milne's do.
-/

open scoped Pointwise

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

/-- **Lattices in $\mathbb C$** (Milne, *EC*, V.4, p. 208, the set $\mathcal L$; I, Section 3): a subgroup of
$\mathbb C$ of the form $\mathbb Z\omega_1 + \mathbb Z\omega_2$ with $\omega_1, \omega_2$ linearly independent over
$\mathbb R$, i.e. the lattice of a Mathlib `PeriodPair`. -/
def IsLatticeC (Λ : Submodule ℤ ℂ) : Prop :=
  ∃ L : PeriodPair, L.lattice = Λ

/-- The set $\mathcal L$ of lattices in $\mathbb C$ (Milne, *EC*, V.4, p. 208). -/
abbrev LatticeC : Type := {Λ : Submodule ℤ ℂ // IsLatticeC Λ}

/-- The index $(\Lambda : \Lambda')$ of a subgroup $\Lambda'$ in $\Lambda$ (the relative index of the underlying
additive subgroups; $0$ if infinite). -/
def latIndex (Λ' Λ : Submodule ℤ ℂ) : ℕ :=
  Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup

/-- The lattices $\Lambda' \subset \Lambda$ with $(\Lambda : \Lambda') = n$. -/
def sublatticesOfIndex (n : ℕ) (Λ : LatticeC) : Set LatticeC :=
  {Λ' | Λ'.1 ≤ Λ.1 ∧ latIndex Λ'.1 Λ.1 = n}

/-- A lattice has rank two. -/
theorem IsLatticeC.finrank_eq {Λ : Submodule ℤ ℂ} (h : IsLatticeC Λ) : Module.finrank ℤ Λ = 2 := by
  obtain ⟨L, rfl⟩ := h; exact L.finrank_lattice

/-- A lattice is a free $\mathbb Z$-module. -/
theorem IsLatticeC.free {Λ : Submodule ℤ ℂ} (h : IsLatticeC Λ) : Module.Free ℤ Λ := by
  obtain ⟨L, rfl⟩ := h; exact Module.Free.of_basis L.latticeBasis

/-- A lattice is a finitely generated $\mathbb Z$-module. -/
theorem IsLatticeC.finite {Λ : Submodule ℤ ℂ} (h : IsLatticeC Λ) : Module.Finite ℤ Λ := by
  obtain ⟨L, rfl⟩ := h; exact Module.Finite.of_basis L.latticeBasis

/-- A sublattice of a lattice has finite index. -/
theorem latIndex_ne_zero {A Λ : Submodule ℤ ℂ} (hA : IsLatticeC A) (hΛ : IsLatticeC Λ) (h : A ≤ Λ) :
    latIndex A Λ ≠ 0 := by
  have := hΛ.free
  have := hΛ.finite
  have hfin : Finite (Λ ⧸ A.comap Λ.subtype) := by
    apply Submodule.finiteQuotientOfFreeOfRankEq
    rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq, hA.finrank_eq, hΛ.finrank_eq]
  unfold latIndex AddSubgroup.relIndex
  have : Finite (Λ ⧸ (A.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup)) := hfin
  exact AddSubgroup.index_ne_zero_of_finite
/-- An element of a subgroup is killed by the relative index. -/
theorem latIndex_nsmul_mem {A Λ : Submodule ℤ ℂ} {x : ℂ} (hx : x ∈ Λ) :
    latIndex A Λ • x ∈ A := by
  have := AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := Λ.toAddSubgroup) hx
  exact this

/-- A subgroup of finite index in a lattice is a lattice. -/
theorem isLatticeC_of_latIndex_ne_zero {A Λ : Submodule ℤ ℂ} (hΛ : IsLatticeC Λ) (h : A ≤ Λ)
    (hi : latIndex A Λ ≠ 0) : IsLatticeC A := by
  obtain ⟨L, rfl⟩ := hΛ
  -- A is discrete
  have hdisc : DiscreteTopology A := by
    refine DiscreteTopology.of_continuous_injective (f := Submodule.inclusion h) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val) _
    · exact Submodule.inclusion_injective h
  have hspan : Submodule.span ℝ (A : Set ℂ) = ⊤ := by
    rw [eq_top_iff]
    have h1 : Submodule.span ℝ (L.lattice : Set ℂ) = ⊤ := IsZLattice.span_top (K := ℝ) (L := L.lattice)
    rw [← h1]
    apply Submodule.span_le.2
    intro x hx
    have hmem : latIndex A L.lattice • x ∈ A := latIndex_nsmul_mem hx
    have hne : ((latIndex A L.lattice : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hi
    have : x = ((latIndex A L.lattice : ℕ) : ℝ)⁻¹ • ((latIndex A L.lattice) • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hZ : IsZLattice ℝ A := ⟨hspan⟩
  have hrank : Module.finrank ℤ A = 2 := by
    rw [ZLattice.rank ℝ A]; simp
  have hfin : Module.Finite ℤ A := ZLattice.module_finite ℝ A
  have hfree : Module.Free ℤ A := ZLattice.module_free ℝ A
  let b0 : Module.Basis (Fin 2) ℤ A := Module.finBasisOfFinrankEq ℤ A hrank
  let B := b0.ofZLatticeBasis ℝ A
  refine ⟨⟨b0 0, b0 1, ?_⟩, ?_⟩
  · convert B.linearIndependent using 1
    ext i
    fin_cases i <;> simp [B]
  · have hs : (Submodule.span ℤ (Set.range b0)).map A.subtype = A := by
      rw [b0.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span] at hs
    refine Eq.trans ?_ hs
    unfold PeriodPair.lattice
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨_, ⟨0, rfl⟩, rfl⟩
      · exact ⟨_, ⟨1, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
/-- A lattice has only finitely many sublattices of a given index (for $n \ge 1$ they all contain $n\Lambda$, and
$\Lambda / n\Lambda$ is finite; for $n = 0$ there are none). -/
theorem sublatticesOfIndex_finite (n : ℕ) (Λ : LatticeC) : (sublatticesOfIndex n Λ).Finite := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · convert Set.finite_empty
    ext Λ'
    simp only [sublatticesOfIndex, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h
    exact latIndex_ne_zero Λ'.2 Λ.2 h
  · have := Λ.2.free
    have := Λ.2.finite
    let N := (nsmulAddMonoidHom (α := Λ.1) n).range
    have hN : N.index ≠ 0 := by
      have h := AddSubgroup.index_range_nsmul Λ.1 n
      rw [show N.index = _ from h]
      exact pow_ne_zero _ hn.ne'
    have : N.FiniteIndex := ⟨hN⟩
    let f : LatticeC → Set (Λ.1 ⧸ N) := fun B =>
      {q | ∃ x : Λ.1, (QuotientAddGroup.mk x : Λ.1 ⧸ N) = q ∧ (x : ℂ) ∈ B.1}
    have key : ∀ B1 ∈ sublatticesOfIndex n Λ, ∀ B2 ∈ sublatticesOfIndex n Λ,
        f B1 ⊆ f B2 → B1.1 ≤ B2.1 := by
      intro B1 h1 B2 h2 hsub y hy
      have hyΛ : y ∈ Λ.1 := h1.1 hy
      obtain ⟨x, hx, hxB⟩ := hsub ⟨⟨y, hyΛ⟩, rfl, hy⟩
      rw [QuotientAddGroup.eq] at hx
      obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1 hx
      have hz' : (n • (z : ℂ)) = -(x : ℂ) + y := by
        have := congrArg (fun w : Λ.1 => (w : ℂ)) hz
        simpa using this
      have hmem : n • (z : ℂ) ∈ B2.1 := by
        have := latIndex_nsmul_mem (A := B2.1) z.2
        rwa [h2.2] at this
      have : y = (x : ℂ) + n • (z : ℂ) := by rw [hz']; ring
      rw [this]
      exact add_mem hxB hmem
    refine Set.Finite.of_injOn (f := f) (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_
      (Set.toFinite _)
    intro B1 h1 B2 h2 heq
    exact Subtype.ext (le_antisymm (key B1 h1 B2 h2 heq.le) (key B2 h2 B1 h1 heq.ge))

/-- The scaling $c\Lambda$ of a lattice by $c \in \mathbb C^\times$ is a lattice. -/
theorem isLatticeC_smul (c : ℂˣ) {Λ : Submodule ℤ ℂ} (hΛ : IsLatticeC Λ) : IsLatticeC ((c : ℂ) • Λ) := by
  obtain ⟨L, rfl⟩ := hΛ
  have hc : (c : ℂ) ≠ 0 := c.ne_zero
  have hker : LinearMap.ker (LinearMap.mulLeft ℝ (c : ℂ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    exact mul_left_cancel₀ hc hab
  refine ⟨⟨c * L.ω₁, c * L.ω₂, ?_⟩, ?_⟩
  · have := L.indep.map' (LinearMap.mulLeft ℝ (c : ℂ)) hker
    convert this using 1
    ext i
    fin_cases i <;> simp
  · simp only [PeriodPair.lattice, Submodule.smul_span, Set.smul_set_insert,
      Set.smul_set_singleton, smul_eq_mul]

/-- Membership in a scaled subgroup. -/
theorem mem_smul_latticeSub {c : ℂ} {A : Submodule ℤ ℂ} {x : ℂ} :
    x ∈ c • A ↔ ∃ y ∈ A, c * y = x := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp [smul_eq_mul]

/-- Scaling by a nonzero complex number preserves relative indices. -/
theorem latIndex_smul {c : ℂ} (hc : c ≠ 0) (A B : Submodule ℤ ℂ) :
    latIndex (c • A) (c • B) = latIndex A B := by
  let f : ℂ →+ ℂ := AddMonoidHom.mulLeft c
  have hf : Function.Injective f := fun a b h => mul_left_cancel₀ hc h
  have hmap : ∀ C : Submodule ℤ ℂ, (c • C).toAddSubgroup = C.toAddSubgroup.map f := by
    intro C
    ext x
    rw [AddSubgroup.mem_map]
    exact mem_smul_latticeSub
  unfold latIndex
  rw [hmap, hmap]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hf

/-- $\mathbb C^\times$ acts on $\mathcal L$ by scaling, $\Lambda \mapsto c\Lambda$. -/
instance : SMul ℂˣ LatticeC where
  smul c Λ := ⟨(c : ℂ) • Λ.1, isLatticeC_smul c Λ.2⟩

@[simp] theorem LatticeC.coe_smul (c : ℂˣ) (Λ : LatticeC) : ((c • Λ : LatticeC) : Submodule ℤ ℂ) = (c : ℂ) • Λ.1 :=
  rfl

/-- **The free abelian group $\mathcal D$ on $\mathcal L$** (Milne, *EC*, V.4, p. 208): an element is a finite sum
$\sum n_\Lambda [\Lambda]$, $n_\Lambda \in \mathbb Z$. -/
abbrev LatDiv : Type := LatticeC →₀ ℤ

/-- **The Hecke operator $T(n)$ on $\mathcal D$** (Milne, *EC*, V.4, p. 208):
$T(n)[\Lambda] = \sum_{(\Lambda : \Lambda') = n} [\Lambda']$, extended linearly. -/
def heckeT (n : ℕ) : LatDiv →ₗ[ℤ] LatDiv :=
  Finsupp.linearCombination ℤ fun Λ =>
    ∑ Λ' ∈ (sublatticesOfIndex_finite n Λ).toFinset, Finsupp.single Λ' (1 : ℤ)

/-- **The operator $R(n)$ on $\mathcal D$** (Milne, *EC*, V.4, p. 208): $R(n)[\Lambda] = [n\Lambda]$ for
$n \ge 1$ (and $R(0) = 0$). -/
def heckeR (n : ℕ) : LatDiv →ₗ[ℤ] LatDiv :=
  if h : n = 0 then 0 else
    Finsupp.lmapDomain ℤ ℤ fun Λ => Units.mk0 (n : ℂ) (Nat.cast_ne_zero.mpr h) • Λ

theorem heckeT_single (n : ℕ) (Λ : LatticeC) :
    heckeT n (Finsupp.single Λ 1) =
      ∑ Λ' ∈ (sublatticesOfIndex_finite n Λ).toFinset, Finsupp.single Λ' (1 : ℤ) := by
  simp [heckeT]

theorem mem_sublatticesOfIndex {n : ℕ} {Λ Λ' : LatticeC} :
    Λ' ∈ sublatticesOfIndex n Λ ↔ Λ'.1 ≤ Λ.1 ∧ latIndex Λ'.1 Λ.1 = n := Iff.rfl

open Classical in
/-- The coefficient of $[\Lambda_0]$ in $T(n)[\Lambda]$. -/
theorem heckeT_single_apply (n : ℕ) (Λ Λ0 : LatticeC) :
    (heckeT n (Finsupp.single Λ 1)) Λ0 = if Λ0 ∈ sublatticesOfIndex n Λ then 1 else 0 := by
  classical
  rw [heckeT_single, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp

open Classical in
/-- The coefficient of $[\Lambda_0]$ in $T(m)(T(n)[\Lambda])$ counts the intermediate lattices. -/
theorem heckeT_comp_single_apply (m n : ℕ) (Λ Λ0 : LatticeC) :
    ((heckeT m ∘ₗ heckeT n) (Finsupp.single Λ 1)) Λ0 =
      (((sublatticesOfIndex_finite n Λ).toFinset.filter
        (fun Λ' => Λ0 ∈ sublatticesOfIndex m Λ')).card : ℤ) := by
  rw [LinearMap.comp_apply, heckeT_single, map_sum, Finsupp.finsetSum_apply]
  simp only [heckeT_single_apply]
  rw [Finset.sum_boole]

/-- The relative indices multiply along a chain. -/
theorem latIndex_mul {A B C : Submodule ℤ ℂ} (hAB : A ≤ B) (hBC : B ≤ C) :
    latIndex A B * latIndex B C = latIndex A C :=
  AddSubgroup.relIndex_mul_relIndex (H := A.toAddSubgroup) (K := B.toAddSubgroup)
    (L := C.toAddSubgroup) hAB hBC

theorem latIndex_eq_one {A B : Submodule ℤ ℂ} : latIndex A B = 1 ↔ B ≤ A :=
  AddSubgroup.relIndex_eq_one

/-- Two nested subgroups of a common subgroup with the same finite index are equal. -/
theorem eq_of_latIndex_eq {A B C : Submodule ℤ ℂ} (hAB : A ≤ B) (hBC : B ≤ C)
    (h : latIndex A C = latIndex B C) (h0 : latIndex B C ≠ 0) : A = B := by
  have h1 := latIndex_mul hAB hBC
  have h2 : latIndex A B * latIndex B C = 1 * latIndex B C := by rw [one_mul, h1, h]
  have : latIndex A B = 1 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h0) h2
  exact le_antisymm hAB (latIndex_eq_one.1 this)

/-- A prime dividing the index of $A$ in $B$ divides every exponent killing $B / A$ (Cauchy). -/
theorem prime_dvd_of_dvd_latIndex {A B : Submodule ℤ ℂ} (hi : latIndex A B ≠ 0) {e : ℕ}
    (he : ∀ x ∈ B, e • x ∈ A) {q : ℕ} (hq : q.Prime) (hqd : q ∣ latIndex A B) : q ∣ e := by
  have : Fact q.Prime := ⟨hq⟩
  let H := A.toAddSubgroup.addSubgroupOf B.toAddSubgroup
  have hcard : Nat.card (B.toAddSubgroup ⧸ H) = latIndex A B := rfl
  have : Finite (B.toAddSubgroup ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hi)
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := B.toAddSubgroup ⧸ H) q (hcard ▸ hqd)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective g
  have h0 : e • (QuotientAddGroup.mk y : B.toAddSubgroup ⧸ H) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact he y y.2
  rw [← hg]
  exact addOrderOf_dvd_of_nsmul_eq_zero h0

theorem natCast_smul_le (n : ℕ) (Λ : Submodule ℤ ℂ) : (n : ℂ) • Λ ≤ Λ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_smul_latticeSub.1 hx
  have := Λ.toAddSubgroup.nsmul_mem hy n
  simpa [nsmul_eq_mul] using this

theorem natCast_smul_le_of_latIndex {B Λ : Submodule ℤ ℂ} {n : ℕ} (h : latIndex B Λ = n) :
    (n : ℂ) • Λ ≤ B := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_smul_latticeSub.1 hx
  have := latIndex_nsmul_mem (A := B) hy
  rw [h, nsmul_eq_mul] at this
  exact this

theorem nsmul_mem_natCast_smul {Λ : Submodule ℤ ℂ} {n : ℕ} {x : ℂ} (hx : x ∈ Λ) :
    n • x ∈ (n : ℂ) • Λ :=
  mem_smul_latticeSub.2 ⟨x, hx, by simp [nsmul_eq_mul]⟩

/-- The index of $n\Lambda$ in a lattice $\Lambda$ is $n^2$. -/
theorem latIndex_natCast_smul {Λ : Submodule ℤ ℂ} (hΛ : IsLatticeC Λ) (n : ℕ) :
    latIndex ((n : ℂ) • Λ) Λ = n ^ 2 := by
  have h1 : Module.Free ℤ Λ.toAddSubgroup.toIntSubmodule := hΛ.free
  have h2 : Module.Finite ℤ Λ.toAddSubgroup.toIntSubmodule := hΛ.finite
  have h := AddSubgroup.relIndex_map_nsmul n Λ.toAddSubgroup
  have h3 : Module.finrank ℤ Λ.toAddSubgroup = 2 := hΛ.finrank_eq
  rw [h3] at h
  have h4 : Λ.toAddSubgroup.map (nsmulAddMonoidHom (α := ℂ) n) = ((n : ℂ) • Λ).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_map]
    change _ ↔ x ∈ (n : ℂ) • Λ
    rw [mem_smul_latticeSub]
    simp [nsmul_eq_mul]
  rw [h4] at h
  exact h

/-- The core of Proposition 4.11(a): for coprime $m, n$, the subgroup $A + n\Lambda$ is the unique
intermediate subgroup of index $n$ in $\Lambda$, and it contains $A$ with index $m$. -/
theorem coprime_core {A Λ : Submodule ℤ ℂ} {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n)
    (hA : A ≤ Λ) (hi : latIndex A Λ = m * n) :
    latIndex (A ⊔ (n : ℂ) • Λ) Λ = n ∧ latIndex A (A ⊔ (n : ℂ) • Λ) = m := by
  set M := A ⊔ (n : ℂ) • Λ with hM
  have hAM : A ≤ M := le_sup_left
  have hMΛ : M ≤ Λ := sup_le hA (natCast_smul_le n Λ)
  have hmul := latIndex_mul hAM hMΛ
  rw [hi] at hmul
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
  have hk0 : latIndex M Λ ≠ 0 := fun h0 => hmn (by rw [← hmul, h0, mul_zero])
  have hm0 : latIndex A M ≠ 0 := fun h0 => hmn (by rw [← hmul, h0, zero_mul])
  have hkn : latIndex M Λ ∣ n := by
    have hcop : (latIndex M Λ).Coprime m := by
      refine Nat.coprime_of_dvd (fun q hq hqk hqm => ?_)
      have hqn : q ∣ n := prime_dvd_of_dvd_latIndex hk0
        (fun x hx => (le_sup_right : (n : ℂ) • Λ ≤ M) (nsmul_mem_natCast_smul hx)) hq hqk
      exact hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h hqm hqn)
    exact hcop.dvd_of_dvd_mul_left (Dvd.intro_left _ hmul)
  have hmm : latIndex A M ∣ m := by
    have hcop : (latIndex A M).Coprime n := by
      refine Nat.coprime_of_dvd (fun q hq hqk hqn => ?_)
      have hqm : q ∣ m := by
        refine prime_dvd_of_dvd_latIndex hm0 (e := m) ?_ hq hqk
        intro x hx
        obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
        obtain ⟨y, hy, rfl⟩ := mem_smul_latticeSub.1 hz
        have h1 : (m * n) • y ∈ A := by
          have := latIndex_nsmul_mem (A := A) hy
          rwa [hi] at this
        have h2 : m • (a + (n : ℂ) * y) = m • a + (m * n) • y := by
          simp only [nsmul_eq_mul, Nat.cast_mul, mul_add]; ring
        rw [h2]
        exact add_mem (A.toAddSubgroup.nsmul_mem ha m) h1
      exact hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h hqm hqn)
    exact hcop.dvd_of_dvd_mul_right (Dvd.intro _ hmul)
  have hk := Nat.le_of_dvd hn hkn
  have hm' := Nat.le_of_dvd hm hmm
  have hkpos := Nat.pos_of_ne_zero hk0
  have hmpos := Nat.pos_of_ne_zero hm0
  constructor
  · by_contra hne
    have : latIndex M Λ < n := lt_of_le_of_ne hk hne
    nlinarith
  · by_contra hne
    have : latIndex A M < m := lt_of_le_of_ne hm' hne
    nlinarith

/-- Number of subgroups of prime index in an elementary abelian group of order $p^2$. -/
theorem card_index_prime_subgroups {G : Type*} [AddCommGroup G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p ^ 2) (hexp : ∀ g : G, p • g = 0) :
    {H : AddSubgroup G | H.index = p}.ncard = p + 1 := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (AddSubgroup G)
  have hp2 := hp.two_le
  have hHcard : ∀ H : AddSubgroup G, H.index = p → Nat.card H = p := by
    intro H hH
    have h1 := H.index_mul_card
    rw [hH, hcard] at h1
    have : p * Nat.card H = p * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  have hz : ∀ g : G, g ≠ 0 → Nat.card (AddSubgroup.zmultiples g) = p := by
    intro g hg
    rw [Nat.card_zmultiples]
    have hd : addOrderOf g ∣ p := addOrderOf_dvd_of_nsmul_eq_zero (hexp g)
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · exact absurd (by simpa [h] using addOrderOf_nsmul_eq_zero g) hg
    · exact h
  have hzi : ∀ g : G, g ≠ 0 → (AddSubgroup.zmultiples g).index = p := by
    intro g hg
    have h1 := (AddSubgroup.zmultiples g).index_mul_card
    rw [hz g hg, hcard] at h1
    have : (AddSubgroup.zmultiples g).index * p = p * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos this
  set T : Finset (AddSubgroup G) := Finset.univ.filter (fun H => H.index = p) with hT
  have hTc : {H : AddSubgroup G | H.index = p}.ncard = T.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext H
    simp [hT]
  rw [hTc]
  set Z : Finset G := Finset.univ.erase 0 with hZ
  have hfib : ∀ H ∈ T, (Z.filter (fun g => AddSubgroup.zmultiples g = H)).card = p - 1 := by
    intro H hH
    have hHi : H.index = p := by simpa [hT] using hH
    have hHc := hHcard H hHi
    have : Z.filter (fun g => AddSubgroup.zmultiples g = H) =
        (Finset.univ.filter (fun g => g ∈ H)).erase 0 := by
      ext g
      simp only [hZ, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      constructor
      · rintro ⟨hg, h⟩
        exact ⟨hg, h ▸ AddSubgroup.mem_zmultiples g⟩
      · rintro ⟨hg, h⟩
        refine ⟨hg, ?_⟩
        refine AddSubgroup.eq_of_le_of_card_ge ?_ ?_
        · exact (AddSubgroup.zmultiples_le_of_mem h)
        · exact le_of_eq (by rw [hHc, hz g hg])
    rw [this, Finset.card_erase_of_mem (by simp)]
    have : (Finset.univ.filter (fun g => g ∈ H)).card = p := by
      rw [← hHc, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [this]
  have hsum := Finset.card_eq_sum_card_fiberwise (s := Z) (t := T)
    (f := fun g => AddSubgroup.zmultiples g) (by
      intro g hg
      have hg0 : g ≠ 0 := by simpa [hZ] using hg
      simp [hT, hzi g hg0])
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hsum
  have hZc : Z.card = p ^ 2 - 1 := by
    rw [hZ, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard]
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have hk : 0 < k := by omega
  have e1 : (k + 1) ^ 2 - 1 = k * (k + 2) := by
    have : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
    omega
  rw [hZc, e1, Nat.add_sub_cancel] at hsum
  have : T.card * k = (k + 2) * k := by rw [mul_comm (k + 2) k, hsum]
  exact Nat.eq_of_mul_eq_mul_right hk this

/-- A lattice has exactly $p + 1$ subgroups of prime index $p$. -/
theorem ncard_index_prime {Λ : Submodule ℤ ℂ} (hΛ : IsLatticeC Λ) {p : ℕ} (hp : p.Prime) :
    {K : Submodule ℤ ℂ | K ≤ Λ ∧ latIndex K Λ = p}.ncard = p + 1 := by
  classical
  obtain ⟨L, rfl⟩ := hΛ
  have : Fact p.Prime := ⟨hp⟩
  let e := L.latticeEquivProd
  let f : L.lattice.toAddSubgroup →+ ZMod p × ZMod p :=
    ((Int.castAddHom (ZMod p)).prodMap (Int.castAddHom (ZMod p))).comp e.toAddMonoidHom
  have hf : Function.Surjective f := by
    rintro ⟨a, b⟩
    obtain ⟨a', rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨b', rfl⟩ := ZMod.intCast_surjective b
    refine ⟨e.symm (a', b'), ?_⟩
    simp [f]
  have hexp : ∀ g : ZMod p × ZMod p, p • g = 0 := by
    intro g
    ext <;> simp
  have hker : ∀ x : L.lattice.toAddSubgroup, f x = 0 ↔ (x : ℂ) ∈ (p : ℂ) • L.lattice := by
    intro x
    constructor
    · intro h0
      have h1 : ((e x).1 : ZMod p) = 0 := congrArg Prod.fst h0
      have h2 : ((e x).2 : ZMod p) = 0 := congrArg Prod.snd h0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
      obtain ⟨a, ha⟩ := h1
      obtain ⟨b, hb⟩ := h2
      refine mem_smul_latticeSub.2 ⟨(e.symm (a, b) : ℂ), (e.symm (a, b)).2, ?_⟩
      have : (p : ℕ) • e.symm (a, b) = x := by
        apply e.injective
        rw [map_nsmul]
        simp only [LinearEquiv.apply_symm_apply]
        ext <;> simp [ha, hb]
      have := congrArg (fun w : L.lattice => (w : ℂ)) this
      simpa [nsmul_eq_mul] using this
    · intro hx
      obtain ⟨y, hy, hxy⟩ := mem_smul_latticeSub.1 hx
      have : x = p • (⟨y, hy⟩ : L.lattice.toAddSubgroup) := by
        apply Subtype.ext
        simp [← hxy, nsmul_eq_mul]
      rw [this, map_nsmul]
      exact hexp _
  have hG := card_index_prime_subgroups (G := ZMod p × ZMod p) hp
    (by simp [ZMod.card]; ring) hexp
  rw [← hG]
  let Φ : Submodule ℤ ℂ → AddSubgroup (ZMod p × ZMod p) := fun K =>
    (K.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup).map f
  have hker_le : ∀ K : Submodule ℤ ℂ, K ≤ L.lattice → latIndex K L.lattice = p →
      f.ker ≤ K.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup := by
    intro K hK hi x hx
    obtain ⟨y, hy, hxy⟩ := mem_smul_latticeSub.1 ((hker x).1 hx)
    have := latIndex_nsmul_mem (A := K) hy
    rw [hi, nsmul_eq_mul] at this
    rw [AddSubgroup.mem_addSubgroupOf]
    show (x : ℂ) ∈ K
    rw [← hxy]
    exact this
  have hΦidx : ∀ K : Submodule ℤ ℂ, K ≤ L.lattice → latIndex K L.lattice = p →
      (Φ K).index = p := by
    intro K hK hi
    rw [AddSubgroup.index_map_eq _ hf (hker_le K hK hi)]
    exact hi
  have hinj : Set.InjOn Φ {K | K ≤ L.lattice ∧ latIndex K L.lattice = p} := by
    intro K1 h1 K2 h2 heq
    have c1 : (Φ K1).comap f = K1.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup := by
      show (AddSubgroup.map f _).comap f = _
      rw [AddSubgroup.comap_map_eq, sup_of_le_left (hker_le K1 h1.1 h1.2)]
    have c2 : (Φ K2).comap f = K2.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup := by
      show (AddSubgroup.map f _).comap f = _
      rw [AddSubgroup.comap_map_eq, sup_of_le_left (hker_le K2 h2.1 h2.2)]
    have h12 : K1.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup =
        K2.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup := by
      rw [← c1, ← c2, heq]
    ext x
    constructor
    · intro hx
      have hxΛ : x ∈ L.lattice := h1.1 hx
      have : (⟨x, hxΛ⟩ : L.lattice.toAddSubgroup) ∈
          K1.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup := hx
      rw [h12] at this
      exact this
    · intro hx
      have hxΛ : x ∈ L.lattice := h2.1 hx
      have : (⟨x, hxΛ⟩ : L.lattice.toAddSubgroup) ∈
          K2.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup := hx
      rw [← h12] at this
      exact this
  have himg : Φ '' {K | K ≤ L.lattice ∧ latIndex K L.lattice = p} =
      {H : AddSubgroup (ZMod p × ZMod p) | H.index = p} := by
    ext H
    constructor
    · rintro ⟨K, ⟨hK, hi⟩, rfl⟩
      exact hΦidx K hK hi
    · intro hH
      let K' : AddSubgroup L.lattice.toAddSubgroup := H.comap f
      let K : Submodule ℤ ℂ := AddSubgroup.toIntSubmodule (K'.map L.lattice.toAddSubgroup.subtype)
      have hKΛ : K ≤ L.lattice := by
        rintro x ⟨y, _, rfl⟩
        exact y.2
      have hKsub : K.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup = K' := by
        ext y
        rw [AddSubgroup.mem_addSubgroupOf]
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := Subtype.ext hzy
          exact this ▸ hz
        · intro hy
          exact ⟨y, hy, rfl⟩
      have hKi : latIndex K L.lattice = p := by
        show (K.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup).index = p
        rw [hKsub]
        exact (AddSubgroup.index_comap_of_surjective H hf).trans hH
      refine ⟨K, ⟨hKΛ, hKi⟩, ?_⟩
      show (K.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup).map f = H
      rw [hKsub]
      exact AddSubgroup.map_comap_eq_self_of_surjective hf H
  have hnc : {K : Submodule ℤ ℂ | K ≤ L.lattice ∧ latIndex K L.lattice = p}.ncard =
      (Φ '' {K | K ≤ L.lattice ∧ latIndex K L.lattice = p}).ncard :=
    hinj.ncard_image.symm
  rw [hnc, himg]

/-- The unit $n \in \mathbb C^\times$ for a nonzero natural number $n$. -/
def natUnit (n : ℕ) (hn : n ≠ 0) : ℂˣ := Units.mk0 (n : ℂ) (Nat.cast_ne_zero.mpr hn)

@[simp] theorem natUnit_val (n : ℕ) (hn : n ≠ 0) : ((natUnit n hn : ℂˣ) : ℂ) = n := rfl

theorem heckeR_single {n : ℕ} (hn : n ≠ 0) (Λ : LatticeC) :
    heckeR n (Finsupp.single Λ 1) = Finsupp.single (natUnit n hn • Λ) 1 := by
  simp [heckeR, hn, natUnit]

open Classical in
/-- The coefficient of $[\Lambda_0]$ in $R(p)(T(n)[\Lambda])$. -/
theorem heckeR_heckeT_single_apply {p : ℕ} (hp : p ≠ 0) (n : ℕ) (Λ Λ0 : LatticeC) :
    ((heckeR p ∘ₗ heckeT n) (Finsupp.single Λ 1)) Λ0 =
      (((sublatticesOfIndex_finite n Λ).toFinset.filter
        (fun Λ''' => (p : ℂ) • Λ'''.1 = Λ0.1)).card : ℤ) := by
  rw [LinearMap.comp_apply, heckeT_single, map_sum, Finsupp.finsetSum_apply]
  simp only [heckeR_single hp, Finsupp.single_apply]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun Λ''' _ => ?_)
  by_cases h : (p : ℂ) • Λ'''.1 = Λ0.1
  · have h' : natUnit p hp • Λ''' = Λ0 := Subtype.ext h
    simp [h, h']
  · have h' : ¬ natUnit p hp • Λ''' = Λ0 := fun h' => h (congrArg Subtype.val h')
    simp [h, h']

/-- Nakayama-type statement: if $A + p\Lambda = \Lambda$ and $A$ has finite index, then $A = \Lambda$. -/
theorem le_of_sup_natCast_smul_eq {A Λ : Submodule ℤ ℂ} {p k : ℕ}
    (hk : latIndex A Λ = p ^ k) (hsup : A ⊔ (p : ℂ) • Λ = Λ) : Λ ≤ A := by
  have key : ∀ j : ℕ, ∀ x ∈ Λ, ∃ a ∈ A, ∃ z ∈ Λ, x = a + ((p ^ j : ℕ) : ℂ) * z := by
    intro j
    induction j with
    | zero => intro x hx; exact ⟨0, A.zero_mem, x, hx, by simp⟩
    | succ j ih =>
      intro x hx
      obtain ⟨a, ha, z, hz, rfl⟩ := ih x hx
      rw [← hsup] at hz
      obtain ⟨a1, ha1, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨u, hu, rfl⟩ := mem_smul_latticeSub.1 hw
      refine ⟨a + (p ^ j) • a1, add_mem ha (A.toAddSubgroup.nsmul_mem ha1 _), u, hu, ?_⟩
      simp only [nsmul_eq_mul]
      push_cast
      ring
  intro x hx
  obtain ⟨a, ha, z, hz, rfl⟩ := key k x hx
  have := latIndex_nsmul_mem (A := A) hz
  rw [hk, nsmul_eq_mul] at this
  exact add_mem ha (by simpa using this)

/-- The number of sublattices of prime index $p$ is $p + 1$. -/
theorem ncard_sublatticesOfIndex_prime (Λ : LatticeC) {p : ℕ} (hp : p.Prime) :
    (sublatticesOfIndex p Λ).ncard = p + 1 := by
  rw [← ncard_index_prime Λ.2 hp, ← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext K
  constructor
  · rintro ⟨Λ', ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨K, isLatticeC_of_latIndex_ne_zero Λ.2 h1 (by rw [h2]; exact hp.ne_zero)⟩,
      ⟨h1, h2⟩, rfl⟩

/-- **Proposition 4.11(a)** (Milne, *EC*, V, Proposition 4.11(a), p. 209): $T(mn) = T(m) \circ T(n)$ if
$\gcd(m, n) = 1$. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.11(a) (pdf p. 209)"]
theorem prop_4_11_a {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) :
    heckeT (m * n) = heckeT m ∘ₗ heckeT n := by
  classical
  apply Finsupp.lhom_ext'
  intro Λ
  apply LinearMap.ext_ring
  ext Λ0
  change (heckeT (m * n) (Finsupp.single Λ 1)) Λ0 = ((heckeT m ∘ₗ heckeT n) (Finsupp.single Λ 1)) Λ0
  rw [heckeT_single_apply, heckeT_comp_single_apply]
  by_cases hΛ0 : Λ0 ∈ sublatticesOfIndex (m * n) Λ
  · simp only [hΛ0, ↓reduceIte]
    obtain ⟨hA, hi⟩ := hΛ0
    obtain ⟨hk, hk'⟩ := coprime_core hm hn h hA hi
    have hlat : IsLatticeC (Λ0.1 ⊔ (n : ℂ) • Λ.1) :=
      isLatticeC_of_latIndex_ne_zero Λ.2 (sup_le hA (natCast_smul_le n Λ.1))
        (by rw [hk]; exact hn.ne')
    have hcard : ((sublatticesOfIndex_finite n Λ).toFinset.filter
        (fun Λ' => Λ0 ∈ sublatticesOfIndex m Λ')).card = 1 := by
      refine Finset.card_eq_one.2 ⟨⟨_, hlat⟩, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
      · simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨⟨sup_le hA (natCast_smul_le n Λ.1), hk⟩, le_sup_left, hk'⟩
      · intro Λ' hΛ'
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hΛ'
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hΛ'
        refine Subtype.ext ?_
        have hMΛ' : Λ0.1 ⊔ (n : ℂ) • Λ.1 ≤ Λ'.1 := sup_le h3 (natCast_smul_le_of_latIndex h2)
        exact (eq_of_latIndex_eq hMΛ' h1 (by rw [hk, h2]) (by rw [h2]; exact hn.ne')).symm
    rw [hcard]; simp
  · simp only [hΛ0, ↓reduceIte]
    have : ((sublatticesOfIndex_finite n Λ).toFinset.filter
        (fun Λ' => Λ0 ∈ sublatticesOfIndex m Λ')).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro Λ' hΛ' hΛ0'
      simp only [Set.Finite.mem_toFinset] at hΛ'
      apply hΛ0
      refine ⟨hΛ0'.1.trans hΛ'.1, ?_⟩
      rw [← latIndex_mul hΛ0'.1 hΛ'.1, hΛ0'.2, hΛ'.2]
    rw [this]; simp

/-- **Proposition 4.11(b)** (Milne, *EC*, V, Proposition 4.11(b), p. 209): for a prime $p$ and $r \ge 1$,
$T(p^r) \circ T(p) = T(p^{r+1}) + p\,R(p) \circ T(p^{r-1})$. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.11(b) (pdf p. 209)"]
theorem prop_4_11_b {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) :
    heckeT (p ^ r) ∘ₗ heckeT p = heckeT (p ^ (r + 1)) + (p : ℤ) • (heckeR p ∘ₗ heckeT (p ^ (r - 1))) := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : 1 < p := hp.one_lt
  simp only [Nat.add_sub_cancel]
  apply Finsupp.lhom_ext'
  intro Λ
  apply LinearMap.ext_ring
  ext Λ0
  change ((heckeT (p ^ (s + 1)) ∘ₗ heckeT p) (Finsupp.single Λ 1)) Λ0 =
    (heckeT (p ^ (s + 1 + 1)) (Finsupp.single Λ 1) +
      (p : ℤ) • (heckeR p ∘ₗ heckeT (p ^ s)) (Finsupp.single Λ 1)) Λ0
  rw [Finsupp.add_apply, Finsupp.smul_apply, heckeT_comp_single_apply, heckeT_single_apply,
    heckeR_heckeT_single_apply hp0]
  have hpow : p ^ 2 * p ^ s = p ^ (s + 1 + 1) := by ring
  by_cases hA : Λ0 ∈ sublatticesOfIndex (p ^ (s + 1 + 1)) Λ
  swap
  · have h1 : ((sublatticesOfIndex_finite p Λ).toFinset.filter
        (fun Λ' => Λ0 ∈ sublatticesOfIndex (p ^ (s + 1)) Λ')).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro Λ' hΛ' hΛ0'
      simp only [Set.Finite.mem_toFinset] at hΛ'
      apply hA
      refine ⟨hΛ0'.1.trans hΛ'.1, ?_⟩
      rw [← latIndex_mul hΛ0'.1 hΛ'.1, hΛ0'.2, hΛ'.2]
      ring
    have h2 : ((sublatticesOfIndex_finite (p ^ s) Λ).toFinset.filter
        (fun L3 => (p : ℂ) • L3.1 = Λ0.1)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro L3 hL3 heq
      simp only [Set.Finite.mem_toFinset] at hL3
      apply hA
      have hle : (p : ℂ) • L3.1 ≤ L3.1 := natCast_smul_le p _
      refine ⟨by rw [← heq]; exact hle.trans hL3.1, ?_⟩
      rw [← heq, ← latIndex_mul hle hL3.1, latIndex_natCast_smul L3.2, hL3.2, hpow]
    rw [h1, h2]
    simp [hA]
  · simp only [hA, ↓reduceIte]
    have hAidx : latIndex Λ0.1 Λ.1 = p ^ (s + 1 + 1) := hA.2
    by_cases hB : Λ0.1 ≤ (p : ℂ) • Λ.1
    · have h1 : ((sublatticesOfIndex_finite p Λ).toFinset.filter
          (fun Λ' => Λ0 ∈ sublatticesOfIndex (p ^ (s + 1)) Λ')).card = p + 1 := by
        rw [Finset.filter_true_of_mem, ← Set.ncard_eq_toFinset_card _ (sublatticesOfIndex_finite p Λ),
          ncard_sublatticesOfIndex_prime Λ hp]
        intro Λ' hΛ'
        simp only [Set.Finite.mem_toFinset] at hΛ'
        have hle : Λ0.1 ≤ Λ'.1 := hB.trans (natCast_smul_le_of_latIndex hΛ'.2)
        refine ⟨hle, ?_⟩
        have hm := latIndex_mul hle hΛ'.1
        rw [hΛ'.2, hAidx] at hm
        have : latIndex Λ0.1 Λ'.1 * p = p ^ (s + 1) * p := by rw [hm]; ring
        exact Nat.eq_of_mul_eq_mul_right hp.pos this
      have h2 : ((sublatticesOfIndex_finite (p ^ s) Λ).toFinset.filter
          (fun L3 => (p : ℂ) • L3.1 = Λ0.1)).card = 1 := by
        let c : ℂˣ := natUnit p hp0
        have hinv : (p : ℂ) * ((c⁻¹ : ℂˣ) : ℂ) = 1 := c.mul_inv
        have hinv' : ((c⁻¹ : ℂˣ) : ℂ) * (p : ℂ) = 1 := c.inv_mul
        have hlat : IsLatticeC (((c⁻¹ : ℂˣ) : ℂ) • Λ0.1) := isLatticeC_smul c⁻¹ Λ0.2
        have hcs : (p : ℂ) • (((c⁻¹ : ℂˣ) : ℂ) • Λ0.1) = Λ0.1 := by
          rw [smul_smul, hinv, one_smul]
        have hle1 : ((c⁻¹ : ℂˣ) : ℂ) • Λ0.1 ≤ Λ.1 := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := mem_smul_latticeSub.1 hx
          obtain ⟨z, hz, rfl⟩ := mem_smul_latticeSub.1 (hB hy)
          rw [← mul_assoc, hinv', one_mul]
          exact hz
        refine Finset.card_eq_one.2 ⟨⟨_, hlat⟩, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
        · simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
          refine ⟨⟨hle1, ?_⟩, hcs⟩
          have hle : (p : ℂ) • (((c⁻¹ : ℂˣ) : ℂ) • Λ0.1) ≤ ((c⁻¹ : ℂˣ) : ℂ) • Λ0.1 :=
            natCast_smul_le p _
          have hm := latIndex_mul hle hle1
          rw [latIndex_natCast_smul hlat, hcs, hAidx] at hm
          have : p ^ 2 * latIndex (((c⁻¹ : ℂˣ) : ℂ) • Λ0.1) Λ.1 = p ^ 2 * p ^ s := by
            rw [hpow, ← hm]
          exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) this
        · intro L3 hL3
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hL3
          refine Subtype.ext ?_
          show L3.1 = ((c⁻¹ : ℂˣ) : ℂ) • Λ0.1
          rw [← hL3.2, smul_smul, hinv', one_smul]
      rw [h1, h2]
      push_cast
      ring
    · have hMΛ : Λ0.1 ⊔ (p : ℂ) • Λ.1 ≤ Λ.1 := sup_le hA.1 (natCast_smul_le p _)
      have hcM : (p : ℂ) • Λ.1 ≤ Λ0.1 ⊔ (p : ℂ) • Λ.1 := le_sup_right
      have hk1 : latIndex (Λ0.1 ⊔ (p : ℂ) • Λ.1) Λ.1 ≠ 1 := by
        intro h1
        have hΛM : Λ.1 ≤ Λ0.1 ⊔ (p : ℂ) • Λ.1 := latIndex_eq_one.1 h1
        have hsup : Λ0.1 ⊔ (p : ℂ) • Λ.1 = Λ.1 := le_antisymm hMΛ hΛM
        have := le_of_sup_natCast_smul_eq (A := Λ0.1) (Λ := Λ.1) hAidx hsup
        have h2 : latIndex Λ0.1 Λ.1 = 1 := latIndex_eq_one.2 this
        rw [hAidx] at h2
        have : 1 < p ^ (s + 1 + 1) := Nat.one_lt_pow (by omega) hp1
        omega
      have ha1 : latIndex ((p : ℂ) • Λ.1) (Λ0.1 ⊔ (p : ℂ) • Λ.1) ≠ 1 := by
        intro h1
        exact hB (le_sup_left.trans (latIndex_eq_one.1 h1))
      have hmul := latIndex_mul hcM hMΛ
      rw [latIndex_natCast_smul Λ.2] at hmul
      have hMidx : latIndex (Λ0.1 ⊔ (p : ℂ) • Λ.1) Λ.1 = p := by
        have hd : latIndex (Λ0.1 ⊔ (p : ℂ) • Λ.1) Λ.1 ∣ p ^ 2 := Dvd.intro_left _ hmul
        obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow hp).1 hd
        interval_cases i
        · simp at hik; exact absurd hik hk1
        · simpa using hik
        · rw [hik] at hmul
          have : latIndex ((p : ℂ) • Λ.1) (Λ0.1 ⊔ (p : ℂ) • Λ.1) * p ^ 2 = 1 * p ^ 2 := by
            rw [hmul, one_mul]
          exact absurd (Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) this) ha1
      have hMlat : IsLatticeC (Λ0.1 ⊔ (p : ℂ) • Λ.1) :=
        isLatticeC_of_latIndex_ne_zero Λ.2 hMΛ (by rw [hMidx]; exact hp0)
      have h1 : ((sublatticesOfIndex_finite p Λ).toFinset.filter
          (fun Λ' => Λ0 ∈ sublatticesOfIndex (p ^ (s + 1)) Λ')).card = 1 := by
        refine Finset.card_eq_one.2 ⟨⟨_, hMlat⟩, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
        · simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
          refine ⟨⟨hMΛ, hMidx⟩, le_sup_left, ?_⟩
          have hm := latIndex_mul (le_sup_left : Λ0.1 ≤ Λ0.1 ⊔ (p : ℂ) • Λ.1) hMΛ
          rw [hMidx, hAidx] at hm
          have : latIndex Λ0.1 (Λ0.1 ⊔ (p : ℂ) • Λ.1) * p = p ^ (s + 1) * p := by
            rw [hm]; ring
          exact Nat.eq_of_mul_eq_mul_right hp.pos this
        · intro Λ' hΛ'
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hΛ'
          refine Subtype.ext ?_
          have hMΛ' : Λ0.1 ⊔ (p : ℂ) • Λ.1 ≤ Λ'.1 :=
            sup_le hΛ'.2.1 (natCast_smul_le_of_latIndex hΛ'.1.2)
          exact (eq_of_latIndex_eq hMΛ' hΛ'.1.1 (by rw [hMidx, hΛ'.1.2])
            (by rw [hΛ'.1.2]; exact hp0)).symm
      have h2 : ((sublatticesOfIndex_finite (p ^ s) Λ).toFinset.filter
          (fun L3 => (p : ℂ) • L3.1 = Λ0.1)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro L3 hL3 heq
        simp only [Set.Finite.mem_toFinset] at hL3
        apply hB
        rw [← heq]
        intro x hx
        obtain ⟨y, hy, rfl⟩ := mem_smul_latticeSub.1 hx
        exact mem_smul_latticeSub.2 ⟨y, hL3.1 hy, rfl⟩
      rw [h1, h2]
      simp

/-- Scaling by a unit is injective on subgroups. -/
theorem smul_left_cancel_sub (c : ℂˣ) {A B : Submodule ℤ ℂ} (h : (c : ℂ) • A = (c : ℂ) • B) :
    A = B := by
  have := congrArg (fun X => ((c⁻¹ : ℂˣ) : ℂ) • X) h
  simpa [smul_smul] using this

/-- Scaling by a unit carries the sublattices of index $n$ of $\Lambda$ to those of $c\Lambda$. -/
theorem sublatticesOfIndex_smul (c : ℂˣ) (n : ℕ) (Λ : LatticeC) :
    sublatticesOfIndex n (c • Λ) = (fun L => c • L) '' sublatticesOfIndex n Λ := by
  ext L
  constructor
  · rintro ⟨h1, h2⟩
    let L' : LatticeC := ⟨((c⁻¹ : ℂˣ) : ℂ) • L.1, isLatticeC_smul c⁻¹ L.2⟩
    have hcL : (c : ℂ) • L'.1 = L.1 := by
      show (c : ℂ) • (((c⁻¹ : ℂˣ) : ℂ) • L.1) = L.1
      rw [smul_smul, Units.mul_inv, one_smul]
    refine ⟨L', ⟨?_, ?_⟩, Subtype.ext hcL⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_smul_latticeSub.1 hx
      obtain ⟨z, hz, rfl⟩ := mem_smul_latticeSub.1 (h1 hy)
      rw [← mul_assoc, Units.inv_mul, one_mul]
      exact hz
    · have := latIndex_smul c.ne_zero L'.1 Λ.1
      rw [hcL] at this
      rw [← this]
      exact h2
  · rintro ⟨L', ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_smul_latticeSub.1 hx
      exact mem_smul_latticeSub.2 ⟨y, h1 hy, rfl⟩
    · show latIndex ((c : ℂ) • L'.1) ((c : ℂ) • Λ.1) = n
      rw [latIndex_smul c.ne_zero]
      exact h2

/-- For $n = 0$ there is no sublattice of index $0$ (infinite index) in a lattice. -/
theorem sublatticesOfIndex_zero (Λ : LatticeC) : sublatticesOfIndex 0 Λ = ∅ := by
  ext Λ'
  simp only [sublatticesOfIndex, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h
  exact latIndex_ne_zero Λ'.2 Λ.2 h

theorem heckeT_zero : heckeT 0 = 0 := by
  apply Finsupp.lhom_ext'
  intro Λ
  apply LinearMap.ext_ring
  change heckeT 0 (Finsupp.single Λ 1) = 0
  rw [heckeT_single]
  have : (sublatticesOfIndex_finite 0 Λ).toFinset = ∅ := by
    ext L
    simp [sublatticesOfIndex_zero]
  rw [this, Finset.sum_empty]

theorem heckeR_zero : heckeR 0 = 0 := by simp [heckeR]

theorem heckeT_one : heckeT 1 = 1 := by
  apply Finsupp.lhom_ext'
  intro Λ
  apply LinearMap.ext_ring
  change heckeT 1 (Finsupp.single Λ 1) = Finsupp.single Λ 1
  rw [heckeT_single]
  have : (sublatticesOfIndex_finite 1 Λ).toFinset = {Λ} := by
    ext L
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact Subtype.ext (le_antisymm h1 (latIndex_eq_one.1 h2))
    · rintro rfl
      exact ⟨le_rfl, AddSubgroup.relIndex_self _⟩
  rw [this, Finset.sum_singleton]

theorem heckeR_one : heckeR 1 = 1 := by
  apply Finsupp.lhom_ext'
  intro Λ
  apply LinearMap.ext_ring
  change heckeR 1 (Finsupp.single Λ 1) = Finsupp.single Λ 1
  rw [heckeR_single one_ne_zero]
  congr 1
  apply Subtype.ext
  show ((natUnit 1 one_ne_zero : ℂˣ) : ℂ) • Λ.1 = Λ.1
  simp

theorem heckeR_mul (a b : ℕ) : heckeR (a * b) = heckeR a ∘ₗ heckeR b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [heckeR_zero]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [heckeR_zero]
  apply Finsupp.lhom_ext'
  intro Λ
  apply LinearMap.ext_ring
  change heckeR (a * b) (Finsupp.single Λ 1) = heckeR a (heckeR b (Finsupp.single Λ 1))
  rw [heckeR_single (Nat.mul_ne_zero ha.ne' hb.ne'), heckeR_single hb.ne', heckeR_single ha.ne']
  congr 1
  apply Subtype.ext
  show ((a * b : ℕ) : ℂ) • Λ.1 = (a : ℂ) • ((b : ℂ) • Λ.1)
  rw [smul_smul, Nat.cast_mul]

theorem toFinset_sublatticesOfIndex_smul (c : ℂˣ) (n : ℕ) (Λ : LatticeC) :
    (sublatticesOfIndex_finite n (c • Λ)).toFinset =
      (sublatticesOfIndex_finite n Λ).toFinset.image (fun L => c • L) := by
  classical
  ext L
  simp only [Set.Finite.mem_toFinset, Finset.mem_image, sublatticesOfIndex_smul]
  exact Set.mem_image _ _ _

theorem smul_injective_latticeC (c : ℂˣ) : Function.Injective (fun L : LatticeC => c • L) :=
  fun _ _ h => Subtype.ext (smul_left_cancel_sub c (congrArg Subtype.val h))

theorem heckeR_heckeT_comm (n m : ℕ) : heckeR n ∘ₗ heckeT m = heckeT m ∘ₗ heckeR n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [heckeR_zero]
  apply Finsupp.lhom_ext'
  intro Λ
  apply LinearMap.ext_ring
  change heckeR n (heckeT m (Finsupp.single Λ 1)) = heckeT m (heckeR n (Finsupp.single Λ 1))
  rw [heckeR_single hn.ne' Λ, heckeT_single m Λ, heckeT_single m (natUnit n hn.ne' • Λ), map_sum]
  simp only [heckeR_single hn.ne']
  rw [toFinset_sublatticesOfIndex_smul, Finset.sum_image (fun a _ b _ h => smul_injective_latticeC _ h)]

/-- The generators $T(p)$, $R(p)$ ($p$ prime) of the Hecke algebra of lattices. -/
def heckeGen : Set (Module.End ℤ LatDiv) :=
  {T | ∃ p : ℕ, p.Prime ∧ T = heckeT p} ∪ {R | ∃ p : ℕ, p.Prime ∧ R = heckeR p}

theorem heckeGen_pairwise_commute : heckeGen.Pairwise Commute := by
  have hTT : ∀ p q : ℕ, p.Prime → q.Prime → Commute (heckeT p) (heckeT q) := by
    intro p q hp hq
    by_cases hpq : p = q
    · subst hpq; exact Commute.refl _
    · have hc : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
      have h1 := prop_4_11_a hp.pos hq.pos hc
      have h2 := prop_4_11_a hq.pos hp.pos hc.symm
      rw [mul_comm q p, h1] at h2
      exact h2
  have hTR : ∀ p q : ℕ, Commute (heckeT p) (heckeR q) := fun p q =>
    (heckeR_heckeT_comm q p).symm
  have hRR : ∀ p q : ℕ, Commute (heckeR p) (heckeR q) := by
    intro p q
    have h1 := heckeR_mul p q
    have h2 := heckeR_mul q p
    rw [mul_comm q p, h1] at h2
    exact h2
  rintro x (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) y (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) _
  · exact hTT p q hp hq
  · exact hTR p q
  · exact (hTR q p).symm
  · exact hRR p q

theorem heckeAdjoin_comm :
    ∀ x ∈ Algebra.adjoin ℤ heckeGen, ∀ y ∈ Algebra.adjoin ℤ heckeGen, x * y = y * x := by
  have := Algebra.isMulCommutative_adjoin ℤ heckeGen_pairwise_commute
  intro x hx y hy
  exact congrArg Subtype.val (this.is_comm.comm (⟨x, hx⟩ : Algebra.adjoin ℤ heckeGen) ⟨y, hy⟩)

theorem heckeR_mem_adjoin (n : ℕ) : heckeR n ∈ Algebra.adjoin ℤ heckeGen := by
  induction n using Nat.recOnMul with
  | zero => rw [heckeR_zero]; exact zero_mem _
  | one => rw [heckeR_one]; exact one_mem _
  | prime p hp => exact Algebra.subset_adjoin (Or.inr ⟨p, hp, rfl⟩)
  | mul a b ha hb =>
    have : heckeR (a * b) = heckeR a * heckeR b := heckeR_mul a b
    rw [this]
    exact mul_mem ha hb

theorem heckeT_mem_adjoin_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    heckeT (p ^ k) ∈ Algebra.adjoin ℤ heckeGen ∧ heckeT (p ^ (k + 1)) ∈ Algebra.adjoin ℤ heckeGen := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [pow_zero, heckeT_one]; exact one_mem _
    · rw [zero_add, pow_one]; exact Algebra.subset_adjoin (Or.inl ⟨p, hp, rfl⟩)
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h := prop_4_11_b hp (r := k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    have h3 : heckeT (p ^ (k + 1)) * heckeT p = heckeT (p ^ (k + 1 + 1)) +
        (p : ℤ) • (heckeR p * heckeT (p ^ k)) := h
    have h' : heckeT (p ^ (k + 1 + 1)) =
        heckeT (p ^ (k + 1)) * heckeT p - (p : ℤ) • (heckeR p * heckeT (p ^ k)) := by
      rw [h3]; abel
    rw [h']
    exact sub_mem (mul_mem ih.2 (Algebra.subset_adjoin (Or.inl ⟨p, hp, rfl⟩)))
      (zsmul_mem (mul_mem (heckeR_mem_adjoin p) ih.1) _)

theorem heckeT_mem_adjoin (n : ℕ) : heckeT n ∈ Algebra.adjoin ℤ heckeGen := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => rw [heckeT_zero]; exact zero_mem _
  | one => rw [heckeT_one]; exact one_mem _
  | prime_pow p k hp hk => exact (heckeT_mem_adjoin_prime_pow hp k).1
  | coprime a b ha hb hab iha ihb =>
    have : heckeT (a * b) = heckeT a * heckeT b := prop_4_11_a (by omega) (by omega) hab
    rw [this]
    exact mul_mem iha ihb

/-- The sum over divisors of a product of coprime numbers splits. -/
theorem sum_divisors_coprime {M : Type*} [AddCommMonoid M] {a b : ℕ} (h : a.Coprime b) (f : ℕ → M) :
    ∑ d ∈ (a * b).divisors, f d = ∑ d₁ ∈ a.divisors, ∑ d₂ ∈ b.divisors, f (d₁ * d₂) := by
  rw [Nat.Coprime.divisors_mul h, Finset.sum_map]
  rw [← Finset.sum_product (f := fun p : ℕ × ℕ => f (p.1 * p.2))]
  exact Finset.sum_attach (Finset.product a.divisors b.divisors) (fun p => f (p.1 * p.2))

/-- The right-hand side of Milne's Corollary 4.12 for an abstract family. -/
def heckeF {A : Type*} [CommRing A] (T R : ℕ → A) (m n : ℕ) : A :=
  ∑ d ∈ (Nat.gcd m n).divisors, (d : A) * (R d * T (m * n / d ^ 2))

section abstract

variable {A : Type*} [CommRing A] (T R : ℕ → A)

/-- Multiplicativity of `heckeF` over coprime splittings. -/
theorem heckeF_mul_of_coprime
    (hTcop : ∀ m n, 0 < m → 0 < n → m.Coprime n → T (m * n) = T m * T n)
    (hRmul : ∀ m n, R (m * n) = R m * R n)
    {m₁ n₁ m₂ n₂ : ℕ} (hm₁ : 0 < m₁) (hn₁ : 0 < n₁) (hm₂ : 0 < m₂) (hn₂ : 0 < n₂)
    (hcop : (m₁ * n₁).Coprime (m₂ * n₂)) :
    heckeF T R (m₁ * m₂) (n₁ * n₂) = heckeF T R m₁ n₁ * heckeF T R m₂ n₂ := by
  have c1 : m₁.Coprime m₂ := (hcop.coprime_dvd_left (Dvd.intro _ rfl)).coprime_dvd_right (Dvd.intro _ rfl)
  have c2 : m₁.Coprime n₂ := (hcop.coprime_dvd_left (Dvd.intro _ rfl)).coprime_dvd_right (Dvd.intro_left _ rfl)
  have c3 : n₁.Coprime m₂ := (hcop.coprime_dvd_left (Dvd.intro_left _ rfl)).coprime_dvd_right (Dvd.intro _ rfl)
  have c4 : n₁.Coprime n₂ := (hcop.coprime_dvd_left (Dvd.intro_left _ rfl)).coprime_dvd_right (Dvd.intro_left _ rfl)
  have hg : Nat.gcd (m₁ * m₂) (n₁ * n₂) = Nat.gcd m₁ n₁ * Nat.gcd m₂ n₂ := by
    rw [Nat.Coprime.gcd_mul _ c4, Nat.Coprime.gcd_mul_right_cancel _ c3.symm,
      Nat.Coprime.gcd_mul_left_cancel _ c2]
  have hgc : (Nat.gcd m₁ n₁).Coprime (Nat.gcd m₂ n₂) :=
    (hcop.coprime_dvd_left ((Nat.gcd_dvd_left _ _).trans (Dvd.intro _ rfl))).coprime_dvd_right
      ((Nat.gcd_dvd_left _ _).trans (Dvd.intro _ rfl))
  unfold heckeF
  rw [hg, sum_divisors_coprime hgc, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun d₁ hd₁ => Finset.sum_congr rfl (fun d₂ hd₂ => ?_))
  rw [Nat.mem_divisors] at hd₁ hd₂
  have h1m : d₁ ∣ m₁ := hd₁.1.trans (Nat.gcd_dvd_left _ _)
  have h1n : d₁ ∣ n₁ := hd₁.1.trans (Nat.gcd_dvd_right _ _)
  have h2m : d₂ ∣ m₂ := hd₂.1.trans (Nat.gcd_dvd_left _ _)
  have h2n : d₂ ∣ n₂ := hd₂.1.trans (Nat.gcd_dvd_right _ _)
  have e1 : d₁ ^ 2 ∣ m₁ * n₁ := by rw [pow_two]; exact mul_dvd_mul h1m h1n
  have e2 : d₂ ^ 2 ∣ m₂ * n₂ := by rw [pow_two]; exact mul_dvd_mul h2m h2n
  have hd1 : 0 < d₁ := Nat.pos_of_dvd_of_pos h1m hm₁
  have hd2 : 0 < d₂ := Nat.pos_of_dvd_of_pos h2m hm₂
  have hx : 0 < m₁ * n₁ / d₁ ^ 2 := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hm₁ hn₁) e1) (by positivity)
  have hy : 0 < m₂ * n₂ / d₂ ^ 2 := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hm₂ hn₂) e2) (by positivity)
  have hxy : (m₁ * n₁ / d₁ ^ 2).Coprime (m₂ * n₂ / d₂ ^ 2) :=
    (hcop.coprime_dvd_left (Nat.div_dvd_of_dvd e1)).coprime_dvd_right (Nat.div_dvd_of_dvd e2)
  have hq : m₁ * m₂ * (n₁ * n₂) / (d₁ * d₂) ^ 2 = m₁ * n₁ / d₁ ^ 2 * (m₂ * n₂ / d₂ ^ 2) := by
    rw [Nat.div_mul_div_comm e1 e2, mul_pow]
    congr 1
    ring
  rw [hq, hTcop _ _ hx hy hxy, hRmul, Nat.cast_mul]
  ring

/-- The antidiagonal sum appearing in the Chebyshev-type product formula. -/
def chebS (t : ℕ → A) (q : A) (r u : ℕ) : A :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r, q ^ ij.1 * t (u + 2 * ij.2)

theorem cheb_step (t : ℕ → A) (q : A) (ht : ∀ a, t (a + 1) * t 1 = t (a + 2) + q * t a) (r u : ℕ) :
    chebS t q (r + 2) u + q * chebS t q r (u + 2) = t 1 * chebS t q (r + 1) (u + 1) := by
  have h1 : chebS t q (r + 2) u =
      t (u + 2 * (r + 2)) + ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (r + 1), q ^ (ij.1 + 1) * t (u + 2 * ij.2) := by
    unfold chebS
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp
  have h2 : chebS t q (r + 1) (u + 2) = t (u + 2 + 2 * (r + 1)) + q * chebS t q r (u + 2) := by
    unfold chebS
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.mul_sum]
    simp only [pow_zero, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    ring
  have h3 : t 1 * chebS t q (r + 1) (u + 1) = chebS t q (r + 1) (u + 2) +
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (r + 1), q ^ (ij.1 + 1) * t (u + 2 * ij.2) := by
    unfold chebS
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    have e : u + 1 + 2 * ij.2 = u + 2 * ij.2 + 1 := by ring
    have e' : u + 2 + 2 * ij.2 = u + 2 * ij.2 + 2 := by ring
    rw [e, e']
    linear_combination q ^ ij.1 * ht (u + 2 * ij.2)
  have e : u + 2 * (r + 2) = u + 2 + 2 * (r + 1) := by ring
  rw [h3, h2, h1, e]
  ring

theorem cheb_prod (t : ℕ → A) (q : A) (ht0 : t 0 = 1) (ht : ∀ a, t (a + 1) * t 1 = t (a + 2) + q * t a) :
    ∀ r u, t r * t (r + u) = chebS t q r u := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro u
    match r, ih with
    | 0, _ => simp [chebS, ht0]
    | 1, _ =>
      have := ht u
      simp only [chebS, Finset.Nat.sum_antidiagonal_succ, Finset.HasAntidiagonal.antidiagonal_zero,
        Finset.sum_singleton]
      rw [add_comm 1 u]
      simp
      linear_combination this
    | r + 2, ih =>
      have h := cheb_step t q ht r u
      have hr2 : t (r + 2) = t (r + 1) * t 1 - q * t r := by linear_combination -(ht r)
      have i1 := ih (r + 1) (by omega) (u + 1)
      have i0 := ih r (by omega) (u + 2)
      have e1 : r + 1 + (u + 1) = r + 2 + u := by ring
      have e2 : r + (u + 2) = r + 2 + u := by ring
      calc t (r + 2) * t (r + 2 + u)
          = (t (r + 1) * t 1 - q * t r) * t (r + 2 + u) := by rw [hr2]
        _ = t 1 * (t (r + 1) * t (r + 1 + (u + 1))) - q * (t r * t (r + (u + 2))) := by
            rw [e1, e2]; ring
        _ = t 1 * chebS t q (r + 1) (u + 1) - q * chebS t q r (u + 2) := by rw [i1, i0]
        _ = chebS t q (r + 2) u := by linear_combination -h

theorem heckeF_comm (m n : ℕ) : heckeF T R m n = heckeF T R n m := by
  unfold heckeF
  rw [Nat.gcd_comm, mul_comm m n]

theorem R_pow (hR1 : R 1 = 1) (hRmul : ∀ m n, R (m * n) = R m * R n) (p k : ℕ) :
    R (p ^ k) = R p ^ k := by
  induction k with
  | zero => simp [hR1]
  | succ k ih => rw [pow_succ, hRmul, ih, pow_succ]

/-- Product formula for prime powers (Milne, Corollary 4.12, prime power case). -/
theorem prime_pow_prod (hT1 : T 1 = 1) (hR1 : R 1 = 1) (hRmul : ∀ m n, R (m * n) = R m * R n)
    {p : ℕ} (hp : p.Prime)
    (hTp : ∀ r, 1 ≤ r → T (p ^ r) * T p = T (p ^ (r + 1)) + (p : A) * (R p * T (p ^ (r - 1))))
    (r s : ℕ) : T (p ^ r) * T (p ^ s) = heckeF T R (p ^ r) (p ^ s) := by
  have key : ∀ r s, r ≤ s → T (p ^ r) * T (p ^ s) = heckeF T R (p ^ r) (p ^ s) := by
    intro r s hrs
    have ht0 : (fun a => T (p ^ a)) 0 = 1 := by simp [hT1]
    have ht : ∀ a, (fun a => T (p ^ a)) (a + 1) * (fun a => T (p ^ a)) 1 =
        (fun a => T (p ^ a)) (a + 2) + ((p : A) * R p) * (fun a => T (p ^ a)) a := by
      intro a
      have := hTp (a + 1) (by omega)
      simp only [pow_one, Nat.add_sub_cancel] at this ⊢
      rw [this]
      ring
    have h := cheb_prod (fun a => T (p ^ a)) ((p : A) * R p) ht0 ht r (s - r)
    have hs : r + (s - r) = s := by omega
    simp only [hs] at h
    rw [h]
    unfold heckeF chebS
    rw [Nat.gcd_eq_left (pow_dvd_pow p hrs), Nat.divisors_prime_pow hp, Finset.sum_map,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => ((p : A) * R p) ^ i * T (p ^ (s - r + 2 * j)))]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ r := by simpa [Nat.lt_succ_iff] using hk
    simp only [Function.Embedding.coeFn_mk]
    have hdiv : p ^ r * p ^ s / (p ^ k) ^ 2 = p ^ (s - r + 2 * (r - k)) := by
      rw [← pow_add, ← pow_mul, Nat.pow_div (by omega) hp.pos]
      congr 1
      omega
    rw [hdiv, R_pow R hR1 hRmul]
    push_cast
    ring
  rcases le_total r s with h | h
  · exact key r s h
  · rw [mul_comm, key s r h, heckeF_comm]

/-- The abstract form of Milne's Corollary 4.12. -/
theorem hecke_product_formula (hT1 : T 1 = 1) (hR1 : R 1 = 1)
    (hTcop : ∀ m n, 0 < m → 0 < n → m.Coprime n → T (m * n) = T m * T n)
    (hRmul : ∀ m n, R (m * n) = R m * R n)
    (hTp : ∀ p r, p.Prime → 1 ≤ r →
      T (p ^ r) * T p = T (p ^ (r + 1)) + (p : A) * (R p * T (p ^ (r - 1)))) :
    ∀ m, 0 < m → ∀ n, 0 < n → T m * T n = heckeF T R m n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm n hn
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · obtain ⟨p, hp, hpd⟩ : ∃ p, p.Prime ∧ p ∣ m := ⟨m.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd m⟩
      obtain ⟨a, m', hpm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
      obtain ⟨b, n', hpn', hneq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
      have ha : 1 ≤ a := by
        by_contra hcon
        have : a = 0 := by omega
        subst this
        apply hpm'
        rw [hmeq] at hpd
        simpa using hpd
      have hm'pos : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with h | h
        · rw [h] at hmeq; omega
        · exact h
      have hn'pos : 0 < n' := by
        rcases Nat.eq_zero_or_pos n' with h | h
        · rw [h] at hneq; omega
        · exact h
      have hpa : 0 < p ^ a := pow_pos hp.pos a
      have hpb : 0 < p ^ b := pow_pos hp.pos b
      have hlt : m' < m := by
        rw [hmeq]
        have : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.one_lt
        nlinarith
      have cm : (p ^ a).Coprime m' := Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm')
      have cn : (p ^ b).Coprime n' := Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn')
      have hcop : (p ^ a * p ^ b).Coprime (m' * n') := by
        rw [← pow_add]
        refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_)
        intro hd
        rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
        · exact hpm' hd
        · exact hpn' hd
      have e : T m * T n = (T (p ^ a) * T (p ^ b)) * (T m' * T n') := by
        rw [hmeq, hneq, hTcop _ _ hpa hm'pos cm, hTcop _ _ hpb hn'pos cn]
        ring
      rw [e, prime_pow_prod T R hT1 hR1 hRmul hp (fun r hr => hTp p r hp hr) a b, ih m' hlt hm'pos n' hn'pos,
        ← heckeF_mul_of_coprime T R hTcop hRmul hpa hpb hm'pos hn'pos hcop, ← hmeq, ← hneq]
    · have : m = 1 := by omega
      subst this
      simp [heckeF, hT1, hR1]

end abstract

/-- **Corollary 4.12** (Milne, *EC*, V, Corollary 4.12, p. 210): for $m, n \ge 1$,
$T(m) \circ T(n) = \sum_{d \mid \gcd(m, n)} d\,R(d) \circ T(mn/d^2)$. -/
@[kb "milne2006ec" "Ch. V, Corollary 4.12 (pdf p. 210)"]
theorem cor_4_12 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    heckeT m ∘ₗ heckeT n =
      ∑ d ∈ (Nat.gcd m n).divisors, (d : ℤ) • (heckeR d ∘ₗ heckeT (m * n / d ^ 2)) := by
  classical
  let H := Algebra.adjoin ℤ heckeGen
  let _ : CommRing H := { (inferInstance : Ring H) with
    mul_comm := fun a b => Subtype.ext (heckeAdjoin_comm a.1 a.2 b.1 b.2) }
  let T' : ℕ → H := fun n => ⟨heckeT n, heckeT_mem_adjoin n⟩
  let R' : ℕ → H := fun n => ⟨heckeR n, heckeR_mem_adjoin n⟩
  have hTp : ∀ p r, p.Prime → 1 ≤ r →
      T' (p ^ r) * T' p = T' (p ^ (r + 1)) + (p : H) * (R' p * T' (p ^ (r - 1))) := by
    intro p r hp hr
    apply Subtype.ext
    have h := prop_4_11_b hp hr
    show heckeT (p ^ r) * heckeT p = heckeT (p ^ (r + 1)) +
      (p : Module.End ℤ LatDiv) * (heckeR p * heckeT (p ^ (r - 1)))
    rw [← nsmul_eq_mul, ← natCast_zsmul]
    exact h
  have key := hecke_product_formula T' R' (Subtype.ext heckeT_one) (Subtype.ext heckeR_one)
    (fun m n _ _ h => Subtype.ext (prop_4_11_a ‹_› ‹_› h))
    (fun m n => Subtype.ext (heckeR_mul m n)) hTp m hm n hn
  have h := congrArg Subtype.val key
  refine h.trans ?_
  unfold heckeF
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  show (d : Module.End ℤ LatDiv) * (heckeR d * heckeT (m * n / d ^ 2)) = _
  rw [← nsmul_eq_mul, ← natCast_zsmul]
  rfl

/-- The $\mathbb Z$-subalgebra $H$ of $\mathrm{End}(\mathcal D)$ generated by the $T(p)$ and $R(p)$, $p$ prime
(Milne, *EC*, V, Corollary 4.13). -/
def heckeLatticeAlgebra : Subalgebra ℤ (Module.End ℤ LatDiv) :=
  Algebra.adjoin ℤ ({T | ∃ p : ℕ, p.Prime ∧ T = heckeT p} ∪ {R | ∃ p : ℕ, p.Prime ∧ R = heckeR p})

/-- **Corollary 4.13** (Milne, *EC*, V, Corollary 4.13, p. 210): the $\mathbb Z$-subalgebra $H$ of
$\mathrm{End}(\mathcal D)$ generated by the $T(p)$ and $R(p)$ ($p$ prime) is commutative and contains $T(n)$ for
all $n \ge 1$. -/
@[kb "milne2006ec" "Ch. V, Corollary 4.13 (pdf p. 210)"]
theorem cor_4_13 :
    (∀ x ∈ heckeLatticeAlgebra, ∀ y ∈ heckeLatticeAlgebra, x * y = y * x) ∧
      ∀ n : ℕ, 0 < n → heckeT n ∈ heckeLatticeAlgebra :=
  ⟨heckeAdjoin_comm, fun n _ => heckeT_mem_adjoin n⟩

/-- The linear extension $F : \mathcal D \to \mathbb C$, $F(\sum n_\Lambda [\Lambda]) = \sum n_\Lambda F(\Lambda)$, of a
function $F : \mathcal L \to \mathbb C$ (Milne, *EC*, V.4, p. 210). -/
def latFnExt (F : LatticeC → ℂ) : LatDiv →ₗ[ℤ] ℂ :=
  Finsupp.linearCombination ℤ F

/-- For a linear map $T : \mathcal D \to \mathcal D$ and $F : \mathcal L \to \mathbb C$, the function
$T \cdot F : \Lambda \mapsto F(T\Lambda)$ (Milne, *EC*, V.4, p. 210). -/
def heckeActFn (T : LatDiv →ₗ[ℤ] LatDiv) (F : LatticeC → ℂ) : LatticeC → ℂ :=
  fun Λ => latFnExt F (T (Finsupp.single Λ 1))

/-- $F : \mathcal L \to \mathbb C$ is homogeneous of weight $-2k$: $F(\lambda\Lambda) = \lambda^{-2k}F(\Lambda)$ for
all $\lambda \in \mathbb C^\times$ (Milne, *EC*, V.4, pp. 208, 210). -/
def IsHomogeneousLat (k : ℤ) (F : LatticeC → ℂ) : Prop :=
  ∀ (c : ℂˣ) (Λ : LatticeC), F (c • Λ) = (c : ℂ) ^ (-2 * k) * F Λ

theorem latFnExt_single (F : LatticeC → ℂ) (Λ : LatticeC) (b : ℤ) :
    latFnExt F (Finsupp.single Λ b) = b • F Λ := by
  simp [latFnExt, Finsupp.linearCombination_single]

/-- $F$ extended linearly after applying $T$ is the extension of $T \cdot F$. -/
theorem latFnExt_heckeActFn (T : LatDiv →ₗ[ℤ] LatDiv) (F : LatticeC → ℂ) (x : LatDiv) :
    latFnExt (heckeActFn T F) x = latFnExt F (T x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | single a b =>
    have h : (Finsupp.single a b : LatDiv) = b • Finsupp.single a 1 :=
      (Finsupp.smul_single_one a b).symm
    rw [h, map_smul, map_smul, map_smul]
    congr 1
    simp [latFnExt_single, heckeActFn]

/-- Milne, *EC*, V.4, p. 210 (running text): for example $(T(n) \cdot F)(\Lambda) = \sum_{(\Lambda:\Lambda') = n}
F(\Lambda')$. -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 210): formula for T(n)·F"]
theorem heckeActFn_heckeT (n : ℕ) (F : LatticeC → ℂ) (Λ : LatticeC) :
    heckeActFn (heckeT n) F Λ = ∑ Λ' ∈ (sublatticesOfIndex_finite n Λ).toFinset, F Λ' := by
  simp only [heckeActFn, heckeT_single, map_sum, latFnExt_single, one_smul]

/-- Milne, *EC*, V.4, p. 210 (running text): if $F$ is homogeneous of weight $-2k$, then
$R(n) \cdot F = n^{-2k} F$ ($n \ge 1$). -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 210): R(n)·F = n^(-2k) F"]
theorem heckeR_act_of_homogeneous {k : ℤ} {F : LatticeC → ℂ} (hF : IsHomogeneousLat k F) {n : ℕ} (hn : 0 < n) :
    heckeActFn (heckeR n) F = fun Λ => (n : ℂ) ^ (-2 * k) * F Λ := by
  funext Λ
  simp only [heckeActFn, heckeR_single hn.ne', latFnExt_single, one_smul]
  exact hF (natUnit n hn.ne') Λ

/-- $F \circ R(n) = n^{-2k} F$ on all of $\mathcal D$ for homogeneous $F$. -/
theorem latFnExt_heckeR {k : ℤ} {F : LatticeC → ℂ} (hF : IsHomogeneousLat k F) {n : ℕ} (hn : 0 < n)
    (x : LatDiv) : latFnExt F (heckeR n x) = (n : ℂ) ^ (-2 * k) * latFnExt F x := by
  rw [← latFnExt_heckeActFn, heckeR_act_of_homogeneous hF hn]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]
  | single a b => simp [latFnExt_single]; ring

/-- **Proposition 4.14, first assertion** (Milne, *EC*, V, Proposition 4.14, p. 210): if $F$ is homogeneous of
weight $-2k$, so is $T(n) \cdot F$. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.14 (pdf p. 210): T(n)·F is homogeneous"]
theorem prop_4_14 {k : ℤ} {F : LatticeC → ℂ} (hF : IsHomogeneousLat k F) (n : ℕ) :
    IsHomogeneousLat k (heckeActFn (heckeT n) F) := by
  classical
  intro c Λ
  rw [heckeActFn_heckeT, heckeActFn_heckeT]
  have himg : (sublatticesOfIndex_finite n (c • Λ)).toFinset =
      (sublatticesOfIndex_finite n Λ).toFinset.image (fun L => c • L) := by
    ext L
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, sublatticesOfIndex_smul]
    exact Set.mem_image _ _ _
  have hinj : Function.Injective (fun L : LatticeC => c • L) := fun a b h =>
    Subtype.ext (smul_left_cancel_sub c (congrArg Subtype.val h))
  rw [himg, Finset.sum_image (fun a _ b _ h => hinj h), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun L _ => hF c L)

/-- **Proposition 4.14(a)** (Milne, *EC*, V, Proposition 4.14(a), p. 210): $T(mn) \cdot F = T(m) \cdot T(n) \cdot F$
if $\gcd(m, n) = 1$. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.14(a) (pdf p. 210)"]
theorem prop_4_14_a {k : ℤ} {F : LatticeC → ℂ} (_hF : IsHomogeneousLat k F) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m.Coprime n) :
    heckeActFn (heckeT (m * n)) F = heckeActFn (heckeT m) (heckeActFn (heckeT n) F) := by
  funext Λ
  show latFnExt F (heckeT (m * n) (Finsupp.single Λ 1)) =
    latFnExt (heckeActFn (heckeT n) F) (heckeT m (Finsupp.single Λ 1))
  rw [latFnExt_heckeActFn, mul_comm m n, prop_4_11_a hn hm h.symm]
  rfl

/-- **Proposition 4.14(b)** (Milne, *EC*, V, Proposition 4.14(b), p. 210): for a prime $p$ and $r \ge 1$,
$T(p) \cdot T(p^r) \cdot F = T(p^{r+1}) \cdot F + p^{1-2k}\,T(p^{r-1}) \cdot F$. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.14(b) (pdf p. 210)"]
theorem prop_4_14_b {k : ℤ} {F : LatticeC → ℂ} (hF : IsHomogeneousLat k F) {p : ℕ} (hp : p.Prime) {r : ℕ}
    (hr : 1 ≤ r) :
    heckeActFn (heckeT p) (heckeActFn (heckeT (p ^ r)) F) =
      heckeActFn (heckeT (p ^ (r + 1))) F + (p : ℂ) ^ (1 - 2 * k) • heckeActFn (heckeT (p ^ (r - 1))) F := by
  funext Λ
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  show latFnExt (heckeActFn (heckeT (p ^ r)) F) (heckeT p (Finsupp.single Λ 1)) = _
  rw [latFnExt_heckeActFn]
  have h := congrArg (fun T => latFnExt F (T (Finsupp.single Λ 1))) (prop_4_11_b hp hr)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    map_smul] at h
  rw [latFnExt_heckeR hF hp.pos] at h
  rw [h]
  have e : (p : ℂ) ^ (1 - 2 * k) = (p : ℂ) * (p : ℂ) ^ (-2 * k) := by
    rw [show (1 - 2 * k) = 1 + (-2 * k) by ring, zpow_add₀ hp0, zpow_one]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, heckeActFn, zsmul_eq_mul,
    Int.cast_natCast]
  ring

end NumberFieldKB.MilneEC.Vb
