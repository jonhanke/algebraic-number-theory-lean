import NumberFieldKB.MilneEC.Ch5LSeries
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Finset.NatDivisors
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Milne, *Elliptic Curves*, Chapter V §4: Hecke operators on lattices

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §4, pdf pp. 208–210: the free abelian group
$\mathcal D$ on lattices, $T(n)$, $R(n)$, Proposition 4.11, Corollaries 4.12, 4.13, Proposition 4.14, the
correspondence between functions on lattices and on $\mathbb H$, and the Hecke operators of level one.
Lattices in $\mathbb C$ are the $\mathbb Z$-spans of Mathlib's `PeriodPair`s (as in Chapter III,
`NumberFieldKB.MilneEC.IsLattice`).
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold Pointwise Modular ArithmeticFunction.sigma

namespace NumberFieldKB.MilneEC.V

/-! ### Lattices and the free abelian group $\mathcal D$ -/

/-- A lattice in $\mathbb C$: the $\mathbb Z$-span of two $\mathbb R$-linearly independent complex numbers. -/
def IsLatticeC (Λ : Submodule ℤ ℂ) : Prop := ∃ L : PeriodPair, L.lattice = Λ

/-- The set $\mathcal L$ of lattices in $\mathbb C$ (pdf p. 208). -/
def LatticeC : Type := {Λ : Submodule ℤ ℂ // IsLatticeC Λ}

/-- The lattice of a period pair. -/
def LatticeC.ofPeriodPair (L : PeriodPair) : LatticeC := ⟨L.lattice, L, rfl⟩

/-- The lattice $\Lambda(z, 1) = \mathbb Zz + \mathbb Z$. -/
noncomputable def LatticeC.ofH (z : ℍ) : LatticeC := LatticeC.ofPeriodPair (periodPairOf z)

/-- Multiplication by $c \ne 0$ carries lattices to lattices. -/
theorem isLatticeC_map_mul {c : ℂ} (hc : c ≠ 0) (Λ : LatticeC) : IsLatticeC (Λ.1.map (LinearMap.mul ℤ ℂ c)) := by
  obtain ⟨L, hL⟩ := Λ.2
  have hind : LinearIndependent ℝ ![c * L.ω₁, c * L.ω₂] := by
    have := L.indep.map' (LinearMap.mulLeft ℝ c) (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hc))
    convert this using 1
    ext i; fin_cases i <;> simp
  refine ⟨⟨c * L.ω₁, c * L.ω₂, hind⟩, ?_⟩
  rw [← hL]
  simp only [PeriodPair.lattice, Submodule.map_span, Set.image_pair]
  simp

/-- The lattice $c\Lambda$, $c \ne 0$. -/
def LatticeC.scale {c : ℂ} (hc : c ≠ 0) (Λ : LatticeC) : LatticeC :=
  ⟨Λ.1.map (LinearMap.mul ℤ ℂ c), isLatticeC_map_mul hc Λ⟩

/-- The sublattices of index $n$ of $\Lambda$. -/
def sublatticesOfIndex (n : ℕ) (Λ : LatticeC) : Set LatticeC :=
  {Λ' | Λ'.1 ≤ Λ.1 ∧ Λ'.1.toAddSubgroup.relIndex Λ.1.toAddSubgroup = n}

/-- A lattice is a finitely generated `ℤ`-module. -/
theorem LatticeC.moduleFinite (Λ : LatticeC) : Module.Finite ℤ Λ.1 := by
  obtain ⟨L, hL⟩ := Λ.2
  rw [← hL]
  exact Module.Finite.of_basis L.latticeBasis

/-- A lattice has rank two. -/
theorem LatticeC.finrank_eq (Λ : LatticeC) : Module.finrank ℤ Λ.1 = 2 := by
  obtain ⟨L, hL⟩ := Λ.2
  rw [← hL]
  exact L.finrank_lattice

/-- If `Λ' ⊆ Λ` has relative index `n`, then `n • Λ ⊆ Λ'`. -/
theorem nsmul_mem_of_relIndex {Λ Λ' : Submodule ℤ ℂ} {n : ℕ}
    (hi : Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup = n) {x : ℂ} (hx : x ∈ Λ) : n • x ∈ Λ' := by
  have := AddSubgroup.nsmul_relIndex_mem Λ'.toAddSubgroup (K := Λ.toAddSubgroup) (g := x) hx
  rwa [hi] at this

/-- A lattice has finitely many sublattices of index $n \ge 1$ (they contain $n\Lambda$). -/
theorem sublatticesOfIndex_finite {n : ℕ} (hn : 1 ≤ n) (Λ : LatticeC) : (sublatticesOfIndex n Λ).Finite := by
  classical
  have := Λ.moduleFinite
  have : NeZero n := ⟨by omega⟩
  let N : Submodule ℤ Λ.1 := LinearMap.range (LinearMap.lsmul ℤ Λ.1 n)
  let g : AddSubgroup (ModN Λ.1 n) → AddSubgroup ℂ :=
    fun Q => (Q.comap (N.mkQ : Λ.1 →+ ModN Λ.1 n)).map Λ.1.toAddSubgroup.subtype
  have hfin : (Set.range g).Finite := Set.finite_range g
  have hsub : (fun Λ' : LatticeC => Λ'.1.toAddSubgroup) '' sublatticesOfIndex n Λ ⊆ Set.range g := by
    rintro _ ⟨Λ', ⟨hle, hi⟩, rfl⟩
    refine ⟨(Λ'.1.toAddSubgroup.addSubgroupOf Λ.1.toAddSubgroup).map (N.mkQ : Λ.1 →+ ModN Λ.1 n), ?_⟩
    have hker : (N.mkQ : Λ.1 →+ ModN Λ.1 n).ker ≤ Λ'.1.toAddSubgroup.addSubgroupOf Λ.1.toAddSubgroup := by
      intro x hx
      have hx' : x ∈ N := by simpa [Submodule.ker_mkQ] using hx
      obtain ⟨y, hy⟩ := hx'
      show (x : ℂ) ∈ Λ'.1
      rw [← hy]
      simpa using nsmul_mem_of_relIndex hi y.2
    simp only [g]
    rw [AddSubgroup.comap_map_eq, sup_of_le_left hker, AddSubgroup.addSubgroupOf_map_subtype]
    exact inf_eq_left.2 hle
  exact Set.Finite.of_finite_image (hfin.subset hsub) (fun a _ b _ h => Subtype.ext (by simpa using h))

/-- Every subgroup of index $n \ge 1$ of a lattice is a lattice: `sublatticesOfIndex` is the set of all subgroups
of index $n$ (Milne sums over all $\Lambda' \subset \Lambda$ with $(\Lambda : \Lambda') = n$). -/
theorem isLatticeC_of_relIndex {n : ℕ} (hn : 1 ≤ n) (Λ : LatticeC) (Λ' : Submodule ℤ ℂ) (hle : Λ' ≤ Λ.1)
    (hi : Λ'.toAddSubgroup.relIndex Λ.1.toAddSubgroup = n) : IsLatticeC Λ' := by
  classical
  obtain ⟨L, hL⟩ := Λ.2
  have hle' : Λ' ≤ L.lattice := hL ▸ hle
  have hmem : ∀ x ∈ L.lattice, n • x ∈ Λ' := fun x hx => nsmul_mem_of_relIndex hi (hL ▸ hx)
  have hfgΛ : (L.lattice).FG := Submodule.fg_span (Set.toFinite _)
  have hNoeth : IsNoetherian ℤ L.lattice := isNoetherian_of_fg_of_noetherian _ hfgΛ
  have hfg : Λ'.FG := by
    have h1 := IsNoetherian.noetherian (Λ'.comap L.lattice.subtype)
    have h2 := h1.map L.lattice.subtype
    rwa [Submodule.map_comap_subtype, inf_of_le_right hle'] at h2
  have : Module.Finite ℤ Λ' := Module.Finite.iff_fg.2 hfg
  have : Module.Finite ℤ L.lattice := Module.Finite.of_basis L.latticeBasis
  let b := Module.finBasis ℤ Λ'
  let v : Fin (Module.finrank ℤ Λ') → ℂ := fun i => ((b i : Λ') : ℂ)
  have hspanZ : Submodule.span ℤ (Set.range v) = Λ' := by
    have h := b.span_eq
    have h2 := congrArg (Submodule.map Λ'.subtype) h
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h2
    have h3 : Set.range v = ⇑Λ'.subtype '' Set.range ⇑b := by
      ext x; simp [v]
    rw [h3]; exact h2
  have hspanR : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    have hΛ'R : (Λ' : Set ℂ) ⊆ Submodule.span ℝ (Set.range v) := by
      intro x hx
      rw [← hspanZ] at hx
      exact Submodule.span_le_restrictScalars ℤ ℝ _ hx
    have hω : ∀ ω ∈ L.lattice, ω ∈ Submodule.span ℝ (Set.range v) := by
      intro ω hω
      have h1 := hΛ'R (hmem ω hω)
      have h2 := Submodule.smul_mem _ ((n : ℝ)⁻¹) h1
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      convert h2 using 1
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn0, one_smul]
    rw [← L.basis.span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using hω _ L.ω₁_mem_lattice
    · simpa using hω _ L.ω₂_mem_lattice
  have hge : 2 ≤ Module.finrank ℤ Λ' := by
    have h1 := finrank_range_le_card (R := ℝ) v
    have htop : Submodule.span ℝ (Set.range v) = ⊤ := eq_top_iff.2 hspanR
    rw [Set.finrank, htop, finrank_top, Complex.finrank_real_complex, Fintype.card_fin] at h1
    exact h1
  have hle2 : Module.finrank ℤ Λ' ≤ 2 := by
    have := Submodule.finrank_mono hle'
    rwa [L.finrank_lattice] at this
  have hr : Module.finrank ℤ Λ' = 2 := le_antisymm hle2 hge
  let w : Fin 2 → ℂ := v ∘ Fin.cast hr.symm
  have hrange : Set.range w = Set.range v :=
    (finCongr hr.symm).surjective.range_comp v
  have hind : LinearIndependent ℝ w := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · rw [hrange]; exact hspanR
    · simp
  refine ⟨⟨w 0, w 1, ?_⟩, ?_⟩
  · convert hind using 1
    ext i; fin_cases i <;> rfl
  · simp only [PeriodPair.lattice]
    rw [← hspanZ, ← hrange]
    congr 1
    ext x; simp [Fin.exists_fin_two, eq_comm]

/-- Milne's free abelian group $\mathcal D$ on the set $\mathcal L$ of lattices (pdf p. 208). -/
abbrev LatticeDiv : Type := LatticeC →₀ ℤ

open Classical in
/-- The sum $\sum_{(\Lambda:\Lambda') = n}[\Lambda']$ (empty for $n = 0$). -/
noncomputable def heckeSum (n : ℕ) (Λ : LatticeC) : LatticeDiv :=
  if h : (sublatticesOfIndex n Λ).Finite then ∑ Λ' ∈ h.toFinset, Finsupp.single Λ' 1 else 0

/-- $T(n) : \mathcal D \to \mathcal D$, $[\Lambda] \mapsto \sum_{(\Lambda:\Lambda') = n}[\Lambda']$ (pdf p. 208). -/
@[kb "milne2006ec" "Ch. V, §4, the operator T(n) on lattices (definition in prose), pdf p. 208"]
noncomputable def heckeTL (n : ℕ) : Module.End ℤ LatticeDiv :=
  Finsupp.linearCombination ℤ (heckeSum n)

/-- $R(n) : \mathcal D \to \mathcal D$, $[\Lambda] \mapsto [n\Lambda]$ (pdf p. 208), $n \ge 1$ ($R(0) = 0$). -/
@[kb "milne2006ec" "Ch. V, §4, the operator R(n) on lattices (definition in prose), pdf p. 208"]
noncomputable def heckeRL (n : ℕ) : Module.End ℤ LatticeDiv :=
  if h : (n : ℂ) ≠ 0 then Finsupp.linearCombination ℤ (fun Λ ↦ Finsupp.single (LatticeC.scale h Λ) 1) else 0

/-- Membership in the rescaled lattice $c\Lambda$. -/
theorem LatticeC.mem_scale {c : ℂ} (hc : c ≠ 0) (Λ : LatticeC) (x : ℂ) :
    x ∈ (LatticeC.scale hc Λ).1 ↔ ∃ y ∈ Λ.1, c * y = x := by
  simp [LatticeC.scale, Submodule.mem_map]

/-- Membership in the lattice $\mathbb Z z + \mathbb Z$ attached to a point $z$ of the upper half plane. -/
theorem LatticeC.mem_ofH (z : ℍ) (x : ℂ) :
    x ∈ (LatticeC.ofH z).1 ↔ ∃ m n : ℤ, (m : ℂ) * z + n = x := by
  simp [LatticeC.ofH, LatticeC.ofPeriodPair, PeriodPair.mem_lattice, periodPairOf]

/-- Two lattices with the same elements are equal. -/
theorem LatticeC.ext' {Λ Λ' : LatticeC} (h : ∀ x, x ∈ Λ.1 ↔ x ∈ Λ'.1) : Λ = Λ' :=
  Subtype.ext (Submodule.ext h)

/-- Rescaling by $d$ and then by $c$ is rescaling by $cd$. -/
theorem LatticeC.scale_scale {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) (Λ : LatticeC) :
    LatticeC.scale hc (LatticeC.scale hd Λ) = LatticeC.scale (mul_ne_zero hc hd) Λ := by
  refine LatticeC.ext' fun x => ?_
  simp only [LatticeC.mem_scale]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨d * y, ⟨y, hy, rfl⟩, by ring⟩

/-- Rescaling by $1$ does not change the lattice. -/
theorem LatticeC.scale_one (h : (1 : ℂ) ≠ 0) (Λ : LatticeC) : LatticeC.scale h Λ = Λ := by
  refine LatticeC.ext' fun x => ?_
  simp [LatticeC.mem_scale]

/-- Rescaling by equal nonzero scalars gives the same lattice. -/
theorem LatticeC.scale_congr {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) (Λ : LatticeC) (h : c = d) :
    LatticeC.scale hc Λ = LatticeC.scale hd Λ := by
  subst h; rfl

/-- The Hecke operator $T_n$ applied to a single lattice $\Lambda$ is the sum over its sublattices of index $n$. -/
theorem heckeTL_single (n : ℕ) (Λ : LatticeC) : heckeTL n (Finsupp.single Λ 1) = heckeSum n Λ := by
  simp [heckeTL, Finsupp.linearCombination_single]

/-- The operator $R_n$ applied to a single lattice $\Lambda$ is the single lattice $n\Lambda$. -/
theorem heckeRL_single {n : ℕ} (h : (n : ℂ) ≠ 0) (Λ : LatticeC) :
    heckeRL n (Finsupp.single Λ 1) = Finsupp.single (LatticeC.scale h Λ) 1 := by
  rw [heckeRL, dif_pos h, Finsupp.linearCombination_single, one_smul]

open Classical in
/-- The coefficient of $\Lambda''$ in the sum over sublattices of index $n$ of $\Lambda$ is $1$ or $0$ according to whether $\Lambda''$ is such a sublattice. -/
theorem heckeSum_apply {n : ℕ} (hn : 1 ≤ n) (Λ Λ'' : LatticeC) :
    heckeSum n Λ Λ'' = if Λ'' ∈ sublatticesOfIndex n Λ then 1 else 0 := by
  classical
  have hfin := sublatticesOfIndex_finite hn Λ
  rw [heckeSum, dif_pos hfin, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

/-- The relative index of submodules of `ℂ`, as a natural number. -/
noncomputable def rix (A B : Submodule ℤ ℂ) : ℕ := A.toAddSubgroup.relIndex B.toAddSubgroup

/-- For a chain $A \le B \le C$ of subgroups, the indices multiply: $[B:A][C:B] = [C:A]$. -/
theorem rix_mul {A B C : Submodule ℤ ℂ} (h1 : A ≤ B) (h2 : B ≤ C) : rix A B * rix B C = rix A C :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2

/-- If $[B:A] = n$ then $n x \in A$ for every $x \in B$. -/
theorem rix_nsmul_mem {A B : Submodule ℤ ℂ} {n : ℕ} (h : rix A B = n) {x : ℂ} (hx : x ∈ B) : n • x ∈ A :=
  nsmul_mem_of_relIndex h hx

/-- If $A \le A'$ then $[C:A']$ divides $[C:A]$. -/
theorem rix_dvd_of_le {A A' : Submodule ℤ ℂ} (C : Submodule ℤ ℂ) (h : A ≤ A') : rix A' C ∣ rix A C :=
  AddSubgroup.relIndex_dvd_of_le_left _ h

/-- The index $[B:A]$ is $1$ if and only if $B \le A$. -/
theorem rix_eq_one_iff {A B : Submodule ℤ ℂ} : rix A B = 1 ↔ B ≤ A := by
  unfold rix
  rw [AddSubgroup.relIndex_eq_one]
  exact Iff.rfl

/-- If $m$ is coprime to the relative index of two subgroups and $m$ times every element of one lies in the other, the corresponding relative index is coprime to $m$. -/
theorem coprime_relIndex_of_nsmul_mem {A : Type*} [AddCommGroup A] {K D : AddSubgroup A} {m k : ℕ}
    (hm : ∀ x ∈ D, m • x ∈ K) (hmk : m.Coprime k) (h0 : K.relIndex D ≠ 0) :
    (K.relIndex D).Coprime k := by
  classical
  refine Nat.coprime_of_dvd fun p hp hpd hpk => ?_
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (D ⧸ K.addSubgroupOf D) := Nat.finite_of_card_ne_zero h0
  have := Fintype.ofFinite (D ⧸ K.addSubgroupOf D)
  have hcard : p ∣ Fintype.card (D ⧸ K.addSubgroupOf D) := by
    rw [← Nat.card_eq_fintype_card]; exact hpd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hcard
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  have h1 : m • (y : D ⧸ K.addSubgroupOf D) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hm y y.2
  have := addOrderOf_dvd_of_nsmul_eq_zero h1
  rw [hx] at this
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hmk this hpk)

/-- The submodule `n • C`. -/
def nsmulSub (n : ℕ) (C : Submodule ℤ ℂ) : Submodule ℤ ℂ :=
  C.map (n • (LinearMap.id : ℂ →ₗ[ℤ] ℂ))

/-- An element lies in $nC$ if and only if it is $n y$ for some $y \in C$. -/
theorem mem_nsmulSub {n : ℕ} {C : Submodule ℤ ℂ} {x : ℂ} : x ∈ nsmulSub n C ↔ ∃ y ∈ C, n • y = x := by
  simp [nsmulSub, Submodule.mem_map]

/-- If $y \in C$ then $n y \in nC$. -/
theorem nsmul_mem_nsmulSub {n : ℕ} {C : Submodule ℤ ℂ} {y : ℂ} (hy : y ∈ C) : n • y ∈ nsmulSub n C :=
  mem_nsmulSub.2 ⟨y, hy, rfl⟩

/-- The subgroup $nC$ is contained in $C$. -/
theorem nsmulSub_le {n : ℕ} {C : Submodule ℤ ℂ} : nsmulSub n C ≤ C := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_nsmulSub.1 hx
  exact nsmul_mem hy n

/-- In a quotient of index `m * n` with `m`, `n` coprime there is exactly one intermediate subgroup of
index `n`. -/
theorem exists_unique_mid_coprime {C K : Submodule ℤ ℂ} (hKC : K ≤ C) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m.Coprime n) (hi : rix K C = m * n) :
    ∃! D : Submodule ℤ ℂ, K ≤ D ∧ D ≤ C ∧ rix D C = n := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
  refine ⟨K ⊔ nsmulSub n C, ⟨le_sup_left, sup_le hKC nsmulSub_le, ?_⟩, ?_⟩
  · have hmem0 : ∀ x ∈ K ⊔ nsmulSub n C, m • x ∈ K := by
      intro x hx
      obtain ⟨k, hk, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨y, hy, rfl⟩ := mem_nsmulSub.1 hw
      rw [smul_add, ← mul_smul]
      exact add_mem (nsmul_mem hk m) (rix_nsmul_mem hi hy)
    have hprod := rix_mul (le_sup_left : K ≤ K ⊔ nsmulSub n C) (sup_le hKC nsmulSub_le)
    rw [hi] at hprod
    have he0 : rix K (K ⊔ nsmulSub n C) ≠ 0 := fun h0 => hmn0 (by rw [← hprod, h0, zero_mul])
    have hd0 : rix (K ⊔ nsmulSub n C) C ≠ 0 := fun h0 => hmn0 (by rw [← hprod, h0, mul_zero])
    have he : (rix K (K ⊔ nsmulSub n C)).Coprime n :=
      coprime_relIndex_of_nsmul_mem (K := K.toAddSubgroup) (D := (K ⊔ nsmulSub n C).toAddSubgroup)
        hmem0 hmn he0
    have hd : (rix (K ⊔ nsmulSub n C) C).Coprime m :=
      coprime_relIndex_of_nsmul_mem (K := (K ⊔ nsmulSub n C).toAddSubgroup) (D := C.toAddSubgroup)
        (fun x hx => (le_sup_right : nsmulSub n C ≤ K ⊔ nsmulSub n C) (nsmul_mem_nsmulSub hx)) hmn.symm hd0
    have h1 : rix K (K ⊔ nsmulSub n C) ∣ m := he.dvd_of_dvd_mul_right ⟨_, hprod.symm⟩
    have h2 : rix (K ⊔ nsmulSub n C) C ∣ n := by
      apply hd.dvd_of_dvd_mul_left
      exact ⟨rix K (K ⊔ nsmulSub n C), by rw [← hprod]; ring⟩
    have h1' := Nat.le_of_dvd (by omega) h1
    have h2' := Nat.le_of_dvd (by omega) h2
    have hdpos : 0 < rix (K ⊔ nsmulSub n C) C := Nat.pos_of_ne_zero hd0
    have hepos : 0 < rix K (K ⊔ nsmulSub n C) := Nat.pos_of_ne_zero he0
    by_contra hne
    have hlt : rix (K ⊔ nsmulSub n C) C < n := lt_of_le_of_ne h2' hne
    nlinarith
  · rintro D ⟨hKD, hDC, hD⟩
    have hmul := rix_mul hKD hDC
    rw [hD, hi] at hmul
    have hKm : rix K D = m := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn0) hmul
    apply le_antisymm
    · intro x hx
      have hmx : m • x ∈ K := rix_nsmul_mem hKm hx
      have hnx : n • x ∈ nsmulSub n C := nsmul_mem_nsmulSub (hDC hx)
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hmn.symm
      have hx' : x = u • (n • x) + v • (m • x) := by
        simp only [nsmul_eq_mul, zsmul_eq_mul]
        have := congrArg (Int.cast : ℤ → ℂ) huv
        push_cast at this
        linear_combination (-x) * this
      rw [hx']
      exact add_mem (Submodule.mem_sup_right (Submodule.smul_mem _ _ hnx))
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ hmx))
    · refine sup_le hKD fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := mem_nsmulSub.1 hx
      exact rix_nsmul_mem hD hy

/-- A lattice $\Lambda'$ is a sublattice of $\Lambda$ of index $n$ if and only if $\Lambda' \le \Lambda$ and $[\Lambda:\Lambda'] = n$. -/
theorem mem_sublatticesOfIndex {n : ℕ} {Λ Λ' : LatticeC} :
    Λ' ∈ sublatticesOfIndex n Λ ↔ Λ'.1 ≤ Λ.1 ∧ rix Λ'.1 Λ.1 = n := Iff.rfl

open Classical in
/-- The coefficient of $\Lambda''$ in $T_m T_n$ applied to a single lattice $\Lambda$, as a count of intermediate lattices. -/
theorem heckeTL_comp_single_apply {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (Λ Λ'' : LatticeC) :
    heckeTL m (heckeTL n (Finsupp.single Λ 1)) Λ'' =
      (Set.ncard {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex n Λ ∧ Λ'' ∈ sublatticesOfIndex m Λ'} : ℤ) := by
  have hfin := sublatticesOfIndex_finite hn Λ
  rw [heckeTL_single, heckeSum, dif_pos hfin, map_sum, Finsupp.finsetSum_apply]
  simp only [heckeTL_single, heckeSum_apply hm]
  rw [Finset.sum_boole]
  have : {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex n Λ ∧ Λ'' ∈ sublatticesOfIndex m Λ'} =
      ↑(hfin.toFinset.filter (fun Λ' => Λ'' ∈ sublatticesOfIndex m Λ')) := by
    ext; simp
  rw [this, Set.ncard_coe_finset]

open Classical in
/-- The coefficient of $\Lambda''$ in $R_d T_n$ applied to a single lattice $\Lambda$, as a count of sublattices. -/
theorem heckeRL_comp_single_apply {n d : ℕ} (hd : (d : ℂ) ≠ 0) (hn : 1 ≤ n) (Λ Λ'' : LatticeC) :
    heckeRL d (heckeTL n (Finsupp.single Λ 1)) Λ'' =
      (Set.ncard {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex n Λ ∧ LatticeC.scale hd Λ' = Λ''} : ℤ) := by
  have hfin := sublatticesOfIndex_finite hn Λ
  rw [heckeTL_single, heckeSum, dif_pos hfin, map_sum, Finsupp.finsetSum_apply]
  simp only [heckeRL_single hd, Finsupp.single_apply]
  rw [Finset.sum_boole]
  have : {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex n Λ ∧ LatticeC.scale hd Λ' = Λ''} =
      ↑(hfin.toFinset.filter (fun Λ' => LatticeC.scale hd Λ' = Λ'')) := by
    ext; simp
  rw [this, Set.ncard_coe_finset]

/-- Two endomorphisms of the group of lattice divisors that agree on every single lattice are equal. -/
theorem hecke_ext {f g : Module.End ℤ LatticeDiv}
    (h : ∀ Λ Λ'' : LatticeC, f (Finsupp.single Λ 1) Λ'' = g (Finsupp.single Λ 1) Λ'') : f = g := by
  apply Finsupp.lhom_ext
  intro Λ a
  rw [← Finsupp.smul_single_one, map_zsmul, map_zsmul]
  congr 1
  ext Λ''
  exact h Λ Λ''

/-- Multiplication by a nonzero scalar $c$ preserves the index $[B:A]$. -/
theorem rix_map_mul {c : ℂ} (hc : c ≠ 0) (A B : Submodule ℤ ℂ) :
    rix (A.map (LinearMap.mul ℤ ℂ c)) (B.map (LinearMap.mul ℤ ℂ c)) = rix A B := by
  unfold rix
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  have hinj : Function.Injective ((LinearMap.mul ℤ ℂ c : ℂ →ₗ[ℤ] ℂ) : ℂ →+ ℂ) := mul_right_injective₀ hc
  exact AddSubgroup.relIndex_map_map_of_injective A.toAddSubgroup B.toAddSubgroup hinj

/-- Inclusion of lattices is preserved and reflected by rescaling by a nonzero scalar $c$. -/
theorem scale_le_iff {c : ℂ} (hc : c ≠ 0) (A B : LatticeC) :
    (LatticeC.scale hc A).1 ≤ (LatticeC.scale hc B).1 ↔ A.1 ≤ B.1 := by
  constructor
  · intro h x hx
    have : c * x ∈ (LatticeC.scale hc B).1 := h ((LatticeC.mem_scale hc A _).2 ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, hxy⟩ := (LatticeC.mem_scale hc B _).1 this
    rwa [mul_left_cancel₀ hc hxy] at hy
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := (LatticeC.mem_scale hc A _).1 hx
    exact (LatticeC.mem_scale hc B _).2 ⟨y, h hy, rfl⟩

/-- Rescaling by a nonzero scalar $c$ preserves and reflects being a sublattice of index $n$. -/
theorem scale_mem_sublatticesOfIndex_iff {c : ℂ} (hc : c ≠ 0) {n : ℕ} (Λ Λ1 : LatticeC) :
    LatticeC.scale hc Λ1 ∈ sublatticesOfIndex n (LatticeC.scale hc Λ) ↔ Λ1 ∈ sublatticesOfIndex n Λ := by
  rw [mem_sublatticesOfIndex, mem_sublatticesOfIndex, scale_le_iff]
  exact and_congr_right fun _ => by
    show rix (Λ1.1.map _) (Λ.1.map _) = n ↔ _
    rw [rix_map_mul hc]

/-- Rescaling lattices by a nonzero scalar $c$ is injective. -/
theorem scale_injective {c : ℂ} (hc : c ≠ 0) : Function.Injective (LatticeC.scale hc) := by
  intro A B h
  refine LatticeC.ext' fun x => ?_
  have h1 := LatticeC.mem_scale hc A (c * x)
  have h2 := LatticeC.mem_scale hc B (c * x)
  rw [h] at h1
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := h2.1 (h1.2 ⟨x, hx, rfl⟩)
    rwa [mul_left_cancel₀ hc hxy] at hy
  · intro hx
    obtain ⟨y, hy, hxy⟩ := h1.1 (h2.2 ⟨x, hx, rfl⟩)
    rwa [mul_left_cancel₀ hc hxy] at hy

/-- The lattice $n\Lambda$ has index $n^2$ in $\Lambda$ (stated for rescaling by $n$). -/
theorem rix_scale_self {n : ℕ} (hn : 1 ≤ n) (Λ : LatticeC) :
    rix (LatticeC.scale (by exact_mod_cast (by omega : n ≠ 0) : (n : ℂ) ≠ 0) Λ).1 Λ.1 = n ^ 2 := by
  classical
  have := Λ.moduleFinite
  have : Module.Free ℤ Λ.1 := by
    obtain ⟨L, hL⟩ := Λ.2
    rw [← hL]
    exact Module.Free.of_basis L.latticeBasis
  have : NeZero n := ⟨by omega⟩
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have key : (LatticeC.scale hnc Λ).1.toAddSubgroup.addSubgroupOf Λ.1.toAddSubgroup =
      (LinearMap.range (LinearMap.lsmul ℤ Λ.1 n)).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, LatticeC.mem_scale,
      LinearMap.mem_range, LinearMap.lsmul_apply]
    constructor
    · rintro ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      simp [← hxy]
    · rintro ⟨y, hy⟩
      refine ⟨y, y.2, ?_⟩
      rw [← hy]; simp
  show ((LatticeC.scale hnc Λ).1.toAddSubgroup.addSubgroupOf Λ.1.toAddSubgroup).index = n ^ 2
  rw [key]
  have h := ModN.natCard_eq Λ.1 n
  rw [LatticeC.finrank_eq] at h
  exact h

/-- Build a lattice from a submodule known to be a lattice. -/
def LatticeC.mk' (D : Submodule ℤ ℂ) (h : IsLatticeC D) : LatticeC := ⟨D, h⟩

/-- A group of order `p ^ 2` killed by `p` has exactly `p + 1` subgroups of index `p`. -/
theorem card_index_prime_subgroups {G : Type*} [AddCommGroup G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p ^ 2) (hexp : ∀ x : G, p • x = 0) :
    Set.ncard {H : AddSubgroup G | H.index = p} = p + 1 := by
  classical
  have := Fintype.ofFinite G
  have hp2 := hp.two_le
  have hH : ∀ H : AddSubgroup G, H.index = p → Nat.card H = p := by
    intro H hH
    have := H.card_mul_index
    rw [hcard, hH] at this
    exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [this]; ring)
  have hz : ∀ x : G, x ≠ 0 → (AddSubgroup.zmultiples x).index = p := by
    intro x hx
    have h1 : addOrderOf x ∣ p := addOrderOf_dvd_of_nsmul_eq_zero (hexp x)
    have h2 : addOrderOf x = p := by
      rcases (Nat.dvd_prime hp).1 h1 with h | h
      · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) hx
      · exact h
    have := (AddSubgroup.zmultiples x).card_mul_index
    rw [Nat.card_zmultiples, h2, hcard] at this
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [this]; ring)
  let P : Finset (AddSubgroup G) := Finset.univ.filter (fun H => H.index = p)
  have hPset : {H : AddSubgroup G | H.index = p} = ↑P := by ext; simp [P]
  rw [hPset, Set.ncard_coe_finset]
  let S : Finset G := Finset.univ.erase 0
  have hS : S.card = p ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  have hfib : ∀ H ∈ P, (S.filter (fun x => AddSubgroup.zmultiples x = H)).card = p - 1 := by
    intro H hHP
    have hHi : H.index = p := by simpa [P] using hHP
    have hHc := hH H hHi
    have : S.filter (fun x => AddSubgroup.zmultiples x = H) = (Finset.univ.filter (· ∈ H)).erase 0 := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true, ne_eq]
      constructor
      · rintro ⟨hx, rfl⟩
        exact ⟨hx, AddSubgroup.mem_zmultiples x⟩
      · rintro ⟨hx, hxH⟩
        refine ⟨hx, ?_⟩
        have hle : AddSubgroup.zmultiples x ≤ H := (AddSubgroup.zmultiples_le).2 hxH
        have hc : Nat.card H ≤ Nat.card (AddSubgroup.zmultiples x) := by
          rw [hHc, Nat.card_zmultiples]
          have h1 : addOrderOf x ∣ p := addOrderOf_dvd_of_nsmul_eq_zero (hexp x)
          rcases (Nat.dvd_prime hp).1 h1 with h | h
          · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) hx
          · exact h.ge
        exact AddSubgroup.eq_of_le_of_card_ge hle hc
    have hc2 : (Finset.univ.filter (· ∈ H)).card = p := by
      rw [← hHc, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    rw [this, Finset.card_erase_of_mem (by simp), hc2]
  have hmaps : ∀ x ∈ S, AddSubgroup.zmultiples x ∈ P := by
    intro x hx
    have hx0 : x ≠ 0 := by simpa [S] using hx
    simp [P, hz x hx0]
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun x => AddSubgroup.zmultiples x) hmaps
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hS] at hsum
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have h3 : (q + 2) ^ 2 - 1 = (q + 1) * (q + 3) := by
    have : (q + 2) ^ 2 = (q + 1) * (q + 3) + 1 := by ring
    omega
  rw [h3] at hsum
  have h4 : q + 2 - 1 = q + 1 := by omega
  rw [h4] at hsum
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < q + 1) (by rw [hsum]; ring : (q + 1) * (q + 3) = (q + 1) * P.card)
  omega

/-- A lattice is a free $\mathbb Z$-module. -/
theorem LatticeC.moduleFree (Λ : LatticeC) : Module.Free ℤ Λ.1 := by
  obtain ⟨L, hL⟩ := Λ.2
  rw [← hL]
  exact Module.Free.of_basis L.latticeBasis

/-- If $[\Lambda:\Lambda'] = n$ then the kernel of the quotient map by $\Lambda'$ is contained in the corresponding subgroup of $\Lambda$. -/
theorem ker_mkQ_le_addSubgroupOf {n : ℕ} {Λ : LatticeC} {Λ' : Submodule ℤ ℂ} (hi : rix Λ' Λ.1 = n) :
    ((LinearMap.range (LinearMap.lsmul ℤ Λ.1 n)).mkQ : Λ.1 →+ ModN Λ.1 n).ker ≤
      Λ'.toAddSubgroup.addSubgroupOf Λ.1.toAddSubgroup := by
  intro x hx
  have hx' : x ∈ LinearMap.range (LinearMap.lsmul ℤ Λ.1 n) := by
    simpa [Submodule.ker_mkQ] using hx
  obtain ⟨y, hy⟩ := hx'
  show (x : ℂ) ∈ Λ'
  rw [← hy]
  simpa using rix_nsmul_mem hi y.2

/-- A lattice has exactly `p + 1` sublattices of prime index `p`. -/
theorem ncard_sublatticesOfIndex_prime {p : ℕ} (hp : p.Prime) (Λ : LatticeC) :
    (sublatticesOfIndex p Λ).ncard = p + 1 := by
  classical
  have := Λ.moduleFinite
  have := Λ.moduleFree
  have : NeZero p := ⟨hp.ne_zero⟩
  let N : Submodule ℤ Λ.1 := LinearMap.range (LinearMap.lsmul ℤ Λ.1 p)
  have hcard : Nat.card (ModN Λ.1 p) = p ^ 2 := by
    have h := ModN.natCard_eq Λ.1 p
    rwa [LatticeC.finrank_eq] at h
  have hexp : ∀ x : ModN Λ.1 p, p • x = 0 := by
    intro x
    rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
    simp
  rw [← card_index_prime_subgroups hp hcard hexp]
  apply Set.ncard_congr (fun Λ' _ =>
    (Λ'.1.toAddSubgroup.addSubgroupOf Λ.1.toAddSubgroup).map (N.mkQ : Λ.1 →+ ModN Λ.1 p))
  · intro Λ' hΛ'
    obtain ⟨hle, hi⟩ := hΛ'
    show _ = p
    rw [AddSubgroup.index_map_eq _ (N.mkQ_surjective) (ker_mkQ_le_addSubgroupOf hi)]
    exact hi
  · intro A B hA hB hAB
    obtain ⟨hleA, hiA⟩ := hA
    obtain ⟨hleB, hiB⟩ := hB
    have h1 := congrArg (AddSubgroup.comap (N.mkQ : Λ.1 →+ ModN Λ.1 p)) hAB
    rw [AddSubgroup.comap_map_eq, AddSubgroup.comap_map_eq, sup_of_le_left (ker_mkQ_le_addSubgroupOf hiA),
      sup_of_le_left (ker_mkQ_le_addSubgroupOf hiB)] at h1
    have h2 := congrArg (AddSubgroup.map Λ.1.toAddSubgroup.subtype) h1
    rw [AddSubgroup.addSubgroupOf_map_subtype, AddSubgroup.addSubgroupOf_map_subtype,
      inf_eq_left.2 (show A.1.toAddSubgroup ≤ Λ.1.toAddSubgroup from hleA),
      inf_eq_left.2 (show B.1.toAddSubgroup ≤ Λ.1.toAddSubgroup from hleB)] at h2
    exact LatticeC.ext' fun x => by
      have := SetLike.ext_iff.1 h2 x
      simpa using this
  · intro H' hH'
    let H : AddSubgroup Λ.1 := H'.comap (N.mkQ : Λ.1 →+ ModN Λ.1 p)
    have hHi : H.index = p := by
      rw [AddSubgroup.index_comap_of_surjective _ N.mkQ_surjective]
      exact hH'
    let A : Submodule ℤ ℂ := AddSubgroup.toIntSubmodule (H.map Λ.1.toAddSubgroup.subtype)
    have hAle : A ≤ Λ.1 := by
      rintro _ ⟨y, hy, rfl⟩
      exact y.2
    have hAH : A.toAddSubgroup.addSubgroupOf Λ.1.toAddSubgroup = H := by
      show ((H.map Λ.1.toAddSubgroup.subtype).addSubgroupOf Λ.1.toAddSubgroup) = H
      exact AddSubgroup.comap_map_eq_self_of_injective Subtype.val_injective H
    have hAi : rix A Λ.1 = p := by
      show (A.toAddSubgroup.addSubgroupOf Λ.1.toAddSubgroup).index = p
      rw [hAH]; exact hHi
    have hAlat : IsLatticeC A := isLatticeC_of_relIndex hp.one_lt.le Λ A hAle hAi
    refine ⟨LatticeC.mk' A hAlat, ⟨hAle, hAi⟩, ?_⟩
    show AddSubgroup.map (N.mkQ : Λ.1 →+ ModN Λ.1 p) (A.toAddSubgroup.addSubgroupOf Λ.1.toAddSubgroup) = H'
    rw [hAH]
    exact AddSubgroup.map_comap_eq_self_of_surjective N.mkQ_surjective H'

/-- If $(\Lambda : \Lambda'') = p^r$ with $p$ prime and $r \ge 1$, then $\Lambda \not\subseteq \Lambda'' + p\Lambda$. -/
theorem not_le_sup_nsmulSub {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) {Λ Λ'' : Submodule ℤ ℂ}
    (hi : rix Λ'' Λ = p ^ r) : ¬ Λ ≤ Λ'' ⊔ nsmulSub p Λ := by
  classical
  intro hcov
  have : Fact p.Prime := ⟨hp⟩
  have h0 : Λ''.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 := by
    change rix Λ'' Λ ≠ 0
    rw [hi]; exact pow_ne_zero _ hp.ne_zero
  have hfin : Finite (Λ ⧸ Λ''.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero h0
  have := Fintype.ofFinite (Λ ⧸ Λ''.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup)
  have hcard : p ∣ Fintype.card (Λ ⧸ Λ''.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup) := by
    rw [← Nat.card_eq_fintype_card]
    change p ∣ rix Λ'' Λ
    rw [hi]; exact dvd_pow_self p (by omega)
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hcard
  have hsurj : Function.Surjective
      (fun y : Λ ⧸ Λ''.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup => p • y) := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨k, hk, w, hw, hkw⟩ := Submodule.mem_sup.1 (hcov z.2)
    obtain ⟨u, hu, rfl⟩ := mem_nsmulSub.1 hw
    refine ⟨((⟨u, hu⟩ : Λ) : Λ ⧸ Λ''.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup), ?_⟩
    show p • ((⟨u, hu⟩ : Λ) : Λ ⧸ Λ''.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup) = (z : Λ ⧸ _)
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq]
    show ((-(p • (⟨u, hu⟩ : Λ)) + z : Λ) : ℂ) ∈ Λ''
    have : ((-(p • (⟨u, hu⟩ : Λ)) + z : Λ) : ℂ) = k := by
      have hz : (z : ℂ) = k + p • u := hkw.symm
      simp [hz]
    rw [this]; exact hk
  have hinj := Finite.injective_iff_surjective.2 hsurj
  have hx0 : p • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have : x = 0 := hinj (by simpa using hx0)
  rw [this, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

/-- The lattice $n\Lambda$ is contained in $\Lambda$. -/
theorem scale_le_self {n : ℕ} (hn : (n : ℂ) ≠ 0) (Λ : LatticeC) : (LatticeC.scale hn Λ).1 ≤ Λ.1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (LatticeC.mem_scale hn Λ x).1 hx
  have : (n : ℂ) * y = n • y := by simp
  rw [this]; exact nsmul_mem hy n

/-- The rescaled lattice $n\Lambda$ has underlying subgroup $n\Lambda$. -/
theorem scale_val_eq_nsmulSub {n : ℕ} (hn : (n : ℂ) ≠ 0) (Λ : LatticeC) :
    (LatticeC.scale hn Λ).1 = nsmulSub n Λ.1 := by
  refine Submodule.ext fun x => ?_
  rw [LatticeC.mem_scale, mem_nsmulSub]
  simp

/-- If $\Lambda''$ is not a sublattice of $\Lambda$ of index $mn$, the set of intermediate lattices in a chain of indices $m$ and $n$ is empty. -/
theorem chain_set_eq_empty {m n : ℕ} {Λ Λ'' : LatticeC} (h : Λ'' ∉ sublatticesOfIndex (m * n) Λ) :
    {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex n Λ ∧ Λ'' ∈ sublatticesOfIndex m Λ'} = ∅ := by
  ext Λ'
  simp only [Set.mem_setOf_eq, mem_sublatticesOfIndex, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, h3, h4⟩
  apply h
  refine ⟨h3.trans h1, ?_⟩
  show rix Λ''.1 Λ.1 = m * n
  rw [← rix_mul h3 h1, h4, h2]

/-- The subgroup $n\Lambda$ has index $n^2$ in $\Lambda$. -/
theorem rix_nsmulSub_self {n : ℕ} (hn : 1 ≤ n) (Λ : LatticeC) : rix (nsmulSub n Λ.1) Λ.1 = n ^ 2 := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [← scale_val_eq_nsmulSub hnc]
  exact rix_scale_self hn Λ

/-- If $(\Lambda : \Lambda_3) = k$ then $(\Lambda : n\Lambda_3) = kn^2$. -/
theorem scale_mem_S {n k : ℕ} (hn : 1 ≤ n) (hnc : (n : ℂ) ≠ 0) {Λ Λ3 : LatticeC}
    (h : Λ3 ∈ sublatticesOfIndex k Λ) : LatticeC.scale hnc Λ3 ∈ sublatticesOfIndex (k * n ^ 2) Λ := by
  have h1 : (LatticeC.scale hnc Λ3).1 ≤ (LatticeC.scale hnc Λ).1 := (scale_le_iff hnc _ _).2 h.1
  have h2 := scale_le_self hnc Λ
  refine ⟨h1.trans h2, ?_⟩
  show rix _ _ = _
  rw [← rix_mul h1 h2, rix_scale_self hn Λ]
  have : rix (LatticeC.scale hnc Λ3).1 (LatticeC.scale hnc Λ).1 = k := by
    show rix (Λ3.1.map _) (Λ.1.map _) = k
    rw [rix_map_mul hnc]; exact h.2
  rw [this]

/-- If $(\Lambda : \Lambda'') = kn^2$ and $\Lambda'' \subseteq n\Lambda$, then $(n\Lambda : \Lambda'') = k$. -/
theorem mem_S_of_le_scale {n k : ℕ} (hn : 1 ≤ n) (hnc : (n : ℂ) ≠ 0) {Λ Λ'' : LatticeC}
    (h : Λ'' ∈ sublatticesOfIndex (k * n ^ 2) Λ) (hle : Λ''.1 ≤ (LatticeC.scale hnc Λ).1) :
    Λ'' ∈ sublatticesOfIndex k (LatticeC.scale hnc Λ) := by
  refine ⟨hle, ?_⟩
  have h2 := scale_le_self hnc Λ
  have := rix_mul hle h2
  rw [rix_scale_self hn Λ] at this
  have h3 : rix Λ''.1 Λ.1 = k * n ^ 2 := h.2
  rw [h3] at this
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

/-- If $(\Lambda : \Lambda'') = p^r$ ($r \ge 1$) and $\Lambda'' \not\subseteq p\Lambda$, then $(\Lambda : \Lambda'' + p\Lambda) = p$. -/
theorem rix_sup_nsmulSub {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) {Λ Λ'' : LatticeC}
    (hle : Λ''.1 ≤ Λ.1) (hi : rix Λ''.1 Λ.1 = p ^ r) (hnle : ¬ Λ''.1 ≤ nsmulSub p Λ.1) :
    rix (Λ''.1 ⊔ nsmulSub p Λ.1) Λ.1 = p := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hsq := rix_nsmulSub_self hp1 Λ
  have hnl : nsmulSub p Λ.1 ≤ Λ''.1 ⊔ nsmulSub p Λ.1 := le_sup_right
  have hD0 : Λ''.1 ⊔ nsmulSub p Λ.1 ≤ Λ.1 := sup_le hle nsmulSub_le
  have hdvd := rix_dvd_of_le Λ.1 hnl
  rw [hsq] at hdvd
  obtain ⟨i, hi2, hd⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases i
  · exfalso
    rw [pow_zero, rix_eq_one_iff] at hd
    exact not_le_sup_nsmulSub hp hr hi hd
  · simpa using hd
  · exfalso
    have hm := rix_mul hnl hD0
    rw [hsq, hd] at hm
    have : rix (nsmulSub p Λ.1) (Λ''.1 ⊔ nsmulSub p Λ.1) = 1 := by
      have hp2 : 0 < p ^ 2 := by positivity
      exact Nat.eq_of_mul_eq_mul_right hp2 (by rw [hm]; ring)
    rw [rix_eq_one_iff] at this
    exact hnle (le_sup_left.trans this)

/-- Part (a) of Proposition 4.11. -/
theorem heckeTL_mul_coprime {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m.Coprime n) :
    heckeTL (m * n) = heckeTL m ∘ₗ heckeTL n := by
  classical
  apply hecke_ext
  intro Λ Λ''
  rw [LinearMap.comp_apply, heckeTL_comp_single_apply hm hn, heckeTL_single,
    heckeSum_apply (Nat.mul_pos hm hn)]
  by_cases h : Λ'' ∈ sublatticesOfIndex (m * n) Λ
  · rw [if_pos h]
    obtain ⟨hle, hi⟩ := h
    change rix Λ''.1 Λ.1 = m * n at hi
    obtain ⟨D, ⟨hKD, hDC, hD⟩, huniq⟩ := exists_unique_mid_coprime hle hm hn hmn hi
    have hDlat : IsLatticeC D := isLatticeC_of_relIndex hn Λ D hDC hD
    have hset : {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex n Λ ∧ Λ'' ∈ sublatticesOfIndex m Λ'} =
        {LatticeC.mk' D hDlat} := by
      ext Λ'
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, mem_sublatticesOfIndex]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact Subtype.ext (huniq Λ'.1 ⟨h3, h1, h2⟩)
      · rintro rfl
        refine ⟨⟨hDC, hD⟩, hKD, ?_⟩
        have := rix_mul hKD hDC
        rw [hD, hi] at this
        show rix Λ''.1 D = m
        exact Nat.eq_of_mul_eq_mul_right (by omega) this
    rw [hset, Set.ncard_singleton]
    simp
  · rw [if_neg h]
    have hset : {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex n Λ ∧ Λ'' ∈ sublatticesOfIndex m Λ'} = ∅ := by
      ext Λ'
      simp only [Set.mem_setOf_eq, mem_sublatticesOfIndex, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨h1, h2⟩, h3, h4⟩
      apply h
      refine ⟨h3.trans h1, ?_⟩
      show rix Λ''.1 Λ.1 = m * n
      rw [← rix_mul h3 h1, h4, h2]
    rw [hset]
    simp

/-- Rescaling by $c^{-1}$ after rescaling by $c$ gives back the original lattice. -/
theorem scale_inv_scale {c : ℂ} (hc : c ≠ 0) (Λ : LatticeC) :
    LatticeC.scale (inv_ne_zero hc) (LatticeC.scale hc Λ) = Λ :=
  (LatticeC.scale_scale _ _ _).trans
    ((LatticeC.scale_congr _ one_ne_zero Λ (inv_mul_cancel₀ hc)).trans (LatticeC.scale_one _ _))

/-- Rescaling by $c$ after rescaling by $c^{-1}$ gives back the original lattice. -/
theorem scale_scale_inv {c : ℂ} (hc : c ≠ 0) (Λ : LatticeC) :
    LatticeC.scale hc (LatticeC.scale (inv_ne_zero hc) Λ) = Λ :=
  (LatticeC.scale_scale _ _ _).trans
    ((LatticeC.scale_congr _ one_ne_zero Λ (mul_inv_cancel₀ hc)).trans (LatticeC.scale_one _ _))

/-- Part (b) of Proposition 4.11. -/
theorem heckeTL_pow_succ {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    heckeTL (p ^ r) ∘ₗ heckeTL p =
      heckeTL (p ^ (r + 1)) + (p : ℤ) • (heckeRL p ∘ₗ heckeTL (p ^ (r - 1))) := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have e : s + 1 - 1 = s := by omega
  rw [e]
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hps : 1 ≤ p ^ s := Nat.one_le_pow _ _ hp.pos
  have hps1 : 1 ≤ p ^ (s + 1) := Nat.one_le_pow _ _ hp.pos
  have hps2 : 1 ≤ p ^ (s + 1 + 1) := Nat.one_le_pow _ _ hp.pos
  have hpow : p ^ (s + 1 + 1) = p ^ s * p ^ 2 := by ring
  have hpow' : p ^ (s + 1 + 1) = p ^ (s + 1) * p := by ring
  apply hecke_ext
  intro Λ Λ''
  rw [LinearMap.comp_apply, heckeTL_comp_single_apply hps1 hp1, LinearMap.add_apply, Finsupp.add_apply,
    LinearMap.smul_apply, Finsupp.smul_apply, LinearMap.comp_apply, heckeRL_comp_single_apply hpc hps,
    heckeTL_single, heckeSum_apply hps2, smul_eq_mul]
  by_cases h : Λ'' ∈ sublatticesOfIndex (p ^ (s + 1 + 1)) Λ
  · rw [if_pos h]
    obtain ⟨hle, hi⟩ := h
    change rix Λ''.1 Λ.1 = _ at hi
    have hmemS : Λ'' ∈ sublatticesOfIndex (p ^ s * p ^ 2) Λ := by rw [← hpow]; exact ⟨hle, hi⟩
    by_cases hsc : Λ''.1 ≤ (LatticeC.scale hpc Λ).1
    · -- the case Λ'' ⊆ pΛ
      have hA : {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex p Λ ∧
          Λ'' ∈ sublatticesOfIndex (p ^ (s + 1)) Λ'} = sublatticesOfIndex p Λ := by
        ext Λ1
        simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
        intro h1
        have hpΛ : (LatticeC.scale hpc Λ).1 ≤ Λ1.1 := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := (LatticeC.mem_scale hpc Λ x).1 hx
          have := rix_nsmul_mem h1.2 hy
          simpa using this
        have h3 : Λ''.1 ≤ Λ1.1 := hsc.trans hpΛ
        refine ⟨h3, ?_⟩
        have h12 : rix Λ1.1 Λ.1 = p := h1.2
        have := rix_mul h3 h1.1
        rw [h12, hi, hpow'] at this
        show rix Λ''.1 Λ1.1 = _
        exact Nat.eq_of_mul_eq_mul_right hp.pos this
      have hB : {Λ3 : LatticeC | Λ3 ∈ sublatticesOfIndex (p ^ s) Λ ∧ LatticeC.scale hpc Λ3 = Λ''} =
          {LatticeC.scale (inv_ne_zero hpc) Λ''} := by
        ext Λ3
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨_, rfl⟩
          exact (scale_inv_scale hpc Λ3).symm
        · rintro rfl
          have hsc' : LatticeC.scale hpc (LatticeC.scale (inv_ne_zero hpc) Λ'') = Λ'' :=
            scale_scale_inv hpc Λ''
          refine ⟨?_, hsc'⟩
          rw [← scale_mem_sublatticesOfIndex_iff hpc, hsc']
          exact mem_S_of_le_scale hp.pos hpc hmemS hsc
      rw [hA, hB, ncard_sublatticesOfIndex_prime hp, Set.ncard_singleton]
      push_cast
      ring
    · -- the case Λ'' ⊄ pΛ
      have hnle : ¬ Λ''.1 ≤ nsmulSub p Λ.1 := by
        rwa [← scale_val_eq_nsmulSub hpc]
      have hD := rix_sup_nsmulSub hp (by omega : 1 ≤ s + 1 + 1) hle hi hnle
      have hDle : Λ''.1 ⊔ nsmulSub p Λ.1 ≤ Λ.1 := sup_le hle nsmulSub_le
      have hDlat : IsLatticeC (Λ''.1 ⊔ nsmulSub p Λ.1) := isLatticeC_of_relIndex hp1 Λ _ hDle hD
      have hA : {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex p Λ ∧
          Λ'' ∈ sublatticesOfIndex (p ^ (s + 1)) Λ'} = {LatticeC.mk' _ hDlat} := by
        ext Λ1
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h3, h4⟩
          have hpΛ : nsmulSub p Λ.1 ≤ Λ1.1 := by
            intro x hx
            obtain ⟨y, hy, rfl⟩ := mem_nsmulSub.1 hx
            exact rix_nsmul_mem h1.2 hy
          have hD1 : Λ''.1 ⊔ nsmulSub p Λ.1 ≤ Λ1.1 := sup_le h3 hpΛ
          have h12 : rix Λ1.1 Λ.1 = p := h1.2
          have := rix_mul hD1 h1.1
          rw [h12, hD] at this
          have h5 : rix (Λ''.1 ⊔ nsmulSub p Λ.1) Λ1.1 = 1 := by
            have := this
            nlinarith [hp.pos]
          exact Subtype.ext (le_antisymm (rix_eq_one_iff.1 h5) hD1)
        · rintro rfl
          refine ⟨⟨hDle, hD⟩, le_sup_left, ?_⟩
          have := rix_mul (le_sup_left : Λ''.1 ≤ Λ''.1 ⊔ nsmulSub p Λ.1) hDle
          rw [hD, hi, hpow'] at this
          show rix Λ''.1 (Λ''.1 ⊔ nsmulSub p Λ.1) = _
          exact Nat.eq_of_mul_eq_mul_right hp.pos this
      have hB : {Λ3 : LatticeC | Λ3 ∈ sublatticesOfIndex (p ^ s) Λ ∧ LatticeC.scale hpc Λ3 = Λ''} = ∅ := by
        ext Λ3
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h3, rfl⟩
        exact hsc ((scale_le_iff hpc _ _).2 h3.1)
      rw [hA, hB, Set.ncard_singleton, Set.ncard_empty]
      simp
  · rw [if_neg h, chain_set_eq_empty (m := p ^ (s + 1)) (n := p) (by rwa [← pow_succ])]
    have hB : {Λ3 : LatticeC | Λ3 ∈ sublatticesOfIndex (p ^ s) Λ ∧ LatticeC.scale hpc Λ3 = Λ''} = ∅ := by
      ext Λ3
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h3, rfl⟩
      apply h
      have := scale_mem_S hp1 hpc h3
      rwa [← hpow] at this
    rw [hB]
    simp

/-- Two endomorphisms of the group of lattice divisors that agree on every single lattice are equal (second form). -/
theorem hecke_ext' {f g : Module.End ℤ LatticeDiv}
    (h : ∀ Λ : LatticeC, f (Finsupp.single Λ 1) = g (Finsupp.single Λ 1)) : f = g := by
  apply Finsupp.lhom_ext
  intro Λ a
  rw [← Finsupp.smul_single_one, map_zsmul, map_zsmul, h Λ]

/-- The only sublattice of index $1$ of $\Lambda$ is $\Lambda$ itself. -/
theorem sublatticesOfIndex_one (Λ : LatticeC) : sublatticesOfIndex 1 Λ = {Λ} := by
  ext Λ'
  simp only [mem_sublatticesOfIndex, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (le_antisymm h1 (rix_eq_one_iff.1 h2))
  · rintro rfl
    exact ⟨le_rfl, rix_eq_one_iff.2 le_rfl⟩

/-- The Hecke operator $T_1$ is the identity. -/
theorem heckeTL_one : heckeTL 1 = 1 := by
  apply hecke_ext'
  intro Λ
  rw [heckeTL_single, heckeSum, dif_pos (sublatticesOfIndex_finite le_rfl Λ)]
  simp only [sublatticesOfIndex_one]
  simp

/-- The operator $R_1$ is the identity. -/
theorem heckeRL_one : heckeRL 1 = 1 := by
  apply hecke_ext'
  intro Λ
  have h : ((1 : ℕ) : ℂ) ≠ 0 := by simp
  rw [heckeRL_single h]
  simp [LatticeC.scale_one]

/-- The operators satisfy $R_{ab} = R_a R_b$. -/
theorem heckeRL_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : heckeRL (a * b) = heckeRL a * heckeRL b := by
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have habc : ((a * b : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : a * b ≠ 0)
  apply hecke_ext'
  intro Λ
  rw [Module.End.mul_apply, heckeRL_single hbc, heckeRL_single hac, heckeRL_single habc,
    LatticeC.scale_scale]
  exact congrArg (fun x => Finsupp.single x 1) (LatticeC.scale_congr _ _ _ (by push_cast; rfl))

/-- The operators satisfy $R_{p^i} = R_p^i$. -/
theorem heckeRL_pow {p : ℕ} (hp : 1 ≤ p) (i : ℕ) : heckeRL (p ^ i) = heckeRL p ^ i := by
  induction i with
  | zero => simpa using heckeRL_one
  | succ i ih =>
    rw [pow_succ, heckeRL_mul (Nat.one_le_pow _ _ hp) hp, ih, pow_succ]

/-- The operator $R_d$ commutes with the Hecke operator $T_n$. -/
theorem heckeRL_comm_heckeTL {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    heckeRL d * heckeTL n = heckeTL n * heckeRL d := by
  classical
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  apply hecke_ext
  intro Λ Λ''
  rw [Module.End.mul_apply, Module.End.mul_apply, heckeRL_comp_single_apply hdc hn, heckeRL_single hdc,
    heckeTL_single, heckeSum_apply hn]
  by_cases h : Λ'' ∈ sublatticesOfIndex n (LatticeC.scale hdc Λ)
  · rw [if_pos h]
    have hset : {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex n Λ ∧ LatticeC.scale hdc Λ' = Λ''} =
        {LatticeC.scale (inv_ne_zero hdc) Λ''} := by
      ext Λ'
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨_, rfl⟩
        exact (scale_inv_scale hdc Λ').symm
      · rintro rfl
        have hsc' := scale_scale_inv hdc Λ''
        refine ⟨?_, hsc'⟩
        rw [← scale_mem_sublatticesOfIndex_iff hdc, hsc']
        exact h
    rw [hset, Set.ncard_singleton]
    simp
  · rw [if_neg h]
    have hset : {Λ' : LatticeC | Λ' ∈ sublatticesOfIndex n Λ ∧ LatticeC.scale hdc Λ' = Λ''} = ∅ := by
      ext Λ'
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, rfl⟩
      exact h ((scale_mem_sublatticesOfIndex_iff hdc Λ Λ').2 h1)
    rw [hset]
    simp

/-- The Hecke operators $T_m$ and $T_n$ commute when $m$ and $n$ are coprime. -/
theorem heckeTL_comm_coprime {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m.Coprime n) :
    heckeTL m * heckeTL n = heckeTL n * heckeTL m := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← heckeTL_mul_coprime hm hn h,
    ← heckeTL_mul_coprime hn hm h.symm, mul_comm]

/-- The operators $R_a$ and $R_b$ commute. -/
theorem heckeRL_comm {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : heckeRL a * heckeRL b = heckeRL b * heckeRL a := by
  rw [← heckeRL_mul ha hb, ← heckeRL_mul hb ha, mul_comm]

/-- The generators `T(p)`, `R(p)` of the Hecke algebra. -/
def heckeGens : Set (Module.End ℤ LatticeDiv) :=
  {x | ∃ p : ℕ, p.Prime ∧ (x = heckeTL p ∨ x = heckeRL p)}

/-- The generating set of Hecke operators is pairwise commuting. -/
theorem heckeGens_pairwise : heckeGens.Pairwise Commute := by
  rintro x ⟨p, hp, hx⟩ y ⟨q, hq, hy⟩ _
  have hp1 := hp.one_lt.le
  have hq1 := hq.one_lt.le
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · by_cases hpq : p = q
    · subst hpq; exact Commute.refl _
    · exact heckeTL_comm_coprime hp1 hq1 ((Nat.coprime_primes hp hq).2 hpq)
  · exact (heckeRL_comm_heckeTL hq1 hp1).symm
  · exact heckeRL_comm_heckeTL hp1 hq1
  · exact heckeRL_comm hp1 hq1

/-- Any two elements of the algebra generated by the Hecke operators commute. -/
theorem heckeGens_commute {x y : Module.End ℤ LatticeDiv} (hx : x ∈ Algebra.adjoin ℤ heckeGens)
    (hy : y ∈ Algebra.adjoin ℤ heckeGens) : x * y = y * x := by
  have h1 : ∀ g ∈ heckeGens, Commute g y := by
    intro g hg
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy ?_
    intro c hc
    by_cases hgc : g = c
    · subst hgc; exact Commute.refl _
    · exact heckeGens_pairwise hg hc hgc
  have h2 : Commute y x :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun b hb => (h1 b hb).symm
  exact h2.eq.symm

/-- The operator $T_{p^k}$ lies in the algebra generated by the Hecke operators. -/
theorem heckeTL_prime_pow_mem {p : ℕ} (hp : p.Prime) (k : ℕ) :
    heckeTL (p ^ k) ∈ Algebra.adjoin ℤ heckeGens ∧ heckeTL (p ^ (k + 1)) ∈ Algebra.adjoin ℤ heckeGens := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [pow_zero, heckeTL_one]; exact Subalgebra.one_mem _
    · rw [zero_add, pow_one]; exact Algebra.subset_adjoin (show heckeTL p ∈ heckeGens from ⟨p, hp, Or.inl rfl⟩)
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hb : heckeTL (p ^ (k + 1)) ∘ₗ heckeTL p =
        heckeTL (p ^ (k + 1 + 1)) + (p : ℤ) • (heckeRL p ∘ₗ heckeTL (p ^ k)) := by
      simpa using heckeTL_pow_succ hp (r := k + 1) (by omega)
    have e : heckeTL (p ^ (k + 1 + 1)) = heckeTL (p ^ (k + 1)) * heckeTL p -
        (p : ℤ) • (heckeRL p * heckeTL (p ^ k)) := by
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, hb]; abel
    rw [e]
    refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ ih.2 (Algebra.subset_adjoin (show heckeTL p ∈ heckeGens from ⟨p, hp, Or.inl rfl⟩)))
      (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Algebra.subset_adjoin (show heckeRL p ∈ heckeGens from ⟨p, hp, Or.inr rfl⟩)) ih.1) _)

/-- The operator $T_n$ lies in the algebra generated by the Hecke operators. -/
theorem heckeTL_mem_adjoin {n : ℕ} (hn : 1 ≤ n) : heckeTL n ∈ Algebra.adjoin ℤ heckeGens := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => rw [heckeTL_one]; exact Subalgebra.one_mem _
  | prime_pow p k hp hk => exact (heckeTL_prime_pow_mem hp k).1
  | coprime a b ha hb hab iha ihb =>
    rw [heckeTL_mul_coprime (by omega) (by omega) hab]
    exact Subalgebra.mul_mem _ (iha (by omega)) (ihb (by omega))

/-- The operator $R_n$ lies in the algebra generated by the Hecke operators. -/
theorem heckeRL_mem_adjoin {n : ℕ} (hn : 1 ≤ n) : heckeRL n ∈ Algebra.adjoin ℤ heckeGens := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => rw [heckeRL_one]; exact Subalgebra.one_mem _
  | prime_pow p k hp hk =>
    rw [heckeRL_pow hp.one_lt.le]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (show heckeRL p ∈ heckeGens from ⟨p, hp, Or.inr rfl⟩)) k
  | coprime a b ha hb hab iha ihb =>
    rw [heckeRL_mul (by omega) (by omega)]
    exact Subalgebra.mul_mem _ (iha (by omega)) (ihb (by omega))

/-- **Proposition 4.11** (pdf p. 209): (a) $T(mn) = T(m)\circ T(n)$ for coprime $m$, $n$;
(b) $T(p^r)\circ T(p) = T(p^{r+1}) + p\,R(p)\circ T(p^{r-1})$ for $p$ prime, $r \ge 1$. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.11, pdf p. 209"]
theorem prop_4_11 :
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m.Coprime n → heckeTL (m * n) = heckeTL m ∘ₗ heckeTL n) ∧
    (∀ p r : ℕ, p.Prime → 1 ≤ r →
      heckeTL (p ^ r) ∘ₗ heckeTL p = heckeTL (p ^ (r + 1)) + (p : ℤ) • (heckeRL p ∘ₗ heckeTL (p ^ (r - 1)))) :=
  ⟨fun _ _ hm hn h => heckeTL_mul_coprime hm hn h, fun _ _ hp hr => heckeTL_pow_succ hp hr⟩

/-- The Hecke operators $T_m$ and $T_n$ commute. -/
theorem heckeTL_comm_all {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) : heckeTL m * heckeTL n = heckeTL n * heckeTL m :=
  heckeGens_commute (heckeTL_mem_adjoin hm) (heckeTL_mem_adjoin hn)

/-- The operator $R_d$ commutes with the Hecke operator $T_n$ (second form). -/
theorem heckeRL_comm_heckeTL' {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    heckeTL n * heckeRL d = heckeRL d * heckeTL n :=
  (heckeRL_comm_heckeTL hd hn).symm

/-- A two-step recursion for the operators $T_{p^k}$ at a prime $p$. -/
theorem heckeTL_pow_two_step {p : ℕ} (hp : p.Prime) (k : ℕ) :
    heckeTL (p ^ (k + 2)) = heckeTL (p ^ (k + 1)) * heckeTL p - (p : ℤ) • (heckeRL p * heckeTL (p ^ k)) := by
  have hb : heckeTL (p ^ (k + 1)) ∘ₗ heckeTL p =
      heckeTL (p ^ (k + 1 + 1)) + (p : ℤ) • (heckeRL p ∘ₗ heckeTL (p ^ k)) := by
    simpa using heckeTL_pow_succ hp (r := k + 1) (by omega)
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, hb]
  abel

/-- The product of $T_p$ with $T_{p^b}$ at a prime $p$, expanded in terms of other Hecke operators. -/
theorem heckeTL_mul_pow {p : ℕ} (hp : p.Prime) {b : ℕ} (hb : 1 ≤ b) :
    heckeTL p * heckeTL (p ^ b) = heckeTL (p ^ (b + 1)) + (p : ℤ) • (heckeRL p * heckeTL (p ^ (b - 1))) := by
  have := heckeTL_pow_succ hp hb
  rw [heckeTL_comm_all hp.one_lt.le (Nat.one_le_pow _ _ hp.pos), Module.End.mul_eq_comp, this]
  rfl

/-- The `i`-th term of the formula for the product of Hecke operators at a prime power. -/
noncomputable def hG (p t i : ℕ) : Module.End ℤ LatticeDiv :=
  ((p ^ i : ℕ) : ℤ) • (heckeRL (p ^ i) * heckeTL (p ^ (t - 2 * i)))

/-- An index shift identity for the auxiliary family of operators at a prime $p$. -/
theorem hG_shift {p : ℕ} (hp : p.Prime) (t i : ℕ) :
    hG p (t + 2) (i + 1) = (p : ℤ) • (heckeRL p * hG p t i) := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have e : t + 2 - 2 * (i + 1) = t - 2 * i := by omega
  unfold hG
  rw [e, pow_succ' p i, heckeRL_mul hp1 (Nat.one_le_pow _ _ hp.pos), mul_smul_comm, smul_smul]
  simp only [Nat.cast_mul, mul_assoc]

/-- An index shift identity for partial sums of the auxiliary family of operators at a prime $p$. -/
theorem hG_sum_shift {p : ℕ} (hp : p.Prime) (t n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), hG p (t + 2) i =
      hG p (t + 2) 0 + (p : ℤ) • (heckeRL p * ∑ i ∈ Finset.range n, hG p t i) := by
  rw [Finset.sum_range_succ', add_comm, Finset.mul_sum, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hG_shift hp t i

/-- The product formula for Hecke operators at powers of a prime $p$. -/
theorem hecke_prime_pow_mul {p : ℕ} (hp : p.Prime) :
    ∀ a b : ℕ, a ≤ b → heckeTL (p ^ a) * heckeTL (p ^ b) = ∑ i ∈ Finset.range (a + 1), hG p (a + b) i := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b hab
    rcases a with _ | _ | a
    · simp [hG, heckeTL_one, heckeRL_one]
    · have hb1 : 1 ≤ b := by omega
      rw [pow_one, heckeTL_mul_pow hp hb1]
      simp [Finset.sum_range_succ, hG, heckeRL_pow hp1]
      have e1 : 1 + b = b + 1 := add_comm _ _
      have e2 : b + 1 - 2 = b - 1 := by omega
      rw [e1, e2]
    · have hb1 : 1 ≤ b := by omega
      have hpp : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ hp.pos
      have e1 : heckeTL (p ^ (a + 1 + 1)) =
          heckeTL (p ^ (a + 1)) * heckeTL p - (p : ℤ) • (heckeRL p * heckeTL (p ^ a)) :=
        heckeTL_pow_two_step hp a
      have e2 := heckeTL_mul_pow hp hb1
      have ih1 := ih (a + 1) (by omega) (b + 1) (by omega)
      have ih2 := ih (a + 1) (by omega) (b - 1) (by omega)
      have ih3 := ih a (by omega) b (by omega)
      have h1 : a + 1 + (b + 1) = a + b + 2 := by omega
      have h2 : a + 1 + (b - 1) = a + b := by omega
      have h3 : a + 1 + 1 + b = a + b + 2 := by omega
      rw [h1] at ih1
      rw [h2] at ih2
      rw [h3]
      have hc1 : heckeTL (p ^ (a + 1)) * heckeRL p = heckeRL p * heckeTL (p ^ (a + 1)) :=
        heckeRL_comm_heckeTL' hp1 hpp
      have key : heckeTL (p ^ (a + 1 + 1)) * heckeTL (p ^ b) =
          heckeTL (p ^ (a + 1)) * heckeTL (p ^ (b + 1)) +
            (p : ℤ) • (heckeRL p * (heckeTL (p ^ (a + 1)) * heckeTL (p ^ (b - 1)))) -
            (p : ℤ) • (heckeRL p * (heckeTL (p ^ a) * heckeTL (p ^ b))) := by
        rw [e1, sub_mul, smul_mul_assoc, mul_assoc, mul_assoc, e2, mul_add, mul_smul_comm,
          ← mul_assoc (heckeTL (p ^ (a + 1))) (heckeRL p), hc1, mul_assoc]
      rw [key, ih1, ih2, ih3, hG_sum_shift hp (a + b) (a + 1 + 1), hG_sum_shift hp (a + b) (a + 1)]
      abel

/-- The right-hand side of Corollary 4.12. -/
noncomputable def heckePsi (m n : ℕ) : Module.End ℤ LatticeDiv :=
  ∑ d ∈ (Nat.gcd m n).divisors, (d : ℤ) • (heckeRL d ∘ₗ heckeTL (m * n / d ^ 2))

/-- The auxiliary operator $\Psi(p^a, p^b)$ at powers of a prime $p$ with $a \le b$. -/
theorem heckePsi_pp {p : ℕ} (hp : p.Prime) {a b : ℕ} (hab : a ≤ b) :
    heckePsi (p ^ a) (p ^ b) = ∑ i ∈ Finset.range (a + 1), hG p (a + b) i := by
  unfold heckePsi
  rw [Nat.gcd_eq_left (pow_dvd_pow p hab), Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ a := by simpa [Nat.lt_succ_iff] using hi
  have e : p ^ a * p ^ b / (p ^ i) ^ 2 = p ^ (a + b - 2 * i) := by
    rw [← pow_add, ← pow_mul, mul_comm i 2]
    exact Nat.pow_div (by omega) hp.pos
  simp only [Function.Embedding.coeFn_mk, hG, e]
  rfl

/-- The auxiliary operator $\Psi(1, n)$ equals the Hecke operator $T_n$. -/
theorem heckePsi_one_left {n : ℕ} (hn : 1 ≤ n) : heckePsi 1 n = heckeTL n := by
  unfold heckePsi
  simp [heckeRL_one]
  exact LinearMap.id_comp _

/-- A sum over the divisors of a product of coprime integers factors as a double sum over the divisors of each factor. -/
theorem sum_divisors_coprime_mul {M : Type*} [AddCommMonoid M] {a b : ℕ} (hab : a.Coprime b) (f : ℕ → M) :
    ∑ d ∈ (a * b).divisors, f d = ∑ x ∈ a.divisors, ∑ y ∈ b.divisors, f (x * y) := by
  classical
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image hab.mul_injOn_divisors, Finset.sum_product]

/-- The auxiliary operator $\Psi$ is multiplicative in both arguments for coprime inputs. -/
theorem heckePsi_mul {m1 n1 m2 n2 : ℕ} (hm1 : 1 ≤ m1) (hn1 : 1 ≤ n1) (hm2 : 1 ≤ m2) (hn2 : 1 ≤ n2)
    (hc : (m1 * n1).Coprime (m2 * n2)) :
    heckePsi (m1 * m2) (n1 * n2) = heckePsi m1 n1 * heckePsi m2 n2 := by
  have hn12 : n1.Coprime n2 := (hc.coprime_dvd_left (dvd_mul_left n1 m1)).coprime_dvd_right (dvd_mul_left n2 m2)
  have h_m2n1 : m2.Coprime n1 :=
    ((hc.symm).coprime_dvd_left (dvd_mul_right m2 n2)).coprime_dvd_right (dvd_mul_left n1 m1)
  have h_m1n2 : m1.Coprime n2 :=
    (hc.coprime_dvd_left (dvd_mul_right m1 n1)).coprime_dvd_right (dvd_mul_left n2 m2)
  have hg : Nat.gcd (m1 * m2) (n1 * n2) = Nat.gcd m1 n1 * Nat.gcd m2 n2 := by
    rw [Nat.Coprime.gcd_mul (m1 * m2) hn12, Nat.Coprime.gcd_mul_right_cancel m1 h_m2n1,
      Nat.Coprime.gcd_mul_left_cancel m2 h_m1n2]
  have hcop : (Nat.gcd m1 n1).Coprime (Nat.gcd m2 n2) :=
    (hc.coprime_dvd_left ((Nat.gcd_dvd_left m1 n1).trans (dvd_mul_right m1 n1))).coprime_dvd_right
      ((Nat.gcd_dvd_left m2 n2).trans (dvd_mul_right m2 n2))
  unfold heckePsi
  rw [hg, sum_divisors_coprime_mul hcop, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [Nat.mem_divisors] at hx hy
  have hx1 : x ∣ m1 := hx.1.trans (Nat.gcd_dvd_left _ _)
  have hx2 : x ∣ n1 := hx.1.trans (Nat.gcd_dvd_right _ _)
  have hy1 : y ∣ m2 := hy.1.trans (Nat.gcd_dvd_left _ _)
  have hy2 : y ∣ n2 := hy.1.trans (Nat.gcd_dvd_right _ _)
  have hxpos : 1 ≤ x := Nat.pos_of_dvd_of_pos hx1 hm1
  have hypos : 1 ≤ y := Nat.pos_of_dvd_of_pos hy1 hm2
  have hxA : x ^ 2 ∣ m1 * n1 := by rw [pow_two]; exact mul_dvd_mul hx1 hx2
  have hyB : y ^ 2 ∣ m2 * n2 := by rw [pow_two]; exact mul_dvd_mul hy1 hy2
  have hAB : (m1 * n1 / x ^ 2).Coprime (m2 * n2 / y ^ 2) :=
    (hc.coprime_dvd_left (Nat.div_dvd_of_dvd hxA)).coprime_dvd_right (Nat.div_dvd_of_dvd hyB)
  have hApos : 1 ≤ m1 * n1 / x ^ 2 :=
    Nat.div_pos (Nat.le_of_dvd (by positivity) hxA) (by positivity)
  have hBpos : 1 ≤ m2 * n2 / y ^ 2 :=
    Nat.div_pos (Nat.le_of_dvd (by positivity) hyB) (by positivity)
  have e : m1 * m2 * (n1 * n2) / (x * y) ^ 2 = m1 * n1 / x ^ 2 * (m2 * n2 / y ^ 2) := by
    rw [Nat.div_mul_div_comm hxA hyB, mul_pow]
    congr 1
    ring
  rw [e, heckeTL_mul_coprime hApos hBpos hAB, heckeRL_mul hxpos hypos]
  simp only [← Module.End.mul_eq_comp, Nat.cast_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hc' : heckeTL (m1 * n1 / x ^ 2) * heckeRL y = heckeRL y * heckeTL (m1 * n1 / x ^ 2) :=
    heckeRL_comm_heckeTL' hypos hApos
  rw [mul_assoc (heckeRL x) (heckeTL _), ← mul_assoc (heckeTL (m1 * n1 / x ^ 2)) (heckeRL y), hc',
    mul_assoc (heckeRL y), ← mul_assoc (heckeRL x)]
  rw [mul_comm (y : ℤ)]

/-- The auxiliary operator is symmetric: $\Psi(m, n) = \Psi(n, m)$. -/
theorem heckePsi_comm (m n : ℕ) : heckePsi m n = heckePsi n m := by
  unfold heckePsi
  rw [Nat.gcd_comm, mul_comm]

/-- The product $T_{p^a} T_{p^b}$ at a prime $p$ in terms of the auxiliary operators. -/
theorem heckeTL_pp_mul {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    heckeTL (p ^ a) * heckeTL (p ^ b) = heckePsi (p ^ a) (p ^ b) := by
  rcases le_total a b with h | h
  · rw [hecke_prime_pow_mul hp a b h, heckePsi_pp hp h]
  · rw [heckeTL_comm_all (Nat.one_le_pow _ _ hp.pos) (Nat.one_le_pow _ _ hp.pos),
      hecke_prime_pow_mul hp b a h, heckePsi_comm, heckePsi_pp hp h, add_comm]

/-- The product $T_m T_n$ equals the auxiliary operator $\Psi(m, n)$. -/
theorem heckeTL_mul_eq_psi (m : ℕ) : 1 ≤ m → ∀ n, 1 ≤ n → heckeTL m * heckeTL n = heckePsi m n := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm n hn
  by_cases hm1 : m = 1
  · subst hm1; rw [heckeTL_one, one_mul, heckePsi_one_left hn]
  · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    obtain ⟨a, m', hpm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) p hp.ne_one
    obtain ⟨b, n', hpn', hneq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
    have hp1 := hp.one_lt.le
    have hpa : 1 ≤ p ^ a := Nat.one_le_pow _ _ hp.pos
    have hpb : 1 ≤ p ^ b := Nat.one_le_pow _ _ hp.pos
    have hm'1 : 1 ≤ m' := by
      rcases Nat.eq_zero_or_pos m' with h | h
      · subst h; simp at hmeq; omega
      · exact h
    have hn'1 : 1 ≤ n' := by
      rcases Nat.eq_zero_or_pos n' with h | h
      · subst h; simp at hneq; omega
      · exact h
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; simp at hmeq; subst hmeq; exact absurd hpm hpm'
      · exact h
    have hlt : m' < m := by
      rw [hmeq]
      calc m' = 1 * m' := (one_mul _).symm
        _ < p ^ a * m' := by
          apply Nat.mul_lt_mul_of_pos_right _ hm'1
          calc 1 < p := hp.one_lt
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
    have hcm : (p ^ a).Coprime m' := Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm')
    have hcn : (p ^ b).Coprime n' := Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn')
    have hcop : (p ^ a * p ^ b).Coprime (m' * n') := by
      rw [← pow_add]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm'))
        (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn'))
    have hmain : heckeTL (p ^ a * m') * heckeTL (p ^ b * n') = heckePsi (p ^ a * m') (p ^ b * n') := by
      rw [heckePsi_mul hpa hpb hm'1 hn'1 hcop, ← heckeTL_pp_mul hp, ← ih m' hlt hm'1 n' hn'1,
        heckeTL_mul_coprime hpa hm'1 hcm, heckeTL_mul_coprime hpb hn'1 hcn]
      have c1 := heckeTL_comm_all hm'1 hpb
      simp only [← Module.End.mul_eq_comp, mul_assoc]
      rw [← mul_assoc (heckeTL m') (heckeTL (p ^ b)), c1, mul_assoc]
    rw [hmeq, hneq]
    exact hmain

/-- **Corollary 4.12** (pdf p. 210): $T(m)\circ T(n) = \sum_{d \mid \gcd(m,n)} d\,R(d)\circ T(mn/d^2)$. -/
@[kb "milne2006ec" "Ch. V, Corollary 4.12, pdf p. 210"]
theorem cor_4_12 (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    heckeTL m ∘ₗ heckeTL n = ∑ d ∈ (Nat.gcd m n).divisors, (d : ℤ) • (heckeRL d ∘ₗ heckeTL (m * n / d ^ 2)) :=
  heckeTL_mul_eq_psi m hm n hn

/-- The $\mathbb Z$-subalgebra $H$ of $\mathrm{End}(\mathcal D)$ generated by the $T(p)$ and $R(p)$, $p$ prime. -/
noncomputable def heckeAlgebraL : Subalgebra ℤ (Module.End ℤ LatticeDiv) :=
  Algebra.adjoin ℤ ({x | ∃ p : ℕ, p.Prime ∧ (x = heckeTL p ∨ x = heckeRL p)})

/-- **Corollary 4.13** (pdf p. 210): $H$ is commutative and contains $T(n)$ for all $n \ge 1$. -/
@[kb "milne2006ec" "Ch. V, Corollary 4.13, pdf p. 210"]
theorem cor_4_13 :
    (∀ x ∈ heckeAlgebraL, ∀ y ∈ heckeAlgebraL, x * y = y * x) ∧ ∀ n : ℕ, 1 ≤ n → heckeTL n ∈ heckeAlgebraL :=
  ⟨fun _ hx _ hy => heckeGens_commute hx hy, fun _ hn => heckeTL_mem_adjoin hn⟩

/-! ### Functions on lattices -/

/-- The extension $F(\sum n_\Lambda[\Lambda]) = \sum n_\Lambda F(\Lambda)$ of $F : \mathcal L \to \mathbb C$ to
$\mathcal D$ (pdf p. 210). -/
noncomputable def extendLin (F : LatticeC → ℂ) (x : LatticeDiv) : ℂ := x.sum fun Λ n ↦ (n : ℂ) * F Λ

/-- $T\cdot F$, $(T\cdot F)(\Lambda) = F(T\Lambda)$ for $T : \mathcal D \to \mathcal D$ (pdf p. 210). -/
noncomputable def endSmulFun (T : Module.End ℤ LatticeDiv) (F : LatticeC → ℂ) (Λ : LatticeC) : ℂ :=
  extendLin F (T (Finsupp.single Λ 1))

/-- $F$ is homogeneous of weight $-2k$: $F(\lambda\Lambda) = \lambda^{-2k}F(\Lambda)$. -/
def IsHomogeneous (k : ℕ) (F : LatticeC → ℂ) : Prop :=
  ∀ (c : ℂ) (hc : c ≠ 0) (Λ : LatticeC), F (LatticeC.scale hc Λ) = c ^ (-(2 * k : ℤ)) * F Λ

/-- The linear extension of $F$ to lattice divisors, written as a finite sum over the support. -/
theorem extendLin_eq (F : LatticeC → ℂ) (x : LatticeDiv) :
    extendLin F x = Finsupp.linearCombination ℤ F x := by
  simp [extendLin, Finsupp.linearCombination_apply, zsmul_eq_mul]

/-- The linear extension of $F$ takes a single lattice $\Lambda$ to $F(\Lambda)$. -/
theorem extendLin_single (F : LatticeC → ℂ) (Λ : LatticeC) : extendLin F (Finsupp.single Λ 1) = F Λ := by
  rw [extendLin_eq, Finsupp.linearCombination_single, one_smul]

/-- The linear extension of $F$ is additive. -/
theorem extendLin_add (F : LatticeC → ℂ) (x y : LatticeDiv) :
    extendLin F (x + y) = extendLin F x + extendLin F y := by
  simp only [extendLin_eq, map_add]

/-- The linear extension of $F$ commutes with finite sums. -/
theorem extendLin_sum (F : LatticeC → ℂ) {ι : Type*} (s : Finset ι) (f : ι → LatticeDiv) :
    extendLin F (∑ i ∈ s, f i) = ∑ i ∈ s, extendLin F (f i) := by
  simp only [extendLin_eq, map_sum]

/-- The linear extension of $F$ commutes with multiplication by an integer $a$. -/
theorem extendLin_zsmul (F : LatticeC → ℂ) (a : ℤ) (x : LatticeDiv) :
    extendLin F (a • x) = (a : ℂ) * extendLin F x := by
  simp only [extendLin_eq, map_zsmul, zsmul_eq_mul]

/-- Running text (pdf p. 210): if $F$ is homogeneous of weight $-2k$ then $R(n)\cdot F = n^{-2k}F$. -/
theorem heckeRL_smul_homogeneous {k : ℕ} {F : LatticeC → ℂ} (hF : IsHomogeneous k F) {n : ℕ} (hn : 1 ≤ n) :
    endSmulFun (heckeRL n) F = fun Λ ↦ (n : ℂ) ^ (-(2 * k : ℤ)) * F Λ := by
  have h : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  funext Λ
  rw [endSmulFun, heckeRL_single h, extendLin_single]
  exact hF _ h Λ

/-- The linear extension of the action of an endomorphism $T$ on $F$ is $x \mapsto \operatorname{ext}(F)(T x)$. -/
theorem extendLin_endSmulFun (T : Module.End ℤ LatticeDiv) (F : LatticeC → ℂ) (x : LatticeDiv) :
    extendLin (endSmulFun T F) x = extendLin F (T x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp [extendLin_eq]
  | add f g hf hg => rw [map_add, extendLin_add, extendLin_add, hf, hg]
  | single Λ a =>
    rw [← Finsupp.smul_single_one, map_zsmul, extendLin_zsmul, extendLin_zsmul, extendLin_single]
    rfl

/-- The action on functions of a composite of endomorphisms is the composite of the actions. -/
theorem endSmulFun_comp (T1 T2 : Module.End ℤ LatticeDiv) (F : LatticeC → ℂ) :
    endSmulFun T1 (endSmulFun T2 F) = endSmulFun (T2 ∘ₗ T1) F := by
  funext Λ
  simp only [endSmulFun, LinearMap.comp_apply]
  exact extendLin_endSmulFun T2 F _

/-- The action on functions of a sum of endomorphisms is the sum of the actions. -/
theorem endSmulFun_add (T1 T2 : Module.End ℤ LatticeDiv) (F : LatticeC → ℂ) :
    endSmulFun (T1 + T2) F = endSmulFun T1 F + endSmulFun T2 F := by
  funext Λ
  simp only [endSmulFun, LinearMap.add_apply, extendLin_add, Pi.add_apply]

/-- The action on functions of an integer multiple of an endomorphism is the same multiple of the action. -/
theorem endSmulFun_zsmul (a : ℤ) (T : Module.End ℤ LatticeDiv) (F : LatticeC → ℂ) :
    endSmulFun (a • T) F = fun Λ => (a : ℂ) * endSmulFun T F Λ := by
  funext Λ
  simp only [endSmulFun, LinearMap.smul_apply, extendLin_zsmul]

/-- For $F$ homogeneous of degree $k$, the operator $R_n$ acts on the linear extension of $F$ by multiplication by $n^{-k}$. -/
theorem extendLin_heckeRL {k : ℕ} {F : LatticeC → ℂ} (hF : IsHomogeneous k F) {n : ℕ} (hn : 1 ≤ n)
    (x : LatticeDiv) : extendLin F (heckeRL n x) = (n : ℂ) ^ (-(2 * k : ℤ)) * extendLin F x := by
  have h : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  induction x using Finsupp.induction_linear with
  | zero => simp [extendLin_eq]
  | add f g hf hg => rw [map_add, extendLin_add, extendLin_add, hf, hg, mul_add]
  | single Λ a =>
    rw [← Finsupp.smul_single_one, map_zsmul, extendLin_zsmul, extendLin_zsmul, heckeRL_single h,
      extendLin_single, extendLin_single, hF _ h Λ]
    ring

/-- The action of $T_n$ on $F$ at $\Lambda$ is the sum of $F$ over the sublattices of index $n$ of $\Lambda$. -/
theorem endSmulFun_heckeTL_eq {n : ℕ} (hn : 1 ≤ n) (F : LatticeC → ℂ) (Λ : LatticeC) :
    endSmulFun (heckeTL n) F Λ = ∑ Λ' ∈ (sublatticesOfIndex_finite hn Λ).toFinset, F Λ' := by
  classical
  rw [endSmulFun, heckeTL_single, heckeSum, dif_pos (sublatticesOfIndex_finite hn Λ), extendLin_sum]
  simp only [extendLin_single]

/-- The Hecke operator $T_n$ sends functions homogeneous of degree $k$ to functions homogeneous of degree $k$. -/
theorem heckeTL_homogeneous {k : ℕ} {F : LatticeC → ℂ} (hF : IsHomogeneous k F) {n : ℕ} (hn : 1 ≤ n) :
    IsHomogeneous k (endSmulFun (heckeTL n) F) := by
  classical
  intro c hc Λ
  rw [endSmulFun_heckeTL_eq hn, endSmulFun_heckeTL_eq hn, Finset.mul_sum]
  refine (Finset.sum_nbij' (LatticeC.scale hc) (LatticeC.scale (inv_ne_zero hc)) ?_ ?_ ?_ ?_ ?_).symm
  · intro Λ1 h1
    simp only [Set.Finite.mem_toFinset] at h1 ⊢
    exact (scale_mem_sublatticesOfIndex_iff hc Λ Λ1).2 h1
  · intro Λ' h1
    simp only [Set.Finite.mem_toFinset] at h1 ⊢
    rw [← scale_mem_sublatticesOfIndex_iff hc, scale_scale_inv]
    exact h1
  · intro Λ1 _
    exact scale_inv_scale hc Λ1
  · intro Λ' _
    exact scale_scale_inv hc Λ'
  · intro Λ1 _
    exact (hF c hc Λ1).symm

/-- **Proposition 4.14** (pdf p. 210): if $F$ is homogeneous of weight $-2k$ then so is $T(n)\cdot F$, and
(a) $T(mn)\cdot F = T(m)\cdot T(n)\cdot F$ for coprime $m$, $n$;
(b) $T(p)\cdot T(p^r)\cdot F = T(p^{r+1})\cdot F + p^{1-2k}T(p^{r-1})\cdot F$. -/
@[kb "milne2006ec" "Ch. V, Proposition 4.14, pdf p. 210"]
theorem prop_4_14 {k : ℕ} {F : LatticeC → ℂ} (hF : IsHomogeneous k F) :
    (∀ n : ℕ, 1 ≤ n → IsHomogeneous k (endSmulFun (heckeTL n) F)) ∧
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m.Coprime n →
      endSmulFun (heckeTL (m * n)) F = endSmulFun (heckeTL m) (endSmulFun (heckeTL n) F)) ∧
    (∀ p r : ℕ, p.Prime → 1 ≤ r →
      endSmulFun (heckeTL p) (endSmulFun (heckeTL (p ^ r)) F) =
        endSmulFun (heckeTL (p ^ (r + 1))) F + (p : ℂ) ^ (1 - 2 * k : ℤ) • endSmulFun (heckeTL (p ^ (r - 1))) F) := by
  refine ⟨fun n hn => heckeTL_homogeneous hF hn, ?_, ?_⟩
  · intro m n hm hn hmn
    rw [endSmulFun_comp, ← heckeTL_mul_coprime hn hm hmn.symm, mul_comm]
  · intro p r hp hr
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [endSmulFun_comp, heckeTL_pow_succ hp hr, endSmulFun_add, endSmulFun_zsmul]
    funext Λ
    have h2 : endSmulFun (heckeRL p ∘ₗ heckeTL (p ^ (r - 1))) F Λ =
        (p : ℂ) ^ (-(2 * k : ℤ)) * endSmulFun (heckeTL (p ^ (r - 1))) F Λ := by
      simp only [endSmulFun, LinearMap.comp_apply]
      exact extendLin_heckeRL hF hp1 _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2, Int.cast_natCast]
    congr 1
    rw [sub_eq_add_neg, zpow_add₀ hpc, zpow_one]
    ring

/-- $f : \mathbb H \to \mathbb C$ satisfies (3.1b) for $\mathrm{SL}_2(\mathbb Z)$ in weight $2k$. -/
def IsWeightInvariant (k : ℕ) (f : ℍ → ℂ) : Prop :=
  ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) * f z

/-- The denominator $cz + d$ of an element of $\mathrm{SL}_2(\mathbb Z)$ is nonzero on the upper half plane. -/
theorem sl_denom_ne(γ : SL(2, ℤ)) (z : ℍ) : ((γ 1 0 : ℂ) * z + γ 1 1) ≠ 0 := by
  have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
  simpa [UpperHalfPlane.denom] using this

/-- An element of $\mathrm{SL}_2(\mathbb Z)$ has determinant $ad - bc = 1$ as complex numbers. -/
theorem sl_det (γ : SL(2, ℤ)) : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

/-- The action of $\mathrm{SL}_2(\mathbb Z)$ on the upper half plane, as a Möbius transformation of complex numbers. -/
theorem sl_smul_coe (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- The lattice attached to $\gamma z$ is a rescaling of the lattice attached to $z$ by $(cz + d)^{-1}$. -/
theorem ofH_smul (γ : SL(2, ℤ)) (z : ℍ) :
    LatticeC.ofH (γ • z) = LatticeC.scale (inv_ne_zero (sl_denom_ne γ z)) (LatticeC.ofH z) := by
  refine LatticeC.ext' fun x => ?_
  rw [LatticeC.mem_ofH, LatticeC.mem_scale]
  have hc := sl_denom_ne γ z
  have hdet := sl_det γ
  rw [sl_smul_coe]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨(m * γ 0 0 + n * γ 1 0 : ℤ) * z + (m * γ 0 1 + n * γ 1 1 : ℤ), (LatticeC.mem_ofH _ _).2 ⟨_, _, rfl⟩, ?_⟩
    push_cast
    field_simp
    ring
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, v, rfl⟩ := (LatticeC.mem_ofH _ _).1 hy
    refine ⟨u * γ 1 1 - v * γ 1 0, -u * γ 0 1 + v * γ 0 0, ?_⟩
    push_cast
    field_simp
    linear_combination (u * z + v) * hdet

/-- If $Az + B = A'z + B'$ with integers $A, B, A', B'$ and $z$ in the upper half plane, then $A = A'$ and $B = B'$. -/
theorem coeff_eq_of_zone (z : ℍ) {A B A' B' : ℤ} (h : (A : ℂ) * z + B = A' * z + B') : A = A' ∧ B = B' := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  have hy : (z : ℂ).im ≠ 0 := z.im_ne_zero
  rcases him with him | him
  · have hAA : A = A' := by exact_mod_cast him
    subst hAA
    refine ⟨rfl, ?_⟩
    have : (B : ℝ) = B' := by linarith
    exact_mod_cast this
  · exact absurd him hy

/-- If `Λ(z', 1) = t Λ(z, 1)` then `z' = γ z` and `t = (cz+d)⁻¹` for some `γ ∈ SL(2, ℤ)`. -/
theorem exists_sl_of_ofH_eq_scale {t : ℂ} (ht : t ≠ 0) (z z' : ℍ)
    (h : LatticeC.ofH z' = LatticeC.scale ht (LatticeC.ofH z)) :
    ∃ γ : SL(2, ℤ), z' = γ • z ∧ ((γ 1 0 : ℂ) * z + γ 1 1) * t = 1 := by
  have m1 : (z' : ℂ) ∈ (LatticeC.ofH z').1 := (LatticeC.mem_ofH _ _).2 ⟨1, 0, by simp⟩
  have m2 : (1 : ℂ) ∈ (LatticeC.ofH z').1 := (LatticeC.mem_ofH _ _).2 ⟨0, 1, by simp⟩
  have m3 : t * z ∈ (LatticeC.ofH z').1 := by
    rw [h, LatticeC.mem_scale]; exact ⟨z, (LatticeC.mem_ofH _ _).2 ⟨1, 0, by simp⟩, rfl⟩
  have m4 : t ∈ (LatticeC.ofH z').1 := by
    rw [h, LatticeC.mem_scale]; exact ⟨1, (LatticeC.mem_ofH _ _).2 ⟨0, 1, by simp⟩, by simp⟩
  rw [h, LatticeC.mem_scale] at m1 m2
  obtain ⟨y1, hy1, e1⟩ := m1
  obtain ⟨y2, hy2, e2⟩ := m2
  obtain ⟨p, q, rfl⟩ := (LatticeC.mem_ofH _ _).1 hy1
  obtain ⟨r, s, rfl⟩ := (LatticeC.mem_ofH _ _).1 hy2
  obtain ⟨a, b, e3⟩ := (LatticeC.mem_ofH _ _).1 m3
  obtain ⟨c, d, e4⟩ := (LatticeC.mem_ofH _ _).1 m4
  have h1 : (((1 : ℤ) : ℂ)) * z + ((0 : ℤ) : ℂ) = ((a * p + b * r : ℤ) : ℂ) * z + ((a * q + b * s : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ ht
    linear_combination -e3 - a * e1 - b * e2
  have h2 : (((0 : ℤ) : ℂ)) * z + ((1 : ℤ) : ℂ) = ((c * p + d * r : ℤ) : ℂ) * z + ((c * q + d * s : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ ht
    linear_combination -e4 - c * e1 - d * e2
  obtain ⟨k1, k2⟩ := coeff_eq_of_zone z h1
  obtain ⟨k3, k4⟩ := coeff_eq_of_zone z h2
  have hD : (p * s - q * r) * (a * d - b * c) = 1 := by
    have : (p * s - q * r) * (a * d - b * c)
        = (a * p + b * r) * (c * q + d * s) - (a * q + b * s) * (c * p + d * r) := by ring
    rw [this, ← k1, ← k2, ← k3, ← k4]; norm_num
  have hw : (r : ℂ) * z + s ≠ 0 := by
    intro h0; rw [h0] at e2; simp at e2
  have hz' : (z' : ℂ) * ((r : ℂ) * z + s) = p * z + q := by
    rw [← e1]
    linear_combination ((p : ℂ) * z + q) * e2
  have hpos : 0 < p * s - q * r := by
    have hn : 0 < Complex.normSq ((r : ℂ) * z + s) := Complex.normSq_pos.2 hw
    have hu : ((p : ℂ) * z + q) * (starRingEnd ℂ) ((r : ℂ) * z + s)
        = z' * (Complex.normSq ((r : ℂ) * z + s) : ℂ) := by
      rw [← hz', mul_assoc, Complex.mul_conj]
    have e := congrArg Complex.im hu
    simp [Complex.mul_im, Complex.mul_re] at e
    have key : ((p * s - q * r : ℤ) : ℝ) * z.im = z'.im * Complex.normSq ((r : ℂ) * z + s) := by
      push_cast
      linear_combination e
    have hy := z.im_pos
    have hy' := z'.im_pos
    have : (0 : ℝ) < ((p * s - q * r : ℤ) : ℝ) := by
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_pos hy' hn, mul_nonneg (neg_nonneg.2 hneg) hy.le]
    exact_mod_cast this
  have hD1 : p * s - q * r = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hD with h1 | h1
    · exact h1
    · omega
  have hγ : ∃ γ : SL(2, ℤ), γ 0 0 = p ∧ γ 0 1 = q ∧ γ 1 0 = r ∧ γ 1 1 = s :=
    ⟨⟨!![p, q; r, s], by simp [Matrix.det_fin_two]; linarith⟩, rfl, rfl, rfl, rfl⟩
  obtain ⟨γ, g00, g01, g10, g11⟩ := hγ
  refine ⟨γ, ?_, ?_⟩
  · apply UpperHalfPlane.ext
    rw [sl_smul_coe, g00, g01, g10, g11, eq_div_iff hw]
    exact hz'
  · rw [g10, g11]
    linear_combination e2

/-- A coordinate lemma for the cover of lattices by `c Λ(z, 1)`. -/
theorem exists_scale_ofH (Λ : LatticeC) : ∃ (c : ℂ) (hc : c ≠ 0) (z : ℍ), Λ = LatticeC.scale hc (LatticeC.ofH z) := by
  obtain ⟨L, hL⟩ := Λ.2
  have h1 : L.ω₁ ≠ 0 := L.indep.ne_zero 0
  have h2 : L.ω₂ ≠ 0 := L.indep.ne_zero 1
  have hw : (L.ω₁ / L.ω₂).im ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ : ∃ u : ℝ, L.ω₁ / L.ω₂ = (u : ℂ) :=
      ⟨(L.ω₁ / L.ω₂).re, Complex.ext (by simp) (by simp [h0])⟩
    have hω : L.ω₁ = (u : ℂ) * L.ω₂ := by
      rw [← hu]; field_simp
    have := LinearIndependent.pair_iff.1 L.indep 1 (-u) (by
      simp only [Complex.real_smul]
      rw [hω]; push_cast; ring)
    simp at this
  have hΛ : ∀ x, x ∈ Λ.1 ↔ ∃ m n : ℤ, (m : ℂ) * L.ω₁ + n * L.ω₂ = x := by
    intro x; rw [← hL]; exact PeriodPair.mem_lattice
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have hpos' : 0 < (L.ω₂ / L.ω₁).im := by
      have : L.ω₂ / L.ω₁ = (L.ω₁ / L.ω₂)⁻¹ := (inv_div _ _).symm
      rw [this, Complex.inv_im]
      have : 0 < Complex.normSq (L.ω₁ / L.ω₂) := Complex.normSq_pos.2 (div_ne_zero h1 h2)
      have := neg_pos.2 hneg
      positivity
    refine ⟨L.ω₁, h1, ⟨L.ω₂ / L.ω₁, hpos'⟩, LatticeC.ext' fun x => ?_⟩
    rw [LatticeC.mem_scale, hΛ]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨(n : ℂ) * ((⟨L.ω₂ / L.ω₁, hpos'⟩ : ℍ) : ℂ) + m, (LatticeC.mem_ofH _ _).2 ⟨n, m, rfl⟩, ?_⟩
      simp only [UpperHalfPlane.coe_mk]
      field_simp
      ring
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨m, n, rfl⟩ := (LatticeC.mem_ofH _ _).1 hy
      refine ⟨n, m, ?_⟩
      simp only [UpperHalfPlane.coe_mk]
      field_simp
      ring
  · refine ⟨L.ω₂, h2, ⟨L.ω₁ / L.ω₂, hpos⟩, LatticeC.ext' fun x => ?_⟩
    rw [LatticeC.mem_scale, hΛ]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨(m : ℂ) * ((⟨L.ω₁ / L.ω₂, hpos⟩ : ℍ) : ℂ) + n, (LatticeC.mem_ofH _ _).2 ⟨m, n, rfl⟩, ?_⟩
      simp only [UpperHalfPlane.coe_mk]
      field_simp
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨m, n, rfl⟩ := (LatticeC.mem_ofH _ _).1 hy
      refine ⟨m, n, ?_⟩
      simp only [UpperHalfPlane.coe_mk]
      field_simp

/-- Running text (pdf p. 208): $f(z) = F(\Lambda(z, 1))$ is a one-to-one correspondence between functions $F$ on
lattices homogeneous of weight $-2k$ and functions $f$ on $\mathbb H$ with $f(\gamma z) = (cz+d)^{2k}f(z)$. -/
@[kb "milne2006ec" "Ch. V, §4, lattice functions and functions on ℍ (running text), pdf p. 208"]
theorem lattice_correspondence (k : ℕ) :
    (∀ F : LatticeC → ℂ, IsHomogeneous k F → IsWeightInvariant k (fun z ↦ F (LatticeC.ofH z))) ∧
    ∀ f : ℍ → ℂ, IsWeightInvariant k f → ∃! F : LatticeC → ℂ, IsHomogeneous k F ∧ ∀ z, F (LatticeC.ofH z) = f z := by
  have hz2 : ∀ c : ℂ, c ^ (-(2 * k : ℤ)) = (c ^ (2 * k))⁻¹ := by
    intro c
    rw [show (-(2 * k : ℤ)) = -((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  constructor
  · intro F hF γ z
    show F (LatticeC.ofH (γ • z)) = _ * F (LatticeC.ofH z)
    rw [ofH_smul, hF _ (inv_ne_zero (sl_denom_ne γ z)), hz2, inv_pow, inv_inv]
  · intro f hf
    have hwd : ∀ (c c' : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (z z' : ℍ),
        LatticeC.scale hc (LatticeC.ofH z) = LatticeC.scale hc' (LatticeC.ofH z') →
        c ^ (-(2 * k : ℤ)) * f z = c' ^ (-(2 * k : ℤ)) * f z' := by
      intro c c' hc hc' z z' h
      have ht : c'⁻¹ * c ≠ 0 := mul_ne_zero (inv_ne_zero hc') hc
      have E : LatticeC.ofH z' = LatticeC.scale ht (LatticeC.ofH z) := by
        calc LatticeC.ofH z' = LatticeC.scale one_ne_zero (LatticeC.ofH z') :=
              (LatticeC.scale_one _ _).symm
          _ = LatticeC.scale (mul_ne_zero (inv_ne_zero hc') hc') (LatticeC.ofH z') :=
              LatticeC.scale_congr _ _ _ (by field_simp)
          _ = LatticeC.scale (inv_ne_zero hc') (LatticeC.scale hc' (LatticeC.ofH z')) :=
              (LatticeC.scale_scale _ _ _).symm
          _ = LatticeC.scale (inv_ne_zero hc') (LatticeC.scale hc (LatticeC.ofH z)) := by rw [h]
          _ = LatticeC.scale ht (LatticeC.ofH z) := LatticeC.scale_scale _ _ _
      obtain ⟨γ, hγ, hden⟩ := exists_sl_of_ofH_eq_scale ht z z' E
      have hw : (γ 1 0 : ℂ) * z + γ 1 1 = c' / c := by
        rw [eq_div_iff hc]
        field_simp at hden ⊢
        linear_combination hden
      rw [hγ, hf γ z, hw, hz2, hz2]
      field_simp
      rw [div_pow]
      field_simp
    have hex : ∀ Λ : LatticeC, ∃ v : ℂ, ∀ (c : ℂ) (hc : c ≠ 0) (z : ℍ),
        Λ = LatticeC.scale hc (LatticeC.ofH z) → v = c ^ (-(2 * k : ℤ)) * f z := by
      intro Λ
      obtain ⟨c, hc, z, hz⟩ := exists_scale_ofH Λ
      exact ⟨c ^ (-(2 * k : ℤ)) * f z, fun c' hc' z' h' => hwd c c' hc hc' z z' (hz.symm.trans h')⟩
    choose F hF using hex
    refine ⟨F, ⟨?_, ?_⟩, ?_⟩
    · intro d hd Λ
      obtain ⟨c, hc, z, hz⟩ := exists_scale_ofH Λ
      rw [hF Λ c hc z hz, hF (LatticeC.scale hd Λ) (d * c) (mul_ne_zero hd hc) z
        (by rw [hz, LatticeC.scale_scale]), mul_zpow]
      ring
    · intro z
      have := hF (LatticeC.ofH z) 1 one_ne_zero z (LatticeC.scale_one _ _).symm
      simpa using this
    · rintro F' ⟨h1, h2⟩
      funext Λ
      obtain ⟨c, hc, z, hz⟩ := exists_scale_ofH Λ
      rw [hF Λ c hc z hz, hz, h1 c hc (LatticeC.ofH z), h2 z]

/-- The function $F$ on lattices attached to a weight-$2k$ function $f$ on $\mathbb H$ (the unique one of
`lattice_correspondence` when $f$ satisfies (3.1b); junk otherwise). -/
noncomputable def latticeFun (k : ℕ) (f : ℍ → ℂ) : LatticeC → ℂ := by
  classical
  exact if h : ∃ F : LatticeC → ℂ, IsHomogeneous k F ∧ ∀ z, F (LatticeC.ofH z) = f z then h.choose else 0

/-- The Hecke operator on modular forms of level one (definition in prose, pdf p. 210):
$(T(n)f)(z) = n^{2k-1}(T(n)\cdot F)(\Lambda(z, 1))$, $F$ the function on lattices attached to $f$. -/
@[kb "milne2006ec" "Ch. V, §4, the Hecke operator T(n) on modular forms (definition in prose), pdf p. 210"]
noncomputable def heckeOpLevelOne (k n : ℕ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  (n : ℂ) ^ (2 * k - 1) * endSmulFun (heckeTL n) (latticeFun k f) (LatticeC.ofH z)

end NumberFieldKB.MilneEC.V
