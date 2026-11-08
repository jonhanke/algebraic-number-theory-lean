import NumberFieldKB.WeilBNT.PFieldLattices
import NumberFieldKB.WeilBNT.PFieldExtensions

/-!
# Weil, *Basic Number Theory*, II.§2: closed $R$-modules, lattices of extension rings, Cor. 1 and 3 of Thm. 2

$K$ is a $p$-field (commutative or not) with maximal compact subring $R$ (`pR hK`), maximal ideal $P$ (`pP hK`),
module $q$ (`pq hK`) and a prime element $\pi$; $V$ is a left vector space of finite dimension $n$ over $K$ with its
natural topology. An *$R$-module in $V$* is an additive subgroup $M$ with $RM\subseteq M$ (`IsRModule`), a *lattice*
a compact open one (`IsKLattice`). Indices are 0-based (Weil's $v_1,\dots,v_n$ are `b 0, …, b (n-1)`).

* **`weil_II_2_text_p28_stability`**: text p. 28. A closed subgroup $X$ of $V$ is an $R$-module if and only if
  $\pi X\subseteq X$ and $aX\subseteq X$ for every $a$ in a full set $A$ of representatives of $R/P$ in $R$.
  `weil_II_2_text_p28_stability_nat`: if $A$ consists of integers $m\cdot1$ (e.g. $q=p$, $A=\{0,\dots,p-1\}$), $X$ is
  an $R$-module if and only if $\pi X\subseteq X$.
* **`weil_II_2_thm1_flag`**: Thm. 1, second assertion. For a lattice $L$ and a flag $W_0=V\supset W_1\supset\cdots$
  with $\dim W_i=n-i$, the basis with $L=\sum Rv_i$ may be chosen with $W_i$ spanned by $v_i,\dots,v_{n-1}$.
* **`weil_II_2_text_p30`**: text p. 30. For a commutative $p$-field $K$ and a $p$-field $K'\supset K$ of finite
  dimension over $K$, the maximal compact subring $R'$ is a $K$-lattice in $K'$, so $R'=\sum_jRy_j$ for a basis
  $(y_j)$ of $K'$ over $K$, and the matrix $(a_{ij})$ of left multiplication by any $y\in R'$ ($yy_i=\sum_ja_{ij}y_j$)
  has its entries in $R$.
* **`weil_II_2_cor1_thm2`**: Cor. 1 of Thm. 2. For a lattice $L$ and an $R$-module $M$ in $V$ there are a basis
  $(v_i)$ and integers $0\le r\le s\le n$, $\nu_i$, with $L=\sum Rv_i$ and
  $M=\sum_{i<r}\pi^{\nu_i}Rv_i+\sum_{r\le i<s}Kv_i$.
* **`weil_II_2_cor3_thm2`**: Cor. 3 of Thm. 2. In Cor. 1 the integers $r$, $s$ and the family
  $(\nu_i)_{i<r}$ up to order (as a multiset) depend only on $L$ and $M$.
-/

open Topology Filter
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

section General

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}
  {V : Type*} [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul K V] [T2Space V] [FiniteDimensional K V]

/-- **Text p. 28.** A closed subgroup $X$ of $V$ is an $R$-module if and only if $\pi X\subseteq X$ and
$aX\subseteq X$ for all $a$ in a full set $A$ of representatives of $R/P$ (Cor. 2 of I.§4 Thm. 6). -/
@[kb "weil1973bnt" "Ch. II, §2, text p. 28 (a closed subgroup is an R-module iff stable under π and representatives)"]
theorem weil_II_2_text_p28_stability (hK : IsPField K p) {π : K} (hπ0 : π ≠ 0)
    (hπ : modK K π = (pq hK : ℝ≥0)⁻¹) {A : Set K} (hA : A ⊆ pR hK)
    (hrep : ∀ x ∈ pR hK, ∃! a, a ∈ A ∧ modK K (x - a) ≤ (pq hK : ℝ≥0)⁻¹)
    {X : AddSubgroup V} (hX : IsClosed (X : Set V)) :
    IsRModule hK X ↔ (∀ x ∈ X, π • x ∈ X) ∧ ∀ a ∈ A, ∀ x ∈ X, a • x ∈ X := by
  constructor
  · intro hM
    have hπR : π ∈ pR hK := by
      rw [mem_pR, hπ]
      exact inv_le_one_of_one_le₀ (one_lt_pq_norms hK).le
    exact ⟨fun x hx => hM π hπR x hx, fun a ha x hx => hM a (hA ha) x hx⟩
  · rintro ⟨h1, h2⟩ r hr x hx
    have hpow : ∀ i : ℕ, π ^ i • x ∈ X := by
      intro i
      induction i with
      | zero => simpa using hx
      | succ i ih => rw [pow_succ', mul_smul]; exact h1 _ ih
    obtain ⟨a, ha, hsum⟩ := (weil_I_4_cor2_thm6 hK hπ0 (n := 1) le_rfl (by simpa using hπ) hA
      (by simpa using hrep) 0 (x := r) (by simpa using mem_pR.1 hr)).exists
    have hsum' : HasSum (fun i : ℕ => (a i * π ^ i) • x) (r • x) := by
      have := hsum.smul_const x
      simpa using this
    refine hX.mem_of_tendsto hsum'.tendsto_sum_nat (Filter.Eventually.of_forall fun n => ?_)
    refine X.sum_mem fun i _ => ?_
    rw [mul_smul]
    exact h2 _ (ha i) _ (hpow i)

/-- **Text p. 28**, the case of integer representatives (e.g. $q=p$ and $A=\{0,1,\dots,p-1\}$): a closed subgroup
$X$ is an $R$-module if and only if $\pi X\subseteq X$. -/
@[kb "weil1973bnt" "Ch. II, §2, text p. 28 (integer representatives: R-module iff πX ⊆ X)"]
theorem weil_II_2_text_p28_stability_nat (hK : IsPField K p) {π : K} (hπ0 : π ≠ 0)
    (hπ : modK K π = (pq hK : ℝ≥0)⁻¹) {A : Set K} (hA : A ⊆ pR hK)
    (hrep : ∀ x ∈ pR hK, ∃! a, a ∈ A ∧ modK K (x - a) ≤ (pq hK : ℝ≥0)⁻¹)
    (hAnat : A ⊆ Set.range (Nat.cast : ℕ → K))
    {X : AddSubgroup V} (hX : IsClosed (X : Set V)) :
    IsRModule hK X ↔ ∀ x ∈ X, π • x ∈ X := by
  rw [weil_II_2_text_p28_stability hK hπ0 hπ hA hrep hX]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro a ha x hx
  obtain ⟨m, rfl⟩ := hAnat ha
  rw [Nat.cast_smul_eq_nsmul K]
  exact X.nsmul_mem hx m

/-- **Thm. 1**, second assertion: the basis may be adapted to a flag (0-based: Weil's $W_{i+1}$ is `W i`). -/
@[kb "weil1973bnt" "Ch. II, §2, Thm. 1 (adapted to a flag)"]
theorem weil_II_2_thm1_flag (hK : IsPField K p) {L : AddSubgroup V} (hL : IsKLattice hK L)
    (W : Fin (Module.finrank K V) → Submodule K V) (hW0 : ∀ h : 0 < Module.finrank K V, W ⟨0, h⟩ = ⊤)
    (hWmono : ∀ i j : Fin (Module.finrank K V), i ≤ j → W j ≤ W i)
    (hWdim : ∀ i : Fin (Module.finrank K V), Module.finrank K (W i) = Module.finrank K V - i) :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      (L : Set V) = {w | ∃ c : Fin (Module.finrank K V) → K, (∀ i, c i ∈ pR hK) ∧ w = ∑ i, c i • b i} ∧
      ∀ i, W i = Submodule.span K (b '' {j | i ≤ j}) := by
  have hM := hL.1
  have hMo := hL.2.2
  have hN := (isKNorm_latticeNorm_iff hK hM hMo).2 hL
  obtain ⟨b, hb, hW⟩ := weil_II_1_prop3_flag hK hN W hW0 hWmono hWdim
  have hpos : ∀ i, 0 < latticeNorm K L (b i) := fun i =>
    pos_iff_ne_zero.2 fun h => b.ne_zero i ((hN.eq_zero_iff _).1 h)
  choose y hy0 hyv hy using fun i => exists_attained hK hMo (hpos i)
  obtain ⟨b2, hb2⟩ := exists_rescaled_basis b y hy0
  have hsup2 : ∀ c : Fin (Module.finrank K V) → K, latticeNorm K L (∑ i, c i • b2 i) =
      Finset.univ.sup fun i => latticeNorm K L (c i • b2 i) := by
    simp only [hb2]; exact sup_rescale y hb
  have hNb2 : ∀ i, latticeNorm K L (b2 i) = 1 := by
    intro i
    rw [hb2 i, latticeNorm_smul hK hM hMo, hy i]
    exact mul_inv_cancel₀ (modK_pos_iff.2 (hy0 i)).ne'
  refine ⟨b2, ?_, fun i => ?_⟩
  · ext w
    constructor
    · intro hw
      refine ⟨fun i => b2.repr w i, fun i => ?_, (b2.sum_repr w).symm⟩
      have h1 : ∑ i, b2.repr w i • b2 i ∈ L := by rw [b2.sum_repr]; exact hw
      have := (sum_mem_iff_forall hK hM hMo hsup2 (fun i => b2.repr w i)).1 h1 i
      rw [hNb2, mul_one] at this
      exact this
    · rintro ⟨c, hc, rfl⟩
      exact (sum_mem_iff_forall hK hM hMo hsup2 c).2 fun i => by rw [hNb2, mul_one]; exact hc i
  · rw [hW i]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      have : b j = (y j)⁻¹ • b2 j := by
        rw [hb2, smul_smul, inv_mul_cancel₀ (hy0 j), one_smul]
      rw [SetLike.mem_coe, this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, hb2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

/-- The shape of Cor. 1 of Thm. 2: $L=\sum Rv_i$ and $M=\sum_{i<r}\pi^{\nu_i}Rv_i+\sum_{r\le i<s}Kv_i$. -/
def IsCor1Basis (hK : IsPField K p) (π : K) (L M : AddSubgroup V)
    (b : Module.Basis (Fin (Module.finrank K V)) K V) (r s : ℕ) (ν : Fin (Module.finrank K V) → ℤ) : Prop :=
  r ≤ s ∧ s ≤ Module.finrank K V ∧
    (L : Set V) = {w | ∃ c : Fin (Module.finrank K V) → K, (∀ i, c i ∈ pR hK) ∧ w = ∑ i, c i • b i} ∧
    (M : Set V) = {w | ∃ c : Fin (Module.finrank K V) → K, (∀ i : Fin (Module.finrank K V), (i : ℕ) < r → c i ∈ pR hK) ∧
      (∀ i : Fin (Module.finrank K V), s ≤ (i : ℕ) → c i = 0) ∧
      w = ∑ i : Fin (Module.finrank K V), (if (i : ℕ) < r then c i * π ^ ν i else c i) • b i}

section Cor1Aux

/-- A sum over `Fin n` of a function supported on the first `r` indices. -/
theorem sum_fin_lt {M' : Type*} [AddCommMonoid M'] {n r : ℕ} (hr : r ≤ n) (H : Fin r → M') :
    ∑ i : Fin n, (if h : (i : ℕ) < r then H ⟨i, h⟩ else 0) = ∑ k : Fin r, H k := by
  let H' : ℕ → M' := fun i => if h : i < r then H ⟨i, h⟩ else 0
  have h1 : ∑ i : Fin n, (if h : (i : ℕ) < r then H ⟨i, h⟩ else 0) = ∑ i ∈ Finset.range n, H' i :=
    Fin.sum_univ_eq_sum_range H' n
  have h2 : ∑ k : Fin r, H k = ∑ i ∈ Finset.range r, H' i := by
    rw [← Fin.sum_univ_eq_sum_range H' r]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [H', k.2]
  rw [h1, h2]
  refine (Finset.sum_subset (Finset.range_subset_range.2 hr) ?_).symm
  intro i _ hi
  simp only [Finset.mem_range, not_lt] at hi
  simp [H', not_lt.2 hi]

/-- Splitting a sum over `Fin n` into the first `r` indices and the rest. -/
theorem sum_split {M' : Type*} [AddCommMonoid M'] {n r : ℕ} (hr : r ≤ n) (G : Fin n → M') :
    ∑ i, G i = ∑ k : Fin r, G (Fin.castLE hr k) + ∑ i : Fin n, (if r ≤ (i : ℕ) then G i else 0) := by
  have h1 : ∀ i : Fin n, G i = (if h : (i : ℕ) < r then G (Fin.castLE hr ⟨i, h⟩) else 0) +
      (if r ≤ (i : ℕ) then G i else 0) := by
    intro i
    by_cases h : (i : ℕ) < r
    · have : Fin.castLE hr ⟨i, h⟩ = i := Fin.ext rfl
      simp [h, not_le.2 h, this]
    · simp [h, not_lt.1 h]
  conv_lhs => rw [Finset.sum_congr rfl fun i _ => h1 i]
  rw [Finset.sum_add_distrib, sum_fin_lt hr (fun k => G (Fin.castLE hr k))]

/-- Thm. 2 with the dimension given as a numeral. -/
theorem thm2_fin (hK : IsPField K p) {L L' : AddSubgroup V} (hL : IsKLattice hK L)
    (hL' : IsKLattice hK L') {π : K} (hπ0 : π ≠ 0) (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K))
    {m : ℕ} (hm : Module.finrank K V = m) :
    ∃ (b : Module.Basis (Fin m) K V) (ν : Fin m → ℤ),
      (L : Set V) = {w | ∃ c : Fin m → K, (∀ i, c i ∈ pR hK) ∧ w = ∑ i, c i • b i} ∧
      (L' : Set V) = {w | ∃ c : Fin m → K, (∀ i, c i ∈ pR hK) ∧ w = ∑ i, (c i * π ^ ν i) • b i} := by
  subst hm
  exact weil_II_2_thm2 hK hL hL' hπ0 hπ

/-- The span of the first `r` vectors of a basis. -/
def lowSpan {n : ℕ} (a : Module.Basis (Fin n) K V) (r : ℕ) : Submodule K V :=
  Submodule.span K (a '' {i | (i : ℕ) < r})

/-- Membership in the span of a set of basis vectors, in coordinates. -/
theorem mem_span_image_iff {n : ℕ} (a : Module.Basis (Fin n) K V) (P : Fin n → Prop) (w : V) :
    w ∈ Submodule.span K (a '' {i | P i}) ↔ ∀ j, ¬ P j → a.repr w j = 0 := by
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra h0
    exact hj (h (by simpa [Finsupp.mem_support_iff] using h0))
  · intro h j hj
    by_contra hPj
    exact (Finsupp.mem_support_iff.1 hj) (h j hPj)

theorem mem_lowSpan_iff {n : ℕ} (a : Module.Basis (Fin n) K V) (r : ℕ) (w : V) :
    w ∈ lowSpan a r ↔ ∀ j : Fin n, r ≤ (j : ℕ) → a.repr w j = 0 := by
  unfold lowSpan
  rw [show a '' {i : Fin n | (i : ℕ) < r} = a '' {i | (fun i : Fin n => (i : ℕ) < r) i} from rfl,
    mem_span_image_iff]
  simp only [not_lt]

theorem finrank_lowSpan {n : ℕ} (a : Module.Basis (Fin n) K V) {r : ℕ} (hr : r ≤ n) :
    Module.finrank K (lowSpan a r) = r := by
  have h1 : a '' {i | (i : ℕ) < r} = Set.range (fun k : Fin r => a (Fin.castLE hr k)) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨Fin.castLE hr k, k.2, rfl⟩
  have hli : LinearIndependent K (fun k : Fin r => a (Fin.castLE hr k)) :=
    a.linearIndependent.comp _ (Fin.castLE_injective hr)
  unfold lowSpan
  rw [h1, finrank_span_eq_card hli, Fintype.card_fin]

/-- The largest subspace contained in an additive subgroup exists. -/
theorem exists_maximal_subspace (M : AddSubgroup V) :
    ∃ U : Submodule K V, (U : Set V) ⊆ M ∧ ∀ U' : Submodule K V, (U' : Set V) ⊆ M → U' ≤ U := by
  have hne : ∃ U : Submodule K V, (U : Set V) ⊆ M := by
    refine ⟨⊥, fun x hx => ?_⟩
    rw [SetLike.mem_coe, Submodule.mem_bot] at hx
    subst hx
    exact M.zero_mem
  obtain ⟨U, hU, hmax⟩ := (wellFounded_gt (α := Submodule K V)).has_min {U | (U : Set V) ⊆ M} hne
  refine ⟨U, hU, fun U' hU' => ?_⟩
  have hsup : ((U ⊔ U' : Submodule K V) : Set V) ⊆ M := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    exact M.add_mem (hU ha) (hU' hb)
  by_contra hle
  exact hmax (U ⊔ U') hsup (lt_of_le_of_ne le_sup_left fun h => hle (h ▸ le_sup_right))

/-- Rescaling the basis vectors by nonzero scalars does not change the spans of subsets. -/
theorem span_rescale {ι : Type*} (b b2 : ι → V) (y : ι → K) (hy0 : ∀ i, y i ≠ 0)
    (hb2 : ∀ i, b2 i = y i • b i) (S : Set ι) :
    Submodule.span K (b2 '' S) = Submodule.span K (b '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, hb2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have : b j = (y j)⁻¹ • b2 j := by
      rw [hb2, smul_smul, inv_mul_cancel₀ (hy0 j), one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

/-- Thm. 1, adapted to a decreasing sequence of subspaces (the generalization of the flag version). -/
theorem exists_lattice_basis_chain (hK : IsPField K p) {L : AddSubgroup V} (hL : IsKLattice hK L)
    (Wt : ℕ → Submodule K V) (hWt : Antitone Wt) :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      (L : Set V) = {w | ∃ c : Fin (Module.finrank K V) → K, (∀ i, c i ∈ pR hK) ∧ w = ∑ i, c i • b i} ∧
      ∀ i, Wt i = Submodule.span K
        (b '' {j | Module.finrank K V - Module.finrank K (Wt i) ≤ (j : ℕ)}) := by
  have hM := hL.1
  have hMo := hL.2.2
  have hN := (isKNorm_latticeNorm_iff hK hM hMo).2 hL
  obtain ⟨b0, hO, hspan, hW⟩ := exists_orth_seq hK (Module.finrank K V) V rfl (latticeNorm K L) hN Wt hWt
  obtain ⟨b, hB⟩ := exists_basis_of_orthSeq rfl hspan
  have hb : ∀ c : Fin (Module.finrank K V) → K, latticeNorm K L (∑ i, c i • b i) =
      Finset.univ.sup fun i => latticeNorm K L (c i • b i) := fun c => by
    simpa [hB] using fin_orth hO c
  have hpos : ∀ i, 0 < latticeNorm K L (b i) := fun i =>
    pos_iff_ne_zero.2 fun h => b.ne_zero i ((hN.eq_zero_iff _).1 h)
  choose y hy0 hyv hy using fun i => exists_attained hK hMo (hpos i)
  obtain ⟨b2, hb2⟩ := exists_rescaled_basis b y hy0
  have hsup2 : ∀ c : Fin (Module.finrank K V) → K, latticeNorm K L (∑ i, c i • b2 i) =
      Finset.univ.sup fun i => latticeNorm K L (c i • b2 i) := by
    simp only [hb2]; exact sup_rescale y hb
  have hNb2 : ∀ i, latticeNorm K L (b2 i) = 1 := by
    intro i
    rw [hb2 i, latticeNorm_smul hK hM hMo, hy i]
    exact mul_inv_cancel₀ (modK_pos_iff.2 (hy0 i)).ne'
  refine ⟨b2, ?_, fun i => ?_⟩
  · ext w
    constructor
    · intro hw
      refine ⟨fun i => b2.repr w i, fun i => ?_, (b2.sum_repr w).symm⟩
      have h1 : ∑ i, b2.repr w i • b2 i ∈ L := by rw [b2.sum_repr]; exact hw
      have := (sum_mem_iff_forall hK hM hMo hsup2 (fun i => b2.repr w i)).1 h1 i
      rw [hNb2, mul_one] at this
      exact this
    · rintro ⟨c, hc, rfl⟩
      exact (sum_mem_iff_forall hK hM hMo hsup2 c).2 fun i => by rw [hNb2, mul_one]; exact hc i
  · rw [span_rescale b b2 y hy0 hb2]
    refine (hW i).trans ?_
    have hset : b '' {j | Module.finrank K V - Module.finrank K (Wt i) ≤ (j : ℕ)} =
        b0 '' Set.Ico (Module.finrank K V - Module.finrank K (Wt i)) (Module.finrank K V) := by
      ext z
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, ⟨hj, j.2⟩, (hB j).symm⟩
      · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
        exact ⟨⟨j, h2⟩, h1, hB _⟩
    rw [hset]

/-- A rotation of `Fin n` taking the last `s` indices to the first `s`... (shifting by `n - s`). -/
theorem exists_rot {n s : ℕ} (hs : s ≤ n) :
    ∃ τ : Fin n ≃ Fin n, ∀ i : Fin n,
      ((τ i : Fin n) : ℕ) = if (i : ℕ) < s then (i : ℕ) + (n - s) else (i : ℕ) - s := by
  let f : Fin n → Fin n := fun i =>
    ⟨if (i : ℕ) < s then (i : ℕ) + (n - s) else (i : ℕ) - s, by
      have := i.2
      split_ifs <;> omega⟩
  have hinj : Function.Injective f := by
    intro i j h
    have h' : (if (i : ℕ) < s then (i : ℕ) + (n - s) else (i : ℕ) - s) =
        (if (j : ℕ) < s then (j : ℕ) + (n - s) else (j : ℕ) - s) := congrArg Fin.val h
    have := i.2
    have := j.2
    apply Fin.ext
    split_ifs at h' <;> omega
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => rfl⟩

end Cor1Aux

section Cor1Core

/-- The core of Cor. 1: given a basis `a` adapted to `L`, with `M` described by coordinates. -/
theorem cor1_core (hK : IsPField K p) {L M : AddSubgroup V} (hL : IsKLattice hK L)
    (hM : IsRModule hK M) {π : K} (hπ0 : π ≠ 0) (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K))
    (a : Module.Basis (Fin (Module.finrank K V)) K V) {r s : ℕ} (hrs : r ≤ s)
    (hsn : s ≤ Module.finrank K V)
    (hLa : (L : Set V) = {w | ∃ c : Fin (Module.finrank K V) → K, (∀ i, c i ∈ pR hK) ∧
      w = ∑ i, c i • a i})
    (hM1 : ∀ w ∈ M, ∀ j : Fin (Module.finrank K V), s ≤ (j : ℕ) → a.repr w j = 0)
    (hM2 : ∀ w : V, (∀ j : Fin (Module.finrank K V), ((j : ℕ) < r ∨ s ≤ (j : ℕ)) → a.repr w j = 0) →
      w ∈ M)
    (hM3 : ∀ U : Submodule K V, (U : Set V) ⊆ M → ∀ u ∈ U, ∀ j : Fin (Module.finrank K V),
      (j : ℕ) < r → a.repr u j = 0)
    (hMo : IsOpen {x : lowSpan a r | (x : V) ∈ M}) :
    ∃ (b : Module.Basis (Fin (Module.finrank K V)) K V) (ν : Fin (Module.finrank K V) → ℤ),
      IsCor1Basis hK π L M b r s ν := by
  have hr : r ≤ Module.finrank K V := hrs.trans hsn
  set W'' := lowSpan a r with hW''
  have haL : ∀ i, a i ∈ L := by
    intro i
    have : a i ∈ (L : Set V) := by
      rw [hLa]
      refine ⟨Pi.single i 1, fun k => ?_, by simp⟩
      by_cases h : k = i
      · subst h; simp
      · simp [h]
    exact this
  have haW : ∀ k : Fin (Module.finrank K V), (k : ℕ) < r → a k ∈ W'' :=
    fun k hk => Submodule.subset_span ⟨k, hk, rfl⟩
  -- the lattices in `W''`
  have hLl : IsKLattice hK (L.comap W''.subtype.toAddMonoidHom) := weil_II_2_text_p28_inf hK hL W''
  have hMl : IsKLattice hK (M.comap W''.subtype.toAddMonoidHom) := by
    have hM' : IsRModule hK (M.comap W''.subtype.toAddMonoidHom) := by
      intro r hr m hm
      exact hM r hr _ hm
    refine (weil_II_2_cor1_prop6 (V := W'') hK hM' hMo).2 ?_
    intro U hU
    have hU' : ((U.map W''.subtype : Submodule K V) : Set V) ⊆ M := by
      rintro _ ⟨u, hu, rfl⟩
      exact hU hu
    rw [Submodule.eq_bot_iff]
    intro u hu
    apply Subtype.ext
    apply a.repr.injective
    ext j
    by_cases hj : (j : ℕ) < r
    · simpa using hM3 _ hU' _ ⟨u, hu, rfl⟩ j hj
    · have := (mem_lowSpan_iff a r (u : V)).1 u.2 j (not_lt.1 hj)
      simpa using this
  obtain ⟨b'', ν'', hL'', hM''⟩ := thm2_fin (V := W'') hK hLl hMl hπ0 hπ (finrank_lowSpan a hr)
  -- the new family
  let F : Fin (Module.finrank K V) → V := fun i =>
    if h : (i : ℕ) < r then (b'' ⟨i, h⟩ : V) else a i
  have hF1 : ∀ k : Fin r, F (Fin.castLE hr k) = (b'' k : V) := by
    intro k
    simp [F, k.2]
  have hF2 : ∀ i : Fin (Module.finrank K V), r ≤ (i : ℕ) → F i = a i := by
    intro i hi
    simp [F, not_lt.2 hi]
  have hb''L : ∀ k, (b'' k : V) ∈ L := by
    intro k
    have : b'' k ∈ ((L.comap W''.subtype.toAddMonoidHom : AddSubgroup W'') : Set W'') := by
      rw [hL'']
      refine ⟨Pi.single k 1, fun k' => ?_, by simp⟩
      by_cases h : k' = k
      · subst h; simp
      · simp [h]
    exact this
  have hFL : ∀ i, F i ∈ L := by
    intro i
    by_cases h : (i : ℕ) < r
    · simp only [F, h, ↓reduceDIte]; exact hb''L _
    · simp only [F, h, ↓reduceDIte]; exact haL i
  have hspanW : Submodule.span K (Set.range fun k : Fin r => (b'' k : V)) = W'' := by
    have := Submodule.map_span W''.subtype (Set.range b'')
    rw [b''.span_eq, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this.symm
  have hFspan : ⊤ ≤ Submodule.span K (Set.range F) := by
    have hW''le : W'' ≤ Submodule.span K (Set.range F) := by
      rw [← hspanW, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨Fin.castLE hr k, ?_⟩
      exact hF1 k
    have hai : ∀ j, a j ∈ Submodule.span K (Set.range F) := by
      intro j
      by_cases h : (j : ℕ) < r
      · exact hW''le (haW j h)
      · rw [← hF2 j (not_lt.1 h)]
        exact Submodule.subset_span ⟨j, rfl⟩
    intro v _
    rw [← a.sum_repr v]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hai j)
  let Fb := basisOfTopLeSpanOfCardEqFinrank F hFspan (by simp)
  have hFb : ∀ i, Fb i = F i := fun i => by simp [Fb]
  refine ⟨Fb, fun i => if h : (i : ℕ) < r then ν'' ⟨i, h⟩ else 0, hrs, hsn, ?_, ?_⟩
  · -- the lattice `L`
    simp only [hFb]
    ext w
    constructor
    · intro hw
      have hw' := hw
      rw [SetLike.mem_coe, ← SetLike.mem_coe, hLa] at hw'
      obtain ⟨c, hc, rfl⟩ := hw'
      set u : V := ∑ k : Fin r, c (Fin.castLE hr k) • a (Fin.castLE hr k) with hu
      have huW : u ∈ W'' := Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (haW _ k.2)
      have huL : u ∈ L := L.sum_mem fun k _ => hL.1 _ (hc _) _ (haL _)
      have : (⟨u, huW⟩ : W'') ∈ ((L.comap W''.subtype.toAddMonoidHom : AddSubgroup W'') : Set W'') :=
        huL
      rw [hL''] at this
      obtain ⟨d, hd, hdu⟩ := this
      have hdu' : u = ∑ k : Fin r, d k • (b'' k : V) := by
        have := congrArg Subtype.val hdu
        simpa using this
      set c' : Fin (Module.finrank K V) → K := fun i => if h : (i : ℕ) < r then d ⟨i, h⟩ else c i
        with hc'
      refine ⟨c', fun i => ?_, ?_⟩
      · by_cases h : (i : ℕ) < r
        · simp only [hc', h, ↓reduceDIte]; exact hd _
        · simp only [hc', h, ↓reduceDIte]; exact hc i
      · rw [sum_split hr (fun i => c i • a i), sum_split hr (fun i => c' i • F i)]
        congr 1
        · rw [← hu, hdu']
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hF1 k]
          simp [hc']
        · refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : r ≤ (i : ℕ)
          · simp [hc', h, not_lt.2 h, hF2 i h]
          · simp [h]
    · rintro ⟨c, hc, rfl⟩
      exact L.sum_mem fun i _ => hL.1 _ (hc i) _ (hFL i)
  · -- the module `M`
    simp only [hFb]
    ext w
    constructor
    · intro hw
      set x := a.repr w with hx
      set u : V := ∑ k : Fin r, x (Fin.castLE hr k) • a (Fin.castLE hr k) with hu
      set w' : V := ∑ i : Fin (Module.finrank K V), (if r ≤ (i : ℕ) then x i • a i else 0)
        with hw'
      have hwsplit : w = u + w' := by
        conv_lhs => rw [← a.sum_repr w]
        exact sum_split hr (fun i => a.repr w i • a i)
      have hw'repr : ∀ j, a.repr w' j = if r ≤ (j : ℕ) then x j else 0 := by
        intro j
        have : w' = ∑ i : Fin (Module.finrank K V), (if r ≤ (i : ℕ) then x i else 0) • a i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : r ≤ (i : ℕ) <;> simp [h]
        rw [this, a.repr_sum_self]
      have hw'M : w' ∈ M := by
        apply hM2
        intro j hj
        rw [hw'repr]
        rcases hj with hj | hj
        · simp [not_le.2 hj]
        · split_ifs
          · exact hM1 w hw j hj
          · rfl
      have huM : u ∈ M := by
        have : u = w - w' := by rw [hwsplit]; abel
        rw [this]
        exact M.sub_mem hw hw'M
      have huW : u ∈ W'' := Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (haW _ k.2)
      have : (⟨u, huW⟩ : W'') ∈ ((M.comap W''.subtype.toAddMonoidHom : AddSubgroup W'') : Set W'') :=
        huM
      rw [hM''] at this
      obtain ⟨d, hd, hdu⟩ := this
      have hdu' : u = ∑ k : Fin r, (d k * π ^ ν'' k) • (b'' k : V) := by
        have := congrArg Subtype.val hdu
        simpa using this
      refine ⟨fun i => if h : (i : ℕ) < r then d ⟨i, h⟩ else x i, fun i hi => ?_, fun i hi => ?_, ?_⟩
      · simp only [hi, ↓reduceDIte]; exact hd _
      · have : ¬ (i : ℕ) < r := by omega
        simp only [this, ↓reduceDIte]
        exact hM1 w hw i hi
      · rw [hwsplit, sum_split hr]
        congr 1
        · rw [hdu']
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hF1 k]
          simp
        · refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : r ≤ (i : ℕ)
          · simp [h, not_lt.2 h, hF2 i h]
          · simp [h]
    · rintro ⟨c, hc, hc0, rfl⟩
      rw [SetLike.mem_coe, sum_split hr]
      refine M.add_mem ?_ (M.sum_mem fun i _ => ?_)
      · have hmem : (⟨∑ k : Fin r, (c (Fin.castLE hr k) * π ^ ν'' k) • (b'' k : V),
              Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b'' k).2⟩ : W'') ∈
            ((M.comap W''.subtype.toAddMonoidHom : AddSubgroup W'') : Set W'') := by
          rw [hM'']
          refine ⟨fun k => c (Fin.castLE hr k), fun k => hc _ k.2, ?_⟩
          apply Subtype.ext
          simp
        have : (∑ k : Fin r, (c (Fin.castLE hr k) * π ^ ν'' k) • (b'' k : V)) ∈ M := hmem
        rw [Finset.sum_congr rfl (fun k _ => ?_)]
        · exact this
        · rw [hF1 k]
          simp [k.2]
      · by_cases h : r ≤ (i : ℕ)
        · simp only [h, ↓reduceIte, not_lt.2 h, hF2 i h]
          by_cases hs : s ≤ (i : ℕ)
          · rw [hc0 i hs, zero_smul]; exact M.zero_mem
          · apply hM2
            intro j hj
            by_cases hji : j = i
            · subst hji; omega
            · simp [hji]
        · simp [h, M.zero_mem]

end Cor1Core

/-- **Cor. 1 of Thm. 2.** For a lattice $L$ and an $R$-module $M$ in $V$ there are a basis $(v_i)$ and integers
$0\le r\le s\le n$, $\nu_i$ with $L=\sum Rv_i$ and $M=\sum_{i<r}\pi^{\nu_i}Rv_i+\sum_{r\le i<s}Kv_i$. -/
@[kb "weil1973bnt" "Ch. II, §2, Cor. 1 of Thm. 2"]
theorem weil_II_2_cor1_thm2 (hK : IsPField K p) {L M : AddSubgroup V} (hL : IsKLattice hK L)
    (hM : IsRModule hK M) {π : K} (hπ0 : π ≠ 0) (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K)) :
    ∃ (b : Module.Basis (Fin (Module.finrank K V)) K V) (r s : ℕ) (ν : Fin (Module.finrank K V) → ℤ),
      IsCor1Basis hK π L M b r s ν := by
  classical
  obtain ⟨W', hW'M, hW'max⟩ := exists_maximal_subspace (K := K) M
  set Ws : Submodule K V := Submodule.span K (M : Set V) with hWs
  have hW'Ws : W' ≤ Ws := fun x hx => Submodule.subset_span (hW'M hx)
  set s := Module.finrank K Ws with hs
  set d := Module.finrank K W' with hd
  have hds : d ≤ s := Submodule.finrank_mono hW'Ws
  have hsn : s ≤ Module.finrank K V := Submodule.finrank_le (R := K) Ws
  set r := s - d with hr
  let Wt : ℕ → Submodule K V := fun k => if k = 0 then Ws else W'
  have hWt : Antitone Wt := by
    intro i j hij
    by_cases hj : j = 0
    · have : i = 0 := by omega
      simp [Wt, hj, this]
    · by_cases hi : i = 0
      · simp [Wt, hi, hj, hW'Ws]
      · simp [Wt, hi, hj]
  obtain ⟨b, hLb, hWb⟩ := exists_lattice_basis_chain hK hL Wt hWt
  have h0 : Ws = Submodule.span K (b '' {j | Module.finrank K V - s ≤ (j : ℕ)}) := hWb 0
  have h1 : W' = Submodule.span K (b '' {j | Module.finrank K V - d ≤ (j : ℕ)}) := hWb 1
  obtain ⟨τ, hτ⟩ := exists_rot hsn
  set a := b.reindex τ.symm with ha
  have ha_apply : ∀ i, a i = b (τ i) := by intro i; simp [ha]
  have ha_repr : ∀ w i, a.repr w i = b.repr w (τ i) := by intro w i; simp [ha]
  have k1 : ∀ i : Fin (Module.finrank K V), Module.finrank K V - s ≤ ((τ i : Fin _) : ℕ) ↔
      (i : ℕ) < s := by
    intro i
    rw [hτ i]
    have := i.2
    split_ifs <;> omega
  have k2 : ∀ i : Fin (Module.finrank K V), Module.finrank K V - d ≤ ((τ i : Fin _) : ℕ) ↔
      r ≤ (i : ℕ) ∧ (i : ℕ) < s := by
    intro i
    rw [hτ i]
    have := i.2
    split_ifs <;> omega
  have hWs_iff : ∀ w, w ∈ Ws ↔ ∀ i : Fin (Module.finrank K V), s ≤ (i : ℕ) → a.repr w i = 0 := by
    intro w
    rw [h0, mem_span_image_iff]
    constructor
    · intro h i hi
      rw [ha_repr]
      apply h
      rw [k1]
      omega
    · intro h j hj
      obtain ⟨i, rfl⟩ := τ.surjective j
      rw [← ha_repr]
      apply h
      by_contra hlt
      exact hj ((k1 i).2 (not_le.1 hlt))
  have hW's_iff : ∀ w, w ∈ W' ↔
      ∀ i : Fin (Module.finrank K V), ((i : ℕ) < r ∨ s ≤ (i : ℕ)) → a.repr w i = 0 := by
    intro w
    rw [h1, mem_span_image_iff]
    constructor
    · intro h i hi
      rw [ha_repr]
      apply h
      rw [k2]
      omega
    · intro h j hj
      obtain ⟨i, rfl⟩ := τ.surjective j
      rw [← ha_repr]
      apply h
      by_contra hlt
      apply hj
      rw [k2]
      omega
  have hLa : (L : Set V) = {w | ∃ c : Fin (Module.finrank K V) → K, (∀ i, c i ∈ pR hK) ∧
      w = ∑ i, c i • a i} := by
    rw [hLb]
    ext w
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun i => c (τ i), fun i => hc _, ?_⟩
      simp only [ha_apply]
      exact (Equiv.sum_comp τ (fun j => c j • b j)).symm
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun j => c (τ.symm j), fun j => hc _, ?_⟩
      simp only [ha_apply]
      rw [← Equiv.sum_comp τ (fun j => c (τ.symm j) • b j)]
      simp
  have hM1 : ∀ w ∈ M, ∀ j : Fin (Module.finrank K V), s ≤ (j : ℕ) → a.repr w j = 0 :=
    fun w hw j hj => (hWs_iff w).1 (Submodule.subset_span hw) j hj
  have hM2 : ∀ w : V, (∀ j : Fin (Module.finrank K V), ((j : ℕ) < r ∨ s ≤ (j : ℕ)) →
      a.repr w j = 0) → w ∈ M := fun w h => hW'M ((hW's_iff w).2 h)
  have hM3 : ∀ U : Submodule K V, (U : Set V) ⊆ M → ∀ u ∈ U, ∀ j : Fin (Module.finrank K V),
      (j : ℕ) < r → a.repr u j = 0 :=
    fun U hU u hu j hj => (hW's_iff u).1 (hW'max U hU hu) j (Or.inl hj)
  have hlow : lowSpan a r ≤ Ws := by
    intro x hx
    rw [hWs_iff]
    intro i hi
    exact (mem_lowSpan_iff a r x).1 hx i (by omega)
  have hc : Continuous (fun x : lowSpan a r => (⟨(x : V), hlow x.2⟩ : Ws)) :=
    Continuous.subtype_mk continuous_subtype_val _
  have hMo : IsOpen {x : lowSpan a r | (x : V) ∈ M} :=
    (weil_II_2_prop5_isOpen hK hM).preimage hc
  obtain ⟨Fb, ν, hFb⟩ := cor1_core hK hL hM hπ0 hπ a (r := r) (s := s) (by omega) hsn hLa hM1 hM2
    hM3 hMo
  exact ⟨Fb, r, s, ν, hFb⟩

section Cor3Aux

/-- Coordinates of a vector of $L$ in a Cor. 1 basis lie in $R$. -/
theorem cor1_L_iff {hK : IsPField K p} {π : K} {L M : AddSubgroup V}
    {b : Module.Basis (Fin (Module.finrank K V)) K V} {r s : ℕ}
    {ν : Fin (Module.finrank K V) → ℤ} (h : IsCor1Basis hK π L M b r s ν) (w : V) :
    w ∈ L ↔ ∀ i, b.repr w i ∈ pR hK := by
  have hLs := h.2.2.1
  constructor
  · intro hw
    have : w ∈ (L : Set V) := hw
    rw [hLs] at this
    obtain ⟨c, hc, rfl⟩ := this
    intro i
    rw [b.repr_sum_self]
    exact hc i
  · intro hw
    have : w ∈ (L : Set V) := by
      rw [hLs]
      exact ⟨fun i => b.repr w i, hw, (b.sum_repr w).symm⟩
    exact this

/-- Coordinates of a vector of $M$ in a Cor. 1 basis. -/
theorem cor1_M_iff {hK : IsPField K p} {π : K} {L M : AddSubgroup V}
    {b : Module.Basis (Fin (Module.finrank K V)) K V} {r s : ℕ}
    {ν : Fin (Module.finrank K V) → ℤ} (h : IsCor1Basis hK π L M b r s ν) (w : V) :
    w ∈ M ↔ (∀ i : Fin (Module.finrank K V), (i : ℕ) < r → ∃ c ∈ pR hK, b.repr w i = c * π ^ ν i) ∧
      (∀ i : Fin (Module.finrank K V), s ≤ (i : ℕ) → b.repr w i = 0) := by
  obtain ⟨hrs, hsn, -, hMs⟩ := h
  constructor
  · intro hw
    have : w ∈ (M : Set V) := hw
    rw [hMs] at this
    obtain ⟨c, hc, hc0, rfl⟩ := this
    have hrep : ∀ i : Fin (Module.finrank K V), b.repr (∑ j : Fin (Module.finrank K V),
        (if (j : ℕ) < r then c j * π ^ ν j else c j) • b j) i =
        (if (i : ℕ) < r then c i * π ^ ν i else c i) := fun i => by
      rw [b.repr_sum_self]
    refine ⟨fun i hi => ⟨c i, hc i hi, ?_⟩, fun i hi => ?_⟩
    · rw [hrep, if_pos hi]
    · rw [hrep, if_neg (by omega)]
      exact hc0 i hi
  · rintro ⟨h1, h2⟩
    have : w ∈ (M : Set V) := by
      rw [hMs]
      have hex : ∀ i : Fin (Module.finrank K V), ∃ c : K, ((i : ℕ) < r → c ∈ pR hK ∧
          b.repr w i = c * π ^ ν i) ∧ (¬ (i : ℕ) < r → c = b.repr w i) := by
        intro i
        by_cases hi : (i : ℕ) < r
        · obtain ⟨c, hc, hc'⟩ := h1 i hi
          exact ⟨c, fun _ => ⟨hc, hc'⟩, fun h => absurd hi h⟩
        · exact ⟨b.repr w i, fun h => absurd h hi, fun _ => rfl⟩
      choose c hc using hex
      refine ⟨c, fun i hi => (hc i).1 hi |>.1, fun i hi => ?_, ?_⟩
      · rw [(hc i).2 (by omega)]
        exact h2 i hi
      · conv_lhs => rw [← b.sum_repr w]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : (i : ℕ) < r
        · rw [if_pos hi, ← ((hc i).1 hi).2]
        · rw [if_neg hi, (hc i).2 hi]
    exact this

/-- The residue ring $R/P$. -/
abbrev Rk (hK : IsPField K p) : Type _ := ↥(pR hK) ⧸ pPAdd hK

/-- Reduction of the coordinates modulo $P$, on an additive subgroup whose coordinates lie in $R$. -/
def redHom (hK : IsPField K p) (b : Module.Basis (Fin (Module.finrank K V)) K V) (E : AddSubgroup V)
    (hE : ∀ w ∈ E, ∀ i, b.repr w i ∈ pR hK) : E →+ (Fin (Module.finrank K V) → Rk hK) where
  toFun w i := QuotientAddGroup.mk ⟨b.repr (w : V) i, hE w w.2 i⟩
  map_zero' := by
    funext i
    have : (⟨b.repr (((0 : E)) : V) i, hE _ (0 : E).2 i⟩ : ↥(pR hK)) = 0 :=
      Subtype.ext (by simp)
    show QuotientAddGroup.mk _ = (0 : Fin (Module.finrank K V) → Rk hK) i
    rw [this]
    rfl
  map_add' x y := by
    funext i
    have : (⟨b.repr (((x + y : E)) : V) i, hE _ (x + y : E).2 i⟩ : ↥(pR hK)) =
        ⟨b.repr (x : V) i, hE _ x.2 i⟩ + ⟨b.repr (y : V) i, hE _ y.2 i⟩ := Subtype.ext (by simp)
    exact (congrArg (QuotientAddGroup.mk (s := pPAdd hK)) this).trans
      (QuotientAddGroup.mk_add (pPAdd hK) _ _)

theorem redHom_apply_eq_zero (hK : IsPField K p) (b : Module.Basis (Fin (Module.finrank K V)) K V)
    (E : AddSubgroup V) (hE : ∀ w ∈ E, ∀ i, b.repr w i ∈ pR hK) (w : E) :
    redHom hK b E hE w = 0 ↔ ∀ i, modK K (b.repr (w : V) i) < 1 := by
  constructor
  · intro h i
    have := congrFun h i
    exact (QuotientAddGroup.eq_zero_iff _).1 this
  · intro h
    funext i
    exact (QuotientAddGroup.eq_zero_iff _).2 (h i)

/-- The kernel of the reduction does not depend on the basis: it consists of the vectors that are
$\pi$ times a vector of $L$. -/
theorem redHom_ker {hK : IsPField K p} {π : K} {L M : AddSubgroup V}
    {b : Module.Basis (Fin (Module.finrank K V)) K V} {r s : ℕ}
    {ν : Fin (Module.finrank K V) → ℤ} (h : IsCor1Basis hK π L M b r s ν)
    (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K)) (E : AddSubgroup V)
    (hE : ∀ w ∈ E, ∀ i, b.repr w i ∈ pR hK) (w : E) :
    redHom hK b E hE w = 0 ↔ ∃ u ∈ L, (w : V) = π • u := by
  rw [redHom_apply_eq_zero]
  constructor
  · intro hw
    have hy : ∀ i, ∃ y ∈ pR hK, b.repr (w : V) i = π * y := fun i => by
      have : b.repr (w : V) i ∈ pP hK := hw i
      rw [hπ] at this
      obtain ⟨y, hy, hy'⟩ := this
      exact ⟨y, hy, hy'.symm⟩
    choose y hyR hy using hy
    refine ⟨∑ i, y i • b i, ?_, ?_⟩
    · exact (cor1_L_iff h _).2 (fun i => by rw [b.repr_sum_self]; exact hyR i)
    · rw [Finset.smul_sum]
      conv_lhs => rw [← b.sum_repr (w : V)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, hy i]
  · rintro ⟨u, hu, hwu⟩ i
    have hui : modK K (b.repr u i) ≤ 1 := (cor1_L_iff h u).1 hu i
    have hπP : modK K π < 1 := by
      have : π ∈ pP hK := by rw [hπ]; exact ⟨1, (pR hK).one_mem, mul_one π⟩
      exact this
    rw [hwu]
    have : b.repr (π • u) i = π * b.repr u i := by simp
    rw [this, modK_mul]
    exact (mul_le_mul' le_rfl hui).trans_lt (by simpa using hπP)

/-- $E_t=\{w\in L:\pi^tw\in M\}$. -/
def Etsub (L M : AddSubgroup V) (π : K) (t : ℤ) : AddSubgroup V where
  carrier := {w | w ∈ L ∧ (π ^ t) • w ∈ M}
  add_mem' := fun ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨L.add_mem h1 h3, by rw [smul_add]; exact M.add_mem h2 h4⟩
  zero_mem' := ⟨L.zero_mem, by rw [smul_zero]; exact M.zero_mem⟩
  neg_mem' := fun ⟨h1, h2⟩ => ⟨L.neg_mem h1, by rw [smul_neg]; exact M.neg_mem h2⟩

theorem Etsub_coord {hK : IsPField K p} {π : K} {L M : AddSubgroup V}
    {b : Module.Basis (Fin (Module.finrank K V)) K V} {r s : ℕ}
    {ν : Fin (Module.finrank K V) → ℤ} (h : IsCor1Basis hK π L M b r s ν) (t : ℤ) :
    ∀ w ∈ Etsub L M π t, ∀ i, b.repr w i ∈ pR hK := fun w hw => (cor1_L_iff h w).1 hw.1

/-- The coordinates that survive the reduction of $E_t$ modulo $P$. -/
def CPred {n : ℕ} (r s : ℕ) (ν : Fin n → ℤ) (t : ℤ) (i : Fin n) : Prop :=
  ((i : ℕ) < r ∧ ν i ≤ t) ∨ (r ≤ (i : ℕ) ∧ (i : ℕ) < s)

/-- The image of $E_t$ under reduction modulo $P$, in coordinates. -/
theorem mem_range_redHom {hK : IsPField K p} {π : K} {L M : AddSubgroup V}
    {b : Module.Basis (Fin (Module.finrank K V)) K V} {r s : ℕ}
    {ν : Fin (Module.finrank K V) → ℤ} (h : IsCor1Basis hK π L M b r s ν) (hπ0 : π ≠ 0)
    (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K)) (t : ℤ)
    (y : Fin (Module.finrank K V) → Rk hK) :
    y ∈ (redHom hK b (Etsub L M π t) (Etsub_coord h t)).range ↔
      ∀ i, ¬ CPred r s ν t i → y i = 0 := by
  have hrs := h.1
  have hsn := h.2.1
  have hq : modK K π = (pq hK : ℝ≥0)⁻¹ := weil_I_4_thm6_modK_prime hK hπ0 hπ
  have hq1 : modK K π < 1 := by
    have : π ∈ pP hK := by rw [hπ]; exact ⟨1, (pR hK).one_mem, mul_one π⟩
    exact this
  have hqpos : 0 < modK K π := modK_pos_iff.2 hπ0
  constructor
  · rintro ⟨w, rfl⟩ i hi
    show (QuotientAddGroup.mk _ : Rk hK) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    show modK K (b.repr (w : V) i) < 1
    obtain ⟨hwL, hwM⟩ := w.2
    have hM' := (cor1_M_iff h _).1 hwM
    have hrepr : b.repr (π ^ t • (w : V)) i = π ^ t * b.repr (w : V) i := by simp
    by_cases his : s ≤ (i : ℕ)
    · have h0 := hM'.2 i his
      rw [hrepr] at h0
      have : b.repr (w : V) i = 0 := (mul_eq_zero.1 h0).resolve_left (zpow_ne_zero _ hπ0)
      rw [this]
      simp
    · have hir : (i : ℕ) < r := by
        by_contra hnr
        exact hi (Or.inr ⟨not_lt.1 hnr, not_le.1 his⟩)
      have hνt : t < ν i := by
        by_contra hle
        exact hi (Or.inl ⟨hir, not_lt.1 hle⟩)
      obtain ⟨c, hc, hceq⟩ := hM'.1 i hir
      rw [hrepr] at hceq
      obtain ⟨k, hk⟩ : ∃ k : ℕ, ν i = t + ((k + 1 : ℕ) : ℤ) := ⟨(ν i - t - 1).toNat, by omega⟩
      have hpow : π ^ ν i = π ^ t * π ^ (k + 1) := by
        rw [hk, zpow_add₀ hπ0, zpow_natCast]
      have h1 : modK K (π ^ t) * modK K (b.repr (w : V) i) =
          modK K (π ^ t) * (modK K c * modK K π ^ (k + 1)) := by
        rw [← modK_mul, hceq, modK_mul, hpow, modK_mul, modK_pow]
        ring
      have hpos : modK K (π ^ t) ≠ 0 := (modK_pos_iff.2 (zpow_ne_zero _ hπ0)).ne'
      have h2 := mul_left_cancel₀ hpos h1
      have hc1 : modK K c ≤ 1 := hc
      calc modK K (b.repr (w : V) i) = modK K c * modK K π ^ (k + 1) := h2
        _ ≤ 1 * modK K π ^ (k + 1) := mul_le_mul' hc1 le_rfl
        _ = modK K π ^ (k + 1) := one_mul _
        _ ≤ modK K π := pow_le_of_le_one zero_le hq1.le (Nat.succ_ne_zero k)
        _ < 1 := hq1
  · intro hy
    classical
    have hz : ∀ i, ∃ z : ↥(pR hK), (QuotientAddGroup.mk z : Rk hK) = y i := fun i =>
      QuotientAddGroup.mk_surjective (y i)
    choose z hz using hz
    let x : Fin (Module.finrank K V) → K := fun i => if CPred r s ν t i then (z i : K) else 0
    have hxR : ∀ i, x i ∈ pR hK := fun i => by
      simp only [x]
      split_ifs
      · exact (z i).2
      · exact (pR hK).zero_mem
    have hx0 : ∀ i, ¬ CPred r s ν t i → x i = 0 := fun i hp => by simp [x, hp]
    have hxz : ∀ i, CPred r s ν t i → x i = (z i : K) := fun i hp => by simp [x, hp]
    let w : V := ∑ i, x i • b i
    have hwrepr : ∀ i, b.repr w i = x i := fun i => by
      simp only [w]
      rw [b.repr_sum_self]
    have hrepr : ∀ i, b.repr (π ^ t • w) i = π ^ t * x i := fun i => by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hwrepr]
    have hwE : w ∈ Etsub L M π t := by
      refine ⟨(cor1_L_iff h w).2 (fun i => by rw [hwrepr]; exact hxR i),
        (cor1_M_iff h _).2 ⟨fun i hi => ?_, fun i hi => ?_⟩⟩
      · rw [hrepr]
        by_cases hν : ν i ≤ t
        · refine ⟨π ^ t * x i * (π ^ ν i)⁻¹, ?_, inv_mul_cancel_right₀ (zpow_ne_zero _ hπ0) _ |>.symm⟩
          show modK K (π ^ t * x i * (π ^ ν i)⁻¹) ≤ 1
          rw [modK_mul, modK_mul, modK_inv (zpow_ne_zero _ hπ0), modK_zpow hπ0, modK_zpow hπ0]
          have hxi : modK K (x i) ≤ 1 := hxR i
          have hle : modK K π ^ t ≤ modK K π ^ ν i :=
            zpow_le_zpow_right_of_le_one₀ hqpos hq1.le hν
          have hpos : 0 < modK K π ^ ν i := zpow_pos hqpos _
          calc modK K π ^ t * modK K (x i) * (modK K π ^ ν i)⁻¹
              ≤ modK K π ^ ν i * 1 * (modK K π ^ ν i)⁻¹ := mul_le_mul' (mul_le_mul' hle hxi) le_rfl
            _ = 1 := by rw [mul_one, mul_inv_cancel₀ hpos.ne']
        · have hp : ¬ CPred r s ν t i := by
            rintro (⟨_, h2⟩ | ⟨h1, _⟩)
            · exact hν h2
            · omega
          exact ⟨0, (pR hK).zero_mem, by rw [hx0 i hp]; simp⟩
      · have hp : ¬ CPred r s ν t i := by
          rintro (⟨h1, _⟩ | ⟨_, h2⟩) <;> omega
        rw [hrepr, hx0 i hp, mul_zero]
    refine ⟨⟨w, hwE⟩, ?_⟩
    funext i
    show (QuotientAddGroup.mk _ : Rk hK) = y i
    by_cases hp : CPred r s ν t i
    · rw [← hz i]
      congr 1
      apply Subtype.ext
      show b.repr w i = (z i : K)
      rw [hwrepr, hxz i hp]
    · rw [hy i hp, QuotientAddGroup.eq_zero_iff]
      show modK K (b.repr w i) < 1
      rw [hwrepr, hx0 i hp]
      simp

open scoped Classical in
theorem card_range_redHom {hK : IsPField K p} {π : K} {L M : AddSubgroup V}
    {b : Module.Basis (Fin (Module.finrank K V)) K V} {r s : ℕ}
    {ν : Fin (Module.finrank K V) → ℤ} (h : IsCor1Basis hK π L M b r s ν) (hπ0 : π ≠ 0)
    (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K)) (t : ℤ) :
    Nat.card (redHom hK b (Etsub L M π t) (Etsub_coord h t)).range =
      pq hK ^ (Finset.univ.filter (CPred r s ν t)).card := by
  classical
  have e1 : (redHom hK b (Etsub L M π t) (Etsub_coord h t)).range ≃
      {y : Fin (Module.finrank K V) → Rk hK // ∀ i, ¬ CPred r s ν t i → y i = 0} :=
    Equiv.subtypeEquivRight (fun y => mem_range_redHom h hπ0 hπ t y)
  rw [Nat.card_congr (e1.trans (Equiv.subtypePiEquivPi (p := fun i x => ¬ CPred r s ν t i → x = 0))),
    Nat.card_pi]
  have hcard : ∀ i, Nat.card {x : Rk hK // ¬ CPred r s ν t i → x = 0} =
      if CPred r s ν t i then pq hK else 1 := by
    intro i
    by_cases hp : CPred r s ν t i
    · rw [if_pos hp, Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => fun h => absurd hp h))]
      rfl
    · rw [if_neg hp]
      have : Unique {x : Rk hK // ¬ CPred r s ν t i → x = 0} :=
        ⟨⟨⟨0, fun _ => rfl⟩⟩, fun a => Subtype.ext (a.2 hp)⟩
      exact Nat.card_unique
  simp only [hcard]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem card_range_eq {hK : IsPField K p} {π : K} {L M : AddSubgroup V}
    {b b' : Module.Basis (Fin (Module.finrank K V)) K V} {r s r' s' : ℕ}
    {ν ν' : Fin (Module.finrank K V) → ℤ} (h : IsCor1Basis hK π L M b r s ν)
    (h' : IsCor1Basis hK π L M b' r' s' ν')
    (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K)) (t : ℤ) :
    Nat.card (redHom hK b (Etsub L M π t) (Etsub_coord h t)).range =
      Nat.card (redHom hK b' (Etsub L M π t) (Etsub_coord h' t)).range := by
  have hker : (redHom hK b (Etsub L M π t) (Etsub_coord h t)).ker =
      (redHom hK b' (Etsub L M π t) (Etsub_coord h' t)).ker := by
    ext w
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, redHom_ker h hπ, redHom_ker h' hπ]
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange
      (redHom hK b (Etsub L M π t) (Etsub_coord h t))).toEquiv,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange
      (redHom hK b' (Etsub L M π t) (Etsub_coord h' t))).toEquiv, hker]

open scoped Classical in
theorem card_filter_eq {hK : IsPField K p} {π : K} {L M : AddSubgroup V}
    {b b' : Module.Basis (Fin (Module.finrank K V)) K V} {r s r' s' : ℕ}
    {ν ν' : Fin (Module.finrank K V) → ℤ} (h : IsCor1Basis hK π L M b r s ν)
    (h' : IsCor1Basis hK π L M b' r' s' ν') (hπ0 : π ≠ 0)
    (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K)) (t : ℤ) :
    (Finset.univ.filter (CPred r s ν t)).card = (Finset.univ.filter (CPred r' s' ν' t)).card := by
  have h1 := card_range_eq h h' hπ t
  rw [card_range_redHom h hπ0 hπ, card_range_redHom h' hπ0 hπ] at h1
  have hq : 2 ≤ pq hK := by
    have : 1 < pq hK := by exact_mod_cast one_lt_pq_norms hK
    omega
  exact Nat.pow_right_injective hq h1

theorem repr_smul_basis (b : Module.Basis (Fin (Module.finrank K V)) K V) (c : K)
    (i j : Fin (Module.finrank K V)) : b.repr (c • b i) j = if j = i then c else 0 := by
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

theorem finrank_span_cor1 {hK : IsPField K p} {π : K} {L M : AddSubgroup V}
    {b : Module.Basis (Fin (Module.finrank K V)) K V} {r s : ℕ}
    {ν : Fin (Module.finrank K V) → ℤ} (h : IsCor1Basis hK π L M b r s ν) (hπ0 : π ≠ 0) :
    Module.finrank K (Submodule.span K (M : Set V)) = s := by
  have hrs := h.1
  have hsn := h.2.1
  have hspan : Submodule.span K (M : Set V) = lowSpan b s := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro w hw
      exact (mem_lowSpan_iff b s w).2 (fun j hj => ((cor1_M_iff h w).1 hw).2 j hj)
    · unfold lowSpan
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      by_cases hir : (i : ℕ) < r
      · have hmem : π ^ ν i • b i ∈ M := by
          rw [cor1_M_iff h]
          refine ⟨fun j hj => ?_, fun j hj => ?_⟩
          · rw [repr_smul_basis]
            by_cases hji : j = i
            · exact ⟨1, (pR hK).one_mem, by simp [hji]⟩
            · exact ⟨0, (pR hK).zero_mem, by simp [hji]⟩
          · rw [repr_smul_basis, if_neg]
            intro hji
            subst hji
            have : (j : ℕ) < s := hi
            omega
        have : b i = (π ^ ν i)⁻¹ • (π ^ ν i • b i) := by
          rw [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hπ0), one_smul]
        rw [SetLike.mem_coe, this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
      · have hmem : b i ∈ M := by
          have : b i = (1 : K) • b i := (one_smul K _).symm
          rw [this, cor1_M_iff h]
          refine ⟨fun j hj => ?_, fun j hj => ?_⟩
          · rw [repr_smul_basis, if_neg]
            · exact ⟨0, (pR hK).zero_mem, by simp⟩
            · intro hji
              subst hji
              omega
          · rw [repr_smul_basis, if_neg]
            intro hji
            subst hji
            have : (j : ℕ) < s := hi
            omega
        exact Submodule.subset_span hmem
  rw [hspan]
  exact finrank_lowSpan b hsn

theorem card_filter_Ico {n r s : ℕ} (hs : s ≤ n) :
    (Finset.univ.filter fun i : Fin n => r ≤ (i : ℕ) ∧ (i : ℕ) < s).card = s - r := by
  have : (Finset.univ.filter fun i : Fin n => r ≤ (i : ℕ) ∧ (i : ℕ) < s).map Fin.valEmbedding =
      Finset.Ico r s := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, by omega⟩, ⟨h1, h2⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Ico]

theorem multiset_eq_of_card_filter_le (m1 m2 : Multiset ℤ)
    (h : ∀ v : ℤ, Multiset.card (m1.filter (· ≤ v)) = Multiset.card (m2.filter (· ≤ v))) :
    m1 = m2 := by
  have key : ∀ (m : Multiset ℤ) (v : ℤ), Multiset.card (m.filter (· ≤ v)) =
      Multiset.card (m.filter (· ≤ v - 1)) + m.count v := by
    intro m v
    have h1 : m.filter (· ≤ v) = m.filter (· ≤ v - 1) + m.filter (· = v) := by
      ext x
      simp only [Multiset.count_add, Multiset.count_filter]
      split_ifs <;> omega
    rw [h1, Multiset.card_add, Multiset.filter_eq', Multiset.card_replicate]
  ext v
  have e1 := key m1 v
  have e2 := key m2 v
  have := h v
  have := h (v - 1)
  omega

open scoped Classical in
theorem card_filter_CPred {n : ℕ} (r s : ℕ) (ν : Fin n → ℤ) (t : ℤ) :
    (Finset.univ.filter (CPred r s ν t)).card =
      (Finset.univ.filter fun i : Fin n => (i : ℕ) < r ∧ ν i ≤ t).card +
        (Finset.univ.filter fun i : Fin n => r ≤ (i : ℕ) ∧ (i : ℕ) < s).card := by
  have h1 : Finset.univ.filter (CPred r s ν t) =
      (Finset.univ.filter fun i : Fin n => (i : ℕ) < r ∧ ν i ≤ t) ∪
        (Finset.univ.filter fun i : Fin n => r ≤ (i : ℕ) ∧ (i : ℕ) < s) := by
    ext i
    simp [CPred]
  rw [h1, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro i _ h1 h2
  omega

theorem card_map_filter_le {n : ℕ} (r : ℕ) (ν : Fin n → ℤ) (v : ℤ) :
    Multiset.card (((Finset.univ.filter fun i : Fin n => (i : ℕ) < r).val.map ν).filter (· ≤ v)) =
      (Finset.univ.filter fun i : Fin n => (i : ℕ) < r ∧ ν i ≤ v).card := by
  rw [Multiset.filter_map, Multiset.card_map, ← Finset.filter_val, Finset.card_val,
    Finset.filter_filter]
  rfl

end Cor3Aux

/-- **Cor. 3 of Thm. 2.** The integers $r$, $s$ and the multiset $\{\nu_i\}_{i<r}$ of Cor. 1 depend only on $L$
and $M$. -/
@[kb "weil1973bnt" "Ch. II, §2, Cor. 3 of Thm. 2"]
theorem weil_II_2_cor3_thm2 (hK : IsPField K p) {L M : AddSubgroup V} {π : K} (hπ0 : π ≠ 0)
    (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K))
    {b b' : Module.Basis (Fin (Module.finrank K V)) K V} {r s r' s' : ℕ} {ν ν' : Fin (Module.finrank K V) → ℤ}
    (h : IsCor1Basis hK π L M b r s ν) (h' : IsCor1Basis hK π L M b' r' s' ν') :
    r = r' ∧ s = s' ∧
      ((Finset.univ.filter fun i : Fin (Module.finrank K V) => (i : ℕ) < r).val.map ν) =
        ((Finset.univ.filter fun i : Fin (Module.finrank K V) => (i : ℕ) < r').val.map ν') := by
  have hrs := h.1
  have hsn := h.2.1
  have hrs' := h'.1
  have hsn' := h'.2.1
  have hss : s = s' := by
    rw [← finrank_span_cor1 h hπ0, ← finrank_span_cor1 h' hπ0]
  obtain ⟨t0, ht0, ht0'⟩ : ∃ t0 : ℤ, (∀ i, t0 < ν i) ∧ (∀ i, t0 < ν' i) := by
    refine ⟨-((∑ i, ((ν i).natAbs + (ν' i).natAbs) : ℕ) : ℤ) - 1, fun i => ?_, fun i => ?_⟩
    · have := Finset.single_le_sum (f := fun i => (ν i).natAbs + (ν' i).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    · have := Finset.single_le_sum (f := fun i => (ν i).natAbs + (ν' i).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
  have hB : s - r = s' - r' := by
    have h1 := card_filter_eq h h' hπ0 hπ t0
    rw [card_filter_CPred, card_filter_CPred, card_filter_Ico hsn, card_filter_Ico hsn'] at h1
    have e1 : (Finset.univ.filter fun i : Fin (Module.finrank K V) =>
        (i : ℕ) < r ∧ ν i ≤ t0).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hh
      have := ht0 i
      omega
    have e2 : (Finset.univ.filter fun i : Fin (Module.finrank K V) =>
        (i : ℕ) < r' ∧ ν' i ≤ t0).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hh
      have := ht0' i
      omega
    omega
  obtain rfl : r = r' := by omega
  refine ⟨rfl, hss, ?_⟩
  apply multiset_eq_of_card_filter_le
  intro v
  rw [card_map_filter_le, card_map_filter_le]
  have h1 := card_filter_eq h h' hπ0 hπ v
  rw [card_filter_CPred, card_filter_CPred, card_filter_Ico hsn, card_filter_Ico hsn'] at h1
  omega

end General

section Extension

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}
  {K' : Type*} [DivisionRing K'] [Algebra K K'] [FiniteDimensional K K'] [TopologicalSpace K']
  [IsTopologicalDivisionRing K'] [T2Space K'] [ContinuousSMul K K']
  [LocallyCompactSpace K'] [(𝓝[≠] (0 : K')).NeBot]

/-- **Text p. 30.** $R'$ is a $K$-lattice in $K'$; hence $R'=\sum_jRy_j$ for a basis $(y_j)$ of $K'$ over $K$, and
for $y\in R'$ the coefficients $a_{ij}$ of $yy_i=\sum_ja_{ij}y_j$ lie in $R$. -/
@[kb "weil1973bnt" "Ch. II, §2, text p. 30 (R' is a lattice; the matrix of y ∈ R' has entries in R)"]
theorem weil_II_2_text_p30 (hK : IsPField K p) (hK' : IsPField K' p) :
    IsKLattice hK (pR hK').toAddSubgroup ∧
      ∃ b : Module.Basis (Fin (Module.finrank K K')) K K',
        (pR hK' : Set K') = {w | ∃ c : Fin (Module.finrank K K') → K, (∀ i, c i ∈ pR hK) ∧ w = ∑ i, c i • b i} ∧
        ∀ y ∈ pR hK', ∀ i j, b.repr (y * b i) j ∈ pR hK := by
  have hL : IsKLattice hK (pR hK').toAddSubgroup := by
    refine ⟨?_, weil_I_4_thm6_isCompact hK', (weil_I_4_thm6_isOpen hK').1⟩
    intro r hr m hm
    have hm' : modK K' m ≤ 1 := mem_pR (hK := hK') |>.1 hm
    show r • m ∈ pR hK'
    rw [mem_pR, Algebra.smul_def, modK_mul]
    exact mul_le_one' ((weil_I_4_cor5_thm6_R (K' := K') r).2 (mem_pR.1 hr)) hm'
  refine ⟨hL, ?_⟩
  obtain ⟨b, hb⟩ := weil_II_2_thm1 hK hL
  have hb' : (pR hK' : Set K') = {w | ∃ c : Fin (Module.finrank K K') → K, (∀ i, c i ∈ pR hK) ∧
      w = ∑ i, c i • b i} := hb
  refine ⟨b, hb', fun y hy i j => ?_⟩
  have hbi : b i ∈ pR hK' := by
    have : b i ∈ (pR hK' : Set K') := by
      rw [hb']
      refine ⟨Pi.single i 1, fun k => ?_, ?_⟩
      · by_cases h : k = i
        · subst h; simp
        · simp [h]
      · simp
    exact this
  have hyb : y * b i ∈ (pR hK' : Set K') := (pR hK').mul_mem hy hbi
  rw [hb'] at hyb
  obtain ⟨c, hc, hcy⟩ := hyb
  rw [hcy, b.repr_sum_self]
  exact hc j

end Extension

end NumberFieldKB.WeilBNT.FieldModule
