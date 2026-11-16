import NumberFieldKB.MilneEC.Ch5HeckeLattice
import NumberFieldKB.MilneEC.Ch5Euler
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Milne, *Elliptic Curves*, Chapter V §4: Hecke operators

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §4, pdf pp. 207–212.

Lattices in $\mathbb C$ are the $\mathbb Z$-spans of Mathlib's `PeriodPair`s (as in Chapter III,
`NumberFieldKB.MilneEC.IsLattice`); `LatticeDiv` is Milne's free abelian group $\mathcal D$ on the set
$\mathcal L$ of lattices, with the operators $T(n)$, $R(n)$ (pdf p. 208), Proposition 4.11, Corollaries 4.12, 4.13,
the action on functions on lattices and Proposition 4.14, the correspondence between homogeneous functions on
lattices and functions on $\mathbb H$ (pdf p. 208), the Hecke operators on modular forms of level one (definition
in prose, pdf p. 210), Lemma 4.15 and the explicit formula for $T(n)f$.

For level $N > 1$ Milne does not define $T(n)$ ("much the same, only a little more complicated", pdf p. 211);
`heckeT N k n` is the standard explicit operator
$(T(n)f)(z) = n^{2k-1}\sum_{ad = n,\ (a,N) = 1}\sum_{0 \le b < d}d^{-2k}f((az+b)/d)$, which for $N = 1$ is Milne's
formula (pdf p. 211) and for $p \mid N$ gives the operator $U(p)$ of footnote 4. Theorem 4.7 for general $N$ is a
named statement; Theorem 4.8 is proved for every $N$ from the explicit formula.
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold

namespace NumberFieldKB.MilneEC.V

/-! ### Lemma 4.15 and the explicit formula -/

/-- **Lemma 4.15** (pdf p. 211): every $A \in M_2(\mathbb Z)$ with $\det A = n \ge 1$ can be brought by some
$U \in \mathrm{SL}_2(\mathbb Z)$ to the form $UA = \begin{pmatrix}a&b\\0&d\end{pmatrix}$, $ad = n$, $a \ge 1$,
$0 \le b < d$, and $a$, $b$, $d$ are uniquely determined. Milne writes "$U \in M_2(\mathbb Z)$" and omits
$\det A = n$; $U$ must be invertible (it is a product of elementary operations of determinant $1$) (erratum). -/
@[kb "milne2006ec" "Ch. V, Lemma 4.15, pdf p. 211"]
theorem lemma_4_15 {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = n) :
    (∃ U : SL(2, ℤ), ∃ a b d : ℤ, (U : Matrix (Fin 2) (Fin 2) ℤ) * A = !![a, b; 0, d] ∧ a * d = n ∧ 1 ≤ a ∧
      0 ≤ b ∧ b < d) ∧
    ∀ (U U' : SL(2, ℤ)) (a b d a' b' d' : ℤ), (U : Matrix (Fin 2) (Fin 2) ℤ) * A = !![a, b; 0, d] →
      (U' : Matrix (Fin 2) (Fin 2) ℤ) * A = !![a', b'; 0, d'] → a * d = n → 1 ≤ a → 0 ≤ b → b < d →
      a' * d' = n → 1 ≤ a' → 0 ≤ b' → b' < d' → a = a' ∧ b = b' ∧ d = d' := by
  have hn' : (0:ℤ) < n := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = n := by rw [← hA, Matrix.det_fin_two]
    have hg : Int.gcd (A 0 0) (A 1 0) ≠ 0 := by
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, h2] at hdet
      simp at hdet
      omega
    have hgpos : (0:ℤ) < (Int.gcd (A 0 0) (A 1 0) : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hg
    obtain ⟨p', hp'⟩ := Int.gcd_dvd_left (a := A 0 0) (b := A 1 0)
    obtain ⟨r', hr'⟩ := Int.gcd_dvd_right (a := A 0 0) (b := A 1 0)
    have hbez := Int.gcd_eq_gcd_ab (A 0 0) (A 1 0)
    set g : ℤ := (Int.gcd (A 0 0) (A 1 0) : ℤ) with hgdef
    set x := Int.gcdA (A 0 0) (A 1 0)
    set y := Int.gcdB (A 0 0) (A 1 0)
    have h1 : x * p' + y * r' = 1 := by
      have : g * (x * p' + y * r') = g * 1 := by
        calc g * (x * p' + y * r') = (g * p') * x + (g * r') * y := by ring
          _ = A 0 0 * x + A 1 0 * y := by rw [← hp', ← hr']
          _ = g * 1 := by rw [hbez]; ring
      exact mul_left_cancel₀ hgpos.ne' this
    let U : SL(2, ℤ) := ⟨!![x, y; -r', p'], by simp [Matrix.det_fin_two]; linarith⟩
    set d : ℤ := p' * A 1 1 - r' * A 0 1 with hd
    set b0 : ℤ := x * A 0 1 + y * A 1 1 with hb0
    have hgd : g * d = n := by
      rw [← hdet, hd]
      calc g * (p' * A 1 1 - r' * A 0 1) = (g * p') * A 1 1 - (g * r') * A 0 1 := by ring
        _ = _ := by rw [← hp', ← hr']; ring
    have hdpos : 0 < d := by
      by_contra hneg
      have := not_lt.mp hneg
      nlinarith
    have hUA : (U : Matrix (Fin 2) (Fin 2) ℤ) * A = !![g, b0; 0, d] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [U, Matrix.mul_apply, Fin.sum_univ_two, hd, hb0] <;>
        first | ring1 | (rw [hbez]; ring1) | (rw [hp', hr']; ring1)
    let V : SL(2, ℤ) := ⟨!![1, -(b0 / d); 0, 1], by simp [Matrix.det_fin_two]⟩
    refine ⟨V * U, g, b0 % d, d, ?_, hgd, by omega, Int.emod_nonneg _ hdpos.ne',
      Int.emod_lt_of_pos _ hdpos⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hUA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [V, Matrix.mul_apply, Fin.sum_univ_two, Int.emod_def] <;> ring
  · intro U U' a b d a' b' d' h h' had ha hb hbd had' ha' hb' hbd'
    have hdpos : 0 < d := by
      by_contra hneg
      have := not_lt.mp hneg
      nlinarith
    have hVM : ((U' * U⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] = !![a', b'; 0, d'] := by
      rw [← h, ← h', ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    have hdetV := (U' * U⁻¹ : SL(2, ℤ)).det_coe
    rw [Matrix.det_fin_two] at hdetV
    set V := ((U' * U⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    have e00 := congrFun (congrFun hVM 0) 0
    have e01 := congrFun (congrFun hVM 0) 1
    have e10 := congrFun (congrFun hVM 1) 0
    have e11 := congrFun (congrFun hVM 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    have hv10 : V 1 0 = 0 := by
      rcases e10 with h0 | h0
      · exact h0
      · omega
    rw [hv10] at hdetV
    have hv : V 0 0 * V 1 1 = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hv with h0 | h0
    · have h11 : V 1 1 = 1 := by rw [h0] at hv; linarith
      rw [h0] at e00
      rw [hv10, h11] at e11
      rw [h0] at e01
      have hv01 : V 0 1 = 0 := by
        rcases lt_trichotomy (V 0 1) 0 with h2 | h2 | h2
        · nlinarith
        · exact h2
        · nlinarith
      rw [hv01] at e01
      refine ⟨by linarith, by linarith, by linarith⟩
    · rw [h0] at e00
      omega

/-- The triples $(a, b, d)$ with $ad = n$, $0 \le b < d$ ($a, d \ge 1$). -/
def heckeTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Nat.divisorsAntidiagonal n).biUnion fun ad ↦ (Finset.range ad.2).image fun b ↦ (ad.1, b, ad.2)

/-- $xz + y = 0$ with integers $x$, $y$ forces $x = y = 0$. -/
lemma int_comb_eq_zero (z : ℍ) {x y : ℤ} (h : (x : ℂ) * z + y = 0) : x = 0 ∧ y = 0 := by
  have h1 := congrArg Complex.im h
  have h2 := congrArg Complex.re h
  simp at h1 h2
  rcases h1 with h1 | h1
  · subst h1
    simp at h2
    exact ⟨rfl, h2⟩
  · exact absurd h1 z.im_pos.ne'

/-- Integer combinations $xz + y$ lie in $\Lambda(z, 1)$. -/
lemma mem_lattice_ofH (z : ℍ) (x y : ℤ) : (x : ℂ) * z + y ∈ (periodPairOf z).lattice :=
  (PeriodPair.mem_lattice).mpr ⟨x, y, by simp [periodPairOf]⟩

/-- The $\mathbb Z$-basis $(z, 1)$ of $\Lambda(z, 1)$, as a basis of the submodule attached to its additive
subgroup. -/
noncomputable def lattBasis (z : ℍ) :
    Module.Basis (Fin 2) ℤ (periodPairOf z).lattice.toAddSubgroup.toIntSubmodule :=
  (periodPairOf z).latticeBasis.map (LinearEquiv.ofEq _ _ rfl)

/-- The coordinates of $xz + y$ in the basis $(z, 1)$ are $(x, y)$. -/
lemma lattBasis_repr (z : ℍ) (w : (periodPairOf z).lattice.toAddSubgroup.toIntSubmodule) (x y : ℤ)
    (h : (w : ℂ) = x * z + y) : (lattBasis z).repr w 0 = x ∧ (lattBasis z).repr w 1 = y := by
  have c0 : ((lattBasis z 0 : (periodPairOf z).lattice.toAddSubgroup.toIntSubmodule) : ℂ) = z :=
    PeriodPair.latticeBasis_zero (L := periodPairOf z)
  have c1 : ((lattBasis z 1 : (periodPairOf z).lattice.toAddSubgroup.toIntSubmodule) : ℂ) = 1 :=
    PeriodPair.latticeBasis_one (L := periodPairOf z)
  have : w = x • lattBasis z 0 + y • lattBasis z 1 := by
    apply Subtype.ext
    rw [h]
    change _ = ((x • lattBasis z 0 : (periodPairOf z).lattice.toAddSubgroup.toIntSubmodule) : ℂ) +
      ((y • lattBasis z 1 : (periodPairOf z).lattice.toAddSubgroup.toIntSubmodule) : ℂ)
    simp only [Submodule.coe_smul, c0, c1, zsmul_eq_mul, mul_one]
  rw [this, map_add, map_zsmul, map_zsmul, Module.Basis.repr_self, Module.Basis.repr_self]
  simp

/-- Two integer combinations $xz + y$ with nonzero determinant are $\mathbb Z$-linearly independent. -/
lemma linearIndependent_pair_ofH (z : ℍ) {x1 y1 x2 y2 : ℤ} (hdet : x1 * y2 - x2 * y1 ≠ 0) :
    LinearIndependent ℤ ![(x1 : ℂ) * z + y1, (x2 : ℂ) * z + y2] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  simp only [zsmul_eq_mul] at h
  have h' : ((s * x1 + t * x2 : ℤ) : ℂ) * z + ((s * y1 + t * y2 : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination h
  obtain ⟨h1, h2⟩ := int_comb_eq_zero z h'
  constructor
  · by_contra hs
    apply hdet
    have : s * (x1 * y2 - x2 * y1) = 0 := by linear_combination y2 * h1 - x2 * h2
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hs
    · exact h0
  · by_contra ht
    apply hdet
    have : t * (x1 * y2 - x2 * y1) = 0 := by linear_combination (-y1) * h1 + x1 * h2
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 ht
    · exact h0

/-- The sublattice $\mathbb Z(x_1z + y_1) + \mathbb Z(x_2z + y_2)$ of $\Lambda(z, 1)$ has index
$|x_1y_2 - x_2y_1|$ (when this is nonzero). -/
lemma relIndex_span_pair (z : ℍ) {x1 y1 x2 y2 : ℤ} (hdet : x1 * y2 - x2 * y1 ≠ 0) :
    Submodule.span ℤ {(x1 : ℂ) * z + y1, (x2 : ℂ) * z + y2} ≤ (periodPairOf z).lattice ∧
    (Submodule.span ℤ {(x1 : ℂ) * z + y1, (x2 : ℂ) * z + y2}).toAddSubgroup.relIndex
      (periodPairOf z).lattice.toAddSubgroup = (x1 * y2 - x2 * y1).natAbs := by
  have hle : Submodule.span ℤ {(x1 : ℂ) * z + y1, (x2 : ℂ) * z + y2} ≤ (periodPairOf z).lattice :=
    Submodule.span_le.mpr (by rintro _ (rfl | rfl) <;> apply mem_lattice_ofH)
  refine ⟨hle, ?_⟩
  have hli := linearIndependent_pair_ofH z hdet
  have hrange : Submodule.span ℤ (Set.range ![(x1 : ℂ) * z + y1, (x2 : ℂ) * z + y2]) =
      Submodule.span ℤ {(x1 : ℂ) * z + y1, (x2 : ℂ) * z + y2} := by
    congr 1
    ext w
    simp [or_comm]
  let b₁ : Module.Basis (Fin 2) ℤ
      (Submodule.span ℤ {(x1 : ℂ) * z + y1, (x2 : ℂ) * z + y2}).toAddSubgroup.toIntSubmodule :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ (by rw [hrange]; rfl))
  have hb₁ : ∀ i, (b₁ i : ℂ) = ![(x1 : ℂ) * z + y1, (x2 : ℂ) * z + y2] i := by
    intro i
    exact congrArg Subtype.val (Module.Basis.span_apply hli i)
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ hle b₁ (lattBasis z), Module.Basis.det_apply,
    Matrix.det_fin_two]
  have e00 := lattBasis_repr z ⟨b₁ 0, hle (b₁ 0).2⟩ x1 y1 (by simpa using hb₁ 0)
  have e01 := lattBasis_repr z ⟨b₁ 1, hle (b₁ 1).2⟩ x2 y2 (by simpa using hb₁ 1)
  simp only [Module.Basis.toMatrix_apply]
  rw [e00.1, e00.2, e01.1, e01.2]

/-- Independent periods have nonzero determinant in the basis $(z, 1)$. -/
lemma det_ne_zero_of_indep (z : ℍ) (L : PeriodPair) {x1 y1 x2 y2 : ℤ}
    (h1 : L.ω₁ = x1 * z + y1) (h2 : L.ω₂ = x2 * z + y2) : x1 * y2 - x2 * y1 ≠ 0 := by
  intro hdet
  have hdet' : (x1 : ℂ) * y2 - x2 * y1 = 0 := by exact_mod_cast hdet
  have key := LinearIndependent.pair_iff.mp L.indep
  have r1 := key (x2 : ℝ) (-(x1 : ℝ)) (by
    simp only [Complex.real_smul, h1, h2]
    push_cast
    linear_combination (-1 : ℂ) * hdet')
  have r2 := key (y2 : ℝ) (-(y1 : ℝ)) (by
    simp only [Complex.real_smul, h1, h2]
    push_cast
    linear_combination (z : ℂ) * hdet')
  have hx1 : x1 = 0 := by exact_mod_cast (neg_eq_zero.mp r1.2)
  have hy1 : y1 = 0 := by exact_mod_cast (neg_eq_zero.mp r2.2)
  have r3 := key 1 0 (by
    simp only [Complex.real_smul, h1]
    simp [hx1, hy1])
  exact one_ne_zero r3.1

/-- The rows of an integer matrix as complex numbers $xz + y$. -/
def rowC (z : ℍ) (A : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) : ℂ := (A i 0 : ℂ) * z + (A i 1 : ℂ)

/-- The row vectors of a product of integer matrices are integer combinations of the rows of the second factor. -/
lemma rowC_mul (z : ℍ) (M A : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    rowC z (M * A) i = ∑ j, (M i j : ℂ) * rowC z A j := by
  simp only [rowC, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

/-- The lattice spanned by the rows of $MA$ is contained in the lattice spanned by the rows of $A$. -/
lemma span_rowC_mul_le (z : ℍ) (M A : Matrix (Fin 2) (Fin 2) ℤ) :
    Submodule.span ℤ (Set.range (rowC z (M * A))) ≤ Submodule.span ℤ (Set.range (rowC z A)) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [rowC_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  have : ((M i j : ℤ) : ℂ) * rowC z A j = (M i j) • rowC z A j := by simp [zsmul_eq_mul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Row operations by $\mathrm{SL}_2(\mathbb Z)$ do not change the span of the rows. -/
lemma span_rowC_mul_eq (z : ℍ) (U : SL(2, ℤ)) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    Submodule.span ℤ (Set.range (rowC z ((U : Matrix (Fin 2) (Fin 2) ℤ) * A))) =
      Submodule.span ℤ (Set.range (rowC z A)) := by
  apply le_antisymm (span_rowC_mul_le z _ _)
  have : A = ((U⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * ((U : Matrix (Fin 2) (Fin 2) ℤ) * A) := by
    rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  conv_lhs => rw [this]
  exact span_rowC_mul_le z _ _

/-- The $\mathbb Z$-span of the pair $(u, v)$ equals the span of the set $\{u, v\}$. -/
lemma span_range_pair (u v : ℂ) : Submodule.span ℤ (Set.range ![u, v]) = Submodule.span ℤ {u, v} := by
  congr 1
  ext w
  simp [or_comm]

/-- A sublattice $\mathbb Z(az + b) + \mathbb Zd$ with $0 \le b < d$ determines $a$, $b$, $d$
($a$, $d$ positive). -/
lemma span_pair_inj (z : ℍ) {a b d a' b' d' : ℤ} (ha : 1 ≤ a) (ha' : 1 ≤ a') (hd : 1 ≤ d) (hd' : 1 ≤ d')
    (hb : 0 ≤ b) (hbd : b < d) (hb' : 0 ≤ b') (hbd' : b' < d')
    (h : Submodule.span ℤ {(a : ℂ) * z + b, (d : ℂ)} = Submodule.span ℤ {(a' : ℂ) * z + b', (d' : ℂ)}) :
    a = a' ∧ b = b' ∧ d = d' := by
  have m1 : (a : ℂ) * z + b ∈ Submodule.span ℤ {(a' : ℂ) * z + b', (d' : ℂ)} :=
    h ▸ Submodule.subset_span (by simp)
  have m2 : (d : ℂ) ∈ Submodule.span ℤ {(a' : ℂ) * z + b', (d' : ℂ)} :=
    h ▸ Submodule.subset_span (by simp)
  have m3 : (a' : ℂ) * z + b' ∈ Submodule.span ℤ {(a : ℂ) * z + b, (d : ℂ)} :=
    h ▸ Submodule.subset_span (by simp)
  have m4 : (d' : ℂ) ∈ Submodule.span ℤ {(a : ℂ) * z + b, (d : ℂ)} :=
    h ▸ Submodule.subset_span (by simp)
  rw [Submodule.mem_span_pair] at m1 m2 m3 m4
  obtain ⟨s, t, hst⟩ := m1
  obtain ⟨u, v, huv⟩ := m2
  obtain ⟨s', t', hst'⟩ := m3
  obtain ⟨u', v', huv'⟩ := m4
  simp only [zsmul_eq_mul] at hst huv hst' huv'
  have e1 := int_comb_eq_zero z (x := s * a' - a) (y := s * b' + t * d' - b)
    (by push_cast; linear_combination hst)
  have e2 := int_comb_eq_zero z (x := u * a') (y := u * b' + v * d' - d)
    (by push_cast; linear_combination huv)
  have e3 := int_comb_eq_zero z (x := s' * a - a') (y := s' * b + t' * d - b')
    (by push_cast; linear_combination hst')
  have e4 := int_comb_eq_zero z (x := u' * a) (y := u' * b + v' * d - d')
    (by push_cast; linear_combination huv')
  obtain ⟨e1a, e1b⟩ := e1
  obtain ⟨e2a, e2b⟩ := e2
  obtain ⟨e3a, e3b⟩ := e3
  obtain ⟨e4a, e4b⟩ := e4
  have hu : u = 0 := by
    rcases mul_eq_zero.mp e2a with h0 | h0
    · exact h0
    · omega
  have hu' : u' = 0 := by
    rcases mul_eq_zero.mp e4a with h0 | h0
    · exact h0
    · omega
  subst hu hu'
  have hs : 0 < s := by
    by_contra hneg
    have := not_lt.mp hneg
    nlinarith
  have hs' : 0 < s' := by
    by_contra hneg
    have := not_lt.mp hneg
    nlinarith
  have hv : 0 < v := by
    by_contra hneg
    have := not_lt.mp hneg
    nlinarith
  have hv' : 0 < v' := by
    by_contra hneg
    have := not_lt.mp hneg
    nlinarith
  have hss : s * s' = 1 := by
    have : a * (s * s' - 1) = 0 := by linear_combination s * e3a + e1a
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · linarith
  have hvv : v * v' = 1 := by
    have : d * (v * v' - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · linarith
  have hs1 : s = 1 := by nlinarith
  have hv1 : v = 1 := by nlinarith
  subst hs1 hv1
  have hda : a = a' := by linarith
  have hdd : d = d' := by linarith
  subst hda hdd
  have ht : t = 0 := by
    rcases lt_trichotomy t 0 with h0 | h0 | h0
    · nlinarith
    · exact h0
    · nlinarith
  subst ht
  exact ⟨rfl, by linarith, rfl⟩

/-- The row vector of the integer matrix with entries $p, q, r, s$ at the point $z$, written out explicitly. -/
lemma rowC_of (z : ℍ) (p q r s : ℤ) :
    rowC z !![p, q; r, s] = ![(p : ℂ) * z + q, (r : ℂ) * z + s] := by
  funext i
  fin_cases i <;> simp [rowC]

/-- Running text (pdf p. 211): the sublattices of index $n$ of $\Lambda(z, 1)$ are exactly the lattices
$\mathbb Z(az + b) + \mathbb Zd$ with $(a, b, d)$ as in Lemma 4.15. -/
@[kb "milne2006ec" "Ch. V, §4, sublattices of index n of Λ(z,1) (running text), pdf p. 211"]
theorem sublatticesOfIndex_ofH {n : ℕ} (hn : 1 ≤ n) (z : ℍ) (Λ' : LatticeC) :
    Λ' ∈ sublatticesOfIndex n (LatticeC.ofH z) ↔
      ∃ t ∈ heckeTriples n, Λ'.1 = Submodule.span ℤ {(t.1 : ℂ) * z + t.2.1, (t.2.2 : ℂ)} := by
  have hΛ : (LatticeC.ofH z).1 = (periodPairOf z).lattice := rfl
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  constructor
  · rintro ⟨hle, hidx⟩
    rw [hΛ] at hle hidx
    obtain ⟨L, hL⟩ := Λ'.2
    have m1 : L.ω₁ ∈ (periodPairOf z).lattice := hle (hL ▸ L.ω₁_mem_lattice)
    have m2 : L.ω₂ ∈ (periodPairOf z).lattice := hle (hL ▸ L.ω₂_mem_lattice)
    obtain ⟨x1, y1, h1⟩ := PeriodPair.mem_lattice.mp m1
    obtain ⟨x2, y2, h2⟩ := PeriodPair.mem_lattice.mp m2
    have h1' : L.ω₁ = x1 * z + y1 := by rw [← h1]; simp [periodPairOf]
    have h2' : L.ω₂ = x2 * z + y2 := by rw [← h2]; simp [periodPairOf]
    have hdet := det_ne_zero_of_indep z L h1' h2'
    have hsp : Λ'.1 = Submodule.span ℤ {(x1 : ℂ) * z + y1, (x2 : ℂ) * z + y2} := by
      rw [← hL, PeriodPair.lattice, h1', h2']
    have hnat : (x1 * y2 - x2 * y1).natAbs = n := by
      have := (relIndex_span_pair z hdet).2
      rw [← hsp, hidx] at this
      exact this.symm
    have hB : ∃ B : Matrix (Fin 2) (Fin 2) ℤ, B.det = n ∧
        Submodule.span ℤ (Set.range (rowC z B)) = Λ'.1 := by
      rcases Int.natAbs_eq (x1 * y2 - x2 * y1) with h | h
      · refine ⟨!![x1, y1; x2, y2], ?_, ?_⟩
        · rw [Matrix.det_fin_two_of]
          rw [hnat] at h
          linarith
        · rw [rowC_of, span_range_pair, hsp]
      · refine ⟨!![x2, y2; x1, y1], ?_, ?_⟩
        · rw [Matrix.det_fin_two_of]
          rw [hnat] at h
          linarith
        · rw [rowC_of, span_range_pair, hsp, Set.pair_comm]
    obtain ⟨B, hBdet, hBspan⟩ := hB
    obtain ⟨⟨U, a, b, d, hUB, had, ha, hb, hbd⟩, -⟩ := lemma_4_15 hn B hBdet
    have hd : 1 ≤ d := by
      by_contra hneg
      have := not_le.mp hneg
      nlinarith
    have ca : ((a.toNat : ℕ) : ℂ) = (a : ℂ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    have cb : ((b.toNat : ℕ) : ℂ) = (b : ℂ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    have cd : ((d.toNat : ℕ) : ℂ) = (d : ℂ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    refine ⟨(a.toNat, b.toNat, d.toNat), ?_, ?_⟩
    · unfold heckeTriples
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
      refine ⟨(a.toNat, d.toNat), ?_, b.toNat, by simp only; omega, rfl⟩
      rw [Nat.mem_divisorsAntidiagonal]
      refine ⟨?_, by omega⟩
      have : ((a.toNat * d.toNat : ℕ) : ℤ) = n := by
        push_cast
        rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
        exact had
      exact_mod_cast this
    · simp only
      rw [ca, cb, cd, ← hBspan, ← span_rowC_mul_eq z U B, hUB, rowC_of, span_range_pair]
      simp
  · rintro ⟨⟨a, b, d⟩, ht, hΛ'⟩
    unfold heckeTriples at ht
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, Nat.mem_divisorsAntidiagonal] at ht
    obtain ⟨⟨a', d'⟩, ⟨had, hn0⟩, b', hb', hteq⟩ := ht
    simp only [Prod.mk.injEq] at hteq
    obtain ⟨rfl, rfl, rfl⟩ := hteq
    simp only at had hb' hΛ'
    have ha : 1 ≤ a' := Nat.one_le_iff_ne_zero.mpr (left_ne_zero_of_mul (had ▸ hn0))
    have hd : 1 ≤ d' := Nat.one_le_iff_ne_zero.mpr (right_ne_zero_of_mul (had ▸ hn0))
    have hdet : ((a' : ℕ) : ℤ) * ((d' : ℕ) : ℤ) - (0 : ℤ) * ((b' : ℕ) : ℤ) ≠ 0 := by
      have : 0 < ((a' : ℕ) : ℤ) * ((d' : ℕ) : ℤ) := by positivity
      omega
    have key := relIndex_span_pair z (x1 := ((a' : ℕ) : ℤ)) (y1 := ((b' : ℕ) : ℤ)) (x2 := 0)
      (y2 := ((d' : ℕ) : ℤ)) hdet
    simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_natCast, zero_mul, sub_zero] at key
    rw [← hΛ'] at key
    refine ⟨key.1, ?_⟩
    rw [hΛ, key.2]
    have : (((a' : ℕ) : ℤ) * ((d' : ℕ) : ℤ)).natAbs = a' * d' := by
      rw [← Nat.cast_mul, Int.natAbs_natCast]
    rw [this, had]

/-- The explicit Hecke operator of level $N$ and weight $2k$:
$(T(n)f)(z) = n^{2k-1}\sum_{ad = n,\ \gcd(a, N) = 1,\ 0 \le b < d}d^{-2k}f((az + b)/d)$ (see the module
docstring). -/
noncomputable def heckeT (N k n : ℕ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  (n : ℂ) ^ (2 * k - 1) * ∑ t ∈ (heckeTriples n).filter (fun t ↦ t.1.Coprime N),
    (t.2.2 : ℂ) ^ (-(2 * k : ℤ)) * f (ofComplex (((t.1 : ℂ) * z + t.2.1) / t.2.2))

/-- The elements of `heckeTriples n` are the triples $(a, b, d)$ with $a, d \ge 1$, $ad = n$, $b < d$. -/
lemma mem_heckeTriples {n : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ heckeTriples n) :
    1 ≤ t.1 ∧ 1 ≤ t.2.2 ∧ t.1 * t.2.2 = n ∧ t.2.1 < t.2.2 := by
  obtain ⟨a, b, d⟩ := t
  unfold heckeTriples at ht
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, Nat.mem_divisorsAntidiagonal] at ht
  obtain ⟨⟨a', d'⟩, ⟨had, hn0⟩, b', hb', hteq⟩ := ht
  simp only [Prod.mk.injEq] at hteq
  obtain ⟨rfl, rfl, rfl⟩ := hteq
  exact ⟨Nat.one_le_iff_ne_zero.mpr (left_ne_zero_of_mul (had ▸ hn0)),
    Nat.one_le_iff_ne_zero.mpr (right_ne_zero_of_mul (had ▸ hn0)), had, hb'⟩

/-- The lattice $d\,\Lambda((az+b)/d, 1)$ attached to a triple $(a, b, d)$ (junk value $\Lambda(z, 1)$ if
$d = 0$). -/
noncomputable def tripleLattice (z : ℍ) (t : ℕ × ℕ × ℕ) : LatticeC :=
  if h : (t.2.2 : ℂ) ≠ 0 then
    LatticeC.scale h (LatticeC.ofH (ofComplex (((t.1 : ℂ) * z + t.2.1) / t.2.2)))
  else LatticeC.ofH z

/-- For $a, d \ge 1$ the point $(az + b)/d$ lies in $\mathbb H$. -/
lemma im_affine_pos (z : ℍ) {a d : ℕ} (b : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d) :
    0 < (((a : ℂ) * z + b) / d).im := by
  have h1 : (0 : ℝ) < a := by exact_mod_cast ha
  have h2 : (0 : ℝ) < d := by exact_mod_cast hd
  have := z.im_pos
  simp [Complex.div_natCast_im]
  positivity

/-- The underlying lattice of the triple lattice with parameters $a, b, d$ at the point $z$. -/
lemma tripleLattice_val (z : ℍ) {a b d : ℕ} (ha : 1 ≤ a) (hd : 1 ≤ d) :
    (tripleLattice z (a, b, d)).1 = Submodule.span ℤ {(a : ℂ) * z + b, (d : ℂ)} := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have him := im_affine_pos z b ha hd
  unfold tripleLattice
  rw [dif_pos hd0]
  show Submodule.map (LinearMap.mul ℤ ℂ (d : ℂ)) (periodPairOf _).lattice = _
  rw [PeriodPair.lattice, Submodule.map_span, Set.image_pair]
  simp only [periodPairOf, ofComplex_apply_of_im_pos him, LinearMap.mul_apply']
  congr 2 <;> simp [mul_div_cancel₀ _ hd0]

/-- The function on lattices attached to $f$ satisfying (3.1b) is homogeneous and restricts to $f$. -/
lemma latticeFun_spec {k : ℕ} {f : ℍ → ℂ} (hf : IsWeightInvariant k f) :
    IsHomogeneous k (latticeFun k f) ∧ ∀ z, latticeFun k f (LatticeC.ofH z) = f z := by
  have h := ((lattice_correspondence k).2 f hf).exists
  unfold latticeFun
  rw [dif_pos h]
  exact h.choose_spec

/-- $(T(n)\cdot F)(\Lambda(z, 1)) = \sum_{(a,b,d)}d^{-2k}F(\Lambda((az+b)/d, 1))$ for homogeneous $F$. -/
lemma endSmulFun_heckeTL_ofH {k n : ℕ} (hn : 1 ≤ n) {F : LatticeC → ℂ} (hF : IsHomogeneous k F) (z : ℍ) :
    endSmulFun (heckeTL n) F (LatticeC.ofH z) =
      ∑ t ∈ heckeTriples n, (t.2.2 : ℂ) ^ (-(2 * k : ℤ)) *
        F (LatticeC.ofH (ofComplex (((t.1 : ℂ) * z + t.2.1) / t.2.2))) := by
  have hS : sublatticesOfIndex n (LatticeC.ofH z) = tripleLattice z '' (heckeTriples n : Set (ℕ × ℕ × ℕ)) := by
    ext Λ'
    rw [sublatticesOfIndex_ofH hn]
    constructor
    · rintro ⟨t, ht, h⟩
      obtain ⟨ha, hd, -, -⟩ := mem_heckeTriples ht
      refine ⟨t, ht, ?_⟩
      apply Subtype.ext
      obtain ⟨a, b, d⟩ := t
      rw [tripleLattice_val z ha hd, h]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨ha, hd, -, -⟩ := mem_heckeTriples ht
      refine ⟨t, ht, ?_⟩
      obtain ⟨a, b, d⟩ := t
      exact tripleLattice_val z ha hd
  have hfin : (sublatticesOfIndex n (LatticeC.ofH z)).Finite := by
    rw [hS]
    exact (Finset.finite_toSet _).image _
  have h1 : endSmulFun (heckeTL n) F (LatticeC.ofH z) = ∑ Λ' ∈ hfin.toFinset, F Λ' := by
    unfold endSmulFun heckeTL heckeSum
    rw [Finsupp.linearCombination_single, one_smul, dif_pos hfin, extendLin_eq, map_sum]
    refine Finset.sum_congr rfl fun Λ' _ => ?_
    simp [Finsupp.linearCombination_single]
  rw [h1]
  symm
  refine Finset.sum_bij (fun t _ => tripleLattice z t) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Set.Finite.mem_toFinset, hS]
    exact ⟨t, ht, rfl⟩
  · intro t₁ ht₁ t₂ ht₂ h
    obtain ⟨ha₁, hd₁, -, hb₁⟩ := mem_heckeTriples ht₁
    obtain ⟨ha₂, hd₂, -, hb₂⟩ := mem_heckeTriples ht₂
    obtain ⟨a₁, b₁, d₁⟩ := t₁
    obtain ⟨a₂, b₂, d₂⟩ := t₂
    have h' := congrArg Subtype.val h
    rw [tripleLattice_val z ha₁ hd₁, tripleLattice_val z ha₂ hd₂] at h'
    have := span_pair_inj z (a := a₁) (b := b₁) (d := d₁) (a' := a₂) (b' := b₂) (d' := d₂)
      (by exact_mod_cast ha₁) (by exact_mod_cast ha₂) (by exact_mod_cast hd₁) (by exact_mod_cast hd₂)
      (by positivity) (by exact_mod_cast hb₁) (by positivity) (by exact_mod_cast hb₂)
      (by simpa using h')
    obtain ⟨e1, e2, e3⟩ := this
    simp only [Prod.mk.injEq]
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2, by exact_mod_cast e3⟩
  · intro Λ' hΛ'
    rw [Set.Finite.mem_toFinset, hS] at hΛ'
    obtain ⟨t, ht, rfl⟩ := hΛ'
    exact ⟨t, ht, rfl⟩
  · intro t ht
    obtain ⟨ha, hd, -, -⟩ := mem_heckeTriples ht
    obtain ⟨a, b, d⟩ := t
    have hd1 : 1 ≤ d := hd
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    show _ = F (tripleLattice z (a, b, d))
    unfold tripleLattice
    rw [dif_pos hd0, hF]

/-- Running text (pdf p. 211): for $f$ satisfying (3.1b) for $\mathrm{SL}_2(\mathbb Z)$,
$(T(n)f)(z) = n^{2k-1}\sum_{a,b,d}d^{-2k}f((az+b)/d)$, the explicit operator `heckeT 1`. -/
@[kb "milne2006ec" "Ch. V, §4, explicit formula for T(n)f (running text), pdf p. 211"]
theorem heckeOpLevelOne_eq {k n : ℕ} (hn : 1 ≤ n) {f : ℍ → ℂ} (hf : IsWeightInvariant k f) :
    heckeOpLevelOne k n f = heckeT 1 k n f := by
  funext z
  obtain ⟨hF, hFf⟩ := latticeFun_spec hf
  unfold heckeOpLevelOne heckeT
  rw [endSmulFun_heckeTL_ofH hn hF, Finset.filter_true_of_mem (fun t _ => Nat.coprime_one_right _)]
  simp only [hFf]

/-! ### Theorems 4.7, 4.8, Corollary 4.9, Example 4.10 -/

/-- $T(n)$ is linear. -/
lemma heckeT_smul (N k n : ℕ) (a : ℂ) (g : ℍ → ℂ) : heckeT N k n (a • g) = a • heckeT N k n g := by
  funext z
  simp only [heckeT, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

/-- $T(n)$ kills the zero function. -/
lemma heckeT_zero (N k n : ℕ) : heckeT N k n (0 : ℍ → ℂ) = 0 := by
  have := heckeT_smul N k n 0 (0 : ℍ → ℂ)
  simpa using this

/-- A cusp form of weight zero vanishes (it is constant and zero at the cusp $\infty$). -/
lemma cuspForm_weight_zero_eq_zero {N : ℕ} [NeZero N] (f : CuspForm (Gamma0GL N) 0) :
    (⇑f : ℍ → ℂ) = 0 := by
  obtain ⟨C, hC⟩ := ModularForm.eq_const_of_weight_zero (f : ModularForm (Gamma0GL N) 0)
  have h0 := CuspFormClass.zero_at_infty f
  have hf : (⇑f : ℍ → ℂ) = fun _ => C := hC
  have h1 : Tendsto (fun _ : ℍ => C) atImInfty (nhds 0) := hf ▸ h0
  have : C = 0 := tendsto_nhds_unique h1 tendsto_const_nhds |>.symm
  rw [hf, this]
  rfl

/-- $\Gamma_0(1) = \mathrm{SL}_2(\mathbb Z)$. -/
lemma Gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp only [Subgroup.mem_top, iff_true]
  rw [CongruenceSubgroup.Gamma0_mem]
  exact Subsingleton.elim _ _

/-- $\Gamma_0(1)$, as a subgroup of $\mathrm{GL}_2(\mathbb R)$, is the level of Mathlib's level one forms. -/
lemma Gamma0GL_one_eq : Gamma0GL 1 = 𝒮ℒ := by
  rw [Gamma0GL, Gamma0_one_eq_top, MonoidHom.range_eq_map]

/-- Cusp forms for $\Gamma_0(1)$ and for $\mathrm{SL}_2(\mathbb Z)$ (Mathlib's `𝒮ℒ`) of any weight are the same
functions. -/
lemma exists_cuspForm_Gamma0GL_one_iff_weight (w : ℤ) (g : ℍ → ℂ) :
    (∃ F : CuspForm (Gamma0GL 1) w, ⇑F = g) ↔ ∃ F : CuspForm 𝒮ℒ w, ⇑F = g := by
  rw [Gamma0GL_one_eq]

/-- Cusp forms of weight $2k$ for $\Gamma_0(1)$ and for $\mathrm{SL}_2(\mathbb Z)$ are the same functions. -/
lemma exists_cuspForm_Gamma0GL_one_iff (k : ℕ) (g : ℍ → ℂ) :
    (∃ F : CuspForm (Gamma0GL 1) (2 * k : ℤ), ⇑F = g) ↔ ∃ F : CuspForm 𝒮ℒ (2 * k : ℤ), ⇑F = g :=
  exists_cuspForm_Gamma0GL_one_iff_weight _ g

/-- A level one cusp form of weight $0$ vanishes. -/
lemma cuspForm_levelOne_weight_zero (f : CuspForm 𝒮ℒ (2 * ((0 : ℕ) : ℤ))) : (⇑f : ℍ → ℂ) = 0 := by
  have h0 : ∀ w : ℤ, w = 0 → ∀ g : CuspForm 𝒮ℒ w, (⇑g : ℍ → ℂ) = 0 := by
    rintro w rfl g
    obtain ⟨F, hF⟩ := (exists_cuspForm_Gamma0GL_one_iff_weight 0 ⇑g).mpr ⟨g, rfl⟩
    rw [← hF]
    exact cuspForm_weight_zero_eq_zero F
  exact h0 _ (by norm_num) f

/-- Slash invariance for $\mathrm{SL}_2(\mathbb Z)$ is (3.1b). -/
lemma isWeightInvariant_of_slash {k : ℕ} {g : ℍ → ℂ} (h : ∀ γ ∈ 𝒮ℒ, g ∣[(2 * k : ℤ)] γ = g) :
    IsWeightInvariant k g := by
  intro γ z
  have h1 : g ∣[(2 * k : ℤ)] γ = g := h (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩
  have := (slash_action_eq'_iff (2 * k : ℤ) g γ z).mp (congrFun h1 z)
  have e : (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) := by push_cast; ring
  rwa [e, zpow_natCast] at this

/-- (3.1b) is slash invariance for $\mathrm{SL}_2(\mathbb Z)$. -/
lemma slash_of_isWeightInvariant {k : ℕ} {g : ℍ → ℂ} (h : IsWeightInvariant k g) :
    ∀ γ ∈ 𝒮ℒ, g ∣[(2 * k : ℤ)] γ = g := by
  rintro _ ⟨γ, rfl⟩
  funext z
  change (g ∣[(2 * k : ℤ)] γ) z = g z
  rw [slash_action_eq'_iff]
  have e : (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_natCast]
  exact h γ z

/-- Level one cusp forms satisfy (3.1b). -/
lemma isWeightInvariant_cuspForm {k : ℕ} (f : CuspForm 𝒮ℒ (2 * k : ℤ)) : IsWeightInvariant k f :=
  isWeightInvariant_of_slash (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)

/-- The function on lattices attached to $g$ is the given homogeneous function $G$ when
$G(\Lambda(z, 1)) = g(z)$. -/
lemma latticeFun_unique {k : ℕ} {g : ℍ → ℂ} {G : LatticeC → ℂ} (hG : IsHomogeneous k G)
    (hGg : ∀ z, G (LatticeC.ofH z) = g z) : latticeFun k g = G := by
  have hg : IsWeightInvariant k g := by
    have := (lattice_correspondence k).1 G hG
    have e : (fun z => G (LatticeC.ofH z)) = g := funext hGg
    rwa [e] at this
  exact ((lattice_correspondence k).2 g hg).unique (latticeFun_spec hg) ⟨hG, hGg⟩

/-- A scalar multiple of a function homogeneous of degree $k$ is homogeneous of degree $k$. -/
lemma isHomogeneous_smul {k : ℕ} {G : LatticeC → ℂ} (hG : IsHomogeneous k G) (c : ℂ) :
    IsHomogeneous k (c • G) := by
  intro a ha Λ
  simp only [Pi.smul_apply, smul_eq_mul, hG a ha Λ]
  ring

/-- The linear extension of $F$ is compatible with multiplying $F$ by a scalar $c$. -/
lemma extendLin_smul (c : ℂ) (F : LatticeC → ℂ) (x : LatticeDiv) :
    extendLin (c • F) x = c * extendLin F x := by
  unfold extendLin Finsupp.sum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Λ _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The action of an endomorphism on functions on lattices commutes with scalar multiplication. -/
lemma endSmulFun_smul (T : Module.End ℤ LatticeDiv) (c : ℂ) (F : LatticeC → ℂ) :
    endSmulFun T (c • F) = c • endSmulFun T F := by
  funext Λ
  simp only [endSmulFun, extendLin_smul, Pi.smul_apply, smul_eq_mul]

/-- The lattice description of the level one Hecke operator: if $f$ satisfies (3.1b) then so does
$T(n)f$, and $T(n)f$ corresponds to $n^{2k-1}(T(n)\cdot F)$, $F$ the lattice function of $f$. -/
lemma heckeT_one_lattice {k n : ℕ} (hn : 1 ≤ n) {f : ℍ → ℂ} (hf : IsWeightInvariant k f) :
    IsWeightInvariant k (heckeT 1 k n f) ∧
      latticeFun k (heckeT 1 k n f) = (n : ℂ) ^ (2 * k - 1) • endSmulFun (heckeTL n) (latticeFun k f) := by
  obtain ⟨hF, hFf⟩ := latticeFun_spec hf
  have hG : IsHomogeneous k ((n : ℂ) ^ (2 * k - 1) • endSmulFun (heckeTL n) (latticeFun k f)) :=
    isHomogeneous_smul ((prop_4_14 hF).1 n hn) _
  have hGg : ∀ z, ((n : ℂ) ^ (2 * k - 1) • endSmulFun (heckeTL n) (latticeFun k f)) (LatticeC.ofH z) =
      heckeT 1 k n f z := by
    intro z
    rw [← heckeOpLevelOne_eq hn hf]
    rfl
  refine ⟨?_, latticeFun_unique hG hGg⟩
  have := (lattice_correspondence k).1 _ hG
  have e : (fun z => ((n : ℂ) ^ (2 * k - 1) • endSmulFun (heckeTL n) (latticeFun k f))
      (LatticeC.ofH z)) = heckeT 1 k n f := funext hGg
  rwa [e] at this

/-- $(T(n)f)(z) = n^{2k-1}(T(n)\cdot F)(\Lambda(z, 1))$. -/
lemma heckeT_one_apply {k n : ℕ} (hn : 1 ≤ n) {f : ℍ → ℂ} (hf : IsWeightInvariant k f) (z : ℍ) :
    heckeT 1 k n f z = (n : ℂ) ^ (2 * k - 1) * endSmulFun (heckeTL n) (latticeFun k f) (LatticeC.ofH z) := by
  rw [← heckeOpLevelOne_eq hn hf]
  rfl

/-- $(T(m)T(n)f)(z) = m^{2k-1}n^{2k-1}(T(m)\cdot T(n)\cdot F)(\Lambda(z, 1))$. -/
lemma heckeT_one_comp_apply {k m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {f : ℍ → ℂ} (hf : IsWeightInvariant k f)
    (z : ℍ) :
    heckeT 1 k m (heckeT 1 k n f) z = (m : ℂ) ^ (2 * k - 1) * ((n : ℂ) ^ (2 * k - 1) *
      endSmulFun (heckeTL m) (endSmulFun (heckeTL n) (latticeFun k f)) (LatticeC.ofH z)) := by
  obtain ⟨h1, h2⟩ := heckeT_one_lattice hn hf
  rw [heckeT_one_apply hm h1, h2, endSmulFun_smul]
  rfl

/-- The affine map $(a u + b)/d$ with $a, d \ge 1$ sends a point of positive imaginary part to one of positive imaginary part. -/
lemma im_affine_pos' {u : ℂ} (hu : 0 < u.im) {a d : ℕ} (b : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d) :
    0 < (((a : ℂ) * u + b) / d).im := by
  have h1 : (0 : ℝ) < a := by exact_mod_cast ha
  have h2 : (0 : ℝ) < d := by exact_mod_cast hd
  simp [Complex.div_natCast_im]
  positivity

/-- $T(n)f$ is holomorphic if $f$ is. -/
lemma mdiff_heckeT (N k n : ℕ) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (heckeT N k n f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have hterm : ∀ t ∈ (heckeTriples n).filter (fun t ↦ t.1.Coprime N),
      DifferentiableOn ℂ (fun u : ℂ ↦ (t.2.2 : ℂ) ^ (-(2 * k : ℤ)) *
        (f ∘ ofComplex) (((t.1 : ℂ) * u + t.2.1) / t.2.2)) {z : ℂ | 0 < z.im} := by
    intro t ht
    obtain ⟨h1, h2, -, -⟩ := mem_heckeTriples (Finset.mem_filter.mp ht).1
    refine DifferentiableOn.const_mul (hf.comp ?_ ?_) _
    · fun_prop
    · intro u hu
      exact im_affine_pos' hu t.2.1 h1 h2
  refine ((DifferentiableOn.sum hterm).const_mul ((n : ℂ) ^ (2 * k - 1))).congr ?_
  intro u hu
  have hc : ((ofComplex u : ℍ) : ℂ) = u := by
    rw [ofComplex_apply_of_im_pos hu]
  simp only [Function.comp_apply, heckeT, hc, Finset.sum_apply]

/-- $T(n)f$ is zero at $i\infty$ if $f$ is. -/
lemma isZeroAtImInfty_heckeT (N k n : ℕ) {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeT N k n f) := by
  unfold IsZeroAtImInfty ZeroAtFilter at *
  have hterm : ∀ t ∈ (heckeTriples n).filter (fun t ↦ t.1.Coprime N),
      Tendsto (fun z : ℍ ↦ (t.2.2 : ℂ) ^ (-(2 * k : ℤ)) *
        f (ofComplex (((t.1 : ℂ) * z + t.2.1) / t.2.2))) atImInfty (nhds 0) := by
    intro t ht
    obtain ⟨h1, h2, -, -⟩ := mem_heckeTriples (Finset.mem_filter.mp ht).1
    have h1' : (0 : ℝ) < (t.1 : ℝ) / t.2.2 := by
      have a1 : (0 : ℝ) < t.1 := by exact_mod_cast h1
      have a2 : (0 : ℝ) < t.2.2 := by exact_mod_cast h2
      positivity
    have haff : Tendsto (fun z : ℍ ↦ ((t.1 : ℂ) * z + t.2.1) / t.2.2) atImInfty
        (comap Complex.im atTop) := by
      rw [tendsto_comap_iff]
      have h : (Complex.im ∘ fun z : ℍ ↦ ((t.1 : ℂ) * z + t.2.1) / t.2.2) =
          fun z : ℍ ↦ ((t.1 : ℝ) / t.2.2) * z.im := by
        funext z
        simp [Complex.div_natCast_im]
        ring
      rw [h]
      exact tendsto_comap.const_mul_atTop h1'
    have hφ : Tendsto (fun z : ℍ ↦ (ofComplex (((t.1 : ℂ) * z + t.2.1) / t.2.2) : ℍ)) atImInfty
        atImInfty := tendsto_comap_im_ofComplex.comp haff
    have := (hf.comp hφ).const_mul ((t.2.2 : ℂ) ^ (-(2 * k : ℤ)))
    simpa using this
  have key := (tendsto_finsetSum _ hterm).const_mul ((n : ℂ) ^ (2 * k - 1))
  simp only [Finset.sum_const_zero, mul_zero] at key
  exact key

/-- $T(n)$ maps level one cusp forms to level one cusp forms. -/
lemma exists_cuspForm_heckeT {k n : ℕ} (hn : 1 ≤ n) (f : CuspForm 𝒮ℒ (2 * k : ℤ)) :
    ∃ F : CuspForm 𝒮ℒ (2 * k : ℤ), ⇑F = heckeT 1 k n f := by
  have hwi := (heckeT_one_lattice hn (isWeightInvariant_cuspForm f)).1
  have hslash := slash_of_isWeightInvariant hwi
  have hholo := mdiff_heckeT 1 k n (CuspFormClass.holo f)
  have hz := isZeroAtImInfty_heckeT 1 k n (CuspFormClass.zero_at_infty f)
  refine ⟨⟨⟨heckeT 1 k n f, hslash⟩, hholo, fun {c} hc => ?_⟩, rfl⟩
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  have : heckeT 1 k n f ∣[(2 * k : ℤ)] γ = heckeT 1 k n f := hslash _ ⟨γ, rfl⟩
  rw [this]
  exact hz

/-- Theorem 4.7 (a) for level one. -/
lemma heckeT_one_mul {k m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m.Coprime n) {f : ℍ → ℂ}
    (hf : IsWeightInvariant k f) : heckeT 1 k (m * n) f = heckeT 1 k m (heckeT 1 k n f) := by
  funext z
  rw [heckeT_one_apply (Nat.mul_pos hm hn) hf, heckeT_one_comp_apply hm hn hf,
    (prop_4_14 (latticeFun_spec hf).1).2.1 m n hm hn hmn]
  push_cast
  rw [mul_pow]
  ring

/-- Theorem 4.7 (d) for level one. -/
lemma heckeT_one_comm {k m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {f : ℍ → ℂ} (hf : IsWeightInvariant k f) :
    heckeT 1 k m (heckeT 1 k n f) = heckeT 1 k n (heckeT 1 k m f) := by
  have hcomm : heckeTL n ∘ₗ heckeTL m = heckeTL m ∘ₗ heckeTL n := by
    have := cor_4_13.1 (heckeTL n) (cor_4_13.2 n hn) (heckeTL m) (cor_4_13.2 m hm)
    simpa only [Module.End.mul_eq_comp] using this
  funext z
  rw [heckeT_one_comp_apply hm hn hf, heckeT_one_comp_apply hn hm hf, endSmulFun_comp, endSmulFun_comp,
    hcomm]
  ring

/-- Theorem 4.7 (b) for level one, weight $2k$ with $k \ge 1$. -/
lemma heckeT_one_prime_pow {k : ℕ} (hk : 1 ≤ k) {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) {f : ℍ → ℂ}
    (hf : IsWeightInvariant k f) :
    heckeT 1 k p (heckeT 1 k (p ^ r) f) =
      heckeT 1 k (p ^ (r + 1)) f + (p : ℂ) ^ (2 * k - 1) • heckeT 1 k (p ^ (r - 1)) f := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  funext z
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpr : 1 ≤ p ^ (s + 1) := Nat.one_le_pow _ _ hp.pos
  have hps : 1 ≤ p ^ s := Nat.one_le_pow _ _ hp.pos
  have hpr2 : 1 ≤ p ^ (s + 1 + 1) := Nat.one_le_pow _ _ hp.pos
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hc : (p : ℂ) ^ (1 - 2 * (k : ℤ)) = ((p : ℂ) ^ (2 * k - 1))⁻¹ := by
    have : (1 - 2 * (k : ℤ)) = -((2 * k - 1 : ℕ) : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast]
  rw [heckeT_one_comp_apply hp1 hpr hf]
  simp only [Nat.add_sub_cancel, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [heckeT_one_apply hpr2 hf, heckeT_one_apply hps hf,
    (prop_4_14 (latticeFun_spec hf).1).2.2 p (s + 1) hp hr]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc]
  push_cast
  have e : 2 * k - 1 + 1 = 2 * k := by omega
  field_simp
  ring

/-- **Theorem 4.7** for level one (pdf p. 207; "Theorem 4.7 in the case $N = 1$ follows easily from the
Proposition", pdf p. 210): $T(n)$ maps $S_{2k}(\mathrm{SL}_2(\mathbb Z))$ to itself, and (a)
$T(mn) = T(m)T(n)$ for coprime $m, n$; (b) $T(p)T(p^r) = T(p^{r+1}) + p^{2k-1}T(p^{r-1})$; (d) the $T(n)$
commute. ((c) concerns $p \mid N$ and is empty for $N = 1$.) -/
@[kb "milne2006ec" "Ch. V, Theorem 4.7 (N = 1), pdf p. 207"]
theorem thm_4_7_level_one (k : ℕ) :
    (∀ n : ℕ, 1 ≤ n → ∀ f : CuspForm 𝒮ℒ (2 * k : ℤ), ∃ F : CuspForm 𝒮ℒ (2 * k : ℤ), ⇑F = heckeT 1 k n f) ∧
    (∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → m.Coprime n → ∀ f : CuspForm 𝒮ℒ (2 * k : ℤ),
      heckeT 1 k (m * n) f = heckeT 1 k m (heckeT 1 k n f)) ∧
    (∀ (p r : ℕ), p.Prime → 1 ≤ r → ∀ f : CuspForm 𝒮ℒ (2 * k : ℤ),
      heckeT 1 k p (heckeT 1 k (p ^ r) f) =
        heckeT 1 k (p ^ (r + 1)) f + (p : ℂ) ^ (2 * k - 1) • heckeT 1 k (p ^ (r - 1)) f) ∧
    (∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ f : CuspForm 𝒮ℒ (2 * k : ℤ),
      heckeT 1 k m (heckeT 1 k n f) = heckeT 1 k n (heckeT 1 k m f)) := by
  refine ⟨fun n hn f ↦ exists_cuspForm_heckeT hn f,
    fun m n hm hn hmn f ↦ heckeT_one_mul hm hn hmn (isWeightInvariant_cuspForm f), ?_,
    fun m n hm hn f ↦ heckeT_one_comm hm hn (isWeightInvariant_cuspForm f)⟩
  intro p r hp hr f
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [cuspForm_levelOne_weight_zero f]
    simp only [heckeT_zero, smul_zero, add_zero]
  · exact heckeT_one_prime_pow hk hp hr (isWeightInvariant_cuspForm f)

/-- **Theorem 4.7** (pdf p. 207), level $N$, a named statement: the $T(n)$ map $S_{2k}(\Gamma_0(N))$ to itself and
(a) $T(mn) = T(m)T(n)$ for coprime $m$, $n$; (b) $T(p)T(p^r) = T(p^{r+1}) + p^{2k-1}T(p^{r-1})$ for $p \nmid N$;
(c) $T(p^r) = T(p)^r$ for $p \mid N$; (d) all $T(n)$ commute. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.7, pdf p. 207"]
structure Thm4_7 (N k : ℕ) [NeZero N] : Prop where
  maps_to : ∀ n : ℕ, 1 ≤ n → ∀ f : CuspForm (Gamma0GL N) (2 * k : ℤ),
    ∃ F : CuspForm (Gamma0GL N) (2 * k : ℤ), ⇑F = heckeT N k n f
  mul : ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → m.Coprime n → ∀ f : CuspForm (Gamma0GL N) (2 * k : ℤ),
    heckeT N k (m * n) f = heckeT N k m (heckeT N k n f)
  prime_pow : ∀ (p r : ℕ), p.Prime → ¬ p ∣ N → 1 ≤ r → ∀ f : CuspForm (Gamma0GL N) (2 * k : ℤ),
    heckeT N k p (heckeT N k (p ^ r) f) =
      heckeT N k (p ^ (r + 1)) f + (p : ℂ) ^ (2 * k - 1) • heckeT N k (p ^ (r - 1)) f
  prime_pow_dvd : ∀ (p r : ℕ), p.Prime → p ∣ N → 1 ≤ r → ∀ f : CuspForm (Gamma0GL N) (2 * k : ℤ),
    heckeT N k (p ^ r) f = (heckeT N k p)^[r] f
  comm : ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ f : CuspForm (Gamma0GL N) (2 * k : ℤ),
    heckeT N k m (heckeT N k n f) = heckeT N k n (heckeT N k m f)

/-- Theorem 4.7 at level one is proved (`thm_4_7_level_one`). -/
theorem thm4_7_one (k : ℕ) : Thm4_7 1 k := by
  obtain ⟨h1, h2, h3, h4⟩ := thm_4_7_level_one k
  have tr : ∀ f : CuspForm (Gamma0GL 1) (2 * k : ℤ), ∃ f' : CuspForm 𝒮ℒ (2 * k : ℤ), ⇑f' = ⇑f :=
    fun f ↦ (exists_cuspForm_Gamma0GL_one_iff k _).mp ⟨f, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn f
    obtain ⟨f', hf'⟩ := tr f
    obtain ⟨F, hF⟩ := h1 n hn f'
    obtain ⟨F', hF'⟩ := (exists_cuspForm_Gamma0GL_one_iff k _).mpr ⟨F, hF⟩
    exact ⟨F', by rw [hF', hf']⟩
  · intro m n hm hn hmn f
    obtain ⟨f', hf'⟩ := tr f
    have := h2 m n hm hn hmn f'
    rwa [hf'] at this
  · intro p r hp _ hr f
    obtain ⟨f', hf'⟩ := tr f
    have := h3 p r hp hr f'
    rwa [hf'] at this
  · intro p r hp hpN
    exact absurd (Nat.dvd_one.mp hpN) hp.ne_one
  · intro m n hm hn f
    obtain ⟨f', hf'⟩ := tr f
    have := h4 m n hm hn f'
    rwa [hf'] at this

/-- Orthogonality of roots of unity: $\sum_{b < d}(\zeta^m)^b = d$ if $d \mid m$ and $0$ otherwise,
$\zeta = e^{2\pi i/d}$. -/
lemma sum_rootOfUnity_pow (d m : ℕ) (hd : 1 ≤ d) :
    ∑ b ∈ Finset.range d, (cexp (2 * π * I / d) ^ m) ^ b = if d ∣ m then (d : ℂ) else 0 := by
  have hprim := Complex.isPrimitiveRoot_exp d (by omega)
  split_ifs with h
  · have : cexp (2 * π * I / d) ^ m = 1 := (hprim.pow_eq_one_iff_dvd m).mpr h
    simp [this]
  · have h1 : cexp (2 * π * I / d) ^ m ≠ 1 := fun h' => h ((hprim.pow_eq_one_iff_dvd m).mp h')
    rw [geom_sum_eq h1]
    have : (cexp (2 * π * I / d) ^ m) ^ d = 1 := by
      rw [← pow_mul, mul_comm m d, pow_mul, hprim.pow_eq_one, one_pow]
    simp [this]

/-- The sum over $b < d$ of $f((az + b)/d)$ is a $q$-series, for $f = \sum c(m)q^m$:
$\sum_{b < d} f((az+b)/d) = \sum_{a \mid m} d\,c(dm/a)\,q^m$. -/
lemma hasSum_shifts {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hfs : ∀ w : ℍ, HasSum (fun m : ℕ ↦ c m * cexp (2 * π * I * w) ^ m) (f w))
    {a d : ℕ} (ha : 1 ≤ a) (hd : 1 ≤ d) (z : ℍ) :
    HasSum (fun m : ℕ ↦ (if a ∣ m then (d : ℂ) * c (d * (m / a)) else 0) * cexp (2 * π * I * z) ^ m)
      (∑ b ∈ Finset.range d, f (ofComplex (((a : ℂ) * z + b) / d))) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have him : ∀ b : ℕ, 0 < (((a : ℂ) * z + b) / d).im := by
    intro b
    have h1 : (0 : ℝ) < a := by exact_mod_cast ha
    have h2 : (0 : ℝ) < d := by exact_mod_cast hd
    have := z.im_pos
    simp [Complex.div_natCast_im]
    positivity
  set P : ℂ := cexp (2 * π * I * a * z / d) with hP
  set ζ : ℂ := cexp (2 * π * I / d) with hζ
  have hq : ∀ b : ℕ, cexp (2 * π * I * (ofComplex (((a : ℂ) * z + b) / d) : ℍ)) = P * ζ ^ b := by
    intro b
    rw [ofComplex_apply_of_im_pos (him b)]
    simp only [P, ζ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    field_simp
  have h1 : HasSum (fun m : ℕ ↦ ∑ b ∈ Finset.range d, c m * (P * ζ ^ b) ^ m)
      (∑ b ∈ Finset.range d, f (ofComplex (((a : ℂ) * z + b) / d))) := by
    refine hasSum_sum fun b _ ↦ ?_
    have := hfs (ofComplex (((a : ℂ) * z + b) / d))
    rwa [hq b] at this
  have h2 : (fun m : ℕ ↦ ∑ b ∈ Finset.range d, c m * (P * ζ ^ b) ^ m) =
      fun m ↦ c m * P ^ m * (if d ∣ m then (d : ℂ) else 0) := by
    funext m
    rw [← sum_rootOfUnity_pow d m hd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm b m]
    ring
  rw [h2] at h1
  have hPd : P ^ d = cexp (2 * π * I * z) ^ a := by
    simp only [P]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  have h3 : HasSum (fun j : ℕ ↦ (d : ℂ) * c (d * j) * (cexp (2 * π * I * z) ^ a) ^ j)
      (∑ b ∈ Finset.range d, f (ofComplex (((a : ℂ) * z + b) / d))) := by
    have hinj : Function.Injective (fun j : ℕ => d * j) := fun x y hxy => by
      simpa [Nat.pos_iff_ne_zero.mp hd] using hxy
    have := (Function.Injective.hasSum_iff hinj
      (f := fun m : ℕ ↦ c m * P ^ m * (if d ∣ m then (d : ℂ) else 0))
      (by
        intro m hm
        have : ¬ d ∣ m := fun ⟨j, hj⟩ => hm ⟨j, hj.symm⟩
        simp [this])).mpr h1
    convert this using 1
    funext j
    simp only [Function.comp, dvd_mul_right, ite_true]
    rw [pow_mul, hPd, ← pow_mul]
    ring
  have hinj : Function.Injective (fun j : ℕ => a * j) := fun x y hxy => by
    simpa [Nat.pos_iff_ne_zero.mp ha] using hxy
  refine (Function.Injective.hasSum_iff hinj
    (f := fun m : ℕ ↦ (if a ∣ m then (d : ℂ) * c (d * (m / a)) else 0) * cexp (2 * π * I * z) ^ m)
      (by
        intro m hm
        have : ¬ a ∣ m := fun ⟨j, hj⟩ => hm ⟨j, hj.symm⟩
        simp [this])).mp ?_
  convert h3 using 1
  funext j
  simp only [Function.comp, dvd_mul_right, ite_true]
  rw [Nat.mul_div_cancel_left _ (by omega), pow_mul]

/-- The sum over `heckeTriples n`, as a double sum over the divisor pairs and the shifts. -/
lemma sum_heckeTriples {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ × ℕ × ℕ → M) :
    ∑ t ∈ heckeTriples n, F t =
      ∑ ad ∈ Nat.divisorsAntidiagonal n, ∑ b ∈ Finset.range ad.2, F (ad.1, b, ad.2) := by
  unfold heckeTriples
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun ad _ => ?_
    rw [Finset.sum_image]
    intro x _ y _ hxy
    simpa using hxy
  · intro ad _ ad' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro t ht ht'
    simp only [Finset.mem_image, Finset.mem_range] at ht ht'
    obtain ⟨b, _, rfl⟩ := ht
    obtain ⟨b', _, h⟩ := ht'
    apply hne
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.symm h.2.2.symm

/-- `heckeT` as a sum over divisor pairs `(a, d)` with `a` coprime to the level. -/
lemma heckeT_eq (N k n : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    heckeT N k n f z = (n : ℂ) ^ (2 * k - 1) * ∑ ad ∈ Nat.divisorsAntidiagonal n,
      if ad.1.Coprime N then (ad.2 : ℂ) ^ (-(2 * k : ℤ)) *
        ∑ b ∈ Finset.range ad.2, f (ofComplex (((ad.1 : ℂ) * z + b) / ad.2)) else 0 := by
  unfold heckeT
  rw [Finset.sum_filter, sum_heckeTriples]
  congr 1
  refine Finset.sum_congr rfl fun ad _ => ?_
  by_cases h : ad.1.Coprime N <;> simp [h, Finset.mul_sum]

/-- The coefficients of the $q$-expansion of $T(n)f$ in terms of the coefficients $c$ of $f$. -/
noncomputable def heckeCoeff (N k n : ℕ) (c : ℕ → ℂ) (m : ℕ) : ℂ :=
  (n : ℂ) ^ (2 * k - 1) * ∑ ad ∈ Nat.divisorsAntidiagonal n,
    if ad.1.Coprime N then (ad.2 : ℂ) ^ (-(2 * k : ℤ)) *
      (if ad.1 ∣ m then (ad.2 : ℂ) * c (ad.2 * (m / ad.1)) else 0) else 0

/-- The $q$-expansion of $T(n)f$ for $f = \sum c(m)q^m$ (valid at every point of $\mathbb H$). -/
lemma hasSum_heckeT {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hfs : ∀ w : ℍ, HasSum (fun m : ℕ ↦ c m * cexp (2 * π * I * w) ^ m) (f w))
    (N k n : ℕ) (z : ℍ) :
    HasSum (fun m : ℕ ↦ heckeCoeff N k n c m * cexp (2 * π * I * z) ^ m) (heckeT N k n f z) := by
  rw [heckeT_eq]
  have h := hasSum_sum (s := Nat.divisorsAntidiagonal n)
    (f := fun (ad : ℕ × ℕ) (m : ℕ) ↦ if ad.1.Coprime N then (ad.2 : ℂ) ^ (-(2 * k : ℤ)) *
      ((if ad.1 ∣ m then (ad.2 : ℂ) * c (ad.2 * (m / ad.1)) else 0) * cexp (2 * π * I * z) ^ m) else 0)
    (a := fun ad ↦ if ad.1.Coprime N then (ad.2 : ℂ) ^ (-(2 * k : ℤ)) *
        ∑ b ∈ Finset.range ad.2, f (ofComplex (((ad.1 : ℂ) * z + b) / ad.2)) else 0)
    (fun ad had ↦ by
      obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp had
      have ha : 1 ≤ ad.1 := Nat.one_le_iff_ne_zero.mpr (left_ne_zero_of_mul (hmul ▸ hn0))
      have hd : 1 ≤ ad.2 := Nat.one_le_iff_ne_zero.mpr (right_ne_zero_of_mul (hmul ▸ hn0))
      split_ifs
      · exact (hasSum_shifts hfs ha hd z).mul_left _
      · exact hasSum_zero)
  convert h.mul_left ((n : ℂ) ^ (2 * k - 1)) using 1
  funext m
  unfold heckeCoeff
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun ad _ => ?_
  split_ifs <;> ring

/-- The coefficient of $q$ in $T(n)f$ is $c(n)$ (weight $2k$ with $k \ge 1$). -/
lemma heckeCoeff_one (N k : ℕ) (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n) (c : ℕ → ℂ) :
    heckeCoeff N k n c 1 = c n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold heckeCoeff
  rw [Finset.sum_eq_single (1, n)]
  · have hz : (n : ℂ) ^ (-(2 * k : ℤ)) = ((n : ℂ) ^ (2 * k))⁻¹ := by
      rw [zpow_neg, ← zpow_natCast]
      push_cast
      rfl
    obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 1 := ⟨2 * k - 1, by omega⟩
    have hm' : 2 * k - 1 = m := by omega
    simp only [ite_true, dvd_refl, Nat.div_one, mul_one]
    rw [hz, hm', hm, pow_succ, if_pos (Nat.coprime_one_left N)]
    field_simp
  · intro ad had hne
    obtain ⟨hmul, _⟩ := Nat.mem_divisorsAntidiagonal.mp had
    have : ¬ ad.1 ∣ 1 := by
      intro h
      have h1 := Nat.dvd_one.mp h
      apply hne
      rw [h1] at hmul
      ext <;> simp_all
    simp [this]
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, by omega⟩) h

/-- **Theorem 4.8** (pdf p. 207), for every level $N$: if a cusp form $f = \sum c(n)q^n$ of weight $2k$ for
$\Gamma_0(N)$ satisfies $T(n)f = \lambda(n)f$ for all $n \ge 1$, then $c(n) = \lambda(n)c(1)$. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.8, pdf p. 207"]
theorem thm_4_8 {N : ℕ} [NeZero N] {k : ℕ} (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) (lam : ℕ → ℂ)
    (hf : ∀ n : ℕ, 1 ≤ n → heckeT N k n f = lam n • ⇑f) :
    ∀ n : ℕ, 1 ≤ n → (qExpansion 1 f).coeff n = lam n * (qExpansion 1 f).coeff 1 := by
  intro n hn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : ∀ w : ℤ, w = 0 → ∀ g : CuspForm (Gamma0GL N) w, (⇑g : ℍ → ℂ) = 0 := by
      rintro w rfl g
      exact cuspForm_weight_zero_eq_zero g
    rw [h0 (2 * ((0 : ℕ) : ℤ)) (by norm_num) f]
    simp [qExpansion_zero]
  · have hΓ : (1 : ℝ) ∈ (Gamma0GL N).strictPeriods := by
      have := (Gamma0GL N).strictWidthInfty_mem_strictPeriods
      rwa [strictWidthInfty_Gamma0GL] at this
    have hfs : ∀ w : ℍ,
        HasSum (fun m : ℕ ↦ (qExpansion 1 f).coeff m * cexp (2 * π * I * w) ^ m) (f w) := by
      intro w
      have := ModularForm.hasSum_qExpansion (f := f) one_pos hΓ w
      simpa [Function.Periodic.qParam] using this
    set F : CuspForm (Gamma0GL N) (2 * k : ℤ) := lam n • f with hF
    have hFF : (⇑F : ℍ → ℂ) = heckeT N k n f := by
      rw [hf n hn]
      rfl
    have h1 := ModularFormClass.qExpansion_coeff_unique (f := F)
      (c := heckeCoeff N k n (fun m => (qExpansion 1 f).coeff m)) one_pos hΓ (fun τ => by
        have := hasSum_heckeT (c := fun m => (qExpansion 1 f).coeff m) hfs N k n τ
        rw [← hFF] at this
        simpa [Function.Periodic.qParam] using this) 1
    rw [heckeCoeff_one N k hk hn, hF, show (⇑(lam n • f) : ℍ → ℂ) = lam n • ⇑f from rfl,
      ModularForm.qExpansion_smul one_pos hΓ] at h1
    simpa using h1

/-- The $q$-expansion of a cusp form for $\Gamma_0(N)$ converges at every point of $\mathbb H$. -/
lemma hasSum_cuspForm_qExpansion {N : ℕ} [NeZero N] {k : ℕ} (f : CuspForm (Gamma0GL N) (2 * k : ℤ))
    (w : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion 1 f).coeff m * cexp (2 * π * I * w) ^ m) (f w) := by
  have hΓ : (1 : ℝ) ∈ (Gamma0GL N).strictPeriods := by
    have := (Gamma0GL N).strictWidthInfty_mem_strictPeriods
    rwa [strictWidthInfty_Gamma0GL] at this
  have := ModularForm.hasSum_qExpansion (f := f) one_pos hΓ w
  simpa [Function.Periodic.qParam] using this

/-- Running text after Theorem 4.8 (pdf p. 208): a nonzero simultaneous eigenform has $c(1) \ne 0$. -/
theorem coeff_one_ne_zero_of_eigen {N : ℕ} [NeZero N] {k : ℕ} (f : CuspForm (Gamma0GL N) (2 * k : ℤ))
    (hf0 : f ≠ 0) (lam : ℕ → ℂ) (hf : ∀ n : ℕ, 1 ≤ n → heckeT N k n f = lam n • ⇑f) :
    (qExpansion 1 f).coeff 1 ≠ 0 := by
  intro h1
  apply hf0
  have hΓ : (1 : ℝ) ∈ (Gamma0GL N).strictPeriods := by
    have := (Gamma0GL N).strictWidthInfty_mem_strictPeriods
    rwa [strictWidthInfty_Gamma0GL] at this
  have h48 := thm_4_8 f lam hf
  have hzero : ∀ m : ℕ, (qExpansion 1 f).coeff m = 0 := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact CuspFormClass.qExpansion_coeff_zero f one_pos hΓ
    · rw [h48 m hm, h1, mul_zero]
  ext z
  have h := hasSum_cuspForm_qExpansion f z
  simp only [hzero, zero_mul] at h
  simpa using h.unique hasSum_zero

/-- If $a g = b g$ for a nonzero function $g$ then $a = b$. -/
lemma eq_of_smul_eq {g : ℍ → ℂ} (hg : g ≠ 0) {a b : ℂ} (h : a • g = b • g) : a = b := by
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra h'
    exact hg (funext fun z => by_contra fun hz => h' ⟨z, hz⟩)
  have := congrFun h z
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hz this

/-- For an eigenform normalised by $c(1) = 1$, the coefficients are the eigenvalues. -/
lemma coeff_eq_lam {N : ℕ} [NeZero N] {k : ℕ} (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) (lam : ℕ → ℂ)
    (hf : ∀ n : ℕ, 1 ≤ n → heckeT N k n f = lam n • ⇑f) (h1 : (qExpansion 1 f).coeff 1 = 1)
    (n : ℕ) (hn : 1 ≤ n) : (qExpansion 1 f).coeff n = lam n := by
  have := thm_4_8 f lam hf n hn
  rwa [h1, mul_one] at this

/-- The relations of Theorem 4.7 (named) and Theorem 4.8 give the conditions $(*)$ of Proposition 4.5 for the
coefficients of an eigenform normalised by $c(1) = 1$. -/
lemma heckeRecurrence_of_eigen {N : ℕ} [NeZero N] {k : ℕ} (h47 : Thm4_7 N k)
    (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) (lam : ℕ → ℂ)
    (hf : ∀ n : ℕ, 1 ≤ n → heckeT N k n f = lam n • ⇑f) (h1 : (qExpansion 1 f).coeff 1 = 1) :
    HeckeRecurrence N k (fun n ↦ (qExpansion 1 f).coeff n) := by
  have hc : ∀ n, 1 ≤ n → (qExpansion 1 f).coeff n = lam n := coeff_eq_lam f lam hf h1
  have hf0 : (⇑f : ℍ → ℂ) ≠ 0 := by
    intro h0
    have : qExpansion 1 (⇑f : ℍ → ℂ) = 0 := by rw [h0]; exact qExpansion_zero 1
    rw [this] at h1
    simp at h1
  have hpos : ∀ p r : ℕ, p.Prime → 1 ≤ p ^ r := fun p r hp => Nat.one_le_pow _ _ hp.pos
  refine ⟨?_, ?_, ?_⟩
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : n = 1 := by simpa using hmn
      subst this
      simp [h1]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : m = 1 := by simpa using hmn
      subst this
      simp [h1]
    show (qExpansion 1 f).coeff (m * n) = (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n
    rw [hc _ (Nat.mul_pos hm hn), hc m hm, hc n hn]
    have e := h47.mul m n hm hn hmn f
    rw [hf (m * n) (Nat.mul_pos hm hn), hf n hn, heckeT_smul, hf m hm, smul_smul] at e
    exact (eq_of_smul_eq hf0 e).trans (mul_comm _ _)
  · intro p r hp hpN hr
    show (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p ^ r) =
      (qExpansion 1 f).coeff (p ^ (r + 1)) + (p : ℂ) ^ (2 * k - 1) * (qExpansion 1 f).coeff (p ^ (r - 1))
    rw [hc p hp.one_lt.le, hc _ (hpos p r hp), hc _ (hpos p (r + 1) hp), hc _ (hpos p (r - 1) hp)]
    have e := h47.prime_pow p r hp hpN hr f
    rw [hf (p ^ r) (hpos p r hp), heckeT_smul, hf p hp.one_lt.le, smul_smul, hf (p ^ (r + 1)) (hpos p _ hp),
      hf (p ^ (r - 1)) (hpos p _ hp), smul_smul, ← add_smul] at e
    have := eq_of_smul_eq hf0 e
    linear_combination this
  · intro p r hp hpN hr
    show (qExpansion 1 f).coeff (p ^ r) = (qExpansion 1 f).coeff p ^ r
    rw [hc p hp.one_lt.le, hc _ (hpos p r hp)]
    have e := h47.prime_pow_dvd p r hp hpN hr f
    have hit : ∀ j : ℕ, (heckeT N k p)^[j] (⇑f : ℍ → ℂ) = lam p ^ j • ⇑f := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply', ih, heckeT_smul, hf p hp.one_lt.le, smul_smul, pow_succ]
    rw [hit, hf (p ^ r) (hpos p r hp)] at e
    exact eq_of_smul_eq hf0 e

/-- **Corollary 4.9** (pdf p. 208), from Theorem 4.7 (named) and Theorem 4.8: a simultaneous eigenform
$f \in S_{2k}(\Gamma_0(N))$ normalised by $c(1) = 1$ has the Euler product
$L(f, s) = \prod_{p \mid N}(1 - c(p)p^{-s})^{-1}\prod_{p \nmid N}(1 - c(p)p^{-s} + p^{2k-1-2s})^{-1}$
(for $\Re s$ large). -/
@[kb "milne2006ec" "Ch. V, Corollary 4.9, pdf p. 208"]
theorem cor_4_9 {N : ℕ} [NeZero N] {k : ℕ} (hk : 0 < k) (h47 : Thm4_7 N k) (f : CuspForm (Gamma0GL N) (2 * k : ℤ))
    (lam : ℕ → ℂ) (hf : ∀ n : ℕ, 1 ≤ n → heckeT N k n f = lam n • ⇑f) (h1 : (qExpansion 1 f).coeff 1 = 1) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      HasProd (fun p : Nat.Primes ↦ eulerFactor N k (fun n ↦ (qExpansion 1 f).coeff n) p s)
        (ModularForm.L (by positivity : (0 : ℤ) < 2 * k) f s) := by
  have hrec := heckeRecurrence_of_eigen h47 f lam hf h1
  obtain ⟨C, hC⟩ := (cuspForm_coeff_bound_and_hasSum_L hk f).1
  have hgrowth : ∃ C A : ℝ, ∀ n : ℕ, ‖(fun n ↦ (qExpansion 1 f).coeff n) n‖ ≤ C * (n : ℝ) ^ A :=
    ⟨C, k, fun n ↦ by simpa [Real.rpow_natCast] using hC n⟩
  obtain ⟨σ, hσ⟩ := (prop_4_5 N k hk (fun n ↦ (qExpansion 1 f).coeff n) h1 hgrowth).mpr hrec
  have hΓ : (1 : ℝ) ∈ (Gamma0GL N).strictPeriods := by
    have := (Gamma0GL N).strictWidthInfty_mem_strictPeriods
    rwa [strictWidthInfty_Gamma0GL] at this
  have h0 : (qExpansion 1 f).coeff 0 = 0 := CuspFormClass.qExpansion_coeff_zero f one_pos hΓ
  refine ⟨max σ ((k : ℝ) + 1), fun s hs ↦ ?_⟩
  have hs1 : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : (k : ℝ) + 1 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hL : LSeries (fun n ↦ (qExpansion 1 f).coeff n) s = ModularForm.L (by positivity : (0 : ℤ) < 2 * k) f s := by
    have hsum := (cuspForm_coeff_bound_and_hasSum_L hk f).2 s hs2
    rw [← hsum.tsum_eq, LSeries]
    refine tsum_congr fun n ↦ ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, h0]
    · simp [LSeries.term, hn.ne']
  rw [← hL]
  exact hσ s hs1

/-- **Example 4.10** (pdf p. 208): $S_{12}(\mathrm{SL}_2(\mathbb Z))$ has dimension $1$, so $\Delta$ is an eigenform
of all $T(n)$, and Ramanujan's conjecture (b) holds: $\tau(mn) = \tau(m)\tau(n)$ for coprime $m$, $n$, and
$\tau(p)\tau(p^n) = \tau(p^{n+1}) + p^{11}\tau(p^{n-1})$ for $p$ prime, $n \ge 1$ (Mordell 1917). -/
@[kb "milne2006ec" "Ch. V, Example 4.10, pdf p. 208"]
theorem example_4_10 :
    (∀ n : ℕ, 1 ≤ n → ∃ c : ℂ, heckeT 1 6 n discr = c • discr) ∧
    (∀ m n : ℕ, m.Coprime n → tau (m * n) = tau m * tau n) ∧
    (∀ p n : ℕ, p.Prime → 1 ≤ n → tau p * tau (p ^ n) = tau (p ^ (n + 1)) + (p : ℂ) ^ 11 * tau (p ^ (n - 1))) := by
  obtain ⟨D1, hD1⟩ := (exists_cuspForm_Gamma0GL_one_iff 6 ModularForm.discriminant).mpr
    ⟨CuspForm.discriminant, rfl⟩
  have h47 := thm4_7_one 6
  have heig : ∀ n : ℕ, 1 ≤ n → ∃ c : ℂ, heckeT 1 6 n ⇑D1 = c • ⇑D1 := by
    intro n hn
    obtain ⟨F, hF⟩ := h47.maps_to n hn D1
    obtain ⟨G, hG⟩ := (exists_cuspForm_Gamma0GL_one_iff 6 _).mp ⟨F, hF⟩
    obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve G
    refine ⟨c, ?_⟩
    rw [← hG, ← hc, hD1]
    rfl
  choose! lam hlam using heig
  have h1 : (qExpansion 1 (D1 : ℍ → ℂ)).coeff 1 = 1 := by
    rw [hD1]
    exact ModularForm.discriminant_qExpansion_coeff_one
  have hrec := heckeRecurrence_of_eigen h47 D1 lam hlam h1
  have htau : (fun n ↦ (qExpansion 1 (D1 : ℍ → ℂ)).coeff n) = tau := by
    funext n
    rw [hD1]
    rfl
  rw [htau] at hrec
  refine ⟨fun n hn ↦ ?_, fun m n hmn ↦ hrec.1 m n hmn, fun p n hp hn ↦ ?_⟩
  · refine ⟨lam n, ?_⟩
    have hd : discr = ((2 * π : ℂ) ^ 12) • ModularForm.discriminant := by
      funext z
      simp [discr_eq]
    rw [hd, heckeT_smul, ← hD1, hlam n hn, smul_comm]
  · have := hrec.2.1 p n hp (by simpa [Nat.dvd_one] using hp.ne_one) hn
    simpa using this

end NumberFieldKB.MilneEC.V
