import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, III.§3, text pp. 52–53: polynomial mappings

$E,E'$ are finite-dimensional vector spaces over a field $k$ with bases $\mathfrak e=(e_i)_{i\in\iota}$,
$\mathfrak e'=(e'_j)_{j\in\iota'}$ (`b`, `b'`). A map $f:E\to E'$ is a *polynomial mapping* if there are
$P_j\in k[X_i]_{i\in\iota}$ with $f(\sum_ix_ie_i)=\sum_jP_j(x)e'_j$ for all $x\in k^\iota$
(`IsPolynomialMap b b' f`, with the polynomials `P` displayed in `IsPolynomialMapBy b b' P f`).

* `isPolynomialMap_iff_of_basis`: the notion does not depend on the bases.
* `isPolynomialMapBy_unique`: if $k$ is infinite, the $P_j$ are determined by $f$, $\mathfrak e$, $\mathfrak e'$.
* `polyDegree_eq_of_basis`: for $E'=k$ (a *polynomial function*) and $k$ infinite, the total degree of $P$ does not
  depend on $\mathfrak e$ (the *degree* of $f$).
* **`weil_III_3_extension`**: for a field $K\supset k$, $k$ infinite, there is one and only one polynomial mapping
  $E_K\to E'_K$ ($E_K=K\otimes_kE$) which coincides with $f$ on $E$; **`weil_III_3_extension_polys`**: it is given, in
  the bases $\mathfrak e,\mathfrak e'$ of $E_K,E'_K$ over $K$, by the same polynomials $P_j$.

Indices are arbitrary finite types (Weil's $1,\dots,n$; Mathlib's `Fin n` is 0-based).
-/

open TensorProduct

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {k : Type*} [Field k] {E E' : Type*} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']
  {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

/-- $f$ is the polynomial mapping given by the polynomials $P_j$ in the bases `b`, `b'`:
$f(\sum_ix_ie_i)=\sum_jP_j(x)e'_j$. -/
def IsPolynomialMapBy (b : Module.Basis ι k E) (b' : Module.Basis ι' k E') (P : ι' → MvPolynomial ι k)
    (f : E → E') : Prop :=
  ∀ x : ι → k, ∀ j, b'.repr (f (b.equivFun.symm x)) j = MvPolynomial.eval x (P j)

/-- **Weil, III.§3, text p. 52.** $f:E\to E'$ is a *polynomial mapping* (with respect to the bases `b`, `b'`). -/
@[kb "weil1973bnt" "Ch. III, §3, Def. (text p. 52), polynomial mapping"]
def IsPolynomialMap (b : Module.Basis ι k E) (b' : Module.Basis ι' k E') (f : E → E') : Prop :=
  ∃ P : ι' → MvPolynomial ι k, IsPolynomialMapBy b b' P f

/-- Linear substitution polynomials expressing the `b`-coordinates in terms of the `c`-coordinates. -/
def coordSubst {κ : Type*} [Fintype κ] (b : Module.Basis ι k E) (c : Module.Basis κ k E) (i : ι) :
    MvPolynomial κ k :=
  ∑ l, MvPolynomial.C (b.repr (c l) i) * MvPolynomial.X l

/-- Evaluating `coordSubst` computes the `b`-coordinates of the vector with `c`-coordinates `y`. -/
lemma eval_coordSubst {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis ι k E)
    (c : Module.Basis κ k E) (y : κ → k) (i : ι) :
    MvPolynomial.eval y (coordSubst b c i) = b.equivFun (c.equivFun.symm y) i := by
  simp [coordSubst, Module.Basis.equivFun_symm_apply, mul_comm]

/-- `coordSubst` has total degree at most one. -/
lemma totalDegree_coordSubst_le {κ : Type*} [Fintype κ] (b : Module.Basis ι k E) (c : Module.Basis κ k E)
    (i : ι) : (coordSubst b c i).totalDegree ≤ 1 := by
  unfold coordSubst
  refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_C]

/-- Linear substitution does not increase the total degree. -/
lemma totalDegree_bind₁_coordSubst_le {κ : Type*} [Fintype κ] (b : Module.Basis ι k E)
    (c : Module.Basis κ k E) (p : MvPolynomial ι k) :
    (MvPolynomial.bind₁ (coordSubst b c) p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun d hd => ?_
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ d.support, (coordSubst b c i ^ d i).totalDegree
      ≤ ∑ i ∈ d.support, d i := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (MvPolynomial.totalDegree_pow _ _).trans ?_
        simpa using Nat.mul_le_mul_left (d i) (totalDegree_coordSubst_le b c i)
    _ ≤ p.totalDegree := by
        have := MvPolynomial.le_totalDegree hd
        simpa [Finsupp.degree, Finsupp.sum] using this

/-- Change of basis for polynomial maps (one direction). -/
lemma isPolynomialMapBy_change {κ κ' : Type*} [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ']
    {b : Module.Basis ι k E} {b' : Module.Basis ι' k E'} (c : Module.Basis κ k E) (c' : Module.Basis κ' k E')
    {P : ι' → MvPolynomial ι k} {f : E → E'} (h : IsPolynomialMapBy b b' P f) :
    IsPolynomialMapBy c c' (fun j => ∑ j', MvPolynomial.C (c'.repr (b' j') j) *
      MvPolynomial.bind₁ (coordSubst b c) (P j')) f := by
  intro y j
  have h1 : c'.repr (f (c.equivFun.symm y)) j
      = ∑ j', b'.repr (f (c.equivFun.symm y)) j' * c'.repr (b' j') j := by
    generalize f (c.equivFun.symm y) = w
    calc c'.repr w j = c'.repr (∑ j', b'.repr w j' • b' j') j := by rw [b'.sum_repr]
      _ = _ := by
        simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
          Pi.smul_apply, smul_eq_mul]
  rw [h1]
  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun j' _ => ?_
  have h2 : MvPolynomial.eval y (MvPolynomial.bind₁ (coordSubst b c) (P j'))
      = MvPolynomial.eval (b.equivFun (c.equivFun.symm y)) (P j') := by
    have := MvPolynomial.eval₂Hom_bind₁ (RingHom.id k) y (coordSubst b c) (P j')
    simp only [MvPolynomial.coe_eval₂Hom] at this
    change MvPolynomial.eval₂ _ _ _ = MvPolynomial.eval₂ _ _ _ at this
    simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom] at *
    rw [this]
    congr 1
    funext i
    exact eval_coordSubst b c y i
  rw [h2, mul_comm, ← h (b.equivFun (c.equivFun.symm y)) j']
  simp

/-- **Weil, III.§3, text p. 52.** Being a polynomial mapping does not depend on the choice of bases. -/
@[kb "weil1973bnt" "Ch. III, §3, text p. 52, polynomial mappings: independent of the bases"]
theorem isPolynomialMap_iff_of_basis {κ κ' : Type*} [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ']
    (b : Module.Basis ι k E) (b' : Module.Basis ι' k E') (c : Module.Basis κ k E) (c' : Module.Basis κ' k E')
    (f : E → E') : IsPolynomialMap b b' f ↔ IsPolynomialMap c c' f := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨_, isPolynomialMapBy_change c c' hP⟩
  · rintro ⟨P, hP⟩
    exact ⟨_, isPolynomialMapBy_change b b' hP⟩

/-- **Weil, III.§3, text p. 52.** Over an infinite field the polynomials $P_j$ are uniquely determined by $f$ and the
bases. -/
@[kb "weil1973bnt" "Ch. III, §3, text p. 52, polynomial mappings: the polynomials are unique (k infinite)"]
theorem isPolynomialMapBy_unique [Infinite k] (b : Module.Basis ι k E) (b' : Module.Basis ι' k E')
    {P Q : ι' → MvPolynomial ι k} {f : E → E'} (hP : IsPolynomialMapBy b b' P f) (hQ : IsPolynomialMapBy b b' Q f) :
    P = Q := by
  funext j
  refine MvPolynomial.funext fun x => ?_
  rw [← hP x j, ← hQ x j]

/-- One inequality of the degree independence. -/
lemma totalDegree_le_of_basis [Infinite k] {ι₁ κ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype κ]
    [DecidableEq κ] (b : Module.Basis ι₁ k E) (c : Module.Basis κ k E) {f : E → k} {P : MvPolynomial ι₁ k}
    {Q : MvPolynomial κ k} (hP : IsPolynomialMapBy b (Module.Basis.singleton Unit k) (fun _ => P) f)
    (hQ : IsPolynomialMapBy c (Module.Basis.singleton Unit k) (fun _ => Q) f) :
    Q.totalDegree ≤ P.totalDegree := by
  have h := isPolynomialMapBy_change c (Module.Basis.singleton Unit k) hP
  have h2 := isPolynomialMapBy_unique c _ hQ h
  have h3 := congrFun h2 ()
  rw [h3]
  simp only [Fintype.sum_unique, Module.Basis.singleton_apply, Module.Basis.singleton_repr]
  simpa using totalDegree_bind₁_coordSubst_le b c P

/-- **Weil, III.§3, text p. 52.** The degree of a polynomial function $f:E\to k$ (the total degree of its polynomial,
$k$ infinite) does not depend on the basis. -/
@[kb "weil1973bnt" "Ch. III, §3, text p. 52, polynomial functions: the degree is independent of the basis"]
theorem polyDegree_eq_of_basis [Infinite k] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k E) (c : Module.Basis κ k E) {f : E → k} {P : MvPolynomial ι k} {Q : MvPolynomial κ k}
    (hP : IsPolynomialMapBy b (Module.Basis.singleton Unit k) (fun _ => P) f)
    (hQ : IsPolynomialMapBy c (Module.Basis.singleton Unit k) (fun _ => Q) f) :
    P.totalDegree = Q.totalDegree := by
  exact le_antisymm (totalDegree_le_of_basis c b hQ hP) (totalDegree_le_of_basis b c hP hQ)

variable (K : Type*) [Field K] [Algebra k K]

/-- The coordinates of `1 ⊗ x` in the base-changed basis are the images of those of `x`. -/
lemma baseChange_repr_one_tmul (b : Module.Basis ι k E) (x : E) (i : ι) :
    (b.baseChange K).repr (1 ⊗ₜ x) i = algebraMap k K (b.repr x i) := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- The vector of `K ⊗ E` with coordinates `algebraMap ∘ x` is `1 ⊗ (the vector with coordinates x)`. -/
lemma baseChange_equivFun_symm_algebraMap (b : Module.Basis ι k E) (x : ι → k) :
    (b.baseChange K).equivFun.symm (fun i => algebraMap k K (x i)) = 1 ⊗ₜ b.equivFun.symm x := by
  rw [LinearEquiv.symm_apply_eq]
  funext i
  rw [Module.Basis.equivFun_apply, baseChange_repr_one_tmul, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]

/-- Evaluating a mapped polynomial at the image of a point. -/
lemma eval_map_algebraMap (p : MvPolynomial ι k) (x : ι → k) :
    MvPolynomial.eval (fun i => algebraMap k K (x i)) (MvPolynomial.map (algebraMap k K) p)
      = algebraMap k K (MvPolynomial.eval x p) := by
  rw [MvPolynomial.eval_map]
  have := MvPolynomial.eval₂_comp_left (algebraMap k K) (RingHom.id k) x p
  exact this.symm

/-- The explicit extension of a polynomial map to `K ⊗ E`, using the same polynomials. -/
def extMap (b : Module.Basis ι k E) (b' : Module.Basis ι' k E') (P : ι' → MvPolynomial ι k)
    (y : K ⊗[k] E) : K ⊗[k] E' :=
  (b'.baseChange K).equivFun.symm
    (fun j => MvPolynomial.eval ((b.baseChange K).equivFun y) (MvPolynomial.map (algebraMap k K) (P j)))

/-- Coordinates of `extMap`. -/
lemma repr_extMap (b : Module.Basis ι k E) (b' : Module.Basis ι' k E') (P : ι' → MvPolynomial ι k)
    (y : K ⊗[k] E) (j : ι') :
    (b'.baseChange K).repr (extMap K b b' P y) j
      = MvPolynomial.eval ((b.baseChange K).equivFun y) (MvPolynomial.map (algebraMap k K) (P j)) := by
  rw [extMap, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

/-- Any polynomial map over `K` extending `f` has the polynomials `map P`. -/
lemma polys_eq_map [Infinite k] (b : Module.Basis ι k E) (b' : Module.Basis ι' k E')
    {P : ι' → MvPolynomial ι k} {f : E → E'} (hf : IsPolynomialMapBy b b' P f) {F : K ⊗[k] E → K ⊗[k] E'}
    {R : ι' → MvPolynomial ι K} (hR : IsPolynomialMapBy (b.baseChange K) (b'.baseChange K) R F)
    (hFf : ∀ x : E, F (1 ⊗ₜ x) = 1 ⊗ₜ f x) :
    R = fun j => MvPolynomial.map (algebraMap k K) (P j) := by
  funext j
  refine MvPolynomial.funext_set (fun _ => Set.range (algebraMap k K))
    (fun _ => Set.infinite_range_of_injective (algebraMap k K).injective) ?_
  intro z hz
  choose x hx using fun i => hz i (Set.mem_univ i)
  have hz' : z = fun i => algebraMap k K (x i) := funext fun i => (hx i).symm
  subst hz'
  rw [← hR, baseChange_equivFun_symm_algebraMap, hFf, eval_map_algebraMap, baseChange_repr_one_tmul,
    hf]

/-- **Weil, III.§3, text p. 53.** If $k$ is infinite and $K\supset k$ is a field, a polynomial mapping $f:E\to E'$ has
one and only one extension to a polynomial mapping $E_K\to E'_K$, i.e. one coinciding with $f$ on $E$. -/
@[kb "weil1973bnt" "Ch. III, §3, text p. 53, extension of a polynomial mapping to E ⊗ K (unique, k infinite)"]
theorem weil_III_3_extension [Infinite k] (b : Module.Basis ι k E) (b' : Module.Basis ι' k E') {f : E → E'}
    (hf : IsPolynomialMap b b' f) :
    ∃! F : K ⊗[k] E → K ⊗[k] E', IsPolynomialMap (b.baseChange K) (b'.baseChange K) F ∧
      ∀ x : E, F (1 ⊗ₜ x) = 1 ⊗ₜ f x := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨extMap K b b' P, ⟨⟨fun j => MvPolynomial.map (algebraMap k K) (P j), ?_⟩, ?_⟩, ?_⟩
  · intro x j
    rw [repr_extMap, LinearEquiv.apply_symm_apply]
  · intro x
    apply (b'.baseChange K).repr.injective
    ext j
    have hx : (b.baseChange K).equivFun (1 ⊗ₜ x) = fun i => algebraMap k K (b.equivFun x i) := by
      funext i
      rw [Module.Basis.equivFun_apply, baseChange_repr_one_tmul, Module.Basis.equivFun_apply]
    rw [repr_extMap, baseChange_repr_one_tmul, hx, eval_map_algebraMap, ← hP (b.equivFun x) j,
      LinearEquiv.symm_apply_apply]
  · rintro G ⟨⟨R, hR⟩, hG⟩
    have hRP := polys_eq_map K b b' hP hR hG
    subst hRP
    funext y
    apply (b'.baseChange K).repr.injective
    ext j
    have := hR ((b.baseChange K).equivFun y) j
    rw [LinearEquiv.symm_apply_apply] at this
    rw [this, repr_extMap]

/-- **Weil, III.§3, text p. 53.** The extension is given, in the bases $\mathfrak e,\mathfrak e'$ of $E_K,E'_K$ over $K$,
by the same polynomials. -/
@[kb "weil1973bnt" "Ch. III, §3, text p. 53, the extension is given by the same polynomials"]
theorem weil_III_3_extension_polys [Infinite k] (b : Module.Basis ι k E) (b' : Module.Basis ι' k E')
    {P : ι' → MvPolynomial ι k} {f : E → E'} (hf : IsPolynomialMapBy b b' P f) {F : K ⊗[k] E → K ⊗[k] E'}
    (hF : IsPolynomialMap (b.baseChange K) (b'.baseChange K) F) (hFf : ∀ x : E, F (1 ⊗ₜ x) = 1 ⊗ₜ f x) :
    IsPolynomialMapBy (b.baseChange K) (b'.baseChange K) (fun j => MvPolynomial.map (algebraMap k K) (P j)) F := by
  obtain ⟨R, hR⟩ := hF
  rw [← polys_eq_map K b b' hf hR hFf]
  exact hR

end NumberFieldKB.WeilBNT
