import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeTraceSum

/-!
# Weil, *Basic Number Theory*, Chapter IV, §1, Corollary 3 of Theorem 1, finite places (number fields)

$k'/k$ is a finite extension of number fields (here `K/k`), $b$ a basis of $k'$ over $k$, $v$ a finite place of $k$.
The $v$-quasifactor of $(k'/k)_{\mathbb A}$ is $k_v^\iota$ (coordinates $b$), and Weil's isomorphism $\Phi$ of Thm. 1
identifies it with $\prod_{w\mid v}k'_w$ (Cor. 1; QuadFormsKB's `localPiEquiv b v`, $c\mapsto(\sum_ic_ib_i)_{w\mid v}$).

**Cor. 3** (p. 64): for an adele $x'$ of $k'$, the trace and norm of $x'$ over $k_{\mathbb A}$ (those of
$\xi\mapsto x'\xi$ on $(k'/k)_{\mathbb A}$) have $v$-components $y_v=\sum_{w\mid v}\mathrm{Tr}_{k'_w/k_v}(x'_w)$ and
$z_v=\prod_{w\mid v}N_{k'_w/k_v}(x'_w)$. Here, place by place:

* **`weil_IV_1_thm1_cor3_trace`**: for $y\in\prod_{w\mid v}k'_w$, the trace over $k_v$ of multiplication by $y$ on
  $k_v^\iota$ (transported by `localPiEquiv`) is $\sum_{w\mid v}\mathrm{Tr}_{k'_w/k_v}(y_w)$ (QuadFormsKB
  `trace_localPi_conj`);
* **`weil_IV_1_thm1_cor3_norm`**: its determinant is $\prod_{w\mid v}N_{k'_w/k_v}(y_w)$;
* **`weil_IV_1_thm1_cor3_trace_global`**, **`weil_IV_1_thm1_cor3_norm_global`**: for $x\in k'$,
  $\mathrm{Tr}_{k'/k}(x)=\sum_{w\mid v}\mathrm{Tr}_{k'_w/k_v}(x)$ and $N_{k'/k}(x)=\prod_{w\mid v}N_{k'_w/k_v}(x)$ in
  $k_v$.

The general fact used, **`algebraNorm_pi`**: the norm of a finite product of free finite algebras is the product of the
norms. Gluing the $v$-components into an adelic statement (QuadFormsKB's `adeleNorm`) is not packaged here.
-/

open IsDedekindDomain NumberField QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NumberFieldKB.WeilBNT

/-- The determinant of a block-diagonal matrix with blocks of varying sizes is the product of the determinants of
the blocks. -/
theorem det_blockDiagonal'_eq_prod {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (d : ∀ i, Matrix (m i) (m i) R) :
    (Matrix.blockDiagonal' d).det = ∏ i, (d i).det := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun i _ => ?_
  let e : {a : Σ j, m j // a.1 = i} ≃ m i :=
    { toFun := fun a => a.2 ▸ a.1.2
      invFun := fun x => ⟨⟨i, x⟩, rfl⟩
      left_inv := by rintro ⟨⟨j, x⟩, rfl⟩; rfl
      right_inv := fun x => rfl }
  have : Matrix.toSquareBlock (Matrix.blockDiagonal' d) Sigma.fst i = Matrix.reindex e.symm e.symm (d i) := by
    ext a b
    obtain ⟨⟨j, x⟩, hj⟩ := a
    obtain ⟨⟨j', y⟩, hj'⟩ := b
    dsimp only at hj hj'
    subst hj
    subst hj'
    simp [Matrix.toSquareBlock_def, Matrix.blockDiagonal'_apply, e]
  rw [this, Matrix.det_reindex_self]

/-- The norm of a product algebra $A\times B$ is the product of the norms. -/
theorem algebraNorm_prod {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B] (x : A × B) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_prodMap]
  congr 1

/-- The norm of a finite product of free finite algebras is the product of the norms. -/
theorem algebraNorm_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (x : ∀ i, A i) : Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  classical
  let s : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex R (A i)) R (A i) := fun i => Module.Free.chooseBasis R (A i)
  have h : Algebra.leftMulMatrix (Pi.basis s) x = Matrix.blockDiagonal' fun i => Algebra.leftMulMatrix (s i) (x i) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.blockDiagonal'_apply]
    by_cases hij : i = j
    · subst hij
      simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply, Pi.mul_apply]
    · simp [hij, Pi.basis_repr, Pi.basis_apply, Pi.mul_apply]
  rw [Algebra.norm_eq_matrix_det (Pi.basis s), h, det_blockDiagonal'_eq_prod]
  exact Finset.prod_congr rfl fun i _ => (Algebra.norm_eq_matrix_det (s i) (x i)).symm

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] (b : Module.Basis ι k K) (v : HeightOneSpectrum (𝓞 k))

/-- **Weil, IV.§1, Cor. 3 of Thm. 1**, trace, at a finite place $v$: the trace of multiplication by
$y\in\prod_{w\mid v}k'_w$ on the $v$-quasifactor $k_v^\iota$ of $(k'/k)_{\mathbb A}$ is
$\sum_{w\mid v}\mathrm{Tr}_{k'_w/k_v}(y_w)$. -/
@[kb "weil1973bnt" "Ch. IV, §1, Cor. 3 of Thm. 1 (p. 64), trace, finite places, number field case"]
theorem weil_IV_1_thm1_cor3_trace (y : PlaceProd (K := K) v) :
    LinearMap.trace (v.adicCompletion k) (ι → v.adicCompletion k)
        ((localPiEquiv b v).symm.conj (LinearMap.mulLeft (v.adicCompletion k) y)) =
      ∑ w : PlaceSet (K := K) v, Algebra.trace (v.adicCompletion k) (w.1.adicCompletion K) (y w) :=
  trace_localPi_conj b v y

/-- **Weil, IV.§1, Cor. 3 of Thm. 1**, norm, at a finite place $v$: the determinant of multiplication by
$y\in\prod_{w\mid v}k'_w$ on the $v$-quasifactor $k_v^\iota$ of $(k'/k)_{\mathbb A}$ is
$\prod_{w\mid v}N_{k'_w/k_v}(y_w)$. -/
@[kb "weil1973bnt" "Ch. IV, §1, Cor. 3 of Thm. 1 (p. 64), norm, finite places, number field case"]
theorem weil_IV_1_thm1_cor3_norm (y : PlaceProd (K := K) v) :
    LinearMap.det ((localPiEquiv b v).symm.conj (LinearMap.mulLeft (v.adicCompletion k) y)) =
      ∏ w : PlaceSet (K := K) v, Algebra.norm (v.adicCompletion k) (y w) := by
  classical
  rw [LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]
  change Algebra.norm (v.adicCompletion k) (y : PlaceProd (K := K) v) = _
  exact algebraNorm_pi y

/-- **Weil, IV.§1, Cor. 3 of Thm. 1**, on $k'$: $\mathrm{Tr}_{k'/k}(x)=\sum_{w\mid v}\mathrm{Tr}_{k'_w/k_v}(x)$ in
$k_v$. -/
theorem weil_IV_1_thm1_cor3_trace_global (x : K) :
    algebraMap k (v.adicCompletion k) (Algebra.trace k K x) =
      ∑ w : PlaceSet (K := K) v, Algebra.trace (v.adicCompletion k) (w.1.adicCompletion K) (x : w.1.adicCompletion K) :=
  trace_eq_sum_localTrace v x

/-- **Weil, IV.§1, Cor. 3 of Thm. 1**, on $k'$: $N_{k'/k}(x)=\prod_{w\mid v}N_{k'_w/k_v}(x)$ in $k_v$. -/
@[kb "weil1973bnt" "Ch. IV, §1, Cor. 3 of Thm. 1 (p. 64), norm of elements of k', number field case"]
theorem weil_IV_1_thm1_cor3_norm_global (x : K) :
    algebraMap k (v.adicCompletion k) (Algebra.norm k x) =
      ∏ w : PlaceSet (K := K) v, Algebra.norm (v.adicCompletion k) (x : w.1.adicCompletion K) := by
  classical
  have hconj : (localPiEquiv (Module.finBasis k K) v).symm.conj
      (LinearMap.mulLeft (v.adicCompletion k) (fun w : PlaceSet (K := K) v => ((x : K) : w.1.adicCompletion K))) =
      Matrix.toLin' ((Algebra.leftMulMatrix (Module.finBasis k K) x).map (algebraMap k (v.adicCompletion k))) := by
    refine LinearMap.ext fun c => ?_
    rw [LinearEquiv.conj_apply_apply, Matrix.toLin'_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_eq]
    exact (localPi_mulVec (Module.finBasis k K) v x c).symm
  rw [← weil_IV_1_thm1_cor3_norm (Module.finBasis k K) v, hconj, LinearMap.det_toLin',
    Algebra.norm_eq_matrix_det (Module.finBasis k K), RingHom.map_det]
  rfl

end NumberFieldKB.WeilBNT
