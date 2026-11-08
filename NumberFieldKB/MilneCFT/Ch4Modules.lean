import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, Class Field Theory, Chapter IV, §1 and §5: modules over simple and semisimple algebras

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV ("Brauer groups").  This file proves the items of §1 and §5 about modules that Mathlib
does not state: uniqueness of the decomposition into simple modules (Cor. 1.3), "modules of the
same dimension over a simple algebra are isomorphic" (Cor. 1.21, second assertion), uniqueness
in Wedderburn's theorem (Cor. 1.22) and modules over a product of simple algebras (Thm. 5.5).

Conventions.  Milne's $A$-modules are finitely generated left modules over a finite-dimensional
algebra $A$ over a field $k$.  Results that hold over any ring are stated over a ring; the
docstrings say where Milne's finiteness is used.  Locators give the printed page of the book
(printed page = pdf page − 9).
-/

namespace NumberFieldKB.MilneCFT.Ch4

universe u v w

/-- Splitting off the `p`-th factor of a finite product of modules. -/
def piSplit {R : Type u} [Ring R] {k : ℕ} (V : Fin (k + 1) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (p : Fin (k + 1)) :
    (Π i, V i) ≃ₗ[R] V p × Π i, V (p.succAbove i) where
  toFun f := (f p, fun i => f (p.succAbove i))
  invFun x := Fin.insertNth p x.1 x.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Fin.insertNth_self_removeNth p f
  right_inv x := by simp

/-- Schur complement: if `V0 × X ≃ T × Z` and the `V0 → T` block is bijective, then `X ≃ Z`. -/
theorem schur_complement {R : Type u} [Ring R] {V0 : Type v} {T : Type w} {X Z : Type*}
    [AddCommGroup V0] [Module R V0] [AddCommGroup T] [Module R T] [AddCommGroup X] [Module R X]
    [AddCommGroup Z] [Module R Z] (f : (V0 × X) ≃ₗ[R] (T × Z))
    (ha : Function.Bijective (fun v : V0 => (f (v, 0)).1)) : Nonempty (X ≃ₗ[R] Z) := by
  let a : V0 →ₗ[R] T := LinearMap.fst R T Z ∘ₗ f.toLinearMap ∘ₗ LinearMap.inl R V0 X
  have ha' : Function.Bijective a := ha
  let aeq : V0 ≃ₗ[R] T := LinearEquiv.ofBijective a ha'
  let b : X →ₗ[R] T := LinearMap.fst R T Z ∘ₗ f.toLinearMap ∘ₗ LinearMap.inr R V0 X
  let c : V0 →ₗ[R] Z := LinearMap.snd R T Z ∘ₗ f.toLinearMap ∘ₗ LinearMap.inl R V0 X
  let d : X →ₗ[R] Z := LinearMap.snd R T Z ∘ₗ f.toLinearMap ∘ₗ LinearMap.inr R V0 X
  let d' : X →ₗ[R] Z := d - c ∘ₗ aeq.symm.toLinearMap ∘ₗ b
  have hf : ∀ v x, f (v, x) = (a v + b x, c v + d x) := by
    intro v x
    have : (v, x) = (v, 0) + (0, x) := by simp
    rw [this, map_add]
    refine Prod.ext ?_ ?_ <;> simp [a, b, c, d]
  have hd' : ∀ x, d' x = d x - c (aeq.symm (b x)) := fun x => rfl
  have haeq : ∀ y, a (aeq.symm y) = y := fun y => aeq.apply_symm_apply y
  have hinj : Function.Injective d' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [hd'] at hx
    have h1 : f (-(aeq.symm (b x)), x) = 0 := by
      rw [hf, map_neg, haeq, map_neg]
      refine Prod.ext ?_ ?_
      · simp
      · simpa [neg_add_eq_sub] using hx
    have := f.injective (h1.trans (map_zero f).symm)
    exact (Prod.ext_iff.mp this).2
  have hsurj : Function.Surjective d' := by
    intro z
    obtain ⟨⟨v, x⟩, hvx⟩ := f.surjective (0, z)
    rw [hf] at hvx
    have h1 : a v + b x = 0 := congrArg Prod.fst hvx
    have h2 : c v + d x = z := congrArg Prod.snd hvx
    have h3 : v = -(aeq.symm (b x)) := by
      have h4 : a v = - b x := eq_neg_of_add_eq_zero_left h1
      have h5 : aeq v = - b x := h4
      rw [← map_neg, ← h5, aeq.symm_apply_apply]
    refine ⟨x, ?_⟩
    rw [hd', ← h2, h3]
    simp [sub_eq_neg_add]
  exact ⟨LinearEquiv.ofBijective d' ⟨hinj, hsurj⟩⟩

/-- Krull-Schmidt for products of simple modules, by induction on the number of factors. -/
theorem krull_schmidt_aux {R : Type u} [Ring R] : ∀ (r s : ℕ) (V : Fin r → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, IsSimpleModule R (V i)]
    (W : Fin s → Type v) [∀ j, AddCommGroup (W j)] [∀ j, Module R (W j)]
    [∀ j, IsSimpleModule R (W j)] (_ : (Π i, V i) ≃ₗ[R] (Π j, W j)),
    r = s ∧ ∃ σ : Fin r ≃ Fin s, ∀ i, Nonempty (V i ≃ₗ[R] W (σ i)) := by
  intro r
  induction r with
  | zero =>
    intro s V _ _ _ W _ _ _ e
    cases s with
    | zero => exact ⟨rfl, Equiv.refl _, fun i => i.elim0⟩
    | succ s' =>
      exfalso
      have : Nontrivial (Π j, W j) := by
        have : ∀ j, Nontrivial (W j) := fun j => IsSimpleModule.nontrivial R (W j)
        infer_instance
      have : Subsingleton (Π i : Fin 0, V i) := inferInstance
      have : Subsingleton (Π j, W j) := e.symm.injective.subsingleton
      exact not_subsingleton (Π j, W j) ‹_›
  | succ k ih =>
    intro s V _ _ _ W _ _ _ e
    cases s with
    | zero =>
      exfalso
      have : Nontrivial (Π i, V i) := by
        have : ∀ i, Nontrivial (V i) := fun i => IsSimpleModule.nontrivial R (V i)
        infer_instance
      have : Subsingleton (Π j : Fin 0, W j) := inferInstance
      have : Subsingleton (Π i, V i) := e.injective.subsingleton
      exact not_subsingleton (Π i, V i) ‹_›
    | succ s' =>
      have : Nontrivial (V 0) := IsSimpleModule.nontrivial R (V 0)
      let f : (V 0 × Π i, V ((0 : Fin (k + 1)).succAbove i)) ≃ₗ[R] Π j, W j :=
        (piSplit V 0).symm.trans e
      let q : V 0 →ₗ[R] Π j, W j := f.toLinearMap ∘ₗ LinearMap.inl R _ _
      have hq : Function.Injective q := f.injective.comp LinearMap.inl_injective
      obtain ⟨v, hv⟩ := exists_ne (0 : V 0)
      have hqv : q v ≠ 0 := fun h => hv (hq (h.trans (map_zero q).symm))
      obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hqv
      let a : V 0 →ₗ[R] W j0 := LinearMap.proj j0 ∘ₗ q
      have ha0 : a ≠ 0 := fun h => hj0 (by
        have := LinearMap.congr_fun h v
        simpa [a] using this)
      have hab : Function.Bijective a := LinearMap.bijective_of_ne_zero ha0
      let f' : (V 0 × Π i, V ((0 : Fin (k + 1)).succAbove i)) ≃ₗ[R]
          (W j0 × Π i, W (j0.succAbove i)) := f.trans (piSplit W j0)
      have hbij : Function.Bijective (fun v : V 0 => (f' (v, 0)).1) := hab
      obtain ⟨e'⟩ := schur_complement f' hbij
      obtain ⟨hks, σ', hσ'⟩ := ih s' (fun i => V ((0 : Fin (k + 1)).succAbove i))
        (fun i => W (j0.succAbove i)) e'
      refine ⟨by omega, ?_⟩
      let σ : Fin (k + 1) ≃ Fin (s' + 1) :=
        (finSuccEquiv' 0).trans ((Equiv.optionCongr σ').trans (finSuccEquiv' j0).symm)
      have hσ0 : σ 0 = j0 := by simp [σ, finSuccEquiv'_at]
      have hσs : ∀ i, σ ((0 : Fin (k + 1)).succAbove i) = j0.succAbove (σ' i) := by
        intro i
        simp only [σ, Equiv.trans_apply, finSuccEquiv'_succAbove, Equiv.optionCongr_apply,
          Option.map_some, finSuccEquiv'_symm_some]
      refine ⟨σ, fun i => ?_⟩
      rcases Fin.eq_self_or_eq_succAbove 0 i with rfl | ⟨i', rfl⟩
      · rw [hσ0]; exact ⟨(LinearEquiv.ofBijective a hab)⟩
      · rw [hσs]; exact hσ' i'

/-- Corollary 1.3 of Milne: if a module is isomorphic to two direct sums
$V_1 \oplus \dots \oplus V_r \cong W_1 \oplus \dots \oplus W_s$ of simple modules, then $r = s$ and
there is a permutation $\sigma$ with $V_i \cong W_{\sigma(i)}$ for all $i$.

Milne's indices $1, \dots, r$ are `Fin r` here (0-based).  Stated for modules over any ring (the
direct sums are finite, so they are products). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 1.3, p. 120"]
theorem cor_1_3 {R : Type u} [Ring R] {r s : ℕ} (V : Fin r → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, IsSimpleModule R (V i)]
    (W : Fin s → Type v) [∀ j, AddCommGroup (W j)] [∀ j, Module R (W j)]
    [∀ j, IsSimpleModule R (W j)] (e : (Π i, V i) ≃ₗ[R] (Π j, W j)) :
    r = s ∧ ∃ σ : Fin r ≃ Fin s, ∀ i, Nonempty (V i ≃ₗ[R] W (σ i)) :=
  krull_schmidt_aux r s V W e

/-- Theorem 1.19 (a) ⇒ (c) of Milne, in the form used later: over a simple artinian ring (for
instance a finite-dimensional simple algebra over a field), any two simple modules are
isomorphic. -/
theorem nonempty_linearEquiv_of_isSimpleRing {R : Type u} [Ring R] [IsSimpleRing R]
    [IsArtinianRing R] (M : Type v) (N : Type w) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] [AddCommGroup N] [Module R N] [IsSimpleModule R N] :
    Nonempty (M ≃ₗ[R] N) := by
  have h1 : IsSimpleModule R (LinearMap.range (LinearMap.inl R M N)) :=
    IsSimpleModule.congr (LinearEquiv.ofInjective _ LinearMap.inl_injective).symm
  have h2 : IsSimpleModule R (LinearMap.range (LinearMap.inr R M N)) :=
    IsSimpleModule.congr (LinearEquiv.ofInjective _ LinearMap.inr_injective).symm
  obtain ⟨e⟩ := (IsSimpleRing.isIsotypic R (M × N) (LinearMap.range (LinearMap.inl R M N))
    (LinearMap.range (LinearMap.inr R M N)))
  exact ⟨(LinearEquiv.ofInjective _ LinearMap.inl_injective).trans
    (e.symm.trans (LinearEquiv.ofInjective _ LinearMap.inr_injective).symm)⟩

/-- Decomposition data: a nontrivial finite module over a simple artinian ring. -/
theorem decomp_aux {K : Type u} [Field K] {A : Type v} [Ring A] [Algebra K A] [IsSimpleRing A]
    [FiniteDimensional K A] (M : Type w) [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [FiniteDimensional K M] [Nontrivial M] :
    ∃ (n : ℕ) (S : Submodule A M), IsSimpleModule A S ∧ 0 < n ∧
      Nonempty (M ≃ₗ[A] Fin n → S) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite K A M
  obtain ⟨n, hn, S, hS, e⟩ := (IsSimpleRing.isIsotypic A M).linearEquiv_fun
  exact ⟨n, S, hS, Nat.pos_of_ne_zero hn.out, e⟩

/-- Corollary 1.21 of Milne, second assertion: over a simple finite-dimensional $K$-algebra $A$,
two $A$-modules that are finite dimensional over $K$ of the same dimension are isomorphic. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 1.21 (second assertion), p. 125"]
theorem cor_1_21 {K : Type u} [Field K] {A : Type v} [Ring A] [Algebra K A] [IsSimpleRing A]
    [FiniteDimensional K A] (M N : Type w) [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [FiniteDimensional K M] [AddCommGroup N] [Module A N] [Module K N]
    [IsScalarTower K A N] [FiniteDimensional K N]
    (h : Module.finrank K M = Module.finrank K N) : Nonempty (M ≃ₗ[A] N) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  by_cases hM : Subsingleton M
  · have h0 : Module.finrank K M = 0 := Module.finrank_zero_of_subsingleton
    rw [h0] at h
    have : Subsingleton N := Module.finrank_zero_iff.mp h.symm
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    have hN : Nontrivial N := by
      by_contra hc
      have : Subsingleton N := not_nontrivial_iff_subsingleton.mp hc
      have := Module.finrank_zero_of_subsingleton (R := K) (M := N)
      have hp := Module.finrank_pos (R := K) (M := M)
      omega
    obtain ⟨n, S, hS, hn, ⟨e⟩⟩ := decomp_aux (K := K) (A := A) M
    obtain ⟨m, S', hS', hm, ⟨e'⟩⟩ := decomp_aux (K := K) (A := A) N
    obtain ⟨f⟩ := nonempty_linearEquiv_of_isSimpleRing (R := A) S S'
    have hfin : Module.Finite K S := Module.Finite.of_injective
      ((S.subtype).restrictScalars K) Subtype.val_injective
    have hfin' : Module.Finite K S' := Module.Finite.of_injective
      ((S'.subtype).restrictScalars K) Subtype.val_injective
    have hnt : Nontrivial S := IsSimpleModule.nontrivial A S
    have hpos : 0 < Module.finrank K S := Module.finrank_pos
    have h1 : Module.finrank K M = n * Module.finrank K S := by
      rw [(e.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]
      simp
    have h2 : Module.finrank K N = m * Module.finrank K S' := by
      rw [(e'.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]
      simp
    have h3 : Module.finrank K S = Module.finrank K S' := (f.restrictScalars K).finrank_eq
    rw [h1, h2, ← h3] at h
    have hnm : n = m := Nat.eq_of_mul_eq_mul_right hpos h
    subst hnm
    exact ⟨e.trans ((LinearEquiv.piCongrRight fun _ => f).trans e'.symm)⟩

theorem exists_mulVec_eq {D : Type u} [DivisionRing D] {n : Type v} [Fintype n] [DecidableEq n]
    (v w : n → D) (hv : v ≠ 0) : ∃ B : Matrix n n D, B.mulVec v = w := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  refine ⟨Matrix.of fun i k => if k = j then w i * (v j)⁻¹ else 0, ?_⟩
  have hj' : v j ≠ 0 := hj
  ext i
  simp [Matrix.mulVec, dotProduct, hj']

theorem isSimpleModule_of_transitive {R : Type u} [Ring R] {M : Type v} [AddCommGroup M]
    [Module R M] [Nontrivial M] (h : ∀ v w : M, v ≠ 0 → ∃ a : R, a • v = w) :
    IsSimpleModule R M := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨‹_›, fun x hx w => ?_⟩
  obtain ⟨a, ha⟩ := h x w hx
  exact ⟨a, by simpa using ha⟩

theorem isSimpleModule_pi_matrix (D : Type u) [DivisionRing D] (n : Type v) [Fintype n]
    [DecidableEq n] [Nonempty n] : IsSimpleModule (Matrix n n D) (n → D) :=
  isSimpleModule_of_transitive fun v w hv => by
    obtain ⟨B, hB⟩ := exists_mulVec_eq v w hv
    exact ⟨B, hB⟩

theorem commute_eq_rmul {D : Type u} [DivisionRing D] {m : Type v} [Fintype m] [DecidableEq m]
    (i0 : m) (g : (m → D) → (m → D))
    (hg : ∀ (b : Matrix m m D) (w : m → D), g (b.mulVec w) = b.mulVec (g w)) :
    ∃ c : D, ∀ w, g w = fun i => w i * c := by
  set ε : m → D := Pi.single i0 1 with hε
  refine ⟨g ε i0, fun w => ?_⟩
  set P : Matrix m m D := Matrix.of fun i k => if k = i0 then w i else 0 with hP
  have h3 : P.mulVec ε = w := by
    ext i; simp [hP, hε, Matrix.mulVec, dotProduct]
  have h5 : g w = P.mulVec (g ε) := by rw [← h3, hg]
  rw [h5]
  ext i
  simp [hP, Matrix.mulVec, dotProduct]

theorem rmul_mulVec_comm {D : Type u} [Ring D] {m : Type v} [Fintype m] (b : Matrix m m D)
    (u : m → D) (d : D) :
    (fun i => (b.mulVec u) i * d) = b.mulVec (fun i => u i * d) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

/-- Corollary 1.22 of Milne: in Wedderburn's theorem $A \cong M_n(D)$ (Thm. 1.17), the integer
$n$ is determined by $A$, and the division algebra $D$ is determined up to isomorphism: if
$M_n(D) \cong M_m(D')$ as $K$-algebras with $n, m \neq 0$ and $D, D'$ division algebras, then
$n = m$ and $D \cong D'$.  (Finite dimension of $D, D'$ over $K$ is Milne's convention; the
proof uses $D^{\mathrm{opp}} \cong \mathrm{End}_A(S)$ for a simple $A$-module $S$.) -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 1.22, p. 125"]
theorem cor_1_22 {K : Type u} [Field K] (D : Type v) (D' : Type w) [DivisionRing D]
    [Algebra K D] [FiniteDimensional K D] [DivisionRing D'] [Algebra K D']
    [FiniteDimensional K D'] {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (e : Matrix (Fin n) (Fin n) D ≃ₐ[K] Matrix (Fin m) (Fin m) D') :
    n = m ∧ Nonempty (D ≃ₐ[K] D') := by
  classical
  have : NeZero n := ⟨hn⟩
  have : NeZero m := ⟨hm⟩
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
  have : IsArtinianRing (Matrix (Fin n) (Fin n) D) := IsArtinianRing.of_finite K _
  let σ : Matrix (Fin n) (Fin n) D →+* Matrix (Fin m) (Fin m) D' := e.toAlgHom.toRingHom
  letI : Module (Matrix (Fin n) (Fin n) D) (Fin m → D') := Module.compHom _ σ
  have hsmul : ∀ (a : Matrix (Fin n) (Fin n) D) (w : Fin m → D'),
      a • w = (σ a).mulVec w := fun a w => rfl
  have : IsSimpleModule (Matrix (Fin n) (Fin n) D) (Fin m → D') := by
    refine isSimpleModule_of_transitive fun v w hv => ?_
    obtain ⟨B, hB⟩ := exists_mulVec_eq v w hv
    refine ⟨e.symm B, ?_⟩
    rw [hsmul]
    show (e (e.symm B)).mulVec v = w
    simpa using hB
  have : IsSimpleModule (Matrix (Fin n) (Fin n) D) (Fin n → D) := isSimpleModule_pi_matrix D _
  obtain ⟨φ⟩ := nonempty_linearEquiv_of_isSimpleRing (R := Matrix (Fin n) (Fin n) D)
    (Fin n → D) (Fin m → D')
  have hφ : ∀ (a : Matrix (Fin n) (Fin n) D) (v : Fin n → D),
      φ (a.mulVec v) = (σ a).mulVec (φ v) :=
    fun a v => φ.map_smul a v
  have hφK : ∀ (k : K) (v : Fin n → D), φ (k • v) = k • φ v := by
    intro k v
    have h1 : k • v = algebraMap K (Matrix (Fin n) (Fin n) D) k • v :=
      (algebraMap_smul _ k v).symm
    rw [h1, φ.map_smul]
    show (σ (algebraMap K (Matrix (Fin n) (Fin n) D) k)).mulVec (φ v) = _
    have h2 : σ (algebraMap K (Matrix (Fin n) (Fin n) D) k) = algebraMap K _ k := e.commutes k
    rw [h2, ← Matrix.smul_eq_mulVec]
    exact algebraMap_smul (Matrix (Fin m) (Fin m) D') k (φ v)
  let φK : (Fin n → D) ≃ₗ[K] (Fin m → D') :=
    { φ.toAddEquiv with map_smul' := hφK }
  -- dimension count
  have hdD : 0 < Module.finrank K D := Module.finrank_pos
  have hdD' : 0 < Module.finrank K D' := Module.finrank_pos
  have f1 : Module.finrank K (Fin n → D) = n * Module.finrank K D := by
    simp [Module.finrank_pi_fintype]
  have f2 : Module.finrank K (Fin m → D') = m * Module.finrank K D' := by
    simp [Module.finrank_pi_fintype]
  have f3 : Module.finrank K (Matrix (Fin n) (Fin n) D) = n * n * Module.finrank K D := by
    simp [Module.finrank_matrix]
  have f4 : Module.finrank K (Matrix (Fin m) (Fin m) D') = m * m * Module.finrank K D' := by
    simp [Module.finrank_matrix]
  have h1 : n * Module.finrank K D = m * Module.finrank K D' := by
    rw [← f1, ← f2]; exact φK.finrank_eq
  have h2 : n * n * Module.finrank K D = m * m * Module.finrank K D' := by
    rw [← f3, ← f4]; exact e.toLinearEquiv.finrank_eq
  have hX : 0 < m * Module.finrank K D' := Nat.mul_pos (Nat.pos_of_ne_zero hm) hdD'
  have h3 : m * (m * Module.finrank K D') = n * (m * Module.finrank K D') := by
    calc m * (m * Module.finrank K D') = m * m * Module.finrank K D' := by ring
      _ = n * n * Module.finrank K D := h2.symm
      _ = n * (n * Module.finrank K D) := by ring
      _ = n * (m * Module.finrank K D') := by rw [h1]
  have hnm : n = m := (Nat.eq_of_mul_eq_mul_right hX h3).symm
  refine ⟨hnm, ?_⟩
  have hd : Module.finrank K D = Module.finrank K D' := by
    rw [hnm] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h1
  -- the induced map on D
  let i0 : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  have hg : ∀ (d : D) (b : Matrix (Fin m) (Fin m) D') (w : Fin m → D'),
      (fun w => φ (fun i => (φ.symm w) i * d)) (b.mulVec w) =
        b.mulVec ((fun w => φ (fun i => (φ.symm w) i * d)) w) := by
    intro d b w
    have hb : σ (e.symm b) = b := by
      show e (e.symm b) = b
      simp
    have hs : φ.symm (b.mulVec w) = (e.symm b).mulVec (φ.symm w) := by
      apply φ.injective
      rw [hφ, hb]; simp
    simp only
    rw [hs, rmul_mulVec_comm, hφ, hb]
  choose Φ hΦ using fun d : D =>
    commute_eq_rmul i0 (fun w => φ (fun i => (φ.symm w) i * d)) (hg d)
  have hP : ∀ (d : D) (v : Fin n → D),
      φ (fun i => v i * d) = fun i => φ v i * Φ d := by
    intro d v
    have := hΦ d (φ v)
    simpa using this
  have key : ∀ c c' : D', (∀ v : Fin n → D, (fun i => φ v i * c) = fun i => φ v i * c') →
      c = c' := by
    intro c c' h
    have := congrFun (h (φ.symm (fun _ => 1))) i0
    simpa using this
  have hadd : ∀ d₁ d₂ : D, Φ (d₁ + d₂) = Φ d₁ + Φ d₂ := by
    intro d₁ d₂
    apply key
    intro v
    rw [← hP]
    have : (fun i => v i * (d₁ + d₂)) = (fun i => v i * d₁) + (fun i => v i * d₂) := by
      ext i; simp [mul_add]
    rw [this, map_add, hP, hP]
    ext i; simp [mul_add]
  have hmul : ∀ d₁ d₂ : D, Φ (d₁ * d₂) = Φ d₁ * Φ d₂ := by
    intro d₁ d₂
    apply key
    intro v
    rw [← hP]
    have : (fun i => v i * (d₁ * d₂)) = (fun i => (v i * d₁) * d₂) := by
      ext i; simp [mul_assoc]
    rw [this, hP, hP]
    ext i; simp [mul_assoc]
  have hone : Φ 1 = 1 := by
    apply key
    intro v
    rw [← hP]
    simp
  have hzero : Φ 0 = 0 := by
    apply key
    intro v
    rw [← hP]
    have : (fun i => v i * (0 : D)) = 0 := by ext i; simp
    rw [this, map_zero]
    ext i; simp
  have hcomm : ∀ k : K, Φ (algebraMap K D k) = algebraMap K D' k := by
    intro k
    apply key
    intro v
    rw [← hP]
    have : (fun i => v i * algebraMap K D k) = k • v := by
      ext i
      simp [Algebra.smul_def, Algebra.commutes]
    rw [this, hφK]
    ext i
    simp [Algebra.smul_def, Algebra.commutes]
  let Φ' : D →ₐ[K] D' :=
    { toFun := Φ, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := hadd,
      commutes' := hcomm }
  have hinj : Function.Injective Φ' := (Φ'.toRingHom).injective
  have hsurj : Function.Surjective Φ'.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hinj
  exact ⟨AlgEquiv.ofBijective Φ' ⟨hinj, hsurj⟩⟩

section Thm55

variable {ι : Type w} [Fintype ι] [DecidableEq ι] {A : ι → Type v} [∀ i, Ring (A i)]

/-- The module $S$ over $A_i$ regarded as a module over the product $A = \prod_i A_i$ through the
projection: $(a_j)_j \cdot m = a_i m$ (Milne, before Theorem 5.5). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §5, module over a factor of a product, p. 143"]
def ProdModule (_A : ι → Type v) (_i : ι) (S : Type u) : Type u := S

instance (i : ι) (S : Type u) [AddCommGroup S] : AddCommGroup (ProdModule A i S) :=
  inferInstanceAs (AddCommGroup S)

noncomputable instance (i : ι) (S : Type u) [AddCommGroup S] [Module (A i) S] :
    Module (Π j, A j) (ProdModule A i S) :=
  Module.compHom S (Pi.evalRingHom A i)

/-- Coercion into `ProdModule`. -/
def pm (A : ι → Type v) (i : ι) {S : Type u} (s : S) : ProdModule A i S := s

/-- Coercion out of `ProdModule`. -/
def pmv {i : ι} {S : Type u} (s : ProdModule A i S) : S := s

theorem prodModule_smul {i : ι} {S : Type u} [AddCommGroup S] [Module (A i) S]
    (a : Π j, A j) (s : ProdModule A i S) : a • s = pm A i (a i • pmv s) := rfl

theorem isSimpleModule_prodModule (i : ι) (S : Type u) [AddCommGroup S] [Module (A i) S]
    [IsSimpleModule (A i) S] : IsSimpleModule (Π j, A j) (ProdModule A i S) := by
  have : Nontrivial (ProdModule A i S) := IsSimpleModule.nontrivial (A i) S
  refine isSimpleModule_of_transitive fun v w hv => ?_
  have hv' : pmv v ≠ 0 := hv
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective (R := A i) hv' (pmv w)
  refine ⟨Pi.single i a, ?_⟩
  rw [prodModule_smul]
  have ha' : a • pmv v = pmv w := by simpa using ha
  simp only [Pi.single_eq_same]
  exact congrArg (pm A i) ha'

/-- The central idempotent `e_i = (0, ..., 1, ..., 0)` of a product of rings. -/
theorem single_one_mul_comm (i : ι) (a : Π j, A j) :
    (Pi.single i (1 : A i) : Π j, A j) * a = a * Pi.single i 1 := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem mul_single_one (i : ι) (c : Π j, A j) :
    c * (Pi.single i (1 : A i) : Π j, A j) = Pi.single i (c i) := by
  ext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem single_one_mul_single_one (i j : ι) :
    (Pi.single i (1 : A i) : Π k, A k) * Pi.single j (1 : A j) =
      if i = j then Pi.single i 1 else 0 := by
  split_ifs with h
  · subst h
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  · ext k
    by_cases hk : k = i
    · subst hk; simp [Pi.single_eq_of_ne h]
    · simp [Pi.single_eq_of_ne hk]

theorem sum_single_one_smul {M : Type*} [AddCommGroup M] [Module (Π j, A j) M] (m : M) :
    ∑ i, (Pi.single i (1 : A i) : Π k, A k) • m = m := by
  rw [← Finset.sum_smul]
  have : ∑ i, (Pi.single i (1 : A i) : Π k, A k) = 1 :=
    Finset.univ_sum_single (fun i => (1 : A i))
  rw [this, one_smul]

/-- Multiplication by the central idempotent `e_i` as a linear endomorphism. -/
def eSMul (i : ι) (M : Type*) [AddCommGroup M] [Module (Π j, A j) M] : M →ₗ[Π j, A j] M where
  toFun m := (Pi.single i (1 : A i) : Π j, A j) • m
  map_add' := smul_add _
  map_smul' c m := by
    simp only [RingHom.id_apply]
    rw [← mul_smul, ← mul_smul, single_one_mul_comm]

theorem eq_of_equiv_idem {i j : ι} {S : Type u} [AddCommGroup S] [Module (A j) S] [Nontrivial S]
    {Y : Type u} [AddCommGroup Y] [Module (Π k, A k) Y]
    (g : ProdModule A j S ≃ₗ[Π k, A k] Y)
    (hY : ∀ y : Y, (Pi.single i (1 : A i) : Π k, A k) • y = y) : j = i := by
  by_contra hji
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  have h1 : (Pi.single i (1 : A i) : Π k, A k) • (pm A j s) = 0 := by
    rw [prodModule_smul, Pi.single_eq_of_ne hji, zero_smul] <;> rfl
  have h2 := hY (g (pm A j s))
  rw [← g.map_smul, h1, map_zero] at h2
  exact hs (g.injective (a₁ := pm A j s) (a₂ := 0) (by rw [map_zero]; exact h2.symm))

/-- Theorem 5.5 (a) of Milne: let $A = A_1 \times \dots \times A_t$ be a product of simple rings
(Milne: simple $k$-algebras; artinian is what is used), and let $S_i$ be a simple $A_i$-module.
Each $S_i$ is a simple $A$-module, and every simple $A$-module is isomorphic to exactly one of
the $S_i$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 5.5(a), p. 143"]
theorem thm_5_5a [∀ i, IsSimpleRing (A i)] [∀ i, IsArtinianRing (A i)] (S : ι → Type u)
    [∀ i, AddCommGroup (S i)] [∀ i, Module (A i) (S i)] [∀ i, IsSimpleModule (A i) (S i)] :
    (∀ i, IsSimpleModule (Π j, A j) (ProdModule A i (S i))) ∧
      ∀ (M : Type u) [AddCommGroup M] [Module (Π j, A j) M], IsSimpleModule (Π j, A j) M →
        ∃! i, Nonempty (M ≃ₗ[Π j, A j] ProdModule A i (S i)) := by
  have hntS : ∀ j, Nontrivial (S j) := fun j => IsSimpleModule.nontrivial (A j) (S j)
  refine ⟨fun i => isSimpleModule_prodModule i (S i), ?_⟩
  intro M _ _ hM
  have hnt : Nontrivial M := IsSimpleModule.nontrivial (Π j, A j) M
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hex : ∃ i, (Pi.single i (1 : A i) : Π k, A k) • x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    rw [← sum_single_one_smul (A := A) x]
    exact Finset.sum_eq_zero fun i _ => h i
  obtain ⟨i, hi⟩ := hex
  have hid : ∀ m : M, (Pi.single i (1 : A i) : Π k, A k) • m = m := by
    have hrange : LinearMap.range (eSMul (A := A) i M) = ⊤ := by
      rcases eq_bot_or_eq_top (LinearMap.range (eSMul (A := A) i M)) with h | h
      · exfalso
        apply hi
        have hmem : eSMul (A := A) i M x ∈ LinearMap.range (eSMul (A := A) i M) :=
          LinearMap.mem_range_self _ x
        rw [h] at hmem
        exact (Submodule.mem_bot _).mp hmem
      · exact h
    intro m
    have hm : m ∈ LinearMap.range (eSMul (A := A) i M) := by rw [hrange]; trivial
    obtain ⟨m', rfl⟩ := hm
    show (Pi.single i (1 : A i) : Π k, A k) • (Pi.single i (1 : A i) : Π k, A k) • m' = _
    rw [← mul_smul, single_one_mul_single_one, if_pos rfl]
    rfl
  let mod : Module (A i) M :=
    { smul := fun a m => (Pi.single i a : Π k, A k) • m
      one_smul := hid
      mul_smul := fun a b m => by
        show (Pi.single i (a * b) : Π k, A k) • m =
          (Pi.single i a : Π k, A k) • (Pi.single i b : Π k, A k) • m
        rw [← mul_smul, Pi.single_mul]
      smul_zero := fun a => smul_zero _
      smul_add := fun a x y => smul_add _ _ _
      add_smul := fun a b m => by
        show (Pi.single i (a + b) : Π k, A k) • m =
          (Pi.single i a : Π k, A k) • m + (Pi.single i b : Π k, A k) • m
        rw [Pi.single_add, add_smul]
      zero_smul := fun m => by
        show (Pi.single i (0 : A i) : Π k, A k) • m = 0
        rw [Pi.single_zero, zero_smul] }
  letI : Module (A i) M := mod
  have hsm : ∀ (a : A i) (m : M), a • m = (Pi.single i a : Π k, A k) • m := fun _ _ => rfl
  have hcact : ∀ (c : Π k, A k) (m : M), c • m = c i • m := by
    intro c m
    calc c • m = c • ((Pi.single i (1 : A i) : Π k, A k) • m) := by rw [hid]
      _ = (c * Pi.single i 1) • m := by rw [mul_smul]
      _ = c i • m := by rw [hsm, mul_single_one]
  have hsimpA : IsSimpleModule (A i) M := by
    refine isSimpleModule_of_transitive fun v w hv => ?_
    obtain ⟨c, hc⟩ := IsSimpleModule.toSpanSingleton_surjective (R := Π k, A k) hv w
    exact ⟨c i, by rw [← hcact]; simpa using hc⟩
  obtain ⟨f⟩ := nonempty_linearEquiv_of_isSimpleRing (R := A i) M (S i)
  let F : M ≃ₗ[Π k, A k] ProdModule A i (S i) :=
    { f.toAddEquiv with
      map_smul' := by
        intro c m
        show f (c • m) = pm A i (c i • f m)
        rw [hcact]
        exact f.map_smul (c i) m }
  refine ⟨i, ⟨F⟩, fun j hj => ?_⟩
  obtain ⟨g⟩ := hj
  exact eq_of_equiv_idem (S := S j) g.symm hid

/-- The image `e_i M` of a module under the central idempotent `e_i`. -/
abbrev eRange (i : ι) (M : Type*) [AddCommGroup M] [Module (Π j, A j) M] :
    Submodule (Π j, A j) M :=
  LinearMap.range (eSMul (A := A) i M)

theorem single_smul_eRange (i : ι) {M : Type*} [AddCommGroup M] [Module (Π j, A j) M]
    (y : eRange (A := A) i M) : (Pi.single i (1 : A i) : Π k, A k) • y = y := by
  obtain ⟨y, m', hm'⟩ := y
  apply Subtype.ext
  show (Pi.single i (1 : A i) : Π k, A k) • y = y
  rw [← hm']
  show (Pi.single i (1 : A i) : Π k, A k) • (Pi.single i (1 : A i) : Π k, A k) • m' = _
  rw [← mul_smul, single_one_mul_single_one, if_pos rfl]
  rfl

theorem exists_pi_eRange_equiv (M : Type*) [AddCommGroup M] [Module (Π j, A j) M] :
    Nonempty (M ≃ₗ[Π j, A j] Π i, eRange (A := A) i M) := by
  let T : M →ₗ[Π j, A j] Π i, eRange (A := A) i M :=
    LinearMap.pi fun i => (eSMul (A := A) i M).rangeRestrict
  have hT : ∀ m i, ((T m i : eRange (A := A) i M) : M) =
      (Pi.single i (1 : A i) : Π k, A k) • m := fun _ _ => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    rw [← sum_single_one_smul (A := A) m]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrArg (fun f => ((f i : eRange (A := A) i M) : M)) hm
    simpa [hT] using this
  have hsurj : Function.Surjective T := by
    intro n
    have key : ∀ i j, (Pi.single j (1 : A j) : Π k, A k) • ((n i : eRange (A := A) i M) : M) =
        if j = i then ((n i : eRange (A := A) i M) : M) else 0 := by
      intro i j
      obtain ⟨m', hm'⟩ := (n i).2
      rw [← hm']
      show (Pi.single j (1 : A j) : Π k, A k) • (Pi.single i (1 : A i) : Π k, A k) • m' =
        if j = i then (Pi.single i (1 : A i) : Π k, A k) • m' else 0
      rw [← mul_smul, single_one_mul_single_one]
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    refine ⟨∑ i, ((n i : eRange (A := A) i M) : M), ?_⟩
    funext j
    apply Subtype.ext
    rw [hT, Finset.smul_sum]
    simp_rw [key]
    simp
  exact ⟨LinearEquiv.ofBijective T ⟨hinj, hsurj⟩⟩

theorem pi_component_equiv {P : Type*} [Ring P] {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Z Z' : κ → Type*} [∀ k, AddCommGroup (Z k)] [∀ k, Module P (Z k)]
    [∀ k, AddCommGroup (Z' k)] [∀ k, Module P (Z' k)]
    (ε : κ → P) (hε : ∀ i (y : Π k, Z k), ε i • y = Pi.single i (y i))
    (hε' : ∀ i (y : Π k, Z' k), ε i • y = Pi.single i (y i))
    (F : (Π k, Z k) ≃ₗ[P] Π k, Z' k) (i : κ) : Nonempty (Z i ≃ₗ[P] Z' i) := by
  let G : Z i →ₗ[P] Z' i := LinearMap.proj i ∘ₗ F.toLinearMap ∘ₗ LinearMap.single P Z i
  have hF : ∀ z : Z i, F (Pi.single i z) = Pi.single i (G z) := by
    intro z
    have h1 : ε i • (Pi.single i z : Π k, Z k) = Pi.single i z := by rw [hε]; simp
    calc F (Pi.single i z) = F (ε i • Pi.single i z) := by rw [h1]
      _ = ε i • F (Pi.single i z) := F.map_smul _ _
      _ = Pi.single i (F (Pi.single i z) i) := hε' i _
      _ = Pi.single i (G z) := rfl
  refine ⟨LinearEquiv.ofBijective G ⟨?_, ?_⟩⟩
  · intro z z' h
    have h1 : F (Pi.single i z) = F (Pi.single i z') := by rw [hF, hF, h]
    have h2 := congrFun (F.injective h1) i
    simpa using h2
  · intro z'
    set y := F.symm (Pi.single i z') with hy
    have h1 : ε i • y = Pi.single i (y i) := hε i y
    have h1' : ε i • (Pi.single i z' : Π k, Z' k) = Pi.single i z' := by rw [hε']; simp
    have h2 : ε i • y = y := by rw [hy, ← F.symm.map_smul, h1']
    have hFy : F (Pi.single i (y i)) = Pi.single i z' := by
      rw [← h1, h2, hy, F.apply_symm_apply]
    refine ⟨y i, ?_⟩
    show F (Pi.single i (y i)) i = z'
    rw [hFy]
    simp

theorem single_smul_pi {r : ι → ℕ} {S : ι → Type u} [∀ i, AddCommGroup (S i)]
    [∀ i, Module (A i) (S i)] (i : ι) (y : Π k, Fin (r k) → ProdModule A k (S k)) :
    (Pi.single i (1 : A i) : Π k, A k) • y = Pi.single i (y i) := by
  funext k l
  by_cases h : k = i
  · subst h
    simp [prodModule_smul]
    rfl
  · simp [Pi.single_eq_of_ne h, prodModule_smul]
    rfl

/-- Theorem 5.5 (b) of Milne: with the notation of (a), every finitely generated $A$-module is
isomorphic to $\bigoplus_i r_i S_i$ for some $r_i \in \mathbb N$, and $\bigoplus_i r_i S_i \cong
\bigoplus_i r'_i S_i$ if and only if $r_i = r'_i$ for all $i$.  ($r_i S_i$ is
`Fin (r i) → S_i`; finitely generated is Milne's convention for modules.) -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 5.5(b), p. 143"]
theorem thm_5_5b [∀ i, IsSimpleRing (A i)] [∀ i, IsArtinianRing (A i)] (S : ι → Type u)
    [∀ i, AddCommGroup (S i)] [∀ i, Module (A i) (S i)] [∀ i, IsSimpleModule (A i) (S i)] :
    (∀ (M : Type u) [AddCommGroup M] [Module (Π j, A j) M] [Module.Finite (Π j, A j) M],
        ∃ r : ι → ℕ, Nonempty (M ≃ₗ[Π j, A j] Π i, Fin (r i) → ProdModule A i (S i))) ∧
      ∀ r r' : ι → ℕ,
        Nonempty ((Π i, Fin (r i) → ProdModule A i (S i)) ≃ₗ[Π j, A j]
            Π i, Fin (r' i) → ProdModule A i (S i)) ↔ r = r' := by
  have hntS : ∀ j, Nontrivial (S j) := fun j => IsSimpleModule.nontrivial (A j) (S j)
  have hsimpS : ∀ i, IsSimpleModule (Π j, A j) (ProdModule A i (S i)) :=
    fun i => isSimpleModule_prodModule i (S i)
  have hsemi : ∀ i, IsSemisimpleRing (A i) := fun i => inferInstance
  refine ⟨?_, ?_⟩
  · intro M _ _ _
    have hN : ∀ i, ∃ n : ℕ, Nonempty (eRange (A := A) i M ≃ₗ[Π j, A j]
        (Fin n → ProdModule A i (S i))) := by
      intro i
      have hiso : IsIsotypicOfType (Π j, A j) (eRange (A := A) i M) (ProdModule A i (S i)) := by
        intro m hm
        obtain ⟨j, ⟨g⟩, _⟩ := (thm_5_5a S).2 m hm
        have hY : ∀ y : m, (Pi.single i (1 : A i) : Π k, A k) • y = y := by
          intro y
          apply Subtype.ext
          rw [Submodule.coe_smul]
          exact single_smul_eRange i y.1
        have hj : j = i := eq_of_equiv_idem (A := A) (S := S j) (i := i) (Y := m) g.symm hY
        subst hj
        exact ⟨g⟩
      exact hiso.linearEquiv_fun
    choose n hn using hN
    obtain ⟨D⟩ := exists_pi_eRange_equiv (A := A) M
    exact ⟨n, ⟨D.trans (LinearEquiv.piCongrRight fun i => (hn i).some)⟩⟩
  · intro r r'
    constructor
    · rintro ⟨F⟩
      funext i
      obtain ⟨G⟩ := pi_component_equiv (P := Π j, A j)
        (Z := fun k => Fin (r k) → ProdModule A k (S k))
        (Z' := fun k => Fin (r' k) → ProdModule A k (S k))
        (fun i => (Pi.single i (1 : A i) : Π k, A k))
        (fun i y => single_smul_pi (r := r) (S := S) i y)
        (fun i y => single_smul_pi (r := r') (S := S) i y) F i
      exact (cor_1_3 (R := Π j, A j) (fun _ : Fin (r i) => ProdModule A i (S i))
        (fun _ : Fin (r' i) => ProdModule A i (S i)) G).1
    · rintro rfl
      exact ⟨LinearEquiv.refl _ _⟩

end Thm55

end NumberFieldKB.MilneCFT.Ch4
