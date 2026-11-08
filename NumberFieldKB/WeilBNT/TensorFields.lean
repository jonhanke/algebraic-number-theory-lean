import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*: purely algebraic rows of I.§1, III.§2 and III.§3

* `weil_I_1_cor3_thm2`: I.§1, Cor. 3 of Thm. 2. If $F$ is a finite field with $q^d$ elements containing a field with
  $q$ elements (here: $q=p^f$ for the characteristic $p$), the elements fixed by $x\mapsto x^{q^n}$ form a subfield
  with $q^{(d,n)}$ elements.
* `weil_III_2_lemma2_unique`, `weil_III_2_lemma2_hom`: III.§2, Lemma 2. A commutative ring which is a direct sum of
  fields is so in only one way (the unit elements $e_i$ of the summands are determined), and a homomorphism of such a
  sum into a field is $0$ on all summands but one.
* `weil_III_2_cor1_exists`, `weil_III_2_cor1_unique_index`, `weil_III_2_cor1_unique_hom`: III.§2, Cor. 1 of Prop. 3:
  given a decomposition $\varphi:K\otimes_kk'\cong\bigoplus_iK_i$ into fields (Weil's Prop. 3, which is in Mathlib for
  separable $k'$), every $k$-linear embedding $\lambda$ of $k'$ into a field $K'\supseteq K$ factors uniquely as
  $\sigma\circ\lambda_i$, $\lambda_i$ the $i$-th component of $\varphi$ on $k'$. Here $A=K\otimes_kk'$ (Weil writes
  $k'\otimes_kK$; the two are canonically isomorphic, and $K\otimes_kk'$ carries Mathlib's $K$-algebra instance).
* `weil_III_2_cor4`: III.§2, Cor. 4. If $k'/k$ is Galois (normal suffices), all $k$-embeddings of $k'$ into a field
  $K$ have the same image.
* `weil_III_3_prop4_trace`, `weil_III_3_prop4_norm`: III.§3, Prop. 4 (trace and norm in $A$ through the $K_i$), and
  `weil_III_3_cor2_trace`, `weil_III_3_cor2_norm`: its Corollary 2 for $x\in k'$.
* `weil_III_3_lemma3_nondegenerate`, `weil_III_3_lemma3_det`: III.§3, Lemma 3 ($\lambda(xy)$ is non-degenerate for
  every nonzero linear form $\lambda$).
-/

open scoped TensorProduct

noncomputable section

namespace NumberFieldKB.WeilBNT.TensorFields

/-! ### I.§1 -/

/-- In a cyclic group, for $e$ dividing the order, exactly $e$ elements satisfy $u^e=1$. -/
theorem card_filter_pow_eq_one_of_dvd {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    {e : ℕ} (he : 0 < e) (hdvd : e ∣ Fintype.card G) :
    (Finset.univ.filter fun u : G => u ^ e = 1).card = e := by
  refine le_antisymm (IsCyclic.card_pow_eq_one_le he) ?_
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨t, ht⟩ := hdvd
  have hord : orderOf γ = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card]
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, mul_zero] at ht; omega
    · exact h
  refine Finset.le_card_of_inj_on_range (fun j => γ ^ (t * j)) (fun j _ => ?_) (fun i hi j hj hij => ?_)
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : (γ ^ (t * j)) ^ e = (γ ^ Fintype.card G) ^ j := by
      rw [← pow_mul, ← pow_mul, ht]
      congr 1
      ring
    rw [this, pow_card_eq_one, one_pow]
  · have h1 : t * i < orderOf γ := by
      rw [hord, ht]; nlinarith
    have h2 : t * j < orderOf γ := by
      rw [hord, ht]; nlinarith
    have := pow_injOn_Iio_orderOf h1 h2 hij
    exact Nat.eq_of_mul_eq_mul_left htpos this

/-- For $a\ge1$: $u^a=u$ iff $u^{a-1}=1$. -/
theorem pow_eq_self_iff {G : Type*} [Group G] (u : G) {a : ℕ} (ha : 1 ≤ a) : u ^ a = u ↔ u ^ (a - 1) = 1 := by
  have e : a = (a - 1) + 1 := (Nat.sub_add_cancel ha).symm
  constructor
  · intro h
    have : u ^ (a - 1) * u = 1 * u := by
      rw [← pow_succ, ← e, h, one_mul]
    exact mul_right_cancel this
  · intro h
    conv_lhs => rw [e]
    rw [pow_succ, h, one_mul]

@[kb "weil1973bnt" "Ch. I, §1, Cor. 3 of Thm. 2"]
theorem weil_I_1_cor3_thm2 (F : Type*) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] {f d : ℕ}
    (hf : 0 < f) (hd : 0 < d) (hcard : Fintype.card F = (p ^ f) ^ d) (n : ℕ) (hn : 0 < n) :
    ∃ L : Subfield F, (L : Set F) = {x | x ^ ((p ^ f) ^ n) = x} ∧
      Nat.card L = (p ^ f) ^ Nat.gcd d n := by
  classical
  have hp : p.Prime := Fact.out
  set q := p ^ f with hq
  have hq1 : 1 < q := Nat.one_lt_pow hf.ne' hp.one_lt
  set g := Nat.gcd d n with hg
  have hgd : g ∣ d := Nat.gcd_dvd_left d n
  have hgn : g ∣ n := Nat.gcd_dvd_right d n
  have hN : Fintype.card Fˣ = q ^ d - 1 := by
    rw [Fintype.card_units, hcard]
  have hqpos : ∀ m, 1 ≤ q ^ m := fun m => Nat.one_le_pow _ _ (by omega)
  -- unit-level equivalence
  have hunit : ∀ u : Fˣ, u ^ (q ^ n) = u ↔ u ^ (q ^ g) = u := by
    intro u
    rw [pow_eq_self_iff u (hqpos n), pow_eq_self_iff u (hqpos g)]
    have hN1 : u ^ (q ^ d - 1) = 1 := by rw [← hN]; exact pow_card_eq_one
    have hgcd : Nat.gcd (q ^ n - 1) (q ^ d - 1) = q ^ g - 1 := by
      rw [Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_comm]
    constructor
    · intro h
      have := pow_gcd_eq_one.mpr ⟨h, hN1⟩
      rwa [hgcd] at this
    · intro h
      obtain ⟨c, hc⟩ := Nat.pow_sub_one_dvd_pow_sub_one q hgn
      rw [hc, pow_mul, h, one_pow]
  have hkey : ∀ x : F, x ^ (q ^ n) = x ↔ x ^ (q ^ g) = x := by
    intro x
    by_cases hx : x = 0
    · subst hx
      have h0 : ∀ m, (0 : F) ^ (q ^ m) = 0 := fun m => zero_pow (pow_pos (by omega : 0 < q) m).ne'
      simp [h0]
    · have := hunit (Units.mk0 x hx)
      simpa [Units.ext_iff] using this
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left n hd
  have hcount : (Finset.univ.filter fun x : F => x ^ (q ^ g) = x).card = q ^ g := by
    have hlt : 1 < q ^ g := Nat.one_lt_pow hgpos.ne' hq1
    have hZ : (Finset.univ.filter fun u : Fˣ => u ^ (q ^ g - 1) = 1).card = q ^ g - 1 := by
      apply card_filter_pow_eq_one_of_dvd
      · omega
      · rw [hN]; exact Nat.pow_sub_one_dvd_pow_sub_one q hgd
    have hset : (Finset.univ.filter fun x : F => x ^ (q ^ g) = x) =
        insert 0 ((Finset.univ.filter fun u : Fˣ => u ^ (q ^ g - 1) = 1).map ⟨Units.val, fun _ _ h => Units.ext h⟩) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_map]
      by_cases hx : x = 0
      · subst hx
        have h0 : (0 : F) ^ (q ^ g) = 0 := zero_pow (pow_pos (by omega : 0 < q) g).ne'
        simp [h0]
      · have := pow_eq_self_iff (Units.mk0 x hx) (hqpos g)
        constructor
        · intro h
          right
          refine ⟨Units.mk0 x hx, this.mp ?_, rfl⟩
          simpa [Units.ext_iff] using h
        · rintro (h | ⟨u, hu, rfl⟩)
          · exact absurd h hx
          · have := (pow_eq_self_iff u (hqpos g)).mpr hu
            change (u : F) ^ (q ^ g) = (u : F)
            exact_mod_cast congrArg Units.val this
    rw [hset, Finset.card_insert_of_notMem, Finset.card_map, hZ]
    · omega
    · simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
      intro u _
      exact u.ne_zero
  refine ⟨(iterateFrobenius F p (f * n)).eqLocusField (RingHom.id F), ?_, ?_⟩
  · ext x
    simp [iterateFrobenius_def, pow_mul, hq]
  · rw [← hcount]
    show Nat.card {x // x ∈ (iterateFrobenius F p (f * n)).eqLocusField (RingHom.id F)} = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, RingHom.mem_eqLocusField,
      iterateFrobenius_def, RingHom.id_apply]
    rw [← hkey x]
    simp [pow_mul, hq]

/-! ### III.§2, Lemma 2 -/

section Lemma2

variable {B : Type*} [CommRing B] {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
  {Ki : ι → Type*} [∀ i, Field (Ki i)] {Lj : ι' → Type*} [∀ j, Field (Lj j)]

/-- A primitive idempotent: a nonzero idempotent $e$ such that $ee'\in\{0,e\}$ for every idempotent $e'$. -/
def IsPrimitiveIdempotent {R : Type*} [CommRing R] (e : R) : Prop :=
  e ≠ 0 ∧ IsIdempotentElem e ∧ ∀ e' : R, IsIdempotentElem e' → e * e' = 0 ∨ e * e' = e

/-- Ring isomorphisms preserve primitive idempotents. -/
theorem isPrimitiveIdempotent_equiv {R S : Type*} [CommRing R] [CommRing S] (χ : R ≃+* S) (e : R)
    (h : IsPrimitiveIdempotent e) : IsPrimitiveIdempotent (χ e) := by
  obtain ⟨h0, hi, hp⟩ := h
  refine ⟨fun h => h0 (χ.injective (by simpa using h)), by simpa [IsIdempotentElem, ← map_mul] using congrArg χ hi, ?_⟩
  intro e' he'
  have he'' : IsIdempotentElem (χ.symm e') := by
    unfold IsIdempotentElem at he' ⊢
    rw [← map_mul, he']
  rcases hp _ he'' with h | h
  · left
    have := congrArg χ h
    simpa using this
  · right
    have := congrArg χ h
    simpa using this

/-- The primitive idempotents of a finite product of fields are the standard idempotents. -/
theorem isPrimitiveIdempotent_pi {e : (i : ι) → Ki i} (h : IsPrimitiveIdempotent e) :
    ∃ i, e = Pi.single i 1 := by
  obtain ⟨h0, hi, hp⟩ := h
  obtain ⟨i, hi0⟩ : ∃ i, e i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (funext hc)
  have hi1 : e i = 1 := by
    have := congrFun hi i
    simp only [Pi.mul_apply] at this
    exact (IsIdempotentElem.iff_eq_zero_or_one.mp this).resolve_left hi0
  refine ⟨i, ?_⟩
  have hsi : IsIdempotentElem (Pi.single i (1 : Ki i) : (i : ι) → Ki i) := by
    unfold IsIdempotentElem
    rw [← Pi.single_mul, mul_one]
  rcases hp _ hsi with h | h
  · exfalso
    have := congrFun h i
    simp [hi1] at this
  · rw [← h]
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hi1]
    · simp [hj]

/-- The standard idempotents of a finite product of fields are primitive. -/
theorem isPrimitiveIdempotent_single (i : ι) : IsPrimitiveIdempotent (Pi.single i 1 : (i : ι) → Ki i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrFun h i
    simp at this
  · unfold IsIdempotentElem
    rw [← Pi.single_mul, mul_one]
  · intro e' he'
    have hj : e' i = 0 ∨ e' i = 1 := IsIdempotentElem.iff_eq_zero_or_one.mp (show IsIdempotentElem (e' i) from congrFun he' i)
    rcases hj with h | h
    · left
      funext j
      by_cases hj : j = i
      · subst hj; simp [h]
      · simp [hj]
    · right
      funext j
      by_cases hj : j = i
      · subst hj; simp [h]
      · simp [hj]

/-- The standard idempotents of a product of fields are pairwise distinct. -/
theorem single_one_injective {ι : Type*} [DecidableEq ι] (Ki : ι → Type*) [∀ i, Field (Ki i)]
    (i i' : ι) (h : (Pi.single i 1 : (i : ι) → Ki i) = Pi.single i' 1) : i = i' := by
  by_contra hne
  have := congrFun h i
  simp [hne] at this

/-- Every standard idempotent of one decomposition is a standard idempotent of another. -/
theorem exists_single_eq {B : Type*} [CommRing B] {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
    {Ki : ι → Type*} [∀ i, Field (Ki i)] {Lj : ι' → Type*} [∀ j, Field (Lj j)] [Fintype ι] [Fintype ι']
    (φ : B ≃+* ((i : ι) → Ki i)) (ψ : B ≃+* ((j : ι') → Lj j)) (i : ι) :
    ∃ j, φ.symm (Pi.single i 1) = ψ.symm (Pi.single j 1) := by
  have h1 := isPrimitiveIdempotent_equiv φ.symm _ (isPrimitiveIdempotent_single (Ki := Ki) i)
  have h2 := isPrimitiveIdempotent_equiv ψ _ h1
  obtain ⟨j, hj⟩ := isPrimitiveIdempotent_pi h2
  refine ⟨j, ?_⟩
  apply ψ.injective
  rw [← hj]
  simp

/-- III.§2, Lemma 2, first assertion: two decompositions of $B$ as a direct sum of fields have the same summands,
i.e. the same unit elements $e_i$ (so $K_i=e_iB$), up to a bijection of the index sets. -/
@[kb "weil1973bnt" "Ch. III, §2, Lemma 2 (uniqueness of the decomposition)"]
theorem weil_III_2_lemma2_unique (φ : B ≃+* ((i : ι) → Ki i)) (ψ : B ≃+* ((j : ι') → Lj j)) :
    ∃ σ : ι ≃ ι', ∀ i, φ.symm (Pi.single i 1) = ψ.symm (Pi.single (σ i) 1) := by
  choose σ hσ using exists_single_eq φ ψ
  choose τ hτ using exists_single_eq ψ φ
  refine ⟨⟨σ, τ, fun i => ?_, fun j => ?_⟩, hσ⟩
  · have h := (hσ i).trans (hτ (σ i))
    exact (single_one_injective Ki _ _ (φ.symm.injective h)).symm
  · have h := (hτ j).trans (hσ (τ j))
    exact (single_one_injective Lj _ _ (ψ.symm.injective h)).symm

/-- III.§2, Lemma 2, second assertion: a ring homomorphism of $\bigoplus_iK_i$ into a field vanishes on all summands
except one. -/
@[kb "weil1973bnt" "Ch. III, §2, Lemma 2 (homomorphisms into a field)"]
theorem weil_III_2_lemma2_hom {L : Type*} [Field L] (f : ((i : ι) → Ki i) →+* L) :
    ∃! i, ∀ j, j ≠ i → ∀ x : Ki j, f (Pi.single j x) = 0 := by
  have hmul : ∀ j x, f (Pi.single j x) = f (Pi.single j 1) * f (Pi.single j x) := by
    intro j x
    rw [← map_mul, ← Pi.single_mul, one_mul]
  have hsum : ∑ j, f (Pi.single j 1) = 1 := by
    rw [← map_sum, ← map_one f]
    congr 1
    funext a
    simp [Finset.sum_apply]
  have hidem : ∀ j, f (Pi.single j 1) = 0 ∨ f (Pi.single j 1) = 1 := by
    intro j
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    unfold IsIdempotentElem
    rw [← map_mul, ← Pi.single_mul, mul_one]
  have hort : ∀ i j, i ≠ j → f (Pi.single i 1) * f (Pi.single j 1) = 0 := by
    intro i j hij
    rw [← map_mul]
    have : (Pi.single i 1 : (i : ι) → Ki i) * Pi.single j 1 = 0 := by
      funext a
      by_cases hai : a = i
      · subst hai; simp [hij]
      · simp [hai]
    rw [this, map_zero]
  obtain ⟨i, hi⟩ : ∃ i, f (Pi.single i 1) = 1 := by
    by_contra hc
    push Not at hc
    have : ∑ j, f (Pi.single j 1) = 0 :=
      Finset.sum_eq_zero fun j _ => (hidem j).resolve_right (hc j)
    rw [hsum] at this
    exact one_ne_zero this
  refine ⟨i, fun j hj x => ?_, fun i' hi' => ?_⟩
  · have h0 : f (Pi.single j 1) = 0 := by
      have := hort j i hj
      rwa [hi, mul_one] at this
    rw [hmul j x, h0, zero_mul]
  · by_contra hne
    have h0 : f (Pi.single i 1) = 0 := by
      have := hi' i (Ne.symm hne) 1
      exact this
    rw [hi] at h0
    exact one_ne_zero h0

end Lemma2

/-! ### III.§2, Cor. 1 and Cor. 4 of Prop. 3 -/

section Cor1

variable {k k' K : Type*} [Field k] [Field k'] [Field K] [Algebra k k'] [Algebra k K]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {Ki : ι → Type*} [∀ i, Field (Ki i)] [∀ i, Algebra K (Ki i)]
  [∀ i, Algebra k (Ki i)] [∀ i, IsScalarTower k K (Ki i)]

/-- The component $\mu_i$ of a decomposition $\varphi:K\otimes_kk'\cong\bigoplus_iK_i$ ($K$-linear). -/
def mu (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (i : ι) : K ⊗[k] k' →ₐ[K] Ki i :=
  (Pi.evalAlgHom K Ki i).comp φ.toAlgHom

/-- The embedding $\lambda_i$ of $k'$ into $K_i$: $\mu_i$ restricted to $k'$ ($k$-linear). -/
def lam (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (i : ι) : k' →ₐ[k] Ki i :=
  ((mu φ i).restrictScalars k).comp Algebra.TensorProduct.includeRight

variable {K' : Type*} [Field K'] [Algebra K K'] [Algebra k K'] [IsScalarTower k K K']

/-- A $K$-algebra homomorphism out of $\prod_iK_i$ vanishing on all summands but the $i$-th is determined by its
restriction to the $i$-th summand. -/
theorem apply_eq_single_of_vanish {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {Ki : ι → Type*} [∀ i, Field (Ki i)] [∀ i, Algebra K (Ki i)]
    (ν : ((i : ι) → Ki i) →ₐ[K] K') (i : ι) (h : ∀ j, j ≠ i → ∀ x : Ki j, ν (Pi.single j x) = 0)
    (z : (i : ι) → Ki i) : ν z = ν (Pi.single i (z i)) := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  exact Finset.sum_eq_single i (fun j _ hj => h j hj _) (fun hi => absurd (Finset.mem_univ i) hi)

/-- The restriction to the $i$-th summand of a $K$-algebra homomorphism out of $\prod_iK_i$ which vanishes on the
other summands. -/
def algHomOfVanish {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {Ki : ι → Type*} [∀ i, Field (Ki i)] [∀ i, Algebra K (Ki i)]
    (ν : ((i : ι) → Ki i) →ₐ[K] K') (i : ι) (h : ∀ j, j ≠ i → ∀ x : Ki j, ν (Pi.single j x) = 0) :
    Ki i →ₐ[K] K' where
  toFun w := ν (Pi.single i w)
  map_one' := by
    have := apply_eq_single_of_vanish ν i h 1
    rw [map_one] at this
    simpa using this.symm
  map_mul' x y := by simp [← map_mul, Pi.single_mul]
  map_zero' := by simp
  map_add' x y := by simp [Pi.single_add]
  commutes' c := by
    have h1 : ν (Pi.single i 1) = 1 := by
      have := apply_eq_single_of_vanish ν i h 1
      rw [map_one] at this
      simpa using this.symm
    have : (Pi.single i (algebraMap K (Ki i) c) : (i : ι) → Ki i) = c • Pi.single i 1 := by
      rw [← Pi.single_smul, Algebra.algebraMap_eq_smul_one]
    simp only [this, map_smul]
    rw [h1, ← Algebra.algebraMap_eq_smul_one]

theorem algHomOfVanish_apply {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {Ki : ι → Type*} [∀ i, Field (Ki i)] [∀ i, Algebra K (Ki i)]
    (ν : ((i : ι) → Ki i) →ₐ[K] K') (i : ι) (h : ∀ j, j ≠ i → ∀ x : Ki j, ν (Pi.single j x) = 0)
    (z : (i : ι) → Ki i) : algHomOfVanish ν i h (z i) = ν z :=
  (apply_eq_single_of_vanish ν i h z).symm

/-- Factoring $l$ through the $i$-th component is the same as factoring its $K$-linear extension through $\mu_i$. -/
theorem comp_lam_eq_iff (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (l : k' →ₐ[k] K') (i : ι) (σ : Ki i →ₐ[K] K') :
    l = (σ.restrictScalars k).comp (lam φ i) ↔ σ.comp (mu φ i) = AlgHom.liftEquiv k K k' K' l := by
  have key : (AlgHom.liftEquiv k K k' K').symm (σ.comp (mu φ i)) = (σ.restrictScalars k).comp (lam φ i) := rfl
  rw [← key]
  constructor
  · intro h
    exact (AlgHom.liftEquiv k K k' K').symm_apply_eq.mp h.symm
  · intro h
    exact ((AlgHom.liftEquiv k K k' K').symm_apply_eq.mpr h).symm

/-- Evaluating a $K$-algebra homomorphism from the product at a standard idempotent. -/
theorem mu_symm_single (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (i j : ι) (w : Ki j) :
    mu φ i (φ.symm (Pi.single j w)) = (Pi.single j w : (i : ι) → Ki i) i := by
  simp [mu]

@[kb "weil1973bnt" "Ch. III, §2, Cor. 1 of Prop. 3 (existence)"]
theorem weil_III_2_cor1_exists (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (l : k' →ₐ[k] K') :
    ∃ (i : ι) (σ : Ki i →ₐ[K] K'), l = (σ.restrictScalars k).comp (lam φ i) := by
  classical
  set μ0 := AlgHom.liftEquiv k K k' K' l with hμ0
  let ν : ((i : ι) → Ki i) →ₐ[K] K' := μ0.comp φ.symm.toAlgHom
  obtain ⟨i, hi, -⟩ := weil_III_2_lemma2_hom (ν : ((i : ι) → Ki i) →+* K')
  refine ⟨i, algHomOfVanish ν i hi, (comp_lam_eq_iff φ l i _).mpr ?_⟩
  refine AlgHom.ext fun a => ?_
  have := algHomOfVanish_apply ν i hi (φ a)
  simpa [ν, mu] using this

@[kb "weil1973bnt" "Ch. III, §2, Cor. 1 of Prop. 3 (the index is unique)"]
theorem weil_III_2_cor1_unique_index (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (l : k' →ₐ[k] K')
    {i j : ι} (σ : Ki i →ₐ[K] K') (τ : Ki j →ₐ[K] K')
    (hσ : l = (σ.restrictScalars k).comp (lam φ i)) (hτ : l = (τ.restrictScalars k).comp (lam φ j)) :
    i = j := by
  by_contra hij
  have hσ' := (comp_lam_eq_iff φ l i σ).mp hσ
  have hτ' := (comp_lam_eq_iff φ l j τ).mp hτ
  have h1 : AlgHom.liftEquiv k K k' K' l (φ.symm (Pi.single j 1)) = 1 := by
    rw [← hτ', AlgHom.comp_apply, mu_symm_single]
    simp
  have h2 : AlgHom.liftEquiv k K k' K' l (φ.symm (Pi.single j 1)) = 0 := by
    rw [← hσ', AlgHom.comp_apply, mu_symm_single]
    simp [Pi.single_eq_of_ne hij]
  rw [h1] at h2
  exact one_ne_zero h2

@[kb "weil1973bnt" "Ch. III, §2, Cor. 1 of Prop. 3 (the embedding is unique)"]
theorem weil_III_2_cor1_unique_hom (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (l : k' →ₐ[k] K')
    {i : ι} (σ τ : Ki i →ₐ[K] K')
    (hσ : l = (σ.restrictScalars k).comp (lam φ i)) (hτ : l = (τ.restrictScalars k).comp (lam φ i)) :
    σ = τ := by
  have hσ' := (comp_lam_eq_iff φ l i σ).mp hσ
  have hτ' := (comp_lam_eq_iff φ l i τ).mp hτ
  refine AlgHom.ext fun w => ?_
  have e1 := congrArg (fun f => f (φ.symm (Pi.single i w))) hσ'
  have e2 := congrArg (fun f => f (φ.symm (Pi.single i w))) hτ'
  simp only [AlgHom.comp_apply, mu_symm_single, Pi.single_eq_same] at e1 e2
  rw [e1, e2]

end Cor1

/-- If $k'/k$ is normal, the image of one $k$-embedding of $k'$ into a field lies in the image of any other. -/
theorem fieldRange_le_of_normal {k k' K : Type*} [Field k] [Field k'] [Field K] [Algebra k k'] [Algebra k K]
    [Normal k k'] (l l' : k' →ₐ[k] K) : l'.fieldRange ≤ l.fieldRange := by
  rintro _ ⟨x, rfl⟩
  have hint : IsIntegral k x := Algebra.IsIntegral.isIntegral x
  have hf0 : (minpoly k x).map (algebraMap k k') ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  have hroot : (((minpoly k x).map (algebraMap k k')).map (l : k' →+* K)).IsRoot (l' x) := by
    have hmap : ((minpoly k x).map (algebraMap k k')).map (l : k' →+* K) = (minpoly k x).map (algebraMap k K) := by
      rw [Polynomial.map_map]
      congr 1
      exact l.comp_algebraMap
    rw [hmap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    have := Polynomial.aeval_algHom_apply l' x (minpoly k x)
    rw [minpoly.aeval, map_zero] at this
    exact this
  obtain ⟨y, hy⟩ := (Normal.splits inferInstance x).mem_range_of_isRoot hf0 hroot
  exact ⟨y, hy⟩

@[kb "weil1973bnt" "Ch. III, §2, Cor. 4 of Prop. 3"]
theorem weil_III_2_cor4 {k k' K : Type*} [Field k] [Field k'] [Field K] [Algebra k k'] [Algebra k K]
    [Normal k k'] (l l' : k' →ₐ[k] K) : l.fieldRange = l'.fieldRange := by
  exact le_antisymm (fieldRange_le_of_normal l' l) (fieldRange_le_of_normal l l')

/-! ### III.§3, Prop. 4 and Cor. 2 -/

/-- The trace of a finite product of free finite algebras is the sum of the traces. -/
theorem algebraTrace_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (x : ∀ i, A i) : Algebra.trace R (∀ i, A i) x = ∑ i, Algebra.trace R (A i) (x i) := by
  classical
  let s : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex R (A i)) R (A i) := fun i => Module.Free.chooseBasis R (A i)
  have h : Algebra.leftMulMatrix (Pi.basis s) x = Matrix.blockDiagonal' fun i => Algebra.leftMulMatrix (s i) (x i) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.blockDiagonal'_apply]
    by_cases hij : i = j
    · subst hij
      simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply, Pi.mul_apply]
    · simp [hij, Pi.basis_repr, Pi.basis_apply, Pi.mul_apply]
  rw [Algebra.trace_eq_matrix_trace (Pi.basis s), h, Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ => (Algebra.trace_eq_matrix_trace (s i) (x i)).symm

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

/-- The norm of a finite product of free finite algebras is the product of the norms. -/
theorem algebraNorm_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
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

section Prop4

variable {k k' K : Type*} [Field k] [Field k'] [Field K] [Algebra k k'] [Algebra k K] [FiniteDimensional k k']
  {ι : Type*} [Fintype ι] [DecidableEq ι] {Ki : ι → Type*} [∀ i, Field (Ki i)] [∀ i, Algebra K (Ki i)]
  [∀ i, Algebra k (Ki i)] [∀ i, IsScalarTower k K (Ki i)] [∀ i, FiniteDimensional K (Ki i)]

@[kb "weil1973bnt" "Ch. III, §3, Prop. 4 (trace)"]
theorem weil_III_3_prop4_trace (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (a : K ⊗[k] k') :
    Algebra.trace K (K ⊗[k] k') a = ∑ i, Algebra.trace K (Ki i) (mu φ i a) := by
  rw [← Algebra.trace_eq_of_algEquiv φ a, algebraTrace_pi]
  rfl

@[kb "weil1973bnt" "Ch. III, §3, Prop. 4 (norm)"]
theorem weil_III_3_prop4_norm (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (a : K ⊗[k] k') :
    Algebra.norm K a = ∏ i, Algebra.norm K (mu φ i a) := by
  rw [← Algebra.norm_eq_of_algEquiv φ a, algebraNorm_pi]
  rfl

omit [FiniteDimensional k k'] in
/-- Multiplication by $1\otimes x$ on $K\otimes_kk'$ is the base change of multiplication by $x$. -/
theorem mulLeft_one_tmul (x : k') :
    LinearMap.mulLeft K (1 ⊗ₜ[k] x : K ⊗[k] k') = (LinearMap.mulLeft k x).baseChange K := by
  refine TensorProduct.AlgebraTensorModule.curry_injective ?_
  ext y
  simp

@[kb "weil1973bnt" "Ch. III, §3, Cor. 2 of Prop. 4 (trace)"]
theorem weil_III_3_cor2_trace (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (x : k') :
    algebraMap k K (Algebra.trace k k' x) = ∑ i, Algebra.trace K (Ki i) (lam φ i x) := by

  have h : Algebra.trace K (K ⊗[k] k') (1 ⊗ₜ[k] x : K ⊗[k] k') = algebraMap k K (Algebra.trace k k' x) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange (A := K)]
    exact congrArg _ (mulLeft_one_tmul x)
  rw [← h, weil_III_3_prop4_trace φ]
  rfl

@[kb "weil1973bnt" "Ch. III, §3, Cor. 2 of Prop. 4 (norm)"]
theorem weil_III_3_cor2_norm (φ : K ⊗[k] k' ≃ₐ[K] ((i : ι) → Ki i)) (x : k') :
    algebraMap k K (Algebra.norm k x) = ∏ i, Algebra.norm K (lam φ i x) := by

  have h : Algebra.norm K (1 ⊗ₜ[k] x : K ⊗[k] k') = algebraMap k K (Algebra.norm k x) := by
    rw [Algebra.norm_apply, Algebra.norm_apply]
    have := LinearMap.det_baseChange (A := K) (LinearMap.mulLeft k x)
    rw [← mulLeft_one_tmul] at this
    exact this
  rw [← h, weil_III_3_prop4_norm φ]
  rfl

end Prop4

/-! ### III.§3, Lemma 3 -/

section Lemma3

variable {k k' : Type*} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']

/-- The bilinear form $(x,y)\mapsto\lambda(xy)$ on $k'$. -/
def lamForm (l : k' →ₗ[k] k) : LinearMap.BilinForm k k' := (LinearMap.mul k k').compr₂ l

@[kb "weil1973bnt" "Ch. III, §3, Lemma 3 (non-degeneracy)"]
theorem weil_III_3_lemma3_nondegenerate {l : k' →ₗ[k] k} (hl : l ≠ 0) : (lamForm l).Nondegenerate := by
  obtain ⟨a, ha⟩ : ∃ a, l a ≠ 0 := by
    by_contra h
    push Not at h
    exact hl (LinearMap.ext h)
  have hform : ∀ x y, lamForm l x y = l (x * y) := fun x y => rfl
  constructor
  · intro x hx
    by_contra hx0
    apply ha
    have := hx (x⁻¹ * a)
    rwa [hform, mul_inv_cancel_left₀ hx0] at this
  · intro y hy
    by_contra hy0
    apply ha
    have := hy (a * y⁻¹)
    rwa [hform, mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this

@[kb "weil1973bnt" "Ch. III, §3, Lemma 3 (the determinant)"]
theorem weil_III_3_lemma3_det {l : k' →ₗ[k] k} (hl : l ≠ 0) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n k k') : (Matrix.of fun i j => l (b i * b j)).det ≠ 0 := by
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp (weil_III_3_lemma3_nondegenerate hl)
  convert h using 2
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply, lamForm]

end Lemma3

end NumberFieldKB.WeilBNT.TensorFields
