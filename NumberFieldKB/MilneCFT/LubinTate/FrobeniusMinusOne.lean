import NumberFieldKB.MilneCFT.LubinTate.Complements

/-!
# Lemma 3.11 (Milne, *Class Field Theory*, Ch. I): $\sigma - 1$ is surjective on $B$ and $B^\times$

Proof of the named statement `FrobeniusMinusOneSurjective`. Everything is reduced to one successive approximation
lemma (`surj_of_step`): an additive map $G : B \to B$ with $G(\varpi x) = \varpi G(x)$ which is surjective modulo
$\varpi$ is surjective on the $\varpi$-adically complete ring $B$. It is applied to $G_c(x) = \sigma x - c x$; modulo
$\varpi$ this is the Artin–Schreier type equation $x^q - \bar c x = \bar d$ in the algebraically closed residue field.
The kernel statements use that the residue field of $A$ is exactly the set of roots of $X^q - X$.
-/

open scoped ValuativeRel
open Polynomial IsLocalRing

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

/-! ## Generic approximation lemmas -/

theorem mem_smul_top_iff {R : Type*} [CommRing R] (J : Ideal R) (x : R) :
    x ∈ (J • ⊤ : Submodule R R) ↔ x ∈ J := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

theorem mem_span_pow_iff {R : Type*} [CommRing R] (ϖ x : R) (n : ℕ) :
    x ∈ Ideal.span {ϖ} ^ n ↔ ∃ z, x = ϖ ^ n * z := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [← hz]; ring⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz]; ring⟩

/-- Successive approximation: a compatible sequence of approximate solutions has a limit. -/
theorem exists_adic_limit {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (P : ℕ → R → Prop) (h0 : ∃ x, P 0 x)
    (hstep : ∀ n x, P n x → ∃ y, P (n + 1) y ∧ y - x ∈ I ^ n) :
    ∃ (f : ℕ → R) (L : R), (∀ n, P n (f n)) ∧ ∀ n, L - f n ∈ I ^ n := by
  have hs : ∀ n (x : {x // P n x}), ∃ y : {x // P (n + 1) x}, y.1 - x.1 ∈ I ^ n := by
    intro n x
    obtain ⟨y, hy, h⟩ := hstep n x.1 x.2
    exact ⟨⟨y, hy⟩, h⟩
  choose g hg using hs
  obtain ⟨x0, hx0⟩ := h0
  let s : ∀ n, {x // P n x} := fun n =>
    Nat.rec (motive := fun n => {x // P n x}) ⟨x0, hx0⟩ (fun n x => g n x) n
  have hsucc : ∀ n, (s (n + 1)).1 - (s n).1 ∈ I ^ n := fun n => hg n (s n)
  have hcauchy : ∀ m n, m ≤ n → (s n).1 - (s m).1 ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have : (s (n + 1)).1 - (s m).1 = ((s (n + 1)).1 - (s n).1) + ((s n).1 - (s m).1) := by ring
      rw [this]
      exact add_mem (Ideal.pow_le_pow_right hmn (hsucc n)) ih
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => (s n).1) (by
    intro m n hmn
    have h := neg_mem (hcauchy m n hmn)
    rw [neg_sub] at h
    exact SModEq.sub_mem.2 ((mem_smul_top_iff _ _).2 h))
  refine ⟨fun n => (s n).1, L, fun n => (s n).2, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, mem_smul_top_iff] at h
  have h2 := neg_mem h
  rwa [neg_sub] at h2

/-- An additive map commuting with multiplication by `ϖ` which is surjective modulo `ϖ` is surjective on a
`ϖ`-adically complete ring. -/
theorem surj_of_step {R : Type*} [CommRing R] (ϖ : R) [IsAdicComplete (Ideal.span {ϖ}) R]
    (G : R →+ R) (hG : ∀ x, G (ϖ * x) = ϖ * G x)
    (hstep : ∀ d, ∃ b, d - G b ∈ Ideal.span {ϖ}) (c : R) : ∃ b, G b = c := by
  have hGp : ∀ n x, G (ϖ ^ n * x) = ϖ ^ n * G x := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih =>
      have : ϖ ^ (n + 1) * x = ϖ * (ϖ ^ n * x) := by ring
      rw [this, hG, ih]; ring
  obtain ⟨f, L, hf, hL⟩ := exists_adic_limit (Ideal.span {ϖ}) (fun n b => c - G b ∈ Ideal.span {ϖ} ^ n)
    ⟨0, by simp⟩ (by
      intro n x hx
      obtain ⟨d, hd⟩ := (mem_span_pow_iff ϖ _ n).1 hx
      obtain ⟨b1, hb1⟩ := hstep d
      obtain ⟨e, he⟩ := (Ideal.mem_span_singleton'.1 hb1)
      refine ⟨x + ϖ ^ n * b1, ?_, ?_⟩
      · refine (mem_span_pow_iff ϖ _ (n + 1)).2 ⟨e, ?_⟩
        rw [map_add, hGp]
        have : d - G b1 = ϖ * e := by rw [← he]; ring
        calc c - (G x + ϖ ^ n * G b1) = (c - G x) - ϖ ^ n * G b1 := by ring
          _ = ϖ ^ n * (d - G b1) := by rw [hd]; ring
          _ = ϖ ^ (n + 1) * e := by rw [this]; ring
      · simp only [add_sub_cancel_left]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self ϖ) n))
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := Ideal.span {ϖ}) (M := R)
  intro n
  rw [SModEq.sub_mem, sub_zero, mem_smul_top_iff]
  obtain ⟨z, hz⟩ := (mem_span_pow_iff ϖ _ n).1 (hL n)
  have h1 : c - G L = (c - G (f n)) - G (L - f n) := by rw [map_sub]; ring
  rw [← neg_sub, neg_mem_iff, h1, hz, hGp]
  exact sub_mem (hf n) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self ϖ) n))

/-! ## The completed unramified setting -/

section Main

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  {σ : B ≃+* B}

variable (K) in
theorem one_lt_resCard : 1 < resCard K := Finite.one_lt_card

theorem residue_sigma (h : IsCompletedUnramifiedInt K B σ) (b : B) :
    residue B (σ b) = residue B b ^ resCard K := by
  have := h.frob_mod b
  rw [← sub_eq_zero, ← map_pow, ← map_sub, residue_eq_zero_iff]
  exact this

/-- Residue-level surjectivity of $x \mapsto \sigma x - c x$. -/
theorem residue_step (h : IsCompletedUnramifiedInt K B σ) (c d : B) :
    ∃ b, d - (σ b - c * b) ∈ maximalIdeal B := by
  have := h.residue_isAlgClosed
  have hq := one_lt_resCard K
  let p : (ResidueField B)[X] := X ^ resCard K - (C (residue B c) * X + C (residue B d))
  have hdeg : p.degree = resCard K := by
    have h1 : (C (residue B c) * X + C (residue B d)).degree <
        (X ^ resCard K : (ResidueField B)[X]).degree := by
      calc _ ≤ 1 := degree_linear_le
        _ < (resCard K : WithBot ℕ) := by exact_mod_cast hq
        _ = _ := (degree_X_pow _).symm
    rw [degree_sub_eq_left_of_degree_lt h1, degree_X_pow]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p
    (by rw [hdeg]; exact_mod_cast (by omega : resCard K ≠ 0))
  obtain ⟨b, rfl⟩ := residue_surjective x
  refine ⟨b, ?_⟩
  rw [← residue_eq_zero_iff]
  have hroot : residue B b ^ resCard K - (residue B c * residue B b + residue B d) = 0 := by
    simpa [p] using hx
  rw [map_sub, map_sub, map_mul, residue_sigma h]
  linear_combination -hroot

theorem mul_step (h : IsCompletedUnramifiedInt K B σ) (c : B) (hc : IsUnit c) :
    ∃ b0, IsUnit b0 ∧ σ b0 - c * b0 ∈ maximalIdeal B := by
  have := h.residue_isAlgClosed
  have hq := one_lt_resCard K
  have hrc : residue B c ≠ 0 := by
    rw [Ne, residue_eq_zero_iff]; exact notMem_maximalIdeal.2 hc
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (residue B c) (show 0 < resCard K - 1 by omega)
  obtain ⟨b, rfl⟩ := residue_surjective x
  have hxne : residue B b ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hx
    exact hrc hx.symm
  refine ⟨b, notMem_maximalIdeal.1 (by rwa [Ne, residue_eq_zero_iff] at hxne), ?_⟩
  rw [← residue_eq_zero_iff, map_sub, map_mul, residue_sigma h]
  have : residue B b ^ resCard K = residue B b ^ (resCard K - 1) * residue B b := by
    rw [← pow_succ]; congr 1; omega
  rw [this, hx]; ring

theorem exists_sigma_sub_mul (h : IsCompletedUnramifiedInt K B σ) (π : 𝒪[K]) (hπ : Irreducible π)
    (c d : B) : ∃ b, σ b - c * b = d := by
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (h.irreducible π hπ)
  have : IsAdicComplete (Ideal.span {algebraMap 𝒪[K] B π}) B := by rw [← hm]; exact h.complete
  let G : B →+ B :=
    { toFun := fun x => σ x - c * x
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add]; ring }
  obtain ⟨b, hb⟩ := surj_of_step (algebraMap 𝒪[K] B π) G
    (by intro x; show σ (_ * x) - c * (_ * x) = _ * (σ x - c * x); rw [map_mul, h.frob_fix]; ring)
    (by
      intro d
      obtain ⟨b, hb⟩ := residue_step h c d
      exact ⟨b, by rw [← hm]; exact hb⟩) d
  exact ⟨b, hb⟩

theorem isLocalHom_algebraMap (h : IsCompletedUnramifiedInt K B σ) (π : 𝒪[K]) (hπ : Irreducible π) :
    IsLocalHom (algebraMap 𝒪[K] B) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmA : a ∈ maximalIdeal 𝒪[K] := by rw [mem_maximalIdeal, mem_nonunits_iff]; exact hna
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ] at hmA
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hmA
  rw [← hx, map_mul] at ha
  exact (h.irreducible π hπ).not_isUnit (isUnit_of_mul_isUnit_right ha)

theorem exists_lift (h : IsCompletedUnramifiedInt K B σ) (π : 𝒪[K]) (hπ : Irreducible π) (z : B)
    (hz : σ z = z) : ∃ a : 𝒪[K], z - algebraMap 𝒪[K] B a ∈ maximalIdeal B := by
  classical
  have := isLocalHom_algebraMap h π hπ
  let _ : Fintype 𝓀[K] := Fintype.ofFinite _
  have hq := one_lt_resCard K
  have hqc : Fintype.card 𝓀[K] = resCard K := (Nat.card_eq_fintype_card).symm
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓀[K] →+* ResidueField B,
      ∀ r, φ (residue 𝒪[K] r) = residue B (algebraMap 𝒪[K] B r) :=
    ⟨ResidueField.map (algebraMap 𝒪[K] B), ResidueField.map_residue _⟩
  let Q : (ResidueField B)[X] := X ^ resCard K - X
  have hQd : Q.natDegree = resCard K := FiniteField.X_pow_card_sub_X_natDegree_eq _ hq
  have hQ0 : Q ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hQd; omega
  let S : Finset (ResidueField B) := Finset.univ.image φ
  let R : Finset (ResidueField B) := Q.roots.toFinset
  have hSR : S ⊆ R := by
    intro y hy
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def]
    simp only [Q, eval_sub, eval_pow, eval_X]
    rw [← map_pow, sub_eq_zero, ← hqc, FiniteField.pow_card]
  have hScard : S.card = resCard K := by
    rw [Finset.card_image_of_injective _ φ.injective, Finset.card_univ, hqc]
  have hRcard : R.card ≤ resCard K := by
    calc R.card ≤ Q.roots.card := Multiset.toFinset_card_le _
      _ ≤ Q.natDegree := card_roots' Q
      _ = _ := hQd
  have hSR' : S = R := Finset.eq_of_subset_of_card_le hSR (by omega)
  have hzR : residue B z ∈ R := by
    rw [Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def]
    simp only [Q, eval_sub, eval_pow, eval_X]
    have := residue_sigma h z
    rw [hz] at this
    rw [← this, sub_self]
  rw [← hSR'] at hzR
  obtain ⟨t, -, ht⟩ := Finset.mem_image.1 hzR
  obtain ⟨a, rfl⟩ := residue_surjective t
  refine ⟨a, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← ht, hφ, sub_self]

theorem add_ker_aux (h : IsCompletedUnramifiedInt K B σ) (b : B) (hb : σ b = b) :
    ∃ a : 𝒪[K], algebraMap 𝒪[K] B a = b := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ := h.irreducible π hπ
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hϖ
  have : IsAdicComplete (Ideal.span {algebraMap 𝒪[K] B π}) B := by rw [← hm]; exact h.complete
  have hmA := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  have hπm : π ∈ maximalIdeal 𝒪[K] := by rw [hmA]; exact Ideal.mem_span_singleton_self π
  obtain ⟨f, L, hf, hL⟩ := exists_adic_limit (maximalIdeal 𝒪[K])
    (fun n a => b - algebraMap 𝒪[K] B a ∈ Ideal.span {algebraMap 𝒪[K] B π} ^ n) ⟨0, by simp⟩ (by
      intro n a ha
      obtain ⟨z, hz⟩ := (mem_span_pow_iff _ _ n).1 ha
      have hσz : σ z = z := by
        have h1 : σ (b - algebraMap 𝒪[K] B a) = b - algebraMap 𝒪[K] B a := by
          rw [map_sub, hb, h.frob_fix]
        rw [hz, map_mul, map_pow, h.frob_fix] at h1
        exact mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) h1
      obtain ⟨a0, ha0⟩ := exists_lift h π hπ z hσz
      rw [hm] at ha0
      refine ⟨a + π ^ n * a0, ?_, ?_⟩
      · obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 ha0
        refine (mem_span_pow_iff _ _ (n + 1)).2 ⟨e, ?_⟩
        have h2 : z - algebraMap 𝒪[K] B a0 = algebraMap 𝒪[K] B π * e := by rw [← he]; ring
        calc b - algebraMap 𝒪[K] B (a + π ^ n * a0)
            = (b - algebraMap 𝒪[K] B a) - algebraMap 𝒪[K] B π ^ n * algebraMap 𝒪[K] B a0 := by
              simp only [map_add, map_mul, map_pow]; ring
          _ = algebraMap 𝒪[K] B π ^ n * (z - algebraMap 𝒪[K] B a0) := by rw [hz]; ring
          _ = _ := by rw [h2]; ring
      · simp only [add_sub_cancel_left]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm n))
  refine ⟨L, ?_⟩
  have h0 : b - algebraMap 𝒪[K] B L = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {algebraMap 𝒪[K] B π}) (M := B)
    intro n
    rw [SModEq.sub_mem, sub_zero, mem_smul_top_iff]
    have hLn := hL n
    rw [hmA] at hLn
    obtain ⟨w, hw⟩ := (mem_span_pow_iff _ _ n).1 hLn
    have h3 : b - algebraMap 𝒪[K] B L = (b - algebraMap 𝒪[K] B (f n)) - algebraMap 𝒪[K] B (L - f n) := by
      rw [map_sub]; ring
    rw [h3, hw, map_mul, map_pow]
    exact sub_mem (hf n)
      (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n))
  exact (sub_eq_zero.1 h0).symm

variable (K) in
/-- **Lemma 3.11** (Milne, *Class Field Theory*, Ch. I, Lemma 3.11): $b \mapsto \sigma b - b$ and
$b \mapsto \sigma b / b$ are surjective on $B$ and $B^\times$ with kernels $A$ and $A^\times$. Proof by successive
approximation modulo powers of a prime element $\pi$ of $A$ (`surj_of_step`, `exists_adic_limit`), the residue
equations being $x^q - \bar c x = \bar d$ (algebraically closed residue field) and, for the kernels, the fact that
the $q$ elements of $k$ are all the roots of $X^q - X$. -/
@[kb "milne2020cft" "Ch. I, Lemma 3.11"]
theorem frobeniusMinusOneSurjective : FrobeniusMinusOneSurjective K where
  add_surjective B _ _ _ _ σ h c := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    obtain ⟨b, hb⟩ := exists_sigma_sub_mul h π hπ 1 c
    exact ⟨b, by simpa using hb⟩
  add_ker B _ _ _ _ σ h b :=
    ⟨fun hb => add_ker_aux h b (sub_eq_zero.1 hb),
      fun ⟨a, ha⟩ => by rw [← ha, h.frob_fix, sub_self]⟩
  mul_surjective B _ _ _ _ σ h c := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (h.irreducible π hπ)
    obtain ⟨b0, hb0, hmem⟩ := mul_step h (c : B) c.isUnit
    rw [hm] at hmem
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hmem
    obtain ⟨y, hy⟩ := exists_sigma_sub_mul h π hπ c (-e)
    have hb : σ (b0 + algebraMap 𝒪[K] B π * y) = c * (b0 + algebraMap 𝒪[K] B π * y) := by
      rw [map_add, map_mul, h.frob_fix]
      linear_combination (-1 : B) * he + algebraMap 𝒪[K] B π * hy
    have hub : IsUnit (b0 + algebraMap 𝒪[K] B π * y) := by
      rw [← notMem_maximalIdeal]
      intro hmem2
      have : b0 ∈ maximalIdeal B := by
        have h4 : b0 = (b0 + algebraMap 𝒪[K] B π * y) - algebraMap 𝒪[K] B π * y := by ring
        rw [h4]
        exact sub_mem hmem2 (by rw [hm]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      exact notMem_maximalIdeal.2 hb0 this
    refine ⟨hub.unit, ?_⟩
    rw [div_eq_iff_eq_mul]
    ext
    simpa using hb
  mul_ker B _ _ _ _ σ h b := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    constructor
    · intro hb
      have hb' : σ (b : B) = b := by
        rw [div_eq_one] at hb
        simpa using congrArg Units.val hb
      obtain ⟨a, ha⟩ := add_ker_aux h b hb'
      have := isLocalHom_algebraMap h π hπ
      have hu : IsUnit a := isUnit_of_map_unit (algebraMap 𝒪[K] B) a (by rw [ha]; exact b.isUnit)
      refine ⟨hu.unit, ?_⟩
      ext
      simp [ha]
    · rintro ⟨u, rfl⟩
      rw [div_eq_one]
      ext
      simp [h.frob_fix]

end Main

end NumberFieldKB.MilneCFT.LocalCFT
