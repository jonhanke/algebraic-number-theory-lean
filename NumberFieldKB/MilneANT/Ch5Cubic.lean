import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch5CubicBound

/-!
# Milne, *Algebraic Number Theory*, Chapter 5: cubic fields with negative discriminant

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers.

* **Example 5.4** (`example_5_4`): for $K = \mathbb Q[\alpha]$, $\alpha$ a root of $X^3 + 10X + 1$:
  $\Delta_K = -4027$, $r = s = 1$, $\operatorname{Nm}(\alpha) = -1$, so $\alpha$ is a unit, of infinite order.
* **Lemma 5.13**: see `Ch5CubicBound.lean` (used here for Example 5.14).
* **Example 5.14** (`example_5_14_units`; the class group: `Ch5CubicClassGroup.lean`): for the same field, $-\alpha^{-1}$ is the
  fundamental unit $> 1$, $U_K = \{\pm\alpha^m\}$, and the class group is cyclic of order $6$.

The field is `MilneCubicField = AdjoinRoot (X^3 + 10X + 1)` over $\mathbb Q$ and `milneAlpha` the class of $X$ as an
element of $\mathcal O_K$. Real embeddings are ring homomorphisms $K \to \mathbb R$ (Milne identifies $K$ with a
subfield of $\mathbb R$ through its unique real embedding).
-/

open NumberField Polynomial NumberField.InfinitePlace

namespace NumberFieldKB.MilneANT

/-- Milne's cubic $X^3 + 10X + 1$ (Examples 5.4 and 5.14). -/
noncomputable abbrev milneCubic : ℚ[X] := X ^ 3 + C 10 * X + 1

/-- The cubic has degree three. -/
theorem milneCubic_natDegree : milneCubic.natDegree = 3 := by
  unfold milneCubic; compute_degree!

/-- The cubic is monic. -/
theorem milneCubic_monic : milneCubic.Monic := by
  unfold milneCubic; monicity!

/-- $X^3 + 10X + 1$ is irreducible over $\mathbb Q$ (a cubic without rational root: $\pm1$ are not roots). -/
theorem milneCubic_irreducible : Irreducible milneCubic := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [milneCubic_natDegree]; simp
  · intro x hx
    have hm : (X ^ 3 + C 10 * X + 1 : ℤ[X]).Monic := by monicity!
    have hr : aeval x (X ^ 3 + C 10 * X + 1 : ℤ[X]) = 0 := by
      have : x ^ 3 + 10 * x + 1 = 0 := by simpa [milneCubic, IsRoot] using hx
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, map_one]
      simpa using this
    obtain ⟨n, hn⟩ := isInteger_of_is_root_of_monic hm hr
    subst hn
    have h : (n : ℚ) ^ 3 + 10 * n + 1 = 0 := by
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, map_one] at hr
      simpa using hr
    have h' : n ^ 3 + 10 * n + 1 = 0 := by exact_mod_cast h
    rcases lt_trichotomy n 0 with h0 | h0 | h0
    · nlinarith [sq_nonneg n]
    · subst h0; simp at h'
    · nlinarith [sq_nonneg n]

instance : Fact (Irreducible milneCubic) := ⟨milneCubic_irreducible⟩

/-- The cubic field $K = \mathbb Q[\alpha] = \mathbb Q[X]/(X^3 + 10X + 1)$ of Examples 5.4 and 5.14. -/
abbrev MilneCubicField : Type := AdjoinRoot milneCubic

instance : NumberField MilneCubicField := by
  have : Module.Finite ℚ MilneCubicField :=
    (AdjoinRoot.powerBasis milneCubic_monic.ne_zero).finite
  exact ⟨⟩

/-- The relation $\alpha^3 + 10\alpha + 1 = 0$ in $K$. -/
theorem milneRoot_eq :
    (AdjoinRoot.root milneCubic) ^ 3 + 10 * AdjoinRoot.root milneCubic + 1 = 0 := by
  have := AdjoinRoot.eval₂_root milneCubic
  simpa [milneCubic] using this

/-- $\alpha$ is integral over $\mathbb Z$ (a root of a monic integer polynomial). -/
theorem milneRoot_integral : IsIntegral ℤ (AdjoinRoot.root milneCubic) := by
  refine ⟨X ^ 3 + C 10 * X + 1, by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_one]
  simpa using milneRoot_eq

/-- The root $\alpha$ of $X^3 + 10X + 1$, as an algebraic integer of $K$. -/
noncomputable def milneAlpha : 𝓞 MilneCubicField :=
  ⟨AdjoinRoot.root milneCubic, milneRoot_integral⟩

/-- $\alpha$ as a unit of $\mathcal O_K$: $\alpha \cdot (-(\alpha^2 + 10)) = 1$. -/
noncomputable def milneAlphaUnit : (𝓞 MilneCubicField)ˣ where
  val := milneAlpha
  inv := -(milneAlpha ^ 2 + 10)
  val_inv := by
    apply Subtype.ext
    have := milneRoot_eq
    show AdjoinRoot.root milneCubic * -(AdjoinRoot.root milneCubic ^ 2 + 10) = 1
    linear_combination (-1 : MilneCubicField) * this
  inv_val := by
    apply Subtype.ext
    have := milneRoot_eq
    show -(AdjoinRoot.root milneCubic ^ 2 + 10) * AdjoinRoot.root milneCubic = 1
    linear_combination (-1 : MilneCubicField) * this

/-- The power basis $1, \alpha, \alpha^2$ of $K$ over $\mathbb Q$. -/
noncomputable def milnePB : PowerBasis ℚ MilneCubicField :=
  AdjoinRoot.powerBasis milneCubic_monic.ne_zero

/-- The power basis has dimension three. -/
theorem milnePB_dim : milnePB.dim = 3 := by
  show (AdjoinRoot.powerBasis _).dim = 3
  rw [AdjoinRoot.powerBasis_dim]; exact milneCubic_natDegree

/-- The generator of the power basis is $\alpha$. -/
theorem milnePB_gen : milnePB.gen = AdjoinRoot.root milneCubic := by
  simp [milnePB]

/-- $K$ has degree three over $\mathbb Q$. -/
theorem milne_finrank : Module.finrank ℚ MilneCubicField = 3 := by
  rw [PowerBasis.finrank, milnePB_dim]

/-- The minimal polynomial of $\alpha$ over $\mathbb Q$ is $X^3 + 10X + 1$. -/
theorem milnePB_minpoly : minpoly ℚ (AdjoinRoot.root milneCubic) = milneCubic := by
  rw [← milnePB_gen]
  exact AdjoinRoot.minpoly_powerBasis_gen_of_monic milneCubic_monic

/-- $\operatorname{Nm}(\alpha) = -1$. -/
theorem milne_norm : Algebra.norm ℚ (AdjoinRoot.root milneCubic) = -1 := by
  rw [← milnePB_gen, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, milnePB_gen,
    milnePB_minpoly, milnePB_dim]
  simp [milneCubic]
  norm_num

/-- Small matrix computations for the traces: powers of the companion matrix of $X^3 + 10X + 1$. -/
theorem milne_matrix_traces (n : ℕ) (hn : n = 3) (c : ℕ → ℚ) (h0 : c 0 = 1) (h1 : c 1 = 10)
    (h2 : c 2 = 0) :
    let M : Matrix (Fin n) (Fin n) ℚ :=
      Matrix.of fun i j => if (j : ℕ) + 1 = n then -c i else if (i : ℕ) = j + 1 then 1 else 0
    M.trace = 0 ∧ (M ^ 2).trace = -20 ∧ (M ^ 3).trace = -3 ∧ (M ^ 4).trace = 200 := by
  subst hn
  intro M
  simp only [M]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [Matrix.trace, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2] <;> norm_num

/-- The trace of $\alpha^k$ is the trace of the $k$-th power of the multiplication matrix. -/
theorem milne_trace_pow (k : ℕ) :
    Algebra.trace ℚ MilneCubicField (AdjoinRoot.root milneCubic ^ k) =
      ((Algebra.leftMulMatrix milnePB.basis (AdjoinRoot.root milneCubic)) ^ k).trace := by
  rw [Algebra.trace_eq_matrix_trace milnePB.basis, map_pow]

/-- The multiplication-by-$\alpha$ matrix in the power basis (the companion matrix). -/
theorem milne_leftMul : Algebra.leftMulMatrix milnePB.basis (AdjoinRoot.root milneCubic) =
    Matrix.of fun (i j : Fin milnePB.dim) =>
      if (j : ℕ) + 1 = milnePB.dim then -(milneCubic.coeff i)
      else if (i : ℕ) = j + 1 then 1 else 0 := by
  have := PowerBasis.leftMulMatrix milnePB
  rw [PowerBasis.minpolyGen_eq, milnePB_gen, milnePB_minpoly] at this
  exact this

/-- The traces of $1, \alpha, \dots, \alpha^4$ are $3, 0, -20, -3, 200$. -/
theorem milne_traces :
    Algebra.trace ℚ MilneCubicField (AdjoinRoot.root milneCubic ^ 0) = 3 ∧
    Algebra.trace ℚ MilneCubicField (AdjoinRoot.root milneCubic ^ 1) = 0 ∧
    Algebra.trace ℚ MilneCubicField (AdjoinRoot.root milneCubic ^ 2) = -20 ∧
    Algebra.trace ℚ MilneCubicField (AdjoinRoot.root milneCubic ^ 3) = -3 ∧
    Algebra.trace ℚ MilneCubicField (AdjoinRoot.root milneCubic ^ 4) = 200 := by
  have h := milne_matrix_traces milnePB.dim milnePB_dim milneCubic.coeff
    (by simp [milneCubic, coeff_one]) (by simp [milneCubic, coeff_one])
    (by simp [milneCubic, coeff_one])
  rw [milne_trace_pow 0, milne_trace_pow 1, milne_trace_pow 2, milne_trace_pow 3, milne_trace_pow 4,
    milne_leftMul]
  refine ⟨?_, by simpa using h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  simp [Matrix.trace, milnePB_dim]

/-- The determinant of the trace matrix, given the traces, is $-4027$. -/
theorem milne_det (n : ℕ) (hn : n = 3) (T : ℕ → ℚ) (T0 : T 0 = 3) (T1 : T 1 = 0) (T2 : T 2 = -20)
    (T3 : T 3 = -3) (T4 : T 4 = 200) :
    (Matrix.of fun (i j : Fin n) => T ((i : ℕ) + j)).det = -4027 := by
  subst hn
  rw [Matrix.det_fin_three]
  simp [T0, T1, T2, T3, T4]
  norm_num

/-- The discriminant of the power basis $1, \alpha, \alpha^2$ is $-4027$. -/
theorem milne_discr_pb : Algebra.discr ℚ milnePB.basis = -4027 := by
  rw [Algebra.discr_def]
  have : Algebra.traceMatrix ℚ milnePB.basis = Matrix.of fun (i j : Fin milnePB.dim) =>
      Algebra.trace ℚ MilneCubicField (AdjoinRoot.root milneCubic ^ ((i : ℕ) + j)) := by
    ext i j
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, pow_add, milnePB_gen]
  rw [this]
  obtain ⟨T0, T1, T2, T3, T4⟩ := milne_traces
  exact milne_det _ milnePB_dim
    (fun k => Algebra.trace ℚ MilneCubicField (AdjoinRoot.root milneCubic ^ k)) T0 T1 T2 T3 T4

/-- If $m^2 D = -4027$ then $D = -4027$, since $4027$ is prime. -/
theorem milne_discr_sq (m D : ℤ) (h : m ^ 2 * D = -4027) : D = -4027 := by
  have hp : Nat.Prime 4027 := by norm_num
  have h1 : m.natAbs ∣ 4027 := by
    have : (m.natAbs : ℤ) ∣ 4027 := by
      refine ⟨m.natAbs * (-D), ?_⟩
      have : (m.natAbs : ℤ) ^ 2 = m ^ 2 := Int.natAbs_sq m
      rw [← mul_assoc, ← sq, this]; linarith
    exact_mod_cast this
  rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
  · have : m ^ 2 = 1 := by
      rw [← Int.natAbs_sq, h2]; norm_num
    rw [this] at h; linarith
  · have : m ^ 2 = 4027 ^ 2 := by
      rw [← Int.natAbs_sq, h2]; norm_num
    rw [this] at h; omega

/-- The discriminant of $K$ is $-4027$: the index of $\mathbb Z[\alpha]$ in $\mathcal O_K$, squared, divides
the prime $4027$. -/
theorem milne_discr : discr MilneCubicField = -4027 := by
  have hrank : Module.finrank ℤ (𝓞 MilneCubicField) = 3 := by
    rw [RingOfIntegers.rank, milne_finrank]
  let bO : Module.Basis (Fin 3) ℤ (𝓞 MilneCubicField) := Module.finBasisOfFinrankEq ℤ _ hrank
  have hD : (discr MilneCubicField : ℚ) =
      Algebra.discr ℚ (bO.localizationLocalization ℚ (nonZeroDivisors ℤ) MilneCubicField) := by
    rw [← NumberField.discr_eq_discr MilneCubicField bO,
      Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) MilneCubicField bO]
    simp
  let v : Fin 3 → MilneCubicField := fun j => AdjoinRoot.root milneCubic ^ (j : ℕ)
  have hv : Algebra.discr ℚ v = -4027 := by
    rw [← milne_discr_pb, ← Algebra.discr_reindex ℚ milnePB.basis (finCongr milnePB_dim)]
    congr 1
    funext j
    simp [v, PowerBasis.coe_basis, milnePB_gen]
  let P : Matrix (Fin 3) (Fin 3) ℚ := fun i j => (bO.repr (milneAlpha ^ (j : ℕ)) i : ℚ)
  have hvec : v = Matrix.vecMul
      (bO.localizationLocalization ℚ (nonZeroDivisors ℤ) MilneCubicField)
      (P.map (algebraMap ℚ MilneCubicField)) := by
    funext j
    have h1 := bO.sum_repr (milneAlpha ^ (j : ℕ))
    have h2 : v j = ((milneAlpha ^ (j : ℕ) : 𝓞 MilneCubicField) : MilneCubicField) := by
      rfl
    rw [h2, ← h1]
    simp [Matrix.vecMul, dotProduct, mul_comm]
    exact Finset.sum_congr rfl fun x _ => rfl
  have hdet := Algebra.discr_of_matrix_vecMul
    (bO.localizationLocalization ℚ (nonZeroDivisors ℤ) MilneCubicField) P
  rw [← hvec, hv, ← hD] at hdet
  have hP : P.det =
      ((Matrix.of fun i j : Fin 3 => bO.repr (milneAlpha ^ (j : ℕ)) i).det : ℤ) := by
    exact ((Int.castRingHom ℚ).map_det
      (Matrix.of fun i j : Fin 3 => bO.repr (milneAlpha ^ (j : ℕ)) i)).symm
  rw [hP] at hdet
  apply milne_discr_sq (Matrix.of fun i j : Fin 3 => bO.repr (milneAlpha ^ (j : ℕ)) i).det
  exact_mod_cast hdet.symm

/-- $K$ has one real and one complex place. -/
theorem milne_places : nrRealPlaces MilneCubicField = 1 ∧ nrComplexPlaces MilneCubicField = 1 := by
  have hs := NumberField.sign_discr MilneCubicField
  rw [milne_discr] at hs
  have hr := card_add_two_mul_card_eq_rank (K := MilneCubicField)
  rw [milne_finrank] at hr
  rcases Nat.even_or_odd (nrComplexPlaces MilneCubicField) with he | ho
  · rw [he.neg_one_pow] at hs
    exact absurd hs (by decide)
  · obtain ⟨k, hk⟩ := ho
    omega

/-- $\alpha$ has infinite order (the torsion units of a field of odd degree are $\pm1$). -/
theorem milne_not_finOrder : ¬ IsOfFinOrder milneAlphaUnit := by
  intro h
  have mem : milneAlphaUnit ∈ Units.torsion MilneCubicField := (CommGroup.mem_torsion _).2 h
  have hodd : Odd (Module.finrank ℚ MilneCubicField) := by rw [milne_finrank]; decide
  have key : ((milneAlphaUnit : 𝓞 MilneCubicField) : MilneCubicField) =
      AdjoinRoot.root milneCubic := rfl
  have := milneRoot_eq
  rcases Units.torsion_eq_one_or_neg_one_of_odd_finrank hodd ⟨_, mem⟩ with h1 | h1
  · have h2 : ((milneAlphaUnit : 𝓞 MilneCubicField) : MilneCubicField) = 1 := by
      have := congrArg
        (fun u : (𝓞 MilneCubicField)ˣ => ((u : 𝓞 MilneCubicField) : MilneCubicField)) h1
      simpa using this
    rw [key] at h2
    rw [h2] at this
    norm_num at this
  · have h2 : ((milneAlphaUnit : 𝓞 MilneCubicField) : MilneCubicField) = -1 := by
      have := congrArg
        (fun u : (𝓞 MilneCubicField)ˣ => ((u : 𝓞 MilneCubicField) : MilneCubicField)) h1
      simpa using this
    rw [key] at h2
    rw [h2] at this
    norm_num at this

/-- **Example 5.4.** Let $K = \mathbb Q[\alpha]$ with $\alpha$ a root of $X^3 + 10X + 1$. Then $\Delta_K = -4027$;
since $\operatorname{sign}(\Delta_K) = (-1)^s$ and $r + 2s = 3$, $r = s = 1$; $\operatorname{Nm}(\alpha) = -1$, so
$\alpha$ is a unit; and $\alpha$ has infinite order. -/
@[kb "milne2020ant" "v3.08, Example 5.4, p. 86"]
theorem example_5_4 :
    discr MilneCubicField = -4027 ∧ nrRealPlaces MilneCubicField = 1 ∧
      nrComplexPlaces MilneCubicField = 1 ∧
      Algebra.norm ℚ (AdjoinRoot.root milneCubic) = -1 ∧ IsUnit milneAlpha ∧
      ¬ IsOfFinOrder milneAlphaUnit :=
  ⟨milne_discr, milne_places.1, milne_places.2, milne_norm, ⟨milneAlphaUnit, rfl⟩,
    milne_not_finOrder⟩

/-- A unit $\varepsilon$ generates the units up to sign: every unit is $\pm\varepsilon^m$. -/
def IsFundUnit {R : Type*} [CommRing R] (ε : Rˣ) : Prop :=
  ∀ u : Rˣ, ∃ m : ℤ, u = ε ^ m ∨ u = -ε ^ m

/-- $(-y)^m = \pm y^m$. -/
theorem neg_zpow_cases {R : Type*} [CommRing R] (y : Rˣ) (m : ℤ) :
    (-y) ^ m = y ^ m ∨ (-y) ^ m = -y ^ m := by
  have h : -y = (-1 : Rˣ) * y := by simp
  rw [h, mul_zpow]
  rcases Int.even_or_odd m with he | ho
  · left; rw [he.neg_one_zpow, one_mul]
  · right; rw [ho.neg_one_zpow, neg_one_mul]

/-- If $\varepsilon$ generates the units up to sign, so does $-\varepsilon$. -/
theorem IsFundUnit.neg {R : Type*} [CommRing R] {ε : Rˣ} (h : IsFundUnit ε) :
    IsFundUnit (-ε) := by
  intro u
  obtain ⟨m, hm⟩ := h u
  refine ⟨m, ?_⟩
  rcases neg_zpow_cases ε m with h1 | h1 <;> rcases hm with h2 | h2 <;> rw [h1] <;> simp [h2]

/-- If $\varepsilon$ generates the units up to sign, so does $\varepsilon^{-1}$. -/
theorem IsFundUnit.inv {R : Type*} [CommRing R] {ε : Rˣ} (h : IsFundUnit ε) :
    IsFundUnit ε⁻¹ := by
  intro u
  obtain ⟨m, hm⟩ := h u
  refine ⟨-m, ?_⟩
  simpa using hm

/-- The value of a real embedding on a unit of the ring of integers. -/
def unitVal {K : Type*} [Field K] [NumberField K] (φ : K →+* ℝ) (u : (𝓞 K)ˣ) : ℝ :=
  φ ((u : 𝓞 K) : K)

/-- `unitVal` is multiplicative. -/
theorem unitVal_mul {K : Type*} [Field K] [NumberField K] (φ : K →+* ℝ) (u v : (𝓞 K)ˣ) :
    unitVal φ (u * v) = unitVal φ u * unitVal φ v := by
  simp [unitVal]

/-- `unitVal` of the negative. -/
theorem unitVal_neg {K : Type*} [Field K] [NumberField K] (φ : K →+* ℝ) (u : (𝓞 K)ˣ) :
    unitVal φ (-u) = - unitVal φ u := by
  simp [unitVal]

/-- `unitVal` of the inverse. -/
theorem unitVal_inv {K : Type*} [Field K] [NumberField K] (φ : K →+* ℝ) (u : (𝓞 K)ˣ) :
    unitVal φ u⁻¹ = (unitVal φ u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← unitVal_mul]; simp [unitVal]

/-- `unitVal` of a unit is nonzero. -/
theorem unitVal_ne_zero {K : Type*} [Field K] [NumberField K] (φ : K →+* ℝ) (u : (𝓞 K)ˣ) :
    unitVal φ u ≠ 0 := by
  intro h
  have := unitVal_mul φ u u⁻¹
  rw [h, zero_mul] at this
  simp [unitVal] at this

/-- `unitVal` of an integer power. -/
theorem unitVal_zpow {K : Type*} [Field K] [NumberField K] (φ : K →+* ℝ) (u : (𝓞 K)ˣ) (m : ℤ) :
    unitVal φ (u ^ m) = (unitVal φ u) ^ m := by
  induction m using Int.induction_on with
  | zero => simp [unitVal]
  | succ n ih => rw [zpow_add_one, unitVal_mul, ih, zpow_add_one₀ (unitVal_ne_zero φ u)]
  | pred n ih =>
    rw [zpow_sub_one, unitVal_mul, unitVal_inv, ih, zpow_sub_one₀ (unitVal_ne_zero φ u)]

/-- A sign-generating unit whose absolute value exceeds one can be replaced by one exceeding one. -/
theorem exists_fund_gt_one_aux {K : Type*} [Field K] [NumberField K] (φ : K →+* ℝ)
    {ε : (𝓞 K)ˣ} (h : IsFundUnit ε) (ht : 1 < |unitVal φ ε|) :
    ∃ ε1 : (𝓞 K)ˣ, IsFundUnit ε1 ∧ 1 < unitVal φ ε1 := by
  rcases lt_or_gt_of_ne (unitVal_ne_zero φ ε) with hneg | hpos
  · refine ⟨-ε, h.neg, ?_⟩
    rw [unitVal_neg]
    rw [abs_of_neg hneg] at ht
    exact ht
  · refine ⟨ε, h, ?_⟩
    rwa [abs_of_pos hpos] at ht

/-- A sign-generating unit whose absolute value is not one can be replaced by one exceeding one. -/
theorem exists_fund_gt_one {K : Type*} [Field K] [NumberField K] (φ : K →+* ℝ) {ε : (𝓞 K)ˣ}
    (h : IsFundUnit ε) (ht : |unitVal φ ε| ≠ 1) :
    ∃ ε1 : (𝓞 K)ˣ, IsFundUnit ε1 ∧ 1 < unitVal φ ε1 := by
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · apply exists_fund_gt_one_aux φ h.inv
    rw [unitVal_inv, abs_inv]
    have : 0 < |unitVal φ ε| := abs_pos.2 (unitVal_ne_zero φ ε)
    exact one_lt_inv₀ this |>.2 hlt
  · exact exists_fund_gt_one_aux φ h hgt

/-- Every real embedding sends $\alpha$ into $(-1, 0)$. -/
theorem milne_real_root (φ : MilneCubicField →+* ℝ) :
    φ (AdjoinRoot.root milneCubic) ^ 3 + 10 * φ (AdjoinRoot.root milneCubic) + 1 = 0 ∧
      -1 < φ (AdjoinRoot.root milneCubic) ∧ φ (AdjoinRoot.root milneCubic) < 0 := by
  have h := congrArg φ milneRoot_eq
  have h10 : φ 10 = 10 := map_ofNat φ 10
  simp only [map_add, map_mul, map_pow, map_one, map_zero, h10] at h
  set a := φ (AdjoinRoot.root milneCubic)
  refine ⟨h, ?_, ?_⟩
  · by_contra hle
    push Not at hle
    nlinarith [sq_nonneg a, sq_nonneg (a + 1)]
  · by_contra hle
    push Not at hle
    nlinarith [sq_nonneg a, pow_nonneg hle 3]

/-- The unit $-\alpha^{-1}$ equals $\alpha^2 + 10$ in $\mathcal O_K$. -/
theorem milne_e_val : ((-milneAlphaUnit⁻¹ : (𝓞 MilneCubicField)ˣ) : 𝓞 MilneCubicField) =
    milneAlpha ^ 2 + 10 := by
  show -(-(milneAlpha ^ 2 + 10)) = _
  simp

/-- Under any real embedding, $-\alpha^{-1}$ lies in $(10, 11)$. -/
theorem milne_e_bounds (φ : MilneCubicField →+* ℝ) :
    10 < unitVal φ (-milneAlphaUnit⁻¹) ∧ unitVal φ (-milneAlphaUnit⁻¹) < 11 := by
  obtain ⟨_, h1, h2⟩ := milne_real_root φ
  have : unitVal φ (-milneAlphaUnit⁻¹) = φ (AdjoinRoot.root milneCubic) ^ 2 + 10 := by
    unfold unitVal
    rw [milne_e_val]
    show φ (AdjoinRoot.root milneCubic ^ 2 + 10) = _
    rw [map_add, map_pow, map_ofNat]
  rw [this]
  constructor <;> nlinarith

/-- The units of $K$ are generated up to sign by a single unit (unit rank one, torsion $\pm1$). -/
theorem milne_exists_fund : ∃ ε : (𝓞 MilneCubicField)ˣ, IsFundUnit ε := by
  have hrank : Units.rank MilneCubicField = 1 := by
    rw [Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces, milne_places.1, milne_places.2]
  have : Unique (Fin (Units.rank MilneCubicField)) :=
    ⟨⟨⟨0, by omega⟩⟩, fun a => Fin.ext (by have := a.2; omega)⟩
  refine ⟨Units.fundSystem MilneCubicField default, fun u => ?_⟩
  obtain ⟨⟨ζ, e⟩, hx, _⟩ := Units.exist_unique_eq_mul_prod MilneCubicField u
  simp only [Fintype.prod_unique] at hx
  have hodd : Odd (Module.finrank ℚ MilneCubicField) := by rw [milne_finrank]; decide
  refine ⟨e default, ?_⟩
  rcases Units.torsion_eq_one_or_neg_one_of_odd_finrank hodd ζ with h | h
  · left; rw [hx, h, one_mul]
  · right; rw [hx, h, neg_one_mul]

/-- If $x > 10$ and $10 < x^m < 11$ for an integer $m$, then $m = 1$. -/
theorem milne_zpow_eq_one (x : ℝ) (m : ℤ) (hx : 10 < x) (hlo : 10 < x ^ m) (hhi : x ^ m < 11) :
    m = 1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt'
  · have : x ^ m ≤ 1 := zpow_le_one_of_nonpos₀ (by linarith) (by omega)
    linarith
  · have h2 : x ^ (2 : ℤ) ≤ x ^ m := zpow_le_zpow_right₀ (by linarith) (by omega)
    have h3 : x ^ (2 : ℤ) = x * x := by rw [zpow_two]
    have h4 : 10 * 10 < x * x := mul_lt_mul'' hx hx (by norm_num) (by norm_num)
    have h5 : x * x ≤ x ^ m := h3 ▸ h2
    have h6 := lt_trans (lt_of_lt_of_le h4 h5) hhi
    norm_num at h6

/-- **Example 5.14, units.** For $K = \mathbb Q[\alpha]$, $\alpha^3 + 10\alpha + 1 = 0$: the unit
$\varepsilon = -\alpha^{-1}$ ($\approx 10.00998$ under the real embedding, where $\alpha \approx -0.0999$) is the
fundamental unit $> 1$, and $U_K = \{\pm\alpha^m : m \in \mathbb Z\}$. -/
@[kb "milne2020ant" "v3.08, Example 5.14, p. 93"]
theorem example_5_14_units :
    (∀ φ : MilneCubicField →+* ℝ,
      1 < φ (((-milneAlphaUnit⁻¹ : (𝓞 MilneCubicField)ˣ) : 𝓞 MilneCubicField) : MilneCubicField)) ∧
      ∀ u : (𝓞 MilneCubicField)ˣ, ∃ m : ℤ, u = milneAlphaUnit ^ m ∨ u = -milneAlphaUnit ^ m := by
  refine ⟨fun φ => ?_, ?_⟩
  · have := (milne_e_bounds φ).1
    exact lt_trans (by norm_num) this
  · -- a real embedding
    obtain ⟨φ0⟩ : Nonempty (MilneCubicField →+* ℝ) := by
      have hpos : 0 < nrRealPlaces MilneCubicField := by rw [milne_places.1]; norm_num
      have : Nonempty {w : InfinitePlace MilneCubicField // w.IsReal} :=
        by classical exact Fintype.card_pos_iff.1 hpos
      obtain ⟨⟨w, hw⟩⟩ := this
      exact ⟨embedding_of_isReal hw⟩
    obtain ⟨ε0, h0⟩ := milne_exists_fund
    have hE := milne_e_bounds φ0
    have ht : |unitVal φ0 ε0| ≠ 1 := by
      intro h1
      obtain ⟨m, hm⟩ := h0 (-milneAlphaUnit⁻¹)
      have : |unitVal φ0 (-milneAlphaUnit⁻¹)| = 1 := by
        rcases hm with hm | hm <;> rw [hm] <;> simp [unitVal_neg, unitVal_zpow, abs_zpow, h1]
      rw [abs_of_pos (by linarith [hE.1])] at this
      linarith [hE.1]
    obtain ⟨ε1, h1, hgt⟩ := exists_fund_gt_one φ0 h0 ht
    have hb := lemma_5_13 (K := MilneCubicField) milne_finrank
      (by rw [milne_discr]; norm_num) ε1 h1 φ0 hgt
    rw [milne_discr] at hb
    have hx : (4027 : ℝ) < 4 * unitVal φ0 ε1 ^ 3 + 24 := by
      have : |((-4027 : ℤ) : ℝ)| = 4027 := by norm_num
      rw [this] at hb
      exact hb
    set x := unitVal φ0 ε1 with hxdef
    clear_value x
    have hx10 : 10 < x := by
      by_contra hle
      push Not at hle
      nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) hle 3]
    have hxpos : 0 < x := by linarith
    -- the unit `e = -α⁻¹` is a power of `ε1`
    obtain ⟨m, hm⟩ := h1 (-milneAlphaUnit⁻¹)
    have heq : -milneAlphaUnit⁻¹ = ε1 := by
      rcases hm with hm | hm
      · have hv : unitVal φ0 (-milneAlphaUnit⁻¹) = x ^ m := by
          rw [hm, unitVal_zpow, hxdef]
        have hlo : 10 < x ^ m := hv ▸ hE.1
        have hhi : x ^ m < 11 := hv ▸ hE.2
        have hm1 : m = 1 := milne_zpow_eq_one x m hx10 hlo hhi
        rw [hm, hm1, zpow_one]
      · exfalso
        have hv : unitVal φ0 (-milneAlphaUnit⁻¹) = - x ^ m := by
          rw [hm, unitVal_neg, unitVal_zpow, hxdef]
        have : 0 < x ^ m := zpow_pos hxpos m
        linarith [hE.1]
    have he : IsFundUnit (-milneAlphaUnit⁻¹) := heq ▸ h1
    have hα : IsFundUnit milneAlphaUnit := by
      have := he.neg.inv
      simpa using this
    exact hα

end NumberFieldKB.MilneANT
