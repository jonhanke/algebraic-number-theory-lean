import NumberFieldKB.WeilBNT.PFieldUnits
import NumberFieldKB.WeilBNT.PFieldExtensions
import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Weil, *Basic Number Theory*, I.§4: Cor. 1 of Thm. 7, Thm. 8, Prop. 6 and text p. 21–23

$K$ is a $p$-field (`PField`), $M^\times$ a subgroup of $K^\times$ of order $q-1$ (Thm. 7, `PFieldUnits`).

* `weil_I_4_cor1_thm7`: Cor. 1 of Thm. 7. In characteristic $p$, $M=M^\times\cup\{0\}$ is a subfield of $K$;
  `weil_I_4_cor1_thm7_comm`: if $K$ is moreover commutative, $M$ is the algebraic closure of the prime field in $K$.
* **`weil_I_4_thm8`**: Thm. 8. A commutative $p$-field of characteristic $p$ is isomorphic, as a topological field, to
  the field $\mathbb F_q((T))$ of formal Laurent series over a finite field with $q$ elements ($q$ = the module of $K$;
  Mathlib's `LaurentSeries (GaloisField p f)` with its $T$-adic topology).
* `weil_I_4_prop6`: Prop. 6. If $K_0$ is a $p$-field contained in the center of $K$ (here: $K$ is an algebra over the
  field $K_0$), the maximal compact subring $R$ of $K$ consists of the elements of $K$ integral over $R_0$;
  text p. 23 is the commutative case.
-/

open Topology Filter
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}

open scoped IsMulCommutative in
/-- The elements of `M` generate a commutative subring `C` of `K` (the group `M` is cyclic), and every nonzero
element of `C` with `z ^ (q - 1) = 1` lies in `M` (counting the roots of `X ^ (q - 1) - 1` in the domain `C`). -/
theorem cor1_key (hK : IsPField K p) (M : Subgroup Kˣ) (hM : Nat.card M = pq hK - 1) :
    ∃ C : Subring K, IsMulCommutative C ∧ (∀ μ ∈ M, ((μ : Kˣ) : K) ∈ C) ∧
      ∀ z ∈ C, z ≠ 0 → z ^ (pq hK - 1) = 1 → ∃ μ ∈ M, z = ((μ : Kˣ) : K) := by
  classical
  have hcyc := weil_I_4_thm7_cyclic hK M hM
  have hpos : 0 < pq hK - 1 := by have := one_lt_pq_nat hK; omega
  let s : Set K := {x | ∃ μ ∈ M, x = ((μ : Kˣ) : K)}
  have hs : s.Pairwise Commute := by
    intro a ha b hb _
    obtain ⟨μ, hμ, rfl⟩ := ha
    obtain ⟨ν, hν, rfl⟩ := hb
    have := mul_comm (⟨μ, hμ⟩ : M) ⟨ν, hν⟩
    have h2 := congrArg (fun m : M => ((m : Kˣ) : K)) this
    exact h2
  have hC : IsMulCommutative (Subring.closure s) := Subring.isMulCommutative_closure hs
  refine ⟨Subring.closure s, hC, fun μ hμ => Subring.subset_closure ⟨μ, hμ, rfl⟩, ?_⟩
  intro z hz hz0 hzq
  have hD : IsDomain (Subring.closure s) := inferInstance
  have : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; omega)
  have : Fintype M := Fintype.ofFinite M
  have hsub : ∀ μ : M, ((μ : Kˣ) : K) ∈ Subring.closure s :=
    fun μ => Subring.subset_closure ⟨μ, μ.2, rfl⟩
  let T := (Polynomial.nthRoots (pq hK - 1) (1 : Subring.closure s)).toFinset
  have hT : T.card ≤ pq hK - 1 :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  let Im : Finset (Subring.closure s) :=
    Finset.univ.image (fun μ : M => (⟨((μ : Kˣ) : K), hsub μ⟩ : Subring.closure s))
  have hIm : Im ⊆ T := by
    intro y hy
    obtain ⟨μ, -, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hpos]
    exact Subtype.ext (by simpa using (subgroup_elem hK M hM μ).1)
  have hinj : Function.Injective
      (fun μ : M => (⟨((μ : Kˣ) : K), hsub μ⟩ : Subring.closure s)) :=
    fun a b h => Subtype.ext (Units.ext (congrArg Subtype.val h))
  have hcard : Im.card = pq hK - 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card, hM]
  have hEq : Im = T := Finset.eq_of_subset_of_card_le hIm (by omega)
  have hxT : (⟨z, hz⟩ : Subring.closure s) ∈ T := by
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hpos]
    exact Subtype.ext (by simpa using hzq)
  rw [← hEq] at hxT
  obtain ⟨μ, -, hμ⟩ := Finset.mem_image.1 hxT
  exact ⟨μ, μ.2, (congrArg Subtype.val hμ).symm⟩

@[kb "weil1973bnt" "Ch. I, §4, Cor. 1 of Thm. 7 (M is a field)"]
theorem weil_I_4_cor1_thm7 (hK : IsPField K p) [CharP K p] (M : Subgroup Kˣ) (hM : Nat.card M = pq hK - 1) :
    ∃ L : Subfield K, (L : Set K) = {x | x = 0 ∨ ∃ μ ∈ M, x = ((μ : Kˣ) : K)} := by
  classical
  have : Fact p.Prime := ⟨hK.1⟩
  obtain ⟨C, hCc, hCM, hroot⟩ := cor1_key hK M hM
  obtain ⟨f, -, hqf⟩ := weil_I_4_thm6_residue hK
  have hpos : 0 < pq hK - 1 := by have := one_lt_pq_nat hK; omega
  set S : Set K := {x | x = 0 ∨ ∃ μ ∈ M, x = ((μ : Kˣ) : K)} with hS
  have hSC : ∀ x ∈ S, x ∈ C := by
    rintro x (rfl | ⟨μ, hμ, rfl⟩)
    · exact C.zero_mem
    · exact hCM μ hμ
  have hSq : ∀ x ∈ S, x ^ pq hK = x := by
    rintro x (rfl | ⟨μ, hμ, rfl⟩)
    · have : pq hK ≠ 0 := by omega
      simp [this]
    · have h := (subgroup_elem hK M hM ⟨μ, hμ⟩).1
      have : pq hK = (pq hK - 1) + 1 := by omega
      rw [this, pow_succ, h, one_mul]
  have hfix : ∀ z ∈ C, z ^ pq hK = z → z ∈ S := by
    intro z hz hzq
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · refine Or.inr (hroot z hz hz0 ?_)
      have : z * z ^ (pq hK - 1) = z * 1 := by
        rw [← pow_succ', mul_one, show pq hK - 1 + 1 = pq hK by omega, hzq]
      exact mul_left_cancel₀ hz0 this
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    intro x hx y hy
    have h1 := hSC x hx
    have h2 := hSC y hy
    have := hCc.is_comm.comm (⟨x, h1⟩ : C) ⟨y, h2⟩
    exact congrArg Subtype.val this
  have hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S := by
    intro x hx y hy
    apply hfix _ (C.add_mem (hSC x hx) (hSC y hy))
    rw [hqf, add_pow_char_pow_of_commute p f (hcomm x hx y hy), ← hqf, hSq x hx, hSq y hy]
  have hneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    apply hfix _ (C.neg_mem (hSC x hx))
    have hxn : Commute x (-x) := (Commute.refl x).neg_right
    have h := add_pow_char_pow_of_commute p f hxn
    rw [add_neg_cancel, zero_pow (by rw [← hqf]; omega), ← hqf, hSq x hx] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro x (rfl | ⟨μ, hμ, rfl⟩) y (rfl | ⟨ν, hν, rfl⟩)
    · simp [hS]
    · simp [hS]
    · simp [hS]
    · exact Or.inr ⟨μ * ν, M.mul_mem hμ hν, by simp⟩
  have hinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    rintro x (rfl | ⟨μ, hμ, rfl⟩)
    · simp [hS]
    · exact Or.inr ⟨μ⁻¹, M.inv_mem hμ, by simp⟩
  refine ⟨
    { carrier := S
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      one_mem' := Or.inr ⟨1, M.one_mem, by simp⟩
      add_mem' := fun {a b} ha hb => hadd a ha b hb
      zero_mem' := Or.inl rfl
      neg_mem' := fun {a} ha => hneg a ha
      inv_mem' := fun a ha => hinv a ha }, rfl⟩

@[kb "weil1973bnt" "Ch. I, §4, Cor. 1 of Thm. 7 (commutative case: the algebraic closure of the prime field)"]
theorem weil_I_4_cor1_thm7_comm {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] (hF : IsPField F p) [CharP F p]
    (M : Subgroup Fˣ) (hM : Nat.card M = pq hF - 1) (x : F) :
    letI := ZMod.algebra F p
    IsAlgebraic (ZMod p) x ↔ (x = 0 ∨ ∃ μ ∈ M, x = ((μ : Fˣ) : F)) := by
  classical
  have : Fact p.Prime := ⟨hF.1⟩
  let _ := ZMod.algebra F p
  have hpos : 0 < pq hF - 1 := by have := one_lt_pq_nat hF; omega
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    refine Or.inr ?_
    have hint : IsIntegral (ZMod p) x := hx.isIntegral
    have : FiniteDimensional (ZMod p) (IntermediateField.adjoin (ZMod p) {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    have : Finite (IntermediateField.adjoin (ZMod p) {x}) := Module.finite_of_finite (ZMod p)
    have : Fintype (IntermediateField.adjoin (ZMod p) {x}) := Fintype.ofFinite _
    have hmem : x ∈ IntermediateField.adjoin (ZMod p) {x} :=
      IntermediateField.mem_adjoin_simple_self _ x
    let a : IntermediateField.adjoin (ZMod p) {x} := ⟨x, hmem⟩
    have ha : a ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
    have h1 := FiniteField.pow_card_sub_one_eq_one a ha
    obtain ⟨n, -, hn⟩ := FiniteField.card (IntermediateField.adjoin (ZMod p) {x}) p
    have h2 : 2 ≤ p ^ (n : ℕ) := hF.1.two_le.trans (Nat.le_self_pow n.ne_zero p)
    have hcop : Nat.Coprime (Fintype.card (IntermediateField.adjoin (ZMod p) {x}) - 1) p := by
      rw [hn, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hF.1]
      intro hd
      have h3 : p ∣ p ^ (n : ℕ) := dvd_pow_self p n.ne_zero
      have h4 : p ∣ p ^ (n : ℕ) - (p ^ (n : ℕ) - 1) := Nat.dvd_sub h3 hd
      have h5 : p ^ (n : ℕ) - (p ^ (n : ℕ) - 1) = 1 := by omega
      rw [h5] at h4
      exact hF.1.ne_one (Nat.dvd_one.1 h4)
    have hcpos : 0 < Fintype.card (IntermediateField.adjoin (ZMod p) {x}) - 1 := by
      rw [hn]; omega
    have hxu : (Units.mk0 x hx0) ^ (Fintype.card (IntermediateField.adjoin (ZMod p) {x}) - 1) = 1 := by
      apply Units.ext
      simpa [a] using congrArg Subtype.val h1
    have := (weil_I_4_thm7_comm hF M hM (Units.mk0 x hx0)).2 ⟨_, hcpos, hcop, hxu⟩
    exact ⟨_, this, rfl⟩
  · rintro (rfl | ⟨μ, hμ, rfl⟩)
    · exact isAlgebraic_zero
    · refine ⟨Polynomial.X ^ (pq hF - 1) - 1, ?_, ?_⟩
      · have := Polynomial.X_pow_sub_C_ne_zero (R := ZMod p) hpos 1
        simpa using this
      · have := (subgroup_elem hF M hM ⟨μ, hμ⟩).1
        simp [this]

section Thm8Gen

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot]

/-- The data used to evaluate power series at a prime element: a field homomorphism `φ` from the coefficient
field whose image is a full set of representatives of `R / P`, and a prime element `π`. -/
structure Thm8Data (hF : IsPField F p) (G : Type*) [Field G] where
  /-- the embedding of the coefficient field -/
  φ : G →+* F
  /-- a prime element -/
  π : F
  hπ0 : π ≠ 0
  hπ : modK F π = ((pq hF : ℝ≥0) ^ 1)⁻¹
  hφ1 : ∀ g, modK F (φ g) ≤ 1
  hrep : ∀ x ∈ pR hF, ∃! a, a ∈ Set.range φ ∧ modK F (x - a) ≤ ((pq hF : ℝ≥0) ^ 1)⁻¹

namespace Thm8Data

variable {hF : IsPField F p} {G : Type*} [Field G] (D : Thm8Data hF G)

theorem modK_pi : modK F D.π = qi hF := by rw [D.hπ]; simp [qi]

/-- The terms of an evaluated power series are small. -/
theorem modK_term (g : G) (i : ℕ) : modK F (D.φ g * D.π ^ i) ≤ qi hF ^ i := by
  rw [modK_mul, modK_pow, D.modK_pi]
  calc modK F (D.φ g) * qi hF ^ i ≤ 1 * qi hF ^ i := mul_le_mul' (D.hφ1 g) le_rfl
    _ = qi hF ^ i := one_mul _

theorem tendsto_term (b : ℕ → G) : Tendsto (fun i => D.φ (b i) * D.π ^ i) atTop (𝓝 0) :=
  tendsto_zero_of_modK_le_pow (qi_lt_one hF) fun i => D.modK_term (b i) i

/-- Evaluation of a power series at `π`. -/
def ev (a : PowerSeries G) : F := ∑' i : ℕ, D.φ (PowerSeries.coeff i a) * D.π ^ i

theorem hasSum_ev (a : PowerSeries G) :
    HasSum (fun i : ℕ => D.φ (PowerSeries.coeff i a) * D.π ^ i) (D.ev a) :=
  (weil_I_4_cor1_thm6 hF (D.tendsto_term fun i => PowerSeries.coeff i a)).hasSum

theorem modK_ev_le (a : PowerSeries G) : modK F (D.ev a) ≤ 1 :=
  modK_le_of_hasSum (isUltrametricMod_of_isPField hF) (D.hasSum_ev a) fun i =>
    (D.modK_term _ i).trans (pow_le_one₀ zero_le (qi_lt_one hF).le)

/-- Partial sums of the evaluation. -/
def pe (n : ℕ) (a : PowerSeries G) : F :=
  ∑ i ∈ Finset.range n, D.φ (PowerSeries.coeff i a) * D.π ^ i

theorem tendsto_pe (a : PowerSeries G) : Tendsto (fun n => D.pe n a) atTop (𝓝 (D.ev a)) :=
  (D.hasSum_ev a).tendsto_sum_nat

theorem pe_eq_eval₂ (n : ℕ) (a : PowerSeries G) :
    D.pe n a = Polynomial.eval₂ D.φ D.π (PowerSeries.trunc n a) := by
  rw [PowerSeries.trunc_apply, Polynomial.eval₂_finsetSum, pe, Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval₂_monomial]

theorem modK_eval₂_small (n : ℕ) (Q : Polynomial G) (h : ∀ k < n, Q.coeff k = 0) :
    modK F (Polynomial.eval₂ D.φ D.π Q) ≤ qi hF ^ n := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine modK_sum_le hF _ _ fun k _ => ?_
  by_cases hk : k < n
  · rw [h k hk]; simp
  · exact (D.modK_term _ k).trans (pow_le_pow_of_le_one zero_le (qi_lt_one hF).le (not_lt.1 hk))

/-- The partial sums are multiplicative up to terms of order `q ^ (-n)`. -/
theorem pe_mul_sub (n : ℕ) (a b : PowerSeries G) :
    modK F (D.pe n a * D.pe n b - D.pe n (a * b)) ≤ qi hF ^ n := by
  rw [D.pe_eq_eval₂, D.pe_eq_eval₂, D.pe_eq_eval₂, ← PowerSeries.trunc_trunc_mul_trunc,
    ← Polynomial.eval₂_mul, ← Polynomial.eval₂_sub]
  refine D.modK_eval₂_small n _ fun k hk => ?_
  rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, ← Polynomial.coe_mul, Polynomial.coeff_coe]
  simp [hk]

theorem ev_mul (a b : PowerSeries G) : D.ev (a * b) = D.ev a * D.ev b := by
  have h1 := (D.tendsto_pe a).mul (D.tendsto_pe b)
  have h2 := D.tendsto_pe (a * b)
  have h3 : Tendsto (fun n => D.pe n a * D.pe n b - D.pe n (a * b)) atTop (𝓝 0) :=
    tendsto_zero_of_modK_le_pow (qi_lt_one hF) fun n => D.pe_mul_sub n a b
  have := tendsto_nhds_unique (h1.sub h2) h3
  exact (sub_eq_zero.1 this).symm

theorem ev_add (a b : PowerSeries G) : D.ev (a + b) = D.ev a + D.ev b := by
  have h := (D.hasSum_ev a).add (D.hasSum_ev b)
  have h2 := D.hasSum_ev (a + b)
  simp only [map_add, add_mul] at h2
  exact h2.unique h

theorem ev_one : D.ev 1 = 1 := by
  have h := D.hasSum_ev 1
  have h2 : HasSum (fun i : ℕ => D.φ (PowerSeries.coeff i (1 : PowerSeries G)) * D.π ^ i) 1 := by
    convert hasSum_single (f := fun i : ℕ => D.φ (PowerSeries.coeff i (1 : PowerSeries G)) * D.π ^ i) 0
      (fun i hi => by simp [PowerSeries.coeff_one, hi]) using 1
    simp
  exact h.unique h2

theorem ev_zero : D.ev 0 = 0 := by
  have h := D.hasSum_ev 0
  simp only [map_zero, zero_mul] at h
  exact h.unique hasSum_zero

theorem ev_X : D.ev PowerSeries.X = D.π := by
  have h := D.hasSum_ev PowerSeries.X
  have h2 : HasSum (fun i : ℕ => D.φ (PowerSeries.coeff i (PowerSeries.X : PowerSeries G)) * D.π ^ i) D.π := by
    convert hasSum_single (f := fun i : ℕ => D.φ (PowerSeries.coeff i (PowerSeries.X : PowerSeries G)) * D.π ^ i) 1
      (fun i hi => by simp [PowerSeries.coeff_X, hi]) using 1
    simp
  exact h.unique h2

/-- The evaluation as a ring homomorphism. -/
def evHom : PowerSeries G →+* F where
  toFun := D.ev
  map_one' := D.ev_one
  map_mul' := D.ev_mul
  map_zero' := D.ev_zero
  map_add' := D.ev_add

/-- Digit expansions (Cor. 2 of Thm. 6 with `n = 1`). -/
theorem digits (ν : ℤ) {x : F} (hx : modK F x ≤ ((pq hF : ℝ≥0) ^ ν)⁻¹) :
    ∃! a : ℕ → F, (∀ i, a i ∈ Set.range D.φ) ∧ HasSum (fun i : ℕ => a i * D.π ^ ((i : ℤ) + ν)) x :=
  weil_I_4_cor2_thm6 hF D.hπ0 le_rfl D.hπ (A := Set.range D.φ)
    (by rintro _ ⟨g, rfl⟩; exact mem_pR.2 (D.hφ1 g)) D.hrep ν (by simpa using hx)

theorem ev_injective : Function.Injective D.ev := by
  intro a b hab
  have key : ∀ c : PowerSeries G,
      HasSum (fun i : ℕ => D.φ (PowerSeries.coeff i c) * D.π ^ ((i : ℤ) + 0)) (D.ev c) := by
    intro c; simpa using D.hasSum_ev c
  have hx : modK F (D.ev a) ≤ ((pq hF : ℝ≥0) ^ (0 : ℤ))⁻¹ := by simpa using D.modK_ev_le a
  obtain ⟨s, -, hs⟩ := D.digits 0 hx
  have h1 := hs (fun i => D.φ (PowerSeries.coeff i a)) ⟨fun i => ⟨_, rfl⟩, key a⟩
  have h2 := hs (fun i => D.φ (PowerSeries.coeff i b)) ⟨fun i => ⟨_, rfl⟩, by rw [hab]; exact key b⟩
  ext i
  exact D.φ.injective (congrFun (h1.trans h2.symm) i)

/-- The evaluation of Laurent series at `π`, as a field homomorphism (the extension of `evHom` to the field of
fractions of the power series ring). -/
def lap : LaurentSeries G →+* F :=
  IsFractionRing.lift (A := PowerSeries G) (K := LaurentSeries G) (g := D.evHom) D.ev_injective

theorem lap_coe (a : PowerSeries G) : D.lap (a : LaurentSeries G) = D.ev a := by
  rw [← LaurentSeries.coe_algebraMap]
  exact IsFractionRing.lift_algebraMap (A := PowerSeries G) (K := LaurentSeries G) (g := D.evHom)
    D.ev_injective a

theorem lap_single (ν : ℤ) : D.lap (HahnSeries.single ν (1 : G)) = D.π ^ ν := by
  rw [RatFunc.single_zpow, map_zpow₀, ← PowerSeries.coe_X, D.lap_coe, D.ev_X]

/-- A Laurent series of valuation at most `exp (-N)` is evaluated to an element of module at most `q ^ (-N)`. -/
theorem modK_lap_le (N : ℤ) {s : LaurentSeries G} (hs : Valued.v s ≤ WithZero.exp (-N)) :
    modK F (D.lap s) ≤ ((pq hF : ℝ≥0) ^ N)⁻¹ := by
  by_cases h0 : s = 0
  · simp [h0]
  have hN : N ≤ s.order := by
    rw [HahnSeries.le_order_iff_forall h0]
    exact (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero G).1 hs
  have hform : D.lap s = D.π ^ s.order * D.ev s.powerSeriesPart := by
    conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
    rw [map_mul, D.lap_single, D.lap_coe]
  rw [hform, modK_mul, modK_zpow D.hπ0, D.modK_pi]
  calc qi hF ^ s.order * modK F (D.ev s.powerSeriesPart) ≤ qi hF ^ s.order * 1 :=
        mul_le_mul' le_rfl (D.modK_ev_le _)
    _ ≤ qi hF ^ N := by
        rw [mul_one]; exact zpow_le_zpow_right_of_le_one₀ (qi_pos hF) (qi_lt_one hF).le hN
    _ = ((pq hF : ℝ≥0) ^ N)⁻¹ := by simp [qi]

/-- Every element of module at most `q ^ (-N)` is the evaluation of a Laurent series of valuation at most
`exp (-N)` (this is the existence part of Cor. 2 of Thm. 6). -/
theorem exists_preimage (N : ℤ) {x : F} (hx : modK F x ≤ ((pq hF : ℝ≥0) ^ N)⁻¹) :
    ∃ s : LaurentSeries G, Valued.v s ≤ WithZero.exp (-N) ∧ D.lap s = x := by
  obtain ⟨a, ⟨haA, hsum⟩, -⟩ := D.digits N hx
  choose b hb using haA
  let ps : PowerSeries G := PowerSeries.mk b
  have h1 : HasSum (fun i : ℕ => D.φ (PowerSeries.coeff i ps) * D.π ^ i) (x * D.π ^ (-N)) := by
    convert hsum.mul_right (D.π ^ (-N)) using 2 with i
    rw [PowerSeries.coeff_mk, hb, mul_assoc, ← zpow_add₀ D.hπ0,
      show ((i : ℤ) + N + -N) = (i : ℤ) by ring, zpow_natCast]
  have h2 : D.ev ps = x * D.π ^ (-N) := (D.hasSum_ev ps).unique h1
  refine ⟨HahnSeries.single N 1 * (ps : LaurentSeries G), ?_, ?_⟩
  · rw [map_mul, LaurentSeries.valuation_single_zpow]
    calc WithZero.exp (-N) * Valued.v (ps : LaurentSeries G) ≤ WithZero.exp (-N) * 1 :=
          mul_le_mul' le_rfl ((LaurentSeries.val_le_one_iff_eq_coe G _).2 ⟨ps, rfl⟩)
      _ = WithZero.exp (-N) := mul_one _
  · rw [map_mul, D.lap_single, D.lap_coe, h2, mul_comm x, ← mul_assoc, ← zpow_add₀ D.hπ0,
      add_neg_cancel, zpow_zero, one_mul]

theorem lap_surjective : Function.Surjective D.lap := by
  intro x
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨n, hn⟩ := weil_I_4_thm6_range hF hx
  obtain ⟨s, -, hs⟩ := D.exists_preimage (-n) (x := x) (by rw [hn, zpow_neg, inv_inv])
  exact ⟨s, hs⟩

/-- The evaluation at `π` as a ring isomorphism. -/
def lapEquiv : LaurentSeries G ≃+* F :=
  RingEquiv.ofBijective D.lap ⟨D.lap.injective, D.lap_surjective⟩

/-- The set of Laurent series of valuation at most `exp (-N)` is a neighbourhood of zero. -/
theorem ball_mem_nhds (N : ℤ) :
    {s : LaurentSeries G | Valued.v s ≤ WithZero.exp (-N)} ∈ 𝓝 (0 : LaurentSeries G) := by
  let y : LaurentSeries G := HahnSeries.single N 1
  have hy : Valued.v y = WithZero.exp (-N) := LaurentSeries.valuation_single_zpow G N
  have hr : (Valued.v (R := LaurentSeries G)).restrict y ≠ 0 := by
    rw [Valuation.restrict_def, ne_eq, MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff]
    simp [hy]
  have hopen := Valued.isOpen_closedBall (LaurentSeries G) hr
  have heq : {x : LaurentSeries G | (Valued.v (R := LaurentSeries G)).restrict x ≤
      (Valued.v (R := LaurentSeries G)).restrict y} = {s | Valued.v s ≤ WithZero.exp (-N)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hy]
  rw [heq] at hopen
  refine hopen.mem_nhds ?_
  simp

/-- The sets of Laurent series of valuation at most `exp (-N)` form a neighbourhood basis of zero. -/
theorem exists_ball_subset {U : Set (LaurentSeries G)} (hU : U ∈ 𝓝 (0 : LaurentSeries G)) :
    ∃ N : ℤ, {s : LaurentSeries G | Valued.v s ≤ WithZero.exp (-N)} ⊆ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
  have he : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by
    intro h
    have := MonoidWithZeroHom.ValueGroup₀.embedding_injective (h.trans (map_zero _).symm)
    exact γ.ne_zero this
  refine ⟨1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1), fun s hs => hγ ?_⟩
  show (Valued.v (R := LaurentSeries G)).restrict s < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hs ?_
  conv_rhs => rw [← WithZero.exp_log he]
  rw [WithZero.exp_lt_exp]
  omega

theorem continuous_lap : Continuous D.lap := by
  refine continuous_of_continuousAt_zero D.lap.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  rw [hasBasis_nhds_zero_modK.tendsto_right_iff]
  intro m hm
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hm (qi_lt_one hF)
  filter_upwards [ball_mem_nhds (G := G) (k : ℤ)] with s hs
  refine (D.modK_lap_le (k : ℤ) hs).trans ?_
  have : ((pq hF : ℝ≥0) ^ (k : ℤ))⁻¹ = qi hF ^ k := by simp [qi]
  rw [this]
  exact hk.le

theorem continuous_lapEquiv_symm : Continuous D.lapEquiv.symm := by
  refine continuous_of_continuousAt_zero D.lapEquiv.symm.toRingHom.toAddMonoidHom ?_
  intro U hU
  obtain ⟨N, hN⟩ := exists_ball_subset (G := G) (by simpa using hU)
  have hpos : (0 : ℝ≥0) < ((pq hF : ℝ≥0) ^ N)⁻¹ := by
    have : 0 < (pq hF : ℝ≥0) := by exact_mod_cast (zero_lt_one.trans (one_lt_pq_nat hF))
    positivity
  have hnhds := (hasBasis_nhds_zero_modK (K := F)).mem_of_mem hpos
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hnhds fun x hx => ?_
  obtain ⟨s, hs, hsx⟩ := D.exists_preimage N hx
  have : D.lapEquiv.symm x = s := by
    rw [RingEquiv.symm_apply_eq]; exact hsx.symm
  show D.lapEquiv.symm x ∈ U
  rw [this]
  exact hN hs

end Thm8Data

/-- The number of elements of the subfield `M ∪ {0}` is `q`. -/
theorem natCard_subfield_M (hF : IsPField F p)
    (M : Subgroup Fˣ) (hM : Nat.card M = pq hF - 1) (L : Subfield F)
    (hL : (L : Set F) = {x | x = 0 ∨ ∃ μ ∈ M, x = ((μ : Fˣ) : F)}) :
    Finite L ∧ Nat.card L = pq hF := by
  have hpos : 0 < pq hF - 1 := by have := one_lt_pq_nat hF; omega
  have hMfin : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; omega)
  have hset : (L : Set F) = insert 0 ((fun μ : Fˣ => (μ : F)) '' (M : Set Fˣ)) := by
    rw [hL]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro (h | ⟨μ, hμ, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨μ, hμ, h.symm⟩
    · rintro (h | ⟨μ, hμ, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨μ, hμ, h.symm⟩
  have hinj : Function.Injective (fun μ : Fˣ => (μ : F)) := Units.val_injective
  have hfinM : (M : Set Fˣ).Finite := Set.toFinite _
  have h0 : (0 : F) ∉ (fun μ : Fˣ => (μ : F)) '' (M : Set Fˣ) := by
    rintro ⟨μ, -, h⟩
    exact μ.ne_zero h
  have hfin : (L : Set F).Finite := by
    rw [hset]; exact (hfinM.image _).insert 0
  refine ⟨hfin.to_subtype, ?_⟩
  have h1 : Nat.card L = (L : Set F).ncard := Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_insert_of_notMem h0 ((hfinM.image _)), Set.ncard_image_of_injective _ hinj,
    ← Nat.card_coe_set_eq]
  have : Nat.card ((M : Set Fˣ)) = Nat.card M := rfl
  rw [this, hM]
  have := one_lt_pq_nat hF
  omega

end Thm8Gen

/-- Thm. 8: a commutative $p$-field of characteristic $p$, with $q=p^f$, is isomorphic as a topological field to
$\mathbb F_q((T))$. -/
@[kb "weil1973bnt" "Ch. I, §4, Thm. 8"]
theorem weil_I_4_thm8 {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] (hF : IsPField F p) [CharP F p] {f : ℕ}
    (hf : pq hF = p ^ f) :
    haveI : Fact p.Prime := ⟨hF.1⟩
    ∃ e : F ≃+* LaurentSeries (GaloisField p f), Continuous e ∧ Continuous e.symm := by
  classical
  have : Fact p.Prime := ⟨hF.1⟩
  obtain ⟨M, hM⟩ := weil_I_4_thm7_exists hF
  obtain ⟨L, hL⟩ := weil_I_4_cor1_thm7 hF M hM
  obtain ⟨hLfin, hLcard⟩ := natCard_subfield_M hF M hM L hL
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := one_lt_pq_nat hF
    rw [hf] at this
    simp at this
  let _ : Fintype L := Fintype.ofFinite L
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p f) = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GaloisField.card p f hf0, hLcard, hf]
  let e0 : GaloisField p f ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let φ : GaloisField p f →+* F := L.subtype.comp (e0 : GaloisField p f →+* L)
  have hrange : Set.range φ = {x | x = 0 ∨ ∃ μ ∈ M, x = ((μ : Fˣ) : F)} := by
    rw [← hL]
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (e0 g).2
    · intro hx
      exact ⟨e0.symm ⟨x, hx⟩, by simp [φ]⟩
  obtain ⟨π, hπ0, hπ1, hmax⟩ := exists_gen hF
  have hP := pP_eq_left (hK := hF) hπ0 hπ1 hmax
  have hmπ := weil_I_4_thm6_modK_prime hF hπ0 hP
  obtain ⟨hMR, hrepr⟩ := weil_I_4_thm7_repr hF M hM
  let D : Thm8Data hF (GaloisField p f) :=
    { φ := φ
      π := π
      hπ0 := hπ0
      hπ := by rw [pow_one]; exact hmπ
      hφ1 := by
        intro g
        have : φ g ∈ Set.range φ := ⟨g, rfl⟩
        rw [hrange] at this
        rcases this with h | ⟨μ, hμ, h⟩
        · rw [h]; simp
        · rw [h]; exact mem_pR.1 (hMR μ hμ)
      hrep := by
        intro x hx
        obtain ⟨m, ⟨hm1, hm2⟩, huniq⟩ := hrepr x hx
        have hle : ∀ y : F, y ∈ pP hF → modK F y ≤ ((pq hF : ℝ≥0) ^ 1)⁻¹ := by
          intro y hy
          rw [pow_one]
          exact modK_le_qi_of_lt_one hF hy
        have hle' : ∀ y : F, modK F y ≤ ((pq hF : ℝ≥0) ^ 1)⁻¹ → y ∈ pP hF := by
          intro y hy
          refine lt_of_le_of_lt hy ?_
          have := qi_lt_one hF
          simpa [qi] using this
        refine ⟨m, ⟨by rw [hrange]; exact hm1, hle _ hm2⟩, fun a ⟨ha1, ha2⟩ => ?_⟩
        rw [hrange] at ha1
        exact huniq a ⟨ha1, hle' _ ha2⟩ }
  exact ⟨D.lapEquiv.symm, D.continuous_lapEquiv_symm, by
    rw [RingEquiv.symm_symm]; exact D.continuous_lap⟩

section Prop6

variable {K₀ : Type*} [Field K₀] [TopologicalSpace K₀] [IsTopologicalDivisionRing K₀]
    [LocallyCompactSpace K₀] [T2Space K₀] [(𝓝[≠] (0 : K₀)).NeBot] [Algebra K₀ K] [FiniteDimensional K₀ K]
    [ContinuousSMul K₀ K]

/-- A root of a monic polynomial with coefficients in `R₀` lies in `R` (the module of the leading term of a
monic polynomial dominates the other terms if the module of the root exceeds one). -/
theorem prop6_mem_of_monic (hK : IsPField K p) (hK₀ : IsPField K₀ p) (x : K) (P : Polynomial K₀)
    (hP : P.Monic) (hc : ∀ i, P.coeff i ∈ pR hK₀) (hx : Polynomial.aeval x P = 0) : x ∈ pR hK := by
  by_contra hxR
  have hx1 : 1 < modK K x := lt_of_not_ge (fun h => hxR (mem_pR.2 h))
  have hn : 0 < P.natDegree := by
    by_contra h0
    have h1 : P = 1 := (Polynomial.Monic.natDegree_eq_zero hP).1 (by omega)
    rw [h1] at hx
    simp at hx
  obtain ⟨n, hn'⟩ : ∃ n, P.natDegree = n + 1 := ⟨P.natDegree - 1, by omega⟩
  rw [Polynomial.aeval_eq_sum_range, hn', Finset.sum_range_succ] at hx
  have hlead : P.coeff (n + 1) = 1 := by
    have := hP.coeff_natDegree
    rwa [hn'] at this
  rw [hlead, one_smul] at hx
  have hxn : x ^ (n + 1) = -∑ i ∈ Finset.range (n + 1), P.coeff i • x ^ i :=
    eq_neg_of_add_eq_zero_right hx
  have hs : modK K (∑ i ∈ Finset.range (n + 1), P.coeff i • x ^ i) ≤ modK K x ^ n := by
    refine modK_sum_le hK _ _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Algebra.smul_def, modK_mul, modK_pow, modK_algebraMap]
    calc modK K₀ (P.coeff i) ^ Module.finrank K₀ K * modK K x ^ i
        ≤ 1 * modK K x ^ n := by
          refine mul_le_mul' (pow_le_one₀ zero_le (mem_pR.1 (hc i))) ?_
          exact pow_le_pow_right₀ hx1.le (by omega)
      _ = modK K x ^ n := one_mul _
  have h2 : modK K (x ^ (n + 1)) ≤ modK K x ^ n := by
    rw [hxn, modK_neg]; exact hs
  rw [modK_pow] at h2
  have h3 : modK K x ^ n < modK K x ^ (n + 1) := pow_lt_pow_right₀ hx1 (by omega)
  exact absurd h2 (not_le.2 h3)

/-- The maximal compact subring `R` of `K` as a module over the maximal compact subring `R₀` of `K₀`. -/
def pRSub (hK : IsPField K p) (hK₀ : IsPField K₀ p) : Submodule (pR hK₀) K where
  carrier := pR hK
  add_mem' := (pR hK).add_mem
  zero_mem' := (pR hK).zero_mem
  smul_mem' := fun r y hy => by
    show modK K ((r : K₀) • y) ≤ 1
    rw [Algebra.smul_def, modK_mul, modK_algebraMap]
    exact mul_le_one' (pow_le_one₀ zero_le (mem_pR.1 r.2)) (mem_pR.1 hy)

/-- `R` is a finitely generated `R₀`-module: a finite set of representatives of `R` modulo `cR` (for a
nonzero `c` in `P₀`) generates `R` over `R₀`, because the module they generate is compact, hence closed, and
dense in `R`. -/
theorem prop6_fg (hK : IsPField K p) (hK₀ : IsPField K₀ p) : (pRSub hK hK₀).FG := by
  classical
  obtain ⟨π₀, hπ0, hπ1, -⟩ := exists_gen hK₀
  have hd : Module.finrank K₀ K ≠ 0 := Module.finrank_pos.ne'
  set c : K := algebraMap K₀ K π₀ with hc
  have hc0 : c ≠ 0 := by simpa [c] using hπ0
  have hcm : modK K c < 1 := by
    rw [hc, modK_algebraMap]; exact pow_lt_one₀ zero_le hπ1 hd
  have hπR : π₀ ∈ pR hK₀ := mem_pR.2 hπ1.le
  have hopen : IsOpen ((fun r => c * r) '' (pR hK : Set K)) :=
    (Homeomorph.mulLeft₀ c hc0).isOpenMap _ (weil_I_4_thm6_isOpen hK).1
  have hnhds : ∀ s ∈ (pR hK : Set K),
      (fun y => s + y) '' ((fun r => c * r) '' (pR hK : Set K)) ∈ 𝓝 s := by
    intro s _
    refine IsOpen.mem_nhds ((Homeomorph.addLeft s).isOpenMap _ hopen)
      ⟨0, ⟨0, (pR hK).zero_mem, by simp⟩, by simp⟩
  obtain ⟨t, htR, hcov⟩ := (weil_I_4_thm6_isCompact hK).elim_nhds_subcover _ hnhds
  let N : Submodule (pR hK₀) K := Submodule.span (pR hK₀) (t : Set K)
  have hcs : ∀ m : ℕ, ∀ s ∈ t, c ^ m * s ∈ N := by
    intro m s hs
    have h1 : (⟨π₀ ^ m, (pR hK₀).pow_mem hπR m⟩ : pR hK₀) • s ∈ N :=
      N.smul_mem _ (Submodule.subset_span hs)
    have h2 : (⟨π₀ ^ m, (pR hK₀).pow_mem hπR m⟩ : pR hK₀) • s = c ^ m * s := by
      show (π₀ ^ m) • s = _
      rw [Algebra.smul_def, map_pow]
    rwa [h2] at h1
  have hstep : ∀ r ∈ pR hK, ∃ s ∈ t, ∃ r' ∈ pR hK, r = s + c * r' := by
    intro r hr
    have := hcov hr
    simp only [Set.mem_iUnion] at this
    obtain ⟨s, hs, y, ⟨r', hr', rfl⟩, hy⟩ := this
    exact ⟨s, hs, r', hr', hy.symm⟩
  have hclaim : ∀ m : ℕ, ∀ y ∈ pR hK, ∃ n ∈ N, ∃ r ∈ pR hK, y = n + c ^ m * r := by
    intro m
    induction m with
    | zero => intro y hy; exact ⟨0, N.zero_mem, y, hy, by simp⟩
    | succ m ih =>
      intro y hy
      obtain ⟨n, hn, r, hr, rfl⟩ := ih y hy
      obtain ⟨s, hs, r', hr', rfl⟩ := hstep r hr
      refine ⟨n + c ^ m * s, N.add_mem hn (hcs m s hs), r', hr', ?_⟩
      simp only [mul_add, pow_succ, mul_assoc, add_assoc]
  -- N is compact, hence closed
  have hcompactR : CompactSpace (pR hK₀) :=
    isCompact_iff_compactSpace.1 (weil_I_4_thm6_isCompact hK₀)
  let g : (t → pR hK₀) → K := fun f => ∑ a : t, ((f a : pR hK₀) : K₀) • (a : K)
  have hg : Continuous g := continuous_finsetSum _ fun a _ =>
    ((continuous_subtype_val.comp (continuous_apply a))).smul continuous_const
  have hNrange : (N : Set K) = Set.range g := by
    ext x
    simp only [SetLike.mem_coe, N, Submodule.mem_span_finset', Set.mem_range, g]
    rfl
  have hNclosed : IsClosed (N : Set K) := by
    rw [hNrange]; exact (isCompact_range hg).isClosed
  refine ⟨t, le_antisymm (Submodule.span_le.2 fun s hs => htR s hs) fun x hx => ?_⟩
  choose n hn r hr hxn using fun m => hclaim m x hx
  have htend : Tendsto (fun m : ℕ => x - n m) atTop (𝓝 0) := by
    refine tendsto_zero_of_modK_le_pow hcm fun m => ?_
    have : x - n m = c ^ m * r m := by rw [sub_eq_iff_eq_add']; exact hxn m
    rw [this, modK_mul, modK_pow]
    exact mul_le_of_le_one_right zero_le (mem_pR.1 (hr m))
  have htend2 : Tendsto n atTop (𝓝 x) := by
    have := (tendsto_const_nhds (x := x)).sub htend
    simpa using this
  exact hNclosed.mem_of_tendsto htend2 (Eventually.of_forall hn)

end Prop6

open scoped IsMulCommutative in
/-- Prop. 6: $K_0$ a $p$-field, $K$ a $p$-field which is an algebra over $K_0$ ($K_0$ in the center of $K$):
$x\in R$ iff $x$ is a root of a monic polynomial with coefficients in $R_0$. -/
@[kb "weil1973bnt" "Ch. I, §4, Prop. 6 and text p. 23"]
theorem weil_I_4_prop6 {K₀ : Type*} [Field K₀] [TopologicalSpace K₀] [IsTopologicalDivisionRing K₀]
    [LocallyCompactSpace K₀] [T2Space K₀] [(𝓝[≠] (0 : K₀)).NeBot] [Algebra K₀ K] [FiniteDimensional K₀ K]
    [ContinuousSMul K₀ K] (hK₀ : IsPField K₀ p) (hK : IsPField K p) (x : K) :
    x ∈ pR hK ↔ ∃ P : Polynomial K₀, P.Monic ∧ (∀ i, P.coeff i ∈ pR hK₀) ∧ Polynomial.aeval x P = 0 := by
  constructor
  · intro hx
    have hint : IsIntegral (pR hK₀) x := by
      let B : Subalgebra (pR hK₀) K := Algebra.adjoin (pR hK₀) ({x} : Set K)
      have hB : IsMulCommutative B := inferInstance
      let _ : CommRing B := inferInstance
      have hxB : x ∈ B := Algebra.self_mem_adjoin_singleton _ x
      have hBint : IsIntegral (pR hK₀) (⟨x, hxB⟩ : B) := by
        refine isIntegral_of_smul_mem_submodule (A := B) (pRSub hK hK₀) ?_ (prop6_fg hK hK₀) _ ?_
        · intro h
          have h1 : (1 : K) ∈ pRSub hK hK₀ := (pR hK).one_mem
          rw [h] at h1
          simp at h1
        · intro n hn
          show (x : K) * n ∈ pRSub hK hK₀
          exact (pR hK).mul_mem hx hn
      exact hBint.map B.val
    obtain ⟨P, hPm, hP⟩ := hint
    refine ⟨P.map (algebraMap (pR hK₀) K₀), hPm.map _, fun i => ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (P.coeff i).2
    · rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]; exact hP
  · rintro ⟨P, hP, hc, hx⟩
    exact prop6_mem_of_monic hK hK₀ x P hP hc hx

end NumberFieldKB.WeilBNT.FieldModule
