import Mathlib

/-!
# Frobenius elements: powers, uniqueness, order
Abstract commutative-algebra layer on Mathlib's `IsArithFrobAt` / `arithFrobAt`
(`Mathlib/RingTheory/Frobenius.lean`) and the Hilbert theory of `Mathlib/NumberTheory/RamificationInertia/`.

Setting: `A → C` a finite flat extension of domains, `G` a finite group with `IsGaloisGroup G A C`,
`p` a maximal ideal of `A`, `P` a maximal ideal of `C` over `p`, `p` unramified in `C`
(`p.ramificationIdxIn C = 1`).

* `frobPow_congr`: if `σ • x ≡ x ^ n (mod P)` and `σ` fixes `P`, then `σ ^ k • x ≡ x ^ (n ^ k)`.
* `inertia_eq_bot`: unramified implies the inertia group `P.inertia G` is trivial.
* `eq_of_congr_pow`: an element of `G` is determined by its congruence `σ • x ≡ x ^ n (mod P)`
  when the inertia group is trivial.
* **`orderOf_arithFrobAt`**: the order of `Frob_P` equals the residue degree `P.inertiaDeg A`.
* **`arithFrobAt_eq_one_iff`**: `Frob_P = 1` iff the residue degree of `P` over `p` is `1`.
-/

set_option linter.unusedSectionVars false

open Ideal Pointwise

namespace NumberFieldKB.Chebotarev

section Congruence

variable {C G : Type*} [CommRing C] [Group G] [MulSemiringAction G C]

/-- Powers of a Frobenius-type congruence: if `σ` fixes `P` and `σ • x ≡ x ^ n (mod P)` for all `x`,
then `σ ^ k • x ≡ x ^ (n ^ k) (mod P)` for all `x`. -/
theorem frobPow_congr {σ : G} {P : Ideal C} (hσ : σ • P = P) {n : ℕ}
    (h : ∀ x : C, σ • x - x ^ n ∈ P) (k : ℕ) (x : C) : (σ ^ k) • x - x ^ (n ^ k) ∈ P := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, pow_succ', pow_mul]
    have h1 : σ • ((σ ^ k) • x) - σ • (x ^ (n ^ k)) ∈ P := by
      rw [← smul_sub]
      have := smul_mem_pointwise_smul σ _ P (ih x)
      rwa [hσ] at this
    have h2 : (σ • x) ^ (n ^ k) - (x ^ n) ^ (n ^ k) ∈ P := by
      rw [← Ideal.Quotient.eq, map_pow, map_pow, Ideal.Quotient.eq.mpr (h x)]
    rw [smul_pow'] at h1
    have := add_mem h1 h2
    simpa using this

end Congruence

section Unramified

variable {A C G : Type*} [CommRing A] [CommRing C] [IsDomain A] [IsDomain C] [Algebra A C]
  [Module.Finite A C] [Module.Flat A C] [Group G] [Finite G] [MulSemiringAction G C]
  [IsGaloisGroup G A C]

/-- If `p` is unramified in `C` (`e = 1`), the inertia group of every prime `P` over `p` is trivial. -/
theorem inertia_eq_bot (p : Ideal A) [p.IsPrime] (P : Ideal C) [P.IsPrime] [P.LiesOver p]
    [Algebra.HasSeparableResidueFieldsAt A C p] (he : p.ramificationIdxIn C = 1) :
    P.inertia G = ⊥ := by
  have h := Ideal.card_inertia_eq_ramificationIdxIn (G := G) p P
  rw [he] at h
  exact Subgroup.eq_bot_of_card_eq _ h

/-- With trivial inertia, an element `σ : G` is determined by a congruence `σ • x ≡ x ^ n (mod P)`. -/
theorem eq_of_congr_pow {P : Ideal C} (hb : P.inertia G = ⊥) {σ τ : G} {n : ℕ}
    (hσ : ∀ x : C, σ • x - x ^ n ∈ P) (hτ : ∀ x : C, τ • x - x ^ n ∈ P) : σ = τ := by
  have : σ * τ⁻¹ ∈ P.inertia G := by
    intro x
    simpa [mul_smul] using sub_mem (hσ (τ⁻¹ • x)) (hτ (τ⁻¹ • x))
  rw [hb, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact this

section Order

variable (p : Ideal A) [p.IsMaximal] (P : Ideal C) [P.IsMaximal] [P.LiesOver p]
  [Algebra.HasSeparableResidueFieldsAt A C p]

attribute [local instance] Ideal.Quotient.field

/-- For a Frobenius `σ` at `P` in a group with trivial inertia, `σ ^ n = 1` iff every `x` satisfies
`x ^ (q ^ n) ≡ x (mod P)` where `q = #(A/p)`. -/
theorem pow_eq_one_iff_of_isArithFrobAt (hb : P.inertia G = ⊥) {σ : G}
    (hσ : IsArithFrobAt A σ P) (n : ℕ) :
    σ ^ n = 1 ↔ ∀ x : C, x ^ (Nat.card (A ⧸ P.under A) ^ n) - x ∈ P := by
  have hst : σ • P = P := by
    have := hσ.mem_stabilizer
    rwa [MulAction.mem_stabilizer_iff] at this
  have key := frobPow_congr hst (n := Nat.card (A ⧸ P.under A)) hσ n
  constructor
  · intro h x
    have := key x
    rw [h, one_smul] at this
    simpa using neg_mem this
  · intro h
    have : σ ^ n ∈ P.inertia G := by
      intro x
      simpa using add_mem (key x) (h x)
    rwa [hb, Subgroup.mem_bot] at this

/-- **The order of the Frobenius element is the residue degree.**
If `p` is unramified in `C` and `P` is a prime over `p` with finite residue field, then
`orderOf (arithFrobAt A G P) = P.inertiaDeg A = [C/P : A/p]`. -/
theorem orderOf_arithFrobAt [Finite (C ⧸ P)] (he : p.ramificationIdxIn C = 1) :
    orderOf (arithFrobAt A G P) = P.inertiaDeg A := by
  have hb := inertia_eq_bot (G := G) p P he
  have hF := IsArithFrobAt.arithFrobAt A G P
  have hunder : P.under A = p := (Ideal.over_def P p).symm
  have hfin : Finite (A ⧸ p) :=
    Finite.of_injective (Ideal.quotientMap P (algebraMap A C) hunder.symm.le)
      (Ideal.quotientMap_injective' hunder.le)
  have : Fintype (A ⧸ p) := Fintype.ofFinite _
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P, ← FiniteField.orderOf_frobeniusAlgHom (A ⧸ p) (C ⧸ P)]
  refine orderOf_eq_orderOf_iff.mpr fun n => ?_
  rw [pow_eq_one_iff_of_isArithFrobAt P hb hF n, hunder, Nat.card_eq_fintype_card]
  rw [DFunLike.ext_iff]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := h x
    simp [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]
    rw [← map_pow]
    exact Ideal.Quotient.eq.mpr this
  · intro h x
    have := h (Ideal.Quotient.mk P x)
    simp [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate] at this
    rw [← map_pow] at this
    exact Ideal.Quotient.eq.mp this

/-- `Frob_P = 1` iff the residue degree of `P` over `p` is `1`. -/
theorem arithFrobAt_eq_one_iff [Finite (C ⧸ P)] (he : p.ramificationIdxIn C = 1) :
    arithFrobAt A G P = 1 ↔ P.inertiaDeg A = 1 := by
  rw [← orderOf_arithFrobAt (G := G) p P he, orderOf_eq_one_iff]

/-- **Splitting via Frobenius.** An unramified prime `p` splits completely in the Galois extension
(the number of primes of `C` over `p` is `#G`) iff `Frob_P = 1` for one (equivalently every) `P | p`. -/
theorem arithFrobAt_eq_one_iff_ncard_primesOver [Finite (C ⧸ P)] (he : p.ramificationIdxIn C = 1) :
    arithFrobAt A G P = 1 ↔ (p.primesOver C).ncard = Nat.card G := by
  rw [arithFrobAt_eq_one_iff (G := G) p P he]
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (G := G) p C
  rw [he, one_mul, Ideal.inertiaDegIn_eq_inertiaDeg p P G] at h
  have hpos : 0 < P.inertiaDeg A := Ideal.inertiaDeg_pos P A
  constructor
  · intro h1
    rw [h1, mul_one] at h
    exact h
  · intro h2
    have hG : 0 < Nat.card G := Nat.card_pos
    rw [← h2] at h hG
    exact Nat.eq_of_mul_eq_mul_left hG (by rw [h, mul_one])

end Order

section Tower

variable {A C G : Type*} [CommRing A] [CommRing C] [IsDomain A] [IsDomain C] [Algebra A C]
  [Module.Finite A C] [Module.Flat A C] [Group G] [Finite G] [MulSemiringAction G C]
  [IsGaloisGroup G A C]
  {B : Type*} [CommRing B] [Algebra A B] [Algebra B C] [IsScalarTower A B C]
  {H : Type*} [Group H] [Finite H] [MulSemiringAction H C] [IsGaloisGroup H B C]
  (ι : H →* G) (hι : ∀ (h : H) (x : C), ι h • x = h • x)

/-- The pullback of a prime with finite residue field along any ring map has finite residue field. -/
theorem finite_quotient_under {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [Finite (S ⧸ P)] : Finite (R ⧸ P.under R) :=
  Finite.of_injective (Ideal.quotientMap P (algebraMap R S) le_rfl) Ideal.quotientMap_injective

theorem isMaximal_under_of_finite {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)] : (P.under R).IsMaximal := by
  have : Finite (R ⧸ P.under R) := finite_quotient_under P
  have : (P.under R).IsPrime := inferInstance
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

/-- Residue field cardinalities: `#(B/Q) = #(A/p) ^ f(Q|p)`. -/
theorem natCard_quotient_eq_pow {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (Q : Ideal B) [Q.LiesOver p] [p.IsMaximal] [Q.IsMaximal] [Finite (B ⧸ Q)] :
    Nat.card (B ⧸ Q) = Nat.card (A ⧸ p) ^ Q.inertiaDeg A := by
  let _ : Field (A ⧸ p) := Ideal.Quotient.field p
  let _ : Field (B ⧸ Q) := Ideal.Quotient.field Q
  rw [Ideal.inertiaDeg_eq_of_isMaximal p Q]
  exact Module.natCard_eq_pow_finrank

include hι in
/-- **Frobenius in a tower, subgroup form** (Milne ANT Prop. 8.13(b)).
Let `A → B → C` with `G` acting on `C` (Galois over `A`) and a group `H` acting on `C`
(Galois over `B`), mapped to `G` by `ι` compatibly with the actions (e.g. `Gal(L/E) → Gal(L/K)`). If `P` is a prime of `C` with finite residue field, unramified over `A`, then
`Frob_P(C/B) = Frob_P(C/A) ^ f` where `f = f(P ∩ B | P ∩ A)` is the residue degree of `P ∩ B`
over `A`. In particular, if `P ∩ B` has degree `1` over `P ∩ A` the two Frobenius elements agree. -/
theorem arithFrobAt_subgroup_eq_pow (P : Ideal C) [P.IsPrime] [Finite (C ⧸ P)]
    [Algebra.HasSeparableResidueFieldsAt A C (P.under A)]
    (he : (P.under A).ramificationIdxIn C = 1) :
    ι (arithFrobAt B H P) = arithFrobAt A G P ^ (P.under B).inertiaDeg A := by
  have hpm : (P.under A).IsMaximal := isMaximal_under_of_finite P
  have hQ : (P.under B).IsMaximal := isMaximal_under_of_finite P
  have hb := inertia_eq_bot (G := G) (P.under A) P he
  have hσ := IsArithFrobAt.arithFrobAt A G P
  have hτ := IsArithFrobAt.arithFrobAt B H P
  have hst : arithFrobAt A G P • P = P := by
    have := hσ.mem_stabilizer
    rwa [MulAction.mem_stabilizer_iff] at this
  have hcard : Nat.card (B ⧸ P.under B) =
      Nat.card (A ⧸ P.under A) ^ (P.under B).inertiaDeg A := by
    have hfin : Finite (B ⧸ P.under B) := finite_quotient_under P
    have hu : (P.under B).under A = P.under A := Ideal.under_under _
    have hpm' : ((P.under B).under A).IsMaximal := hu ▸ hpm
    have := natCard_quotient_eq_pow ((P.under B).under A) (P.under B)
    rwa [hu] at this
  refine eq_of_congr_pow hb (n := Nat.card (B ⧸ P.under B)) ?_ ?_
  · intro x
    rw [hι]
    exact hτ x
  · intro x
    rw [hcard]
    exact frobPow_congr hst hσ _ x

section Quotient

variable {A B C G G' : Type*} [CommRing A] [CommRing B] [CommRing C] [IsDomain A] [IsDomain B]
  [IsDomain C] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [Module.Finite A B] [Module.Flat A B] [Module.Finite A C] [Module.Flat A C]
  [Group G] [Finite G] [MulSemiringAction G C] [IsGaloisGroup G A C]
  [Group G'] [Finite G'] [MulSemiringAction G' B] [IsGaloisGroup G' A B]

/-- **Frobenius under restriction to a Galois subextension** (Milne ANT Prop. 8.13(a)).
`G` acts on `C` and `G'` on `B ⊆ C`, both Galois over `A`, and `π : G →* G'` is compatible with the
inclusion `B → C` (the restriction map). If `P` is a prime of `C` with finite residue field, unramified
over `A`, and `Q = P ∩ B` is unramified over `A` (automatic, see the number field statement), then
`π (Frob_P) = Frob_Q`. -/
theorem map_arithFrobAt_eq (π : G →* G')
    (hπ : ∀ (g : G) (b : B), algebraMap B C (π g • b) = g • algebraMap B C b)
    (P : Ideal C) [P.IsPrime] [Finite (C ⧸ P)] [Finite (B ⧸ P.under B)]
    [Algebra.HasSeparableResidueFieldsAt A B ((P.under B).under A)]
    (he' : ((P.under B).under A).ramificationIdxIn B = 1) :
    π (arithFrobAt A G P) = arithFrobAt A G' (P.under B) := by
  have hQ : (P.under B).IsPrime := inferInstance
  have hpm : ((P.under B).under A).IsMaximal := isMaximal_under_of_finite (P.under B)
  have hb := inertia_eq_bot (G := G') ((P.under B).under A) (P.under B) he'
  have hσ := IsArithFrobAt.arithFrobAt A G P
  have hτ := IsArithFrobAt.arithFrobAt A G' (P.under B)
  have hu : (P.under B).under A = P.under A := Ideal.under_under _
  refine eq_of_congr_pow hb (n := Nat.card (A ⧸ P.under A)) ?_ ?_
  · intro b
    have h1 := hσ (algebraMap B C b)
    show algebraMap B C _ ∈ P
    rw [map_sub, map_pow, hπ]
    exact h1
  · intro b
    have := hτ b
    rwa [hu] at this

end Quotient

end Tower

end Unramified

end NumberFieldKB.Chebotarev
