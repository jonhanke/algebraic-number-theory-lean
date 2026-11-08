import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Theorems 3.31 and 3.32: modules over a Dedekind domain

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), pp. 57–58; bib key `milne2020ant`. Milne gives
only a sketch and refers to Curtis–Reiner, Fröhlich–Taylor and Narkiewicz.

The structure theorem (3.31) and the invariant factor theorem (3.32) are stated here as **named statements**
(`Prop`-valued structures, never axioms): `TorsionFreeModuleStructure A` and `InvariantFactorTheorem A`. What is
proved unconditionally:

* `thm_3_31_rank_one` (the "moreover" of Theorem 3.31): two fractional ideals are isomorphic as $A$-modules iff they
  have the same ideal class.

The named statement `InvariantFactorTheorem A K` (Theorem 3.32) is **proved** for every Dedekind domain in
`Ch3InvariantFactors.lean` (`InvariantFactors.invariantFactorTheorem`).

A fractional ideal $\mathfrak a$ (Milne: a nonzero finitely generated $A$-submodule of $K$) is a unit of
`FractionalIdeal (nonZeroDivisors A) K`, viewed as the $A$-submodule `(a : Submodule A K)` of $K$. "Torsion-free" is
Mathlib's `NoZeroSMulDivisors A M`.
-/

open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT

universe u

/-- **Theorem 3.31** (named statement), over a Dedekind domain $A$ with field of fractions $K$:

(a) every finitely generated torsion-free $A$-module $M$ is isomorphic to a direct sum
$\mathfrak a_1 \oplus \dots \oplus \mathfrak a_m$ of fractional ideals;

(b) $\mathfrak a_1 \oplus \dots \oplus \mathfrak a_m \cong \mathfrak b_1 \oplus \dots \oplus \mathfrak b_n$ iff
$m = n$ and $\mathfrak a_1 \cdots \mathfrak a_m \equiv \mathfrak b_1 \cdots \mathfrak b_n$ modulo principal ideals
(i.e. the products have the same class in $\mathrm{Cl}(A)$). -/
@[kb "milne2020ant" "v3.08, Thm. 3.31, pp. 57–58"]
structure TorsionFreeModuleStructure (A : Type u) [CommRing A] [IsDedekindDomain A] (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K] : Prop where
  /-- (a): a finitely generated torsion-free module is a direct sum of fractional ideals. -/
  decomposition : ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M],
    ∃ (m : ℕ) (a : Fin m → (FractionalIdeal A⁰ K)ˣ),
      Nonempty (M ≃ₗ[A] ∀ i, ((a i : FractionalIdeal A⁰ K) : Submodule A K))
  /-- (b): classification of direct sums of fractional ideals by the number of summands and the class of the
  product. -/
  iso_iff : ∀ (m n : ℕ) (a : Fin m → (FractionalIdeal A⁰ K)ˣ) (b : Fin n → (FractionalIdeal A⁰ K)ˣ),
    Nonempty ((∀ i, ((a i : FractionalIdeal A⁰ K) : Submodule A K)) ≃ₗ[A]
        ∀ j, ((b j : FractionalIdeal A⁰ K) : Submodule A K)) ↔
      m = n ∧ ClassGroup.mk K (∏ i, a i) = ClassGroup.mk K (∏ j, b j)

private theorem mk_eq_mk_iff {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (a b : (FractionalIdeal A⁰ K)ˣ) :
    ClassGroup.mk K a = ClassGroup.mk K b ↔ ∃ x : Kˣ, a * toPrincipalIdeal A K x = b := by
  rw [← (ClassGroup.equiv (R := A) K).injective.eq_iff]
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl,
    QuotientGroup.mk'_eq_mk', MonoidHom.mem_range]
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, h⟩
    exact ⟨x, h⟩
  · rintro ⟨x, h⟩
    exact ⟨_, ⟨x, rfl⟩, h⟩

private noncomputable def equiv_of_mul_eq {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (a b : (FractionalIdeal A⁰ K)ˣ) (x : Kˣ)
    (hx : a * toPrincipalIdeal A K x = b) :
    ((a : FractionalIdeal A⁰ K) : Submodule A K) ≃ₗ[A] ((b : FractionalIdeal A⁰ K) : Submodule A K) := by
  have hb : ((a : FractionalIdeal A⁰ K) : Submodule A K).map (LinearMap.mulLeft A (x : K)) =
      ((b : FractionalIdeal A⁰ K) : Submodule A K) := by
    rw [← hx]
    ext y
    simp only [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coe_mul,
      FractionalIdeal.coe_spanSingleton, Submodule.mem_map, LinearMap.mulLeft_apply]
    rw [mul_comm, Submodule.mem_span_singleton_mul]
  exact (Submodule.equivMapOfInjective (LinearMap.mulLeft A (x : K))
    (mul_right_injective₀ x.ne_zero) _).trans (LinearEquiv.ofEq _ _ hb)

private theorem exists_mul_eq_of_equiv {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (a b : (FractionalIdeal A⁰ K)ˣ)
    (φ : ((a : FractionalIdeal A⁰ K) : Submodule A K) ≃ₗ[A] ((b : FractionalIdeal A⁰ K) : Submodule A K)) :
    ∃ x : Kˣ, a * toPrincipalIdeal A K x = b := by
  have ha : ((a : FractionalIdeal A⁰ K) : Submodule A K) ≠ ⊥ := by
    have := a.ne_zero
    rwa [Ne, ← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_zero] at this
  obtain ⟨y0, hy0, hy0ne⟩ := (Submodule.ne_bot_iff _).mp ha
  set y0' : ((a : FractionalIdeal A⁰ K) : Submodule A K) := ⟨y0, hy0⟩ with hy0'
  have hφ0 : (φ y0' : K) ≠ 0 := by
    intro h
    have : φ y0' = 0 := Subtype.ext h
    rw [LinearEquiv.map_eq_zero_iff] at this
    exact hy0ne (congrArg Subtype.val this)
  set x : K := (φ y0' : K) / y0 with hx
  have hx0 : x ≠ 0 := div_ne_zero hφ0 hy0ne
  have key : ∀ z : ((a : FractionalIdeal A⁰ K) : Submodule A K), (φ z : K) = x * z := by
    intro z
    obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := A) (z := (z : K) / y0)
    have hs0 : algebraMap A K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h1 : algebraMap A K s * (z : K) = algebraMap A K r * y0 := by
      field_simp at hrs
      linear_combination -hrs
    have h2 : s • z = r • y0' := Subtype.ext (by simpa [Algebra.smul_def] using h1)
    have h3 := congrArg (fun w => (φ w : K)) h2
    simp only [map_smul, Submodule.coe_smul, Algebra.smul_def] at h3
    rw [hx]
    field_simp
    apply mul_left_cancel₀ hs0
    linear_combination y0 * h3 - (φ y0' : K) * h1
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Units.ext
  apply FractionalIdeal.coeToSubmodule_injective
  ext y
  simp only [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coe_mul,
    FractionalIdeal.coe_spanSingleton, Units.val_mk0, Submodule.mem_mul_span_singleton]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have := key ⟨z, hz⟩
    rw [mul_comm, ← this]
    exact (φ ⟨z, hz⟩).2
  · intro hy
    refine ⟨(φ.symm ⟨y, hy⟩ : K), (φ.symm ⟨y, hy⟩).2, ?_⟩
    have := key (φ.symm ⟨y, hy⟩)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [mul_comm, ← this]

/-- **Theorem 3.31**, last assertion.Two fractional ideals $\mathfrak a$, $\mathfrak b$ of a Dedekind domain $A$ are
isomorphic as $A$-modules iff they define the same element of the class group of $A$. -/
@[kb "milne2020ant" "v3.08, Thm. 3.31 (moreover), p. 58"]
theorem thm_3_31_rank_one {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (a b : (FractionalIdeal A⁰ K)ˣ) :
    Nonempty (((a : FractionalIdeal A⁰ K) : Submodule A K) ≃ₗ[A] ((b : FractionalIdeal A⁰ K) : Submodule A K)) ↔
      ClassGroup.mk K a = ClassGroup.mk K b := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨φ⟩
    exact exists_mul_eq_of_equiv a b φ
  · rintro ⟨x, hx⟩
    exact ⟨equiv_of_mul_eq a b x hx⟩

/-- **Theorem 3.32** (invariant factor theorem; named statement), over a Dedekind domain $A$ with field of fractions
$K$. Torsion-free modules of rank $m$ are realized inside an $m$-dimensional $K$-vector space $V$
(Milne's $M \subseteq K \otimes_A M$). Let $N \subseteq M \subseteq V$ be finitely generated $A$-submodules that both
span $V$ over $K$. Then there are a $K$-basis $e_1, \dots, e_m$ of $V$, fractional ideals
$\mathfrak a_1, \dots, \mathfrak a_m$ and nonzero integral ideals $\mathfrak b_1 \supseteq \mathfrak b_2 \supseteq
\dots \supseteq \mathfrak b_m$ with
$$M = \mathfrak a_1e_1 \oplus \dots \oplus \mathfrak a_me_m, \qquad
N = \mathfrak a_1\mathfrak b_1e_1 \oplus \dots \oplus \mathfrak a_m\mathfrak b_me_m,$$
and the $\mathfrak b_i$ are uniquely determined by the pair $N \subseteq M$.

**Invariant factors** (a definition in prose, p. 58): the ideals $\mathfrak b_1, \dots, \mathfrak b_m$ are the
invariant factors of $N$ in $M$. (The sum is direct because $e$ is a $K$-basis; indices are $0$-based.) -/
@[kb "milne2020ant" "v3.08, Thm. 3.32 and definition in prose (invariant factors), p. 58"]
structure InvariantFactorTheorem (A : Type u) [CommRing A] [IsDedekindDomain A] (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K] : Prop where
  /-- Existence of adapted bases and fractional ideals. -/
  exists_adapted : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] (m : ℕ),
    Module.finrank K V = m → ∀ (M N : Submodule A V), M.FG → N.FG → N ≤ M →
      Submodule.span K (N : Set V) = ⊤ →
      ∃ (e : Module.Basis (Fin m) K V) (a : Fin m → (FractionalIdeal A⁰ K)ˣ) (b : Fin m → Ideal A),
        (∀ i, b i ≠ ⊥) ∧ (∀ i j, i ≤ j → b j ≤ b i) ∧
        M = ⨆ i, ((a i : FractionalIdeal A⁰ K) : Submodule A K).map
          ((LinearMap.toSpanSingleton K V (e i)).restrictScalars A) ∧
        N = ⨆ i, (((a i : FractionalIdeal A⁰ K) * (b i : FractionalIdeal A⁰ K) : FractionalIdeal A⁰ K) :
          Submodule A K).map ((LinearMap.toSpanSingleton K V (e i)).restrictScalars A)
  /-- Uniqueness of the invariant factors. -/
  unique : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] (m : ℕ)
    (M N : Submodule A V) (e e' : Module.Basis (Fin m) K V) (a a' : Fin m → (FractionalIdeal A⁰ K)ˣ)
    (b b' : Fin m → Ideal A), (∀ i, b i ≠ ⊥) → (∀ i j, i ≤ j → b j ≤ b i) →
    (∀ i, b' i ≠ ⊥) → (∀ i j, i ≤ j → b' j ≤ b' i) →
    M = ⨆ i, ((a i : FractionalIdeal A⁰ K) : Submodule A K).map
      ((LinearMap.toSpanSingleton K V (e i)).restrictScalars A) →
    N = ⨆ i, (((a i : FractionalIdeal A⁰ K) * (b i : FractionalIdeal A⁰ K) : FractionalIdeal A⁰ K) :
      Submodule A K).map ((LinearMap.toSpanSingleton K V (e i)).restrictScalars A) →
    M = ⨆ i, ((a' i : FractionalIdeal A⁰ K) : Submodule A K).map
      ((LinearMap.toSpanSingleton K V (e' i)).restrictScalars A) →
    N = ⨆ i, (((a' i : FractionalIdeal A⁰ K) * (b' i : FractionalIdeal A⁰ K) : FractionalIdeal A⁰ K) :
      Submodule A K).map ((LinearMap.toSpanSingleton K V (e' i)).restrictScalars A) →
    b = b'

end NumberFieldKB.MilneANT
