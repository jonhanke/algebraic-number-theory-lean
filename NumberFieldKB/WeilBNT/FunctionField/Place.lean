import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.RingTheory.Valuation.IsTrivialOn
import QuadFormsKB.Citation

/-!
# Places of a global function field (Weil, *Basic Number Theory*, III.§1, Ch. VI)

Weil's places of an A-field $k$ of characteristic $p$ are its nontrivial absolute values (III.§1); for a function
field these are the discrete valuations of $k$, all of them, including those Mathlib's `FunctionField` API calls
"infinite". Here $k$ is a field with an algebra structure over a finite field $\mathbb F_q$ (`Fq`).

* **`Place Fq k`**: a *normalized* discrete valuation `k → ℤᵐ⁰`, i.e. a surjective valuation, trivial on
  $\mathbb F_q$. This is the definition of Tau Ceti's `TauCeti.Place k F`
  (`TauCeti/FieldTheory/FunctionField/Place/Basic.lean`, Tau Ceti 7ed979d, Apache 2.0; Stichtenoth, Def. 1.1.4, 1.1.9),
  restated here because Tau Ceti cannot be imported on our toolchain; the two structures have the same fields, so
  the comparison after an upgrade is the identity. Normalizing the value group to all of $\mathbb Z$ makes equality
  of places equality of valuations: equivalent normalized valuations are equal (`Place.eq_of_isEquiv`).
* Since $\mathbb F_q$ is finite, every valuation of $k$ is trivial on it (Mathlib `FiniteField.valuation_algebraMap_eq_one`),
  so `Place.mk'` builds a place from any surjective valuation.
* **`Place.integers`** ($\mathfrak r_v$, the valuation ring of the place), a discrete valuation ring
  (`Place.isDiscreteValuationRing`); **`Place.ord`** the additive order, $\operatorname{ord}_v(0)=0$ by convention.
* **`Place.ofHeightOneSpectrum`**: a nonzero prime $\mathfrak p$ of a Dedekind domain $A\subset k$ with fraction field
  $k$ and $\mathbb F_q\to A$ gives a place (its adic valuation, Mathlib `HeightOneSpectrum.valuation`). This is the
  comparison with Mathlib's finite places of a model; `Model.lean` proves every place arises this way from one of two
  models.

Weil's index $v$ in $k_v$, $\mathfrak r_v$, $\mathfrak p_v$ is a `Place Fq k`.
-/

open scoped WithZero
open Valuation IsDedekindDomain

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable (Fq k : Type*) [Field Fq] [Field k] [Algebra Fq k]

/-- **A place of the global function field $k$ over $\mathbb F_q$** (Weil III.§1; Tau Ceti `TauCeti.Place`): a
normalized discrete valuation of $k$, i.e. a surjective valuation `k → ℤᵐ⁰`, trivial on the constants
$\mathbb F_q$. -/
structure Place where
  /-- The normalized valuation $v$ (multiplicative convention: $\mathfrak r_v=\{x : v(x)\le 1\}$, a prime element
  $\pi$ has $v(\pi)=\exp(-1)$). -/
  valuation : Valuation k ℤᵐ⁰
  /-- Normalization: the value group is all of $\mathbb Z$. -/
  valuation_surjective : Function.Surjective valuation
  /-- Triviality on the constants. -/
  isTrivialOn : valuation.IsTrivialOn Fq

namespace Place

variable {Fq k}

instance (v : Place Fq k) : v.valuation.IsTrivialOn Fq := v.isTrivialOn

@[ext]
theorem ext {v w : Place Fq k} (h : v.valuation = w.valuation) : v = w := by
  cases v; cases w; congr

theorem valuation_injective : Function.Injective (valuation : Place Fq k → Valuation k ℤᵐ⁰) :=
  fun _ _ h => ext h

/-- Over a finite field of constants every surjective valuation is a place: triviality on $\mathbb F_q$ is
automatic. -/
def mk' [Finite Fq] (v : Valuation k ℤᵐ⁰) (hv : Function.Surjective v) : Place Fq k :=
  ⟨v, hv, inferInstance⟩

@[simp] theorem mk'_valuation [Finite Fq] (v : Valuation k ℤᵐ⁰) (hv : Function.Surjective v) :
    (mk' (Fq := Fq) v hv).valuation = v := rfl

variable (v : Place Fq k)

/-- The valuation ring $\mathfrak r_v=\{x\in k : v(x)\le1\}$ of the place. -/
def integers : ValuationSubring k := v.valuation.valuationSubring

theorem mem_integers_iff {x : k} : x ∈ v.integers ↔ v.valuation x ≤ 1 := Iff.rfl

theorem valuation_algebraMap {c : Fq} (hc : c ≠ 0) : v.valuation (algebraMap Fq k c) = 1 :=
  v.isTrivialOn.eq_one c hc

theorem algebraMap_mem_integers (c : Fq) : algebraMap Fq k c ∈ v.integers := by
  rw [mem_integers_iff]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [v.valuation_algebraMap hc]

theorem valueGroup_eq_top : v.valuation.valueGroup = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨x, hx⟩ := v.valuation_surjective (g : ℤᵐ⁰)
  exact MonoidWithZeroHom.mem_valueGroup _ ⟨x, hx⟩

instance : IsCyclic v.valuation.valueGroup := Subgroup.isCyclic _

instance : Nontrivial v.valuation.valueGroup := by
  obtain ⟨x, hx⟩ := v.valuation_surjective (WithZero.exp 1)
  have h1 : (WithZero.exp (1 : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  refine ⟨⟨⟨Units.mk0 _ h1, MonoidWithZeroHom.mem_valueGroup _ ⟨x, hx⟩⟩, 1, fun h => ?_⟩⟩
  have := congrArg (fun u : v.valuation.valueGroup => ((u : ℤᵐ⁰ˣ) : ℤᵐ⁰)) h
  simp [← WithZero.exp_zero] at this

/-- $\mathfrak r_v$ is a discrete valuation ring. -/
instance isDiscreteValuationRing : IsDiscreteValuationRing v.integers :=
  Valuation.valuationSubring_isDiscreteValuationRing v.valuation

/-- The additive order $\operatorname{ord}_v(x)=-\log v(x)$ (with $\operatorname{ord}_v(0)=0$). -/
def ord (x : k) : ℤ := -WithZero.log (v.valuation x)

theorem integers_ne_top : v.integers ≠ ⊤ := by
  intro h
  obtain ⟨x, hx⟩ := v.valuation_surjective (WithZero.exp 1)
  have : x ∈ v.integers := h ▸ trivial
  rw [mem_integers_iff, hx] at this
  exact absurd this (by simp [← WithZero.exp_zero])

end Place

/-! ### Places from Dedekind models -/

section Model

variable {Fq k} [Finite Fq] (A : Type*) [CommRing A] [IsDedekindDomain A] [Algebra A k] [IsFractionRing A k]

/-- **The place of $k$ at a nonzero prime $\mathfrak p$ of a Dedekind model** $A$ of $k$ (fraction field $k$):
Mathlib's $\mathfrak p$-adic valuation `HeightOneSpectrum.valuation`, which is surjective; triviality on
$\mathbb F_q$ is automatic. -/
def Place.ofHeightOneSpectrum (p : HeightOneSpectrum A) : Place Fq k :=
  Place.mk' (p.valuation k) (p.valuation_surjective k)

@[simp] theorem Place.ofHeightOneSpectrum_valuation (p : HeightOneSpectrum A) :
    (Place.ofHeightOneSpectrum (Fq := Fq) A p).valuation = p.valuation k := rfl

end Model

end NumberFieldKB.WeilBNT.FF
