import NumberFieldKB.HilbertClassField.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Moduli, ray class groups and class fields (Milne, *Class Field Theory*, Introduction)

The definitions in prose of Milne's Introduction (pp. 1–9), for a number field $K$:

* `IsTotallyRamifiedIn` (p. 2); splitting completely is `SplitsCompletelyIn` / `splitPrimes` (existing).
* `IsPositiveAt` (an element positive at a real prime, p. 4).
* `Modulus K` $\mathfrak m = \mathfrak m_0\mathfrak m_\infty$, the group `coprimeIdeals m` $= I^{S(\mathfrak m)}$, the
  subgroup `rayPrincipal m` $= P_\mathfrak m$ and the **ray class group** `RayClassGroup m` $= C_\mathfrak m$ (p. 5),
  with $C_{(1)} \cong \mathrm{Cl}_K$ (`rayClassGroupOneEquiv`) and the narrow class group (`narrowModulus`).
* **Class fields**: `IsUnramifiedClassField` (for a subgroup of the class group, p. 4) and `IsClassField` (for a
  subgroup of a ray class group, p. 5); the conductor (`IsConductor`, p. 5).
* The Weber $L$-series of a character of a ray class group (`weberLSeries`, p. 8) and the Artin $L$-function of a
  representation (`artinLFunction`, p. 8). Dirichlet $L$-functions are Mathlib's `DirichletCharacter.LFunction`.

Finite, real and complex primes (p. 4) are Mathlib's `IsDedekindDomain.HeightOneSpectrum (𝓞 K)`,
`NumberField.InfinitePlace.IsReal`, `NumberField.InfinitePlace.IsComplex`; the Frobenius element of an unramified
prime (p. 7) is `NumberFieldKB.Chebotarev.frobAt` (Mathlib's `arithFrobAt`), its conjugacy class `frobClass`.

**Erratum.** Milne p. 5 defines a class field for $H \subseteq C_\mathfrak m$ as "an abelian extension $L$ of $K$,
unramified at the primes dividing $\mathfrak m$" with the prescribed splitting; the intended condition (used in
Theorem 0.5) is *unramified at the primes not dividing $\mathfrak m$*. `IsClassField` uses the latter.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

/-! ## Splitting and ramification of primes (p. 2) -/

/-- **Totally ramified prime** (Milne, *CFT*, Introduction, p. 2): a prime $\mathfrak p$ of $\mathcal O_K$ is totally
ramified in $L$ if every prime $\mathfrak P$ of $\mathcal O_L$ above it has $e(\mathfrak P/\mathfrak p) = [L:K]$
(then there is exactly one, $\mathfrak p\mathcal O_L = \mathfrak P^{[L:K]}$). (The text of v4.03 reads "when all
$e_i > 1$"; the standard notion, used in Chapter I, is the one here.) -/
@[kb "milne2020cft" "Introduction, p. 2 (totally ramified prime)"]
def IsTotallyRamifiedIn (L : Type) [Field L] [NumberField L] [Algebra K L] (𝔭 : Ideal (𝓞 K)) : Prop :=
  ∀ 𝔓 : Ideal (𝓞 L), 𝔓.IsPrime → 𝔓.LiesOver 𝔭 → 𝔓.ramificationIdx (𝓞 K) = Module.finrank K L

/-- **Positive at a real prime** (Milne, *CFT*, Introduction, p. 4): $a \in K$ is positive at the real place $v$ if its
image under the corresponding real embedding is positive. -/
@[kb "milne2020cft" "Introduction, p. 4 (positive at a real prime)"]
def IsPositiveAt (v : InfinitePlace K) (hv : v.IsReal) (a : K) : Prop :=
  0 < InfinitePlace.embedding_of_isReal hv a

/-! ## Moduli and ray class groups (p. 5) -/

/-- **A modulus** $\mathfrak m = \mathfrak m_0\mathfrak m_\infty$ of $K$ (Milne, *CFT*, Introduction, p. 5): a nonzero
integral ideal $\mathfrak m_0$ of $\mathcal O_K$ and a set $\mathfrak m_\infty$ of real places. -/
@[kb "milne2020cft" "Introduction, p. 5 (modulus)"]
structure Modulus where
  /-- The finite part $\mathfrak m_0$. -/
  finite : Ideal (𝓞 K)
  finite_ne_bot : finite ≠ ⊥
  /-- The infinite part $\mathfrak m_\infty$: a set of real places. -/
  infinite : Set (InfinitePlace K)
  isReal_of_mem : ∀ v ∈ infinite, v.IsReal

variable {K}

/-- $\mathrm{ord}_\mathfrak p(\mathfrak m_0)$, the exponent of $\mathfrak p$ in $\mathfrak m_0$. -/
def Modulus.ord (m : Modulus K) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk m.finite).factors

/-- The `v`-adic valuation of `a` is `exp (-count_v (a))`. -/
theorem valuation_eq_exp_neg_count (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    v.valuation K (a : K) =
      WithZero.exp (-(FractionalIdeal.count K v
        (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K))) := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (𝓞 K)⁰ (a : K)
  simp only at hnd
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hnd
    exact a.ne_zero hnd.symm
  have hd : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hI : (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) (d : 𝓞 K))⁻¹ *
        ((Ideal.span {n} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
      ← map_mul, ← hnd]
    rw [IsFractionRing.mk'_eq_div, div_eq_inv_mul]
  have hne : (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    (Units.ne_zero _)
  rw [FractionalIdeal.count_well_defined K v hne hI, ← hnd, HeightOneSpectrum.valuation_of_mk',
    HeightOneSpectrum.intValuation_if_neg _ hn,
    HeightOneSpectrum.intValuation_if_neg _ (nonZeroDivisors.coe_ne_zero d), ← WithZero.exp_sub]
  congr 1
  ring

theorem one_le_ord (m : Modulus K) (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ m.finite) :
    1 ≤ m.ord v := by
  have := (Associates.count_ne_zero_iff_dvd m.finite_ne_bot v.irreducible).2 hv
  unfold Modulus.ord
  omega

/-- $I^{S(\mathfrak m)}$ (Milne, *CFT*, Introduction, p. 5): the fractional ideals of $K$ prime to $\mathfrak m_0$
(exponent $0$ at every prime dividing $\mathfrak m_0$). -/
@[kb "milne2020cft" "Introduction, p. 5 (the group I^{S(m)})"]
def coprimeIdeals (m : Modulus K) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.finite →
    FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  mul_mem' := by
    intro I J hI hJ v hv
    simp only [Units.val_mul]
    rw [FractionalIdeal.count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv]
    rfl
  one_mem' := by
    intro v _
    simp [FractionalIdeal.count_one]
  inv_mem' := by
    intro I hI v hv
    have : ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        ((I : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv₀ I.ne_zero]; exact I.inv_mul
    show FractionalIdeal.count K v ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 0
    rw [this, FractionalIdeal.count_inv, hI v hv]; rfl

/-- If `v(a - 1) < 1` then `v(a) = 1`. -/
theorem valuation_eq_one_of_sub_lt (v : HeightOneSpectrum (𝓞 K)) {a : K}
    (h : v.valuation K (a - 1) < 1) : v.valuation K a = 1 := by
  have := Valuation.map_eq_of_sub_lt (v.valuation K) (x := 1) (y := a) (by simpa using h)
  simpa using this

theorem valuation_sub_one_lt (m : Modulus K) (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ m.finite)
    {a : K} (h : v.valuation K (a - 1) ≤ WithZero.exp (-(m.ord v : ℤ))) :
    v.valuation K (a - 1) < 1 := by
  refine lt_of_le_of_lt h ?_
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  have := one_le_ord m v hv
  omega

/-- $a \equiv 1 \bmod^\times \mathfrak m$ (Milne, *CFT*, Introduction, p. 5): $a > 0$ at every real prime in
$\mathfrak m_\infty$, and $\mathrm{ord}_\mathfrak p(a - 1) \ge \mathrm{ord}_\mathfrak p(\mathfrak m_0)$ for every prime
$\mathfrak p \mid \mathfrak m_0$ (in terms of the $\mathfrak p$-adic valuation, $v_\mathfrak p(a-1) \le
\exp(-\mathrm{ord}_\mathfrak p\mathfrak m_0)$). These $a$ form the subgroup `congruenceSubgroup m` of $K^\times$. -/
@[kb "milne2020cft" "Introduction, p. 5 (a ≡ 1 mod m)"]
def congruenceSubgroup (m : Modulus K) : Subgroup Kˣ where
  carrier := {a | (∀ v (hv : v ∈ m.infinite), IsPositiveAt K v (m.isReal_of_mem v hv) a) ∧
    ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.finite →
      v.valuation K ((a : K) - 1) ≤ WithZero.exp (-(m.ord v : ℤ))}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have := ha1 v hv
      have := hb1 v hv
      unfold IsPositiveAt at *
      simp only [Units.val_mul, map_mul]
      positivity
    · have h1 := ha2 v hv
      have h2 := hb2 v hv
      have hva := valuation_eq_one_of_sub_lt v (valuation_sub_one_lt m v hv h1)
      have : ((a * b : Kˣ) : K) - 1 = (a : K) * ((b : K) - 1) + ((a : K) - 1) := by
        push_cast; ring
      rw [this]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ h1)
      rw [map_mul, hva, one_mul]; exact h2
  one_mem' := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · unfold IsPositiveAt; simp
    · simp
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have := ha1 v hv
      unfold IsPositiveAt at *
      simp only [Units.val_inv_eq_inv_val, map_inv₀]
      positivity
    · have h1 := ha2 v hv
      have hva := valuation_eq_one_of_sub_lt v (valuation_sub_one_lt m v hv h1)
      have : (((a⁻¹ : Kˣ)) : K) - 1 = -(((a : K) - 1) * (a : K)⁻¹) := by
        have := a.ne_zero
        push_cast; field_simp; ring
      rw [this, Valuation.map_neg, map_mul, map_inv₀, hva]
      simpa using h1

/-- $P_\mathfrak m$ (Milne, *CFT*, Introduction, p. 5): the principal fractional ideals $(a)$ with
$a \equiv 1 \bmod^\times \mathfrak m$. -/
@[kb "milne2020cft" "Introduction, p. 5 (the group P_m)"]
def rayPrincipal (m : Modulus K) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (congruenceSubgroup m).map (toPrincipalIdeal (𝓞 K) K)

/-- $P_\mathfrak m \subseteq I^{S(\mathfrak m)}$. -/
theorem rayPrincipal_le (m : Modulus K) : rayPrincipal m ≤ coprimeIdeals m := by
  rintro _ ⟨a, ⟨_, ha2⟩, rfl⟩ v hv
  have h1 := ha2 v hv
  have hva := valuation_eq_one_of_sub_lt v (valuation_sub_one_lt m v hv h1)
  have := valuation_eq_exp_neg_count v a
  rw [hva, eq_comm, ← WithZero.exp_zero, WithZero.exp_inj] at this
  omega

/-- **The ray class group** $C_\mathfrak m = I^{S(\mathfrak m)}/P_\mathfrak m$ (Milne, *CFT*, Introduction, p. 5). -/
@[kb "milne2020cft" "Introduction, p. 5 (ray class group C_m)"]
abbrev RayClassGroup (m : Modulus K) : Type :=
  coprimeIdeals m ⧸ (rayPrincipal m).subgroupOf (coprimeIdeals m)

/-- Every subgroup of the (abelian) ray class group is normal, so $C_\mathfrak m/H$ is a group. -/
instance RayClassGroup.normal (m : Modulus K) (H : Subgroup (RayClassGroup m)) : H.Normal :=
  ⟨fun n hn g => by rwa [mul_comm g n, mul_inv_cancel_right]⟩

/-- A nonzero prime $\mathfrak p \nmid \mathfrak m_0$ as an element of $I^{S(\mathfrak m)}$. -/
def coprimePrime (m : Modulus K) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) :
    coprimeIdeals m :=
  ⟨FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩, by
    intro w hw
    have hwv : w ≠ v := by rintro rfl; exact hv hw
    rw [FractionalIdeal.coe_mk0]
    exact FractionalIdeal.count_maximal_coprime K w hwv.symm⟩

/-- The class $[\mathfrak p] \in C_\mathfrak m$ of a prime $\mathfrak p \nmid \mathfrak m_0$. -/
def rayClass (m : Modulus K) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) : RayClassGroup m :=
  QuotientGroup.mk (coprimePrime m v hv)

variable (K) in
/-- The modulus $\mathfrak m = (1)$ (no primes). -/
def Modulus.one : Modulus K where
  finite := ⊤
  finite_ne_bot := top_ne_bot
  infinite := ∅
  isReal_of_mem := fun _ h => h.elim

variable (K) in
/-- The modulus $\mathfrak m_\infty$ = the product of all real places ($\mathfrak m_0 = 1$); its ray class group is the
**narrow class group** (Milne, *CFT*, Introduction, p. 5). -/
@[kb "milne2020cft" "Introduction, p. 5 (narrow class group)"]
def narrowModulus : Modulus K where
  finite := ⊤
  finite_ne_bot := top_ne_bot
  infinite := {v | v.IsReal}
  isReal_of_mem := fun _ h => h

theorem coprimeIdeals_eq_top (m : Modulus K) (h0 : m.finite = ⊤) : coprimeIdeals m = ⊤ := by
  rw [eq_top_iff]
  intro I _ v hv
  rw [h0, Ideal.dvd_iff_le, top_le_iff] at hv
  exact absurd hv v.isPrime.ne_top

theorem congruenceSubgroup_eq_top (m : Modulus K) (h0 : m.finite = ⊤) (hinf : m.infinite = ∅) :
    congruenceSubgroup m = ⊤ := by
  rw [eq_top_iff]
  intro a _
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [hinf] at hv; exact hv.elim
  · rw [h0, Ideal.dvd_iff_le, top_le_iff] at hv
    exact absurd hv v.isPrime.ne_top

/-- The identification `I^{S(m)} ≃ (FractionalIdeal)ˣ` when `m₀ = (1)`. -/
def coprimeIdealsEquiv (m : Modulus K) (h0 : m.finite = ⊤) :
    coprimeIdeals m ≃* (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (MulEquiv.subgroupCongr (coprimeIdeals_eq_top m h0)).trans Subgroup.topEquiv

theorem coprimeIdealsEquiv_apply (m : Modulus K) (h0 : m.finite = ⊤) (x : coprimeIdeals m) :
    coprimeIdealsEquiv m h0 x = (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := rfl

/-- For a modulus with $\mathfrak m_0 = (1)$ and $\mathfrak m_\infty = \emptyset$, $C_\mathfrak m$ is the class group:
$I^{S(\mathfrak m)}$ is all fractional ideals and $P_\mathfrak m$ all principal ones. -/
def rayClassGroupEquivClassGroup (m : Modulus K) (h0 : m.finite = ⊤) (hinf : m.infinite = ∅) :
    RayClassGroup m ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.congr _ (toPrincipalIdeal (𝓞 K) K).range (coprimeIdealsEquiv m h0) (by
    have hP : rayPrincipal m = (toPrincipalIdeal (𝓞 K) K).range := by
      rw [rayPrincipal, congruenceSubgroup_eq_top m h0 hinf, ← MonoidHom.range_eq_map]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hP]; exact hx
    · intro hy
      rw [← hP] at hy
      exact ⟨(coprimeIdealsEquiv m h0).symm y, hy, by simp⟩)).trans (ClassGroup.equiv K).symm

/-- Under `rayClassGroupEquivClassGroup`, the ray class of a prime is its ideal class. -/
theorem rayClassGroupEquivClassGroup_rayClass (m : Modulus K) (h0 : m.finite = ⊤) (hinf : m.infinite = ∅)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) :
    rayClassGroupEquivClassGroup m h0 hinf (rayClass m v hv) = primeClass K v := by
  simp only [rayClassGroupEquivClassGroup]
  rw [primeClass, MulEquiv.trans_apply, MulEquiv.symm_apply_eq, ClassGroup.equiv_mk0]
  rfl

variable (K) in
/-- **$C_{(1)}$ is the class group** (Milne, *CFT*, Introduction, p. 5: "if $\mathfrak m = 1$, then
$C_\mathfrak m = C$"). -/
@[kb "milne2020cft" "Introduction, p. 5 (C_1 = C)"]
def rayClassGroupOneEquiv : RayClassGroup (Modulus.one K) ≃* ClassGroup (𝓞 K) :=
  rayClassGroupEquivClassGroup (Modulus.one K) rfl rfl

/-! ## Class fields (pp. 4–5) -/

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **Class field for a subgroup of the class group** (Milne, *CFT*, Introduction, p. 4): for $H \subseteq C$, a finite
abelian extension $L$ of $K$, unramified at every prime ideal and at every real prime, such that the prime ideals of
$\mathcal O_K$ splitting in $L$ are exactly those whose class lies in $H$. -/
@[kb "milne2020cft" "Introduction, p. 4 (class field for a subgroup of the class group)"]
structure IsUnramifiedClassField (H : Subgroup (ClassGroup (𝓞 K))) : Prop where
  comm : ∀ σ τ : Gal(L/K), σ * τ = τ * σ
  unramified : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K L
  unramifiedAtInfinitePlaces : IsUnramifiedAtInfinitePlaces K L
  splits_iff : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ splitPrimes K L ↔ primeClass K v ∈ H

/-- **Class field for a subgroup of a ray class group** (Milne, *CFT*, Introduction, p. 5): for
$H \subseteq C_\mathfrak m$, a finite abelian extension $L$ of $K$, unramified at the primes not dividing
$\mathfrak m_0$ (see the erratum in the module docstring), such that a prime $\mathfrak p \nmid \mathfrak m_0$ splits
in $L$ iff its class in $C_\mathfrak m$ lies in $H$. -/
@[kb "milne2020cft" "Introduction, p. 5 (class field for a subgroup of a ray class group)"]
structure IsClassField (m : Modulus K) (H : Subgroup (RayClassGroup m)) : Prop where
  comm : ∀ σ τ : Gal(L/K), σ * τ = τ * σ
  unramified : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ m.finite → v ∈ unramifiedPrimes K L
  splits_iff : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite),
    v ∈ splitPrimes K L ↔ rayClass m v hv ∈ H

/-- $\mathfrak m'$ divides $\mathfrak m$: $\mathfrak m'_0 \mid \mathfrak m_0$ and
$\mathfrak m'_\infty \subseteq \mathfrak m_\infty$. -/
def Modulus.Dvd (m' m : Modulus K) : Prop := m'.finite ∣ m.finite ∧ m'.infinite ⊆ m.infinite

/-- **The conductor** of a finite abelian extension $L/K$ (Milne, *CFT*, Introduction, p. 5): the smallest modulus
$\mathfrak f$ (for divisibility) such that $L$ is a class field for some subgroup of $C_\mathfrak f$. -/
@[kb "milne2020cft" "Introduction, p. 5 (conductor of an abelian extension)"]
def IsConductor (f : Modulus K) : Prop :=
  (∃ H : Subgroup (RayClassGroup f), IsClassField L f H) ∧
    ∀ m : Modulus K, (∃ H : Subgroup (RayClassGroup m), IsClassField L m H) → f.Dvd m

/-! ## Weber and Artin $L$-functions (p. 8) -/

/-- The class in $C_\mathfrak m$ of a nonzero integral ideal $\mathfrak a$ prime to $\mathfrak m_0$. -/
def idealRayClass (m : Modulus K) (𝔞 : Ideal (𝓞 K)) (h0 : 𝔞 ≠ ⊥) (h : 𝔞 ⊔ m.finite = ⊤) : RayClassGroup m :=
  QuotientGroup.mk ⟨FractionalIdeal.mk0 K ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h0⟩, by
    intro w hw
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coe K w h0]
    have : ¬ w.asIdeal ∣ 𝔞 := by
      intro hd
      have : w.asIdeal ∣ 𝔞 ⊔ m.finite := by
        rw [Ideal.dvd_iff_le] at hd hw ⊢; exact sup_le hd hw
      rw [h, Ideal.dvd_iff_le, top_le_iff] at this
      exact w.isPrime.ne_top this
    have := mt (Associates.count_ne_zero_iff_dvd h0 w.irreducible).1 this
    simpa using this⟩

open Classical in
/-- **The Weber $L$-series** of a character $\chi$ of a ray class group $C_\mathfrak m$ (Milne, *CFT*,
Introduction, p. 8): $L(s,\chi) = \sum_{(\mathfrak a, \mathfrak m) = 1} \chi(\mathfrak a)\,N\mathfrak a^{-s}$, the sum over
nonzero integral ideals prime to $\mathfrak m_0$ (absolutely convergent for $\mathrm{Re}\, s > 1$). -/
@[kb "milne2020cft" "Introduction, p. 8 (Weber L-series)"]
def weberLSeries (m : Modulus K) (χ : RayClassGroup m →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' 𝔞 : Ideal (𝓞 K),
    if h : 𝔞 ≠ ⊥ ∧ 𝔞 ⊔ m.finite = ⊤ then
      (χ (idealRayClass m 𝔞 h.1 h.2) : ℂ) * ((Ideal.absNorm 𝔞 : ℕ) : ℂ) ^ (-s)
    else 0

/-- **The Artin $L$-function** (Milne, *CFT*, Introduction, p. 8): for a finite set $S$ of primes of $K$ containing
those ramified in $L$ and a representation $\rho : \mathrm{Gal}(L/K) \to \mathrm{GL}_n(\mathbb C)$,
$L_S(s,\rho) = \prod_{\mathfrak p \notin S} \det(I - \rho(\mathrm{Frob}_\mathfrak p) N\mathfrak p^{-s})^{-1}$. The
determinant depends only on the conjugacy class of $\mathrm{Frob}_\mathfrak p$; the product is Mathlib's
unconditional product `tprod` (it converges for $\mathrm{Re}\, s > 1$). -/
@[kb "milne2020cft" "Introduction, p. 8 (Artin L-function)"]
def artinLFunction (S : Set (HeightOneSpectrum (𝓞 K))) {n : ℕ} (ρ : Gal(L/K) →* GL (Fin n) ℂ) (s : ℂ) : ℂ :=
  ∏' 𝔭 : {𝔭 : HeightOneSpectrum (𝓞 K) // 𝔭 ∉ S},
    (Matrix.det (1 - ((Ideal.absNorm 𝔭.1.asIdeal : ℂ) ^ (-s)) •
      ((ρ (frobAt K L 𝔭.1 (Classical.arbitrary _)) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))⁻¹

end NumberFieldKB.MilneCFT
