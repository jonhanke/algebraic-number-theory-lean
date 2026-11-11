import NumberFieldKB.MilneANT.Ch7PlacesFFClosedDiff
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Algebraic Number Theory*, Remark 7.17(b): the sum formula for function fields over an algebraically
closed field

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 7.17(b), p. 112; bib key `milne2020ant`.

**`remark7_17b`** proves the named statement `Remark7_17b k K` unconditionally: for $k$ algebraically closed and $K$
finite over $k(T)$, the primes of $K$ trivial on $k$ (surjective valuations $v : K \to \mathbb Z_{\mathrm m 0}$ trivial
on $k$, with $\operatorname{ord}_v = -\log v$) satisfy: for $a \neq 0$ only finitely many have $v(a) \neq 1$, and
$\sum_v \operatorname{ord}_v(a) = 0$.

Proof outline.
1. (`Ch7PlacesFFClosedZeros`) For a separating element $x$ (transcendental, $K/k(x)$ separable; it exists since $k$ is
   perfect), the places with $v(x)<1$ are the primes of the integral closure $B$ of $k[X]$ in $K$ over $(X)$, with
   $\operatorname{ord}_v x$ the ramification index; all residue degrees are $1$ since $k[X]/(X)\cong k$ is algebraically
   closed. The fundamental identity gives $\sum_v \max(\operatorname{ord}_v x, 0) = [K:k(x)]$ (`Sep.sum_max_ord`).
2. Applying 1 to $x^{-1}$ (again separating, $k(x^{-1}) = k(x)$) gives the same for the poles, so $\operatorname{ord}_v x$
   has finite support and sum $0$ (`good_sep`).
3. (`Ch7PlacesFFClosedDiff`) Every $a \in K^\times$ is a quotient of separating elements (Kähler differentials), and
   `Good` (finite support, sum zero) is closed under products and inverses (`good_all`).

The arguments are adapted from the finite-constant-field Weil track,
`NumberFieldKB/WeilBNT/FunctionField/{Place,PlaceDedekind,Separating,FundamentalIdentity,ProductFormula}.lean`, with
residue degree $1$ replacing the degree $\deg v$.
-/

open scoped Polynomial
open NumberFieldKB.WeilBNT.FF KaehlerDifferential IntermediateField

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneANT.FFClosed

universe u v

/-- The conclusion for an element $a$: $\operatorname{ord}_w a$ has finite support and sum $0$ over the places
$w$ of $K$ trivial on $k$. -/
def Good (k : Type u) {K : Type v} [Field k] [Field K] [Algebra k K] (a : K) : Prop :=
  (Function.support fun w : Place k K => w.ord a).Finite ∧ ∑ᶠ w : Place k K, w.ord a = 0

variable {k : Type u} {K : Type v} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

theorem ord_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (w : Place k K) :
    w.ord (a * b) = w.ord a + w.ord b := by
  have h1 : w.valuation a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have h2 : w.valuation b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
  rw [Place.ord, Place.ord, Place.ord, map_mul, WithZero.log_mul h1 h2]
  ring

theorem ord_inv {a : K} (w : Place k K) : w.ord a⁻¹ = -w.ord a := by
  rw [Place.ord, Place.ord, map_inv₀, WithZero.log_inv]

theorem Good.mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (h1 : Good k a) (h2 : Good k b) : Good k (a * b) := by
  have e : (fun w : Place k K => w.ord (a * b)) = (fun w => w.ord a) + (fun w => w.ord b) :=
    funext fun w => ord_mul ha hb w
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (h1.1.union h2.1).subset (Function.support_add _ _)
  · simp_rw [ord_mul ha hb]
    rw [finsum_add_distrib h1.1 h2.1, h1.2, h2.2, add_zero]

theorem Good.inv {a : K} (h : Good k a) : Good k a⁻¹ := by
  unfold Good
  simp_rw [ord_inv]
  refine ⟨by simpa [Function.support_neg] using h.1, ?_⟩
  rw [finsum_neg_distrib, h.2, neg_zero]

/-- A separating element satisfies the sum formula. -/
theorem good_sep (s : SeparatingElement k K) : Good k s.x := by
  obtain ⟨h1, n1⟩ := Sep.sum_max_ord s
  obtain ⟨h2, n2⟩ := Sep.sum_max_ord s.inv
  have e2 : ∀ w : Place k K, w.ord s.inv.x = -w.ord s.x := fun w => ord_inv w
  have e3 : Module.finrank k⟮s.inv.x⟯ K = Module.finrank k⟮s.x⟯ K := by
    rw [SeparatingElement.inv_x, adjoin_inv_eq]
  simp only [e2] at h2 n2
  rw [e3] at n2
  have key : ∀ w : Place k K, w.ord s.x = max (w.ord s.x) 0 - max (-w.ord s.x) 0 := by
    intro w; omega
  refine ⟨(h1.union h2).subset ?_, ?_⟩
  · intro w hw
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h hw
    apply hw
    rw [key w, h.1, h.2, sub_self]
  · rw [finsum_congr key, finsum_sub_distrib h1 h2, n1, n2, sub_self]

/-- Every nonzero element satisfies the sum formula. -/
theorem good_all {a : K} (ha : a ≠ 0) : Good k a := by
  obtain ⟨s⟩ := exists_separating (k := k) (K := K)
  by_cases hD : D k K a = 0
  · have hxa : D k K (s.x * a) ≠ 0 := by
      rw [Derivation.leibniz, hD, smul_zero, zero_add]
      intro h
      exact Sep.D_x_ne_zero s ((smul_eq_zero.mp h).resolve_left ha)
    have hg := good_sep (Sep.ofDNeZero s (s.x * a) hxa)
    have hs := good_sep s
    have hx := s.x_ne_zero
    have heq : a = (s.x * a) * s.x⁻¹ := by field_simp
    rw [heq]
    exact Good.mul (mul_ne_zero hx ha) (inv_ne_zero hx) hg hs.inv
  · exact good_sep (Sep.ofDNeZero s a hD)

end NumberFieldKB.MilneANT.FFClosed

namespace NumberFieldKB.MilneANT

open FFClosed

/-- **Remark 7.17(b)** (proved, unconditionally): for a finite extension $K$ of $k(T)$ with $k$ algebraically
closed, the normalized discrete valuations $\operatorname{ord}_v$ of $K$ trivial on $k$ satisfy
$\sum_v \operatorname{ord}_v(a) = 0$ for every $a \in K^\times$ (a finite sum). -/
@[kb "milne2020ant" "v3.08, Remark 7.17, p. 112"]
theorem remark7_17b (k K : Type*) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FiniteDimensional (RatFunc k) K] : Remark7_17b k K := by
  let e : {v : Valuation K (WithZero (Multiplicative ℤ)) //
      Function.Surjective v ∧ ∀ c : k, c ≠ 0 → v (algebraMap k K c) = 1} ≃ Place k K :=
    { toFun := fun v => ⟨v.1, v.2.1, ⟨v.2.2⟩⟩
      invFun := fun w => ⟨w.valuation, w.valuation_surjective, fun c hc => w.valuation_algebraMap hc⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hlog : ∀ (v : {v : Valuation K (WithZero (Multiplicative ℤ)) //
      Function.Surjective v ∧ ∀ c : k, c ≠ 0 → v (algebraMap k K c) = 1}) (a : K),
      WithZero.log (v.1 a) = -(e v).ord a := by
    intro v a
    simp [e, Place.ord]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have h := (good_all (k := k) ha).1
    refine (h.preimage e.injective.injOn).subset ?_
    intro v hv
    simp only [Set.mem_preimage, Function.mem_support]
    intro h0
    apply hv
    have hv0 : v.1 a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
    rw [← WithZero.exp_log hv0, hlog, h0]
    simp
  · simp_rw [hlog]
    rw [finsum_neg_distrib, finsum_comp_equiv e (f := fun w : Place k K => w.ord a), (good_all (k := k) ha).2, neg_zero]

end NumberFieldKB.MilneANT
