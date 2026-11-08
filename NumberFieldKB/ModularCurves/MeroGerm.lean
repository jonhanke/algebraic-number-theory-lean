import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Valuation.Basic

/-!
# The field of germs of meromorphic functions at a point, with its order valuation

Used for the finite fibres of $j : X_0(N) \to X_0(1)$ (J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2,
pdf p. 196): the conjugates of $\mathbb Q(X_0(N))$ are embedded into the field of meromorphic germs at a point
$\tau_0 \in \mathbb H$, and the order of vanishing at $\tau_0$ is the valuation used in `FibreCount.lean`.

`MeroGerm x` is the subring of germs along the punctured neighbourhood filter $\mathcal N_{\ne}(x)$ of functions
$\mathbb C \to \mathbb C$ meromorphic at $x$. It is a field (`MeroGerm.instField`): a meromorphic germ that is not
zero is eventually nonzero. The valuation `ordVal x` is $\exp(-\operatorname{ord}_x)$ (`ordVal_mk`).
-/

open Filter Topology
open scoped WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

variable (x : ℂ)

/-- Germs of functions $\mathbb C \to \mathbb C$ on a punctured neighbourhood of $x$. -/
abbrev PGerm : Type := (𝓝[≠] x).Germ ℂ

/-- The germs of functions meromorphic at $x$. -/
def meroSubring : Subring (PGerm x) where
  carrier := {g | ∃ f : ℂ → ℂ, MeromorphicAt f x ∧ (f : PGerm x) = g}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, MeromorphicAt.const 1 x, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, MeromorphicAt.const 0 x, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

/-- The ring of germs of meromorphic functions at $x$. -/
abbrev MeroGerm : Type := meroSubring x

variable {x}

namespace MeroGerm

/-- The germ of a function meromorphic at $x$. -/
def mk (f : ℂ → ℂ) (hf : MeromorphicAt f x) : MeroGerm x := ⟨(f : PGerm x), f, hf, rfl⟩

theorem exists_eq_mk (a : MeroGerm x) : ∃ f : ℂ → ℂ, ∃ hf : MeromorphicAt f x, a = mk f hf := by
  obtain ⟨_, f, hf, h⟩ := a
  exact ⟨f, hf, Subtype.ext h.symm⟩

theorem mk_eq_mk {f g : ℂ → ℂ} {hf : MeromorphicAt f x} {hg : MeromorphicAt g x} :
    mk f hf = mk g hg ↔ f =ᶠ[𝓝[≠] x] g := by
  rw [Subtype.ext_iff]
  exact Filter.Germ.coe_eq

theorem mk_mul (f g : ℂ → ℂ) (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    mk (f * g) (hf.mul hg) = mk f hf * mk g hg := rfl

theorem mk_add (f g : ℂ → ℂ) (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    mk (f + g) (hf.add hg) = mk f hf + mk g hg := rfl

theorem mk_sub (f g : ℂ → ℂ) (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    mk (f - g) (hf.sub hg) = mk f hf - mk g hg := rfl

theorem mk_neg (f : ℂ → ℂ) (hf : MeromorphicAt f x) : mk (-f) hf.neg = -mk f hf := rfl

theorem mk_one : mk (fun _ => (1 : ℂ)) (MeromorphicAt.const 1 x) = 1 := rfl

theorem mk_zero : mk (fun _ => (0 : ℂ)) (MeromorphicAt.const 0 x) = 0 := rfl

theorem mk_pow (f : ℂ → ℂ) (hf : MeromorphicAt f x) (n : ℕ) : mk (f ^ n) (hf.pow n) = mk f hf ^ n := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  exact Filter.Germ.coe_pow f n

theorem mk_eq_zero_iff {f : ℂ → ℂ} {hf : MeromorphicAt f x} : mk f hf = 0 ↔ f =ᶠ[𝓝[≠] x] 0 := by
  rw [← mk_zero, mk_eq_mk]
  rfl

theorem isField : IsField (MeroGerm x) where
  exists_pair_ne := ⟨0, 1, by
    rw [← mk_zero, ← mk_one, Ne, mk_eq_mk]
    intro h
    obtain ⟨y, hy⟩ := h.exists
    exact zero_ne_one hy⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    intro a ha
    obtain ⟨f, hf, rfl⟩ := exists_eq_mk a
    have hne : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := by
      rcases hf.eventually_eq_zero_or_eventually_ne_zero with h | h
      · exact absurd (mk_eq_zero_iff.2 h) ha
      · exact h
    refine ⟨mk f⁻¹ hf.inv, ?_⟩
    rw [← mk_mul, ← mk_one, mk_eq_mk]
    filter_upwards [hne] with y hy
    simp [hy]

instance instField : Field (MeroGerm x) := (isField (x := x)).toField

/-- The order of a germ (independent of the representative, `meromorphicOrderAt_congr`). -/
def ord (a : MeroGerm x) : WithTop ℤ :=
  Filter.Germ.liftOn a.1 (fun f => meromorphicOrderAt f x) fun _ _ h => meromorphicOrderAt_congr h

theorem ord_mk (f : ℂ → ℂ) (hf : MeromorphicAt f x) : ord (mk f hf) = meromorphicOrderAt f x := rfl

end MeroGerm

/-- $\exp(-n)$, with $\exp(-\top) = 0$. -/
def toVal (a : WithTop ℤ) : ℤᵐ⁰ := if h : a = ⊤ then 0 else WithZero.exp (-(a.untop h))

@[simp] theorem toVal_top : toVal ⊤ = 0 := by simp [toVal]

@[simp] theorem toVal_coe (n : ℤ) : toVal (n : WithTop ℤ) = WithZero.exp (-n) := by simp [toVal]

theorem toVal_add (a b : WithTop ℤ) : toVal (a + b) = toVal a * toVal b := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe m =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      rw [← WithTop.coe_add, toVal_coe, toVal_coe, toVal_coe, neg_add, WithZero.exp_add]

theorem toVal_antitone {a b : WithTop ℤ} (h : a ≤ b) : toVal b ≤ toVal a := by
  induction b using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    induction a using WithTop.recTopCoe with
    | top => simp at h
    | coe m =>
      rw [toVal_coe, toVal_coe, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast h

theorem toVal_min (a b : WithTop ℤ) : toVal (min a b) = max (toVal a) (toVal b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (toVal_antitone h)]
  · rw [min_eq_right h, max_eq_right (toVal_antitone h)]

theorem toVal_eq_exp {a : WithTop ℤ} {n : ℤ} : toVal a = WithZero.exp (-n) ↔ a = n := by
  induction a using WithTop.recTopCoe with
  | top =>
    simp only [toVal_top, WithTop.top_ne_coe, iff_false]
    exact fun h => WithZero.exp_ne_zero h.symm
  | coe m => simp

variable (x)

/-- **The order valuation** $\exp(-\operatorname{ord}_x)$ on `MeroGerm x`. -/
def ordVal : Valuation (MeroGerm x) ℤᵐ⁰ where
  toFun a := toVal (MeroGerm.ord a)
  map_zero' := by
    rw [← MeroGerm.mk_zero, MeroGerm.ord_mk, meromorphicOrderAt_eq_top_iff.2 (by simp), toVal_top]
  map_one' := by
    rw [← MeroGerm.mk_one, MeroGerm.ord_mk]
    have : meromorphicOrderAt (fun _ : ℂ => (1 : ℂ)) x = 0 := by
      rw [meromorphicOrderAt_const]
      simp
    rw [this]
    exact toVal_coe 0
  map_mul' a b := by
    obtain ⟨f, hf, rfl⟩ := MeroGerm.exists_eq_mk a
    obtain ⟨g, hg, rfl⟩ := MeroGerm.exists_eq_mk b
    rw [← MeroGerm.mk_mul, MeroGerm.ord_mk, MeroGerm.ord_mk, MeroGerm.ord_mk, meromorphicOrderAt_mul hf hg,
      toVal_add]
  map_add_le_max' a b := by
    obtain ⟨f, hf, rfl⟩ := MeroGerm.exists_eq_mk a
    obtain ⟨g, hg, rfl⟩ := MeroGerm.exists_eq_mk b
    rw [← MeroGerm.mk_add, MeroGerm.ord_mk, MeroGerm.ord_mk, MeroGerm.ord_mk, ← toVal_min]
    exact toVal_antitone (meromorphicOrderAt_add hf hg)

variable {x}

theorem ordVal_mk (f : ℂ → ℂ) (hf : MeromorphicAt f x) :
    ordVal x (MeroGerm.mk f hf) = toVal (meromorphicOrderAt f x) := rfl

/-- The valuation of an analytic germ of order $n$. -/
theorem ordVal_mk_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f x) {n : ℕ} (hn : analyticOrderAt f x = n) :
    ordVal x (MeroGerm.mk f hf.meromorphicAt) = WithZero.exp (-(n : ℤ)) := by
  rw [ordVal_mk, hf.meromorphicOrderAt_eq, hn]
  exact toVal_coe n

end NumberFieldKB.ModularCurves
