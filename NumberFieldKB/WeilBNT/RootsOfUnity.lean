import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, Chapter IV, §4, Theorem 8

Let $k$ be a number field, $F$ the set of $e\in k$ with $\lvert e\rvert_v\le1$ at every place $v$, and $E=F\setminus\{0\}$.
Weil's Theorem 8 (p. 77): $E$ is a finite cyclic group consisting of all the roots of unity in $k$.

* **`integralEverywhere K`**: the set $F$ (at the infinite places $w(e)\le1$, at the finite places $v(e)\le1$);
* **`weil_IV_4_thm8_finite`**: $F$ is finite;
* **`weil_IV_4_thm8_rootsOfUnity`**: for $e\ne0$, $e\in F$ if and only if $e^n=1$ for some $n>0$.

(Cyclicity of the finite group of roots of unity of a field is Mathlib's `rootsOfUnity.isCyclic`.)

Weil's proof of finiteness: $F$ is $k$ intersected with the compact set $\prod_v\{\lvert x_v\rvert_v\le1\}$ of
$k_{\mathbb A}$, and $k$ is discrete in $k_{\mathbb A}$. Below, the finite places cut $F$ down to the ring of integers
$\mathfrak r = k\cap\prod_v r_v$ (`mem_integers_of_valuation_le_one`), and the remaining infinite-place statement is
Mathlib's `Embeddings.finite_of_norm_le` (the discreteness of $\mathfrak r$ in $k_\infty$, the same compactness-discreteness
argument). Then $E$ is a finite set stable under multiplication in the group $k^\times$, so every element has finite order;
conversely a root of unity has $\lvert e\rvert_v=1$ everywhere.
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.WeilBNT

variable (K : Type*) [Field K] [NumberField K]

/-- Weil's set $F$: the elements of $k$ with $\lvert e\rvert_v\le1$ at every place $v$ of $k$. -/
def integralEverywhere : Set K :=
  {e | (∀ w : InfinitePlace K, w e ≤ 1) ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K e ≤ 1}

variable {K}

theorem mul_mem_integralEverywhere {a b : K} (ha : a ∈ integralEverywhere K) (hb : b ∈ integralEverywhere K) :
    a * b ∈ integralEverywhere K := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · rw [map_mul]
    calc w a * w b ≤ 1 * 1 := mul_le_mul (ha.1 w) (hb.1 w) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  · rw [map_mul]
    exact mul_le_one' (ha.2 v) (hb.2 v)

theorem one_mem_integralEverywhere : (1 : K) ∈ integralEverywhere K :=
  ⟨fun w => by simp, fun v => by simp⟩

/-- **Weil, IV.§4, Theorem 8, finiteness**: only finitely many $e\in k$ satisfy $\lvert e\rvert_v\le1$ at every place. -/
@[kb "weil1973bnt" "Ch. IV, §4, Thm. 8 (p. 77), number field case"]
theorem weil_IV_4_thm8_finite : (integralEverywhere K).Finite := by
  refine (Embeddings.finite_of_norm_le K ℂ 1).subset fun e he => ⟨?_, fun φ => ?_⟩
  · obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K e he.2
    exact (RingOfIntegers.isIntegral r).algebraMap
  · have := he.1 (InfinitePlace.mk φ)
    rwa [InfinitePlace.apply] at this

/-- **Weil, IV.§4, Theorem 8, roots of unity**: a nonzero $e\in k$ has $\lvert e\rvert_v\le1$ at every place if and only
if it is a root of unity. -/
@[kb "weil1973bnt" "Ch. IV, §4, Thm. 8 (p. 77), number field case"]
theorem weil_IV_4_thm8_rootsOfUnity {e : K} (he : e ≠ 0) :
    e ∈ integralEverywhere K ↔ ∃ n : ℕ, 0 < n ∧ e ^ n = 1 := by
  constructor
  · intro hF
    set u : Kˣ := Units.mk0 e he
    have hpow : ∀ n : ℕ, ((u ^ n : Kˣ) : K) ∈ integralEverywhere K := by
      intro n
      induction n with
      | zero => simpa using one_mem_integralEverywhere
      | succ k ih => rw [pow_succ, Units.val_mul]; exact mul_mem_integralEverywhere ih hF
    have hfin : (Submonoid.powers u : Set Kˣ).Finite := by
      refine (weil_IV_4_thm8_finite.preimage Units.val_injective.injOn).subset ?_
      rintro _ ⟨n, rfl⟩
      exact hpow n
    obtain ⟨n, hn, hun⟩ := isOfFinOrder_iff_pow_eq_one.mp (finite_powers.mp hfin)
    refine ⟨n, hn, ?_⟩
    have := congrArg Units.val hun
    simpa [u] using this
  · rintro ⟨n, hn, hen⟩
    refine ⟨fun w => ?_, fun v => ?_⟩
    · have h : w e ^ n = 1 := by rw [← map_pow, hen, map_one]
      exact ((pow_eq_one_iff_of_nonneg (by positivity) hn.ne').mp h).le
    · have h : v.valuation K e ^ n = 1 := by rw [← map_pow, hen, map_one]
      by_contra hlt
      push Not at hlt
      have := one_lt_pow' hlt hn.ne'
      rw [h] at this
      exact lt_irrefl _ this

end NumberFieldKB.WeilBNT
