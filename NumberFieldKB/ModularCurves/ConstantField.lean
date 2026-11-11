import NumberFieldKB.ModularCurves.PlaneModel
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# $\mathbb Q$ is the exact constant field of $\mathbb Q(j, j_N)$
J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §2 (pdf pp. 193–195): $X_0(N)$ is a curve over $\mathbb Q$,
i.e. $\mathbb Q$ is algebraically closed in its function field $\mathbb Q(X_0(N)) = \mathbb Q(j, j_N)$ (equivalently the
curve is geometrically irreducible). We prove this in the analytic model, where an element of $\mathbb Q(j, j_N)$ is a
quotient $P(j, j_N)/Q(j, j_N)$ of functions on $\mathbb H$ with $P, Q \in \mathbb Q[X, Y]$ and $Q(j, j_N) \ne 0$:

* `exists_eq_smul_of_algebraic`: if $P/Q$ is a root of a nonzero $p \in \mathbb Q[T]$ (in the homogeneous form
  $\sum_i p_i P^i Q^{d - i} = 0$, $d = \deg p$, which avoids division), then $P = c\,Q$ for a constant $c \in \mathbb C$
  (holomorphic functions on $\mathbb H$ have no zero divisors);
* `rat_of_eval_eq_smul`: if $P(j, j_N) = c\,Q(j, j_N)$ with $c \in \mathbb C$ and $Q(j, j_N) \ne 0$, then
  $c \in \mathbb Q$ (from Proposition 2.4: $F_N \in \mathbb Q[X][Y]$ generates the ideal of $(j, j_N)$ over $\mathbb C$);
* `algebraic_eq_rat_smul`: the two together.
-/

open UpperHalfPlane hiding I
open Polynomial
open scoped Manifold

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable {N : ℕ}

theorem mdiff_prod {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (hf : ∀ i ∈ s, MDiff (f i)) :
    MDiff (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact mdifferentiable_const
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A finite product of holomorphic functions on $\mathbb H$ vanishes only if a factor does. -/
theorem exists_eq_zero_of_prod_eq_zero {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (hf : ∀ i ∈ s, MDiff (f i))
    (h0 : ∏ i ∈ s, f i = 0) : ∃ i ∈ s, f i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exfalso
    have := congrFun h0 UpperHalfPlane.I
    simp at this
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h0
    have hprod : MDiff (∏ i ∈ s, f i) := mdiff_prod s f fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rcases mdiff_mul_eq_zero (hf a (Finset.mem_insert_self a s)) hprod h0 with h | h
    · exact ⟨a, Finset.mem_insert_self a s, h⟩
    · obtain ⟨i, hi, hi0⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) h
      exact ⟨i, Finset.mem_insert_of_mem hi, hi0⟩

/-- **Algebraic elements of $\mathbb C(j, j_N)$ are constant.** If $P/Q$ is a root of the nonzero polynomial
$p \in \mathbb Q[T]$ of degree $d$, in the form $\sum_i p_i P^i Q^{d-i} = 0$, then $P = cQ$ for some $c \in \mathbb C$. -/
theorem exists_eq_smul_of_algebraic (hN : 1 ≤ N) (P Q : ℚ[X][X]) (p : ℚ[X]) (hp : p ≠ 0)
    (hroot : ∑ i ∈ Finset.range (p.natDegree + 1),
      (p.coeff i : ℂ) • (evalJJNRat N P ^ i * evalJJNRat N Q ^ (p.natDegree - i)) = 0) :
    ∃ c : ℂ, evalJJNRat N P = c • evalJJNRat N Q := by
  set A := evalJJNRat N P
  set B := evalJJNRat N Q
  set d := p.natDegree
  set pc := p.map (algebraMap ℚ ℂ)
  have hpc : pc ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).2 hp
  have hdc : pc.natDegree = d := natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective p
  have hz : ∀ z, ∑ i ∈ Finset.range (d + 1), (p.coeff i : ℂ) * (A z ^ i * B z ^ (d - i)) = 0 := by
    intro z
    have := congrFun hroot z
    simpa [Finset.sum_apply] using this
  -- `p` has positive degree, so it has a complex root
  have hd : 0 < d := by
    by_contra hd0
    have hd0 : d = 0 := by omega
    have := hz UpperHalfPlane.I
    rw [hd0] at this
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, Nat.sub_self] at this
    have hc0 : p.coeff 0 = 0 := by exact_mod_cast this
    apply hp
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd0, hc0, map_zero]
  obtain ⟨r0, hr0⟩ := Complex.exists_root (f := pc) (by
    rw [degree_eq_natDegree hpc, hdc]; exact_mod_cast hd)
  have hr0mem : r0 ∈ pc.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hpc]; exact hr0
  have hprod : ∏ r ∈ pc.roots.toFinset, (fun z => A z - r * B z) = 0 := by
    funext z
    rw [Finset.prod_apply, Pi.zero_apply]
    by_cases hB : B z = 0
    · -- only the term `i = d` survives
      have h1 := hz z
      rw [Finset.sum_eq_single d] at h1
      · rw [hB, Nat.sub_self, pow_zero, mul_one] at h1
        have hlc : (p.coeff d : ℂ) ≠ 0 := by
          exact_mod_cast (show p.coeff d ≠ 0 from leadingCoeff_ne_zero.2 hp)
        have hA : A z = 0 := pow_eq_zero_iff (n := d) (by omega) |>.1 ((mul_eq_zero.1 h1).resolve_left hlc)
        exact Finset.prod_eq_zero hr0mem (by rw [hA, hB]; ring)
      · intro i hi hid
        have : i < d := by rw [Finset.mem_range] at hi; omega
        rw [hB, zero_pow (by omega), mul_zero, mul_zero]
      · intro hd'; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self d)) hd'
    · have heval : pc.eval (A z / B z) = 0 := by
        have h1 := hz z
        rw [eval_eq_sum_range, hdc]
        have : ∑ i ∈ Finset.range (d + 1), pc.coeff i * (A z / B z) ^ i =
            (∑ i ∈ Finset.range (d + 1), (p.coeff i : ℂ) * (A z ^ i * B z ^ (d - i))) / B z ^ d := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hid : i ≤ d := by rw [Finset.mem_range] at hi; omega
          rw [coeff_map, eq_ratCast, div_pow]
          have : B z ^ d = B z ^ i * B z ^ (d - i) := by rw [← pow_add, Nat.add_sub_cancel' hid]
          rw [this]
          field_simp
        rw [this, h1, zero_div]
      have hmem : A z / B z ∈ pc.roots.toFinset := by
        rw [Multiset.mem_toFinset, mem_roots hpc]; exact heval
      exact Finset.prod_eq_zero hmem (by field_simp; ring)
  have hmd : ∀ r ∈ pc.roots.toFinset, MDiff (fun z => A z - r * B z) := fun r _ =>
    (mdifferentiable_evalJJNHom _ hN P).sub (mdifferentiable_const.mul (mdifferentiable_evalJJNHom _ hN Q))
  obtain ⟨r, -, hr⟩ := exists_eq_zero_of_prod_eq_zero _ _ hmd hprod
  refine ⟨r, funext fun z => ?_⟩
  have := congrFun hr z
  simp only [Pi.zero_apply, sub_eq_zero] at this
  simpa using this

/-- **Constants of $\mathbb Q(j, j_N)$ are rational.** If $P(j, j_N) = c\,Q(j, j_N) \ne 0$ with $c \in \mathbb C$ and
$P, Q \in \mathbb Q[X][Y]$, then $c \in \mathbb Q$. -/
theorem rat_of_eval_eq_smul (h : Prop2_4 N) (P Q : ℚ[X][X]) (c : ℂ) (hQ : evalJJNRat N Q ≠ 0)
    (hPQ : evalJJNRat N P = c • evalJJNRat N Q) : ∃ q : ℚ, (q : ℂ) = c := by
  have hm := modPolyQ_monic h
  have hdiv := h.exists_poly.choose_spec.2.2.2
  set F := modPolyQ h
  set ι : ℚ[X] →+* ℂ[X] := mapRingHom (algebraMap ℚ ℂ)
  have hinj : Function.Injective ι := by
    simp only [ι, coe_mapRingHom]; exact map_injective _ (algebraMap ℚ ℂ).injective
  have hF : evalJJNRat N F = 0 := by
    rw [← RingHom.mem_ker, ker_evalJJNRat h]; exact Ideal.subset_span rfl
  have hred : ∀ G : ℚ[X][X], evalJJNRat N (G %ₘ F) = evalJJNRat N G := fun G => by
    conv_rhs => rw [← modByMonic_add_div G F]
    rw [map_add, map_mul, hF, zero_mul, add_zero]
  set P0 := P %ₘ F
  set Q0 := Q %ₘ F
  have hP0 : evalJJNRat N P0 = evalJJNRat N P := hred P
  have hQ0' : evalJJNRat N Q0 = evalJJNRat N Q := hred Q
  have hQ0 : Q0 ≠ 0 := fun h0 => hQ (by rw [← hQ0', h0, map_zero])
  -- evaluation over ℂ, compared with the rational evaluation
  have hC : ∀ (G : ℂ[X][X]) (z : ℍ), evalJJN N G z = evalJJNC N G z := fun G z => by
    rw [evalJJNHom_apply, mapRingHom_id, Polynomial.map_id]
  have hCR : ∀ (G : ℚ[X][X]) (z : ℍ), evalJJNC N (G.map ι) z = evalJJNRat N G z := fun G z => by
    rw [← hC, ← evalJJNHom_apply]
  set G : ℂ[X][X] := P0.map ι - C (C c) * Q0.map ι
  have hG : ∀ z, evalJJN N G z = 0 := fun z => by
    rw [hC]
    simp only [G, map_sub, map_mul, Pi.sub_apply, Pi.mul_apply, hCR]
    rw [hP0, hQ0']
    have := congrFun hPQ z
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    simp [evalJJNHom]
  have hdeg : G.degree < (F.map ι).degree := by
    rw [degree_map_eq_of_injective hinj]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · rw [degree_map_eq_of_injective hinj]; exact degree_modByMonic_lt _ hm
    · rw [← smul_eq_C_mul]
      refine lt_of_le_of_lt (degree_smul_le _ _) ?_
      rw [degree_map_eq_of_injective hinj]; exact degree_modByMonic_lt _ hm
  have hG0 : G = 0 := eq_zero_of_dvd_of_degree_lt (hdiv G hG) hdeg
  obtain ⟨i, hi⟩ : ∃ i, Q0.coeff i ≠ 0 := by
    by_contra! H
    exact hQ0 (Polynomial.ext (by simpa using H))
  obtain ⟨k, hk⟩ : ∃ k, (Q0.coeff i).coeff k ≠ 0 := by
    by_contra! H
    exact hi (Polynomial.ext (by simpa using H))
  have hcoef := congrArg (fun G : ℂ[X][X] => (G.coeff i).coeff k) hG0
  simp only [G, coeff_sub, coeff_C_mul, coeff_map, ι, coe_mapRingHom, coeff_zero] at hcoef
  rw [sub_eq_zero] at hcoef
  refine ⟨(P0.coeff i).coeff k / (Q0.coeff i).coeff k, ?_⟩
  have hk' : (((Q0.coeff i).coeff k : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hk
  push_cast
  rw [div_eq_iff hk']
  simpa using hcoef

/-- **$\mathbb Q$ is algebraically closed in $\mathbb Q(j, j_N) = \mathbb Q(X_0(N))$** (Milne V §2: $X_0(N)$ is a
curve over $\mathbb Q$, geometrically irreducible): an element $P(j, j_N)/Q(j, j_N)$ algebraic over $\mathbb Q$ is a
rational number. -/
@[kb "milne2006ec" "Ch. V, §2, Q is algebraically closed in Q(j, j_N) (X_0(N) is a curve over Q), pdf p. 195"]
theorem algebraic_eq_rat_smul (h : Prop2_4 N) (hN : 1 ≤ N) (P Q : ℚ[X][X]) (hQ : evalJJNRat N Q ≠ 0)
    (p : ℚ[X]) (hp : p ≠ 0)
    (hroot : ∑ i ∈ Finset.range (p.natDegree + 1),
      (p.coeff i : ℂ) • (evalJJNRat N P ^ i * evalJJNRat N Q ^ (p.natDegree - i)) = 0) :
    ∃ q : ℚ, evalJJNRat N P = (q : ℂ) • evalJJNRat N Q := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_algebraic hN P Q p hp hroot
  obtain ⟨q, rfl⟩ := rat_of_eval_eq_smul h P Q c hQ hc
  exact ⟨q, hc⟩

end NumberFieldKB.ModularCurves
