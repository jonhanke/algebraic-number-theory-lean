import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import QuadFormsKB.Citation
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Milne, Elliptic Curves, Chapter IV §11: the curve $X^{q+1} + Y^{q+1} + Z^{q+1} = 0$ over $\mathbb F_{q^2}$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 11 ("Elliptic curves and
sphere packings"), Lemma 11.3, pdf p. 178.  Locators give the pdf page of the text `ectext6`
(printed page = pdf page − 8).

$q$ is a power of the prime $p$ and $K$ is a field with $q^2$ elements.  Points of the projective plane over $K$ are
Mathlib's `Projectivization K (Fin 3 → K)`; a homogeneous equation is satisfied by one representative of a point if and
only if by all.

## Proved
* `lemma_11_3_a`: the curve $C : X^{q+1} + Y^{q+1} + Z^{q+1} = 0$ is nonsingular: its partial derivatives
  $X^q, Y^q, Z^q$ have no common zero in $\mathbb P^2$.  (The genus $q(q-1)/2$ is not formalized: Mathlib has no genus
  of a curve.)
* `lemma_11_3_b`: $\#C(\mathbb F_{q^2}) = q^3 + 1$.
-/

open MvPolynomial Finset

namespace NumberFieldKB.MilneEC

/-- The Fermat polynomial $X^{q+1} + Y^{q+1} + Z^{q+1}$ (pdf p. 178). -/
noncomputable def fermatPoly (K : Type*) [CommRing K] (q : ℕ) : MvPolynomial (Fin 3) K :=
  X 0 ^ (q + 1) + X 1 ^ (q + 1) + X 2 ^ (q + 1)

/-- Fibre sizes of the $(q+1)$-th power map on the unit group of a field with $q^2$ elements. -/
theorem units_pow_fiber_card (K : Type*) [Field K] [Fintype K] [DecidableEq K] (q : ℕ) (hq : 2 ≤ q)
    (hK : Fintype.card K = q ^ 2) (a : Kˣ) (ha : a ^ (q - 1) = 1) :
    #{u : Kˣ | u ^ (q + 1) = a} = q + 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have hqm : r + 2 - 1 = r + 1 := by omega
  rw [hqm] at ha
  set R : Finset Kˣ := univ.filter fun a : Kˣ => a ^ (r + 1) = 1 with hR
  let f : Kˣ →* Kˣ := powMonoidHom (r + 2 + 1)
  have hf : ∀ u, f u = u ^ (r + 2 + 1) := fun u => rfl
  have hcardU : Fintype.card Kˣ + 1 = (r + 2) ^ 2 := by
    rw [Fintype.card_units, ← hK]
    have : 0 < Fintype.card K := Fintype.card_pos
    omega
  set m := #{u : Kˣ | u ^ (r + 2 + 1) = 1} with hm
  have hm_le : m ≤ r + 3 := by
    have := IsCyclic.card_pow_eq_one_le (α := Kˣ) (n := r + 2 + 1) (by omega)
    simpa [hm] using this
  have hfib : ∀ b ∈ (univ : Finset Kˣ).image f, #{u : Kˣ | f u = b} = m := by
    intro b hb
    have := MonoidHom.card_fiber_eq_of_mem_range f (x := b) (y := 1) (by simpa using hb)
      ⟨1, map_one f⟩
    simpa [hm, hf] using this
  have hsum : Fintype.card Kˣ = #((univ : Finset Kˣ).image f) * m := by
    rw [Fintype.card, Finset.card_eq_sum_card_image f univ]
    rw [Finset.sum_congr rfl (fun b hb => by simpa using hfib b hb)]
    simp
  have hsub : (univ : Finset Kˣ).image f ⊆ R := by
    intro b hb
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hb
    rw [hR, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [hf, ← pow_mul]
    have h1 : u ^ Fintype.card Kˣ = 1 := pow_card_eq_one
    have h2 : (r + 2 + 1) * (r + 1) = Fintype.card Kˣ := by
      have : (r + 2) ^ 2 = (r + 2 + 1) * (r + 1) + 1 := by ring
      omega
    rw [h2, h1]
  have hRle : #R ≤ r + 1 := by
    have := IsCyclic.card_pow_eq_one_le (α := Kˣ) (n := r + 1) (by omega)
    simpa using this
  have hi := Finset.card_le_card hsub
  have hmeq : m = r + 3 := by
    by_contra h
    have h' : m ≤ r + 2 := by omega
    have := Nat.mul_le_mul (hi.trans hRle) h'
    nlinarith
  have hieq : #((univ : Finset Kˣ).image f) = r + 1 := by
    rw [hmeq] at hsum
    nlinarith
  have heq : (univ : Finset Kˣ).image f = R :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have haI : a ∈ (univ : Finset Kˣ).image f := by
    rw [heq]; simp [hR, ha]
  have := hfib a haI
  simpa [hf, hmeq] using this


/-- Counting the zeros of a homogeneous function on $K^3$ in terms of its zeros on the projective plane. -/
theorem fermat_proj_card (K : Type*) [Field K] [Fintype K] [DecidableEq K] (n : ℕ) (hn : 0 < n)
    (F : (Fin 3 → K) → K) (hF : ∀ (c : K) v, F (c • v) = c ^ n * F v) :
    Fintype.card {v : Fin 3 → K // F v = 0} =
      Nat.card {P : Projectivization K (Fin 3 → K) // F P.rep = 0} * (Fintype.card K - 1) + 1 := by
  classical
  have hmk : ∀ v : {v : Fin 3 → K // v ≠ 0},
      (Projectivization.nonZeroEquivProjectivizationProdUnits K (Fin 3 → K) v).1 =
        Projectivization.mk K v.1 v.2 := fun v => rfl
  have hF0 : F 0 = 0 := by
    have := hF 0 0
    simpa [zero_pow hn.ne'] using this
  have hmem : ∀ (v : Fin 3 → K) (hv : v ≠ 0),
      F (Projectivization.mk K v hv).rep = 0 ↔ F v = 0 := by
    intro v hv
    obtain ⟨a, ha⟩ := Projectivization.mk_eq_mk_iff K _ _ (Projectivization.rep_nonzero _) hv |>.mp
      (Projectivization.mk_rep (Projectivization.mk K v hv))
    rw [← ha, show ((a : Kˣ) • v) = (a : K) • v from rfl, hF]
    simp
  let e := Projectivization.nonZeroEquivProjectivizationProdUnits K (Fin 3 → K)
  have h1 : Fintype.card {v : Fin 3 → K // F v = 0} =
      Fintype.card {w : {v : Fin 3 → K // v ≠ 0} // F w.1 = 0} + 1 := by
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun v : Fin 3 → K => v ≠ 0)
      (fun v => F v = 0)), Fintype.card_subtype, Fintype.card_subtype]
    have : (univ : Finset (Fin 3 → K)).filter (fun v => F v = 0) =
        insert 0 (univ.filter (fun v => v ≠ 0 ∧ F v = 0)) := by
      ext v
      by_cases hv : v = 0
      · simp [hv, hF0]
      · simp [hv]
    rw [this, Finset.card_insert_of_notMem (by simp)]
  have h2 : Fintype.card {w : {v : Fin 3 → K // v ≠ 0} // F w.1 = 0} =
      Nat.card {P : Projectivization K (Fin 3 → K) // F P.rep = 0} * Fintype.card Kˣ := by
    have eq1 : {w : {v : Fin 3 → K // v ≠ 0} // F w.1 = 0} ≃
        {p : Projectivization K (Fin 3 → K) × Kˣ // F p.1.rep = 0} :=
      e.subtypeEquiv (fun w => by
        rw [hmk]; exact (hmem w.1 w.2).symm)
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (eq1.trans (Equiv.prodSubtypeFstEquivSubtypeProd
      (p := fun P : Projectivization K (Fin 3 → K) => F P.rep = 0))), Nat.card_prod,
      Nat.card_eq_fintype_card (α := Kˣ)]
  rw [h1, h2, Fintype.card_units]


/-- The fibres of $x \mapsto x^{q+1}$ on a field with $q^2$ elements. -/
theorem pow_succ_fiber_card (K : Type*) [Field K] [Fintype K] [DecidableEq K] (q : ℕ) (hq : 2 ≤ q)
    (hK : Fintype.card K = q ^ 2) (a : K) :
    #{x : K | x ^ (q + 1) = a} = if a ^ q = a then (if a = 0 then 1 else q + 1) else 0 := by
  have hsq : ∀ x : K, x ^ (q ^ 2) = x := fun x => by rw [← hK]; exact FiniteField.pow_card x
  by_cases h : a ^ q = a
  · simp only [h, ↓reduceIte]
    by_cases h0 : a = 0
    · subst h0
      simp only [↓reduceIte]
      have : (univ : Finset K).filter (fun x : K => x ^ (q + 1) = 0) = {0} := by
        ext x
        simp [pow_eq_zero_iff]
      rw [this]; simp
    · simp only [h0, ↓reduceIte]
      have ha : (Units.mk0 a h0) ^ (q - 1) = 1 := by
        apply mul_right_cancel (b := Units.mk0 a h0)
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul]
        exact Units.ext (by simpa using h)
      refine Eq.trans ?_ (units_pow_fiber_card K q hq hK _ ha)
      symm
      apply Finset.card_bij (fun (u : Kˣ) _ => (u : K))
      · intro u hu
        simp only [mem_filter, mem_univ, true_and] at hu ⊢
        rw [← Units.val_pow_eq_pow_val, hu]; rfl
      · intro u _ w _ huw; exact Units.ext huw
      · intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        have hx0 : x ≠ 0 := by rintro rfl; simp at hx; exact h0 hx.symm
        refine ⟨Units.mk0 x hx0, ?_, rfl⟩
        simp only [mem_filter, mem_univ, true_and]
        exact Units.ext (by simpa using hx)
  · simp only [h, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    apply h
    rw [← hx]
    have : (x ^ (q + 1)) ^ q = x ^ (q + 1) := by
      calc (x ^ (q + 1)) ^ q = x ^ (q ^ 2) * x ^ q := by rw [← pow_mul, ← pow_add]; congr 1; ring
        _ = x ^ (q + 1) := by rw [hsq, pow_succ']
    exact this


/-- Evaluation of the triple sum over a finite set closed under negation, where the summand is the number of
preimages under $x \mapsto x^{q+1}$. -/
theorem fermat_final_sum (K : Type*) [Field K] [DecidableEq K] (F : Finset K) (q : ℕ)
    (h0 : (0 : K) ∈ F) (hneg : ∀ a ∈ F, -a ∈ F) (hc : #F = q) :
    ∑ a ∈ F, ∑ b ∈ F, (((q : ℤ) + 1) - q * (if a = 0 then 1 else 0)) *
      (((q : ℤ) + 1) - q * (if b = 0 then 1 else 0)) *
      (((q : ℤ) + 1) - q * (if -(a + b) = 0 then 1 else 0)) = (q : ℤ) ^ 5 - q ^ 3 + q ^ 2 := by
  have i0 : ∑ a ∈ F, (if a = 0 then (1 : ℤ) else 0) = 1 := by simp [h0]
  have i1 : ∀ a ∈ F, ∑ b ∈ F, (if -(a + b) = 0 then (1 : ℤ) else 0) = 1 := by
    intro a ha
    have : ∀ b : K, (-(a + b) = 0) ↔ (b = -a) := fun b => by
      rw [neg_eq_zero, add_eq_zero_iff_eq_neg']
    simp_rw [this]
    rw [Finset.sum_ite_eq']
    simp [hneg a ha]
  have i2 : ∀ a ∈ F, ∑ b ∈ F, (if b = 0 then (1 : ℤ) else 0) * (if -(a + b) = 0 then 1 else 0) =
      if a = 0 then 1 else 0 := by
    intro a ha
    rw [Finset.sum_eq_single (0 : K)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd h0 h
  have step : ∀ a ∈ F, ∑ b ∈ F, (((q : ℤ) + 1) - q * (if a = 0 then 1 else 0)) *
      (((q : ℤ) + 1) - q * (if b = 0 then 1 else 0)) *
      (((q : ℤ) + 1) - q * (if -(a + b) = 0 then 1 else 0)) =
      ((q : ℤ) + 1) ^ 3 * q - ((q : ℤ) + 1) ^ 2 * q * ((if a = 0 then 1 else 0) * q + 1 + 1)
        + ((q : ℤ) + 1) * q ^ 2 * (2 * (if a = 0 then 1 else 0) + (if a = 0 then 1 else 0))
        - q ^ 3 * (if a = 0 then 1 else 0) := by
    intro a ha
    have e : ∀ b : K, (((q : ℤ) + 1) - q * (if a = 0 then 1 else 0)) *
      (((q : ℤ) + 1) - q * (if b = 0 then 1 else 0)) *
      (((q : ℤ) + 1) - q * (if -(a + b) = 0 then 1 else 0)) =
      ((q : ℤ) + 1) ^ 3 - ((q : ℤ) + 1) ^ 2 * q * (if a = 0 then 1 else 0)
        - ((q : ℤ) + 1) ^ 2 * q * (if b = 0 then 1 else 0)
        - ((q : ℤ) + 1) ^ 2 * q * (if -(a + b) = 0 then 1 else 0)
        + (((q : ℤ) + 1) * q ^ 2 * (if a = 0 then 1 else 0)) * (if b = 0 then 1 else 0)
        + (((q : ℤ) + 1) * q ^ 2 * (if a = 0 then 1 else 0)) * (if -(a + b) = 0 then 1 else 0)
        + ((q : ℤ) + 1) * q ^ 2 * ((if b = 0 then 1 else 0) * (if -(a + b) = 0 then 1 else 0))
        - (q ^ 3 * (if a = 0 then 1 else 0)) *
          ((if b = 0 then 1 else 0) * (if -(a + b) = 0 then 1 else 0)) := fun b => by ring
    rw [Finset.sum_congr rfl (fun b _ => e b)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
      i0, i1 a ha, i2 a ha, hc, nsmul_eq_mul]
    by_cases hz : a = 0 <;> simp [hz] <;> ring
  rw [Finset.sum_congr rfl step]
  have i0' : ∑ x ∈ F, (if x = 0 then (1 : ℤ) else 0) * q = q := by
    rw [← Finset.sum_mul, i0, one_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, i0', ← Finset.mul_sum,
      i0, hc, nsmul_eq_mul]
  ring


/-- **Lemma 11.3(a)** (pdf p. 178), nonsingularity: in characteristic $p$ with $q$ a power of $p$, the partial
derivatives of $X^{q+1} + Y^{q+1} + Z^{q+1}$ (namely $X^q, Y^q, Z^q$) vanish simultaneously only at $(0, 0, 0)$, so
$C$ has no singular point in $\mathbb P^2(K)$, for every field $K$ of characteristic $p$. -/
@[kb "milne2006ec" "Ch. IV, Lemma 11.3(a), pdf p. 178"]
theorem lemma_11_3_a (p : ℕ) [Fact p.Prime] (e : ℕ) (he : 1 ≤ e) (K : Type*) [Field K] [CharP K p] (v : Fin 3 → K)
    (hv : ∀ i, eval v (pderiv i (fermatPoly K (p ^ e))) = 0) : v = 0:= by
  have he0 : e ≠ 0 := by omega
  funext i
  have h := hv i
  have hd : ∀ j : Fin 3, pderiv i (X j ^ (p ^ e + 1) : MvPolynomial (Fin 3) K) =
      if i = j then X j ^ (p ^ e) else 0 := by
    intro j
    rw [Derivation.leibniz_pow, pderiv_X]
    by_cases hij : i = j
    · subst hij
      simp [he0]
    · simp [hij]
  simp only [fermatPoly, map_add, hd] at h
  fin_cases i <;> simp [he0] at h ⊢ <;> exact h.1


/-- Summing a function of the $n$-th power over a finite field, grouped by the value of the power. -/
theorem sum_pow_fiber (K : Type*) [Field K] [Fintype K] [DecidableEq K] (n : ℕ) (h : K → ℤ) :
    ∑ x : K, h (x ^ n) = ∑ a : K, (#{x : K | x ^ n = a} : ℤ) * h a := by
  rw [← Finset.sum_fiberwise univ (fun x : K => x ^ n) (fun x => h (x ^ n))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2] : ∀ x ∈ univ.filter
    (fun x : K => x ^ n = a), h (x ^ n) = h a)]
  simp

/-- **Lemma 11.3(b)** (pdf p. 178): for $q$ a power of $p$ and $K$ a field with $q^2$ elements, the curve
$X^{q+1} + Y^{q+1} + Z^{q+1} = 0$ has exactly $q^3 + 1$ points in $\mathbb P^2(K)$. -/
@[kb "milne2006ec" "Ch. IV, Lemma 11.3(b), pdf p. 178"]
theorem lemma_11_3_b (p : ℕ) [Fact p.Prime] (e : ℕ) (he : 1 ≤ e) (K : Type*) [Field K] [Fintype K] [CharP K p]
    (hK : Fintype.card K = (p ^ e) ^ 2) :
    Nat.card {P : Projectivization K (Fin 3 → K) // eval P.rep (fermatPoly K (p ^ e)) = 0} = (p ^ e) ^ 3 + 1:= by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : 2 ≤ p ^ e := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  generalize hqdef : p ^ e = q at hq2 hK ⊢
  -- the Frobenius fixed points
  let φ := iterateFrobenius K p e
  have hφ : ∀ x : K, φ x = x ^ q := fun x => by rw [iterateFrobenius_def, hqdef]
  set F : Finset K := univ.filter fun a : K => a ^ q = a with hFdef
  have h0 : (0 : K) ∈ F := by simp [hFdef, zero_pow (by omega : q ≠ 0)]
  have hneg : ∀ a ∈ F, -a ∈ F := by
    intro a ha
    simp only [hFdef, mem_filter, mem_univ, true_and] at ha ⊢
    rw [← hφ, map_neg, hφ, ha]
  have hadd : ∀ a ∈ F, ∀ b ∈ F, -(a + b) ∈ F := by
    intro a ha b hb
    apply hneg
    simp only [hFdef, mem_filter, mem_univ, true_and] at ha hb ⊢
    rw [← hφ, map_add, hφ, hφ, ha, hb]
  have hfib := pow_succ_fiber_card K q hq2 hK
  have hcF : #F = q := by
    have h1 : Fintype.card K = ∑ a : K, #{x : K | x ^ (q + 1) = a} := by
      rw [Fintype.card, Finset.card_eq_sum_card_fiberwise (f := fun x : K => x ^ (q + 1))
        (t := univ) (fun _ _ => mem_univ _)]
    simp_rw [hfib] at h1
    have h2 : ∑ a : K, (if a ^ q = a then (if a = 0 then 1 else q + 1) else 0) =
        ∑ a ∈ F, (if a = 0 then 1 else q + 1) := by
      rw [hFdef, Finset.sum_filter]
    rw [h2, ← Finset.add_sum_erase F _ h0, hK] at h1
    rw [Finset.sum_congr rfl (fun x hx => by
      simp [(Finset.mem_erase.1 hx).1] : ∀ x ∈ F.erase 0, (if x = 0 then 1 else q + 1) = q + 1)]
      at h1
    simp only [ite_true, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h0] at h1
    have hc : 1 ≤ #F := Finset.card_pos.2 ⟨0, h0⟩
    have : #F * (q + 1) = q * (q + 1) := by
      zify [hc] at h1 ⊢
      nlinarith
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  -- the fibre sizes, as integers
  have hfibF : ∀ a : K, a ∉ F → (#{x : K | x ^ (q + 1) = a} : ℤ) = 0 := by
    intro a ha
    have : ¬ a ^ q = a := by simpa [hFdef] using ha
    simp [hfib a, this]
  have hfibT : ∀ a ∈ F, (#{x : K | x ^ (q + 1) = a} : ℤ) =
      ((q : ℤ) + 1) - q * (if a = 0 then 1 else 0) := by
    intro a ha
    have : a ^ q = a := by simpa [hFdef] using ha
    by_cases h0a : a = 0
    · rw [hfib a]; simp [h0a]; omega
    · rw [hfib a]; simp [this, h0a]
  let F' : (Fin 3 → K) → K := fun v => eval v (fermatPoly K q)
  have hhom : ∀ (c : K) v, F' (c • v) = c ^ (q + 1) * F' v := by
    intro c v
    simp only [F', fermatPoly, map_add, map_pow, eval_X, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  have hproj := fermat_proj_card K (q + 1) (by omega) F' hhom
  let e3 : (Fin 3 → K) ≃ K × K × K :=
    { toFun := fun v => (v 0, v 1, v 2)
      invFun := fun t => ![t.1, t.2.1, t.2.2]
      left_inv := fun v => by funext i; fin_cases i <;> rfl
      right_inv := fun t => rfl }
  have hF'e : ∀ x y z : K, F' (e3.symm (x, y, z)) = x ^ (q + 1) + y ^ (q + 1) + z ^ (q + 1) := by
    intro x y z
    show F' ![x, y, z] = _
    simp [F', fermatPoly]
  have hcount : (Fintype.card {v : Fin 3 → K // F' v = 0} : ℤ) = (q : ℤ) ^ 5 - q ^ 3 + q ^ 2 := by
    rw [Fintype.card_subtype, Finset.card_filter]
    push_cast
    rw [← Equiv.sum_comp e3.symm]
    simp only [Fintype.sum_prod_type, hF'e]
    have e1 : ∀ x y : K, ∑ z : K, (if x ^ (q + 1) + y ^ (q + 1) + z ^ (q + 1) = 0 then (1 : ℤ) else 0) =
        (#{z : K | z ^ (q + 1) = -(x ^ (q + 1) + y ^ (q + 1))} : ℤ) := by
      intro x y
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      have : x ^ (q + 1) + y ^ (q + 1) + z ^ (q + 1) = 0 ↔
          z ^ (q + 1) = -(x ^ (q + 1) + y ^ (q + 1)) := by
        rw [eq_neg_iff_add_eq_zero, add_comm (z ^ (q + 1))]
      simp only [this]
    simp_rw [e1]
    have e2 : ∑ x : K, ∑ y : K, (#{z : K | z ^ (q + 1) = -(x ^ (q + 1) + y ^ (q + 1))} : ℤ) =
        ∑ a : K, ∑ b : K, (#{x : K | x ^ (q + 1) = a} : ℤ) * ((#{x : K | x ^ (q + 1) = b} : ℤ) *
          (#{x : K | x ^ (q + 1) = -(a + b)} : ℤ)) := by
      rw [sum_pow_fiber K (q + 1) (fun a => ∑ y : K,
        (#{z : K | z ^ (q + 1) = -(a + y ^ (q + 1))} : ℤ))]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [sum_pow_fiber K (q + 1) (fun b => (#{z : K | z ^ (q + 1) = -(a + b)} : ℤ)),
        Finset.mul_sum]
    rw [e2]
    have e3' : ∀ a : K, ∑ b : K, (#{x : K | x ^ (q + 1) = a} : ℤ) *
        ((#{x : K | x ^ (q + 1) = b} : ℤ) * (#{x : K | x ^ (q + 1) = -(a + b)} : ℤ)) =
        ∑ b ∈ F, (#{x : K | x ^ (q + 1) = a} : ℤ) *
        ((#{x : K | x ^ (q + 1) = b} : ℤ) * (#{x : K | x ^ (q + 1) = -(a + b)} : ℤ)) := by
      intro a
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      rw [hfibF b hb]; simp
    simp_rw [e3']
    rw [← Finset.sum_subset (Finset.subset_univ F) (fun a _ ha => by
      rw [Finset.sum_eq_zero]
      intro b _
      rw [hfibF a ha]; simp)]
    rw [← fermat_final_sum K F q h0 hneg hcF]
    refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
    rw [hfibT a ha, hfibT b hb, hfibT _ (hadd a ha b hb)]
    simp only [neg_eq_zero]
    ring
  have hKcast : (Fintype.card K : ℤ) = (q : ℤ) ^ 2 := by exact_mod_cast hK
  have hKpos : 1 ≤ Fintype.card K := Fintype.card_pos
  have hcast : ((Nat.card {P : Projectivization K (Fin 3 → K) // eval P.rep (fermatPoly K q) = 0} : ℕ) : ℤ)
      * ((q : ℤ) ^ 2 - 1) + 1 = (q : ℤ) ^ 5 - q ^ 3 + q ^ 2 := by
    rw [← hcount, hproj]
    push_cast [Nat.cast_sub hKpos, hKcast]
    rfl
  have hq1 : ((q : ℤ) ^ 2 - 1) ≠ 0 := by
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq2
    nlinarith
  have : ((Nat.card {P : Projectivization K (Fin 3 → K) // eval P.rep (fermatPoly K q) = 0} : ℕ) : ℤ)
      = (q : ℤ) ^ 3 + 1 := by
    apply mul_right_cancel₀ hq1
    linear_combination hcast
  exact_mod_cast this


end NumberFieldKB.MilneEC
