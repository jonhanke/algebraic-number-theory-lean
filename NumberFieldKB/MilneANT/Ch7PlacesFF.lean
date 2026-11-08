import NumberFieldKB.MilneANT.Ch7Places
import NumberFieldKB.WeilBNT.FunctionField.ProductFormula

/-!
# Milne, *Algebraic Number Theory*, Remark 7.17(a): the product formula for function fields over a finite field

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 7.17, p. 112; bib key `milne2020ant`.

**`remark7_17a`** proves the named statement `Remark7_17a k K` unconditionally, from the product formula of the
Weil track: `WeilBNT.FF.Divisor.deg_div_eq_zero` ($\deg\operatorname{div}\xi = 0$, Weil VI.§1, p. 97) and
`WeilBNT.FF.Place.weil_III_1_thm3_ff` ($|\xi|_v = 1$ for almost all $v$). A place of the Weil track
(`WeilBNT.FF.Place k K`) is a surjective valuation `K → ℤᵐ⁰` trivial on $k$; over a finite field every valuation is
trivial on $k$ (`Place.mk'`), so these are exactly Milne's primes. With $Nv = q^{\deg v}$
(`Place.card_residueField`) and $\log v(a) = -\operatorname{ord}_v(a)$:
$\prod_v Nv^{\log v(a)} = q^{-\sum_v \deg(v)\operatorname{ord}_v(a)} = q^{-\deg\operatorname{div}(a)} = 1$.
-/

open NumberFieldKB.WeilBNT.FF

namespace NumberFieldKB.MilneANT

noncomputable section

variable (k K : Type*) [Field k] [Finite k] [Field K] [Algebra (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

/-- The $k$-algebra structure of $K$ through $k(T)$. -/
@[reducible] def algebraOfRatFunc : Algebra k K :=
  ((algebraMap (RatFunc k) K).comp (algebraMap k (RatFunc k))).toAlgebra

/-- **Remark 7.17(a)** (proved, unconditionally): for a finite extension $K$ of $k(T)$, $k$ finite, the normalized
absolute values $|a|_v = Nv^{-\operatorname{ord}_v(a)}$ satisfy $|a|_v = 1$ for almost all $v$ and
$\prod_v |a|_v = 1$. -/
@[kb "milne2020ant" "v3.08, Remark 7.17, p. 112"]
theorem remark7_17a : Remark7_17a k K := by
  letI : Algebra k K := algebraOfRatFunc k K
  haveI : IsScalarTower k (RatFunc k) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FunctionField k K := inferInstance
  -- Milne's primes are the places of the Weil track
  let P : {v : Valuation K (WithZero (Multiplicative ℤ)) // Function.Surjective v} ≃ Place k K :=
    { toFun := fun v => Place.mk' v.1 v.2
      invFun := fun w => ⟨w.valuation, w.valuation_surjective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin : ∀ a : K, a ≠ 0 →
      {v : {v : Valuation K (WithZero (Multiplicative ℤ)) // Function.Surjective v} | v.1 a ≠ 1}.Finite := by
    intro a ha
    have h := Place.weil_III_1_thm3_ff (Fq := k) (k := K) ha
    refine (h.preimage P.injective.injOn).subset ?_
    intro v hv
    exact hv
  refine ⟨hfin, ?_⟩
  intro a ha
  set u : Kˣ := Units.mk0 a ha
  set S := (hfin a ha).toFinset
  set q : ℝ := (Nat.card k : ℝ)
  have hq : q ≠ 0 := by
    have : 0 < Nat.card k := Nat.card_pos
    simp only [q]
    positivity
  -- each factor is `q ^ (- deg v * ord_v a)`
  have hterm : ∀ v : {v : Valuation K (WithZero (Multiplicative ℤ)) // Function.Surjective v},
      (Nat.card (IsLocalRing.ResidueField v.1.valuationSubring) : ℝ) ^ (WithZero.log (v.1 a)) =
        q ^ (-((P v).degree : ℤ) * (P v).ord a) := by
    intro v
    have hc : Nat.card (IsLocalRing.ResidueField v.1.valuationSubring) = Nat.card k ^ (P v).degree :=
      Place.card_residueField (P v)
    rw [hc, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 1
    have h : (P v).valuation a = v.1 a := rfl
    simp only [Place.ord, h]
    ring
  classical
  have hzs : ∀ (T : Finset {v : Valuation K (WithZero (Multiplicative ℤ)) // Function.Surjective v})
      (f : {v : Valuation K (WithZero (Multiplicative ℤ)) // Function.Surjective v} → ℤ),
      ∏ v ∈ T, q ^ f v = q ^ (∑ v ∈ T, f v) := by
    intro T f
    induction T using Finset.induction_on with
    | empty => simp
    | insert a T ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hq, ih]
  rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
  · rw [Finset.prod_congr rfl (fun v _ => hterm v), hzs]
    have hdeg := Divisor.deg_div_eq_zero (Fq := k) (k := K) u
    have hsum : ∑ v ∈ S, -((P v).degree : ℤ) * (P v).ord a = -Divisor.deg (Divisor.div u : Divisor k K) := by
      have hsupp : (Divisor.div u : Divisor k K).support ⊆ S.map P.toEmbedding := by
        intro w hw
        rw [Finsupp.mem_support_iff, Divisor.div_apply] at hw
        simp only [Finset.mem_map_equiv, S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        intro h1
        apply hw
        have h2 : w.valuation (u : K) = 1 := h1
        simp [Place.ord, h2]
      rw [Divisor.deg, Finsupp.liftAddHom_apply, Finsupp.sum_of_support_subset _ hsupp]
      · rw [Finset.sum_map, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp [u, mul_comm]
      · intro w _
        simp
    rw [hsum, hdeg, neg_zero, zpow_zero]
  · intro v hv
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq, S]
    intro h1
    apply hv
    simp [h1]

end

end NumberFieldKB.MilneANT
