import NumberFieldKB.MilneEC.Ch4IsogenyDescent
import NumberFieldKB.MilneEC.Ch4Lemma21

/-!
# Proposition 8.2, the Tate-Shafarevich part (Milne, *Elliptic Curves*, Ch. IV, Proposition 8.2, pdf p. 152)

For a prime $p \equiv 1 \pmod 8$ such that $2$ is not a fourth power modulo $p$, the curve
$E : Y^2 = X^3 + pX$ has rank $0$ and $Ш(E/\mathbb Q)_2 \cong (\mathbb Z/2\mathbb Z)^2$.

The rank is `prop_8_2_rank` (`Ch4IsogenyDescent.lean`).  The Sha part is deduced here from Proposition 8.1
(`Prop8_1`, a named statement: $S^{(2)}(E/\mathbb Q) \cong (\mathbb Z/2\mathbb Z)^3$) by the exact sequence (23):
$\#E(\mathbb Q)/2E(\mathbb Q) = 2$ (`card_quot_two_curveP`), hence $\#Ш[2] = 8/2 = 4$, and a finite abelian group
killed by $2$ with $2^n$ elements is $(\mathbb Z/2)^n$ (`addEquiv_fin_zmod_two_of_card`).

* `addEquiv_fin_zmod_two_of_card`: the general lemma.
* `card_quot_two_curveP`: $\#E(\mathbb Q)/2E(\mathbb Q) = 2$.
* `prop_8_2_of_prop_8_1`: Proposition 8.1 implies Proposition 8.2.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace NumberFieldKB.MilneEC

open IsogenyDescent

/-- A finite abelian group $G$ killed by $2$ with $2^n$ elements is isomorphic to $(\mathbb Z/2)^n$: it is a
vector space over $\mathbb Z/2$ of dimension $n$. -/
theorem addEquiv_fin_zmod_two_of_card {G : Type*} [AddCommGroup G] [Finite G] (h2 : ∀ x : G, x + x = 0)
    (n : ℕ) (hn : Nat.card G = 2 ^ n) : Nonempty (G ≃+ (Fin n → ZMod 2)) := by
  have h2' : ∀ x : G, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact h2 x
  let _ : Module (ZMod 2) G := AddCommGroup.zmodModule h2'
  have hfin : Module.Finite (ZMod 2) G := Module.Finite.of_finite
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := G)
  rw [hn, Nat.card_zmod] at hc
  have hr : Module.finrank (ZMod 2) G = n := (Nat.pow_right_injective le_rfl hc).symm
  have : Module.finrank (ZMod 2) G = Module.finrank (ZMod 2) (Fin n → ZMod 2) := by
    rw [hr]; simp
  exact ⟨(LinearEquiv.ofFinrankEq G (Fin n → ZMod 2) this).toAddEquiv⟩

section Main

variable {p : ℕ}

private theorem card_zero_pointT (p : ℕ) [Fact p.Prime] :
    Function.Injective ![(0 : (curveP p).toAffine.Point), pointT p] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact pointT_ne_zero hij.symm
  · exact pointT_ne_zero hij

/-- For $p$ as in Proposition 8.2, $\#E(\mathbb Q)/2E(\mathbb Q) = 2$ for $E : Y^2 = X^3 + pX$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 8.2, pdf p. 152"]
theorem card_quot_two_curveP (hp : p.Prime) (h8 : p % 8 = 1) (h2 : ¬ ∃ x : ZMod p, x ^ 4 = 2) :
    Nat.card ((curveP p).toAffine.Point ⧸ multiples (curveP p).toAffine.Point 2) = 2 := by
  have := Fact.mk hp
  have h2' : ∀ z : ZMod p, z ^ 4 ≠ 2 := fun z hz => h2 ⟨z, hz⟩
  have := fg_curveP h8 h2'
  have hlow := two_pow_mul_le_card_quot_two ![(0 : (curveP p).toAffine.Point), pointT p]
    (card_zero_pointT p) (by
    intro i
    fin_cases i
    · show (2 : ℤ) • (0 : (curveP p).toAffine.Point) = 0
      exact zsmul_zero 2
    · show (2 : ℤ) • pointT p = 0
      rw [two_zsmul, pointT_add_self])
  have hup := card_quot_two_curveP_le h8 h2'
  have h0 := prop_8_2_rank p hp h8 h2
  have h1 : Module.finrank ℤ (curveP p).toAffine.Point = 0 := h0
  rw [h1] at hlow
  simp at hlow
  omega

end Main

/-- **Proposition 8.2** (Milne, *EC*, IV, Proposition 8.2, pdf p. 152), from Proposition 8.1: the rank is $0$
(`prop_8_2_rank`), and $Ш(E/\mathbb Q)_2 \cong (\mathbb Z/2)^2$ since, by the exact sequence (23), $\#Ш[2] =
\#S^{(2)}/\#E(\mathbb Q)/2E(\mathbb Q) = 8/2 = 4$ and $Ш[2]$ is killed by $2$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 8.2, pdf p. 152"]
theorem prop_8_2_of_prop_8_1 (h : Prop8_1) : Prop8_2 := by
  refine ⟨prop_8_2_rank, ?_⟩
  intro p hp h8 h2
  have hell := curveP_isElliptic hp.ne_zero
  obtain ⟨-, hb, hc⟩ := exact_23 ℚ (curveP p) lemma2_1 2 two_ne_zero
  set S := selmerGroup ℚ (curveP p) 2 with hS
  let φ : S →+ _ := (torsionToPointsH1 (curveP p) (AlgebraicClosure ℚ) 2).comp S.subtype
  have hrange : φ.range = shaTwoTorsion (curveP p) := by
    rw [shaTwoTorsion, ← hb]
    ext y
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hS8 : Nat.card S = 8 := by
    obtain ⟨e⟩ := h.selmer p hp h8
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  -- the kernel of φ corresponds to the image of the Kummer map
  have hker : Nat.card φ.ker = 2 := by
    have e1 : φ.ker ≃ (kummerMap (curveP p) lemma2_1 2 two_ne_zero).range :=
      { toFun := fun x => ⟨x.1.1, (hc x.1.1 x.1.2).1 x.2⟩
        invFun := fun y => ⟨⟨y.1, exact_23 ℚ (curveP p) lemma2_1 2 two_ne_zero |>.1 y.2⟩,
          (hc y.1 (exact_23 ℚ (curveP p) lemma2_1 2 two_ne_zero |>.1 y.2)).2 y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    have hrg : (kummerMap (curveP p) lemma2_1 2 two_ne_zero).range =
        (kummerQuotientHom (curveP p) lemma2_1 2 two_ne_zero).range := by
      ext y
      simp only [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨P, rfl⟩
        exact ⟨QuotientAddGroup.mk P, rfl⟩
      · rintro ⟨q, rfl⟩
        induction q using QuotientAddGroup.induction_on with
        | H P => exact ⟨P, rfl⟩
    have e2 : Nat.card (kummerQuotientHom (curveP p) lemma2_1 2 two_ne_zero).range =
        Nat.card ((curveP p).toAffine.Point ⧸ multiples (curveP p).toAffine.Point 2) := by
      exact (Nat.card_congr (AddMonoidHom.ofInjective
        (kummerQuotientHom_injective (curveP p) lemma2_1 2 two_ne_zero)).toEquiv).symm
    rw [Nat.card_congr e1, hrg, e2]
    exact card_quot_two_curveP hp h8 h2
  have hsha : Nat.card (shaTwoTorsion (curveP p)) = 4 := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
    have h3 := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
    rw [hrange] at h3
    rw [← h3]
    rw [hker, hS8] at h1
    omega
  have : Finite (shaTwoTorsion (curveP p)) := Nat.finite_of_card_ne_zero (by rw [hsha]; norm_num)
  refine addEquiv_fin_zmod_two_of_card (fun x => ?_) 2 (by rw [hsha]; norm_num)
  have hx2 := x.2.2
  apply Subtype.ext
  simpa [two_zsmul] using hx2

end NumberFieldKB.MilneEC
