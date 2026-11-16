import NumberFieldKB.MilneEC.Ch1Functions
import NumberFieldKB.ModularCurves.Genus
import NumberFieldKB.TauCetiPort.FieldTheory.FunctionField.PlaneCurve.Projective
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, Elliptic Curves, Chapter I §4: Riemann's theorem, Riemann–Roch, divisors of functions and the genus formula
for nonsingular projective plane curves

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §4 (pdf pp. 41–45). The named statements `Thm4_13`,
`Remark4_7`, `PrincipalDivisors` and `GenusFormula` are proved here from the port of Tau Ceti's function-field
Riemann–Roch theorem and plane-curve genus formula (`NumberFieldKB/TauCetiPort/`, Apache License 2.0, copyright the
Tau Ceti contributors; Tau Ceti main `e8758b7`, unchanged at `d2083f0f` for the theorems used), through the bridge of
`NumberFieldKB/ModularCurves/Genus.lean` (Milne's prime divisors are Tau Ceti's places).

The bridge to Tau Ceti's hypotheses (`plane_chart`): for a nonsingular absolutely irreducible projective plane curve
$C_F$ there is a coordinate $X_i$ not divisible by `F`, and the affine coordinates $x = X_j/X_i$, $y = X_l/X_i$
($j < l$ the other two indices) lie in $k(C)$, generate it over `k`, satisfy $F(\ldots, 1, \ldots) = 0$ with `1` in
position `i`, and one of them is transcendental over `k`.

## Main results

* `isFunctionField_projFunctionField`, `isIntegrallyClosedIn_projFunctionField`: $k(C)$ is a function field of one
  variable with exact constant field `k`.
* `thm4_13`, `remark4_7`, `principalDivisors_holds`, `genusFormula`: the four named statements.
* `theorem_4_5_unconditional`, `remark_4_7_eq_unconditional`, `remark_4_7_equality_unconditional`: the results
  of Chapter I §4 that assumed them.
-/

open MvPolynomial IntermediateField
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace NumberFieldKB.MilneEC

variable {k : Type} [Field k]

/-- Nonsingularity in Tau Ceti's form: every nonzero zero of `F` over $k^{\mathrm{al}}$ has a nonvanishing partial
derivative. -/
theorem exists_pderiv_ne_zero_of_nonsingular {F : MvPolynomial (Fin 3) k} (hF : IsProjectivePlaneCurve F)
    (hns : IsNonsingularProjCurve F) :
    ∀ b : Fin 3 → AlgebraicClosure k, b ≠ 0 → aeval b F = 0 → ∃ l, aeval b (pderiv l F) ≠ 0 := by
  intro b hb hbF
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (AlgebraicClosure k) b hb
  set P : ℙ (AlgebraicClosure k) (Fin 3 → AlgebraicClosure k) := Projectivization.mk _ b hb
  have hP : P ∈ projectivePoints F (AlgebraicClosure k) := by
    show aeval P.rep F = 0
    rw [← hc, Units.smul_def, aeval_smul_of_isHomogeneous hF.1, hbF, mul_zero]
  have h := (isNonsingularProjPoint_iff hF.1 P hP).1 (hns P hP)
  push Not at h
  obtain ⟨j, hj⟩ := h
  refine ⟨j, fun h0 => hj ?_⟩
  rw [← hc, Units.smul_def, aeval_smul_of_isHomogeneous (hF.1.pderiv (i := j)), h0, mul_zero]

/-! ### The affine chart -/

/-- The homogenization $\sum_n c_n X_a^n X_b^{N - n}$ ($N = \deg p$) of a polynomial $p = \sum_n c_n T^n$ of one
variable, with $T = X_a/X_b$. -/
def homogPair (p : Polynomial k) (a b : Fin 3) : MvPolynomial (Fin 3) k :=
  ∑ n ∈ Finset.range (p.natDegree + 1), C (p.coeff n) * X a ^ n * X b ^ (p.natDegree - n)

theorem homogPair_isHomogeneous (p : Polynomial k) (a b : Fin 3) :
    (homogPair p a b).IsHomogeneous p.natDegree := by
  apply IsHomogeneous.sum
  intro n hn
  have hn' : n ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have := ((isHomogeneous_C (Fin 3) (p.coeff n)).mul ((isHomogeneous_X k a).pow n)).mul
    ((isHomogeneous_X k b).pow (p.natDegree - n))
  convert this using 1
  omega

theorem aeval_homogPair {L : Type*} [CommRing L] [Algebra k L] (p : Polynomial k) (a b : Fin 3)
    (w : Fin 3 → L) (hb : w b = 1) : aeval w (homogPair p a b) = Polynomial.aeval (w a) p := by
  simp [homogPair, hb, Polynomial.aeval_eq_sum_range, Algebra.smul_def]

theorem homogPair_ne_zero (p : Polynomial k) (hp : p ≠ 0) {a b : Fin 3} (hab : a ≠ b) :
    homogPair p a b ≠ 0 := by
  intro h0
  have := aeval_homogPair p a b (fun m => if m = a then (Polynomial.X : Polynomial k) else 1)
    (by simp [hab.symm])
  rw [h0, map_zero] at this
  simp only [↓reduceIte, Polynomial.aeval_X_left_apply] at this
  exact hp this.symm

theorem degreeOf_homogPair (p : Polynomial k) (a b m : Fin 3) (ha : m ≠ a) (hb : m ≠ b) :
    degreeOf m (homogPair p a b) = 0 := by
  apply Nat.eq_zero_of_le_zero
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun n _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_mul_le m (C (p.coeff n)) (X a ^ n)
  have h2 := degreeOf_pow_le m (X a : MvPolynomial (Fin 3) k) n
  have h3 := degreeOf_pow_le m (X b : MvPolynomial (Fin 3) k) (p.natDegree - n)
  rw [degreeOf_C] at h1
  rw [degreeOf_X, ite_eq_right_iff.2 (fun h => absurd h ha)] at h2
  rw [degreeOf_X, ite_eq_right_iff.2 (fun h => absurd h hb)] at h3
  omega

/-- Some coordinate $X_i$ is not divisible by the irreducible `F`. -/
theorem exists_not_dvd_X (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] : ∃ i : Fin 3, ¬ F ∣ X i := by
  by_contra h
  push Not at h
  have hirr := (Fact.out : Prime F).irreducible
  have h0 := hirr.associated_of_dvd (X_prime (i := (0 : Fin 3))).irreducible (h 0)
  have h1 := hirr.associated_of_dvd (X_prime (i := (1 : Fin 3))).irreducible (h 1)
  have := X_dvd_X.1 (h0.symm.trans h1).dvd
  exact absurd this (by decide)

/-- **The affine chart of a plane curve as Tau Ceti's data**: a coordinate index `i` and $x, y \in k(C)$ with one of
them transcendental, $k(x, y) = k(C)$ and $F$ vanishing at the point with `1` in position `i` and `x`, `y` in the
other positions (in increasing order). -/
theorem plane_chart (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (hF : IsProjectivePlaneCurve F) :
    ∃ (i : Fin 3) (x y : projFunctionField F), (Transcendental k x ∨ Transcendental k y) ∧
      k⟮x, y⟯ = ⊤ ∧ aeval (i.insertNth 1 ![x, y]) F = 0 := by
  obtain ⟨i, hi⟩ := exists_not_dvd_X F
  have hz : homogFrac F (X i) ≠ 0 := homogFrac_ne_zero F hi
  let v : Fin 3 → FractionRing (homogCoordRing F) := fun m => homogFrac F (X m) / homogFrac F (X i)
  have hmem : ∀ m, v m ∈ projFunctionField F := fun m => by
    have : v m ∈ (projFunctionField F : Set (FractionRing (homogCoordRing F))) := by
      rw [projFunctionField_eq]
      exact ⟨1, X m, X i, isHomogeneous_X k m, isHomogeneous_X k i, hi, rfl⟩
    exact this
  let w : Fin 3 → projFunctionField F := fun m => ⟨v m, hmem m⟩
  let ι : projFunctionField F →ₐ[k] FractionRing (homogCoordRing F) :=
    { (projFunctionField F).subtype with commutes' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have hev : ∀ (g : MvPolynomial (Fin 3) k) (e : ℕ), g.IsHomogeneous e →
      ι (aeval w g) = homogFrac F g / homogFrac F (X i) ^ e := by
    intro g e hg
    rw [comp_aeval_apply]
    have : (fun m => ι (w m)) = (homogFrac F (X i))⁻¹ • (fun m => homogFrac F (X m)) := by
      funext m
      show homogFrac F (X m) / homogFrac F (X i) = _
      simp [div_eq_inv_mul]
    rw [this, aeval_smul_of_isHomogeneous hg, aeval_homogFrac, inv_pow, inv_mul_eq_div]
  have hwi : w i = 1 := Subtype.ext (div_self hz)
  have hins : i.insertNth 1 ![w (i.succAbove 0), w (i.succAbove 1)] = w := by
    rw [← hwi]
    convert Fin.insertNth_self_removeNth i w using 2
    funext t
    fin_cases t <;> rfl
  have hzero : ∀ g : MvPolynomial (Fin 3) k, ∀ e, g.IsHomogeneous e → aeval w g = 0 → F ∣ g := by
    intro g e hg h0
    have := hev g e hg
    rw [h0, map_zero, eq_comm, div_eq_zero_iff] at this
    rcases this with h1 | h1
    · exact (homogFrac_eq_zero_iff F).1 h1
    · exact absurd h1 (pow_ne_zero _ hz)
  refine ⟨i, w (i.succAbove 0), w (i.succAbove 1), ?_, ?_, ?_⟩
  · -- one of the two affine coordinates is transcendental
    by_contra hcon
    obtain ⟨hx, hy⟩ := not_or.mp hcon
    simp only [Transcendental, not_not] at hx hy
    have key : ∀ a m : Fin 3, a ≠ i → m ≠ i → m ≠ a → IsAlgebraic k (w a) → degreeOf m F = 0 := by
      intro a m hai hmi hma halg
      obtain ⟨p, hp, hpa⟩ := halg
      have hP := homogPair_ne_zero p hp hai
      obtain ⟨q, hq⟩ := hzero (homogPair p a i) _ (homogPair_isHomogeneous p a i)
        (by rw [aeval_homogPair p a i w hwi]; exact hpa)
      have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hP hq
      have := degreeOf_homogPair p a i m hma hmi
      rw [hq, degreeOf_mul_eq (Fact.out : Prime F).ne_zero hq0] at this
      omega
    have h01 : i.succAbove 0 ≠ i.succAbove 1 := Fin.succAbove_right_injective.ne (by decide)
    have hdeg : ∀ m, m ≠ i → degreeOf m F = 0 := by
      intro m hm
      obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hm
      fin_cases t
      · exact key (i.succAbove 1) _ (Fin.succAbove_ne _ _) (Fin.succAbove_ne _ _) h01 hy
      · exact key (i.succAbove 0) _ (Fin.succAbove_ne _ _) (Fin.succAbove_ne _ _) h01.symm hx
    apply hi
    suffices hXF : (X i : MvPolynomial (Fin 3) k) ∣ F from
      ((X_prime (i := i)).irreducible.associated_of_dvd (Fact.out : Prime F).irreducible hXF).symm.dvd
    rw [F.as_sum]
    refine Finset.dvd_sum fun s hs => ?_
    have hsi : s i ≠ 0 := by
      intro h0
      have hs0 : s = 0 := by
        ext m
        by_cases hm : m = i
        · subst hm; exact h0
        · have := monomial_le_degreeOf m hs
          rw [hdeg m hm] at this
          simpa using this
      have hw := hF.1 (mem_support_iff.mp hs)
      rw [hs0, map_zero] at hw
      exact hF.2.1 hw.symm
    rw [show (X i : MvPolynomial (Fin 3) k) = monomial (Finsupp.single i 1) 1 from rfl]
    exact monomial_dvd_monomial.2
      ⟨Or.inr (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hsi)), one_dvd _⟩
  · -- the two affine coordinates generate the function field
    rw [eq_top_iff]
    rintro ⟨t, ht⟩ -
    have ht' : t ∈ homogFractions F := by
      have : t ∈ (projFunctionField F : Set (FractionRing (homogCoordRing F))) := ht
      rwa [projFunctionField_eq] at this
    obtain ⟨e, g, h, hg, hh, hFh, rfl⟩ := ht'
    have hw : ∀ m, w m ∈ k⟮w (i.succAbove 0), w (i.succAbove 1)⟯ := by
      intro m
      by_cases hm : m = i
      · subst hm; rw [hwi]; exact one_mem _
      · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hm
        fin_cases t
        · exact subset_adjoin k _ (Set.mem_insert _ _)
        · exact subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)
    have hsub : ∀ q : MvPolynomial (Fin 3) k,
        aeval w q ∈ k⟮w (i.succAbove 0), w (i.succAbove 1)⟯ := by
      intro q
      have e1 : aeval w q = (k⟮w (i.succAbove 0), w (i.succAbove 1)⟯).val
          (aeval (fun m => (⟨w m, hw m⟩ : k⟮w (i.succAbove 0), w (i.succAbove 1)⟯)) q) := by
        rw [comp_aeval_apply]; rfl
      rw [e1]
      exact SetLike.coe_mem _
    have hval : (⟨homogFrac F g / homogFrac F h, ht⟩ : projFunctionField F) =
        aeval w g / aeval w h := by
      apply hι
      show homogFrac F g / homogFrac F h = ι (aeval w g / aeval w h)
      rw [map_div₀, hev g e hg, hev h e hh, div_div_div_cancel_right₀ (pow_ne_zero _ hz)]
    rw [hval]
    exact div_mem (hsub g) (hsub h)
  · -- the point lies on the curve
    rw [hins]
    apply hι
    rw [map_zero, hev F _ hF.1, (homogFrac_eq_zero_iff F).2 dvd_rfl, zero_div]

theorem isIntegrallyClosedIn_projFunctionField (F : MvPolynomial (Fin 3) k) [Fact (Prime F)]
    (hF : IsProjectivePlaneCurve F) (hns : IsNonsingularProjCurve F) :
    IsIntegrallyClosedIn k (projFunctionField F) := by
  obtain ⟨i, x, y, hxy, hgen, h⟩ := plane_chart F hF
  exact TauCeti.isIntegrallyClosedIn_of_isHomogeneous_of_aeval_insertNth_eq_zero (K := AlgebraicClosure k)
    hF.1 (exists_pderiv_ne_zero_of_nonsingular hF hns) i hxy hgen h

theorem isFunctionField_projFunctionField (F : MvPolynomial (Fin 3) k) [Fact (Prime F)]
    (hF : IsProjectivePlaneCurve F) (hns : IsNonsingularProjCurve F) :
    TauCeti.IsFunctionField k (projFunctionField F) := by
  obtain ⟨i, x, y, hxy, hgen, h⟩ := plane_chart F hF
  have hirr := TauCeti.irreducible_map_dehomogenize (K := AlgebraicClosure k) le_rfl hF.1
    (exists_pderiv_ne_zero_of_nonsingular hF hns) i (fun hu => by
      obtain ⟨c, hc, hcG⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
      have hxy' := congrArg (aeval ![x, y]) hcG
      rw [TauCeti.aeval_dehomogenize, h, aeval_C] at hxy'
      exact hc.ne_zero ((map_eq_zero_iff _ (algebraMap k _).injective).mp hxy'.symm))
  have hg : TauCeti.dehomogenize i F ≠ 0 := fun h0 => hirr.ne_zero (by rw [h0, map_zero])
  have hev : aeval ![x, y] (TauCeti.dehomogenize i F) = 0 := by rw [TauCeti.aeval_dehomogenize, h]
  rcases hxy with hx | hy
  · exact TauCeti.isFunctionField_of_aeval_eq_zero hg hx hgen hev
  · refine TauCeti.isFunctionField_of_aeval_eq_zero (g := rename (Equiv.swap 0 1) (TauCeti.dehomogenize i F))
      ?_ hy (by rw [Set.pair_comm]; exact hgen) ?_
    · intro h0
      apply hg
      apply rename_injective _ (Equiv.injective (Equiv.swap (0 : Fin 2) 1))
      rw [h0, map_zero]
    · rw [aeval_rename]
      convert hev using 3
      funext m
      fin_cases m <;> rfl

theorem genus_projFunctionField (F : MvPolynomial (Fin 3) k) [Fact (Prime F)]
    (hF : IsProjectivePlaneCurve F) (hns : IsNonsingularProjCurve F) :
    TauCeti.genus k (projFunctionField F) = (curveDegree F - 1) * (curveDegree F - 2) / 2 := by
  obtain ⟨i, x, y, hxy, hgen, h⟩ := plane_chart F hF
  exact TauCeti.genus_eq_of_isHomogeneous_of_aeval_insertNth_eq_zero (K := AlgebraicClosure k)
    hF.1 (exists_pderiv_ne_zero_of_nonsingular hF hns) i hxy hgen h

/-- **Theorem 4.13 (Riemann)** (Milne, pdf p. 45), proved: discharges the named statement `Thm4_13`. -/
@[kb "milne2006ec" "Ch. I, Thm. 4.13, pdf p. 45"]
theorem thm4_13 : Thm4_13 := by
  refine ⟨fun k _ _ F _ hF _ hns => ?_⟩
  exact ⟨_, isGenus_tauCetiGenus (isFunctionField_projFunctionField F hF hns)
    (isIntegrallyClosedIn_projFunctionField F hF hns)⟩

/-- **Remark 4.7 (a) (Riemann–Roch)** (Milne, pdf p. 41), proved: discharges the named statement `Remark4_7`. -/
@[kb "milne2006ec" "Ch. I, Rem. 4.7 (a), pdf p. 41"]
theorem remark4_7 : Remark4_7 := by
  refine ⟨fun k _ _ F _ hF _ hns => ?_⟩
  exact riemannRoch (isFunctionField_projFunctionField F hF hns) (isIntegrallyClosedIn_projFunctionField F hF hns)

/-- **Divisors of functions** (Milne, p. 45), proved: discharges the named statement `PrincipalDivisors`. -/
@[kb "milne2006ec" "Ch. I, §4, divisors of functions, pdf p. 45"]
theorem principalDivisors_holds : PrincipalDivisors := by
  refine ⟨fun k _ _ F _ hF _ hns h hh => ?_⟩
  have hFF := isFunctionField_projFunctionField F hF hns
  obtain ⟨D, hD⟩ := exists_isDivisorOf hFF hh
  exact ⟨D, hD, deg_eq_zero_of_isDivisorOf hFF hD⟩

/-- **The genus of a nonsingular plane curve of degree `d` is $(d-1)(d-2)/2$** (Milne, formula (7), p. 42), proved:
discharges the named statement `GenusFormula`. -/
@[kb "milne2006ec" "Ch. I, §4, formula (7), pdf p. 42"]
theorem genusFormula : GenusFormula := by
  refine ⟨fun k _ _ F _ hF _ hns => ?_⟩
  have h := isGenus_tauCetiGenus (isFunctionField_projFunctionField F hF hns)
    (isIntegrallyClosedIn_projFunctionField F hF hns)
  rw [genus_projFunctionField F hF hns] at h
  convert h using 1
  have hd : curveDegree F ≠ 0 := hF.2.1
  obtain ⟨n, hn⟩ : ∃ n, curveDegree F = n + 1 := Nat.exists_eq_succ_of_ne_zero hd
  rw [hn]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, show n + 1 + 1 - 2 = n by omega]
    push_cast
    ring_nf

/-! ### Downstream results, now unconditional -/

/-- **Theorem 4.5 (Riemann)** (p. 41), unconditional: `theorem_4_5` with `Thm4_13` supplied by `thm4_13`. -/
@[kb "milne2006ec" "Ch. I, Thm. 4.5, pdf p. 41"]
theorem theorem_4_5_unconditional (k : Type) [Field k] [IsAlgClosed k] (F : MvPolynomial (Fin 3) k)
    [Fact (Prime F)] (hF : IsProjectivePlaneCurve F) (hirr : Irreducible (baseChange (AlgebraicClosure k) F))
    (hns : IsNonsingularProjCurve F) :
    ∃ g : ℤ, ∀ D : Divisor k (projFunctionField F), (D.deg + 1 - g ≤ D.ell) ∧
      ∃ N : ℤ, ∀ D : Divisor k (projFunctionField F), N ≤ D.deg → (D.ell : ℤ) = D.deg + 1 - g :=
  theorem_4_5 thm4_13 k F hF hirr hns

/-- **Remark 4.7 (a)** (p. 41), unconditional: a divisor of negative degree has $\ell(D) = 0$
(`remark_4_7_equality` with `PrincipalDivisors` supplied by `principalDivisors_holds`). -/
@[kb "milne2006ec" "Ch. I, Rem. 4.7 (a), pdf p. 41"]
theorem remark_4_7_equality_unconditional (k : Type) [Field k] [PerfectField k]
    (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (hF : IsProjectivePlaneCurve F)
    (hirr : Irreducible (baseChange (AlgebraicClosure k) F)) (hns : IsNonsingularProjCurve F)
    (D : Divisor k (projFunctionField F)) (hD : D.deg < 0) : D.ell = 0 :=
  remark_4_7_equality principalDivisors_holds k F hF hirr hns D hD

/-- **Remark 4.7 (a)** (p. 41), unconditional: equality in Riemann's inequality when $\deg D > 2g - 2$
(`remark_4_7_eq` with `Remark4_7` and `PrincipalDivisors` supplied by `remark4_7` and `principalDivisors_holds`). -/
@[kb "milne2006ec" "Ch. I, Rem. 4.7 (a), pdf p. 41"]
theorem remark_4_7_eq_unconditional (k : Type) [Field k] [PerfectField k] (F : MvPolynomial (Fin 3) k)
    [Fact (Prime F)] (hF : IsProjectivePlaneCurve F) (hirr : Irreducible (baseChange (AlgebraicClosure k) F))
    (hns : IsNonsingularProjCurve F) :
    ∃ W : Divisor k (projFunctionField F), W.deg = 2 * genus k (projFunctionField F) - 2 ∧
      ∀ D : Divisor k (projFunctionField F), 2 * genus k (projFunctionField F) - 2 < D.deg →
        (D.ell : ℤ) = D.deg + 1 - genus k (projFunctionField F) :=
  remark_4_7_eq remark4_7 principalDivisors_holds k F hF hirr hns

end NumberFieldKB.MilneEC
