import NumberFieldKB.MilneEC.Ch3Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!
# Milne, Elliptic Curves, Chapter III §3: torsion points

Proposition 3.13, Lemmas 3.14 and 3.15 and Remark 3.16 of Milne, *Elliptic Curves*
(`milne2006ec`, pdf pp. 103–104).  Theorem 3.12 and the torsion of `ℂ/Λ` are in
`Ch3TorsionComplex.lean`.

* `E(k)ₙ` is Mathlib's `AddSubgroup.torsionBy E(k) n`; "free `ℤ/nℤ`-module of rank 2" is
  "isomorphic to `ℤ/nℤ × ℤ/nℤ` as a group" (a `ℤ/nℤ`-module structure is unique).
* Lemma 3.14 (the coordinates of `nP` in terms of division polynomials) is a named statement
  (`DivisionPolynomialFormula`): Milne's proof is "use induction" (citing Cassels), and the
  induction is a long computation not in Mathlib.  Proposition 3.13 and Theorem 3.12 over an
  arbitrary algebraically closed field of characteristic zero are proved from it; Theorem 3.12
  over `ℂ` is proved unconditionally (from `ℂ/Λ ≅ E(Λ)(ℂ)` and Theorem 3.10).
* Remark 3.16 (characteristic `p`) is a named statement.
* Milne's division polynomials of `Y² = X³ + aX + b` are Mathlib's `WeierstrassCurve.ψ` of the
  curve with `a₄ = a`, `a₆ = b` (`ψ_milne_*` compare the first four).
-/

open Polynomial

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace NumberFieldKB.MilneEC.III

/-! ### Lemma 3.14 (named statement) -/

/-- The curve `Y² = X³ + aX + b` of Lemma 3.14. -/
def shortCurve {k : Type*} [CommRing k] (a b : k) : WeierstrassCurve k :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

theorem ψ_milne_two {k : Type*} [CommRing k] (a b : k) :
    (shortCurve a b).ψ 2 = C (C 2) * X := by
  rw [WeierstrassCurve.ψ_two, WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
  simp [shortCurve]

theorem ψ_milne_three {k : Type*} [CommRing k] (a b : k) :
    (shortCurve a b).ψ 3 = C (3 * X ^ 4 + C (6 * a) * X ^ 2 + C (12 * b) * X - C (a ^ 2)) := by
  rw [WeierstrassCurve.ψ_three, WeierstrassCurve.Ψ₃]
  simp [shortCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  C_simp
  ring

theorem ψ_milne_four {k : Type*} [CommRing k] (a b : k) :
    (shortCurve a b).ψ 4 = C (C 4) * X * C (X ^ 6 + C (5 * a) * X ^ 4 + C (20 * b) * X ^ 3 -
      C (5 * a ^ 2) * X ^ 2 - C (4 * a * b) * X - C (8 * b ^ 2) - C (a ^ 3)) := by
  rw [WeierstrassCurve.ψ_four, WeierstrassCurve.preΨ₄, WeierstrassCurve.ψ₂,
    WeierstrassCurve.Affine.polynomialY]
  simp [shortCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, WeierstrassCurve.Affine.polynomial]
  C_simp
  ring

/-- **Lemma 3.14** (Milne, pdf pp. 103–104; Cassels 1966, 7.2), as a named statement: for the
curve `E : Y²Z = X³ + aXZ² + bZ³` over a field and a point `P = (x : y : 1)`, with Milne's
division polynomials `ψₙ` (Mathlib's `WeierstrassCurve.ψ`),
`nP = (xψₙ⁴ − ψₙ₋₁ψₙ₊₁ψₙ² : ψ₂ₙ/2 : ψₙ⁴)` for `n ≥ 1`; in affine terms, `nP` is the affine
point `(x − ψₙ₋₁ψₙ₊₁/ψₙ², ψ₂ₙ/(2ψₙ⁴))` when `ψₙ(P) ≠ 0`, and `nP = O` when `ψₙ(P) = 0`.
The statement is for fields of characteristic not `2` (Milne's `ψ₂ₙ/2`). -/
@[kb "milne2006ec" "Ch. III, Lemma 3.14, pdf p. 103"]
structure DivisionPolynomialFormula : Prop where
  smul_eq_zero : ∀ (k : Type) [Field k] [DecidableEq k], (2 : k) ≠ 0 →
    ∀ (a b : k) [(shortCurve a b).IsElliptic]
    (x y : k) (h : (shortCurve a b).toAffine.Nonsingular x y) (n : ℕ), 1 ≤ n →
    ((shortCurve a b).ψ n).evalEval x y = 0 → n • WeierstrassCurve.Affine.Point.some x y h = 0
  smul_eq_some : ∀ (k : Type) [Field k] [DecidableEq k], (2 : k) ≠ 0 →
    ∀ (a b : k) [(shortCurve a b).IsElliptic]
    (x y : k) (h : (shortCurve a b).toAffine.Nonsingular x y) (n : ℕ), 1 ≤ n →
    ((shortCurve a b).ψ n).evalEval x y ≠ 0 →
      ∃ h' : (shortCurve a b).toAffine.Nonsingular
          (x - ((shortCurve a b).ψ (n - 1)).evalEval x y * ((shortCurve a b).ψ (n + 1)).evalEval x y /
            ((shortCurve a b).ψ n).evalEval x y ^ 2)
          (((shortCurve a b).ψ (2 * n)).evalEval x y / (2 * ((shortCurve a b).ψ n).evalEval x y ^ 4)),
        n • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some _ _ h'

/-! ### Lemma 3.15 -/

theorem algClosed_mem_range {k Ω : Type*} [Field k] [IsAlgClosed k] [Field Ω] [Algebra k Ω]
    (x : Ω) (hx : IsAlgebraic k x) : x ∈ Set.range (algebraMap k Ω) := by
  have h1 := minpoly.irreducible hx.isIntegral
  have h2 := IsAlgClosed.degree_eq_one_of_irreducible k h1
  exact (minpoly.degree_eq_one_iff.1 h2)

/-- Gauss-lemma step: a nonunit common divisor over the fraction field gives a nonunit common
divisor over `S`. -/
theorem gauss_common {S : Type*} [CommRing S] [IsDomain S] [IsGCDMonoid S]
    {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K] (F G : S[X]) (D : K[X])
    (hD : ¬ IsUnit D) (hD0 : D ≠ 0) (hF : D ∣ F.map (algebraMap S K))
    (hG : D ∣ G.map (algebraMap S K)) :
    ∃ H : S[X], H ∣ F ∧ H ∣ G ∧ ¬ IsUnit H := by
  let _ : NormalizedGCDMonoid S := Nonempty.some inferInstance
  obtain ⟨b, hb, hbD⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors S) D
  set D₁ := IsLocalization.integerNormalization (nonZeroDivisors S) D with hD₁
  have hD₁0 : D₁ ≠ 0 := fun h =>
    hD0 ((IsLocalization.integerNormalization_eq_zero_iff (le_refl _) D).1 h)
  set H := D₁.primPart with hH
  have hHprim : H.IsPrimitive := D₁.isPrimitive_primPart
  have hc : D₁.content ≠ 0 := by
    intro h; exact hD₁0 (by rw [D₁.eq_C_content_mul_primPart, h]; simp)
  have hb0 : algebraMap S K b ≠ 0 := by
    have : (b : S) ≠ 0 := nonZeroDivisors.ne_zero hb
    exact (map_ne_zero_iff (algebraMap S K) (IsFractionRing.injective S K)).2 this
  have hmap : (b : S) • D = C (algebraMap S K D₁.content) * H.map (algebraMap S K) := by
    rw [← hbD]
    conv_lhs => rw [D₁.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
  have hDH : D = C ((algebraMap S K b)⁻¹ * algebraMap S K D₁.content) * H.map (algebraMap S K) := by
    have : D = C ((algebraMap S K b)⁻¹) * ((b : S) • D) := by
      rw [← IsScalarTower.algebraMap_smul K (b : S) D, Algebra.smul_def]
      simp [← mul_assoc, ← C_mul, hb0]
    rw [this, hmap, ← mul_assoc, ← C_mul]
  have hmapH : H.map (algebraMap S K) ∣ D := ⟨C ((algebraMap S K b)⁻¹ * algebraMap S K D₁.content), by
    rw [mul_comm]; exact hDH⟩
  have key : ∀ F : S[X], D ∣ F.map (algebraMap S K) → H ∣ F := by
    intro F hF
    by_cases hF0 : F = 0
    · simp [hF0]
    have hcF : F.content ≠ 0 := by
      intro h; exact hF0 (by rw [F.eq_C_content_mul_primPart, h]; simp)
    have h1 : H.map (algebraMap S K) ∣ F.primPart.map (algebraMap S K) := by
      have h2 := hmapH.trans hF
      rw [F.eq_C_content_mul_primPart, Polynomial.map_mul, Polynomial.map_C] at h2
      have hu : IsUnit (C (algebraMap S K F.content)) := by
        apply Polynomial.isUnit_C.2
        exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff (algebraMap S K) (IsFractionRing.injective S K)).2 hcF)
      exact (hu.dvd_mul_left).1 h2
    have h3 := (hHprim.dvd_iff_fraction_map_dvd_fraction_map K).2 h1
    exact h3.trans ⟨C F.content, by rw [mul_comm]; exact F.eq_C_content_mul_primPart⟩
  refine ⟨H, key F hF, key G hG, ?_⟩
  intro hu
  apply hD
  rw [hDH]
  refine IsUnit.mul ?_ (hu.map (mapRingHom (algebraMap S K)))
  apply Polynomial.isUnit_C.2
  refine isUnit_iff_ne_zero.2 (mul_ne_zero (inv_ne_zero hb0) ?_)
  exact (map_ne_zero_iff (algebraMap S K) (IsFractionRing.injective S K)).2 hc

theorem evalEval_map_eq {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (x y : Ω)
    (A : Polynomial (Polynomial k)) :
    (A.map (mapRingHom (algebraMap k Ω))).evalEval x y =
      (A.map (Polynomial.eval₂RingHom (algebraMap k Ω) x)).eval y := by
  induction A using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, Polynomial.evalEval_add, eval_add, hp, hq]
  | monomial n s =>
    simp [Polynomial.evalEval]
    left
    rfl

/-- Lemma 3.15 (Milne, pdf p. 104): let `k ⊆ Ω` be algebraically closed fields.  If
`F, G ∈ k[X, Y]` have no common factor, every common zero of `F` and `G` with coordinates in `Ω`
has coordinates in `k`.  (Polynomials in `X, Y` are `Polynomial (Polynomial k)`, the outer
variable being `Y`; `F(x, y)` is `evalEval x y`.) -/
@[kb "milne2006ec" "Ch. III, Lemma 3.15, pdf p. 104"]
theorem lemma_3_15 {k Ω : Type*} [Field k] [IsAlgClosed k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (F G : Polynomial (Polynomial k)) (hFG : ∀ H : Polynomial (Polynomial k), H ∣ F → H ∣ G → IsUnit H) (x y : Ω)
    (hF : (F.map (mapRingHom (algebraMap k Ω))).evalEval x y = 0)
    (hG : (G.map (mapRingHom (algebraMap k Ω))).evalEval x y = 0) :
    x ∈ Set.range (algebraMap k Ω) ∧ y ∈ Set.range (algebraMap k Ω) := by
  rw [evalEval_map_eq] at hF hG
  set φ : Polynomial k →+* Ω := Polynomial.eval₂RingHom (algebraMap k Ω) x with hφ
  have hx : IsAlgebraic k x := by
    by_contra hx
    have hinj : Function.Injective φ := by
      have := (transcendental_iff_injective (R := k) (x := x)).1 hx
      exact this
    letI : Algebra (Polynomial k) Ω := φ.toAlgebra
    let K := FractionRing (Polynomial k)
    let ι : K →+* Ω := IsFractionRing.lift hinj
    have hι : ∀ s, ι (algebraMap (Polynomial k) K s) = φ s := fun s =>
      IsFractionRing.lift_algebraMap hinj s
    let FK : Polynomial K := F.map (algebraMap (Polynomial k) K)
    let GK : Polynomial K := G.map (algebraMap (Polynomial k) K)
    have hmapι : ∀ A : Polynomial (Polynomial k),
        ((A.map (algebraMap (Polynomial k) K)).map ι) = A.map φ := by
      intro A
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext hι
    set I : Ideal (Polynomial K) := Ideal.span {FK, GK} with hI
    set D : Polynomial K := Submodule.IsPrincipal.generator I with hDdef
    have hDI : D ∈ I := Submodule.IsPrincipal.generator_mem I
    have hFI : FK ∈ I := Ideal.subset_span (by simp)
    have hGI : GK ∈ I := Ideal.subset_span (by simp)
    have hDF : D ∣ FK := (Submodule.IsPrincipal.mem_iff_generator_dvd I).1 hFI
    have hDG : D ∣ GK := (Submodule.IsPrincipal.mem_iff_generator_dvd I).1 hGI
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hDI
    have hF' : (FK.map ι).eval y = 0 := by rw [hmapι]; exact hF
    have hG' : (GK.map ι).eval y = 0 := by rw [hmapι]; exact hG
    have hDy : (D.map ι).eval y = 0 := by
      rw [← hab]
      simp [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hF', hG']
    have hDnu : ¬ IsUnit D := by
      intro hu
      have := (hu.map (mapRingHom ι)).map (evalRingHom y)
      have h0 : (evalRingHom y) ((mapRingHom ι) D) = 0 := hDy
      rw [h0] at this
      exact not_isUnit_zero this
    have hD0 : D ≠ 0 := by
      intro h0
      rw [h0] at hDF hDG
      have hF0 : F = 0 := by
        have := zero_dvd_iff.1 hDF
        exact (Polynomial.map_injective _ (IsFractionRing.injective _ K)) (by simpa [FK] using this)
      have hG0 : G = 0 := by
        have := zero_dvd_iff.1 hDG
        exact (Polynomial.map_injective _ (IsFractionRing.injective _ K)) (by simpa [GK] using this)
      have := hFG 0 (by rw [hF0]) (by rw [hG0])
      exact not_isUnit_zero this
    obtain ⟨H, hHF, hHG, hHu⟩ := gauss_common F G D hDnu hD0 hDF hDG
    exact hHu (hFG H hHF hHG)
  obtain ⟨a, ha⟩ := algClosed_mem_range x hx
  refine ⟨⟨a, ha⟩, ?_⟩
  have hφa : φ = (algebraMap k Ω).comp (evalRingHom a) := by
    apply RingHom.ext
    intro s
    simp only [hφ, RingHom.comp_apply, coe_evalRingHom, coe_eval₂RingHom, ← ha]
    exact eval₂_at_apply (algebraMap k Ω) a
  have hpt : ∀ A : Polynomial (Polynomial k), (A.map φ).eval y =
      ((A.map (evalRingHom a)).map (algebraMap k Ω)).eval y := by
    intro A
    rw [Polynomial.map_map, hφa]
  rw [hpt] at hF hG
  by_cases hF0 : F.map (evalRingHom a) = 0
  · by_cases hG0 : G.map (evalRingHom a) = 0
    · exfalso
      have hdiv : ∀ A : Polynomial (Polynomial k), A.map (evalRingHom a) = 0 →
          C (X - C a) ∣ A := by
        intro A hA
        rw [C_dvd_iff_dvd_coeff]
        intro i
        rw [dvd_iff_isRoot]
        have := congrArg (fun p => p.coeff i) hA
        simpa [coeff_map] using this
      have hu := hFG _ (hdiv F hF0) (hdiv G hG0)
      have := natDegree_eq_zero_of_isUnit (Polynomial.isUnit_C.1 hu)
      simp at this
    · refine algClosed_mem_range y ⟨_, hG0, ?_⟩
      rw [aeval_def, eval₂_eq_eval_map]
      exact hG
  · refine algClosed_mem_range y ⟨_, hF0, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map]
    exact hF

/-! ### Change of variables `x = x' + r`, `y = y' + s x' + t` on points -/

section VariableChange

open WeierstrassCurve WeierstrassCurve.Affine

/-- Coefficient relations of a change of variables `x = x' + r`, `y = y' + s x' + t`. -/
structure IsVC {F : Type*} [CommRing F] (W W' : WeierstrassCurve F) (r s t : F) : Prop where
  a1 : W'.a₁ = W.a₁ + 2 * s
  a2 : W'.a₂ = W.a₂ - s * W.a₁ + 3 * r - s ^ 2
  a3 : W'.a₃ = W.a₃ + r * W.a₁ + 2 * t
  a4 : W'.a₄ = W.a₄ - s * W.a₃ + 2 * r * W.a₂ - (t + r * s) * W.a₁ + 3 * r ^ 2 - 2 * s * t
  a6 : W'.a₆ = W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3 - t * W.a₃ - t ^ 2 - r * t * W.a₁

theorem IsVC.map {F G : Type*} [CommRing F] [CommRing G] {W W' : WeierstrassCurve F} {r s t : F}
    (hv : IsVC W W' r s t) (f : F →+* G) : IsVC (W.map f) (W'.map f) (f r) (f s) (f t) where
  a1 := by simp [hv.a1, map_ofNat f 2]
  a2 := by simp [hv.a2, map_ofNat f 2, map_ofNat f 3]
  a3 := by simp [hv.a3, map_ofNat f 2]
  a4 := by simp [hv.a4, map_ofNat f 2, map_ofNat f 3]
  a6 := by simp [hv.a6]

section
variable {F : Type*} [Field F] [DecidableEq F] {W W' : WeierstrassCurve F} {r s t : F}

omit [DecidableEq F] in
theorem IsVC.equation (hv : IsVC W W' r s t) {x y : F} (h : W.toAffine.Equation x y) :
    W'.toAffine.Equation (x - r) (y - s * (x - r) - t) := by
  rw [equation_iff] at h ⊢
  rw [hv.a1, hv.a2, hv.a3, hv.a4, hv.a6]
  linear_combination h

omit [DecidableEq F] in
theorem IsVC.negY (hv : IsVC W W' r s t) (x y : F) :
    W'.toAffine.negY (x - r) (y - s * (x - r) - t) = W.toAffine.negY x y - s * (x - r) - t := by
  simp only [Affine.negY, hv.a1, hv.a3]
  ring

omit [DecidableEq F] in
theorem IsVC.addX (hv : IsVC W W' r s t) (x₁ x₂ L : F) :
    W'.toAffine.addX (x₁ - r) (x₂ - r) (L - s) = W.toAffine.addX x₁ x₂ L - r := by
  simp only [Affine.addX, hv.a1, hv.a2]
  ring

omit [DecidableEq F] in
theorem IsVC.addY (hv : IsVC W W' r s t) (x₁ x₂ y₁ L : F) :
    W'.toAffine.addY (x₁ - r) (x₂ - r) (y₁ - s * (x₁ - r) - t) (L - s) =
      W.toAffine.addY x₁ x₂ y₁ L - s * (W.toAffine.addX x₁ x₂ L - r) - t := by
  simp only [Affine.addY, Affine.negAddY, hv.addX]
  simp only [Affine.negY, Affine.addX, hv.a1, hv.a3]
  ring

theorem IsVC.slope (hv : IsVC W W' r s t) {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂))
    (hD : x₁ = x₂ → y₁ - W.toAffine.negY x₁ y₁ ≠ 0) :
    W'.toAffine.slope (x₁ - r) (x₂ - r) (y₁ - s * (x₁ - r) - t) (y₂ - s * (x₂ - r) - t) =
      W.toAffine.slope x₁ x₂ y₁ y₂ - s := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    have hD' := hD hx
    subst hx
    have hy' : y₁ - s * (x₁ - r) - t ≠ W'.toAffine.negY (x₁ - r) (y₂ - s * (x₁ - r) - t) := by
      rw [hv.negY]
      intro h
      apply hy
      linear_combination h
    rw [Affine.slope_of_Y_ne rfl hy', Affine.slope_of_Y_ne rfl hy, hv.negY]
    have e : y₁ - s * (x₁ - r) - t - (W.toAffine.negY x₁ y₁ - s * (x₁ - r) - t) =
        y₁ - W.toAffine.negY x₁ y₁ := by ring
    rw [e]
    field_simp
    simp only [Affine.negY, hv.a1, hv.a2, hv.a4]
    ring
  · have hx' : x₁ - r ≠ x₂ - r := fun h => hx (by linear_combination h)
    rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx]
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
    field_simp
    ring

/-- The point map of a change of variables. -/
noncomputable def vcPoint (hv : IsVC W W' r s t) [W'.IsElliptic] :
    W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (x - r) (y - s * (x - r) - t)
      (equation_iff_nonsingular.1 (hv.equation h.1))

theorem vcPoint_add (hv : IsVC W W' r s t) [W'.IsElliptic] (P Q : W.toAffine.Point) :
    vcPoint hv (P + Q) = vcPoint hv P + vcPoint hv Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · have h0 : vcPoint hv (0 : W.toAffine.Point) = 0 := rfl
    show vcPoint hv (0 + Q) = vcPoint hv 0 + vcPoint hv Q
    rw [zero_add, h0, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · have h0 : vcPoint hv (0 : W.toAffine.Point) = 0 := rfl
    show vcPoint hv (_ + 0) = vcPoint hv _ + vcPoint hv 0
    rw [add_zero, h0, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · obtain ⟨rfl, hy⟩ := hxy
    rw [Point.add_of_Y_eq rfl hy]
    have : vcPoint hv (Point.some x₁ y₁ h₁) + vcPoint hv (Point.some x₁ y₂ h₂) = 0 := by
      simp only [vcPoint]
      apply Point.add_of_Y_eq rfl
      rw [hv.negY, hy]
    rw [this]
    rfl
  · have hD : x₁ = x₂ → y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := by
      intro hx
      have hy : y₁ ≠ W.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      have := Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hx hy
      subst hx this
      exact sub_ne_zero.2 hy
    have hxy' : ¬(x₁ - r = x₂ - r ∧ y₁ - s * (x₁ - r) - t =
        W'.toAffine.negY (x₂ - r) (y₂ - s * (x₂ - r) - t)) := by
      rintro ⟨h1, h2⟩
      apply hxy
      have hx : x₁ = x₂ := by linear_combination h1
      refine ⟨hx, ?_⟩
      subst hx
      rw [hv.negY] at h2
      linear_combination h2
    rw [Point.add_some hxy]
    simp only [vcPoint]
    rw [Point.add_some hxy']
    simp only [Point.some.injEq]
    rw [hv.slope hxy hD, hv.addX, hv.addY]
    exact ⟨rfl, rfl⟩

/-- The point map of a change of variables, as a group homomorphism. -/
noncomputable def vcHom (hv : IsVC W W' r s t) [W'.IsElliptic] :
    W.toAffine.Point →+ W'.toAffine.Point :=
  AddMonoidHom.mk' (vcPoint hv) (vcPoint_add hv)

end

end VariableChange

/-! ### Torsion points on `Y² = X³ + aX + b` -/

section ShortCase

open WeierstrassCurve WeierstrassCurve.Affine

/-- On a point of the curve, `ψₙ` agrees with `Ψₙ = preΨₙ · (ψ₂ if n is even)`. -/
theorem evalEval_ψ_of_equation {K : Type*} [Field K] (W : WeierstrassCurve K) {x y : K}
    (h : W.toAffine.Equation x y) (n : ℕ) :
    (W.ψ n).evalEval x y =
      (W.preΨ' n).eval x * (if Even n then W.ψ₂.evalEval x y else 1) := by
  have h1 := WeierstrassCurve.Affine.CoordinateRing.mk_ψ W (n : ℤ)
  unfold WeierstrassCurve.Affine.CoordinateRing.mk at h1
  rw [AdjoinRoot.mk_eq_mk] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : (W.ψ n - W.Ψ n).evalEval x y = 0 := by
    rw [hc, evalEval_mul]
    have : W.toAffine.polynomial.evalEval x y = 0 := h
    rw [this, zero_mul]
  rw [evalEval_sub, sub_eq_zero] at h2
  rw [h2, WeierstrassCurve.Ψ_ofNat, evalEval_mul, evalEval_C]
  split_ifs <;> simp

theorem natCast_ne_zero_of_lt_ringChar {k : Type*} [Field k] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (h : ringChar k < ℓ) : (ℓ : k) ≠ 0 := by
  intro h0
  rw [ringChar.spec k ℓ] at h0
  rcases (Nat.dvd_prime hℓ).1 h0 with h1 | h1
  · have := (ringChar.spec k 1).2 (by rw [h1])
    simp at this
  · omega

/-- `Ψₙ` is not the zero polynomial for `n ≥ 1`, using that `k` has a point of order a large
prime `ℓ` (this is where `DivisionPolynomialFormula` enters). -/
theorem preΨ'_ne_zero_short (h : DivisionPolynomialFormula) {k : Type} [Field k] [DecidableEq k]
    [IsAlgClosed k] (h2 : (2 : k) ≠ 0) (a b : k) [(shortCurve a b).IsElliptic] (n : ℕ)
    (hn : 1 ≤ n) : (shortCurve a b).preΨ' n ≠ 0 := by
  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (n + ringChar k + 3)
  have hℓk : (ℓ : k) ≠ 0 := natCast_ne_zero_of_lt_ringChar ℓ hℓ (by omega)
  have hℓ2 : 2 < ℓ := by omega
  have hdeg : 0 < ((shortCurve a b).preΨ' ℓ).natDegree :=
    (shortCurve a b).natDegree_preΨ'_pos hℓ2 hℓk
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root ((shortCurve a b).preΨ' ℓ)
    (Polynomial.natDegree_pos_iff_degree_pos.1 hdeg).ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + a * x + b) (n := 2) (by norm_num)
  have hE : (shortCurve a b).toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [shortCurve]
    linear_combination hy
  have hns := WeierstrassCurve.Affine.equation_iff_nonsingular.1 hE
  have hodd : ¬ Even ℓ := by rw [hℓ.even_iff]; omega
  have hψℓ : ((shortCurve a b).ψ ℓ).evalEval x y = 0 := by
    rw [evalEval_ψ_of_equation _ hE, if_neg hodd, mul_one]
    exact hx
  have hℓP := h.smul_eq_zero k h2 a b x y hns ℓ (by omega) hψℓ
  have hnP : n • WeierstrassCurve.Affine.Point.some x y hns ≠ 0 := by
    intro hnP0
    have hcop : Nat.gcd ℓ n = 1 := by
      have := (Nat.Prime.coprime_iff_not_dvd hℓ).2 (fun hd => by
        have := Nat.le_of_dvd hn hd
        omega)
      exact this
    have h1 := addOrderOf_dvd_of_nsmul_eq_zero hℓP
    have h3 := addOrderOf_dvd_of_nsmul_eq_zero hnP0
    have h4 : addOrderOf (WeierstrassCurve.Affine.Point.some x y hns) ∣ Nat.gcd ℓ n :=
      Nat.dvd_gcd h1 h3
    rw [hcop] at h4
    exact WeierstrassCurve.Affine.Point.some_ne_zero hns
      (AddMonoid.addOrderOf_eq_one_iff.1 (Nat.dvd_one.1 h4))
  have hψn : ((shortCurve a b).ψ n).evalEval x y ≠ 0 := fun hz =>
    hnP (h.smul_eq_zero k h2 a b x y hns n hn hz)
  rw [evalEval_ψ_of_equation _ hE] at hψn
  intro hz
  apply hψn
  rw [hz]
  simp

/-- A torsion point on a curve of the form `shortCurve` has `ψₙ(P) = 0`. -/
theorem ψ_eq_zero_of_torsion (h : DivisionPolynomialFormula) {Ω : Type} [Field Ω] [DecidableEq Ω]
    (h2 : (2 : Ω) ≠ 0) (W : WeierstrassCurve Ω) (a b : Ω) (hW : W = shortCurve a b)
    [W.IsElliptic] (x y : Ω) (hns : W.toAffine.Nonsingular x y) (n : ℕ) (hn : 1 ≤ n)
    (hQ : n • WeierstrassCurve.Affine.Point.some x y hns = 0) :
    ((shortCurve a b).ψ n).evalEval x y = 0 := by
  subst hW
  by_contra hne
  obtain ⟨h', hh⟩ := h.smul_eq_some Ω h2 a b x y hns n hn hne
  rw [hQ] at hh
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ hh.symm

/-- The coordinates of an `n`-torsion point of `Y² = X³ + aX + b` over `Ω` lie in `k`. -/
theorem torsion_coords_short (h : DivisionPolynomialFormula) {k Ω : Type} [Field k] [DecidableEq k]
    [IsAlgClosed k] [Field Ω] [DecidableEq Ω] [IsAlgClosed Ω] [Algebra k Ω] (h2 : (2 : k) ≠ 0)
    (a b : k) (E' : WeierstrassCurve k) (hE' : E' = shortCurve a b) [E'.IsElliptic] (x y : Ω)
    (hns : (E'.baseChange Ω).toAffine.Nonsingular x y) (n : ℕ) (hn : 0 < n)
    (hQ : n • WeierstrassCurve.Affine.Point.some x y hns = 0) :
    x ∈ Set.range (algebraMap k Ω) ∧ y ∈ Set.range (algebraMap k Ω) := by
  subst hE'
  set f := algebraMap k Ω with hf
  have hW : (shortCurve a b).baseChange Ω = shortCurve (f a) (f b) := by
    ext <;> simp [WeierstrassCurve.baseChange, shortCurve, hf]
  have hmap : shortCurve (f a) (f b) = (shortCurve a b).map f := by
    ext <;> simp [shortCurve]
  have h2Ω : (2 : Ω) ≠ 0 := by
    have : (2 : Ω) = f 2 := (map_ofNat f 2).symm
    rw [this]
    exact (map_ne_zero_iff f f.injective).2 h2
  haveI : ((shortCurve a b).baseChange Ω).IsElliptic :=
    inferInstanceAs ((shortCurve a b).map f).IsElliptic
  have hψ := ψ_eq_zero_of_torsion h h2Ω ((shortCurve a b).baseChange Ω) (f a) (f b) hW x y hns n
    hn hQ
  have hEq : (shortCurve (f a) (f b)).toAffine.Equation x y := by
    rw [← hW]; exact hns.1
  rw [evalEval_ψ_of_equation _ hEq] at hψ
  have hψ₂ : ((shortCurve (f a) (f b)).ψ₂).evalEval x y = 2 * y := by
    rw [← WeierstrassCurve.ψ_two, ψ_milne_two, evalEval_mul, evalEval_CC, evalEval_X]
  have hP : (shortCurve (f a) (f b)).preΨ' n = ((shortCurve a b).preΨ' n).map f := by
    rw [hmap]; exact (shortCurve a b).map_preΨ' f n
  have hPn := preΨ'_ne_zero_short h h2 a b n hn
  have hEq' := hEq
  rw [WeierstrassCurve.Affine.equation_iff] at hEq'
  simp only [shortCurve] at hEq'
  have hxalg : IsAlgebraic k x := by
    by_cases hev : Even n
    · rw [if_pos hev, hψ₂] at hψ
      rcases mul_eq_zero.1 hψ with h1 | h1
      · refine ⟨_, hPn, ?_⟩
        rw [aeval_def, eval₂_eq_eval_map, ← hP]
        exact h1
      · have hy0 : y = 0 := (mul_eq_zero.1 h1).resolve_left h2Ω
        refine ⟨X ^ 3 + C a * X + C b, ?_, ?_⟩
        · intro h0
          have := congrArg (fun p => p.coeff 3) h0
          simp [coeff_X_pow, coeff_C, coeff_X] at this
        · rw [aeval_def, eval₂_add, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_C]
          subst hy0
          simp only [← hf]
          linear_combination (-1 : Ω) * hEq'
    · rw [if_neg hev, mul_one] at hψ
      refine ⟨_, hPn, ?_⟩
      rw [aeval_def, eval₂_eq_eval_map, ← hP]
      exact hψ
  obtain ⟨x₀, hx₀⟩ := algClosed_mem_range x hxalg
  refine ⟨⟨x₀, hx₀⟩, algClosed_mem_range y ?_⟩
  refine ⟨X ^ 2 - C (x₀ ^ 3 + a * x₀ + b), X_pow_sub_C_ne_zero (by norm_num) _, ?_⟩
  rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]
  have : x = f x₀ := hx₀.symm
  subst this
  simp only [map_add, map_mul, map_pow]
  linear_combination hEq'

end ShortCase

/-! ### Proposition 3.13 -/

/-- Proposition 3.13 (Milne, pdf p. 103), from Lemma 3.14: for an elliptic curve `E` over an
algebraically closed field `k` and an algebraically closed field `Ω ⊇ k`, `E(k) → E(Ω)` induces
an isomorphism on torsion subgroups: it is injective, and every torsion point of `E(Ω)` comes
from `E(k)`.  Milne's proof writes `E` as `Y² = X³ + aX + b` and uses Lemma 3.14 for that form,
which needs the characteristic to be different from `2` and `3`; the statement in that
generality is proved here, and the statement in all characteristics is recorded as the named
statement `TorsionBaseChange`. -/
@[kb "milne2006ec" "Ch. III, Prop. 3.13, pdf p. 103"]
theorem prop_3_13 (h : DivisionPolynomialFormula) {k Ω : Type} [Field k] [DecidableEq k] [IsAlgClosed k]
    [Field Ω] [DecidableEq Ω] [IsAlgClosed Ω] [Algebra k Ω] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (E : WeierstrassCurve k) [E.IsElliptic] :
    Function.Injective (WeierstrassCurve.Affine.Point.baseChange (W' := E) k Ω) ∧
      ∀ Q : (E.baseChange Ω).toAffine.Point, (∃ n : ℕ, 0 < n ∧ n • Q = 0) →
        ∃ P : E.toAffine.Point, WeierstrassCurve.Affine.Point.baseChange (W' := E) k Ω P = Q := by
  refine ⟨WeierstrassCurve.Affine.Point.map_injective _, ?_⟩
  rintro Q ⟨n, hn, hQ⟩
  rcases Q with _ | ⟨x, y, hns⟩
  · exact ⟨0, map_zero _⟩
  -- change variables to the short form `Y² = X³ + aX + b`
  let s : k := -E.a₁ / 2
  let r : k := -(E.a₂ + E.a₁ ^ 2 / 4) / 3
  let t : k := -(E.a₃ + r * E.a₁) / 2
  let C : WeierstrassCurve.VariableChange k := ⟨1, r, s, t⟩
  let E' : WeierstrassCurve k := C • E
  have hv : IsVC E E' r s t := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (C • E).a₁ = _
      rw [WeierstrassCurve.variableChange_a₁]; simp [C]
    · show (C • E).a₂ = _
      rw [WeierstrassCurve.variableChange_a₂]; simp [C]
    · show (C • E).a₃ = _
      rw [WeierstrassCurve.variableChange_a₃]; simp [C]
    · show (C • E).a₄ = _
      rw [WeierstrassCurve.variableChange_a₄]; simp [C]
    · show (C • E).a₆ = _
      rw [WeierstrassCurve.variableChange_a₆]; simp [C]
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have ha1 : E'.a₁ = 0 := by
    rw [hv.a1]; simp only [s]; field_simp; ring
  have ha2 : E'.a₂ = 0 := by
    rw [hv.a2]; simp only [s, r]; field_simp; ring
  have ha3 : E'.a₃ = 0 := by
    rw [hv.a3]; simp only [t]; field_simp; ring
  have hE' : E' = shortCurve E'.a₄ E'.a₆ := by
    ext <;> simp [shortCurve, ha1, ha2, ha3]
  haveI : E'.IsElliptic := inferInstanceAs (C • E).IsElliptic
  have hvΩ := hv.map (algebraMap k Ω)
  haveI : (E'.baseChange Ω).IsElliptic := inferInstanceAs (E'.map (algebraMap k Ω)).IsElliptic
  haveI : (E'.map (algebraMap k Ω)).IsElliptic := inferInstance
  have hQ' : n • WeierstrassCurve.Affine.Point.some (x - algebraMap k Ω r)
      (y - algebraMap k Ω s * (x - algebraMap k Ω r) - algebraMap k Ω t)
      (WeierstrassCurve.Affine.equation_iff_nonsingular.1 (hvΩ.equation hns.1)) = 0 := by
    have := map_nsmul (vcHom hvΩ) n
      (WeierstrassCurve.Affine.Point.some x y hns : (E.map (algebraMap k Ω)).toAffine.Point)
    rw [show n • (WeierstrassCurve.Affine.Point.some x y hns :
      (E.map (algebraMap k Ω)).toAffine.Point) = 0 from hQ, map_zero] at this
    exact this.symm
  obtain ⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩ := torsion_coords_short h (Ω := Ω) h2 E'.a₄ E'.a₆ E' hE' _ _ _ n hn hQ'
  have hx0 : algebraMap k Ω (x₁ + r) = x := by
    rw [map_add, hx₁]; ring
  have hy0 : algebraMap k Ω (y₁ + s * x₁ + t) = y := by
    rw [map_add, map_add, map_mul, hx₁, hy₁]; ring
  subst hx0 hy0
  have h₀ : E.toAffine.Nonsingular (x₁ + r) (y₁ + s * x₁ + t) :=
    (WeierstrassCurve.Affine.map_nonsingular (W := E.toAffine) (f := algebraMap k Ω)
      (algebraMap k Ω).injective _ _).1 hns
  exact ⟨.some _ _ h₀, rfl⟩

/-- **Proposition 3.13 in every characteristic** (Milne, pdf p. 103), as a named statement:
Milne's proof covers only characteristic different from `2` and `3` (`prop_3_13`). -/
@[kb "milne2006ec" "Ch. III, Prop. 3.13, pdf p. 103"]
structure TorsionBaseChange : Prop where
  bijective : ∀ (k Ω : Type) [Field k] [DecidableEq k] [IsAlgClosed k] [Field Ω] [DecidableEq Ω]
    [IsAlgClosed Ω] [Algebra k Ω]
    (E : WeierstrassCurve k) [E.IsElliptic], ∀ Q : (E.baseChange Ω).toAffine.Point,
      (∃ n : ℕ, 0 < n ∧ n • Q = 0) →
        ∃ P : E.toAffine.Point, WeierstrassCurve.Affine.Point.baseChange (W' := E) k Ω P = Q

/-! ### Remark 3.16 (named statement) -/

/-- **Remark 3.16** (Milne, pdf p. 104), as a named statement: let `E` be an elliptic curve over
an algebraically closed field `k` of characteristic `p ≠ 0`.  Theorem 3.12 holds for `n` prime to
`p`; and for powers of `p`, either `E` has no points of order `p` (the supersingular case), or
`E` has `p^m` points of order dividing `p^m` for every `m ≥ 1` (the ordinary case). -/
@[kb "milne2006ec" "Ch. III, Rem. 3.16, pdf p. 104"]
structure TorsionCharP : Prop where
  prime_to_p : ∀ (k : Type) [Field k] [DecidableEq k] [IsAlgClosed k] (p : ℕ) [CharP k p], p ≠ 0 →
    ∀ (E : WeierstrassCurve k) [E.IsElliptic] (n : ℕ), 0 < n → n.Coprime p →
      Nonempty (AddSubgroup.torsionBy E.toAffine.Point n ≃+ ZMod n × ZMod n)
  p_power : ∀ (k : Type) [Field k] [DecidableEq k] [IsAlgClosed k] (p : ℕ) [CharP k p], p ≠ 0 →
    ∀ (E : WeierstrassCurve k) [E.IsElliptic],
      AddSubgroup.torsionBy E.toAffine.Point p = ⊥ ∨
        ∀ m : ℕ, 1 ≤ m → Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p ^ m)) = p ^ m

/-- The supersingular case of Remark 3.16 has no nonzero `p`-power torsion at all. -/
theorem TorsionCharP.torsionBy_pow_eq_bot {k : Type} [Field k] [DecidableEq k] {p : ℕ} [Fact p.Prime]
    {E : WeierstrassCurve k} [E.IsElliptic]
    (hp : AddSubgroup.torsionBy E.toAffine.Point p = ⊥) (m : ℕ) :
    AddSubgroup.torsionBy E.toAffine.Point (p ^ m) = ⊥ := by
  induction m with
  | zero =>
    ext x
    simp only [pow_zero, Nat.cast_one, AddSubgroup.mem_bot]
    rw [show ((1 : ℤ)) = ((1 : ℕ) : ℤ) by simp, AddSubgroup.torsionBy.nsmul_iff]
    simp
  | succ m ih =>
    rw [eq_bot_iff]
    intro x hx
    have hx' : (p ^ (m + 1) : ℕ) • x = 0 := by
      have := (AddSubgroup.torsionBy.nsmul_iff (n := p ^ (m + 1))).1 (by exact_mod_cast hx)
      exact this
    have h1 : p • x ∈ AddSubgroup.torsionBy E.toAffine.Point (p ^ m : ℕ) := by
      rw [AddSubgroup.torsionBy.nsmul_iff, ← mul_nsmul', ← pow_succ]
      exact hx'
    have h1' : p • x = 0 := by
      have : p • x ∈ (⊥ : AddSubgroup E.toAffine.Point) := by
        rw [← ih]; exact_mod_cast h1
      simpa using this
    have h2 : x ∈ AddSubgroup.torsionBy E.toAffine.Point (p : ℕ) :=
      AddSubgroup.torsionBy.nsmul_iff.2 h1'
    rw [show ((p : ℕ) : ℤ) = (p : ℤ) from rfl, hp] at h2
    exact h2

end NumberFieldKB.MilneEC.III
