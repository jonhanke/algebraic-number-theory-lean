import NumberFieldKB.MilneEC.Ch3Curve
import NumberFieldKB.MilneEC.Ch3Torsion
import NumberFieldKB.MilneEC.Ch3JInvariant
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Milne, Elliptic Curves, Chapter III §3: torsion points over `ℂ` and Theorem 3.12

The torsion of `ℂ/Λ` (pdf p. 103) and Theorem 3.12 of Milne, *Elliptic Curves* (`milne2006ec`):
over `ℂ` unconditionally (from `ℂ/Λ ≅ E(Λ)(ℂ)` and Theorem 3.10), and over an algebraically
closed field of characteristic zero from Lemma 3.14 (the named statement
`DivisionPolynomialFormula`), by Milne's argument: the curve is defined over an algebraically
closed subfield `k₀` of finite transcendence degree over `ℚ`, which embeds in `ℂ`, and
Proposition 3.13 is applied twice.
-/

namespace NumberFieldKB.MilneEC.III

/-! ### Torsion of `ℂ/Λ` (pdf p. 103) -/

open PeriodPair in
theorem lat_uniq (L : PeriodPair) {a b c d : ℤ}
    (h : (a : ℂ) * L.ω₁ + b * L.ω₂ = c * L.ω₁ + d * L.ω₂) : a = c ∧ b = d := by
  have h' : L.latticeEquivProd.symm (a, b) = L.latticeEquivProd.symm (c, d) :=
    Subtype.ext (by rw [L.latticeEquiv_symm_apply, L.latticeEquiv_symm_apply]; exact h)
  have := L.latticeEquivProd.symm.injective h'
  simpa [Prod.ext_iff] using this

/-- The quotient map `ℂ → ℂ/Λ` as an additive homomorphism. -/
noncomputable def qmk (L : PeriodPair) : ℂ →+ ℂ ⧸ L.lattice :=
  (Submodule.mkQ L.lattice).toAddMonoidHom

theorem qmk_eq (L : PeriodPair) (z : ℂ) : qmk L z = 0 ↔ z ∈ L.lattice :=
  Submodule.Quotient.mk_eq_zero _

/-- The homomorphism `ℤ/n → ℂ/Λ`, `a ↦ aω/n`, for a period `ω`. -/
noncomputable def divHom (L : PeriodPair) (n : ℕ) (hn : 0 < n) (ω : ℂ) (hω : ω ∈ L.lattice) :
    ZMod n →+ ℂ ⧸ L.lattice :=
  ZMod.lift n ⟨zmultiplesHom _ (qmk L (ω / n)), by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [zmultiplesHom_apply]
    rw [← map_zsmul, qmk_eq]
    simpa [zsmul_eq_mul, mul_div_cancel₀ _ hn'] using hω⟩

theorem divHom_intCast (L : PeriodPair) (n : ℕ) (hn : 0 < n) (ω : ℂ) (hω : ω ∈ L.lattice)
    (a : ℤ) : divHom L n hn ω hω (a : ZMod n) = qmk L (a * ω / n) := by
  simp only [divHom, ZMod.lift_coe, zmultiplesHom_apply]
  rw [← map_zsmul]
  congr 1
  simp [zsmul_eq_mul]
  ring

/-- Milne (pdf p. 103): `(ℂ/Λ)ₙ = n⁻¹Λ/Λ` is a free `ℤ/nℤ`-module of rank `2`. -/
@[kb "milne2006ec" "Ch. III, §3, E(C)_n ≅ (n⁻¹Λ)/Λ free of rank 2 over Z/nZ, pdf p. 103"]
theorem torsionBy_quotient (L : PeriodPair) (n : ℕ) (hn : 0 < n) :
    Nonempty (AddSubgroup.torsionBy (ℂ ⧸ L.lattice) n ≃+ ZMod n × ZMod n) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let F : ZMod n × ZMod n →+ ℂ ⧸ L.lattice :=
    (divHom L n hn L.ω₁ L.ω₁_mem_lattice).coprod (divHom L n hn L.ω₂ L.ω₂_mem_lattice)
  have hF : ∀ a b : ℤ, F ((a : ZMod n), (b : ZMod n)) = qmk L ((a * L.ω₁ + b * L.ω₂) / n) := by
    intro a b
    simp only [F, AddMonoidHom.coprod_apply, divHom_intCast, ← map_add]
    congr 1
    ring
  have hmem : ∀ x, F x ∈ AddSubgroup.torsionBy (ℂ ⧸ L.lattice) n := by
    intro x
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective x.1
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective x.2
    have : x = ((a : ZMod n), (b : ZMod n)) := by ext <;> simp [ha, hb]
    subst this
    rw [AddSubgroup.torsionBy.nsmul_iff, hF, ← map_nsmul, qmk_eq]
    refine L.mem_lattice.2 ⟨a, b, ?_⟩
    simp [nsmul_eq_mul, mul_div_cancel₀ _ hn']
  let G : ZMod n × ZMod n →+ AddSubgroup.torsionBy (ℂ ⧸ L.lattice) n := F.codRestrict _ hmem
  have hbij : Function.Bijective G := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, ha⟩ := ZMod.intCast_surjective x.1
      obtain ⟨b, hb⟩ := ZMod.intCast_surjective x.2
      have : x = ((a : ZMod n), (b : ZMod n)) := by ext <;> simp [ha, hb]
      subst this
      have h0 : F ((a : ZMod n), (b : ZMod n)) = 0 := congrArg Subtype.val hx
      rw [hF, qmk_eq] at h0
      obtain ⟨c, d, hcd⟩ := L.mem_lattice.1 h0
      have h1 : (a : ℂ) * L.ω₁ + b * L.ω₂ =
          ((n * c : ℤ) : ℂ) * L.ω₁ + ((n * d : ℤ) : ℂ) * L.ω₂ := by
        push_cast
        have : ((c : ℂ) * L.ω₁ + d * L.ω₂) * n = (a * L.ω₁ + b * L.ω₂) := by
          rw [hcd]; field_simp
        linear_combination -this
      obtain ⟨e1, e2⟩ := lat_uniq L h1
      subst e1 e2
      ext <;> simp
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective L.lattice z
      have hz' : n • (Submodule.Quotient.mk w : ℂ ⧸ L.lattice) = 0 :=
        AddSubgroup.torsionBy.nsmul_iff.1 hz
      have hw : qmk L ((n : ℂ) * w) = 0 := by
        have : qmk L ((n : ℂ) * w) = n • (Submodule.Quotient.mk w : ℂ ⧸ L.lattice) := by
          have := map_nsmul (qmk L) n w
          rw [nsmul_eq_mul] at this
          rw [this]; rfl
        rw [this, hz']
      obtain ⟨c, d, hcd⟩ := L.mem_lattice.1 ((qmk_eq L _).1 hw)
      refine ⟨((c : ZMod n), (d : ZMod n)), Subtype.ext ?_⟩
      show F _ = _
      rw [hF]
      have : (c * L.ω₁ + d * L.ω₂) / n = w := by
        rw [hcd]; field_simp
      rw [this]; rfl
  exact ⟨(AddEquiv.ofBijective G hbij).symm⟩

/-! ### Point maps for changes of variables with scaling -/

section Scaling

open WeierstrassCurve WeierstrassCurve.Affine

/-- Coefficient relations of a scaling `x = u² x'`, `y = u³ y'`. -/
structure IsSc {F : Type*} [CommRing F] (W W' : WeierstrassCurve F) (u : F) : Prop where
  a1 : W'.a₁ * u = W.a₁
  a2 : W'.a₂ * u ^ 2 = W.a₂
  a3 : W'.a₃ * u ^ 3 = W.a₃
  a4 : W'.a₄ * u ^ 4 = W.a₄
  a6 : W'.a₆ * u ^ 6 = W.a₆

section
variable {F : Type*} [Field F] [DecidableEq F] {W W' : WeierstrassCurve F} {u : F}

omit [DecidableEq F] in
theorem IsSc.equation (hv : IsSc W W' u) (hu : u ≠ 0) {x y : F} (h : W.toAffine.Equation x y) :
    W'.toAffine.Equation (x / u ^ 2) (y / u ^ 3) := by
  rw [equation_iff] at h ⊢
  rw [← hv.a1, ← hv.a2, ← hv.a3, ← hv.a4, ← hv.a6] at h
  field_simp
  linear_combination h

omit [DecidableEq F] in
theorem IsSc.negY (hv : IsSc W W' u) (hu : u ≠ 0) (x y : F) :
    W'.toAffine.negY (x / u ^ 2) (y / u ^ 3) = W.toAffine.negY x y / u ^ 3 := by
  simp only [Affine.negY, ← hv.a1, ← hv.a3]
  field_simp

omit [DecidableEq F] in
theorem IsSc.addX (hv : IsSc W W' u) (hu : u ≠ 0) (x₁ x₂ L : F) :
    W'.toAffine.addX (x₁ / u ^ 2) (x₂ / u ^ 2) (L / u) = W.toAffine.addX x₁ x₂ L / u ^ 2 := by
  simp only [Affine.addX, ← hv.a1, ← hv.a2]
  field_simp

theorem IsSc.addY (hv : IsSc W W' u) (hu : u ≠ 0) (x₁ x₂ y₁ L : F) :
    W'.toAffine.addY (x₁ / u ^ 2) (x₂ / u ^ 2) (y₁ / u ^ 3) (L / u) =
      W.toAffine.addY x₁ x₂ y₁ L / u ^ 3 := by
  simp only [Affine.addY, Affine.negAddY, hv.addX hu]
  simp only [Affine.negY, Affine.addX, ← hv.a1, ← hv.a3, ← hv.a2]
  field_simp

theorem IsSc.slope (hv : IsSc W W' u) (hu : u ≠ 0) {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂))
    (hD : x₁ = x₂ → y₁ - W.toAffine.negY x₁ y₁ ≠ 0) :
    W'.toAffine.slope (x₁ / u ^ 2) (x₂ / u ^ 2) (y₁ / u ^ 3) (y₂ / u ^ 3) =
      W.toAffine.slope x₁ x₂ y₁ y₂ / u := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    have hD' := hD hx
    subst hx
    have hy' : y₁ / u ^ 3 ≠ W'.toAffine.negY (x₁ / u ^ 2) (y₂ / u ^ 3) := by
      rw [hv.negY hu]
      intro h
      apply hy
      field_simp at h
      exact h
    rw [Affine.slope_of_Y_ne rfl hy', Affine.slope_of_Y_ne rfl hy, hv.negY hu]
    have hne : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := hD'
    have e : y₁ / u ^ 3 - W.toAffine.negY x₁ y₁ / u ^ 3 =
        (y₁ - W.toAffine.negY x₁ y₁) / u ^ 3 := by ring
    rw [e]
    simp only [Affine.negY, ← hv.a1, ← hv.a2, ← hv.a3, ← hv.a4] at hne ⊢
    have hu3 : u ^ 3 ≠ 0 := pow_ne_zero _ hu
    field_simp
  · have hx' : x₁ / u ^ 2 ≠ x₂ / u ^ 2 := by
      intro h
      apply hx
      field_simp at h
      exact h
    rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx]
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
    field_simp

/-- The point map of a scaling. -/
noncomputable def scPoint (hv : IsSc W W' u) (hu : u ≠ 0) [W'.IsElliptic] :
    W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (x / u ^ 2) (y / u ^ 3)
      (equation_iff_nonsingular.1 (hv.equation hu h.1))

theorem scPoint_add (hv : IsSc W W' u) (hu : u ≠ 0) [W'.IsElliptic]
    (P Q : W.toAffine.Point) : scPoint hv hu (P + Q) = scPoint hv hu P + scPoint hv hu Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · have h0 : scPoint hv hu (0 : W.toAffine.Point) = 0 := rfl
    show scPoint hv hu (0 + Q) = scPoint hv hu 0 + scPoint hv hu Q
    rw [zero_add, h0, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · have h0 : scPoint hv hu (0 : W.toAffine.Point) = 0 := rfl
    show scPoint hv hu (_ + 0) = scPoint hv hu _ + scPoint hv hu 0
    rw [add_zero, h0, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · obtain ⟨rfl, hy⟩ := hxy
    rw [Point.add_of_Y_eq rfl hy]
    have : scPoint hv hu (Point.some x₁ y₁ h₁) + scPoint hv hu (Point.some x₁ y₂ h₂) = 0 := by
      simp only [scPoint]
      apply Point.add_of_Y_eq rfl
      rw [hv.negY hu, hy]
    rw [this]
    rfl
  · have hD : x₁ = x₂ → y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := by
      intro hx
      have hy : y₁ ≠ W.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      have := Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hx hy
      subst hx this
      exact sub_ne_zero.2 hy
    have hxy' : ¬(x₁ / u ^ 2 = x₂ / u ^ 2 ∧
        y₁ / u ^ 3 = W'.toAffine.negY (x₂ / u ^ 2) (y₂ / u ^ 3)) := by
      rintro ⟨h1, h2⟩
      apply hxy
      have hx : x₁ = x₂ := by field_simp at h1; exact h1
      refine ⟨hx, ?_⟩
      subst hx
      rw [hv.negY hu] at h2
      field_simp at h2
      exact h2
    rw [Point.add_some hxy]
    simp only [scPoint]
    rw [Point.add_some hxy']
    simp only [Point.some.injEq]
    rw [hv.slope hu hxy hD, hv.addX hu, hv.addY hu]
    exact ⟨rfl, rfl⟩

/-- The point map of a scaling, as a group homomorphism. -/
noncomputable def scHom (hv : IsSc W W' u) (hu : u ≠ 0) [W'.IsElliptic] :
    W.toAffine.Point →+ W'.toAffine.Point :=
  AddMonoidHom.mk' (scPoint hv hu) (scPoint_add hv hu)

theorem scPoint_injective (hv : IsSc W W' u) (hu : u ≠ 0) [W'.IsElliptic] :
    Function.Injective (scPoint hv hu) := by
  intro P Q h
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · exact absurd h (by simp [scPoint])
  · exact absurd h (by simp [scPoint])
  · simp only [scPoint, Point.some.injEq] at h
    have hu2 : u ^ 2 ≠ 0 := pow_ne_zero _ hu
    have hu3 : u ^ 3 ≠ 0 := pow_ne_zero _ hu
    obtain ⟨e1, e2⟩ := h
    rw [div_left_inj' hu2] at e1
    rw [div_left_inj' hu3] at e2
    subst e1 e2
    rfl

theorem scPoint_surjective (hv : IsSc W W' u) (hu : u ≠ 0) [W.IsElliptic] [W'.IsElliptic] :
    Function.Surjective (scPoint hv hu) := by
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero _ hu
  have hu3 : u ^ 3 ≠ 0 := pow_ne_zero _ hu
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, rfl⟩
  · have h' : W.toAffine.Equation (x * u ^ 2) (y * u ^ 3) := by
      replace h := (equation_iff _ _).1 h.1
      rw [equation_iff]
      rw [← hv.a1, ← hv.a2, ← hv.a3, ← hv.a4, ← hv.a6]
      linear_combination u ^ 6 * h
    refine ⟨.some (x * u ^ 2) (y * u ^ 3) (equation_iff_nonsingular.1 h'), ?_⟩
    simp only [scPoint, Point.some.injEq]
    constructor <;> field_simp
end

section
variable {F : Type*} [Field F] {W W' : WeierstrassCurve F} {r s t : F}

theorem vcPoint_bijective (hv : IsVC W W' r s t) [W.IsElliptic] [W'.IsElliptic] :
    Function.Bijective (vcPoint hv) := by
  constructor
  · intro P Q h
    rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
    · rfl
    · exact absurd h (by simp [vcPoint])
    · exact absurd h (by simp [vcPoint])
    · simp only [vcPoint, Point.some.injEq] at h
      obtain ⟨e1, e2⟩ := h
      have ex : x₁ = x₂ := by linear_combination e1
      subst ex
      have ey : y₁ = y₂ := by linear_combination e2
      subst ey
      rfl
  · rintro (_ | ⟨x, y, h⟩)
    · exact ⟨0, rfl⟩
    · have h' : W.toAffine.Equation (x + r) (y + s * x + t) := by
        have h1 := (equation_iff _ _).1 h.1
        rw [equation_iff, hv.a1, hv.a2, hv.a3, hv.a4, hv.a6] at *
        linear_combination h1
      refine ⟨.some (x + r) (y + s * x + t) (equation_iff_nonsingular.1 h'), ?_⟩
      simp only [vcPoint, Point.some.injEq]
      constructor <;> ring

end

end Scaling

/-- Any variable change `C` induces a group isomorphism `E(F) ≃ (C • E)(F)`. -/
theorem nonempty_equiv_varChange {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
    [E.IsElliptic] (C : WeierstrassCurve.VariableChange F) :
    Nonempty (E.toAffine.Point ≃+ (C • E).toAffine.Point) := by
  let W₁ : WeierstrassCurve F := (⟨1, C.r, C.s, C.t⟩ : WeierstrassCurve.VariableChange F) • E
  have hv : IsVC E W₁ C.r C.s C.t := by
    constructor <;> simp [W₁, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hsc : IsSc W₁ (C • E) (C.u : F) := by
    constructor
    · simp [W₁, WeierstrassCurve.variableChange_a₁]
      field_simp
    · simp [W₁, WeierstrassCurve.variableChange_a₂]
      field_simp
    · simp [W₁, WeierstrassCurve.variableChange_a₃]
      field_simp
    · simp [W₁, WeierstrassCurve.variableChange_a₄]
      field_simp
    · simp [W₁, WeierstrassCurve.variableChange_a₆]
      field_simp
  have hb : Function.Bijective ((scHom hsc hu).comp (vcHom hv)) :=
    Function.Bijective.comp (g := scPoint hsc hu) (f := vcPoint hv)
      ⟨scPoint_injective hsc hu, scPoint_surjective hsc hu⟩ (vcPoint_bijective hv)
  exact ⟨AddEquiv.ofBijective _ hb⟩

/-! ### Transport of torsion -/

theorem torsion_equiv_of_inj {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)
    (hf : Function.Injective f) (hs : ∀ h : H, (∃ n : ℕ, 0 < n ∧ n • h = 0) → ∃ g, f g = h)
    (n : ℕ) (hn : 0 < n) :
    Nonempty (AddSubgroup.torsionBy G n ≃+ AddSubgroup.torsionBy H n) := by
  have hmem : ∀ g : AddSubgroup.torsionBy G n, f g ∈ AddSubgroup.torsionBy H n := by
    rintro ⟨g, hg⟩
    rw [AddSubgroup.torsionBy.nsmul_iff] at hg ⊢
    rw [← map_nsmul, hg, map_zero]
  let F : AddSubgroup.torsionBy G n →+ AddSubgroup.torsionBy H n :=
    (f.comp (AddSubgroup.torsionBy G n).subtype).codRestrict _ hmem
  refine ⟨AddEquiv.ofBijective F ⟨?_, ?_⟩⟩
  · intro a b hab
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hab
  · rintro ⟨h, hh⟩
    obtain ⟨g, rfl⟩ := hs h ⟨n, hn, AddSubgroup.torsionBy.nsmul_iff.1 hh⟩
    refine ⟨⟨g, ?_⟩, rfl⟩
    rw [AddSubgroup.torsionBy.nsmul_iff]
    apply hf
    rw [map_nsmul, map_zero]
    exact AddSubgroup.torsionBy.nsmul_iff.1 hh

theorem torsion_equiv_of_equiv {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    (n : ℕ) (hn : 0 < n) :
    Nonempty (AddSubgroup.torsionBy G n ≃+ AddSubgroup.torsionBy H n) :=
  torsion_equiv_of_inj e.toAddMonoidHom e.injective (fun h _ => ⟨e.symm h, e.apply_symm_apply h⟩) n hn

/-- Theorem 3.12 over `ℂ` (Milne, pdf p. 103): for an elliptic curve `E` over `ℂ`, `E(ℂ)ₙ` is a
free `ℤ/nℤ`-module of rank `2`. -/
@[kb "milne2006ec" "Ch. III, Thm. 3.12 (k = C), pdf p. 103"]
theorem thm_3_12_complex (E : WeierstrassCurve ℂ) [E.IsElliptic] (n : ℕ) (hn : 0 < n) :
    Nonempty (AddSubgroup.torsionBy E.toAffine.Point n ≃+ ZMod n × ZMod n) := by
  obtain ⟨L, C, hC⟩ := thm_3_10 E
  obtain ⟨e₁⟩ := nonempty_equiv_varChange E C
  rw [hC] at e₁
  obtain ⟨t₁⟩ := torsion_equiv_of_equiv e₁ n hn
  obtain ⟨t₂⟩ := torsion_equiv_of_equiv (quotEquivCurve L).symm n hn
  obtain ⟨t₃⟩ := torsionBy_quotient L n hn
  exact ⟨t₁.trans (t₂.trans t₃)⟩

/-! ### Embedding of a finite-transcendence-degree algebraically closed field into `ℂ` -/

open Cardinal in
theorem exists_ringHom_complex (A : Type) [Field A] [CharZero A] [IsAlgClosed A]
    [FinTrdeg ℚ A] : Nonempty (A →+* ℂ) := by
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis ℚ A
  obtain ⟨T, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hbig : ℵ₀ < #ℂ := by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]
  have hcard : #T = #ℂ :=
    (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
      (v' := ((↑) : T → ℂ)) ht (by simp) hbig).symm
  have hle : #s ≤ #T := by
    rw [hcard]
    have : #s < ℵ₀ := Cardinal.mk_lt_aleph0
    exact (this.trans hbig).le
  obtain ⟨f⟩ := Cardinal.le_def _ _ |>.1 hle
  have hg : AlgebraicIndependent ℚ (fun i : s => ((f i : T) : ℂ)) := ht.1.comp f f.injective
  let R := Algebra.adjoin ℚ (Set.range ((↑) : s → A))
  let φ : R →+* ℂ :=
    (MvPolynomial.aeval (fun i : s => ((f i : T) : ℂ)) : MvPolynomial s ℚ →ₐ[ℚ] ℂ).toRingHom.comp
      hs.1.aevalEquiv.symm.toRingEquiv.toRingHom
  have hφ : Function.Injective φ := by
    intro a b h
    apply hs.1.aevalEquiv.symm.injective
    exact hg h
  letI : Algebra R ℂ := φ.toAlgebra
  have : IsAlgClosure R A := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  have hfs : FaithfulSMul R ℂ := (faithfulSMul_iff_algebraMap_injective R ℂ).2 hφ
  have hfaith : Module.IsTorsionFree R ℂ := inferInstance
  have := this.isAlgebraic
  exact ⟨((IsAlgClosed.lift (R := R) (S := A) (M := ℂ)) : A →ₐ[R] ℂ).toRingHom⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- Theorem 3.12 (Milne, pdf p. 103), from Lemma 3.14: for an elliptic curve `E` over an
algebraically closed field `k` of characteristic zero, `E(k)ₙ` is a free `ℤ/nℤ`-module of rank
`2`.  (Over `ℂ` this is `thm_3_12_complex`, unconditional.) -/
@[kb "milne2006ec" "Ch. III, Thm. 3.12, pdf p. 103"]
theorem thm_3_12 (h : DivisionPolynomialFormula) {k : Type} [Field k] [DecidableEq k] [IsAlgClosed k]
    [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic] (n : ℕ) (hn : 0 < n) :
    Nonempty (AddSubgroup.torsionBy E.toAffine.Point n ≃+ ZMod n × ZMod n) := by
  classical
  let S : Set k := {E.a₁, E.a₂, E.a₃, E.a₄, E.a₆}
  let F := IntermediateField.adjoin ℚ S
  let A := algebraicClosure F k
  have : IsAlgClosure F A := inferInstance
  have : IsAlgClosed A := IsAlgClosure.isAlgClosed F
  have : CharZero A := (RingHom.charZero_iff (algebraMap A k).injective).2 inferInstance
  have : FinTrdeg ℚ F := inferInstance
  have : FinTrdeg F A := inferInstance
  have : FinTrdeg ℚ A := FinTrdeg.trans ℚ F A
  obtain ⟨σ⟩ := exists_ringHom_complex A
  have hmem : ∀ x ∈ S, x ∈ A := fun x hx =>
    (mem_algebraicClosure_iff).2
      (isAlgebraic_algebraMap (⟨x, IntermediateField.subset_adjoin ℚ S hx⟩ : F))
  let E₀ : WeierstrassCurve A :=
    ⟨⟨E.a₁, hmem _ (by simp [S])⟩, ⟨E.a₂, hmem _ (by simp [S])⟩, ⟨E.a₃, hmem _ (by simp [S])⟩,
      ⟨E.a₄, hmem _ (by simp [S])⟩, ⟨E.a₆, hmem _ (by simp [S])⟩⟩
  have hE : E₀.baseChange k = E := by
    cases E; rfl
  have hell : E₀.IsElliptic := by
    have h1 := (WeierstrassCurve.isElliptic_iff E).1 inferInstance
    rw [← hE, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ] at h1
    rw [WeierstrassCurve.isElliptic_iff]
    rw [isUnit_iff_ne_zero] at h1 ⊢
    intro h0
    apply h1
    rw [h0, map_zero]
  letI : Algebra A ℂ := σ.toAlgebra
  have hellC : (E₀.baseChange ℂ).IsElliptic := by
    have hΔ : E₀.Δ ≠ 0 := by
      have := (WeierstrassCurve.isElliptic_iff E₀).1 hell
      exact this.ne_zero
    rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ,
      isUnit_iff_ne_zero]
    exact (map_ne_zero _).2 hΔ
  have h2 : (2 : A) ≠ 0 := two_ne_zero
  have h3 : (3 : A) ≠ 0 := three_ne_zero
  obtain ⟨hinj1, hsurj1⟩ := prop_3_13 h (k := A) (Ω := k) h2 h3 E₀
  obtain ⟨hinj2, hsurj2⟩ := prop_3_13 h (k := A) (Ω := ℂ) h2 h3 E₀
  obtain ⟨e₁⟩ := torsion_equiv_of_inj _ hinj1 hsurj1 n hn
  obtain ⟨e₂⟩ := torsion_equiv_of_inj _ hinj2 hsurj2 n hn
  obtain ⟨e₃⟩ := thm_3_12_complex (E₀.baseChange ℂ) n hn
  have key : Nonempty
      (AddSubgroup.torsionBy (E₀.baseChange k).toAffine.Point n ≃+ ZMod n × ZMod n) :=
    ⟨e₁.symm.trans (e₂.trans e₃)⟩
  rwa [hE] at key

end NumberFieldKB.MilneEC.III
