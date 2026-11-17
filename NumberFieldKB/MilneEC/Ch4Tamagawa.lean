import NumberFieldKB.FormalConjectures.EllipticCurve
import NumberFieldKB.MilneEC.Ch4MinimalTransport
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange

/-!
# Local Tamagawa numbers: independence of the model, transport, and good reduction

Formal Conjectures' local Tamagawa number `tamagawaNumber K W` of an integral Weierstrass model `W` over a discrete
valuation ring `R` with fraction field `K` is the number of translates of the set $E_0(K)$ of points with
non-singular reduction (`nonsingularReduction`). Here:

* `mem_nonsingularReduction_iff`: $P = (x, y) \in E_0(K)$ iff $x \notin R$ (then $P$ reduces to the point at
  infinity) or $x, y \in R$ and $(\bar x, \bar y)$ is non-singular on the reduction; the point at infinity is in
  $E_0(K)$.
* `tamagawaNumber_eq_of_addEquiv`: a group isomorphism of points carrying $E_0$ onto $E_0$ preserves the number.
* `tamagawaNumber_variableChange`: an integral change of variables preserves it.
* `tamagawaNumber_map_ringEquiv`: so does an isomorphism of discrete valuation rings.
* `tamagawaNumber_minimal_eq`: so any two minimal models give the same number.
* `tamagawaNumber_eq_one_of_hasGoodReduction`: $c_v = 1$ for a model with good reduction.
-/

open WeierstrassCurve WeierstrassCurve.Projective IsDiscreteValuationRing IsLocalRing

namespace NumberFieldKB.MilneEC.Tamagawa

open FormalConjectures

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- A `y` over an integral `x` on a Weierstrass equation is integral. -/
lemma exists_integral_y (W : WeierstrassCurve R) (x y : K) (h : (W⁄K).toAffine.Equation x y) (a : R)
    (ha : algebraMap R K a = x) : ∃ b : R, algebraMap R K b = y := by
  have hint : IsIntegral R y := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (W.a₁ * a + W.a₃) * Polynomial.X
      - Polynomial.C (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆), ?_, ?_⟩
    · monicity!
    · rw [Affine.equation_iff] at h
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow, map_add, map_mul, map_pow]
      subst ha
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
      linear_combination h
  exact IsIntegrallyClosed.isIntegral_iff.1 hint

/-- An element of `K` not coming from `R` has inverse in the maximal ideal of `R`. -/
lemma exists_inv_of_not_integer (z : K) (hz : ¬ ∃ a : R, algebraMap R K a = z) :
    ∃ b : R, algebraMap R K b = z⁻¹ ∧ residue R b = 0 := by
  have h := (ValuationRing.isFractionRing_iff (𝒪 := R) (K := K)).1 inferInstance
  obtain ⟨a, ha | ha⟩ := h.1 z
  · exact absurd ⟨a, ha.symm⟩ hz
  · refine ⟨a, ha.symm, ?_⟩
    rw [residue_eq_zero_iff]
    intro hu
    apply hz
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    refine ⟨v, ?_⟩
    have : algebraMap R K a * algebraMap R K v = 1 := by rw [← map_mul, hv, map_one]
    rw [← ha] at this
    have h0 : z ≠ 0 := fun h0 => hz ⟨0, by simp [h0]⟩
    exact ((inv_mul_eq_one₀ h0).1 this).symm

/-- A point of the model with non-integral `x` has an integral representative reducing to `(0, 1, 0)`. -/
lemma exists_integral_rep_of_not_integer (W : WeierstrassCurve R) (x y : K)
    (h : (W⁄K).toAffine.Equation x y) (hx : ¬ ∃ a : R, algebraMap R K a = x) :
    y ≠ 0 ∧ ∃ q : Fin 3 → R, (fun i => algebraMap R K (q i)) = y⁻¹ • ![x, y, 1] ∧
      (fun i => residue R (q i)) = ![0, 1, 0] := by
  have hx0 : x ≠ 0 := fun h0 => hx ⟨0, by simp [h0]⟩
  obtain ⟨σ, hσ, -⟩ := exists_inv_of_not_integer x hx
  have ht : ¬ ∃ c : R, algebraMap R K c = y / x := by
    rintro ⟨c, hc⟩
    apply hx
    refine ⟨c ^ 2 + W.a₁ * c + W.a₃ * σ * c - W.a₂ - W.a₄ * σ - W.a₆ * σ ^ 2, ?_⟩
    rw [Affine.equation_iff] at h
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
    simp only [map_sub, map_add, map_mul, map_pow, hc, hσ]
    have hy : y = y / x * x := by field_simp
    generalize y / x = t at hy hc ⊢
    subst hy
    field_simp
    linear_combination h
  have ht0 : y / x ≠ 0 := fun h0 => ht ⟨0, by simp [h0]⟩
  have hy0 : y ≠ 0 := fun h0 => ht0 (by simp [h0])
  obtain ⟨τ, hτ, hτ0⟩ := exists_inv_of_not_integer (y / x) ht
  refine ⟨hy0, ![τ, 1, σ * τ], ?_, ?_⟩
  · ext i
    fin_cases i
    · simp [hτ]; field_simp
    · simp; field_simp
    · simp [hτ, hσ]; field_simp
  · ext i
    fin_cases i <;> simp [hτ0]

open scoped Classical in
/-- **The points with non-singular reduction, in affine coordinates.** The point at infinity always lies in
$E_0(K)$; an affine point $(x, y)$ lies in it iff $x \notin R$ or ($x, y \in R$ and the reduction of $(x, y)$ is
non-singular). -/
theorem mem_nonsingularReduction_iff (W : WeierstrassCurve R) (P : (W.toProjective⁄K).Point) :
    P ∈ nonsingularReduction K W.toProjective ↔
      ∀ (x y : K) (h : (W⁄K).toAffine.Nonsingular x y),
        Projective.Point.toAffineLift P = Affine.Point.some x y h →
          (¬ ∃ a : R, algebraMap R K a = x) ∨
            ∃ a b : R, algebraMap R K a = x ∧ algebraMap R K b = y ∧
              (W.map (residue R)).toAffine.Nonsingular (residue R a) (residue R b) := by
  constructor
  · rintro ⟨q, hq, hqs⟩ x y h hxy
    rcases P with @⟨pt, hpt⟩
    simp only at hq
    subst hq
    rw [Projective.Point.toAffineLift_eq] at hxy
    have hq2 : algebraMap R K (q 2) ≠ 0 := by
      intro h0
      rw [Projective.Point.toAffine_of_Z_eq_zero h0] at hxy
      exact absurd hxy (by simp)
    rw [Projective.Point.toAffine_of_Z_ne_zero ((Projective.nonsingularLift_iff _).1 hpt) hq2] at hxy
    simp only [Affine.Point.some.injEq] at hxy
    obtain ⟨hx, hy⟩ := hxy
    by_cases hu : IsUnit (q 2)
    · right
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have hvK : algebraMap R K v = (algebraMap R K (q 2))⁻¹ :=
        eq_inv_of_mul_eq_one_right (by rw [← map_mul, hv, map_one])
      refine ⟨v * q 0, v * q 1, ?_, ?_, ?_⟩
      · simp only [map_mul, hvK, ← hx]
        simp [div_eq_inv_mul]
      · simp only [map_mul, hvK, ← hy]
        simp [div_eq_inv_mul]
      · have hz : residue R (q 2) ≠ 0 := fun h0 =>
          (IsLocalRing.notMem_maximalIdeal.2 hu) ((residue_eq_zero_iff _).1 h0)
        have hvr : residue R v = (residue R (q 2))⁻¹ :=
          eq_inv_of_mul_eq_one_right (by rw [← map_mul, hv, map_one])
        have := (Projective.nonsingular_of_Z_ne_zero (W := W.toProjective.map (residue R)) (P := fun i => residue R (q i)) hz).1 hqs
        simpa [map_mul, hvr, div_eq_inv_mul] using this
    · left
      rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := exists_integral_y W x y h.1 a ha
      have hzq : residue R (q 2) = 0 := by
        by_contra hn
        exact hu (IsLocalRing.notMem_maximalIdeal.1 (fun hm => hn ((residue_eq_zero_iff _).2 hm)))
      have hq0 : q 0 = a * q 2 := by
        apply IsFractionRing.injective R K
        rw [map_mul, ha, ← hx]; field_simp
      have hq1 : q 1 = b * q 2 := by
        apply IsFractionRing.injective R K
        rw [map_mul, hb, ← hy]; field_simp
      have hzero : (fun i => residue R (q i)) = 0 := by
        ext i
        fin_cases i
        · simp [hq0, hzq]
        · simp [hq1, hzq]
        · simpa using hzq
      rw [hzero] at hqs
      simp [Projective.nonsingular_iff] at hqs
  · intro H
    rcases P with @⟨pt, hpt⟩
    induction pt using Quotient.inductionOn with | h p => ?_
    have hp : (W.toProjective⁄K).Nonsingular p := (Projective.nonsingularLift_iff _).1 hpt
    by_cases hz : p 2 = 0
    · have hK : (fun i => algebraMap R K (![0, 1, 0] i : R)) = ![0, 1, 0] := by
        ext i; fin_cases i <;> simp
      have hR : (fun i => residue R (![0, 1, 0] i : R)) = ![0, 1, 0] := by
        ext i; fin_cases i <;> simp
      refine ⟨![0, 1, 0], ?_, ?_⟩
      · show (⟦p⟧ : Projective.PointClass K) = _
        rw [hK]
        exact Quotient.sound (Projective.equiv_zero_of_Z_eq_zero hp hz)
      · rw [hR]; exact Projective.nonsingular_zero
    · have hP' := (Projective.nonsingular_of_Z_ne_zero hz).1 hp
      have hlift : Projective.Point.toAffineLift (@Projective.Point.mk _ _ _ ⟦p⟧ hpt) =
          Affine.Point.some _ _ hP' := Projective.Point.toAffineLift_of_Z_ne_zero hz
      have hpe : (⟦p⟧ : Projective.PointClass K) = ⟦![p 0 / p 2, p 1 / p 2, 1]⟧ :=
        Quotient.sound (Projective.equiv_some_of_Z_ne_zero hz)
      rcases H _ _ hP' hlift with hno | ⟨a, b, ha, hb, hns⟩
      · obtain ⟨hy0, q, hq1, hq2⟩ := exists_integral_rep_of_not_integer W _ _ hP'.1 hno
        refine ⟨q, ?_, ?_⟩
        · show (⟦p⟧ : Projective.PointClass K) = _
          rw [hq1, Projective.smul_eq _ (Ne.isUnit (inv_ne_zero hy0)), hpe]
        · rw [hq2]; exact Projective.nonsingular_zero
      · have hK : (fun i => algebraMap R K (![a, b, 1] i : R)) = ![p 0 / p 2, p 1 / p 2, 1] := by
          ext i; fin_cases i <;> simp [ha, hb]
        have hR : (fun i => residue R (![a, b, 1] i : R)) = ![residue R a, residue R b, 1] := by
          ext i; fin_cases i <;> simp
        refine ⟨![a, b, 1], ?_, ?_⟩
        · show (⟦p⟧ : Projective.PointClass K) = _
          rw [hK, hpe]
        · rw [hR]; exact (Projective.nonsingular_some _ _).2 hns

/-- A group isomorphism of the points carrying the points with non-singular reduction onto each other preserves
the local Tamagawa number. -/
theorem tamagawaNumber_eq_of_addEquiv {R' K' : Type*} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Field K'] [Algebra R' K'] [IsFractionRing R' K'] (W : WeierstrassCurve R) (W' : WeierstrassCurve R')
    (φ : (W.toProjective⁄K).Point ≃+ (W'.toProjective⁄K').Point)
    (hφ : ∀ P, P ∈ nonsingularReduction K W.toProjective ↔ φ P ∈ nonsingularReduction K' W'.toProjective) :
    tamagawaNumber K W.toProjective = tamagawaNumber K' W'.toProjective := by
  unfold tamagawaNumber
  have hE : ∀ P, (φ P + ·) '' nonsingularReduction K' W'.toProjective =
      φ '' ((P + ·) '' nonsingularReduction K W.toProjective) := by
    intro P
    ext Q
    simp only [Set.mem_image]
    constructor
    · rintro ⟨S, hS, rfl⟩
      refine ⟨φ.symm S + P, ⟨φ.symm S, ?_, add_comm _ _⟩, ?_⟩
      · rw [hφ]; simpa using hS
      · simp [add_comm]
    · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
      exact ⟨φ S, (hφ S).1 hS, by simp⟩
  have hr : Set.range (fun P : (W'.toProjective⁄K').Point ↦ (P + ·) '' nonsingularReduction K' W'.toProjective) =
      (fun S => φ '' S) '' Set.range (fun P : (W.toProjective⁄K).Point ↦ (P + ·) '' nonsingularReduction K W.toProjective) := by
    ext T
    constructor
    · rintro ⟨P', rfl⟩
      refine ⟨_, ⟨φ.symm P', rfl⟩, ?_⟩
      simp only
      rw [← hE]; simp
    · rintro ⟨_, ⟨P, rfl⟩, rfl⟩
      exact ⟨φ P, (hE P)⟩
  rw [hr]
  symm
  exact Nat.card_image_of_injOn (Set.image_injective.2 φ.injective).injOn

variable (K) in
/-- The integrality-and-reduction condition on the coordinates of an affine point. -/
def NSCond (W : WeierstrassCurve R) (x y : K) : Prop :=
  (¬ ∃ a : R, algebraMap R K a = x) ∨
    ∃ a b : R, algebraMap R K a = x ∧ algebraMap R K b = y ∧
      (W.map (residue R)).toAffine.Nonsingular (residue R a) (residue R b)

variable (K) in
/-- The condition `NSCond` at an affine point, vacuous at infinity. -/
def AffCond (W : WeierstrassCurve R) (A : (W⁄K).toAffine.Point) : Prop :=
  ∀ (x y : K) (h : (W⁄K).toAffine.Nonsingular x y), A = Affine.Point.some x y h → NSCond K W x y

lemma affCond_some (W : WeierstrassCurve R) {x y : K} (h : (W⁄K).toAffine.Nonsingular x y) :
    AffCond K W (Affine.Point.some x y h) ↔ NSCond K W x y := by
  constructor
  · intro H; exact H x y h rfl
  · intro H x₁ y₁ h₁ e
    simp only [Affine.Point.some.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact H

lemma affCond_zero (W : WeierstrassCurve R) : AffCond K W 0 := by
  intro x y h e
  exact absurd e (by simp)

open scoped Classical in
/-- Transport of the local Tamagawa number along an isomorphism of affine point groups compatible with
the integrality-and-reduction conditions on coordinates. -/
theorem tamagawaNumber_eq_of_affine {R' K' : Type*} [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    (W : WeierstrassCurve R) (W' : WeierstrassCurve R')
    (ψ : (W⁄K).toAffine.Point ≃+ (W'⁄K').toAffine.Point)
    (hψ : ∀ (x y : K) (h : (W⁄K).toAffine.Nonsingular x y),
      ∃ (x' y' : K') (h' : (W'⁄K').toAffine.Nonsingular x' y'),
        ψ (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          (NSCond K W x y ↔ NSCond K' W' x' y')) :
    tamagawaNumber K W.toProjective = tamagawaNumber K' W'.toProjective := by
  classical
  refine tamagawaNumber_eq_of_addEquiv W W'
    ((Projective.Point.toAffineAddEquiv (W.toProjective⁄K)).trans
      (ψ.trans (Projective.Point.toAffineAddEquiv (W'.toProjective⁄K')).symm)) ?_
  intro P
  rw [mem_nonsingularReduction_iff, mem_nonsingularReduction_iff]
  have hlift : Projective.Point.toAffineLift
      (((Projective.Point.toAffineAddEquiv (W.toProjective⁄K)).trans
      (ψ.trans (Projective.Point.toAffineAddEquiv (W'.toProjective⁄K')).symm)) P) =
        ψ (Projective.Point.toAffineLift P) :=
    (Projective.Point.toAffineAddEquiv (W'.toProjective⁄K')).apply_symm_apply _
  rw [hlift]
  show AffCond K W (Projective.Point.toAffineLift P) ↔ AffCond K' W' (ψ (Projective.Point.toAffineLift P))
  generalize Projective.Point.toAffineLift P = A
  rcases A with _ | ⟨x, y, h⟩
  · have : ψ 0 = 0 := map_zero ψ
    change AffCond K W 0 ↔ AffCond K' W' (ψ 0)
    rw [this]
    exact ⟨fun _ => affCond_zero _, fun _ => affCond_zero _⟩
  · obtain ⟨x', y', h', he, hc⟩ := hψ x y h
    rw [he, affCond_some, affCond_some]
    exact hc

section VariableChangeAux

variable {S : Type*} [CommRing S] (φ : R →+* S) (C : VariableChange R)

lemma inv_image_x (x : S) :
    φ ((C⁻¹).u : R) ^ 2 * (φ (C.u : R) ^ 2 * x + φ C.r) + φ (C⁻¹).r = x := by
  have hu : φ (C.u : R) * φ ((C.u⁻¹ : Rˣ) : R) = 1 := by rw [← map_mul, C.u.mul_inv, map_one]
  simp only [VariableChange.inv_def, map_mul, map_neg, map_pow]
  linear_combination x * (φ (C.u : R) * φ ((C.u⁻¹ : Rˣ) : R) + 1) * hu

lemma inv_image_y (x y : S) :
    φ ((C⁻¹).u : R) ^ 3 * (φ (C.u : R) ^ 3 * y + φ (C.u : R) ^ 2 * φ C.s * x + φ C.t) +
      φ ((C⁻¹).u : R) ^ 2 * φ (C⁻¹).s * (φ (C.u : R) ^ 2 * x + φ C.r) + φ (C⁻¹).t = y := by
  have hu : φ (C.u : R) * φ ((C.u⁻¹ : Rˣ) : R) = 1 := by rw [← map_mul, C.u.mul_inv, map_one]
  simp only [VariableChange.inv_def, map_mul, map_neg, map_pow, map_sub]
  linear_combination y * ((φ (C.u : R) * φ ((C.u⁻¹ : Rˣ) : R)) ^ 2 +
    φ (C.u : R) * φ ((C.u⁻¹ : Rˣ) : R) + 1) * hu

end VariableChangeAux

lemma nsCond_variableChange_fwd (W : WeierstrassCurve R) (C : VariableChange R) (x y x' y' : K)
    (hx' : x' = algebraMap R K (C.u : R) ^ 2 * x + algebraMap R K C.r)
    (hy' : y' = algebraMap R K (C.u : R) ^ 3 * y + algebraMap R K (C.u : R) ^ 2 * algebraMap R K C.s * x +
      algebraMap R K C.t) :
    NSCond K (C • W) x y → NSCond K W x' y' := by
  rintro (hno | ⟨a, b, ha, hb, hns⟩)
  · left
    rintro ⟨a', ha'⟩
    apply hno
    refine ⟨((C.u⁻¹ : Rˣ) : R) ^ 2 * (a' - C.r), ?_⟩
    have hvu : algebraMap R K ((C.u⁻¹ : Rˣ) : R) * algebraMap R K (C.u : R) = 1 := by
      rw [← map_mul, C.u.inv_mul, map_one]
    simp only [map_mul, map_pow, map_sub]
    rw [ha', hx']
    linear_combination x * (algebraMap R K ((C.u⁻¹ : Rˣ) : R) * algebraMap R K (C.u : R) + 1) * hvu
  · right
    refine ⟨(C.u : R) ^ 2 * a + C.r, (C.u : R) ^ 3 * b + (C.u : R) ^ 2 * C.s * a + C.t, ?_, ?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, ha, hx']
    · simp only [map_add, map_mul, map_pow, ha, hb, hy']
    · have h1 := (Affine.variableChange_nonsingular (W.map (residue R)) (C.map (residue R))
        (residue R a) (residue R b)).2 (by rwa [WeierstrassCurve.map_variableChange])
      simpa [VariableChange.map] using h1

/-- An integral change of variables preserves the local Tamagawa number. -/
theorem tamagawaNumber_variableChange (W : WeierstrassCurve R) (C : VariableChange R) :
    tamagawaNumber K (C • W).toProjective = tamagawaNumber K W.toProjective := by
  classical
  refine tamagawaNumber_eq_of_affine (K := K) (K' := K) (C • W) W (W.pointEquivVariableChange K C) ?_
  intro x y h
  refine ⟨_, _, _, WeierstrassCurve.pointEquivVariableChange_some W K C h, ?_⟩
  refine ⟨nsCond_variableChange_fwd W C x y _ _ rfl rfl, fun H => ?_⟩
  have hx'' : x = algebraMap R K ((C⁻¹).u : R) ^ 2 *
      (algebraMap R K (C.u : R) ^ 2 * x + algebraMap R K C.r) + algebraMap R K (C⁻¹).r :=
    (inv_image_x (algebraMap R K) C x).symm
  have hy'' : y = algebraMap R K ((C⁻¹).u : R) ^ 3 *
      (algebraMap R K (C.u : R) ^ 3 * y + algebraMap R K (C.u : R) ^ 2 * algebraMap R K C.s * x +
        algebraMap R K C.t) +
      algebraMap R K ((C⁻¹).u : R) ^ 2 * algebraMap R K (C⁻¹).s *
        (algebraMap R K (C.u : R) ^ 2 * x + algebraMap R K C.r) + algebraMap R K (C⁻¹).t :=
    (inv_image_y (algebraMap R K) C x y).symm
  exact nsCond_variableChange_fwd (C • W) C⁻¹ _ _ x y hx'' hy'' (by rwa [inv_smul_smul])

lemma nsCond_map_ringEquiv {R' K' : Type*} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Field K'] [Algebra R' K'] (e : K ≃+* K') (eR : R ≃+* R')
    (he : ∀ r : R, e (algebraMap R K r) = algebraMap R' K' (eR r)) (W : WeierstrassCurve R) (x y : K) :
    NSCond K W x y ↔ NSCond K' (W.map (eR : R →+* R')) (e x) (e y) := by
  constructor
  · rintro (hno | ⟨a, b, ha, hb, hns⟩)
    · left
      rintro ⟨a', ha'⟩
      apply hno
      refine ⟨eR.symm a', e.injective ?_⟩
      rw [he, RingEquiv.apply_symm_apply, ha']
    · right
      refine ⟨eR a, eR b, by rw [← he, ha], by rw [← he, hb], ?_⟩
      exact (Affine.map_nonsingular (W := (W.map (residue R)).toAffine)
        (f := IsLocalRing.ResidueField.map (eR : R →+* R')) (RingHom.injective _) _ _).2 hns
  · rintro (hno | ⟨a', b', ha', hb', hns⟩)
    · left
      rintro ⟨a, ha⟩
      exact hno ⟨eR a, by rw [← he, ha]⟩
    · right
      have h1 : ∀ (a' : R') (x : K), algebraMap R' K' a' = e x → algebraMap R K (eR.symm a') = x := by
        intro a' x h
        apply e.injective
        rw [he, RingEquiv.apply_symm_apply, h]
      refine ⟨eR.symm a', eR.symm b', h1 _ _ ha', h1 _ _ hb', ?_⟩
      refine (Affine.map_nonsingular (W := (W.map (residue R)).toAffine)
        (f := IsLocalRing.ResidueField.map (eR : R →+* R')) (RingHom.injective _) _ _).1 ?_
      have : IsLocalRing.ResidueField.map (eR : R →+* R') (residue R (eR.symm a')) = residue R' a' := by
        simp
      have h2 : IsLocalRing.ResidueField.map (eR : R →+* R') (residue R (eR.symm b')) = residue R' b' := by
        simp
      rw [this, h2]
      exact hns

/-- An isomorphism of discrete valuation rings, extended to the fraction fields, preserves the local Tamagawa
number. -/
theorem tamagawaNumber_map_ringEquiv {R' K' : Type*} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Field K'] [Algebra R' K'] [IsFractionRing R' K'] (e : K ≃+* K') (eR : R ≃+* R')
    (he : ∀ r : R, e (algebraMap R K r) = algebraMap R' K' (eR r)) (W : WeierstrassCurve R) :
    tamagawaNumber K' (W.map (eR : R →+* R')).toProjective = tamagawaNumber K W.toProjective := by
  classical
  let : Algebra R K' := ((algebraMap R' K').comp (eR : R →+* R')).toAlgebra
  let f : K →ₐ[R] K' := { (e : K →+* K') with commutes' := fun r => he r }
  have hinj : Function.Injective (Affine.Point.map (W' := W.toAffine) f) :=
    Affine.Point.map_injective f
  have hf : ∀ z, f (e.symm z) = z := fun z => e.apply_symm_apply z
  have hsurj : Function.Surjective (Affine.Point.map (W' := W.toAffine) f) := by
    rintro (_ | ⟨x', y', h'⟩)
    · exact ⟨0, rfl⟩
    · refine ⟨Affine.Point.some (e.symm x') (e.symm y') ?_, ?_⟩
      · refine (Affine.baseChange_nonsingular (W := W.toAffine) (f := f) f.injective _ _).1 ?_
        rw [hf, hf]; exact h'
      · simp only [Affine.Point.map_some, Affine.Point.some.injEq, hf]

  let ψ : (W⁄K).toAffine.Point ≃+ ((W.map (eR : R →+* R'))⁄K').toAffine.Point :=
    AddEquiv.ofBijective (Affine.Point.map (W' := W.toAffine) f) ⟨hinj, hsurj⟩
  symm
  refine tamagawaNumber_eq_of_affine (K := K) (K' := K') W (W.map (eR : R →+* R')) ψ ?_
  intro x y h
  exact ⟨e x, e y, _, rfl, nsCond_map_ringEquiv e eR he W x y⟩

/-- Any two minimal models of a curve with nonzero discriminant give the same local Tamagawa number. -/
theorem tamagawaNumber_minimal_eq {W : WeierstrassCurve K} (hΔ : W.Δ ≠ 0) (C : VariableChange K)
    [W.IsMinimal R] [(C • W).IsMinimal R] :
    tamagawaNumber K (W.integralModel R).toProjective = tamagawaNumber K ((C • W).integralModel R).toProjective := by
  obtain ⟨CR, hCR⟩ := MinimalTransport.exists_baseChange_eq_of_isMinimal (R := R) hΔ C
  have heq : CR • W.integralModel R = (C • W).integralModel R := by
    apply WeierstrassCurve.map_injective (f := algebraMap R K) (IsFractionRing.injective R K)
    show (CR • W.integralModel R).baseChange K = ((C • W).integralModel R).baseChange K
    rw [← baseChange_smul_baseChange, baseChange_integralModel_eq, hCR, baseChange_integralModel_eq]
  rw [← heq, tamagawaNumber_variableChange]

/-- **$c_v = 1$ at good reduction**: if the minimal equation `W` has good reduction, every point
has non-singular reduction, so the local Tamagawa number of its integral model is $1$. -/
theorem tamagawaNumber_eq_one_of_hasGoodReduction (W : WeierstrassCurve K) [W.HasGoodReduction R] :
    tamagawaNumber K (W.integralModel R).toProjective = 1 := by
  have hE : ((W.integralModel R).map (residue R)).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).1 inferInstance
  have hall : ∀ P : ((W.integralModel R).toProjective⁄K).Point,
      P ∈ nonsingularReduction K (W.integralModel R).toProjective := by
    intro P
    rw [mem_nonsingularReduction_iff]
    intro x y h _
    by_cases hx : ∃ a : R, algebraMap R K a = x
    · right
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := exists_integral_y _ x y h.1 a ha
      refine ⟨a, b, ha, hb, ?_⟩
      have hEq : (W.integralModel R).toAffine.Equation a b :=
        (Affine.map_equation (W := (W.integralModel R).toAffine) (f := algebraMap R K)
          (IsFractionRing.injective R K) a b).1 (ha ▸ hb ▸ h.1)
      exact (Affine.equation_iff_nonsingular (W := (W.integralModel R).map (residue R))).1
        (hEq.map (residue R))
    · left; exact hx
  have himg : ∀ P : ((W.integralModel R).toProjective⁄K).Point,
      (P + ·) '' nonsingularReduction K (W.integralModel R).toProjective = Set.univ := by
    intro P
    have : nonsingularReduction K (W.integralModel R).toProjective = Set.univ :=
      Set.eq_univ_of_forall hall
    rw [this]
    exact Set.image_univ_of_surjective (add_left_surjective P)
  unfold tamagawaNumber
  simp only [himg, Set.range_const]
  simp

end NumberFieldKB.MilneEC.Tamagawa
