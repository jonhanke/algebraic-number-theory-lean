import NumberFieldKB.MilneEC.Ch3Defs

/-!
# Milne, Elliptic Curves, Chapter III §1–§2: lattices, bases, doubly periodic functions

Proposition 1.1 of Milne, *Elliptic Curves* (`milne2006ec`, pdf p. 90), the bijections (18), the
period parallelogram, and condition (19) for doubly periodic functions.

The action of `SL₂(ℤ)` on pairs is Milne's: `(a b; c d) · (ω₁, ω₂) = (aω₁ + bω₂, cω₁ + dω₂)`
(column vectors, matrix indices 0-based: `A 0 0 = a`, `A 0 1 = b`, `A 1 0 = c`, `A 1 1 = d`).
-/

open Complex Set Filter Topology Pointwise Matrix MatrixGroups

namespace NumberFieldKB.MilneEC.III

/-! ### The action of `SL₂(ℤ)` on oriented pairs -/

/-- The underlying pair of `A · (ω₁, ω₂)`. -/
def smulPair (A : SL(2, ℤ)) (p : ℂ × ℂ) : ℂ × ℂ :=
  ((A 0 0 : ℂ) * p.1 + (A 0 1 : ℂ) * p.2, (A 1 0 : ℂ) * p.1 + (A 1 1 : ℂ) * p.2)

private theorem OrientedPair.snd_ne_zero (p : OrientedPair) : p.1.2 ≠ 0 := by
  intro h
  have := p.2
  simp [h] at this

private theorem den_ne_zero' (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ((A 1 0 : ℂ) * τ + (A 1 1 : ℂ)) ≠ 0 := by
  intro h
  have := (A • τ).im_pos
  rw [UpperHalfPlane.specialLinearGroup_apply] at this
  simp [h] at this

private theorem smulPair_div (A : SL(2, ℤ)) (p : OrientedPair) :
    (smulPair A p.1).1 / (smulPair A p.1).2 = ((A • p.ratio : UpperHalfPlane) : ℂ) := by
  have hw := p.snd_ne_zero
  have hd := den_ne_zero' A p.ratio
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp only [OrientedPair.ratio] at hd ⊢
  simp only [smulPair, eq_intCast, Complex.ofReal_intCast]
  have h2 : (A 1 0 : ℂ) * p.1.1 + (A 1 1 : ℂ) * p.1.2 ≠ 0 := by
    intro h
    apply hd
    have : ((A 1 0 : ℂ) * (p.1.1 / p.1.2) + (A 1 1 : ℂ)) = ((A 1 0 : ℂ) * p.1.1 + (A 1 1 : ℂ) * p.1.2) / p.1.2 := by
      field_simp
    rw [this, h, zero_div]
  field_simp

/-- `Im (ω₁' / ω₂') > 0` is preserved: with `z = ω₁/ω₂`, `ω₁'/ω₂' = (az+b)/(cz+d)` and
`Im((az+b)/(cz+d)) = (ad - bc) Im z / |cz+d|²` (Milne, pdf p. 89). -/
theorem im_div_smulPair_pos (A : SL(2, ℤ)) (p : OrientedPair) :
    0 < ((smulPair A p.1).1 / (smulPair A p.1).2).im := by
  rw [smulPair_div]
  exact (A • p.ratio).im_pos

/-- Milne's action of `SL₂(ℤ)` on the set `M` of Proposition 1.1. -/
instance : MulAction SL(2, ℤ) OrientedPair where
  smul A p := ⟨smulPair A p.1, im_div_smulPair_pos A p⟩
  one_smul p := by
    apply Subtype.ext
    show smulPair 1 p.1 = p.1
    simp [smulPair]
  mul_smul A B p := by
    apply Subtype.ext
    show smulPair (A * B) p.1 = smulPair A (smulPair B p.1)
    simp only [smulPair, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Prod.mk.injEq]
    push_cast
    constructor <;> ring

theorem OrientedPair.smul_val (A : SL(2, ℤ)) (p : OrientedPair) :
    (A • p).1 = smulPair A p.1 := rfl

private theorem indep_of_im_ne {w₁ w₂ : ℂ} (h : (w₁ / w₂).im ≠ 0) :
    LinearIndependent ℝ ![w₁, w₂] := by
  have hw : w₂ ≠ 0 := by
    intro h0
    simp [h0] at h
  rw [LinearIndependent.pair_iff]
  intro s t e
  simp only [Complex.real_smul] at e
  have e' : (s : ℂ) * (w₁ / w₂) + t = 0 := by
    have : ((s : ℂ) * w₁ + t * w₂) / w₂ = 0 := by rw [e, zero_div]
    rw [← this]; field_simp
  have him := congrArg Complex.im e'
  simp at him
  rcases him with h1 | h1
  · subst h1
    simp at e
    rcases e with h2 | h2
    · exact ⟨rfl, h2⟩
    · exact absurd h2 hw
  · exact absurd h1 h

private theorem im_ne_of_indep {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    (w₁ / w₂).im ≠ 0 := by
  intro him
  rw [LinearIndependent.pair_iff] at h
  have hw : w₂ ≠ 0 := by
    intro h0
    have := h 0 1 (by simp [h0])
    simp at this
  have hr : w₁ / w₂ = ((w₁ / w₂).re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have := h 1 (-(w₁ / w₂).re) (by
    rw [Complex.real_smul, Complex.real_smul]
    have : w₁ = ((w₁ / w₂).re : ℂ) * w₂ := by
      rw [← hr]; field_simp
    simp only [ofReal_one, one_mul, ofReal_neg]
    rw [neg_mul, ← sub_eq_add_neg, sub_eq_zero]
    exact this)
  simp at this

/-- The `PeriodPair` of an oriented pair. -/
def OrientedPair.toPeriodPair (p : OrientedPair) : PeriodPair :=
  ⟨p.1.1, p.1.2, indep_of_im_ne p.2.ne'⟩

theorem OrientedPair.lattice_eq (p : OrientedPair) : p.lattice = p.toPeriodPair.lattice := rfl

/-- The lattice of an oriented pair is a lattice. -/
theorem OrientedPair.isLattice (p : OrientedPair) : IsLattice p.lattice :=
  ⟨p.toPeriodPair, rfl⟩

private theorem pair_coeff {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) (m n : ℤ)
    (e : (m : ℂ) * w₁ + n * w₂ = 0) : m = 0 ∧ n = 0 := by
  rw [LinearIndependent.pair_iff] at h
  have := h m n (by simpa [Complex.real_smul] using e)
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

private theorem mem_lattice_pair {p : OrientedPair} {x : ℂ} :
    x ∈ p.lattice ↔ ∃ m n : ℤ, x = m * p.1.1 + n * p.1.2 := by
  rw [OrientedPair.lattice_eq, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩

private theorem mem_lattice_fst (p : OrientedPair) : p.1.1 ∈ p.lattice :=
  Submodule.subset_span (by simp)

private theorem mem_lattice_snd (p : OrientedPair) : p.1.2 ∈ p.lattice :=
  Submodule.subset_span (by simp)

private theorem smul_lattice_le (A : SL(2, ℤ)) (p : OrientedPair) :
    (A • p).lattice ≤ p.lattice := by
  unfold OrientedPair.lattice
  rw [Submodule.span_le]
  rintro x (rfl | rfl)
  · exact mem_lattice_pair.2 ⟨A 0 0, A 0 1, rfl⟩
  · exact mem_lattice_pair.2 ⟨A 1 0, A 1 1, rfl⟩

private theorem im_div_eq (z w : ℂ) : (z / w).im = (z * (starRingEnd ℂ) w).im / Complex.normSq w := by
  rw [Complex.div_im]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem im_mul_conj_pos {z w : ℂ} (hw : w ≠ 0) :
    0 < (z / w).im ↔ 0 < (z * (starRingEnd ℂ) w).im := by
  rw [im_div_eq]
  have := Complex.normSq_pos.2 hw
  exact div_pos_iff_of_pos_right this

/-- Proposition 1.1, injectivity: two oriented pairs span the same lattice if and only if they
lie in the same `SL₂(ℤ)`-orbit. -/
@[kb "milne2006ec" "Ch. III, Prop. 1.1, pdf p. 90"]
theorem prop_1_1_lattice_eq_iff (p q : OrientedPair) :
    p.lattice = q.lattice ↔ ∃ A : SL(2, ℤ), A • p = q := by
  constructor
  · intro hpq
    have hq1 : q.1.1 ∈ p.lattice := hpq ▸ mem_lattice_fst q
    have hq2 : q.1.2 ∈ p.lattice := hpq ▸ mem_lattice_snd q
    have hp1 : p.1.1 ∈ q.lattice := hpq ▸ mem_lattice_fst p
    have hp2 : p.1.2 ∈ q.lattice := hpq ▸ mem_lattice_snd p
    obtain ⟨a, b, h1⟩ := mem_lattice_pair.1 hq1
    obtain ⟨c, d, h2⟩ := mem_lattice_pair.1 hq2
    obtain ⟨a', b', g1⟩ := mem_lattice_pair.1 hp1
    obtain ⟨c', d', g2⟩ := mem_lattice_pair.1 hp2
    have hind : LinearIndependent ℝ ![q.1.1, q.1.2] := q.toPeriodPair.indep
    have E : ∀ (x y : ℤ) (u v : ℤ), (x : ℂ) * q.1.1 + y * q.1.2 = u * q.1.1 + v * q.1.2 →
        x = u ∧ y = v := by
      intro x y u v e
      have := pair_coeff hind (x - u) (y - v) (by push_cast; linear_combination e)
      omega
    have E1 := E (a * a' + b * c') (a * b' + b * d') 1 0 (by
      push_cast
      linear_combination (-(a : ℂ)) * g1 + (-(b : ℂ)) * g2 - h1)
    have E2 := E (c * a' + d * c') (c * b' + d * d') 0 1 (by
      push_cast
      linear_combination (-(c : ℂ)) * g1 + (-(d : ℂ)) * g2 - h2)
    obtain ⟨e1, e2⟩ := E1
    obtain ⟨e3, e4⟩ := E2
    have hdet : (a * d - b * c) * (a' * d' - b' * c') = 1 := by
      calc (a * d - b * c) * (a' * d' - b' * c')
          = (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c') := by
            ring
        _ = 1 := by rw [e1, e2, e3, e4]; norm_num
    have hqpos : 0 < (q.1.1 * (starRingEnd ℂ) q.1.2).im :=
      (im_mul_conj_pos q.snd_ne_zero).1 q.2
    have hppos : 0 < (p.1.1 * (starRingEnd ℂ) p.1.2).im :=
      (im_mul_conj_pos p.snd_ne_zero).1 p.2
    have hrel : (q.1.1 * (starRingEnd ℂ) q.1.2).im = ((a * d - b * c : ℤ) : ℝ) *
        (p.1.1 * (starRingEnd ℂ) p.1.2).im := by
      rw [h1, h2]
      simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, map_add, map_mul,
        map_intCast, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
        Complex.conj_im]
      push_cast
      ring
    have hd1 : a * d - b * c = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
      · exact h
      · exfalso
        rw [h] at hrel
        push_cast at hrel
        linarith
    refine ⟨⟨!![a, b; c, d], by simpa [Matrix.det_fin_two_of] using hd1⟩, ?_⟩
    apply Subtype.ext
    show smulPair _ p.1 = q.1
    refine Prod.ext ?_ ?_
    · simp [smulPair, h1]
    · simp [smulPair, h2]
  · rintro ⟨A, rfl⟩
    apply le_antisymm
    · calc p.lattice = (A⁻¹ • (A • p)).lattice := by rw [inv_smul_smul]
        _ ≤ (A • p).lattice := smul_lattice_le _ _
    · exact smul_lattice_le A p

/-- Proposition 1.1, surjectivity: every lattice has an oriented basis. -/
@[kb "milne2006ec" "Ch. III, Prop. 1.1, pdf p. 90"]
theorem prop_1_1_exists (Λ : Submodule ℤ ℂ) (hΛ : IsLattice Λ) :
    ∃ p : OrientedPair, p.lattice = Λ := by
  obtain ⟨L, rfl⟩ := hΛ
  have hne := im_ne_of_indep L.indep
  by_cases h : 0 < (L.ω₁ / L.ω₂).im
  · exact ⟨⟨(L.ω₁, L.ω₂), h⟩, rfl⟩
  · have hneg : (L.ω₁ / L.ω₂).im < 0 := lt_of_le_of_ne (not_lt.1 h) hne
    have hz : L.ω₁ / L.ω₂ ≠ 0 := by
      intro h0
      rw [h0] at hneg
      simp at hneg
    have hpos : 0 < (L.ω₂ / L.ω₁).im := by
      have : L.ω₂ / L.ω₁ = (L.ω₁ / L.ω₂)⁻¹ := by rw [inv_div]
      rw [this, Complex.inv_im]
      exact div_pos (by linarith) (Complex.normSq_pos.2 hz)
    refine ⟨⟨(L.ω₂, L.ω₁), hpos⟩, ?_⟩
    show Submodule.span ℤ {L.ω₂, L.ω₁} = Submodule.span ℤ {L.ω₁, L.ω₂}
    rw [Set.pair_comm]

/-- Proposition 1.1 (Milne, pdf p. 90): `(ω₁, ω₂) ↦ ℤω₁ + ℤω₂` induces a bijection
`SL₂(ℤ)\M → L` onto the set of lattices in `ℂ`. -/
@[kb "milne2006ec" "Ch. III, Prop. 1.1, pdf p. 90"]
noncomputable def prop_1_1 :
    MulAction.orbitRel.Quotient SL(2, ℤ) OrientedPair ≃ {Λ : Submodule ℤ ℂ // IsLattice Λ} :=
  Equiv.ofBijective
    (Quotient.lift (fun p : OrientedPair => (⟨p.lattice, p.isLattice⟩ : {Λ // IsLattice Λ}))
      (fun p q h => by
        obtain ⟨A, hA⟩ := h
        exact Subtype.ext ((prop_1_1_lattice_eq_iff q p).2 ⟨A, hA⟩).symm))
    (by
      constructor
      · rintro ⟨p⟩ ⟨q⟩ h
        obtain ⟨A, hA⟩ := (prop_1_1_lattice_eq_iff p q).1 (congrArg Subtype.val h)
        exact Quotient.sound ⟨A⁻¹, by simp only [← hA, inv_smul_smul]⟩
      · rintro ⟨Λ, hΛ⟩
        obtain ⟨p, hp⟩ := prop_1_1_exists Λ hΛ
        exact ⟨⟦p⟧, Subtype.ext hp⟩)

/-! ### The bijections (18) -/

/-- The map `(ω₁, ω₂) ↦ ω₁/ω₂` is compatible with the actions of `SL₂(ℤ)` on `M` and on `ℍ`
(Milne, pdf p. 90: `(a b; c d) τ = (aτ + b)/(cτ + d)`). -/
@[kb "milne2006ec" "Ch. III, §1, (18), compatibility of the actions, pdf p. 90"]
theorem ratio_smul (A : SL(2, ℤ)) (p : OrientedPair) : (A • p).ratio = A • p.ratio := by
  apply UpperHalfPlane.ext
  exact smulPair_div A p

private theorem lattice_eq_smul_of (c : ℂ) (p q : OrientedPair) (h1 : q.1.1 = c * p.1.1)
    (h2 : q.1.2 = c * p.1.2) : q.lattice = c • p.lattice := by
  unfold OrientedPair.lattice
  rw [Submodule.pointwise_smul_def, Submodule.map_span, Set.image_pair, h1, h2]
  simp

/-- `(ω₁, ω₂) ↦ ω₁/ω₂` induces a bijection `M/ℂ^× → ℍ` (Milne, pdf p. 90): it is surjective, and
two pairs have the same ratio if and only if they differ by a nonzero scalar. -/
@[kb "milne2006ec" "Ch. III, §1, M/C^× ≅ H, pdf p. 90"]
theorem ratio_surjective : Function.Surjective OrientedPair.ratio := by
  intro τ
  refine ⟨⟨((τ : ℂ), 1), by simpa using τ.im_pos⟩, ?_⟩
  apply UpperHalfPlane.ext
  simp [OrientedPair.ratio]

@[kb "milne2006ec" "Ch. III, §1, M/C^× ≅ H, pdf p. 90"]
theorem ratio_eq_iff (p q : OrientedPair) :
    p.ratio = q.ratio ↔ ∃ c : ℂ, c ≠ 0 ∧ q.1.1 = c * p.1.1 ∧ q.1.2 = c * p.1.2 := by
  have hp := p.snd_ne_zero
  have hq := q.snd_ne_zero
  constructor
  · intro h
    have h' : p.1.1 / p.1.2 = q.1.1 / q.1.2 := congrArg UpperHalfPlane.coe h
    refine ⟨q.1.2 / p.1.2, div_ne_zero hq hp, ?_, ?_⟩
    · rw [div_eq_div_iff hp hq] at h'
      field_simp
      linear_combination -h'
    · field_simp
  · rintro ⟨c, hc, h1, h2⟩
    apply UpperHalfPlane.ext
    show p.1.1 / p.1.2 = q.1.1 / q.1.2
    rw [h1, h2, mul_div_mul_left _ _ hc]

/-- The bijections (18) of Milne (pdf p. 90): `L/ℂ^× ≅ SL₂(ℤ)\M/ℂ^× ≅ SL₂(ℤ)\ℍ`, in the form:
the lattices of two oriented pairs are homothetic if and only if their ratios lie in the same
`SL₂(ℤ)`-orbit of `ℍ`. -/
@[kb "milne2006ec" "Ch. III, §1, (18), pdf p. 90"]
theorem lattice_homothetic_iff (p q : OrientedPair) :
    (∃ c : ℂ, c ≠ 0 ∧ q.lattice = c • p.lattice) ↔ ∃ A : SL(2, ℤ), A • p.ratio = q.ratio := by
  constructor
  · rintro ⟨c, hc, h⟩
    let p' : OrientedPair := ⟨(c * p.1.1, c * p.1.2), by
      show 0 < (c * p.1.1 / (c * p.1.2)).im
      rw [mul_div_mul_left _ _ hc]; exact p.2⟩
    have hl : q.lattice = p'.lattice := h.trans (lattice_eq_smul_of c p p' rfl rfl).symm
    obtain ⟨A, hA⟩ := (prop_1_1_lattice_eq_iff p' q).1 hl.symm
    refine ⟨A, ?_⟩
    have hr : p'.ratio = p.ratio := by
      apply UpperHalfPlane.ext
      show c * p.1.1 / (c * p.1.2) = p.1.1 / p.1.2
      rw [mul_div_mul_left _ _ hc]
    rw [← hA, ratio_smul, hr]
  · rintro ⟨A, hA⟩
    obtain ⟨c, hc, h1, h2⟩ := (ratio_eq_iff (A • p) q).1 (by rw [ratio_smul, hA])
    refine ⟨c, hc, ?_⟩
    rw [lattice_eq_smul_of c (A • p) q h1 h2]
    rw [← (prop_1_1_lattice_eq_iff p (A • p)).2 ⟨A, rfl⟩]

/-! ### The period parallelogram -/

/-- The closed period parallelogram. -/
def closedPeriodParallelogram (ω₁ ω₂ z₀ : ℂ) : Set ℂ :=
  {z | ∃ s t : ℝ, s ∈ Icc (0 : ℝ) 1 ∧ t ∈ Icc (0 : ℝ) 1 ∧ z = z₀ + s * ω₁ + t * ω₂}

/-- The coordinate homeomorphism `ℂ ≃ₜ ℝ²` of the basis `(ω₁, ω₂)`. -/
private noncomputable def coordHomeo (L : PeriodPair) : ℂ ≃ₜ (Fin 2 → ℝ) :=
  L.basis.equivFun.toContinuousLinearEquiv.toHomeomorph

private theorem coordHomeo_apply (L : PeriodPair) (z : ℂ) (i : Fin 2) :
    coordHomeo L z i = L.basis.repr z i := rfl

/-- The coordinate homeomorphism, centred at `z₀`. -/
private noncomputable def shiftHomeo (L : PeriodPair) (z₀ : ℂ) : ℂ ≃ₜ (Fin 2 → ℝ) :=
  (Homeomorph.subRight z₀).trans (coordHomeo L)

private theorem shiftHomeo_apply (L : PeriodPair) (z₀ z : ℂ) (i : Fin 2) :
    shiftHomeo L z₀ z i = L.basis.repr (z - z₀) i := rfl

private theorem repr_comb (L : PeriodPair) (s t : ℝ) (i : Fin 2) :
    L.basis.repr ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) i = if i = 0 then s else t := by
  have h1 : ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) = s • L.basis 0 + t • L.basis 1 := by
    simp [Complex.real_smul]
  rw [h1, map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  fin_cases i <;> simp

private theorem eq_comb (L : PeriodPair) (w : ℂ) :
    w = (L.basis.repr w 0 : ℂ) * L.ω₁ + (L.basis.repr w 1 : ℂ) * L.ω₂ := by
  have := L.basis.sum_repr w
  rw [Fin.sum_univ_two] at this
  conv_lhs => rw [← this]
  simp [Complex.real_smul]

private theorem mem_param_iff (L : PeriodPair) (z₀ : ℂ) (S : Set ℝ) (z : ℂ) :
    (∃ s t : ℝ, s ∈ S ∧ t ∈ S ∧ z = z₀ + s * L.ω₁ + t * L.ω₂) ↔
      z ∈ shiftHomeo L z₀ ⁻¹' (Set.pi univ fun _ => S) := by
  simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, shiftHomeo_apply, Fin.forall_fin_two]
  constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    have : z₀ + s * L.ω₁ + t * L.ω₂ - z₀ = s * L.ω₁ + t * L.ω₂ := by ring
    rw [this, repr_comb, repr_comb]
    simpa using ⟨hs, ht⟩
  · rintro ⟨h0, h1⟩
    refine ⟨_, _, h0, h1, ?_⟩
    have := eq_comb L (z - z₀)
    linear_combination this

private theorem periodParallelogram_eq_preimage (L : PeriodPair) (z₀ : ℂ) :
    periodParallelogram L.ω₁ L.ω₂ z₀ =
      shiftHomeo L z₀ ⁻¹' (Set.pi univ fun _ => Ioo (0 : ℝ) 1) := by
  ext z
  exact mem_param_iff L z₀ (Ioo 0 1) z

private theorem closedPeriodParallelogram_eq_preimage (L : PeriodPair) (z₀ : ℂ) :
    closedPeriodParallelogram L.ω₁ L.ω₂ z₀ =
      shiftHomeo L z₀ ⁻¹' (Set.pi univ fun _ => Icc (0 : ℝ) 1) := by
  ext z
  exact mem_param_iff L z₀ (Icc 0 1) z

/-- Comparison with Mathlib: Milne's period parallelogram is the translate by `z₀` of the
interior of Mathlib's half-open fundamental domain `ZSpan.fundamentalDomain` of the basis
`(ω₁, ω₂)`. -/
theorem periodParallelogram_eq (L : PeriodPair) (z₀ : ℂ) :
    periodParallelogram L.ω₁ L.ω₂ z₀ = z₀ +ᵥ interior (ZSpan.fundamentalDomain L.basis) := by
  have hF : ZSpan.fundamentalDomain L.basis =
      coordHomeo L ⁻¹' (Set.pi univ fun _ => Ico (0 : ℝ) 1) := by
    ext m
    simp [ZSpan.mem_fundamentalDomain, coordHomeo_apply]
  rw [hF, ← Homeomorph.preimage_interior, interior_pi_set Set.finite_univ, interior_Ico]
  rw [periodParallelogram_eq_preimage]
  ext z
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simp [shiftHomeo_apply, coordHomeo_apply, sub_eq_neg_add]

theorem closure_periodParallelogram (L : PeriodPair) (z₀ : ℂ) :
    closure (periodParallelogram L.ω₁ L.ω₂ z₀) = closedPeriodParallelogram L.ω₁ L.ω₂ z₀ := by
  rw [periodParallelogram_eq_preimage, closedPeriodParallelogram_eq_preimage,
    ← Homeomorph.preimage_closure, closure_pi_set]
  have hc : closure (Ioo (0 : ℝ) 1) = Icc 0 1 := closure_Ioo (by norm_num)
  simp only [hc]

private theorem isOpen_periodParallelogram (L : PeriodPair) (z₀ : ℂ) :
    IsOpen (periodParallelogram L.ω₁ L.ω₂ z₀) := by
  rw [periodParallelogram_eq_preimage]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage (shiftHomeo L z₀).continuous

theorem frontier_periodParallelogram (L : PeriodPair) (z₀ : ℂ) :
    frontier (periodParallelogram L.ω₁ L.ω₂ z₀) =
      closedPeriodParallelogram L.ω₁ L.ω₂ z₀ \ periodParallelogram L.ω₁ L.ω₂ z₀ := by
  rw [frontier, closure_periodParallelogram, (isOpen_periodParallelogram L z₀).interior_eq]

/-- A period parallelogram is a fundamental domain away from its boundary: if no translate
`z + ω` (`ω ∈ Λ`) lies on the boundary of `D`, then exactly one translate lies in `D`. -/
theorem existsUnique_add_mem_periodParallelogram (L : PeriodPair) (z₀ z : ℂ)
    (hz : ∀ ω ∈ L.lattice, z + ω ∉ frontier (periodParallelogram L.ω₁ L.ω₂ z₀)) :
    ∃! ω, ω ∈ L.lattice ∧ z + ω ∈ periodParallelogram L.ω₁ L.ω₂ z₀ := by
  set x0 := L.basis.repr (z - z₀) 0 with hx0
  set x1 := L.basis.repr (z - z₀) 1 with hx1
  have shift : ∀ (m n : ℤ) (i : Fin 2), L.basis.repr (z + ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) - z₀) i =
      L.basis.repr (z - z₀) i + (if i = 0 then (m : ℝ) else (n : ℝ)) := by
    intro m n i
    have : z + ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) - z₀ =
        (z - z₀) + (((m : ℝ) : ℂ) * L.ω₁ + ((n : ℝ) : ℂ) * L.ω₂) := by
      push_cast; ring
    rw [this, map_add, Finsupp.add_apply, repr_comb]
  have key : ∀ m n : ℤ, z + ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ∈ periodParallelogram L.ω₁ L.ω₂ z₀ ↔
      (x0 + m ∈ Ioo (0 : ℝ) 1 ∧ x1 + n ∈ Ioo (0 : ℝ) 1) := by
    intro m n
    rw [periodParallelogram_eq_preimage]
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, shiftHomeo_apply,
      Fin.forall_fin_two, shift]
    simp [hx0, hx1]
  have keyC : ∀ m n : ℤ,
      z + ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ∈ closedPeriodParallelogram L.ω₁ L.ω₂ z₀ ↔
      (x0 + m ∈ Icc (0 : ℝ) 1 ∧ x1 + n ∈ Icc (0 : ℝ) 1) := by
    intro m n
    rw [closedPeriodParallelogram_eq_preimage]
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, shiftHomeo_apply,
      Fin.forall_fin_two, shift]
    simp [hx0, hx1]
  have hA : ∀ m n : ℤ, (x0 + m ∈ Icc (0 : ℝ) 1 ∧ x1 + n ∈ Icc (0 : ℝ) 1) →
      (x0 + m ∈ Ioo (0 : ℝ) 1 ∧ x1 + n ∈ Ioo (0 : ℝ) 1) := by
    intro m n h
    by_contra hn
    apply hz ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) (PeriodPair.mem_lattice.2 ⟨m, n, rfl⟩)
    rw [frontier_periodParallelogram]
    exact ⟨(keyC m n).2 h, fun hP => hn ((key m n).1 hP)⟩
  have f0 := Int.floor_le x0
  have f0' := Int.lt_floor_add_one x0
  have f1 := Int.floor_le x1
  have f1' := Int.lt_floor_add_one x1
  have b0 : x0 + ((-⌊x0⌋ : ℤ) : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    have := hA (-⌊x0⌋) (-⌊x1⌋) ⟨⟨by push_cast; linarith, by push_cast; linarith⟩,
      ⟨by push_cast; linarith, by push_cast; linarith⟩⟩
    exact this.1
  have b1 : x1 + ((-⌊x1⌋ : ℤ) : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    have := hA (-⌊x0⌋) (-⌊x1⌋) ⟨⟨by push_cast; linarith, by push_cast; linarith⟩,
      ⟨by push_cast; linarith, by push_cast; linarith⟩⟩
    exact this.2
  refine ⟨(((-⌊x0⌋ : ℤ) : ℂ) * L.ω₁ + ((-⌊x1⌋ : ℤ) : ℂ) * L.ω₂),
    ⟨PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩, (key _ _).2 ⟨b0, b1⟩⟩, ?_⟩
  rintro ω ⟨hω, hP⟩
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hω
  obtain ⟨c0, c1⟩ := (key m n).1 hP
  have hm : m = -⌊x0⌋ := by
    have h1 : (m : ℝ) < (-⌊x0⌋ : ℤ) + 1 := by push_cast at b0 ⊢; linarith [c0.1, c0.2, b0.1, b0.2]
    have h2 : ((-⌊x0⌋ : ℤ) : ℝ) < m + 1 := by push_cast at b0 ⊢; linarith [c0.1, c0.2, b0.1, b0.2]
    have h1' : m < (-⌊x0⌋ : ℤ) + 1 := by exact_mod_cast h1
    have h2' : (-⌊x0⌋ : ℤ) < m + 1 := by exact_mod_cast h2
    omega
  have hn : n = -⌊x1⌋ := by
    have h1 : (n : ℝ) < (-⌊x1⌋ : ℤ) + 1 := by push_cast at b1 ⊢; linarith [c1.1, c1.2, b1.1, b1.2]
    have h2 : ((-⌊x1⌋ : ℤ) : ℝ) < n + 1 := by push_cast at b1 ⊢; linarith [c1.1, c1.2, b1.1, b1.2]
    have h1' : n < (-⌊x1⌋ : ℤ) + 1 := by exact_mod_cast h1
    have h2' : (-⌊x1⌋ : ℤ) < n + 1 := by exact_mod_cast h2
    omega
  rw [hm, hn]

/-! ### Doubly periodic functions -/

/-- Milne (pdf p. 90): if `{ω₁, ω₂}` is a basis of `Λ`, condition (19) is equivalent to
`f(z + ω₁) = f(z)` and `f(z + ω₂) = f(z)`. -/
@[kb "milne2006ec" "Ch. III, §2, (19) for a basis, pdf p. 90"]
theorem isPeriodicFor_iff (L : PeriodPair) (f : ℂ → ℂ) :
    IsPeriodicFor L.lattice f ↔ Function.Periodic f L.ω₁ ∧ Function.Periodic f L.ω₂ := by
  constructor
  · intro h
    exact ⟨fun z => h _ L.ω₁_mem_lattice z, fun z => h _ L.ω₂_mem_lattice z⟩
  · rintro ⟨h1, h2⟩ ω hω z
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hω
    have h1' : Function.Periodic f ((m : ℂ) * L.ω₁) := by
      simpa using h1.int_mul m
    have h2' : Function.Periodic f ((n : ℂ) * L.ω₂) := by
      simpa using h2.int_mul n
    exact (h1'.add_period h2') z

theorem isDoublyPeriodic_weierstrassP (L : PeriodPair) :
    IsDoublyPeriodic L.lattice L.weierstrassP :=
  ⟨L.meromorphic_weierstrassP, fun ω hω z => L.weierstrassP_add_coe z ⟨ω, hω⟩⟩

theorem isDoublyPeriodic_derivWeierstrassP (L : PeriodPair) :
    IsDoublyPeriodic L.lattice L.derivWeierstrassP := by
  refine ⟨?_, fun ω hω z => L.derivWeierstrassP_add_coe z ⟨ω, hω⟩⟩
  have := L.meromorphic_weierstrassP.deriv
  simpa using this

end NumberFieldKB.MilneEC.III
