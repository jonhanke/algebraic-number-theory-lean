import NumberFieldKB.ModularCurves.CuspInfinity

/-!
# Polynomial identities between meromorphic functions pass to Laurent expansions

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2. If $f_i = A_i / B_i$ with $A_i, B_i$ having
$q$-expansions and $B_i$ nowhere zero, and $G(f_1, f_2) = 0$ on $\mathbb H$ for $G \in \mathbb Q[X][Y]$, then
$G(\hat A_1/\hat B_1, \hat A_2/\hat B_2) = 0$ in $\mathbb C((q))$ (`eval_qHat_div_eq_zero`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex ModularForm

namespace NumberFieldKB.ModularCurves

/-- Evaluation of $G \in \mathbb Q[X][Y]$ at $(x, y)$ in a $\mathbb Q$-algebra. -/
noncomputable def evalQ2 {R : Type*} [CommRing R] [Algebra ℚ R] (G : ℚ[X][X]) (x y : R) : R :=
  G.eval₂ (Polynomial.eval₂RingHom (algebraMap ℚ R) x) y

/-- Ring homomorphisms commute with `evalQ2`. -/
theorem evalQ2_map {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (f : R →+* S)
    (G : ℚ[X][X]) (x y : R) : f (evalQ2 G x y) = evalQ2 G (f x) (f y) := by
  unfold evalQ2
  rw [Polynomial.hom_eval₂]
  congr 2
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

/-- `qHat d` is nonzero for a nowhere-vanishing `d`. -/
theorem qHat_ne_zero_of_nowhere {d : ℍ → ℂ} (hd : IsQExp d) (hd0 : ∀ z, d z ≠ 0) : qHat d ≠ 0 := by
  rw [Ne, qHat_eq_zero_iff hd]
  intro h
  exact hd0 UpperHalfPlane.I (congrFun h _)

/-- The functions `f` with `d ^ n * f` having a `q`-expansion for some `n`. -/
def qMerD (d : ℍ → ℂ) (hd : IsQExp d) : Subalgebra ℚ (ℍ → ℂ) where
  carrier := {f | ∃ n : ℕ, IsQExp (d ^ n * f)}
  mul_mem' := by
    rintro f g ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : d ^ (n + m) * (f * g) = (d ^ n * f) * (d ^ m * g) := by ring
    rw [this]
    exact hn.mul hm
  one_mem' := ⟨0, by simpa using IsQExp.one⟩
  add_mem' := by
    rintro f g ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : d ^ (n + m) * (f + g) = d ^ m * (d ^ n * f) + d ^ n * (d ^ m * g) := by ring
    rw [this]
    exact ((hd.pow m).mul hn).add ((hd.pow n).mul hm)
  zero_mem' := ⟨0, by simpa using IsQExp.zero⟩
  algebraMap_mem' := by
    intro r
    refine ⟨0, ?_⟩
    have := IsQExp.const (r : ℂ)
    convert this using 1
    funext z
    simp

/-- The Laurent expansion `qHat (d ^ n * f) / qHat d ^ n` does not depend on `n`. -/
theorem qHat_div_eq' {d : ℍ → ℂ} (hd : IsQExp d) (hd0 : ∀ z, d z ≠ 0) {f : ℍ → ℂ} {n m : ℕ}
    (hn : IsQExp (d ^ n * f)) (hm : IsQExp (d ^ m * f)) :
    qHat (d ^ n * f) / qHat d ^ n = qHat (d ^ m * f) / qHat d ^ m := by
  have h0 := qHat_ne_zero_of_nowhere hd hd0
  rw [div_eq_div_iff (pow_ne_zero _ h0) (pow_ne_zero _ h0), ← qHat_pow hd, ← qHat_pow hd,
    ← qHat_mul hn (hd.pow m), ← qHat_mul hm (hd.pow n)]
  congr 1
  ring

/-- The Laurent expansion of an element of `qMerD d hd`. -/
noncomputable def qMerDFun {d : ℍ → ℂ} (hd : IsQExp d) (f : qMerD d hd) : LaurentSeries ℂ :=
  qHat (d ^ f.2.choose * f.1) / qHat d ^ f.2.choose

/-- `qMerDFun` is computed with any admissible exponent. -/
theorem qMerDFun_eq {d : ℍ → ℂ} (hd : IsQExp d) (hd0 : ∀ z, d z ≠ 0) (f : qMerD d hd) {n : ℕ}
    (hn : IsQExp (d ^ n * f.1)) : qMerDFun hd f = qHat (d ^ n * f.1) / qHat d ^ n :=
  qHat_div_eq' hd hd0 f.2.choose_spec hn

/-- `qMerDFun` agrees with `qHat` on functions with a `q`-expansion. -/
theorem qMerDFun_of_isQExp {d : ℍ → ℂ} (hd : IsQExp d) (hd0 : ∀ z, d z ≠ 0) (f : qMerD d hd)
    (hf : IsQExp f.1) : qMerDFun hd f = qHat f.1 := by
  rw [qMerDFun_eq hd hd0 f (n := 0) (by simpa using hf)]
  simp

/-- The Laurent expansion as a ring map on `qMerD d hd`. -/
noncomputable def qMerDHom {d : ℍ → ℂ} (hd : IsQExp d) (hd0 : ∀ z, d z ≠ 0) :
    qMerD d hd →+* LaurentSeries ℂ where
  toFun := qMerDFun hd
  map_one' := by
    rw [qMerDFun_of_isQExp hd hd0 1 IsQExp.one]
    exact qHat_one
  map_mul' f g := by
    obtain ⟨n, hn⟩ := f.2
    obtain ⟨m, hm⟩ := g.2
    have e : d ^ (n + m) * (f.1 * g.1) = (d ^ n * f.1) * (d ^ m * g.1) := by ring
    have hnm : IsQExp (d ^ (n + m) * (f.1 * g.1)) := by
      rw [e]; exact hn.mul hm
    rw [qMerDFun_eq hd hd0 (f * g) (n := n + m) hnm, qMerDFun_eq hd hd0 f hn, qMerDFun_eq hd hd0 g hm]
    change qHat (d ^ (n + m) * (f.1 * g.1)) / _ = _
    rw [e, qHat_mul hn hm, pow_add]
    ring
  map_zero' := by
    rw [qMerDFun_of_isQExp hd hd0 0 IsQExp.zero]
    change qHat (0 : ℍ → ℂ) = 0
    rw [qHat, qExpansion_zero, map_zero]
  map_add' f g := by
    obtain ⟨n, hn⟩ := f.2
    obtain ⟨m, hm⟩ := g.2
    have h0 := qHat_ne_zero_of_nowhere hd hd0
    have e : d ^ (n + m) * (f.1 + g.1) = d ^ m * (d ^ n * f.1) + d ^ n * (d ^ m * g.1) := by ring
    have h1 : IsQExp (d ^ m * (d ^ n * f.1)) := (hd.pow m).mul hn
    have h2 : IsQExp (d ^ n * (d ^ m * g.1)) := (hd.pow n).mul hm
    have hnm : IsQExp (d ^ (n + m) * (f.1 + g.1)) := by rw [e]; exact h1.add h2
    rw [qMerDFun_eq hd hd0 (f + g) (n := n + m) hnm, qMerDFun_eq hd hd0 f hn, qMerDFun_eq hd hd0 g hm]
    change qHat (d ^ (n + m) * (f.1 + g.1)) / _ = _
    rw [e, qHat_add h1 h2, qHat_mul (hd.pow m) hn, qHat_mul (hd.pow n) hm, qHat_pow hd, qHat_pow hd,
      pow_add]
    field_simp

/-- **Transfer of polynomial identities to Laurent expansions.** -/
theorem eval_qHat_div_eq_zero {A₁ B₁ A₂ B₂ : ℍ → ℂ} (hA₁ : IsQExp A₁) (hB₁ : IsQExp B₁) (hA₂ : IsQExp A₂)
    (hB₂ : IsQExp B₂) (hB₁0 : ∀ z, B₁ z ≠ 0) (hB₂0 : ∀ z, B₂ z ≠ 0) (G : ℚ[X][X])
    (hG : ∀ z, evalQ2 G (A₁ z / B₁ z) (A₂ z / B₂ z) = 0) :
    evalQ2 G (qHat A₁ / qHat B₁) (qHat A₂ / qHat B₂) = 0 := by
  have hd : IsQExp (B₁ * B₂) := hB₁.mul hB₂
  have hd0 : ∀ z, (B₁ * B₂) z ≠ 0 := fun z => mul_ne_zero (hB₁0 z) (hB₂0 z)
  have h1 : qHat B₁ ≠ 0 := qHat_ne_zero_of_nowhere hB₁ hB₁0
  have h2 : qHat B₂ ≠ 0 := qHat_ne_zero_of_nowhere hB₂ hB₂0
  let x₁ : qMerD (B₁ * B₂) hd := ⟨A₁ / B₁, 1, by
    have : (B₁ * B₂) ^ 1 * (A₁ / B₁) = A₁ * B₂ := by
      funext z; have := hB₁0 z; simp; field_simp
    rw [this]; exact hA₁.mul hB₂⟩
  let x₂ : qMerD (B₁ * B₂) hd := ⟨A₂ / B₂, 1, by
    have : (B₁ * B₂) ^ 1 * (A₂ / B₂) = A₂ * B₁ := by
      funext z; have := hB₂0 z; simp; field_simp
    rw [this]; exact hA₂.mul hB₁⟩
  have e1 : qMerDHom hd hd0 x₁ = qHat A₁ / qHat B₁ := by
    change qMerDFun hd x₁ = _
    rw [qMerDFun_eq hd hd0 x₁ (n := 1) (by
      have : (B₁ * B₂) ^ 1 * (A₁ / B₁) = A₁ * B₂ := by
        funext z; have := hB₁0 z; simp; field_simp
      show IsQExp ((B₁ * B₂) ^ 1 * (A₁ / B₁))
      rw [this]; exact hA₁.mul hB₂)]
    show qHat ((B₁ * B₂) ^ 1 * (A₁ / B₁)) / qHat (B₁ * B₂) ^ 1 = _
    have : (B₁ * B₂) ^ 1 * (A₁ / B₁) = A₁ * B₂ := by
      funext z; have := hB₁0 z; simp; field_simp
    rw [this, qHat_mul hA₁ hB₂, qHat_mul hB₁ hB₂]
    field_simp
  have e2 : qMerDHom hd hd0 x₂ = qHat A₂ / qHat B₂ := by
    change qMerDFun hd x₂ = _
    rw [qMerDFun_eq hd hd0 x₂ (n := 1) (by
      have : (B₁ * B₂) ^ 1 * (A₂ / B₂) = A₂ * B₁ := by
        funext z; have := hB₂0 z; simp; field_simp
      show IsQExp ((B₁ * B₂) ^ 1 * (A₂ / B₂))
      rw [this]; exact hA₂.mul hB₁)]
    show qHat ((B₁ * B₂) ^ 1 * (A₂ / B₂)) / qHat (B₁ * B₂) ^ 1 = _
    have : (B₁ * B₂) ^ 1 * (A₂ / B₂) = A₂ * B₁ := by
      funext z; have := hB₂0 z; simp; field_simp
    rw [this, qHat_mul hA₂ hB₁, qHat_mul hB₁ hB₂]
    field_simp
  have hzero : evalQ2 G x₁ x₂ = 0 := by
    apply Subtype.ext
    have := evalQ2_map ((qMerD (B₁ * B₂) hd).val : qMerD (B₁ * B₂) hd →+* (ℍ → ℂ)) G x₁ x₂
    change (evalQ2 G x₁ x₂).1 = 0
    change ((qMerD (B₁ * B₂) hd).val : qMerD (B₁ * B₂) hd →+* (ℍ → ℂ)) (evalQ2 G x₁ x₂) = _ at this
    refine this.trans ?_
    funext z
    exact (evalQ2_map (Pi.evalRingHom (fun _ : ℍ => ℂ) z) G (A₁ / B₁) (A₂ / B₂)).trans (hG z)
  rw [← e1, ← e2, ← evalQ2_map, hzero, map_zero]

end NumberFieldKB.ModularCurves
