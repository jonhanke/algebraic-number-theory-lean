import NumberFieldKB.MilneEC.Ch1Intersection
import NumberFieldKB.MilneEC.Ch1Resultant
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Control.Traversable.Equiv
import Mathlib.LinearAlgebra.TensorProduct.Submodule

/-!
# Milne, Elliptic Curves, Chapter I, Proposition 1.8 (existence) and Remark 1.9

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §1 (pdf pp. 16–17).  The proof that the dimension
$\dim_k k[X, Y]_{(0,0)}/(f, g)$ is finite on $\mathcal F(k)$ and has the properties (a)–(e) of
Proposition 1.8 (after Fulton 1969, III §3), which proves the named statement `Prop1_8`; and Remark 1.9:
the intersection number does not change when `k` is replaced by a larger field.

Finiteness: dividing by the greatest common divisor (a unit in the local ring, since it does not vanish at
the origin), `f` and `g` may be assumed coprime; their resultants in $Y$ and in $X$ are then nonzero
polynomials $r_1(X)$, $r_2(Y)$ in the ideal $(f, g)$, so $X^m$ and $Y^n$ lie in $(f, g)$ in the local ring,
and the quotient is a quotient of $k[X, Y]/(X^m, Y^n)$.  Property (c) comes from the exact sequence
$0 \to \mathcal O/(f, h) \xrightarrow{\,g\,} \mathcal O/(f, gh) \to \mathcal O/(f, g) \to 0$.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC

variable {k : Type*} [Field k]

/-- Decomposition by the greatest common divisor. -/
theorem exists_gcd_decomp (f g : MvPolynomial (Fin 2) k) (hfg : ¬ (f = 0 ∧ g = 0)) :
    ∃ d f' g' : MvPolynomial (Fin 2) k, f = d * f' ∧ g = d * g' ∧ d ≠ 0 ∧ IsRelPrime f' g' := by
  let := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial (Fin 2) k)
  have hd : gcd f g ≠ 0 := fun h => hfg ((gcd_eq_zero_iff f g).mp h)
  obtain ⟨f', hf'⟩ := gcd_dvd_left f g
  obtain ⟨g', hg'⟩ := gcd_dvd_right f g
  refine ⟨gcd f g, f', g', hf', hg', hd, ?_⟩
  intro e hef heg
  obtain ⟨a, ha⟩ := hef
  obtain ⟨b, hb⟩ := heg
  have : gcd f g * e ∣ gcd f g := by
    apply dvd_gcd
    · exact ⟨a, by rw [mul_assoc, ← ha]; exact hf'⟩
    · exact ⟨b, by rw [mul_assoc, ← hb]; exact hg'⟩
  obtain ⟨c, hc⟩ := this
  have : e * c = 1 := by
    have h2 : gcd f g * (e * c) = gcd f g * 1 := by rw [mul_one]; nth_rewrite 2 [hc]; ring
    exact mul_left_cancel₀ hd h2
  exact IsUnit.of_mul_eq_one _ this

/-- Evaluation at the origin commutes with extension of the base field. -/
theorem eval_zero_baseChange {K : Type*} [Field K] [Algebra k K] (p : MvPolynomial (Fin 2) k) :
    eval (0 : Fin 2 → K) (baseChange K p) = algebraMap k K (eval (0 : Fin 2 → k) p) := by
  induction p using MvPolynomial.induction_on <;> simp_all

/-- A divisor of a polynomial not vanishing at the origin does not vanish there. -/
theorem eval_ne_zero_of_dvd {K : Type*} [Field K] {a b : MvPolynomial (Fin 2) K} (hab : a ∣ b)
    (hb : eval (0 : Fin 2 → K) b ≠ 0) : eval (0 : Fin 2 → K) a ≠ 0 := by
  intro h0
  obtain ⟨c, rfl⟩ := hab
  apply hb
  rw [map_mul, h0, zero_mul]

/-- A pair in $\mathcal F(k)$ is not the pair of zero polynomials. -/
theorem ncf_not_both_zero {f g : MvPolynomial (Fin 2) k} (h : NoCommonFactorAtOrigin f g) :
    ¬ (f = 0 ∧ g = 0) := by
  rintro ⟨rfl, rfl⟩
  exact h 0 dvd_rfl dvd_rfl (by simp)

/-- Base change preserves $\mathcal F(k)$ (the proof of `NoCommonFactorAtOrigin.baseChange`). -/
theorem ncf_baseChange_aux {f g : MvPolynomial (Fin 2) k}
    (h : NoCommonFactorAtOrigin f g) (K : Type*) [Field K] [Algebra k K] :
    NoCommonFactorAtOrigin (baseChange K f) (baseChange K g) := by
  obtain ⟨d, f', g', hf, hg, hd0, hrel⟩ := exists_gcd_decomp f g (ncf_not_both_zero h)
  let := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial (Fin 2) K)
  have hdev : eval (0 : Fin 2 → k) d ≠ 0 := h d ⟨f', hf⟩ ⟨g', hg⟩
  have hrelK := corollary_1_25 (f := f') (g := g') hrel K
  intro e hef heg
  have hf' : baseChange K f = baseChange K d * baseChange K f' := by rw [hf]; exact map_mul (MvPolynomial.map (algebraMap k K)) d f'
  have hg' : baseChange K g = baseChange K d * baseChange K g' := by rw [hg]; exact map_mul (MvPolynomial.map (algebraMap k K)) d g'
  rw [hf'] at hef
  rw [hg'] at heg
  have h1 : e ∣ gcd (baseChange K d * baseChange K f') (baseChange K d * baseChange K g') :=
    dvd_gcd hef heg
  have h2 := gcd_mul_left' (baseChange K d) (baseChange K f') (baseChange K g')
  have h3 : IsUnit (gcd (baseChange K f') (baseChange K g')) :=
    gcd_isUnit_iff_isRelPrime.mpr hrelK
  have h4 : e ∣ baseChange K d := by
    have := h1.trans h2.dvd
    exact this.trans ((mul_dvd_mul_left _ (isUnit_iff_dvd_one.mp h3)).trans (by simp))
  have : eval (0 : Fin 2 → K) (baseChange K d) ≠ 0 := by
    rw [eval_zero_baseChange]
    exact (map_ne_zero_iff _ (algebraMap k K).injective).mpr hdev
  exact eval_ne_zero_of_dvd h4 this

/-! ### The local ring -/

/-- Membership in the complement of the origin ideal is nonvanishing at the origin. -/
theorem mem_primeCompl_originIdeal {s : MvPolynomial (Fin 2) k} :
    s ∈ (originIdeal k).primeCompl ↔ eval (0 : Fin 2 → k) s ≠ 0 := by
  simp [originIdeal, Ideal.primeCompl, RingHom.mem_ker]

/-- Polynomials not vanishing at the origin are units in the local ring. -/
theorem isUnit_algebraMap_of_eval_ne_zero {s : MvPolynomial (Fin 2) k}
    (hs : eval (0 : Fin 2 → k) s ≠ 0) : IsUnit (algebraMap _ (LocalRingAtOrigin k) s) :=
  IsLocalization.map_units (LocalRingAtOrigin k) (⟨s, mem_primeCompl_originIdeal.mpr hs⟩ :
    (originIdeal k).primeCompl)

/-- Multiplying both generators of an ideal by a unit does not change it. -/
theorem span_pair_unit_mul {R : Type*} [CommRing R] {u : R} (hu : IsUnit u) (a b : R) :
    Ideal.span {u * a, u * b} = Ideal.span {a, b} := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · have := Ideal.mul_mem_left (Ideal.span {u * x, u * b}) v
        (Ideal.subset_span (by simp) : u * x ∈ Ideal.span {u * x, u * b})
      rwa [← mul_assoc, mul_comm v, hv, one_mul] at this
    · have := Ideal.mul_mem_left (Ideal.span {u * a, u * x}) v
        (Ideal.subset_span (by simp) : u * x ∈ Ideal.span {u * a, u * x})
      rwa [← mul_assoc, mul_comm v, hv, one_mul] at this

/-- The map from the polynomial ring to its localization is injective. -/
theorem algebraMap_injective_localRing :
    Function.Injective (algebraMap (MvPolynomial (Fin 2) k) (LocalRingAtOrigin k)) :=
  IsLocalization.injective (LocalRingAtOrigin k) (Ideal.primeCompl_le_nonZeroDivisors (originIdeal k))

/-- Every element of the local ring is a fraction with denominator not vanishing at the origin. -/
theorem exists_frac (u : LocalRingAtOrigin k) :
    ∃ (a s : MvPolynomial (Fin 2) k), eval (0 : Fin 2 → k) s ≠ 0 ∧
      u * algebraMap _ _ s = algebraMap _ _ a := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (originIdeal k).primeCompl u
  exact ⟨a, s, mem_primeCompl_originIdeal.mp s.2, h⟩

/-- Cancelling a common factor: if `g w = a f` in the local ring with `(f, g)` in $\mathcal F(k)$,
then `f` divides `w` in the local ring. -/
theorem localRing_dvd_of_mul_eq {f g : MvPolynomial (Fin 2) k} (hfg : NoCommonFactorAtOrigin f g)
    (w a : LocalRingAtOrigin k)
    (h : algebraMap _ _ g * w = a * algebraMap _ (LocalRingAtOrigin k) f) :
    ∃ c, w = c * algebraMap _ (LocalRingAtOrigin k) f := by
  set ι := algebraMap (MvPolynomial (Fin 2) k) (LocalRingAtOrigin k) with hι
  obtain ⟨d, f', g', hf, hg, hd0, hrel⟩ := exists_gcd_decomp f g (ncf_not_both_zero hfg)
  have hdev : eval (0 : Fin 2 → k) d ≠ 0 := hfg d ⟨f', hf⟩ ⟨g', hg⟩
  obtain ⟨vd, hvd⟩ := (isUnit_algebraMap_of_eval_ne_zero hdev).exists_right_inv
  have h1 : ι g' * w = a * ι f' := by
    rw [hf, hg, map_mul, map_mul] at h
    have : ι d * (ι g' * w) = ι d * (a * ι f') := by linear_combination h
    exact mul_left_cancel₀ (isUnit_algebraMap_of_eval_ne_zero hdev).ne_zero this
  obtain ⟨w0, s, hs, hw⟩ := exists_frac w
  obtain ⟨a0, t, ht, ha⟩ := exists_frac a
  have h2 : ι (g' * w0 * t) = ι (a0 * f' * s) := by
    simp only [map_mul]
    rw [← hw, ← ha]
    linear_combination (ι t * ι s) * h1
  have h3 := algebraMap_injective_localRing h2
  have h4 : f' ∣ w0 * t := by
    apply hrel.dvd_of_dvd_mul_left
    exact ⟨a0 * s, by linear_combination h3⟩
  obtain ⟨e, he⟩ := h4
  obtain ⟨vs, hvs⟩ := (isUnit_algebraMap_of_eval_ne_zero hs).exists_right_inv
  obtain ⟨vt, hvt⟩ := (isUnit_algebraMap_of_eval_ne_zero ht).exists_right_inv
  refine ⟨vd * ι e * vs * vt, ?_⟩
  have e5 : ι w0 * ι t = ι f' * ι e := by rw [← map_mul, ← map_mul, he]
  rw [hf, map_mul]
  linear_combination (-w * ι t * vt) * hvs + (-w) * hvt + (ι t * vs * vt) * hw + (vs * vt) * e5 +
    (-(ι f' * ι e * vs * vt)) * hvd

/-! ### Properties (a) to (e) -/

/-- Evaluation at the origin as a `k`-algebra map on the local ring. -/
noncomputable def evLocal : LocalRingAtOrigin k →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := (originIdeal k).primeCompl)
    (f := (MvPolynomial.aeval (0 : Fin 2 → k) : MvPolynomial (Fin 2) k →ₐ[k] k))
    (fun y => by
      have := mem_primeCompl_originIdeal.mp y.2
      simpa [MvPolynomial.coe_aeval_eq_eval] using this.isUnit)

/-- Evaluation on the local ring extends evaluation at the origin. -/
theorem evLocal_algebraMap (a : MvPolynomial (Fin 2) k) :
    evLocal (algebraMap _ (LocalRingAtOrigin k) a) = eval (0 : Fin 2 → k) a := by
  simp [evLocal, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq,
    MvPolynomial.coe_aeval_eq_eval]

/-- Property (a): the local quotient by $(X, Y)$ has dimension one. -/
theorem finrank_X_Y :
    Module.finrank k (LocalQuotient (X 0 : MvPolynomial (Fin 2) k) (X 1)) = 1 := by
  have hsurj : Function.Surjective (evLocal (k := k)) := by
    intro c
    refine ⟨algebraMap (MvPolynomial (Fin 2) k) (LocalRingAtOrigin k) (C c), ?_⟩
    rw [evLocal_algebraMap]; simp
  have hker : RingHom.ker (evLocal (k := k)) = Ideal.span
      {algebraMap _ (LocalRingAtOrigin k) (X 0 : MvPolynomial (Fin 2) k),
      algebraMap _ (LocalRingAtOrigin k) (X 1 : MvPolynomial (Fin 2) k)} := by
    apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker] at hz
      obtain ⟨a, s, hs, hzs⟩ := exists_frac z
      have ha : eval (0 : Fin 2 → k) a = 0 := by
        have := congrArg evLocal hzs
        rw [map_mul, evLocal_algebraMap, evLocal_algebraMap, hz, zero_mul] at this
        exact this.symm
      have hmem : a ∈ Ideal.span (X '' ({0, 1} : Set (Fin 2)) : Set (MvPolynomial (Fin 2) k)) := by
        rw [mem_ideal_span_X_image]
        intro m hm
        by_contra hcon
        push Not at hcon
        have hm0 : m = 0 := by
          ext i
          fin_cases i
          · simpa using hcon 0 (by simp)
          · simpa using hcon 1 (by simp)
        subst hm0
        rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq, ← eval_zero] at hm
        exact hm ha
      rw [Set.image_pair] at hmem
      obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hmem
      obtain ⟨vs, hvs⟩ := (isUnit_algebraMap_of_eval_ne_zero hs).exists_right_inv
      refine Ideal.mem_span_pair.mpr ⟨algebraMap _ _ c * vs, algebraMap _ _ d * vs, ?_⟩
      have h2 : algebraMap _ (LocalRingAtOrigin k) (c * X 0 + d * X 1) = z * algebraMap _ _ s := by
        rw [hcd, hzs]
      simp only [map_add, map_mul] at h2
      linear_combination vs * h2 + z * hvs
    · rw [Ideal.span_le]
      rintro x (rfl | rfl) <;> simp [evLocal_algebraMap]
  have e1 := Ideal.quotientKerAlgEquivOfSurjective hsurj
  have e2 := Ideal.quotientEquivAlgOfEq k hker.symm
  have := ((e2.trans e1).toLinearEquiv).finrank_eq
  rw [this, Module.finrank_self]

/-- Equal ideals give quotients of equal dimension. -/
theorem finrank_quotient_congr {R : Type*} [CommRing R] [Algebra k R] {I J : Ideal R} (h : I = J) :
    Module.finrank k (R ⧸ I) = Module.finrank k (R ⧸ J) := by
  subst h; rfl

/-- Property (b). -/
theorem localIntersectionNumber_symm (f g : MvPolynomial (Fin 2) k) :
    localIntersectionNumber f g = localIntersectionNumber g f := by
  unfold localIntersectionNumber LocalQuotient
  exact finrank_quotient_congr (by rw [Set.pair_comm])

/-- Property (d). -/
theorem localIntersectionNumber_add_mul (f g h : MvPolynomial (Fin 2) k) :
    localIntersectionNumber f (g + h * f) = localIntersectionNumber f g := by
  unfold localIntersectionNumber LocalQuotient
  refine finrank_quotient_congr ?_
  rw [map_add, map_mul, Set.pair_comm (algebraMap _ _ f), Set.pair_comm (algebraMap _ _ f),
    Ideal.span_pair_add_mul_right]

/-- Property (e). -/
theorem localIntersectionNumber_eq_zero (f g : MvPolynomial (Fin 2) k)
    (hg : eval (0 : Fin 2 → k) g ≠ 0) : localIntersectionNumber f g = 0 := by
  unfold localIntersectionNumber
  have : Subsingleton (LocalQuotient f g) := by
    rw [LocalQuotient, Ideal.Quotient.subsingleton_iff, Ideal.eq_top_iff_one]
    obtain ⟨v, hv⟩ := (isUnit_algebraMap_of_eval_ne_zero hg).exists_right_inv
    have := Ideal.mul_mem_left (Ideal.span {algebraMap _ (LocalRingAtOrigin k) f,
      algebraMap _ (LocalRingAtOrigin k) g}) v
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)) :
        algebraMap _ (LocalRingAtOrigin k) g ∈ _)
    rwa [mul_comm, hv] at this
  exact Module.finrank_zero_of_subsingleton

/-- If `(f, g)` and `(f, h)` lie in $\mathcal F(k)$, so does `(f, g h)`. -/
theorem ncf_mul_right {f g h : MvPolynomial (Fin 2) k} (hg : NoCommonFactorAtOrigin f g)
    (hh : NoCommonFactorAtOrigin f h) : NoCommonFactorAtOrigin f (g * h) := by
  have hne : ¬ (f = 0 ∧ g * h = 0) := by
    rintro ⟨rfl, h0⟩
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact ncf_not_both_zero hg ⟨rfl, h0⟩
    · exact ncf_not_both_zero hh ⟨rfl, h0⟩
  intro d hdf hdgh
  induction d using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    exact absurd ⟨zero_dvd_iff.mp hdf, zero_dvd_iff.mp hdgh⟩ hne
  | h₂ x hx => exact eval_zero_ne_zero_of_isUnit hx
  | h₃ a p ha hp ih =>
    have h1 : eval (0 : Fin 2 → k) a ≠ 0 := ih ((dvd_mul_left a p).trans hdf)
      ((dvd_mul_left a p).trans hdgh)
    have h2 : eval (0 : Fin 2 → k) p ≠ 0 := by
      have hpf : p ∣ f := (dvd_mul_right p a).trans hdf
      have hpgh : p ∣ g * h := (dvd_mul_right p a).trans hdgh
      rcases hp.dvd_or_dvd hpgh with hpg | hph
      · exact hg p hpf hpg
      · exact hh p hpf hph
    rw [map_mul]
    exact mul_ne_zero h2 h1

/-! ### Finiteness -/

/-- Coprime nonzero polynomials: the ideal contains a nonzero polynomial in $X$ alone. -/
theorem exists_ofX_mem_span {f g : MvPolynomial (Fin 2) k} (hf : f ≠ 0) (hg : g ≠ 0)
    (hrel : IsRelPrime f g) :
    ∃ r : Polynomial k, r ≠ 0 ∧ ofX r ∈ Ideal.span {f, g} := by
  by_cases hdeg : 0 < degY f ∨ 0 < degY g
  · obtain ⟨a, b, hab, -, -⟩ := prop_1_24_a hf hg hdeg
    refine ⟨resultantY f g, ?_, ?_⟩
    · intro h0
      obtain ⟨h, hh, hhf, hhg⟩ := (prop_1_24_b hf hg).mp h0
      have := Polynomial.degree_eq_zero_of_isUnit ((hrel hhf hhg).map yPolyEquiv)
      exact absurd hh (by rw [degY, this]; exact lt_irrefl _)
    · rw [← hab]
      exact Ideal.mem_span_pair.mpr ⟨a, b, rfl⟩
  · push Not at hdeg
    have hF : yPolyEquiv f ≠ 0 := (map_ne_zero_iff _ yPolyEquiv.injective).mpr hf
    have h1 : yPolyEquiv f = Polynomial.C ((yPolyEquiv f).coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero hdeg.1
    have hc : (yPolyEquiv f).coeff 0 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact hF h1
    refine ⟨(yPolyEquiv f).coeff 0, hc, ?_⟩
    have : ofX ((yPolyEquiv f).coeff 0) = f := by
      apply yPolyEquiv.injective
      rw [yPolyEquiv_ofX]
      exact h1.symm
    rw [this]
    exact Ideal.subset_span (by simp)

/-- Coprime nonzero polynomials: the ideal contains a nonzero polynomial in $Y$ alone. -/
theorem exists_ofY_mem_span {f g : MvPolynomial (Fin 2) k} (hf : f ≠ 0) (hg : g ≠ 0)
    (hrel : IsRelPrime f g) :
    ∃ r : Polynomial k, r ≠ 0 ∧ Polynomial.aeval (X 1 : MvPolynomial (Fin 2) k) r ∈
      Ideal.span {f, g} := by
  set σ : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
    renameEquiv k (Equiv.swap (0 : Fin 2) 1) with hσ
  have hrel' : IsRelPrime (σ f) (σ g) := by
    intro e hef heg
    have h1 := map_dvd σ.symm hef
    have h2 := map_dvd σ.symm heg
    simp only [AlgEquiv.symm_apply_apply] at h1 h2
    simpa using (hrel h1 h2).map σ
  obtain ⟨r, hr, hmem⟩ := exists_ofX_mem_span (f := σ f) (g := σ g)
    ((map_ne_zero_iff _ σ.injective).mpr hf) ((map_ne_zero_iff _ σ.injective).mpr hg) hrel'
  refine ⟨r, hr, ?_⟩
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
  have := congrArg σ.symm hab
  rw [map_add, map_mul, map_mul, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply] at this
  have h3 : σ.symm (ofX r) = Polynomial.aeval (X 1 : MvPolynomial (Fin 2) k) r := by
    unfold ofX
    have := Polynomial.aeval_algHom_apply (σ.symm : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k)
      (X 0 : MvPolynomial (Fin 2) k) r
    change Polynomial.aeval (σ.symm (X 0)) r = σ.symm (Polynomial.aeval (X 0) r) at this
    rw [show σ.symm (X 0) = (X 1 : MvPolynomial (Fin 2) k) by simp [hσ]] at this
    exact this.symm
  rw [h3] at this
  exact Ideal.mem_span_pair.mpr ⟨σ.symm a, σ.symm b, this⟩

/-- Evaluating a polynomial in one variable substituted for a variable. -/
theorem eval_aeval_X (i : Fin 2) (v : Fin 2 → k) (p : Polynomial k) :
    eval v (Polynomial.aeval (X i : MvPolynomial (Fin 2) k) p) = p.eval (v i) := by
  have h := Polynomial.aeval_algHom_apply (aeval v : MvPolynomial (Fin 2) k →ₐ[k] k)
    (X i : MvPolynomial (Fin 2) k) p
  rw [← MvPolynomial.coe_aeval_eq_eval]
  change (aeval v) _ = _
  rw [← h]
  simp [Polynomial.aeval_def]

/-- A nonzero polynomial in one variable lying in the ideal gives a power of the variable in the
ideal of the local ring. -/
theorem exists_pow_mem_of_poly {J : Ideal (LocalRingAtOrigin k)} (i : Fin 2) {r : Polynomial k}
    (hr : r ≠ 0)
    (hmem : algebraMap _ (LocalRingAtOrigin k) (Polynomial.aeval (X i : MvPolynomial (Fin 2) k) r)
      ∈ J) :
    ∃ m : ℕ, algebraMap _ (LocalRingAtOrigin k) ((X i : MvPolynomial (Fin 2) k) ^ m) ∈ J := by
  obtain ⟨u, hqu, hu⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr 0
  simp only [map_zero, sub_zero] at hqu hu
  refine ⟨Polynomial.rootMultiplicity 0 r, ?_⟩
  have hev : eval (0 : Fin 2 → k) (Polynomial.aeval (X i : MvPolynomial (Fin 2) k) u) ≠ 0 := by
    rw [eval_aeval_X]
    intro h0
    exact hu (Polynomial.X_dvd_iff.mpr (by simpa [Polynomial.coeff_zero_eq_eval_zero] using h0))
  obtain ⟨v, hv⟩ := (isUnit_algebraMap_of_eval_ne_zero hev).exists_right_inv
  have := Ideal.mul_mem_right v J hmem
  rw [hqu] at this
  simp only [map_mul, map_pow, Polynomial.aeval_X] at this
  rw [map_pow]
  have e : algebraMap _ (LocalRingAtOrigin k) (X i : MvPolynomial (Fin 2) k) ^
      Polynomial.rootMultiplicity 0 r =
      algebraMap _ (LocalRingAtOrigin k) (X i : MvPolynomial (Fin 2) k) ^
      Polynomial.rootMultiplicity 0 r *
        (algebraMap _ (LocalRingAtOrigin k) (Polynomial.aeval (X i : MvPolynomial (Fin 2) k) u) *
          v) := by rw [hv, mul_one]
  rw [e, ← mul_assoc]
  exact this

/-- The image of an ideal element lies in the extended ideal. -/
theorem algebraMap_mem_span_pair {f g x : MvPolynomial (Fin 2) k} (hx : x ∈ Ideal.span {f, g}) :
    algebraMap _ (LocalRingAtOrigin k) x ∈ Ideal.span {algebraMap _ (LocalRingAtOrigin k) f,
      algebraMap _ (LocalRingAtOrigin k) g} := by
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
  rw [map_add, map_mul, map_mul]
  exact Ideal.mem_span_pair.mpr ⟨_, _, rfl⟩

/-- The ideal `(f, g)` of the local ring contains a power of `X` and a power of `Y`. -/
theorem exists_pow_mem {f g : MvPolynomial (Fin 2) k} (h : NoCommonFactorAtOrigin f g) :
    (∃ m : ℕ, algebraMap _ (LocalRingAtOrigin k) ((X 0 : MvPolynomial (Fin 2) k) ^ m) ∈
      Ideal.span {algebraMap _ (LocalRingAtOrigin k) f, algebraMap _ (LocalRingAtOrigin k) g}) ∧
    (∃ n : ℕ, algebraMap _ (LocalRingAtOrigin k) ((X 1 : MvPolynomial (Fin 2) k) ^ n) ∈
      Ideal.span {algebraMap _ (LocalRingAtOrigin k) f, algebraMap _ (LocalRingAtOrigin k) g}) := by
  obtain ⟨d, f', g', hf, hg, hd0, hrel⟩ := exists_gcd_decomp f g (ncf_not_both_zero h)
  have hdev : eval (0 : Fin 2 → k) d ≠ 0 := h d ⟨f', hf⟩ ⟨g', hg⟩
  have hJ : Ideal.span {algebraMap _ (LocalRingAtOrigin k) f, algebraMap _ (LocalRingAtOrigin k) g} =
      Ideal.span {algebraMap _ (LocalRingAtOrigin k) f', algebraMap _ (LocalRingAtOrigin k) g'} := by
    rw [hf, hg, map_mul, map_mul]
    exact span_pair_unit_mul (isUnit_algebraMap_of_eval_ne_zero hdev) _ _
  rw [hJ]
  have htop : ∀ (u : MvPolynomial (Fin 2) k), IsUnit u → u ∈ ({f', g'} : Set _) →
      (1 : LocalRingAtOrigin k) ∈ Ideal.span {algebraMap _ (LocalRingAtOrigin k) f',
        algebraMap _ (LocalRingAtOrigin k) g'} := by
    intro u hu hmem
    have : algebraMap _ (LocalRingAtOrigin k) u ∈ Ideal.span
        {algebraMap _ (LocalRingAtOrigin k) f', algebraMap _ (LocalRingAtOrigin k) g'} := by
      apply Ideal.subset_span
      rcases hmem with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    obtain ⟨v, hv⟩ := (hu.map (algebraMap (MvPolynomial (Fin 2) k) (LocalRingAtOrigin k))).exists_right_inv
    have := Ideal.mul_mem_right v _ this
    rwa [hv] at this
  by_cases hf0 : f' = 0
  · have hu : IsUnit g' := hrel (by rw [hf0]; exact dvd_zero _) dvd_rfl
    have h1 := htop g' hu (by simp)
    exact ⟨⟨0, by simpa using h1⟩, ⟨0, by simpa using h1⟩⟩
  by_cases hg0 : g' = 0
  · have hu : IsUnit f' := hrel dvd_rfl (by rw [hg0]; exact dvd_zero _)
    have h1 := htop f' hu (by simp)
    exact ⟨⟨0, by simpa using h1⟩, ⟨0, by simpa using h1⟩⟩
  obtain ⟨r1, hr1, hm1⟩ := exists_ofX_mem_span hf0 hg0 hrel
  obtain ⟨r2, hr2, hm2⟩ := exists_ofY_mem_span hf0 hg0 hrel
  exact ⟨exists_pow_mem_of_poly 0 hr1 (algebraMap_mem_span_pair hm1),
    exists_pow_mem_of_poly 1 hr2 (algebraMap_mem_span_pair hm2)⟩

/-- The structure map `k[X, Y] → k[X, Y]_{(0,0)}/(f, g)` as a `k`-algebra map. -/
noncomputable def toLocalQuotient (f g : MvPolynomial (Fin 2) k) :
    MvPolynomial (Fin 2) k →ₐ[k] LocalQuotient f g :=
  (Ideal.Quotient.mkₐ k _).comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k)
    (LocalRingAtOrigin k))

/-- Kernel of the structure map. -/
theorem toLocalQuotient_eq_zero_iff (f g x : MvPolynomial (Fin 2) k) :
    toLocalQuotient f g x = 0 ↔ algebraMap _ (LocalRingAtOrigin k) x ∈
      Ideal.span {algebraMap _ (LocalRingAtOrigin k) f, algebraMap _ (LocalRingAtOrigin k) g} :=
  Ideal.Quotient.eq_zero_iff_mem

/-- If powers of `X` and `Y` lie in the ideal, the local quotient is finite-dimensional. -/
theorem localQuotient_finite_of_pow_mem {f g : MvPolynomial (Fin 2) k} {m n : ℕ}
    (hm : algebraMap _ (LocalRingAtOrigin k) ((X 0 : MvPolynomial (Fin 2) k) ^ m) ∈
      Ideal.span {algebraMap _ (LocalRingAtOrigin k) f, algebraMap _ (LocalRingAtOrigin k) g})
    (hn : algebraMap _ (LocalRingAtOrigin k) ((X 1 : MvPolynomial (Fin 2) k) ^ n) ∈
      Ideal.span {algebraMap _ (LocalRingAtOrigin k) f, algebraMap _ (LocalRingAtOrigin k) g}) :
    Module.Finite k (LocalQuotient f g) := by
  set φ := toLocalQuotient f g with hφ
  set F : Fin (m + 1) × Fin (n + 1) → LocalQuotient f g :=
    fun ij => φ (X 0 ^ (ij.1 : ℕ) * X 1 ^ (ij.2 : ℕ)) with hF
  set S : Submodule k (LocalQuotient f g) := Submodule.span k (Set.range F) with hS
  have hmono : ∀ a b : ℕ, φ (X 0 ^ a * X 1 ^ b) ∈ S := by
    intro a b
    by_cases ha : a < m + 1
    · by_cases hb : b < n + 1
      · exact Submodule.subset_span ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
      · have : φ (X 0 ^ a * X 1 ^ b) = 0 := by
          rw [hφ, toLocalQuotient_eq_zero_iff]
          have e : (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) k) =
              (X 0 ^ a * X 1 ^ (b - (n + 1))) * X 1 ^ (n + 1) := by
            rw [mul_assoc, ← pow_add, show b - (n + 1) + (n + 1) = b by omega]
          rw [e, map_mul]
          refine Ideal.mul_mem_left _ _ ?_
          rw [map_pow, pow_succ', ← map_pow]
          exact Ideal.mul_mem_left _ _ hn
        rw [this]; exact S.zero_mem
    · have : φ (X 0 ^ a * X 1 ^ b) = 0 := by
        rw [hφ, toLocalQuotient_eq_zero_iff]
        have e : (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) k) =
            X 0 ^ (m + 1) * (X 0 ^ (a - (m + 1)) * X 1 ^ b) := by
          rw [← mul_assoc, ← pow_add, show m + 1 + (a - (m + 1)) = a by omega]
        rw [e, map_mul]
        refine Ideal.mul_mem_right _ _ ?_
        rw [map_pow, pow_succ', ← map_pow]
        exact Ideal.mul_mem_left _ _ hm
      rw [this]; exact S.zero_mem
  have hall : ∀ p, φ p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on' with
    | monomial u a =>
      have e : (monomial u a : MvPolynomial (Fin 2) k) = C a * (X 0 ^ (u 0) * X 1 ^ (u 1)) := by
        rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
      rw [e, ← MvPolynomial.smul_eq_C_mul, map_smul]
      exact S.smul_mem a (hmono _ _)
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
  set N : Subalgebra k (LocalQuotient f g) := φ.range with hN
  have : Module.Finite k S := Module.Finite.span_of_finite k (Set.finite_range F)
  have hNS : N.toSubmodule ≤ S := by
    rintro _ ⟨p, rfl⟩
    exact hall p
  have : FiniteDimensional k N.toSubmodule := Submodule.finiteDimensional_of_le hNS
  have hall' : ∀ q : LocalQuotient f g, q ∈ N := by
    intro q
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, s, hs, hus⟩ := exists_frac u
    have hxN : φ s ∈ N := ⟨s, rfl⟩
    have hxu : IsUnit (φ s) :=
      (isUnit_algebraMap_of_eval_ne_zero hs).map (Ideal.Quotient.mk _)
    let L : N.toSubmodule →ₗ[k] N.toSubmodule :=
      (LinearMap.mulLeft k (φ s)).restrict (fun v hv => N.mul_mem hxN hv)
    have hinj : Function.Injective L := by
      intro v w hvw
      apply Subtype.ext
      have : φ s * (v : LocalQuotient f g) = φ s * (w : LocalQuotient f g) :=
        congrArg Subtype.val hvw
      exact hxu.mul_left_cancel this
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨1, N.one_mem⟩
    have hxy : φ s * (y : LocalQuotient f g) = 1 := congrArg Subtype.val hy
    have hq : Ideal.Quotient.mk _ u * φ s = φ a := by
      change Ideal.Quotient.mk _ u * Ideal.Quotient.mk _ (algebraMap _ _ s) =
        Ideal.Quotient.mk _ (algebraMap _ _ a)
      rw [← map_mul, hus]
    have : Ideal.Quotient.mk _ u = φ a * (y : LocalQuotient f g) := by
      linear_combination (-(Ideal.Quotient.mk _ u : LocalQuotient f g)) * hxy +
        (y : LocalQuotient f g) * hq
    rw [this]
    exact N.mul_mem ⟨a, rfl⟩ y.2
  have htop : S = ⊤ := eq_top_iff.mpr fun q _ => hNS (hall' q)
  exact ⟨by rw [← htop]; exact Submodule.fg_span (Set.finite_range F)⟩

/-- For $(f, g) \in \mathcal F(k)$ the space $k[X, Y]_{(0,0)}/(f, g)$ is finite-dimensional. -/
theorem localQuotient_finite {f g : MvPolynomial (Fin 2) k} (h : NoCommonFactorAtOrigin f g) :
    Module.Finite k (LocalQuotient f g) := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := exists_pow_mem h
  exact localQuotient_finite_of_pow_mem hm hn

/-! ### Additivity -/

section Additivity

variable (f g h : MvPolynomial (Fin 2) k)

/-- Multiplication by `g`: $\mathcal O/(f, h) \to \mathcal O/(f, gh)$. -/
noncomputable def mulMap : LocalQuotient f h →ₗ[k] LocalQuotient f (g * h) :=
  (Submodule.mapQ (Ideal.span {algebraMap _ (LocalRingAtOrigin k) f,
      algebraMap _ (LocalRingAtOrigin k) h})
    (Ideal.span {algebraMap _ (LocalRingAtOrigin k) f, algebraMap _ (LocalRingAtOrigin k) (g * h)})
    (LinearMap.mulLeft (LocalRingAtOrigin k) (algebraMap _ (LocalRingAtOrigin k) g))
    (by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · rw [SetLike.mem_coe, Submodule.mem_comap]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · rw [SetLike.mem_coe, Submodule.mem_comap]
        change algebraMap _ (LocalRingAtOrigin k) g * algebraMap _ (LocalRingAtOrigin k) h ∈ _
        rw [← map_mul]
        exact Ideal.subset_span (by simp))).restrictScalars k

/-- The projection $\mathcal O/(f, gh) \to \mathcal O/(f, g)$. -/
noncomputable def projMap : LocalQuotient f (g * h) →ₗ[k] LocalQuotient f g :=
  (Submodule.mapQ (Ideal.span {algebraMap _ (LocalRingAtOrigin k) f,
      algebraMap _ (LocalRingAtOrigin k) (g * h)})
    (Ideal.span {algebraMap _ (LocalRingAtOrigin k) f, algebraMap _ (LocalRingAtOrigin k) g})
    LinearMap.id
    (by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [SetLike.mem_coe, Submodule.mem_comap, map_mul]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))).restrictScalars k

/-- Value of `mulMap` on a class. -/
theorem mulMap_mk (w : LocalRingAtOrigin k) :
    mulMap f g h (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ (algebraMap _ _ g * w) := rfl

/-- Value of `projMap` on a class. -/
theorem projMap_mk (w : LocalRingAtOrigin k) :
    projMap f g h (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ w := rfl

/-- Injectivity of multiplication by `g` (uses that `f` and `g` have no common factor at the origin). -/
theorem mulMap_injective {f g h : MvPolynomial (Fin 2) k} (hg : NoCommonFactorAtOrigin f g) :
    Function.Injective (mulMap f g h) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mulMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hx
  have h1 : algebraMap _ (LocalRingAtOrigin k) g * (w - b * algebraMap _ _ h) =
      (a * 1) * algebraMap _ (LocalRingAtOrigin k) f := by
    rw [map_mul] at hab
    linear_combination -hab
  obtain ⟨c, hc⟩ := localRing_dvd_of_mul_eq hg _ _ (by simpa using h1)
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.mem_span_pair.mpr ⟨c, b, ?_⟩
  linear_combination -hc

/-- The projection is surjective. -/
theorem projMap_surjective : Function.Surjective (projMap f g h) := by
  intro x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ w, rfl⟩

/-- Exactness in the middle. -/
theorem ker_projMap : LinearMap.ker (projMap f g h) = LinearMap.range (mulMap f g h) := by
  ext x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [LinearMap.mem_ker, projMap_mk, Ideal.Quotient.eq_zero_iff_mem, LinearMap.mem_range]
  constructor
  · intro hz
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hz
    refine ⟨Ideal.Quotient.mk _ b, ?_⟩
    rw [mulMap_mk, Ideal.Quotient.eq]
    refine Ideal.mem_span_pair.mpr ⟨-a, 0, ?_⟩
    linear_combination -hab
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mulMap_mk, Ideal.Quotient.eq] at hy
    have : z = algebraMap _ (LocalRingAtOrigin k) g * w - (algebraMap _ (LocalRingAtOrigin k) g * w - z) := by ring
    rw [this]
    refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))) ?_
    have hle : Ideal.span {algebraMap _ (LocalRingAtOrigin k) f,
        algebraMap _ (LocalRingAtOrigin k) (g * h)} ≤
        Ideal.span {algebraMap _ (LocalRingAtOrigin k) f, algebraMap _ (LocalRingAtOrigin k) g} := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [SetLike.mem_coe, map_mul]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    exact hle hy

/-- Property (c), by the exact sequence of the module docstring. -/
theorem localIntersectionNumber_mul {f g h : MvPolynomial (Fin 2) k}
    (hg : NoCommonFactorAtOrigin f g) (hh : NoCommonFactorAtOrigin f h) :
    localIntersectionNumber f (g * h) = localIntersectionNumber f g + localIntersectionNumber f h := by
  have hgh := ncf_mul_right hg hh
  have : Module.Finite k (LocalQuotient f (g * h)) := localQuotient_finite hgh
  have h2 := LinearMap.finrank_range_add_finrank_ker (projMap f g h)
  rw [LinearMap.range_eq_top.mpr (projMap_surjective f g h), finrank_top, ker_projMap,
    LinearMap.finrank_range_of_inj (mulMap_injective hg)] at h2
  unfold localIntersectionNumber
  omega

end Additivity

/-- The dimension of the local quotient has the properties (a)–(e) of Proposition 1.8. -/
theorem isIntersectionNumber_localIntersectionNumber :
    IsIntersectionNumber (localIntersectionNumber (k := k)) where
  X_Y := finrank_X_Y
  symm f g _ := localIntersectionNumber_symm f g
  mul_right _ _ _ hg hh := localIntersectionNumber_mul hg hh
  add_mul_right f g h _ := localIntersectionNumber_add_mul f g h
  eq_zero f g _ hg := localIntersectionNumber_eq_zero f g hg

/-- **Proposition 1.8, existence** (p. 16): the named statement `Prop1_8` holds. -/
@[kb "milne2006ec" "Ch. I, Prop. 1.8 (existence), pdf p. 17"]
theorem prop1_8_holds : Prop1_8 :=
  ⟨fun _ _ _ _ h => localQuotient_finite h, fun _ _ => isIntersectionNumber_localIntersectionNumber⟩

/-- $\mathcal F(k) \subseteq \mathcal F(K)$ for every field `K` containing `k` (proof of Proposition 1.8,
via Corollary 1.25). -/
@[kb "milne2006ec" "Ch. I, Prop. 1.8 (proof): F(k) ⊆ F(K), pdf p. 17"]
theorem NoCommonFactorAtOrigin.baseChange {f g : MvPolynomial (Fin 2) k}
    (h : NoCommonFactorAtOrigin f g) (K : Type*) [Field K] [Algebra k K] :
    NoCommonFactorAtOrigin (baseChange K f) (baseChange K g) :=
  ncf_baseChange_aux h K

/-- **Remark 1.9** (p. 17): $I(f, g)$ does not depend on whether `f` and `g` are regarded as polynomials
over `k` or over a larger field `K`; and $I(f, g) = \dim_k k[X, Y]_{(0,0)}/(f, g)$ for every field `k`
(by definition here, with `prop1_8_holds`). -/
@[kb "milne2006ec" "Ch. I, Rem. 1.9, pdf p. 17"]
theorem remark_1_9 {f g : MvPolynomial (Fin 2) k} (h : NoCommonFactorAtOrigin f g) (K : Type*)
    [Field K] [Algebra k K] :
    localIntersectionNumber (baseChange K f) (baseChange K g) = localIntersectionNumber f g := by
  set J : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ :=
    fun f g => localIntersectionNumber (baseChange K f) (baseChange K g) with hJ
  have hJI : IsIntersectionNumber J := by
    have hK := isIntersectionNumber_localIntersectionNumber (k := K)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hJ] using hK.X_Y
    · intro f g hfg
      exact hK.symm _ _ (hfg.baseChange K)
    · intro f g h hg hh
      simp only [hJ, map_mul]
      exact hK.mul_right _ _ _ (hg.baseChange K) (hh.baseChange K)
    · intro f g h hfg
      simp only [hJ, map_add, map_mul]
      exact hK.add_mul_right _ _ _ (hfg.baseChange K)
    · intro f g hfg hg
      simp only [hJ]
      refine hK.eq_zero _ _ (hfg.baseChange K) ?_
      rw [eval_zero_baseChange]
      exact (map_ne_zero_iff _ (algebraMap k K).injective).mpr hg
  exact intersectionNumber_unique hJI (isIntersectionNumber_localIntersectionNumber (k := k)) f g h


end NumberFieldKB.MilneEC
