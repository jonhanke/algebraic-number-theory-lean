import NumberFieldKB.MilneEC.Ch4Selmer
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Milne, Elliptic Curves, Chapter IV §3: toward the finiteness of the Selmer group

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 3 ("The finiteness of the
Selmer group"): Lemma 3.8, the review of algebraic number theory (3.9–3.12) and Lemma 3.13.  Locators give the pdf
page of the text `ectext6` (printed page = pdf page − 8).

Conventions.
* For a number field $K$ and a field $L$ with $K \subseteq L \subseteq \bar K$ (an `IntermediateField`), $H^1(L, M)$
  is the cohomology of the subgroup `L.fixingSubgroup` of $\operatorname{Gal}(\bar K/K)$ (which is
  $\operatorname{Gal}(\bar K/L)$, $\bar K$ being an algebraic closure of $L$), and the restriction map is
  `resToField`.
* In 3.12 and 3.13, $T$ is a finite set of prime ideals of $\mathcal{O}_L$ (Milne's $T$ also contains the infinite
  places, which play no role in these statements).  $\operatorname{ord}_{\mathfrak p}$ is minus the exponent of
  Mathlib's multiplicative valuation `valuationOfNeZero`.  Milne defines $U_T$ and $C_T$ "by the exactness of"
  $0 \to U_T \to L^\times \to \bigoplus_{\mathfrak p \notin T} \mathbb{Z} \to C_T \to 0$; here they are the kernel and
  cokernel of `ordAway T`.  The group $N$ of Lemma 3.13 is Mathlib's Selmer group $L(T, n)$ of the Dedekind domain
  $\mathcal{O}_L$ (`IsDedekindDomain.selmerGroup`).
-/

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine NumberField
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical nonZeroDivisors

set_option backward.isDefEq.respectTransparency false

namespace NumberFieldKB.MilneEC

/-! ## Lemma 3.8 -/

section Lemma38

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

/-- The restriction map $H^1(K, M) \to H^1(L, M)$ for an intermediate field $K \subseteq L \subseteq \bar K$. -/
noncomputable def resToField (L : IntermediateField K (AlgebraicClosure K)) (n : ℤ) :
    H1 (torsionRep W (AlgebraicClosure K) n) →+
      H1 (Rep.res L.fixingSubgroup.subtype (torsionRep W (AlgebraicClosure K) n)) :=
  (map L.fixingSubgroup.subtype (𝟙 _) 1).hom.toAddMonoidHom

omit [DecidableEq K] in
/-- A point of $E(\bar K)$ fixed by the Galois group of $\bar K$ over $L$ comes from $E(L)$. -/
lemma exists_point_of_fixed [IsGalois K (AlgebraicClosure K)]
    (L : IntermediateField K (AlgebraicClosure K)) (P : (W.toAffine⁄(AlgebraicClosure K)).Point)
    (hP : ∀ σ ∈ L.fixingSubgroup,
      Point.map (W' := W.toAffine) (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) P = P) :
    ∃ Q : (W.toAffine⁄L).Point, Point.map (W' := W.toAffine) L.val Q = P := by
  cases P with
  | zero => exact ⟨0, rfl⟩
  | @some x y hxy =>
    have hx : ∀ σ ∈ L.fixingSubgroup, σ x = x := fun σ hσ => by
      have := hP σ hσ
      simp only [Point.map_some] at this
      exact (Point.some.inj this).1
    have hy : ∀ σ ∈ L.fixingSubgroup, σ y = y := fun σ hσ => by
      have := hP σ hσ
      simp only [Point.map_some] at this
      exact (Point.some.inj this).2
    have hxL : x ∈ L := by
      have : x ∈ IntermediateField.fixedField L.fixingSubgroup :=
        (IntermediateField.mem_fixedField_iff _ _).2 hx
      rwa [InfiniteGalois.fixedField_fixingSubgroup] at this
    have hyL : y ∈ L := by
      have : y ∈ IntermediateField.fixedField L.fixingSubgroup :=
        (IntermediateField.mem_fixedField_iff _ _).2 hy
      rwa [InfiniteGalois.fixedField_fixingSubgroup] at this
    exact ⟨Point.some (⟨x, hxL⟩ : L) ⟨y, hyL⟩
      ((W.toAffine.baseChange_nonsingular (f := L.val) L.val.injective ⟨x, hxL⟩ ⟨y, hyL⟩).1 hxy), rfl⟩

omit [DecidableEq K] in
/-- The points of $E_n(\bar K)$ fixed by $\operatorname{Gal}(\bar K/L)$ form a finite group (for a number field
$L$): they are the $n$-torsion points over $L$, finitely many by the finiteness of torsion over number fields. -/
lemma finite_invariants [NumberField K] [W.IsElliptic] (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] (n : ℤ) (hn : 1 ≤ n) :
    Finite (Representation.invariants
      ((torsionRep W (AlgebraicClosure K) n).ρ.comp L.fixingSubgroup.subtype)) := by
  have : NumberField L := NumberField.of_module_finite K L
  have : (W.toAffine⁄L).IsElliptic :=
    (inferInstance : (WeierstrassCurve.map W (algebraMap K L)).IsElliptic)
  have : Finite (AddCommGroup.torsion (W.toAffine⁄L).Point) :=
    WeierstrassCurve.Affine.finite_torsion
  set A := torsionRep W (AlgebraicClosure K) n with hA
  let ι : Representation.invariants (A.ρ.comp L.fixingSubgroup.subtype) →
      (W.toAffine⁄(AlgebraicClosure K)).Point := fun v => ((v : A) : (W.toAffine⁄(AlgebraicClosure K)).Point)
  have hinj : Function.Injective ι := fun v w h =>
    Subtype.ext (Subtype.ext h)
  let T0 : Set (W.toAffine⁄(AlgebraicClosure K)).Point :=
    Set.range (fun Q : AddCommGroup.torsion (W.toAffine⁄L).Point =>
      Point.map (W' := W.toAffine) L.val Q.1)
  have hT0 : T0.Finite := Set.finite_range _
  have hmem : ∀ v, ι v ∈ T0 := by
    intro v
    obtain ⟨Q, hQ⟩ := exists_point_of_fixed W L (ι v) (fun σ hσ => by
      have := congrArg Subtype.val (Representation.mem_invariants _ _ |>.1 v.2 ⟨σ, hσ⟩)
      exact this)
    refine ⟨⟨Q, ?_⟩, hQ⟩
    have hv : n • ι v = 0 := (v.1 : torsionPoints W (AlgebraicClosure K) n).2
    rw [← hQ, ← map_zsmul] at hv
    have hQ0 : n • Q = 0 := Point.map_injective (W' := W.toAffine) L.val (by rw [map_zsmul]; simpa using hv)
    lift n to ℕ using (by omega)
    rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_nsmul_eq_zero]
    exact ⟨n, by omega, by simpa using hQ0⟩
  have := hT0.to_subtype
  exact Finite.of_injective (fun v => (⟨ι v, hmem v⟩ : T0)) (fun v w h => by
    have h' : (⟨ι v, hmem v⟩ : T0) = ⟨ι w, hmem w⟩ := h
    exact hinj (Subtype.mk.inj h'))

/-- **Lemma 3.8** (pdf p. 122).  For an elliptic curve over a number field $K$, a finite Galois extension $L$ of
$K$ and an integer $n \ge 1$, the kernel of $S^{(n)}(E/K) \to S^{(n)}(E/L)$ is finite.  Stated (as in Milne's proof)
as: only finitely many elements of $S^{(n)}(E/K)$ restrict to zero in $H^1(L, E_n)$.  (Milne states it for
$K = \mathbb{Q}$.) -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.8, pdf p. 122"]
theorem lemma_3_8 [NumberField K] [W.IsElliptic] (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsGalois K L] (n : ℤ) (hn : 1 ≤ n) :
    {x | x ∈ selmerGroup K W n ∧ resToField W L n x = 0}.Finite := by
  have hN : L.fixingSubgroup.Normal := by
    rw [← IntermediateField.restrictNormalHom_ker]; infer_instance
  set A := torsionRep W (AlgebraicClosure K) n with hA
  have hG : Finite ((AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ⧸ L.fixingSubgroup) := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact Finite.of_injective _ (QuotientGroup.kerLift_injective (AlgEquiv.restrictNormalHom L))
  have hB : Finite (A.quotientToInvariants L.fixingSubgroup) := finite_invariants W L n hn
  have hC : Finite (cocycles₁ (A.quotientToInvariants L.fixingSubgroup)) := by
    refine Finite.of_injective (fun f => (f : _ → A.quotientToInvariants L.fixingSubgroup))
      (fun f g h => Subtype.ext h)
  have hH : Finite (H1 (A.quotientToInvariants L.fixingSubgroup)) :=
    Finite.of_surjective _ (h1_eq_crossed_mod_principal _).1
  have hex := (remark_1_7 A L.fixingSubgroup).2
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hH' : Finite (H1InfRes A L.fixingSubgroup).X₁ := hH
  refine (Set.finite_range (fun y : (H1InfRes A L.fixingSubgroup).X₁ =>
    (H1InfRes A L.fixingSubgroup).f y)).subset ?_
  intro x hx
  obtain ⟨y, hy⟩ := hex x hx.2
  exact ⟨y, hy⟩

end Lemma38

/-! ## Review of algebraic number theory (3.9–3.12) -/

section ANT

variable (L : Type) [Field L] [NumberField L]

/-- **Theorem 3.9** (Dedekind, pdf p. 123).  Every nonzero ideal of $\mathcal{O}_L$ is uniquely a product of prime
ideals (Mathlib: `Ideal.uniqueFactorizationMonoid`, the ideals of a Dedekind domain form a unique factorization
monoid). -/
@[kb "milne2006ec" "Ch. IV, Thm. 3.9, pdf p. 123"]
theorem thm_3_9 : UniqueFactorizationMonoid (Ideal (𝓞 L)) := inferInstance

/-- **Theorem 3.10** (finiteness of the class number, pdf p. 123).  The ideal class group of $L$ is finite
(Mathlib: `NumberField.RingOfIntegers.instFintypeClassGroup`).  Milne defines the class group as the cokernel of
$L^\times \to \bigoplus_{\mathfrak p} \mathbb{Z}$; Mathlib's `ClassGroup` is invertible fractional ideals modulo
principal ones, which is the same group (the fractional ideal $\prod \mathfrak p^{a_{\mathfrak p}}$ corresponds to
$(a_{\mathfrak p})$); with $T = \emptyset$, Corollary 3.12 below is also the finiteness of Milne's cokernel. -/
@[kb "milne2006ec" "Ch. IV, Thm. 3.10 and the definition of the class group, pdf p. 123"]
theorem thm_3_10 : Finite (ClassGroup (𝓞 L)) := inferInstance

/-- **Theorem 3.11** (Dirichlet's unit theorem, finite generation, pdf p. 124).  The group of units of
$\mathcal{O}_L$ is finitely generated (Mathlib: the instance `Monoid.FG (𝓞 K)ˣ` in
`Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean`; the rank formula is
`NumberField.Units.finrank_eq`). -/
@[kb "milne2006ec" "Ch. IV, Thm. 3.11, pdf p. 124"]
theorem thm_3_11 : Monoid.FG (𝓞 L)ˣ := inferInstance

variable {L} (T : Finset (HeightOneSpectrum (𝓞 L)))

/-- $\operatorname{ord}_{\mathfrak p}(x)$ for $x \in L^\times$ (pdf p. 123). -/
noncomputable def ordPSelmer (v : HeightOneSpectrum (𝓞 L)) (x : Lˣ) : ℤ :=
  -Multiplicative.toAdd (v.valuationOfNeZero x)

/-- $\operatorname{ord}_{\mathfrak p}$ is multiplicative. -/
lemma ordPSelmer_mul (v : HeightOneSpectrum (𝓞 L)) (x y : Lˣ) : ordPSelmer v (x * y) = ordPSelmer v x + ordPSelmer v y := by
  simp only [ordPSelmer, map_mul, toAdd_mul]; ring

/-- $\operatorname{ord}_{\mathfrak p}(1) = 0$. -/
lemma ordPSelmer_one (v : HeightOneSpectrum (𝓞 L)) : ordPSelmer v 1 = 0 := by
  simp [ordPSelmer]

/-- $\operatorname{ord}_{\mathfrak p}(x^n) = n \operatorname{ord}_{\mathfrak p}(x)$. -/
lemma ordPSelmer_pow (v : HeightOneSpectrum (𝓞 L)) (x : Lˣ) (n : ℕ) : ordPSelmer v (x ^ n) = n * ordPSelmer v x := by
  induction n with
  | zero => simp [ordPSelmer_one]
  | succ k ih => rw [pow_succ, ordPSelmer_mul, ih]; push_cast; ring

/-- $\operatorname{ord}_{\mathfrak p}(x^{-1}) = -\operatorname{ord}_{\mathfrak p}(x)$. -/
lemma ordPSelmer_inv (v : HeightOneSpectrum (𝓞 L)) (x : Lˣ) : ordPSelmer v x⁻¹ = - ordPSelmer v x := by
  have := ordPSelmer_mul v x x⁻¹
  rw [mul_inv_cancel, ordPSelmer_one] at this
  omega

/-- A unit with nonzero order at a prime lies in the support of it or of its inverse. -/
lemma ordPSelmer_ne_zero_mem_support (v : HeightOneSpectrum (𝓞 L)) (x : Lˣ) (h : ordPSelmer v x ≠ 0) :
    v ∈ HeightOneSpectrum.Support (𝓞 L) (x : L) ∪ HeightOneSpectrum.Support (𝓞 L) ((x⁻¹ : Lˣ) : L) := by
  have h : v.valuationOfNeZero x ≠ 1 := by
    intro h1; apply h; simp [ordPSelmer, h1]
  have := v.valuationOfNeZero_eq x
  have h2 : v.valuation L x ≠ 1 := by
    intro h1; apply h; rw [← WithZero.coe_inj, this, h1]; rfl
  rcases lt_trichotomy (v.valuation L x) 1 with h3|h3|h3
  · right
    simp only [HeightOneSpectrum.Support, Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀]
    have : v.valuation L x ≠ 0 := by simp
    exact one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 this, h3⟩
  · exact absurd h3 h2
  · left; exact h3

/-- Only finitely many primes have nonzero order at a given unit. -/
lemma ordPSelmer_finite_support (x : Lˣ) : {v : HeightOneSpectrum (𝓞 L) | ordPSelmer v x ≠ 0}.Finite :=
  ((HeightOneSpectrum.Support.finite (𝓞 L) (x : L)).union
    (HeightOneSpectrum.Support.finite (𝓞 L) ((x⁻¹ : Lˣ) : L))).subset
    (fun v hv => ordPSelmer_ne_zero_mem_support v x hv)

/-- The map $L^\times \to \bigoplus_{\mathfrak p \notin T} \mathbb{Z}$, $a \mapsto (\operatorname{ord}_{\mathfrak p} a)$
(pdf p. 124). -/
@[kb "milne2006ec" "Ch. IV, Cor. 3.12, the map L^× → ⊕_{p ∉ T} Z, pdf p. 124"]
noncomputable def ordAway : Additive Lˣ →+ ({v : HeightOneSpectrum (𝓞 L) // v ∉ T} →₀ ℤ) where
  toFun x := Finsupp.ofSupportFinite (fun v => ordPSelmer v.1 (Additive.toMul x)) (by
    exact (ordPSelmer_finite_support (Additive.toMul x)).preimage Subtype.val_injective.injOn)
  map_zero' := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, ordPSelmer_one]
  map_add' := by
    intro x y
    ext v
    simp [Finsupp.ofSupportFinite_coe, ordPSelmer_mul]

/-- The $T$-units $U_T$ (pdf p. 124): the kernel of `ordAway T`. -/
@[kb "milne2006ec" "Ch. IV, Cor. 3.12, definition of U_T, pdf p. 124"]
noncomputable abbrev unitsAway : AddSubgroup (Additive Lˣ) := (ordAway T).ker

/-- Membership in $U_T$: all orders outside $T$ vanish. -/
lemma mem_unitsAway_iff (u : Additive Lˣ) :
    u ∈ unitsAway T ↔ ∀ v : HeightOneSpectrum (𝓞 L), v ∉ T → ordPSelmer v (Additive.toMul u) = 0 := by
  rw [AddMonoidHom.mem_ker, Finsupp.ext_iff]
  constructor
  · intro h v hv
    simpa [ordAway, Finsupp.ofSupportFinite_coe] using h ⟨v, hv⟩
  · intro h v
    simpa [ordAway, Finsupp.ofSupportFinite_coe] using h v.1 v.2

/-- The group $C_T$ (pdf p. 124): the cokernel of `ordAway T`. -/
@[kb "milne2006ec" "Ch. IV, Cor. 3.12, definition of C_T, pdf p. 124"]
abbrev classGroupAway : Type := ({v : HeightOneSpectrum (𝓞 L) // v ∉ T} →₀ ℤ) ⧸ (ordAway T).range

/-- The valuation of a unit in terms of $\operatorname{ord}_{\mathfrak p}$. -/
lemma valuation_eq_exp_neg_ordP (v : HeightOneSpectrum (𝓞 L)) (x : Lˣ) :
    v.valuation L (x : L) = WithZero.exp (-ordPSelmer v x) := by
  rw [← v.valuationOfNeZero_eq x]
  simp only [ordPSelmer, neg_neg]
  rfl

/-- The exponent of a prime in a nonzero integer, as the count of the principal fractional ideal. -/
lemma intValuation_eq_exp_neg_count (v : HeightOneSpectrum (𝓞 L)) {r : 𝓞 L} (hr : r ≠ 0) :
    v.intValuation r = WithZero.exp (-(FractionalIdeal.count L v
      (FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L r)))) := by
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe L v (by simpa using hr), v.intValuation_if_neg hr]

/-- The count of the principal fractional ideal generated by a unit is its order. -/
lemma count_spanSingleton (v : HeightOneSpectrum (𝓞 L)) (x : Lˣ) :
    FractionalIdeal.count L v (FractionalIdeal.spanSingleton (𝓞 L)⁰ (x : L)) = ordPSelmer v x := by
  obtain ⟨⟨a, d⟩, h⟩ := IsLocalization.surj (𝓞 L)⁰ (x : L)
  have hd : (d : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hinj := IsFractionRing.injective (𝓞 L) L
  have hd' : algebraMap (𝓞 L) L d ≠ 0 := fun h0 => hd (hinj (by simp [h0]))
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, map_zero] at h
    rcases mul_eq_zero.1 h with h | h
    · exact x.ne_zero h
    · exact hd' h
  have ha' : algebraMap (𝓞 L) L a ≠ 0 := fun h0 => ha (hinj (by simpa using h0))
  have h1 : FractionalIdeal.spanSingleton (𝓞 L)⁰ (x : L) *
      FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L d) =
      FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L a) := by
    rw [← map_mul, h]
  have hcount := FractionalIdeal.count_mul L v
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 x.ne_zero)
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 hd')
  rw [h1] at hcount
  have hv : v.valuation L (x : L) * v.valuation L (algebraMap (𝓞 L) L d) =
      v.valuation L (algebraMap (𝓞 L) L a) := by rw [← map_mul, h]
  rw [valuation_eq_exp_neg_ordP, valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_eq_exp_neg_count v hd, intValuation_eq_exp_neg_count v ha, ← WithZero.exp_add,
    WithZero.exp_inj] at hv
  omega

section ClassGroupFinite

/-- A nonzero fractional ideal gives an element of $\bigoplus_{\mathfrak p \notin T} \mathbb{Z}$ (its exponents). -/
noncomputable def idealToCT (I : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : {v : HeightOneSpectrum (𝓞 L) // v ∉ T} →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => FractionalIdeal.count L v.1 (I : FractionalIdeal (𝓞 L)⁰ L)) (by
    have := FractionalIdeal.finite_factors (I : FractionalIdeal (𝓞 L)⁰ L)
    exact (Filter.eventually_cofinite.1 this).preimage Subtype.val_injective.injOn)

lemma idealToCT_mul (I J : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    idealToCT T (I * J) = idealToCT T I + idealToCT T J := by
  ext v
  simp [idealToCT, Finsupp.ofSupportFinite_coe, FractionalIdeal.count_mul L v.1 I.ne_zero J.ne_zero]

lemma idealToCT_one : idealToCT T (1 : (FractionalIdeal (𝓞 L)⁰ L)ˣ) = 0 := by
  ext v
  simp [idealToCT, Finsupp.ofSupportFinite_coe, FractionalIdeal.count_one]

lemma idealToCT_principal (x : Lˣ) :
    idealToCT T (toPrincipalIdeal (𝓞 L) L x) = ordAway T (Additive.ofMul x) := by
  ext v
  simp [idealToCT, ordAway, Finsupp.ofSupportFinite_coe, count_spanSingleton]

lemma idealToCT_surjective (a : {v : HeightOneSpectrum (𝓞 L) // v ∉ T} →₀ ℤ) :
    ∃ I, idealToCT T I = a := by
  let exps : HeightOneSpectrum (𝓞 L) →₀ ℤ :=
    Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ a
  have hJ : exps.prod (fun v n => (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ n) ≠ 0 := by
    unfold Finsupp.prod
    exact Finset.prod_ne_zero_iff.2 fun v _ =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  refine ⟨Units.mk0 _ hJ, ?_⟩
  ext v
  simp only [idealToCT, Finsupp.ofSupportFinite_coe, Units.val_mk0]
  rw [FractionalIdeal.count_finsuppProd]
  exact Finsupp.embDomain_apply_self (⟨Subtype.val, Subtype.val_injective⟩ :
    {v : HeightOneSpectrum (𝓞 L) // v ∉ T} ↪ HeightOneSpectrum (𝓞 L)) a v

/-- $C_T$ is finite: it is a quotient of the class group. -/
lemma finite_classGroupAway : Finite (classGroupAway T) := by
  let Φ : (FractionalIdeal (𝓞 L)⁰ L)ˣ →* Multiplicative (classGroupAway T) :=
    { toFun := fun I => Multiplicative.ofAdd (QuotientAddGroup.mk (idealToCT T I))
      map_one' := by simp [idealToCT_one]
      map_mul' := fun I J => by
        simp only [idealToCT_mul, QuotientAddGroup.mk_add]; rfl }
  have hker : (toPrincipalIdeal (𝓞 L) L).range ≤ Φ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (QuotientAddGroup.mk (idealToCT T _)) = 1
    rw [idealToCT_principal]
    show Multiplicative.ofAdd (QuotientAddGroup.mk (ordAway T (Additive.ofMul x))) =
      Multiplicative.ofAdd 0
    congr 1
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨_, rfl⟩
  have hfin : Finite ((FractionalIdeal (𝓞 L)⁰ L)ˣ ⧸ (toPrincipalIdeal (𝓞 L) L).range) :=
    Finite.of_equiv _ (ClassGroup.equiv (R := 𝓞 L) L).toEquiv
  have hsurj : Function.Surjective (QuotientGroup.lift _ Φ hker) := by
    intro y
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd y)
    obtain ⟨I, hI⟩ := idealToCT_surjective T a
    refine ⟨QuotientGroup.mk I, ?_⟩
    show Multiplicative.ofAdd (QuotientAddGroup.mk (idealToCT T I)) = y
    rw [hI, ha]
    rfl
  have : Finite (Multiplicative (classGroupAway T)) := Finite.of_surjective _ hsurj
  exact Finite.of_equiv _ Multiplicative.toAdd

end ClassGroupFinite

/-- $U_T$ is finitely generated: it is an extension of a subgroup of $\mathbb{Z}^T$ by the unit group of
$\mathcal{O}_L$. -/
lemma fg_unitsAway : AddGroup.FG (unitsAway T) := by
  rw [← Module.Finite.iff_addGroup_fg]
  let φ : unitsAway T →+ (T → ℤ) :=
    { toFun := fun u t => ordPSelmer t.1 (Additive.toMul u.1)
      map_zero' := by ext t; simp [ordPSelmer_one]
      map_add' := fun u w => by ext t; simp [ordPSelmer_mul] }
  let f0 : Additive (𝓞 L)ˣ →+ Additive Lˣ :=
    (Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L)).toAdditive
  have hf0 : ∀ u, f0 u ∈ unitsAway T := fun u => by
    rw [mem_unitsAway_iff]
    intro v _
    show ordPSelmer v (Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) (Additive.toMul u)) = 0
    simp [ordPSelmer]
  let f : Additive (𝓞 L)ˣ →+ unitsAway T := f0.codRestrict (unitsAway T) hf0
  have hex : Function.Exact f.toIntLinearMap φ.toIntLinearMap.rangeRestrict := by
    intro s
    constructor
    · intro hs
      have h0 : φ s = 0 := by
        have := congrArg Subtype.val hs
        exact this
      have hall : ∀ v, ordPSelmer v (Additive.toMul s.1) = 0 := by
        intro v
        by_cases hv : v ∈ T
        · exact congrFun h0 ⟨v, hv⟩
        · exact (mem_unitsAway_iff T _).1 s.2 v hv
      set y : Lˣ := Additive.toMul s.1 with hy
      have hle : ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L (y : L) ≤ 1 := fun v => by
        rw [valuation_eq_exp_neg_ordP, hall, neg_zero, WithZero.exp_zero]
      have hle' : ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L ((y⁻¹ : Lˣ) : L) ≤ 1 := fun v => by
        rw [valuation_eq_exp_neg_ordP, ordPSelmer_inv, hall, neg_zero, neg_zero, WithZero.exp_zero]
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L (y : L) hle
      obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L ((y⁻¹ : Lˣ) : L) hle'
      have hab : a * b = 1 := by
        apply IsFractionRing.injective (𝓞 L) L
        simp [ha, hb]
      let u : (𝓞 L)ˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
      refine ⟨Additive.ofMul u, Subtype.ext ?_⟩
      show Additive.ofMul (Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) u) = s.1
      have : Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) u = y := Units.ext (by simpa using ha)
      rw [this]
      rfl
    · rintro ⟨u, rfl⟩
      apply Subtype.ext
      ext t
      show ordPSelmer t.1 (Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) (Additive.toMul u)) = 0
      simp [ordPSelmer]
  have hsurj : Function.Surjective φ.toIntLinearMap.rangeRestrict :=
    LinearMap.surjective_rangeRestrict _
  exact Module.Finite.of_exact hex hsurj

/-- **Corollary 3.12** (pdf p. 124).  For a finite set $T$ of prime ideals of $\mathcal{O}_L$, the group $U_T$ is
finitely generated and the group $C_T$ is finite. -/
@[kb "milne2006ec" "Ch. IV, Cor. 3.12, pdf p. 124"]
theorem cor_3_12 : AddGroup.FG (unitsAway T) ∧ Finite (classGroupAway T) :=
  ⟨fg_unitsAway T, finite_classGroupAway T⟩

/-- **Lemma 3.13** (pdf p. 125).  Let $N \subseteq L^\times/L^{\times n}$ be the kernel of
$a \mapsto (\operatorname{ord}_{\mathfrak p}(a) \bmod n)_{\mathfrak p \notin T}$.  There is an exact sequence
$0 \to U_T/U_T^n \to N \to (C_T)_n$, the second map sending the class of $\alpha$ to the class of
$(\operatorname{ord}_{\mathfrak p}(\alpha)/n)_{\mathfrak p \notin T}$.  Stated elementwise:
(a) (injectivity) an element of $U_T$ that is an $n$-th power in $L^\times$ is an $n$-th power in $U_T$;
(b) (exactness at $N$) for $\alpha$ with $n \mid \operatorname{ord}_{\mathfrak p}(\alpha)$ for all $\mathfrak p \notin T$,
$\alpha \in U_T \cdot L^{\times n}$ if and only if $(\operatorname{ord}_{\mathfrak p}(\alpha)/n)$ lies in the image of
$L^\times$, i.e. maps to zero in $C_T$;
(c) $N$ is Mathlib's Selmer group $L(T, n)$: the classes of such $\alpha$. -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.13, pdf p. 125"]
theorem lemma_3_13 (n : ℕ) (hn : 0 < n) :
    (∀ u ∈ unitsAway T, ∀ y : Lˣ, Additive.ofMul (y ^ n) = u →
      ∃ z ∈ unitsAway T, n • z = u) ∧
    (∀ α : Lˣ, (∀ v : HeightOneSpectrum (𝓞 L), v ∉ T → (n : ℤ) ∣ ordPSelmer v α) →
      ((∃ u ∈ unitsAway T, ∃ y : Lˣ, α = Additive.toMul u * y ^ n) ↔
        ∃ β : Lˣ, ∀ v : HeightOneSpectrum (𝓞 L), v ∉ T → ordPSelmer v α = n * ordPSelmer v β)) ∧
    (∀ α : Lˣ, (QuotientGroup.mk α : Lˣ ⧸ (powMonoidHom (α := Lˣ) n).range) ∈
        IsDedekindDomain.selmerGroup (R := 𝓞 L) (K := L) (S := (T : Set (HeightOneSpectrum (𝓞 L)))) (n := n) ↔
      ∀ v : HeightOneSpectrum (𝓞 L), v ∉ T → (n : ℤ) ∣ ordPSelmer v α) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu y hy
    have hu' := (mem_unitsAway_iff T u).1 hu
    have hyu : Additive.toMul u = y ^ n := by rw [← hy]; rfl
    refine ⟨Additive.ofMul y, (mem_unitsAway_iff T _).2 ?_, ?_⟩
    · intro v hv
      have h := hu' v hv
      rw [hyu, ordPSelmer_pow] at h
      have : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
      exact (mul_eq_zero.1 h).resolve_left this
    · rw [← hy]; rfl
  · intro α _
    constructor
    · rintro ⟨u, hu, y, rfl⟩
      refine ⟨y, fun v hv => ?_⟩
      rw [ordPSelmer_mul, ordPSelmer_pow, (mem_unitsAway_iff T u).1 hu v hv, zero_add]
    · rintro ⟨β, hβ⟩
      refine ⟨Additive.ofMul (α * (β ^ n)⁻¹), (mem_unitsAway_iff T _).2 ?_, β, ?_⟩
      · intro v hv
        simp only [toMul_ofMul, ordPSelmer_mul, ordPSelmer_inv, ordPSelmer_pow, hβ v hv]
        ring
      · simp
  · intro α
    have key : ∀ v : HeightOneSpectrum (𝓞 L),
        v.valuationOfNeZeroMod n (QuotientGroup.mk α) = 1 ↔ (n : ℤ) ∣ ordPSelmer v α := by
      intro v
      have : v.valuationOfNeZeroMod n (QuotientGroup.mk α) =
          Multiplicative.ofAdd (((Multiplicative.toAdd (v.valuationOfNeZero α) : ℤ)) : ZMod n) := rfl
      rw [this, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [ordPSelmer]
      exact dvd_neg.symm
    show (∀ v, v ∉ (T : Set (HeightOneSpectrum (𝓞 L))) → _) ↔ _
    simp only [Finset.mem_coe, key]

end ANT

end NumberFieldKB.MilneEC
