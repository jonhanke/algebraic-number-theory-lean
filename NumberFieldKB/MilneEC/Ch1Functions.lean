import NumberFieldKB.MilneEC.Ch1Projective
import Mathlib.Computability.Reduce
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int

/-!
# Milne, Elliptic Curves, Chapter I, Section 4: regular functions; the Riemann–Roch theorem

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §4 (pdf pp. 37–46): coordinate rings and rational
functions of affine and projective plane curves, Remark 4.2, divisors, the spaces $L(D)$, Riemann's
theorem (Theorems 4.5 and 4.13, named statements), the genus, Picard groups, Proposition 4.10 (a named
statement), Asides 4.8 and 4.9 (named statements).

**Divisors.** Milne gives two definitions of divisors: over an algebraically closed field, formal sums of
points with the divisor of a function defined by intersection numbers (p. 40); over a perfect field,
formal sums of *prime divisors*, the discrete valuation rings of the function field containing `k`
(p. 44–45).  We formalize the second, which is intrinsic to the function field and applies to both
cases; over an algebraically closed field the prime divisors of a nonsingular curve correspond to its
points (the named statement `PointPrimeDivisor`).  Everything is stated for a field extension `K/k`
(the function field) and then specialized to the function field of a projective plane curve.

**Valuations.** For a prime divisor `p` with chosen uniformizer $t_p$, `p.ord h` is the integer `n` with
$h = u\,t_p^n$, `u` a unit (p. 44); and $\varphi \in L(D)$ is expressed as $\varphi\, t_p^{D(p)} \in \mathcal O_p$
for all `p`, which is $\operatorname{ord}_p(\varphi) + D(p) \geq 0$ for $\varphi \neq 0$ (and holds for
$\varphi = 0$).
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace NumberFieldKB.MilneEC

variable {k : Type*} [Field k]

/-! ### Regular and rational functions on affine and projective plane curves -/

/-- The ring of regular functions $k[C] = k[X, Y]/(f)$ of the affine plane curve $C_f$ (p. 37). -/
@[kb "milne2006ec" "Ch. I, §4, Def. of k[C] = k[X,Y]/(f), pdf p. 37"]
abbrev coordinateRing (f : MvPolynomial (Fin 2) k) := MvPolynomial (Fin 2) k ⧸ Ideal.span {f}

instance coordinateRing_isDomain (f : MvPolynomial (Fin 2) k) [hf : Fact (Prime f)] :
    IsDomain (coordinateRing f) :=
  haveI : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime hf.out.ne_zero).mpr hf.out
  Ideal.Quotient.isDomain _

/-- The field of rational functions $k(C)$, the field of fractions of $k[C]$ (p. 38). -/
@[kb "milne2006ec" "Ch. I, §4, Def. of k(C), pdf p. 38"]
abbrev functionField (f : MvPolynomial (Fin 2) k) := FractionRing (coordinateRing f)

/-- Regular functions (p. 37): over an algebraically closed field, a polynomial vanishes on $C_f(k)$ if and
only if it is a multiple of the irreducible `f` (Hilbert's Nullstellensatz); so $k[X, Y]/(f)$ is the ring
of regular functions on `C`. -/
@[kb "milne2006ec" "Ch. I, §4, k[X,Y]/(f) is the ring of regular functions, pdf p. 37"]
theorem vanishes_on_curve_iff [IsAlgClosed k] {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (g : MvPolynomial (Fin 2) k) :
    (∀ P ∈ affinePoints f k, evalAt g P = 0) ↔ f ∣ g := by
  have hpt : ∀ x : Fin 2 → k, (![x 0, x 1] : Fin 2 → k) = x := by
    intro x
    funext i
    fin_cases i <;> rfl
  constructor
  · intro H
    have hprime : (Ideal.span {f}).IsPrime :=
      (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
    have hg : g ∈ vanishingIdeal k (zeroLocus k (Ideal.span {f} : Ideal (MvPolynomial (Fin 2) k))) := by
      intro x hx
      have hfx : aeval x f = 0 := hx f (Ideal.subset_span rfl)
      have hmem : ((x 0, x 1) : k × k) ∈ affinePoints f k := by
        show evalAt f (x 0, x 1) = 0
        simp only [evalAt]
        rw [hpt x]
        exact hfx
      have := H _ hmem
      simp only [evalAt] at this
      rw [hpt x] at this
      exact this
    rw [vanishingIdeal_zeroLocus_eq_radical, hprime.radical] at hg
    exact Ideal.mem_span_singleton.mp hg
  · rintro ⟨q, rfl⟩ P hP
    have h0 : evalAt f P = 0 := hP
    simp only [evalAt] at h0 ⊢
    rw [map_mul, h0, zero_mul]

/-- The homogeneous coordinate ring $k[x, y, z] = k[X, Y, Z]/(F)$ of a projective plane curve (p. 38). -/
abbrev homogCoordRing (F : MvPolynomial (Fin 3) k) := MvPolynomial (Fin 3) k ⧸ Ideal.span {F}

instance homogCoordRing_isDomain (F : MvPolynomial (Fin 3) k) [hF : Fact (Prime F)] :
    IsDomain (homogCoordRing F) :=
  haveI : (Ideal.span {F}).IsPrime := (Ideal.span_singleton_prime hF.out.ne_zero).mpr hF.out
  Ideal.Quotient.isDomain _

/-- The class in $k(x, y, z)$ of a polynomial. -/
abbrev homogFrac (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (g : MvPolynomial (Fin 3) k) :
    FractionRing (homogCoordRing F) :=
  algebraMap (homogCoordRing F) _ (Ideal.Quotient.mk (Ideal.span {F}) g)

/-- The quotients $g/h$ of classes of homogeneous polynomials of the same degree, $h \neq 0$ in
$k[x, y, z]$ (p. 38). -/
def homogFractions (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] :
    Set (FractionRing (homogCoordRing F)) :=
  {φ | ∃ (d : ℕ) (g h : MvPolynomial (Fin 3) k), g.IsHomogeneous d ∧ h.IsHomogeneous d ∧
    ¬ F ∣ h ∧ φ = homogFrac F g / homogFrac F h}

/-- The field of rational functions $k(C) = k(x, y, z)_0$ of a projective plane curve $C_F$, `F`
irreducible (p. 38), as the subfield generated by `homogFractions F` (which equals that set,
`projFunctionField_eq`). -/
@[kb "milne2006ec" "Ch. I, §4, Def. of k(C) for a projective curve, pdf p. 38"]
def projFunctionField (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] :
    Subfield (FractionRing (homogCoordRing F)) :=
  Subfield.closure (homogFractions F)

/-- A polynomial not divisible by `F` has nonzero class in $k(x, y, z)$. -/
theorem homogFrac_ne_zero (F : MvPolynomial (Fin 3) k) [Fact (Prime F)]
    {h : MvPolynomial (Fin 3) k} (hh : ¬ F ∣ h) : homogFrac F h ≠ 0 := by
  intro h0
  have h1 := IsFractionRing.injective (homogCoordRing F) (FractionRing (homogCoordRing F))
    (h0.trans (map_zero (algebraMap (homogCoordRing F) (FractionRing (homogCoordRing F)))).symm)
  exact hh (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h1))

theorem homogFrac_add (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (a b : MvPolynomial (Fin 3) k) :
    homogFrac F (a + b) = homogFrac F a + homogFrac F b := by
  unfold homogFrac
  rw [(Ideal.Quotient.mk _).map_add, RingHom.map_add]

theorem homogFrac_mul (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (a b : MvPolynomial (Fin 3) k) :
    homogFrac F (a * b) = homogFrac F a * homogFrac F b := by
  unfold homogFrac
  rw [(Ideal.Quotient.mk _).map_mul, RingHom.map_mul]

theorem homogFrac_neg (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (a : MvPolynomial (Fin 3) k) :
    homogFrac F (-a) = - homogFrac F a := by
  unfold homogFrac
  rw [(Ideal.Quotient.mk (Ideal.span {F})).map_neg a, RingHom.map_neg]

/-- The quotients of homogeneous elements of equal degree form a subfield. -/
def homogFractionsSubfield (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] :
    Subfield (FractionRing (homogCoordRing F)) where
  carrier := homogFractions F
  zero_mem' := ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _,
    fun h => (Fact.out : Prime F).not_dvd_one h, by simp [homogFrac]⟩
  one_mem' := ⟨0, 1, 1, isHomogeneous_one _ _, isHomogeneous_one _ _,
    fun h => (Fact.out : Prime F).not_dvd_one h, by
      rw [div_self (homogFrac_ne_zero F fun h => (Fact.out : Prime F).not_dvd_one h)]⟩
  add_mem' := by
    rintro _ _ ⟨d, g, h, hg, hh, hFh, rfl⟩ ⟨d', g', h', hg', hh', hFh', rfl⟩
    have h1 := homogFrac_ne_zero F hFh
    have h2 := homogFrac_ne_zero F hFh'
    refine ⟨d + d', g * h' + g' * h, h * h', ?_, hh.mul hh', ?_, ?_⟩
    · have h4 := hg'.mul hh
      rw [add_comm d' d] at h4
      exact (hg.mul hh').add h4
    · intro hd
      rcases (Fact.out : Prime F).dvd_or_dvd hd with h3 | h3
      · exact hFh h3
      · exact hFh' h3
    · simp only [homogFrac_add, homogFrac_mul]
      field_simp
  neg_mem' := by
    rintro _ ⟨d, g, h, hg, hh, hFh, rfl⟩
    refine ⟨d, -g, h, hg.neg, hh, hFh, ?_⟩
    rw [homogFrac_neg, neg_div]
  mul_mem' := by
    rintro _ _ ⟨d, g, h, hg, hh, hFh, rfl⟩ ⟨d', g', h', hg', hh', hFh', rfl⟩
    refine ⟨d + d', g * g', h * h', hg.mul hg', hh.mul hh', ?_, ?_⟩
    · intro hd
      rcases (Fact.out : Prime F).dvd_or_dvd hd with h3 | h3
      · exact hFh h3
      · exact hFh' h3
    · rw [homogFrac_mul, homogFrac_mul, div_mul_div_comm]
  inv_mem' := by
    rintro _ ⟨d, g, h, hg, hh, hFh, rfl⟩
    by_cases hFg : F ∣ g
    · refine ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _,
        fun h => (Fact.out : Prime F).not_dvd_one h, ?_⟩
      have : homogFrac F g = 0 := by
        unfold homogFrac
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hFg)]
        simp
      simp [this, homogFrac]
    · exact ⟨d, h, g, hh, hg, hFg, by rw [inv_div]⟩

/-- $k(x, y, z)_0$ is already a field: the quotients of homogeneous elements of equal degree form a
subfield (p. 39). -/
theorem projFunctionField_eq (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] :
    (projFunctionField F : Set (FractionRing (homogCoordRing F))) = homogFractions F := by
  have := Subfield.closure_eq (homogFractionsSubfield F)
  exact congrArg SetLike.coe this

theorem algebraMap_mem_projFunctionField (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (c : k) :
    algebraMap k (FractionRing (homogCoordRing F)) c ∈ projFunctionField F := by
  apply Subfield.subset_closure
  refine ⟨0, C c, 1, isHomogeneous_C _ _, isHomogeneous_one _ _,
    fun h => (Fact.out : Prime F).not_dvd_one h, ?_⟩
  have h1 : homogFrac F 1 = 1 := by simp only [homogFrac, map_one]
  rw [h1, div_one, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 3) k) _ c]
  rfl

noncomputable instance (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] :
    Algebra k (projFunctionField F) :=
  ((algebraMap k (FractionRing (homogCoordRing F))).codRestrict
    (projFunctionField F).toSubring (algebraMap_mem_projFunctionField F)).toAlgebra

theorem homogFrac_pow (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (a : MvPolynomial (Fin 3) k)
    (n : ℕ) : homogFrac F (a ^ n) = homogFrac F a ^ n := by
  unfold homogFrac
  rw [(Ideal.Quotient.mk (Ideal.span {F})).map_pow a n, RingHom.map_pow]

theorem homogFrac_eq_zero_iff (F : MvPolynomial (Fin 3) k) [Fact (Prime F)]
    {h : MvPolynomial (Fin 3) k} : homogFrac F h = 0 ↔ F ∣ h := by
  constructor
  · intro h0
    by_contra hn
    exact homogFrac_ne_zero F hn h0
  · rintro ⟨q, rfl⟩
    unfold homogFrac
    rw [(Ideal.Quotient.mk (Ideal.span {F})).map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F), zero_mul,
      RingHom.map_zero]

/-- The ring homomorphism `homogFrac`, as an algebra homomorphism over `k`. -/
noncomputable def homogFracAlg (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] :
    MvPolynomial (Fin 3) k →ₐ[k] FractionRing (homogCoordRing F) :=
  IsScalarTower.toAlgHom k (MvPolynomial (Fin 3) k) _

theorem homogFracAlg_apply (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (G : MvPolynomial (Fin 3) k) :
    homogFracAlg F G = homogFrac F G := by
  show algebraMap (MvPolynomial (Fin 3) k) _ G = _
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 3) k) (homogCoordRing F)
    (FractionRing (homogCoordRing F))]
  rfl

theorem aeval_homogFrac (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (G : MvPolynomial (Fin 3) k) :
    aeval (fun i => homogFrac F (X i)) G = homogFrac F G := by
  have h1 : (homogFracAlg F ∘ X) = fun i => homogFrac F (X i) :=
    funext fun i => homogFracAlg_apply F _
  have := congrArg (fun φ : MvPolynomial (Fin 3) k →ₐ[k] FractionRing (homogCoordRing F) => φ G)
    (aeval_unique (homogFracAlg F))
  rw [h1, homogFracAlg_apply] at this
  exact this.symm

/-- Every polynomial in two variables is the dehomogenization of a homogeneous polynomial in three
variables (homogenization). -/
theorem exists_homogeneous_dehomogenize (P : MvPolynomial (Fin 2) k) :
    ∃ (e : ℕ) (Q : MvPolynomial (Fin 3) k), Q.IsHomogeneous e ∧ dehomogenize 2 Q = P := by
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    refine ⟨m 0 + m 1, C c * X 0 ^ m 0 * X 1 ^ m 1, ?_, ?_⟩
    · have := ((isHomogeneous_C (Fin 3) c).mul ((isHomogeneous_X k (0 : Fin 3)).pow (m 0))).mul
        ((isHomogeneous_X k (1 : Fin 3)).pow (m 1))
      simpa using this
    · rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
      simp [dehomogenize, pieceSubst, mul_assoc]
  | add P Q hP hQ =>
    obtain ⟨e1, Q1, h1, d1⟩ := hP
    obtain ⟨e2, Q2, h2, d2⟩ := hQ
    have hx : dehomogenize 2 (X 2 : MvPolynomial (Fin 3) k) = 1 := by
      simp [dehomogenize, pieceSubst]
    have hadd : ∀ (A B : MvPolynomial (Fin 3) k),
        dehomogenize 2 (A + B) = dehomogenize 2 A + dehomogenize 2 B := fun A B => map_add _ A B
    have hmul : ∀ (A B : MvPolynomial (Fin 3) k),
        dehomogenize 2 (A * B) = dehomogenize 2 A * dehomogenize 2 B := fun A B => map_mul _ A B
    have hpow : ∀ (A : MvPolynomial (Fin 3) k) (n : ℕ),
        dehomogenize 2 (A ^ n) = dehomogenize 2 A ^ n := fun A n => map_pow _ A n
    rcases le_total e1 e2 with h | h
    · refine ⟨e2, X 2 ^ (e2 - e1) * Q1 + Q2, ?_, ?_⟩
      · have hz := ((isHomogeneous_X k (2 : Fin 3)).pow (e2 - e1)).mul h1
        have h3 : 1 * (e2 - e1) + e1 = e2 := by omega
        rw [h3] at hz
        exact hz.add h2
      · rw [hadd, hmul, hpow, hx, one_pow, one_mul, d1, d2]
    · refine ⟨e1, Q1 + X 2 ^ (e1 - e2) * Q2, ?_, ?_⟩
      · have hz := ((isHomogeneous_X k (2 : Fin 3)).pow (e1 - e2)).mul h2
        have h3 : 1 * (e1 - e2) + e2 = e1 := by omega
        rw [h3] at hz
        exact h1.add hz
      · rw [hadd, hmul, hpow, hx, one_pow, one_mul, d1, d2]

/-- The substitution $X \mapsto x/z$, $Y \mapsto y/z$ into $k(x, y, z)$. -/
noncomputable def phiAff (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] :
    MvPolynomial (Fin 2) k →ₐ[k] FractionRing (homogCoordRing F) :=
  aeval ![homogFrac F (X 0) / homogFrac F (X 2), homogFrac F (X 1) / homogFrac F (X 2)]

theorem phiAff_dehomogenize (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (hZ : ¬ F ∣ X 2) {d : ℕ}
    {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous d) :
    phiAff F (dehomogenize 2 G) = homogFrac F G / homogFrac F (X 2) ^ d := by
  have hz : homogFrac F (X 2) ≠ 0 := homogFrac_ne_zero F hZ
  unfold dehomogenize phiAff
  rw [comp_aeval_apply]
  have hv : (fun j => (aeval ![homogFrac F (X 0) / homogFrac F (X 2),
      homogFrac F (X 1) / homogFrac F (X 2)] : MvPolynomial (Fin 2) k →ₐ[k] _) (pieceSubst 2 j)) =
      (homogFrac F (X 2))⁻¹ • (fun i => homogFrac F (X i)) := by
    funext j
    fin_cases j <;> simp [pieceSubst, div_eq_inv_mul, hz]
  rw [hv, aeval_smul_of_isHomogeneous hG, aeval_homogFrac, inv_pow, inv_mul_eq_div]

/-- **Remark 4.2** (p. 39): if the irreducible projective curve $C_F$ is not the line at infinity
$Z = 0$, the map $g(x', y')/h(x', y') \mapsto g^*(x, y, z)\, z^{\deg h}/(z^{\deg g} h^*(x, y, z))$ is an
isomorphism from the field of rational functions of the affine curve $C \cap U_2$ (`dehomogenize 2 F`)
onto $k(C)$; here $g^*$ is `g` made homogeneous with the fewest possible factors $Z$
(`Polynomial`-free form: we state it for the polynomial classes). -/
@[kb "milne2006ec" "Ch. I, Rem. 4.2, pdf p. 39"]
theorem remark_4_2 (F : MvPolynomial (Fin 3) k) [Fact (Prime F)]
    (hFh : F.IsHomogeneous F.totalDegree) (hZ : ¬ F ∣ X 2) [Fact (Prime (dehomogenize 2 F))] :
    ∃ e : functionField (dehomogenize 2 F) ≃ₐ[k] projFunctionField F,
      ∀ (g : MvPolynomial (Fin 3) k) (d : ℕ), g.IsHomogeneous d →
        ((e (algebraMap (coordinateRing (dehomogenize 2 F)) _
            (Ideal.Quotient.mk (Ideal.span {dehomogenize 2 F}) (dehomogenize 2 g))) :
              projFunctionField F) : FractionRing (homogCoordRing F)) =
          homogFrac F g / homogFrac F (X 2 ^ d) := by
  have hz : homogFrac F (X 2) ≠ 0 := homogFrac_ne_zero F hZ
  have hker : ∀ a ∈ Ideal.span {dehomogenize 2 F}, phiAff F a = 0 := by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, phiAff_dehomogenize F hZ hFh, (homogFrac_eq_zero_iff F).mpr dvd_rfl, zero_div,
      zero_mul]
  let Φ : coordinateRing (dehomogenize 2 F) →ₐ[k] FractionRing (homogCoordRing F) :=
    Ideal.Quotient.liftₐ (Ideal.span {dehomogenize 2 F}) (phiAff F) hker
  have hΦ : ∀ P, Φ (Ideal.Quotient.mk _ P) = phiAff F P := fun P => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hΦ] at ha
    obtain ⟨e, Q, hQ, rfl⟩ := exists_homogeneous_dehomogenize P
    rw [phiAff_dehomogenize F hZ hQ, div_eq_zero_iff] at ha
    rcases ha with h0 | h0
    · obtain ⟨q, rfl⟩ := (homogFrac_eq_zero_iff F).mp h0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [Ideal.mem_span_singleton]
      exact ⟨dehomogenize 2 q, map_mul (aeval (pieceSubst 2)) F q⟩
    · exact absurd h0 (pow_ne_zero _ hz)
  let ψ : functionField (dehomogenize 2 F) →ₐ[k] FractionRing (homogCoordRing F) :=
    IsFractionRing.liftAlgHom hinj
  have hψ : ∀ a, ψ (algebraMap _ _ a) = Φ a := fun a => IsFractionRing.lift_algebraMap hinj a
  have hmemT : ∀ a, Φ a ∈ projFunctionField F := by
    intro a
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨e, Q, hQ, rfl⟩ := exists_homogeneous_dehomogenize P
    rw [hΦ, phiAff_dehomogenize F hZ hQ, ← homogFrac_pow]
    refine Subfield.subset_closure ⟨e, Q, X 2 ^ e, hQ, ?_, ?_, rfl⟩
    · simpa using (isHomogeneous_X k (2 : Fin 3)).pow e
    · exact fun h => hZ ((Fact.out : Prime F).dvd_of_dvd_pow h)
  have hψT : ∀ u, ψ u ∈ projFunctionField F := by
    intro u
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := coordinateRing (dehomogenize 2 F)) u
    rw [map_div₀, hψ, hψ]
    exact div_mem (hmemT a) (hmemT b)
  let ψT : functionField (dehomogenize 2 F) →ₐ[k] projFunctionField F :=
    { toRingHom := ψ.toRingHom.codRestrict (projFunctionField F).toSubring hψT
      commutes' := fun c => Subtype.ext (ψ.commutes c) }
  have hψT_apply : ∀ u, ((ψT u : projFunctionField F) : FractionRing (homogCoordRing F)) = ψ u :=
    fun u => rfl
  have hbij : Function.Bijective ψT := by
    constructor
    · intro a b hab
      apply ψ.toRingHom.injective
      have := congrArg (fun t : projFunctionField F => (t : FractionRing (homogCoordRing F))) hab
      exact this
    · rintro ⟨t, ht⟩
      have ht' : t ∈ homogFractions F := by
        have : t ∈ (projFunctionField F : Set (FractionRing (homogCoordRing F))) := ht
        rwa [projFunctionField_eq] at this
      obtain ⟨d, g, h, hg, hh, hFh', rfl⟩ := ht'
      have hh0 : homogFrac F h ≠ 0 := homogFrac_ne_zero F hFh'
      refine ⟨algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {dehomogenize 2 F}) (dehomogenize 2 g)) /
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {dehomogenize 2 F}) (dehomogenize 2 h)), ?_⟩
      apply Subtype.ext
      rw [hψT_apply, map_div₀, hψ, hψ, hΦ, hΦ, phiAff_dehomogenize F hZ hg,
        phiAff_dehomogenize F hZ hh]
      have hzd : homogFrac F (X 2) ^ d ≠ 0 := pow_ne_zero _ hz
      field_simp
  refine ⟨AlgEquiv.ofBijective ψT hbij, fun g d hg => ?_⟩
  show ψ _ = _
  rw [hψ, hΦ, phiAff_dehomogenize F hZ hg, homogFrac_pow]

/-! ### Prime divisors and divisors of a function field -/

variable (k) in
/-- A **prime divisor** of a field `K` containing `k` (p. 44–45): a discrete valuation ring
$\mathcal O_p \subseteq K$ with field of fractions `K`, containing `k`. -/
@[kb "milne2006ec" "Ch. I, §4, Def. of prime divisor, pdf p. 45"]
structure PrimeDivisor (K : Type*) [Field K] [Algebra k K] where
  /-- The discrete valuation ring $\mathcal O_p$. -/
  O : ValuationSubring K
  algebraMap_mem : ∀ c : k, algebraMap k K c ∈ O
  isDVR : IsDiscreteValuationRing O

namespace PrimeDivisor

variable {K : Type*} [Field K] [Algebra k K] (p : PrimeDivisor k K)

/-- A chosen uniformizer $t_p$ (an irreducible element of $\mathcal O_p$), as an element of `K`. -/
noncomputable def unif : K :=
  ((haveI := p.isDVR; IsDiscreteValuationRing.exists_irreducible p.O).choose : p.O)

/-- The inclusion of `k` into $\mathcal O_p$. -/
noncomputable def ofBase : k →+* p.O :=
  (algebraMap k K).codRestrict p.O.toSubring p.algebraMap_mem

/-- The **degree** of a prime divisor (p. 45): the dimension over `k` of the residue field of
$\mathcal O_p$. -/
@[kb "milne2006ec" "Ch. I, §4, Def. of the degree of a prime divisor, pdf p. 45"]
noncomputable def deg : ℕ :=
  letI : IsLocalRing p.O := inferInstance
  letI : Module k (IsLocalRing.ResidueField p.O) :=
    ((IsLocalRing.residue p.O).comp p.ofBase).toModule
  Module.finrank k (IsLocalRing.ResidueField p.O)

open Classical in
/-- The valuation $\operatorname{ord}_p(h)$ (p. 44): the integer `n` with $h = u\,t_p^n$, `u` a unit of
$\mathcal O_p$ (0 for $h = 0$). -/
@[kb "milne2006ec" "Ch. I, §4, Def. of ord_p, pdf p. 44"]
noncomputable def ord (h : K) : ℤ :=
  if H : ∃ n : ℤ, ∃ u : p.Oˣ, h = (u : K) * p.unif ^ n then H.choose else 0

end PrimeDivisor

variable (k) in
/-- The group of divisors (p. 45): the free abelian group on the prime divisors. -/
@[kb "milne2006ec" "Ch. I, §4, Def. of the group of divisors Div(C), pdf p. 45"]
abbrev Divisor (K : Type*) [Field K] [Algebra k K] := PrimeDivisor k K →₀ ℤ

variable {K : Type*} [Field K] [Algebra k K]

/-- The degree of a divisor, $\deg \sum n_p p = \sum n_p \deg p$ (p. 45). -/
@[kb "milne2006ec" "Ch. I, §4, Def. of the degree of a divisor, pdf p. 45"]
noncomputable def Divisor.deg : Divisor k K →+ ℤ :=
  Finsupp.liftAddHom fun p => (zmultiplesHom ℤ (p.deg : ℤ))

/-- `D` is the divisor of the nonzero function `h` (p. 45): $D = \sum_p \operatorname{ord}_p(h)\, p$. -/
def IsDivisorOf (D : Divisor k K) (h : K) : Prop := h ≠ 0 ∧ ∀ p, D p = p.ord h

/-- The space $L(D) = \{\varphi \mid \operatorname{div}(\varphi) + D \geq 0\} \cup \{0\}$ (equation (5),
p. 41), as a `k`-subspace of `K`: $\varphi\, t_p^{D(p)} \in \mathcal O_p$ for every prime divisor `p`. -/
@[kb "milne2006ec" "Ch. I, §4, Def. of L(D), equation (5), pdf p. 41"]
def Divisor.L (D : Divisor k K) : Submodule k K where
  carrier := {φ | ∀ p : PrimeDivisor k K, φ * p.unif ^ (D p) ∈ p.O}
  add_mem' {φ ψ} hφ hψ p := by
    rw [add_mul]
    exact add_mem (hφ p) (hψ p)
  zero_mem' p := by simp
  smul_mem' c φ hφ p := by
    rw [Algebra.smul_def, mul_assoc]
    exact mul_mem (p.algebraMap_mem c) (hφ p)

/-- $\ell(D) = \dim_k L(D)$ (p. 41). -/
@[kb "milne2006ec" "Ch. I, §4, Def. of l(D), pdf p. 41"]
noncomputable def Divisor.ell (D : Divisor k K) : ℕ := Module.finrank k D.L

/-- The integer `g` of Riemann's theorem in the form of Theorem 4.13 (p. 45): $L(D)$ is finite-dimensional
and $\ell(D) \geq \deg D + 1 - g$ for every divisor, with equality when $\deg D > 2g - 2$. -/
def IsGenus (k K : Type*) [Field k] [Field K] [Algebra k K] (g : ℤ) : Prop :=
  ∀ D : Divisor k K, FiniteDimensional k D.L ∧ D.deg + 1 - g ≤ D.ell ∧
    (2 * g - 2 < D.deg → (D.ell : ℤ) = D.deg + 1 - g)

open Classical in
/-- The **genus** (p. 41): the integer `g` of Riemann's theorem (0 if there is none). -/
@[kb "milne2006ec" "Ch. I, §4, Def. of the genus, pdf p. 41"]
noncomputable def genus (k K : Type*) [Field k] [Field K] [Algebra k K] : ℤ :=
  if h : ∃ g, IsGenus k K g then h.choose else 0

/-- **Divisors of functions** (p. 45), as a named statement (Fulton 1969, Chap. 8): in the function field
of a nonsingular absolutely irreducible projective plane curve, a nonzero function has only finitely
many zeros and poles, and its divisor has degree 0. -/
@[kb "milne2006ec" "Ch. I, §4, div(h) is a divisor of degree zero, pdf p. 45"]
structure PrincipalDivisors : Prop where
  exists_div : ∀ (k : Type) [Field k] [PerfectField k] (F : MvPolynomial (Fin 3) k) [Fact (Prime F)],
    IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsNonsingularProjCurve F → ∀ h : projFunctionField F, h ≠ 0 →
      ∃ D : Divisor k (projFunctionField F), IsDivisorOf D h ∧ D.deg = 0

/-- **Theorem 4.13 (Riemann)** (p. 45), as a named statement (Milne: "the usual proofs apply over
arbitrary fields"; Fulton 1969, Chap. 8): for a nonsingular absolutely irreducible projective plane
curve over a perfect field there is an integer `g` with $\ell(D) \geq \deg D + 1 - g$ for all divisors,
with equality for $\deg D > 2g - 2$. -/
@[kb "milne2006ec" "Ch. I, Thm. 4.13, pdf p. 45"]
structure Thm4_13 : Prop where
  riemann : ∀ (k : Type) [Field k] [PerfectField k] (F : MvPolynomial (Fin 3) k) [Fact (Prime F)],
    IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsNonsingularProjCurve F → ∃ g : ℤ, IsGenus k (projFunctionField F) g

/-- **Theorem 4.5 (Riemann)** (p. 41): over an algebraically closed field, for a nonsingular projective
plane curve there is an integer `g` with $\ell(D) \geq \deg D + 1 - g$ for all divisors, with equality for
$\deg D$ sufficiently positive.  Deduced from the named statement `Thm4_13` (an algebraically closed field
is perfect).  Divisors are taken in the form of p. 45 (prime divisors); see the module docstring. -/
@[kb "milne2006ec" "Ch. I, Thm. 4.5, pdf p. 41"]
theorem theorem_4_5 (h : Thm4_13) (k : Type) [Field k] [IsAlgClosed k] (F : MvPolynomial (Fin 3) k)
    [Fact (Prime F)] (hF : IsProjectivePlaneCurve F) (hirr : Irreducible (baseChange (AlgebraicClosure k) F))
    (hns : IsNonsingularProjCurve F) :
    ∃ g : ℤ, ∀ D : Divisor k (projFunctionField F), (D.deg + 1 - g ≤ D.ell) ∧
      ∃ N : ℤ, ∀ D : Divisor k (projFunctionField F), N ≤ D.deg → (D.ell : ℤ) = D.deg + 1 - g := by
  obtain ⟨g, hg⟩ := h.riemann k F hF hirr hns
  exact ⟨g, fun D => ⟨(hg D).2.1, 2 * g - 1, fun D' hD' => (hg D').2.2 (by omega)⟩⟩

/-- **Remark 4.7 (a) (Riemann–Roch)** (p. 41), as a named statement (Fulton 1969, Chap. 8, §§5–6): there is
a divisor `W` (canonical divisor) of degree $2g - 2$ with $\ell(D) = \deg D + 1 - g + \ell(W - D)$ for all `D`,
`g` the genus.  (The identification of the canonical divisors with the divisors of differentials is not
formalized.) -/
@[kb "milne2006ec" "Ch. I, Rem. 4.7 (a), pdf p. 41"]
structure Remark4_7 : Prop where
  riemann_roch : ∀ (k : Type) [Field k] [PerfectField k] (F : MvPolynomial (Fin 3) k) [Fact (Prime F)],
    IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsNonsingularProjCurve F →
    ∃ W : Divisor k (projFunctionField F),
      W.deg = 2 * genus k (projFunctionField F) - 2 ∧
      ∀ D : Divisor k (projFunctionField F),
        (D.ell : ℤ) = D.deg + 1 - genus k (projFunctionField F) + (W - D).ell

namespace PrimeDivisor

variable (p : PrimeDivisor k K)

/-- The chosen uniformizer is the image of an irreducible element of $\mathcal O_p$. -/
theorem exists_uniO : ∃ t : p.O, Irreducible t ∧ (t : K) = p.unif := by
  haveI := p.isDVR
  exact ⟨_, (IsDiscreteValuationRing.exists_irreducible p.O).choose_spec, rfl⟩

/-- The inverse of a unit of $\mathcal O_p$, viewed in `K`. -/
theorem coe_unit_inv (u : p.Oˣ) : (((u⁻¹ : p.Oˣ) : p.O) : K) = ((u : p.O) : K)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have h : (((u⁻¹ : p.Oˣ) : p.O) * ((u : p.O)) : p.O) = 1 := u.inv_mul
  have h2 := congrArg (fun x : p.O => (x : K)) h
  exact h2

/-- Every nonzero element of `K` is a unit of $\mathcal O_p$ times an integer power of the uniformizer. -/
theorem exists_rep {φ : K} (hφ : φ ≠ 0) :
    ∃ (n : ℤ) (u : p.Oˣ), φ = ((u : p.O) : K) * p.unif ^ n := by
  haveI := p.isDVR
  obtain ⟨t, ht, htu⟩ := p.exists_uniO
  rcases p.O.mem_or_inv_mem φ with h | h
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨φ, h⟩ : p.O)) (fun h0 => hφ (congrArg Subtype.val h0)) ht
    refine ⟨n, u, ?_⟩
    have := congrArg Subtype.val hu
    simp only [] at this
    rw [← htu, zpow_natCast]
    simpa using this
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨φ⁻¹, h⟩ : p.O)) (fun h0 => hφ (inv_eq_zero.mp (congrArg Subtype.val h0))) ht
    refine ⟨-(n : ℤ), u⁻¹, ?_⟩
    have h2 : φ⁻¹ = ((u : p.O) : K) * p.unif ^ n := by
      have := congrArg Subtype.val hu
      rw [← htu]
      simpa using this
    rw [coe_unit_inv, zpow_neg, zpow_natCast, ← mul_inv, ← h2, inv_inv]

/-- The exponent in `exists_rep` is unique. -/
theorem rep_unique {u u' : p.Oˣ} {m m' : ℤ}
    (h : ((u : p.O) : K) * p.unif ^ m = ((u' : p.O) : K) * p.unif ^ m') : m = m' := by
  haveI := p.isDVR
  obtain ⟨t, ht, htu⟩ := p.exists_uniO
  have ht0 : p.unif ≠ 0 := by
    rw [← htu]
    intro h0
    exact ht.ne_zero (Subtype.ext h0)
  have aux : ∀ {u u' : p.Oˣ} {m m' : ℤ},
      ((u : p.O) : K) * p.unif ^ m = ((u' : p.O) : K) * p.unif ^ m' → m < m' → False := by
    intro u u' m m' h hlt
    have he : ((m' - m).toNat : ℤ) = m' - m := Int.toNat_of_nonneg (by omega)
    have he0 : (m' - m).toNat ≠ 0 := by omega
    have hm' : p.unif ^ m' = p.unif ^ m * p.unif ^ ((m' - m).toNat) := by
      rw [← zpow_natCast, he, ← zpow_add₀ ht0]
      congr 1
      omega
    rw [hm'] at h
    have h3 : ((u : p.O) : K) = ((u' : p.O) : K) * p.unif ^ ((m' - m).toNat) := by
      apply mul_right_cancel₀ (zpow_ne_zero m ht0)
      rw [h]
      ring
    have h4 : (u : p.O) = (u' : p.O) * t ^ ((m' - m).toNat) := by
      apply Subtype.ext
      rw [h3, ← htu]
      simp
    have h5 : IsUnit ((u' : p.O) * t ^ ((m' - m).toNat)) := h4 ▸ u.isUnit
    exact ht.not_isUnit ((isUnit_pow_iff he0).mp ((IsUnit.mul_iff.mp h5).2))
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact (aux h hlt).elim
  · exact heq
  · exact (aux h.symm hgt).elim

/-- For $\varphi \neq 0$: $\varphi\, t_p^n \in \mathcal O_p$ if and only if $0 \leq \operatorname{ord}_p \varphi + n$. -/
theorem mul_unif_zpow_mem_iff {φ : K} (hφ : φ ≠ 0) (n : ℤ) :
    φ * p.unif ^ n ∈ p.O ↔ 0 ≤ p.ord φ + n := by
  haveI := p.isDVR
  obtain ⟨t, ht, htu⟩ := p.exists_uniO
  have ht0 : p.unif ≠ 0 := by
    rw [← htu]
    intro h0
    exact ht.ne_zero (Subtype.ext h0)
  obtain ⟨m, u, hm⟩ := p.exists_rep hφ
  have hord : p.ord φ = m := by
    have H : ∃ n : ℤ, ∃ u : p.Oˣ, φ = (u : K) * p.unif ^ n := ⟨m, u, hm⟩
    unfold ord
    rw [dif_pos H]
    obtain ⟨u', hu'⟩ := H.choose_spec
    exact p.rep_unique (hu'.symm.trans hm)
  rw [hord, hm, mul_assoc, ← zpow_add₀ ht0]
  constructor
  · intro hmem
    by_contra hs
    push_neg at hs
    have he : (((-(m + n)).toNat : ℕ) : ℤ) = -(m + n) := Int.toNat_of_nonneg (by omega)
    have he0 : (-(m + n)).toNat ≠ 0 := by omega
    set b : p.O := ⟨_, hmem⟩ with hb
    have h6 : (u : p.O) = t ^ ((-(m + n)).toNat) * b := by
      apply Subtype.ext
      simp only [hb, Subring.coe_mul, SubmonoidClass.coe_pow, ← htu]
      have : p.unif ^ ((-(m + n)).toNat) * (↑u * p.unif ^ (m + n)) = ↑u := by
        rw [← zpow_natCast, he, mul_left_comm, ← zpow_add₀ ht0]
        simp
      simpa [← htu] using this.symm
    have h5 : IsUnit (t ^ ((-(m + n)).toNat) * b) := h6 ▸ u.isUnit
    exact ht.not_isUnit ((isUnit_pow_iff he0).mp ((IsUnit.mul_iff.mp h5).1))
  · intro hs
    have he : (((m + n).toNat : ℕ) : ℤ) = m + n := Int.toNat_of_nonneg hs
    have : (u : K) * p.unif ^ (m + n) = (((u : p.O) * t ^ ((m + n).toNat) : p.O) : K) := by
      have h7 : p.unif ^ (m + n) = p.unif ^ ((m + n).toNat) := by rw [← zpow_natCast, he]
      rw [h7, ← htu]
      rfl
    rw [this]
    exact Subtype.property _

end PrimeDivisor

/-- A divisor with all multiplicities nonnegative has nonnegative degree. -/
theorem Divisor.deg_nonneg {D : Divisor k K} (hD : ∀ p, 0 ≤ D p) : 0 ≤ D.deg := by
  simp only [Divisor.deg, Finsupp.liftAddHom_apply, zmultiplesHom_apply]
  unfold Finsupp.sum
  exact Finset.sum_nonneg fun p _ => by
    dsimp only
    rw [zmultiplesHom_apply, smul_eq_mul]
    exact mul_nonneg (hD p) (Int.natCast_nonneg _)

/-- **Remark 4.7 (a)** (p. 41): the Riemann–Roch theorem gives equality in Riemann's inequality when
$\deg D > 2g - 2$ (then $\ell(W - D) = 0$ since $\deg(W - D) < 0$; this step uses that a divisor of negative
degree has $\ell = 0$, which follows from the named statement `PrincipalDivisors`). -/
@[kb "milne2006ec" "Ch. I, Rem. 4.7 (a), pdf p. 41"]
theorem remark_4_7_equality (hP : PrincipalDivisors) (k : Type) [Field k] [PerfectField k]
    (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (hF : IsProjectivePlaneCurve F)
    (hirr : Irreducible (baseChange (AlgebraicClosure k) F)) (hns : IsNonsingularProjCurve F)
    (D : Divisor k (projFunctionField F)) (hD : D.deg < 0) : D.ell = 0 := by
  unfold Divisor.ell
  have key' : ∀ φ : projFunctionField F, φ ∈ D.L → φ = 0 := by
    intro φ hφ
    by_contra hφ0
    obtain ⟨D', ⟨_, hD'⟩, hdeg⟩ := hP.exists_div k F hF hirr hns φ hφ0
    have hnn : ∀ p, 0 ≤ (D' + D) p := by
      intro p
      rw [Finsupp.add_apply, hD' p]
      exact (p.mul_unif_zpow_mem_iff hφ0 (D p)).mp (hφ p)
    have := Divisor.deg_nonneg hnn
    rw [map_add, hdeg] at this
    omega
  haveI : Subsingleton D.L :=
    ⟨fun a b => Subtype.ext ((key' a a.2).trans (key' b b.2).symm)⟩
  exact Module.finrank_zero_of_subsingleton

/-- **Genus of a plane curve** (formula (7), p. 42), as a named statement (Fulton 1969, p. 199): a
nonsingular projective plane curve of degree `d` has genus $(d - 1)(d - 2)/2$. -/
@[kb "milne2006ec" "Ch. I, §4, genus formula (7), pdf p. 42"]
structure GenusFormula : Prop where
  genus_eq : ∀ (k : Type) [Field k] [PerfectField k] (F : MvPolynomial (Fin 3) k) [Fact (Prime F)],
    IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsNonsingularProjCurve F →
      IsGenus k (projFunctionField F) (((curveDegree F : ℤ) - 1) * ((curveDegree F : ℤ) - 2) / 2)

/-- **Remark 4.7 (a)** (p. 41): from the Riemann–Roch theorem (named statement `Remark4_7`), equality holds
in Riemann's inequality when $\deg D > 2g - 2$ (using `PrincipalDivisors` for $\ell(W - D) = 0$). -/
@[kb "milne2006ec" "Ch. I, Rem. 4.7 (a), pdf p. 41"]
theorem remark_4_7_eq (hRR : Remark4_7) (hP : PrincipalDivisors) (k : Type) [Field k]
    [PerfectField k] (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (hF : IsProjectivePlaneCurve F)
    (hirr : Irreducible (baseChange (AlgebraicClosure k) F)) (hns : IsNonsingularProjCurve F) :
    ∃ W : Divisor k (projFunctionField F), W.deg = 2 * genus k (projFunctionField F) - 2 ∧
      ∀ D : Divisor k (projFunctionField F), 2 * genus k (projFunctionField F) - 2 < D.deg →
        (D.ell : ℤ) = D.deg + 1 - genus k (projFunctionField F) := by
  obtain ⟨W, hW, hRR'⟩ := hRR.riemann_roch k F hF hirr hns
  refine ⟨W, hW, fun D hD => ?_⟩
  have hneg : (W - D).deg < 0 := by
    rw [map_sub]
    omega
  have h0 := remark_4_7_equality hP k F hF hirr hns (W - D) hneg
  rw [hRR' D, h0]
  simp

/-- The multiplicity of a point of a projective plane curve, computed on its affine piece. -/
noncomputable def projMultiplicity (F : MvPolynomial (Fin 3) k) {K : Type*} [Field K] [Algebra k K]
    (P : ℙ K (Fin 3 → K)) : ℕ :=
  multiplicityAt (dehomogenize (pieceIndex P.rep) F) (pieceCoords (pieceIndex P.rep) P.rep)

/-- **Aside 4.8** (p. 42), the genus formula, as a named statement (Fulton 1969, p. 199): over an
algebraically closed field, an irreducible projective plane curve `C'` of degree `d` whose singular points
are ordinary multiple points has (function field of) genus
$\frac{(d-1)(d-2)}{2} - \sum_P \frac{m_P(m_P - 1)}{2}$, the sum over the (finitely many) singular points.
(The existence of such plane models of every curve, also in Aside 4.8, is not formalized.) -/
@[kb "milne2006ec" "Ch. I, Aside 4.8, pdf p. 42"]
structure Aside4_8 : Prop where
  genus_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (F : MvPolynomial (Fin 3) k) [Fact (Prime F)],
    IsProjectivePlaneCurve F →
    (∀ P ∈ projectivePoints F k, ¬ IsNonsingularProjPoint F P →
      IsOrdinarySingularity (dehomogenize (pieceIndex P.rep) F) (pieceCoords (pieceIndex P.rep) P.rep)) →
    ∃ S : Finset (ℙ k (Fin 3 → k)),
      (S : Set _) = {P | P ∈ projectivePoints F k ∧ ¬ IsNonsingularProjPoint F P} ∧
      IsGenus k (projFunctionField F)
        (((curveDegree F : ℤ) - 1) * ((curveDegree F : ℤ) - 2) / 2 -
          ∑ P ∈ S, ((projMultiplicity F P : ℤ) * ((projMultiplicity F P : ℤ) - 1) / 2))

/-- **Aside 4.9** (p. 42), as a named statement (Fulton 1969, Chap. 3): for a nonsingular absolutely
irreducible affine plane curve, $k[C]$ is a Dedekind domain.  Its Picard group is then its ideal class
group, Mathlib's `ClassGroup` (isomorphic to the Picard group of the ring, `ClassGroup.equivPic`). -/
@[kb "milne2006ec" "Ch. I, Aside 4.9, pdf p. 42"]
structure Aside4_9 : Prop where
  isDedekindDomain : ∀ (k : Type) [Field k] (f : MvPolynomial (Fin 2) k),
    IsAffinePlaneCurve f → IsGeometricallyIrreducible f → IsNonsingularCurve f →
    IsDedekindDomain (coordinateRing f)

/-! ### Principal divisors and Picard groups -/

/-- The group of principal divisors $P(C)$ (p. 42), generated by the divisors of nonzero functions. -/
@[kb "milne2006ec" "Ch. I, §4, Def. of principal divisors P(C), pdf p. 42"]
def principalDivisors : AddSubgroup (Divisor k K) :=
  AddSubgroup.closure {D | ∃ h : K, IsDivisorOf D h}

/-- Divisors `D`, `D'` are **linearly equivalent** if $D - D'$ is principal (p. 42). -/
@[kb "milne2006ec" "Ch. I, §4, Def. of linear equivalence, pdf p. 42"]
def LinearlyEquivalent (D D' : Divisor k K) : Prop := D - D' ∈ principalDivisors

/-- The divisors of degree 0, $\mathrm{Div}^0(C)$ (p. 42). -/
abbrev divisorsDegZero : AddSubgroup (Divisor k K) := (Divisor.deg (k := k) (K := K)).ker

/-- The Picard group $\mathrm{Pic}(C) = \mathrm{Div}(C)/P(C)$ (p. 42). -/
@[kb "milne2006ec" "Ch. I, §4, Def. of Pic(C), pdf p. 42"]
abbrev Pic (k K : Type*) [Field k] [Field K] [Algebra k K] :=
  Divisor k K ⧸ (principalDivisors : AddSubgroup (Divisor k K))

/-- The group $\mathrm{Pic}^0(C) = \mathrm{Div}^0(C)/P(C)$ (p. 42). -/
@[kb "milne2006ec" "Ch. I, §4, Def. of Pic^0(C), pdf p. 42"]
abbrev Pic0 (k K : Type*) [Field k] [Field K] [Algebra k K] :=
  divisorsDegZero (k := k) (K := K) ⧸
    (principalDivisors (k := k) (K := K)).addSubgroupOf (divisorsDegZero (k := k) (K := K))

/-- $[p] - [q]$ has degree 0 when `p` and `q` have degree 1. -/
theorem Divisor.deg_single_sub_single {p q : PrimeDivisor k K} (hp : p.deg = 1) (hq : q.deg = 1) :
    Divisor.deg (Finsupp.single p 1 - Finsupp.single q 1) = 0 := by
  rw [map_sub]
  simp only [Divisor.deg, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, hp, hq]
  simp

/-! ### Points and prime divisors -/

/-- The prime divisor `p` is the local ring of the curve at the point `P ∈ C(k)` (p. 44): its elements are
the quotients $G/H$ of homogeneous polynomials of equal degree with $H(P) \neq 0$. -/
def IsLocalRingAt (F : MvPolynomial (Fin 3) k) [Fact (Prime F)]
    (p : PrimeDivisor k (projFunctionField F)) (P : ℙ k (Fin 3 → k)) : Prop :=
  ∀ φ : projFunctionField F, φ ∈ p.O ↔
    ∃ (d : ℕ) (g h : MvPolynomial (Fin 3) k), g.IsHomogeneous d ∧ h.IsHomogeneous d ∧
      eval P.rep h ≠ 0 ∧
      (φ : FractionRing (homogCoordRing F)) = homogFrac F g / homogFrac F h

/-- **Points and prime divisors** (pp. 40, 44), as a named statement (Fulton 1969, Chap. 3, Thm. 1, p. 70):
for a nonsingular absolutely irreducible projective plane curve, the local ring at a point $P \in C(k)$ is a
discrete valuation ring, so a prime divisor of degree 1, and when `k` is algebraically closed every prime
divisor is the local ring at a unique point. -/
@[kb "milne2006ec" "Ch. I, §4, local rings at points are prime divisors, pdf pp. 40, 44"]
structure PointPrimeDivisor : Prop where
  exists_unique : ∀ (k : Type) [Field k] [PerfectField k] (F : MvPolynomial (Fin 3) k) [Fact (Prime F)],
    IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsNonsingularProjCurve F → ∀ P ∈ projectivePoints F k,
      ∃! p : PrimeDivisor k (projFunctionField F), IsLocalRingAt F p P ∧ p.deg = 1
  surj : ∀ (k : Type) [Field k] [IsAlgClosed k] (F : MvPolynomial (Fin 3) k) [Fact (Prime F)],
    IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsNonsingularProjCurve F → ∀ p : PrimeDivisor k (projFunctionField F),
      ∃! P, P ∈ projectivePoints F k ∧ IsLocalRingAt F p P

/-- **Proposition 4.10** (p. 43), as a named statement (Milne's proof uses 4.24 (b) and 4.26 (a)): let `C`
be a nonsingular projective curve of genus 1 over an algebraically closed field and $O \in C(k)$; then
$P \mapsto [P] - [O]$ is a bijection $C(k) \to \mathrm{Pic}^0(C)$.  The point–prime-divisor correspondence
`ψ` is any map with `IsLocalRingAt F (ψ P) P` (unique by `PointPrimeDivisor`). -/
@[kb "milne2006ec" "Ch. I, Prop. 4.10, pdf p. 43"]
structure Prop4_10 : Prop where
  bijective : ∀ (k : Type) [Field k] [IsAlgClosed k] (F : MvPolynomial (Fin 3) k) [Fact (Prime F)],
    IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsNonsingularProjCurve F → IsGenus k (projFunctionField F) 1 →
    ∀ (ψ : ℙ k (Fin 3 → k) → PrimeDivisor k (projFunctionField F)),
      (hψ : ∀ P ∈ projectivePoints F k, IsLocalRingAt F (ψ P) P ∧ (ψ P).deg = 1) →
      ∀ O (hO : O ∈ projectivePoints F k),
        Function.Bijective fun P : projectivePoints F k =>
          (QuotientAddGroup.mk
            (⟨Finsupp.single (ψ P.1) 1 - Finsupp.single (ψ O) 1,
              Divisor.deg_single_sub_single (hψ P.1 P.2).2 (hψ O hO).2⟩ :
              divisorsDegZero (k := k) (K := projFunctionField F)) :
            Pic0 k (projFunctionField F))

end NumberFieldKB.MilneEC

end
