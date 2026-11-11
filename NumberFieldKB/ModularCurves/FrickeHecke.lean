import NumberFieldKB.ModularCurves.HeckePic
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Order.Filter.Germ.Basic

/-!
# The Fricke involution and the degeneracy maps

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §4 (pdf p. 205). For $M = deN$ the Fricke involutions
$w_M(z) = -1/(Mz)$ and $w_N$ intertwine the degeneracy maps $z \mapsto dz$ and $z \mapsto ez$:
$d \cdot w_M(z) = w_N(ez)$. On function fields (contravariantly):

* **`frickeX0_comp_degeneracy`**: $w_M^* \circ \iota_d = \iota_e \circ w_N^*$ as maps
  $\mathbb Q(X_0(N)) \to \mathbb Q(X_0(M))$.

Everything is checked on functions: `toGerm_frickeX0_x0Frac` computes the germ of $w_M^* f$ as $f \circ w_M$ for
$f$ given as a quotient $P(j, j_M)/Q(j, j_M)$.

On points (places over $\mathbb Q$, cusps included) and divisors:

* `PrimeDivisor.comapEquiv` (general): the place $\sigma^* Q$ for a field automorphism $\sigma$, with
  $\operatorname{ord}_{\sigma^*Q} = \operatorname{ord}_Q \circ \sigma$ and $\deg \sigma^* Q = \deg Q$.
* `frickePlace`, `frickeDiv`: $w_N$ on the points and divisors of $X_0(N)$.
* `degeneracyPlace_frickePlace`, `ramIndex_frickePlace`, `resDegX0_frickePlace`: $w$ intertwines the maps on points
  and preserves ramification indices and residue degrees; hence `frickeDiv_pushX0`, `frickeDiv_pullX0`.
* **`frickeDiv_heckeX0_frickeDiv`**: $w_N\,T(p)\,w_N = T(p)^{\mathsf t} = \pi_{1*}\pi_p^*$ on divisors, and
  **`frickePic0_heckePic0_frickePic0`**: the same on $\mathrm{Pic}^0(X_0(N)) = J_0(N)(\mathbb Q)$.

That $T(p)^{\mathsf t} = T(p)$ for $p \nmid N$ (so that $w_N$ commutes with $T(p)$) needs the Atkin–Lehner
involution $w_p$ of $X_0(pN)$ exchanging the two degeneracy maps; it is not proved here.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC NumberFieldKB.MilneEC.V

variable {N M : ℕ} [NeZero N] [NeZero M]

omit [NeZero M] in
/-- $w_M$ is an involution of $\mathbb H$. -/
theorem fricke_fricke (hM : 1 ≤ M) (z : ℍ) : fricke M (fricke M z) = z := by
  ext
  rw [coe_fricke hM, coe_fricke hM]
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  field_simp

/-- $j_d(w_M z) = j_e(z)$ for $de = M$. -/
theorem jN_fricke_mul {d e : ℕ} (hde : d * e = M) (z : ℍ) : jN d (fricke M z) = jN e z := by
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hd : d ≠ 0 := by rintro rfl; simp at hde; exact NeZero.ne M hde.symm
  have he : e ≠ 0 := by rintro rfl; simp at hde; exact NeZero.ne M hde.symm
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
  set u : ℍ := ofComplex ((e : ℂ) * z) with hu
  have hu' : (u : ℂ) = (e : ℂ) * z := coe_ofComplex_mul he1 z
  unfold jN
  rw [← jFun_neg_inv u]
  congr 2
  rw [coe_fricke hM, hu']
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast he
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  rw [← hde]
  push_cast
  field_simp

/-- **$w_M^*$ on functions**: if $f \cdot Q(j, j_M) = P(j, j_M)$ with $Q(j, j_M) \ne 0$, the germ of
$w_M^*(P/Q)$ is that of $f \circ w_M$. -/
theorem toGerm_frickeX0_x0Frac {P Q : ℚ[X][X]} {f : ℍ → ℂ} (hQ : evalJJNRat M Q ≠ 0)
    (hf : ∀ z, f z * evalJJNRat M Q z = evalJJNRat M P z) :
    toGerm M (frickeX0 (prop2_4' M) (x0Frac M P Q)) = germ (f ∘ fricke M) := by
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have e1 : frickeX0 (prop2_4' M) (x0Frac M P Q) = x0Frac M (swapQ P) (swapQ Q) := by
    rw [x0Frac, map_div₀, frickeX0_coordToX0, frickeX0_coordToX0, frickeCoord_mk, frickeCoord_mk]
    rfl
  rw [e1]
  refine toGerm_x0Frac ?_ ?_
  · intro h0
    apply hQ
    funext z
    have := congrFun h0 (fricke M z)
    rw [evalJJNRat_swapQ hM, fricke_fricke hM] at this
    simpa using this
  · intro z
    rw [evalJJNRat_swapQ hM, evalJJNRat_swapQ hM]
    exact hf (fricke M z)

/-- $w_M^*(j_d) = j_e$ in $\mathbb Q(X_0(M))$, for $de = M$. -/
theorem frickeX0_jNElt {d e : ℕ} (hde : d * e = M) (hd : d ∣ M) (he : e ∣ M) :
    frickeX0 (prop2_4' M) (jNElt M d hd) = jNElt M e he := by
  apply toGerm_injective (N := M)
  rw [toGerm_jNElt, jNElt, toGerm_frickeX0_x0Frac (exists_rat_jN_of_dvd hd).choose_spec.choose_spec.1
    (exists_rat_jN_of_dvd hd).choose_spec.choose_spec.2]
  congr 1
  funext z
  exact jN_fricke_mul hde z

/-- Ring maps out of $\mathbb Q(X_0(N))$ agree if they agree on $j$ and $j_N$. -/
theorem X0.ringHom_ext {L : Type*} [CommRing L] {f g : X0 N →+* L} (h1 : f (jX0 (prop2_4' N)) = g (jX0 (prop2_4' N)))
    (h2 : f (jNX0 (prop2_4' N)) = g (jNX0 (prop2_4' N))) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext'
  · apply ratFunc_ringHom_ext
    have e : (AdjoinRoot.of _ RatFunc.X : X0 N) = jX0 (prop2_4' N) := by
      rw [← AdjoinRoot.algebraMap_eq]; exact algebraMap_X_X0
    change f (AdjoinRoot.of _ RatFunc.X) = g (AdjoinRoot.of _ RatFunc.X)
    rw [e, h1]
  · have e : (AdjoinRoot.root _ : X0 N) = jNX0 (prop2_4' N) := by
      rw [jNX0, coordToX0_mk, Polynomial.map_X]; rfl
    change f (AdjoinRoot.root _) = g (AdjoinRoot.root _)
    rw [e, h2]

/-- **The Fricke involutions intertwine the degeneracy maps** (Milne V §4): for $M = deN$,
$w_M^* \circ \iota_d = \iota_e \circ w_N^*$, i.e. $d \cdot w_M(z) = w_N(ez)$. -/
@[kb "milne2006ec" "Ch. V, §4, w_M and the maps z ↦ dz between X_0(M) and X_0(N), pdf p. 205"]
theorem frickeX0_comp_degeneracy {d e : ℕ} (hde : d * e * N = M) (hd : d * N ∣ M) (he : e * N ∣ M) :
    (frickeX0 (prop2_4' M)).toRingHom.comp (degeneracy N M d hd) =
      (degeneracy N M e he).comp (frickeX0 (prop2_4' N)).toRingHom := by
  apply X0.ringHom_ext
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [degeneracy_jX0, frickeX0_jX0, degeneracy_jNX0]
    exact frickeX0_jNElt (by rw [← hde]; ring) _ _
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [degeneracy_jNX0, frickeX0_jNX0, degeneracy_jX0]
    exact frickeX0_jNElt (by rw [← hde]; ring) _ _

/-! ### Transporting places along a field automorphism -/

section PlaceEquiv

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The place $\sigma^* Q$ of `K` for an automorphism $\sigma$: valuation ring $\sigma^{-1}(\mathcal O_Q)$. -/
noncomputable def _root_.NumberFieldKB.MilneEC.PrimeDivisor.comapEquiv (σ : K ≃+* K) (Q : PrimeDivisor ℚ K) :
    PrimeDivisor ℚ K where
  O := Q.O.comap σ.toRingHom
  algebraMap_mem c := by
    rw [ValuationSubring.mem_comap]
    have : σ.toRingHom (algebraMap ℚ K c) = algebraMap ℚ K c := by
      simp only [RingEquiv.toRingHom_eq_coe, eq_ratCast, map_ratCast]
    rw [this]
    exact Q.algebraMap_mem c
  isDVR := by
    have := Q.isDVR
    let e : Q.O ≃+* Q.O.comap σ.toRingHom :=
      { toFun := fun x => ⟨σ.symm x, by rw [ValuationSubring.mem_comap]; simp⟩
        invFun := fun y => ⟨σ y, ValuationSubring.mem_comap.1 y.2⟩
        left_inv := fun x => by ext; simp
        right_inv := fun y => by ext; simp
        map_mul' := fun x y => Subtype.ext (map_mul σ.symm x.1 y.1)
        map_add' := fun x y => Subtype.ext (map_add σ.symm x.1 y.1) }
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e

theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.mem_comapEquiv_O (σ : K ≃+* K) (Q : PrimeDivisor ℚ K) (x : K) :
    x ∈ (Q.comapEquiv σ).O ↔ σ x ∈ Q.O :=
  ValuationSubring.mem_comap

/-- $\sigma : \mathcal O_{\sigma^* Q} \cong \mathcal O_Q$. -/
noncomputable def _root_.NumberFieldKB.MilneEC.PrimeDivisor.comapEquivRingEquiv (σ : K ≃+* K)
    (Q : PrimeDivisor ℚ K) : (Q.comapEquiv σ).O ≃+* Q.O where
  toFun x := ⟨σ x, (Q.mem_comapEquiv_O σ x).1 x.2⟩
  invFun y := ⟨σ.symm y, (Q.mem_comapEquiv_O σ _).2 (by simp)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := Subtype.ext (map_mul σ x.1 y.1)
  map_add' x y := Subtype.ext (map_add σ x.1 y.1)

theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.comapEquiv_comapEquiv {σ τ : K ≃+* K}
    (h : ∀ x, τ (σ x) = x) (Q : PrimeDivisor ℚ K) : (Q.comapEquiv τ).comapEquiv σ = Q := by
  apply PrimeDivisor.ext_O
  ext x
  rw [PrimeDivisor.mem_comapEquiv_O, PrimeDivisor.mem_comapEquiv_O, h]

/-- $\operatorname{ord}_{\sigma^* Q}(x) = \operatorname{ord}_Q(\sigma x)$. -/
theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.ord_comapEquiv (σ : K ≃+* K) (Q : PrimeDivisor ℚ K) {x : K}
    (hx : x ≠ 0) : (Q.comapEquiv σ).ord x = Q.ord (σ x) := by
  have hO : (Q.comapEquiv σ).O = (Q.valuation.comap σ.toRingHom).valuationSubring := by
    ext y
    rw [PrimeDivisor.mem_comapEquiv_O, Q.mem_O_iff_valuation_le_one, Valuation.mem_valuationSubring_iff,
      Valuation.comap_apply]
    rfl
  have h0 : σ.symm Q.unif ≠ 0 := by simpa using Q.unif_ne_zero
  have h1 : ordV (Q.valuation.comap σ.toRingHom) (σ.symm Q.unif) = 1 := by
    rw [ordV, Valuation.comap_apply]
    have : σ.toRingHom (σ.symm Q.unif) = Q.unif := by simp
    rw [this, ← ordV, Q.ordV_valuation_unif]
  rw [PrimeDivisor.ord_eq_ordV _ _ hO h0 h1 hx, Q.ord_eq_ordV_valuation ((map_ne_zero σ).2 hx), ordV, ordV,
    Valuation.comap_apply]
  rfl

/-- $\deg \sigma^* Q = \deg Q$. -/
theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.deg_comapEquiv (σ : K ≃+* K) (Q : PrimeDivisor ℚ K) :
    (Q.comapEquiv σ).deg = Q.deg := by
  let : Algebra ℚ (IsLocalRing.ResidueField (Q.comapEquiv σ).O) :=
    ((IsLocalRing.residue (Q.comapEquiv σ).O).comp (Q.comapEquiv σ).ofBase).toAlgebra
  let : Algebra ℚ (IsLocalRing.ResidueField Q.O) := ((IsLocalRing.residue Q.O).comp Q.ofBase).toAlgebra
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl ℚ)
    (IsLocalRing.ResidueField.mapEquiv (Q.comapEquivRingEquiv σ)) (RingHom.ext_rat _ _)

/-- Divisors transported along $\sigma$: $[Q] \mapsto [\sigma^* Q]$. -/
noncomputable def divComapEquiv (σ : K ≃+* K) : Divisor ℚ K →+ Divisor ℚ K :=
  Finsupp.mapDomain.addMonoidHom (PrimeDivisor.comapEquiv σ)

theorem divComapEquiv_single (σ : K ≃+* K) (Q : PrimeDivisor ℚ K) (n : ℤ) :
    divComapEquiv σ (Finsupp.single Q n) = Finsupp.single (Q.comapEquiv σ) n :=
  Finsupp.mapDomain_single

/-- For an involution, $(\sigma D)(Q) = D(\sigma^* Q)$. -/
theorem divComapEquiv_apply {σ : K ≃+* K} (hσ : ∀ x, σ (σ x) = x) (D : Divisor ℚ K) (Q : PrimeDivisor ℚ K) :
    divComapEquiv σ D Q = D (Q.comapEquiv σ) := by
  have hinj : Function.Injective (PrimeDivisor.comapEquiv (K := K) σ) := fun a b hab => by
    rw [← PrimeDivisor.comapEquiv_comapEquiv hσ a, hab, PrimeDivisor.comapEquiv_comapEquiv hσ b]
  conv_lhs => rw [← PrimeDivisor.comapEquiv_comapEquiv hσ Q]
  exact Finsupp.mapDomain_apply_of_injective hinj D _

theorem divComapEquiv_divComapEquiv {σ : K ≃+* K} (hσ : ∀ x, σ (σ x) = x) (D : Divisor ℚ K) :
    divComapEquiv σ (divComapEquiv σ D) = D := by
  ext Q
  rw [divComapEquiv_apply hσ, divComapEquiv_apply hσ, PrimeDivisor.comapEquiv_comapEquiv hσ]

theorem deg_divComapEquiv (σ : K ≃+* K) (D : Divisor ℚ K) : Divisor.deg (divComapEquiv σ D) = Divisor.deg D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [map_add, map_add, hD, hE, map_add]
  | single Q n =>
    rw [divComapEquiv_single]
    simp only [Divisor.deg, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, PrimeDivisor.deg_comapEquiv]

/-- $\sigma \operatorname{div}(g) = \operatorname{div}(\sigma g)$ for an involution $\sigma$. -/
theorem isDivisorOf_divComapEquiv {σ : K ≃+* K} (hσ : ∀ x, σ (σ x) = x) {D : Divisor ℚ K} {g : K}
    (hD : IsDivisorOf D g) : IsDivisorOf (divComapEquiv σ D) (σ g) := by
  refine ⟨(map_ne_zero σ).2 hD.1, fun Q => ?_⟩
  rw [divComapEquiv_apply hσ, hD.2, PrimeDivisor.ord_comapEquiv σ Q hD.1]

end PlaceEquiv

/-! ### $w_N$ on the points and divisors of $X_0(N)$ -/

section X0

/-- **The Fricke involution on the points of $X_0(N)$** (places, cusps included): $Q \mapsto w_N^* Q$. -/
noncomputable abbrev frickePlace (N : ℕ) [NeZero N] (Q : PrimeDivisor ℚ (X0 N)) : PrimeDivisor ℚ (X0 N) :=
  Q.comapEquiv (frickeX0 (prop2_4' N))

theorem frickePlace_frickePlace (Q : PrimeDivisor ℚ (X0 N)) : frickePlace N (frickePlace N Q) = Q :=
  PrimeDivisor.comapEquiv_comapEquiv (frickeX0_frickeX0 _) Q

/-- **The Fricke involution on divisors of $X_0(N)$.** -/
@[kb "milne2006ec" "Ch. V, §4, the Fricke involution w_N on X_0(N), pdf p. 205"]
noncomputable def frickeDiv (N : ℕ) [NeZero N] : Divisor ℚ (X0 N) →+ Divisor ℚ (X0 N) :=
  divComapEquiv (frickeX0 (prop2_4' N))

theorem frickeDiv_apply (D : Divisor ℚ (X0 N)) (Q : PrimeDivisor ℚ (X0 N)) :
    frickeDiv N D Q = D (frickePlace N Q) :=
  divComapEquiv_apply (frickeX0_frickeX0 _) D Q

theorem frickeDiv_frickeDiv (D : Divisor ℚ (X0 N)) : frickeDiv N (frickeDiv N D) = D :=
  divComapEquiv_divComapEquiv (frickeX0_frickeX0 _) D

theorem frickeDiv_single (Q : PrimeDivisor ℚ (X0 N)) (n : ℤ) :
    frickeDiv N (Finsupp.single Q n) = Finsupp.single (frickePlace N Q) n :=
  divComapEquiv_single _ Q n

/-- The residue degree $f(Q / \pi_d Q)$ for $z \mapsto dz$. -/
noncomputable def resDegX0 {d : ℕ} (h : d * N ∣ M) (Q : PrimeDivisor ℚ (X0 M)) : ℕ :=
  letI := (degeneracy N M d h).toAlgebra
  haveI := isScalarTower_rat_degeneracy h
  haveI := isAlgebraic_degeneracy h
  Q.residueDeg (K := X0 N)

theorem pushX0_single {d : ℕ} (h : d * N ∣ M) (Q : PrimeDivisor ℚ (X0 M)) (n : ℤ) :
    pushX0 h (Finsupp.single Q n) = Finsupp.single (degeneracyPlace h Q) (n * resDegX0 h Q) := by
  simp only [pushX0, pushDiv, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, Finsupp.smul_single,
    smul_eq_mul]
  rfl

/-- Involutions $\sigma$ of $\mathbb Q(X_0(M))$ and $\tau$ of $\mathbb Q(X_0(N))$ with $\sigma\iota_d = \iota_e\tau$:
on curves, $\pi_d \circ \sigma = \tau \circ \pi_e$. -/
structure Intertwines {d e : ℕ} (hd : d * N ∣ M) (he : e * N ∣ M) (σ : X0 M ≃+* X0 M) (τ : X0 N ≃+* X0 N) :
    Prop where
  invol_left : ∀ x, σ (σ x) = x
  invol_right : ∀ x, τ (τ x) = x
  comm : ∀ x, σ (degeneracy N M d hd x) = degeneracy N M e he (τ x)

section Intertwine

variable {d e : ℕ} {hd : d * N ∣ M} {he : e * N ∣ M} {σ : X0 M ≃+* X0 M} {τ : X0 N ≃+* X0 N}

theorem Intertwines.comm' (H : Intertwines hd he σ τ) (x : X0 N) :
    σ (degeneracy N M e he x) = degeneracy N M d hd (τ x) := by
  conv_lhs => rw [← H.invol_right x, ← H.comm, H.invol_left]

theorem Intertwines.symm (H : Intertwines hd he σ τ) : Intertwines he hd σ τ :=
  ⟨H.invol_left, H.invol_right, H.comm'⟩

/-- **The maps on points are intertwined**: $\pi_e(\sigma^* Q) = \tau^*(\pi_d Q)$. -/
theorem degeneracyPlace_comapEquiv (H : Intertwines hd he σ τ) (Q : PrimeDivisor ℚ (X0 M)) :
    degeneracyPlace he (Q.comapEquiv σ) = (degeneracyPlace hd Q).comapEquiv τ := by
  apply PrimeDivisor.ext_O
  ext x
  rw [mem_degeneracyPlace_O, PrimeDivisor.mem_comapEquiv_O, PrimeDivisor.mem_comapEquiv_O,
    mem_degeneracyPlace_O, H.comm']

/-- **Ramification indices are preserved**: $e(\sigma^* Q / \tau^* P) = e(Q/P)$. -/
theorem ramIndex_comapEquiv (H : Intertwines hd he σ τ) (Q : PrimeDivisor ℚ (X0 M)) :
    ramIndex he (degeneracyPlace he (Q.comapEquiv σ)) (Q.comapEquiv σ) =
      ramIndex hd (degeneracyPlace hd Q) Q := by
  rw [degeneracyPlace_comapEquiv H]
  set P := degeneracyPlace hd Q with hP
  set y := (P.comapEquiv τ).unif
  have hy : y ≠ 0 := PrimeDivisor.unif_ne_zero _
  have hwy : τ y ≠ 0 := (_root_.map_ne_zero _).2 hy
  rw [ramIndex, PrimeDivisor.ord_comapEquiv _ _ ((_root_.map_ne_zero _).2 hy), H.comm']
  let := (degeneracy N M d hd).toAlgebra
  have := isScalarTower_rat_degeneracy hd
  have := isAlgebraic_degeneracy hd
  have : FiniteDimensional (X0 N) (X0 M) := finiteDimensional_degeneracy hd
  have h1 := Q.ord_algebraMap_of_comap_eq P rfl hwy
  have h2 : P.ord (τ y) = 1 := by
    rw [← PrimeDivisor.ord_comapEquiv _ _ hy, PrimeDivisor.ord_unif]
  change Q.ord (algebraMap (X0 N) (X0 M) _) = Q.ord (algebraMap (X0 N) (X0 M) P.unif)
  rw [h1, h2, mul_one]

/-- **Residue degrees are preserved**: $f(\sigma^* Q / \tau^* P) = f(Q/P)$. -/
theorem resDegX0_comapEquiv (H : Intertwines hd he σ τ) (Q : PrimeDivisor ℚ (X0 M)) :
    resDegX0 he (Q.comapEquiv σ) = resDegX0 hd Q := by
  set P := degeneracyPlace hd Q with hP
  set Q' := Q.comapEquiv σ with hQ'def
  set P' := P.comapEquiv τ with hP'def
  have hQ' : degeneracyPlace he Q' = P' := degeneracyPlace_comapEquiv H Q
  have hmem : ∀ x : P'.O, degeneracy N M e he x ∈ Q'.O := fun x =>
    (mem_degeneracyPlace_O he Q' x).1 (by rw [hQ']; exact x.2)
  let ψ : P'.O →+* Q'.O := ((degeneracy N M e he).comp P'.O.subtype).codRestrict Q'.O.toSubring hmem
  have hex : ∃ _ : IsLocalHom ψ, resDegX0 he Q' =
      letI := (IsLocalRing.ResidueField.map ψ).toAlgebra
      Module.finrank (IsLocalRing.ResidueField P'.O) (IsLocalRing.ResidueField Q'.O) := by
    unfold resDegX0
    let := (degeneracy N M e he).toAlgebra
    have := isScalarTower_rat_degeneracy he
    have := isAlgebraic_degeneracy he
    exact Q'.residueDeg_eq_of_comap_eq P' hQ' ψ (fun x => rfl)
  obtain ⟨hloc, h1⟩ := hex
  rw [h1]
  unfold resDegX0
  let := (degeneracy N M d hd).toAlgebra
  have := isScalarTower_rat_degeneracy hd
  have := isAlgebraic_degeneracy hd
  let := (IsLocalRing.ResidueField.map ψ).toAlgebra
  let := (Q.residueMap (K := X0 N)).toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (P.comapEquivRingEquiv τ))
    (IsLocalRing.ResidueField.mapEquiv (Q.comapEquivRingEquiv σ)) ?_
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun x => ?_
  change IsLocalRing.ResidueField.map (Q.comapHom (K := X0 N))
      (IsLocalRing.ResidueField.map (P.comapEquivRingEquiv τ : P'.O →+* P.O)
        (IsLocalRing.residue _ x)) =
    IsLocalRing.ResidueField.map (Q.comapEquivRingEquiv σ : Q'.O →+* Q.O)
      (IsLocalRing.ResidueField.map ψ (IsLocalRing.residue _ x))
  rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.map_residue]
  erw [IsLocalRing.ResidueField.map_residue]
  congr 1
  apply Subtype.ext
  change degeneracy N M d hd (τ x) = σ (degeneracy N M e he x)
  rw [H.comm']

/-- **Push-forward is intertwined**: $\tau \circ \pi_{d*} = \pi_{e*} \circ \sigma$ on divisors. -/
theorem divComapEquiv_pushX0 (H : Intertwines hd he σ τ) (D : Divisor ℚ (X0 M)) :
    divComapEquiv τ (pushX0 hd D) = pushX0 he (divComapEquiv σ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => rw [map_add, map_add, hD, hE, map_add, map_add]
  | single Q n =>
    rw [pushX0_single, divComapEquiv_single, divComapEquiv_single, pushX0_single,
      degeneracyPlace_comapEquiv H, resDegX0_comapEquiv H]

/-- **Pullback is intertwined**: $\sigma \circ \pi_d^* = \pi_e^* \circ \tau$ on divisors. -/
theorem divComapEquiv_pullX0 (H : Intertwines hd he σ τ) (D : Divisor ℚ (X0 N)) :
    divComapEquiv σ (pullX0 hd D) = pullX0 he (divComapEquiv τ D) := by
  ext Q'
  obtain ⟨Q, rfl⟩ : ∃ Q, Q' = Q.comapEquiv σ :=
    ⟨Q'.comapEquiv σ, (PrimeDivisor.comapEquiv_comapEquiv H.invol_left Q').symm⟩
  rw [divComapEquiv_apply H.invol_left, PrimeDivisor.comapEquiv_comapEquiv H.invol_left, pullX0_apply,
    pullX0_apply, divComapEquiv_apply H.invol_right, degeneracyPlace_comapEquiv H,
    PrimeDivisor.comapEquiv_comapEquiv H.invol_right, ← degeneracyPlace_comapEquiv H, ramIndex_comapEquiv H]

end Intertwine

theorem frickeX0_degeneracy_apply {d e : ℕ} (hde : d * e * N = M) (hd : d * N ∣ M) (he : e * N ∣ M)
    (x : X0 N) : frickeX0 (prop2_4' M) (degeneracy N M d hd x) = degeneracy N M e he (frickeX0 (prop2_4' N) x) :=
  RingHom.congr_fun (frickeX0_comp_degeneracy hde hd he) x

theorem intertwines_fricke {d e : ℕ} (hde : d * e * N = M) (hd : d * N ∣ M) (he : e * N ∣ M) :
    Intertwines hd he (frickeX0 (prop2_4' M)) (frickeX0 (prop2_4' N)) :=
  ⟨frickeX0_frickeX0 _, frickeX0_frickeX0 _, frickeX0_degeneracy_apply hde hd he⟩

/-- **$w$ and push-forward**: $w_N \circ \pi_{d*} = \pi_{e*} \circ w_M$ on divisors, for $M = deN$. -/
theorem frickeDiv_pushX0 {d e : ℕ} (hde : d * e * N = M) (hd : d * N ∣ M) (he : e * N ∣ M)
    (D : Divisor ℚ (X0 M)) : frickeDiv N (pushX0 hd D) = pushX0 he (frickeDiv M D) :=
  divComapEquiv_pushX0 (intertwines_fricke hde hd he) D

/-- **$w$ and pullback**: $w_M \circ \pi_d^* = \pi_e^* \circ w_N$ on divisors, for $M = deN$. -/
theorem frickeDiv_pullX0 {d e : ℕ} (hde : d * e * N = M) (hd : d * N ∣ M) (he : e * N ∣ M)
    (D : Divisor ℚ (X0 N)) : frickeDiv M (pullX0 hd D) = pullX0 he (frickeDiv N D) :=
  divComapEquiv_pullX0 (intertwines_fricke hde hd he) D

/-- The transpose of $T(p)$: $\pi_{1*} \circ \pi_p^*$ (the correspondence with its two maps exchanged). -/
noncomputable def heckeX0Transpose (N p : ℕ) [NeZero N] [NeZero p] :
    Divisor ℚ (X0 N) →+ Divisor ℚ (X0 N) :=
  (pushX0 (d := 1) (one_mul_dvd_mul N p)).comp (pullX0 (d := p) (dvd_rfl : p * N ∣ p * N))

/-- **$w_N T(p) w_N = T(p)^{\mathsf t}$** on divisors of $X_0(N)$, cusps included (Milne V §4: $w_{pN}$ exchanges the
two maps $z \mapsto z$ and $z \mapsto pz$ of $X_0(pN) \to X_0(N)$, up to $w_N$). -/
@[kb "milne2006ec" "Ch. V, §4, w_N and the Hecke correspondence T(p) on X_0(N), pdf p. 205"]
theorem frickeDiv_heckeX0_frickeDiv (N p : ℕ) [NeZero N] [NeZero p] (D : Divisor ℚ (X0 N)) :
    frickeDiv N (heckeX0 N p (frickeDiv N D)) = heckeX0Transpose N p D := by
  rw [heckeX0, AddMonoidHom.comp_apply, frickeDiv_pushX0 (d := p) (e := 1) (by ring) dvd_rfl (one_mul_dvd_mul N p),
    frickeDiv_pullX0 (d := 1) (e := p) (by ring) (one_mul_dvd_mul N p) dvd_rfl, frickeDiv_frickeDiv]
  rfl

/-! ### On $\mathrm{Pic}^0(X_0(N))$ -/

theorem frickeDiv_principal {D : Divisor ℚ (X0 N)} (hD : D ∈ principalDivisors) :
    frickeDiv N D ∈ principalDivisors := by
  have hle : (principalDivisors (k := ℚ) (K := X0 N)) ≤
      (principalDivisors (k := ℚ) (K := X0 N)).comap (frickeDiv N) := by
    refine (AddSubgroup.closure_le _).2 fun E ⟨f, hf⟩ => ?_
    exact AddSubgroup.subset_closure ⟨_, isDivisorOf_divComapEquiv (frickeX0_frickeX0 _) hf⟩
  exact hle hD

theorem frickeDiv_mem_divisorsDegZero {D : Divisor ℚ (X0 N)} (hD : D ∈ divisorsDegZero) :
    frickeDiv N D ∈ divisorsDegZero := by
  rw [AddMonoidHom.mem_ker] at hD ⊢
  rw [frickeDiv, deg_divComapEquiv, hD]

theorem heckeX0Transpose_eq (N p : ℕ) [NeZero N] [NeZero p] :
    heckeX0Transpose N p = (frickeDiv N).comp ((heckeX0 N p).comp (frickeDiv N)) :=
  AddMonoidHom.ext fun D => (frickeDiv_heckeX0_frickeDiv N p D).symm

theorem heckeX0Transpose_principal (N p : ℕ) [NeZero N] [NeZero p] {D : Divisor ℚ (X0 N)}
    (hD : D ∈ principalDivisors) : heckeX0Transpose N p D ∈ principalDivisors := by
  rw [heckeX0Transpose_eq]
  exact frickeDiv_principal (heckeX0_principal N p (frickeDiv_principal hD))

theorem heckeX0Transpose_mem_divisorsDegZero (N p : ℕ) [NeZero N] [NeZero p] {D : Divisor ℚ (X0 N)}
    (hD : D ∈ divisorsDegZero) : heckeX0Transpose N p D ∈ divisorsDegZero := by
  rw [heckeX0Transpose_eq]
  exact frickeDiv_mem_divisorsDegZero (heckeX0_mem_divisorsDegZero N p (frickeDiv_mem_divisorsDegZero hD))

/-- A map of divisors of $X_0(N)$ preserving degree 0 and principal divisors acts on $\mathrm{Pic}^0$. -/
noncomputable def pic0Map (φ : Divisor ℚ (X0 N) →+ Divisor ℚ (X0 N))
    (h0 : ∀ D ∈ divisorsDegZero (k := ℚ) (K := X0 N), φ D ∈ divisorsDegZero (k := ℚ) (K := X0 N))
    (hp : ∀ D ∈ principalDivisors (k := ℚ) (K := X0 N), φ D ∈ principalDivisors (k := ℚ) (K := X0 N)) :
    Pic0X0 N →+ Pic0X0 N :=
  QuotientAddGroup.map _ _ ((φ.comp (divisorsDegZero (k := ℚ) (K := X0 N)).subtype).codRestrict _
    fun D => h0 D D.2) fun D hD => by
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
      rw [AddSubgroup.mem_addSubgroupOf] at hD
      exact hp _ hD

theorem pic0Map_mk (φ : Divisor ℚ (X0 N) →+ Divisor ℚ (X0 N)) (h0) (hp)
    (D : divisorsDegZero (k := ℚ) (K := X0 N)) :
    pic0Map φ h0 hp (QuotientAddGroup.mk D) = QuotientAddGroup.mk ⟨φ D, h0 D D.2⟩ :=
  rfl

/-- **The Fricke involution $w_N$ on $\mathrm{Pic}^0(X_0(N)) = J_0(N)(\mathbb Q)$.** -/
@[kb "milne2006ec" "Ch. V, §4, the Fricke involution w_N acting on the jacobian J_0(N), pdf p. 205"]
noncomputable def frickePic0 (N : ℕ) [NeZero N] : Pic0X0 N →+ Pic0X0 N :=
  pic0Map (frickeDiv N) (fun _ hD => frickeDiv_mem_divisorsDegZero hD) (fun _ hD => frickeDiv_principal hD)

theorem frickePic0_frickePic0 (c : Pic0X0 N) : frickePic0 N (frickePic0 N c) = c := by
  induction c using QuotientAddGroup.induction_on with
  | H D =>
    rw [frickePic0, pic0Map_mk, pic0Map_mk]
    congr 1
    exact Subtype.ext (frickeDiv_frickeDiv D.1)

/-- The transpose $T(p)^{\mathsf t}$ on $\mathrm{Pic}^0(X_0(N))$. -/
noncomputable def heckePic0Transpose (N p : ℕ) [NeZero N] [NeZero p] : Pic0X0 N →+ Pic0X0 N :=
  pic0Map (heckeX0Transpose N p) (fun _ hD => heckeX0Transpose_mem_divisorsDegZero N p hD)
    (fun _ hD => heckeX0Transpose_principal N p hD)

/-- **$w_N T(p) w_N = T(p)^{\mathsf t}$ on $J_0(N)(\mathbb Q) = \mathrm{Pic}^0(X_0(N))$.** -/
@[kb "milne2006ec" "Ch. V, §4 and §7, w_N and T(p) on the jacobian J_0(N), pdf pp. 205, 225"]
theorem frickePic0_heckePic0_frickePic0 (N p : ℕ) [NeZero N] [NeZero p] (c : Pic0X0 N) :
    frickePic0 N (heckePic0 N p (frickePic0 N c)) = heckePic0Transpose N p c := by
  induction c using QuotientAddGroup.induction_on with
  | H D =>
    rw [frickePic0, pic0Map_mk, heckePic0_mk, pic0Map_mk, heckePic0Transpose, pic0Map_mk]
    congr 1
    exact Subtype.ext (frickeDiv_heckeX0_frickeDiv N p D.1)

end X0

end NumberFieldKB.ModularCurves
