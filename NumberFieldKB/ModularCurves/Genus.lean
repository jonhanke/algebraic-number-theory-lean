import NumberFieldKB.ModularCurves.PlaceFundamental
import NumberFieldKB.TauCetiPort.FieldTheory.FunctionField.Differential.CanonicalDivisor
import NumberFieldKB.TauCetiPort.FieldTheory.FunctionField.Place.OfValuationSubring
import NumberFieldKB.TauCetiPort.FieldTheory.FunctionField.RiemannRoch.RatFunc

/-!
# The genus of a function field of one variable over an arbitrary constant field

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. I, §4 (pdf pp. 41–45): the genus (`MilneEC.genus`, defined by
Riemann's theorem in the form `MilneEC.IsGenus`), divisors of functions, Riemann–Roch. Milne states these for plane
curves and says "the usual proofs apply over arbitrary fields". Here they are proved for every function field `K` of
one variable over any field `k` (Tau Ceti's `TauCeti.IsFunctionField k K`: `K` is finite over `k(x)` for some
transcendental `x`), from the port of Tau Ceti's Riemann–Roch theorem (`NumberFieldKB/TauCetiPort/`, Stichtenoth's
proof, Tau Ceti main `e8758b7`).

The bridge. Milne's places (`MilneEC.PrimeDivisor k K`: a discrete valuation ring of `K` containing `k`) are Tau
Ceti's places (`TauCeti.Place k K`: a normalized discrete valuation trivial on `k`): `primeDivisorEquivPlace`. Under
it the orders, degrees, divisors and the spaces $L(D)$ agree (`PrimeDivisor.ord_eq_place_ord`,
`PrimeDivisor.deg_eq_place_degree`, `divisorEquiv`, `Divisor.L_eq_riemannRochSpace`).

## Main results

* **`isGenus_tauCetiGenus`**: over an exact constant field (`IsIntegrallyClosedIn k K`), `MilneEC.IsGenus k K g` holds
  for `g` Tau Ceti's genus: $L(D)$ is finite-dimensional, $\ell(D) \ge \deg D + 1 - g$, with equality for
  $\deg D > 2g - 2$ (Riemann–Roch with a canonical divisor of degree $2g - 2$).
* **`genus_eq_tauCetiGenus`**: Milne's `genus k K` is that integer (the integer of `IsGenus` is unique).
* **`riemannRoch`**: Milne's Remark 4.7 (a): a divisor `W` of degree $2g - 2$ with
  $\ell(D) = \deg D + 1 - g + \ell(W - D)$ for every `D`.
* **`genus_ratFunc`**: $g(k(t)) = 0$ for every field `k` (Example 4.6 over an arbitrary field).
* **`deg_eq_zero_of_isDivisorOf`**: the divisor of a nonzero function has degree 0 (Milne p. 45; Tau Ceti's
  `TauCeti.Divisor.degree_principal`, the product formula).
-/

open scoped WithZero

noncomputable section

namespace NumberFieldKB.MilneEC

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Places -/

namespace PrimeDivisor

/-- The ring of a prime divisor is a proper subring of `K`. -/
theorem O_ne_top (p : PrimeDivisor k K) : p.O ≠ ⊤ := by
  intro h
  have hu : ¬ IsUnit (⟨p.unif, by rw [h]; trivial⟩ : p.O) := by
    obtain ⟨t, ht, e⟩ := p.exists_uniO
    have : (⟨p.unif, by rw [h]; trivial⟩ : p.O) = t := Subtype.ext e.symm
    rw [this]
    exact ht.not_isUnit
  apply hu
  refine IsUnit.of_mul_eq_one (⟨p.unif⁻¹, by rw [h]; trivial⟩ : p.O) ?_
  exact Subtype.ext (mul_inv_cancel₀ p.unif_ne_zero)

variable (hF : TauCeti.IsFunctionField k K)

/-- Milne's prime divisor as a Tau Ceti place (Stichtenoth, Theorem 1.1.13). -/
def toPlace (p : PrimeDivisor k K) : TauCeti.Place k K :=
  TauCeti.Place.ofValuationSubring hF p.algebraMap_mem p.O_ne_top

@[simp]
theorem integers_toPlace (p : PrimeDivisor k K) : (p.toPlace hF).integers = p.O :=
  TauCeti.Place.integers_ofValuationSubring hF _ _

end PrimeDivisor

/-- A Tau Ceti place as Milne's prime divisor: its valuation ring. -/
def _root_.TauCeti.Place.toPrimeDivisor (P : TauCeti.Place k K) : PrimeDivisor k K where
  O := P.integers
  algebraMap_mem := P.algebraMap_mem_integers
  isDVR := inferInstance

@[simp]
theorem _root_.TauCeti.Place.O_toPrimeDivisor (P : TauCeti.Place k K) : P.toPrimeDivisor.O = P.integers := rfl

variable (hF : TauCeti.IsFunctionField k K)

/-- **Milne's prime divisors are Tau Ceti's places.** -/
def primeDivisorEquivPlace : PrimeDivisor k K ≃ TauCeti.Place k K where
  toFun p := p.toPlace hF
  invFun P := P.toPrimeDivisor
  left_inv p := PrimeDivisor.ext_O (by simp)
  right_inv P := TauCeti.Place.integers_injective (by simp)

@[simp]
theorem primeDivisorEquivPlace_apply (p : PrimeDivisor k K) : primeDivisorEquivPlace hF p = p.toPlace hF := rfl

@[simp]
theorem primeDivisorEquivPlace_symm_apply (P : TauCeti.Place k K) :
    (primeDivisorEquivPlace hF).symm P = P.toPrimeDivisor := rfl

namespace PrimeDivisor

/-- The order of a function at a Tau Ceti place is the order at its valuation ring, read off a valuation. -/
theorem _root_.TauCeti.Place.ord_eq_ordV (P : TauCeti.Place k K) (x : K) : P.ord x = ordV P.valuation x := by
  rw [TauCeti.Place.ord_def, ordV]

/-- **Orders agree.** Milne's $\operatorname{ord}_p$ is the order of Tau Ceti's place `P` with valuation ring
$\mathcal O_p$ (for $x \ne 0$; both are 0 at $x = 0$ by convention, see `ord_eq_place_ord`). -/
theorem _root_.TauCeti.Place.ord_toPrimeDivisor (P : TauCeti.Place k K) (x : K) :
    P.toPrimeDivisor.ord x = P.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [P.ord_zero]
    unfold PrimeDivisor.ord
    split_ifs with H
    · obtain ⟨u, hu⟩ := H.choose_spec
      exfalso
      have h1 : ((u : P.toPrimeDivisor.O) : K) ≠ 0 := by
        intro h0
        exact u.ne_zero (Subtype.ext h0)
      have h2 : P.toPrimeDivisor.unif ^ H.choose ≠ 0 := zpow_ne_zero _ P.toPrimeDivisor.unif_ne_zero
      exact mul_ne_zero h1 h2 hu.symm
    · rfl
  · obtain ⟨π, hπ⟩ := P.exists_isUniformizer
    have hπ0 : π ≠ 0 := by
      intro h0
      rw [h0] at hπ
      simp only [Valuation.IsUniformizer, map_zero] at hπ
      exact (Units.ne_zero _) hπ.symm
    refine PrimeDivisor.ord_eq_ordV _ P.valuation rfl hπ0 ?_ hx |>.trans (P.ord_eq_ordV x).symm
    rw [← P.ord_eq_ordV, ← TauCeti.Place.isUniformizer_iff_ord_eq_one]
    exact hπ

theorem ord_eq_place_ord (p : PrimeDivisor k K) (x : K) : p.ord x = (p.toPlace hF).ord x := by
  conv_lhs => rw [← (primeDivisorEquivPlace hF).left_inv p]
  exact TauCeti.Place.ord_toPrimeDivisor _ x

/-- **Degrees agree**: Milne's degree of the place with ring $\mathcal O_P$ is Tau Ceti's degree of `P`. -/
theorem _root_.TauCeti.Place.deg_toPrimeDivisor (P : TauCeti.Place k K) : P.toPrimeDivisor.deg = P.degree := by
  unfold PrimeDivisor.deg TauCeti.Place.degree
  congr 1

theorem deg_eq_place_degree (p : PrimeDivisor k K) : p.deg = (p.toPlace hF).degree := by
  conv_lhs => rw [← (primeDivisorEquivPlace hF).left_inv p]
  exact TauCeti.Place.deg_toPrimeDivisor _

end PrimeDivisor

/-! ### Divisors -/

/-- Milne's divisors are Tau Ceti's divisors. -/
def divisorEquiv : Divisor k K ≃+ TauCeti.Divisor k K :=
  Finsupp.domCongr (primeDivisorEquivPlace hF)

theorem divisorEquiv_apply' (D : Divisor k K) (P : TauCeti.Place k K) :
    divisorEquiv hF D P = D P.toPrimeDivisor := by
  rw [divisorEquiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, primeDivisorEquivPlace_symm_apply]

theorem divisorEquiv_apply (D : Divisor k K) (p : PrimeDivisor k K) :
    divisorEquiv hF D (p.toPlace hF) = D p := by
  rw [divisorEquiv_apply']
  congr 1
  exact (primeDivisorEquivPlace hF).left_inv p

theorem divisorEquiv_single (p : PrimeDivisor k K) (n : ℤ) :
    divisorEquiv hF (Finsupp.single p n) = Finsupp.single (p.toPlace hF) n := by
  rw [divisorEquiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single, primeDivisorEquivPlace_apply]

theorem Divisor.deg_eq_degree (D : Divisor k K) : D.deg = TauCeti.Divisor.degree (divisorEquiv hF D) := by
  have : (Divisor.deg : Divisor k K →+ ℤ) =
      (TauCeti.Divisor.degree (k := k) (F := K)).comp (divisorEquiv hF).toAddMonoidHom := by
    refine Finsupp.addHom_ext fun p n => ?_
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, divisorEquiv_single,
      TauCeti.Divisor.degree_apply, Divisor.deg, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply,
      smul_eq_mul]
    rw [Finsupp.sum_single_index (by simp), PrimeDivisor.deg_eq_place_degree hF, mul_comm]
  exact DFunLike.congr_fun this D

/-- **The spaces $L(D)$ agree.** -/
theorem Divisor.L_eq_riemannRochSpace (D : Divisor k K) : D.L = TauCeti.riemannRochSpace (divisorEquiv hF D) := by
  ext φ
  show (∀ p : PrimeDivisor k K, φ * p.unif ^ (D p) ∈ p.O) ↔
    ∀ P : TauCeti.Place k K, P.valuation φ ≤ WithZero.exp ((divisorEquiv hF D).coeff P)
  rw [(primeDivisorEquivPlace hF).forall_congr_left]
  refine forall_congr' fun P => ?_
  rw [primeDivisorEquivPlace_symm_apply, TauCeti.AlgebraicGeometry.WeilDivisor.coeff,
    divisorEquiv_apply', TauCeti.Place.O_toPrimeDivisor, TauCeti.Place.mem_integers_iff, map_mul, map_zpow₀]
  set n := D P.toPrimeDivisor
  have hu : P.valuation P.toPrimeDivisor.unif = WithZero.exp (-1) := by
    have h1 := P.toPrimeDivisor.ord_unif
    rw [TauCeti.Place.ord_toPrimeDivisor] at h1
    rw [P.valuation_eq_exp_neg_ord P.toPrimeDivisor.unif_ne_zero, h1]
  rw [hu, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one]
  rcases eq_or_ne φ 0 with rfl | hφ
  · simp
  · rw [P.valuation_eq_exp_neg_ord hφ, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp,
      WithZero.exp_le_exp]
    omega

theorem Divisor.ell_eq_dim (D : Divisor k K) : D.ell = TauCeti.Divisor.dim (divisorEquiv hF D) := by
  rw [Divisor.ell, TauCeti.Divisor.dim_def, Divisor.L_eq_riemannRochSpace hF D]

/-! ### Riemann–Roch and the genus -/

include hF in
/-- **Riemann's theorem with equality in large degree** (Milne, Theorem 4.13, over an arbitrary constant field):
over an exact constant field, Tau Ceti's genus satisfies Milne's `IsGenus`. -/
@[kb "milne2006ec" "Ch. I, Thm. 4.13, pdf p. 45"]
theorem isGenus_tauCetiGenus (hex : IsIntegrallyClosedIn k K) : IsGenus k K (TauCeti.genus k K) := by
  intro D
  refine ⟨?_, ?_, fun hD => ?_⟩
  · rw [Divisor.L_eq_riemannRochSpace hF D]
    exact TauCeti.finiteDimensional_riemannRochSpace hF _
  · rw [Divisor.ell_eq_dim hF, Divisor.deg_eq_degree hF]
    exact TauCeti.Divisor.degree_add_one_sub_genus_le_dim hF _
  · obtain ⟨W, hW⟩ := TauCeti.exists_isRiemannRochDivisor hF hex
    rw [Divisor.ell_eq_dim hF, Divisor.deg_eq_degree hF, hW (divisorEquiv hF D)]
    rw [Divisor.deg_eq_degree hF] at hD
    have hdeg := hW.degree_eq hF hex
    have h0 : TauCeti.Divisor.dim (W - divisorEquiv hF D) = 0 :=
      TauCeti.Divisor.dim_eq_zero_of_degree_neg hF (by rw [map_sub]; omega)
    rw [h0]
    push_cast
    ring

include hF in
/-- A function field has prime divisors of every positive multiple of some degree, so the integer of `IsGenus` is
unique. -/
theorem isGenus_unique {g g' : ℤ} (hg : IsGenus k K g) (hg' : IsGenus k K g') : g = g' := by
  obtain ⟨P⟩ := TauCeti.Place.nonempty hF
  set n : ℤ := 2 * (|g| + |g'|) + 1 with hn_def
  have ha := le_abs_self g
  have ha' := le_abs_self g'
  have hb := abs_nonneg g
  have hb' := abs_nonneg g'
  have hgn : 2 * g - 2 < n := by omega
  have hgn' : 2 * g' - 2 < n := by omega
  set D : Divisor k K := Finsupp.single P.toPrimeDivisor n
  have hdeg1 : 1 ≤ (P.toPrimeDivisor.deg : ℤ) := by
    rw [TauCeti.Place.deg_toPrimeDivisor]
    exact_mod_cast P.one_le_degree_of_isFunctionField hF
  have hD : D.deg = n * P.toPrimeDivisor.deg := by
    simp [D, Divisor.deg, zmultiplesHom_apply]
  have hn : n ≤ D.deg := by
    rw [hD]
    have : 0 ≤ n := by omega
    nlinarith
  have h1 := (hg D).2.2 (by omega)
  have h2 := (hg' D).2.2 (by omega)
  omega

include hF in
/-- **The genus of a function field over an exact constant field** is Tau Ceti's genus (Stichtenoth, Definition
1.4.15). -/
theorem genus_eq_tauCetiGenus (hex : IsIntegrallyClosedIn k K) : genus k K = TauCeti.genus k K := by
  have h : ∃ g, IsGenus k K g := ⟨_, isGenus_tauCetiGenus hF hex⟩
  rw [genus, dite_cond_eq_true (eq_true h)]
  exact isGenus_unique hF h.choose_spec (isGenus_tauCetiGenus hF hex)

include hF in
theorem isGenus_genus (hex : IsIntegrallyClosedIn k K) : IsGenus k K (genus k K) := by
  rw [genus_eq_tauCetiGenus hF hex]
  exact isGenus_tauCetiGenus hF hex

include hF in
theorem genus_nonneg (hex : IsIntegrallyClosedIn k K) : 0 ≤ genus k K := by
  rw [genus_eq_tauCetiGenus hF hex]
  positivity

include hF in
/-- **The Riemann–Roch theorem** (Milne, Remark 4.7 (a), over an arbitrary constant field; Stichtenoth, Theorem
1.5.15): over an exact constant field there is a divisor `W` of degree $2g - 2$ with
$\ell(D) = \deg D + 1 - g + \ell(W - D)$ for every divisor `D`. -/
@[kb "milne2006ec" "Ch. I, Rem. 4.7 (a), pdf p. 41"]
theorem riemannRoch (hex : IsIntegrallyClosedIn k K) :
    ∃ W : Divisor k K, W.deg = 2 * genus k K - 2 ∧
      ∀ D : Divisor k K, (D.ell : ℤ) = D.deg + 1 - genus k K + (W - D).ell := by
  obtain ⟨W, hW⟩ := TauCeti.exists_isRiemannRochDivisor hF hex
  refine ⟨(divisorEquiv hF).symm W, ?_, fun D => ?_⟩
  · rw [Divisor.deg_eq_degree hF, AddEquiv.apply_symm_apply, hW.degree_eq hF hex,
      genus_eq_tauCetiGenus hF hex]
  · rw [Divisor.ell_eq_dim hF, Divisor.ell_eq_dim hF, Divisor.deg_eq_degree hF, map_sub,
      AddEquiv.apply_symm_apply, hW, genus_eq_tauCetiGenus hF hex]

/-- **The projective line has genus 0** (Milne, Example 4.6, over an arbitrary field `k`): $g(k(t)) = 0$. -/
@[kb "milne2006ec" "Ch. I, Ex. 4.6, pdf p. 41"]
theorem genus_ratFunc : genus k (RatFunc k) = 0 := by
  rw [genus_eq_tauCetiGenus (TauCeti.IsFunctionField.ratFunc k) inferInstance, TauCeti.genus_ratFunc]
  rfl

/-! ### Principal divisors -/

/-- The divisor of a function corresponds to Tau Ceti's principal divisor. -/
theorem divisorEquiv_of_isDivisorOf {D : Divisor k K} {h : K} (hD : IsDivisorOf D h) :
    divisorEquiv hF D = TauCeti.Divisor.principal hF (Units.mk0 h hD.1) := by
  refine Finsupp.ext fun P => ?_
  rw [divisorEquiv_apply', hD.2 P.toPrimeDivisor, TauCeti.Place.ord_toPrimeDivisor]
  exact (TauCeti.Divisor.coeff_principal hF (Units.mk0 h hD.1) P).symm

include hF in
/-- **The divisor of a nonzero function has degree 0** (Milne, Ch. I, §4, p. 45, over an arbitrary constant field;
Tau Ceti's `TauCeti.Divisor.degree_principal`, the product formula, Stichtenoth Theorem 1.4.11). -/
@[kb "milne2006ec" "Ch. I, §4, div(h) is a divisor of degree zero, pdf p. 45"]
theorem deg_eq_zero_of_isDivisorOf {D : Divisor k K} {h : K} (hD : IsDivisorOf D h) : D.deg = 0 := by
  rw [Divisor.deg_eq_degree hF, divisorEquiv_of_isDivisorOf hF hD]
  exact TauCeti.Divisor.degree_principal hF _

include hF in
/-- Every nonzero function has a divisor (finitely many zeros and poles). -/
theorem exists_isDivisorOf {h : K} (hh : h ≠ 0) : ∃ D : Divisor k K, IsDivisorOf D h := by
  refine ⟨(divisorEquiv hF).symm (TauCeti.Divisor.principal hF (Units.mk0 h hh)), hh, fun p => ?_⟩
  have := divisorEquiv_apply hF ((divisorEquiv hF).symm (TauCeti.Divisor.principal hF (Units.mk0 h hh))) p
  rw [AddEquiv.apply_symm_apply] at this
  rw [← this, PrimeDivisor.ord_eq_place_ord hF]
  exact TauCeti.Divisor.coeff_principal hF _ _

end NumberFieldKB.MilneEC
