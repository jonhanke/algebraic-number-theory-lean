import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.ZMod.QuotientRing

/-!
# The idelic Dirichlet character of $\mathbb Q$
$\chi$ is a Dirichlet character mod $m\ge1$. We build the Hecke character $\tilde\chi$ of $\mathbb Q$ attached to $\chi$.

* **The rational part of an idele** (`ratPart`): $q(x) = \operatorname{sgn}(x_\infty)\prod_pp^{v_p(x_p)}\in\mathbb Q^\times$,
  a homomorphism $\mathbb A_{\mathbb Q}^\times\to\mathbb Q^\times$ with $q(a) = a$ for $a\in\mathbb Q^\times$
  (`ratPart_unitEmbedding`). Every component of $x/q(x)$ at a finite place is a unit (`valued_unitPart`).
* **The residue mod $m$** (`resMod`): $r(x)\in\mathbb Z/m$ is the reduction, at the primes $p\mid m$ and combined by
  the Chinese remainder theorem (`ZMod.equivPi`), of the components of $x/q(x)$. It is a homomorphism, trivial on
  $\mathbb Q^\times$, and trivial on an open neighbourhood of $1$.
* **The character** $\tilde\chi(x) = \chi(r(x))^{-1}$ (`ideleChar m χ`; the Hecke character `ratDirichletChar` on $C_{\mathbb Q}$ is in `DirichletHecke.lean`). At a
  prime $p\nmid m$ it is unramified with $\tilde\chi_p(\varpi) = \chi(p)$ for every uniformizer $\varpi$, and
  $\tilde\chi^n = 1$ whenever $\chi^n = 1$.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero Filter Topology
open scoped RestrictedProduct Classical

namespace NumberFieldKB.Chebotarev.RatIdele

noncomputable section

/-- The finite places of $\mathbb Q$. -/
abbrev Pl := HeightOneSpectrum (𝓞 ℚ)

/-- The idele group of $\mathbb Q$. -/
abbrev IdQ := IdeleGroup (𝓞 ℚ) ℚ

/-- The prime $p_v$ of the place $v$. -/
abbrev pr (v : Pl) : ℕ := Rat.HeightOneSpectrum.natGenerator v

theorem pr_prime (v : Pl) : (pr v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v

/-! ### Components -/

/-- The component of an idele at a finite place. -/
def compV (v : Pl) : IdQ →* (v.adicCompletion ℚ)ˣ :=
  Units.map
    { toFun := fun a : AdeleRing (𝓞 ℚ) ℚ => a.2 v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp] theorem coe_compV (v : Pl) (x : IdQ) : (compV v x : v.adicCompletion ℚ) = (x : AdeleRing (𝓞 ℚ) ℚ).2 v := rfl

/-- The valuation exponent $v(x_v)\in\mathbb Z$ (so $|x_v|_v = \exp(-v(x_v))$ multiplicatively). -/
def ordV (v : Pl) (x : IdQ) : ℤ := -log (Valued.v (compV v x : v.adicCompletion ℚ))

theorem valued_compV_ne_zero (v : Pl) (x : IdQ) : Valued.v (compV v x : v.adicCompletion ℚ) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (compV v x).ne_zero

theorem valued_compV (v : Pl) (x : IdQ) : Valued.v (compV v x : v.adicCompletion ℚ) = exp (-ordV v x) := by
  rw [ordV, neg_neg, exp_log (valued_compV_ne_zero v x)]

theorem ordV_mul (v : Pl) (x y : IdQ) : ordV v (x * y) = ordV v x + ordV v y := by
  simp only [ordV, map_mul, Units.val_mul, map_mul]
  rw [log_mul (valued_compV_ne_zero v x) (valued_compV_ne_zero v y)]
  ring

theorem ordV_one (v : Pl) : ordV v 1 = 0 := by simp [ordV]

theorem ordV_eq_zero_of_mem {v : Pl} {x : IdQ}
    (hv1 : (x : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ)
    (hv2 : ((x⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ) : ordV v x = 0 := by
  have hv1' : Valued.v (compV v x : v.adicCompletion ℚ) ≤ 1 := hv1
  have hv2' : Valued.v (compV v x⁻¹ : v.adicCompletion ℚ) ≤ 1 := hv2
  have hmul : Valued.v (compV v x : v.adicCompletion ℚ) * Valued.v (compV v x⁻¹ : v.adicCompletion ℚ) = 1 := by
    rw [← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, map_one]
  have heq : Valued.v (compV v x : v.adicCompletion ℚ) = 1 := by
    refine le_antisymm hv1' ?_
    by_contra hlt
    push_neg at hlt
    have h3 : Valued.v (compV v x : v.adicCompletion ℚ) * Valued.v (compV v x⁻¹ : v.adicCompletion ℚ) <
        1 * Valued.v (compV v x⁻¹ : v.adicCompletion ℚ) := by
      have hne : Valued.v (compV v x⁻¹ : v.adicCompletion ℚ) ≠ 0 := valued_compV_ne_zero v _
      exact mul_lt_mul_of_pos_right hlt (zero_lt_iff.mpr hne)
    rw [hmul, one_mul] at h3
    exact absurd hv2' (not_le.mpr h3)
  rw [ordV, heq, log_one, neg_zero]

/-- An idele is a unit at almost every finite place. -/
theorem eventually_ordV_eq_zero (x : IdQ) : ∀ᶠ v in cofinite, ordV v x = 0 := by
  have h1 := (x : AdeleRing (𝓞 ℚ) ℚ).2.2
  have h2 := ((x⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2.2
  filter_upwards [h1, h2] with v hv1 hv2
  exact ordV_eq_zero_of_mem hv1 hv2

/-! ### Valuations of rational numbers -/

theorem natCast_mem_asIdeal_iff (v : Pl) (n : ℕ) : ((n : 𝓞 ℚ) ∈ v.asIdeal) ↔ pr v ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n,
    Ideal.apply_mem_of_equiv_iff]

theorem asIdeal_eq_span (v : Pl) : v.asIdeal = Ideal.span {((pr v : ℕ) : 𝓞 ℚ)} := by
  ext x
  rw [← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)),
    ← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
    ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast]

/-- The embedding $\mathbb Q\to\mathbb Q_v$ through the finite adeles. -/
def cq (v : Pl) : ℚ →+* v.adicCompletion ℚ :=
  (RestrictedProduct.evalRingHom (fun w : Pl => w.adicCompletion ℚ) v).comp
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))

theorem ratCast_eq (v : Pl) (a : ℚ) :
    (a : v.adicCompletion ℚ) = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a v :=
  (eq_ratCast (cq v) a).symm

theorem valued_ratCast (v : Pl) (a : ℚ) : Valued.v (a : v.adicCompletion ℚ) = v.valuation ℚ a := by
  rw [ratCast_eq, FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation']

theorem valued_prime (v : Pl) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Valued.v ((ℓ : ℚ) : v.adicCompletion ℚ) = if pr v = ℓ then exp (-1) else 1 := by
  rw [valued_ratCast, show (ℓ : ℚ) = algebraMap (𝓞 ℚ) ℚ (ℓ : 𝓞 ℚ) by simp, valuation_of_algebraMap]
  split_ifs with h
  · subst h
    exact v.intValuation_singleton (by exact_mod_cast (pr_prime v).ne_zero) (asIdeal_eq_span v)
  · rw [intValuation_eq_one_iff, natCast_mem_asIdeal_iff]
    intro hd
    exact h ((Nat.prime_dvd_prime_iff_eq (pr_prime v) hℓ).mp hd)

theorem valued_natCast_le_one (v : Pl) (n : ℕ) : Valued.v (n : v.adicCompletion ℚ) ≤ 1 := by
  rw [← Rat.cast_natCast, valued_ratCast, show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) by simp,
    valuation_of_algebraMap]
  exact v.intValuation_le_one _

theorem valued_neg_one (v : Pl) : Valued.v ((-1 : ℚ) : v.adicCompletion ℚ) = 1 := by
  rw [valued_ratCast, Valuation.map_neg, map_one]

/-- The place $w_p$ of the prime $p$. -/
def placeOf (p : ℕ) (hp : p.Prime) : Pl := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

theorem pr_placeOf (p : ℕ) (hp : p.Prime) : pr (placeOf p hp) = p := by
  have := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩
  exact congrArg Subtype.val this

theorem eq_placeOf_iff (v : Pl) (p : ℕ) (hp : p.Prime) : v = placeOf p hp ↔ pr v = p := by
  constructor
  · rintro rfl; exact pr_placeOf p hp
  · intro h
    exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).eq_symm_apply.mpr (Subtype.ext h)

theorem pr_injective : Function.Injective pr := fun v w h => by
  have h1 := (eq_placeOf_iff v (pr w) (pr_prime w)).mpr h
  have h2 := (eq_placeOf_iff w (pr w) (pr_prime w)).mpr rfl
  exact h1.trans h2.symm

/-- The absolute norm of the prime of $\mathbb Z$ at $v$ is $p_v$. -/
theorem absNorm_asIdeal (v : Pl) : Ideal.absNorm v.asIdeal = pr v := by
  rw [asIdeal_eq_span, Ideal.absNorm_span_singleton, show ((pr v : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (pr v : ℤ) by simp,
    Algebra.norm_algebraMap, RingOfIntegers.rank, Module.finrank_self, pow_one]
  simp

/-! ### Rational units -/

/-- A homomorphism on $\mathbb Q^\times$ is determined by its values on $-1$ and the primes. -/
theorem ratUnits_hom_ext {G : Type*} [CommGroup G] {f g : ℚˣ →* G} (hneg : f (-1) = g (-1))
    (hpr : ∀ (p : ℕ) (hp : p.Prime), f (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)) =
      g (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero))) : f = g := by
  have hnat : ∀ (n : ℕ) (hn : n ≠ 0), f (Units.mk0 (n : ℚ) (Nat.cast_ne_zero.mpr hn)) =
      g (Units.mk0 (n : ℚ) (Nat.cast_ne_zero.mpr hn)) := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro h; rw [show Units.mk0 ((1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr h) = 1 from Units.ext (by simp),
        map_one, map_one]
    | prime p hp => intro _; exact hpr p hp
    | mul a b ha hb =>
      intro hab
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
      have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
      have e : Units.mk0 ((a * b : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hab) =
          Units.mk0 (a : ℚ) (Nat.cast_ne_zero.mpr ha0) * Units.mk0 (b : ℚ) (Nat.cast_ne_zero.mpr hb0) :=
        Units.ext (by simp)
      rw [e, map_mul, map_mul, ha ha0, hb hb0]
  have hint : ∀ (z : ℤ) (hz : z ≠ 0), f (Units.mk0 (z : ℚ) (Int.cast_ne_zero.mpr hz)) =
      g (Units.mk0 (z : ℚ) (Int.cast_ne_zero.mpr hz)) := by
    intro z hz
    have hn : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
    rcases Int.natAbs_eq z with h | h
    · have e : Units.mk0 (z : ℚ) (Int.cast_ne_zero.mpr hz) = Units.mk0 (z.natAbs : ℚ) (Nat.cast_ne_zero.mpr hn) :=
        Units.ext (by simp only [Units.val_mk0]; rw [← Int.cast_natCast, ← h])
      rw [e, hnat _ hn]
    · have e : Units.mk0 (z : ℚ) (Int.cast_ne_zero.mpr hz) =
          -1 * Units.mk0 (z.natAbs : ℚ) (Nat.cast_ne_zero.mpr hn) :=
        Units.ext (by
          simp only [Units.val_mk0, Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]
          rw [← Int.cast_natCast, ← Int.cast_neg, ← h])
      rw [e, map_mul, map_mul, hneg, hnat _ hn]
  ext a
  have hnum : (a : ℚ).num ≠ 0 := Rat.num_ne_zero.mpr a.ne_zero
  have hden : ((a : ℚ).den : ℤ) ≠ 0 := by exact_mod_cast (a : ℚ).den_ne_zero
  have e : a = Units.mk0 ((a : ℚ).num : ℚ) (Int.cast_ne_zero.mpr hnum) *
      (Units.mk0 (((a : ℚ).den : ℤ) : ℚ) (Int.cast_ne_zero.mpr hden))⁻¹ :=
    Units.ext (by rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, Int.cast_natCast,
      ← div_eq_mul_inv, Rat.num_div_den])
  rw [e, map_mul, map_mul, map_inv, map_inv, hint _ hnum, hint _ hden]

/-! ### The sign at infinity -/

/-- The real embedding of the completion of $\mathbb Q$ at its infinite place. -/
def eInf : (Rat.infinitePlace).Completion →+* ℝ :=
  InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace

theorem continuous_eInf : Continuous eInf :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous

/-- The real number $x_\infty$. -/
def realPart (x : IdQ) : ℝ := eInf ((x : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace)

theorem realPart_one : realPart 1 = 1 := map_one eInf

theorem realPart_mul (x y : IdQ) : realPart (x * y) = realPart x * realPart y := by
  simp only [realPart, Units.val_mul]
  exact map_mul eInf _ _

theorem realPart_ne_zero (x : IdQ) : realPart x ≠ 0 := by
  intro h
  have h1 : realPart x * realPart x⁻¹ = 1 := by
    rw [← realPart_mul, mul_inv_cancel, realPart_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- The sign of $x_\infty$, in $\mathbb Q^\times$. -/
def sgnInf : IdQ →* ℚˣ where
  toFun x := if 0 < realPart x then 1 else -1
  map_one' := by simp [realPart_one]
  map_mul' x y := by
    have hx := realPart_ne_zero x
    have hy := realPart_ne_zero y
    rw [realPart_mul]
    rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
    · simp [mul_pos_of_neg_of_neg hx hy, not_lt.mpr hx.le, not_lt.mpr hy.le]
    · simp [not_lt.mpr (mul_neg_of_neg_of_pos hx hy).le, not_lt.mpr hx.le, hy]
    · simp [not_lt.mpr (mul_neg_of_pos_of_neg hx hy).le, hx, not_lt.mpr hy.le]
    · simp [mul_pos hx hy, hx, hy]

/-! ### The rational part -/

/-- $p_v$ as a unit of $\mathbb Q$. -/
def prU (v : Pl) : ℚˣ := Units.mk0 (pr v : ℚ) (by exact_mod_cast (pr_prime v).ne_zero)

/-- The factor $p_v^{v(x_v)}$. -/
def ratFactor (x : IdQ) (v : Pl) : ℚˣ := prU v ^ ordV v x

theorem mulSupport_ratFactor_finite (x : IdQ) : (Function.mulSupport (ratFactor x)).Finite := by
  refine (eventually_cofinite.mp (eventually_ordV_eq_zero x)).subset fun v hv => ?_
  intro h0
  exact hv (by simp only [ratFactor, h0, zpow_zero])

/-- **The rational part of an idele**: $q(x) = \operatorname{sgn}(x_\infty)\prod_pp^{v_p(x_p)}$. -/
def ratPart : IdQ →* ℚˣ where
  toFun x := sgnInf x * ∏ᶠ v, ratFactor x v
  map_one' := by
    simp [ratFactor, ordV_one]
  map_mul' x y := by
    have e : (fun v => ratFactor (x * y) v) = fun v => ratFactor x v * ratFactor y v := by
      funext v; simp only [ratFactor, ordV_mul, zpow_add]
    rw [map_mul, e, finprod_mul_distrib (mulSupport_ratFactor_finite x) (mulSupport_ratFactor_finite y)]
    exact mul_mul_mul_comm _ _ _ _

/-! ### The rational part of a principal idele -/

/-- The principal idele of $a\in\mathbb Q^\times$. -/
abbrev diag : ℚˣ →* IdQ := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ

theorem coe_compV_diag (v : Pl) (a : ℚˣ) : (compV v (diag a) : v.adicCompletion ℚ) = ((a : ℚ) : v.adicCompletion ℚ) :=
  (ratCast_eq v a).symm

theorem realPart_diag (a : ℚˣ) : realPart (diag a) = (a : ℚ) := by
  let f : ℚ →+* ℝ := eInf.comp ((Pi.evalRingHom _ Rat.infinitePlace).comp (algebraMap ℚ (InfiniteAdeleRing ℚ)))
  exact eq_ratCast f (a : ℚ)

theorem ordV_diag_neg_one (v : Pl) : ordV v (diag (-1)) = 0 := by
  rw [ordV, coe_compV_diag, Units.val_neg, Units.val_one, valued_neg_one, log_one, neg_zero]

theorem ordV_diag_prime (v : Pl) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ordV v (diag (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr hℓ.ne_zero))) = if pr v = ℓ then 1 else 0 := by
  rw [ordV, coe_compV_diag, Units.val_mk0, valued_prime v hℓ]
  split_ifs <;> simp

theorem ratPart_apply (x : IdQ) : ratPart x = sgnInf x * ∏ᶠ v, ratFactor x v := rfl

/-- **$q(a) = a$ on $\mathbb Q^\times$.** -/
theorem ratPart_diag (a : ℚˣ) : ratPart (diag a) = a := by
  have h := ratUnits_hom_ext (f := ratPart.comp diag) (g := MonoidHom.id ℚˣ) ?_ ?_
  · exact DFunLike.congr_fun h a
  · simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, ratPart_apply]
    have h1 : sgnInf (diag (-1)) = -1 := by
      show (if 0 < realPart (diag (-1)) then 1 else -1) = _
      rw [realPart_diag]; norm_num
    have h2 : (fun v => ratFactor (diag (-1)) v) = fun _ => 1 := by
      funext v; rw [ratFactor, ordV_diag_neg_one, zpow_zero]
    rw [h1, h2, finprod_one, mul_one]
  · intro ℓ hℓ
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, ratPart_apply]
    set a := Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr hℓ.ne_zero)
    have h1 : sgnInf (diag a) = 1 := by
      show (if 0 < realPart (diag a) then 1 else -1) = _
      rw [realPart_diag, if_pos (by simp [a, hℓ.pos])]
    set w := placeOf ℓ hℓ
    have h2 : ∀ v, v ≠ w → ratFactor (diag a) v = 1 := by
      intro v hv
      rw [ratFactor, ordV_diag_prime v hℓ, if_neg (fun h => hv ((eq_placeOf_iff v ℓ hℓ).mpr h)), zpow_zero]
    rw [h1, one_mul, finprod_eq_single _ w h2, ratFactor,
      ordV_diag_prime w hℓ, if_pos (pr_placeOf ℓ hℓ : pr w = ℓ), zpow_one]
    exact Units.ext (by simp only [prU, a, Units.val_mk0]; rw [show pr w = ℓ from pr_placeOf ℓ hℓ])

/-! ### The unit part -/

/-- The idele $x/q(x)$: a unit at every finite place. -/
def unitPart : IdQ →* IdQ := (MonoidHom.id IdQ) * (diag.comp ratPart)⁻¹

theorem unitPart_apply (x : IdQ) : unitPart x = x * (diag (ratPart x))⁻¹ := rfl

theorem unitPart_diag (a : ℚˣ) : unitPart (diag a) = 1 := by
  rw [unitPart_apply, ratPart_diag, mul_inv_cancel]

/-- $v(x_v)$ as a homomorphism to `Multiplicative ℤ`. -/
def ordVHom (v : Pl) : IdQ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ordV v x)
  map_one' := by simp [ordV_one]
  map_mul' x y := by simp [ordV_mul, ofAdd_add]

theorem ordV_diag_prU (v w : Pl) : ordV v (diag (prU w)) = if v = w then 1 else 0 := by
  rw [show prU w = Units.mk0 ((pr w : ℕ) : ℚ) (Nat.cast_ne_zero.mpr (pr_prime w).ne_zero) from rfl,
    ordV_diag_prime v (pr_prime w)]
  exact if_congr ⟨fun h => pr_injective h, fun h => h ▸ rfl⟩ rfl rfl

theorem ordV_diag_sgnInf (v : Pl) (x : IdQ) : ordV v (diag (sgnInf x)) = 0 := by
  show ordV v (diag (if 0 < realPart x then 1 else -1)) = 0
  split_ifs
  · rw [map_one, ordV_one]
  · exact ordV_diag_neg_one v

theorem ordV_diag_ratPart (v : Pl) (x : IdQ) : ordV v (diag (ratPart x)) = ordV v x := by
  let φ : ℚˣ →* Multiplicative ℤ := (ordVHom v).comp diag
  have hφ : ∀ a, φ a = Multiplicative.ofAdd (ordV v (diag a)) := fun a => rfl
  have hfac : ∀ w, φ (ratFactor x w) = if v = w then Multiplicative.ofAdd (ordV v x) else 1 := by
    intro w
    rw [ratFactor, map_zpow, hφ, ordV_diag_prU]
    split_ifs with h
    · subst h; rw [← ofAdd_zsmul, smul_eq_mul, mul_one]
    · rw [ofAdd_zero, one_zpow]
  have hprod : φ (∏ᶠ w, ratFactor x w) = Multiplicative.ofAdd (ordV v x) := by
    rw [MonoidHom.map_finprod φ (mulSupport_ratFactor_finite x), finprod_congr hfac,
      finprod_eq_single _ v (fun w hw => if_neg (Ne.symm hw)), if_pos rfl]
  have h1 : φ (ratPart x) = Multiplicative.ofAdd (ordV v x) := by
    rw [ratPart_apply, map_mul, hprod, hφ (sgnInf x), ordV_diag_sgnInf, ofAdd_zero, one_mul]
  have h2 : Multiplicative.ofAdd (ordV v (diag (ratPart x))) = Multiplicative.ofAdd (ordV v x) := h1
  exact Multiplicative.ofAdd.injective h2

theorem ordV_unitPart (v : Pl) (x : IdQ) : ordV v (unitPart x) = 0 := by
  have h := ordV_mul v (unitPart x) (diag (ratPart x))
  rw [unitPart_apply, inv_mul_cancel_right, ordV_diag_ratPart] at h
  rw [unitPart_apply]
  linarith

theorem valued_unitPart (v : Pl) (x : IdQ) : Valued.v (compV v (unitPart x) : v.adicCompletion ℚ) = 1 := by
  rw [valued_compV, ordV_unitPart, neg_zero, exp_zero]

/-! ### Reduction modulo $p^e$ -/

section Red

/-- $\mathbb Q_{w_p}$. -/
abbrev Kp (p : ℕ) (hp : p.Prime) : Type := (placeOf p hp).adicCompletion ℚ

/-- $\mathcal O_{w_p}$. -/
abbrev Op (p : ℕ) (hp : p.Prime) : Type := (placeOf p hp).adicCompletionIntegers ℚ

variable (p : ℕ) (hp : p.Prime) (e : ℕ)


/-- The reduction $\mathcal O_{w_p}\cong\mathbb Z_p\to\mathbb Z/p^e$. -/
def redO : Op p hp →+* ZMod (p ^ e) :=
  haveI := Fact.mk hp
  (PadicInt.toZModPow e).comp
    (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) (⟨p, hp⟩ : Nat.Primes)).symm.toRingEquiv.toRingHom

/-- Reduction $\mathcal O_{w_p}\to\mathbb Z/p^e$, extended by $0$ to $\mathbb Q_{w_p}$. -/
def redP (z : Kp p hp) : ZMod (p ^ e) :=
  if h : Valued.v z ≤ 1 then redO p hp e ⟨z, h⟩ else 0

variable {p hp e}

theorem redP_of_le {z : Kp p hp} (h : Valued.v z ≤ 1) : redP p hp e z = redO p hp e ⟨z, h⟩ := dif_pos h

theorem redP_mul {z z' : Kp p hp} (h : Valued.v z ≤ 1) (h' : Valued.v z' ≤ 1) :
    redP p hp e (z * z') = redP p hp e z * redP p hp e z' := by
  have hzz : Valued.v (z * z') ≤ 1 := by rw [map_mul]; exact mul_le_one' h h'
  rw [redP_of_le h, redP_of_le h', redP_of_le hzz, ← map_mul]
  rfl

theorem redP_natCast (n : ℕ) : redP p hp e (n : Kp p hp) = n := by
  rw [redP_of_le (valued_natCast_le_one _ n)]
  have : (⟨(n : Kp p hp), valued_natCast_le_one _ n⟩ : Op p hp) = (n : Op p hp) := Subtype.ext (by simp)
  rw [this, map_natCast]

theorem redP_one : redP p hp e 1 = 1 := by
  simpa using redP_natCast (p := p) (hp := hp) (e := e) 1

/-- $\mathbb Q_{w_p}$ has $|p| = e^{-1}$. -/
theorem valued_placeOf : Valued.v (p : Kp p hp) = exp (-1) := by
  rw [← Rat.cast_natCast, valued_prime _ hp, if_pos (pr_placeOf p hp)]

/-- **The kernel of the reduction**: $z\equiv1\bmod p^e$ reduces to $1$. -/
theorem redP_eq_one {z : Kp p hp} (h : Valued.v ((z - 1) / (p : Kp p hp) ^ e) ≤ 1) : redP p hp e z = 1 := by
  have hP : Valued.v (p : Kp p hp) = exp (-1) := valued_placeOf
  have hP0 : (p : Kp p hp) ^ e ≠ 0 :=
    pow_ne_zero _ (by intro h0; rw [h0, map_zero] at hP; exact exp_ne_zero hP.symm)
  have hPle : Valued.v ((p : Kp p hp) ^ e) ≤ 1 := by
    rw [map_pow]; exact pow_le_one' (valued_natCast_le_one _ _) _
  have hzt : z = 1 + (p : Kp p hp) ^ e * ((z - 1) / (p : Kp p hp) ^ e) := by
    field_simp
    ring
  have hz1 : Valued.v z ≤ 1 := by
    rw [hzt]
    refine Valuation.map_add_le _ (by rw [map_one]) ?_
    rw [map_mul]
    exact mul_le_one' hPle h
  rw [redP_of_le hz1]
  have : (⟨z, hz1⟩ : Op p hp) = 1 + (p : Op p hp) ^ e * ⟨_, h⟩ := Subtype.ext (by simpa using hzt)
  rw [this, map_add, map_one, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]

end Red

/-! ### The residue modulo $m$ -/

variable (m : ℕ) [NeZero m]

/-- The place $w_p$ for $p\in$ `m.primeFactors`. -/
abbrev placeP (p : m.primeFactors) : Pl := placeOf p (Nat.prime_of_mem_primeFactors p.2)

/-- **The residue $r(x)\in\mathbb Z/m$**: the components of $x/q(x)$ at $p\mid m$ reduced mod $p^{v_p(m)}$, combined
by the Chinese remainder theorem. -/
def resModFun (x : IdQ) : ZMod m :=
  (ZMod.equivPi m (NeZero.ne m)).symm fun p =>
    redP p (Nat.prime_of_mem_primeFactors p.2) (m.factorization p) (compV (placeP m p) (unitPart x)).val

/-- $r$ is a homomorphism. -/
def resMod : IdQ →* ZMod m where
  toFun := resModFun m
  map_one' := by
    rw [resModFun, map_one]
    simp only [map_one, Units.val_one, redP_one]
    exact map_one _
  map_mul' x y := by
    simp only [resModFun]
    rw [← map_mul]
    congr 1
    funext p
    rw [map_mul, map_mul, Units.val_mul, Pi.mul_apply,
      redP_mul (valued_unitPart _ x).le (valued_unitPart _ y).le]

theorem resMod_apply (x : IdQ) : resMod m x = resModFun m x := rfl

theorem resMod_diag (a : ℚˣ) : resMod m (diag a) = 1 := by
  rw [resMod_apply, resModFun, unitPart_diag]
  simp only [map_one, Units.val_one, redP_one]
  exact map_one _

/-- If every component of $x/q(x)$ at the primes $p\mid m$ is $1$, then $r(x) = 1$. -/
theorem resMod_eq_one_of {x : IdQ}
    (h : ∀ p : m.primeFactors, redP p (Nat.prime_of_mem_primeFactors p.2) (m.factorization p)
      (compV (placeP m p) (unitPart x)).val = 1) : resMod m x = 1 := by
  rw [resMod_apply, resModFun]
  have : (fun p : m.primeFactors => redP p (Nat.prime_of_mem_primeFactors p.2) (m.factorization p)
      (compV (placeP m p) (unitPart x)).val) = 1 := funext h
  rw [this, map_one]

/-! ### The character -/

/-- The character $x\mapsto\chi(r(x))^{-1}$ of $\mathbb A_{\mathbb Q}^\times$. -/
def ideleChar (χ : DirichletCharacter ℂ m) : IdQ →* ℂˣ := (χ.toUnitHom.comp (resMod m).toHomUnits)⁻¹

theorem coe_ideleChar (χ : DirichletCharacter ℂ m) (x : IdQ) :
    ((ideleChar m χ x : ℂˣ) : ℂ) = ((χ.toUnitHom ((resMod m).toHomUnits x) : ℂˣ) : ℂ)⁻¹ := by
  simp [ideleChar]

theorem ideleChar_diag (χ : DirichletCharacter ℂ m) (a : ℚˣ) : ideleChar m χ (diag a) = 1 := by
  have h : (resMod m).toHomUnits (diag a) = 1 := Units.ext (by simp [resMod_diag])
  simp [ideleChar, h]

/-! ### Continuity -/

/-- The finite component map of an idele, as a continuous map to the finite adeles. -/
theorem continuous_finPart : Continuous (fun x : IdQ => ((x : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  continuous_snd.comp Units.continuous_val

/-- The finite component map of the inverse of an idele. -/
theorem continuous_finPart_inv :
    Continuous (fun x : IdQ => (((x⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  continuous_snd.comp Units.continuous_coe_inv

theorem continuous_realPart : Continuous realPart :=
  continuous_eInf.comp
    ((continuous_apply Rat.infinitePlace).comp (continuous_fst.comp Units.continuous_val))

/-- Near $1$, the real part is positive. -/
theorem eventually_realPart_pos : ∀ᶠ x in 𝓝 (1 : IdQ), 0 < realPart x :=
  (isOpen_Ioi.preimage continuous_realPart).mem_nhds (by simp [realPart_one])

/-- Near $1$, an idele and its inverse are integral at every finite place. -/
theorem eventually_mem_integers :
    ∀ᶠ x in 𝓝 (1 : IdQ), ∀ v : Pl, ((x : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ ∧
      ((x⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ := by
  have hO : IsOpen {f : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v : Pl, f v ∈ v.adicCompletionIntegers ℚ} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : Pl => v.adicCompletion ℚ)
      (A := fun v : Pl => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
      (fun v => Valued.isOpen_valuationSubring _)
  have h1 : IsOpen {x : IdQ | ∀ v : Pl, (x : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ} :=
    hO.preimage continuous_finPart
  have h2 : IsOpen {x : IdQ | ∀ v : Pl, ((x⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ} :=
    hO.preimage continuous_finPart_inv
  have h3 : (1 : IdQ) ∈ {x : IdQ | ∀ v : Pl, (x : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ} ∩
      {x : IdQ | ∀ v : Pl, ((x⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ} := by
    refine ⟨fun v => ?_, fun v => ?_⟩ <;> exact (one_mem _)
  filter_upwards [(h1.inter h2).mem_nhds h3] with x hx v using ⟨hx.1 v, hx.2 v⟩

/-- Near $1$, $x_{w_p}\equiv1\bmod p^e$. -/
theorem eventually_congr_one (p : ℕ) (hp : p.Prime) (e : ℕ) :
    ∀ᶠ x in 𝓝 (1 : IdQ),
      Valued.v (((((x : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 (placeOf p hp) : Kp p hp) - 1) / (p : Kp p hp) ^ e) ≤ 1 := by
  have hc : Continuous (fun z : Kp p hp => (z - 1) / (p : Kp p hp) ^ e) :=
    (continuous_id.sub continuous_const).div_const _
  have hev : Continuous (fun x : IdQ => ((x : AdeleRing (𝓞 ℚ) ℚ).2 (placeOf p hp) : Kp p hp)) :=
    (RestrictedProduct.continuous_eval (placeOf p hp)).comp continuous_finPart
  have ho : IsOpen {x : IdQ |
      Valued.v (((((x : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 (placeOf p hp) : Kp p hp) - 1) / (p : Kp p hp) ^ e) ≤ 1} :=
    (Valued.isOpen_valuationSubring (Kp p hp)).preimage (hc.comp hev)
  refine ho.mem_nhds ?_
  show Valued.v (((((1 : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 (placeOf p hp) : Kp p hp) - 1) / (p : Kp p hp) ^ e) ≤ 1
  have : (((1 : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 (placeOf p hp) : Kp p hp) = 1 := rfl
  rw [this, sub_self, zero_div, map_zero]
  exact zero_le'

/-- The rational part of an idele with positive real part, integral with integral inverse, is $1$. -/
theorem ratPart_eq_one_of {x : IdQ} (h0 : 0 < realPart x)
    (hx : ∀ v : Pl, (x : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ ∧
      ((x⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ) : ratPart x = 1 := by
  have hs : sgnInf x = 1 := if_pos h0
  have hf : ∀ v, ratFactor x v = 1 := fun v => by
    rw [ratFactor, ordV_eq_zero_of_mem (hx v).1 (hx v).2, zpow_zero]
  rw [ratPart_apply, hs, one_mul, finprod_congr hf, finprod_one]

/-- **$r$ is trivial near $1$**: on $\{x_\infty>0,\ x_v\in\mathcal O_v^\times\ \forall v,\
x_{w_p}\equiv1\bmod p^{v_p(m)}\ \forall p\mid m\}$. -/
theorem eventually_resMod_eq_one : ∀ᶠ x in 𝓝 (1 : IdQ), resMod m x = 1 := by
  have hfin : ∀ᶠ x in 𝓝 (1 : IdQ), ∀ p : m.primeFactors,
      Valued.v (((((x : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 (placeP m p) : Kp p (Nat.prime_of_mem_primeFactors p.2)) - 1) /
        ((p : ℕ) : Kp p (Nat.prime_of_mem_primeFactors p.2)) ^ (m.factorization p)) ≤ 1 :=
    Filter.eventually_all.mpr fun p =>
      eventually_congr_one p (Nat.prime_of_mem_primeFactors p.2) (m.factorization p)
  filter_upwards [eventually_realPart_pos, eventually_mem_integers, hfin] with x h0 hx hp
  refine resMod_eq_one_of m fun p => ?_
  have hq := ratPart_eq_one_of h0 hx
  have hu : unitPart x = x := by rw [unitPart_apply, hq, map_one, inv_one, mul_one]
  rw [hu]
  exact redP_eq_one (hp p)

variable (χ : DirichletCharacter ℂ m)

instance : IsTopologicalGroup IdQ := inferInstanceAs (IsTopologicalGroup (AdeleRing (𝓞 ℚ) ℚ)ˣ)

theorem continuous_ideleChar : Continuous (ideleChar m χ) := by
  refine continuous_of_continuousAt_one (ideleChar m χ) ?_
  have : ∀ᶠ x in 𝓝 (1 : IdQ), ideleChar m χ 1 = ideleChar m χ x := by
    filter_upwards [eventually_resMod_eq_one m] with x hx
    have h : (resMod m).toHomUnits x = 1 := Units.ext (by simp [hx])
    simp [ideleChar, h]
  exact continuousAt_const.congr this

/-! ### Local components at $p\nmid m$ -/

theorem compV_ofAdicCompletion_self (v : Pl) (u : (v.adicCompletion ℚ)ˣ) :
    compV v (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = u := by
  let := Classical.decEq Pl
  refine Units.ext ?_
  rw [coe_compV, IdeleGroup.val_ofAdicCompletion_apply]
  change RestrictedProduct.mulSingle _ v (u : v.adicCompletion ℚ) v = _
  rw [RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_same]

theorem compV_ofAdicCompletion_ne {v w : Pl} (h : w ≠ v) (u : (v.adicCompletion ℚ)ˣ) :
    compV w (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := by
  let := Classical.decEq Pl
  refine Units.ext ?_
  rw [coe_compV, IdeleGroup.val_ofAdicCompletion_apply, Units.val_one]
  change RestrictedProduct.mulSingle _ v (u : v.adicCompletion ℚ) w = _
  rw [RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_of_ne h]

theorem realPart_ofAdicCompletion (v : Pl) (u : (v.adicCompletion ℚ)ˣ) :
    realPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := by
  rw [realPart, IdeleGroup.val_ofAdicCompletion_apply]
  exact map_one eInf

theorem ratPart_ofAdicCompletion (v : Pl) (u : (v.adicCompletion ℚ)ˣ) (k : ℤ)
    (hu : Valued.v (u : v.adicCompletion ℚ) = exp (-k)) :
    ratPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = prU v ^ k := by
  rw [ratPart_apply]
  have hs : sgnInf (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 :=
    if_pos (by rw [realPart_ofAdicCompletion]; exact one_pos)
  have hne : ∀ w, w ≠ v → ratFactor (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) w = 1 := by
    intro w hw
    rw [ratFactor, ordV, compV_ofAdicCompletion_ne hw, Units.val_one, map_one, log_one, neg_zero, zpow_zero]
  rw [hs, one_mul, finprod_eq_single _ v hne, ratFactor, ordV, compV_ofAdicCompletion_self, hu, log_exp, neg_neg]

theorem placeOf_ne {v : Pl} (hv : (pr v).Coprime m) (p : m.primeFactors) : placeP m p ≠ v := by
  intro h
  have h1 : pr v = p := by rw [← h, placeP, pr_placeOf]
  have h2 : pr v ∣ m := by rw [h1]; exact Nat.dvd_of_mem_primeFactors p.2
  exact (pr_prime v).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hv h2)

/-- **Unramified at $p\nmid m$.** -/
theorem ideleChar_unit {v : Pl} (hv : (pr v).Coprime m) (u : (v.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    ideleChar m χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := by
  have hq : ratPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := by
    rw [ratPart_ofAdicCompletion v u 0 (by rw [hu, neg_zero, exp_zero]), zpow_zero]
  have hu' : unitPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u := by
    rw [unitPart_apply, hq, map_one, inv_one, mul_one]
  have hr : resMod m (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := by
    refine resMod_eq_one_of m fun p => ?_
    rw [hu']
    have : compV (placeP m p) (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 :=
      compV_ofAdicCompletion_ne (placeOf_ne m hv p) u
    rw [this, Units.val_one, redP_one]
  have h : (resMod m).toHomUnits (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := Units.ext (by simp [hr])
  simp [ideleChar, h]

theorem valued_prU_inv (w v : Pl) (hwv : w ≠ v) :
    Valued.v ((((prU v)⁻¹ : ℚˣ) : ℚ) : w.adicCompletion ℚ) = 1 := by
  have e : (((prU v)⁻¹ : ℚˣ) : ℚ) = ((pr v : ℕ) : ℚ)⁻¹ := rfl
  rw [e, valued_ratCast, map_inv₀, ← valued_ratCast, valued_prime w (pr_prime v),
    if_neg (fun h => hwv (pr_injective h)), inv_one]

/-- **The value on a uniformizer at $p\nmid m$** is $\chi(p)$. -/
theorem ideleChar_uniformizer {v : Pl} (hv : (pr v).Coprime m) (ϖ : (v.adicCompletion ℚ)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = exp (-1)) :
    ((ideleChar m χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v ϖ) : ℂˣ) : ℂ) = χ (pr v) := by
  obtain ⟨x, hx⟩ : ∃ x, x = IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v ϖ := ⟨_, rfl⟩
  have hq : ratPart x = prU v := by rw [hx, ratPart_ofAdicCompletion v ϖ 1 hϖ, zpow_one]
  have hcomp : ∀ p : m.primeFactors, (compV (placeP m p) (unitPart x) :
      (placeP m p).adicCompletion ℚ) = ((((prU v)⁻¹ : ℚˣ) : ℚ) : _) := by
    intro p
    rw [unitPart_apply, hq, ← map_inv diag (prU v), map_mul, Units.val_mul, hx,
      compV_ofAdicCompletion_ne (placeOf_ne m hv p), Units.val_one, one_mul, coe_compV_diag]
  have hr : resMod m x * (pr v : ZMod m) = 1 := by
    have e : (pr v : ZMod m) = (ZMod.equivPi m (NeZero.ne m)).symm (fun _ => (pr v : ZMod _)) := by
      rw [← map_natCast (ZMod.equivPi m (NeZero.ne m)).symm (pr v)]
      rfl
    rw [e, resMod_apply, resModFun, ← map_mul, ← map_one (ZMod.equivPi m (NeZero.ne m)).symm]
    congr 1
    funext p
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [hcomp p]
    have hA := (valued_prU_inv _ v (placeOf_ne m hv p)).le
    have h1 := redP_mul (p := p) (hp := Nat.prime_of_mem_primeFactors p.2) (e := m.factorization p) hA
      (valued_natCast_le_one _ (pr v))
    have h2 := redP_natCast (p := p) (hp := Nat.prime_of_mem_primeFactors p.2) (e := m.factorization p) (pr v)
    have h3 : ((((prU v)⁻¹ : ℚˣ) : ℚ) : (placeP m p).adicCompletion ℚ) * ((pr v : ℕ) : (placeP m p).adicCompletion ℚ)
        = 1 := by
      have hq : (((prU v)⁻¹ : ℚˣ) : ℚ) * ((pr v : ℕ) : ℚ) = 1 := by
        rw [Units.val_inv_eq_inv_val]
        exact inv_mul_cancel₀ (show ((prU v : ℚˣ) : ℚ) ≠ 0 from (prU v).ne_zero)
      have := congrArg (cq (placeP m p)) hq
      rw [map_mul, map_one, eq_ratCast, eq_ratCast, Rat.cast_natCast] at this
      exact this
    rw [h3, redP_one, h2] at h1
    exact h1.symm
  have hχ : χ (resMod m x) * χ (pr v) = 1 := by rw [← map_mul, hr, map_one]
  rw [← hx, coe_ideleChar, MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits]
  exact inv_eq_of_mul_eq_one_right hχ

/-- **Finite order**: $\tilde\chi^n = 1$ whenever $\chi^n = 1$. -/
theorem ideleChar_pow_eq_one {n : ℕ} (hn : χ ^ n = 1) : ideleChar m χ ^ n = 1 := by
  ext x
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one, coe_ideleChar,
    MulChar.coe_toUnitHom, inv_pow, ← MulChar.pow_apply_coe χ n ((resMod m).toHomUnits x), hn,
    MulChar.one_apply_coe, inv_one]

end

end NumberFieldKB.Chebotarev.RatIdele
