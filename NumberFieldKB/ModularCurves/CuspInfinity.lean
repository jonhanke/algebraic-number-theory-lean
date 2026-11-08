import NumberFieldKB.ModularCurves.AtkinLehner

/-!
# The cusp $\infty$ of $X_0(N)$ over $\mathbb Q$: $q$-expansions as a place

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf pp. 190–196): the cusp $\infty$ of $X_0(N)$, with
local parameter $q = e^{2\pi i z}$ ($\Gamma_0(N)$ contains $\begin{pmatrix}1&1\\0&1\end{pmatrix}$, so the width is 1).

* `qMer N`: the functions $f$ on $\mathbb H$ with $\delta^n f$ holomorphic with a $q$-expansion for some $n$,
  $\delta = \Delta(z)\Delta(Nz)$; a subring containing $j$ and $j_N$. `qMerHom N` sends $f$ to its Laurent expansion in
  $q$ (in `LaurentSeries ℂ`); it is an injective ring map (`qMerHom_injective`).
* `qSeriesPoly N G` $= G(J, J_N)$ for the Laurent expansions $J$, $J_N$ of $j$, $j_N$, and
  **`qSeriesPoly_eq_zero_iff`**: $G(J, J_N) = 0 \iff G(j, j_N) = 0$ on $\mathbb H$.
* **`qExpX0 N`**: the field embedding $\mathbb Q(X_0(N)) \to \mathbb C((q))$, and **`cuspInf N`**, the place of
  the order in $q$: $\operatorname{ord}_\infty(1/j) = 1$, $\operatorname{ord}_\infty(1/j_N) = N$
  (from Mathlib's `discriminant_qExpansion_order`).
* `substN`: $q \mapsto q^N$; $z \mapsto z$ and $z \mapsto Nz$ send $\infty$ to the cusp of $X(1)$.
* **`cusp0 N`** $= w_N(\infty)$, with $\operatorname{ord}_0(1/j) = N$; **`ramIndex_cuspInf`** ($e = 1$) and
  **`ramIndex_cusp0`** ($e = N$) for $X_0(N) \to X(1)$, and `cuspInf_ne_cusp0` for $N > 1$.

Not done: the other cusps $a/c$ with $1 < c < N$, $c \mid N$ (their widths), and residue degrees at the cusps.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Complex ModularForm
open scoped MatrixGroups WithZero

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC NumberFieldKB.MilneEC.V

local notation "Δ" => ModularForm.discriminant

/-! ### $q$-expansions of products and sums -/

namespace IsQExp

theorem zero : IsQExp (0 : ℍ → ℂ) := by simpa using one.smul 0

theorem neg {f : ℍ → ℂ} (hf : IsQExp f) : IsQExp (-f) := by simpa using hf.smul (-1)

theorem const (c : ℂ) : IsQExp (fun _ : ℍ => c) := by
  have := one.smul c
  convert this using 1
  funext z
  simp

theorem qExpansion_mul {f g : ℍ → ℂ} (hf : IsQExp f) (hg : IsQExp g) :
    qExpansion 1 (f * g) = qExpansion 1 f * qExpansion 1 g :=
  UpperHalfPlane.qExpansion_mul hf.analytic hg.analytic

theorem qExpansion_add {f g : ℍ → ℂ} (hf : IsQExp f) (hg : IsQExp g) :
    qExpansion 1 (f + g) = qExpansion 1 f + qExpansion 1 g :=
  UpperHalfPlane.qExpansion_add hf.analytic hg.analytic

theorem qExpansion_eq_zero_iff {f : ℍ → ℂ} (hf : IsQExp f) : qExpansion 1 f = 0 ↔ f = 0 :=
  UpperHalfPlane.qExpansion_eq_zero_iff one_pos hf.periodic hf.mdiff hf.bounded

end IsQExp

/-- The Laurent series of a function with a $q$-expansion. -/
noncomputable def qHat (f : ℍ → ℂ) : LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 f)

theorem qHat_mul {f g : ℍ → ℂ} (hf : IsQExp f) (hg : IsQExp g) : qHat (f * g) = qHat f * qHat g := by
  rw [qHat, hf.qExpansion_mul hg, map_mul]; rfl

theorem qHat_add {f g : ℍ → ℂ} (hf : IsQExp f) (hg : IsQExp g) : qHat (f + g) = qHat f + qHat g := by
  rw [qHat, hf.qExpansion_add hg, map_add]; rfl

theorem qHat_one : qHat 1 = 1 := by rw [qHat, qExpansion_one, map_one]

theorem qHat_pow {f : ℍ → ℂ} (hf : IsQExp f) (n : ℕ) : qHat (f ^ n) = qHat f ^ n := by
  induction n with
  | zero => simpa using qHat_one
  | succ n ih => rw [pow_succ, qHat_mul (hf.pow n) hf, ih, pow_succ]

theorem qHat_eq_zero_iff {f : ℍ → ℂ} (hf : IsQExp f) : qHat f = 0 ↔ f = 0 := by
  rw [qHat, ← hf.qExpansion_eq_zero_iff]
  exact ⟨fun h => HahnSeries.ofPowerSeries_injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

/-! ### The ring of functions meromorphic at $i\infty$ with poles only where $\delta$ vanishes -/

variable (N : ℕ)

/-- $A = E_4^3$. -/
noncomputable abbrev cubeE4 : ℍ → ℂ := (E₄ : ℍ → ℂ) ^ 3

/-- $D = \Delta$. -/
noncomputable abbrev discFun : ℍ → ℂ := fun z => Δ z

/-- $\delta = \Delta(z)\,\Delta(Nz)$. -/
noncomputable abbrev deltaN : ℍ → ℂ := discFun * scaleN N discFun

variable {N}

theorem isQExp_cubeE4 : IsQExp cubeE4 := (IsRatQExp.E4.pow 3).toIsQExp

theorem isQExp_discFun : IsQExp discFun := IsRatQExp.disc.toIsQExp

section QMerSec

variable (hN : 1 ≤ N)
include hN

theorem isQExp_deltaN : IsQExp (deltaN N) := isQExp_discFun.mul (isQExp_discFun.scaleN hN)

omit hN in
theorem deltaN_ne_zero (z : ℍ) : deltaN N z ≠ 0 :=
  mul_ne_zero (ModularForm.discriminant_ne_zero z) (ModularForm.discriminant_ne_zero _)

theorem qHat_deltaN_ne_zero : qHat (deltaN N) ≠ 0 := by
  rw [Ne, qHat_eq_zero_iff (isQExp_deltaN hN)]
  intro h
  exact deltaN_ne_zero (UpperHalfPlane.I) (congrFun h _)

omit hN

/-- The functions $f$ with $\delta^n f$ having a $q$-expansion for some $n$. -/
def qMer (N : ℕ) (hN : 1 ≤ N) : Subring (ℍ → ℂ) where
  carrier := {f | ∃ n : ℕ, IsQExp (deltaN N ^ n * f)}
  mul_mem' := by
    rintro f g ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : deltaN N ^ (n + m) * (f * g) = (deltaN N ^ n * f) * (deltaN N ^ m * g) := by ring
    rw [this]
    exact hn.mul hm
  one_mem' := ⟨0, by simpa using IsQExp.one⟩
  add_mem' := by
    rintro f g ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : deltaN N ^ (n + m) * (f + g) =
        deltaN N ^ m * (deltaN N ^ n * f) + deltaN N ^ n * (deltaN N ^ m * g) := by ring
    rw [this]
    exact (((isQExp_deltaN hN).pow m).mul hn).add (((isQExp_deltaN hN).pow n).mul hm)
  zero_mem' := ⟨0, by simpa using IsQExp.zero⟩
  neg_mem' := by
    rintro f ⟨n, hn⟩
    exact ⟨n, by simpa [mul_neg] using hn.neg⟩

include hN

/-- The Laurent expansion is well defined: $\hat q(\delta^n f)/\hat q(\delta)^n$ does not depend on $n$. -/
theorem qHat_div_eq {f : ℍ → ℂ} {n m : ℕ} (hn : IsQExp (deltaN N ^ n * f)) (hm : IsQExp (deltaN N ^ m * f)) :
    qHat (deltaN N ^ n * f) / qHat (deltaN N) ^ n = qHat (deltaN N ^ m * f) / qHat (deltaN N) ^ m := by
  have hd := isQExp_deltaN hN
  have h0 := qHat_deltaN_ne_zero hN
  rw [div_eq_div_iff (pow_ne_zero _ h0) (pow_ne_zero _ h0), ← qHat_pow hd, ← qHat_pow hd,
    ← qHat_mul hn (hd.pow m), ← qHat_mul hm (hd.pow n)]
  congr 1
  ring

/-- The Laurent expansion of an element of `qMer N`. -/
noncomputable def qMerFun (f : qMer N hN) : LaurentSeries ℂ :=
  qHat (deltaN N ^ f.2.choose * f.1) / qHat (deltaN N) ^ f.2.choose

theorem qMerFun_eq (f : qMer N hN) {n : ℕ} (hn : IsQExp (deltaN N ^ n * f.1)) :
    qMerFun hN f = qHat (deltaN N ^ n * f.1) / qHat (deltaN N) ^ n :=
  qHat_div_eq hN f.2.choose_spec hn

theorem qMerFun_of_isQExp (f : qMer N hN) (hf : IsQExp f.1) : qMerFun hN f = qHat f.1 := by
  rw [qMerFun_eq hN f (n := 0) (by simpa using hf)]
  simp

/-- **$q$-expansion as a ring map** on `qMer N`. -/
noncomputable def qMerHom : qMer N hN →+* LaurentSeries ℂ where
  toFun := qMerFun hN
  map_one' := by
    rw [qMerFun_of_isQExp hN 1 IsQExp.one]
    exact qHat_one
  map_mul' f g := by
    obtain ⟨n, hn⟩ := f.2
    obtain ⟨m, hm⟩ := g.2
    have hnm : IsQExp (deltaN N ^ (n + m) * (f.1 * g.1)) := by
      have : deltaN N ^ (n + m) * (f.1 * g.1) = (deltaN N ^ n * f.1) * (deltaN N ^ m * g.1) := by ring
      rw [this]; exact hn.mul hm
    rw [qMerFun_eq hN (f * g) (n := n + m) hnm, qMerFun_eq hN f hn, qMerFun_eq hN g hm]
    have : deltaN N ^ (n + m) * (f.1 * g.1) = (deltaN N ^ n * f.1) * (deltaN N ^ m * g.1) := by ring
    change qHat (deltaN N ^ (n + m) * (f.1 * g.1)) / _ = _
    rw [this, qHat_mul hn hm, pow_add]
    ring
  map_zero' := by
    rw [qMerFun_of_isQExp hN 0 IsQExp.zero]
    change qHat (0 : ℍ → ℂ) = 0
    rw [qHat, qExpansion_zero, map_zero]
  map_add' f g := by
    obtain ⟨n, hn⟩ := f.2
    obtain ⟨m, hm⟩ := g.2
    have hd := isQExp_deltaN hN
    have h0 := qHat_deltaN_ne_zero hN
    have e : deltaN N ^ (n + m) * (f.1 + g.1) =
        deltaN N ^ m * (deltaN N ^ n * f.1) + deltaN N ^ n * (deltaN N ^ m * g.1) := by ring
    have h1 : IsQExp (deltaN N ^ m * (deltaN N ^ n * f.1)) := (hd.pow m).mul hn
    have h2 : IsQExp (deltaN N ^ n * (deltaN N ^ m * g.1)) := (hd.pow n).mul hm
    have hnm : IsQExp (deltaN N ^ (n + m) * (f.1 + g.1)) := by rw [e]; exact h1.add h2
    rw [qMerFun_eq hN (f + g) (n := n + m) hnm, qMerFun_eq hN f hn, qMerFun_eq hN g hm]
    change qHat (deltaN N ^ (n + m) * (f.1 + g.1)) / _ = _
    rw [e, qHat_add h1 h2, qHat_mul (hd.pow m) hn, qHat_mul (hd.pow n) hm, qHat_pow hd, qHat_pow hd, pow_add]
    field_simp

theorem qMerHom_injective : Function.Injective (qMerHom hN) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨n, hn⟩ := f.2
  change qMerFun hN f = 0 at hf
  rw [qMerFun_eq hN f hn, div_eq_zero_iff] at hf
  rcases hf with hf | hf
  · rw [qHat_eq_zero_iff hn] at hf
    apply Subtype.ext
    funext z
    have := congrFun hf z
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ (deltaN_ne_zero z))
  · exact absurd (pow_eq_zero_iff'.1 hf).1 (qHat_deltaN_ne_zero hN)

/-! ### $j$ and $j_N$ in `qMer N`, and $G(J, J_N)$ -/

omit hN in
theorem scaleN_discFun_ne_zero : scaleN N discFun ≠ 0 := fun h =>
  ModularForm.discriminant_ne_zero _ (congrFun h UpperHalfPlane.I)

theorem qHat_scaleN_discFun_ne_zero : qHat (scaleN N discFun) ≠ 0 := by
  rw [Ne, qHat_eq_zero_iff (isQExp_discFun.scaleN hN)]
  exact scaleN_discFun_ne_zero

omit hN in
theorem qHat_discFun_ne_zero : qHat discFun ≠ 0 := by
  rw [Ne, qHat_eq_zero_iff isQExp_discFun]
  intro h
  exact ModularForm.discriminant_ne_zero UpperHalfPlane.I (congrFun h _)

omit hN in
theorem deltaN_mul_jFun : deltaN N * jFun = cubeE4 * scaleN N discFun := by
  funext z
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [← jFun_mul_disc]
  ring

omit hN in
theorem deltaN_mul_jN : deltaN N * jN N = discFun * scaleN N cubeE4 := by
  funext z
  simp only [Pi.mul_apply, Pi.pow_apply, scaleN, jN]
  rw [← jFun_mul_disc]
  ring

theorem isQExp_delta_jFun : IsQExp (deltaN N ^ 1 * jFun) := by
  rw [pow_one, deltaN_mul_jFun]; exact isQExp_cubeE4.mul (isQExp_discFun.scaleN hN)

theorem isQExp_delta_jN : IsQExp (deltaN N ^ 1 * jN N) := by
  rw [pow_one, deltaN_mul_jN]; exact isQExp_discFun.mul (isQExp_cubeE4.scaleN hN)

/-- $j \in$ `qMer N`. -/
noncomputable def jMer : qMer N hN := ⟨jFun, 1, isQExp_delta_jFun hN⟩

/-- $j_N \in$ `qMer N`. -/
noncomputable def jNMer : qMer N hN := ⟨jN N, 1, isQExp_delta_jN hN⟩

/-- The constants. -/
noncomputable def constMer : ℚ →+* qMer N hN :=
  ((Pi.constRingHom ℍ ℂ).comp (algebraMap ℚ ℂ)).codRestrict (qMer N hN) fun c =>
    ⟨0, by rw [pow_zero, one_mul]; exact IsQExp.const _⟩

/-- $G \mapsto G(j, j_N)$ into `qMer N`. -/
noncomputable def evalMer : ℚ[X][X] →+* qMer N hN :=
  eval₂RingHom (eval₂RingHom (constMer hN) (jMer hN)) (jNMer hN)

theorem subtype_evalMer : (qMer N hN).subtype.comp (evalMer hN) = evalJJNRat N := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · exact RingHom.ext_rat _ _
    · simp [evalMer, evalJJNHom, jMer]
  · simp [evalMer, evalJJNHom, jNMer]

/-- The Laurent expansion $J = E_4^3/\Delta$ of $j$. -/
noncomputable def jSer : LaurentSeries ℂ := qHat cubeE4 / qHat discFun

/-- The Laurent expansion $J_N$ of $j_N$. -/
noncomputable def jNSer (N : ℕ) : LaurentSeries ℂ := qHat (scaleN N cubeE4) / qHat (scaleN N discFun)

theorem qMerHom_jMer : qMerHom hN (jMer hN) = jSer := by
  change qMerFun hN (jMer hN) = _
  rw [qMerFun_eq hN (jMer hN) (isQExp_delta_jFun hN)]
  change qHat (deltaN N ^ 1 * jFun) / _ = _
  rw [pow_one, pow_one, deltaN_mul_jFun, qHat_mul isQExp_cubeE4 (isQExp_discFun.scaleN hN),
    qHat_mul isQExp_discFun (isQExp_discFun.scaleN hN), jSer]
  have h1 := qHat_scaleN_discFun_ne_zero hN
  have h2 := qHat_discFun_ne_zero
  field_simp

theorem qMerHom_jNMer : qMerHom hN (jNMer hN) = jNSer N := by
  change qMerFun hN (jNMer hN) = _
  rw [qMerFun_eq hN (jNMer hN) (isQExp_delta_jN hN)]
  change qHat (deltaN N ^ 1 * jN N) / _ = _
  rw [pow_one, pow_one, deltaN_mul_jN, qHat_mul isQExp_discFun (isQExp_cubeE4.scaleN hN),
    qHat_mul isQExp_discFun (isQExp_discFun.scaleN hN), jNSer]
  have h1 := qHat_scaleN_discFun_ne_zero hN
  have h2 := qHat_discFun_ne_zero
  field_simp

/-- $G \mapsto G(J, J_N)$, the Laurent expansion of $G(j, j_N)$. -/
noncomputable def qSeriesPoly : ℚ[X][X] →+* LaurentSeries ℂ := (qMerHom hN).comp (evalMer hN)

theorem qSeriesPoly_C_X : qSeriesPoly hN (C X) = jSer := by
  rw [qSeriesPoly, RingHom.comp_apply, ← qMerHom_jMer hN]
  congr 1
  simp [evalMer]

theorem qSeriesPoly_X : qSeriesPoly hN X = jNSer N := by
  rw [qSeriesPoly, RingHom.comp_apply, ← qMerHom_jNMer hN]
  congr 1
  simp [evalMer]

/-- **$G(J, J_N) = 0$ iff $G(j, j_N) = 0$ on $\mathbb H$.** -/
theorem qSeriesPoly_eq_zero_iff (G : ℚ[X][X]) : qSeriesPoly hN G = 0 ↔ evalJJNRat N G = 0 := by
  rw [qSeriesPoly, RingHom.comp_apply, map_eq_zero_iff _ (qMerHom_injective hN), ← subtype_evalMer hN,
    RingHom.comp_apply]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

end QMerSec

/-! ### Orders of Laurent expansions -/

/-- The valuation of a Laurent series whose first nonzero coefficient is in degree $n \ge 0$. -/
theorem valuation_ofPowerSeries {F : PowerSeries ℂ} {n : ℕ} (hn : PowerSeries.coeff n F ≠ 0)
    (hlt : ∀ i < n, PowerSeries.coeff i F = 0) :
    Valued.v (HahnSeries.ofPowerSeries ℤ ℂ F) = WithZero.exp (-(n : ℤ)) := by
  have hle : Valued.v (HahnSeries.ofPowerSeries ℤ ℂ F) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
    intro m hm
    rcases lt_or_ge m 0 with h0 | h0
    · rw [HahnSeries.ofPowerSeries_apply]
      rw [HahnSeries.embDomain_of_notMem_range]
      rintro ⟨k, hk⟩
      have : (0 : ℤ) ≤ k := by exact_mod_cast Nat.zero_le k
      simp at hk
      omega
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
      rw [HahnSeries.ofPowerSeries_apply_coeff]
      exact hlt k (by exact_mod_cast hm)
  have hnot : ¬ Valued.v (HahnSeries.ofPowerSeries ℤ ℂ F) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
    rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
    intro h
    apply hn
    have := h n (by omega)
    rwa [HahnSeries.ofPowerSeries_apply_coeff] at this
  have hne : Valued.v (HahnSeries.ofPowerSeries ℤ ℂ F) ≠ 0 := by
    intro h0
    apply hnot
    rw [h0]
    exact zero_le
  rw [← WithZero.exp_log hne] at hle hnot ⊢
  rw [WithZero.exp_le_exp] at hle
  rw [WithZero.exp_le_exp] at hnot
  congr 1
  omega

theorem coeff_qExpansion_cubeE4_zero : PowerSeries.coeff 0 (qExpansion 1 cubeE4) = 1 := by
  have h := (IsQExp.of_modularForm E₄)
  have e : qExpansion 1 cubeE4 = qExpansion 1 (E₄ : ℍ → ℂ) ^ 3 := by
    rw [cubeE4, pow_succ, pow_succ, pow_one, (h.mul h).qExpansion_mul h, h.qExpansion_mul h]
    ring
  rw [e, PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, E4_coeff]
  simp

theorem valuation_qHat_cubeE4 : Valued.v (qHat cubeE4) = 1 := by
  have := valuation_ofPowerSeries (F := qExpansion 1 cubeE4) (n := 0)
    (by rw [coeff_qExpansion_cubeE4_zero]; exact one_ne_zero) (fun i hi => absurd hi (Nat.not_lt_zero i))
  rw [qHat, this]
  rfl

theorem valuation_qHat_discFun : Valued.v (qHat discFun) = WithZero.exp (-1 : ℤ) := by
  have hord : (qExpansion 1 discFun).order = 1 := ModularForm.discriminant_qExpansion_order
  obtain ⟨h1, h2⟩ := PowerSeries.order_eq_nat.1 hord
  rw [qHat, valuation_ofPowerSeries h1 h2]
  rfl

/-- The $q$-expansion of $f(Nz)$: the coefficient of $q^n$ is that of $q^{n/N}$ in $f$ if $N \mid n$, else $0$. -/
theorem qExpansion_scaleN_coeff (hN : 1 ≤ N) {f : ℍ → ℂ} (hf : IsQExp f) (n : ℕ) :
    (qExpansion 1 (scaleN N f)).coeff n = dilateCoeff N (fun k => (qExpansion 1 f).coeff k) n := by
  have hsum : ∀ τ : ℍ, HasSum (fun m => dilateCoeff N (fun k => (qExpansion 1 f).coeff k) m •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (scaleN N f τ) := by
    intro τ
    have h0 := hasSum_qExpansion one_pos hf.periodic hf.mdiff hf.bounded (ofComplex ((N : ℂ) * τ))
    rw [qParam_mul hN] at h0
    show HasSum _ (f (ofComplex ((N : ℂ) * τ)))
    have hinj : Function.Injective (fun m : ℕ => N * m) := fun a b hab =>
      Nat.eq_of_mul_eq_mul_left (by omega) hab
    rw [← hinj.hasSum_iff]
    · convert h0 using 1
      funext m
      simp only [Function.comp_apply, dilateCoeff, dvd_mul_right, ite_true,
        Nat.mul_div_cancel_left _ (by omega : 0 < N), ← pow_mul]
    · intro x hx
      have hnd : ¬ N ∣ x := by
        rintro ⟨k, rfl⟩
        exact hx ⟨k, rfl⟩
      simp only [dilateCoeff, hnd, ite_false, zero_smul]
  exact (qExpansion_coeff_unique' (hf.scaleN hN).analytic hsum n).symm

theorem valuation_qHat_scaleN_cubeE4 (hN : 1 ≤ N) : Valued.v (qHat (scaleN N cubeE4)) = 1 := by
  have h0 : PowerSeries.coeff 0 (qExpansion 1 (scaleN N cubeE4)) ≠ 0 := by
    rw [qExpansion_scaleN_coeff hN isQExp_cubeE4]
    simp only [dilateCoeff, dvd_zero, ite_true, Nat.zero_div]
    rw [coeff_qExpansion_cubeE4_zero]
    exact one_ne_zero
  rw [qHat, valuation_ofPowerSeries h0 (fun i hi => absurd hi (Nat.not_lt_zero i))]
  rfl

theorem valuation_qHat_scaleN_discFun (hN : 1 ≤ N) :
    Valued.v (qHat (scaleN N discFun)) = WithZero.exp (-(N : ℤ)) := by
  obtain ⟨h1, h2⟩ := PowerSeries.order_eq_nat.1 (ModularForm.discriminant_qExpansion_order)
  have hc : PowerSeries.coeff N (qExpansion 1 (scaleN N discFun)) ≠ 0 := by
    rw [qExpansion_scaleN_coeff hN isQExp_discFun]
    simp only [dilateCoeff, dvd_refl, ite_true, Nat.div_self (by omega : 0 < N)]
    exact h1
  have hlt : ∀ i < N, PowerSeries.coeff i (qExpansion 1 (scaleN N discFun)) = 0 := by
    intro i hi
    rw [qExpansion_scaleN_coeff hN isQExp_discFun]
    simp only [dilateCoeff]
    split_ifs with hdvd
    · have : i / N = 0 := Nat.div_eq_of_lt hi
      rw [this]
      exact h2 0 one_pos
    · rfl
  rw [qHat, valuation_ofPowerSeries hc hlt]

theorem valuation_jSer : Valued.v jSer = WithZero.exp (1 : ℤ) := by
  rw [jSer, map_div₀, valuation_qHat_cubeE4, valuation_qHat_discFun, one_div, ← WithZero.exp_neg, neg_neg]

theorem valuation_jNSer (hN : 1 ≤ N) : Valued.v (jNSer N) = WithZero.exp (N : ℤ) := by
  rw [jNSer, map_div₀, valuation_qHat_scaleN_cubeE4 hN, valuation_qHat_scaleN_discFun hN, one_div,
    ← WithZero.exp_neg, neg_neg]

/-! ### The $q$-expansion of $\mathbb Q(X_0(N))$ and the cusp $\infty$ -/

section X0

variable (N) [NeZero N]

/-- $\mathbb Q[X, Y]/(F_N) \to \mathbb C((q))$, $X \mapsto J$, $Y \mapsto J_N$. -/
noncomputable def qExpCoord : coordRingX0 N →+* LaurentSeries ℂ :=
  Ideal.Quotient.lift _ (qSeriesPoly (one_le_neZero N)) fun G hG => by
    rw [qSeriesPoly_eq_zero_iff]
    have : G ∈ RingHom.ker (evalJJNRat N) := by rw [ker_evalJJNRat_modPoly]; exact hG
    exact this

variable {N}

theorem qExpCoord_mk (G : ℚ[X][X]) :
    qExpCoord N (Ideal.Quotient.mk _ G) = qSeriesPoly (one_le_neZero N) G := rfl

theorem qExpCoord_injective : Function.Injective (qExpCoord N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [qExpCoord_mk, qSeriesPoly_eq_zero_iff] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have : G ∈ RingHom.ker (evalJJNRat N) := hx
  rwa [ker_evalJJNRat_modPoly] at this

variable (N)

/-- **The $q$-expansion of $\mathbb Q(X_0(N))$**: the field embedding into $\mathbb C((q))$ with $j \mapsto J$,
$j_N \mapsto J_N$ (the expansion at the cusp $\infty$). -/
@[kb "milne2006ec" "Ch. V, §2, q-expansions of modular functions at the cusp ∞ (running text), pdf pp. 190-192"]
noncomputable def qExpX0 : X0 N →+* LaurentSeries ℂ :=
  letI : Algebra (coordRingX0 N) (X0 N) := (coordToX0 (prop2_4' N)).toAlgebra
  haveI := isFractionRing_coordToX0 (prop2_4' N)
  IsFractionRing.lift (A := coordRingX0 N) (K := X0 N) (g := qExpCoord N) (qExpCoord_injective (N := N))

variable {N}

theorem qExpX0_coordToX0 (x : coordRingX0 N) : qExpX0 N (coordToX0 (prop2_4' N) x) = qExpCoord N x := by
  let : Algebra (coordRingX0 N) (X0 N) := (coordToX0 (prop2_4' N)).toAlgebra
  have := isFractionRing_coordToX0 (prop2_4' N)
  have h := IsFractionRing.lift_algebraMap (A := coordRingX0 N) (K := X0 N) (g := qExpCoord N)
    (qExpCoord_injective (N := N)) x
  rw [RingHom.algebraMap_toAlgebra] at h
  exact h

theorem qExpX0_jX0 : qExpX0 N (jX0 (prop2_4' N)) = jSer := by
  rw [jX0, qExpX0_coordToX0, qExpCoord_mk, qSeriesPoly_C_X]

theorem qExpX0_jNX0 : qExpX0 N (jNX0 (prop2_4' N)) = jNSer N := by
  rw [jNX0, qExpX0_coordToX0, qExpCoord_mk, qSeriesPoly_X]

variable (N)

/-- The valuation of $\mathbb Q(X_0(N))$ at the cusp $\infty$: the order in $q$. -/
noncomputable def cuspVal : Valuation (X0 N) ℤᵐ⁰ := (Valued.v : Valuation (LaurentSeries ℂ) ℤᵐ⁰).comap (qExpX0 N)

variable {N}

theorem cuspVal_apply (x : X0 N) : cuspVal N x = Valued.v (qExpX0 N x) := rfl

theorem cuspVal_inv_jX0 : cuspVal N (jX0 (prop2_4' N))⁻¹ = WithZero.exp (-1 : ℤ) := by
  rw [cuspVal_apply, map_inv₀, qExpX0_jX0, map_inv₀, valuation_jSer, ← WithZero.exp_neg]

theorem cuspVal_inv_jNX0 : cuspVal N (jNX0 (prop2_4' N))⁻¹ = WithZero.exp (-(N : ℤ)) := by
  rw [cuspVal_apply, map_inv₀, qExpX0_jNX0, map_inv₀, valuation_jNSer (one_le_neZero N), ← WithZero.exp_neg]

variable (N)

/-- **The cusp $\infty$ of $X_0(N)$ as a place of $\mathbb Q(X_0(N))$**: the valuation ring of the order in $q$. -/
@[kb "milne2006ec" "Ch. V, §2, the cusp ∞ of X_0(N), with local parameter q (running text), pdf pp. 190-196"]
noncomputable def cuspInf : PrimeDivisor ℚ (X0 N) where
  O := (cuspVal N).valuationSubring
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff, cuspVal_apply]
    have e : qExpX0 N (algebraMap ℚ (X0 N) c) =
        HahnSeries.ofPowerSeries ℤ ℂ (algebraMap ℚ (PowerSeries ℂ) c) :=
      RingHom.congr_fun (RingHom.ext_rat ((qExpX0 N).comp (algebraMap ℚ (X0 N)))
        ((HahnSeries.ofPowerSeries ℤ ℂ).comp (algebraMap ℚ (PowerSeries ℂ)))) c
    rw [e]
    exact (LaurentSeries.val_le_one_iff_eq_coe ℂ _).2 ⟨_, rfl⟩
  isDVR := by
    set v := cuspVal N
    have : IsCyclic v.valueGroup := inferInstance
    have : Nontrivial v.valueGroup := by
      have hx0 : v (jX0 (prop2_4' N))⁻¹ ≠ 0 := by rw [cuspVal_inv_jX0]; exact WithZero.exp_ne_zero
      rw [Subgroup.nontrivial_iff_exists_ne_one]
      refine ⟨Units.mk0 _ hx0, MonoidWithZeroHom.mem_valueGroup _ ⟨_, rfl⟩, fun h => ?_⟩
      have := congrArg Units.val h
      simp only [Units.val_mk0, Units.val_one] at this
      rw [cuspVal_inv_jX0, ← WithZero.exp_zero] at this
      exact absurd (WithZero.exp_injective this) (by norm_num)
    exact Valuation.valuationSubring_isDiscreteValuationRing v

variable {N}

theorem ord_cuspInf {x : X0 N} (hx : x ≠ 0) : (cuspInf N).ord x = ordV (cuspVal N) x := by
  have h0 : (jX0 (prop2_4' N))⁻¹ ≠ 0 := by
    intro h
    have := cuspVal_inv_jX0 (N := N)
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  refine PrimeDivisor.ord_eq_ordV _ _ rfl h0 ?_ hx
  rw [ordV, cuspVal_inv_jX0, WithZero.log_exp, neg_neg]

/-- **$1/j$ is a local parameter at the cusp $\infty$**: $\operatorname{ord}_\infty(1/j) = 1$. -/
theorem ord_cuspInf_inv_jX0 : (cuspInf N).ord (jX0 (prop2_4' N))⁻¹ = 1 := by
  have h0 : (jX0 (prop2_4' N))⁻¹ ≠ 0 := by
    intro h
    have := cuspVal_inv_jX0 (N := N)
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  rw [ord_cuspInf h0, ordV, cuspVal_inv_jX0, WithZero.log_exp, neg_neg]

/-- $\operatorname{ord}_\infty(1/j_N) = N$. -/
theorem ord_cuspInf_inv_jNX0 : (cuspInf N).ord (jNX0 (prop2_4' N))⁻¹ = N := by
  have h0 : (jNX0 (prop2_4' N))⁻¹ ≠ 0 := by
    intro h
    have := cuspVal_inv_jNX0 (N := N)
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  rw [ord_cuspInf h0, ordV, cuspVal_inv_jNX0, WithZero.log_exp, neg_neg]

end X0

/-! ### The substitution $q \mapsto q^N$ -/

theorem ofPowerSeries_coeff_neg (F : PowerSeries ℂ) {m : ℤ} (hm : m < 0) :
    (HahnSeries.ofPowerSeries ℤ ℂ F).coeff m = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  rintro ⟨k, hk⟩
  have : (0 : ℤ) ≤ k := by exact_mod_cast Nat.zero_le k
  simp at hk
  omega

section Subst

variable {M : ℕ}

/-- The order embedding $n \mapsto Mn$ of $\mathbb Z$. -/
def mulEmb (hM : 1 ≤ M) : ℤ ↪o ℤ :=
  ⟨⟨fun n => (M : ℤ) * n, fun a b h => by
      have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      exact mul_left_cancel₀ hM0 h⟩,
    fun {g g'} => by
      have hM0 : (0 : ℤ) < M := by exact_mod_cast (by omega : 0 < M)
      exact mul_le_mul_iff_of_pos_left hM0⟩

/-- $q \mapsto q^M$ on Laurent series. -/
noncomputable def substN (hM : 1 ≤ M) : LaurentSeries ℂ →+* LaurentSeries ℂ :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (M : ℤ)) (mulEmb hM).injective
    (fun _ _ => (mulEmb hM).le_iff_le)

theorem substN_apply (hM : 1 ≤ M) (f : LaurentSeries ℂ) : substN hM f = HahnSeries.embDomain (mulEmb hM) f := rfl

theorem substN_coeff_mul (hM : 1 ≤ M) (f : LaurentSeries ℂ) (n : ℤ) :
    (substN hM f).coeff ((M : ℤ) * n) = f.coeff n := by
  rw [substN_apply]
  exact HahnSeries.embDomain_coeff (f := mulEmb hM) (a := n)

theorem substN_coeff_of_not_dvd (hM : 1 ≤ M) (f : LaurentSeries ℂ) {m : ℤ} (hm : ¬ (M : ℤ) ∣ m) :
    (substN hM f).coeff m = 0 := by
  rw [substN_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨n, rfl⟩
  exact hm ⟨n, rfl⟩

theorem valuation_substN_le_one_iff (hM : 1 ≤ M) (f : LaurentSeries ℂ) :
    Valued.v (substN hM f) ≤ 1 ↔ Valued.v f ≤ 1 := by
  have e : (1 : ℤᵐ⁰) = WithZero.exp (-(0 : ℤ)) := by rw [neg_zero, WithZero.exp_zero]
  rw [e, LaurentSeries.valuation_le_iff_coeff_lt_eq_zero, LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
  have hM0 : (0 : ℤ) < M := by exact_mod_cast (by omega : 0 < M)
  constructor
  · intro h n hn
    rw [← substN_coeff_mul hM]
    exact h _ (by nlinarith)
  · intro h m hm
    by_cases hd : (M : ℤ) ∣ m
    · obtain ⟨n, rfl⟩ := hd
      rw [substN_coeff_mul hM]
      exact h n (by nlinarith)
    · exact substN_coeff_of_not_dvd hM f hd

theorem substN_qHat (hM : 1 ≤ M) {f : ℍ → ℂ} (hf : IsQExp f) : substN hM (qHat f) = qHat (scaleN M f) := by
  ext m
  have hM0 : (0 : ℤ) < M := by exact_mod_cast (by omega : 0 < M)
  by_cases hd : (M : ℤ) ∣ m
  · obtain ⟨n, rfl⟩ := hd
    rw [substN_coeff_mul hM]
    rcases lt_or_ge n 0 with hn | hn
    · rw [qHat, qHat, ofPowerSeries_coeff_neg _ hn, ofPowerSeries_coeff_neg _ (by nlinarith)]
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      have e : (M : ℤ) * (k : ℤ) = ((M * k : ℕ) : ℤ) := by push_cast; ring
      rw [e, qHat, qHat, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        qExpansion_scaleN_coeff hM hf]
      simp only [dilateCoeff, dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ (by omega : 0 < M)]
  · rw [substN_coeff_of_not_dvd hM _ hd]
    rcases lt_or_ge m 0 with hm | hm
    · rw [qHat, ofPowerSeries_coeff_neg _ hm]
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [qHat, HahnSeries.ofPowerSeries_apply_coeff, qExpansion_scaleN_coeff hM hf]
      have hnd : ¬ M ∣ k := fun hk => hd (by exact_mod_cast hk)
      simp only [dilateCoeff, hnd, ite_false]

theorem substN_jSer (hM : 1 ≤ M) : substN hM jSer = jNSer M := by
  rw [jSer, map_div₀, substN_qHat hM isQExp_cubeE4, substN_qHat hM isQExp_discFun, jNSer]

end Subst

theorem scaleN_one (f : ℍ → ℂ) : scaleN 1 f = f := by
  funext z
  simp only [scaleN]
  congr 1
  ext
  rw [coe_ofComplex_mul le_rfl]
  simp

theorem jNSer_one : jNSer 1 = jSer := by rw [jNSer, scaleN_one, scaleN_one, jSer]

/-! ### The cusps $\infty$ and $0$ over the cusp of $X(1)$ -/

section Cusps

variable {N : ℕ} [NeZero N]

theorem one_mul_one_dvd (N : ℕ) : 1 * 1 ∣ N := by simp

theorem mul_one_dvd_self (N : ℕ) : N * 1 ∣ N := by simp

theorem jNElt_mul_one (h : N * 1 ∣ N) : jNElt N (N * 1) h = jNX0 (prop2_4' N) := by
  apply toGerm_injective (N := N)
  rw [toGerm_jNElt, toGerm_jNX0, mul_one]

theorem jNX0_one : jNX0 (prop2_4' 1) = jX0 (prop2_4' 1) := by
  apply toGerm_injective (N := 1)
  rw [toGerm_jNX0, toGerm_jX0]
  congr 1
  funext z
  unfold jN
  congr 1
  ext
  rw [coe_ofComplex_mul le_rfl]
  simp

/-- On $q$-expansions, $z \mapsto z$ from $X_0(N)$ to $X(1)$ is the identity. -/
theorem qExpX0_degeneracy_one (x : X0 1) :
    qExpX0 N (degeneracy 1 N 1 (one_mul_one_dvd N) x) = qExpX0 1 x := by
  have key : (qExpX0 N).comp (degeneracy 1 N 1 (one_mul_one_dvd N)) = qExpX0 1 := by
    apply X0.ringHom_ext
    · rw [RingHom.comp_apply, degeneracy_jX0, jNElt_one, qExpX0_jX0, qExpX0_jX0]
    · rw [RingHom.comp_apply, degeneracy_jNX0]
      rw [show jNElt N (1 * 1) (one_mul_one_dvd N) = jNElt N 1 (dvd_trans (dvd_mul_right 1 1) (one_mul_one_dvd N))
        from rfl, jNElt_one, qExpX0_jX0, qExpX0_jNX0, jNSer_one]
  exact RingHom.congr_fun key x

/-- On $q$-expansions, $z \mapsto Nz$ from $X_0(N)$ to $X(1)$ is $q \mapsto q^N$. -/
theorem qExpX0_degeneracy_N (x : X0 1) :
    qExpX0 N (degeneracy 1 N N (mul_one_dvd_self N) x) = substN (one_le_neZero N) (qExpX0 1 x) := by
  have key : (qExpX0 N).comp (degeneracy 1 N N (mul_one_dvd_self N)) =
      (substN (one_le_neZero N)).comp (qExpX0 1) := by
    apply X0.ringHom_ext
    · rw [RingHom.comp_apply, RingHom.comp_apply, degeneracy_jX0, jNElt_self, qExpX0_jNX0, qExpX0_jX0,
        substN_jSer]
    · rw [RingHom.comp_apply, RingHom.comp_apply, degeneracy_jNX0, jNElt_mul_one, qExpX0_jNX0, qExpX0_jNX0,
        jNSer_one, substN_jSer]
  exact RingHom.congr_fun key x

theorem mem_cuspInf_O (x : X0 N) : x ∈ (cuspInf N).O ↔ Valued.v (qExpX0 N x) ≤ 1 :=
  Valuation.mem_valuationSubring_iff _ _

/-- **The cusp $\infty$ of $X_0(N)$ lies over the cusp of $X(1)$** (for $z \mapsto z$). -/
theorem degeneracyPlace_cuspInf_one : degeneracyPlace (one_mul_one_dvd N) (cuspInf N) = cuspInf 1 := by
  apply PrimeDivisor.ext_O
  ext x
  rw [mem_degeneracyPlace_O, mem_cuspInf_O, mem_cuspInf_O, qExpX0_degeneracy_one]

/-- The cusp $\infty$ of $X_0(N)$ also lies over the cusp of $X(1)$ for $z \mapsto Nz$. -/
theorem degeneracyPlace_cuspInf_N : degeneracyPlace (mul_one_dvd_self N) (cuspInf N) = cuspInf 1 := by
  apply PrimeDivisor.ext_O
  ext x
  rw [mem_degeneracyPlace_O, mem_cuspInf_O, mem_cuspInf_O, qExpX0_degeneracy_N, valuation_substN_le_one_iff]

theorem frickeX0_one (x : X0 1) : frickeX0 (prop2_4' 1) x = x := by
  have key : (frickeX0 (prop2_4' 1)).toRingHom = RingHom.id _ := by
    apply X0.ringHom_ext
    · simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingHom.id_apply]
      rw [frickeX0_jX0, jNX0_one]
    · simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingHom.id_apply]
      rw [frickeX0_jNX0, jNX0_one]
  exact RingHom.congr_fun key x

variable (N) in
/-- **The cusp $0$ of $X_0(N)$**: $w_N(\infty)$. -/
@[kb "milne2006ec" "Ch. V, §2, the cusps ∞ and 0 of X_0(N), exchanged by w_N (running text), pdf pp. 190-196"]
noncomputable abbrev cusp0 : PrimeDivisor ℚ (X0 N) := frickePlace N (cuspInf N)

/-- The cusp $0$ lies over the cusp of $X(1)$. -/
theorem degeneracyPlace_cusp0 : degeneracyPlace (one_mul_one_dvd N) (cusp0 N) = cuspInf 1 := by
  have H := intertwines_fricke (N := 1) (M := N) (d := N) (e := 1) (by ring) (mul_one_dvd_self N)
    (one_mul_one_dvd N)
  rw [cusp0, frickePlace, degeneracyPlace_comapEquiv H, degeneracyPlace_cuspInf_N]
  apply PrimeDivisor.ext_O
  ext x
  rw [PrimeDivisor.mem_comapEquiv_O, frickeX0_one]

theorem inv_jX0_ne_zero : (jX0 (prop2_4' N))⁻¹ ≠ 0 := by
  intro h
  have := cuspVal_inv_jX0 (N := N)
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

/-- $\operatorname{ord}_0(1/j) = N$. -/
theorem ord_cusp0_inv_jX0 : (cusp0 N).ord (jX0 (prop2_4' N))⁻¹ = N := by
  rw [cusp0, frickePlace, PrimeDivisor.ord_comapEquiv _ _ (inv_jX0_ne_zero (N := N)), map_inv₀, frickeX0_jX0,
    ord_cuspInf_inv_jNX0]

/-- $\operatorname{ord}_0(1/j_N) = 1$. -/
theorem ord_cusp0_inv_jNX0 : (cusp0 N).ord (jNX0 (prop2_4' N))⁻¹ = 1 := by
  have h0 : (jNX0 (prop2_4' N))⁻¹ ≠ 0 := by
    intro h
    have := cuspVal_inv_jNX0 (N := N)
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  rw [cusp0, frickePlace, PrimeDivisor.ord_comapEquiv _ _ h0, map_inv₀, frickeX0_jNX0, ord_cuspInf_inv_jX0]

/-- The ramification index over the cusp of $X(1)$ is the order of $1/j$. -/
theorem ramIndex_cusp_eq_ord (Q : PrimeDivisor ℚ (X0 N))
    (hQ : degeneracyPlace (one_mul_one_dvd N) Q = cuspInf 1) :
    ramIndex (one_mul_one_dvd N) (cuspInf 1) Q = Q.ord (jX0 (prop2_4' N))⁻¹ := by
  let := (degeneracy 1 N 1 (one_mul_one_dvd N)).toAlgebra
  have := isScalarTower_rat_degeneracy (one_mul_one_dvd N)
  have := isAlgebraic_degeneracy (one_mul_one_dvd N)
  have : FiniteDimensional (X0 1) (X0 N) := finiteDimensional_degeneracy (one_mul_one_dvd N)
  have h1 := Q.ord_algebraMap_of_comap_eq (cuspInf 1) hQ (inv_jX0_ne_zero (N := 1))
  have e : algebraMap (X0 1) (X0 N) (jX0 (prop2_4' 1))⁻¹ = (jX0 (prop2_4' N))⁻¹ := by
    change degeneracy 1 N 1 (one_mul_one_dvd N) _ = _
    rw [map_inv₀, degeneracy_jX0, jNElt_one]
  rw [e, ord_cuspInf_inv_jX0, mul_one] at h1
  rw [h1]
  rfl

/-- **The cusp $\infty$ of $X_0(N)$ is unramified over $X(1)$**: $e(\infty/\infty) = 1$ (width 1). -/
@[kb "milne2006ec" "Ch. V, §2, the ramification of X_0(N) → X(1) at the cusps (width of a cusp), pdf p. 196"]
theorem ramIndex_cuspInf : ramIndex (one_mul_one_dvd N) (cuspInf 1) (cuspInf N) = 1 := by
  rw [ramIndex_cusp_eq_ord _ degeneracyPlace_cuspInf_one, ord_cuspInf_inv_jX0]

/-- **The cusp $0$ of $X_0(N)$ has ramification index $N$ over the cusp of $X(1)$** (width $N$). -/
@[kb "milne2006ec" "Ch. V, §2, the ramification of X_0(N) → X(1) at the cusps (width of a cusp), pdf p. 196"]
theorem ramIndex_cusp0 : ramIndex (one_mul_one_dvd N) (cuspInf 1) (cusp0 N) = N := by
  rw [ramIndex_cusp_eq_ord _ degeneracyPlace_cusp0, ord_cusp0_inv_jX0]

/-- For $N > 1$ the cusps $\infty$ and $0$ are distinct. -/
theorem cuspInf_ne_cusp0 (hN : 1 < N) : cuspInf N ≠ cusp0 N := by
  intro h
  have h1 := ord_cuspInf_inv_jX0 (N := N)
  rw [h, ord_cusp0_inv_jX0] at h1
  omega

end Cusps

end NumberFieldKB.ModularCurves
