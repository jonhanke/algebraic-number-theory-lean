import NumberFieldKB.MilneEC.Ch5HStar
import NumberFieldKB.ModularCurves.JInjective
import Mathlib.NumberTheory.Modular
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Milne, *Elliptic Curves*, Proposition V.1.7 (compactness): $X(\Gamma)$ is compact

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §1, Proposition 1.7 (pdf p. 186).

**Credit.** The compactness argument is adapted from the author's (unpublished) modular forms library
(`compactSpace_compactifiedQuotient_map_sl2zToPSL2R`): $X(\Gamma)$ is
covered by the images of finitely many translates $r_q \cdot \mathcal D^*$ of the closed fundamental domain with its
cusp, one for each coset $q \in \mathrm{SL}_2(\mathbb Z)/\Gamma$. That proof is written for Tau Ceti's
`Subgroup.CompactifiedQuotient` (a different construction of $\Gamma\backslash\mathbb H^*$, with the cusp charts of a
Riemann surface); it cannot be copied as code, since Tau Ceti is not a dependency here. It is redone for this
repository's $\mathbb H^*$ with Milne's topology (`HStar`, file `Ch5HStar`):

* `continuous_smul_hstar`: every $g \in \mathrm{SL}_2(\mathbb Z)$ acts continuously on $\mathbb H^*$ (half of the
  named running-text statement `HStarTopology`). The preimages of the generating open sets under the generators
  $S$ and $T^n$ are again generating open sets: $T^n$ translates horodisks; $S$ exchanges the neighbourhoods
  $\{\Im z > M\}$ of $\infty$ and the horodisks at $0$, and sends the horodisk of radius $r$ at $a \ne 0$ to the
  horodisk of radius $r/a^2$ at $-1/a$.
* `isCompact_fdStar`: $\mathcal D^* = \mathcal D \cup \{\infty\}$ is compact (an open set containing $\infty$ contains
  some $\{\Im z > M\} \cup \{\infty\}$, `exists_horoInfty_subset`, and the rest is Mathlib's compact truncated
  fundamental domain).
* `compactSpace_xGamma`: **Proposition 1.7, compactness**: $X(\Gamma)$ is compact for $\Gamma$ of finite index.

The Hausdorff half of Proposition 1.7 is proved in `XGammaHausdorff` (`t2Space_xGamma`, and `prop_1_7`); for
$\Gamma = \mathrm{SL}_2(\mathbb Z)$ it also follows from Proposition 1.9 (`prop_1_9_unconditional`: $X(1)$ is homeomorphic to the sphere, so
`t2Space_xGamma_top`).
-/

open UpperHalfPlane hiding I
open Complex Filter Topology Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups OnePoint ModularGroup

namespace NumberFieldKB.MilneEC.V

/-- A point of $\mathbb H$ as a point of $\mathbb H^*$. -/
def HStar.inl (z : ℍ) : HStar := Sum.inl z

/-- A cusp as a point of $\mathbb H^*$. -/
def HStar.cusp (c : OnePoint ℚ) : HStar := Sum.inr c

/-! ### Membership in the generating open sets -/

theorem mem_horoInfty_inl (M : ℝ) (z : ℍ) : HStar.inl z ∈ HStar.horoInfty M ↔ M < z.im := by
  unfold HStar.inl
  constructor
  · rintro (⟨w, hw, h⟩ | h)
    · cases hw; exact h
    · cases h
  · intro h; exact Or.inl ⟨z, rfl, h⟩

theorem mem_horoInfty_inr (M : ℝ) (c : OnePoint ℚ) : HStar.cusp c ∈ HStar.horoInfty M ↔ c = ∞ := by
  unfold HStar.cusp
  constructor
  · rintro (⟨w, hw, h⟩ | h)
    · cases hw
    · cases h; rfl
  · rintro rfl; exact Or.inr rfl

/-- The horodisk condition $|z - (a + ir)| < r$ is $(x - a)^2 + y^2 < 2ry$. -/
theorem horo_iff (z : ℍ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    ‖(z : ℂ) - ((a : ℂ) + r * I)‖ < r ↔ (z.re - a) ^ 2 + z.im ^ 2 < 2 * r * z.im := by
  have hn : ‖(z : ℂ) - ((a : ℂ) + r * I)‖ ^ 2 = (z.re - a) ^ 2 + (z.im - r) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, Complex.I_re, Complex.I_im, sub_im, add_im, mul_im]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  constructor
  · intro h
    have h2 : ‖(z : ℂ) - ((a : ℂ) + r * I)‖ ^ 2 < r ^ 2 := pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
    rw [hn] at h2
    nlinarith
  · intro h
    have h2 : ‖(z : ℂ) - ((a : ℂ) + r * I)‖ ^ 2 < r ^ 2 := by rw [hn]; nlinarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).mp h2

theorem mem_horoDisk_inl (a : ℚ) {r : ℝ} (hr : 0 < r) (z : ℍ) :
    HStar.inl z ∈ HStar.horoDisk a r ↔ (z.re - a) ^ 2 + z.im ^ 2 < 2 * r * z.im := by
  rw [← horo_iff z a hr]
  unfold HStar.inl
  constructor
  · rintro (⟨w, hw, h⟩ | h)
    · cases hw; exact_mod_cast h
    · cases h
  · intro h; exact Or.inl ⟨z, rfl, by exact_mod_cast h⟩

theorem mem_horoDisk_inr (a : ℚ) (r : ℝ) (c : OnePoint ℚ) :
    HStar.cusp c ∈ HStar.horoDisk a r ↔ c = (a : OnePoint ℚ) := by
  unfold HStar.cusp
  constructor
  · rintro (⟨w, hw, h⟩ | h)
    · cases hw
    · cases h; rfl
  · rintro rfl; exact Or.inr rfl

/-! ### The action on $\mathbb H^*$ -/

/-- Case analysis on a point of $\mathbb H^*$: a point of $\mathbb H$ or a cusp. -/
@[elab_as_elim]
theorem HStar.ind {P : HStar → Prop} (inl : ∀ z : ℍ, P (HStar.inl z)) (inr : ∀ c : OnePoint ℚ, P (HStar.cusp c))
    (x : HStar) : P x :=
  Sum.rec (motive := fun x => P x) inl inr x

theorem smul_inl (g : SL(2, ℤ)) (z : ℍ) : g • HStar.inl z = HStar.inl (g • z) := rfl

theorem smul_inr (g : SL(2, ℤ)) (c : OnePoint ℚ) : g • HStar.cusp c = HStar.cusp (g • c) := rfl

theorem smul_onePoint_def (g : SL(2, ℤ)) (c : OnePoint ℚ) : g • c = mapGL ℚ g • c := rfl

theorem continuous_smul_upperHalfPlane (g : SL(2, ℤ)) : Continuous fun z : ℍ => g • z := by
  have : (fun z : ℍ => g • z) = fun z => (mapGL ℝ g) • z := by
    funext z
    rfl
  rw [this]
  exact continuous_const_smul _

/-- The action of $T^n$ on the cusps: $a \mapsto a + n$, $\infty \mapsto \infty$. -/
theorem mapGL_T_zpow_apply (n : ℤ) (i j : Fin 2) :
    ((mapGL ℚ (T ^ n) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j =
      ((!![1, n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
  rw [← coe_T_zpow]
  rfl

theorem T_zpow_smul_coe (n : ℤ) (q : ℚ) : (T ^ n) • (q : OnePoint ℚ) = ((q + n : ℚ) : OnePoint ℚ) := by
  rw [smul_onePoint_def, OnePoint.smul_some_eq_ite]
  simp only [mapGL_T_zpow_apply]
  simp

theorem T_zpow_smul_infty (n : ℤ) : (T ^ n) • (∞ : OnePoint ℚ) = ∞ := by
  rw [smul_onePoint_def, OnePoint.smul_infty_eq_ite]
  simp only [mapGL_T_zpow_apply]
  simp

/-- The action of $S$ on the cusps: $0 \mapsto \infty$, $a \mapsto -1/a$ for $a \ne 0$. -/
theorem S_smul_coe (q : ℚ) : S • (q : OnePoint ℚ) = if q = 0 then ∞ else ((-1 / q : ℚ) : OnePoint ℚ) := by
  rw [smul_onePoint_def, OnePoint.smul_some_eq_ite]
  have e : ∀ i j, ((mapGL ℚ S : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = ((S : SL(2, ℤ)) i j : ℚ) :=
    fun i j => rfl
  simp [e, coe_S]

theorem S_smul_infty : S • (∞ : OnePoint ℚ) = ((0 : ℚ) : OnePoint ℚ) := by
  rw [smul_onePoint_def, OnePoint.smul_infty_eq_ite]
  have e : ∀ i j, ((mapGL ℚ S : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = ((S : SL(2, ℤ)) i j : ℚ) :=
    fun i j => rfl
  simp [e, coe_S]

theorem T_zpow_smul_re (n : ℤ) (z : ℍ) : ((T ^ n) • z).re = z.re + n := by
  rw [modular_T_zpow_smul, vadd_re]; ring

theorem T_zpow_smul_im (n : ℤ) (z : ℍ) : ((T ^ n) • z).im = z.im := by
  rw [modular_T_zpow_smul, vadd_im]

theorem S_smul_coe_upper (z : ℍ) : ((S • z : ℍ) : ℂ) = (-(z : ℂ))⁻¹ := by
  rw [modular_S_smul]

theorem normSq_upper (z : ℍ) : Complex.normSq (z : ℂ) = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.normSq_apply]; simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring

theorem S_smul_re (z : ℍ) : (S • z).re = -z.re / (z.re ^ 2 + z.im ^ 2) := by
  rw [← UpperHalfPlane.coe_re, S_smul_coe_upper, Complex.inv_re, Complex.normSq_neg, normSq_upper, neg_re,
    UpperHalfPlane.coe_re]

theorem S_smul_im (z : ℍ) : (S • z).im = z.im / (z.re ^ 2 + z.im ^ 2) := by
  rw [← UpperHalfPlane.coe_im, S_smul_coe_upper, Complex.inv_im, Complex.normSq_neg, normSq_upper, neg_im,
    UpperHalfPlane.coe_im, neg_neg]

/-! ### Continuity of the action -/

/-- A map of $\mathbb H^*$ is continuous when the preimages of the generating open sets are open. -/
theorem continuous_of_generators {f : HStar → HStar}
    (h1 : ∀ U : Set ℍ, IsOpen U → IsOpen (f ⁻¹' (HStar.inl '' U)))
    (h2 : ∀ M : ℝ, 0 < M → IsOpen (f ⁻¹' HStar.horoInfty M))
    (h3 : ∀ (a : ℚ) (r : ℝ), 0 < r → IsOpen (f ⁻¹' HStar.horoDisk a r)) : Continuous f := by
  rw [continuous_generateFrom_iff]
  rintro s ((⟨U, hU, rfl⟩ | ⟨M, hM, rfl⟩) | ⟨a, r, hr, rfl⟩)
  · exact h1 U hU
  · exact h2 M hM
  · exact h3 a r hr

theorem isOpen_smul_preimage_inl (g : SL(2, ℤ)) {U : Set ℍ} (hU : IsOpen U) :
    IsOpen ((fun x : HStar => g • x) ⁻¹' (HStar.inl '' U)) := by
  have e : (fun x : HStar => g • x) ⁻¹' (HStar.inl '' U) = HStar.inl '' ((fun z : ℍ => g • z) ⁻¹' U) := by
    ext x
    constructor
    · rintro ⟨w, hw, h⟩
      refine ⟨g⁻¹ • w, ?_, ?_⟩
      · show g • (g⁻¹ • w) ∈ U
        rwa [smul_inv_smul]
      · have : HStar.inl (g⁻¹ • w) = g⁻¹ • HStar.inl w := rfl
        have h' : HStar.inl w = g • x := h
        rw [this, h']
        exact inv_smul_smul g x
    · rintro ⟨w, hw, rfl⟩
      exact ⟨g • w, hw, rfl⟩
  rw [e]
  exact isOpen_inl_image (hU.preimage (continuous_smul_upperHalfPlane g))

theorem continuous_T_zpow_smul (n : ℤ) : Continuous fun x : HStar => (T ^ n) • x := by
  refine continuous_of_generators (fun U hU => isOpen_smul_preimage_inl _ hU) (fun M hM => ?_)
    (fun a r hr => ?_)
  · have e : (fun x : HStar => (T ^ n) • x) ⁻¹' HStar.horoInfty M = HStar.horoInfty M := by
      ext x
      induction x using HStar.ind with
      | inl z =>
        simp only [Set.mem_preimage, smul_inl, mem_horoInfty_inl, T_zpow_smul_im]
      | inr c =>
        simp only [Set.mem_preimage, smul_inr, mem_horoInfty_inr]
        induction c using OnePoint.rec with
        | infty => simp [T_zpow_smul_infty]
        | coe q => simp [T_zpow_smul_coe]
    rw [e]
    exact isOpen_horoInfty hM
  · have e : (fun x : HStar => (T ^ n) • x) ⁻¹' HStar.horoDisk a r = HStar.horoDisk (a - n) r := by
      ext x
      induction x using HStar.ind with
      | inl z =>
        simp only [Set.mem_preimage, smul_inl, mem_horoDisk_inl _ hr, T_zpow_smul_im, T_zpow_smul_re]
        push_cast
        ring_nf
      | inr c =>
        simp only [Set.mem_preimage, smul_inr, mem_horoDisk_inr]
        induction c using OnePoint.rec with
        | infty => simp [T_zpow_smul_infty]
        | coe q =>
          rw [T_zpow_smul_coe]
          simp only [OnePoint.coe_eq_coe]
          constructor <;> intro h <;> linarith
    rw [e]
    exact isOpen_horoDisk _ hr

theorem continuous_S_smul : Continuous fun x : HStar => S • x := by
  refine continuous_of_generators (fun U hU => isOpen_smul_preimage_inl _ hU) (fun M hM => ?_)
    (fun a r hr => ?_)
  · have hr : 0 < 1 / (2 * M) := by positivity
    have e : (fun x : HStar => S • x) ⁻¹' HStar.horoInfty M = HStar.horoDisk 0 (1 / (2 * M)) := by
      ext x
      induction x using HStar.ind with
      | inl z =>
        simp only [Set.mem_preimage, smul_inl, mem_horoInfty_inl, mem_horoDisk_inl _ hr, S_smul_im]
        have hy := z.im_pos
        have hN : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
        rw [lt_div_iff₀ hN]
        push_cast
        constructor
        · intro h
          field_simp
          nlinarith
        · intro h
          field_simp at h
          nlinarith
      | inr c =>
        simp only [Set.mem_preimage, smul_inr, mem_horoInfty_inr, mem_horoDisk_inr]
        induction c using OnePoint.rec with
        | infty => simp [S_smul_infty]
        | coe q =>
          rw [S_smul_coe]
          split_ifs with hq <;> simp [hq]
    rw [e]
    exact isOpen_horoDisk _ hr
  · by_cases ha : a = 0
    · subst ha
      have hM : 0 < 1 / (2 * r) := by positivity
      have e : (fun x : HStar => S • x) ⁻¹' HStar.horoDisk 0 r = HStar.horoInfty (1 / (2 * r)) := by
        ext x
        induction x using HStar.ind with
        | inl z =>
          simp only [Set.mem_preimage, smul_inl, mem_horoInfty_inl, mem_horoDisk_inl _ hr, S_smul_im,
            S_smul_re]
          have hy := z.im_pos
          have hN : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
          push_cast
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
          constructor
          · intro h
            have : (z.re ^ 2 + z.im ^ 2) * (1 : ℝ) < (z.re ^ 2 + z.im ^ 2) * (2 * r * z.im) := by
              have h' := h
              field_simp at h'
              nlinarith
            nlinarith
          · intro h
            field_simp
            nlinarith
        | inr c =>
          simp only [Set.mem_preimage, smul_inr, mem_horoInfty_inr, mem_horoDisk_inr]
          induction c using OnePoint.rec with
          | infty => simp [S_smul_infty]
          | coe q =>
            rw [S_smul_coe]
            split_ifs with hq
            · simp [hq]
            · simp only [OnePoint.coe_eq_coe, ]
              constructor
              · intro h
                exfalso
                have : (-1 / q : ℚ) ≠ 0 := div_ne_zero (by norm_num) hq
                exact this h
              · intro h
                exact absurd h (OnePoint.coe_ne_infty q)
      rw [e]
      exact isOpen_horoInfty hM
    · have hr' : 0 < r / (a : ℝ) ^ 2 := by
        have : (a : ℝ) ≠ 0 := by exact_mod_cast ha
        positivity
      have e : (fun x : HStar => S • x) ⁻¹' HStar.horoDisk a r = HStar.horoDisk (-1 / a) (r / (a : ℝ) ^ 2) := by
        ext x
        induction x using HStar.ind with
        | inl z =>
          simp only [Set.mem_preimage, smul_inl, mem_horoDisk_inl _ hr, mem_horoDisk_inl _ hr', S_smul_im,
            S_smul_re]
          have hy := z.im_pos
          have hN : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
          have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
          have ha2 : 0 < (a : ℝ) ^ 2 := by positivity
          push_cast
          -- both sides are equivalent to `1 + 2 a x + a² (x² + y²) < 2 r y`
          have hL : (-z.re / (z.re ^ 2 + z.im ^ 2) - a) ^ 2 + (z.im / (z.re ^ 2 + z.im ^ 2)) ^ 2 -
              2 * r * (z.im / (z.re ^ 2 + z.im ^ 2)) =
              (1 + 2 * a * z.re + a ^ 2 * (z.re ^ 2 + z.im ^ 2) - 2 * r * z.im) / (z.re ^ 2 + z.im ^ 2) := by
            field_simp
            ring
          have hR : (z.re - -1 / (a : ℝ)) ^ 2 + z.im ^ 2 - 2 * (r / (a : ℝ) ^ 2) * z.im =
              (1 + 2 * a * z.re + a ^ 2 * (z.re ^ 2 + z.im ^ 2) - 2 * r * z.im) / (a : ℝ) ^ 2 := by
            field_simp
            ring
          rw [← sub_neg, hL, ← sub_neg (a := (z.re - -1 / (a : ℝ)) ^ 2 + z.im ^ 2), hR,
            div_neg_iff, div_neg_iff]
          constructor
          · rintro (⟨-, h⟩ | ⟨h, -⟩)
            · exact absurd h (not_lt.mpr hN.le)
            · exact Or.inr ⟨h, ha2⟩
          · rintro (⟨-, h⟩ | ⟨h, -⟩)
            · exact absurd h (not_lt.mpr ha2.le)
            · exact Or.inr ⟨h, hN⟩
        | inr c =>
          simp only [Set.mem_preimage, smul_inr, mem_horoDisk_inr]
          induction c using OnePoint.rec with
          | infty =>
            rw [S_smul_infty]
            simp only [OnePoint.coe_eq_coe, OnePoint.infty_ne_coe, iff_false]
            exact Ne.symm ha
          | coe q =>
            rw [S_smul_coe]
            split_ifs with hq
            · subst hq
              simp only [OnePoint.infty_ne_coe, OnePoint.coe_eq_coe, false_iff]
              intro h
              have : (-1 / a : ℚ) ≠ 0 := div_ne_zero (by norm_num) ha
              exact this h.symm
            · simp only [OnePoint.coe_eq_coe]
              constructor
              · intro h
                rw [← h]
                field_simp
              · intro h
                rw [h]
                field_simp
      rw [e]
      exact isOpen_horoDisk _ hr'

/-- **Every element of $\mathrm{SL}_2(\mathbb Z)$ acts continuously on $\mathbb H^*$** (Milne, pdf p. 184, the
second half of the named running-text statement `HStarTopology`). -/
@[kb "milne2006ec" "Ch. V, §1, SL₂(ℤ) acts continuously on ℍ* (running text), pdf p. 184"]
theorem continuous_smul_hstar (g : SL(2, ℤ)) : Continuous fun x : HStar => g • x := by
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {g | Continuous (fun x : HStar => g • x) ∧ Continuous (fun x : HStar => g⁻¹ • x)}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, ?_⟩
        · exact (ha.comp hb).congr fun x => (mul_smul a b x).symm
        · exact (hb'.comp ha').congr fun x => by
            simp only [Function.comp_apply, mul_inv_rev, mul_smul]
      one_mem' := by simp only [Set.mem_ofPred_eq, inv_one, one_smul]; exact ⟨continuous_id, continuous_id⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        simp only [Set.mem_ofPred_eq, inv_inv]
        exact ⟨ha', ha⟩ }
  have hS : S ∈ H := by
    refine ⟨continuous_S_smul, ?_⟩
    have hS4 : S⁻¹ = S * S * S := by
      rw [inv_eq_iff_mul_eq_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_S, Matrix.mul_apply, Fin.sum_univ_two]
    show Continuous fun x : HStar => S⁻¹ • x
    simp only [hS4, mul_smul]
    exact continuous_S_smul.comp (continuous_S_smul.comp continuous_S_smul)
  have hT : T ∈ H := by
    refine ⟨?_, ?_⟩
    · simpa using continuous_T_zpow_smul 1
    · simpa using continuous_T_zpow_smul (-1)
  have hH : H = ⊤ := by
    rw [eq_top_iff, ← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hS
    · exact hT
  have : g ∈ H := hH ▸ Subgroup.mem_top g
  exact this.1

/-! ### Compactness -/

theorem continuous_inl_hstar : Continuous HStar.inl := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro s ((⟨U, hU, rfl⟩ | ⟨M, hM, rfl⟩) | ⟨a, r, hr, rfl⟩)
  · have : HStar.inl ⁻¹' (HStar.inl '' U) = U := Set.preimage_image_eq U fun a b h => Sum.inl_injective h
    show IsOpen (HStar.inl ⁻¹' (HStar.inl '' U))
    rw [this]
    exact hU
  · have : HStar.inl ⁻¹' HStar.horoInfty M = {z | M < z.im} := by
      ext z
      exact mem_horoInfty_inl M z
    rw [this]
    exact isOpen_lt continuous_const UpperHalfPlane.continuous_im
  · have : HStar.inl ⁻¹' HStar.horoDisk a r = {z : ℍ | (z.re - a) ^ 2 + z.im ^ 2 < 2 * r * z.im} := by
      ext z
      exact mem_horoDisk_inl a hr z
    rw [this]
    exact isOpen_lt (((UpperHalfPlane.continuous_re.sub continuous_const).pow 2).add
      (UpperHalfPlane.continuous_im.pow 2)) (continuous_const.mul UpperHalfPlane.continuous_im)

theorem horoInfty_mono {M M' : ℝ} (h : M ≤ M') : HStar.horoInfty M' ⊆ HStar.horoInfty M := by
  rintro x (⟨z, rfl, hz⟩ | hx)
  · exact Or.inl ⟨z, rfl, lt_of_le_of_lt h hz⟩
  · exact Or.inr hx

/-- An open set of $\mathbb H^*$ containing $\infty$ contains a neighbourhood $\{\Im z > M\} \cup \{\infty\}$. -/
theorem exists_horoInfty_subset {V : Set HStar} (hV : IsOpen V) (h : HStar.cusp ∞ ∈ V) :
    ∃ M : ℝ, 0 < M ∧ HStar.horoInfty M ⊆ V := by
  have hV' : TopologicalSpace.GenerateOpen _ V := hV
  clear hV
  induction hV' with
  | basic s hs =>
    rcases hs with (⟨U, hU, rfl⟩ | ⟨M, hM, rfl⟩) | ⟨a, r, hr, rfl⟩
    · obtain ⟨w, -, hw⟩ := h
      exact absurd hw Sum.inl_ne_inr
    · exact ⟨M, hM, subset_rfl⟩
    · exact absurd ((mem_horoDisk_inr a r ∞).mp h) (OnePoint.infty_ne_coe a)
  | univ => exact ⟨1, one_pos, Set.subset_univ _⟩
  | inter s t _ _ hs ht =>
    obtain ⟨M, hM, hMs⟩ := hs h.1
    obtain ⟨M', hM', hMt⟩ := ht h.2
    exact ⟨max M M', lt_max_of_lt_left hM, fun x hx =>
      ⟨hMs (horoInfty_mono (le_max_left _ _) hx), hMt (horoInfty_mono (le_max_right _ _) hx)⟩⟩
  | sUnion S _ hS =>
    obtain ⟨s, hs, hxs⟩ := h
    obtain ⟨M, hM, hMs⟩ := hS s hs hxs
    exact ⟨M, hM, hMs.trans (Set.subset_sUnion_of_mem hs)⟩

/-- The closed fundamental domain with its cusp, $\mathcal D^* = \mathcal D \cup \{\infty\}$. -/
def fdStar : Set HStar := HStar.inl '' ModularGroup.fd ∪ {HStar.cusp ∞}

/-- $\mathcal D^*$ is compact. -/
theorem isCompact_fdStar : IsCompact fdStar := by
  classical
  rw [isCompact_iff_finite_subcover]
  intro ι U hU hcover
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (hcover (Or.inr rfl))
  obtain ⟨M, -, hM⟩ := exists_horoInfty_subset (hU i₀) hi₀
  have hK : IsCompact (HStar.inl '' truncatedFundamentalDomain M) :=
    (isCompact_truncatedFundamentalDomain M).image continuous_inl_hstar
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU (fun x hx => by
    obtain ⟨z, hz, rfl⟩ := hx
    exact hcover (Or.inl ⟨z, hz.1, rfl⟩))
  refine ⟨insert i₀ t, fun x hx => ?_⟩
  rw [Finset.set_biUnion_insert]
  rcases hx with ⟨z, hz, rfl⟩ | rfl
  · by_cases hzM : z.im ≤ M
    · exact Or.inr (ht ⟨z, ⟨hz, hzM⟩, rfl⟩)
    · exact Or.inl (hM ((mem_horoInfty_inl M z).mpr (not_le.mp hzM)))
  · exact Or.inl hi₀

/-- Every point of $\mathbb H^*$ has a translate in $\mathcal D^*$. -/
theorem exists_smul_mem_fdStar (x : HStar) : ∃ g : SL(2, ℤ), g • x ∈ fdStar := by
  induction x using HStar.ind with
  | inl z =>
    obtain ⟨g, hg⟩ := exists_smul_mem_fd z
    exact ⟨g, Or.inl ⟨g • z, hg, rfl⟩⟩
  | inr c =>
    obtain ⟨γ, hγ⟩ := exists_smul_infty c
    refine ⟨γ⁻¹, Or.inr ?_⟩
    show γ⁻¹ • HStar.cusp c = HStar.cusp ∞
    rw [smul_inr, ← hγ, inv_smul_smul]

/-- **Proposition 1.7, compactness** (Milne, *EC*, V, Proposition 1.7, pdf p. 186): for $\Gamma$ of finite index in
$\mathrm{SL}_2(\mathbb Z)$, $X(\Gamma) = \Gamma\backslash\mathbb H^*$ is compact. Adapted from the modular forms
library (see the module docstring). -/
@[kb "milne2006ec" "Ch. V, Proposition 1.7 (compactness), pdf p. 186"]
theorem compactSpace_xGamma (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : CompactSpace (XGamma Γ) := by
  classical
  have : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  let r : SL(2, ℤ) ⧸ Γ → SL(2, ℤ) := fun q => (Quotient.out q)⁻¹
  let π : HStar → XGamma Γ := Quotient.mk _
  have hπ : Continuous π := continuous_quotient_mk'
  refine ⟨?_⟩
  have hcover : (Set.univ : Set (XGamma Γ)) = ⋃ q, (fun x => π (r q • x)) '' fdStar := by
    refine (Set.eq_univ_of_forall fun p => ?_).symm
    refine Quotient.inductionOn p fun x => ?_
    obtain ⟨g, hg⟩ := exists_smul_mem_fdStar x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ g
    refine Set.mem_iUnion.mpr ⟨(g : SL(2, ℤ) ⧸ Γ), g • x, hg, ?_⟩
    apply Quotient.sound
    refine MulAction.orbitRel_apply.mpr ⟨⟨(h : SL(2, ℤ))⁻¹, Γ.inv_mem h.2⟩, ?_⟩
    show (h : SL(2, ℤ))⁻¹ • x = r (g : SL(2, ℤ) ⧸ Γ) • g • x
    simp only [r, hh, ← mul_smul]
    rw [show (g * (h : SL(2, ℤ)))⁻¹ * g = (h : SL(2, ℤ))⁻¹ by group]
  rw [hcover]
  exact isCompact_iUnion fun q => isCompact_fdStar.image (hπ.comp (continuous_smul_hstar _))


/-- **Proposition 1.9, unconditional** (Milne, *EC*, V, Proposition 1.9, pdf p. 187), topological form: $j$ induces a
homeomorphism of $X_0(1) = \mathrm{SL}_2(\mathbb Z)\backslash\mathbb H^*$ onto the sphere $\mathbb P^1(\mathbb C)$.
From the compactness proved here and the injectivity of $j$ proved in `NumberFieldKB.ModularCurves.jInjective`. -/
@[kb "milne2006ec" "Ch. V, Proposition 1.9, pdf p. 187"]
theorem prop_1_9_unconditional :
    ∃ e : XGamma ⊤ ≃ₜ OnePoint ℂ, ∀ x : HStar, e (Quotient.mk _ x) = jStar x :=
  prop_1_9_of_compactSpace (compactSpace_xGamma ⊤) NumberFieldKB.ModularCurves.jInjective

/-- **Proposition 1.7 for $\Gamma = \mathrm{SL}_2(\mathbb Z)$**: $X(1)$ is Hausdorff (it is homeomorphic to the
sphere). -/
@[kb "milne2006ec" "Ch. V, Proposition 1.7 (Hausdorff, level one), pdf p. 186"]
theorem t2Space_xGamma_top : T2Space (XGamma ⊤) := by
  obtain ⟨e, -⟩ := prop_1_9_unconditional
  exact e.symm.t2Space

end NumberFieldKB.MilneEC.V
