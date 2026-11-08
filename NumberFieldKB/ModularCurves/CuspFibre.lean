import NumberFieldKB.ModularCurves.FibreCount
import NumberFieldKB.ModularCurves.GenusFormula
import NumberFieldKB.ModularCurves.QExpShift
import NumberFieldKB.ModularCurves.QExpTransfer
import NumberFieldKB.ModularCurves.InftyEmbedding
import NumberFieldKB.ModularCurves.LaurentSupport
import NumberFieldKB.ModularCurves.CosetUpperTriangular

/-!
# The fibre of $j : X_0(N) \to X_0(1)$ over the cusp: the cusps of $X_0(N)$ and their widths

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf pp. 192–196). Put $z = N\tau$ and
$q = e^{2\pi i \tau}$. For each coset $c = \gamma\Gamma_0(N)$, with $a = \gcd(N, r)$ for the lower left entry $r$ of
$\gamma^{-1}$ and $d = N/a$, the conjugate $j_N(\gamma^{-1} z)$ is $j(a^2\tau + b/d)$ (`jN_smul_ofComplex_mul`), with
Laurent expansion $Y_c = J(\zeta_d^b q^{a^2})$. So $j \mapsto J(q^N)$, $j_N \mapsto Y_c$ is a $\mathbb Q(j)$-embedding
$\sigma_c : \mathbb Q(X_0(N)) \to \mathbb C((q))$ (`cuspEmb`), the $\mu$ embeddings are distinct
(`cuspEmb_injective`), and $\mathbb C((q))$ induces $v_\infty^N$ on $\mathbb Q(j)$. By `FibreCount.lean`, every cusp
of $X_0(N)$ is the place of some $\sigma_c$, and
$$N \sum_{P' \mid \infty} f(P') = \sum_c c(\sigma_c), \qquad c(\sigma_c) = \gcd(N, a_c^2)$$
(`scale_cuspEmb`, `mul_geomCount_infty`): the cusp of $\sigma_c$ has width $e = N / \gcd(N, a_c^2) = d/\gcd(a, d)$.
-/

open UpperHalfPlane hiding I
open Polynomial Complex ModularForm TauCeti
open scoped MatrixGroups WithZero Real

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable (N : ℕ) [NeZero N]

/-- See `RiemannHurwitz.lean`: the $\mathbb Q$-algebra structure of $\mathbb Q(t)$ through $\mathbb Q[t]$. -/
local instance (priority := high) ratFuncAlgebraRatCusp : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-! ### The modular polynomial over $\mathbb C$ and its roots -/

theorem modPolyQ_map_eq : (modPolyQ (prop2_4' N)).map (mapRingHom (algebraMap ℚ ℂ)) = modPolyCx N := by
  obtain ⟨hm, hdeg, -, hdiv⟩ := (prop2_4' N).exists_poly.choose_spec
  have hd := hdiv (modPolyCx N) (evalJJN_modPolyCx (N := N))
  have hm' : ((modPolyQ (prop2_4' N)).map (mapRingHom (algebraMap ℚ ℂ))).Monic := hm.map _
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hm' modPolyCx_monic hd ?_).symm
  rw [modPolyCx_natDegree, card_cosets, natDegree_map_eq_of_injective
    (by rw [coe_mapRingHom]; exact map_injective _ (algebraMap ℚ ℂ).injective)]
  exact hdeg.ge

theorem evalQ2_eq_eval (G : ℚ[X][X]) (x y : ℂ) :
    evalQ2 G x y = ((G.map (mapRingHom (algebraMap ℚ ℂ))).map (evalRingHom x)).eval y := by
  rw [evalQ2, Polynomial.eval_map, Polynomial.eval₂_map]
  congr 1
  ext r
  · simp
  · simp

/-- **The conjugates $j_N \circ \gamma^{-1}$ are roots of $F_N(j, Y)$.** -/
theorem evalQ2_modPolyQ_cosetRoot (c : Cosets N) (z : ℍ) :
    evalQ2 (modPolyQ (prop2_4' N)) (jFun z) (cosetRoot N c z) = 0 := by
  rw [evalQ2_eq_eval, modPolyQ_map_eq, modPolyCx_map, rootPoly, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [eval_sub, eval_X, eval_C, sub_self])

/-! ### The data of a coset -/

theorem one_le_N : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)

/-- The matrix $\gamma^{-1}$ for the coset $c = \gamma\Gamma_0(N)$. -/
def cosetMat (c : Cosets N) : SL(2, ℤ) := (Quotient.out c)⁻¹

/-- $a_c = \gcd(N, r)$. -/
def cosetA (c : Cosets N) : ℕ := cuspA N (cosetMat N c)

/-- $b_c$. -/
def cosetB (c : Cosets N) : ℤ := (jN_smul_ofComplex_mul N (one_le_N N) (cosetMat N c)).choose

/-- The real shift $b_c / d_c$. -/
def cosetShift (c : Cosets N) : ℝ := (cosetB N c : ℝ) / ((N / cosetA N c : ℕ) : ℝ)

theorem cosetA_pos (c : Cosets N) : 0 < cosetA N c := Nat.gcd_pos_of_pos_left _ (one_le_N N)

/-- Numerator and denominator of $j(a^2\tau + b/d)$. -/
def numC (c : Cosets N) : ℍ → ℂ := scaleN (cosetA N c ^ 2) (shiftR (cosetShift N c) cubeE4)
def denC (c : Cosets N) : ℍ → ℂ := scaleN (cosetA N c ^ 2) (shiftR (cosetShift N c) discFun)

theorem one_le_cosetA_sq (c : Cosets N) : 1 ≤ cosetA N c ^ 2 := Nat.one_le_pow _ _ (cosetA_pos N c)

theorem isQExp_numC (c : Cosets N) : IsQExp (numC N c) :=
  (isQExp_cubeE4.shift _).scaleN (one_le_cosetA_sq N c)

theorem isQExp_denC (c : Cosets N) : IsQExp (denC N c) :=
  (isQExp_discFun.shift _).scaleN (one_le_cosetA_sq N c)

theorem denC_ne_zero (c : Cosets N) (τ : ℍ) : denC N c τ ≠ 0 := ModularForm.discriminant_ne_zero _

theorem jFun_eq_div (z : ℍ) : jFun z = cubeE4 z / discFun z := by
  rw [eq_div_iff (ModularForm.discriminant_ne_zero z), jFun_mul_disc]
  rfl

theorem scaleN_shiftR_apply (m : ℕ) (hm : 1 ≤ m) (r : ℝ) (f : ℍ → ℂ) (τ : ℍ) :
    scaleN m (shiftR r f) τ = f (ofComplex ((m : ℂ) * τ + r)) := by
  have hpos : 0 < ((m : ℂ) * τ).im := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    simp [Complex.mul_im]; exact mul_pos this τ.im_pos
  have hpos' : 0 < ((m : ℂ) * τ + r).im := by simpa using hpos
  simp only [scaleN, shiftR]
  congr 1
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd, ofComplex_apply_of_im_pos hpos, ofComplex_apply_of_im_pos hpos']
  ring

/-- **The conjugate at the cusp**: $j_N(\gamma^{-1}(N\tau)) = \mathrm{num}_c(\tau)/\mathrm{den}_c(\tau)$. -/
theorem cosetRoot_ofComplex_mul (c : Cosets N) (τ : ℍ) :
    cosetRoot N c (ofComplex ((N : ℂ) * τ)) = numC N c τ / denC N c τ := by
  have h := (jN_smul_ofComplex_mul N (one_le_N N) (cosetMat N c)).choose_spec τ
  rw [cosetRoot, ← cosetMat, h, numC, denC, scaleN_shiftR_apply _ (one_le_cosetA_sq N c),
    scaleN_shiftR_apply _ (one_le_cosetA_sq N c), ← jFun_eq_div]
  congr 3
  · simp only [cosetA]; push_cast; ring
  · rw [cosetShift]; push_cast; rfl

theorem jN_eq_div (τ : ℍ) : jFun (ofComplex ((N : ℂ) * τ)) = scaleN N cubeE4 τ / scaleN N discFun τ := by
  rw [jFun_eq_div]
  rfl

/-! ### The embeddings $\sigma_c$ -/

/-- $J(q^N)$, the image of $j$. -/
theorem valuation_jNSer' : Valued.v (jNSer N) = WithZero.exp (N : ℤ) := valuation_jNSer (one_le_N N)

/-- $\mathbb C((q))$ as a $\mathbb Q(j)$-algebra through $j \mapsto J(q^N)$ (a type synonym, so that the algebra
structure may depend on $N$). -/
def CuspField (N : ℕ) : Type := LaurentSeries ℂ

instance : Field (CuspField N) := inferInstanceAs (Field (LaurentSeries ℂ))

/-- $j \mapsto J(q^N)$. -/
def jToLaurent : RatFunc ℚ →+* LaurentSeries ℂ := ratFuncToLaurent (valuation_jNSer' N) (one_le_N N)

instance : Algebra (RatFunc ℚ) (CuspField N) := (jToLaurent N).toAlgebra

/-- The valuation of $\mathbb C((q))$ on `CuspField N`. -/
def lVal : Valuation (CuspField N) ℤᵐ⁰ := (Valued.v : Valuation (LaurentSeries ℂ) ℤᵐ⁰)

theorem cuspVal_algebraMap (x : RatFunc ℚ) :
    lVal N (algebraMap (RatFunc ℚ) (CuspField N) x) = (Place.infty ℚ).valuation x ^ N :=
  valuation_ratFuncToLaurent (valuation_jNSer' N) (one_le_N N) x

/-- $Y_c = \hat{\mathrm{num}}_c / \hat{\mathrm{den}}_c$, the expansion of $j_N(\gamma^{-1}(N\tau))$. -/
def ySer (c : Cosets N) : CuspField N := (qHat (numC N c) / qHat (denC N c) : LaurentSeries ℂ)

theorem jToLaurent_X : jToLaurent N RatFunc.X = jNSer N := by
  rw [jToLaurent, ← RatFunc.algebraMap_X, ratFuncToLaurent_algebraMap, polyToLaurent, coe_eval₂RingHom, eval₂_X]

/-- $Y_c$ is a root of $F_N(J(q^N), Y)$. -/
theorem aeval_ySer (c : Cosets N) :
    ((modPolyQ (prop2_4' N)).map (algebraMap ℚ[X] (RatFunc ℚ))).eval₂ (algebraMap (RatFunc ℚ) (CuspField N))
      (ySer N c) = 0 := by
  have h := eval_qHat_div_eq_zero (isQExp_cubeE4.scaleN (one_le_N N)) (isQExp_discFun.scaleN (one_le_N N))
    (isQExp_numC N c) (isQExp_denC N c) (fun _ => ModularForm.discriminant_ne_zero _) (denC_ne_zero N c)
    (modPolyQ (prop2_4' N)) fun τ => by
      rw [← jN_eq_div, ← cosetRoot_ofComplex_mul]
      exact evalQ2_modPolyQ_cosetRoot N c _
  have hcomp : (algebraMap (RatFunc ℚ) (CuspField N)).comp (algebraMap ℚ[X] (RatFunc ℚ)) =
      polyToLaurent (jNSer N) :=
    RingHom.ext fun p => ratFuncToLaurent_algebraMap (valuation_jNSer' N) (one_le_N N) p
  rw [Polynomial.eval₂_map, hcomp]
  exact h

/-- **The embedding $\sigma_c$**: $j \mapsto J(q^N)$, $j_N \mapsto Y_c$. -/
def cuspEmb (c : Cosets N) : X0 N →ₐ[RatFunc ℚ] CuspField N :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId (RatFunc ℚ) (CuspField N)) (ySer N c) (aeval_ySer N c)

theorem cuspEmb_root (c : Cosets N) : cuspEmb N c (AdjoinRoot.root _) = ySer N c :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem qHat_neg {g : ℍ → ℂ} (hg : IsQExp g) : qHat (-g) = -qHat g := by
  have h : qHat (-g) + qHat g = 0 := by
    rw [← qHat_add hg.neg hg, neg_add_cancel, qHat, qExpansion_zero, map_zero]
  exact eq_neg_of_add_eq_zero_left h

theorem qHat_injective {f g : ℍ → ℂ} (hf : IsQExp f) (hg : IsQExp g) (h : qHat f = qHat g) : f = g := by
  have h0 : qHat (f + -g) = 0 := by rw [qHat_add hf hg.neg, qHat_neg hg, h, add_neg_cancel]
  rw [qHat_eq_zero_iff (hf.add hg.neg)] at h0
  exact (add_neg_eq_zero.1 h0)

theorem ofComplex_mul_ofComplex_div (z : ℍ) :
    ofComplex ((N : ℂ) * (ofComplex ((z : ℂ) / N) : ℍ)) = z := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : 0 < ((z : ℂ) / N).im := by
    have : ((z : ℂ) / N) = (((N : ℝ)⁻¹ : ℝ) : ℂ) * z := by push_cast; field_simp
    rw [this, Complex.im_ofReal_mul]
    exact mul_pos (inv_pos.2 hNr) z.im_pos
  have e : ((ofComplex ((z : ℂ) / N) : ℍ) : ℂ) = (z : ℂ) / N := by
    rw [ofComplex_apply_of_im_pos h1]
  rw [e, mul_div_cancel₀ _ hN, ofComplex_apply]

/-- **The $\mu$ embeddings $\sigma_c$ are distinct.** -/
theorem cuspEmb_injective : Function.Injective (cuspEmb N) := by
  intro c c' h
  have hy : ySer N c = ySer N c' := by rw [← cuspEmb_root, ← cuspEmb_root, h]
  have hd := qHat_ne_zero_of_nowhere (isQExp_denC N c) (denC_ne_zero N c)
  have hd' := qHat_ne_zero_of_nowhere (isQExp_denC N c') (denC_ne_zero N c')
  change qHat (numC N c) / qHat (denC N c) = qHat (numC N c') / qHat (denC N c') at hy
  rw [div_eq_div_iff hd hd', ← qHat_mul (isQExp_numC N c) (isQExp_denC N c'),
    ← qHat_mul (isQExp_numC N c') (isQExp_denC N c)] at hy
  have hf := qHat_injective ((isQExp_numC N c).mul (isQExp_denC N c'))
    ((isQExp_numC N c').mul (isQExp_denC N c)) hy
  apply cosetRoot_injective (one_le_N N)
  funext z
  rw [← ofComplex_mul_ofComplex_div N z, cosetRoot_ofComplex_mul, cosetRoot_ofComplex_mul,
    div_eq_div_iff (denC_ne_zero N c _) (denC_ne_zero N c' _)]
  exact congrFun hf _

theorem card_cosets_eq_finrank : Fintype.card (Cosets N) = Module.finrank (RatFunc ℚ) (X0 N) := by
  rw [card_cosets, finrank_X0]

/-- **The cusps of $X_0(N)$ from the embeddings**: $N \sum_{P' \mid \infty} f(P') = \sum_c c(\sigma_c)$. -/
theorem mul_geomCount_infty_eq_sum_scale :
    (N : ℤ) * geomCount N (Place.infty ℚ) =
      ∑ c, scale (isFunctionField_X0 N) (cuspVal_algebraMap N) (cuspEmb N c) (one_le_N N) := by
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  have h := mul_sum_relativeDegree_eq (isFunctionField_X0 N) (cuspVal_algebraMap N) (cuspEmb N)
    (cuspEmb_injective N) (card_cosets_eq_finrank N) (one_le_N N)
  rw [geomCount, Nat.cast_sum]
  exact h

end NumberFieldKB.ModularCurves
