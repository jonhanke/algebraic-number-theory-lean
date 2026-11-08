import NumberFieldKB.ModularCurves.ComplexConverse
import NumberFieldKB.ModularCurves.ComplexCuspVanish
import NumberFieldKB.ModularCurves.CuspCountX0

/-!
# From $L(W)$ to cusp forms: the condition at the cusps

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Proposition 3.3 and Corollary 3.4 (pdf p. 199), the converse
direction at the cusps. Let $f$ be holomorphic with representative $h = P(j,j_N)/d(j) \in L(W)$, $c$ a coset and
$F(\tau) = (f|_2\gamma_c^{-1})(N\tau)$ (holomorphic and $1$-periodic, `slash_vadd_N_of`). By `rep_identity_coset`,
$F\,B = A$ with $A = \delta^n P(\ldots)\,j'(N\tau)$ and $B = \delta^n d(j(N\tau))$ having $q$-expansions, and
$\hat A/\hat B = \sigma_c(h)\cdot$ `jDerSer N`, of order $\ge 1$ since $h \in L(W)$ (`forall_infty_iff_jDerSer`).
Hence $F \to 0$ at $i\infty$ (`isZeroAtImInfty_of_mul_eq`) and so does $f|_2\gamma$ for every
$\gamma \in \mathrm{SL}_2(\mathbb Z)$ (`IsRep.isZeroAtImInfty_slash`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti ModularForm
open scoped WithZero MatrixGroups Manifold

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable {N : ℕ}

/-- `slash_vadd_N` for any function invariant of weight 2 under $\Gamma_0(N)$. -/
theorem slash_vadd_N_of {f : ℍ → ℂ} (hslash : ∀ δ ∈ CongruenceSubgroup.Gamma0 N, f ∣[(2 : ℤ)] δ = f)
    (γ : SL(2, ℤ)) (τ : ℍ) : (f ∣[(2 : ℤ)] γ) ((N : ℝ) +ᵥ τ) = (f ∣[(2 : ℤ)] γ) τ := by
  set T' : SL(2, ℤ) := ModularGroup.T ^ (N : ℤ)
  have keyT : (f ∣[(2 : ℤ)] γ) ∣[(2 : ℤ)] T' = f ∣[(2 : ℤ)] γ := by
    rw [← SlashAction.slash_mul]
    have : γ * T' = (γ * T' * γ⁻¹) * γ := by simp
    rw [this, SlashAction.slash_mul, hslash _ (conj_T_zpow_mem_Gamma0 N γ)]
  have hc : (T' 1 0 : ℂ) * τ + T' 1 1 = 1 := by
    have h : (T' : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] := ModularGroup.coe_T_zpow (N : ℤ)
    have e10 : (T' 1 0 : ℤ) = 0 := by simpa using congrFun (congrFun h 1) 0
    have e11 : (T' 1 1 : ℤ) = 1 := by simpa using congrFun (congrFun h 1) 1
    rw [e10, e11]; simp
  have := congrFun keyT τ
  have h2 : ((f ∣[(2 : ℤ)] γ) ∣[(2 : ℤ)] T') τ =
      (T' 1 0 * (τ : ℂ) + T' 1 1) ^ (-(2 : ℤ)) * (f ∣[(2 : ℤ)] γ) (T' • τ) :=
    slash_mapGL_apply 2 _ T' τ
  rw [h2, hc, one_zpow, one_mul, UpperHalfPlane.modular_T_zpow_smul] at this
  exact_mod_cast this

theorem tendsto_ofComplex_div (hN : 1 ≤ N) :
    Tendsto (fun τ : ℍ => ofComplex ((τ : ℂ) / N)) atImInfty atImInfty := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [atImInfty, tendsto_comap_iff]
  have : (UpperHalfPlane.im ∘ fun τ : ℍ => ofComplex ((τ : ℂ) / N)) = fun τ : ℍ => τ.im / N := by
    funext τ
    have him : 0 < ((τ : ℂ) / N).im := by
      rw [Complex.div_natCast_im]; exact div_pos τ.im_pos hNpos
    simp only [Function.comp_apply]
    rw [← UpperHalfPlane.coe_im, ofComplex_apply_of_im_pos him, Complex.div_natCast_im]
    rfl
  rw [this]
  exact tendsto_comap.atTop_div_const hNpos

/-- If $F(\tau) = G(N\tau) \to 0$ at $i\infty$, then $G \to 0$. -/
theorem isZeroAtImInfty_of_scaleN (hN : 1 ≤ N) {G : ℍ → ℂ} (h : IsZeroAtImInfty (scaleN N G)) :
    IsZeroAtImInfty G := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have e : G = scaleN N G ∘ fun τ : ℍ => ofComplex ((τ : ℂ) / N) := by
    funext τ
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have him : 0 < ((τ : ℂ) / N).im := by
      rw [Complex.div_natCast_im]; exact div_pos τ.im_pos hNpos
    simp only [Function.comp_apply, scaleN]
    rw [ofComplex_apply_of_im_pos him]
    change G τ = G (ofComplex ((N : ℂ) * ((τ : ℂ) / N)))
    rw [mul_div_cancel₀ _ hNne, ofComplex_apply]
  rw [e]
  exact h.comp (tendsto_ofComplex_div hN)

variable (N) [NeZero N]

/-- `CuspField N` is `LaurentSeries ℂ`. -/
def cuspToL : CuspField N →+* LaurentSeries ℂ := RingHom.id _

omit [NeZero N] in
theorem lVal_eq (x : CuspField N) : lVal N x = Valued.v (cuspToL N x) := rfl

/-- **The cusp condition for a function with a representative in $L(W)$**, at the cusp of a coset. -/
theorem IsRep.isZeroAtImInfty_cosetMat {f : ℍ → ℂ} {hf : MDiff f} {h : X0C N} (H : IsRep N f hf h)
    (hW : h ∈ riemannRochSpace (canonicalW N)) (c : Cosets N) :
    IsZeroAtImInfty (f ∣[(2 : ℤ)] cosetMat N c) := by
  have hN := one_le_N N
  -- the cusp condition on `h`
  have hLW : lVal N (cuspEmbC N c h * jDerSer N) ≤ WithZero.exp (-1 : ℤ) := by
    rcases eq_or_ne h 0 with rfl | hh
    · rw [map_zero, zero_mul, map_zero]; exact zero_le
    · exact (forall_infty_iff_jDerSer N hh).1
        (fun P' _ => (mem_riemannRochSpace_iff_neg_le_ord hh).1 hW P') c
  obtain ⟨P, d, hd, rfl⟩ := exists_eq_div_mkC N h
  have hQ := mkC_C_ne_zero N hd
  have hslash : ∀ δ ∈ CongruenceSubgroup.Gamma0 N, f ∣[(2 : ℤ)] δ = f := fun δ hδ => H.slash_eq N hδ
  set F := scaleN N (f ∣[(2 : ℤ)] cosetMat N c)
  refine isZeroAtImInfty_of_scaleN hN ?_
  -- the pointwise identity in the variable of the cusp
  have hpt : ∀ τ : ℍ,
      (P.map (evalRingHom (scaleN N cubeE4 τ / scaleN N discFun τ))).eval (numC N c τ / denC N c τ) *
        ((-(2 * Real.pi * Complex.I)) * scaleN N derNum τ / scaleN N discFun τ) =
      F τ * ((C d).map (evalRingHom (scaleN N cubeE4 τ / scaleN N discFun τ))).eval
        (numC N c τ / denC N c τ) := by
    intro τ
    have h := rep_identity_coset N hf hQ H c (ofComplex ((N : ℂ) * τ))
    rw [jN_eq_div N τ, cosetRoot_ofComplex_mul N c τ, jD, deriv_jFun_mul_eq N τ] at h
    rw [show (-(2 * Real.pi * Complex.I)) * scaleN N derNum τ / scaleN N discFun τ =
      -(2 * Real.pi * Complex.I) * scaleN N derNum τ / scaleN N discFun τ by ring]
    exact h
  set dd : ℍ → ℂ := scaleN N discFun * denC N c
  have hd' : IsQExp dd := (isQExp_discFun.scaleN hN).mul (isQExp_denC N c)
  have hd0 : ∀ z, dd z ≠ 0 := fun z => mul_ne_zero (ModularForm.discriminant_ne_zero _) (denC_ne_zero N c z)
  have hD0 : ∀ z, scaleN N discFun z ≠ 0 := fun z => ModularForm.discriminant_ne_zero _
  let xj := divMerD hd' (isQExp_cubeE4.scaleN hN) (isQExp_denC N c) rfl hD0
  let xy := divMerD hd' (isQExp_numC N c) (isQExp_discFun.scaleN hN) (mul_comm _ _) (denC_ne_zero N c)
  let xD := divMerD hd' ((isQExp_derNum.scaleN hN).smul (-(2 * Real.pi * Complex.I))) (isQExp_denC N c) rfl hD0
  let xPD := evalMerD hd' xj xy P * xD
  let xQ := evalMerD hd' xj xy (C d)
  have hid : ∀ τ, xPD.1 τ = F τ * xQ.1 τ := by
    intro τ
    change (evalMerD hd' xj xy P).1 τ * xD.1 τ = F τ * (evalMerD hd' xj xy (C d)).1 τ
    rw [coe_evalMerD, coe_evalMerD]
    have := hpt τ
    simpa [xj, xy, xD, divMerD, Pi.div_apply, Pi.smul_apply, smul_eq_mul, mul_div_assoc] using this
  -- the Laurent expansions
  have ej : qMerDHom hd' hd0 xj = jNSer N :=
    qMerDHom_divMerD hd' hd0 (isQExp_cubeE4.scaleN hN) (isQExp_discFun.scaleN hN) (isQExp_denC N c) rfl hD0
  have ey : qMerDHom hd' hd0 xy = (ySer N c : LaurentSeries ℂ) :=
    qMerDHom_divMerD hd' hd0 (isQExp_numC N c) (isQExp_denC N c) (isQExp_discFun.scaleN hN) (mul_comm _ _)
      (denC_ne_zero N c)
  have eD : qMerDHom hd' hd0 xD =
      qHat ((-(2 * Real.pi * Complex.I)) • scaleN N derNum) / qHat (scaleN N discFun) :=
    qMerDHom_divMerD hd' hd0 ((isQExp_derNum.scaleN hN).smul _) (isQExp_discFun.scaleN hN) (isQExp_denC N c) rfl
      hD0
  have ePD : qMerDHom hd' hd0 xPD = (cuspEmbC N c (mkC N P) * jDerSer N : CuspField N) := by
    change qMerDHom hd' hd0 (evalMerD hd' xj xy P * xD) = _
    rw [map_mul, qMerDHom_evalMerD, ej, ey, eD, qHat_smul (isQExp_derNum.scaleN hN), cuspEmbC_mkC]
    rfl
  have eQ : qMerDHom hd' hd0 xQ = (cuspEmbC N c (mkC N (C d)) : CuspField N) := by
    change qMerDHom hd' hd0 (evalMerD hd' xj xy (C d)) = _
    rw [qMerDHom_evalMerD, ej, ey, cuspEmbC_mkC]
    rfl
  -- clear the denominators
  obtain ⟨n1, h1⟩ := xPD.2
  obtain ⟨n2, h2⟩ := xQ.2
  set A : ℍ → ℂ := dd ^ (n1 + n2) * xPD.1
  set B : ℍ → ℂ := dd ^ (n1 + n2) * xQ.1
  have hA : IsQExp A := by
    have : A = dd ^ n2 * (dd ^ n1 * xPD.1) := by simp only [A, pow_add]; ring
    rw [this]; exact (hd'.pow n2).mul h1
  have hB : IsQExp B := by
    have : B = dd ^ n1 * (dd ^ n2 * xQ.1) := by simp only [B, pow_add]; ring
    rw [this]; exact (hd'.pow n1).mul h2
  have hFB : ∀ z, F z * B z = A z := fun z => by
    simp only [A, B, Pi.mul_apply, hid z]; ring
  have hdn : qHat dd ^ (n1 + n2) ≠ 0 := pow_ne_zero _ (qHat_ne_zero_of_nowhere hd' hd0)
  have eA : qHat A = cuspToL N (cuspEmbC N c (mkC N P) * jDerSer N) * qHat dd ^ (n1 + n2) := by
    rw [← ePD]
    change qHat A = qMerDFun hd' xPD * _
    rw [qMerDFun_eq hd' hd0 xPD hA, div_mul_cancel₀ _ hdn]
  have eB : qHat B = cuspToL N (cuspEmbC N c (mkC N (C d))) * qHat dd ^ (n1 + n2) := by
    rw [← eQ]
    change qHat B = qMerDFun hd' xQ * _
    rw [qMerDFun_eq hd' hd0 xQ hB, div_mul_cancel₀ _ hdn]
  have hb : cuspToL N (cuspEmbC N c (mkC N (C d))) ≠ 0 :=
    (map_ne_zero_iff _ (cuspEmbC N c).toRingHom.injective).2 hQ
  have hB0 : qHat B ≠ 0 := by rw [eB]; exact mul_ne_zero hb hdn
  have eAB : qHat A = cuspToL N (cuspEmbC N c (mkC N P / mkC N (C d)) * jDerSer N) * qHat B := by
    rw [eA, eB, map_mul, map_mul, map_div₀, map_div₀]
    field_simp
  refine isZeroAtImInfty_of_mul_eq hA hB hB0 hFB ?_
  rw [eAB, map_mul, ← lVal_eq]
  exact mul_le_mul_left hLW _

/-- **The cusp condition**: $f|_2\gamma \to 0$ at $i\infty$ for every $\gamma \in \mathrm{SL}_2(\mathbb Z)$. -/
theorem IsRep.isZeroAtImInfty_slash {f : ℍ → ℂ} {hf : MDiff f} {h : X0C N} (H : IsRep N f hf h)
    (hW : h ∈ riemannRochSpace (canonicalW N)) (γ : SL(2, ℤ)) : IsZeroAtImInfty (f ∣[(2 : ℤ)] γ) := by
  obtain ⟨k, hk, e⟩ := cosetMat_mk (N := N) γ⁻¹
  rw [inv_inv] at e
  have hγ : γ = k⁻¹ * cosetMat N (QuotientGroup.mk γ⁻¹) := by rw [e]; group
  rw [hγ, SlashAction.slash_mul, H.slash_eq N (inv_mem hk)]
  exact H.isZeroAtImInfty_cosetMat N hW _

end NumberFieldKB.ModularCurves
