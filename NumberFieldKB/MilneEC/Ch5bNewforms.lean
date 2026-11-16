import NumberFieldKB.MilneEC.Ch5bHeckeOp
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
# Milne, *Elliptic Curves*, Chapter V, Section 4: the Petersson product and newforms

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, subsections "The Petersson inner product" and "New forms: the
theorem of Atkin and Lehner" (pdf pp. 214–215), and the definition of newforms in Section 5 (p. 216).

* `peterssonProduct N k f g` $= \iint_D f\bar g\,y^{2k}\,dx\,dy/y^2$ over a fundamental domain $D$ for $\Gamma_0(N)$,
  computed as $\sum_{\gamma} \iint_{\mathcal F} (f \bar g y^{2k})(\gamma z)\,dx\,dy/y^2$ with $\mathcal F$ the standard
  fundamental domain of $\mathrm{SL}_2(\mathbb Z)$ (`ModularGroup.fd`) and $\gamma$ running through representatives
  of $\Gamma_0(N) \backslash \mathrm{SL}_2(\mathbb Z)$, i.e. $D = \bigcup_\gamma \gamma\mathcal F$. Milne's remark that
  the integral does not depend on $D$ is not formalized; the definition fixes this $D$.
* **Theorem 4.19** (Petersson): named statement `Thm4_19` (convergence and self-adjointness of $T(n)$,
  $\gcd(n, N) = 1$). The hermitian symmetry is proved unconditionally (`peterssonProduct_conj_symm`), positivity and
  sesquilinearity from the convergence part (`thm_4_19_hermitian`).
* **Old and new forms** (Definition in prose, p. 215): `oldForms`, `newFormSet`. **Correction**: Milne calls old the cusp forms lying in some $S_{2k}(\Gamma_0(M))$, $M \mid N$,
  $M < N$; the theorem of Atkin and Lehner is about the space spanned by the $f(dz)$, $f \in S_{2k}(\Gamma_0(M))$,
  $dM \mid N$ (Atkin and Lehner 1970; Diamond and Shurman, Definition 5.6.1), which is what is used here.
* The stability of $S^{\mathrm{new}}_{2k}(\Gamma_0(N))$ under the $T(n)$ and $w_N$ (p. 215, running text): named
  statement `NewformsStable`.
* **Theorem 4.20** (Atkin and Lehner): named statement `Thm4_20`.
* Newforms and normalized newforms (Section 5, p. 216): `IsNewform`, `IsNormalizedNewform`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate Manifold

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

/-- **The Petersson product** (Milne, *EC*, V.4, p. 214): $\langle f, g\rangle = \iint_D f(z)\overline{g(z)}\,y^{2k}\,
\frac{dx\,dy}{y^2}$ for $D$ a fundamental domain of $\Gamma_0(N)$, here $D = \bigcup \gamma^{-1}\mathcal F$ over
representatives $\gamma$ of $\mathrm{SL}_2(\mathbb Z)/\Gamma_0(N)$ (see the module docstring). Weight $2k$. -/
def peterssonProduct (N : ℕ) (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∑ᶠ x : SL(2, ℤ) ⧸ Gamma0 N, ∫ z in ModularGroup.fd, petersson (2 * k) g f ((Quotient.out x)⁻¹ • z)

/-- The Petersson product is hermitian: $\langle g, f\rangle = \overline{\langle f, g\rangle}$. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.19 (pdf p. 214): hermitian symmetry"]
theorem peterssonProduct_conj_symm {N : ℕ} [NeZero N] (k : ℤ) (f g : ℍ → ℂ) :
    peterssonProduct N k g f = conj (peterssonProduct N k f g) := by
  have : Finite (SL(2, ℤ) ⧸ Gamma0 N) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (SL(2, ℤ) ⧸ Gamma0 N)
  unfold peterssonProduct
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => petersson_symm _ _ _ _)

/-- **Theorem 4.19 (Petersson)** (named statement; Milne, *EC*, V, Theorem 4.19, p. 214; Knapp, p. 280): the
Petersson integral converges if at least one of $f$, $g$ is a cusp form (each piece over $\gamma^{-1}\mathcal F$ is
integrable), and the Hecke operators $T(n)$ with $\gcd(n, N) = 1$ are self-adjoint on $S_{2k}(\Gamma_0(N))$. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.19 (Petersson; input)"]
structure Thm4_19 : Prop where
  integrable_left : ∀ (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma0 N) (2 * k))
    (g : ModularForm (Gamma0 N) (2 * k)) (γ : SL(2, ℤ)),
    IntegrableOn (fun z => petersson (2 * k) g f (γ • z)) ModularGroup.fd
  integrable_right : ∀ (N : ℕ) [NeZero N] (k : ℤ) (f : ModularForm (Gamma0 N) (2 * k))
    (g : CuspForm (Gamma0 N) (2 * k)) (γ : SL(2, ℤ)),
    IntegrableOn (fun z => petersson (2 * k) g f (γ • z)) ModularGroup.fd
  selfAdjoint : ∀ (N : ℕ) [NeZero N] (k : ℤ) (f g : CuspForm (Gamma0 N) (2 * k)) (n : ℕ), 0 < n →
    n.Coprime N → peterssonProduct N k (heckeOp N k n f) g = peterssonProduct N k f (heckeOp N k n g)

/-- A nonempty open subset of the upper half plane has positive invariant volume. -/
lemma volume_pos_of_isOpen {U : Set ℍ} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (volume : Measure ℍ) U := by
  have hc : Continuous fun x : ℍ => NNReal.mk x.im x.im_pos.le := continuous_im.subtype_mk _
  have hm : Measurable (fun x : ℍ => (↑((1 / NNReal.mk x.im x.im_pos.le : NNReal) ^ 2) : ENNReal)) :=
    Measurable.coe_nnreal_ennreal ((measurable_const.div hc.measurable).pow_const 2)
  rw [pos_iff_ne_zero, volume_def, Ne, withDensity_apply_eq_zero' hm.aemeasurable]
  have hset : {x : ℍ | (↑((1 / NNReal.mk x.im x.im_pos.le : NNReal) ^ 2) : ENNReal) ≠ 0} = Set.univ := by
    ext x
    have : (NNReal.mk x.im x.im_pos.le) ≠ 0 := fun h => x.im_ne_zero (by simpa using congrArg NNReal.toReal h)
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ENNReal.coe_ne_zero.mpr (pow_ne_zero 2 (one_div_ne_zero this))
  rw [hset, Set.univ_inter, measurableEmbedding_coe.comap_apply]
  exact (isOpenEmbedding_coe.isOpenMap U hU).measure_pos _ (hne.image _) |>.ne'

/-- A holomorphic function on the upper half plane vanishing on the standard open fundamental domain
vanishes identically (identity theorem). -/
lemma exists_ne_zero_mem_fdo {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (h0 : F ≠ 0) :
    ∃ z ∈ ModularGroup.fdo, F z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h0
  have hG : DifferentiableOn ℂ (F ∘ ofComplex) {z | 0 < z.im} := mdifferentiable_iff.mp hF
  have han := hG.analyticOnNhd isOpen_upperHalfPlaneSet
  have hp : (⟨2 * Complex.I, by simp⟩ : ℍ) ∈ ModularGroup.fdo := by
    refine ⟨?_, ?_⟩ <;> simp [Complex.normSq_apply]
    norm_num
  have hopen : IsOpen (((↑) : ℍ → ℂ) '' ModularGroup.fdo) :=
    isOpenEmbedding_coe.isOpenMap _ ModularGroup.isOpen_fdo
  have hev : (F ∘ ofComplex) =ᶠ[nhds (2 * Complex.I)] 0 := by
    filter_upwards [hopen.mem_nhds ⟨_, hp, rfl⟩] with w ⟨q, hq, hqw⟩
    subst hqw
    simp [hcon q hq]
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt (0:ℝ)).isPreconnected (z₀ := 2 * Complex.I) (by simp) hev
  ext z
  simpa using this z.im_pos

/-- The Petersson product as a finite sum over the cosets. -/
lemma pp_eq_sum {N : ℕ} [Fintype (SL(2, ℤ) ⧸ Gamma0 N)] (k : ℤ) (f g : ℍ → ℂ) :
    peterssonProduct N k f g = ∑ x : SL(2, ℤ) ⧸ Gamma0 N,
      ∫ z in ModularGroup.fd, petersson (2 * k) g f ((Quotient.out x)⁻¹ • z) :=
  finsum_eq_sum_of_fintype _

/-- Integrability of each piece, from the convergence part of Theorem 4.19. -/
lemma pp_int (h : Thm4_19) {N : ℕ} [NeZero N] (k : ℤ) (f g : CuspForm (Gamma0 N) (2 * k))
    (γ : SL(2, ℤ)) :
    IntegrableOn (fun z => petersson (2 * k) g f (γ • z)) ModularGroup.fd :=
  h.integrable_left N k f (CuspForm.toModularFormₗ g) γ

lemma pp_add_left (h : Thm4_19) {N : ℕ} [NeZero N] (k : ℤ) (f f' g : CuspForm (Gamma0 N) (2 * k)) :
    peterssonProduct N k (f + f') g = peterssonProduct N k f g + peterssonProduct N k f' g := by
  have : Finite (SL(2, ℤ) ⧸ Gamma0 N) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (SL(2, ℤ) ⧸ Gamma0 N)
  rw [pp_eq_sum, pp_eq_sum, pp_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← integral_add (pp_int h k f g _) (pp_int h k f' g _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [petersson, mul_add, add_mul]

lemma pp_smul_left (N : ℕ) [NeZero N] (k : ℤ) (c : ℂ) (f g : CuspForm (Gamma0 N) (2 * k)) :
    peterssonProduct N k (c • f) g = c * peterssonProduct N k f g := by
  have : Finite (SL(2, ℤ) ⧸ Gamma0 N) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (SL(2, ℤ) ⧸ Gamma0 N)
  rw [pp_eq_sum, pp_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [petersson]
  ring

lemma pp_add_right (h : Thm4_19) {N : ℕ} [NeZero N] (k : ℤ) (f g g' : CuspForm (Gamma0 N) (2 * k)) :
    peterssonProduct N k f (g + g') = peterssonProduct N k f g + peterssonProduct N k f g' := by
  have : Finite (SL(2, ℤ) ⧸ Gamma0 N) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (SL(2, ℤ) ⧸ Gamma0 N)
  rw [pp_eq_sum, pp_eq_sum, pp_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← integral_add (pp_int h k f g _) (pp_int h k f g' _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [petersson, add_mul]

lemma pp_smul_right (N : ℕ) [NeZero N] (k : ℤ) (c : ℂ) (f g : CuspForm (Gamma0 N) (2 * k)) :
    peterssonProduct N k f (c • g) = conj c * peterssonProduct N k f g := by
  have : Finite (SL(2, ℤ) ⧸ Gamma0 N) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (SL(2, ℤ) ⧸ Gamma0 N)
  rw [pp_eq_sum, pp_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [petersson]
  ring

/-- The inverse of the chosen representative of the trivial coset lies in `Gamma0 N`. -/
lemma out_inv_mem (N : ℕ) :
    (Quotient.out (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Gamma0 N))⁻¹ ∈ Gamma0 N := by
  have h2 : ((Quotient.out (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Gamma0 N) : SL(2, ℤ)) :
      SL(2, ℤ) ⧸ Gamma0 N) = QuotientGroup.mk 1 := Quotient.out_eq _
  rw [QuotientGroup.eq] at h2
  simpa using h2

/-- The Petersson integrand of a cusp form with itself is real and nonnegative. -/
lemma petersson_self_eq {N : ℕ} (k : ℤ) (f : CuspForm (Gamma0 N) (2 * k)) (τ : ℍ) :
    petersson (2 * k) f f τ = ((‖f τ‖ ^ 2 * τ.im ^ (2 * k) : ℝ) : ℂ) := by
  simp [petersson, Complex.conj_mul']

/-- The Petersson integrand of a cusp form with itself is invariant under `Gamma0 N`. -/
lemma petersson_self_invariant {N : ℕ} (k : ℤ) (f : CuspForm (Gamma0 N) (2 * k))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (τ : ℍ) :
    petersson (2 * k) f f (γ • τ) = petersson (2 * k) f f τ := by
  have hinv : (f : ℍ → ℂ) ∣[2 * k] γ = f := by
    rw [ModularForm.SL_slash]
    exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  rw [← petersson_slash_SL, hinv]

/-- Positivity of the Petersson product of a nonzero cusp form with itself. -/
lemma pp_self_pos (h : Thm4_19) {N : ℕ} [NeZero N] (k : ℤ) (f : CuspForm (Gamma0 N) (2 * k))
    (hf : f ≠ 0) :
    0 < (peterssonProduct N k f f).re ∧ (peterssonProduct N k f f).im = 0 := by
  have : Finite (SL(2, ℤ) ⧸ Gamma0 N) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (SL(2, ℤ) ⧸ Gamma0 N)
  set R : ℍ → ℝ := fun τ => ‖f τ‖ ^ 2 * τ.im ^ (2 * k) with hR
  have hRnn : ∀ τ, 0 ≤ R τ := fun τ => by
    have := τ.im_pos
    positivity
  have hsum : peterssonProduct N k f f = ((∑ x : SL(2, ℤ) ⧸ Gamma0 N,
      ∫ z in ModularGroup.fd, R ((Quotient.out x)⁻¹ • z) : ℝ) : ℂ) := by
    rw [pp_eq_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact petersson_self_eq k f _
  rw [hsum, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  set x₀ : SL(2, ℤ) ⧸ Gamma0 N := QuotientGroup.mk 1 with hx₀
  have hinv : ∀ z, R ((Quotient.out x₀)⁻¹ • z) = R z := fun z => by
    have := petersson_self_invariant k f (out_inv_mem N) z
    rw [petersson_self_eq, petersson_self_eq] at this
    exact_mod_cast this
  have hint : IntegrableOn R ModularGroup.fd := by
    have h1 := (pp_int h k f f 1).re
    exact h1.congr (Filter.Eventually.of_forall fun z => by
      simp only [one_smul, petersson_self_eq, RCLike.re_to_complex,
        Complex.ofReal_re, hR])
  have hcont : Continuous R := by
    have : Continuous (f : ℍ → ℂ) := (CuspFormClass.holo f).continuous
    simp only [hR]
    fun_prop (disch := simp [im_ne_zero])
  have hf0 : (f : ℍ → ℂ) ≠ 0 := fun hz => hf (by ext z; simpa using congrFun hz z)
  obtain ⟨z₀, hz₀, hz₀ne⟩ := exists_ne_zero_mem_fdo (CuspFormClass.holo f) hf0
  have hU : IsOpen (ModularGroup.fdo ∩ {z | f z ≠ 0}) :=
    ModularGroup.isOpen_fdo.inter (isOpen_ne_fun (CuspFormClass.holo f).continuous continuous_const)
  have hUsub : ModularGroup.fdo ∩ {z | f z ≠ 0} ⊆ Function.support R ∩ ModularGroup.fd := by
    rintro z ⟨hz, hzne⟩
    refine ⟨?_, ModularGroup.fdo_subset_fd hz⟩
    have hn : 0 < ‖f z‖ := norm_pos_iff.mpr hzne
    have : 0 < R z := mul_pos (by positivity) (zpow_pos z.im_pos _)
    exact this.ne'
  have hpos0 : 0 < ∫ z in ModularGroup.fd, R z := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hRnn) hint]
    exact lt_of_lt_of_le (volume_pos_of_isOpen hU ⟨z₀, hz₀, hz₀ne⟩) (measure_mono hUsub)
  refine Finset.sum_pos' (fun x _ => integral_nonneg fun z => hRnn _) ⟨x₀, Finset.mem_univ _, ?_⟩
  simpa only [hinv] using hpos0

/-- Theorem 4.19, second assertion (Milne, *EC*, V, Theorem 4.19, p. 214: "It therefore defines a positive-definite
hermitian form on $S_{2k}(\Gamma_0(N))$"), from the convergence part of the named statement: the Petersson product
is a sesquilinear form on $S_{2k}(\Gamma_0(N))$ (conjugate-linear in $g$), hermitian, with $\langle f, f\rangle > 0$
for $f \ne 0$. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.19 (pdf p. 214): positive-definite hermitian form"]
theorem thm_4_19_hermitian (h : Thm4_19) (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ B : CuspForm (Gamma0 N) (2 * k) →ₗ⋆[ℂ] CuspForm (Gamma0 N) (2 * k) →ₗ[ℂ] ℂ,
      (∀ f g, B g f = peterssonProduct N k f g) ∧
      ∀ f : CuspForm (Gamma0 N) (2 * k), f ≠ 0 →
        0 < (peterssonProduct N k f f).re ∧ (peterssonProduct N k f f).im = 0 := by
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun g f => peterssonProduct N k f g)
    (fun g g' f => pp_add_right h k f g g') (fun c g f => pp_smul_right N k c f g)
    (fun g f f' => pp_add_left h k f f' g) (fun c g f => pp_smul_left N k c f g), ?_, ?_⟩
  · intro f g
    rfl
  · exact fun f hf => pp_self_pos h k f hf

/-- The function $z \mapsto f(dz)$. -/
def scaleArg (d : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z => f (ofComplex ((d : ℂ) * z))

/-- The cusp forms of weight $2k$ for $\Gamma_0(N)$, as a subspace of the functions on $\mathbb H$. -/
def cuspSpace (N : ℕ) (k : ℤ) : Submodule ℂ (ℍ → ℂ) where
  carrier := Set.range (fun f : CuspForm (Gamma0 N) (2 * k) => (f : ℍ → ℂ))
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f + g, rfl⟩
  zero_mem' := ⟨0, rfl⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    exact ⟨c • f, rfl⟩

/-- Milne, *EC*, V.4, p. 215 (running text): if $M \mid N$ then $\Gamma_0(N) \subset \Gamma_0(M)$, and so
$S_{2k}(\Gamma_0(M)) \subset S_{2k}(\Gamma_0(N))$. -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 215): S(Γ₀(M)) ⊂ S(Γ₀(N)) for M | N"]
theorem cuspSpace_mono {M N : ℕ} [NeZero M] [NeZero N] (h : M ∣ N) (k : ℤ) : cuspSpace M k ≤ cuspSpace N k := by
  rintro _ ⟨f, rfl⟩
  have hle : (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) := by
    have : Gamma0 N ≤ Gamma0 M := by
      intro A hA
      rw [Gamma0_mem] at hA ⊢
      have := congrArg (ZMod.castHom h (ZMod M)) hA
      simpa using this
    exact Subgroup.map_mono this
  refine ⟨{ toFun := (f : ℍ → ℂ)
            slash_action_eq' := fun γ hγ => f.slash_action_eq' γ (hle hγ)
            holo' := f.holo'
            zero_at_cusps' := fun {c} hc => ?_ }, rfl⟩
  refine f.zero_at_cusps' ?_
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact hc

/-- **Old forms** (Milne, *EC*, V.4, p. 215, definition in prose, corrected as in the module docstring): the span of
the functions $z \mapsto f(dz)$ with $f \in S_{2k}(\Gamma_0(M))$, $M \mid N$, $M < N$, $dM \mid N$. -/
def oldForms (N : ℕ) (k : ℤ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ {g | ∃ M d : ℕ, 0 < M ∧ M ∣ N ∧ M < N ∧ 0 < d ∧ d * M ∣ N ∧ g ∈ (cuspSpace M k).map
    (LinearMap.funLeft ℂ ℂ fun z : ℍ => ofComplex ((d : ℂ) * z))}

/-- **New forms** (Milne, *EC*, V.4, p. 215, definition in prose): $S^{\mathrm{new}}_{2k}(\Gamma_0(N))$, the
orthogonal complement of the old forms in $S_{2k}(\Gamma_0(N))$ for the Petersson product. (A set: that it is a
subspace uses the convergence part of Theorem 4.19.) -/
def newFormSet (N : ℕ) (k : ℤ) : Set (ℍ → ℂ) :=
  {f | f ∈ cuspSpace N k ∧ ∀ g ∈ oldForms N k, peterssonProduct N k f g = 0}

/-- The involution $w_N$ (Milne, *EC*, V.4, p. 205): $(w_N f)(z) = (\sqrt N z)^{-2k} f(-1/(Nz))$. -/
def frickeOp (N : ℕ) (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z => ((Real.sqrt N : ℂ) * z) ^ (-2 * k) * f (ofComplex (-1 / ((N : ℂ) * z)))

/-- **Stability of the new forms** (named statement; Milne, *EC*, V.4, p. 215, running text, Atkin and Lehner 1970):
$S^{\mathrm{new}}_{2k}(\Gamma_0(N))$ is stable under all the $T(n)$ and under $w_N$. -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 215): S^new is stable under T(n) and w_N (input)"]
structure NewformsStable : Prop where
  hecke : ∀ (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ), 0 < n → ∀ f ∈ newFormSet N k, heckeOp N k n f ∈ newFormSet N k
  fricke : ∀ (N : ℕ) [NeZero N] (k : ℤ), ∀ f ∈ newFormSet N k, frickeOp N k f ∈ newFormSet N k

/-- **Theorem 4.20 (Atkin and Lehner 1970)** (named statement; Milne, *EC*, V, Theorem 4.20, p. 215): the
simultaneous eigenspaces $W_i$ in $S^{\mathrm{new}}_{2k}(\Gamma_0(N))$ for the $T(n)$, $\gcd(n, N) = 1$, are
one-dimensional: two new forms with the same eigenvalues $\lambda(n)$ for all $T(n)$, $\gcd(n, N) = 1$, are
proportional. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.20 (Atkin-Lehner; input)"]
structure Thm4_20 : Prop where
  dim_one : ∀ (N : ℕ) [NeZero N] (k : ℤ) (eig : ℕ → ℂ) (f g : ℍ → ℂ), f ∈ newFormSet N k → g ∈ newFormSet N k →
    (∀ n, 0 < n → n.Coprime N → heckeOp N k n f = eig n • f) →
    (∀ n, 0 < n → n.Coprime N → heckeOp N k n g = eig n • g) → f = 0 ∨ ∃ c : ℂ, g = c • f

/-- **Newform** (Milne, *EC*, V.5, p. 216, definition in prose): a nonzero element of one of the simultaneous
eigenspaces $W_i$ of $S^{\mathrm{new}}_{2k}(\Gamma_0(N))$ for the $T(n)$, $\gcd(n, N) = 1$. -/
def IsNewform (N : ℕ) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  f ∈ newFormSet N k ∧ f ≠ 0 ∧ ∃ eig : ℕ → ℂ, ∀ n, 0 < n → n.Coprime N → heckeOp N k n f = eig n • f

/-- **Normalized newform** (Milne, *EC*, V.5, p. 216): a newform $f = \sum c(n) q^n$ with $c(1) = 1$. -/
def IsNormalizedNewform (N : ℕ) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  IsNewform N k f ∧ (qExpansion 1 f).coeff 1 = 1

/-- Milne, *EC*, V.5, p. 216 (running text, "In each $W_i$ there is exactly one form $f_i$ with $c(1) = 1$"),
uniqueness part, from Theorem 4.20: two normalized newforms with the same eigenvalues are equal. -/
@[kb "milne2006ec" "Ch. V, Section 5 (pdf p. 216): uniqueness of the normalized form in W_i"]
theorem normalizedNewform_unique (h : Thm4_20) {N : ℕ} [NeZero N] {k : ℤ} {f g : ℍ → ℂ}
    (hf : IsNormalizedNewform N k f) (hg : IsNormalizedNewform N k g) (eig : ℕ → ℂ)
    (hfe : ∀ n, 0 < n → n.Coprime N → heckeOp N k n f = eig n • f)
    (hge : ∀ n, 0 < n → n.Coprime N → heckeOp N k n g = eig n • g) : f = g := by
  obtain ⟨⟨hfn, hf0, -⟩, hf1⟩ := hf
  obtain ⟨⟨hgn, -, -⟩, hg1⟩ := hg
  rcases h.dim_one N k eig f g hfn hgn hfe hge with h0 | ⟨c, hc⟩
  · exact absurd h0 hf0
  · obtain ⟨F, rfl⟩ := hfn.1
    have hper : (1 : ℝ) ∈ Subgroup.strictPeriods (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by simp
    have han := ModularFormClass.analyticAt_cuspFunction_zero F one_pos hper
    rw [hc, qExpansion_smul han, PowerSeries.coeff_smul, hf1, smul_eq_mul, mul_one] at hg1
    rw [hc, hg1, one_smul]

end NumberFieldKB.MilneEC.Vb
