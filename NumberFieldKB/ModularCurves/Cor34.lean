import NumberFieldKB.ModularCurves.ComplexCuspLink
import NumberFieldKB.ModularCurves.ComplexCuspDeriv
import NumberFieldKB.ModularCurves.ComplexConverseCusp
import NumberFieldKB.ModularCurves.GenusX0

/-!
# Milne, Corollary V.3.4: $\dim S_2(\Gamma_0(N)) = g(X_0(N))$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Corollary 3.4 (pdf p. 199). A weight 2 cusp form $f$ for
$\Gamma_0(N)$ corresponds to the holomorphic differential $f(z)\,dz = h\,dj$ on $X_0(N)$, $h = f/j' \in
\mathbb C(X_0(N))$, and $h\,dj$ is holomorphic iff $h \in L(W)$, $W = \operatorname{div}(dj)$. Here:

* `IsRep.mem_canonicalW`: the representative $h_f$ of a cusp form lies in $L(W)$ (finite places:
  `IsRep.forall_finite`; cusps: `cuspEmbC_mul_jDerSer`, `forall_infty_iff_jDerSer`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped WithZero MatrixGroups Manifold

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable (N : ℕ) [NeZero N]

/-- **The representative of a cusp form lies in $L(W)$.** -/
theorem IsRep.mem_canonicalW {f : ℍ → ℂ} (hf : IsCuspFormMilne (CongruenceSubgroup.Gamma0 N) 1 f) {h : X0C N}
    (H : IsRep N f hf.1 h) : h ∈ riemannRochSpace (canonicalW N) := by
  rcases eq_or_ne h 0 with rfl | hh
  · exact Submodule.zero_mem _
  obtain ⟨P, d, hd, rfl⟩ := exists_eq_div_mkC N h
  have hQ : mkC N (C d) ≠ 0 := by
    rw [mkC_C]
    exact (_root_.map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).2 hd)
  rw [mem_riemannRochSpace_iff_neg_le_ord hh]
  intro P'
  by_cases hP : P'.restrict ℂ (RatFunc ℂ) = Place.infty ℂ
  · refine (forall_infty_iff_jDerSer N hh).2 (fun c => ?_) P' hP
    have e := cuspEmbC_mul_jDerSer N hf hQ H c
    rw [e]
    exact valuation_qHat_le_of_isZeroAtImInfty (isQExp_slashScale N hf _) (isZeroAtImInfty_slashScale N hf _)
  · exact H.forall_finite N hh P' hP

/-! ### The converse and the isomorphism -/

theorem IsRep.add {f g : ℍ → ℂ} {hf : MDiff f} {hg : MDiff g} {a b : X0C N} (Ha : IsRep N f hf a)
    (Hb : IsRep N g hg b) : IsRep N (f + g) (hf.add hg) (a + b) := fun τ => by
  rw [map_add, add_mul, Ha τ, Hb τ, ← MeroGerm.mk_add]
  rfl

theorem IsRep.const_smul {f : ℍ → ℂ} {hf : MDiff f} {a : X0C N} (Ha : IsRep N f hf a) (r : ℂ) :
    IsRep N (r • f) (hf.const_smul r) (r • a) := fun τ => by
  have e : r • a = mkC N (C (C r)) * a := by rw [mkC_C_C, Algebra.smul_def]
  rw [e, map_mul, mul_assoc, Ha τ, finEmbC_mkC, polyGerm2, ← MeroGerm.mk_mul, MeroGerm.mk_eq_mk]
  refine Filter.Eventually.of_forall fun w => ?_
  simp [polyFun2]

/-- A function represented by $0$ is $0$. -/
theorem IsRep.eq_zero {f : ℍ → ℂ} {hf : MDiff f} (H : IsRep N f hf 0) : f = 0 := by
  have H' : IsRep N f hf (mkC N 0 / mkC N (C 1)) := by
    convert H using 1
    rw [map_zero, div_eq_mul_inv, zero_mul]
  funext z
  have := rep_identity N hf (mkC_C_ne_zero N one_ne_zero) H' z
  rw [evalJJN_C] at this
  simpa [evalJJN] using this.symm

/-- **Every element of $L(W)$ represents a cusp form.** -/
theorem isCuspFormMilne_of_mem {f : ℍ → ℂ} {hf : MDiff f} {h : X0C N} (H : IsRep N f hf h)
    (hW : h ∈ riemannRochSpace (canonicalW N)) : IsCuspFormMilne (CongruenceSubgroup.Gamma0 N) 1 f := by
  refine ⟨hf, fun γ hγ z => ?_, fun γ => ?_⟩
  · have e := (weight_two_iff_differential_invariant γ f).2 (fun w => by
      rw [pullback_eq_slash, H.slash_eq N hγ]) z
    simpa using e
  · have := H.isZeroAtImInfty_slash N hW γ
    convert this using 1
    funext z
    rw [show (2 * ((1 : ℕ) : ℤ)) = 2 by norm_num]
    exact (slash_mapGL_apply 2 f γ z).symm

/-- The cusp forms of weight 2 for $\Gamma_0(N)$ (Mathlib). -/
abbrev S2 : Type := CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2

theorem isCuspFormMilne_S2 (F : S2 N) : IsCuspFormMilne (CongruenceSubgroup.Gamma0 N) 1 F :=
  (def_3_1_cusp _ 1 F).2 ⟨F, rfl⟩

theorem exists_isRep_S2 (F : S2 N) : ∃ h, IsRep N F (isCuspFormMilne_S2 N F).1 h := by
  obtain ⟨P, Q, -, H⟩ := exists_isRep N (isCuspFormMilne_S2 N F)
  exact ⟨_, H⟩

/-- The representative $h_F = F/j' \in \mathbb C(X_0(N))$ of a cusp form. -/
def repS2 (F : S2 N) : X0C N := (exists_isRep_S2 N F).choose

theorem isRep_repS2 (F : S2 N) : IsRep N F (isCuspFormMilne_S2 N F).1 (repS2 N F) :=
  (exists_isRep_S2 N F).choose_spec

/-- **$F \mapsto F/j'$, $S_2(\Gamma_0(N)) \to L(W)$**, $\mathbb C$-linear. -/
def repS2Hom : S2 N →ₗ[ℂ] riemannRochSpace (canonicalW N) where
  toFun F := ⟨repS2 N F, (isRep_repS2 N F).mem_canonicalW N (isCuspFormMilne_S2 N F)⟩
  map_add' F G := by
    apply Subtype.ext
    exact (IsRep.unique N (isRep_repS2 N (F + G))
      ((isRep_repS2 N F).add N (isRep_repS2 N G)))
  map_smul' r F := by
    apply Subtype.ext
    exact (IsRep.unique N (isRep_repS2 N (r • F)) ((isRep_repS2 N F).const_smul N r))

theorem repS2Hom_injective : Function.Injective (repS2Hom N) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  have h0 : repS2 N F = 0 := congrArg Subtype.val hF
  have H := isRep_repS2 N F
  rw [h0] at H
  exact DFunLike.coe_injective (H.eq_zero N)

theorem repS2Hom_surjective : Function.Surjective (repS2Hom N) := by
  rintro ⟨h, hW⟩
  obtain ⟨f, hf, H⟩ := exists_isRep_of_mem N hW
  obtain ⟨F, hF⟩ := (def_3_1_cusp _ 1 f).1 (isCuspFormMilne_of_mem N H hW)
  subst hF
  refine ⟨F, Subtype.ext ?_⟩
  exact IsRep.unique N (isRep_repS2 N F) H

/-- **$S_2(\Gamma_0(N)) \cong L(W)$**, $W = \operatorname{div}(dj)$. -/
def cuspFormEquiv : S2 N ≃ₗ[ℂ] riemannRochSpace (canonicalW N) :=
  LinearEquiv.ofBijective (repS2Hom N) ⟨repS2Hom_injective N, repS2Hom_surjective N⟩

/-- **Milne, Corollary V.3.4**: $\dim_{\mathbb C} S_2(\Gamma_0(N)) = g(X_0(N))$, the genus of the function field
$\mathbb Q(X_0(N))$. -/
@[kb "milne2006ec" "Ch. V, Corollary 3.4, pdf p. 199"]
theorem cor_3_4 : (Module.finrank ℂ (S2 N) : ℤ) = NumberFieldKB.MilneEC.genus ℚ (X0 N) := by
  rw [(cuspFormEquiv N).finrank_eq, ← Divisor.dim_def, dim_canonicalW_eq_genus,
    genus_X0_eq N]

end NumberFieldKB.ModularCurves
