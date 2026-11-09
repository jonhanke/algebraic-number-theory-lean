import NumberFieldKB.MilneCFT.LubinTate.ArtinMap
import NumberFieldKB.MilneCFT.LubinTate.YamaguchiBridge

/-!
# $K[\Lambda_{f,n}]$ does not depend on $f$ (Milne, *CFT*, I, §3, p. 36)

Proof of `TorsionFieldIndependence`. For distinguished Lubin–Tate polynomials $f, g$ for the same $\pi$, let
$\varphi = [1]_{g,f}$ and $\psi = [1]_{f,g}$ (`lubinTateSeriesHom`); then $g^{(n)} \circ \varphi = \varphi \circ f^{(n)}$.
A root $\alpha$ of $f^{(n)}$ is sent to the root $\varphi(\alpha)$ of $g^{(n)}$, where $\varphi(\alpha)$ is the value
at $\alpha$ of a ring homomorphism $\mathcal O_K[[T]] \to \Omega$ extending the evaluation of polynomials at $\alpha$
(`IsEvAt`; it exists and is unique by Weierstrass division). Since $\varphi \circ \psi = T$, this map is a bijection
between the roots, and $\varphi(\alpha) \in K(\alpha)$.
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

section Aux

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- A ring homomorphism `E : 𝒪_K[[T]] → Ω` evaluating at `α`: it is the structure map on constants and sends `T`
to `α`. -/
def IsEvAt (E : PowerSeries 𝒪[K] →+* Ω) (α : Ω) : Prop :=
  (∀ a : 𝒪[K], E (PowerSeries.C a) = algebraMap K Ω (algebraMap 𝒪[K] K a)) ∧ E PowerSeries.X = α

theorem IsEvAt.coe_poly {E : PowerSeries 𝒪[K] →+* Ω} {α : Ω} (h : IsEvAt E α) (p : 𝒪[K][X]) :
    E (p : PowerSeries 𝒪[K]) = aeval α (p.map (algebraMap 𝒪[K] K)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.coe_add, map_add, hp, hq, Polynomial.map_add, map_add]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_pow,
      h.1, h.2, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, aeval_C, aeval_X]

theorem IsEvAt.eq {E E' : PowerSeries 𝒪[K] →+* Ω} {α : Ω} (hE : IsEvAt E α) (hE' : IsEvAt E' α)
    {F : 𝒪[K][X]} (hF : PowerSeries.map (IsLocalRing.residue 𝒪[K]) (F : PowerSeries 𝒪[K]) ≠ 0)
    (hα : aeval α (F.map (algebraMap 𝒪[K] K)) = 0) : E = E' := by
  refine RingHom.ext fun P => ?_
  have h := PowerSeries.eq_mul_weierstrassDiv_add_weierstrassMod (f := P) hF
  rw [h, map_add, map_add, map_mul, map_mul, hE.coe_poly, hE.coe_poly, hE'.coe_poly, hE'.coe_poly, hα]
  simp

theorem IsEvAt.mem {E : PowerSeries 𝒪[K] →+* Ω} {α : Ω} (hE : IsEvAt E α) {F : 𝒪[K][X]}
    (hF : PowerSeries.map (IsLocalRing.residue 𝒪[K]) (F : PowerSeries 𝒪[K]) ≠ 0)
    (hα : aeval α (F.map (algebraMap 𝒪[K] K)) = 0) (L : IntermediateField K Ω) (hL : α ∈ L)
    (P : PowerSeries 𝒪[K]) : E P ∈ L := by
  have h := PowerSeries.eq_mul_weierstrassDiv_add_weierstrassMod (f := P) hF
  rw [h, map_add, map_mul, hE.coe_poly, hE.coe_poly, hα, zero_mul, zero_add]
  rw [Polynomial.aeval_eq_sum_range]
  exact L.sum_mem fun i _ => by rw [Algebra.smul_def]; exact L.mul_mem (L.algebraMap_mem _) (_root_.pow_mem hL _)

/-- Existence of the evaluation homomorphism at a root of a distinguished polynomial. -/
theorem exists_isEvAt {F : 𝒪[K][X]} (hF : F.IsDistinguishedAt 𝓂[K]) {α : Ω}
    (hα : aeval α (F.map (algebraMap 𝒪[K] K)) = 0) : ∃ E : PowerSeries 𝒪[K] →+* Ω, IsEvAt E α := by
  let ε : 𝒪[K][X] →+* Ω :=
    (Polynomial.aeval α : K[X] →ₐ[K] Ω).toRingHom.comp (Polynomial.mapRingHom (algebraMap 𝒪[K] K))
  have hε : ∀ p, ε p = aeval α (p.map (algebraMap 𝒪[K] K)) := fun p => rfl
  have hker : Ideal.span {F} ≤ RingHom.ker ε := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (RingHom.mem_ker).2 (by rw [hε, hα])
  let e := hF.algEquivQuotient
  let E : PowerSeries 𝒪[K] →+* Ω :=
    ((Ideal.Quotient.lift (Ideal.span {F}) ε fun a ha => hker ha).comp
      e.symm.toRingEquiv.toRingHom).comp (Ideal.Quotient.mk _)
  have hE : ∀ p : 𝒪[K][X], E (p : PowerSeries 𝒪[K]) = ε p := by
    intro p
    have : e.symm (Ideal.Quotient.mk _ (p : PowerSeries 𝒪[K])) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [E, RingHom.comp_apply]
    change Ideal.Quotient.lift (Ideal.span {F}) ε _ (e.symm (Ideal.Quotient.mk _ _)) = _
    rw [this]; rfl
  refine ⟨E, fun a => ?_, ?_⟩
  · have := hE (Polynomial.C a)
    rw [Polynomial.coe_C, hε] at this
    rw [this]; simp
  · have := hE Polynomial.X
    rw [Polynomial.coe_X, hε] at this
    rw [this]; simp

/-- Composition of an evaluation with a substitution. -/
theorem isEvAt_comp {E : PowerSeries 𝒪[K] →+* Ω} {α : Ω} (hE : IsEvAt E α) {φ : PowerSeries 𝒪[K]}
    (hφ : PowerSeries.constantCoeff φ = 0) :
    IsEvAt (E.comp (PowerSeries.substAlgHom (R := 𝒪[K]) (S := 𝒪[K])
      (PowerSeries.HasSubst.of_constantCoeff_zero' hφ) : PowerSeries 𝒪[K] →ₐ[𝒪[K]] PowerSeries 𝒪[K]).toRingHom)
      (E φ) := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero' hφ
  refine ⟨fun a => ?_, ?_⟩
  · have : (PowerSeries.substAlgHom (R := 𝒪[K]) (S := 𝒪[K]) ha : PowerSeries 𝒪[K] →ₐ[𝒪[K]] PowerSeries 𝒪[K])
        (PowerSeries.C a) = PowerSeries.C a :=
      (PowerSeries.substAlgHom (R := 𝒪[K]) (S := 𝒪[K]) ha).commutes a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [this, hE.1]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [PowerSeries.substAlgHom_X]

/-- A root of `F` is sent by a substitution `φ` intertwining `F` and `G` to a root of `G`. -/
theorem aeval_eval_root {F G : 𝒪[K][X]} {φ : PowerSeries 𝒪[K]} (hφ : PowerSeries.constantCoeff φ = 0)
    (hF0 : PowerSeries.constantCoeff (F : PowerSeries 𝒪[K]) = 0)
    (hcomp : (G : PowerSeries 𝒪[K]).subst φ = φ.subst (F : PowerSeries 𝒪[K]))
    {E : PowerSeries 𝒪[K] →+* Ω} {α : Ω} (hE : IsEvAt E α)
    (hα : aeval α (F.map (algebraMap 𝒪[K] K)) = 0) :
    aeval (E φ) (G.map (algebraMap 𝒪[K] K)) = 0 := by
  have h1 := (isEvAt_comp hE hφ).coe_poly G
  rw [← h1]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, PowerSeries.coe_substAlgHom]
  rw [hcomp]
  obtain ⟨φ', hφ'⟩ := PowerSeries.X_dvd_iff.mpr hφ
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hF0
  have : φ.subst (F : PowerSeries 𝒪[K]) = (F : PowerSeries 𝒪[K]) * φ'.subst (F : PowerSeries 𝒪[K]) := by
    rw [hφ', PowerSeries.subst_mul hs, PowerSeries.subst_X hs]
  rw [this, map_mul, hE.coe_poly, hα, zero_mul]

/-- The residue of a distinguished polynomial is nonzero. -/
theorem residue_ne_zero {g : 𝒪[K][X]} (hg : g.IsDistinguishedAt 𝓂[K]) :
    PowerSeries.map (IsLocalRing.residue 𝒪[K]) (g : PowerSeries 𝒪[K]) ≠ 0 :=
  hg.map_ne_zero_of_eq_mul (f := (g : PowerSeries 𝒪[K])) (h := 1)
    (by rw [map_one]; exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    (by simp)

theorem isDistinguishedAt_of_map {g : 𝒪[K][X]} (hm : g.Monic) {k : ℕ}
    (h : g.map (Ideal.Quotient.mk 𝓂[K]) = X ^ k) : g.IsDistinguishedAt 𝓂[K] := by
  have hk : g.natDegree = k := by
    rw [← hm.natDegree_map (Ideal.Quotient.mk 𝓂[K]), h, natDegree_X_pow]
  refine ⟨⟨fun {i} hi => ?_⟩, hm⟩
  have := congrArg (fun p => p.coeff i) h
  simp only [coeff_map, coeff_X_pow] at this
  rw [← Ideal.Quotient.eq_zero_iff_mem, this]
  simp [show i ≠ k by omega]

/-- The iterate `f^{(n)}`, as in `torsionField`. -/
def polyIter (f : 𝒪[K][X]) (n : ℕ) : 𝒪[K][X] := (fun p => f.comp p)^[n] X

theorem polyIter_succ (f : 𝒪[K][X]) (n : ℕ) : polyIter f (n + 1) = f.comp (polyIter f n) := by
  rw [polyIter, polyIter, Function.iterate_succ_apply']

theorem polyIter_zero (f : 𝒪[K][X]) : polyIter f 0 = X := rfl

/-- Iterates of a distinguished polynomial of positive degree are distinguished. -/
theorem polyIter_distinguished {f : 𝒪[K][X]} (hf : f.IsDistinguishedAt 𝓂[K]) (hd : f.natDegree ≠ 0)
    (n : ℕ) : (polyIter f n).IsDistinguishedAt 𝓂[K] ∧ (polyIter f n).natDegree ≠ 0 := by
  induction n with
  | zero =>
    rw [polyIter_zero]
    refine ⟨isDistinguishedAt_of_map monic_X (k := 1) (by simp), by simp⟩
  | succ n ih =>
    obtain ⟨hp, hpd⟩ := ih
    rw [polyIter_succ]
    have hmon : (f.comp (polyIter f n)).Monic := hf.monic.comp hp.monic hpd
    refine ⟨isDistinguishedAt_of_map hmon (k := (polyIter f n).natDegree * f.natDegree) ?_, ?_⟩
    · rw [Polynomial.map_comp, hf.map_eq_X_pow, hp.map_eq_X_pow, Polynomial.X_pow_comp, ← pow_mul]
    · rw [natDegree_comp]; exact mul_ne_zero hd hpd

theorem natDegree_ne_zero_of_mem {π : 𝒪[K]} {f : 𝒪[K][X]} (hf : (f : PowerSeries 𝒪[K]) ∈ lubinTateSeries π (resCard K))
    (hfd : f.IsDistinguishedAt 𝓂[K]) : f.natDegree ≠ 0 := by
  intro h
  have h1 := Polynomial.eq_one_of_monic_natDegree_zero hfd.monic h
  have := hf.1
  rw [h1] at this
  simp at this

theorem coe_comp (f p : 𝒪[K][X]) (hp : PowerSeries.constantCoeff (p : PowerSeries 𝒪[K]) = 0) :
    ((f.comp p : 𝒪[K][X]) : PowerSeries 𝒪[K]) = (f : PowerSeries 𝒪[K]).subst (p : PowerSeries 𝒪[K]) := by
  rw [PowerSeries.subst_coe (PowerSeries.HasSubst.of_constantCoeff_zero' hp), Polynomial.comp_eq_aeval]
  exact (Polynomial.aeval_algHom_apply (Polynomial.coeToPowerSeries.algHom 𝒪[K]) p f).symm

theorem constantCoeff_polyIter {f : 𝒪[K][X]} (hf : PowerSeries.constantCoeff (f : PowerSeries 𝒪[K]) = 0)
    (n : ℕ) : PowerSeries.constantCoeff ((polyIter f n : 𝒪[K][X]) : PowerSeries 𝒪[K]) = 0 := by
  induction n with
  | zero => simp [polyIter_zero]
  | succ n ih =>
    rw [polyIter_succ, coe_comp _ _ ih]
    exact PowerSeries.constantCoeff_subst_eq_zero ih _ hf

theorem polyIter_subst {f g : 𝒪[K][X]} (hf : PowerSeries.constantCoeff (f : PowerSeries 𝒪[K]) = 0)
    (hg : PowerSeries.constantCoeff (g : PowerSeries 𝒪[K]) = 0) {φ : PowerSeries 𝒪[K]}
    (hφ : PowerSeries.constantCoeff φ = 0)
    (h : (g : PowerSeries 𝒪[K]).subst φ = φ.subst (f : PowerSeries 𝒪[K])) (n : ℕ) :
    ((polyIter g n : 𝒪[K][X]) : PowerSeries 𝒪[K]).subst φ =
      φ.subst ((polyIter f n : 𝒪[K][X]) : PowerSeries 𝒪[K]) := by
  have hφs := PowerSeries.HasSubst.of_constantCoeff_zero' hφ
  induction n with
  | zero =>
    rw [polyIter_zero, polyIter_zero, Polynomial.coe_X, PowerSeries.subst_X hφs, PowerSeries.X_subst]
  | succ n ih =>
    have hGs := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_polyIter hg n)
    have hFs := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_polyIter hf n)
    have hfs := PowerSeries.HasSubst.of_constantCoeff_zero' hf
    rw [polyIter_succ, polyIter_succ, coe_comp _ _ (constantCoeff_polyIter hg n),
      coe_comp _ _ (constantCoeff_polyIter hf n), PowerSeries.subst_comp_subst_apply hGs hφs, ih,
      ← PowerSeries.subst_comp_subst_apply hφs hFs, h, PowerSeries.subst_comp_subst_apply hfs hFs]

end Aux

section Main

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- One inclusion: `K[Λ_{g,n}] ≤ K[Λ_{f,n}]`. -/
theorem torsionField_le {π : 𝒪[K]} (hπ : Irreducible π) {f g : 𝒪[K][X]}
    (hf : (f : PowerSeries 𝒪[K]) ∈ lubinTateSeries π (resCard K)) (hfd : f.IsDistinguishedAt 𝓂[K])
    (hg : (g : PowerSeries 𝒪[K]) ∈ lubinTateSeries π (resCard K)) (hgd : g.IsDistinguishedAt 𝓂[K])
    (n : ℕ) : torsionField Ω g n ≤ torsionField Ω f n := by
  have H := lubinTateHyp_of_isNonarchimedeanLocalField K hπ
  have hFd := (polyIter_distinguished hfd (natDegree_ne_zero_of_mem hf hfd) n).1
  have hGd := (polyIter_distinguished hgd (natDegree_ne_zero_of_mem hg hgd) n).1
  unfold torsionField
  change IntermediateField.adjoin K (((polyIter g n).map (algebraMap 𝒪[K] K)).rootSet Ω) ≤
    IntermediateField.adjoin K (((polyIter f n).map (algebraMap 𝒪[K] K)).rootSet Ω)
  rw [IntermediateField.adjoin_le_iff]
  intro β hβ
  have hβ' := ((Polynomial.mem_rootSet).1 hβ).2
  obtain ⟨φ0, φ1, φ2⟩ := lubinTateSeriesHom_spec H hf hg 1
  obtain ⟨ψ0, ψ1, ψ2⟩ := lubinTateSeriesHom_spec H hg hf 1
  set φ := lubinTateSeriesHom H hf hg 1
  set ψ := lubinTateSeriesHom H hg hf 1
  have hφψ : φ.subst ψ = PowerSeries.X := by
    have := lubinTateSeriesHom_mul H hg hf hg 1 1
    rw [mul_one, lubinTateSeriesHom_self_one] at this
    exact this.symm
  obtain ⟨EG, hEG⟩ := exists_isEvAt hGd hβ'
  have hcomp : ((polyIter f n : 𝒪[K][X]) : PowerSeries 𝒪[K]).subst ψ =
      ψ.subst ((polyIter g n : 𝒪[K][X]) : PowerSeries 𝒪[K]) := polyIter_subst hg.1 hf.1 ψ0 ψ2 n
  have hα := aeval_eval_root ψ0 (constantCoeff_polyIter hg.1 n) hcomp hEG hβ'
  obtain ⟨EF, hEF⟩ := exists_isEvAt hFd hα
  have hEq : EF = EG.comp (PowerSeries.substAlgHom (R := 𝒪[K]) (S := 𝒪[K])
      (PowerSeries.HasSubst.of_constantCoeff_zero' ψ0) :
        PowerSeries 𝒪[K] →ₐ[𝒪[K]] PowerSeries 𝒪[K]).toRingHom :=
    hEF.eq (isEvAt_comp hEG ψ0) (residue_ne_zero hFd) hα
  have hβeq : EF φ = β := by
    rw [hEq]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, PowerSeries.coe_substAlgHom]
    rw [hφψ, hEG.2]
  have hαmem : EG ψ ∈ IntermediateField.adjoin K
      (((polyIter f n).map (algebraMap 𝒪[K] K)).rootSet Ω) :=
    IntermediateField.subset_adjoin K _
      ((Polynomial.mem_rootSet).2 ⟨(hFd.monic.map _).ne_zero, hα⟩)
  rw [← hβeq]
  exact hEF.mem (residue_ne_zero hFd) hα _ hαmem φ

end Main

section Final

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **$K[\Lambda_{f,n}]$ does not depend on $f$** (Milne, *CFT*, I, §3, p. 36). -/
theorem torsionFieldIndependence : TorsionFieldIndependence K Ω where
  eq := fun {_} hπ _ _ hf hfd hg hgd n =>
    le_antisymm (torsionField_le hπ hg hgd hf hfd n) (torsionField_le hπ hf hfd hg hgd n)

end Final


end NumberFieldKB.MilneCFT.LocalCFT
