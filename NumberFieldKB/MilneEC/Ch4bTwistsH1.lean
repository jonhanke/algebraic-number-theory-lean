import Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.LocallyConstant.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch4bTwists
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Milne, Elliptic Curves, Chapter IV §7: Theorem 7.15 (twists and nonabelian Galois cohomology)

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, §7, pdf p. 148.  Conventions as in
`NumberFieldKB.MilneEC.Ch4bTwists`: characteristic not $2$ or $3$, $E_0 = E(a,b)$, isomorphisms are changes of
variables, $k$ perfect, $k^{\mathrm{al}}$ = `AlgebraicClosure k`, $\Gamma = \operatorname{Gal}(k^{\mathrm{al}}/k)$ with
the Krull topology.

## Named statement
* `Example1_8a`: Hilbert's Theorem 90 for $\Gamma$ (proved in Chapter IV §1 as `example_1_8_a`).

## Proved
* `theorem_7_15_injective` (unconditional), `theorem_7_15_surjective` and `theorem_7_15` (from `Example1_8a`): $E \mapsto [\alpha]$ is a bijection from twists of $E_0$ modulo isomorphism over $k$ onto
  $H^1(\Gamma, \operatorname{Aut}_{k^{\mathrm{al}}}(E_0, O))$ (Remark 7.20's nonabelian $H^1$).
-/

open WeierstrassCurve

namespace NumberFieldKB.MilneEC

/-! ## Theorem 7.15: twists and $H^1(k, \operatorname{Aut}_{k^{\mathrm{al}}}(E_0))$ -/

section Twists

variable (k : Type*) [Field k] [PerfectField k]

/-- $\operatorname{Gal}(k^{\mathrm{al}}/k)$ acts on changes of variables over $k^{\mathrm{al}}$ through the
coefficients. -/
noncomputable instance galActionVariableChange :
    MulDistribMulAction (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (VariableChange (AlgebraicClosure k)) where
  smul σ C := C.map (σ : AlgebraicClosure k →+* AlgebraicClosure k)
  one_smul C := rfl
  mul_smul σ τ C := rfl
  smul_one σ := (VariableChange.mapHom (σ : AlgebraicClosure k →+* AlgebraicClosure k)).map_one
  smul_mul σ C C' := (VariableChange.mapHom (σ : AlgebraicClosure k →+* AlgebraicClosure k)).map_mul C C'

variable {k}

/-- The action of $\sigma$ on a change of variables is `VariableChange.map`. -/
lemma gal_smul_def (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (C : VariableChange (AlgebraicClosure k)) :
    σ • C = C.map (σ : AlgebraicClosure k →+* AlgebraicClosure k) := rfl

/-- A curve defined over $k$ is fixed by $\Gamma$ after base change. -/
lemma baseChange_map_gal (E₀ : WeierstrassCurve k) (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
    (E₀.baseChange (AlgebraicClosure k)).map (σ : AlgebraicClosure k →+* AlgebraicClosure k) =
      E₀.baseChange (AlgebraicClosure k) := by
  ext <;> simp [WeierstrassCurve.baseChange]

/-- If $C$ carries $E_0$ to $E$ (both over $k$) then so does ${}^\sigma C$. -/
lemma gal_smul_curve {E₀ E : WeierstrassCurve k} {C : VariableChange (AlgebraicClosure k)}
    (hC : C • E₀.baseChange (AlgebraicClosure k) = E.baseChange (AlgebraicClosure k))
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
    (σ • C) • E₀.baseChange (AlgebraicClosure k) = E.baseChange (AlgebraicClosure k) := by
  have h := congrArg (fun W => W.map (σ : AlgebraicClosure k →+* AlgebraicClosure k)) hC
  rw [← WeierstrassCurve.map_variableChange, baseChange_map_gal, baseChange_map_gal] at h
  exact h

/-- The map $\sigma \mapsto \sigma x$ is locally constant on $\Gamma$ (stabilizers are open). -/
lemma gal_apply_locallyConstant (x : AlgebraicClosure k) :
    IsLocallyConstant (fun σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k => σ x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro σ₀
  refine ⟨(fun σ => σ₀⁻¹ * σ) ⁻¹' (MulAction.stabilizer (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) x : Set _),
    ?_, ?_, ?_⟩
  · exact (stabilizer_isOpen_of_isIntegral x).preimage (continuous_const.mul continuous_id)
  · simp
  · intro σ hσ
    have h : σ₀.symm (σ x) = x := hσ
    exact (AlgEquiv.symm_apply_eq _).1 h

/-- The map $\sigma \mapsto {}^\sigma C$ is locally constant on $\Gamma$. -/
lemma gal_smul_locallyConstant (C : VariableChange (AlgebraicClosure k)) :
    IsLocallyConstant (fun σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k => σ • C) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro σ₀
  have h1 := (gal_apply_locallyConstant (k := k) (C.u : AlgebraicClosure k)).isOpen_fiber (σ₀ C.u)
  have h3 := (gal_apply_locallyConstant (k := k) C.r).isOpen_fiber (σ₀ C.r)
  have h4 := (gal_apply_locallyConstant (k := k) C.s).isOpen_fiber (σ₀ C.s)
  have h5 := (gal_apply_locallyConstant (k := k) C.t).isOpen_fiber (σ₀ C.t)
  refine ⟨_, (((h1.inter h3).inter h4).inter h5), ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  rintro σ ⟨⟨⟨e1, e3⟩, e4⟩, e5⟩
  replace e1 : σ C.u = σ₀ C.u := e1
  replace e3 : σ C.r = σ₀ C.r := e3
  replace e4 : σ C.s = σ₀ C.s := e4
  replace e5 : σ C.t = σ₀ C.t := e5
  rw [gal_smul_def, gal_smul_def]
  have hu : (Units.map (σ : AlgebraicClosure k →* AlgebraicClosure k) C.u) =
      Units.map (σ₀ : AlgebraicClosure k →* AlgebraicClosure k) C.u := Units.ext (by simpa using e1)
  exact VariableChange.ext hu (by simpa using e3) (by simpa using e4) (by simpa using e5)


/-- **$\operatorname{Aut}_{k^{\mathrm{al}}}(E_0, O)$** (pdf p. 147): the changes of variables over $k^{\mathrm{al}}$
fixing $E_0$. -/
noncomputable abbrev AutAl (E₀ : WeierstrassCurve k) : Subgroup (VariableChange (AlgebraicClosure k)) :=
  AutO (E₀.baseChange (AlgebraicClosure k))

/-- $\Gamma$ acts on $\operatorname{Aut}_{k^{\mathrm{al}}}(E_0, O)$ ($E_0$ is defined over $k$). -/
noncomputable instance (E₀ : WeierstrassCurve k) :
    MulDistribMulAction (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (AutAl E₀) where
  smul σ C := ⟨σ • (C : VariableChange (AlgebraicClosure k)),
    MulAction.mem_stabilizer_iff.2 (gal_smul_curve (E := E₀) (MulAction.mem_stabilizer_iff.1 C.2) σ)⟩
  one_smul C := Subtype.ext (one_smul _ _)
  mul_smul σ τ C := Subtype.ext (mul_smul σ τ (C : VariableChange (AlgebraicClosure k)))
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ C C' := Subtype.ext (smul_mul' σ (C : VariableChange (AlgebraicClosure k)) C')

/-- An elliptic curve $E$ over $k$ is a **twist** of $E_0$ (pdf p. 146) if it becomes isomorphic to $E_0$ over
$k^{\mathrm{al}}$. -/
noncomputable def IsTwist (E₀ E : WeierstrassCurve k) : Prop :=
  ∃ C : VariableChange (AlgebraicClosure k),
    C • E₀.baseChange (AlgebraicClosure k) = E.baseChange (AlgebraicClosure k)

/-- The crossed homomorphism $\alpha(\sigma) = \varphi^{-1} \circ {}^\sigma\varphi$ of a twist, for an isomorphism
$\varphi : E_0 \to E$ over $k^{\mathrm{al}}$ (pdf p. 148). -/
noncomputable def twistCocycle (E₀ E : WeierstrassCurve k) (C : VariableChange (AlgebraicClosure k))
    (hC : C • E₀.baseChange (AlgebraicClosure k) = E.baseChange (AlgebraicClosure k)) :
    {f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → AutAl E₀ //
      IsContCrossedHom (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (AutAl E₀) f} :=
  ⟨fun σ => ⟨C⁻¹ * σ • C, by
      refine MulAction.mem_stabilizer_iff.2 ?_
      rw [mul_smul, gal_smul_curve hC σ, ← hC, inv_smul_smul]⟩,
    fun σ τ => Subtype.ext (by
      show C⁻¹ * (σ * τ) • C = (C⁻¹ * σ • C) * (σ • (C⁻¹ * τ • C))
      simp [smul_mul', smul_inv', mul_smul, mul_assoc]),
    by
      rw [IsLocallyConstant.iff_exists_open]
      intro σ₀
      obtain ⟨U, hU, h0, hc⟩ := (IsLocallyConstant.iff_exists_open _).1 (gal_smul_locallyConstant C) σ₀
      exact ⟨U, hU, h0, fun σ hσ => Subtype.ext (by simp only [hc σ hσ])⟩⟩

/-- **The class $[\alpha] \in H^1(\Gamma, \operatorname{Aut}_{k^{\mathrm{al}}}(E_0, O))$ of a twist** (pdf p. 148),
computed with a chosen isomorphism (a different choice gives an equivalent crossed homomorphism). -/
noncomputable def twistClass (E₀ E : WeierstrassCurve k) (h : IsTwist E₀ E) :
    NonabelianH1 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (AutAl E₀) :=
  Quotient.mk _ (twistCocycle E₀ E h.choose h.choose_spec)

variable (k) in
/-- **Example 1.8(a)** for $k^{\mathrm{al}}$ (named statement; Milne, pdf p. 114, Hilbert's Theorem 90 for the absolute
Galois group of a perfect field): every continuous crossed homomorphism $\Gamma \to k^{\mathrm{al}\times}$ is
principal.  Chapter IV §1 proves it as `example_1_8_a`. -/
@[kb "milne2006ec" "Ch. IV, Example 1.8(a), pdf p. 114 (input)"]
structure Example1_8a : Prop where
  principal : ∀ f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → AlgebraicClosure k, (∀ σ, f σ ≠ 0) →
    (∀ σ τ, f (σ * τ) = σ (f τ) * f σ) → IsLocallyConstant f →
      ∃ u : AlgebraicClosure k, u ≠ 0 ∧ ∀ σ, f σ = σ u / u

/-- Two isomorphisms $E_0 \to E$ over $k^{\mathrm{al}}$ give equivalent crossed homomorphisms. -/
lemma twistCocycle_equiv {E₀ E : WeierstrassCurve k} {C C₁ : VariableChange (AlgebraicClosure k)}
    (hC : C • E₀.baseChange (AlgebraicClosure k) = E.baseChange (AlgebraicClosure k))
    (hC₁ : C₁ • E₀.baseChange (AlgebraicClosure k) = E.baseChange (AlgebraicClosure k)) :
    Quotient.mk (crossedHomSetoid (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (AutAl E₀))
        (twistCocycle E₀ E C hC) =
      Quotient.mk _ (twistCocycle E₀ E C₁ hC₁) := by
  refine Quotient.sound ?_
  refine ⟨⟨C⁻¹ * C₁, MulAction.mem_stabilizer_iff.2 ?_⟩, fun σ => Subtype.ext ?_⟩
  · rw [mul_smul, hC₁, ← hC, inv_smul_smul]
  · show C₁⁻¹ * σ • C₁ = (C⁻¹ * C₁)⁻¹ * (C⁻¹ * σ • C) * σ • (C⁻¹ * C₁)
    simp [smul_mul', smul_inv', mul_assoc]

/-- The class of a twist can be computed with any isomorphism. -/
lemma twistClass_eq_mk {E₀ E : WeierstrassCurve k} (h : IsTwist E₀ E) {C : VariableChange (AlgebraicClosure k)}
    (hC : C • E₀.baseChange (AlgebraicClosure k) = E.baseChange (AlgebraicClosure k)) :
    twistClass E₀ E h = Quotient.mk _ (twistCocycle E₀ E C hC) :=
  twistCocycle_equiv h.choose_spec hC

/-- Descent: a change of variables over $k^{\mathrm{al}}$ fixed by $\Gamma$ has coefficients in $k$. -/
lemma exists_baseChange_of_gal_fixed (D : VariableChange (AlgebraicClosure k))
    (h : ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, σ • D = D) :
    ∃ D₀ : VariableChange k, D₀.baseChange (AlgebraicClosure k) = D := by
  have hfix : ∀ x : AlgebraicClosure k, (∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, σ x = x) →
      ∃ y : k, algebraMap k (AlgebraicClosure k) y = x := fun x hx =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hx
  obtain ⟨x, hx⟩ := hfix (D.u : AlgebraicClosure k)
    (fun σ => congrArg (fun C : VariableChange (AlgebraicClosure k) => (C.u : AlgebraicClosure k)) (h σ))
  obtain ⟨r, hr⟩ := hfix D.r (fun σ => congrArg (fun C : VariableChange (AlgebraicClosure k) => C.r) (h σ))
  obtain ⟨s, hs⟩ := hfix D.s (fun σ => congrArg (fun C : VariableChange (AlgebraicClosure k) => C.s) (h σ))
  obtain ⟨t, ht⟩ := hfix D.t (fun σ => congrArg (fun C : VariableChange (AlgebraicClosure k) => C.t) (h σ))
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hx
    exact D.u.ne_zero hx.symm
  exact ⟨⟨Units.mk0 x hx0, r, s, t⟩, VariableChange.ext (Units.ext (by simpa [VariableChange.baseChange] using hx))
    (by simpa [VariableChange.baseChange] using hr) (by simpa [VariableChange.baseChange] using hs)
    (by simpa [VariableChange.baseChange] using ht)⟩

/-- A base change from $k$ is fixed by $\Gamma$. -/
lemma gal_smul_baseChange (D₀ : VariableChange k) (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
    σ • D₀.baseChange (AlgebraicClosure k) = D₀.baseChange (AlgebraicClosure k) :=
  VariableChange.map_baseChange (S := k) D₀ σ.toAlgHom

/-- Base change commutes with the action of changes of variables. -/
lemma baseChange_smul (D₀ : VariableChange k) (E : WeierstrassCurve k) :
    D₀.baseChange (AlgebraicClosure k) • E.baseChange (AlgebraicClosure k) =
      (D₀ • E).baseChange (AlgebraicClosure k) :=
  WeierstrassCurve.map_variableChange (W := E) (C := D₀) (φ := algebraMap k (AlgebraicClosure k))

/-- **Theorem 7.15, injectivity** (pdf p. 148), characteristic not $2$ or $3$, $k$ perfect: two twists of
$E_0 = E(a,b)$ have the same class in $H^1(\Gamma, \operatorname{Aut}_{k^{\mathrm{al}}}(E_0, O))$ if and only if they
are isomorphic over $k$ (Milne: "the proof is similar to that of Theorem 7.8"; the descent step is that a change of
variables over $k^{\mathrm{al}}$ fixed by $\Gamma$ has coefficients in $k$). -/
@[kb "milne2006ec" "Ch. IV, Theorem 7.15, pdf p. 148"]
theorem theorem_7_15_injective [NeZero (2 : k)] [NeZero (3 : k)] (a b : k) [(shortW a b).IsElliptic]
    (E E' : WeierstrassCurve k) (h : IsTwist (shortW a b) E) (h' : IsTwist (shortW a b) E') :
    twistClass _ E h = twistClass _ E' h' ↔ ∃ C : VariableChange k, C • E = E' := by
  constructor
  · intro heq
    obtain ⟨m, hm⟩ := Quotient.exact (s := crossedHomSetoid _ _) heq
    set C := h.choose with hCdef
    set C' := h'.choose with hC'def
    have hC := h.choose_spec
    have hC' := h'.choose_spec
    have key : ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
        C'⁻¹ * σ • C' = (m : VariableChange (AlgebraicClosure k))⁻¹ * (C⁻¹ * σ • C) *
          σ • (m : VariableChange (AlgebraicClosure k)) := fun σ => congrArg Subtype.val (hm σ)
    have hm' : (m : VariableChange (AlgebraicClosure k)) • (shortW a b).baseChange (AlgebraicClosure k) =
        (shortW a b).baseChange (AlgebraicClosure k) := MulAction.mem_stabilizer_iff.1 m.2
    set D : VariableChange (AlgebraicClosure k) := C' * (m : VariableChange (AlgebraicClosure k))⁻¹ * C⁻¹ with hD
    have hfix : ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, σ • D = D := by
      intro σ
      have e : σ • C' = C' * ((m : VariableChange (AlgebraicClosure k))⁻¹ * (C⁻¹ * σ • C) *
          σ • (m : VariableChange (AlgebraicClosure k))) := by
        rw [← key σ]; simp
      rw [hD]
      simp only [smul_mul', smul_inv']
      rw [e]
      group
    obtain ⟨D₀, hD₀⟩ := exists_baseChange_of_gal_fixed D hfix
    refine ⟨D₀, ?_⟩
    apply WeierstrassCurve.map_injective (algebraMap k (AlgebraicClosure k)).injective
    show (D₀ • E).baseChange (AlgebraicClosure k) = E'.baseChange (AlgebraicClosure k)
    rw [← baseChange_smul, hD₀, hD, mul_smul, mul_smul, inv_smul_eq_iff.2 hC.symm, ← hC',
      inv_smul_eq_iff.2 hm'.symm]
  · rintro ⟨D₀, hD₀⟩
    have hC := h.choose_spec
    have hC1 : (D₀.baseChange (AlgebraicClosure k) * h.choose) • (shortW a b).baseChange (AlgebraicClosure k) =
        E'.baseChange (AlgebraicClosure k) := by
      rw [mul_smul, hC, baseChange_smul, hD₀]
    rw [twistClass_eq_mk h hC, twistClass_eq_mk h' hC1]
    refine congrArg _ (Subtype.ext (funext fun σ => Subtype.ext ?_))
    show h.choose⁻¹ * σ • h.choose = (D₀.baseChange (AlgebraicClosure k) * h.choose)⁻¹ *
      σ • (D₀.baseChange (AlgebraicClosure k) * h.choose)
    rw [smul_mul', gal_smul_baseChange]
    group

/-- $2 \neq 0$ in $k^{\mathrm{al}}$ when $2 \neq 0$ in $k$. -/
lemma two_ne_zero_alg [NeZero (2 : k)] : (2 : AlgebraicClosure k) ≠ 0 := by
  intro h
  apply two_ne_zero (α := k)
  apply (algebraMap k (AlgebraicClosure k)).injective
  rw [map_ofNat, h, map_zero]

/-- $3 \neq 0$ in $k^{\mathrm{al}}$ when $3 \neq 0$ in $k$. -/
lemma three_ne_zero_alg [NeZero (3 : k)] : (3 : AlgebraicClosure k) ≠ 0 := by
  intro h
  apply NeZero.ne (3 : k)
  apply (algebraMap k (AlgebraicClosure k)).injective
  rw [map_ofNat, h, map_zero]

/-- An automorphism of $E(a,b)$ over $k^{\mathrm{al}}$ (characteristic not $2$ or $3$) has $r = s = t = 0$. -/
lemma aut_shortW_rst [NeZero (2 : k)] [NeZero (3 : k)] (a b : k) (m : AutAl (shortW a b)) :
    (m : VariableChange (AlgebraicClosure k)).r = 0 ∧ (m : VariableChange (AlgebraicClosure k)).s = 0 ∧
      (m : VariableChange (AlgebraicClosure k)).t = 0 := by
  have h := MulAction.mem_stabilizer_iff.1 m.2
  have hb : (shortW a b).baseChange (AlgebraicClosure k) =
      shortW (algebraMap k (AlgebraicClosure k) a) (algebraMap k (AlgebraicClosure k) b) := by
    ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map, shortW]
  rw [hb] at h
  have h2 := two_ne_zero_alg (k := k)
  have h3 := three_ne_zero_alg (k := k)
  have h1 := congrArg WeierstrassCurve.a₁ h
  have h1' := congrArg WeierstrassCurve.a₂ h
  have h1'' := congrArg WeierstrassCurve.a₃ h
  rw [variableChange_a₁] at h1
  rw [variableChange_a₂] at h1'
  rw [variableChange_a₃] at h1''
  simp [shortW, h2] at h1
  simp [shortW, h1, h3] at h1'
  simp [shortW, h1, h1', h2] at h1''
  exact ⟨h1', h1, h1''⟩

/-- Descent for curves: a Weierstrass curve over $k^{\mathrm{al}}$ fixed by $\Gamma$ is defined over $k$. -/
lemma exists_baseChange_curve_of_gal_fixed (W : WeierstrassCurve (AlgebraicClosure k))
    (h : ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, W.map (σ : AlgebraicClosure k →+* AlgebraicClosure k) = W) :
    ∃ W₀ : WeierstrassCurve k, W₀.baseChange (AlgebraicClosure k) = W := by
  have hfix : ∀ x : AlgebraicClosure k, (∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, σ x = x) →
      ∃ y : k, algebraMap k (AlgebraicClosure k) y = x := fun x hx =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hx
  obtain ⟨x1, h1⟩ := hfix W.a₁ (fun σ => congrArg WeierstrassCurve.a₁ (h σ))
  obtain ⟨x2, h2⟩ := hfix W.a₂ (fun σ => congrArg WeierstrassCurve.a₂ (h σ))
  obtain ⟨x3, h3⟩ := hfix W.a₃ (fun σ => congrArg WeierstrassCurve.a₃ (h σ))
  obtain ⟨x4, h4⟩ := hfix W.a₄ (fun σ => congrArg WeierstrassCurve.a₄ (h σ))
  obtain ⟨x6, h6⟩ := hfix W.a₆ (fun σ => congrArg WeierstrassCurve.a₆ (h σ))
  exact ⟨⟨x1, x2, x3, x4, x6⟩, by ext <;> simp [WeierstrassCurve.baseChange, h1, h2, h3, h4, h6]⟩

/-- **Theorem 7.15, surjectivity** (pdf p. 148), from Hilbert's Theorem 90 (`Example1_8a`): every class in
$H^1(\Gamma, \operatorname{Aut}_{k^{\mathrm{al}}}(E_0, O))$ is the class of a twist of $E_0 = E(a,b)$.
($\operatorname{Aut}_{k^{\mathrm{al}}}(E_0, O) = \mu_n$, $n \in \{2, 4, 6\}$, acting through $u$; Hilbert 90 writes the
cocycle as $\sigma u_0/u_0$ and the twist is $E(u_0^{-4}a, u_0^{-6}b)$, whose coefficients lie in $k$.) -/
@[kb "milne2006ec" "Ch. IV, Theorem 7.15, pdf p. 148"]
theorem theorem_7_15_surjective [NeZero (2 : k)] [NeZero (3 : k)] (hH90 : Example1_8a k) (a b : k)
    [(shortW a b).IsElliptic]
    (c : NonabelianH1 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (AutAl (shortW a b))) :
    ∃ (E : WeierstrassCurve k) (h : IsTwist (shortW a b) E), twistClass _ E h = c := by
  induction c using Quotient.inductionOn with
  | _ α =>
  have hrst := fun σ => aut_shortW_rst a b (α.1 σ)
  let f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → AlgebraicClosure k :=
    fun σ => ((α.1 σ : VariableChange (AlgebraicClosure k)).u : AlgebraicClosure k)
  have hf0 : ∀ σ, f σ ≠ 0 := fun σ => Units.ne_zero _
  have hfm : ∀ σ τ, f (σ * τ) = σ (f τ) * f σ := by
    intro σ τ
    have h := congrArg (fun m : AutAl (shortW a b) => ((m : VariableChange (AlgebraicClosure k)).u : AlgebraicClosure k))
      (α.2.1 σ τ)
    rw [mul_comm]
    exact h
  have hlc : IsLocallyConstant f :=
    α.2.2.comp (fun m : AutAl (shortW a b) => ((m : VariableChange (AlgebraicClosure k)).u : AlgebraicClosure k))
  obtain ⟨u₀, hu₀, hfu⟩ := hH90.principal f hf0 hfm hlc
  let C : VariableChange (AlgebraicClosure k) := ⟨Units.mk0 u₀ hu₀, 0, 0, 0⟩
  have hαC : ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      C⁻¹ * σ • C = (α.1 σ : VariableChange (AlgebraicClosure k)) := by
    intro σ
    obtain ⟨hr, hs, ht⟩ := hrst σ
    have hfs : ((α.1 σ : VariableChange (AlgebraicClosure k)).u : AlgebraicClosure k) = σ u₀ / u₀ := hfu σ
    refine VariableChange.ext (Units.ext ?_) ?_ ?_ ?_
    · show (u₀)⁻¹ * σ u₀ = _
      rw [hfs]; ring
    · simp [C, hr, VariableChange.mul_def, VariableChange.inv_def, gal_smul_def]
    · simp [C, hs, VariableChange.mul_def, VariableChange.inv_def, gal_smul_def]
    · simp [C, ht, VariableChange.mul_def, VariableChange.inv_def, gal_smul_def]
  have hfixW : ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      (C • (shortW a b).baseChange (AlgebraicClosure k)).map (σ : AlgebraicClosure k →+* AlgebraicClosure k) =
        C • (shortW a b).baseChange (AlgebraicClosure k) := by
    intro σ
    have h0 := MulAction.mem_stabilizer_iff.1 (α.1 σ).2
    rw [← hαC σ, mul_smul] at h0
    have h1 : (σ • C) • (shortW a b).baseChange (AlgebraicClosure k) =
        C • (shortW a b).baseChange (AlgebraicClosure k) := inv_smul_eq_iff.1 h0
    rw [← WeierstrassCurve.map_variableChange, baseChange_map_gal]
    exact h1
  obtain ⟨E, hE⟩ := exists_baseChange_curve_of_gal_fixed _ hfixW
  have hC : C • (shortW a b).baseChange (AlgebraicClosure k) = E.baseChange (AlgebraicClosure k) := hE.symm
  refine ⟨E, ⟨C, hC⟩, ?_⟩
  rw [twistClass_eq_mk ⟨C, hC⟩ hC]
  exact congrArg _ (Subtype.ext (funext fun σ => Subtype.ext (hαC σ)))

/-- **Theorem 7.15** (pdf p. 148), characteristic not $2$ or $3$, $k$ perfect: $E \mapsto [\alpha]$ is a one-to-one
correspondence between elliptic curves over $k$ isomorphic to $E_0$ over $k^{\mathrm{al}}$, modulo isomorphism over
$k$, and $H^1(\Gamma, \operatorname{Aut}_{k^{\mathrm{al}}}(E_0, O))$, given Hilbert's Theorem 90 (`Example1_8a`).
$E_0 = E(a,b)$ by Milne's convention. -/
@[kb "milne2006ec" "Ch. IV, Theorem 7.15, pdf p. 148"]
theorem theorem_7_15 [NeZero (2 : k)] [NeZero (3 : k)] (hH90 : Example1_8a k) (a b : k) [(shortW a b).IsElliptic] :
    (∀ (E E' : WeierstrassCurve k) (h : IsTwist (shortW a b) E) (h' : IsTwist (shortW a b) E'),
      twistClass _ E h = twistClass _ E' h' ↔ ∃ C : VariableChange k, C • E = E') ∧
    (∀ c : NonabelianH1 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (AutAl (shortW a b)),
      ∃ (E : WeierstrassCurve k) (h : IsTwist (shortW a b) E), twistClass _ E h = c) :=
  ⟨theorem_7_15_injective a b, theorem_7_15_surjective hH90 a b⟩

end Twists

end NumberFieldKB.MilneEC
