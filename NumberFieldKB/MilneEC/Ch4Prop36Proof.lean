import NumberFieldKB.MilneEC.Ch4Lemma35
import NumberFieldKB.MilneEC.Ch4DivPointsGeneral
import NumberFieldKB.MilneEC.Ch4Prop36
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Milne, *Elliptic Curves*, Chapter IV, Proposition 3.6 for $p \ge 5$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, Proposition 3.6 (pdf p. 120).

**Proof, at the level of cocycles.**  Let $\gamma \in S^{(n)}(E/\mathbb Q)$ be the class of a crossed homomorphism
$c : G_{\mathbb Q} \to E_n(\bar{\mathbb Q})$.
1. The Selmer group is defined with the completions `adicCompletion ℚ v`; `Padic.adicCompletionEquiv` (Mathlib)
   identifies the one at $p$ with $\mathbb Q_p$ over $\mathbb Q$.  Vanishing of a localization does not depend on the
   local field up to $\mathbb Q$-isomorphism (`locTorsion_eq_zero_of_algEquiv`): two $\mathbb Q$-embeddings
   $\bar{\mathbb Q} \to \bar{\mathbb Q}_p$ differ by $\tau \in G_{\mathbb Q}$ (`exists_algEquiv_comp_eq`), and
   $c(\tau g \tau^{-1}) = \tau c(g) + c(\tau) - \tau g \tau^{-1} c(\tau)$ differs from $\tau c(g)$ by a coboundary.
2. So there is $R \in E(\bar{\mathbb Q}_p)$ with $\iota\, c(\mathrm{dec}\,\sigma) = \sigma R - R$ for all
   $\sigma \in G_{\mathbb Q_p}$ (`locTorsion_eq_zero_iff`).  Then $\sigma(nR) = nR$, so $nR = P \in E(\mathbb Q_p)$.
3. By `exists_unramified_divPoints` there is a finite unramified $K$ containing every $Q$ with $nQ = P$, in
   particular $R$ and $E_n(\bar{\mathbb Q}_p)$.  For $\sigma \in G_K$: $\sigma R = R$, so $c(\mathrm{dec}\,\sigma) = 0$,
   and $\mathrm{dec}\,\sigma$ fixes $E_n(\bar{\mathbb Q})$.

The local model: a curve $W$ over $\mathbb Q$ and an integral model $W_0$ over $\mathbb Z_p$ with unit discriminant
and the same base change to $\mathbb Q_p$.
-/

namespace NumberFieldKB.MilneEC

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

set_option backward.isDefEq.respectTransparency false

/-- Two embeddings over $K$ of an algebraic closure of $K$ into an algebraically closed field differ by an
automorphism. -/
theorem exists_algEquiv_comp_eq {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (i j : AlgebraicClosure K →ₐ[K] Ω) :
    ∃ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, j = i.comp (τ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) := by
  letI : Algebra (AlgebraicClosure K) Ω := i.toRingHom.toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K) Ω := IsScalarTower.of_algebraMap_eq fun x => (i.commutes x).symm
  have hmem : ∀ x, ∃ y, i y = j x := by
    intro x
    have hint : IsIntegral K (j x) := (Algebra.IsIntegral.isIntegral x).map j
    have hint' : IsIntegral (AlgebraicClosure K) (j x) := hint.tower_top
    haveI : FiniteDimensional (AlgebraicClosure K) (IntermediateField.adjoin (AlgebraicClosure K) {j x}) :=
      IntermediateField.adjoin.finiteDimensional hint'
    have h0 := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
      (IntermediateField.adjoin (AlgebraicClosure K) {j x})
    have : j x ∈ IntermediateField.adjoin (AlgebraicClosure K) {j x} :=
      IntermediateField.mem_adjoin_simple_self _ _
    rw [h0, IntermediateField.mem_bot] at this
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩
  choose f hf using hmem
  let τ0 : AlgebraicClosure K →ₐ[K] AlgebraicClosure K :=
    { toFun := f
      map_one' := i.injective (by change i _ = i _; rw [hf, map_one, map_one])
      map_mul' := fun a b => i.injective (by change i _ = i _; rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := i.injective (by change i _ = i _; rw [hf, map_zero, map_zero])
      map_add' := fun a b => i.injective (by change i _ = i _; rw [hf, map_add, map_add, hf, hf])
      commutes' := fun r => i.injective (by change i _ = i _; rw [hf, j.commutes, i.commutes]) }
  refine ⟨AlgEquiv.ofBijective τ0 (Algebra.IsAlgebraic.algHom_bijective τ0), ?_⟩
  exact AlgHom.ext fun x => (hf x).symm


/-- Class of a pulled-back-and-pushed cocycle. -/
theorem map_H1π_res {G H : Type} [Group G] [Group H] (f : G →* H) {A : Rep ℤ H} {B : Rep ℤ G}
    (φ : Rep.res f A ⟶ B) (c : cocycles₁ A) (y : cocycles₁ B)
    (hy : ∀ g, (y : G → B) g = φ.hom (c (f g))) :
    map f φ 1 (H1π A c) = H1π B y := by
  rw [H1π_comp_map_apply]
  congr 1
  exact Subtype.ext (funext fun g => (hy g).symm)

section Local

variable {K : Type} [Field K] (W : WeierstrassCurve K) (n : ℤ)

/-- The localization of the class of a crossed homomorphism vanishes iff the localized crossed homomorphism is a
coboundary. -/
theorem locTorsion_eq_zero_iff (Kv : Type) [Field Kv] [Algebra K Kv]
    (c : cocycles₁ (torsionRep W (AlgebraicClosure K) n)) :
    locTorsion Kv W n (H1π _ c) = 0 ↔
      ∃ R : (W.toAffine⁄(AlgebraicClosure Kv)).Point, ∀ σ : AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv,
        Point.map (W' := W.toAffine) (closureEmb Kv) ((c (decompHom Kv σ) : torsionPoints W _ n) :
            (W.toAffine⁄(AlgebraicClosure K)).Point) =
          Point.map (W' := W.toAffine)
            ((AlgEquiv.restrictScalarsHom K σ : AlgebraicClosure Kv ≃ₐ[K] AlgebraicClosure Kv) :
              AlgebraicClosure Kv →ₐ[K] AlgebraicClosure Kv) R - R := by
  have h := map_H1π_res (decompHom Kv) (localizeTorsion Kv W n) c
    (mapCocycles₁ (decompHom Kv) (localizeTorsion Kv W n) c) (fun g => rfl)
  change map (decompHom Kv) (localizeTorsion Kv W n) 1 (H1π _ c) = 0 ↔ _
  rw [h, H1π_eq_zero_iff]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨R, fun σ => ?_⟩
    have := congrFun hR σ
    exact this.symm
  · rintro ⟨R, hR⟩
    refine ⟨R, funext fun σ => ?_⟩
    exact (hR σ).symm

theorem torsionRep_ρ_val {L : Type} [Field L] [Algebra K L] (g : L ≃ₐ[K] L)
    (P : torsionPoints W L n) :
    (((torsionRep W L n).ρ g P : torsionPoints W L n) : (W.toAffine⁄L).Point) =
      Point.map (W' := W.toAffine) (g : L →ₐ[K] L) (P : (W.toAffine⁄L).Point) := rfl

theorem cocycle_val {L : Type} [Field L] [Algebra K L] (c : cocycles₁ (torsionRep W L n))
    (g h : L ≃ₐ[K] L) :
    ((c (g * h) : torsionPoints W L n) : (W.toAffine⁄L).Point) =
      Point.map (W' := W.toAffine) (g : L →ₐ[K] L) (c h : torsionPoints W L n) +
        ((c g : torsionPoints W L n) : (W.toAffine⁄L).Point) := by
  have := (mem_cocycles₁_iff (A := torsionRep W L n) c).1 c.2 g h
  exact congrArg Subtype.val this

theorem exists_Psi {Kv Kv' : Type} [Field Kv] [Field Kv'] [Algebra K Kv] [Algebra K Kv']
    (ψ : Kv ≃ₐ[K] Kv') :
    ∃ Ψ : AlgebraicClosure Kv ≃ₐ[K] AlgebraicClosure Kv',
      ∀ a : Kv, Ψ (algebraMap Kv (AlgebraicClosure Kv) a) = algebraMap Kv' (AlgebraicClosure Kv') (ψ a) := by
  let e := IsAlgClosure.equivOfEquiv (AlgebraicClosure Kv) (AlgebraicClosure Kv') ψ.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := e) (fun r => ?_), fun a => ?_⟩
  · rw [IsScalarTower.algebraMap_apply K Kv (AlgebraicClosure Kv),
      IsScalarTower.algebraMap_apply K Kv' (AlgebraicClosure Kv')]
    exact (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure Kv) (AlgebraicClosure Kv') ψ.toRingEquiv _).trans
      (by simp)
  · exact IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure Kv) (AlgebraicClosure Kv') ψ.toRingEquiv a

/-- Conjugation of Galois groups along `Ψ`. -/
noncomputable def conjAut {Kv Kv' : Type} [Field Kv] [Field Kv'] [Algebra K Kv] [Algebra K Kv']
    (ψ : Kv ≃ₐ[K] Kv') (Ψ : AlgebraicClosure Kv ≃ₐ[K] AlgebraicClosure Kv')
    (hΨ : ∀ a : Kv, Ψ (algebraMap Kv (AlgebraicClosure Kv) a) = algebraMap Kv' (AlgebraicClosure Kv') (ψ a))
    (σ' : AlgebraicClosure Kv' ≃ₐ[Kv'] AlgebraicClosure Kv') :
    AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv :=
  AlgEquiv.ofRingEquiv (f := (Ψ.toRingEquiv.trans σ'.toRingEquiv).trans Ψ.symm.toRingEquiv) (fun a => by
    show Ψ.symm (σ' (Ψ (algebraMap Kv (AlgebraicClosure Kv) a))) = _
    rw [hΨ, AlgEquiv.commutes]
    rw [← hΨ]; exact Ψ.symm_apply_apply _)

theorem Ψ_conjAut {Kv Kv' : Type} [Field Kv] [Field Kv'] [Algebra K Kv] [Algebra K Kv']
    (ψ : Kv ≃ₐ[K] Kv') (Ψ : AlgebraicClosure Kv ≃ₐ[K] AlgebraicClosure Kv')
    (hΨ : ∀ a : Kv, Ψ (algebraMap Kv (AlgebraicClosure Kv) a) = algebraMap Kv' (AlgebraicClosure Kv') (ψ a))
    (σ' : AlgebraicClosure Kv' ≃ₐ[Kv'] AlgebraicClosure Kv') (x : AlgebraicClosure Kv) :
    Ψ (conjAut ψ Ψ hΨ σ' x) = σ' (Ψ x) := by
  show Ψ (Ψ.symm (σ' (Ψ x))) = _
  exact Ψ.apply_symm_apply _

/-- Vanishing of a localization depends on the local field only up to isomorphism over $K$. -/
theorem locTorsion_eq_zero_of_algEquiv {Kv Kv' : Type} [Field Kv] [Field Kv'] [Algebra K Kv] [Algebra K Kv']
    (ψ : Kv ≃ₐ[K] Kv') (x : H1 (torsionRep W (AlgebraicClosure K) n)) (hx : locTorsion Kv W n x = 0) :
    locTorsion Kv' W n x = 0 := by
  induction x using H1_induction_on with | @h c => ?_
  rw [locTorsion_eq_zero_iff] at hx ⊢
  obtain ⟨R, hR⟩ := hx
  obtain ⟨Ψ, hΨ⟩ := exists_Psi (K := K) ψ
  obtain ⟨τ, hτ⟩ := exists_algEquiv_comp_eq
    ((Ψ : AlgebraicClosure Kv ≃ₐ[K] AlgebraicClosure Kv').toAlgHom.comp (closureEmb (K := K) Kv))
    (closureEmb (K := K) Kv')
  set a : (W.toAffine⁄(AlgebraicClosure K)).Point := ((c τ : torsionPoints W _ n) : (W.toAffine⁄(AlgebraicClosure K)).Point)
    with ha
  have hτ' : ∀ y, closureEmb (K := K) Kv' y = Ψ (closureEmb (K := K) Kv (τ y)) := fun y =>
    congrArg (fun f : AlgebraicClosure K →ₐ[K] AlgebraicClosure Kv' => f y) hτ
  have E1 : ∀ P : (W.toAffine⁄(AlgebraicClosure K)).Point,
      Point.map (W' := W.toAffine) (closureEmb (K := K) Kv')
        (Point.map (W' := W.toAffine) ((τ⁻¹ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →ₐ[K] AlgebraicClosure K) P) =
      Point.map (W' := W.toAffine) (Ψ.toAlgHom) (Point.map (W' := W.toAffine) (closureEmb (K := K) Kv) P) := by
    intro P
    rw [Point.map_map, Point.map_map]
    have e : (closureEmb (K := K) Kv').comp ((τ⁻¹ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →ₐ[K] AlgebraicClosure K) =
        Ψ.toAlgHom.comp (closureEmb (K := K) Kv) := by
      refine AlgHom.ext fun y => ?_
      show closureEmb (K := K) Kv' (τ.symm y) = _
      rw [hτ']
      simp
    rw [e]
  refine ⟨Point.map (W' := W.toAffine) Ψ.toAlgHom R +
    Point.map (W' := W.toAffine) Ψ.toAlgHom (Point.map (W' := W.toAffine) (closureEmb (K := K) Kv) a),
    fun σ' => ?_⟩
  set σ := conjAut ψ Ψ hΨ σ' with hσ
  have hg' : decompHom Kv' σ' = τ⁻¹ * decompHom Kv σ * τ := by
    refine AlgEquiv.ext fun y => (closureEmb (K := K) Kv').injective ?_
    show closureEmb (K := K) Kv' _ = closureEmb (K := K) Kv' (τ.symm (decompHom Kv σ (τ y)))
    rw [closureEmb_decompHom, hτ' (τ.symm _), AlgEquiv.apply_symm_apply, closureEmb_decompHom, Ψ_conjAut, ← hτ']
  have hc1 : ((c (decompHom Kv' σ') : torsionPoints W _ n) : (W.toAffine⁄(AlgebraicClosure K)).Point) =
      Point.map (W' := W.toAffine) ((τ⁻¹ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →ₐ[K] AlgebraicClosure K)
        (Point.map (W' := W.toAffine) ((decompHom Kv σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →ₐ[K] AlgebraicClosure K) a) +
      Point.map (W' := W.toAffine) ((τ⁻¹ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →ₐ[K] AlgebraicClosure K)
        ((c (decompHom Kv σ) : torsionPoints W _ n) : (W.toAffine⁄(AlgebraicClosure K)).Point) -
      Point.map (W' := W.toAffine) ((τ⁻¹ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →ₐ[K] AlgebraicClosure K) a := by
    have h1 := cocycle_val W n c τ⁻¹ (decompHom Kv σ * τ)
    have h2 := cocycle_val W n c (decompHom Kv σ) τ
    have h3 := cocycle_val W n c τ⁻¹ τ
    rw [← mul_assoc] at h1
    rw [inv_mul_cancel, cocycles₁_map_one] at h3
    rw [hg', h1, h2, map_add]
    have : ((c τ⁻¹ : torsionPoints W _ n) : (W.toAffine⁄(AlgebraicClosure K)).Point) =
        - Point.map (W' := W.toAffine) ((τ⁻¹ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →ₐ[K] AlgebraicClosure K) a := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      simpa using h3.symm
    rw [this]; abel
  rw [hc1, map_sub, map_add, E1, E1, E1, localize_map, hR σ]
  have E4 : ∀ Q : (W.toAffine⁄(AlgebraicClosure Kv)).Point,
      Point.map (W' := W.toAffine) Ψ.toAlgHom
        (Point.map (W' := W.toAffine)
          ((AlgEquiv.restrictScalarsHom K σ : AlgebraicClosure Kv ≃ₐ[K] AlgebraicClosure Kv) :
            AlgebraicClosure Kv →ₐ[K] AlgebraicClosure Kv) Q) =
      Point.map (W' := W.toAffine)
        ((AlgEquiv.restrictScalarsHom K σ' : AlgebraicClosure Kv' ≃ₐ[K] AlgebraicClosure Kv') :
          AlgebraicClosure Kv' →ₐ[K] AlgebraicClosure Kv')
        (Point.map (W' := W.toAffine) Ψ.toAlgHom Q) := by
    intro Q
    rw [Point.map_map, Point.map_map]
    have e : Ψ.toAlgHom.comp
          ((AlgEquiv.restrictScalarsHom K σ : AlgebraicClosure Kv ≃ₐ[K] AlgebraicClosure Kv) :
            AlgebraicClosure Kv →ₐ[K] AlgebraicClosure Kv) =
        ((AlgEquiv.restrictScalarsHom K σ' : AlgebraicClosure Kv' ≃ₐ[K] AlgebraicClosure Kv') :
          AlgebraicClosure Kv' →ₐ[K] AlgebraicClosure Kv').comp Ψ.toAlgHom :=
      AlgHom.ext fun y => Ψ_conjAut ψ Ψ hΨ σ' y
    rw [e]
  simp only [map_add, map_sub, E4]
  abel

end Local

theorem ptCast_map_apply {F : Type*} [Field F] [DecidableEq F]
    {R₁ S₁ R₂ S₂ : Type*} [CommRing R₁] [CommRing S₁] [CommRing R₂] [CommRing S₂]
    [Algebra R₁ S₁] [Algebra R₁ F] [Algebra S₁ F] [IsScalarTower R₁ S₁ F]
    [Algebra R₂ S₂] [Algebra R₂ F] [Algebra S₂ F] [IsScalarTower R₂ S₂ F]
    (W₁ : WeierstrassCurve R₁) (W₂ : WeierstrassCurve R₂) (h : W₁.baseChange F = W₂.baseChange F)
    (σ₁ : F →ₐ[S₁] F) (σ₂ : F →ₐ[S₂] F) (hσ : ∀ x, σ₁ x = σ₂ x)
    (P : (W₁.toAffine⁄F).Point) :
    ptCast h (Point.map (W' := W₁.toAffine) σ₁ P) = Point.map (W' := W₂.toAffine) σ₂ (ptCast h P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · show ptCast h (Point.map (W' := W₁.toAffine) σ₁ 0) = Point.map (W' := W₂.toAffine) σ₂ (ptCast h 0)
    rw [map_zero, map_zero, map_zero]
  · obtain ⟨h1, e1⟩ := ptCast_some h hxy
    have hns := (W₁.toAffine.baseChange_nonsingular σ₁.injective x y).2 hxy
    obtain ⟨h2, e2⟩ := ptCast_some h hns
    rw [Point.map_some, e2, e1, Point.map_some]
    simp only [hσ]


section Local5

variable (p : ℕ) [Fact p.Prime]

theorem curve_eq_AC (W : WeierstrassCurve ℚ) (W₀ : WeierstrassCurve ℤ_[p])
    (hW : W.baseChange ℚ_[p] = W₀.baseChange ℚ_[p]) :
    W.baseChange (AlgebraicClosure ℚ_[p]) = W₀.baseChange (AlgebraicClosure ℚ_[p]) := by
  have h1 : W.baseChange (AlgebraicClosure ℚ_[p]) = (W.baseChange ℚ_[p]).baseChange (AlgebraicClosure ℚ_[p]) := by
    show W.map (algebraMap ℚ (AlgebraicClosure ℚ_[p])) =
      (W.map (algebraMap ℚ ℚ_[p])).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]))
    rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]
  rw [h1, hW, baseChange_baseChange_eq]

theorem exists_point_of_fixed_L (W₀ : WeierstrassCurve ℤ_[p]) (Y : (W₀.toAffine⁄(AlgebraicClosure ℚ_[p])).Point)
    (hY : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
      Point.map (W' := W₀.toAffine) (σ : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) Y = Y) :
    ∃ P : (W₀.toAffine⁄ℚ_[p]).Point,
      Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p])) P = Y := by
  rcases Y with _ | ⟨x, y, hxy⟩
  · exact ⟨0, map_zero _⟩
  · have hx : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], σ x = x := fun σ => by
      have := hY σ
      simp only [Point.map_some] at this
      exact (Point.some.inj this).1
    have hy : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], σ y = y := fun σ => by
      have := hY σ
      simp only [Point.map_some] at this
      exact (Point.some.inj this).2
    obtain ⟨x', hx'⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hx
    obtain ⟨y', hy'⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).2 hy
    subst hx' hy'
    have hns : (W₀.toAffine⁄ℚ_[p]).Nonsingular x' y' :=
      (W₀.toAffine.baseChange_nonsingular (f := Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p]))
        (Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p])).injective x' y').1 hxy
    exact ⟨Point.some _ _ hns, rfl⟩

end Local5

/-- A Selmer class over $\mathbb Q$ is locally trivial at $\mathbb Q_p$. -/
theorem locTorsion_padic_eq_zero (W : WeierstrassCurve ℚ) (n : ℤ)
    (γ : H1 (torsionRep W (AlgebraicClosure ℚ) n)) (hγ : γ ∈ selmerGroup ℚ W n) (p : ℕ) [Fact p.Prime] :
    locTorsion ℚ_[p] W n γ = 0 := by
  have hmem := ((mem_selmerGroup_iff ℚ W n γ).1 hγ).2.1
  let pp : Nat.Primes := ⟨p, Fact.out⟩
  exact locTorsion_eq_zero_of_algEquiv W n
    (Padic.adicCompletionEquiv (NumberField.RingOfIntegers ℚ) pp).symm.toAlgEquiv γ
    (hmem ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm pp))

/-- **Proposition 3.6**, strong form at the level of cocycles ($p \nmid n$, good reduction at $p$, every prime
$p$): a Selmer cocycle vanishes on the decomposition image of $G_K$ for a finite unramified $K$, and that image
acts trivially on $E_n$. -/
theorem exists_unramified_cocycle_eq_zero (W : WeierstrassCurve ℚ) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0)
    (c : cocycles₁ (torsionRep W (AlgebraicClosure ℚ) n)) (hγ : H1π _ c ∈ selmerGroup ℚ W n)
    (p : ℕ) [Fact p.Prime] (hpn : ¬ (p : ℤ) ∣ n) (W₀ : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W₀.Δ)
    (hW : W.baseChange ℚ_[p] = W₀.baseChange ℚ_[p]) :
    ∃ K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]), FiniteDimensional ℚ_[p] K ∧
      IsUnramifiedOverQp p K ∧ ∀ σ ∈ K.fixingSubgroup,
        c (decompHom ℚ_[p] σ) = 0 ∧
          ∀ t : torsionPoints W (AlgebraicClosure ℚ) n,
            Point.map (W' := W.toAffine) ((decompHom ℚ_[p] σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
              AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) (t : (W.toAffine⁄(AlgebraicClosure ℚ)).Point) = t := by
  have hAC := curve_eq_AC p W W₀ hW
  let e : (W.toAffine⁄(AlgebraicClosure ℚ_[p])).Point ≃+ (W₀.toAffine⁄(AlgebraicClosure ℚ_[p])).Point :=
    ptCast hAC
  obtain ⟨R, hR⟩ := (locTorsion_eq_zero_iff W n ℚ_[p] c).1 (locTorsion_padic_eq_zero W n _ hγ p)
  have hfixW : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
      Point.map (W' := W.toAffine)
        ((AlgEquiv.restrictScalarsHom ℚ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ] AlgebraicClosure ℚ_[p]) :
          AlgebraicClosure ℚ_[p] →ₐ[ℚ] AlgebraicClosure ℚ_[p]) (n • R) = n • R := by
    intro σ
    rw [map_zsmul]
    have h1 := hR σ
    rw [eq_sub_iff_add_eq] at h1
    rw [← h1, smul_add, ← map_zsmul,
      show n • ((c (decompHom ℚ_[p] σ) : torsionPoints W _ n) : (W.toAffine⁄(AlgebraicClosure ℚ)).Point) = 0 from
        (c (decompHom ℚ_[p] σ)).2, map_zero, zero_add]
  have hfixY : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
      Point.map (W' := W₀.toAffine) (σ : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (e (n • R)) = e (n • R) := by
    intro σ
    rw [← ptCast_map_apply W W₀ hAC
      ((AlgEquiv.restrictScalarsHom ℚ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ] AlgebraicClosure ℚ_[p]) :
          AlgebraicClosure ℚ_[p] →ₐ[ℚ] AlgebraicClosure ℚ_[p])
      (σ : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (fun x => rfl)]
    exact congrArg e (hfixW σ)
  obtain ⟨P, hP⟩ := exists_point_of_fixed_L p W₀ _ hfixY
  obtain ⟨Kf, hfd, hun, hK⟩ := exists_unramified_divPoints_general W₀ hΔ hpn P
  have hrat : ∀ Z : (W.toAffine⁄(AlgebraicClosure ℚ_[p])).Point, n • Z = n • R →
      ∀ σ ∈ Kf.fixingSubgroup,
        Point.map (W' := W.toAffine)
          ((AlgEquiv.restrictScalarsHom ℚ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ] AlgebraicClosure ℚ_[p]) :
            AlgebraicClosure ℚ_[p] →ₐ[ℚ] AlgebraicClosure ℚ_[p]) Z = Z := by
    intro Z hZ σ hσ
    obtain ⟨Q₀, hQ₀⟩ := hK (e Z) (by rw [hP, ← map_zsmul, hZ])
    apply e.injective
    rw [ptCast_map_apply W W₀ hAC
      ((AlgEquiv.restrictScalarsHom ℚ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ] AlgebraicClosure ℚ_[p]) :
          AlgebraicClosure ℚ_[p] →ₐ[ℚ] AlgebraicClosure ℚ_[p])
      (σ : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (fun x => rfl)]
    show Point.map (W' := W₀.toAffine) (σ : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (e Z) = e Z
    rw [← hQ₀, Point.map_map]
    have : (σ : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]).comp Kf.val = Kf.val :=
      AlgHom.ext fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x.1 x.2
    rw [this]
  refine ⟨Kf, hfd, hun, fun σ hσ => ?_⟩
  have hR1 := hrat R rfl σ hσ
  refine ⟨?_, fun t => ?_⟩
  · have h1 := hR σ
    rw [hR1, sub_self] at h1
    refine Subtype.ext (Point.map_injective (W' := W.toAffine) (closureEmb ℚ_[p]) ?_)
    rw [h1]
    exact (map_zero _).symm
  · have h2 := hrat (R + Point.map (W' := W.toAffine) (closureEmb ℚ_[p]) (t : (W.toAffine⁄(AlgebraicClosure ℚ)).Point))
      (by
        rw [zsmul_add, ← map_zsmul, show n • (t : (W.toAffine⁄(AlgebraicClosure ℚ)).Point) = 0 from t.2, map_zero,
          add_zero]) σ hσ
    rw [map_add, hR1] at h2
    have h3 := add_left_cancel h2
    apply Point.map_injective (W' := W.toAffine) (closureEmb ℚ_[p])
    rw [localize_map]
    exact h3

/-- **Proposition 3.6** (Milne, pdf p. 120) for every prime $p$: the statement of the named `Prop3_6`
(helper for `prop3_6` in `Ch4Lemma32General.lean`). -/
theorem prop_3_6_general (W₀ : WeierstrassCurve ℤ) [(W₀.map (Int.castRingHom ℚ)).IsElliptic] (n : ℤ)
    (hn : n ≠ 0) (γ : H1 (torsionRep (W₀.map (Int.castRingHom ℚ)) (AlgebraicClosure ℚ) n))
    (hγ : γ ∈ selmerGroup ℚ (W₀.map (Int.castRingHom ℚ)) n) (p : ℕ) [Fact p.Prime]
    (hpΔ : ¬ (p : ℤ) ∣ 2 * n * W₀.Δ) :
    ∃ K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]), FiniteDimensional ℚ_[p] K ∧
      IsUnramifiedOverQp p K ∧ resToLocalField p (W₀.map (Int.castRingHom ℚ)) n K γ = 0 := by
  induction γ using H1_induction_on with | @h c => ?_
  have hΔ : IsUnit (W₀.map (Int.castRingHom ℤ_[p])).Δ := by
    rw [WeierstrassCurve.map_Δ]
    exact unit_int_of_not_dvd (p := p) (fun h => hpΔ (Dvd.dvd.mul_left h _))
  have hpn : ¬ (p : ℤ) ∣ n := fun h => hpΔ (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have hW : (W₀.map (Int.castRingHom ℚ)).baseChange ℚ_[p] =
      (W₀.map (Int.castRingHom ℤ_[p])).baseChange ℚ_[p] := by
    show (W₀.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[p]) =
      (W₀.map (Int.castRingHom ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p])
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    congr 1
  obtain ⟨K, hfd, hun, hK⟩ := exists_unramified_cocycle_eq_zero (W₀.map (Int.castRingHom ℚ)) n hn c hγ p hpn
    _ hΔ hW
  refine ⟨K, hfd, hun, ?_⟩
  have hc1 := map_H1π_res (decompHom ℚ_[p]) (localizeTorsionTorsion p (W₀.map (Int.castRingHom ℚ)) n) c
    (mapCocycles₁ (decompHom ℚ_[p]) (localizeTorsionTorsion p (W₀.map (Int.castRingHom ℚ)) n) c) (fun g => rfl)
  have hc2 := map_H1π_res K.fixingSubgroup.subtype (𝟙 _)
    (mapCocycles₁ (decompHom ℚ_[p]) (localizeTorsionTorsion p (W₀.map (Int.castRingHom ℚ)) n) c)
    (mapCocycles₁ K.fixingSubgroup.subtype (𝟙 _)
      (mapCocycles₁ (decompHom ℚ_[p]) (localizeTorsionTorsion p (W₀.map (Int.castRingHom ℚ)) n) c))
    (fun g => rfl)
  show map _ (𝟙 _) 1 (map (decompHom ℚ_[p]) (localizeTorsionTorsion p (W₀.map (Int.castRingHom ℚ)) n) 1
    (H1π _ c)) = 0
  rw [hc1, hc2, H1π_eq_zero_iff]
  have h0 : ⇑(mapCocycles₁ K.fixingSubgroup.subtype (𝟙 _)
      (mapCocycles₁ (decompHom ℚ_[p]) (localizeTorsionTorsion p (W₀.map (Int.castRingHom ℚ)) n) c)) = 0 := by
    funext σ
    show (localizeTorsionTorsion p (W₀.map (Int.castRingHom ℚ)) n).hom (c (decompHom ℚ_[p] σ.1)) = 0
    rw [(hK σ.1 σ.2).1, map_zero]
  rw [h0]
  exact zero_mem _

/-- **Proposition 3.6** (Milne, pdf p. 120) for $p \ge 5$: the statement of the named `Prop3_6` with the extra
hypothesis $5 \le p$ (kept; it is a special case of `prop_3_6_general`). -/
@[kb "milne2006ec" "Ch. IV, Prop. 3.6, pdf p. 120"]
theorem prop_3_6_of_five_le (W₀ : WeierstrassCurve ℤ) [(W₀.map (Int.castRingHom ℚ)).IsElliptic] (n : ℤ)
    (hn : n ≠ 0) (γ : H1 (torsionRep (W₀.map (Int.castRingHom ℚ)) (AlgebraicClosure ℚ) n))
    (hγ : γ ∈ selmerGroup ℚ (W₀.map (Int.castRingHom ℚ)) n) (p : ℕ) [Fact p.Prime] (_hp : 5 ≤ p)
    (hpΔ : ¬ (p : ℤ) ∣ 2 * n * W₀.Δ) :
    ∃ K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]), FiniteDimensional ℚ_[p] K ∧
      IsUnramifiedOverQp p K ∧ resToLocalField p (W₀.map (Int.castRingHom ℚ)) n K γ = 0 :=
  prop_3_6_general W₀ n hn γ hγ p hpΔ

end NumberFieldKB.MilneEC
