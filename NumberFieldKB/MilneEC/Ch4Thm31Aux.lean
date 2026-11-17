import NumberFieldKB.MilneEC.Ch4Prop36Proof
import NumberFieldKB.MilneEC.Ch4SelmerFinite
import NumberFieldKB.MilneANT.Ch8Thm842
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Helpers for Theorem 3.1 over $\mathbb Q$ (Hermite's route)

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, proof of Theorem 3.1 (pdf pp. 120–125).

For a crossed homomorphism $c : G_{\mathbb Q} \to E_n(\bar{\mathbb Q})$:
* `cocycleKernel c` $= \{\sigma : \sigma \text{ fixes } E_n(\bar{\mathbb Q}),\ c(\sigma) = 0\}$, a normal subgroup
  (`cocycleKernel_normal`), open when $c$ is continuous (`cocycleKernel_isOpen`), of index at most
  $B = |E_n|^{|E_n|}\,|E_n|$ (`cocycleKernel_index_le`: $\sigma \mapsto (\sigma|_{E_n}, c(\sigma))$ is injective on
  cosets).
* `cocycleField c`, the fixed field: finite Galois over $\mathbb Q$ of degree $\le B$ with fixing subgroup
  `cocycleKernel c` (`cocycleField_spec`).
* `isUnramifiedIn_of_embedding`: if a finite Galois $M \subseteq \bar{\mathbb Q}$ embeds (by `closureEmb`) into a
  finite unramified extension of $\mathbb Q_p$ in $\bar{\mathbb Q}_p$, then $p$ is unramified in $M$: the prime
  $\mathfrak P_0$ pulled back from $\mathcal O_K$ has $p \notin \mathfrak P_0^2$ (as $p\mathcal O_K$ is the maximal
  ideal), so $e(\mathfrak P_0/p) = 1$, and all primes above $p$ are Galois conjugate.
* `finite_selmer_of_finite_fields`: if every Selmer class has a cocycle whose field lies in a fixed finite set,
  the Selmer group is finite (Lemma 3.8, extended to $n \ne 0$ in `lemma_3_8'`).
-/

namespace NumberFieldKB.MilneEC

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine NumberField
  IsDedekindDomain
open scoped Classical

set_option backward.isDefEq.respectTransparency false

section Kernel

variable (W : WeierstrassCurve ℚ) (n : ℤ)

/-- The subgroup of $G_{\mathbb Q}$ fixing $E_n(\bar{\mathbb Q})$ on which the cocycle $c$ vanishes. -/
noncomputable def cocycleKernel (c : cocycles₁ (torsionRep W (AlgebraicClosure ℚ) n)) :
    Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) where
  carrier := {σ | (∀ t, (torsionRep W (AlgebraicClosure ℚ) n).ρ σ t = t) ∧ c σ = 0}
  one_mem' := by
    refine ⟨fun t => by simp, ?_⟩
    exact cocycles₁_map_one c
  mul_mem' := by
    rintro σ τ ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨fun t => by rw [map_mul, Module.End.mul_apply, h3, h1], ?_⟩
    show c (σ * τ) = 0
    rw [(mem_cocycles₁_iff c).1 c.2 σ τ, h4, h2, map_zero, add_zero]
  inv_mem' := by
    rintro σ ⟨h1, h2⟩
    refine ⟨fun t => ?_, ?_⟩
    · conv_lhs => rw [← h1 t]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · have := cocycles₁_map_inv c σ
      rw [h1, h2, neg_zero] at this
      exact this

lemma cocycleKernel_normal (c : cocycles₁ (torsionRep W (AlgebraicClosure ℚ) n)) :
    (cocycleKernel W n c).Normal := by
  refine ⟨fun ρ hρ τ => ?_⟩
  obtain ⟨h1, h2⟩ := hρ
  have hcc := (mem_cocycles₁_iff c).1 c.2
  refine ⟨fun t => ?_, ?_⟩
  · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1, ← Module.End.mul_apply,
      ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · show c (τ * ρ * τ⁻¹) = 0
    have e1 : c (ρ * τ⁻¹) = c τ⁻¹ := by
      rw [hcc, h2, add_zero, h1]
    rw [mul_assoc, hcc τ (ρ * τ⁻¹), e1, ← hcc, mul_inv_cancel]
    exact cocycles₁_map_one c

lemma finite_torsionPoints [W.IsElliptic] (hn : n ≠ 0) :
    Finite (torsionPoints W (AlgebraicClosure ℚ) n) := by
  have hΔ : (W.baseChange (AlgebraicClosure ℚ)).Δ ≠ 0 :=
    (inferInstance : (W.baseChange (AlgebraicClosure ℚ)).IsElliptic).isUnit.ne_zero
  have h : ((torsionPoints W (AlgebraicClosure ℚ) n : AddSubgroup _) : Set _).Finite :=
    (torsion_finite _ hΔ hn).subset (fun Q hQ => hQ)
  exact h.to_subtype

lemma torsionRep_stab_isOpen (t : torsionPoints W (AlgebraicClosure ℚ) n) :
    IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
      (torsionRep W (AlgebraicClosure ℚ) n).ρ σ t = t} := by
  have := pointsRep_isDiscreteModule W (AlgebraicClosure ℚ) (t : (W.toAffine⁄(AlgebraicClosure ℚ)).Point)
  convert this using 2
  ext σ
  exact Subtype.ext_iff

/-- The statement `cocycleKernel_isOpen` is false for `n = 0` (then `E_0 = E(ℚbar)` and the kernel is trivial for
`c = 0`); this is the version with the needed hypotheses. -/
lemma cocycleKernel_isOpen' [W.IsElliptic] (hn : n ≠ 0)
    (c : cocycles₁ (torsionRep W (AlgebraicClosure ℚ) n))
    (hc : c ∈ contCocycles₁ (torsionRep W (AlgebraicClosure ℚ) n)) :
    IsOpen (cocycleKernel W n c : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
  haveI := finite_torsionPoints W n hn
  have h1 : IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
      ∀ t, (torsionRep W (AlgebraicClosure ℚ) n).ρ σ t = t} := by
    have : {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
      ∀ t, (torsionRep W (AlgebraicClosure ℚ) n).ρ σ t = t} =
        ⋂ t, {σ | (torsionRep W (AlgebraicClosure ℚ) n).ρ σ t = t} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun t => torsionRep_stab_isOpen W n t
  have h2 : IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | c σ = 0} := by
    let _ : TopologicalSpace (torsionRep W (AlgebraicClosure ℚ) n) := ⊥
    have _ : DiscreteTopology (torsionRep W (AlgebraicClosure ℚ) n) := ⟨rfl⟩
    have hc' : Continuous (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      torsionRep W (AlgebraicClosure ℚ) n) := hc
    exact hc'.isOpen_preimage {0} (isOpen_discrete _)
  exact h1.inter h2

/-- The bound $|E_n|^{|E_n|}\,|E_n|$ on the index. -/
noncomputable def kernelBound : ℕ :=
  Nat.card (torsionPoints W (AlgebraicClosure ℚ) n) ^ Nat.card (torsionPoints W (AlgebraicClosure ℚ) n) *
    Nat.card (torsionPoints W (AlgebraicClosure ℚ) n)

lemma cocycleKernel_index_le [W.IsElliptic] (hn : n ≠ 0)
    (c : cocycles₁ (torsionRep W (AlgebraicClosure ℚ) n)) :
    (cocycleKernel W n c).index ≠ 0 ∧ (cocycleKernel W n c).index ≤ kernelBound W n := by
  haveI := finite_torsionPoints W n hn
  set E := torsionPoints W (AlgebraicClosure ℚ) n with hE
  set ρ := (torsionRep W (AlgebraicClosure ℚ) n).ρ with hρ
  have hcc := (mem_cocycles₁_iff c).1 c.2
  have hmul : ∀ g h (t : E), ρ (g * h) t = ρ g (ρ h t) := fun g h t => by
    rw [map_mul, Module.End.mul_apply]
  let Φ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ((E → E) × E) :=
    fun σ => (fun t => ρ σ t, c σ)
  have hfwd : ∀ a b, a⁻¹ * b ∈ cocycleKernel W n c → Φ a = Φ b := by
    intro a b ⟨h1, h2⟩
    have hb : b = a * (a⁻¹ * b) := by group
    refine Prod.ext (funext fun t => ?_) ?_
    · show ρ a t = ρ b t
      conv_rhs => rw [hb, hmul, h1]
    · show c a = c b
      conv_rhs => rw [hb, hcc, h2, map_zero, zero_add]
  have hbwd : ∀ a b, Φ a = Φ b → a⁻¹ * b ∈ cocycleKernel W n c := by
    intro a b hab
    have h1 : ∀ t, ρ a t = ρ b t := fun t => congrFun (congrArg Prod.fst hab) t
    have h2 : c a = c b := congrArg Prod.snd hab
    refine ⟨fun t => ?_, ?_⟩
    · show ρ (a⁻¹ * b) t = t
      rw [hmul, ← h1, ← hmul, inv_mul_cancel, map_one, Module.End.one_apply]
    · show c (a⁻¹ * b) = 0
      rw [hcc, ← h2, ← hcc, inv_mul_cancel]
      exact cocycles₁_map_one c
  let Ψ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ cocycleKernel W n c → ((E → E) × E) :=
    Quotient.lift Φ (fun a b hab => hfwd a b ((QuotientGroup.leftRel_apply).1 hab))
  have hinj : Function.Injective Ψ := by
    intro x y
    induction x using Quotient.inductionOn with | _ a => ?_
    induction y using Quotient.inductionOn with | _ b => ?_
    intro h
    exact Quotient.sound ((QuotientGroup.leftRel_apply).2 (hbwd a b h))
  haveI : Finite ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ cocycleKernel W n c) :=
    Finite.of_injective Ψ hinj
  refine ⟨(Nat.card_pos).ne', ?_⟩
  have := Nat.card_le_card_of_injective Ψ hinj
  rw [Nat.card_prod, Nat.card_fun] at this
  exact this

/-- The fixed field of `cocycleKernel c`. -/
noncomputable def cocycleField (c : cocycles₁ (torsionRep W (AlgebraicClosure ℚ) n)) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField (cocycleKernel W n c)

lemma cocycleField_spec [W.IsElliptic] (hn : n ≠ 0) (c : cocycles₁ (torsionRep W (AlgebraicClosure ℚ) n))
    (hc : c ∈ contCocycles₁ (torsionRep W (AlgebraicClosure ℚ) n)) :
    FiniteDimensional ℚ (cocycleField W n c) ∧ IsGalois ℚ (cocycleField W n c) ∧
      Module.finrank ℚ (cocycleField W n c) ≤ kernelBound W n ∧
      (cocycleField W n c).fixingSubgroup = cocycleKernel W n c := by
  have hN := cocycleKernel_normal W n c
  have hO := cocycleKernel_isOpen' W n hn c hc
  let Hc : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    ⟨cocycleKernel W n c, Subgroup.isClosed_of_isOpen _ hO⟩
  have hfix : (cocycleField W n c).fixingSubgroup = cocycleKernel W n c :=
    InfiniteGalois.fixingSubgroup_fixedField Hc
  obtain ⟨hfd, hgal⟩ := (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
    (cocycleField W n c)).1 ⟨by rw [hfix]; exact hO, by rw [hfix]; exact hN⟩
  refine ⟨hfd, hgal, ?_, hfix⟩
  have h1 : Module.finrank ℚ (cocycleField W n c) = (cocycleKernel W n c).index := by
    rw [← IsGalois.card_aut_eq_finrank, Subgroup.index]
    exact (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient Hc).toEquiv).symm
  rw [h1]
  exact (cocycleKernel_index_le W n hn c).2

end Kernel

/-- If a finite Galois extension $M$ of $\mathbb Q$ in $\bar{\mathbb Q}$ is carried by `closureEmb` into a finite
unramified extension of $\mathbb Q_p$, then $p$ is unramified in $M$. -/
theorem isUnramifiedIn_of_embedding (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ M]
    [IsGalois ℚ M] (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    [FiniteDimensional ℚ_[p] K] (hK : IsUnramifiedOverQp p K)
    (hMK : ∀ x ∈ M, closureEmb ℚ_[p] x ∈ K) (𝔭 : HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : (Rat.HeightOneSpectrum.primesEquiv 𝔭 : ℕ) = p) :
    Algebra.IsUnramifiedIn (𝓞 M) 𝔭.asIdeal := by
  haveI : NumberField M := NumberField.of_module_finite ℚ M
  haveI : IsGaloisGroup Gal(M/ℚ) (𝓞 ℚ) (𝓞 M) := inferInstance
  -- a ring homomorphism `𝓞 M → 𝓞_K`
  let g0 : 𝓞 M →+* AlgebraicClosure ℚ_[p] :=
    (closureEmb (K := ℚ) ℚ_[p]).toRingHom.comp (M.val.toRingHom.comp (algebraMap (𝓞 M) M))
  let g1 : 𝓞 M →+* K := g0.codRestrict K.toSubfield.toSubring
    (fun x => hMK ((x : M) : AlgebraicClosure ℚ) (x : M).2)
  have hint : ∀ x, g1 x ∈ (integralClosure ℤ_[p] K).toSubring := fun x =>
    ((Algebra.IsIntegral.isIntegral (R := ℤ) x).map g1.toIntAlgHom).tower_top
  let φ : 𝓞 M →+* integralClosure ℤ_[p] K := g1.codRestrict (integralClosure ℤ_[p] K).toSubring hint
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (integralClosure ℤ_[p] K)
  have hmp : m = Ideal.span {((p : ℕ) : integralClosure ℤ_[p] K)} := hK m hm
  haveI := hm.isPrime
  haveI hP₀ : (m.comap φ).IsPrime := Ideal.comap_isPrime φ m
  have hp0 : ((p : ℕ) : integralClosure ℤ_[p] K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpm : ((p : ℕ) : integralClosure ℤ_[p] K) ∈ m := hmp ▸ Ideal.mem_span_singleton_self _
  have hgen : Rat.HeightOneSpectrum.natGenerator 𝔭 = p := h𝔭
  have hp𝔭 : ((p : ℕ) : 𝓞 ℚ) ∈ 𝔭.asIdeal := by
    have h1 := (Rat.HeightOneSpectrum.natGenerator_dvd_iff 𝔭 (n := p)).1 (by rw [hgen])
    rwa [← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) p, Ideal.apply_mem_of_equiv_iff] at h1
  have hdvd : ∀ x ∈ 𝔭.asIdeal, ∃ y : 𝓞 ℚ, x = ((p : ℕ) : 𝓞 ℚ) * y := by
    intro x hx
    have h1 : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x ∈
        𝔭.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := Ideal.mem_map_of_mem _ hx
    rw [← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton] at h1
    obtain ⟨z, hz⟩ := h1
    refine ⟨(Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm z, ?_⟩
    apply (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective
    rw [hz, map_mul, map_natCast, RingEquiv.apply_symm_apply, hgen]
  have hle : 𝔭.asIdeal ≤ (m.comap φ).under (𝓞 ℚ) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hdvd x hx
    simp only [Ideal.under, Ideal.mem_comap, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ hpm
  haveI hlies : (m.comap φ).LiesOver 𝔭.asIdeal :=
    ⟨(HeightOneSpectrum.isMaximal 𝔭).eq_of_le Ideal.IsPrime.ne_top' hle⟩
  have hmapne : 𝔭.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 M)) ≤ m.comap φ :=
    Ideal.map_le_iff_le_comap.2 hle
  have hne1 : ¬ 𝔭.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 M)) ≤ (m.comap φ) ^ 2 := by
    intro h
    have h1 : ((p : ℕ) : 𝓞 M) ∈ (m.comap φ) ^ 2 := by
      have := h (Ideal.mem_map_of_mem (algebraMap (𝓞 ℚ) (𝓞 M)) hp𝔭)
      rwa [map_natCast] at this
    have h2 : φ ((p : ℕ) : 𝓞 M) ∈ m ^ 2 := by
      have := Ideal.mem_map_of_mem φ h1
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono Ideal.map_comap_le 2 this
    rw [map_natCast, hmp, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
    obtain ⟨z, hz⟩ := h2
    have h3 : ((p : ℕ) : integralClosure ℤ_[p] K) * (p * z) = p * 1 := by
      calc ((p : ℕ) : integralClosure ℤ_[p] K) * (p * z) = (p : integralClosure ℤ_[p] K) ^ 2 * z := by ring
      _ = p := hz.symm
      _ = p * 1 := (mul_one _).symm
    have h4 := mul_left_cancel₀ hp0 h3
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m hpm (IsUnit.of_mul_eq_one z h4))
  have he' : 𝔭.asIdeal.ramificationIdx' (m.comap φ) = 1 := by
    by_contra hne
    exact hne1 ((Ideal.ramificationIdx'_ne_one_iff hmapne).1 hne)
  have he : (m.comap φ).ramificationIdx (𝓞 ℚ) = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx 𝔭.asIdeal (m.comap φ) 𝔭.ne_bot]
    exact he'
  intro P hP hPl
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 ℚ),
    Ideal.ramificationIdx_eq_of_isGaloisGroup 𝔭.asIdeal P (m.comap φ) Gal(M/ℚ)]
  exact he

/-- If the decomposition image of $\operatorname{Gal}(\bar{\mathbb Q}_p/K)$ lies in the fixing subgroup of $M$,
then `closureEmb` carries $M$ into $K$. -/
theorem closureEmb_mem_of_decompHom (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (h : ∀ σ ∈ K.fixingSubgroup, decompHom ℚ_[p] σ ∈ M.fixingSubgroup) :
    ∀ x ∈ M, closureEmb ℚ_[p] x ∈ K := by
  intro x hx
  rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  rw [← closureEmb_decompHom]
  congr 1
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (h σ hσ) x hx

/-- Outside a finite set of primes, a curve over $\mathbb Q$ has an integral model over $\mathbb Z_p$ with unit
discriminant: take $N$ the product of the denominators of the coefficients and the numerator of $\Delta$. -/
theorem exists_integralModel (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
      ∃ W₀ : WeierstrassCurve ℤ_[p], IsUnit W₀.Δ ∧ W.baseChange ℚ_[p] = W₀.baseChange ℚ_[p] := by
  have hΔne : W.Δ ≠ 0 := (inferInstance : W.IsElliptic).isUnit.ne_zero
  refine ⟨(W.a₁.den * W.a₂.den * W.a₃.den * W.a₄.den * W.a₆.den) * W.Δ.num.natAbs, ?_, ?_⟩
  · simp [Rat.den_nz, hΔne]
  intro p _ hp
  have hp' : p.Prime := Fact.out
  simp only [hp'.dvd_mul, not_or] at hp
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hp
  let W₀ : WeierstrassCurve ℤ_[p] :=
    ⟨⟨(W.a₁ : ℚ_[p]), Padic.norm_rat_le_one h1⟩, ⟨(W.a₂ : ℚ_[p]), Padic.norm_rat_le_one h2⟩,
      ⟨(W.a₃ : ℚ_[p]), Padic.norm_rat_le_one h3⟩, ⟨(W.a₄ : ℚ_[p]), Padic.norm_rat_le_one h4⟩,
      ⟨(W.a₆ : ℚ_[p]), Padic.norm_rat_le_one h5⟩⟩
  have hW : W.baseChange ℚ_[p] = W₀.baseChange ℚ_[p] := by
    ext <;> rfl
  refine ⟨W₀, ?_, hW⟩
  have hΔ : ((W₀.Δ : ℤ_[p]) : ℚ_[p]) = (W.Δ : ℚ_[p]) := by
    have := congrArg WeierstrassCurve.Δ hW
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ] at this
    exact this.symm
  have hnum : IsUnit ((W.Δ.num : ℤ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    intro h
    exact h6 (Int.natCast_dvd.1 h)
  have key : W₀.Δ * ((W.Δ.den : ℕ) : ℤ_[p]) = ((W.Δ.num : ℤ) : ℤ_[p]) := by
    apply PadicInt.ext
    have := congrArg (Rat.cast : ℚ → ℚ_[p]) (Rat.mul_den_eq_num W.Δ)
    push_cast at this ⊢
    rw [hΔ]
    exact this
  rw [← key] at hnum
  exact isUnit_of_mul_isUnit_left hnum

/-- `finite_invariants` for every $n \ne 0$. -/
lemma finite_invariants' (W : WeierstrassCurve ℚ) [W.IsElliptic] (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] (n : ℤ) (hn : n ≠ 0) :
    Finite (Representation.invariants
      ((torsionRep W (AlgebraicClosure ℚ) n).ρ.comp L.fixingSubgroup.subtype)) := by
  have : NumberField L := NumberField.of_module_finite ℚ L
  have : (W.toAffine⁄L).IsElliptic :=
    (inferInstance : (WeierstrassCurve.map W (algebraMap ℚ L)).IsElliptic)
  have : Finite (AddCommGroup.torsion (W.toAffine⁄L).Point) :=
    WeierstrassCurve.Affine.finite_torsion
  set A := torsionRep W (AlgebraicClosure ℚ) n with hA
  let ι : Representation.invariants (A.ρ.comp L.fixingSubgroup.subtype) →
      (W.toAffine⁄(AlgebraicClosure ℚ)).Point := fun v => ((v : A) : (W.toAffine⁄(AlgebraicClosure ℚ)).Point)
  have hinj : Function.Injective ι := fun v w h =>
    Subtype.ext (Subtype.ext h)
  let T0 : Set (W.toAffine⁄(AlgebraicClosure ℚ)).Point :=
    Set.range (fun Q : AddCommGroup.torsion (W.toAffine⁄L).Point =>
      Point.map (W' := W.toAffine) L.val Q.1)
  have hT0 : T0.Finite := Set.finite_range _
  have hmem : ∀ v, ι v ∈ T0 := by
    intro v
    obtain ⟨Q, hQ⟩ := exists_point_of_fixed W L (ι v) (fun σ hσ => by
      have := congrArg Subtype.val (Representation.mem_invariants _ _ |>.1 v.2 ⟨σ, hσ⟩)
      exact this)
    refine ⟨⟨Q, ?_⟩, hQ⟩
    have hv : n • ι v = 0 := (v.1 : torsionPoints W (AlgebraicClosure ℚ) n).2
    rw [← hQ, ← map_zsmul] at hv
    have hQ0 : n • Q = 0 := Point.map_injective (W' := W.toAffine) L.val (by rw [map_zsmul]; simpa using hv)
    rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨n.natAbs, Int.natAbs_pos.2 hn, ?_⟩
    have h2 : ((n.natAbs : ℤ)) • Q = 0 := by
      rcases Int.natAbs_eq n with h | h
      · rw [← h]; exact hQ0
      · rw [h] at hQ0
        simpa using hQ0
    simpa using h2
  have := hT0.to_subtype
  exact Finite.of_injective (fun v => (⟨ι v, hmem v⟩ : T0)) (fun v w h => by
    have h' : (⟨ι v, hmem v⟩ : T0) = ⟨ι w, hmem w⟩ := h
    exact hinj (Subtype.mk.inj h'))

/-- Lemma 3.8 for every $n \ne 0$. -/
theorem lemma_3_8' (W : WeierstrassCurve ℚ) [W.IsElliptic] (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (n : ℤ) (hn : n ≠ 0) :
    {x | x ∈ selmerGroup ℚ W n ∧ resToField W L n x = 0}.Finite := by
  have hN : L.fixingSubgroup.Normal := by
    rw [← IntermediateField.restrictNormalHom_ker]; infer_instance
  set A := torsionRep W (AlgebraicClosure ℚ) n with hA
  have hG : Finite ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup) := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact Finite.of_injective _ (QuotientGroup.kerLift_injective (AlgEquiv.restrictNormalHom L))
  have hB : Finite (A.quotientToInvariants L.fixingSubgroup) := finite_invariants' W L n hn
  have hC : Finite (cocycles₁ (A.quotientToInvariants L.fixingSubgroup)) := by
    refine Finite.of_injective (fun f => (f : _ → A.quotientToInvariants L.fixingSubgroup))
      (fun f g h => Subtype.ext h)
  have hH : Finite (H1 (A.quotientToInvariants L.fixingSubgroup)) :=
    Finite.of_surjective _ (h1_eq_crossed_mod_principal _).1
  have hex := (remark_1_7 A L.fixingSubgroup).2
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hH' : Finite (H1InfRes A L.fixingSubgroup).X₁ := hH
  refine (Set.finite_range (fun y : (H1InfRes A L.fixingSubgroup).X₁ =>
    (H1InfRes A L.fixingSubgroup).f y)).subset ?_
  intro x hx
  obtain ⟨y, hy⟩ := hex x hx.2
  exact ⟨y, hy⟩

/-- The restriction of the class of $c$ to the fixing subgroup of `cocycleField c` is zero. -/
theorem resToField_cocycleField (W : WeierstrassCurve ℚ) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0)
    (c : cocycles₁ (torsionRep W (AlgebraicClosure ℚ) n))
    (hc : c ∈ contCocycles₁ (torsionRep W (AlgebraicClosure ℚ) n)) :
    resToField W (cocycleField W n c) n (H1π _ c) = 0 := by
  have hfix := (cocycleField_spec W n hn c hc).2.2.2
  have key : ∀ x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      x ∈ (cocycleField W n c).fixingSubgroup → c x = 0 := fun x hx => (hfix.le hx).2
  have h := map_H1π_res (cocycleField W n c).fixingSubgroup.subtype (𝟙 _) c 0 (fun g => by
    have := key g.1 g.2
    simp [this] <;> rfl)
  change map _ (𝟙 _) 1 (H1π _ c) = 0
  rw [h, map_zero]

end NumberFieldKB.MilneEC
