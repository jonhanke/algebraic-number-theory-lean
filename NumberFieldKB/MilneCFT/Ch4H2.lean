import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Torsion

/-!
# Milne, Class Field Theory, Chapter IV, §3: $H^2(L/k) \cong \mathrm{Br}(L/k)$ (Theorem 3.14)

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`).
$H^2(L/K)$ is Mathlib's `groupCohomology.H2 (Rep.ofAlgebraAutOnUnits K L)`; Mathlib's group
cohomology needs the group and the coefficient ring `ℤ` in the same universe, so $K, L$ are in
`Type`.  Locators give the printed page of the book (printed page = pdf page − 9).
-/

namespace NumberFieldKB.MilneCFT.Ch4

/-! ### The isomorphism $H^2(L/K) \cong \mathrm{Br}(L/K)$ -/

section H2

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The class in $H^2(L/K)$ of a normalized cocycle. -/
noncomputable def NormalizedCocycle.toH2 (φ : NormalizedCocycle K L) :
    groupCohomology.H2 (Rep.ofAlgebraAutOnUnits K L) :=
  (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)).hom
    (groupCohomology.cocyclesOfIsMulCocycle₂ φ.isMulCocycle₂)

namespace NormalizedCocycle

/-- Normalization of a function $f : G \times G \to L^\times$: $f(\sigma, \tau) / \sigma(f(1,1))$. -/
noncomputable def normFun (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) :
    (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ :=
  fun p => f p / p.1 • f (1, 1)

theorem normFun_cocycle {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hf : groupCohomology.IsMulCocycle₂ f) : groupCohomology.IsMulCocycle₂ (normFun f) := by
  intro σ τ ρ
  have h := hf σ τ ρ
  show f (σ * τ, ρ) / (σ * τ) • f (1, 1) * (f (σ, τ) / σ • f (1, 1)) =
    σ • (f (τ, ρ) / τ • f (1, 1)) * (f (σ, τ * ρ) / σ • f (1, 1))
  rw [smul_div', ← mul_smul, div_mul_div_comm, div_mul_div_comm, h]

/-- The normalized cocycle cohomologous to a given cocycle. -/
noncomputable def normalize (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (hf : groupCohomology.IsMulCocycle₂ f) : NormalizedCocycle K L :=
  ⟨normFun f, normFun_cocycle hf, by simp [normFun]⟩

theorem ext_toFun {φ ψ : NormalizedCocycle K L} (h : ∀ p, φ p = ψ p) : φ = ψ := by
  obtain ⟨a, ha, ha1⟩ := φ
  obtain ⟨b, hb, hb1⟩ := ψ
  have : a = b := funext h
  subst this
  rfl

theorem normalize_eq (φ : NormalizedCocycle K L) (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (hfφ : ∀ p, f p = φ p) (hf : groupCohomology.IsMulCocycle₂ f) : normalize f hf = φ := by
  apply ext_toFun
  intro p
  show f p / p.1 • f (1, 1) = φ p
  rw [hfφ, hfφ, φ.map_one_one, smul_one, div_one]

theorem normalize_mul (f g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (hf : groupCohomology.IsMulCocycle₂ f) (hg : groupCohomology.IsMulCocycle₂ g)
    (hfg : groupCohomology.IsMulCocycle₂ (fun p => f p * g p)) :
    normalize (fun p => f p * g p) hfg = mul (normalize f hf) (normalize g hg) := by
  apply ext_toFun
  intro p
  show f p * g p / p.1 • (f (1, 1) * g (1, 1)) = f p / p.1 • f (1, 1) * (g p / p.1 • g (1, 1))
  rw [smul_mul', mul_div_mul_comm]

theorem key_cancel2 (a b d c c' : Lˣ) : (a / c') / (b / c) * (d / c) = a / b * d / c' := by
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  have e : c * c⁻¹ = 1 := mul_inv_cancel c
  calc a * c'⁻¹ * (b⁻¹ * c) * (d * c⁻¹) = a * c'⁻¹ * b⁻¹ * d * (c * c⁻¹) := by ac_rfl
    _ = a * b⁻¹ * d * c'⁻¹ := by rw [e, mul_one]; ac_rfl

theorem normalize_cohomologous_one (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (hf : groupCohomology.IsMulCocycle₂ f) (hb : groupCohomology.IsMulCoboundary₂ f) :
    Cohomologous (normalize f hf) one := by
  obtain ⟨x, hx⟩ := hb
  have hc : f (1, 1) = x 1 := by simpa using (hx 1 1).symm
  refine ⟨fun σ => x σ / x 1, fun σ τ => ?_⟩
  have h := hx σ τ
  show σ • (x τ / x 1) / (x (σ * τ) / x 1) * (x σ / x 1) =
    f (σ, τ) / σ • f (1, 1) / (1 : Lˣ)
  rw [hc, ← h, smul_div', div_one, key_cancel2]

theorem key_cancel (a b d c c' : Lˣ) : (a * c') / (b * c) * (d * c) = a / b * d * c' := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  have e : c⁻¹ * c = 1 := inv_mul_cancel c
  calc a * c' * (b⁻¹ * c⁻¹) * (d * c) = a * c' * b⁻¹ * d * (c⁻¹ * c) := by ac_rfl
    _ = a * b⁻¹ * d * c' := by rw [e, mul_one]; ac_rfl

end NormalizedCocycle

section Aux

variable [IsGalois K L]

/-- The class $[A(\text{normalization of } z)]$ of a 2-cocycle. -/
noncomputable def cocycleClass
    (z : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) :
    BrauerGroup.{0, 0} K :=
  BrauerGroup.mk (CrossedProduct.toCSA (NormalizedCocycle.normalize
    (fun p => Additive.toMul (z.1 p))
    (groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (G := L ≃ₐ[K] L) (M := Lˣ) z.1 z.2)))

theorem cocycleClass_add
    (z₁ z₂ : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) :
    cocycleClass (z₁ + z₂) = cocycleClass z₁ * cocycleClass z₂ := by
  unfold cocycleClass
  rw [BrauerGroup.mk_mul_mk, BrauerGroup.mk_eq_mk_iff]
  have e := NormalizedCocycle.normalize_mul (K := K) (L := L) (fun p => Additive.toMul (z₁.1 p))
    (fun p => Additive.toMul (z₂.1 p))
    (groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (G := L ≃ₐ[K] L) (M := Lˣ) z₁.1 z₁.2)
    (groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (G := L ≃ₐ[K] L) (M := Lˣ) z₂.1 z₂.2)
    (groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (G := L ≃ₐ[K] L) (M := Lˣ) (z₁ + z₂).1
      (z₁ + z₂).2)
  rw [show NormalizedCocycle.normalize (fun p => Additive.toMul ((z₁ + z₂).1 p)) _ = _ from e]
  exact lemma_3_15 _ _

theorem cocycleClass_of_mem_coboundaries₂
    (z : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ))
    (hz : z.1 ∈ groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) :
    cocycleClass z = 1 := by
  have hb := groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂ (G := L ≃ₐ[K] L) (M := Lˣ)
    z.1 hz
  have hco := NormalizedCocycle.normalize_cohomologous_one _
    (groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (G := L ≃ₐ[K] L) (M := Lˣ) z.1 z.2) hb
  rw [cocycleClass, ← mk_crossedProduct_one (K := K) (L := L)]
  exact mk_crossedProduct_eq_of_cohomologous _ _ hco

theorem mem_coboundaries₂_of_cocycleClass_eq_one
    (z : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ))
    (h : cocycleClass z = 1) :
    z.1 ∈ groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) := by
  have hz := groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (G := L ≃ₐ[K] L) (M := Lˣ) z.1 z.2
  set ψ := NormalizedCocycle.normalize (fun p => Additive.toMul (z.1 p)) hz with hψ
  obtain ⟨m, hm, ⟨e⟩⟩ := (BrauerGroup.mk_eq_one_iff _).1 h
  obtain ⟨n, hn, ⟨e'⟩⟩ := (BrauerGroup.mk_eq_one_iff _).1
    (mk_crossedProduct_one (K := K) (L := L))
  have d1 : Module.finrank K (CrossedProduct ψ) = Module.finrank K L ^ 2 :=
    CrossedProduct.finrank_eq ψ
  have d2 : Module.finrank K (CrossedProduct (NormalizedCocycle.one (K := K) (L := L))) =
      Module.finrank K L ^ 2 := CrossedProduct.finrank_eq _
  have f1 : Module.finrank K (CrossedProduct ψ) =
      Module.finrank K (Matrix (Fin m) (Fin m) K) := e.toLinearEquiv.finrank_eq
  have f2 : Module.finrank K (CrossedProduct (NormalizedCocycle.one (K := K) (L := L))) =
      Module.finrank K (Matrix (Fin n) (Fin n) K) := e'.toLinearEquiv.finrank_eq
  rw [Module.finrank_matrix] at f1 f2
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at f1 f2
  have hmn : m = n := by
    have h1 : m * m = n * n := by
      rw [d1] at f1
      rw [d2] at f2
      nlinarith
    nlinarith
  subst hmn
  have iso : CrossedProduct ψ ≃ₐ[K] CrossedProduct (NormalizedCocycle.one (K := K) (L := L)) :=
    e.trans e'.symm
  obtain ⟨hA, hc⟩ := thm_3_11_surj ψ
  obtain ⟨hA', hc'⟩ := thm_3_11_surj (NormalizedCocycle.one (K := K) (L := L))
  obtain ⟨x, hx⟩ := (thm_3_11_fibres _ _ _ _ hA hA' ψ NormalizedCocycle.one hc hc').1 ⟨iso⟩
  let f₀ : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ := fun p => Additive.toMul (z.1 p)
  have hbd : groupCohomology.IsMulCoboundary₂ f₀ := by
    refine ⟨fun σ => x σ * f₀ (1, 1), fun σ τ => ?_⟩
    have := hx σ τ
    have h2 : ψ (σ, τ) = f₀ (σ, τ) / σ • f₀ (1, 1) := rfl
    beta_reduce at this
    rw [h2, NormalizedCocycle.one_apply, div_one, eq_div_iff_mul_eq'] at this
    show σ • (x τ * f₀ (1, 1)) / (x (σ * τ) * f₀ (1, 1)) * (x σ * f₀ (1, 1)) = f₀ (σ, τ)
    rw [smul_mul', NormalizedCocycle.key_cancel]
    exact this
  exact (groupCohomology.coboundariesOfIsMulCoboundary₂ hbd).2

theorem mk_crossedProduct_mem_relBrauer (φ : NormalizedCocycle K L) :
    BrauerGroup.mk (CrossedProduct.toCSA φ) ∈ relBrauer K L := by
  rw [mk_mem_relBrauer_iff]
  exact (cor_3_6 (CrossedProduct.toCSA φ) L).2 ⟨CrossedProduct.toCSA φ,
    isBrauerEquivalent_of_algEquiv (AlgEquiv.refl), ⟨CrossedProduct.incl φ⟩,
    CrossedProduct.finrank_eq φ⟩

end Aux

/-- Theorem 3.14 of Milne: for a finite Galois extension $L/K$, $\varphi \mapsto [A(\varphi)]$
defines an isomorphism of abelian groups $H^2(L/K) \to \mathrm{Br}(L/K)$.  Stated as: there is an
injective group homomorphism $H^2(L/K) \to \mathrm{Br}(K)$ (written additively) sending the class of
every normalized cocycle $\varphi$ to $[A(\varphi)]$, with image $\mathrm{Br}(L/K)$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 3.14, p. 137"]
theorem thm_3_14 [IsGalois K L] :
    ∃ f : groupCohomology.H2 (Rep.ofAlgebraAutOnUnits K L) →+ Additive (BrauerGroup.{0, 0} K),
      Function.Injective f ∧
        (∀ φ : NormalizedCocycle K L,
          f (NormalizedCocycle.toH2 φ) = Additive.ofMul (BrauerGroup.mk (CrossedProduct.toCSA φ))) ∧
        ∀ x : BrauerGroup.{0, 0} K, x ∈ relBrauer K L ↔ Additive.ofMul x ∈ f.range := by
  classical
  change ∃ f : groupCohomology.H2 (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) →+
      Additive (BrauerGroup.{0, 0} K),
      Function.Injective f ∧
        (∀ φ : NormalizedCocycle K L,
          f (NormalizedCocycle.toH2 φ) = Additive.ofMul (BrauerGroup.mk (CrossedProduct.toCSA φ))) ∧
        ∀ x : BrauerGroup.{0, 0} K, x ∈ relBrauer K L ↔ Additive.ofMul x ∈ f.range
  let g : (ModuleCat.of ℤ (groupCohomology.cocycles₂
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ))) →+ Additive (BrauerGroup.{0, 0} K) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (cocycleClass z)) (fun a b => by
      show Additive.ofMul (cocycleClass (a + b)) = _
      rw [cocycleClass_add]
      rfl)
  let π : (ModuleCat.of ℤ (groupCohomology.cocycles₂
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ))) →+
      groupCohomology.H2 (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) :=
    (groupCohomology.H2π (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)).hom.toAddMonoidHom
  have hsurj : Function.Surjective π := fun x =>
    groupCohomology.H2_induction_on x (fun z => ⟨z, rfl⟩)
  have hker : π.ker ≤ g.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker] at hz ⊢
    have hz' : (groupCohomology.H2π (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) z = 0 := hz
    rw [groupCohomology.H2π_eq_zero_iff] at hz'
    have := cocycleClass_of_mem_coboundaries₂ z hz'
    show Additive.ofMul (cocycleClass z) = 0
    rw [this]
    rfl
  let f := AddMonoidHom.liftOfSurjective π hsurj ⟨g, hker⟩
  have hfπ : ∀ z, f (π z) = g z := fun z =>
    AddMonoidHom.liftOfRightInverse_comp_apply π _ _ ⟨g, hker⟩ z
  have hf : ∀ φ : NormalizedCocycle K L,
      f (NormalizedCocycle.toH2 φ) =
        Additive.ofMul (BrauerGroup.mk (CrossedProduct.toCSA φ)) := by
    intro φ
    have h1 : NormalizedCocycle.toH2 φ =
        π (groupCohomology.cocyclesOfIsMulCocycle₂ φ.isMulCocycle₂) := rfl
    rw [h1, hfπ]
    show Additive.ofMul (cocycleClass _) = _
    unfold cocycleClass
    exact congrArg (fun a => Additive.ofMul (BrauerGroup.mk (CrossedProduct.toCSA a)))
      (NormalizedCocycle.normalize_eq φ _ (fun p => rfl) _)
  refine ⟨f, ?_, hf, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := hsurj x
    rw [hfπ] at hx
    have hx' : cocycleClass z = 1 := hx
    have := mem_coboundaries₂_of_cocycleClass_eq_one z hx'
    show (groupCohomology.H2π (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) z = 0
    rw [groupCohomology.H2π_eq_zero_iff]
    exact this
  · intro x
    constructor
    · intro hx
      obtain ⟨φ, rfl⟩ := exists_crossedProduct_of_mem_relBrauer x hx
      exact ⟨_, hf φ⟩
    · rintro ⟨c, hc⟩
      obtain ⟨z, rfl⟩ := hsurj c
      rw [hfπ] at hc
      have hc' : cocycleClass z = x := hc
      rw [← hc']
      exact mk_crossedProduct_mem_relBrauer _

end H2

end NumberFieldKB.MilneCFT.Ch4
