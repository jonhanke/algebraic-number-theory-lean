import NumberFieldKB.MilneCFT.Ch7.Cohomology
import NumberFieldKB.MilneCFT.Ch8.H2TauCeti

/-!
# Milne, *Class Field Theory*, Chapter VII, Proposition 2.2, proved unconditionally

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII,
Proposition 2.2.

The named statement `Prop2_2 K L` (`Cohomology.lean`) is proved here for every finite Galois extension $L/K$ of
number fields (`prop2_2`), without any hypothesis.

The proof goes through the explicit description of the Galois action on the finite components of an idele.
Our action on $\mathbb A_L$ is Tau Ceti's `adeleGaloisAction` (`smul_eq_adeleGaloisAction`), and Tau Ceti's semilocal
decomposition (`semilocalEquiv_baseChangeAutHom`) shows: if $\sigma w = w'$ then
$(\sigma x)_{w'} = \sigma_w(x_w)$ with $\sigma_w : L_w\to L_{w'}$ the isomorphism of completions
(`exists_smul_component`). We encode the transport $L_w^\times\to L_{w'}^\times$ as `transport σ w w'`
$u\mapsto(\sigma\cdot\iota_w(u))_{w'}$; its multiplicativity, composition law, and valuation invariance
(`transport_comp`, `valued_transport`) follow from that formula and the surjectivity of $\alpha\mapsto\alpha_w$.
Then the three fields of `Prop2_2` are proved: `stable` (`prop2_2_stable`), `bijective` (`prop2_2_bijective`) and
`units` (`prop2_2_units`), the last two via injectivity (an idele above $v$ is determined by its components at the
places $\tau^{-1}w_0$) and surjectivity (an explicit finite product of local ideles).
-/

open IsDedekindDomain NumberField NumberFieldKB.Ideles QuadFormsKB.Tamagawa.Measure.Weil
open scoped Pointwise Classical TensorProduct

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- `ideleComponent` is Tau Ceti's finite coordinate of an idele. -/
theorem ideleComponent_eq (w : HeightOneSpectrum (𝓞 L)) (x : IdeleGroup (𝓞 L) L) :
    ideleComponent L w x = w.ideleFiniteCoord x :=
  Units.ext rfl

theorem coe_ideleComponent (w : HeightOneSpectrum (𝓞 L)) (x : IdeleGroup (𝓞 L) L) :
    ((ideleComponent L w x : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      (x : AdeleRing (𝓞 L) L).2 w :=
  rfl

theorem ideleComponent_ofAdic_self (w : HeightOneSpectrum (𝓞 L)) (u : (w.adicCompletion L)ˣ) :
    ideleComponent L w (IdeleGroup.ofAdicCompletion (𝓞 L) L w u) = u := by
  rw [ideleComponent_eq]
  exact HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self w u

theorem ideleComponent_ofAdic_ne {w w' : HeightOneSpectrum (𝓞 L)} (h : w' ≠ w)
    (u : (w.adicCompletion L)ˣ) :
    ideleComponent L w' (IdeleGroup.ofAdicCompletion (𝓞 L) L w u) = 1 := by
  rw [ideleComponent_eq]
  exact HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne w' h u

/-- The component formula for the adeles: $(\sigma x)_{w'} = \sigma_w(x_w)$ for a suitable ring isomorphism of
completions $\sigma_w$, which preserves the valuations. -/
theorem exists_smul_snd (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]
    (h : w'.asIdeal = σ • w.asIdeal) (x : AdeleRing (𝓞 L) L) :
    (σ • x).2 w' = v.completionCongr σ h (x.2 w) := by
  have hmap (z : v.adicCompletion K ⊗[K] L) :
      Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (v.adicCompletion K))
        (σ : L →ₐ[K] L) z =
      TauCeti.Algebra.TensorProduct.baseChangeAutHom (v.adicCompletion K) L σ z := by
    induction z using TensorProduct.inductionOn with
    | tmul a y => simp
    | add y z hy hz => rw [map_add, map_add, hy, hz]
  have hw := congrFun (TauCeti.semilocalEquiv_finiteAdeleSemilocalHom (v := v)
    (TauCeti.GlobalNumberFields.finiteAdeleEquiv L L σ.toRingEquiv x.2)) ⟨w', inferInstance⟩
  rw [TauCeti.finiteAdeleSemilocalHom_finiteAdeleEquiv, hmap,
    TauCeti.semilocalEquiv_baseChangeAutHom σ (w := ⟨w, inferInstance⟩) (w' := ⟨w', inferInstance⟩) h,
    TauCeti.semilocalEquiv_finiteAdeleSemilocalHom] at hw
  rw [smul_eq_adeleGaloisAction, TauCeti.GlobalNumberFields.adeleGaloisAction_apply,
    TauCeti.GlobalNumberFields.adeleEquiv_snd]
  exact hw.symm

/-! ## The transport between completions -/

/-- The transport $L_w^\times\to L_{w'}^\times$ along $\sigma$: $u\mapsto(\sigma\cdot\iota_w(u))_{w'}$. For
$w' = \sigma w$ it is induced by the isomorphism of completions (`ideleComponent_smul`). -/
def transport (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) :
    (w.adicCompletion L)ˣ →* (w'.adicCompletion L)ˣ :=
  (ideleComponent L w').comp
    ((MulDistribMulAction.toMonoidHom (IdeleGroup (𝓞 L) L) σ).comp
      (IdeleGroup.ofAdicCompletion (𝓞 L) L w))

theorem transport_apply (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) (u : (w.adicCompletion L)ˣ) :
    transport σ w w' u = ideleComponent L w' (σ • IdeleGroup.ofAdicCompletion (𝓞 L) L w u) :=
  rfl

/-- **The component formula**: if $w' = \sigma w$ then $(\sigma\alpha)_{w'}$ is the transport of $\alpha_w$, and
the valuations agree. -/
theorem ideleComponent_smul (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝓞 L)}
    (h : w'.asIdeal = σ • w.asIdeal) (α : IdeleGroup (𝓞 L) L) :
    ideleComponent L w' (σ • α) = transport σ w w' (ideleComponent L w α) ∧
    Valued.v ((ideleComponent L w' (σ • α) : (w'.adicCompletion L)ˣ) : w'.adicCompletion L) =
      Valued.v ((ideleComponent L w α : (w.adicCompletion L)ˣ) : w.adicCompletion L) := by
  have h1 : w.asIdeal.LiesOver (primeBelow K L w).asIdeal := ⟨rfl⟩
  have h2 : w'.asIdeal.LiesOver (primeBelow K L w).asIdeal :=
    ⟨by rw [h]; exact (Ideal.under_smul (𝓞 K) w.asIdeal σ).symm⟩
  have key : ∀ β : IdeleGroup (𝓞 L) L,
      ((ideleComponent L w' (σ • β) : (w'.adicCompletion L)ˣ) : w'.adicCompletion L) =
        (primeBelow K L w).completionCongr σ h
          ((ideleComponent L w β : (w.adicCompletion L)ˣ) : w.adicCompletion L) :=
    fun β => exists_smul_snd σ (primeBelow K L w) w w' h (β : AdeleRing (𝓞 L) L)
  have htr : ∀ u : (w.adicCompletion L)ˣ,
      ((transport σ w w' u : (w'.adicCompletion L)ˣ) : w'.adicCompletion L) =
        (primeBelow K L w).completionCongr σ h (u : w.adicCompletion L) := fun u => by
    rw [transport_apply, key, ideleComponent_ofAdic_self]
  refine ⟨Units.ext ?_, ?_⟩
  · rw [key, htr]
  · rw [key, HeightOneSpectrum.valued_completionCongr]

theorem valued_transport (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝓞 L)}
    (h : w'.asIdeal = σ • w.asIdeal) (u : (w.adicCompletion L)ˣ) :
    Valued.v ((transport σ w w' u : (w'.adicCompletion L)ˣ) : w'.adicCompletion L) =
      Valued.v (u : w.adicCompletion L) := by
  have := (ideleComponent_smul σ h (IdeleGroup.ofAdicCompletion (𝓞 L) L w u)).2
  rw [ideleComponent_ofAdic_self] at this
  rw [transport_apply]
  exact this

theorem transport_comp (σ τ : L ≃ₐ[K] L) {w w' w'' : HeightOneSpectrum (𝓞 L)}
    (h2 : w''.asIdeal = τ • w'.asIdeal) (u : (w.adicCompletion L)ˣ) :
    transport τ w' w'' (transport σ w w' u) = transport (τ * σ) w w'' u := by
  rw [transport_apply σ, ← (ideleComponent_smul τ h2 _).1, transport_apply, mul_smul]

theorem transport_one (w : HeightOneSpectrum (𝓞 L)) (u : (w.adicCompletion L)ˣ) :
    transport (1 : L ≃ₐ[K] L) w w u = u := by
  rw [transport_apply, one_smul, ideleComponent_ofAdic_self]

theorem localSMul_eq_transport [IsGalois K L] (w₀ : HeightOneSpectrum (𝓞 L)) (σ : L ≃ₐ[K] L)
    (y : (w₀.adicCompletion L)ˣ) : localSMul K L w₀ σ y = transport σ w₀ w₀ y :=
  rfl

/-! ## Places -/

/-- The place $\sigma w$. -/
def actPlace (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 L) where
  asIdeal := σ • w.asIdeal
  isPrime := inferInstance
  ne_bot := by
    intro h
    apply w.ne_bot
    have : σ⁻¹ • (σ • w.asIdeal) = w.asIdeal := inv_smul_smul σ _
    rw [← this, h]
    simp

theorem actPlace_asIdeal (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (actPlace σ w).asIdeal = σ • w.asIdeal :=
  rfl

theorem primeBelow_actPlace (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    primeBelow K L (actPlace σ w) = primeBelow K L w := by
  apply HeightOneSpectrum.ext
  exact Ideal.under_smul (𝓞 K) w.asIdeal σ

theorem exists_smul_eq_of_primeBelow_eq [IsGalois K L] {w w₀ : HeightOneSpectrum (𝓞 L)}
    (h : primeBelow K L w = primeBelow K L w₀) : ∃ τ : L ≃ₐ[K] L, τ • w.asIdeal = w₀.asIdeal := by
  have : w₀.asIdeal.LiesOver (primeBelow K L w₀).asIdeal := ⟨rfl⟩
  have : w.asIdeal.LiesOver (primeBelow K L w₀).asIdeal := ⟨by rw [← h]; rfl⟩
  exact Ideal.exists_smul_eq_of_isGaloisGroup (primeBelow K L w₀).asIdeal w.asIdeal w₀.asIdeal
    (L ≃ₐ[K] L)

theorem idele_ext {x y : IdeleGroup (𝓞 L) L}
    (h1 : (x : AdeleRing (𝓞 L) L).1 = (y : AdeleRing (𝓞 L) L).1)
    (h2 : ∀ w, ideleComponent L w x = ideleComponent L w y) : x = y := by
  refine Units.ext (Prod.ext h1 ?_)
  apply RestrictedProduct.ext
  intro w
  exact congrArg Units.val (h2 w)

theorem ofAdic_fst (w : HeightOneSpectrum (𝓞 L)) (u : (w.adicCompletion L)ˣ) :
    ((IdeleGroup.ofAdicCompletion (𝓞 L) L w u : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L).1 = 1 := by
  funext w'
  have := congrArg Units.val (InfinitePlace.ideleInfiniteCoord_ofAdicCompletion
    (R := 𝓞 L) (K := L) w' w u)
  simpa [InfinitePlace.coe_ideleInfiniteCoord] using this

theorem fst_prod_ofAdic (S : Finset (HeightOneSpectrum (𝓞 L)))
    (u : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ) :
    ((∏ w ∈ S, IdeleGroup.ofAdicCompletion (𝓞 L) L w (u w) : IdeleGroup (𝓞 L) L) :
      AdeleRing (𝓞 L) L).1 = 1 := by
  funext w
  have h : w.ideleInfiniteCoord (∏ w' ∈ S, IdeleGroup.ofAdicCompletion (𝓞 L) L w' (u w')) = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun w' _ =>
      InfinitePlace.ideleInfiniteCoord_ofAdicCompletion (R := 𝓞 L) (K := L) w w' (u w')
  have := congrArg Units.val h
  rw [InfinitePlace.coe_ideleInfiniteCoord] at this
  exact this

/-! ## Stability of the local ideles -/

/-- **Proposition 2.2, first part**: $G_{w_0}$ preserves the ideles supported at $w_0$. -/
theorem prop2_2_stable [IsGalois K L] (w₀ : HeightOneSpectrum (𝓞 L)) (σ : L ≃ₐ[K] L)
    (hσ : σ • w₀.asIdeal = w₀.asIdeal) (y : (w₀.adicCompletion L)ˣ) :
    σ • IdeleGroup.ofAdicCompletion (𝓞 L) L w₀ y =
      IdeleGroup.ofAdicCompletion (𝓞 L) L w₀ (localSMul K L w₀ σ y) := by
  refine idele_ext ?_ fun w' => ?_
  · have h1 : ((σ • IdeleGroup.ofAdicCompletion (𝓞 L) L w₀ y : IdeleGroup (𝓞 L) L) :
        AdeleRing (𝓞 L) L).1 = 1 := by
      rw [val_smul_idele, smul_eq_adeleGaloisAction, TauCeti.GlobalNumberFields.adeleGaloisAction_fst,
        ofAdic_fst, map_one]
    rw [h1, ofAdic_fst]
  · by_cases hw : w' = w₀
    · subst hw
      rw [ideleComponent_ofAdic_self]
      rfl
    · rw [ideleComponent_ofAdic_ne hw]
      have h1 : w'.asIdeal = σ • (actPlace σ⁻¹ w').asIdeal := by
        rw [actPlace_asIdeal, smul_inv_smul]
      rw [(ideleComponent_smul σ h1 _).1]
      have hne : actPlace σ⁻¹ w' ≠ w₀ := by
        intro h
        apply hw
        have : w'.asIdeal = σ • w₀.asIdeal := by rw [← h]; exact h1
        exact HeightOneSpectrum.ext (this.trans hσ)
      rw [ideleComponent_ofAdic_ne hne, map_one]

/-! ## The construction of an idele with prescribed components -/

variable (K) in
/-- The finite set of places $\tau^{-1}w_0$ (the places above $v$, by transitivity). -/
def placesAbove (w₀ : HeightOneSpectrum (𝓞 L)) : Finset (HeightOneSpectrum (𝓞 L)) :=
  (Set.finite_range fun τ : L ≃ₐ[K] L => actPlace τ⁻¹ w₀).toFinset

theorem mem_placesAbove (w₀ w : HeightOneSpectrum (𝓞 L)) :
    w ∈ placesAbove K w₀ ↔ ∃ τ : L ≃ₐ[K] L, actPlace τ⁻¹ w₀ = w := by
  simp [placesAbove]

/-- The prescribed component at $w$: the transport of $f(\tau)$ for some $\tau$ with $\tau w = w_0$. -/
def uFam {w₀ : HeightOneSpectrum (𝓞 L)} (f : (L ≃ₐ[K] L) → (w₀.adicCompletion L)ˣ)
    (w : HeightOneSpectrum (𝓞 L)) : (w.adicCompletion L)ˣ :=
  if h : ∃ τ : L ≃ₐ[K] L, τ • w.asIdeal = w₀.asIdeal then transport h.choose⁻¹ w₀ w (f h.choose)
  else 1

/-- The idele $\prod_{w}\iota_w(u_w)$ over the finite set of places above $v$. -/
def idelePre (w₀ : HeightOneSpectrum (𝓞 L)) (f : (L ≃ₐ[K] L) → (w₀.adicCompletion L)ˣ) :
    IdeleGroup (𝓞 L) L :=
  ∏ w ∈ placesAbove K w₀, IdeleGroup.ofAdicCompletion (𝓞 L) L w (uFam f w)

theorem ideleComponent_idelePre (w₀ : HeightOneSpectrum (𝓞 L))
    (f : (L ≃ₐ[K] L) → (w₀.adicCompletion L)ˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ideleComponent L w (idelePre w₀ f) = if w ∈ placesAbove K w₀ then uFam f w else 1 := by
  rw [ideleComponent_eq]
  exact w.ideleFiniteCoord_prod_ofAdicCompletion _ _

theorem ideleComponent_idelePre_apply [IsGalois K L] (w₀ : HeightOneSpectrum (𝓞 L))
    (f : (L ≃ₐ[K] L) → (w₀.adicCompletion L)ˣ)
    (hf : ∀ σ τ : L ≃ₐ[K] L, σ • w₀.asIdeal = w₀.asIdeal → f (σ * τ) = localSMul K L w₀ σ (f τ))
    (τ : L ≃ₐ[K] L) : ideleComponent L w₀ (τ • idelePre w₀ f) = f τ := by
  have hmem : actPlace τ⁻¹ w₀ ∈ placesAbove K w₀ := (mem_placesAbove w₀ _).2 ⟨τ, rfl⟩
  have h1 : w₀.asIdeal = τ • (actPlace τ⁻¹ w₀).asIdeal := by
    rw [actPlace_asIdeal, smul_inv_smul]
  have hex : ∃ τ' : L ≃ₐ[K] L, τ' • (actPlace τ⁻¹ w₀).asIdeal = w₀.asIdeal := ⟨τ, h1.symm⟩
  rw [(ideleComponent_smul τ h1 _).1, ideleComponent_idelePre, if_pos hmem]
  unfold uFam
  rw [dif_pos hex]
  have hτ' := hex.choose_spec
  rw [transport_comp _ _ h1]
  have hσ : (τ * hex.choose⁻¹) • w₀.asIdeal = w₀.asIdeal := by
    rw [mul_smul, inv_smul_eq_iff.2 hτ'.symm, ← h1]
  have := hf (τ * hex.choose⁻¹) hex.choose hσ
  rw [localSMul_eq_transport, inv_mul_cancel_right] at this
  exact this.symm

theorem idelePre_mem [IsGalois K L] (w₀ : HeightOneSpectrum (𝓞 L))
    (f : (L ≃ₐ[K] L) → (w₀.adicCompletion L)ˣ) :
    idelePre w₀ f ∈ idelesAbove K L (primeBelow K L w₀) := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · exact congrFun (fst_prod_ofAdic _ _) w
  · have hnot : w ∉ placesAbove K w₀ := by
      intro hmem
      obtain ⟨τ, rfl⟩ := (mem_placesAbove w₀ w).1 hmem
      exact hw (primeBelow_actPlace _ _)
    rw [← coe_ideleComponent, ideleComponent_idelePre, if_neg hnot, Units.val_one]

theorem valued_idelePre [IsGalois K L] (w₀ : HeightOneSpectrum (𝓞 L))
    (f : (L ≃ₐ[K] L) → (w₀.adicCompletion L)ˣ) (hf1 : ∀ τ, Valued.v ((f τ : (w₀.adicCompletion L)ˣ) :
      w₀.adicCompletion L) = 1) (w : HeightOneSpectrum (𝓞 L)) :
    Valued.v (((idelePre w₀ f : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L).2 w) = 1 := by
  rw [← coe_ideleComponent, ideleComponent_idelePre]
  split_ifs with hmem
  · unfold uFam
    split_ifs with h
    · rw [valued_transport _ (eq_inv_smul_iff.2 h.choose_spec)]
      exact hf1 _
    · simp
  · simp

/-! ## Injectivity -/

theorem phi_inj [IsGalois K L] (w₀ : HeightOneSpectrum (𝓞 L)) {α β : IdeleGroup (𝓞 L) L}
    (hα : α ∈ idelesAbove K L (primeBelow K L w₀)) (hβ : β ∈ idelesAbove K L (primeBelow K L w₀))
    (h : (fun τ : L ≃ₐ[K] L => ideleComponent L w₀ (τ • α)) =
      fun τ : L ≃ₐ[K] L => ideleComponent L w₀ (τ • β)) : α = β := by
  refine idele_ext ?_ fun w => ?_
  · funext w
    rw [hα.1 w, hβ.1 w]
  · by_cases hw : primeBelow K L w = primeBelow K L w₀
    · obtain ⟨τ, hτ⟩ := exists_smul_eq_of_primeBelow_eq hw
      have h1 : w₀.asIdeal = τ • w.asIdeal := hτ.symm
      have e : ideleComponent L w₀ (τ • α) = ideleComponent L w₀ (τ • β) := congrFun h τ
      rw [(ideleComponent_smul τ h1 α).1, (ideleComponent_smul τ h1 β).1] at e
      have h2 : w.asIdeal = τ⁻¹ • w₀.asIdeal := eq_inv_smul_iff.2 hτ
      have := congrArg (transport τ⁻¹ w₀ w) e
      rwa [transport_comp _ _ h2, transport_comp _ _ h2, inv_mul_cancel, transport_one,
        transport_one] at this
    · have e1 : ideleComponent L w α = 1 :=
        Units.ext (by rw [coe_ideleComponent, hα.2 w hw, Units.val_one])
      have e2 : ideleComponent L w β = 1 :=
        Units.ext (by rw [coe_ideleComponent, hβ.2 w hw, Units.val_one])
      rw [e1, e2]

/-! ## Equivariance and the three fields -/

theorem phi_equivariant [IsGalois K L] (w₀ : HeightOneSpectrum (𝓞 L)) (α : IdeleGroup (𝓞 L) L)
    (σ τ : L ≃ₐ[K] L) (hσ : σ • w₀.asIdeal = w₀.asIdeal) :
    ideleComponent L w₀ ((σ * τ) • α) = localSMul K L w₀ σ (ideleComponent L w₀ (τ • α)) := by
  rw [mul_smul, localSMul_eq_transport, ← (ideleComponent_smul σ hσ.symm _).1]

/-- **Proposition 2.2, second part.** -/
theorem prop2_2_bijective [IsGalois K L] (w₀ : HeightOneSpectrum (𝓞 L)) :
    Set.BijOn (fun (α : IdeleGroup (𝓞 L) L) (τ : L ≃ₐ[K] L) => ideleComponent L w₀ (τ • α))
      (idelesAbove K L (primeBelow K L w₀))
      {f | ∀ σ τ : L ≃ₐ[K] L, σ • w₀.asIdeal = w₀.asIdeal →
        f (σ * τ) = localSMul K L w₀ σ (f τ)} := by
  refine ⟨fun α _ σ τ hσ => phi_equivariant w₀ α σ τ hσ, fun α hα β hβ h => phi_inj w₀ hα hβ h,
    fun f hf => ⟨idelePre w₀ f, idelePre_mem w₀ f, funext fun τ => ?_⟩⟩
  exact ideleComponent_idelePre_apply w₀ f hf τ

/-- **Proposition 2.2, third part** (the unit version). -/
theorem prop2_2_units [IsGalois K L] (w₀ : HeightOneSpectrum (𝓞 L)) :
    Set.BijOn (fun (α : IdeleGroup (𝓞 L) L) (τ : L ≃ₐ[K] L) => ideleComponent L w₀ (τ • α))
      {α | α ∈ idelesAbove K L (primeBelow K L w₀) ∧
        ∀ w, Valued.v ((α : AdeleRing (𝓞 L) L).2 w) = 1}
      {f | (∀ τ, Valued.v ((f τ : (w₀.adicCompletion L)ˣ) : w₀.adicCompletion L) = 1) ∧
        ∀ σ τ : L ≃ₐ[K] L, σ • w₀.asIdeal = w₀.asIdeal →
          f (σ * τ) = localSMul K L w₀ σ (f τ)} := by
  refine ⟨fun α hα => ⟨fun τ => ?_, fun σ τ hσ => phi_equivariant w₀ α σ τ hσ⟩,
    fun α hα β hβ h => phi_inj w₀ hα.1 hβ.1 h,
    fun f hf => ⟨idelePre w₀ f, ⟨idelePre_mem w₀ f, valued_idelePre w₀ f hf.1⟩,
      funext fun τ => ?_⟩⟩
  · have h1 : w₀.asIdeal = τ • (actPlace τ⁻¹ w₀).asIdeal := by
      rw [actPlace_asIdeal, smul_inv_smul]
    have := (ideleComponent_smul τ h1 α).2
    change Valued.v ((ideleComponent L w₀ (τ • α) : (w₀.adicCompletion L)ˣ) : w₀.adicCompletion L) = 1
    rw [this, coe_ideleComponent]
    exact hα.2 _
  · exact ideleComponent_idelePre_apply w₀ f hf.2 τ

/-- **Milne, *CFT*, Chapter VII, Proposition 2.2**, unconditionally: for every finite Galois extension $L/K$ of
number fields, the named statement `Prop2_2 K L` holds. -/
@[kb "milne2020cft" "Ch. VII, Prop. 2.2"]
theorem prop2_2 (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] : Prop2_2 K L where
  stable := prop2_2_stable
  bijective := prop2_2_bijective
  units := prop2_2_units

end NumberFieldKB.MilneCFT.Ch7
