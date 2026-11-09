import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Tate

/-!
# Milne, *Class Field Theory*, Chapter II §3: Lemma 3.3

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits

variable {G : Type} [Group G] [Fintype G]

/-! ## Lemma 3.3 -/

/-- The trivial $G$-module $\mathbb Q / \mathbb Z$. -/
noncomputable abbrev QZ : Type := ℚ ⧸ (Int.castAddHom ℚ).range

/-- The exact sequence $0 \to \mathbb Z \to \mathbb Q \to \mathbb Q/\mathbb Z \to 0$ of trivial $G$-modules. -/
noncomputable def seqZQ (G : Type) [Group G] : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (Rep.ofHom (X := ℤ) (Y := ℚ) (ρ := Representation.trivial ℤ G ℤ)
      (σ := Representation.trivial ℤ G ℚ) ⟨(Int.castAddHom ℚ).toIntLinearMap, fun _ => rfl⟩)
    (Rep.ofHom (X := ℚ) (Y := QZ) (ρ := Representation.trivial ℤ G ℚ) (σ := Representation.trivial ℤ G QZ)
      ⟨(QuotientAddGroup.mk' _).toIntLinearMap, fun _ => rfl⟩)
    (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact (QuotientAddGroup.eq_zero_iff _).2 ⟨x, rfl⟩)

theorem seqZQ_shortExact (G : Type) [Group G] : (seqZQ G).ShortExact := by
  have h1 : (seqZQ G).Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful (seqZQ G) (F := forget₂ (Rep ℤ G) (ModuleCat ℤ)),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    ext x
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨y, rfl⟩
      exact (QuotientAddGroup.eq_zero_iff _).2 ⟨y, rfl⟩
    · intro hx
      obtain ⟨y, hy⟩ := (QuotientAddGroup.eq_zero_iff _).1 hx
      exact ⟨y, hy⟩
  have h2 : Mono (seqZQ G).f := by
    rw [Rep.mono_iff_injective]
    intro a b h
    exact Int.cast_injective (α := ℚ) (by exact h)
  have h3 : Epi (seqZQ G).g := by
    rw [Rep.epi_iff_surjective]
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact ⟨x, rfl⟩
  exact { exact := h1, mono_f := h2, epi_g := h3 }

instance (n : ℤ) : (tateCohomologyFunctor (R := ℤ) (G := G) n).Additive := by
  unfold tateCohomologyFunctor
  infer_instance

/-- **Lemma 3.3 (a)** (p. 80). $H^r_T(G, \mathbb Q) = 0$ for all $r \in \mathbb Z$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Lemma 3.3 (a), p. 80"]
theorem lemma_3_3a (r : ℤ) : IsZero (tateCohomology (trivial ℤ G ℚ) r) := by
  classical
  set n : ℕ := Fintype.card G with hn
  have hn0 : (n : ℚ) ≠ 0 := by
    have : 0 < n := Fintype.card_pos
    exact_mod_cast this.ne'
  -- division by n, as a morphism of representations
  let g : trivial ℤ G ℚ ⟶ trivial ℤ G ℚ :=
    Rep.ofHom (X := ℚ) (Y := ℚ) (ρ := Representation.trivial ℤ G ℚ)
      (σ := Representation.trivial ℤ G ℚ)
      ⟨(AddMonoidHom.mulLeft ((n : ℚ)⁻¹)).toIntLinearMap, fun _ => rfl⟩
  have hgf : g ≫ ((n : ℤ) • 𝟙 (trivial ℤ G ℚ)) = 𝟙 _ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have : ((g ≫ ((n : ℤ) • 𝟙 (trivial ℤ G ℚ))).hom.toLinearMap x : ℚ) = (n : ℤ) • ((n : ℚ)⁻¹ * x) := rfl
    refine this.trans ?_
    rw [zsmul_eq_mul]
    field_simp
    rfl
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : tateCohomology (trivial ℤ G ℚ) r, x = 0 by rw [h x, h y]
  intro x
  have h1 : x = (tateCohomologyFunctor r).map (g ≫ ((n : ℤ) • 𝟙 (trivial ℤ G ℚ))) x := by
    rw [hgf, CategoryTheory.Functor.map_id]; rfl
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id] at h1
  rw [h1]
  have h3 := tate_card_smul_eq_zero (trivial ℤ G ℚ) r ((tateCohomologyFunctor r).map g x)
  simpa using h3

theorem tate0_aux : Nonempty (tateCohomology (trivial ℤ G ℤ) 0 ≃+ ZMod (Fintype.card G)) := by
  classical
  let M : Rep ℤ G := trivial ℤ G ℤ
  let S := (tateComplex M).sc' (-1) 0 1
  have hg : S.g = 0 := by
    show (tateComplex M).d 0 1 = 0
    refine (tateComplex_d_ofNat M 0).trans ?_
    ext; simp [inhomogeneousCochains.d, Unique.eq_default (α := Fin 0 → G),
      CochainComplex.of.d, Representation.isTrivial_apply]
    rfl
  let e1 : tateCohomology M 0 ≅ S.homology :=
    (tateComplex M).homologyIsoSc' (-1) 0 1 (by simp) (by simp)
  let e2 : S.homology ≅ cokernel S.f :=
    (ShortComplex.LeftHomologyData.ofHasCokernel S hg).homologyIso
  let e3 := ModuleCat.cokernelIsoRangeQuotient S.f
  let e : tateCohomology M 0 ≃ₗ[ℤ] (S.X₂ ⧸ LinearMap.range S.f.hom) :=
    (e1 ≪≫ e2 ≪≫ e3).toLinearEquiv
  let φ : S.X₂ →ₗ[ℤ] ZMod (Fintype.card G) :=
    (Int.castAddHom (ZMod (Fintype.card G))).toIntLinearMap ∘ₗ
      (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 0 → G => ℤ) default)
  have hφs : Function.Surjective φ := by
    intro y
    have : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
    refine ⟨fun _ => (y.val : ℤ), ?_⟩
    show Int.castAddHom (ZMod (Fintype.card G)) ((y.val : ℕ) : ℤ) = y
    simp
  have hker : LinearMap.ker φ = LinearMap.range S.f.hom := by
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    have hnorm : ∀ c, (M.tateNorm.hom c) = fun _ => (Fintype.card G : ℤ) * c default := by
      intro c
      rw [Rep.tateNorm_eq]
      ext g
      simp [Representation.norm, Finsupp.lsum_apply, Finsupp.sum_fintype]
      show ∑ _x : G, c default = _
      simp
    have hnorm' : ∀ c : (Fin 0 → G) →₀ ℤ,
        S.f.hom c = fun _ => (Fintype.card G : ℤ) * c default :=
      fun c => hnorm c
    have : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
    constructor
    · intro h
      have h' : (Fintype.card G : ℤ) ∣ f default := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h
      obtain ⟨k, hk⟩ := h'
      refine ⟨Finsupp.single default k, ?_⟩
      rw [hnorm']
      funext x
      rw [Subsingleton.elim x default]
      simpa using hk.symm
    · rintro ⟨c, rfl⟩
      let c : (Fin 0 → G) →₀ ℤ := c
      have := hnorm' c
      show φ (S.f.hom c) = 0
      rw [this]
      show (((Fintype.card G : ℤ) * c default : ℤ) : ZMod (Fintype.card G)) = 0
      simp
  exact ⟨e.toAddEquiv.trans ((Submodule.quotEquivOfEq _ _ hker.symm).toAddEquiv.trans
    (φ.quotKerEquivOfSurjective hφs).toAddEquiv)⟩

/-- **Lemma 3.3 (b)** (p. 80). $H^0_T(G, \mathbb Z) \simeq \mathbb Z/(G:1)\mathbb Z$ and $H^1(G, \mathbb Z) = 0$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Lemma 3.3 (b), p. 80"]
theorem lemma_3_3b :
    Nonempty (tateCohomology (trivial ℤ G ℤ) 0 ≃+ ZMod (Fintype.card G)) ∧
      IsZero (groupCohomology (trivial ℤ G ℤ) 1) := by
  classical
  refine ⟨tate0_aux, ?_⟩
  · have hsub : Subsingleton (Additive G →+ ℤ) := by
      refine ⟨fun f g => ?_⟩
      have key : ∀ f : Additive G →+ ℤ, f = 0 := by
        intro f
        refine AddMonoidHom.ext fun x => ?_
        have h : Fintype.card (Additive G) • x = 0 := card_nsmul_eq_zero
        have h2 := congrArg f h
        rw [map_nsmul, map_zero] at h2
        simp only [nsmul_eq_mul, mul_eq_zero] at h2
        rcases h2 with h2 | h2
        · exact absurd (by exact_mod_cast h2) (Fintype.card_ne_zero)
        · simpa using h2
      rw [key f, key g]
    have hz : IsZero (ModuleCat.of ℤ (Additive G →+ ℤ)) :=
      ModuleCat.isZero_of_subsingleton _
    exact hz.of_iso (H1IsoOfIsTrivial (trivial ℤ G ℤ))

/-- **Lemma 3.3 (c)** (p. 80). The connecting map $H^1(G, \mathbb Q/\mathbb Z) \to H^2(G, \mathbb Z)$ of
$0 \to \mathbb Z \to \mathbb Q \to \mathbb Q/\mathbb Z \to 0$ is an isomorphism; composed with
$\operatorname{Hom}(G, \mathbb Q/\mathbb Z) \simeq H^1(G, \mathbb Q/\mathbb Z)$ (formula (16), Mathlib's
`groupCohomology.H1IsoOfIsTrivial`) it is the canonical isomorphism
$\operatorname{Hom}(G, \mathbb Q/\mathbb Z) \to H^2(G, \mathbb Z)$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Lemma 3.3 (c), p. 80"]
theorem lemma_3_3c : IsIso (δ (seqZQ_shortExact G) 1 2 rfl) := by
  have hz : ∀ (n : ℕ) [NeZero n], IsZero (groupCohomology (trivial ℤ G ℚ) n) := fun n _ =>
    (lemma_3_3a (G := G) n).of_iso ((TateCohomology.isoGroupCohomology n).app (trivial ℤ G ℚ)).symm
  exact isIso_δ_of_isZero (seqZQ_shortExact G) 1 (hz 1) (hz 2)

end NumberFieldKB.MilneCFT
