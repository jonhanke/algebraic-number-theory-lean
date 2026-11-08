import NumberFieldKB.WeilBNT.AlgebraAdeleTopology

/-!
# Weil, *Basic Number Theory*, Chapter IV, §3, Theorem 4 (division algebras over a number field)

$k$ is a number field (here `F`) and $D$ a division algebra of finite dimension over $k$. As in
`NumberFieldKB.WeilBNT.AlgebraAdeleTopology`, $D_{\mathbb A}=k_{\mathbb A}\otimes_kD$ carries the topology of
$k_{\mathbb A}^n$ through coordinates, and its idele group $D_{\mathbb A}^\times$ carries Mathlib's topology on units,
for which $x\mapsto(x,x^{-1})$ is a homeomorphism onto its image in $D_{\mathbb A}\times D_{\mathbb A}$: this is
Weil's Def. 2. $D^\times$ sits in $D_{\mathbb A}^\times$ as $a\mapsto1\otimes a$ (`unitsA`, image `unitsD`), and
$D_{\mathbb A}^\times/D^\times$ is the space of left cosets $dD^\times$.

**Theorem 4** (p. 74): for $\mu\ge1$, the set $D_\mu$ of $d\in D_{\mathbb A}^\times$ such that the modules of $x\mapsto dx$
and $x\mapsto xd$ are respectively $\le\mu$ and $\ge\mu^{-1}$ is closed in $D_{\mathbb A}^\times$, with compact image in
$D_{\mathbb A}^\times/D^\times$. The modules are $\lvert N(d)\rvert_{\mathbb A}$ (`modL`) and
$\lvert N'(d)\rvert_{\mathbb A}$ (`modR`), by the Corollary of Prop. 3 and the text p. 74
(`algVol_mul_left`, `algVol_mul_right`).

* **`weil_IV_3_thm4`**, for every real $\mu$ (the condition $\mu\ge1$ is not needed).

*Proof* (Weil's): take a compact $C\subset D_{\mathbb A}$ of volume $>\mu$ (the volume of $D_{\mathbb A}/D$ being $1$);
put $C'=C-C$, $C''=C'C'$. For $d\in D_\mu$, $Cd$ and $d^{-1}C$ have volume $>1$, so (II.4 Lemma 1, `algBlichfeldt`)
there are $c_1,c_2\in C'$ with $b_1=c_1d$ and $b_2=d^{-1}c_2$ in $D^\times$. Then $b_1b_2=c_1c_2$ lies in the finite set
$D^\times\cap C''=\{\gamma_1,\dots,\gamma_N\}$, so $\gamma_i^{-1}c_1c_2=1$, $c_2$ is invertible with
$c_2^{-1}=\gamma_i^{-1}c_1$, and $db_2=c_2$ lies in the compact set $X$ of ideles $x$ with $x\in C'$ and
$x^{-1}\in\bigcup_i\gamma_i^{-1}C'$. Hence $D_\mu\subset XD^\times$. As $D_\mu$ is closed and stable under $D^\times$
(product formula, `modL_unitsA`, `modR_unitsA`), its image is a closed subset of the compact image of $X$.
-/

open IsDedekindDomain NumberField MeasureTheory QuadFormsKB.Tamagawa.Measure.Weil Topology
open scoped TensorProduct Pointwise

noncomputable section

namespace NumberFieldKB.WeilBNT

attribute [local instance] adelesAlgebra algAdeleTop continuous_mul_algAdele continuous_add_algAdele
  t2Space_algAdele

variable {F : Type} [Field F] [NumberField F] {D : Type} [DivisionRing D] [Algebra F D] [FiniteDimensional F D]

variable (F D) in
/-- $D^\times$ as a subgroup of the idele group of $D$. -/
def unitsD : Subgroup (Adeles F ⊗[F] D)ˣ := (unitsA (F := F) (A := D)).range

variable (F D) in
/-- Weil's $D_\mu$: the ideles $d$ of $D$ with module of $x\mapsto dx$ at most $\mu$ and module of $x\mapsto xd$ at least
$\mu^{-1}$. -/
def weilDmu (μ : ℝ) : Set (Adeles F ⊗[F] D)ˣ := {d | modL F D d ≤ μ ∧ μ⁻¹ ≤ modR F D d}

theorem modL_one : modL F D 1 = 1 := by
  have h := modL_mul (F := F) (A := D) 1 1
  rw [mul_one] at h
  have hp := modL_pos (F := F) (A := D) 1
  field_simp at h
  linarith [h]

theorem modR_one : modR F D 1 = 1 := by
  have h := modR_mul (F := F) (A := D) 1 1
  rw [mul_one] at h
  have hp := modR_pos (F := F) (A := D) 1
  field_simp at h
  linarith [h]

theorem modL_inv (d : (Adeles F ⊗[F] D)ˣ) : modL F D d⁻¹ = (modL F D d)⁻¹ := by
  have h := modL_mul (F := F) (A := D) d d⁻¹
  rw [mul_inv_cancel, modL_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- $D_\mu$ is stable under right multiplication by $D^\times$ (product formula). -/
theorem weilDmu_mul_unitsD {μ : ℝ} {d : (Adeles F ⊗[F] D)ˣ} (hd : d ∈ weilDmu F D μ) {h : (Adeles F ⊗[F] D)ˣ}
    (hh : h ∈ unitsD F D) : d * h ∈ weilDmu F D μ := by
  obtain ⟨a, rfl⟩ := hh
  refine ⟨?_, ?_⟩
  · rw [modL_mul, modL_unitsA, mul_one]; exact hd.1
  · rw [modR_mul, modR_unitsA, mul_one]; exact hd.2

/-- Subtraction is continuous on $D_{\mathbb A}$ (it is so in coordinates). -/
theorem continuousSub_algAdele : ContinuousSub (Adeles F ⊗[F] D) := by
  refine ⟨?_⟩
  have hc : Continuous (coordsA F D) := continuous_induced_dom
  rw [continuous_induced_rng]
  have : (coordsA F D ∘ fun p : (Adeles F ⊗[F] D) × (Adeles F ⊗[F] D) => p.1 - p.2) =
      fun p => coordsA F D p.1 - coordsA F D p.2 := by
    funext p; simp
  rw [this]
  exact (hc.comp continuous_fst).sub (hc.comp continuous_snd)

attribute [local instance] continuousSub_algAdele

/-- A one-sided inverse in $D_{\mathbb A}$ is two-sided (it is a finite free algebra over $k_{\mathbb A}$). -/
theorem isUnit_of_mul_eq_one_algAdele {u c : Adeles F ⊗[F] D} (h : u * c = 1) : IsUnit c := by
  have hsurj : Function.Surjective (LinearMap.mulRight (Adeles F) c) := fun x => ⟨x * u, by
    rw [LinearMap.mulRight_apply, mul_assoc, h, mul_one]⟩
  have hinj := OrzechProperty.injective_of_surjective_endomorphism _ hsurj
  exact isUnit_of_bijective_mulRight ⟨hinj, hsurj⟩

/-- **Weil, IV.§3, Theorem 4** (number field case): $D_\mu$ is closed in $D_{\mathbb A}^\times$ and its image in
$D_{\mathbb A}^\times/D^\times$ is compact. -/
@[kb "weil1973bnt" "Ch. IV, §3, Thm. 4 (p. 74), number field case"]
theorem weil_IV_3_thm4 (μ : ℝ) :
    IsClosed (weilDmu F D μ) ∧
      IsCompact ((QuotientGroup.mk : (Adeles F ⊗[F] D)ˣ → (Adeles F ⊗[F] D)ˣ ⧸ unitsD F D) '' weilDmu F D μ) := by
  have hclosed : IsClosed (weilDmu F D μ) :=
    (isClosed_le continuous_modL continuous_const).inter (isClosed_le continuous_const continuous_modR)
  refine ⟨hclosed, ?_⟩
  -- the image is closed, since `weilDmu` is saturated
  have himgClosed : IsClosed ((QuotientGroup.mk : (Adeles F ⊗[F] D)ˣ → (Adeles F ⊗[F] D)ˣ ⧸ unitsD F D) ''
      weilDmu F D μ) := by
    rw [← (QuotientGroup.isQuotientMap_mk (unitsD F D)).isClosed_preimage]
    convert hclosed using 1
    ext x
    refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
    rintro ⟨d, hd, hdx⟩
    have : d⁻¹ * x ∈ unitsD F D := QuotientGroup.eq.mp hdx
    have hx : x = d * (d⁻¹ * x) := by group
    rw [hx]
    exact weilDmu_mul_unitsD hd this
  rcases le_or_gt μ 0 with hμ | hμ
  · -- `weilDmu` is empty
    have : weilDmu F D μ = ∅ := by
      ext d
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hd => absurd (hd.1.trans hμ) (not_le.mpr (modL_pos d))
    rw [this, Set.image_empty]
    exact isCompact_empty
  -- the compact sets `C`, `C'`, `C''`
  obtain ⟨C, hC, hCvol⟩ := exists_isCompact_algVol_gt (F := F) (A := D) (ENNReal.ofReal μ) ENNReal.ofReal_ne_top
  set C' : Set (Adeles F ⊗[F] D) := (fun p : (Adeles F ⊗[F] D) × (Adeles F ⊗[F] D) => p.1 - p.2) '' (C ×ˢ C)
    with hC'def
  have hC' : IsCompact C' := (hC.prod hC).image (continuous_fst.sub continuous_snd)
  set C'' : Set (Adeles F ⊗[F] D) := (fun p : (Adeles F ⊗[F] D) × (Adeles F ⊗[F] D) => p.1 * p.2) '' (C' ×ˢ C')
    with hC''def
  have hC'' : IsCompact C'' := (hC'.prod hC').image (continuous_fst.mul continuous_snd)
  set Γ : Set D := {a : D | (1 : Adeles F) ⊗ₜ[F] a ∈ C''} with hΓdef
  have hΓ : Γ.Finite := finite_inter_isCompact hC''
  set K : Set (Adeles F ⊗[F] D) := ⋃ a ∈ Γ, (fun c => ((1 : Adeles F) ⊗ₜ[F] a⁻¹) * c) '' C' with hKdef
  have hK : IsCompact K := hΓ.isCompact_biUnion fun a _ => hC'.image (continuous_const.mul continuous_id)
  set X : Set (Adeles F ⊗[F] D)ˣ := Units.embedProduct (Adeles F ⊗[F] D) ⁻¹' (C' ×ˢ (MulOpposite.op '' K))
    with hXdef
  have hX : IsCompact X :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC'.prod (hK.image MulOpposite.continuous_op))
  -- the key inclusion
  have hsub : (QuotientGroup.mk : (Adeles F ⊗[F] D)ˣ → (Adeles F ⊗[F] D)ˣ ⧸ unitsD F D) '' weilDmu F D μ ⊆
      QuotientGroup.mk '' X := by
    rintro _ ⟨d, hd, rfl⟩
    have hμinv : 1 < ENNReal.ofReal μ⁻¹ * algVol F D C := by
      have h1 : ENNReal.ofReal μ⁻¹ * ENNReal.ofReal μ = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hμ.le), inv_mul_cancel₀ hμ.ne', ENNReal.ofReal_one]
      rw [← h1]
      gcongr
      simp
    -- `c₁ d ∈ D^×`
    have hCd : IsCompact ((fun x => x * (d : Adeles F ⊗[F] D)) '' C) :=
      hC.image (continuous_id.mul continuous_const)
    have hdR : IsUnit (coregularNorm (d : Adeles F ⊗[F] D)) := (weil_IV_3_coregular_iff _).mp d.isUnit
    have hvol1 : 1 < algVol F D ((fun x => x * (d : Adeles F ⊗[F] D)) '' C) := by
      rw [algVol_mul_right d hdR (measurableSet_coords_of_isCompact hC)]
      have hR : ideleNorm F hdR.unit = modR F D d := by
        unfold modR; congr 1; exact Units.ext rfl
      rw [hR]
      calc 1 < ENNReal.ofReal μ⁻¹ * algVol F D C := hμinv
        _ ≤ ENNReal.ofReal (modR F D d) * algVol F D C := by gcongr; exact hd.2
    obtain ⟨a₁, ha₁, _, ⟨x₁, hx₁, rfl⟩, _, ⟨y₁, hy₁, rfl⟩, h₁⟩ :=
      algBlichfeldt (measurableSet_coords_of_isCompact hCd) hvol1
    -- `d⁻¹ c₂ ∈ D^×`
    have hdC : IsCompact ((fun x => ((d⁻¹ : (Adeles F ⊗[F] D)ˣ) : Adeles F ⊗[F] D) * x) '' C) :=
      hC.image (continuous_const.mul continuous_id)
    have hvol2 : 1 < algVol F D ((fun x => ((d⁻¹ : (Adeles F ⊗[F] D)ˣ) : Adeles F ⊗[F] D) * x) '' C) := by
      rw [algVol_mul_left d⁻¹ (measurableSet_coords_of_isCompact hC)]
      have hL : ideleNorm F (Units.map (Algebra.norm (Adeles F)) d⁻¹) = (modL F D d)⁻¹ := modL_inv d
      rw [hL]
      calc 1 < ENNReal.ofReal μ⁻¹ * algVol F D C := hμinv
        _ ≤ ENNReal.ofReal (modL F D d)⁻¹ * algVol F D C := by
          gcongr
          all_goals first | exact modL_pos d | exact hd.1
    obtain ⟨a₂, ha₂, _, ⟨x₂, hx₂, rfl⟩, _, ⟨y₂, hy₂, rfl⟩, h₂⟩ :=
      algBlichfeldt (measurableSet_coords_of_isCompact hdC) hvol2
    set c₁ := x₁ - y₁
    set c₂ := x₂ - y₂
    have hc₁ : c₁ ∈ C' := ⟨(x₁, y₁), ⟨hx₁, hy₁⟩, rfl⟩
    have hc₂ : c₂ ∈ C' := ⟨(x₂, y₂), ⟨hx₂, hy₂⟩, rfl⟩
    have hb₁ : c₁ * (d : Adeles F ⊗[F] D) = (1 : Adeles F) ⊗ₜ[F] a₁ := by
      rw [← h₁]; simp only [c₁, sub_mul]
    have hb₂ : ((d⁻¹ : (Adeles F ⊗[F] D)ˣ) : Adeles F ⊗[F] D) * c₂ = (1 : Adeles F) ⊗ₜ[F] a₂ := by
      rw [← h₂]; simp only [c₂, mul_sub]
    -- `b₁ b₂ = c₁ c₂ ∈ D ∩ C''`
    have hprod : c₁ * c₂ = (1 : Adeles F) ⊗ₜ[F] (a₁ * a₂) := by
      have : c₁ * c₂ = (c₁ * (d : Adeles F ⊗[F] D)) * (((d⁻¹ : (Adeles F ⊗[F] D)ˣ) : Adeles F ⊗[F] D) * c₂) := by
        rw [mul_assoc, ← mul_assoc (d : Adeles F ⊗[F] D), Units.mul_inv, one_mul]
      rw [this, hb₁, hb₂, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hγ : a₁ * a₂ ∈ Γ := by
      show (1 : Adeles F) ⊗ₜ[F] (a₁ * a₂) ∈ C''
      rw [← hprod]; exact ⟨(c₁, c₂), ⟨hc₁, hc₂⟩, rfl⟩
    have hγ0 : a₁ * a₂ ≠ 0 := mul_ne_zero ha₁ ha₂
    -- `c₂` is a unit with inverse `γ⁻¹ c₁`
    have hinvγ : ((1 : Adeles F) ⊗ₜ[F] (a₁ * a₂)⁻¹) * ((1 : Adeles F) ⊗ₜ[F] (a₁ * a₂)) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hγ0]; rfl
    have hleft : ((1 : Adeles F) ⊗ₜ[F] (a₁ * a₂)⁻¹ * c₁) * c₂ = 1 := by
      rw [mul_assoc, hprod, hinvγ]
    obtain ⟨u, hu⟩ := isUnit_of_mul_eq_one_algAdele hleft
    have hu_inv : ((u⁻¹ : (Adeles F ⊗[F] D)ˣ) : Adeles F ⊗[F] D) = (1 : Adeles F) ⊗ₜ[F] (a₁ * a₂)⁻¹ * c₁ := by
      calc ((u⁻¹ : (Adeles F ⊗[F] D)ˣ) : Adeles F ⊗[F] D)
          = ((1 : Adeles F) ⊗ₜ[F] (a₁ * a₂)⁻¹ * c₁ * (u : Adeles F ⊗[F] D)) *
              ((u⁻¹ : (Adeles F ⊗[F] D)ˣ) : Adeles F ⊗[F] D) := by rw [hu, hleft, one_mul]
        _ = (1 : Adeles F) ⊗ₜ[F] (a₁ * a₂)⁻¹ * c₁ := by rw [mul_assoc _ (u : Adeles F ⊗[F] D), Units.mul_inv, mul_one]
    -- `u ∈ X`
    have huX : u ∈ X := by
      refine ⟨show (u : Adeles F ⊗[F] D) ∈ C' from hu ▸ hc₂, ?_⟩
      refine ⟨((u⁻¹ : (Adeles F ⊗[F] D)ˣ) : Adeles F ⊗[F] D), ?_, rfl⟩
      rw [hu_inv]
      exact Set.mem_biUnion hγ ⟨c₁, hc₁, rfl⟩
    -- `d = u b₂⁻¹`, so `d D^× = u D^×`
    have ha₂u : IsUnit a₂ := isUnit_iff_ne_zero.mpr ha₂
    have hdu : unitsA ha₂u.unit = d⁻¹ * u := by
      apply Units.ext
      rw [unitsA_val, IsUnit.unit_spec, Units.val_mul, ← hb₂, hu]
    refine ⟨u, huX, ?_⟩
    rw [QuotientGroup.eq]
    refine ⟨ha₂u.unit⁻¹, ?_⟩
    rw [map_inv, hdu, mul_inv_rev, inv_inv]
  exact hX.image continuous_quot_mk |>.of_isClosed_subset himgClosed hsub

end NumberFieldKB.WeilBNT
