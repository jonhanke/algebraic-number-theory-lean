import Mathlib.RingTheory.TotallySplit
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Module.ZLattice.Basic
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, IV.§4, Lemma 5

Let $G\cong\mathbb R^r\times\mathbb Z^{s+1-r}$ with $s\ge r\ge0$. If $r>0$, let $\lambda:G\to\mathbb R$ be a morphism
(continuous homomorphism) non-trivial on $\mathbb R^r$; if $r=0$, let $\lambda:G\to\mathbb Z$ be a non-trivial
morphism. Let $G_1=\ker\lambda$ and let $\Gamma$ be a discrete subgroup of $G_1$ with $G_1/\Gamma$ compact. Then
$\Gamma\cong\mathbb Z^s$.

Here $G$ is $(\mathrm{Fin}\,r\to\mathbb R)\times(\mathrm{Fin}\,(s+1-r)\to\mathbb Z)$ (Weil: "we may assume
$G=\mathbb R^r\times\mathbb Z^{s+1-r}$"; coordinates are 0-based, Weil's $x_0,\dots,x_s$ are the same), and for $r=0$
it is $\mathrm{Fin}\,(s+1)\to\mathbb Z$. $G_1$ carries the subspace topology, $G_1/\Gamma$ the quotient topology.

* **`weil_IV_4_lemma5_real`**: the case $r>0$.
* **`weil_IV_4_lemma5_int`**: the case $r=0$.
* **`weil_IV_4_lemma5`**: Weil's form, for any topological group $G$ isomorphic to $\mathbb R^r\times\mathbb Z^{s+1-r}$
  (case $r>0$).

*Proof* (Weil's). Embed $G$ in $V=\mathbb R^{s+1}$; $\lambda$ extends to a linear form, with kernel $V_1$ of
dimension $s$, and $G_1=G\cap V_1$ spans $V_1$ (Weil's vectors $e_j$). If $\Gamma$ did not span $V_1$, a non-zero linear
form $f$ on $V_1$ vanishing on $\Gamma$ would factor through the compact group $G_1/\Gamma$, so be bounded on $G_1$,
hence zero on $G_1$ (a bounded additive map vanishes), hence zero. So $\Gamma$ is a discrete subgroup of $V_1$ spanning
it: a lattice, free of rank $s$ (`Real.finrank_eq_int_finrank_of_discrete`, Weil's Prop. 11 of Chap. II-4).
-/

noncomputable section

namespace NumberFieldKB.WeilBNT

/-- An additive map to $\mathbb R$ bounded on a group is zero (look at $n\cdot h$). -/
theorem addMonoidHom_eq_zero_of_bounded {H : Type*} [AddCommGroup H] (g : H →+ ℝ) (C : ℝ)
    (hC : ∀ h, |g h| ≤ C) : g = 0 := by
  refine AddMonoidHom.ext fun h => ?_
  by_contra hne
  rw [AddMonoidHom.zero_apply] at hne
  have h0 : 0 < |g h| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |g h|)
  have := hC (n • h)
  rw [map_nsmul, nsmul_eq_mul, abs_mul, Nat.abs_cast] at this
  rw [div_lt_iff₀ h0] at hn
  linarith

/-- If $\varphi:H\to E$ is a continuous additive map whose image spans the finite-dimensional real space $E$,
and $\Gamma\le H$ has compact quotient, then $\varphi(\Gamma)$ spans $E$ (Weil's argument: a linear form
vanishing on $\varphi(\Gamma)$ factors through the compact quotient, so is bounded, so is zero). -/
theorem span_image_eq_top_of_compactQuotient {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (φ : H →+ E) (hφ : Continuous φ) (hspan : Submodule.span ℝ (Set.range φ) = ⊤)
    (Γ : AddSubgroup H) [CompactSpace (H ⧸ Γ)] :
    Submodule.span ℝ (φ '' (Γ : Set H)) = ⊤ := by
  by_contra hne
  have hlt : Submodule.span ℝ (φ '' (Γ : Set H)) < ⊤ := lt_top_iff_ne_top.mpr hne
  obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  let g : H →+ ℝ := (f : E →+ ℝ).comp φ
  have hgΓ : ∀ γ ∈ Γ, g γ = 0 := fun γ hγ => hfle (Submodule.subset_span ⟨γ, hγ, rfl⟩)
  have hgc : Continuous g :=
    (LinearMap.continuous_of_finiteDimensional f).comp hφ
  let gh : H ⧸ Γ →  ℝ := QuotientAddGroup.lift Γ g (fun γ hγ => hgΓ γ hγ)
  have hghc : Continuous gh :=
    ((QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff).mpr hgc
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hghc.continuousOn
  have hb : ∀ h, |g h| ≤ C := fun h => by
    have := hC (QuotientAddGroup.mk h) (Set.mem_univ _)
    exact this
  have hg0 := addMonoidHom_eq_zero_of_bounded g C hb
  have hker : Submodule.span ℝ (Set.range φ) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    have := congrArg (fun k : H →+ ℝ => k h) hg0
    simpa [g] using this
  rw [hspan] at hker
  exact hf0 (LinearMap.ker_eq_top.mp (top_le_iff.mp hker))

/-- **Abstract core of Lemma 5.** Let $E$ be a finite-dimensional real normed space, $H$ a topological
additive commutative group, $\varphi:H\to E$ a continuous additive topological embedding whose image spans $E$, and
$\Gamma\le H$ discrete with compact quotient. Then $\Gamma\cong\mathbb Z^{\dim E}$: $\varphi(\Gamma)$ is a discrete
subgroup of $E$ spanning $E$, hence a lattice. -/
theorem nonempty_addEquiv_pi_of_embedding {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (φ : H →+ E) (hφ : Topology.IsEmbedding φ) (hspan : Submodule.span ℝ (Set.range φ) = ⊤)
    (Γ : AddSubgroup H) [DiscreteTopology Γ] [CompactSpace (H ⧸ Γ)] :
    Nonempty (Γ ≃+ (Fin (Module.finrank ℝ E) → ℤ)) := by
  classical
  let L : Submodule ℤ E := (Γ.map φ).toIntSubmodule
  have hLmem : ∀ x : E, x ∈ L ↔ ∃ γ ∈ Γ, φ γ = x := fun x => by
    change x ∈ Γ.map φ ↔ _
    simp [AddSubgroup.mem_map]
  let ψ : Γ →+ L :=
    { toFun := fun γ => ⟨φ γ, (hLmem _).2 ⟨γ, γ.2, rfl⟩⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hψinj : Function.Injective ψ := fun a b hab =>
    Subtype.ext (hφ.injective (congrArg Subtype.val hab))
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨γ, hγ, rfl⟩ := (hLmem x).1 hx
    exact ⟨⟨γ, hγ⟩, rfl⟩
  have hψind : Topology.IsInducing ψ := by
    refine Topology.IsInducing.of_comp (g := Subtype.val) ?_ continuous_subtype_val ?_
    · exact Continuous.subtype_mk (hφ.continuous.comp continuous_subtype_val) _
    · exact hφ.isInducing.comp Topology.IsEmbedding.subtypeVal.isInducing
  let e : Γ ≃ₜ L :=
    (Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).toHomeomorphOfIsInducing hψind
  have : DiscreteTopology L := e.discreteTopology
  have : IsZLattice ℝ L := ⟨by
    have : (L : Set E) = φ '' (Γ : Set H) := by
      ext x
      rw [SetLike.mem_coe, hLmem]
      simp
    rw [this]
    exact span_image_eq_top_of_compactQuotient φ hφ.continuous hspan Γ⟩
  have hrank : Module.finrank ℤ L = Module.finrank ℝ E := ZLattice.rank ℝ L
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℤ L := Module.finBasisOfFinrankEq ℤ L hrank
  exact ⟨(AddEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans b.equivFun.toAddEquiv⟩

/-- The kernel of a non-zero real linear form on a finite-dimensional real vector space has dimension one less. -/
theorem finrank_ker_add_one {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : V →ₗ[ℝ] ℝ) (v : V) (hv : L v ≠ 0) :
    Module.finrank ℝ (LinearMap.ker L) + 1 = Module.finrank ℝ V := by
  have hsurj : Function.Surjective L := fun t =>
    ⟨(t / L v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]⟩
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at h
  omega

/-- Weil's trick for showing that a set `T` spans the kernel of `L`: if `P` is a linear map that is multiplication
by a non-zero scalar `c` on the kernel of `L`, and sends a spanning set `B` of the whole space into the span of `T`,
then every element of the kernel lies in the span of `T`. -/
theorem ker_subset_span_of_projection {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] ℝ) (P : V →ₗ[ℝ] V) (c : ℝ) (hc : c ≠ 0) (hP : ∀ v, L v = 0 → P v = c • v)
    (B T : Set V) (hB : Submodule.span ℝ B = ⊤) (hBT : ∀ b ∈ B, P b ∈ Submodule.span ℝ T)
    (v : V) (hv : L v = 0) : v ∈ Submodule.span ℝ T := by
  have hle : Submodule.span ℝ B ≤ (Submodule.span ℝ T).comap P := Submodule.span_le.2 hBT
  rw [hB] at hle
  have h1 : P v ∈ Submodule.span ℝ T := hle Submodule.mem_top
  rw [hP v hv] at h1
  have := Submodule.smul_mem _ c⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- A family in the kernel of `L` spans the kernel (as a vector space in its own right) as soon as its image in
the ambient space spans every element of the kernel. -/
theorem span_range_eq_top_of_ker {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →ₗ[ℝ] ℝ) (ψ : H → LinearMap.ker L)
    (h : ∀ v, L v = 0 → v ∈ Submodule.span ℝ (Set.range fun x => (ψ x : V))) :
    Submodule.span ℝ (Set.range ψ) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have hv' : v ∈ Submodule.map (LinearMap.ker L).subtype (Submodule.span ℝ (Set.range ψ)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact h v hv
  obtain ⟨w, hw, hwv⟩ := hv'
  have : w = ⟨v, hv⟩ := Subtype.ext hwv
  rwa [this] at hw

/-- The coordinatewise inclusion $\mathbb R^r\times\mathbb Z^m\to\mathbb R^r\times\mathbb R^m$. -/
def castHom (r m : ℕ) : (Fin r → ℝ) × (Fin m → ℤ) →+ (Fin r → ℝ) × (Fin m → ℝ) where
  toFun p := (p.1, fun j => (p.2 j : ℝ))
  map_zero' := Prod.ext (by simp) (funext fun j => by simp)
  map_add' a b := Prod.ext (by simp) (funext fun j => by simp)

/-- The coordinatewise inclusion is a topological embedding. -/
theorem castHom_isEmbedding (r m : ℕ) : Topology.IsEmbedding (castHom r m) :=
  Topology.IsEmbedding.prodMap Topology.IsEmbedding.id
    (Topology.IsClosedEmbedding.piMap (fun _ : Fin m => Int.isClosedEmbedding_coe_real)).isEmbedding

/-- The image of the coordinatewise inclusion spans $\mathbb R^r\times\mathbb R^m$ over $\mathbb R$. -/
theorem span_range_castHom (r m : ℕ) : Submodule.span ℝ (Set.range (castHom r m)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have h1 : ((x, 0) : (Fin r → ℝ) × (Fin m → ℝ)) ∈ Submodule.span ℝ (Set.range (castHom r m)) :=
    Submodule.subset_span ⟨(x, 0), Prod.ext (by simp [castHom]) (funext fun j => by simp [castHom])⟩
  have h2 : ∀ j, ((0, Pi.single j 1) : (Fin r → ℝ) × (Fin m → ℝ)) ∈
      Submodule.span ℝ (Set.range (castHom r m)) := fun j =>
    Submodule.subset_span ⟨(0, Pi.single j 1), Prod.ext (by simp [castHom])
      (funext fun i => by simp [castHom, Pi.single_apply, apply_ite])⟩
  have hy : y = ∑ j, y j • (Pi.single j 1 : Fin m → ℝ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  have h3 : ((0, y) : (Fin r → ℝ) × (Fin m → ℝ)) = ∑ j, y j • ((0, Pi.single j 1) :
      (Fin r → ℝ) × (Fin m → ℝ)) := by
    calc ((0, y) : (Fin r → ℝ) × (Fin m → ℝ))
        = LinearMap.inr ℝ (Fin r → ℝ) (Fin m → ℝ) (∑ j, y j • (Pi.single j 1 : Fin m → ℝ)) := by
          rw [← hy]; rfl
      _ = _ := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => by simp
  have h4 : ((x, y) : (Fin r → ℝ) × (Fin m → ℝ)) = (x, 0) + (0, y) := by simp
  rw [h4, h3]
  exact add_mem h1 (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h2 j))

/-- The real linear form on $\mathbb R^r\times\mathbb R^m$ extending a continuous additive map
$\mathbb R^r\times\mathbb Z^m\to\mathbb R$ (on $\mathbb R^r$ a continuous additive map is real linear; on the
integer part use the values on the basis vectors). -/
def extForm {r m : ℕ} (l0 : (Fin r → ℝ) × (Fin m → ℤ) →+ ℝ) (hc : Continuous l0) :
    (Fin r → ℝ) × (Fin m → ℝ) →ₗ[ℝ] ℝ :=
  ((l0.comp (AddMonoidHom.inl _ _)).toRealLinearMap
    (by exact hc.comp (continuous_id.prodMk continuous_const))).toLinearMap.coprod
    (∑ j, (l0 (0, Pi.single j 1)) • (LinearMap.proj j : (Fin m → ℝ) →ₗ[ℝ] ℝ))

/-- `extForm` extends the given additive map along `castHom`. -/
theorem extForm_castHom {r m : ℕ} (l0 : (Fin r → ℝ) × (Fin m → ℤ) →+ ℝ) (hc : Continuous l0)
    (g : (Fin r → ℝ) × (Fin m → ℤ)) : extForm l0 hc (castHom r m g) = l0 g := by
  obtain ⟨x, n⟩ := g
  have h1 : l0 (0, n) = ∑ j, (n j : ℝ) * l0 (0, Pi.single j 1) := by
    have hn : n = ∑ j, n j • (Pi.single j 1 : Fin m → ℤ) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    calc l0 (0, n)
        = (l0.comp (AddMonoidHom.inr _ _)) (∑ j, n j • (Pi.single j 1 : Fin m → ℤ)) := by
          rw [← hn]; rfl
      _ = _ := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, zsmul_eq_mul]; rfl
  have h2 : l0 (x, n) = l0 (x, 0) + l0 (0, n) := by rw [← map_add]; simp
  simp [extForm, castHom, h2, h1, LinearMap.coprod_apply, LinearMap.sum_apply, mul_comm]

/-- **Lemma 5, case $r>0$, for an abstract group $G$ isomorphic to $\mathbb R^r\times\mathbb Z^m$** ($r+m=s+1$). -/
theorem lemma5_real_aux {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {r m s : ℕ} (hrm : r + m = s + 1) (φ : G ≃ₜ+ (Fin r → ℝ) × (Fin m → ℤ))
    (l : G →+ ℝ) (hl : Continuous l) (hl0 : ∃ x : Fin r → ℝ, l (φ.symm (x, 0)) ≠ 0)
    (Γ : AddSubgroup l.ker) [DiscreteTopology Γ] [CompactSpace (l.ker ⧸ Γ)] :
    Nonempty (Γ ≃+ (Fin s → ℤ)) := by
  classical
  let l0 : (Fin r → ℝ) × (Fin m → ℤ) →+ ℝ :=
    { toFun := fun g => l (φ.symm g)
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hl0c : Continuous l0 := hl.comp φ.symm.continuous
  have hl0l : ∀ g, l0 (φ g) = l g := fun g => by simp [l0]
  let L := extForm l0 hl0c
  have hL : ∀ g, L (castHom r m g) = l0 g := extForm_castHom l0 hl0c
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin r, L (Pi.single i₀ 1, 0) ≠ 0 := by
    obtain ⟨x, hx⟩ := hl0
    by_contra hcon
    push Not at hcon
    apply hx
    have hx' : x = ∑ i, x i • (Pi.single i 1 : Fin r → ℝ) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    have h2 : L (x, 0) = 0 := by
      calc L (x, 0) = L (LinearMap.inl ℝ (Fin r → ℝ) (Fin m → ℝ)
            (∑ i, x i • (Pi.single i 1 : Fin r → ℝ))) := by rw [← hx']; rfl
        _ = 0 := by
          rw [map_sum, map_sum]
          refine Finset.sum_eq_zero fun i _ => ?_
          have e1 : LinearMap.inl ℝ (Fin r → ℝ) (Fin m → ℝ) (x i • (Pi.single i 1 : Fin r → ℝ)) =
              x i • ((Pi.single i 1 : Fin r → ℝ), (0 : Fin m → ℝ)) := by simp
          rw [e1, map_smul, hcon i, smul_zero]
    have hc0 : castHom r m (x, 0) = (x, 0) :=
      Prod.ext rfl (funext fun j => by simp [castHom])
    have h3 : l0 (x, 0) = 0 := by
      rw [← hL, hc0]
      exact h2
    exact h3
  obtain ⟨a, ha⟩ : ∃ a, L (Pi.single i₀ 1, 0) = a := ⟨_, rfl⟩
  rw [ha] at hi₀
  let P : (Fin r → ℝ) × (Fin m → ℝ) →ₗ[ℝ] (Fin r → ℝ) × (Fin m → ℝ) :=
    LinearMap.id - (a⁻¹ • L).smulRight ((Pi.single i₀ 1 : Fin r → ℝ), (0 : Fin m → ℝ))
  have hPapp : ∀ v, P v = v - (a⁻¹ * L v) • ((Pi.single i₀ 1 : Fin r → ℝ), (0 : Fin m → ℝ)) := by
    intro v; simp [P]
  have hLP : ∀ v, L (P v) = 0 := by
    intro v
    rw [hPapp, map_sub, map_smul, smul_eq_mul, ha]
    have : a⁻¹ * L v * a = L v := by field_simp
    linarith
  let ψ : l.ker →+ LinearMap.ker L :=
    { toFun := fun x => ⟨castHom r m (φ x), by
        rw [LinearMap.mem_ker, hL, hl0l]; exact AddMonoidHom.mem_ker.1 x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hemb : Topology.IsEmbedding ψ := by
    refine Topology.IsEmbedding.of_comp (g := Subtype.val)
      (Continuous.subtype_mk ((castHom_isEmbedding r m).continuous.comp
        (φ.continuous.comp continuous_subtype_val)) _) continuous_subtype_val ?_
    exact (castHom_isEmbedding r m).comp (φ.toHomeomorph.isEmbedding.comp
      Topology.IsEmbedding.subtypeVal)
  have hspan : Submodule.span ℝ (Set.range ψ) = ⊤ := by
    refine span_range_eq_top_of_ker L ψ fun v hv => ?_
    refine ker_subset_span_of_projection L P 1 one_ne_zero (fun v hv => by rw [hPapp, hv]; simp)
      (Set.range (castHom r m)) _ (span_range_castHom r m) ?_ v hv
    rintro _ ⟨g0, rfl⟩
    apply Submodule.subset_span
    have hg' : castHom r m (g0.1 - (a⁻¹ * l0 g0) • (Pi.single i₀ 1 : Fin r → ℝ), g0.2) =
        P (castHom r m g0) := by
      rw [hPapp, hL]
      exact Prod.ext (by simp [castHom]) (funext fun j => by simp [castHom])
    have hker : l (φ.symm (g0.1 - (a⁻¹ * l0 g0) • (Pi.single i₀ 1 : Fin r → ℝ), g0.2)) = 0 := by
      have h := hL (g0.1 - (a⁻¹ * l0 g0) • (Pi.single i₀ 1 : Fin r → ℝ), g0.2)
      rw [hg', hLP] at h
      exact h.symm
    refine ⟨⟨φ.symm (g0.1 - (a⁻¹ * l0 g0) • (Pi.single i₀ 1 : Fin r → ℝ), g0.2), hker⟩, ?_⟩
    simp [ψ, hg']
  have hfin : Module.finrank ℝ (LinearMap.ker L) = s := by
    have := finrank_ker_add_one L (Pi.single i₀ 1, 0) (by rw [ha]; exact hi₀)
    simp [Module.finrank_prod] at this
    omega
  have key := nonempty_addEquiv_pi_of_embedding ψ hemb hspan Γ
  rw [hfin] at key
  exact key

/-- **Weil, IV.§4, Lemma 5**, case $r>0$: $G=\mathbb R^r\times\mathbb Z^{s+1-r}$, $\lambda:G\to\mathbb R$ continuous,
additive, non-trivial on $\mathbb R^r$; a discrete subgroup $\Gamma$ of $G_1=\ker\lambda$ with $G_1/\Gamma$ compact is
isomorphic to $\mathbb Z^s$. -/
@[kb "weil1973bnt" "Ch. IV, §4, Lemma 5 (p. 78), case r > 0"]
theorem weil_IV_4_lemma5_real {r s : ℕ} (hrs : r ≤ s) (hr : 0 < r)
    (l : (Fin r → ℝ) × (Fin (s + 1 - r) → ℤ) →+ ℝ) (hl : Continuous l)
    (hl0 : ∃ x : Fin r → ℝ, l (x, 0) ≠ 0)
    (Γ : AddSubgroup l.ker) [DiscreteTopology Γ] [CompactSpace (l.ker ⧸ Γ)] :
    Nonempty (Γ ≃+ (Fin s → ℤ)) :=
  lemma5_real_aux (by omega) (ContinuousAddEquiv.refl _) l hl hl0 Γ

/-- The coordinatewise inclusion $\mathbb Z^n\to\mathbb R^n$. -/
def castHomInt (n : ℕ) : (Fin n → ℤ) →+ (Fin n → ℝ) where
  toFun x j := (x j : ℝ)
  map_zero' := funext fun j => by simp
  map_add' a b := funext fun j => by simp

/-- The coordinatewise inclusion $\mathbb Z^n\to\mathbb R^n$ is a topological embedding. -/
theorem castHomInt_isEmbedding (n : ℕ) : Topology.IsEmbedding (castHomInt n) :=
  (Topology.IsClosedEmbedding.piMap (fun _ : Fin n => Int.isClosedEmbedding_coe_real)).isEmbedding

/-- The image of $\mathbb Z^n$ spans $\mathbb R^n$ over $\mathbb R$. -/
theorem span_range_castHomInt (n : ℕ) : Submodule.span ℝ (Set.range (castHomInt n)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : y = ∑ j, y j • (Pi.single j 1 : Fin n → ℝ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  rw [hy]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨Pi.single j 1, funext fun i => by simp [castHomInt, Pi.single_apply, apply_ite]⟩

/-- An additive map $\mathbb Z^n\to\mathbb Z$ is the dot product with its values on the basis vectors. -/
theorem int_addMonoidHom_apply {n : ℕ} (l : (Fin n → ℤ) →+ ℤ) (g : Fin n → ℤ) :
    l g = ∑ j, g j * l (Pi.single j 1) := by
  have hg : g = ∑ j, g j • (Pi.single j 1 : Fin n → ℤ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hg]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, smul_eq_mul]

/-- The real linear form on $\mathbb R^n$ extending an additive map $\mathbb Z^n\to\mathbb Z$. -/
def extFormInt {n : ℕ} (l : (Fin n → ℤ) →+ ℤ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ j, ((l (Pi.single j 1) : ℤ) : ℝ) • (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)

/-- `extFormInt` extends the given additive map along `castHomInt`. -/
theorem extFormInt_castHomInt {n : ℕ} (l : (Fin n → ℤ) →+ ℤ) (g : Fin n → ℤ) :
    extFormInt l (castHomInt n g) = (l g : ℝ) := by
  rw [int_addMonoidHom_apply l g]
  push_cast
  simp [extFormInt, castHomInt, LinearMap.sum_apply, mul_comm]

/-- **Weil, IV.§4, Lemma 5**, case $r=0$: $G=\mathbb Z^{s+1}$, $\lambda:G\to\mathbb Z$ a non-trivial morphism; a
subgroup $\Gamma$ of $G_1=\ker\lambda$ with $G_1/\Gamma$ compact (here: finite; $G$ is discrete, so $\Gamma$ is
automatically discrete) is isomorphic to $\mathbb Z^s$. -/
@[kb "weil1973bnt" "Ch. IV, §4, Lemma 5 (p. 78), case r = 0"]
theorem weil_IV_4_lemma5_int {s : ℕ} (l : (Fin (s + 1) → ℤ) →+ ℤ) (hl : l ≠ 0)
    (Γ : AddSubgroup l.ker) [CompactSpace (l.ker ⧸ Γ)] :
    Nonempty (Γ ≃+ (Fin s → ℤ)) := by
  classical
  let L := extFormInt l
  have hL : ∀ g, L (castHomInt (s + 1) g) = (l g : ℝ) := extFormInt_castHomInt l
  obtain ⟨j₀, hj₀⟩ : ∃ j, l (Pi.single j 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hl
    refine AddMonoidHom.ext fun g => ?_
    rw [int_addMonoidHom_apply l g]
    simp [hcon]
  obtain ⟨c, hc⟩ : ∃ c : ℤ, l (Pi.single j₀ 1) = c := ⟨_, rfl⟩
  rw [hc] at hj₀
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hj₀
  have hLe : L (Pi.single j₀ 1) = c := by
    have := hL (Pi.single j₀ 1)
    rw [hc] at this
    rw [← this]
    congr 1
    funext j
    simp [castHomInt, Pi.single_apply]
  let P : (Fin (s + 1) → ℝ) →ₗ[ℝ] (Fin (s + 1) → ℝ) :=
    (c : ℝ) • LinearMap.id - L.smulRight (Pi.single j₀ 1 : Fin (s + 1) → ℝ)
  have hPapp : ∀ v, P v = (c : ℝ) • v - L v • (Pi.single j₀ 1 : Fin (s + 1) → ℝ) := by
    intro v; simp [P]
  let ψ : l.ker →+ LinearMap.ker L :=
    { toFun := fun x => ⟨castHomInt (s + 1) x, by
        rw [LinearMap.mem_ker, hL, AddMonoidHom.mem_ker.1 x.2]; simp⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hemb : Topology.IsEmbedding ψ := by
    refine Topology.IsEmbedding.of_comp (g := Subtype.val)
      (Continuous.subtype_mk ((castHomInt_isEmbedding (s + 1)).continuous.comp
        continuous_subtype_val) _) continuous_subtype_val ?_
    exact (castHomInt_isEmbedding (s + 1)).comp Topology.IsEmbedding.subtypeVal
  have hspan : Submodule.span ℝ (Set.range ψ) = ⊤ := by
    refine span_range_eq_top_of_ker L ψ fun v hv => ?_
    refine ker_subset_span_of_projection L P (c : ℝ) hcR (fun v hv => by rw [hPapp, hv]; simp)
      (Set.range (castHomInt (s + 1))) _ (span_range_castHomInt (s + 1)) ?_ v hv
    rintro _ ⟨g, rfl⟩
    apply Submodule.subset_span
    have hker : l (c • g - l g • (Pi.single j₀ 1 : Fin (s + 1) → ℤ)) = 0 := by
      rw [map_sub, map_zsmul, map_zsmul, hc]
      simp [mul_comm]
    refine ⟨⟨c • g - l g • (Pi.single j₀ 1 : Fin (s + 1) → ℤ), hker⟩, ?_⟩
    show castHomInt (s + 1) (c • g - l g • (Pi.single j₀ 1 : Fin (s + 1) → ℤ)) =
      P (castHomInt (s + 1) g)
    rw [hPapp, hL]
    funext j
    simp [castHomInt, Pi.single_apply]
  have hfin : Module.finrank ℝ (LinearMap.ker L) = s := by
    have := finrank_ker_add_one L (Pi.single j₀ 1) (by rw [hLe]; exact hcR)
    simp at this
    omega
  have key := nonempty_addEquiv_pi_of_embedding ψ hemb hspan Γ
  rw [hfin] at key
  exact key

/-- **Weil, IV.§4, Lemma 5** in Weil's form (case $r>0$): $G$ any topological additive group with an isomorphism of
topological groups $\phi:G\cong\mathbb R^r\times\mathbb Z^{s+1-r}$, and $\lambda:G\to\mathbb R$ a morphism non-trivial on
(the copy of) $\mathbb R^r$. -/
@[kb "weil1973bnt" "Ch. IV, §4, Lemma 5 (p. 78), G isomorphic to R^r x Z^(s+1-r)"]
theorem weil_IV_4_lemma5 {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {r s : ℕ} (hrs : r ≤ s) (hr : 0 < r) (φ : G ≃ₜ+ (Fin r → ℝ) × (Fin (s + 1 - r) → ℤ))
    (l : G →+ ℝ) (hl : Continuous l) (hl0 : ∃ x : Fin r → ℝ, l (φ.symm (x, 0)) ≠ 0)
    (Γ : AddSubgroup l.ker) [DiscreteTopology Γ] [CompactSpace (l.ker ⧸ Γ)] :
    Nonempty (Γ ≃+ (Fin s → ℤ)) :=
  lemma5_real_aux (by omega) φ l hl hl0 Γ

end NumberFieldKB.WeilBNT
