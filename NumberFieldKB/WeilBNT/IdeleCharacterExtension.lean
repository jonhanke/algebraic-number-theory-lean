import NumberFieldKB.WeilBNT.IdeleDensity
import NumberFieldKB.MilneCFT.Ch5IdelesChar

/-!
# Weil, *Basic Number Theory*, VII.§8, Proposition 17: extending a morphism of $I(P)$ to the ideles

$k$ is a number field (`K`), $P=P_\infty\cup S$ with $S$ a finite set of finite places, $G_P$ the ideles equal to $1$ on
$P$ (`NumberFieldKB.MilneCFT.idelesTrivialAt S`), and $I(P)$ the fractional ideals prime to $P$
(`NumberFieldKB.MilneCFT.sIdeals S`). For every $v\in P$ let $g_v$ be an open subgroup of $k_v^\times$, contained in
$r_v^\times$ when $v$ is finite (`gInf w`, `gFin v`). As in Weil, "morphism" means continuous homomorphism; $\Gamma$ is a
commutative topological group.

* **Prop. 17** (p. 136): $\varphi\circ\mathrm{id}$ on $G_P$ extends to a morphism $\omega$ of $k_{\mathbb A}^\times$ into
  $\Gamma$, trivial on $k^\times$, if and only if there are morphisms $\psi_v:g_v\to\Gamma$ ($v\in P$) with
  $\varphi(\mathrm{id}(\xi))=\prod_{v\in P}\psi_v(\xi)$ for every $\xi\in\bigcap_{v\in P}(k^\times\cap g_v)$
  (`weil_VII_8_prop17`). When that is so, $\omega$ is unique with the property of inducing $\psi_v^{-1}$ on every
  $g_v$ (`weil_VII_8_prop17_unique`).
* **Corollary** (p. 137), case (a), $\Gamma$ discrete: the extension exists if and only if the $g_v$ can be chosen with
  all $\psi_v=1$ (`weil_VII_8_prop17_cor_discrete`).

*Proof* (Weil's): $g\cdot G_P$, with $g=\prod_{v\in P}g_v$, is an open subgroup of $k_{\mathbb A}^\times$; so is
$k^\times g\cdot G_P$, which by Prop. 15 is then all of $k_{\mathbb A}^\times$. A morphism of $g\cdot G_P$ into $\Gamma$
extends to one of $k^\times g\cdot G_P$ trivial on $k^\times$ if and only if it is trivial on
$k^\times\cap g\cdot G_P$, and then uniquely; the extensions of $\varphi\circ\mathrm{id}$ to $g\cdot G_P$ are the
$\psi^{-1}\cdot(\varphi\circ\mathrm{id})$.
-/

open IsDedekindDomain NumberField Filter Topology NumberFieldKB.MilneCFT nonZeroDivisors

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

/-! ### Extension from a subgroup supplementing a subgroup -/

section Abstract

variable {G Γ : Type*} [CommGroup G] [CommGroup Γ]

/-- If $H\cdot N=G$, a morphism $f$ of $H$ trivial on $H\cap N$ extends uniquely to a morphism of $G$ trivial on $N$. -/
theorem existsUnique_extend_of_sup_eq_top (H N : Subgroup G) (hHN : H ⊔ N = ⊤) (f : H →* Γ)
    (hf : ∀ h : H, (h : G) ∈ N → f h = 1) :
    ∃! ω : G →* Γ, (∀ h : H, ω h = f h) ∧ ∀ n ∈ N, ω n = 1 := by
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp H.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ H ⊔ N := hHN ▸ Subgroup.mem_top x
    obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup.1 hx
    refine ⟨⟨h, hh⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simpa using N.inv_mem hn
  have hker : ((QuotientGroup.mk' N).comp H.subtype).ker ≤ f.ker := by
    intro h hh
    rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      Subgroup.coe_subtype, QuotientGroup.eq_one_iff] at hh
    exact hf h hh
  let e := QuotientGroup.quotientKerEquivOfSurjective _ hsurj
  let ω : G →* Γ := ((QuotientGroup.lift _ f hker).comp e.symm.toMonoidHom).comp (QuotientGroup.mk' N)
  have hωH : ∀ h : H, ω h = f h := by
    intro h
    have : e.symm (QuotientGroup.mk' N (h : G)) = (h : H ⧸ ((QuotientGroup.mk' N).comp H.subtype).ker) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    simp only [ω, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this]
    rfl
  have hωN : ∀ n ∈ N, ω n = 1 := fun n hn => by
    simp only [ω, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff n).2 hn, map_one]
  refine ⟨ω, ⟨hωH, hωN⟩, ?_⟩
  rintro ω' ⟨h1, h2⟩
  refine MonoidHom.ext fun x => ?_
  have hx : x ∈ H ⊔ N := hHN ▸ Subgroup.mem_top x
  obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup.1 hx
  rw [map_mul, map_mul, h2 n hn, hωN n hn]
  exact congrArg (· * 1) ((h1 ⟨h, hh⟩).trans (hωH ⟨h, hh⟩).symm)

end Abstract

/-- A homomorphism with open kernel from a topological group to any topological space with a group structure is
continuous (its fibres are cosets of the kernel). -/
theorem continuous_of_isOpen_ker' {A B : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group B]
    [TopologicalSpace B] (f : A →* B) (h : IsOpen (f.ker : Set A)) : Continuous f := by
  refine continuous_def.2 fun U _ => ?_
  have : f ⁻¹' U = ⋃ x ∈ f ⁻¹' U, (fun y => x⁻¹ * y) ⁻¹' (f.ker : Set A) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv,
      exists_prop]
    refine ⟨fun hy => ⟨y, hy, by rw [inv_mul_cancel]⟩, fun ⟨x, hx, hxy⟩ => ?_⟩
    have : f y = f x := (inv_mul_eq_one.1 hxy).symm
    rwa [this]
  rw [this]
  exact isOpen_biUnion fun x _ => h.preimage (continuous_const.mul continuous_id)

theorem ideleFinAt_ofAdicCompletion_self (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    ideleFinAt (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) v = u := by
  classical
  exact Pi.mulSingle_eq_same (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v
    (u : v.adicCompletion K)

theorem ideleFinAt_ofAdicCompletion_ne (v v' : HeightOneSpectrum (𝓞 K)) (h : v' ≠ v) (u : (v.adicCompletion K)ˣ) :
    ideleFinAt (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) v' = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) h
    (u : v.adicCompletion K)

theorem ideleInfAt_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (w : InfinitePlace K) : ideleInfAt (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) w = 1 := rfl

/-! ### The groups $g=\prod_{v\in P}g_v$ and the product of the $\psi_v$ -/

section Prop17

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- $g=\prod_{v\in P}g_v$, as a subgroup of $k_P^\times=\prod_{v\in P}k_v^\times$ (`placeUnits S`). -/
def gProd (gInf : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
    (gFin : ∀ v : S, Subgroup ((v.1).adicCompletion K)ˣ) : Subgroup (placeUnits S) where
  carrier := {c | (∀ w, c.1 w ∈ gInf w) ∧ ∀ v, c.2 v ∈ gFin v}
  one_mem' := ⟨fun w => (gInf w).one_mem, fun v => (gFin v).one_mem⟩
  mul_mem' := fun ha hb => ⟨fun w => (gInf w).mul_mem (ha.1 w) (hb.1 w), fun v => (gFin v).mul_mem (ha.2 v) (hb.2 v)⟩
  inv_mem' := fun ha => ⟨fun w => (gInf w).inv_mem (ha.1 w), fun v => (gFin v).inv_mem (ha.2 v)⟩

variable {S} {gInf : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ}
  {gFin : ∀ v : S, Subgroup ((v.1).adicCompletion K)ˣ}

/-- The component at an infinite place of an element of $g$. -/
def gProdInf (w : InfinitePlace K) : gProd S gInf gFin →* gInf w where
  toFun c := ⟨c.1.1 w, c.2.1 w⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The component at a place of `S` of an element of $g$. -/
def gProdFin (v : S) : gProd S gInf gFin →* gFin v where
  toFun c := ⟨c.1.2 v, c.2.2 v⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {Γ : Type*} [CommGroup Γ]

/-- $\psi=\prod_{v\in P}\psi_v$ on $g=\prod_{v\in P}g_v$. -/
def psiProd (ψInf : ∀ w, gInf w →* Γ) (ψFin : ∀ v, gFin v →* Γ) : gProd S gInf gFin →* Γ :=
  (∏ w, (ψInf w).comp (gProdInf w)) * ∏ v, (ψFin v).comp (gProdFin v)

theorem psiProd_apply (ψInf : ∀ w, gInf w →* Γ) (ψFin : ∀ v, gFin v →* Γ) (c : gProd S gInf gFin) :
    psiProd ψInf ψFin c = (∏ w, ψInf w (gProdInf w c)) * ∏ v, ψFin v (gProdFin v c) := by
  simp [psiProd]

theorem isOpen_gProd (hInf : ∀ w, IsOpen (gInf w : Set (w.Completion)ˣ))
    (hFin : ∀ v, IsOpen (gFin v : Set ((v.1).adicCompletion K)ˣ)) :
    IsOpen (gProd S gInf gFin : Set (placeUnits S)) := by
  have : (gProd S gInf gFin : Set (placeUnits S)) =
      (Set.univ.pi fun w => (gInf w : Set (w.Completion)ˣ)) ×ˢ
        (Set.univ.pi fun v => (gFin v : Set ((v.1).adicCompletion K)ˣ)) := by
    ext c; simp [gProd]
  rw [this]
  exact (isOpen_set_pi Set.finite_univ fun w _ => hInf w).prod (isOpen_set_pi Set.finite_univ fun v _ => hFin v)

variable (S gInf gFin) in
/-- Weil's $g\cdot G_P$: the ideles whose components at the places of $P$ lie in the $g_v$. -/
def gGP : Subgroup (IdeleGroup (𝓞 K) K) := (gProd S gInf gFin).comap (pproj S)

theorem isOpen_gGP (hInf : ∀ w, IsOpen (gInf w : Set (w.Completion)ˣ))
    (hFin : ∀ v, IsOpen (gFin v : Set ((v.1).adicCompletion K)ˣ)) :
    IsOpen (gGP S gInf gFin : Set (IdeleGroup (𝓞 K) K)) :=
  (isOpen_gProd hInf hFin).preimage (continuous_pproj S)

theorem pproj_eq_one_of_mem {x : IdeleGroup (𝓞 K) K} (hx : x ∈ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K)))) :
    pproj S x = 1 :=
  Prod.ext (funext fun w => Units.ext (hx.1 w)) (funext fun v => Units.ext (hx.2 v.1 v.2))

theorem idelesTrivialAt_le_gGP : idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))) ≤ gGP S gInf gFin := by
  intro x hx
  show pproj S x ∈ gProd S gInf gFin
  rw [pproj_eq_one_of_mem hx]
  exact (gProd S gInf gFin).one_mem

theorem idelesOneAt_le_idelesTrivialAt :
    idelesOneAt (K := K) (S : Set (HeightOneSpectrum (𝓞 K))) ≤ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))) :=
  fun _ hx => ⟨fun w => congrFun hx.1 w, hx.2⟩

/-- Weil: $k^\times g\cdot G_P$ is an open subgroup containing the dense set $k^\times G_P$ (Prop. 15), hence everything. -/
theorem gGP_sup_range_eq_top (hInf : ∀ w, IsOpen (gInf w : Set (w.Completion)ˣ))
    (hFin : ∀ v, IsOpen (gFin v : Set ((v.1).adicCompletion K)ˣ)) :
    gGP S gInf gFin ⊔ (IdeleGroup.unitEmbedding (𝓞 K) K).range = ⊤ := by
  set L := gGP S gInf gFin ⊔ (IdeleGroup.unitEmbedding (𝓞 K) K).range
  have hLo : IsOpen (L : Set (IdeleGroup (𝓞 K) K)) := Subgroup.isOpen_mono le_sup_left (isOpen_gGP hInf hFin)
  have hLc : IsClosed (L : Set (IdeleGroup (𝓞 K) K)) := Subgroup.isClosed_of_isOpen _ hLo
  have hsub : {x : IdeleGroup (𝓞 K) K | ∃ ξ : Kˣ, ∃ g ∈ idelesOneAt (S : Set (HeightOneSpectrum (𝓞 K))),
      x = IdeleGroup.unitEmbedding (𝓞 K) K ξ * g} ⊆ L := by
    rintro x ⟨ξ, g, hg, rfl⟩
    exact L.mul_mem (Subgroup.mem_sup_right ⟨ξ, rfl⟩)
      (Subgroup.mem_sup_left (idelesTrivialAt_le_gGP (idelesOneAt_le_idelesTrivialAt hg)))
  have := (weil_VII_8_prop15 S).closure_eq ▸ closure_minimal hsub hLc
  exact eq_top_iff.2 fun x _ => this (Set.mem_univ x)

theorem pfin_val (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup (𝓞 K) K) :
    ((pfin v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = ideleFinAt x v := rfl

theorem pinf_val (w : InfinitePlace K) (x : IdeleGroup (𝓞 K) K) :
    ((pinf w x : (w.Completion)ˣ) : w.Completion) = ideleInfAt x w := rfl

theorem valued_ideleFinAt_of_mem (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
    {x : IdeleGroup (𝓞 K) K} (hx : x ∈ gGP S gInf gFin) (v : S) : Valued.v (ideleFinAt x v.1) = 1 := by
  have h := hFinU v _ (hx.2 v)
  rw [← pfin_val]
  exact h

variable (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
include hFinU

/-- $z\mapsto\mathrm{id}(z)$ maps $g\cdot G_P$ into $I(P)$. -/
def idGP : gGP S gInf gFin →* sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) :=
  MonoidHom.codRestrict ((ideleToIdeal K).comp (gGP S gInf gFin).subtype) _ fun x =>
    (ideleToIdeal_mem_sIdeals_iff _ _).2 fun v hv => valued_ideleFinAt_of_mem hFinU x.2 ⟨v, hv⟩

omit hFinU in
/-- The projection of $g\cdot G_P$ onto $g$. -/
def pprojG : gGP S gInf gFin →* gProd S gInf gFin :=
  MonoidHom.codRestrict ((pproj S).comp (gGP S gInf gFin).subtype) _ fun x => x.2

omit hFinU in
theorem continuous_pprojG : Continuous (pprojG (S := S) (gInf := gInf) (gFin := gFin)) :=
  ((continuous_pproj S).comp continuous_subtype_val).subtype_mk _

omit hFinU in
theorem continuous_psiProd (ψInf : ∀ w, gInf w →* Γ) (ψFin : ∀ v, gFin v →* Γ) [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (hψInf : ∀ w, Continuous (ψInf w)) (hψFin : ∀ v, Continuous (ψFin v)) :
    Continuous (psiProd ψInf ψFin) := by
  have : (psiProd ψInf ψFin : gProd S gInf gFin → Γ) =
      fun c => (∏ w, ψInf w (gProdInf w c)) * ∏ v, ψFin v (gProdFin v c) := funext (psiProd_apply ψInf ψFin)
  rw [this]
  refine (continuous_finsetProd _ fun w _ => (hψInf w).comp ?_).mul
    (continuous_finsetProd _ fun v _ => (hψFin v).comp ?_)
  · exact ((continuous_apply w).comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _
  · exact ((continuous_apply v).comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _

omit hFinU

theorem idGP_val (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1) (x : gGP S gInf gFin) :
    ((idGP hFinU x : sIdeals (S : Set (HeightOneSpectrum (𝓞 K)))) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      ideleToIdeal K x := rfl

theorem ideleToIdeal_ofCompletion (w : InfinitePlace K) (u : (w.Completion)ˣ) :
    ideleToIdeal K (IdeleGroup.ofCompletion (𝓞 K) K w u) = 1 :=
  (item_4_1.2 _).2 fun v => by rw [ideleFinAt_ofCompletion, map_one]

theorem ideleToIdeal_ofAdicCompletion_of_valued (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    ideleToIdeal K (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = 1 := by
  rw [ideleToIdeal_ofAdicCompletion, hu, WithZero.log_one, neg_zero, zpow_zero]

/-- `psect` is the product of the local embeddings. -/
theorem psect_eq (c : placeUnits S) : psect S c = (∏ w : InfinitePlace K, IdeleGroup.ofCompletion (𝓞 K) K w (c.1 w)) *
    ∏ v : S, IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 (c.2 v) := rfl

theorem ideleToIdeal_psect (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
    (c : gProd S gInf gFin) : ideleToIdeal K (psect S c) = 1 := by
  rw [psect_eq, map_mul, map_prod, map_prod]
  simp only [ideleToIdeal_ofCompletion, Finset.prod_const_one, one_mul]
  exact Finset.prod_eq_one fun v _ => ideleToIdeal_ofAdicCompletion_of_valued _ _ (hFinU v _ (c.2.2 v))

theorem psect_inv_mul_mem (x : IdeleGroup (𝓞 K) K) :
    (psect S (pproj S x))⁻¹ * x ∈ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))) :=
  idelesOneAt_le_idelesTrivialAt (mem_idelesOneAt_of_pproj_eq_one S (by
    rw [map_mul, map_inv, pproj_psect, inv_mul_cancel]))

/-- Weil's decomposition $z=c\cdot z'$ with $c\in g$, $z'\in G_P$: a morphism agreeing with $\varphi\circ\mathrm{id}$ on
$G_P$ takes on $z\in g\cdot G_P$ the value $\omega(c)\,\varphi(\mathrm{id}(z))$. -/
theorem map_of_mem_gGP (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
    (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* Γ) (ω : IdeleGroup (𝓞 K) K →* Γ)
    (hG : ∀ x ∈ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))),
      ∀ b : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))), (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
        ω x = φ b) (h : gGP S gInf gFin) :
    ω h = ω (psect S (pproj S h)) * φ (idGP hFinU h) := by
  have hx := psect_inv_mul_mem (S := S) (h : IdeleGroup (𝓞 K) K)
  have e : ω ((psect S (pproj S h))⁻¹ * h) = φ (idGP hFinU h) := by
    refine hG _ hx _ ?_
    have h1 : ideleToIdeal K (psect S (pproj S h)) = 1 := ideleToIdeal_psect hFinU (pprojG h)
    rw [idGP_val, map_mul, map_inv, h1, inv_one, one_mul]
  rw [← e, ← map_mul, mul_inv_cancel_left]

theorem map_psect (ω : IdeleGroup (𝓞 K) K →* Γ) (c : placeUnits S) :
    ω (psect S c) = (∏ w, ω (IdeleGroup.ofCompletion (𝓞 K) K w (c.1 w))) *
      ∏ v : S, ω (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 (c.2 v)) := by
  rw [psect_eq, map_mul, map_prod, map_prod]

variable (S gInf gFin) in
/-- **The condition of Prop. 17**: $\varphi(\mathrm{id}(\xi))=\prod_{v\in P}\psi_v(\xi)$ for every
$\xi\in\bigcap_{v\in P}(k^\times\cap g_v)$. -/
def Prop17Condition (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* Γ) (ψInf : ∀ w, gInf w →* Γ)
    (ψFin : ∀ v, gFin v →* Γ) : Prop :=
  ∀ (ξ : Kˣ) (hξ : pproj S (IdeleGroup.unitEmbedding (𝓞 K) K ξ) ∈ gProd S gInf gFin)
    (b : sIdeals (S : Set (HeightOneSpectrum (𝓞 K)))),
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = toPrincipalIdeal (𝓞 K) K ξ → φ b = psiProd ψInf ψFin ⟨_, hξ⟩

/-- The morphism of $g\cdot G_P$ into $\Gamma$ given by $\psi^{-1}\cdot(\varphi\circ\mathrm{id})$. -/
def fGP (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
    (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* Γ) (ψInf : ∀ w, gInf w →* Γ)
    (ψFin : ∀ v, gFin v →* Γ) : gGP S gInf gFin →* Γ :=
  ((psiProd ψInf ψFin).comp pprojG)⁻¹ * φ.comp (idGP hFinU)

theorem fGP_apply (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
    (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* Γ) (ψInf : ∀ w, gInf w →* Γ)
    (ψFin : ∀ v, gFin v →* Γ) (h : gGP S gInf gFin) :
    fGP hFinU φ ψInf ψFin h = (psiProd ψInf ψFin (pprojG h))⁻¹ * φ (idGP hFinU h) := rfl

theorem pprojG_eq_one_of_mem {x : gGP S gInf gFin}
    (hx : (x : IdeleGroup (𝓞 K) K) ∈ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K)))) : pprojG x = 1 :=
  Subtype.ext (pproj_eq_one_of_mem hx)

theorem isOpen_ker_idGP (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1) :
    IsOpen ((idGP (gInf := gInf) hFinU).ker : Set (gGP S gInf gFin)) := by
  have : ((idGP (gInf := gInf) hFinU).ker : Set (gGP S gInf gFin)) =
      Subtype.val ⁻¹' ((ideleToIdeal K).ker : Set (IdeleGroup (𝓞 K) K)) := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage]
    constructor
    · intro h
      have := congrArg (fun b : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) =>
        (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) h
      rw [idGP_val] at this
      exact this
    · intro h
      exact Subtype.ext (by rw [idGP_val]; exact h)
  rw [this]
  exact (isOpen_ker_ideleToIdeal K).preimage continuous_subtype_val

variable [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem continuous_fGP (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
    (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* Γ) (ψInf : ∀ w, gInf w →* Γ)
    (ψFin : ∀ v, gFin v →* Γ) (hψInf : ∀ w, Continuous (ψInf w)) (hψFin : ∀ v, Continuous (ψFin v)) :
    Continuous (fGP hFinU φ ψInf ψFin) := by
  have h1 : Continuous (φ.comp (idGP (gInf := gInf) hFinU)) := by
    refine continuous_of_isOpen_ker' _ (Subgroup.isOpen_mono (fun x hx => ?_) (isOpen_ker_idGP hFinU))
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [MonoidHom.comp_apply, hx, map_one]
  have h2 : Continuous ((psiProd ψInf ψFin).comp (pprojG (S := S) (gInf := gInf) (gFin := gFin))) :=
    (continuous_psiProd ψInf ψFin hψInf hψFin).comp continuous_pprojG
  exact h2.inv.mul h1

/-- A homomorphism of a topological group whose restriction to an open subgroup is continuous is continuous. -/
theorem continuous_of_continuous_restrict {A B : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (H : Subgroup A) (hH : IsOpen (H : Set A)) (ω : A →* B)
    (h : Continuous (ω.comp H.subtype)) : Continuous ω := by
  refine continuous_of_continuousAt_one ω ?_
  have hon : ContinuousOn ω H := continuousOn_iff_continuous_domRestrict.2 h
  exact hon.continuousAt (hH.mem_nhds H.one_mem)

/-- The extension constructed in Weil's proof: $\omega=\psi^{-1}\cdot(\varphi\circ\mathrm{id})$ on $g\cdot G_P$ and
$\omega=1$ on $k^\times$. -/
theorem exists_extension (hInf : ∀ w, IsOpen (gInf w : Set (w.Completion)ˣ))
    (hFin : ∀ v, IsOpen (gFin v : Set ((v.1).adicCompletion K)ˣ))
    (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
    (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* Γ) (ψInf : ∀ w, gInf w →* Γ)
    (ψFin : ∀ v, gFin v →* Γ) (hψInf : ∀ w, Continuous (ψInf w)) (hψFin : ∀ v, Continuous (ψFin v))
    (hc : Prop17Condition S gInf gFin φ ψInf ψFin) :
    ∃ ω : IdeleGroup (𝓞 K) K →* Γ, Continuous ω ∧ (∀ h : gGP S gInf gFin, ω h = fGP hFinU φ ψInf ψFin h) ∧
      ∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1 := by
  have hf : ∀ h : gGP S gInf gFin, (h : IdeleGroup (𝓞 K) K) ∈ (IdeleGroup.unitEmbedding (𝓞 K) K).range →
      fGP hFinU φ ψInf ψFin h = 1 := by
    rintro ⟨x, hx⟩ ⟨ξ, rfl⟩
    rw [fGP_apply, inv_mul_eq_one]
    refine (hc ξ hx _ ?_).symm
    rw [idGP_val]
    exact ideleToIdeal_unitEmbedding ξ
  obtain ⟨ω, ⟨hωH, hωN⟩, -⟩ :=
    existsUnique_extend_of_sup_eq_top _ _ (gGP_sup_range_eq_top hInf hFin) _ hf
  refine ⟨ω, ?_, hωH, fun ξ => hωN _ ⟨ξ, rfl⟩⟩
  refine continuous_of_continuous_restrict _ (isOpen_gGP hInf hFin) ω ?_
  have : ω.comp (gGP S gInf gFin).subtype = fGP hFinU φ ψInf ψFin := MonoidHom.ext hωH
  rw [this]
  exact continuous_fGP hFinU φ ψInf ψFin hψInf hψFin

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
/-- Two morphisms equal to `fGP` on $g\cdot G_P$ and trivial on $k^\times$ are equal. -/
theorem eq_of_eq_fGP (hInf : ∀ w, IsOpen (gInf w : Set (w.Completion)ˣ))
    (hFin : ∀ v, IsOpen (gFin v : Set ((v.1).adicCompletion K)ˣ)) (f : gGP S gInf gFin →* Γ)
    (ω ω' : IdeleGroup (𝓞 K) K →* Γ) (h1 : ∀ h : gGP S gInf gFin, ω h = f h)
    (h1' : ∀ h : gGP S gInf gFin, ω' h = f h) (h2 : ∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1)
    (h2' : ∀ ξ : Kˣ, ω' (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1) : ω = ω' := by
  refine MonoidHom.ext fun x => ?_
  have hx : x ∈ gGP S gInf gFin ⊔ (IdeleGroup.unitEmbedding (𝓞 K) K).range :=
    gGP_sup_range_eq_top hInf hFin ▸ Subgroup.mem_top x
  obtain ⟨h, hh, n, ⟨ξ, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
  rw [map_mul, map_mul, h2, h2', h1 ⟨h, hh⟩, h1' ⟨h, hh⟩]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
/-- The extension agrees with $\varphi\circ\mathrm{id}$ on $G_P$. -/
theorem fGP_of_mem_idelesTrivialAt (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
    (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* Γ) (ψInf : ∀ w, gInf w →* Γ)
    (ψFin : ∀ v, gFin v →* Γ) (x : IdeleGroup (𝓞 K) K)
    (hx : x ∈ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K)))) (b : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))))
    (hb : (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x) :
    fGP hFinU φ ψInf ψFin ⟨x, idelesTrivialAt_le_gGP hx⟩ = φ b := by
  rw [fGP_apply, pprojG_eq_one_of_mem hx, map_one, inv_one, one_mul]
  congr 1
  exact Subtype.ext (by rw [idGP_val]; exact hb.symm)

/-- **Weil, VII.§8, Proposition 17** (p. 136), number field case. Let $\varphi:I(P)\to\Gamma$ be a morphism into a
commutative topological group, and $g_v$ ($v\in P$) open subgroups of $k_v^\times$, contained in $r_v^\times$ for $v$
finite. Then $\varphi\circ\mathrm{id}$ on $G_P$ extends to a (continuous) morphism $\omega$ of $k_{\mathbb A}^\times$
into $\Gamma$, trivial on $k^\times$, if and only if there are morphisms $\psi_v:g_v\to\Gamma$ with
$\varphi(\mathrm{id}(\xi))=\prod_{v\in P}\psi_v(\xi)$ for all $\xi\in\bigcap_{v\in P}(k^\times\cap g_v)$. -/
@[kb "weil1973bnt" "Ch. VII, §8, Prop. 17 (p. 136), number field case"]
theorem weil_VII_8_prop17 (hInf : ∀ w, IsOpen (gInf w : Set (w.Completion)ˣ))
    (hFin : ∀ v, IsOpen (gFin v : Set ((v.1).adicCompletion K)ˣ))
    (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
    (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* Γ) :
    (∃ ω : IdeleGroup (𝓞 K) K →* Γ, Continuous ω ∧ (∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1) ∧
      ∀ x ∈ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))),
        ∀ b : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))), (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
          ω x = φ b) ↔
    ∃ (ψInf : ∀ w, gInf w →* Γ) (ψFin : ∀ v, gFin v →* Γ), (∀ w, Continuous (ψInf w)) ∧
      (∀ v, Continuous (ψFin v)) ∧ Prop17Condition S gInf gFin φ ψInf ψFin := by
  constructor
  · rintro ⟨ω, hω, hk, hG⟩
    refine ⟨fun w => ((ω.comp (IdeleGroup.ofCompletion (𝓞 K) K w)).comp (gInf w).subtype)⁻¹,
      fun v => ((ω.comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1)).comp (gFin v).subtype)⁻¹,
      fun w => ?_, fun v => ?_, ?_⟩
    · exact (hω.comp ((item_4_3.2 w).continuous.comp continuous_subtype_val)).inv
    · exact (hω.comp ((item_4_3.1 v.1).continuous.comp continuous_subtype_val)).inv
    · intro ξ hξ b hb
      have e := map_of_mem_gGP hFinU φ ω hG ⟨_, hξ⟩
      have hb' : idGP hFinU ⟨_, hξ⟩ = b :=
        Subtype.ext (by rw [idGP_val, hb]; exact ideleToIdeal_unitEmbedding ξ)
      rw [hb', hk, map_psect] at e
      rw [psiProd_apply]
      simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, Finset.prod_inv_distrib]
      rw [← mul_inv, eq_inv_iff_mul_eq_one, mul_comm]
      exact e.symm
  · rintro ⟨ψInf, ψFin, hψInf, hψFin, hc⟩
    obtain ⟨ω, hω, hωH, hk⟩ := exists_extension hInf hFin hFinU φ ψInf ψFin hψInf hψFin hc
    refine ⟨ω, hω, hk, fun x hx b hb => ?_⟩
    rw [show x = ((⟨x, idelesTrivialAt_le_gGP hx⟩ : gGP S gInf gFin) : IdeleGroup (𝓞 K) K) from rfl, hωH]
    exact fGP_of_mem_idelesTrivialAt hFinU φ ψInf ψFin x hx b hb

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem pproj_ofCompletion_fst_self (w : InfinitePlace K) (t : (w.Completion)ˣ) :
    (pproj S (IdeleGroup.ofCompletion (𝓞 K) K w t)).1 w = t :=
  Units.ext (ideleInfAt_ofCompletion_self w t)

theorem pproj_ofCompletion_fst_ne (w w' : InfinitePlace K) (h : w' ≠ w) (t : (w.Completion)ˣ) :
    (pproj S (IdeleGroup.ofCompletion (𝓞 K) K w t)).1 w' = 1 :=
  Units.ext (ideleInfAt_ofCompletion_ne w w' h t)

theorem pproj_ofCompletion_snd (w : InfinitePlace K) (t : (w.Completion)ˣ) (v : S) :
    (pproj S (IdeleGroup.ofCompletion (𝓞 K) K w t)).2 v = 1 :=
  Units.ext (ideleFinAt_ofCompletion w t v.1)

theorem pproj_ofAdic_fst (v : S) (t : ((v.1).adicCompletion K)ˣ) (w : InfinitePlace K) :
    (pproj S (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 t)).1 w = 1 :=
  Units.ext (ideleInfAt_ofAdicCompletion v.1 t w)

theorem pproj_ofAdic_snd_self (v : S) (t : ((v.1).adicCompletion K)ˣ) :
    (pproj S (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 t)).2 v = t :=
  Units.ext (ideleFinAt_ofAdicCompletion_self v.1 t)

theorem pproj_ofAdic_snd_ne (v v' : S) (h : v' ≠ v) (t : ((v.1).adicCompletion K)ˣ) :
    (pproj S (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 t)).2 v' = 1 :=
  Units.ext (ideleFinAt_ofAdicCompletion_ne v.1 v'.1 (fun e => h (Subtype.ext e)) t)

theorem ofCompletion_mem_gGP (w : InfinitePlace K) (t : gInf w) :
    IdeleGroup.ofCompletion (𝓞 K) K w t ∈ gGP S gInf gFin := by
  refine ⟨fun w' => ?_, fun v => ?_⟩
  · rcases eq_or_ne w' w with rfl | h
    · rw [pproj_ofCompletion_fst_self]; exact t.2
    · rw [pproj_ofCompletion_fst_ne w w' h]; exact (gInf w').one_mem
  · rw [pproj_ofCompletion_snd]; exact (gFin v).one_mem

theorem ofAdic_mem_gGP (v : S) (t : gFin v) :
    IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 t ∈ gGP S gInf gFin := by
  refine ⟨fun w => ?_, fun v' => ?_⟩
  · rw [pproj_ofAdic_fst]; exact (gInf w).one_mem
  · rcases eq_or_ne v' v with rfl | h
    · rw [pproj_ofAdic_snd_self]; exact t.2
    · rw [pproj_ofAdic_snd_ne v v' h]; exact (gFin v').one_mem

theorem psiProd_ofCompletion (ψInf : ∀ w, gInf w →* Γ) (ψFin : ∀ v, gFin v →* Γ) (w : InfinitePlace K)
    (t : gInf w) : psiProd ψInf ψFin (pprojG ⟨_, ofCompletion_mem_gGP (gFin := gFin) w t⟩) = ψInf w t := by
  rw [psiProd_apply]
  have h2 : ∀ v, gProdFin v (pprojG ⟨_, ofCompletion_mem_gGP (gFin := gFin) w t⟩) = 1 := fun v =>
    Subtype.ext (pproj_ofCompletion_snd w t v)
  simp only [h2, map_one, Finset.prod_const_one, mul_one]
  rw [Finset.prod_eq_single w]
  · exact congrArg (ψInf w) (Subtype.ext (pproj_ofCompletion_fst_self (S := S) w t))
  · intro w' _ h
    rw [show gProdInf w' (pprojG ⟨_, ofCompletion_mem_gGP (gFin := gFin) w t⟩) = 1 from
      Subtype.ext (pproj_ofCompletion_fst_ne (S := S) w w' h t), map_one]
  · intro h; exact absurd (Finset.mem_univ w) h

theorem psiProd_ofAdic (ψInf : ∀ w, gInf w →* Γ) (ψFin : ∀ v, gFin v →* Γ) (v : S)
    (t : gFin v) : psiProd ψInf ψFin (pprojG ⟨_, ofAdic_mem_gGP (gInf := gInf) v t⟩) = ψFin v t := by
  rw [psiProd_apply]
  have h1 : ∀ w, gProdInf w (pprojG ⟨_, ofAdic_mem_gGP (gInf := gInf) v t⟩) = 1 := fun w =>
    Subtype.ext (pproj_ofAdic_fst v t w)
  simp only [h1, map_one, Finset.prod_const_one, one_mul]
  rw [Finset.prod_eq_single v]
  · exact congrArg (ψFin v) (Subtype.ext (pproj_ofAdic_snd_self v t))
  · intro v' _ h
    rw [show gProdFin v' (pprojG ⟨_, ofAdic_mem_gGP (gInf := gInf) v t⟩) = 1 from
      Subtype.ext (pproj_ofAdic_snd_ne v v' h t), map_one]
  · intro h; exact absurd (Finset.mem_univ v) h

variable [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **Weil, VII.§8, Proposition 17, last assertion** (p. 136), number field case: when the condition holds, there is
exactly one morphism $\omega$ of $k_{\mathbb A}^\times$ into $\Gamma$, trivial on $k^\times$, equal to
$\varphi\circ\mathrm{id}$ on $G_P$, and inducing $\psi_v^{-1}$ on $g_v$ for every $v\in P$. -/
@[kb "weil1973bnt" "Ch. VII, §8, Prop. 17, last assertion (p. 136), number field case"]
theorem weil_VII_8_prop17_unique (hInf : ∀ w, IsOpen (gInf w : Set (w.Completion)ˣ))
    (hFin : ∀ v, IsOpen (gFin v : Set ((v.1).adicCompletion K)ˣ))
    (hFinU : ∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1)
    (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* Γ) (ψInf : ∀ w, gInf w →* Γ)
    (ψFin : ∀ v, gFin v →* Γ) (hψInf : ∀ w, Continuous (ψInf w)) (hψFin : ∀ v, Continuous (ψFin v))
    (hc : Prop17Condition S gInf gFin φ ψInf ψFin) :
    ∃! ω : IdeleGroup (𝓞 K) K →* Γ, Continuous ω ∧ (∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1) ∧
      (∀ x ∈ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))),
        ∀ b : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))), (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
          ω x = φ b) ∧
      (∀ w (t : gInf w), ω (IdeleGroup.ofCompletion (𝓞 K) K w t) = (ψInf w t)⁻¹) ∧
      ∀ v (t : gFin v), ω (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 t) = (ψFin v t)⁻¹ := by
  obtain ⟨ω, hω, hωH, hk⟩ := exists_extension hInf hFin hFinU φ ψInf ψFin hψInf hψFin hc
  refine ⟨ω, ⟨hω, hk, fun x hx b hb => ?_, fun w t => ?_, fun v t => ?_⟩, ?_⟩
  · rw [show x = ((⟨x, idelesTrivialAt_le_gGP hx⟩ : gGP S gInf gFin) : IdeleGroup (𝓞 K) K) from rfl, hωH]
    exact fGP_of_mem_idelesTrivialAt hFinU φ ψInf ψFin x hx b hb
  · rw [show IdeleGroup.ofCompletion (𝓞 K) K w t = ((⟨_, ofCompletion_mem_gGP (gFin := gFin) w t⟩ :
      gGP S gInf gFin) : IdeleGroup (𝓞 K) K) from rfl, hωH, fGP_apply, psiProd_ofCompletion]
    have : idGP hFinU ⟨_, ofCompletion_mem_gGP (gFin := gFin) w t⟩ = 1 :=
      Subtype.ext (by rw [idGP_val]; exact ideleToIdeal_ofCompletion w t)
    rw [this, map_one, mul_one]
  · rw [show IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 t = ((⟨_, ofAdic_mem_gGP (gInf := gInf) v t⟩ :
      gGP S gInf gFin) : IdeleGroup (𝓞 K) K) from rfl, hωH, fGP_apply, psiProd_ofAdic]
    have : idGP hFinU ⟨_, ofAdic_mem_gGP (gInf := gInf) v t⟩ = 1 :=
      Subtype.ext (by rw [idGP_val]; exact ideleToIdeal_ofAdicCompletion_of_valued _ _ (hFinU v _ t.2))
    rw [this, map_one, mul_one]
  · rintro ω' ⟨-, hk', hG', hInf', hFin'⟩
    refine (eq_of_eq_fGP hInf hFin (fGP hFinU φ ψInf ψFin) ω ω' hωH (fun h => ?_) hk hk').symm
    rw [map_of_mem_gGP hFinU φ ω' hG' h, map_psect, fGP_apply, psiProd_apply]
    have e1 : ∀ w, ω' (IdeleGroup.ofCompletion (𝓞 K) K w ((pproj S h).1 w)) =
        (ψInf w (gProdInf w (pprojG h)))⁻¹ := fun w => hInf' w ⟨_, h.2.1 w⟩
    have e2 : ∀ v : S, ω' (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1 ((pproj S h).2 v)) =
        (ψFin v (gProdFin v (pprojG h)))⁻¹ := fun v => hFin' v ⟨_, h.2.2 v⟩
    simp only [e1, e2, Finset.prod_inv_distrib, mul_inv]

end Prop17

/-! ### The Corollary, case (a): $\Gamma$ discrete -/

/-- The units of $r_v$: the elements of $k_v^\times$ of valuation $1$. -/
def unitsInt (v : HeightOneSpectrum (𝓞 K)) : Subgroup (v.adicCompletion K)ˣ where
  carrier := {u | Valued.v (u : v.adicCompletion K) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
    rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
    rw [ha, inv_one]

theorem isOpen_unitsInt (v : HeightOneSpectrum (𝓞 K)) : IsOpen (unitsInt (K := K) v : Set (v.adicCompletion K)ˣ) := by
  have hO : IsOpen {x : v.adicCompletion K | Valued.v x ≤ 1} := Valued.isOpen_integer (v.adicCompletion K)
  have : (unitsInt (K := K) v : Set (v.adicCompletion K)ˣ) =
      (fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K)) ⁻¹' {x | Valued.v x ≤ 1} ∩
        (fun u : (v.adicCompletion K)ˣ => ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ⁻¹'
          {x | Valued.v x ≤ 1} := by
    ext u
    change Valued.v (u : v.adicCompletion K) = 1 ↔
      Valued.v (u : v.adicCompletion K) ≤ 1 ∧ Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    constructor
    · intro h; rw [h]; simp
    · rintro ⟨h1, h2⟩
      have hne : Valued.v (u : v.adicCompletion K) ≠ 0 := by simp
      refine le_antisymm h1 ?_
      by_contra hlt
      push Not at hlt
      have : 1 < (Valued.v (u : v.adicCompletion K))⁻¹ := one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 hne, hlt⟩
      exact absurd h2 (not_le.2 this)
  rw [this]
  exact (hO.preimage Units.continuous_val).inter (hO.preimage Units.continuous_coe_inv)

/-- **Weil, VII.§8, Corollary of Prop. 17, case (a)** (p. 137), number field case: if $\Gamma$ is discrete, the
extension $\omega$ of $\varphi\circ\mathrm{id}$ exists if and only if open subgroups $g_v$ ($v\in P$, contained in
$r_v^\times$ for $v$ finite) can be chosen so that the condition of Prop. 17 holds with all $\psi_v=1$, i.e.
$\varphi(\mathrm{id}(\xi))=1$ for every $\xi\in\bigcap_{v\in P}(k^\times\cap g_v)$. -/
@[kb "weil1973bnt" "Ch. VII, §8, Corollary of Prop. 17, case (a) (p. 137), number field case"]
theorem weil_VII_8_prop17_cor_discrete {Γ : Type*} [CommGroup Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* Γ) :
    (∃ ω : IdeleGroup (𝓞 K) K →* Γ, Continuous ω ∧ (∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1) ∧
      ∀ x ∈ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))),
        ∀ b : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))), (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
          ω x = φ b) ↔
    ∃ (gInf : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ) (gFin : ∀ v : S, Subgroup ((v.1).adicCompletion K)ˣ),
      (∀ w, IsOpen (gInf w : Set (w.Completion)ˣ)) ∧ (∀ v, IsOpen (gFin v : Set ((v.1).adicCompletion K)ˣ)) ∧
      (∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1) ∧
      Prop17Condition S gInf gFin φ (fun _ => 1) (fun _ => 1) := by
  have : IsTopologicalGroup Γ := { }
  constructor
  · rintro ⟨ω, hω, hk, hG⟩
    have hcInf : ∀ w, Continuous (ω.comp (IdeleGroup.ofCompletion (𝓞 K) K w)) := fun w =>
      hω.comp (item_4_3.2 w).continuous
    have hcFin : ∀ v : S, Continuous (ω.comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1)) := fun v =>
      hω.comp (item_4_3.1 v.1).continuous
    have hU : ∀ v : S, ∀ u ∈ (ω.comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1)).ker ⊓ unitsInt v.1,
        Valued.v (u : (v.1).adicCompletion K) = 1 := fun v u hu => hu.2
    refine ⟨fun w => (ω.comp (IdeleGroup.ofCompletion (𝓞 K) K w)).ker,
      fun v => (ω.comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1)).ker ⊓ unitsInt v.1,
      fun w => ?_, fun v => ?_, hU, ?_⟩
    · exact (isOpen_discrete ({1} : Set Γ)).preimage (hcInf w)
    · exact ((isOpen_discrete ({1} : Set Γ)).preimage (hcFin v)).inter (isOpen_unitsInt v.1)
    · intro ξ hξ b hb
      have e := map_of_mem_gGP hU φ ω hG ⟨_, hξ⟩
      have hb' : idGP hU ⟨_, hξ⟩ = b :=
        Subtype.ext (by rw [idGP_val, hb]; exact ideleToIdeal_unitEmbedding ξ)
      rw [hb', hk, map_psect] at e
      have h1 : ∀ w, ω (IdeleGroup.ofCompletion (𝓞 K) K w
          ((pproj S (IdeleGroup.unitEmbedding (𝓞 K) K ξ)).1 w)) = 1 := fun w => hξ.1 w
      have h2 : ∀ v : S, ω (IdeleGroup.ofAdicCompletion (𝓞 K) K v.1
          ((pproj S (IdeleGroup.unitEmbedding (𝓞 K) K ξ)).2 v)) = 1 := fun v => (hξ.2 v).1
      simp only [h1, h2, Finset.prod_const_one, one_mul] at e
      rw [← e]
      simp [psiProd_apply]
  · rintro ⟨gInf, gFin, hInf, hFin, hFinU, hc⟩
    exact (weil_VII_8_prop17 hInf hFin hFinU φ).2
      ⟨fun _ => 1, fun _ => 1, fun _ => continuous_const, fun _ => continuous_const, hc⟩

end NumberFieldKB.WeilBNT
