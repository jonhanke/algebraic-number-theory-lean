import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Induced
import NumberFieldKB.MilneCFT.Ch2Corestriction

/-!
# Milne, *Class Field Theory*, Chapter II §3: the Tate groups

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Throughout, $G$ is a finite group. Milne's Tate groups $H^r_T(G, M)$, $r \in \mathbb Z$, are Mathlib's
`tateCohomology M r` (homology of the Tate complex, which splices the inhomogeneous chain and cochain complexes
with the norm map), with the long exact sequence `TateCohomology.δ`, `TateCohomology.exact₁`, `exact₃` and the
comparisons `TateCohomology.isoGroupCohomology` ($r > 0$) and `TateCohomology.isoGroupHomology` ($r < -1$).

Contents.
* Proposition 3.1 (induced modules have trivial Tate cohomology), dimension shifting in both directions, the
  claim that $|G|$ kills every $H^r_T(G, M)$ (running text, p. 79), Proposition 3.4 (periodicity for
  cyclic groups).
* Lemma 3.3 is in `Ch2Lemma33.lean`.
* The Herbrand quotient and Propositions 3.6, 3.8, Corollary 3.9 are in `Ch2Herbrand.lean`; Lemma 3.7 in
  `Ch2Exact.lean`.
* Theorem 3.10, Tate's theorem 3.11 and Remark 3.12 as named statements; the splitting module of a 2-cocycle.
* Proposition 3.2 as a named statement.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology groupHomology Limits MonoidalCategory

section Tate

variable {G : Type} [Group G] [Fintype G]

/-! ## Proposition 3.1 and dimension shifting -/

/-! Vanishing in degrees $0$ and $-1$ when the identity is a trace $\sum_g g e g^{-1}$. -/

theorem tate_zero_of_split {M : Rep ℤ G} (e : M →+ M) (he : ∀ m, ∑ g : G, M.ρ g (e (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M 0) := by
  show IsZero ((tateComplex M).homology 0)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change (inhomogeneousCochains M).d 0 1 x = 0 at hx
  obtain ⟨m, rfl⟩ : ∃ m, x = (cochainsIso₀ M).inv m := ⟨(cochainsIso₀ M).hom x, ((cochainsIso₀ M).hom_inv_id_apply x).symm⟩
  have h1 := eq_d₀₁_comp_inv_apply M m
  have h2 : d₀₁ M m = 0 := by
    have : (cochainsIso₁ M).inv (d₀₁ M m) = 0 := by rw [← h1]; exact hx
    simpa using congrArg (cochainsIso₁ M).hom this
  have hinv : ∀ g : G, M.ρ g m = m := fun g => by
    have := congrFun h2 g
    exact sub_eq_zero.1 this
  refine ⟨Finsupp.single default (e m), ?_⟩
  change M.tateNorm _ = _
  rw [Rep.tateNorm_eq]
  funext y
  simp [cochainsIso₀, Representation.norm]
  simpa [hinv] using he m


theorem tate_neg_one_of_split {M : Rep ℤ G} (e : M →+ M)
    (he : ∀ m, ∑ g : G, M.ρ g (e (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M (-1)) := by
  show IsZero ((tateComplex M).homology (-1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change M.tateNorm x = 0 at hx
  obtain ⟨m, rfl⟩ : ∃ m, x = (chainsIso₀ M).inv m :=
    ⟨(chainsIso₀ M).hom x, ((chainsIso₀ M).hom_inv_id_apply x).symm⟩
  have hN : ∑ g : G, M.ρ g m = 0 := by
    rw [Rep.tateNorm_eq] at hx
    have := congrFun hx default
    simp [chainsIso₀, Representation.norm] at this
    exact this
  have hN' : ∑ g : G, M.ρ g⁻¹ m = 0 := by
    rw [← hN]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)
  refine ⟨(chainsIso₁ M).inv (∑ g : G, Finsupp.single g⁻¹ (e (M.ρ g⁻¹ m))), ?_⟩
  change (inhomogeneousChains M).d 1 0 _ = _
  rw [eq_d₁₀_comp_inv_apply]
  congr 1
  have key : (d₁₀ M).hom (∑ g : G, Finsupp.single g⁻¹ (e (M.ρ g⁻¹ m))) =
      ∑ g : G, (d₁₀ M).hom (Finsupp.single g⁻¹ (e (M.ρ g⁻¹ m))) := map_sum _ _ _
  refine key.trans ?_
  simp only [ModuleCat.hom_ofHom, d₁₀, Finsupp.lsum_single, inv_inv, LinearMap.sub_apply,
    LinearMap.id_apply, Finset.sum_sub_distrib]
  rw [← map_sum e, hN']
  simp [he]


open scoped Classical in
theorem tate_indG_zero (M₀ : Type) [AddCommGroup M₀] [Module ℤ M₀] :
    IsZero (tateCohomology (indG G M₀) 0) ∧ IsZero (tateCohomology (indG G M₀) (-1)) := by
  let e : indG G M₀ →+ indG G M₀ :=
    { toFun := fun φ => ⟨fun x => if x = 1 then φ.1 1 else 0, mem_indV (k := ℤ) (G := G) M₀ _⟩
      map_zero' := by ext x; simp
      map_add' := fun φ ψ => by ext x; by_cases h : x = 1 <;> simp [h] }
  have he : ∀ φ, ∑ g : G, (indG G M₀).ρ g (e ((indG G M₀).ρ g⁻¹ φ)) = φ := by
    intro φ
    have hρ : ∀ (g : G) (ψ : indG G M₀) (x : G), ((indG G M₀).ρ g ψ).1 x = ψ.1 (x * g) :=
      fun _ _ _ => rfl
    have he1 : ∀ (ψ : indG G M₀) (x : G), (e ψ).1 x = if x = 1 then ψ.1 1 else 0 :=
      fun _ _ => rfl
    ext x
    have hterm : ∀ g : G, ((indG G M₀).ρ g (e ((indG G M₀).ρ g⁻¹ φ))).1 x =
        if x * g = 1 then φ.1 g⁻¹ else 0 := fun g => by
      rw [hρ, he1, hρ]
      simp
    rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_congr rfl (fun g _ => hterm g),
      Finset.sum_eq_single x⁻¹]
    · simp
    · intro g _ hg
      have : x * g ≠ 1 := fun h => hg (eq_inv_of_mul_eq_one_right h)
      simp [this]
    · simp
  exact ⟨tate_zero_of_split e he, tate_neg_one_of_split e he⟩


open scoped Classical in
/-- **Proposition 3.1** (p. 78). If $M$ is an induced $G$-module, then $H^r_T(G, M) = 0$ for all $r \in \mathbb Z$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 3.1, p. 78"]
theorem prop_3_1 {M : Rep ℤ G} (hM : IsInduced M) (r : ℤ) : IsZero (tateCohomology M r) := by
  obtain ⟨M₀, _, _, ⟨e⟩⟩ := hM
  have hM' : ∀ r, IsZero (tateCohomology (indG G M₀) r) → IsZero (tateCohomology M r) :=
    fun r h => h.of_iso ((tateCohomologyFunctor r).mapIso e)
  refine hM' r ?_
  rcases r with (_ | n) | n
  · exact (tate_indG_zero M₀).1
  · have h := cor_1_12 (M := indG G M₀) ⟨M₀, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩ (n + 1) n.succ_pos
    exact h.of_iso ((TateCohomology.isoGroupCohomology (n + 1)).app _)
  · rcases n with _ | n
    · exact (tate_indG_zero M₀).2
    · have h1 : IsZero (groupHomology (Rep.trivial ℤ (⊥ : Subgroup G) M₀) (n + 1)) :=
        isZero_groupHomology_succ_of_subsingleton _ n
      have h2 := h1.of_iso (groupHomology.indIso (⊥ : Subgroup G) (Rep.trivial ℤ (⊥ : Subgroup G) M₀) (n + 1))
      have h3 := h2.of_iso ((groupHomology.functor ℤ G (n + 1)).mapIso
        (indCoindIso (Rep.trivial ℤ (⊥ : Subgroup G) M₀)).symm)
      exact h3.of_iso ((TateCohomology.isoGroupHomology _ (n + 1) (by rw [Int.negSucc_eq])).app _)

/-- Dimension shifting for Tate groups (p. 79, after Proposition 3.1; Remark 1.13 for all degrees): if
$0 \to M \to J \to N \to 0$ is exact and $H^r_T(G, J) = 0$ for all $r$, the connecting maps
$H^r_T(G, N) \to H^{r+1}_T(G, M)$ are isomorphisms for all $r \in \mathbb Z$. -/
@[kb "milne2020cft" "v4.03, Ch. II, §3, dimension shifting for the Tate groups, p. 79"]
theorem tate_isIso_δ {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact)
    (hJ : ∀ r : ℤ, IsZero (tateCohomology S.X₂ r)) (r : ℤ) : IsIso (TateCohomology.δ hS r) := by
  have hmono : Mono (TateCohomology.δ hS r) :=
    (TateCohomology.exact₃ hS r).mono_g ((hJ r).eq_of_src _ _)
  have hepi : Epi (TateCohomology.δ hS r) :=
    (TateCohomology.exact₁ hS r).epi_f ((hJ (r + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

set_option backward.isDefEq.respectTransparency false in
/-- Generic-coefficient version of `augTensor` (avoids the `ℤ`-module diamond). -/
noncomputable def augTensorAux {k : Type} [CommRing k] (M : Rep k G) : leftRegular k G ⊗ M ⟶ M :=
  Rep.ofHom ⟨TensorProduct.lift
      (Finsupp.lift (M →ₗ[k] M) k G (fun _ => LinearMap.id) ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap), fun g => by
    refine TensorProduct.ext' fun a m => ?_
    simp only [LinearMap.comp_apply]
    change (TensorProduct.lift _) (TensorProduct.map _ _ (a ⊗ₜ m)) = _
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | single x r =>
      simp [Representation.ofMulAction_single, MonoidAlgebra.coeff_single,
        Finsupp.sum_single_index]⟩

/-- The augmentation $\mathbb Z[G] \otimes M \to M$, $g \otimes m \mapsto m$ (diagonal action on the source): the
augmentation sequence (19) tensored with $M$ (p. 79). -/
noncomputable def augTensor (M : Rep ℤ G) : leftRegular ℤ G ⊗ M ⟶ M :=
  augTensorAux M

set_option backward.isDefEq.respectTransparency false in
theorem augTensorAux_apply {k : Type} [CommRing k] (M : Rep k G) (g : G) (m : M) :
    (augTensorAux M).hom (TensorProduct.tmul k (M := leftRegular k G) (N := M)
      (MonoidAlgebra.single g (1 : k)) m) = m := by
  simp [augTensorAux, MonoidAlgebra.coeff_single]

set_option backward.isDefEq.respectTransparency false in
theorem augTensorAux_single {k : Type} [CommRing k] (M : Rep k G) (g : G) (r : k) (m : M) :
    (augTensorAux M).hom (MonoidAlgebra.single g r ⊗ₜ[k] m) = r • m := by
  simp [augTensorAux, MonoidAlgebra.coeff_single]

set_option backward.isDefEq.respectTransparency false in
theorem augTensor_apply (M : Rep ℤ G) (g : G) (m : M) :
    (augTensor M).hom (rtmul (A := leftRegular ℤ G) (B := M) (MonoidAlgebra.single g (1 : ℤ)) m) = m :=
  augTensorAux_apply M g m

/-- The exact sequence $0 \to M' \to \mathbb Z[G] \otimes_{\mathbb Z} M \to M \to 0$ obtained by tensoring the
augmentation sequence (19) with $M$ (p. 79): $M'$ is the kernel of `augTensor`. -/
@[kb "milne2020cft" "v4.03, Ch. II, §3, the sequence 0 → M' → Z[G] ⊗ M → M → 0, p. 79"]
noncomputable def augSeq (M : Rep ℤ G) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (kernel.ι (augTensor M)) (augTensor M) (kernel.condition _)

theorem augSeq_shortExact (M : Rep ℤ G) : (augSeq M).ShortExact := by
  have : Epi (augTensor M) := by
    rw [Rep.epi_iff_surjective]
    intro m
    exact ⟨_, augTensor_apply M 1 m⟩
  have : Mono (augSeq M).f := inferInstanceAs (Mono (kernel.ι (augTensor M)))
  have : Epi (augSeq M).g := ‹Epi (augTensor M)›
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (augTensor M)) inferInstance inferInstance

/-- Milne (p. 79, p. 83): $\mathbb Z[G] \otimes_{\mathbb Z} M \simeq \mathbb Z[G] \otimes_{\mathbb Z} M_0 \simeq
\operatorname{Ind}^G(M_0)$ is induced (Remarks 1.4 and 1.3). -/
@[kb "milne2020cft" "v4.03, Ch. II, §3, Z[G] ⊗ M is induced, p. 79, p. 83"]
theorem isInduced_leftRegular_tensor (M : Rep ℤ G) : IsInduced (leftRegular ℤ G ⊗ M) :=
  ⟨M, inferInstance, inferInstance, ⟨(remark_1_4 M).symm ≪≫ (indGIsoTensor (G := G) M).symm⟩⟩

omit [Fintype G] in
theorem zsmul_eq_zero_of_mono {A B : ModuleCat ℤ} (f : A ⟶ B) [Mono f] (n : ℤ) (x : A)
    (h : n • f x = 0) : n • x = 0 := by
  have hinj := (ModuleCat.mono_iff_injective f).1 ‹_›
  apply hinj
  rw [map_zsmul, map_zero]
  exact h

/-- Milne (p. 79): $H^r_T(G, M)$ is killed by $|G|$ for every $G$-module $M$ and every $r \in \mathbb Z$. (For
$r > 0$ this is Corollary 1.31; Milne extends it to all $r$ by dimension shifting.) -/
@[kb "milne2020cft" "v4.03, Ch. II, §3, H^r_T(G, M) is killed by (G : 1), p. 79"]
theorem tate_card_smul_eq_zero (M : Rep ℤ G) (r : ℤ) (x : tateCohomology M r) :
    (Fintype.card G : ℤ) • x = 0 := by
  have key : ∀ (n : ℕ) (M : Rep ℤ G) (r : ℤ), 1 - (n : ℤ) ≤ r → ∀ x : tateCohomology M r,
      (Fintype.card G : ℤ) • x = 0 := by
    intro n
    induction n with
    | zero =>
      intro M r hr x
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = (m + 1 : ℕ) := ⟨(r - 1).toNat, by omega⟩
      refine zsmul_eq_zero_of_mono ((TateCohomology.isoGroupCohomology (m + 1)).app M).hom _ x ?_
      have := cor_1_31 M (m + 1) m.succ_pos
        (((TateCohomology.isoGroupCohomology (m + 1)).app M).hom x)
      rw [Nat.card_eq_fintype_card] at this
      exact this
    | succ n ih =>
      intro M r hr x
      by_cases h : 1 ≤ r
      · exact ih M r (by omega) x
      · have hiso := tate_isIso_δ (augSeq_shortExact M)
          (fun r => prop_3_1 (isInduced_leftRegular_tensor M) r) r
        haveI : Mono (TateCohomology.δ (augSeq_shortExact M) r) := inferInstance
        refine zsmul_eq_zero_of_mono (TateCohomology.δ (augSeq_shortExact M) r) _
          (x : tateCohomology (augSeq M).X₃ r) ?_
        exact ih (augSeq M).X₁ (r + 1) (by omega) _
  exact key (1 - r).toNat M r (by omega) x

/-! ## Proposition 3.4: periodicity for cyclic groups -/

section Cyclic

/-- For finite cyclic $G$: the $G$-map $M \to \mathbb Z[G] \otimes M$, $m \mapsto \mathrm{Nm}_G \otimes m =
\sum_{h \in G} h \otimes m$ (the first map of the sequence in the proof of Proposition 3.4, tensored with $M$). -/
noncomputable def normTensor (M : Rep ℤ G) : M ⟶ leftRegular ℤ G ⊗ M :=
  Rep.ofHom ⟨∑ h : G, TensorProduct.mk ℤ (MonoidAlgebra ℤ G) M (MonoidAlgebra.single h (1 : ℤ)), fun g => by
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, TensorProduct.mk_apply,
      Representation.tprod_apply, TensorProduct.map_tmul, Representation.ofMulAction_single]
    exact (Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun x => rfl)).symm⟩

theorem normTensor_apply (M : Rep ℤ G) (m : M) :
    (normTensor M).hom m =
      ∑ h : G, rtmul (A := leftRegular ℤ G) (B := M) (MonoidAlgebra.single h (1 : ℤ)) m := by
  simp [normTensor, rtmul]

omit [Fintype G] in
theorem mul_comm_of_mem_zpowers {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : G) : g * x = x * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  exact ((Commute.refl g).zpow_right k).eq

set_option backward.isDefEq.respectTransparency false in
/-- The endomorphism $a \otimes m \mapsto (g - 1)a \otimes m$ of $\mathbb Z[G] \otimes M$, $G$-linear because
$g$ is central. -/
noncomputable def subOneEnd (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) :
    leftRegular ℤ G ⊗ M ⟶ leftRegular ℤ G ⊗ M :=
  Rep.ofHom ⟨TensorProduct.map ((leftRegular ℤ G).ρ g - LinearMap.id) LinearMap.id, fun x => by
    refine monoidAlgebra_tensor_ext fun y r v => ?_
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.ofMulAction_single, LinearMap.sub_apply, LinearMap.id_apply,
      TensorProduct.sub_tmul]
    have : g • x • y = x • g • y := by
      simp only [smul_eq_mul, ← mul_assoc, mul_comm_of_mem_zpowers hg x]
    rw [this, map_sub]
    simp [Representation.ofMulAction_single]⟩

set_option backward.isDefEq.respectTransparency false in
theorem subOneEnd_comp_augTensor (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) :
    subOneEnd g hg M ≫ augTensor M = 0 := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext ?_)
  refine monoidAlgebra_tensor_ext fun x r v => ?_
  change (augTensor M).hom ((subOneEnd g hg M).hom (MonoidAlgebra.single x r ⊗ₜ[ℤ] v)) = 0
  have : (subOneEnd g hg M).hom (MonoidAlgebra.single x r ⊗ₜ[ℤ] v) =
      MonoidAlgebra.single (g * x) r ⊗ₜ[ℤ] v - MonoidAlgebra.single x r ⊗ₜ[ℤ] v := by
    simp [subOneEnd, Representation.ofMulAction_single, TensorProduct.sub_tmul]
  rw [this, map_sub]
  change (augTensorAux M).hom _ - (augTensorAux M).hom _ = 0
  rw [augTensorAux_single, augTensorAux_single, sub_self]

/-- For $G$ cyclic with generator $g$: the $G$-map $\mathbb Z[G] \otimes M \to M'$, $a \otimes m \mapsto
(g - 1)a \otimes m$, where $M' = \operatorname{Ker}(\mathbb Z[G] \otimes M \to M)$ (the middle map of the sequence in
the proof of Proposition 3.4; it is $G$-linear because $G$ is commutative). -/
noncomputable def subOneTensor (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) : leftRegular ℤ G ⊗ M ⟶ kernel (augTensor M) :=
  kernel.lift (augTensor M) (subOneEnd g hg M) (subOneEnd_comp_augTensor g hg M)

theorem subOneTensor_apply (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) (h : G) (m : M) :
    kernel.ι (augTensor M) ((subOneTensor g hg M).hom
      (rtmul (A := leftRegular ℤ G) (B := M) (MonoidAlgebra.single h (1 : ℤ)) m)) =
      rtmul (A := leftRegular ℤ G) (B := M) (MonoidAlgebra.single (g * h) (1 : ℤ)) m -
        rtmul (A := leftRegular ℤ G) (B := M) (MonoidAlgebra.single h (1 : ℤ)) m := by
  rw [← Rep.comp_apply, subOneTensor, kernel.lift_ι]
  simp [subOneEnd, rtmul, Representation.ofMulAction_single, TensorProduct.sub_tmul]

set_option backward.isDefEq.respectTransparency false in
theorem normTensor_comp_subOneTensor (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) :
    normTensor M ≫ subOneTensor g hg M = 0 := by
  refine (cancel_mono (kernel.ι (augTensor M))).1 ?_
  rw [zero_comp]
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun m => ?_))
  change kernel.ι (augTensor M) ((subOneTensor g hg M).hom ((normTensor M).hom m)) = 0
  rw [normTensor_apply, map_sum, map_sum]
  simp only [subOneTensor_apply, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun x => rfl)

theorem exists_telescope {A : Type} [AddCommGroup A] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (φ : G → A) (h : ∑ x, φ x = 0) : ∃ ψ : G → A, ∀ x, ψ (g⁻¹ * x) - ψ x = φ x := by
  classical
  set n := orderOf g with hn
  have hpos : 0 < n := orderOf_pos g
  have hsurj : ∀ x : G, ∃ i, i < n ∧ g ^ i = x := fun x => by
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).2 (hg x)
    exact ⟨k % n, Nat.mod_lt _ hpos, (pow_mod_orderOf g k).trans hk⟩
  have hinj : ∀ i j, i < n → j < n → g ^ i = g ^ j → i = j := fun i j hi hj h =>
    pow_injOn_Iio_orderOf hi hj h
  have hsurj' := hsurj
  choose idx hidx hgidx using hsurj
  have hidx_eq : ∀ x i, i < n → g ^ i = x → idx x = i := fun x i hi h =>
    hinj _ _ (hidx x) hi (by rw [hgidx x, h])
  have hsum : ∑ i ∈ Finset.range n, φ (g ^ i) = 0 := by
    rw [← h]
    refine Finset.sum_bij (fun i _ => g ^ i) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb hab
      exact hinj a b (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab
    · intro x _
      obtain ⟨i, hi, rfl⟩ := hsurj' x
      exact ⟨i, Finset.mem_range.2 hi, rfl⟩
    · intro i _; rfl
  refine ⟨fun x => φ 1 - ∑ j ∈ Finset.range (idx x + 1), φ (g ^ j), fun x => ?_⟩
  have hgn : g ^ n = 1 := pow_orderOf_eq_one g
  have hx := hgidx x
  have hi := hidx x
  generalize idx x = i at hx hi
  have key : ∀ j, j < n → idx (g ^ j) = j := fun j hj => hidx_eq _ j hj rfl
  rcases i with _ | j
  · subst hx
    have h1 : g⁻¹ * g ^ 0 = g ^ (n - 1) := by
      rw [pow_zero, mul_one, inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hpos, hgn]
    simp only [h1, key (n - 1) (by omega), key 0 hpos]
    rw [Nat.sub_add_cancel hpos, hsum]
    simp
  · subst hx
    have h1 : g⁻¹ * g ^ (j + 1) = g ^ j := by
      rw [pow_succ', ← mul_assoc, inv_mul_cancel, one_mul]
    simp only [h1, key j (by omega), key (j + 1) hi]
    rw [Finset.sum_range_succ _ (j + 1)]
    abel


open scoped TensorProduct in
/-- The coordinates $k[G] \otimes M_0 \to (G \to M_0)$, $a \otimes m \mapsto (x \mapsto a_x m)$. -/
noncomputable def coordFun {k : Type} [CommRing k] (M₀ : Type) [AddCommGroup M₀] [Module k M₀] :
    MonoidAlgebra k G ⊗[k] M₀ →ₗ[k] (G → M₀) :=
  TensorProduct.lift (LinearMap.mk₂ k (fun (a : MonoidAlgebra k G) (m : M₀) => fun x : G =>
      a.coeff x • m)
    (fun a b m => by funext x; simp [add_smul])
    (fun c a m => by funext x; simp [mul_smul])
    (fun a m n => by funext x; simp [smul_add])
    (fun c a m => by funext x; simp [smul_comm c]))

open scoped TensorProduct in
theorem coordFun_tmul {k : Type} [CommRing k] (M₀ : Type) [AddCommGroup M₀] [Module k M₀]
    (a : MonoidAlgebra k G) (m : M₀) (x : G) :
    coordFun (k := k) M₀ (a ⊗ₜ[k] m) x = a.coeff x • m := by
  simp [coordFun]

open scoped TensorProduct in
theorem coordFun_single {k : Type} [CommRing k] (M₀ : Type) [AddCommGroup M₀] [Module k M₀]
    [DecidableEq G] (y : G) (r : k) (m : M₀) (x : G) :
    coordFun (k := k) M₀ (MonoidAlgebra.single y r ⊗ₜ[k] m) x = if x = y then r • m else 0 := by
  rw [coordFun_tmul, MonoidAlgebra.coeff_single]
  by_cases h : x = y <;> simp [h]

open scoped TensorProduct in
omit [Fintype G] in
theorem tensor_eq_sum {k : Type} [CommRing k] (M₀ : Type) [AddCommGroup M₀] [Module k M₀]
    [Fintype G] [DecidableEq G] (t : MonoidAlgebra k G ⊗[k] M₀) :
    t = ∑ x : G, MonoidAlgebra.single x (1 : k) ⊗ₜ[k] (coordFun (k := k) M₀ t x) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      conv_lhs => rw [TensorProduct.add_tmul, ha, hb]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← TensorProduct.tmul_add]
      simp only [TensorProduct.add_tmul, map_add, Pi.add_apply]
    | single y r =>
      simp only [coordFun_single, TensorProduct.tmul_ite, TensorProduct.tmul_zero]
      rw [Finset.sum_ite_eq' Finset.univ y, if_pos (Finset.mem_univ y)]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', MonoidAlgebra.smul_single, smul_eq_mul,
        mul_one]
  | add t u ht hu =>
    conv_lhs => rw [ht, hu]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← TensorProduct.tmul_add, ← Pi.add_apply, ← map_add]

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
theorem subOneEnd_single (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) (y : G) (r : ℤ) (m : M) :
    (subOneEnd g hg M).hom (MonoidAlgebra.single y r ⊗ₜ[ℤ] m) =
      MonoidAlgebra.single (g * y) r ⊗ₜ[ℤ] m - MonoidAlgebra.single y r ⊗ₜ[ℤ] m := by
  simp [subOneEnd, Representation.ofMulAction_single, TensorProduct.sub_tmul]

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
theorem coordFun_subOneEnd (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G)
    (t : MonoidAlgebra ℤ G ⊗[ℤ] M) (x : G) :
    coordFun (k := ℤ) M ((subOneEnd g hg M).hom t) x =
      coordFun (k := ℤ) M t (g⁻¹ * x) - coordFun (k := ℤ) M t x := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply, sub_self]
  | tmul a m =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp only [TensorProduct.zero_tmul, map_zero, Pi.zero_apply, sub_self]
    | add a b ha hb =>
      rw [TensorProduct.add_tmul, map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, Pi.add_apply,
        ha, hb]
      abel
    | single y r =>
      rw [subOneEnd_single, map_sub, Pi.sub_apply, coordFun_single, coordFun_single, coordFun_single]
      simp only [inv_mul_eq_iff_eq_mul]
  | add t u ht hu =>
    rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, Pi.add_apply, ht, hu]
    abel

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
theorem coordFun_normTensor (M : Rep ℤ G) (m : M) (x : G) :
    coordFun (k := ℤ) M ((normTensor M).hom m) x = m := by
  classical
  rw [normTensor_apply, map_sum, Finset.sum_apply]
  simp only [rtmul, coordFun_single]
  simp

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
theorem augTensor_eq_sum (M : Rep ℤ G) (t : MonoidAlgebra ℤ G ⊗[ℤ] M) :
    (augTensor M).hom t = ∑ x : G, coordFun (k := ℤ) M t x := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [TensorProduct.add_tmul, map_add, ha, hb, map_add]
      simp [Finset.sum_add_distrib]
    | single y r =>
      change (augTensorAux M).hom _ = _
      rw [augTensorAux_single]
      simp only [coordFun_single]
      simp
  | add t u ht hu =>
    rw [map_add, ht, hu, map_add]
    simp [Finset.sum_add_distrib]

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
theorem exists_of_subOneEnd_eq_zero (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G)
    (t : MonoidAlgebra ℤ G ⊗[ℤ] M) (ht : (subOneEnd g hg M).hom t = 0) :
    ∃ m : M, t = (normTensor M).hom m := by
  classical
  have h1 : ∀ x, coordFun (k := ℤ) M t (g⁻¹ * x) = coordFun (k := ℤ) M t x := fun x => by
    have := coordFun_subOneEnd g hg M t x
    rw [ht] at this
    simp only [map_zero, Pi.zero_apply] at this
    exact (sub_eq_zero.1 this.symm)
  have h2 : ∀ k : ℤ, coordFun (k := ℤ) M t (g ^ k) = coordFun (k := ℤ) M t 1 := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [← ih, ← h1 (g ^ ((k : ℤ) + 1))]
      congr 1
      group
    | pred k ih =>
      rw [← ih, ← h1 (g ^ (-(k : ℤ)))]
      congr 1
      group
  refine ⟨coordFun (k := ℤ) M t 1, ?_⟩
  refine (tensor_eq_sum (k := ℤ) M t).trans ?_
  rw [normTensor_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  rw [h2]

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
theorem exists_subOneEnd_eq_of_augTensor_eq_zero (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (M : Rep ℤ G) (t : MonoidAlgebra ℤ G ⊗[ℤ] M) (ht : (augTensor M).hom t = 0) :
    ∃ s, (subOneEnd g hg M).hom s = t := by
  classical
  rw [augTensor_eq_sum] at ht
  obtain ⟨ψ, hψ⟩ := exists_telescope g hg (coordFun (k := ℤ) M t) ht
  let s : MonoidAlgebra ℤ G ⊗[ℤ] M := ∑ x : G, MonoidAlgebra.single x (1 : ℤ) ⊗ₜ[ℤ] ψ x
  have hs : ∀ z, coordFun (k := ℤ) M s z = ψ z := fun z => by
    simp only [s, map_sum, Finset.sum_apply, coordFun_single]
    simp
  refine ⟨s, ?_⟩
  refine (tensor_eq_sum (k := ℤ) M _).trans ?_
  refine Eq.trans (Finset.sum_congr rfl fun x _ => ?_) (tensor_eq_sum (k := ℤ) M t).symm
  rw [coordFun_subOneEnd, hs, hs, hψ]

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
theorem normTensor_injective (M : Rep ℤ G) : Function.Injective (normTensor M).hom := by
  intro m n h
  have := congrArg (fun t => coordFun (k := ℤ) M t 1) h
  rwa [coordFun_normTensor, coordFun_normTensor] at this

/-- The exact sequence $0 \to M \to \mathbb Z[G] \otimes M \to M' \to 0$ for $G$ cyclic with generator $g$: with
`augSeq M` it splices to Milne's sequence $0 \to M \to \mathbb Z[G] \otimes M \to \mathbb Z[G] \otimes M \to M \to 0$
(proof of Proposition 3.4, p. 81). -/
noncomputable def cyclicSeq (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (normTensor M) (subOneTensor g hg M) (normTensor_comp_subOneTensor g hg M)

theorem cyclicSeq_shortExact (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) : (cyclicSeq g hg M).ShortExact := by
  have hι : Function.Injective (kernel.ι (augTensor M)).hom :=
    (Rep.mono_iff_injective _).1 inferInstance
  have hι' : ∀ t, (kernel.ι (augTensor M)).hom ((subOneTensor g hg M).hom t) =
      (subOneEnd g hg M).hom t := fun t => by
    rw [← Rep.comp_apply, subOneTensor, kernel.lift_ι]
  have hmono : Mono (cyclicSeq g hg M).f := (Rep.mono_iff_injective _).2 (normTensor_injective M)
  have hepi : Epi (cyclicSeq g hg M).g := by
    rw [Rep.epi_iff_surjective]
    change Function.Surjective (subOneTensor g hg M).hom
    intro y
    obtain ⟨s, hs⟩ := exists_subOneEnd_eq_of_augTensor_eq_zero g hg M
      ((kernel.ι (augTensor M)).hom y) (by
        rw [← Rep.comp_apply, kernel.condition]; rfl)
    exact ⟨s, hι (by rw [hι', hs])⟩
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ G) (ModuleCat ℤ)),
    ShortComplex.moduleCat_exact_iff]
  refine fun (t : ↑(leftRegular ℤ G ⊗ M)) (ht : (subOneTensor g hg M).hom t = 0) => ?_
  have ht' : (subOneEnd g hg M).hom t = 0 := by
    rw [← hι', ht, map_zero]
  exact (exists_of_subOneEnd_eq_zero g hg M t ht').imp fun m hm => hm.symm

/-- The periodicity isomorphism $H^r_T(G, M) \to H^{r+2}_T(G, M)$ for $G$ cyclic with generator $g$ (Proposition
3.4, p. 81): the composite of the connecting isomorphisms of `augSeq M` and `cyclicSeq g hg M`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 3.4, the periodicity isomorphism, p. 81"]
noncomputable def periodicity (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) (r : ℤ) : tateCohomology M r ≅ tateCohomology M (r + 2) :=
  @asIso _ _ _ _ (TateCohomology.δ (augSeq_shortExact M) r)
      (tate_isIso_δ (augSeq_shortExact M) (fun r => prop_3_1 (isInduced_leftRegular_tensor M) r) r) ≪≫
    @asIso _ _ _ _ (TateCohomology.δ (cyclicSeq_shortExact g hg M) (r + 1))
      (tate_isIso_δ (cyclicSeq_shortExact g hg M)
        (fun r => prop_3_1 (isInduced_leftRegular_tensor M) r) (r + 1)) ≪≫
    eqToIso (by rw [add_assoc]; rfl)

/-- **Proposition 3.4** (p. 81). Let $G$ be a finite cyclic group. The choice of a generator determines
isomorphisms $H^r_T(G, M) \to H^{r+2}_T(G, M)$ for all $G$-modules $M$ and all $r \in \mathbb Z$ (`periodicity`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 3.4, p. 81"]
theorem prop_3_4 (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Rep ℤ G) (r : ℤ) : Nonempty (tateCohomology M r ≅ tateCohomology M (r + 2)) :=
  ⟨periodicity g hg M r⟩

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
omit [Fintype G] in
theorem whisker_tmul {M N : Rep ℤ G} (f : M ⟶ N) (a : MonoidAlgebra ℤ G) (m : M) :
    (𝟙 (leftRegular ℤ G) ⊗ₘ f).hom (a ⊗ₜ[ℤ] m) = a ⊗ₜ[ℤ] f.hom m := by
  simp

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
theorem whisker_comp_augTensor {M N : Rep ℤ G} (f : M ⟶ N) :
    (𝟙 (leftRegular ℤ G) ⊗ₘ f) ≫ augTensor N = augTensor M ≫ f := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext ?_)
  refine monoidAlgebra_tensor_ext fun x r v => ?_
  change (augTensorAux N).hom ((𝟙 (leftRegular ℤ G) ⊗ₘ f).hom (MonoidAlgebra.single x r ⊗ₜ[ℤ] v)) =
    f.hom ((augTensorAux M).hom (MonoidAlgebra.single x r ⊗ₜ[ℤ] v))
  rw [whisker_tmul, augTensorAux_single, augTensorAux_single]
  exact (f.hom.toLinearMap.map_smul r v).symm

/-- The map $M' \to N'$ on the kernels of the augmentations induced by `f : M ⟶ N`. -/
noncomputable def augKernelMap {M N : Rep ℤ G} (f : M ⟶ N) : kernel (augTensor M) ⟶ kernel (augTensor N) :=
  kernel.map (augTensor M) (augTensor N) (𝟙 (leftRegular ℤ G) ⊗ₘ f) f (whisker_comp_augTensor f).symm

/-- The morphism `augSeq M ⟶ augSeq N` induced by `f : M ⟶ N`. -/
noncomputable def augMap {M N : Rep ℤ G} (f : M ⟶ N) : augSeq M ⟶ augSeq N where
  τ₁ := augKernelMap f
  τ₂ := 𝟙 (leftRegular ℤ G) ⊗ₘ f
  τ₃ := f
  comm₁₂ := by simp [augSeq, augKernelMap]
  comm₂₃ := whisker_comp_augTensor f

set_option backward.isDefEq.respectTransparency false in
theorem subOneEnd_comp_whisker (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) {M N : Rep ℤ G} (f : M ⟶ N) :
    subOneEnd g hg M ≫ (𝟙 (leftRegular ℤ G) ⊗ₘ f) = (𝟙 (leftRegular ℤ G) ⊗ₘ f) ≫ subOneEnd g hg N := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext ?_)
  refine monoidAlgebra_tensor_ext fun x r v => ?_
  change (𝟙 (leftRegular ℤ G) ⊗ₘ f).hom ((subOneEnd g hg M).hom (MonoidAlgebra.single x r ⊗ₜ[ℤ] v)) =
    (subOneEnd g hg N).hom ((𝟙 (leftRegular ℤ G) ⊗ₘ f).hom (MonoidAlgebra.single x r ⊗ₜ[ℤ] v))
  rw [whisker_tmul, subOneEnd_single, subOneEnd_single, map_sub, whisker_tmul, whisker_tmul]

/-- The morphism `cyclicSeq g hg M ⟶ cyclicSeq g hg N` induced by `f : M ⟶ N`. -/
noncomputable def cyclicMap (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) {M N : Rep ℤ G} (f : M ⟶ N) :
    cyclicSeq g hg M ⟶ cyclicSeq g hg N where
  τ₁ := f
  τ₂ := 𝟙 (leftRegular ℤ G) ⊗ₘ f
  τ₃ := augKernelMap f
  comm₁₂ := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun (m : M) => ?_))
    change (normTensor N).hom (f.hom m) = (𝟙 (leftRegular ℤ G) ⊗ₘ f).hom ((normTensor M).hom m)
    rw [normTensor_apply, normTensor_apply, map_sum]
    exact Finset.sum_congr rfl fun x _ => (whisker_tmul f _ m).symm
  comm₂₃ := by
    refine (cancel_mono (kernel.ι (augTensor N))).1 ?_
    have h1 : ∀ (M : Rep ℤ G), subOneTensor g hg M ≫ kernel.ι (augTensor M) = subOneEnd g hg M :=
      fun M => kernel.lift_ι _ _ _
    change (𝟙 (leftRegular ℤ G) ⊗ₘ f) ≫ subOneTensor g hg N ≫ kernel.ι (augTensor N) =
      subOneTensor g hg M ≫ augKernelMap f ≫ kernel.ι (augTensor N)
    have h2 : augKernelMap f ≫ kernel.ι (augTensor N) = kernel.ι (augTensor M) ≫ (𝟙 (leftRegular ℤ G) ⊗ₘ f) :=
      kernel.lift_ι _ _ _
    rw [h2, ← Category.assoc (subOneTensor g hg M), h1, h1, subOneEnd_comp_whisker]

omit [Group G] [Fintype G] in
theorem comp_comp_comp_aux {A A' B B' C C' D D' : ModuleCat ℤ} (δ₁ : A ⟶ B) (δ₂ : B ⟶ C) (e : C ⟶ D)
    (δ₁' : A' ⟶ B') (δ₂' : B' ⟶ C') (e' : C' ⟶ D') {u : A ⟶ A'} {v : B ⟶ B'} {w : C ⟶ C'}
    {x : D ⟶ D'} (h₁ : δ₁ ≫ v = u ≫ δ₁') (h₂ : δ₂ ≫ w = v ≫ δ₂') (h₃ : e ≫ x = w ≫ e') :
    (δ₁ ≫ δ₂ ≫ e) ≫ x = u ≫ δ₁' ≫ δ₂' ≫ e' := by
  rw [Category.assoc, Category.assoc, h₃, ← Category.assoc δ₂, h₂, Category.assoc, ← Category.assoc δ₁, h₁,
    Category.assoc]

theorem eqToHom_tate_naturality (a b : ℤ) (h : a = b) {M N : Rep ℤ G} (f : M ⟶ N)
    (hM : tateCohomology M a = tateCohomology M b) (hN : tateCohomology N a = tateCohomology N b) :
    eqToHom hM ≫ (tateCohomologyFunctor b).map f = (tateCohomologyFunctor a).map f ≫ eqToHom hN := by
  subst h
  simp

/-- The periodicity isomorphisms are natural in $M$. -/
theorem periodicity_naturality (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) {M N : Rep ℤ G} (f : M ⟶ N) (r : ℤ) :
    (periodicity g hg M r).hom ≫ (tateCohomologyFunctor (r + 2)).map f =
      (tateCohomologyFunctor r).map f ≫ (periodicity g hg N r).hom := by
  have h1 := TateCohomology.δ_naturality (augSeq_shortExact M) (augSeq_shortExact N) (augMap f) r
  have h2 := TateCohomology.δ_naturality (cyclicSeq_shortExact g hg M) (cyclicSeq_shortExact g hg N)
    (cyclicMap g hg f) (r + 1)
  dsimp only [periodicity, Iso.trans_hom, asIso, eqToIso.hom]
  refine comp_comp_comp_aux _ _ _ _ _ _ h1 h2 ?_
  exact eqToHom_tate_naturality (r + 1 + 1) (r + 2) (by omega) f _ _

end Cyclic

end Tate

/-! ## Theorems 3.10, 3.11 and Remark 3.12 -/

/-- **Theorem 3.10** (p. 83), as a named statement. Let $G$ be a finite group and $M$ a $G$-module. If
$H^1(H, M) = 0 = H^2(H, M)$ for all subgroups $H$ of $G$, then $H^r_T(G, M) = 0$ for all $r \in \mathbb Z$. Milne's
proof (cyclic case by periodicity, solvable case by induction with Proposition 1.34, general case by Sylow
subgroups and Corollary 1.33) needs Proposition 1.34 in all degrees.

**Proved here** as `thm3_10` (`Ch2TateTriviality.lean`), from the ported copy under `NumberFieldKB/TauCetiPort/` of Tau Ceti
`TauCeti.TateCohomology.isZero_of_forall_isPGroup`
(`TauCeti/RepresentationTheory/Homological/TateCohomology/TrivialityCriterion.lean:193`) (read at Tau Ceti `7ed979dc`, ported from `67aa1716`).
Needed to apply it here: Tau Ceti needs the vanishing hypotheses only for subgroups of prime-power order, in two
consecutive degrees (take degrees one and two); one must compare ordinary cohomology in degrees one and two with Tate
cohomology, and our Tate cohomology with Tau Ceti's. -/
@[kb "milne2020cft" "v4.03, Ch. II, Thm. 3.10, p. 83"]
structure Thm3_10 : Prop where
  vanish : ∀ (G : Type) [Group G] [Fintype G] (M : Rep ℤ G),
    (∀ H : Subgroup G, IsZero (groupCohomology (res H.subtype M) 1) ∧
      IsZero (groupCohomology (res H.subtype M) 2)) →
    ∀ r : ℤ, IsZero (tateCohomology M r)

/-- **Theorem 3.11 (Tate's theorem)** (p. 84), as a named statement. Let $G$ be a finite group and $C$ a
$G$-module such that for every subgroup $H$ of $G$ (including $H = G$), $H^1(H, C) = 0$ and $H^2(H, C)$ is
cyclic of order $(H : 1)$. Then for every generator $\gamma$ of $H^2(G, C)$ and every $r \in \mathbb Z$ there is an
isomorphism $H^r_T(G, \mathbb Z) \to H^{r+2}_T(G, C)$ (depending only on $\gamma$: Milne's is the double connecting
map of the sequence (24) built from the splitting module of a cocycle representing $\gamma$; by Remark 3.13 it is
cup product with $\gamma$). -/
@[kb "milne2020cft" "v4.03, Ch. II, Thm. 3.11, p. 84"]
structure Thm3_11 : Prop where
  iso : ∀ (G : Type) [Group G] [Fintype G] (C : Rep ℤ G),
    (∀ H : Subgroup G, IsZero (groupCohomology (res H.subtype C) 1) ∧
      IsAddCyclic (groupCohomology (res H.subtype C) 2) ∧
      Nat.card (groupCohomology (res H.subtype C) 2) = Nat.card H) →
    ∀ γ : groupCohomology C 2, (∀ x : groupCohomology C 2, x ∈ AddSubgroup.zmultiples γ) →
    ∀ r : ℤ, Nonempty (tateCohomology (trivial ℤ G ℤ) r ≅ tateCohomology C (r + 2))

/-- **Remark 3.12** (p. 85), as a named statement. Under the hypotheses of Tate's theorem, for a $G$-module $M$
with $\operatorname{Tor}^{\mathbb Z}_1(M, C) = 0$ (for example if $M$ or $C$ is torsion-free), tensoring the
4-term sequence (24) with $M$ gives isomorphisms $H^r_T(G, M) \to H^{r+2}_T(G, M \otimes C)$ for all $r$. The
condition is stated for the underlying abelian groups with Mathlib's `CategoryTheory.Tor` in `ModuleCat ℤ`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 3.12, p. 85"]
structure Remark3_12 : Prop where
  iso : ∀ (G : Type) [Group G] [Fintype G] (C M : Rep ℤ G),
    (∀ H : Subgroup G, IsZero (groupCohomology (res H.subtype C) 1) ∧
      IsAddCyclic (groupCohomology (res H.subtype C) 2) ∧
      Nat.card (groupCohomology (res H.subtype C) 2) = Nat.card H) →
    IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M)).obj (ModuleCat.of ℤ C)) →
    ∀ γ : groupCohomology C 2, (∀ x : groupCohomology C 2, x ∈ AddSubgroup.zmultiples γ) →
    ∀ r : ℤ, Nonempty (tateCohomology M r ≅ tateCohomology (M ⊗ C) (r + 2))

/-! ## The splitting module (p. 84) -/

section Splitting

variable {G : Type} [Group G] (C : Rep ℤ G) (φ : cocycles₂ C)

/-- The underlying abelian group of the **splitting module** $C(\varphi)$ of a 2-cocycle $\varphi$ (p. 84): the
direct sum of $C$ with the free abelian group on symbols $x_\sigma$, $\sigma \in G$, $\sigma \neq 1$. -/
abbrev SplittingCarrier : Type := C × ({σ : G // σ ≠ 1} →₀ ℤ)

/-- The symbol $x_\sigma \in C(\varphi)$, with $x_1$ interpreted as $\varphi(1, 1) \in C$ (p. 84). -/
noncomputable def splittingX [DecidableEq G] (σ : G) : SplittingCarrier C :=
  if h : σ = 1 then ((φ : G × G → C) (1, 1), 0) else (0, Finsupp.single ⟨σ, h⟩ 1)

variable [DecidableEq G]

/-- The action of $\sigma \in G$ on the splitting module, as an additive map: $\sigma$ on $C$, and
$x_\tau \mapsto x_{\sigma\tau} - x_\sigma + \varphi(\sigma, \tau)$ on the symbols. -/
noncomputable def splittingAct (σ : G) : SplittingCarrier C →+ SplittingCarrier C :=
  AddMonoidHom.coprod ((AddMonoidHom.inl C _).comp (C.ρ σ).toAddMonoidHom)
    (Finsupp.liftAddHom fun τ : {τ : G // τ ≠ 1} =>
      zmultiplesHom _ (splittingX C φ (σ * τ) - splittingX C φ σ + ((φ : G × G → C) (σ, τ), 0)))

@[simp] theorem splittingAct_inl (σ : G) (c : C) :
    splittingAct C φ σ (c, 0) = (C.ρ σ c, 0) := by
  simp [splittingAct]

theorem splittingX_one : splittingX C φ 1 = ((φ : G × G → C) (1, 1), 0) := by
  simp [splittingX]

theorem splittingAct_X (σ τ : G) :
    splittingAct C φ σ (splittingX C φ τ) =
      splittingX C φ (σ * τ) - splittingX C φ σ + ((φ : G × G → C) (σ, τ), 0) := by
  by_cases h : τ = 1
  · subst h
    rw [splittingX_one, splittingAct_inl, mul_one, cocycles₂_map_one_snd φ σ]
    simp
  · simp only [splittingX, dite_eq_right h, splittingAct]
    simp

/-- An additive endomorphism of the splitting module is determined by its values on $C$ and on the symbols
$x_\tau$, $\tau \neq 1$. -/
theorem splitting_ext {f g : SplittingCarrier C →+ SplittingCarrier C}
    (hC : ∀ c : C, f (c, 0) = g (c, 0))
    (hX : ∀ τ : G, τ ≠ 1 → f (splittingX C φ τ) = g (splittingX C φ τ)) : f = g := by
  refine AddMonoidHom.ext fun ⟨c, x⟩ => ?_
  have hcx : ((c, x) : SplittingCarrier C) = (c, 0) + (0, x) := by simp
  rw [hcx, map_add, map_add, hC]
  clear hcx
  congr 1
  induction x using Finsupp.induction_linear with
  | zero => simp only [Prod.mk_zero_zero, map_zero]
  | add a b ha hb =>
    have hab : ((0 : C), a + b) = ((0 : C), a) + (0, b) := by simp
    rw [hab, map_add, map_add, ha, hb]
  | single τ n =>
    have hτ : ((0 : C), Finsupp.single τ n) = n • splittingX C φ τ := by
      simp only [splittingX, τ.2, dite_false, Prod.smul_mk, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [zsmul_zero]
    rw [hτ, map_zsmul, map_zsmul, hX τ τ.2]

theorem splittingAct_one : splittingAct C φ 1 = AddMonoidHom.id _ := by
  apply splitting_ext C φ
  · intro c; simp
  · intro τ _
    rw [splittingAct_X, one_mul, splittingX_one, cocycles₂_map_one_fst φ τ]
    simp

theorem splittingAct_mul (σ τ : G) :
    splittingAct C φ (σ * τ) = (splittingAct C φ σ).comp (splittingAct C φ τ) := by
  apply splitting_ext C φ
  · intro c; simp [map_mul]
  · intro ρ _
    have hc := (mem_cocycles₂_iff (φ : G × G → C)).1 φ.2 σ τ ρ
    rw [AddMonoidHom.comp_apply, splittingAct_X C φ (σ * τ) ρ, splittingAct_X C φ τ ρ, map_add, map_sub,
      splittingAct_X C φ σ (τ * ρ), splittingAct_X C φ σ τ, splittingAct_inl, mul_assoc]
    ext
    · simp only [Prod.fst_add, Prod.fst_sub]
      have : (φ : G × G → C) (σ * τ, ρ) = C.ρ σ ((φ : G × G → C) (τ, ρ)) +
          (φ : G × G → C) (σ, τ * ρ) - (φ : G × G → C) (σ, τ) := by
        rw [← hc]; abel
      rw [this]; abel
    · simp only [Prod.snd_add, Prod.snd_sub]
      abel_nf

/-- The **splitting module** $C(\varphi)$ of a 2-cocycle $\varphi$ (p. 84): $G$ acts on $C$ as before and by
$\sigma x_\tau = x_{\sigma\tau} - x_\sigma + \varphi(\sigma, \tau)$ on the symbols. That this is an action is the
2-cocycle identity (`splittingAct_mul`); $1$ acts trivially since $\varphi(1, \tau) = \varphi(1, 1)$
(`splittingAct_one`). -/
@[kb "milne2020cft" "v4.03, Ch. II, §3, the splitting module C(φ), p. 84"]
noncomputable def splittingModule : Rep ℤ G :=
  Rep.of (({
      toFun := fun σ => (splittingAct C φ σ).toIntLinearMap
      map_one' := by ext x : 1; simp [splittingAct_one]
      map_mul' := fun σ τ => by ext x : 1; simp [splittingAct_mul] } :
    Representation ℤ G (SplittingCarrier C)))

@[simp] theorem splittingModule_ρ_X (σ τ : G) :
    (splittingModule C φ).ρ σ (splittingX C φ τ) =
      splittingX C φ (σ * τ) - splittingX C φ σ + ((φ : G × G → C) (σ, τ), 0) :=
  splittingAct_X C φ σ τ

@[simp] theorem splittingModule_ρ_inl (σ : G) (c : C) :
    (splittingModule C φ).ρ σ (c, 0) = (C.ρ σ c, 0) :=
  splittingAct_inl C φ σ c

end Splitting

/-! ## Proposition 3.2 -/

section Prop3_2

variable {G : Type} [Group G]

open scoped Classical in
/-- Restriction on $H_1$ for a subgroup $H$ of finite index (the restriction map on $H^{-2}_T$, p. 79): the map
$H_1(G, M) \to H_1(G, \operatorname{Coind}_H^G M) \simeq H_1(G, \operatorname{Ind}_H^G M) \simeq H_1(H, M)$
induced by $M \to \operatorname{Coind}_H^G M$, $m \mapsto (g \mapsto gm)$, Mathlib's `Rep.indCoindIso` and
Shapiro's lemma for homology `groupHomology.indIso` (Milne's construction of restriction in Example 1.27 (b),
transported to homology). -/
noncomputable def resH1 [DecidableEq G] (H : Subgroup G) [H.FiniteIndex] (M : Rep ℤ G) :
    groupHomology M 1 ⟶ groupHomology (res H.subtype M) 1 :=
  (groupHomology.functor ℤ G 1).map ((resCoindAdjunction ℤ H.subtype).unit.app M ≫
      (indCoindIso (res H.subtype M)).inv) ≫
    (groupHomology.indIso H (res H.subtype M) 1).hom

/-- **Proposition 3.2** (p. 79), as a named statement. Let $H$ be a subgroup of the finite group $G$. Under the
isomorphisms $H^{-2}_T(-, \mathbb Z) = H_1(-, \mathbb Z) \simeq (-)^{ab}$ (Mathlib's
`groupHomology.H1AddEquivOfIsTrivial`, with $G^{ab} \otimes \mathbb Z = G^{ab}$):
(a) corestriction $H_1(H, \mathbb Z) \to H_1(G, \mathbb Z)$ (the map induced by the inclusion, Mathlib's
`groupHomology.map H.subtype`) corresponds to the map $H^{ab} \to G^{ab}$ induced by the inclusion;
(b) restriction `resH1` corresponds to the transfer (Verlagerung) $G^{ab} \to H^{ab}$ (Mathlib's
`MonoidHom.transfer` of the abelianization map of $H$). Milne defers the proof to Weiss 1969, 3-5-5, 3-5-7. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 3.2, p. 79–80"]
structure Prop3_2 : Prop where
  cor : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (x : groupHomology (trivial ℤ H ℤ) 1),
    groupHomology.H1AddEquivOfIsTrivial (trivial ℤ G ℤ)
        (groupHomology.map H.subtype (𝟙 (res H.subtype (trivial ℤ G ℤ))) 1 x) =
      TensorProduct.map (Abelianization.map H.subtype).toAdditive.toIntLinearMap LinearMap.id
        (groupHomology.H1AddEquivOfIsTrivial (trivial ℤ H ℤ) x)
  res : ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (H : Subgroup G) (g : G),
    groupHomology.H1AddEquivOfIsTrivial (trivial ℤ H ℤ)
        (resH1 H (trivial ℤ G ℤ) ((groupHomology.H1AddEquivOfIsTrivial (trivial ℤ G ℤ)).symm
          (Additive.ofMul (Abelianization.of g) ⊗ₜ (1 : ℤ)))) =
      Additive.ofMul (MonoidHom.transfer (Abelianization.of : H →* Abelianization H) g) ⊗ₜ (1 : ℤ)

end Prop3_2

end NumberFieldKB.MilneCFT
