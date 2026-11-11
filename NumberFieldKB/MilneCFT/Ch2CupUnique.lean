import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Cup
import NumberFieldKB.MilneCFT.Ch2Induced

/-!
# Milne, *Class Field Theory*, Chapter II §1: uniqueness of cup products

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

We prove the uniqueness half of Proposition 1.38 (p. 73): any two families of cup-product pairings satisfying
(a)–(d) (`CupProductFamily`) have the same pairings. Following Milne, the proof is by dimension shifting
(Lemma 1.37 / Remark 1.13): the sequence (15) `0 → N → Ind N → N^* → 0` of `Ch2Induced.lean` splits over `ℤ`, so
it stays exact after `M ⊗ -` and `- ⊗ N` (`seq15_tensorLeft`, `seq15_tensorRight`); every class of
$H^{s+1}(G, N)$ is a connecting image from $H^s(G, N^*)$ (`delta_surjective`). In bidegree $(0, s)$ the pairing
is forced to be induced by $n \mapsto m \otimes n$ (`cup_zero_left`), and the general case follows by shifting `r`.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits MonoidalCategory

variable {G : Type} [Group G]

/-- A short complex of `G`-modules is short exact as soon as its underlying maps of abelian groups are injective,
surjective and exact in the middle. -/
lemma shortExact_of_forget₂ {S : ShortComplex (Rep ℤ G)}
    (hinj : Function.Injective S.f.hom) (hsurj : Function.Surjective S.g.hom)
    (hex : Function.Exact S.f.hom S.g.hom) : S.ShortExact := by
  have h1 : Mono S.f := (Rep.mono_iff_injective _).2 hinj
  have h2 : Epi S.g := (Rep.epi_iff_surjective _).2 hsurj
  refine ShortComplex.ShortExact.mk' ?_ h1 h2
  rw [← ShortComplex.exact_map_iff_of_faithful S (forget₂ (Rep ℤ G) (ModuleCat ℤ))]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact (LinearMap.exact_iff.1 hex).symm

/-- The underlying maps of a short exact sequence of `G`-modules are exact. -/
lemma functionExact_of_shortExact {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact) :
    Function.Exact S.f.hom S.g.hom := by
  have h := hS.exact.map (forget₂ (Rep ℤ G) (ModuleCat ℤ))
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  exact LinearMap.exact_iff.2 h.symm

/-- If `S` is short exact and `S.f` has a ℤ-linear left inverse, `M ⊗ -` keeps `S` short exact. -/
lemma tensorLeft_shortExact {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact) (M : Rep ℤ G)
    (r : S.X₂ →ₗ[ℤ] S.X₁) (hr : ∀ x, r (S.f.hom x) = x) :
    (S.map (tensorLeft M)).ShortExact := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  refine shortExact_of_forget₂ ?_ ?_ ?_
  · intro a b hab
    have : (LinearMap.lTensor M r) ((LinearMap.lTensor M S.f.hom) a) =
        (LinearMap.lTensor M r) ((LinearMap.lTensor M S.f.hom) b) := congrArg _ hab
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp] at this
    have e : r ∘ₗ (S.f.hom : S.X₁ →ₗ[ℤ] S.X₂) = LinearMap.id := LinearMap.ext hr
    rwa [e, LinearMap.lTensor_id] at this
  · exact LinearMap.lTensor_surjective M hg
  · exact lTensor_exact M (functionExact_of_shortExact hS) hg

/-- If `S` is short exact and `S.f` has a ℤ-linear left inverse, `- ⊗ M` keeps `S` short exact. -/
lemma tensorRight_shortExact {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact) (M : Rep ℤ G)
    (r : S.X₂ →ₗ[ℤ] S.X₁) (hr : ∀ x, r (S.f.hom x) = x) :
    (S.map (tensorRight M)).ShortExact := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  refine shortExact_of_forget₂ ?_ ?_ ?_
  · intro a b hab
    have : (LinearMap.rTensor M r) ((LinearMap.rTensor M S.f.hom) a) =
        (LinearMap.rTensor M r) ((LinearMap.rTensor M S.f.hom) b) := congrArg _ hab
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp] at this
    have e : r ∘ₗ (S.f.hom : S.X₁ →ₗ[ℤ] S.X₂) = LinearMap.id := LinearMap.ext hr
    rwa [e, LinearMap.rTensor_id] at this
  · exact LinearMap.rTensor_surjective M hg
  · exact rTensor_exact M (functionExact_of_shortExact hS) hg

set_option backward.isDefEq.respectTransparency false in
/-- The ℤ-linear retraction `f ↦ f 1` of `toIndG`, i.e. of the first map of the sequence (15). -/
noncomputable def indRetraction (N : Rep ℤ G) : (seq15 N).X₂ →ₗ[ℤ] (seq15 N).X₁ where
  toFun f := (f : indG G N).1 1
  map_add' _ _ := rfl
  map_smul' _ _ := by simp; rfl

set_option backward.isDefEq.respectTransparency false in
lemma indRetraction_toIndG (N : Rep ℤ G) (x : (seq15 N).X₁) :
    indRetraction N ((seq15 N).f.hom x) = x := by
  change N.ρ 1 x = x
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The sequence (15) stays short exact after `M ⊗ -` (it is split over ℤ). -/
lemma seq15_tensorLeft (M N : Rep ℤ G) : ((seq15 N).map (tensorLeft M)).ShortExact :=
  tensorLeft_shortExact (seq15_shortExact N) M (indRetraction N) (indRetraction_toIndG N)

set_option backward.isDefEq.respectTransparency false in
/-- The sequence (15) stays short exact after `- ⊗ M` (it is split over ℤ). -/
lemma seq15_tensorRight (M N : Rep ℤ G) : ((seq15 N).map (tensorRight M)).ShortExact :=
  tensorRight_shortExact (seq15_shortExact N) M (indRetraction N) (indRetraction_toIndG N)

set_option backward.isDefEq.respectTransparency false in
/-- Generic-coefficient version of `tensorLeftOf`. -/
noncomputable def tensorLeftOfAux {k : Type} [CommRing k] {M : Rep k G} (m : M.ρ.invariants)
    (N : Rep k G) : N ⟶ M ⊗ N :=
  Rep.ofHom ⟨TensorProduct.mk k M N (m : M), fun g => by
    refine LinearMap.ext fun n => ?_
    change (m : M) ⊗ₜ[k] N.ρ g n = TensorProduct.map (M.ρ g) (N.ρ g) ((m : M) ⊗ₜ[k] n)
    rw [TensorProduct.map_tmul, m.2 g]⟩

/-- The `G`-map `N ⟶ M ⊗ N`, `n ↦ m ⊗ n`, for an invariant element `m` of `M` (diagonal action on `M ⊗ N`). -/
noncomputable def tensorLeftOf {M : Rep ℤ G} (m : M.ρ.invariants) (N : Rep ℤ G) : N ⟶ M ⊗ N :=
  tensorLeftOfAux m N

set_option backward.isDefEq.respectTransparency false in
lemma tensorLeftOf_apply {M : Rep ℤ G} (m : M.ρ.invariants) (N : Rep ℤ G) (n : N) :
    (tensorLeftOf m N).hom n = rtmul (A := M) (B := N) (m : M) n := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `n ↦ m ⊗ n` as a morphism of short complexes `seq15 N ⟶ (seq15 N).map (tensorLeft M)`. -/
noncomputable def seq15Hom {M : Rep ℤ G} (m : M.ρ.invariants) (N : Rep ℤ G) :
    seq15 N ⟶ (seq15 N).map (tensorLeft M) where
  τ₁ := tensorLeftOf m N
  τ₂ := tensorLeftOf m (indG G N)
  τ₃ := tensorLeftOf m (mStar N)
  comm₁₂ := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
    rfl
  comm₂₃ := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
    rfl

/-- Dimension shifting (Remark 1.13): every class of $H^{s+1}(G, N)$ is the connecting image of a class of
$H^s(G, N^*)$ for the sequence (15). -/
lemma delta_surjective (N : Rep ℤ G) (s : ℕ) :
    Function.Surjective (δ (seq15_shortExact N) s (s + 1) rfl).hom := by
  rcases s with _ | s
  · exact (ModuleCat.epi_iff_surjective _).1 (remark_1_13 (seq15_shortExact N) fun r hr =>
      cor_1_12 (M := indG G N) ⟨N, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩ r hr).1
  · have := remark_1_13_mStar N (s + 1) (by omega)
    exact (ModuleCat.epi_iff_surjective _).1 inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- **Bidegree $(0, s)$ is forced** (the first step of the uniqueness proof of Proposition 1.38, p. 73): for any
cup-product family, $m \cup y$ with $m \in M^G = H^0(G, M)$ is the image of $y$ under the map
$H^s(G, N) \to H^s(G, M \otimes N)$ induced by $n \mapsto m \otimes n$. Proof: degree $0$ is axiom (b), and the
step $s \to s + 1$ is dimension shifting along (15) using axiom (d) and naturality of $\delta$. -/
theorem cup_zero_left (c : CupProductFamily G) (M : Rep ℤ G) (m : M.ρ.invariants) (s : ℕ) :
    ∀ (N : Rep ℤ G) (y : groupCohomology N s),
      c.cup M N 0 s s (zero_add s) ((H0Iso M).inv m) y =
        (groupCohomology.functor ℤ G s).map (tensorLeftOf m N) y := by
  induction s with
  | zero =>
    intro N y
    obtain ⟨n, rfl⟩ : ∃ n, y = (H0Iso N).inv n := ⟨(H0Iso N).hom y, by simp⟩
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback (H0Iso (M ⊗ N)).hom)
    rw [c.zero M N m n]
    have := congrArg (fun φ => φ.hom ((H0Iso N).inv n))
      (map_id_comp_H0Iso_hom (tensorLeftOf m N))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    refine Eq.trans ?_ this.symm
    simp only [Iso.inv_hom_id_apply]
    rfl
  | succ s ih =>
    intro N y
    obtain ⟨y', rfl⟩ := delta_surjective N s y
    have h1 := c.delta_right M (seq15 N) (seq15_shortExact N) (seq15_tensorLeft M N) 0 s s
      (zero_add s) ((H0Iso M).inv m) y'
    refine h1.trans ?_
    rw [pow_zero, one_smul]
    have h2 : c.cup M (seq15 N).X₃ 0 s s (zero_add s) ((H0Iso M).inv m) y' =
        (groupCohomology.functor ℤ G s).map (tensorLeftOf m (mStar N)) y' := ih (mStar N) y'
    rw [h2]
    have h3 := congrArg (fun φ => φ.hom y')
      (δ_naturality (seq15_shortExact N) (seq15_tensorLeft M N) (seq15Hom m N) s (s + 1) rfl)
    exact h3.symm

/-- **Proposition 1.38, uniqueness** (p. 73): any two families of cup-product pairings satisfying (a)–(d) agree.
Milne's proof: by dimension shifting (Lemma 1.37). Here: for $r = 0$ the pairing is forced by `cup_zero_left`;
for $r + 1$ write the first argument as $\delta x'$ for (15) of $M$ and use axiom (c) (`delta_left`) with the
inductive hypothesis for $r$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.38, uniqueness, p. 73"]
theorem cupProductFamily_cup_unique (c₁ c₂ : CupProductFamily G) : c₁.cup = c₂.cup := by
  have key : ∀ (r : ℕ) (M N : Rep ℤ G) (s n : ℕ) (h : r + s = n) (x : groupCohomology M r)
      (y : groupCohomology N s), c₁.cup M N r s n h x y = c₂.cup M N r s n h x y := by
    intro r
    induction r with
    | zero =>
      intro M N s n h x y
      have hn : s = n := by omega
      subst hn
      obtain ⟨m, rfl⟩ : ∃ m, x = (H0Iso M).inv m := ⟨(H0Iso M).hom x, by simp⟩
      rw [cup_zero_left c₁ M m s N y, cup_zero_left c₂ M m s N y]
    | succ r ih =>
      intro M N s n h x y
      obtain ⟨x', rfl⟩ := delta_surjective M r x
      obtain rfl : n = r + s + 1 := by omega
      have h1 := c₁.delta_left (seq15 M) (seq15_shortExact M) N (seq15_tensorRight N M) r s
        (r + s) rfl x' y
      have h2 := c₂.delta_left (seq15 M) (seq15_shortExact M) N (seq15_tensorRight N M) r s
        (r + s) rfl x' y
      refine h1.trans (Eq.trans ?_ h2.symm)
      exact congrArg _ (ih (seq15 M).X₃ N s (r + s) rfl x' y)
  funext M N r s n h
  exact AddMonoidHom.ext fun x => AddMonoidHom.ext fun y => key r M N s n h x y

end NumberFieldKB.MilneCFT
