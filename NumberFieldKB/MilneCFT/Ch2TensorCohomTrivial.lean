import NumberFieldKB.MilneCFT.Ch2Remark312
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.DirectedUnion
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Tensor products with cohomologically trivial modules over a finite p-group

Let `G` be a finite `p`-group; every representation is an integral representation of `G`, and `⊗` is the tensor
product with the diagonal action.

* `isZero_tateCohomology_tensor_of_pTorsion`: if `V` is killed by `p` and `ℤ / p ⊗ A` has no Tate cohomology, then
  `V ⊗ A` has no Tate cohomology. Proof: a nonzero finite `V` killed by `p` has a nonzero fixed vector
  (`exists_fixed_ne_zero`), which spans a copy of `ℤ / p` that is a `ℤ`-direct summand, so induction on the order of
  `V` along `0 → ℤ / p ⊗ A → V ⊗ A → (V / ⟨v⟩) ⊗ A → 0` works; a general `V` is the directed union of its finite
  subrepresentations (`orbitSpan`) and Tate cohomology commutes with directed unions.
* `isZero_tateCohomology_tensor_of_torsionFree`: if `W` has no `ℤ`-torsion and no Tate cohomology, then `M ⊗ W` has
  no Tate cohomology for every `M`. Proof: multiplication by `p` on `M` factors as a surjection onto its image
  followed by an injection; the kernel and the cokernel are killed by `p` and stay exact after `- ⊗ W` since `W` is
  flat, so the previous lemma shows that multiplication by `p` is injective on `Ĥⁿ(G, M ⊗ W)`; but this group is
  killed by `|G| = p^k`.

This is the `p`-group case of the tensor lemma `TensorCohomTrivialLemma` (Milne, Class Field Theory, II, Remark 3.12).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Rep Limits MonoidalCategory
open TauCeti TauCeti.TateCohomology
open scoped TensorProduct

namespace NumberFieldKB.MilneCFT

section Fixed

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]

/-- A nonzero finite representation of a finite `p`-group killed by `p` has a nonzero fixed vector. -/
theorem exists_fixed_ne_zero (hG : IsPGroup p G) (V : Rep ℤ G) [Finite V.V]
    (hV : ∀ x : V.V, p • x = 0) [Nontrivial V.V] : ∃ v : V.V, v ≠ 0 ∧ ∀ g, V.ρ g v = v := by
  classical
  letI : MulAction G V.V :=
    { smul := fun g v => V.ρ g v
      one_smul := fun v => by change V.ρ 1 v = v; simp
      mul_smul := fun g h v => by change V.ρ (g * h) v = V.ρ g (V.ρ h v); simp }
  letI : Module (ZMod p) V.V := AddCommGroup.zmodModule hV
  haveI := Fintype.ofFinite V.V
  have h1 := hG.card_modEq_card_fixedPoints V.V
  have hcard : Nat.card V.V = p ^ Module.finrank (ZMod p) V.V := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hr : Module.finrank (ZMod p) V.V ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hcard
    exact (Finite.one_lt_card (α := V.V)).ne' hcard
  have hdvd : p ∣ Nat.card V.V := by
    rw [hcard]; exact dvd_pow_self p hr
  have hdvd2 : p ∣ Nat.card (MulAction.fixedPoints G V.V) :=
    (Nat.modEq_zero_iff_dvd.1 (h1.symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd)))
  by_contra hcon
  push Not at hcon
  have h0 : (0 : V.V) ∈ MulAction.fixedPoints G V.V := fun g => by
    change V.ρ g 0 = 0
    simp
  have hsub : Subsingleton (MulAction.fixedPoints G V.V) := by
    refine ⟨fun a b => ?_⟩
    have key : ∀ c : MulAction.fixedPoints G V.V, c.1 = 0 := fun c => by
      by_contra h
      obtain ⟨g, hg⟩ := hcon c.1 h
      exact hg (c.2 g)
    exact Subtype.ext ((key a).trans (key b).symm)
  haveI : Nonempty (MulAction.fixedPoints G V.V) := ⟨⟨0, h0⟩⟩
  have hle : Nat.card (MulAction.fixedPoints G V.V) ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub
  have hpos := Nat.card_pos (α := MulAction.fixedPoints G V.V)
  have := Nat.le_of_dvd hpos hdvd2
  have := (Fact.out : p.Prime).two_le
  omega

end Fixed

section Split

/-- An additive map between abelian groups carrying arbitrary integer module structures is integer linear. -/
def intLinearOfAddHom {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B]
    (f : A →+ B) : A →ₗ[ℤ] B where
  toFun := f
  map_add' := map_add f
  map_smul' m x := by
    have e1 := Int.cast_smul_eq_zsmul ℤ m x
    have e2 := Int.cast_smul_eq_zsmul ℤ m (f x)
    rw [Int.cast_id] at e1 e2
    rw [RingHom.id_apply, e1, e2]
    exact map_zsmul f m x

@[simp] theorem intLinearOfAddHom_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℤ A]
    [Module ℤ B] (f : A →+ B) (x : A) : intLinearOfAddHom f x = f x := rfl

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]

/-- An injective additive map into a group killed by a prime `p` has an additive retraction (such a group is a
vector space over the field with `p` elements). -/
theorem exists_addMonoidHom_leftInverse {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (hB : ∀ x : B, p • x = 0) (f : A →+ B) (hf : Function.Injective f) :
    ∃ r : B →+ A, ∀ a, r (f a) = a := by
  have hA : ∀ a : A, p • a = 0 := fun a => hf (by rw [map_nsmul, hB, map_zero])
  letI : Module (ZMod p) A := AddCommGroup.zmodModule hA
  letI : Module (ZMod p) B := AddCommGroup.zmodModule hB
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (f.toZModLinearMap p)
    (LinearMap.ker_eq_bot.2 hf)
  exact ⟨r.toAddMonoidHom, fun a => by simpa using LinearMap.congr_fun hr a⟩

/-- An injective morphism of representations into a representation killed by `p` has a `ℤ`-linear retraction. -/
theorem exists_linear_leftInverse {T V : Rep ℤ G} (hV : ∀ x : V.V, p • x = 0) (i : T ⟶ V)
    (hi : Function.Injective i.hom) :
    ∃ r : V.V →ₗ[ℤ] T.V, Function.LeftInverse r i.hom := by
  obtain ⟨r, hr⟩ := exists_addMonoidHom_leftInverse hV i.hom.toLinearMap.toAddMonoidHom hi
  exact ⟨intLinearOfAddHom r, fun a => hr a⟩

end Split

section Finite

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]

variable (p G) in
/-- The group `ℤ / p` with the trivial action. -/
abbrev zmodTrivial : Rep ℤ G := Rep.trivial ℤ G (ZMod p)

/-- The morphism from `ℤ / p` (trivial action) sending `1` to a fixed vector `v` killed by `p`. -/
noncomputable def fixedHom {V : Rep ℤ G} (v : V.V) (hv : p • v = 0) (hfix : ∀ g, V.ρ g v = v) :
    zmodTrivial p G ⟶ V :=
  Rep.ofHom ⟨intLinearOfAddHom (ZMod.lift p ⟨zmultiplesHom V.V v, by simpa using hv⟩), fun g => by
    ext x
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    simp [ZMod.lift_coe, hfix]⟩

theorem fixedHom_apply_intCast {V : Rep ℤ G} (v : V.V) (hv : p • v = 0) (hfix : ∀ g, V.ρ g v = v)
    (n : ℤ) : (fixedHom v hv hfix).hom (n : ZMod p) = n • v := by
  simp [fixedHom, ZMod.lift_coe]

theorem fixedHom_injective {V : Rep ℤ G} (v : V.V) (hv : p • v = 0) (hfix : ∀ g, V.ρ g v = v)
    (hne : v ≠ 0) : Function.Injective (fixedHom v hv hfix).hom := by
  intro x y hxy
  have h0 : (fixedHom v hv hfix).hom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (x - y)
  rw [← hn, fixedHom_apply_intCast] at h0
  have hord : addOrderOf v = p := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 (addOrderOf_dvd_of_nsmul_eq_zero hv) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) hne
    · exact h
  have hdvd : ((p : ℕ) : ℤ) ∣ n := by
    rw [← hord]; exact addOrderOf_dvd_iff_zsmul_eq_zero.2 h0
  have : (n : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).2 hdvd
  rw [hn] at this
  exact sub_eq_zero.1 this

/-- **Tensor lemma for finite modules.** -/
theorem isZero_tateCohomology_tensor_of_finite (hG : IsPGroup p G) (A : Rep ℤ G)
    (hA : ∀ n, IsZero (tateCohomology (zmodTrivial p G ⊗ A) n)) :
    ∀ (N : ℕ) (V : Rep ℤ G), Nat.card V.V = N → Finite V.V → (∀ x : V.V, p • x = 0) →
      ∀ n, IsZero (tateCohomology (V ⊗ A) n) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro V hN hfin hV n
  by_cases hsub : Subsingleton V.V
  · have : IsZero (V ⊗ A) := by
      rw [Rep.isZero_iff]
      change Subsingleton (V.V ⊗[ℤ] A.V)
      infer_instance
    exact (tateCohomologyFunctor n).map_isZero this
  · have hnt : Nontrivial V.V := not_subsingleton_iff_nontrivial.1 hsub
    obtain ⟨v, hv0, hfix⟩ := exists_fixed_ne_zero hG V hV
    have hvp : p • v = 0 := hV v
    set i := fixedHom v hvp hfix with hi
    have hinj := fixedHom_injective v hvp hfix hv0
    haveI : Mono i := (Rep.mono_iff_injective i).2 hinj
    have hS := TauCeti.cokernelSequence_shortExact i
    obtain ⟨r, hr⟩ := exists_linear_leftInverse hV i hinj
    have hS' := shortExact_map_tensorRight_of_leftInverse hS.exact A
      (S := ShortComplex.cokernelSequence i) hr
    have hg : Function.Surjective (fun x : V.V => (ShortComplex.cokernelSequence i).g.hom x) :=
      (Rep.epi_iff_surjective _).1 hS.epi_g
    have hfin3 : Finite (ShortComplex.cokernelSequence i).X₃.V := Finite.of_surjective (α := V.V) _ hg
    have hkill3 : ∀ x : (ShortComplex.cokernelSequence i).X₃.V, p • x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := hg x
      change p • (ShortComplex.cokernelSequence i).g.hom y = 0
      have hy : p • y = 0 := hV y
      have h := map_nsmul (ShortComplex.cokernelSequence i).g.hom.toLinearMap p y
      rw [hy] at h
      exact h.symm.trans (map_zero _)
    have hlt : Nat.card (ShortComplex.cokernelSequence i).X₃.V < N := by
      rw [← hN]
      refine lt_of_le_of_ne (Nat.card_le_card_of_surjective (α := V.V) _ hg) fun heq => ?_
      have hb : Function.Bijective (fun x : V.V => (ShortComplex.cokernelSequence i).g.hom x) :=
        hg.bijective_of_nat_card_le heq.ge
      have hz : (ShortComplex.cokernelSequence i).g.hom (i.hom 1) = 0 := by
        have := congrArg (fun h => h.hom (1 : ZMod p)) (ShortComplex.cokernelSequence i).zero
        rw [Rep.hom_comp, Rep.zero_hom] at this
        exact this
      have h1 : i.hom 1 = 0 := hb.1 (hz.trans (map_zero _).symm)
      have h2 : i.hom (1 : ZMod p) = v := by
        simpa using fixedHom_apply_intCast v hvp hfix 1
      exact hv0 (h2.symm.trans h1)
    exact isZero_X₂_of_isZero_X₁_of_isZero_X₃ hS' n (hA n) (ih _ hlt _ rfl hfin3 hkill3 n)

end Finite

section Union

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]

/-- The subgroup generated by the orbits of the elements of a finite set `s`. -/
def orbitSpan (V : Rep ℤ G) (s : Finset V.V) : Submodule ℤ V.V :=
  Submodule.span ℤ {w | ∃ g : G, ∃ v ∈ s, w = V.ρ g v}

theorem orbitSpan_le_comap (V : Rep ℤ G) (s : Finset V.V) (g : G) :
    orbitSpan V s ≤ (orbitSpan V s).comap (V.ρ g) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨h, v, hv, rfl⟩
  refine Submodule.subset_span ⟨g * h, v, hv, ?_⟩
  simp

theorem mem_orbitSpan (V : Rep ℤ G) (s : Finset V.V) {v : V.V} (hv : v ∈ s) : v ∈ orbitSpan V s :=
  Submodule.subset_span ⟨1, v, hv, by simp⟩

theorem finite_orbitSpan (V : Rep ℤ G) (hV : ∀ x : V.V, p • x = 0) (s : Finset V.V) :
    Finite (orbitSpan V s) := by
  classical
  haveI : Module.Finite ℤ (orbitSpan V s) := by
    unfold orbitSpan
    suffices hs : Set.Finite {w | ∃ g : G, ∃ v ∈ s, w = V.ρ g v} by
      have h := Module.Finite.span_of_finite (M := V.V) ℤ hs
      convert h
      exact Subsingleton.elim _ _
    have : {w | ∃ g : G, ∃ v ∈ s, w = V.ρ g v} =
        (fun gv : G × V.V => V.ρ gv.1 gv.2) '' ((Set.univ : Set G) ×ˢ (s : Set V.V)) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_univ, Finset.mem_coe, true_and,
        Prod.exists]
      constructor
      · rintro ⟨g, v, hv, rfl⟩; exact ⟨g, v, hv, rfl⟩
      · rintro ⟨g, v, hv, rfl⟩; exact ⟨g, v, hv, rfl⟩
    rw [this]
    exact (Set.toFinite _).image _
  refine Module.finite_of_fg_torsion (orbitSpan V s) ?_
  intro x
  refine ⟨⟨(p : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)⟩, ?_⟩
  apply Subtype.ext
  simpa using hV x

/-- **Tensor lemma for a finite `p`-group, torsion factor on the left.** Let `G` be a finite `p`-group, `V` a
representation of `G` killed by `p` and `A` a representation such that `ℤ / p ⊗ A` (trivial action on `ℤ / p`) has
no Tate cohomology. Then `V ⊗ A` has no Tate cohomology.

The hypothesis on `A` holds, for instance, when `A` has no `ℤ`-torsion and no Tate cohomology
(`isZero_tateCohomology_zmodTrivial_tensor`). Only the cohomology of `G` itself is used, not that of its
subgroups. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 3.12, p. 85 (tensor lemma, p-group case)"]
theorem isZero_tateCohomology_tensor_of_pTorsion (hG : IsPGroup p G) (V A : Rep ℤ G)
    (hV : ∀ x : V.V, p • x = 0)
    (hA : ∀ n, IsZero (tateCohomology (zmodTrivial p G ⊗ A) n)) (n : ℤ) :
    IsZero (tateCohomology (V ⊗ A) n) := by
  classical
  let sub : Finset V.V → Rep ℤ G := fun s =>
    Rep.subrepresentation V (orbitSpan V s) (orbitSpan_le_comap V s)
  let ι : ∀ s, sub s ⟶ V := fun s => Rep.subtype V (orbitSpan V s) (orbitSpan_le_comap V s)
  have hιinj : ∀ s, Function.Injective (ι s).hom := fun s => Subtype.val_injective
  have hsubkill : ∀ s (x : (sub s).V), p • x = 0 := fun s x => Subtype.ext (by
    rw [AddSubmonoidClass.coe_nsmul]
    exact hV x.1)
  have hfinsub : ∀ s, Finite (sub s).V := fun s => finite_orbitSpan V hV s
  have hfi : ∀ s, Function.Injective (ι s ▷ A).hom := by
    intro s
    obtain ⟨r, hr⟩ := exists_linear_leftInverse hV (ι s) (hιinj s)
    haveI : Mono (ι s) := (Rep.mono_iff_injective _).2 (hιinj s)
    have hS := TauCeti.cokernelSequence_shortExact (ι s)
    have hS' := shortExact_map_tensorRight_of_leftInverse hS.exact A
      (S := ShortComplex.cokernelSequence (ι s)) hr
    exact (Rep.mono_iff_injective _).1 hS'.mono_f
  have hclaim : ∀ z : (V ⊗ A : Rep ℤ G).V, ∃ s0 : Finset V.V, ∀ t, s0 ⊆ t → z ∈ Set.range (ι t ▷ A).hom := by
    intro z
    refine TensorProduct.inductionOn (motive := fun z : V.V ⊗[ℤ] A.V =>
      ∃ s0 : Finset V.V, ∀ t, s0 ⊆ t → z ∈ Set.range (ι t ▷ A).hom) z ?_ ?_
    · intro v a
      refine ⟨{v}, fun t ht => ?_⟩
      let w : (sub t).V := ⟨v, mem_orbitSpan V t (ht (Finset.mem_singleton_self v))⟩
      exact ⟨@TensorProduct.tmul ℤ _ (sub t).V A.V _ _ (sub t).hV2 A.hV2 w a, rfl⟩
    · rintro x y ⟨s0, h0⟩ ⟨s1, h1⟩
      refine ⟨s0 ∪ s1, fun t ht => ?_⟩
      obtain ⟨y0, hy0⟩ := h0 t (fun a ha => ht (Finset.mem_union_left _ ha))
      obtain ⟨y1, hy1⟩ := h1 t (fun a ha => ht (Finset.mem_union_right _ ha))
      exact ⟨y0 + y1, by rw [map_add, hy0, hy1]⟩
  choose s0 hs0 using hclaim
  have hdir : ∀ s : Finset (V ⊗ A : Rep ℤ G).V, ∃ t : Finset V.V, ∀ m ∈ s, m ∈ Set.range (ι t ▷ A).hom :=
    fun s => ⟨s.biUnion s0, fun m hm => hs0 m _ (Finset.subset_biUnion_of_mem s0 hm)⟩
  refine ModuleCat.isZero_of_iff_subsingleton.2 (subsingleton_of_forall_eq 0 fun x => ?_)
  obtain ⟨t, y, rfl⟩ := exists_tateCohomologyFunctor_map_eq (fun t => ι t ▷ A) hfi hdir n x
  have hy : y = 0 := (ModuleCat.subsingleton_of_isZero (isZero_tateCohomology_tensor_of_finite hG A hA
    _ (sub t) rfl (hfinsub t) (hsubkill t) n)).elim _ _
  rw [hy]
  exact map_zero _

end Union


section TorsionFree

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]

variable (p G) in
/-- Multiplication by `p` on the integers with the trivial action. -/
noncomputable def mulPTrivial : Rep.trivial ℤ G ℤ ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom ⟨intLinearOfAddHom (AddMonoidHom.mulLeft (p : ℤ)), fun g => by ext; simp⟩

variable (p G) in
/-- Reduction modulo `p` from the integers with the trivial action to `ℤ / p` with the trivial action. -/
noncomputable def reduceTrivial : Rep.trivial ℤ G ℤ ⟶ zmodTrivial p G :=
  Rep.ofHom ⟨intLinearOfAddHom (Int.castAddHom (ZMod p)), fun g => by ext; simp⟩

variable (p G) in
/-- The short exact sequence `0 → ℤ → ℤ → ℤ / p → 0` of representations with trivial action. -/
noncomputable def reduceSeq : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (mulPTrivial p G) (reduceTrivial p G) (by
    ext
    simp [mulPTrivial, reduceTrivial])

theorem reduceSeq_shortExact : (reduceSeq p G).ShortExact := by
  haveI : Mono (reduceSeq p G).f := by
    rw [Rep.mono_iff_injective]
    have key : ∀ a b : ℤ, (p : ℤ) * a = p * b → a = b := fun a b h =>
      mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero) h
    intro (a : ℤ) (b : ℤ) h
    exact key a b h
  haveI : Epi (reduceSeq p G).g := by
    rw [Rep.epi_iff_surjective]
    intro (y : ZMod p)
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y
    exact ⟨n, rfl⟩
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [Rep.exact_iff_function_exact]
  intro (y : ℤ)
  constructor
  · intro h
    have h' : ((y : ℤ) : ZMod p) = 0 := h
    obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 h'
    exact ⟨c, hc.symm⟩
  · rintro ⟨(c : ℤ), rfl⟩
    show (((p : ℤ) * c : ℤ) : ZMod p) = 0
    simp

theorem flat_of_torsionFree (W : Rep ℤ G) (hW : ∀ (m : ℤ) (w : W.V), m • w = 0 → m = 0 ∨ w = 0) :
    Module.Flat ℤ W.V := by
  haveI : Module.IsTorsionFree ℤ W.V := ⟨fun r hr a b hab => by
    have h0 : r ≠ 0 := hr.ne_zero
    have e1 := Int.cast_smul_eq_zsmul ℤ r a
    have e2 := Int.cast_smul_eq_zsmul ℤ r b
    rw [Int.cast_id] at e1 e2
    have : r • (a - b) = 0 := by
      rw [zsmul_sub, ← e1, ← e2]
      exact sub_eq_zero.2 hab
    rcases hW r _ this with h | h
    · exact absurd h h0
    · exact sub_eq_zero.1 h⟩
  infer_instance

/-- If `W` has no torsion and no Tate cohomology, then `ℤ / p ⊗ W` has no Tate cohomology. -/
theorem isZero_tateCohomology_zmodTrivial_tensor (W : Rep ℤ G)
    (hW : ∀ (m : ℤ) (w : W.V), m • w = 0 → m = 0 ∨ w = 0)
    (hWc : ∀ n, IsZero (tateCohomology W n)) (n : ℤ) :
    IsZero (tateCohomology (zmodTrivial p G ⊗ W) n) := by
  haveI := flat_of_torsionFree W hW
  have hS := shortExact_map_tensorRight_of_flat (reduceSeq_shortExact (p := p) (G := G)) W
  have h2 : ∀ m, IsZero (tateCohomology (Rep.trivial ℤ G ℤ ⊗ W) m) := fun m =>
    ((tateCohomologyFunctor m).mapIso (λ_ W)).isZero_iff.2 (hWc m)
  exact isZero_X₃_of_isZero_X₂_of_isZero_X₁ hS n (n + 1) rfl (h2 n) (h2 (n + 1))

variable (M : Rep ℤ G) in
theorem mulP_hom (y : M.V) :
    (((p : ℕ) • 𝟙 M : M ⟶ M)).hom y = p • y := by
  rw [Rep.nsmul_hom]
  rfl

theorem eq_zero_of_injective_nsmul {B : Type*} [AddCommGroup B] (p k : ℕ)
    (hinj : Function.Injective (fun x : B => p • x)) (x : B) (hx : p ^ k • x = 0) : x = 0 := by
  induction k generalizing x with
  | zero => simpa using hx
  | succ k ih =>
    refine ih x (hinj ?_)
    simp only [smul_zero]
    rw [← mul_smul, ← pow_succ']
    exact hx

/-- The multiplication by `p` on the Tate cohomology of `M ⊗ W` is the map induced by `φ ▷ W`. -/
theorem tateCohomology_map_whiskerRight_nsmul_id (M W : Rep ℤ G) (n : ℕ) (m : ℤ)
    (x : tateCohomology (M ⊗ W) m) :
    ((tateCohomologyFunctor m).map ((n • 𝟙 M : M ⟶ M) ▷ W)).hom x = n • x := by
  have h : (tensorRight W ⋙ tateCohomologyFunctor m).map (n • 𝟙 M) =
      n • (tensorRight W ⋙ tateCohomologyFunctor m).map (𝟙 M) := Functor.map_nsmul _
  rw [CategoryTheory.Functor.map_id] at h
  have h3 : (tateCohomologyFunctor m).map ((n • 𝟙 M : M ⟶ M) ▷ W) = n • 𝟙 _ := h
  rw [h3]
  simp

/-- **Tensor lemma for a finite `p`-group, torsion-free factor on the right.** Let `G` be a finite `p`-group and `W`
a representation without `ℤ`-torsion whose Tate cohomology vanishes in every degree. Then `M ⊗ W` has no Tate
cohomology, for every representation `M` (no condition on `M`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 3.12, p. 85 (tensor lemma, p-group case)"]
theorem isZero_tateCohomology_tensor_of_torsionFree (hG : IsPGroup p G) (W : Rep ℤ G)
    (hW : ∀ (m : ℤ) (w : W.V), m • w = 0 → m = 0 ∨ w = 0)
    (hWc : ∀ n, IsZero (tateCohomology W n)) (M : Rep ℤ G) (n : ℤ) :
    IsZero (tateCohomology (M ⊗ W) n) := by
  classical
  haveI := flat_of_torsionFree W hW
  let φ : M ⟶ M := (p : ℕ) • 𝟙 M
  let ψ := Abelian.factorThruImage φ
  let ι := Abelian.image.ι φ
  have hfac : ψ ≫ ι = φ := Abelian.image.fac φ
  have hS1 := TauCeti.kernelSequence_shortExact ψ
  have hS2 := TauCeti.cokernelSequence_shortExact ι
  have hS1' := shortExact_map_tensorRight_of_flat hS1 W
  have hS2' := shortExact_map_tensorRight_of_flat hS2 W
  have hφ : ∀ y : M.V, φ.hom y = p • y := fun y => by
    change ((p : ℕ) • 𝟙 M : M ⟶ M).hom y = _
    rw [Rep.nsmul_hom]
    rfl
  have hφι : ∀ b : M.V, φ.hom b = ι.hom (ψ.hom b) := fun b =>
    (congrArg (fun h => h.hom b) hfac).symm
  -- the kernel and the cokernel are killed by `p`
  have hK : ∀ x : (ShortComplex.kernelSequence ψ).X₁.V, p • x = 0 := by
    have hmono : Function.Injective (ShortComplex.kernelSequence ψ).f.hom :=
      (Rep.mono_iff_injective _).1 hS1.mono_f
    intro x
    refine hmono ?_
    obtain ⟨a, hadef⟩ : ∃ a : M.V, a = (ShortComplex.kernelSequence ψ).f.hom x := ⟨_, rfl⟩
    have hz : ψ.hom a = 0 := by
      have := congrArg (fun h => h.hom x) (ShortComplex.kernelSequence ψ).zero
      rw [Rep.hom_comp, Rep.zero_hom] at this
      rw [hadef]
      exact this
    have ha : p • a = 0 := by
      rw [← hφ, hφι, hz]
      exact map_zero _
    have h1 : (ShortComplex.kernelSequence ψ).f.hom (p • x) = p • a := by
      rw [hadef]
      exact map_nsmul (ShortComplex.kernelSequence ψ).f.hom.toLinearMap p x
    rw [h1, ha]
    exact (map_zero _).symm
  have hQ : ∀ y : (ShortComplex.cokernelSequence ι).X₃.V, p • y = 0 := by
    have hg : Function.Surjective (fun x : M.V => (ShortComplex.cokernelSequence ι).g.hom x) :=
      (Rep.epi_iff_surjective _).1 hS2.epi_g
    intro y
    obtain ⟨b, rfl⟩ := hg y
    have hz : (ShortComplex.cokernelSequence ι).g.hom (ι.hom (ψ.hom b)) = 0 := by
      have := congrArg (fun h => h.hom (ψ.hom b)) (ShortComplex.cokernelSequence ι).zero
      rw [Rep.hom_comp, Rep.zero_hom] at this
      exact this
    have h1 : p • (ShortComplex.cokernelSequence ι).g.hom b =
        (ShortComplex.cokernelSequence ι).g.hom (p • b) :=
      (map_nsmul (ShortComplex.cokernelSequence ι).g.hom.toLinearMap p b).symm
    change p • (ShortComplex.cokernelSequence ι).g.hom b = 0
    rw [h1, ← hφ, hφι]
    exact hz
  have hA := isZero_tateCohomology_zmodTrivial_tensor (p := p) W hW hWc
  have hKz := isZero_tateCohomology_tensor_of_pTorsion hG (ShortComplex.kernelSequence ψ).X₁ W hK hA
  have hQz := isZero_tateCohomology_tensor_of_pTorsion hG (ShortComplex.cokernelSequence ι).X₃ W hQ hA
  have h1 : Function.Injective ((tateCohomologyFunctor n).map (ψ ▷ W)).hom := by
    rw [← ModuleCat.mono_iff_injective]
    exact (_root_.TateCohomology.exact₂ hS1' n).mono_g ((hKz n).eq_of_src _ _)
  have h2 : Function.Injective ((tateCohomologyFunctor n).map (ι ▷ W)).hom :=
    map_f_injective_of_isZero_X₃ hS2' (n - 1) n (sub_add_cancel n 1) (hQz (n - 1))
  have hinj : Function.Injective (fun x : tateCohomology (M ⊗ W) n => p • x) := by
    have : (fun x : tateCohomology (M ⊗ W) n => p • x) =
        ((tateCohomologyFunctor n).map (ι ▷ W)).hom ∘ ((tateCohomologyFunctor n).map (ψ ▷ W)).hom :=
      funext fun x => by
        rw [← tateCohomology_map_whiskerRight_nsmul_id M W p n x]
        change _ = ((tateCohomologyFunctor n).map (ψ ▷ W) ≫ (tateCohomologyFunctor n).map (ι ▷ W)).hom x
        rw [← Functor.map_comp, ← comp_whiskerRight]
        exact congrArg (fun f => ((tateCohomologyFunctor n).map (f ▷ W)).hom x) hfac.symm
    rw [this]
    exact h2.comp h1
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  refine ModuleCat.isZero_of_iff_subsingleton.2 (subsingleton_of_forall_eq 0 fun x =>
    eq_zero_of_injective_nsmul p k hinj x ?_)
  rw [← hk]
  exact natCard_nsmul_eq_zero x

end TorsionFree

end NumberFieldKB.MilneCFT

