import NumberFieldKB.MilneANT.Ch8Dedekind

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: proof of the Frobenius form of Dedekind's theorem

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

Proves the named statement `DedekindFrobenius` (the content of Milne's proof of Theorem 8.23): reduction modulo
$\mathfrak P$ maps the roots of $f$ in $L$ injectively (as $f \bmod \mathfrak p$ is squarefree) onto the roots of
$f \bmod \mathfrak p$ in the residue field of $\mathfrak P$, a Frobenius element acts on reduced roots as
$x \mapsto x^{N\mathfrak p}$, and Corollary 8.22 reads off the cycle type.
-/

open NumberField IsDedekindDomain Polynomial UniqueFactorizationMonoid
open scoped Classical

namespace NumberFieldKB.MilneANT

noncomputable section

/-- The cycle type of a permutation, fixed points included, is invariant under transport along a bijection. -/
theorem parts_partition_congr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) (h : ∀ a, e (σ a) = τ (e a)) :
    σ.partition.parts = τ.partition.parts := by
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  let f : α ≃ {b : β // True} := e.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm
  have hτ : σ.extendDomain f = τ := by
    ext b
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [show e a = (f a : β) from rfl, Equiv.Perm.extendDomain_apply_image]
    exact h a
  have hc : σ.cycleType = τ.cycleType := by
    rw [← hτ]; exact (Equiv.Perm.cycleType_extendDomain f).symm
  rw [Equiv.Perm.parts_partition, Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType,
    ← Equiv.Perm.sum_cycleType, hc, hcard]

/-- Two injective maps with the same range, intertwining permutations with the same self-map of the target,
give permutations with the same cycle type. -/
theorem parts_partition_congr_range {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (ι : α → γ) (κ : β → γ)
    (hι : Function.Injective ι) (hκ : Function.Injective κ) (hr : Set.range ι = Set.range κ)
    (F : γ → γ) (σ : Equiv.Perm α) (τ : Equiv.Perm β) (hσ : ∀ a, ι (σ a) = F (ι a))
    (hτ : ∀ b, κ (τ b) = F (κ b)) :
    σ.partition.parts = τ.partition.parts := by
  have hb : ∀ a, ∃ b, κ b = ι a := fun a => by
    have : ι a ∈ Set.range κ := hr ▸ ⟨a, rfl⟩
    exact this
  choose e he using hb
  have einj : Function.Injective e := fun a a' h => hι (by rw [← he a, ← he a', h])
  have hbi : ∀ b, ∃ a, e a = b := fun b => by
    have : κ b ∈ Set.range ι := hr ▸ ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := this
    refine ⟨a, hκ ?_⟩
    rw [he, ha]
  refine parts_partition_congr (Equiv.ofBijective e ⟨einj, hbi⟩) σ τ fun a => ?_
  apply hκ
  show κ (e (σ a)) = κ (τ (e a))
  rw [he, hτ, he, hσ]

/-- **Frobenius cycle type over a finite field** (from Corollary 8.22): if the roots of a monic separable `g`
over a finite field `k` are listed injectively in an extension `ℓ` in which `g` splits, and `σ` permutes the list
by `x ↦ x ^ #k`, then the cycle type of `σ` (fixed points included) is the multiset of degrees of the irreducible
factors of `g`. -/
theorem frob_parts_of_roots {k ℓ : Type*} [Field k] [Fintype k] [Field ℓ] [Algebra k ℓ] (g : k[X])
    (hg : g.Monic) (hs : g.Separable) (hsp : (g.map (algebraMap k ℓ)).Splits)
    {α : Type*} [Fintype α] [DecidableEq α] (ρ : α → ℓ) (hρ : Function.Injective ρ) (hr : Set.range ρ = g.rootSet ℓ)
    (σ : Equiv.Perm α) (hσ : ∀ a, ρ (σ a) = ρ a ^ Fintype.card k) :
    σ.partition.parts = (normalizedFactors g).map natDegree := by
  rw [← cor_8_22 k g hg hs]
  set ι : g.SplittingField →ₐ[k] ℓ := SplittingField.lift g hsp with hι
  have hmaps : ∀ b : g.rootSet g.SplittingField, ι b ∈ g.rootSet ℓ := fun b => by
    have hb := (mem_rootSet'.1 b.2)
    refine mem_rootSet'.2 ⟨?_, ?_⟩
    · exact (Polynomial.map_ne_zero_iff (algebraMap k ℓ).injective).2 hg.ne_zero
    · rw [aeval_algHom_apply, hb.2, map_zero]
  let κ' : g.rootSet g.SplittingField → g.rootSet ℓ := fun b => ⟨ι b, hmaps b⟩
  have hκ'inj : Function.Injective κ' := fun a b h =>
    Subtype.ext (ι.injective (congrArg Subtype.val h))
  have hcard : Fintype.card (g.rootSet g.SplittingField) = Fintype.card (g.rootSet ℓ) := by
    rw [card_rootSet_eq_natDegree hs (SplittingField.splits g), card_rootSet_eq_natDegree hs hsp]
  have hκ'bij : Function.Bijective κ' := (Fintype.bijective_iff_injective_and_card κ').2 ⟨hκ'inj, hcard⟩
  refine parts_partition_congr_range ρ (fun b : g.rootSet g.SplittingField => ι b) hρ
    (fun a b h => hκ'inj (Subtype.ext h)) ?_ (fun x => x ^ Fintype.card k) σ
    (galPerm g (FiniteField.frobeniusAlgEquivOfAlgebraic k g.SplittingField)) hσ ?_
  · rw [hr]
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := hκ'bij.2 ⟨x, hx⟩
      exact ⟨b, congrArg Subtype.val hb⟩
    · rintro ⟨b, rfl⟩
      exact hmaps b
  · intro b
    show ι (FiniteField.frobeniusAlgEquivOfAlgebraic k g.SplittingField b) = ι b ^ Fintype.card k
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    simp

section Abstract

set_option linter.unusedSectionVars false

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A root in `L` of a monic polynomial over `𝓞 K` is integral over `ℤ`. -/
theorem isIntegral_of_mem_roots (f : (𝓞 K)[X]) (hf : f.Monic) {x : L}
    (hx : x ∈ (f.map (algebraMap (𝓞 K) L)).roots) : IsIntegral ℤ x := by
  have h0 : (f.map (algebraMap (𝓞 K) L)) ≠ 0 := (hf.map _).ne_zero
  have hx' := (mem_roots h0).1 hx
  have : IsIntegral (𝓞 K) x := ⟨f, hf, by
    rw [eval₂_eq_eval_map]; exact hx'⟩
  exact isIntegral_trans (R := ℤ) (A := 𝓞 K) x this

/-- A monic polynomial over `𝓞 K` that splits in `L` splits over `𝓞 L` into linear factors whose roots are the
roots in `L`. -/
theorem exists_lift_roots (f : (𝓞 K)[X]) (hf : f.Monic)
    (hsp : (f.map (algebraMap (𝓞 K) L)).Splits) :
    ∃ M : Multiset (𝓞 L), f.map (algebraMap (𝓞 K) (𝓞 L)) = (M.map fun y => X - C y).prod ∧
      M.map (algebraMap (𝓞 L) L) = (f.map (algebraMap (𝓞 K) L)).roots := by
  set m := (f.map (algebraMap (𝓞 K) L)).roots with hm
  let lift : L → 𝓞 L := fun x => if h : IsIntegral ℤ x then ⟨x, h⟩ else 0
  have hlift : ∀ x ∈ m, algebraMap (𝓞 L) L (lift x) = x := fun x hx => by
    simp [lift, isIntegral_of_mem_roots f hf hx]; rfl
  refine ⟨m.map lift, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap (𝓞 L) L) (IsFractionRing.injective (𝓞 L) L)
    have h1 := hsp.eq_prod_roots_of_monic (hf.map _)
    calc (f.map (algebraMap (𝓞 K) (𝓞 L))).map (algebraMap (𝓞 L) L)
        = f.map (algebraMap (𝓞 K) L) := by
          rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      _ = (m.map (X - C ·)).prod := h1
      _ = _ := by
          rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
          congr 1
          apply Multiset.map_congr rfl
          intro x hx
          simp [hlift x hx]
  · rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id' m]
    exact Multiset.map_congr rfl hlift

/-- **Reduction of the roots** (abstract form of the proof of Theorem 8.23): let $f \in \mathcal O_K[X]$ be monic and
split in $L$, let $\psi_K, \psi_L$ be compatible ring homomorphisms from $\mathcal O_K, \mathcal O_L$ to a finite field
$k$ and an extension $\ell$ of it, with $f$ squarefree over $k$, and let $\sigma$ act as $x \mapsto x^{\#k}$ after
$\psi_L$. Then $\sigma$, as a permutation of the roots of $f$ in $L$, has the cycle type of the factorization of
$f$ over $k$. -/
theorem dedekind_abstract [IsGalois K L] (f : (𝓞 K)[X]) (hf : f.Monic)
    (hsp : (f.map (algebraMap (𝓞 K) L)).Splits)
    {k ℓ : Type} [Field k] [Fintype k] [Field ℓ] [Algebra k ℓ] (ψK : 𝓞 K →+* k) (ψL : 𝓞 L →+* ℓ)
    (hcomm : ∀ a, ψL (algebraMap (𝓞 K) (𝓞 L) a) = algebraMap k ℓ (ψK a))
    (hsq : Squarefree (f.map ψK)) (σ : Gal(L/K))
    (hfrob : ∀ y : 𝓞 L, ψL (σ • y) = ψL y ^ Fintype.card k) :
    (rootPerm (f.map (algebraMap (𝓞 K) K)) (E := L) σ).partition.parts =
      (normalizedFactors (f.map ψK)).map natDegree := by
  obtain ⟨M, hMf, hMm⟩ := exists_lift_roots f hf hsp
  set m := (f.map (algebraMap (𝓞 K) L)).roots with hm
  set g := f.map ψK with hg
  have hgmonic : g.Monic := hf.map _
  have hgsep : g.Separable := (PerfectField.separable_iff_squarefree).2 hsq
  have hĝ : g.map (algebraMap k ℓ) = ((M.map ψL).map fun c => X - C c).prod := by
    have : g.map (algebraMap k ℓ) = (f.map (algebraMap (𝓞 K) (𝓞 L))).map ψL := by
      rw [hg, Polynomial.map_map, Polynomial.map_map]
      congr 1
      exact RingHom.ext fun a => (hcomm a).symm
    rw [this, hMf, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro y _
    simp
  have hsplit : (g.map (algebraMap k ℓ)).Splits := by
    rw [hĝ]
    exact Splits.multisetProd (fun p hp => by
      obtain ⟨c, _, rfl⟩ := Multiset.mem_map.1 hp
      exact Splits.X_sub_C c)
  have hroots_ℓ : ∀ β, β ∈ g.rootSet ℓ ↔ β ∈ M.map ψL := by
    intro β
    rw [rootSet_def, aroots_def, hĝ, roots_multiset_prod_X_sub_C]
    simp
  have hroots_L : ∀ x, x ∈ (f.map (algebraMap (𝓞 K) K)).rootSet L ↔ x ∈ m := by
    intro x
    rw [rootSet_def, aroots_def, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    simp only [Finset.mem_coe, Multiset.mem_toFinset, hm]
  have hex : ∀ x : (f.map (algebraMap (𝓞 K) K)).rootSet L,
      ∃ y ∈ M, algebraMap (𝓞 L) L y = x := fun x =>
    Multiset.mem_map.1 (hMm ▸ (hroots_L x).1 x.2)
  choose y hyM hy using hex
  let ρ : (f.map (algebraMap (𝓞 K) K)).rootSet L → ℓ := fun x => ψL (y x)
  have hyinj : ∀ a b : 𝓞 L, algebraMap (𝓞 L) L a = algebraMap (𝓞 L) L b → a = b :=
    fun a b h => IsFractionRing.injective (𝓞 L) L h
  have hinj : Function.Injective ρ := by
    intro x x' h
    by_contra hne
    have hyne : y x ≠ y x' := fun h' => hne (Subtype.ext (by rw [← hy x, ← hy x', h']))
    have h1 : y x' ∈ M.erase (y x) := (Multiset.mem_erase_of_ne (Ne.symm hyne)).2 (hyM x')
    obtain ⟨N, hN⟩ := Multiset.exists_cons_of_mem h1
    have hM : M = y x ::ₘ y x' ::ₘ N := by rw [← hN, Multiset.cons_erase (hyM x)]
    have hdvd : (X - C (ρ x)) * (X - C (ρ x)) ∣ g.map (algebraMap k ℓ) := by
      rw [hĝ, hM]
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have e : ψL (y x') = ρ x := h.symm
      rw [e]
      exact mul_dvd_mul_left _ (dvd_mul_right _ _)
    exact not_isUnit_X_sub_C _ (hgsep.map.squarefree _ hdvd)
  have hrange : Set.range ρ = g.rootSet ℓ := by
    ext β
    rw [hroots_ℓ]
    constructor
    · rintro ⟨x, rfl⟩
      exact Multiset.mem_map_of_mem _ (hyM x)
    · intro hβ
      obtain ⟨y0, hy0, rfl⟩ := Multiset.mem_map.1 hβ
      have hx : algebraMap (𝓞 L) L y0 ∈ (f.map (algebraMap (𝓞 K) K)).rootSet L := by
        rw [hroots_L, ← hMm]
        exact Multiset.mem_map_of_mem _ hy0
      refine ⟨⟨_, hx⟩, ?_⟩
      show ψL (y ⟨_, hx⟩) = ψL y0
      rw [hyinj _ _ (hy ⟨_, hx⟩)]
  have hσ : ∀ x, ρ (rootPerm (f.map (algebraMap (𝓞 K) K)) (E := L) σ x) = ρ x ^ Fintype.card k := by
    intro x
    have : y (rootPerm (f.map (algebraMap (𝓞 K) K)) (E := L) σ x) = σ • y x := by
      apply hyinj
      rw [hy]
      show σ • (x : L) = _
      rw [← hy x]
      rfl
    show ψL (y _) = ψL (y x) ^ _
    rw [this, hfrob]
  exact frob_parts_of_roots g hgmonic hgsep hsplit ρ hinj hrange _ hσ

end Abstract

/-- **`DedekindFrobenius` holds** (Milne, proof of Theorem 8.23). -/
@[kb "milne2020ant" "v3.08, Thm. 8.23 (proof), p. 145"]
theorem dedekindFrobenius : DedekindFrobenius := by
  refine ⟨?_⟩
  intro K L _ _ _ _ _ _ f hf hsp 𝔭 hsq P _ _ σ hσ
  have h𝔭 : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have hover : 𝔭.asIdeal = P.comap (algebraMap (𝓞 K) (𝓞 L)) := Ideal.LiesOver.over
  let _ : Fintype 𝔭.asIdeal.ResidueField := Fintype.ofFinite _
  let _ : Algebra 𝔭.asIdeal.ResidueField P.ResidueField :=
    (Ideal.ResidueField.map 𝔭.asIdeal P (algebraMap (𝓞 K) (𝓞 L)) hover).toAlgebra
  have hcard : Fintype.card 𝔭.asIdeal.ResidueField = Nat.card (𝓞 K ⧸ P.under (𝓞 K)) := by
    rw [← Nat.card_eq_fintype_card, ← Ideal.LiesOver.over (p := 𝔭.asIdeal) (P := P)]
    exact (Nat.card_congr (Equiv.ofBijective _ 𝔭.asIdeal.bijective_algebraMap_quotient_residueField)).symm
  refine dedekind_abstract f hf hsp (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField)
    (algebraMap (𝓞 L) P.ResidueField) ?_ hsq σ ?_
  · intro a
    exact (Ideal.ResidueField.map_algebraMap 𝔭.asIdeal P (algebraMap (𝓞 K) (𝓞 L)) hover a).symm
  · intro y
    have h1 := congrArg (algebraMap (𝓞 L ⧸ P) P.ResidueField) (AlgHom.IsArithFrobAt.mk_apply hσ y)
    rw [map_pow, Ideal.algebraMap_quotient_residueField_mk,
      Ideal.algebraMap_quotient_residueField_mk] at h1
    rw [hcard]
    exact h1

end

end NumberFieldKB.MilneANT
