import NumberFieldKB.MilneCFT.Ch7.Basic
import NumberFieldKB.MilneCFT.Ch6.Splitting
import NumberFieldKB.MilneCFT.Ch7.Lemma45Aux

/-!
# Milne, *Class Field Theory*, Chapter VII §4: applications of the first inequality

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

* **Proposition 2.8** (`Prop2_8`, named statement; numbered in the book, missing from the audit's list):
  $\mathrm{Nm}_{L/K}\mathbb I_L$ contains an open subgroup of $\mathbb I_K$ (from local field theory: local norm groups
  are open, and unramified local norms are onto the units).
* **Lemma 4.5** (`lemma_4_5`): a solvable $L/K$ with a subgroup $D\subseteq\mathrm{Nm}(\mathbb I_L)$ such that
  $K^\times D$ is dense in $\mathbb I_K$ is trivial. Stated with the first inequality (Corollary 4.4 for cyclic
  extensions) and Proposition 2.8 as hypotheses (`FirstInequality`, `Prop2_8`).
* **Proposition 4.6** (`prop_4_6`) and **Proposition 4.7** (`prop_4_7`) (numbered, missing from the audit's list) and
  **Corollary 4.8** (`cor_4_8`): proved from the unconditional Chebotarev theorem of this library (Milne derives them
  from Lemma 4.5 to keep the proof of the reciprocity law free of analysis; Remark 4.9 notes the analytic route).
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K]

/-- **Proposition 2.8** (named statement; Milne, *CFT*, Chapter VII, p. 207): for every finite Galois extension $L/K$
of number fields, $\mathrm{Nm}_{L/K}\mathbb I_L$ contains an open subgroup of $\mathbb I_K$, and therefore is itself
open.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.GlobalNumberFields.isOpen_range_ideleNormMap`
(`TauCeti/NumberTheory/NumberField/Global/Ideles/Norm/Open.lean:118`) at Tau Ceti commit `7ed979dc`. Needed to apply
it here: Tau Ceti proves it for every finite extension of number fields, with no Galois hypothesis; one must identify
our idele group and idele norm map with Tau Ceti's. -/
@[kb "milne2020cft" "Ch. VII, Prop. 2.8 (input)"]
structure Prop2_8 : Prop where
  isOpen : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    IsOpen ((normIdeles K L : Subgroup (IdeleGroup (𝓞 K) K)) : Set (IdeleGroup (𝓞 K) K))

/-- **The first inequality** (Milne, *CFT*, Chapter VII, Corollary 4.4) as a hypothesis: for every cyclic extension
$L/K$, $(\mathbb I_K : K^\times\mathrm{Nm}(\mathbb I_L))\ge[L:K]$. It follows from Theorem 4.3 (`cor_4_4`). -/
def FirstInequality : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L], IsCyclic Gal(L/K) →
    (principalNormIdeles K L).FiniteIndex ∧ Module.finrank K L ≤ (principalNormIdeles K L).index

/-- **Lemma 4.5** (Milne, *CFT*, Chapter VII, p. 211): let $L/K$ be a finite Galois extension with solvable Galois
group. If there is a subgroup $D$ of $\mathbb I_K$ with (a) $D\subseteq\mathrm{Nm}_{L/K}\mathbb I_L$ and (b)
$K^\times\cdot D$ dense in $\mathbb I_K$, then $L = K$. Conditional on the first inequality and Proposition 2.8. -/
@[kb "milne2020cft" "Ch. VII, Lemma 4.5"]
theorem lemma_4_5 (h44 : FirstInequality K) (h28 : Prop2_8 K)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (hsolv : Group.IsSolvable Gal(L/K))
    (D : Subgroup (IdeleGroup (𝓞 K) K)) (hD : D ≤ normIdeles K L)
    (hdense : Dense ((IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D : Subgroup (IdeleGroup (𝓞 K) K)) :
      Set (IdeleGroup (𝓞 K) K))) :
    Module.finrank K L = 1 := by
  by_contra hne
  have hnt : Nontrivial Gal(L/K) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply hne
    rw [← IsGalois.card_aut_eq_finrank]
    exact Nat.card_unique
  have := hsolv
  obtain ⟨H, hHn, hHtop, hcyc⟩ := Lemma45Aux.exists_normal_cyclic_quotient Gal(L/K)
  let K' : IntermediateField K L := IntermediateField.fixedField H
  have : IsGalois K K' := IsGalois.of_fixedField_normal_subgroup H
  -- the cyclic quotient
  have hcycK' : IsCyclic Gal(K'/K) :=
    isCyclic_of_surjective (IsGalois.normalAutEquivQuotient H).toMonoidHom
      (IsGalois.normalAutEquivQuotient H).surjective
  -- norm inclusion
  have hle : normIdeles K L ≤ normIdeles K K' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨ideleNorm K' L x, Lemma45Aux.ideleNorm_comp x⟩
  -- principalNormIdeles K K' is everything
  have hopen : IsOpen ((principalNormIdeles K K' : Subgroup (IdeleGroup (𝓞 K) K)) :
      Set (IdeleGroup (𝓞 K) K)) :=
    Subgroup.isOpen_mono (le_sup_right : normIdeles K K' ≤ principalNormIdeles K K') (h28.isOpen K')
  have hdense' : Dense ((principalNormIdeles K K' : Subgroup (IdeleGroup (𝓞 K) K)) :
      Set (IdeleGroup (𝓞 K) K)) :=
    hdense.mono (SetLike.coe_subset_coe.mpr (sup_le_sup_left (hD.trans hle) _))
  have htop : principalNormIdeles K K' = ⊤ := by
    have hcl := (Subgroup.isClosed_of_isOpen _ hopen).closure_eq
    have := hdense'.closure_eq
    rw [hcl] at this
    exact Subgroup.coe_eq_univ.mp this
  have hidx : (principalNormIdeles K K').index = 1 := by rw [htop]; exact Subgroup.index_top
  obtain ⟨-, hfin⟩ := h44 K' hcycK'
  rw [hidx] at hfin
  -- but [K' : K] = [G : H] > 1
  have h1 : Module.finrank K K' = H.index := by
    rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (IsGalois.normalAutEquivQuotient H).symm.toEquiv,
      ← Subgroup.index_eq_card]
  have h2 : H.index ≠ 1 := fun h => hHtop (Subgroup.index_eq_one.mp h)
  have h3 : 0 < Module.finrank K K' := Module.finrank_pos
  omega

variable {K}
variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **Proposition 4.6** (Milne, *CFT*, Chapter VII, p. 211): if $L/K$ is a finite solvable extension and $L\ne K$, then
infinitely many primes of $K$ do not split completely in $L$. (True for every finite Galois extension; proved from
Chebotarev's density theorem: the split primes have density $1/[L:K] < 1$.) -/
@[kb "milne2020cft" "Ch. VII, Prop. 4.6"]
theorem prop_4_6 (_hsolv : Group.IsSolvable Gal(L/K)) (hL : 1 < Module.finrank K L) :
    (splitPrimes K L)ᶜ.Infinite := by
  intro hfin
  have h1 := HasDirichletDensity.compl (hasDirichletDensity_of_finite hfin)
  rw [compl_compl, sub_zero] at h1
  have h2 := HasDirichletDensity.unique h1 (splitPrimes_hasDirichletDensity_unconditional K L)
  have hn : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  rw [eq_div_iff hn.ne', one_mul] at h2
  have : (Module.finrank K L : ℝ) = 1 := h2
  exact absurd (by exact_mod_cast this : Module.finrank K L = 1) hL.ne'

/-- **Proposition 4.7** (Milne, *CFT*, Chapter VII, p. 212): for a finite solvable extension $L/K$ and a finite set
$T$ of primes containing those that ramify, the Frobenius elements $(\mathfrak P, L/K)$, $\mathfrak P\notin T$,
generate $\mathrm{Gal}(L/K)$. (Proved from Chebotarev: every element is such a Frobenius element.) -/
@[kb "milne2020cft" "Ch. VII, Prop. 4.7"]
theorem prop_4_7 (_hsolv : Group.IsSolvable Gal(L/K)) (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite) :
    Subgroup.closure {σ | ∃ (v : HeightOneSpectrum (𝓞 K)) (Q : v.asIdeal.primesOver (𝓞 L)),
      v ∉ T ∧ v ∈ unramifiedPrimes K L ∧ frobAt K L v Q = σ} = ⊤ := by
  refine eq_top_iff.mpr fun σ _ => Subgroup.subset_closure ?_
  obtain ⟨v, ⟨hv, Q, hQ⟩, hvT⟩ := ((setOf_frobAt_eq_infinite K L σ).sdiff hT).nonempty
  exact ⟨v, Q, hvT, hv, hQ⟩

/-- **Corollary 4.8** (Milne, *CFT*, Chapter VII, p. 212): for every abelian extension $L/K$ and finite set $S$ of
primes containing those that ramify, $\mathfrak p\mapsto(\mathfrak p, L/K) : I^S\to\mathrm{Gal}(L/K)$ is surjective.
The same statement as Chapter VI, Corollary 3.8 (`NumberFieldKB.MilneCFT.Ch6.cor_3_8`). -/
@[kb "milne2020cft" "Ch. VII, Cor. 4.8"]
theorem cor_4_8 (hab : ∀ σ τ : Gal(L/K), σ * τ = τ * σ) (m : Modulus K)
    (hm : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ unramifiedPrimes K L → v.asIdeal ∣ m.finite)
    (ψ : coprimeIdeals m →* Gal(L/K))
    (hψ : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) (Q : v.asIdeal.primesOver (𝓞 L)),
      ψ (coprimePrime m v hv) = frobAt K L v Q) :
    Function.Surjective ψ :=
  Ch6.cor_3_8 hab m hm ψ hψ

end NumberFieldKB.MilneCFT.Ch7
