import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Polynomial.Roots
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, VII.§3, Lemma 4, third assertion (converse), conditional on duality

Weil (VII.§3, Lemma 4, p. 115): if $G$ is compact and commutative and all its characters have finite order, then $G$
is totally disconnected (the open subgroups form a basis of neighbourhoods of $1$). Weil's proof: $G$ is the dual of
the discrete group $G^*$, and it is then the projective limit of finite groups. Mathlib has no Pontryagin duality.

The one fact used from duality theory is that **the characters of a compact group separate points** (a consequence of
Pontryagin duality, or of the Peter–Weyl theorem). It is taken here as a named input, `CharactersSeparatePoints G`
(a cited result, not proved here; it is not the conclusion: it says nothing about open subgroups). Given it, the
conclusion follows without duality:

* **`weil_VII_3_lemma4_converse`**: if $G$ is a compact group whose characters (continuous morphisms into
  $\mathbb C^\times$) separate points and all have finite order, then every neighbourhood of $1$ contains an open
  subgroup. (Commutativity is not needed for this deduction.)

*Proof.* The kernel of a character of finite order is open (its values lie in the finite set of $n$-th roots of $1$, so
$\chi^{-1}(1)$ is the preimage of a small disc around $1$). For an open neighbourhood $U$ of $1$, the compact set
$G\setminus U$ is covered by the open sets $\{x:\chi_g(x)\ne1\}$, $g\notin U$, where $\chi_g(g)\ne1$; a finite subcover
gives finitely many characters, and the intersection of their kernels is an open subgroup contained in $U$.
-/

open Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable (G : Type*) [Group G] [TopologicalSpace G]

/-- **Named input** (Pontryagin duality, or the Peter–Weyl theorem, for a compact group $G$): the continuous
morphisms $G\to\mathbb C^\times$ separate the points of $G$. Not proved here. -/
structure CharactersSeparatePoints : Prop where
  separate : ∀ g : G, g ≠ 1 → ∃ χ : G →* ℂˣ, Continuous χ ∧ χ g ≠ 1

variable {G}

/-- The kernel of a continuous morphism into $\mathbb C^\times$ of finite order is open. -/
theorem isOpen_ker_of_pow_eq_one (χ : G →* ℂˣ) (hχ : Continuous χ) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ g, χ g ^ n = 1) : IsOpen (χ.ker : Set G) := by
  -- the n-th roots of unity other than 1 form a finite set not containing 1
  set S : Finset ℂ := (Polynomial.nthRoots n (1 : ℂ)).toFinset.erase 1
  have hcl : IsClosed ((Units.val : ℂˣ → ℂ) ⁻¹' (S : Set ℂ)) :=
    (S.finite_toSet.isClosed).preimage Units.continuous_val
  have hker : (χ.ker : Set G) = (χ ⁻¹' ((Units.val : ℂˣ → ℂ) ⁻¹' (S : Set ℂ)))ᶜ := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_compl_iff, Set.mem_preimage,
      S, Finset.mem_erase, Multiset.mem_toFinset, ne_eq]
    constructor
    · intro h; simp [h]
    · intro h
      by_contra h1
      apply h
      refine ⟨fun h2 => h1 (Units.ext h2), ?_⟩
      rw [Polynomial.mem_nthRoots hn]
      have := congrArg Units.val (hpow g)
      simpa using this
  rw [hker]
  exact (hcl.preimage hχ).isOpen_compl

/-- **Weil, VII.§3, Lemma 4, third assertion**, conditional on `CharactersSeparatePoints`: a compact group all of
whose characters have finite order has a basis of neighbourhoods of $1$ made of open subgroups. -/
@[kb "weil1973bnt" "Ch. VII, §3, Lemma 4, third assertion (conditional on characters separating points)"]
theorem weil_VII_3_lemma4_converse [CompactSpace G] (hsep : CharactersSeparatePoints G)
    (hfin : ∀ χ : G →* ℂˣ, Continuous χ → ∃ n : ℕ, 0 < n ∧ ∀ g, χ g ^ n = 1)
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) : ∃ H : OpenSubgroup G, (H : Set G) ⊆ U := by
  obtain ⟨V, hVU, hVo, hV1⟩ := mem_nhds_iff.mp hU
  -- for each g outside V, a character with χ g ≠ 1
  have hchoice : ∀ g : (Vᶜ : Set G), ∃ χ : G →* ℂˣ, Continuous χ ∧ χ g ≠ 1 := fun g =>
    hsep.separate g (fun h => g.2 (h ▸ hV1))
  choose χ hχc hχg using hchoice
  have hcpt : IsCompact (Vᶜ : Set G) := hVo.isClosed_compl.isCompact
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover (fun g : (Vᶜ : Set G) => {x | χ g x ≠ 1})
    (fun g => (isOpen_ne_fun (hχc g) continuous_const))
    (fun g hg => Set.mem_iUnion.mpr ⟨⟨g, hg⟩, hχg ⟨g, hg⟩⟩)
  -- each kernel is open
  have hopen : ∀ g, IsOpen ((χ g).ker : Set G) := fun g => by
    obtain ⟨n, hn, hpow⟩ := hfin (χ g) (hχc g)
    exact isOpen_ker_of_pow_eq_one (χ g) (hχc g) hn hpow
  let H : Subgroup G := ⨅ g ∈ t, (χ g).ker
  have hHopen : IsOpen (H : Set G) := by
    have : (H : Set G) = ⋂ g ∈ t, ((χ g).ker : Set G) := by
      simp [H, Subgroup.coe_iInf]
    rw [this]
    exact isOpen_biInter_finset fun g _ => hopen g
  refine ⟨⟨H, hHopen⟩, fun x hx => hVU ?_⟩
  by_contra hxV
  obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp (ht hxV)
  have : x ∈ (χ g).ker := by
    have hx' : x ∈ H := hx
    exact (Subgroup.mem_iInf.mp hx' g |> Subgroup.mem_iInf.mp) hg
  exact hxg this

end NumberFieldKB.WeilBNT
