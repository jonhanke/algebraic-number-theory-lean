import NumberFieldKB.MilneCFT.Ch5Artin
import NumberFieldKB.HeckeCharacter.Basic
import NumberFieldKB.Ideles.Norm
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Milne, *Class Field Theory*, Chapter V: items already in Mathlib or in this library

Citation file for J. S. Milne, *Class Field Theory*, v4.03 (2020), `milne2020cft`, Chapter V. Convention as in
`NumberFieldKB/MilneANT/ProseCite.lean`: a declaration whose statement is Milne's is tagged directly with
`attribute [kb ...]` (a comment names the item and any difference); otherwise a short restating theorem is proved.

* 1.9–1.12 (properties of the Frobenius element): the library's proofs of Milne, *ANT*, 8.14–8.17
  (`NumberFieldKB.MilneANT.item_8_14_*`, `item_8_15`, `item_8_16`, `item_8_17`), and the sentence after 1.12
  ($\mathfrak p$ splits in $L_1L_2$ iff it splits in $L_1$ and in $L_2$: `MilneANT.splitPrimes_sup`).
* Definitions in prose: primes of a number field, decomposition group, Frobenius element, principal Dirichlet
  character, topological group, idèle group, idèle class group, content, finite idèles, Hecke characters.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

/-! ## 1.9–1.12 -/

-- 1.9: D(τP) = τ D(P) τ⁻¹ (Mathlib's `MulAction.stabilizer_smul_eq_stabilizer_map_conj`).
attribute [kb "milne2020cft" "Ch. V, 1.9 (D(τP) = τD(P)τ⁻¹)"] MilneANT.item_8_14_stabilizer
-- 1.9: (τP, L/K) = τ (P, L/K) τ⁻¹ (Mathlib's `IsArithFrobAt.conj`).
attribute [kb "milne2020cft" "Ch. V, 1.9 ((τP, L/K) = τ(P, L/K)τ⁻¹)"] MilneANT.item_8_14_frob
-- After 1.9: the Frobenius elements of the primes above p form a conjugacy class (p, L/K).
attribute [kb "milne2020cft" "Ch. V, §1, p. 153 ((p, L/K) is a conjugacy class)"] MilneANT.item_8_14_conjClass
-- After 1.9: for L/K abelian, (P, L/K) depends only on p.
attribute [kb "milne2020cft" "Ch. V, §1, p. 153 ((p, L/K) for abelian L/K)"] MilneANT.item_8_14_abelian
-- 1.10: (Q, M/L) = (Q, M/K)^{f(P/p)}.
attribute [kb "milne2020cft" "Ch. V, 1.10"] MilneANT.item_8_15
-- 1.11: (Q, M/K)|_L = (P, L/K) for L/K Galois.
attribute [kb "milne2020cft" "Ch. V, 1.11"] MilneANT.item_8_16
-- The injective map Gal(L₁L₂/K) → Gal(L₁/K) × Gal(L₂/K) before 1.12, and 1.12.
attribute [kb "milne2020cft" "Ch. V, §1, p. 154 (Gal(L₁L₂/K) → Gal(L₁/K) × Gal(L₂/K) is injective)"]
  MilneANT.item_8_17_injective
attribute [kb "milne2020cft" "Ch. V, 1.12"] MilneANT.item_8_17
-- After 1.12: p splits completely in L₁L₂ iff it splits completely in L₁ and in L₂.
attribute [kb "milne2020cft" "Ch. V, §1, p. 154 (p splits in L₁L₂ iff in L₁ and L₂)"] MilneANT.splitPrimes_sup

/-! ## Definitions in prose -/

-- Primes of a number field (p. 147): the finite primes are the nonzero prime ideals of 𝓞_K, the infinite primes
-- the real embeddings and the conjugate pairs of complex embeddings. Two types, no common type of all primes.
attribute [kb "milne2020cft" "Ch. V, §1, p. 147 (finite primes)"] IsDedekindDomain.HeightOneSpectrum
attribute [kb "milne2020cft" "Ch. V, §1, p. 147 (infinite primes)"] NumberField.InfinitePlace

/-- **The decomposition group** $D(\mathfrak P) = \{\sigma \in G : \sigma\mathfrak P = \mathfrak P\}$ (Milne, *CFT*, V, §1,
p. 152): Mathlib's stabilizer `MulAction.stabilizer` for the action of $G$ on ideals. -/
@[kb "milne2020cft" "Ch. V, §1, p. 152 (the decomposition group D(P))"]
theorem mem_decompositionGroup_iff (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (P : Ideal (𝓞 L)) (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) P ↔ σ • P = P :=
  MulAction.mem_stabilizer_iff

/-- **The Frobenius element** $(\mathfrak P, L/K)$ (Milne, *CFT*, V, §1, p. 153): for $\mathfrak P$ unramified over
$\mathfrak p$ it is the unique $\sigma \in G$ with (a) $\sigma \in D(\mathfrak P)$ and (b) $\sigma\alpha \equiv \alpha^q
\bmod \mathfrak P$ for all $\alpha \in \mathcal O_L$, $q = N\mathfrak p$ (Mathlib's `IsArithFrobAt`; the library's
`Chebotarev.frobAt`). -/
@[kb "milne2020cft" "Ch. V, §1, p. 153 (the Frobenius element (P, L/K))"]
theorem frobenius_existsUnique (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : 𝔭 ∈ unramifiedPrimes K L)
    (Q : 𝔭.asIdeal.primesOver (𝓞 L)) :
    ∃! σ : Gal(L/K), σ ∈ MulAction.stabilizer Gal(L/K) Q.1 ∧ IsArithFrobAt (𝓞 K) σ Q.1 := by
  have := Q.2.1
  refine ⟨frobAt K L 𝔭 Q, ⟨(isArithFrobAt_frobAt K L 𝔭 Q).mem_stabilizer, isArithFrobAt_frobAt K L 𝔭 Q⟩,
    fun σ hσ => (frobAt_eq_of_isArithFrobAt K L h𝔭 Q hσ.2).symm⟩

/-- **The principal Dirichlet character** $\chi_0$ modulo $m$ (Milne, *CFT*, V, §2, p. 154): the trivial character,
equal to $1$ on the integers prime to $m$ (Mathlib's `1 : DirichletCharacter ℂ m`). -/
@[kb "milne2020cft" "Ch. V, §2, p. 154 (principal Dirichlet character)"]
theorem principalDirichletCharacter_apply (m : ℕ) (n : ℕ) (hn : n.Coprime m) :
    (1 : DirichletCharacter ℂ m) n = 1 :=
  MulChar.one_apply ((ZMod.isUnit_iff_coprime n m).mpr hn)

-- Topological group (p. 169): multiplication and inversion continuous. Mathlib's `IsTopologicalGroup`.
attribute [kb "milne2020cft" "Ch. V, §4, p. 169 (topological group)"] IsTopologicalGroup

-- The idèle group (p. 169): Milne's restricted product of the K_v^× with the restricted product topology.
-- Mathlib's `IdeleGroup` is the unit group of the adèle ring with the unit-group topology; the two topologies
-- agree (standard; not proved here).
attribute [kb "milne2020cft" "Ch. V, §4, p. 169 (the idèle group I_K)"] NumberField.IdeleGroup

-- The idèle class group C_K = I_K/K^× (p. 171).
attribute [kb "milne2020cft" "Ch. V, §4, p. 171 (the idèle class group)"] NumberField.IdeleClassGroup

-- The content c(a) = ∏_v |a_v|_v (4.4, p. 171): the library's `Ideles.ideleGroupNorm`.
attribute [kb "milne2020cft" "Ch. V, 4.4, p. 171 (the content of an idèle)"] NumberFieldKB.Ideles.ideleGroupNorm

/-- **The finite idèles** $I_f$ (Milne, *CFT*, V, Aside 4.5, p. 171): the units of Mathlib's finite adèle ring. -/
@[kb "milne2020cft" "Ch. V, Aside 4.5, p. 171 (finite idèles)"]
abbrev FiniteIdeles (K : Type) [Field K] [NumberField K] : Type :=
  (FiniteAdeleRing (𝓞 K) K)ˣ

-- Hecke characters (p. 175): Milne's are continuous characters of C_K with values in the circle (equivalently
-- admissible homomorphisms I^S → circle, Remark 4.8). The library's `HeckeCharacter` allows values in ℂ^×
-- (quasi-characters); Milne's are those with values of absolute value 1 (`HeckeCharacter.IsUnitary`).
attribute [kb "milne2020cft" "Ch. V, Remark 4.8, p. 175 (Hecke character)"] NumberFieldKB.HeckeCharacter

end NumberFieldKB.MilneCFT
