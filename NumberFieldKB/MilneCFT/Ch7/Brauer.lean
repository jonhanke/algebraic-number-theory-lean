import NumberFieldKB.MilneCFT.Ch7.Basic
import NumberFieldKB.MilneCFT.Ch7.Lemma73Aux

/-!
# Milne, *Class Field Theory*, Chapter VII §7: application to the Brauer group

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

Milne writes $H^2(L/K) = H^2(\mathrm{Gal}(L/K), L^\times)$ ($=\mathrm{Br}(L/K)$, Chapter IV) and states the results of
this section both cohomologically and "in more concrete terms" for central simple algebras (p. 220). The local
groups $H^2(L_v/K_v)$ are those of the completions; by Shapiro's lemma $H^2(G_w, L_w^\times)\cong
H^2(G,(L\otimes_KK_v)^\times)$ ($L\otimes_KK_v\cong\prod_{w\mid v}L_w$, Proposition 2.3), so the localization map is
$H^2(G, L^\times)\to H^2(G,(L\otimes_KK_v)^\times)$, induced by $L^\times\to(L\otimes_KK_v)^\times$.

* **Theorem 7.1** (`Theorem7_1`, named statement): $H^2(L/K)\to\bigoplus_vH^2(L_v/K_v)$ is injective; and its concrete
  form (`Theorem7_1.splits`): a central simple algebra over $K$ split by every $K_v$ is split.
* **Proposition 7.2** (`Prop7_2`, named statement, concrete form): every central simple algebra over $K$ is split by a
  cyclic cyclotomic extension.
* **Lemma 7.3** (`lemma_7_3`): totally complex cyclic cyclotomic extensions with prescribed divisibility of local
  degrees exist.
* `IsCyclotomicExt K L` (definition in prose, p. 220): $L\subseteq K[\zeta]$ for a root of unity $\zeta$; compared with
  Mathlib's `IsCyclotomicExtension` (`isCyclotomicExt_of_isCyclotomicExtension`).
-/

open IsDedekindDomain NumberField CategoryTheory TensorProduct

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K]

/-- **Cyclotomic extension** (definition in prose; Milne, *CFT*, Chapter VII, p. 220): $L/K$ is cyclotomic if
$L\subseteq K[\zeta]$ for some root of unity $\zeta$: there are $n\ge1$ and an extension $E = K(\zeta_n)$
(Mathlib's `IsCyclotomicExtension {n} K E`) into which $L$ embeds over $K$. -/
@[kb "milne2020cft" "Ch. VII, §7, p. 220 (cyclotomic extension)"]
def IsCyclotomicExt (L : Type) [Field L] [Algebra K L] : Prop :=
  ∃ (n : ℕ) (_ : 0 < n) (E : Type) (_ : Field E) (_ : Algebra K E), IsCyclotomicExtension {n} K E ∧
    Nonempty (L →ₐ[K] E)

omit [NumberField K] in
/-- Mathlib's `IsCyclotomicExtension {n} K L` ($L = K(\zeta_n)$) is cyclotomic in Milne's sense. -/
theorem isCyclotomicExt_of_isCyclotomicExtension (L : Type) [Field L] [Algebra K L] (n : ℕ) (hn : 0 < n)
    [IsCyclotomicExtension {n} K L] : IsCyclotomicExt K L :=
  ⟨n, hn, L, inferInstance, inferInstance, inferInstance, ⟨AlgHom.id K L⟩⟩

/-- A central simple $K$-algebra $A$ is split by the field $F\supseteq K$: $F\otimes_KA\cong M_n(F)$. -/
def SplitsOver (A : Type) [Ring A] [Algebra K A] (F : Type) [Field F] [Algebra K F] : Prop :=
  ∃ n : ℕ, Nonempty (F ⊗[K] A ≃ₐ[F] Matrix (Fin n) (Fin n) F)

/-- The map $L^\times\to(L\otimes_KF)^\times$, $x\mapsto x\otimes1$, as a map of $G$-modules
($G = \mathrm{Aut}_K(L)$ acting on the first factor). -/
def unitsToTensor (L : Type) [Field L] [Algebra K L] (F : Type) [Field F] [Algebra K F] : Lˣ →* (L ⊗[K] F)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] F).toMonoidHom

/-- $G = \mathrm{Aut}_K(L)$ acts on $L\otimes_KF$ through the first factor. -/
instance tensorAction (L : Type) [Field L] [Algebra K L] (F : Type) [Field F] [Algebra K F] :
    MulSemiringAction (L ≃ₐ[K] L) (L ⊗[K] F) where
  smul σ x := Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F) x
  one_smul x := by
    show Algebra.TensorProduct.map (1 : L ≃ₐ[K] L).toAlgHom (AlgHom.id K F) x = x
    have h : (1 : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := rfl
    rw [h, Algebra.TensorProduct.map_id]
    rfl
  mul_smul σ τ x := by
    show Algebra.TensorProduct.map (σ * τ).toAlgHom (AlgHom.id K F) x =
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F)
        (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K F) x)
    have h : (σ * τ).toAlgHom = σ.toAlgHom.comp τ.toAlgHom := rfl
    have h2 : AlgHom.id K F = (AlgHom.id K F).comp (AlgHom.id K F) := rfl
    rw [h, h2, Algebra.TensorProduct.map_comp]
    rfl
  smul_zero σ := map_zero _
  smul_add σ := map_add _
  smul_one σ := map_one _
  smul_mul σ := map_mul _

/-- The induced action on $(L\otimes_KF)^\times$. -/
instance tensorUnitsAction (L : Type) [Field L] [Algebra K L] (F : Type) [Field F] [Algebra K F] :
    MulDistribMulAction (L ≃ₐ[K] L) (L ⊗[K] F)ˣ where
  smul σ x := Units.map (MulSemiringAction.toRingHom _ _ σ).toMonoidHom x
  one_smul x := Units.ext (one_smul (L ≃ₐ[K] L) (x : L ⊗[K] F))
  mul_smul σ τ x := Units.ext (mul_smul σ τ (x : L ⊗[K] F))
  smul_mul σ x y := map_mul _ x y
  smul_one σ := map_one _

/-- **Theorem 7.1** (named statement; Milne, *CFT*, Chapter VII, p. 219): for every finite Galois extension $L/K$ of
number fields, the canonical map $H^2(L/K)\to\bigoplus_vH^2(L_v/K_v)$ is injective; and (p. 220, "in more concrete
terms", the case of $L$ infinite) a central simple algebra over $K$ that splits over $K_v$ for all $v$ splits over $K$.
Here the cohomological statement is for $L$ finite: a class of $H^2(G, L^\times)$ that becomes trivial in the cohomology
of every $(L\otimes_KK_v)^\times$, $v$ finite or infinite, is trivial (the cocycle form: a $2$-cocycle that is a
coboundary in each $(L\otimes K_v)^\times$ is a coboundary in $L^\times$). -/
@[kb "milne2020cft" "Ch. VII, Thm. 7.1 (input)"]
structure Theorem7_1 : Prop where
  injective : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (f : Gal(L/K) × Gal(L/K) → Lˣ), groupCohomology.IsMulCocycle₂ f →
    (∀ v : HeightOneSpectrum (𝓞 K), groupCohomology.IsMulCoboundary₂
      (fun g : Gal(L/K) × Gal(L/K) => unitsToTensor K L (v.adicCompletion K) (f g))) →
    (∀ w : InfinitePlace K, groupCohomology.IsMulCoboundary₂
      (fun g : Gal(L/K) × Gal(L/K) => unitsToTensor K L w.Completion (f g))) →
    groupCohomology.IsMulCoboundary₂ f
  splits : ∀ (A : Type) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A],
    (∀ v : HeightOneSpectrum (𝓞 K), SplitsOver K A (v.adicCompletion K)) →
    (∀ w : InfinitePlace K, SplitsOver K A w.Completion) → SplitsOver K A K

/-- **Proposition 7.2** (named statement; Milne, *CFT*, Chapter VII, p. 220, in the concrete form of p. 221): every
central simple algebra over $K$ splits over a cyclic cyclotomic extension of $K$. -/
@[kb "milne2020cft" "Ch. VII, Prop. 7.2 (input)"]
structure Prop7_2 : Prop where
  splits : ∀ (A : Type) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A],
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsGalois K L),
      IsCyclic Gal(L/K) ∧ IsCyclotomicExt K L ∧ SplitsOver K A L

/-- **Lemma 7.3** (Milne, *CFT*, Chapter VII, p. 220): given a number field $K$, a finite set $S$ of finite primes of
$K$ and an integer $m > 0$, there is a totally complex cyclic cyclotomic extension $L/K$ such that $m$ divides the
local degree $[L_w:K_v] = e(w/v)f(w/v)$ for all $v\in S$ and $w\mid v$. -/
@[kb "milne2020cft" "Ch. VII, Lemma 7.3"]
theorem lemma_7_3 (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (hm : 0 < m) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsGalois K L),
      IsCyclic Gal(L/K) ∧ IsCyclotomicExt K L ∧ (∀ w : InfinitePlace L, w.IsComplex) ∧
      ∀ v ∈ S, ∀ Q : v.asIdeal.primesOver (𝓞 L),
        m ∣ Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K) := by
  obtain ⟨N, hN, L, hG, hC, hT, hQ⟩ := Lemma73.Fld.exists_field K S m hm
  exact ⟨↥L, inferInstance, inferInstance, inferInstance, hG, hC,
    ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), Lemma73.Fld.E K N, inferInstance, inferInstance,
      inferInstance, ⟨L.val⟩⟩, hT, hQ⟩

end NumberFieldKB.MilneCFT.Ch7
