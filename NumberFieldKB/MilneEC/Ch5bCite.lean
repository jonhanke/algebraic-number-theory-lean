import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter V, Section 8: definitions in prose that are in Mathlib

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Section 8, pp. 230–231. Mathlib's declarations are already tagged
with `milne2020ant` (`NumberFieldKB/MilneANT/ProseCite.lean`, `Ch8Frobenius.lean`), so the `milne2006ec` citations are
short restating theorems.

* D144 (a prime $p$ is unramified in a number field $K$ if no prime of $\mathcal O_K$ over $p$ has $e > 1$):
  Mathlib's `Algebra.IsUnramifiedIn` with `Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one`
  (`unramified_iff_ramificationIdx`).
* D145 (the Frobenius element $F_{\mathfrak p} \in G(\mathfrak p)$ with $F_{\mathfrak p} x \equiv x^p \bmod \mathfrak p$,
  well defined up to conjugation): Mathlib's `IsArithFrobAt`, with `IsArithFrobAt.mem_stabilizer` and
  `IsArithFrobAt.conj` (`frobenius_mem_decomposition`, `frobenius_conj`). Mathlib's notion is for finite Galois
  extensions; the infinite extension $K_S$ is treated in `Ch5bGalois.lean` (`IsFrobeniusAt`).
-/

open NumberField
open scoped Pointwise

namespace NumberFieldKB.MilneEC.Vb

/-- **Unramified prime** (Milne, *EC*, V.8, p. 230, definition in prose; Mathlib
`Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one`): $p$ is unramified in the number field $K$ (Mathlib's
`Algebra.IsUnramifiedIn`) if and only if no prime $\mathfrak P$ of $\mathcal O_K$ over $p$ has ramification index
$e_{\mathfrak P} > 1$. -/
@[kb "milne2006ec" "Ch. V, Section 8 (pdf p. 230): unramified prime (definition in prose)"]
theorem unramified_iff_ramificationIdx (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) ↔
      ∀ (P : Ideal (𝓞 K)) [P.IsPrime], P.LiesOver (Ideal.span {(p : ℤ)}) → Ideal.ramificationIdx P ℤ = 1 :=
  Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one

/-- **Frobenius element, decomposition group** (Milne, *EC*, V.8, p. 231, definition in prose; Mathlib
`IsArithFrobAt.mem_stabilizer`): for a Galois extension $L/\mathbb Q$ and a prime $\mathfrak P$ of $\mathcal O_L$, a
$\sigma$ with $\sigma x \equiv x^{\#(\mathbb Z/\mathfrak P \cap \mathbb Z)} \bmod \mathfrak P$ for all
$x \in \mathcal O_L$ (Mathlib's `IsArithFrobAt`) satisfies $\sigma\mathfrak P = \mathfrak P$. -/
@[kb "milne2006ec" "Ch. V, Section 8 (pdf p. 231): Frobenius element lies in G(P) (definition in prose)"]
theorem frobenius_mem_decomposition (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] {σ : L ≃ₐ[ℚ] L}
    {P : Ideal (𝓞 L)} [P.IsPrime] (h : IsArithFrobAt ℤ σ P) : σ • P = P :=
  h.mem_stabilizer

/-- **Frobenius element, conjugation** (Milne, *EC*, V.8, p. 231, running text: "$F_{\mathfrak p'} = \tau F_{\mathfrak p}
\tau^{-1}$"; Mathlib `IsArithFrobAt.conj`): if $\sigma$ is a Frobenius element at $\mathfrak P$ then $\tau\sigma\tau^{-1}$
is a Frobenius element at $\tau\mathfrak P$. -/
@[kb "milne2006ec" "Ch. V, Section 8 (pdf p. 231): F_{τP} = τ F_P τ⁻¹"]
theorem frobenius_conj (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] {σ : L ≃ₐ[ℚ] L} {P : Ideal (𝓞 L)}
    (h : IsArithFrobAt ℤ σ P) (τ : L ≃ₐ[ℚ] L) : IsArithFrobAt ℤ (τ * σ * τ⁻¹) (τ • P) :=
  h.conj τ

end NumberFieldKB.MilneEC.Vb
