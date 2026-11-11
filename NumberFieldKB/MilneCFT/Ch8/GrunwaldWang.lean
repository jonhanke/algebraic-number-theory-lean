import NumberFieldKB.MilneCFT.Ch7
import NumberFieldKB.MilneCFT.Ch4
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Milne, *Class Field Theory*, Chapter VIII §2: the Grunwald–Wang theorem

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §2,
printed pp. 231–234 (printed page = pdf page − 9).

* **Question 2.1** (a question, not a result): recorded in the docstring of `Corollary2_5`.
* **Example 2.2** (`Example2_2`, named statement): no cyclic extension of $\mathbb Q$ of degree $8$ in which $(2)$
  stays prime; its ingredient (i) is proved (`exercise_1_3`, `not_eighth_power_padic_two`).
* **Theorem 2.3** (`Theorem2_3`), **Theorem 2.4** (Grunwald–Wang, `Theorem2_4`), **Corollary 2.5** (`Corollary2_5`),
  **Theorem 2.6** (`Theorem2_6`): named statements (Artin–Tate, Chapter X).

Local degrees: for a finite Galois $L/K$ and a finite prime $v$, $n_v = [L_w:K_v] = e(w/v)f(w/v)$ for any $w \mid v$;
at an infinite prime $n_v = 2$ if $v$ ramifies in $L$ and $1$ otherwise.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable (K : Type) [Field K] [NumberField K]

/-- **Example 2.2** (named statement; Milne, *CFT*, VIII, Example 2.2, p. 231): let $L$ be a cyclic extension of
$\mathbb Q$ of degree $8$; then $(2)$ does not remain prime in $L$. (Milne deduces it from (i) $16 \in
\mathbb Q_p^{\times 8}$ for $p \ne 2$ (including $p = \infty$) but not for $p = 2$ — proved here as
`exercise_1_3` and `not_eighth_power_padic_two` —, (ii) the product formula for the local Artin maps and (iii)
$16$ is not a norm from the unramified extension of degree $8$ of $\mathbb Q_2$.) -/
@[kb "milne2020cft" "Ch. VIII, Example 2.2, p. 231 (input)"]
structure Example2_2 : Prop where
  not_inert : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L], IsCyclic Gal(L/ℚ) →
    Module.finrank ℚ L = 8 → ¬ (Ideal.span {(2 : 𝓞 L)}).IsPrime

/-- **Theorem 2.3** (named statement; Milne, *CFT*, VIII, Theorem 2.3, p. 232, from Artin–Tate, pp. 98–99): let $S$ be
a finite set of primes of $K$ and, for each $v \in S$, $N_v$ an open subgroup of finite index of $K_v^\times$. There is
a finite abelian extension $L$ of $K$ such that, for all $v \in S$, $L_v$ is the extension of $K_v$ corresponding to
$N_v$ by local class field theory: its local norm group (Chapter VII's `localNormGroup`, `localNormGroupInf`) is
$N_v$. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.3, p. 232 (input)"]
structure Theorem2_3 : Prop where
  exists_ext : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (N' : ∀ w : InfinitePlace K, Subgroup w.Completionˣ),
    (∀ v ∈ S, IsOpen (N v : Set (v.adicCompletion K)ˣ) ∧ (N v).FiniteIndex) →
    (∀ w ∈ T, IsOpen (N' w : Set w.Completionˣ) ∧ (N' w).FiniteIndex) →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      (∀ v ∈ S, Ch7.localNormGroup L v = N v) ∧ ∀ w ∈ T, Ch7.localNormGroupInf L w = N' w

/-- **Theorem 2.4, the Grunwald–Wang theorem** (named statement; Milne, *CFT*, VIII, Theorem 2.4, p. 232; Artin–Tate,
Chapter X, Theorem 5): let $S$ be a finite set of primes and, for $v \in S$, $\chi_v$ a (continuous) character of
$K_v^\times$ of finite order $n_v$; let $n = \mathrm{lcm}(n_v)$. There is a continuous character $\chi$ of $C_K$ whose
restriction to $K_v^\times$ is $\chi_v$ for all $v \in S$, and $\chi$ can be chosen of order $n$ except possibly when
$2^t \mid n$ for some $t$ with $K[\zeta_{2^t}]$ not cyclic over $K$. Characters take values in $\mathbb C^\times$; the
restriction of $\chi$ to $K_v^\times$ is $\chi$ composed with $K_v^\times \to \mathbb I_K \to C_K$. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.4, p. 232 (Grunwald-Wang; input)"]
structure Theorem2_4 : Prop where
  exists_char : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ),
    (∀ v ∈ S, Continuous (χ v) ∧ IsOfFinOrder (χ v)) → (∀ w ∈ T, Continuous (χ' w) ∧ IsOfFinOrder (χ' w)) →
    ∀ n : ℕ, (∀ v ∈ S, orderOf (χ v) ∣ n) → (∀ w ∈ T, orderOf (χ' w) ∣ n) →
      (∀ m : ℕ, (∀ v ∈ S, orderOf (χ v) ∣ m) → (∀ w ∈ T, orderOf (χ' w) ∣ m) → n ∣ m) →
      ∃ ψ : IdeleClassGroup (𝓞 K) K →* ℂˣ, Continuous ψ ∧
        (∀ v ∈ S, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)) = χ v) ∧
        (∀ w ∈ T, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofCompletion (𝓞 K) K w)) = χ' w) ∧
        ((∀ t : ℕ, 2 ^ t ∣ n →
            IsCyclic (CyclotomicField (2 ^ t) K ≃ₐ[K] CyclotomicField (2 ^ t) K)) → orderOf ψ = n)

/-- **Corollary 2.5** (named statement; Milne, *CFT*, VIII, Corollary 2.5, p. 232; Artin–Tate, p. 105, Theorem 5): let
$S$ be a finite set of primes and, for $v \in S$, $n_v \ge 1$, with $n_v$ a possible order of an extension of $K_v$
when $v$ is infinite ($n_v \le 2$ at real and $n_v = 1$ at complex primes). There is a cyclic extension $L$ of $K$ of
degree $n = \mathrm{lcm}(n_v)$ whose local degree is $n_v$ for all $v \in S$. This answers **Question 2.1**
(Milne, p. 231: given cyclic $K^v/K_v$ of degree $n_v$ at $v \in S$, is there a cyclic $L/K$ of degree
$\mathrm{lcm}(n_v)$ with $L_v \cong K^v$?) for the local degrees; Example 2.2 shows the answer to the question itself
can be no. -/
@[kb "milne2020cft" "Ch. VIII, Corollary 2.5, p. 232 (input)"]
structure Corollary2_5 : Prop where
  exists_cyclic : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (nv : HeightOneSpectrum (𝓞 K) → ℕ) (nw : InfinitePlace K → ℕ),
    (∀ v ∈ S, 0 < nv v) → (∀ w ∈ T, nw w = 1 ∨ (w.IsReal ∧ nw w = 2)) →
    ∀ n : ℕ, (∀ v ∈ S, nv v ∣ n) → (∀ w ∈ T, nw w ∣ n) →
      (∀ m : ℕ, (∀ v ∈ S, nv v ∣ m) → (∀ w ∈ T, nw w ∣ m) → n ∣ m) →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsGalois K L),
        IsCyclic Gal(L/K) ∧ Module.finrank K L = n ∧
          (∀ v ∈ S, ∀ Q : v.asIdeal.primesOver (𝓞 L),
            Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K) = nv v) ∧
          ∀ w ∈ T, (InfinitePlace.RamifiesIn L w ↔ nw w = 2)

/-- **Theorem 2.6** (named statement; Milne, *CFT*, VIII, Theorem 2.6, p. 233, deduced from Corollary 2.5 and the
fundamental exact sequence; Brauer–Hasse–Noether, Albert): for every central division algebra $D$ over a number field
$K$, the order of $[D]$ in $\mathrm{Br}(K)$ is $\sqrt{[D:K]}$, and $D$ contains a cyclic extension of $K$ as a maximal
subfield (and hence is split by it, Chapter IV, Corollary 3.7). The running-text consequence "$D$ is a cyclic algebra"
(Dickson) is part (`cyclic`): $D$ is generated by such a field $L$ and one element $\beta$ with
$\beta\alpha\beta^{-1} = \sigma(\alpha)$ ($\alpha\in L$), $\beta^d = \gamma \in K^\times$, $\sigma$ a generator of
$\mathrm{Gal}(L/K)$. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.6, p. 233 (input)"]
structure Theorem2_6 : Prop where
  order_eq : ∀ (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D],
    (orderOf (Ch4.BrauerGroup.mk (⟨.of K D⟩ : CSA.{0, 0} K))) ^ 2 = Module.finrank K D
  cyclic : ∀ (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D],
    ∃ (L : Subalgebra K D) (_ : IsField L), IsCyclic (L ≃ₐ[K] L) ∧ Nat.card (L ≃ₐ[K] L) = Module.finrank K L ∧
      (Module.finrank K L) ^ 2 = Module.finrank K D ∧
      ∃ (σ : L ≃ₐ[K] L) (β : D) (γ : K), Subgroup.zpowers σ = ⊤ ∧ γ ≠ 0 ∧
        β ^ Module.finrank K L = algebraMap K D γ ∧ (∀ α : L, β * (α : D) = (σ α : D) * β) ∧
        Algebra.adjoin K ((L : Set D) ∪ {β}) = ⊤

end NumberFieldKB.MilneCFT.Ch8
