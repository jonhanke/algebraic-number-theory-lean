import NumberFieldKB.MilneCFT.Intro.RayClass

/-!
# Milne, *Class Field Theory*, Chapter VIII §10: more on $L$-series

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §10,
printed pp. 261–263 (printed page = pdf page − 9). (Sections 8 and 9 announce topics without stating results.)

* The functional equation of Dirichlet $L$-series (p. 261): Mathlib's `DirichletCharacter.completedLFunction_one_sub`
  (`dirichlet_functional_equation`, for primitive characters over $\mathbb Q$; Milne cites Narkiewicz).
* Artin $L$-series (definition in prose, p. 261): the Introduction's `artinLFunction` (cited).
* Artin's and Brauer's induction theorems (p. 262): named statements `ArtinInduction`, `BrauerInduction`
  (characters of finite groups; the consequences for $L$-series are not formalized).
* Artin's conjecture (p. 262): the proposition `ArtinConjecture` (a conjecture, not asserted).
* Hecke characters (definition in prose, p. 262): NumberFieldKB's `HeckeCharacter` and `HeckeL.heckeL` (cited).
* A theorem of Gauss (p. 263): named statement `GaussCubicCount`; the consequence $|N_p - p - 1| < 2\sqrt p$
  (`weil_bound_of_gauss`) is proved from it.
-/

open NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

/-- **The functional equation of Dirichlet $L$-series** (Milne, *CFT*, VIII, §10, p. 261, citing Narkiewicz): for a
primitive Dirichlet character $\chi$ modulo $N$, the completed $L$-function satisfies $\Lambda(1-s,\chi) =
\varepsilon(\chi)\Lambda(s,\bar\chi)$ with $|\varepsilon| = 1$. Mathlib's `DirichletCharacter.completedLFunction_one_sub`
(root number `rootNumber`). -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 261 (functional equation of Dirichlet L-series)"]
theorem dirichlet_functional_equation {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction χ (1 - s) =
      N ^ (s - 1 / 2) * χ.rootNumber * DirichletCharacter.completedLFunction χ⁻¹ s :=
  hχ.completedLFunction_one_sub s

open scoped Classical in
/-- **Artin's induction theorem** (named statement; Milne, *CFT*, VIII, §10, p. 262): every character of a finite
group $G$ is a linear combination with rational coefficients of characters induced from cyclic subgroups. Stated for
class functions $G \to \mathbb C$: the character $\chi$ of a representation lies in the $\mathbb Q$-span of the
characters $\mathrm{Ind}_H^G\psi$, $H$ cyclic, $\psi$ a one-dimensional character of $H$, where
$\mathrm{Ind}_H^G\psi(g) = \frac1{|H|}\sum_{x \in G,\ x g x^{-1} \in H}\psi(xgx^{-1})$. -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (Artin's induction theorem; input)"]
structure ArtinInduction : Prop where
  span : ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (n : ℕ) (ρ : G →* GL (Fin n) ℂ),
    (fun g => Matrix.trace ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) ∈
      Submodule.span ℚ {f : G → ℂ | ∃ (H : Subgroup G) (_ : IsCyclic H) (ψ : H →* ℂˣ),
        f = fun g => (Fintype.card H : ℂ)⁻¹ *
          ∑ x : G, if h : x * g * x⁻¹ ∈ H then (ψ ⟨_, h⟩ : ℂ) else 0}

open scoped Classical in
/-- **Brauer's induction theorem** (named statement; Milne, *CFT*, VIII, §10, p. 262): every character of a finite
group is a $\mathbb Z$-linear combination of characters induced from one-dimensional characters of subgroups
(Brauer's form; Milne: "a stronger theorem"). -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (Brauer's induction theorem; input)"]
structure BrauerInduction : Prop where
  span : ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (n : ℕ) (ρ : G →* GL (Fin n) ℂ),
    (fun g => Matrix.trace ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) ∈
      Submodule.span ℤ {f : G → ℂ | ∃ (H : Subgroup G) (ψ : H →* ℂˣ),
        f = fun g => (Fintype.card H : ℂ)⁻¹ *
          ∑ x : G, if h : x * g * x⁻¹ ∈ H then (ψ ⟨_, h⟩ : ℂ) else 0}

/-- **Artin's conjecture** (Milne, *CFT*, VIII, §10, p. 262; a conjecture, not asserted here): for a finite Galois
extension $L/K$ of number fields and a representation $\rho$ of $\mathrm{Gal}(L/K)$ not containing the trivial
representation, $L(s,\rho)$ extends to an entire function. Formalized as: the Artin $L$-function `artinLFunction`
(the Introduction's, with $S$ the finite primes ramified in $L$) agrees on $\mathrm{Re}\,s > 1$ with an entire
function. -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (Artin's conjecture; a conjecture)"]
def ArtinConjecture : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (n : ℕ) (ρ : Gal(L/K) →* GL (Fin n) ℂ),
    (¬ ∃ v : Fin n → ℂ, v ≠ 0 ∧ ∀ σ, ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).mulVec v = v) →
      ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ s : ℂ, 1 < s.re →
        f s = artinLFunction L (Chebotarev.unramifiedPrimes K L)ᶜ ρ s

/-- The number of nonzero solutions $(x,y,z) \in \mathbb F_p^3$ of $x^3 + y^3 + z^3 = 0$; it is $(p-1)N_p$, $N_p$ the
number of points of the projective curve $E : X^3 + Y^3 + Z^3 = 0$ over $\mathbb F_p$. -/
def cubicAffineCount (p : ℕ) [Fact p.Prime] : ℕ :=
  (Finset.univ.filter fun v : Fin 3 → ZMod p => v ≠ 0 ∧ v 0 ^ 3 + v 1 ^ 3 + v 2 ^ 3 = 0).card

/-- **A theorem of Gauss** (named statement; Milne, *CFT*, VIII, §10, p. 263, citing Silverman–Tate IV.2): let $N_p$
be the number of points of $E : X^3 + Y^3 + Z^3 = 0$ over $\mathbb F_p$. (a) If $p \not\equiv 1 \pmod 3$, $N_p = p +
1$. (b) If $p \equiv 1 \pmod 3$, $N_p = p + 1 + A$ where $A$ is the unique integer $\equiv 1 \pmod 3$ with $4p = A^2 +
27B^2$. (The extracted text of (b) is damaged; the form is Silverman–Tate's, checked here for $p = 7$: $N_7 = 9$,
$A = 1$.) -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 263 (a theorem of Gauss; input)"]
structure GaussCubicCount : Prop where
  not_one : ∀ (p : ℕ) [Fact p.Prime], p % 3 ≠ 1 → cubicAffineCount p = (p - 1) * (p + 1)
  one : ∀ (p : ℕ) [Fact p.Prime], p % 3 = 1 → ∃ A B : ℤ, A % 3 = 1 ∧ 4 * p = A ^ 2 + 27 * B ^ 2 ∧
    (cubicAffineCount p : ℤ) = (p - 1) * (p + 1 + A) ∧
    ∀ A' B' : ℤ, A' % 3 = 1 → 4 * p = A' ^ 2 + 27 * B' ^ 2 → A' = A

/-- **The Weil bound from Gauss's theorem** (Milne, *CFT*, VIII, §10, p. 263: "Gauss's theorem implies that the Weil
conjecture holds for $E/\mathbb F_p$"): $|N_p - p - 1| < 2\sqrt p$, in the squared form $(N_p - p - 1)^2 < 4p$ with
$(p-1)N_p$ = `cubicAffineCount p`. -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 263 (Weil bound for X^3 + Y^3 + Z^3 = 0)"]
theorem weil_bound_of_gauss (h : GaussCubicCount) (p : ℕ) [Fact p.Prime] :
    ∃ N : ℤ, (cubicAffineCount p : ℤ) = (p - 1) * N ∧ (N - p - 1) ^ 2 < 4 * p := by
  have hp := (Fact.out : p.Prime)
  have hp2 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  by_cases h3 : p % 3 = 1
  · obtain ⟨A, B, -, hAB, hc, -⟩ := h.one p h3
    refine ⟨p + 1 + A, hc, ?_⟩
    have hB : B ≠ 0 := by
      intro hB0
      subst hB0
      have h4 : (4 * p : ℤ) = A ^ 2 := by simpa using hAB
      have h2 : (2 : ℤ) ∣ A := by
        have : (2 : ℤ) ∣ A ^ 2 := ⟨2 * p, by rw [← h4]; ring⟩
        exact Int.prime_two.dvd_of_dvd_pow this
      obtain ⟨k, rfl⟩ := h2
      have hk : (p : ℤ) = k ^ 2 := by nlinarith
      have hk' : p = k.natAbs ^ 2 := by
        have : (p : ℤ) = (k.natAbs : ℤ) ^ 2 := by rw [hk]; simp
        exact_mod_cast this
      have := (Nat.prime_def.mp hp).2 k.natAbs ⟨k.natAbs, by rw [hk']; ring⟩
      rcases this with h1 | h1
      · rw [h1] at hk'; simp at hk'; exact hp.one_lt.ne' hk'
      · rw [h1] at hk'; nlinarith [hp.one_lt]
    have : 0 < B ^ 2 := by positivity
    nlinarith
  · obtain hc := h.not_one p h3
    refine ⟨p + 1, ?_, by nlinarith⟩
    rw [hc]
    have : 1 ≤ p := hp.one_le
    push_cast [this]
    ring

end NumberFieldKB.MilneCFT.Ch8
