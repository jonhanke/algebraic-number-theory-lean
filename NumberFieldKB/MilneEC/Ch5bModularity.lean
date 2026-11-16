import NumberFieldKB.MilneEC.Ch5bNewforms
import NumberFieldKB.MilneEC.Ch5bGalois
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Milne, *Elliptic Curves*, Chapter V, Sections 5–7: modularity and the theorem of Eichler and Shimura

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Section 5 "Statement of the main theorems" (pdf pp. 216–218),
Theorem 7.10 (p. 229).

**Conventions.**
* The conductor (Milne, V.4, p. 202, recalled from IV): $N = \prod p^{f_p}$ with $f_p = 0$ for good reduction,
  $f_p = 1$ for nodal (multiplicative) reduction, $f_p \ge 2$ otherwise, $f_p = 2$ unless $p = 2, 3$. Milne does not
  define $f_2, f_3$ for additive reduction, so `IsConductorOf E N` records exactly these conditions (it pins $N$ down
  except for the exponents at $2$ and $3$ of additive reduction).
* "$L(E, s) = L(f, s)$" is an identity of Dirichlet series, i.e. of their coefficients (`LSeriesAgree`): the
  coefficients of Mathlib's `WeierstrassCurve.LFunction` (a formal Dirichlet series) and the $q$-expansion
  coefficients $c(n)$ of $f$.
* Newforms of weight $2$ are `IsNormalizedNewform N 1` (weight $2k$, $k = 1$).

Contents: `IsConductorOf`, `LSeriesAgree`, `IsModularCurve` (p. 217), Conjecture 5.1 (`ModularityConjecture`, a
definition), Theorem 5.2 (named `Thm5_2`) and the "if" of Conjecture 5.1 from it (`conj_5_1_if`), the theorems of Wiles
and Taylor and of Breuil, Conrad, Diamond and Taylor (p. 218; named `WilesTaylor`, `BCDT`) and Conjecture 5.1 from
Theorem 5.2 and `BCDT` (`conj_5_1_of_bcdt`), Theorem 7.10 (named `Thm7_10`).

Theorem 6.3 (the map $X_0(N) \to E_f$ through the jacobian) is not stated: modular curves as algebraic curves,
jacobians and differentials on them are not formalized.
-/

open UpperHalfPlane CongruenceSubgroup

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

/-- An elliptic curve $E$ over $\mathbb Q$ has additive (cuspidal) reduction at $p$. -/
def HasAdditiveReductionAt (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasAdditiveReduction ℤ_[p]

/-- **$N$ is the conductor of $E$** (Milne, *EC*, V.4, p. 202, recalled; see the module docstring): for every prime
$p$, $p \nmid N$ iff good reduction, $p \parallel N$ iff nodal reduction, and additive reduction gives $p^2 \mid N$,
with $p^3 \nmid N$ if $p \ge 5$. -/
def IsConductorOf (E : WeierstrassCurve ℚ) (N : ℕ) : Prop :=
  0 < N ∧ ∀ (p : ℕ) [Fact p.Prime],
    (HasGoodReductionAt E p ↔ ¬ p ∣ N) ∧
    (HasMultiplicativeReductionAt E p ↔ (p ∣ N ∧ ¬ p ^ 2 ∣ N)) ∧
    (HasAdditiveReductionAt E p → p ^ 2 ∣ N ∧ (5 ≤ p → ¬ p ^ 3 ∣ N))

/-- $L(E, s) = L(f, s)$ as Dirichlet series: the $n$-th coefficient of $L(E, s)$ is the $q$-expansion coefficient
$c(n)$ of $f$, for all $n \ge 1$. -/
def LSeriesAgree (E : WeierstrassCurve ℚ) (f : ℍ → ℂ) : Prop :=
  ∀ n : ℕ, 0 < n → ((E.LFunction n : ℤ) : ℂ) = (qExpansion 1 f).coeff n

/-- $\sum c(n) n^{-s}$ (integer coefficients) is $L(E, s)$. -/
def LSeriesIs (E : WeierstrassCurve ℚ) (c : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 0 < n → E.LFunction n = c n

/-- **Modular elliptic curve** (Milne, *EC*, V.5, p. 217): $E$ arises from a modular form, i.e.
$L(E, s) = L(f, s)$ for a normalized newform $f$ of weight $2$ for $\Gamma_0(N)$, $N$ the conductor of $E$. -/
def IsModularCurve (E : WeierstrassCurve ℚ) : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (f : ℍ → ℂ), IsConductorOf E N ∧ IsNormalizedNewform N 1 f ∧ LSeriesAgree E f

/-- **Conjecture 5.1 (modularity)** (Milne, *EC*, V, Conjecture 5.1, p. 216; a definition, the proposition): a
Dirichlet series $\sum c(n) n^{-s}$, $c(n) \in \mathbb Z$, is the $L$-series of an elliptic curve over $\mathbb Q$ of
conductor $N$ if and only if it is the $L$-series of a normalized newform for $\Gamma_0(N)$ (of weight $2$). -/
@[kb "milne2006ec" "Ch. V, Conjecture 5.1 (modularity; the statement)"]
def ModularityConjecture : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : ℕ → ℤ),
    (∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧ IsConductorOf E N ∧ LSeriesIs E c) ↔
      ∃ f : ℍ → ℂ, IsNormalizedNewform N 1 f ∧ ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = c n

/-- **Theorem 5.2 (Eichler and Shimura)** (named statement; Milne, *EC*, V, Theorem 5.2, p. 216): for a normalized
newform $f = \sum c(n) q^n$ for $\Gamma_0(N)$ (weight $2$) with all $c(n) \in \mathbb Z$ there is an elliptic curve
$E_f$ over $\mathbb Q$ of conductor $N$ with $L(E_f, s) = L(f, s)$. -/
@[kb "milne2006ec" "Ch. V, Theorem 5.2 (Eichler-Shimura; input)"]
structure Thm5_2 : Prop where
  exists_curve : ∀ (N : ℕ) [NeZero N] (f : ℍ → ℂ), IsNormalizedNewform N 1 f →
    (∀ n : ℕ, ∃ m : ℤ, (qExpansion 1 f).coeff n = m) →
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧ IsConductorOf E N ∧ LSeriesAgree E f

/-- Milne, *EC*, V.5, p. 216 ("The next theorem proves the 'if'"): the "if" direction of Conjecture 5.1 follows from
Theorem 5.2. -/
@[kb "milne2006ec" "Ch. V, Section 5 (pdf p. 216): Theorem 5.2 proves the 'if' of Conjecture 5.1"]
theorem conj_5_1_if (h : Thm5_2) (N : ℕ) [NeZero N] (c : ℕ → ℤ)
    (hf : ∃ f : ℍ → ℂ, IsNormalizedNewform N 1 f ∧ ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = c n) :
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧ IsConductorOf E N ∧ LSeriesIs E c := by
  obtain ⟨f, hf, hc⟩ := hf
  have hint : ∀ n : ℕ, ∃ m : ℤ, (qExpansion 1 f).coeff n = m := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨0, ?_⟩
      obtain ⟨g, hg⟩ := hf.1.1.1
      rw [← hg]
      simpa using CuspFormClass.qExpansion_coeff_zero g one_pos (by simp)
    · exact ⟨c n, hc n hn⟩
  obtain ⟨E, hE, hN, hL⟩ := h.exists_curve N f hf hint
  exact ⟨E, hE, hN, fun n hn => by exact_mod_cast (hL n hn).trans (hc n hn)⟩

/-- An elliptic curve over $\mathbb Q$ is semistable if it has no additive (cuspidal) reduction (Milne, *EC*, V.5,
p. 218: "semistable just means that the curve doesn't have cuspidal reduction at any prime"). -/
def IsSemistable (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ¬ HasAdditiveReductionAt E p

/-- **Theorem of Wiles and Taylor** (named statement; Milne, *EC*, V.5, p. 218, running text): all semistable elliptic
curves over $\mathbb Q$ are modular. -/
@[kb "milne2006ec" "Ch. V, Section 5 (pdf p. 218): Wiles-Taylor, semistable curves are modular (input)"]
structure WilesTaylor : Prop where
  modular : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsSemistable E → IsModularCurve E

/-- **Theorem of Breuil, Conrad, Diamond and Taylor** (named statement; Milne, *EC*, V.5, p. 218, running text): every
elliptic curve over $\mathbb Q$ is modular, with the newform of level the conductor ("the map $f \mapsto E_f$ is
surjective"). -/
@[kb "milne2006ec" "Ch. V, Section 5 (pdf p. 218): Breuil-Conrad-Diamond-Taylor, all curves are modular (input)"]
structure BCDT : Prop where
  modular : ∀ (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N], E.IsElliptic → IsConductorOf E N →
    ∃ f : ℍ → ℂ, IsNormalizedNewform N 1 f ∧ LSeriesAgree E f

/-- Conjecture 5.1 holds, given Theorem 5.2 and the theorem of Breuil, Conrad, Diamond and Taylor (Milne, *EC*, V.5,
pp. 216–218). -/
@[kb "milne2006ec" "Ch. V, Conjecture 5.1 from Theorem 5.2 and BCDT (pdf pp. 216-218)"]
theorem conj_5_1_of_bcdt (h52 : Thm5_2) (h : BCDT) : ModularityConjecture := by
  intro N _ c
  refine ⟨fun ⟨E, hE, hN, hL⟩ => ?_, conj_5_1_if h52 N c⟩
  obtain ⟨f, hf, hfL⟩ := h.modular E N hE hN
  exact ⟨f, hf, fun n hn => by rw [← hfL n hn, hL n hn]⟩

/-- **Theorem 7.10** (named statement; Milne, *EC*, V, Theorem 7.10, p. 229): for a normalized newform
$f = \sum c(n) q^n$ of weight $2$ for $\Gamma_0(N)$ with integer coefficients and the elliptic curve $E$ of
Theorem 6.3 (which is not formalized, hence "some elliptic curve $E$ with good reduction outside $N$"),
$c(p) = a_p = p + 1 - N_p(E)$ for all $p \nmid N$. -/
@[kb "milne2006ec" "Ch. V, Theorem 7.10 (c(p) = a_p; input)"]
structure Thm7_10 : Prop where
  ap : ∀ (N : ℕ) [NeZero N] (f : ℍ → ℂ), IsNormalizedNewform N 1 f →
    (∀ n : ℕ, ∃ m : ℤ, (qExpansion 1 f).coeff n = m) →
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
      HasGoodReductionAt E p ∧ (qExpansion 1 f).coeff p = apAt E p

end NumberFieldKB.MilneEC.Vb
