import NumberFieldKB.MilneEC.Ch4Rank
import NumberFieldKB.MilneEC.Ch5bModularity
import NumberFieldKB.MilneEC.Ch3Weierstrass
import NumberFieldKB.MilneEC.Ch5LSeries
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Milne, *Elliptic Curves*, Chapter IV §§8–10: Propositions 8.1, 8.2, Aside 9.5, Aside 10.7, the sign $w_E$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV.  Locators give the pdf page of
the text `ectext6` (printed page = pdf page − 8).

These are results that Milne quotes without proof (he refers to Silverman 1986, X.6, to Taylor and collaborators,
and to Goldfeld 1982).  They are recorded as **named statements** (`Prop`-valued structures, never axioms), using
the Selmer and Tate–Shafarevich groups of `Ch4Selmer.lean`, the rank of `Ch4Rank.lean`, the point counts and
reduction types of `Ch5LSeries.lean`, the conductor and modularity of `Ch5bModularity.lean`, and Mathlib's
$L$-series `WeierstrassCurve.LSeries`.

* **Proposition 8.1** (`Prop8_1`): for a prime $p \equiv 1 \pmod 8$, the $2$-Selmer group of
  $E \colon Y^2Z = X^3 + pXZ^2$ over $\mathbb Q$ is $(\mathbb Z/2)^3$.
* **Proposition 8.2** (`Prop8_2`): if moreover $2$ is not a fourth power modulo $p$, then $\operatorname{rank}
  E(\mathbb Q) = 0$ and $Ш(E/\mathbb Q)_2 \cong (\mathbb Z/2)^2$.  (In the text the relation symbol between
  $Ш(E/\mathbb Q)_2$ and $(\mathbb Z/2)^2$ was lost in extraction; the isomorphism is what follows from
  Proposition 8.1 and the displayed formula $\operatorname{rank} + \dim Ш_2 = \dim S^{(2)} - 1$ on pdf p. 152,
  and is Silverman's X.6.2(b).)  Proved here: the curve is elliptic (`curveP_isElliptic`) and the hypotheses of 8.2
  hold for $p = 17, 41, 97, 193$, Milne's examples in Remark 8.3 (`prop_8_2_hyp_17` and so on).
* **Aside 9.5 (Sato–Tate)** (`SatoTate`): for $E$ over $\mathbb Q$ without complex multiplication, the angles
  $\theta(p) \in [0, \pi]$ with $a_p = 2\sqrt p\cos\theta(p)$ are equidistributed for the measure
  $\frac 2\pi \sin^2 t\,dt$.  Complex multiplication (`HasComplexMultiplication`) is defined through the lattice:
  $E_{\mathbb C} \cong \mathbb C/\Lambda$, and $\operatorname{End}(E) \ne \mathbb Z$ iff $\alpha\Lambda \subseteq
  \Lambda$ for some $\alpha \notin \mathbb Z$ (Milne III, §3: maps $\mathbb C/\Lambda \to \mathbb C/\Lambda$ are
  multiplications by such $\alpha$); Mathlib has no endomorphism rings of elliptic curves.
* **Aside 10.7 (Goldfeld)** (`Goldfeld`): for modular $E$, if $\prod_{p \le x} N_p/p \sim C(\log x)^r$ with
  $C > 0$, then $L(E, s) \sim C'(s-1)^r$ as $s \to 1$ and $L(E, s) \ne 0$ for $\operatorname{Re}(s) > 1$.
* **The sign $w_E$** (definition in prose, pdf p. 175; `IsSignOfFunctionalEquation`): $w = \pm 1$ is the sign
  in $\Lambda(E, s) = w\,\Lambda(E, 2 - s)$, $\Lambda(E,s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(E,s)$.
-/

open WeierstrassCurve Filter Topology

namespace NumberFieldKB.MilneEC

/-! ## §8: the curves $Y^2 = X^3 + pX$ -/

/-- Milne's curve $E \colon Y^2Z = X^3 + pXZ^2$ of Proposition 8.1 (pdf p. 151), as a Weierstrass curve over
$\mathbb Q$. -/
def curveP (p : ℕ) : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := p, a₆ := 0 }

theorem curveP_Δ (p : ℕ) : (curveP p).Δ = -64 * (p : ℚ) ^ 3 := by
  simp only [curveP, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- For $p \ne 0$ the curve $Y^2 = X^3 + pX$ is elliptic (its discriminant is $-64p^3$). -/
theorem curveP_isElliptic {p : ℕ} (hp : p ≠ 0) : (curveP p).IsElliptic :=
  ⟨isUnit_iff_ne_zero.2 (by rw [curveP_Δ]; simp [hp])⟩

/-- The $2$-torsion of the Tate–Shafarevich group, $Ш(E/\mathbb Q)_2$. -/
noncomputable def shaTwoTorsion (W : WeierstrassCurve ℚ) :
    AddSubgroup (groupCohomology.H1 (pointsRep W (AlgebraicClosure ℚ))) :=
  tateShafarevich ℚ W ⊓ (zsmulAddGroupHom (α := groupCohomology.H1 (pointsRep W (AlgebraicClosure ℚ))) 2).ker

/-- **Proposition 8.1** (named statement; Milne, *EC*, IV, Proposition 8.1, pdf p. 151, quoting Silverman 1986,
X.6.2): for a prime $p \equiv 1 \pmod 8$, the $2$-Selmer group $S^{(2)}(E/\mathbb Q)$ of
$E \colon Y^2Z = X^3 + pXZ^2$ is isomorphic to $(\mathbb Z/2\mathbb Z)^3$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 8.1, pdf p. 151"]
structure Prop8_1 : Prop where
  selmer : ∀ p : ℕ, p.Prime → p % 8 = 1 →
    Nonempty (selmerGroup ℚ (curveP p) 2 ≃+ (Fin 3 → ZMod 2))

/-- **Proposition 8.2** (named statement; Milne, *EC*, IV, Proposition 8.2, pdf p. 152): for a prime
$p \equiv 1 \pmod 8$ such that $2$ is not a fourth power modulo $p$, the curve of Proposition 8.1 has
$\operatorname{rank} E(\mathbb Q) = 0$ and $Ш(E/\mathbb Q)_2 \cong (\mathbb Z/2\mathbb Z)^2$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 8.2, pdf p. 152"]
structure Prop8_2 : Prop where
  rank_eq_zero : ∀ p : ℕ, p.Prime → p % 8 = 1 → (¬ ∃ x : ZMod p, x ^ 4 = 2) → rank (curveP p) = 0
  sha_two : ∀ p : ℕ, p.Prime → p % 8 = 1 → (¬ ∃ x : ZMod p, x ^ 4 = 2) →
    Nonempty (shaTwoTorsion (curveP p) ≃+ (Fin 2 → ZMod 2))

/-- Euler's criterion for fourth powers, one direction: if $4 \mid p - 1$ and $2^{(p-1)/4} \ne 1$ in
$\mathbb F_p$, then $2$ is not a fourth power modulo $p$. -/
theorem not_fourth_power_two {p : ℕ} [hp : Fact p.Prime] (h4 : 4 ∣ p - 1)
    (h : (2 : ZMod p) ^ ((p - 1) / 4) ≠ 1) : ¬ ∃ x : ZMod p, x ^ 4 = 2 := by
  rintro ⟨x, hx⟩
  by_cases hx0 : x = 0
  · subst hx0
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat, ← hx]; ring
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2
    subst hp2
    norm_num at h4
  · apply h
    rw [← hx, ← pow_mul, Nat.mul_div_cancel' h4, ZMod.pow_card_sub_one_eq_one hx0]

/-- The hypotheses of Proposition 8.2 hold for $p = 17$ (Milne, Remark 8.3: $17 = 1^2 + 4^2$). -/
@[kb "milne2006ec" "Ch. IV, Remark 8.3 (examples for Proposition 8.2), pdf p. 152"]
theorem prop_8_2_hyp_17 : Nat.Prime 17 ∧ 17 % 8 = 1 ∧ ¬ ∃ x : ZMod 17, x ^ 4 = 2 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact ⟨this.out, by norm_num, not_fourth_power_two (by norm_num) (by decide +revert)⟩

/-- The hypotheses of Proposition 8.2 hold for $p = 41$ ($41 = 5^2 + 4^2$). -/
@[kb "milne2006ec" "Ch. IV, Remark 8.3 (examples for Proposition 8.2), pdf p. 152"]
theorem prop_8_2_hyp_41 : Nat.Prime 41 ∧ 41 % 8 = 1 ∧ ¬ ∃ x : ZMod 41, x ^ 4 = 2 := by
  have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  exact ⟨this.out, by norm_num, not_fourth_power_two (by norm_num) (by decide +revert)⟩

/-- The hypotheses of Proposition 8.2 hold for $p = 97$ ($97 = 9^2 + 4^2$). -/
@[kb "milne2006ec" "Ch. IV, Remark 8.3 (examples for Proposition 8.2), pdf p. 152"]
theorem prop_8_2_hyp_97 : Nat.Prime 97 ∧ 97 % 8 = 1 ∧ ¬ ∃ x : ZMod 97, x ^ 4 = 2 := by
  have : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact ⟨this.out, by norm_num, not_fourth_power_two (by norm_num) (by decide +revert)⟩

set_option maxRecDepth 20000 in
/-- The hypotheses of Proposition 8.2 hold for $p = 193$ ($193 = 7^2 + 12^2$). -/
@[kb "milne2006ec" "Ch. IV, Remark 8.3 (examples for Proposition 8.2), pdf p. 152"]
theorem prop_8_2_hyp_193 : Nat.Prime 193 ∧ 193 % 8 = 1 ∧ ¬ ∃ x : ZMod 193, x ^ 4 = 2 := by
  have : Fact (Nat.Prime 193) := ⟨by norm_num⟩
  exact ⟨this.out, by norm_num, not_fourth_power_two (by norm_num) (by decide +revert)⟩

/-! ## §9: the Sato–Tate conjecture (Aside 9.5) -/

/-- **Complex multiplication** for an elliptic curve $E$ over $\mathbb Q$ (Milne, *EC*, IV, Aside 9.5 and §10:
"$\operatorname{End}(E) \ne \mathbb Z$"), through the uniformization of $E_{\mathbb C}$: there are a lattice
$\Lambda$ with $j(E(\Lambda)) = j(E)$ (so $E_{\mathbb C} \cong E(\Lambda) \cong \mathbb C/\Lambda$, Milne III, §3,
and II 2.1) and $\alpha \in \mathbb C \setminus \mathbb Z$ with $\alpha\Lambda \subseteq \Lambda$ (the endomorphisms
of $\mathbb C/\Lambda$ are the multiplications by such $\alpha$, Milne III, §3). Mathlib has no endomorphism rings
of elliptic curves, so this is the definition used here. -/
@[kb "milne2006ec" "Ch. IV, Aside 9.5 and §10, curves with complex multiplication (End(E) ≠ Z), pdf pp. 158, 175"]
def HasComplexMultiplication (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∃ (L : PeriodPair) (α : ℂ), (III.curveOf L).j = (E.map (algebraMap ℚ ℂ)).j ∧ (∀ n : ℤ, α ≠ n) ∧
    ∀ ω ∈ L.lattice, α * ω ∈ L.lattice

/-- $p$ is a prime of good reduction for $E$. -/
def IsGoodPrime (E : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  ∃ h : p.Prime, haveI : Fact p.Prime := ⟨h⟩; V.HasGoodReductionAt E p

/-- $N_p = \#E_p(\mathbb F_p)$ as a real number ($0$ if $p$ is not prime). -/
noncomputable def numPointsAt (E : WeierstrassCurve ℚ) (p : ℕ) : ℝ :=
  if h : p.Prime then haveI : Fact p.Prime := ⟨h⟩; (V.numPoints E p : ℝ) else 0

/-- The **Frobenius angle** $\theta(p) \in [0, \pi]$ (Milne, Aside 9.5): with $a_p = p + 1 - N_p$, the root
$\alpha_p = \sqrt p\,e^{i\theta(p)}$ of $X^2 - a_pX + p$, i.e. $a_p = 2\sqrt p\cos\theta(p)$. (For $|a_p| \le 2\sqrt p$,
the Hasse bound, this determines $\theta(p)$; `Real.arccos` is used.) -/
noncomputable def frobeniusAngle (E : WeierstrassCurve ℚ) (p : ℕ) : ℝ :=
  Real.arccos (((p : ℝ) + 1 - numPointsAt E p) / (2 * Real.sqrt p))

open scoped Classical in
/-- **Aside 9.5, the Sato–Tate conjecture** (named statement; Milne, *EC*, IV, Aside 9.5, pdf p. 158; proved by
Taylor and collaborators, announced 2006): for an elliptic curve over $\mathbb Q$ without complex multiplication,
the density of the primes $p$ with $a \le \theta(p) \le b$ is $\frac 2\pi\int_a^b \sin^2 t\,dt$ (natural density among
the primes; the finitely many bad primes do not matter). -/
@[kb "milne2006ec" "Ch. IV, Aside 9.5 (Sato-Tate), pdf p. 158"]
structure SatoTate : Prop where
  equidistributed : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ¬ HasComplexMultiplication E →
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi →
      Tendsto (fun x : ℕ =>
        (((Finset.range (x + 1)).filter fun p =>
            IsGoodPrime E p ∧ a ≤ frobeniusAngle E p ∧ frobeniusAngle E p ≤ b).card : ℝ) /
          ((Finset.range (x + 1)).filter Nat.Prime).card)
        atTop (𝓝 ((2 / Real.pi) * ∫ t in a..b, Real.sin t ^ 2))

/-! ## §10: the sign of the functional equation and Goldfeld's theorem -/

/-- **The sign $w_E$** (definition in prose; Milne, *EC*, IV, §10, Conjecture 10.3, pdf p. 175): $w = \pm 1$ is the
sign in the functional equation $\Lambda(E, s) = w\,\Lambda(E, 2 - s)$, where
$\Lambda(E, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(E, s)$ for $\operatorname{Re}(s) > 3/2$, continued to a meromorphic
function on $\mathbb C$ (the identity holds off a discrete set). The conductor $N$ is a parameter with
`Vb.IsConductorOf E N`, since that predicate does not fix the exponents at $2$ and $3$ (Ogg's formula is not
formalized). -/
@[kb "milne2006ec" "Ch. IV, §10, the sign w_E of the functional equation (definition in prose), pdf p. 175"]
def IsSignOfFunctionalEquation (E : WeierstrassCurve ℚ) (N : ℕ) (w : ℤ) : Prop :=
  Vb.IsConductorOf E N ∧ (w = 1 ∨ w = -1) ∧ ∃ Λ : ℂ → ℂ, MeromorphicOn Λ Set.univ ∧
    (∀ s : ℂ, 3 / 2 < s.re →
      Λ s = (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * E.LSeries s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ, Λ s = w * Λ (2 - s)

open scoped Classical in
/-- **Aside 10.7, Goldfeld's theorem** (named statement; Milne, *EC*, IV, Aside 10.7, pdf p. 174, citing Goldfeld
1982): for a modular elliptic curve $E$ over $\mathbb Q$, if $\prod_{p \le x} N_p/p \sim C(\log x)^r$ for some $C > 0$
and $r$, then $L(E, s) \sim C'(s - 1)^r$ as $s \to 1$ for some $C' \ne 0$, and $L(E, s) \ne 0$ for
$\operatorname{Re}(s) > 1$ (the generalized Riemann hypothesis for $L(E,s)$). Here $L(E, s)$ is the entire
continuation of Mathlib's `E.LSeries` (it exists for modular $E$); the product runs over the good primes (finitely
many factors only change $C$), and $s \to 1$ through real $s > 1$. -/
@[kb "milne2006ec" "Ch. IV, Aside 10.7 (Goldfeld), pdf p. 174"]
structure Goldfeld : Prop where
  bsd_and_grh : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], Vb.IsModularCurve E →
    ∀ L : ℂ → ℂ, Differentiable ℂ L → (∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s) →
    ∀ C r : ℝ, 0 < C →
      Tendsto (fun x : ℕ => (∏ p ∈ (Finset.range (x + 1)).filter (IsGoodPrime E),
          numPointsAt E p / p) / (C * Real.log x ^ r)) atTop (𝓝 1) →
      (∃ C' : ℂ, C' ≠ 0 ∧
        Tendsto (fun s : ℝ => L s / (((s - 1) ^ r : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 C')) ∧
      ∀ s : ℂ, 1 < s.re → L s ≠ 0

end NumberFieldKB.MilneEC
