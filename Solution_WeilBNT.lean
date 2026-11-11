/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.WeilBNT.AdeleSelfDuality
import NumberFieldKB.WeilBNT.AdeleAnnihilator
import NumberFieldKB.WeilBNT.IdeleClassFiniteness
import NumberFieldKB.WeilBNT.FunctionField.ZetaFinal
import NumberFieldKB.WeilBNT.FunctionField.HeckeRamFE

/-!
# Headline statements of NumberFieldKB 0.2.1: Weil, Basic Number Theory, proved

The declarations of `Challenge.lean`, with the same names and statements, each proved by citing the library theorems
named in its proof. `lake comparator` (configured by `comparator.json`) checks that every theorem here has exactly the
statement of its counterpart in `Challenge.lean` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. Read `Challenge.lean` for the statements, their docstrings and the definitions they use.
-/

noncomputable section

namespace NumberFieldKB.Headlines

/-! ## Weil, *Basic Number Theory*: number fields -/

open IsDedekindDomain NumberField in
open NumberFieldKB.WeilBNT in
/-- **Self-duality of the adeles** (Weil, *Basic Number Theory*, Chapter IV, §2, Theorem 3, for $E = K$): let $\chi$ be
the standard character of $\mathbb A_K$ (`chiA K`, trivial on $K$). Every continuous character $\psi$ of the additive
group $\mathbb A_K$ is $x \mapsto \chi(ax)$ for a unique $a \in \mathbb A_K$; and $\chi(a\xi) = 1$ for every $\xi \in K$ if
and only if $a \in K$ (the annihilator of $K$ is $K$). -/
theorem adeles_selfDual (K : Type) [Field K] [NumberField K] :
    (∀ ψ : AddChar (AdeleRing (𝓞 K) K) Circle, Continuous ψ →
      ∃! a : AdeleRing (𝓞 K) K, ∀ x, ψ x = chiA K (a * x)) ∧
    ∀ a : AdeleRing (𝓞 K) K,
      ((∀ ξ : K, chiA K (a * algebraMap K (AdeleRing (𝓞 K) K) ξ) = 1) ↔
        a ∈ Set.range (algebraMap K (AdeleRing (𝓞 K) K))) :=
  ⟨fun ψ hψ => NumberFieldKB.WeilBNT.weil_IV_2_thm3_char ψ hψ,
      fun a => NumberFieldKB.WeilBNT.weil_IV_2_thm3_annihilator a⟩

open IsDedekindDomain NumberField in
open NumberFieldKB.WeilBNT in
/-- **Weil, *Basic Number Theory*, Chapter IV, §4, Theorem 7** (number fields): for every set $S$ of finite primes of $K$,
with $P$ the set of the infinite places and $S$, the group $\mathbb A_K^\times / K^\times\,\Omega(P)$ is finite, where
$\Omega(P)$ (`omega K S`) is the group of ideles that are units at every finite prime outside $S$. For $S = \emptyset$
this is the finiteness of the class number. -/
theorem idele_classes_finite (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) :
    Finite (IdeleGroup (𝓞 K) K ⧸ (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ omega K S)) :=
  NumberFieldKB.WeilBNT.weil_IV_4_thm7 S

/-! ## Weil, *Basic Number Theory*: function fields -/

open scoped Polynomial in
open NumberFieldKB.WeilBNT.FF in
open Divisor Rep in
/-- **The zeta function of a function field** (Weil, *Basic Number Theory*, Chapter VII, §6, Theorem 4): let $k$ be a
function field of one variable with field of constants $\mathbb F_q$, of genus $g$, and $Z(u) = \sum_{\mathfrak a \ge 0}
u^{\deg \mathfrak a}$ (so $\zeta_k(s) = Z(q^{-s})$). Then $Z(u)(1 - u)(1 - qu) = P(u)$ with $P \in \mathbb Z[u]$ of
degree $2g$, $P(0) = 1$, $P(1) = h$ the number of divisor classes of degree $0$, and $P(u) = q^g u^{2g} P(1/qu)$ (stated
on the coefficients). -/
theorem zeta_functionField {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
    [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k] (hc : IsConstantField Fq k) :
    ∃ P : ℤ[X], P.natDegree = 2 * genus Fq k ∧ P.eval 0 = 1 ∧
      P.eval 1 = Nat.card (ClassGroup0 Fq k) ∧
      zetaSeries Fq k * ((1 - PowerSeries.X) * (1 - (Nat.card Fq : PowerSeries ℤ) * PowerSeries.X)) =
        (P : PowerSeries ℤ) ∧
      ∀ i ≤ 2 * genus Fq k,
        P.coeff (2 * genus Fq k - i) * (Nat.card Fq : ℤ) ^ i = (Nat.card Fq : ℤ) ^ genus Fq k * P.coeff i :=
  NumberFieldKB.WeilBNT.FF.weil_VII_6_thm4_ff hc

open NumberFieldKB.WeilBNT.FF in
/-- **Hecke $L$-functions of a function field** (Weil, *Basic Number Theory*, Chapter VII, §7, Theorem 6, ramified case):
for a quasicharacter $\omega$ of the idele class group of a function field $k$ with field of constants $\mathbb F_q$,
with conductor $\mathfrak f \ne 0$, the series $L(u, \omega)$ is a polynomial in $u$ of degree exactly
$2g - 2 + \deg \mathfrak f$. -/
theorem heckeL_functionField_polynomial {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
    [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]
    (ω : FFHeckeCharacter Fq k) (hc : IsConstantField Fq k) (hf : ω.conductor ≠ 0) :
    ∃ P : Polynomial ℂ, (P.natDegree : ℤ) = 2 * (genus Fq k : ℤ) - 2 + Divisor.deg ω.conductor ∧
      (P : PowerSeries ℂ) = ω.lSeriesF :=
  NumberFieldKB.WeilBNT.FF.FFHeckeCharacter.weil_VII_7_thm6_ramified_exact ω hc hf

end NumberFieldKB.Headlines
