/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.MilneANT.Ch6FermatThm
import NumberFieldKB.MilneANT.Ch8Unconditional
import NumberFieldKB.MilneANT.Ch7Ostrowski
import NumberFieldKB.WeilBNT.AdeleSelfDuality
import NumberFieldKB.WeilBNT.AdeleAnnihilator
import NumberFieldKB.WeilBNT.IdeleClassFiniteness
import NumberFieldKB.WeilBNT.FunctionField.ZetaFinal
import NumberFieldKB.WeilBNT.FunctionField.HeckeRamFE
import NumberFieldKB.GlobalZeta.FunctionalEquation
import NumberFieldKB.HeckeL.RootNumber
import NumberFieldKB.HeckeL.DedekindCont
import NumberFieldKB.Pontryagin.Unconditional
import NumberFieldKB.ModularCurves.EllipticCount
import NumberFieldKB.ModularCurves.EllipticCountClosed
import NumberFieldKB.ModularCurves.GenusX0
import NumberFieldKB.ModularCurves.Rationality
import NumberFieldKB.ModularCurves.Theorem23
import NumberFieldKB.ModularCurves.Cor34
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangUncond
import NumberFieldKB.MilneCFT.Ch8.Theorem26Uncond
import NumberFieldKB.MilneCFT.LubinTate.LocalKroneckerWeberCFT
import NumberFieldKB.MilneCFT.Ch8.Eisenstein.Reciprocity
import NumberFieldKB.MilneCFT.Ch8.Eisenstein.Furtwangler
import NumberFieldKB.MilneCFT.Ch8.GaussCubicUncond
import NumberFieldKB.MilneCFT.Ch5LSeriesExtends
import NumberFieldKB.MilneEC.Ch1Bezout
import NumberFieldKB.MilneEC.Ch1Assoc
import NumberFieldKB.MilneEC.Ch4TwoDescent
import NumberFieldKB.MilneEC.Ch4Example57
import NumberFieldKB.MilneEC.Ch4bLangUnconditional
import NumberFieldKB.MilneEC.Ch4BSD
import NumberFieldKB.MilneEC.Ch4Prop81
import NumberFieldKB.MilneEC.Ch4LocalPeriodBad
import NumberFieldKB.MilneEC.Ch4LocalPeriodRemark
import NumberFieldKB.MilneEC.Ch3RealPeriod
import NumberFieldKB.MilneEC.Ch2MazurRealization
import NumberFieldKB.MilneEC.ShaComparison

/-!
# Headline statements of NumberFieldKB 0.4.0, proved

The declarations of `Challenge.lean`, with the same names and statements, each proved by citing the library theorems
named in its proof. `lake comparator` (configured by `comparator.json`) checks that every theorem here has exactly the
statement of its counterpart in `Challenge.lean` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. Read `Challenge.lean` for the statements, their docstrings and the definitions they use.
-/

noncomputable section

namespace NumberFieldKB.Headlines

/-! ## Milne, *Algebraic Number Theory* -/

open NumberField Polynomial in
/-- **Kummer's theorem** (Milne, *Algebraic Number Theory*, Theorem 6.8): if $p$ is an odd prime that does not divide
the class number of $\mathbb Q(\zeta_p)$, then $x^p + y^p = z^p$ has no solution in integers with $p \nmid xyz$. -/
theorem kummer_regular (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (hreg : ¬ p ∣ classNumber (CyclotomicField p ℚ)) :
    ¬ ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧ ¬ (p : ℤ) ∣ x * y * z :=
  NumberFieldKB.MilneANT.theorem_6_8 p hodd hreg

open NumberField IsDedekindDomain Polynomial UniqueFactorizationMonoid in
open scoped Classical in
open NumberFieldKB.MilneANT in
/-- **Dedekind's theorem** (Milne, *Algebraic Number Theory*, Theorem 8.23): let $f$ be a monic polynomial over the
ring of integers of a number field $K$ and $\mathfrak p$ a prime such that $f$ is squarefree modulo $\mathfrak p$.
Then some element of the Galois group of $f$ over $K$, acting on the roots of $f$, has as cycle type the multiset of
the degrees of the irreducible factors of $f$ modulo $\mathfrak p$. -/
theorem dedekind_factorizationType {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X]) (hf : f.Monic)
    (𝔭 : HeightOneSpectrum (𝓞 K))
    (hsq : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))) :
    ∃ σ : (f.map (algebraMap (𝓞 K) K)).Gal,
      (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts =
        (normalizedFactors (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))).map natDegree :=
  NumberFieldKB.MilneANT.thm_8_23' f hf 𝔭 hsq

open NumberField in
open NumberFieldKB.MilneANT in
/-- **The places of a number field** (Milne, *Algebraic Number Theory*, Theorem 7.14): every nontrivial absolute value
on a number field $K$ is equivalent to exactly one of the absolute values attached to a nonzero prime ideal, a real
embedding, or a conjugate pair of complex embeddings. In Lean: the map from Mathlib's finite and infinite places to the
equivalence classes of nontrivial absolute values on $K$ (`MilnePlace K`) is a bijection. -/
theorem ostrowski_numberField (K : Type) [Field K] [NumberField K] : Function.Bijective (placeOf K) :=
  NumberFieldKB.MilneANT.thm_7_14_unconditional K

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

/-! ## Tate's thesis -/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set in
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil in
open scoped Classical ENNReal NNReal nonZeroDivisors in
open NumberFieldKB NumberFieldKB.GlobalZeta in
/-- **Tate's main theorem** (Cassels–Fröhlich, Chapter XV, Main Theorem 4.4.1): for a number field $F$, a factorizable
Schwartz–Bruhat function $\Phi$ on $\mathbb A_F$ and a Hecke character $\chi$ with $|\chi| = \|\cdot\|^\sigma$, the zeta
integral $Z(\Phi, \chi, s) = \int_{\mathbb A_F^\times} \Phi(x)\chi(x)\|x\|^s\,d^\times x$ (convergent for
$\operatorname{Re} s + \sigma > 1$) extends to a meromorphic function $Z$ on $\mathbb C$ with
$Z(1 - s) = Z(\hat\Phi, \chi^{-1}, s)$ wherever the right side converges. (The library proves this for its continuation
`globalZetaCont`; the headline states the existence of the continuation.) -/
theorem tate_globalZeta_functionalEquation {F : Type} [Field F] [NumberField F] (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) :
    ∃ Z : ℂ → ℂ, Meromorphic Z ∧
      (∀ s : ℂ, 1 < s.re + χ.shift → Z s = globalZeta (Φ : Adeles F → ℂ) χ s) ∧
      ∀ s : ℂ, 1 < s.re - χ.shift → Z (1 - s) = globalZeta Φ.fourier χ⁻¹ s :=
  ⟨NumberFieldKB.GlobalZeta.globalZetaCont Φ χ, NumberFieldKB.GlobalZeta.meromorphic_globalZetaCont Φ χ,
      fun _ hs => NumberFieldKB.GlobalZeta.globalZetaCont_eq Φ χ hs,
      fun _ hs => NumberFieldKB.GlobalZeta.globalZetaCont_one_sub Φ χ hs⟩

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set in
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil in
open scoped Classical ENNReal NNReal nonZeroDivisors in
open NumberFieldKB NumberFieldKB.GlobalZeta in
/-- **Poles and residues** (Cassels–Fröhlich, Chapter XV, Main Theorem 4.4.1): for $\chi = \|\cdot\|^c$ the continuation $Z$ of
$Z(\Phi, \chi, s)$ has residue $\hat\Phi(0)\rho_F$ at $s = 1 - c$ and $-\Phi(0)\rho_F$ at $s = -c$, where $\rho_F$ is the residue of
the Dedekind zeta function at $s = 1$ (Mathlib's `NumberField.dedekindZeta_residue`, given by the class number formula).
(The library proves this for its continuation `globalZetaCont`.) -/
theorem tate_globalZeta_residues {F : Type} [Field F] [NumberField F] (Φ : SchwartzBruhat F) (c : ℂ) :
    ∃ Z : ℂ → ℂ, Meromorphic Z ∧
      (∀ s : ℂ, 1 < s.re + (HeckeCharacter.normPow F c).shift →
        Z s = globalZeta (Φ : Adeles F → ℂ) (HeckeCharacter.normPow F c) s) ∧
      Tendsto (fun s => (s - (1 - c)) * Z s) (𝓝[≠] (1 - c)) (𝓝 (Φ.fourier 0 * dedekindZeta_residue F)) ∧
      Tendsto (fun s => (s + c) * Z s) (𝓝[≠] (-c)) (𝓝 (-((Φ : Adeles F → ℂ) 0 * dedekindZeta_residue F))) :=
  ⟨NumberFieldKB.GlobalZeta.globalZetaCont Φ (HeckeCharacter.normPow F c),
      NumberFieldKB.GlobalZeta.meromorphic_globalZetaCont Φ _,
      fun _ hs => NumberFieldKB.GlobalZeta.globalZetaCont_eq Φ _ hs,
      NumberFieldKB.GlobalZeta.tendsto_globalZetaCont_normPow_residue_one Φ c,
      NumberFieldKB.GlobalZeta.tendsto_globalZetaCont_normPow_residue_zero Φ c⟩

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set in
open Topology in
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil in
open scoped Classical ComplexConjugate in
open NumberFieldKB NumberFieldKB.HeckeL NumberFieldKB.GlobalZeta NumberFieldKB.LocalZeta in
/-- **Hecke $L$-functions** (Cassels–Fröhlich, Chapter XV, §4.5): for every Hecke character $\chi$ of a number field $F$,
the completed $L$-function $\Lambda(s, \chi)$ equals $A(\chi)^{s/2} L_\infty(s, \chi) L(s, \chi)$ for
$\operatorname{Re} s + \sigma > 1$ ($A(\chi) = |d_F| \cdot N\mathfrak f(\chi)$, $L(s, \chi)$ the Euler product over the finite
primes, $L_\infty$ the product of the archimedean Gamma factors), is holomorphic at every $s$ that is not a pole
(every $s$, unless $\chi = \|\cdot\|^c$; then $s \ne -c, 1 - c$), and satisfies
$\Lambda(s, \chi) = W(\chi) \Lambda(1 - s, \chi^{-1})$ with a root number of absolute value $1$ when $\chi$ is unitary. -/
theorem heckeL_functionalEquation {F : Type} [Field F] [NumberField F] (χ : HeckeCharacter F) :
    (∀ s : ℂ, 1 < s.re + χ.shift →
      completedHeckeL χ s = ((condDisc χ : ℝ) : ℂ) ^ (s / 2) * gammaInf χ s * heckeL χ s) ∧
    (∀ s : ℂ, IsPoleFree χ s → DifferentiableAt ℂ (completedHeckeL χ) s) ∧
    (∀ s : ℂ, IsPoleFree χ s → completedHeckeL χ s = rootNumber χ * completedHeckeL χ⁻¹ (1 - s)) ∧
    (χ.IsUnitary → ‖rootNumber χ‖ = 1) :=
  ⟨fun _ hs => NumberFieldKB.HeckeL.completedHeckeL_eq χ hs,
      fun _ hs => NumberFieldKB.HeckeL.differentiableAt_completedHeckeL hs,
      fun _ hs => NumberFieldKB.HeckeL.completedHeckeL_functional_equation χ hs,
      fun hχ => NumberFieldKB.HeckeL.norm_rootNumber hχ⟩

open NumberField Filter Topology in
/-- **The Dedekind zeta function** of a number field $F$ (Mathlib's `NumberField.dedekindZeta`, defined by its Dirichlet
series for $\operatorname{Re} s > 1$) extends to a function holomorphic on $\mathbb C \setminus \{1\}$, with residue at $s = 1$
equal to $2^{r_1}(2\pi)^{r_2} h_F R_F / (w_F \sqrt{|d_F|})$ (Mathlib's `NumberField.dedekindZeta_residue`): the class number
formula, read on the continuation. -/
theorem dedekindZeta_continuation (F : Type) [Field F] [NumberField F] :
    ∃ Z : ℂ → ℂ, (∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ Z s) ∧
      (∀ s : ℂ, 1 < s.re → Z s = dedekindZeta F s) ∧
      Tendsto (fun s => (s - 1) * Z s) (𝓝[≠] 1) (𝓝 (dedekindZeta_residue F : ℂ)) :=
  ⟨NumberFieldKB.HeckeL.dedekindZetaCont F, fun _ hs => NumberFieldKB.HeckeL.differentiableAt_dedekindZetaCont (F := F) hs,
      fun _ hs => NumberFieldKB.HeckeL.dedekindZetaCont_eq (F := F) hs,
      NumberFieldKB.HeckeL.tendsto_sub_one_mul_dedekindZetaCont (F := F)⟩

open NumberField NumberField.InfinitePlace Filter Topology in
/-- **The functional equation of the Dedekind zeta function** (Neukirch, *Algebraic Number Theory*, Chapter VII,
Corollary 5.11): for a number field $F$ with $r_1$ real and $r_2$ complex places, the function
$\Lambda_F(s) = |d_F|^{s/2}\,\Gamma_{\mathbb R}(s)^{r_1}\Gamma_{\mathbb C}(s)^{r_2}\zeta_F(s)$ ($\operatorname{Re} s > 1$) extends to a
function holomorphic on $\mathbb C \setminus \{0, 1\}$ with $\Lambda_F(1 - s) = \Lambda_F(s)$. Only Mathlib definitions occur. -/
theorem completedDedekindZeta_functionalEquation (F : Type) [Field F] [NumberField F] :
    ∃ Λ : ℂ → ℂ, (∀ s : ℂ, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ Λ s) ∧
      (∀ s : ℂ, 1 < s.re → Λ s = (((|(discr F : ℝ)| : ℝ)) : ℂ) ^ (s / 2) *
        (Complex.Gammaℝ s ^ nrRealPlaces F * Complex.Gammaℂ s ^ nrComplexPlaces F) * dedekindZeta F s) ∧
      ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s :=
  ⟨NumberFieldKB.HeckeL.completedDedekindZeta F,
      fun _ h0 h1 => NumberFieldKB.HeckeL.differentiableAt_completedDedekindZeta (F := F) h0 h1,
      fun _ hs => NumberFieldKB.HeckeL.completedDedekindZeta_eq (F := F) hs,
      fun _ h0 h1 => NumberFieldKB.HeckeL.completedDedekindZeta_one_sub (F := F) h0 h1⟩

/-! ## Pontryagin duality -/

open MeasureTheory Topology in
/-- **Pontryagin duality** (Folland, *A Course in Abstract Harmonic Analysis*, Theorem 4.32; Weil, *Basic Number
Theory*, Chapter II, §5): for every locally compact commutative Hausdorff topological group $G$, the canonical map
$G \to G^{**}$, $g \mapsto (\chi \mapsto \chi(g))$, is an isomorphism of topological groups. Only Mathlib definitions occur
(`PontryaginDual` is Mathlib's group of continuous characters to the circle, with the compact-open topology). -/
theorem pontryaginDuality {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G), ∀ (g : G) (χ : PontryaginDual G), e g χ = χ g :=
  by
    obtain ⟨e, he⟩ := NumberFieldKB.Pontryagin.Unconditional.pontryaginDuality (G := G)
    exact ⟨e, fun g χ => by rw [he]; rfl⟩

open MeasureTheory Topology in
open NumberFieldKB.Pontryagin in
/-- **Fourier inversion and the dual measure** (Weil, *Basic Number Theory*, Chapter VII, §2, p. 105): for every regular
Haar measure $\alpha$ on a locally compact commutative Hausdorff group $G$ there is a regular Haar measure $\beta$ on
$G^*$ (the dual measure) for which Fourier inversion $\Phi(g) = \int \Phi^*(g^*) \langle -g, g^* \rangle\,d\beta(g^*)$ holds for
every function $\Phi$ admissible for $G$ (integrable and continuous with integrable Fourier transform, the library's
`IsAdmissible`). -/
theorem fourierInversion_dualMeasure {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (α : Measure G) [α.IsHaarMeasure] [α.Regular]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)] :
    ∃ β : Measure (PontryaginDual G), β.IsHaarMeasure ∧ β.Regular ∧ IsDualMeasure α β :=
  NumberFieldKB.Pontryagin.Unconditional.exists_isDualMeasure α

open MeasureTheory Topology in
open NumberFieldKB.Pontryagin in
/-- **Closed subgroups and annihilators** (Weil, *Basic Number Theory*, Chapter II, §5, pp. 38–39): let $G$ be a locally
compact commutative Hausdorff group, $H$ a closed subgroup and $H^* \subseteq G^*$ its annihilator (the characters
trivial on $H$). Then the elements of $G$ on which every character of $H^*$ is trivial are exactly those of $H$; $H$ is
isomorphic, as a topological group, to the dual of $G^*/H^*$; $H$ is open if and only if $H^*$ is compact; $H$ is
compact if and only if $H^*$ is open; and $G/H$ is compact if and only if $H^*$ is discrete. -/
theorem pontryagin_closedSubgroups {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] (H : Subgroup G) [IsClosed (H : Set G)] :
    {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H ∧
    Nonempty (H ≃ₜ* PontryaginDual (PontryaginDual G ⧸ annihilator H)) ∧
    (IsOpen (H : Set G) ↔ IsCompact (annihilator H : Set (PontryaginDual G))) ∧
    (IsCompact (H : Set G) ↔ IsOpen (annihilator H : Set (PontryaginDual G))) ∧
    (CompactSpace (G ⧸ H) ↔ DiscreteTopology (annihilator H)) :=
  ⟨NumberFieldKB.Pontryagin.Unconditional.doubleAnnihilator_eq H,
      ⟨NumberFieldKB.Pontryagin.Unconditional.subgroupEquivDualQuotient H⟩,
      NumberFieldKB.Pontryagin.Unconditional.isOpen_iff_isCompact_annihilator H,
      NumberFieldKB.Pontryagin.Unconditional.isCompact_iff_isOpen_annihilator H,
      NumberFieldKB.Pontryagin.Unconditional.compactSpace_quotient_iff H⟩

open MeasureTheory Topology in
/-- **Compact and discrete groups are dual to each other** (Weil, *Basic Number Theory*, Chapter II, §5, p. 38): for a
locally compact commutative Hausdorff group $G$, $G$ is compact if and only if $G^*$ is discrete, and $G$ is discrete if
and only if $G^*$ is compact. (Mathlib has the directions from $G$ to $G^*$; the converses use the duality theorem.)
Only Mathlib definitions occur. -/
theorem compact_iff_dual_discrete {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] :
    (CompactSpace G ↔ DiscreteTopology (PontryaginDual G)) ∧
    (DiscreteTopology G ↔ CompactSpace (PontryaginDual G)) :=
  ⟨NumberFieldKB.Pontryagin.Unconditional.compactSpace_iff_discreteTopology_dual,
      NumberFieldKB.Pontryagin.Unconditional.discreteTopology_iff_compactSpace_dual⟩

/-! ## The modular curves X₀(N) -/

open NumberFieldKB.MilneEC NumberFieldKB.ModularCurves in
/-- **The genus of $X_0(N)$** (Milne, *Elliptic Curves*, Chapter V, §2): for $N \ge 1$, the function field
$\mathbb Q(X_0(N)) = \mathbb Q(j, j_N)$ has a genus $g$ in the sense of Riemann's theorem ($\ell(D) \ge \deg D + 1 - g$ for
every divisor $D$, with equality when $\deg D > 2g - 2$), and
$12 g = 12 + \mu - 3\nu_2 - 4\nu_3 - 6\nu_\infty$, where $\mu = [\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N)]$,
$\nu_2 = \prod_{p \mid N}(1 + \chi_4(p))$ (or $0$ if $4 \mid N$), $\nu_3 = \prod_{p \mid N}(1 + (p/3))$ (or $0$ if $9 \mid N$) and
$\nu_\infty = \sum_{d \mid N} \varphi(\gcd(d, N/d))$. (The library states the formula with its counts `nu2`, `nu3` of fixed
cosets; they are replaced here by their closed forms, proved in the library.) -/
theorem genus_X0 (N : ℕ) [NeZero N] :
    IsGenus ℚ (X0 N) (genus ℚ (X0 N)) ∧
    12 * genus ℚ (X0 N) = 12 + (CongruenceSubgroup.Gamma0 N).index -
      3 * (if 4 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + ZMod.χ₄ p)) -
      4 * (if 9 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + legendreSym 3 p)) -
      6 * ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d)) :=
  by
    refine ⟨NumberFieldKB.ModularCurves.isGenus_X0 N, ?_⟩
    rw [← NumberFieldKB.ModularCurves.nu2_eq_prod N, ← NumberFieldKB.ModularCurves.nu3_eq_prod N]
    exact NumberFieldKB.ModularCurves.genus_formula_X0 N

open UpperHalfPlane hiding I in
open Polynomial in
open NumberFieldKB.MilneEC.V in
/-- **The modular polynomial** (Milne, *Elliptic Curves*, Chapter V, Proposition 2.4): for $N \ge 1$ there is a monic
$F_N \in \mathbb Q[X][Y]$ of degree $[\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N)]$ in $Y$ with $F_N(j(z), j(Nz)) = 0$ for every $z$ in
the upper half plane, which divides every $G \in \mathbb C[X][Y]$ with $G(j(z), j(Nz)) = 0$ for all $z$ (so it is the
minimal polynomial of $j_N$ over $\mathbb C(j)$): the curve $X_0(N)$ is defined over $\mathbb Q$. (The library's statement is
the field of the structure `Prop2_4`, unfolded here.) -/
theorem modularPolynomial_rational {N : ℕ} (hN : 1 ≤ N) :
    ∃ F : Polynomial (Polynomial ℚ), F.Monic ∧
      F.natDegree = (CongruenceSubgroup.Gamma0 N).index ∧
      (∀ z, evalJJN N (F.map (Polynomial.mapRingHom (algebraMap ℚ ℂ))) z = 0) ∧
      ∀ G : Polynomial (Polynomial ℂ), (∀ z, evalJJN N G z = 0) →
        F.map (Polynomial.mapRingHom (algebraMap ℚ ℂ)) ∣ G :=
  (NumberFieldKB.ModularCurves.prop2_4 hN).exists_poly

open UpperHalfPlane hiding I in
open scoped UpperHalfPlane in
open Filter Polynomial in
open NumberFieldKB.MilneEC.V in
/-- **The function field of $X_0(N)$** (Milne, *Elliptic Curves*, Chapter V, Theorem 2.3): for $N \ge 1$, every modular
function $f$ for $\Gamma_0(N)$ (meromorphic on the upper half plane $\mathbb H$, invariant under $\Gamma_0(N)$, and
meromorphic at every cusp) agrees, off a discrete subset of $\mathbb H$, with $P(j, j_N)/Q(j, j_N)$ for polynomials
$P, Q \in \mathbb C[X][Y]$ with $Q(j, j_N)$ not identically zero, where $j_N(z) = j(Nz)$: the field of modular
functions for $\Gamma_0(N)$ is $\mathbb C(j, j_N)$. (The library's statement is the field of the structure `Thm2_3`,
unfolded here; `codiscrete ℍ` is Mathlib's filter of complements of closed discrete sets.) -/
theorem modularFunctions_Gamma0 (N : ℕ) (hN : 1 ≤ N) (f : ℍ → ℂ) (hf : IsModularFunction (CongruenceSubgroup.Gamma0 N) f) :
    ∃ P Q : Polynomial (Polynomial ℂ), (∃ z, evalJJN N Q z ≠ 0) ∧
      f =ᶠ[codiscrete ℍ] fun z ↦ evalJJN N P z / evalJJN N Q z :=
  NumberFieldKB.ModularCurves.thm2_3.rational N hN f hf

open NumberFieldKB.MilneEC NumberFieldKB.ModularCurves in
/-- **Cusp forms of weight 2 and the genus** (Milne, *Elliptic Curves*, Chapter V, Corollary 3.4): for $N \ge 1$, the
complex dimension of the space $S_2(\Gamma_0(N))$ of cusp forms of weight 2 for $\Gamma_0(N)$ (Mathlib's `CuspForm`)
equals the genus of $X_0(N)$, the genus of the function field $\mathbb Q(X_0(N))$ of the headline `genus_X0` (so
$\dim S_2(\Gamma_0(N)) = 1 + \mu/12 - \nu_2/4 - \nu_3/3 - \nu_\infty/2$). -/
theorem cuspForms_weightTwo_finrank (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2) : ℤ) =
      genus ℚ (X0 N) :=
  NumberFieldKB.ModularCurves.cor_3_4 N

/-! ## Milne, *Class Field Theory* -/

open NumberField IsDedekindDomain in
/-- **The Grunwald–Wang theorem** (Milne, *Class Field Theory*, Chapter VIII, Theorem 2.4): let $K$ be a number field,
$S$ a finite set of finite places and $T$ a finite set of infinite places, and for each $v \in S \cup T$ let
$\chi_v$ be a continuous character of finite order of $K_v^\times$; let $n$ be the least common multiple of their
orders. There is a continuous character $\psi$ of the idele class group $C_K$ whose restriction to $K_v^\times$ is
$\chi_v$ for all $v \in S \cup T$, and $\psi$ can be chosen of order exactly $n$ unless $2^t \mid n$ for some $t$
with $K(\zeta_{2^t})/K$ not cyclic (Wang's special case). (The library's named statement `Theorem2_4`, unfolded.) -/
theorem grunwaldWang {K : Type} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ)
    (hχ : ∀ v ∈ S, Continuous (χ v) ∧ IsOfFinOrder (χ v)) (hχ' : ∀ w ∈ T, Continuous (χ' w) ∧ IsOfFinOrder (χ' w))
    (n : ℕ) (hn : ∀ v ∈ S, orderOf (χ v) ∣ n) (hn' : ∀ w ∈ T, orderOf (χ' w) ∣ n)
    (hlcm : ∀ m : ℕ, (∀ v ∈ S, orderOf (χ v) ∣ m) → (∀ w ∈ T, orderOf (χ' w) ∣ m) → n ∣ m) :
    ∃ ψ : IdeleClassGroup (𝓞 K) K →* ℂˣ, Continuous ψ ∧
      (∀ v ∈ S, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)) = χ v) ∧
      (∀ w ∈ T, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofCompletion (𝓞 K) K w)) = χ' w) ∧
      ((∀ t : ℕ, 2 ^ t ∣ n →
          IsCyclic (CyclotomicField (2 ^ t) K ≃ₐ[K] CyclotomicField (2 ^ t) K)) → orderOf ψ = n) :=
  (NumberFieldKB.MilneCFT.Ch8.GW.theorem2_4 (K := K)).exists_char S T χ χ' hχ hχ' n hn hn' hlcm

open NumberField in
open NumberFieldKB.MilneCFT in
/-- **Central division algebras over a number field** (Milne, *Class Field Theory*, Chapter VIII, Theorem 2.6;
Albert, Brauer–Hasse–Noether): for every finite-dimensional central division algebra $D$ over a number field $K$, the
order of the class of $D$ in the Brauer group of $K$ is $\sqrt{[D:K]}$, and $D$ is a cyclic algebra: it contains a
cyclic extension $L$ of $K$ with $[L:K]^2 = [D:K]$, and is generated by $L$ and one element $\beta$ with
$\beta\alpha\beta^{-1} = \sigma(\alpha)$ for $\alpha \in L$ and $\beta^{[L:K]} = \gamma \in K^\times$, $\sigma$ a
generator of $\mathrm{Gal}(L/K)$. (The library's named statement `Theorem2_6`, unfolded; the Brauer group is the
library's `Ch4.BrauerGroup` of central simple algebras.) -/
theorem centralDivisionAlgebra_cyclic {K : Type} [Field K] [NumberField K] (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] :
    (orderOf (Ch4.BrauerGroup.mk (⟨.of K D⟩ : CSA.{0, 0} K))) ^ 2 = Module.finrank K D ∧
    ∃ (L : Subalgebra K D) (_ : IsField L), IsCyclic (L ≃ₐ[K] L) ∧ Nat.card (L ≃ₐ[K] L) = Module.finrank K L ∧
      (Module.finrank K L) ^ 2 = Module.finrank K D ∧
      ∃ (σ : L ≃ₐ[K] L) (β : D) (γ : K), Subgroup.zpowers σ = ⊤ ∧ γ ≠ 0 ∧
        β ^ Module.finrank K L = algebraMap K D γ ∧ (∀ α : L, β * (α : D) = (σ α : D) * β) ∧
        Algebra.adjoin K ((L : Set D) ∪ {β}) = ⊤ :=
  ⟨(NumberFieldKB.MilneCFT.Ch8.T26.theorem2_6 (K := K)).order_eq D,
    (NumberFieldKB.MilneCFT.Ch8.T26.theorem2_6 (K := K)).cyclic D⟩

open scoped ValuativeRel in
open NumberFieldKB.MilneCFT.LocalCFT in
/-- **The local Kronecker–Weber theorem** (Milne, *Class Field Theory*, Chapter I, Theorem 4.8): let $K$ be a
nonarchimedean local field (of any characteristic), $\Omega$ a separable closure and $\pi$ a prime element. Every
finite abelian extension $L$ of $K$ in $\Omega$ lies in $K_\pi K^{\mathrm{un}}$, the compositum of the Lubin–Tate
tower $K_\pi = \bigcup_n K(\Lambda_n)$ of $\pi$ (the fields generated by the $\pi^n$-torsion of a Lubin–Tate formal
group, the library's `ltTower`) and the maximal unramified extension. (The library's named statement
`LocalKroneckerWeber`, unfolded; its proof uses the Lubin–Tate extension theorem, Milne I.3.6, proved from a port of
Yamaguchi's library, and the local reciprocity law from a port of Tau Ceti.) -/
theorem localKroneckerWeber_lubinTate (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] {π : 𝒪[K]} (hπ : Irreducible π)
    (L : FiniteAbelianExt K Ω) :
    L.toField ≤ ltTower Ω π ⊔ unramifiedClosure K Ω :=
  (NumberFieldKB.MilneCFT.LocalCFT.localKroneckerWeber K Ω).le hπ L

open NumberField Ideal in
/-- **The Eisenstein reciprocity law** (Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Theorem
14.5.1; used by Milne, *Class Field Theory*, Chapter VIII, §5, for Theorem 5.14): let $p$ be an odd prime,
$K = \mathbb Q(\zeta_p)$, $a \in \mathbb Z$ prime to $p$ and $\alpha \in \mathcal O_K$ a primary non-unit prime to
$a$. Then $(\alpha/a)_p = (a/\alpha)_p$ for the $p$-th power residue symbols at the ideals $(a)$ and $(\alpha)$.
(Proved from the Hilbert reciprocity law for the idelic Artin map; the library's named statement
`EisensteinReciprocity`, unfolded.) -/
theorem eisensteinReciprocity (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (α : 𝓞 K) (a : ℤ) (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α)
    (hu : ¬ IsUnit α) (ha : ¬ (p : ℤ) ∣ a) (hcop : IsCoprime α (a : 𝓞 K)) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) :=
  NumberFieldKB.MilneCFT.Ch8.Eisenstein.eisensteinReciprocity.law p hp K hζ α a hα hu ha hcop

/-- **Furtwängler's theorem** (Milne, *Class Field Theory*, Chapter VIII, Theorem 5.14): let $p$ be an odd prime and
$x, y, z$ relatively prime positive integers with $p \nmid xyz$ and $x^p + y^p = z^p$. Then $q^{p-1} \equiv 1
\pmod{p^2}$ for every prime $q$ dividing $xyz$. (The library's named statement `Theorem5_14`, unfolded; proved from the
Eisenstein reciprocity law.) -/
theorem furtwangler_fermat (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgcd : Nat.gcd (Nat.gcd x y) z = 1) (hpxyz : ¬ p ∣ x * y * z) (hF : x ^ p + y ^ p = z ^ p)
    (q : ℕ) (hq : q.Prime) (hqxyz : q ∣ x * y * z) :
    q ^ (p - 1) ≡ 1 [MOD p ^ 2] :=
  NumberFieldKB.MilneCFT.Ch8.Eisenstein.theorem5_14.cong p hp hp2 x y z hx hy hz hgcd hpxyz hF q hq hqxyz

open NumberFieldKB.MilneCFT.Ch8 in
/-- **A theorem of Gauss** (Milne, *Class Field Theory*, Chapter VIII, §10; Silverman–Tate IV.2): let $N_p$ be the
number of points of the projective curve $X^3 + Y^3 + Z^3 = 0$ over $\mathbb F_p$, so that the number of nonzero
solutions in $\mathbb F_p^3$ (`cubicAffineCount p`) is $(p-1)N_p$. If $p \not\equiv 1 \pmod 3$ then $N_p = p + 1$;
if $p \equiv 1 \pmod 3$ then $N_p = p + 1 + A$, where $A$ is the unique integer $\equiv 1 \pmod 3$ with
$4p = A^2 + 27B^2$ for some integer $B$. (The library's named statement `GaussCubicCount`, unfolded.) -/
theorem gauss_cubicCurve_count (p : ℕ) [Fact p.Prime] :
    (p % 3 ≠ 1 → cubicAffineCount p = (p - 1) * (p + 1)) ∧
    (p % 3 = 1 → ∃ A B : ℤ, A % 3 = 1 ∧ 4 * p = A ^ 2 + 27 * B ^ 2 ∧
      (cubicAffineCount p : ℤ) = (p - 1) * (p + 1 + A) ∧
      ∀ A' B' : ℤ, A' % 3 = 1 → 4 * p = A' ^ 2 + 27 * B' ^ 2 → A' = A) :=
  ⟨NumberFieldKB.MilneCFT.Ch8.gaussCubicCount.not_one p, NumberFieldKB.MilneCFT.Ch8.gaussCubicCount.one p⟩

open NumberField in
open NumberFieldKB.MilneCFT in
/-- **Weber $L$-series** (Milne, *Class Field Theory*, Chapter V, Theorem 2.4(b), in the corrected form: the book says
"converges for $\mathrm{Re}(s) > 0$", which fails in general for $[K:\mathbb Q] \ge 2$; the author of this library
confirmed "extends" as the intended reading): for a modulus $\mathfrak m$ of a number field $K$ and a nontrivial
character $\chi$ of the ray class group $C_\mathfrak m$, the series
$L(s,\chi) = \sum_{(\mathfrak a,\mathfrak m_0) = 1}\chi(\mathfrak a)N\mathfrak a^{-s}$ (`weberLSeries`) extends to a
holomorphic function on $\mathrm{Re}(s) > 0$ whose value at $s = 1$ is nonzero. (The library's named statement
`Theorem2_4bExtends`, unfolded; proved from the Hecke $L$-function of the attached Hecke character of finite order.) -/
theorem weberL_continuation {K : Type} [Field K] [NumberField K] (m : Modulus K) (χ : RayClassGroup m →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → L s = weberLSeries m χ s) ∧ L 1 ≠ 0 :=
  (NumberFieldKB.MilneCFT.theorem_2_4b_extends K).extends_ m χ hχ

/-! ## Milne, *Elliptic Curves* -/

open MvPolynomial in
open scoped LinearAlgebra.Projectivization in
open NumberFieldKB.MilneEC in
/-- **Bézout's theorem** (Milne, *Elliptic Curves*, Theorem I.1.18): two projective plane curves $F$, $G$ over a
field $k$ with no common component meet in finitely many points of $\mathbb P^2(k^{\mathrm{al}})$, and the sum of
the intersection numbers at these points is $\deg F \cdot \deg G$. (The library's named statement `Thm1_18`,
unfolded; proved by Fulton's dimension count, *Algebraic Curves*, Chapter 5.) -/
theorem bezout (k : Type) [Field k] (F G : MvPolynomial (Fin 3) k)
    (hF : IsProjectivePlaneCurve F) (hG : IsProjectivePlaneCurve G) (hFG : NoCommonComponent F G) :
    ∃ S : Finset (ℙ (AlgebraicClosure k) (Fin 3 → AlgebraicClosure k)),
      (S : Set _) = projectivePoints F (AlgebraicClosure k) ∩ projectivePoints G (AlgebraicClosure k) ∧
      ∑ P ∈ S, projIntersectionNumber F G P = curveDegree F * curveDegree G :=
  NumberFieldKB.MilneEC.thm1_18.bezout k F G hF hG hFG

open MvPolynomial in
open scoped LinearAlgebra.Projectivization in
open NumberFieldKB.MilneEC in
/-- **The group law on a plane cubic** (Milne, *Elliptic Curves*, Theorem I.3.1): for a nonsingular projective plane
cubic $C$ over a perfect field $k$ and a point $O \in C(k)$, the chord-tangent addition (the third point of the line
through $O$ and the third point of the line through $P$ and $Q$) is associative. The cubic need not be in Weierstrass
form. (The library's named statement `Thm3_1`, unfolded; proved by Fulton's argument from Bézout's theorem and the
nine-point lemma with multiplicities.) -/
theorem chordTangent_assoc (k : Type) [Field k] [PerfectField k] (F : MvPolynomial (Fin 3) k)
    (hF : IsNonsingularCubic F) (O P Q R : CurvePoints F) :
    chordAdd hF O (chordAdd hF O P Q) R = chordAdd hF O P (chordAdd hF O Q R) :=
  NumberFieldKB.MilneEC.thm3_1.assoc k F hF O P Q R

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Proposition IV.5.5** (Milne, *Elliptic Curves*), with Mordell's theorem for these curves: for distinct integers
$\alpha, \beta, \gamma$ and $E : Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$ over $\mathbb Q$, the group
$E(\mathbb Q)$ is finitely generated and its rank is at most twice the number of primes dividing $2\Delta$,
$\Delta = (\alpha - \beta)^2(\beta - \gamma)^2(\gamma - \alpha)^2$. Proved by Milne's explicit descent: the map
$x - T$ of Remark IV.3.7 makes $E(\mathbb Q)/2E(\mathbb Q)$ finite, and the canonical height gives finite generation;
no Selmer group is used. (`rank` is `Module.finrank ℤ` of the group of rational points.) -/
theorem rank_bound_twoDescent (α β γ : ℤ) (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) :
    AddGroup.FG (cubicCurve α β γ).toAffine.Point ∧
      rank (cubicCurve α β γ) ≤ 2 * (2 * cubicDisc α β γ).natAbs.primeFactors.card :=
  ⟨NumberFieldKB.MilneEC.fg_cubicCurve hαβ hβγ hγα,
      NumberFieldKB.MilneEC.prop_5_5_rank_unconditional hαβ hβγ hγα⟩

/-- **Example IV.5.7** (Milne, *Elliptic Curves*): for $E : Y^2 = X^3 - X$ over $\mathbb Q$,
$E(\mathbb Q) \cong (\mathbb Z/2\mathbb Z)^2$ (the points $O$, $(0,0)$, $(\pm1,0)$); in particular the rank is $0$.
Proved by Milne's explicit 2-descent (the map $x - T$ of Remark IV.3.7 and the bound of Proposition IV.5.6) and
reduction modulo 3. The curve is Mathlib's Weierstrass curve with $a_4 = -1$ and the other coefficients $0$. -/
theorem points_x3_sub_x : Nonempty ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).toAffine.Point ≃+ ZMod 2 × ZMod 2) :=
  by
    have h : NumberFieldKB.MilneEC.cubicCurve (-1) 0 1 = ⟨0, 0, 0, -1, 0⟩ := by
      simp only [NumberFieldKB.MilneEC.cubicCurve, WeierstrassCurve.mk.injEq]; norm_num
    rw [← h]
    exact NumberFieldKB.MilneEC.example_5_7_unconditional.2

/-- **$1$ is not a congruent number** (Milne, *Elliptic Curves*, Introduction, with Example IV.5.7): there is no right
triangle with rational sides and area $1$. A triangle gives a rational point of $Y^2 = X^3 - X$ with $Y \ne 0$,
which Example IV.5.7 excludes. -/
theorem one_not_congruent : ¬ ∃ x y z : ℚ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ x * y / 2 = 1 :=
  fun ⟨x, y, z, hx, hy, hz, h, ha⟩ =>
    NumberFieldKB.MilneEC.not_isCongruentNumber_one ⟨x, y, z, hx, hy, hz, h, by rw [ha]; norm_num⟩

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Lang's theorem for elliptic curves** (Milne, *Elliptic Curves*, Proposition IV.9.2): for an elliptic curve $E$
over a finite field $k$, $H^1(k, E) = 0$, where $H^1$ is the group of continuous crossed homomorphisms of the absolute
Galois group $\mathrm{Gal}(k^{\mathrm{al}}/k)$ into $E(k^{\mathrm{al}})$ modulo the principal ones (`ContH1`).
Milne reduces it to the surjectivity of $P \mapsto \varphi(P) - P$ ($\varphi$ the Frobenius map); here that
surjectivity is proved from the divisibility of $E(k^{\mathrm{al}})$ (Lemma IV.2.1, in every characteristic) by
counting on the finite groups $E(\mathbb F_{q^m})$, instead of Milne's appeal to Proposition I.4.23. -/
theorem lang_H1_eq_zero (k : Type) [Field k] [Fintype k] (W : WeierstrassCurve k) [W.IsElliptic]
    (c : ContH1 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
    c = 0 :=
  NumberFieldKB.MilneEC.prop_9_2_unconditional k W c

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Milne's Conjecture IV.10.5 against Formal Conjectures** (conditional on three named comparison statements; no
conjecture is assumed): for an elliptic curve $E$ over $\mathbb Q$ given by a minimal equation, Milne's form of the
conjecture of Birch and Swinnerton-Dyer, with the height pairing normalized as in the standard regulator
(`Conjecture10_5Corrected`: Milne's printed constant divided by $2^r$; as printed, Milne's pairing is twice the
standard one), is equivalent to Formal Conjectures' `StrongBSD`. The named inputs, not proved here: the two
formalizations of the Tate–Shafarevich group are isomorphic (`ShaComparison`), Milne's period $\Omega$ is Formal
Conjectures' global period for a minimal equation (`PeriodComparison`), and Milne's product of the Tamagawa numbers
at the bad primes is Formal Conjectures' Tamagawa product (`TamagawaComparison`). The finite generation of
$E(\mathbb Q)$ (Mordell's theorem) is an instance argument, as in Formal Conjectures. -/
theorem bsd_milne_iff_strongBSD (E : WeierstrassCurve ℚ) [E.IsElliptic] [Module.Finite ℤ E.toAffine.Point]
    (hSha : ShaComparison) (hΩ : PeriodComparison) (hc : TamagawaComparison) (hmin : IsMinimalOverRat E) :
    Conjecture10_5Corrected E ↔ NumberFieldKB.FormalConjectures.StrongBSD E.toAffine :=
  NumberFieldKB.MilneEC.conjecture10_5Corrected_iff_strongBSD E hSha hΩ hc hmin

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Propositions IV.8.1 and IV.8.2** (Milne, *Elliptic Curves*; Silverman, *The Arithmetic of Elliptic Curves*,
X.6.2): let $p \equiv 1 \pmod 8$ be a prime and $E : Y^2 = X^3 + pX$ over $\mathbb Q$. Then the $2$-Selmer group
$S^{(2)}(E/\mathbb Q)$ is isomorphic to $(\mathbb Z/2)^3$; if moreover $2$ is not a fourth power modulo $p$, then
$E(\mathbb Q)$ has rank $0$ and the $2$-torsion of the Tate–Shafarevich group, $Ш(E/\mathbb Q)[2]$, is isomorphic to
$(\mathbb Z/2)^2$. The Selmer and Tate–Shafarevich groups are Milne's: continuous classes in
$H^1(\operatorname{Gal}(\mathbb Q^{\mathrm{al}}/\mathbb Q), -)$ whose images in $H^1(\mathbb Q_v, E)$ vanish at every place
$v$, finite and infinite. Proved directly on the Galois-cohomological Selmer group, by Kummer theory for
$\mathbb Z/2$ and the local conditions at $2$, $p$ and $\infty$. (The library's statements are the fields of the
structures `Prop8_1` and `Prop8_2`, unfolded here; `rank` is `Module.finrank ℤ` of the group of rational points.) -/
theorem selmer_sha_x3_add_px (p : ℕ) (hp : p.Prime) (h8 : p % 8 = 1) :
    Nonempty (selmerGroup ℚ (curveP p) 2 ≃+ (Fin 3 → ZMod 2)) ∧
      ((¬ ∃ x : ZMod p, x ^ 4 = 2) →
        rank (curveP p) = 0 ∧ Nonempty (shaTwoTorsion (curveP p) ≃+ (Fin 2 → ZMod 2))) :=
  ⟨NumberFieldKB.MilneEC.prop_8_1.selmer p hp h8, fun h4 =>
      ⟨NumberFieldKB.MilneEC.prop_8_2.rank_eq_zero p hp h8 h4, NumberFieldKB.MilneEC.prop_8_2.sha_two p hp h8 h4⟩⟩

open MeasureTheory QuadFormsKB.Analysis in
open scoped ENNReal in
open NumberFieldKB.MilneEC.LocalPeriod in
/-- **The local measure of $E_0(\mathbb Q_p)$** (Milne, *Elliptic Curves*, Remark IV.10.6 (a), the step that does
not involve $c_p$): let $p$ be an odd prime and $W$ a minimal Weierstrass equation over $\mathbb Q_p$, with good,
multiplicative or additive reduction. Then $\int_{E_0(\mathbb Q_p)}|\omega|_p = N_p/p$, where
$\omega = dx/(2y + a_1x + a_3)$, $E_0(\mathbb Q_p)$ is the set of points with non-singular reduction and $N_p$ is the
number of non-singular points of the reduction over $\mathbb F_p$ (Mathlib's `Point` type of `W.reduction`, which
includes the point at infinity). The measure is read on the $x$-line: `omegaDensity W x` is the number of square
roots $\psi$ of $\Psi_2^2(x) = 4x^3 + b_2x^2 + 2b_4x + b_6$ in $\mathbb Q_p$ divided by $|\psi|_p$, `zeroComponentX W`
is the image of $E_0(\mathbb Q_p)$ under $x$, and `haarP p` is the Haar measure on $\mathbb Q_p$ with
$\operatorname{vol}(\mathbb Z_p) = 1$ (from quadratic-forms-lean). -/
theorem omega_measure_zeroComponent (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p]) [W.IsMinimal ℤ_[p]] :
    ∫⁻ x in zeroComponentX W, omegaDensity W x ∂haarP p =
      (Nat.card (W.reduction ℤ_[p]).toAffine.Point : ℝ≥0∞) / p :=
  NumberFieldKB.MilneEC.LocalPeriod.omegaVolume_zeroComponent hp2 W

open MeasureTheory QuadFormsKB.Analysis in
open scoped ENNReal in
open NumberFieldKB.MilneEC.LocalPeriod in
/-- **The local Tamagawa measure at good reduction** (Milne, *Elliptic Curves*, Remark IV.10.6 (a)): for an odd
prime $p$ and a Weierstrass equation $W$ over $\mathbb Q_p$ with good reduction (Mathlib's `HasGoodReduction`, which
includes minimality), $\int_{E(\mathbb Q_p)}|\omega|_p = c_p N_p/p$, with $c_p$ the local Tamagawa number of Formal
Conjectures (`tamagawaNumber`, the number of translates of $E_0(\mathbb Q_p)$; here $c_p = 1$) and
$N_p = \#\tilde E(\mathbb F_p)$. The measure `omegaVolume W` is the integral of `omegaDensity W` over $\mathbb Q_p$ for
the Haar measure with $\operatorname{vol}(\mathbb Z_p) = 1$ (see `omega_measure_zeroComponent`). -/
theorem omega_measure_goodReduction (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p]) [W.HasGoodReduction ℤ_[p]] :
    omegaVolume W = (NumberFieldKB.FormalConjectures.tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective :
      ℝ≥0∞) * Nat.card (W.reduction ℤ_[p]).toAffine.Point / p :=
  NumberFieldKB.MilneEC.LocalPeriod.remark_10_6_a_good_cp hp2 W

open NumberFieldKB.MilneEC.III in
/-- **The real period through the uniformization** (Milne, *Elliptic Curves*, the period $\Omega$ of Conjecture
IV.10.5, through Chapter III): for every elliptic curve $W$ over $\mathbb R$ there is a lattice $\Lambda$ with real
invariants $g_2, g_3$ (Mathlib's `PeriodPair`) and a change of variables with $u = 1$ taking $W$ to
$E(\Lambda) : y^2 = x^3 - \tfrac{g_2}4x - \tfrac{g_3}4$; for it, the real period of Formal Conjectures,
$\Omega(W) = \int_{E(\mathbb R)}|\omega| = 2\int_{\mathbb R}dx/\sqrt{\Psi_2^2(x)}$, equals the number of connected
components of $E(\mathbb R)$ (2 if $\Delta > 0$, else 1) times the least positive real element of $\Lambda$. Proved
by the substitution $x = \wp(t)$. -/
theorem realPeriod_eq_latticePeriod (W : WeierstrassCurve ℝ) [W.IsElliptic] :
    ∃ L : PeriodPair, HasRealInvariants L ∧
      ∃ C : WeierstrassCurve.VariableChange ℝ, C.u = 1 ∧ C • W = realCurveOf L ∧
        NumberFieldKB.FormalConjectures.realPeriod W = realComponentCount W * leastRealPeriod L :=
  NumberFieldKB.MilneEC.III.rp1_real_period W

/-- **Mazur's list is attained** (Milne, *Elliptic Curves*, Remark II.5.11, the realization half; Mazur's theorem,
the other half, is not formalized): each of the groups $\mathbb Z/m$ ($1 \le m \le 10$ or $m = 12$) and
$\mathbb Z/2 \times \mathbb Z/2m$ ($1 \le m \le 4$) is the torsion subgroup of $E(\mathbb Q)$ for an explicit
elliptic curve $E$ over $\mathbb Q$. For each curve the torsion is computed by exhibiting points of the right orders
and bounding the torsion by reduction modulo a prime of good reduction. -/
theorem mazur_torsion_realized :
    (∀ m : ℕ, (1 ≤ m ∧ m ≤ 10 ∨ m = 12) → ∃ W : WeierstrassCurve ℚ, W.IsElliptic ∧
        Nonempty (AddCommGroup.torsion W.toAffine.Point ≃+ ZMod m)) ∧
      ∀ m : ℕ, 1 ≤ m ∧ m ≤ 4 → ∃ W : WeierstrassCurve ℚ, W.IsElliptic ∧
        Nonempty (AddCommGroup.torsion W.toAffine.Point ≃+ ZMod 2 × ZMod (2 * m)) :=
  NumberFieldKB.MilneEC.II.mazur_groups_realized

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Milne's Conjecture IV.10.5 against Formal Conjectures, over $\mathbb Q$** (conditional on one named local
statement; no conjecture is assumed): for an elliptic curve $E$ over $\mathbb Q$ given by a minimal equation,
Milne's form of the conjecture of Birch and Swinnerton-Dyer with the standard normalization of the height pairing
(`Conjecture10_5Corrected`) is equivalent to Formal Conjectures' `StrongBSD`. Unlike `bsd_milne_iff_strongBSD`, the
finite generation of $E(\mathbb Q)$ is the library's Mordell–Weil theorem over $\mathbb Q$ (`mordell_weil_rat`, by
Milne's descent), not an instance argument; the period and Tamagawa comparisons are proved; and the comparison of the
two Tate–Shafarevich groups is proved from one named input, `LocalPointsInjective`: at every place $v$ of
$\mathbb Q$, a continuous class of $\operatorname{Gal}(\bar{\mathbb Q}_v/\mathbb Q_v)$ with values in
$E(\bar{\mathbb Q})$ that becomes trivial in $E(\bar{\mathbb Q}_v)$ is trivial (Milne, *Arithmetic Duality
Theorems*, Remark I.3.10, by Greenberg approximation at the finite places). -/
theorem bsd_milne_iff_strongBSD_rat (E : WeierstrassCurve ℚ) [E.IsElliptic] (hloc : LocalPointsInjective) (hmin : IsMinimalOverRat E) :
    haveI := NumberFieldKB.MilneEC.mordell_weil_rat E
    Conjecture10_5Corrected E ↔ NumberFieldKB.FormalConjectures.StrongBSD E.toAffine :=
  NumberFieldKB.MilneEC.conjecture10_5Corrected_iff_strongBSD_of_localPointsInjective E hloc hmin

open MeasureTheory QuadFormsKB.Analysis in
open scoped ENNReal in
open NumberFieldKB.MilneEC.LocalPeriod in
/-- **The local Tamagawa measure at every reduction type** (Milne, *Elliptic Curves*, Remark IV.10.6 (a);
conditional on one named input): for an odd prime $p$ and a minimal equation $W$ of an elliptic curve over
$\mathbb Q_p$, $\int_{E(\mathbb Q_p)}|\omega|_p = c_p N_p/p$, with $c_p$ Formal Conjectures' local Tamagawa number
and $N_p$ the number of non-singular points of the reduction. The named input `ZeroComponentIndex` is Milne's first
step, $\int_{E(\mathbb Q_p)}|\omega|_p = c_p\int_{E_0(\mathbb Q_p)}|\omega|_p$ ($|\omega|_p$ is invariant under
translation and $E(\mathbb Q_p)$ is the union of $c_p$ translates of $E_0(\mathbb Q_p)$); the second step,
$\int_{E_0(\mathbb Q_p)}|\omega|_p = N_p/p$, is the unconditional headline `omega_measure_zeroComponent`. -/
theorem omega_measure_of_zeroComponentIndex (hI : ZeroComponentIndex) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p])
    [W.IsElliptic] [W.IsMinimal ℤ_[p]] :
    omegaVolume W = (NumberFieldKB.FormalConjectures.tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective :
      ℝ≥0∞) * Nat.card (W.reduction ℤ_[p]).toAffine.Point / p :=
  NumberFieldKB.MilneEC.LocalPeriod.remark_10_6_a_of_index hI hp2 W

end NumberFieldKB.Headlines
