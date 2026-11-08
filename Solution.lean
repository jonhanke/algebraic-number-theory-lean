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

/-!
# Headline statements of NumberFieldKB 0.1.0, proved

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

end NumberFieldKB.Headlines
