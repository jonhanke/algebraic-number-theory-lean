import NumberFieldKB.MilneCFT.Intro.RayClass
import NumberFieldKB.MilneCFT.Ch6.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Milne, *Class Field Theory*, Chapter VI §2: partial zeta functions of ray classes

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

For a modulus $\mathfrak m$ of a number field $K$ and a class $k\in C_\mathfrak m$ (`RayClassGroup m`, Introduction):

* `partialZeta m k s` $= \zeta(s,k) = \sum_{\mathfrak a\in k}N\mathfrak a^{-s}$, the sum over the integral ideals in
  $k$ (definition in prose, p. 189); `idealCount m k x` $= S(x,k)$.
* The regulator $\mathrm{reg}(K)$ (definition in prose, p. 189) is Mathlib's `NumberField.Units.regulator`, the
  covolume of the logarithmic unit lattice `unitLattice`; `unitsMod m` $= U_{\mathfrak m,1} = U\cap K_{\mathfrak m,1}$,
  and `regulatorMod m` $= \mathrm{reg}(\mathfrak m)$, the covolume of its logarithmic image (definition in prose, p. 189).
* `rayResidue m` $= g_\mathfrak m$ and **Proposition 2.8** (`Prop2_8`, named statement, Lang's lattice point count):
  $|S(x,k) - g_\mathfrak m x|\le Cx^{1-1/d}$.

**Erratum (p. 189).** Milne writes $\mathrm{reg}(\mathfrak m) = \mathrm{reg}(K)(U : U(\mathfrak m))$. The index of
the lattice $l(U_{\mathfrak m,1})$ in $l(U)$ is $(U : U_{\mathfrak m,1}\mu_K) = (U:U_{\mathfrak m,1})\,w_\mathfrak m/w_K$
(the kernel of $l$ is the torsion), so $\mathrm{reg}(\mathfrak m) = \mathrm{reg}(K)(U:U_{\mathfrak m,1})w_\mathfrak m/w_K$.
The formula for $g_\mathfrak m$ is stated in terms of $\mathrm{reg}(\mathfrak m)$ and $w_\mathfrak m$ and is not affected.
Also, $\sum_{k\in C_\mathfrak m}\zeta(s,k)$ is $\zeta_K(s)\prod_{\mathfrak p\mid\mathfrak m_0}(1-N\mathfrak p^{-s})$
(only ideals prime to $\mathfrak m_0$ occur), equal to $\zeta_K(s)$ only when $\mathfrak m_0 = 1$, as in Corollary 2.12.
-/

open NumberField IsDedekindDomain NumberField.Units NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open scoped Classical

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6

variable {K : Type} [Field K] [NumberField K]

/-- **The partial zeta function** of a ray class (Milne, *CFT*, Chapter VI, p. 189): for $k\in C_\mathfrak m$,
$\zeta(s,k) = \sum N\mathfrak a^{-s}$, the sum over the nonzero integral ideals $\mathfrak a$ prime to $\mathfrak m_0$
whose class in $C_\mathfrak m$ is $k$. -/
@[kb "milne2020cft" "Ch. VI, §2, p. 189 (partial zeta function ζ(s, k))"]
def partialZeta (m : Modulus K) (k : RayClassGroup m) (s : ℂ) : ℂ :=
  ∑' 𝔞 : Ideal (𝓞 K),
    if h : 𝔞 ≠ ⊥ ∧ 𝔞 ⊔ m.finite = ⊤ then
      (if idealRayClass m 𝔞 h.1 h.2 = k then ((Ideal.absNorm 𝔞 : ℕ) : ℂ) ^ (-s) else 0)
    else 0

/-- $S(x,k)$ (Milne, *CFT*, Chapter VI, p. 189): the number of integral ideals $\mathfrak a\in k$ with
$N\mathfrak a\le x$. -/
def idealCount (m : Modulus K) (k : RayClassGroup m) (x : ℝ) : ℕ :=
  Set.ncard {𝔞 : Ideal (𝓞 K) | ∃ h : 𝔞 ≠ ⊥ ∧ 𝔞 ⊔ m.finite = ⊤,
    idealRayClass m 𝔞 h.1 h.2 = k ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x}

/-- **The regulator** of $K$ (Milne, *CFT*, Chapter VI, p. 189): the volume of a fundamental parallelepiped of the
lattice $l(U)\subset\mathbb R^{r+s-1}$, $l(u) = (\log|\sigma_1u|,\dots,2\log|\sigma_{r+s}u|)$ (one coordinate
dropped). Mathlib's `NumberField.Units.regulator` (covolume of `unitLattice`). -/
@[kb "milne2020cft" "Ch. VI, §2, p. 189 (regulator reg(K))"]
theorem regulator_def : regulator K = ZLattice.covolume (unitLattice K) := rfl

/-- $U_{\mathfrak m,1} = U\cap K_{\mathfrak m,1}$ (Milne, *CFT*, Chapter VI, p. 189): the units $u$ of $\mathcal O_K$
with $u\equiv1\bmod^\times\mathfrak m$. -/
def unitsMod (m : Modulus K) : Subgroup (𝓞 K)ˣ :=
  (congruenceSubgroup m).comap (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K))

/-- **The regulator $\mathrm{reg}(\mathfrak m)$** (Milne, *CFT*, Chapter VI, p. 189): the volume of a fundamental
parallelepiped of the lattice $l(U_{\mathfrak m,1})$, i.e. the covolume of the span of its logarithmic image. -/
@[kb "milne2020cft" "Ch. VI, §2, p. 189 (regulator reg(m) of U_{m,1})"]
def regulatorMod (m : Modulus K) : ℝ :=
  ZLattice.covolume (Submodule.span ℤ
    ((fun u : (𝓞 K)ˣ => logEmbedding K (Additive.ofMul u)) '' (unitsMod m : Set (𝓞 K)ˣ)))

/-- $w_\mathfrak m$: the number of roots of unity in $K_{\mathfrak m,1}$ (the torsion of $U_{\mathfrak m,1}$). -/
def rootsOfUnityMod (m : Modulus K) : ℕ :=
  Nat.card {u : (𝓞 K)ˣ // u ∈ unitsMod m ∧ u ∈ torsion K}

/-- $N(\mathfrak m) = N(\mathfrak m_0)\,2^{r_0}$, $r_0$ the number of real primes in $\mathfrak m_\infty$. -/
def modulusNorm (m : Modulus K) : ℕ := Ideal.absNorm m.finite * 2 ^ m.infinite.ncard

/-- **The constant** $g_\mathfrak m = \dfrac{2^r(2\pi)^s\,\mathrm{reg}(\mathfrak m)}{w_\mathfrak m N(\mathfrak m)
|\Delta_{K/\mathbb Q}|^{1/2}}$ of Proposition 2.8 ($r$, $s$ the numbers of real and complex primes). -/
def rayResidue (m : Modulus K) : ℝ :=
  2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * regulatorMod m /
    (rootsOfUnityMod m * modulusNorm m * Real.sqrt |(discr K : ℝ)|)

variable (K) in
/-- **Proposition 2.8** (named statement; Milne, *CFT*, Chapter VI, p. 189, proof in Lang, *Algebraic Number Theory*,
VI.3, Theorem 3): for every modulus $\mathfrak m$, every class $k\in C_\mathfrak m$ and all $x\ge1$,
$|S(x,k) - g_\mathfrak m x|\le Cx^{1-1/d}$, $d = [K:\mathbb Q]$, for a constant $C$ (depending on $\mathfrak m$ and
$k$). -/
@[kb "milne2020cft" "Ch. VI, Prop. 2.8 (input)"]
structure Prop2_8 : Prop where
  bound : ∀ (m : Modulus K) (k : RayClassGroup m), ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    |(idealCount m k x : ℝ) - rayResidue m * x| ≤ C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ))

end NumberFieldKB.MilneCFT.Ch6
