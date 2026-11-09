import NumberFieldKB.MilneCFT.Ch5IdelesChar

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 4.8, corrected and proved

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Remark 4.8, p. 174
(after Tate 1967, Proposition 4.1 [unverified locator]).

Remark 4.8 as printed (named statement `Remark4_8`) has two sentences.

1. *Extension.* "Every admissible $\psi : I^S \to G$ defines a homomorphism $\varphi : \mathbb I_K \to G$ satisfying
   (a), (b), (c) of Proposition 4.7", for every commutative topological group $G$. This is false without completeness
   (`not_remark4_8_rat`, $G = \mathbb Z/2$ indiscrete); the missing hypothesis, confirmed by Jon Hanke (2026-11-08), is
   that $G$ is **complete**, which in Milne's (Bourbaki's) usage includes Hausdorff. Mathlib's `CompleteSpace` does not
   include Hausdorff (the indiscrete $\mathbb Z/2$ of the counterexample is a complete uniform group), so the corrected
   statement assumes `[CompleteSpace G] [T2Space G]`.
2. *Converse.* "If $G$ is complete and has no small subgroups, every continuous $\varphi$ trivial on $K^\times$ arises
   from an admissible $\psi$." With Milne's admissibility (by moduli, which only make $a$ positive at the real places,
   not close to $1$ at the infinite places) this is false for Hecke characters of nontrivial infinity type:
   $K = \mathbb Q$, $G$ the circle, $\varphi = \|\cdot\|^{it}$ ($t \ne 0$) forces $\psi(p) = p^{-it}$, and
   $\psi((a)) = a^{-it}$, $a \equiv 1 \bmod \mathfrak m$, is dense in the circle (`not_remark4_8_converse_rat`, in
   `Ch5Remark48ConverseCounter.lean`). The converse holds exactly when $\varphi$ is also trivial on the identity
   component of $K_\infty^\times$ (the idèles that are $1$ at every finite place and positive at the real places):
   necessity because admissibility and weak approximation force $\varphi$ to be arbitrarily close to $1$ there.

**Proved** in `Ch5Remark48Uncond.lean` (`remark4_8_corrected : Remark4_8Corrected K`): the extension for $G$ complete Hausdorff, and the
converse for $G$ complete with no small subgroups and $\varphi$ trivial on the identity component of
$K_\infty^\times$.

*Proof of the extension.* On the subgroup $H = K^\times \cdot \mathbb I_S$ ($\mathbb I_S$ the idèles that are $1$ at
$S$ and at the infinite places; $K^\times \cap \mathbb I_S = 1$) put $\varphi_0(a x) = \psi(\mathrm{id}(x))$.
Admissibility says exactly that $\varphi_0$ is continuous at $1$ for the topology induced from $\mathbb I_K$
($\varphi_0(ax) = \psi((a))^{-1}$ when $ax$ is close to $1$ at $S$, positive at the real places and a unit outside
$S$). $H$ is dense in $\mathbb I_K$ by weak approximation, and a homomorphism continuous at $1$ on a dense subgroup with
values in a complete Hausdorff commutative group extends to a continuous homomorphism (uniform continuity).

*Proof of the converse.* As for Proposition 4.7 (`prop_4_7_converse`): no small subgroups gives an open subgroup of the
unit idèles on which $\varphi$ is trivial; with the hypothesis at the infinite places, $\varphi$ is trivial on the
idèles positive at the real places, close to $1$ at a finite set $T$ and units elsewhere, so the induced
$\psi : I^T \to G$ is trivial on $i(K_{\mathfrak m,1})$ for a modulus $\mathfrak m$ supported on $T$, hence
admissible.
-/

open NumberField IsDedekindDomain Topology
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

/-- The second sentence of **Remark 4.8** as printed and formalized (the `converse` field of `Remark4_8`). False for
$K = \mathbb Q$ (`not_remark4_8_converse_rat`). -/
def Remark4_8Converse : Prop :=
  ∀ (G : Type) [CommGroup G] [UniformSpace G] [IsUniformGroup G] [CompleteSpace G],
    NoSmallSubgroups G → ∀ φ : IdeleGroup (𝓞 K) K →* G, Continuous φ →
      (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) →
      ∃ (S : Set (HeightOneSpectrum (𝓞 K))) (_ : S.Finite) (ψ : sIdeals S →* G), IsAdmissible S ψ ∧
        ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
          φ x = ψ b

/-- **Remark 4.8, corrected** (Milne, *CFT*, V, Remark 4.8, p. 174; Tate 1967, Prop. 4.1 [unverified locator]).
(1) For a commutative topological group $G$ that is **complete and Hausdorff** (the missing hypothesis, confirmed by
Jon Hanke, 2026-11-08), every admissible $\psi : I^S \to G$ ($S$ finite) defines a continuous $\varphi : \mathbb I_K \to
G$, trivial on $K^\times$, with $\varphi(x) = \psi(\mathrm{id}(x))$ for $x$ equal to $1$ at $S$ and at the infinite
places ((a), (b), (c) of Proposition 4.7). (2) If $G$ is complete and has no small subgroups, every continuous
$\varphi : \mathbb I_K \to G$ trivial on $K^\times$ **and on the identity component of $K_\infty^\times$** (the idèles
equal to $1$ at the finite places and positive at the real places; this hypothesis is missing in the printed remark,
see `not_remark4_8_converse_rat`) arises from an admissible $\psi$. -/
@[kb "milne2020cft" "Ch. V, Remark 4.8 (corrected: G complete Hausdorff; converse for phi trivial on the identity component at infinity)"]
structure Remark4_8Corrected : Prop where
  extend : ∀ (G : Type) [CommGroup G] [UniformSpace G] [IsUniformGroup G] [CompleteSpace G] [T2Space G]
    (S : Set (HeightOneSpectrum (𝓞 K))) (ψ : sIdeals S →* G), S.Finite → IsAdmissible S ψ →
      ∃ φ : IdeleGroup (𝓞 K) K →* G, Continuous φ ∧ (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
        ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
          φ x = ψ b
  converse : ∀ (G : Type) [CommGroup G] [UniformSpace G] [IsUniformGroup G] [CompleteSpace G],
    NoSmallSubgroups G → ∀ φ : IdeleGroup (𝓞 K) K →* G, Continuous φ →
      (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) →
      (∀ x : IdeleGroup (𝓞 K) K, (∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) →
        (∀ v, ideleFinAt x v = 1) → φ x = 1) →
      ∃ (S : Set (HeightOneSpectrum (𝓞 K))) (_ : S.Finite) (ψ : sIdeals S →* G), IsAdmissible S ψ ∧
        ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
          φ x = ψ b

end NumberFieldKB.MilneCFT
