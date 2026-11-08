import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter V: common definitions

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8).

This file fixes the objects of Chapter V §§1–4 that are not literally in Mathlib, in Milne's normalisation, and
proves the comparisons with Mathlib's normalised objects:

* `Gamma0GL N`: the group $\Gamma_0(N)$ as a subgroup of $\mathrm{GL}_2(\mathbb R)$ (Mathlib's levels live there);
* `eisG w`: the Eisenstein series $G_w(z) = \sum_{(m,n) \ne (0,0)} (mz+n)^{-w}$ (Milne writes $G_{2k}$, $w = 2k$);
  Mathlib's normalised series is `ModularForm.E` with $G_w = 2\zeta(w)E_w$ (`eisG_eq`);
* `g4`, `g6`, `discr`: $g_4 = 60G_4$, $g_6 = 140G_6$, $\Delta = g_4^3 - 27g_6^2$ (Chapter III); Mathlib's
  `ModularForm.discriminant` is $(2\pi)^{-12}\Delta$ (`discr_eq`);
* `jFun`: the modular invariant $j = 1728g_4^3/\Delta$ (pdf p. 190); `jFun_eq` gives $j = E_4^3/\Delta_{\mathrm{Mathlib}}$;
* `jN N`: $j_N(z) = j(Nz)$ (pdf p. 191);
* `IsModularFunction Γ f`: the modular functions for $\Gamma$ (pdf p. 189).

Mathlib uses the integer weight $k$ where Milne writes $2k$; we write `w` for Mathlib's weight.
Milne's $\rho = e^{2\pi i/6}$ (Proposition 1.3); Mathlib's `UpperHalfPlane.ρ` is $e^{2\pi i/3} = \rho^2$, the other
elliptic point of the closed fundamental domain.
-/

open UpperHalfPlane ModularForm Complex Filter Topology
open scoped MatrixGroups Real

namespace NumberFieldKB.MilneEC.V

/-- The congruence subgroup $\Gamma_0(N) = \{\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb Z) :
c \equiv 0 \bmod N\}$ (pdf p. 186), as a subgroup of $\mathrm{GL}_2(\mathbb R)$, the ambient group of Mathlib's
levels. $\Gamma_0(1) = \mathrm{SL}_2(\mathbb Z)$. -/
@[kb "milne2006ec" "Ch. V, §1, the subgroups Γ₀(N) (definition in prose), pdf p. 186"]
noncomputable abbrev Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- The period pair $(z, 1)$ of $z \in \mathbb H$, spanning the lattice $\Lambda(z, 1) = \mathbb Zz + \mathbb Z$. -/
noncomputable def periodPairOf (z : ℍ) : PeriodPair where
  ω₁ := z
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp at h1 h2
    rcases h1 with h1 | h1
    · subst h1; simp at h2; exact ⟨rfl, h2⟩
    · exact absurd h1 z.im_pos.ne'

/-- The Eisenstein series $G_w(z) = G_w(\Lambda(z,1)) = \sum_{\omega \in \Lambda(z,1) \smallsetminus 0}\omega^{-w}$
(Milne's $G_{2k}$ with $w = 2k$, pdf p. 190 and p. 192), built on Mathlib's lattice Eisenstein series
`PeriodPair.G` (the term $\omega = 0$ is $0^{-1} = 0$ in Lean). -/
@[kb "milne2006ec" "Ch. V, §2, the Eisenstein series G_{2k}(z) = G_{2k}(Λ(z,1)), pdf p. 190"]
noncomputable def eisG (w : ℕ) (z : ℍ) : ℂ := (periodPairOf z).G w

/-- $g_4(z) = 60G_4(z)$ (pdf p. 190), Mathlib's `PeriodPair.g₂` of $\Lambda(z,1)$. -/
@[kb "milne2006ec" "Ch. V, §2, g₄(z) = 60G₄(z), pdf p. 190"]
noncomputable def g4 (z : ℍ) : ℂ := (periodPairOf z).g₂

/-- $g_6(z) = 140G_6(z)$ (pdf p. 190), Mathlib's `PeriodPair.g₃` of $\Lambda(z,1)$. -/
@[kb "milne2006ec" "Ch. V, §2, g₆(z) = 140G₆(z), pdf p. 190"]
noncomputable def g6 (z : ℍ) : ℂ := (periodPairOf z).g₃

/-- Milne's discriminant $\Delta(z) = g_4(z)^3 - 27g_6(z)^2$ (pdf p. 190). Mathlib's `ModularForm.discriminant`
is $\eta^{24} = (2\pi)^{-12}\Delta$ (`discr_eq`). -/
@[kb "milne2006ec" "Ch. V, §2, Δ(z) = g₄(z)³ − 27g₆(z)², pdf p. 190"]
noncomputable def discr (z : ℍ) : ℂ := g4 z ^ 3 - 27 * g6 z ^ 2

/-- The modular invariant $j(z) = 1728g_4(z)^3/\Delta(z)$, the $j$-invariant of the elliptic curve
$\mathbb C/(\mathbb Zz + \mathbb Z)$ (pdf p. 190). -/
@[kb "milne2006ec" "Ch. V, §2, j(z) = 1728g₄(z)³/Δ(z), pdf p. 190"]
noncomputable def jFun (z : ℍ) : ℂ := 1728 * g4 z ^ 3 / discr z

/-- $j_N(z) = j(Nz)$ (pdf p. 191). For $N = 0$ the value is a junk value (`ofComplex` of a real number). -/
@[kb "milne2006ec" "Ch. V, §2, j_N(z) = j(Nz) (definition in prose), pdf p. 191"]
noncomputable def jN (N : ℕ) (z : ℍ) : ℂ := jFun (ofComplex ((N : ℂ) * z))

/-- A function $f$ on $\mathbb H$ is meromorphic: $f \circ$ (the inclusion) is meromorphic on the open set
$\{\Im z > 0\}$ of $\mathbb C$. -/
def IsMeromorphicOnUpperHalfPlane (f : ℍ → ℂ) : Prop :=
  MeromorphicOn (f ∘ ofComplex) {z : ℂ | 0 < z.im}

/-- A function $f$ on $\mathbb H$ is meromorphic at the cusp $\infty$: for some period $h > 0$ of $f$,
$f(z) = f^*(e^{2\pi iz/h})$ with $f^*$ meromorphic at $0$ (pdf p. 198). -/
def IsMeromorphicAtImInfty (f : ℍ → ℂ) : Prop :=
  ∃ h : ℝ, 0 < h ∧ Function.Periodic (f ∘ ofComplex) h ∧ MeromorphicAt (cuspFunction h f) 0

/-- The *modular functions* for a subgroup $\Gamma$ of finite index in $\mathrm{SL}_2(\mathbb Z)$ (pdf p. 189): the
functions $f$ on $\mathbb H$ that are (a) meromorphic on $\mathbb H$, (b) invariant, $f(\gamma z) = f(z)$ for
$\gamma \in \Gamma$, and (c) meromorphic at the cusps: for every $\gamma \in \mathrm{SL}_2(\mathbb Z)$ the function
$f \circ \gamma$ is meromorphic at $\infty$ (the cusp $\gamma\infty$ of $f$). These are the meromorphic functions on
$\Gamma\backslash\mathbb H^*$; values at poles are junk values. -/
@[kb "milne2006ec" "Ch. V, §2, modular functions for Γ (definition in prose), pdf p. 189"]
structure IsModularFunction (Γ : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) : Prop where
  meromorphic : IsMeromorphicOnUpperHalfPlane f
  invariant : ∀ γ ∈ Γ, ∀ z, f (γ • z) = f z
  meromorphic_cusps : ∀ γ : SL(2, ℤ), IsMeromorphicAtImInfty (fun z ↦ f (γ • z))

end NumberFieldKB.MilneEC.V
