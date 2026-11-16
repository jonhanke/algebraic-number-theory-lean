import NumberFieldKB.MilneEC.Ch5bGalois
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Milne, *Elliptic Curves*, Chapter V, Sections 7–9: the named statements

The named statements (cited results, not proved in this library) of Milne, *Elliptic Curves*, Chapter V, Sections
7–9, and the result proved from one of them, on the definitions of `NumberFieldKB.MilneEC.Ch5bGalois`:
Proposition 7.5 (`Prop7_5`) with Corollary 7.6 (`cor_7_6`, proved from it, with the transpose of the Frobenius
`frobTransposePts`), Proposition 8.1 (`Prop8_1`), the Tate module is free of rank 2 (`TorsionFreeRankTwo`),
Proposition 8.3 (`Prop8_3`), Theorem 8.6 (`Thm8_6`) and Theorem 9.1 (`Thm9_1`). They are kept apart from the
definitions, which are used without them.
-/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Pointwise

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

section Frobenius

variable (p : ℕ) [Fact p.Prime]

/-- **Proposition 7.5** (named statement; Milne, *EC*, V, Proposition 7.5, p. 228, with (38), p. 227): for an
elliptic curve $E$ over $\mathbb F_p$ and a prime $\ell \ne p$, at every level $n \ge 1$ the module
$E(\mathbb F)_{\ell^n} = T_\ell E / \ell^n$ is free of rank $2$ over $\mathbb Z/\ell^n$, and the Frobenius
endomorphism has trace $a_p = p + 1 - N_p$ and determinant $\deg \varphi_p = p$. -/
@[kb "milne2006ec" "Ch. V, Proposition 7.5 (trace of Frobenius on the Tate module; input)"]
structure Prop7_5 : Prop where
  free : ∀ (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
    ∀ n : ℕ, 0 < n → Module.Free (ZMod (ℓ ^ n)) (torsionPts E (Fpbar p) (ℓ ^ n)) ∧
      Module.finrank (ZMod (ℓ ^ n)) (torsionPts E (Fpbar p) (ℓ ^ n)) = 2
  trace : ∀ (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
    ∀ n : ℕ, torsionTrace E (Fpbar p) (ℓ ^ n) (restrictTorsion E (Fpbar p) (ℓ ^ n) (frobPts p E)) =
      ((p + 1 - numPoints p E : ℤ) : ZMod (ℓ ^ n))
  det : ∀ (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
    ∀ n : ℕ, torsionDet E (Fpbar p) (ℓ ^ n) (restrictTorsion E (Fpbar p) (ℓ ^ n) (frobPts p E)) = (p : ZMod (ℓ ^ n))

/-- **The transpose $\varphi_p^{\mathrm{tr}}$** of the Frobenius (Milne, *EC*, V.7, p. 224 and p. 228): the
endomorphism of $E(\mathbb F) = J(E)$ with $\varphi_p \circ \varphi_p^{\mathrm{tr}} = p$ (Milne's proof of
Corollary 7.6: "Because $\varphi_p$ has degree $p$, $\varphi_p \circ \varphi_p^{\mathrm{tr}} = p$"), i.e.
$\varphi_p^{\mathrm{tr}} = p\,\varphi_p^{-1}$ (the divisor $\varphi_p^{-1}[P]$ is $p[\varphi_p^{-1}P]$). -/
def frobTransposePts (E : WeierstrassCurve (ZMod p)) : pts E (Fpbar p) →+ pts E (Fpbar p) :=
  p • (AddEquiv.ofBijective (frobPts p E) (frobPts_bijective p E)).symm.toAddMonoidHom

/-- **Corollary 7.6** (Milne, *EC*, V, Corollary 7.6, p. 228), from Proposition 7.5: for an elliptic curve $E$ over
$\mathbb F_p$, $\mathrm{Tr}(\varphi_p^{\mathrm{tr}} \mid T_\ell E) = \mathrm{Tr}(\varphi_p \mid T_\ell E)$ (at every
level $\ell^n$, $\ell \ne p$). -/
@[kb "milne2006ec" "Ch. V, Corollary 7.6 (pdf p. 228)"]
theorem cor_7_6 (h : Prop7_5) (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (n : ℕ) :
    torsionTrace E (Fpbar p) (ℓ ^ n) (restrictTorsion E (Fpbar p) (ℓ ^ n) (frobTransposePts p E)) =
      torsionTrace E (Fpbar p) (ℓ ^ n) (restrictTorsion E (Fpbar p) (ℓ ^ n) (frobPts p E)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero ℓ)
    exact Subsingleton.elim _ _
  have : Nontrivial (ZMod (ℓ ^ n)) :=
    ZMod.nontrivial_iff.2 (Nat.one_lt_pow hn.ne' (Fact.out : ℓ.Prime).one_lt).ne'
  obtain ⟨hfree, hrank⟩ := h.free p E ℓ hℓ n hn
  have := hfree
  have hdet := h.det p E ℓ hℓ n
  have hs : ∀ Q, frobPts p E ((AddEquiv.ofBijective _ (frobPts_bijective p E)).symm Q) = Q :=
    fun Q => (AddEquiv.ofBijective _ (frobPts_bijective p E)).apply_symm_apply Q
  have key1 : ∀ Q, frobPts p E (frobTransposePts p E Q) = p • Q := fun Q => by
    show frobPts p E (p • (AddEquiv.ofBijective _ (frobPts_bijective p E)).symm Q) = p • Q
    rw [map_nsmul, hs]
  have key2 : ∀ Q, frobTransposePts p E (frobPts p E Q) = p • Q := fun Q => by
    show p • (AddEquiv.ofBijective _ (frobPts_bijective p E)).symm (frobPts p E Q) = p • Q
    rw [← AddEquiv.ofBijective_apply _ (frobPts_bijective p E) Q,
      AddEquiv.symm_apply_apply]
  have hcop : Nat.Coprime p (ℓ ^ n) :=
    Nat.Coprime.pow_right n ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).2 hℓ.symm)
  obtain ⟨u, hu⟩ : ∃ u : ZMod (ℓ ^ n), u * (p : ZMod (ℓ ^ n)) = 1 :=
    ⟨((ZMod.isUnit_iff_coprime p (ℓ ^ n)).2 hcop).unit⁻¹.val, by simp⟩
  unfold torsionTrace
  refine trace_inverse_two hrank u p hu _ _ hdet ?_ ?_
  · ext P
    show frobPts p E (frobTransposePts p E (P : pts E (Fpbar p))) = ((p : ZMod (ℓ ^ n)) • P : _)
    rw [key1, Nat.cast_smul_eq_nsmul]
    rfl
  · ext P
    show frobTransposePts p E (frobPts p E (P : pts E (Fpbar p))) = ((p : ZMod (ℓ ^ n)) • P : _)
    rw [key2, Nat.cast_smul_eq_nsmul]
    rfl

end Frobenius

/-- **Proposition 8.1** (named statement; Milne, *EC*, V, Proposition 8.1, p. 231): for an elliptic curve $E$ over
$\mathbb Q$, a prime $\ell$ and a finite set $S$ of primes containing $\ell$ and the primes of bad reduction, all
points of order $\ell^n$ have coordinates in $K_S$. -/
@[kb "milne2006ec" "Ch. V, Proposition 8.1 (torsion is unramified outside S; input)"]
structure Prop8_1 : Prop where
  coords : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (S : Finset ℕ),
    (∀ p, p.Prime → InBadSet E ℓ p → p ∈ S) → ∀ (n : ℕ) (x y : Qbar) (h : (E.toAffine.baseChange Qbar).Nonsingular x y),
    (Point.some (x := x) (y := y) h : pts E Qbar) ∈ torsionPts E Qbar (ℓ ^ n) → x ∈ fieldKS S ∧ y ∈ fieldKS S

/-- **The Tate module is free of rank 2** (named statement; Milne, *EC*, V.8, p. 231, running text: "$T_\ell E$ is
the free $\mathbb Z_\ell$-module of rank 2 such that $T_\ell E/\ell^n T_\ell E = E(\bar{\mathbb Q})_{\ell^n}$"): at
every level $n \ge 1$, $E(\bar{\mathbb Q})_{\ell^n}$ is free of rank $2$ over $\mathbb Z/\ell^n$ (at $n = 0$ the
ring $\mathbb Z/1$ is zero and Mathlib's rank is $1$). -/
@[kb "milne2006ec" "Ch. V, Section 8 (pdf p. 231): T_ℓE is free of rank 2 (input)"]
structure TorsionFreeRankTwo : Prop where
  free : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ), 0 < n →
    Module.Free (ZMod (ℓ ^ n)) (torsionPts E Qbar (ℓ ^ n)) ∧
      Module.finrank (ZMod (ℓ ^ n)) (torsionPts E Qbar (ℓ ^ n)) = 2

/-- **Proposition 8.3** (named statement; Milne, *EC*, V, Proposition 8.3, p. 232): for an elliptic curve $E$ over
$\mathbb Q$, a prime $\ell$ and a prime $p \notin S$ (i.e. $p \ne \ell$ and $E$ has good reduction at $p$),
$\mathrm{Tr}(\rho_\ell(F_p) \mid T_\ell E) = a_p = p + 1 - N_p(E)$, at every level $\ell^n$ and for every Frobenius
element $F_p$ at $p$. -/
@[kb "milne2006ec" "Ch. V, Proposition 8.3 (trace of Frobenius on T_ℓE; input)"]
structure Prop8_3 : Prop where
  trace : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime], p ≠ ℓ →
    HasGoodReductionAt E p → ∀ σ : GQ, IsFrobeniusAt σ p → ∀ n : ℕ,
      torsionTrace E Qbar (ℓ ^ n) (torsionRep E Qbar (ℓ ^ n) σ) = ((apAt E p : ℤ) : ZMod (ℓ ^ n))

/-- **Theorem 8.6 (Langlands, Tunnell)** (named statement; Milne, *EC*, V, Theorem 8.6, p. 232): if
$\bar\rho : G_S \to \mathrm{GL}_2(\mathbb F_3)$ is odd and irreducible, then it is modular (standard notion
`IsModularRepModLChar`; Langlands and Tunnell give a form of weight $1$ with character). -/
@[kb "milne2006ec" "Ch. V, Theorem 8.6 (Langlands-Tunnell; input)"]
structure Thm8_6 : Prop where
  modular : ∀ (S : Finset ℕ) (ρ : GQ →* GL (Fin 2) (ZMod 3)), IsGSRep S ρ → IsOddRep ρ → IsIrreducibleRep ρ →
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    IsModularRepModLChar 3 S ρ

/-- **Theorem 9.1** (named statement; Milne, *EC*, V, Theorem 9.1, p. 234; Néron, Ogg, Shafarevich): for primes
$\ell \ne p$, an elliptic curve $E$ over $\mathbb Q$ has good reduction at $p$ if and only if the representation of
$G$ on $E(\bar{\mathbb Q})_{\ell^n}$ is unramified at $p$ for all $n$. (Milne's statement omits $p \ne \ell$; the case
$p = \ell$ is Theorem 9.2.) -/
@[kb "milne2006ec" "Ch. V, Theorem 9.1 (Néron-Ogg-Shafarevich; input)"]
structure Thm9_1 : Prop where
  iff : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime], p ≠ ℓ →
    (HasGoodReductionAt E p ↔ ∀ n : ℕ, IsUnramifiedRepAt (torsionRep E Qbar (ℓ ^ n)) p)

end NumberFieldKB.MilneEC.Vb
