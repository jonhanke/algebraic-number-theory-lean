import NumberFieldKB.MilneEC.Ch4bTwistsH1
import NumberFieldKB.TauCetiPort.FieldTheory.GaloisCohomology.Hilbert90
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Milne, Elliptic Curves: named inputs discharged from the Tau Ceti port

J. S. Milne, *Elliptic Curves* (`milne2006ec`). Named inputs of the Milne EC part that follow from theorems of Tau Ceti
already ported to `NumberFieldKB/TauCetiPort/` (Apache License 2.0, copyright the Tau Ceti contributors; see
`NumberFieldKB/TauCetiPort/README.md`). The decision for each Milne EC input matched by Tau Ceti main `d2083f0f`
was taken by the size of its import closure.

## Main results

* `example1_8a` (Example 1.8(a), Hilbert's Theorem 90 for $\operatorname{Gal}(k^{\mathrm{al}}/k)$, $k$ perfect), from
  `TauCeti.isMulCoboundary₁_of_isMulCocycle₁_of_isLocallyConstant` (Tau Ceti
  `FieldTheory/GaloisCohomology/Hilbert90.lean`, whose whole import closure was already ported). Downstream:
  `theorem_7_15_unconditional` (Theorem 7.15 with no named input).
-/

open WeierstrassCurve

namespace NumberFieldKB.MilneEC

section Hilbert90

variable (k : Type*) [Field k] [PerfectField k]

/-- **Example 1.8(a)** (Milne, pdf p. 114, Hilbert's Theorem 90 for the absolute Galois group of a perfect field):
every continuous crossed homomorphism $\Gamma \to k^{\mathrm{al}\times}$ is principal.  Discharged from Tau Ceti's
Hilbert 90 for an arbitrary Galois extension (`TauCeti.isMulCoboundary₁_of_isMulCocycle₁_of_isLocallyConstant`),
applied to $k^{\mathrm{al}}/k$, which is Galois since $k$ is perfect. -/
@[kb "milne2006ec" "Ch. IV, Example 1.8(a), pdf p. 114"]
theorem example1_8a : Example1_8a k := by
  refine ⟨fun f hf0 hcoc hlc => ?_⟩
  let g : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → (AlgebraicClosure k)ˣ :=
    fun σ => Units.mk0 (f σ) (hf0 σ)
  have hg : groupCohomology.IsMulCocycle₁ g := by
    intro σ τ
    ext
    simp [g, hcoc σ τ]
  have hgl : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro u
    have : g ⁻¹' {u} = f ⁻¹' {(u : AlgebraicClosure k)} := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, g]
      constructor
      · rintro rfl; rfl
      · intro h; ext; exact h
    rw [this]
    exact hlc.isOpen_fiber _
  obtain ⟨u, hu⟩ := TauCeti.isMulCoboundary₁_of_isMulCocycle₁_of_isLocallyConstant hg hgl
  refine ⟨u, u.ne_zero, fun σ => ?_⟩
  have := congrArg (fun v : (AlgebraicClosure k)ˣ => (v : AlgebraicClosure k)) (hu σ)
  simpa [g, Units.smul_def, div_eq_mul_inv] using this.symm

/-- **Theorem 7.15** (pdf p. 148), characteristic not $2$ or $3$, $k$ perfect, unconditional: $E \mapsto [\alpha]$ is a
one-to-one correspondence between elliptic curves over $k$ isomorphic to $E_0 = E(a, b)$ over $k^{\mathrm{al}}$, modulo
isomorphism over $k$, and $H^1(\Gamma, \operatorname{Aut}_{k^{\mathrm{al}}}(E_0, O))$.  `theorem_7_15` with
Hilbert's Theorem 90 supplied by `example1_8a`. -/
@[kb "milne2006ec" "Ch. IV, Theorem 7.15, pdf p. 148"]
theorem theorem_7_15_unconditional [NeZero (2 : k)] [NeZero (3 : k)] (a b : k) [(shortW a b).IsElliptic] :
    (∀ (E E' : WeierstrassCurve k) (h : IsTwist (shortW a b) E) (h' : IsTwist (shortW a b) E'),
      twistClass _ E h = twistClass _ E' h' ↔ ∃ C : VariableChange k, C • E = E') ∧
    (∀ c : NonabelianH1 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (AutAl (shortW a b)),
      ∃ (E : WeierstrassCurve k) (h : IsTwist (shortW a b) E), twistClass _ E h = c) :=
  theorem_7_15 (example1_8a k) a b

end Hilbert90

end NumberFieldKB.MilneEC
