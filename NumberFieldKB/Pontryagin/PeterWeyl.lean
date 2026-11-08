import NumberFieldKB.Pontryagin.Compact
import NumberFieldKB.TauCetiPort.RepresentationTheory.Compact.RepresentativeDensity

/-!
# The Peter–Weyl theorem (point separation form), from the Tau Ceti port

**`peterWeylTheorem`** proves the named statement `PeterWeylTheorem` (Compact.lean) unconditionally, from
`TauCeti.exists_contRepresentation_apply_ne` with `𝕜 = ℂ` (Tau Ceti
`TauCeti/RepresentationTheory/Compact/RepresentativeDensity.lean`, ported under `NumberFieldKB/TauCetiPort` from Tau
Ceti main, 2026-11-05). Tau Ceti's proof: the representative functions (matrix coefficients of finite-dimensional
continuous unitary representations) are uniformly dense in $C(G)$, by convolution with an approximate identity and the
spectral theorem for the compact self-adjoint convolution operators on $L^2(G)$; a continuous function separating
$x \ne y$ is approximated by a matrix coefficient, which then also separates them.

The bridge: a `ContRepresentation ℂ G V` is a monoid homomorphism `G →* (V →L[ℂ] V)` (Mathlib), and the named
statement asks for exactly such a homomorphism, continuous for the operator norm.

Consequently `pontryaginDuality_compact` and everything proved from `PeterWeylTheorem` in this directory is
unconditional.
-/

namespace NumberFieldKB.Pontryagin

universe u

/-- **The Peter–Weyl theorem** (point separation form; proved, unconditionally, from the Tau Ceti port): the
finite-dimensional continuous representations of a compact Hausdorff group separate its points. -/
theorem peterWeylTheorem : PeterWeylTheorem.{u} where
  separates K _ _ _ _ _ x y hxy := by
    obtain ⟨n, π, hπ, hne⟩ := TauCeti.exists_contRepresentation_apply_ne (𝕜 := ℂ) x y hxy
    exact ⟨n, π.toMonoidHom, hπ, hne⟩

end NumberFieldKB.Pontryagin
