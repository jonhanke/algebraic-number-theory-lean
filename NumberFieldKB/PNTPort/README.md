# Port of PrimeNumberTheoremAnd's strong prime number theorem

Source: AlexKontorovich/PrimeNumberTheoremAnd, main `127b50e33f6033e2147921167a117af96d9ba4ea` (2026-11-06), Lean
`v4.35.0`, Mathlib rev `56a005855ea17e0b0958f73ec801ae140b0a1679` (the same as ours), Apache License 2.0, copyright the
PrimeNumberTheoremAnd contributors (headers and authors kept; files without a header get the project's).

Contents: the import closure of `PrimeNumberTheoremAnd/StrongPNT.lean` inside the project (14 files, 14,705 upstream
lines, no `sorry`, `axiom`, `native_decide`, `implemented_by` or `extern`), at the same relative paths, module names
`NumberFieldKB.PNTPort.X` instead of `PrimeNumberTheoremAnd.X`. Nothing outside the closure is ported. Headline:
`NumberFieldKB.PNTPort.StrongPNT : ∃ c > 0, (ψ - id) =O[atTop] fun x ↦ x * Real.exp (-c * (Real.log x) ^ (1/2))`,
where `ψ` is `Chebyshev.psi` (Mathlib). The upstream file ends with `#print axioms StrongPNT` (kept): it prints
`[propext, Classical.choice, Quot.sound]`.

The files are generated from the upstream checkout by a script. Changes,
all mechanical, no statement changed:
- `import Architect` dropped and `@[blueprint ...]` attribute entries removed (blueprint metadata only);
  `blueprint_comment /-- ... -/` blocks become plain comments. This is why the ported files are shorter.
- Declarations are in `namespace NumberFieldKB.PNTPort`. Blocks `namespace Complex/Chebyshev/Function ... end` stay at
  the root as upstream. A top-level declaration whose dotted name extends a Mathlib namespace (e.g.
  `DifferentiableAt.comp_ofReal`, `MeasureTheory.setIntegral_integral_swap`) is declared `_root_.` (so dot notation
  works, and the name is the upstream one), preceded by `open A in` because `_root_.A.b`, unlike upstream's `A.b`, does
  not open `A` in its body. Upstream references `_root_.x` to a closure declaration `x` become
  `NumberFieldKB.PNTPort.x`. In `EulerMaclaurin.lean` (a `module` file) the namespace opens after
  `@[expose] public section`.
- Licence header added to the files that have none (the project's Apache 2.0 header, authors: the contributors).

Hand edits after generation: none.

Reuse of Mathlib: the closure already uses Mathlib's `Chebyshev.psi`, `riemannZeta`, `mellin` and the Abel summation
of `Mathlib.NumberTheory.AbelSummation`; it defines no duplicate of a Mathlib definition used elsewhere in
NumberFieldKB. Two upstream files under `Mathlib/` (`Algebra/Notation/Support`, `Analysis/SpecialFunctions/Log/Basic`)
are small lemma files not yet in our Mathlib; they are ported like the others.

Consumer: `NumberFieldKB.MilneCFT.Ch6.R42.pntError` (`NumberFieldKB/MilneCFT/Ch6/Remark42aPNTError.lean`) proves the
named input `R42.PNTError` from `StrongPNT`, and `NumberFieldKB.MilneCFT.Ch6.remark_4_2a` proves `Remark4_2a`.
