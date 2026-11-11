import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.ClassFormation
import QuadFormsKB.Citation

/-!
# Milne, *Class Field Theory*, Lemma VIII.4.6, from the Tau Ceti port

**Lemma VIII.4.6** (`Ch8.lemma4_6`): restriction from $K$ to a finite extension $E$ multiplies the global invariant
by $[E:K]$.

Proof: this is Tau Ceti's `globalInv_res` (port under `NumberFieldKB/TauCetiPort/`, Apache 2.0, the Tau Ceti
contributors). Milne's $\mathrm{inv}_K$ on $H^2(\Omega/K)$ (idèle-class cohomology) is characterized by: on the image
of $\bigoplus_v \mathrm{Br}(K_v)$ it is the sum of the local invariants. Tau Ceti's `globalInv` is defined on every
finite Galois layer $M/F$ of $K^{\mathrm{sep}}/K$ and has exactly this property (`globalInv_ideleToClassH2`, the sum
of the local invariants of an idèle lift; `globalInv_unique`) and is compatible with inflation (`globalInv_infl`), so
it is Milne's invariant read on the finite layers. A restriction of layers `LayerRestriction small big` takes the
layer $M/F$ to $M/E$ for $F\subseteq E\subseteq M$, and its `relativeDegree` is $[E:F]$.

This file imports only Tau Ceti's `ClassFormation`, and the statement switches off three instances, so that the
statement elaborates to exactly the type of `globalInv_res`. With more of the library imported, instance search
picks other proofs of propositional instance arguments (`Algebra.IsAlgebraic K K`, `IsLocalRing`) than in Tau Ceti,
and checking the proof term against such a statement did not terminate.
-/

open TauCeti.ClassFieldTheory

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type} [Field K] [NumberField K]

attribute [-instance] IsPurelyInseparable.normal normal_self Normal.toIsAlgebraic in
/-- **Lemma 4.6** (Milne, *CFT*, VIII, Lemma 4.6, p. 242): for a finite extension $E/F$ of number fields and a class
$\gamma$ of the idèle-class cohomology, $\mathrm{inv}_E(\mathrm{Res}\,\gamma) = [E:F]\,\mathrm{inv}_F(\gamma)$. Read on
a finite Galois layer `big` $= M/F$ of $K^{\mathrm{sep}}/K$ and its restriction `small` $= M/E$, with Tau Ceti's global
invariant (the sum of the local invariants, see the module docstring); `R.relativeDegree` is $[E:F]$. -/
@[kb "milne2020cft" "Ch. VIII, Lemma 4.6, p. 242"]
theorem lemma4_6 {small big : NormalLayer (TauCeti.AbsoluteGaloisGroup K)} (R : LayerRestriction small big)
    (γ : big.H (globalFormation K) 2) :
    globalInv K small (R.cohomologyRes (globalFormation K) 2 γ) = R.relativeDegree • globalInv K big γ :=
  globalInv_res R γ

end NumberFieldKB.MilneCFT.Ch8
