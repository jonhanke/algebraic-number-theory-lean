import NumberFieldKB.MilneCFT.Ch5IdelesChar
import NumberFieldKB.MilneCFT.Ch5Artin
import NumberFieldKB.MilneCFT.Ch8.Remark32Local
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 4.8: the first sentence is false for a general topological group

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Remark 4.8 (p. 174).

Remark 4.8 asserts that for **every** commutative topological group $G$, an admissible $\psi : I^S \to G$ extends to a
continuous $\varphi : \mathbb I_K \to G$, trivial on $K^\times$, with $\varphi(x) = \psi(\mathrm{id}(x))$ for $x$ trivial at
$S$ and at the infinite places. Tate's construction needs $G$ complete (Hausdorff). Counterexample
(`not_remark4_8_rat`): $K = \mathbb Q$, $S = \emptyset$, $G = \mathbb Z/2$ (multiplicatively) with the indiscrete topology
(so every $\psi$ is admissible and every map to $G$ is continuous), $\psi(\mathfrak a) = $ the parity of
$\mathrm{ord}_2\mathfrak a$. If $\varphi$ existed: $2 = 2_\infty \cdot y$ with $y$ trivial at $\infty$ and
$\mathrm{id}(y) = (2)$, so $1 = \varphi(2) = \varphi(2_\infty)\psi((2))$; but $2_\infty = (\sqrt2_\infty)^2$ and $G$ has
exponent $2$, so $\psi((2)) = 1$, a contradiction.
-/

open NumberField IsDedekindDomain Topology
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

/-- $\mathbb Z/2$ (multiplicatively) with the indiscrete topology. -/
def IndiscreteZ2 : Type := Multiplicative (ZMod 2)

instance : CommGroup IndiscreteZ2 := inferInstanceAs (CommGroup (Multiplicative (ZMod 2)))

instance : TopologicalSpace IndiscreteZ2 := ⊤

instance : IsTopologicalGroup IndiscreteZ2 where
  continuous_mul := continuous_top
  continuous_inv := continuous_top

theorem indiscreteZ2_sq (g : IndiscreteZ2) : g ^ 2 = 1 := by
  have key : ∀ a : ZMod 2, (Multiplicative.ofAdd a) ^ 2 = (1 : Multiplicative (ZMod 2)) := by decide
  exact key (Multiplicative.toAdd (g : Multiplicative (ZMod 2)))

/-- $\mathfrak a \mapsto$ the parity of $\mathrm{ord}_v\mathfrak a$. -/
def parityChar (v : HeightOneSpectrum (𝓞 ℚ)) : sIdeals (∅ : Set (HeightOneSpectrum (𝓞 ℚ))) →* IndiscreteZ2 where
  toFun I := Multiplicative.ofAdd
    ((FractionalIdeal.count ℚ v ((I : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) : ℤ) : ZMod 2)
  map_one' := by
    change Multiplicative.ofAdd (((FractionalIdeal.count ℚ v (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ)) : ℤ) : ZMod 2) = _
    rw [FractionalIdeal.count_one]
    rfl
  map_mul' I J := by
    change Multiplicative.ofAdd (((FractionalIdeal.count ℚ v (((I : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : _) *
      ((J : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : _))) : ℤ) : ZMod 2) = _
    rw [FractionalIdeal.count_mul ℚ v (I : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ).ne_zero
      (J : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ).ne_zero]
    push_cast
    rfl

/-- **Remark 4.8 (`extend`) is false as formalized** (Milne, *CFT*, V, Remark 4.8, p. 174; see the module docstring):
for $G$ a non-Hausdorff topological group the extension need not exist. Hence `Remark4_8 ℚ` fails. -/
@[kb "milne2020cft" "Ch. V, Remark 4.8 (counterexample: G not complete)"]
theorem not_remark4_8_rat : ¬ Remark4_8 ℚ := by
  intro h
  obtain ⟨v2, hv2, hT2⟩ := exists_prime_toPrincipalIdeal 2 Nat.prime_two
  have hadm : IsAdmissible (∅ : Set (HeightOneSpectrum (𝓞 ℚ))) (parityChar v2) := by
    intro N hN
    have hNu : N = Set.univ := by
      rw [nhds_top, Filter.mem_top] at hN
      exact hN
    refine ⟨Modulus.one ℚ, fun v hv => ?_, fun a _ _ => by rw [hNu]; trivial⟩
    have hv' : v.asIdeal ∣ (⊤ : Ideal (𝓞 ℚ)) := hv
    exact v.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hv'))
  obtain ⟨φ, -, hK, hT⟩ := h.extend IndiscreteZ2 ∅ (parityChar v2) Set.finite_empty hadm
  let w : InfinitePlace ℚ := Rat.infinitePlace
  obtain ⟨r, hr⟩ := (by
    rcases w.isReal_or_isComplex with hw | hw
    · let f := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
      refine ⟨f (Real.sqrt 2), ?_⟩
      rw [← map_mul, Real.mul_self_sqrt (by norm_num), map_ofNat]
    · haveI : IsAlgClosed w.Completion :=
        IsAlgClosed.of_ringEquiv ℂ _ (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
      exact IsAlgClosed.isSquare _ : IsSquare (2 : w.Completion))
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h20 : algebraMap ℚ w.Completion 2 = algebraMap ℚ w.Completion 0 := by
      rw [map_ofNat, map_zero, hr, mul_zero]
    have := (algebraMap ℚ w.Completion).injective h20
    norm_num at this
  let two : ℚˣ := Units.mk0 2 (by norm_num)
  let ru : w.Completionˣ := Units.mk0 r hr0
  have h2u : Units.map (algebraMap ℚ w.Completion).toMonoidHom two = ru * ru := by
    ext; simp [two, ru, hr]
  let t := IdeleGroup.ofCompletion (𝓞 ℚ) ℚ w (ru * ru)
  let y := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ two * t⁻¹
  have hy : y ∈ idelesTrivialAt (∅ : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    refine ⟨fun w' => ?_, fun v hv => hv.elim⟩
    rw [Subsingleton.elim w' w, ideleInfAt_mul, ideleInfAt_inv, ideleInfAt_unitEmbedding,
      ideleInfAt_ofCompletion_self, ← h2u, Units.coe_map]
    refine mul_inv_cancel₀ ?_
    intro h0
    exact (Units.map (algebraMap ℚ w.Completion).toMonoidHom two).ne_zero h0
  have hid : ideleToIdeal ℚ y = toPrincipalIdeal (𝓞 ℚ) ℚ two := by
    have ht : ideleToIdeal ℚ t = 1 := by
      change QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal ℚ (Units.map _ t) = 1
      rw [show Units.map (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom t = 1 from
        Units.ext rfl, map_one]
    rw [map_mul, map_inv, ht, inv_one, mul_one, ideleToIdeal_unitEmbedding]
  have hφy := hT y hy ⟨toPrincipalIdeal (𝓞 ℚ) ℚ two, fun v hv => hv.elim⟩ hid.symm
  have hφt : φ t = 1 := by
    have : t = (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ w ru) ^ 2 := by rw [sq, ← map_mul]
    rw [this, map_pow, indiscreteZ2_sq]
  rw [map_mul, map_inv, hK, hφt, inv_one, one_mul] at hφy
  have hval : parityChar v2 ⟨toPrincipalIdeal (𝓞 ℚ) ℚ two, fun v hv => hv.elim⟩ ≠ 1 := by
    change Multiplicative.ofAdd ((FractionalIdeal.count ℚ v2
      ((toPrincipalIdeal (𝓞 ℚ) ℚ two : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) : ℤ) : ZMod 2) ≠ 1
    have h2 : toPrincipalIdeal (𝓞 ℚ) ℚ two = primeUnitIdeal v2 := by
      rw [← hT2]; rfl
    rw [h2]
    change Multiplicative.ofAdd ((FractionalIdeal.count ℚ v2 (v2.asIdeal : FractionalIdeal (𝓞 ℚ)⁰ ℚ) : ℤ) : ZMod 2) ≠ 1
    rw [FractionalIdeal.count_self]
    decide
  exact hval hφy.symm

end NumberFieldKB.MilneCFT
