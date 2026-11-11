import NumberFieldKB.MilneANT.Ch8Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.WithAbs

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: decomposition groups and the Frobenius element

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Setting: $L/K$ a finite Galois extension of number fields, $G = \mathrm{Gal}(L/K)$ acting on `𝓞 L` and on its ideals.
The decomposition group $D(\mathfrak P) = G(\mathfrak P)$ is Mathlib's `MulAction.stabilizer G 𝔓` (equal to the
decomposition group of the $\mathfrak P$-adic absolute value, `decompGroupAbv_finitePlace`), the inertia group
$I(\mathfrak P)$ is Mathlib's `Ideal.inertia G 𝔓`, and a Frobenius element at $\mathfrak P$ is an element satisfying
Mathlib's `IsArithFrobAt` ($\sigma\alpha \equiv \alpha^q \bmod \mathfrak P$); for $\mathfrak P$ unramified it is unique
(`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`) and in $G(\mathfrak P)$ (`IsArithFrobAt.mem_stabilizer`).

* **Proposition 8.10** (`Prop8_10`, named statement): $G_w \cong \mathrm{Gal}(L_w/K_v)$.
* **Proposition 8.11** (`prop_8_11a` … `prop_8_11d`, proved), and the remark after it (`prop_8_11_decompField`).

Proposition 8.13 and the Frobenius items 8.14–8.17 are in `Ch8Frobenius.lean`.
-/

open NumberField IsDedekindDomain
open scoped Pointwise

namespace NumberFieldKB.MilneANT

noncomputable section

/-! ## Proposition 8.10 -/

/-- **Proposition 8.10** (named statement): for $L/K$ Galois of number fields and an absolute value $w$ of $L$ with
restriction $v$ to $K$, every $\sigma$ in the decomposition group $G_w$ (`decompGroupAbv`) is an isometry of $(L, w)$,
hence extends uniquely to a continuous automorphism of the completion $L_w$, and the resulting homomorphism
$G_w \to \mathrm{Gal}(L_w/K_v)$ is an isomorphism. Stated as: there is a group isomorphism
$\varphi : G_w \cong \mathrm{Gal}(L_w/K_v)$ with $\varphi(\sigma)(x) = \sigma(x)$ for $x \in L$ (which pins down
$\varphi$ as Milne's map). The completions are Mathlib's `AbsoluteValue.Completion`, with the $K_v$-algebra structure
`AbsoluteValue.Completion.algebraOfLiesOver`. -/
@[kb "milne2020ant" "v3.08, Prop. 8.10, p. 139"]
structure Prop8_10 : Prop where
  iso : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (w : AbsoluteValue L ℝ),
    letI := AbsoluteValue.Completion.algebraOfLiesOver (w.under K) w
    ∃ φ : decompGroupAbv (K := K) w ≃* (w.Completion ≃ₐ[(w.under K).Completion] w.Completion),
      ∀ (σ : decompGroupAbv (K := K) w) (x : L),
        φ σ (x : w.Completion) = ((σ.1 x : L) : w.Completion)

/-! ## Proposition 8.11 -/

section Prop811

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (𝔭 : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver 𝔭.asIdeal]

/-- The decomposition field $L^{D(\mathfrak P)}$: the fixed field of the decomposition group. -/
abbrev decompField : IntermediateField K L :=
  IntermediateField.fixedField (MulAction.stabilizer Gal(L/K) P)

/-- The inertia field $L^{I(\mathfrak P)}$: the fixed field of the inertia group. -/
abbrev inertiaField : IntermediateField K L :=
  IntermediateField.fixedField (P.inertia Gal(L/K))

/-! ### Helper lemmas

These hold for every prime $\mathfrak P$ of $\mathcal O_L$, including the zero ideal (the statements of
Proposition 8.11 do not assume $\mathfrak P \neq 0$), so each lemma treats the zero ideal separately where
Mathlib's results need a maximal ideal. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- The stabilizer of the zero ideal is the whole Galois group. -/
theorem stabilizer_bot : MulAction.stabilizer Gal(L/K) (⊥ : Ideal (𝓞 L)) = ⊤ := by
  ext σ
  simp

/-- The Galois group acts faithfully on the ring of integers of $L$. -/
theorem faithfulSMul_gal_integers : FaithfulSMul Gal(L/K) (𝓞 L) where
  eq_of_smul_eq_smul {g h} H := by
    refine AlgEquiv.ext fun x => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
    have ha := congrArg (fun z : 𝓞 L => (z : L)) (H a)
    have hb' := congrArg (fun z : 𝓞 L => (z : L)) (H b)
    simp only [map_div₀]
    exact congrArg₂ (· / ·) ha hb'

/-- The inertia group of the zero ideal is trivial. -/
theorem inertia_bot_nf : (⊥ : Ideal (𝓞 L)).inertia Gal(L/K) = ⊥ :=
  haveI := faithfulSMul_gal_integers K L
  Ideal.inertia_bot Gal(L/K) (𝓞 L)

/-- The decomposition-field facts for any intermediate field $F$ that is the fixed field of the stabilizer of
$\mathfrak P$ (stated for an arbitrary such $F$ so that it applies to conjugate primes): $\mathfrak P$ is the only
prime above $\mathfrak P \cap F$, and $\mathfrak P \cap F$ has ramification index and inertia degree $1$ over
$K$. -/
theorem decomp_general (F : IntermediateField K L)
    [h : IsGaloisGroup (MulAction.stabilizer Gal(L/K) P) F L] :
    (P.under (𝓞 F)).primesOver (𝓞 L) = {P} ∧
      (P.under (𝓞 F)).ramificationIdx (𝓞 K) = 1 ∧ (P.under (𝓞 F)).inertiaDeg (𝓞 K) = 1 := by
  haveI : IsGaloisGroup (MulAction.stabilizer Gal(L/K) P) (𝓞 F) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (MulAction.stabilizer Gal(L/K) P) (𝓞 F) (𝓞 L) F L
  by_cases hP : P = ⊥
  · subst hP
    rw [Ideal.under_bot]
    refine ⟨?_, Ideal.ramificationIdx_bot_eq_one _, ?_⟩
    · ext Q
      simp only [Ideal.primesOver, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hQ, hQo⟩
        exact Ideal.eq_bot_of_liesOver_bot (𝓞 F) Q
      · rintro rfl
        exact ⟨inferInstance, inferInstance⟩
    · rw [Ideal.inertiaDeg_bot_eq_finrank,
        ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 F) F]
      have h1 := IsGaloisGroup.card_eq_finrank (MulAction.stabilizer Gal(L/K) (⊥ : Ideal (𝓞 L))) F L
      have h2 := IsGaloisGroup.card_eq_finrank Gal(L/K) K L
      have h4 : Nat.card (MulAction.stabilizer Gal(L/K) (⊥ : Ideal (𝓞 L))) = Nat.card Gal(L/K) := by
        rw [stabilizer_bot K L]; simp
      have h3 := Module.finrank_mul_finrank K F L
      have h5 : 0 < Module.finrank K L := Module.finrank_pos
      rw [h4, h2] at h1
      rw [← h1] at h3
      nlinarith
  · haveI := Chebotarev.finite_quotient_of_ne_bot P hP
    haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
    haveI : Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 L) (P.under (𝓞 K)) :=
      Chebotarev.hasSeparableResidueFieldsAt_under P
    haveI : (P.under (𝓞 F)).IsMaximal := Chebotarev.isMaximal_under_of_finite P
    refine ⟨?_, ?_, ?_⟩
    · exact IsDecompositionField.primesOver_eq_singleton K L P F (𝓞 F) (P.under (𝓞 F))
    · exact IsDecompositionField.ramificationIdx_eq (𝓞 K) K L (P.under (𝓞 K)) P F (𝓞 F)
        (P.under (𝓞 F))
    · exact IsDecompositionField.inertiaDeg_eq (𝓞 K) K L (P.under (𝓞 K)) P F (𝓞 F)
        (P.under (𝓞 F))

/-- $\mathrm{Gal}(L/L^D)$ is the decomposition group. -/
theorem isGG_decomp : IsGaloisGroup (MulAction.stabilizer Gal(L/K) P) (decompField K L P) L :=
  IsGaloisGroup.subgroup Gal(L/K) K L _

/-- $\mathrm{Gal}(L/L^I)$ is the inertia group. -/
theorem isGG_inertia : IsGaloisGroup (P.inertia Gal(L/K)) (inertiaField K L P) L :=
  IsGaloisGroup.subgroup Gal(L/K) K L _

/-- Residue field extensions of $\mathcal O_L$ over $\mathcal O_F$ are separable at $\mathfrak P \cap F$, for
every prime $\mathfrak P$ (including zero). -/
theorem hasSep_under_field (F : IntermediateField K L) :
    Algebra.HasSeparableResidueFieldsAt (𝓞 F) (𝓞 L) (P.under (𝓞 F)) := by
  by_cases hP : P = ⊥
  · subst hP
    have h0 : Ideal.under (𝓞 F) (⊥ : Ideal (𝓞 L)) = ⊥ := Ideal.under_bot _ _
    have : Algebra.HasSeparableResidueFieldsAt (𝓞 F) (𝓞 L) (⊥ : Ideal (𝓞 F)) := inferInstance
    exact Chebotarev.hasSep_congr h0.symm this
  · haveI := Chebotarev.finite_quotient_of_ne_bot P hP
    exact Chebotarev.hasSeparableResidueFieldsAt_under (K := F) P

/-- The inertia-field facts: $\mathfrak P$ is the only prime above $\mathfrak P \cap L^I$, the ramification index
$e(\mathfrak P / \mathfrak P_I)$ is the order of the inertia group, and $f(\mathfrak P / \mathfrak P_I) = 1$. -/
theorem inertia_general :
    (P.under (𝓞 (inertiaField K L P))).primesOver (𝓞 L) = {P} ∧
      P.ramificationIdx (𝓞 (inertiaField K L P)) = Nat.card (P.inertia Gal(L/K)) ∧
      P.inertiaDeg (𝓞 (inertiaField K L P)) = 1 := by
  set E := inertiaField K L P with hE
  haveI := isGG_inertia K L P
  haveI hGG : IsGaloisGroup (P.inertia Gal(L/K)) (𝓞 E) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (P.inertia Gal(L/K)) (𝓞 E) (𝓞 L) E L
  haveI := hasSep_under_field K L P E
  have hsing : (P.under (𝓞 E)).primesOver (𝓞 L) = {P} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, ?_⟩
    rintro Q ⟨hQ, hQo⟩
    obtain ⟨σ, rfl⟩ :=
      Ideal.exists_smul_eq_of_isGaloisGroup (P.under (𝓞 E)) P Q (P.inertia Gal(L/K))
    exact Ideal.inertia_le_stabilizer P σ.prop
  have htop : P.inertia (P.inertia Gal(L/K)) = ⊤ := by
    refine (Subgroup.eq_top_iff' _).mpr fun σ => ?_
    exact Ideal.mem_inertia.mpr fun x => Ideal.mem_inertia.mp σ.prop x
  have H1 := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := P.inertia Gal(L/K))
    (P.under (𝓞 E)) P
  have H2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (P.under (𝓞 E))
    (𝓞 L) (P.inertia Gal(L/K))
  rw [hsing, Set.ncard_singleton, htop, Subgroup.card_top, one_mul] at H1
  rw [hsing, Set.ncard_singleton, one_mul,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 E)) P (P.inertia Gal(L/K)),
    Ideal.inertiaDegIn_eq_inertiaDeg (P.under (𝓞 E)) P (P.inertia Gal(L/K))] at H2
  have hpos : 0 < Nat.card (P.inertia Gal(L/K)) := Nat.card_pos
  have hf : P.inertiaDeg (𝓞 E) = 1 := by
    have : Nat.card (P.inertia Gal(L/K)) * P.inertiaDeg (𝓞 E) =
        Nat.card (P.inertia Gal(L/K)) * 1 := by
      rw [mul_one]; exact H1
    exact Nat.eq_of_mul_eq_mul_left hpos this
  refine ⟨hsing, ?_, hf⟩
  rw [hf, mul_one] at H2
  exact H2

/-- Residue field extensions of $\mathcal O_L$ over $\mathcal O_K$ are separable at $\mathfrak P \cap K$, for every
prime $\mathfrak P$ (including zero). -/
theorem hasSep_under_base :
    Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 L) (P.under (𝓞 K)) := by
  by_cases hP : P = ⊥
  · subst hP
    have h0 : Ideal.under (𝓞 K) (⊥ : Ideal (𝓞 L)) = ⊥ := Ideal.under_bot _ _
    have : Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 L) (⊥ : Ideal (𝓞 K)) := inferInstance
    exact Chebotarev.hasSep_congr h0.symm this
  · haveI := Chebotarev.finite_quotient_of_ne_bot P hP
    exact Chebotarev.hasSeparableResidueFieldsAt_under (K := K) P

/-- The order of the inertia group is the ramification index $e(\mathfrak P / \mathfrak p)$. -/
theorem card_inertia_eq_ram : Nat.card (P.inertia Gal(L/K)) = P.ramificationIdx (𝓞 K) := by
  haveI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  haveI := hasSep_under_base K L P
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (P.under (𝓞 K)) P,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P Gal(L/K)]

/-- The content of Proposition 8.11(c), as a helper placed before the definition of the algebra structure used
in part (b). -/
theorem inertia_facts :
    (P.under (𝓞 (inertiaField K L P))).primesOver (𝓞 L) = {P} ∧
      P.ramificationIdx (𝓞 (inertiaField K L P)) = Module.finrank (inertiaField K L P) L ∧
      P.ramificationIdx (𝓞 (inertiaField K L P)) = P.ramificationIdx (𝓞 K) := by
  obtain ⟨h1, h2, -⟩ := inertia_general K L P
  haveI := isGG_inertia K L P
  refine ⟨h1, ?_, ?_⟩
  · rw [h2]; exact IsGaloisGroup.card_eq_finrank _ _ _
  · rw [h2]; exact card_inertia_eq_ram K L P

/-- If the decomposition group is normal, it is also the stabilizer of every conjugate of $\mathfrak P$. -/
theorem stabilizer_smul_eq (hD : (MulAction.stabilizer Gal(L/K) P).Normal) (σ : Gal(L/K)) :
    MulAction.stabilizer Gal(L/K) (σ • P) = MulAction.stabilizer Gal(L/K) P := by
  ext τ
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h1 : (σ⁻¹ * τ * σ) ∈ MulAction.stabilizer Gal(L/K) P := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, h, inv_smul_smul]
    have := hD.conj_mem _ h1 σ
    simpa [mul_assoc] using this
  · intro h
    have h1 : (σ⁻¹ * τ * σ) ∈ MulAction.stabilizer Gal(L/K) P :=
      by simpa [mul_assoc] using hD.conj_mem _ (MulAction.mem_stabilizer_iff.mpr h) σ⁻¹
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul] at h1
    calc τ • σ • P = σ • σ⁻¹ • τ • σ • P := by rw [smul_inv_smul]
      _ = σ • P := by rw [h1]

/-- **Proposition 8.11(a)** (proved): the only prime ideal of $L$ lying over $\mathfrak P_D = \mathfrak P \cap L^D$ is
$\mathfrak P$. -/
@[kb "milne2020ant" "v3.08, Prop. 8.11(a), p. 140"]
theorem prop_8_11a :
    (P.under (𝓞 (decompField K L P))).primesOver (𝓞 L) = {P} := by
  haveI := isGG_decomp K L P
  exact (decomp_general K L P (decompField K L P)).1

/-- $L^D \subseteq L^I$, since $I(\mathfrak P) \subseteq D(\mathfrak P)$. -/
theorem decompField_le_inertiaField : decompField K L P ≤ inertiaField K L P :=
  IntermediateField.fixedField_antitone (Ideal.inertia_le_stabilizer P)

/-- The inertia field as an algebra over the decomposition field (inclusion of subfields of $L$). -/
@[instance_reducible]
def inertiaFieldAlgebra : Algebra (decompField K L P) (inertiaField K L P) :=
  (IntermediateField.inclusion (decompField_le_inertiaField K L P)).toRingHom.toAlgebra

/-- **Proposition 8.11(b)** (proved): $\mathfrak P_D$ is unramified in $L^I$ (every prime of $L^I$ above it has
ramification index $1$) and $f(\mathfrak P_I/\mathfrak P_D) = f(\mathfrak P/\mathfrak p)$. The inertia field is an
algebra over the decomposition field by inclusion (`inertiaFieldAlgebra`). -/
@[kb "milne2020ant" "v3.08, Prop. 8.11(b), p. 140"]
theorem prop_8_11b :
    letI := inertiaFieldAlgebra K L P
    (∀ Q ∈ (P.under (𝓞 (decompField K L P))).primesOver (𝓞 (inertiaField K L P)),
        Q.ramificationIdx (𝓞 (decompField K L P)) = 1) ∧
      (P.under (𝓞 (inertiaField K L P))).inertiaDeg (𝓞 (decompField K L P)) =
        P.inertiaDeg (𝓞 K) := by
  letI := inertiaFieldAlgebra K L P
  haveI := isGG_decomp K L P
  obtain ⟨hs, he, hf⟩ := decomp_general K L P (decompField K L P)
  obtain ⟨-, hc2, hc3⟩ := inertia_facts K L P
  obtain ⟨-, -, hc4⟩ := inertia_general K L P
  have hT : IsScalarTower (𝓞 (decompField K L P)) (𝓞 (inertiaField K L P)) (𝓞 L) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  have eD := Ideal.ramificationIdx_tower (R := 𝓞 K) (P.under (𝓞 (decompField K L P))) P
  have fD := Ideal.inertiaDeg_tower (R := 𝓞 K) (P.under (𝓞 (decompField K L P))) P
  have eE := Ideal.ramificationIdx_tower (R := 𝓞 (decompField K L P))
    (P.under (𝓞 (inertiaField K L P))) P
  have fE := Ideal.inertiaDeg_tower (R := 𝓞 (decompField K L P))
    (P.under (𝓞 (inertiaField K L P))) P
  have hpos : 0 < P.ramificationIdx (𝓞 K) := by
    rw [← card_inertia_eq_ram K L P]; exact Nat.card_pos
  refine ⟨?_, ?_⟩
  · rintro Q ⟨hQ, hQo⟩
    obtain ⟨⟨P', hP', hP'o⟩⟩ : Nonempty (Q.primesOver (𝓞 L)) := inferInstance
    haveI : P'.LiesOver (P.under (𝓞 (decompField K L P))) := Ideal.LiesOver.trans P' Q _
    have hP'P : P' ∈ (P.under (𝓞 (decompField K L P))).primesOver (𝓞 L) := ⟨hP', inferInstance⟩
    rw [hs, Set.mem_singleton_iff] at hP'P
    have hQ' : Q = P.under (𝓞 (inertiaField K L P)) := by
      have := Ideal.LiesOver.over (p := Q) (P := P')
      rwa [hP'P] at this
    subst hQ'
    rw [he, one_mul] at eD
    rw [← eD, hc3] at eE
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact eE.symm)
  · rw [hf, one_mul] at fD
    rw [hc4, mul_one] at fE
    rw [fD, fE]

/-- **Proposition 8.11(c)** (proved): $\mathfrak P_I = \mathfrak P \cap L^I$ is totally ramified in $L$ ($\mathfrak P$
is the only prime above it and $e(\mathfrak P/\mathfrak P_I) = [L : L^I]$), and $e(\mathfrak P/\mathfrak P_I) =
e(\mathfrak P/\mathfrak p)$. -/
@[kb "milne2020ant" "v3.08, Prop. 8.11(c), p. 140"]
theorem prop_8_11c :
    (P.under (𝓞 (inertiaField K L P))).primesOver (𝓞 L) = {P} ∧
      P.ramificationIdx (𝓞 (inertiaField K L P)) = Module.finrank (inertiaField K L P) L ∧
      P.ramificationIdx (𝓞 (inertiaField K L P)) = P.ramificationIdx (𝓞 K) :=
  inertia_facts K L P

/-- **Remark after Proposition 8.11** (proved): in general $\mathfrak p\mathcal O_{L^D} = \prod\mathfrak P_i^{e_i}$
with $\mathfrak P_1 = \mathfrak P_D$ and $e_1 = f_1 = 1$. -/
@[kb "milne2020ant" "v3.08, Prop. 8.11 (remark after the proof), p. 140"]
theorem prop_8_11_decompField :
    (P.under (𝓞 (decompField K L P))).ramificationIdx (𝓞 K) = 1 ∧
      (P.under (𝓞 (decompField K L P))).inertiaDeg (𝓞 K) = 1 := by
  haveI := isGG_decomp K L P
  obtain ⟨-, h1, h2⟩ := decomp_general K L P (decompField K L P)
  exact ⟨h1, h2⟩

/-- **Proposition 8.11(d)** (proved): if $D(\mathfrak P)$ is normal in $G$, then $\mathfrak p$ splits completely in
$L^D$: $\mathfrak p\mathcal O_{L^D} = \prod \sigma\mathfrak P_D$, the product of $[G : D(\mathfrak P)]$ distinct
primes, each with $e = f = 1$. -/
@[kb "milne2020ant" "v3.08, Prop. 8.11(d), p. 140"]
theorem prop_8_11d (hD : (MulAction.stabilizer Gal(L/K) P).Normal) :
    (∀ Q ∈ 𝔭.asIdeal.primesOver (𝓞 (decompField K L P)),
        Q.ramificationIdx (𝓞 K) = 1 ∧ Q.inertiaDeg (𝓞 K) = 1) ∧
      (𝔭.asIdeal.primesOver (𝓞 (decompField K L P))).ncard =
        (MulAction.stabilizer Gal(L/K) P).index := by
  haveI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have hGG : ∀ P' ∈ 𝔭.asIdeal.primesOver (𝓞 L),
      IsGaloisGroup (MulAction.stabilizer Gal(L/K) P') (decompField K L P) L := by
    intro P' hP'
    haveI := hP'.1
    haveI := hP'.2
    obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal P P' Gal(L/K)
    rw [stabilizer_smul_eq K L P hD σ]
    exact isGG_decomp K L P
  have hlift : ∀ Q ∈ 𝔭.asIdeal.primesOver (𝓞 (decompField K L P)),
      ∃ P' ∈ 𝔭.asIdeal.primesOver (𝓞 L), P'.under (𝓞 (decompField K L P)) = Q := by
    rintro Q ⟨hQ, hQo⟩
    obtain ⟨⟨P', hP', hP'o⟩⟩ : Nonempty (Q.primesOver (𝓞 L)) := inferInstance
    haveI : P'.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans P' Q 𝔭.asIdeal
    exact ⟨P', ⟨hP', inferInstance⟩, Ideal.LiesOver.over.symm⟩
  refine ⟨?_, ?_⟩
  · intro Q hQ
    obtain ⟨P', hP', rfl⟩ := hlift Q hQ
    haveI := hP'.1
    haveI := hP'.2
    haveI := hGG P' hP'
    obtain ⟨-, h1, h2⟩ := decomp_general K L P' (decompField K L P)
    exact ⟨h1, h2⟩
  · set T := 𝔭.asIdeal.primesOver (𝓞 L) with hTdef
    have hTcard : T.ncard = (MulAction.stabilizer Gal(L/K) P).index := by
      rw [MulAction.index_stabilizer,
        Algebra.IsInvariant.orbit_eq_primesOver (𝓞 K) (𝓞 L) Gal(L/K) 𝔭.asIdeal P]
    rw [← hTcard]
    have himg : (fun P' : Ideal (𝓞 L) => P'.under (𝓞 (decompField K L P))) '' T =
        𝔭.asIdeal.primesOver (𝓞 (decompField K L P)) := by
      ext Q
      constructor
      · rintro ⟨P', hP', rfl⟩
        haveI := hP'.1
        haveI := hP'.2
        refine ⟨inferInstance, ⟨?_⟩⟩
        rw [Ideal.under_under]
        exact Ideal.LiesOver.over
      · intro hQ
        obtain ⟨P', hP', hP'Q⟩ := hlift Q hQ
        exact ⟨P', hP', hP'Q⟩
    have hinj : Set.InjOn (fun P' : Ideal (𝓞 L) => P'.under (𝓞 (decompField K L P))) T := by
      intro P1 h1 P2 h2 h12
      haveI := h1.1
      haveI := h1.2
      haveI := h2.1
      haveI := hGG P1 h1
      haveI : P2.LiesOver (P1.under (𝓞 (decompField K L P))) := ⟨h12⟩
      obtain ⟨h3, -, -⟩ := decomp_general K L P1 (decompField K L P)
      have : P2 ∈ (P1.under (𝓞 (decompField K L P))).primesOver (𝓞 L) :=
        ⟨inferInstance, inferInstance⟩
      rw [h3] at this
      exact (Set.mem_singleton_iff.mp this).symm
    rw [← himg, hinj.ncard_image]

end Prop811


end

end NumberFieldKB.MilneANT
