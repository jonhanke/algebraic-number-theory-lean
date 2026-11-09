import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNFMain
import QuadFormsKB.Literature.HasseNorm.Main
import QuadFormsKB.Lattices.SACorrection
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Lattices.KneserLocal
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF
import QuadFormsKB.Lattices.StrongApproximationProof
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Tamagawa.FormClassNF
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationNF
import QuadFormsKB.Literature.LocalGlobal.PrescribedNF
import QuadFormsKB.Literature.Classical.SumsOfSquares
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Witt.Cancellation
import QuadFormsKB.Literature.LocalGlobal.HasseConventionsNF
import QuadFormsKB.Citation

/-!
# Milne, *Class Field Theory*, Chapter VIII §6: the classification of quadratic forms over a number field

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §6,
printed pp. 250–258 (printed page = pdf page − 9).

Most of this section is formalized in QuadFormsKB (proved without class field theory; Lemma 6.13 by a
Chebotarev-type argument with Dedekind zeta functions instead of Milne's idèlic argument); the theorems below restate
it in Milne's form. Over a field of characteristic $0$, forms are `QuadForm F n`; diagonal forms
$\langle a_0, \dots, a_{n-1}\rangle$ are `QuadForm.diag a` (0-based: Milne's $a_1, \dots, a_n$ are $a_0, \dots,
a_{n-1}$). Milne's Hasse invariant $S(q) = \prod_{i \le j}(a_i, a_j)$ is QuadFormsKB's `NFPlace.hasseOMeara` for
coefficients in $F$ and `hasseS` below for coefficients in a local field.

New here: Lemma 6.13 in Milne's form (`lemma_6_13`), Proposition 6.11 (`prop_6_11`), the realizability statement over
$\mathbb R$ (`realizable_real`), Proposition 6.2 in Milne's subspace form (`prop_6_2`). Named statements: Lemma 6.8
(`Lemma6_8`, O'Meara 58:1), Theorem 6.12 (`Theorem6_12`, O'Meara 72:1).
-/

open NumberField IsDedekindDomain QuadFormsKB

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

/-! ## Generalities -/

/-- **Proposition 6.2** (Milne, *CFT*, VIII, Proposition 6.2, p. 251; Witt's theorem): let $U$, $W$ be isometric
subspaces of a finite-dimensional quadratic space $(V, Q)$ over a field of characteristic $\ne 2$, with $Q|_U$
nondegenerate. Then $U^\perp$ and $W^\perp$ are isometric. Here $(V,Q)$ is nondegenerate, Milne's standing
convention in the proof (QuadFormsKB's Witt extension theorem `QuadraticForm.exists_isometryEquiv_extend_of_associated`
extends the isometry $U \to W$ to $V$). Orthogonal complements are for the polar form; isometries of subspaces are
isometries of the restricted forms. -/
@[kb "milne2020cft" "Ch. VIII, Proposition 6.2, p. 251"]
theorem prop_6_2 {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Invertible (2 : k)] (h2 : (2 : k) ≠ 0) (Q : QuadraticForm k V) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (U W : Submodule k V) (e : (Q.comp U.subtype).IsometryEquiv (Q.comp W.subtype))
    (hU : (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate) :
    Nonempty ((Q.comp (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) U).subtype).IsometryEquiv
      (Q.comp (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) W).subtype)) := by
  -- Extend the isometry `U → W` to an isometry `ρ` of `(V, Q)` (Witt), then restrict `ρ` to `U^⊥ → W^⊥`.
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_associated Q hQ
    (W := U) (W.subtype ∘ₗ e.toLinearEquiv.toLinearMap)
    (Subtype.val_injective.comp e.toLinearEquiv.injective) (fun u => by
      have := e.map_app u
      exact this)
  have hB : ∀ x y : V, QuadraticMap.associated Q (ρ x) (ρ y) = QuadraticMap.associated Q x y := by
    intro x y
    have hadd : ρ x + ρ y = ρ (x + y) := (ρ.toLinearEquiv.map_add x y).symm
    rw [QuadraticMap.associated_apply, QuadraticMap.associated_apply, hadd, ρ.map_app, ρ.map_app,
      ρ.map_app]
  have hρU : ∀ u : U, ρ u = (e u : V) := fun u => hρ u
  have hmap : (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) U).map ρ.toLinearEquiv.toLinearMap =
      LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) W := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      obtain ⟨u, hu⟩ := e.toLinearEquiv.surjective ⟨w, hw⟩
      have hρu : ρ u = w := by rw [hρU u]; exact congrArg Subtype.val hu
      have hx' := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) u u.2
      replace hx' : QuadraticMap.associated Q u x = 0 := hx'
      show QuadraticMap.associated Q w (ρ x) = 0
      rw [← hρu, hB]
      exact hx'
    · intro hy
      refine ⟨ρ.toLinearEquiv.symm y, ?_, ρ.toLinearEquiv.apply_symm_apply y⟩
      rw [SetLike.mem_coe]
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      have hw : ρ u ∈ W := by
        rw [hρU ⟨u, hu⟩]; exact (e ⟨u, hu⟩).2
      have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) (ρ u) hw
      replace h1 : QuadraticMap.associated Q (ρ u) y = 0 := h1
      show QuadraticMap.associated Q u _ = 0
      have hz : ρ (ρ.toLinearEquiv.symm y) = y := ρ.toLinearEquiv.apply_symm_apply y
      rw [← hB u (ρ.toLinearEquiv.symm y), hz]
      exact h1
  exact ⟨{ toLinearEquiv := LinearEquiv.ofSubmodules ρ.toLinearEquiv _ _ hmap
           map_app' := fun x => ρ.map_app x }⟩

/-- **Lemma 6.8** (named statement; Milne, *CFT*, VIII, Lemma 6.8, p. 254, citing O'Meara 58:1): any two orthogonal
bases $B$, $B'$ of a nondegenerate quadratic space $(V,Q)$ over a field of characteristic $\ne 2$ are joined by a
chain of orthogonal bases $B = B_1, \dots, B_m = B'$, each obtained from the previous one by altering at most two
adjacent elements. (O'Meara 58:1 assumes $\dim V \ge 3$; for $\dim V \le 2$ the statement is immediate: any two
bases differ in at most two adjacent elements.) Bases are indexed by `Fin n`. -/
@[kb "milne2020cft" "Ch. VIII, Lemma 6.8, p. 254 (input; O'Meara 58:1)"]
structure Lemma6_8 : Prop where
  chain : ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [Invertible (2 : k)] (_ : (2 : k) ≠ 0) (n : ℕ)
    (Q : QuadraticForm k V), (QuadraticMap.associated Q).Nondegenerate →
    ∀ B B' : Module.Basis (Fin n) k V,
      (∀ i j, i ≠ j → QuadraticMap.associated Q (B i) (B j) = 0) →
      (∀ i j, i ≠ j → QuadraticMap.associated Q (B' i) (B' j) = 0) →
      ∃ (m : ℕ) (C : Fin (m + 1) → Module.Basis (Fin n) k V), C 0 = B ∧ C (Fin.last m) = B' ∧
        (∀ l i j, i ≠ j → QuadraticMap.associated Q (C l i) (C l j) = 0) ∧
        ∀ l : Fin m, ∃ i : ℕ, ∀ j : Fin n, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 →
          C l.castSucc j = C l.succ j

/-! ## Local fields -/

/-- Milne's Hasse invariant $S(q) = \prod_{i \le j} (a_i, a_j)$ of a diagonal form $\langle a_0, \dots,
a_{n-1}\rangle$ with coefficients in a field $K$ (QuadFormsKB's `hilbertSymbol K`); for coefficients in a number field
and $K$ a completion it is QuadFormsKB's `NFPlace.hasseOMeara` (`hasseOMeara_finite_eq_hasseS`). -/
@[kb "milne2020cft" "Ch. VIII, §6, p. 253 (the Hasse invariant S(q))"]
def hasseS (K : Type*) [Field K] {n : ℕ} (a : Fin n → K) : ℤ :=
  ∏ i, ∏ j, if i ≤ j then hilbertSymbol K (a i) (a j) else 1

/-- Comparison with QuadFormsKB: at a finite place the two Hasse invariants agree. -/
theorem hasseOMeara_finite_eq_hasseS {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (a : Fin n → F) :
    (NFPlace.finite v).hasseOMeara a = hasseS (v.adicCompletion F) (fun i => algebraMap F _ (a i)) := by
  rfl

section LocalField

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => v.adicCompletion F

/-- The completion $F_v$ at a finite prime satisfies QuadFormsKB's Hilbert-symbol axioms
(bimultiplicativity, nondegeneracy, isotropy of rank 5). -/
private lemma hK : PadicClass.LocalHilbertField Kv := HasseIsoNF.localHilbertField_adicCompletion v

/-- **Lemma 6.5 (a)** (Milne, *CFT*, VIII, Lemma 6.5 (a), p. 253): over a completion $K = F_v$ at a finite prime,
the Hilbert symbol is bimultiplicative on $K^\times \times K^\times$ and invariant under squares in either
variable: $(aa', b) = (a,b)(a',b)$, $(a, bb') = (a,b)(a,b')$, $(ac^2, b) = (a,b) = (a, bc^2)$ ($c \ne 0$). -/
@[kb "milne2020cft" "Ch. VIII, Lemma 6.5 (a), p. 253"]
theorem lemma_6_5a :
    (∀ a a' b : Kv, a ≠ 0 → a' ≠ 0 → b ≠ 0 →
      hilbertSymbol Kv (a * a') b = hilbertSymbol Kv a b * hilbertSymbol Kv a' b) ∧
    (∀ a b b' : Kv, a ≠ 0 → b ≠ 0 → b' ≠ 0 →
      hilbertSymbol Kv a (b * b') = hilbertSymbol Kv a b * hilbertSymbol Kv a b') ∧
    (∀ a b c : Kv, c ≠ 0 → hilbertSymbol Kv (a * c ^ 2) b = hilbertSymbol Kv a b) ∧
    (∀ a b c : Kv, c ≠ 0 → hilbertSymbol Kv a (b * c ^ 2) = hilbertSymbol Kv a b) := by
  refine ⟨fun a a' b ha ha' hb => (hK v).mul_left a a' b ha ha' hb,
    fun a b b' ha hb hb' => (hK v).mul_right ha hb hb', fun a b c hc => ?_, fun a b c hc => ?_⟩
  · rw [mul_comm]; exact PadicClass.hs_sq_left a b c hc
  · rw [mul_comm]; exact PadicClass.hs_sq_right a b c hc

/-- **Lemma 6.5 (b)** (Milne, *CFT*, VIII, Lemma 6.5 (b), p. 253): for a nonsquare $a \in K^\times$ there is
$b \in K^\times$ with $(a,b) = -1$ (nondegeneracy). -/
@[kb "milne2020cft" "Ch. VIII, Lemma 6.5 (b), p. 253"]
theorem lemma_6_5b (a : Kv) (ha : a ≠ 0) (hns : ¬ IsSquare a) :
    ∃ b : Kv, b ≠ 0 ∧ hilbertSymbol Kv a b = -1 :=
  (hK v).exists_neg_one a ha hns

/-- **Lemma 6.5 (c)** (Milne, *CFT*, VIII, Lemma 6.5 (c), p. 253): $(b,a) = (a,b)$; since the values are $\pm1$
this equals $(a,b)^{-1}$. -/
@[kb "milne2020cft" "Ch. VIII, Lemma 6.5 (c), p. 253"]
theorem lemma_6_5c (a b : Kv) : hilbertSymbol Kv b a = hilbertSymbol Kv a b :=
  hilbertSymbol_comm _ b a

/-- **Lemma 6.5 (d)** (Milne, *CFT*, VIII, Lemma 6.5 (d), p. 253): $(a,-a) = 1$ for $a \ne 0$ and $(a, 1-a) = 1$
for $a \ne 0, 1$. -/
@[kb "milne2020cft" "Ch. VIII, Lemma 6.5 (d), p. 253"]
theorem lemma_6_5d :
    (∀ a : Kv, a ≠ 0 → hilbertSymbol Kv a (-a) = 1) ∧
    (∀ a : Kv, a ≠ 0 → a ≠ 1 → hilbertSymbol Kv a (1 - a) = 1) := by
  refine ⟨fun a _ => hilbertSymbol_self_neg _ a, fun a _ _ => ?_⟩
  unfold hilbertSymbol
  rw [if_pos]
  exact ⟨1, 1, 1, by simp, by ring⟩

omit [NumberField F] in
/-- The Hasse invariant of a form with a coefficient `x` adjoined in front. -/
private lemma hasseS_cons {K : Type*} [Field K] {n : ℕ} (x : K) (a : Fin n → K) :
    hasseS K (Fin.cons x a : Fin (n + 1) → K) =
      hilbertSymbol K x x * (∏ j, hilbertSymbol K x (a j)) * hasseS K a := by
  unfold hasseS
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]; simp
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_le_succ_iff, Fin.succ_ne_zero]

/-- $F_v$ has a nonsquare (it has at least $4$ square classes). -/
private lemma exists_nonsquare : ∃ u : Kv, u ≠ 0 ∧ ¬ IsSquare u := by
  by_contra hcon
  push_neg at hcon
  have h1 : ∀ x : SqDual.SqCl Kv, x = 1 := fun x => by
    induction x using QuotientGroup.induction_on with
    | H a => exact (SqDual.mk_eq_one_iff_isSquare _ a).mpr (hcon a a.ne_zero)
  have : Subsingleton (SqDual.SqCl Kv) := ⟨fun x y => by rw [h1 x, h1 y]⟩
  have h2 := Finite.card_le_one_iff_subsingleton.mpr this
  have h4 := LocalRankFive.four_le_card_sqCl v
  omega

/-- Rank 1 of Proposition 6.11. -/
private lemma ex1 (d : Kv) (s : ℤ) (hd : d ≠ 0) (hs : s = hilbertSymbol Kv (-1) d) :
    ∃ a : Fin 1 → Kv, (∀ i, a i ≠ 0) ∧ (∃ c : Kv, c ≠ 0 ∧ ∏ i, a i = d * c ^ 2) ∧ hasseS Kv a = s := by
  refine ⟨fun _ => d, fun _ => hd, ⟨1, one_ne_zero, by simp⟩, ?_⟩
  simp only [hasseS, Fin.prod_univ_one, le_refl, if_true]
  rw [(hK v).self hd, hilbertSymbol_comm, hs]

/-- Rank 2 of Proposition 6.11 (Milne's case analysis, using Lemma 6.5 (b)). -/
private lemma ex2 (d : Kv) (s : ℤ) (hd : d ≠ 0) (hs : s = 1 ∨ s = -1)
    (h2 : (∃ c : Kv, d = -1 * c ^ 2) → s = hilbertSymbol Kv (-1) (-1)) :
    ∃ a : Fin 2 → Kv, (∀ i, a i ≠ 0) ∧ (∃ c : Kv, c ≠ 0 ∧ ∏ i, a i = d * c ^ 2) ∧ hasseS Kv a = s := by
  have key : ∀ x : Kv, x ≠ 0 → hasseS Kv ![x, d * x] =
      hilbertSymbol Kv x (-d) * hilbertSymbol Kv (-1) d := by
    intro x hx
    have hdx : d * x ≠ 0 := mul_ne_zero hd hx
    have e0 : hasseS Kv ![x, d * x] = hilbertSymbol Kv x x * hilbertSymbol Kv x (d * x) *
        hilbertSymbol Kv (d * x) (d * x) := by
      simp [hasseS, Fin.prod_univ_two]
    rw [e0, (hK v).self hx, (hK v).self hdx, (hK v).mul_right hx hd hx, (hK v).self hx,
      (hK v).mul_left d x (-1) hd hx (by norm_num), show -d = -1 * d by ring,
      (hK v).mul_right hx (by norm_num) hd, hilbertSymbol_comm _ (-1) d]
    rcases PadicClass.hs_pm x (-1 : Kv) with h | h <;> rw [h] <;> ring
  obtain ⟨x, hx0, hx⟩ : ∃ x : Kv, x ≠ 0 ∧
      hilbertSymbol Kv x (-d) = s * hilbertSymbol Kv (-1) d := by
    by_cases e : s * hilbertSymbol Kv (-1) d = 1
    · exact ⟨1, one_ne_zero, by rw [e, hilbertSymbol_comm]; exact hilbertSymbol_one_right _ _⟩
    · have e' : s * hilbertSymbol Kv (-1) d = -1 := by
        rcases hs with rfl | rfl <;> rcases PadicClass.hs_pm (-1 : Kv) d with h | h <;>
          simp_all
      have hns : ¬ IsSquare (-d) := by
        rintro ⟨y, hy⟩
        have hy0 : y ≠ 0 := by rintro rfl; simp at hy; exact hd hy
        have hdy : d = -1 * y ^ 2 := by linear_combination -hy
        have hs1 := h2 ⟨y, hdy⟩
        have hs2 : hilbertSymbol Kv (-1) d = hilbertSymbol Kv (-1) (-1) := by
          rw [hdy]; exact (lemma_6_5a v).2.2.2 _ _ _ hy0
        rw [hs1, hs2] at e'
        rcases PadicClass.hs_pm (-1 : Kv) (-1) with h | h <;> rw [h] at e' <;> norm_num at e'
      obtain ⟨b, hb0, hb⟩ := lemma_6_5b v (-d) (neg_ne_zero.mpr hd) hns
      exact ⟨b, hb0, by rw [hilbertSymbol_comm, hb, e']⟩
  refine ⟨![x, d * x], fun i => ?_, ⟨x, hx0, ?_⟩, ?_⟩
  · fin_cases i <;> simp [hx0, hd]
  · simp [Fin.prod_univ_two]; ring
  · rw [key x hx0, hx]
    rcases hs with rfl | rfl <;> rcases PadicClass.hs_pm (-1 : Kv) d with h | h <;> rw [h] <;> norm_num

/-- Adding a coefficient to a form of rank `n` (the inductive step of Proposition 6.11 for rank $\ge 3$). -/
private lemma cons_step {n : ℕ} (d : Kv) (s : ℤ) (hd : d ≠ 0) (hs : s = 1 ∨ s = -1) (u : Kv) (hu0 : u ≠ 0)
    (H : ∃ a' : Fin n → Kv, (∀ i, a' i ≠ 0) ∧ (∃ c : Kv, c ≠ 0 ∧ ∏ i, a' i = -u * c ^ 2) ∧
      hasseS Kv a' = s * hilbertSymbol Kv d u) :
    ∃ a : Fin (n + 1) → Kv, (∀ i, a i ≠ 0) ∧ (∃ c : Kv, c ≠ 0 ∧ ∏ i, a i = d * c ^ 2) ∧
      hasseS Kv a = s := by
  obtain ⟨a', ha', ⟨c, hc0, hprod⟩, hS⟩ := H
  have hnu : -u ≠ 0 := neg_ne_zero.mpr hu0
  have hx : d * -u ≠ 0 := mul_ne_zero hd hnu
  refine ⟨Fin.cons (d * -u) a', PadicClass.cons_ne_zero hx ha', ⟨c * -u, mul_ne_zero hc0 hnu, ?_⟩, ?_⟩
  · rw [Fin.prod_cons, hprod]; ring
  · rw [hasseS_cons, (hK v).self hx, PadicClass.hs_prod_right (hK v) hx ha', hprod,
      (lemma_6_5a v).2.2.2 _ _ _ hc0, hS, ← mul_assoc, ← (hK v).mul_right hx (by norm_num) hnu,
      show (-1 : Kv) * -u = u by ring, (hK v).mul_left d (-u) u hd hnu hu0, hilbertSymbol_comm _ (-u) u,
      show (-u) = -u from rfl]
    have h1 : hilbertSymbol Kv u (-u) = 1 := hilbertSymbol_self_neg _ u
    rw [h1]
    rcases PadicClass.hs_pm d u with h | h <;> rw [h] <;> rcases hs with rfl | rfl <;> norm_num

/-- Rank at least $3$ of Proposition 6.11: every $(d, s)$ occurs (induction on the rank, adjoining one coefficient). -/
private lemma exN (hu : ∃ u : Kv, u ≠ 0 ∧ ¬ IsSquare u) : ∀ m : ℕ, ∀ (d : Kv) (s : ℤ), d ≠ 0 → (s = 1 ∨ s = -1) →
    ∃ a : Fin (m + 3) → Kv, (∀ i, a i ≠ 0) ∧ (∃ c : Kv, c ≠ 0 ∧ ∏ i, a i = d * c ^ 2) ∧
      hasseS Kv a = s := by
  obtain ⟨u, hu0, hus⟩ := hu
  intro m
  induction m with
  | zero =>
    intro d s hd hs
    refine cons_step v d s hd hs u hu0 (ex2 v (-u) _ (neg_ne_zero.mpr hu0) ?_ ?_)
    · rcases hs with rfl | rfl <;> rcases PadicClass.hs_pm d u with h | h <;> rw [h] <;> norm_num
    · rintro ⟨c, hc⟩
      exact absurd ⟨c, by linear_combination -hc⟩ hus
  | succ m ih =>
    intro d s hd hs
    refine cons_step v d s hd hs u hu0 (ih (-u) _ (neg_ne_zero.mpr hu0) ?_)
    rcases hs with rfl | rfl <;> rcases PadicClass.hs_pm d u with h | h <;> rw [h] <;> norm_num

/-- **Proposition 6.11** (Milne, *CFT*, VIII, Proposition 6.11, p. 255): over a nonarchimedean local field $K$ (here a
completion $F_v$ of a number field at a finite prime), the invariants of a form of rank $n$ satisfy (a) if $n = 1$,
$S(q) = (-1, d)$; (b) if $n = 2$ and $d(q) = -1$ (mod squares), $S(q) = (-1,-1)$. Apart from these constraints every
triple $n \ge 1$, $d \in K^\times/K^{\times2}$, $s = \pm1$ occurs. -/
@[kb "milne2020cft" "Ch. VIII, Proposition 6.11, p. 255"]
theorem prop_6_11 :
    (∀ a : Fin 1 → Kv, (∀ i, a i ≠ 0) → hasseS Kv a = hilbertSymbol Kv (-1) (∏ i, a i)) ∧
    (∀ a : Fin 2 → Kv, (∀ i, a i ≠ 0) → (∃ c : Kv, ∏ i, a i = -1 * c ^ 2) →
      hasseS Kv a = hilbertSymbol Kv (-1) (-1)) ∧
    ∀ (n : ℕ) (d : Kv) (s : ℤ), 1 ≤ n → d ≠ 0 → (s = 1 ∨ s = -1) →
      (n = 1 → s = hilbertSymbol Kv (-1) d) → (n = 2 → (∃ c : Kv, d = -1 * c ^ 2) → s = hilbertSymbol Kv (-1) (-1)) →
      ∃ a : Fin n → Kv, (∀ i, a i ≠ 0) ∧ (∃ c : Kv, c ≠ 0 ∧ ∏ i, a i = d * c ^ 2) ∧ hasseS Kv a = s := by
  refine ⟨fun a ha => ?_, fun a ha ⟨c, hc⟩ => ?_, fun n d s hn hd hs h1 h2 => ?_⟩
  · simp only [hasseS, Fin.prod_univ_one, le_refl, if_true]
    rw [(hK v).self (ha 0), hilbertSymbol_comm]
  · simp only [Fin.prod_univ_two] at hc
    have key : hasseS Kv a = hilbertSymbol Kv (a 0) (a 0) * hilbertSymbol Kv (a 0) (a 1) *
        hilbertSymbol Kv (a 1) (a 1) := by
      simp [hasseS, Fin.prod_univ_two]
    have h0 := ha 0
    have h1 := ha 1
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc
      rcases hc with h | h
      · exact h0 h
      · exact h1 h
    have ha1 : a 1 = (-a 0) * (c / a 0) ^ 2 := by
      apply mul_left_cancel₀ h0
      have hq : a 0 * (c / a 0) = c := by field_simp
      calc a 0 * a 1 = -1 * c ^ 2 := hc
        _ = a 0 * (-a 0 * (c / a 0) ^ 2) := by linear_combination (a 0 * (c / a 0) + c) * hq
    have e1 : hilbertSymbol Kv (a 0) (a 1) = 1 := by
      rw [ha1, (lemma_6_5a v).2.2.2 _ _ _ (div_ne_zero hc0 h0)]
      exact hilbertSymbol_self_neg _ _
    rw [key, e1, (hK v).self h0, (hK v).self h1, hilbertSymbol_comm _ (a 0), hilbertSymbol_comm _ (a 1),
      mul_one, ← (hK v).mul_right (by norm_num) h0 h1, hc]
    exact (lemma_6_5a v).2.2.2 _ _ _ hc0
  · rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · exact ex1 v d s hd (h1 rfl)
      · exact ex2 v d s hd hs (h2 rfl)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      exact exN v (exists_nonsquare v) m d s hd hs

end LocalField

/-- Over $\mathbb R$, for $x, y \in \{\pm1\}$, $(x,y) = -1$ iff $x, y < 0$. -/
private lemma hs_real_pm (x y : ℝ) (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    hilbertSymbol ℝ x y = if x < 0 ∧ y < 0 then -1 else 1 := by
  have hx0 : x ≠ 0 := by rcases hx with h | h <;> simp [h]
  have hy0 : y ≠ 0 := by rcases hy with h | h <;> simp [h]
  have := hilbertSymbol_real x y hx0 hy0
  rcases HN.hilbertSymbol_eq_one_or ℝ x y with h | h
  · rw [h]
    rw [if_neg]
    intro hc
    have := this.mpr hc
    omega
  · rw [h, if_pos (this.mp h)]

/-- Counting pairs $i \le j$ among the last $t$ of $n$ indices: $t(t+1)/2$. -/
private lemma count_aux (n t : ℕ) (ht : t ≤ n) :
    ∑ i ∈ Finset.range n, (if n - t ≤ i then n - i else 0) = t * (t + 1) / 2 := by
  induction t with
  | zero => simp; intro i hi h; omega
  | succ t ih =>
    have ih := ih (by omega)
    have h : ∀ i ∈ Finset.range n, (if n - (t+1) ≤ i then n - i else 0) =
        (if n - t ≤ i then n - i else 0) + (if i = n - (t+1) then t + 1 else 0) := by
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases h1 : i = n - (t+1)
      · subst h1
        have : ¬ (n - t ≤ n - (t+1)) := by omega
        simp only [if_neg this, if_true]
        rw [if_pos (le_refl _)]; omega
      · by_cases h2 : n - t ≤ i
        · rw [if_pos h2, if_pos (by omega), if_neg h1]; simp
        · rw [if_neg h2, if_neg h1]
          by_cases h3 : n - (t+1) ≤ i
          · exfalso; omega
          · simp [h3]
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih,
      Finset.sum_ite_eq' (Finset.range n) (n - (t+1)) (fun _ => t + 1)]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
    have : (t + 1) * (t + 1 + 1) = t * (t + 1) + 2 * (t + 1) := by ring
    rw [this]
    omega

/-- **Realizability over $\mathbb R$** (Milne, *CFT*, VIII, §6, p. 256, "Generalities" (b)): over $\mathbb R$, the
system $(n, d, s, t)$ is realizable by $\langle 1, \dots, 1, -1, \dots, -1\rangle$ ($t$ entries $-1$) whenever
$0 \le t \le n$, $d = (-1)^t$, $s = (-1)^{t(t+1)/2}$; and the Hasse invariant of a real form is $(-1)^{t(t+1)/2}$. -/
@[kb "milne2020cft" "Ch. VIII, §6, p. 256 (realizability over R; S(q) over R)"]
theorem realizable_real (n t : ℕ) (ht : t ≤ n) :
    hasseS ℝ (fun i : Fin n => if (i : ℕ) < n - t then (1 : ℝ) else -1) = (-1) ^ (t * (t + 1) / 2) ∧
      ∏ i : Fin n, (if (i : ℕ) < n - t then (1 : ℝ) else -1) = (-1) ^ t := by
  constructor
  · have h : ∀ i j : Fin n, (if i ≤ j then hilbertSymbol ℝ (if (i : ℕ) < n - t then (1 : ℝ) else -1)
        (if (j : ℕ) < n - t then (1 : ℝ) else -1) else 1) =
        (-1 : ℤ) ^ (if n - t ≤ (i : ℕ) ∧ i ≤ j then 1 else 0) := by
      intro i j
      rw [hs_real_pm _ _ (by split_ifs <;> simp) (by split_ifs <;> simp)]
      by_cases h1 : (i : ℕ) < n - t <;> by_cases h2 : (j : ℕ) < n - t <;> by_cases h3 : i ≤ j <;>
        simp [h1, h2, h3] <;> (try split_ifs) <;> first | omega | (norm_num at *)
    unfold hasseS
    simp_rw [h]
    simp only [Finset.prod_pow_eq_pow_sum]
    congr 1
    have hin : ∀ i : Fin n, (∑ j : Fin n, (if n - t ≤ (i : ℕ) ∧ i ≤ j then 1 else 0)) =
        (if n - t ≤ (i : ℕ) then n - (i : ℕ) else 0) := by
      intro i
      by_cases hi : n - t ≤ (i : ℕ)
      · simp only [hi, true_and, if_true, Fin.le_def]
        rw [Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) ≤ j then 1 else 0) n]
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        have : (Finset.range n).filter (fun j => (i : ℕ) ≤ j) = Finset.Ico (i : ℕ) n := by
          ext j; simp [Finset.mem_Ico]; omega
        rw [this]; simp
      · simp [hi]
    simp only [hin]
    rw [Fin.sum_univ_eq_sum_range (fun i => if n - t ≤ i then n - i else 0) n]
    exact count_aux n t ht
  · have h : ∀ i : Fin n, (if (i : ℕ) < n - t then (1 : ℝ) else -1) =
        (-1 : ℝ) ^ (if n - t ≤ (i : ℕ) then 1 else 0) := by
      intro i
      by_cases h1 : (i : ℕ) < n - t
      · simp [h1, not_le.mpr h1]
      · simp [h1, not_lt.mp h1]
    simp only [h, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun i => if n - t ≤ i then 1 else 0) n]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have : (Finset.range n).filter (fun j => n - t ≤ j) = Finset.Ico (n - t) n := by
      ext j; simp [Finset.mem_Ico]; omega
    rw [this]; simp; omega

/-! ## Global fields -/

section Global

variable (F : Type) [Field F] [NumberField F]

open Classical in
/-- **Lemma 6.13** (Milne, *CFT*, VIII, Lemma 6.13, p. 256): let $T$ be a finite set of real or finite primes of $F$
with an even number of elements and $b \in F^\times$ not a square in $F_v$ for any $v \in T$. There is $a \in F^\times$
with $(a,b)_v = -1$ for $v \in T$ and $(a,b)_v = 1$ otherwise. From QuadFormsKB's `exists_prescribed_hilbert_nf`. -/
@[kb "milne2020cft" "Ch. VIII, Lemma 6.13, p. 256"]
theorem lemma_6_13 (T : Set (NFPlace F)) (hT : T.Finite) (hreal : ∀ w : InfinitePlace F, NFPlace.infinite w ∈ T → w.IsReal)
    (heven : Even T.ncard) (b : F) (hb : b ≠ 0)
    (hsq : ∀ v ∈ T, v.atPlace fun K _ _ => ¬ IsSquare (algebraMap F K b)) :
    ∃ a : F, a ≠ 0 ∧ ∀ v : NFPlace F, v.hilbert a b = if v ∈ T then -1 else 1 := by
  have h1 : {v : NFPlace F | ∃ _ : Unit, (fun (_ : Unit) (v : NFPlace F) => (if v ∈ T then (-1 : ℤ) else 1)) () v = -1}.Finite := by
    refine hT.subset fun v hv => ?_
    obtain ⟨_, hv⟩ := hv
    by_contra hvT
    simp [hvT] at hv
  have h2 : ∀ _ : Unit, Even {v : NFPlace F | (fun (_ : Unit) (v : NFPlace F) => (if v ∈ T then (-1 : ℤ) else 1)) () v = -1}.ncard := by
    intro _
    have : {v : NFPlace F | (fun (_ : Unit) (v : NFPlace F) => (if v ∈ T then (-1 : ℤ) else 1)) () v = -1} = T := by
      ext v
      by_cases hv : v ∈ T <;> simp [hv]
    rw [this]; exact heven
  have h3 : ∀ v : NFPlace F, v.atPlace fun K _ _ =>
      ∃ x : K, x ≠ 0 ∧ ∀ _ : Unit, hilbertSymbol K (algebraMap F K b) x =
        (fun (_ : Unit) (v : NFPlace F) => (if v ∈ T then (-1 : ℤ) else 1)) () v := by
    intro v
    cases v with
    | finite p =>
      by_cases hv : NFPlace.finite p ∈ T
      · have hs : ¬ IsSquare (algebraMap F (p.adicCompletion F) b) := hsq _ hv
        obtain ⟨y, hy0, hy⟩ := (HasseIsoNF.localHilbertField_adicCompletion p).exists_neg_one
          (algebraMap F _ b) (by simpa using hb) hs
        exact ⟨y, hy0, fun _ => by simp only [if_pos hv]; exact hy⟩
      · exact ⟨1, one_ne_zero, fun _ => by simp only [if_neg hv]; exact hilbertSymbol_one_right _ _⟩
    | infinite w =>
      by_cases hv : NFPlace.infinite w ∈ T
      · have hw := hreal w hv
        have hs : ¬ IsSquare (algebraMap F w.Completion b) := hsq _ hv
        let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
        have hneg : e (algebraMap F w.Completion b) < 0 := by
          by_contra hnn
          push_neg at hnn
          apply hs
          refine ⟨e.symm (Real.sqrt (e (algebraMap F w.Completion b))), ?_⟩
          apply e.injective
          rw [map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hnn]
        refine ⟨e.symm (-1), by simp, fun _ => ?_⟩
        simp only [if_pos hv]
        rw [← HasseIsoNF.hilbertSymbol_ringEquiv e]
        simp only [RingEquiv.apply_symm_apply]
        exact (hilbertSymbol_real _ _ hneg.ne (by norm_num)).mpr ⟨hneg, by norm_num⟩
      · exact ⟨1, one_ne_zero, fun _ => by simp only [if_neg hv]; exact hilbertSymbol_one_right _ _⟩
  obtain ⟨x, hx0, hx⟩ := NFInputs.exists_prescribed_hilbert_nf (ι := Unit) (fun _ => b) (fun _ => hb)
    (fun _ v => if v ∈ T then (-1 : ℤ) else 1) (fun _ v => by by_cases hv : v ∈ T <;> simp [hv]) h1 h2 h3
  refine ⟨x, hx0, fun v => ?_⟩
  have hxv : v.hilbert b x = if v ∈ T then -1 else 1 := hx () v
  rw [← hxv]
  cases v <;> exact hilbertSymbol_comm _ _ _

/-- **Theorem 6.12** (named statement; Milne, *CFT*, VIII, Theorem 6.12, p. 256; O'Meara 72:1): let $n \in \mathbb N$
and, for each prime $v$ of $F$, a nondegenerate quadratic form $q_v$ of rank $n$ over $F_v$ (diagonal, without loss
of generality: `QuadForm.diag (a v)`, finite primes, and `QuadForm.diag (b w)`, infinite primes). There is a form
$q_0$ over $F$ with $(q_0)_v \cong q_v$ for every $v$ iff (a) some $d_0 \in F^\times$ is $d(q_v)$ modulo
$F_v^{\times2}$ for all $v$, and (b) $S(q_v) = 1$ for almost all $v$ and $\prod_v S(q_v) = 1$. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 6.12, p. 256 (input; O'Meara 72:1)"]
structure Theorem6_12 : Prop where
  iff : ∀ (n : ℕ) (a : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (b : ∀ w : InfinitePlace F, Fin n → w.Completion), (∀ v i, a v i ≠ 0) → (∀ w i, b w i ≠ 0) →
    ((∃ q₀ : QuadForm F n, q₀.Nondegenerate ∧
        (∀ v, (q₀.map (algebraMap F (v.adicCompletion F))).IsometricIn (v.adicCompletion F) (QuadForm.diag (a v))) ∧
        ∀ w, (q₀.map (algebraMap F w.Completion)).IsometricIn w.Completion (QuadForm.diag (b w))) ↔
      (∃ d₀ : F, d₀ ≠ 0 ∧ (∀ v, ∃ c : v.adicCompletion F, c ≠ 0 ∧ ∏ i, a v i = algebraMap F _ d₀ * c ^ 2) ∧
          ∀ w, ∃ c : w.Completion, c ≠ 0 ∧ ∏ i, b w i = algebraMap F _ d₀ * c ^ 2) ∧
        {v | hasseS (v.adicCompletion F) (a v) ≠ 1}.Finite ∧
        (∏ᶠ v, hasseS (v.adicCompletion F) (a v)) * ∏ w, hasseS w.Completion (b w) = 1)

end Global

end NumberFieldKB.MilneCFT.Ch8
