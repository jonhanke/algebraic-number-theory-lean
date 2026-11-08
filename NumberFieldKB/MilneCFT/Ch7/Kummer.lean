import NumberFieldKB.MilneCFT.Ch7.Basic
import QuadFormsKB.Literature.HasseNorm.SquareClasses
import QuadFormsKB.Literature.HasseNorm.Infinite

/-!
# Milne, *Class Field Theory*, Chapter VII §6: the algebraic proof of the second inequality

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

Notation. $K$ is a number field, $n\ge1$, $p$ a prime. For a finite prime $v$: $K_v$ (`v.adicCompletion K`), its unit
group $U_v$ (`localUnits v`), the $n$-th powers $K_v^{\times n}$ (`(powMonoidHom n).range`). For a set $S$ of finite
primes, $U(S)$ is Mathlib's `S.unit K` (the $S$-units; Milne's $S$ also contains the infinite primes, whose number is
added in the counts $s$ below). The local index $(K_v^\times : K_v^{\times n})$ is computed by Proposition 6.8.

* **Lemma 6.5** (`lemma_6_5`): $(AC:BC)(A\cap C:B\cap C) = (A:B)$ for subgroups $B\subseteq A$, $C$ of an abelian group.
* **Proposition 6.8** (`Prop6_8`, named statement, for the finite completions of number fields; the archimedean case
  `prop_6_8_real`, `prop_6_8_complex` is proved; the case $n = 2$ is QuadFormsKB's `index_sq_completion`,
  `index_sq_U0`).
* **Lemma 6.9**, **Proposition 6.10**, **Lemmas 6.2–6.4, 6.6, 6.7**: see below.
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

/-! ## Lemma 6.5 -/

/-- **Lemma 6.5** (Milne, *CFT*, Chapter VII, p. 216): let $A$, $B$, $C$ be subgroups of an abelian group with
$B\subseteq A$. Then $(AC : BC)(A\cap C : B\cap C) = (A:B)$, in the sense that if two of the indexes are finite, so is
the third, and the equality holds. Here with `Subgroup.relIndex` (value $0$ for an infinite index), the equality in
$\mathbb N$ holds without finiteness hypotheses and contains the finiteness statement. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.5"]
theorem lemma_6_5 {G : Type*} [CommGroup G] {A B C : Subgroup G} (hBA : B ≤ A) :
    (B ⊔ C).relIndex (A ⊔ C) * (B ⊓ C).relIndex (A ⊓ C) = B.relIndex A := by
  have h1 : A ⊔ (B ⊔ C) = A ⊔ C := by
    rw [← sup_assoc, sup_eq_left.mpr hBA]
  have hD : A ⊓ (B ⊔ C) = B ⊔ (A ⊓ C) := by
    ext x
    constructor
    · rintro ⟨hxA, hx⟩
      obtain ⟨b, hb, c, hc, rfl⟩ := Subgroup.mem_sup.mp hx
      have hcA : c ∈ A := by
        have := A.mul_mem (A.inv_mem (hBA hb)) hxA
        simpa using this
      exact Subgroup.mem_sup.mpr ⟨b, hb, c, ⟨hcA, hc⟩, rfl⟩
    · intro hx
      obtain ⟨b, hb, c, hc, rfl⟩ := Subgroup.mem_sup.mp hx
      exact ⟨A.mul_mem (hBA hb) hc.1, Subgroup.mem_sup.mpr ⟨b, hb, c, hc.2, rfl⟩⟩
  have hBE : B ⊓ (A ⊓ C) = B ⊓ C := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hBA h.1, h.2⟩⟩
  have e1 : (B ⊔ C).relIndex (A ⊔ C) = (B ⊔ C).relIndex A := by
    rw [← h1]
    exact Subgroup.relIndex_sup_right _ _
  have e2 : B.relIndex (B ⊔ (A ⊓ C)) = (B ⊓ C).relIndex (A ⊓ C) := by
    rw [sup_comm, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right, hBE]
  have e3 : B.relIndex (A ⊓ (B ⊔ C)) = B.relIndex (B ⊔ (A ⊓ C)) := by rw [hD]
  have hle : B ≤ B ⊔ (A ⊓ C) := le_sup_left
  have hle2 : B ⊔ (A ⊓ C) ≤ A := sup_le hBA inf_le_left
  rw [← Subgroup.relIndex_mul_relIndex B _ A hle hle2, e2, e1, ← hD, Subgroup.inf_relIndex_left,
    mul_comm]

/-! ## Proposition 6.8 -/

variable (K : Type) [Field K] [NumberField K]

/-- The units $U_v$ of $K_v$. -/
abbrev localUnits (v : HeightOneSpectrum (𝓞 K)) : Subgroup (v.adicCompletion K)ˣ :=
  (v.adicCompletionIntegers K).units

/-- The number of $n$-th roots of $1$ in a field. -/
def numRootsOfUnity (F : Type*) [Field F] (n : ℕ) : ℕ := Nat.card (rootsOfUnity n F)

/-- **The quantity $h_n(M)$** (definition in prose; Milne, *CFT*, Chapter VII, proof of Proposition 6.8, p. 218): for an
abelian group $M$, $h_n(M) = (M : nM)/(M_n : 1)$, $M_n = \{x : nx = 0\}$ (the Herbrand quotient of $M$ as a module
with trivial action of $\mathbb Z/n\mathbb Z$; meaningful when both are finite). -/
@[kb "milne2020cft" "Ch. VII, proof of Prop. 6.8, p. 218 (h_n(M))"]
def herbrandN (M : Type*) [AddCommGroup M] (n : ℕ) : ℚ :=
  ((nsmulAddMonoidHom n : M →+ M).range.index : ℚ) / Nat.card {x : M // n • x = 0}

/-- $\mathrm{ord}_v(n)$ for a positive integer $n$: the exponent of $v$ in $n\mathcal O_K$. -/
def ordNat (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(n : 𝓞 K)})).factors

/-- **Proposition 6.8** (named statement; Milne, *CFT*, Chapter VII, p. 217), nonarchimedean case: for a finite prime
$v$ of $K$ and $n\ge1$, with $\mu_n$ the $n$-th roots of $1$ in $K_v$ and $|n|_v = N\mathfrak p^{-\mathrm{ord}_v n}$,
$(K_v^\times : K_v^{\times n}) = n\,|\mu_n|/|n|_v$ and $(U_v : U_v^n) = |\mu_n|/|n|_v$. (Milne states it for local fields
of characteristic zero; the completions of number fields at finite primes are those fields up to isomorphism.) -/
@[kb "milne2020cft" "Ch. VII, Prop. 6.8 (input, nonarchimedean case)"]
structure Prop6_8 : Prop where
  index_pow : ∀ (v : HeightOneSpectrum (𝓞 K)) (n : ℕ), 0 < n →
    (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index =
      n * numRootsOfUnity (v.adicCompletion K) n * Ideal.absNorm v.asIdeal ^ ordNat K v n
  index_pow_units : ∀ (v : HeightOneSpectrum (𝓞 K)) (n : ℕ), 0 < n →
    (powMonoidHom n : localUnits K v →* localUnits K v).range.index =
      numRootsOfUnity (v.adicCompletion K) n * Ideal.absNorm v.asIdeal ^ ordNat K v n

/-- **Proposition 6.8, $K_v = \mathbb R$** (Milne, *CFT*, Chapter VII, p. 218): $(\mathbb R^\times:\mathbb R^{\times n})
= n|\mu_n(\mathbb R)|/|n|$, i.e. $2$ for $n$ even and $1$ for $n$ odd. -/
@[kb "milne2020cft" "Ch. VII, Prop. 6.8 (K = ℝ)"]
theorem prop_6_8_real (n : ℕ) (hn : 0 < n) :
    ((powMonoidHom n : ℝˣ →* ℝˣ).range.index : ℚ) = n * numRootsOfUnity ℝ n / n := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hroot : ∀ c : ℝ, 0 < c → ∃ d : ℝ, 0 < d ∧ d ^ n = c := fun c hc =>
    ⟨c ^ ((n : ℝ)⁻¹), Real.rpow_pos_of_pos hc _, Real.rpow_inv_natCast_pow hc.le hn.ne'⟩
  have hpm : ∀ ζ : ℝˣ, ζ ^ n = 1 → ζ = 1 ∨ ζ = -1 := by
    intro ζ hζ
    have h1 : (ζ : ℝ) ^ n = 1 := by
      have := congrArg Units.val hζ
      simpa using this
    have h2 : |(ζ : ℝ)| = 1 := by
      have : |(ζ : ℝ)| ^ n = 1 := by rw [← abs_pow, h1, abs_one]
      exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hn.ne').mp this
    rcases abs_eq (zero_le_one) |>.mp h2 with h | h
    · left; exact Units.ext h
    · right; exact Units.ext h
  rcases Nat.even_or_odd n with he | ho
  · have hsq : ∀ c : ℝˣ, c ∈ (powMonoidHom n : ℝˣ →* ℝˣ).range ↔ 0 < (c : ℝ) := by
      intro c
      constructor
      · rintro ⟨d, rfl⟩
        simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val]
        exact he.pow_pos (Units.ne_zero d)
      · intro hc
        obtain ⟨d, hd, hdc⟩ := hroot c hc
        exact ⟨Units.mk0 d hd.ne', by ext; simpa using hdc⟩
    have hidx : (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨-1, fun b => ?_⟩
      rw [hsq, hsq]
      simp only [Units.val_neg, mul_neg, mul_one, Left.neg_pos_iff]
      rcases lt_or_gt_of_ne (Units.ne_zero b) with h | h
      · simp [h, not_lt.mpr h.le]
      · simp [h, not_lt.mpr h.le]
    have hcard : numRootsOfUnity ℝ n = 2 := by
      unfold numRootsOfUnity
      rw [Nat.card_eq_two_iff]
      have hm1 : (-1 : ℝˣ) ^ n = 1 := he.neg_one_pow
      refine ⟨⟨1, by simp⟩, ⟨-1, by simpa [mem_rootsOfUnity] using hm1⟩, ?_, ?_⟩
      · intro h
        have := congrArg Subtype.val h
        have h' : (1 : ℝˣ) = -1 := this
        have := congrArg Units.val h'
        norm_num at this
      · ext ⟨ζ, hζ⟩
        simp only [Set.mem_univ, iff_true, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.mk.injEq]
        exact hpm ζ ((mem_rootsOfUnity _ _).mp hζ)
    rw [hidx, hcard]
    push_cast
    field_simp
  · have htop : (powMonoidHom n : ℝˣ →* ℝˣ).range = ⊤ := by
      rw [eq_top_iff]
      intro c _
      rcases lt_or_gt_of_ne (Units.ne_zero c) with h | h
      · obtain ⟨d, hd, hdc⟩ := hroot (-(c : ℝ)) (by linarith)
        refine ⟨-(Units.mk0 d hd.ne'), ?_⟩
        ext
        simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_mk0]
        rw [ho.neg_pow, hdc]; ring
      · obtain ⟨d, hd, hdc⟩ := hroot c h
        exact ⟨Units.mk0 d hd.ne', by ext; simpa using hdc⟩
    have hcard : numRootsOfUnity ℝ n = 1 := by
      unfold numRootsOfUnity
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
      have key : ∀ ζ : rootsOfUnity n ℝ, ζ = 1 := by
        rintro ⟨ζ, hζ⟩
        rcases hpm ζ ((mem_rootsOfUnity _ _).mp hζ) with h | h
        · exact Subtype.ext h
        · exfalso
          have hm := (mem_rootsOfUnity _ _).mp hζ
          rw [h, ho.neg_one_pow] at hm
          have := congrArg Units.val hm
          norm_num at this
      rw [key a, key b]
    rw [Subgroup.index_eq_one.mpr htop, hcard]
    push_cast
    field_simp

/-- **Proposition 6.8, $K_v = \mathbb C$** (Milne, *CFT*, Chapter VII, p. 218): $(\mathbb C^\times:\mathbb C^{\times n})
= 1 = n\cdot n/n^2$ (normalized absolute value $|n|_{\mathbb C} = n^2$). -/
@[kb "milne2020cft" "Ch. VII, Prop. 6.8 (K = ℂ)"]
theorem prop_6_8_complex (n : ℕ) (hn : 0 < n) :
    ((powMonoidHom n : ℂˣ →* ℂˣ).range.index : ℚ) = n * numRootsOfUnity ℂ n / (n ^ 2 : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have : NeZero n := ⟨hn.ne'⟩
  have htop : (powMonoidHom n : ℂˣ →* ℂˣ).range = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ) hn
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hr
      exact (Units.ne_zero c) hr.symm
    exact ⟨Units.mk0 r hr0, by ext; simp [hr]⟩
  have hcard : numRootsOfUnity ℂ n = n := by
    unfold numRootsOfUnity
    exact Complex.card_rootsOfUnity n
  rw [Subgroup.index_eq_one.mpr htop, hcard]
  push_cast
  field_simp

end NumberFieldKB.MilneCFT.Ch7
