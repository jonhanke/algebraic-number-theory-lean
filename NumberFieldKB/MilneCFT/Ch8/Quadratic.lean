import NumberFieldKB.MilneCFT.Ch7
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

/-!
# Milne, *Class Field Theory*, Chapter VIII §3: the local-global principle for norms and quadratic forms

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §3,
printed pp. 234–239 (printed page = pdf page − 9).

Quadratic forms in $n$ variables over a field are QuadFormsKB's `QuadForm F n` (upper-triangular coefficient
matrix; `IsotropicIn K` = has a nontrivial zero over $K$, Milne's "represents $0$"; `RepresentsIn K c` = takes the
value $c$ over $K$, which for $c \ne 0$ is Milne's "represents $c$"; `Nondegenerate` = the Hessian has nonzero
determinant, Milne's nondegenerate in characteristic $\ne 2$). Lemma 3.3 is stated for Mathlib's general
`QuadraticForm` on a vector space, as Milne states it.

* **Theorem 3.1** (Hasse norm theorem, cyclic extensions): named statement `HasseNormTheorem`; the quadratic case is
  proved in QuadFormsKB (`theorem_3_1_quadratic`).
* **Remark 3.2**: named statement `Remark3_2` ($5^2$ and $\mathbb Q[\sqrt{13},\sqrt{17}]$).
* **Lemma 3.3** (`lemma_3_3`), **Lemma 3.4** (`lemma_3_4`), **Theorem 3.5** (`theorem_3_5a`, `theorem_3_5b`),
  **Corollary 3.6** (`cor_3_6`), **Proposition 3.7** (`prop_3_7a` … `prop_3_7d`), **Lemma 3.8** (`lemma_3_8`),
  **Proposition 3.9** (`prop_3_9`), **Corollary 3.10** (`cor_3_10`), **Corollary 3.11** (`cor_3_11`),
  **Remark 3.12** (`remark_3_12`, `remark_3_12_corrected`): proved.
-/

open NumberField IsDedekindDomain QuadFormsKB

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

/-! ## Norms -/

section Norms

variable (K : Type) [Field K] [NumberField K]

/-- $a \in K^\times$ is a local norm from $L$ at the finite prime $v$: its image in $K_v^\times$ lies in the local norm
group of Chapter VII (`Ch7.localNormGroup`, the elements of $K_v^\times$ whose idèle is a norm from $\mathbb I_L$;
by Chapter VII, 2.5 this is $\mathrm{Nm}(L\otimes_KK_v)^\times$). -/
def IsLocalNorm (L : Type) [Field L] [NumberField L] [Algebra K L] (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Prop :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a ∈ Ch7.localNormGroup L v

/-- $a \in K^\times$ is a local norm from $L$ at the infinite prime $w$. -/
def IsLocalNormInf (L : Type) [Field L] [NumberField L] [Algebra K L] (a : Kˣ) (w : InfinitePlace K) : Prop :=
  Units.map (algebraMap K w.Completion).toMonoidHom a ∈ Ch7.localNormGroupInf L w

/-- **Theorem 3.1, the Hasse norm theorem** (named statement; Milne, *CFT*, VIII, Theorem 3.1, p. 234; Milne's proof
uses $H^1(G, C_L) = 0$, Chapter VII, Theorem 5.1): let $L/K$ be a cyclic extension of number fields and
$a \in K^\times$. Then $a$ is a norm from $L_v$ for all but finitely many $v$, and if it is a norm for all $v$
(finite and infinite), then it is a norm from $L$. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 3.1, p. 234 (Hasse norm theorem; input)"]
structure HasseNormTheorem : Prop where
  almost_all : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L], IsCyclic Gal(L/K) →
    ∀ a : Kˣ, {v : HeightOneSpectrum (𝓞 K) | ¬ IsLocalNorm K L a v}.Finite
  norm : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L], IsCyclic Gal(L/K) →
    ∀ a : Kˣ, (∀ v, IsLocalNorm K L a v) → (∀ w, IsLocalNormInf K L a w) →
      ∃ b : L, Algebra.norm K b = (a : K)

/-- **Theorem 3.1 for quadratic extensions** (proved in QuadFormsKB, `HasseNorm.hilbert_eq_one_of_everywhere`, by
Chevalley's algebraic second inequality, without class field theory): for $a, b \in K^\times$, $b$ is a norm from
$K[\sqrt a]$ (the Hilbert symbol $(a,b)_K = 1$, QuadFormsKB's `hilbertSymbol`) if it is a norm everywhere locally
($(a,b)_v = 1$ at every place $v$). -/
@[kb "milne2020cft" "Ch. VIII, Theorem 3.1, p. 234 (quadratic case)"]
theorem theorem_3_1_quadratic (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (h : ∀ v : NFPlace K, v.hilbert a b = 1) :
    hilbertSymbol K a b = 1 :=
  HasseNorm.hilbert_eq_one_of_everywhere a b ha hb h

/-- **Remark 3.2** (named statement; Milne, *CFT*, VIII, Remark 3.2, p. 234, citing Cassels–Fröhlich, Exercise 5.3):
the Hasse norm theorem fails for noncyclic extensions: $5^2$ is a local norm from $L = \mathbb Q[\sqrt{13},\sqrt{17}]$
at all primes but is not a global norm. ($L$ is any number field generated over $\mathbb Q$ by square roots $s, t$ of
$13$ and $17$.) -/
@[kb "milne2020cft" "Ch. VIII, Remark 3.2, p. 234 (input)"]
structure Remark3_2 : Prop where
  counterexample : ∀ (L : Type) [Field L] [NumberField L] (s t : L), s ^ 2 = 13 → t ^ 2 = 17 →
    IntermediateField.adjoin ℚ ({s, t} : Set L) = ⊤ →
      (∀ v, IsLocalNorm ℚ L (Units.mk0 (25 : ℚ) (by norm_num)) v) ∧ (∀ w, IsLocalNormInf ℚ L (Units.mk0 (25 : ℚ) (by norm_num)) w) ∧
        ¬ ∃ b : L, Algebra.norm ℚ b = 25

end Norms

/-! ## Quadratic forms: generalities -/

/-- **Lemma 3.3** (Milne, *CFT*, VIII, Lemma 3.3, p. 235): if a nondegenerate quadratic form $Q$ on a vector space
$V$ over a field $k$ represents $0$ (a nonzero isotropic vector), then it represents every $c \in k$ by a nonzero
vector. Nondegenerate: the bilinear form $B(v,w) = Q(v+w) - Q(v) - Q(w)$ (Mathlib's `QuadraticMap.polarBilin`) is
nondegenerate. No assumption on the characteristic is needed. -/
@[kb "milne2020cft" "Ch. VIII, Lemma 3.3, p. 235"]
theorem lemma_3_3 {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (Q : QuadraticForm k V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h0 : ∃ v : V, v ≠ 0 ∧ Q v = 0) (c : k) :
    ∃ w : V, w ≠ 0 ∧ Q w = c := by
  obtain ⟨v, hv, hQv⟩ := h0
  by_cases hc : c = 0
  · exact ⟨v, hv, by rw [hQv, hc]⟩
  have hex : ∃ w, QuadraticMap.polarBilin Q v w ≠ 0 := by
    by_contra hcon
    exact hv (hQ.1 v (by simpa using hcon))
  obtain ⟨w, hw⟩ := hex
  have hB : QuadraticMap.polarBilin Q v w = QuadraticMap.polar Q v w := rfl
  rw [hB] at hw
  refine ⟨((c - Q w) / QuadraticMap.polar Q v w) • v + w, ?_, ?_⟩
  · intro h
    have : Q (((c - Q w) / QuadraticMap.polar Q v w) • v + w) = c := by
      rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQv, QuadraticMap.polar_smul_left]
      simp only [smul_eq_mul, mul_zero]
      field_simp
      ring
    rw [h, QuadraticMap.map_zero] at this
    exact hc this.symm
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQv, QuadraticMap.polar_smul_left]
    simp only [smul_eq_mul, mul_zero]
    field_simp
    ring

section Diag

variable {F : Type} [Field F] [CharZero F] {n : ℕ}

/-- **Lemma 3.4** (Milne, *CFT*, VIII, Lemma 3.4, p. 235; QuadFormsKB's
`QuadForm.representsIn_iff_isotropicIn_orthSum`): a nondegenerate form $q$ represents $a \in F^\times$ over a field
$K \supseteq F$ iff $r = q \perp \langle -a\rangle = q - aY^2$ represents $0$ over $K$. (Milne's $a$ ranges over $k$;
for $a = 0$ the form $r$ is degenerate and always isotropic, so $a \ne 0$ is needed, as in Milne's proof.) -/
@[kb "milne2020cft" "Ch. VIII, Lemma 3.4, p. 235"]
theorem lemma_3_4 (K : Type*) [Field K] [Algebra F K] {q : QuadForm F n} (hq : q.Nondegenerate) (a : F) :
    q.RepresentsIn K a ↔ (QuadForm.orthSum q (QuadForm.diag ![-a])).IsotropicIn K :=
  QuadForm.representsIn_iff_isotropicIn_orthSum K hq a

end Diag

section LocalGlobal

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Theorem 3.5 (a)** (Milne, *CFT*, VIII, Theorem 3.5 (a), p. 235; QuadFormsKB's `Lattices.finite_anisotropic`): a
nondegenerate quadratic form in $n \ge 3$ variables over a number field $F$ represents $0$ in $F_v$ for all but
finitely many $v$. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 3.5 (a), p. 235"]
theorem theorem_3_5a (q : QuadForm F n) (hq : q.Nondegenerate) (hn : 3 ≤ n) :
    {v : HeightOneSpectrum (𝓞 F) | ¬ q.IsotropicIn (v.adicCompletion F)}.Finite :=
  Lattices.finite_anisotropic q hq hn

/-- **Theorem 3.5 (b)** (Hasse–Minkowski; Milne, *CFT*, VIII, Theorem 3.5 (b), p. 235; QuadFormsKB's
`hasseMinkowski_nf`, proved without class field theory): a nondegenerate quadratic form over a number field $F$
represents $0$ in $F$ if it represents $0$ in $F_v$ for all $v$ (finite and infinite). -/
@[kb "milne2020cft" "Ch. VIII, Theorem 3.5 (b), p. 235"]
theorem theorem_3_5b (q : QuadForm F n) (hq : q.Nondegenerate)
    (h : NFPlace.Everywhere (F := F) fun K _ _ => q.IsotropicIn K) : q.IsotropicIn F :=
  (hasseMinkowski_nf q hq).mpr h

/-- **Corollary 3.6** (Milne, *CFT*, VIII, Corollary 3.6, p. 236; QuadFormsKB's `represents_iff_everywhere_nf`): a
nondegenerate quadratic form $q$ over a number field $F$ represents $c \in F^\times$ in $F$ iff it represents $c$ in
$F_v$ for all $v$. ($c = 0$ is Theorem 3.5 (b).) -/
@[kb "milne2020cft" "Ch. VIII, Corollary 3.6, p. 236"]
theorem cor_3_6 (q : QuadForm F n) (hq : q.Nondegenerate) (c : F) (hc : c ≠ 0) :
    q.RepresentsIn F c ↔ NFPlace.Everywhere (F := F) fun K _ _ => q.RepresentsIn K c :=
  represents_iff_everywhere_nf q hq c hc

end LocalGlobal

/-! ## Proposition 3.7 and Lemma 3.8: forms of rank at most $4$ and norms -/

section Prop37

variable {k : Type*} [Field k]

/-- Every element of $F(\delta)$ with $\delta^2 \in F$ has the form $x + y\delta$ with $x, y \in F$. -/
theorem exists_eq_add_mul_of_mem_adjoin {F E : Type*} [Field F] [Field E] [Algebra F E] (δ : E) (d : F)
    (hδ : δ ^ 2 = algebraMap F E d) {m : E} (hm : m ∈ IntermediateField.adjoin F {δ}) :
    ∃ x y : F, m = algebraMap F E x + algebraMap F E y * δ := by
  have hint : IsIntegral F δ := ⟨Polynomial.X ^ 2 - Polynomial.C d, Polynomial.monic_X_pow_sub_C d two_ne_zero, by simp [hδ]⟩
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hm
  induction hm using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x1, x2, rfl⟩ := hx
    obtain ⟨y1, y2, rfl⟩ := hy
    exact ⟨x1 + y1, x2 + y2, by simp; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x1, x2, rfl⟩ := hx
    obtain ⟨y1, y2, rfl⟩ := hy
    refine ⟨x1 * y1 + x2 * y2 * d, x1 * y2 + x2 * y1, ?_⟩
    simp only [map_add, map_mul]
    linear_combination (algebraMap F E x2 * algebraMap F E y2) * hδ

/-- **Norms from a quadratic extension.** For $F$ of characteristic $\ne 2$, $d \in F^\times$ and $\delta^2 = d$ in a field
$E \supseteq F$: $c \in F$ is a norm from $F(\delta)$ iff $c = x^2 - d y^2$ with $x, y \in F$ (this includes the case
that $d$ is a square, when $F(\delta) = F$ and every $c$ is both a norm and of the form $x^2 - dy^2$). -/
theorem exists_norm_eq_iff {F E : Type*} [Field F] [Field E] [Algebra F E] (h2 : (2 : F) ≠ 0) (δ : E) (d : F)
    (hd : d ≠ 0) (hδ : δ ^ 2 = algebraMap F E d) (M : IntermediateField F E)
    (hM : M = IntermediateField.adjoin F {δ}) (c : F) :
    (∃ w : M, Algebra.norm F w = c) ↔ ∃ x y : F, x ^ 2 - d * y ^ 2 = c := by
  subst hM
  have hint : IsIntegral F δ := ⟨Polynomial.X ^ 2 - Polynomial.C d, Polynomial.monic_X_pow_sub_C d two_ne_zero, by simp [hδ]⟩
  set M := IntermediateField.adjoin F {δ} with hMdef
  have hδM : δ ∈ M := IntermediateField.subset_adjoin F {δ} (Set.mem_singleton δ)
  have hspan : ∀ m : M, ∃ x y : F, m = algebraMap F M x + algebraMap F M y * ⟨δ, hδM⟩ := by
    intro m
    obtain ⟨x, y, h⟩ := exists_eq_add_mul_of_mem_adjoin δ d hδ m.2
    exact ⟨x, y, Subtype.ext (by simpa using h)⟩
  by_cases hsq : IsSquare d
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; exact hd (by simpa using hr)
    have hrange : δ ∈ (algebraMap F E).range := by
      have h0 : algebraMap F E d = algebraMap F E r * algebraMap F E r := by rw [hr, map_mul]
      have h1 : (δ - algebraMap F E r) * (δ + algebraMap F E r) = 0 := by
        linear_combination hδ + h0
      rcases mul_eq_zero.mp h1 with h | h
      · exact ⟨r, by linear_combination -h⟩
      · exact ⟨-r, by rw [map_neg]; linear_combination -h⟩
    have hfr : Module.finrank F M = 1 := by
      rw [IntermediateField.adjoin.finrank hint, minpoly.natDegree_eq_one_iff]
      exact hrange
    have hRHS : ∃ x y : F, x ^ 2 - d * y ^ 2 = c :=
      ⟨(c + 1) / 2, (c - 1) / (2 * r), by rw [hr]; field_simp; ring⟩
    refine ⟨fun _ => hRHS, fun _ => ⟨algebraMap F M c, ?_⟩⟩
    rw [Algebra.norm_algebraMap, hfr, pow_one]
  · have hδM1 : (⟨δ, hδM⟩ : M) ^ 2 = algebraMap F M d := Subtype.ext (by simpa using hδ)
    have hli : LinearIndependent F ![(1 : M), ⟨δ, hδM⟩] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hE : algebraMap F E s + algebraMap F E t * δ = 0 := by
        have := congrArg (fun m : M => (m : E)) hst
        simpa [Algebra.smul_def] using this
      have ht : t = 0 := by
        by_contra ht
        apply hsq
        refine ⟨(s / t), ?_⟩
        apply (algebraMap F E).injective
        have ht' : algebraMap F E t ≠ 0 := (_root_.map_ne_zero _).mpr ht
        have hδe : δ = -(algebraMap F E s) / algebraMap F E t := by
          field_simp; linear_combination hE
        rw [← hδ, hδe, map_mul, map_div₀]
        field_simp
      subst ht
      simp at hE
      exact ⟨hE, rfl⟩
    have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : M), ⟨δ, hδM⟩]) := by
      intro m _
      obtain ⟨x, y, rfl⟩ := hspan m
      refine Submodule.add_mem _ ?_ ?_
      · have : algebraMap F M x = x • (1 : M) := by simp [Algebra.smul_def]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
      · have : algebraMap F M y * ⟨δ, hδM⟩ = y • (⟨δ, hδM⟩ : M) := by simp [Algebra.smul_def]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
    let b : Module.Basis (Fin 2) F M := Module.Basis.mk hli hsp
    have hb0 : b 0 = 1 := by simp [b]
    have hb1 : b 1 = ⟨δ, hδM⟩ := by simp [b]
    have key : ∀ x y : F, Algebra.norm F (algebraMap F M x + algebraMap F M y * ⟨δ, hδM⟩) =
        x ^ 2 - d * y ^ 2 := by
      intro x y
      rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
      have e0 : (algebraMap F M x + algebraMap F M y * ⟨δ, hδM⟩) * b 0 = x • b 0 + y • b 1 := by
        rw [hb0, hb1]; simp [Algebra.smul_def]
      have e1 : (algebraMap F M x + algebraMap F M y * ⟨δ, hδM⟩) * b 1 = (y * d) • b 0 + x • b 1 := by
        rw [hb0, hb1]
        simp only [Algebra.smul_def, map_mul, mul_one]
        linear_combination (algebraMap F M y) * hδM1
      simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1, map_add, map_smul, Module.Basis.repr_self]
      simp
      ring
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨x, y, rfl⟩ := hspan w
      exact ⟨x, y, by rw [← hw, key]⟩
    · rintro ⟨x, y, hxy⟩
      exact ⟨_, by rw [key, hxy]⟩

/-- If $d$ is a square (and $\operatorname{char} \ne 2$), every $c$ is $x^2 - dy^2$. -/
theorem exists_sq_sub_of_isSquare {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) {a : k} (ha : a ≠ 0)
    (hsq : IsSquare a) (c : k) : ∃ x y : k, x ^ 2 - a * y ^ 2 = c := by
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by rintro rfl; exact ha (by simpa using hr)
  exact ⟨(c + 1) / 2, (c - 1) / (2 * r), by rw [hr]; field_simp; ring⟩

/-- Algebraic core of the hard direction of Lemma 3.8: $c = s^2 + abt^2 - ap^2 - a^2bq^2$ with $st = apq$ is
$(x^2 - ay^2)(z^2 - bw^2)$. -/
theorem key_alg {k : Type*} [Field k] (a b c : k) (ha : a ≠ 0) (s t p q : k) (hB : s * t = a * p * q)
    (hA : s ^ 2 + a * b * t ^ 2 - a * p ^ 2 - a ^ 2 * b * q ^ 2 = c) :
    ∃ x y z w : k, (x ^ 2 - a * y ^ 2) * (z ^ 2 - b * w ^ 2) = c := by
  by_cases hs : s = 0
  · subst hs
    have : p = 0 ∨ q = 0 := by
      have : a * p * q = 0 := by rw [← hB]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact (mul_eq_zero.mp h).elim (fun h => absurd h ha) Or.inl
      · exact Or.inr h
    rcases this with rfl | rfl
    · exact ⟨a * q, t, 0, 1, by linear_combination hA⟩
    · exact ⟨0, 1, p, t, by linear_combination hA⟩
  · refine ⟨1, p / s, s, a * q, ?_⟩
    field_simp
    linear_combination (-a * b * (s * t + a * p * q)) * hB + s ^ 2 * hA

/-- The $\gamma$-coefficient comparison: if $(s + t\gamma)^2 - a(p + q\gamma)^2 = c$ with $\gamma^2 = ab$ then
$c = (x^2 - ay^2)(z^2 - bw^2)$ for some $x, y, z, w \in k$. -/
theorem key_E {k E : Type*} [Field k] [Field E] [Algebra k E] (h2 : (2 : k) ≠ 0) (a b c : k) (ha : a ≠ 0)
    (g : E) (hg : g ^ 2 = algebraMap k E (a * b)) (s t p q : k)
    (h : (algebraMap k E s + algebraMap k E t * g) ^ 2 -
      algebraMap k E a * (algebraMap k E p + algebraMap k E q * g) ^ 2 = algebraMap k E c) :
    ∃ x y z w : k, (x ^ 2 - a * y ^ 2) * (z ^ 2 - b * w ^ 2) = c := by
  by_cases hmem : g ∈ (algebraMap k E).range
  · obtain ⟨g0, rfl⟩ := hmem
    refine ⟨s + t * g0, p + q * g0, 1, 0, ?_⟩
    apply (algebraMap k E).injective
    simp only [map_sub, map_add, map_mul, map_pow, map_one, map_zero] at h ⊢
    linear_combination h
  · have hE : algebraMap k E (s ^ 2 + a * b * t ^ 2 - a * p ^ 2 - a ^ 2 * b * q ^ 2 - c) +
        algebraMap k E (2 * (s * t - a * p * q)) * g = 0 := by
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at hg h ⊢
      linear_combination h - (algebraMap k E t ^ 2 - algebraMap k E a * algebraMap k E q ^ 2) * hg
    by_cases hB : 2 * (s * t - a * p * q) = 0
    · rw [hB, map_zero, zero_mul, add_zero] at hE
      have hA := (map_eq_zero_iff _ (algebraMap k E).injective).mp hE
      have hB' : s * t = a * p * q := by
        have := (mul_eq_zero.mp hB).resolve_left h2
        linear_combination this
      exact key_alg a b c ha s t p q hB' (by linear_combination hA)
    · exfalso
      apply hmem
      refine ⟨-(s ^ 2 + a * b * t ^ 2 - a * p ^ 2 - a ^ 2 * b * q ^ 2 - c) / (2 * (s * t - a * p * q)), ?_⟩
      have hB' : algebraMap k E (2 * (s * t - a * p * q)) ≠ 0 := (_root_.map_ne_zero _).mpr hB
      rw [map_div₀, map_neg, div_eq_iff hB']
      linear_combination -hE

/-- Lemma 3.8, reduced to elementary form: $c$ is a norm from $k(\alpha\beta)(\alpha,\beta)$ down to $k(\alpha\beta)$ iff
$c = (x^2 - ay^2)(z^2 - bw^2)$ with $x,y,z,w \in k$. -/
theorem rhs_iff {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (a b c : k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {E : Type*} [Field E] [Algebra k E] (α β : E) (hα : α ^ 2 = algebraMap k E a)
    (hβ : β ^ 2 = algebraMap k E b) :
    (∃ z : IntermediateField.adjoin (IntermediateField.adjoin k ({α * β} : Set E)) ({α, β} : Set E),
        Algebra.norm (IntermediateField.adjoin k ({α * β} : Set E)) z =
          algebraMap k (IntermediateField.adjoin k ({α * β} : Set E)) c) ↔
      ∃ x y z w : k, (x ^ 2 - a * y ^ 2) * (z ^ 2 - b * w ^ 2) = c := by
  set K0 := IntermediateField.adjoin k ({α * β} : Set E) with hK0
  have hγ : (α * β) ^ 2 = algebraMap k E (a * b) := by rw [mul_pow, hα, hβ, map_mul]
  have hγK : α * β ∈ K0 := IntermediateField.mem_adjoin_simple_self k (α * β)
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply ha
    apply (algebraMap k E).injective
    simpa using hα.symm
  have hM : IntermediateField.adjoin K0 ({α, β} : Set E) = IntermediateField.adjoin K0 ({α} : Set E) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases hx with rfl | hx
      · exact IntermediateField.mem_adjoin_simple_self K0 x
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        have h1 : x = algebraMap K0 E ⟨α * x, hγK⟩ * α⁻¹ := by
          show x = (α * x) * α⁻¹
          field_simp
        rw [h1]
        exact mul_mem (IntermediateField.algebraMap_mem _ _)
          (inv_mem (IntermediateField.mem_adjoin_simple_self K0 α))
    · exact IntermediateField.adjoin.mono K0 _ _ (by simp)
  have h2' : (2 : K0) ≠ 0 := by
    intro h
    apply h2
    have h3 : algebraMap K0 E 2 = algebraMap K0 E 0 := by rw [h]
    have h4 : (2 : E) = 0 := by rwa [map_ofNat, map_zero] at h3
    exact (algebraMap k E).injective (by rw [map_ofNat, map_zero]; exact h4)
  have ha' : algebraMap k K0 a ≠ 0 := (_root_.map_ne_zero _).mpr ha
  have hα' : α ^ 2 = algebraMap K0 E (algebraMap k K0 a) := by
    rw [← IsScalarTower.algebraMap_apply]; exact hα
  rw [exists_norm_eq_iff h2' α _ ha' hα' _ hM]
  constructor
  · rintro ⟨u, v, h⟩
    obtain ⟨s, t, hu⟩ := exists_eq_add_mul_of_mem_adjoin (α * β) (a * b) hγ u.2
    obtain ⟨p, q, hv⟩ := exists_eq_add_mul_of_mem_adjoin (α * β) (a * b) hγ v.2
    have h' := congrArg (fun m : K0 => (m : E)) h
    push_cast at h'
    refine key_E h2 a b c ha (α * β) hγ s t p q ?_
    rw [← hu, ← hv]
    simpa using h'
  · rintro ⟨x, y, z, w, h⟩
    have hmem1 : algebraMap k E (x * z) + algebraMap k E (y * w) * (α * β) ∈ K0 :=
      add_mem (IntermediateField.algebraMap_mem _ _) (mul_mem (IntermediateField.algebraMap_mem _ _) hγK)
    have hmem2 : algebraMap k E (y * z) + algebraMap k E (x * w / a) * (α * β) ∈ K0 :=
      add_mem (IntermediateField.algebraMap_mem _ _) (mul_mem (IntermediateField.algebraMap_mem _ _) hγK)
    refine ⟨⟨_, hmem1⟩, ⟨_, hmem2⟩, Subtype.ext ?_⟩
    push_cast
    have hk1 : x * z * (y * w) - a * (y * z) * (x * w / a) = 0 := by field_simp; ring
    have hk2 : (x * z) ^ 2 + a * b * (y * w) ^ 2 - a * (y * z) ^ 2 - a ^ 2 * b * (x * w / a) ^ 2 = c := by
      rw [← h]; field_simp; ring
    have e1 := congrArg (algebraMap k E) hk2
    have e2 := congrArg (algebraMap k E) hk1
    simp only [map_sub, map_add, map_mul, map_pow, map_zero, map_div₀] at e1 e2 hγ
    show _ = algebraMap k E c
    linear_combination e1 + 2 * (α * β) * e2 + (algebraMap k E y * algebraMap k E w) ^ 2 * hγ -
      algebraMap k E a * (algebraMap k E x * algebraMap k E w / algebraMap k E a) ^ 2 * hγ

/-- **Proposition 3.7 (a)** (Milne, *CFT*, VIII, Proposition 3.7 (a), p. 236): the form $X^2$ does not represent
$0$. -/
@[kb "milne2020cft" "Ch. VIII, Proposition 3.7 (a), p. 236"]
theorem prop_3_7a : ¬ ∃ x : k, x ≠ 0 ∧ x ^ 2 = 0 := by
  rintro ⟨x, hx, h⟩
  exact hx (pow_eq_zero_iff (two_ne_zero) |>.mp h)

/-- **Proposition 3.7 (b)** (Milne, *CFT*, VIII, Proposition 3.7 (b), p. 236): $X^2 - aY^2$ represents $0$ iff $a$ is
a square. -/
@[kb "milne2020cft" "Ch. VIII, Proposition 3.7 (b), p. 236"]
theorem prop_3_7b (a : k) : (∃ x y : k, (x, y) ≠ 0 ∧ x ^ 2 - a * y ^ 2 = 0) ↔ IsSquare a := by
  constructor
  · rintro ⟨x, y, hxy, h⟩
    have hy : y ≠ 0 := by
      rintro rfl
      have hx : x = 0 := by simpa using h
      exact hxy (by simp [hx])
    exact ⟨x / y, by field_simp; linear_combination (-1 : k) * h⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, 1, by simp, by rw [hr]; ring⟩

/-- **Proposition 3.7 (c)** (Milne, *CFT*, VIII, Proposition 3.7 (c), p. 236): over a field $k$ of characteristic
$\ne 2$, for $a, b \in k^\times$, $X^2 - aY^2 - bZ^2$ represents $0$ iff $b$ is a norm from the field $k[\sqrt a]$.
Here $\sqrt a$ is a square root $\alpha$ of $a$ in any extension field $E$, and $k[\sqrt a] = k(\alpha)$
(`IntermediateField.adjoin`; it is $k$ when $a$ is a square). -/
@[kb "milne2020cft" "Ch. VIII, Proposition 3.7 (c), p. 236"]
theorem prop_3_7c (h2 : (2 : k) ≠ 0) (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) {E : Type*} [Field E] [Algebra k E]
    (α : E) (hα : α ^ 2 = algebraMap k E a) :
    (∃ x y z : k, (x, y, z) ≠ 0 ∧ x ^ 2 - a * y ^ 2 - b * z ^ 2 = 0) ↔
      ∃ w : IntermediateField.adjoin k ({α} : Set E), Algebra.norm k w = b := by
  rw [exists_norm_eq_iff h2 α a ha hα _ rfl b]
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    by_cases hz : z = 0
    · subst hz
      have hxy : (x, y) ≠ 0 := fun h0 => hne (by simp_all [Prod.ext_iff])
      exact exists_sq_sub_of_isSquare h2 ha ((prop_3_7b a).mp ⟨x, y, hxy, by linear_combination h⟩) b
    · exact ⟨x / z, y / z, by field_simp; linear_combination h⟩
  · rintro ⟨x, y, hxy⟩
    exact ⟨x, y, 1, by simp [Prod.ext_iff], by linear_combination hxy⟩

/-- **Lemma 3.8** (Milne, *CFT*, VIII, Lemma 3.8, p. 236): over a field $k$ of characteristic $\ne 2$, an element
$c \in k^\times$ is the product of a norm from $k[\sqrt a]$ and a norm from $k[\sqrt b]$ iff, as an element of
$k[\sqrt{ab}]$, it is a norm from $L = k[\sqrt a, \sqrt b]$. Square roots $\alpha, \beta$ of $a, b \in k^\times$ are
taken in an extension field $E$; $k[\sqrt{ab}] = k(\alpha\beta)$ and $L = k(\alpha\beta)(\alpha,\beta) =
k(\alpha,\beta)$. Milne leaves the degenerate cases ($a$, $b$ or $ab$ a square) to the reader; they are included. -/
@[kb "milne2020cft" "Ch. VIII, Lemma 3.8, p. 236"]
theorem lemma_3_8 (h2 : (2 : k) ≠ 0) (a b c : k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) {E : Type*} [Field E]
    [Algebra k E] (α β : E) (hα : α ^ 2 = algebraMap k E a) (hβ : β ^ 2 = algebraMap k E b) :
    (∃ (u : IntermediateField.adjoin k ({α} : Set E)) (w : IntermediateField.adjoin k ({β} : Set E)),
        Algebra.norm k u * Algebra.norm k w = c) ↔
      ∃ z : IntermediateField.adjoin (IntermediateField.adjoin k ({α * β} : Set E)) ({α, β} : Set E),
        Algebra.norm (IntermediateField.adjoin k ({α * β} : Set E)) z =
          algebraMap k (IntermediateField.adjoin k ({α * β} : Set E)) c := by
  rw [rhs_iff h2 a b c ha hb hc α β hα hβ]
  constructor
  · rintro ⟨u, v, h⟩
    obtain ⟨x, y, hxy⟩ := (exists_norm_eq_iff h2 α a ha hα _ rfl (Algebra.norm k u)).mp ⟨u, rfl⟩
    obtain ⟨z, w, hzw⟩ := (exists_norm_eq_iff h2 β b hb hβ _ rfl (Algebra.norm k v)).mp ⟨v, rfl⟩
    exact ⟨x, y, z, w, by rw [hxy, hzw]; exact h⟩
  · rintro ⟨x, y, z, w, h⟩
    obtain ⟨u, hu⟩ := (exists_norm_eq_iff h2 α a ha hα (IntermediateField.adjoin k ({α} : Set E)) rfl
      (x ^ 2 - a * y ^ 2)).mpr ⟨x, y, rfl⟩
    obtain ⟨v, hv⟩ := (exists_norm_eq_iff h2 β b hb hβ (IntermediateField.adjoin k ({β} : Set E)) rfl
      (z ^ 2 - b * w ^ 2)).mpr ⟨z, w, rfl⟩
    exact ⟨u, v, by rw [hu, hv]; exact h⟩

/-- **Proposition 3.7 (d)** (Milne, *CFT*, VIII, Proposition 3.7 (d), p. 236): over a field $k$ of characteristic
$\ne 2$, for $a, b, c \in k^\times$, the form $X^2 - bY^2 - cZ^2 + acT^2$ represents $0$ in $k$ iff $c$, as an element
of $k[\sqrt{ab}]$, is a norm from $k[\sqrt a, \sqrt b]$ (notation of `lemma_3_8`). -/
@[kb "milne2020cft" "Ch. VIII, Proposition 3.7 (d), p. 236"]
theorem prop_3_7d (h2 : (2 : k) ≠ 0) (a b c : k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) {E : Type*} [Field E]
    [Algebra k E] (α β : E) (hα : α ^ 2 = algebraMap k E a) (hβ : β ^ 2 = algebraMap k E b) :
    (∃ x y z t : k, (x, y, z, t) ≠ 0 ∧ x ^ 2 - b * y ^ 2 - c * z ^ 2 + a * c * t ^ 2 = 0) ↔
      ∃ z : IntermediateField.adjoin (IntermediateField.adjoin k ({α * β} : Set E)) ({α, β} : Set E),
        Algebra.norm (IntermediateField.adjoin k ({α * β} : Set E)) z =
          algebraMap k (IntermediateField.adjoin k ({α * β} : Set E)) c := by
  rw [rhs_iff h2 a b c ha hb hc α β hα hβ]
  constructor
  · rintro ⟨X, Y, Z, T, hne, h⟩
    have hXY : X ^ 2 - b * Y ^ 2 = c * (Z ^ 2 - a * T ^ 2) := by linear_combination h
    by_cases hm : Z ^ 2 - a * T ^ 2 = 0
    · rw [hm, mul_zero] at hXY
      by_cases hZT : (Z, T) = 0
      · have hXY' : (X, Y) ≠ 0 := fun h0 => hne (by simp_all [Prod.ext_iff])
        obtain ⟨z, w, hzw⟩ := exists_sq_sub_of_isSquare h2 hb ((prop_3_7b b).mp ⟨X, Y, hXY', hXY⟩) c
        exact ⟨1, 0, z, w, by linear_combination hzw⟩
      · obtain ⟨x, y, hxy⟩ := exists_sq_sub_of_isSquare h2 ha ((prop_3_7b a).mp ⟨Z, T, hZT, hm⟩) c
        exact ⟨x, y, 1, 0, by linear_combination hxy⟩
    · refine ⟨Z / (Z ^ 2 - a * T ^ 2), T / (Z ^ 2 - a * T ^ 2), X, Y, ?_⟩
      have key : (Z / (Z ^ 2 - a * T ^ 2)) ^ 2 - a * (T / (Z ^ 2 - a * T ^ 2)) ^ 2 =
          1 / (Z ^ 2 - a * T ^ 2) := by
        field_simp
      rw [key]
      field_simp
      linear_combination hXY
  · rintro ⟨x, y, z, w, h⟩
    have hm : x ^ 2 - a * y ^ 2 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h; exact hc h.symm
    refine ⟨(x ^ 2 - a * y ^ 2) * z, (x ^ 2 - a * y ^ 2) * w, x, y, ?_, ?_⟩
    · intro h0
      have h3 := congrArg (fun p : k × k × k × k => p.2.2.1) h0
      have h4 := congrArg (fun p : k × k × k × k => p.2.2.2) h0
      simp only [Prod.snd_zero, Prod.fst_zero] at h3 h4
      apply hm
      rw [h3, h4]; ring
    · rw [← h]; ring

end Prop37

/-! ## Local fields -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

/-- **Proposition 3.9** (Milne, *CFT*, VIII, Proposition 3.9, p. 238): a nondegenerate quadratic form in $4$ variables
over a finite extension $K$ of $\mathbb Q_p$ represents every element of $K^\times$. Here $K$ is the completion
$F_v$ of a number field at a finite prime (every finite extension of $\mathbb Q_p$ is one, by Krasner's lemma; that
identification is not formalized), with the coefficients of the form in $F_v$. From QuadFormsKB's
`PadicClass.represents_of_four_le` (diagonal forms over fields satisfying the local Hilbert symbol axioms) and
`HasseIsoNF.localHilbertField_adicCompletion`. -/
@[kb "milne2020cft" "Ch. VIII, Proposition 3.9, p. 238"]
theorem prop_3_9 (q : QuadForm (v.adicCompletion F) 4) (hq : q.Nondegenerate) (c : v.adicCompletion F)
    (hc : c ≠ 0) : q.RepresentsIn (v.adicCompletion F) c := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag q hq
  exact QuadForm.representsIn_of_isometricIn _ hiso
    (PadicClass.represents_of_four_le (HasseIsoNF.localHilbertField_adicCompletion v) ha le_rfl c)

/-- **Corollary 3.10** (Milne, *CFT*, VIII, Corollary 3.10, p. 238): every nondegenerate quadratic form in $n \ge 5$
variables over a finite extension of $\mathbb Q_p$ (here: a completion $F_v$, as in `prop_3_9`) represents $0$. -/
@[kb "milne2020cft" "Ch. VIII, Corollary 3.10, p. 238"]
theorem cor_3_10 (q : QuadForm (v.adicCompletion F) n) (hq : q.Nondegenerate) (hn : 5 ≤ n) :
    q.IsotropicIn (v.adicCompletion F) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag q hq
  obtain ⟨z, hz, hz0⟩ := LocalRankFive.isotropic_diag_five v (fun i : Fin 5 => a (Fin.castAdd m i))
    (fun i => ha _)
  have hd : (QuadForm.diag a).IsotropicIn (v.adicCompletion F) := by
    refine ⟨Fin.append z 0, fun h0 => hz (funext fun i => ?_), ?_⟩
    · have := congrFun h0 (Fin.castAdd m i)
      simpa using this
    · rw [PadicClass.evalIn_diag_self, Fin.sum_univ_add]
      rw [PadicClass.evalIn_diag_self] at hz0
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
      simpa using hz0
  exact (FieldGen.isotropicIn_iff_of_isometricIn _ hiso).mpr hd

variable (F) in
/-- **Corollary 3.11** (Milne, *CFT*, VIII, Corollary 3.11, p. 239): a nondegenerate quadratic form in $n \ge 5$
variables over a number field $F$ represents $0$ iff it represents $0$ in every real completion of $F$. -/
@[kb "milne2020cft" "Ch. VIII, Corollary 3.11, p. 239"]
theorem cor_3_11 (q : QuadForm F n) (hq : q.Nondegenerate) (hn : 5 ≤ n) :
    q.IsotropicIn F ↔ ∀ w : InfinitePlace F, w.IsReal → q.IsotropicIn w.Completion := by
  constructor
  · rintro ⟨x, hx, hx0⟩ w _
    refine ⟨fun i => algebraMap F w.Completion (x i), fun h => hx (funext fun i => ?_), ?_⟩
    · exact (map_eq_zero_iff _ (algebraMap F w.Completion).injective).mp (congrFun h i)
    · have : q.evalIn w.Completion (fun i => algebraMap F w.Completion (x i)) =
          algebraMap F w.Completion (q.evalIn F x) := by
        simp only [QuadForm.evalIn, map_sum, Algebra.algebraMap_self, RingHom.id_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp only [map_mul, map_zero]
      rw [this, hx0, map_zero]
  · intro h
    refine Lattices.isotropicIn_of_five_le q hn hq fun w => ?_
    by_cases hw : w.IsReal
    · exact h w hw
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      obtain ⟨a, ha, hP⟩ := FieldGen.exists_isometric_diag q hq
      refine (FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hP)).mpr ?_
      have : IsAlgClosed w.Completion :=
        IsAlgClosed.of_ringEquiv ℂ _ (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm
      have hn2 : 1 < n := by omega
      obtain ⟨s, hs⟩ := IsAlgClosed.isSquare
        (-(algebraMap F w.Completion (a ⟨1, hn2⟩)) / algebraMap F w.Completion (a ⟨0, by omega⟩))
      have h0 : algebraMap F w.Completion (a ⟨0, by omega⟩) ≠ 0 :=
        (map_ne_zero _).mpr (ha _)
      refine ⟨fun i => if i = ⟨0, by omega⟩ then s else if i = ⟨1, hn2⟩ then 1 else 0, ?_, ?_⟩
      · intro h1
        have := congrFun h1 ⟨1, hn2⟩
        simp at this
      · set i0 : Fin n := ⟨0, by omega⟩ with hi0
        set i1 : Fin n := ⟨1, hn2⟩ with hi1
        have hne : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
        rw [QuadForm.evalIn_diag, Finset.sum_eq_add i0 i1 hne]
        · have h' : algebraMap F w.Completion (a i0) * (s * s) =
              -algebraMap F w.Completion (a i1) := by
            rw [← hs]; field_simp
          simp only [ite_true, hne.symm, ite_false]
          linear_combination h'
        · intro c _ hc
          simp [hc.1, hc.2]
        · intro h; exact absurd (Finset.mem_univ _) h
        · intro h; exact absurd (Finset.mem_univ _) h

end Local

/-- **Remark 3.12** (Milne, *CFT*, VIII, Remark 3.12, p. 239), in the form its proof gives
($\mathrm{Nm}(H(b,c)^\times) = \mathrm{Nm}(\mathbb C^\times) = \mathbb R_{>0}$): for $b, c \in \mathbb R^\times$, if
$X^2 - bY^2 - cZ^2 + bcT^2$ (the reduced norm of the quaternion algebra $H(b,c)$) does not represent $0$ over
$\mathbb R$, then the nonzero reals it represents are exactly the positive reals. -/
@[kb "milne2020cft" "Ch. VIII, Remark 3.12, p. 239"]
theorem remark_3_12 (b c : ℝ) (hb : b ≠ 0) (hc : c ≠ 0)
    (haniso : ¬ ∃ x y z t : ℝ, (x, y, z, t) ≠ 0 ∧ x ^ 2 - b * y ^ 2 - c * z ^ 2 + b * c * t ^ 2 = 0)
    (r : ℝ) (hr : r ≠ 0) : (∃ x y z t : ℝ, x ^ 2 - b * y ^ 2 - c * z ^ 2 + b * c * t ^ 2 = r) ↔ 0 < r := by
  have hb' : b < 0 := by
    by_contra h
    have hb0 : 0 < b := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hb)
    exact haniso ⟨Real.sqrt b, 1, 0, 0, by simp, by rw [Real.sq_sqrt hb0.le]; ring⟩
  have hc' : c < 0 := by
    by_contra h
    have hc0 : 0 < c := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hc)
    exact haniso ⟨Real.sqrt c, 0, 1, 0, by simp, by rw [Real.sq_sqrt hc0.le]; ring⟩
  constructor
  · rintro ⟨x, y, z, t, h⟩
    have hbc : 0 < b * c := mul_pos_of_neg_of_neg hb' hc'
    have : 0 ≤ x ^ 2 - b * y ^ 2 - c * z ^ 2 + b * c * t ^ 2 := by
      have := sq_nonneg x; have := sq_nonneg y; have := sq_nonneg z; have := sq_nonneg t
      nlinarith
    exact lt_of_le_of_ne (h ▸ this) (Ne.symm hr)
  · intro hr0
    exact ⟨Real.sqrt r, 0, 0, 0, by simp [Real.sq_sqrt hr0.le]⟩

/-- **Remark 3.12, corrected general form** (Milne, *CFT*, VIII, Remark 3.12, p. 239). *Erratum:* Milne concludes that
a nondegenerate form in $4$ variables over $\mathbb R$ that does not represent zero represents all strictly positive
reals; this holds only after scaling the form (as in the proof of Proposition 3.9): $-(X_0^2+X_1^2+X_2^2+X_3^2)$
represents no positive real. Correct statement: such a form represents every $r > 0$ or every $r < 0$. -/
@[kb "milne2020cft" "Ch. VIII, Remark 3.12, p. 239 (corrected)"]
theorem remark_3_12_corrected (q : QuadForm ℝ 4) (hq : q.Nondegenerate) (haniso : ¬ q.IsotropicIn ℝ) :
    (∀ r : ℝ, 0 < r → q.RepresentsIn ℝ r) ∨ (∀ r : ℝ, r < 0 → q.RepresentsIn ℝ r) := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag q hq
  have hd : ¬ (QuadForm.diag a).IsotropicIn ℝ := fun h =>
    haniso ((FieldGen.isotropicIn_iff_of_isometricIn ℝ hiso).mpr h)
  have hsign : (∀ i, 0 < a i) ∨ (∀ i, a i < 0) := by
    by_contra hcon
    have hp : ∃ j, 0 < a j := by
      by_contra h
      apply hcon; right
      intro i
      exact lt_of_le_of_ne (not_lt.mp (fun h' => h ⟨i, h'⟩)) (ha i)
    have hn : ∃ i, a i < 0 := by
      by_contra h
      apply hcon; left
      intro i
      exact lt_of_le_of_ne (not_lt.mp (fun h' => h ⟨i, h'⟩)) (ha i).symm
    obtain ⟨j, hj⟩ := hp
    obtain ⟨i, hi⟩ := hn
    have hij : i ≠ j := by rintro rfl; linarith
    apply hd
    refine ⟨fun k => if k = i then Real.sqrt (a j) else if k = j then Real.sqrt (-a i) else 0, ?_, ?_⟩
    · intro h1
      have := congrFun h1 j
      simp [hij.symm, Real.sqrt_eq_zero', not_le.mpr (neg_pos.mpr hi)] at this
    · rw [PadicClass.evalIn_diag_self, Finset.sum_eq_add i j hij]
      · simp [hij.symm, Real.sq_sqrt hj.le, Real.sq_sqrt (neg_nonneg.mpr hi.le)]
        ring
      · intro c _ hc
        simp [hc.1, hc.2]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro h; exact absurd (Finset.mem_univ _) h
  have key : ∀ r : ℝ, 0 < r / a 0 → q.RepresentsIn ℝ r := by
    intro r hr
    refine QuadForm.representsIn_of_isometricIn _ hiso ⟨![Real.sqrt (r / a 0), 0, 0, 0], ?_⟩
    rw [PadicClass.evalIn_diag_self, Fin.sum_univ_four]
    have h0 := ha 0
    simp [Real.sq_sqrt hr.le]
    field_simp
  rcases hsign with h | h
  · exact Or.inl fun r hr => key r (div_pos hr (h 0))
  · exact Or.inr fun r hr => key r (div_pos_of_neg_of_neg hr (h 0))

/-- The counterexample to the uncorrected Remark 3.12: $-(X_0^2+X_1^2+X_2^2+X_3^2)$ is nondegenerate, does not
represent $0$ over $\mathbb R$ and does not represent $1$. -/
theorem remark_3_12_counterexample :
    (QuadForm.diag (fun _ : Fin 4 => (-1 : ℝ))).Nondegenerate ∧
      ¬ (QuadForm.diag (fun _ : Fin 4 => (-1 : ℝ))).IsotropicIn ℝ ∧
        ¬ (QuadForm.diag (fun _ : Fin 4 => (-1 : ℝ))).RepresentsIn ℝ 1 := by
  refine ⟨QuadForm.nondegenerate_diag (fun _ => by norm_num), ?_, ?_⟩
  · rintro ⟨x, hx, h⟩
    rw [PadicClass.evalIn_diag_self, Fin.sum_univ_four] at h
    apply hx
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
    have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
    have h3 : x 3 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  · rintro ⟨x, h⟩
    rw [PadicClass.evalIn_diag_self, Fin.sum_univ_four] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]

end NumberFieldKB.MilneCFT.Ch8
