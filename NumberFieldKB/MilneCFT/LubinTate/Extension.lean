import NumberFieldKB.MilneCFT.LocalCFT.Basic
import NumberFieldKB.MilneCFT.LubinTate.Padic
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# The Lubin–Tate extensions $K_{\pi,n}$ (Milne, *Class Field Theory*, Chapter I, §3)

$K$ is a nonarchimedean local field with ring of integers $A = \mathcal O_K$, residue field of $q$ elements, and $\pi$
a prime element; $\Omega = K^{\mathrm{al}}$ is a separable closure (the setting of `LocalCFT/Basic.lean`).

**Torsion points without analysis.** Milne defines $\Lambda_f$ as the maximal ideal of $K^{\mathrm{al}}$ with the
addition $F_f$ and the $A$-action $a \cdot \alpha = [a]_f(\alpha)$ (convergent power series), and $\Lambda_n$ as the
kernel of $[\pi^n]_f = f^{(n)}$. By Remark 3.1, for $f = \pi T + T^q$ the set $\Lambda_n$ is the set of **all** roots of
the polynomial $f^{(n)} = f \circ \cdots \circ f$ in $K^{\mathrm{al}}$; this is the definition used here
(`ltTorsion`). The polynomial $f^{(n)}$ is *distinguished* at $\mathfrak m$ (monic, all lower coefficients in
$\mathfrak m$: `ltPolyIter_isDistinguishedAt`), so a power series $P \in A[[T]]$ can be evaluated at a root $\alpha$
of $f^{(n)}$ algebraically: $P(\alpha) := r(\alpha)$ where $r$ is the Weierstrass remainder of $P$ modulo $f^{(n)}$
(`ltEval`; Mathlib's `PowerSeries.weierstrassMod`). This equals the convergent sum, because $P = f^{(n)} Q + r$ and
$f^{(n)}(\alpha) = 0$. The $A$-module structure of $\Lambda_n$ (Proposition 3.4) is stated through a generator:
$a \mapsto [a]_f(\lambda_0)$ induces $A/(\pi^n) \cong \Lambda_n$ (the addition is then the transported one,
$[a]_f(\lambda_0) +_{F_f} [b]_f(\lambda_0) = [a+b]_f(\lambda_0)$ by Proposition 2.15).

## Contents
* `ltPoly` ($f = \pi T + T^q$), `ltPolyIter` ($f^{(n)}$), `ltTorsion` ($\Lambda_n$, Remark 3.1), `ltField`
  ($K_{\pi,n} = K[\Lambda_n]$), `ltTower` ($K_\pi = \bigcup_n K_{\pi,n}$), `ltEval`, `ltUnitAction`.
* **Lemma 3.3**: `NumberFieldKB.MilneCFT.lemma_3_3` (`LubinTate/TorsionModule.lean`).
* **Proposition 3.4** (named statement `LubinTateTorsionModule`) and **Theorem 3.6** (named statement
  `LubinTateExtensionTheorem`), with consequences: $K_{\pi,n}/K$ is finite, Galois and abelian.
* **Lemma 3.5** in the form used here (`ltEval_galois`): a $K$-automorphism commutes with the evaluation of a power
  series at a point of $\Lambda_n$. (Milne states it for any finite Galois $L/K$, any $F \in \mathcal O_K[[X_1, \dots,
  X_n]]$ and any $\alpha_i \in \mathfrak m_L$; that form needs the topology of $L$ and is not stated here.)
* **Example 3.2** (`example_3_2`): for $K = \mathbb Q_p$, $f = (T+1)^p - 1$, the roots of $f^{(n)}$ are the
  $\zeta - 1$ with $\zeta^{p^n} = 1$.
* `IsTotallyRamifiedExt`.
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-! ## Totally ramified extensions -/

/-- **Totally ramified finite extension** of a local field (Milne, *CFT*, I, §1 and Theorem 3.6 (a)):
$\mathfrak m_K\mathcal O_L = \mathfrak P^{[L:K]}$ for a maximal ideal $\mathfrak P$ of $\mathcal O_L$ (ramification
index $e = [L:K]$, residue degree $1$). -/
@[kb "milne2020cft" "Ch. I, §3 (totally ramified extension)"]
def IsTotallyRamifiedExt (L : IntermediateField K Ω) : Prop :=
  ∃ P : Ideal (integers L), P.IsMaximal ∧
    (𝓂[K]).map (algebraMap 𝒪[K] (integers L)) = P ^ Module.finrank K L

/-! ## The polynomials $f^{(n)}$ and the torsion points $\Lambda_n$ -/

variable (K) in
/-- $q = |k|$, the number of elements of the residue field. -/
abbrev resCard : ℕ := Nat.card 𝓀[K]

/-- **$f = \pi T + T^q$** (Milne, *CFT*, I, Example 2.10 (a), Remark 3.1), an element of $\mathcal F_\pi$. -/
@[kb "milne2020cft" "Ch. I, Remark 3.1 (f = πT + T^q)"]
def ltPoly (π : 𝒪[K]) : 𝒪[K][X] := C π * X + X ^ resCard K

/-- **$f^{(n)} = f \circ \cdots \circ f$** ($n$ factors; $f^{(0)} = T$) (Milne, *CFT*, I, Remark 3.1); it is
$[\pi^n]_f$. -/
@[kb "milne2020cft" "Ch. I, Remark 3.1 (f^(n))"]
def ltPolyIter (π : 𝒪[K]) (n : ℕ) : 𝒪[K][X] := (fun p => (ltPoly π).comp p)^[n] X

theorem ltPolyIter_succ (π : 𝒪[K]) (n : ℕ) : ltPolyIter π (n + 1) = (ltPoly π).comp (ltPolyIter π n) := by
  rw [ltPolyIter, ltPolyIter, Function.iterate_succ_apply']

/-- The power series of `ltPoly` is $\pi T + T^q \in \mathcal F_\pi$. -/
theorem ltPoly_coe (π : 𝒪[K]) :
    ((ltPoly π : 𝒪[K][X]) : PowerSeries 𝒪[K]) = PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ resCard K := by
  simp [ltPoly]

theorem ltPoly_mem {π : 𝒪[K]} (hπ : Irreducible π) :
    ((ltPoly π : 𝒪[K][X]) : PowerSeries 𝒪[K]) ∈ lubinTateSeries π (resCard K) := by
  rw [ltPoly_coe]
  exact C_mul_X_add_X_pow_mem π (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt

theorem ltPolyIter_aux {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    (ltPolyIter π n).Monic ∧ (ltPolyIter π n).natDegree = resCard K ^ n ∧
      (ltPolyIter π n).map (Ideal.Quotient.mk 𝓂[K]) = X ^ (resCard K ^ n) := by
  have hq : 2 ≤ resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt
  have hπm : Ideal.Quotient.mk 𝓂[K] π = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
  induction n with
  | zero => simp [ltPolyIter]
  | succ n ih =>
    obtain ⟨hm, hd, hmap⟩ := ih
    have h : ltPolyIter π (n + 1) = C π * ltPolyIter π n + ltPolyIter π n ^ resCard K := by
      rw [ltPolyIter_succ]; simp [ltPoly]
    generalize ltPolyIter π n = g at *
    have hpm : (g ^ resCard K).Monic := hm.pow _
    have hpd : (g ^ resCard K).natDegree = resCard K ^ (n + 1) := by
      rw [hm.natDegree_pow, hd, pow_succ, mul_comm]
    have hlt : (C π * g).degree < (g ^ resCard K).degree := by
      rw [degree_eq_natDegree hpm.ne_zero, hpd]
      refine lt_of_le_of_lt (degree_le_natDegree.trans (WithBot.coe_le_coe.2 (natDegree_C_mul_le _ _))) ?_
      rw [hd]
      exact WithBot.coe_lt_coe.2 (show resCard K ^ n < resCard K ^ (n + 1) from
        Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self n))
    refine ⟨?_, ?_, ?_⟩
    · rw [h]; exact hpm.add_of_right hlt
    · rw [h, natDegree_add_eq_right_of_degree_lt hlt, hpd]
    · rw [h]; simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, hmap, hπm, ← pow_mul, pow_succ]

/-- $f^{(n)}$ is distinguished at $\mathfrak m$: monic of degree $q^n$, all other coefficients in $\mathfrak m$
(Milne, *CFT*, I, Remark 3.1: $f^{(n)}(T) = \pi^n T + \cdots + T^{q^n}$). -/
theorem ltPolyIter_isDistinguishedAt {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    (ltPolyIter π n).IsDistinguishedAt 𝓂[K] := by
  obtain ⟨hm, hd, hmap⟩ := ltPolyIter_aux hπ n
  refine ⟨⟨fun {i} hi => ?_⟩, hm⟩
  have := congrArg (fun p => p.coeff i) hmap
  simp only [coeff_map, coeff_X_pow] at this
  rw [← Ideal.Quotient.eq_zero_iff_mem, this]
  simp [show i ≠ resCard K ^ n by omega]

theorem ltPolyIter_natDegree {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    (ltPolyIter π n).natDegree = resCard K ^ n := (ltPolyIter_aux hπ n).2.1

variable (Ω) in
/-- **$\Lambda_n$** (Milne, *CFT*, I, §3 and Remark 3.1): the roots of $f^{(n)}$ in $K^{\mathrm{al}}$ (for
$f = \pi T + T^q$, these all have absolute value $< 1$ and are exactly the $[\pi^n]_f$-torsion of $\Lambda_f$). -/
@[kb "milne2020cft" "Ch. I, §3 (Λ_n) and Remark 3.1"]
def ltTorsion (π : 𝒪[K]) (n : ℕ) : Set Ω :=
  ((ltPolyIter π n).map (algebraMap 𝒪[K] K)).rootSet Ω

variable (Ω) in
/-- **$K_{\pi,n} = K[\Lambda_n]$** (Milne, *CFT*, I, Theorem 3.6): the subfield of $K^{\mathrm{al}}$ generated by
$\Lambda_n$. -/
@[kb "milne2020cft" "Ch. I, Theorem 3.6 (K_{π,n})"]
def ltField (π : 𝒪[K]) (n : ℕ) : IntermediateField K Ω :=
  IntermediateField.adjoin K (ltTorsion Ω π n)

variable (Ω) in
/-- **$K_\pi = \bigcup_n K_{\pi,n}$** (Milne, *CFT*, I, §3, Summary 3.7). -/
@[kb "milne2020cft" "Ch. I, §3 (K_π, Summary 3.7)"]
def ltTower (π : 𝒪[K]) : IntermediateField K Ω := ⨆ n, ltField Ω π n

theorem mem_ltField {π : 𝒪[K]} {n : ℕ} {α : Ω} (hα : α ∈ ltTorsion Ω π n) : α ∈ ltField Ω π n :=
  IntermediateField.subset_adjoin K _ hα

instance ltField_finiteDimensional (π : 𝒪[K]) (n : ℕ) : FiniteDimensional K (ltField Ω π n) := by
  have : Algebra.IsAlgebraic K Ω := Algebra.IsSeparable.isAlgebraic K Ω
  have hfin : (ltTorsion Ω π n).Finite := by
    unfold ltTorsion
    exact Polynomial.rootSet_finite _ _
  have : Finite (ltTorsion Ω π n) := hfin.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

/-! ## Evaluating power series at the points of $\Lambda_n$ -/

/-- $\mathcal O_K$ is $\mathfrak m$-adically complete (Mathlib's instance, stated there for a uniform structure on
$K$; the statement does not depend on it). -/
instance isAdicComplete_integers : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  infer_instance

/-- **$P(\alpha)$ for $\alpha \in \Lambda_n$**: the Weierstrass remainder of $P$ modulo $f^{(n)}$, evaluated at
$\alpha$ (see the module docstring; it is the value of the convergent series $\sum_i c_i\alpha^i$). -/
def ltEval (π : 𝒪[K]) (n : ℕ) (P : PowerSeries 𝒪[K]) (α : Ω) : Ω :=
  aeval α ((P %ʷ ((ltPolyIter π n : 𝒪[K][X]) : PowerSeries 𝒪[K])).map (algebraMap 𝒪[K] K))

/-- The action $\alpha \mapsto [a]_f(\alpha)$ of $a \in A$ on $\Lambda_n$ (Milne, *CFT*, I, §3), with $[a]_f$ the
endomorphism of Corollary 2.17 (`lubinTateEnd`). -/
@[kb "milne2020cft" "Ch. I, §3 (the A-action a·α = [a]_f(α) on Λ_n)"]
def ltAct {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) (a : 𝒪[K]) (α : Ω) : Ω :=
  ltEval π n (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) (ltPoly_mem hπ) a).toPowerSeries α

/-- **Lemma 3.5, in the form used here** (Milne, *CFT*, I, Lemma 3.5): a $K$-automorphism $\sigma$ of $\Omega$
commutes with the evaluation of a power series with coefficients in $\mathcal O_K$ at a point of $\Lambda_n$. -/
@[kb "milne2020cft" "Ch. I, Lemma 3.5 (evaluation at points of Λ_n)"]
theorem ltEval_galois (π : 𝒪[K]) (n : ℕ) (P : PowerSeries 𝒪[K]) (σ : Ω ≃ₐ[K] Ω) (α : Ω) :
    σ (ltEval π n P α) = ltEval π n P (σ α) := by
  unfold ltEval
  rw [Polynomial.aeval_algHom_apply]

/-! ## Proposition 3.4 and Theorem 3.6 (named statements) -/

variable (K Ω) in
/-- **Proposition 3.4** (named statement; Milne, *CFT*, I, Proposition 3.4): $\Lambda_n \cong A/(\pi^n)$ as an
$A$-module. In the form here: there is $\lambda_0 \in \Lambda_n$ such that $a \mapsto [a]_f(\lambda_0)$ induces a
bijection $A/(\pi^n) \to \Lambda_n$, i.e. $[a]_f(\lambda_0) = [b]_f(\lambda_0)$ iff $a \equiv b \pmod{\pi^n}$, and
every point of $\Lambda_n$ is some $[a]_f(\lambda_0)$. (Milne's proof: Lemma 3.3 for $M = \Lambda_f$, with the
Newton polygon of $f(T) - \alpha$ giving surjectivity of $\pi$.) Consequently
$\mathrm{End}_A(\Lambda_n) = A/(\pi^n)$ and $\mathrm{Aut}_A(\Lambda_n) = (A/(\pi^n))^\times$. -/
@[kb "milne2020cft" "Ch. I, Proposition 3.4 (input)"]
structure LubinTateTorsionModule : Prop where
  cyclic : ∀ {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ), ∃ x₀ ∈ ltTorsion Ω π n,
    (∀ a b : 𝒪[K], ltAct hπ n a x₀ = ltAct hπ n b x₀ ↔ a - b ∈ Ideal.span {π ^ n}) ∧
    ∀ α ∈ ltTorsion Ω π n, ∃ a : 𝒪[K], α = ltAct hπ n a x₀

variable (K Ω) in
/-- **Theorem 3.6** (named statement; Milne, *CFT*, I, Theorem 3.6): for every $n \ge 1$,
(a) $K_{\pi,n}/K$ is totally ramified of degree $(q-1)q^{n-1}$;
(b) the action of $A$ on $\Lambda_n$ defines an isomorphism $(A/\mathfrak m^n)^\times \to \mathrm{Gal}(K_{\pi,n}/K)$:
the class of a unit $u$ acts by $\lambda \mapsto [u]_f(\lambda)$ on $\Lambda_n$; in particular $K_{\pi,n}/K$ is abelian
(`ltField_isAbelianGalois`);
(c) $\pi$ is a norm from $K_{\pi,n}$. -/
@[kb "milne2020cft" "Ch. I, Theorem 3.6 (input)"]
structure LubinTateExtensionTheorem : Prop where
  totallyRamified : ∀ {π : 𝒪[K]}, Irreducible π → ∀ n : ℕ, 1 ≤ n → IsTotallyRamifiedExt (ltField Ω π n)
  finrank_eq : ∀ {π : 𝒪[K]}, Irreducible π → ∀ n : ℕ, 1 ≤ n →
    Module.finrank K (ltField Ω π n) = (resCard K - 1) * resCard K ^ (n - 1)
  galois : ∀ {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ), 1 ≤ n →
    ∃ χ : (𝒪[K] ⧸ 𝓂[K] ^ n)ˣ ≃* Gal(ltField Ω π n/K), ∀ (u : 𝒪[K]ˣ) (α : Ω) (hα : α ∈ ltTorsion Ω π n),
      ((χ (Units.map (Ideal.Quotient.mk (𝓂[K] ^ n)).toMonoidHom u) ⟨α, mem_ltField hα⟩ : ltField Ω π n) : Ω) =
        ltAct hπ n u α
  isNorm : ∀ {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ), primeUnit hπ ∈ normGroup (ltField Ω π n)

/-- The number of units of $A/\mathfrak m^n$ ($n \ge 1$) is $(q-1)q^{n-1}$. -/
theorem card_units_quot_maximalIdeal_pow (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (𝒪[K] ⧸ 𝓂[K] ^ n)ˣ = (resCard K - 1) * resCard K ^ (n - 1) := by
  have hq : 2 ≤ resCard K := by
    have : Nontrivial 𝓀[K] := inferInstance
    have : Finite 𝓀[K] := inferInstance
    have h1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
    exact h1
  have hm : 𝓂[K] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hres : Nat.card (𝒪[K] ⧸ 𝓂[K]) = resCard K := rfl
  have hcard : Nat.card (𝒪[K] ⧸ 𝓂[K] ^ n) = resCard K ^ n := by
    rw [← Submodule.cardQuot_apply, cardQuot_pow_of_prime hm, Submodule.cardQuot_apply, hres]
  have hfin : Finite (𝒪[K] ⧸ 𝓂[K] ^ n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  set J : Submodule 𝒪[K] (𝒪[K] ⧸ 𝓂[K] ^ n) := Submodule.map (𝓂[K] ^ n).mkQ 𝓂[K] with hJ
  have hJcard : Nat.card J * resCard K = resCard K ^ n := by
    rw [← hcard, ← hres]
    exact Submodule.card_quotient_mul_card_quotient _ _ (Ideal.pow_le_self (by omega))
  have hJc : Nat.card J = resCard K ^ (n - 1) := by
    have h' : Nat.card J * resCard K = resCard K ^ (n - 1) * resCard K := by
      rw [hJcard, ← pow_succ, Nat.sub_add_cancel hn]
    exact Nat.eq_of_mul_eq_mul_right (by omega) h'
  have hunit : ∀ x : 𝒪[K] ⧸ 𝓂[K] ^ n, IsUnit x ↔ x ∉ J := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hmem : Ideal.Quotient.mk (𝓂[K] ^ n) a ∈ J ↔ a ∈ 𝓂[K] := by
      rw [hJ, Submodule.mem_map]
      constructor
      · rintro ⟨b, hb, hba⟩
        have : a - b ∈ 𝓂[K] ^ n := by
          rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
          exact hba.symm
        have h2 : a - b ∈ 𝓂[K] := Ideal.pow_le_self (by omega) this
        simpa using Ideal.add_mem _ h2 hb
      · intro ha
        exact ⟨a, ha, rfl⟩
    rw [hmem]
    constructor
    · intro hu ha
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑hu.unit⁻¹ : 𝒪[K] ⧸ 𝓂[K] ^ n)
      have h1 : Ideal.Quotient.mk (𝓂[K] ^ n) (a * b) = Ideal.Quotient.mk (𝓂[K] ^ n) 1 := by
        rw [map_mul, hb, map_one]
        exact hu.mul_val_inv
      have h2 : a * b - 1 ∈ 𝓂[K] ^ n := Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _ |>.1 h1
      have h3 : a * b - 1 ∈ 𝓂[K] := Ideal.pow_le_self (by omega) h2
      have h4 : (1 : 𝒪[K]) ∈ 𝓂[K] := by
        simpa using Ideal.sub_mem _ (Ideal.mul_mem_right b _ ha) h3
      exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h4
    · intro ha
      exact ((IsLocalRing.notMem_maximalIdeal.1 ha).map _)
  have hequiv : (𝒪[K] ⧸ 𝓂[K] ^ n)ˣ ≃ {x : 𝒪[K] ⧸ 𝓂[K] ^ n // x ∉ J} :=
    { toFun := fun u => ⟨u, (hunit _).1 u.isUnit⟩
      invFun := fun x => ((hunit x.1).2 x.2).unit
      left_inv := fun u => by ext; rfl
      right_inv := fun x => by ext; rfl }
  have := Set.ncard_add_ncard_compl (J : Set (𝒪[K] ⧸ 𝓂[K] ^ n))
  rw [Nat.card_congr hequiv]
  have hc : Nat.card {x : 𝒪[K] ⧸ 𝓂[K] ^ n // x ∉ J} = Set.ncard (J : Set (𝒪[K] ⧸ 𝓂[K] ^ n))ᶜ := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [hc]
  have hj : Set.ncard (J : Set (𝒪[K] ⧸ 𝓂[K] ^ n)) = Nat.card J := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [hj, hJc, hcard] at this
  have hpow : resCard K ^ n = resCard K ^ (n - 1) * resCard K := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hpow] at this
  rw [Nat.sub_one_mul]
  have hm' : resCard K ^ (n - 1) * resCard K = resCard K * resCard K ^ (n - 1) := mul_comm _ _
  omega

/-- From Theorem 3.6: $K_{\pi,n}/K$ is Galois ($|\mathrm{Gal}| = |(A/\mathfrak m^n)^\times| = (q-1)q^{n-1} =
[K_{\pi,n}:K]$). -/
theorem ltField_isGalois (h : LubinTateExtensionTheorem K Ω) {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ}
    (hn : 1 ≤ n) : IsGalois K (ltField Ω π n) := by
  obtain ⟨χ, -⟩ := h.galois hπ n hn
  apply IsGalois.of_card_aut_eq_finrank
  rw [← Nat.card_congr χ.toEquiv, card_units_quot_maximalIdeal_pow n hn, h.finrank_eq hπ n hn]

/-- From Theorem 3.6 (b): $K_{\pi,n}/K$ is abelian. -/
@[kb "milne2020cft" "Ch. I, Theorem 3.6 (b) (K_{π,n}/K is abelian)"]
theorem ltField_isAbelianGalois (h : LubinTateExtensionTheorem K Ω) {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ}
    (hn : 1 ≤ n) : IsAbelianGalois K (ltField Ω π n) := by
  have hG := ltField_isGalois h hπ hn
  obtain ⟨χ, -⟩ := h.galois hπ n hn
  have hc : IsMulCommutative Gal(ltField Ω π n/K) :=
    ⟨⟨fun a b => by
      apply χ.symm.injective
      rw [map_mul, map_mul]
      exact mul_comm (χ.symm a) (χ.symm b)⟩⟩
  exact { hG, hc with }

/-- $K_{\pi,n}$ as a finite abelian extension (given Theorem 3.6). -/
def ltFieldExt (h : LubinTateExtensionTheorem K Ω) {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    FiniteAbelianExt K Ω where
  toField := ltField Ω π n
  isAbelianGalois := ltField_isAbelianGalois h hπ hn

/-! ## Example 3.2 -/

/-- **Example 3.2** (Milne, *CFT*, I): for $K = \mathbb Q_p$, $\pi = p$ and $f = (T+1)^p - 1 \in \mathcal F_p$, the
$n$-fold composite is $f^{(n)} = (T+1)^{p^n} - 1$, so its roots in any field $\Omega \supseteq \mathbb Q_p$ are the
$\zeta - 1$ with $\zeta^{p^n} = 1$; $+_{F_f}$ corresponds to multiplication of roots of unity
(`lubinTateFormalGroup_padicInt`). -/
@[kb "milne2020cft" "Ch. I, Example 3.2"]
theorem example_3_2 (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ_[p] Ω] (n : ℕ) :
    (((fun g : ℚ_[p][X] => ((X + 1) ^ p - 1 : ℚ_[p][X]).comp g)^[n] X).rootSet Ω) =
      {α : Ω | (α + 1) ^ (p ^ n) = 1} := by
  have hiter : ∀ m : ℕ, (fun g : ℚ_[p][X] => ((X + 1) ^ p - 1 : ℚ_[p][X]).comp g)^[m] X =
      (X + 1) ^ (p ^ m) - 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [sub_comp, pow_comp, add_comp, ← pow_mul, pow_succ]
  rw [hiter n]
  have hne : ((X + 1) ^ (p ^ n) - 1 : ℚ_[p][X]) ≠ 0 := by
    intro h
    have h1 : ((X + 1) ^ (p ^ n) : ℚ_[p][X]) = 1 := sub_eq_zero.1 h
    have h2 := congrArg Polynomial.natDegree h1
    have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
    simp [natDegree_pow] at h2
    have := (Fact.out : p.Prime).pos
    omega
  ext α
  rw [Polynomial.mem_rootSet]
  simp [hne, sub_eq_zero]

end NumberFieldKB.MilneCFT.LocalCFT
