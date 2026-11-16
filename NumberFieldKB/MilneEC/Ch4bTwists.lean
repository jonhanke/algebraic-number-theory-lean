import Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import QuadFormsKB.Citation

/-!
# Milne, Elliptic Curves, Chapter IV §7: twists of elliptic curves

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, §7, subsections "Twists of elliptic
curves" and "Curves of genus 1" (pdf pp. 146–151).  Locators give the pdf page of the text `ectext6`
(printed page = pdf page − 8).

**Conventions.** Milne assumes throughout this subsection that the characteristic of $k$ is not $2$ or $3$, and writes
elliptic curves as $E(a,b) : Y^2Z = X^3 + aXZ^2 + bZ^3$ with $\Delta = 4a^3 + 27b^2 \neq 0$ (`shortW a b`, Mathlib's
Weierstrass curve with $a_1 = a_2 = a_3 = 0$, $a_4 = a$, $a_6 = b$; it is `shortCurve` of Chapter II, by `rfl`).
Isomorphisms of elliptic curves are Mathlib's changes of variables (`WeierstrassCurve.VariableChange`); Milne's
isomorphism $(x : y : z) \mapsto (c^2x : c^3y : z)$ from $E(a,b)$ to $E(c^4a, c^6b)$ is the change of variables with
$u = c^{-1}$, $r = s = t = 0$.  The automorphism group $\operatorname{Aut}(E, O)$ is the stabilizer of $E$ in the group
of changes of variables.  For Theorem 7.15, $k$ is perfect (Milne's Galois cohomology of $k$ is for perfect fields,
Chapter IV §1), $k^{\mathrm{al}}$ is `AlgebraicClosure k` and $\Gamma = \operatorname{Gal}(k^{\mathrm{al}}/k)$ has the
Krull topology.

## Proved
* `example_7_12`: the twist $E_d$ is an elliptic curve, isomorphic to $E(a,b)$ over every extension in which $d$ is a
  square.
* `prop_7_13`: $\operatorname{Aut}(E,O)$ is $\{\pm 1\} = \mu_2(k)$, or $\mu_6(k)$ if $j = 0$, or $\mu_4(k)$ if
  $j = 1728$.
* `cor_7_16`: if $j(E_0) \neq 0, 1728$, every twist of $E_0$ is isomorphic over $k$ to some $E_d$.
* `remark_7_18`: $\operatorname{Aut}(E) = E(k) \rtimes \operatorname{Aut}(E,O)$, for any group of permutations of
  $E(k)$ containing the translations whose elements fixing $O$ are homomorphisms (Milne's argument).
* `NonabelianH1` (Remark 7.20) and `theorem_7_15` (twists of $E_0$ correspond to
  $H^1(\Gamma, \operatorname{Aut}_{k^{\mathrm{al}}}(E_0, O))$).

## Named statements
* `Remark7_14b`: in characteristic $2$ or $3$, $\operatorname{Aut}(E,O)$ has $2$ elements if $j \neq 0, 1728$ and at
  most $24$ in general (stated without proof by Milne; Silverman, *The Arithmetic of Elliptic Curves*, III.10.1 and
  Appendix A).
-/

open WeierstrassCurve

namespace NumberFieldKB.MilneEC

variable {k : Type*} [Field k]

/-- Milne's $E(a,b) : Y^2Z = X^3 + aXZ^2 + bZ^3$ (pdf p. 146), as a Weierstrass curve. -/
def shortW (a b : k) : WeierstrassCurve k := ⟨0, 0, 0, a, b⟩

/-- **The automorphism group $\operatorname{Aut}(E, O)$** (pdf p. 147): the changes of variables fixing $E$. -/
abbrev AutO (E : WeierstrassCurve k) : Subgroup (VariableChange k) := MulAction.stabilizer (VariableChange k) E

/-! ## Example 7.12: quadratic twists -/

/-- **The quadratic twist $E_d : dY^2Z = X^3 + aXZ^2 + bZ^3$** (Example 7.12, pdf p. 146), in Weierstrass form
$Y^2 = X^3 + d^2a X + d^3 b$ (substitute $X \mapsto X/d$, $Y \mapsto Y/d^2$ and multiply by $d^3$; Milne's form
$Y^2 = X^3 + (a/d^2)X + b/d^3$ is isomorphic over $k$ via $c = d$). -/
def quadTwist (a b d : k) : WeierstrassCurve k := shortW (d ^ 2 * a) (d ^ 3 * b)

/-- The points of $dY^2 = X^3 + aX + b$ correspond to those of `quadTwist a b d` by $(x, y) \mapsto (dx, d^2y)$. -/
theorem quadTwist_equation_iff (a b d x y : k) (hd : d ≠ 0) :
    d * y ^ 2 = x ^ 3 + a * x + b ↔ (quadTwist a b d).toAffine.Equation (d * x) (d ^ 2 * y) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [quadTwist, shortW, zero_mul, add_zero]
  constructor
  · intro h
    linear_combination d ^ 3 * h
  · intro h
    have h' : d ^ 3 * (d * y ^ 2) = d ^ 3 * (x ^ 3 + a * x + b) := by linear_combination h
    exact mul_left_cancel₀ (pow_ne_zero 3 hd) h'

/-- The discriminant of `shortW a b` is $-16(4a^3 + 27b^2)$. -/
lemma shortW_Δ (a b : k) : (shortW a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, shortW]
  ring

/-- The base change of `shortW a b` is `shortW` of the images. -/
lemma shortW_baseChange (K : Type*) [Field K] [Algebra k K] (a b : k) :
    (shortW a b).baseChange K = shortW (algebraMap k K a) (algebraMap k K b) := by
  ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map, shortW]

/-- **Example 7.12** (pdf pp. 146–147): for $d \in k^\times$, $E_d$ is an elliptic curve over $k$, and it becomes
isomorphic to $E(a,b)$ over every extension $K$ of $k$ in which $d$ is a square (so over $k^{\mathrm{al}}$). -/
@[kb "milne2006ec" "Ch. IV, Example 7.12, pdf p. 146"]
theorem example_7_12 [NeZero (2 : k)] (a b d : k) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hd : d ≠ 0) :
    (quadTwist a b d).IsElliptic ∧
    ∀ (K : Type*) [Field K] [Algebra k K], IsSquare (algebraMap k K d) →
      ∃ C : VariableChange K, C • (shortW a b).baseChange K = (quadTwist a b d).baseChange K := by
  have h16 : (16 : k) ≠ 0 := by
    have : (16 : k) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero 4 two_ne_zero
  refine ⟨⟨?_⟩, ?_⟩
  · rw [isUnit_iff_ne_zero]
    have : (quadTwist a b d).Δ = -16 * d ^ 6 * (4 * a ^ 3 + 27 * b ^ 2) := by
      rw [quadTwist, shortW_Δ]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 h16) (pow_ne_zero 6 hd)) hΔ
  · intro K _ _ ⟨e, he⟩
    have hd' : algebraMap k K d ≠ 0 := by simpa using hd
    have he0 : e ≠ 0 := by
      rintro rfl; apply hd'; rw [he]; simp
    refine ⟨⟨(Units.mk0 e he0)⁻¹, 0, 0, 0⟩, ?_⟩
    rw [shortW_baseChange, quadTwist, shortW_baseChange]
    ext <;> simp [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, shortW, he, map_mul, map_pow]
    all_goals (left; ring)

/-! ## Proposition 7.13: automorphisms fixing $O$ -/

/-- A change of variables sends `shortW A B` to `shortW A' B'` exactly when $r = s = t = 0$,
$A' = u^{-4}A$ and $B' = u^{-6}B$ (characteristic not $2$ or $3$). -/
lemma smul_shortW_eq_iff [NeZero (2 : k)] [NeZero (3 : k)] (C : VariableChange k) (A B A' B' : k) :
    C • shortW A B = shortW A' B' ↔
      C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ (C.u⁻¹ : kˣ) ^ 4 * A = A' ∧ (C.u⁻¹ : kˣ) ^ 6 * B = B' := by
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have h3 : (3 : k) ≠ 0 := NeZero.ne 3
  rw [WeierstrassCurve.ext_iff]
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, shortW]
  constructor
  · rintro ⟨h1, h2', h3', h4, h6⟩
    have hs : C.s = 0 := by
      simpa [h2] using h1
    have hr : C.r = 0 := by
      simpa [h3, hs] using h2'
    have ht : C.t = 0 := by
      simpa [h2] using h3'
    refine ⟨hr, hs, ht, ?_, ?_⟩
    · simpa [hr, hs, ht] using h4
    · simpa [hr, hs, ht] using h6
  · rintro ⟨hr, hs, ht, h4, h6⟩
    rw [hr, hs, ht]
    refine ⟨by simp, by simp, by simp, ?_, ?_⟩
    · simp [← h4]
    · simp [← h6]

/-- Facts about $a, b$ and $j$ for an elliptic curve `shortW a b` (characteristic not $2$ or $3$). -/
lemma shortW_j_facts [NeZero (2 : k)] [NeZero (3 : k)] (a b : k) [(shortW a b).IsElliptic] :
    (shortW a b).j = 6912 * a ^ 3 / (4 * a ^ 3 + 27 * b ^ 2) ∧ 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  have : (shortW a b).IsShortNF := ⟨rfl, rfl, rfl⟩
  have hΔ := (shortW a b).isUnit_Δ.ne_zero
  rw [shortW_Δ] at hΔ
  exact ⟨WeierstrassCurve.j_of_isShortNF _, right_ne_zero_of_mul hΔ⟩

lemma shortW_j_zero_iff [NeZero (2 : k)] [NeZero (3 : k)] (a b : k) [(shortW a b).IsElliptic] :
    (shortW a b).j = 0 ↔ a = 0 := by
  obtain ⟨hj, hne⟩ := shortW_j_facts a b
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have h3 : (3 : k) ≠ 0 := NeZero.ne 3
  have h6912 : (6912 : k) ≠ 0 := by
    have : (6912 : k) = 2 ^ 8 * 3 ^ 3 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  rw [hj, div_eq_zero_iff]
  simp [h6912, hne]

lemma shortW_j_1728_iff [NeZero (2 : k)] [NeZero (3 : k)] (a b : k) [(shortW a b).IsElliptic] :
    (shortW a b).j = 1728 ↔ b = 0 := by
  obtain ⟨hj, hne⟩ := shortW_j_facts a b
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have h3 : (3 : k) ≠ 0 := NeZero.ne 3
  have h46656 : (46656 : k) ≠ 0 := by
    have : (46656 : k) = 2 ^ 6 * 3 ^ 6 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  rw [hj, div_eq_iff hne]
  constructor
  · intro h
    have : (46656 : k) * b ^ 2 = 0 := by linear_combination -h
    have := (mul_eq_zero.1 this).resolve_left h46656
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  · rintro rfl
    ring

/-- Builds the isomorphism of Proposition 7.13 from the condition on units. -/
noncomputable def autEquiv [NeZero (2 : k)] [NeZero (3 : k)] (a b : k) (n : ℕ)
    (h : ∀ v : kˣ, (v ^ 4 * a = a ∧ v ^ 6 * b = b) ↔ v ^ n = 1) :
    AutO (shortW a b) ≃* rootsOfUnity n k := by
  have hmem : ∀ C : VariableChange k, C ∈ AutO (shortW a b) ↔
      C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ (C.u⁻¹ : kˣ) ^ n = 1 := by
    intro C
    rw [MulAction.mem_stabilizer_iff, smul_shortW_eq_iff]
    have := h C.u⁻¹
    tauto
  let f : AutO (shortW a b) →* rootsOfUnity n k :=
    { toFun := fun C => ⟨C.1.u⁻¹, by rw [mem_rootsOfUnity]; exact ((hmem C.1).1 C.2).2.2.2⟩
      map_one' := by ext; simp [VariableChange.one_def]
      map_mul' := fun C C' => by
        ext
        simp [VariableChange.mul_def, mul_comm] }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro C C' hCC
    have hu : C.1.u = C'.1.u := by
      have := congrArg (fun z : rootsOfUnity n k => ((z : kˣ)⁻¹)) hCC
      simpa [f] using this
    obtain ⟨hr, hs, ht, _⟩ := (hmem C.1).1 C.2
    obtain ⟨hr', hs', ht', _⟩ := (hmem C'.1).1 C'.2
    exact Subtype.ext (VariableChange.ext hu (hr.trans hr'.symm) (hs.trans hs'.symm) (ht.trans ht'.symm))
  · intro ζ
    have hζ : (ζ : kˣ) ^ n = 1 := (mem_rootsOfUnity n _).1 ζ.2
    refine ⟨⟨⟨(ζ : kˣ)⁻¹, 0, 0, 0⟩, (hmem _).2 ⟨rfl, rfl, rfl, by simpa using hζ⟩⟩, ?_⟩
    ext
    simp [f]

/-- **Proposition 7.13** (pdf p. 147), characteristic not $2$ or $3$: the automorphism group of $(E, O)$, for
$E = E(a,b)$, is $\{\pm 1\} = \mu_2(k)$ unless $j(E)$ is $0$ or $1728$, in which cases it is isomorphic to $\mu_6(k)$
or $\mu_4(k)$ respectively.  The isomorphisms send a change of variables to $u^{-1}$ (Milne's $c$). -/
@[kb "milne2006ec" "Ch. IV, Proposition 7.13, pdf p. 147"]
theorem prop_7_13 [NeZero (2 : k)] [NeZero (3 : k)] (a b : k) [(shortW a b).IsElliptic] :
    ((shortW a b).j ≠ 0 → (shortW a b).j ≠ 1728 → Nonempty (AutO (shortW a b) ≃* rootsOfUnity 2 k)) ∧
    ((shortW a b).j = 0 → Nonempty (AutO (shortW a b) ≃* rootsOfUnity 6 k)) ∧
    ((shortW a b).j = 1728 → Nonempty (AutO (shortW a b) ≃* rootsOfUnity 4 k)) := by
  have hu : ∀ (v : kˣ) (n : ℕ), v ^ n = 1 ↔ (v : k) ^ n = 1 := fun v n => by
    rw [Units.ext_iff]; simp
  obtain ⟨_, hne⟩ := shortW_j_facts a b
  refine ⟨?_, ?_, ?_⟩
  · intro h0 h1728
    have ha : a ≠ 0 := fun h => h0 ((shortW_j_zero_iff a b).2 h)
    have hb : b ≠ 0 := fun h => h1728 ((shortW_j_1728_iff a b).2 h)
    refine ⟨autEquiv a b 2 fun v => ?_⟩
    rw [hu]
    constructor
    · rintro ⟨h4, h6⟩
      have h4' : (v : k) ^ 4 = 1 := mul_right_cancel₀ ha (by simpa using h4)
      have h6' : (v : k) ^ 6 = 1 := mul_right_cancel₀ hb (by simpa using h6)
      linear_combination h6' - (v : k) ^ 2 * h4'
    · intro h
      have h4 : (v : k) ^ 4 = 1 := by linear_combination ((v : k) ^ 2 + 1) * h
      have h6 : (v : k) ^ 6 = 1 := by linear_combination ((v : k) ^ 4 + (v : k) ^ 2 + 1) * h
      simp [h4, h6]
  · intro h0
    have ha : a = 0 := (shortW_j_zero_iff a b).1 h0
    have hb : b ≠ 0 := by
      intro h; simp [h, ha] at hne
    refine ⟨autEquiv a b 6 fun v => ?_⟩
    rw [hu]
    constructor
    · rintro ⟨_, h6⟩
      exact mul_right_cancel₀ hb (by simpa using h6)
    · intro h
      exact ⟨by simp [ha], by simp [h]⟩
  · intro h0
    have hb : b = 0 := (shortW_j_1728_iff a b).1 h0
    have ha : a ≠ 0 := by
      intro h; simp [h, hb] at hne
    refine ⟨autEquiv a b 4 fun v => ?_⟩
    rw [hu]
    constructor
    · rintro ⟨h4, _⟩
      exact mul_right_cancel₀ ha (by simpa using h4)
    · intro h
      exact ⟨by simp [h], by simp [hb]⟩

/-- **Remark 7.14(b)** (named statement; pdf p. 147, stated without proof; Silverman, *The Arithmetic of Elliptic
Curves*, III.10.1 and Appendix A): over a field of any characteristic (in particular $2$ or $3$), the automorphism
group of an elliptic curve $(E, O)$ in Weierstrass form is $\{\pm 1\}$ (two elements) when $j(E) \neq 0, 1728$, and
has at most $24$ elements in every case. -/
@[kb "milne2006ec" "Ch. IV, Remark 7.14(b), pdf p. 147 (input)"]
structure Remark7_14b : Prop where
  card_eq_two : ∀ (k : Type) [Field k] (E : WeierstrassCurve k) [E.IsElliptic], E.j ≠ 0 → E.j ≠ 1728 →
    Nat.card (AutO E) = 2
  card_le : ∀ (k : Type) [Field k] (E : WeierstrassCurve k) [E.IsElliptic], Nat.card (AutO E) ≤ 24

/-! ## Corollary 7.16: twists when $j \neq 0, 1728$ -/

/-- **Corollary 7.16** (pdf p. 148), characteristic not $2$ or $3$: if $j(E_0) \neq 0, 1728$, the twists of
$E_0 = E(a,b)$ in Example 7.12 are all its twists: every elliptic curve $E(a',b')$ over $k$ that becomes isomorphic to
$E_0$ over some extension $K$ of $k$ is isomorphic over $k$ to $E_d$ for some $d \in k^\times$.  (Milne derives this
from Theorem 7.15; here it is proved directly from Theorem I.2.1: $d = c^2 = a'b/(ab') \in k$.) -/
@[kb "milne2006ec" "Ch. IV, Corollary 7.16, pdf p. 148"]
theorem cor_7_16 [NeZero (2 : k)] [NeZero (3 : k)] (a b a' b' : k) [(shortW a b).IsElliptic]
    (hj0 : (shortW a b).j ≠ 0) (hj1728 : (shortW a b).j ≠ 1728)
    (K : Type*) [Field K] [Algebra k K]
    (hK : ∃ C : VariableChange K, C • (shortW a b).baseChange K = (shortW a' b').baseChange K) :
    ∃ d : k, d ≠ 0 ∧ ∃ C : VariableChange k, C • quadTwist a b d = shortW a' b' := by
  have hinj := (algebraMap k K).injective
  have h2K : NeZero (2 : K) := ⟨fun h => two_ne_zero (α := k) (hinj (by rw [map_ofNat, map_zero]; exact h))⟩
  have h3K : NeZero (3 : K) :=
    ⟨fun h => (NeZero.ne (3 : k)) (hinj (by rw [map_ofNat, map_zero]; exact h))⟩
  obtain ⟨C, hC⟩ := hK
  rw [shortW_baseChange, shortW_baseChange, smul_shortW_eq_iff] at hC
  obtain ⟨-, -, -, h4, h6⟩ := hC
  have ha : a ≠ 0 := fun h => hj0 ((shortW_j_zero_iff a b).2 h)
  have hb : b ≠ 0 := fun h => hj1728 ((shortW_j_1728_iff a b).2 h)
  have haK : algebraMap k K a ≠ 0 := by simpa using ha
  have hbK : algebraMap k K b ≠ 0 := by simpa using hb
  have hv : ((C.u⁻¹ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have ha' : a' ≠ 0 := by
    intro h
    rw [h, map_zero] at h4
    exact mul_ne_zero (pow_ne_zero 4 hv) haK h4
  have hb' : b' ≠ 0 := by
    intro h
    rw [h, map_zero] at h6
    exact mul_ne_zero (pow_ne_zero 6 hv) hbK h6
  have hd : algebraMap k K (a * b' / (a' * b)) = ((C.u⁻¹ : Kˣ) : K) ^ 2 := by
    rw [map_div₀, map_mul, map_mul, ← h4, ← h6]
    field_simp
  refine ⟨a * b' / (a' * b), div_ne_zero (mul_ne_zero ha hb') (mul_ne_zero ha' hb), 1, ?_⟩
  rw [one_smul, quadTwist]
  congr 1
  · apply hinj
    rw [map_mul, map_pow, hd, ← h4]; ring
  · apply hinj
    rw [map_mul, map_pow, hd, ← h6]; ring

/-! ## Remark 7.18: $\operatorname{Aut}(E) = E(k) \rtimes \operatorname{Aut}(E, O)$ -/

/-- Milne's computation (pdf p. 149): for an automorphism α fixing O (a homomorphism),
α ∘ t_Q ∘ α⁻¹ = t_{α(Q)}. -/
@[kb "milne2006ec" "Ch. IV, Remark 7.18, pdf p. 149"]
theorem remark_7_18_conj {M : Type*} [AddCommGroup M] (α : Equiv.Perm M)
    (hα : ∀ P Q, α (P + Q) = α P + α Q) (Q : M) :
    α * Equiv.addRight Q * α⁻¹ = Equiv.addRight (α Q) := by
  ext x
  simp [Equiv.Perm.mul_apply, hα]

/-- **Remark 7.18** (pdf pp. 148–149): let $G$ be a group of permutations of $E(k)$ (Milne's $\operatorname{Aut}(E)$)
containing every translation $t_Q : P \mapsto P + Q$, such that every element fixing $O$ is a homomorphism (Milne,
pdf p. 147: automorphisms fixing $O$ map lines to lines).  Then (a) the translations form a normal subgroup
(Milne's computation $\alpha \circ t_Q \circ \alpha^{-1} = t_{\alpha(Q)}$ for $\alpha$ fixing $O$ is `remark_7_18_conj`),
(b) the only translation fixing $O$ is the identity, and (c) every element is a translation composed with an element
fixing $O$; that is, $\operatorname{Aut}(E) = E(k) \rtimes \operatorname{Aut}(E, O)$. -/
@[kb "milne2006ec" "Ch. IV, Remark 7.18, pdf p. 148"]
theorem remark_7_18 {M : Type*} [AddCommGroup M] (G : Subgroup (Equiv.Perm M))
    (htrans : ∀ Q : M, Equiv.addRight Q ∈ G)
    (hhom : ∀ g ∈ G, g 0 = 0 → ∀ P Q, g (P + Q) = g P + g Q) :
    (∀ g ∈ G, ∀ Q : M, ∃ Q' : M, g * Equiv.addRight Q * g⁻¹ = Equiv.addRight Q') ∧
    (∀ Q : M, Equiv.addRight Q 0 = 0 → Q = 0) ∧
    (∀ g ∈ G, ∃ Q : M, ∃ α ∈ G, α 0 = 0 ∧ g = Equiv.addRight Q * α) := by
  have hc : ∀ g ∈ G, ∃ Q : M, ∃ α ∈ G, α 0 = 0 ∧ g = Equiv.addRight Q * α := by
    intro g hg
    refine ⟨g 0, Equiv.addRight (-g 0) * g, G.mul_mem (htrans _) hg, ?_, ?_⟩
    · simp
    · ext x
      simp
  refine ⟨?_, ?_, hc⟩
  · intro g hg Q
    obtain ⟨R, α, hαG, hα0, rfl⟩ := hc g hg
    have hαh := hhom α hαG hα0
    refine ⟨α Q, ?_⟩
    ext x
    have h2 := Equiv.congr_fun (remark_7_18_conj α hαh Q) (x - R)
    simp only [Equiv.Perm.mul_apply, Equiv.coe_addRight, Equiv.Perm.coe_inv, mul_inv_rev] at h2 ⊢
    have e : (Equiv.addRight R).symm x = x - R := by simp [sub_eq_add_neg]
    rw [e, h2]
    abel
  · intro Q h
    simpa using h

/-! ## Remark 7.20: $H^1$ with nonabelian coefficients -/

section NonabelianH1

variable (Γ : Type*) [Group Γ] [TopologicalSpace Γ] (M : Type*) [Group M] [MulDistribMulAction Γ M]

/-- A **crossed homomorphism** $f : \Gamma \to M$ into a possibly noncommutative group (Remark 7.20, pdf p. 150):
$f(\sigma\tau) = f(\sigma) \cdot \sigma f(\tau)$; continuous for the discrete topology on $M$ (locally constant), as
for $H^1(k, \cdot)$ (pdf p. 114). -/
def IsContCrossedHom (f : Γ → M) : Prop :=
  (∀ σ τ : Γ, f (σ * τ) = f σ * σ • f τ) ∧ IsLocallyConstant f

/-- Two crossed homomorphisms are **equivalent** (Remark 7.20) if $g(\sigma) = m^{-1} \cdot f(\sigma) \cdot \sigma m$
for some $m \in M$. -/
def crossedHomSetoid : Setoid {f : Γ → M // IsContCrossedHom Γ M f} where
  r f g := ∃ m : M, ∀ σ : Γ, g.1 σ = m⁻¹ * f.1 σ * σ • m
  iseqv := by
    refine ⟨fun f => ⟨1, fun σ => by simp⟩, ?_, ?_⟩
    · rintro f g ⟨m, hm⟩
      refine ⟨m⁻¹, fun σ => ?_⟩
      rw [hm σ]
      simp [smul_inv', mul_assoc]
    · rintro f g h ⟨m, hm⟩ ⟨n, hn⟩
      refine ⟨m * n, fun σ => ?_⟩
      rw [hn σ, hm σ]
      simp [smul_mul', mul_assoc]

/-- **$H^1(G, M)$ for a noncommutative $M$** (Remark 7.20, pdf p. 150): equivalence classes of (continuous) crossed
homomorphisms, a set with distinguished element the class of $\sigma \mapsto 1$. -/
@[kb "milne2006ec" "Ch. IV, Remark 7.20, pdf p. 150"]
def NonabelianH1 : Type _ := Quotient (crossedHomSetoid Γ M)

/-- The distinguished element of `NonabelianH1`, the class of $\sigma \mapsto 1$. -/
def NonabelianH1.one : NonabelianH1 Γ M :=
  Quotient.mk _ ⟨fun _ => 1, fun σ τ => by simp, IsLocallyConstant.const 1⟩

end NonabelianH1

end NumberFieldKB.MilneEC
