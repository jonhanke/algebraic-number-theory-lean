import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter II §3: algebraic groups of dimension 1

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8).

The additive group $\mathbb G_a(k) = k$ and the multiplicative group $\mathbb G_m(k) = k^\times$ are Mathlib's `k`
and `kˣ`. The twisted multiplicative group $\mathbb G_m[a]$ (p. 63) is defined here through Mathlib's quadratic
algebra $L = k[\alpha]$, $\alpha^2 = a$ (`QuadraticAlgebra k a 0`, a field when $a$ is not a square): its group of
$k$-points is the kernel of the norm $L^\times \to k^\times$, which is Milne's description
$\mathbb G_m[a](k) = \{\gamma \in L \mid \operatorname{Nm}_{L/k}\gamma = 1\}$. `mem_twistedMulGroup_iff` and
`twistedMulGroup_mul` show it is the affine conic $X^2 - aY^2 = 1$ with Milne's group law
$(x, y)\cdot(x', y') = (xx' + ayy', xy' + x'y)$.

Contents: Definition of $\mathbb G_m[a]$ (D055), the isomorphisms $\mathbb G_m[a] \cong \mathbb G_m[ac^2]$ and,
for $a = \alpha^2$, $\mathbb G_m[a] \cong \mathbb G_m$ (p. 63), Example 3.1 (point counts over $\mathbb F_q$), and
the rational parametrization of the conic behind the count.
-/

namespace NumberFieldKB.MilneEC.II

variable {k : Type*} [Field k]

/-- **The twisted multiplicative group** $\mathbb G_m[a]$ (Milne, Ch. II §3, p. 63), as its group of $k$-points:
the elements of norm $1$ in $k[\alpha]$, $\alpha^2 = a$. -/
@[kb "milne2006ec" "Ch. II, §3, twisted multiplicative groups (definition in prose), pdf p. 63"]
def twistedMulGroup (a : k) : Subgroup (QuadraticAlgebra k a 0)ˣ :=
  (QuadraticAlgebra.norm.comp (Units.coeHom (QuadraticAlgebra k a 0))).ker

/-- Points of $\mathbb G_m[a]$ are the points $(x, y)$ of the conic $X^2 - aY^2 = 1$. -/
@[kb "milne2006ec" "Ch. II, §3, twisted multiplicative groups (definition in prose), pdf p. 63"]
theorem mem_twistedMulGroup_iff {a : k} (z : (QuadraticAlgebra k a 0)ˣ) :
    z ∈ twistedMulGroup a ↔ (z : QuadraticAlgebra k a 0).re ^ 2 - a * (z : QuadraticAlgebra k a 0).im ^ 2 = 1 := by
  simp only [twistedMulGroup, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.coeHom_apply,
    QuadraticAlgebra.norm_def]
  constructor <;> intro h <;> linear_combination h

/-- The coordinate $x$ of a point $(x, y)$ of $\mathbb G_m[a]$ (the component $x$ of $x + \alpha y$). -/
def gmX {a : k} (z : twistedMulGroup a) : k :=
  ((z : (QuadraticAlgebra k a 0)ˣ) : QuadraticAlgebra k a 0).re

/-- The coordinate $y$ of a point $(x, y)$ of $\mathbb G_m[a]$. -/
def gmY {a : k} (z : twistedMulGroup a) : k :=
  ((z : (QuadraticAlgebra k a 0)ˣ) : QuadraticAlgebra k a 0).im

/-- The point $(x, y)$ of $\mathbb G_m[a]$ built from a solution of $x^2 - ay^2 = 1$; its inverse is $(x, -y)$. -/
def gmMk (a : k) (x y : k) (h : x ^ 2 - a * y ^ 2 = 1) : twistedMulGroup a :=
  ⟨⟨⟨x, y⟩, ⟨x, -y⟩, by
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;>
      first | linear_combination h | ring, by
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;>
      first | linear_combination h | ring⟩, by
    rw [mem_twistedMulGroup_iff]; exact h⟩

@[simp] theorem gmX_mk (a x y : k) (h : x ^ 2 - a * y ^ 2 = 1) : gmX (gmMk a x y h) = x := rfl

@[simp] theorem gmY_mk (a x y : k) (h : x ^ 2 - a * y ^ 2 = 1) : gmY (gmMk a x y h) = y := rfl

/-- Milne's group law on $\mathbb G_m[a]$: $(x, y)\cdot(x', y') = (xx' + ayy', xy' + x'y)$. -/
@[kb "milne2006ec" "Ch. II, §3, twisted multiplicative groups (definition in prose), pdf p. 63"]
theorem twistedMulGroup_mul {a : k} (z w : twistedMulGroup a) :
    gmX (z * w) = gmX z * gmX w + a * gmY z * gmY w ∧ gmY (z * w) = gmX z * gmY w + gmX w * gmY z := by
  constructor
  · simp [gmX, gmY]
  · simp [gmX, gmY]; try ring

/-- A point of $\mathbb G_m[a]$ lies on the conic $X^2 - aY^2 = 1$. -/
theorem twistedMulGroup_conic {a : k} (z : twistedMulGroup a) : gmX z ^ 2 - a * gmY z ^ 2 = 1 := by
  have := (mem_twistedMulGroup_iff (a := a) (z : (QuadraticAlgebra k a 0)ˣ)).1 z.2
  exact this

/-- A point of $\mathbb G_m[a]$ is determined by its coordinates. -/
theorem twistedMulGroup_ext {a : k} {z w : twistedMulGroup a} (hx : gmX z = gmX w) (hy : gmY z = gmY w) : z = w := by
  apply Subtype.ext
  apply Units.ext
  exact QuadraticAlgebra.ext hx hy

/-- The points of $\mathbb G_m[a]$ as a set of pairs: the conic $X^2 - aY^2 = 1$. -/
theorem twistedMulGroup_equiv_conic (a : k) :
    Nonempty (twistedMulGroup a ≃ {p : k × k // p.1 ^ 2 - a * p.2 ^ 2 = 1}) :=
  ⟨{ toFun := fun z => ⟨(gmX z, gmY z), twistedMulGroup_conic z⟩
     invFun := fun p => gmMk a p.1.1 p.1.2 p.2
     left_inv := fun z => twistedMulGroup_ext (by simp) (by simp)
     right_inv := fun p => by ext <;> simp }⟩

/-- p. 63: an invertible change of variables transforms $\mathbb G_m[a]$ into $\mathbb G_m[ac^2]$, $c \in k^\times$. -/
@[kb "milne2006ec" "Ch. II, §3, p. 63: G_m[a] is isomorphic to G_m[ac^2]"]
theorem twistedMulGroup_iso_mul_sq (a : k) {c : k} (hc : c ≠ 0) :
    Nonempty (twistedMulGroup a ≃* twistedMulGroup (a * c ^ 2)) := by
  have h1 : ∀ z : twistedMulGroup a, gmX z ^ 2 - a * c ^ 2 * (gmY z / c) ^ 2 = 1 := fun z => by
    have := twistedMulGroup_conic z
    field_simp
    linear_combination this
  have h2 : ∀ w : twistedMulGroup (a * c ^ 2), gmX w ^ 2 - a * (gmY w * c) ^ 2 = 1 := fun w => by
    have := twistedMulGroup_conic w
    linear_combination this
  refine ⟨{ toFun := fun z => gmMk _ (gmX z) (gmY z / c) (h1 z)
            invFun := fun w => gmMk _ (gmX w) (gmY w * c) (h2 w)
            left_inv := fun z => twistedMulGroup_ext (by simp) (by simp [hc])
            right_inv := fun w => twistedMulGroup_ext (by simp) (by simp [hc])
            map_mul' := fun z w => ?_ }⟩
  have hz := twistedMulGroup_mul z w
  apply twistedMulGroup_ext
  · conv_rhs => rw [(twistedMulGroup_mul _ _).1]
    simp only [gmX_mk, gmY_mk, hz.1]; field_simp
  · conv_rhs => rw [(twistedMulGroup_mul _ _).2]
    simp only [gmX_mk, gmY_mk, hz.2]; field_simp

/-- p. 63: when $a = \alpha^2$ with $\alpha \neq 0$ and the characteristic is not $2$, the change of variables
$X' = X + \alpha Y$, $Y' = X - \alpha Y$ identifies $\mathbb G_m[a]$ with $\mathbb G_m$; the isomorphism is
$(x, y) \mapsto x + \alpha y$. -/
@[kb "milne2006ec" "Ch. II, §3, p. 63: G_m[a] is isomorphic to G_m when a is a square"]
theorem twistedMulGroup_iso_units_of_sq [NeZero (2 : k)] {a α : k} (hα : α ≠ 0) (ha : a = α ^ 2) :
    ∃ e : twistedMulGroup a ≃* kˣ, ∀ z : twistedMulGroup a,
      (e z : k) = gmX z + α * gmY z := by
  subst ha
  have h2 : (2 : k) ≠ 0 := NeZero.ne 2
  have hz : ∀ z : twistedMulGroup (α ^ 2), (gmX z + α * gmY z) * (gmX z - α * gmY z) = 1 := fun z => by
    linear_combination twistedMulGroup_conic z
  have hne : ∀ z : twistedMulGroup (α ^ 2), gmX z + α * gmY z ≠ 0 := fun z h => by
    have := hz z; rw [h, zero_mul] at this; exact zero_ne_one this
  have hc : ∀ t : kˣ, ((t + (t⁻¹ : kˣ) : k) / 2) ^ 2 - α ^ 2 * (((t : k) - (t⁻¹ : kˣ)) / (2 * α)) ^ 2 = 1 := by
    intro t
    have := t.mul_inv
    field_simp
    linear_combination (4 : k) * this
  refine ⟨{ toFun := fun z => ⟨gmX z + α * gmY z, gmX z - α * gmY z, hz z, by rw [mul_comm]; exact hz z⟩
            invFun := fun t => gmMk _ (((t : k) + (t⁻¹ : kˣ)) / 2) (((t : k) - (t⁻¹ : kˣ)) / (2 * α)) (hc t)
            left_inv := fun z => ?_
            right_inv := fun t => ?_
            map_mul' := fun z w => ?_ }, fun z => rfl⟩
  · have hi : ((gmX z + α * gmY z)⁻¹ : k) = gmX z - α * gmY z := inv_eq_of_mul_eq_one_right (hz z)
    apply twistedMulGroup_ext
    · simp only [gmX_mk, Units.val_inv_eq_inv_val]
      rw [hi]; field_simp; ring
    · simp only [gmY_mk, Units.val_inv_eq_inv_val]
      rw [hi]; field_simp; ring
  · apply Units.ext
    simp only [gmX_mk, gmY_mk]
    field_simp
    ring
  · apply Units.ext
    have := twistedMulGroup_mul z w
    simp only [Units.val_mul, this.1, this.2]
    ring

/-- For $a$ not a square, $am^2 - 1 \neq 0$. -/
theorem sq_mul_sub_one_ne_zero {a : k} (ha : ¬IsSquare a) (m : k) : a * m ^ 2 - 1 ≠ 0 := by
  intro h
  have hm : m ≠ 0 := by rintro rfl; simp at h
  exact ha ⟨m⁻¹, by field_simp; linear_combination h⟩

/-- The point of $\mathbb G_m[a]$ with parameter $m$ in the rational parametrization from $(1, 0)$. -/
def gmParam {a : k} (ha : ¬IsSquare a) (m : k) : twistedMulGroup a :=
  gmMk a ((a * m ^ 2 + 1) / (a * m ^ 2 - 1)) (2 * m / (a * m ^ 2 - 1)) (by
    have := sq_mul_sub_one_ne_zero ha m
    field_simp
    ring)

/-- The map $k \sqcup \{\ast\} \to \mathbb G_m[a]$ of the rational parametrization. -/
def gmParamOption {a : k} (ha : ¬IsSquare a) : Option k → twistedMulGroup a
  | none => gmMk a 1 0 (by simp)
  | some m => gmParam ha m

/-- The rational parametrization of the conic $X^2 - aY^2 = 1$ from its point $(1, 0)$, for $a$ not a square and
characteristic $\neq 2$: $m \mapsto \big((am^2 + 1)/(am^2 - 1), 2m/(am^2 - 1)\big)$, together with $(1, 0)$, is a
bijection $k \sqcup \{\ast\} \to \mathbb G_m[a]$. (In characteristic $2$ the conic is $(X + 1)^2 = aY^2$,
whose only point is $(1, 0)$ when $a$ is not a square.) -/
theorem twistedMulGroup_equiv_option [NeZero (2 : k)] {a : k} (ha : ¬IsSquare a) :
    Nonempty (twistedMulGroup a ≃ Option k) := by
  have h2 : (2 : k) ≠ 0 := NeZero.ne 2
  have key : ∀ m : k, (a * m ^ 2 + 1) / (a * m ^ 2 - 1) = 1 + 2 / (a * m ^ 2 - 1) := fun m => by
    have := sq_mul_sub_one_ne_zero ha m
    field_simp
    ring
  have hbij : Function.Bijective (gmParamOption ha) := by
    constructor
    · rintro (_ | m) (_ | m') h
      · rfl
      · have hx := congrArg gmX h
        simp only [gmParamOption, gmParam, gmX_mk, key] at hx
        have := sq_mul_sub_one_ne_zero ha m'
        exfalso
        have : 2 / (a * m' ^ 2 - 1) = 0 := by linear_combination -hx
        simp [h2, sq_mul_sub_one_ne_zero ha m'] at this
      · have hx := congrArg gmX h
        simp only [gmParamOption, gmParam, gmX_mk, key] at hx
        exfalso
        have : 2 / (a * m ^ 2 - 1) = 0 := by linear_combination hx
        simp [h2, sq_mul_sub_one_ne_zero ha m] at this
      · have hx := congrArg gmX h
        have hy := congrArg gmY h
        simp only [gmParamOption, gmParam, gmX_mk, gmY_mk, key] at hx hy
        have hD := sq_mul_sub_one_ne_zero ha m
        have hD' := sq_mul_sub_one_ne_zero ha m'
        have e : a * m ^ 2 - 1 = a * m' ^ 2 - 1 := by
          have : 2 / (a * m ^ 2 - 1) = 2 / (a * m' ^ 2 - 1) := by linear_combination hx
          rw [div_eq_div_iff hD hD'] at this
          exact (mul_left_cancel₀ h2 this).symm
        rw [← e] at hy
        have : 2 * m = 2 * m' := (div_left_inj' hD).mp hy
        congr 1
        exact mul_left_cancel₀ h2 this
    · intro z
      by_cases hx : gmX z = 1
      · refine ⟨none, ?_⟩
        have hc := twistedMulGroup_conic z
        have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
        have hy : gmY z = 0 := by
          rw [hx] at hc
          have : a * gmY z ^ 2 = 0 := by linear_combination -hc
          simpa [ha0] using this
        exact twistedMulGroup_ext (by simp [gmParamOption, hx]) (by simp [gmParamOption, hy])
      · have hx' : gmX z - 1 ≠ 0 := sub_ne_zero.mpr hx
        have hc := twistedMulGroup_conic z
        set m := gmY z / (gmX z - 1) with hm
        have hD : a * m ^ 2 - 1 = 2 / (gmX z - 1) := by
          rw [hm]; field_simp; linear_combination -hc
        refine ⟨some m, twistedMulGroup_ext ?_ ?_⟩
        · simp only [gmParamOption, gmParam, gmX_mk, hD]
          rw [show a * m ^ 2 + 1 = 2 / (gmX z - 1) + 2 by linear_combination hD]
          field_simp
          ring
        · simp only [gmParamOption, gmParam, gmY_mk, hD]
          rw [hm]
          field_simp
  exact ⟨(Equiv.ofBijective _ hbij).symm⟩

/-- **Example 3.1** (pdf p. 63). Over $\mathbb F_q$: $\mathbb G_a(\mathbb F_q)$ has $q$ elements,
$\mathbb G_m(\mathbb F_q)$ has $q - 1$, and $\mathbb G_m[a](\mathbb F_q)$ has $q + 1$ for every nonsquare $a$. -/
@[kb "milne2006ec" "Ch. II, Example 3.1, pdf p. 63"]
theorem example_3_1 [Fintype k] (a : k) (ha : ¬IsSquare a) :
    Nat.card k = Fintype.card k ∧ Nat.card kˣ = Fintype.card k - 1 ∧
      Nat.card (twistedMulGroup a) = Fintype.card k + 1 := by
  refine ⟨Nat.card_eq_fintype_card, ?_, ?_⟩
  · classical
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  · have h2 : (2 : k) ≠ 0 := by
      intro h
      have : ringChar k = 2 := by
        have : CharP k 2 := ringChar.of_eq (by
          rcases CharP.exists k with ⟨p, hp⟩
          exact (CharP.ringChar_of_prime_eq_zero Nat.prime_two (by exact_mod_cast h)))
        exact ringChar.eq k 2
      exact ha (FiniteField.isSquare_of_char_two this a)
    have : NeZero (2 : k) := ⟨h2⟩
    obtain ⟨e⟩ := twistedMulGroup_equiv_option ha
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option]

end NumberFieldKB.MilneEC.II
