import NumberFieldKB.WeilBNT.PFieldDuality
import NumberFieldKB.WeilBNT.FieldVectorSpaces

/-!
# Weil, *Basic Number Theory*, II.§5, Thm. 3 and text p. 39: the dual of a vector space over a $p$-field

$K$ is a $p$-field (`hK : IsPField K p`, commutative or not) and $V$ a left vector space of finite dimension over $K$
with its natural topology (a Hausdorff topological vector space; it is unique by I.§2 Cor. 1 of Thm. 3). A *character*
of $V$ is a continuous `AddChar V Circle`. The algebraic dual $V'$ is `V →ₗ[K] K` with $[v,v']=v'(v)$.

* `charSMul`, `continuous_charSMul`, `charSMul_mul`, `charSMul_add`, `charSMul_one`: text p. 39, formula (8). For a
  character $v^*$ and $a\in K$, $v\mapsto(av,v^*)$ is a character $v^*a$, and this is a right action of $K$ on the
  additive group of characters: $(v^*a)b=v^*(ab)$, $v^*(a+b)=v^*a+v^*b$, $v^*1=v^*$.
* **`weil_II_5_thm3`**: Thm. 3. For a non-trivial character $\chi$ of $K$, every character of $V$ is
  $v\mapsto\chi([v,v'])$ for one and only one $v'\in V'$ (with `continuous_comp_linear`: each such map is a character).
  So $v'\mapsto v^*$ is a bijection of $V'$ onto the topological dual $V^*$.
* **`weil_II_5_thm3_alpha`**, `weil_II_5_thm3_alpha_unique`, `weil_II_5_thm3_alpha_eq_refl_iff`: the automorphism
  $\alpha$ of the proof: $\chi(tx)=\chi(\alpha(x)t)$ for all $x,t\in K$ determines a unique ring automorphism $\alpha$
  of $K$, and $\alpha$ is the identity if and only if $\chi(xy)=\chi(yx)$ for all $x,y$.
* **`weil_II_5_thm3_semilinear`**: the map $v'\mapsto v^*$ is $\alpha$-semilinear: the character of $v'x$ is
  $v^*\alpha(x)$.

*Proof* (not Weil's dimension count, which uses Pontryagin duality). Take a basis $(e_i)$ of $V$; the character
$t\mapsto(te_i,v^*)$ of $K$ is $t\mapsto\chi(tx_i)$ by the Corollary (`weil_II_5_cor_thm3_right`), and
$v'(\sum t_ie_i)=\sum t_ix_i$ works. Uniqueness: if $\chi\circ v'=1$ with $v'\ne0$ then $v'$ is onto $K$ and $\chi=1$.
The automorphism $\alpha(x)$ is the $y$ of the Corollary (left form) for the character $t\mapsto\chi(tx)$.
-/

open Topology Filter
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul K V] [T2Space V]

/-! ### The right vector space structure of the dual (text p. 39) -/

/-- The character $v^*a: v\mapsto(av,v^*)$ (Weil's formula (8)). -/
def charSMul (ψ : AddChar V Circle) (a : K) : AddChar V Circle :=
  ψ.compAddMonoidHom (DistribSMul.toAddMonoidHom V a)

@[simp] theorem charSMul_apply (ψ : AddChar V Circle) (a : K) (v : V) : charSMul ψ a v = ψ (a • v) := rfl

@[kb "weil1973bnt" "Ch. II, §5, text p. 39 (V* a right vector space: v*a is a character)"]
theorem continuous_charSMul {ψ : AddChar V Circle} (hψ : Continuous ψ) (a : K) : Continuous (charSMul ψ a) := by
  exact hψ.comp (continuous_const_smul a)

@[kb "weil1973bnt" "Ch. II, §5, text p. 39 (V* a right vector space: (v*a)b = v*(ab))"]
theorem charSMul_mul (ψ : AddChar V Circle) (a b : K) : charSMul (charSMul ψ a) b = charSMul ψ (a * b) := by
  ext v
  simp [smul_smul]

@[kb "weil1973bnt" "Ch. II, §5, text p. 39 (V* a right vector space: v*(a+b) = v*a + v*b)"]
theorem charSMul_add (ψ : AddChar V Circle) (a b : K) : charSMul ψ (a + b) = charSMul ψ a * charSMul ψ b := by
  ext v
  simp [add_smul, AddChar.map_add_eq_mul]

theorem charSMul_one (ψ : AddChar V Circle) : charSMul ψ (1 : K) = ψ := by
  ext v
  simp

/-! ### Theorem 3 -/

/-- A character of an abelian group maps a finite sum to the product of the values. -/
theorem char_sum_eq_prod {A : Type*} [AddCommGroup A] (ψ : AddChar A Circle) {ι : Type*} (s : Finset ι)
    (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- A $K$-linear map from $V$ to $K$ is continuous (Cor. 1 of Thm. 3 of I.§2). -/
theorem continuous_linear_aux (l : V →ₗ[K] K) : Continuous l := by
  set b := Module.finBasis K V with hb
  set e : (Fin (Module.finrank K V) → K) ≃ₗ[K] V := b.equivFun.symm with he
  have hh : IsHomeomorph e := weil_I_2_thm3_cor1 e
  have h1 : Continuous (fun x : Fin (Module.finrank K V) → K => l (e x)) := by
    have : (fun x : Fin (Module.finrank K V) → K => l (e x)) = fun x => ∑ i, x i * l (b i) := by
      funext x
      simp [he, Module.Basis.equivFun_symm_apply, map_sum]
    rw [this]
    fun_prop
  have h2 : l = (fun x : Fin (Module.finrank K V) → K => l (e x)) ∘ hh.homeomorph.symm := by
    funext v
    have := hh.homeomorph.apply_symm_apply v
    simp only [Function.comp_apply]
    rw [show e (hh.homeomorph.symm v) = v from this]
  rw [h2]
  exact h1.comp hh.homeomorph.symm.continuous

/-- Each $v\mapsto\chi([v,v'])$ is a character of $V$. -/
theorem continuous_comp_linear {χ : AddChar K Circle} (hχ : Continuous χ) (l : V →ₗ[K] K) :
    Continuous (fun v => χ (l v)) :=
  hχ.comp (continuous_linear_aux l)

/-- If `χ ≠ 1` and `χ (a * t) = χ (b * t)` for all `t`, then `a = b`. -/
theorem eq_of_char_mul_left {χ : AddChar K Circle} (hχ1 : χ ≠ 1) {a b : K}
    (h : ∀ t, χ (a * t) = χ (b * t)) : a = b := by
  by_contra hne
  have hne' : a - b ≠ 0 := sub_ne_zero.2 hne
  apply hχ1
  refine AddChar.ext _ _ fun t => ?_
  rw [AddChar.one_apply]
  have := h ((a - b)⁻¹ * t)
  have h2 : χ ((a - b) * ((a - b)⁻¹ * t)) = 1 := by
    rw [sub_mul, AddChar.map_sub_eq_div, this, div_self']
  rwa [← mul_assoc, mul_inv_cancel₀ hne', one_mul] at h2

/-- **Thm. 3** ($p$-fields). For a non-trivial character $\chi$ of $K$, every character $v^*$ of $V$ is
$v\mapsto\chi([v,v'])$ for one and only one $v'$ in the algebraic dual $V'$. -/
@[kb "weil1973bnt" "Ch. II, §5, Thm. 3 (p-fields: the bijection of V' onto V*)"]
theorem weil_II_5_thm3 (hK : IsPField K p) {χ : AddChar K Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    {ψ : AddChar V Circle} (hψ : Continuous ψ) : ∃! l : V →ₗ[K] K, ∀ v, ψ v = χ (l v) := by
  set b := Module.finBasis K V with hb
  have hx : ∀ i, ∃ x : K, ∀ t, ψ (t • b i) = χ (t * x) := by
    intro i
    let θ : AddChar K Circle :=
      ψ.compAddMonoidHom (LinearMap.toSpanSingleton K V (b i)).toAddMonoidHom
    have hθ : Continuous θ := hψ.comp (continuous_id.smul continuous_const)
    obtain ⟨x, hx, -⟩ := weil_II_5_cor_thm3_right hK hχ hχ1 hθ
    exact ⟨x, hx⟩
  choose x hx using hx
  let l : V →ₗ[K] K := ∑ i, (LinearMap.toSpanSingleton K K (x i)).comp (b.coord i)
  have hl : ∀ v, l v = ∑ i, b.repr v i * x i := by
    intro v
    simp [l]
  have hexist : ∀ v, ψ v = χ (l v) := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [char_sum_eq_prod, hl, char_sum_eq_prod]
    exact Finset.prod_congr rfl fun i _ => hx i _
  refine ⟨l, hexist, fun l' hl' => ?_⟩
  by_contra hne
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, l' v₀ ≠ l v₀ := by
    by_contra hcon
    push Not at hcon
    exact hne (LinearMap.ext hcon)
  have hd : ∀ v, χ (l' v - l v) = 1 := by
    intro v
    rw [AddChar.map_sub_eq_div, ← hl', ← hexist, div_self']
  apply hχ1
  refine AddChar.ext _ _ fun t => ?_
  rw [AddChar.one_apply]
  have hne' : l' v₀ - l v₀ ≠ 0 := sub_ne_zero.2 hv₀
  have := hd ((t * (l' v₀ - l v₀)⁻¹) • v₀)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub, mul_assoc, inv_mul_cancel₀ hne', mul_one] at this
  simpa using this

/-- The automorphism $\alpha$ of the proof of Thm. 3: $\chi(tx)=\chi(\alpha(x)t)$. -/
@[kb "weil1973bnt" "Ch. II, §5, proof of Thm. 3 (the automorphism α)"]
theorem weil_II_5_thm3_alpha (hK : IsPField K p) {χ : AddChar K Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) :
    ∃ α : K ≃+* K, ∀ x t : K, χ (t * x) = χ (α x * t) := by
  have hex : ∀ x : K, ∃ y : K, ∀ t, χ (t * x) = χ (y * t) := by
    intro x
    let θ : AddChar K Circle :=
      ⟨fun t => χ (t * x), by simp, fun s t => by simp [add_mul, AddChar.map_add_eq_mul]⟩
    have hθ : Continuous θ := hχ.comp (continuous_id.mul continuous_const)
    obtain ⟨y, hy, -⟩ := weil_II_5_cor_thm3_left hK hχ hχ1 hθ
    exact ⟨y, hy⟩
  choose a ha using hex
  have hadd : ∀ x y, a (x + y) = a x + a y := by
    intro x y
    refine eq_of_char_mul_left hχ1 fun t => ?_
    calc χ (a (x + y) * t) = χ (t * (x + y)) := (ha _ _).symm
      _ = χ (t * x) * χ (t * y) := by rw [mul_add, AddChar.map_add_eq_mul]
      _ = χ (a x * t) * χ (a y * t) := by rw [ha x t, ha y t]
      _ = χ ((a x + a y) * t) := by rw [add_mul, AddChar.map_add_eq_mul]
  have hmul : ∀ x y, a (x * y) = a x * a y := by
    intro x y
    refine eq_of_char_mul_left hχ1 fun t => ?_
    calc χ (a (x * y) * t) = χ (t * (x * y)) := (ha _ _).symm
      _ = χ ((t * x) * y) := by rw [mul_assoc]
      _ = χ (a y * (t * x)) := ha y (t * x)
      _ = χ ((a y * t) * x) := by rw [mul_assoc]
      _ = χ (a x * (a y * t)) := ha x _
      _ = χ ((a x * a y) * t) := by rw [mul_assoc]
  have hone : a 1 = 1 := by
    refine eq_of_char_mul_left hχ1 fun t => ?_
    rw [← ha, one_mul, mul_one]
  have hzero : a 0 = 0 := by
    have := hadd 0 0
    simpa using this
  let f : K →+* K := { toFun := a, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := hadd }
  have hsurj : Function.Surjective f := by
    intro y
    let θ : AddChar K Circle :=
      ⟨fun t => χ (y * t), by simp, fun s t => by simp [mul_add, AddChar.map_add_eq_mul]⟩
    have hθ : Continuous θ := hχ.comp (continuous_const.mul continuous_id)
    obtain ⟨x, hx, -⟩ := weil_II_5_cor_thm3_right hK hχ hχ1 hθ
    refine ⟨x, eq_of_char_mul_left hχ1 fun t => ?_⟩
    show χ (a x * t) = χ (y * t)
    rw [← ha]
    exact (hx t).symm
  exact ⟨RingEquiv.ofBijective f ⟨f.injective, hsurj⟩, fun x t => ha x t⟩

theorem weil_II_5_thm3_alpha_unique {χ : AddChar K Circle} (hχ1 : χ ≠ 1) {α β : K ≃+* K}
    (hα : ∀ x t : K, χ (t * x) = χ (α x * t)) (hβ : ∀ x t : K, χ (t * x) = χ (β x * t)) : α = β := by
  ext x
  exact eq_of_char_mul_left hχ1 fun t => ((hα x t).symm.trans (hβ x t))

/-- $\alpha$ is the identity if and only if $\chi(xy)=\chi(yx)$ for all $x,y$. -/
@[kb "weil1973bnt" "Ch. II, §5, proof of Thm. 3 (α is the identity iff χ(xy) = χ(yx))"]
theorem weil_II_5_thm3_alpha_eq_refl_iff {χ : AddChar K Circle} (hχ1 : χ ≠ 1) {α : K ≃+* K}
    (hα : ∀ x t : K, χ (t * x) = χ (α x * t)) : α = RingEquiv.refl K ↔ ∀ x y : K, χ (x * y) = χ (y * x) := by
  constructor
  · rintro rfl x y
    simpa using hα y x
  · intro h
    ext x
    refine eq_of_char_mul_left hχ1 fun t => ?_
    simp only [RingEquiv.refl_apply]
    rw [← hα, h]

/-- **Thm. 3**, semilinearity: the character attached to $v'x$ ($v\mapsto[v,v']x$) is $v^*\alpha(x)$. -/
@[kb "weil1973bnt" "Ch. II, §5, Thm. 3 (the map V' → V* is α-semilinear)"]
theorem weil_II_5_thm3_semilinear {χ : AddChar K Circle} {α : K ≃+* K}
    (hα : ∀ x t : K, χ (t * x) = χ (α x * t)) (l : V →ₗ[K] K) (x : K) (v : V) :
    χ (l v * x) = χ (l (α x • v)) := by
  rw [map_smul, smul_eq_mul]
  exact hα x (l v)

end NumberFieldKB.WeilBNT.FieldModule
