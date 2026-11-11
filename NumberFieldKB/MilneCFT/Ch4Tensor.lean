import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Module.StablyFree.Basic
import QuadFormsKB.Citation

/-!
# Milne, Class Field Theory, Chapter IV, §2: tensor products of simple algebras

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV ("Brauer groups"), §2: centralizers in tensor products (Prop. 2.3), primordial
elements (Prop. 2.5), simplicity of tensor products (Lemma 2.7, Prop. 2.6, Cor. 2.8),
$A \otimes_k A^{\mathrm{opp}} \cong \mathrm{End}_k(A)$ (Cor. 2.9), extension of the base field
(Prop. 2.15, Cor. 2.16).

Conventions.
* Milne's standing convention in Chapter IV is that a $k$-algebra is finite dimensional over the
  field $k$.  Results whose proofs do not need finite dimension are stated here without it (they
  then hold in particular under Milne's convention); the docstrings say so.
* Milne writes the base change of $A$ to a field $L \supseteq k$ as $A \otimes_k L$.  Lean's
  $L$-algebra structure is on `L ⊗[K] A` (the scalars act on the left factor), so we use that order.
* Locators give the printed page of the book (printed page = pdf page − 9).
-/

open scoped TensorProduct

namespace NumberFieldKB.MilneCFT.Ch4

universe u v w

variable {K : Type u} [Field K]

/-! ### Centralizers in tensor products -/

/-- Over a field, the tensor product of injective algebra maps is injective. -/
private lemma map_injective_of_inj {A : Type v} {A' : Type w} {C C' : Type*} [Ring C]
    [Algebra K C] [Ring C'] [Algebra K C'] [Ring A] [Algebra K A] [Ring A'] [Algebra K A']
    (f : C →ₐ[K] A) (g : C' →ₐ[K] A') (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.map f g) := by
  have := TensorProduct.map_injective_of_flat_flat (R := K) f.toLinearMap g.toLinearMap hf hg
  have h : ⇑(Algebra.TensorProduct.map f g) =
      ⇑(TensorProduct.map f.toLinearMap g.toLinearMap) := by
    funext t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [h]; exact this

/-- Proposition 2.3 of Milne: for $K$-algebras $A, A'$ with subalgebras $B, B'$, the centralizer
of $B \otimes_K B'$ in $A \otimes_K A'$ is $C_A(B) \otimes_K C_{A'}(B')$.

Here $B \otimes B'$ and $C_A(B) \otimes C_{A'}(B')$ are the images in $A \otimes_K A'$ (over a
field the maps are injective).  No finite dimension is needed. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 2.3, p. 126"]
theorem prop_2_3 (A : Type v) (A' : Type w) [Ring A] [Algebra K A] [Ring A'] [Algebra K A']
    (B : Subalgebra K A) (B' : Subalgebra K A') :
    Subalgebra.centralizer K
        ((Algebra.TensorProduct.map B.val B'.val).range : Set (A ⊗[K] A')) =
      (Algebra.TensorProduct.map (Subalgebra.centralizer K (B : Set A)).val
        (Subalgebra.centralizer K (B' : Set A')).val).range := by
  apply le_antisymm
  · intro z hz
    rw [Subalgebra.mem_centralizer_iff] at hz
    have hz1 : z ∈ Subalgebra.centralizer K
        (Algebra.TensorProduct.includeLeft (S := K) (R := K) (A := A) (B := A') '' (B : Set A)) := by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      apply hz
      exact ⟨(⟨b, hb⟩ : B) ⊗ₜ[K] (1 : B'), by simp⟩
    rw [Subalgebra.centralizer_coe_image_includeLeft_eq_center_tensorProduct] at hz1
    obtain ⟨t, rfl⟩ : ∃ t, Algebra.TensorProduct.map (Subalgebra.centralizer K (B : Set A)).val
        (AlgHom.id K A') t = z := hz1
    have hinj := map_injective_of_inj (K := K) (Subalgebra.centralizer K (B : Set A)).val
      (AlgHom.id K A') Subtype.val_injective Function.injective_id
    have ht : t ∈ Subalgebra.centralizer K
        (Algebra.TensorProduct.includeRight (R := K)
          (A := Subalgebra.centralizer K (B : Set A)) (B := A') '' (B' : Set A')) := by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨b', hb', rfl⟩
      apply hinj
      rw [map_mul, map_mul]
      have h1 := hz (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := A') b')
        ⟨(1 : B) ⊗ₜ[K] (⟨b', hb'⟩ : B'), by simp⟩
      have h2 : Algebra.TensorProduct.map (Subalgebra.centralizer K (B : Set A)).val
          (AlgHom.id K A')
          (Algebra.TensorProduct.includeRight (R := K)
            (A := Subalgebra.centralizer K (B : Set A)) (B := A') b') =
          Algebra.TensorProduct.includeRight (R := K) (A := A) (B := A') b' := by simp
      rw [h2]
      exact h1
    rw [Subalgebra.centralizer_coe_image_includeRight_eq_center_tensorProduct] at ht
    obtain ⟨s, rfl⟩ : ∃ s, Algebra.TensorProduct.map
        (AlgHom.id K (Subalgebra.centralizer K (B : Set A)))
        (Subalgebra.centralizer K (B' : Set A')).val s = t := ht
    have hcomp : ∀ s : Subalgebra.centralizer K (B : Set A) ⊗[K]
        Subalgebra.centralizer K (B' : Set A'),
        Algebra.TensorProduct.map (Subalgebra.centralizer K (B : Set A)).val
          (Subalgebra.centralizer K (B' : Set A')).val s =
        Algebra.TensorProduct.map (Subalgebra.centralizer K (B : Set A)).val (AlgHom.id K A')
          (Algebra.TensorProduct.map (AlgHom.id K (Subalgebra.centralizer K (B : Set A)))
            (Subalgebra.centralizer K (B' : Set A')).val s) := by
      intro s
      induction s using TensorProduct.inductionOn with
      | tmul a b => simp
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    exact ⟨s, hcomp s⟩
  · rintro _ ⟨t, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨s, rfl⟩
    show Algebra.TensorProduct.map B.val B'.val s *
        Algebra.TensorProduct.map (Subalgebra.centralizer K (B : Set A)).val
          (Subalgebra.centralizer K (B' : Set A')).val t =
        Algebra.TensorProduct.map (Subalgebra.centralizer K (B : Set A)).val
          (Subalgebra.centralizer K (B' : Set A')).val t *
        Algebra.TensorProduct.map B.val B'.val s
    induction s using TensorProduct.inductionOn with
    | tmul b b' =>
      induction t using TensorProduct.inductionOn with
      | tmul c c' =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
        have e1 := (Subalgebra.mem_centralizer_iff (R := K)).mp c.2 b b.2
        have e2 := (Subalgebra.mem_centralizer_iff (R := K)).mp c'.2 b' b'.2
        simp only [Subalgebra.coe_val, e1, e2]
      | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]
    | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]

/-- The remark after Proposition 2.3 of Milne: the centre of $A \otimes_K B$ is
$Z(A) \otimes_K Z(B)$ (as subalgebras of $A \otimes_K B$). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §2, centre of a tensor product (after Prop. 2.3), p. 127"]
theorem center_tensorProduct (A : Type v) (B : Type w) [Ring A] [Algebra K A] [Ring B]
    [Algebra K B] :
    Subalgebra.center K (A ⊗[K] B) =
      (Algebra.TensorProduct.map (Subalgebra.center K A).val
        (Subalgebra.center K B).val).range := by
  have h := prop_2_3 (K := K) A B ⊤ ⊤
  have e1 : (Algebra.TensorProduct.map (⊤ : Subalgebra K A).val (⊤ : Subalgebra K B).val).range
      = ⊤ := by
    rw [eq_top_iff]
    intro z _
    induction z using TensorProduct.inductionOn with
    | tmul a b => exact ⟨(⟨a, trivial⟩ : (⊤ : Subalgebra K A)) ⊗ₜ[K] ⟨b, trivial⟩, by simp⟩
    | add x y hx hy => exact Subalgebra.add_mem _ (hx trivial) (hy trivial)
  have e2 : Subalgebra.centralizer K ((⊤ : Subalgebra K A) : Set A) = Subalgebra.center K A := by
    rw [Algebra.coe_top, Subalgebra.centralizer_univ]
  have e3 : Subalgebra.centralizer K ((⊤ : Subalgebra K B) : Set B) = Subalgebra.center K B := by
    rw [Algebra.coe_top, Subalgebra.centralizer_univ]
  rw [e1, e2, e3] at h
  rw [← h]
  rw [← Subalgebra.centralizer_univ, ← Algebra.coe_top (R := K)]

/-! ### Primordial elements -/

section Primordial

variable {k : Type u} [DivisionRing k] {V : Type v} [AddCommGroup V] [Module k V]
  {ι : Type w}

/-- Milne's $J(v)$: the set of indices $i$ with $a_i \neq 0$ in $v = \sum a_i e_i$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §2, def. of J(v), p. 127"]
noncomputable def supp (b : Module.Basis ι k V) (v : V) : Finset ι :=
  (b.repr v).support

/-- A nonzero element $w$ of a subspace $W$ is *primordial* (relative to $V$ and the basis
$(e_i)$) if $J(w)$ is minimal among the sets $J(w')$ for nonzero $w' \in W$, and at least one
coefficient of $w$ equals $1$.  ($k$ may be a division ring, as Milne remarks.) -/
@[kb "milne2020cft" "v4.03, Ch. IV, §2, def. of primordial element, p. 127"]
def IsPrimordial (b : Module.Basis ι k V) (W : Submodule k V) (w : V) : Prop :=
  w ∈ W ∧ w ≠ 0 ∧ (∀ w' ∈ W, w' ≠ 0 → ¬ supp b w' ⊂ supp b w) ∧ ∃ i, b.repr w i = 1

/-- Proposition 2.5 (a) of Milne: if $w \in W$ is nonzero with $J(w)$ minimal and $w' \in W$ is
nonzero, then $J(w') \subseteq J(w)$ if and only if $w' = c w$ for a nonzero $c \in k$, in which
case $J(w') = J(w)$.  (Scalars act on the left.) -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 2.5(a), p. 127"]
theorem prop_2_5a (b : Module.Basis ι k V) (W : Submodule k V) {w w' : V} (hw : w ∈ W)
    (_hw0 : w ≠ 0) (hmin : ∀ w'' ∈ W, w'' ≠ 0 → ¬ supp b w'' ⊂ supp b w) (hw' : w' ∈ W)
    (hw'0 : w' ≠ 0) :
    (supp b w' ⊆ supp b w ↔ ∃ c : k, c ≠ 0 ∧ w' = c • w) ∧
      (supp b w' ⊆ supp b w → supp b w' = supp b w) := by
  have hsmul : ∀ (c : k), c ≠ 0 → supp b (c • w) = supp b w := by
    intro c hc
    ext i
    simp [supp, hc]
  have main : supp b w' ⊆ supp b w ↔ ∃ c : k, c ≠ 0 ∧ w' = c • w := by
    constructor
    · intro hsub
      have hne : (b.repr w').support.Nonempty := by
        rw [Finsupp.support_nonempty_iff]
        intro h; apply hw'0; simpa using h
      obtain ⟨j, hj⟩ := hne
      have hjw : j ∈ supp b w := hsub hj
      have ha : b.repr w j ≠ 0 := Finsupp.mem_support_iff.mp hjw
      set c : k := b.repr w' j * (b.repr w j)⁻¹ with hc
      have hw'' : w' - c • w ∈ W := W.sub_mem hw' (W.smul_mem c hw)
      have hrepr : ∀ i, b.repr (w' - c • w) i = b.repr w' i - c * b.repr w i := by
        intro i; simp
      by_cases h0 : w' - c • w = 0
      · refine ⟨c, ?_, sub_eq_zero.mp h0⟩
        intro hc0
        apply hw'0
        have := sub_eq_zero.mp h0
        rw [this, hc0, zero_smul]
      · exfalso
        apply hmin _ hw'' h0
        refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨j, hjw, ?_⟩
        · intro i hi
          rw [supp, Finsupp.mem_support_iff, hrepr] at hi
          by_contra hiw
          apply hi
          have : b.repr w i = 0 := by simpa [supp] using hiw
          have h2 : b.repr w' i = 0 := by
            by_contra h2
            exact hiw (hsub (Finsupp.mem_support_iff.mpr h2))
          rw [this, h2]; simp
        · rw [supp, Finsupp.mem_support_iff, hrepr, hc]
          simp [ha]
    · rintro ⟨c, hc, rfl⟩
      rw [hsmul c hc]
  refine ⟨main, fun h => ?_⟩
  obtain ⟨c, hc, rfl⟩ := main.mp h
  exact hsmul c hc

/-- Helper for Prop. 2.5 (b): below every nonzero element of `W` there is a primordial element
(with smaller or equal support). -/
theorem exists_primordial_le (b : Module.Basis ι k V) (W : Submodule k V) :
    ∀ n, ∀ w ∈ W, w ≠ 0 → (supp b w).card = n → ∃ p, IsPrimordial b W p ∧ supp b p ⊆ supp b w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw hw0 hn
    by_cases hm : ∀ w'' ∈ W, w'' ≠ 0 → ¬ supp b w'' ⊂ supp b w
    · have hne : (b.repr w).support.Nonempty := by
        rw [Finsupp.support_nonempty_iff]
        intro h; apply hw0; simpa using h
      obtain ⟨i, hi⟩ := hne
      have ha : b.repr w i ≠ 0 := Finsupp.mem_support_iff.mp hi
      refine ⟨(b.repr w i)⁻¹ • w, ⟨W.smul_mem _ hw, ?_, ?_, ⟨i, ?_⟩⟩, ?_⟩
      · simpa [ha] using hw0
      · intro w'' h1 h2
        have : supp b ((b.repr w i)⁻¹ • w) = supp b w := by
          ext j; simp [supp, ha]
        rw [this]; exact hm w'' h1 h2
      · simp [ha]
      · intro j hj; simpa [supp, ha] using hj
    · push Not at hm
      obtain ⟨w'', h1, h2, h3⟩ := hm
      obtain ⟨p, hp, hpsub⟩ := ih _ (hn ▸ Finset.card_lt_card h3) w'' h1 h2 rfl
      exact ⟨p, hp, hpsub.trans h3.subset⟩

/-- Proposition 2.5 (b) of Milne: the primordial elements of $W$ span $W$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 2.5(b), p. 127"]
theorem prop_2_5b (b : Module.Basis ι k V) (W : Submodule k V) :
    Submodule.span k {w | IsPrimordial b W w} = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro w hw; exact hw.1
  · have key : ∀ n, ∀ w ∈ W, (supp b w).card = n →
        w ∈ Submodule.span k {w | IsPrimordial b W w} := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro w hw hn
        by_cases hw0 : w = 0
        · simp [hw0]
        obtain ⟨p, hp, hpsub⟩ := exists_primordial_le b W _ w hw hw0 rfl
        obtain ⟨i, hi⟩ := hp.2.2.2
        have hip : i ∈ supp b p := by
          rw [supp, Finsupp.mem_support_iff, hi]; exact one_ne_zero
        set c := b.repr w i with hc
        have hw1 : w - c • p ∈ W := W.sub_mem hw (W.smul_mem c hp.1)
        by_cases h0 : w - c • p = 0
        · have : w = c • p := sub_eq_zero.mp h0
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.subset_span hp)
        · have hlt : supp b (w - c • p) ⊂ supp b w := by
            refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨i, hpsub hip, ?_⟩
            · intro j hj
              rw [supp, Finsupp.mem_support_iff] at hj
              by_contra hjw
              apply hj
              have h1 : b.repr w j = 0 := by simpa [supp] using hjw
              have h2 : b.repr p j = 0 := by
                by_contra h2
                exact hjw (hpsub (Finsupp.mem_support_iff.mpr h2))
              simp [h1, h2]
            · rw [supp, Finsupp.mem_support_iff]
              simp [hi, hc]
          have := ih _ (hn ▸ Finset.card_lt_card hlt) _ hw1 rfl
          have h3 := Submodule.add_mem _ this (Submodule.smul_mem _ c (Submodule.subset_span hp))
          simpa using h3
    intro w hw
    exact key _ w hw rfl

end Primordial

/-! ### Simplicity of tensor products -/

section KeyAux

variable {A : Type v} {B : Type w} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
variable {ι : Type*} [DecidableEq ι]

private lemma phi_mul_left (e : Module.Basis ι K A) (u : B) (x : A ⊗[K] B) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft e ((1 ⊗ₜ[K] u) * x) i =
      u * TensorProduct.equivFinsuppOfBasisLeft e x i := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [mul_add, hx, hy]

private lemma phi_mul_right (e : Module.Basis ι K A) (u : B) (x : A ⊗[K] B) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft e (x * (1 ⊗ₜ[K] u)) i =
      TensorProduct.equivFinsuppOfBasisLeft e x i * u := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [add_mul, hx, hy]

/-- Core of the proof of Lemma 2.7: a nonzero element `x` of a two-sided ideal `I` of `A ⊗ B`
(`B` central simple) yields `a` with `a ⊗ 1 ∈ I`, whose coefficient (in the basis `e` of `A`)
is `1` at an index in the support of `x` and which is supported inside the support of `x`. -/
private lemma exists_central_elt [Algebra.IsCentral K B] [IsSimpleRing B]
    (e : Module.Basis ι K A)
    (I : TwoSidedIdeal (A ⊗[K] B)) (x : A ⊗[K] B) (hxI : x ∈ I) (hx0 : x ≠ 0) :
    ∃ a : A, a ⊗ₜ[K] (1 : B) ∈ I ∧ ∃ j, TensorProduct.equivFinsuppOfBasisLeft e x j ≠ 0 ∧
      TensorProduct.equivFinsuppOfBasisLeft e (a ⊗ₜ[K] (1 : B)) j = 1 ∧
      ∀ i, TensorProduct.equivFinsuppOfBasisLeft e x i = 0 →
        TensorProduct.equivFinsuppOfBasisLeft e (a ⊗ₜ[K] (1 : B)) i = 0 := by
  classical
  set Φ := TensorProduct.equivFinsuppOfBasisLeft (R := K) (M := A) (N := B) e with hΦ
  have hex : ∃ n, ∃ y ∈ I, y ≠ 0 ∧ (Φ y).support ⊆ (Φ x).support ∧ (Φ y).support.card = n :=
    ⟨_, x, hxI, hx0, subset_rfl, rfl⟩
  obtain ⟨y, hyI, hy0, hyx, hycard⟩ := Nat.find_spec hex
  have hmin : ∀ z ∈ I, z ≠ 0 → (Φ z).support ⊆ (Φ x).support →
      (Φ y).support.card ≤ (Φ z).support.card := by
    intro z hz hz0 hzx
    rw [hycard]; exact Nat.find_min' hex ⟨z, hz, hz0, hzx, rfl⟩
  have hΦy : Φ y ≠ 0 := fun h => hy0 (Φ.injective (by simpa using h))
  obtain ⟨j0, hj0⟩ := Finsupp.support_nonempty_iff.mpr hΦy
  have hd : Φ y j0 ≠ 0 := Finsupp.mem_support_iff.mp hj0
  -- the ideal of attainable coefficients
  let T : Set B := {z | ∃ y' ∈ I, (∀ i, Φ y i = 0 → Φ y' i = 0) ∧ Φ y' j0 = z}
  let J0 : TwoSidedIdeal B := TwoSidedIdeal.mk' T
    ⟨0, I.zero_mem, fun i _ => by simp, by simp⟩
    (by
      rintro _ _ ⟨y1, h1, s1, r1⟩ ⟨y2, h2, s2, r2⟩
      exact ⟨y1 + y2, I.add_mem h1 h2, fun i hi => by simp [s1 i hi, s2 i hi], by simp [r1, r2]⟩)
    (by
      rintro _ ⟨y1, h1, s1, r1⟩
      exact ⟨-y1, I.neg_mem h1, fun i hi => by simp [s1 i hi], by simp [r1]⟩)
    (by
      rintro r _ ⟨y1, h1, s1, r1⟩
      refine ⟨(1 ⊗ₜ[K] r) * y1, I.mul_mem_left _ _ h1, fun i hi => ?_, ?_⟩
      · rw [hΦ, phi_mul_left, ← hΦ, s1 i hi, mul_zero]
      · rw [hΦ, phi_mul_left, ← hΦ, r1])
    (by
      rintro _ r ⟨y1, h1, s1, r1⟩
      refine ⟨y1 * (1 ⊗ₜ[K] r), I.mul_mem_right _ _ h1, fun i hi => ?_, ?_⟩
      · rw [hΦ, phi_mul_right, ← hΦ, s1 i hi, zero_mul]
      · rw [hΦ, phi_mul_right, ← hΦ, r1])
  have h1 : (1 : B) ∈ J0 := by
    have hspan : (1 : B) ∈ TwoSidedIdeal.span {Φ y j0} :=
      IsSimpleRing.one_mem_of_ne_zero_mem _ hd (TwoSidedIdeal.subset_span rfl)
    rw [TwoSidedIdeal.mem_span_iff] at hspan
    apply hspan J0
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    show _ ∈ J0
    rw [TwoSidedIdeal.mem_mk']
    exact ⟨y, hyI, fun i hi => hi, rfl⟩
  obtain ⟨y', hy'I, hy'y, hy'j⟩ : ∃ y' ∈ I, (∀ i, Φ y i = 0 → Φ y' i = 0) ∧ Φ y' j0 = 1 := by
    have := (TwoSidedIdeal.mem_mk' T _ _ _ _ _ _).mp h1
    exact this
  have hy'0 : y' ≠ 0 := by
    rintro rfl
    simp at hy'j
  have hsub : (Φ y').support ⊆ (Φ y).support := by
    intro i hi
    by_contra h
    exact (Finsupp.mem_support_iff.mp hi) (hy'y i (by simpa using h))
  have hsubx : (Φ y').support ⊆ (Φ x).support := hsub.trans hyx
  have hcard : (Φ y).support.card ≤ (Φ y').support.card := hmin y' hy'I hy'0 hsubx
  have heq : (Φ y').support = (Φ y).support := Finset.eq_of_subset_of_card_le hsub hcard
  have hcomm : ∀ β : B, ∀ i, β * Φ y' i = Φ y' i * β := by
    intro β
    have hz : (1 ⊗ₜ[K] β) * y' - y' * (1 ⊗ₜ[K] β) ∈ I :=
      I.sub_mem (I.mul_mem_left _ _ hy'I) (I.mul_mem_right _ _ hy'I)
    have hzi : ∀ i, Φ ((1 ⊗ₜ[K] β) * y' - y' * (1 ⊗ₜ[K] β)) i = β * Φ y' i - Φ y' i * β := by
      intro i
      rw [map_sub, Finsupp.sub_apply, hΦ, phi_mul_left, phi_mul_right]
    by_cases hz0 : (1 ⊗ₜ[K] β) * y' - y' * (1 ⊗ₜ[K] β) = 0
    · intro i
      have := hzi i
      rw [hz0, map_zero] at this
      exact (sub_eq_zero.mp this.symm)
    · exfalso
      have hsz : (Φ ((1 ⊗ₜ[K] β) * y' - y' * (1 ⊗ₜ[K] β))).support ⊂ (Φ y').support := by
        refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨j0, ?_, ?_⟩
        · intro i hi
          rw [Finsupp.mem_support_iff, hzi] at hi
          rw [Finsupp.mem_support_iff]
          intro h; apply hi; rw [h]; simp
        · rw [Finsupp.mem_support_iff, hy'j]; exact one_ne_zero
        · rw [Finsupp.mem_support_iff, hzi, hy'j]; simp
      have := hmin _ hz hz0 (hsz.subset.trans hsubx)
      have := Finset.card_lt_card hsz
      rw [heq] at this
      omega
  have hcentral : ∀ i, ∃ r : K, algebraMap K B r = Φ y' i := by
    intro i
    have hmem : Φ y' i ∈ Subalgebra.center K B := by
      rw [Subalgebra.mem_center_iff]
      intro b; exact hcomm b i
    have := Algebra.IsCentral.out hmem
    rw [Algebra.mem_bot] at this
    obtain ⟨r, hr⟩ := this
    exact ⟨r, hr⟩
  choose lam hlam using hcentral
  have hy'eq : y' = (∑ i ∈ (Φ y').support, lam i • e i) ⊗ₜ[K] (1 : B) := by
    apply Φ.injective
    have hsymm : y' = Φ.symm (Φ y') := (Φ.symm_apply_apply y').symm
    conv_lhs => rw [hsymm]
    rw [hΦ, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum,
      TensorProduct.sum_tmul]
    apply congrArg
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hlam i, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine ⟨_, hy'eq ▸ hy'I, j0, ?_, ?_, ?_⟩
  · exact Finsupp.mem_support_iff.mp
      (hsubx (by rw [Finsupp.mem_support_iff, hy'j]; exact one_ne_zero))
  · rw [← hy'eq]; exact hy'j
  · intro i hi
    rw [← hy'eq]
    exact hy'y i (by
      by_contra h
      exact h (by
        by_contra h2
        exact (Finsupp.mem_support_iff.mp (hyx (Finsupp.mem_support_iff.mpr h))) hi))

end KeyAux

/-- Generalization of Lemma 2.7 of Milne used for Prop. 2.6: for a $K$-algebra $A$ and a central
simple $K$-algebra $B$ (no finite dimension needed), every two-sided ideal $I$ of $A \otimes_K B$
is spanned by the elements $a \otimes b$ with $a \otimes 1 \in I$. -/
theorem twoSidedIdeal_eq_span_of_isCentral (A : Type v) (B : Type w) [Ring A] [Algebra K A]
    [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B]
    (I : TwoSidedIdeal (A ⊗[K] B)) :
    (I : Set (A ⊗[K] B)) =
      Submodule.span K {x | ∃ (a : A) (b : B), a ⊗ₜ[K] (1 : B) ∈ I ∧ x = a ⊗ₜ[K] b} := by
  classical
  let e := Module.Free.chooseBasis K A
  set Φ := TensorProduct.equivFinsuppOfBasisLeft (R := K) (M := A) (N := B) e with hΦ
  apply Set.Subset.antisymm
  · intro x0 hx0
    have key : ∀ n, ∀ x ∈ I, (Φ x).support.card = n → x ∈ Submodule.span K
        {x | ∃ (a : A) (b : B), a ⊗ₜ[K] (1 : B) ∈ I ∧ x = a ⊗ₜ[K] b} := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro x hxI hn
        by_cases hx : x = 0
        · simp [hx]
        obtain ⟨a, haI, j, hj, hj1, hsupp⟩ := exists_central_elt e I x hxI hx
        set c := Φ x j with hc
        have hac : a ⊗ₜ[K] c = (1 ⊗ₜ[K] c) * (a ⊗ₜ[K] (1 : B)) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        have hacI : a ⊗ₜ[K] c ∈ I := by
          rw [hac]; exact I.mul_mem_left _ _ haI
        have hwI : x - a ⊗ₜ[K] c ∈ I := I.sub_mem hxI hacI
        have hwi : ∀ i, Φ (x - a ⊗ₜ[K] c) i = Φ x i - c * Φ (a ⊗ₜ[K] (1 : B)) i := by
          intro i
          rw [map_sub, Finsupp.sub_apply, hac, hΦ, phi_mul_left]
        have hsz : (Φ (x - a ⊗ₜ[K] c)).support ⊂ (Φ x).support := by
          refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨j, ?_, ?_⟩
          · intro i hi
            rw [Finsupp.mem_support_iff, hwi] at hi
            rw [Finsupp.mem_support_iff]
            intro h; apply hi; rw [h, hsupp i h]; simp
          · exact Finsupp.mem_support_iff.mpr hj
          · rw [Finsupp.mem_support_iff, hwi, hj1]; simp [hc]
        have hlt := Finset.card_lt_card hsz
        have hw := ih _ (hn ▸ hlt) _ hwI rfl
        have : a ⊗ₜ[K] c ∈ Submodule.span K
            {x | ∃ (a : A) (b : B), a ⊗ₜ[K] (1 : B) ∈ I ∧ x = a ⊗ₜ[K] b} :=
          Submodule.subset_span ⟨a, c, haI, rfl⟩
        have := Submodule.add_mem _ hw this
        simpa using this
    exact key _ x0 hx0 rfl
  · intro x hx
    have hx' : x ∈ Submodule.span K
        {x | ∃ (a : A) (b : B), a ⊗ₜ[K] (1 : B) ∈ I ∧ x = a ⊗ₜ[K] b} := hx
    clear hx
    show x ∈ I
    induction hx' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, b, ha, rfl⟩ := hx
      have : a ⊗ₜ[K] b = (a ⊗ₜ[K] (1 : B)) * (1 ⊗ₜ[K] b) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [this]
      exact I.mul_mem_right _ _ ha
    | zero => exact I.zero_mem
    | add x y _ _ hx hy => exact I.add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact I.mul_mem_left _ _ hx

/-- Lemma 2.7 of Milne: let $A$ be a $K$-algebra and $D$ a division algebra with centre $K$.
Then every two-sided ideal $\mathfrak A$ of $A \otimes_K D$ is generated as a left $D$-module
(with $\delta (\alpha \otimes \delta') = \alpha \otimes \delta\delta'$) by
$\mathfrak a = \mathfrak A \cap (A \otimes 1)$.

The $D$-module generated by $\mathfrak a$ is written out: it is the $K$-span of the elements
$\delta \cdot (a \otimes 1) = a \otimes \delta$ with $a \otimes 1 \in \mathfrak A$.  As Milne
notes (proof of Prop. 2.15), finite dimension of $D$ is not used. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Lem. 2.7, p. 128"]
theorem lemma_2_7 (A : Type v) (D : Type w) [Ring A] [Algebra K A] [DivisionRing D]
    [Algebra K D] [Algebra.IsCentral K D] (I : TwoSidedIdeal (A ⊗[K] D)) :
    (I : Set (A ⊗[K] D)) =
      Submodule.span K {x | ∃ (a : A) (δ : D), a ⊗ₜ[K] (1 : D) ∈ I ∧ x = a ⊗ₜ[K] δ} :=
  twoSidedIdeal_eq_span_of_isCentral A D I

/-- Proposition 2.6 of Milne, case "the second factor is central": the tensor product of a
simple $K$-algebra and a central simple $K$-algebra is simple (no finite dimension needed). -/
theorem isSimpleRing_tensorProduct_of_isCentral_right (A : Type v) (B : Type w) [Ring A]
    [Algebra K A] [IsSimpleRing A] [Ring B] [Algebra K B] [Algebra.IsCentral K B]
    [IsSimpleRing B] : IsSimpleRing (A ⊗[K] B) := by
  classical
  have hinj : Function.Injective (algebraMap K B) := (algebraMap K B).injective
  have : Nontrivial (A ⊗[K] B) :=
    (Algebra.TensorProduct.includeLeft_injective (S := K) (R := K) (A := A) (B := B)
      hinj).nontrivial
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  have hmul : ∀ x y : A, (x * y) ⊗ₜ[K] (1 : B) = (x ⊗ₜ[K] (1 : B)) * (y ⊗ₜ[K] (1 : B)) := by
    intro x y; simp [Algebra.TensorProduct.tmul_mul_tmul]
  obtain ⟨𝔞, h𝔞⟩ : ∃ 𝔞 : TwoSidedIdeal A, ∀ a, a ∈ 𝔞 ↔ a ⊗ₜ[K] (1 : B) ∈ I := by
    refine ⟨TwoSidedIdeal.mk' {a | a ⊗ₜ[K] (1 : B) ∈ I} ?_ ?_ ?_ ?_ ?_, fun a => ?_⟩
    · show (0 : A) ⊗ₜ[K] (1 : B) ∈ I
      rw [TensorProduct.zero_tmul]; exact I.zero_mem
    · intro x y hx hy
      show (x + y) ⊗ₜ[K] (1 : B) ∈ I
      rw [TensorProduct.add_tmul]; exact I.add_mem hx hy
    · intro x hx
      show (-x) ⊗ₜ[K] (1 : B) ∈ I
      rw [TensorProduct.neg_tmul]; exact I.neg_mem hx
    · intro x y hy
      show (x * y) ⊗ₜ[K] (1 : B) ∈ I
      rw [hmul]; exact I.mul_mem_left _ _ hy
    · intro x y hx
      show (x * y) ⊗ₜ[K] (1 : B) ∈ I
      rw [hmul]; exact I.mul_mem_right _ _ hx
    · rw [TwoSidedIdeal.mem_mk']; rfl
  rcases eq_bot_or_eq_top 𝔞 with h | h
  · left
    have hI := twoSidedIdeal_eq_span_of_isCentral A B I
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ (I : Set (A ⊗[K] B)) := hx
    rw [hI] at hx'
    have hle : Submodule.span K {x | ∃ (a : A) (b : B), a ⊗ₜ[K] (1 : B) ∈ I ∧ x = a ⊗ₜ[K] b}
        ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro _ ⟨a, b, ha, rfl⟩
      have h1 : a ∈ 𝔞 := (h𝔞 a).mpr ha
      rw [h, TwoSidedIdeal.mem_bot] at h1
      subst h1
      simp
    have := Submodule.mem_bot K |>.mp (hle hx')
    rw [TwoSidedIdeal.mem_bot]
    exact this
  · right
    have h1 : (1 : A) ∈ 𝔞 := by rw [h]; trivial
    have h2 := (h𝔞 1).mp h1
    rw [← Algebra.TensorProduct.one_def] at h2
    exact TwoSidedIdeal.eq_top I h2

/-- Proposition 2.6 of Milne: the tensor product of two simple $K$-algebras, at least one of
which is central, is simple.  No finite dimension is needed. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 2.6, p. 128"]
theorem prop_2_6 (A : Type v) (B : Type w) [Ring A] [Algebra K A] [IsSimpleRing A] [Ring B]
    [Algebra K B] [IsSimpleRing B] (h : Algebra.IsCentral K A ∨ Algebra.IsCentral K B) :
    IsSimpleRing (A ⊗[K] B) := by
  rcases h with h | h
  · have := h
    exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm K B A).toRingEquiv
      (isSimpleRing_tensorProduct_of_isCentral_right (K := K) B A)
  · have := h
    exact isSimpleRing_tensorProduct_of_isCentral_right A B

/-- Corollary 2.8 of Milne: the tensor product of two central simple $K$-algebras is central
simple (no finite dimension needed). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 2.8, p. 128"]
theorem cor_2_8 (A : Type v) (B : Type w) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B] :
    Algebra.IsCentral K (A ⊗[K] B) ∧ IsSimpleRing (A ⊗[K] B) := by
  refine ⟨⟨fun z hz => ?_⟩, prop_2_6 A B (Or.inl inferInstance)⟩
  rw [center_tensorProduct] at hz
  obtain ⟨t, rfl⟩ : ∃ t, Algebra.TensorProduct.map (Subalgebra.center K A).val
      (Subalgebra.center K B).val t = z := hz
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out a.2)
    obtain ⟨s, hs⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out b.2)
    rw [Algebra.mem_bot]
    refine ⟨r * s, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, Subalgebra.coe_val]
    have h1 : ∀ c : K, algebraMap K A c ⊗ₜ[K] (1 : B) = algebraMap K (A ⊗[K] B) c :=
      fun c => (Algebra.TensorProduct.algebraMap_apply c).symm
    rw [← hr, ← hs, Algebra.algebraMap_eq_smul_one (A := B), TensorProduct.tmul_smul, h1,
      Algebra.smul_def, ← map_mul, mul_comm]
  | add x y hx hy =>
    rw [map_add]
    exact Subalgebra.add_mem _ hx hy

instance isCentral_tensorProduct (A : Type v) (B : Type w) [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [Ring B] [Algebra K B] [Algebra.IsCentral K B]
    [IsSimpleRing B] : Algebra.IsCentral K (A ⊗[K] B) :=
  (cor_2_8 A B).1

instance isSimpleRing_tensorProduct (A : Type v) (B : Type w) [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [Ring B] [Algebra K B] [Algebra.IsCentral K B]
    [IsSimpleRing B] : IsSimpleRing (A ⊗[K] B) :=
  (cor_2_8 A B).2

/-- Corollary 2.9 of Milne: for a central simple $K$-algebra $A$ of finite dimension $n$, the
map $a \otimes a' \mapsto (v \mapsto a v a')$ is an isomorphism
$A \otimes_K A^{\mathrm{opp}} \to \mathrm{End}_K(A)$, and $\mathrm{End}_K(A) \cong M_n(K)$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 2.9, p. 129"]
theorem cor_2_9 (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] :
    Function.Bijective (AlgHom.mulLeftRight K A) ∧
      Nonempty (A ⊗[K] Aᵐᵒᵖ ≃ₐ[K]
        Matrix (Fin (Module.finrank K A)) (Fin (Module.finrank K A)) K) := by
  classical
  have hinj : Function.Injective (AlgHom.mulLeftRight K A) :=
    RingHom.injective (AlgHom.mulLeftRight K A).toRingHom
  have hdim : Module.finrank K (A ⊗[K] Aᵐᵒᵖ) = Module.finrank K (Module.End K A) := by
    rw [Module.finrank_tensorProduct, Module.finrank_linearMap,
      (MulOpposite.opLinearEquiv K (M := A)).finrank_eq]
  have hbij : Function.Bijective (AlgHom.mulLeftRight K A) := by
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (AlgHom.mulLeftRight K A).toLinearMap)).mp hinj
    exact ⟨hinj, this⟩
  exact ⟨hbij, ⟨(AlgEquiv.ofBijective _ hbij).trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K A))⟩⟩

/-- A finite-dimensional central simple algebra over a field is an Azumaya algebra (this is
Corollary 2.9 in Mathlib's language). -/
theorem isAzumaya_of_isCentral (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] : IsAzumaya K A :=
  { bij := (cor_2_9 A).1 }

/-! ### Extension of the base field -/

/-- Proposition 2.15 of Milne: for a central simple $K$-algebra $A$ and a field $L \supseteq K$
(not necessarily of finite degree), $L \otimes_K A$ is a central simple $L$-algebra.
(Milne writes $A \otimes_k L$; see the module docstring.) -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 2.15, p. 131"]
theorem prop_2_15 (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    (L : Type w) [Field L] [Algebra K L] :
    Algebra.IsCentral L (L ⊗[K] A) ∧ IsSimpleRing (L ⊗[K] A) := by
  refine ⟨⟨fun z hz => ?_⟩, isSimpleRing_tensorProduct_of_isCentral_right (K := K) L A⟩
  have hz' : z ∈ Subalgebra.centralizer K
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).range := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g ⟨a, rfl⟩
    exact (Subalgebra.mem_center_iff.mp hz _)
  clear hz
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct] at hz'
  obtain ⟨t, rfl⟩ : ∃ t, Algebra.TensorProduct.map (AlgHom.id K L)
      (Subalgebra.center K A).val t = z := hz'
  induction t using TensorProduct.inductionOn with
  | tmul l a =>
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out a.2)
    rw [Algebra.mem_bot]
    refine ⟨algebraMap K L r * l, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, Subalgebra.coe_val, AlgHom.id_apply]
    rw [← hr, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := A),
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    simp
  | add x y hx hy =>
    rw [map_add]
    exact Subalgebra.add_mem _ hx hy

/-- Corollary 2.16 of Milne: the dimension of a (finite-dimensional) central simple $K$-algebra
is a square. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 2.16, p. 131"]
theorem cor_2_16 (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] : ∃ n : ℕ, Module.finrank K A = n ^ 2 := by
  classical
  obtain ⟨hc, hs⟩ := prop_2_15 (K := K) A (AlgebraicClosure K)
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
    (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
  refine ⟨n, ?_⟩
  have h1 := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_matrix, Fintype.card_fin] at h1
  rw [h1]; simp [sq]

end NumberFieldKB.MilneCFT.Ch4
