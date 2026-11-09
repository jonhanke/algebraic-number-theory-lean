import NumberFieldKB.MilneCFT.Ch8.QuaternionIso
import NumberFieldKB.MilneCFT.Ch8.Example44
import QuadFormsKB.Tamagawa.FormClassNF
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationGeneralNF
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF
import QuadFormsKB.Binary.RelGenusHilbert

/-!
# Milne, *Class Field Theory*, Chapter VIII, Example 4.4(b): the ramification set determines $H(a,b)$

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §4, Example 4.4
(pdf p. 250, printed p. 241): "The family $(i_v)$ determines the isomorphism class of $D$ [...] For example, to give a
quaternion algebra over $\mathbb Q$ is the same as to give a set of primes of $\mathbb Q$ having an even finite number
of elements."

For a quaternion algebra $H(a,b) = (a,b)_F$ over a number field $F$, $i_v \in \{0, \tfrac12\}$ and $i_v = \tfrac12$ iff
$v \in \mathrm{Ram}(a,b)$ (the places where $H(a,b) \otimes F_v$ is a division algebra, QuadFormsKB
`Quat.IsRamifiedAt`). Here, for $a, b, c, d \in F^\times$:

* `example_4_4b_algEquiv_iff_ramified`: $H(c,d) \cong H(a,b)$ as $F$-algebras iff
  $\mathrm{Ram}(a,b) = \mathrm{Ram}(c,d)$;
* `example_4_4b_rat`: over $\mathbb Q$, every finite set of places of even cardinality is $\mathrm{Ram}(a,b)$ for some
  $a, b$, and $\mathrm{Ram}$ determines the algebra up to isomorphism (Milne's last sentence).

*Proof.* $(a,b)_F$ and $(c,d)_F$ are isomorphic iff their pure norm forms $\langle -a,-b,ab\rangle$ and
$\langle -c,-d,cd\rangle$ are isometric (`Ch8.nonempty_algEquiv_of_pureForm_isometric`,
`Ch8.pureForm_isometric_of_algEquiv`). Both have square determinant; Serre's Hasse invariant is
$\varepsilon_v\langle -a,-b,ab\rangle = (-1,-1)_v(a,b)_v$ (`hasseSerre_pure`); at a real place the negative index is
$0$ if $a, b < 0$ and $2$ otherwise (`realNegCount_pure`). By the local classification (QuadFormsKB
`NFPlace.isometric_iff`) the pure forms are isometric over $F_v$ iff $(a,b)_v = (c,d)_v$, and by the Hasse–Minkowski
theorem over number fields (QuadFormsKB `Tamagawa.FormClassNF.isometricIn_of_everywhere_nf`) everywhere-local isometry
gives global isometry. No class field theory is used (Milne's route is the Brauer group; Tau Ceti has the general
Brauer-group statement, `TauCeti.ClassFieldTheory.brLocalization_injective`, see the coverage page).
-/

open NumberField IsDedekindDomain QuadFormsKB Quaternion

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {F : Type} [Field F] [NumberField F]

/-- A local Hilbert symbol is a unit $\pm 1$: its square is $1$. -/
theorem hilbert_mul_self (v : NFPlace F) (a b : F) : v.hilbert a b * v.hilbert a b = 1 := by
  rcases NFPlace.hilbert_eq_one_or v a b with h | h <;> rw [h] <;> norm_num

/-- **Serre's Hasse invariant of the pure norm form:** $\varepsilon_v\langle -a,-b,ab\rangle = (-1,-1)_v (a,b)_v$. -/
theorem hasseSerre_pure (v : NFPlace F) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    v.hasseSerre ![-a, -b, a * b] = v.hilbert (-1) (-1) * v.hilbert a b := by
  have h1 : (-1 : F) ≠ 0 := by norm_num
  have e1 : v.hilbert (-a) (-b) =
      v.hilbert (-1) (-1) * v.hilbert (-1) b * (v.hilbert a (-1) * v.hilbert a b) := by
    rw [show -a = -1 * a by ring, show -b = -1 * b by ring, NFPlace.hilbert_mul_left v h1 ha (by simpa using hb),
      NFPlace.hilbert_mul_right v h1 h1 hb, NFPlace.hilbert_mul_right v ha h1 hb]
  have e2 : v.hilbert (-a) (a * b) =
      v.hilbert (-1) a * v.hilbert (-1) b * (v.hilbert a (-1) * v.hilbert a b) := by
    rw [show -a = -1 * a by ring, NFPlace.hilbert_mul_left v h1 ha (mul_ne_zero ha hb),
      NFPlace.hilbert_mul_right v h1 ha hb, NFPlace.hilbert_mul_right v ha ha hb, NFPlace.hilbert_self v ha]
  have e3 : v.hilbert (-b) (a * b) =
      v.hilbert (-1) a * v.hilbert (-1) b * (v.hilbert a b * v.hilbert b (-1)) := by
    rw [show -b = -1 * b by ring, NFPlace.hilbert_mul_left v h1 hb (mul_ne_zero ha hb),
      NFPlace.hilbert_mul_right v h1 ha hb, NFPlace.hilbert_mul_right v hb ha hb, NFPlace.hilbert_self v hb,
      NFPlace.hilbert_comm v b a]
  have hs : v.hasseSerre ![-a, -b, a * b] =
      v.hilbert (-a) (-b) * v.hilbert (-a) (a * b) * v.hilbert (-b) (a * b) := by
    simp [NFPlace.hasseSerre, Fin.prod_univ_three]
  rw [hs, e1, e2, e3, NFPlace.hilbert_comm v (-1) a, NFPlace.hilbert_comm v (-1) b]
  rcases NFPlace.hilbert_eq_one_or v a (-1) with h₁ | h₁ <;>
    rcases NFPlace.hilbert_eq_one_or v b (-1) with h₂ | h₂ <;>
    rcases NFPlace.hilbert_eq_one_or v a b with h₃ | h₃ <;>
    simp only [h₁, h₂, h₃] <;> ring

/-- **The negative index of the pure norm form at a real place:** under the real embedding $\sigma$ of $w$,
$\langle -a,-b,ab\rangle$ has $0$ negative entries if $\sigma(a), \sigma(b) < 0$ and $2$ otherwise. -/
theorem realNegCount_pure (w : InfinitePlace F) (hw : w.IsReal) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    LocalClassNF.realNegCount w hw ![-a, -b, a * b] =
      if w.embedding_of_isReal hw a < 0 ∧ w.embedding_of_isReal hw b < 0 then 0 else 2 := by
  have hs : w.embedding_of_isReal hw a ≠ 0 := (map_ne_zero _).mpr ha
  have ht : w.embedding_of_isReal hw b ≠ 0 := (map_ne_zero _).mpr hb
  rw [LocalClassNF.realNegCount, Finset.card_filter, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_neg, map_mul]
  rcases hs.lt_or_gt with h1 | h1 <;> rcases ht.lt_or_gt with h2 | h2
  · have : 0 < w.embedding_of_isReal hw a * w.embedding_of_isReal hw b := mul_pos_of_neg_of_neg h1 h2
    simp [h1, h2, not_lt.mpr this.le, not_lt.mpr (neg_pos.mpr h1).le, not_lt.mpr (neg_pos.mpr h2).le]
  · have : w.embedding_of_isReal hw a * w.embedding_of_isReal hw b < 0 := mul_neg_of_neg_of_pos h1 h2
    simp [h1, h2, this, not_lt.mpr (neg_pos.mpr h1).le, not_lt.mpr h2.le]
  · have : w.embedding_of_isReal hw a * w.embedding_of_isReal hw b < 0 := mul_neg_of_pos_of_neg h1 h2
    simp [h1, h2, this, not_lt.mpr (neg_pos.mpr h2).le, not_lt.mpr h1.le]
  · have : 0 < w.embedding_of_isReal hw a * w.embedding_of_isReal hw b := mul_pos h1 h2
    simp [h1, h2, not_lt.mpr this.le, not_lt.mpr h1.le]

/-- **The Hilbert symbol at a real place** in terms of the real embedding $\sigma$: $(a,b)_w = -1$ iff
$\sigma(a), \sigma(b) < 0$. -/
theorem hilbert_real_eq (w : InfinitePlace F) (hw : w.IsReal) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (NFPlace.infinite w).hilbert a b =
      if w.embedding_of_isReal hw a < 0 ∧ w.embedding_of_isReal hw b < 0 then -1 else 1 := by
  let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hφ : ∀ x : F, φ (algebraMap F w.Completion x) = w.embedding_of_isReal hw x := fun x => by simp [φ]
  rw [NFPlace.hilbert, ← HasseIsoNF.hilbertSymbol_ringEquiv φ, hφ, hφ]
  exact HasseIsoNF.hilbertSymbol_real_eq _ _ ((map_ne_zero _).mpr ha) ((map_ne_zero _).mpr hb)

/-- **Local isometry of pure norm forms from equal Hilbert symbols:** if $(a,b)_v = (c,d)_v$, then
$\langle -a,-b,ab\rangle \cong \langle -c,-d,cd\rangle$ over $F_v$. -/
theorem atPlace_pureForm_isometric (v : NFPlace F) {a b c d : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (h : v.hilbert a b = v.hilbert c d) :
    v.atPlace fun K _ _ => (Quat.pureForm a b).IsometricIn K (Quat.pureForm c d) := by
  have hne : ∀ x y : F, x ≠ 0 → y ≠ 0 → ∀ i, (![-x, -y, x * y] : Fin 3 → F) i ≠ 0 := by
    intro x y hx hy i
    fin_cases i <;> simp [hx, hy]
  have key := (NFPlace.isometric_iff v ![-a, -b, a * b] ![-c, -d, c * d] (hne a b ha hb) (hne c d hc hd)).mpr
  refine key ⟨?_, ?_, ?_⟩
  · have hsq : (∏ i, (![-a, -b, a * b] : Fin 3 → F) i) / ∏ i, (![-c, -d, c * d] : Fin 3 → F) i =
        (a * b / (c * d)) * (a * b / (c * d)) := by
      simp [Fin.prod_univ_three]
      field_simp
    cases v <;>
    · simp only [NFPlace.atPlace]
      rw [hsq, map_mul]
      exact ⟨_, rfl⟩
  · rw [hasseSerre_pure v ha hb, hasseSerre_pure v hc hd, h]
  · cases v with
    | finite v => rfl
    | infinite w =>
      simp only [NFPlace.negIndex]
      split_ifs with hw
      · rw [realNegCount_pure w hw ha hb, realNegCount_pure w hw hc hd]
        rw [hilbert_real_eq w hw ha hb, hilbert_real_eq w hw hc hd] at h
        split_ifs at h ⊢ <;> first | rfl | norm_num at h
      · rfl

/-- The Hilbert symbols agree at $v$ iff the ramification of $(a,b)$ and $(c,d)$ at $v$ agrees. -/
theorem hilbert_eq_iff_isRamifiedAt (v : NFPlace F) {a b c d : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) :
    v.hilbert a b = v.hilbert c d ↔ (Quat.IsRamifiedAt a b v ↔ Quat.IsRamifiedAt c d v) := by
  rw [Quat.isRamifiedAt_iff ha hb, Quat.isRamifiedAt_iff hc hd]
  rcases NFPlace.hilbert_eq_one_or v a b with h₁ | h₁ <;>
    rcases NFPlace.hilbert_eq_one_or v c d with h₂ | h₂ <;> simp [h₁, h₂]

/-- **Example 4.4(b), quaternion algebras: the ramification set determines the algebra** (Milne, *CFT*, VIII,
Example 4.4, p. 241: "the family $(i_v)$ determines the isomorphism class of $D$"): for $a, b, c, d \in F^\times$ over
a number field $F$, if $H(a,b)$ and $H(c,d)$ ramify at the same places then $H(c,d) \cong H(a,b)$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Example 4.4(b), quaternion case: the invariants determine the algebra, p. 241"]
theorem example_4_4b_algEquiv_of_ramified_eq {a b c d : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : {v : NFPlace F | Quat.IsRamifiedAt a b v} = {v : NFPlace F | Quat.IsRamifiedAt c d v}) :
    Nonempty (ℍ[F,c,d] ≃ₐ[F] ℍ[F,a,b]) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hloc : ∀ v : NFPlace F, v.hilbert a b = v.hilbert c d := fun v =>
    (hilbert_eq_iff_isRamifiedAt v ha hb hc hd).mpr (Set.ext_iff.mp h v)
  have hglob := Tamagawa.FormClassNF.isometricIn_of_everywhere_nf (Quat.pureForm a b) (Quat.pureForm c d)
    (Quat.pureForm_nondegenerate h2 ha hb) (Quat.pureForm_nondegenerate h2 hc hd)
    (fun v => atPlace_pureForm_isometric v ha hb hc hd (hloc v))
  exact nonempty_algEquiv_of_pureForm_isometric h2 ha hb hc hd hglob

/-- **Isomorphic quaternion algebras ramify at the same places** (the converse of
`example_4_4b_algEquiv_of_ramified_eq`). -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Example 4.4(b), quaternion case, p. 241"]
theorem example_4_4b_ramified_eq_of_algEquiv {a b c d : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (e : ℍ[F,c,d] ≃ₐ[F] ℍ[F,a,b]) :
    {v : NFPlace F | Quat.IsRamifiedAt a b v} = {v : NFPlace F | Quat.IsRamifiedAt c d v} := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hglob := pureForm_isometric_of_algEquiv h2 ha hb hc hd e
  ext v
  refine (hilbert_eq_iff_isRamifiedAt v ha hb hc hd).mp ?_
  have hne : ∀ x y : F, x ≠ 0 → y ≠ 0 → ∀ i, (![-x, -y, x * y] : Fin 3 → F) i ≠ 0 := by
    intro x y hx hy i
    fin_cases i <;> simp [hx, hy]
  have hv := LocalClassNF.atPlace_isometricIn_of_base v hglob
  obtain ⟨-, hS, -⟩ := (NFPlace.isometric_iff v ![-a, -b, a * b] ![-c, -d, c * d] (hne a b ha hb)
    (hne c d hc hd)).mp hv
  rw [hasseSerre_pure v ha hb, hasseSerre_pure v hc hd] at hS
  have hu := hilbert_mul_self v (-1) (-1)
  calc v.hilbert a b = v.hilbert (-1) (-1) * (v.hilbert (-1) (-1) * v.hilbert a b) := by
        rw [← mul_assoc, hu, one_mul]
    _ = v.hilbert c d := by rw [hS, ← mul_assoc, hu, one_mul]

/-- **Example 4.4(b), quaternion algebras: classification by the ramification set** (Milne, *CFT*, VIII, Example 4.4,
p. 241): over a number field, $H(c,d) \cong H(a,b)$ iff $\mathrm{Ram}(a,b) = \mathrm{Ram}(c,d)$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Example 4.4(b), quaternion case: classification by Ram, p. 241"]
theorem example_4_4b_algEquiv_iff_ramified {a b c d : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    Nonempty (ℍ[F,c,d] ≃ₐ[F] ℍ[F,a,b]) ↔
      {v : NFPlace F | Quat.IsRamifiedAt a b v} = {v : NFPlace F | Quat.IsRamifiedAt c d v} :=
  ⟨fun ⟨e⟩ => example_4_4b_ramified_eq_of_algEquiv ha hb hc hd e,
    example_4_4b_algEquiv_of_ramified_eq ha hb hc hd⟩

/-- **Example 4.4(b) over $\mathbb Q$** (Milne, *CFT*, VIII, Example 4.4, p. 241: "to give a quaternion algebra over
$\mathbb Q$ is the same as to give a set of primes of $\mathbb Q$ having an even finite number of elements"): the
ramification set of $H(a,b)$, $a, b \in \mathbb Q^\times$, is a finite set of places of even cardinality; every such
set occurs; and two quaternion algebras $H(a,b)$, $H(c,d)$ are isomorphic iff they have the same ramification set.
("Primes" includes the real place, as in Milne's convention for $\sum_v i_v = 0$.) -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Example 4.4(b), quaternion algebras over Q, p. 241"]
theorem example_4_4b_rat :
    (∀ a b : ℚ, a ≠ 0 → b ≠ 0 →
      {v : NFPlace ℚ | Quat.IsRamifiedAt a b v}.Finite ∧ Even {v : NFPlace ℚ | Quat.IsRamifiedAt a b v}.ncard) ∧
    (∀ T : Set (NFPlace ℚ), T.Finite → Even T.ncard →
      ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧ {v : NFPlace ℚ | Quat.IsRamifiedAt a b v} = T) ∧
    (∀ a b c d : ℚ, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
      (Nonempty (ℍ[ℚ,c,d] ≃ₐ[ℚ] ℍ[ℚ,a,b]) ↔
        {v : NFPlace ℚ | Quat.IsRamifiedAt a b v} = {v : NFPlace ℚ | Quat.IsRamifiedAt c d v})) :=
  ⟨fun _ _ ha hb => example_4_4b_ramified_finite_even ha hb, example_4_4b_exists_ramified,
    fun _ _ _ _ ha hb hc hd => example_4_4b_algEquiv_iff_ramified ha hb hc hd⟩

end NumberFieldKB.MilneCFT.Ch8
