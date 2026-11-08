import NumberFieldKB.MilneCFT.Ch8.QuadraticForms
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationGeneralNF

/-!
# Milne, *CFT*, VIII, Theorem 6.12 (O'Meara 72:1): existence of a global form with prescribed local forms

Proof of `Theorem6_12`, unconditionally, from QuadFormsKB's local classification, Hilbert reciprocity, the
prescribed-Hilbert-symbol theorem (`NFInputs.exists_prescribed_hilbert_nf`) and Mathlib's weak approximation.

**Necessity** (`necessity`): diagonalize the global form (`diagOf`); at each place the local forms are isometric
to its image, so the discriminants agree with `d₀ = ∏ cᵢ` modulo squares, Hasse's `S_v` is an isometry invariant
(`GoodK.hasseS_inv`, via `hasseVec_eq_of_isometric` at finite places, Sylvester's law at real places, triviality at
complex places), and the product formula for `S_v` of the global diagonal form (`NFPlace.hasseOMeara_product_formula`)
gives finiteness and `∏ S_v = 1` (the split of the product over all places is `finprod_nfplace`).

**Sufficiency** (`suff`): induction on `n`, splitting off one global coefficient `x` (`reduce`). If `x` is
represented by every local form, then locally `f_v ≅ ⟨x⟩ ⊥ g_v` (`split_local`); the data `(g_v)` has discriminant
`d₀ x` and Hasse invariants `S(g_v) = S(f_v)(x,d₀)_v`, so the hypotheses persist by Hilbert reciprocity. The
existence of `x` (`ExistsX`) depends on the rank:
* rank 1: `x = d₀` (`existsX_zero`);
* rank 2: `x` with prescribed symbols `(x,-d₀)_v = S_v (d₀,-1)_v` at all places, from the prescribed-symbol
  theorem; the parity condition is the product formula (`existsX_one`, `rank2_sym`, `rep2_inf`);
* rank `≥ 3`: all but finitely many finite places have universal local forms (rank `≥ 4`, or rank `3` with
  `S_v = (-1,-1)_v = 1`, `rank3_good`); at the finitely many bad places and at all infinite places choose `x`
  in the square class of the first coefficient by weak approximation (`weak_approx`), which is then represented
  (`existsX_ge2`).
-/

open NumberField IsDedekindDomain QuadFormsKB PadicClass

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8
namespace T612

/-- The properties of a completion `K` used below: the Hilbert symbol is multiplicative in the first
variable and the invariant `hasseVec` is an isometry invariant of nondegenerate diagonal forms. -/
structure GoodK (K : Type) [Field K] [CharZero K] : Prop where
  mul_left : ∀ a a' b : K, a ≠ 0 → a' ≠ 0 → b ≠ 0 →
    hilbertSymbol K (a * a') b = hilbertSymbol K a b * hilbertSymbol K a' b
  inv : ∀ (n : ℕ) (a b : Fin n → K), (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) →
    (QuadForm.diag a).IsometricIn K (QuadForm.diag b) → hasseVec a = hasseVec b

variable {F : Type} [Field F] [NumberField F]

theorem goodK_finite (v : HeightOneSpectrum (𝓞 F)) : GoodK (v.adicCompletion F) :=
  ⟨(HasseIsoNF.localHilbertField_adicCompletion v).mul_left,
    fun n a b ha hb h => hasseVec_eq_of_isometric (HasseIsoNF.localHilbertField_adicCompletion v) n a b ha hb h⟩

instance charZero_completion (w : InfinitePlace F) : CharZero w.Completion :=
  charZero_of_injective_algebraMap (algebraMap F _).injective

theorem goodK_infinite (w : InfinitePlace F) : GoodK w.Completion := by
  refine ⟨NFLocal.hilbertSymbol_mul_left_infinite_nf w, fun n a b ha hb h => ?_⟩
  rcases w.isReal_or_isComplex with hw | hw
  · let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    rw [← HasseIsoNF.hasseVec_ringEquiv φ, ← HasseIsoNF.hasseVec_ringEquiv φ b]
    exact HasseIsoNF.hasseVec_real_isometric _ _ (fun i => (map_ne_zero _).mpr (ha i))
      (fun i => (map_ne_zero _).mpr (hb i)) (HasseIsoNF.isometricIn_ringEquiv φ h)
  · simp [hasseVec, HasseIsoNF.hilbertSymbol_complex_place hw]

/-! ### Generic lemmas on a field with `GoodK` -/

section Generic

variable {K : Type} [Field K] [CharZero K] (hK : GoodK K)
include hK

theorem GoodK.mul_right' {a b b' : K} (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSymbol K a (b * b') = hilbertSymbol K a b * hilbertSymbol K a b' := by
  rw [hilbertSymbol_comm, hK.mul_left _ _ _ hb hb' ha, hilbertSymbol_comm K b,
    hilbertSymbol_comm K b']

theorem GoodK.self' {a : K} (ha : a ≠ 0) : hilbertSymbol K a a = hilbertSymbol K a (-1) := by
  have h := hilbertSymbol_self_neg K a
  rw [show -a = -1 * a by ring, hK.mul_right' ha (by norm_num) ha] at h
  rcases hs_pm a (-1 : K) with h1 | h1 <;> rw [h1] at h ⊢ <;> linarith

theorem GoodK.prod_left {ι : Type*} (s : Finset ι) (a : ι → K) (ha : ∀ i ∈ s, a i ≠ 0) {b : K}
    (hb : b ≠ 0) : hilbertSymbol K (∏ i ∈ s, a i) b = ∏ i ∈ s, hilbertSymbol K (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hs_one_left]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj,
      hK.mul_left _ _ _ (ha j (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun i hi => ha i (Finset.mem_insert_of_mem hi)) hb,
      ih fun i hi => ha i (Finset.mem_insert_of_mem hi)]

theorem GoodK.prod_right {ι : Type*} (s : Finset ι) (a : ι → K) (ha : ∀ i ∈ s, a i ≠ 0) {b : K}
    (hb : b ≠ 0) : hilbertSymbol K b (∏ i ∈ s, a i) = ∏ i ∈ s, hilbertSymbol K b (a i) := by
  rw [hilbertSymbol_comm, hK.prod_left s a ha hb]
  exact Finset.prod_congr rfl fun i _ => hilbertSymbol_comm _ _ _

theorem GoodK.prod_self {n : ℕ} {a : Fin n → K} (ha : ∀ i, a i ≠ 0) :
    ∏ i, hilbertSymbol K (a i) (a i) = hilbertSymbol K (∏ i, a i) (∏ i, a i) := by
  have hD : ∏ i, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  rw [hK.self' hD, hK.prod_left Finset.univ a (fun i _ => ha i) (by norm_num)]
  exact Finset.prod_congr rfl fun i _ => hK.self' (ha i)

/-- `hasseS` is `hasseVec` times the correction `(d, d)`. -/
theorem GoodK.hasseS_eq {n : ℕ} {a : Fin n → K} (ha : ∀ i, a i ≠ 0) :
    hasseS K a = hasseVec a * hilbertSymbol K (∏ i, a i) (∏ i, a i) := by
  unfold hasseS hasseVec
  rw [QuadFormsKB.prod_ite_le_eq (fun i j => hilbertSymbol K (a i) (a j)), hK.prod_self ha]

theorem GoodK.hasseS_cons {n : ℕ} {x : K} (hx : x ≠ 0) {a : Fin n → K} (ha : ∀ i, a i ≠ 0) :
    hasseS K (Fin.cons x a : Fin (n + 1) → K) =
      hilbertSymbol K x (x * ∏ i, a i) * hasseS K a := by
  have h0 : hasseS K (Fin.cons x a : Fin (n + 1) → K) =
      hilbertSymbol K x x * (∏ j, hilbertSymbol K x (a j)) * hasseS K a := by
    unfold hasseS
    rw [Fin.prod_univ_succ]
    congr 1
    · rw [Fin.prod_univ_succ]; simp
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [Fin.prod_univ_succ]
      simp [Fin.succ_le_succ_iff, Fin.succ_ne_zero]
  rw [h0, hK.mul_right' hx hx (Finset.prod_ne_zero_iff.mpr fun i _ => ha i),
    hK.prod_right Finset.univ a (fun i _ => ha i) hx]

/-- `hasseS` is invariant under isometry of nondegenerate diagonal forms over `K`. -/
theorem GoodK.hasseS_inv {n : ℕ} {a b : Fin n → K} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) : hasseS K a = hasseS K b := by
  obtain ⟨t, ht, hd⟩ := disc_of_isometric h
  rw [hK.hasseS_eq ha, hK.hasseS_eq hb, hK.inv n a b ha hb h, hd, hs_sq_left _ _ _ ht,
    hs_sq_right _ _ _ ht]

end Generic

/-! ### Products over all places -/

section Places

theorem finite_part_finite (s : NFPlace F → ℤ) (hs : Function.HasFiniteMulSupport s) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => s (NFPlace.finite v)).Finite := by
  refine (Set.Finite.preimage (f := fun v : HeightOneSpectrum (𝓞 F) => (NFPlace.finite v : NFPlace F))
    (fun x _ y _ h => NFPlace.finite.inj h) hs).subset ?_
  intro v hv
  exact hv

/-- A product over all places splits into finite and infinite places. -/
theorem finprod_nfplace (s : NFPlace F → ℤ) (hs : Function.HasFiniteMulSupport s) :
    ∏ᶠ v : NFPlace F, s v =
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), s (NFPlace.finite v)) * ∏ w : InfinitePlace F, s (NFPlace.infinite w) := by
  classical
  have hfin := finite_part_finite s hs
  set T : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset
  set U : Finset (NFPlace F) := T.map ⟨NFPlace.finite, fun x y h => NFPlace.finite.inj h⟩ ∪
    Finset.univ.map ⟨NFPlace.infinite, fun x y h => by cases h; rfl⟩
  rw [finprod_eq_prod_of_mulSupport_subset s (s := U), finprod_eq_prod_of_mulSupport_subset
    (fun v : HeightOneSpectrum (𝓞 F) => s (NFPlace.finite v)) (s := T)]
  · rw [Finset.prod_union, Finset.prod_map, Finset.prod_map]
    · rfl
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx hx'
      obtain ⟨_, _, rfl⟩ := hx
      obtain ⟨_, _, h⟩ := hx'
      cases h
  · intro v hv
    simpa [T] using hv
  · intro v hv
    cases v with
    | finite v =>
      rw [Finset.mem_coe, Finset.mem_union]
      left
      rw [Finset.mem_map]
      exact ⟨v, by simpa [T] using hv, rfl⟩
    | infinite w =>
      rw [Finset.mem_coe, Finset.mem_union]
      right
      rw [Finset.mem_map]
      exact ⟨w, Finset.mem_univ _, rfl⟩

end Places

/-! ### The hypotheses (a), (b) of Theorem 6.12, and necessity -/

section Nec

variable (F)

/-- The right-hand side of Theorem 6.12 together with nonvanishing of the entries. -/
structure Hyp (n : ℕ) (d₀ : F) (a : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (b : ∀ w : InfinitePlace F, Fin n → w.Completion) : Prop where
  a_ne : ∀ v i, a v i ≠ 0
  b_ne : ∀ w i, b w i ≠ 0
  d_ne : d₀ ≠ 0
  disc_a : ∀ v, ∃ c : v.adicCompletion F, c ≠ 0 ∧ ∏ i, a v i = algebraMap F _ d₀ * c ^ 2
  disc_b : ∀ w, ∃ c : w.Completion, c ≠ 0 ∧ ∏ i, b w i = algebraMap F _ d₀ * c ^ 2
  fin : {v | hasseS (v.adicCompletion F) (a v) ≠ 1}.Finite
  prod : (∏ᶠ v, hasseS (v.adicCompletion F) (a v)) * ∏ w, hasseS w.Completion (b w) = 1

variable {F}

theorem evalIn_map_self {K : Type} [Field K] [Algebra F K] {n : ℕ} (q : QuadForm F n) (x : Fin n → K) :
    (q.map (algebraMap F K)).evalIn K x = q.evalIn K x := by
  simp [QuadForm.evalIn, QuadForm.map]

theorem isometricIn_map {K : Type} [Field K] [Algebra F K] {n : ℕ} {q q' : QuadForm F n}
    (h : q.IsometricIn K q') :
    (q.map (algebraMap F K)).IsometricIn K (q'.map (algebraMap F K)) := by
  obtain ⟨P, hP, hx⟩ := h
  exact ⟨P, hP, fun x => by rw [evalIn_map_self, evalIn_map_self]; exact hx x⟩

theorem map_diag {K : Type} [Field K] [Algebra F K] {n : ℕ} (c : Fin n → F) :
    (QuadForm.diag c).map (algebraMap F K) = QuadForm.diag (fun i => algebraMap F K (c i)) := by
  ext i j
  simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem local_iso_diagOf {K : Type} [Field K] [Algebra F K] {n : ℕ} {q₀ : QuadForm F n}
    (hq : q₀.Nondegenerate) {R : QuadForm K n} (h : (q₀.map (algebraMap F K)).IsometricIn K R) :
    (QuadForm.diag fun i => algebraMap F K (LocalClassNF.diagOf q₀ i)).IsometricIn K R := by
  have Y := isometricIn_map (K := K) (FieldGen.isometricIn_of_base K (LocalClassNF.isometricIn_diagOf hq))
  rw [map_diag] at Y
  exact QuadForm.isometricIn_trans K (QuadForm.isometricIn_symm K Y) h

theorem local_nec {K : Type} [Field K] [CharZero K] [Algebra F K] (hK : GoodK K) {n : ℕ}
    {c : Fin n → F} (hc : ∀ i, c i ≠ 0) {aK : Fin n → K} (ha : ∀ i, aK i ≠ 0)
    (h : (QuadForm.diag fun i => algebraMap F K (c i)).IsometricIn K (QuadForm.diag aK)) :
    (∃ t : K, t ≠ 0 ∧ ∏ i, aK i = algebraMap F K (∏ i, c i) * t ^ 2) ∧
      hasseS K aK = hasseS K (fun i => algebraMap F K (c i)) := by
  have hc' : ∀ i, algebraMap F K (c i) ≠ 0 := fun i => (map_ne_zero _).mpr (hc i)
  refine ⟨?_, (hK.hasseS_inv hc' ha h).symm⟩
  obtain ⟨t, ht, e⟩ := disc_of_isometric h
  exact ⟨t, ht, by rw [e, map_prod]; ring⟩

theorem necessity {n : ℕ} (a : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (b : ∀ w : InfinitePlace F, Fin n → w.Completion) (ha : ∀ v i, a v i ≠ 0) (hb : ∀ w i, b w i ≠ 0)
    (q₀ : QuadForm F n) (hq : q₀.Nondegenerate)
    (hv : ∀ v, (q₀.map (algebraMap F (v.adicCompletion F))).IsometricIn (v.adicCompletion F)
      (QuadForm.diag (a v)))
    (hw : ∀ w : InfinitePlace F, (q₀.map (algebraMap F w.Completion)).IsometricIn w.Completion
      (QuadForm.diag (b w))) :
    Hyp F n (∏ i, LocalClassNF.diagOf q₀ i) a b := by
  set c := LocalClassNF.diagOf q₀ with hcdef
  have hc : ∀ i, c i ≠ 0 := LocalClassNF.diagOf_ne_zero hq
  have hd : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hc i
  have Lv := fun v : HeightOneSpectrum (𝓞 F) =>
    local_nec (goodK_finite v) hc (ha v) (local_iso_diagOf hq (hv v))
  have Lw := fun w : InfinitePlace F =>
    local_nec (goodK_infinite w) hc (hb w) (local_iso_diagOf hq (hw w))
  obtain ⟨hsf, hsp⟩ := NFPlace.hasseOMeara_product_formula c hc
  have eqv : ∀ v : HeightOneSpectrum (𝓞 F),
      hasseS (v.adicCompletion F) (a v) = (NFPlace.finite v).hasseOMeara c := fun v => (Lv v).2
  have eqw : ∀ w : InfinitePlace F,
      hasseS w.Completion (b w) = (NFPlace.infinite w).hasseOMeara c := fun w => (Lw w).2
  refine ⟨ha, hb, hd, fun v => ?_, fun w => ?_, ?_, ?_⟩
  · obtain ⟨t, ht, e⟩ := (Lv v).1
    exact ⟨t, ht, by rw [e]⟩
  · obtain ⟨t, ht, e⟩ := (Lw w).1
    exact ⟨t, ht, by rw [e]⟩
  · refine (finite_part_finite _ hsf).subset ?_
    intro v hv'
    simpa [Function.mem_mulSupport, eqv v] using hv'
  · simp only [eqv, eqw]
    rw [← finprod_nfplace _ hsf]
    exact hsp

end Nec

/-! ### Splitting off a represented value -/

section Split

theorem split_local {K : Type} [Field K] [CharZero K] (hK : GoodK K) {m : ℕ} {a : Fin (m + 1) → K}
    (ha : ∀ i, a i ≠ 0) {x : K} (hx : x ≠ 0) (hr : (QuadForm.diag a).RepresentsIn K x) :
    ∃ g : Fin m → K, (∀ i, g i ≠ 0) ∧
      (QuadForm.diag a).IsometricIn K (QuadForm.diag (Fin.cons x g : Fin (m + 1) → K)) ∧
      (∃ t : K, t ≠ 0 ∧ x * ∏ i, g i = t ^ 2 * ∏ i, a i) ∧
      ∀ d c : K, d ≠ 0 → c ≠ 0 → ∏ i, a i = d * c ^ 2 →
        hasseS K g = hasseS K a * hilbertSymbol K x d := by
  obtain ⟨g, hg, hiso⟩ := QuadForm.exists_isometric_diag_cons (QuadForm.nondegenerate_diag ha) hx hr
  obtain ⟨t, ht, e⟩ := disc_of_isometric hiso
  rw [Fin.prod_cons] at e
  refine ⟨g, hg, hiso, ⟨t, ht, e⟩, ?_⟩
  intro d c hd hc hdc
  have hca : ∀ i, (Fin.cons x g : Fin (m + 1) → K) i ≠ 0 := by
    intro i
    induction i using Fin.cases with
    | zero => simpa using hx
    | succ i => simpa using hg i
  have h1 := hK.hasseS_inv ha hca hiso
  rw [hK.hasseS_cons hx hg, e, hdc, show t ^ 2 * (d * c ^ 2) = (t * c) ^ 2 * d by ring,
    hs_sq_right _ _ _ (mul_ne_zero ht hc)] at h1
  rcases hs_pm x d with h | h <;> rw [h] at h1 ⊢ <;> linarith

theorem reduce {m : ℕ} {d₀ : F}
    {a : ∀ v : HeightOneSpectrum (𝓞 F), Fin (m + 1) → v.adicCompletion F}
    {b : ∀ w : InfinitePlace F, Fin (m + 1) → w.Completion}
    (H : Hyp F (m + 1) d₀ a b) {x : F} (hx : x ≠ 0)
    (hra : ∀ v : HeightOneSpectrum (𝓞 F),
      (QuadForm.diag (a v)).RepresentsIn (v.adicCompletion F) (algebraMap F _ x))
    (hrb : ∀ w : InfinitePlace F, (QuadForm.diag (b w)).RepresentsIn w.Completion (algebraMap F _ x)) :
    ∃ (g : ∀ v : HeightOneSpectrum (𝓞 F), Fin m → v.adicCompletion F)
      (g' : ∀ w : InfinitePlace F, Fin m → w.Completion),
      Hyp F m (d₀ * x) g g' ∧
      (∀ v, (QuadForm.diag (a v)).IsometricIn (v.adicCompletion F)
        (QuadForm.diag (Fin.cons (algebraMap F _ x) (g v) : Fin (m + 1) → v.adicCompletion F))) ∧
      (∀ w, (QuadForm.diag (b w)).IsometricIn w.Completion
        (QuadForm.diag (Fin.cons (algebraMap F _ x) (g' w) : Fin (m + 1) → w.Completion))) := by
  have hxv : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) x ≠ 0 :=
    fun v => (map_ne_zero _).mpr hx
  have hxw : ∀ w : InfinitePlace F, algebraMap F w.Completion x ≠ 0 :=
    fun w => (map_ne_zero _).mpr hx
  choose g hg0 hgiso hgdisc hgS using fun v : HeightOneSpectrum (𝓞 F) =>
    split_local (goodK_finite v) (H.a_ne v) (hxv v) (hra v)
  choose g' hg'0 hg'iso hg'disc hg'S using fun w : InfinitePlace F =>
    split_local (goodK_infinite w) (H.b_ne w) (hxw w) (hrb w)
  obtain ⟨hsf, hsp⟩ := NFPlace.finprod_hilbert x d₀ hx H.d_ne
  have hd0v : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) d₀ ≠ 0 :=
    fun v => (map_ne_zero _).mpr H.d_ne
  have hd0w : ∀ w : InfinitePlace F, algebraMap F w.Completion d₀ ≠ 0 :=
    fun w => (map_ne_zero _).mpr H.d_ne
  have hSv : ∀ v : HeightOneSpectrum (𝓞 F), hasseS (v.adicCompletion F) (g v) =
      hasseS (v.adicCompletion F) (a v) * (NFPlace.finite v).hilbert x d₀ := by
    intro v
    obtain ⟨c, hc, hcd⟩ := H.disc_a v
    exact hgS v _ c (hd0v v) hc hcd
  have hSw : ∀ w : InfinitePlace F, hasseS w.Completion (g' w) =
      hasseS w.Completion (b w) * (NFPlace.infinite w).hilbert x d₀ := by
    intro w
    obtain ⟨c, hc, hcd⟩ := H.disc_b w
    exact hg'S w _ c (hd0w w) hc hcd
  have hfb := finite_part_finite _ hsf
  refine ⟨g, g', ⟨hg0, hg'0, mul_ne_zero H.d_ne hx, ?_, ?_, ?_, ?_⟩, hgiso, hg'iso⟩
  · intro v
    obtain ⟨c, hc, hcd⟩ := H.disc_a v
    obtain ⟨t, ht, e⟩ := hgdisc v
    rw [hcd] at e
    refine ⟨t * c / algebraMap F _ x, div_ne_zero (mul_ne_zero ht hc) (hxv v), ?_⟩
    have hX := hxv v
    rw [map_mul]
    apply mul_left_cancel₀ hX
    field_simp
    linear_combination e
  · intro w
    obtain ⟨c, hc, hcd⟩ := H.disc_b w
    obtain ⟨t, ht, e⟩ := hg'disc w
    rw [hcd] at e
    refine ⟨t * c / algebraMap F _ x, div_ne_zero (mul_ne_zero ht hc) (hxw w), ?_⟩
    have hX := hxw w
    rw [map_mul]
    apply mul_left_cancel₀ hX
    field_simp
    linear_combination e
  · refine (H.fin.union hfb).subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq] at hv
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
    apply hv
    rw [hSv]
    have h2 : (NFPlace.finite v).hilbert x d₀ = 1 := by simpa [Function.mem_mulSupport] using hn.2
    rw [hn.1, h2]; norm_num
  · have e1 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), hasseS (v.adicCompletion F) (g v) =
        (∏ᶠ v : HeightOneSpectrum (𝓞 F), hasseS (v.adicCompletion F) (a v)) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hilbert x d₀ := by
      simp_rw [hSv]
      exact finprod_mul_distrib H.fin hfb
    have e2 : ∏ w : InfinitePlace F, hasseS w.Completion (g' w) =
        (∏ w : InfinitePlace F, hasseS w.Completion (b w)) *
          ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert x d₀ := by
      simp_rw [hSw]
      exact Finset.prod_mul_distrib
    rw [finprod_nfplace _ hsf] at hsp
    rw [e1, e2]
    calc _ = ((∏ᶠ v : HeightOneSpectrum (𝓞 F), hasseS (v.adicCompletion F) (a v)) *
            ∏ w : InfinitePlace F, hasseS w.Completion (b w)) *
          ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hilbert x d₀) *
            ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert x d₀) := by ring
      _ = 1 := by rw [H.prod, hsp]; ring

end Split

/-! ### Weak approximation up to squares -/

section WeakApprox

/-- In a complete normed field with `2 ≠ 0`, elements near `1` are squares. -/
theorem sq_near_one (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) :
    ∃ δ > 0, ∀ u : K, ‖u - 1‖ < δ → IsSquare u := by
  have hn : 0 < ‖(2:K)‖ := norm_pos_iff.mpr h2
  set n := ‖(2:K)‖ with hn_def
  refine ⟨n^2/8, by positivity, fun u hu => ?_⟩
  set c := u - 1
  let f : K → K := fun y => (c - y^2)/2
  let s := Metric.closedBall (0:K) (n/4)
  have hmaps : Set.MapsTo f s s := by
    intro y hy
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy ⊢
    simp only [f, norm_div]
    rw [div_le_iff₀ hn]
    calc ‖c - y^2‖ ≤ ‖c‖ + ‖y‖^2 := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_pow]
      _ ≤ n^2/8 + (n/4)^2 := by gcongr
      _ ≤ n/4 * n := by nlinarith
  have hcon : ContractingWith (1/2 : NNReal) (hmaps.restrict f s s) := by
    refine ⟨one_half_lt_one, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    have hy := y.2; have hy' := y'.2
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy hy'
    change dist (f (y:K)) (f y') ≤ ((1/2 : NNReal) : ℝ) * dist (y:K) y'
    simp only [dist_eq_norm, f]
    have : (c - (y:K)^2)/2 - (c - (y':K)^2)/2 = -((y:K) - y') * ((y:K) + y') / 2 := by ring
    rw [this, norm_div, norm_mul, norm_neg, div_le_iff₀ hn]
    have : ‖(y:K) + y'‖ ≤ n/2 := (norm_add_le _ _).trans (by linarith)
    push_cast
    calc ‖(y:K) - y'‖ * ‖(y:K) + y'‖ ≤ ‖(y:K) - y'‖ * (n/2) := by gcongr
      _ = 1/2 * ‖(y:K) - ↑y'‖ * n := by ring
  obtain ⟨y, -, hfix, -⟩ := ContractingWith.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete)
    hmaps hcon (x := 0) (by simp [s]; positivity) (edist_ne_top _ _)
  refine ⟨1 + y, ?_⟩
  have : f y = y := hfix
  simp only [f] at this
  have h2' : (2:K) * y = c - y^2 := by
    have h3 : (2:K) * ((c - y^2)/2) = 2 * y := by rw [this]
    rw [mul_div_cancel₀ _ h2] at h3
    exact h3.symm
  simp only [c] at h2'
  linear_combination -h2'

/-- Open sets of `WithAbs A` on which the image in `K` is `t` times a nonzero square. -/
theorem local_open_sq (K : Type) [NormedField K] [CompleteSpace K] [Algebra F K] (A : AbsoluteValue F ℝ)
    (t : K) (ht : t ≠ 0)
    (hcont : Continuous (fun x : WithAbs A => algebraMap F K (WithAbs.equiv A x)))
    (hdense : DenseRange (algebraMap F K)) :
    ∃ U : Set (WithAbs A), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, ∃ s : K, s ≠ 0 ∧ algebraMap F K (WithAbs.equiv A p) = t * s ^ 2 := by
  have h2 : (2:K) ≠ 0 := by
    have := (algebraMap F K).injective.ne (two_ne_zero : (2:F) ≠ 0)
    rwa [map_ofNat, map_zero] at this
  obtain ⟨δ, hδ, hsq⟩ := sq_near_one K h2
  let V : Set K := {k | ‖k / t - 1‖ < min δ 1}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have htV : t ∈ V := by
    simp only [V, Set.mem_ofPred_eq, div_self ht, sub_self, norm_zero]; positivity
  refine ⟨(fun x : WithAbs A => algebraMap F K (WithAbs.equiv A x)) ⁻¹' V, hV.preimage hcont, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hdense.exists_mem_open hV ⟨t, htV⟩
    exact ⟨(WithAbs.equiv A).symm x, by simpa using hx⟩
  · intro p hp
    simp only [Set.mem_preimage, V, Set.mem_ofPred_eq] at hp
    set k := algebraMap F K (WithAbs.equiv A p)
    have hne : k / t ≠ 0 := by
      intro h0
      rw [h0, zero_sub, norm_neg, norm_one] at hp
      exact absurd (hp.trans_le (min_le_right _ _)) (lt_irrefl _)
    obtain ⟨s, hs⟩ := hsq _ (hp.trans_le (min_le_left _ _))
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply hne
      rw [hs]; simp
    refine ⟨s, hs0, ?_⟩
    have : k = t * (k / t) := by field_simp
    rw [this, hs]; ring

/-- **Weak approximation up to squares:** for a finite set `S` of places and nonzero local targets, some
`x ∈ F^×` is, at each place of `S`, the target times a nonzero square. -/
theorem weak_approx (S : Finset (NFPlace F))
    (tf : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (ti : ∀ w : InfinitePlace F, w.Completion)
    (htf : ∀ v, NFPlace.finite v ∈ S → tf v ≠ 0) (hti : ∀ w, NFPlace.infinite w ∈ S → ti w ≠ 0) :
    ∃ x : F, x ≠ 0 ∧
      (∀ v, NFPlace.finite v ∈ S → ∃ s : v.adicCompletion F, s ≠ 0 ∧ algebraMap F _ x = tf v * s ^ 2) ∧
      (∀ w, NFPlace.infinite w ∈ S → ∃ s : w.Completion, s ≠ 0 ∧ algebraMap F _ x = ti w * s ^ 2) := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨v0, hv0⟩
  · subst hS
    exact ⟨1, one_ne_zero, fun v hv => absurd hv (by simp), fun w hw => absurd hw (by simp)⟩
  let absv : NFPlace F → AbsoluteValue F ℝ := fun v => match v with
    | .infinite w => w.1
    | .finite v => NumberField.HeightOneSpectrum.adicAbv F v
  have hle : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F),
      NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x) ≤ 1 := by
    intro v x; rw [← FinitePlace.norm_embedding]; exact FinitePlace.norm_le_one F v x
  have hlt : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F),
      NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x) < 1 ↔ x ∈ v.asIdeal := by
    intro v x; rw [← FinitePlace.norm_embedding]; exact FinitePlace.norm_lt_one_iff_mem F v x
  have hw2 : ∀ w : InfinitePlace F, w 2 = 2 := by
    intro w; rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; norm_num
  have hfi : ∀ (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)),
      ¬ (NumberField.HeightOneSpectrum.adicAbv F v).IsEquiv w.1 := by
    intro w v h
    have h0 := hle v 2
    rw [map_ofNat] at h0
    have h1 := (h 2 1).mp (by rw [map_one]; exact h0)
    change w 2 ≤ w 1 at h1
    rw [hw2, map_one] at h1; norm_num at h1
  have hpw : Pairwise fun i j : S => ¬ (absv i).IsEquiv (absv j) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij h
    cases i with
    | infinite w =>
      cases j with
      | infinite w' =>
        have e := InfinitePlace.eq_iff_isEquiv.mpr h
        subst e
        exact hij rfl
      | finite v => exact hfi w v h.symm
    | finite v =>
      cases j with
      | infinite w' => exact hfi w' v h
      | finite v' =>
        have hvv : v ≠ v' := by
          intro e; subst e; exact hij rfl
        have : ¬ v'.asIdeal ≤ v.asIdeal := by
          intro hle'
          exact hvv (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle').symm)
        obtain ⟨y, hy', hy⟩ := SetLike.not_le_iff_exists.mp this
        have h1 := (h 1 (algebraMap (𝓞 F) F y)).mp (by
          rw [map_one]; exact not_lt.mp (fun hh => hy ((hlt v y).mp hh)))
        rw [map_one] at h1
        exact absurd ((hlt v' y).mpr hy') (not_lt.mpr h1)
  have hnt : ∀ i : S, (absv i).IsNontrivial := by
    rintro ⟨i, hi⟩
    cases i with
    | infinite w => exact InfinitePlace.isNontrivial w
    | finite v =>
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
      refine ⟨algebraMap (𝓞 F) F x, by simpa using hx0, ?_⟩
      exact ((hlt v x).mpr hx).ne
  have hdense := AbsoluteValue.denseRange_algebraMap_pi hnt hpw
  let Pred : NFPlace F → F → Prop := fun i y => match i with
    | .infinite w => ∃ s : w.Completion, s ≠ 0 ∧ algebraMap F _ y = ti w * s ^ 2
    | .finite v => ∃ s : v.adicCompletion F, s ≠ 0 ∧ algebraMap F _ y = tf v * s ^ 2
  have hU : ∀ i : S, ∃ U : Set (WithAbs (absv i)), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, Pred i (WithAbs.equiv _ p) := by
    rintro ⟨i, hi⟩
    cases i with
    | infinite w =>
      refine local_open_sq (F := F) w.Completion w.1 (ti w) (hti w hi)
        (InfinitePlace.Completion.continuous_coe w) ?_
      have : (algebraMap F w.Completion : F → w.Completion) = (fun x : WithAbs w.1 =>
          InfinitePlace.Completion.ofCompletion (x : UniformSpace.Completion (WithAbs w.1))) ∘
          (WithAbs.equiv w.1).symm := rfl
      rw [this]
      unfold DenseRange
      rw [Function.Surjective.range_comp (WithAbs.equiv w.1).symm.surjective]
      exact InfinitePlace.Completion.denseRange_coe w
    | finite v =>
      refine local_open_sq (F := F) (v.adicCompletion F) (NumberField.HeightOneSpectrum.adicAbv F v)
        (tf v) (htf v hi) ?_ (HeightOneSpectrum.denseRange_algebraMap F v)
      have : Isometry ((FinitePlace.embedding v).comp
          (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv F v)).toRingHom) := by
        apply AddMonoidHomClass.isometry_of_norm
        intro x
        rw [WithAbs.norm_eq_apply_ofAbs]
        exact FinitePlace.norm_embedding v _
      exact this.continuous
  choose U hUo hUn hUp using hU
  choose p hp using hUn
  let V : Set (Π i : S, WithAbs (absv i)) := ⋂ i, (fun q => q i) ⁻¹' U i
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i => (hUo i).preimage (continuous_apply i)
  have hVn : V.Nonempty := ⟨fun i => p i, Set.mem_iInter.mpr fun i => hp i⟩
  obtain ⟨x, hxy⟩ := hdense.exists_mem_open hVo hVn
  have key : ∀ i : S, Pred i x := fun i => hUp i _ (Set.mem_iInter.mp hxy i)
  have hx0 : x ≠ 0 := by
    have := key ⟨v0, hv0⟩
    cases v0 with
    | infinite w =>
      obtain ⟨s, hs, e⟩ := this
      intro h0
      rw [h0, map_zero] at e
      exact (mul_ne_zero (hti w hv0) (pow_ne_zero 2 hs)) e.symm
    | finite v =>
      obtain ⟨s, hs, e⟩ := this
      intro h0
      rw [h0, map_zero] at e
      exact (mul_ne_zero (htf v hv0) (pow_ne_zero 2 hs)) e.symm
  exact ⟨x, hx0, fun v hv => key ⟨NFPlace.finite v, hv⟩, fun w hw => key ⟨NFPlace.infinite w, hw⟩⟩

end WeakApprox

/-! ### Existence of the first coefficient -/

section ExistsXProof

/-- The existence of a global value represented everywhere locally (the key step), in rank `n + 1`. -/
def ExistsX (F : Type) [Field F] [NumberField F] (n : ℕ) : Prop :=
  ∀ (d₀ : F) (a : ∀ v : HeightOneSpectrum (𝓞 F), Fin (n + 1) → v.adicCompletion F)
    (b : ∀ w : InfinitePlace F, Fin (n + 1) → w.Completion), Hyp F (n + 1) d₀ a b →
    ∃ x : F, x ≠ 0 ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        (QuadForm.diag (a v)).RepresentsIn (v.adicCompletion F) (algebraMap F _ x)) ∧
      (∀ w : InfinitePlace F, (QuadForm.diag (b w)).RepresentsIn w.Completion (algebraMap F _ x))

theorem rep_mul_sq {K : Type} [Field K] [CharZero K] {n : ℕ} {a : Fin n → K} {z : K}
    (h : (QuadForm.diag a).RepresentsIn K z) (s : K) :
    (QuadForm.diag a).RepresentsIn K (s ^ 2 * z) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨s • y, ?_⟩
  rw [QuadForm.evalIn_smul, hy]
  simp

theorem rep_coeff_sq {K : Type} [Field K] [CharZero K] {n : ℕ} (a : Fin n → K) (i : Fin n) (s : K) :
    (QuadForm.diag a).RepresentsIn K (a i * s ^ 2) := by
  rw [mul_comm]
  exact rep_mul_sq (represents_coeff a i) s

theorem hasFiniteMulSupport_nfplace (s : NFPlace F → ℤ)
    (hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => s (NFPlace.finite v)).Finite) :
    Function.HasFiniteMulSupport s := by
  have h1 : (NFPlace.finite '' (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      s (NFPlace.finite v))).Finite := hf.image _
  have h2 : (Set.range (NFPlace.infinite : InfinitePlace F → NFPlace F)).Finite := Set.finite_range _
  refine (h1.union h2).subset ?_
  intro v hv
  cases v with
  | finite v => left; exact ⟨v, hv, rfl⟩
  | infinite w => right; exact ⟨w, rfl⟩

theorem even_of_finprod {P : Type*} (s : P → ℤ) (hpm : ∀ v, s v = 1 ∨ s v = -1)
    (hF : {v | s v = -1}.Finite) (h1 : ∏ᶠ v, s v = 1) : Even {v | s v = -1}.ncard := by
  have hms : Function.mulSupport s = {v | s v = -1} := by
    ext v
    rcases hpm v with h | h <;> simp [Function.mem_mulSupport, h]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hF.toFinset) (by rw [hms]; simp)] at h1
  rw [Finset.prod_congr rfl (fun v hv => (by simpa using hv : s v = -1))] at h1
  rw [Finset.prod_const] at h1
  rw [neg_one_pow_eq_one_iff_even (by decide)] at h1
  rw [Set.ncard_eq_toFinset_card _ hF]
  exact h1

/-- Rank one: the first coefficient is `d₀`. -/
theorem existsX_zero : ExistsX F 0 := by
  intro d₀ a b H
  refine ⟨d₀, H.d_ne, fun v => ?_, fun w => ?_⟩
  · obtain ⟨c, hc, e⟩ := H.disc_a v
    rw [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at e
    have := rep_mul_sq (represents_coeff (a v) 0) c⁻¹
    convert this using 1
    rw [e]; field_simp
  · obtain ⟨c, hc, e⟩ := H.disc_b w
    rw [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at e
    have := rep_mul_sq (represents_coeff (b w) 0) c⁻¹
    convert this using 1
    rw [e]; field_simp

/-- A ternary form with `S = 1` and `(-1,-1) = 1` is universal. -/
theorem rank3_good {K : Type} [Field K] [CharZero K] (hK : LocalHilbertField K) (hG : GoodK K)
    (a : Fin 3 → K) (ha : ∀ i, a i ≠ 0) (hS : hasseS K a = 1)
    (h11 : hilbertSymbol K (-1) (-1) = 1) :
    ∀ y : K, y ≠ 0 → (QuadForm.diag a).RepresentsIn K y := by
  intro y hy
  have hv : hasseVec a = hilbertSymbol K (a 0) (a 1) * hilbertSymbol K (a 0) (a 2) *
      hilbertSymbol K (a 1) (a 2) := by
    conv_lhs => rw [eq_vec_three a]
    exact hasseVec_three _ _ _
  have hD : a 0 * a 1 * a 2 ≠ 0 := mul_ne_zero (mul_ne_zero (ha 0) (ha 1)) (ha 2)
  have hS' := hG.hasseS_eq ha
  rw [hS, Fin.prod_univ_three, hv] at hS'
  rw [eq_vec_three a, represents_three_iff hK (ha 0) (ha 1) (ha 2) hy]
  intro _
  have e1 : hilbertSymbol K (-1) (-(a 0 * a 1 * a 2)) =
      hilbertSymbol K (a 0 * a 1 * a 2) (a 0 * a 1 * a 2) := by
    rw [show -(a 0 * a 1 * a 2) = -1 * (a 0 * a 1 * a 2) by ring,
      hG.mul_right' (by norm_num) (by norm_num) hD, h11, one_mul,
      hilbertSymbol_comm K (-1) (a 0 * a 1 * a 2), (hG.self' hD).symm]
  rw [e1]
  rcases hs_pm (a 0) (a 1) with h1 | h1 <;> rcases hs_pm (a 0) (a 2) with h2 | h2 <;>
    rcases hs_pm (a 1) (a 2) with h3 | h3 <;>
    rcases hs_pm (a 0 * a 1 * a 2) (a 0 * a 1 * a 2) with h4 | h4 <;>
    rw [h1, h2, h3, h4] at hS' ⊢ <;> first | rfl | (norm_num at hS')

/-- Symbol identities for a binary form `⟨a0, a1⟩` with `a0 a1 = d c²`. -/
theorem rank2_sym {K : Type} [Field K] [CharZero K] (hG : GoodK K) {a0 a1 d c : K}
    (h0 : a0 ≠ 0) (h1 : a1 ≠ 0) (hc : c ≠ 0) (e : a0 * a1 = d * c ^ 2) :
    hilbertSymbol K a0 a1 = hasseS K ![a0, a1] * hilbertSymbol K d (-1) ∧
    hilbertSymbol K (-d) a0 = hilbertSymbol K a0 a1 ∧
    ∀ x : K, hilbertSymbol K (-d) x = hilbertSymbol K a0 a1 →
      hilbertSymbol K x (-(a0 * a1)) = hilbertSymbol K a0 a1 := by
  have ha : ∀ i, (![a0, a1] : Fin 2 → K) i ≠ 0 := fun i => by fin_cases i <;> simpa
  have hD : a0 * a1 ≠ 0 := mul_ne_zero h0 h1
  have hd : d ≠ 0 := by
    rintro rfl
    simp at e
    rcases e with h | h
    · exact h0 h
    · exact h1 h
  have hS := hG.hasseS_eq ha
  have hprod : ∏ i, (![a0, a1] : Fin 2 → K) i = a0 * a1 := by simp [Fin.prod_univ_two]
  rw [hprod, hasseVec_two] at hS
  have hDD : hilbertSymbol K (a0 * a1) (a0 * a1) = hilbertSymbol K d (-1) := by
    rw [e, hG.self' (mul_ne_zero hd (pow_ne_zero 2 hc)), mul_comm d, hs_sq_left _ _ _ hc]
  rw [hDD] at hS
  have h1' : hilbertSymbol K a0 a1 = hasseS K ![a0, a1] * hilbertSymbol K d (-1) := by
    rcases hs_pm a0 a1 with h | h <;> rcases hs_pm d (-1 : K) with h' | h' <;> rw [h, h'] at hS ⊢ <;>
      linarith
  refine ⟨h1', ?_, ?_⟩
  · have e2 : c ^ 2 * -d = (-a0) * a1 := by linear_combination e
    rw [hilbertSymbol_comm K (-d) a0, ← hs_sq_right a0 (-d) c hc, e2,
      hG.mul_right' h0 (neg_ne_zero.mpr h0) h1, hilbertSymbol_self_neg, one_mul]
  · intro x hx
    have e2 : c ^ 2 * -d = -(a0 * a1) := by linear_combination e
    rw [← e2, hs_sq_right _ _ _ hc, hilbertSymbol_comm K x, hx]

/-- Real case of the representation criterion for binary forms. -/
theorem real_rep2 (X B0 B1 : ℝ) (hX : X ≠ 0) (hB0 : B0 ≠ 0) (hB1 : B1 ≠ 0)
    (h : hilbertSymbol ℝ X (-(B0 * B1)) = hilbertSymbol ℝ B0 B1) :
    (∃ s : ℝ, X = B0 * s ^ 2) ∨ (∃ s : ℝ, X = B1 * s ^ 2) := by
  have sq : ∀ B : ℝ, 0 < X * B → ∃ s : ℝ, X = B * s ^ 2 := by
    intro B hB
    have hB' : B ≠ 0 := by rintro rfl; simp at hB
    have hpos : 0 ≤ X / B := by
      rw [div_nonneg_iff]
      rcases lt_or_gt_of_ne hB' with h' | h'
      · right; constructor
        · by_contra hh; push_neg at hh; nlinarith
        · exact h'.le
      · left; constructor
        · by_contra hh; push_neg at hh; nlinarith
        · exact h'.le
    refine ⟨Real.sqrt (X / B), ?_⟩
    rw [Real.sq_sqrt hpos]; field_simp
  by_cases h0 : 0 < X * B0
  · exact Or.inl (sq B0 h0)
  by_cases h1 : 0 < X * B1
  · exact Or.inr (sq B1 h1)
  exfalso
  have n0 : X * B0 < 0 := lt_of_le_of_ne (not_lt.mp h0) (mul_ne_zero hX hB0)
  have n1 : X * B1 < 0 := lt_of_le_of_ne (not_lt.mp h1) (mul_ne_zero hX hB1)
  have hBB : 0 < B0 * B1 := by
    rcases lt_or_gt_of_ne hX with hx | hx
    · have a0 : 0 < B0 := by nlinarith
      have a1 : 0 < B1 := by nlinarith
      positivity
    · have a0 : B0 < 0 := by nlinarith
      have a1 : B1 < 0 := by nlinarith
      nlinarith
  rw [HasseIsoNF.hilbertSymbol_real_eq _ _ hX (neg_ne_zero.mpr (mul_ne_zero hB0 hB1)),
    HasseIsoNF.hilbertSymbol_real_eq _ _ hB0 hB1] at h
  rcases lt_or_gt_of_ne hX with hx | hx
  · have a0 : 0 < B0 := by nlinarith
    have a1 : 0 < B1 := by nlinarith
    have : X < 0 ∧ -(B0 * B1) < 0 := ⟨hx, by linarith⟩
    rw [if_pos this, if_neg (by rintro ⟨h', -⟩; linarith)] at h
    norm_num at h
  · have a0 : B0 < 0 := by nlinarith
    have a1 : B1 < 0 := by nlinarith
    rw [if_neg (by rintro ⟨h', -⟩; linarith), if_pos ⟨a0, a1⟩] at h
    norm_num at h

/-- Binary forms at an infinite place: the symbol criterion implies representation. -/
theorem rep2_inf (w : InfinitePlace F) {b0 b1 x d c : w.Completion} (h0 : b0 ≠ 0) (h1 : b1 ≠ 0)
    (hx : x ≠ 0) (hc : c ≠ 0) (e : b0 * b1 = d * c ^ 2)
    (hxs : hilbertSymbol w.Completion (-d) x = hilbertSymbol w.Completion b0 b1) :
    (QuadForm.diag ![b0, b1]).RepresentsIn w.Completion x := by
  have key := (rank2_sym (goodK_infinite w) h0 h1 hc e).2.2 x hxs
  have hrep : ∀ s : w.Completion, ((QuadForm.diag ![b0, b1]).RepresentsIn w.Completion (b0 * s ^ 2)) ∧
      ((QuadForm.diag ![b0, b1]).RepresentsIn w.Completion (b1 * s ^ 2)) := fun s =>
    ⟨rep_coeff_sq (![b0, b1] : Fin 2 → w.Completion) 0 s, rep_coeff_sq (![b0, b1] : Fin 2 → w.Completion) 1 s⟩
  rcases w.isReal_or_isComplex with hw | hw
  · let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have key' := key
    rw [← HasseIsoNF.hilbertSymbol_ringEquiv φ] at key'
    simp only [map_neg, map_mul] at key'
    rw [← HasseIsoNF.hilbertSymbol_ringEquiv φ] at key'
    rcases real_rep2 (φ x) (φ b0) (φ b1) ((map_ne_zero _).mpr hx) ((map_ne_zero _).mpr h0)
      ((map_ne_zero _).mpr h1) (by simpa using key') with ⟨s, hs⟩ | ⟨s, hs⟩
    · have : x = b0 * (φ.symm s) ^ 2 := by
        apply φ.injective
        simp [hs]
      rw [this]; exact (hrep _).1
    · have : x = b1 * (φ.symm s) ^ 2 := by
        apply φ.injective
        simp [hs]
      rw [this]; exact (hrep _).2
  · obtain ⟨s, hs⟩ := LocalClassNF.exists_sq_complex hw (x / b0)
    have : x = b0 * s ^ 2 := by rw [hs]; field_simp
    rw [this]; exact (hrep _).1

theorem hasseS_pm {K : Type} [Field K] [CharZero K] {n : ℕ} (a : Fin n → K) :
    hasseS K a = 1 ∨ hasseS K a = -1 := by
  unfold hasseS
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun i _ => ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun j _ => ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  split_ifs
  · exact hs_pm _ _
  · exact Or.inl rfl

theorem rank2_sym' {K : Type} [Field K] [CharZero K] (hG : GoodK K) (a : Fin 2 → K)
    (ha : ∀ i, a i ≠ 0) {d c : K} (hc : c ≠ 0) (e : ∏ i, a i = d * c ^ 2) :
    hilbertSymbol K (a 0) (a 1) = hasseS K a * hilbertSymbol K d (-1) ∧
    hilbertSymbol K (-d) (a 0) = hilbertSymbol K (a 0) (a 1) ∧
    ∀ x : K, hilbertSymbol K (-d) x = hilbertSymbol K (a 0) (a 1) →
      hilbertSymbol K x (-(a 0 * a 1)) = hilbertSymbol K (a 0) (a 1) := by
  rw [Fin.prod_univ_two] at e
  have h := rank2_sym hG (ha 0) (ha 1) hc e
  rwa [← eq_vec_two a] at h

theorem existsX_one : ExistsX F 1 := by
  classical
  intro d₀ a b H
  let ε : NFPlace F → ℤ := fun v => match v with
    | .finite v => hasseS (v.adicCompletion F) (a v) * (NFPlace.finite v).hilbert d₀ (-1)
    | .infinite w => hasseS w.Completion (b w) * (NFPlace.infinite w).hilbert d₀ (-1)
  have hεf : ∀ v : HeightOneSpectrum (𝓞 F), ε (NFPlace.finite v) =
      hasseS (v.adicCompletion F) (a v) * (NFPlace.finite v).hilbert d₀ (-1) := fun v => rfl
  have hεi : ∀ w : InfinitePlace F, ε (NFPlace.infinite w) =
      hasseS w.Completion (b w) * (NFPlace.infinite w).hilbert d₀ (-1) := fun w => rfl
  obtain ⟨hsf, hsp⟩ := NFPlace.finprod_hilbert d₀ (-1) H.d_ne (by norm_num)
  have hfb := finite_part_finite _ hsf
  have hf1 : ∀ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hilbert d₀ (-1) =
      hilbertSymbol (v.adicCompletion F) (algebraMap F _ d₀) (-1) := fun v => by
    show hilbertSymbol _ _ (algebraMap F _ (-1)) = _
    rw [map_neg, map_one]
  have hi1 : ∀ w : InfinitePlace F, (NFPlace.infinite w).hilbert d₀ (-1) =
      hilbertSymbol w.Completion (algebraMap F _ d₀) (-1) := fun w => by
    show hilbertSymbol _ _ (algebraMap F _ (-1)) = _
    rw [map_neg, map_one]
  have hpm : ∀ v, ε v = 1 ∨ ε v = -1 := by
    intro v
    cases v with
    | finite v =>
      rw [hεf]
      rcases hasseS_pm (a v) with h | h <;> rcases NFPlace.hilbert_eq_one_or (NFPlace.finite v) d₀ (-1) with h' | h' <;>
        rw [h, h'] <;> simp
    | infinite w =>
      rw [hεi]
      rcases hasseS_pm (b w) with h | h <;> rcases NFPlace.hilbert_eq_one_or (NFPlace.infinite w) d₀ (-1) with h' | h' <;>
        rw [h, h'] <;> simp
  have hεfs : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ε (NFPlace.finite v)).Finite := by
    refine (H.fin.union hfb).subset ?_
    intro v hv
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
    apply hv
    show ε (NFPlace.finite v) = 1
    rw [hεf, hn.1]
    have h2 : (NFPlace.finite v).hilbert d₀ (-1) = 1 := by simpa [Function.mem_mulSupport] using hn.2
    rw [h2]; norm_num
  have hεsup : Function.HasFiniteMulSupport ε := hasFiniteMulSupport_nfplace ε hεfs
  have hprod : ∏ᶠ v : NFPlace F, ε v = 1 := by
    rw [finprod_nfplace ε hεsup]
    have e1 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ε (NFPlace.finite v) =
        (∏ᶠ v : HeightOneSpectrum (𝓞 F), hasseS (v.adicCompletion F) (a v)) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hilbert d₀ (-1) := by
      simp_rw [hεf]
      exact finprod_mul_distrib H.fin hfb
    have e2 : ∏ w : InfinitePlace F, ε (NFPlace.infinite w) =
        (∏ w : InfinitePlace F, hasseS w.Completion (b w)) *
          ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert d₀ (-1) := by
      simp_rw [hεi]
      exact Finset.prod_mul_distrib
    rw [finprod_nfplace _ hsf] at hsp
    rw [e1, e2]
    calc _ = ((∏ᶠ v : HeightOneSpectrum (𝓞 F), hasseS (v.adicCompletion F) (a v)) *
            ∏ w : InfinitePlace F, hasseS w.Completion (b w)) *
          ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hilbert d₀ (-1)) *
            ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert d₀ (-1)) := by ring
      _ = 1 := by rw [H.prod, hsp]; ring
  have hFin : {v : NFPlace F | ε v = -1}.Finite :=
    hεsup.subset (fun v hv => by
      simp only [Set.mem_ofPred_eq] at hv
      simp [Function.mem_mulSupport, hv])
  have heven := even_of_finprod ε hpm hFin hprod
  have hloc : ∀ v : NFPlace F, v.atPlace fun K _ _ => ∃ x : K, x ≠ 0 ∧ ∀ _ : Unit,
      hilbertSymbol K (algebraMap F K (-d₀)) x = ε v := by
    intro v
    cases v with
    | finite v =>
      obtain ⟨c, hc, e⟩ := H.disc_a v
      obtain ⟨s1, s2, -⟩ := rank2_sym' (goodK_finite v) (a v) (H.a_ne v) hc e
      refine ⟨a v 0, H.a_ne v 0, fun _ => ?_⟩
      rw [hεf, map_neg]
      show hilbertSymbol (v.adicCompletion F) (-(algebraMap F _ d₀)) (a v 0) = _
      rw [s2, s1, hf1]
    | infinite w =>
      obtain ⟨c, hc, e⟩ := H.disc_b w
      obtain ⟨s1, s2, -⟩ := rank2_sym' (goodK_infinite w) (b w) (H.b_ne w) hc e
      refine ⟨b w 0, H.b_ne w 0, fun _ => ?_⟩
      rw [hεi, map_neg]
      show hilbertSymbol w.Completion (-(algebraMap F _ d₀)) (b w 0) = _
      rw [s2, s1, hi1]
  obtain ⟨x, hx0, hx⟩ := NFInputs.exists_prescribed_hilbert_nf (ι := Unit) (fun _ => -d₀)
    (fun _ => neg_ne_zero.mpr H.d_ne) (fun _ v => ε v) (fun _ v => hpm v)
    (by
      refine hFin.subset ?_
      rintro v ⟨_, hv⟩
      exact hv)
    (fun _ => heven) hloc
  have hx0' : ∀ K : Type, ∀ [Field K] [Algebra F K], algebraMap F K x ≠ 0 := fun K _ _ =>
    (map_ne_zero _).mpr hx0
  refine ⟨x, hx0, fun v => ?_, fun w => ?_⟩
  · obtain ⟨c, hc, e⟩ := H.disc_a v
    obtain ⟨s1, s2, s3⟩ := rank2_sym' (goodK_finite v) (a v) (H.a_ne v) hc e
    have hxv := hx () (NFPlace.finite v)
    have hxs : hilbertSymbol (v.adicCompletion F) (-(algebraMap F _ d₀)) (algebraMap F _ x) =
        hilbertSymbol (v.adicCompletion F) (a v 0) (a v 1) := by
      have h := hx () (NFPlace.finite v)
      rw [hεf, hf1] at h
      change hilbertSymbol (v.adicCompletion F) (algebraMap F _ (-d₀)) (algebraMap F _ x) = _ at h
      rw [map_neg] at h
      rw [h, s1]
    have h3 := s3 _ hxs
    rw [eq_vec_two (a v)]
    rw [represents_two_iff (HasseIsoNF.localHilbertField_adicCompletion v) (H.a_ne v 0) (H.a_ne v 1)
      (hx0' _)]
    exact h3
  · obtain ⟨c, hc, e⟩ := H.disc_b w
    obtain ⟨s1, s2, s3⟩ := rank2_sym' (goodK_infinite w) (b w) (H.b_ne w) hc e
    have hxs : hilbertSymbol w.Completion (-(algebraMap F _ d₀)) (algebraMap F _ x) =
        hilbertSymbol w.Completion (b w 0) (b w 1) := by
      have h := hx () (NFPlace.infinite w)
      rw [hεi, hi1] at h
      change hilbertSymbol w.Completion (algebraMap F _ (-d₀)) (algebraMap F _ x) = _ at h
      rw [map_neg] at h
      rw [h, s1]
    rw [eq_vec_two (b w)]
    rw [Fin.prod_univ_two] at e
    exact rep2_inf w (H.b_ne w 0) (H.b_ne w 1) (hx0' _) hc e hxs

theorem existsX_ge2 (n : ℕ) : ExistsX F (n + 2) := by
  classical
  intro d₀ a b H
  let Good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    ∀ y : v.adicCompletion F, y ≠ 0 → (QuadForm.diag (a v)).RepresentsIn (v.adicCompletion F) y
  have hBad : {v | ¬ Good v}.Finite := by
    rcases n with _ | n
    · obtain ⟨hsf, hsp⟩ := NFPlace.finprod_hilbert (-1 : F) (-1) (by norm_num) (by norm_num)
      refine (H.fin.union (finite_part_finite _ hsf)).subset ?_
      intro v hv
      by_contra hn
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
      apply hv
      exact rank3_good (HasseIsoNF.localHilbertField_adicCompletion v) (goodK_finite v) (a v) (H.a_ne v)
        hn.1 (by
          have h := hn.2
          simp only [Function.mem_mulSupport, not_not] at h
          simpa [NFPlace.hilbert] using h)
    · refine Set.Finite.subset (Set.finite_empty) ?_
      intro v hv
      exfalso
      apply hv
      intro y _
      exact represents_of_four_le (HasseIsoNF.localHilbertField_adicCompletion v) (H.a_ne v)
        (by omega) y
  let S : Finset (NFPlace F) :=
    hBad.toFinset.map ⟨NFPlace.finite, fun x y h => NFPlace.finite.inj h⟩ ∪
      Finset.univ.map ⟨NFPlace.infinite, fun x y h => by cases h; rfl⟩
  obtain ⟨x, hx0, hxf, hxi⟩ := weak_approx S (fun v => a v 0) (fun w => b w 0)
    (fun v _ => H.a_ne v 0) (fun w _ => H.b_ne w 0)
  refine ⟨x, hx0, fun v => ?_, fun w => ?_⟩
  · by_cases hg : Good v
    · exact hg _ ((map_ne_zero _).mpr hx0)
    · have hvS : NFPlace.finite v ∈ S := by
        simp only [S, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
        left
        exact ⟨v, by simpa using hg, rfl⟩
      obtain ⟨s, -, e⟩ := hxf v hvS
      rw [e]
      exact rep_coeff_sq (a v) 0 s
  · have hwS : NFPlace.infinite w ∈ S := by
      simp only [S, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
      right
      exact ⟨w, Finset.mem_univ _, rfl⟩
    obtain ⟨s, -, e⟩ := hxi w hwS
    rw [e]
    exact rep_coeff_sq (b w) 0 s

end ExistsXProof

/-! ### The induction -/

section Induction

theorem cons_map {K : Type} [Field K] [Algebra F K] {n : ℕ} (x : F) (c : Fin n → F) :
    (fun i => algebraMap F K ((Fin.cons x c : Fin (n + 1) → F) i)) =
      (Fin.cons (algebraMap F K x) (fun i => algebraMap F K (c i)) : Fin (n + 1) → K) := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp

theorem suff (hex : ∀ n, ExistsX F n) : ∀ (n : ℕ) (d₀ : F)
    (a : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (b : ∀ w : InfinitePlace F, Fin n → w.Completion), Hyp F n d₀ a b →
    ∃ c : Fin n → F, (∀ i, c i ≠ 0) ∧
      (∀ v, (QuadForm.diag fun i => algebraMap F (v.adicCompletion F) (c i)).IsometricIn
        (v.adicCompletion F) (QuadForm.diag (a v))) ∧
      (∀ w, (QuadForm.diag fun i => algebraMap F w.Completion (c i)).IsometricIn
        w.Completion (QuadForm.diag (b w))) := by
  intro n
  induction n with
  | zero =>
    intro d₀ a b _
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun v => ?_, fun w => ?_⟩
    · rw [Subsingleton.elim (fun i : Fin 0 => algebraMap F (v.adicCompletion F) (Fin.elim0 i)) (a v)]
      exact QuadForm.isometricIn_refl _ _
    · rw [Subsingleton.elim (fun i : Fin 0 => algebraMap F w.Completion (Fin.elim0 i)) (b w)]
      exact QuadForm.isometricIn_refl _ _
  | succ m ih =>
    intro d₀ a b H
    obtain ⟨x, hx, hra, hrb⟩ := hex m d₀ a b H
    obtain ⟨g, g', H', hgiso, hg'iso⟩ := reduce H hx hra hrb
    obtain ⟨c', hc', hv, hw⟩ := ih (d₀ * x) g g' H'
    refine ⟨Fin.cons x c', ?_, fun v => ?_, fun w => ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hx
      | succ i => simpa using hc' i
    · rw [cons_map]
      exact QuadForm.isometricIn_trans _ (QuadForm.isometricIn_diag_cons_of _ _ (hv v))
        (QuadForm.isometricIn_symm _ (hgiso v))
    · rw [cons_map]
      exact QuadForm.isometricIn_trans _ (QuadForm.isometricIn_diag_cons_of _ _ (hw w))
        (QuadForm.isometricIn_symm _ (hg'iso w))

end Induction

theorem hex_all : ∀ n, ExistsX F n
  | 0 => existsX_zero
  | 1 => existsX_one
  | n + 2 => existsX_ge2 n

theorem theorem6_12_of (hex : ∀ n, ExistsX F n) : Theorem6_12 F := by
  refine ⟨fun n a b ha hb => ⟨?_, ?_⟩⟩
  · rintro ⟨q₀, hq, hv, hw⟩
    have H := necessity a b ha hb q₀ hq hv hw
    exact ⟨⟨_, H.d_ne, H.disc_a, H.disc_b⟩, H.fin, H.prod⟩
  · rintro ⟨⟨d₀, hd₀, hda, hdb⟩, hfin, hprod⟩
    obtain ⟨c, hc, hv, hw⟩ := suff hex n d₀ a b ⟨ha, hb, hd₀, hda, hdb, hfin, hprod⟩
    refine ⟨QuadForm.diag c, QuadForm.nondegenerate_diag hc, fun v => ?_, fun w => ?_⟩
    · rw [map_diag]; exact hv v
    · rw [map_diag]; exact hw w

end T612

/-- **Theorem 6.12** (Milne, *CFT*, VIII, Theorem 6.12, p. 256; O'Meara 72:1), proved unconditionally: a family
of local nondegenerate diagonal forms of rank `n` is the family of localizations of a global form iff the
discriminants come from one `d₀ ∈ F^×`, the Hasse invariants are `1` almost everywhere and their product is `1`.
See the module docstring for the proof. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 6.12, p. 256 (O'Meara 72:1)"]
theorem theorem6_12 (F : Type) [Field F] [NumberField F] : Theorem6_12 F :=
  T612.theorem6_12_of T612.hex_all

end NumberFieldKB.MilneCFT.Ch8
