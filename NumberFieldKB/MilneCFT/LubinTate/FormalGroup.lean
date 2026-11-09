import NumberFieldKB.MilneCFT.LubinTate.Basic

/-!
# Lubin–Tate formal group laws (Milne, *Class Field Theory*, Chapter I, §2, Propositions 2.12–2.15)

For $f \in \mathcal F_\pi$: the Lubin–Tate formal group law $F_f$ (Proposition 2.12), the homomorphisms
$[a]_{g,f} : F_f \to F_g$ (Proposition 2.14, 2.15), the canonical isomorphism $F_f \cong F_g$ (Corollary 2.16), and
the ring homomorphism $a \mapsto [a]_f$, $A \to \mathrm{End}(F_f)$ (Corollary 2.17, Remark 2.19). Everything follows
from Lemma 2.11 (`exists_unique_lubinTate`) by its uniqueness clause. Summary 2.20 is the conjunction of these
results.
-/

open MvPowerSeries

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {A : Type*} [CommRing A] {π : A} {q : ℕ}

section Helpers

variable {σ τ : Type*}

/-- Substituting after a power-series substitution: $(f \circ \varphi)(v) = f \circ (\varphi(v))$. -/
theorem mvSubst_powerSeriesSubst {φ : MvPowerSeries τ A} (hφ : constantCoeff φ = 0)
    (f : PowerSeries A) {v : τ → MvPowerSeries σ A} (hv : MvPowerSeries.HasSubst v) :
    MvPowerSeries.subst v (f.subst φ) = f.subst (MvPowerSeries.subst v φ) := by
  have h1 : MvPowerSeries.HasSubst (fun _ : Unit => φ) :=
    (PowerSeries.HasSubst.of_constantCoeff_zero hφ).const
  show MvPowerSeries.subst v (MvPowerSeries.subst (fun _ : Unit => φ) f) =
    MvPowerSeries.subst (fun _ : Unit => MvPowerSeries.subst v φ) f
  rw [subst_comp_subst_apply h1 hv]

/-- The coefficient of a variable in a substitution, when everything has zero constant term:
$\mathrm{coeff}_{X_i}\, P(v) = \sum_j \mathrm{coeff}_{X_j} P \cdot \mathrm{coeff}_{X_i} v_j$. -/
theorem coeff_single_subst [Fintype τ] [DecidableEq τ] [DecidableEq σ] {P : MvPowerSeries τ A}
    (hP : constantCoeff P = 0) {v : τ → MvPowerSeries σ A} (hv : ∀ j, constantCoeff (v j) = 0)
    (i : σ) :
    coeff (Finsupp.single i 1) (P.subst v) =
      ∑ j, coeff (Finsupp.single j 1) P * coeff (Finsupp.single i 1) (v j) := by
  have hvs : MvPowerSeries.HasSubst v := hasSubst_of_constantCoeff_zero hv
  set L : MvPowerSeries τ A := ∑ j, C (coeff (Finsupp.single j 1) P) * X j with hL
  have hord : (2 : ℕ∞) ≤ (P - L).order := by
    apply MvPowerSeries.le_order
    intro d hd
    have hd' : Finsupp.degree d < 2 := by exact_mod_cast hd
    rcases (by omega : Finsupp.degree d = 0 ∨ Finsupp.degree d = 1) with h0 | h0
    · have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 h0
      subst this
      simp [hL, hP]
    · have hmem : d ∈ {d : τ →₀ ℕ | d.degree = 1} := h0
      rw [← Finsupp.range_single_one] at hmem
      obtain ⟨j, rfl⟩ := hmem
      simp [hL, map_sum, coeff_C_mul, coeff_X, Finsupp.single_left_inj]
  have h1 : (1 : ℕ∞) ≤ ⨅ j, (v j).order := by
    refine le_iInf fun j => ?_
    exact (one_le_order_iff_constCoeff_eq_zero).2 (hv j)
  have h2 := le_order_subst hvs (P - L)
  have h3 : coeff (Finsupp.single i 1) ((P - L).subst v) = 0 := by
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h2
    refine lt_of_lt_of_le ?_ (mul_le_mul' h1 hord)
    simp
  have h4 : P.subst v = (P - L).subst v + L.subst v := by
    rw [← subst_add hvs]; simp
  rw [h4, map_add, h3, zero_add]
  have h5 : L.subst v = ∑ j, C (coeff (Finsupp.single j 1) P) * v j := by
    rw [hL, ← coe_substAlgHom hvs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coe_substAlgHom hvs, subst_mul hvs, subst_C, subst_X hvs]
  rw [h5]
  simp [map_sum, coeff_C_mul]

/-- A power series without constant term, substituted for a variable, has no constant term. -/
theorem constantCoeff_twist {g : PowerSeries A} (hg : PowerSeries.constantCoeff g = 0) (i : σ) :
    constantCoeff (g.subst (X i : MvPowerSeries σ A)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg

theorem hasSubst_twist [Finite σ] {g : PowerSeries A} (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.HasSubst (fun i : σ => g.subst (X i : MvPowerSeries σ A)) :=
  hasSubst_of_constantCoeff_zero fun i => constantCoeff_twist hg i

/-- Composition preserves the intertwining property: if $f \circ P = P(g(X_i))$ and each $v_j$ satisfies
$g \circ v_j = v_j(h(X_k))$, then $f \circ P(v) = P(v)(h(X_k))$. -/
theorem subst_twist_comp [Finite τ] [Finite σ] {f g h : PowerSeries A}
    (hg0 : PowerSeries.constantCoeff g = 0) (hh0 : PowerSeries.constantCoeff h = 0)
    {P : MvPowerSeries τ A} (hP0 : constantCoeff P = 0)
    (hP : f.subst P = P.subst (fun i => g.subst (X i : MvPowerSeries τ A)))
    {v : τ → MvPowerSeries σ A} (hv0 : ∀ j, constantCoeff (v j) = 0)
    (hv : ∀ j, g.subst (v j) = (v j).subst (fun i => h.subst (X i : MvPowerSeries σ A))) :
    f.subst (P.subst v) = (P.subst v).subst (fun i => h.subst (X i : MvPowerSeries σ A)) := by
  have hvs : MvPowerSeries.HasSubst v := hasSubst_of_constantCoeff_zero hv0
  rw [← mvSubst_powerSeriesSubst hP0 f hvs, hP, subst_comp_subst_apply (hasSubst_twist hg0) hvs,
    subst_comp_subst_apply hvs (hasSubst_twist hh0)]
  congr 1
  funext s
  rw [mvSubst_powerSeriesSubst (by simp) g hvs, subst_X hvs, hv s]

/-- For one variable, the intertwining substitution is just $f$. -/
theorem twist_unit (f : PowerSeries A) :
    (fun i : Unit => f.subst (X i : MvPowerSeries Unit A)) = fun _ => f := by
  funext i
  exact PowerSeries.X_subst f

end Helpers

section Phi

variable (H : LubinTateHyp A π q) {f g : PowerSeries A} (hf : f ∈ lubinTateSeries π q)
  (hg : g ∈ lubinTateSeries π q)

/-- Substituting two $f$-intertwined series into $F_f$ gives an $f$-intertwined series whose linear
coefficients are the sums of the linear coefficients. -/
theorem lubinTatePhi_subst {σ : Type*} [Fintype σ] [DecidableEq σ] {p r : MvPowerSeries σ A}
    (hp0 : constantCoeff p = 0) (hr0 : constantCoeff r = 0)
    (hp : f.subst p = p.subst (fun i => f.subst (X i : MvPowerSeries σ A)))
    (hr : f.subst r = r.subst (fun i => f.subst (X i : MvPowerSeries σ A))) :
    constantCoeff ((lubinTatePhi H (σ := Fin 2) (fun _ => 1) hf hf).subst ![p, r]) = 0 ∧
      (∀ i, coeff (Finsupp.single i 1)
          ((lubinTatePhi H (σ := Fin 2) (fun _ => 1) hf hf).subst ![p, r]) =
        coeff (Finsupp.single i 1) p + coeff (Finsupp.single i 1) r) ∧
      f.subst ((lubinTatePhi H (σ := Fin 2) (fun _ => 1) hf hf).subst ![p, r]) =
        ((lubinTatePhi H (σ := Fin 2) (fun _ => 1) hf hf).subst ![p, r]).subst
          (fun i => f.subst (X i : MvPowerSeries σ A)) := by
  obtain ⟨h0, h1, h2⟩ := lubinTatePhi_spec H (σ := Fin 2) (fun _ => 1) hf hf
  have hv0 : ∀ j, constantCoeff (![p, r] j) = 0 := by
    intro j; fin_cases j <;> simpa
  refine ⟨constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hv0) hv0 h0, fun i => ?_,
    subst_twist_comp hf.1 hf.1 h0 h2 hv0 ?_⟩
  · rw [coeff_single_subst h0 hv0]
    simp [Fin.sum_univ_two, h1]
  · intro j; fin_cases j <;> simpa

end Phi


/-- **The Lubin–Tate formal group law $F_f$** (Milne, *CFT*, I, Proposition 2.12): for $f \in \mathcal F_\pi$, the
unique $F_f(X,Y) = X + Y + (\deg \ge 2)$ with $f(F_f(X,Y)) = F_f(f(X), f(Y))$ (Lemma 2.11 with
$\phi_1 = X + Y$); it is a formal group law. -/
@[kb "milne2020cft" "Ch. I, Proposition 2.12"]
def lubinTateFormalGroup (H : LubinTateHyp A π q) {f : PowerSeries A} (hf : f ∈ lubinTateSeries π q) :
    FormalGroup A where
  toPowerSeries := lubinTatePhi H (σ := Fin 2) (fun _ => 1) hf hf
  zero_constantCoeff := (lubinTatePhi_spec H (σ := Fin 2) (fun _ => 1) hf hf).1
  lin_coeff_X := (lubinTatePhi_spec H (σ := Fin 2) (fun _ => 1) hf hf).2.1 0
  lin_coeff_Y := (lubinTatePhi_spec H (σ := Fin 2) (fun _ => 1) hf hf).2.1 1
  assoc := by
    obtain ⟨h0, h1, h2⟩ := lubinTatePhi_spec H (σ := Fin 2) (fun _ => 1) hf hf
    have hX : ∀ i : Fin 3, constantCoeff (X i : MvPowerSeries (Fin 3) A) = 0 ∧
        f.subst (X i : MvPowerSeries (Fin 3) A) =
          (X i : MvPowerSeries (Fin 3) A).subst (fun j => f.subst (X j : MvPowerSeries (Fin 3) A)) :=
      fun i => ⟨by simp, by rw [subst_X (hasSubst_twist hf.1)]⟩
    have hXc : ∀ i j : Fin 3, coeff (Finsupp.single i 1) (X j : MvPowerSeries (Fin 3) A) =
        if i = j then 1 else 0 := by
      intro i j
      simp [coeff_X, Finsupp.single_left_inj, eq_comm]
    -- the inner products
    obtain ⟨a0, a1, a2⟩ := lubinTatePhi_subst H hf (σ := Fin 3) (hX 1).1 (hX 2).1 (hX 1).2 (hX 2).2
    obtain ⟨b0, b1, b2⟩ := lubinTatePhi_subst H hf (σ := Fin 3) (hX 0).1 (hX 1).1 (hX 0).2 (hX 1).2
    obtain ⟨c0, c1, c2⟩ := lubinTatePhi_subst H hf (σ := Fin 3) (hX 0).1 a0 (hX 0).2 a2
    obtain ⟨d0, d1, d2⟩ := lubinTatePhi_subst H hf (σ := Fin 3) b0 (hX 2).1 b2 (hX 2).2
    have e1 := eq_lubinTatePhi H (σ := Fin 3) (fun _ => 1) hf hf c0
      (fun i => by rw [c1, a1]; fin_cases i <;> simp [hXc]) c2
    have e2 := eq_lubinTatePhi H (σ := Fin 3) (fun _ => 1) hf hf d0
      (fun i => by rw [d1, b1]; fin_cases i <;> simp [hXc]) d2
    exact e2.trans e1.symm

section FormalGroupLaw

variable (H : LubinTateHyp A π q) {f g h : PowerSeries A} (hf : f ∈ lubinTateSeries π q)
  (hg : g ∈ lubinTateSeries π q) (hh : h ∈ lubinTateSeries π q)

/-- **Proposition 2.12, commutativity** (Milne, *CFT*, I): $F_f(X,Y) = F_f(Y,X)$. -/
@[kb "milne2020cft" "Ch. I, Proposition 2.12 (commutativity)"]
instance lubinTateFormalGroup_isComm : (lubinTateFormalGroup H hf).IsComm := by
  refine ⟨?_⟩
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) A) = 0 ∧
      f.subst (X i : MvPowerSeries (Fin 2) A) =
        (X i : MvPowerSeries (Fin 2) A).subst (fun j => f.subst (X j : MvPowerSeries (Fin 2) A)) :=
    fun i => ⟨by simp, by rw [subst_X (hasSubst_twist hf.1)]⟩
  obtain ⟨c0, c1, c2⟩ := lubinTatePhi_subst H hf (σ := Fin 2) (hX 1).1 (hX 0).1 (hX 1).2 (hX 0).2
  exact (eq_lubinTatePhi H (σ := Fin 2) (fun _ => 1) hf hf c0
    (fun i => by rw [c1]; fin_cases i <;> simp [coeff_X, Finsupp.single_left_inj]) c2).symm

/-- **$f$ is an endomorphism of $F_f$** (Milne, *CFT*, I, Proposition 2.12). -/
@[kb "milne2020cft" "Ch. I, Proposition 2.12"]
def lubinTateEndo : FormalGroupHom (lubinTateFormalGroup H hf) (lubinTateFormalGroup H hf) where
  toPowerSeries := f
  constantCoeff_eq_zero := hf.1
  map_add := by
    have h := (lubinTatePhi_spec H (σ := Fin 2) (fun _ => 1) hf hf).2.2
    have h' : (fun i : Fin 2 => f.subst (X i : MvPowerSeries (Fin 2) A)) =
        ![f.subst (X 0 : MvPowerSeries (Fin 2) A), f.subst (X 1 : MvPowerSeries (Fin 2) A)] := by
      funext i; fin_cases i <;> rfl
    rw [h'] at h
    exact h

/-- **Uniqueness in Proposition 2.12** (Milne, *CFT*, I): $F_f$ is the only formal group law admitting $f$ as an
endomorphism. (Milne's formal group laws are commutative; uniqueness holds among all formal group laws.) -/
@[kb "milne2020cft" "Ch. I, Proposition 2.12 (uniqueness)"]
theorem eq_lubinTateFormalGroup (F : FormalGroup A)
    (hF : f.subst F.toPowerSeries = F.toPowerSeries.subst ![f.subst (X 0 : MvPowerSeries (Fin 2) A),
      f.subst (X 1 : MvPowerSeries (Fin 2) A)]) :
    F = lubinTateFormalGroup H hf := by
  refine FormalGroup.ext ?_
  refine eq_lubinTatePhi H (σ := Fin 2) (fun _ => 1) hf hf F.zero_constantCoeff (fun i => ?_) ?_
  · fin_cases i
    exacts [F.lin_coeff_X, F.lin_coeff_Y]
  · rw [hF]
    congr 1
    funext i; fin_cases i <;> rfl

/-- **$[a]_{g,f}$** (Milne, *CFT*, I, Proposition 2.14): for $f, g \in \mathcal F_\pi$ and $a \in A$, the unique
$[a]_{g,f}(T) = aT + (\deg \ge 2)$ with $g \circ [a]_{g,f} = [a]_{g,f} \circ f$ (Lemma 2.11 with one variable). -/
def lubinTateSeriesHom (a : A) : PowerSeries A :=
  lubinTatePhi H (σ := Unit) (fun _ => a) hg hf

/-- The defining properties of $[a]_{g,f}$: no constant term, linear coefficient $a$, and
$g \circ [a]_{g,f} = [a]_{g,f} \circ f$. -/
theorem lubinTateSeriesHom_spec (a : A) :
    PowerSeries.constantCoeff (lubinTateSeriesHom H hf hg a) = 0 ∧
      PowerSeries.coeff 1 (lubinTateSeriesHom H hf hg a) = a ∧
      g.subst (lubinTateSeriesHom H hf hg a) = (lubinTateSeriesHom H hf hg a).subst f := by
  obtain ⟨h0, h1, h2⟩ := lubinTatePhi_spec H (σ := Unit) (fun _ => a) hg hf
  refine ⟨h0, h1 (), ?_⟩
  rw [twist_unit] at h2
  exact h2

/-- Uniqueness of $[a]_{g,f}$. -/
theorem eq_lubinTateSeriesHom (a : A) {φ : PowerSeries A} (h0 : PowerSeries.constantCoeff φ = 0)
    (h1 : PowerSeries.coeff 1 φ = a) (h : g.subst φ = φ.subst f) :
    φ = lubinTateSeriesHom H hf hg a := by
  refine eq_lubinTatePhi H (σ := Unit) (fun _ => a) hg hf h0 (fun _ => h1) ?_
  rw [twist_unit]
  exact h

/-- **Proposition 2.14** (Milne, *CFT*, I): $[a]_{g,f}$ is a homomorphism $F_f \to F_g$. -/
@[kb "milne2020cft" "Ch. I, Proposition 2.14"]
def lubinTateHom (a : A) : FormalGroupHom (lubinTateFormalGroup H hf) (lubinTateFormalGroup H hg) where
  toPowerSeries := lubinTateSeriesHom H hf hg a
  constantCoeff_eq_zero := (lubinTateSeriesHom_spec H hf hg a).1
  map_add := by
    obtain ⟨U0, U1, U2⟩ := lubinTateSeriesHom_spec H hf hg a
    obtain ⟨F0, F1, F2⟩ := lubinTatePhi_spec H (σ := Fin 2) (fun _ => 1) hf hf
    obtain ⟨G0, G1, G2⟩ := lubinTatePhi_spec H (σ := Fin 2) (fun _ => 1) hg hg
    set U := lubinTateSeriesHom H hf hg a with hU
    set Ff := lubinTatePhi H (σ := Fin 2) (fun _ => 1) hf hf with hFf
    set Fg := lubinTatePhi H (σ := Fin 2) (fun _ => 1) hg hg with hFg
    have hFs : MvPowerSeries.HasSubst fun _ : Unit => Ff :=
      hasSubst_of_constantCoeff_zero fun _ => F0
    have hw0 : ∀ j : Fin 2, constantCoeff (U.subst (X j : MvPowerSeries (Fin 2) A)) = 0 :=
      fun j => constantCoeff_twist U0 j
    have e1 : U.subst Ff = lubinTatePhi H (σ := Fin 2) (fun _ => a) hg hf := by
      refine eq_lubinTatePhi H (σ := Fin 2) (fun _ => a) hg hf (φ := U.subst Ff) ?_ (fun i => ?_) ?_
      · exact PowerSeries.constantCoeff_subst_eq_zero F0 U U0
      · have := coeff_single_subst (τ := Unit) (P := U) U0
          (v := fun _ => Ff) (fun _ => F0) i
        change coeff (Finsupp.single i 1) (MvPowerSeries.subst (fun _ : Unit => Ff) U) = a
        rw [this]
        simp [F1]
        exact U1
      · have := subst_twist_comp (τ := Unit) (σ := Fin 2) (f := g) (g := f) (h := f) hf.1 hf.1
          (P := U) U0 (by rw [twist_unit]; exact U2) (v := fun _ => Ff) (fun _ => F0)
          (fun _ => F2)
        exact this
    have e2 : Fg.subst ![U.subst (X 0 : MvPowerSeries (Fin 2) A),
        U.subst (X 1 : MvPowerSeries (Fin 2) A)] =
        lubinTatePhi H (σ := Fin 2) (fun _ => a) hg hf := by
      have hw : ![U.subst (X 0 : MvPowerSeries (Fin 2) A), U.subst (X 1 : MvPowerSeries (Fin 2) A)] =
          fun j => U.subst (X j : MvPowerSeries (Fin 2) A) := by
        funext j; fin_cases j <;> rfl
      rw [hw]
      refine eq_lubinTatePhi H (σ := Fin 2) (fun _ => a) hg hf (φ := _) ?_ (fun i => ?_) ?_
      · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hw0) hw0 G0
      · rw [coeff_single_subst G0 hw0]
        have hc : ∀ j : Fin 2, coeff (Finsupp.single i 1) (U.subst (X j : MvPowerSeries (Fin 2) A)) =
            if i = j then a else 0 := by
          intro j
          have := coeff_single_subst (τ := Unit) (P := U) U0
            (v := fun _ => (X j : MvPowerSeries (Fin 2) A)) (fun _ => by simp) i
          change coeff (Finsupp.single i 1) (MvPowerSeries.subst (fun _ : Unit => (X j : MvPowerSeries (Fin 2) A)) U) = _
          rw [this]
          simp [coeff_X, Finsupp.single_left_inj]
          rw [U1]
        simp [hc, G1]
      · refine subst_twist_comp (f := g) (g := g) (h := f) hg.1 hf.1 G0 G2 hw0 (fun j => ?_)
        have hXs : MvPowerSeries.HasSubst fun _ : Unit => (X j : MvPowerSeries (Fin 2) A) :=
          hasSubst_of_constantCoeff_zero fun _ => by simp
        have h1 := mvSubst_powerSeriesSubst (φ := U) U0 g hXs
        change g.subst (MvPowerSeries.subst (fun _ : Unit => (X j : MvPowerSeries (Fin 2) A)) U) = _
        rw [← h1, U2]
        change MvPowerSeries.subst (fun _ : Unit => (X j : MvPowerSeries (Fin 2) A))
          (MvPowerSeries.subst (fun _ : Unit => f) U) = MvPowerSeries.subst
            (fun i => f.subst (X i : MvPowerSeries (Fin 2) A))
            (MvPowerSeries.subst (fun _ : Unit => (X j : MvPowerSeries (Fin 2) A)) U)
        have hfs : MvPowerSeries.HasSubst fun _ : Unit => f :=
          (PowerSeries.HasSubst.of_constantCoeff_zero' hf.1).const
        rw [subst_comp_subst_apply hfs hXs, subst_comp_subst_apply hXs (hasSubst_twist hf.1)]
        congr 1
        funext _
        rw [subst_X (hasSubst_twist hf.1)]
        rfl
    exact e1.trans e2.symm

/-- **Proposition 2.15, additivity** (Milne, *CFT*, I): $[a+b]_{g,f} = [a]_{g,f} +_{F_g} [b]_{g,f}$, where
$u +_{F_g} v = F_g(u(T), v(T))$. -/
@[kb "milne2020cft" "Ch. I, Proposition 2.15"]
theorem lubinTateSeriesHom_add (a b : A) :
    lubinTateSeriesHom H hf hg (a + b) =
      (lubinTateFormalGroup H hg).toPowerSeries.subst
        ![lubinTateSeriesHom H hf hg a, lubinTateSeriesHom H hf hg b] := by
  obtain ⟨Ua0, Ua1, Ua2⟩ := lubinTateSeriesHom_spec H hf hg a
  obtain ⟨Ub0, Ub1, Ub2⟩ := lubinTateSeriesHom_spec H hf hg b
  obtain ⟨G0, G1, G2⟩ := lubinTatePhi_spec H (σ := Fin 2) (fun _ => 1) hg hg
  have hv0 : ∀ j : Fin 2, constantCoeff (![lubinTateSeriesHom H hf hg a,
      lubinTateSeriesHom H hf hg b] j) = 0 := by
    intro j; fin_cases j
    exacts [Ua0, Ub0]
  refine (eq_lubinTateSeriesHom H hf hg (a + b) (g := g) ?_ ?_ ?_).symm
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hv0) hv0 G0
  · change coeff (Finsupp.single () 1) (MvPowerSeries.subst _
      (lubinTatePhi H (σ := Fin 2) (fun _ => 1) hg hg)) = _
    rw [coeff_single_subst G0 hv0]
    simp [Fin.sum_univ_two, G1]
    exact congrArg₂ (· + ·) Ua1 Ub1
  · have := subst_twist_comp (τ := Fin 2) (σ := Unit) (f := g) (g := g) (h := f) hg.1 hf.1 G0 G2
      hv0 (fun j => by
        rw [twist_unit]
        fin_cases j
        exacts [Ua2, Ub2])
    rw [twist_unit] at this
    exact this

/-- **Proposition 2.15, multiplicativity** (Milne, *CFT*, I): $[ab]_{h,f} = [a]_{h,g} \circ [b]_{g,f}$. -/
@[kb "milne2020cft" "Ch. I, Proposition 2.15"]
theorem lubinTateSeriesHom_mul (a b : A) :
    lubinTateSeriesHom H hf hh (a * b) =
      (lubinTateSeriesHom H hg hh a).subst (lubinTateSeriesHom H hf hg b) := by
  obtain ⟨Ua0, Ua1, Ua2⟩ := lubinTateSeriesHom_spec H hg hh a
  obtain ⟨Ub0, Ub1, Ub2⟩ := lubinTateSeriesHom_spec H hf hg b
  set Ua := lubinTateSeriesHom H hg hh a
  set Ub := lubinTateSeriesHom H hf hg b
  have hUa : PowerSeries.HasSubst Ua := PowerSeries.HasSubst.of_constantCoeff_zero' Ua0
  have hUb : PowerSeries.HasSubst Ub := PowerSeries.HasSubst.of_constantCoeff_zero' Ub0
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf.1
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg.1
  refine (eq_lubinTateSeriesHom H hf hh (a * b) ?_ ?_ ?_).symm
  · exact PowerSeries.constantCoeff_subst_eq_zero Ub0 Ua Ua0
  · change coeff (Finsupp.single () 1) (MvPowerSeries.subst (fun _ : Unit => Ub) Ua) = _
    rw [coeff_single_subst (τ := Unit) Ua0 (v := fun _ => Ub) (fun _ => Ub0)]
    simp
    rw [← Ua1, ← Ub1]
  · rw [← PowerSeries.subst_comp_subst_apply hUa hUb, Ua2,
      PowerSeries.subst_comp_subst_apply hgs hUb]
    rw [Ub2]
    exact (PowerSeries.subst_comp_subst_apply hUb hfs Ua).symm

/-- $[1]_{f,f} = T$. -/
theorem lubinTateSeriesHom_self_one : lubinTateSeriesHom H hf hf 1 = PowerSeries.X := by
  refine (eq_lubinTateSeriesHom H hf hf 1 (φ := PowerSeries.X) (by simp) (by simp) ?_).symm
  rw [PowerSeries.X_subst, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hf.1)]

/-- **Corollary 2.16** (Milne, *CFT*, I, and the remark after it): $[1]_{g,f} : F_f \to F_g$ is an isomorphism
(with inverse $[1]_{f,g}$). -/
@[kb "milne2020cft" "Ch. I, Corollary 2.16"]
theorem isIso_lubinTateHom_one : (lubinTateHom H hf hg 1).IsIso := by
  refine ⟨lubinTateHom H hg hf 1, ?_, ?_⟩
  · have h := lubinTateSeriesHom_mul H hg hf hg 1 1
    rw [mul_one, lubinTateSeriesHom_self_one] at h
    exact h.symm
  · have h := lubinTateSeriesHom_mul H hf hg hf 1 1
    rw [mul_one, lubinTateSeriesHom_self_one] at h
    exact h.symm

/-- **Corollary 2.16** (Milne, *CFT*, I): any two Lubin–Tate formal group laws for the same prime element are
isomorphic, $F_f \cong F_g$. -/
@[kb "milne2020cft" "Ch. I, Corollary 2.16"]
theorem nonempty_iso :
    ∃ φ : FormalGroupHom (lubinTateFormalGroup H hf) (lubinTateFormalGroup H hg), φ.IsIso :=
  ⟨_, isIso_lubinTateHom_one H hf hg⟩

/-- **$[a]_f$** (Milne, *CFT*, I, Corollary 2.17): the endomorphism $[a]_{f,f}$ of $F_f$, the unique power series
$aT + (\deg \ge 2)$ commuting with $f$. -/
@[kb "milne2020cft" "Ch. I, Corollary 2.17"]
def lubinTateEnd (a : A) : FormalGroupHom (lubinTateFormalGroup H hf) (lubinTateFormalGroup H hf) :=
  lubinTateHom H hf hf a

/-- **Corollary 2.17** (Milne, *CFT*, I): $a \mapsto [a]_f$ is a ring homomorphism $A \to \mathrm{End}(F_f)$
(the ring of Lemma 2.8 (b)). -/
@[kb "milne2020cft" "Ch. I, Corollary 2.17"]
def lubinTateEndRingHom : A →+* FormalGroupHom (lubinTateFormalGroup H hf) (lubinTateFormalGroup H hf) where
  toFun := lubinTateEnd H hf
  map_one' := by
    refine FormalGroupHom.ext ?_
    rw [FormalGroupHom.one_toPowerSeries]
    exact lubinTateSeriesHom_self_one H hf
  map_mul' := fun x y => by
    refine FormalGroupHom.ext ?_
    rw [FormalGroupHom.mul_toPowerSeries]
    exact lubinTateSeriesHom_mul H hf hf hf x y
  map_zero' := by
    refine FormalGroupHom.ext ?_
    rw [FormalGroupHom.zero_toPowerSeries]
    refine (eq_lubinTateSeriesHom H hf hf 0 (φ := 0) (by simp) (by simp) ?_).symm
    have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf.1
    rw [PowerSeries.subst_zero_of_constantCoeff_zero hf.1, ← PowerSeries.coe_substAlgHom hfs,
      map_zero]
  map_add' := fun x y => by
    refine FormalGroupHom.ext ?_
    rw [FormalGroupHom.add_toPowerSeries]
    exact lubinTateSeriesHom_add H hf hf x y

theorem lubinTateEndRingHom_apply (a : A) : lubinTateEndRingHom H hf a = lubinTateEnd H hf a := rfl

/-- **Remark 2.19 (a)** (Milne, *CFT*, I): $[\pi]_f = f$. -/
@[kb "milne2020cft" "Ch. I, Remark 2.19 (a)"]
theorem lubinTateEnd_pi : (lubinTateEnd H hf π).toPowerSeries = f :=
  (eq_lubinTateSeriesHom H hf hf π (φ := f) hf.1 hf.2.1 rfl).symm

/-- **Remark 2.19 (b)** (Milne, *CFT*, I): $a \mapsto [a]_f$ is injective ($a$ is the linear coefficient). -/
@[kb "milne2020cft" "Ch. I, Remark 2.19 (b); Corollary 2.17 (injectivity)"]
theorem lubinTateEndRingHom_injective : Function.Injective (lubinTateEndRingHom H hf) := by
  intro a b hab
  have h := congrArg (fun x => PowerSeries.coeff 1 x.toPowerSeries) hab
  change PowerSeries.coeff 1 (lubinTateSeriesHom H hf hf a) =
    PowerSeries.coeff 1 (lubinTateSeriesHom H hf hf b) at h
  rwa [(lubinTateSeriesHom_spec H hf hf a).2.1, (lubinTateSeriesHom_spec H hf hf b).2.1] at h

/-- **Remark 2.19 (c)** (Milne, *CFT*, I): the canonical isomorphism $[1]_{g,f}$ commutes with the $A$-actions:
$[a]_g \circ [1]_{g,f} = [a]_{g,f} = [1]_{g,f} \circ [a]_f$. -/
@[kb "milne2020cft" "Ch. I, Remark 2.19 (c)"]
theorem lubinTateEnd_comp_one (a : A) :
    (lubinTateEnd H hg a).toPowerSeries.subst (lubinTateSeriesHom H hf hg 1) =
        lubinTateSeriesHom H hf hg a ∧
      (lubinTateSeriesHom H hf hg 1).subst (lubinTateEnd H hf a).toPowerSeries =
        lubinTateSeriesHom H hf hg a := by
  constructor
  · have h := lubinTateSeriesHom_mul H hf hg hg a 1
    rw [mul_one] at h
    exact h.symm
  · have h := lubinTateSeriesHom_mul H hf hf hg 1 a
    rw [one_mul] at h
    exact h.symm

end FormalGroupLaw

end NumberFieldKB.MilneCFT
