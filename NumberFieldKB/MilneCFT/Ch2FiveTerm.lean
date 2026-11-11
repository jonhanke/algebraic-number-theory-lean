import Mathlib.Tactic.Have
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Remarks

/-!
# Milne, *Class Field Theory*, Chapter II: Remark 1.35 (a), the five-term sequence

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

A proof of the named statement `Remark1_35` (Ch2Remarks) for an arbitrary (discrete) group `G`, in Mathlib's
explicit low-degree cochain API. The construction is the one of the profinite port
(`NumberFieldKB/TauCetiPort/.../ContCohomology/Transgression.lean`), with the compactness hypothesis
(used there only to choose continuous lifts) removed.

* `FiveTerm.IsTLift c f`: `f : G → M` is a *transgression lift* of `c : H → M`, i.e.
  `f (g h) = f g + g c(h)` and `g c(g⁻¹ h g) - c h = h f(g) - f(g)`.
* `FiveTerm.IsTLift.descC`: the coboundary `d f` descends to a 2-cocycle on `G/H` with values in `M^H`.
* `FiveTerm.exists_lift`: a cocycle with `G`-fixed class has a lift (choice of coset representatives).
* `FiveTerm.tg`: the transgression `H¹(H, M)^{G/H} → H²(G/H, M^H)`, well defined by
  `FiveTerm.IsTLift.descC_indep` and additive by `FiveTerm.IsTLift.descC_add`.
* `FiveTerm.part_i`, `FiveTerm.tg_eq_zero_iff`, `FiveTerm.inf_eq_zero_iff`: the three conjuncts.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits

namespace FiveTerm

variable {G : Type} [Group G] {H : Subgroup G} [H.Normal] {M : Rep ℤ G}

theorem conjNormal_inv_coe (g : G) (h : H) : ((conjNormal H g⁻¹ h : H) : G) = g⁻¹ * h * g := by
  rw [conjNormal_apply, inv_inv]

theorem conjAction_H1π (c : cocycles₁ (res H.subtype M)) (g : G) :
    conjAction H M 1 g (H1π _ c) =
      H1π _ (mapCocycles₁ (conjNormal H g) (conjNormalCompat H g M) c) := by
  have := H1π_comp_map (A := res H.subtype M) (conjNormal H g) (conjNormalCompat H g M)
  exact congr($this c)

theorem coe_mapCocycles₁_conj (c : cocycles₁ (res H.subtype M)) (g : G) (h : H) :
    (mapCocycles₁ (conjNormal H g) (conjNormalCompat H g M) c) h =
      M.ρ g⁻¹ (c (conjNormal H g h)) := rfl

theorem H1π_mem_H1Fixed_iff (c : cocycles₁ (res H.subtype M)) :
    H1π _ c ∈ H1Fixed H M ↔ ∀ g : G, ∃ m : M, ∀ h : H,
      M.ρ g (c (conjNormal H g⁻¹ h)) - c h = M.ρ h m - m := by
  constructor
  · intro hx g
    have h1 := hx g⁻¹
    rw [conjAction_H1π, H1π_eq_iff] at h1
    obtain ⟨m, hm⟩ := h1
    refine ⟨m, fun h => ?_⟩
    have key : M.ρ h m - m = M.ρ g⁻¹⁻¹ (c (conjNormal H g⁻¹ h)) - c h := congr_fun hm h
    rw [inv_inv] at key
    exact key.symm
  · intro hx g
    show conjAction H M 1 g (H1π _ c) = H1π _ c
    rw [conjAction_H1π, H1π_eq_iff]
    obtain ⟨m, hm⟩ := hx g⁻¹
    refine ⟨m, funext fun h => ?_⟩
    have key := hm h
    rw [inv_inv] at key
    exact key.symm

/-- A transgression lift. -/
structure IsTLift (c : H → M) (f : G → M) : Prop where
  apply_mul : ∀ (g : G) (h : H), f (g * h) = f g + M.ρ g (c h)
  conj : ∀ (g : G) (h : H),
    M.ρ g (c (conjNormal H g⁻¹ h)) - c h = M.ρ h (f g) - f g

theorem IsTLift.mem_H1Fixed {c : cocycles₁ (res H.subtype M)} {f : G → M}
    (hf : IsTLift (H := H) (M := M) c f) : H1π _ c ∈ H1Fixed H M :=
  (H1π_mem_H1Fixed_iff c).2 fun g => ⟨f g, hf.conj g⟩

theorem isTLift_of_cocycle {c : G → M} (hc : c ∈ cocycles₁ M) :
    IsTLift (H := H) (fun h : H => c h) c where
  apply_mul g h := by
    rw [(mem_cocycles₁_iff c).1 hc g h]; abel
  conj g h := by
    have h1 := (mem_cocycles₁_iff c).1 hc g (g⁻¹ * h * g)
    have h2 := (mem_cocycles₁_iff c).1 hc h g
    have e : g * (g⁻¹ * (h : G) * g) = h * g := by group
    rw [e, h2] at h1
    simp only [conjNormal_inv_coe]
    change M.ρ g (c (g⁻¹ * h * g)) - c h = _
    have := eq_sub_of_add_eq h1.symm
    rw [this]; abel


theorem ρ_mul' (a b : G) (x : M) : M.ρ (a * b) x = M.ρ a (M.ρ b x) := by
  rw [map_mul]; rfl

theorem conj_calc (c : cocycles₁ (res H.subtype M)) (F : M) (T : G) (U h : H)
    (hF : M.ρ T (c (conjNormal H T⁻¹ h)) - c h = M.ρ h F - F) :
    M.ρ (T * U) (c (conjNormal H (T * U)⁻¹ h)) - c h =
      M.ρ h (F + M.ρ T (c U)) - (F + M.ρ T (c U)) := by
  have hcc : ∀ a b : H, c (a * b) = M.ρ a (c b) + c a := (mem_cocycles₁_iff _).1 c.2
  set h' := conjNormal H T⁻¹ h with hh'
  have hk : conjNormal H (T * U)⁻¹ h = U⁻¹ * (h' * U) := by
    apply Subtype.ext
    simp [hh', conjNormal_apply, mul_assoc]
  have hinv : M.ρ U (c U⁻¹) = - c U := cocycles₁_map_inv c U
  have step1 : M.ρ U (c (U⁻¹ * (h' * U))) = c h' + M.ρ h' (c U) - c U := by
    rw [hcc U⁻¹ (h' * U), hcc h' U, map_add, map_add, hinv]
    simp only [← ρ_mul', Subgroup.coe_inv]
    simp
    abel
  have hcomm : ∀ x : M, M.ρ T (M.ρ h' x) = M.ρ h (M.ρ T x) := by
    intro x
    rw [← ρ_mul', ← ρ_mul']
    congr 2
    simp [hh', conjNormal_apply]
    group
  rw [hk, ρ_mul', step1]
  simp only [map_add, map_sub, hcomm]
  have hF' := eq_add_of_sub_eq hF
  rw [hF']
  abel


theorem exists_lift (c : cocycles₁ (res H.subtype M)) (hc : H1π _ c ∈ H1Fixed H M) :
    ∃ f : G → M, IsTLift (H := H) (M := M) c f := by
  have hcc : ∀ a b : H, c (a * b) = M.ρ a (c b) + c a := (mem_cocycles₁_iff _).1 c.2
  choose F hF using (H1π_mem_H1Fixed_iff c).1 hc
  let t : G → G := fun g => (QuotientGroup.mk g : G ⧸ H).out
  have ht : ∀ g, (t g)⁻¹ * g ∈ H := fun g => QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  let u : G → H := fun g => ⟨(t g)⁻¹ * g, ht g⟩
  have ht_mul : ∀ (g : G) (h : H), t (g * h) = t g := by
    intro g h
    simp only [t]
    rw [QuotientGroup.mk_mul_of_mem g h.2]
  have hu_mul : ∀ (g : G) (h : H), u (g * h) = u g * h := by
    intro g h
    apply Subtype.ext
    simp only [u]
    rw [ht_mul]
    simp [mul_assoc]
  have hg : ∀ g, t g * (u g : G) = g := fun g => by simp [u]
  refine ⟨fun g => F (t g) + M.ρ (t g) (c (u g)), fun g h => ?_, fun g h => ?_⟩
  · show F (t (g * h)) + M.ρ (t (g * h)) (c (u (g * h))) = _
    rw [ht_mul, hu_mul, hcc, map_add]
    have : M.ρ g (c h) = M.ρ (t g) (M.ρ (u g) (c h)) := by rw [← ρ_mul', hg]
    show _ = F (t g) + M.ρ (t g) (c (u g)) + M.ρ g (c h)
    rw [this]
    abel
  · have := conj_calc c (F (t g)) (t g) (u g) h (hF (t g) h)
    rw [hg g] at this
    exact this


/-- The coboundary of a function `f : G → M`. -/
def dd (f : G → M) : G × G → M := fun p => M.ρ p.1 (f p.2) - f (p.1 * p.2) + f p.1

theorem dd_cocycle (f : G → M) (g h k : G) :
    dd f (g * h, k) + dd f (g, h) = M.ρ g (dd f (h, k)) + dd f (g, h * k) := by
  simp only [dd, map_sub, map_add, ρ_mul', mul_assoc]
  abel

theorem dd_mem (f : G → M) : dd f ∈ cocycles₂ M :=
  (mem_cocycles₂_iff _).2 (dd_cocycle f)

/-! Descent to the quotient. -/

/-- Descent of a function on `G × G` to `(G/H) × (G/H)` with values in `M^H`. -/
noncomputable def liftQ₂ (F : G × G → M) (hI : ∀ (n : H) g h, M.ρ n (F (g, h)) = F (g, h)) :
    (G ⧸ H) × (G ⧸ H) → M.quotientToInvariants H :=
  fun p => ⟨F (p.1.out, p.2.out), fun n => hI n _ _⟩

theorem coe_liftQ₂_mk (F : G × G → M) (hI : ∀ (n : H) g h, M.ρ n (F (g, h)) = F (g, h))
    (hR : ∀ g h (n : H), F (g, h * n) = F (g, h)) (hL : ∀ g h (n : H), F (g * n, h) = F (g, h))
    (g h : G) :
    ((liftQ₂ F hI (QuotientGroup.mk g, QuotientGroup.mk h) : M.quotientToInvariants H) : M) =
      F (g, h) := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul H g
  obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul H h
  show F ((QuotientGroup.mk g : G ⧸ H).out, (QuotientGroup.mk h : G ⧸ H).out) = _
  rw [ha, hb, hL, hR]

/-- Descent of a function on `G` to `G/H` with values in `M^H`. -/
noncomputable def liftQ₁ (F : G → M) (hI : ∀ (n : H) g, M.ρ n (F g) = F g) :
    (G ⧸ H) → M.quotientToInvariants H :=
  fun q => ⟨F q.out, fun n => hI n _⟩

theorem coe_liftQ₁_mk (F : G → M) (hI : ∀ (n : H) g, M.ρ n (F g) = F g)
    (hR : ∀ g (n : H), F (g * n) = F g) (g : G) :
    ((liftQ₁ F hI (QuotientGroup.mk g) : M.quotientToInvariants H) : M) = F g := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul H g
  show F ((QuotientGroup.mk g : G ⧸ H).out) = _
  rw [ha, hR]


section lift
variable {c : H → M} {f : G → M}

theorem IsTLift.dd_right (hf : IsTLift c f) (g h : G) (n : H) :
    dd f (g, h * n) = dd f (g, h) := by
  simp only [dd]
  rw [← mul_assoc, hf.apply_mul h n, hf.apply_mul (g * h) n, map_add, ρ_mul']
  abel

theorem IsTLift.dd_left (hf : IsTLift c f) (g h : G) (n : H) :
    dd f (g * n, h) = dd f (g, h) := by
  have hmul : g * (n : G) * h = g * h * ((conjNormal H h⁻¹ n : H) : G) := by
    rw [conjNormal_inv_coe]; group
  have hconj := hf.conj h n
  have hn : M.ρ n (f h) = M.ρ h (c (conjNormal H h⁻¹ n)) - c n + f h :=
    eq_add_of_sub_eq hconj.symm
  simp only [dd]
  rw [hmul, hf.apply_mul (g * h), hf.apply_mul g n, ρ_mul' g, ρ_mul' g h, hn]
  simp only [map_add, map_sub]
  abel

theorem IsTLift.dd_one_left (hf : IsTLift c f) (n : H) (x : G) :
    dd f (n, x) = f 1 := by
  have hmul : (n : G) * x = x * ((conjNormal H x⁻¹ n : H) : G) := by
    rw [conjNormal_inv_coe]; group
  have hconj := hf.conj x n
  have hn : M.ρ n (f x) = M.ρ x (c (conjNormal H x⁻¹ n)) - c n + f x :=
    eq_add_of_sub_eq hconj.symm
  have h1 := hf.apply_mul 1 n
  rw [one_mul, map_one, Module.End.one_apply] at h1
  simp only [dd]
  rw [hmul, hf.apply_mul x, hn, h1]
  abel

theorem IsTLift.dd_inv (hf : IsTLift c f) (n : H) (g h : G) :
    M.ρ n (dd f (g, h)) = dd f (g, h) := by
  have h2 := dd_cocycle f n g h
  have hmul : (n : G) * g = g * ((conjNormal H g⁻¹ n : H) : G) := by
    rw [conjNormal_inv_coe]; group
  rw [hmul, hf.dd_left, hf.dd_one_left, hf.dd_one_left] at h2
  exact add_right_cancel (h2.symm.trans (by rw [add_comm]))


theorem quot_ρ_coe (g : G) (x : M.quotientToInvariants H) :
    (((M.quotientToInvariants H).ρ (QuotientGroup.mk g) x : _) : M) = M.ρ g (x : M) := rfl

/-- The descended coboundary of a lift, as a function on `(G/H)²`. -/
noncomputable def IsTLift.lift (hf : IsTLift c f) :
    (G ⧸ H) × (G ⧸ H) → M.quotientToInvariants H :=
  liftQ₂ (dd f) hf.dd_inv

theorem IsTLift.coe_lift (hf : IsTLift c f) (g h : G) :
    ((hf.lift (QuotientGroup.mk g, QuotientGroup.mk h) : M.quotientToInvariants H) : M) =
      dd f (g, h) :=
  coe_liftQ₂_mk _ _ (fun g h n => hf.dd_right g h n) (fun g h n => hf.dd_left g h n) g h

/-- The descended coboundary of a lift, as a 2-cocycle on `G/H` with values in `M^H`. -/
noncomputable def IsTLift.descC (hf : IsTLift c f) : cocycles₂ (M.quotientToInvariants H) :=
  ⟨hf.lift, (mem_cocycles₂_iff _).2 (by
    intro q r s
    induction q using QuotientGroup.induction_on with | H a => ?_
    induction r using QuotientGroup.induction_on with | H b => ?_
    induction s using QuotientGroup.induction_on with | H d => ?_
    apply Subtype.ext
    show (((hf.lift (QuotientGroup.mk (a * b), QuotientGroup.mk d) :
        M.quotientToInvariants H) : M) +
        ((hf.lift (QuotientGroup.mk a, QuotientGroup.mk b) : M.quotientToInvariants H) : M)) =
      M.ρ a ((hf.lift (QuotientGroup.mk b, QuotientGroup.mk d) : M.quotientToInvariants H) : M) +
        ((hf.lift (QuotientGroup.mk a, QuotientGroup.mk (b * d)) :
          M.quotientToInvariants H) : M)
    rw [hf.coe_lift, hf.coe_lift, hf.coe_lift, hf.coe_lift]
    exact dd_cocycle f a b d)⟩

theorem IsTLift.descC_apply (hf : IsTLift c f) (g h : G) :
    ((hf.descC (QuotientGroup.mk g, QuotientGroup.mk h) : M.quotientToInvariants H) : M) =
      dd f (g, h) := hf.coe_lift g h


theorem IsTLift.add {c' : H → M} {f' : G → M} (hf : IsTLift c f) (hf' : IsTLift c' f') :
    IsTLift (c + c') (f + f') where
  apply_mul g h := by
    simp only [Pi.add_apply, hf.apply_mul, hf'.apply_mul, map_add]
    abel
  conj g h := by
    have e1 := hf.conj g h
    have e2 := hf'.conj g h
    simp only [Pi.add_apply, map_add]
    rw [add_sub_add_comm, e1, e2, add_sub_add_comm]

theorem dd_add (f f' : G → M) : dd (f + f') = dd f + dd f' := by
  funext p
  simp only [dd, Pi.add_apply, map_add]
  abel

theorem IsTLift.descC_add {c' : H → M} {f' : G → M} (hf : IsTLift c f) (hf' : IsTLift c' f') :
    (hf.add hf').descC = hf.descC + hf'.descC := by
  refine cocycles₂_ext fun q r => ?_
  induction q using QuotientGroup.induction_on with | H a => ?_
  induction r using QuotientGroup.induction_on with | H b => ?_
  apply Subtype.ext
  show ((((hf.add hf').descC (QuotientGroup.mk a, QuotientGroup.mk b) :
      M.quotientToInvariants H)) : M) = ((hf.descC (QuotientGroup.mk a, QuotientGroup.mk b) :
      M.quotientToInvariants H) : M) + ((hf'.descC (QuotientGroup.mk a, QuotientGroup.mk b) :
      M.quotientToInvariants H) : M)
  rw [(hf.add hf').descC_apply, hf.descC_apply, hf'.descC_apply, dd_add]
  rfl

theorem IsTLift.descC_indep {c' : H → M} {f' : G → M} (hf : IsTLift c f) (hf' : IsTLift c' f')
    (m : M) (hm : ∀ h : H, c h - c' h = M.ρ h m - m) :
    H2π _ hf.descC = H2π _ hf'.descC := by
  set e : G → M := fun g => f g - f' g - (M.ρ g m - m) with he
  have e_mul : ∀ (g : G) (n : H), e (g * n) = e g := by
    intro g n
    have := hm n
    have h1 := eq_add_of_sub_eq (hm n)
    simp only [he]
    rw [hf.apply_mul, hf'.apply_mul, h1, ρ_mul']
    simp only [map_add, map_sub]
    abel
  have e_inv : ∀ (n : H) g, M.ρ n (e g) = e g := by
    intro n g
    set k := conjNormal H g⁻¹ n with hk
    have hgk : g * (k : G) = n * g := by
      rw [hk, conjNormal_inv_coe]; group
    have A := eq_add_of_sub_eq (hf.conj g n).symm
    have B := eq_add_of_sub_eq (hf'.conj g n).symm
    have Cm := eq_add_of_sub_eq (hm k)
    have Dm := eq_add_of_sub_eq (hm n)
    rw [← hk] at A B
    have hC : M.ρ g (c k) = M.ρ g (c' k) + (M.ρ n (M.ρ g m) - M.ρ g m) := by
      rw [Cm, map_add, map_sub, ← ρ_mul', hgk, ρ_mul']
      abel
    simp only [he]
    rw [map_sub, map_sub, map_sub, A, B, hC, Dm]
    abel
  refine (H2π_eq_iff _ _).2 ⟨liftQ₁ e e_inv, ?_⟩
  funext p
  obtain ⟨q, r⟩ := p
  induction q using QuotientGroup.induction_on with | H a => ?_
  induction r using QuotientGroup.induction_on with | H b => ?_
  apply Subtype.ext
  show M.ρ a ((liftQ₁ e e_inv (QuotientGroup.mk b) : M.quotientToInvariants H) : M) -
      ((liftQ₁ e e_inv (QuotientGroup.mk (a * b)) : M.quotientToInvariants H) : M) +
      ((liftQ₁ e e_inv (QuotientGroup.mk a) : M.quotientToInvariants H) : M) =
    ((hf.descC (QuotientGroup.mk a, QuotientGroup.mk b) : M.quotientToInvariants H) : M) -
      ((hf'.descC (QuotientGroup.mk a, QuotientGroup.mk b) : M.quotientToInvariants H) : M)
  rw [coe_liftQ₁_mk e e_inv e_mul, coe_liftQ₁_mk e e_inv e_mul, coe_liftQ₁_mk e e_inv e_mul,
    hf.descC_apply, hf'.descC_apply]
  simp only [he, dd, ρ_mul', map_sub]
  abel

end lift


theorem tgAux (y : H1Fixed H M) :
    ∃ (c : cocycles₁ (res H.subtype M)) (f : G → M), H1π _ c = y.1 ∧ IsTLift (H := H) (M := M) c f := by
  have : ∀ x : groupCohomology (res H.subtype M) 1, x ∈ H1Fixed H M →
      ∃ (c : cocycles₁ (res H.subtype M)) (f : G → M), H1π _ c = x ∧ IsTLift (H := H) (M := M) c f := by
    intro x
    induction x using H1_induction_on with | h c =>
    intro hc
    obtain ⟨f, hf⟩ := exists_lift c hc
    exact ⟨c, f, rfl, hf⟩
  exact this y.1 y.2

/-- The transgression on a chosen representative. -/
noncomputable def tgFun (y : H1Fixed H M) : groupCohomology (M.quotientToInvariants H) 2 :=
  H2π _ (tgAux y).choose_spec.choose_spec.2.descC

theorem tgFun_eq (y : H1Fixed H M) (c : cocycles₁ (res H.subtype M)) (f : G → M)
    (hc : H1π _ c = y.1) (hf : IsTLift (H := H) (M := M) c f) : tgFun y = H2π _ hf.descC := by
  obtain ⟨hc0, -⟩ := (tgAux y).choose_spec.choose_spec
  have h0 : H1π _ (tgAux y).choose = H1π _ c := hc0.trans hc.symm
  rw [H1π_eq_iff] at h0
  obtain ⟨m, hm⟩ := h0
  exact IsTLift.descC_indep (c := ⇑(tgAux y).choose) (c' := ⇑c) _ hf m (fun h => by
    have := congr_fun hm h
    simpa using this.symm)

/-- **The transgression** `H¹(H, M)^{G/H} → H²(G/H, M^H)`. -/
noncomputable def tg : H1Fixed H M →+ groupCohomology (M.quotientToInvariants H) 2 :=
  AddMonoidHom.mk' tgFun fun y y' => by
    obtain ⟨c, f, hc, hf⟩ := tgAux y
    obtain ⟨c', f', hc', hf'⟩ := tgAux y'
    have hf'' : IsTLift (H := H) (M := M) (c + c' : cocycles₁ (res H.subtype M)) (f + f') :=
      hf.add hf'
    rw [tgFun_eq y c f hc hf, tgFun_eq y' c' f' hc' hf',
      tgFun_eq (y + y') (c + c') (f + f') (by rw [map_add, hc, hc']; rfl) hf'', IsTLift.descC_add,
      map_add]

theorem tg_apply (y : H1Fixed H M) (c : cocycles₁ (res H.subtype M)) (f : G → M)
    (hc : H1π _ c = y.1) (hf : IsTLift (H := H) (M := M) c f) : tg y = H2π _ hf.descC :=
  tgFun_eq y c f hc hf

theorem res_H1π (c : cocycles₁ M) :
    (HInfRes M H 1).g (H1π M c) = H1π _ (mapCocycles₁ H.subtype (𝟙 (res H.subtype M)) c) := by
  have := H1π_comp_map (A := M) H.subtype (𝟙 (res H.subtype M))
  exact congr($this c)

theorem part_i (x : groupCohomology M 1) : (HInfRes M H 1).g x ∈ H1Fixed H M := by
  induction x using H1_induction_on with | h c =>
  rw [res_H1π]
  exact IsTLift.mem_H1Fixed (f := ⇑c) (isTLift_of_cocycle c.2)


theorem dd_sub (f f' : G → M) : dd (f - f') = dd f - dd f' := by
  funext p
  simp only [dd, Pi.sub_apply, map_sub]
  abel

theorem tg_eq_zero_iff (y : H1Fixed H M) :
    tg y = 0 ↔ ∃ x : groupCohomology M 1, (HInfRes M H 1).g x = y.1 := by
  constructor
  · intro h0
    obtain ⟨c, f, hc, hf⟩ := tgAux y
    rw [tg_apply y c f hc hf, H2π_eq_zero_iff] at h0
    obtain ⟨u, hu⟩ := h0
    set p : G → M := fun g => ((u (QuotientGroup.mk g) : M.quotientToInvariants H) : M) with hp
    have hpp : ∀ a b : G, M.ρ a (p b) - p (a * b) + p a = dd f (a, b) := by
      intro a b
      have key := congr_arg (fun x : M.quotientToInvariants H => (x : M))
        (congr_fun hu (QuotientGroup.mk a, QuotientGroup.mk b))
      exact key.trans (hf.descC_apply a b)
    have hdd : ∀ a b, dd (f - p) (a, b) = 0 := by
      intro a b
      rw [dd_sub]
      have := hpp a b
      simp only [Pi.sub_apply]
      rw [sub_eq_zero]
      exact this.symm
    have hmem : (f - p) ∈ cocycles₁ M := by
      rw [mem_cocycles₁_iff]
      intro g h
      have h1 := hdd g h
      simp only [dd] at h1
      have e : (f - p) (g * h) - (M.ρ g ((f - p) h) + (f - p) g) =
          -(M.ρ g ((f - p) h) - (f - p) (g * h) + (f - p) g) := by abel
      exact sub_eq_zero.1 (e.trans (by rw [h1]; simp))
    refine ⟨H1π M ⟨f - p, hmem⟩, ?_⟩
    rw [res_H1π, ← hc, H1π_eq_iff]
    have h1 : ((⟨f - p, hmem⟩ : cocycles₁ M) : G → M) 1 = 0 := cocycles₁_map_one ⟨f - p, hmem⟩
    have : ⇑(mapCocycles₁ H.subtype (𝟙 (res H.subtype M)) ⟨f - p, hmem⟩) = ⇑c := by
      funext h
      have e1 := hf.apply_mul 1 h
      rw [one_mul, map_one, Module.End.one_apply] at e1
      have e2 : p h = p 1 := by
        simp only [hp]
        rw [show (QuotientGroup.mk (h : G) : G ⧸ H) = QuotientGroup.mk 1 from
          (QuotientGroup.eq_one_iff (h : G)).2 h.2]
      have e3 : f 1 = p 1 := by
        have : f 1 - p 1 = 0 := h1
        exact sub_eq_zero.1 this
      show (f - p) h = c h
      simp only [Pi.sub_apply]
      rw [e1, e2, e3]
      abel
    rw [this, sub_self]
    exact zero_mem _
  · rintro ⟨x, hx⟩
    induction x using H1_induction_on with | h c0 =>
    rw [res_H1π] at hx
    have hf : IsTLift (H := H) (M := M)
        (mapCocycles₁ H.subtype (𝟙 (res H.subtype M)) c0) c0 := isTLift_of_cocycle c0.2
    rw [tg_apply y _ c0 hx hf]
    refine (H2π_eq_zero_iff _).2 ⟨0, ?_⟩
    rw [map_zero]
    funext p
    obtain ⟨q, r⟩ := p
    induction q using QuotientGroup.induction_on with | H a => ?_
    induction r using QuotientGroup.induction_on with | H b => ?_
    apply Subtype.ext
    show (0 : M) = ((hf.descC (QuotientGroup.mk a, QuotientGroup.mk b) :
      M.quotientToInvariants H) : M)
    rw [hf.descC_apply, dd]
    have : c0 (a * b) = M.ρ a (c0 b) + c0 a := (mem_cocycles₁_iff _).1 c0.2 a b
    simp only
    rw [this]
    abel


theorem IsTLift.mem_cocycles₁ {c : H → M} {f : G → M} (hf : IsTLift c f) :
    c ∈ cocycles₁ (res H.subtype M) := by
  rw [mem_cocycles₁_iff]
  intro a b
  have e1 : f (((a * b : H)) : G) = f a + M.ρ a (c b) := hf.apply_mul (a : G) b
  have e2 := hf.apply_mul 1 a
  rw [one_mul, map_one, Module.End.one_apply] at e2
  have e3' : f (((a * b : H)) : G) = f 1 + c (a * b) := by
    have := hf.apply_mul 1 (a * b)
    rw [one_mul, map_one, Module.End.one_apply] at this
    exact this
  show c (a * b) = M.ρ a (c b) + c a
  have : c (a * b) = f (((a * b : H)) : G) - f 1 := by rw [e3']; abel
  rw [this, e1, e2]
  abel

theorem inf_eq_zero_iff (z : groupCohomology (M.quotientToInvariants H) 2) :
    (HInfRes M H 2).f z = 0 ↔ ∃ y, tg y = z := by
  constructor
  · intro h0
    induction z using H2_induction_on with | h w =>
    simp only [HInfRes_X₂, HInfRes_X₁, HInfRes_f,
      H2π_comp_map_apply (QuotientGroup.mk' H)] at h0
    rw [H2π_eq_zero_iff] at h0
    obtain ⟨f, hf⟩ := h0
    set W : G → G → M := fun a b =>
      ((w (QuotientGroup.mk a, QuotientGroup.mk b) : M.quotientToInvariants H) : M) with hWdef
    have hW : ∀ a b : G, dd f (a, b) = W a b := fun a b => congr_fun hf (a, b)
    have hinv : ∀ (n : H) (x : M.quotientToInvariants H), M.ρ n (x : M) = x := fun n x => x.2 n
    have hWinv : ∀ (n : H) a b, M.ρ n (W a b) = W a b := fun n a b => hinv n _
    set w0 : M := W 1 1 with hw0
    have hW1 : ∀ g : G, W g 1 = M.ρ g w0 := by
      intro g
      exact congr_arg (fun x : M.quotientToInvariants H => (x : M))
        (cocycles₂_map_one_snd w (QuotientGroup.mk g))
    have hW2 : ∀ g : G, W 1 g = w0 := by
      intro g
      exact congr_arg (fun x : M.quotientToInvariants H => (x : M))
        (cocycles₂_map_one_fst w (QuotientGroup.mk g))
    have hmk : ∀ n : H, (QuotientGroup.mk (n : G) : G ⧸ H) = QuotientGroup.mk 1 :=
      fun n => (QuotientGroup.eq_one_iff (n : G)).2 n.2
    have hWr : ∀ (g : G) (n : H), W g n = M.ρ g w0 := by
      intro g n
      rw [← hW1 g]
      simp only [hWdef]
      rw [hmk n]
    have hWl : ∀ (g : G) (n : H), W n g = w0 := by
      intro g n
      rw [← hW2 g]
      simp only [hWdef]
      rw [hmk n]
    have hw0inv : ∀ n : H, M.ρ n w0 = w0 := fun n => hWinv n 1 1
    have hlift : IsTLift (H := H) (M := M) (fun h : H => f h - w0) (fun g => f g - w0) := by
      refine ⟨fun g h => ?_, fun g h => ?_⟩
      · have e : M.ρ g (f h) - f (g * h) + f g = M.ρ g w0 := by
          have := hW g h
          rw [hWr] at this
          exact this
        have e' : f (g * h) = M.ρ g (f h) + f g - M.ρ g w0 := by rw [← e]; abel
        show f (g * h) - w0 = f g - w0 + M.ρ g (f h - w0)
        rw [e', map_sub]
        abel
      · set k := conjNormal H g⁻¹ h with hk
        have hgk : g * (k : G) = h * g := by
          rw [hk, conjNormal_inv_coe]; group
        have e1 : M.ρ g (f k) - f (h * g) + f g = M.ρ g w0 := by
          have := hW g k
          rw [hWr] at this
          simp only [dd] at this
          rw [hgk] at this
          exact this
        have e2 : M.ρ h (f g) - f (h * g) + f h = w0 := by
          have := hW h g
          rw [hWl] at this
          exact this
        show M.ρ g (f k - w0) - (f h - w0) = M.ρ h (f g - w0) - (f g - w0)
        have e1' : M.ρ g (f k) = M.ρ g w0 + f (h * g) - f g := by rw [← e1]; abel
        have e2' : f (h * g) = M.ρ h (f g) + f h - w0 := by rw [← e2]; abel
        rw [map_sub, map_sub, hw0inv h, e1', e2']
        abel
    let C : cocycles₁ (res H.subtype M) := ⟨fun h : H => f h - w0, hlift.mem_cocycles₁⟩
    have hlift' : IsTLift (H := H) (M := M) C (fun g => f g - w0) := hlift
    refine ⟨⟨H1π _ C, hlift'.mem_H1Fixed⟩, ?_⟩
    rw [tg_apply _ C (fun g => f g - w0) rfl hlift', H2π_eq_iff]
    refine ⟨fun _ => -(w (QuotientGroup.mk 1, QuotientGroup.mk 1)), ?_⟩
    funext p
    obtain ⟨q, r⟩ := p
    induction q using QuotientGroup.induction_on with | H a => ?_
    induction r using QuotientGroup.induction_on with | H b => ?_
    apply Subtype.ext
    show M.ρ a (-w0) - (-w0) + (-w0) =
      ((hlift'.descC (QuotientGroup.mk a, QuotientGroup.mk b) : M.quotientToInvariants H) : M) -
        W a b
    rw [hlift'.descC_apply, ← hW a b]
    simp only [dd, map_sub, map_neg]
    abel
  · rintro ⟨y, rfl⟩
    obtain ⟨c, f, hc, hf⟩ := tgAux y
    rw [tg_apply y c f hc hf]
    simp only [HInfRes_X₂, HInfRes_X₁, HInfRes_f, H2π_comp_map_apply (QuotientGroup.mk' H)]
    rw [H2π_eq_zero_iff]
    refine ⟨f, funext fun p => ?_⟩
    obtain ⟨a, b⟩ := p
    exact (hf.descC_apply a b).symm

end FiveTerm

/-- **Remark 1.35 (a)** (p. 72), the five-term sequence, proved for every group `G`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.35 (a), p. 72"]
theorem remark1_35 : Remark1_35 where
  exact _ _ _ _ _ :=
    ⟨FiveTerm.part_i, FiveTerm.tg, FiveTerm.tg_eq_zero_iff, FiveTerm.inf_eq_zero_iff⟩

end NumberFieldKB.MilneCFT
