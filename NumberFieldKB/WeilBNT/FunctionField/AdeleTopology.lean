import NumberFieldKB.WeilBNT.FunctionField.AdeleVolume
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Topology of the adeles of a function field: neighbourhoods of $0$, single adeles, density

$k$ is a global function field over $\mathbb F_q$, $k_{\mathbb A}$ = `FFAdeleRing Fq k`.

* `FFAdeleRing.single v t`: the adele with component $t$ at $v$ and $0$ elsewhere; `mul_single`.
* `exists_U_subset_of_mem_nhds_zero`: the $U(\mathfrak b)$ form a basis of neighbourhoods of $0$ (one direction:
  every neighbourhood of $0$ contains one).
* `exists_U_trivial`: a character of $k_{\mathbb A}$ is trivial on some $U(\mathfrak b)$ (the circle has no small
  subgroups).
* `dense_finiteSupport`: the adeles with finitely many non-zero components are dense.
-/

open scoped WithZero RestrictedProduct
open Topology

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace FFAdeleRing

/-- The adele with component $t$ at $v$ and $0$ elsewhere. -/
abbrev single (v : Place Fq k) (t : v.Completion) : FFAdeleRing Fq k :=
  open Classical in RestrictedProduct.single (fun w : Place Fq k => w.completionIntegers) v t

open Classical in
theorem single_apply (v : Place Fq k) (t : v.Completion) (w : Place Fq k) :
    single v t w = if h : w = v then h ▸ t else 0 := by
  show Pi.single v t w = _
  by_cases h : w = v
  · subst h; simp
  · rw [dif_neg h]; exact Pi.single_eq_of_ne h _

@[simp] theorem single_apply_same (v : Place Fq k) (t : v.Completion) : single v t v = t := by
  classical
  exact RestrictedProduct.single_eq_same _ _ _

theorem single_apply_of_ne {v w : Place Fq k} (h : w ≠ v) (t : v.Completion) : single v t w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne _ _ h

theorem single_add (v : Place Fq k) (s t : v.Completion) : single v (s + t) = single v s + single v t := by
  classical
  exact RestrictedProduct.single_add _ _ _ _

theorem mul_single (x : FFAdeleRing Fq k) (v : Place Fq k) (t : v.Completion) :
    x * single v t = single v (x v * t) := by
  classical
  exact (RestrictedProduct.mul_single _ _ _ _).symm

theorem continuous_single (v : Place Fq k) : Continuous (single (Fq := Fq) (k := k) v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (Place Fq k)) := by
    rw [Filter.le_principal_iff]; simp
  let f : v.Completion → RestrictedProduct (fun w : Place Fq k => w.Completion)
      (fun w => (w.completionIntegers : Set w.Completion)) (Filter.principal ({v}ᶜ : Set (Place Fq k))) :=
    fun t => ⟨Pi.single v t, fun w hw => by
      have hw' : w ≠ v := hw
      show Pi.single v t w ∈ (w.completionIntegers : Set w.Completion)
      rw [Pi.single_eq_of_ne hw']; exact (w.completionIntegers).zero_mem⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_pi_iff.2 fun w => by
      by_cases h : w = v
      · subst h
        show Continuous fun t : w.Completion => (Pi.single w t : ∀ u : Place Fq k, u.Completion) w
        simp only [Pi.single_eq_same]; exact continuous_id
      · show Continuous fun t : v.Completion => (Pi.single v t : ∀ u : Place Fq k, u.Completion) w
        simp only [Pi.single_eq_of_ne h]; exact continuous_const
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem single_mem_U_iff (a : Divisor Fq k) (v : Place Fq k) (t : v.Completion) :
    single v t ∈ U a ↔ Valued.v t ≤ WithZero.exp (a v) := by
  classical
  constructor
  · intro h
    simpa using h v
  · intro h w
    by_cases hw : w = v
    · subst hw; simpa using h
    · rw [single_apply_of_ne hw]; simp

/-- Helper: a small valuation implies a small restricted valuation. -/
theorem ff_exists_nat_restrict_lt {L : Type*} [Field L] (v : Valuation L (WithZero (Multiplicative ℤ)))
    (γ : v.ValueGroup₀ˣ) :
    ∃ N : ℕ, ∀ y : L, v y ≤ WithZero.exp (-(N : ℤ)) → v.restrict y < γ.1 := by
  obtain ⟨e, he0, key⟩ : ∃ e : WithZero (Multiplicative ℤ), e ≠ 0 ∧ ∀ y : L, v y < e → v.restrict y < γ.1 := by
    refine ⟨_, ?_, fun y => (Valuation.restrict_lt_iff_lt_embedding (v := v) (x := y) (g := γ.1)).mpr⟩
    intro h
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h.trans (map_zero _).symm))
  refine ⟨(1 - WithZero.log e).toNat, fun y hy => key y (lt_of_le_of_lt hy ?_)⟩
  refine lt_of_lt_of_eq (WithZero.exp_lt_exp.mpr (?_ : _ < WithZero.log e)) (WithZero.exp_log he0)
  omega

open Classical in
/-- Helper: a neighbourhood of $0$ contains all adeles integral everywhere and small on a finite set. -/
theorem ff_exists_finset_nat_of_mem_nhds_zero {W : Set (FFAdeleRing Fq k)}
    (hW : W ∈ 𝓝 (0 : FFAdeleRing Fq k)) :
    ∃ (S : Finset (Place Fq k)) (N : ℕ), ∀ x : FFAdeleRing Fq k,
      (∀ u, x u ∈ (u.completionIntegers : Set u.Completion)) →
      (∀ u ∈ S, Valued.v (x u) ≤ WithZero.exp (-(N : ℤ))) → x ∈ W := by
  have hopen : ∀ u : Place Fq k,
      IsOpen (u.completionIntegers : Set u.Completion) :=
    fun _ => Valued.isOpen_valuationSubring _
  have h0 := RestrictedProduct.nhds_zero_eq_map_structureMap
    (R := fun u : Place Fq k => u.Completion)
    (B := fun u => u.completionIntegers) hopen
  have hW2 : W ∈ Filter.map (RestrictedProduct.structureMap
      (fun u : Place Fq k => u.Completion)
      (fun u => (u.completionIntegers : Set u.Completion)) Filter.cofinite) (𝓝 0) := by
    rw [← h0]; exact hW
  have hW3 := Filter.mem_map.mp hW2
  rw [nhds_pi, Filter.mem_pi'] at hW3
  obtain ⟨I, t, ht, hIt⟩ := hW3
  have hN : ∀ u, ∃ N : ℕ, ∀ y : u.completionIntegers,
      Valued.v (y : u.Completion) ≤ WithZero.exp (-(N : ℤ)) → y ∈ t u := by
    intro u
    obtain ⟨V, hV, hVt⟩ := mem_nhds_subtype _ _ _ |>.mp (ht u)
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hV
    obtain ⟨N, hN⟩ := ff_exists_nat_restrict_lt (Valued.v : Valuation u.Completion _) γ
    exact ⟨N, fun y hy => hVt (hγ (hN y hy))⟩
  choose N hN using hN
  refine ⟨I, I.sup N, fun x hxint hx => ?_⟩
  have hxm : RestrictedProduct.structureMap (fun u : Place Fq k => u.Completion)
      (fun u => (u.completionIntegers : Set u.Completion)) Filter.cofinite
      (fun u => ⟨x u, hxint u⟩) = x := rfl
  rw [← hxm]
  refine hIt (fun u hu => hN u _ ?_)
  refine le_trans (hx u hu) ?_
  refine WithZero.exp_le_exp.mpr ?_
  have : N u ≤ I.sup N := Finset.le_sup hu
  omega

/-- A neighbourhood of $0$ in $k_{\mathbb A}$ contains some $U(\mathfrak b)$. -/
theorem exists_U_subset_of_mem_nhds_zero {W : Set (FFAdeleRing Fq k)} (hW : W ∈ 𝓝 (0 : FFAdeleRing Fq k)) :
    ∃ b : Divisor Fq k, (U b : Set (FFAdeleRing Fq k)) ⊆ W := by
  classical
  obtain ⟨S, N, hSN⟩ := ff_exists_finset_nat_of_mem_nhds_zero hW
  refine ⟨∑ v ∈ S, Finsupp.single v (-(N : ℤ)), fun x hx => hSN x (fun v => ?_) (fun v hv => ?_)⟩
  · have h := hx v
    refine h.trans ?_
    rw [← WithZero.exp_zero]
    refine WithZero.exp_le_exp.2 ?_
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_nonpos fun w _ => ?_
    rw [Finsupp.single_apply]
    split_ifs <;> omega
  · have h := hx v
    refine h.trans (WithZero.exp_le_exp.2 ?_)
    rw [Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, hv]

/-- Helper: the circle group has no small subgroups (copy of `circle_noSmallSubgroups`). -/
theorem ff_circle_noSmallSubgroups :
    ∃ U ∈ 𝓝 (1 : Circle), ∀ H : Subgroup Circle, (H : Set Circle) ⊆ U → H = ⊥ := by
  refine ⟨{z : Circle | 0 < (z : ℂ).re}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ (by simp)
    exact isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
  · intro H hH
    rw [eq_bot_iff]
    intro z hz
    by_contra hz1
    have hz1' : z ≠ 1 := hz1
    set θ := Complex.arg (z : ℂ) with hθ
    have hzexp : (z : ℂ) = Complex.exp (θ * Complex.I) := by
      have := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
      rw [Circle.norm_coe, Complex.ofReal_one, one_mul] at this
      exact this.symm
    have hθ0 : θ ≠ 0 := by
      intro h0
      apply hz1'
      apply Circle.ext
      rw [hzexp, h0]; simp
    have hpos : 0 < |θ| := abs_pos.2 hθ0
    have hex : ∃ k : ℕ, Real.pi / 2 ≤ k * |θ| := by
      obtain ⟨k, hk⟩ := Archimedean.arch (Real.pi / 2) hpos
      exact ⟨k, by simpa [nsmul_eq_mul] using hk⟩
    classical
    set k := Nat.find hex with hk
    have hkspec : Real.pi / 2 ≤ k * |θ| := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h
      rw [h] at hkspec
      simp at hkspec
      linarith [Real.pi_pos]
    have hkm : ¬ (Real.pi / 2 ≤ ((k - 1 : ℕ) : ℝ) * |θ|) := Nat.find_min hex (by omega)
    have hlt : ((k : ℝ) - 1) * |θ| < Real.pi / 2 := by
      push Not at hkm
      rwa [Nat.cast_sub (by omega), Nat.cast_one] at hkm
    have hre : 0 < (z : ℂ).re := hH hz
    have hθlt : |θ| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    have hzk : (z ^ k) ∈ H := H.pow_mem hz k
    have hre2 : 0 < ((z ^ k : Circle) : ℂ).re := hH hzk
    rw [Circle.coe_pow, hzexp, ← Complex.exp_nat_mul,
      show (k : ℂ) * (θ * Complex.I) = ((k * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re] at hre2
    have hcos : Real.cos (k * θ) ≤ 0 := by
      have : Real.cos (k * θ) = Real.cos (k * |θ|) := by
        rcases abs_choice θ with h | h
        · rw [h]
        · rw [h, mul_neg, Real.cos_neg]
      rw [this]
      apply Real.cos_nonpos_of_pi_div_two_le_of_le hkspec
      nlinarith [Real.pi_pos]
    linarith

/-- A continuous character of $k_{\mathbb A}$ is trivial on some $U(\mathfrak b)$. -/
theorem exists_U_trivial (ψ : AddChar (FFAdeleRing Fq k) Circle) (hψ : Continuous ψ) :
    ∃ b : Divisor Fq k, ∀ x ∈ U b, ψ x = 1 := by
  obtain ⟨N0, hN, hN0⟩ := ff_circle_noSmallSubgroups
  have hW : ψ ⁻¹' N0 ∈ 𝓝 (0 : FFAdeleRing Fq k) := by
    refine hψ.continuousAt.preimage_mem_nhds ?_
    rw [AddChar.map_zero_eq_one]; exact hN
  obtain ⟨b, hb⟩ := exists_U_subset_of_mem_nhds_zero hW
  refine ⟨b, fun x hx => ?_⟩
  let H : Subgroup Circle := (AddSubgroup.toSubgroup (U b)).map ψ.toMonoidHom
  have hH : (H : Set Circle) ⊆ N0 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hb ha
  have h1 : ψ x ∈ H := ⟨Multiplicative.ofAdd x, hx, rfl⟩
  rw [hN0 H hH] at h1
  exact Subgroup.mem_bot.1 h1

/-- The adeles with finitely many non-zero components are dense in $k_{\mathbb A}$. -/
theorem dense_finiteSupport :
    Dense {x : FFAdeleRing Fq k | Set.Finite {v : Place Fq k | x v ≠ 0}} := by
  classical
  intro x
  rw [mem_closure_iff_nhds]
  intro t ht
  have hW : {w | x + w ∈ t} ∈ 𝓝 (0 : FFAdeleRing Fq k) := by
    have : Continuous fun w : FFAdeleRing Fq k => x + w := continuous_const.add continuous_id
    exact this.continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨b, hb⟩ := exists_U_subset_of_mem_nhds_zero hW
  have hfin := Filter.eventually_cofinite.mp x.2
  set T : Finset (Place Fq k) := hfin.toFinset ∪ b.support with hT
  let y : FFAdeleRing Fq k := ⟨fun v => if v ∈ T then x v else 0,
    Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
      by_contra hvT
      exact hv (by
        show (if v ∈ T then x v else 0) ∈ (v.completionIntegers : Set v.Completion)
        simp only [show v ∉ T from hvT, ↓reduceIte]
        exact (v.completionIntegers).zero_mem))⟩
  have hy : ∀ v, y v = if v ∈ T then x v else 0 := fun v => rfl
  have hU : y - x ∈ U b := by
    intro v
    show Valued.v (y v - x v) ≤ _
    rw [hy v]
    by_cases hv : v ∈ T
    · simp only [hv, ite_true, sub_self, map_zero]
      exact zero_le
    · simp only [hv, ite_false, zero_sub, Valuation.map_neg]
      have h1 : v ∉ hfin.toFinset := fun h => hv (Finset.mem_union_left _ h)
      have h2 : v ∉ b.support := fun h => hv (Finset.mem_union_right _ h)
      rw [Finsupp.notMem_support_iff.1 h2, WithZero.exp_zero]
      have : x v ∈ (v.completionIntegers : Set v.Completion) := by
        by_contra hno
        exact h1 (hfin.mem_toFinset.mpr hno)
      exact this
  refine ⟨y, ?_, ?_⟩
  · have := hb hU
    simpa using this
  · refine T.finite_toSet.subset fun v hv => ?_
    by_contra hvT
    exact hv (by rw [hy v]; simp [show v ∉ T from hvT])

end FFAdeleRing

end NumberFieldKB.WeilBNT.FF
