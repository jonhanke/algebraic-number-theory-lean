import QuadFormsKB.Tamagawa.IdealEuler
import NumberFieldKB.HeckeCharacter.Units

/-!
# Auxiliary results for the Euler product

* **`hasProd_tsum_finsupp`**: the Euler product for absolutely convergent complex series indexed by finitely
  supported exponent vectors, $\sum_x\prod_vf_v(x_v) = \prod_v\sum_jf_v(j)$, when $|f_v|\le g_v$ and the $g_v$ satisfy the
  hypotheses of QuadFormsKB's `hasSum_finsupp_finprod` (the nonnegative real version).
* **`ofReal_prod_cpow`**: $(\prod_ir_i)^s = \prod_ir_i^s$ for real $r_i\ge0$.
* **`MonoidHom.eq_one_of_continuous_pi`**: a continuous homomorphism from a product of groups to $\mathbb C^\times$ that
  is trivial on the factors outside $S$ is trivial on $\{x : x_i = 1\ (i\in S)\}$ ($\mathbb C^\times$ has no small
  subgroups).
-/

open Filter Topology

namespace NumberFieldKB.GlobalZeta

noncomputable section

open QuadFormsKB.Tamagawa

/-! ### The complex Euler product over exponent vectors -/

section ComplexEuler

variable {ι : Type*} [DecidableEq ι]

/-- A finite product of absolutely convergent complex series, indexed by the vectors supported in $T$. -/
theorem hasSum_supported_complex (f : ι → ℤ → ℂ) (hs : ∀ v, Summable fun j => ‖f v j‖) (T : Finset ι) :
    HasSum (fun x : SuppIn T => ∏ v ∈ T, f v ((x : ι →₀ ℤ) v)) (∏ v ∈ T, ∑' j, f v j) ∧
      Summable fun x : SuppIn T => ‖∏ v ∈ T, f v ((x : ι →₀ ℤ) v)‖ := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    have : Unique (SuppIn (∅ : Finset ι)) :=
      ⟨⟨⟨0, by simp⟩⟩, fun x => Subtype.ext (Finsupp.support_eq_empty.mp (Finset.subset_empty.mp x.2))⟩
    exact ⟨by convert hasSum_fintype (fun _ : SuppIn (∅ : Finset ι) => (1 : ℂ)) using 1; simp,
      Summable.of_finite⟩
  | insert a T ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set g : SuppIn T → ℂ := fun x => ∏ v ∈ T, f v ((x : ι →₀ ℤ) v)
    have hprod : Summable fun p : ℤ × SuppIn T => ‖f a p.1 * g p.2‖ := Summable.mul_norm (hs a) ih2
    have h1 : HasSum (fun p : ℤ × SuppIn T => f a p.1 * g p.2) ((∑' j, f a j) * ∏ v ∈ T, ∑' j, f v j) :=
      HasSum.mul (hs a).of_norm.hasSum ih1 hprod.of_norm
    have hcomp : (fun x : SuppIn (insert a T) => ∏ v ∈ insert a T, f v ((x : ι →₀ ℤ) v)) =
        (fun p : ℤ × SuppIn T => f a p.1 * g p.2) ∘ suppInsertEquiv ha := by
      funext x
      rw [Function.comp_apply, Finset.prod_insert ha, suppInsertEquiv_fst]
      congr 1
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [suppInsertEquiv_snd ha x v fun h => ha (h ▸ hv)]
    refine ⟨?_, ?_⟩
    · rw [Finset.prod_insert ha, hcomp, (suppInsertEquiv ha).hasSum_iff]
      exact h1
    · have : (fun x : SuppIn (insert a T) => ‖∏ v ∈ insert a T, f v ((x : ι →₀ ℤ) v)‖) =
          (fun p : ℤ × SuppIn T => ‖f a p.1 * g p.2‖) ∘ suppInsertEquiv ha := by
        funext x
        rw [congrFun hcomp x]
        rfl
      rw [this, (suppInsertEquiv ha).summable_iff]
      exact hprod

/-- **The Euler product for absolutely convergent complex series**:
$\prod_v\sum_jf_v(j) = \sum_x\prod_vf_v(x_v)$ over finitely supported $x$, if $f_v(0) = 1$ outside a finite set $S_0$ and
$|f_v|\le g_v$ with $g$ as in QuadFormsKB's `hasSum_finsupp_finprod`. -/
theorem hasProd_tsum_finsupp (f : ι → ℤ → ℂ) (S₀ : Finset ι) (hf1 : ∀ v ∉ S₀, f v 0 = 1) (g : ι → ℤ → ℝ)
    (hfg : ∀ v j, ‖f v j‖ ≤ g v j) (hg1 : ∀ v ∉ S₀, g v 0 = 1) (hgs : ∀ v, Summable (g v)) {G : ℝ}
    (hG : HasProd (fun v => ∑' j, g v j) G) :
    Summable (fun x : ι →₀ ℤ => ∏ᶠ v, f v (x v)) ∧
      HasProd (fun v => ∑' j, f v j) (∑' x : ι →₀ ℤ, ∏ᶠ v, f v (x v)) := by
  have hg0 : ∀ v j, 0 ≤ g v j := fun v j => (norm_nonneg _).trans (hfg v j)
  have hE := hasSum_finsupp_finprod g hg0 S₀ hg1 hgs hG
  -- on vectors supported in `T ⊇ S₀`, the finprods are products over `T`
  have hfin : ∀ (T : Finset ι), S₀ ⊆ T → ∀ x : ι →₀ ℤ, x.support ⊆ T →
      ∏ᶠ v, f v (x v) = ∏ v ∈ T, f v (x v) := by
    intro T hT x hx
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvT
    apply hv
    have hx0 : x v = 0 := by
      by_contra h; exact hvT (hx (Finsupp.mem_support_iff.mpr h))
    show f v (x v) = 1
    rw [hx0]; exact hf1 v fun h => hvT (hT h)
  have hfing : ∀ (T : Finset ι), S₀ ⊆ T → ∀ x : ι →₀ ℤ, x.support ⊆ T →
      ∏ᶠ v, g v (x v) = ∏ v ∈ T, g v (x v) := by
    intro T hT x hx
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvT
    apply hv
    have hx0 : x v = 0 := by
      by_contra h; exact hvT (hx (Finsupp.mem_support_iff.mpr h))
    show g v (x v) = 1
    rw [hx0]; exact hg1 v fun h => hvT (hT h)
  have hbound : ∀ x : ι →₀ ℤ, ‖∏ᶠ v, f v (x v)‖ ≤ ∏ᶠ v, g v (x v) := by
    intro x
    rw [hfin (S₀ ∪ x.support) Finset.subset_union_left x Finset.subset_union_right,
      hfing (S₀ ∪ x.support) Finset.subset_union_left x Finset.subset_union_right, norm_prod]
    exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hfg v _
  have hsum : Summable (fun x : ι →₀ ℤ => ∏ᶠ v, f v (x v)) := Summable.of_norm_bounded hE.summable hbound
  refine ⟨hsum, ?_⟩
  -- the partial products over `T ⊇ S₀` are the sums over the vectors supported in `T`
  have hpartial : ∀ T : Finset ι, S₀ ⊆ T → ∏ v ∈ T, ∑' j, f v j =
      ∑' x : ι →₀ ℤ, if x.support ⊆ T then ∏ᶠ v, f v (x v) else 0 := by
    intro T hT
    have hsT := (hasSum_supported_complex f (fun v => Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => hfg v j) (hgs v)) T).1
    rw [← hsT.tsum_eq]
    rw [← tsum_subtype_eq_of_support_subset (s := {x : ι →₀ ℤ | x.support ⊆ T}) fun x hx => by
      by_contra h
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hx
      exact h hx.1]
    refine tsum_congr fun x => ?_
    rw [if_pos x.2, hfin T hT x.1 x.2]
  have hlim : Tendsto (fun T : Finset ι => ∑' x : ι →₀ ℤ, if x.support ⊆ T then ∏ᶠ v, f v (x v) else 0) atTop
      (𝓝 (∑' x : ι →₀ ℤ, ∏ᶠ v, f v (x v))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun x => ∏ᶠ v, g v (x v)) hE.summable
      (fun x => ?_) (Eventually.of_forall fun T x => ?_)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop x.support] with T hT
      rw [if_pos hT]
    · split_ifs
      · exact hbound x
      · rw [norm_zero]; exact finprod_nonneg fun v => hg0 v _
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop S₀] with T hT
  exact (hpartial T hT).symm

end ComplexEuler

/-! ### Complex powers of products -/

theorem ofReal_prod_cpow {ι : Type*} (T : Finset ι) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (s : ℂ) :
    (((∏ i ∈ T, r i : ℝ)) : ℂ) ^ s = ∏ i ∈ T, ((r i : ℝ) : ℂ) ^ s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr a) (Finset.prod_nonneg fun i _ => hr i), ih]

/-! ### Characters of products trivial on almost all factors -/

/-- A continuous homomorphism $f$ from a product of groups to $\mathbb C^\times$, trivial on every factor outside
$S$, is trivial on $\{x : x_i = 1\ \forall i\in S\}$. -/
theorem _root_.MonoidHom.eq_one_of_continuous_pi {ι : Type*} [DecidableEq ι] {G : ι → Type*}
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] (f : (∀ i, G i) →* ℂˣ) (hf : Continuous f) (S : Set ι)
    (h : ∀ i ∉ S, ∀ y : G i, f (Pi.mulSingle i y) = 1) (x : ∀ i, G i) (hx : ∀ i ∈ S, x i = 1) : f x = 1 := by
  set U : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2}
  have hU : IsOpen U :=
    isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have h1 : f ⁻¹' U ∈ 𝓝 (1 : ∀ i, G i) :=
    hf.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [U]))
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  set J := hI.toFinset
  -- the part of `x` on `I`
  set x₁ : ∀ i, G i := ∏ i ∈ J, Pi.mulSingle i (x i)
  set x₂ : ∀ i, G i := x₁⁻¹ * x
  have hx₁ : f x₁ = 1 := by
    rw [map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases hiS : i ∈ S
    · rw [hx i hiS, Pi.mulSingle_one, map_one]
    · exact h i hiS _
  have hx₁i : ∀ i ∈ I, x₁ i = x i := by
    intro i hi
    simp only [x₁, Finset.prod_apply]
    rw [Finset.prod_eq_single i (fun j _ hji => Pi.mulSingle_eq_of_ne hji.symm _)
      (fun hiJ => absurd (hI.mem_toFinset.mpr hi) hiJ), Pi.mulSingle_eq_same]
  -- the subgroup of elements trivial on `I` maps into `U`, hence to `1`
  set H : Subgroup (∀ i, G i) :=
    { carrier := {z | ∀ i ∈ I, z i = 1}
      mul_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
      one_mem' := fun i _ => rfl
      inv_mem' := fun ha i hi => by simp [ha i hi] }
  have hH : f.comp H.subtype = 1 := MonoidHom.eq_one_of_norm_sub_one_lt _ fun z => by
    have : (z : ∀ i, G i) ∈ (I.pi t) := fun i hi => by rw [z.2 i hi]; exact mem_of_mem_nhds (ht i)
    exact hsub this
  have hx₂ : x₂ ∈ H := fun i hi => by
    simp only [x₂, Pi.mul_apply, Pi.inv_apply, hx₁i i hi, inv_mul_cancel]
  have hfx₂ : f x₂ = 1 := DFunLike.congr_fun hH ⟨x₂, hx₂⟩
  have : x = x₁ * x₂ := by simp [x₂]
  rw [this, map_mul, hx₁, hfx₂, one_mul]

end

end NumberFieldKB.GlobalZeta
