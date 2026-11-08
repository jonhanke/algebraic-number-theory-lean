import NumberFieldKB.WeilBNT.PFieldUnitsZp
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.Finiteness

/-!
# Weil, *Basic Number Theory*, II.§3, Prop. 10: $1+P$ in characteristic $p$

$K$ is a commutative $p$-field of characteristic $p$ (`[CharP K p]`), $q=p^f$ its module, $\pi$ a prime element and
$\alpha_0,\dots,\alpha_{f-1}\in R$ elements whose residues form a basis of the residue field $\mathbb F_q$ over
$\mathbb F_p$, in the digit form used by Weil (`IsResidueBasis`): every $x\in R$ is congruent modulo $P$ to exactly one
$\sum_ia_i\alpha_i$ with integers $0\le a_i<p$. (Weil takes the $\alpha_i$ in the field $\mathbb F_q\subset K$ of Cor. 1
of Thm. 7; any such lifts work.)

* `exists_isResidueBasis`: such $\alpha$ exist, with $p^f=q$.
* **`weil_II_3_prop10`**: the elements $g_{i,n}=1+\alpha_i\pi^n$ ($0\le i<f$, $n>0$ prime to $p$) are free
  topological generators of the $\mathbb Z_p$-module $1+P$: for every family $b_{i,n}\in\mathbb Z_p$ the product
  $\prod g_{i,n}^{b_{i,n}}$ converges (unconditionally, in the group $1+P$), and every $u\in1+P$ is such a product for
  exactly one family $b$. So $1+P$ is the direct product of the countably many modules $g_{i,n}^{\mathbb Z_p}\cong
  \mathbb Z_p$.
-/

open Topology Filter
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ} [hp : Fact p.Prime]

/-- $\alpha_0,\dots,\alpha_{f-1}\in R$ reduce to a basis of $R/P$ over $\mathbb F_p$: every $x\in R$ is congruent modulo
$P$ to exactly one $\sum_ia_i\alpha_i$ with $0\le a_i<p$. -/
def IsResidueBasis (hK : IsPField K p) {f : ℕ} (α : Fin f → K) : Prop :=
  (∀ i, modK K (α i) ≤ 1) ∧
    ∀ x : K, modK K x ≤ 1 → ∃! a : Fin f → Fin p, modK K (x - ∑ i, ((a i : ℕ) : K) * α i) < 1

section Residue

variable (hK : IsPField K p) {f : ℕ} {α : Fin f → K} (hα1 : ∀ i, modK K (α i) ≤ 1)

/-- The lift of $\alpha_i$ to the ring $R$. -/
def alphaR (i : Fin f) : pR hK := ⟨α i, mem_pR.2 (hα1 i)⟩

/-- The residue of $\sum_ia_i\alpha_i^{p^v}$ in the residue field. -/
def Theta (v : ℕ) (a : Fin f → Fin p) : Qt hK :=
  ∑ i, ((a i : ℕ) : Qt hK) * resMap hK (alphaR hK hα1 i) ^ (p ^ v)

theorem digit_iff (r : pR hK) (a : Fin f → Fin p) :
    modK K ((r : K) - ∑ i, ((a i : ℕ) : K) * α i) < 1 ↔ resMap hK r = Theta hK hα1 0 a := by
  have h : resMap hK (r - ∑ i, ((a i : ℕ) : pR hK) * alphaR hK hα1 i) =
      resMap hK r - Theta hK hα1 0 a := by
    simp [Theta, map_sum]
  have hc : (((r - ∑ i, ((a i : ℕ) : pR hK) * alphaR hK hα1 i : pR hK)) : K) =
      (r : K) - ∑ i, ((a i : ℕ) : K) * α i := by
    simp [alphaR]
  rw [← hc, ← resMap_eq_zero hK, h, sub_eq_zero]

theorem digits_of_theta_bijective (hbij : Function.Bijective (Theta hK hα1 0)) :
    ∀ x : K, modK K x ≤ 1 →
      ∃! a : Fin f → Fin p, modK K (x - ∑ i, ((a i : ℕ) : K) * α i) < 1 := by
  intro x hx
  obtain ⟨a, ha, hu⟩ :=
    (Function.bijective_iff_existsUnique _).1 hbij (resMap hK ⟨x, mem_pR.2 hx⟩)
  exact ⟨a, (digit_iff hK hα1 ⟨x, mem_pR.2 hx⟩ a).2 ha.symm,
    fun a' ha' => hu a' ((digit_iff hK hα1 ⟨x, mem_pR.2 hx⟩ a').1 ha').symm⟩

theorem theta_zero_bijective
    (hα : ∀ x : K, modK K x ≤ 1 →
      ∃! a : Fin f → Fin p, modK K (x - ∑ i, ((a i : ℕ) : K) * α i) < 1) :
    Function.Bijective (Theta hK hα1 0) := by
  rw [Function.bijective_iff_existsUnique]
  intro y
  obtain ⟨r, rfl⟩ := resMap_surjective hK y
  obtain ⟨a, ha, hu⟩ := hα (r : K) (mem_pR.1 r.2)
  exact ⟨a, ((digit_iff hK hα1 r a).1 ha).symm,
    fun a' ha' => hu a' ((digit_iff hK hα1 r a').2 ha'.symm)⟩

theorem charP_Qt [CharP K p] : CharP (Qt hK) p := by
  refine (CharP.charP_iff_prime_eq_zero hp.out).2 ?_
  have : ((p : ℕ) : pR hK) = 0 := Subtype.ext (by simp)
  rw [← map_natCast (resMap hK), this, map_zero]

theorem theta_bijective [CharP K p] (hbij : Function.Bijective (Theta hK hα1 0)) (v : ℕ) :
    Function.Bijective (Theta hK hα1 v) := by
  have := charP_Qt hK
  have e : Theta hK hα1 v = iterateFrobenius (Qt hK) p v ∘ Theta hK hα1 0 := by
    funext a
    simp [Theta, map_sum, map_mul, map_natCast, iterateFrobenius_def]
  rw [e]
  refine (?_ : Function.Bijective (iterateFrobenius (Qt hK) p v)).comp hbij
  exact (Finite.injective_iff_bijective).1 (iterateFrobenius_inj (Qt hK) p v)

end Residue

theorem exists_isResidueBasis [CharP K p] (hK : IsPField K p) :
    ∃ (f : ℕ) (α : Fin f → K), pq hK = p ^ f ∧ IsResidueBasis hK α := by
  have := charP_Qt hK
  let _ : Algebra (ZMod p) (Qt hK) := ZMod.algebra (Qt hK) p
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : Module.Finite (ZMod p) (Qt hK) := Module.Finite.of_finite
  let B := Module.finBasis (ZMod p) (Qt hK)
  obtain ⟨lift, hlift⟩ : ∃ lift : Fin (Module.finrank (ZMod p) (Qt hK)) → pR hK,
      ∀ i, resMap hK (lift i) = B i := ⟨fun i => (resMap_surjective hK (B i)).choose,
        fun i => (resMap_surjective hK (B i)).choose_spec⟩
  have hα1 : ∀ i, modK K ((lift i : pR hK) : K) ≤ 1 := fun i => mem_pR.1 (lift i).2
  have hcard : pq hK = p ^ Module.finrank (ZMod p) (Qt hK) := by
    rw [← card_Qt, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  refine ⟨Module.finrank (ZMod p) (Qt hK), fun i => ((lift i : pR hK) : K), hcard, hα1, ?_⟩
  refine digits_of_theta_bijective hK hα1 ?_
  have hι : Function.Bijective (fun t : Fin p => ((t : ℕ) : ZMod p)) := by
    constructor
    · intro s t h
      have := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt s.2, ZMod.val_natCast_of_lt t.2] at this
      exact Fin.ext this
    · intro z
      exact ⟨⟨z.val, ZMod.val_lt z⟩, by simp⟩
  have e : Theta hK hα1 0 = B.equivFun.symm ∘
      (Equiv.piCongrRight fun _ : Fin (Module.finrank (ZMod p) (Qt hK)) =>
        Equiv.ofBijective _ hι) := by
    funext a
    simp only [Theta, Function.comp_apply, Module.Basis.equivFun_symm_apply, Equiv.piCongrRight_apply,
      pow_zero, pow_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : alphaR hK hα1 i = lift i := Subtype.ext rfl
    rw [h1, hlift i]
    show _ = ((a i : ℕ) : ZMod p) • B i
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  rw [e]
  exact B.equivFun.symm.bijective.comp (Equiv.bijective _)

/-- The index set $\{(i,n):0\le i<f,\ n>0,\ p\nmid n\}$ of Weil's generators. -/
abbrev GenIdx (p f : ℕ) : Type := Fin f × {n : ℕ // 0 < n ∧ ¬ p ∣ n}

theorem genElt_mem (hK : IsPField K p) {π : K} (hπ : modK K π < 1) {f : ℕ} {α : Fin f → K}
    (hα : ∀ i, modK K (α i) ≤ 1) (j : GenIdx p f) : modK K ((1 + α j.1 * π ^ (j.2 : ℕ)) - 1) < 1 := by
  rw [add_sub_cancel_left, modK_mul, modK_pow]
  calc modK K (α j.1) * modK K π ^ (j.2 : ℕ) ≤ 1 * modK K π ^ (j.2 : ℕ) :=
        mul_le_mul_of_nonneg_right (hα j.1) zero_le
    _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le hπ (Nat.pos_iff_ne_zero.1 j.2.2.1)

theorem genElt_ne_zero (hK : IsPField K p) {π : K} (hπ : modK K π < 1) {f : ℕ} {α : Fin f → K}
    (hα : ∀ i, modK K (α i) ≤ 1) (j : GenIdx p f) : 1 + α j.1 * π ^ (j.2 : ℕ) ≠ 0 := by
  intro h
  have := genElt_mem hK hπ hα j
  rw [h, zero_sub, modK_neg, modK_one'] at this
  exact lt_irrefl _ this

/-- Weil's generator $g_{i,n}=1+\alpha_i\pi^n$ of $1+P$. -/
def genElt (hK : IsPField K p) {π : K} (hπ : modK K π < 1) {f : ℕ} {α : Fin f → K}
    (hα : ∀ i, modK K (α i) ≤ 1) (j : GenIdx p f) : onePlusPUnits hK :=
  ⟨Units.mk0 _ (genElt_ne_zero hK hπ hα j), genElt_mem hK hπ hα j⟩

section Filtration

variable (hK : IsPField K p)

theorem modK_unit_eq_one (u : onePlusPUnits hK) : modK K ((u : Kˣ) : K) = 1 :=
  modK_eq_one_of_op hK u.2

/-- $1+P^N$ as a subgroup of $1+P$. -/
def Fsub (N : ℕ) : Subgroup (onePlusPUnits hK) where
  carrier := {u | modK K (((u : Kˣ) : K) - 1) ≤ qi hK ^ N}
  mul_mem' := by
    intro a b ha hb
    have h1 := modK_unit_eq_one hK a
    have e : ((((a * b : onePlusPUnits hK)) : Kˣ) : K) - 1 =
        ((a : Kˣ) : K) * (((b : Kˣ) : K) - 1) + (((a : Kˣ) : K) - 1) := by
      simp only [Subgroup.coe_mul, Units.val_mul]; ring
    change modK K (((((a * b : onePlusPUnits hK)) : Kˣ) : K) - 1) ≤ _
    rw [e]
    refine (isUltrametricMod_of_isPField hK _ _).trans (max_le ?_ ha)
    rw [modK_mul, h1, one_mul]; exact hb
  one_mem' := by
    change modK K ((((1 : onePlusPUnits hK) : Kˣ) : K) - 1) ≤ _
    simp
  inv_mem' := by
    intro a ha
    have h1 := modK_unit_eq_one hK a
    have ha0 : ((a : Kˣ) : K) ≠ 0 := (a : Kˣ).ne_zero
    have e : (((a⁻¹ : onePlusPUnits hK) : Kˣ) : K) - 1 =
        -(((a : Kˣ) : K) - 1) * ((a : Kˣ) : K)⁻¹ := by
      simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val]; field_simp; ring
    change modK K ((((a⁻¹ : onePlusPUnits hK) : Kˣ) : K) - 1) ≤ _
    rw [e, modK_mul, modK_neg, modK_inv ha0, h1, inv_one, mul_one]; exact ha

theorem mem_Fsub {N : ℕ} {u : onePlusPUnits hK} :
    u ∈ Fsub hK N ↔ modK K (((u : Kˣ) : K) - 1) ≤ qi hK ^ N := Iff.rfl

theorem Fsub_mono {M N : ℕ} (h : M ≤ N) : Fsub hK N ≤ Fsub hK M := fun _ hu =>
  hu.trans (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le h)

theorem mem_Fsub_one (u : onePlusPUnits hK) : u ∈ Fsub hK 1 := by
  rw [mem_Fsub, pow_one]; exact modK_le_qi_of_lt_one hK u.2

theorem coe_G_mul (u v : onePlusPUnits hK) :
    (((u * v : onePlusPUnits hK) : Kˣ) : K) = ((u : Kˣ) : K) * ((v : Kˣ) : K) := by simp

theorem coe_G_pow (u : onePlusPUnits hK) (m : ℕ) :
    (((u ^ m : onePlusPUnits hK) : Kˣ) : K) = ((u : Kˣ) : K) ^ m := by simp

theorem eq_one_of_forall_mem_Fsub {u : onePlusPUnits hK} (h : ∀ N, 1 ≤ N → u ∈ Fsub hK N) :
    u = 1 := by
  have ht : Tendsto (fun n : ℕ => qi hK ^ n) atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (qi_lt_one hK)
  have h0 : modK K (((u : Kˣ) : K) - 1) ≤ 0 :=
    ge_of_tendsto ht (by filter_upwards [eventually_ge_atTop 1] with n hn using h n hn)
  have h1 : ((u : Kˣ) : K) - 1 = 0 := modK_eq_zero_iff.1 (le_antisymm h0 zero_le)
  exact onePlusPUnits_ext (by simpa [sub_eq_zero] using h1)

theorem continuous_ucoe : Continuous fun u : onePlusPUnits hK => ((u : Kˣ) : K) :=
  Units.continuous_val.comp continuous_subtype_val

theorem isClosed_Fsub (N : ℕ) : IsClosed (Fsub hK N : Set (onePlusPUnits hK)) :=
  isClosed_le (continuous_modK.comp ((continuous_ucoe hK).sub continuous_const)) continuous_const

theorem zpPow_mem_Fsub {N : ℕ} (hN : 1 ≤ N) (a : ℤ_[p]) {u : onePlusPUnits hK}
    (hu : u ∈ Fsub hK N) : zpPow hK a u ∈ Fsub hK N := by
  have hx := u.2
  have hL' := tendsto_zpPowVal_appr hK hx a
  have hcl : Tendsto (fun n => modK K (((u : Kˣ) : K) ^ a.appr n - 1)) atTop
      (𝓝 (modK K (zpPowVal hK a ((u : Kˣ) : K) - 1))) :=
    (continuous_modK.tendsto _).comp (hL'.sub_const _)
  exact le_of_tendsto hcl (Eventually.of_forall fun n =>
    modK_pow_sub_one_le hK (pow_lt_one₀ zero_le (qi_lt_one hK) (by omega)) hu (a.appr n))

theorem isEmbedding_ucoe : Topology.IsEmbedding fun u : onePlusPUnits hK => ((u : Kˣ) : K) :=
  Units.isEmbedding_val₀.comp Topology.IsEmbedding.subtypeVal

theorem compactSpace_onePlusPUnits : CompactSpace (onePlusPUnits hK) := by
  rw [← isCompact_univ_iff, (isEmbedding_ucoe hK).isCompact_iff, Set.image_univ]
  have hrange : Set.range (fun u : onePlusPUnits hK => ((u : Kˣ) : K)) =
      {x : K | modK K (x - 1) ≤ qi hK} := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact modK_le_qi_of_lt_one hK u.2
    · intro hx
      have hx' : modK K (x - 1) < 1 := lt_of_le_of_lt hx (qi_lt_one hK)
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [zero_sub, modK_neg, modK_one'] at hx'
        exact lt_irrefl _ hx'
      exact ⟨⟨Units.mk0 x hx0, hx'⟩, rfl⟩
  rw [hrange]
  refine (weil_I_4_thm6_isCompact hK).of_isClosed_subset
    (isClosed_le (continuous_modK.comp (continuous_id.sub continuous_const)) continuous_const) ?_
  intro x hx
  have := modK_eq_one_of_op hK (lt_of_le_of_lt hx (qi_lt_one hK))
  exact mem_pR.2 this.le

theorem exists_Fsub_subset {U : Set (onePlusPUnits hK)} (hU : U ∈ 𝓝 (1 : onePlusPUnits hK)) :
    ∃ M : ℕ, 1 ≤ M ∧ (Fsub hK M : Set (onePlusPUnits hK)) ⊆ U := by
  rw [(isEmbedding_ucoe hK).nhds_eq_comap] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.1 hU
  have hV1 : V ∈ 𝓝 (1 : K) := by simpa using hV
  have hV0 : (fun y : K => 1 + y) ⁻¹' V ∈ 𝓝 (0 : K) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV1)
  obtain ⟨m, hm, hsub⟩ := hasBasis_nhds_zero_modK.mem_iff.1 hV0
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hm (qi_lt_one hK)
  refine ⟨M + 1, by omega, fun u hu => hVU ?_⟩
  have hle : modK K (((u : Kˣ) : K) - 1) ≤ m :=
    (hu.trans (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (Nat.le_succ M))).trans hM.le
  have := hsub (show ((u : Kˣ) : K) - 1 ∈ {x | modK K x ≤ m} from hle)
  simpa using this

theorem isOpen_Fsub (N : ℕ) : IsOpen (Fsub hK N : Set (onePlusPUnits hK)) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hW : IsOpen {u : onePlusPUnits hK | modK K (((u : Kˣ) : K) - 1) < qi hK ^ N} :=
    isOpen_lt (continuous_modK.comp ((continuous_ucoe hK).sub continuous_const)) continuous_const
  refine Filter.mem_of_superset (hW.mem_nhds ?_) fun u hu =>
    show modK K (((u : Kˣ) : K) - 1) ≤ _ from le_of_lt hu
  have : (((1 : onePlusPUnits hK) : Kˣ) : K) - 1 = 0 := by simp
  show modK K ((((1 : onePlusPUnits hK) : Kˣ) : K) - 1) < _
  rw [this, modK_zero']
  exact pow_pos (qi_pos hK) N

/-- A family in $1+P$ which lies in $1+P^M$ off a finite set, for every $M\ge1$, is unconditionally
multipliable. -/
theorem multipliable_of_forall_mem {ι : Type*} {t : ι → onePlusPUnits hK}
    (ht : ∀ M : ℕ, 1 ≤ M → ∀ᶠ i in cofinite, t i ∈ Fsub hK M) : Multipliable t := by
  let _ : UniformSpace (onePlusPUnits hK) := IsTopologicalGroup.rightUniformSpace _
  have _ : IsUniformGroup (onePlusPUnits hK) := isUniformGroup_of_commGroup
  have _ : CompactSpace (onePlusPUnits hK) := compactSpace_onePlusPUnits hK
  have _ : NonarchimedeanGroup (onePlusPUnits hK) :=
    { is_nonarchimedean := fun U hU => by
        obtain ⟨M, hM1, hM⟩ := exists_Fsub_subset hK hU
        exact ⟨⟨Fsub hK M, isOpen_Fsub hK M⟩, hM⟩ }
  refine NonarchimedeanGroup.multipliable_of_tendsto_cofinite_one ?_
  intro U hU
  obtain ⟨M, hM1, hM⟩ := exists_Fsub_subset hK hU
  exact (ht M hM1).mono fun i hi => hM hi

theorem t2_onePlusPUnits : T2Space (onePlusPUnits hK) := (isEmbedding_ucoe hK).t2Space

theorem tprod_mem_Fsub {ι : Type*} {t : ι → onePlusPUnits hK} (hmul : Multipliable t) {M : ℕ}
    (ht : ∀ i, t i ∈ Fsub hK M) : ∏' i, t i ∈ Fsub hK M := by
  have h := hmul.hasProd
  refine (isClosed_Fsub hK M).mem_of_tendsto h (Eventually.of_forall fun s => ?_)
  exact Subgroup.prod_mem _ fun i _ => ht i

end Filtration

section Gen

variable (hK : IsPField K p) {π : K} (hπ : modK K π = qi hK) {f : ℕ} {α : Fin f → K}
  (hα1 : ∀ i, modK K (α i) ≤ 1)

/-- Weil's generator $g_{i,n}=1+\alpha_i\pi^n$, for a prime element $\pi$ of value $q^{-1}$. -/
abbrev gE (j : GenIdx p f) : onePlusPUnits hK :=
  genElt hK (hπ.trans_lt (qi_lt_one hK)) hα1 j

theorem coe_gE (j : GenIdx p f) :
    (((gE hK hπ hα1 j : onePlusPUnits hK) : Kˣ) : K) = 1 + α j.1 * π ^ (j.2 : ℕ) := rfl

theorem coe_gE_pow [CharP K p] (w : ℕ) (j : GenIdx p f) :
    (((gE hK hπ hα1 j ^ (p ^ w) : onePlusPUnits hK) : Kˣ) : K) =
      1 + α j.1 ^ (p ^ w) * π ^ ((j.2 : ℕ) * p ^ w) := by
  rw [coe_G_pow, coe_gE, add_pow_char_pow, one_pow, mul_pow, ← pow_mul]

theorem gE_pow_mem [CharP K p] {w M : ℕ} (j : GenIdx p f) (hw : M ≤ (j.2 : ℕ) * p ^ w) :
    gE hK hπ hα1 j ^ (p ^ w) ∈ Fsub hK M := by
  rw [mem_Fsub, coe_gE_pow hK hπ hα1, add_sub_cancel_left, modK_mul, modK_pow, modK_pow, hπ]
  calc modK K (α j.1) ^ (p ^ w) * qi hK ^ ((j.2 : ℕ) * p ^ w)
      ≤ 1 * qi hK ^ ((j.2 : ℕ) * p ^ w) :=
        mul_le_mul' (pow_le_one₀ zero_le (hα1 _)) le_rfl
    _ ≤ qi hK ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one zero_le (qi_lt_one hK).le hw

/-- If $c$ is divisible by $p^{v+1}$ whenever $np^v<L$, then $g_{i,n}^c\in1+P^L$. -/
theorem zpPow_gE_mem [CharP K p] {L : ℕ} (hL : 1 ≤ L) (j : GenIdx p f) (c : ℤ_[p])
    (h : ∀ v : ℕ, (j.2 : ℕ) * p ^ v < L → (p : ℤ_[p]) ^ (v + 1) ∣ c) :
    zpPow hK c (gE hK hπ hα1 j) ∈ Fsub hK L := by
  classical
  have hex : ∃ w : ℕ, L ≤ (j.2 : ℕ) * p ^ w := ⟨L, by
    have h1 : L < p ^ L := Nat.lt_pow_self hp.out.one_lt
    have h2 : 1 ≤ (j.2 : ℕ) := j.2.2.1
    nlinarith⟩
  obtain ⟨w, hwL, hmin⟩ : ∃ w, L ≤ (j.2 : ℕ) * p ^ w ∧ ∀ w' < w, ¬ L ≤ (j.2 : ℕ) * p ^ w' :=
    ⟨Nat.find hex, Nat.find_spec hex, fun w' hw' => Nat.find_min hex hw'⟩
  have hdvd : (p : ℤ_[p]) ^ w ∣ c := by
    rcases Nat.eq_zero_or_pos w with h0 | hpos
    · rw [h0]; simp
    · have hlt : (j.2 : ℕ) * p ^ (w - 1) < L := not_le.1 (hmin (w - 1) (by omega))
      have := h (w - 1) hlt
      rwa [Nat.sub_add_cancel hpos] at this
  obtain ⟨c', rfl⟩ := hdvd
  rw [mul_comm, zpPow_mul]
  have e : zpPow hK ((p : ℤ_[p]) ^ w) (gE hK hπ hα1 j) = gE hK hπ hα1 j ^ (p ^ w) := by
    have := zpPow_natCast hK (p ^ w) (gE hK hπ hα1 j)
    simpa using this
  rw [e]
  exact zpPow_mem_Fsub hK hL c' (gE_pow_mem hK hπ hα1 j hwL)

theorem finite_gen_lt (M : ℕ) : {j : GenIdx p f | (j.2 : ℕ) < M}.Finite := by
  have h1 : {n : {n : ℕ // 0 < n ∧ ¬ p ∣ n} | (n : ℕ) < M}.Finite :=
    (Set.finite_Iio M).preimage Subtype.val_injective.injOn
  have : {j : GenIdx p f | (j.2 : ℕ) < M} =
      Set.univ ×ˢ {n : {n : ℕ // 0 < n ∧ ¬ p ∣ n} | (n : ℕ) < M} := by
    ext j; simp
  rw [this]; exact Set.finite_univ.prod h1

theorem multipliable_gE [CharP K p] (b : GenIdx p f → ℤ_[p]) :
    Multipliable fun j => zpPow hK (b j) (gE hK hπ hα1 j) := by
  refine multipliable_of_forall_mem hK fun M hM => ?_
  rw [Filter.eventually_cofinite]
  refine (finite_gen_lt (p := p) (f := f) M).subset fun j hj => ?_
  by_contra hjM
  simp only [Set.mem_ofPred_eq, not_lt] at hjM
  exact hj (zpPow_gE_mem hK hπ hα1 hM j (b j) fun v hv =>
    absurd hv (not_lt.2 (le_trans hjM (Nat.le_mul_of_pos_right _ (pow_pos hp.out.pos v)))))

/-- The product $\prod_jg_j^{b_j}$ of Prop. 10. -/
def Pfam [CharP K p] (b : GenIdx p f → ℤ_[p]) : onePlusPUnits hK :=
  ∏' j, zpPow hK (b j) (gE hK hπ hα1 j)

theorem Pfam_add [CharP K p] (b b' : GenIdx p f → ℤ_[p]) :
    Pfam hK hπ hα1 (b + b') = Pfam hK hπ hα1 b * Pfam hK hπ hα1 b' := by
  have _ := t2_onePlusPUnits hK
  unfold Pfam
  rw [← (multipliable_gE hK hπ hα1 b).tprod_mul (multipliable_gE hK hπ hα1 b')]
  congr 1
  funext j
  exact zpPow_add hK _ _ _

/-- The divisibility condition: the "digits" of $b_{i,n}$ below position $N$ vanish. -/
def DivCond (N : ℕ) (b : GenIdx p f → ℤ_[p]) : Prop :=
  ∀ (j : GenIdx p f) (v : ℕ), (j.2 : ℕ) * p ^ v < N → (p : ℤ_[p]) ^ (v + 1) ∣ b j

theorem divCond_one (b : GenIdx p f → ℤ_[p]) : DivCond 1 b := by
  intro j v hv
  exfalso
  have : 1 ≤ (j.2 : ℕ) * p ^ v := Nat.mul_pos j.2.2.1 (pow_pos hp.out.pos v)
  omega

theorem Pfam_mem_Fsub [CharP K p] {M : ℕ} (hM : 1 ≤ M) {b : GenIdx p f → ℤ_[p]}
    (hb : DivCond M b) : Pfam hK hπ hα1 b ∈ Fsub hK M :=
  tprod_mem_Fsub hK (multipliable_gE hK hπ hα1 b) fun j =>
    zpPow_gE_mem hK hπ hα1 hM j (b j) (hb j)

end Gen

section Phi

variable (hK : IsPField K p) {π : K} (hπ : modK K π = qi hK)
include hπ

theorem ne_zero_of_modK_eq_qi : π ≠ 0 := by
  rintro rfl
  rw [modK_zero'] at hπ
  exact (qi_pos hK).ne hπ

theorem modK_div_pow_le_one {N : ℕ} {x : K} (hx : modK K x ≤ qi hK ^ N) :
    modK K (x / π ^ N) ≤ 1 := by
  have hπ0 := ne_zero_of_modK_eq_qi hK hπ
  rw [div_eq_mul_inv, modK_mul, modK_inv (pow_ne_zero N hπ0), modK_pow, hπ]
  calc modK K x * (qi hK ^ N)⁻¹ ≤ qi hK ^ N * (qi hK ^ N)⁻¹ := mul_le_mul' hx le_rfl
    _ = 1 := mul_inv_cancel₀ (pow_pos (qi_pos hK) N).ne'

/-- The quotient $(u-1)/\pi^N\in R$ for $u\in1+P^N$. -/
def tq {N : ℕ} (u : Fsub hK N) : pR hK :=
  ⟨((((u : onePlusPUnits hK) : Kˣ) : K) - 1) / π ^ N, mem_pR.2 (modK_div_pow_le_one hK hπ u.2)⟩

theorem tq_val {N : ℕ} (u : Fsub hK N) :
    ((tq hK hπ u : pR hK) : K) = ((((u : onePlusPUnits hK) : Kˣ) : K) - 1) / π ^ N := rfl

omit hπ in
theorem resMap_eq_of_lt (a b : pR hK) (h : modK K ((a : K) - (b : K)) < 1) :
    resMap hK a = resMap hK b := by
  have : resMap hK (a - b) = 0 := (resMap_eq_zero hK _).2 (by simpa using h)
  rwa [map_sub, sub_eq_zero] at this

/-- The residue of $(u-1)/\pi^N$: the homomorphism $(1+P^N)\to\mathbb F_q$ with kernel $1+P^{N+1}$. -/
def phiHom {N : ℕ} (hN : 1 ≤ N) : Fsub hK N →* Multiplicative (Qt hK) where
  toFun u := Multiplicative.ofAdd (resMap hK (tq hK hπ u))
  map_one' := by
    have : tq hK hπ (1 : Fsub hK N) = 0 := Subtype.ext (by simp [tq])
    simp [this]
  map_mul' := by
    intro u v
    have hP : π ^ N ≠ 0 := pow_ne_zero N (ne_zero_of_modK_eq_qi hK hπ)
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add, ← map_add]
    congr 1
    apply resMap_eq_of_lt
    have e : ((tq hK hπ (u * v) : pR hK) : K) - ((tq hK hπ u + tq hK hπ v : pR hK) : K) =
        ((((u : onePlusPUnits hK) : Kˣ) : K) - 1) / π ^ N * ((((v : onePlusPUnits hK) : Kˣ) : K) - 1) := by
      rw [Subring.coe_add, tq_val, tq_val, tq_val, Subgroup.coe_mul, coe_G_mul]
      field_simp
      ring
    rw [e, modK_mul]
    calc modK K (((((u : onePlusPUnits hK) : Kˣ) : K) - 1) / π ^ N) *
          modK K ((((v : onePlusPUnits hK) : Kˣ) : K) - 1) ≤ 1 * qi hK ^ N :=
          mul_le_mul' (modK_div_pow_le_one hK hπ u.2) v.2
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le (qi_lt_one hK) (by omega)

theorem phiHom_eq_one_iff {N : ℕ} (hN : 1 ≤ N) (u : Fsub hK N) :
    phiHom hK hπ hN u = 1 ↔ (u : onePlusPUnits hK) ∈ Fsub hK (N + 1) := by
  have hP : π ^ N ≠ 0 := pow_ne_zero N (ne_zero_of_modK_eq_qi hK hπ)
  have hxt : (((u : onePlusPUnits hK) : Kˣ) : K) - 1 = ((tq hK hπ u : pR hK) : K) * π ^ N := by
    rw [tq_val]; field_simp
  show Multiplicative.ofAdd (resMap hK (tq hK hπ u)) = 1 ↔ _
  rw [ofAdd_eq_one, resMap_eq_zero, mem_Fsub, hxt, modK_mul, modK_pow, hπ, pow_succ']
  constructor
  · intro h; exact mul_le_mul' (modK_le_qi_of_lt_one hK h) le_rfl
  · intro h
    have hq : 0 < qi hK ^ N := pow_pos (qi_pos hK) N
    exact lt_of_le_of_lt (le_of_mul_le_mul_right h hq) (qi_lt_one hK)

end Phi

section Step

variable [CharP K p] (hK : IsPField K p) {π : K} (hπ : modK K π = qi hK) {f : ℕ} {α : Fin f → K}
  (hα1 : ∀ i, modK K (α i) ≤ 1) {n : ℕ} (hn : 0 < n ∧ ¬ p ∣ n) (v : ℕ)

/-- $g_{i,n}^{p^v}$ as an element of $1+P^N$, $N=np^v$. -/
def gstep (i : Fin f) : Fsub hK (n * p ^ v) :=
  ⟨gE hK hπ hα1 (i, ⟨n, hn⟩) ^ (p ^ v), gE_pow_mem hK hπ hα1 _ le_rfl⟩

theorem phiHom_gstep (hN : 1 ≤ n * p ^ v) (i : Fin f) :
    phiHom hK hπ hN (gstep hK hπ hα1 hn v i) =
      Multiplicative.ofAdd (resMap hK (alphaR hK hα1 i) ^ (p ^ v)) := by
  have hP : π ^ (n * p ^ v) ≠ 0 := pow_ne_zero _ (ne_zero_of_modK_eq_qi hK hπ)
  show Multiplicative.ofAdd (resMap hK (tq hK hπ (gstep hK hπ hα1 hn v i))) = _
  rw [← map_pow]
  congr 2
  apply Subtype.ext
  rw [tq_val]
  show ((((gE hK hπ hα1 (i, ⟨n, hn⟩) ^ (p ^ v) : onePlusPUnits hK) : Kˣ) : K) - 1) / _ = _
  rw [coe_gE_pow, add_sub_cancel_left]
  simp [alphaR]
  field_simp

/-- The product $\prod_ig_{i,n}^{a_ip^v}$. -/
def Ad (a : Fin f → Fin p) : Fsub hK (n * p ^ v) := ∏ i, gstep hK hπ hα1 hn v i ^ (a i : ℕ)

theorem phiHom_Ad (hN : 1 ≤ n * p ^ v) (a : Fin f → Fin p) :
    phiHom hK hπ hN (Ad hK hπ hα1 hn v a) = Multiplicative.ofAdd (Theta hK hα1 v a) := by
  unfold Ad
  rw [map_prod]
  simp only [map_pow, phiHom_gstep hK hπ hα1 hn v hN]
  rw [Theta, ofAdd_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← ofAdd_nsmul, nsmul_eq_mul]

end Step

theorem not_dvd_aux {n m a b : ℕ} (hn : ¬ p ∣ n) (h : n * p ^ a = m * p ^ b) (hab : a < b) :
    False := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have h2 : n = m * p ^ (k + 1) := by
    have : n * p ^ a = (m * p ^ (k + 1)) * p ^ a := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos a) this
  exact hn (h2 ▸ dvd_mul_of_dvd_right (dvd_pow_self p (Nat.succ_ne_zero k)) m)

/-- Uniqueness of the decomposition $N=np^v$ with $p\nmid n$. -/
theorem eq_of_mul_pow_eq {n m a b : ℕ} (hn : ¬ p ∣ n) (hm : ¬ p ∣ m)
    (h : n * p ^ a = m * p ^ b) : n = m ∧ a = b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact (not_dvd_aux hn h hab).elim
  · exact ⟨Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos a) h, rfl⟩
  · exact (not_dvd_aux hm h.symm hba).elim

theorem eq_zero_of_forall_dvd {x : ℤ_[p]} (h : ∀ k : ℕ, (p : ℤ_[p]) ^ k ∣ x) : x = 0 := by
  have : Tendsto (fun _ : ℕ => x) atTop (𝓝 0) :=
    tendsto_iff_dvd.2 fun k => Eventually.of_forall fun _ => by simpa using h k
  exact (tendsto_nhds_unique this tendsto_const_nhds).symm

section Main

variable [CharP K p] (hK : IsPField K p) {π : K} (hπ : modK K π = qi hK) {f : ℕ} {α : Fin f → K}
  (hα1 : ∀ i, modK K (α i) ≤ 1)

/-- The family with value $a_ip^v$ at $(i,n)$ and $0$ elsewhere. -/
def posFam (n v : ℕ) (a : Fin f → Fin p) : GenIdx p f → ℤ_[p] :=
  fun j => if (j.2 : ℕ) = n then ((a j.1 : ℕ) : ℤ_[p]) * (p : ℤ_[p]) ^ v else 0

theorem Pfam_posFam {n : ℕ} (hn : 0 < n ∧ ¬ p ∣ n) (v : ℕ) (a : Fin f → Fin p) :
    Pfam hK hπ hα1 (posFam n v a) = ((Ad hK hπ hα1 hn v a : Fsub hK (n * p ^ v)) : onePlusPUnits hK) := by
  have _ := t2_onePlusPUnits hK
  unfold Pfam
  rw [tprod_eq_prod (s := Finset.univ.image fun i : Fin f => ((i, ⟨n, hn⟩) : GenIdx p f))]
  · rw [Finset.prod_image (fun x _ y _ h => (Prod.ext_iff.1 h).1)]
    have hA : ((Ad hK hπ hα1 hn v a : Fsub hK (n * p ^ v)) : onePlusPUnits hK) =
        ∏ i, (gE hK hπ hα1 (i, ⟨n, hn⟩) ^ (p ^ v)) ^ (a i : ℕ) := by
      simp [Ad, gstep]
    rw [hA]
    refine Finset.prod_congr rfl fun i _ => ?_
    have e : ((a i : ℕ) : ℤ_[p]) * (p : ℤ_[p]) ^ v = ((p ^ v * (a i : ℕ) : ℕ) : ℤ_[p]) := by
      push_cast; ring
    simp only [posFam, ite_true]
    rw [e, zpPow_natCast, pow_mul]
  · intro j hj
    have : (j.2 : ℕ) ≠ n := by
      intro h
      apply hj
      rw [Finset.mem_image]
      exact ⟨j.1, Finset.mem_univ _, Prod.ext rfl (Subtype.ext h.symm)⟩
    simp [posFam, this, zpPow_zero]

/-- Decomposition of $\prod g^{b}$ at position $N=np^v$: $\prod_jg_j^{b_j}\equiv\prod_ig_{i,n}^{a_ip^v}$
modulo $1+P^{N+1}$, provided the lower digits of $b$ vanish and the digit at $N$ is $a$. -/
theorem digit_decomp {n : ℕ} (hn : 0 < n ∧ ¬ p ∣ n) (v : ℕ) {b : GenIdx p f → ℤ_[p]}
    (hb : DivCond (n * p ^ v) b) (a : Fin f → Fin p)
    (ha : ∀ i, (p : ℤ_[p]) ^ (v + 1) ∣ b (i, ⟨n, hn⟩) - ((a i : ℕ) : ℤ_[p]) * (p : ℤ_[p]) ^ v) :
    ∃ E ∈ Fsub hK (n * p ^ v + 1), Pfam hK hπ hα1 b =
      ((Ad hK hπ hα1 hn v a : Fsub hK (n * p ^ v)) : onePlusPUnits hK) * E := by
  have hN : 1 ≤ n * p ^ v := Nat.mul_pos hn.1 (pow_pos hp.out.pos v)
  refine ⟨Pfam hK hπ hα1 (b - posFam n v a), ?_, ?_⟩
  · refine tprod_mem_Fsub hK (multipliable_gE hK hπ hα1 _) fun j => ?_
    refine zpPow_gE_mem hK hπ hα1 (by omega) j _ fun w hw => ?_
    by_cases hjn : (j.2 : ℕ) = n
    · have hjeq : j = (j.1, ⟨n, hn⟩) := Prod.ext rfl (Subtype.ext hjn)
      have hwv : w ≤ v := by
        by_contra hlt0
        have hlt := not_le.1 hlt0
        have : n * p ^ v < n * p ^ w :=
          Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hp.out.one_lt hlt) hn.1
        rw [hjn] at hw
        omega
      simp only [Pi.sub_apply, posFam, hjn, ite_true]
      rcases hwv.lt_or_eq with hlt | rfl
      · have h1 : (p : ℤ_[p]) ^ (w + 1) ∣ b j := hb j w (by
          rw [hjn]; exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hp.out.one_lt hlt) hn.1)
        have h2 : (p : ℤ_[p]) ^ (w + 1) ∣ ((a j.1 : ℕ) : ℤ_[p]) * (p : ℤ_[p]) ^ v :=
          dvd_mul_of_dvd_right (pow_dvd_pow _ hlt) _
        exact dvd_sub h1 h2
      · have := ha j.1
        rwa [← hjeq] at this
    · simp [Pi.sub_apply, posFam, hjn]
      apply hb j w
      have hle : (j.2 : ℕ) * p ^ w ≤ n * p ^ v := by omega
      rcases hle.lt_or_eq with h | h
      · exact h
      · exact absurd (eq_of_mul_pow_eq j.2.2.2 hn.2 h).1 hjn
  · have hsplit : Pfam hK hπ hα1 b = Pfam hK hπ hα1 (b - posFam n v a) *
        Pfam hK hπ hα1 (posFam n v a) := by
      rw [← Pfam_add, sub_add_cancel]
    rw [hsplit, Pfam_posFam, mul_comm]

/-- If $\prod g^c=1$ and the digits of $c$ below $N$ vanish then so does the digit at $N$. -/
theorem divCond_succ_of_prod_eq_one (hbij : ∀ v, Function.Bijective (Theta hK hα1 v))
    {c : GenIdx p f → ℤ_[p]} (hc : Pfam hK hπ hα1 c = 1) {N : ℕ} (hN : 1 ≤ N)
    (h : DivCond N c) : DivCond (N + 1) c := by
  obtain ⟨v, n, hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := N) (by omega) p hp.out.ne_one
  have hNe' : N = n * p ^ v := by rw [hNe, mul_comm]
  subst hNe'
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hn : 0 < n ∧ ¬ p ∣ n := ⟨hnpos, hn'⟩
  have hdv : ∀ i, (p : ℤ_[p]) ^ v ∣ c (i, ⟨n, hn⟩) := by
    intro i
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · simp
    · have := h (i, ⟨n, hn⟩) (v - 1)
        (Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hp.out.one_lt (by omega)) hnpos)
      rwa [Nat.sub_add_cancel hv] at this
  choose c' hc' using hdv
  have hlt : ∀ i, (c' i).appr 1 < p := fun i => by simpa using PadicInt.appr_lt (c' i) 1
  let a : Fin f → Fin p := fun i => ⟨(c' i).appr 1, hlt i⟩
  have hspec : ∀ i, (p : ℤ_[p]) ∣ c' i - ((a i : ℕ) : ℤ_[p]) := fun i => by
    simpa using Ideal.mem_span_singleton.1 (PadicInt.appr_spec 1 (c' i))
  have ha : ∀ i, (p : ℤ_[p]) ^ (v + 1) ∣
      c (i, ⟨n, hn⟩) - ((a i : ℕ) : ℤ_[p]) * (p : ℤ_[p]) ^ v := fun i => by
    have e : c (i, ⟨n, hn⟩) - ((a i : ℕ) : ℤ_[p]) * (p : ℤ_[p]) ^ v =
        (p : ℤ_[p]) ^ v * (c' i - ((a i : ℕ) : ℤ_[p])) := by rw [hc' i]; ring
    rw [e, pow_succ]
    exact mul_dvd_mul_left _ (hspec i)
  obtain ⟨E, hE, hP⟩ := digit_decomp hK hπ hα1 hn v h a ha
  have hN' : 1 ≤ n * p ^ v := hN
  have hAd : ((Ad hK hπ hα1 hn v a : Fsub hK (n * p ^ v)) : onePlusPUnits hK) ∈
      Fsub hK (n * p ^ v + 1) := by
    rw [hc] at hP
    have : ((Ad hK hπ hα1 hn v a : Fsub hK (n * p ^ v)) : onePlusPUnits hK) = E⁻¹ :=
      eq_inv_of_mul_eq_one_left hP.symm
    rw [this]
    exact (Fsub hK _).inv_mem hE
  have h1 := (phiHom_eq_one_iff hK hπ hN' _).2 hAd
  rw [phiHom_Ad hK hπ hα1 hn v hN' a] at h1
  have h2 : Theta hK hα1 v a = Theta hK hα1 v 0 := by
    have := ofAdd_eq_one.1 h1
    rw [this]
    simp [Theta]
  have h3 : a = 0 := (hbij v).1 h2
  have h4 : ∀ i, (p : ℤ_[p]) ∣ c' i := fun i => by
    have := hspec i
    have h5 : ((a i : ℕ) : ℤ_[p]) = 0 := by rw [h3]; simp
    rwa [h5, sub_zero] at this
  intro j w hw
  rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hlt' | heq
  · exact h j w hlt'
  · obtain ⟨hjn, hwv⟩ := eq_of_mul_pow_eq j.2.2.2 hn' heq
    have hjeq : j = (j.1, ⟨n, hn⟩) := Prod.ext rfl (Subtype.ext hjn)
    rw [hjeq, hc' j.1, hwv, pow_succ]
    exact mul_dvd_mul_left _ (h4 j.1)

theorem eq_zero_of_Pfam_eq_one (hbij : ∀ v, Function.Bijective (Theta hK hα1 v))
    {c : GenIdx p f → ℤ_[p]} (hc : Pfam hK hπ hα1 c = 1) : c = 0 := by
  have hall : ∀ N, 1 ≤ N → DivCond N c := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact divCond_one c
    | succ N hN ih => exact divCond_succ_of_prod_eq_one hK hπ hα1 hbij hc hN ih
  funext j
  refine eq_zero_of_forall_dvd fun k => ?_
  rcases k with _ | v
  · simp
  · exact hall ((j.2 : ℕ) * p ^ v + 1) (by omega) j v (Nat.lt_succ_self _)

theorem exists_Pfam_close (hbij : ∀ v, Function.Bijective (Theta hK hα1 v)) (u : onePlusPUnits hK) :
    ∀ N, 1 ≤ N → ∃ b : GenIdx p f → ℤ_[p], u * (Pfam hK hπ hα1 b)⁻¹ ∈ Fsub hK N := by
  have _ := t2_onePlusPUnits hK
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact ⟨0, mem_Fsub_one hK _⟩
  | succ N hN ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨v, n, hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := N) (by omega) p hp.out.ne_one
    have hNe' : N = n * p ^ v := by rw [hNe, mul_comm]
    subst hNe'
    have hnpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hn : 0 < n ∧ ¬ p ∣ n := ⟨hnpos, hn'⟩
    let w : Fsub hK (n * p ^ v) := ⟨u * (Pfam hK hπ hα1 b)⁻¹, hb⟩
    obtain ⟨a, ha⟩ := (hbij v).2 (Multiplicative.toAdd (phiHom hK hπ hN w))
    have hcd : DivCond (n * p ^ v) (posFam n v a) := by
      intro j w' hw'
      by_cases hjn : (j.2 : ℕ) = n
      · simp only [posFam, hjn, ite_true]
        have hlt : w' < v := by
          by_contra hge
          have hge := not_lt.1 hge
          have : n * p ^ v ≤ n * p ^ w' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.out.pos hge)
          rw [hjn] at hw'
          omega
        exact dvd_mul_of_dvd_right (pow_dvd_pow _ hlt) _
      · simp [posFam, hjn]
    obtain ⟨E, hE, hP⟩ := digit_decomp hK hπ hα1 hn v hcd a (fun i => by simp [posFam])
    refine ⟨b + posFam n v a, ?_⟩
    have hker : ((w * (Ad hK hπ hα1 hn v a)⁻¹ : Fsub hK (n * p ^ v)) : onePlusPUnits hK) ∈
        Fsub hK (n * p ^ v + 1) := by
      refine (phiHom_eq_one_iff hK hπ hN _).1 ?_
      have hw' : phiHom hK hπ hN w = Multiplicative.ofAdd (Theta hK hα1 v a) := by rw [ha]; rfl
      rw [map_mul, map_inv, phiHom_Ad hK hπ hα1 hn v hN a, hw']
      simp
    have e : u * (Pfam hK hπ hα1 (b + posFam n v a))⁻¹ =
        ((w * (Ad hK hπ hα1 hn v a)⁻¹ : Fsub hK (n * p ^ v)) : onePlusPUnits hK) * E⁻¹ := by
      rw [Pfam_add, hP]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, w, mul_inv_rev, mul_comm,
        mul_left_comm]
    rw [e]
    exact (Fsub hK _).mul_mem hker ((Fsub hK _).inv_mem hE)

theorem exists_Pfam_eq (hbij : ∀ v, Function.Bijective (Theta hK hα1 v)) (u : onePlusPUnits hK) :
    ∃ b : GenIdx p f → ℤ_[p], Pfam hK hπ hα1 b = u := by
  have _ := t2_onePlusPUnits hK
  choose bN hbN using fun N : ℕ => exists_Pfam_close hK hπ hα1 hbij u (N + 1) (by omega)
  obtain ⟨bs, hbs⟩ := exists_clusterPt_of_compactSpace (Filter.map bN atTop)
  have hbs' : MapClusterPt bs atTop bN := hbs
  refine ⟨bs, ?_⟩
  have key : ∀ M, 1 ≤ M → u * (Pfam hK hπ hα1 bs)⁻¹ ∈ Fsub hK M := by
    intro M hM
    have hW : {b' : GenIdx p f → ℤ_[p] | DivCond M (bs - b')} ∈ 𝓝 bs := by
      have hfin := finite_gen_lt (p := p) (f := f) M
      have h1 : ∀ j ∈ hfin.toFinset, ∀ w ∈ Finset.range M,
          ∀ᶠ b' in 𝓝 bs, (p : ℤ_[p]) ^ (w + 1) ∣ bs j - b' j := by
        intro j _ w _
        filter_upwards [tendsto_iff_dvd.1 ((continuous_apply j).tendsto bs) (w + 1)] with b' hb'
        exact dvd_sub_comm.1 hb'
      have h2 := (Filter.eventually_all_finset _).2 fun j hj =>
        (Filter.eventually_all_finset _).2 (h1 j hj)
      filter_upwards [h2] with b' hb' j w hw
      have hj : j ∈ hfin.toFinset := by
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (pow_pos hp.out.pos w)) hw
      have hwM : w ∈ Finset.range M := by
        rw [Finset.mem_range]
        have h3 : w < p ^ w := Nat.lt_pow_self hp.out.one_lt
        have h4 : p ^ w ≤ (j.2 : ℕ) * p ^ w := Nat.le_mul_of_pos_left _ j.2.2.1
        omega
      exact hb' j hj w hwM
    obtain ⟨N, hN, hNM⟩ := (((mapClusterPt_iff_frequently.1 hbs') _ hW).and_eventually
      (eventually_ge_atTop M)).exists
    have h1 : Pfam hK hπ hα1 (bs - bN N) ∈ Fsub hK M := Pfam_mem_Fsub hK hπ hα1 hM hN
    have h2 : u * (Pfam hK hπ hα1 (bN N))⁻¹ ∈ Fsub hK M := Fsub_mono hK (by omega) (hbN N)
    have e : u * (Pfam hK hπ hα1 bs)⁻¹ =
        (u * (Pfam hK hπ hα1 (bN N))⁻¹) * (Pfam hK hπ hα1 (bs - bN N))⁻¹ := by
      have : Pfam hK hπ hα1 bs = Pfam hK hπ hα1 (bs - bN N) * Pfam hK hπ hα1 (bN N) := by
        rw [← Pfam_add, sub_add_cancel]
      rw [this]
      group
    rw [e]
    exact (Fsub hK M).mul_mem h2 ((Fsub hK M).inv_mem h1)
  exact (mul_inv_eq_one.1 (eq_one_of_forall_mem_Fsub hK key)).symm

end Main

/-- **Weil, II.§3, Prop. 10.** In characteristic $p$, for a prime element $\pi$ and a residue basis $\alpha$, the
$g_{i,n}=1+\alpha_i\pi^n$ ($p\nmid n$) are free topological generators of the $\mathbb Z_p$-module $1+P$: every product
$\prod_{(i,n)}g_{i,n}^{b_{i,n}}$ ($b_{i,n}\in\mathbb Z_p$) converges in $1+P$, and each $u\in1+P$ is such a product for
exactly one family $b$. -/
@[kb "weil1973bnt" "Ch. II, §3, Prop. 10"]
theorem weil_II_3_prop10 [CharP K p] (hK : IsPField K p) {π : K} (hπ0 : π ≠ 0)
    (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K)) {f : ℕ} (hf : pq hK = p ^ f) {α : Fin f → K}
    (hα : IsResidueBasis hK α) :
    haveI hπ1 : modK K π < 1 := by rw [weil_I_4_thm6_modK_prime hK hπ0 hπ]; exact qi_lt_one hK
    (∀ b : GenIdx p f → ℤ_[p], Multipliable fun j => zpPow hK (b j) (genElt hK hπ1 hα.1 j)) ∧
      ∀ u : onePlusPUnits hK, ∃! b : GenIdx p f → ℤ_[p],
        HasProd (fun j => zpPow hK (b j) (genElt hK hπ1 hα.1 j)) u := by
  have hπq : modK K π = qi hK := weil_I_4_thm6_modK_prime hK hπ0 hπ
  have hbij : ∀ v, Function.Bijective (Theta hK hα.1 v) := fun v =>
    theta_bijective hK hα.1 (theta_zero_bijective hK hα.1 hα.2) v
  have _ := t2_onePlusPUnits hK
  refine ⟨fun b => multipliable_gE hK hπq hα.1 b, fun u => ?_⟩
  obtain ⟨b, hb⟩ := exists_Pfam_eq hK hπq hα.1 hbij u
  have hhas : ∀ b : GenIdx p f → ℤ_[p],
      HasProd (fun j => zpPow hK (b j) (gE hK hπq hα.1 j)) (Pfam hK hπq hα.1 b) := fun b =>
    (multipliable_gE hK hπq hα.1 b).hasProd
  have hu : HasProd (fun j => zpPow hK (b j) (gE hK hπq hα.1 j)) u := by
    rw [← hb]; exact hhas b
  refine ⟨b, hu, fun b' hb' => ?_⟩
  have h1 : HasProd (fun j => zpPow hK ((b' - b) j) (gE hK hπq hα.1 j)) 1 := by
    have h2 := hb'.div hu
    rw [div_self'] at h2
    convert h2 using 1
    funext j
    have h4 := zpPow_add hK ((b' - b) j) (b j) (gE hK hπq hα.1 j)
    simp only [Pi.sub_apply, sub_add_cancel] at h4 ⊢
    rw [h4, mul_div_cancel_right]
  have h3 : Pfam hK hπq hα.1 (b' - b) = 1 := h1.tprod_eq
  exact sub_eq_zero.1 (eq_zero_of_Pfam_eq_one hK hπq hα.1 hbij h3)

end NumberFieldKB.WeilBNT.FieldModule
