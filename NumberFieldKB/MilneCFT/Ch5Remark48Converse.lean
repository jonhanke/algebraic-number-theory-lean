import NumberFieldKB.MilneCFT.Ch5Remark48Corrected

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 4.8: the converse (with the hypothesis at the infinite places)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Remark 4.8, p. 174.
See `Ch5Remark48Corrected.lean` for the statement `Remark4_8Corrected` and the proof outline.
-/

open NumberField IsDedekindDomain Topology
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-- The open subgroup of idèles that are `1` at the infinite places, in `1 + p^N` at `T` (`N ≥ 1`) and units elsewhere. -/
def smallIdeles (T : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (hN : 1 ≤ N) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {y | (∀ w, ideleInfAt y w = 1) ∧ (∀ v ∈ T, Valued.v (ideleFinAt y v - 1) ≤ WithZero.exp (-(N : ℤ))) ∧
    (∀ v ∉ T, Valued.v (ideleFinAt y v) = 1)}
  mul_mem' := by
    have hlt : WithZero.exp (-(N : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [ideleInfAt_mul, hx1 w, hy1 w, one_mul]
    · rw [ideleFinAt_mul]; exact val_mul_sub_one_le Valued.v hlt (hx2 v hv) (hy2 v hv)
    · rw [ideleFinAt_mul, map_mul, hx3 v hv, hy3 v hv, one_mul]
  one_mem' := ⟨fun w => ideleInfAt_one w, fun v _ => by
    rw [ideleFinAt_one, sub_self, map_zero]; exact zero_le, fun v _ => by rw [ideleFinAt_one, map_one]⟩
  inv_mem' := by
    have hlt : WithZero.exp (-(N : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    rintro x ⟨hx1, hx2, hx3⟩
    refine ⟨fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [ideleInfAt_inv, hx1 w, inv_one]
    · rw [ideleFinAt_inv]; exact val_inv_sub_one_le Valued.v hlt (hx2 v hv)
    · rw [ideleFinAt_inv, map_inv₀, hx3 v hv, inv_one]

/-- The analogue of `ker_contains` for groups with no small subgroups, using the hypothesis at the infinite places. -/
theorem ker_contains_nss {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : NoSmallSubgroups G) (φ : IdeleGroup (𝓞 K) K →* G) (hφ : Continuous φ)
    (hinf : ∀ x : IdeleGroup (𝓞 K) K, (∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) →
      (∀ v, ideleFinAt x v = 1) → φ x = 1) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ), ∀ x : IdeleGroup (𝓞 K) K,
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) →
      (∀ v ∈ T, Valued.v (ideleFinAt x v - 1) ≤ WithZero.exp (-(n : ℤ))) →
      (∀ v ∉ T, Valued.v (ideleFinAt x v) = 1) → φ x = 1 := by
  obtain ⟨U, hU, hUH⟩ := hG
  obtain ⟨T, n, hTn⟩ := idele_nhds_one (hφ.continuousAt.preimage_mem_nhds (by simpa using hU))
  have hn1 : 1 ≤ n + 1 := by omega
  have hsub : ((Subgroup.map φ (smallIdeles T (n + 1) hn1) : Subgroup G) : Set G) ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hTn y hy.1 (fun v hv => (hy.2.1 v hv).trans (by rw [WithZero.exp_le_exp]; omega)) hy.2.2
  have hbot := hUH _ hsub
  refine ⟨T, n + 1, fun x h1 h2 h3 => ?_⟩
  have hy : x * (infPart x)⁻¹ ∈ smallIdeles T (n + 1) hn1 := by
    refine ⟨fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [ideleInfAt_mul, ideleInfAt_inv, ideleInfAt_infPart]
      exact mul_inv_cancel₀ (ideleInfAt_ne_zero x w)
    · rw [ideleFinAt_mul, ideleFinAt_inv, ideleFinAt_infPart, inv_one, mul_one]
      exact h2 v hv
    · rw [ideleFinAt_mul, ideleFinAt_inv, ideleFinAt_infPart, inv_one, mul_one]
      exact h3 v hv
  have hmem : φ (x * (infPart x)⁻¹) ∈ Subgroup.map φ (smallIdeles T (n + 1) hn1) := ⟨_, hy, rfl⟩
  rw [hbot, Subgroup.mem_bot, map_mul, map_inv, hinf (infPart x) (fun w hw => h1 w hw)
    (fun v => ideleFinAt_infPart x v), inv_one, mul_one] at hmem
  exact hmem

/-- **Remark 4.8, second sentence, corrected**: the converse for $\varphi$ trivial on the identity component of
$K_\infty^\times$. -/
@[kb "milne2020cft" "Ch. V, Remark 4.8 (converse, phi trivial on the identity component at infinity)"]
theorem remark4_8_converse (G : Type) [CommGroup G] [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
    (hG : NoSmallSubgroups G) (φ : IdeleGroup (𝓞 K) K →* G) (hφ : Continuous φ)
    (hK : ∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1)
    (hinf : ∀ x : IdeleGroup (𝓞 K) K, (∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) →
      (∀ v, ideleFinAt x v = 1) → φ x = 1) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 K))) (_ : S.Finite) (ψ : sIdeals S →* G), IsAdmissible S ψ ∧
      ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
        φ x = ψ b := by
  classical
  obtain ⟨T, n₀, h⟩ := ker_contains_nss hG φ hφ hinf
  set S : Set (HeightOneSpectrum (𝓞 K)) := ↑T with hSdef
  have hf : Function.Surjective (idealOfTrivialAt S) := by
    intro b
    obtain ⟨x0, hx0⟩ := item_4_1.1 (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    have hx0S : ∀ v ∈ T, Valued.v (ideleFinAt x0 v) = 1 := by
      intro v hv
      have hb := b.2
      rw [← hx0, ideleToIdeal_mem_sIdeals_iff] at hb
      exact hb v hv
    have hmem : x0 * (infPart x0 * localPart x0 T)⁻¹ ∈ idelesTrivialAt S := splitTriv_mem x0 T S le_rfl
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [idealOfTrivialAt_apply]
    show ideleToIdeal K (x0 * (infPart x0 * localPart x0 T)⁻¹) = _
    rw [ideleToIdeal_splitTriv x0 T hx0S, hx0]
  have hker : (idealOfTrivialAt S).ker ≤ (φ.comp (idelesTrivialAt S).subtype).ker := by
    intro x hx
    have hx1 : ideleToIdeal K (x : IdeleGroup (𝓞 K) K) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      exact this
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have hu := (item_4_1.2 _).1 hx1
    refine h x ?_ ?_ ?_
    · intro w hw
      show 0 < _
      rw [x.2.1 w]; simp
    · intro v hv
      rw [x.2.2 v hv, sub_self, map_zero]; exact zero_le
    · intro v _; exact hu v
  set ψ : sIdeals S →* G := (idealOfTrivialAt S).liftOfRightInverse (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨φ.comp (idelesTrivialAt S).subtype, hker⟩ with hψ
  have hψx : ∀ x : idelesTrivialAt S, ψ (idealOfTrivialAt S x) = φ x := fun x =>
    (idealOfTrivialAt S).liftOfRightInverse_comp_apply (Function.surjInv hf) (Function.rightInverse_surjInv hf)
      ⟨φ.comp (idelesTrivialAt S).subtype, hker⟩ x
  refine ⟨S, T.finite_toSet, ψ, ?_, ?_⟩
  · intro N hN
    obtain ⟨m, hminf, hmS, hmord⟩ := exists_modulus T (n₀ + 1) (by omega)
    refine ⟨m, hmS.le, fun a ha haS => ?_⟩
    set a' := IdeleGroup.unitEmbedding (𝓞 K) K a with ha'
    have ham : a' ∈ idelesMod m := (mem_congruenceSubgroup_iff_mem_idelesMod m a).1 ha
    have hunit : ∀ v ∈ T, Valued.v (ideleFinAt a' v) = 1 := by
      intro v hv
      refine val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one m v (by rw [hmS]; exact hv)) ?_
      exact ham.2 v (by rw [hmS]; exact hv)
    have hmem : a' * (infPart a' * localPart a' T)⁻¹ ∈ idelesTrivialAt S := splitTriv_mem a' T S le_rfl
    have hb : (⟨toPrincipalIdeal (𝓞 K) K a, haS⟩ : sIdeals S) = idealOfTrivialAt S ⟨_, hmem⟩ := by
      refine Subtype.ext ?_
      rw [idealOfTrivialAt_apply]
      show toPrincipalIdeal (𝓞 K) K a = ideleToIdeal K (a' * (infPart a' * localPart a' T)⁻¹)
      rw [ideleToIdeal_splitTriv a' T hunit, ha', ideleToIdeal_unitEmbedding]
    have hw : φ (infPart a' * localPart a' T) = 1 := by
      refine h _ (fun w' hw' => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · rw [ideleInfAt_mul, ideleInfAt_infPart, ideleInfAt_localPart, mul_one]
        exact ham.1 w' (by rw [hminf]; exact hw')
      · rw [ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart, if_pos hv, one_mul]
        refine (ham.2 v (by rw [hmS]; exact hv)).trans ?_
        rw [WithZero.exp_le_exp]
        have := hmord v hv
        omega
      · rw [ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart, if_neg hv, one_mul, map_one]
    suffices ψ ⟨toPrincipalIdeal (𝓞 K) K a, haS⟩ = 1 by rw [this]; exact mem_of_mem_nhds hN
    rw [hb, hψx]
    show φ (a' * (infPart a' * localPart a' T)⁻¹) = 1
    rw [map_mul, map_inv, hw, inv_one, mul_one, ha', hK a]
  · intro x hx b hb
    have : b = idealOfTrivialAt S ⟨x, hx⟩ := Subtype.ext (by rw [idealOfTrivialAt_apply]; exact hb)
    rw [this, hψx]

end NumberFieldKB.MilneCFT
