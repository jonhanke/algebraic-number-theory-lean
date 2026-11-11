import Mathlib.GroupTheory.FiniteAbelian.Basic

open scoped DirectSum

namespace NumberFieldKB.MilneCFT

lemma zmod_inj_aux (m n : ℕ) [NeZero n] (h : m ∣ n) (x : ZMod m) (hx : x ≠ 0) :
    ∃ f : ZMod m →+ ZMod n, f x ≠ 0 := by
  obtain ⟨d, hd⟩ := h
  have hm : m ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (by simpa using hd)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (by simpa using hd)
  have : NeZero m := ⟨hm⟩
  refine ⟨ZMod.lift m ⟨(AddMonoidHom.mulLeft (d : ZMod n)).comp (Int.castAddHom (ZMod n)), ?_⟩, ?_⟩
  · simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom, AddMonoidHom.coe_mulLeft]
    have : ((m * d : ℕ) : ZMod n) = 0 := by
      rw [← hd]; exact ZMod.natCast_self n
    push_cast at this
    simpa [mul_comm] using this
  · have hx' : x = ((x.val : ℤ) : ZMod m) := by simp
    rw [hx', ZMod.lift_coe]
    simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom, AddMonoidHom.coe_mulLeft]
    have : (d : ZMod n) * ((x.val : ℤ) : ZMod n) = ((d * x.val : ℕ) : ZMod n) := by
      push_cast; ring
    rw [this, Ne, ZMod.natCast_eq_zero_iff, hd]
    intro hdvd
    have h2 : m ∣ x.val := by
      have : d * m ∣ d * x.val := by rw [mul_comm d m]; exact hdvd
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd0)).1 this
    have hv : x.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hx
    exact hv (Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt x))

/-- Characters with values in ℤ/n separate the points of a finite abelian group of exponent dividing n. -/
theorem exists_zmod_char_ne_zero {G : Type} [AddCommGroup G] [Finite G] {n : ℕ} [NeZero n]
    (hG : ∀ g : G, n • g = 0) (g : G) (hg : g ≠ 0) : ∃ χ : G →+ ZMod n, χ g ≠ 0 := by
  classical
  obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  have hne : e g ≠ 0 := by simpa using hg
  obtain ⟨i, hi⟩ : ∃ i, (e g) i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (DFinsupp.ext (fun i => by simpa using hcon i))
  have hdvd : m i ∣ n := by
    have h1 : n • (DirectSum.of (fun j => ZMod (m j)) i 1) = 0 := by
      have := hG (e.symm (DirectSum.of (fun j => ZMod (m j)) i 1))
      have h3 := congrArg e this
      simpa using h3
    have h4 := congrArg (fun y => y i) h1
    simp only [DirectSum.smul_apply, DirectSum.of_eq_same, DirectSum.zero_apply] at h4
    rw [← ZMod.natCast_eq_zero_iff]
    simpa [nsmul_eq_mul] using h4
  obtain ⟨f, hf⟩ := zmod_inj_aux (m i) n hdvd _ hi
  exact ⟨f.comp ((DirectSum.component ℤ ι (fun j => ZMod (m j)) i).toAddMonoidHom.comp
    e.toAddMonoidHom), by show ¬ f ((e g) i) = 0; exact hf⟩

end NumberFieldKB.MilneCFT
