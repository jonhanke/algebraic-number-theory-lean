import NumberFieldKB.MilneCFT.Ch5Complements
import NumberFieldKB.MilneCFT.Ch5IdelicReciprocityTauCeti
import NumberFieldKB.MilneCFT.Ch7.IdealReciprocityKer
import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 3.8 (the conductor), unconditional

The named statement `Remark3_8` (every finite abelian extension $L/K$ has a conductor $\mathfrak f(L/K)$, the least
modulus through which the Artin map factors, and its support is exactly the ramified places) is proved here
(`remark3_8`) from the idèlic reciprocity law (`idelicReciprocity`, Tau Ceti).

The proof is idèlic.  For the idèlic Artin map $\phi$ of $L/K$:

* `artinFactorsThrough_iff`: $\psi_{L/K}$ factors through $C_\mathfrak m$ iff $L$ is unramified outside $\mathfrak m$ and
  $W_\mathfrak m\subseteq\ker\phi$ (`idelesW`).  The easy direction is the computation of
  `le_ker_artinMap_of_idelic`; the other one uses weak approximation to move an idèle of $W_\mathfrak m$ into
  $I_{\mathfrak m'}$ for a multiple $\mathfrak m'$ of $\mathfrak m$ on which $\phi$ is the ideal-theoretic Artin map.
* `Modulus.gcd`, `idelesW_gcd_le`: $W_{\gcd(\mathfrak m_1,\mathfrak m_2)} \subseteq W_{\mathfrak m_1}W_{\mathfrak m_2}$
  (a local computation), hence `ArtinFactorsThrough` is closed under $\gcd$.
* The set of moduli through which $\psi$ factors has a gcd-least element (the finite parts form a Noetherian family,
  the infinite parts a finite one).
* Support: the finite support of any such modulus contains the ramified primes (unramified outside $\mathfrak m$) and
  is contained in that of a defining modulus (`reciprocityLaw_ideal_of_idelic`); a ramified real place has
  $\phi(-1_w)\ne1$ (`infiniteLocalArtinAt_eq_one_iff_mem_normGroup`), so it lies in the infinite part.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped nonZeroDivisors IsMulCommutative

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## Moduli: divisibility, orders, gcd -/

theorem Modulus.pow_dvd_iff_le_ord (m : Modulus K) (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    v.asIdeal ^ k ∣ m.finite ↔ k ≤ m.ord v := by
  have hm : Associates.mk m.finite ≠ 0 := Associates.mk_ne_zero.2 m.finite_ne_bot
  rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
  exact Associates.prime_pow_dvd_iff_le hm v.associates_irreducible

theorem Modulus.ord_le_of_dvd {f m : Modulus K} (hd : f.Dvd m) (v : HeightOneSpectrum (𝓞 K)) :
    f.ord v ≤ m.ord v := by
  rw [← Modulus.pow_dvd_iff_le_ord]
  exact (Modulus.pow_dvd_iff_le_ord f v _).2 le_rfl |>.trans hd.1

/-- The gcd of two moduli: sum of the finite parts, intersection of the infinite parts. -/
def Modulus.gcd (m₁ m₂ : Modulus K) : Modulus K where
  finite := m₁.finite ⊔ m₂.finite
  finite_ne_bot := fun h => m₁.finite_ne_bot (eq_bot_iff.2 (le_sup_left.trans h.le))
  infinite := m₁.infinite ∩ m₂.infinite
  isReal_of_mem := fun v hv => m₁.isReal_of_mem v hv.1

theorem Modulus.gcd_dvd_left (m₁ m₂ : Modulus K) : (Modulus.gcd m₁ m₂).Dvd m₁ :=
  ⟨Ideal.dvd_iff_le.2 le_sup_left, Set.inter_subset_left⟩

theorem Modulus.gcd_dvd_right (m₁ m₂ : Modulus K) : (Modulus.gcd m₁ m₂).Dvd m₂ :=
  ⟨Ideal.dvd_iff_le.2 le_sup_right, Set.inter_subset_right⟩

theorem Modulus.dvd_gcd {f m₁ m₂ : Modulus K} (h₁ : f.Dvd m₁) (h₂ : f.Dvd m₂) :
    f.Dvd (Modulus.gcd m₁ m₂) :=
  ⟨Ideal.dvd_iff_le.2 (sup_le (Ideal.dvd_iff_le.1 h₁.1) (Ideal.dvd_iff_le.1 h₂.1)),
    Set.subset_inter h₁.2 h₂.2⟩

theorem Modulus.min_ord_le_gcd (m₁ m₂ : Modulus K) (v : HeightOneSpectrum (𝓞 K)) :
    min (m₁.ord v) (m₂.ord v) ≤ (Modulus.gcd m₁ m₂).ord v := by
  rw [← Modulus.pow_dvd_iff_le_ord]
  refine Ideal.dvd_iff_le.2 (sup_le (Ideal.dvd_iff_le.1 ?_) (Ideal.dvd_iff_le.1 ?_))
  · exact (Modulus.pow_dvd_iff_le_ord _ _ _).2 (min_le_left _ _)
  · exact (Modulus.pow_dvd_iff_le_ord _ _ _).2 (min_le_right _ _)

/-! ## Monotonicity of the idèle groups -/

theorem idelesMod_le_of_dvd {f m : Modulus K} (hd : f.Dvd m) : idelesMod m ≤ idelesMod f := by
  rintro x ⟨h1, h2⟩
  refine ⟨fun w hw => h1 w (hd.2 hw), fun v hv => ?_⟩
  have hvm : v ∈ m.finiteSupport := (show v.asIdeal ∣ f.finite from hv).trans hd.1
  refine (h2 v hvm).trans (WithZero.exp_le_exp.2 ?_)
  have := Modulus.ord_le_of_dvd hd v
  omega

theorem idelesW_unit {m : Modulus K} {x : IdeleGroup (𝓞 K) K} (hx : x ∈ idelesW m)
    (v : HeightOneSpectrum (𝓞 K)) : Valued.v (ideleFinAt x v) = 1 := by
  by_cases hv : v ∈ m.finiteSupport
  · exact val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one m v hv) (hx.1.2 v hv)
  · exact hx.2 v hv

theorem idelesW_le_of_dvd {f m : Modulus K} (hd : f.Dvd m) : idelesW m ≤ idelesW f :=
  fun _ hx => ⟨idelesMod_le_of_dvd hd hx.1, fun v _ => idelesW_unit hx v⟩

/-! ## `ArtinFactorsThrough` in terms of the idèlic Artin map -/

section Idelic

variable (hR : IdelicReciprocity K) (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- If $L$ is unramified outside $\mathfrak m$ and $W_\mathfrak m\subseteq\ker\phi$, then $\psi_{L/K}$ factors through
$C_\mathfrak m$. -/
theorem artinFactorsThrough_of_idelesW (m : Modulus K)
    (hm : ∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L) (hW : idelesW m ≤ (idelicArtinOf hR L).ker) :
    ArtinFactorsThrough L m := by
  refine ⟨hm, fun a ha ha' => ?_⟩
  have h1 : artinTot L (toPrincipalIdeal (𝓞 K) K a) = 1 := by
    rw [← ideleToIdeal_unitEmbedding, ← idelicArtinOf_eq_artinTot hR L m hm hW _
      ((mem_congruenceSubgroup_iff_mem_idelesMod m a).mp ha),
      (idelicArtinOf_spec hR L).2.1 a]
  exact h1

/-- If $\psi_{L/K}$ factors through $C_\mathfrak m$ then $W_\mathfrak m\subseteq\ker\phi$. -/
theorem idelesW_le_ker_of_artinFactorsThrough (m : Modulus K) (h : ArtinFactorsThrough L m) :
    idelesW m ≤ (idelicArtinOf hR L).ker := by
  classical
  obtain ⟨M, hMs, hMinf, hMW⟩ := exists_modulus_idelesW_le_ker hR L
  let m' : Modulus K := ⟨m.finite * M.finite, mul_ne_zero m.finite_ne_bot M.finite_ne_bot,
    m.infinite ∪ M.infinite, fun w hw => hw.elim (m.isReal_of_mem w) (M.isReal_of_mem w)⟩
  have hdm : m.Dvd m' := ⟨dvd_mul_right _ _, Set.subset_union_left⟩
  have hdM : M.Dvd m' := ⟨dvd_mul_left _ _, Set.subset_union_right⟩
  have hm' : ∀ v, v ∉ m'.finiteSupport → v ∈ unramifiedPrimes K L := fun v hv => by
    by_contra hc
    have hvM : v ∈ M.finiteSupport := by rw [hMs]; exact hc
    exact hv ((show v.asIdeal ∣ M.finite from hvM).trans hdM.1)
  have hW' : idelesW m' ≤ (idelicArtinOf hR L).ker := (idelesW_le_of_dvd hdM).trans hMW
  intro x hx
  obtain ⟨b, hb⟩ := exists_unitEmbedding_mul_mem_idelesMod m' x
  set y := IdeleGroup.unitEmbedding (𝓞 K) K b * x with hy
  have hφy := idelicArtinOf_eq_artinTot hR L m' hm' hW' y hb
  have hx1 : ideleToIdeal K x = 1 := (item_4_1 (K := K)).2 x |>.2 (idelesW_unit hx)
  have hyid : ideleToIdeal K y = toPrincipalIdeal (𝓞 K) K b := by
    rw [hy, map_mul, ideleToIdeal_unitEmbedding, hx1, mul_one]
  have hbm : b ∈ congruenceSubgroup m := by
    rw [mem_congruenceSubgroup_iff_mem_idelesMod]
    have : IdeleGroup.unitEmbedding (𝓞 K) K b = y * x⁻¹ := by rw [hy]; group
    rw [this]
    exact mul_mem (idelesMod_le_of_dvd hdm hb) (inv_mem hx.1)
  have hmem : toPrincipalIdeal (𝓞 K) K b ∈ sIdeals m.finiteSupport := by
    have := rayPrincipal_le m ⟨b, hbm, rfl⟩
    rwa [coprimeIdeals_eq_sIdeals] at this
  have h2 := h.2 b hbm hmem
  rw [MonoidHom.mem_ker]
  have h3 : idelicArtinOf hR L y = idelicArtinOf hR L x := by
    rw [hy, map_mul, (idelicArtinOf_spec hR L).2.1 b, one_mul]
  rw [← h3, hφy, hyid]
  exact h2

theorem artinFactorsThrough_iff (m : Modulus K) :
    ArtinFactorsThrough L m ↔
      (∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L) ∧ idelesW m ≤ (idelicArtinOf hR L).ker :=
  ⟨fun h => ⟨h.1, idelesW_le_ker_of_artinFactorsThrough hR L m h⟩,
    fun h => artinFactorsThrough_of_idelesW hR L m h.1 h.2⟩

end Idelic

/-! ## `W_gcd ⊆ W_{m₁} W_{m₂}` -/

theorem Modulus.gcd_aux {m₁ m₂ : Modulus K} {v : HeightOneSpectrum (𝓞 K)} (h₁ : v ∈ m₁.finiteSupport)
    (h₂ : m₁.ord v ≤ m₂.ord v) :
    v ∈ (Modulus.gcd m₁ m₂).finiteSupport ∧ m₁.ord v ≤ (Modulus.gcd m₁ m₂).ord v := by
  have h := Modulus.min_ord_le_gcd m₁ m₂ v
  rw [min_eq_left h₂] at h
  have h1 := one_le_ord m₁ v h₁
  exact ⟨(modulus_mem_finiteSupport_iff _ v).2 (by omega), h⟩

theorem Modulus.gcd_aux' {m₁ m₂ : Modulus K} {v : HeightOneSpectrum (𝓞 K)} (h₂ : v ∈ m₂.finiteSupport)
    (h₁ : m₂.ord v ≤ m₁.ord v) :
    v ∈ (Modulus.gcd m₁ m₂).finiteSupport ∧ m₂.ord v ≤ (Modulus.gcd m₁ m₂).ord v := by
  have h := Modulus.min_ord_le_gcd m₁ m₂ v
  rw [min_eq_right h₁] at h
  have h1 := one_le_ord m₂ v h₂
  exact ⟨(modulus_mem_finiteSupport_iff _ v).2 (by omega), h⟩

theorem Modulus.mem_gcd_finiteSupport {m₁ m₂ : Modulus K} {v : HeightOneSpectrum (𝓞 K)}
    (h₁ : v ∈ m₁.finiteSupport) (h₂ : v ∈ m₂.finiteSupport) : v ∈ (Modulus.gcd m₁ m₂).finiteSupport := by
  rcases le_total (m₁.ord v) (m₂.ord v) with h | h
  · exact (Modulus.gcd_aux h₁ h).1
  · exact (Modulus.gcd_aux' h₂ h).1

theorem idelesW_gcd_le (m₁ m₂ : Modulus K) :
    idelesW (Modulus.gcd m₁ m₂) ≤ idelesW m₁ ⊔ idelesW m₂ := by
  classical
  intro x hx
  have hAfin : {v | v ∈ m₁.finiteSupport ∧ m₂.ord v < m₁.ord v}.Finite :=
    (Ideal.finite_factors m₁.finite_ne_bot).subset fun v hv => hv.1
  set A := hAfin.toFinset with hA
  have hAmem : ∀ v, v ∈ A ↔ v ∈ m₁.finiteSupport ∧ m₂.ord v < m₁.ord v := fun v => by
    rw [hA, Set.Finite.mem_toFinset]; rfl
  set B : Finset (InfinitePlace K) := Finset.univ.filter (fun w => w ∈ m₁.infinite ∧ w ∉ m₂.infinite) with hB
  have hBmem : ∀ w, w ∈ B ↔ w ∈ m₁.infinite ∧ w ∉ m₂.infinite := fun w => by
    rw [hB, Finset.mem_filter]; simp
  set uf : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ :=
    fun v => Units.mk0 (ideleFinAt x v) (ideleFinAt_ne_zero x v) with huf
  set ui : (w : InfinitePlace K) → w.Completionˣ :=
    fun w => Units.mk0 (ideleInfAt x w) (ideleInfAt_ne_zero x w) with hui
  set F : InfinitePlace K → IdeleGroup (𝓞 K) K := fun w => IdeleGroup.ofCompletion (𝓞 K) K w (ui w) with hF
  set t : IdeleGroup (𝓞 K) K := prodOfAdic A uf * ∏ w ∈ B, F w with ht
  have htfin : ∀ v, ideleFinAt t v = if v ∈ A then ideleFinAt x v else 1 := by
    intro v
    have h1 : ideleFinAt (∏ w ∈ B, F w) v = ∏ w ∈ B, ideleFinAt (F w) v :=
      map_prod (finAtHom v) F B
    have h2 : ideleFinAt (∏ w ∈ B, F w) v = 1 := by
      rw [h1]; exact Finset.prod_eq_one fun w _ => ideleFinAt_ofCompletion w _ v
    rw [ht, ideleFinAt_mul, h2, mul_one, ideleFinAt_prodOfAdic]
    split_ifs <;> rfl
  have htinf : ∀ w, ideleInfAt t w = if w ∈ B then ideleInfAt x w else 1 := by
    intro w
    have h1 : ideleInfAt (∏ w' ∈ B, F w') w = ∏ w' ∈ B, ideleInfAt (F w') w :=
      map_prod (infAtHom w) F B
    rw [ht, ideleInfAt_mul, ideleInfAt_prodOfAdic, one_mul, h1]
    split_ifs with hw
    · rw [Finset.prod_eq_single_of_mem w hw]
      · rw [hF]; exact ideleInfAt_ofCompletion_self w (ui w)
      · intro w' _ hne
        exact ideleInfAt_ofCompletion_ne w' w (Ne.symm hne) _
    · exact Finset.prod_eq_one fun w' hw' => ideleInfAt_ofCompletion_ne w' w
        (by rintro rfl; exact hw hw') _
  have htunit : ∀ v, Valued.v (ideleFinAt t v) = 1 := by
    intro v
    rw [htfin]
    split_ifs
    · exact idelesW_unit hx v
    · exact map_one _
  have hxy : x = (x * t⁻¹) * t := by group
  rw [hxy]
  refine Subgroup.mul_mem_sup (x := x * t⁻¹) (y := t) ?_ ?_
  · -- `x t⁻¹ ∈ W_{m₁}`
    refine ⟨⟨fun w hw => ?_, fun v hv => ?_⟩, fun v _ => ?_⟩
    · by_cases hwB : w ∈ B
      · unfold IsPosAt
        rw [ideleInfAt_mul, ideleInfAt_inv, htinf, if_pos hwB, mul_inv_cancel₀ (ideleInfAt_ne_zero x w)]
        simp
      · have hw2 : w ∈ m₂.infinite := by
          by_contra hc
          exact hwB ((hBmem w).2 ⟨hw, hc⟩)
        have := hx.1.1 w (show w ∈ m₁.infinite ∩ m₂.infinite from ⟨hw, hw2⟩)
        unfold IsPosAt at this ⊢
        rw [ideleInfAt_mul, ideleInfAt_inv, htinf, if_neg hwB, inv_one, mul_one]
        exact this
    · by_cases hvA : v ∈ A
      · rw [ideleFinAt_mul, ideleFinAt_inv, htfin, if_pos hvA, mul_inv_cancel₀ (ideleFinAt_ne_zero x v),
          sub_self, map_zero]
        exact zero_le'
      · rw [ideleFinAt_mul, ideleFinAt_inv, htfin, if_neg hvA, inv_one, mul_one]
        have hle : m₁.ord v ≤ m₂.ord v := by
          by_contra hc
          exact hvA ((hAmem v).2 ⟨hv, not_le.1 hc⟩)
        obtain ⟨hvg, hog⟩ := Modulus.gcd_aux hv hle
        exact (hx.1.2 v hvg).trans (WithZero.exp_le_exp.2 (by omega))
    · rw [ideleFinAt_mul, ideleFinAt_inv, map_mul, map_inv₀, htunit v, idelesW_unit hx v]
      simp
  · -- `t ∈ W_{m₂}`
    refine ⟨⟨fun w hw => ?_, fun v hv => ?_⟩, fun v _ => htunit v⟩
    · have hwB : w ∉ B := fun h => ((hBmem w).1 h).2 hw
      unfold IsPosAt
      rw [htinf, if_neg hwB]
      simp
    · by_cases hvA : v ∈ A
      · rw [htfin, if_pos hvA]
        have hlt := ((hAmem v).1 hvA).2
        obtain ⟨hvg, hog⟩ := Modulus.gcd_aux' hv hlt.le
        exact (hx.1.2 v hvg).trans (WithZero.exp_le_exp.2 (by omega))
      · rw [htfin, if_neg hvA, sub_self, map_zero]
        exact zero_le'

section Gcd

variable (hR : IdelicReciprocity K) (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

include hR in
/-- `ArtinFactorsThrough` is closed under gcd. -/
theorem artinFactorsThrough_gcd {m₁ m₂ : Modulus K} (h₁ : ArtinFactorsThrough L m₁)
    (h₂ : ArtinFactorsThrough L m₂) : ArtinFactorsThrough L (Modulus.gcd m₁ m₂) := by
  have k₁ := idelesW_le_ker_of_artinFactorsThrough hR L m₁ h₁
  have k₂ := idelesW_le_ker_of_artinFactorsThrough hR L m₂ h₂
  refine artinFactorsThrough_of_idelesW hR L _ (fun v hv => ?_) fun x hx => ?_
  · by_cases hv1 : v ∈ m₁.finiteSupport
    · by_cases hv2 : v ∈ m₂.finiteSupport
      · exact absurd (Modulus.mem_gcd_finiteSupport hv1 hv2) hv
      · exact h₂.1 v hv2
    · exact h₁.1 v hv1
  · obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 (idelesW_gcd_le m₁ m₂ hx)
    exact mul_mem (k₁ hy) (k₂ hz)

end Gcd

/-! ## Ramified real places lie in the infinite part -/

section Real

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

theorem idelicArtinOf_idelicReciprocity :
    idelicArtinOf (idelicReciprocity K) L = idelicArtinTauCeti L :=
  idelicArtin_unique L _ _ (idelicArtinOf_spec (idelicReciprocity K) L).1 (isIdelicArtinMap_tauCeti L)
    (idelicArtinOf_spec (idelicReciprocity K) L).2.1 (idelicArtinTauCeti_principal L)

/-- At a real place ramified in $L$ the idèle $-1_w$ has nontrivial Artin symbol (complex conjugation). -/
theorem idelicArtinTauCeti_ofCompletion_neg_one_ne_one (w : InfinitePlace K)
    (hw : InfinitePlace.RamifiesIn L w) :
    idelicArtinTauCeti L (IdeleGroup.ofCompletion (𝓞 K) K w (-1)) ≠ 1 := by
  intro h
  obtain ⟨hvR, u, hu, huc⟩ := hw
  have : u.LiesOver w := by subst hu; infer_instance
  have hram : u.IsRamified K := InfinitePlace.isRamified_iff.mpr ⟨huc, hu ▸ hvR⟩
  rw [idelicArtinTauCeti_eq_one_iff,
    TauCeti.ClassFieldTheory.globalArtinMap_infiniteLocal, ofMul_eq_zero,
    TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_one_iff_mem_normGroup w u,
    InfinitePlace.Completion.mem_normGroup_iff_of_isRamified hram hvR] at h
  norm_num at h

/-- If $\psi_{L/K}$ factors through $C_\mathfrak m$, every real place ramified in $L$ lies in $\mathfrak m_\infty$. -/
theorem mem_infinite_of_artinFactorsThrough {m : Modulus K} (h : ArtinFactorsThrough L m) {w : InfinitePlace K}
    (hw : InfinitePlace.RamifiesIn L w) : w ∈ m.infinite := by
  by_contra hwm
  have hker := idelesW_le_ker_of_artinFactorsThrough (idelicReciprocity K) L m h
  have hx : IdeleGroup.ofCompletion (𝓞 K) K w (-1) ∈ idelesW m := by
    refine ⟨⟨fun w' hw' => ?_, fun v _ => ?_⟩, fun v _ => ?_⟩
    · have hne : w' ≠ w := fun e => hwm (e ▸ hw')
      unfold IsPosAt
      rw [ideleInfAt_ofCompletion_ne w w' hne]
      simp
    · rw [ideleFinAt_ofCompletion, sub_self, map_zero]
      exact zero_le
    · rw [ideleFinAt_ofCompletion]
      exact map_one _
  have := hker hx
  rw [MonoidHom.mem_ker, idelicArtinOf_idelicReciprocity] at this
  exact idelicArtinTauCeti_ofCompletion_neg_one_ne_one L w hw this

end Real

/-! ## The conductor -/

section Conductor

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- **Existence of the conductor** (Milne, *CFT*, V, Remark 3.8). -/
theorem exists_artinConductor : ∃ f : Modulus K, IsArtinConductor L f := by
  classical
  obtain ⟨m0, hm0⟩ := (reciprocityLaw_ideal_of_idelic K (idelicReciprocity K)).exists_definingModulus L
  have hP : ArtinFactorsThrough L m0 := hm0.artinFactorsThrough L
  obtain ⟨I, ⟨mI, hmI, hmIf⟩, hImax⟩ := (wellFounded_gt (α := Ideal (𝓞 K))).has_min
    {I | ∃ m : Modulus K, ArtinFactorsThrough L m ∧ m.finite = I} ⟨_, m0, hP, rfl⟩
  obtain ⟨s, ⟨f, hf, hfI, hfs⟩, hsmin⟩ := (wellFounded_lt (α := Set (InfinitePlace K))).has_min
    {s | ∃ m : Modulus K, ArtinFactorsThrough L m ∧ m.finite = I ∧ m.infinite = s}
    ⟨_, mI, hmI, hmIf, rfl⟩
  refine ⟨f, hf, fun m hm => ?_⟩
  have hg := artinFactorsThrough_gcd (idelicReciprocity K) L hf hm
  have hgI : (Modulus.gcd f m).finite = I := by
    by_contra hne
    have hle : I ≤ (Modulus.gcd f m).finite := hfI ▸ le_sup_left
    exact hImax _ ⟨_, hg, rfl⟩ (lt_of_le_of_ne hle (Ne.symm hne))
  have hgs : (Modulus.gcd f m).infinite = s := by
    by_contra hne
    have hle : (Modulus.gcd f m).infinite ≤ s := hfs ▸ Set.inter_subset_left
    exact hsmin _ ⟨_, hg, hgI, rfl⟩ (lt_of_le_of_ne hle hne)
  refine ⟨Ideal.dvd_iff_le.2 ?_, ?_⟩
  · have : m.finite ≤ (Modulus.gcd f m).finite := le_sup_right
    rw [hgI, ← hfI] at this
    exact this
  · intro w hw
    have h2 : w ∈ (Modulus.gcd f m).infinite := by rw [hgs, ← hfs]; exact hw
    exact h2.2

/-- **The support of the conductor** (Milne, *CFT*, V, Remark 3.8). -/
theorem artinConductor_support {f : Modulus K} (hf : IsArtinConductor L f) :
    f.finiteSupport = (unramifiedPrimes K L)ᶜ ∧
      ∀ w : InfinitePlace K, w ∈ f.infinite ↔ InfinitePlace.RamifiesIn L w := by
  obtain ⟨m0, hm0⟩ := (reciprocityLaw_ideal_of_idelic K (idelicReciprocity K)).exists_definingModulus L
  have hd : f.Dvd m0 := hf.2 m0 (hm0.artinFactorsThrough L)
  refine ⟨?_, fun w => ⟨fun hw => (hm0.infinite_iff w).1 (hd.2 hw), fun hw =>
    mem_infinite_of_artinFactorsThrough L hf.1 hw⟩⟩
  ext v
  constructor
  · intro hv
    rw [← hm0.finiteSupport_eq]
    exact (show v.asIdeal ∣ f.finite from hv).trans hd.1
  · intro hv
    by_contra hvf
    exact hv (hf.1.1 v hvf)

end Conductor

variable (K) in
/-- **Remark 3.8, unconditional** (Milne, *CFT*, V, Remark 3.8, p. 158): every finite abelian extension has a
conductor, and it is divisible exactly by the primes (finite and real) ramifying in the extension. -/
@[kb "milne2020cft" "Ch. V, Remark 3.8"]
theorem remark3_8 : Remark3_8 K where
  exists_conductor L _ _ _ _ := exists_artinConductor L
  support L _ _ _ _ f hf := artinConductor_support L hf

end NumberFieldKB.MilneCFT
