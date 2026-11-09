import NumberFieldKB.MilneCFT.Ch7.HilbertIdelic

/-!
# The ideal-theoretic existence theorem from the idelic one (Milne, *CFT*, Chapter V, Remark 5.8, existence half)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Remark 5.8 (p. 180), Theorem 3.6 and the note after it (p. 158), Proposition 4.6 (p. 173).

For a congruence subgroup $H$ modulo $\mathfrak m$, let $\hat H = \{x\in I_\mathfrak m : \mathrm{id}(x)\in H\}$
(`idelesOfCongr`) and $N$ its image in $C_K$ (open of finite index: $\hat H\supseteq W_\mathfrak m$, and
$C_K/N\cong I^{S(\mathfrak m)}/H$ by Proposition 4.6). The class field $L$ of $N$ (Theorem 5.5) is unramified outside
$\mathfrak m$ (`ArtinInertia`), its Artin map on $I^{S(\mathfrak m)}$ is onto with kernel exactly $H$ (from
$\ker\phi_{L/K} = K^\times\hat H$), and $H = P_\mathfrak m\cdot\mathrm{Nm}(I_L^{S(\mathfrak m)})$
(`ker_artinMap_le_of_idelic'`: the kernel inclusion of Remark 5.8 without assuming that the real places of
$\mathfrak m$ ramify, approximating also the signs at the real places).
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

section Norms

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

open scoped Classical in
/-- `exists_sq_idele` allowing also real places at which `y` is positive. -/
theorem exists_sq_idele_pos (y : IdeleGroup (𝓞 L) L) (P : InfinitePlace L → Prop)
    (hP : ∀ u, P u → u.IsComplex ∨ ∃ hu : u.IsReal, IsPosAt u hu (ideleInfAt y u)) :
    ∃ t : IdeleGroup (𝓞 L) L, (∀ u, P u → ideleInfAt t u * ideleInfAt t u = ideleInfAt y u) ∧
      (∀ u, ¬ P u → ideleInfAt t u = 1) ∧ (∀ v, ideleFinAt t v = 1) := by
  have hex : ∀ u : InfinitePlace L, ∃ s : u.Completion, s ≠ 0 ∧ (P u → s * s = ideleInfAt y u) ∧
      (¬ P u → s = 1) := by
    intro u
    by_cases h : P u
    · rcases hP u h with hc | ⟨hr, hpos⟩
      · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
        obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (e (ideleInfAt y u))
        have hs : e.symm r * e.symm r = ideleInfAt y u := by
          rw [← map_mul, ← hr, RingEquiv.symm_apply_apply]
        refine ⟨e.symm r, ?_, fun _ => hs, fun h' => absurd h h'⟩
        intro h0
        rw [h0, mul_zero] at hs
        exact ideleInfAt_ne_zero y u hs.symm
      · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hr
        have hpos' : 0 < e (ideleInfAt y u) := hpos
        have hs : e.symm (Real.sqrt (e (ideleInfAt y u))) * e.symm (Real.sqrt (e (ideleInfAt y u))) =
            ideleInfAt y u := by
          rw [← map_mul, Real.mul_self_sqrt hpos'.le, RingEquiv.symm_apply_apply]
        refine ⟨_, ?_, fun _ => hs, fun h' => absurd h h'⟩
        intro h0
        rw [h0, mul_zero] at hs
        exact ideleInfAt_ne_zero y u hs.symm
    · exact ⟨1, one_ne_zero, fun h' => absurd h' h, fun _ => rfl⟩
  choose s hs0 hs1 hs2 using hex
  refine ⟨⟨((s : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)),
    (((fun u => (s u)⁻¹) : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)),
    Prod.ext (funext fun u => mul_inv_cancel₀ (hs0 u)) (mul_one _),
    Prod.ext (funext fun u => inv_mul_cancel₀ (hs0 u)) (mul_one _)⟩, ?_, ?_, ?_⟩
  · intro u hu; exact hs1 u hu
  · intro u hu; exact hs2 u hu
  · intro v; rfl

/-- The norm of an idele is positive at a real place $w$ of $K$ if the idele is positive at every real place of $L$
above $w$. -/
theorem isPosAt_ideleNormMap_of_pos (y : IdeleGroup (𝓞 L) L) (w : InfinitePlace K) (hw : w.IsReal)
    (hpos : ∀ (u : InfinitePlace L) (hu : u.IsReal), u.comap (algebraMap K L) = w → IsPosAt u hu (ideleInfAt y u)) :
    IsPosAt w hw (ideleInfAt (ideleNormMap K L y) w) := by
  classical
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_sq_idele_pos L y (fun u => u.comap (algebraMap K L) = w) (by
    intro u hu
    by_cases hr : u.IsReal
    · exact Or.inr ⟨hr, hpos u hr hu⟩
    · exact Or.inl (InfinitePlace.not_isReal_iff_isComplex.1 hr))
  obtain ⟨y₂, hy₂def⟩ : ∃ y₂ : IdeleGroup (𝓞 L) L, y₂ = y * (t * t)⁻¹ := ⟨_, rfl⟩
  have hy₂ : ∀ u : InfinitePlace L, u.comap (algebraMap K L) = w → ideleInfAt y₂ u = 1 := by
    intro u hu
    rw [hy₂def, ideleInfAt_mul, ideleInfAt_inv, ideleInfAt_mul, ht1 u hu]
    exact mul_inv_cancel₀ (ideleInfAt_ne_zero y u)
  have h1 := extEmb_ideleInfAt_ideleNormMap_eq_one L w hw y₂ hy₂
  have hy : y = y₂ * (t * t) := by rw [hy₂def]; group
  have hN : ideleNormMap K L y = ideleNormMap K L y₂ * (ideleNormMap K L t * ideleNormMap K L t) := by
    rw [← map_mul, ← map_mul, ← hy]
  unfold IsPosAt
  rw [hN, ideleInfAt_mul, ideleInfAt_mul, map_mul, map_mul, h1, one_mul]
  exact mul_self_pos.2 ((map_ne_zero _).2 (ideleInfAt_ne_zero _ w))

theorem extEmb_coe (L : Type) [Field L] [NumberField L] (u : InfinitePlace L) (hu : u.IsReal) (b : L) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hu (b : u.Completion) = u.embedding_of_isReal hu b :=
  InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hu ((WithAbs.equiv u.1).symm b)

theorem sign_mul_pos (L : Type) [Field L] [NumberField L] (u : InfinitePlace L) (hu : u.IsReal) (b : L)
    (Y : ℝ) (hY : Y ≠ 0) (hb : u (b - (if 0 < Y then 2 else -2)) < 1) :
    0 < u.embedding_of_isReal hu b * Y := by
  have habs : |u.embedding_of_isReal hu (b - (if 0 < Y then 2 else -2))| < 1 := by
    rw [← Real.norm_eq_abs, InfinitePlace.norm_embedding_of_isReal hu]; exact hb
  have h2 : u.embedding_of_isReal hu (2 : L) = 2 := map_ofNat _ 2
  split_ifs at habs with h
  · rw [map_sub, h2, abs_lt] at habs
    exact mul_pos (by linarith [habs.1]) h
  · rw [map_sub, map_neg, h2, abs_lt] at habs
    exact mul_pos_of_neg_of_neg (by linarith [habs.2]) (lt_of_le_of_ne (not_lt.1 h) hY)

/-- `exists_mul_close_above` with signs: moreover $\beta y$ is positive at every real place of $L$ above a given
finite set $R$ of real places of $K$. -/
theorem exists_mul_close_above_pos (y : IdeleGroup (𝓞 L) L) (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (N : ℕ) (R : Set (InfinitePlace K)) : ∃ β : Lˣ,
      (∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) ∈ HeightOneSpectrum.asIdeal '' S →
        Valued.v (ideleFinAt (IdeleGroup.unitEmbedding (𝓞 L) L β * y) w) = 1) ∧
      (∀ v ∈ S, Valued.v (ideleFinAt (ideleNormMap K L (IdeleGroup.unitEmbedding (𝓞 L) L β * y)) v - 1) ≤
        WithZero.exp (-(N : ℤ))) ∧
      ∀ (u : InfinitePlace L) (hu : u.IsReal), u.comap (algebraMap K L) ∈ R →
        IsPosAt u hu (ideleInfAt (IdeleGroup.unitEmbedding (𝓞 L) L β * y) u) := by
  classical
  set A : Set (IdeleGroup (𝓞 K) K) :=
    {x | ∀ v ∈ S, Valued.v (ideleFinAt x v - 1) ≤ WithZero.exp (-(N : ℤ))} with hA
  have hAopen : IsOpen A := by
    have : A = ⋂ v ∈ S, (fun x : IdeleGroup (𝓞 K) K => ideleFinAt x v) ⁻¹'
        {z : v.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-(N : ℤ))} := by
      ext x; simp [hA]
    rw [this]
    refine hS.isOpen_biInter fun v _ => (isOpen_valued_sub_one_le v _).preimage ?_
    exact (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)
  have hWopen : IsOpen ((ideleNormMap K L) ⁻¹' A) := hAopen.preimage (map_continuous (ideleNormMap K L))
  have hW1 : (1 : IdeleGroup (𝓞 L) L) ∈ (ideleNormMap K L) ⁻¹' A := by
    show ideleNormMap K L 1 ∈ A
    rw [map_one]
    intro v _
    rw [ideleFinAt_one, sub_self, map_zero]; exact zero_le
  obtain ⟨S₀, ε, hε, hbox⟩ := exists_box_idele (ideleNormMap K L ⁻¹' A) hWopen hW1
  set ε' : HeightOneSpectrum (𝓞 L) → WithZero (Multiplicative ℤ) :=
    fun w => min (ε w) (WithZero.exp (-1)) with hε'
  have hlt1 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hε'0 : ∀ w, ε' w ≠ 0 := fun w =>
    (lt_min (zero_lt_iff.2 (hε w)) (zero_lt_iff.2 WithZero.exp_ne_zero)).ne'
  have hε'1 : ∀ w, ε' w ≤ WithZero.exp (-1) := fun w => min_le_right _ _
  have hε'2 : ∀ w, ε' w ≤ ε w := fun w => min_le_left _ _
  have hTfin := finite_primesAbove_ker (K := K) (L := L) hS
  set T := hTfin.toFinset with hT
  have hTmem : ∀ w, w ∈ T ↔ primeBelow K L w ∈ S := fun w => by
    rw [hT, Set.Finite.mem_toFinset]; rfl
  have hy0 : ∀ w, Valued.v (ideleFinAt y w) ≠ 0 := fun w => by
    rw [Ne, map_eq_zero]; exact ideleFinAt_ne_zero y w
  set γ : HeightOneSpectrum (𝓞 L) → WithZero (Multiplicative ℤ) :=
    fun w => ε' w * (Valued.v (ideleFinAt y w))⁻¹ with hγ
  have hγ0 : ∀ w, γ w ≠ 0 := fun w => mul_ne_zero (hε'0 w) (inv_ne_zero (hy0 w))
  choose c hc using fun w => exists_close w ((ideleFinAt y w)⁻¹) (γ w) (hγ0 w)
  let q : InfinitePlace L → L := fun u =>
    if h : u.IsReal then
      (if 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal h (ideleInfAt y u) then 2 else -2)
    else 2
  obtain ⟨b, hb1, hb2⟩ := exists_approx T Finset.univ c γ (fun w _ => hγ0 w) q
  have hsign : ∀ (u : InfinitePlace L) (hu : u.IsReal),
      0 < u.embedding_of_isReal hu b *
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hu (ideleInfAt y u) := by
    intro u hu
    have h := hb2 u (Finset.mem_univ u)
    simp only [q, dif_pos hu] at h
    exact sign_mul_pos L u hu b _ ((map_ne_zero _).2 (ideleInfAt_ne_zero y u)) h
  have hbT : ∀ w ∈ T, Valued.v (algebraMap L (w.adicCompletion L) b * ideleFinAt y w - 1) < ε' w := by
    intro w hw
    have h1 : Valued.v (algebraMap L (w.adicCompletion L) (b - c w)) < γ w := by
      have e : Valued.v (algebraMap L (w.adicCompletion L) (b - c w)) = w.valuation L (b - c w) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ _
      rw [e]; exact hb1 w hw
    have hα := ideleFinAt_ne_zero y w
    have hinv : (ideleFinAt y w)⁻¹ * ideleFinAt y w = 1 := inv_mul_cancel₀ hα
    have e : algebraMap L (w.adicCompletion L) b * ideleFinAt y w - 1 =
        (algebraMap L (w.adicCompletion L) (b - c w) +
          (algebraMap L (w.adicCompletion L) (c w) - (ideleFinAt y w)⁻¹)) * ideleFinAt y w := by
      rw [map_sub]; linear_combination hinv
    rw [e, map_mul]
    have h2 := Valuation.map_add_lt _ h1 (hc w)
    calc _ < γ w * Valued.v (ideleFinAt y w) := mul_lt_mul_of_pos_right h2 (zero_lt_iff.2 (hy0 w))
      _ = ε' w := inv_mul_cancel_right₀ (hy0 w) (ε' w)
  obtain ⟨b', hb'0, hb', hsg⟩ : ∃ b' : L, b' ≠ 0 ∧
      (∀ w ∈ T, Valued.v (algebraMap L (w.adicCompletion L) b' * ideleFinAt y w - 1) < ε' w) ∧
      ∀ (u : InfinitePlace L) (hu : u.IsReal),
        0 < u.embedding_of_isReal hu b' *
          InfinitePlace.Completion.extensionEmbeddingOfIsReal hu (ideleInfAt y u) := by
    by_cases hb0 : b = 0
    · refine ⟨1, one_ne_zero, fun w hw => ?_, fun u hu => ?_⟩
      · exfalso
        have := hbT w hw
        rw [hb0, map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one] at this
        exact lt_irrefl _ ((this.trans_le (hε'1 w)).trans hlt1)
      · exfalso
        have := hsign u hu
        rw [hb0, map_zero, zero_mul] at this
        exact lt_irrefl _ this
    · exact ⟨b, hb0, hbT, hsign⟩
  set β : Lˣ := Units.mk0 b' hb'0 with hβ
  set z := IdeleGroup.unitEmbedding (𝓞 L) L β * y with hz
  have hzfin : ∀ w, ideleFinAt z w = algebraMap L (w.adicCompletion L) b' * ideleFinAt y w := fun w => by
    rw [hz, ideleFinAt_mul, ideleFinAt_unitEmbedding]; rfl
  have hzT : ∀ w ∈ T, Valued.v (ideleFinAt z w - 1) < ε' w := fun w hw => by
    rw [hzfin]; exact hb' w hw
  have hz1 : ∀ w ∈ T, Valued.v (ideleFinAt z w) = 1 := fun w hw =>
    val_eq_one_of_sub_one_le Valued.v hlt1 ((hzT w hw).le.trans (hε'1 w))
  refine ⟨β, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hw
    have hvb : v = primeBelow K L w := HeightOneSpectrum.ext hvw
    exact hz1 w ((hTmem w).2 (hvb ▸ hv))
  · intro v hv
    set u : (w : HeightOneSpectrum (𝓞 L)) → (w.adicCompletion L)ˣ :=
      fun w => Units.mk0 (ideleFinAt z w) (ideleFinAt_ne_zero z w) with hu
    set z₁ := prodOfAdic T u with hz₁
    have hz1fin : ∀ w, ideleFinAt z₁ w = if w ∈ T then ideleFinAt z w else 1 :=
      fun w => ideleFinAt_prodOfAdic T u w
    have hz2 : ∀ w, primeBelow K L w = v → ideleFinAt (z * z₁⁻¹) w = 1 := by
      intro w hw
      have hwT : w ∈ T := (hTmem w).2 (hw ▸ hv)
      rw [ideleFinAt_mul, ideleFinAt_inv, hz1fin, if_pos hwT]
      exact mul_inv_cancel₀ (ideleFinAt_ne_zero z w)
    have hz1W : z₁ ∈ ideleNormMap K L ⁻¹' A := by
      refine hbox z₁ (ideleInfAt_prodOfAdic T u) ?_ ?_ ?_ ?_
      · intro w; rw [hz1fin]
        split_ifs with h
        · exact (hz1 w h).le
        · simp
      · intro w; rw [ideleFinAt_inv, hz1fin]
        split_ifs with h
        · rw [map_inv₀, hz1 w h, inv_one]
        · simp
      · intro w _; rw [hz1fin]
        split_ifs with h
        · exact (hzT w h).trans_le (hε'2 w)
        · rw [sub_self, map_zero]; exact zero_lt_iff.2 (hε w)
      · intro w _; rw [ideleFinAt_inv, hz1fin]
        split_ifs with h
        · have := val_inv_sub_one_le Valued.v (γ := Valued.v (ideleFinAt z w - 1))
            (((hzT w h).trans_le (hε'1 w)).trans hlt1) le_rfl
          exact this.trans_lt ((hzT w h).trans_le (hε'2 w))
        · rw [inv_one, sub_self, map_zero]; exact zero_lt_iff.2 (hε w)
    have hN : ideleNormMap K L z = ideleNormMap K L (z * z₁⁻¹) * ideleNormMap K L z₁ := by
      rw [← map_mul]; congr 1; group
    have hn := ideleFinAt_ideleNormMap_eq_one (K := K) L v (z * z₁⁻¹) hz2
    rw [hN, ideleFinAt_mul, hn, one_mul]
    exact (hz1W : ideleNormMap K L z₁ ∈ A) v hv
  · intro u hu _
    have h := hsg u hu
    unfold IsPosAt
    rw [ideleInfAt_mul, ideleInfAt_unitEmbedding, map_mul, extEmb_coe L u hu]
    exact h

variable (hR : IdelicReciprocity K) [IsAbelianGalois K L]

/-- The kernel inclusion of Remark 5.8 for any modulus $\mathfrak m$ with $W_\mathfrak m\subseteq\ker\phi_{L/K}$
(no condition on the real places of $\mathfrak m$). -/
theorem ker_artinMap_le_of_idelic' (m : Modulus K)
    (hm : ∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L) (hW : idelesW m ≤ (idelicArtinOf hR L).ker) :
    (artinMap L m.finiteSupport).ker ≤
      (rayPrincipal m ⊔ normIdeals K L m.finiteSupport).subgroupOf (sIdeals m.finiteSupport) := by
  classical
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hg' : artinTot L (g : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1 := hg
  rw [Subgroup.mem_subgroupOf]
  have hfin : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  obtain ⟨x, hx, hxg⟩ := exists_mem_idelesMod_ideleToIdeal m (g : (FractionalIdeal (𝓞 K)⁰ K)ˣ) g.2
  have hφ : idelicArtinOf hR L x = 1 := by
    rw [idelicArtinOf_eq_artinTot hR L m hm hW x hx, hxg]; exact hg'
  have hxN : x ∈ ideleNormGroup L := by
    rw [← (idelicArtinOf_spec hR L).2.2.2]; exact MonoidHom.mem_ker.mpr hφ
  obtain ⟨p, ⟨c, rfl⟩, r, ⟨y, rfl⟩, hpr⟩ := Subgroup.mem_sup.mp hxN
  obtain ⟨β, hβ1, hβ2, hβ3⟩ := exists_mul_close_above_pos L y m.finiteSupport hfin
    (hfin.toFinset.sup m.ord) m.infinite
  set z := IdeleGroup.unitEmbedding (𝓞 L) L β * y with hz
  set c' : Kˣ := c * (Units.map (Algebra.norm K : L →* K) β)⁻¹ with hc'
  have hNz : ideleNormMap K L z = IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (Algebra.norm K : L →* K) β) *
      ideleNormMap K L y := by
    rw [hz, map_mul, (ideleNormMap_comm (K := K) L).1]
  have hxz : x = IdeleGroup.unitEmbedding (𝓞 K) K c' * ideleNormMap K L z := by
    rw [hNz, hc', map_mul, map_inv, ← hpr]
    simp [mul_assoc]
  have hNzm : ideleNormMap K L z ∈ idelesMod m := by
    refine ⟨fun w hw => isPosAt_ideleNormMap_of_pos L z w (m.isReal_of_mem w hw)
      fun u hu hc => hβ3 u hu (hc ▸ hw), fun v hv => ?_⟩
    refine (hβ2 v hv).trans (WithZero.exp_le_exp.mpr ?_)
    have : m.ord v ≤ hfin.toFinset.sup m.ord := Finset.le_sup (f := m.ord) (hfin.mem_toFinset.mpr hv)
    omega
  have hc'm : c' ∈ congruenceSubgroup m := by
    rw [mem_congruenceSubgroup_iff_mem_idelesMod]
    have : IdeleGroup.unitEmbedding (𝓞 K) K c' = x * (ideleNormMap K L z)⁻¹ := by
      rw [hxz]; group
    rw [this]
    exact mul_mem hx (inv_mem hNzm)
  have hzs : ideleToIdeal L z ∈ sIdeals (primesAbove K L m.finiteSupport) := by
    intro w hw
    rw [count_ideleToIdeal, hβ1 w ⟨primeBelow K L w, hw, rfl⟩, WithZero.log_one]
    simp
  have hmem : (g : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ rayPrincipal m ⊔ normIdeals K L m.finiteSupport := by
    refine Subgroup.mem_sup.mpr ⟨toPrincipalIdeal (𝓞 K) K c', ⟨c', hc'm, rfl⟩,
      idealNorm K L (ideleToIdeal L z), ⟨_, hzs, rfl⟩, ?_⟩
    rw [← (ideleNormMap_comm (K := K) L).2, ← ideleToIdeal_unitEmbedding, ← map_mul, ← hxz, hxg]
  exact hmem

end Norms

/-- $\hat H = \{x\in I_\mathfrak m : \mathrm{id}(x)\in H\}$. -/
def idelesOfCongr (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Subgroup (IdeleGroup (𝓞 K) K) :=
  idelesMod m ⊓ H.comap (ideleToIdeal K)

section Existence

variable (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem ideleToIdeal_eq_one_of_mem_idelesW {x : IdeleGroup (𝓞 K) K} (hx : x ∈ idelesW m) :
    ideleToIdeal K x = 1 := by
  refine ((item_4_1 (K := K)).2 x).2 fun v => ?_
  by_cases hv : v ∈ m.finiteSupport
  · exact val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one m v hv) (hx.1.2 v hv)
  · exact hx.2 v hv

theorem idelesW_le_idelesOfCongr : idelesW m ≤ idelesOfCongr m H := fun x hx =>
  ⟨hx.1, by
    show ideleToIdeal K x ∈ H
    rw [ideleToIdeal_eq_one_of_mem_idelesW m hx]; exact one_mem _⟩

variable {m H}

theorem unitEmbedding_mem_idelesOfCongr (hP : rayPrincipal m ≤ H) {c : Kˣ} (hc : c ∈ congruenceSubgroup m) :
    IdeleGroup.unitEmbedding (𝓞 K) K c ∈ idelesOfCongr m H :=
  ⟨(mem_congruenceSubgroup_iff_mem_idelesMod m c).1 hc, by
    show ideleToIdeal K _ ∈ H
    rw [ideleToIdeal_unitEmbedding]; exact hP ⟨c, hc, rfl⟩⟩

theorem finiteIndex_idelesOfCongr_sup (hP : rayPrincipal m ≤ H) :
    (idelesOfCongr m H ⊔ IdeleGroup.principalSubgroup (𝓞 K) K).FiniteIndex := by
  have hfinR : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  have hker : (idelesModToRay m).ker ≤ (idelesOfCongr m H).subgroupOf (idelesMod m) := by
    intro x hx
    have := ((prop_4_6a m).2 x).1 (MonoidHom.mem_ker.1 hx)
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨y, ⟨b, hb, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 this
    rw [← hyz]
    exact mul_mem (unitEmbedding_mem_idelesOfCongr hP hb) (idelesW_le_idelesOfCongr m H hz)
  have : (idelesModToRay m).ker.FiniteIndex := by
    refine ⟨?_⟩
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  have : ((idelesOfCongr m H).subgroupOf (idelesMod m)).FiniteIndex := Subgroup.finiteIndex_of_le hker
  have : Finite (idelesMod m ⧸ (idelesOfCongr m H).subgroupOf (idelesMod m)) :=
    Subgroup.finite_quotient_of_finiteIndex
  let f : idelesMod m ⧸ (idelesOfCongr m H).subgroupOf (idelesMod m) →*
      IdeleGroup (𝓞 K) K ⧸ (idelesOfCongr m H ⊔ IdeleGroup.principalSubgroup (𝓞 K) K) :=
    QuotientGroup.lift _ ((QuotientGroup.mk' _).comp (idelesMod m).subtype) (by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left hx))
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx⟩ := (prop_4_6b m).1 (a : IdeleClassGroup (𝓞 K) K)
    refine ⟨QuotientGroup.mk x, ?_⟩
    have h1 : (x : IdeleGroup (𝓞 K) K)⁻¹ * a ∈ IdeleGroup.principalSubgroup (𝓞 K) K :=
      QuotientGroup.eq.mp hx
    show (QuotientGroup.mk (x : IdeleGroup (𝓞 K) K) : IdeleGroup (𝓞 K) K ⧸ _) = QuotientGroup.mk a
    rw [QuotientGroup.eq]
    exact Subgroup.mem_sup_right h1
  have := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

theorem ofAdic_mem_idelesOfCongr {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ m.finiteSupport)
    (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1) :
    IdeleGroup.ofAdicCompletion (𝓞 K) K v u ∈ idelesOfCongr m H := by
  refine ⟨⟨fun w hw => ?_, fun v' hv' => ?_⟩, ?_⟩
  · unfold IsPosAt; rw [ideleInfAt_ofAdic]; simp
  · have hne : v' ≠ v := fun h => hv (h ▸ hv')
    rw [ideleFinAt_ofAdic_ne hne]; simp
  · show ideleToIdeal K _ ∈ H
    rw [((item_4_1 (K := K)).2 _).2 ((mem_idelesS_empty_iff _).1 (ofAdic_mem_idelesS_empty v u hu))]
    exact one_mem _

theorem ofCompletion_mem_idelesOfCongr {w : InfinitePlace K} (hw : w ∉ m.infinite) (t : w.Completionˣ) :
    IdeleGroup.ofCompletion (𝓞 K) K w t ∈ idelesOfCongr m H := by
  refine ⟨⟨fun w' hw' => ?_, fun v' hv' => ?_⟩, ?_⟩
  · have hne : w' ≠ w := fun h => hw (h ▸ hw')
    unfold IsPosAt; rw [ideleInfAt_ofCompletion_ne w w' hne]; simp
  · rw [ideleFinAt_ofCompletion]; simp
  · show ideleToIdeal K _ ∈ H
    rw [((item_4_1 (K := K)).2 _).2 ((mem_idelesS_empty_iff _).1 (ofCompletion_mem_idelesS_empty w t))]
    exact one_mem _

end Existence

variable (K) in
/-- **Theorem 3.6 with the Artin isomorphism (ideal-theoretic existence theorem) from Theorems 5.3 and 5.5** (Milne,
*CFT*, Chapter V, Remark 5.8, the existence half), conditional on `ArtinInertia`. -/
@[kb "milne2020cft" "Ch. V, Remark 5.8 (Thms. 5.3, 5.5 ⇒ Thm. 3.6)"]
theorem existenceTheoremArtin_of_idelic (hR : IdelicReciprocity K) (hE : IdelicExistence K) (hI : ArtinInertia K) :
    ExistenceTheoremArtin K := by
  classical
  refine ⟨fun m H ⟨hP, hH⟩ => ?_⟩
  set Hh := idelesOfCongr m H with hHh
  set P := IdeleGroup.principalSubgroup (𝓞 K) K with hPdef
  have hopen : IsOpen (Hh : Set (IdeleGroup (𝓞 K) K)) :=
    Subgroup.isOpen_mono (idelesW_le_idelesOfCongr m H) (isOpen_idelesW m)
  set N := Hh.map (QuotientGroup.mk' P) with hN
  have hNopen : IsOpen (N : Set (IdeleClassGroup (𝓞 K) K)) :=
    (QuotientGroup.isOpenMap_coe (N := P)) _ hopen
  have hcomap : N.comap (QuotientGroup.mk' P) = Hh ⊔ P := by
    rw [hN, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hNfin : N.FiniteIndex := by
    have h3 : N.index = (Hh ⊔ P).index := by
      rw [← hcomap, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have := finiteIndex_idelesOfCongr_sup (m := m) hP
    refine ⟨?_⟩
    rw [h3]
    exact this.index_ne_zero
  obtain ⟨L, _, _, _, _, hNL⟩ := hE.exists_field N hNopen hNfin
  have hspec := idelicArtinOf_spec hR L
  have hker : (idelicArtinOf hR L).ker = Hh ⊔ P := by
    rw [hspec.2.2.2, ← comap_normGroupC L, hNL, hcomap]
  have hHker : Hh ≤ (idelicArtinOf hR L).ker := hker ▸ le_sup_left
  have hWker : idelesW m ≤ (idelicArtinOf hR L).ker := (idelesW_le_idelesOfCongr m H).trans hHker
  have hunr : ∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L := fun v hv =>
    hI.finite L _ hspec.1 hspec.2.1 v fun u hu => hHker (ofAdic_mem_idelesOfCongr hv u hu)
  have hunrR : ∀ w : InfinitePlace K, w ∉ m.infinite → ¬ InfinitePlace.RamifiesIn L w := by
    intro w hw
    by_cases hr : w.IsReal
    · exact hI.real L _ hspec.1 hspec.2.1 w hr fun t => hHker (ofCompletion_mem_idelesOfCongr hw t)
    · exact fun h => hr h.1
  have hsurj := artinMap_surjective_of_idelic hR L m hunr hWker
  have hkereq : (artinMap L m.finiteSupport).ker = H.subgroupOf (sIdeals m.finiteSupport) := by
    ext g
    constructor
    · intro hg
      rw [MonoidHom.mem_ker] at hg
      have hg' : artinTot L (g : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1 := hg
      obtain ⟨x, hx, hxg⟩ := exists_mem_idelesMod_ideleToIdeal m (g : (FractionalIdeal (𝓞 K)⁰ K)ˣ) g.2
      have hφ : idelicArtinOf hR L x = 1 := by
        rw [idelicArtinOf_eq_artinTot hR L m hunr hWker x hx, hxg]; exact hg'
      have hxk : x ∈ Hh ⊔ P := hker ▸ MonoidHom.mem_ker.2 hφ
      obtain ⟨h, hh, c', ⟨c, rfl⟩, hxe⟩ := Subgroup.mem_sup.1 hxk
      have hcm : c ∈ congruenceSubgroup m := by
        rw [mem_congruenceSubgroup_iff_mem_idelesMod]
        have : IdeleGroup.unitEmbedding (𝓞 K) K c = h⁻¹ * x := by rw [← hxe]; group
        rw [this]
        exact mul_mem (inv_mem hh.1) hx
      rw [Subgroup.mem_subgroupOf, ← hxg, ← hxe, map_mul, ideleToIdeal_unitEmbedding]
      exact mul_mem hh.2 (hP ⟨c, hcm, rfl⟩)
    · intro hg
      rw [Subgroup.mem_subgroupOf] at hg
      obtain ⟨x, hx, hxg⟩ := exists_mem_idelesMod_ideleToIdeal m (g : (FractionalIdeal (𝓞 K)⁰ K)ˣ) g.2
      have hxH : x ∈ Hh := ⟨hx, by show ideleToIdeal K x ∈ H; rw [hxg]; exact hg⟩
      have hφ : idelicArtinOf hR L x = 1 := MonoidHom.mem_ker.1 (hHker hxH)
      rw [idelicArtinOf_eq_artinTot hR L m hunr hWker x hx, hxg] at hφ
      exact MonoidHom.mem_ker.2 hφ
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨⟨fun v hv => hunr v hv, hunrR⟩, hsurj, hkereq⟩, ?_⟩
  apply le_antisymm
  · intro h hh
    have : (⟨h, hH hh⟩ : sIdeals m.finiteSupport) ∈ (artinMap L m.finiteSupport).ker := by
      rw [hkereq]; exact hh
    exact ker_artinMap_le_of_idelic' L hR m hunr hWker this
  · refine sup_le hP fun n hn => ?_
    have h2 : artinTot L n = 1 := cor_3_4 L m.finiteSupport hunr ⟨n, normIdeals_le K L _ hn⟩ hn
    have : (⟨n, normIdeals_le K L _ hn⟩ : sIdeals m.finiteSupport) ∈ (artinMap L m.finiteSupport).ker :=
      MonoidHom.mem_ker.2 h2
    rw [hkereq] at this
    exact this

variable (K) in
/-- **Remark 5.8** (Milne, *CFT*, Chapter V, p. 180) as a theorem, conditional on `ArtinInertia`: the idelic
reciprocity law and existence theorem imply the ideal-theoretic ones. -/
@[kb "milne2020cft" "Ch. V, Remark 5.8 (from ArtinInertia)"]
theorem remark5_8_of_artinInertia (hI : ArtinInertia K) : Remark5_8 K :=
  ⟨reciprocityLaw_ideal_of_idelic K, fun hR hE => existenceTheoremArtin_of_idelic K hR hE hI⟩

end NumberFieldKB.MilneCFT
