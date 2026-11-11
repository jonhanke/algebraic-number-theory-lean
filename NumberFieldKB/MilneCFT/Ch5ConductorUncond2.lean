import NumberFieldKB.MilneCFT.Ch5ConductorUncond
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 3.12 (the Takagi group), unconditional

`ch5Remark3_12`: for a finite abelian $L/K$ with conductor $\mathfrak f$ and a modulus $\mathfrak m$ with
$\mathfrak f\mid\mathfrak m$ and $S(\mathfrak m)$ the ramified primes, the Takagi group
$T(L/K,\mathfrak m)=i(K_{\mathfrak m,1})\,\mathrm{Nm}(I_L^{S(\mathfrak m)})$ is the kernel of the Artin map; hence it has
index $[L:K]$ and does not depend on $\mathfrak m$.

The inclusion $\ker\psi\subseteq T(L/K,\mathfrak m)$ is the idèlic argument of `ker_artinMap_le_of_idelic`, without the
hypothesis that $\mathfrak m_\infty$ consists of ramified places: at a real place of $\mathfrak m_\infty$ unramified in
$L$ the sign of the norm is controlled by choosing $\beta\in L^\times$ with prescribed signs at the real places above
it (`exists_mul_close_above_pos_of_dvd`, weak approximation) and writing positive reals as squares
(`exists_sq_idele'`, `isPosAt_ideleNormMap_of_forall'`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev NumberFieldKB.Ideles
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

section Sign

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

open scoped Classical in
theorem exists_sq_idele' (y : IdeleGroup (𝓞 L) L) (P : InfinitePlace L → Prop)
    (hP : ∀ u, P u → u.IsComplex ∨ ∃ hr : u.IsReal, IsPosAt u hr (ideleInfAt y u)) :
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

theorem isPosAt_ideleNormMap_of_forall' (y : IdeleGroup (𝓞 L) L) (w : InfinitePlace K) (hw : w.IsReal)
    (hc : ∀ u : InfinitePlace L, u.comap (algebraMap K L) = w →
      u.IsComplex ∨ ∃ hr : u.IsReal, IsPosAt u hr (ideleInfAt y u)) :
    IsPosAt w hw (ideleInfAt (ideleNormMap K L y) w) := by
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_sq_idele' L y (fun u => u.comap (algebraMap K L) = w) hc
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

/-- Weak approximation for the norm with prescribed signs: as `exists_mul_close_above`, and moreover `β y` is positive at
the real places of a finite set `R` of places of `L`. -/
theorem exists_mul_close_above_pos_of_dvd (y : IdeleGroup (𝓞 L) L) (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (N : ℕ) (R : Finset (InfinitePlace L)) : ∃ β : Lˣ,
      (∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) ∈ HeightOneSpectrum.asIdeal '' S →
        Valued.v (ideleFinAt (IdeleGroup.unitEmbedding (𝓞 L) L β * y) w) = 1) ∧
      (∀ v ∈ S, Valued.v (ideleFinAt (ideleNormMap K L (IdeleGroup.unitEmbedding (𝓞 L) L β * y)) v - 1) ≤
        WithZero.exp (-(N : ℤ))) ∧
      ∀ u ∈ R, ∀ hu : u.IsReal, IsPosAt u hu (ideleInfAt (IdeleGroup.unitEmbedding (𝓞 L) L β * y) u) := by
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
  -- the infinite targets: `±2` according to the sign of `y_u`
  set q : InfinitePlace L → L := fun u => if h : u.IsReal then
    (if 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal h (ideleInfAt y u) then 2 else -2) else 0 with hq
  obtain ⟨b, hb1, hb2⟩ := exists_approx T R c γ (fun w _ => hγ0 w) q
  have hsign : ∀ u ∈ R, ∀ hu : u.IsReal, 0 < InfinitePlace.embedding_of_isReal hu b *
      InfinitePlace.Completion.extensionEmbeddingOfIsReal hu (ideleInfAt y u) := by
    intro u hur hu
    have h1 := hb2 u hur
    have hne : InfinitePlace.Completion.extensionEmbeddingOfIsReal hu (ideleInfAt y u) ≠ 0 :=
      (map_ne_zero _).2 (ideleInfAt_ne_zero y u)
    rw [← InfinitePlace.norm_embedding_of_isReal hu, map_sub, Real.norm_eq_abs, abs_lt] at h1
    simp only [hq, dif_pos hu] at h1
    by_cases hp : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hu (ideleInfAt y u)
    · rw [if_pos hp] at h1
      simp only [map_ofNat] at h1
      exact mul_pos (by linarith [h1.1]) hp
    · rw [if_neg hp] at h1
      have hn : InfinitePlace.Completion.extensionEmbeddingOfIsReal hu (ideleInfAt y u) < 0 :=
        lt_of_le_of_ne (not_lt.1 hp) hne
      simp only [map_neg, map_ofNat] at h1
      exact mul_pos_of_neg_of_neg (by linarith [h1.2]) hn
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
  obtain ⟨b', hb'0, hb', hb'sign⟩ : ∃ b' : L, b' ≠ 0 ∧
      (∀ w ∈ T, Valued.v (algebraMap L (w.adicCompletion L) b' * ideleFinAt y w - 1) < ε' w) ∧
      ∀ u ∈ R, ∀ hu : u.IsReal, 0 < InfinitePlace.embedding_of_isReal hu b' *
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hu (ideleInfAt y u) := by
    by_cases hb0 : b = 0
    · refine ⟨1, one_ne_zero, fun w hw => ?_, fun u hur hu => ?_⟩
      · exfalso
        have := hbT w hw
        rw [hb0, map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one] at this
        exact lt_irrefl _ ((this.trans_le (hε'1 w)).trans hlt1)
      · exfalso
        have := hsign u hur hu
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
  · intro u hur hu
    have h := hb'sign u hur hu
    unfold IsPosAt
    rw [ideleInfAt_mul, map_mul, ideleInfAt_unitEmbedding]
    have : InfinitePlace.Completion.extensionEmbeddingOfIsReal hu (((β : Lˣ) : L) : u.Completion) =
        InfinitePlace.embedding_of_isReal hu b' := extEmbedding_coe hu _
    rw [this]
    exact h

end Sign

/-! ## The kernel of the Artin map for an arbitrary modulus -/

section Kernel

variable (hR : IdelicReciprocity K) (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- The kernel of $\psi_{L/K}$ on $I^{S(\mathfrak m)}$ is contained in $T(L/K,\mathfrak m)$, for every modulus
$\mathfrak m$ through which the idèlic Artin map is trivial on $W_\mathfrak m$ (no condition on $\mathfrak m_\infty$). -/
theorem ker_artinMap_le_takagi (m : Modulus K)
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
  let R : Finset (InfinitePlace L) := Finset.univ.filter
    (fun u => u.IsReal ∧ u.comap (algebraMap K L) ∈ m.infinite)
  obtain ⟨β, hβ1, hβ2, hβ3⟩ := exists_mul_close_above_pos_of_dvd L y m.finiteSupport hfin
    (hfin.toFinset.sup m.ord) R
  set z := IdeleGroup.unitEmbedding (𝓞 L) L β * y with hz
  set c' : Kˣ := c * (Units.map (Algebra.norm K : L →* K) β)⁻¹ with hc'
  have hNz : ideleNormMap K L z = IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (Algebra.norm K : L →* K) β) *
      ideleNormMap K L y := by
    rw [hz, map_mul, (ideleNormMap_comm (K := K) L).1]
  have hxz : x = IdeleGroup.unitEmbedding (𝓞 K) K c' * ideleNormMap K L z := by
    rw [hNz, hc', map_mul, map_inv, ← hpr]
    simp [mul_assoc]
  have hNzm : ideleNormMap K L z ∈ idelesMod m := by
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · by_cases hr : InfinitePlace.RamifiesIn L w
      · exact isPosAt_ideleNormMap L z w hr
      · refine isPosAt_ideleNormMap_of_forall' L z w (m.isReal_of_mem w hw) fun u hu => ?_
        rcases u.isReal_or_isComplex with hur | huc
        · refine Or.inr ⟨hur, hβ3 u ?_ hur⟩
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hur, hu ▸ hw⟩
        · exact absurd ⟨m.isReal_of_mem w hw, u, hu, huc⟩ hr
    · refine (hβ2 v hv).trans (WithZero.exp_le_exp.mpr ?_)
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

end Kernel

/-! ## Remark 3.12 -/

section Takagi

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

theorem takagiGroup_le_sIdeals (m : Modulus K) : takagiGroup L m ≤ sIdeals m.finiteSupport :=
  sup_le (by rw [← coprimeIdeals_eq_sIdeals]; exact rayPrincipal_le m) (normIdeals_le K L _)

/-- If the Artin map factors through $\mathfrak m$, its kernel on $I^{S(\mathfrak m)}$ is the Takagi group. -/
theorem artinMap_ker_eq_takagi {m : Modulus K} (h : ArtinFactorsThrough L m) :
    (artinMap L m.finiteSupport).ker = (takagiGroup L m).subgroupOf (sIdeals m.finiteSupport) := by
  obtain ⟨hm, hW⟩ := (artinFactorsThrough_iff (idelicReciprocity K) L m).1 h
  exact le_antisymm (ker_artinMap_le_takagi (idelicReciprocity K) L m hm hW)
    (le_ker_artinMap_of_idelic (idelicReciprocity K) L m hm hW)

/-- If the Artin map factors through $\mathfrak m$, the index of the Takagi group in $I^{S(\mathfrak m)}$ is $[L:K]$. -/
theorem takagi_index {m : Modulus K} (h : ArtinFactorsThrough L m) :
    ((takagiGroup L m).subgroupOf (sIdeals m.finiteSupport)).index = Module.finrank K L := by
  obtain ⟨hm, hW⟩ := (artinFactorsThrough_iff (idelicReciprocity K) L m).1 h
  rw [← artinMap_ker_eq_takagi L h, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (artinMap_surjective_of_idelic (idelicReciprocity K) L m hm hW),
    Subgroup.card_top]
  exact IsGalois.card_aut_eq_finrank K L

end Takagi

variable (K) in
/-- **Remark 3.12, unconditional** (Milne, *CFT*, V, Remark 3.12, p. 160, Takagi and Artin). -/
@[kb "milne2020cft" "Ch. V, Remark 3.12"]
theorem ch5Remark3_12 : Ch5Remark3_12 K where
  takagi L _ _ _ _ f m hf hd hs := by
    have hsf : f.finiteSupport = m.finiteSupport := by
      rw [hs]; exact (artinConductor_support L hf).1
    have hfm : ArtinFactorsThrough L m := ArtinFactorsThrough.of_dvd L hf.1 hd
    have kf := artinMap_ker_eq_takagi L hf.1
    have km := artinMap_ker_eq_takagi L hfm
    rw [hsf] at kf
    refine ⟨?_, takagi_index L hfm, km⟩
    have h : (takagiGroup L m).subgroupOf (sIdeals m.finiteSupport) =
        (takagiGroup L f).subgroupOf (sIdeals m.finiteSupport) := km.symm.trans kf
    rw [Subgroup.subgroupOf_inj, inf_of_le_left (takagiGroup_le_sIdeals L m)] at h
    rw [h]
    have := takagiGroup_le_sIdeals L f
    rw [hsf] at this
    exact inf_of_le_left this

end NumberFieldKB.MilneCFT
