import NumberFieldKB.MilneCFT.Ch5IdelicMain
import NumberFieldKB.MilneCFT.Ch5MainIdeal

/-!
# From the idelic reciprocity law to the ideal-theoretic one (Milne, *CFT*, Chapter V, Remark 5.8, first steps)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Remark 5.8 (p. 180), Proposition 4.6 (p. 173), Theorem 3.5 (p. 158).

For a finite abelian extension $L/K$ and the idelic Artin map $\phi_{L/K}$ of Theorem 5.3:

* `exists_modulus_idelesW_le_ker`: there is a modulus $\mathfrak m$ supported exactly on the ramified primes and the
  ramified real places with $W_\mathfrak m\subseteq\ker\phi_{L/K}$ (property (a) of Summary 5.10).
* `idelicArtinOf_eq_artinTot`: for such $\mathfrak m$ and $x\in I_\mathfrak m$, $\phi_{L/K}(x) =
  \psi_{L/K}(\mathrm{id}(x))$ (property (b): Frobenius on uniformizers).
* `artinMap_surjective_of_idelic`: the ideal-theoretic Artin map $I^{S(\mathfrak m)}\to\mathrm{Gal}(L/K)$ is onto
  (Proposition 4.6 (b)).
* `le_ker_artinMap_of_idelic`: its kernel contains $P_\mathfrak m\cdot\mathrm{Nm}(I_L^{S(\mathfrak m)})$
  (Corollary 3.4 for the norms).
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev
open scoped nonZeroDivisors IsMulCommutative

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

variable (hR : IdelicReciprocity K) (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- The ideal of an idèle has order `-log (v a_v)` at `v`. -/
theorem count_ideleToIdeal (x : IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (ideleToIdeal K x : FractionalIdeal (𝓞 K)⁰ K) =
      -WithZero.log (Valued.v (ideleFinAt x v)) :=
  QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K →+*
      FiniteAdeleRing (𝓞 K) K).toMonoidHom x) v

theorem artinTot_ideleToIdeal_ofAdic (v : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1)) (k : ℤ) :
    artinTot L (ideleToIdeal K (IdeleGroup.ofAdicCompletion (𝓞 K) K v (π ^ k))) = artinFrob L v ^ k := by
  change ∏ᶠ w : HeightOneSpectrum (𝓞 K), artinFrob L w ^
    FractionalIdeal.count K w (ideleToIdeal K (IdeleGroup.ofAdicCompletion (𝓞 K) K v (π ^ k)) :
      FractionalIdeal (𝓞 K)⁰ K) = _
  rw [finprod_eq_single _ v]
  · rw [count_ideleToIdeal, ideleFinAt_ofAdic_self, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ,
      ← WithZero.exp_zsmul, WithZero.log_exp]
    simp
  · intro w hw
    rw [count_ideleToIdeal, ideleFinAt_ofAdic_ne hw, map_one, WithZero.log_one]
    simp

/-- There is a modulus supported exactly on the ramified primes and real places with $W_\mathfrak m\subseteq
\ker\phi_{L/K}$. -/
theorem exists_modulus_idelesW_le_ker : ∃ m : Modulus K, m.finiteSupport = (unramifiedPrimes K L)ᶜ ∧
    (∀ w : InfinitePlace K, w ∈ m.infinite ↔ InfinitePlace.RamifiesIn L w) ∧
    idelesW m ≤ (idelicArtinOf hR L).ker := by
  classical
  obtain ⟨n, hn⟩ := (idelicArtinOf_spec hR L).1.local_ramified
  have hS := finite_compl_unramifiedPrimes K L
  let I : Ideal (𝓞 K) := ∏ v ∈ hS.toFinset, v.asIdeal ^ (n + 1)
  have hI : I ≠ ⊥ := by
    refine Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  let m : Modulus K := ⟨I, hI, {w | InfinitePlace.RamifiesIn L w}, fun w hw => hw.1⟩
  have hdvd : ∀ v ∈ (unramifiedPrimes K L)ᶜ, v.asIdeal ^ (n + 1) ∣ I := fun v hv =>
    Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal ^ (n + 1)) (hS.mem_toFinset.mpr hv)
  have hord : ∀ v ∈ (unramifiedPrimes K L)ᶜ, v ∈ m.finiteSupport ∧ n ≤ m.ord v := by
    intro v hv
    refine ⟨(dvd_pow_self v.asIdeal (Nat.succ_ne_zero n)).trans (hdvd v hv), ?_⟩
    have h1 : Associates.mk v.asIdeal ^ (n + 1) ≤ Associates.mk I := by
      rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
      exact hdvd v hv
    have hI' : Associates.mk (I : Ideal (𝓞 K)) ≠ 0 := Associates.mk_ne_zero.mpr hI
    have := (Associates.prime_pow_dvd_iff_le hI' v.associates_irreducible).mp h1
    show n ≤ (Associates.mk v.asIdeal).count (Associates.mk I).factors
    omega
  have hsupp : m.finiteSupport = (unramifiedPrimes K L)ᶜ := by
    refine Set.Subset.antisymm ?_ (fun v hv => (hord v hv).1)
    intro v hv
    have hp : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    obtain ⟨i, hi, hvi⟩ := (Prime.dvd_finsetProd_iff hp _).mp hv
    have hvi' : v.asIdeal ∣ i.asIdeal := hp.dvd_of_dvd_pow hvi
    have hle : i.asIdeal ≤ v.asIdeal := Ideal.le_of_dvd hvi'
    have : i.asIdeal = v.asIdeal := i.isMaximal.eq_of_le v.isPrime.ne_top hle
    have hiv : i = v := HeightOneSpectrum.ext this
    rw [← hiv]
    exact hS.mem_toFinset.mp hi
  refine ⟨m, hsupp, fun w => Iff.rfl, ?_⟩
  rintro x ⟨⟨hinf, hfin⟩, hunit⟩
  rw [MonoidHom.mem_ker]
  refine hn x (fun v hv => hunit v (by rw [hsupp]; exact fun h => h hv)) (fun v hv => ?_)
    (fun w hw hr => hinf w hr)
  have hvm : v ∈ m.finiteSupport := by rw [hsupp]; exact hv
  refine (hfin v hvm).trans (WithZero.exp_le_exp.mpr ?_)
  have := (hord v hv).2
  omega

/-- On $I_\mathfrak m$ the idelic Artin map is the ideal-theoretic one composed with $\mathrm{id}$. -/
theorem idelicArtinOf_eq_artinTot (m : Modulus K)
    (hm : ∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L) (hW : idelesW m ≤ (idelicArtinOf hR L).ker)
    (x : IdeleGroup (𝓞 K) K) (hx : x ∈ idelesMod m) :
    idelicArtinOf hR L x = artinTot L (ideleToIdeal K x) := by
  classical
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ y : IdeleGroup (𝓞 K) K, y ∈ idelesMod m →
      (∀ v ∉ m.finiteSupport, v ∉ T → Valued.v (ideleFinAt y v) = 1) →
      idelicArtinOf hR L y = artinTot L (ideleToIdeal K y) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro y hy h3
      have hyW : y ∈ idelesW m := ⟨hy, fun v hv => h3 v hv (Finset.notMem_empty v)⟩
      have h1 : idelicArtinOf hR L y = 1 := MonoidHom.mem_ker.mp (hW hyW)
      have h2 : ideleToIdeal K y = 1 := by
        refine ((item_4_1 (K := K)).2 y).mpr fun v => ?_
        by_cases hv : v ∈ m.finiteSupport
        · exact val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one m v hv) (hy.2 v hv)
        · exact hyW.2 v hv
      rw [h1, h2, map_one]
    | insert v T hvT ih =>
      intro y hy h3
      by_cases hv : v ∉ m.finiteSupport ∧ Valued.v (ideleFinAt y v) ≠ 1
      · obtain ⟨hvS, hv1⟩ := hv
        obtain ⟨π, hπv⟩ := exists_unit_uniformizer v
        have hne : Valued.v (ideleFinAt y v) ≠ 0 := (Valuation.ne_zero_iff _).mpr (ideleFinAt_ne_zero y v)
        set k : ℤ := WithZero.log (Valued.v (ideleFinAt y v)) with hk
        have hkv : Valued.v (ideleFinAt y v) = WithZero.exp k := (WithZero.exp_log hne).symm
        set z := IdeleGroup.ofAdicCompletion (𝓞 K) K v (π ^ k) with hz
        have hzv : ideleFinAt z v = ((π ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) :=
          ideleFinAt_ofAdic_self v _
        have hval : Valued.v (ideleFinAt (y * z) v) = 1 := by
          have : ideleFinAt (y * z) v = ideleFinAt y v * ideleFinAt z v := rfl
          rw [this, map_mul, hzv, Units.val_zpow_eq_zpow_val, map_zpow₀, hπv, hkv, ← WithZero.exp_zsmul,
            ← WithZero.exp_add]
          simp
        have hzm : z ∈ idelesMod m := by
          refine ⟨fun w hw => ?_, fun v' hv' => ?_⟩
          · unfold IsPosAt; rw [hz, ideleInfAt_ofAdic]; simp
          · have hne : v' ≠ v := fun h => hvS (h ▸ hv')
            rw [hz, ideleFinAt_ofAdic_ne hne]; simp
        have hyz := ih (y * z) (mul_mem hy hzm) (by
          intro v' hv'S hv'T
          by_cases hvv : v' = v
          · subst hvv; exact hval
          · have : ideleFinAt (y * z) v' = ideleFinAt y v' * ideleFinAt z v' := rfl
            rw [this, hz, ideleFinAt_ofAdic_ne hvv, mul_one]
            exact h3 v' hv'S (by simp [hvv, hv'T]))
        have hzz : idelicArtinOf hR L z = artinTot L (ideleToIdeal K z) := by
          rw [hz, artinTot_ideleToIdeal_ofAdic L v π hπv k, map_zpow, map_zpow,
            (idelicArtinOf_spec hR L).1.frobenius v (hm v hvS) π hπv]
        rw [map_mul, map_mul, map_mul, hzz] at hyz
        exact mul_right_cancel hyz
      · refine ih y hy (fun v' hv'S hv'T => ?_)
        by_cases hvv : v' = v
        · subst hvv
          by_contra hcon
          exact hv ⟨hv'S, hcon⟩
        · exact h3 v' hv'S (by simp [hvv, hv'T])
  refine key (finite_valued_ne_one x).toFinset x hx fun v _ hvT => ?_
  by_contra hcon
  exact hvT ((finite_valued_ne_one x).mem_toFinset.mpr hcon)

/-- The Artin map $I^{S(\mathfrak m)}\to\mathrm{Gal}(L/K)$ is onto. -/
theorem artinMap_surjective_of_idelic (m : Modulus K)
    (hm : ∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L) (hW : idelesW m ≤ (idelicArtinOf hR L).ker) :
    Function.Surjective (artinMap L m.finiteSupport) := by
  intro g
  obtain ⟨z, rfl⟩ := (idelicArtinOf_spec hR L).2.2.1 g
  obtain ⟨y, hy⟩ := (prop_4_6b m).1 (z : IdeleClassGroup (𝓞 K) K)
  obtain ⟨a, ha⟩ := (QuotientGroup.eq.mp hy)
  have hx : z = (y : IdeleGroup (𝓞 K) K) * IdeleGroup.unitEmbedding (𝓞 K) K a := by
    rw [ha]; simp
  refine ⟨⟨ideleToIdeal K y, ideleToIdeal_mem_coprimeIdeals m y y.2⟩, ?_⟩
  change artinTot L (ideleToIdeal K y) = _
  rw [← idelicArtinOf_eq_artinTot hR L m hm hW y y.2, hx, map_mul,
    (idelicArtinOf_spec hR L).2.1 a, mul_one]

/-- The kernel of the Artin map $I^{S(\mathfrak m)}\to\mathrm{Gal}(L/K)$ contains
$P_\mathfrak m\cdot\mathrm{Nm}(I_L^{S(\mathfrak m)})$. -/
theorem le_ker_artinMap_of_idelic (m : Modulus K)
    (hm : ∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L) (hW : idelesW m ≤ (idelicArtinOf hR L).ker) :
    (rayPrincipal m ⊔ normIdeals K L m.finiteSupport).subgroupOf (sIdeals m.finiteSupport) ≤
      (artinMap L m.finiteSupport).ker := by
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨r, ⟨a, ha, rfl⟩, n, hn, hrn⟩ := Subgroup.mem_sup.mp hg
  rw [MonoidHom.mem_ker]
  change artinTot L (g : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1
  have h1 : artinTot L (toPrincipalIdeal (𝓞 K) K a) = 1 := by
    rw [← ideleToIdeal_unitEmbedding, ← idelicArtinOf_eq_artinTot hR L m hm hW _
      ((mem_congruenceSubgroup_iff_mem_idelesMod m a).mp ha),
      (idelicArtinOf_spec hR L).2.1 a]
  have h2 : artinTot L n = 1 :=
    cor_3_4 L m.finiteSupport hm ⟨n, normIdeals_le K L _ hn⟩ hn
  rw [← hrn, map_mul, h1, h2, mul_one]

end NumberFieldKB.MilneCFT
