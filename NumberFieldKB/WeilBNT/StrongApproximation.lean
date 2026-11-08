import NumberFieldKB.WeilBNT.FundamentalSet
import NumberFieldKB.WeilBNT.AdeleAnnihilator
import NumberFieldKB.Ideles.InfiniteAdeleRing

/-!
# Weil, *Basic Number Theory*, IV.§2, Cor. 2 of Thm. 3: $E+E_v$ is dense in $E_{\mathbb A}$ (number fields)

$k$ is a number field (`K`), $k_{\mathbb A}$ Mathlib's adele ring `AdeleRing (𝓞 K) K`
$=k_\infty\times\mathbb A_k^{\mathrm{fin}}$, $k$ embedded diagonally (`algebraMap`). For a place $v$, the quasifactor
$k_v$ of $k_{\mathbb A}$ is the set of adeles whose components at all places $\ne v$ are $0$.

* `weil_IV_2_cor2_thm3_infinite`: for an infinite place $w$, $k+k_w$ is dense in $k_{\mathbb A}$ ("strong
  approximation"; the case used most often).
* `weil_IV_2_cor2_thm3_finite`: for a finite place $v$, $k+k_v$ is dense in $k_{\mathbb A}$.
* `weil_IV_2_cor2_thm3_pi_infinite`, `weil_IV_2_cor2_thm3_pi_finite`: the same for $E=k^n$, $E_{\mathbb A}=k_{\mathbb A}^n$
  (Weil's Corollary for an arbitrary finite-dimensional $E$, in coordinates).

*Proof* (not Weil's, which uses the duality theory of the adeles; this is the argument of Cassels–Fröhlich, Ch. II,
§15). By V.§4 Prop. 6 (`FundamentalSet`), $k_{\mathbb A}=k+C$ with $C$ bounded at the infinite places and integral at the
finite places. Given a basic neighbourhood $U$ of $0$ (prescribed divisibility by an ideal $\mathfrak a$ at finitely
many finite places, integral elsewhere, small at the infinite places other than $v$), Minkowski's theorem in the ideal
lattice $\mathfrak a$ (or $\mathfrak a\mathfrak p_v^{-N}$ when $v$ is finite) gives $y\in k^\times$ with $yC\subseteq U+k_v$;
then $k_{\mathbb A}=y k_{\mathbb A}=k+yC\subseteq k+k_v+U$.
-/

open IsDedekindDomain NumberField Topology Filter NumberField.mixedEmbedding
open QuadFormsKB.Tamagawa.Measure.Weil
open NumberFieldKB.Ideles
open scoped RestrictedProduct nonZeroDivisors

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

open Classical in
/-- The quasifactor $k_w$ of $k_{\mathbb A}$ at an infinite place $w$: $x\mapsto(x\text{ at }w,0\text{ elsewhere})$. -/
def quasiInf (w : InfinitePlace K) (x : w.Completion) : AdeleRing (𝓞 K) K :=
  ((Pi.single w x : InfiniteAdeleRing K), 0)

/-- A finite adele $f$ viewed in $k_{\mathbb A}$ (infinite components $0$). -/
def ofFinite (f : FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K := ((0 : InfiniteAdeleRing K), f)

theorem exists_nat_restrict_lt {L : Type*} [Field L] (v : Valuation L (WithZero (Multiplicative ℤ)))
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
/-- A neighbourhood of zero in the finite adeles contains all finite adeles that are integral everywhere and
divisible by a high power of the uniformizer at the places of some finite set. -/
theorem exists_finset_nat_of_mem_nhds_zero {W : Set (FiniteAdeleRing (𝓞 K) K)}
    (hW : W ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ), ∀ x : FiniteAdeleRing (𝓞 K) K,
      (∀ u, x u ∈ u.adicCompletionIntegers K) →
      (∀ u ∈ S, Valued.v (x u) ≤ WithZero.exp (-(N : ℤ))) → x ∈ W := by
  have hopen : ∀ u : HeightOneSpectrum (𝓞 K),
      IsOpen (u.adicCompletionIntegers K : Set (u.adicCompletion K)) :=
    fun _ => Valued.isOpen_valuationSubring _
  have h0 := RestrictedProduct.nhds_zero_eq_map_structureMap
    (R := fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K)
    (B := fun u => u.adicCompletionIntegers K) hopen
  have hW2 : W ∈ Filter.map (RestrictedProduct.structureMap
      (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K)
      (fun u => (u.adicCompletionIntegers K : Set (u.adicCompletion K))) cofinite) (𝓝 0) := by
    rw [← h0]; exact hW
  have hW3 := Filter.mem_map.mp hW2
  rw [nhds_pi, Filter.mem_pi'] at hW3
  obtain ⟨I, t, ht, hIt⟩ := hW3
  have hN : ∀ u, ∃ N : ℕ, ∀ y : u.adicCompletionIntegers K,
      Valued.v (y : u.adicCompletion K) ≤ WithZero.exp (-(N : ℤ)) → y ∈ t u := by
    intro u
    obtain ⟨V, hV, hVt⟩ := mem_nhds_subtype _ _ _ |>.mp (ht u)
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hV
    obtain ⟨N, hN⟩ := exists_nat_restrict_lt (Valued.v : Valuation (u.adicCompletion K) _) γ
    exact ⟨N, fun y hy => hVt (hγ (hN y hy))⟩
  choose N hN using hN
  refine ⟨I, I.sup N, fun x hxint hx => ?_⟩
  have hxm : RestrictedProduct.structureMap (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K)
      (fun u => (u.adicCompletionIntegers K : Set (u.adicCompletion K))) cofinite
      (fun u => ⟨x u, hxint u⟩) = x := rfl
  rw [← hxm]
  refine hIt (fun u hu => hN u _ ?_)
  refine le_trans (hx u hu) ?_
  refine WithZero.exp_le_exp.mpr ?_
  have : N u ≤ I.sup N := Finset.le_sup hu
  omega

/-- A neighbourhood of zero in the infinite adeles contains all infinite adeles that are small at every place. -/
theorem exists_eps_of_mem_nhds_zero {V : Set (InfiniteAdeleRing K)}
    (hV : V ∈ 𝓝 (0 : InfiniteAdeleRing K)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : InfiniteAdeleRing K, (∀ w, ‖x w‖ < ε) → x ∈ V := by
  have hV' : V ∈ Filter.pi (fun w : InfinitePlace K => 𝓝 (0 : w.Completion)) := by
    have := hV
    rw [show (0 : InfiniteAdeleRing K) = (fun _ => 0) from rfl, show 𝓝 (fun w : InfinitePlace K => (0 : w.Completion)) = Filter.pi (fun w => 𝓝 0) from nhds_pi] at this
    exact this
  rw [Filter.mem_pi'] at hV'
  obtain ⟨I, t, ht, hIt⟩ := hV'
  have hε : ∀ w, ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : w.Completion) ε ⊆ t w := fun w => Metric.mem_nhds_iff.mp (ht w)
  choose ε hε0 hεt using hε
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ε, (Finset.lt_inf'_iff _).mpr fun w _ => hε0 w, fun x hx => hIt fun w _ => hεt w ?_⟩
  rw [mem_ball_zero_iff]
  exact lt_of_lt_of_le (hx w) (Finset.inf'_le _ (Finset.mem_univ w))

open Classical in
/-- A neighbourhood basis statement for the adele ring at zero. -/
theorem exists_eps_finset_nat_of_mem_nhds_zero {U : Set (AdeleRing (𝓞 K) K)}
    (hU : U ∈ 𝓝 (0 : AdeleRing (𝓞 K) K)) :
    ∃ (ε : ℝ) (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ), 0 < ε ∧ ∀ x : AdeleRing (𝓞 K) K,
      (∀ w, ‖x.1 w‖ < ε) → (∀ u, x.2 u ∈ u.adicCompletionIntegers K) →
      (∀ u ∈ S, Valued.v (x.2 u) ≤ WithZero.exp (-(N : ℤ))) → x ∈ U := by
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hU
  obtain ⟨ε, hε, hεV⟩ := exists_eps_of_mem_nhds_zero hV
  obtain ⟨S, N, hSN⟩ := exists_finset_nat_of_mem_nhds_zero hW
  exact ⟨ε, S, N, hε, fun x h1 h2 h3 => hVW ⟨hεV x.1 h1, hSN x.2 h2 h3⟩⟩

open Classical in
/-- Weil V.4 Prop. 6 in the form needed here: there is a bound `R` such that every adele is a number field
element plus an adele that is bounded by `R` at the infinite places and integral at the finite places. -/
theorem exists_bounded_decomposition :
    ∃ R : ℝ, 0 < R ∧ ∀ a : AdeleRing (𝓞 K) K, ∃ (ξ : K) (c : AdeleRing (𝓞 K) K),
      a = algebraMap K _ ξ + c ∧ (∀ w, ‖c.1 w‖ ≤ R) ∧ ∀ u, c.2 u ∈ u.adicCompletionIntegers K := by
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  have hbdd : Bornology.IsBounded (thetaBox b) := by
    rw [thetaBox_eq]; exact ZSpan.fundamentalDomain_isBounded _
  obtain ⟨R0, hR0⟩ := hbdd.exists_norm_le
  refine ⟨max R0 0 + 1, by positivity, fun a => ?_⟩
  obtain ⟨ξ, hξ, -⟩ := weil_V_4_prop6 b
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K a.1, a.2) : Adeles K)
  refine ⟨ξ, a - algebraMap K _ ξ, by ring, fun w => ?_, fun u => hξ.2 u⟩
  have h1 := hξ.1
  have h2 : InfiniteAdeleRing.ringEquiv_mixedSpace K (a - algebraMap K _ ξ).1 =
      InfiniteAdeleRing.ringEquiv_mixedSpace K a.1 - mixedEmbedding K ξ := by
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← map_sub]; rfl
  rw [← normAtPlace_ringEquiv_mixedSpace, h2]
  set d := InfiniteAdeleRing.ringEquiv_mixedSpace K a.1 - mixedEmbedding K ξ with hd
  have h3 : normAtPlace w d ≤ ‖d‖ := by
    rw [norm_eq_sup'_normAtPlace]
    exact Finset.le_sup' (fun w => normAtPlace w d) (Finset.mem_univ w)
  have h4 : ‖d‖ ≤ R0 := hR0 d h1
  linarith [le_max_left R0 0]

open Classical in
/-- Minkowski's theorem for the ring of integers: a nonzero integer that is small at every infinite place exists as
soon as the product of the bounds (with multiplicities) exceeds a constant. -/
theorem exists_integer_lt_of_prod_gt :
    ∃ B : NNReal, ∀ f : InfinitePlace K → NNReal, B < ∏ w, f w ^ w.mult →
      ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < f w := by
  refine ⟨(minkowskiBound K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)).toNNReal, fun f hf => ?_⟩
  refine exists_ne_zero_mem_ringOfIntegers_lt K ?_
  rw [convexBodyLT_volume, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)).ne]
  exact ENNReal.coe_lt_coe.mpr (lt_of_lt_of_le hf
    (le_mul_of_one_le_left zero_le (one_le_convexBodyLTFactor K)))

open Classical in
/-- A nonzero integer that is smaller than prescribed positive bounds at all infinite places but one. -/
theorem exists_integer_lt_except (w : InfinitePlace K) (c : InfinitePlace K → ℝ) (hc : ∀ w', 0 < c w') :
    ∃ s : 𝓞 K, s ≠ 0 ∧ ∀ w', w' ≠ w → w' s < c w' := by
  obtain ⟨B, hB⟩ := exists_integer_lt_of_prod_gt (K := K)
  set P : NNReal := ∏ w' ∈ Finset.univ.erase w, (c w').toNNReal ^ w'.mult with hPdef
  have hP : 0 < P := Finset.prod_pos fun w' _ => pow_pos (Real.toNNReal_pos.mpr (hc w')) _
  set M : NNReal := max 1 ((B + 1) / P) with hM
  obtain ⟨a, ha0, ha⟩ := hB (fun w' => if w' = w then M else (c w').toNNReal) (by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
    have h1 : ∏ w' ∈ Finset.univ.erase w, (if w' = w then M else (c w').toNNReal) ^ w'.mult = P :=
      Finset.prod_congr rfl fun w' hw' => by simp [Finset.ne_of_mem_erase hw']
    rw [h1, if_pos rfl]
    have h2 : M ≤ M ^ w.mult := le_self_pow₀ (le_max_left _ _) (InfinitePlace.mult_pos).ne'
    calc B < B + 1 := by simp
      _ = (B + 1) / P * P := (div_mul_cancel₀ _ hP.ne').symm
      _ ≤ M * P := by gcongr; exact le_max_right _ _
      _ ≤ M ^ w.mult * P := by gcongr)
  refine ⟨a, ha0, fun w' hw' => ?_⟩
  have := ha w'
  rw [if_neg hw', Real.coe_toNNReal _ (hc w').le] at this
  exact this

/-- The valuation of the completion restricted to the number field is the adic valuation. -/
theorem valued_algebraMap' (v : HeightOneSpectrum (𝓞 K)) (y : K) :
    Valued.v (algebraMap K (v.adicCompletion K) y) = v.valuation K y := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion (𝓞 K)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y

/-- An integer has valuation at most one at every finite place. -/
theorem valued_integer_le_one (u : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    Valued.v (algebraMap K (u.adicCompletion K) (x : K)) ≤ 1 := by
  rw [valued_algebraMap']
  exact u.valuation_le_one x

open Classical in
/-- A nonzero integer divisible by the `N`-th power of every prime in `S`. -/
theorem exists_integer_dvd_pow (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ u ∈ S, d ∈ u.asIdeal ^ N := by
  have hne : (∏ u ∈ S, u.asIdeal ^ N) ≠ ⊥ :=
    Finset.prod_ne_zero_iff.mpr fun u _ => pow_ne_zero _ u.ne_bot
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨d, hd0, fun u hu => ?_⟩
  have : u.asIdeal ^ N ∣ ∏ u ∈ S, u.asIdeal ^ N := Finset.dvd_prod_of_mem _ hu
  exact (Ideal.dvd_iff_le.mp this) hd

/-- The multiplier for the infinite place case: a nonzero number field element that is small at all infinite
places but `w`, integral at all finite places and divisible by a high power at the places of `S`. -/
theorem exists_multiplier_infinite (w : InfinitePlace K) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    ∃ y : K, y ≠ 0 ∧ (∀ w', w' ≠ w → w' y * R < ε) ∧
      (∀ u : HeightOneSpectrum (𝓞 K), Valued.v (algebraMap K (u.adicCompletion K) y) ≤ 1) ∧
      ∀ u ∈ S, Valued.v (algebraMap K (u.adicCompletion K) y) ≤ WithZero.exp (-(N : ℤ)) := by
  obtain ⟨d, hd0, hd⟩ := exists_integer_dvd_pow S N
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  obtain ⟨s, hs0, hs⟩ := exists_integer_lt_except w (fun w' => ε / (R * w' (d : K)))
    (fun w' => div_pos hε (mul_pos hR ((InfinitePlace.pos_iff).mpr hdK)))
  have hsK : (s : K) ≠ 0 := by exact_mod_cast hs0
  refine ⟨(d : K) * s, mul_ne_zero hdK hsK, fun w' hw' => ?_, fun u => ?_, fun u hu => ?_⟩
  · have h1 := hs w' hw'
    have hpos : 0 < w' (d : K) := (InfinitePlace.pos_iff).mpr hdK
    rw [map_mul]
    calc w' (d : K) * w' (s : K) * R < w' (d : K) * (ε / (R * w' (d : K))) * R := by gcongr
      _ = ε := by field_simp
  · rw [map_mul, map_mul]
    exact mul_le_one' (valued_integer_le_one u d) (valued_integer_le_one u s)
  · rw [map_mul, map_mul]
    calc Valued.v (algebraMap K (u.adicCompletion K) (d : K)) * Valued.v (algebraMap K (u.adicCompletion K) (s : K))
        ≤ WithZero.exp (-(N : ℤ)) * 1 :=
          mul_le_mul' (QuadFormsKB.Analysis.valued_algebraMap_int_le_of_mem u (hd u hu)) (valued_integer_le_one u s)
      _ = _ := mul_one _

theorem sa_norm_coe_completion (w : InfinitePlace K) (y : K) : ‖(y : w.Completion)‖ = w y := by
  have := InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm y)
  simpa using this

/-- Density criterion in terms of neighbourhoods of zero. -/
theorem dense_of_forall_mem_nhds_zero {D : Set (AdeleRing (𝓞 K) K)}
    (h : ∀ a : AdeleRing (𝓞 K) K, ∀ U ∈ 𝓝 (0 : AdeleRing (𝓞 K) K), ∃ s ∈ D, a - s ∈ U) : Dense D := by
  intro a
  rw [mem_closure_iff_nhds]
  intro t ht
  have hU : {x | a - x ∈ t} ∈ 𝓝 (0 : AdeleRing (𝓞 K) K) := by
    have : Continuous fun x : AdeleRing (𝓞 K) K => a - x := continuous_const.sub continuous_id
    exact this.tendsto' 0 a (sub_zero a) ht
  obtain ⟨s, hs, hsU⟩ := h a _ hU
  exact ⟨s, by simpa using hsU, hs⟩

theorem snd_algebraMap_apply (y : K) (u : HeightOneSpectrum (𝓞 K)) :
    (algebraMap K (AdeleRing (𝓞 K) K) y).2 u = algebraMap K (u.adicCompletion K) y := rfl

open Classical in
theorem sub_quasiInf_fst_same (e : AdeleRing (𝓞 K) K) (w : InfinitePlace K) :
    (e - quasiInf w (e.1 w)).1 w = 0 := by
  show e.1 w - (Pi.single w (e.1 w) : InfiniteAdeleRing K) w = 0
  rw [Pi.single_eq_same, sub_self]

open Classical in
theorem sub_quasiInf_fst_ne (e : AdeleRing (𝓞 K) K) {w w' : InfinitePlace K} (h : w' ≠ w) :
    (e - quasiInf w (e.1 w)).1 w' = e.1 w' := by
  show e.1 w' - (Pi.single w (e.1 w) : InfiniteAdeleRing K) w' = _
  rw [Pi.single_eq_of_ne h, sub_zero]

theorem sub_quasiInf_snd (e : AdeleRing (𝓞 K) K) (w : InfinitePlace K) (x : w.Completion) :
    (e - quasiInf w x).2 = e.2 := by
  show e.2 - 0 = _
  rw [sub_zero]

theorem snd_algebraMap_mul_apply (y : K) (c : AdeleRing (𝓞 K) K) (u : HeightOneSpectrum (𝓞 K)) :
    (algebraMap K (AdeleRing (𝓞 K) K) y * c).2 u = algebraMap K (u.adicCompletion K) y * c.2 u := rfl


/-- Minkowski's theorem with real bounds. -/
theorem exists_integer_lt_of_prod_gt_real :
    ∃ B : ℝ, ∀ f : InfinitePlace K → ℝ, (∀ w, 0 < f w) → B < ∏ w, f w ^ w.mult →
      ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < f w := by
  obtain ⟨B, hB⟩ := exists_integer_lt_of_prod_gt (K := K)
  refine ⟨B, fun f hf hprod => ?_⟩
  obtain ⟨a, ha0, ha⟩ := hB (fun w => (f w).toNNReal) (by
    rw [← NNReal.coe_lt_coe]
    push_cast
    simpa [Real.coe_toNNReal _ (hf _).le] using hprod)
  exact ⟨a, ha0, fun w => by simpa [Real.coe_toNNReal _ (hf w).le] using ha w⟩

/-- Some power of a prime is principal (the class group is finite). -/
theorem exists_generator_pow (v : HeightOneSpectrum (𝓞 K)) :
    ∃ (h : ℕ) (t : 𝓞 K), 0 < h ∧ Ideal.span {t} = v.asIdeal ^ h := by
  have hmem : v.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  refine ⟨Fintype.card (ClassGroup (𝓞 K)), ?_⟩
  have h1 : ClassGroup.mk0 (⟨v.asIdeal, hmem⟩ : (Ideal (𝓞 K))⁰) ^ Fintype.card (ClassGroup (𝓞 K)) = 1 :=
    pow_card_eq_one
  rw [← map_pow, SubmonoidClass.mk_pow] at h1
  have h2 := (ClassGroup.mk0_eq_one_iff (pow_mem hmem _)).mp h1
  have := h2
  exact ⟨Submodule.IsPrincipal.generator (v.asIdeal ^ Fintype.card (ClassGroup (𝓞 K))), Fintype.card_pos,
    Ideal.span_singleton_generator _⟩

theorem generator_ne_zero {v : HeightOneSpectrum (𝓞 K)} {h : ℕ} {t : 𝓞 K}
    (ht : Ideal.span {t} = v.asIdeal ^ h) : t ≠ 0 := by
  rintro rfl
  rw [Ideal.span_singleton_eq_bot.mpr rfl] at ht
  exact pow_ne_zero _ v.ne_bot ht.symm

theorem generator_not_mem {v u : HeightOneSpectrum (𝓞 K)} {h : ℕ} {t : 𝓞 K}
    (ht : Ideal.span {t} = v.asIdeal ^ h) (huv : u ≠ v) : t ∉ u.asIdeal := by
  intro hmem
  have h1 : v.asIdeal ^ h ≤ u.asIdeal := by
    rw [← ht]; exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have h2 : v.asIdeal ≤ u.asIdeal := u.isPrime.le_of_pow_le h1
  exact huv (HeightOneSpectrum.ext ((v.isMaximal.eq_of_le u.isPrime.ne_top h2).symm))

theorem valued_generator_eq_one {v u : HeightOneSpectrum (𝓞 K)} {h : ℕ} {t : 𝓞 K}
    (ht : Ideal.span {t} = v.asIdeal ^ h) (huv : u ≠ v) :
    Valued.v (algebraMap K (u.adicCompletion K) (t : K)) = 1 := by
  rw [valued_algebraMap', HeightOneSpectrum.valuation_of_algebraMap]
  refine le_antisymm (u.intValuation_le_one t) (not_lt.mp fun hlt => ?_)
  exact generator_not_mem ht huv ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).mp hlt)

theorem one_lt_prod_generator {v : HeightOneSpectrum (𝓞 K)} {h : ℕ} {t : 𝓞 K} (hh : 0 < h)
    (ht : Ideal.span {t} = v.asIdeal ^ h) : 1 < ∏ w : InfinitePlace K, w (t : K) ^ w.mult := by
  have h0 := generator_ne_zero ht
  have hne : Ideal.span {t} ≠ ⊤ := by
    rw [ht]
    exact ne_top_of_le_ne_top v.isPrime.ne_top (Ideal.pow_le_self hh.ne')
  have h1 : Ideal.absNorm (Ideal.span {t}) ≠ 1 := fun h1 => hne (Ideal.absNorm_eq_one_iff.mp h1)
  rw [Ideal.absNorm_span_singleton] at h1
  have h2 : (Algebra.norm ℤ t).natAbs ≠ 0 := by
    rw [Ne, Int.natAbs_eq_zero, Algebra.norm_eq_zero_iff]; exact h0
  rw [InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int]
  have h3 : (1 : ℤ) < |Algebra.norm ℤ t| := by
    rw [Int.abs_eq_natAbs]; omega
  exact_mod_cast h3

open Classical in
/-- The multiplier for the finite place case: a nonzero number field element that is small at all infinite places,
integral at all finite places other than `v`, and divisible by a high power at the places of `S` other than `v`. -/
theorem exists_multiplier_finite (v : HeightOneSpectrum (𝓞 K)) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    ∃ y : K, y ≠ 0 ∧ (∀ w' : InfinitePlace K, w' y * R < ε) ∧
      (∀ u : HeightOneSpectrum (𝓞 K), u ≠ v → Valued.v (algebraMap K (u.adicCompletion K) y) ≤ 1) ∧
      ∀ u ∈ S, u ≠ v → Valued.v (algebraMap K (u.adicCompletion K) y) ≤ WithZero.exp (-(N : ℤ)) := by
  obtain ⟨h, t, hh, ht⟩ := exists_generator_pow v
  obtain ⟨d, hd0, hd⟩ := exists_integer_dvd_pow (S.erase v) N
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  have ht0 : t ≠ 0 := generator_ne_zero ht
  have htK : (t : K) ≠ 0 := by exact_mod_cast ht0
  obtain ⟨B, hB⟩ := exists_integer_lt_of_prod_gt_real (K := K)
  set δ : InfinitePlace K → ℝ := fun w' => ε / (R * w' (d : K)) with hδ
  have hδpos : ∀ w', 0 < δ w' := fun w' => div_pos hε (mul_pos hR ((InfinitePlace.pos_iff).mpr hdK))
  have hΔ : 0 < ∏ w' : InfinitePlace K, δ w' ^ w'.mult := Finset.prod_pos fun w' _ => pow_pos (hδpos w') _
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (B / ∏ w' : InfinitePlace K, δ w' ^ w'.mult)
    (one_lt_prod_generator hh ht)
  have htpos : ∀ w' : InfinitePlace K, 0 < w' (t : K) := fun w' => (InfinitePlace.pos_iff).mpr htK
  obtain ⟨s, hs0, hs⟩ := hB (fun w' => δ w' * w' (t : K) ^ m) (fun w' => mul_pos (hδpos w') (pow_pos (htpos w') _)) (by
    have : ∏ w' : InfinitePlace K, (δ w' * w' (t : K) ^ m) ^ w'.mult =
        (∏ w' : InfinitePlace K, δ w' ^ w'.mult) * (∏ w' : InfinitePlace K, w' (t : K) ^ w'.mult) ^ m := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w' _ => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m]
    rw [this]
    rw [div_lt_iff₀ hΔ] at hm
    linarith)
  have hsK : (s : K) ≠ 0 := by exact_mod_cast hs0
  refine ⟨(d : K) * s / (t : K) ^ m, div_ne_zero (mul_ne_zero hdK hsK) (pow_ne_zero _ htK), fun w' => ?_,
    fun u hu => ?_, fun u hu huv => ?_⟩
  · have h1 := hs w'
    have ha : 0 < w' (d : K) := (InfinitePlace.pos_iff).mpr hdK
    have hb : 0 < w' (t : K) ^ m := pow_pos (htpos w') _
    simp only [hδ] at h1
    rw [map_div₀, map_mul, map_pow, div_mul_eq_mul_div, div_lt_iff₀ hb]
    rw [show ε / (R * w' (d : K)) * w' (t : K) ^ m = ε * w' (t : K) ^ m / (R * w' (d : K)) by ring,
      lt_div_iff₀ (mul_pos hR ha)] at h1
    calc w' (d : K) * w' (s : K) * R = w' (s : K) * (R * w' (d : K)) := by ring
      _ < ε * w' (t : K) ^ m := h1
  · simp only [map_div₀, map_mul, map_pow]
    rw [valued_generator_eq_one ht hu, one_pow, div_one]
    exact mul_le_one' (valued_integer_le_one u d) (valued_integer_le_one u s)
  · simp only [map_div₀, map_mul, map_pow]
    rw [valued_generator_eq_one ht huv, one_pow, div_one]
    calc _ ≤ WithZero.exp (-(N : ℤ)) * 1 :=
          mul_le_mul' (QuadFormsKB.Analysis.valued_algebraMap_int_le_of_mem u
            (hd u (Finset.mem_erase.mpr ⟨huv, hu⟩))) (valued_integer_le_one u s)
      _ = _ := mul_one _


open Classical in
/-- The finite adele supported at the place `v` with value `x` there. -/
def finiteSingle (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.single (G := fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K)
    (fun u => u.adicCompletionIntegers K) v x

open Classical in
theorem finiteSingle_same (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteSingle v x v = x :=
  RestrictedProduct.single_eq_same _ _ _

open Classical in
theorem finiteSingle_ne (v u : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (h : u ≠ v) :
    finiteSingle v x u = 0 :=
  RestrictedProduct.single_eq_of_ne _ _ h


@[kb "weil1973bnt" "Ch. IV, §2, Cor. 2 of Thm. 3 (E = k, an infinite place; number field case)"]
theorem weil_IV_2_cor2_thm3_infinite (w : InfinitePlace K) :
    Dense {a : AdeleRing (𝓞 K) K | ∃ (ξ : K) (x : w.Completion), a = algebraMap K _ ξ + quasiInf w x} := by
  classical
  refine dense_of_forall_mem_nhds_zero fun a U hU => ?_
  obtain ⟨ε, S, N, hε, hmain⟩ := exists_eps_finset_nat_of_mem_nhds_zero hU
  obtain ⟨R, hR, hdec⟩ := exists_bounded_decomposition (K := K)
  obtain ⟨y, hy0, hy1, hy2, hy3⟩ := exists_multiplier_infinite w hR hε S N
  obtain ⟨ξ, c, hc, hcw, hcint⟩ := hdec (algebraMap K _ y⁻¹ * a)
  set e : AdeleRing (𝓞 K) K := algebraMap K _ y * c with he
  have hya : algebraMap K (AdeleRing (𝓞 K) K) y * algebraMap K _ y⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
  have ha : a = algebraMap K _ (y * ξ) + e := by
    have : a = algebraMap K (AdeleRing (𝓞 K) K) y * (algebraMap K _ y⁻¹ * a) := by
      rw [← mul_assoc, hya, one_mul]
    rw [this, hc, map_mul, he]; ring
  refine ⟨algebraMap K _ (y * ξ) + quasiInf w (e.1 w), ⟨y * ξ, e.1 w, rfl⟩, ?_⟩
  have hsub : a - (algebraMap K _ (y * ξ) + quasiInf w (e.1 w)) = e - quasiInf w (e.1 w) := by
    rw [ha]; ring
  rw [hsub]
  refine hmain _ (fun w' => ?_) (fun u => ?_) (fun u hu => ?_)
  · by_cases hw : w' = w
    · subst hw
      rw [sub_quasiInf_fst_same, norm_zero]; exact hε
    · have h1 : (e - quasiInf w (e.1 w)).1 w' = (y : w'.Completion) * c.1 w' := by
        rw [sub_quasiInf_fst_ne e hw]; rfl
      rw [h1, norm_mul, sa_norm_coe_completion]
      calc w' y * ‖c.1 w'‖ ≤ w' y * R := by gcongr; exact hcw w'
        _ < ε := hy1 w' hw
  · rw [sub_quasiInf_snd, he, snd_algebraMap_mul_apply, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul]
    exact mul_le_one' (hy2 u) ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hcint u))
  · rw [sub_quasiInf_snd, he, snd_algebraMap_mul_apply, map_mul]
    calc _ ≤ WithZero.exp (-(N : ℤ)) * 1 :=
          mul_le_mul' (hy3 u hu) ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hcint u))
      _ = _ := mul_one _

@[kb "weil1973bnt" "Ch. IV, §2, Cor. 2 of Thm. 3 (E = k, a finite place; number field case)"]
theorem weil_IV_2_cor2_thm3_finite (v : HeightOneSpectrum (𝓞 K)) :
    Dense {a : AdeleRing (𝓞 K) K | ∃ (ξ : K) (f : FiniteAdeleRing (𝓞 K) K),
      (∀ v', v' ≠ v → f v' = 0) ∧ a = algebraMap K _ ξ + ofFinite f} := by
  classical
  refine dense_of_forall_mem_nhds_zero fun a U hU => ?_
  obtain ⟨ε, S, N, hε, hmain⟩ := exists_eps_finset_nat_of_mem_nhds_zero hU
  obtain ⟨R, hR, hdec⟩ := exists_bounded_decomposition (K := K)
  obtain ⟨y, hy0, hy1, hy2, hy3⟩ := exists_multiplier_finite v hR hε S N
  obtain ⟨ξ, c, hc, hcw, hcint⟩ := hdec (algebraMap K _ y⁻¹ * a)
  set e : AdeleRing (𝓞 K) K := algebraMap K _ y * c with he
  have hya : algebraMap K (AdeleRing (𝓞 K) K) y * algebraMap K _ y⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
  have ha : a = algebraMap K _ (y * ξ) + e := by
    have : a = algebraMap K (AdeleRing (𝓞 K) K) y * (algebraMap K _ y⁻¹ * a) := by
      rw [← mul_assoc, hya, one_mul]
    rw [this, hc, map_mul, he]; ring
  refine ⟨algebraMap K _ (y * ξ) + ofFinite (finiteSingle v (e.2 v)),
    ⟨y * ξ, finiteSingle v (e.2 v), fun u hu => finiteSingle_ne v u _ hu, rfl⟩, ?_⟩
  have hsub : a - (algebraMap K _ (y * ξ) + ofFinite (finiteSingle v (e.2 v))) =
      e - ofFinite (finiteSingle v (e.2 v)) := by
    rw [ha]; ring
  rw [hsub]
  have hfst : ∀ w' : InfinitePlace K, (e - ofFinite (finiteSingle v (e.2 v))).1 w' = (y : w'.Completion) * c.1 w' := by
    intro w'
    show e.1 w' - 0 = _
    rw [sub_zero]; rfl
  have hsnd : ∀ u, (e - ofFinite (finiteSingle v (e.2 v))).2 u = e.2 u - finiteSingle v (e.2 v) u := fun u => rfl
  have hcu : ∀ u, Valued.v (c.2 u) ≤ 1 := fun u =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hcint u)
  refine hmain _ (fun w' => ?_) (fun u => ?_) (fun u hu => ?_)
  · rw [hfst, norm_mul, sa_norm_coe_completion]
    calc w' y * ‖c.1 w'‖ ≤ w' y * R := by gcongr; exact hcw w'
      _ < ε := hy1 w'
  · rw [hsnd, HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases huv : u = v
    · subst huv
      rw [finiteSingle_same, sub_self, map_zero]; exact zero_le
    · rw [finiteSingle_ne v u _ huv, sub_zero, he, snd_algebraMap_mul_apply, map_mul]
      exact mul_le_one' (hy2 u huv) (hcu u)
  · rw [hsnd]
    by_cases huv : u = v
    · subst huv
      rw [finiteSingle_same, sub_self, map_zero]; exact zero_le
    · rw [finiteSingle_ne v u _ huv, sub_zero, he, snd_algebraMap_mul_apply, map_mul]
      calc _ ≤ WithZero.exp (-(N : ℤ)) * 1 := mul_le_mul' (hy3 u hu huv) (hcu u)
        _ = _ := mul_one _

@[kb "weil1973bnt" "Ch. IV, §2, Cor. 2 of Thm. 3 (E = k^n, an infinite place; number field case)"]
theorem weil_IV_2_cor2_thm3_pi_infinite (n : ℕ) (w : InfinitePlace K) :
    Dense {a : Fin n → AdeleRing (𝓞 K) K | ∃ (ξ : Fin n → K) (x : Fin n → w.Completion),
      a = fun i => algebraMap K _ (ξ i) + quasiInf w (x i)} := by
  have : {a : Fin n → AdeleRing (𝓞 K) K | ∃ (ξ : Fin n → K) (x : Fin n → w.Completion),
      a = fun i => algebraMap K _ (ξ i) + quasiInf w (x i)} =
      Set.pi Set.univ (fun _ : Fin n => {a : AdeleRing (𝓞 K) K | ∃ (ξ : K) (x : w.Completion),
        a = algebraMap K _ ξ + quasiInf w x}) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨ξ, x, rfl⟩ i
      exact ⟨ξ i, x i, rfl⟩
    · intro h
      choose ξ x hx using h
      exact ⟨ξ, x, funext hx⟩
  rw [this]
  exact dense_pi _ fun _ _ => weil_IV_2_cor2_thm3_infinite w

@[kb "weil1973bnt" "Ch. IV, §2, Cor. 2 of Thm. 3 (E = k^n, a finite place; number field case)"]
theorem weil_IV_2_cor2_thm3_pi_finite (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    Dense {a : Fin n → AdeleRing (𝓞 K) K | ∃ (ξ : Fin n → K) (f : Fin n → FiniteAdeleRing (𝓞 K) K),
      (∀ i, ∀ v', v' ≠ v → f i v' = 0) ∧
        a = fun i => algebraMap K _ (ξ i) + ofFinite (f i)} := by
  have : {a : Fin n → AdeleRing (𝓞 K) K | ∃ (ξ : Fin n → K) (f : Fin n → FiniteAdeleRing (𝓞 K) K),
      (∀ i, ∀ v', v' ≠ v → f i v' = 0) ∧
        a = fun i => algebraMap K _ (ξ i) + ofFinite (f i)} =
      Set.pi Set.univ (fun _ : Fin n => {a : AdeleRing (𝓞 K) K | ∃ (ξ : K) (f : FiniteAdeleRing (𝓞 K) K),
        (∀ v', v' ≠ v → f v' = 0) ∧ a = algebraMap K _ ξ + ofFinite f}) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨ξ, f, hf, rfl⟩ i
      exact ⟨ξ i, f i, hf i, rfl⟩
    · intro h
      choose ξ f hf hx using h
      exact ⟨ξ, f, hf, funext hx⟩
  rw [this]
  exact dense_pi _ fun _ _ => weil_IV_2_cor2_thm3_finite v

end NumberFieldKB.WeilBNT
