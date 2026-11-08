import NumberFieldKB.MilneCFT.Ch8.Density

/-!
# Milne, *Class Field Theory*, Chapter VIII, Theorem 7.1, proved unconditionally

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, Theorem 7.1, p. 258.

**Theorem 7.1** (`theorem7_1`): for every modulus $\mathfrak m$ of a number field $K$ and every nontrivial character
$\chi : C_\mathfrak m \to \mathbb C^\times$ of the ray class group, $L(1,\chi) \ne 0$: the Weber $L$-series
`weberLSeries` tends to a nonzero limit as $s \downarrow 1$ (`Ch6.WeberLOneNeZero`). This discharges the named
statement `Theorem7_1 K` without the reciprocity law.

*Proof.* The route is analytic and does not use class field theory.

1. **A Euler product for ideal Dirichlet series** (`hasProd_euler`): if $g$ is a completely multiplicative function on the
   ideals of $\mathcal O_K$ with $|g(\mathfrak a)| \le N\mathfrak a^{-s}$, $s > 1$ real, then
   $\sum_\mathfrak a g(\mathfrak a) = \prod_\mathfrak p (1 - g(\mathfrak p))^{-1}$, unconditionally. This is the complex
   version of QuadFormsKB's sieve proof of the Euler product of $\zeta_K$ (`NFEuler.hasProd_dedekindZeta`).
2. **The Weber series** (`webTerm`, `weberLSeries_eq_tsum`) is such a series for $s > 1$ (`hasProd_weber`).
3. **The Hecke character** $\Psi$ of the finite order attached to $\chi$ (`exists_heckeChar`, Chapter V of this library):
   unramified outside $\mathfrak m_0$ with $\Psi_\mathfrak p(\varpi) = \chi([\mathfrak p])$. Its Hecke $L$-function and
   the Weber series differ by the finitely many Euler factors at $\mathfrak p \mid \mathfrak m_0$
   (`weberLSeries_mul_prod_eq_heckeL`), each continuous and nonzero at $s = 1$.
4. For $\chi \ne 1$, $\Psi$ is unitary and not a power of the norm, so `heckeLCont Ψ` is entire and nonzero at $1$
   (`NonVanishing.heckeLCont_ne_zero_of_re_eq_one`).
-/

open NumberField IsDedekindDomain Filter Topology QuadFormsKB QuadFormsKB.NFEuler
open NumberFieldKB.HeckeCharacter NumberFieldKB.HeckeL NumberFieldKB.NonVanishing NumberFieldKB.GlobalZeta
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type} [Field K] [NumberField K]

/-! ## A Euler product for completely multiplicative ideal series -/

section Sieve

open Classical

/-- The sieve sum $\sum_{\mathfrak a \text{ prime to } T} g(\mathfrak a)$. -/
def sieveC (g : Ideal (𝓞 K) → ℂ) (T : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  ∑' I, (coprimeTo T).indicator g I

variable (g : Ideal (𝓞 K) → ℂ) {s : ℝ}

theorem summable_of_bound (hs : 1 < s) (hbound : ∀ I, ‖g I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-s)) :
    Summable g :=
  Summable.of_norm_bounded (summable_absNorm_rpow (F := K) hs) hbound

/-- One sieve step: $Z(T \cup \{\mathfrak p\}) = (1 - g(\mathfrak p))\,Z(T)$ for $\mathfrak p \notin T$. -/
theorem sieveC_insert (hs : 1 < s) (hmul : ∀ I J, g (I * J) = g I * g J)
    (hbound : ∀ I, ‖g I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-s))
    {T : Finset (HeightOneSpectrum (𝓞 K))} {p : HeightOneSpectrum (𝓞 K)} (hp : p ∉ T) :
    sieveC g (insert p T) = (1 - g p.asIdeal) * sieveC g T := by
  have hgs : Summable g := summable_of_bound g hs hbound
  set q := p.asIdeal
  set D : Set (Ideal (𝓞 K)) := {I | I ∈ coprimeTo T ∧ I ≤ q} with hD
  have hsplit : ∀ I, (coprimeTo T).indicator g I =
      (coprimeTo (insert p T)).indicator g I + D.indicator g I := by
    intro I
    by_cases hI : I ∈ coprimeTo T
    · by_cases hIq : I ≤ q
      · have h1 : I ∉ coprimeTo (insert p T) := fun h => h p (Finset.mem_insert_self _ _) hIq
        have h2 : I ∈ D := ⟨hI, hIq⟩
        rw [Set.indicator_of_mem hI, Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]
      · have h1 : I ∈ coprimeTo (insert p T) := by
          intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hv
          · exact hIq
          · exact hI v hv
        have h2 : I ∉ D := fun h => hIq h.2
        rw [Set.indicator_of_mem hI, Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
    · have h1 : I ∉ coprimeTo (insert p T) := fun h => hI fun v hv => h v (Finset.mem_insert_of_mem hv)
      have h2 : I ∉ D := fun h => hI h.1
      rw [Set.indicator_of_notMem hI, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
  have hD_eq : ∑' I, D.indicator g I = g q * sieveC g T := by
    have hq0 : q ≠ ⊥ := p.ne_bot
    have hinj : Function.Injective (fun J : Ideal (𝓞 K) => q * J) := fun x y hxy =>
      mul_left_cancel₀ hq0 hxy
    have hsupp : Function.support (D.indicator g) ⊆ Set.range (fun J : Ideal (𝓞 K) => q * J) := by
      intro I hI
      have hmem : I ∈ D := by
        by_contra hn; exact hI (Set.indicator_of_notMem hn _)
      obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hmem.2
      exact ⟨J, hJ.symm⟩
    rw [← hinj.tsum_eq hsupp, sieveC, ← tsum_mul_left]
    congr 1
    funext J
    have hiff : q * J ∈ D ↔ J ∈ coprimeTo T := by
      rw [hD, Set.mem_ofPred_eq, mul_mem_coprimeTo_iff hp]
      exact ⟨fun h => h.1, fun h => ⟨h, Ideal.mul_le_left⟩⟩
    by_cases hJ : J ∈ coprimeTo T
    · rw [Set.indicator_of_mem (hiff.mpr hJ), Set.indicator_of_mem hJ, hmul]
    · rw [Set.indicator_of_notMem (fun h => hJ (hiff.mp h)), Set.indicator_of_notMem hJ, mul_zero]
  have hsum : sieveC g T = sieveC g (insert p T) + ∑' I, D.indicator g I := by
    rw [sieveC, sieveC, ← Summable.tsum_add (hgs.indicator _) (hgs.indicator _)]
    exact tsum_congr hsplit
  rw [hD_eq] at hsum
  linear_combination (-1 : ℂ) * hsum

theorem sieveC_empty : sieveC g (∅ : Finset (HeightOneSpectrum (𝓞 K))) = ∑' I, g I := by
  unfold sieveC
  congr 1
  funext I
  rw [Set.indicator_of_mem]
  simp [coprimeTo]

theorem sieveC_eq_prod (hs : 1 < s) (hmul : ∀ I J, g (I * J) = g I * g J)
    (hbound : ∀ I, ‖g I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-s)) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    sieveC g T = (∏ p ∈ T, (1 - g p.asIdeal)) * ∑' I, g I := by
  induction T using Finset.induction_on with
  | empty => simp [sieveC_empty]
  | insert p T hp ih => rw [sieveC_insert g hs hmul hbound hp, ih, Finset.prod_insert hp, mul_assoc]

theorem norm_sieveC_sub_one_le (hs : 1 < s) (htop : g ⊤ = 1) (hbot : g ⊥ = 0)
    (hbound : ∀ I, ‖g I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-s)) (X : ℕ)
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hT : primesNormLe K X ⊆ T) :
    ‖sieveC g T - 1‖ ≤ ∑' I, {I : Ideal (𝓞 K) | X < Ideal.absNorm I}.indicator
      (fun I => (Ideal.absNorm I : ℝ) ^ (-s)) I := by
  have hgs : Summable g := summable_of_bound g hs hbound
  have hs0 : -s ≠ 0 := by linarith
  set δ : Ideal (𝓞 K) → ℂ := fun I => if I = ⊤ then 1 else 0 with hδ
  have hδs : Summable δ := summable_of_ne_finset_zero (s := {⊤}) (fun I hI => by
    simp only [Finset.mem_singleton] at hI; simp [hδ, hI])
  have hδsum : ∑' I, δ I = 1 := by simp only [hδ]; rw [tsum_ite_eq]
  have hdiff : sieveC g T - 1 = ∑' I, ((coprimeTo T).indicator g I - δ I) := by
    rw [Summable.tsum_sub (hgs.indicator _) hδs, hδsum]; rfl
  rw [hdiff]
  have hsumT : Summable (fun I : Ideal (𝓞 K) => {I : Ideal (𝓞 K) | X < Ideal.absNorm I}.indicator
      (fun I => (Ideal.absNorm I : ℝ) ^ (-s)) I) :=
    (summable_absNorm_rpow (F := K) hs).indicator _
  refine tsum_of_norm_bounded hsumT.hasSum (fun I => ?_)
  have hnn : 0 ≤ {I : Ideal (𝓞 K) | X < Ideal.absNorm I}.indicator
      (fun I => (Ideal.absNorm I : ℝ) ^ (-s)) I :=
    Set.indicator_nonneg (fun J _ => by positivity) I
  by_cases hI : I ∈ coprimeTo T
  · rw [Set.indicator_of_mem hI]
    by_cases htp : I = ⊤
    · subst htp; simp [hδ, htop]; exact hnn
    · have hδ0 : δ I = 0 := by simp [hδ, htp]
      rw [hδ0, sub_zero]
      by_cases hb : I = ⊥
      · subst hb; rw [hbot, norm_zero]; exact hnn
      · obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I htp
        have hm0 : m ≠ ⊥ := fun h => hb (le_bot_iff.mp (h ▸ hIm))
        set v : HeightOneSpectrum (𝓞 K) := ⟨m, hm.isPrime, hm0⟩
        have hvT : v ∉ T := fun h => hI v h hIm
        have hvX : X < normP v := by
          by_contra hc
          exact hvT (hT (mem_primesNormLe.mpr (not_lt.mp hc)))
        have hI0 : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
        have hle : normP v ≤ Ideal.absNorm I :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero hI0) (Ideal.absNorm_dvd_absNorm_of_le hIm)
        rw [Set.indicator_of_mem (show I ∈ {I : Ideal (𝓞 K) | X < Ideal.absNorm I} from
          lt_of_lt_of_le hvX hle)]
        exact hbound I
  · rw [Set.indicator_of_notMem hI]
    have htp : I ≠ ⊤ := fun h => hI (h ▸ fun v _ h' => v.isPrime.ne_top (top_le_iff.mp h'))
    have hδ0 : δ I = 0 := by simp [hδ, htp]
    rw [hδ0]; simpa using hnn

theorem tendsto_sieveC (hs : 1 < s) (htop : g ⊤ = 1) (hbot : g ⊥ = 0)
    (hbound : ∀ I, ‖g I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-s)) :
    Tendsto (sieveC g) atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨X, hX⟩ := ((tendsto_order.1 (tendsto_tail_absNorm (F := K) s)).2 ε hε).exists
  filter_upwards [eventually_ge_atTop (primesNormLe K X)] with T hT
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (norm_sieveC_sub_one_le g hs htop hbot hbound X hT) hX

/-- **Euler product** for a completely multiplicative function on ideals with $|g(\mathfrak a)| \le N\mathfrak a^{-s}$,
$s > 1$ real: $\sum_\mathfrak a g(\mathfrak a) = \prod_\mathfrak p (1-g(\mathfrak p))^{-1}$, converging unconditionally. -/
theorem hasProd_euler (hs : 1 < s) (hmul : ∀ I J, g (I * J) = g I * g J) (htop : g ⊤ = 1) (hbot : g ⊥ = 0)
    (hbound : ∀ I, ‖g I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-s)) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - g v.asIdeal)⁻¹) (∑' I, g I) := by
  set W := ∑' I, g I with hW
  have ht : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) => (∏ p ∈ T, (1 - g p.asIdeal)) * W) atTop
      (𝓝 1) :=
    (tendsto_sieveC g hs htop hbot hbound).congr fun T => sieveC_eq_prod g hs hmul hbound T
  have hW0 : W ≠ 0 := by
    intro h0
    rw [h0] at ht
    simp only [mul_zero] at ht
    exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds ht)
  have h2 := ht.mul_const W⁻¹
  simp only [mul_assoc, mul_inv_cancel₀ hW0, mul_one, one_mul] at h2
  have h3 : HasProd (fun p : HeightOneSpectrum (𝓞 K) => 1 - g p.asIdeal) W⁻¹ := h2
  have h4 := h3.inv₀ (inv_ne_zero hW0)
  rw [inv_inv] at h4
  exact h4

end Sieve

/-! ## The Weber series as a completely multiplicative ideal series -/

section Weber

open Classical

/-- The term of the Weber $L$-series at an ideal $\mathfrak a$: $\chi(\mathfrak a)N\mathfrak a^{-s}$ if $\mathfrak a \ne 0$
is prime to $\mathfrak m_0$, and $0$ otherwise. -/
def webTerm (m : Modulus K) (χ : RayClassGroup m →* ℂˣ) (s : ℂ) (𝔞 : Ideal (𝓞 K)) : ℂ :=
  if h : 𝔞 ≠ ⊥ ∧ 𝔞 ⊔ m.finite = ⊤ then
    (χ (idealRayClass m 𝔞 h.1 h.2) : ℂ) * ((Ideal.absNorm 𝔞 : ℕ) : ℂ) ^ (-s)
  else 0

theorem weberLSeries_eq_tsum (m : Modulus K) (χ : RayClassGroup m →* ℂˣ) (s : ℂ) :
    weberLSeries m χ s = ∑' 𝔞, webTerm m χ s 𝔞 := rfl

variable (m : Modulus K) (χ : RayClassGroup m →* ℂˣ) (s : ℂ)

theorem webTerm_bot : webTerm m χ s ⊥ = 0 := by simp [webTerm]

theorem webTerm_top : webTerm m χ s ⊤ = 1 := by
  have h : (⊤ : Ideal (𝓞 K)) ≠ ⊥ ∧ (⊤ : Ideal (𝓞 K)) ⊔ m.finite = ⊤ := ⟨top_ne_bot, top_sup_eq _⟩
  rw [webTerm, dif_pos h]
  have : idealRayClass m ⊤ h.1 h.2 = 1 := by
    unfold idealRayClass
    have : (⟨FractionalIdeal.mk0 K ⟨⊤, mem_nonZeroDivisors_of_ne_zero h.1⟩, by
        intro w hw
        rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coe K w h.1]
        have := mt (Associates.count_ne_zero_iff_dvd h.1 w.irreducible).1
          (fun hd => w.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd hd)))
        simpa using this⟩ : coprimeIdeals m) = 1 := by
      apply Subtype.ext
      have h1 : (⟨⊤, mem_nonZeroDivisors_of_ne_zero h.1⟩ : (Ideal (𝓞 K))⁰) = 1 := Subtype.ext Ideal.one_eq_top.symm
      show FractionalIdeal.mk0 K ⟨⊤, mem_nonZeroDivisors_of_ne_zero h.1⟩ = 1
      rw [h1, map_one]
    rw [this]; rfl
  rw [this, map_one, Units.val_one, Ideal.absNorm_top]
  simp

theorem idealRayClass_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIm : I ⊔ m.finite = ⊤)
    (hJm : J ⊔ m.finite = ⊤) (hIJ : I * J ≠ ⊥) (hIJm : I * J ⊔ m.finite = ⊤) :
    idealRayClass m (I * J) hIJ hIJm = idealRayClass m I hI hIm * idealRayClass m J hJ hJm := by
  unfold idealRayClass
  rw [← QuotientGroup.mk_mul]
  refine congrArg QuotientGroup.mk (Subtype.ext ?_)
  show FractionalIdeal.mk0 K ⟨I * J, _⟩ = FractionalIdeal.mk0 K ⟨I, _⟩ * FractionalIdeal.mk0 K ⟨J, _⟩
  rw [← map_mul]
  rfl

theorem webTerm_mul (I J : Ideal (𝓞 K)) : webTerm m χ s (I * J) = webTerm m χ s I * webTerm m χ s J := by
  by_cases hI : I = ⊥
  · subst hI; simp [webTerm_bot]
  by_cases hJ : J = ⊥
  · subst hJ; simp [webTerm_bot]
  have hIJ : I * J ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hI hJ
  by_cases hc : I ⊔ m.finite = ⊤ ∧ J ⊔ m.finite = ⊤
  · have hIJm : I * J ⊔ m.finite = ⊤ :=
      Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr hc.1).mul_left (Ideal.isCoprime_iff_sup_eq.mpr hc.2))
    rw [webTerm, dif_pos ⟨hIJ, hIJm⟩, webTerm, dif_pos ⟨hI, hc.1⟩, webTerm, dif_pos ⟨hJ, hc.2⟩,
      idealRayClass_mul m I J hI hJ hc.1 hc.2 hIJ hIJm, map_mul, Units.val_mul, map_mul, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring
  · have : ¬ (I * J ⊔ m.finite = ⊤) := by
      intro h
      rw [← Ideal.isCoprime_iff_sup_eq] at h
      exact hc ⟨Ideal.isCoprime_iff_sup_eq.mp (h.of_mul_left_left), Ideal.isCoprime_iff_sup_eq.mp h.of_mul_left_right⟩
    rw [webTerm, dif_neg (fun h => this h.2)]
    by_cases h1 : I ⊔ m.finite = ⊤
    · have h2 : ¬ (J ⊔ m.finite = ⊤) := fun h2 => hc ⟨h1, h2⟩
      have hJ0 : webTerm m χ s J = 0 := by rw [webTerm, dif_neg (fun h => h2 h.2)]
      rw [hJ0, mul_zero]
    · have hI0 : webTerm m χ s I = 0 := by rw [webTerm, dif_neg (fun h => h1 h.2)]
      rw [hI0, zero_mul]

theorem norm_eq_one_of_finite (hfin : Finite (RayClassGroup m)) (g : RayClassGroup m) : ‖(χ g : ℂ)‖ = 1 := by
  have hn : Nat.card (RayClassGroup m) ≠ 0 := Nat.card_pos.ne'
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card (RayClassGroup m)) ?_ hn
  have h1 : (χ g) ^ Nat.card (RayClassGroup m) = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have := congrArg (fun z : ℂˣ => (z : ℂ)) h1
  simpa using this

theorem norm_webTerm_le (hfin : Finite (RayClassGroup m)) {σ : ℝ} (hσ : s = σ) (𝔞 : Ideal (𝓞 K)) :
    ‖webTerm m χ s 𝔞‖ ≤ (Ideal.absNorm 𝔞 : ℝ) ^ (-σ) := by
  unfold webTerm
  split_ifs with h
  · have hpos : 0 < Ideal.absNorm 𝔞 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h.1)
    rw [norm_mul, norm_eq_one_of_finite m χ hfin, one_mul, Complex.norm_natCast_cpow_of_pos hpos, hσ]
    simp
  · rw [norm_zero]; positivity

/-- The Weber term at a prime $\mathfrak p \nmid \mathfrak m_0$. -/
theorem webTerm_prime (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) :
    webTerm m χ s v.asIdeal = (χ (rayClass m v hv) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) := by
  have hc : v.asIdeal ⊔ m.finite = ⊤ := by
    by_contra hne
    apply hv
    have : v.asIdeal = v.asIdeal ⊔ m.finite :=
      v.isMaximal.eq_of_le hne le_sup_left
    rw [Ideal.dvd_iff_le]
    rw [this]; exact le_sup_right
  rw [webTerm, dif_pos ⟨v.ne_bot, hc⟩]
  rfl

theorem webTerm_prime_dvd (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ m.finite) :
    webTerm m χ s v.asIdeal = 0 := by
  rw [webTerm, dif_neg]
  rintro ⟨-, h⟩
  have : v.asIdeal ⊔ m.finite = v.asIdeal := sup_eq_left.mpr (Ideal.dvd_iff_le.mp hv)
  rw [this] at h
  exact v.isPrime.ne_top h

/-- **The Euler product of the Weber $L$-series** for real $s > 1$. -/
theorem hasProd_weber (hfin : Finite (RayClassGroup m)) {σ : ℝ} (hσ : 1 < σ) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - webTerm m χ σ v.asIdeal)⁻¹)
      (weberLSeries m χ σ) :=
  hasProd_euler (webTerm m χ (σ : ℂ)) hσ (webTerm_mul m χ σ) (webTerm_top m χ σ) (webTerm_bot m χ σ)
    (norm_webTerm_le m χ σ hfin rfl)

end Weber

/-! ## Comparison with the Hecke $L$-function and the limit at $s = 1$ -/

section Analytic

open Classical

variable (m : Modulus K) (χ : RayClassGroup m →* ℂˣ)

/-- The finitely many primes dividing $\mathfrak m_0$. -/
def badPrimes : Finset (HeightOneSpectrum (𝓞 K)) := (Ideal.finite_factors m.finite_ne_bot).toFinset

theorem mem_badPrimes {v : HeightOneSpectrum (𝓞 K)} : v ∈ badPrimes m ↔ v.asIdeal ∣ m.finite := by
  simp [badPrimes]

/-- For a Hecke character $\Psi$ unramified outside $\mathfrak m_0$ with $\Psi_\mathfrak p(\varpi) =
\chi([\mathfrak p])$, the Weber series and $L(s,\Psi)$ differ by the finitely many Euler factors at $\mathfrak p \mid
\mathfrak m_0$: for real $\sigma > 1$, $L(\sigma,\chi)\prod_{\mathfrak p\mid\mathfrak m_0}L_\mathfrak p(\sigma,\Psi) =
L(\sigma,\Psi)$. -/
theorem weberLSeries_mul_prod_eq_heckeL (hfin : Finite (RayClassGroup m)) (Ψ : HeckeCharacter K)
    (hunit : Ψ.IsUnitary)
    (hloc : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), Ψ.IsUnramifiedAt v ∧
      (Ψ.finiteComponent v (Analysis.ϖU v) : ℂ) = χ (rayClass m v hv))
    {σ : ℝ} (hσ : 1 < σ) :
    weberLSeries m χ σ * ∏ v ∈ badPrimes m, localL Ψ σ v = heckeL Ψ σ := by
  set g := webTerm m χ (σ : ℂ) with hg
  have hbd : ∀ v : HeightOneSpectrum (𝓞 K), ‖g v.asIdeal‖ ≤ 1 / 2 := fun v =>
    (norm_webTerm_le m χ (σ : ℂ) hfin rfl _).trans (rpow_neg_normP_le_half v hσ.le)
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), 1 - g v.asIdeal ≠ 0 := by
    intro v h
    have h1 : g v.asIdeal = 1 := by linear_combination -h
    have := hbd v
    rw [h1, norm_one] at this
    norm_num at this
  have hloc_eq : ∀ v ∉ badPrimes m, localL Ψ σ v = (1 - g v.asIdeal)⁻¹ := by
    intro v hv
    have hv' : ¬ v.asIdeal ∣ m.finite := fun h => hv ((mem_badPrimes m).2 h)
    have hr : rV Ψ σ v = g v.asIdeal := by
      rw [hg, webTerm_prime m χ _ v hv']
      unfold rV
      rw [(hloc v hv').2, Complex.ofReal_natCast]
    rw [localL, if_pos (hloc v hv').1, hr]
  have hshift : Ψ.shift = 0 := (shift_eq_zero_iff Ψ).mpr hunit
  have hP : HasProd (localL Ψ σ) (heckeL Ψ σ) := hasProd_heckeL Ψ (by simp [hshift, hσ])
  set h : HeightOneSpectrum (𝓞 K) → ℂ := fun v => localL Ψ σ v * (1 - g v.asIdeal) with hh_def
  have hh : HasProd h (∏ v ∈ badPrimes m, h v) :=
    hasProd_prod_of_ne_finset_one fun v hv => by
      rw [hh_def]; simp only; rw [hloc_eq v hv]; exact inv_mul_cancel₀ (hne v)
  have hprod := hh.mul (hasProd_weber m χ hfin hσ)
  have hfun : (fun v => h v * (1 - webTerm m χ σ v.asIdeal)⁻¹) = localL Ψ σ := by
    funext v
    simp only [hh_def, hg]
    rw [mul_assoc, mul_inv_cancel₀ (hne v), mul_one]
  rw [hfun] at hprod
  have heq := hP.unique hprod
  have hbad : ∏ v ∈ badPrimes m, h v = ∏ v ∈ badPrimes m, localL Ψ σ v :=
    Finset.prod_congr rfl fun v hv => by
      simp only [hh_def, hg]
      rw [webTerm_prime_dvd m χ _ v ((mem_badPrimes m).1 hv), sub_zero, mul_one]
  rw [heq, hbad]
  ring

/-- **Theorem 7.1 for a character of finite order and a Hecke character attached to it** (the analytic core). -/
theorem weberLOneNeZero_of_hecke (hfin : Finite (RayClassGroup m)) (Ψ : HeckeCharacter K)
    (hunit : Ψ.IsUnitary) (hnp : ∀ c : ℂ, Ψ ≠ HeckeCharacter.normPow K c)
    (hloc : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), Ψ.IsUnramifiedAt v ∧
      (Ψ.finiteComponent v (Analysis.ϖU v) : ℂ) = χ (rayClass m v hv)) :
    Ch6.WeberLOneNeZero m χ := by
  have hshift : Ψ.shift = 0 := (shift_eq_zero_iff Ψ).mpr hunit
  have hlocal_cont : ∀ v : HeightOneSpectrum (𝓞 K), ContinuousAt (fun σ : ℝ => localL Ψ σ v) 1 := by
    intro v
    unfold localL
    by_cases hu : Ψ.IsUnramifiedAt v
    · simp only [hu, if_true]
      have hc : Continuous fun σ : ℝ => rV Ψ (σ : ℂ) v := by
        unfold rV
        exact continuous_const.mul (Continuous.const_cpow (by fun_prop)
          (Or.inl (Complex.ofReal_ne_zero.2 (normV_pos v).ne')))
      exact (continuous_const.sub hc).continuousAt.inv₀
        (one_sub_rV_ne_zero Ψ (by simp [hshift]) v)
    · simp only [hu, if_false]
      exact continuousAt_const
  have hPc : Tendsto (fun σ : ℝ => ∏ v ∈ badPrimes m, localL Ψ σ v) (𝓝 1)
      (𝓝 (∏ v ∈ badPrimes m, localL Ψ ((1 : ℝ) : ℂ) v)) :=
    tendsto_finsetProd _ fun v _ => hlocal_cont v
  have hP0 : (∏ v ∈ badPrimes m, localL Ψ ((1 : ℝ) : ℂ) v) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => localL_ne_zero Ψ (by simp [hshift]) v
  have hAc : Tendsto (fun σ : ℝ => heckeLCont Ψ (σ : ℂ)) (𝓝 1) (𝓝 (heckeLCont Ψ ((1 : ℝ) : ℂ))) :=
    ((differentiable_heckeLCont hnp).continuous.comp Complex.continuous_ofReal).continuousAt
  have hA0 : heckeLCont Ψ ((1 : ℝ) : ℂ) ≠ 0 :=
    heckeLCont_ne_zero_of_re_eq_one hunit hnp (by simp)
  refine ⟨heckeLCont Ψ ((1 : ℝ) : ℂ) / ∏ v ∈ badPrimes m, localL Ψ ((1 : ℝ) : ℂ) v,
    div_ne_zero hA0 hP0, ?_⟩
  refine ((hAc.div hPc hP0).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ' : (1 : ℝ) < σ := hσ
  have hP : (∏ v ∈ badPrimes m, localL Ψ σ v) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => localL_ne_zero Ψ (by simp [hshift]; exact hσ'.le) v
  have key := weberLSeries_mul_prod_eq_heckeL m χ hfin Ψ hunit hloc hσ'
  show heckeLCont Ψ σ / ∏ v ∈ badPrimes m, localL Ψ σ v = _
  rw [heckeLCont_eq Ψ (by simp [hshift, hσ']), ← key]
  field_simp

end Analytic

/-- **Theorem 7.1** (Milne, *CFT*, VIII, Theorem 7.1, p. 258; here unconditional): for every modulus $\mathfrak m$ of
$K$ and every nontrivial character $\chi$ of $C_\mathfrak m$, $L(1,\chi) \ne 0$ (`Ch6.WeberLOneNeZero`). Proved
analytically: the finite-order Hecke character attached to $\chi$ (`exists_heckeChar`) is unitary and not a power of the
norm, hence its $L$-function is entire and nonzero at $1$ (`heckeLCont_ne_zero_of_re_eq_one`); the Weber series differs
from it by finitely many Euler factors (`weberLSeries_mul_prod_eq_heckeL`, from `hasProd_euler`). No reciprocity law is
used. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 7.1, p. 258"]
theorem theorem7_1 (K : Type) [Field K] [NumberField K] : Theorem7_1 K := by
  classical
  refine ⟨fun m χ hχ => ?_⟩
  haveI hfin : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  let ψ : MulChar (RayClassGroup m) ℂ := MulChar.ofUnitHom (χ.comp (toUnits (G := RayClassGroup m)).symm.toMonoidHom)
  have hψ : ∀ g, ψ g = (χ g : ℂ) := by
    intro g
    have : ψ ((toUnits g : (RayClassGroup m)ˣ) : RayClassGroup m) =
        ((χ.comp (toUnits (G := RayClassGroup m)).symm.toMonoidHom) (toUnits g) : ℂˣ) :=
      MulChar.ofUnitHom_coe _ _
    simpa using this
  obtain ⟨Ψ, hpow, hne, hloc⟩ := exists_heckeChar m ψ
  have hn : Nat.card (RayClassGroup m) ≠ 0 := Nat.card_pos.ne'
  have hψne : ψ ≠ 1 := by
    intro h1
    apply hχ
    refine MonoidHom.ext fun g => Units.ext ?_
    rw [← hψ g, h1, MulChar.one_apply (Group.isUnit g)]
    rfl
  exact weberLOneNeZero_of_hecke m χ hfin Ψ (isUnitary_of_pow_eq_one hn hpow)
    (ne_normPow_of_pow_eq_one hn hpow (hne hψne))
    (fun v hv => ⟨(hloc v hv).1, by rw [(hloc v hv).2, hψ]⟩)

end NumberFieldKB.MilneCFT.Ch8
