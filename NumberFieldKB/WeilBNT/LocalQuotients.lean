import NumberFieldKB.WeilBNT.IntegersDense
import QuadFormsKB.LocalDensity.NFBridge

/-!
# Weil, *Basic Number Theory*, V.§3, Theorem 4 and corollaries, for ideals

$k$ is a number field, $\mathfrak r$ its ring of integers, $r_v$ the ring of integers of $k_v$ at a finite place $v$.
For a nonzero integral ideal $\mathfrak a$ (Weil's lattices $L=\mathfrak r\supseteq M=\mathfrak a$ in $E=k$), its local
component is $\mathfrak a_v=\mathfrak a\,r_v$ (`Ideal.map` along $\mathfrak r\to r_v$).

* **`weil_V_3_thm4`** (Weil, Thm. 4, p. 87, case $E=k$, $L=\mathfrak r$): the diagonal map
  $\mathfrak r\to\prod_vr_v/\mathfrak a_v$ (`localQuotientsHom`) is surjective with kernel $\mathfrak a$, so
  $\mathfrak r/\mathfrak a\cong\prod_vr_v/\mathfrak a_v$ (`weil_V_3_thm4_equiv`); all but finitely many factors are $0$;
* **`weil_V_3_cor1`** (Cor. 1, p. 88): $[\mathfrak r:\mathfrak a]=\prod_v[r_v:\mathfrak a_v]$, almost all factors $1$;
* **`weil_V_3_cor2`** (Cor. 2, p. 88): $\mathfrak r/\mathfrak p_v\cong r_v/p_v$ (residue fields agree).
-/

open IsDedekindDomain NumberField Filter Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

variable (K) in
/-- The local component $\mathfrak a_v=\mathfrak a\,r_v$ of an ideal $\mathfrak a$ of $\mathfrak r$. -/
abbrev localIdeal (𝔞 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : Ideal (v.adicCompletionIntegers K) :=
  𝔞.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))

variable (K) in
/-- The diagonal map $\mathfrak r\to\prod_v r_v/\mathfrak a_v$. -/
def localQuotientsHom (𝔞 : Ideal (𝓞 K)) :
    𝓞 K →+* ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K ⧸ localIdeal K 𝔞 v :=
  RingHom.pi fun v => (Ideal.Quotient.mk (localIdeal K 𝔞 v)).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))

open QuadFormsKB.LocalDensity.NF in
/-- **Weil, V.§3, Thm. 4**: almost all local factors are $0$: $\mathfrak a_v=r_v$ for $v\nmid\mathfrak a$. -/
theorem localIdeal_eq_top_of_not_le (𝔞 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ 𝔞 ≤ v.asIdeal) :
    localIdeal K 𝔞 v = ⊤ := by
  obtain ⟨a, ha, hav⟩ := Set.not_subset.mp hv
  have h1 : ι v a ∉ Ideal.span {π v ^ 1} := by
    rw [ι_mem_span_π_pow, pow_one]; exact hav
  have hu : IsUnit (ι v a) := by
    by_contra h
    apply h1
    rw [pow_one, ← (irreducible_π v).maximalIdeal_eq]
    exact h
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha) hu

/-- The exponent of `v` in `𝔞`. -/
abbrev expo (𝔞 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔞).factors

open QuadFormsKB.LocalDensity.NF in
/-- Local component of `𝔞` at `v` is `(π^e)` with `e` the exponent of `v` in `𝔞`. -/
theorem localIdeal_eq_span (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    localIdeal K 𝔞 v = Ideal.span {π v ^ expo 𝔞 v} := by
  have hle : 𝔞 ≤ v.asIdeal ^ expo 𝔞 v := by
    have := iInf_le (fun w : HeightOneSpectrum (𝓞 K) => w.maxPowDividing 𝔞) v
    rw [Ideal.iInf_maxPowDividing_eq h𝔞] at this
    exact this
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ι_mem_span_π_pow]
    exact hle hx
  · have hnd : ¬ 𝔞 ≤ v.asIdeal ^ (expo 𝔞 v + 1) := by
      intro h
      apply Ideal.finprod_not_dvd v 𝔞 h𝔞
      rw [Ideal.finprod_heightOneSpectrum_factorization h𝔞]
      exact Ideal.dvd_iff_le.mpr h
    obtain ⟨a, ha, hna⟩ := Set.not_subset.mp hnd
    have hna : a ∉ v.asIdeal ^ (expo 𝔞 v + 1) := hna
    have h1 : ι v a ∈ Ideal.span {π v ^ expo 𝔞 v} := (ι_mem_span_π_pow v _ a).mpr (hle ha)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h1
    have hcu : IsUnit c := by
      by_contra h
      apply hna
      rw [← ι_mem_span_π_pow, hc, Ideal.mem_span_singleton, pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [← Ideal.mem_span_singleton, ← pow_one (π v), ← Ideal.span_singleton_pow,
        ← (irreducible_π v).maximalIdeal_eq]
      rw [pow_one]
      exact (IsLocalRing.mem_maximalIdeal c).mpr h
    have : π v ^ expo 𝔞 v = ι v a * ↑hcu.unit⁻¹ := by
      rw [hc, mul_assoc]; simp
    rw [Ideal.span_singleton_le_iff_mem, this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

open QuadFormsKB.LocalDensity.NF in
/-- Every class in `𝔬 / 𝔞_v` is hit by some global integer. -/
theorem exists_ι_sub_mem (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K))
    (w : v.adicCompletionIntegers K) : ∃ x : 𝓞 K, ι v x - w ∈ localIdeal K 𝔞 v := by
  obtain ⟨x, hx⟩ := redHom_surjective v (expo 𝔞 v) (Ideal.Quotient.mk _ w)
  refine ⟨x, ?_⟩
  rw [localIdeal_eq_span 𝔞 h𝔞, ← Ideal.Quotient.eq]
  exact hx

open QuadFormsKB.LocalDensity.NF in
/-- **Weil, V.§3, Thm. 4** (p. 87), for $E=k$, $L=\mathfrak r$, $M=\mathfrak a\ne0$: $\mathfrak r\to\prod_vr_v/\mathfrak a_v$
has kernel $\mathfrak a$ and is surjective. -/
@[kb "weil1973bnt" "Ch. V, §3, Thm. 4 (p. 87), case E = k, L = ring of integers"]
theorem weil_V_3_thm4 (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    RingHom.ker (localQuotientsHom K 𝔞) = 𝔞 ∧ Function.Surjective (localQuotientsHom K 𝔞) := by
  constructor
  · ext a
    have : a ∈ 𝔞 ↔ ∀ v : HeightOneSpectrum (𝓞 K), a ∈ v.maxPowDividing 𝔞 := by
      conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq h𝔞]
      rw [Submodule.mem_iInf]
    rw [this, RingHom.mem_ker]
    simp only [localQuotientsHom, funext_iff, RingHom.pi_apply, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem, Pi.zero_apply]
    refine forall_congr' fun v => ?_
    rw [localIdeal_eq_span 𝔞 h𝔞, ι_mem_span_π_pow]
    rfl
  · intro y
    classical
    have hx : ∀ v, ∃ x : 𝓞 K, ι v x - (y v).out ∈ localIdeal K 𝔞 v :=
      fun v => exists_ι_sub_mem 𝔞 h𝔞 v _
    choose x hx using hx
    set s := (Ideal.finite_factors h𝔞).toFinset with hs
    obtain ⟨z, hz⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
      (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) (fun v => expo 𝔞 v)
      (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
      (fun i _ j _ h h' => h (HeightOneSpectrum.ext h')) (fun i => x i.1)
    refine ⟨z, funext fun v => ?_⟩
    simp only [localQuotientsHom, RingHom.pi_apply, RingHom.comp_apply]
    by_cases hv : v ∈ s
    · rw [← Quotient.out_eq (y v)]
      change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      rw [Ideal.Quotient.eq]
      have h1 : ι v z - ι v (x v) ∈ localIdeal K 𝔞 v := by
        rw [localIdeal_eq_span 𝔞 h𝔞, ← map_sub, ι_mem_span_π_pow]
        exact hz v hv
      have := Ideal.add_mem _ h1 (hx v)
      convert this using 1
      ring
    · have hnle : ¬ 𝔞 ≤ v.asIdeal := by
        intro h
        apply hv
        rw [hs, Set.Finite.mem_toFinset]
        exact Ideal.dvd_iff_le.mpr h
      have := localIdeal_eq_top_of_not_le 𝔞 v hnle
      have hsub : Subsingleton (v.adicCompletionIntegers K ⧸ localIdeal K 𝔞 v) :=
        Ideal.Quotient.subsingleton_iff.mpr this
      exact Subsingleton.elim _ _

/-- **Weil, V.§3, Thm. 4**, as an isomorphism $\mathfrak r/\mathfrak a\cong\prod_vr_v/\mathfrak a_v$. -/
def weil_V_3_thm4_equiv (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    𝓞 K ⧸ 𝔞 ≃+* ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K ⧸ localIdeal K 𝔞 v :=
  (Ideal.quotEquivOfEq (weil_V_3_thm4 𝔞 h𝔞).1.symm).trans
    (RingHom.quotientKerEquivOfSurjective (weil_V_3_thm4 𝔞 h𝔞).2)

open QuadFormsKB.LocalDensity.NF in
/-- **Weil, V.§3, Cor. 1 of Thm. 4** (p. 88): $[\mathfrak r:\mathfrak a]=\prod_v[r_v:\mathfrak a_v]$, with almost all
factors equal to $1$. -/
@[kb "weil1973bnt" "Ch. V, §3, Cor. 1 of Thm. 4 (p. 88), case E = k, L = ring of integers"]
theorem weil_V_3_cor1 (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    (Set.Finite {v : HeightOneSpectrum (𝓞 K) | Nat.card (v.adicCompletionIntegers K ⧸ localIdeal K 𝔞 v) ≠ 1}) ∧
      Ideal.absNorm 𝔞 = ∏ᶠ v : HeightOneSpectrum (𝓞 K), Nat.card (v.adicCompletionIntegers K ⧸ localIdeal K 𝔞 v) := by
  classical
  have hcard : ∀ v : HeightOneSpectrum (𝓞 K),
      Nat.card (v.adicCompletionIntegers K ⧸ localIdeal K 𝔞 v) = Ideal.absNorm (v.maxPowDividing 𝔞) := by
    intro v
    rw [localIdeal_eq_span 𝔞 h𝔞, card_quot_π_pow, HeightOneSpectrum.maxPowDividing, map_pow]
  have hsub : {v : HeightOneSpectrum (𝓞 K) | v.maxPowDividing 𝔞 ≠ 1} ⊆
      {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔞} := by
    intro v hv
    have : expo 𝔞 v ≠ 0 := fun h => hv (by simp [HeightOneSpectrum.maxPowDividing, h])
    exact (Associates.count_ne_zero_iff_dvd h𝔞 v.irreducible).mp this
  have hfin := (Ideal.finite_factors h𝔞).subset hsub
  have hone : ∀ v, Nat.card (v.adicCompletionIntegers K ⧸ localIdeal K 𝔞 v) ≠ 1 ↔
      v.maxPowDividing 𝔞 ≠ 1 := by
    intro v
    rw [hcard]
    refine not_congr ⟨fun h => ?_, fun h => by rw [h]; simp⟩
    have : Ideal.absNorm (v.maxPowDividing 𝔞) = 1 := h
    rw [Ideal.absNorm_eq_one_iff] at this
    rw [this, Ideal.one_eq_top]
  refine ⟨?_, ?_⟩
  · simpa only [hone] using hfin
  · simp only [hcard]
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization h𝔞]
    have hms : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing 𝔞) ⊆ hfin.toFinset := by
      intro v hv; simpa using hv
    have hms' : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm (v.maxPowDividing 𝔞)) ⊆ hfin.toFinset := by
      intro v hv
      simp only [Function.mem_mulSupport] at hv
      simp only [Set.Finite.coe_toFinset]
      intro h; apply hv; rw [h]; simp
    rw [finprod_eq_prod_of_mulSupport_subset _ hms, finprod_eq_prod_of_mulSupport_subset _ hms', map_prod]

/-- **Weil, V.§3, Cor. 2 of Thm. 4** (p. 88): $\mathfrak r/\mathfrak p_v\cong r_v/p_v$, the map being induced by
$\mathfrak r\to r_v$. -/
@[kb "weil1973bnt" "Ch. V, §3, Cor. 2 of Thm. 4 (p. 88)"]
theorem weil_V_3_cor2 (v : HeightOneSpectrum (𝓞 K)) :
    ∃ e : 𝓞 K ⧸ v.asIdeal ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K),
      ∀ a : 𝓞 K, e (Ideal.Quotient.mk _ a) =
        IsLocalRing.residue _ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) := by
  have h1 : Ideal.span {QuadFormsKB.LocalDensity.NF.π v ^ 1} = IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [pow_one]; exact (QuadFormsKB.LocalDensity.NF.irreducible_π v).maximalIdeal_eq.symm
  refine ⟨((Ideal.quotEquivOfEq (pow_one v.asIdeal).symm).trans
    ((QuadFormsKB.LocalDensity.NF.quotEquiv v 1).trans (Ideal.quotEquivOfEq h1))), fun a => ?_⟩
  rfl

end NumberFieldKB.WeilBNT

end
