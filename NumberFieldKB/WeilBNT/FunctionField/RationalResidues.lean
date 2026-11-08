import NumberFieldKB.WeilBNT.FunctionField.RationalPlaces

/-!
# Weil, *Basic Number Theory*, III.§1, Corollary of Theorem 2: residues at a finite place of $\mathbb F_q(T)$

Let $\pi\in\mathbb F_q[T]$ be irreducible of degree $b$ and $v$ the place of $k=\mathbb F_q(T)$ attached to $\pi$
(`placeAt π hπ`, the $\pi$-adic valuation of Mathlib's `HeightOneSpectrum` of $\mathbb F_q[T]$). Weil's $r_v$ is the
ring of integers of the completion $k_v$ and $P_v$ its maximal ideal, $\{x:\lvert x\rvert_v<1\}$.

* **`weil_III_1_cor_thm2`**: the polynomials of degree $<b$ form a full set of representatives of $r_v$ modulo $P_v$:
  every $x\in k_v$ with $\lvert x\rvert_v\le1$ is congruent modulo $P_v$ to one and only one polynomial $f$ with
  $\deg f<\deg\pi$.

*Proof* (Weil's): $k$ is dense in $k_v$, so $x$ is congruent to some $\xi\in k\cap r_v$, and $\xi=\alpha/\beta$ with
$\beta$ prime to $\pi$; the polynomials of degree $<b$ represent $\mathbb F_q[T]/\pi$, and $\beta$ is invertible
modulo $\pi$. Two such polynomials congruent modulo $P_v$ differ by a multiple of $\pi$ of degree $<b$, hence are equal.
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq : Type*} [Field Fq] [Finite Fq]

/-- The height-one prime $(\pi)$ of $\mathbb F_q[T]$ for an irreducible $\pi$. -/
def primeAt (π : Fq[X]) (hπ : Irreducible π) : HeightOneSpectrum Fq[X] where
  asIdeal := Ideal.span {π}
  isPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ.prime
  ne_bot := by simpa using hπ.ne_zero

/-- The place of $\mathbb F_q(T)$ attached to an irreducible polynomial $\pi$ (Weil III.§1, Thm. 2). -/
abbrev placeAt (π : Fq[X]) (hπ : Irreducible π) : Place Fq (RatFunc Fq) :=
  Place.ofHeightOneSpectrum (Fq := Fq) (k := RatFunc Fq) Fq[X] (primeAt π hπ)

/-- For `g : Fq[X]`, the valuation of `placeAt π hπ` at `g` is `< 1` iff `π ∣ g`. -/
theorem placeAt_valuation_lt_one_iff (π : Fq[X]) (hπ : Irreducible π) (g : Fq[X]) :
    (placeAt π hπ).valuation (algebraMap Fq[X] (RatFunc Fq) g) < 1 ↔ π ∣ g := by
  rw [placeAt, Place.ofHeightOneSpectrum_valuation, (primeAt π hπ).valuation_lt_one_iff_mem]
  show g ∈ Ideal.span {π} ↔ _
  exact Ideal.mem_span_singleton

/-- An element of `Fq(X)` of `π`-adic valuation `≤ 1` is `a / b` with `π ∤ b`. -/
theorem exists_num_den_of_valuation_le_one (π : Fq[X]) (hπ : Irreducible π) (ξ : RatFunc Fq)
    (hξ : (placeAt π hπ).valuation ξ ≤ 1) :
    ∃ a b : Fq[X], ¬ π ∣ b ∧ ξ = algebraMap Fq[X] (RatFunc Fq) a / algebraMap Fq[X] (RatFunc Fq) b := by
  refine ⟨ξ.num, ξ.denom, ?_, (RatFunc.num_div_denom ξ).symm⟩
  intro hd
  have hcop := RatFunc.isCoprime_num_denom ξ
  have hnum : ¬ π ∣ ξ.num := fun hn => hπ.not_isUnit (hcop.isUnit_of_dvd' hn hd)
  have h1 : (placeAt π hπ).valuation (algebraMap Fq[X] (RatFunc Fq) ξ.num) = 1 := by
    refine le_antisymm ((primeAt π hπ).valuation_le_one _) (not_lt.1 ?_)
    rw [placeAt_valuation_lt_one_iff]; exact hnum
  have h2 := (placeAt_valuation_lt_one_iff π hπ ξ.denom).2 hd
  have hden0 : algebraMap Fq[X] (RatFunc Fq) ξ.denom ≠ 0 := by
    simpa using ξ.denom_ne_zero
  have hv0 : (placeAt π hπ).valuation (algebraMap Fq[X] (RatFunc Fq) ξ.denom) ≠ 0 := by
    simpa using hden0
  have : (placeAt π hπ).valuation ξ =
      1 / (placeAt π hπ).valuation (algebraMap Fq[X] (RatFunc Fq) ξ.denom) := by
    conv_lhs => rw [← RatFunc.num_div_denom ξ]
    rw [map_div₀, h1]
  rw [this] at hξ
  rw [div_le_one₀ (zero_lt_iff.2 hv0)] at hξ
  exact absurd h2 (not_lt.2 hξ)

/-- **Weil, III.§1, Corollary of Theorem 2.** At the place $v$ of $\mathbb F_q(T)$ given by an irreducible
polynomial $\pi$, the polynomials of degree $<\deg\pi$ form a full set of representatives of $r_v$ modulo $P_v$. -/
@[kb "weil1973bnt" "Ch. III, §1, Cor. of Thm. 2 (p. 47), polynomials of degree < deg π represent r_v / P_v"]
theorem weil_III_1_cor_thm2 (π : Fq[X]) (hπ : Irreducible π) (x : (placeAt π hπ).Completion)
    (hx : Valued.v x ≤ 1) :
    ∃! f : Fq[X], f.degree < π.degree ∧
      Valued.v (x - (placeAt π hπ).toCompletion (algebraMap Fq[X] (RatFunc Fq) f)) < 1 := by
  classical
  have hnhds : {z : (placeAt π hπ).Completion | Valued.v (z - x) < 1} ∈ nhds x :=
    Valued.mem_nhds.2 ⟨1, fun z hz => by simpa [Valuation.restrict_lt_iff] using hz⟩
  obtain ⟨a0, ha0⟩ := (UniformSpace.Completion.denseRange_coe
    (α := WithVal (placeAt π hπ).valuation)).mem_nhds hnhds
  set ξ : RatFunc Fq := WithVal.equiv (placeAt π hπ).valuation a0 with hξdef
  have hxa : (placeAt π hπ).toCompletion ξ = (a0 : (placeAt π hπ).Completion) := rfl
  have hlt : Valued.v ((placeAt π hπ).toCompletion ξ - x) < 1 := by rw [hxa]; exact ha0
  have hξ : (placeAt π hπ).valuation ξ ≤ 1 := by
    rw [← Place.valued_toCompletion]
    have : (placeAt π hπ).toCompletion ξ = ((placeAt π hπ).toCompletion ξ - x) + x := by ring
    rw [this]
    exact (Valuation.map_add_le_max' _ _ _).trans (max_le hlt.le hx)
  obtain ⟨a, b, hb, hab⟩ := exists_num_den_of_valuation_le_one π hπ ξ hξ
  have hcop : IsCoprime π b := (Irreducible.coprime_iff_not_dvd hπ).2 hb
  obtain ⟨u, w, huw⟩ := hcop
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hb0 : algebraMap Fq[X] (RatFunc Fq) b ≠ 0 := by
    intro h
    have := (map_eq_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).1 h
    exact hb (this ▸ dvd_zero π)
  have hbv : (placeAt π hπ).valuation (algebraMap Fq[X] (RatFunc Fq) b) = 1 :=
    RationalFF.valuation_ofHeightOneSpectrum_eq_one (primeAt π hπ) b (by
      show b ∉ Ideal.span {π}
      rw [Ideal.mem_span_singleton]; exact hb)
  have uniq : ∀ f g : Fq[X], f.degree < π.degree → g.degree < π.degree →
      Valued.v (x - (placeAt π hπ).toCompletion (algebraMap Fq[X] (RatFunc Fq) f)) < 1 →
      Valued.v (x - (placeAt π hπ).toCompletion (algebraMap Fq[X] (RatFunc Fq) g)) < 1 → g = f := by
    intro f g hf hg hxf hxg
    have h : Valued.v ((placeAt π hπ).toCompletion (algebraMap Fq[X] (RatFunc Fq) (f - g))) < 1 := by
      have e : (placeAt π hπ).toCompletion (algebraMap Fq[X] (RatFunc Fq) (f - g)) =
          (x - (placeAt π hπ).toCompletion (algebraMap Fq[X] (RatFunc Fq) g)) -
            (x - (placeAt π hπ).toCompletion (algebraMap Fq[X] (RatFunc Fq) f)) := by
        simp only [map_sub]; ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hxg hxf)
    have h' := (placeAt_valuation_lt_one_iff π hπ (f - g)).1
      (lt_of_eq_of_lt (Place.valued_toCompletion _ _).symm h)
    have hd : (f - g).degree < π.degree := (degree_sub_le f g).trans_lt (max_lt hf hg)
    have := eq_zero_of_dvd_of_degree_lt h' hd
    exact (sub_eq_zero.1 this).symm
  have hex : ∃ f : Fq[X], f.degree < π.degree ∧
      Valued.v (x - (placeAt π hπ).toCompletion (algebraMap Fq[X] (RatFunc Fq) f)) < 1 := by
    refine ⟨(a * w) % π, ?_, ?_⟩
    · exact EuclideanDomain.mod_lt _ hπ0
    · have hdvd : π ∣ a - b * ((a * w) % π) := by
        have hq := EuclideanDomain.div_add_mod (a * w) π
        refine ⟨a * u + b * (a * w / π), ?_⟩
        have e : a = a * (u * π + w * b) := by rw [huw]; ring
        linear_combination e - b * hq
      have h1 : (placeAt π hπ).valuation (algebraMap Fq[X] (RatFunc Fq) (a - b * ((a * w) % π))) < 1 :=
        (placeAt_valuation_lt_one_iff π hπ _).2 hdvd
      have h2 : (placeAt π hπ).valuation (ξ - algebraMap Fq[X] (RatFunc Fq) ((a * w) % π)) < 1 := by
        have : ξ - algebraMap Fq[X] (RatFunc Fq) ((a * w) % π) =
            algebraMap Fq[X] (RatFunc Fq) (a - b * ((a * w) % π)) /
              algebraMap Fq[X] (RatFunc Fq) b := by
          rw [hab]; simp only [map_sub, map_mul]; field_simp
        rw [this, map_div₀, hbv, div_one]; exact h1
      have e : x - (placeAt π hπ).toCompletion (algebraMap Fq[X] (RatFunc Fq) ((a * w) % π)) =
          (x - (placeAt π hπ).toCompletion ξ) +
            (placeAt π hπ).toCompletion (ξ - algebraMap Fq[X] (RatFunc Fq) ((a * w) % π)) := by
        rw [map_sub]; ring
      rw [e]
      refine lt_of_le_of_lt (Valuation.map_add_le_max' _ _ _) (max_lt ?_ ?_)
      · exact lt_of_eq_of_lt (Valuation.map_sub_swap Valued.v _ _) hlt
      · exact lt_of_eq_of_lt (Place.valued_toCompletion _ _) h2
  obtain ⟨f, hf⟩ := hex
  exact ⟨f, hf, fun g hg => uniq f g hf.1 hg.1 hf.2 hg.2⟩

end NumberFieldKB.WeilBNT.FF
