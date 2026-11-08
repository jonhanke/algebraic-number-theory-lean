import NumberFieldKB.MilneCFT.Ch8.Remark32Field
import NumberFieldKB.MilneCFT.Ch8.Remark32Rational

/-!
# Milne, *Class Field Theory*, Remark VIII.3.2: $25$ is not a norm from $\mathbb Q(\sqrt{13},\sqrt{17})$

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, Remark 3.2,
p. 234 (citing Cassels–Fröhlich, Exercise 5.3).

Let $L = \mathbb Q(s, t)$, $s^2 = 13$, $t^2 = 17$, $K = \mathbb Q(s)$, and suppose $\mathrm N_{L/\mathbb Q}(b) = 25$.
Then $c = \mathrm N_{L/K}(b) = P^2 - 17Q^2$ with $P, Q \in K$ (`exists_norm_eq_iff`) and $\mathrm N_{K/\mathbb Q}(c) =
25$, i.e. $c = c_1 + c_2 s$ with $c_1^2 - 13c_2^2 = 25$ (`R32.norm_add_mul_s`). Explicit Hilbert 90: with
$z = 5 + c$ and $n = \mathrm N_{K/\mathbb Q}(z)$, $c\bar z = 5z$, so $c = 5z^2/n$ and $5n = (Pn/z)^2 - 17(Qn/z)^2$
(if $n = 0$ then $c = -5$ and $n$ is replaced by $-1 = (3/2)^2 - 13(1/2)^2$). Writing $Pn/z, Qn/z \in K$ in terms of
$\gamma = 17s$ with $\gamma^2 = 17 \cdot 221$, `key_E` (Lemma VIII.3.8) gives
$5n = (x^2 - 17y^2)(z^2 - 221w^2)$ over $\mathbb Q$ with $n = m^2 - 13k^2 \ne 0$, which `R32.rational_core` (Hilbert
reciprocity for $(\cdot, 17)$) rules out (`R32.not_exists_norm_eq_25`).
-/

open IntermediateField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.R32

variable {L : Type} [Field L] [NumberField L] {s t : L}

/-- The norm from $\mathbb Q(s)$, $s^2 = 13$: $\mathrm N(x + ys) = x^2 - 13y^2$. -/
theorem norm_add_mul_s (hs : s ^ 2 = 13) (x y : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ ℚ⟮s⟯ x + algebraMap ℚ ℚ⟮s⟯ y * ⟨s, mem_adjoin_simple_self ℚ s⟩) =
      x ^ 2 - 13 * y ^ 2 := by
  set M := ℚ⟮s⟯
  have hδM : s ∈ M := mem_adjoin_simple_self ℚ s
  have hsq : ¬ IsSquare (13 : ℚ) := by
    rintro ⟨r, hr⟩
    exact (rat_sq_ne r).1 (by rw [hr]; ring)
  have hδ : s ^ 2 = algebraMap ℚ L 13 := by rw [hs, map_ofNat]
  have hspan : ∀ m : M, ∃ x y : ℚ, m = algebraMap ℚ M x + algebraMap ℚ M y * ⟨s, hδM⟩ := by
    intro m
    obtain ⟨x, y, h⟩ := exists_eq_add_mul_of_mem_adjoin s 13 hδ m.2
    exact ⟨x, y, Subtype.ext (by simpa using h)⟩
  have hδM1 : (⟨s, hδM⟩ : M) ^ 2 = algebraMap ℚ M 13 := Subtype.ext (by
    simp only [SubmonoidClass.coe_pow, map_ofNat]; rw [hs]; exact (map_ofNat M.val 13).symm)
  have hli : LinearIndependent ℚ ![(1 : M), ⟨s, hδM⟩] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hE : algebraMap ℚ L a + algebraMap ℚ L b * s = 0 := by
      have := congrArg (fun m : M => (m : L)) hab
      simpa [Algebra.smul_def] using this
    have hb : b = 0 := by
      by_contra hb
      apply hsq
      refine ⟨a / b, ?_⟩
      apply (algebraMap ℚ L).injective
      have hb' : algebraMap ℚ L b ≠ 0 := (_root_.map_ne_zero _).mpr hb
      have hse : s = -(algebraMap ℚ L a) / algebraMap ℚ L b := by
        field_simp; linear_combination hE
      rw [← hδ, hse, map_mul, map_div₀]
      field_simp
    subst hb
    simp at hE
    exact ⟨hE, rfl⟩
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range ![(1 : M), ⟨s, hδM⟩]) := by
    intro m _
    obtain ⟨x, y, rfl⟩ := hspan m
    refine Submodule.add_mem _ ?_ ?_
    · have : algebraMap ℚ M x = x • (1 : M) := by simp [Algebra.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · have : algebraMap ℚ M y * ⟨s, hδM⟩ = y • (⟨s, hδM⟩ : M) := by simp [Algebra.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  let b : Module.Basis (Fin 2) ℚ M := Module.Basis.mk hli hsp
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = ⟨s, hδM⟩ := by simp [b]
  rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
  have e0 : (algebraMap ℚ M x + algebraMap ℚ M y * ⟨s, hδM⟩) * b 0 = x • b 0 + y • b 1 := by
    rw [hb0, hb1]; simp [Algebra.smul_def]
  have e1 : (algebraMap ℚ M x + algebraMap ℚ M y * ⟨s, hδM⟩) * b 1 = (y * 13) • b 0 + x • b 1 := by
    rw [hb0, hb1]
    simp only [Algebra.smul_def, map_mul, mul_one]
    linear_combination (algebraMap ℚ M y) * hδM1
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  rw [e0, e1]
  simp
  ring

variable (hs : s ^ 2 = 13) (ht : t ^ 2 = 17) (hgen : adjoin ℚ ({s, t} : Set L) = ⊤)
include hs ht hgen

/-- **Remark VIII.3.2, global half:** $25$ is not a norm from $L = \mathbb Q(\sqrt{13}, \sqrt{17})$. -/
theorem not_exists_norm_eq_25 : ¬ ∃ b : L, Algebra.norm ℚ b = 25 := by
  rintro ⟨b, hb⟩
  set K := ℚ⟮s⟯
  have hsK : s ∈ K := mem_adjoin_simple_self ℚ s
  have htop : adjoin K ({t} : Set L) = ⊤ := by
    apply restrictScalars_injective ℚ
    rw [adjoin_adjoin_left, restrictScalars_top, ← hgen]
    rfl
  -- the norm to `K`
  set c : K := Algebra.norm K b
  have hc : Algebra.norm ℚ c = 25 := by rw [Algebra.norm_norm]; exact hb
  have h2K : (2 : K) ≠ 0 := two_ne_zero
  obtain ⟨p, q, hpq⟩ := (exists_norm_eq_iff h2K t (17 : K) (by norm_num) (by rw [ht, map_ofNat]) ⊤ htop.symm
    c).mp ⟨⟨b, trivial⟩, by rw [← Algebra.norm_eq_of_algEquiv (topEquiv (F := K) (E := L))]; rfl⟩
  -- coordinates of `c`
  obtain ⟨c1, c2, hcc⟩ := exists_eq_add_mul_of_mem_adjoin s 13 (by rw [hs, map_ofNat]) c.2
  have hcK : c = algebraMap ℚ K c1 + algebraMap ℚ K c2 * ⟨s, hsK⟩ := Subtype.ext (by simpa using hcc)
  have hc25 : c1 ^ 2 - 13 * c2 ^ 2 = 25 := by rw [← norm_add_mul_s hs, ← hcK, hc]
  -- in `L`
  have hCL : (c : L) = (p : L) ^ 2 - 17 * (q : L) ^ 2 := by
    have h17 : ((17 : K) : L) = 17 := map_ofNat K.val 17
    rw [← hpq]; push_cast; rw [h17]
  -- the rational `n = m² - 13 k²` with `5 n = P² - 17 Q²`, `P, Q ∈ K`
  have hmain : ∃ m k : ℚ, m ^ 2 - 13 * k ^ 2 ≠ 0 ∧ ∃ P Q : L, P ∈ K ∧ Q ∈ K ∧
      algebraMap ℚ L (5 * (m ^ 2 - 13 * k ^ 2)) = P ^ 2 - 17 * Q ^ 2 := by
    by_cases hn : (5 + c1) ^ 2 - 13 * c2 ^ 2 = 0
    · have hc2 : c2 = 0 := by
        by_contra hc2
        exact (rat_sq_ne (13 * c2 / (5 + c1))).1 (by
          have h5 : 5 + c1 ≠ 0 := by
            intro h5; rw [h5] at hn
            exact hc2 (by nlinarith [sq_nonneg c2])
          rw [div_pow, div_eq_iff (pow_ne_zero 2 h5)]
          linear_combination (-13) * hn)
      have hc1 : c1 = -5 := by
        subst hc2
        have : (5 + c1) ^ 2 = 0 := by linear_combination hn
        have h0 := (pow_eq_zero_iff two_ne_zero).mp this
        linarith
      refine ⟨3 / 2, 1 / 2, by norm_num, p, q, p.2, q.2, ?_⟩
      rw [← hCL, hcc, hc1, hc2]
      simp only [map_mul, map_sub, map_div₀, map_pow, map_ofNat, map_one, map_neg, map_zero]
      ring
    · refine ⟨5 + c1, c2, hn, ?_⟩
      set z : L := algebraMap ℚ L (5 + c1) + algebraMap ℚ L c2 * s
      set zb : L := algebraMap ℚ L (5 + c1) - algebraMap ℚ L c2 * s
      have hzzb : z * zb = algebraMap ℚ L ((5 + c1) ^ 2 - 13 * c2 ^ 2) := by
        simp only [z, zb, map_sub, map_mul, map_pow, map_ofNat]
        linear_combination (-(algebraMap ℚ L c2) ^ 2) * hs
      have hz : z ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hzzb
        exact hn ((map_eq_zero_iff _ (algebraMap ℚ L).injective).mp hzzb.symm)
      have hczb : (c : L) * zb = 5 * z := by
        rw [hcc]
        simp only [z, zb, map_add, map_ofNat]
        have h25 := congrArg (algebraMap ℚ L) hc25
        simp only [map_sub, map_mul, map_pow, map_ofNat] at h25
        linear_combination h25 - (algebraMap ℚ L c2) ^ 2 * hs
      have hzK : z ∈ K := add_mem (IntermediateField.algebraMap_mem _ _) (mul_mem (IntermediateField.algebraMap_mem _ _) hsK)
      set N : L := algebraMap ℚ L ((5 + c1) ^ 2 - 13 * c2 ^ 2)
      refine ⟨(p : L) * N / z, (q : L) * N / z,
        div_mem (mul_mem p.2 (IntermediateField.algebraMap_mem _ _)) hzK, div_mem (mul_mem q.2 (IntermediateField.algebraMap_mem _ _)) hzK, ?_⟩
      have hC : (c : L) * N = 5 * z ^ 2 := by
        rw [← hzzb]; linear_combination z * hczb
      rw [map_mul, map_ofNat]
      have hN : N ≠ 0 := by
        intro h0; exact hn ((map_eq_zero_iff _ (algebraMap ℚ L).injective).mp h0)
      calc (5 : L) * N = 5 * z ^ 2 * N / z ^ 2 := by field_simp
        _ = (c : L) * N * N / z ^ 2 := by rw [hC]
        _ = ((p : L) ^ 2 - 17 * (q : L) ^ 2) * N * N / z ^ 2 := by rw [hCL]
        _ = _ := by field_simp
  obtain ⟨m, k, hmk, P, Q, hP, hQ, hPQ⟩ := hmain
  obtain ⟨P1, P2, hP'⟩ := exists_eq_add_mul_of_mem_adjoin s 13 (by rw [hs, map_ofNat]) hP
  obtain ⟨Q1, Q2, hQ'⟩ := exists_eq_add_mul_of_mem_adjoin s 13 (by rw [hs, map_ofNat]) hQ
  obtain ⟨x, y, z, w, hxyzw⟩ := key_E (k := ℚ) (E := L) (by norm_num) 17 221 (5 * (m ^ 2 - 13 * k ^ 2))
    (by norm_num) (17 * s) (by rw [mul_pow, hs, map_mul, map_ofNat, map_ofNat]; norm_num)
    P1 (P2 / 17) Q1 (Q2 / 17) (by
      rw [hPQ, hP', hQ']
      simp only [map_div₀, map_ofNat]
      field_simp)
  exact rational_core m k x y z w hmk hxyzw.symm

end NumberFieldKB.MilneCFT.Ch8.R32
