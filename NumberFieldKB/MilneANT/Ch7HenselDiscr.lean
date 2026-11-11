import NumberFieldKB.MilneANT.Ch7Hensel
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Milne, *Algebraic Number Theory*, Remark 7.37: the discriminant form from the resultant form

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`, Remark 7.37, p. 123
(Cassels 1986, p. 107).

Milne's Remark 7.37 states the resultant form of Hensel's lemma (`Remark7_37Resultant`) and remarks that the
hypothesis $\lVert f - g_0h_0\rVert < |\operatorname{Res}(g_0,h_0)|^2$ may be replaced by
$\lVert f - g_0h_0\rVert < |\operatorname{disc} f|$ (`Remark7_37Discriminant`). We prove that the second hypothesis
implies the first (`resultant_hyp_of_discr_hyp`), hence the discriminant form follows from the resultant form
(`remark7_37Discriminant_of_resultant`).

Proof of the reduction. Put $F = g_0h_0$, $n = \deg f = r + s$, $d = \operatorname{disc} f$, $J = (d)\mathfrak m$, and
$\rho = \operatorname{Res}(g_0,h_0)$.
* The leading coefficient of $f$ is a unit and $f \equiv F \pmod J$, so $\operatorname{lc}(g_0)\operatorname{lc}(h_0)$
  is a unit. If $r = 0$ or $s = 0$ then $\rho$ is a unit and there is nothing to prove, since $J \subseteq \mathfrak m$.
* Otherwise, the resultant $\operatorname{Res}_{n,n-1}(f, f')$ is a determinant in the coefficients, hence is congruent
  modulo $J$ to $\operatorname{Res}_{n,n-1}(F, F')$ (`resultant_map_map` for $A \to A/J$).
* `Polynomial.resultant_deriv` gives $\operatorname{Res}_{n,n-1}(f,f') = \pm\operatorname{lc}(f)\,d$.
* $\rho^2$ divides $\operatorname{Res}_{n,n-1}(F,F')$ (`resultant_sq_dvd_resultant_mul_derivative`): multiplicativity
  of the resultant, and $F' = g_0'h_0 + g_0h_0'$ reduces modulo $g_0$, resp. $h_0$.
* Hence $d \in (\rho^2) + \mathfrak m (d)$ and Nakayama's lemma gives $d \in (\rho^2)$, so $(d)\mathfrak m \subseteq
  (\rho^2)\mathfrak m$.
-/

open Polynomial IsLocalRing

namespace NumberFieldKB.MilneANT

section general

variable {R : Type*} [CommRing R]

/-- `Res(g, g'h + gh')` is divisible by `Res(g, h)` (sizes `deg g`, `deg g + deg h - 1`), when both
degrees are positive. -/
theorem resultant_dvd_resultant_derivative_aux (g h : R[X]) (hg : 1 ≤ g.natDegree)
    (hh : 1 ≤ h.natDegree) :
    resultant g h ∣ resultant g (derivative g * h + g * derivative h) g.natDegree
      (g.natDegree + h.natDegree - 1) := by
  have h1 := natDegree_derivative_le h
  have h2 := natDegree_derivative_le g
  have hp : (derivative h).natDegree + g.natDegree ≤ g.natDegree + h.natDegree - 1 := by omega
  rw [resultant_add_mul_right g (derivative g * h) (derivative h) _ _
    hp le_rfl]
  obtain ⟨k, hk⟩ : ∃ k, g.natDegree + h.natDegree - 1 =
      ((derivative g).natDegree + h.natDegree) + k :=
    ⟨g.natDegree + h.natDegree - 1 - ((derivative g).natDegree + h.natDegree), by omega⟩
  rw [hk, resultant_add_right_deg _ _ _ _ _ (natDegree_mul_le.trans le_rfl),
    resultant_mul_right g (derivative g) h g.natDegree le_rfl]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left dvd_rfl _) _

/-- `Res(g,h)^2` divides `Res_{n,n-1}(gh, (gh)')` for `n = deg g + deg h`, when both degrees are positive. -/
theorem resultant_sq_dvd_resultant_mul_derivative (g h : R[X]) (hg : 1 ≤ g.natDegree)
    (hh : 1 ≤ h.natDegree) :
    resultant g h ^ 2 ∣ resultant (g * h) (derivative (g * h)) (g.natDegree + h.natDegree)
      (g.natDegree + h.natDegree - 1) := by
  have hle : (derivative (g * h)).natDegree ≤ g.natDegree + h.natDegree - 1 :=
    (natDegree_derivative_le _).trans (by have := natDegree_mul_le (p := g) (q := h); omega)
  rw [resultant_mul_left g h _ _ hle, pow_two]
  apply mul_dvd_mul
  · rw [derivative_mul]
    exact resultant_dvd_resultant_derivative_aux g h hg hh
  · have := resultant_dvd_resultant_derivative_aux h g hh hg
    have e : derivative (g * h) = derivative h * g + h * derivative g := by
      rw [derivative_mul]; ring
    rw [add_comm h.natDegree g.natDegree] at this
    rw [e]
    refine dvd_trans ?_ this
    rw [resultant_comm h g]
    exact Dvd.intro_left _ rfl

end general

/-- **Reduction for Remark 7.37.** Over a discrete valuation ring, the discriminant hypothesis
$\lVert f - g_0h_0\rVert < |\operatorname{disc} f|$ implies the resultant hypothesis
$\lVert f - g_0h_0\rVert < |\operatorname{Res}(g_0,h_0)|^2$ (written with ideals). -/
theorem resultant_hyp_of_discr_hyp {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f g₀ h₀ : A[X]) (hfu : IsUnit f.leadingCoeff) (hdeg : g₀.natDegree + h₀.natDegree = f.natDegree)
    (hyp : ∀ i, (f - g₀ * h₀).coeff i ∈ Ideal.span {f.discr} * IsLocalRing.maximalIdeal A) :
    ∀ i, (f - g₀ * h₀).coeff i ∈ Ideal.span {resultant g₀ h₀ ^ 2} * IsLocalRing.maximalIdeal A := by
  classical
  have finish : Ideal.span {f.discr} ≤ Ideal.span {resultant g₀ h₀ ^ 2} →
      ∀ i, (f - g₀ * h₀).coeff i ∈ Ideal.span {resultant g₀ h₀ ^ 2} * maximalIdeal A :=
    fun h i => Ideal.mul_mono_left h (hyp i)
  have hm : ∀ i, (f - g₀ * h₀).coeff i ∈ maximalIdeal A := fun i => Ideal.mul_le_right (I := Ideal.span {f.discr}) (J := maximalIdeal A) (hyp i)
  have hlc : f.leadingCoeff = (f - g₀ * h₀).coeff (g₀.natDegree + h₀.natDegree) +
      g₀.leadingCoeff * h₀.leadingCoeff := by
    have : f.coeff (g₀.natDegree + h₀.natDegree) = f.leadingCoeff := by rw [hdeg]; rfl
    rw [coeff_sub, coeff_mul_degree_add_degree, this]; ring
  have hunit : IsUnit (g₀.leadingCoeff * h₀.leadingCoeff) := by
    by_contra hn
    have h1 : g₀.leadingCoeff * h₀.leadingCoeff ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; exact hn
    exact (notMem_maximalIdeal.2 hfu) (by
      rw [hlc]; exact add_mem (hm _) h1)
  have hgu : IsUnit g₀.leadingCoeff := isUnit_of_mul_isUnit_left hunit
  have hhu : IsUnit h₀.leadingCoeff := isUnit_of_mul_isUnit_right hunit
  by_cases hr : g₀.natDegree = 0 ∨ h₀.natDegree = 0
  · apply finish
    have hρ : IsUnit (resultant g₀ h₀) := by
      rcases hr with hr | hr
      · have : resultant g₀ h₀ = g₀.coeff 0 ^ h₀.natDegree := by
          show resultant g₀ h₀ g₀.natDegree h₀.natDegree = _
          rw [hr]; exact resultant_zero_left_deg _ _ _
        rw [this]
        refine IsUnit.pow _ ?_
        simpa [leadingCoeff, hr] using hgu
      · have : resultant g₀ h₀ = h₀.coeff 0 ^ g₀.natDegree := by
          show resultant g₀ h₀ g₀.natDegree h₀.natDegree = _
          rw [hr]; exact resultant_zero_right_deg _ _ _
        rw [this]
        refine IsUnit.pow _ ?_
        simpa [leadingCoeff, hr] using hhu
    rw [Ideal.span_singleton_eq_top.2 (hρ.pow 2)]
    exact le_top
  · simp only [not_or] at hr
    apply finish
    have hpos : 0 < f.degree := by
      rw [← natDegree_pos_iff_degree_pos, ← hdeg]; omega
    have hRf := resultant_deriv hpos
    obtain ⟨c, hc⟩ := resultant_sq_dvd_resultant_mul_derivative g₀ h₀ (Nat.one_le_iff_ne_zero.2 hr.1)
      (Nat.one_le_iff_ne_zero.2 hr.2)
    rw [hdeg] at hc
    obtain ⟨J, hJ⟩ : ∃ J : Ideal A, J = Ideal.span {f.discr} * maximalIdeal A := ⟨_, rfl⟩
    rw [← hJ] at hyp
    have hcong : resultant f (derivative f) f.natDegree (f.natDegree - 1) -
        resultant (g₀ * h₀) (derivative (g₀ * h₀)) f.natDegree (f.natDegree - 1) ∈ J := by
      let φ := Ideal.Quotient.mk J
      have hmap : f.map φ = (g₀ * h₀).map φ := by
        ext i
        rw [coeff_map, coeff_map, Ideal.Quotient.eq]
        simpa [coeff_sub] using hyp i
      have e1 := resultant_map_map f (derivative f) f.natDegree (f.natDegree - 1) φ
      have e2 := resultant_map_map (g₀ * h₀) (derivative (g₀ * h₀)) f.natDegree
        (f.natDegree - 1) φ
      rw [← derivative_map, hmap] at e1
      rw [← derivative_map] at e2
      exact Ideal.Quotient.eq.1 (e1.symm.trans e2)
    obtain ⟨u, hu⟩ : ∃ u : A, u = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff := ⟨_, rfl⟩
    have huu : IsUnit u := hu ▸ (IsUnit.pow _ isUnit_one.neg).mul hfu
    have h1 : u * f.discr ∈ Ideal.span {resultant g₀ h₀ ^ 2} ⊔ maximalIdeal A * Ideal.span {f.discr} := by
      have e : u * f.discr = resultant g₀ h₀ ^ 2 * c +
          (resultant f (derivative f) f.natDegree (f.natDegree - 1) -
            resultant (g₀ * h₀) (derivative (g₀ * h₀)) f.natDegree (f.natDegree - 1)) := by
        rw [hu, hRf, hc]; ring
      rw [e]
      refine Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) ?_
      rw [mul_comm, ← hJ]; exact hcong
    have h2 : f.discr ∈ Ideal.span {resultant g₀ h₀ ^ 2} ⊔ maximalIdeal A * Ideal.span {f.discr} := by
      have := Ideal.mul_mem_left _ (↑huu.unit⁻¹ : A) h1
      simpa [← mul_assoc] using this
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) ⟨{f.discr}, by simp⟩
      (jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top).ge ?_
    rw [Ideal.span_singleton_le_iff_mem]
    simpa [Ideal.smul_eq_mul] using h2

/-- **Remark 7.37, discriminant form from the resultant form** (Milne, citing Cassels 1986, p. 107). -/
@[kb "milne2020ant" "v3.08, Remark 7.37, p. 123"]
theorem remark7_37Discriminant_of_resultant (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A] (h : Remark7_37Resultant A) :
    Remark7_37Discriminant A :=
  ⟨fun f g₀ h₀ hfu hdeg hyp =>
    h.factors f g₀ h₀ hfu hdeg (resultant_hyp_of_discr_hyp f g₀ h₀ hfu hdeg hyp)⟩

end NumberFieldKB.MilneANT
