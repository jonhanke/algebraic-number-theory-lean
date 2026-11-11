import Mathlib.MeasureTheory.Group.FundamentalDomain
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, Chapter V, §4, text p. 89: fundamental sets of order $\nu$

Weil (p. 89): let $\Gamma$ be a discrete subgroup of a locally compact group $G$ and $\alpha$ a Haar measure. A measurable
set $X$ which is a full set of representatives of the cosets modulo $\Gamma$ has $\alpha(X)=\alpha(G/\Gamma)$ (formula (6) of
II.§4 applied to the characteristic function of $X$); more generally, if $X$ is *fundamental of order $\nu$*, i.e. has
exactly $\nu$ points in common with every coset modulo $\Gamma$, then $\alpha(X)=\nu\,\alpha(G/\Gamma)$.

Formalization (a slight generalization): $\Gamma$ is any countable group acting measurably on a measurable space $G$ and
preserving the measure $\mu$ (for a discrete subgroup of a second-countable group acting by translations this is
Weil's situation, and the action is free, so counting the $\gamma$ with $\gamma g\in X$ counts the points of
$\Gamma g\cap X$). The covolume $\alpha(G/\Gamma)$ is $\mu(D)$ for a fundamental domain $D$ (Mathlib's
`IsFundamentalDomain`, which exists for discrete subgroups of second-countable groups, QuadFormsKB
`exists_isFundamentalDomain`).

* **`weil_V_4_text89`**: if $\#\{\gamma\in\Gamma:\gamma g\in X\}=\nu$ for every $g$, then $\mu(X)=\nu\,\mu(D)$.

Proof: $\mu(X)=\sum_\gamma\mu(X\cap\gamma D)=\int_D\#\{\gamma:\gamma x\in X\}\,d\mu=\nu\,\mu(D)$ (Mathlib's
`IsFundamentalDomain.lintegral_eq_tsum` family), the unfolding Weil's formula (6) expresses.
-/

open MeasureTheory

namespace NumberFieldKB.WeilBNT

variable {G Γ : Type*} [Group Γ] [Countable Γ] [MeasurableSpace G] [MulAction Γ G] [MeasurableConstSMul Γ G]
  {μ : Measure G} [SMulInvariantMeasure Γ G μ]

/-- **Weil, V.§4, text p. 89**: a measurable set $X$ meeting every orbit $\Gamma g$ in exactly $\nu$ points (counted as
the $\gamma$ with $\gamma g\in X$) has measure $\nu$ times the covolume $\mu(D)$, $D$ any fundamental domain. -/
@[kb "weil1973bnt" "Ch. V, §4, text p. 89 (fundamental sets of order ν)"]
theorem weil_V_4_text89 {D X : Set G} (hD : IsFundamentalDomain Γ D μ) (hX : MeasurableSet X) (ν : ℕ)
    (hν : ∀ g : G, {γ : Γ | γ • g ∈ X}.encard = ν) : μ X = ν * μ D := by
  have h1 : μ X = ∫⁻ x, X.indicator (1 : G → ENNReal) x ∂μ := by
    rw [lintegral_indicator_one hX]
  have h2 : ∀ x : G, ∑' γ : Γ, X.indicator (1 : G → ENNReal) (γ • x) = (ν : ENNReal) := by
    intro x
    have : ∀ γ : Γ, X.indicator (1 : G → ENNReal) (γ • x) = {γ : Γ | γ • x ∈ X}.indicator 1 γ := by
      intro γ
      by_cases h : γ • x ∈ X <;> simp [Set.indicator, h]
    simp_rw [this]
    have h3 := tsum_subtype {γ : Γ | γ • x ∈ X} (fun _ => (1 : ENNReal))
    rw [ENNReal.tsum_set_one, hν x] at h3
    exact h3.symm
  rw [h1, hD.lintegral_eq_tsum'', ← lintegral_tsum]
  · simp_rw [h2]
    rw [setLIntegral_const, mul_comm]
  · intro γ
    exact ((measurable_one.indicator hX).comp (measurable_const_smul γ)).aemeasurable

end NumberFieldKB.WeilBNT
