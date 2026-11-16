import NumberFieldKB.MilneEC.Ch1BezoutCRT
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The nine-point lemma: local facts

Part of the proof of Milne, *Elliptic Curves*, Proposition I.3.2, from Bezout's theorem.

* `numAt_pos`: at a common zero, the local intersection number is positive (when $K[X,Y]/(f,g)$ is finite
  dimensional).
* `mk_eq_zero_of_numAt_eq_one`: where the intersection is transversal ($\dim \mathcal O_p/(f,g) = 1$),
  every polynomial vanishing at `p` is zero in $\mathcal O_p/(f, g)$.
* `gradient_ne_zero_of_numAt_eq_one`: where the intersection is transversal, one of the two curves is
  nonsingular at `p`.
* `infinite_zeros_of_isHomogeneous`: over an algebraically closed field a form of positive degree has
  infinitely many zeros in the projective plane.
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

theorem span_pair_ne_top (a b : Fin 3 → K) : Submodule.span K ({a, b} : Set (Fin 3 → K)) ≠ ⊤ := by
  classical
  intro h
  have h1 := finrank_span_finset_le_card (R := K) ({a, b} : Finset (Fin 3 → K))
  have h2 : ({a, b} : Finset (Fin 3 → K)).card ≤ 2 := Finset.card_le_two
  have h3 : (↑({a, b} : Finset (Fin 3 → K)) : Set (Fin 3 → K)) = {a, b} := by simp
  rw [Set.finrank, h3, h] at h1
  rw [finrank_top, Module.finrank_fin_fun] at h1
  omega

theorem exists_root_line [IsAlgClosed K] {h : MvPolynomial (Fin 3) K} {e : ℕ}
    (hh : h.IsHomogeneous e) (he : e ≠ 0) (v : Fin 3 → K)
    (hv : h = 0 ∨ aeval v h ≠ 0) (w : Fin 3 → K) :
    ∃ t : K, aeval (w + t • v) h = 0 := by
  have hev : ∀ (a b : Fin 3 → K) (t : K), aeval (a + t • b) h =
      Polynomial.eval t (aeval (fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) h) := by
    intro a b t
    have := MvPolynomial.comp_aeval_apply (R := K)
      (f := fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X)
      (Polynomial.aeval t) h
    simp only [Polynomial.coe_aeval_eq_eval] at this
    have hfun : (a + t • b) =
        fun i => Polynomial.eval t (Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X]
      ring
    rw [this, hfun]
  by_contra hcon
  push Not at hcon
  set ρ := aeval (fun i => Polynomial.C (w i) + Polynomial.C (v i) * Polynomial.X) h with hρ
  have hdeg : ρ.degree = 0 := by
    by_contra hd
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root ρ hd
    exact hcon t (by rw [hev]; exact ht)
  have hconst : ∀ t : K, aeval (w + t • v) h = aeval w h := by
    intro t
    rw [hev, ← hρ, Polynomial.eq_C_of_degree_eq_zero hdeg]
    have := hev w v 0
    simp only [zero_smul, add_zero] at this
    rw [this, ← hρ, Polynomial.eq_C_of_degree_eq_zero hdeg]
    simp
  set σ := aeval (fun i => Polynomial.C (v i) + Polynomial.C (w i) * Polynomial.X) h with hσ
  have hσe : σ = Polynomial.C (aeval w h) * Polynomial.X ^ e := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := {u : K | u ≠ 0})
    · intro u hu
      have hu : u ≠ 0 := hu
      show Polynomial.eval u σ = Polynomial.eval u (Polynomial.C (aeval w h) * Polynomial.X ^ e)
      rw [hσ, ← hev, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      have h1 : v + u • w = u • (w + u⁻¹ • v) := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ hu, one_smul, add_comm]
      rw [h1, aeval_smul_of_isHomogeneous hh, hconst, mul_comm]
    · exact (Set.finite_singleton (0 : K)).infinite_compl
  have h0 := congrArg (Polynomial.eval 0) hσe
  have := hev v w 0
  simp only [zero_smul, add_zero] at this
  rw [← hσ] at this
  rw [← this] at h0
  simp [zero_pow he] at h0
  rcases hv with hv | hv
  · exact hcon 0 (by simp [hv])
  · exact hv h0

theorem exists_eval_localQuotient {f g : MvPolynomial (Fin 2) K} {p : K × K}
    (hp : p ∈ commonZeros f g) :
    ∃ ev : LocalQuotientAt f g p →ₐ[K] K,
      ∀ q : MvPolynomial (Fin 2) K,
        ev (Ideal.Quotient.mk _ (algebraMap _ (LocalRingAt p) q)) = evalAt q p := by
  let ev0 : LocalRingAt p →ₐ[K] K :=
    IsLocalization.liftAlgHom (M := (pointIdeal p).primeCompl)
      (f := (aeval ![p.1, p.2] : MvPolynomial (Fin 2) K →ₐ[K] K)) (fun y => by
        have hy : (y : MvPolynomial (Fin 2) K) ∉ pointIdeal p := y.2
        have hy' : aeval ![p.1, p.2] (y : MvPolynomial (Fin 2) K) ≠ 0 := by
          simpa [pointIdeal] using hy
        exact isUnit_iff_ne_zero.mpr hy')
  have hev0 : ∀ q : MvPolynomial (Fin 2) K,
      ev0 (algebraMap _ (LocalRingAt p) q) = evalAt q p := by
    intro q
    show IsLocalization.lift _ (algebraMap _ (LocalRingAt p) q) = _
    rw [IsLocalization.lift_eq]
    rfl
  have hker : ∀ a ∈ Ideal.span {algebraMap _ (LocalRingAt p) f, algebraMap _ (LocalRingAt p) g},
      ev0 a = 0 := by
    have : Ideal.span {algebraMap _ (LocalRingAt p) f, algebraMap _ (LocalRingAt p) g} ≤
        RingHom.ker ev0.toRingHom := by
      rw [Ideal.span_le]
      intro a ha
      rcases ha with rfl | rfl
      · exact (RingHom.mem_ker).mpr (by simpa using (hev0 f).trans hp.1)
      · exact (RingHom.mem_ker).mpr (by simpa using (hev0 g).trans hp.2)
    intro a ha
    exact (RingHom.mem_ker).mp (this ha)
  exact ⟨Ideal.Quotient.liftₐ _ ev0 hker, fun q => by
    rw [Ideal.Quotient.liftₐ_apply]
    exact hev0 q⟩

theorem finite_localization_quotient {R : Type*} [CommRing R] [Algebra K R] (I : Ideal R)
    [Module.Finite K (R ⧸ I)]
    (Q : Ideal (R ⧸ I)) [Q.IsPrime] (P : Ideal R) [P.IsPrime]
    (hP : Q.comap (Ideal.Quotient.mk I) = P) :
    Module.Finite K (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  have := IsArtinianRing.of_finite K (R ⧸ I)
  obtain ⟨e⟩ := exists_algEquiv_localization_quotient I Q P hP
  have : IsScalarTower K (R ⧸ I) (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply K R _ c, IsScalarTower.algebraMap_apply R (R ⧸ I) _,
        ← IsScalarTower.algebraMap_apply K R (R ⧸ I)]
  have hL : Module.Finite K (Localization.AtPrime Q) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom K (R ⧸ I) _).toLinearMap
      (IsArtinianRing.localization_surjective Q.primeCompl _)
  exact Module.Finite.equiv (e.restrictScalars K).toLinearEquiv

theorem finite_localQuotient [IsAlgClosed K] {f g : MvPolynomial (Fin 2) K}
    (hfin : Module.Finite K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g})) {p : K × K}
    (hp : p ∈ commonZeros f g) : Module.Finite K (LocalQuotientAt f g p) := by
  obtain ⟨m, hm⟩ := exists_maximal_of_point f g p hp
  have := m.isMaximal.isPrime
  have key := finite_localization_quotient (K := K) (Ideal.span {f, g}) m.asIdeal (pointIdeal p) hm
  unfold LocalQuotientAt
  rw [map_span_pair_eq]
  exact key

theorem numAt_pos [IsAlgClosed K] {f g : MvPolynomial (Fin 2) K}
    (hfin : Module.Finite K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g})) {p : K × K}
    (hp : p ∈ commonZeros f g) : 0 < numAt f g p := by
  have := finite_localQuotient hfin hp
  obtain ⟨ev, -⟩ := exists_eval_localQuotient hp
  have := ev.toRingHom.domain_nontrivial
  exact Module.finrank_pos

theorem mk_eq_zero_of_numAt_eq_one {f g q : MvPolynomial (Fin 2) K} {p : K × K}
    (hp : p ∈ commonZeros f g) (h1 : numAt f g p = 1) (hq : evalAt q p = 0) :
    Ideal.Quotient.mk _ (algebraMap _ (LocalRingAt p) q) = (0 : LocalQuotientAt f g p) := by
  obtain ⟨ev, hev⟩ := exists_eval_localQuotient hp
  have h1' : Module.finrank K (LocalQuotientAt f g p) = 1 := h1
  have := Module.finite_of_finrank_pos (R := K) (M := LocalQuotientAt f g p) (by omega)
  have := ev.toRingHom.domain_nontrivial
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : LocalQuotientAt f g p) one_ne_zero).mp h1'
    (Ideal.Quotient.mk _ (algebraMap _ (LocalRingAt p) q))
  have h2 := hev q
  rw [← hc, map_smul, map_one, smul_eq_mul, mul_one, hq] at h2
  rw [← hc, h2, zero_smul]

theorem gradient_ne_zero_of_numAt_eq_one {f g : MvPolynomial (Fin 2) K} {p : K × K}
    (hp : p ∈ commonZeros f g) (h1 : numAt f g p = 1) :
    (evalAt (pderiv 0 f) p ≠ 0 ∨ evalAt (pderiv 1 f) p ≠ 0) ∨
      (evalAt (pderiv 0 g) p ≠ 0 ∨ evalAt (pderiv 1 g) p ≠ 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨hf0, -⟩, ⟨hg0, -⟩⟩ := hcon
  have h0 := mk_eq_zero_of_numAt_eq_one (q := X 0 - C p.1) hp h1 (by simp [evalAt])
  rw [Ideal.Quotient.eq_zero_iff_mem, map_span_pair_eq,
    IsLocalization.mem_map_algebraMap_iff (pointIdeal p).primeCompl] at h0
  obtain ⟨⟨a, s⟩, hs⟩ := h0
  rw [← map_mul] at hs
  have hs' := IsLocalization.injective (LocalRingAt p)
    (Ideal.primeCompl_le_nonZeroDivisors (pointIdeal p)) hs
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp a.2
  have hsp : evalAt (s : MvPolynomial (Fin 2) K) p ≠ 0 := by
    have hy : (s : MvPolynomial (Fin 2) K) ∉ pointIdeal p := s.2
    simpa [pointIdeal, evalAt] using hy
  have heq : (X 0 - C p.1) * (s : MvPolynomial (Fin 2) K) = u * f + v * g := by
    simp only at hs'
    rw [hs', ← huv]
  have hpf : evalAt f p = 0 := hp.1
  have hpg : evalAt g p = 0 := hp.2
  have := congrArg (fun r => aeval ![p.1, p.2] (pderiv 0 r)) heq
  simp [Derivation.leibniz, evalAt] at this hf0 hg0 hsp hpf hpg
  simp [hf0, hg0, hpf, hpg] at this
  exact hsp this

theorem infinite_zeros_of_isHomogeneous [IsAlgClosed K] {h : MvPolynomial (Fin 3) K} {e : ℕ}
    (hh : h.IsHomogeneous e) (he : e ≠ 0) : (projectivePoints h K).Infinite := by
  intro hfin
  have hzero : ∀ x : Fin 3 → K, aeval ((0 : K) • x) h = 0 := fun x => by
    rw [aeval_smul_of_isHomogeneous hh, zero_pow he, zero_mul]
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin 3 → K, v ≠ 0 ∧ (h = 0 ∨ aeval v h ≠ 0) := by
    by_cases h0 : h = 0
    · exact ⟨Pi.single 0 1, fun hc => by simpa using congrFun hc 0, Or.inl h0⟩
    · have : ∃ v : Fin 3 → K, aeval v h ≠ 0 := by
        by_contra hc
        push Not at hc
        apply h0
        apply MvPolynomial.funext
        intro x
        have := hc x
        simpa [MvPolynomial.aeval_eq_eval] using this
      obtain ⟨v, hv⟩ := this
      refine ⟨v, ?_, Or.inr hv⟩
      rintro rfl
      exact hv (by simpa using hzero 0)
  have := hfin.fintype
  let p : Option (projectivePoints h K) → Submodule K (Fin 3 → K) :=
    fun i => Option.elim i (Submodule.span K {v, v}) (fun P => Submodule.span K {P.1.rep, v})
  have hp : ∀ i, p i ≠ ⊤ := by
    intro i
    cases i with
    | none => exact span_pair_ne_top v v
    | some P => exact span_pair_ne_top _ _
  have hcard : (Finset.univ : Finset (Option (projectivePoints h K))).card < ENat.card K := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.natCast_lt_top _
  have := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt _ p hp hcard
  obtain ⟨w, -, hw⟩ := Set.exists_of_ssubset this
  obtain ⟨t, ht⟩ := exists_root_line hh he v hv w
  have hwv : w = (w + t • v) + (-t) • v := by module
  by_cases hx : w + t • v = 0
  · apply hw
    simp only [Set.mem_iUnion]
    refine ⟨none, by simp, ?_⟩
    show w ∈ Submodule.span K {v, v}
    rw [hx, zero_add] at hwv
    rw [hwv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · have hmem : Projectivization.mk K (w + t • v) hx ∈ projectivePoints h K :=
      (mem_projectivePoints_mk hh _ hx).mpr ht
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := K) (w + t • v) hx
    have ha' : (a : K) • (w + t • v) = (Projectivization.mk K (w + t • v) hx).rep := ha
    apply hw
    simp only [Set.mem_iUnion]
    refine ⟨some ⟨_, hmem⟩, by simp, ?_⟩
    show w ∈ Submodule.span K {(Projectivization.mk K (w + t • v) hx).rep, v}
    rw [Submodule.mem_span_pair]
    refine ⟨(a : K)⁻¹, -t, ?_⟩
    rw [← ha', smul_smul, inv_mul_cancel₀ a.ne_zero, one_smul]
    exact hwv.symm

end NumberFieldKB.MilneEC.Bezout
