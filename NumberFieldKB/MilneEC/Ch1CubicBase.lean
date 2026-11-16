import NumberFieldKB.MilneEC.Ch1CubicGrad
import NumberFieldKB.MilneEC.Ch1GroupLaw

/-!
# The chord and tangent construction under extension of the field

Part of the proof of associativity of the chord and tangent law (Milne, *Elliptic Curves*, Theorem I.3.1):
the construction commutes with extending the field of definition, so associativity over `k` follows from
associativity over $k^{\mathrm{al}}$.

* `mapPoint K P`: the point `P` of $\mathbb P^2(k)$ regarded as a point of $\mathbb P^2(K)$; injective.
* `IsThirdPoint.map`: the third point of `P`, `Q` maps to the third point of their images.
* `isSmoothForm_baseChange`: a nonsingular cubic over `k` is a smooth form over $k^{\mathrm{al}}$.
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.Bezout

variable {k : Type*} [Field k]

/-- A point of $\mathbb P^2(k)$ as a point of $\mathbb P^2(K)$. -/
noncomputable def mapPoint (K : Type*) [Field K] [Algebra k K] (P : ℙ k (Fin 3 → k)) :
    ℙ K (Fin 3 → K) :=
  Projectivization.mk K (fun j => algebraMap k K (P.rep j)) (fun h => P.rep_nonzero (funext fun j => by
    simpa using congrFun h j))

theorem mapPoint_injective (K : Type*) [Field K] [Algebra k K] :
    Function.Injective (mapPoint (k := k) K) := by
  intro P Q h
  have hinj : Function.Injective (algebraMap k K) := (algebraMap k K).injective
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
  obtain ⟨j, hj⟩ := exists_ne_zero_coord Q.rep Q.rep_nonzero
  have hj' : algebraMap k K (Q.rep j) ≠ 0 := by simpa using hj
  have haj := congrFun ha j
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at haj
  have hb : ∀ i, P.rep i = (P.rep j / Q.rep j) * Q.rep i := by
    intro i
    apply hinj
    have hi := congrFun ha i
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at hi
    rw [map_mul, map_div₀, ← hi, ← haj]
    field_simp
  refine (Projectivization.mk_rep P).symm.trans (Eq.trans ?_ (Projectivization.mk_rep Q))
  refine (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr ⟨P.rep j / Q.rep j, ?_⟩
  funext i
  simp [hb i]

/-- Two vectors are linearly independent iff some `2 × 2` minor is nonzero. -/
theorem pair_indep_iff_minor {L : Type*} [Field L] (p q : Fin 3 → L) :
    LinearIndependent L ![p, q] ↔ ∃ i j, p i * q j - p j * q i ≠ 0 := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro hind
    by_contra h
    push Not at h
    by_cases hp : p = 0
    · have := hind 1 0 (by simp [hp])
      exact one_ne_zero this.1
    · obtain ⟨i, hi⟩ := exists_ne_zero_coord p hp
      have := hind (q i) (-(p i)) (by
        funext j
        have := h j i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        linear_combination this)
      exact hi (neg_eq_zero.mp this.2)
  · rintro ⟨i, j, hij⟩ s t hst
    have e : ∀ j, s * p j + t * q j = 0 := fun j => by simpa using congrFun hst j
    constructor
    · have : s * (p i * q j - p j * q i) = 0 := by
        linear_combination q j * e i - q i * e j
      exact (mul_eq_zero.mp this).resolve_right hij
    · have : t * (p i * q j - p j * q i) = 0 := by
        linear_combination p i * e j - p j * e i
      exact (mul_eq_zero.mp this).resolve_right hij

theorem mapPoint_mk (K : Type*) [Field K] [Algebra k K] (v : Fin 3 → k) (hv : v ≠ 0) :
    mapPoint K (Projectivization.mk k v hv) = Projectivization.mk K (fun j => algebraMap k K (v j))
      (fun h => hv (funext fun j => by simpa using congrFun h j)) := by
  obtain ⟨l, hl, hvl⟩ := exists_smul_rep v hv
  unfold mapPoint
  refine (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨algebraMap k K l⁻¹, ?_⟩
  funext j
  have hj : v j = l * (Projectivization.mk k v hv).rep j := by
    have := congrFun hvl j
    simpa using this
  simp only [Pi.smul_apply, smul_eq_mul, hj, map_mul, map_inv₀]
  have : algebraMap k K l ≠ 0 := by simpa using hl
  field_simp

theorem mapPoint_rep (K : Type*) [Field K] [Algebra k K] (P : ℙ k (Fin 3 → k)) :
    ∃ κ : K, κ ≠ 0 ∧ (mapPoint K P).rep = κ • (fun j => algebraMap k K (P.rep j)) := by
  have hv0 : (fun j => algebraMap k K (P.rep j)) ≠ 0 := fun h =>
    P.rep_nonzero (funext fun j => by simpa using congrFun h j)
  obtain ⟨κ0, hκ0, hvκ⟩ := exists_smul_rep (fun j => algebraMap k K (P.rep j)) hv0
  refine ⟨κ0⁻¹, inv_ne_zero hκ0, ?_⟩
  exact (eq_inv_smul_iff₀ hκ0).mpr hvκ.symm

theorem lineRestriction_map (K : Type*) [Field K] [Algebra k K] (F : MvPolynomial (Fin 3) k)
    (p q : Fin 3 → k) :
    lineRestriction (baseChange K F) (fun j => algebraMap k K (p j)) (fun j => algebraMap k K (q j)) =
      MvPolynomial.map (algebraMap k K) (lineRestriction F p q) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [lineRestriction]
  | add f g hf hg =>
    unfold lineRestriction at hf hg ⊢
    simp only [map_add] at hf hg ⊢
    rw [hf, hg]
  | mul_X f i hf =>
    unfold lineRestriction at hf ⊢
    simp only [map_mul, MvPolynomial.map_X, aeval_X, map_add, MvPolynomial.map_C] at hf ⊢
    rw [hf]

theorem IsThirdPoint.map {F : MvPolynomial (Fin 3) k} (hF : F.IsHomogeneous 3) (K : Type*) [Field K]
    [Algebra k K] {P Q R : ℙ k (Fin 3 → k)} (h : IsThirdPoint F P Q R) :
    IsThirdPoint (baseChange K F) (mapPoint K P) (mapPoint K Q) (mapPoint K R) := by
  obtain ⟨q, c, s, t, hc, hind, hQ, htan, ⟨hne, hR⟩, hφ⟩ := h
  have hinj : Function.Injective (algebraMap k K) := (algebraMap k K).injective
  obtain ⟨κ, hκ, hrep⟩ := mapPoint_rep K P
  have hq0 : q ≠ 0 := hind.ne_zero 1
  have hq0' : (fun j => algebraMap k K (q j)) ≠ 0 := fun h =>
    hq0 (funext fun j => by simpa using congrFun h j)
  have hind' : LinearIndependent K ![(mapPoint K P).rep, fun j => algebraMap k K (q j)] := by
    rw [pair_indep_iff_minor] at hind ⊢
    obtain ⟨i, j, hij⟩ := hind
    refine ⟨i, j, ?_⟩
    rw [hrep]
    intro h
    apply hij
    apply hinj
    have h2 : κ * (algebraMap k K (P.rep i) * algebraMap k K (q j) -
        algebraMap k K (P.rep j) * algebraMap k K (q i)) = 0 := by
      simp only [Pi.smul_apply, smul_eq_mul] at h
      linear_combination h
    have h3 := (mul_eq_zero.mp h2).resolve_left hκ
    rw [map_sub, map_mul, map_mul, map_zero]
    exact h3
  -- the third point
  have hkey : algebraMap k K s • (mapPoint K P).rep +
      (algebraMap k K t * κ) • (fun j => algebraMap k K (q j)) =
      κ • (fun j => algebraMap k K ((s • P.rep + t • q) j)) := by
    rw [hrep]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  have hR' : ∃ h : algebraMap k K s • (mapPoint K P).rep +
      (algebraMap k K t * κ) • (fun j => algebraMap k K (q j)) ≠ 0,
      mapPoint K R = Projectivization.mk K _ h := by
    have hw : (fun j => algebraMap k K ((s • P.rep + t • q) j)) ≠ 0 := fun h =>
      hne (funext fun j => (map_eq_zero_iff _ hinj).mp
        (by simpa only [Pi.zero_apply] using congrFun h j))
    have hne' : algebraMap k K s • (mapPoint K P).rep +
        (algebraMap k K t * κ) • (fun j => algebraMap k K (q j)) ≠ 0 := by
      rw [hkey]; exact smul_ne_zero hκ hw
    refine ⟨hne', ?_⟩
    rw [hR, mapPoint_mk]
    refine (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨κ⁻¹, ?_⟩
    rw [hkey]
    funext j
    simp [hκ]
  have hline : lineRestriction (baseChange K F) (mapPoint K P).rep
      (fun j => algebraMap k K (q j)) =
      aeval ![C κ * X 0 + C 0 * X 1, C 0 * X 0 + C 1 * X 1]
        (MvPolynomial.map (algebraMap k K) (lineRestriction F P.rep q)) := by
    have := lineRestriction_lin (baseChange K F) (fun j => algebraMap k K (P.rep j))
      (fun j => algebraMap k K (q j)) κ 0 0 1
    simp only [zero_smul, add_zero, zero_add, one_smul] at this
    rw [hrep, this, lineRestriction_map]
  by_cases hPQ : P = Q
  · have hPQ' : mapPoint K P = mapPoint K Q := by rw [hPQ]
    refine ⟨fun j => algebraMap k K (q j), algebraMap k K c, algebraMap k K s,
      algebraMap k K t * κ, by simpa using hc, hind', fun h => absurd hPQ' h, fun _ => ?_, hR', ?_⟩
    · have htan' := htan hPQ
      unfold polarPairing at htan' ⊢
      have hp : ∀ j, eval (mapPoint K P).rep (pderiv j (baseChange K F)) =
          κ ^ 2 * algebraMap k K (eval P.rep (pderiv j F)) := by
        intro j
        rw [pderiv_map, ← aeval_eq_eval, aeval_map_algebraMap, hrep,
          aeval_smul_of_isHomogeneous hF.pderiv,
          show (fun j => algebraMap k K (P.rep j)) = algebraMap k K ∘ P.rep from rfl,
          aeval_algebraMap_apply, aeval_eq_eval]
      simp only [hp]
      have : ∑ j : Fin 3, κ ^ 2 * algebraMap k K (eval P.rep (pderiv j F)) *
          algebraMap k K (q j) = κ ^ 2 * algebraMap k K
            (∑ j : Fin 3, eval P.rep (pderiv j F) * q j) := by
        simp only [map_sum, map_mul, Finset.mul_sum, mul_assoc]
      rw [this, htan']
      simp
    · rw [hline, hφ, ite_X_of_eq hPQ, ite_X_of_eq hPQ']
      simp only [map_mul, map_sub, MvPolynomial.map_C, MvPolynomial.map_X, map_add, aeval_X,
        aeval_C, MvPolynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, map_zero, map_one]
      ring
  · have hPQ' : ¬ mapPoint K P = mapPoint K Q := fun h => hPQ (mapPoint_injective K h)
    refine ⟨fun j => algebraMap k K (q j), algebraMap k K c * κ, algebraMap k K s,
      algebraMap k K t * κ, mul_ne_zero (by simpa using hc) hκ, hind', fun _ => ⟨hq0', ?_⟩,
      fun h => absurd h hPQ', hR', ?_⟩
    · obtain ⟨_, hQq⟩ := hQ hPQ
      rw [hQq, mapPoint_mk]
    · rw [hline, hφ, ite_X_of_ne hPQ, ite_X_of_ne hPQ']
      simp only [map_mul, map_sub, MvPolynomial.map_C, MvPolynomial.map_X, map_add, aeval_X,
        aeval_C, MvPolynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, map_zero, map_one]
      ring

theorem isSmoothForm_baseChange {F : MvPolynomial (Fin 3) k} (hF : IsNonsingularCubic F) :
    IsSmoothForm (baseChange (AlgebraicClosure k) F) := by
  intro v hv h0
  have hH := hF.isHomogeneous
  rw [aeval_map_algebraMap] at h0
  have hP : Projectivization.mk (AlgebraicClosure k) v hv ∈
      projectivePoints F (AlgebraicClosure k) := (mem_projectivePoints_mk hH v hv).mpr h0
  have hns := hF.2.2 _ hP
  obtain ⟨c, hc, hvc⟩ := exists_smul_rep v hv
  generalize (Projectivization.mk (AlgebraicClosure k) v hv) = P at hns hvc hP
  rw [isNonsingularProjPoint_iff hH P hP] at hns
  push Not at hns
  obtain ⟨j, hj⟩ := hns
  refine ⟨j, ?_⟩
  rw [pderiv_map, aeval_map_algebraMap, hvc, aeval_smul_of_isHomogeneous hH.pderiv]
  exact mul_ne_zero (pow_ne_zero _ hc) hj

end NumberFieldKB.MilneEC.Bezout
