import NumberFieldKB.WeilBNT.FunctionField.Idele
import NumberFieldKB.WeilBNT.FunctionField.RiemannRochCor
import Mathlib.NumberTheory.RatFunc.Ostrowski

/-!
# Completions and adeles of $\mathbb F_q(T)$ (Weil IV.§2, Lemmas 3 and 4)

Weil proves IV.§2 Thm. 2 for $k=\mathbb F_p(T)$ from two lemmas. For a place $v$ of $k$ write
$k(v)=\{\xi\in k:\lvert\xi\rvert_w\le1\text{ for all places }w\ne v\}$ (`RationalFF.kAt`). We prove them for
$k=\mathbb F_q(T)$ (`RatFunc Fq`), any finite field $\mathbb F_q$ ($q=p$ is Weil's case):

* **`RationalFF.weil_IV_2_lemma3_sum`**, **`RationalFF.weil_IV_2_lemma3_inter`**: $k_v=k(v)+\mathfrak r_v$ and
  $k(v)\cap\mathfrak r_v=\mathbb F_q$;
* **`RationalFF.weil_IV_2_lemma4_sum`**, **`RationalFF.weil_IV_2_lemma4_inter`**:
  $k_{\mathbb A}=\varphi(k)+\prod_v\mathfrak r_v$ and $\varphi(k)\cap\prod_v\mathfrak r_v=\varphi(\mathbb F_q)$.
* `RationalFF.isConstantField`: $\mathbb F_q$ is the field of constants of $\mathbb F_q(T)$.

Proof: a place $v$ with $v(T)\le1$ is the place of a prime polynomial $\pi$
(`Place.exists_eq_ofHeightOneSpectrum`); an element of $k$ is split by Bézout and division by $\pi^m$ into a part
in $k(v)$ (degree of numerator below that of $\pi^m$) and a part in $\mathfrak r_v$. There is exactly one place with
$v(T)>1$ (the place at infinity, where $v(f)=v(T)^{\deg f}$ for polynomials $f$), and there $k(v)=\mathbb F_q[T]$ and
one divides by the denominator.
-/

open scoped WithZero Polynomial
open Valuation IsDedekindDomain Polynomial

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

namespace RationalFF

variable {Fq : Type*} [Field Fq] [Finite Fq]

/-- Weil's $k(v)$ for $k=\mathbb F_q(T)$: the elements integral at every place other than $v$. -/
def kAt (v : Place Fq (RatFunc Fq)) : Set (RatFunc Fq) :=
  {ξ | ∀ w : Place Fq (RatFunc Fq), w ≠ v → w.valuation ξ ≤ 1}

theorem valuation_poly_le_one_of_X_le_one (w : Place Fq (RatFunc Fq)) (hw : w.valuation RatFunc.X ≤ 1)
    (f : Fq[X]) : w.valuation (algebraMap Fq[X] (RatFunc Fq) f) ≤ 1 := by
  have := Polynomial.valuation_le_one_of_valuation_X_le_one (v := w.valuation) Fq hw f
  simpa using this

/-- At a place with $v(T)>1$, a nonzero polynomial $f$ has $v(f)=v(T)^{\deg f}$. -/
theorem valuation_polynomial_of_one_lt (v : Place Fq (RatFunc Fq)) (hv : 1 < v.valuation (RatFunc.X))
    {f : Fq[X]} (hf : f ≠ 0) :
    v.valuation (algebraMap Fq[X] (RatFunc Fq) f) = v.valuation (RatFunc.X) ^ f.natDegree := by
  classical
  have := Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X (v := v.valuation) Fq hv hf
  simpa using this

theorem valuation_div_le_one_of_degree_lt (w : Place Fq (RatFunc Fq)) (hw : 1 < w.valuation RatFunc.X)
    {r g : Fq[X]} (hg : g ≠ 0) (h : r.degree < g.degree) :
    w.valuation (algebraMap Fq[X] (RatFunc Fq) r / algebraMap Fq[X] (RatFunc Fq) g) ≤ 1 := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [map_div₀, valuation_polynomial_of_one_lt w hw hr, valuation_polynomial_of_one_lt w hw hg]
    have hlt : r.natDegree < g.natDegree := Polynomial.natDegree_lt_natDegree hr h
    have hpos : 0 < w.valuation RatFunc.X := lt_trans zero_lt_one hw
    rw [div_le_one₀ (pow_pos hpos _)]
    exact pow_le_pow_right₀ hw.le hlt.le

theorem valuation_ofHeightOneSpectrum_eq_one (p : IsDedekindDomain.HeightOneSpectrum Fq[X]) (f : Fq[X])
    (hf : f ∉ p.asIdeal) :
    (Place.ofHeightOneSpectrum (Fq := Fq) (k := RatFunc Fq) Fq[X] p).valuation
      (algebraMap Fq[X] (RatFunc Fq) f) = 1 := by
  refine le_antisymm (p.valuation_le_one f) (not_lt.1 ?_)
  rw [Place.ofHeightOneSpectrum_valuation, p.valuation_lt_one_iff_mem]
  exact hf

/-- There is at most one place with $v(T)>1$ (the place at infinity). -/
theorem eq_of_one_lt (v w : Place Fq (RatFunc Fq)) (hv : 1 < v.valuation (RatFunc.X))
    (hw : 1 < w.valuation (RatFunc.X)) : v = w := by
  classical
  exact Place.eq_of_isEquiv
    ((RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hv).trans
      (RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hw).symm)

theorem exists_decomp (v : Place Fq (RatFunc Fq)) (ξ : RatFunc Fq) :
    ∃ η ∈ kAt v, ∃ ρ : RatFunc Fq, v.valuation ρ ≤ 1 ∧ ξ = η + ρ := by
  classical
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Fq[X]) ξ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hφb0 : ∀ {f : Fq[X]}, f ≠ 0 → algebraMap Fq[X] (RatFunc Fq) f ≠ 0 := fun hf =>
    (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).2 hf
  by_cases hvX : 1 < v.valuation RatFunc.X
  · refine ⟨algebraMap Fq[X] (RatFunc Fq) (a / b), ?_,
      algebraMap Fq[X] (RatFunc Fq) (a % b) / algebraMap Fq[X] (RatFunc Fq) b, ?_, ?_⟩
    · intro w hw
      have : w.valuation RatFunc.X ≤ 1 := by
        by_contra h
        exact hw (eq_of_one_lt w v (not_le.1 h) hvX)
      exact valuation_poly_le_one_of_X_le_one w this _
    · exact valuation_div_le_one_of_degree_lt v hvX hb0 (EuclideanDomain.mod_lt a hb0)
    · have h := congrArg (algebraMap Fq[X] (RatFunc Fq)) (EuclideanDomain.div_add_mod a b)
      rw [map_add, map_mul] at h
      rw [← hab, ← h]
      have := hφb0 hb0
      field_simp
  · have hvX' := not_lt.1 hvX
    have hle := valuation_poly_le_one_of_X_le_one v hvX'
    obtain ⟨p, hp⟩ := Place.exists_eq_ofHeightOneSpectrum (Fq := Fq) (k := RatFunc Fq) Fq[X] v hle
    obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal p.asIdeal)
    have hπ' : p.asIdeal = Ideal.span {π} := hπ
    have hπ0 : π ≠ 0 := by
      rintro rfl
      exact p.ne_bot (by rw [hπ']; simp)
    have hprime : Prime π := (Ideal.span_singleton_prime hπ0).1 (hπ' ▸ p.isPrime)
    have hirr : Irreducible π := hprime.irreducible
    obtain ⟨m, h, hnd, hbh⟩ := WfDvdMonoid.max_power_factor hb0 hirr
    have hcop : IsCoprime (π ^ m) h := ((Irreducible.coprime_iff_not_dvd hirr).2 hnd).pow_left
    obtain ⟨s, t, hst⟩ := hcop
    have hP0 : π ^ m ≠ 0 := pow_ne_zero _ hπ0
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact hb0 (by simpa using hbh)
    have hdm := EuclideanDomain.div_add_mod (a * t) (π ^ m)
    obtain ⟨U, R, E, hRdeg⟩ : ∃ U R : Fq[X], a = π ^ m * U + R * h ∧ R.degree < (π ^ m).degree :=
      ⟨a * s + (a * t / π ^ m) * h, a * t % π ^ m, by linear_combination (-a) * hst + (-h) * hdm,
        EuclideanDomain.mod_lt _ hP0⟩
    have hhp : h ∉ p.asIdeal := by
      rw [hπ', Ideal.mem_span_singleton]
      exact hnd
    refine ⟨algebraMap Fq[X] (RatFunc Fq) R / algebraMap Fq[X] (RatFunc Fq) (π ^ m), ?_,
      algebraMap Fq[X] (RatFunc Fq) U / algebraMap Fq[X] (RatFunc Fq) h, ?_, ?_⟩
    · intro w hw
      by_cases hwX : 1 < w.valuation RatFunc.X
      · exact valuation_div_le_one_of_degree_lt w hwX hP0 hRdeg
      · have hwX' := not_lt.1 hwX
        have hle' := valuation_poly_le_one_of_X_le_one w hwX'
        obtain ⟨p', hp'⟩ := Place.exists_eq_ofHeightOneSpectrum (Fq := Fq) (k := RatFunc Fq) Fq[X] w hle'
        have hne : p' ≠ p := by
          rintro rfl
          exact hw (hp'.trans hp.symm)
        have hπp' : π ∉ p'.asIdeal := by
          intro hmem
          have hle2 : p.asIdeal ≤ p'.asIdeal := by
            rw [hπ']
            exact (Ideal.span_singleton_le_iff_mem _).2 hmem
          exact hne (IsDedekindDomain.HeightOneSpectrum.ext
            (p.isMaximal.eq_of_le p'.isPrime.ne_top hle2).symm)
        have h1 := valuation_ofHeightOneSpectrum_eq_one p' π hπp'
        rw [← hp'] at h1
        rw [map_div₀, map_pow, map_pow, h1, one_pow, div_one]
        exact hle' R
    · rw [map_div₀, hp, valuation_ofHeightOneSpectrum_eq_one p h hhp, div_one, ← hp]
      exact hle U
    · have hφP := hφb0 hP0
      have hφh := hφb0 hh0
      have key := congrArg (algebraMap Fq[X] (RatFunc Fq)) E
      rw [map_add, map_mul, map_mul] at key
      have hφb : algebraMap Fq[X] (RatFunc Fq) b =
          algebraMap Fq[X] (RatFunc Fq) (π ^ m) * algebraMap Fq[X] (RatFunc Fq) h := by
        rw [hbh, map_mul]
      rw [← hab, key, hφb]
      field_simp
      ring

/-- **Weil IV.§2, Lemma 3** (first assertion), $k=\mathbb F_q(T)$: $k_v=k(v)+\mathfrak r_v$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Lemma 3 (p. 65), k_v = k(v) + r_v, for F_q(T)"]
theorem weil_IV_2_lemma3_sum (v : Place Fq (RatFunc Fq)) (x : v.Completion) :
    ∃ ξ ∈ kAt v, x - v.toCompletion ξ ∈ v.completionIntegers := by
  obtain ⟨ξ0, hξ0⟩ : ∃ ξ0, Valued.v (x - v.toCompletion ξ0) < 1 := by
    have hn : {z : v.Completion | Valued.v (z - x) < 1} ∈ nhds x :=
      Valued.mem_nhds.2 ⟨1, fun z hz => by simpa [Valuation.restrict_lt_iff] using hz⟩
    obtain ⟨a, ha⟩ := (Place.denseRange_toCompletion v).mem_nhds hn
    exact ⟨a, by rw [Valuation.map_sub_swap]; exact ha⟩
  obtain ⟨η, hη, ρ, hρ, hξρ⟩ := exists_decomp v ξ0
  refine ⟨η, hη, ?_⟩
  have : x - v.toCompletion η = (x - v.toCompletion ξ0) + v.toCompletion ρ := by
    rw [hξρ, map_add]; ring
  rw [Place.mem_completionIntegers_iff, this]
  refine le_trans (Valuation.map_add _ _ _) (max_le hξ0.le ?_)
  rw [Place.valued_toCompletion]
  exact hρ

/-- **$\mathbb F_q$ is the field of constants of $\mathbb F_q(T)$**: an element integral at every place is
constant. -/
theorem mem_range_of_forall_valuation_le_one {ξ : RatFunc Fq}
    (h : ∀ w : Place Fq (RatFunc Fq), w.valuation ξ ≤ 1) : ξ ∈ Set.range (algebraMap Fq (RatFunc Fq)) := by
  classical
  have hint : ∀ q : IsDedekindDomain.HeightOneSpectrum Fq[X],
      q.valuation (RatFunc Fq) ξ ≤ 1 := fun q =>
    h (Place.ofHeightOneSpectrum (Fq := Fq) (k := RatFunc Fq) Fq[X] q)
  obtain ⟨f, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := Fq[X]) (RatFunc Fq) ξ hint
  have hsurj : Function.Surjective (RatFunc.inftyValuation Fq) := by
    intro g
    rcases eq_or_ne g 0 with rfl | hg
    · exact ⟨0, map_zero _⟩
    · refine ⟨RatFunc.X ^ (WithZero.log g), ?_⟩
      rw [RatFunc.inftyValuation.X_zpow, WithZero.exp_log hg]
  let w : Place Fq (RatFunc Fq) := Place.mk' (RatFunc.inftyValuation Fq) hsurj
  have hwX : 1 < w.valuation RatFunc.X := by
    show 1 < RatFunc.inftyValuation Fq RatFunc.X
    rw [RatFunc.inftyValuation.X, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.2 one_pos
  by_cases hf : f = 0
  · exact ⟨0, by simp [hf]⟩
  · have h1 := h w
    rw [valuation_polynomial_of_one_lt w hwX hf] at h1
    have hn : f.natDegree = 0 := by
      by_contra hn
      exact absurd h1 (not_le.2 (one_lt_pow₀ hwX hn))
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hn
    refine ⟨f.coeff 0, ?_⟩
    rw [IsScalarTower.algebraMap_apply Fq Fq[X] (RatFunc Fq), Polynomial.algebraMap_eq, ← hC]

theorem isConstantField : IsConstantField Fq (RatFunc Fq) := by
  intro y hy
  refine mem_range_of_forall_valuation_le_one fun w => ?_
  by_cases hy0 : y = 0
  · simp [hy0]
  · have : w.valuation y = 1 := by
      by_contra hne
      exact Valuation.transcendental_of_ne_one (v := w.valuation) Fq y hy0 hne hy
    simp [this]

/-- **Weil IV.§2, Lemma 3** (second assertion), $k=\mathbb F_q(T)$: $k(v)\cap\mathfrak r_v=\mathbb F_q$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Lemma 3 (p. 65), k(v) ∩ r_v = F_q, for F_q(T)"]
theorem weil_IV_2_lemma3_inter (v : Place Fq (RatFunc Fq)) (ξ : RatFunc Fq) :
    (ξ ∈ kAt v ∧ v.toCompletion ξ ∈ v.completionIntegers) ↔ ξ ∈ Set.range (algebraMap Fq (RatFunc Fq)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine mem_range_of_forall_valuation_le_one fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [Place.mem_completionIntegers_iff, Place.valued_toCompletion] at h2
      exact h2
    · exact h1 w hw
  · rintro ⟨c, rfl⟩
    refine ⟨fun w _ => w.mem_integers_iff.1 (w.algebraMap_mem_integers c), ?_⟩
    rw [Place.mem_completionIntegers_iff, Place.valued_toCompletion]
    exact v.mem_integers_iff.1 (v.algebraMap_mem_integers c)

/-- **Weil IV.§2, Lemma 4** (first assertion), $k=\mathbb F_q(T)$: $k_{\mathbb A}=\varphi(k)+\prod_v\mathfrak r_v$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Lemma 4 (p. 65), k_A = k + prod r_v, for F_q(T)"]
theorem weil_IV_2_lemma4_sum (x : FFAdeleRing Fq (RatFunc Fq)) :
    ∃ ξ : RatFunc Fq, ∀ v : Place Fq (RatFunc Fq),
      ((x - FFAdeleRing.diag ξ : FFAdeleRing Fq (RatFunc Fq)) v) ∈ (v.completionIntegers : Set v.Completion) := by
  classical
  have hS : {v : Place Fq (RatFunc Fq) | x v ∉ (v.completionIntegers : Set v.Completion)}.Finite :=
    Filter.eventually_cofinite.1 x.2
  have hex : ∀ v : Place Fq (RatFunc Fq),
      ∃ ξ ∈ kAt v, x v - v.toCompletion ξ ∈ v.completionIntegers :=
    fun v => weil_IV_2_lemma3_sum v (x v)
  choose f hfk hfx using hex
  refine ⟨∑ v ∈ hS.toFinset, f v, fun w => ?_⟩
  have hsub : (x - FFAdeleRing.diag (∑ v ∈ hS.toFinset, f v) : FFAdeleRing Fq (RatFunc Fq)) w =
      x w - ∑ v ∈ hS.toFinset, w.toCompletion (f v) := by
    show x w - w.toCompletion _ = _
    rw [map_sum]
  have hterm : ∀ v, w ≠ v → w.toCompletion (f v) ∈ w.completionIntegers := fun v hv => by
    rw [Place.mem_completionIntegers_iff, Place.valued_toCompletion]
    exact hfk v w hv
  rw [hsub]
  show _ ∈ w.completionIntegers
  by_cases hw : w ∈ hS.toFinset
  · rw [← Finset.add_sum_erase _ _ hw, ← sub_sub]
    exact sub_mem (hfx w) (sum_mem fun v hv => hterm v (Finset.ne_of_mem_erase hv).symm)
  · have hxw : x w ∈ w.completionIntegers := by
      by_contra hc
      exact hw (hS.mem_toFinset.2 hc)
    exact sub_mem hxw (sum_mem fun v hv => hterm v (fun h => hw (h ▸ hv)))

/-- **Weil IV.§2, Lemma 4** (second assertion), $k=\mathbb F_q(T)$:
$\varphi(k)\cap\prod_v\mathfrak r_v=\varphi(\mathbb F_q)$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Lemma 4 (p. 65), k ∩ prod r_v = F_q, for F_q(T)"]
theorem weil_IV_2_lemma4_inter (ξ : RatFunc Fq) :
    (∀ v : Place Fq (RatFunc Fq), FFAdeleRing.diag ξ v ∈ (v.completionIntegers : Set v.Completion)) ↔
      ξ ∈ Set.range (algebraMap Fq (RatFunc Fq)) := by
  constructor
  · intro h
    refine mem_range_of_forall_valuation_le_one fun w => ?_
    have : (FFAdeleRing.diag ξ) w ∈ w.completionIntegers := h w
    rw [Place.mem_completionIntegers_iff] at this
    rwa [← Place.valued_toCompletion]
  · rintro ⟨c, rfl⟩ w
    show Valued.v (w.toCompletion _) ≤ 1
    rw [Place.valued_toCompletion]
    exact w.mem_integers_iff.1 (w.algebraMap_mem_integers c)

end RationalFF

end NumberFieldKB.WeilBNT.FF
