import NumberFieldKB.WeilBNT.AdeleBoxes
import QuadFormsKB.Analysis.AdelicPoisson

/-!
# Weil, *Basic Number Theory*, IV.§2, Theorem 3 (case $E=k$): $k$ is its own annihilator in $k_{\mathbb A}$

$k$ is a number field and $k_{\mathbb A}=k_\infty\times\mathbb A_k^{\mathrm{fin}}$ is Mathlib's adele ring. The standard
character (QuadFormsKB's local characters, `QuadFormsKB.Analysis.psiInf`, `QuadFormsKB.Analysis.psiV`)
$$\chi(a)=\psi_\infty(a_\infty)\prod_v\psi_v(a_v),\qquad \psi_\infty=e\circ\operatorname{Tr}_\infty,\quad
\psi_v=\psi_p\circ\operatorname{Tr}_{k_v/\mathbb Q_p}$$
(`chiA`) is a character of $k_{\mathbb A}$ (`chiA_add`), trivial on $k$ (`chiA_algebraMap`, the product formula of
QuadFormsKB `fourierChar_trace_mul_finprod_psiV`).

* **`weil_IV_2_thm3_annihilator`** (Weil, Thm. 3, p. 66, last assertion, for $E=E'=k$ and $[e,e']=ee'$): an adele $a$
  has $\chi(a\xi)=1$ for every $\xi\in k$ if and only if $a\in k$.

The first assertion of Thm. 3 (that $a\mapsto(x\mapsto\chi(ax))$ is an isomorphism of $k_{\mathbb A}$ onto its
Pontryagin dual) is not formalized here.

**Proof** (Weil derives the theorem from the duality theory of Chap. II and the compactness of $k_{\mathbb A}/k$; here it
is proved directly). By strong approximation (QuadFormsKB `exists_strong_approx`) subtract an element of $k$ so that
$a_v\in r_v$ for every finite $v$. Then $\psi_\infty(a_\infty x)=1$ for every $x\in\mathfrak r$, so
$\operatorname{Tr}_\infty(a_\infty x)\in\mathbb Z$, and the trace-dual basis of an integral basis gives $b\in k$ with
$a_\infty=b$ and $\operatorname{Tr}(b\mathfrak r)\subseteq\mathbb Z$ (`exists_eq_mixedEmbedding_of_traceInf_int`). Then
$c=a-b$ is a finite adele with $\prod_v\psi_v(c_v\xi)=1$ for all $\xi\in k$, and strong approximation with the
nontriviality of each $\psi_v$ forces $c=0$ (`eq_zero_of_finprod_psiV_eq_one`).
-/

open IsDedekindDomain NumberField WithZero QuadFormsKB.Analysis NumberField.mixedEmbedding
open scoped Real FourierTransform

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

/-! ### The standard character of the adeles -/

theorem valued_le_one_of_mem {v : HeightOneSpectrum (𝓞 K)} {x : v.adicCompletion K}
    (hx : x ∈ v.adicCompletionIntegers K) : Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx

/-- Only finitely many local factors $\psi_v(a_v)$ of a finite adele differ from $1$. -/
theorem finite_mulSupport_psiV (a : FiniteAdeleRing (𝓞 K) K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => psiV v (a v)).Finite := by
  refine (Filter.eventually_cofinite.mp a.2).subset fun v hv => ?_
  intro hmem
  exact hv (psiV_eq_one_of_le_one v (valued_le_one_of_mem hmem))

variable (K) in
/-- The finite part $\prod_v\psi_v(a_v)$ of the standard character. -/
def chiFin (a : FiniteAdeleRing (𝓞 K) K) : Circle := ∏ᶠ v : HeightOneSpectrum (𝓞 K), psiV v (a v)

variable (K) in
/-- The infinite part $\psi_\infty(a_\infty)=e(\operatorname{Tr}_\infty a_\infty)$ of the standard character. -/
def chiInf (y : InfiniteAdeleRing K) : Circle := psiInf (InfiniteAdeleRing.ringEquiv_mixedSpace K y)

variable (K) in
/-- **The standard character of $k_{\mathbb A}$** (Weil, IV.§2, a "basic character" for $k$; Tate's $\psi$):
$\chi(a)=\psi_\infty(a_\infty)\prod_v\psi_v(a_v)$. -/
def chiA (a : AdeleRing (𝓞 K) K) : Circle := chiInf K a.1 * chiFin K a.2

theorem chiFin_add (a b : FiniteAdeleRing (𝓞 K) K) : chiFin K (a + b) = chiFin K a * chiFin K b := by
  unfold chiFin
  rw [← finprod_mul_distrib (finite_mulSupport_psiV a) (finite_mulSupport_psiV b)]
  exact finprod_congr fun v => (psiV v).map_add_eq_mul (a v) (b v)

theorem chiInf_add (y z : InfiniteAdeleRing K) : chiInf K (y + z) = chiInf K y * chiInf K z := by
  unfold chiInf psiInf
  rw [map_add, traceInf_add]
  exact Real.fourierChar.map_add_eq_mul _ _

theorem chiA_add (a b : AdeleRing (𝓞 K) K) : chiA K (a + b) = chiA K a * chiA K b := by
  unfold chiA
  rw [Prod.fst_add, Prod.snd_add, chiInf_add, chiFin_add, mul_mul_mul_comm]

theorem chiFin_zero : chiFin K 0 = 1 := by
  have h := chiFin_add (K := K) 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem chiInf_zero : chiInf K 0 = 1 := by
  have h := chiInf_add (K := K) 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

/-- **$\chi$ is trivial on $k$** (the product formula for the standard character). -/
theorem chiA_algebraMap (ξ : K) : chiA K (algebraMap K (AdeleRing (𝓞 K) K) ξ) = 1 := by
  have h := fourierChar_trace_mul_finprod_psiV ξ
  rw [← traceInf_mixedEmbedding, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] at h
  exact h

/-! ### The infinite place: $\operatorname{Tr}_\infty(y\,\mathfrak r)\subseteq\mathbb Z$ forces $y\in k$ -/

/-- $\operatorname{Tr}_\infty(z\bar z)$ vanishes only at $z=0$. -/
theorem eq_zero_of_traceInf_mul_star (z : mixedSpace K) (h : traceInf (z * star z) = 0) : z = 0 := by
  classical
  have h1 : ∀ w, 0 ≤ z.1 w * z.1 w := fun w => mul_self_nonneg _
  have h2 : ∀ w, 0 ≤ 2 * (z.2 w * star (z.2 w)).re := fun w => by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    exact mul_nonneg zero_le_two (Complex.normSq_nonneg _)
  unfold traceInf at h
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_star, Prod.snd_star, Pi.mul_apply, Pi.star_apply,
    star_trivial] at h
  have hs1 := Finset.sum_nonneg fun w (_ : w ∈ Finset.univ) => h1 w
  have hs2 := Finset.sum_nonneg fun w (_ : w ∈ Finset.univ) => h2 w
  have e1 : ∑ w, z.1 w * z.1 w = 0 := by linarith
  have e2 : ∑ w, 2 * (z.2 w * star (z.2 w)).re = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun w _ => h1 w] at e1
  rw [Finset.sum_eq_zero_iff_of_nonneg fun w _ => h2 w] at e2
  refine Prod.ext (funext fun w => mul_self_eq_zero.mp (e1 w (Finset.mem_univ w))) (funext fun w => ?_)
  have := e2 w (Finset.mem_univ w)
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re] at this
  have : Complex.normSq (z.2 w) = 0 := by linarith
  exact Complex.normSq_eq_zero.mp this

/-- If $\operatorname{Tr}_\infty(y\,x)\in\mathbb Z$ for all $x\in\mathfrak r$, then $y$ is (the image of) an element
$b\in k$ with $\operatorname{Tr}(b\,\mathfrak r)\subseteq\mathbb Z$. -/
theorem exists_eq_mixedEmbedding_of_traceInf_int (y : mixedSpace K)
    (hy : ∀ x : 𝓞 K, ∃ n : ℤ, traceInf (y * mixedEmbedding K (x : K)) = n) :
    ∃ b : K, y = mixedEmbedding K b ∧ ∀ x : 𝓞 K, ∃ m : ℤ, Algebra.trace ℚ K (b * x) = m := by
  classical
  set e := integralBasis K
  have hint : ∀ i, ∃ x : 𝓞 K, (x : K) = e i := fun i => ⟨_, (integralBasis_apply K i).symm⟩
  choose xi hxi using hint
  choose n hn using fun i => hy (xi i)
  set b : K := ∑ j, (n j : K) * e.traceDual j
  have htr : ∀ i, Algebra.trace ℚ K (b * e i) = n i := by
    intro i
    have hb : b * e i = ∑ j, ((n j : ℚ)) • (e.traceDual j * e i) := by
      simp only [b, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Rat.smul_def, mul_assoc]
      push_cast
      rfl
    rw [hb, map_sum]
    simp only [map_smul, Module.Basis.trace_traceDual_mul, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- `y - b` pairs to zero with the lattice basis, hence with everything
  set z := y - mixedEmbedding K b
  have hz : ∀ i, traceInf (z * latticeBasis K i) = 0 := by
    intro i
    have hsub : z * latticeBasis K i =
        y * mixedEmbedding K (xi i : K) + -(mixedEmbedding K (b * (xi i : K))) := by
      rw [latticeBasis_apply, ← hxi i, map_mul]
      simp only [z]
      ring
    rw [hsub, traceInf_add, traceInf_neg, hn i, traceInf_mixedEmbedding, hxi i, htr i]
    push_cast
    ring
  set f : mixedSpace K →ₗ[ℝ] ℝ := traceInfL.comp (LinearMap.mulLeft ℝ z)
  have hf : f = 0 := (latticeBasis K).ext fun i => by simpa [f, traceInfL] using hz i
  have hz0 : z = 0 := eq_zero_of_traceInf_mul_star z (by
    have := LinearMap.congr_fun hf (star z)
    simpa [f, traceInfL] using this)
  refine ⟨b, sub_eq_zero.mp hz0, fun x => ?_⟩
  obtain ⟨m, hm⟩ := hy x
  refine ⟨m, ?_⟩
  have h1 : traceInf (y * mixedEmbedding K (x : K)) = ((Algebra.trace ℚ K (b * x) : ℚ) : ℝ) := by
    rw [sub_eq_zero.mp hz0, ← map_mul, traceInf_mixedEmbedding]
  rw [hm] at h1
  exact_mod_cast h1.symm

/-! ### The finite places: a finite adele orthogonal to $k$ is $0$ -/

/-- If $c\in\mathbb A_k^{\mathrm{fin}}$ has $\prod_v\psi_v(c_v\xi)=1$ for every $\xi\in k$, then $c=0$: for $c_{v_0}\ne0$,
strong approximation gives $\xi$ close to $t/c_{v_0}$ at $v_0$ (with $\psi_{v_0}(t)\ne1$) and with $c_v\xi\in r_v$ at every
other $v$. -/
theorem eq_zero_of_finprod_psiV_eq_one (c : FiniteAdeleRing (𝓞 K) K)
    (h : ∀ ξ : K, ∏ᶠ v : HeightOneSpectrum (𝓞 K), psiV v (c v * algebraMap K (v.adicCompletion K) ξ) = 1) :
    c = 0 := by
  classical
  refine FiniteAdeleRing.ext K fun v0 => ?_
  change c v0 = 0
  by_contra hne
  set t := algebraMap ℚ_[resChar v0] (v0.adicCompletion K)
    (((Module.finrank ℚ_[resChar v0] (v0.adicCompletion K) : ℚ_[resChar v0]) * (resChar v0 : ℚ_[resChar v0]))⁻¹)
  have ht : psiV v0 t ≠ 1 := psiV_nontrivial v0
  set s := t / c v0
  have hfin := Filter.eventually_cofinite.mp c.2
  set S : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset ∪ {v0}
  choose k hk using fun v => exists_valued_le_exp (c v)
  obtain ⟨ξ, hξS, hξout⟩ := exists_strong_approx S
    (fun v => if hv : v = v0 then (hv ▸ s : v.adicCompletion K) else 0) (fun v => (k v : ℤ))
  have hcancel : ∀ v, exp (k v : ℤ) * exp (-(k v : ℤ)) = 1 := fun v => by
    rw [← exp_add, add_neg_cancel, exp_zero]
  have key : ∀ v, v ≠ v0 → psiV v (c v * algebraMap K (v.adicCompletion K) ξ) = 1 := by
    intro v hv
    apply psiV_eq_one_of_le_one
    rw [map_mul]
    by_cases hvS : v ∈ S
    · have h1 := hξS v hvS
      simp only [hv, dite_false, sub_zero] at h1
      exact (mul_le_mul' (hk v) h1).trans (hcancel v).le
    · have hc : Valued.v (c v) ≤ 1 := by
        by_contra hc'
        exact hvS (Finset.mem_union_left _ (hfin.mem_toFinset.mpr fun hm => hc' (valued_le_one_of_mem hm)))
      exact mul_le_one' hc (hξout v hvS)
  have h0 : psiV v0 (c v0 * algebraMap K (v0.adicCompletion K) ξ) = psiV v0 t := by
    have hsplit : c v0 * algebraMap K (v0.adicCompletion K) ξ =
        t + c v0 * (algebraMap K (v0.adicCompletion K) ξ - s) := by
      simp only [s]
      field_simp
      ring
    have h1 := hξS v0 (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    simp only [dite_true] at h1
    rw [hsplit, (psiV v0).map_add_eq_mul, psiV_eq_one_of_le_one v0 (x := c v0 * _), mul_one]
    rw [map_mul]
    exact (mul_le_mul' (hk v0) h1).trans (hcancel v0).le
  have hprod := h ξ
  rw [finprod_eq_single _ v0 key, h0] at hprod
  exact ht hprod

/-! ### Theorem 3 -/

/-- **Weil, IV.§2, Theorem 3** (p. 66), last assertion, for $E=E'=k$ with $[x,y]=xy$ and the standard character
$\chi$ (`chiA`): the annihilator of $k$ in $k_{\mathbb A}$ is $k$, i.e. $\chi(a\xi)=1$ for all $\xi\in k$ iff $a\in k$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3 (p. 66), last assertion, case E = k, number field"]
theorem weil_IV_2_thm3_annihilator (a : AdeleRing (𝓞 K) K) :
    (∀ ξ : K, chiA K (a * algebraMap K (AdeleRing (𝓞 K) K) ξ) = 1) ↔
      a ∈ Set.range (algebraMap K (AdeleRing (𝓞 K) K)) := by
  constructor
  swap
  · rintro ⟨η, rfl⟩ ξ
    rw [← map_mul]
    exact chiA_algebraMap _
  intro h
  -- Step 1: make the finite components integral
  have hfin := Filter.eventually_cofinite.mp a.2.2
  obtain ⟨ξ0, hS, hout⟩ := exists_strong_approx hfin.toFinset (fun v => a.2 v) (fun _ => 0)
  set a' := a - algebraMap K (AdeleRing (𝓞 K) K) ξ0 with ha'
  have hint : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (a'.2 v) ≤ 1 := by
    intro v
    change Valued.v (a.2 v - algebraMap K (v.adicCompletion K) ξ0) ≤ 1
    by_cases hv : v ∈ hfin.toFinset
    · have := hS v hv
      rw [neg_zero, exp_zero] at this
      rwa [Valuation.map_sub_swap]
    · have ha : Valued.v (a.2 v) ≤ 1 := by
        by_contra ha'
        exact hv (hfin.mem_toFinset.mpr fun hm => ha' (valued_le_one_of_mem hm))
      exact (Valuation.map_sub _ _ _).trans (max_le ha (hout v hv))
  have h' : ∀ ξ : K, chiA K (a' * algebraMap K (AdeleRing (𝓞 K) K) ξ) = 1 := by
    intro ξ
    have e : a * algebraMap K (AdeleRing (𝓞 K) K) ξ =
        a' * algebraMap K (AdeleRing (𝓞 K) K) ξ + algebraMap K (AdeleRing (𝓞 K) K) (ξ0 * ξ) := by
      rw [ha', map_mul]
      ring
    have := h ξ
    rwa [e, chiA_add, chiA_algebraMap, mul_one] at this
  -- Step 2: the infinite component is an element `b` of `k`
  set y := InfiniteAdeleRing.ringEquiv_mixedSpace K a'.1 with hy
  have hyint : ∀ x : 𝓞 K, ∃ n : ℤ, traceInf (y * mixedEmbedding K (x : K)) = n := by
    intro x
    have hx := h' x
    have hfin1 : chiFin K (a' * algebraMap K (AdeleRing (𝓞 K) K) (x : K)).2 = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun v => psiV_eq_one_of_le_one v ?_
      change Valued.v (a'.2 v * ((x : K) : v.adicCompletion K)) ≤ 1
      rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact mul_le_one' (hint v) (HeightOneSpectrum.valuation_le_one v x)
    unfold chiA at hx
    rw [hfin1, mul_one] at hx
    have e : InfiniteAdeleRing.ringEquiv_mixedSpace K (a' * algebraMap K (AdeleRing (𝓞 K) K) (x : K)).1 =
        y * mixedEmbedding K (x : K) := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hy, ← map_mul]
      rfl
    unfold chiInf psiInf at hx
    rw [e] at hx
    exact (fourierChar_eq_one_iff _).mp hx
  obtain ⟨b, hyb, -⟩ := exists_eq_mixedEmbedding_of_traceInf_int y hyint
  -- Step 3: the rest is a finite adele orthogonal to `k`, hence `0`
  set c := a' - algebraMap K (AdeleRing (𝓞 K) K) b with hc
  have hc1 : c.1 = 0 := by
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [map_zero]
    change InfiniteAdeleRing.ringEquiv_mixedSpace K (a'.1 - algebraMap K (InfiniteAdeleRing K) b) = 0
    rw [map_sub, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← hy, hyb, sub_self]
  have hc2 : c.2 = 0 := by
    refine eq_zero_of_finprod_psiV_eq_one c.2 fun ξ => ?_
    have e : a' * algebraMap K (AdeleRing (𝓞 K) K) ξ =
        c * algebraMap K (AdeleRing (𝓞 K) K) ξ + algebraMap K (AdeleRing (𝓞 K) K) (b * ξ) := by
      rw [hc, map_mul]
      ring
    have := h' ξ
    rw [e, chiA_add, chiA_algebraMap, mul_one] at this
    unfold chiA at this
    rw [Prod.fst_mul, hc1, zero_mul, chiInf_zero, one_mul] at this
    exact this
  have hc0 : c = 0 := Prod.ext hc1 hc2
  refine ⟨ξ0 + b, ?_⟩
  rw [map_add]
  have : a' = algebraMap K (AdeleRing (𝓞 K) K) b := by rw [← sub_eq_zero]; exact hc0
  rw [← this, ha']
  ring

end NumberFieldKB.WeilBNT

end
