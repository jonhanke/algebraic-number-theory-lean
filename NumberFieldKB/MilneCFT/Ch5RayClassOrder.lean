import NumberFieldKB.MilneCFT.Ch5RayClass
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real

/-!
# Theorem 1.7 and Example 1.8 (Milne, *Class Field Theory*, Chapter V, §1)

The exact sequence $0 \to U/U_{\mathfrak m,1} \to K_\mathfrak m/K_{\mathfrak m,1} \to C_\mathfrak m \to C \to 0$, the
canonical isomorphism $K_\mathfrak m/K_{\mathfrak m,1} \cong \prod\{\pm\}\times(\mathcal O_K/\mathfrak m_0)^\times$, the
order of the ray class group (Theorem 1.7), and the examples 1.8 (the class group, the narrow class group, the rational
ray class groups).
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## Theorem 1.7 (p. 150) -/

/-- $K_\mathfrak m = K^{S(\mathfrak m)}$ (Milne, *CFT*, V, Theorem 1.7): the $\alpha \in K^\times$ with
$\mathrm{ord}_\mathfrak p(\alpha) = 0$ for every $\mathfrak p \mid \mathfrak m_0$. -/
@[kb "milne2020cft" "Ch. V, Theorem 1.7 (the group K_m)"]
def Km (m : Modulus K) : Subgroup Kˣ := primeToS m.finiteSupport

theorem congruenceSubgroup_le_Km (m : Modulus K) : congruenceSubgroup m ≤ Km m := by
  intro a ha
  rw [Km, mem_primeToS_iff]
  intro v hv
  exact valuation_eq_one_of_sub_lt v (valuation_sub_one_lt m v hv (ha.2 v hv))

/-- The set of finite primes dividing a modulus is finite. -/
theorem finiteSupport_finite (m : Modulus K) : m.finiteSupport.Finite :=
  Ideal.finite_factors m.finite_ne_bot

/-- For $a \in K_\mathfrak m$, the principal ideal $(a)$ is trivial iff $a$ is a unit of $\mathcal O_K$
(Lemma 1.1). -/
theorem toPrincipalIdeal_eq_one_iff_Km (m : Modulus K) (a : Km m) :
    toPrincipalIdeal (𝓞 K) K (a : Kˣ) = 1 ↔ (a : Kˣ) ∈ unitsK K := by
  rw [← (lemma_1_1 m.finiteSupport (finiteSupport_finite m)).1 a, Subtype.ext_iff]
  rfl

theorem unitsK_le_Km (m : Modulus K) : unitsK K ≤ Km m := unitsK_le_primeToS _

/-- The map $K_\mathfrak m \to C_\mathfrak m$, $a \mapsto [(a)]$. -/
def kmToRay (m : Modulus K) : Km m →* RayClassGroup m :=
  (QuotientGroup.mk' _).comp ((toPrincipalIdeal (𝓞 K) K).subgroupComap (coprimeIdeals m))

/-- The map $C_\mathfrak m \to C$ induced by $I^{S(\mathfrak m)} \hookrightarrow I$. -/
def rayToClass (m : Modulus K) : RayClassGroup m →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift _ ((ClassGroup.mk K).comp (coprimeIdeals m).subtype) (by
    rintro ⟨I, hI⟩ hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨a, -, ha⟩ := hmem
    have ha' : toPrincipalIdeal (𝓞 K) K a = I := ha
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    rw [← ha', ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
    exact ⟨⟨(a : K), FractionalIdeal.coe_spanSingleton _ _⟩⟩)

/-- **Theorem 1.7**, the exact sequence (Milne, *CFT*, V, p. 150):
$0 \to U/U_{\mathfrak m,1} \to K_\mathfrak m/K_{\mathfrak m,1} \to C_\mathfrak m \to C \to 0$, where
$U_{\mathfrak m,1} = U \cap K_{\mathfrak m,1}$. Exactness at $U/U_{\mathfrak m,1}$ holds by definition of
$U_{\mathfrak m,1}$; here: the kernel of $K_\mathfrak m \to C_\mathfrak m$ is $U\cdot K_{\mathfrak m,1}$ (exactness at
$K_\mathfrak m/K_{\mathfrak m,1}$), the kernel of $C_\mathfrak m \to C$ is the image of $K_\mathfrak m$, and
$C_\mathfrak m \to C$ is onto. -/
@[kb "milne2020cft" "Ch. V, Theorem 1.7 (exact sequence)"]
theorem theorem_1_7_exact (m : Modulus K) :
    (∀ a : Km m, kmToRay m a = 1 ↔ (a : Kˣ) ∈ unitsK K ⊔ congruenceSubgroup m) ∧
      (rayToClass m).ker = (kmToRay m).range ∧ Function.Surjective (rayToClass m) := by
  have hL := lemma_1_1 m.finiteSupport (finiteSupport_finite m)
  refine ⟨fun a => ?_, ?_, ?_⟩
  · have key : kmToRay m a = 1 ↔ ∃ b ∈ congruenceSubgroup m,
        toPrincipalIdeal (𝓞 K) K b = toPrincipalIdeal (𝓞 K) K (a : Kˣ) := by
      show QuotientGroup.mk' _ _ = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, rayPrincipal,
        Subgroup.mem_map]
      rfl
    rw [key]
    constructor
    · rintro ⟨b, hb, hba⟩
      have hbK : b ∈ Km m := congruenceSubgroup_le_Km m hb
      have hu : (a : Kˣ) * b⁻¹ ∈ unitsK K :=
        (toPrincipalIdeal_eq_one_iff_Km m ⟨(a : Kˣ) * b⁻¹, mul_mem a.2 (inv_mem hbK)⟩).1
          (by simp [hba])
      have : (a : Kˣ) = ((a : Kˣ) * b⁻¹) * b := by group
      rw [this]
      exact Subgroup.mul_mem_sup hu hb
    · intro h
      obtain ⟨u, hu, b, hb, hub⟩ := Subgroup.mem_sup.1 h
      refine ⟨b, hb, ?_⟩
      have hu1 : toPrincipalIdeal (𝓞 K) K u = 1 :=
        (toPrincipalIdeal_eq_one_iff_Km m ⟨u, unitsK_le_Km m hu⟩).2 hu
      rw [← hub, map_mul, hu1, one_mul]
  · apply le_antisymm
    · intro c hc
      induction c using QuotientGroup.induction_on with
      | H I =>
        have h1 : I ∈ (sClassMap m.finiteSupport).ker := hc
        rw [hL.2.1] at h1
        obtain ⟨a, ha⟩ := h1
        exact ⟨a, by
          show QuotientGroup.mk' _ _ = _
          rw [QuotientGroup.mk'_apply]
          congr 1⟩
    · rintro _ ⟨a, rfl⟩
      have h : sPrincipal m.finiteSupport a ∈ (sClassMap m.finiteSupport).ker := hL.2.1 ▸ ⟨a, rfl⟩
      exact h
  · intro c
    obtain ⟨I, hI⟩ := hL.2.2 c
    exact ⟨QuotientGroup.mk I, hI⟩

/-! ### Weak approximation at the real places -/

section Approximation

open NumberField.InfinitePlace

/-- Weak approximation at finitely many real places: a number field element whose embeddings at the given
real places are within $1$ of the prescribed real numbers. -/
theorem exists_real_approx (T : Finset (InfinitePlace K)) (hT : ∀ v ∈ T, v.IsReal)
    (t : InfinitePlace K → ℝ) :
    ∃ y : K, ∀ (v : InfinitePlace K) (hv : v ∈ T), |embedding_of_isReal (hT v hv) y - t v| < 1 := by
  classical
  let A : InfinitePlace K → Set (InfiniteAdeleRing K) := fun v =>
    {z | ∀ h : v.IsReal, |Completion.extensionEmbeddingOfIsReal h (z v) - t v| < 1}
  have hA : ∀ v, IsOpen (A v) := by
    intro v
    by_cases h : v.IsReal
    · have hc : Continuous fun z : InfiniteAdeleRing K =>
          |Completion.extensionEmbeddingOfIsReal h (z v) - t v| :=
        (((Completion.isometry_extensionEmbeddingOfIsReal h).continuous.comp
          (continuous_apply v)).sub continuous_const).abs
      have : A v = (fun z : InfiniteAdeleRing K =>
          |Completion.extensionEmbeddingOfIsReal h (z v) - t v|) ⁻¹' Set.Iio 1 := by
        ext z
        exact ⟨fun hz => hz h, fun hz _ => hz⟩
      rw [this]
      exact isOpen_Iio.preimage hc
    · have : A v = Set.univ := by
        ext z
        exact ⟨fun _ => trivial, fun _ h' => absurd h' h⟩
      rw [this]
      exact isOpen_univ
  have hU : IsOpen (⋂ v ∈ T, A v) := isOpen_biInter_finset fun v _ => hA v
  let z0 : InfiniteAdeleRing K := fun v =>
    if h : v.IsReal then (Completion.ringEquivRealOfIsReal h).symm (t v) else 0
  have hz0 : z0 ∈ ⋂ v ∈ T, A v := by
    simp only [Set.mem_iInter]
    intro v _ h
    have h0 : z0 v = (Completion.ringEquivRealOfIsReal h).symm (t v) := by
      simp [z0, h]
    have := (Completion.ringEquivRealOfIsReal h).apply_symm_apply (t v)
    rw [Completion.ringEquivRealOfIsReal_apply] at this
    rw [h0, this]
    simp
  obtain ⟨y, hy⟩ := (InfiniteAdeleRing.denseRange_algebraMap K).exists_mem_open hU ⟨z0, hz0⟩
  refine ⟨y, fun v hv => ?_⟩
  have := (Set.mem_iInter₂.1 hy) v hv (hT v hv)
  simpa using this

theorem signAt_eq_of_mul_pos (v : InfinitePlace K) (hv : v.IsReal) (a : K) (ε : ℤˣ)
    (h : 0 < ((ε : ℤ) : ℝ) * embedding_of_isReal hv a) : signAt v hv a = ε := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · have : 0 < embedding_of_isReal hv a := by simpa using h
    simp [signAt, this]
  · have : embedding_of_isReal hv a < 0 := by simpa using h
    simp [signAt, not_lt.2 this.le]

/-- An element of a number field has a positive integer multiple that is integral. -/
theorem exists_pos_nat_mul_mem (y : K) : ∃ (d : ℕ) (w : 𝓞 K), 0 < d ∧ (w : K) = d * y := by
  have hy : IsAlgebraic ℤ y := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ y)
  obtain ⟨d, w, hd, hw⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 K) hy
  exact ⟨d, w, Nat.pos_of_ne_zero hd, by
    have : ((w : 𝓞 K) : K) = algebraMap (𝓞 K) K w := rfl
    rw [this, ← hw]; simp⟩

/-- Given a residue class mod $\mathfrak m_0$ and signs at the real places of $\mathfrak m_\infty$ there is a
nonzero integral element in the class with these signs (weak approximation). -/
theorem exists_sign_residue (m : Modulus K) (ε : m.infinite → ℤˣ) (x : 𝓞 K) :
    ∃ z : 𝓞 K, z - x ∈ m.finite ∧ z ≠ 0 ∧ ∀ (v : InfinitePlace K) (hv : v ∈ m.infinite),
      signAt v (m.isReal_of_mem v hv) (algebraMap (𝓞 K) K z) = ε ⟨v, hv⟩ := by
  classical
  let T : Finset (InfinitePlace K) := (Set.toFinite m.infinite).toFinset
  have hT : ∀ v ∈ T, v.IsReal := fun v hv =>
    m.isReal_of_mem v ((Set.Finite.mem_toFinset _).1 hv)
  let t : InfinitePlace K → ℝ := fun v =>
    if h : v ∈ m.infinite then ((ε ⟨v, h⟩ : ℤ) : ℝ) *
      (|embedding_of_isReal (m.isReal_of_mem v h) (algebraMap (𝓞 K) K x)| + 2) else 0
  obtain ⟨y, hy⟩ := exists_real_approx T hT t
  obtain ⟨d, w, hd, hw⟩ := exists_pos_nat_mul_mem y
  set n : ℕ := Ideal.absNorm m.finite with hn_def
  have hn : 0 < n := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 m.finite_ne_bot)
  have hnm : (n : 𝓞 K) ∈ m.finite := Ideal.absNorm_mem m.finite
  have key : ∀ (v : InfinitePlace K) (hv : v ∈ m.infinite),
      0 < ((ε ⟨v, hv⟩ : ℤ) : ℝ) *
        embedding_of_isReal (m.isReal_of_mem v hv) (algebraMap (𝓞 K) K (x + (n : 𝓞 K) * w)) := by
    intro v hv
    have hvT : v ∈ T := (Set.Finite.mem_toFinset _).2 hv
    have hyv := hy v hvT
    have ht : t v = ((ε ⟨v, hv⟩ : ℤ) : ℝ) *
        (|embedding_of_isReal (m.isReal_of_mem v hv) (algebraMap (𝓞 K) K x)| + 2) := by
      simp [t, hv]
    set σ := embedding_of_isReal (m.isReal_of_mem v hv) with hσ
    set e : ℝ := ((ε ⟨v, hv⟩ : ℤ) : ℝ) with he
    have he1 : e * e = 1 := by
      rcases Int.units_eq_one_or (ε ⟨v, hv⟩) with h | h <;> simp [he, h]
    have heabs : |e| = 1 := by
      rcases Int.units_eq_one_or (ε ⟨v, hv⟩) with h | h <;> simp [he, h]
    set sx := σ (algebraMap (𝓞 K) K x) with hsx
    have h1 : |e * (σ y - t v)| < 1 := by
      rw [abs_mul, heabs, one_mul]
      exact hyv
    have h1' : e * σ y > |sx| + 1 := by
      have : e * (σ y - t v) = e * σ y - (|sx| + 2) := by
        rw [ht]; linear_combination (-(|sx| + 2)) * he1
      rw [this] at h1
      have := (abs_lt.1 h1).1
      linarith
    have h2 : -|sx| ≤ e * sx := by
      have := neg_abs_le (e * sx)
      rwa [abs_mul, heabs, one_mul] at this
    have hnd : (1 : ℝ) ≤ (n : ℝ) * (d : ℝ) := by
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h2 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith
    have hz : σ (algebraMap (𝓞 K) K (x + (n : 𝓞 K) * w)) = sx + n * (d * σ y) := by
      have : algebraMap (𝓞 K) K (x + (n : 𝓞 K) * w) = algebraMap (𝓞 K) K x + n * (d * y) := by
        rw [map_add, map_mul, map_natCast]
        have : algebraMap (𝓞 K) K w = (d : K) * y := hw
        rw [this]
      rw [this]; simp [hsx]
    rw [hz]
    nlinarith [mul_nonneg (sub_nonneg.2 hnd) (le_of_lt (lt_trans (by positivity : (0:ℝ) < |sx| + 1) h1'))]
  by_cases hz : x + (n : 𝓞 K) * w = 0
  · by_cases hne : m.infinite.Nonempty
    · obtain ⟨v, hv⟩ := hne
      have := key v hv
      rw [hz] at this
      simp at this
    · refine ⟨(n : 𝓞 K), ?_, Nat.cast_ne_zero.2 hn.ne', fun v hv => absurd ⟨v, hv⟩ hne⟩
      have h0 : x = -((n : 𝓞 K) * w) := by linear_combination hz
      rw [h0]
      have : (n : 𝓞 K) + (n : 𝓞 K) * w ∈ m.finite :=
        Ideal.add_mem _ hnm (Ideal.mul_mem_right _ _ hnm)
      convert this using 1
      ring
  · refine ⟨x + (n : 𝓞 K) * w, ?_, hz, fun v hv => signAt_eq_of_mul_pos _ _ _ _ (key v hv)⟩
    rw [add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ hnm

end Approximation

/-! ### The residue map $K_\mathfrak m \to (\mathcal O_K/\mathfrak m_0)^\times$ -/

section Residue

theorem algMap_ne_zero {b : 𝓞 K} (hb : b ≠ 0) : algebraMap (𝓞 K) K b ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hb

/-- An element of $\mathcal O_K$ outside every prime dividing $\mathfrak m_0$ is a unit modulo $\mathfrak m_0$. -/
theorem isUnit_mk_of_not_mem (m : Modulus K) (x : 𝓞 K)
    (hx : ∀ v ∈ m.finiteSupport, x ∉ v.asIdeal) : IsUnit (Ideal.Quotient.mk m.finite x) := by
  by_cases htop : Ideal.span {x} ⊔ m.finite = ⊤
  · have h1 : (1 : 𝓞 K) ∈ Ideal.span {x} ⊔ m.finite := htop ▸ Submodule.mem_top
    obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.1 h1
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk m.finite a) ?_
    have h2 : a * x = 1 - b := by linear_combination hab
    have h3 : Ideal.Quotient.mk m.finite b = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
    rw [← map_mul, mul_comm, h2, map_sub, map_one, h3, sub_zero]
  · exfalso
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ htop
    have hMne : M ≠ ⊥ := fun h => m.finite_ne_bot
      (le_bot_iff.1 (by rw [← h]; exact le_trans le_sup_right hle))
    let v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hMne⟩
    have hv : v ∈ m.finiteSupport := (Ideal.dvd_iff_le).2 (le_trans le_sup_right hle)
    exact hx v hv (hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)))

/-- Conversely, a unit modulo $\mathfrak m_0$ lies in no prime dividing $\mathfrak m_0$. -/
theorem not_mem_of_isUnit_mk (m : Modulus K) (x : 𝓞 K) (hx : IsUnit (Ideal.Quotient.mk m.finite x))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ m.finiteSupport) : x ∉ v.asIdeal := by
  intro hxv
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk m.finite), Ideal.Quotient.eq] at hy
  have h1 : x * y - 1 ∈ v.asIdeal := (Ideal.dvd_iff_le.1 hv) hy
  have h2 : (1 : 𝓞 K) ∈ v.asIdeal := by
    have := v.asIdeal.sub_mem (v.asIdeal.mul_mem_right y hxv) h1
    simpa using this
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

/-- The class of an integral element prime to $\mathfrak m_0$, as a unit of $\mathcal O_K/\mathfrak m_0$. -/
def resUnit (m : Modulus K) (x : 𝓞 K) (hx : ∀ v ∈ m.finiteSupport, x ∉ v.asIdeal) :
    (𝓞 K ⧸ m.finite)ˣ :=
  (isUnit_mk_of_not_mem m x hx).unit

@[simp] theorem coe_resUnit (m : Modulus K) (x : 𝓞 K) (hx : ∀ v ∈ m.finiteSupport, x ∉ v.asIdeal) :
    ((resUnit m x hx : (𝓞 K ⧸ m.finite)ˣ) : 𝓞 K ⧸ m.finite) = Ideal.Quotient.mk m.finite x := rfl

theorem mul_not_mem {m : Modulus K} {x y : 𝓞 K} (hx : ∀ v ∈ m.finiteSupport, x ∉ v.asIdeal)
    (hy : ∀ v ∈ m.finiteSupport, y ∉ v.asIdeal) : ∀ v ∈ m.finiteSupport, x * y ∉ v.asIdeal :=
  fun v hv h => (v.isPrime.mem_or_mem h).elim (hx v hv) (hy v hv)

theorem resUnit_mul (m : Modulus K) {x y : 𝓞 K} (hx : ∀ v ∈ m.finiteSupport, x ∉ v.asIdeal)
    (hy : ∀ v ∈ m.finiteSupport, y ∉ v.asIdeal) :
    resUnit m (x * y) (mul_not_mem hx hy) = resUnit m x hx * resUnit m y hy :=
  Units.ext (by simp)

/-- $a/b$ is a representation of $\alpha$ by integral elements prime to $\mathfrak m_0$ (Lemma 1.5). -/
def IsRep (m : Modulus K) (α : Kˣ) (a b : 𝓞 K) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ (∀ v ∈ m.finiteSupport, a ∉ v.asIdeal ∧ b ∉ v.asIdeal) ∧
    ((α : Kˣ) : K) = algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b

theorem exists_rep (m : Modulus K) (α : Km m) : ∃ a b : 𝓞 K, IsRep m (α : Kˣ) a b :=
  lemma_1_5 m.finiteSupport (finiteSupport_finite m) α

theorem IsRep.num_not_mem {m : Modulus K} {α : Kˣ} {a b : 𝓞 K} (h : IsRep m α a b) :
    ∀ v ∈ m.finiteSupport, a ∉ v.asIdeal := fun v hv => (h.2.2.1 v hv).1

theorem IsRep.den_not_mem {m : Modulus K} {α : Kˣ} {a b : 𝓞 K} (h : IsRep m α a b) :
    ∀ v ∈ m.finiteSupport, b ∉ v.asIdeal := fun v hv => (h.2.2.1 v hv).2

/-- The chosen numerator of an element of $K_\mathfrak m$. -/
def repNum (m : Modulus K) (α : Km m) : 𝓞 K := Classical.choose (exists_rep m α)

/-- The chosen denominator of an element of $K_\mathfrak m$. -/
def repDen (m : Modulus K) (α : Km m) : 𝓞 K :=
  Classical.choose (Classical.choose_spec (exists_rep m α))

theorem repSpec (m : Modulus K) (α : Km m) : IsRep m (α : Kˣ) (repNum m α) (repDen m α) :=
  Classical.choose_spec (Classical.choose_spec (exists_rep m α))

/-- The residue map $K_\mathfrak m \to (\mathcal O_K/\mathfrak m_0)^\times$, $a/b \mapsto [a][b]^{-1}$ (as a
function; `psiHom` is the homomorphism). -/
def psi (m : Modulus K) (α : Km m) : (𝓞 K ⧸ m.finite)ˣ :=
  resUnit m _ (repSpec m α).num_not_mem / resUnit m _ (repSpec m α).den_not_mem

theorem psi_eq (m : Modulus K) (α : Km m) {a b : 𝓞 K} (h : IsRep m (α : Kˣ) a b) :
    psi m α = resUnit m a h.num_not_mem / resUnit m b h.den_not_mem := by
  have h0 := repSpec m α
  unfold psi
  rw [div_eq_div_iff_mul_eq_mul]
  have hK : algebraMap (𝓞 K) K (repNum m α) * algebraMap (𝓞 K) K b =
      algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K (repDen m α) := by
    have e1 := h0.2.2.2
    have e2 := h.2.2.2
    rw [e1, div_eq_div_iff (algMap_ne_zero h0.2.1) (algMap_ne_zero h.2.1)] at e2
    exact e2
  have hO : repNum m α * b = a * repDen m α := by
    apply (IsFractionRing.injective (𝓞 K) K)
    simpa using hK
  apply Units.ext
  simp only [Units.val_mul, coe_resUnit, ← map_mul, hO]

/-- $\psi$ is multiplicative. -/
def psiHom (m : Modulus K) : Km m →* (𝓞 K ⧸ m.finite)ˣ where
  toFun := psi m
  map_one' := by
    have h : IsRep m ((1 : Km m) : Kˣ) 1 1 := by
      refine ⟨one_ne_zero, one_ne_zero, fun v _ => ⟨?_, ?_⟩, by simp⟩ <;>
        exact fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    rw [psi_eq m 1 h]
    apply Units.ext
    simp
  map_mul' := by
    intro α β
    have h1 := repSpec m α
    have h2 := repSpec m β
    have h : IsRep m ((α * β : Km m) : Kˣ) (repNum m α * repNum m β) (repDen m α * repDen m β) := by
      refine ⟨mul_ne_zero h1.1 h2.1, mul_ne_zero h1.2.1 h2.2.1, fun v hv => ⟨mul_not_mem h1.num_not_mem h2.num_not_mem v hv,
        mul_not_mem h1.den_not_mem h2.den_not_mem v hv⟩, ?_⟩
      show ((α : Kˣ) : K) * ((β : Kˣ) : K) = _
      rw [h1.2.2.2, h2.2.2.2]
      simp only [map_mul]
      rw [div_mul_div_comm]
    rw [psi_eq m _ h, resUnit_mul, resUnit_mul, psi, psi]
    simp only [div_eq_mul_inv, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

end Residue

/-! ### The sign maps and the kernel -/

section Iso

open NumberField.InfinitePlace

theorem signAt_mul (v : InfinitePlace K) (hv : v.IsReal) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    signAt v hv (x * y) = signAt v hv x * signAt v hv y := by
  have hx' : embedding_of_isReal hv x ≠ 0 := (map_ne_zero _).2 hx
  have hy' : embedding_of_isReal hv y ≠ 0 := (map_ne_zero _).2 hy
  unfold signAt
  rw [map_mul]
  rcases lt_or_gt_of_ne hx' with h1 | h1 <;> rcases lt_or_gt_of_ne hy' with h2 | h2
  · simp [not_lt.2 h1.le, not_lt.2 h2.le, mul_pos_of_neg_of_neg h1 h2]
  · simp [not_lt.2 h1.le, h2, not_lt.2 (mul_neg_of_neg_of_pos h1 h2).le]
  · simp [h1, not_lt.2 h2.le, not_lt.2 (mul_neg_of_pos_of_neg h1 h2).le]
  · simp [h1, h2, mul_pos h1 h2]

theorem signAt_eq_one_iff (v : InfinitePlace K) (hv : v.IsReal) (a : K) :
    signAt v hv a = 1 ↔ 0 < embedding_of_isReal hv a := by
  unfold signAt
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

/-- The sign of an element of $K^\times$ at a real place, as a homomorphism to $\{\pm 1\}$. -/
def signHom (v : InfinitePlace K) (hv : v.IsReal) : Kˣ →* ℤˣ where
  toFun a := signAt v hv (a : K)
  map_one' := by simp [signAt]
  map_mul' a b := by
    simp only [Units.val_mul]
    exact signAt_mul v hv a.ne_zero b.ne_zero

theorem pow_ord_dvd (m : Modulus K) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ^ m.ord v ∣ m.finite := by
  have hne : (Associates.mk m.finite) ≠ 0 := Associates.mk_ne_zero.2 m.finite_ne_bot
  have h := (Associates.prime_pow_dvd_iff_le (k := m.ord v) hne v.associates_irreducible).2 le_rfl
  exact Associates.mk_le_mk_iff_dvd.1 (by rwa [Associates.mk_pow])

/-- $x \in \mathfrak m_0$ iff $x \in \mathfrak p^{\mathfrak m(\mathfrak p)}$ for every prime $\mathfrak p \mid \mathfrak m_0$. -/
theorem mem_finite_iff (m : Modulus K) (x : 𝓞 K) :
    x ∈ m.finite ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.finite →
      x ∈ v.asIdeal ^ m.ord v := by
  classical
  constructor
  · intro hx v _
    exact Ideal.dvd_iff_le.1 (pow_ord_dvd m v) hx
  · intro h
    rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_mem _
    have hx' : (Ideal.span {x} : Ideal (𝓞 K)) ≠ 0 := by simpa using hx0
    have hm' := m.finite_ne_bot
    rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le,
      UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hm' hx',
      Multiset.le_iff_count]
    intro p
    by_cases hp : p ∈ UniqueFactorizationMonoid.normalizedFactors m.finite
    · have hpp : Prime p := UniqueFactorizationMonoid.prime_of_normalized_factor p hp
      have hpr : p.IsPrime := Ideal.isPrime_of_prime hpp
      let v : HeightOneSpectrum (𝓞 K) := ⟨p, hpr, hpp.ne_zero⟩
      have hv : v.asIdeal ∣ m.finite := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp
      have h1 := (v.intValuation_le_pow_iff_mem x (m.ord v)).2 (h v hv)
      rw [v.intValuation_if_neg hx0, WithZero.exp_le_exp, neg_le_neg_iff, Int.ofNat_le,
        Ideal.count_associates_factors_eq hx' hpr hpp.ne_zero] at h1
      have h2 : m.ord v = Multiset.count p (UniqueFactorizationMonoid.normalizedFactors m.finite) :=
        Ideal.count_associates_factors_eq hm' hpr hpp.ne_zero
      rw [← h2]; exact h1
    · rw [Multiset.count_eq_zero_of_notMem hp]; exact Nat.zero_le _

theorem psi_eq_one_iff (m : Modulus K) (α : Km m) :
    psi m α = 1 ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.finite →
      v.valuation K (((α : Kˣ) : K) - 1) ≤ WithZero.exp (-(m.ord v : ℤ)) := by
  obtain ⟨a, b, h⟩ : ∃ a b : 𝓞 K, IsRep m (α : Kˣ) a b := exists_rep m α
  rw [psi_eq m α h, div_eq_one]
  have e1 : resUnit m a h.num_not_mem = resUnit m b h.den_not_mem ↔ a - b ∈ m.finite := by
    rw [Units.ext_iff, coe_resUnit, coe_resUnit, Ideal.Quotient.eq]
  rw [e1, mem_finite_iff]
  refine forall_congr' fun v => imp_congr_right fun hv => ?_
  have hb : b ∉ v.asIdeal := h.den_not_mem v hv
  have hK : ((α : Kˣ) : K) - 1 = algebraMap (𝓞 K) K (a - b) / algebraMap (𝓞 K) K b := by
    have hb0 := algMap_ne_zero h.2.1
    rw [h.2.2.2, map_sub]
    field_simp
  rw [hK, map_div₀, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) _).2 hb, div_one,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]

/-- The map $K_\mathfrak m \to \prod_{v \in \mathfrak m_\infty}\{\pm 1\} \times (\mathcal O_K/\mathfrak m_0)^\times$ of
Theorem 1.7. -/
def isoMap (m : Modulus K) : Km m →* (m.infinite → ℤˣ) × (𝓞 K ⧸ m.finite)ˣ :=
  (MonoidHom.pi fun v : m.infinite =>
    (signHom v.1 (m.isReal_of_mem v.1 v.2)).comp (Km m).subtype).prod (psiHom m)

theorem isoMap_integral (m : Modulus K) (α : Km m) (x : 𝓞 K)
    (hx : ((α : Kˣ) : K) = algebraMap (𝓞 K) K x) :
    (isoMap m α).1 = (fun v : m.infinite =>
        signAt v.1 (m.isReal_of_mem v.1 v.2) (algebraMap (𝓞 K) K x)) ∧
      (((isoMap m α).2 : (𝓞 K ⧸ m.finite)ˣ) : 𝓞 K ⧸ m.finite) = Ideal.Quotient.mk m.finite x := by
  refine ⟨funext fun v => ?_, ?_⟩
  · show signAt v.1 _ ((α : Kˣ) : K) = _
    rw [hx]
  · have hnot : ∀ v ∈ m.finiteSupport, x ∉ v.asIdeal := fun v hv =>
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) _).1
        (hx ▸ (mem_primeToS_iff _ _).1 α.2 v hv)
    have hx0 : x ≠ 0 := by
      intro h0
      apply (α : Kˣ).ne_zero
      rw [hx, h0, map_zero]
    have hrep : IsRep m (α : Kˣ) x 1 := by
      refine ⟨hx0, one_ne_zero, fun v hv => ⟨hnot v hv, ?_⟩, by simp [hx]⟩
      exact fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    show ((psi m α : (𝓞 K ⧸ m.finite)ˣ) : 𝓞 K ⧸ m.finite) = _
    have h1 : resUnit m 1 hrep.den_not_mem = 1 := Units.ext (by simp)
    rw [psi_eq m α hrep, h1, div_one]
    rfl

theorem isoMap_ker (m : Modulus K) :
    (isoMap m).ker = (congruenceSubgroup m).subgroupOf (Km m) := by
  ext α
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Prod.ext_iff]
  have hp : (isoMap m α).2 = psi m α := rfl
  have hs : ∀ v : m.infinite, (isoMap m α).1 v =
      signAt v.1 (m.isReal_of_mem v.1 v.2) ((α : Kˣ) : K) := fun v => rfl
  simp only [hp, Prod.fst_one, Prod.snd_one, funext_iff, hs, Pi.one_apply, psi_eq_one_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun v hv => (signAt_eq_one_iff _ _ _).1 (h1 ⟨v, hv⟩), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun v => (signAt_eq_one_iff _ _ _).2 (h1 v.1 v.2), h2⟩

theorem isoMap_surjective (m : Modulus K) : Function.Surjective (isoMap m) := by
  rintro ⟨ε, r⟩
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (r : 𝓞 K ⧸ m.finite)
  have hxu : IsUnit (Ideal.Quotient.mk m.finite x) := by rw [hx]; exact r.isUnit
  obtain ⟨z, hz, hz0, hzs⟩ := exists_sign_residue m ε x
  have hmk : Ideal.Quotient.mk m.finite z = Ideal.Quotient.mk m.finite x :=
    Ideal.Quotient.eq.2 hz
  have hzS : ∀ v ∈ m.finiteSupport, z ∉ v.asIdeal := fun v hv =>
    not_mem_of_isUnit_mk m z (hmk ▸ hxu) v hv
  have hmem : Units.mk0 (algebraMap (𝓞 K) K z) (algMap_ne_zero hz0) ∈ Km m := by
    rw [Km, mem_primeToS_iff]
    intro v hv
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) _).2 (hzS v hv)
  obtain ⟨h1, h2⟩ := isoMap_integral m ⟨_, hmem⟩ z rfl
  refine ⟨⟨_, hmem⟩, Prod.ext ?_ ?_⟩
  · rw [h1]
    funext v
    exact hzs v.1 v.2
  · apply Units.ext
    rw [h2, hmk, hx]

end Iso

/-- **Theorem 1.7**, the canonical isomorphism (Milne, *CFT*, V, p. 150):
$K_\mathfrak m/K_{\mathfrak m,1} \cong \prod_{v \mid \mathfrak m_\infty}\{\pm\} \times (\mathcal O_K/\mathfrak m_0)^\times$.
Here: a surjective homomorphism $K_\mathfrak m \to \prod_{v \in \mathfrak m_\infty}\{\pm 1\} \times
(\mathcal O_K/\mathfrak m_0)^\times$ with kernel $K_{\mathfrak m,1}$, sending an integral $a \in K_\mathfrak m$ to
(its signs, its residue class); since every element of $K_\mathfrak m$ is a quotient of integral ones (Lemma 1.5),
this determines the map. -/
@[kb "milne2020cft" "Ch. V, Theorem 1.7 (K_m/K_{m,1} ≅ ∏ {±} × (O_K/m_0)^×)"]
theorem theorem_1_7_iso (m : Modulus K) :
    ∃ φ : Km m →* (m.infinite → ℤˣ) × (𝓞 K ⧸ m.finite)ˣ, Function.Surjective φ ∧
      φ.ker = (congruenceSubgroup m).subgroupOf (Km m) ∧
      ∀ (a : Km m) (x : 𝓞 K), ((a : Kˣ) : K) = algebraMap (𝓞 K) K x →
        (φ a).1 = (fun v => signAt v.1 (m.isReal_of_mem v.1 v.2) (algebraMap (𝓞 K) K x)) ∧
          (((φ a).2 : 𝓞 K ⧸ m.finite) = Ideal.Quotient.mk m.finite x) :=
  ⟨isoMap m, isoMap_surjective m, isoMap_ker m, fun a x hx => isoMap_integral m a x hx⟩

/-- **Theorem 1.7**, the Chinese remainder isomorphism (Milne, *CFT*, V, p. 150):
$(\mathcal O_K/\mathfrak m_0)^\times \cong \prod_{\mathfrak p \mid \mathfrak m_0}(\mathcal O_K/\mathfrak p^{\mathfrak m(\mathfrak p)})^\times$
(Mathlib's ring isomorphism `IsDedekindDomain.quotientEquivPiFactors`, on units). -/
@[kb "milne2020cft" "Ch. V, Theorem 1.7 ((O_K/m_0)^× ≅ ∏ (O_K/p^m(p))^×)"]
def theorem_1_7_crt (m : Modulus K) :
    (𝓞 K ⧸ m.finite)ˣ ≃* ∀ P : (UniqueFactorizationMonoid.factors m.finite).toFinset,
      (𝓞 K ⧸ (P : Ideal (𝓞 K)) ^ (Multiset.count ↑P (UniqueFactorizationMonoid.factors m.finite)))ˣ :=
  (Units.mapEquiv (IsDedekindDomain.quotientEquivPiFactors m.finite_ne_bot).toMulEquiv).trans
    MulEquiv.piUnits

/-! ### Counting units modulo $\mathfrak m_0$ -/

section Counting

theorem natCard_quotient (I : Ideal (𝓞 K)) : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- The number of units of $\mathcal O_K/\mathfrak p^e$ is $N\mathfrak p^e - N\mathfrak p^{e-1}$ for $e \ge 1$. -/
theorem card_units_quotient_pow (P : Ideal (𝓞 K)) (hPp : P.IsPrime) (hP : P ≠ ⊥) {e : ℕ}
    (he : 0 < e) :
    Nat.card (𝓞 K ⧸ P ^ e)ˣ = Ideal.absNorm P ^ e - Ideal.absNorm P ^ (e - 1) := by
  classical
  have hmax : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP hPp
  have hle : P ^ e ≤ P := Ideal.pow_le_self he.ne'
  set f : (𝓞 K ⧸ P ^ e) →+* (𝓞 K ⧸ P) := Ideal.Quotient.factor hle with hf
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ r, rfl⟩
  have : Finite (𝓞 K ⧸ P ^ e) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero e hP)
  have : Nontrivial (𝓞 K ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hPp.ne_top
  have hunit : ∀ x : 𝓞 K ⧸ P ^ e, IsUnit x ↔ f x ≠ 0 := by
    intro x
    constructor
    · intro hx
      exact (hx.map f).ne_zero
    · intro hx
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hr : r ∉ P := by
        intro h
        apply hx
        rw [hf, Ideal.Quotient.factor_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.2 h
      have hlt : P < P ⊔ Ideal.span {r} := lt_of_le_of_ne le_sup_left (fun h => hr (by
        rw [h]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self r)))
      have htop : P ⊔ Ideal.span {r} = ⊤ := hmax.out.2 _ hlt
      have hcop : IsCoprime (P ^ e) (Ideal.span {r}) :=
        (Ideal.isCoprime_iff_sup_eq.2 htop).pow_left
      have h1 : (1 : 𝓞 K) ∈ Ideal.span {r} ⊔ P ^ e := by
        rw [sup_comm, Ideal.isCoprime_iff_sup_eq.1 hcop]; exact Submodule.mem_top
      obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.1 h1
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk (P ^ e) a) ?_
      have h2 : a * r = 1 - b := by linear_combination hab
      have h3 : Ideal.Quotient.mk (P ^ e) b = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
      rw [← map_mul, mul_comm, h2, map_sub, map_one, h3, sub_zero]
  have hcard1 : Nat.card (𝓞 K ⧸ P ^ e)ˣ = Nat.card {x : 𝓞 K ⧸ P ^ e // f x ≠ 0} :=
    Nat.card_congr
      { toFun := fun u => ⟨u, (hunit u).1 u.isUnit⟩
        invFun := fun x => ((hunit x.1).2 x.2).unit
        left_inv := fun u => Units.ext rfl
        right_inv := fun x => Subtype.ext rfl }
  have hcard2 : Nat.card {x : 𝓞 K ⧸ P ^ e // f x ≠ 0} + Nat.card {x : 𝓞 K ⧸ P ^ e // f x = 0} =
      Nat.card (𝓞 K ⧸ P ^ e) := by
    rw [← Nat.card_sum]
    exact Nat.card_congr ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun x : 𝓞 K ⧸ P ^ e => f x = 0)))
  have hker : Nat.card {x : 𝓞 K ⧸ P ^ e // f x = 0} = Nat.card f.toAddMonoidHom.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp)
  have hA : Nat.card (𝓞 K ⧸ P ^ e) = Nat.card (𝓞 K ⧸ P) * Nat.card f.toAddMonoidHom.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.toAddMonoidHom.ker]
    congr 1
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f.toAddMonoidHom hsurj).toEquiv
  rw [natCard_quotient, natCard_quotient, map_pow] at hA
  have hNpos : 0 < Ideal.absNorm P := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 hP)
  have hkerval : Nat.card f.toAddMonoidHom.ker = Ideal.absNorm P ^ (e - 1) := by
    have : Ideal.absNorm P * Nat.card f.toAddMonoidHom.ker =
        Ideal.absNorm P * Ideal.absNorm P ^ (e - 1) := by
      rw [← hA, ← pow_succ']
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left hNpos this
  rw [natCard_quotient, map_pow] at hcard2
  rw [hcard1]
  omega

theorem absNorm_eq_prod (m : Modulus K) :
    Ideal.absNorm m.finite = ∏ P ∈ (UniqueFactorizationMonoid.factors m.finite).toFinset,
      Ideal.absNorm P ^ Multiset.count P (UniqueFactorizationMonoid.factors m.finite) := by
  have h : (UniqueFactorizationMonoid.factors m.finite).prod = m.finite :=
    associated_iff_eq.1 (UniqueFactorizationMonoid.factors_prod m.finite_ne_bot)
  conv_lhs => rw [← h]
  rw [map_multiset_prod, Finset.prod_multiset_map_count]

theorem natCard_units_finite (m : Modulus K) :
    Nat.card (𝓞 K ⧸ m.finite)ˣ =
      ∏ P ∈ (UniqueFactorizationMonoid.factors m.finite).toFinset,
        (Ideal.absNorm P ^ Multiset.count P (UniqueFactorizationMonoid.factors m.finite) -
          Ideal.absNorm P ^ (Multiset.count P (UniqueFactorizationMonoid.factors m.finite) - 1)) := by
  rw [Nat.card_congr (theorem_1_7_crt m).toEquiv, Nat.card_pi]
  rw [Finset.prod_coe_sort (UniqueFactorizationMonoid.factors m.finite).toFinset
    (fun P => Nat.card (𝓞 K ⧸ P ^ Multiset.count P (UniqueFactorizationMonoid.factors m.finite))ˣ)]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hmem := Multiset.mem_toFinset.1 hP
  have hprime : Prime P := UniqueFactorizationMonoid.prime_of_factor P hmem
  exact card_units_quotient_pow P (Ideal.isPrime_of_prime hprime) hprime.ne_zero
    (Multiset.count_pos.2 hmem)

theorem natCard_units_finite_rat (m : Modulus K) :
    (Nat.card (𝓞 K ⧸ m.finite)ˣ : ℚ) = (Ideal.absNorm m.finite : ℚ) *
      ∏ P ∈ (UniqueFactorizationMonoid.factors m.finite).toFinset, (1 - 1 / (Ideal.absNorm P : ℚ)) := by
  rw [natCard_units_finite, absNorm_eq_prod, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hmem := Multiset.mem_toFinset.1 hP
  have hprime : Prime P := UniqueFactorizationMonoid.prime_of_factor P hmem
  have hNpos : 0 < Ideal.absNorm P :=
    Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 hprime.ne_zero)
  have he := Multiset.count_pos.2 hmem
  obtain ⟨k, hk⟩ : ∃ k, Multiset.count P (UniqueFactorizationMonoid.factors m.finite) = k + 1 :=
    ⟨Multiset.count P (UniqueFactorizationMonoid.factors m.finite) - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel]
  rw [Nat.cast_sub (Nat.pow_le_pow_right hNpos (Nat.le_add_right k 1))]
  have : (Ideal.absNorm P : ℚ) ≠ 0 := by exact_mod_cast hNpos.ne'
  push_cast
  field_simp
  ring

end Counting

/-- **Theorem 1.7**, the order of $C_\mathfrak m$ (Milne, *CFT*, V, p. 150): $C_\mathfrak m$ is finite, of order
$h_\mathfrak m = h\,(U : U_{\mathfrak m,1})^{-1}\,2^{r_0}\,N(\mathfrak m_0)\prod_{\mathfrak p \mid \mathfrak m_0}
(1 - 1/N\mathfrak p)$, $r_0$ the number of real primes dividing $\mathfrak m$. -/
@[kb "milne2020cft" "Ch. V, Theorem 1.7 (the order h_m of C_m)"]
theorem theorem_1_7_card (m : Modulus K) :
    Finite (RayClassGroup m) ∧ (Nat.card (RayClassGroup m) : ℚ) =
      (classNumber K : ℚ) * ((congruenceSubgroup m).relIndex (unitsK K) : ℚ)⁻¹ *
        2 ^ m.infinite.ncard * (Ideal.absNorm m.finite : ℚ) *
        ∏ P ∈ (UniqueFactorizationMonoid.factors m.finite).toFinset, (1 - 1 / (Ideal.absNorm P : ℚ)) := by
  classical
  obtain ⟨hex1, hex2, hex3⟩ := theorem_1_7_exact m
  have hfinQ : Finite (𝓞 K ⧸ m.finite) := Ideal.finiteQuotientOfFreeOfNeBot _ m.finite_ne_bot
  have hfinCod : Finite ((m.infinite → ℤˣ) × (𝓞 K ⧸ m.finite)ˣ) := inferInstance
  -- the index of `K_{m,1}` in `K_m`
  have hT : (congruenceSubgroup m).relIndex (Km m) =
      Nat.card ((m.infinite → ℤˣ) × (𝓞 K ⧸ m.finite)ˣ) := by
    rw [Subgroup.relIndex, ← isoMap_ker, Subgroup.index]
    exact Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective (isoMap m) (isoMap_surjective m)).toEquiv
  have hTpos : 0 < (congruenceSubgroup m).relIndex (Km m) := by
    rw [hT]; exact Nat.card_pos
  -- the tower `K_{m,1} ≤ U K_{m,1} ≤ K_m`
  have hle1 : congruenceSubgroup m ≤ unitsK K ⊔ congruenceSubgroup m := le_sup_right
  have hle2 : unitsK K ⊔ congruenceSubgroup m ≤ Km m :=
    sup_le (unitsK_le_Km m) (congruenceSubgroup_le_Km m)
  have htower := Subgroup.relIndex_mul_relIndex (congruenceSubgroup m)
    (unitsK K ⊔ congruenceSubgroup m) (Km m) hle1 hle2
  rw [Subgroup.relIndex_sup_right] at htower
  have hker : (kmToRay m).ker = (unitsK K ⊔ congruenceSubgroup m).subgroupOf (Km m) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hex1 a
  have hI : (unitsK K ⊔ congruenceSubgroup m).relIndex (Km m) = Nat.card (kmToRay m).range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have ha : (congruenceSubgroup m).relIndex (unitsK K) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at htower
    omega
  have hiNe : (unitsK K ⊔ congruenceSubgroup m).relIndex (Km m) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at htower
    omega
  have hfinRange : Finite (kmToRay m).range :=
    Nat.finite_of_card_ne_zero (hI ▸ hiNe)
  have hfinKer : Finite (rayToClass m).ker := by rw [hex2]; exact hfinRange
  have hfinQuot : Finite (RayClassGroup m ⧸ (rayToClass m).ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivOfSurjective (rayToClass m) hex3).toEquiv.symm
  have hfin : Finite (RayClassGroup m) := Finite.of_subgroup_quotient (rayToClass m).ker
  refine ⟨hfin, ?_⟩
  have hCard : Nat.card (RayClassGroup m) = classNumber K * Nat.card (kmToRay m).range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (rayToClass m).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (rayToClass m) hex3).toEquiv,
      Nat.card_eq_fintype_card (α := ClassGroup (𝓞 K)), hex2]
    rfl
  have hCod : Nat.card ((m.infinite → ℤˣ) × (𝓞 K ⧸ m.finite)ˣ) =
      2 ^ m.infinite.ncard * Nat.card (𝓞 K ⧸ m.finite)ˣ := by
    rw [Nat.card_prod, Nat.card_fun, ← Nat.card_coe_set_eq]
    congr 2
    rw [Nat.card_eq_fintype_card]
    rfl
  have hmain : (congruenceSubgroup m).relIndex (unitsK K) * Nat.card (kmToRay m).range =
      2 ^ m.infinite.ncard * Nat.card (𝓞 K ⧸ m.finite)ˣ := by
    rw [← hI, htower, hT, hCod]
  have ha' : ((congruenceSubgroup m).relIndex (unitsK K) : ℚ) ≠ 0 := by exact_mod_cast ha
  have hmainQ : ((congruenceSubgroup m).relIndex (unitsK K) : ℚ) * (Nat.card (kmToRay m).range : ℚ) =
      2 ^ m.infinite.ncard * (Nat.card (𝓞 K ⧸ m.finite)ˣ : ℚ) := by exact_mod_cast hmain
  have hu := natCard_units_finite_rat m
  have key : (Nat.card (kmToRay m).range : ℚ) = ((congruenceSubgroup m).relIndex (unitsK K) : ℚ)⁻¹ *
      (2 ^ m.infinite.ncard * (Nat.card (𝓞 K ⧸ m.finite)ˣ : ℚ)) :=
    (eq_inv_mul_iff_mul_eq₀ ha').2 hmainQ
  rw [hCard, Nat.cast_mul, key, hu]
  ring

/-! ## Example 1.8 (pp. 150–151) -/

/-- **Example 1.8(a)** (Milne, *CFT*, V, p. 150): for $\mathfrak m = 1$, $C_\mathfrak m = C$ (the Introduction's
`rayClassGroupOneEquiv`). -/
@[kb "milne2020cft" "Ch. V, Example 1.8(a)"]
theorem example_1_8a : Nonempty (RayClassGroup (Modulus.one K) ≃* ClassGroup (𝓞 K)) :=
  ⟨rayClassGroupOneEquiv K⟩

/-- The totally positive elements $K^+$ of $K^\times$. -/
def totallyPositive (K : Type) [Field K] [NumberField K] : Subgroup Kˣ where
  carrier := {a | ∀ (v : InfinitePlace K) (hv : v.IsReal), IsPositiveAt K v hv a}
  mul_mem' := by
    intro a b ha hb v hv
    have := ha v hv
    have := hb v hv
    unfold IsPositiveAt at *
    simp only [Units.val_mul, map_mul]
    positivity
  one_mem' := by
    intro v hv
    unfold IsPositiveAt; simp
  inv_mem' := by
    intro a ha v hv
    have := ha v hv
    unfold IsPositiveAt at *
    simp only [Units.val_inv_eq_inv_val, map_inv₀]
    positivity

/-- **Example 1.8(b)** (Milne, *CFT*, V, p. 150): for $\mathfrak m$ the product of the real primes (`narrowModulus`),
$K_\mathfrak m = K^\times$ and $K_{\mathfrak m,1} = K^+$, the totally positive elements, so the sequence of Theorem 1.7
becomes $0 \to U/U^+ \to K^\times/K^+ \to C_\mathfrak m \to C \to 1$, and $K^\times/K^+ \cong \prod_{v \text{ real}}\{\pm\}$
(signs at the real places). -/
@[kb "milne2020cft" "Ch. V, Example 1.8(b) (the narrow class group sequence)"]
theorem example_1_8b_narrow :
    Km (narrowModulus K) = ⊤ ∧ congruenceSubgroup (narrowModulus K) = totallyPositive K ∧
      ∃ φ : Kˣ →* ({v : InfinitePlace K // v.IsReal} → ℤˣ), Function.Surjective φ ∧
        φ.ker = totallyPositive K ∧ ∀ a : Kˣ, φ a = fun v => signAt v.1 v.2 (a : K) := by
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (narrowModulus K).finite := by
    intro v hv
    have : v.asIdeal ∣ (⊤ : Ideal (𝓞 K)) := hv
    rw [Ideal.dvd_iff_le, top_le_iff] at this
    exact v.isPrime.ne_top this
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro a _
    rw [Km, mem_primeToS_iff]
    intro v hv
    exact absurd hv (hfin v)
  · ext a
    constructor
    · intro h v hv
      exact h.1 v hv
    · intro h
      exact ⟨h, fun v hv => absurd hv (hfin v)⟩
  · refine ⟨MonoidHom.pi fun v : {v : InfinitePlace K // v.IsReal} => signHom v.1 v.2, ?_, ?_,
      fun a => rfl⟩
    · intro ε
      obtain ⟨z, -, hz0, hzs⟩ := exists_sign_residue (narrowModulus K) (fun v => ε ⟨v.1, v.2⟩) 0
      exact ⟨Units.mk0 (algebraMap (𝓞 K) K z) (algMap_ne_zero hz0), funext fun v => hzs v.1 v.2⟩
    · ext a
      rw [MonoidHom.mem_ker]
      constructor
      · intro h v hv
        exact (signAt_eq_one_iff v hv _).1 (congrFun h ⟨v, hv⟩)
      · intro h
        funext v
        exact (signAt_eq_one_iff v.1 v.2 _).2 (h v.1 v.2)

/-- **Example 1.8(b)** (Milne, *CFT*, V, p. 151): the narrow class group of $\mathbb Q$ is trivial. -/
@[kb "milne2020cft" "Ch. V, Example 1.8(b) (narrow class group of Q)"]
theorem example_1_8b_rat : Nat.card (RayClassGroup (narrowModulus ℚ)) = 1 := by
  have h : narrowModulus ℚ = ratModulus 1 one_ne_zero := by
    simp [narrowModulus, ratModulus]
  rw [h]
  obtain ⟨e⟩ := rayClassGroup_rat 1 one_ne_zero
  rw [Nat.card_congr e.toEquiv]
  have : Subsingleton (ZMod 1)ˣ := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  exact Nat.card_eq_one_iff_unique.2 ⟨this, ⟨1⟩⟩

section Quadratic

open NumberField.InfinitePlace

open scoped Classical in
/-- For a totally real number field the norm of an element is the product of its real embeddings. -/
theorem norm_eq_prod_real (hr : ∀ v : InfinitePlace K, v.IsReal) (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ v : {v : InfinitePlace K // v.IsReal}, embedding_of_isReal v.2 x := by
  classical
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have hreal : ∀ φ : K →+* ℂ, ComplexEmbedding.IsReal φ := fun φ => isReal_mk_iff.1 (hr (mk φ))
  have hemb : ∀ φ : K →+* ℂ, embedding (mk φ) = φ := by
    intro φ
    have h1 := mk_eq_iff.1 (mk_embedding (mk φ))
    rcases h1 with h1 | h1
    · exact h1
    · rw [ComplexEmbedding.isReal_iff.1 (hreal _)] at h1
      exact h1
  let f : (K →+* ℂ) → {v : InfinitePlace K // v.IsReal} := fun φ => ⟨mk φ, hr _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro φ ψ hφψ
      have h1 := mk_eq_iff.1 (congrArg Subtype.val hφψ)
      rcases h1 with h1 | h1
      · exact h1
      · rw [ComplexEmbedding.isReal_iff.1 (hreal φ)] at h1
        exact h1
    · intro v
      exact ⟨embedding v.1, Subtype.ext (mk_embedding v.1)⟩
  have h2 : ∏ φ : K →+* ℂ, φ x = ∏ σ : K →ₐ[ℚ] ℂ, σ x :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ x)
      (fun σ : K →ₐ[ℚ] ℂ => σ x) (fun _ => by simp [RingHom.equivRatAlgHom_apply])
  have h3 : ∏ φ : K →+* ℂ, φ x = ∏ v : {v : InfinitePlace K // v.IsReal},
      ((embedding_of_isReal v.2 x : ℝ) : ℂ) :=
    Fintype.prod_bijective f hf _ _ (fun φ => by
      simp only [f, embedding_of_isReal_apply, hemb])
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod, ← h3, h2, ← h]
  simp

theorem units_aux : ∀ p q s t : ℤˣ, p ≠ q → s ≠ t → (p = s ∧ q = t) ∨ (p = -s ∧ q = -t) := by
  decide

/-- A totally real quadratic field has exactly two real places. -/
theorem two_real_places (hK : Module.finrank ℚ K = 2) (hr : ∀ v : InfinitePlace K, v.IsReal) :
    ∃ a b : {v : InfinitePlace K // v.IsReal}, a ≠ b ∧ ∀ v, v = a ∨ v = b := by
  classical
  have h1 := card_add_two_mul_card_eq_rank K
  have h2 : nrComplexPlaces K = 0 := by
    apply Fintype.card_eq_zero_iff.2
    exact ⟨fun ⟨w, hw⟩ => not_isReal_iff_isComplex.2 hw (hr w)⟩
  have h3 : Nat.card {v : InfinitePlace K // v.IsReal} = 2 := by
    rw [Nat.card_eq_fintype_card]
    rw [h2, hK] at h1
    simpa using h1
  obtain ⟨a, b, hab, hset⟩ := Nat.card_eq_two_iff.1 h3
  refine ⟨a, b, hab, fun v => ?_⟩
  have : v ∈ ({a, b} : Set {v : InfinitePlace K // v.IsReal}) := by rw [hset]; trivial
  simpa using this

theorem sign_norm_iff (hr : ∀ v : InfinitePlace K, v.IsReal)
    {a b : {v : InfinitePlace K // v.IsReal}} (hab : a ≠ b) (hV : ∀ v, v = a ∨ v = b)
    {x : K} (hx : x ≠ 0) :
    (0 < ((Algebra.norm ℚ x : ℚ) : ℝ)) ↔ signAt a.1 a.2 x = signAt b.1 b.2 x := by
  classical
  have huniv : (Finset.univ : Finset {v : InfinitePlace K // v.IsReal}) = {a, b} := by
    ext v; simp [hV v]
  rw [norm_eq_prod_real hr x, huniv, Finset.prod_pair hab]
  have hp : embedding_of_isReal a.2 x ≠ 0 := (map_ne_zero _).2 hx
  have hq : embedding_of_isReal b.2 x ≠ 0 := (map_ne_zero _).2 hx
  have hne : (1 : ℤˣ) ≠ -1 := by decide
  unfold signAt
  rcases lt_or_gt_of_ne hp with h1 | h1 <;> rcases lt_or_gt_of_ne hq with h2 | h2
  · simp [not_lt.2 h1.le, not_lt.2 h2.le, mul_pos_of_neg_of_neg h1 h2]
  · simp [not_lt.2 h1.le, h2, not_lt.2 (mul_neg_of_neg_of_pos h1 h2).le, hne.symm]
  · simp [h1, not_lt.2 h2.le, not_lt.2 (mul_neg_of_pos_of_neg h1 h2).le, hne]
  · simp [h1, h2, mul_pos h1 h2]

end Quadratic

/-- **Example 1.8(b)** (Milne, *CFT*, V, p. 151): for a real quadratic field $K$ with class number $h$, the narrow
class number $h_\mathfrak m$ is $2h$ if the fundamental unit has norm $+1$ (equivalently every unit has norm $+1$) and
$h$ if it has norm $-1$. -/
@[kb "milne2020cft" "Ch. V, Example 1.8(b) (narrow class number of a real quadratic field)"]
theorem example_1_8b_quadratic (hK : Module.finrank ℚ K = 2) (hr : ∀ v : InfinitePlace K, v.IsReal) :
    ((∀ u : (𝓞 K)ˣ, Algebra.norm ℚ ((u : 𝓞 K) : K) = 1) →
        Nat.card (RayClassGroup (narrowModulus K)) = 2 * classNumber K) ∧
      ((∃ u : (𝓞 K)ˣ, Algebra.norm ℚ ((u : 𝓞 K) : K) = -1) →
        Nat.card (RayClassGroup (narrowModulus K)) = classNumber K) := by
  classical
  obtain ⟨hKm, hcs, φ, hφs, hφk, hφa⟩ := example_1_8b_narrow (K := K)
  obtain ⟨a, b, hab, hV⟩ := two_real_places hK hr
  have hV2 : Nat.card {v : InfinitePlace K // v.IsReal} = 2 := by
    rw [Nat.card_eq_two_iff]
    exact ⟨a, b, hab, by ext v; simp [hV v]⟩
  let ψ : unitsK K →* ({v : InfinitePlace K // v.IsReal} → ℤˣ) := φ.comp (unitsK K).subtype
  have hrel : (congruenceSubgroup (narrowModulus K)).relIndex (unitsK K) =
      Nat.card ψ.range := by
    rw [hcs, Subgroup.relIndex, ← Subgroup.index_ker]
    congr 1
    ext u
    rw [Subgroup.mem_subgroupOf, ← hφk]
    rfl
  have hncard : (narrowModulus K).infinite.ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hV2
  have hnorm : Ideal.absNorm (narrowModulus K).finite = 1 := by
    show Ideal.absNorm (⊤ : Ideal (𝓞 K)) = 1
    exact Ideal.absNorm_top
  have hfac : UniqueFactorizationMonoid.factors (narrowModulus K).finite = 0 := by
    show UniqueFactorizationMonoid.factors (⊤ : Ideal (𝓞 K)) = 0
    rw [← Ideal.one_eq_top]
    exact UniqueFactorizationMonoid.factors_one
  have hc : (Nat.card (RayClassGroup (narrowModulus K)) : ℚ) =
      classNumber K * ((congruenceSubgroup (narrowModulus K)).relIndex (unitsK K) : ℚ)⁻¹ * 4 := by
    rw [(theorem_1_7_card (narrowModulus K)).2, hncard, hnorm, hfac]
    simp only [Multiset.toFinset_zero, Finset.prod_empty, Nat.cast_one, mul_one]
    norm_num
  -- the element `-1`
  have hmem : (-1 : Kˣ) ∈ unitsK K := ⟨-1, by ext; simp⟩
  have hcm1 : (fun _ => -1 : {v : InfinitePlace K // v.IsReal} → ℤˣ) ∈ ψ.range := by
    refine ⟨⟨-1, hmem⟩, funext fun v => ?_⟩
    show φ (-1) v = -1
    rw [hφa]
    simp [signAt]
  have hUval : ∀ u : unitsK K, ∃ u' : (𝓞 K)ˣ, ((u : Kˣ) : K) = ((u' : 𝓞 K) : K) := by
    intro u
    obtain ⟨u', hu'⟩ := u.2
    exact ⟨u', by rw [← hu']; rfl⟩
  have hψ : ∀ (u : unitsK K) (v : {v : InfinitePlace K // v.IsReal}),
      ψ u v = signAt v.1 v.2 ((u : Kˣ) : K) := by
    intro u v
    show φ (u : Kˣ) v = _
    rw [hφa]
  refine ⟨fun hA => ?_, fun hB => ?_⟩
  · have h2 : Nat.card ψ.range = 2 := by
      have hsign : ∀ u : unitsK K, ∃ s : ℤˣ, ψ u = fun _ => s := by
        intro u
        obtain ⟨u', hx⟩ := hUval u
        have hpos : 0 < ((Algebra.norm ℚ ((u : Kˣ) : K) : ℚ) : ℝ) := by
          rw [hx, hA u']; simp
        have hs := (sign_norm_iff hr hab hV (u : Kˣ).ne_zero).1 hpos
        refine ⟨signAt a.1 a.2 ((u : Kˣ) : K), funext fun v => ?_⟩
        rw [hψ]
        rcases hV v with rfl | rfl
        · rfl
        · exact hs.symm
      rw [Nat.card_eq_two_iff]
      refine ⟨⟨1, one_mem _⟩, ⟨fun _ => -1, hcm1⟩, ?_, ?_⟩
      · intro h
        have h1 : (1 : ℤˣ) = -1 := congrFun (congrArg Subtype.val h) a
        exact absurd h1 (by decide)
      · apply Set.eq_univ_of_forall
        rintro ⟨_, ⟨u, rfl⟩⟩
        obtain ⟨s, hs⟩ := hsign u
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases Int.units_eq_one_or s with rfl | rfl
        · left
          exact Subtype.ext hs
        · right
          exact Subtype.ext hs
    have : (Nat.card (RayClassGroup (narrowModulus K)) : ℚ) = 2 * classNumber K := by
      rw [hc, hrel, h2]; push_cast; ring
    exact_mod_cast this
  · obtain ⟨u0, hu0⟩ := hB
    have h4 : Nat.card ψ.range = 4 := by
      let u0' : unitsK K := ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u0, u0, rfl⟩
      have hx0 : ((u0' : Kˣ) : K) = ((u0 : 𝓞 K) : K) := rfl
      have hneg : ¬ (0 < ((Algebra.norm ℚ ((u0' : Kˣ) : K) : ℚ) : ℝ)) := by
        rw [hx0, hu0]; norm_num
      have htne : ψ u0' a ≠ ψ u0' b := by
        rw [hψ, hψ]
        exact fun h => hneg ((sign_norm_iff hr hab hV (u0' : Kˣ).ne_zero).2 h)
      have htop : ψ.range = ⊤ := by
        rw [Subgroup.eq_top_iff']
        intro r
        by_cases hpq : r a = r b
        · have hr' : r = fun _ => r a := by
            funext v
            rcases hV v with rfl | rfl
            · rfl
            · exact hpq.symm
          rcases Int.units_eq_one_or (r a) with h | h
          · rw [hr', h]
            exact one_mem _
          · rw [hr', h]
            exact hcm1
        · rcases units_aux _ _ _ _ hpq htne with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have : r = ψ u0' := by
              funext v
              rcases hV v with rfl | rfl
              · exact h1
              · exact h2
            rw [this]
            exact ⟨u0', rfl⟩
          · have : r = ψ u0' * (fun _ => -1) := by
              funext v
              rcases hV v with rfl | rfl
              · simpa using h1
              · simpa using h2
            rw [this]
            exact Subgroup.mul_mem _ ⟨u0', rfl⟩ hcm1
      rw [htop, Subgroup.card_top, Nat.card_fun, hV2]
      have : Nat.card ℤˣ = 2 := by
        rw [Nat.card_eq_fintype_card]; rfl
      rw [this]
      norm_num
    have : (Nat.card (RayClassGroup (narrowModulus K)) : ℚ) = classNumber K := by
      rw [hc, hrel, h4]; push_cast; field_simp
    exact_mod_cast this

/-- The modulus $(m)$ of $\mathbb Q$, $m \ge 1$ (no infinite part). -/
def ratModulusFinite (m : ℕ) (hm : m ≠ 0) : Modulus ℚ where
  finite := Ideal.span {(m : 𝓞 ℚ)}
  finite_ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  infinite := ∅
  isReal_of_mem := fun _ h => h.elim

section RatFinite

variable (m : ℕ) (hm : m ≠ 0)

/-- The homomorphism $G_m \to C_{(m)}$, $a \mapsto [(a)]$, from the rational numbers prime to $m$. -/
def ThetaFin : Gm m hm →* RayClassGroup (ratModulusFinite m hm) :=
  (QuotientGroup.mk' ((rayPrincipal (ratModulusFinite m hm)).subgroupOf
    (coprimeIdeals (ratModulusFinite m hm)))).comp
    (((toPrincipalIdeal (𝓞 ℚ) ℚ).comp (Gm m hm).subtype).codRestrict
      (coprimeIdeals (ratModulusFinite m hm)) (fun a => a.2))

theorem ThetaFin_surj : Function.Surjective (ThetaFin m hm) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H I =>
    obtain ⟨a, ha⟩ := T_surj (I : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ)
    have hmem : a ∈ Gm m hm := by
      show toPrincipalIdeal (𝓞 ℚ) ℚ a ∈ coprimeIdeals (ratModulus m hm)
      rw [ha]; exact I.2
    refine ⟨⟨a, hmem⟩, ?_⟩
    show QuotientGroup.mk (⟨toPrincipalIdeal (𝓞 ℚ) ℚ a, _⟩ :
      coprimeIdeals (ratModulusFinite m hm)) = _
    congr 1
    exact Subtype.ext ha

theorem ThetaFin_eq_one_iff (a : Gm m hm) :
    ThetaFin m hm a = 1 ↔ ∃ c ∈ congruenceSubgroup (ratModulusFinite m hm),
      toPrincipalIdeal (𝓞 ℚ) ℚ c = toPrincipalIdeal (𝓞 ℚ) ℚ (a : ℚˣ) := by
  unfold ThetaFin
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  show toPrincipalIdeal (𝓞 ℚ) ℚ (a : ℚˣ) ∈ (congruenceSubgroup (ratModulusFinite m hm)).map _ ↔ _
  rw [Subgroup.mem_map]

theorem mem_congruenceSubgroup_fin (c : ℚˣ) :
    c ∈ congruenceSubgroup (ratModulusFinite m hm) ↔
      (Nat.Coprime (c : ℚ).num.natAbs m ∧ Nat.Coprime (c : ℚ).den m ∧
        (m : ℤ) ∣ (c : ℚ).num - (c : ℚ).den) := by
  rw [← fin_iff m hm]
  exact ⟨fun h => h.2, fun h => ⟨fun v hv => absurd hv (by simp [ratModulusFinite]), h⟩⟩

theorem ThetaFin_iff_Psi (a : Gm m hm) :
    ThetaFin m hm a = 1 ↔ Psi m hm a = 1 ∨ Psi m hm a = -1 := by
  have ha := (mem_Gm m hm _).1 ((absU_mem m hm _).2 a.2)
  have hden : Nat.Coprime (absU (a : ℚˣ) : ℚ).den m := ha.2
  have he := ZMod.coe_mul_inv_eq_one _ hden
  have hPsi : ((Psi m hm a : (ZMod m)ˣ) : ZMod m) = ratMod m (absU (a : ℚˣ) : ℚ) := rfl
  rw [ThetaFin_eq_one_iff]
  constructor
  · rintro ⟨c, hc, hca⟩
    rw [mem_congruenceSubgroup_fin] at hc
    obtain ⟨-, -, hd⟩ := hc
    have hcabs : (c : ℚ) = (absU (a : ℚˣ) : ℚ) ∨ (c : ℚ) = -(absU (a : ℚˣ) : ℚ) := by
      rw [absU_coe]
      rcases (T_eq_iff _ _).1 hca with h | h <;>
        rcases abs_choice (((a : ℚˣ)) : ℚ) with h' | h'
      · left; rw [h', h]
      · right; rw [h', h]; ring
      · right; rw [h', h]
      · left; rw [h', h]
    rcases hcabs with h | h
    · left
      rw [Psi_eq_one_iff]
      rw [h] at hd
      exact hd
    · right
      apply Units.ext
      rw [hPsi]
      rw [h, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den] at hd
      have hz : (((-(absU (a : ℚˣ) : ℚ).num - (absU (a : ℚˣ) : ℚ).den : ℤ)) : ZMod m) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
      push_cast at hz
      unfold ratMod
      generalize ((absU (a : ℚˣ) : ℚ).num : ZMod m) = n at *
      generalize ((absU (a : ℚˣ) : ℚ).den : ZMod m) = d at *
      generalize d⁻¹ = i at *
      simp only [Units.val_neg, Units.val_one]
      linear_combination (-i) * hz - he
  · intro h
    rcases h with h | h
    · refine ⟨absU (a : ℚˣ), ?_, T_absU _⟩
      rw [mem_congruenceSubgroup_fin]
      exact ⟨ha.1, ha.2, (Psi_eq_one_iff m hm a).1 h⟩
    · refine ⟨-absU (a : ℚˣ), ?_, ?_⟩
      · rw [mem_congruenceSubgroup_fin]
        refine ⟨?_, ?_, ?_⟩
        · simpa [Rat.num_neg_eq_neg_num] using ha.1
        · simpa [Rat.den_neg_eq_den] using ha.2
        · simp only [Units.val_neg, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den]
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          have hP : ratMod m (absU (a : ℚˣ) : ℚ) = -1 := by
            rw [← hPsi, h]; simp
          unfold ratMod at hP
          push_cast
          generalize ((absU (a : ℚˣ) : ℚ).num : ZMod m) = n at *
          generalize ((absU (a : ℚˣ) : ℚ).den : ZMod m) = d at *
          generalize d⁻¹ = i at *
          linear_combination (-d) * hP + n * he
      · rw [T_eq_iff, Units.val_neg, absU_coe]
        rcases abs_choice ((a : ℚˣ) : ℚ) with h' | h'
        · right; rw [h']
        · left; rw [h']; ring

end RatFinite

/-- **Example 1.8(c)** (Milne, *CFT*, V, p. 151): for $\mathbb Q$ and the modulus $(m)$, the sequence of Theorem 1.7
becomes $0 \to \{\pm 1\} \to (\mathbb Z/m\mathbb Z)^\times \to C_{(m)} \to 0$, so
$C_{(m)} \cong (\mathbb Z/m\mathbb Z)^\times/\{\pm 1\}$; for the modulus $\infty(m)$,
$C_{\infty(m)} \cong (\mathbb Z/m\mathbb Z)^\times$ (the Introduction's Exercise 0.13, `rayClassGroup_rat`). -/
@[kb "milne2020cft" "Ch. V, Example 1.8(c)"]
theorem example_1_8c (m : ℕ) (hm : m ≠ 0) :
    Nonempty (RayClassGroup (ratModulusFinite m hm) ≃*
      (ZMod m)ˣ ⧸ (Subgroup.zpowers (-1 : (ZMod m)ˣ))) ∧
    Nonempty (RayClassGroup (ratModulus m hm) ≃* (ZMod m)ˣ) := by
  refine ⟨?_, rayClassGroup_rat m hm⟩
  let Ψ' : Gm m hm →* (ZMod m)ˣ ⧸ Subgroup.zpowers (-1 : (ZMod m)ˣ) :=
    (QuotientGroup.mk' (Subgroup.zpowers (-1 : (ZMod m)ˣ))).comp (Psi m hm)
  have hΨsurj : Function.Surjective Ψ' := by
    intro y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, rfl⟩ := Psi_surj m hm u
    exact ⟨a, rfl⟩
  have hker : (ThetaFin m hm).ker = Ψ'.ker := by
    ext a
    simp only [MonoidHom.mem_ker, Ψ', MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff, ThetaFin_iff_Psi, Subgroup.mem_zpowers_iff]
    constructor
    · rintro (h | h)
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
    · rintro ⟨k, hk⟩
      rcases Int.even_or_odd k with he | ho
      · left; rw [← hk, he.neg_one_zpow]
      · right; rw [← hk, ho.neg_one_zpow]
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective _ (ThetaFin_surj m hm)).symm).trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hΨsurj))⟩

end NumberFieldKB.MilneCFT
