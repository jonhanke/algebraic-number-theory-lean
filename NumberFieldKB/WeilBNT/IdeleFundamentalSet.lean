import NumberFieldKB.WeilBNT.IdeleDensity
import NumberFieldKB.MilneCFT.Ch5Ideles
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Weil, *Basic Number Theory*, V.§4, Proposition 8: a fundamental set of order $e$ for $k^\times$ in the ideles

$k$ is a number field (`K`) of degree $n$, $r+1$ its number of infinite places ($r$ = `NumberField.Units.rank K`).

* $\Omega_\infty=k_\infty^\times\times\prod_v r_v^\times$, the kernel of $z\mapsto\mathrm{id}(z)$ (`omegaInf`).
* Weil's $l$, formula (3) (p. 93): $l(z)=(\log\lvert z_w\rvert_w)_w$ over the infinite places, with the normalized
  absolute value $\lvert x\rvert_w=\lVert x\rVert^{\delta_w}$, $\delta_w=[k_w:\mathbb R]$ (`weilLog`); on units of
  $\mathfrak r$ it is Mathlib's `logEmbedding` with the place $w_0$ restored.
* Weil's $F$, formula (4) (p. 94): $F(t)=\frac{t_0}{n}\delta+\sum_{j=1}^rt_j\,l(e_j)$ for free generators
  $e_1,\dots,e_r$ of $\mathfrak r^\times$ modulo the roots of unity $E$ (`weilF`); $\lambda(F(t))=t_0$ with
  $\lambda(x)=\sum_wx_w$, and $l(\eta\prod_je_j^{n_j})=F(0,n_1,\dots,n_r)$ for $\eta\in E$, formula (5).
* **Prop. 8** (p. 94): if $a_1,\dots,a_h$ represent the cosets of $k^\times\Omega_\infty$ in $k_{\mathbb A}^\times$, the
  union of the $a_i\,l^{-1}(F(\mathbb R\times I^r))$ ($I=[0,1)$, inside $\Omega_\infty$) is a fundamental set of order
  $e=\lvert E\rvert$ modulo $k^\times$: every coset $k^\times z$ meets it in exactly $e$ points (`weil_V_4_prop8`).

*Proof* (Weil's): write $z=a_i\xi z'$ with $\xi\in k^\times$, $z'\in\Omega_\infty$, $i$ unique. If $\eta z$
($\eta\in k^\times$) lies in the set, it lies in $a_i\Omega_\infty$, so $\varepsilon=\eta\xi$ lies in
$k^\times\cap\Omega_\infty=\mathfrak r^\times$. Writing $l(z')=F(t)$ and $\varepsilon=\zeta\prod_je_j^{n_j}$, we get
$l(\varepsilon z')=F(t_0,t+n)$, which lies in $F(\mathbb R\times I^r)$ for exactly one $n\in\mathbb Z^r$ ($F$ is
bijective); so exactly $e$ units $\varepsilon$, hence $e$ elements $\eta$, qualify.
-/

open IsDedekindDomain NumberField NumberField.Units NumberFieldKB.MilneCFT

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

variable (K) in
/-- Weil's $\Omega_\infty=k_\infty^\times\times\prod_vr_v^\times$: the ideles that are units at every finite place, i.e.
the kernel of $z\mapsto\mathrm{id}(z)$. -/
def omegaInf : Subgroup (IdeleGroup (𝓞 K) K) := (ideleToIdeal K).ker

variable (K) in
/-- **Weil's $l$**, formula (3) of V.§4: $l(z)_w=\log\lvert z_w\rvert_w=\delta_w\log\lVert z_w\rVert$ at the infinite
places $w$. -/
def weilLog (z : IdeleGroup (𝓞 K) K) (w : InfinitePlace K) : ℝ :=
  (w.mult : ℝ) * Real.log ‖ideleInfAt z w‖

/-- A unit of $\mathfrak r$ as a principal idele. -/
def unitIdele (u : (𝓞 K)ˣ) : IdeleGroup (𝓞 K) K :=
  IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u)

/-- **Weil's $F$**, formula (4) of V.§4: $F(t)=\frac{t_0}{n}\delta+\sum_jt_j\,l(e_j)$. -/
def weilF (e : Fin (rank K) → (𝓞 K)ˣ) (t : ℝ × (Fin (rank K) → ℝ)) (w : InfinitePlace K) : ℝ :=
  t.1 / Module.finrank ℚ K * w.mult + ∑ j, t.2 j * weilLog K (unitIdele (e j)) w

/-- The set of Prop. 8: $\bigcup_ia_i\,l^{-1}(F(\mathbb R\times I^r))$, $l^{-1}$ taken in $\Omega_\infty$. -/
def weilProp8Set {h : ℕ} (a : Fin h → IdeleGroup (𝓞 K) K) (e : Fin (rank K) → (𝓞 K)ˣ) :
    Set (IdeleGroup (𝓞 K) K) :=
  ⋃ i, (fun z => a i * z) '' {z | z ∈ omegaInf K ∧
    weilLog K z ∈ weilF e '' (Set.univ ×ˢ Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1)}

/-! ### Properties of $l$ and $F$ -/

theorem weilLog_mul (z z' : IdeleGroup (𝓞 K) K) : weilLog K (z * z') = weilLog K z + weilLog K z' := by
  funext w
  simp only [weilLog, Pi.add_apply]
  rw [ideleInfAt_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (ideleInfAt_ne_zero z w))
    (norm_ne_zero_iff.mpr (ideleInfAt_ne_zero z' w)), mul_add]

theorem weilLog_unitIdele (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    weilLog K (unitIdele u) w = w.mult * Real.log (w (u : K)) := by
  have h : ideleInfAt (unitIdele u) w = (((u : 𝓞 K) : K) : w.Completion) := rfl
  rw [weilLog, h, norm_coe_completion]

theorem unitIdele_mul (u u' : (𝓞 K)ˣ) : unitIdele (u * u') = unitIdele u * unitIdele u' := by
  unfold unitIdele
  rw [map_mul, map_mul]

/-- $l$ vanishes on the roots of unity. -/
theorem weilLog_unitIdele_torsion (ζ : torsion K) : weilLog K (unitIdele (ζ : (𝓞 K)ˣ)) = 0 := by
  funext w
  rw [weilLog_unitIdele]
  have := (mem_torsion K).mp ζ.2 w
  simp [this]

/-- Formula (5) of V.§4: $l(\zeta\prod_je_j^{n_j})=F(0,n)$. -/
theorem weilLog_unitIdele_prod (e : Fin (rank K) → (𝓞 K)ˣ) (ζ : torsion K) (n : Fin (rank K) → ℤ) :
    weilLog K (unitIdele ((ζ : (𝓞 K)ˣ) * ∏ j, e j ^ n j)) = weilF e (0, fun j => (n j : ℝ)) := by
  let H : (𝓞 K)ˣ →* Multiplicative (InfinitePlace K → ℝ) :=
    { toFun := fun u => Multiplicative.ofAdd (weilLog K (unitIdele u))
      map_one' := by
        apply congrArg Multiplicative.ofAdd
        funext w
        have : unitIdele (1 : (𝓞 K)ˣ) = 1 := by unfold unitIdele; simp
        simp [this, weilLog, ideleInfAt_one]
      map_mul' := fun u u' => by
        show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
        rw [unitIdele_mul, weilLog_mul]; rfl }
  have h : weilLog K (unitIdele ((ζ : (𝓞 K)ˣ) * ∏ j, e j ^ n j)) =
      Multiplicative.toAdd (H ((ζ : (𝓞 K)ˣ) * ∏ j, e j ^ n j)) := rfl
  have hz : Multiplicative.toAdd (H (ζ : (𝓞 K)ˣ)) = 0 := weilLog_unitIdele_torsion ζ
  rw [h, map_mul, map_prod, toAdd_mul, toAdd_prod, hz, zero_add]
  funext w
  rw [Finset.sum_apply]
  simp only [weilF, zero_div, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zpow, toAdd_zpow, Pi.smul_apply, zsmul_eq_mul]
  rfl

/-- $F(t)+F(0,s)=F(t_0,t+s)$. -/
theorem weilF_add (e : Fin (rank K) → (𝓞 K)ˣ) (t : ℝ × (Fin (rank K) → ℝ)) (s : Fin (rank K) → ℝ) :
    weilF e t + weilF e (0, s) = weilF e (t.1, t.2 + s) := by
  funext w
  simp only [weilF, Pi.add_apply, Prod.snd_add, zero_div, zero_mul, zero_add, add_mul,
    Finset.sum_add_distrib]
  ring

/-- Free generators modulo the roots of unity have independent logarithms (Mathlib's `IsMaxRank`). -/
theorem isMaxRank_of_generators (e : Fin (rank K) → (𝓞 K)ˣ)
    (he : ∀ u : (𝓞 K)ˣ, ∃ p : torsion K × (Fin (rank K) → ℤ), u = p.1 * ∏ j, e j ^ p.2 j) :
    IsMaxRank e := by
  rw [isMaxRank_iff_closure_finiteIndex, finiteIndex_iff_sup_torsion_finiteIndex]
  have : Subgroup.closure (Set.range e) ⊔ torsion K = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨p, hp⟩ := he u
    rw [hp]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right p.1.2) (Subgroup.mem_sup_left ?_)
    exact Subgroup.prod_mem _ fun j _ => Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self j)) _
  rw [this]
  infer_instance

/-- Weil: $F$ is an automorphism of $\mathbb R^{r+1}$ (here: a bijection onto the functions on the infinite places). -/
theorem weilF_bijective (e : Fin (rank K) → (𝓞 K)ˣ)
    (he : ∀ u : (𝓞 K)ˣ, ∃ p : torsion K × (Fin (rank K) → ℤ), u = p.1 * ∏ j, e j ^ p.2 j) :
    Function.Bijective (weilF e) := by
  classical
  have hmr := isMaxRank_of_generators e he
  let f : (ℝ × (Fin (rank K) → ℝ)) →ₗ[ℝ] (InfinitePlace K → ℝ) :=
    { toFun := weilF e
      map_add' := fun t t' => by
        funext w
        simp only [weilF, Pi.add_apply, Prod.fst_add, Prod.snd_add, add_mul, add_div,
          Finset.sum_add_distrib]
        ring
      map_smul' := fun c t => by
        funext w
        simp only [weilF, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          RingHom.id_apply]
        rw [mul_add, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun j _ => by ring }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    have ht' : weilF e t = 0 := ht
    have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
    have hs : ∑ w : InfinitePlace K, (w.mult : ℝ) = Module.finrank ℚ K := by
      exact_mod_cast InfinitePlace.sum_mult_eq (K := K)
    have hL : ∀ j, ∑ w : InfinitePlace K, weilLog K (unitIdele (e j)) w = 0 := fun j => by
      simp only [weilLog_unitIdele]; exact sum_mult_mul_log (e j)
    have h1 : t.1 = 0 := by
      have h0 : ∑ w : InfinitePlace K, weilF e t w = t.1 := by
        simp only [weilF]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs, Finset.sum_comm]
        simp only [← Finset.mul_sum, hL, mul_zero, Finset.sum_const_zero, add_zero]
        field_simp
      rw [← h0, ht']; simp
    have h2 : ∀ j, t.2 j = 0 := by
      have hsum : ∑ j, t.2 j • logEmbedding K (Additive.ofMul (e j)) = 0 := by
        funext w
        have := congrFun ht' w.1
        simp only [weilF, h1, zero_div, zero_mul, zero_add, Pi.zero_apply,
          weilLog_unitIdele] at this
        simp only [Finset.sum_apply, Pi.smul_apply, dirichletUnitTheorem.logEmbedding_component, smul_eq_mul,
          Pi.zero_apply]
        exact this
      exact fun j => Fintype.linearIndependent_iff.mp hmr t.2 hsum j
    exact Prod.ext h1 (funext h2)
  have hfr : Module.finrank ℝ (ℝ × (Fin (rank K) → ℝ)) =
      Module.finrank ℝ (InfinitePlace K → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun,
      Module.finrank_fintype_fun_eq_card]
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    unfold rank; omega
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj⟩

/-- $k^\times\cap\Omega_\infty=\mathfrak r^\times$. -/
theorem unitEmbedding_mem_omegaInf_iff (ξ : Kˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K ξ ∈ omegaInf K ↔ ∃ u : (𝓞 K)ˣ, Units.map (algebraMap (𝓞 K) K) u = ξ := by
  unfold omegaInf
  rw [MonoidHom.mem_ker, ideleToIdeal_unitEmbedding, toPrincipalIdeal_eq_iff, Units.val_one]
  constructor
  · intro h
    have h1 : (ξ : K) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
      rw [← h]; exact FractionalIdeal.mem_spanSingleton_self _ _
    have h2 : (1 : K) ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (ξ : K) := by
      rw [h]; exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp h1
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_spanSingleton _).mp h2
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, ha, map_one, mul_comm]
      simpa [Algebra.smul_def] using hb
    exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, Units.ext ha⟩
  · rintro ⟨u, hu⟩
    have hu' : algebraMap (𝓞 K) K u = (ξ : K) := congrArg Units.val hu
    refine FractionalIdeal.ext fun x => ?_
    rw [FractionalIdeal.mem_spanSingleton,FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z * u, by rw [map_mul, hu', Algebra.smul_def]⟩
    · rintro ⟨x', rfl⟩
      exact ⟨x' * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K), by
        rw [Algebra.smul_def, ← hu', ← map_mul, mul_assoc, Units.inv_mul, mul_one]⟩

/-- **Weil, V.§4, Proposition 8** (p. 94): let $a_1,\dots,a_h$ be a full set of representatives of the cosets of
$k^\times\Omega_\infty$ in $k_{\mathbb A}^\times$ and $e_1,\dots,e_r$ free generators of $\mathfrak r^\times$ modulo the
group $E$ of roots of unity. Then $\bigcup_ia_i\,l^{-1}(F(\mathbb R\times I^r))$ is a fundamental set of order
$e=\lvert E\rvert$ modulo $k^\times$ in $k_{\mathbb A}^\times$: it meets every coset $k^\times z$ in exactly $e$
points. -/
@[kb "weil1973bnt" "Ch. V, §4, Prop. 8 (p. 94)"]
theorem weil_V_4_prop8 {h : ℕ} (a : Fin h → IdeleGroup (𝓞 K) K)
    (ha : ∀ z : IdeleGroup (𝓞 K) K, ∃! i, ∃ ξ : Kˣ, ∃ y ∈ omegaInf K,
      z = a i * IdeleGroup.unitEmbedding (𝓞 K) K ξ * y)
    (e : Fin (rank K) → (𝓞 K)ˣ)
    (he : ∀ u : (𝓞 K)ˣ, ∃! p : torsion K × (Fin (rank K) → ℤ), u = p.1 * ∏ j, e j ^ p.2 j)
    (z : IdeleGroup (𝓞 K) K) :
    {ξ : Kˣ | IdeleGroup.unitEmbedding (𝓞 K) K ξ * z ∈ weilProp8Set a e}.encard = torsionOrder K := by
  classical
  have he' : ∀ u : (𝓞 K)ˣ, ∃ p : torsion K × (Fin (rank K) → ℤ), u = p.1 * ∏ j, e j ^ p.2 j :=
    fun u => (he u).exists
  have hbij := weilF_bijective e he'
  obtain ⟨i, ⟨ξ0, y, hy, hz⟩, -⟩ := ha z
  obtain ⟨t, ht⟩ := hbij.2 (weilLog K y)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : Fin (rank K) → ℤ, ∀ j, n₀ j = -⌊t.2 j⌋ := ⟨fun j => -⌊t.2 j⌋, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : (𝓞 K)ˣ, c = ∏ j, e j ^ n₀ j := ⟨_, rfl⟩
  let J : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)
  have hJ : Function.Injective J := Units.map_injective (IsFractionRing.injective (𝓞 K) K)
  let g : torsion K → Kˣ := fun ζ => J ((ζ : (𝓞 K)ˣ) * c) * ξ0⁻¹
  have hg : Function.Injective g := by
    intro ζ ζ' h
    have h1 := hJ (mul_right_cancel h)
    exact Subtype.ext (mul_right_cancel h1)
  have hlog : ∀ u : (𝓞 K)ˣ, unitIdele u = IdeleGroup.unitEmbedding (𝓞 K) K (J u) := fun u => rfl
  have hlogζ : ∀ ζ : torsion K, weilLog K (unitIdele ((ζ : (𝓞 K)ˣ) * c)) =
      weilF e (0, fun j => (n₀ j : ℝ)) := fun ζ => by
    rw [hc]; exact weilLog_unitIdele_prod e ζ n₀
  have hA : {ξ : Kˣ | IdeleGroup.unitEmbedding (𝓞 K) K ξ * z ∈ weilProp8Set a e} =
      Set.range g := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_range, weilProp8Set, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨i', w, ⟨hwΩ, s, hs, hsw⟩, hw⟩
      have h1 : i' = i := (ha (IdeleGroup.unitEmbedding (𝓞 K) K η * z)).unique
        ⟨1, w, hwΩ, by rw [map_one, mul_one]; exact hw.symm⟩
        ⟨η * ξ0, y, hy, by rw [hz, map_mul]; ac_rfl⟩
      subst h1
      have hw' : w = IdeleGroup.unitEmbedding (𝓞 K) K (η * ξ0) * y :=
        mul_left_cancel (a := a i') (by rw [hw, hz, map_mul]; ac_rfl)
      have hΩ : IdeleGroup.unitEmbedding (𝓞 K) K (η * ξ0) ∈ omegaInf K := by
        have := (omegaInf K).mul_mem hwΩ ((omegaInf K).inv_mem hy)
        rwa [hw', mul_inv_cancel_right] at this
      obtain ⟨u, hu⟩ := (unitEmbedding_mem_omegaInf_iff _).mp hΩ
      obtain ⟨p, hp⟩ := he' u
      have hwl : weilLog K w = weilF e (t.1, t.2 + fun j => (p.2 j : ℝ)) := by
        rw [hw', ← hu, ← hlog u, weilLog_mul, ← ht, hp, weilLog_unitIdele_prod, add_comm,
          weilF_add]
      have hs2 : s = (t.1, t.2 + fun j => (p.2 j : ℝ)) := hbij.1 (hsw.trans hwl)
      have hp2 : p.2 = n₀ := by
        funext j
        have h3 := hs.2 j (Set.mem_univ j)
        rw [hs2] at h3
        have h4 : t.2 j + (p.2 j : ℝ) ∈ Set.Ico (0 : ℝ) 1 := h3
        rw [← Int.floor_eq_zero_iff, Int.floor_add_intCast] at h4
        rw [hn₀]; omega
      have hu2 : u = (p.1 : (𝓞 K)ˣ) * c := by rw [hp, hc, hp2]
      refine ⟨p.1, ?_⟩
      show J ((p.1 : (𝓞 K)ˣ) * c) * ξ0⁻¹ = η
      rw [← hu2, hu, mul_inv_cancel_right]
    · rintro ⟨ζ, rfl⟩
      refine ⟨i, IdeleGroup.unitEmbedding (𝓞 K) K (J ((ζ : (𝓞 K)ˣ) * c)) * y, ⟨?_, ?_⟩, ?_⟩
      · exact (omegaInf K).mul_mem ((unitEmbedding_mem_omegaInf_iff _).mpr ⟨_, rfl⟩) hy
      · rw [← hlog, weilLog_mul, ← ht, hlogζ, add_comm, weilF_add]
        refine ⟨(t.1, t.2 + fun j => (n₀ j : ℝ)), ⟨Set.mem_univ _, fun j _ => ?_⟩, rfl⟩
        show t.2 j + (n₀ j : ℝ) ∈ Set.Ico (0 : ℝ) 1
        rw [hn₀]; push_cast
        constructor
        · linarith [Int.floor_le (t.2 j)]
        · linarith [Int.lt_floor_add_one (t.2 j)]
      · show _ = IdeleGroup.unitEmbedding (𝓞 K) K (J ((ζ : (𝓞 K)ˣ) * c) * ξ0⁻¹) * z
        rw [hz, map_mul (IdeleGroup.unitEmbedding (𝓞 K) K) (J ((ζ : (𝓞 K)ˣ) * c)) ξ0⁻¹, map_inv]
        calc _ = IdeleGroup.unitEmbedding (𝓞 K) K (J ((ζ : (𝓞 K)ˣ) * c)) * y * a i *
              ((IdeleGroup.unitEmbedding (𝓞 K) K ξ0)⁻¹ * IdeleGroup.unitEmbedding (𝓞 K) K ξ0) := by
              rw [inv_mul_cancel, mul_one]; ac_rfl
          _ = _ := by ac_rfl
  rw [hA, ← Set.image_univ, hg.injOn.encard_image, Set.encard_univ,
    ENat.card_eq_coe_natCard]
  rfl

end NumberFieldKB.WeilBNT
