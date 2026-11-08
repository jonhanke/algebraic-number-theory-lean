import NumberFieldKB.WeilBNT.AdeleAnnihilator
import NumberFieldKB.WeilBNT.StandardCharacter
import NumberFieldKB.WeilBNT.PFieldDuality
import NumberFieldKB.WeilBNT.PFieldCompletion
import NumberFieldKB.Ideles.InfiniteAdeleRing

/-!
# Weil, *Basic Number Theory*, IV.§2, Thm. 3, first assertion ($E=k$): the adeles are self-dual

$k$ is a number field (`K`), $k_{\mathbb A}$ Mathlib's adele ring, $\chi$ the standard character `chiA K`
($\psi_\infty\circ\operatorname{Tr}_\infty$ at infinity, QuadFormsKB's $\psi_v$ at the finite places; `AdeleAnnihilator`).
A *character* of an additive topological group $G$ is a continuous `AddChar G Circle`.

* `exists_unique_linear_of_addChar`: the characters of a finite-dimensional real vector space $V$ are the
  $x\mapsto e(\ell(x))$, $\ell\in V^*$ unique ($e(t)=e^{2\pi it}$).
* `weil_II_5_cor_thm3_infinite`: II.§5, Cor. of Thm. 3 for $k_\infty$ (the mixed space): every character is
  $x\mapsto\psi_\infty(ax)$ with a unique $a\in k_\infty$.
* `weil_II_5_cor_thm3_adicCompletion`: II.§5, Cor. of Thm. 3 for $k_v$, $v$ finite: every character is
  $x\mapsto\psi_v(xa)$ with a unique $a\in k_v$ (from the $p$-field case `PFieldDuality` and `PFieldCompletion`).
* `continuous_chiA`: $\chi$ is continuous.
* **`weil_IV_2_thm3_char`**: IV.§2, Thm. 3, first assertion for $E=k$, algebraic part: every character of
  $k_{\mathbb A}$ is $x\mapsto\chi(ax)$ for a unique $a\in k_{\mathbb A}$.
* **`weil_IV_2_thm3_isEmbedding`**: the topological part: $a\mapsto\chi(a\,\cdot)$ is a homeomorphism of
  $k_{\mathbb A}$ onto its image in $C(k_{\mathbb A},\mathbb T)$ with the compact-open topology (the topology of the
  dual group); with `weil_IV_2_thm3_char` the image is the whole dual, so this is Weil's isomorphism
  $k_{\mathbb A}\cong k_{\mathbb A}^*$.

*Proof* (not Weil's, which uses Pontryagin duality). Locally: $p$-fields by `PFieldDuality`; $k_\infty$ by lifting a
character of a real vector space through $t\mapsto e(t)$. Globally: a character $\psi$ of $k_{\mathbb A}$ restricts to
$x\mapsto\psi_v(xa_v)$ on each $k_v$; continuity forces $\psi$ trivial on $\prod_{v\notin S}r_v$ for a finite $S$, so
$a_v\in\mathfrak d_v^{-1}$ for almost all $v$ and $a=(a_v)$ is an adele; $\psi$ and $\chi(a\,\cdot)$ agree on the
adeles with finitely many nonzero finite components, which are dense.
-/

open IsDedekindDomain NumberField Topology QuadFormsKB.Analysis NumberField.mixedEmbedding
open scoped Real

noncomputable section

namespace NumberFieldKB.WeilBNT

/-- The characters of a finite-dimensional real vector space are $x\mapsto e(\ell(x))$ for a unique linear form
$\ell$. -/
theorem exists_unique_linear_of_addChar {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (ψ : AddChar V Circle) (hψ : Continuous ψ) :
    ∃! l : V →ₗ[ℝ] ℝ, ∀ x, ψ x = Real.fourierChar (l x) := by
  have hcov := Circle.isCoveringMap_exp
  obtain ⟨F, hF0, hF⟩ := (hcov.existsUnique_continuousMap_lifts (⟨ψ, hψ⟩ : C(V, Circle)) 0 0
    (by simp)).exists
  have hFx : ∀ x, Circle.exp (F x) = ψ x := fun x => congrFun hF x
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    let f : C(V × V, Circle) := ⟨fun p => ψ (p.1 + p.2), by fun_prop⟩
    let F1 : C(V × V, ℝ) := ⟨fun p => F (p.1 + p.2), by fun_prop⟩
    let F2 : C(V × V, ℝ) := ⟨fun p => F p.1 + F p.2, by fun_prop⟩
    have h0 : Circle.exp ((0 : ℝ)) = f (0, 0) := by simp [f]
    obtain ⟨G, _, hG⟩ := hcov.existsUnique_continuousMap_lifts f (0, 0) 0 h0
    have e1 : F1 = G := hG F1 ⟨by simp [F1, hF0], by
      ext p; simp [F1, hFx, f]⟩
    have e2 : F2 = G := hG F2 ⟨by simp [F2, hF0], by
      ext p; simp [F2, hFx, f, Circle.exp_add, AddChar.map_add_eq_mul]⟩
    have := congrArg (fun H : C(V × V, ℝ) => H (x, y)) (e1.trans e2.symm)
    simpa [F1, F2] using this
  let Fa : V →+ ℝ := ⟨⟨F, by simpa using hF0⟩, hadd⟩
  have hFc : Continuous Fa := F.continuous
  let L : V →L[ℝ] ℝ := Fa.toRealLinearMap hFc
  have hL : ∀ x, L x = F x := fun x => rfl
  have hmain : ∀ x, ψ x = Real.fourierChar ((((2 * π)⁻¹ : ℝ) • (L : V →ₗ[ℝ] ℝ)) x) := by
    intro x
    simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, hL, smul_eq_mul]
    rw [Real.fourierChar_apply', ← hFx x]
    congr 1
    field_simp
  refine ⟨((2 * π)⁻¹ : ℝ) • (L : V →ₗ[ℝ] ℝ), hmain, ?_⟩
  · intro l2 hl2
    have key : ∀ d : V →ₗ[ℝ] ℝ, (∀ x, Real.fourierChar (d x) = 1) → d = 0 := by
      intro d hd
      ext x
      have hint : ∀ y, ∃ n : ℤ, d y = n := by
        intro y
        have := hd y
        rw [Real.fourierChar_apply', Circle.exp_eq_one] at this
        obtain ⟨n, hn⟩ := this
        exact ⟨n, by
          have hp : (2 * π) ≠ 0 := by positivity
          apply mul_left_cancel₀ hp; linarith⟩
      obtain ⟨m, hm⟩ := hint x
      by_contra hne
      have hm0 : (m : ℝ) ≠ 0 := by
        intro h; apply hne; simp [hm, h]
      obtain ⟨n, hn⟩ := hint ((1 / (2 * m) : ℝ) • x)
      rw [map_smul, hm, smul_eq_mul] at hn
      have : (1 / (2 * (m : ℝ))) * m = 1 / 2 := by field_simp
      rw [this] at hn
      have h2 : (1 : ℝ) = 2 * n := by linarith
      have : (1 : ℤ) = 2 * n := by exact_mod_cast h2
      omega
    have hz := key (l2 - ((2 * π)⁻¹ : ℝ) • (L : V →ₗ[ℝ] ℝ)) (fun x => by
      rw [LinearMap.sub_apply, AddChar.map_sub_eq_div, ← hl2 x, ← hmain x, div_self'])
    exact sub_eq_zero.mp hz

variable {K : Type} [Field K] [NumberField K]

/-- The same for a finite-dimensional separated topological real vector space (transport to Euclidean space). -/
theorem exists_unique_linear_of_addChar_tvs {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
    (ψ : AddChar V Circle) (hψ : Continuous ψ) :
    ∃! l : V →ₗ[ℝ] ℝ, ∀ x, ψ x = Real.fourierChar (l x) := by
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    (LinearEquiv.ofFinrankEq V _ (by simp)).toContinuousLinearEquiv
  let ψ' : AddChar (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) Circle :=
    ψ.compAddMonoidHom (e.symm : _ →+ V)
  have hψ' : Continuous ψ' := hψ.comp e.symm.continuous
  obtain ⟨l, hl, hlu⟩ := exists_unique_linear_of_addChar ψ' hψ'
  refine ⟨l ∘ₗ (e : V →ₗ[ℝ] _), fun x => ?_, fun l2 hl2 => ?_⟩
  · have := hl (e x)
    simpa [ψ'] using this
  · have : l2 ∘ₗ (e.symm : _ →ₗ[ℝ] V) = l := hlu _ fun y => by
      simpa [ψ'] using hl2 (e.symm y)
    rw [← this]
    ext x; simp

/-- The ℝ-linear form `x ↦ Tr_∞(a x)` on the mixed space. -/
def traceMulL (a : mixedSpace K) : mixedSpace K →ₗ[ℝ] ℝ :=
  traceInfL ∘ₗ LinearMap.mulLeft ℝ a

theorem traceMulL_apply (a x : mixedSpace K) : traceMulL a x = traceInf (a * x) := rfl

/-- `a ↦ (x ↦ Tr_∞(a x))` is surjective onto the dual: the trace form is nondegenerate. -/
theorem exists_traceMulL_eq (l : mixedSpace K →ₗ[ℝ] ℝ) : ∃ a : mixedSpace K, traceMulL a = l := by
  let B : mixedSpace K →ₗ[ℝ] Module.Dual ℝ (mixedSpace K) :=
    { toFun := traceMulL
      map_add' := fun a b => LinearMap.ext fun x => by simp [traceMulL_apply, add_mul, traceInf_add]
      map_smul' := fun c a => LinearMap.ext fun x => by simp [traceMulL_apply, traceInf_smul] }
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h := LinearMap.congr_fun ha (star a)
    exact eq_zero_of_traceInf_mul_star a h
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := mixedSpace K)).symm).mp hinj
  obtain ⟨a, ha⟩ := hsurj l
  exact ⟨a, ha⟩

theorem traceMulL_injective : Function.Injective (traceMulL (K := K)) := by
  intro a b hab
  have h : traceMulL (a - b) = 0 := by
    refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun hab x
    simp only [traceMulL_apply] at this
    rw [LinearMap.zero_apply, traceMulL_apply, sub_mul, sub_eq_add_neg, traceInf_add, traceInf_neg]
    linarith
  have h2 := LinearMap.congr_fun h (star (a - b))
  exact sub_eq_zero.mp (eq_zero_of_traceInf_mul_star _ h2)


@[kb "weil1973bnt" "Ch. II, §5, Cor. of Thm. 3 (k_∞, k a number field)"]
theorem weil_II_5_cor_thm3_infinite (ψ : AddChar (mixedSpace K) Circle) (hψ : Continuous ψ) :
    ∃! a : mixedSpace K, ∀ x, ψ x = psiInf (a * x) := by
  obtain ⟨l, hl, hlu⟩ := exists_unique_linear_of_addChar_tvs ψ hψ
  obtain ⟨a, ha⟩ := exists_traceMulL_eq l
  refine ⟨a, fun x => ?_, fun b hb => traceMulL_injective ?_⟩
  · rw [hl x, ← ha]; rfl
  · rw [ha]
    refine hlu _ fun x => ?_
    rw [hb x]; rfl

@[kb "weil1973bnt" "Ch. II, §5, Cor. of Thm. 3 (K = k_v, k a number field)"]
theorem weil_II_5_cor_thm3_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) Circle) (hψ : Continuous ψ) :
    ∃! a : v.adicCompletion K, ∀ x, ψ x = psiV v (x * a) := by
  have hK : FieldModule.IsPField (v.adicCompletion K) (resChar v) :=
    FieldModule.isPField_adicCompletion v Fact.out ((resChar_dvd_iff v (resChar v)).1 dvd_rfl)
  exact FieldModule.weil_II_5_cor_thm3_right hK (continuous_psiV v)
    (fun h => psiV_nontrivial v (by simp [h])) hψ

/-! ### Neighbourhoods of zero in the adeles (copied from `StrongApproximation`, which is not imported) -/

theorem sd_exists_nat_restrict_lt {L : Type*} [Field L] (v : Valuation L (WithZero (Multiplicative ℤ)))
    (γ : v.ValueGroup₀ˣ) :
    ∃ N : ℕ, ∀ y : L, v y ≤ WithZero.exp (-(N : ℤ)) → v.restrict y < γ.1 := by
  obtain ⟨e, he0, key⟩ : ∃ e : WithZero (Multiplicative ℤ), e ≠ 0 ∧ ∀ y : L, v y < e → v.restrict y < γ.1 := by
    refine ⟨_, ?_, fun y => (Valuation.restrict_lt_iff_lt_embedding (v := v) (x := y) (g := γ.1)).mpr⟩
    intro h
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h.trans (map_zero _).symm))
  refine ⟨(1 - WithZero.log e).toNat, fun y hy => key y (lt_of_le_of_lt hy ?_)⟩
  refine lt_of_lt_of_eq (WithZero.exp_lt_exp.mpr (?_ : _ < WithZero.log e)) (WithZero.exp_log he0)
  omega

open Classical in
/-- A neighbourhood of zero in the finite adeles contains all finite adeles that are integral everywhere and
divisible by a high power of the uniformizer at the places of some finite set. -/
theorem sd_exists_finset_nat_of_mem_nhds_zero {W : Set (FiniteAdeleRing (𝓞 K) K)}
    (hW : W ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ), ∀ x : FiniteAdeleRing (𝓞 K) K,
      (∀ u, x u ∈ u.adicCompletionIntegers K) →
      (∀ u ∈ S, Valued.v (x u) ≤ WithZero.exp (-(N : ℤ))) → x ∈ W := by
  have hopen : ∀ u : HeightOneSpectrum (𝓞 K),
      IsOpen (u.adicCompletionIntegers K : Set (u.adicCompletion K)) :=
    fun _ => Valued.isOpen_valuationSubring _
  have h0 := RestrictedProduct.nhds_zero_eq_map_structureMap
    (R := fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K)
    (B := fun u => u.adicCompletionIntegers K) hopen
  have hW2 : W ∈ Filter.map (RestrictedProduct.structureMap
      (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K)
      (fun u => (u.adicCompletionIntegers K : Set (u.adicCompletion K))) Filter.cofinite) (𝓝 0) := by
    rw [← h0]; exact hW
  have hW3 := Filter.mem_map.mp hW2
  rw [nhds_pi, Filter.mem_pi'] at hW3
  obtain ⟨I, t, ht, hIt⟩ := hW3
  have hN : ∀ u, ∃ N : ℕ, ∀ y : u.adicCompletionIntegers K,
      Valued.v (y : u.adicCompletion K) ≤ WithZero.exp (-(N : ℤ)) → y ∈ t u := by
    intro u
    obtain ⟨V, hV, hVt⟩ := mem_nhds_subtype _ _ _ |>.mp (ht u)
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hV
    obtain ⟨N, hN⟩ := sd_exists_nat_restrict_lt (Valued.v : Valuation (u.adicCompletion K) _) γ
    exact ⟨N, fun y hy => hVt (hγ (hN y hy))⟩
  choose N hN using hN
  refine ⟨I, I.sup N, fun x hxint hx => ?_⟩
  have hxm : RestrictedProduct.structureMap (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K)
      (fun u => (u.adicCompletionIntegers K : Set (u.adicCompletion K))) Filter.cofinite
      (fun u => ⟨x u, hxint u⟩) = x := rfl
  rw [← hxm]
  refine hIt (fun u hu => hN u _ ?_)
  refine le_trans (hx u hu) ?_
  refine WithZero.exp_le_exp.mpr ?_
  have : N u ≤ I.sup N := Finset.le_sup hu
  omega

/-- A neighbourhood of zero in the infinite adeles contains all infinite adeles that are small at every place. -/
theorem sd_exists_eps_of_mem_nhds_zero {V : Set (InfiniteAdeleRing K)}
    (hV : V ∈ 𝓝 (0 : InfiniteAdeleRing K)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : InfiniteAdeleRing K, (∀ w, ‖x w‖ < ε) → x ∈ V := by
  have hV' : V ∈ Filter.pi (fun w : InfinitePlace K => 𝓝 (0 : w.Completion)) := by
    have := hV
    rw [show (0 : InfiniteAdeleRing K) = (fun _ => 0) from rfl, show 𝓝 (fun w : InfinitePlace K => (0 : w.Completion)) = Filter.pi (fun w => 𝓝 0) from nhds_pi] at this
    exact this
  rw [Filter.mem_pi'] at hV'
  obtain ⟨I, t, ht, hIt⟩ := hV'
  have hε : ∀ w, ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : w.Completion) ε ⊆ t w := fun w => Metric.mem_nhds_iff.mp (ht w)
  choose ε hε0 hεt using hε
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ε, (Finset.lt_inf'_iff _).mpr fun w _ => hε0 w, fun x hx => hIt fun w _ => hεt w ?_⟩
  rw [mem_ball_zero_iff]
  exact lt_of_lt_of_le (hx w) (Finset.inf'_le _ (Finset.mem_univ w))

open Classical in
/-- A neighbourhood basis statement for the adele ring at zero. -/
theorem sd_exists_eps_finset_nat_of_mem_nhds_zero {U : Set (AdeleRing (𝓞 K) K)}
    (hU : U ∈ 𝓝 (0 : AdeleRing (𝓞 K) K)) :
    ∃ (ε : ℝ) (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ), 0 < ε ∧ ∀ x : AdeleRing (𝓞 K) K,
      (∀ w, ‖x.1 w‖ < ε) → (∀ u, x.2 u ∈ u.adicCompletionIntegers K) →
      (∀ u ∈ S, Valued.v (x.2 u) ≤ WithZero.exp (-(N : ℤ))) → x ∈ U := by
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hU
  obtain ⟨ε, hε, hεV⟩ := sd_exists_eps_of_mem_nhds_zero hV
  obtain ⟨S, N, hSN⟩ := sd_exists_finset_nat_of_mem_nhds_zero hW
  exact ⟨ε, S, N, hε, fun x h1 h2 h3 => hVW ⟨hεV x.1 h1, hSN x.2 h2 h3⟩⟩


/-- Density criterion in terms of neighbourhoods of zero. -/
theorem sd_dense_of_forall_mem_nhds_zero {D : Set (AdeleRing (𝓞 K) K)}
    (h : ∀ a : AdeleRing (𝓞 K) K, ∀ U ∈ 𝓝 (0 : AdeleRing (𝓞 K) K), ∃ s ∈ D, a - s ∈ U) : Dense D := by
  intro a
  rw [mem_closure_iff_nhds]
  intro t ht
  have hU : {x | a - x ∈ t} ∈ 𝓝 (0 : AdeleRing (𝓞 K) K) := by
    have : Continuous fun x : AdeleRing (𝓞 K) K => a - x := continuous_const.sub continuous_id
    exact this.tendsto' 0 a (sub_zero a) ht
  obtain ⟨s, hs, hsU⟩ := h a _ hU
  exact ⟨s, by simpa using hsU, hs⟩


/-- The infinite part of the standard character is continuous. -/
theorem continuous_chiInf : Continuous (chiInf K) :=
  (Real.continuous_fourierChar.comp continuous_traceInf).comp
    (NumberFieldKB.Ideles.continuous_ringEquiv_mixedSpace K)

/-- The finite part of the standard character is continuous: it is trivial on the open subgroup of integral
finite adeles, hence locally constant. -/
theorem continuous_chiFin : Continuous (chiFin K) := by
  have hO : IsOpen {f : FiniteAdeleRing (𝓞 K) K | ∀ v, f v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (fun v => Valued.isOpen_valuationSubring _)
  have h1 : ∀ f ∈ {f : FiniteAdeleRing (𝓞 K) K | ∀ v, f v ∈ v.adicCompletionIntegers K}, chiFin K f = 1 :=
    fun f hf => finprod_eq_one_of_forall_eq_one fun v =>
      psiV_eq_one_of_le_one v (valued_le_one_of_mem (hf v))
  rw [continuous_iff_continuousAt]
  intro a0
  have hmem : (fun a => a - a0) ⁻¹' {f : FiniteAdeleRing (𝓞 K) K | ∀ v, f v ∈ v.adicCompletionIntegers K} ∈
      𝓝 a0 :=
    (hO.preimage (continuous_sub_right a0)).mem_nhds (by
      intro v
      simp only [sub_self]
      exact zero_mem _)
  refine (continuousAt_const (y := chiFin K a0)).congr (Filter.mem_of_superset hmem fun a ha => ?_)
  have := chiFin_add (K := K) (a - a0) a0
  rw [sub_add_cancel, h1 _ ha, one_mul] at this
  exact this.symm

theorem continuous_chiA : Continuous (chiA K) :=
  (continuous_chiInf.comp continuous_fst).mul (continuous_chiFin.comp continuous_snd)

/-- The character $x\mapsto\chi(ax)$ of $k_{\mathbb A}$, as a continuous map. -/
def chiAMul (a : AdeleRing (𝓞 K) K) : C(AdeleRing (𝓞 K) K, Circle) :=
  ⟨fun x => chiA K (a * x), continuous_chiA.comp (continuous_const.mul continuous_id)⟩

/-! ### The global character from its restrictions to the quasifactors -/

local notation "sA" => QuadFormsKB.Tamagawa.Measure.Weil.singleAdele

/-- The inclusion of the mixed space $k_\infty$ into $k_{\mathbb A}$ (finite components $0$). -/
def inclInf : mixedSpace K →+ AdeleRing (𝓞 K) K :=
  (AddMonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toAddMonoidHom

theorem inclInf_apply (y : mixedSpace K) :
    inclInf y = ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y, 0) := rfl

/-- The inclusion of the quasifactor $k_v$ into $k_{\mathbb A}$ (all other components $0$). -/
def inclFin (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K →+ AdeleRing (𝓞 K) K :=
  (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (sA v)

theorem inclFin_apply (v : HeightOneSpectrum (𝓞 K)) (t : v.adicCompletion K) :
    inclFin v t = (0, sA v t) := rfl

theorem continuous_inclInf : Continuous (inclInf (K := K)) :=
  (NumberFieldKB.Ideles.continuous_ringEquiv_mixedSpace_symm K).prodMk continuous_const

theorem continuous_inclFin (v : HeightOneSpectrum (𝓞 K)) : Continuous (inclFin v) :=
  continuous_const.prodMk (QuadFormsKB.Tamagawa.Measure.Weil.continuous_singleAdele v)

/-- The local component at infinity of a character of the adeles. -/
theorem exists_local_inf (ψ : AddChar (AdeleRing (𝓞 K) K) Circle) (hψ : Continuous ψ) :
    ∃ b : InfiniteAdeleRing K, ∀ y : InfiniteAdeleRing K, ψ (y, 0) = chiInf K (b * y) := by
  obtain ⟨a, ha, -⟩ := weil_II_5_cor_thm3_infinite (K := K) (ψ.compAddMonoidHom inclInf)
    (hψ.comp continuous_inclInf)
  refine ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm a, fun y => ?_⟩
  have := ha (InfiniteAdeleRing.ringEquiv_mixedSpace K y)
  simp only [AddChar.compAddMonoidHom_apply] at this
  have e : inclInf (InfiniteAdeleRing.ringEquiv_mixedSpace K y) = (y, 0) := by
    rw [inclInf_apply, RingEquiv.symm_apply_apply]
  rw [e] at this
  rw [this, chiInf, map_mul, RingEquiv.apply_symm_apply]

/-- The local component at a finite place of a character of the adeles. -/
theorem exists_local_fin (ψ : AddChar (AdeleRing (𝓞 K) K) Circle) (hψ : Continuous ψ)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ b : v.adicCompletion K, ∀ t, ψ (0, sA v t) = psiV v (t * b) := by
  obtain ⟨a, ha, -⟩ := weil_II_5_cor_thm3_adicCompletion v (ψ.compAddMonoidHom (inclFin v))
    (hψ.comp (continuous_inclFin v))
  exact ⟨a, fun t => ha t⟩

theorem chiFin_singleAdele (v : HeightOneSpectrum (𝓞 K)) (s : v.adicCompletion K) :
    chiFin K (sA v s) = psiV v s := by
  have h := chiAtFinite_eq (K := K) v s
  unfold chiAtFinite chiA at h
  change chiInf K 0 * chiFin K (sA v s) = psiV v s at h
  rwa [chiInf_zero, one_mul] at h

/-- The local components of a character of the adeles are integral at almost all places: a character is trivial on
the subgroup $r_v$ of $k_v$ once this subgroup lies in a neighbourhood of zero on which the real part is positive
(the circle has no small subgroups), and $\chi_v$ has order $0$ at almost all places. -/
theorem eventually_integral_local (ψ : AddChar (AdeleRing (𝓞 K) K) Circle) (hψ : Continuous ψ)
    (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (hb : ∀ v t, ψ (0, sA v t) = psiV v (t * b v)) :
    ∀ᶠ v in Filter.cofinite, b v ∈ v.adicCompletionIntegers K := by
  have hU : {x : AdeleRing (𝓞 K) K | 0 < ((ψ x : Circle) : ℂ).re} ∈ 𝓝 (0 : AdeleRing (𝓞 K) K) := by
    refine (isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_subtype_val.comp hψ))).mem_nhds ?_
    show 0 < ((ψ 0 : Circle) : ℂ).re
    simp
  obtain ⟨ε, S, N, hε, hSN⟩ := sd_exists_eps_finset_nat_of_mem_nhds_zero hU
  have hF := weil_IV_2_thm3_cor1_order (K := K)
  have key : ∀ v ∉ S, ∀ t : v.adicCompletion K, t ∈ v.adicCompletionIntegers K →
      psiV v (t * b v) = 1 := by
    intro v hv t ht
    rw [← hb]
    apply FieldModule.circle_eq_one_of_pow_re_pos
    intro n
    have h1 : ψ (0, sA v (n • t)) = (ψ (0, sA v t)) ^ n :=
      AddChar.map_nsmul_eq_pow (ψ.compAddMonoidHom (inclFin v)) n t
    rw [← h1]
    refine hSN (0, sA v (n • t)) (fun w => ?_) (fun u => ?_) (fun u hu => ?_)
    · show ‖(0 : w.Completion)‖ < ε
      simpa using hε
    · by_cases huv : u = v
      · subst huv
        show (sA u (n • t)) u ∈ _
        rw [QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_self]
        exact nsmul_mem ht n
      · show (sA v (n • t)) u ∈ _
        rw [QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_ne huv]
        exact zero_mem _
    · have huv : u ≠ v := fun h => hv (h ▸ hu)
      show Valued.v ((sA v (n • t)) u) ≤ _
      rw [QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_ne huv, map_zero]
      exact zero_le
  rw [Filter.eventually_cofinite]
  refine ((S.finite_toSet).union hF).subset ?_
  intro v hv
  by_contra hnot
  have hvS : v ∉ S := fun h => hnot (Or.inl h)
  have hvF : ¬ ({y : v.adicCompletion K | ∀ x : v.adicCompletion K, Valued.v x ≤ 1 →
      chiAtFinite K v (x * y) = 1} ≠ {y | Valued.v y ≤ 1}) := fun h => hnot (Or.inr h)
  have heq := not_not.mp hvF
  have hmem : b v ∈ {y : v.adicCompletion K | Valued.v y ≤ 1} := by
    rw [← heq]
    intro x hx
    rw [chiAtFinite_eq]
    exact key v hvS x ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hx)
  exact hv ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hmem)

theorem mul_singleAdele (f : FiniteAdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K))
    (t : v.adicCompletion K) : f * sA v t = sA v (f v * t) := by
  refine FiniteAdeleRing.ext K fun u => ?_
  show f u * (sA v t) u = (sA v (f v * t)) u
  by_cases h : u = v
  · subst h
    rw [QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_self,
      QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_self]
  · rw [QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_ne h,
      QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_ne h, mul_zero]

/-- Uniqueness: if $\chi(dx)=1$ for all adeles $x$ then $d=0$. -/
theorem eq_zero_of_chiA_mul (d : AdeleRing (𝓞 K) K) (h : ∀ x, chiA K (d * x) = 1) : d = 0 := by
  have h1 : d.1 = 0 := by
    have hc : Continuous ⇑(1 : AddChar (mixedSpace K) Circle) := by
      have : ⇑(1 : AddChar (mixedSpace K) Circle) = fun _ => 1 := by ext; simp
      rw [this]; exact continuous_const
    obtain ⟨a, _, hu⟩ := weil_II_5_cor_thm3_infinite (K := K) 1 hc
    have e1 := hu 0 (fun x => by simp [psiInf, traceInf])
    have e2 := hu (InfiniteAdeleRing.ringEquiv_mixedSpace K d.1) (fun x => by
      have h' := h (inclInf x)
      rw [inclInf_apply] at h'
      change chiInf K (d.1 * _) * chiFin K (d.2 * 0) = 1 at h'
      rw [mul_zero, chiFin_zero, mul_one] at h'
      rw [AddChar.one_apply]
      unfold chiInf at h'
      rw [map_mul, RingEquiv.apply_symm_apply] at h'
      exact h'.symm)
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective).mp (e2.trans e1.symm)
  have h2 : d.2 = 0 := by
    refine FiniteAdeleRing.ext K fun v => ?_
    show d.2 v = 0
    have hc : Continuous ⇑(1 : AddChar (v.adicCompletion K) Circle) := by
      have : ⇑(1 : AddChar (v.adicCompletion K) Circle) = fun _ => 1 := by ext; simp
      rw [this]; exact continuous_const
    obtain ⟨a, _, hu⟩ := weil_II_5_cor_thm3_adicCompletion v 1 hc
    have e1 := hu 0 (fun x => by simp)
    have e2 := hu (d.2 v) (fun t => by
      have h' := h (0, sA v t)
      change chiInf K (d.1 * 0) * chiFin K (d.2 * sA v t) = 1 at h'
      rw [mul_zero, chiInf_zero, one_mul, mul_singleAdele, chiFin_singleAdele] at h'
      rw [AddChar.one_apply, mul_comm]
      exact h'.symm)
    exact e2.trans e1.symm
  exact Prod.ext h1 h2

theorem fourierChar_half : ((Real.fourierChar (1 / 2 : ℝ) : Circle) : ℂ).re = -1 := by
  rw [Real.fourierChar_apply, Complex.exp_re]
  have : ((↑(2 * π * (1 / 2 : ℝ)) * Complex.I : ℂ)).re = 0 := by simp
  have h2 : ((↑(2 * π * (1 / 2 : ℝ)) * Complex.I : ℂ)).im = π := by
    simp; ring
  rw [this, h2]; simp [Real.cos_pi]

open Classical in
theorem traceInf_real_single (z : mixedSpace K) (i : {w : InfinitePlace K // w.IsReal}) (s : ℝ) :
    traceInf (z * ((Pi.single i s, 0) : mixedSpace K)) = z.1 i * s := by
  unfold traceInf
  simp [Pi.single_apply]

open Classical in
theorem traceInf_complex_single (z : mixedSpace K) (i : {w : InfinitePlace K // w.IsComplex}) (s : ℂ) :
    traceInf (z * ((0, Pi.single i s) : mixedSpace K)) = 2 * (z.2 i * s).re := by
  unfold traceInf
  have h1 : ∑ w, (z * ((0, Pi.single i s) : mixedSpace K)).1 w = 0 := by simp
  rw [h1, zero_add, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

open Classical in
/-- Small at the infinite places is detected by a compact set. -/
theorem exists_compact_inf {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Set (InfiniteAdeleRing K), IsCompact B ∧ (0 : InfiniteAdeleRing K) ∈ B ∧
      ∀ z : InfiniteAdeleRing K, (∀ y ∈ B, 0 < ((chiInf K (z * y) : Circle) : ℂ).re) →
        ∀ w, ‖z w‖ < ε := by
  set R : ℝ := 1 / (2 * ε) with hR
  have hR0 : 0 ≤ R := by positivity
  let B' : Set (mixedSpace K) := (Set.pi Set.univ fun _ => Metric.closedBall (0 : ℝ) R) ×ˢ
    (Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R)
  have hB' : IsCompact B' := (isCompact_univ_pi fun _ => isCompact_closedBall _ _).prod
    (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  refine ⟨e.symm '' B', hB'.image (NumberFieldKB.Ideles.continuous_ringEquiv_mixedSpace_symm K),
    ⟨0, ?_, map_zero _⟩, ?_⟩
  · refine ⟨fun i _ => ?_, fun i _ => ?_⟩ <;> simpa using hR0
  intro z hz w
  by_contra hw
  push Not at hw
  have hnorm := NumberFieldKB.Ideles.normAtPlace_ringEquiv_mixedSpace K z w
  have key : ∀ y' ∈ B', 0 < ((psiInf (e z * y') : Circle) : ℂ).re := by
    intro y' hy'
    have := hz (e.symm y') ⟨y', hy', rfl⟩
    have h1 : chiInf K (z * e.symm y') = psiInf (e z * y') := by
      unfold chiInf; rw [map_mul, RingEquiv.apply_symm_apply]
    rwa [h1] at this
  rcases w.isReal_or_isComplex with hr | hc
  · rw [normAtPlace_apply_of_isReal hr] at hnorm
    have hc0 : (e z).1 ⟨w, hr⟩ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      linarith
    have hmem : ((Pi.single ⟨w, hr⟩ (1 / (2 * (e z).1 ⟨w, hr⟩)), 0) : mixedSpace K) ∈ B' := by
      refine ⟨fun i _ => ?_, fun i _ => by simpa using hR0⟩
      by_cases hi : i = ⟨w, hr⟩
      · subst hi
        simp only [Pi.single_eq_same, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
        have hc1 : ε ≤ |(e z).1 ⟨w, hr⟩| := by rw [← Real.norm_eq_abs, hnorm]; exact hw
        rw [abs_div, abs_mul, abs_one, abs_two, hR, one_div, one_div]
        exact inv_anti₀ (by positivity) (by linarith)
      · simpa [Pi.single_eq_of_ne hi] using hR0
    have := key _ hmem
    rw [psiInf, traceInf_real_single] at this
    have h2 : (e z).1 ⟨w, hr⟩ * (1 / (2 * (e z).1 ⟨w, hr⟩)) = 1 / 2 := by field_simp
    rw [h2, fourierChar_half] at this
    linarith
  · rw [normAtPlace_apply_of_isComplex hc] at hnorm
    have hc0 : (e z).2 ⟨w, hc⟩ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      linarith
    have hmem : (((0 : {w : InfinitePlace K // w.IsReal} → ℝ),
        Pi.single ⟨w, hc⟩ (1 / (4 * (e z).2 ⟨w, hc⟩))) : mixedSpace K) ∈ B' := by
      refine ⟨fun i _ => by simpa using hR0, fun i _ => ?_⟩
      by_cases hi : i = ⟨w, hc⟩
      · subst hi
        simp only [Pi.single_eq_same, Metric.mem_closedBall, dist_zero_right]
        have hc1 : ε ≤ ‖(e z).2 ⟨w, hc⟩‖ := by rw [hnorm]; exact hw
        rw [norm_div, norm_mul, norm_one, hR]
        have h4 : ‖(4 : ℂ)‖ = 4 := by simp
        rw [h4, one_div, one_div]
        exact inv_anti₀ (by positivity) (by linarith)
      · simpa [Pi.single_eq_of_ne hi] using hR0
    have := key _ hmem
    rw [psiInf, traceInf_complex_single] at this
    have h2 : (e z).2 ⟨w, hc⟩ * (1 / (4 * (e z).2 ⟨w, hc⟩)) = 1 / 4 := by field_simp
    have h3 : (2 : ℝ) * (((1 : ℂ) / 4).re) = 1 / 2 := by norm_num
    rw [h2, h3, fourierChar_half] at this
    linarith


/-! ### The topology: the characters $\chi(a\,\cdot)$ separate a neighbourhood of zero -/

theorem chiA_mul_single (a : AdeleRing (𝓞 K) K) (u : HeightOneSpectrum (𝓞 K)) (s : u.adicCompletion K) :
    chiA K (a * (show AdeleRing (𝓞 K) K from (0, sA u s))) = psiV u (a.2 u * s) := by
  change chiInf K (a.1 * 0) * chiFin K (a.2 * sA u s) = _
  rw [mul_zero, chiInf_zero, one_mul, mul_singleAdele, chiFin_singleAdele]

theorem chiA_mul_inf (a : AdeleRing (𝓞 K) K) (y : InfiniteAdeleRing K) :
    chiA K (a * (show AdeleRing (𝓞 K) K from (y, 0))) = chiInf K (a.1 * y) := by
  change chiInf K (a.1 * y) * chiFin K (a.2 * 0) = _
  rw [mul_zero, chiFin_zero, mul_one]

/-- If $\psi_v(y\,t)$ has positive real part for all $t\in\mathfrak p_v^{-k-d_v}$ then $y\in\mathfrak p_v^k$ (the
circle has no small subgroups, and the annihilator of $\mathfrak p_v^{-k-d_v}$ is $\mathfrak p_v^k$). -/
theorem valued_le_of_psiV (u : HeightOneSpectrum (𝓞 K)) (k : ℤ) (y : u.adicCompletion K)
    (h : ∀ t ∈ latticeV u (-k - diffExp u), 0 < ((psiV u (y * t) : Circle) : ℂ).re) :
    Valued.v y ≤ WithZero.exp (-k) := by
  have hall : y ∈ annihV u (latticeV u (-k - diffExp u)) := by
    intro t ht
    rw [mul_comm]
    apply FieldModule.circle_eq_one_of_pow_re_pos
    intro n
    have h1 : psiV u (y * (n • t)) = (psiV u (y * t)) ^ n := by
      rw [mul_smul_comm]
      exact AddChar.map_nsmul_eq_pow (psiV u) n (y * t)
    rw [← h1]
    exact h _ (nsmul_mem ht n)
  rw [annihV_latticeV] at hall
  have := (mem_latticeV u).mp hall
  have e : -(-k - (diffExp u : ℤ)) - (diffExp u : ℤ) = k := by ring
  rwa [e] at this

open Classical Pointwise in
/-- A compact set of finite adeles containing $0$ and the $\mathfrak p_u^{-d_u-n_u}$ in the $u$-th coordinate,
where $n_u=N$ for $u\in S$ and $n_u=0$ otherwise. -/
theorem exists_compact_fin (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    ∃ Cf : Set (FiniteAdeleRing (𝓞 K) K), IsCompact Cf ∧ (0 : FiniteAdeleRing (𝓞 K) K) ∈ Cf ∧
      ∀ (u : HeightOneSpectrum (𝓞 K)) (t : u.adicCompletion K),
        t ∈ latticeV u (-(diffExp u : ℤ) - (if u ∈ S then (N : ℤ) else 0)) → sA u t ∈ Cf := by
  classical
  let F : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ (finite_support_diffExp (F := K)).toFinset
  refine ⟨QuadFormsKB.Tamagawa.Measure.Weil.OHat ∪ ⋃ u ∈ F, (QuadFormsKB.Tamagawa.Measure.Weil.OHat +
      (sA u) '' (latticeV u (-(diffExp u : ℤ) - (if u ∈ S then (N : ℤ) else 0)) : Set (u.adicCompletion K))),
    ?_, Or.inl QuadFormsKB.Tamagawa.Measure.Weil.zero_mem_OHat, ?_⟩
  · refine QuadFormsKB.Tamagawa.Measure.Weil.isCompact_OHat.union ?_
    refine F.finite_toSet.isCompact_biUnion fun u _ => ?_
    exact QuadFormsKB.Tamagawa.Measure.Weil.isCompact_OHat.add
      ((isCompact_latticeV u _).image (QuadFormsKB.Tamagawa.Measure.Weil.continuous_singleAdele u))
  · intro u t ht
    by_cases hu : u ∈ F
    · right
      simp only [Set.mem_iUnion]
      refine ⟨u, hu, 0, QuadFormsKB.Tamagawa.Measure.Weil.zero_mem_OHat, sA u t, ⟨t, ht, rfl⟩, ?_⟩
      simp
    · left
      have huS : u ∉ S := fun h => hu (Finset.mem_union_left _ h)
      have hd : (diffExp u : ℤ) = 0 := by
        by_contra hne
        exact hu (Finset.mem_union_right _ ((finite_support_diffExp (F := K)).mem_toFinset.mpr hne))
      simp only [huS, ↓reduceIte, hd] at ht
      have ht1 := (mem_latticeV u).mp ht
      intro v
      by_cases hv : v = u
      · subst hv
        rw [QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_self]
        refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_
        simpa using ht1
      · rw [QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_ne hv]
        exact zero_mem _

/-- **Key estimate**: a neighbourhood of zero in $k_{\mathbb A}$ contains all $a$ for which $\chi(a\,x)$ has positive
real part on a suitable compact set of $x$. -/
theorem exists_compact_of_mem_nhds_zero {U : Set (AdeleRing (𝓞 K) K)} (hU : U ∈ 𝓝 (0 : AdeleRing (𝓞 K) K)) :
    ∃ C : Set (AdeleRing (𝓞 K) K), IsCompact C ∧
      ∀ a : AdeleRing (𝓞 K) K, (∀ x ∈ C, 0 < ((chiA K (a * x) : Circle) : ℂ).re) → a ∈ U := by
  classical
  obtain ⟨ε, S, N, hε, hSN⟩ := sd_exists_eps_finset_nat_of_mem_nhds_zero hU
  obtain ⟨B, hBc, hB0, hB⟩ := exists_compact_inf (K := K) hε
  obtain ⟨Cf, hCfc, hCf0, hCf⟩ := exists_compact_fin S N
  refine ⟨B ×ˢ Cf, hBc.prod hCfc, fun a ha => ?_⟩
  have hloc : ∀ u : HeightOneSpectrum (𝓞 K),
      Valued.v (a.2 u) ≤ WithZero.exp (-(if u ∈ S then (N : ℤ) else 0)) := by
    intro u
    refine valued_le_of_psiV u _ (a.2 u) fun t ht => ?_
    rw [← chiA_mul_single]
    exact ha _ ⟨hB0, hCf u t (by
      have e : -(diffExp u : ℤ) - (if u ∈ S then (N : ℤ) else 0) =
          -(if u ∈ S then (N : ℤ) else 0) - diffExp u := by ring
      rw [e]; exact ht)⟩
  refine hSN a (fun w => ?_) (fun u => ?_) (fun u hu => ?_)
  · refine hB a.1 (fun y hy => ?_) w
    rw [← chiA_mul_inf]
    exact ha _ ⟨hy, hCf0⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ((hloc u).trans ?_)
    by_cases hu : u ∈ S <;> simp [hu]
  · have := hloc u
    simpa [hu] using this

/-- The adeles with only finitely many nonzero finite components. -/
def finiteSupportAdeles : Set (AdeleRing (𝓞 K) K) :=
  {x | ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ u ∉ T, x.2 u = 0}

theorem dense_finiteSupportAdeles : Dense (finiteSupportAdeles (K := K)) := by
  classical
  refine sd_dense_of_forall_mem_nhds_zero fun a U hU => ?_
  obtain ⟨ε, S, N, hε, hSN⟩ := sd_exists_eps_finset_nat_of_mem_nhds_zero hU
  have hfin := Filter.eventually_cofinite.mp a.2.2
  set T : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ hfin.toFinset with hT
  let f : FiniteAdeleRing (𝓞 K) K := ⟨fun u => if u ∈ T then a.2 u else 0,
    Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun u hu => by
      by_contra huT
      exact hu (by
        show (if u ∈ T then a.2 u else 0) ∈ (u.adicCompletionIntegers K : Set (u.adicCompletion K))
        have huT' : u ∉ T := huT
        simp only [huT', ↓reduceIte]
        exact (u.adicCompletionIntegers K).zero_mem))⟩
  refine ⟨(a.1, f), ⟨T, fun u hu => by
    show (if u ∈ T then a.2 u else 0) = 0
    simp [hu]⟩, hSN _ (fun w => ?_) (fun u => ?_) (fun u hu => ?_)⟩
  · have h0 : a.1 - a.1 = 0 := sub_self _
    show ‖(a.1 - a.1) w‖ < ε
    rw [h0]
    show ‖(0 : w.Completion)‖ < ε
    rw [norm_zero]
    exact hε
  · show a.2 u - (if u ∈ T then a.2 u else 0) ∈ _
    by_cases huT : u ∈ T
    · simp only [huT, ite_true, sub_self]; exact zero_mem _
    · simp only [huT, ite_false, sub_zero]
      by_contra hno
      exact huT (Finset.mem_union_right _ (hfin.mem_toFinset.mpr (by exact hno)))
  · show Valued.v (a.2 u - (if u ∈ T then a.2 u else 0)) ≤ _
    have huT : u ∈ T := Finset.mem_union_left _ hu
    simp only [huT, ite_true, sub_self, map_zero]
    exact zero_le

@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3, first assertion (E = k, number field case): every character is χ(a·)"]
theorem weil_IV_2_thm3_char (ψ : AddChar (AdeleRing (𝓞 K) K) Circle) (hψ : Continuous ψ) :
    ∃! a : AdeleRing (𝓞 K) K, ∀ x, ψ x = chiA K (a * x) := by
  classical
  obtain ⟨bI, hbI⟩ := exists_local_inf ψ hψ
  choose b hb using exists_local_fin ψ hψ
  have hint := eventually_integral_local ψ hψ b hb
  let α : AdeleRing (𝓞 K) K := (bI, ⟨b, hint⟩)
  have main : ∀ x, ψ x = chiA K (α * x) := by
    let E : Set (AdeleRing (𝓞 K) K) := {x | ψ x = chiA K (α * x)}
    have hEc : IsClosed E :=
      isClosed_eq hψ (continuous_chiA.comp (continuous_const.mul continuous_id))
    have hEadd : ∀ x y, x ∈ E → y ∈ E → x + y ∈ E := by
      intro x y hx hy
      show ψ (x + y) = chiA K (α * (x + y))
      rw [AddChar.map_add_eq_mul, mul_add, chiA_add]
      exact congr (congrArg _ hx) hy
    have hE0 : (0 : AdeleRing (𝓞 K) K) ∈ E := by
      show ψ 0 = chiA K (α * 0)
      rw [mul_zero, AddChar.map_zero_eq_one]
      change 1 = chiInf K 0 * chiFin K 0
      rw [chiInf_zero, chiFin_zero, mul_one]
    have hEinf : ∀ y : InfiniteAdeleRing K, ((y, 0) : AdeleRing (𝓞 K) K) ∈ E := by
      intro y
      show ψ (y, 0) = chiA K (α * (show AdeleRing (𝓞 K) K from (y, 0)))
      rw [hbI y]
      change _ = chiInf K (bI * y) * chiFin K (_ * 0)
      rw [mul_zero, chiFin_zero, mul_one]
    have hEfin : ∀ (v : HeightOneSpectrum (𝓞 K)) (t : v.adicCompletion K),
        ((0, sA v t) : AdeleRing (𝓞 K) K) ∈ E := by
      intro v t
      show ψ (0, sA v t) = chiA K (α * (show AdeleRing (𝓞 K) K from (0, sA v t)))
      rw [hb v t]
      change _ = chiInf K (bI * 0) * chiFin K (α.2 * sA v t)
      rw [mul_zero, chiInf_zero, one_mul, mul_singleAdele, chiFin_singleAdele]
      exact congrArg _ (mul_comm _ _)
    have hEsupp : ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (f : FiniteAdeleRing (𝓞 K) K),
        (∀ u ∉ T, f u = 0) → (((0 : InfiniteAdeleRing K), f) : AdeleRing (𝓞 K) K) ∈ E := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro f hf
        have : f = 0 := FiniteAdeleRing.ext K fun u => hf u (Finset.notMem_empty u)
        subst this
        exact hE0
      | insert u T hu ih =>
        intro f hf
        have h1 := ih (f - sA u (f u)) (fun w hw => by
          show f w - (sA u (f u)) w = 0
          by_cases hwu : w = u
          · subst hwu
            rw [QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_self, sub_self]
          · rw [QuadFormsKB.Tamagawa.Measure.Weil.singleAdele_apply_ne hwu, sub_zero]
            exact hf w (by simp [hwu, hw]))
        have h2 := hEfin u (f u)
        have h3 := hEadd _ _ h1 h2
        have e : (((0 : InfiniteAdeleRing K), f) : AdeleRing (𝓞 K) K) =
            ((0 : InfiniteAdeleRing K), f - sA u (f u)) + (0, sA u (f u)) :=
          Prod.ext (add_zero 0).symm (sub_add_cancel f _).symm
        rw [e]
        exact h3
    have hD : finiteSupportAdeles (K := K) ⊆ E := by
      rintro x ⟨T, hT⟩
      have e : x = ((x.1, 0) : AdeleRing (𝓞 K) K) + (((0 : InfiniteAdeleRing K), x.2) : AdeleRing (𝓞 K) K) :=
        Prod.ext (add_zero x.1).symm (zero_add x.2).symm
      rw [e]
      exact hEadd _ _ (hEinf _) (hEsupp T x.2 hT)
    have hdense : Dense E := dense_finiteSupportAdeles.mono hD
    intro x
    have : E = Set.univ := by rw [← hEc.closure_eq, hdense.closure_eq]
    have hx : x ∈ E := by rw [this]; exact Set.mem_univ x
    exact hx
  refine ⟨α, main, fun α' hα' => ?_⟩
  have hz : α' - α = 0 := by
    refine eq_zero_of_chiA_mul _ fun x => ?_
    have h1 := main x
    have h2 := hα' x
    have h3 : chiA K (α' * x) = chiA K ((α' - α) * x) * chiA K (α * x) := by
      rw [← chiA_add, ← add_mul, sub_add_cancel]
    rw [h1] at h2
    rw [h2] at h3
    exact (mul_eq_right.mp h3.symm)
  exact sub_eq_zero.mp hz

@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3, first assertion (E = k, number field case): the map is a homeomorphism onto the dual"]
theorem weil_IV_2_thm3_isEmbedding : IsEmbedding (chiAMul (K := K)) := by
  have hinj : Function.Injective (chiAMul (K := K)) := by
    intro a b hab
    have h : ∀ x, chiA K (a * x) = chiA K (b * x) := fun x => DFunLike.congr_fun hab x
    have hz : a - b = 0 := eq_zero_of_chiA_mul _ fun x => by
      have h3 : chiA K (a * x) = chiA K ((a - b) * x) * chiA K (b * x) := by
        rw [← chiA_add, ← add_mul, sub_add_cancel]
      rw [h x] at h3
      exact (mul_eq_right.mp h3.symm)
    exact sub_eq_zero.mp hz
  have hcont : Continuous (chiAMul (K := K)) :=
    ContinuousMap.continuous_of_continuous_uncurry _
      (continuous_chiA.comp (continuous_fst.mul continuous_snd))
  let g : AdeleRing (𝓞 K) K →+ Additive C(AdeleRing (𝓞 K) K, Circle) :=
    { toFun := fun a => Additive.ofMul (chiAMul a)
      map_zero' := by
        refine congrArg Additive.ofMul (ContinuousMap.ext fun x => ?_)
        show chiA K (0 * x) = 1
        rw [zero_mul]
        change chiInf K 0 * chiFin K 0 = 1
        rw [chiInf_zero, chiFin_zero, mul_one]
      map_add' := fun a b => by
        refine congrArg Additive.ofMul (ContinuousMap.ext fun x => ?_)
        show chiA K ((a + b) * x) = chiA K (a * x) * chiA K (b * x)
        rw [add_mul, chiA_add] }
  have hg : Topology.IsInducing g := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    refine le_antisymm ?_ ?_
    swap
    · intro U hU
      obtain ⟨C, hC, hCU⟩ := exists_compact_of_mem_nhds_zero hU
      have hV : IsOpen {z : Circle | 0 < ((z : Circle) : ℂ).re} :=
        isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
      have hW : IsOpen {f : C(AdeleRing (𝓞 K) K, Circle) | Set.MapsTo f C {z : Circle | 0 < ((z : Circle) : ℂ).re}} :=
        ContinuousMap.isOpen_setOfPred_mapsTo hC hV
      refine Filter.mem_comap.mpr ⟨{h : Additive C(AdeleRing (𝓞 K) K, Circle) |
        Set.MapsTo h.toMul C {z : Circle | 0 < ((z : Circle) : ℂ).re}}, hW.mem_nhds ?_, ?_⟩
      · intro x _
        show 0 < (((1 : C(AdeleRing (𝓞 K) K, Circle)) x : Circle) : ℂ).re
        simp
      · intro a ha
        exact hCU a fun x hx => ha hx
    · intro U hU
      obtain ⟨T, hT, hTU⟩ := Filter.mem_comap.mp hU
      have hc : Filter.Tendsto g (𝓝 0) (𝓝 0) := by
        have : ContinuousAt g 0 := (show Continuous g from hcont).continuousAt
        rwa [ContinuousAt, map_zero] at this
      exact Filter.mem_of_superset (hc hT) hTU
  exact ⟨hg, hinj⟩

end NumberFieldKB.WeilBNT
