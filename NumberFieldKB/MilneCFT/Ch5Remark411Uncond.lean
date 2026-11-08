import NumberFieldKB.MilneCFT.Ch5IdelesChar
import NumberFieldKB.Ideles.Compact
import NumberFieldKB.HeckeCharacter.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Ideles.Norm.Surjective

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 4.11, unconditionally

`remark4_11 K : Remark4_11 K`: for every family of homomorphisms $\varphi_\mathfrak m : I_K \to C_\mathfrak m$ that are
trivial on $K^\times$ and equal to the ideal class on $I_{S(\mathfrak m)}$ (no continuity assumed), (i) every compatible
family $(c_\mathfrak m)$ is attained by an idèle, and (ii) $\varphi_\mathfrak m(x)=1$ for all $\mathfrak m$ iff $x$ lies in the
closure of $I_\infty^+ K^\times$.

The proof (all in namespace `R411`):

* **Uniqueness without continuity** (`eq_of_hyp`): two such maps $\varphi,\varphi'$ agree.  With $e=|C_\mathfrak m|$, weak
  approximation (`TauCeti.GlobalNumberFields.exists_unitEmbedding_mul_mem_range_powMonoidHom`) gives $\alpha\in K^\times$
  with $\alpha x$ an $e$-th power at $S(\mathfrak m)$ and at the infinite places.  Build the idèle $R$ of $e$-th roots
  (`ideleOfUnits`); then $\alpha x = Z R^e$ with $Z\in I_{S(\mathfrak m)}$, and $\varphi(R^e)=\varphi(R)^e=1$.  So
  $\varphi(x)=\varphi(Z)=[\mathrm{id}(Z)]=\varphi'(x)$.  Hence every such family is the continuous family `phi0`
  extracted from `remark_4_11_exists`.
* **`key`**: for a continuous such $\varphi$ and $y\in I_\mathfrak m$, $\varphi(y)$ is the ray class of $\mathrm{id}(y)$
  (`idelesModToRay`); proved by correcting $y$ by $b\in K^\times$ so that $by\in I_{\mathfrak m''}$ with $\mathfrak m''$
  deep enough for `ker_contains'`, and splitting off the infinite and local parts as in `prop_4_7_unique`.
* **Surjectivity** (`exists_family`): the sets $F_\mathfrak m=\{q\in C_K^1:\psi_\mathfrak m(q)=c_\mathfrak m\}$ are closed
  (discrete target), nonempty (`phi0` is onto $C_\mathfrak m$ and kills the diagonal idèles `diagIdele`, which adjust the
  norm to $1$), and directed under $\supseteq$ (compatibility `phi0_compat`, common multiple `lcmMod`).  Compactness of
  $C_K^1$ (`IdeleClassGroup.compactSpace_normOne`) and Cantor's intersection theorem give a point of $\bigcap F_\mathfrak m$.
* **Kernel** (`closure_le_ker`, `ker_le_closure`): $\ker\varphi_\mathfrak m$ is open, hence closed, and contains
  $I_\infty^+ K^\times$.  Conversely if all $\varphi_\mathfrak m(x)=1$, then for a neighbourhood $xU$ choose $\mathfrak m$
  with $W_\mathfrak m$ inside $U$ (`idele_nhds_one`); Proposition 4.6 writes the class of $x$ as $K_{\mathfrak m,1}\cdot W_\mathfrak m$,
  and $W_\mathfrak m\subseteq I_\infty^+ U$.
-/

open NumberField IsDedekindDomain Filter Topology
open scoped nonZeroDivisors
open NumberField.InfinitePlace

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NumberFieldKB.MilneCFT
namespace R411

variable {K : Type} [Field K] [NumberField K]

theorem eq_of_hyp (m : Modulus K) (φ φ' : IdeleGroup (𝓞 K) K →* RayClassGroup m)
    (hK : ∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1)
    (hK' : ∀ a : Kˣ, φ' (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1)
    (hI : ∀ x ∈ idelesTrivialAt m.finiteSupport, ∀ b : sIdeals m.finiteSupport,
      (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x → φ x = toRayClass m b)
    (hI' : ∀ x ∈ idelesTrivialAt m.finiteSupport, ∀ b : sIdeals m.finiteSupport,
      (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x → φ' x = toRayClass m b) :
    φ = φ' := by
  classical
  have hfin : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  have hS : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  set e := Nat.card (RayClassGroup m) with he_def
  have he : e ≠ 0 := Nat.card_pos.ne'
  have hpow : ∀ g : RayClassGroup m, g ^ e = 1 := fun g => pow_card_eq_one'
  ext x
  obtain ⟨α, hfinα, hinfα⟩ :=
    TauCeti.GlobalNumberFields.exists_unitEmbedding_mul_mem_range_powMonoidHom hS.toFinset he x
  set X := IdeleGroup.unitEmbedding (𝓞 K) K α * x with hXdef
  have hX : φ x = φ X := by rw [hXdef, map_mul, hK]; exact (one_mul (φ x)).symm
  have hX' : φ' x = φ' X := by rw [hXdef, map_mul, hK']; exact (one_mul (φ' x)).symm
  rw [hX, hX']
  choose r hr using fun w => MonoidHom.mem_range.1 (hinfα w)
  have hex : ∀ v : HeightOneSpectrum (𝓞 K), ∃ u : (v.adicCompletion K)ˣ,
      v ∈ hS.toFinset → u ^ e = v.ideleFiniteCoord X := by
    intro v
    by_cases h : v ∈ hS.toFinset
    · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 (hfinα v h)
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose rf hrf using hex
  set z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ :=
    fun v => if v ∈ hS.toFinset then rf v else 1 with hz
  have hzev : ∀ᶠ v in Filter.cofinite, z v ∈ (v.adicCompletionIntegers K).units := by
    filter_upwards [hS.toFinset.finite_toSet.eventually_cofinite_notMem] with v hv
    have : v ∉ hS.toFinset := by simpa using hv
    simp only [hz, this, ite_false]
    exact one_mem _
  set R := TauCeti.GlobalNumberFields.ideleOfUnits r z hzev with hR
  set Z := X * (R ^ e)⁻¹ with hZ
  have hZmem : Z ∈ idelesTrivialAt m.finiteSupport := by
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · have : w.ideleInfiniteCoord Z = 1 := by
        rw [hZ, map_mul, map_inv, map_pow, hR, TauCeti.GlobalNumberFields.ideleInfiniteCoord_ideleOfUnits,
          ← powMonoidHom_apply, hr w, mul_inv_cancel]
      exact congrArg Units.val this
    · have hv' : v ∈ hS.toFinset := hS.mem_toFinset.2 hv
      have : v.ideleFiniteCoord Z = 1 := by
        rw [hZ, map_mul, map_inv, map_pow, hR, TauCeti.GlobalNumberFields.ideleFiniteCoord_ideleOfUnits]
        simp only [hz, hv', ite_true, hrf v hv', mul_inv_cancel]
      exact congrArg Units.val this
  have hI1 : ideleToIdeal K Z ∈ sIdeals m.finiteSupport :=
    (ideleToIdeal_mem_sIdeals_iff m.finiteSupport Z).2 fun v hv => by rw [hZmem.2 v hv]; exact map_one _
  have hXZ : X = Z * R ^ e := by rw [hZ, inv_mul_cancel_right]
  have h1 : φ X = toRayClass m ⟨_, hI1⟩ := by
    rw [hXZ, map_mul, map_pow, hpow]
    exact (mul_one (φ Z)).trans (hI Z hZmem ⟨_, hI1⟩ rfl)
  have h2 : φ' X = toRayClass m ⟨_, hI1⟩ := by
    rw [hXZ, map_mul, map_pow, hpow]
    exact (mul_one (φ' Z)).trans (hI' Z hZmem ⟨_, hI1⟩ rfl)
  rw [h1, h2]


/-! ### The continuous maps `phi0` -/

theorem exists_phi0 (m : Modulus K) :
    ∃ φ : IdeleGroup (𝓞 K) K →* RayClassGroup m, IsOpen (φ.ker : Set (IdeleGroup (𝓞 K) K)) ∧
      (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
      ∀ x ∈ idelesTrivialAt m.finiteSupport, ∀ b : sIdeals m.finiteSupport,
        (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x → φ x = toRayClass m b := by
  obtain ⟨φ, ⟨hc, hK, hI⟩, -⟩ := remark_4_11_exists m
  refine ⟨φ, ?_, hK, hI⟩
  letI : TopologicalSpace (RayClassGroup m) := ⊥
  haveI : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
  have : (φ.ker : Set (IdeleGroup (𝓞 K) K)) = φ ⁻¹' {1} := by ext y; simp
  rw [this]
  exact (isOpen_discrete _).preimage hc

/-- The continuous map `φ_m` of Remark 4.11 (chosen from `remark_4_11_exists`). -/
def phi0 (m : Modulus K) : IdeleGroup (𝓞 K) K →* RayClassGroup m := (exists_phi0 m).choose

theorem phi0_ker_open (m : Modulus K) : IsOpen ((phi0 m).ker : Set (IdeleGroup (𝓞 K) K)) :=
  (exists_phi0 m).choose_spec.1

theorem phi0_unit (m : Modulus K) (a : Kˣ) : phi0 m (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 :=
  (exists_phi0 m).choose_spec.2.1 a

theorem phi0_triv (m : Modulus K) :
    ∀ x ∈ idelesTrivialAt m.finiteSupport, ∀ b : sIdeals m.finiteSupport,
      (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x → phi0 m x = toRayClass m b :=
  (exists_phi0 m).choose_spec.2.2

/-! ### Moduli -/

theorem pow_dvd_iff_le_ord (m : Modulus K) (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    v.asIdeal ^ k ∣ m.finite ↔ k ≤ m.ord v := by
  have hm : Associates.mk m.finite ≠ 0 := Associates.mk_ne_zero.2 m.finite_ne_bot
  rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
  exact Associates.prime_pow_dvd_iff_le hm v.associates_irreducible

theorem ord_le_of_dvd {f m : Modulus K} (hd : f.Dvd m) (v : HeightOneSpectrum (𝓞 K)) :
    f.ord v ≤ m.ord v := by
  rw [← pow_dvd_iff_le_ord]
  exact ((pow_dvd_iff_le_ord f v _).2 le_rfl).trans hd.1

theorem idelesMod_le_of_dvd {f m : Modulus K} (hd : f.Dvd m) : idelesMod m ≤ idelesMod f := by
  rintro x ⟨h1, h2⟩
  refine ⟨fun w hw => h1 w (hd.2 hw), fun v hv => ?_⟩
  have hvm : v ∈ m.finiteSupport := (show v.asIdeal ∣ f.finite from hv).trans hd.1
  refine (h2 v hvm).trans (WithZero.exp_le_exp.2 ?_)
  have := ord_le_of_dvd hd v
  omega

/-- A modulus divisible by `m`, supported at least on `T` to order at least `N`, with all real places. -/
def bigMod (m : Modulus K) (T : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) : Modulus K where
  finite := m.finite * ∏ v ∈ T, v.asIdeal ^ N
  finite_ne_bot := mul_ne_zero m.finite_ne_bot
    (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ v.ne_bot)
  infinite := {w | w.IsReal}
  isReal_of_mem := fun _ h => h

theorem bigMod_dvd (m : Modulus K) (T : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    m.Dvd (bigMod m T N) :=
  ⟨dvd_mul_right _ _, fun w hw => m.isReal_of_mem w hw⟩

theorem bigMod_pow_dvd (m : Modulus K) (T : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ T) : v.asIdeal ^ N ∣ (bigMod m T N).finite :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal ^ N) hv) _

theorem bigMod_le_ord (m : Modulus K) (T : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ T) : N ≤ (bigMod m T N).ord v :=
  (pow_dvd_iff_le_ord _ v N).1 (bigMod_pow_dvd m T N hv)

theorem bigMod_mem_support (m : Modulus K) (T : Finset (HeightOneSpectrum (𝓞 K))) {N : ℕ} (hN : 1 ≤ N)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ T) : v ∈ (bigMod m T N).finiteSupport :=
  (dvd_pow_self _ (by omega)).trans (bigMod_pow_dvd m T N hv)

/-- The product of two moduli (a common multiple). -/
def lcmMod (m m' : Modulus K) : Modulus K where
  finite := m.finite * m'.finite
  finite_ne_bot := mul_ne_zero m.finite_ne_bot m'.finite_ne_bot
  infinite := m.infinite ∪ m'.infinite
  isReal_of_mem := fun w hw => hw.elim (m.isReal_of_mem w) (m'.isReal_of_mem w)

theorem dvd_lcmMod_left (m m' : Modulus K) : m.Dvd (lcmMod m m') :=
  ⟨dvd_mul_right _ _, Set.subset_union_left⟩

theorem dvd_lcmMod_right (m m' : Modulus K) : m'.Dvd (lcmMod m m') :=
  ⟨dvd_mul_left _ _, Set.subset_union_right⟩

/-! ### The key evaluation lemma -/

/-- On `I_m`, a continuous `φ` as in Remark 4.11 is the ideal-class map `idelesModToRay`. -/
theorem key (m : Modulus K) [TopologicalSpace (RayClassGroup m)] [DiscreteTopology (RayClassGroup m)]
    (φ : IdeleGroup (𝓞 K) K →* RayClassGroup m) (hφ : Continuous φ)
    (hK : ∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1)
    (hI : ∀ x ∈ idelesTrivialAt m.finiteSupport, ∀ b : sIdeals m.finiteSupport,
      (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x → φ x = toRayClass m b)
    (y : idelesMod m) : φ (y : IdeleGroup (𝓞 K) K) = idelesModToRay m y := by
  classical
  obtain ⟨T₀, n₀, h₀⟩ := ker_contains' φ hφ
  have hS : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  set T : Finset (HeightOneSpectrum (𝓞 K)) := hS.toFinset ∪ T₀ with hT
  set N : ℕ := n₀ + 1 with hN
  set M := bigMod m T N with hM
  have hdvd : m.Dvd M := bigMod_dvd m T N
  obtain ⟨b, hb⟩ := exists_unitEmbedding_mul_mem_idelesMod M (y : IdeleGroup (𝓞 K) K)
  set Y := IdeleGroup.unitEmbedding (𝓞 K) K b * (y : IdeleGroup (𝓞 K) K) with hY
  have hYm : Y ∈ idelesMod m := idelesMod_le_of_dvd hdvd hb
  have hbm : IdeleGroup.unitEmbedding (𝓞 K) K b ∈ idelesMod m := by
    have : IdeleGroup.unitEmbedding (𝓞 K) K b = Y * (y : IdeleGroup (𝓞 K) K)⁻¹ := by
      rw [hY, mul_inv_cancel_right]
    rw [this]; exact mul_mem hYm (inv_mem y.2)
  have hbc : b ∈ congruenceSubgroup m := (mem_congruenceSubgroup_iff_mem_idelesMod m b).2 hbm
  have h1 : φ (y : IdeleGroup (𝓞 K) K) = φ Y := by
    rw [hY, map_mul, hK]; exact (one_mul (φ (y : IdeleGroup (𝓞 K) K))).symm
  have hST : m.finiteSupport ⊆ ↑T := fun v hv => by simp [hT, hv]
  have hTM : ∀ v ∈ T, v ∈ M.finiteSupport := fun v hv => bigMod_mem_support m T (by omega) hv
  have hunit : ∀ v ∈ T, Valued.v (ideleFinAt Y v) = 1 := fun v hv =>
    val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one M v (hTM v hv)) (hb.2 v (hTM v hv))
  have hmem : Y * (infPart Y * localPart Y T)⁻¹ ∈ idelesTrivialAt m.finiteSupport :=
    splitTriv_mem Y T _ hST
  have hI1 : ideleToIdeal K (Y * (infPart Y * localPart Y T)⁻¹) ∈ sIdeals m.finiteSupport :=
    (ideleToIdeal_mem_sIdeals_iff _ _).2 fun v hv => by rw [hmem.2 v hv]; exact map_one _
  have hpos : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), IsPosAt w' hw' (ideleInfAt (infPart Y * localPart Y T) w') := by
    intro w' hw'
    rw [ideleInfAt_mul, ideleInfAt_infPart, ideleInfAt_localPart, mul_one]
    exact hb.1 w' hw'
  have hv1 : ∀ v ∈ T, Valued.v (ideleFinAt (infPart Y * localPart Y T) v - 1) ≤ WithZero.exp (-(N : ℤ)) := by
    intro v hv
    rw [ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart, if_pos hv, one_mul]
    refine (hb.2 v (hTM v hv)).trans ?_
    rw [WithZero.exp_le_exp]
    have : N ≤ M.ord v := bigMod_le_ord m T N hv
    omega
  have hv2 : ∀ v ∉ T, Valued.v (ideleFinAt (infPart Y * localPart Y T) v) = 1 := by
    intro v hv
    rw [ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart, if_neg hv, one_mul, map_one]
  have e0 : φ (infPart Y * localPart Y T) = 1 :=
    h₀ T (by intro v hv; simp [hT, hv]) N (by omega) (by omega) _ hpos hv1 hv2
  have h2 : φ Y = toRayClass m ⟨_, hI1⟩ := by
    have hy : Y = (Y * (infPart Y * localPart Y T)⁻¹) * (infPart Y * localPart Y T) := by
      rw [inv_mul_cancel_right]
    calc φ Y = φ ((Y * (infPart Y * localPart Y T)⁻¹) * (infPart Y * localPart Y T)) := by rw [← hy]
      _ = φ (Y * (infPart Y * localPart Y T)⁻¹) * φ (infPart Y * localPart Y T) := map_mul _ _ _
      _ = toRayClass m ⟨_, hI1⟩ := by
        rw [e0]
        exact (mul_one _).trans (hI _ hmem ⟨_, hI1⟩ rfl)
  have h3 : toRayClass m ⟨_, hI1⟩ = idelesModToRay m ⟨Y, hYm⟩ := by
    show (QuotientGroup.mk _ : RayClassGroup m) = QuotientGroup.mk _
    congr 1
    refine Subtype.ext ?_
    exact ideleToIdeal_splitTriv Y T hunit
  have h4 : idelesModToRay m ⟨Y, hYm⟩ = idelesModToRay m ⟨_, hbm⟩ * idelesModToRay m y := by
    rw [← map_mul]; rfl
  have h5 : idelesModToRay m ⟨_, hbm⟩ = 1 := by
    refine ((prop_4_6a m).2 ⟨_, hbm⟩).2 ?_
    exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hbc)
  rw [h1, h2, h3, h4, h5]
  exact one_mul (idelesModToRay m y)

/-! ### Consequences -/

theorem exists_mod_decomp (m : Modulus K) (x : IdeleGroup (𝓞 K) K) :
    ∃ (y : idelesMod m) (a : Kˣ), x = (y : IdeleGroup (𝓞 K) K) * IdeleGroup.unitEmbedding (𝓞 K) K a := by
  obtain ⟨y, hy⟩ := (prop_4_6b m).1 (x : IdeleClassGroup (𝓞 K) K)
  have hy' : ((y : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) = (x : IdeleClassGroup (𝓞 K) K) := hy
  rw [QuotientGroup.eq] at hy'
  obtain ⟨a, ha⟩ := hy'
  exact ⟨y, a, by rw [ha]; group⟩

theorem phi0_eq_ray (m : Modulus K) (y : idelesMod m) :
    phi0 m (y : IdeleGroup (𝓞 K) K) = idelesModToRay m y := by
  letI : TopologicalSpace (RayClassGroup m) := ⊥
  haveI : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
  exact key m (phi0 m) (continuous_of_isOpen_ker _ (phi0_ker_open m)) (phi0_unit m) (phi0_triv m) y

theorem phi0_mul_unit (m : Modulus K) (x : IdeleGroup (𝓞 K) K) (a : Kˣ) :
    phi0 m (x * IdeleGroup.unitEmbedding (𝓞 K) K a) = phi0 m x := by
  rw [map_mul, phi0_unit]; exact mul_one (phi0 m x)

theorem phi0_surjective (m : Modulus K) : Function.Surjective (phi0 m) := by
  intro c
  obtain ⟨y, hy⟩ := (prop_4_6a m).1 c
  exact ⟨y, by rw [phi0_eq_ray, hy]⟩

theorem phi0_compat {m m' : Modulus K} (h : m.Dvd m') (x : IdeleGroup (𝓞 K) K) :
    rayClassMap h (phi0 m' x) = phi0 m x := by
  obtain ⟨y, a, rfl⟩ := exists_mod_decomp m' x
  rw [phi0_mul_unit, phi0_mul_unit, phi0_eq_ray]
  have hy : (y : IdeleGroup (𝓞 K) K) ∈ idelesMod m := idelesMod_le_of_dvd h y.2
  rw [show (y : IdeleGroup (𝓞 K) K) = ((⟨y, hy⟩ : idelesMod m) : IdeleGroup (𝓞 K) K) from rfl, phi0_eq_ray]
  rfl

theorem phi0_infPos (m : Modulus K) (x : IdeleGroup (𝓞 K) K) (hx : x ∈ idelesInfPos K) :
    phi0 m x = 1 := by
  letI : TopologicalSpace (RayClassGroup m) := ⊥
  haveI : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
  exact infinite_part_ker (phi0 m) (continuous_of_isOpen_ker _ (phi0_ker_open m)) x hx.1 hx.2

theorem phi0_diagIdele (m : Modulus K) (s : ℝ) : phi0 m (NumberFieldKB.Ideles.diagIdele K s) = 1 := by
  letI : TopologicalSpace (RayClassGroup m) := ⊥
  haveI : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
  have hc : Continuous (fun s : ℝ => phi0 m (NumberFieldKB.Ideles.diagIdele K s)) :=
    (continuous_of_isOpen_ker _ (phi0_ker_open m)).comp NumberFieldKB.Ideles.continuous_diagIdele
  have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℝ) hc (x := s) (y := 0)
  rw [this, NumberFieldKB.Ideles.diagIdele_zero, map_one]

/-! ### Surjectivity onto compatible families -/

theorem exists_family (c : ∀ m : Modulus K, RayClassGroup m)
    (hc : ∀ m m' (h : m.Dvd m'), rayClassMap h (c m') = c m) :
    ∃ x : IdeleGroup (𝓞 K) K, ∀ m, phi0 m x = c m := by
  classical
  let ψ : ∀ m : Modulus K, IdeleClassGroup (𝓞 K) K →* RayClassGroup m := fun m =>
    QuotientGroup.lift _ (phi0 m) (by rintro _ ⟨a, rfl⟩; exact phi0_unit m a)
  have hψ : ∀ m (x : IdeleGroup (𝓞 K) K), ψ m (x : IdeleClassGroup (𝓞 K) K) = phi0 m x :=
    fun m x => rfl
  let t : Modulus K → Set (NumberFieldKB.Ideles.IdeleClassGroup.normOne K) :=
    fun m => {q | ψ m q.1 = c m}
  have hclosed : ∀ m, IsClosed (t m) := by
    intro m
    letI : TopologicalSpace (RayClassGroup m) := ⊥
    haveI : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
    have hcont : Continuous (ψ m) := by
      refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
      exact continuous_of_isOpen_ker _ (phi0_ker_open m)
    exact (isClosed_discrete {c m}).preimage (hcont.comp continuous_subtype_val)
  have hsub : ∀ m m' (h : m.Dvd m'), t m' ⊆ t m := by
    intro m m' h q hq
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective q.1
    have hq' : ψ m' q.1 = c m' := hq
    show ψ m q.1 = c m
    rw [← hx, hψ] at hq' ⊢
    rw [← phi0_compat h x, hq', hc m m' h]
  have hne : ∀ m, (t m).Nonempty := by
    intro m
    obtain ⟨x₀, hx₀⟩ := phi0_surjective m (c m)
    set r : ℝ := (NumberFieldKB.Ideles.ideleClassNorm K (x₀ : IdeleClassGroup (𝓞 K) K) : ℝ) with hr
    have hr0 : 0 < r := NumberFieldKB.Ideles.coe_ideleClassNorm_pos _
    set s : ℝ := Real.log r⁻¹ / (Module.finrank ℚ K : ℝ) with hs
    set y := x₀ * NumberFieldKB.Ideles.diagIdele K s with hy
    have hnorm : NumberFieldKB.Ideles.ideleClassNorm K (y : IdeleClassGroup (𝓞 K) K) = 1 := by
      apply NNReal.coe_injective
      have h1 : ((y : IdeleClassGroup (𝓞 K) K)) =
          (x₀ : IdeleClassGroup (𝓞 K) K) * (NumberFieldKB.Ideles.diagIdele K s : IdeleClassGroup (𝓞 K) K) :=
        rfl
      rw [h1, map_mul, NNReal.coe_mul, ← hr, hs, NumberFieldKB.Ideles.ideleClassNorm_diagIdele (inv_pos.2 hr0)]
      rw [NNReal.coe_one]
      exact mul_inv_cancel₀ hr0.ne'
    refine ⟨⟨(y : IdeleClassGroup (𝓞 K) K),
      (NumberFieldKB.Ideles.IdeleClassGroup.mem_normOne_iff _).2 hnorm⟩, ?_⟩
    show ψ m (y : IdeleClassGroup (𝓞 K) K) = c m
    rw [hψ, hy, map_mul, phi0_diagIdele, hx₀]
    exact mul_one (c m)
  have hdir : Directed (· ⊇ ·) t := fun m m' =>
    ⟨lcmMod m m', hsub m _ (dvd_lcmMod_left m m'), hsub m' _ (dvd_lcmMod_right m m')⟩
  haveI : Nonempty (Modulus K) := ⟨Modulus.one K⟩
  have hcomp : ∀ m, IsCompact (t m) := fun m => (hclosed m).isCompact
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne hcomp hclosed
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective q.1
  refine ⟨x, fun m => ?_⟩
  have := Set.mem_iInter.1 hq m
  have h' : ψ m q.1 = c m := this
  rw [← hx, hψ] at h'
  exact h'

/-! ### The kernel -/

theorem closure_le_ker (m : Modulus K) (x : IdeleGroup (𝓞 K) K)
    (hx : x ∈ closure ((idelesInfPos K ⊔ IdeleGroup.principalSubgroup (𝓞 K) K : Subgroup _) :
      Set (IdeleGroup (𝓞 K) K))) : phi0 m x = 1 := by
  letI : TopologicalSpace (RayClassGroup m) := ⊥
  haveI : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
  have hcont : Continuous (phi0 m) := continuous_of_isOpen_ker _ (phi0_ker_open m)
  have hcl : IsClosed ((phi0 m) ⁻¹' {1} : Set (IdeleGroup (𝓞 K) K)) := (isClosed_discrete {1}).preimage hcont
  have hsub : ((idelesInfPos K ⊔ IdeleGroup.principalSubgroup (𝓞 K) K : Subgroup _) :
      Set (IdeleGroup (𝓞 K) K)) ⊆ (phi0 m) ⁻¹' {1} := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hz
    obtain ⟨c, rfl⟩ := hb
    show phi0 m (a * IdeleGroup.unitEmbedding (𝓞 K) K c) = 1
    rw [phi0_mul_unit]
    exact phi0_infPos m a ha
  exact closure_minimal hsub hcl hx

theorem ker_le_closure (x : IdeleGroup (𝓞 K) K) (hx : ∀ m : Modulus K, phi0 m x = 1) :
    x ∈ closure ((idelesInfPos K ⊔ IdeleGroup.principalSubgroup (𝓞 K) K : Subgroup _) :
      Set (IdeleGroup (𝓞 K) K)) := by
  classical
  rw [mem_closure_iff_nhds]
  intro t ht
  have hU : (fun u : IdeleGroup (𝓞 K) K => x * u) ⁻¹' t ∈ 𝓝 (1 : IdeleGroup (𝓞 K) K) := by
    have hc : Continuous (fun u : IdeleGroup (𝓞 K) K => x * u) := continuous_const.mul continuous_id
    exact hc.continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨T, n, hTn⟩ := idele_nhds_one hU
  obtain ⟨m, hminf, hmS, hmord⟩ := exists_modulus T (n + 1) (by omega)
  obtain ⟨y, a, hxy⟩ := exists_mod_decomp m x
  have hy1 : idelesModToRay m y = 1 := by
    rw [← phi0_eq_ray, ← hx m, hxy, phi0_mul_unit]
  obtain ⟨y1, ⟨b, hb, rfl⟩, w, hw, hyw⟩ := Subgroup.mem_sup.1 (((prop_4_6a m).2 y).1 hy1)
  have hw' : w⁻¹ ∈ idelesW m := inv_mem hw
  have hwpos : ∀ (w' : InfinitePlace K) (hw'' : w'.IsReal), IsPosAt w' hw'' (ideleInfAt w w') := by
    intro w' hw''
    exact hw.1.1 w' (by rw [hminf]; exact hw'')
  have hinf : infPart w ∈ idelesInfPos K :=
    ⟨fun v => ideleFinAt_infPart w v, fun w' hw'' => by rw [ideleInfAt_infPart]; exact hwpos w' hw''⟩
  have hu : (fun u : IdeleGroup (𝓞 K) K => x * u) (w⁻¹ * infPart w) ∈ t := by
    refine hTn _ (fun w' => ?_) (fun v hv => ?_) (fun v hv => ?_)
    · rw [ideleInfAt_mul, ideleInfAt_inv, ideleInfAt_infPart, inv_mul_cancel₀ (ideleInfAt_ne_zero w w')]
    · rw [ideleFinAt_mul, ideleFinAt_infPart, mul_one]
      have hvm : v ∈ m.finiteSupport := by rw [hmS]; exact hv
      refine (hw'.1.2 v hvm).trans ?_
      rw [WithZero.exp_le_exp]
      have := hmord v hv
      omega
    · have hvm : v ∉ m.finiteSupport := by rw [hmS]; exact hv
      rw [ideleFinAt_mul, ideleFinAt_infPart, mul_one]
      exact hw'.2 v hvm
  have hxe : x * (w⁻¹ * infPart w) =
      IdeleGroup.unitEmbedding (𝓞 K) K (b * a) * infPart w := by
    rw [hxy, ← hyw, map_mul]
    have : IdeleGroup.unitEmbedding (𝓞 K) K b * w * IdeleGroup.unitEmbedding (𝓞 K) K a * (w⁻¹ * infPart w) =
        IdeleGroup.unitEmbedding (𝓞 K) K b * IdeleGroup.unitEmbedding (𝓞 K) K a * infPart w * (w * w⁻¹) := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [this, mul_inv_cancel, mul_one]
  refine ⟨IdeleGroup.unitEmbedding (𝓞 K) K (b * a) * infPart w, ?_, ?_⟩
  · rw [← hxe]; exact hu
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨b * a, rfl⟩) (Subgroup.mem_sup_left hinf)

end R411

/-- **Remark 4.11** (Milne, *CFT*, V, p. 176), unconditionally: for every family of homomorphisms
$\varphi_\mathfrak m : I_K \to C_\mathfrak m$ trivial on $K^\times$ and agreeing with the ideal class on
$I_{S(\mathfrak m)}$, every compatible family $(c_\mathfrak m)$ is attained by one idèle, and the idèles with all
$\varphi_\mathfrak m(x) = 1$ form the closure of $I_\infty^+\cdot K^\times$.  See the module docstring. -/
@[kb "milne2020cft" "Ch. V, Remark 4.11"]
theorem remark4_11 (K : Type) [Field K] [NumberField K] : Remark4_11 K where
  surjective φ hφ c hc := by
    have hφ0 : ∀ m, φ m = R411.phi0 m := fun m =>
      R411.eq_of_hyp m (φ m) (R411.phi0 m) (hφ m).1 (R411.phi0_unit m) (hφ m).2 (R411.phi0_triv m)
    obtain ⟨x, hx⟩ := R411.exists_family c hc
    exact ⟨x, fun m => by rw [hφ0 m]; exact hx m⟩
  ker_eq φ hφ x := by
    have hφ0 : ∀ m, φ m = R411.phi0 m := fun m =>
      R411.eq_of_hyp m (φ m) (R411.phi0 m) (hφ m).1 (R411.phi0_unit m) (hφ m).2 (R411.phi0_triv m)
    constructor
    · intro h
      exact R411.ker_le_closure x fun m => by rw [← hφ0 m]; exact h m
    · intro h m
      rw [hφ0 m]
      exact R411.closure_le_ker m x h

end NumberFieldKB.MilneCFT
