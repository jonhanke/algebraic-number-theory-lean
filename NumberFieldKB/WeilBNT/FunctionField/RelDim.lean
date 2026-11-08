import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Relative dimension of two subspaces

For subspaces $N,N'$ of a vector space $M$ over a field $F$, **`relDim N N'`** is
$\dim_F N'/(N\cap N')$ and **`RelFinite N N'`** says that this quotient is finite-dimensional. These are used for
the dimension counts of Riemann–Roch with repartitions (Weil VI.§2), where all ambient spaces are
infinite-dimensional.
-/

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- $N'/(N\cap N')$, as a quotient of $N'$. -/
abbrev RelQuot (N N' : Submodule F M) : Type _ := N' ⧸ N.comap N'.subtype

/-- The relative dimension $\dim N'/(N\cap N')$. -/
def relDim (N N' : Submodule F M) : ℕ := Module.finrank F (RelQuot N N')

/-- $N'/(N\cap N')$ is finite-dimensional. -/
def RelFinite (N N' : Submodule F M) : Prop := FiniteDimensional F (RelQuot N N')

theorem relQuot_subsingleton_of_le {N N' : Submodule F M} (h : N' ≤ N) :
    Subsingleton (RelQuot N N') := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro x
  exact h x.2

theorem relData_of_equiv {M₂ : Type*} [AddCommGroup M₂] [Module F M₂]
    {a b : Submodule F M} {c d : Submodule F M₂} (e : RelQuot a b ≃ₗ[F] RelQuot c d) :
    (RelFinite a b ↔ RelFinite c d) ∧ relDim a b = relDim c d := by
  unfold RelFinite
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, e.finrank_eq⟩
  · exact Module.Finite.equiv e
  · exact Module.Finite.equiv e.symm

theorem relData_congr {N N2 N' : Submodule F M} (h : ∀ x ∈ N', x ∈ N ↔ x ∈ N2) :
    (RelFinite N N' ↔ RelFinite N2 N') ∧ relDim N N' = relDim N2 N' := by
  have hc : N.comap N'.subtype = N2.comap N'.subtype := by
    ext x; exact h x x.2
  exact relData_of_equiv (Submodule.quotEquivOfEq _ _ hc)

/-- Second isomorphism theorem as a linear equivalence. -/
def relQuotSupEquiv (A B : Submodule F M) : RelQuot A B ≃ₗ[F] RelQuot A (A ⊔ B) := by
  let g : B →ₗ[F] RelQuot A (A ⊔ B) :=
    (Submodule.mkQ (A.comap (A ⊔ B).subtype)).comp (Submodule.inclusion le_sup_right)
  have hker : LinearMap.ker g = A.comap B.subtype := by
    ext x
    simp [g, Submodule.Quotient.mk_eq_zero]
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [g, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simpa using ha
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hsurj)

/-- The inclusion `RelQuot N N' → RelQuot N N''`. -/
def relInc (N : Submodule F M) {N' N'' : Submodule F M} (h : N' ≤ N'') :
    RelQuot N N' →ₗ[F] RelQuot N N'' :=
  Submodule.mapQ _ _ (Submodule.inclusion h) (by
    intro x hx
    simpa using hx)

/-- The projection `RelQuot N N'' → RelQuot N' N''`. -/
def relProj {N N' : Submodule F M} (N'' : Submodule F M) (h : N ≤ N') :
    RelQuot N N'' →ₗ[F] RelQuot N' N'' :=
  Submodule.mapQ _ _ LinearMap.id (by
    intro x hx
    exact h hx)

theorem relInc_injective (N : Submodule F M) {N' N'' : Submodule F M} (h : N' ≤ N'') :
    Function.Injective (relInc N h) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [relInc, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq ⊢
  simpa using hq

theorem relProj_surjective {N N' : Submodule F M} (N'' : Submodule F M) (h : N ≤ N') :
    Function.Surjective (relProj N'' h) := by
  intro q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem relProj_ker {N N' N'' : Submodule F M} (h1 : N ≤ N') (h2 : N' ≤ N'') :
    LinearMap.ker (relProj N'' h1) = LinearMap.range (relInc N h2) := by
  ext q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  constructor
  · intro hy
    have hy' : (y : M) ∈ N' := by
      have : relProj N'' h1 (Submodule.Quotient.mk y) = 0 := hy
      simpa [relProj, Submodule.Quotient.mk_eq_zero] using this
    exact ⟨Submodule.Quotient.mk ⟨y.1, hy'⟩, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hz2 := (Submodule.Quotient.eq _).mp hz
    have hz' : (z : M) ∈ N' := z.2
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub,
      Submodule.coe_inclusion] at hz2
    have hy : (y : M) = (z : M) - ((z : M) - y) := by abel
    show relProj N'' h1 (Submodule.Quotient.mk y) = 0
    simp only [relProj, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.coe_subtype]
    rw [hy]
    exact N'.sub_mem hz' (h1 (by simpa [relInc] using hz2))

theorem relFinite_trans_aux {N N' N'' : Submodule F M} (h1 : N ≤ N') (h2 : N' ≤ N'')
    (f1 : RelFinite N N') (f2 : RelFinite N' N'') : RelFinite N N'' := by
  unfold RelFinite at *
  let φ := relProj N'' h1
  haveI : Module.Finite F (LinearMap.ker φ) := by
    rw [relProj_ker h1 h2]
    exact Module.Finite.equiv (LinearEquiv.ofInjective _ (relInc_injective N h2))
  haveI : Module.Finite F (RelQuot N N'' ⧸ LinearMap.ker φ) :=
    Module.Finite.equiv (φ.quotKerEquivOfSurjective (relProj_surjective N'' h1)).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker φ)

theorem relFinite_of_le {N N' : Submodule F M} (h : N' ≤ N) : RelFinite N N' := by
  haveI := relQuot_subsingleton_of_le h
  unfold RelFinite
  infer_instance

theorem relDim_eq_zero_of_le {N N' : Submodule F M} (h : N' ≤ N) : relDim N N' = 0 := by
  haveI := relQuot_subsingleton_of_le h
  exact Module.finrank_zero_of_subsingleton

theorem le_of_relDim_eq_zero {N N' : Submodule F M} (f : RelFinite N N') (h : relDim N N' = 0) :
    N' ≤ N := by
  unfold RelFinite at f
  have hs : Subsingleton (RelQuot N N') := Module.finrank_zero_iff.mp h
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff'] at hs
  intro x hx
  exact hs ⟨x, hx⟩

/-- Additivity along a chain $N\le N'\le N''$. -/
theorem relFinite_trans {N N' N'' : Submodule F M} (h1 : N ≤ N') (h2 : N' ≤ N'')
    (f1 : RelFinite N N') (f2 : RelFinite N' N'') : RelFinite N N'' := by
  exact relFinite_trans_aux h1 h2 f1 f2

theorem relDim_trans {N N' N'' : Submodule F M} (h1 : N ≤ N') (h2 : N' ≤ N'')
    (f1 : RelFinite N N') (f2 : RelFinite N' N'') :
    relDim N N'' = relDim N N' + relDim N' N'' := by
  have f := relFinite_trans_aux h1 h2 f1 f2
  unfold RelFinite at f f1 f2
  let φ := relProj N'' h1
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr (relProj_surjective N'' h1), finrank_top, relProj_ker h1 h2,
    LinearMap.finrank_range_of_inj (relInc_injective N h2)] at h
  unfold relDim
  omega

/-- The pieces of a chain are finite when the whole is. -/
theorem relFinite_left {N N' N'' : Submodule F M} (h1 : N ≤ N') (h2 : N' ≤ N'')
    (f : RelFinite N N'') : RelFinite N N' ∧ RelFinite N' N'' := by
  unfold RelFinite at *
  exact ⟨Module.Finite.of_injective (relInc N h2) (relInc_injective N h2),
    Module.Finite.of_surjective (relProj N'' h1) (relProj_surjective N'' h1)⟩

/-- Second isomorphism theorem: $(A+B)/A\cong B/(A\cap B)$. -/
theorem relDim_sup_right (A B : Submodule F M) : relDim A (A ⊔ B) = relDim A B := by
  exact (relData_of_equiv (relQuotSupEquiv A B)).2.symm

theorem relFinite_sup_right_iff (A B : Submodule F M) : RelFinite A (A ⊔ B) ↔ RelFinite A B := by
  exact (relData_of_equiv (relQuotSupEquiv A B)).1.symm

/-- For $N\le N'$ and any $K$: $\dim(N'+K)/(N+K)+\dim(N'\cap K)/(N\cap K)=\dim N'/N$. -/
theorem relDim_sup_add_inf {N N' : Submodule F M} (K : Submodule F M) (h : N ≤ N')
    (f : RelFinite N N') :
    RelFinite (N ⊔ K) (N' ⊔ K) ∧ RelFinite (N ⊓ K) (N' ⊓ K) ∧
      relDim (N ⊔ K) (N' ⊔ K) + relDim (N ⊓ K) (N' ⊓ K) = relDim N N' := by
  have hle1 : N ≤ N ⊔ (N' ⊓ K) := le_sup_left
  have hle2 : N ⊔ (N' ⊓ K) ≤ N' := sup_le h inf_le_left
  obtain ⟨fa, fb⟩ := relFinite_left hle1 hle2 f
  have hsum : (N ⊔ K) ⊔ N' = N' ⊔ K :=
    le_antisymm (sup_le (sup_le (h.trans le_sup_left) le_sup_right) le_sup_left)
      (sup_le le_sup_right (le_sup_of_le_left le_sup_right))
  have e1 := relDim_sup_right (N ⊔ K) N'
  have e1f := relFinite_sup_right_iff (N ⊔ K) N'
  rw [hsum] at e1 e1f
  have c1 := relData_congr (N := N ⊔ K) (N2 := N ⊔ (N' ⊓ K)) (N' := N') (by
    intro x hx
    constructor
    · intro hxk
      obtain ⟨n, hn, k, hk, rfl⟩ := Submodule.mem_sup.mp hxk
      refine Submodule.mem_sup.mpr ⟨n, hn, k, Submodule.mem_inf.mpr ⟨?_, hk⟩, rfl⟩
      have : k = (n + k) - n := by abel
      rw [this]
      exact N'.sub_mem hx (h hn)
    · intro hx2
      exact sup_le_sup_left inf_le_right N hx2)
  have c2 := relData_congr (N := N ⊓ K) (N2 := N) (N' := N' ⊓ K) (by
    intro x hx
    simp only [Submodule.mem_inf] at hx ⊢
    tauto)
  have e2 := relDim_sup_right N (N' ⊓ K)
  have e2f := relFinite_sup_right_iff N (N' ⊓ K)
  have tr := relDim_trans hle1 hle2 fa fb
  refine ⟨e1f.mpr (c1.1.mpr fb), c2.1.mpr (e2f.mp fa), ?_⟩
  have := c1.2
  have := c2.2
  omega

/-- Transport along an injective linear map. -/
theorem relDim_map {M' : Type*} [AddCommGroup M'] [Module F M'] (g : M →ₗ[F] M')
    (hg : Function.Injective g) (N N' : Submodule F M) :
    (RelFinite (N.map g) (N'.map g) ↔ RelFinite N N') ∧ relDim (N.map g) (N'.map g) = relDim N N' := by
  have key : RelQuot N N' ≃ₗ[F] RelQuot (N.map g) (N'.map g) := by
    let φ : N' →ₗ[F] RelQuot (N.map g) (N'.map g) :=
      (Submodule.mkQ ((N.map g).comap (N'.map g).subtype)).comp
        (g.restrict (fun x hx => Submodule.mem_map_of_mem hx))
    have hker : LinearMap.ker φ = N.comap N'.subtype := by
      ext x
      simp only [φ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
        Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = (x : M) := hg hyx
        rw [← this]; exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hsurj : Function.Surjective φ := by
      intro q
      obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)
  exact ⟨(relData_of_equiv key).1.symm, (relData_of_equiv key).2.symm⟩

/-- For finite-dimensional $N\le N'$: $\dim N'/N=\dim N'-\dim N$. -/
theorem relDim_of_finiteDimensional {N N' : Submodule F M} (h : N ≤ N') [FiniteDimensional F N'] :
    RelFinite N N' ∧ relDim N N' + Module.finrank F N = Module.finrank F N' := by
  have hfin : RelFinite N N' := by unfold RelFinite; infer_instance
  refine ⟨hfin, ?_⟩
  have h1 := Submodule.finrank_quotient_add_finrank (N.comap N'.subtype)
  have h2 := (Submodule.comapSubtypeEquivOfLe h).finrank_eq
  unfold relDim
  rw [← h2]
  exact h1

/-- $\dim M/N$ as a relative dimension. -/
theorem relDim_top (N : Submodule F M) :
    (RelFinite N ⊤ ↔ FiniteDimensional F (M ⧸ N)) ∧ relDim N ⊤ = Module.finrank F (M ⧸ N) := by
  have key : RelQuot N ⊤ ≃ₗ[F] M ⧸ N := by
    refine Submodule.Quotient.equiv _ _ Submodule.topEquiv ?_
    ext x
    simp [Submodule.mem_map]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, key.finrank_eq⟩
  · unfold RelFinite at h
    exact Module.Finite.equiv key
  · unfold RelFinite
    exact Module.Finite.equiv key.symm

/-- The annihilator of $N$ in the dual has dimension $\dim M/N$ when that is finite. -/
theorem finrank_dualAnnihilator (N : Submodule F M) [FiniteDimensional F (M ⧸ N)] :
    Module.finrank F N.dualAnnihilator = Module.finrank F (M ⧸ N) := by
  rw [← (Submodule.dualQuotEquivDualAnnihilator N).finrank_eq, Subspace.dual_finrank_eq]

end NumberFieldKB.WeilBNT.FF
